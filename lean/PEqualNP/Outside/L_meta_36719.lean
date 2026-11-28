import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36719.Model
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


end PEqualNP.Outside.L_meta_36719.Model

namespace PEqualNP.Outside.L_meta_36719
open PEqualNP.Outside.L_meta_36719.Model
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

def SBf (j : Nat) : Nat := [6, 4, 7, 8, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36719

namespace PEqualNP.Outside.L_meta_36719
open PEqualNP.Outside.L_meta_36719.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x284c1a40128080018076a1601806bf43bd43bf42bd42be41bc41be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x180028810020025aa5a1c754f428ea98832d52107a060087808010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 6
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
  | 4 => packedAt s0K4 (244+((h/4+packedAt s0K4 (224+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s0K3 (170+((h/2+packedAt s0K3 (162+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfe03fffffffe01fffff80fffffff01fff1fe3f
  | 3 => 0xfffc03fc03fffe01fffff01fc07ffe07fe63c7
  | 4 => 0xfffffc0003fffffe01ffffe0007ffff81f83f8
  | 5 => 0xfffffffffc00000001ffffffff8000001ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x9604848428a224242450b162d48b628a26acdb
  | 2 => 0x2ba1292a51451d4948ac0ab56955115551562d
  | 3 => 0x4caba2329a69491d913d58198c66b4479a6346
  | 4 => 0x713233a3639191911dce6cd03078d9e11d83b0
  | 5 => 0x81c3c3c383e1e1e1e1f78f1e3e40e1861ff800
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36719
namespace PEqualNP.Outside.L_meta_36719
open PEqualNP.Outside.L_meta_36719.Model
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
  | 2 => 0x7f01fff80fffe07fe07e0f83ff07fe07f44e73
  | 3 => 0x7ffe03fff01fff81ff800ffc1ff83ff818739c
  | 4 => 0x800003ffffe00001fffff0001fffc0001f83e0
  | 5 => 0xfffffc0000000001ffffffffe00000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x108100881024000028a1104220842a28194a5
  | 2 => 0x2aa529946a548ae8f0548aa35546b415544a52
  | 3 => 0x4c954aa528d91a2b75410ce919d23950586318
  | 4 => 0x68d9b3464c91d34db9e7a8421ee710619e83e0
  | 5 => 0x70e1c3878f1e1c71de79cf73908421861f7c00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36719
namespace PEqualNP.Outside.L_meta_36719
open PEqualNP.Outside.L_meta_36719.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x5c2cd202c1002d2800024001c0002600119442000000700123c6c000589831f00012980000009144468000a539d18bc19000a0bab1e84a8e02a8005460208001020008302000021e0c880ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x23310541400001a400763b8000027000d40c1600000001f1c8000000078003a000013cac1a289302e7b3c000007f00000007028100fc6f35000e4590a11c1600160000000000fcf8002f8008c09409e8486e000f0408300000000000174cc0000104c64500084000e2409400000919cae5c00128ea37320000000368107033029840008080443213130f860311694876000e0d01a6b3c8005c000d8bc02650000004842a0006c2930000645811108883d15800004d151c45007362140074402080000060e892732a800005b29800004e2596806432f1a0fa180f0780458043060000c00180404000c0000200800045004040800000424000000341c10181000140024000424027ca721cf54a439ea8c873e5090e7ca621e794c439ea90873d5110e7ca021cf94f429ea8e853e50d0a7aa92157d4d42ae29a859f5350a78a6a16714d428e29a85af5250a7ea2a14f141429f2a0853f54cca78a9994f952329eaa4659c438caeca3195d546329faa2653c544ca7ca8194f55032ce218653e53d067aa5a0cf943419eaa4835f53506b8a6a0e7d4d419e29a839c5350638a6a0cfd4941dba8a833c505067ca820cfd53319e2a6633e548c67aa918e710e31b7294636d528c67ea898cf151319f2a0633d540c7388618cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710cf951219eaa2433e540867aa810f948421af29c815d539027ca7206794e408f29c819d539027aa5204f546409f284813e531027aa4204f544409f28081ba501027ca9984f55330ce21e613e548c27aa9184fd51309e2a2619c434c2dea4985b14930bba8a6174514c27ea8184f150309f2a6413d54c827ea9104f152209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209f2a6213d54c427ea9084f152109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xac400c80000000ba6004000a805a868000029c398022188c0c81e0240144800000800410878718d51d0a1e63943428d58454ccb14439463287594430ca8d6210c328718d52d061e63943418b58854cc70c4394a3187594430c6956110c318718d544863860551218718d540861c63548408718d511030c4314930c510c514c21e63d50308b588540c23561150308718d54c821e63d52208718d54c421e63d5210
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 5 => packedAt s2K5 (880+((h/16+packedAt s2K5 (768+(h % 16)*7) 7) % 69)*7) 7
  | 4 => packedAt s2K4 (3970+((h/44+packedAt s2K4 (3618+(h % 44)*8) 8) % 194)*9) 9
  | 3 => packedAt s2K3 (1036+((h/8+packedAt s2K3 (988+(h % 8)*6) 6) % 45)*6) 6
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 1 => 0xc0ffffc0fff83fff07c1e0fffe1fe07fd13e73
  | 3 => 0xff03ffff03ffc1fff801ff07ffe1ff81e1cf9c
  | 4 => 0x3fffffc0001fffffe0007fffe0001fe0fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x44100888209000002942410900222a280650a5
  | 1 => 0x92299106492270cb0290a8d2b2154154d12652
  | 3 => 0xa4aa2121a46135550213a44d5419505618b18
  | 4 => 0x2cb344a49074a5a69cf4108769980619ba0de0
  | 5 => 0x30c38738e38739f8e739dce071111861fdf000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88ee88aa88eeaaaa88ee88aa88eeaaaa88ee88aa88eeaaaa88ee88aa88eeaaaa88ee88aa88eeaaaa88ee88aa88eeaaaa88ee88aa88eeaaaa88ee88aa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36719
namespace PEqualNP.Outside.L_meta_36719
open PEqualNP.Outside.L_meta_36719.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x4817e53903bca7205794e40bea9c81dd53902baa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330efa1e61dc43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130efa1a61dc434c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb10a21f521443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf5350af8a6a17714d42ae29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997790f32eea1e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cbbe87197710e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997790d32eea1a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32efa1865dc430cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077a87a0df94b41bea9683be42d077885a0df94341bea86837d54906fca720df54e41df21c83bc43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837e50906faa120dfd4d41efa9a835f53506f8a6a0f714d41ae29a83bf435077a86a0dfd4941be29283be425077884a0fdd0541df20a837f50506f8a0a0df95041bf29883de53106bca620df54c41eea98835d531077c8620ef10c41bf290837d521077e8420ef50841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998f790f31eea1e637e52cc6faa598f78cb31ee196637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31efa1c63dc438c6fca518df54a31ef99463dd328c6fca318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898f790d31eea1a637f524c6f8a498f78c931ee19263f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c7be8618f710c31bf290637d520c7be6418f74c831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a643be54c867ca990df55321deaa6433d54c86f8a990dfd4f21bf29e43de53c86bca790df54f21eea9e435d53c86f8a790df94321bea86437f54886fca910ef952219f2a4437d548877aa910cf55221be2a4437f53886fca710f794e21af29c437d53887baa710d754e21be29c437d52886fca310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821bf28843ef21087ec4210fb48421fa90843e521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x14a293e4be06c3c8ab29867806a7b000000000000001bc59000000000a19ba0001c0000000fe1842b287000910918350983d8d29c53fe000001cf000000f80001d067095844326638ca17848256800000264478a49603488d0979463909d8250fe222000b91b84469d0b38be306328f423e1da49c9d28e2fe8954a90b3ae40481947000a34bb8f10540ccee80000001cae8571ac464851260005984c0c01d421d1e1211665d4b09523fc710b124922c5c4318504541b127a311680acfba100105602121118661c478ac064994c2a8f4861d45128512e1b4fc21e1c010c1600332a3bd229f60006193d0c132419907a401d66ed0b85d2a017c7d28440e000d49574081951e83803c780c212e2f21d8d713f3b03186aa6941a7048c1f900a8c0ed14d08084c102504243ec392673783408791d0d00014481344c9d52a00b52e7c8c88b12288bc001cb1347180a14b29e6bc2f2833fa1f4db8a547e608000e500000013a68000000699080000ec0020e0e80008380022e32cf9a94234930fa1004f2a65199df3dc58d2ba784ba26cf786914031ca12092a6324da955530a4d009db3ce9f0e907a3622552f11507c2247c88613a47c620c537c640239cd3165109d8480f6298ab26b250365001a70306d9268000004406100043a8880000000092c000000000001a09f0a2870cb0000a8970001974cc2b4f601538e0000022900038882030142160001890007887e8004940007a8003563780020851000040a0a000000b280e0400501400010060040c0000100800004000000002401000050140a0040400800044070400005815018010000b030010001a0200800000020200380101000020000000006c1700000000000044700c020000506c00020000040a07418018040180d00003000000000600c040000d0340a000120141202c0400000028020102200014000040ec03008350240601002028010480000020014050180100c0000c0a068050a03600009044000200e02012090350000b0580003c16000000000007c2807c0002c0002407014020382300825004040240100814000040000500c020000100c1e03c000140f0300701001084060b800090050143004400004020180500800000110180a00400000000000f01c0204c0000afca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855
  | 3 => 0x5500e2803a4810521905447806e40c8e0898294c200000129000000bf0102ec4341283a48e9186e83c1144c448a1f4fa000b68000008b400000318470579fc52056d4304d07a00000031432000000000006c8cd9f5340098418bb330000000001182a4be0371100005403f2c8330d5174104000830003f6064d6a5939c5b115a481387705d2622d21e09e12a3d69a866a360420243e125148538aa2030d69b50a19f3e282c761e13da248142704c857d1ba282720003226e45c399408004e26d07386a04408c5ca0246a9093ba961a84b0b8136380000d19a80000000b8004423482a8774a2620f28f327019c9e9d611a2c0519810003700020c4fc8e45a8000002f46d00001ea004b19d05c010010b60967550c000022000001d34346fc050002240682e1ca0b6414900b70004d08da922b85bd1da1b1b62b80000008c634c7800000000d110e0005a9488f43662fce18fc1be0d8ec90c2900b4e49b00002e079016178664c512d2121ccdca5b3a88b09aa1519ea087b97b1ae1040027f2e6360000f84d8030000000007a40008400007000000000a29398000000482488b00c4c1271de4b01c4de8001c85f40012413c240e818014e980bd0990c0a300087e4c688022a5a474a2cb594134c7a9292160b43852a99a126090671331c60e5028940a6000e10004640000004f000000fd059244000001ac000000270003c6744a5000448000ac93711c5a07701d4e42000fa534ac791139cc1fe5b9378d13cc684178622bc2
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1518825f63546209718d518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534833754d4520cd153514835753d4520d514f51483375414520cd15051483575314520d514c514826e65c8520d914721483645148520d9146204825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510826d6588420d954621083655108420d9547200826f6548020b9185200836551480209ed95200825f63553109718d54c425e63153109758c54c423f6454f108f19153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c425e6394b109758e52c436452487109798f548425d63d52109798e548425d63952108f993538423d64d4e108f992538423d6494e108fd91528423c6454a1097d8d528425c6354a108f990528423d6414a109798c528425d6314a10d9d48218423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910d958452442766588510d914a21442746548510d9149214436452841109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520427661148109d597210436552c84109d59421043655208410d954b100427965840109dd9510042e46244010d9549100427b6544010
  | 1 => 0xc71c5450d31c7152324c65e650c931a7590324c71c540c931c7152314c63d6595031c718d540c63e64150319798c540c65d65d0c31c7553430c65d6510c31c7550430c71d54cc83197d95320c69c644c831c7551320c71d54cc43197d95310c69c644c431c7551310c677654c4319798f54c865d63d53219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f21c795153c871d5454f218f99053c863d6414f219798f548865d63d52219798c548865d63152218f993538863d64d4e21c7952538871d5494e21c7951538871d5454e218f990538863d6414e2197d8d544865c63551219ed81544867860551219798c544865d63151218fd91534863c6454d219ed8153486786054d218f990534863d6414d218f990504863d64141219798c504865d631412197d8d540865c63550219798c540865d63150219e980540867960150218fd91530863c6454c218f990530863d6414c219e98053086796014c218f992520863d64948219798e520865d63948218f992510863d64944219798e510865d6394421b958a210866f65484219dd9521086e76548421d9d9521086e460484218fd91500863c645402197d8d500865c6354021d9485500871d5390f40c754c43d031d53d0b40a718d42d031d5350b40c754f41d029c6350740c754d41d031e53d0e40c794d439031e5390a40a758c429031e5310a40c794e419029d6310640c794c419029d63d0240c794f409023e6510d409798c525025d63149408f997425029c63509409798c515025d63145408f997415029c6350540a798e405023f6550c4097d8d521025c63548408f596421029d631084097d8d511025c63544408f596411029d6310440a758f401023f65500409ed95401031c6355330c755343cc31d5410f30c755332cc29c644cb30c755132cc31d54cc730a719131cc31d544c730c758e548c31e5490e30c7951438c31e548ca30a7590328c31e540ca30c7952318c29d640c630c7950318c29d64cc230c7953308c25d63951309bd89544c26c62551309dd85544c274615513097997434c25e6510d30c7550434c23e64149308f590524c25e65cc930a7191324c23e64145308f590514c25e65cc530a7191314c29e648c1309798f540c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c3097d95430c31c5450c308fd91520c23c645483097596320c29d640c8308fd91510c23c645443097596310c29d640c4308f992500c23d6494030a7593300c25f654c0309ed95300c25f63553209718d54c825e63153209758c54c823f6454f208f19153c823e6414f208f59053c823e64947208f59251c825e63947209758e51c825e63d52209758f548825e63952209758e548823e64d4e208f593538823e6494e208f592538823f64546208f19
  | 2 => 0xe000878e226c884000cc1fe4b40000011e000720001440009c09c19a0ac8893434627caf843072104f20002501e0de0000001acb80002447a4a10000005a800189000000000420000009e83b0000000000000029cc8800354000000aa2ec4c40221b398294000002804dc0000013c7dcac0ab3522084406a220000449cf2266fc921fa3264d4d42080002a40021600e0901600042a480e114300083cca0f70fc6f90d2040a2200cb14f3bc85c8a8d5162861050db2ee000028004265e4e21c10d0000c10e82da19d0280030c100d81ae04c020560180000002c1bb3085690f000380008030000600803000000040b008000000b0000e0041e0200f00000008010240104009040010180c0100500000000000180000400008020280003402000000040001c0401400000030000a02402000050200101c01000000000500007000040340700c0501405010100040501c00014040080800004000090400d00404040130740903400000020300500c03000000000000c0400400004000000300001000000000600000004000180203003004010040e11000000020040e00001000000040000c06004050080701c030140302c1600c050000b01803088030040a0180303802008100069d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9c6150c43a7d814310f1d4354843c750d5110f1d439404397d8d51d0a5c63547429798e50d0a5d63943429798e5190a5d639464297d8d5090a5c63542428f9974350b1c53d0d42c714d4350b1c53909428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f65508429d98454cca756115332c715143cca3f64547328f19151cca3e64943328f59250cca7661d52329d587548cb1f5410e328f992518ca3d64946328fd91508ca3c64542328f992544ca5f63551328f994544cb1d631513297996434cb1c5490d3297195434cb1c5450d32c7152324ca3d6595032c718d540ca3e64150329798c540ca5d65d0c32c7553430ca5d6510c32c7550430cb1d54cc83297d95320ca9c644c832c7551320ca6f654c83297d8d52d065c6354b41a758c42d065e63943419758e50d065e6394a419758e529069c6350a4197d8d509065c63542418f997435071c53d0d41c714d435071c53909418f994425069d6310941c714c425071c53905418f596431071d5390c41c754c431071d53d08418fd95421069c6350841c754d421071d53d04418fd95411069c6350441c754d411067765504419b98854cc66d6215331c715143cc63f6454b318f19152cc69d640cb318f99250cc63d64943319b98b548c66d62d5231c7d50438c63e6494a318f592528c69c644ca318fd91508c63c64542318f992544c65f63551318f994544c71d631513197996434c71c5490d3197195434
  | 3 => 0x7d8c79c83d4050468000001fc330002de3bc951680f40000000017855c64a1f0001300007c1a45c88c1010004b800000000000780e92182bc1d00021211c1a98d00021c2d9ec00035800123448000e9a093f0204b090b36a410450cb2ca370a894d200244c61e727c7647504d09603c9900d342578061ba1724381a1ab344844278003e22e0928f93c20547601e2ce7b4a089a4247f46205f3aa5981f8492b6668d311c34e00000011160000460ed18e2506b97f2d677c1c1fe13a8400e1b410a318140f60da898000de1360b8c50000002842a0d802c510000000de0005a8952c07b88f94a1be5e8e592902400511169000000000000002986021900000000000000000431d43ca67c001d7000554ec0003e640ce68b20000c8839d12f6530000e5126600e50000000a40509800078cce030140000001d60467a0b7000000874db8e0000000fd8000000000012700000000225000000b88c10d252c000002c466cca8003f8308e2836278870ff8bb27e0007e1bd3cc000380000001c83718b04a5903d8172a62f8d8800404484ed01f1a02e83c91a0123840982f28e25cd614833271cd7a0c0001f4470000008387e8d42107807d9c9036000199b8000000000000000006700028c0006e8003864481522000c1cc8c94916e0009d90600009c5f8f216c0010590d0ee2102e9141247c8c09393c465c3a8f33e8000000000944c0aa0ad1867ac0011d0c0320000201062908f05a2141903106540c1540000020a118b980b0b80000019d0041151187415c0008b1b638c7c00e800032000000e63200002705640074051837340344759ce3b6000bc0003f20f4002030bc0006c82d0204cc2801a34834ca91ad1e8000110000a45402b8f129c2586d0000ec084389632b239cd91260000009d1dd2ea770718fa40e0000012c1200f00000007c60cd986c28a61c0017d1f0000d28b330a6205a19e08800c651b915000000063000804000fe0b27d46299822e5f8001920624ac2418e000000000001323b8ae0000007bc5e9d201c5590680019e574be11b0c28500008b0000007a8002045b0298000000000017425
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2401aa0040a59c8a018009239400000422678c0000180042610c1431c94354843a28e2a1aa221d1b7050e5010e8ab88a8a1e65459c75410e32838ecaa2641950d7215143cc687396a821c63075d8540c931838ecaa26418c1c76551310c60e3b2a899661071d9544c73083aed2a0651841d76950318c20ebb4a998461431c95410d30a28e2aa0869850d72151430c28ab88a8a1861191d95244010
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 666
  | 4 => 551
  | 3 => 21
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (i*5) 5
  | 6 => packedAt s3K6 (i*16) 16
  | 5 => packedAt s3K5 (i*27) 27
  | 4 => packedAt s3K4 (i*38) 38
  | 3 => packedAt s3K3 (i*49) 49
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (6+((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s3K6 (718+((h/13+packedAt s3K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s3K5 (20202+((h/222+packedAt s3K5 (17982+(h % 222)*10) 10) % 800)*11) 11
  | 4 => packedAt s3K4 (22768+((h/183+packedAt s3K4 (20938+(h % 183)*10) 10) % 728)*11) 11
  | 3 => packedAt s3K3 (1064+((h/7+packedAt s3K3 (1029+(h % 7)*5) 5) % 30)*6) 6
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffc1fffffff03ffff83ffc1fffffcf8f1ff
  | 1 => 0xf03fffe07ffc3ffc1f07fc3ffe1fc0ff473e73
  | 2 => 0xffc0ffff81ffc3ffe007ffc3ffe1ff0387cf9c
  | 4 => 0xfffffe0003fffff80003fffe0003f80fe0
  | 5 => 0xffff0000000003fffffffffc00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8104044410480000a5090044802254501850a5
  | 1 => 0x248a48832490612c0a42a429521482a9432652
  | 2 => 0x429291090d2206554084ca8265412a0a858b18
  | 4 => 0x6b2ce252483aab9a73d06223b9980c33e80de0
  | 5 => 0x8c30c39c71c333e39ce77330311030c3f6f000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8e8e8a8a8eaeae8e8e8e8a8a8eaeae8e8e8e8a8a8eaeae8e8e8e8a8a8eaeae8e8e8e8a8a8eaeae8e8e8e8a8a8eaeae8e8e8e8a8a8eaeae8e8e8e8a8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36719
namespace PEqualNP.Outside.L_meta_36719
open PEqualNP.Outside.L_meta_36719.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2c067922632a46152e8c02800240001a187af400000002b400036615824451516344471d009d090142d2880e7c21c260092e0a0001030883689407449c0105ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x4c26800380000174881b1c000f05735000008336000b43537138c4000000046580000000003e09c026500060fc001804c00002a09800000000092001b0000000001ac1800000e8763424128000000000006d3a18000221593ce000000f408000005c2c4b1b8b872520000000084083800850f0000076000500000000001400000000010000f8ce0022868002c0018c00822b1e40000001e8000000000fe28001400000388000000001a4544200000000000000ea40191ec781523874d01114880820d059540a3f169bcb65328a003e84001cc866639000420212000001212990bc000000000003b80000000380000002f800b803179f462460000000000798432092c8006606000100000400400140000040400001c442c00100014042c000404100c340404040054000c0808040818040004027ca5a1cf947439ea86873d5490f3ea6a1cf149439e28a873f5050e7ca821cf54e429f294853e5190a7aa1215794c42aea98859e5310a7aa6216754c428ea98853e5210b5ca4214f944429ea80853e54cca7aa9996750f32bb28e657551cca7ea9194f152329faa2653c544cb3a86994f950329eaa0653d539067ca520cf946419ea84835e53106baa620e794c419ea98839d531063aa620cf948419f28883b6511067aa020cf953319eaa6639d43cc6dca598db54b319faa4633c548c67ea898cf15131cea1a633e540c67aa818cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710cfd51219e2a2433f5408678a810f948421af29e815d53d033ca7a04f54f40cea9e811d53d027ca5a04f947409eaa4813f5350278a4a04f14540dda82813e541027ca9984f553309f2a4613d548c33a87184f951309eaa2613e540c27aa8186750c30b7290616d520c2eca2185d544309faa6413c54c827ca9104f552209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x30080194010008800018c80000b00680a0001e00e9a200a48ca96b800240047000040010130008758e5190a1f6354242c550d51cca3661d523287195434ca8c6250d328758e529061f6354241c350d52cc62e62d523187195434c6946150d318758c544861d63150218e580540861d63149408758c515021d63951308b189544c2346155130c350d520c31543544308758c54c821d63952208758c54c421d6395210
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 5 => packedAt s4K5 (864+((h/16+packedAt s4K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s4K4 (3970+((h/44+packedAt s4K4 (3618+(h % 44)*8) 8) % 234)*9) 9
  | 3 => packedAt s4K3 (1036+((h/8+packedAt s4K3 (988+(h % 8)*6) 6) % 45)*6) 6
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffff0ffffffff81ffff07ff07fffffe78f1ff
  | 1 => 0xf07fff03f07e1ffe1e0ff87ff878383fa73e93
  | 2 => 0xff83fffc007fe1ffe00fff87ff803fc1c7cf1c
  | 3 => 0x3ffffff8001fffff00007ffffc001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x800010208010000044120088008a0a10085025
  | 1 => 0x2519221924a430960a854853485090aca32692
  | 2 => 0x432a44486949032aa109950595012585458b18
  | 3 => 0x6a5388924c0d55cd33a0c446e6658109f00dc0
  | 5 => 0x8c630ee38e7199f1ddcee660c4460631fef000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeae8eae8eaa8eaa8eae8eae8eaa8eaa8eae8eae8eaa8eaa8eae8eae8eaa8eaa8eae8eae8eaa8eaa8eae8eae8eaa8eaa8eae8eae8eaa8eaa8eae8eae8eaa8eaa8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36719
namespace PEqualNP.Outside.L_meta_36719
open PEqualNP.Outside.L_meta_36719.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x388000a1ea0c25004008e0058000268400d362c1064e009290e10a2a4c68f1522011800a2159744252003a7cc8c0604000608002404d240040ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x81fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc3be6598774cb30bf28e617d51cc37c83986f10730ef98e61dd31cc37e81986f50330bfaa4617e548c37ca9184f95230beaa461bd548c27aa9185f15230bea9c617e528c2faa5185f94630bea8c61be418c3788318778c630ee18c617e508c37e81186f50230ef98461fb308c2fea8985f95130beaa2617c544c2fea4985f14930ef99261dd324c2fea2985f14530df20a61bc414c3be6298774c530dfa0261bd404c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa8861be410c3788218778c430ee188617e500c37e80186f50030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f719641ed32c82fca3905f54720df20e41bc41c83de43907b48720dfa0641bd40c82fea9105f95220df2a4413e54882faa9106f552209eaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620bea8c41be418837883107b88620f610c417e508837e81106f50220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483dc64907b4c920bfa8a417c514837c82906f10520f790a41ed214837e80906f50120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841be410837882107b88420f6108417e500837e80106f50020f790041fa20083da40107e48020bfaa621bf54c427ea9885f95310beaa6217c54c4378a9884f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10df20e21bc41c43ec63887d4c710fb10e21f521c437e81886f50310bfaa4217e548437ca9084f95210beaa421bd548427aa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c21be418437883085f94210dfa0421bd40843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910df20a21bc41443ec62887d4c510fb10a21f5214437e80886f50110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2086f90410de208217e500437e80086f50010fb88021fa10043ea20087e44010
  | 1 => 0xc52507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077c8620ef50c41de218837e52106faa420efd0841df21083bd42107788420df94441dfa0883f6411077a8220fd50441bf280837d501077ea620ef94c41dea9883bc531077ea420ef94841dea9083bc521077e6420ef8c841de99083bc321077ca220cf94441db28883bf501077ca020ef540419ea8083bc50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc6fca598fb94b31b7296637d52cc7daa598db54b31df20e63bc41cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518f7cca31ee994637e518c77c8318ef10631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131bfa92637c524c77c8298ef10531fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf298637e520c6faa418f7cc831ee990637e510c77c8218ef10431ef98863f6310c7ba6218fd4c431bf280637d500c6fea990df95321df2a6433e54c86faa990ef553219eaa6437c54c86fea790df94f21ef29e435e53c86faa790f754f21aea9e437c53c877c8390ef10721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fb8ca21f6994437e518877c8310ef10621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a437e53486faa690df14d21df20a43bc41487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410fb8c821f6990437e510877c8210ef10421f790843f621087da4210fd48421bf280437d50086fca7a05f54f40dfa1e81be43d037a87a06f10f40bf296817d52d037e85a06f90b40dea1681bc42d02fca3a05f54740dfa0e81be41d037a83a06f10740dfa9e81be53d037aa7a06f14f40dfa9681be52d037aa5a06f14b40df99681be32d037a65a06f0cb40dfa8e81be51d027ca3a06f54740de28e81bf31d037c63a06f4c740de18e81bf21d037c43a06f48740de10e817d549027aa9205f94e40bea9c817e52902faa5205f94640bea8c81be419037883205f94240dfa0481fb40902fea6a05f14d40dfa1a81be435037a86a06f10d40bfa92817c525037e84a06f90940dea1281bc42502fea2a05f14540dfa0a81be415037a82a06f10540fda0281be405037ea6a06f94d40dea9a81bc535037ea4a06f94940dea9281bc525037e64a06f8c940de99281bc325037ea2a06f94540dea8a81bc5150278a2a06fcc540df18a81bd315037862a06fc8540df10a81bd215037842a06fd4140dda82817e541027ca8205f94c40bea98817e52102faa4205f94440bea8881be411037882205f94040dfa0
  | 2 => 0x80000000800800008008000000000000000100600000800008004008020020000000000000c0280300e00c0000200400c01001000000038010000180000100400800004006000038020040000000000000c0400000001c0380101a000010010000040000200000000000004000018010000140080000400c0080300000002808000004010010000000000000a00000000000000000000020000c00000600c0000000200c01802002000000000060280080000401c0000300000000006002010010020120000700200600c000020000000000d000008010000020000000000400c02000000000010000020000000300600400801002000000000000100080100000000800002004000010000140180000402000001000004000000000040080100201c0000900000000805004000010010020000000100200c000000020000000400000c02001000000000010020040180100000000800000000000000020040080100000000000000000025f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210fdca421db94843bea9087ed5210edaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42be29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997790f32eea1e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cafca5197b90a32f6a1465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997790d32eea1a65ee424cbda84997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cafca41977cc832f719065dd320cbda6419734c832bf288657d510cafca0195f54032bf29e837d53d06fca5a0df54b41bf286837d50d06faa920df94e41bea9c83bf439077c8720ef50e41de21c837e52906faa520efd0a41df21483bd42907788520df94641dfa0c83f741906fca120df54241dfa9c83be539077aa720ef14e41dfa9483be529077aa520ef14a41df99483be329077a6520ef0ca419f28c83bf509077ca120ef542419ea8483bc50906fea6a0df14d41bfa92837
  | 3 => 0x340000cb1d70006e1808000000000000011a8540000000000000000000614e10a055e000002c80000000000000000064800000000001660000000000000000143000000b140000055446d4899c000000000000006b066000000000000000140000000000059ccc0000008a8f8000000988971761ec114000000060000000000000143800396000352ef000000000000000000000010290c00000000000000004da00000000000000f6a0c2280242983a19a0d932000000540000000003d4000000000000000000000000000000000b480000021c0004400080400000000758002ce17c0000b00035e20c5c9f60a8000000001b8000000000007f0000001f079c1ea8d00071000000448a20f0122000a04a6156196af15107c1f200000000000b2ca08af01e1b8e4adb000000002b71146d0000000004c4000004ec3996fa825420000000044cc7c000fb042930000d400078800000000000000006208640000046a000001ec0000005303b036000003130000012880000000095a7d31e3bc000003c281000000000270000000009d000000000000000004446ac00000000000000000004bc000000227c40000000000079000474000139db0ac000168000007e874ac93e6001680000006e9390000000000000020a000000000000018c07f156430e32540544585605060e5b947a6a0000004c97c000000000000007d40000027e5f8c40842700016f00000072800000000291138b3314c209a9200000018a000000610002ea03e92400178226000000d529a000000ce0005a84d0000000010e000464578ee1ee000000000004520000020e296095179b0194b34cead50000000003800000060ad7000184d917400034d528005ce0000000000000000000000000000002c80000020600047400000000a70a7a5a306644000c001c8d0b00a800000000000000a1000000000000c00001ba54cf497a00026c37832540000000b234200033a8c000000981a652a0008c8000001f585a16020a401b9cd00036c000c80ec000002fe00000000299000a51650000004a00000000000000000320c800000035000135800000000000000000000e800000001490f4000ac93c8001b200000000456000000415865c40021000013449a695c200000000000154000003f20d0000790001d40020028e0000c88254e0018900031228938925000000000004fe0000020953c00000000000000bb8000000000000005e1653d8000000008ab03248b9000000000001018000000000020b0e0000000000001e8f290d5d2608e1800000078480003de688000000001300006b0006a8001a55a6124090c600e0010e8e50000000000021600055000000000000000000016124e0004b40024b00052400028000a585d000000000001335ba4d000000000bac1c80000000073800
  | 4 => 0x4800000001240000006643a0003485613426722eb302f98d29c000000000000b933000466000000003760000025b000000e2800000478100001b00000000024ec0000000000b008f800208b595d82b500188000000000013f0005f81dc3c0000009cc00170000c455700000016cef0002d80004915d17600090800000c080030c2729049eb092786c52e052000bb8002141e60018d9fe0000000000048e9080000058e97ceeaf710c754002fb302aa50d8003a0000000e04c00000000c0001758a80016a6d8f5800000b60000e346c7ec002be1a0054002b10005bc0022e0628355aa3951400047ad207c0000030f57225ccdae8044a6c009b3000c5c8d0732fa448000003a2000000000001a0000000003785c17300000019a3f2040000000028c420a284b2200c00031a000000df0000fc001598000000000021f000118bfaec1dc308ed00400000179800000ae027a5d000a60000000000007599257e35caf9a950a278ad84000089483000000760000f15c600000000000650000000342c0d6800000000002550001695a00000000000000000000000002a20000000000000000000000000000000000000017200000000000000000000005820012b00000000000000000000002782c4860000001f40000000012a00123000000000002452140000000038eab00a0003fa0000020842e73c708000006798b0001ac438000000000011f28916c348002f96147a057207094390000000000000000825831c00000334a90000940002f4cf80021e0009d8004ee8dd3d00b2743dd5816139c000000000c0548448000009b09190700000000000000001378000307517000000078c002ab000190caa31380000b6a3c43422006800000001141f4000b3c002e5000000000660000002f000000000002a60008c00021200083c00091000000002110002300000000000132a9d000000c580000000000000000000000000005d538000000791620000001a40008b000000c70000000000015c1b4b50b580030ca7c508000000000028b0005ec00029000aa0001bc00001800085090170000000003fd71136534a4cc60000000018e8235e0af56e000000000002592aa9f17eb050000000000236a0000008e000000000000000007f1d90000006f943000c1058800000000000000002d0b1a585cc000e980000000000000000730712ff0000000001300000000000000000000170003447e0000000018f0000d800000000100948002750008b11e800000000000000004dc000000000011c15a61a935568bc3fe00000000000000002b64142b50f06d0002591d9ea3f000067800000000de800000000000002f2550002021da00032800000a8c3180000000178a63426b65299f708400000157000000002f63a40012524f0000000e1871e0b681a9c8000000b40
  | 5 => 0x910000000000015d00017e424d70003be000002fa5f0bb4002f5000704db8510000000011108e09802b06186260a100034ea0c00000000c6400000000000a20a31d89007419714e2dcc9800000000000005a25281e00014a0000000000000000000000000818000e2460a40000003100000027c000000000006fc001293723a800000000001108006380018700000000000000000000121654dc7c800000000000000000e400000000000bc800000346000000002640017a00052e940000000f6000000000000008e12a000000000000005640000000000116a8e58c10c000000000000010000015c001404403144f8000000012b8000b00000000007e0000004e0000001626140a2748080024c000001e644600000000000978000fd0000005
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x6410833551904208fd94410823d6510420c794c410831d5310420cd944410833551104209b596210834d5388420d9546210834d5308420d9544210823e64940208f592500823d65d0020c794f400831d53d0020cd947400833551d00208fd95400831e5350020c754d40083365150020cd545400834d53c8020d9547200826f6548020d354d200836551480209ed95200833661d5310ce58354c43366115310ce58054c423e6494f108f59253c426e6294f109b58a53c423f6454f108f19153c423e6494b108f59252c425e6394b109758e52c423f6454b108f19152c42b96090710ae58041c42b661d0310ad18540c423e64d4e108f593538423e6414e108f590538426e6214e109b588538423e64d4a108f593528423e6414a108f590528425e6314a109758c528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544423e61151108f184544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c715053443556114d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910d9584524423e6590510c7d4e414431c5390510cbd4a414432c52905108f994414431f5310510c714c414432f5210510cb1484144354538c5109d195314436452885109d195214423e65d0110c7d4f404431c53d0110cbd4b404432c52d0110ad987404423c6550110c7d4d404431c5350110cbd49404432c5250110ad185404425e63d50109758f540426e62d50109b58b540423d65950108fd81540423d60550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109d984520423f65904108f596410431e5390410c754e410432e5290410cb54a41042b960904108fd94410423d6510410c794c410431d5310410cb948410432d5210410ae580410423e64940108f592500423d65d0010c794f400431d53d0010cb94b400432d52d00108fd95400431e5350010c754d400432e5250010cb549400435553c4010d954b100427965840109dd9510043555344010d954910043b140440109ed9510043b24144010
  | 1 => 0x2ac6254540aed81515023e65cc5408f59731502ae62cc540ab58b315033451cc5408fd95315023c654c540cd14431502ba600c540ae580315023e65c85408f597215029e63c8540a758f215033451c85408fd95215023c6548540cd14421502ba6008540ae580215023d6590440cd944411023f65500409ed95401033a54500409b98854cc26d62153308fd9152cc23c6454b308fd9151cc23c6454730b358b31cc23e61952308f185548c23f64546308f191518c26f62546309b189518c23f65906308f596418c23f65106308f594418c2b960106309bd89544c26c62551309dd85544c27461551308f990524c23d6414930d3149324c23e64d45308f593514c3375110530cd144414c2b9601053097997314c2cd62cc5309b98b540c26d62d50309d987540c27561d50308f596540c23e61950308f185540c23e64150309b988540c26d62150309d984540c2756115030cb952520c32d5494830cb951520c32d5454830cd952510c3355494430d994a510c3655294430cdd92510c33464944308fd91510c23c6454430cd951510c3355454430d9949510c3655254430cdd91510c33464544308fd96410c23d6590430cb94a410c32d5290430cd946410c33551904308fd94410c23d6510430cb948410c32d5210430cd944410c335511043097596310c34d528c430d5546310c34d520c430d5544310c23e64940308f592500c23d65d0030cb94b400c32d52d0030cd947400c33551d00308fd95400c32e5250030cb549400c3365150030cd545400c34d52cc030d5547300c25f654c030d3549300c355514c0309ed95300c25e63153209758c54c823f6454f208f19153c823e6414f208f59053c834c534cb208fd9151c823c6454720b358f21c823e61952208f185548823e64d4e208f593538823e6414e208f59053882766114e209d584538823f64546208f191518825f63546209718d518823f65906208f596418823f65106208f59441882b9601062097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d208f990534823d6414d209b195324834c534c9208f993514823d64d4520cdd4441483345110520ae580414826e65c8520b358f214825e63d50209758f540827661d50209d587540823d65950208f986540823c61550208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c530826e6214c209d98453082756114c20cd95251083355494420d594e51083555394420cdd92510833464944208fd91510823c6454420cd95151083355454420d594d51083555354420cdd91510833464544208fd96410823d6590420c794e410831d5390420cd94
  | 2 => 0x6114841ae98052106b96014841ad98732106b561cc841ad98632106b5618c8418fd95321063c654c8418f994321063d650c841e34c832107366194441a798c501069d6314041ab98850106ad62140419b98b54cc66d62d53318f58254cc63f60553319b98854cc66d6215331cb95252cc72d5494b31cb95152cc72d5454b31cb94a41cc72d5290731cb94841cc72d52107318f99250cc63d64943319b98b548c66d62d52318f992528c63d6494a31d3949328c6cd62cc6318f992508c63d64942318f583544c63e64951318f994544c63d60151318f996414c63e65105318f990504c63d64141319b988504c66d62141319b988540c66d62150319e980540c67960150318f992530c63d6494c318fd91520c63c6454831b5587320c6cd62cc43197d95310c794414c4319dd95310c63e64940318f592500c65e63d53219758f54c863d60953218fd8154c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c863e6414f218f59053c871e5390721c754e41c871e5310721c754c41c863e64943218f59250c865e63d52219758f548863e64d4e218f593538863e6494e218f592538874e534ca21b358f218863e64942218f592508863d60d51218f992544863e65151218f580544863e6494d218f592534866d6294d218fd91534863c6454d219ed8153486786054d218f996414863e65105218f990504863d64141219798c504865d63141219798c540865d63150219e980540867960150218fd91530863c6454c218f990530863d6414c219e98053086796014c218f992520863d64948219798e520865d63948219b59632086e5618c821d314d32086cd63c84219bd9521087a441484219dd95210863e64940218f592500871d5310f40ab98843d02ad6210f40a798c42d029d6310b40cb54842d03365110740ae58353d031d5314f40ab98853d02ad6214f40ae58053d02b960d4b40a798c52d029d6314b40cb54852d02b96014b408fd9532d023c654cb408f99432d023d650cb40e34c832d029e63d4740a758f51d02ae62d4740ab58b51d02b960d4740ae58051d023e65cc7408f59731d02ae62cc740ab58b31d023f654c7408f19531d023e65c87408f59721d029e63c8740a758f21d023f65487408f19521d033651906409b988535026d6214d40c714d43502ae6210d40ab588435025e63149409758c525032c5250940a798c425029d63109408f99741503345190540ae58253502af6254d40ab18953502b76154d40ad18553502bb6054d40c754c53502ae6214d40ab58853502b96094940a7d8d525029c6354940add8552502b46154940aed81525029e6314940a758c525032d52149408fd95325023c654c9408f994325023d650c940e34c832502b96094540a7d8d515029c6354540abd89515
  | 3 => 0x71175000370000722b0000001c4000000002e315800098a79536a582700180200200c0c8000120080200e00205005012030000000130180040180100000c018010160380100401402400000012020020340060000180002a008000030040040000800201c0000407202001800000004008020040640100404804803005002058018040000140c00d0020000000000009c00003004008090010000080381801201c0a80c00401c02002012118048100120100280700a0000100201002c06002002000010010020000080000200802005002004000000180000200604a0000880100400c0001d00001c0101d00600c0380e00400000806022000008040040280380100a06c050170000040480000400c1000a0000001100000801000009054004040010160640300400a080008030000100f00000401c0580b016040000010020480100d022008020010260000200000400c0580600404c0b00c00400c000020000040300000200400800000000000010000140000003e01404804000004010000000063f6550c4397d954310f2f4354843d390d5210f2d4354843d350d5210ead6210e428f9974350a3d6590c42c754e4310b1d5310c42ab5884310b1d53d0842d354e4210a3f6550842c754d4210a6f6550842d354d4210a7661d53329d58754cca3f64547328f19151cca3e64943328f59250cca7661d52329d587548ca3f64546328f191518ca3e64942328f592508ca3e61d51328f583544ca3e64951328f994544cb1d6315132cb588544ca3e61151328f580544cb1c5490d3297195434cacc6250d32cb152424cb8e43909329b195424cacc6350932e350d424ca3e64d45328f593514ca3e64141328f590504ca7661141329d584504ca3d65950328f986540ca3d60950328f185540ca3f60550328f990540ca5e63150329b988540cb1d54cc832cb552320cacd638c83297d95320cb1d544c8329bd95320cb2d544c832b3d95320cb4f654c832e3d91320cb8c644c832d3d51320cb8e544c832d3551320cb8d544c832c3551320cb4d32944328fd91510ca3c64544328f992500ca3d6494032d34c9500ca6e6294e419b58a539071e5350e41ab98843906ad6210e419798e529065d6394a41cb949429069e6310a41a758c42906ae62d4e41ab58b53906b661d4e41c7d4e53906ae6294e41ab58a53906b66114e41a798f529069d63d4a41ad987529069e6394a41a758e529072f5294a41ad984529063f654ca418f195329063e650ca418f594329078d320ca41a798c509069d6314241ab98850906ad6214241c754c43106ae6210c41ab588431069e6310841a758c421072d52108418fd9541106776550441ad987531071d5314c41ab98853106ad6214c41ad98453106ba6014c41ae58053106b661d4841a798c521069d6314841cb54852106b6
  | 4 => 0x24a2ae14c8994e496c16c7fd582af2a4b0d7e1a31da5b8db02142c5a93882e22a3095e87956c18850abb3764ec4a000000750de8bc2ba8613385858e32c2ba1b0007450a2cb5b40001a800120b580006e382000002955fca916622100000000000000000001ae4e054d3490f1d89981e17a25836c0800031800175800470350000002783fc7d8e1000a34890005ce0017501a5a00c17a000316000c380032cafd53a4a6104280001e0002bc122010a28f40000024e82cbf0003221d82d23f336c14ba0a30147d91380008e9f03f95053ac28e28502e23102f800000b210727e0040007818514e890b78de2729fc828002da2f4aa000000608f100029c0000004300000000000000001648000000000016b1e437c590592bc2a0c209c1905e14308c02c7a0212e80f87a800000000211368003d646d1b2433f40007b0000007812b2090000000000000041c3a0aa0004e000000000000d000005a001000003a60005d80008c001088340008495707744a3915b8d70009a910000046b448c0912aa6704d1de25e8cced91a2208f8f81a93a4864000da48e740478c002aa64d29f5374000c30ca35e9352883f32865d55000000b356224b51e000c91721023dc848200700e4001890008703f2045bc879540695dcbb4db80c038bc4822d34b6968a5a6c3308bc971900aa960692d22449e8192b20000000430704a1200702b254000e68455ae0480000000000037a4f00087518ae626eb80000000006b400103044b385a8000000012014c15600177a9e0928086a8d3556000f3a230da0007c29711cad5169b35262e4eb2a6572019111f319800000083000438000003500014408709430c002c523ca1d6a8651d0854ec98147200038995348000758820004904a9e34ae000e4000252a897b8805d2c317914d5c87f8000a919e000b49d5000001130f13443bce103b000930c68004bc4fc001e136aaf0a1114396474331d74a40003aa4e00080cde1a75b2444b80cd07a9087980002e1f42005230004c809490e6a04d5aa518cad00a2280029d56da0c3b00e80f8e215c6213c10c4642f8a52594a87c4bb0003340017b0002c002cbd8041f24d8b1a91280bfc63b0914063c001c71683f03da130004a0001ce3f8795280995be50c2b0680007e4f21f2240470442f01ea2cc00000000000f60002001506b00015a0344f8005f0c042ea34000504b092d474170898001708dd502410002fc001652420000000000062800037000bec0380040a18000207530001801564d09bd3b8674b898438000508b94770d129e9896e80f5fa0bce513324c5e53928c43e14c4b86c5627b90792510c6b11626b00059cfb86b6169cc209cc520c102222e1f4bd4001620004ac000000004f960000000000d51b42889180c8005f2000000002900010d29457c191598ea0000a9
  | 5 => 0x38664c000000000000000022e0016e15b00055d7d0004ec47ccf00000001556164000ae8841ed34c769370e94560000023b0000013d8a41c65f00024437e274701990005f4000a24528a96510b000074001ef0582340015f000000001dc04c77c001fd0000003d1592cc000188c52ee248140a6512b18002805e6000c1800000000000091cc000d80035d8000002cf5528c01380012c000000000f09d00029a50426c351f428e0000003e28c0456a2c109a00000302000a8c0005b1ce2240008b174338b4206000a383080048a2c09a8000368d4649cf410954c708a0007ec98000162000001b92b43f40019f478ab4000a54c694cae000000774000b70000000c00000048cce8001ca000429a1420b616128323285c498293d26c41b2b827a5fd2fa482a24e88b0003641313e8fe096a7d429c61307e06ca0a5165ccdf1c0000a498326020c374318d80002787a00060600000000000a290690d0bca709a0c106613d2e8d02046e0f31325429
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x69085586418030b498d3800e8f4aac01b500910a02bd02e4ea92361c2401f2078a8018011a668dc02900c8a040021a911648b000cc001762cc3800f000450010043870420380000580cc1ac6b10a89950d75951320ca873b2a899065431d9544c832a18e2aa2641950f70551320ca86b94a6a1c83435ce5250a41a1ce5a9ca720e0f5358a539068739ea5294838358f5294a41a1eea9906520e0e654c83290706a9ac4218838358d5210841c1aa6b10a620e19535805310706b1aa4290838a5496014841872e032a6420e0d654c83210686ba4a499463435d2534ca21a1ae829a6410d497014d3208706a9ac421e818358d5210b40c1aa6b10a7a060d6354852d0306b2a6419681435c85350d40a1ae629284a050c7254c535028a38aa629a818354d6214d40a18e6a90a4a060d63548525029238aa4292810d1c5650c940a18ea99064a060d654c83250313310a398a818598c51c8540a1ae8292649863051580414c286ba0a699641435d0534c920c60a2b0082906326158054c430a298c2a0221891486150110c32a6b008208629525804104388a9a8088021c85494044010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x602000804a00906819d9544c83280e87995320ca41a048154d6214d40c05631c5521494080c87595320c940a0481595320c940
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 6 => packedAt s5K6 (788+((h/14+packedAt s5K6 (704+(h % 14)*6) 6) % 53)*7) 7
  | 5 => packedAt s5K5 (24564+((h/267+packedAt s5K5 (21627+(h % 267)*11) 11) % 1700)*11) 11
  | 4 => packedAt s5K4 (32538+((h/260+packedAt s5K4 (29678+(h % 260)*11) 11) % 1031)*11) 11
  | 3 => packedAt s5K3 (2870+((h/18+packedAt s5K3 (2744+(h % 18)*7) 7) % 68)*7) 7
  | 2 => packedAt s5K2 (368+((h/2+packedAt s5K2 (360+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xe0fffe1fffffff81fe1fe1ff87fffffd18f1ff
  | 1 => 0xff07ffe07e1f87fe1fe1fe1ff870707ee73e93
  | 2 => 0xfff83fff801ff8ffe001ffe3ff807f8307cf1c
  | 3 => 0x3fffffe000fffffe0003ffff8003f80fe0
  | 4 => 0xffffc000000000fffffffffc00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x28000204100400004402402400941420085025
  | 1 => 0x42518443242908160a20a20988212158632692
  | 2 => 0x8432a8890d5241aaa1113542d5024b0b058b18
  | 3 => 0x16a53112490352cd33541103664b0213b00dc0
  | 4 => 0x18c621dc719c64f1dd99d990440c0c63def000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeee8eaa8eee8eaa8eee8eaa8eee8eaa8eee8eaa8eee8eaa8eee8eaa8eee8eaa8eee8eaa8eee8eaa8eee8eaa8eee8eaa8eee8eaa8eee8eaa8eee8eaa8eee8eaa8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36719
namespace PEqualNP.Outside.L_meta_36719
open PEqualNP.Outside.L_meta_36719.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10050f029a7a316910001b8000cc01e00e17a012855001e0400a58d5ca600183ae6c219343689499487c5bb06000302a0022b289493a62400164660e0d2638b9d4e061868100040000e0c4800c08700263c180027fd5007fe54027f55007fc54017fd4c057f53017f94c05fd53015f54c05fc53017fd0c05fe43017f50c05fc43027fd4803fe52027f54803fc5201ffd0803fe42007f50803fc42017fcc803fe32017f4c803fc32027fd4409fe51027f54409fc5101ffd0401fe41007f50407fc41017fcc405fe31017f4c405fc3100ffc8401fe21007f48403fc21027fd4009fe50027f54009fc5001ffd0001fe40007f50007fc40017fcc005fe30017f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a200eff19510025f8ca8803b7c65440093e32a2000ffd9110005fec888003bf64440015fb22200dff9911001dfcc888003fd64440017eb22200dff1911001df8c888003bc64440075e322200effd511006ffca88803bfd544401bfe2a2200cffd8d10065fec688003df63440016fb1a200cff98d10015fcc688033fd63440197eb1a200cff18d10015f8c688033dc63440056e31a200cffd4d10066fea688033fe5344019fea9a200cdf54d10067f8a688033ff4344019ff21a200cff50d10067f88688003ff62440017fb122000fbd8910005dec48802ffe62440037f3122000ff58910005fac48802ffc62440037e3122000fb1891000dd8c48803bff5244017ff292200eff5491005ff8a488037ff4244017ff2122000ff5091005ff88488033ff3244017ff192200cff4c91005ff8648803bff514401dff28a200eff54510077f8a288037ff4144001ff20a2000ff5051006ff88288033ff3144019ff18a200cfd8c510067fa6288033f53144019fe18a200bffc8510007fc4288003f62144001fe90a2000fd4851005ff8428803bff504400bff282200eff5411002ff8a088037ff404400bff2022000ff5011002ff88088033ff304400bff182200cff4c11002ff8608802fff204400bff1022000ff4811002ff84088003ff1044001fd8822005ff8411002fec2088017ff650400b7fb282005ff99410025fcca080177e65040093f3282005ff5941004dfaca080177d65040013eb282005ff1941002df8ca08017ff640400b7fb202005ff9901001dfcc808017be64040075f3202005ff59010005fac808017bd64040015eb202005ff1901002df8c808027ff5404011ff2a02009ff55010047f8a808017ff630400b7fb182005ff98c10015fcc608017de63040056f3182005ff58c1003dfac608017dd63040016eb182005ff18c1002df8c60801fff530400fbfa982007ff94c1003ffaa60801f7d530400ffe2982007ffd0c1003ffc860801ffd430400ffe2182005ffd881002dfec408017fe62040037f3102005fb9881000ddcc408017fd62040017eb102005fb58810005dac408017fc620400b7e3102009ffd4810037fca408027fd520400dfe2902008ffd0810037fc8408003fd420400dfe2102007ffcc810037fc640801ffd320400dfe190200abf9841004ffea208027fe5104013fea882009ff14410047fe8208003fe4104001fea082008ff1041003ffe620801ffe310400ffe9882007ff0c410037fe4208003fe2104001fe9082006ff0841002dfcc008017ff500400bff2802005ff5401002ff8a008017ff400400bff2002005ff5001002ff88008017ff300400bff1802005ff4c01002ff86008017ff200400bff1002005ff4801002ff84008017ff100400bfb8802005ff8401002ff42008017fd100400bfa8802000fe44010
  | 1 => 0x7ef2148003ff10a4001ff48520007da4290007fc21480037fb024018ffd412002ffca090063fd504800bfe2824017ffd012002ffc8090003fd404800bfe2024016ffcc12002ffc609005bfd304800bfe1824001ffc812000ff64090017fe204800bf71024005ff0812002fd84090007f8204802bffb2e2015bfd97100affccb88012fe65c402bfeb2e2015bf597100aff8cb88012fc65c4001ffb262000bfd93100a7fcc98800efe64c4001feb262000bf593100a7f8c98800efc64c402bffaa62014ff953100affaa988053fc54c4015ffb1e200abfd8f10057fcc78800afe63c4015feb1e200abf58f10057f8c78800afc63c4015ffa9e200adfd4f10057fca78802bfd53c4015bea9e200aff14f10057fe878802bfe43c4015fea1e200aff10f10007fec588002ff62c4027ff3162001bf98b10007fac588002fd62c4027fe3162001bf18b100affea58804ffe52c402bfea962013ff14b100a7fe858804ffe42c4001fea162013ff10b10057fe658804ffe32c4015fe9962013ff0cb100affea388057fe51c402bfea8e2015ff147100a7fe8388003fe41c4001fea0e2014ff10710057fe638802bfe31c4015fb18e200aff4c710057ea638802bfc31c4027ff90e2000ff88710007ec4388003fd21c4001fa90e2013ff087100affea188017fe50c402bfea862005ff143100a7fe8188017fe40c4001fea062005ff10310057fe6188017fe30c4015fe9862005ff0c31009ffe4188017fe20c4001fe9062005ff0831002ffecb08016ff658400bff32c2004bf9961002ffacb0804afd658400bfe32c2005bf1961002ffec908016ff648400bff3242003bf9921002ffac908002fd648400bfe3242005bf19210097fea908047fe5484025feaa42011ff1521002ffec708016ff638400bff31c2002bf98e1002ffac708042fd638400bfe31c2005bf18e10087fea7080437f5384021ff29c2010ff54e10086faa708043fc5384021ffa1c2010ff90e10087fa8708043fc438400bffb142005bfd8a1002ffcc508006fe628400bfeb142000bf58a1002ff8c508016fc6284025ffa94200fff94a10097faa50803ffc5284023ffa14200fff90a10007fa850803ffc4284021ff994200fff8ca10087fa650803ffc32840197eb0c2012ffd4610097fca30804bfd5184025fe28c2011ffd0610007fc8308003fd4184023fe20c2010ffcc610087fc6308043fd3184021fe18c200fffc8610007fc4308003fd218401ffe10c2005bf9821002ffea108017fe508400bfea842005ff1421002ffe8108017fe408400bfea042005ff1021002ffe6108017fe308400bfe9842005ff0c21002ffe4108017fe208400bfe9042005ff0821002ffe2108017f71084001fd884200effd9510075feca880037f65440013fb2a200eff99510025fcca8803bfd654401d7eb
  | 2 => 0x4001ffe84a000fbf4250007ff2128003ff509400077a84a000ffc425003bff992801cff8c9400effa64a0073fc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8000bf185400f7fea2a007bfe515003dfea8a801eff1454001ffe82a000fbf4150007ff20a8003ff505400077a82a000ffc415003bff98a801dff8c5400effa62a0077fc3150039ff90a8000ff88540007fa42a0073fc21500077fb02801effd414002ffca0a007bfd505000bfe2828003ffd014001ff680a0017fe405000bdf2028005ff1014002f7880a000ff8405003bff9828005ff8c1400effa60a0017fc3050039ff9028005ff0814002ffecb10016ff658800bff32c4004bf9962002ffacb1006efd658800bfe32c4005bf1962002ffec910016ff648800bff3244003bf9922002ffac910002fd648800bfe3244005bf192200dffea91006bfe5488037feaa4401aff1522002ffec710016ff638800bff31c4002bf98e2002ffac710066fd638800bfe31c4005bf18e200cffea7100677f5388033ff29c4019ff54e200cefaa710067fc5388033ffa1c4019ff90e200cffa8710067fc43880037eb144001ffd4a2000ffca510007fd5288003fe2944001ffd0a2000ffc8510007fd4288003fe2144001ffcca2000ffc6510007fd3288003fe1944005ffd862002ffcc310002fe618800bfeb0c4000bf5862002ff8c31006fff5188037ff28c401bff546200dff8a31006bff4188001ff20c4000ff506200d7f88310067ff3188033ff18c4019ff4c6200cff86310007ff2188003ff10c4000fb8862000ffa4310007fc2188003f610c4005bf9822002ffea110017fe508800bfea844005ff1422002ffe8110017fe408800bfea044005ff1022002ffe6110017fe308800bfe9844005ff0c22002ffe4110017ef2088003fd9044005ff0822002ff04110063ff65480317fb2a4000dfd9520004feca90063fe65480097f32a4018ff595200c5faca90063fc65480097e32a4018df19520024f8ca90003ff64480017fb224017ff9912001dfcc890003fd64480017eb224017ff1912001df8c890063ff544802fff2a24018ff551200bff8a89005bff634802d7fb1a4016ff98d20015fcc69005bfd634802d7eb1a4016ff18d20015f8c69005bff534802dbfa9a4016ff94d200b7faa69005b7d534802dfe29a4016ffd0d200b7fc869005bfd434802dfe21a4005bfd892000ffea490007fe5248003fea924001ff1492000ffe8490007fe4248003fea124001ff1092000ffe6490007fe3248003f71924001ff4c9200b7da6490007fc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4000bf185200c7fea290063fe5148031fea8a4018ff145200bffe8290003fe4148001fea0a4017ff105200b7fe629005bfe314802dfe98a4016ff0c52000ffe429000
  | 3 => 0xfb224200bfd912111ffcc89080efe6448401feb224200bf5912111ff8c89080efc6448449ffaa24223ff95121127faa89088ffc5448445ffb1a4222bfd8d21117fcc69080afe6348445feb1a4222bf58d21117f8c69080afc6348445ffa9a4222dfd4d21117fca69088bfd5348445bea9a4222ff14d21117fe869088bfe4348445fea1a4222ff10d2100dfec490807ff5248403ff2924201ff5492100ff8a490807ff4248403ff2124201ff5092100ff88490807ff3248403ff1924201ff4c92100ff86490806ff6148449ffa8a4224ff94521127faa290893fc5148447ffa0a4200ff90521007fa829088ffc4148445ff98a4222ff8c521117fa629088bfc3148403ff90a4201fdc852100ffc4290803ee2148403fe10a4201fb0852100fe84290803ff60484017fb024200ff98121007fac090803fc604840b7e3024224ffd4121127fca090893fd5048449fe2824223ffd012111ff8809088bff3048445ff1824222ff4c121117f86090807ff2048403f79024201ff0812102ffecb20016ff659000bff32c8004bf9964002efccb200127e659000bfeb2c8021bf5964002efacb200027d659000bfe32c8005bf1964001dfac92000fff5490007ff2a48003ff5524001ff8a920017ff639000b7fb1c8005ff98e40015fcc720017fd63900417eb1c8005ff18e4002df8c720083ff5390041bfa9c8020ff94e40107faa7200837d5390041fe29c8003ffd0e4001ffc872000ffd4390007fe21c8005ffd8a4002ffcc520006fe629000bfeb148000bf58a4002ff8c520016fc6290043ffa94801fff94a4010ffaa52007ffc5290007ffa148003ff90a4001ffa852000ffc4290041ff994801fff8ca40107fa652007ffc329000bffb0c8005ff98640005fcc320017fd61900017eb0c8005ff1864010ffea320087fe5190043fea8c8021ff1464001ffe832000ffe4190001df20c8003ff5064001ff8832000fbc4190041ff98c8020ff8c640107fa6320083fc319003fff90c8000ff88640007fa432007ffc219000b7f3048005ffd424002ffca120017fd509000bfe2848005ffd024002f7e812000ffb409000bfe2048005fe1024002ffe6120017fe309000bfe9848005ff0c24002ffe4120017fc209003dffb2a801ebfd95400f7fccaa0012fe655003dfeb2a801ebf595400f7f8caa0012fc655000b7fb228003ffd51400f77ea8a000ffe5450007feaa28003ff1514001f78a8a0077ff635003b7fb1a801dff98d40015fcc6a0077fd635003b7eb1a801dff18d40015f8c6a0077ff535003bbfa9a801dff94d400effaa6a00777d535003bfe29a8003ffd0d4001f7e86a000ffe4350007fea1a801def50d4001ff886a0003ff62500017fb12801cff9894000dfcc4a0003fd6250039fe3128001bf189400f7fea4a0073fe525003dfea92801cff149
  | 4 => 0x80ff74190407fe20c8203fd10641167fe63208b3fe3190459fe98c822cff0c64115ffe43208affc2190401ffb048200ff9824102dfcc120803fd60904017eb048200ff1824116ffea1208b7fe509045bfea84822dff1424101ffe812080ffc4090407de204822cffcc241167fc61208b3fd3090459fe184822bffc824115ff841208abff65504557fb2a8200dfd9541004fecaa08abfe65504097f32a822aff59541155facaa08abfc65504097e32a822adf19541024f8caa080eff6450407ffaa28203ff9514101ffaa8a080ffc5450453ffb1a8229bfd8d4114ffcc6a080afe6350453feb1a8229bf58d4114ff8c6a080afc6350453ffa9a8229dfd4d4114ffca6a08a7fd5350453bea9a8229ff14d4101ffe86a080ffe4350407fea1a8203ff10d41007fec4a0802ff6250451ff3128201bf98941007fac4a08a3fc62504037e312822affd4941147fca4a08abfd5250451fe2928203ffd094101ffc84a080ffd4250407fe2128229ffcc941147fc64a08a7fd3250451fe1928203bfd8541157fea2a08abfe5150455fea8a822aff1454101ffe82a080ff74150407ff20a8200ef9054101ff882a080fbc4150407fa20a8229ffcc54114ffc62a08a7fd3150453fe18a8228ffc8541147f842a0803ff60504017fb028200ff98141007fac0a0803fc605040b7e302822affd4141157fca0a08abfd5050455fe2828203ffd014101f7e80a080ffc4050453ff9828229ff8c14114ffa60a08a7fc3050451ff9028228ff0814113ffecb1089eff658844fff32c4204bf9962113efccb108127e658844ffeb2c4227bf59621006facb108027d658844ffe32c4204bf19621007fec910802ff648844dff3244203bf99221007fac910802fd648844dfe3244203bf1922113ffea91089bfe548844ffeaa44226ff1522112ffec710896ff638844bff31c4202bf98e2112ffac710896fd638844bfe31c4202bf18e2112ffea7108977f538844bff29c4225ff54e2112efaa710897fc538844bffa1c4225ff90e2112ffa8710897fc43884037eb144201ffd4a2100ffca510807fd5288403fe2944201ffd0a2100ffc8510807fd4288403fe2144201ffcca2100ffc6510807ee3288403fe9944225fb4ca2100ff86510806fe618844fffa8c4227ff9462113ffaa31089ffc518844dffa0c4200ff90621007fa831089bfc418844bff98c4225ff8c62112ffa6310897fc3188403ff90c4201fbc862100fee4310807fc2188403fa10c4200ffd8221007fcc110816fe6088401feb044200bf58221007f8c11089fff508844fff2844227ff5422113ff8a11089bff408844dfe2044225ffcc22112ffc6110897fd308844bfe1844201ffc822100ff84110807ec2088449ffb2a4224bfd9521127fcca90812fe6548449feb2a4224bf59521127f8ca90812fc6548401f
  | 5 => 0x700400000007008010018070000100400902800003804008000000010060040700000600804803002000008000080000000000401c038070000380180000c0200000100000001007028080008090020140300000003c0080100200001003000030000000000080181000c00000013000014000010020000080600a00000800000000008060020180e801006010020000040000080300a0040200008804c0000800a004048040000600780200000005808004000020020000440380000400c0200000005c0000000600c0180000c0000080000203c0e00100200000002002000060000040080501b0120b80100000000c00001016004010010020000280400a00c000000020140000100400c0000b002000000010000140200c0000380800200000c000050002fffd954217dfecaa10037f65508013fb2a842fff99542025fccaa10bffd655085f7eb2a842fff19542025f8caa10bf7c65508093e32a8401bfd914201ffea8a100ffe5450807df2a28403ff5514217f7aa8a100ffc545085dffb1a842ebfd8d42177fcc6a100afe635085dfeb1a842ebf58d42177f8c6a100afc635085dffa9a842edfd4d42177fca6a10bbfd535085dbea9a842eff14d4201ffe86a100fbf4350807ff21a8403ff50d421777a86a100ffc43508037fb128401ffd494200ffca4a1007fd5250803fe2928401ffd094201fde84a1007fe4250803df2128401ff1094200f7884a1007ec4250803ff9928401ff8c94200fdc64a1007fd325085df69928401ff0c942007fec2a1002ff6150801ff30a8400ff58542007f8c2a1002fc615085fffa8a842fff9454217ffaa2a10bffc5150807ffa0a8403ff1054201f7882a10bbff315085dff18a842eff4c542177f862a1007ff2150803fe10a8400ffd8142005fec0a1003fe6050801feb028400ff1814202df8c0a10bfff505085fff282842fff5414217ff8a0a100fff4050807dfa028403ff10142177fe60a10bbfe305085dfe982842eff0c14200ffe40a1007fc205085bffb2c822dbfd964116ffccb20812fe659045bfeb2c822dbf5964116ff8cb20812fc65904077eb248203ffd524116f7ea92080ffe5490407feaa48203ff1524101f78a9208b3ff63904597fb1c822cff98e41015fcc7208b3fd63904597eb1c822cff18e41015f8c7208b3ff5390459bfa9c822cff94e41167faa7208b37d5390459fe29c8203ffd0e4101f7e872080ffe4390407fea1c822cef50e4101ff88720803ff6290457ff3148201bf98a41007fac520802fd6290457fe3148201bf18a4116ffea5208affe529045bfea94822bff14a4101ffe852080fbf4290407ff2148203ff50a410077a852080ffc4290459ff994822bff8ca41167fa65208affc32904077f30c822dffd464116ffca3208b7fd519045bfe28c8203ffd064101f7e8320
  | 6 => 0xc0002980000002bc09275437082a4ac23667616466e6066828741c67200003800545fe4962a61dc1489468c634c79e9aa0006282b64304440000002148707f06c61c47341a05e81f04ea9de11e8048388b800078006e51849a00000078425000043a8ca0006c22307ae32200016038e2cc8d81401de0003de91255236e20c30471e48e1d06460002aa00022c5c60003307aa04874234a5640000081e689a0009ae82093e00022a1126744dc0007885ec7b09440001262320002524387f83d62044e42d80008c00f20003440006320000004b82640866f074422e59e7b60005920000008dc0000002fa0008a25ea0806f800077800037e00268800071a4d000082c1a413405e66c6380b051c58e0004b61b844a1925e03720000007228d61f20000002d27320004aa30800031200000000080e00084e0005ee3cc0004d24d684a0001e85b600000009a45c50a3e815a0464c80508b006200000000090800002033c9a00da9024000004e000051a77653649000007c7920000000f05e62c81240000009ca0000007f600000050077c24681201863c2ae5760006b88261ce4b00001fa9380006ce3241d88100605161160000000000004840008e60005745ae0e40001783840005be7c67be01415200005600092c0000d465c89e0782fc4240000000000000000000009700000000000960004ec7ba00042a0000000000008060640007380000000004e200031e9246522dc0005d800000069692e5ce33403a95e00021a6160008f462600040281454841c09e00014e9489e09344626367a24bc00000000005c00033a7e46e40000002429906546d000055456688a6484ae29a68e2c600066200012a4cc2e00004f40006ec41e80c3c204003200045091e0ea6580009c44106ac2e80001ba00000000000059c29200001294000035e5ba42661a47879676c3640006860000007ee3186782de3f64c40000000000000000000008fe5f400028e5b04480000000006d800000094a0002d404e0000aa49c0001887101ec3560000000000401200c09801004000008000120000181200a01400000000004088000000100000000a000000050020000000501800c0180000200c0000000000c00001004000000010000000001000000000002008020028030020200180b00000400816000024008000040300080500400000015002008050020000040400302e00c030030000040200200a0000100c00e0000d8020120000000302400c000020160080000300a0280280401e0080400100800406000004004008060000040980a0000000380102a014000000160240001b012000000060000000b00400000c0000201a00402006000000068010020000000300201801000004030038000020200000500c008000010000080000300600804801000000038080060040100
  | 7 => 0x29e09c07a8c42e60000000160dc16600000019c0000003c84127e26da79a3743f05082c20008326900000008cc5426302088fc2847bc9d04524a66bc9922680001e217c3322249801ae7721187280009986dc3200000000e240636a48800053e0008de0000d200000007600005853c00000016269e0000001da9d828600000054c4da5a60000000002a822226a61c00000035a00089037c46a6b20988be8962a09a88881d619e8081c297c97408821857217400052a5f636800000000070a47e7300000000009da00000000000000000000034069800025c22682e15e0a06c000034e0002f47148a40000000003023e40001fc5f000079c00000046400048c29038c8f02b45069720007620007a65306c83c633e8b22ba58600000021e95c18060218c0fe25e3b800000078e7401228d47ac0000000004ce9b400002a32677045a90610c0000003a886a1f462000054468c71c94252e5d68867a811c00099a1a26105b220244e0004ca1d47ce5404fe6340001b687c5d085a52089c3bc9840001b47520000ac6b42d60000009c01320000001983d00000000000000000000000005bc0669645320004807661720002fe1104f62100007b44943a03ca5800000007180002600000006a26d64566660003360008ae00000047a00077408281646e91013e95a4a200074a00000000000000019052800000098a9d483c0008ee0c000000000000000093282891a6c41684ee68a8a06ae00081e00000000000003600039e5b892a0063884989886a62544224fc0cc1d259a00044c9260008bc20091613806c1767902a47e02744720003e60007482ea00073c97831a6500003fe8e25a81f63ec0003be6a498c8369c20908f841a64c9865148622122566de3fc69a3ac50e24e8d291c0007ec4705707f430c3f47680008b67164160005888f23e03dc3945d212e0c69500b662c3165cc4661cc0a227660e6a82e46248541140004b49dc39a9760000e857c0000009ac00075678a00000067e4a866a58247400000000000000000096a2f80003d464a00035c16a3862800d054e01e4de7da4407a003c5e43b06a046c6429584144fa0000000008aa00000020600000000035473a02c7e60006042b21ca0007c40004f00ba75a1421582821940009b60000006840000006ca0003ae0000000007d08e443696255c0001860006123505de5c27940006cc7040b44084460003a404c0000009bc3b257a00075800000074e56208e81a8400a63068588c232c12c86890a0e02ee7008527fc69210000000000014685e8349660000006d40007d484400092218200058a00045400037a00024400005a2347ea8a81be4a02f075c3a20f899c00000072e00057e80a40a5c832a0001443aa1e40841b09545fa5023960d60008c80000c40720001a61ea0000f413a00000040e74
  | 8 => 0x97e0ae1aa40c6140004a49365220004d400000039c8fa0007d63140002e27fe67216e6f20003909962b884c2580007065da86c55085c0000007466fa65a0004340004ba0004c000010235800000000000038a1844287863489a273e17a00019a6e01083429b894e0be2da22861e0108ea92888e3602f65d46fe70803e3b61c000025a6944322ac9cc70c6706005686e85103820345c41a86ba67c2380fa43e23c0ca7e813628c2c064e76000000000088206a78279848683e00050445e0940003463e20007360004180004e60000004920000007260001f800083a0003d80fc36c6f40000ee1301c823a97a00087600a6fc78c52c0000002ce8b40004b22ec0043ee31c0000007b210400014c00000027c3620007d899e53800000000000069c00000000000072400012860a8780008ac0c80b800087a86e3284685340a496c24a00070e77a6b60004820000009829b09be19604487e86427e26c17e0000000000ce8ce00028a00018a5aa5460000003c43780000005a40000000000000008da3522be7f251200000000000000072c00010e0000006e600090e26e00089276e52693a2b06646d290c4f27a41060004be5947020bc0001e00007dc0001fe5dc6ee00000000000030a8660000001b20000000000000008561ee00065e00089400000000062200077e00000015c7d25ca00088000008a0005960003a600042c9180de17058c00055800011a0000ec0003c08e04c60a826698e0f60221205a09ce64030e83020e7505f224800000000000000002891400081c53a0000000005c000000056e18e8420009944040000c26aa9ba76a8728608ec0008464768982c462a7cc9688f63ce00049e55e00000001a0009042709d60d821c0006b00520748d000000015456a94c4d813c0004f80000000000000007c00006e231000000000047c23e0000000005ac8024e80000004c200000001c8ba36624c00016c04a67a00e2720006685a20006ea9560007120704580000003f800000043c06802421663a7c22784600009a67fa0000001507b857800030000050c0000000000000000000000000005560427c800002e8e80005f88186f60000003ea6be32e00000060c0003b429c5b40000000005900b200000000000096e27a48a0002a200000000020a0000003920000005241bc9b200010a2f20000003fa75e5fc8503ba07e00082293003000063e88c95200000000054a0000008a60002946809c83f20008481563da0262d000056000093c7640007de61800024000059837665600092000039888456c5e21ac00044251e0007ca00055a0000006442960004200e63383d266014a2620002ca00072a2202888009a49c660808c9609d200000c62e90082442e038584
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc325881000cff715881000cfd7158810034fc7158810036ec215881002cff705881002cfe705881002cfd705881002cfc705881002eee205881002eec205881002ef7105881002ef51058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef53588100066f5358810006ee5358810006ed53588100066d5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810036ef7158810006ee7158810006ec7158810006ef5158810006ee5158810006ed5158810006ec5158810006ef4158810006ec4158810006ef3158810006ee3158810006ed3158810006ec315881002eef705881002eee705881002eed705881002eec705881002eef505881002eee505881002eed505881002eec505881002eef405881002eee405881002eed405881002eec405881002eef305881002eee305881002eed305881002eec305881002eef105881002ee7105881002eee105881002eed105881002ee5105881002eec1058810004ff765081002cfe7650810004fd765081002cfc76508100057f755081004d7c755081017e7e65508100067d655081001ebe6450810006bd6450810176de6350810006dd635081000eee6250810006ed6250810005f77150810005f471508100a4ff769041002cfe769041001cfd769041002cfc769041016e7e65904100067d659041001ebe6490410006bd6490410166de6390410006dd639041015eee6290410006ed629041002dfa7090410005f970904100a4ff76504100057f755041004d7c75504101567e65504100067d655041001ebe6450410006bd645041014ede6350410006dd6350410146ee6250410006ed625041009cff768841002cfe768841000cfd768841002cfc768841004d7e75884100057d758841013e7e65884100067d6588410136be6488410006bd648841012ede6388410006dd638841000eee6288410006ed628841009ef6618841002dfa7088410005f9708841009cff76484101267e65484100067d654841011ebe6448410006bd6448410116de6348410006dd634841000eee6248410006ed624841009ef6614841002dfb7644010006fb7644010004fb76440100077b754401018778754401002f7a654401002f796544010007bb7444010007b8744401002fba644401002fb96444010007db7344010197d8734401002fda634401002fd963440101977b5344010197795344010007eb7244010007e8724401002fea624401002fe9624401002dfb714401002ff3714401018efa614401002ff26144010187f25144010187f15144010007f24144010007f14144010
  | 1 => 0x9010006bd5459010046bc5459010004ff7359010014fe7359010004fd7359010014fc73590100067f53590100067d5359010046bf4359010006be4359010006bd4359010046bc4359010004ff725901000cfe725901000cfc7259010046bf4259010006be4259010046bc425901001cff715901001cfd7159010044fc7159010046bc415901002cff705901002cfe705901002cfd705901002cfc705901002ebe405901002ebc4059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf53590100063f5359010006be5359010006bd53590100063d5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006be3259010006bd3259010006bc3259010046bf7159010006be7159010006bc7159010006bf5159010006be5159010006bd5159010006bc5159010006bf3159010006be3159010006bd3159010006bc3159010006bf2159010006bc215901002ebf705901002ebe705901002ebd705901002ebc705901002ebf505901002ebe505901002ebd505901002ebc505901002ebf305901002ebe305901002ebd305901002ebc305901002ebf205901002ebe205901002ebd205901002ebc205901002ebf105901002ebe105901002ebd105901002ebc1059010006df7558c10006de7558c100065e7558c10006dd7558c100065d7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c10006de4258c10006dc4258c1003edf7158c10006de7158c1003edd7158c1003edc7158c10006df5158c10006de5158c10006dd5158c10006dc5158c10006df4158c10006dc4158c10006df2158c10006dc2158c1002edf7058c1002ede7058c1002edd7058c1002edc7058c1002edf5058c1002ede5058c1002edd5058c1002edc5058c1002edf4058c1002ede4058c1002edd4058c1002edc4058c1002edf2058c1002ede2058c1002edd2058c1002edc2058c1002edf1058c1002ed71058c1002ede1058c1002edd1058c1002ed51058c1002edc1058c10004ff7558810024fe7558810004fd7558810024fc7558810004ff745881001cfe745881001cfc7458810004ff7358810014fe7358810004fd7358810014fc73588100067f53588100067d535881002eef7258810006ef5258810036ee5258810006ed5258810036ec5258810006ef4258810036ee4258810036ec4258810006ef3258810036ee3258810006ed3258810036e
  | 2 => 0x7e7628851000ef6628851000ef4628851005fe4628851000ee4628851005fe632885101cfe5328851002df6708851002df470885101c7e620885101c7e4208851002cfc76485100067f65485101267c6548510006bf644851011ebc6448510006df6348510116dc6348510006ef624851000eec624851005fe42148510005fb704851002df8704851002df4764851000ef4764851002cf476485100077765485101bf746548510007b76448510007b464485101b5f773485101b5f57348510007d763485101afd463485101af7753485101af75534851005df77248510007e77248510007e7624851000ef6624851000ef4624851005fe46248510007f3704851002df6704851002df47048510007f0704851005fe7204851001cff765011006cfd765011001cfc76501100067f65501100f67c6550110006bf645011001ebc6450110006df63501100eedc6350110006ef62501100e6ec6250110005f77150110005f4715011002ff0105011000cff764811005cfd764811000cfc76481100057f75481100757c75481100067f65481100c67c6548110006bf64481100bebc6448110006df63481100b6dc6348110006ef624811000eec6248110005f77148110005f47148110007e521481100067f65c41100ae7c65c4110006bf64c41100a6bc64c4110006df63c4110056dc63c4110006ef62c411009eec62c411002df671c411002ef761c411002dfa76c411002efa76c411002cfa76c41100077b65c41101a77865c4110007bb64c4110007b864c4110007db63c411019fd863c411019f7b53c411019f7953c4110007eb62c4110007e862c411002dfa71c411002efb61c411002ff361c411019ff231c411019ff131c4110007f221c4110007f121c41100067f74594100067e74594100067d74594100067c74594100067f73594100047f73594100067e73594100067d73594100047d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067c42594100067f32594100067e32594100067d32594100067c325941004e7f71594100067e715941004e7d715941004e7c71594100067f41594100067c41594100067f31594100067e31594100067d31594100067c31594100067f21594100067c215941002e7f705941002e7e705941002e7d705941002e7c705941002e7f405941002e7e405941002e7d405941002e7c405941002e7f305941002e7e305941002e7d305941002e7c305941002e7f205941002e7e205941002e7d205941002e7c205941002e7f105941002e7e105941002e7d105941002e7c1059410004ff7559010024fe7559010004fd7559010024fc755901002ebf7459010006bf5459010046be545
  | 3 => 0xf71d891005eee71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef41d8910006ec41d8910006ef31d8910006ee31d8910006ed31d8910006ec31d8910006ef70d89101c6ee70d8910006ed70d89101c6ec70d8910006ef50d89101c6ee50d8910006ed50d89101c6ec50d8910006ef40d89101c6ee40d89101c6ec40d8910006ef30d89101c6ee30d8910006ed30d89101c6ec30d89101c6ee10d89101c6ec10d89100057f75589100757c75589100067f65589100067c6558910005bf745891006dbc7458910006bf6458910006bc6458910005df7358910065dc7358910006df6358910006dc635891005eec6258910004ff75589100067f75589100047f7558910024fe7558910004fd7558910024fc75589100067c75589100247c7558910004ff7458910006bf7458910004bf745891001cfe745891001cfc7458910006bc745891001cbc7458910004ff7358910006df7358910004df7358910014fe7358910004fd7358910014fc7358910006dc7358910014dc73589100067f53589100067d535891005cff7258910006ef725891007cff7158910006f7715891009cff7058910006fb7058910005ee761891005eee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc63189100076f53189100076d531891005fe571189101e6ef6118910007e63118910007e531189101e7e610189101e7e41018910004ff7650910004fe7650910004fd7650910004fc76509100057f75509100757c75509100067f655091017e7c6550910006bf645091001ebc6450910006df6350910176dc6350910006ef625091000eec625091008cfe76905100067f659051016e7c6590510006bf649051001ebc6490510006df6390510166dc6390510006ef629051015eec629051002cfc76505100057f75505100757c75505100067f65505101567c6550510006bf645051001ebc6450510006df635051014edc6350510006ef6250510146ec6250510005fb705051002df8705051007cfe76885100757e75885100057d75885100067f658851013e7c6588510006bf6488510136bc6488510006df638851012edc6388510006ef628851000eec6288510005f6768851007ef676885101df7675885100077575885100077765885101df746588510007b76488510007b464885101d5f773885101d5f57388510007d763885101cfd463885101cf7753885101cf75538851005df57288510
  | 4 => 0x8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006de62d8d10006dc62d8d101efd771d8d10067d471d8d101efd610d8d101efd410d8d10006df75d8d100065f75d8d10006de75d8d10006dd75d8d10006dc75d8d100065c75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dc42d8d101eedf71d8d10066de71d8d10066dd71d8d10066dc71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df41d8d10006dc41d8d10006df21d8d10006dc21d8d10006df70d8d101eede70d8d10066dd70d8d101eedc70d8d10006df50d8d101eede50d8d10006dd50d8d101eedc50d8d10006df40d8d101eede40d8d101eedc40d8d10006df20d8d101eede20d8d101eedc20d8d101eede10d8d10066dd10d8d101eedc10d8d1000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d891005eee62d8910004ff75d8910024fe75d8910004fd75d8910024fc75d891001cfe74d8910004fd74d891001cfc74d8910004ff73d8910014fe73d8910004fd73d8910014fc73d89100067f53d89100067d53d8910006ef52d891005eee52d8910006ed52d891005eec52d8910006ef42d891005eee42d891005eec42d8910006ef32d891005eee32d8910006ed32d891005eec32d891000cfe71d891002cfd71d891000cfc71d891005eef21d891002cfe70d891005cfd70d891002cfc70d891005eef20d891005dee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89100076f53d89100076d53d89101c7e771d8910007e631d8910007e531d89101c7e610d89101c7e410d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d89100066f53d8910006ee53d8910006ed53d89100066d53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d89101c6e
  | 5 => 0xcfe72d9110004fd72d911000cfc72d911006ebf42d9110006be42d911006ebc42d911001cfe71d911002cfd71d911001cfc71d911006ebf41d911002cfe70d911006cfd70d911002cfc70d911006ebf40d911006dbe76d911001cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100079c63d91100069c63d91100073f53d91100073d53d9110006be62d9110006bc62d9110007b631d9110007b531d91101ffb610d91101ffb410d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d91100063f53d9110006be53d9110006bd53d91100063d53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d91101febf71d911006ebe71d9110006bd71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf31d9110006be31d9110006bd31d9110006bc31d9110006bf21d9110006bc21d9110006bf70d91101febe70d9110006bd70d91101febc70d9110006bf50d91101febe50d9110006bd50d91101febc50d9110006bf30d91101febe30d9110006bd30d91101febc30d9110006bf20d91101febe20d91101febc20d91101febe10d91101febc10d91100057f75591100757c75591100067f65591100067c655911006ebc6459110005df7359110065dc7359110006dc6359110005ef725911005dec7259110004ff75591100067f75591100047f7559110024fe7559110004fd7559110024fc75591100067c75591100247c755911006cff7459110006bf7459110004ff7359110006df7359110004df7359110014fe7359110004fd7359110014fc7359110006dc7359110014dc73591100067f53591100067d5359110004ff7259110006ef7259110004ef725911000cfe725911000cfc7259110006ec725911000cec725911008cff7159110006f771591100a4ff7059110006fb7059110005be761911006ebe7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006bf6319110006be6319110006bd6319110006bc63191100079c63191100069c63191100073f53191100073d5319110006be6219110006bc62191101f6bf6119110007b63119110007b531191101f7b610191101f7b41019110065de76d8d10066de76d8d10014de76d8d100075f75d8d100075c75d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d
  | 6 => 0xf53592100067d535921008ebf4359210006bd4359210004ff725921000cfe725921000cfc725921008ebf425921008ebf415921002cfc705921002ebe405921002ebc4059210004ff7558a100067f7558a100047f7558a10024fe7558a10004fd7558a10024fc7558a100067c7558a100247c7558a10004ff7458a1001cfe7458a1001cfc7458a10004ff7358a10014fe7358a10004fd7358a10014fc7358a100067f5358a100067d5358a1002eef7258a1007eee3258a10006ed3258a1007eef2158a1002cfc7058a1002eee2058a1002eec2058a1002ef71058a1002ef51058a10004ff7650a1002cfe7650a10004fd7650a1002cfc7650a100057f7550a100957c7550a1001ebe6450a10006bd6450a10005f77150a10005f47150a1006cfd76906101febf649061001ebc649061001cff765061002cfc76506100057f75506100957c755061001ebe6450610006bd6450610005fb705061002df8705061005cfd76886100957e75886100057d75886101c6ef628861000eec628861000cff764861002cfc764861000eee6248610006ed6248610005fb704861002df8704861002df976c4210006f976c421020f7b53c421020f7953c421002ff271c42100757e76d95100767e76d95100247e76d95100067e64d95100067c64d95100057f73d95100057d73d95100067f63d95100067e63d95100067d63d95100067c63d95100075c63d95100065c63d95100067e62d95100067c62d95100077631d95100077531d95102077610d95102077410d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100047f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95102067f71d95100767e71d95100767d71d95100767c71d95100067f41d95100067c41d95100067f31d95100067e31d95100067d31d95100067c31d95100067f21d95100067c21d95100067f70d95102067e70d95100767d70d95102067c70d95100067f40d95102067e40d95102067c40d95100067f30d95102067e30d95100067d30d95102067c30d95100067f20d95102067e20d95102067c20d95102067e10d95100767d10d95102067c10d951001cfe76d91100067f65d91100067c65d911006ebe64d9110006dc63d9110004ff75d9110024fe75d9110004fd75d9110024fc75d9110006bf54d911006ebe54d9110006bd54d911006ebc54d9110004ff73d9110014fe73d9110004fd73d9110014fc73d91100067f53d91100067d53d911006ebf43d9110006be43d9110006bd43d911006ebc43d9110
  | 7 => 0x9310004fd72d931000cfc72d93100a6bf42d9310006f671d93100a6bf41d9310006f970d93101febe40d93101febc40d931001cff76593100057f75593100ad7c75593100a6bc6459310004ff75593100067f75593100047f7559310024fe7559310004fd7559310024fc75593100067c75593100247c7559310006bf7459310004ff7359310014fe7359310004fd7359310014fc73593100067f53593100067d5359310004ff725931000cfe725931000cfc725931002cfc71593100a6bc41593100a6bf40593100ad7e75d8b100057d75d8b1009eee62d8b10004ff75d8b10024fe75d8b100067e75d8b100247e75d8b10004fd75d8b100067d75d8b100047d75d8b10024fc75d8b1001cfe74d8b10004fd74d8b1001cfc74d8b10004ff73d8b10014fe73d8b10004fd73d8b10014fc73d8b100067f53d8b100067d53d8b1009cfd72d8b1009eee32d8b10006ed32d8b10006f671d8b1009eef21d8b10006f970d8b101c6ee20d8b101c6ec20d8b1000cff7658b1009eec6258b10004ff7558b10024fe7558b10004fd7558b10024fc7558b10004ff7458b1001cfe7458b1001cfc7458b10004ff7358b10014fe7358b10004fd7358b10014fc7358b100067f5358b100067d5358b10006ef7258b1002cfc7158b1009eec2158b1009eef2058b10004ff7650b10004fe7650b10004fd7650b10004fc7650b100057f7550b100ad7c7550b10006bf6450b1001ebc6450b1002cfd769071001ebe6490710006bd649071002dfa7090710005f97090710044ff76507100057f75507100ad7c7550710006bf645071001ebc645071002cfd76887100ad7e75887100057d758871000eee6288710006ed628871002dfa7088710005f9708871002df5768871000ef5768871002cf5768871023776758871000775758871022df7738871022df5738871022777538871022775538871000ef6628871009fe66288710007e5628871000ef4628871009fe63288710227e5328871002df67088710007f27088710007f1708871002df470887101c7e620887101c7e42088710034ff7648710006ef624871000eec624871009fe42148710005f77648710036f7764871021df7734871021df57348710217775348710217755348710007e77248710007e7624871000ef6624871000ef4624871009fe4624871002df6704871002df4704871009fe7204871001cff765031001cfc765031001ebe6450310006bd6450310005f77150310005f4715031000cff764831000cfc76483100057f75483100ad7c754831000eee6248310006ed6248310005f77148310005f47148310007e52148310004ff7559210024fe7559210004fd7559210024fc755921002ebf7459210006bf545921008ebc5459210004ff7359210014fe7359210004fd7359210014fc73592100067
  | 8 => 0xc57c75591200067f65591200067c65591200bebc6459120005df73591200b5dc7359120005f77159120005f47159120255fb7059120004ff75591200067f75591200047f7559120024fe7559120004fd7559120024fc75591200067c75591200247c75591200fcff7459120006bf7459120004ff7359120006df7359120004df7359120014fe7359120004fd7359120014fc7359120006dc7359120014dc73591200067f53591200067d53591200bebf4359120006bd43591200e4ff7259120006ef72591200e6ee3259120006ed3259120004ff7159120006f77159120004f77159120004fc7159120006f47159120004f47159120254ff7059120006fb70591200067f65d85200067c65d8520004ff75d8520024fe75d8520004fd75d8520024fc75d852001cfe74d8520004fd74d852001cfc74d8520004ff73d8520014fe73d8520004fd73d8520014fc73d85200067f53d85200067d53d852002cfd72d8520006f741d8520006f441d8520006f731d8520006f431d852007ef621d852007ef521d85200c57e75985200057d75985200067f65985200067c6598520006f7619852005df970985200057f75585200c57c75585200067f65585200067c6558520005bf74585200bdbc7458520005df73585200b5dc735852009dfb70585200067f65185200067c6518520006f56118520004ff7518520024fe7518520004fd7518520024fc751852001cfe7418520004fd741852001cfc7418520004ff7318520014fe7318520004fd7318520014fc73185200067f53185200067d531852002cfd7218520036ee3218520006ed3218520006f74118520006f44118520006f73118520006f43118520036ef2118520036f62118520036f5211852002cfe701852002cfc70185201e6ee20185201e6ec2018520004fe7690520004fd7690520004fc76905200067f659052016e7c6590520006bf649052001ebc649052000dee7290520005ed7290520004ff7650520004fe7650520004fc76505200057f75505200c57c75505200067f65505201567c655052002cec76485200076f654852024f6c6548520245ef7348520245ed734852023f6f534852023f6d534852000def714852000fe77148520007e76148520006ec6148520007e46148520007eb704852002dee704852002dec7048520007e8704852000eef604852000feb604852001cff765012000cfe76501200e4fd765012000cfc76501200067f65501200f67c6550120006bf645012001ebc6450120005ef725012000dec72501200a6be64d9310004ff75d9310024fe75d9310004fd75d9310024fc75d93100a4fd74d9310006bf54d93100a6bc54d9310004ff73d9310014fe73d9310004fd73d9310014fc73d93100067f53d93100067d53d93100a6bf43d9310006bd43d931000cfe72d
  | 9 => 0xf75586200067f75586200047f7558620024fe7558620004fd7558620024fc75586200067c75586200247c7558620004ff7458620006bf7458620004bf745862001cfe745862001cfc7458620006bc745862001cbc7458620004ff7358620006df7358620004df7358620014fe7358620004fd7358620014fc7358620006dc7358620014dc73586200067f53586200067d535862002ef77158620006f63158620006f5315862005ef6215862005ef5215862005eec215862002cfc705862002eef205862002eed205862002ef6105862002ef41058620004ff769062002cfe7690620004fd76906201febf649062001ebc6490620004ff7650620004fd765062002cfc76506200057f75506200dd7c755062001ebe6450620006bd6450620005ef725062000dec725062027f6e75886200076d75886201c6ef6388620276ed63886202776f53886202776d538862000dee718862000fe671886201c7e66188620006ed61886201c7e561886201c7ea70886201c5ed7088620007e9708862000eee608862000fea608862026d7e76d95200c67e76d95200247e76d95200067e64d95200067c64d95200057f73d95200057d73d95200067f63d95200067e63d95200067d63d95200067c63d95202676e32d95200076d32d95202676f21d95202677b20d952025f6e20d952025f6c20d95202677820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200047f73d95200067e73d95200067d73d95200047d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d952025e7f72d95202667e72d95202667d72d95202667c72d95202667f42d95202667e42d95202667d42d95202667c42d95202667f32d95202667e32d95202667d32d95202667c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067c41d95200067f31d95200067e31d95200067d31d95200067c31d95202667f21d95202667e21d95202667d21d95202667c21d95202667f70d952025e7e70d95202667d70d952025e7c70d95200067f40d952025e7e40d952025e7c40d95200067f30d952025e7e30d95200067d30d952025e7c30d95202667f20d952025e7e20d95202667d20d952025e7c20d952025e7e10d952025e7c10d952001cfe76d91200067f65d91200067c65d91200bebe64d9120004ff75d9120024fe75d9120004fd75d9120024fc75d9120004ff73d9120014fe73d9120004fd73d9120014fc73d91200067f53d91200067d53d9120006be43d91200bebc43d912002cff72d912000cfe72d912002cfd72d912000cfc72d91200febf42d91200febd42d91200feee32d9120006ed32d9120004fe71d9120004fd71d91200bebc41d912000cfd70d91200bebf40d91200057f7559120
  | 10 => 0x9400f5be75509400f5bc75509402af3c75509400f53c75509402aebf65509402aebd65509402a5bf73509402a5bd735094029ebf635094029ebd635094029f3f535094029f3d535094001dbf725094001faf7250940007af625094000ebe625094000ebc62509400e7ac625094000eac62509400e7ae325094029fad3250940005bf7150940007bb705094002dbe705094002dbc7050940007b8705094001ebf605094001fbb6050940004ff75d8540024fe75d8540004fd75d8540024fc75d854002cfd74d8540004ff73d8540014fe73d8540004fd73d8540014fc73d85400067f53d85400067d53d854000cfe72d8540004fd72d854000cfc72d854008ef641d854008ef541d8540006f721d8540006f421d8540006f7619854006df970985400057f75585400f57c7558540005df73585400eddc7358540005ef72585400e5ec72585400a5fb70585400f57e75185400057d7518540006f56118540004ff7518540024fe75185400067e75185400247e7518540004fd75185400067d75185400047d7518540024fc751854002cfd7418540006bf5418540046bc5418540004ff7318540014fe7318540004fd7318540014fc73185400067f53185400067d5318540046bf4318540006bd431854000cfe7218540004fd721854000cfc7218540046bf4218540006bd4218540046bf4118540046f64118540046f54118540006f72118540006f421185401f6be40185401f6bc401854002cbc76505400073f75505400f5be75505400f5bc75505402973c75505400f53c755054028dbf735054028dbd73505402873f53505402873d5350540005bf725054001dbf715054001fb77150540007b76150540006bc6150540007b46150540007bb705054002dbe705054002dbc7050540007b8705054001ebf605054001fbb6050540004fe7688540004fd7688540004fc76885400f57e75885400057d758854001dbe7488540005bd7488540006ef628854000eec6288540004ff7648540004fe7648540004fc764854001dbe7448540005bd7448540004ff7559220024fe7559220004fd7559220024fc755922002ebf7459220006bf54592200d6bc5459220004ff7359220014fe7359220004fd7359220014fc73592200067f53592200067d53592200d6bf4359220006bd43592200e6bf42592200e6bd4259220004ff7159220004fc71592200d6bf415922002cfe705922002cfc705922002ebe405922002ebc4059220004ff7598620024fe7598620004fd7598620024fc759862001cfe7498620004fd749862001cfc7498620004ff7398620014fe7398620004fd7398620014fc73986200067f53986200067d539862002ef67198620006f63198620006f5319862009ef6219862009ef5219862002cfe709862002ef6109862002ef41098620004f
  | 11 => 0x67f31596400067e31596400067d31596400067c31596400067f21596400067c215964002e7f705964002e7e705964002e7d705964002e7c705964002e7f405964002e7e405964002e7d405964002e7c405964002e7f305964002e7e305964002e7d305964002e7c305964002e7f205964002e7e205964002e7d205964002e7c205964002e7f105964002e7e105964002e7d105964002e7c1059640004ff7558a40024fe7558a40004fd7558a40024fc7558a40004ff7358a40014fe7358a40004fd7358a40014fc7358a400067f5358a400067d5358a4002eef7258a400feee4258a400beed4258a400feee3258a40006ed3258a40004ff7158a40004fc7158a400bebc4158a400feef2158a4002cfe7058a4002cfc7058a4002ebf4058a4002ebd4058a4002eee2058a4002eec2058a40004ff7598640024fe7598640004fd7598640024fc7598640004ff7398640014fe7398640004fd7398640014fc73986400067f53986400067d539864000cfe7298640004fd729864000cfc729864002ef671986400a6f641986400a6f54198640006f63198640006f5319864002cfe709864002ef6109864002ef41098640004ff7558640024fe7558640004fd7558640024fc7558640004ff7358640014fe7358640004fd7358640014fc73586400067f53586400067d5358640004ff725864000cfe725864000cfc725864002ef7715864006ef6415864006ef5415864006ebc4158640006f63158640006f5315864002cfc705864002ebf405864002ebd405864002ef6105864002ef4105864016ebe65906401ff3e659064016e3e65906401ff3d65906401febc65906401febf63906402bebd63906402bf3f53906402bf3d5390640006bd629064001dbe719064001fb671906401ffb66190640006bd61906401ffb561906401ffba70906401fdbd7090640007b9709064001ebe609064001fba6090640004ff768864002cfe7688640004fd768864010d7e75886400057d758864013e7e65886400067d6588640006f66188640006f56188640004ff7648640004fd764864002cfc76486401267e65486400067d6548640005bf744864001dbc744864000eee6248640006ed6248640006f66148640006f5614864000cfe76d89400e6ee62d8940004ff75d8940024fe75d8940004fd75d8940024fc75d894002cfd74d894000cfc74d8940004ff73d8940014fe73d8940004fd73d8940014fc73d89400067f53d89400067d53d89400d6bf43d8940006bd43d89400e6ee42d89400d6ed42d8940004fe71d8940004fd71d89400e6ec21d894001cfd70d89400e6ef20d89400057f75589400f57c7558940005df73589400eddc73589400e6ec6258940005f77158940005f471589402b5fb705894002dbc765094000ebc765094002cbc76509400073f755
  | 12 => 0xe65582210067d6558221004ff7558221024fe7558221004fd7558221024fc7558221004ff745822101cfe745822101cfc7458221004ff7358221014fe7358221004fd7358221014fc73582210067f53582210067d535822105eee3258221006ed325822105eef215822105efa20582211c6ec205822113d7e75182210057d75182210067e65182210067d6518221135be7418221005bd741822112dde7318221005dd731822102efa6018221006f9601822101cfe76d912111ebe64d9121004ff75d9121024fe75d9121004fd75d9121024fc75d9121006bf54d912111ebc54d9121004ff73d9121014fe73d9121004fd73d9121014fc73d91210067f53d91210067d53d912111ebf43d9121006bd43d912115cff72d912115cfd72d912115ebf42d912115ebd42d912100cfd71d912111ebf41d912102cfe70d9121004fd70d912111ebc40d91210057f75591211257c755912111ebc64591212e5f77159121004ff75591210067f75591210047f7559121024fe7559121004fd7559121024fc75591210067c75591210247c755912115cff7459121006bf7459121004ff7359121014fe7359121004fd7359121014fc73591210067f53591210067d5359121144ff7259121006ef72591212e4ff7159121006f7715912111ebc4159121004ff705912102cfc705912111ebf40591212dcfe769052101ebe6490521006bd649052101cff765052100cfe7650521144fd765052100cfc76505210057f75505211257c7550521006bf645052101ebc6450521005ef725052100dec72505212d76e75885210076d75885212ceef63885212ceed63885212cf6f53885212cf6d538852100dee718852100fe6718852100eef618852100fe76188521005ed7088521004ff75d8121024fe75d8121004fd75d8121024fc75d812101cfe74d8121004fd74d812101cfc74d8121004ff73d8121014fe73d8121004fd73d8121014fc73d81210067f53d81210067d53d812109efa20d8121006fb60981210057f75581211257c7558121005bf745812111dbc7458121005df7358121115dc73581211257e75181210057d751812111dbe7418121005bd7418121115de7318121005dd73181211c6ef621812102efa6018121006f960181212c67f74596402c67e74596402c67d74596402c67c74596400067f73596400047f73596400067e73596400067d73596400047d73596400067c73596402c67f43596402c67e43596402c67d43596402c67c43596400067f72596400067e72596400067d72596400067c72596402c67f42596402c67e42596402c67d42596402c67c42596400067f32596400067e32596400067d32596400067c32596400067f71596400067e71596400067d71596400067c71596402c67f41596402c67e41596402c67d41596402c67c4159640
  | 13 => 0x81410067f65981410067c6598141006fb60981410057f75581411557c75581410067f65581410067c6558141005df735814114ddc7358141005ef7258141145ec72581410067f65181410067c65181411febf641814102efa6018141006f960181412f57f765962113e7f76596210247f76596210067e64596210067c64596210057f73596210057d73596210067f63596210067e63596210067d63596210067c63596212ef6e32596210076d32596212ef6f21596212ef7721596212ef7421596212ef6c20596210067f74596210067e74596210067d74596210067c74596210067f73596210047f73596210067e73596210067d73596210047d73596210067c73596210067f43596210067e43596210067d43596210067c43596212ee7f72596212ee7e72596212ee7d72596212ee7c72596212ee7f42596212ee7e42596212ee7d42596212ee7c42596212ee7f32596212ee7e32596212ee7d32596212ee7c325962113e7f71596212ee7e71596212ee7d71596212ee7c71596210067f41596210067c41596210067f31596210067e31596210067d31596210067c31596212ee7f21596212ee7e21596212ee7d21596212ee7c21596210067f70596210067e70596210067d70596210067c70596210067f40596210067c40596210067f30596210067e30596210067d30596210067c30596212ee7f20596212ee7e20596212ee7d20596212ee7c205962113d7e75d92210057d75d92210067e65d92210067d65d9221136be64d922112dde73d9221005dd73d92212ddf671d9221004ff75d9221024fe75d92210067e75d92210247e75d9221004fd75d92210067d75d92210047d75d9221024fc75d9221144fd74d9221004ff73d9221014fe73d9221006de73d9221014de73d9221004fd73d9221006dd73d9221004dd73d9221014fc73d92210067f53d92210067d53d9221136bf43d9221006bd43d9221006ed72d922115eee32d9221006ed32d92212dcfe71d9221006f671d922102cfe70d9221004fd70d922101cff76592210067e65592210067d6559221136bc6459221004ff7559221024fe7559221004fd7559221024fc7559221006bf7459221004ff7359221014fe7359221004fd7359221014fc73592210067f53592210067d5359221006be4359221136bc4359221146bf4259221146bd4259221146ee3259221006ed325922100cfc7159221136bc4159221004ff705922102cfc7059221136bf405922100cff769062101cfe769062100cfd769062116e7e65906210067d659062101ebe6490621006bd649062100dee7290621005ed72906212e4ff76506210057f755062113d7c75506211567e65506210067d655062113d7e75d82210057d75d82210067e65d82210067d65d82210067e65982210067d6598221006fb60982210067
  | 14 => 0x1fdbc7050a41006fb60982410057f755824116d7c7558241004ff75582410067f75582410047f7558241024fe7558241004fd7558241024fc75582410067c75582410247c7558241006bf545824106ebc5458241004ff7358241014fe7358241004fd7358241014fc73582410067f53582410067d535824106ebf4358241006bd4358241004ff725824100cfe725824100cfc725824106ebf4258241006bd425824106ebf415824106efa40582411febc405824116d7e75182410057d7518241165de7318241005dd731824115dee7218241005ed721824102efa6018241006f9601824131d7e76d95411567e76d95410247e76d95410057f73d95410057d73d95410067f63d95410067e63d95410067d63d95410067c63d95410067e62d95410067c62d95413177741d95413173c41d95413177441d95413173f40d95413167f74d95413167e74d95413167d74d95413167c74d95410067f73d95410047f73d95410067e73d95410067d73d95410047d73d95410067c73d95413167f43d95413167e43d95413167d43d95413167c43d95410067f72d95410067e72d95410067d72d95410067c72d95413167f42d95413167e42d95413167d42d95413167c42d95410067f32d95410067e32d95410067d32d95410067c32d95413167f71d95411567e71d95413167d71d95413167c71d95413167f41d95413167e41d95413167d41d95413167c41d95410067f31d95410067e31d95410067d31d95410067c31d95410067f21d95410067c21d95410067f70d95410067e70d95410067d70d95410067c70d95413167f40d95413167e40d95413167d40d95413167c40d95410067f30d95410067e30d95410067d30d95410067c30d95410067f20d95410067c20d954100cfe76d89410067f65d89410067c65d8941146ee62d8941004ff75d8941024fe75d8941004fd75d8941024fc75d8941004ff73d8941014fe73d8941004fd73d8941014fc73d89410067f53d89410067d53d8941146ee42d8941136ed42d8941146ee32d8941006ed32d894101cfd71d8941136bc41d8941146ef21d894102cfe70d8941004fd70d8941136bf40d8941146ec20d89410057f75589411557c75589410067f65589410067c6558941146ec625894130df771589410073f659054116ebe659054116ebc65905413073c659054116e3c65905412febf63905412febd63905412ff3f53905412ff3d5390541006bf629054101dbe719054101fb6719054101ebf619054101fb76190541005bd70905410067f65d81410067c65d8141004ff75d8141024fe75d8141004fd75d8141024fc75d8141004ff73d8141014fe73d8141004fd73d8141014fc73d81410067f53d81410067d53d814100cfe72d8141004fd72d814100cfc72d81410a6fa40d81411557e75981410057d759
  | 15 => 0xe70d95420067d70d95420067c70d954234e7f40d954234e7e40d954234e7d40d954234e7c40d95420067f30d95420067e30d95420067d30d95420067c30d95423467f20d95423467e20d95423467d20d95423467c20d95420067f65d85420067c65d8542004ff75d8542024fe75d8542004fd75d8542024fc75d854200cfd74d85422e6bd74d8542004ff73d8542014fe73d8542004fd73d8542014fc73d85420067f53d85420067d53d854201cfd72d854230ef641d854230ebc41d8542006f631d8542006f531d85422e6f621d854202cfe70d8542004fd70d854230ebf40d854217d7e75985420057d75985420067f65985420067c6598542175de7398542005dd7398542006f761985420057f755854217d7c75585420067f65585420067c65585420067f65185420067c6518542006f56118542004ff7518542024fe7518542004fd7518542024fc751854200cfd7418542004ff7318542014fe7318542004fd7318542014fc73185420067f53185420067d531854233ebf4318542006bd431854201cfd72185422deee3218542006ed321854233ef54118542006f63118542006f531185422def5211854202cfe7018542004fd701854202cfe76d81420067f65d81420067c65d8142004ff75d8142024fe75d8142004fd75d8142024fc75d814200cfd74d8142004ff73d8142014fe73d8142004fd73d8142014fc73d81420067f53d81420067d53d81422b6bf43d8142006bd43d814201cfd72d8142256ee32d8142006ed32d8142004fe71d8142004fd71d81422b6fa40d8142256fa20d814217d7e75981420057d75981420067f65981420067c6598142006fb60981420057f755814217d7c75581420067f65581420067c6558142005df7358142175dc7358142005f77158142005f471581420067f65181420067c651814202efa6018142006f9601814216d7e75d8a410057d75d8a41165de73d8a41005dd73d8a4115eee62d8a4133df671d8a4100cff7658a4115eec6258a41004ff7558a41024fe7558a41004fd7558a41024fc7558a41004ff7358a41014fe7358a41004fd7358a41014fc7358a410067f5358a410067d5358a4111ebf4358a41006bd4358a4115eee4258a4111eed4258a4101cfc7158a4115eec2158a41004ff7058a4102cfc7058a4115eef2058a4115dbf7650a4100ebf7650a4100cbf7650a410073f7550a4116dbe7550a4116dbc7550a413373c7550a4116d3c7550a41336bf6550a41336bd6550a4132dbf7350a4132dbd7350a41326bf6350a41326bd6350a413273f5350a413273d5350a4101dbf7250a4101faf7250a4100ebe6250a4115fae6250a4100eae6250a41007ad6250a4100ebc6250a4115fae3250a41327ad3250a41005bf7150a41007b77150a41007b47150a4101ebe6150a4101fb66150a41
  | 16 => 0x800400000000100000060020008004002000000800000200600000080020000000000006001000800800e000000800c01400400080000020010008000004000003801400200100000000000020008000000000003000000600000300000000010010004000000000800000a003000800400000300180240040000058008002000004000000200000100040080050000000000000001800400000000080180060000040000006004000000c002001000000000c0000000020000000000001000a00000400080000000000000000004000800c0000000018000000003002800000600000100040080000008000000000000000000a0000008004008000000000c008001000000c002000000000800800100000000000000028008000001000801000200400000140020010000008000000001800400c005000000000200000000080020000010000000000001000000400200180040000000010004000000000002000e004002800400200000000080060000000000000005000800000000300000000000000010000000002000800c008005001800c006001000000c004000000000400000f00000080000000028010000000000000000400100080000000000010004000000000000c004000004800400000000000000000030000000000001002800400000100000140020000000004000000000800c0020010008008000000000000400e000001000800000000080040060050008000000001003805000c00300000000000000008004002001000800000800000000080060050008014000000004800000e000002800400400100000000020020020000000000000000000000b00680100040000008000000000001001000600000680040000003557e76d954217e7e76d95420247e76d95423473f74d95423473c74d95420057f73d95420057d73d95420067f63d95420067e63d95420067d63d95420067c63d954234f3f43d95420073d43d954234f6f42d95423473e42d95423473c42d95423476c42d95423476e32d95420076d32d954234f3c41d954234f3f40d95423467f74d954234e7e74d95423467d74d95423467c74d95420067f73d95420047f73d95420067e73d95420067d73d95420047d73d95420067c73d954234e7f43d954234e7e43d954234e7d43d954234e7c43d95423467f72d95423467e72d95423467d72d95423467c72d95423467f42d95423467e42d95423467d42d95423467c42d95423467f32d95423467e32d95423467d32d95423467c32d95420067f71d95420067e71d95420067d71d95420067c71d954234e7f41d954234e7e41d954234e7d41d954234e7c41d95420067f31d95420067e31d95420067d31d95420067c31d95423467f21d95423467e21d95423467d21d95423467c21d95420067f70d95420067
  | 17 => 0x1f178c0001a630000002f200024e00000003ff1c584f80003fc0001cf000000000028d400000000020cc00000000009a400000000000000000000000000000000115800043a0000000000000362292039c0000350001d8918800000000000007c50000000b762f50000000cfa0000002b85022a013b901ec99e3910001a2c00000017406ac0001940c403bcfc81bd000283c0000000018006000000000000000100300080140000008008000000000000000000100100000000000020000002001000000000e00200080000080080008000000000001801800400400080040000000010000002002000800000600100000000000000008008000000000000400a001000000001000000000040020020038004002002000000c002003001000800200000600180000000000000000007000000000000a001000400000000000000000020018024000001000000c000000000800000a00000000200020090010000014001002800000400b0000008000007001000000000c00380040000000038008008000003000c00800000480000000010000000000000001003800200000000180000010000000002005000000000a000003000801c001000003c0080020018004000000000000400000100080040000000000008000001000800c00200200280000000010008000000007000000000000100000000000000000004000000000000c00000900000000000020008000000007002000800e003000000800000500300000000000000008000001000000000000000180000020000018000008000002000000a003000002c000000000000000400000100000000000008000008000000800000e0000000000008000002000000a00200080000000040000000006000000000000000000000000020020000000000000002000000000200000000060070000000006001000000800000100000000000000040004002001000001400400300280000000030008010000001001800000000300080140020000008008000000001800000000000400000000000010010000001001800000000600000080000040008018004001000800c0000000010000002000000800c0000000000000000007000000000000000000040020030010018000002000000000000000080000000000000000002000000000000c0000010004000003000000800000100100200020010000004000004001800000000400000140020010008004002003004000000a000000000000000000000000020000000000006000001000000000400080000040000000004000000000000000200300180000040090000000000003002000000200500080000000000000024000000000800c0000010000010000000000000400000000080040000000000004002006000000000200b00500040020
  | 18 => 0x7147081068c04a186a40cd0000b867c1000174ce6000008283e90e253f10a0f4105c0002230001352000000000000025c0ab0b8510c0000000000d06000000000000071323e98040e400000020700003f81dd00000000000000000ab077146d80b00008280000001342000257000003c5fb000000124e000113800000042052b83789dc06012080000567c4000140c0004c1492a1b00008dd000000000000f0001f8800000000000000007b7000000000056a00000010de15c3a9026c0000002c700000000001f6000000042b43a100400031f09c91f0000000000118400044500000000002590bc00000000000000000000000097196000000000000000000000001f2121400000000000000005748000000552000000155a7ae000000000023100000000006cb000000000024c24782ac000000168800110e000000000000000026f28a0a8600000000000000b0000000000000051200000009b5505a9b057e000000186c00000000022b80006a74e009fc0005e100000000003d400000000000003d600012ca00049a0e212005dc00000006f20000001920000000000000009e87800028110ec81d00000000009f20001ca40003832112324f280000000000000000000000028069b4019d1904e16900000000006c83bb16540000000b02af48249760000e94df49bd420ab98000424000000000000000023415860002a78000b1200000026e4dac57c0000cf0bb200000005503f4a15284017c0000000658000000a2c00000012c806700000000000000000000000000000000043c000000000000000000000011120003589d5c9b60000001a282620000000b1c00000000022940006d0000196c000000000000000000000007a80000000002680000000000000000036e000000000052a3850000f6a38f0001afc00000000000000000b3000000000043300022d000061605d80000005484d8000062a1ba00025209d800000025a528a0000000cf400000000014385e25753bfa3d0e80aa00002434000141462800000000031ea1200003940000c640007474a68b2c8b400000024dc0007fc568800111e00000000008c08e0000000075ca5e0001d140008c70000000000669000000071c3180000fa83e21900268a38ada8f954b842919ea4300000000000d4562000136c0003d01c1000000000005c40000000000d708080b80001c804c400000011c80000000001a18c240000101b082ea00000022900000000000000000962000000112a96300000000a26cf000294931019c00fa46cac88e7241800031a000000000130c00049e800126600047c1a400000004ec0000d780004909d551740003ae00000007273d200006627ef000051800082009c10e400000012980180003e654a800006000020f8b6c00000025e8e8400037400021dc78211e4
  | 19 => 0x1d251ca5b03ed253cfba1a900a80011960000002140dbc00000000005ee3a8000000000000000000000004ed5170468ef800000023908183fd2e7112d0c226d08f803800000005a800000000000010dc12c00000003580003334b78da000000031480001e44ba0000460000884004800000000038f000000000000000000000000000000afa0000000000000000000000024800031580000003cc33e21500000321fc8000a3207523400000004190001e3c0000000000000a3e0003f380000000000418000000000000000119000000000003882c400000000007bd00026c80007fe47300000f4816000000000000000014e10205330000e89370000000000073600011d80007e08d3000126400000000000000005b53c100011f8000000000108a1d80001efd1d60002dc8000ddc000000030c9ac00000000000008b600000000001f400000013b600000022e000008c510800000000000000a8000000000000000000022c90540000000000001522000000000155e000000000000000000015b0a1207e00017d4cc000000000000000ed039aacc0004ab2eb000000069500009cc00000000025c88d400018800000006e1000000000000018500011fc22300000012d40004e5000000055600009ec00000000000000009970bb98300000000001fb400000000000013084d508d92240008801510538e6600000000000000001cf02143a4000000000155c1cb00000000001f200000000004362530e900001010000000000000484800000045300000004fc000000078c58c0000000e00000000000033905a0000001dbc0000003b48f5cbe80000649c9800024f00024ac5a8a5300002406a24a800020bc00078a2c31cb079c6ef387000000000000000000009c30000000c860005558f7c3240000002808c4c6c90000ca00007f200013c40000000002348000000000095800053e564a81c0000000001475126000000087c0009713cf000000000000000013c0a6a1ad80000009bc37a800000000046a281865c0000000000000655000108c36c00007f800000008200003b000000000000000003981c9000000076d0000000000172000000000000008b08c814200004d000000014b0001bc8bf800007e291527e3d3000065d0462f248798854ea0f600000013e02ae00000000000000000000000000000000122600000000003f60000000000e465ed000000000000000019680002770000860000040371994c000000000167800000000021a40000000000ed00006e502817e8f1a00000000000000002d9000000000000000000000004b6000077000000000000000000000aac000acd000000002c42754f03694b09de4870000f0c428000067c00064600000002ca0000000000f76000072000062c0001990000000000000230d22e0000000000
  | 20 => 0xf68000000000000000000000000009b8000000000144621c36c8f64c9e57f2659e580001f9000000000000020580000006dc21d800109a98c0000000000000000000000000000000000005ac00007a0bc000000000000003b0000000000000042aa0ec0000f12c19cd000029d4d20e312fa5c21908f240006611f7873c0ee000081a0780004fb3d68c2cc8e24600026a015046c0000000d6829a000000150e00000000014fe000094000087082b42100008843454b397f8518000451000000000031f88d057c86830180002ba0000000000a30000000000000034a40303000001cc13d000004c3e42e005d000000000000000001890fc000000004c45a8000000000000256092400000013a82605e60002524b921e43b50000d285370000128000000460984c9520000000001560000000000087e0002a58b9038000000400007080000002280e047151d581a000000000000009e64d00000000000000347800000000000000001280000000000cf20003b8000000000023c80014648242e600000000d14c9000000000000000000003d2000167d0cc62a000000000000000027f803800000000000000004df174865671a000000000000048aa42c000000000000053249100000000000000440000000000000000000000010c80005ae5e516f0000fa20002d309b83da4a30b197ac00069327394486c29d60000001542000000000009280847d9f580001fe5221aa92bc3f656900000000000001d1000000044080000000000f0818504400000000000009ef00020d8000000000000000051128d80014de00000000001b80000000000000a9400000008f00b62480e64000000000000130a000000000050c0003ef000000000057000000000003178000ee80000002a14b743e945e18380000002ad224411e36716808dd4008f100000005fa00000018100000000b400006ae2ef2700000220885549a5050961530000568bd400034499f80002f42c8000000000000028e46c620b00000000b80003e50000000000000000000000000000000000004880000000000461085400000000000000000000000000000000000000000000000000000009c50000664ca882100000000000000000000000208313800153000000019d4b363b539580000d856e4768000b5c00000026401ea000000028000000000014880000000000000000000000000000000000000007ac0000001258000a7031a000060a0000001a8cf4c48c5721c500000002a480000005a700000006ee00000000000002331ec0000000000000000011468237c000051e0000002558c0c000532a40c00041300000000000003a19ee40000003d119cce96000528800089e2cf00000000000000002b8c0006083f4aa9553879d11019400000000000000b7e000000227c97e2b7
  | 21 => 0x300025d4a7a000000096d1603bc4fd84d080a5c13692a7c58645752697b95b20000358000b2e466000000117a00021aa694000000000000036000000000001c0000045800000000018d11ac8749d1000000000061800000007c67f81a680000000f41aa25646f40000ee00003de20606400d000000000000000000bc0000000000000084800151000053e000000000000020fc0000000000000000407000000000009e000000000021a00000000000000000000d802172f2000000000002421683d20430e380000001150520a7154800047995dc4220000002448e6e00041a0000000928308250067e000054a814e9020e00000003b2000136267c4600000000001330000000000000000000000006f024b3b6283000076e000271c000000158800000062e4ada82800000020e800076e0000000000a045720000d008044d83cb8c192c26420629a2000028919680000000000000000da6a3822b00000000000000000f180002c7824c00000000000007cea470e1a8a800000000000005d62720001c440006e4000000000000000000000000002ce80002769e5000203800060951f9a6800000032f14ac4f20000001df42740003f80000000000546828800051c17e00000000000000000cce00000001047c0000392820400000048080000000000000d814340000000000306000086000000013335c1c30eb095d000227400000000000000000000002974d182090001b740001f60001ee800017c00000000006fc15505202169f6000000063a00012017e474c78827e80011b89ff000000000051017517dc00000053b800000043e20689f00000003f580000007640001f600000001d020e85b42a106600000005f20000000654a900000d0549206f3d48e4d48093b2f8a37cfbe0f33b4141499800000024180000ba00014ec000330000000000000000000000004a700017e0000a3300000000004b327aa544ade0000000498dbe00000000000000000001be44201ce000102048a0001599e389768bf223800000075f000006153699c0000ec4000000000000054a0000000000c8099500000000000000000ad80000001e780004840003bd8000aa0a163d5000006c7d501b80000000cd000000000000000000000000002cb0000000000070800000066a0002b385ce0bf0001d4000007c26e800000037b00000004ec61f543000000000000000003b400000013486000000001d3539e00000016f885c0000000b80000000000000055800036a000000000000008900000003baa1c00004f70000000b960000000000000000000000000000000025e92581be000000889c0000000000000000298000087854a000095400017b1cd00000b68021b98e542880003671644000966362042000052000007b80000002e79c042be000000000156e0000001ac
  | 22 => 0xb40000000000000000000388000144c00000000000000000001af80002870000000000000000056456a5d834e88b03ae000000000000000000000007baabc00000010540001458000c8a6a6000048800000044d80000009dd10b000000000000000000000470000000af2946000000000000046c854000000000000002dc5da000138c8d2000000000000000051781183b6000000099d2d03eb00004700000000000000000000441800007e10000000012aa0000001ed0fea5a9000000000001000018ec0003200e9800077e40e01e8a8c00046700000008149f5000000070c8880000d408c6000000000000000022006140005d720b1f412e0513208000000000004c95641fa00054903c0000918374800000098100000000001d00001a640000000001cc92c02652cc16108dc7a50000000000000164a16000000000002012da00016e800000000000019a0888000000080400055500000000a42120000000e6c0005168000dcc57e0cd81989ae00053200000000002d400000009ba000287468e00041c0c906e00001ce800000048b2311c60a580000f80f780007fa000000000000000000000000000001c14dfca6e4770604000000000213803600001e0000a5a0000b3000000000000025280007af00000000000000000000d980000ca800024600033d00000001ff0000000000000000000051064d1ab0000000000000246800000014f00002ae00000000008360005368000242ac711fa4f0a007e3000148cec26370000000d3000000000000180000002ae800097800022cc49c00000000000c63bb1b60b583ea7f13bb80000000002ca14540003c00002880b7016100029180000792b880000003073b2800010c00016c000000000022480001be00000000000003b9000000000077900000000007fd34f8000000000000000000000000000000001270000f140000000000d0800000027d28c06080dd0e421b817200b000000000000013225f803a8372c68000df60e9148000142e73b2e21f6428e00030d26b06fa00015d93c822200011ca284000a500ef0000000000000000000000024200000000005458000000000559000093c00000000004cc3120000001594000000000000000040c0000d020004750001098000000098c00000013a1c2c00000000000000000000d18000abe0000000abd2a600000025088bc39f32080000000760f9856149613c5389930c32000567800000072210d80005d20003fa000012a5931b580000007b10000000b8c66226684b00000000001398a72000000000040079900016695b881f000000081e28d48c800000000039428d8bd29eb0000000000000000000000009f3249204e2e1124552954c3a2f94532aa55341912781ab00007f7000000038454d02580000009940001cb4000498000260c00075
  | 23 => 0x342833cd1a3ad0000000000000000000031c88a0000000fc2494184800000000000000005a6000000000096000007c0000000a3e069800013a1e63328eb0032000000210caa235a1fa9ee083c000000000000008d406997d4d04a51cb157540685f00000ec4080000221f5c39409c00000000000d200000006520004321ae51d2674165237800054154e97411e047300000013a452900000012644c54c780003c45bc0002984000943000000000000013e850c00000000021f8e947c651e8531468000311233093e16b1a6000000000052c800000000000000000000002b28001396000173000078e36500018355760001a70000000000000000000000025c000000000000019c0578000000000091a4f651b8000f420eb00000003fa4eb000000060493a000261c91494b000105c0000000000000292000000000115a92344600440000000000000000000000000057000000011ec0008722fb013800000002286a8000000000000000033800000003a200000000000000000000000822000000000000000002d0001504000121800000000000024800000003fb29eca846760bd132852617002c241138c00000000000007540000000ec000015909440002581fa000119c0000a7a1192e61ec19a0000abc6390da800116e0001ff0000000000000193800079211280014129cc1860fed1949dc53a2358000546000000014e3a900016712f8042000024800000055b18c00009a7000202d37e9e700023c8000a0e3d4069061c00007300006f800000000000000000001428af09bb000000039a0001c08000e7200000010691fe000000000000031c00000002ce0000002174986a6608e80011ee0003c9a5fcb5a3e833700005827e80f28928cd60004160000000000000084c0009ec3c8000000000039c21e400000000020f00ae00000006ec2e66d1000136400000038780015b45010000b148a40004fd00015a858856b00000005a000000000000000cb00000002fb000000000000031f1b0c0000ca0000000e9c000000000057400000010186100003970000c88000000000000000025c931c71a00000000000005de00013fca8e9960d8a9509347b0000000000000013580005023721e8aa38d8a2e3000201546200031e00012a40003c4800000050d0e48000db69e62cca06c62200047d00002b600000000000000004f095a0000781000000000000000000000001420000000712000000077cf081f703f8000ee64880001aec00080100000001c60aa0b500013000002b49c0000000000000000000000000b3800000012480007965922ed8260baa93503ea7a005200000000012980001a490a4c0a9f8000194838299b45d8750de62033831890164238000264d27c42d1f7202800045f000000098c6a1000128800000048b09a800000014b05
  | 24 => 0x2189f4c00070744100000740000002b9d25a0784288000a64000000000062800000000000000001e104801d04ef00012dc00003922685150f4a253488f8950023a36a897c9684972ea000000084700011300008d10001f48000000000000098073d000215c000000000000000000051d8164000000551800000047700000015b60000000000000a5600000015be00000003b80000004bc948438c00000000013f80050000000000000483800000000021e800000000000000000000000000000000ab1000000000054e000000050a00000000000001d6000000000000045c8000f001ad2b58dbd06a0004ba19586ec68e000000054c62030a0f2800000003680000003f20da26ac00000017700000008a9000000000000022a80012a00000001d3c00010605f000000000000001c46885ab06807150002a400011d0a2c00030a8158eba0000000000000000000000000089229b00000006e74098cdc5ec00000000000e0664527800000019e000000000000023f15d800042600006f0000a8a00024300007d400012b4000a121039b0426e1a7419000024a00030e000000000000000000000000000000006aa64aa16cd0c63591e6a7240000000000d7800000042d80000006b54480000e7e76b29880006066a923780000005b70000000ecea840000ecc000000255000000000000000000000000000000b8a49d000067470a000000141000000000000010f600000003dc0005ca05a11e80007c30000d741b20000bf8000ebc0004982b6000018b00000012ae00000014190ac00048285b04a842f16c8e41436add00000000000000000000cf09d90001f3800000000000000008ec00000503500fb00018c80000000000000b0439c40600015028590af0c5d222a7a40b98d80007c01419388a346a5000159ce2c3aa33fa360d5c28a45f000000000000000000000000000000000000000226041e000000000000048e15380000000000000000bfa00043a83600000000000000000a274bd8ed80000003780000000000000000035879f29399c400000038e1bf40008e200013f102800011698c40007c9000197459a6ec2b8000016e00000000001c40003012740f960af00000000009ad000000058400000000000009b10348000000000000198c64400019d0000b90a110000000000000000000000000000003e44b4000000000000020a000000135e00052400000007874459a813ae13f000000000000051e10a800000055419993900002da14d00000a500000f800000000024e40080002bd800050498d3bd2368d3864a425158c00048700000014280000000000000a621a989800005540000ebc8b658a00000000000000002b0800000003a00000003d515000015440000000000dc000000011700002ad4f505f90da09717f13e00000
  | 25 => 0x8ab051a9f800000000000000006965319b34bbe00000014d50b800041e800000005e2498000b6236615409e090c49531680000000c400000000000000000000000000000000099c5c70002afc000000336000025e72a48f830805c000355aa5800000000000015321b226f8438ab8000000145c0000002d50000de83b2000068513c00008c9ef000000051d2a305f45660001150f5644a00015113a60c100000005e60000000000900528000000133a9f111a8000b9a0000000a4400000000000000000000000b5469e091339120800052e2f3a7dc9e894430580000002701148000000000000000000000002a800103400000018e0000a7325b21f4254038242852850087c3d91a100007f911e00014524d402a00000008522ee800084a1dd000095c0009d516e17cc8e200015e82c477a77e000153000000038d800064c00020c0000b6c9e4000000000000000000002ec00000000000006a8000000036e0001c390b139a0ac000128435c44100000000000000000000000000000000000000004700000003f700027a400065100000000000000001844ba2a2b33d80690807dc0001160000000000000000000050400000000002f609bd56a00034380015a0ae200000000001fc471809d1dea100001e54dee0004ef9d8c4eaac62ada18056895c0d99e2c00000000000007b88a300000003aa798000202400000000000000000000002908f8ea1c48e8000000000000000101e8250822af800000042228600000000000000b02633000094000013d00000000dc0001879ce80009c240380001aa000000000000000000000004a4000000000004a00000000008e035f0000b008383c344d0c9c8da0000000000000000272a2bcd2e6b200000000460000001f307c20002328000f9a0000c027f4cde00000000005c40000000628000000000002800000000000000000002588000e840002578000000000000219d1aa22f1131c4874660f3d1800000000000000000000004db80000000004cc80000002280000e5c000375000000154e6f604480009367ee164000061a6250630000000982000000000054037691d92b40005069d0400018700015d000000046300008420a6000000000083100000000000000001310af48a836d000000000000000010d6724086a62d2eead7102800000036a00000005be000000000000000011e80000009c100000006260001bf0000044000000000000000000000000005ff264a2c80003390001b5cb0a87f0001abc57214d00000050a60000002aa85a4000491110c00000053900000000000000000000000000000000000000029f53dc00000000015580000001bc4d7a00039f000066a06a3cda1a91d022148e187817a000000000000088d00028880ba66d000000000000000000003403c455c26b925c50f2b98
  | 26 => 0x1fccc6a24d2b1213c0006ad0c7821cc9600000000000000003f50a6c0000000000000b4a00019f0000d0056100014e80000000000000b440003cd000000001256a80000000000001cd4e4200055c841c5087cf269800045c0652c029e000075a3f28000488a5f000055456045000000000007c2000000000000000000000000000c6021000089700000010e60000001b6000031e0000000ecc00000000005520001bf9b28000000000000000000056026a896a4c2268800159600022400014b40003c180000001e700014bc0009ce095ab780000000001d594d68653a60000000000000000000000000000000000004248000000000000000000000000017c0000000509a3d800000000000000000000000000c469b33ce0d600007e00b7997000000000000007900620f58fcc1fc9d40002b2122800027200000004094180000000268012000000000014924bc0008624472010958000000000000000000008a80000001a3141c0001514fa000149800000000000000000000000000ae52c5a7cc00000000000000000003869fec77ca830c21bfd38829f000195ce6247f4989ba89404b200016300661a23ff80009fc93825204a4dd68c000000000003430000000c5000028a036cbde3db1aa9144000000495000131c00036313a4000000000000000096b4cf014c000899000000000000000000000005e800000012dc000000000000000019b05f44047090001adc0008cd00000840000000002788a162613c2800030498a00000003260000000000d66000000000000000009aa64400010f000000000053c0001c7c000000081000000000000000000000000001050000000270800000000000000000000000002478000430453a99c0006c700022b05289294af98b00005bd00020e4868000000000035e0000002b0400023e00000013128f5000000000012d0000000000222000000000000000000008642980c31b886d2000000268c7048151fd161c5d83480000000000719000100c000000000000000000d00000000006e800000000002970001478000a604930000d6c0000002904c740e50b20000000000000000000000000000000000004130974000000000001c00000000000000004da000000128e0000000000e3a00000000000008e1000000116200001880000000000000000c1440000000000001b8534800018e000000000000000053c80bc0000000000fc400046400000013340002f10c9434a5af00009200006170000000000000000000000069240ca78d5a681200002b49f22f800014980000000000000000000000000000000000000000005a41918000a4a8941b6a6982260001f680015d000022ea928ef000017f8660000000000000065e00008b9fb143c70300000000000000000000000000000000000006400000004e2
  | 27 => 0x481000000000025f00005e00001661ecc05aa1f3f3091c0003715628000a8a00009b1ae800000032c80009d000000000000007b625e000000000000000000000000000000658000000005c0007a7000000112c0000000c6c0509ed52e04c874ea893a88d2c0009b41768000000000009932000000000027e4000924000168cd44a5b0000000ac000000000000003e553b00015680005271ef8b4200000000002280000000000000aea0a922712102362a98000e5e1e034f00011fa00033b80006a4000172a4d88ea25e0000000676000000000078c791000217800000014a80000000d7000000000000000000015988d70dc8000000a192ab80000008295479d6c41800000003a93b400030386fc2c40000002538eb29a21b200000007db057
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8ec87549620400b1dd0fa12c4080163ba1f32588100053742e64b102000a6d85cc96204001c9aa7992c4080163b21d32588100166639a64b102000e4d534c962040015c902992c408002aba10755881000556c20eab102000ace831d5620400159b063aac4080029be1574588100053642ae8b102000ae4815d162040014dd0a3a2c4080029b614745881000567418e8b102000acd831d16204001c5ea92a2c4080029ba16735881000536c2ce6b102000ae7815cd62040015c902b9ac4080029ba14735881000536c28e6b102000aae841cd620400155b0839ac408003335cc735881035f33886a6b10206be6510d4d62040d94db0b29ac40800393d4e535881000727c1aa6b102000e4e7354d6204001c9ae6a9ac4081b399c41535881036732882a6b10206ba6e8514d62040014dd0b21ac4080029b61643588100047743886b1020008ed8710d62040014dd0a21ac4080029b61443588100053742ce2b102000a6d859c56204001ccea328ac408002abe11515881000556422a2b102005aea8014562040015d30028ac4080029ba14415881000536c2882b102005aea8010562040015d30020ac40801a3ba1f315881000476c3e62b102000a6e85cc562040014db0b98ac408002aba13315881000556c2662b102000a6e850c562040014db0a18ac408016baa00315881000574c0062b10200487c85dd9420400b17909bb284080163b20b76508100043fc2aeca10200487c855d942040010fb0dbaa84081a70f99375508100062f31eeaa102068c6e62dd542040010fd0eb2a84080021f21d655081002c5e43ac8a102000c3f755914204001878eab22840800317dd563508100062e3aac6a1020058ec8758942040018deeab1284080031b1d562508100065ab26e2a102000cd563dc542040019cac5b8a84080023d61871508100066ab18e2a102000ce5621c54204001972c8b8482080aa1f61b75504103161f326eaa082000c5e63dd541040018dcc5baa82080021fa1d655041004c3e43acaa082000c3f755914104001878eab22820800317dd563504100062e3aac6a082000c6f7558941040018d8eab1282080021fe1975884100061f322eb1082000c5e635d621040bb8dcc4bac420817a1fe1d65884102ec3ec3acb1082000c3e75592210400187aeab244208003179d563884100062ebaac710820058ef8758a21040018dceab1442080031b5d5628841000674b12e11082000c7875dd910040019b0e7bb220080031ee1776440100063c42eec8802000cbb84dd9100400197109bb2200800336e0f76440100066c41eec8802000c7b53dd910040018f2a7bb220080033ae0b764401000674416ec8802000c7b76dd51004001976edba220080032edd874440100066dbb6e68802000ceb76dc910040019d6ec3922008002dce154144010
  | 1 => 0xd08192ca080028f61032594100072699064b28206fa79809c565040010fd0e20aca080021f61c415941004c3f43e62b28200087d87cc5650400147d0998aca080028f61331594100053741662b282000a6d82cc565040010fd0e18aca080021f61c315941004c3f43e42b28200087d87c85650400147d0990aca080028f61321594100052f41e42b282000a5d83c85650400b4f50010aca080029e600215941002c5f43ea8b202000c3f75d51640400b1790eaa2c8080162fa1e43590100051f42c86b202000a3d8590d640400b1790ea1ac8080162fa1e42590100061fbaceab202000a3e859cd640400147b0b39ac8080028fa1473590100051ec28e6b202000aae821cd640400155b0439ac8081b28f61653590100070fa9ca6b202000e1f8354d64040d747d0a29ac8080028fe1572590100051e42ae4b202000ab4815c9640400147d0a392c8080028f61472590100054f418e4b202000a9d831c9640400117d0e292c8080022f61c52590100054f418a4b202000a9d83149640400147d0b992c8080028f61732590100070ea9e64b202000e1d534c9640400117d0e192c8080022f61c32590100051f42864b202000a3d850c96404001d1a64192c8080028fa1471590100051ec28e2b202000e3751945640400117f0ea8ac8080222f21d51590100445f43e62b2020008bd87cc5640400147d0b98ac8080028f61731590100055741662b202000aad82cc5640400147d0a18ac8080028f614315901002d5d40062b202000ab9800c5640401117d0f90ac8080022f61f21590100051f42e42b202000a3d85c85640400153d0790ac808002a760f215901002d5d40042b202000ab98008564040018beeb3aac6081b29761e7558c1035f2b884eab18206be55109d563040018bf0ebaac6081b395c417558c103672a882eab18206ba5e851d563040014bd0bba2c608002976177458c100052f428e8b182000a5d851d1630400159d043a2c608002b36087458c100070faa4a8b182000a5e85dc963040014bb0bb92c608003175d77258c100062ebaae4b18206ead7815c963040015a902b92c60800297a147258c100052ec28e4b182000a9e841c9630400153b08392c608003335c87258c100046f438a4b1820008dd87149630400153d08292c608002a76105258c100046f43884b1820008dd8710963040014bd0a212c608002976144258c1036d6cc04e2b182000e5751945630400153f08a8ac608002a72115158c100052f42882b182000a5d85105630400b5b50020ac608002b66004158c1003c6f43e42b1820008dd87c8563040014bd0b90ac608002976172158c100054f42642b182000a9d84c85630400b5b50010ac608002b66002158c1000666192e6b1020008f4815cd62040058bce6a9ac408003175cd535881002c7743ea4b102005
  | 2 => 0x95318910006373b2a63122000e2f6454c6244001c58c8a98c48800393d8d53189100072631aa63122000ae6868c46244001d48c9188c488003b118e31189101e572432623122000ea4644c46244001d88c6988c4880121fa1776509100043ec2eeca1220028de83dd942440011bb07bb284880121fa1676509100043ec2ceca12200087f855d942440090f90abb284880022fe1176509100046fc1aeca1220028dc835d942440011df04bb284880023de0576509100243e428eca12200087e86dd542440d3878c9baa84880031718f755091034636316eaa12200087e87d9542440010f90fb2a84880062fa1f64509100061fbaec8a122000c3c75d9142440018beebb1a8488003171d7635091001c7743ec4a122000c6f75d8942440018d8ebb1284881c21fa1b75505103161e326eaa0a2000c5c63dd541440018d8c5baa828818e1fa1f65505102043e43ecaa0a2000c3f75d914144001878ebb2282880ff2e1c364505100062fbaec6a0a2000c5c75d8d41440018deebb1282880031b1d7625051013c3e432eb10a2000c3c645d621440018b8c6bac42881771b18975885100043fc3ecb10a200e87d87d96214400187cebb2442880030f5d764885100062f3aec710a2000c5d75d8e21440018dcebb1442880031b5d762885100066a31ced10a205de64625d62144001cc8c5b2c4288003a918b64885100065b3b0c910a2000ea4621922144001d88c5b1c4288006b9a1b6288510006733b6c510a2000e6421d9521440719d0e1b1242881031d1db654851000732316ca90a203fcb476d91214407d968ec3224288003a918864485101ee6a3b6c690a2001ce476dc921440719c8edb1242880e378dc8704851000672316e2a022000cb7641c540440019c8c438a80880021fa1b75481100061e326ea9022000c5c63dd520440998d8c5baa40881361fa1f65481102643e43eca9022000c3f75d912044001878ebb22408800317dd763481100062e3aec69022000c6f75d8920440018d8ebb1240880032d19371481100066a31ee29022000cb4641c520440019a8c638a408800339d88714811002cf243a429022005ae486485204400b7c10090a40881031e9db65c41101fe5d3b6c98822003cba76193104407b9b4edb1e20880e33a9db62c411000e753b0c58822000c3f749d165040d90fb0f39aca0800317dce73594100062fc1ae6b28206b87e871cd65040010fd0f21aca080021f61e43594100043f43886b28200087d8710d65040014dd0421aca080029b60843594100051f420e4b282000a3d841c965040014bd06392ca080029760c72594100043f43884b28200087d8710965040014bd06212ca080029760c42594100043f43e64b28200087d87cc965040018bae7992ca08003175cd32594100043f43864b28200087d870c9650400147
  | 3 => 0x6b122000c5c7518d624400193ee831ac488003271d063589100243f43eeab12200087d83dd5624400117f08baac48800e2f21175589100046fc1aeab1220028dc835d562440011df04baac4880021fa1c755891001c5f43ee8b122000c3f75dd16244001878ebba2c4880030fdd474589100061e3a8e8b1220028de87dcd62440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018bf0bb9ac4880031721773589100043fc2ae6b12200487c855cd624400117f08b9ac48800e2f211735891000477c12e6b1220008f7815cd62440011bd0e39ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880021fa1f53589100243e43ea6b122000c3f74d4d62440e9878e9a9ac48800317dcf53589100162e39ea6b12200087e8754d62440010f90ea9ac4880030fdd1535891039e1e3a2a6b122000c5f7354d62440058b8e6a9ac4880031bdd77258910006363aee4b122000caf74dc96244001958e9b92c48800333dcf72589100066639ee4b122000cb474dc562440019a8e7b8ac4880031b9db651891000536c1eca3122000e6571d9462440011db0f328c4880029ba16651891000557424ca3122000aad84994624400159d07328c488002b360e651891000477c3aca3122000aaf84594624400155908b28c488002b3e0d65189100056641aca3122000a6e8619462440018dcec328c4880029b60c651891000733388ca3122000e6571194624400195cedb20c4880038bd9764189100071632ec83122000ea571d9062440011db0f320c4880029ba16641891000536c2cc83122000aae84990624400159d07320c488002b360e641891000477c3ac83122000a6f8559062440014d90ab20c488002b3e0d64189100056641ac83122000aae86190624400195cec320c4880038bd94641891000716328c83122000ea57119062440e5d4c20320c4881cba90406418910006673b6c63122000e4f65d8c6244001c98cbb18c488003a3d93631891000746326c63122000e4f85d8c6244001c990bb18c488003b15c7631891000476c3cc63122000a6e8598c62440014db0b318c488002aba12631891000556c24c63122000ace8398c62440011df0eb18c4880029be1563189100053642ac63122000aaf8458c624400155908b18c488002b9e05631891000537428c63122000a6d8518c624400159d0c318c488003339d8631891000727b28c63122000e4c6518c6244001d1ec8318c488003a3190631891000727428c63122000e4d8518c6244001d8b02318c488003b19c4631891000762b88c63122071ec61018c62440e3d8820318c4880029ba1b531891000536436a63122000c6e76d4c6244001c5ec9a98c4880038b193531891000727b1ea63122000e4c63d4c62440014dd0ca98c4880029b21
  | 4 => 0x24400159906b2ec4880029b60c65d891000717b2ec9b122000e2c65d9362440014dd0b326c4880029b61664d89100056741cc9b122000acd8399362440014df0ab26c4880029b21564d891000567c1ac9b122000acc835936244001c5eca326c4880038b19464d891000727b2ec7b122000e4c65d8f6244001d1ec9b1ec488003a319363d891000727c2ec7b122000e4c85d8f62440014dd0b31ec4880029b61663d891000557424c7b122000aad8498f62440014df0ab1ec4880029b21563d891000557c22c7b122000aac8458f62440014dd0a31ec4880029b61463d891000727b28c7b122000e4c6518f6244001d1ec831ec488003a319063d891000727428c7b122000e4d8518f6244001d8b0231ec4880029ba1b53d891000536436a7b122076c6e76d4f6244001c5ec9a9ec4880038b19353d891000727b1ea7b122000e4c63d4f62440014dd0ca9ec4880029b21953d89103ae373b2a7b122000e2f6454f6244001c58c8a9ec48800393d8d53d89100072631aa7b122000ec4638c762440715c90c98ec488002aba1275d891000556c24ebb122000ace839d7624400159b073aec4880029ba1774d891000536c2ee9b122000a6e859d362440014db0b3a6c488002b3a0e74d891000566c1ce9b122000e2f5495362440014dd0b39ec4880029b61673d891000557424e7b122000aad849cf624400199ee739ec4880029ba1473d891000536c28e7b122000ae6811cf62440715cb0239ec48800393d4e53d891000727c1aa7b122000e4f7354f6244001c98e6a9ec4880029ba1643d891000536c2c87b1220008ee8710f62440011db0e21ec4880029ba1443d891000536c2887b122000a6f855c762440014d90ab8ec488002abe1171d891000556422e3b122000acf835c7624400159906b8ec488002abe1151d891000556422a3b122000a6e8510762440014db0a20ec4880e23ba1f31d891000476c3e63b122000a6e85cc762440014db0b98ec488002aba1331d891000556c2663b122000a6e850c762440014db0a18ec4880029ba1770d891000536c2ee1b122000a6e85d0362440014db0ba06c4880029ba1730d891000536c2e61b12200487e86dd562440018d8c5baac4880021fa1f65589100061e3a6cab122000c5c73d9562440010fd0e32ac4880030f1d065589100062e398cab122000c3f65dd16244001878cbba2c4880032b18b74589100045f43ec8b122000c3f75d916244001878ebb22c488003271cf64589100045f438c8b122000c3f751916244001878ea322c488003271cc64589100146f436e6b122000c5f65dcd62440018b8cbb9ac48800327d9373589100064e326e6b122000ccc62dcd62440011bd0fb1ac48800317dd763589100062e3aec6b122000c9f74d8d6244001938e9b1ac48800237a1c63589100062fba8c
  | 5 => 0x80022f61e63191100051f42cc63222000a3d8598c644400155d05318c888002ab60a63191100045fc3ac63222000a3f8558c64440014790ab18c888002abe09631911000556412c63222000a3e8518c644400147b0a318c88800387d9463191100070e328c63222000e1e8518c6444001c3b0a318c888003a560463191100051f436a63222000a3c86d4c644400187ceda98c88800387d8f53191100070e31ea63222000a3e8654c64440014790ca98c8880030f9d953191100070fb1aa63222000e1c6354c644400147d0b310c8880028f61662191100054f41cc43222000a9d839886444001d28c7188c8880faad21931191100074a31a623222000a5e86dd763440018bcedbaec68800297a1875d8d100062f3b0ebb1a2000c5e76d9763440011bb0f32ec68800297a1665d8d100054f424cbb1a2000a9d84997634400159d0532ec688002b360a65d8d100046fc3acbb1a2000a9f84597634400153908b2ec688002b3e0965d8d1000566412cbb1a2000a5e8619763440018bcec32ec688003279db64d8d100070fb2ec9b1a2000e1c65d936344001c3eebb26c688003871d764d8d100046ec3cc9b1a2000a5e8599363440014bb0b326c688002a7a1264d8d1000567414c9b1a2000acd8299363440011bf0eb26c68800297e1564d8d100052e42ac9b1a2000acf82593634400159904b26c688002a7a1864d8d100064f3b0c9b1a2000e1f651936344001c38ca326c68800387dd464d8d100070e3a8c9b1a2000a5e8598b63440014bb0b316c688002a7a1262d8d100054ec24c5b1a2000a5e859d763440018baea3aec68800297a1c75d8d100062f438ebb1a2000a5e859d363440014bb0b3a6c688002b3a0a74d8d1000566c14e9b1a2000a5f855d363440014b90aba6c68800387d5254d8d100062fbaee5b1a2000a5e859cb63440014bb0b396c688002a7a1272d8d100054ec24e5b1a2000ccf729cb63440014bf0ab96c6880029721572d8d100062fbaae5b1a203aad6811cb634407b5ab02396c68800237a1c52d8d100046ec38a5b1a2000a9e8414b634400153b08296c68800237a1c42d8d100046ec3885b1a2000a5e8510b63440014bb0a216c688002a7e1151d8d100054e422a3b1a2000a5e8510763440014bb0a20ec6880f637a1f21d8d100046ec3e43b1a2000a5e85c8763440014bb0b90ec688002a7a1321d8d100054ec2643b1a2032ad681dc363440014bd0ba06c6880029761740d8d1000666196e7b122000c5f7354f62440058b8e6a9ec4880123be1d52d89100053742e65b122000a6d85ccb6244001c9aa7996c48800a3be1d32d89100166739a65b122000e4d534cb62440014db07b2ec488002aba1265d891000556c24cbb122000ace83997624400159b0732ec488002abe1165d891000556422cbb122000acf835976
  | 6 => 0x51ec2cc5b222000a9e8398b644400153b07316c888003a518e31d91101fd5a43263b222000c3d751d7644400147d0b39ec8880028f61673d911000557414e7b222000aad829cf644400147d0a39ec8880028f61473d91100055b408e7b22203fab5811cf6444001c3ea729ec88800387e0d53d91100051f42ee5b222000a3d85dcb644400147d0b396c8880028f61672d91100054f41ce5b222000a9d839cb644400156d02396c8880fead60472d91100045f438a5b2220008bd8714b644400153d06296c888002a760c52d91100051f42e65b222000a3d85ccb6444001c3aa7996c8880038754d32d91100045f43865b2220008bd870cb644400147d0a196c8880028f61432d91100074699065b2220778bf87547644407f1790ea8ec8880fe2fa1f31d91100045ec3e63b222000a3e85cc7644400147b0b98ec888002aba0b31d911000556c1663b222000a3e850c7644400147b0a18ec8880fe2fa1f21d91100045ec3e43b222000a3e85c87644400147b0b90ec888002a7a0f21d91100054ec1e43b222000a3f855c364440014790ab86c8880028fa1730d91100051ec2e61b222000c3c64dd564440010fd0fb2ac888003171cf655911000636396cab22200087e8719564440018b8e632ac8880031b1c865591100062fb2ee6b222000c5c65dcd6444001938c9b9ac88800317dd463591100062e3a8c6b222000ccc7218d64440018decbb92c8880031b197725911000656326e4b222000ccc63dc964440090fd0fbaac8880021f60f75591100045fc22eab2220008df835d564440051b906baac8880023be09755911000c76412eab22200087e871d5644400187eebba2c8880030f1d774591100146f43ee6b222000c5f75dcd64440018b8ebb9ac88800327dd373591100062fc2ee6b222000c5c85dcd64440010ff0ab9ac8880121f21573591100045fc22e6b2220008ef825cd64440031d904b9ac88800237a1c73591100062fba8e6b222000c5c751cd644400193ee839ac8880021fa1f53591100243e43ea6b222000c5f73d4d64440058b8e7a9ac8881db1b1cb53591100043f43aa6b22200087c8754d64440018bee6a9ac88800b171cd53591103ae36392a6b2220018ee87dc964440018deebb92c8880031b1d7725911000657ba6e4b222000ccf73dc96444001998e7b92c8880031bd4f725911000636a9ee4b222000c6f751c964440018d8ea392c8880032bdd0725911000667b98e4b222000ccc731c964440019c8e5b8ac8880030f9db65191100051ec1eca32220008bd87994644400147d0b328c888002a7a0e65191100054ec1cca3222000aae82994644400155b05328c8880022fe1d65191100054fc1aca3222000a9c83594644400155f04b28c888002ab20965191100051f430ca3222000c3e76194644400147b06328c88
  | 7 => 0xbc845cd62840010fd0fa9ac5080121f21f5358a100043f43aa6b14200087c8754d628400b1d90e992c50800b331cd3258a1000726a9a64b14200087f855d942840090f90abb2850800237e0d7650a100146e41aeca1420058bc875914284001878eab228508006ab2096450a100061e3aac8a0c2000a5e8399365440014bb07326ca880029ba0a64d951000536c14c9b2a200087e86dcf65440090ff0fb1eca88003175cf63d95100043ec3cc7b2a2000a3e8498f654400147b0931eca880029ba0a63d951000536c14c7b2a200087f8758f654400147f08b1eca880028f21163d951000537c12c7b2a2000a6c8258f654401d0fb0e31eca88003175cc63d95100062ec38c7b2a2000e558118f654400147d09316ca880028f61262d95100052f41cc5b2a2000a5d8398b6544001ca8c718eca881029d21931d95100072a31a63b2a2000c3d741d365440010fb0f39eca8800317e0d73d95100043f438e7b2a2000c5d731cf65440f34ed0239eca881029d60473d95100043f43c87b2a200087d8790f65440010fd0e21eca880021f61c43d95100053741087b2a2000a6d8210f654400147d09396ca880028f61272d95100052f41ce5b2a2000a5d839cb65440f14ed02396ca881029d60472d95100043f43885b2a200087d8710b65440014bd06216ca880029760c42d95100043f43e65b2a200087d87ccb65440018bee7996ca8800317dcd32d95100043f43865b2a200087d870cb654400147d08196ca880028f61032d95100072699065b2a200087e87107654401d0fb0e20eca881021fa1f31d95100043ec3e63b2a2000a3e84cc7654400147b0998eca880029ba0b31d951000536c1663b2a200087e870c7654401d0fb0e18eca88003954c431d95102043f43e43b2a200087d87c87654400147d0990eca880028f61321d95100052f41e43b2a2000a5d83c8765440614ed03b86ca880021fa1f40d95100043ec3e81b2a200087e87cc365440010fb0f986ca880030f5d754d91100245fc3aa9b222000a3e8590f644400147b0b21ec88800a2fe1d43d91100051ec1ecbb222000a9e83997644400153b0732ec888002aba0a65d911000556c14cbb222000a9f83597644400153906b2ec888002abe0965d911000556412cbb222000a3d83197644400147d0b31ec8880028f61663d911000557414c7b222000aad8298f644400147f0ab1ec8880028f21563d911000557c12c7b222000aac8258f644400147d0a31ec8880028f61463d91100070fb28c7b222000e1c6518f6444001c3d0a31ec8880038761463d91100074ac08c7b222000a3e86d4f64440014790da9ec8881d30f9db53d91100070fb1ea7b222000e1c63d4f644400147d0ca9ec8880028f21953d911039e1f3b2a7b222000e1f6354f6444001c38c6a9ec8880028fa1662d91100
  | 8 => 0xea39ac89000327dd073591200043f43ea6b22400487c87d4d64480018bee7a9ac89000b171cf53591200043f43aa6b22400087c8754d64480018bee6a9ac89000b171cd53591200145e43a86b224002c9c7350d64480051d90e992c89000b331cd325912000726a9a64b224000e8d434c964480018eeebb8ac8900031d1d771591200066bb9ee2b224000cd473dc564480018eea7b8ac8900031d54f71591200063bba8e2b224000c74751c5644800196ee838ac89000335dcc71591200066a398e2b224000ce7721c564480018eea638ac8900031d54c71591200065ba18e2b224000cb5431c564480019cc6438ac890003394c8715912001c5f426ebb0a40008bd84dd7614800156d0998ec2900121fa1b755852025c3e436eab0a400087e87d956148001878e9b2ac290003171cf65585200043f438cab0a4000c3c7419561480018b8e632ac2900030fd9774585200061e32ee8b0a4000c5f65dcd61480018b8cbb9ac2901eb1b5c865185200047bc3ac230a4000ab48458461480015a906b08c2900021fe1574185200243e42ae830a4002c5e7354c61480018bae6a98c29000b331cd321852000726a9a6430a4000ae7814c861480015e300208c290002ada13311852000572c166230a4000ec5320c461480010ff0abb482900121f21576905200243f42eeca0a400087d85dd941480090fd0b3b282900021f61676505200243e428eca0a400087e86dd541480010fd0fb2a82900021f21f655052025e363b6ca90a40138ee871852148001cceca30a42900030f5d754d93100162f39aa7b262000c5d7354f64c400517f0ea1ec98800b279cd43d93100243f43eeab26200087d83dd564c400117f08baac9880021fa1c75593100061e3aee8b26200087f855cd64c40090f90ab9ac9880021fa1f53593100243e43ea6b26200087e8754d64c40010f90ea9ac9880021f61e75d8b100243fc3aebb16200087f835d762c40090fd0bb9ec5880021f61773d8b1001c5f426e7b1620008bd84dcf62c40090ff0fa9ec5880021f61f53d8b100043fc3aa7b16200087d8754f62c40051df0e996c58800b339cd32d8b1000726a9a65b1620008bf845d562c400717908baac5880121fa167650b100043ec2ceca1620028de839d942c40011bb073b285880021fe157650b100243e42aeca1620018be87d9142c4001878ebb228588006aba0b6450b1016d1e42ac920e20058be87d9141c4001878ebb2283881771d5d9758871002c7743ec490e20009d583dd921c40017c301b12438807a8f215645031002cf243a4290620058be87d51648400187eebaa2c90800317dcd53592100162e39aa6b2420058bc8750d6484005938e6a1ac9080121fa1f7558a100043ec1eeab14204b87e871d562840010ff0ab9ac5080121f2157358a100045fc22e6b1420038
  | 9 => 0x75586200045fc22eab0c40038bc845d561880011bf06baac31000a3720d755862001c5f43ee8b0c4000c3f75dd16188001878ebba2c3100030fdd474586200061e3a8e8b0c40028de87dcd61880018beebb9ac310003171d773586200064fba6e6b0c4000c9c74dcd61880018bf0bb9ac3100031721773586200066610ee6b0c403dccf20dcd618807b99a41b9ac3100021fe1573586200243e42ae6b0c40008bf845cd618800717908b9ac31000317dd473586200062e3a8e6b0c4000c9f741cd6188001938e839ac3100021fa1f53586200243e43ea6b0c4000c3f74d4d61880e9878e9a9ac31000317dcf53586200162e39ea6b0c400087e8754d61880010f90ea9ac3100030fdd1535862039e1e3a2a6b0c4000c5f7354d61880058b8e6a9ac31000b351ce315862002c7a43a62b0c400087f855da41880090f90abb483100021fe1576506200243e42aeca0c40008df835d941880051b906bb283100030f1d564506201e477c3ac310c4000acf835862188001ad2eab8443100021fa1b73d95200243fc3ec7b2a4000c5d73d8f65480010fb0f31eca900021fe1d63d95200051fc22c7b2a4000a3c8458f65480014ef02b1eca900029d20563d95200c43ec38c7b2a4000a3e8418f654800147b0831eca90003175cc63d952025d3643265b2a4000d4f734cb6548001c98c6996ca900030fdd274d95200061eba0e9b2a4000c5f32dcf65480018ba65b9eca900021f61e73d95200062fc1ae7b2a400087e871cf654800147d0839eca900028f61073d95200062eb98e7b2a404ca6e821cf65480974db0439eca900021fa1e43d95200043ec3c87b2a400087e8710f65480010fb0e21eca901329ba0843d952000536c1087b2a4000a3e84dc7654800147b09b8eca901329ba0871d952025d36c10e3b2a400087e8710765480010fb0e20eca900021fa1f31d95200043ec3e63b2a4000a3e84cc7654800147b0998eca901329ba0b31d952000536c1663b2a400087e870c765480010fb0e18eca901321fa1f40d95200043ec3e81b2a404c87e87cc365480010fb0f986ca9000b331cd32d912000726a9a65b224000e8e434cb64480090fd0b38ec8900021f61671d91200043f43ecab224000c5c73d9564480010fd0e32ac890003171cc65591200062fb2ee6b224000c5c65dcd64480018eecbb8ac8900031d19771591200063bb28e2b224000c74651c56448001968c838ac8900121fa1f75591200043ec1eeab2240008df835d564480051b906baac8900023de0575591200047a40aeab22400087e871d564480051bd0fb9ac89000317dd773591200062e3aee6b224000c5f85dcd64480018b90bb9ac8900021fe1573591200243e42ae6b2240008bf845cd64480011ef02b9ac8900023d20573591200046f438e6b224000c5f751cd64480018b8
  | 10 => 0xb22420487c855cd64484011f700b9ac8908163e20173591210043f43ea6b22420487c87d4d64484010fd0ea9ac8908021f21d535912100c5fc3ac920a422da3c855924148401878ebb2282909771b9d975885212eeb338aeb10a42018ec865c221484719d0c0b8442908022fe1175d812101c5e422ebb02420087f855d360484090f90aba6c0908e333d8973181210047dc3ac0302426c87d879cd65900018bee739acb2000317e0d735964035c3f438e6b2c8000c6f729c965900b147d08392cb200028f61072596400052f418e4b2c8000a5d831c965900010fd0f992cb200021f61f32596400062eb9e64b2c8000c5d734c965900010fd0e192cb200021f61c32596402c51f42064b2c8000a3d840c96590001c9a64192cb200031ddc671596400051fc22e2b2c8058a3c845c565900010fd0f98acb200021f61f31596402c51f42662b2c8000a3d84cc565900014dd0598acb200029b60b31596400043f43862b2c800087d870c565900010fd0f90acb200021f61f21596402c51f42642b2c8000a3d84c8565900014bd0790acb200029760f215964002d3d40042b2c8000a7980085659000b1d90e992c52000b331cd3258a4000726a9a64b14800487e85dc562900010fb0bb8ac5200163d61e31986400062fb9aa6b0c8002c5c7354d61900090fd0bb92c3200021f617725864002c7a43a62b0c803e8bf8758641900090fd0bbb443200021f61776886400243f42aed10c800087f865d621900010ff0eb2c43200021f61d658864002c7ac3cc310c8000c3e65dd1219000b1e90eb0a432000317dcd53d89400162e39aa7b128002c9c7350f62500010ff0ab8ec4a00121f21571d894000c5e422e3b1280008df835c762500051b906b8ec4a00033918871589403dc9f43eeaa128068c3c76dd542500d1c58c5baa84a0006aba1b62509401f45f436e2a128000d3875dc142500010ff0ab96c2a00121f21572d85400047bc3ac230a8000ae482584615000717908ba8c2a00121fe1d75185400061fc22ea30a8000c3c845d461500010ff06ba8c2a00030fd0975185400061ebaea830a800487e85dcc61500010fb0bb98c2a00121fe1f53185400043ec3ea630a800087f8754c61500010fb0ea98c2a00028f21542185400061ebaa8430a8000ab781508615000156b09908c2a018e4fa1f75505400a45f438c2a0a8000c3c751854150001a70ebb8282a00121fa1476885400043ec28ed10a800487e851d921500010fb0a3b242a00162f21974485400f49e42ae890a80058be87d51648800187eebaa2c91000317dcd53592200162e39aa6b2440058bc8750d6488005938e6a1ac9100121fa1471592200043ec28e2b2440008bf845d6618800717908bacc3100021fe1574986200243e42ae930c40058f5878c661880090fd0fbaac3100021f60f
  | 11 => 0x884010fd0fb1acb108028fa1363596210051ec26c6b2c422787e8798d658840147d0931acb108028f61263596210062fb9cc6b2c420487e8758d65884018bee6b1acb108021fa1c6359621006a6b9a64b2c4200e4e634c9658840187ee93a2cb108030f5d074596210043ec3ce6b2c4200a3e849cd658840147b0939acb1080317dce73596212ed37414e6b2c4200a6d829cd65884018bf06b9acb1080317cc973596210062e992e6b2c420087e871cd65884010fd0f21acb108021f61e43596210043f43886b2c420087d8710d65884bb4dd0421acb108029b60843596210043f43882b2c425d87d87105658844f0fd0f98acb108021f61f31596210051f42662b2c4200a3d84cc565884bb4dd0598acb108029b60b31596210043f43862b2c425d87d870c5658840147d09382cb108028f61270596212ed3b40ce0b2c423ba75819c165884014df04b82cb109769b20970596210043f43e80b2c420087d87d0165884014ed02202cb108029d60440596210043f43e60b2c420087d87cc165884010fd0e182cb108021f61c30596210051f42060b2c4200a3d840c165884bb4dd04182cb108029b60830596210053b40860b2c4200a75810c165884010fb0f32ec910803179ce65d92210043fc3acbb244200c5e7359764884018bccab9ec9108031759573d92210146f41eebb2442008dd83dd764884010fb0f3aec9108121fe1d75d92210043fc1aebb24420487e85dcf64884010fb0bb9ec9108023761e73d92210062f3ace7b244200c5d759cf64884051bf0eb9ec910803179d573d92210062ebaae7b244200c5e855cf64884018bb0ab9ec9108121fe1f53d92210043ec3ea7b244202c5e73d4f64884018bae7a9ec9108021fe1d53d92210043ec3aa7b244202c5e7354f64884018bae6a9ec91080a2fe1d43d92210164f39a87b2442028ef874cb648840599ce6996c9108039354d32d922100746a1a65b244200cd5739c764884f99cae538ec910802a7a0f74592210045f43c86b244202cce734c96488401c9aa6992c910803a390d32592210243f42ee0b24420087d85dc164884550fb0dbaa83108021fa1d655062113c3e43acaa0c425ec767199660884090fd0bba2c1108021f61774582210062fb9aa6b044202c5c7354d608840599ce6992c1108039354d32582210243fc32ea304420087d87994608840187ce9328c110803179ce65182210043fc3aca3044200c3e7459460884018bce6b28c1108030f99574182210061eb2ae83044200c5e655cc60884018bacab98c1108023ee1d60182210061ebaea9b224202c5e7354f64484018bae6a9ec89080a2fe1d43d91210164f39a87b22420087f855c364484090f90ab86c8908121fa1f75591210043ec1eeab2242008bf845d564484010fd0e3aac8908030f1d774591210043fc2ae6
  | 12 => 0x237e0d70185420146e41ae030a8402ccc734cb6050801c9aa6996c0a1003a350d32d81420243f42ce3b02840087d859c760508051bd0738ec0a10023760e71d81423ee1eba0cb302840487e86dd560508d10f90dbaac0a10021fa1f65581420062e39ecab02840087e8719560508018b8e632ac0a100317d9773581420062e32ee6b028400c7765dc560508018e8cbb8ac0a10031dd9471581420063a328e2b02847bc3e7419460508d587ae8328c0a10023ee1d60181420162f39aa6b148200c5d7354d629040593ce6a1ac5209ee4fa1f7550a413461fbb6eaa148268e2e62dd5429040355f0cb12852088e2f61b7150a410069bbaee2a148200d34751c542904090fd0fbaac1208030fa1375582410061ec26eab04820087d83dd5609040187e85baac1208030fdd754582410043fc2ae6b04820487c855cd60904010fd0fa9ac1208121f21f53582410043f43aa6b04820087c8754d60904014790aa12c1208030fdd542582410047dc3ac0304820087e86dcf65504090ff0fb1ecaa0803175cf63d95410043ec3cc7b2a8200a6e8298f65504014db0531ecaa08021fe1d63d95411543ec38c7b2a8200c5d7318f65504014bd07316caa08029760e62d95410043ec3ce7b2a8200c5f835cf65504010fd0e39ecaa0803175cc73d95413151f424e5b2a8200a3d849cb65504014bd07396caa08029760e72d954100636b90e5b2a820087e87ccb65504010fb0f996caa080317dcf32d95410062fb9a65b2a820087e870cb65504010fb0e196caa098a8fa1032d95410051ec2065b2a8200e4d320cb65504c50fd0f98ecaa08021f61f31d95413151f42663b2a8200a3d84cc765504014dd0598ecaa08029b60b31d95410043f43863b2a822a87d870c765504c50fd0f90ecaa08021f61f21d95413151f42643b2a8200a3d84c8765504014bd0790ecaa08029760f21d95413151f420e1b2a8200a3d841c365504010fd0f986caa08021f61f30d95410043f43861b2a820087d870c365504c547d08186caa08028f61030d95410053741061b2a8200a6d820c365504014ed02186caa08029d60430d95410043f43841b2a820087d8708365504c547d08106caa08028f61020d95410052f41841b2a8200a5d8308365504014ed02106caa08029d60420d954101477c3a65b128202cce734cb6250401c9aa6996c4a08021fa1f65589410043f438cab128263a3e86d9641504c5c6ec3b2c82a080e2f21970905410061e32ae120a823fcb8605c2415040b17908baec0a08121fa1b75581413143e436eab02820087e87d9560504018b8e7b2ac0a08031b1cb65581410043f438cab028200c5c7319560504018d8e432ac0a080317d9773581410062e32ee6b028200c6f65dc960504018d8cbb92c0a098f0f9d065181410047dc3ac0302820087f865cd65
  | 13 => 0x801800400800007803400800401000c00400001000400000800401c00000800000400000000400400004c03400001800002400000002401400800c01c03c00400400c00c00c02801000000400000801c01802406400000000000800000000002c00c00401c00804c00400802401001803400001400000c01000000000800000401402000000000400000001c01c02c01000003000401005002400003002002805c05000000000002000000002004000000400400000c00001c01800000000401801803800400000800000800800004c00404800000800800800400800400800000003800c00000400401400001801000c00801801c00402801c00800400000801c01401400000001401802000000000800401400400400001802c01000000001000401000400002400801000000400000000000800002804002400801402400400800003000001400800800404802801000000005800800000006400801402800800000c00800401801400003802403c00000400403000c00800000c00800001c00402c05400000800c02001401002801800400001800800800002002800000000400800801c02c00807402c00408005000c00000000000405400c03400000003801800400008400000400400000000403c00c0d800404000c000010008028000008020000010fd0db9ecaa10121fe1f63d95420062eb9ec7b2a840087d8798f65508014ed0331ecaa10029d60663d95420043fc3ac7b2a842f87d8718f65508018bae631ecaa11a28f21943d95420070e31a87b2a8469a6c864cb6550801a9ee6996caa10039318d32d954200786a1a65b2a8400c5f32dcf65508018ba65b9ecaa10021f61e73d95420062fc1ae7b2a840087e871cf65508d347d0839ecaa11a28f61073d95420062eb98e7b2a8468a6e821cf65508d34db0439ecaa11a68fa1371d95423451ec26e3b2a8400c75711c765508010fd0f98ecaa10021f61f31d954234d1f42663b2a8400a3d84cc765508d14dd0598ecaa10029b60b31d95420043f43863b2a840087d870c765508d347d08386caa11a28f61070d95420043f43e61b2a840087d87cc365508010fd0e186caa10021f61c30d954234d1f42061b2a8400a3d840c365508d14dd04186caa10029b60830d95420053b40861b2a8400a75810c365508d587ae832ec2a10062f61375d854200c5ec26e7b0a8476c3d74d4f61508eb87ae8a9ec2a100b179cd53d85420062eb9aa7b0a84028f7874c761508018bce7b2cc2a1003179cc65985420062fb2ae730a8400c5c655ce61508019aae7b0cc2a10021fa1f65585420043f438cab0a847ec3f7419561508f7878e8328c2a10023de1d61185420166639a6430a8400e4d534c86150801d1a86990c2a100a3d61e3118542007629946230a840087f855c061508090f90ab80c2a1
  | 14 => 0x588482df2ef00000029080009c80034e26480028904d92287800031200038a26836c3a52d521089fb698000001401be3a199580000000024c80034b0000cf0000d80000000000c680019b0003182f68002f480013c84c33ea852812270c033828c9d11651270bb00000007a80026e87519238b98316883f80038e01fa9b9c5807a311342838000000001078000001ce8478352918308002200c080000007d0000ec934b2f3a8b719fe2f08ce8cc94d1cc2a331a8a70ac9b5135a6d0cb9890530550002bfae5353033a7a0d48e28d30ca2e89c20648002b12141a10d1b6903131c9d411a1220f3a2210b32326d88588a2a890a0b61db2d723f14785ea5a1da9ebad3ba40000000108b005c0003220000003352120002f28a630480000a14a8000001bd0918000000001cb8000003598c88830003952c50000000000001672e32db2d12d8ab700008892d07580002001da2580018780011993080012402a0911a6b089c328b99809db302a11718df30b80000027900000000000000000000000000001e14318d80014a00032a9c28f70dea6a30f0b4800036a2a1af8000288003a80f48001a82cb2bd070b031238a4b5038ca8d395a592cc0c617983625083300287c18b9e626e0000000000bd80000030d2b5800143a242033240a980034401d00012980000023bab98000000c11379428000000eb8ab82580013d00000000000000015791d9e41408001e28000001e6a6034a24a0000000000003043551a1b591dc94593500000000003e99295a8000000020001fa2629d0aac000402002000002003002801400c00000c00801804002c00800400800400800001000000400800802000c00401000c03405400800801000403003000401801002800c00800000003800000400003000402c01000000402801000402400403400001c01400400000804c00000403801401000000003801c00000403400000800000800000003400000000c04800c00000000c00800000400800001000c00402800000c02400800400400801802c00800000400403400400000001801002c00800000400000000000c00000400801c00c00400000c02400001c01400000000000000000c01c00000000000001c00800801800800001400c03800000000800c03c00800001000801400000800c00800000000004000401c00800000000400400000000800c0100680300080000040280a802000401800c00000000802801000001c01000000c05400000800800400004000000000c00000c00003000802400000000402000801000002000c00c01800801404800000800000401000401400000c00400000001c01c00c00800c02400001801401c00002801001000c06c00000001800000400400003c01400000800000000800000000800002000000000000000000c018008000
  | 15 => 0x820000001992db8682be273a428e81a7257ba62dfb07b7592e95939ab791ac80000da269f50ee85980014eafa2ad0000ab05e31b98f800209000386aaf9b485a23c883b320a010d00001580034719db5432900000000000000029695695f10200000011d2e080016a8000000000000000000002740001d69191c60411d00000790000f8072b570d69638578001a38891dc1451c895400000000000018f0b328280000000021780000f14c97500000038335480000000023025300032c9ed0003a3800328a5bb340dd1b183b0be0d52f1a89a38a92b6e800350b1b02f8133150002e028b0d59c41599ee0000000529ae000270800000000113aeeb418000003600000fd0002a221c0002a2a2b1bc2e289887e26ba61800000364af80000003920001998868000000001c795480029caa711282412b3578a0a5b0050f3368ac418a82700000011129918e00000083819a800180ba72c703aa4593b12882780024e2862b48001edb680b1800236b7a33f824b6600026532500f9df32b10580000005606b80003c07db0d8001100101148000000000cc0cdaf72ae0458001f780038a86d80025fafc29b0001ffa008003368000002248192ba0770fc00585a8f2ab21bbab2b0b0000768000000001489b68000000e485caef9000000ae00033599a325ad40c90002c58000002bf0000001ff3528128d283f000230800238007388a8a23e9cf0082953618e100cb4a90614d80039f12780022d8000511a780002d3563490002e98000000000000002de9bda7c06100013a29d0000001178929e308e800128202b611e48003058ad32d057186a059cd07882da002161bb03ca8831922c8d22231de8000718002902431f38001c98002b60000000002440001a02a60fa0002bc306b6b13013aa9eb461f80ba8e53998012849c0b9a1c72c9b4cb33afeb741b831013e9ef0120ff38e9fb00019106c29e29c07eaf58000000aa2f98000000000002dd1d70000001f6b63a5e141aaa8000000000002979411a200000011800000033c8c300000000000000006416f9efaab0189b4323a5280006ca4501e800254b8780012a98d11196b0001cfa6fb1193bb8919b953026af5020a3e008ab02292d98001468000000000000000000001a5982b299393aa00000000000032a03b800000000214800248950b7f000000000218b4f0002ec09493e1f0a5aa8f19c0000003568dc9bf8001ae8048000000c716435b8002702a40001b21fc8ac00036fafb09c35d08b08c8ef1471bc8002f024380000000007b800131a2c1759d61460393448000000000000000000000d3a0899d35f02e0001c50001cd811b522ec9e9231aa82630b412f29f044800153b870d8aa01fe8b682180baeb9eea85a74acb80017f8e6ba12a482a8000111c939c0001e5a228e72d300000000000000
  | 16 => 0x1e20002018a400028fa98000193aed21b8760000000bf8002f2000000009863b7b8000000000000002e236d23a8fdb050779a62e912c23785ba49ae4af31dfa9a8d90e5ba239bb2ead180039780000000009b06a0000000000000001950183858002ce8959ad9370000001498000feb408000c28002a90000000db2688420378a78df80011235b20e37a9aa8000000000ea87010b80000000397392080022ea721bf0e02988001cc8000c789a8f90c50b39f22fa88f9ec2ca9678000fe1fb8800931151882938002370592fb8231c1b392b80470000000000001ca8000000670000001312ad95b2ed800138ab79d50000001b60000003928002e80900d99a880000000037d0000a58001550000001580002111380ee28218b27707cb0e9e197a00019882104d18899f0002f78608a80000f98000001f13a29d992120125c8001609268000001b71f025198484c9158001b10428000a122191a8000f500005f00037b00024f09680000006f38080024c2412c80cd2e785d29490738d0c9b14382800213a5388607a14b35a80028716635c0358000000898440000af30000016c394a4f99e1db8398000000222998002f10001e800029322f97c00000027d00014c20f31c30800019c94f0a38001fa8000001fda9600024623f95604b0003008002a18003900bf14f93984a8000000000000000000000001b00000002c393f994a298c4969a32b45b1d9b9ad589e91b39e8282192580042fd35eb20b7280003a09410fa9f9b389980000910398c9beb9d065868800000061800000378a5400000000014bb3780000012ca7ca550000000000cb0f62dc3a91589f60660873128f7a1c9fd1c39eb00012b829aea2f9000273374b2680023910880020795e8b2800244ace000062b851f302931f16580023b09900031723c00013200036e00028c15c00000000000033602e80000006d10480011e160255b2e2e40002040000002a58001a500000020a19797818180000033f00000037cb213410003621290000002840000000de0030000000250efa3606200025d9a0a7e00016a0000000be8001ab00004605221a39d80011c23200000003e2f88eb0c400008283700016e216a4eacfac6b67af40b80000000002b900013600034d86e0002808b5b58aa98000340000d600000000022117f0d1278baaa06b798e7800125a4d8000000001c00000000842478db91e97288dab890dabcaff21e00000001517e302916b8125c3a09e127b00004300000000016100013f2561668f013315ca2880033d28d80027590a8001ec90315e00000000000000000000000000012039180000000b3582b38002ae800000000000000000396000275000000365b179bab1391c9d830380000020da7f98200001980010e36400038000000003222d00011f21a800000048b51
  | 17 => 0x3429aa102996a0d2408002761d18003840003750fb26c36a80033d8e9000038a0b80034002b0d71ea8b880000000015580000000000000000000025e87b04a16d0e08b20c800d0580002d600032b80000000000004510c8002e69cb000000287a6996bab5000000315ae5b81b2f83d8003489421ea0000000000001870ed26089e00039fb9700000000029a0000000003399c6a62263b7e00035395d1d89972251681f5801b3a2ee39b347a7e8b536d81390409097b2cd961b66900aa784faaf31614480039322a8003a0043a598002398e3080ad80000000002da04b92e0000dd9010000bd2490a2800256b21a1587202c21f81aa6680000000037100029226f0538000000920000001730000001a480000000000030a1368000500001b0970ad7881817337000000384a050001d3b0c35e326396ac296da500d000030c9e3913310b1a271069ab30bc0000fc80008839c98ea6a8000000000001e9b6baba8f09c8390ac32fd8e412a2c20c216ead09841f4a1d34b96281bb631ca351a152beb09a8e14900015004f0000a900000038c332b131900811762c18000263072ab9af0ada5880000037700007100020627a897aa6970000202006a208690799960e8887b480401da23daaca659c137f9fc394324ba6a7d8000002f60e3b198b99a31f428aa86986074b14a359140f88000d43780000c597b800267b8b0548000b78003a331d0003228a888e0002cc80037080c0f22e3800151a0700020480000000000614e0000a5101a1e91609f2de0fab739ab8000002b696200024b8000000ffa1f22638206f9a28329d91e00f19942b193c34e97202397db7c0a228eabba11a0e88d000000067a27b7da4680000000028880000000000000032d80031f851800144164974884aca00000036a3700468002ff80000020c0000000002b09d5800000000000000152a7180039e25f0162c480000e0bc80030e0a30002cf0001e7800346b30b2801a00000002c89b8000000001d30001f88000000002b400008a8f5b6500000000000000038600033a8980003a7963000233a7289517e8000000000000daa830000000000b712f8ae88f349b3315217735fa78295978b5c97900034fa7f183ad90001dd377b0a8d78b12dd94824800000006a8001d29ad31e0142662e633c2670000000c38000b0b060000ca80000005595a09600021317780aa171b91ba040ac00002d480016900000008b85b124b3b91080037320cb5a0fb80011b80000000018a2c107382f0000000002cd234000376a7b9a42bb1e701f0f41b2b0930100000000037e80000024d203a349a916f2c8a19b8d8002ea8001098e98000508001f980000021b0000001c48eda470000001f731e8168003453348669d7a3d367000311276ba49e8b8f841b990f1212800223a182a0aa3b01a4b24a8
  | 18 => 0x1510003763839261f18002c900022f049a1d9852c7b9880013296c9052e18ec05f800000000318b980a68000000ba00034d3a58632d6b558e21801930730002d01f2990800000106b3b0000000af8000938001250742c62330000148000002e70000000002c097100000008c0002420001dd84e0000da20ab8832799ea7997c9090000000002bd80025710805680026caa51b7a0b2819b32aa1768002082282779a9a523430aa8ea24036080015d99fa9437217ab938318002eb00034380000000022b80020f80015ba6b1858000cf92190ea802418b91d23912dc91fafe3021170ce00018100015fa2e05d83480000035d89d34c23a1b59b886ea9d8490003898002512d28000652e109a25d0002098a1a691ce26421000030fad20000000228000f6b6f0000e180000000000006000000017d362b2708517436c8001e50bb8000d08000002610000000000001572fc8002912dab3e10f3a980007f8543168c180013381c0000000001e0b4204e83d01c8dc32003000038f00006b0001f90971ac07f11880000e989b3110c01b0000000002f38001d480012300032c00000000001798c0e623500000033180013d99192d9de00000000002bb3880029700
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1d001878c00480234a5428a20110211038e243000000287c10b2e4cd1e368888900640802c003831a0407c000208a10324300513a5b734cb65508d160c9650d32d954234e83219434cb655080103e9721542582410040fa63755096090401a0d844c832d954100513e59734c9658840160d9498d32596210040fe61741d1658840144f9754d32d922101613e1d534cb648840548f9750d32d922101623e1d434cb6488401a0d844c832596400053164c621c5625000103d9721542185400040f26175508615000144e96dcd32d952000583650634cb654800103f985d074d95200051325d534c9644800584c8754d32591200152325d434c9644800588c8750d32591200071154d321c56448001c85434c8715912000513e5d534cb62c400144c9754d3258a1000683611320cb654400188e874c832d911000623613729cb634400148d940cb73d891000623613739cf6244001a0d844c832594100062361d320c9640400188d845c87258c1000523650325cd620400188d845cc7358810
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
  | 10 => 0x138c
  | 11 => 0x94b
  | 12 => 0x94c
  | 13 => 0x94d
  | 14 => 0x94e
  | 15 => 0x124b
  | 16 => 0x124c
  | 17 => 0x124d
  | 18 => 0x124e
  | 19 => 0x138b
  | 20 => 0x138d
  | 21 => 0x138e
  | 22 => 0x98c
  | 23 => 0x98d
  | 24 => 0x98e
  | 25 => 0x128c
  | 26 => 0x128d
  | 27 => 0x128e
  | 28 => 0xa0b
  | 29 => 0xa0c
  | 30 => 0xa0e
  | 31 => 0x130b
  | 32 => 0x130c
  | 33 => 0x130e
  | 34 => 0xb0c
  | 35 => 0xb0d
  | 36 => 0xb0e
  | 37 => 0x140c
  | 38 => 0x140d
  | 39 => 0x140e
  | 40 => 0xb8b
  | 41 => 0xb8c
  | 42 => 0xb8e
  | 43 => 0x148b
  | 44 => 0x148c
  | 45 => 0x148e
  | 46 => 0xd0c
  | 47 => 0xd0e
  | 48 => 0x94056
  | 49 => 0x95394
  | 50 => 0x94054
  | 51 => 0x138954
  | 52 => 0x138956
  | 53 => 0xb0954
  | 54 => 0x94b14
  | 55 => 0xb0956
  | 56 => 0x1409
  | 57 => 0x140954
  | 58 => 0x95414
  | 59 => 0x140956
  | 60 => 0x209
  | 61 => 0x1449
  | 62 => 0x289
  | 63 => 0x1489
  | 64 => 0x14c9
  | 65 => 0x139254
  | 66 => 0xb1394
  | 67 => 0x138b14
  | 68 => 0x141394
  | 69 => 0x139414
  | 70 => 0x141396
  | 71 => 0xb0994
  | 72 => 0x98b14
  | 73 => 0xb0996
  | 74 => 0x180b
  | 75 => 0x1649
  | 76 => 0x134b
  | 77 => 0x14b
  | 78 => 0x141294
  | 79 => 0x141296
  | 80 => 0xb8a14
  | 81 => 0xa0b94
  | 82 => 0xb8a16
  | 83 => 0xd0a14
  | 84 => 0xa0d14
  | 85 => 0xd0a16
  | 86 => 0x150d
  | 87 => 0x149314
  | 88 => 0xa4d
  | 89 => 0x140b14
  | 90 => 0x140b16
  | 91 => 0x28b
  | 92 => 0x184b
  | 93 => 0xbcb
  | 94 => 0x19cb
  | 95 => 0x148b94
  | 96 => 0x148b96
  | 97 => 0x154d
  | 98 => 0x14cd
  | 99 => 0x2cd
  | 100 => 0xd1494
  | 101 => 0x148d14
  | 102 => 0xd1496
  | 103 => 0x20d
  | 104 => 0x194b
  | 105 => 0x164d
  | 106 => 0x74b
  | 107 => 0x1a49
  | 108 => 0xec9
  | 109 => 0x4954
  | 110 => 0x5554
  | 111 => 0x4956
  | 112 => 0x2c9
  | 113 => 0x24211
  | 114 => 0x28211
  | 115 => 0xecd
  | 116 => 0x1a4d
  | 117 => 0xecb
  | 118 => 0x1a4b
  | 119 => 0x28e
  | 120 => 0x95416
  | 121 => 0x95456
  | 122 => 0x449
  | 123 => 0x44d
  | 124 => 0x20b15
  | 125 => 0x74a13
  | 126 => 0x75493
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1265
  | 6 => 2795
  | 5 => 1878
  | 4 => 38
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (51436+((h/421+packedAt gbK7 (46805+(h % 421)*11) 11) % 1837)*12) 12
  | 6 => packedAt gbK6 (146263+((h/931+packedAt gbK6 (134160+(h % 931)*13) 13) % 5941)*13) 13
  | 5 => packedAt gbK5 (118314+((h/626+packedAt gbK5 (110802+(h % 626)*12) 12) % 2726)*12) 12
  | 4 => packedAt gbK4 (2732+((h/12+packedAt gbK4 (2660+(h % 12)*6) 6) % 46)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffe03fe03fe07ff81ffffffff44f9e3d18f1ff
  | 1 => 0x7ffc1ffc1ff83ffe0f01c07fbb469cee73e93
  | 2 => 0xf83ffe0001fffc3fff001ff80c3871f307cf1c
  | 3 => 0x3ffffffe00003fffffe0000fc07e03f80fe0
  | 4 => 0x3fffffffffffc0000000000fff8003fff000
  | 5 => 0xffc0000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8400440024004400115054280018214085025
  | 1 => 0x682c0ac40a8829a20a04815619428c8632692
  | 2 => 0xd0356a021135682d5a0092b02c285163058b18
  | 3 => 0x4239b336b40420379ccac0204ec07c03b00dc0
  | 4 => 0x843e3ddb39de7301080300c18f7e8003def000
  | 5 => 0xe710201c20184206108c03060fff7fbc000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeae8eee8eaa8eeeaeae8eee8eaa8eeeaeae8eee8eaa8eeeaeae8eee8eaa8eeeaeae8eee8eaa8eeeaeae8eee8eaa8eeeaeae8eee8eaa8eeeaeae8eee8eaa8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36719
namespace PEqualNP.Outside.L_meta_36719
open PEqualNP.Outside.L_meta_36719.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 6 := bs0_3_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 26 := bs2_3_0
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
theorem bs2_4_128 : Interval s2Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 134 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 48 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_3_0 : Interval s3Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 21 := bs3_3_0
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
theorem bs3_4_544 : Interval s3Atlas 4 544 7 := block_range (n:=7) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 551 := (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96)) (concat (concat bs3_4_128 bs3_4_160) (concat bs3_4_192 (concat bs3_4_224 bs3_4_256)))) (concat (concat (concat bs3_4_288 bs3_4_320) (concat bs3_4_352 bs3_4_384)) (concat (concat bs3_4_416 bs3_4_448) (concat bs3_4_480 (concat bs3_4_512 bs3_4_544)))))
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
theorem bs3_5_640 : Interval s3Atlas 5 640 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 666 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 (concat bs3_5_512 bs3_5_544)) (concat bs3_5_576 (concat bs3_5_608 bs3_5_640)))))
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
  · exact alls3_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 26 := bs4_3_0
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
theorem bs4_4_128 : Interval s4Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 134 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128)))
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
theorem bs5_2_0 : Interval s5Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 6 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 56 := (concat bs5_3_0 bs5_3_32)
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
theorem bs5_4_512 : Interval s5Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_544 : Interval s5Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_608 : Interval s5Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_640 : Interval s5Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_704 : Interval s5Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_736 : Interval s5Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 781 := (concat (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat bs5_4_288 (concat bs5_4_320 bs5_4_352)))) (concat (concat (concat bs5_4_384 (concat bs5_4_416 bs5_4_448)) (concat bs5_4_480 (concat bs5_4_512 bs5_4_544))) (concat (concat bs5_4_576 (concat bs5_4_608 bs5_4_640)) (concat (concat bs5_4_672 bs5_4_704) (concat bs5_4_736 bs5_4_768)))))
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
theorem bs5_5_640 : Interval s5Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_704 : Interval s5Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_736 : Interval s5Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_800 : Interval s5Atlas 5 800 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 801 := (concat (concat (concat (concat bs5_5_0 (concat bs5_5_32 bs5_5_64)) (concat bs5_5_96 (concat bs5_5_128 bs5_5_160))) (concat (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)) (concat (concat bs5_5_288 bs5_5_320) (concat bs5_5_352 bs5_5_384)))) (concat (concat (concat bs5_5_416 (concat bs5_5_448 bs5_5_480)) (concat bs5_5_512 (concat bs5_5_544 bs5_5_576))) (concat (concat bs5_5_608 (concat bs5_5_640 bs5_5_672)) (concat (concat bs5_5_704 bs5_5_736) (concat bs5_5_768 bs5_5_800)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 44 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 38 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_1856 : Interval gbAtlas 5 1856 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1878 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)) (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 bgb_5_416)))) (concat (concat (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)) (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640))) (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768)) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 bgb_5_896))))) (concat (concat (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 bgb_5_1120))) (concat (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)) (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 bgb_5_1376)))) (concat (concat (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 bgb_5_1600))) (concat (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 bgb_5_1728)) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 bgb_5_1856))))))
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
theorem bgb_6_2784 : Interval gbAtlas 6 2784 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2795 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 (concat bgb_6_448 bgb_6_480))) (concat (concat bgb_6_512 (concat bgb_6_544 bgb_6_576)) (concat bgb_6_608 (concat bgb_6_640 bgb_6_672))))) (concat (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832))) (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)))) (concat (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184))) (concat (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280)) (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)))))) (concat (concat (concat (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536))) (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728)))) (concat (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))) (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080))))) (concat (concat (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240))) (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)))) (concat (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592))) (concat (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688)) (concat bgb_6_2720 (concat bgb_6_2752 bgb_6_2784)))))))
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
theorem bgb_7_1248 : Interval gbAtlas 7 1248 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1265 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 (concat bgb_7_576 bgb_7_608))))) (concat (concat (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 (concat bgb_7_736 bgb_7_768))) (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)))) (concat (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 (concat bgb_7_1216 bgb_7_1248))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeae8eee8eaa8eeeaeae8eee8eaa8eeeaeae8eee8eaa8eeeaeae8eee8eaa8eeeaeae8eee8eaa8eeeaeae8eee8eaa8eeeaeae8eee8eaa8eeeaeae8eee8eaa8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372968 * 2 ^ 32 + 4008241832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36719.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.or,[3,5]⟩,⟨.and,[2,7]⟩,⟨.or,[4,8]⟩,⟨.and,[1,6]⟩,⟨.and,[5,9]⟩,⟨.or,[1,11]⟩,⟨.or,[6,12]⟩,⟨.and,[0,13]⟩,⟨.and,[9,10]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4008241832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4008241832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36719

open PEqualNP.Outside.L_meta_36719 in
theorem PEqualNP.Outside.L_meta_36719 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4008241832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4008241832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
