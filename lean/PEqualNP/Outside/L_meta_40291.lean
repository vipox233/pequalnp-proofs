import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40291.Model
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


end PEqualNP.Outside.L_meta_40291.Model

namespace PEqualNP.Outside.L_meta_40291
open PEqualNP.Outside.L_meta_40291.Model
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

def SBf (j : Nat) : Nat := [6, 7, 7, 8, 6, 7].getD j 0

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

end PEqualNP.Outside.L_meta_40291

namespace PEqualNP.Outside.L_meta_40291
open PEqualNP.Outside.L_meta_40291.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x2000000000210b20020230df30be42de32be40dc32dd30bc42bd41de31dc31bc40bf41
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xa00006000040000138505071884194b14941a6292614e528c6a8a2984b94a40
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/25+packedAt s0K4 (192+(h % 25)*4) 4) % 12)
  | 3 => 2*((h/23+packedAt s0K3 (189+(h % 23)*3) 3) % 7)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffffe07fffffe07fffffffe03ffff1ffe3f
  | 2 => 0xffc0fffffffffffff81ff80fffffffffe38fff
  | 3 => 0x3fff01fff80fe03fffe0fff03ffc0f80fcf3cc
  | 4 => 0xc00001fffff0003fffff00003ffff000ff03f0
  | 5 => 0xfffffe000000003fffffffffc0000000fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4a4414423122490a01652a544a2194aa0d3615
  | 2 => 0x909228a442449414580a510a94c629546288ea
  | 3 => 0x230a4d2890e90566aaa09d6227688e06b4d34c
  | 4 => 0x3a2cb1d12481d9bb34d3064c39b3c418df03b0
  | 5 => 0x3c30c1e1c70e1e3dc71ce78f01c30860fbec00
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0fcc0ccc0f0c0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40291
namespace PEqualNP.Outside.L_meta_40291
open PEqualNP.Outside.L_meta_40291.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x3040003ce0800002c00410054420a105f00090000000dff10ff20bc43fc40fc30ff31fd21fe43fd32fe40bc40fe42fe30fc31be43fc10ff21bd41fd43fc32fd30ff43fd41ff42fd10fe21fe32ff32fe41bf41ff41fd20ff40bf42ff30fe31fd40bd42ef32fc42fe10fd31fd42fc20fe20ec32fc41fc21fc43be40
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xe8082999100808000808e00938081038380800104b48b07008280802c00800000079901058000820009000680800001818d81800403802c0000040700018702030080929481888200090182db14943d72a0653e54886b8a6904fd5110d7a1065cc320c278a0a15d14520afa9a853f54cca7ca1a0cf94c40b7294633c548427ca810eb0cb419f2a4653d54c839ca6196b90f329e2a2656d52d0f5886194f553309faa421ad52d067aa990cf151209ea88873e54c4278a8884f552219fa8a85ad540cb3ea6a14f550219ea8e853d54c427aa8086b0c9419eaa063cf430cad8a4984fd5132b7a92876d521027ca721db14931d7a16659c438ca78a898d714d429e2a6633e50d0a7ca0204fd51319e29a85af32d0678a9104f54840d6a12413d54082dca5a0eb54840b7290219c5350ab8a6884f95320aea9c43ad42086eea2986bcc941af298213e548c27ca621edd4541e619663cc430ca7aa9214f94e408e29a856e528c33ca621cfd5130b729081cc324c678a6a0cfd50309eaa4616e52d0edaa5184f1533296a9081ad420cadaa5a0d7d4d209ea888174514c27aa421f30ca309faa2413f52506dca5196710c329f2a065ae430ca7ea9106bd53329e2a2613e5410a7aa5206b0c840c6218653e5448678a8185bd4930d62a6653f54cc67ca820cf950319e28283ac32902dea4884f55231d7296833e54cc27aa3204f54b41bba8a413e53d0a7aa521cf95321b7a92633e5010e7aa9195754c10d7990813e54042f0a098cf552419f2a0416e530ca7ca121d7d4d10d621e653d5190ef6a098cf55032d6a1665ad42c835ea4a14f952319f29e836d528c65aa5a0eb94840b6292215e53886daa4084f55121d799481ad428867ca1206e94040
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x26d00204400000138100110f04000900000000125e0c01c01450001920800040400000000001c00028bd9732d070c530c9418b588505068c63508218b588540c28c6354840c314d424820c63548408b58854cc70c6354b41c315032cc70f63548408b58a54cc28c6350b209318d52d063561153328b58a54c428f6510c328718d52d070c540c9319318d521021c6354840a958454cca8d6110c32c318d521022d6215210a3980430ca8c6350a218718d544862f62546438d584540c30e530ca408b58a544868c6354b41a398f54cca2d62942438b18d52d062d650cb41a398e430ca2c6354840c3d885350b0c53d4942c3950328c22f65cc840c3d8d52d062c65509208bd89519030c540c830d20c8504c63860551218b58a540c62d650c840a3594430ca8e6315332c394d428872542145208798f548828c635092087594430ca0c6354b41
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x80000000e0868239a8428a41031cd6215210818e6b14a890c0e73d89519020639ac52a621215c76510c32818ec29a849040c735885050682b88a819061419c76214d42
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 6 => 2*((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s1K5 (800+(h % 30)*6) 6) % 50)
  | 4 => 2*((h/76+packedAt s1K4 (4455+(h % 76)*8) 8) % 165)
  | 3 => 2*((h/55+packedAt s1K3 (2280+(h % 55)*6) 6) % 60)
  | 2 => 2*((h/17+packedAt s1K2 (490+(h % 17)*4) 4) % 10)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0xffffffe07ffffffe07c0fffffc1ffffc8fe3f
  | 3 => 0xfc07ffff80fe07fff800f81fffe1f01f0cfcc
  | 4 => 0xf0007ffffff0007ffffff001ffffe001ff0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2045088c4122440805949292501229541350d5
  | 2 => 0x448a31103244983160290564a64152a8c8a62a
  | 3 => 0xa9135a2490e90cdaaa8289b13ab41c0d70cb4c
  | 4 => 0xcc2c64492481d164d34f2041cd298031ad0db0
  | 5 => 0xe307871c70e1e7f1c73ce780e3118c1fef000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaa0a0faa0a0a0faaaa0a0faa0a0a0faaaa0a0faa0a0a0faaaa0a0faa0a0a0faaaa0a0faa0a0a0faaaa0a0faa0a0a0faaaa0a0faa0a0a0faaaa0a0faa0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40291
namespace PEqualNP.Outside.L_meta_40291
open PEqualNP.Outside.L_meta_40291.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x120080118002646844091402800c00c0fd31fd40ff41fe31fc32fd32fe21fd21dc30fe41ff43fe32de30ff40fe40ff42fc31fc40fe10fc10fe43fc42ff32ff20fe20ff21fd42fd20fc20fc43ff30fd43ff10fc21fe42fd41fe30fd30fd10fc30ff31fc41
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xa061cb81000001e0204000000108400041801e16081080198006906801c2ee8a2a05ed4143b6292217751482daa40857d4d40aea9e81da500c2e8a2905e14131ec1862179508ca7ea898d794230b629281d830882e8a2a1d7940309eaa6433f54442daa4205b94a30bc282873e54c8678a8905754c41b6a94615d53c42eaa3215b54a41bd284656f52442d8a498dbd4943bb28c856e52d06bca7885bd4931b6a9683d83048278a88876d0030b7290215f53442baa7905794c41ec200613c544c6d8a4a1f60c010b7a92815e53d02b8a6a04fd5120b729081cd528c36a8220d714d10b7294835c53482f6a098f394a30afa9a415e53c82eea2a1ddd4540
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x1008000961815310750510c120d25483004318540c120b258a500c2c96210030
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 42
  | 4 => 66
  | 3 => 6
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
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/21+packedAt s2K5 (672+(h % 21)*6) 6) % 42)
  | 4 => 2*((h/36+packedAt s2K4 (1782+(h % 36)*7) 7) % 66)
  | 3 => 2*((h/9+packedAt s2K3 (228+(h % 9)*3) 3) % 6)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffff01ffffffff03fffffc03fffffe3fc7ff
  | 1 => 0x3fc07ffffff80ffffc0fc0ffffffc07fc8ffc7
  | 3 => 0xc0007ffe03fff01ffff000fffc0fff81f0f8f8
  | 4 => 0xffff800003ffffffffffff00000fffffff00ff
  | 5 => 0xfffffffffc00001ffffffffffff00001ffff00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x5143014c2889224500b2c92c9152d28a13c35b
  | 1 => 0x5952a145110e48b2c05505536654a6cc85dc5
  | 3 => 0xb52a4c289aa241d75550289ab949bb2970e8e8
  | 4 => 0x260c68b16344891a9a69b203220e2c71ed00b6
  | 5 => 0x383070c183870e1ce38e3ce3c3803041beb600
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaacc88aa880000eeaacc88aa880000eeaacc88aa880000eeaacc88aa880000eeaacc88aa880000eeaacc88aa880000eeaacc88aa880000eeaacc88aa880000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40291
namespace PEqualNP.Outside.L_meta_40291
open PEqualNP.Outside.L_meta_40291.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40618a0000876d408000701c4820c7143ff43fd30fc42bf42fc30de30fd20fd41fe32fd43bc40ff42fc41fc32fc20ff41fe20ff21fc40bd42fe30ff10fe40ff40fd10fc43be40fe21fe41fc21fd31fd21dd32df32fc10fd40fe43dc30ff30fe42fc31fd32ff20fd42ff31fe10fe31ff32
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x61bd32102faa810ef90e40ef2a6657c548837c87a16f50e40dea1461be4350f7ca32077cc941be2a221dc528c3f660987e48210df99481bf420837e85205f94e10bf29e837e531037a84195f94c31ef29843dc53507ba64a0ef50d42de21081f6210877a84985f14940bea9c41df518c378a2a177d4d40afa9a41bf544c6fca4205fd4930dea90817e51902f8a7907708430df2a621dd53c83f641105754c42aea9461df4390ef8a2a1ef90020be2a6437c548c2fea890efd4142ae28265de324cb7e85996fd0930ee996417e5310efea918efd0921de206617c53442f8a2996f50f42eea9883dd32c42fca020778c630eea1a63be4250afaa510f754f10bfa9a83bd21903ba85185f15131ef99463bd42ccbba6518f754c20bea88817d54482faa3a1ef0ca40bf28441bd54c867aa818df94c20dfa9e85bc40043bc84187b88420ef29c85de43cc7bca0184f94240fb98a63de410c37ea8985f55320be2a6413e54c87ba63185f14d41ee2a0617f544c37c80986f14c40cea1061ee4210b7ea4205f94c42eea9843df528c2f8a4a0f7943329faa441df320c37a8410d794f21f710a43dc408c2fea9885f55332bea98837d520c3ba642077d4332bfa9c43be54c837aa3a17754732bea88657d5490fba6420f7cc840efa1a87fa50086fca118ef10110bea9e417e528cbf440105f55331fb08221f721042fea0a15f54241bea9c61de504cbbca7905fd4143ef298417d51c837a652077cca32be2a4657c5150afca9197714d40af298437c53087bea818778c320faa88417c52442f8a8996fd0a30dea12657c544c33c801867d08309eaa465dd518c27aa810ef10210be2a4637e52906f8a9885794230bea8e61de30483be60185bd4910eea1e63dd548c2faa3a177ccb20bf280657d538427aa8105f55110dfa0c837e53106f8a29877cc931bea9621bf42086fca598f750c43dea9a85dc418c37c85205f94d21bf28485dd324c7b86318778c310de2a2615e50ccbba65a0f754532df20461f521c42faa710f7cc841ef996217f5150e7ca81977d5332f7908433f54482fca99877cc831afa9c417f528437a8520df94f20ee18021ef524437a85987d88510bea9e21de53c43be8718774c831bf28483bd540877e84996f10e41ef99241dd53d03be86995fd4b10de290817e5110efca42173d4932bf296617f54cc2fca310cf55242bfaa6415d53087be83185794e42f610c41dd5310afca3996fd0b30efa1e657e500c37a84085f14810ee996637f544c7be6520f74c920be2a421df32d07ee43085f54d20de2a2413c544437aa7a15f94c32ef28861dc30442faa7195f95030fda04817f53c437aa5205f95210ef18041bc539037e42205f95310ee21c617d5010ebaa790df94f10f7190657e50107ee4310efd0a41ef29461bd40103bca790dfd4d10
  | 1 => 0xe52d02fca3214fd5110ef190617e53d03ec438857d4d10beaa483be5350a7ca1a17b08420dea10817c54cca7ca818d794f10df18c81de304435ea4a177d08309e2a241bf4290bea8220df54b30fa90a21de520c2baa7216f50921dea1a83dc428c3bea6885f14e10df988813d521037e84196f94142dea1465de518c2fea8105fd4520ee988617f5150afca9995fd4c20be282437c53c42fca3a05f94c21ee18641ed210877ea8886fd0441dfa98817e5190efca421df54c42bfaa443df32886faa918efd08429f2a041dc514cbb882186f50b21efa1c63bd21103ee4290f70c310ee18861bf420c37c86206f90030bea9083bd42c837ca0205f94a31bea8465dc424cbbea4186f50831bf28863de400c3b885996f50a21dfa1c877c50506faa910f710e31dfaa2417d518c37a849077d0c30bf28461bd51102faa8086f50b10ef10c61dc304837c65207750630be29a855f535037aa2a16f10020bea9683fb405037e85886fd0f41dfa1465bf52903b88618fd08410efa08613d54c437e63205f94d20f699065df218c2fca4185f94332bea8463dd420c2faa5087714132bf28643de308437aa8106f94e40dfa16417c534867aa99877cca10ef98c637f514cafea7085f54732bf28481bc408c2bea6a0dfd4e20dea18877e5390afea7906fd0d42be2a0637f548837a86206f94440dea16837d53086faa9195f55031dea1663dd328437c8620ef0c840fba0a837f5250efaa718df94820de21e857e520cb7c81905f54031de20261bf42107ec6218df54843dfa1887ee20482fca72077cc430de20c81bc31902e8a2907710c30bf290217651083d8a4887ec4110df20621df32c86fca8196f55320de2a263fb108437c80904f55321fba8a417d51082faa790ef95232dfa16837e54c877c82a0f754a30efa18637e518c7ba81185f95120bfa8283be5210378a910774cb21beaa2437f54ccbbc61105f94743de21a85bf43d0bbc86185f94641ef99281ef2088378a52077d5132bfa9283bf42482faa90877cca20bf28085bf43902fca2085f54b40bf28443dd32503f240886fd4942bea9221bf4190378a3a15f54343bea9a217e52443bc65186f90d42beaa0416c52443b860105f94730beaa441dd32882baa7a05f54221df208817d528833880185f54032ef98863f9401037a85205f14e20f799265f7318c6b8a6a05f14143efa0461fb308c37c84205f95043efaa4617d548c2b8a6906f54142de108817e53442fea8907748430fa10c217d530837a84106f50f41eea9061dc54ccafca820efd0b31bf29c87bf32102fca7106f10e40dfa8881dc51ccafaa321fd4c431bea8c65de434c7ba60185fd4c21ef996817d5090bb8a9187d44010ee19061dd320c2fca2207795030ef21887be540cafaa9217750c30ef29883df53506fca518774cb40ed28
  | 2 => 0xcafea6a05f54642dea08813c5050b7ea2a14f15130bf280437f504c6fca121df94a40dea14217e52d0efca3104f15131bea86657e540c7bc60987750e30bf2a0857e53d0bb86518774c921ef28a65dd54ccbf420086f10a40bea8c21dc50ccafca021df14131ef9086175510837ca998774c832f799465ed20082f4a010f715132bfa9a855e53082fea8887e90040eeaa061de544cafaa3105f95020eea1e65df324c2fca1a1770c220f7a1285f451483ba80186f55232beaa0657c54483ba86996f95020cea1887dd324c2faa898dfd5331df21c83bc5350b7c81087dc4010ef10861bd42106faa020df94630bf2a265bf42102fca5a0ef50441df19081bc53d0b7a84a06fd0a10beaa621dd510c3b8a2185f94331df2a043dc520c37e8510cf95042dfa8685df51ccb7c62207dd0641de28c817d544c27ca9986f50941efa9c41f9300c37aa8195fd5021ef21461bd42882faa521df54a31de10c817d52102fca1195f94720dfa18817f53c877aa3205f15021ae29a217950086fea4086fd4742bf28021bf42c86fca3195f54f40dfa1263bd424c6fca710ef100309faa263df400c2f8a5085f14d40bea8683df524caf8a8107750430ef28e657f54043b843187790932ef990435d53106baa4185f14931af29885f521086baa7905fd5232efa8a65de42ccafaa6206fc86409f2a6219d428c2faa4085f54b31ef29e817d51902faa010df95121df2a063bf42502fea2a07714d20ef99461dc534437c43206750b32dea1681dd32086f8a4985f15331df20281dd328c2faa9984f54a40be2a243bf42882f8a9987754e42efa8861be40882f8a2a05f54442dfa8c815e5310778a0a17e88110dfa1463f920083baa0995f14d20dfa08817e52087dc431077d4d20be296217f544cb3e85997bc8621ef20c61f6411077882206fd0b40bf290637d540c3bca6215f94020bfaa643dc53882fca898ef10c41bea94617d549037a62207e8c030de18881de548c37881905f54b43bf288437f53483be64885f95231bf298219f428c3be61185f95110beaa643bc40c437e81205fd5210bea9063de310c37ea7207d94420cf204617c504cbee21085fd4940bf2a6637d510c2f8a6085f54740ee992213e540877ca2a15f15221aea9e219f32902fca2216f55031efa82657f514c33e84994f95320af28061df32cc3b8a3185794f20ee994833c548837ca6206fd0831ce99481bf42506fca5886f50a31eeaa265dd32cc2fea498f78c010bf29487be53d0b7a83205f94343ee988637e500c6fea9187710030be29e437c54042fca790f74ca21eea8665bc404837aa9985f14e21bf288657e54103bc6298f7cc810af29865bd420c3f441085f14c20de98c81ed4210afaa720cf55032bea84877d53487ba64086e94040ae29a83bc43102baa7195f14142f7a14857
  | 3 => 0x9c010000c0005a01211832000180080401004081640800d66006008020c0460a0180e80019013a30001e038080040001e0781e0087e0000000216070540000006e8205993260000082e020b6039a8670001380a158064b0260000030802098340a2d40080050ad00006a5b0023c00a0606c0080409826000005600207000008660104226002050440b0000000c5a01a148000022201838191560111801014000040c83e0000a0b810c28ca00002010800b05c768be0481c088003700255000150460182a008000002eca0c0003c00d800080f80100c0100205007558011b002008588182a000323301e01022d10040500600152288220a832020282591800806000041f8061c804270ee0001c0000000154006b84c854248006c8720a81c1e026020005e9b20009802850075b8328349d83c0383f4b1346f007648080a8eaa50084b82a0101434806070520d000a50000000e0380a0900004012060000080800844004d848054030000c86c03804010286d05400802010a61c830000be5d8000182c2f1520e804018ac2000c00994079b20b86a0200835990200401a00016808030c40b80200018438000001e0101a38efd4d42af29e81be41902eea2905f14520eea16657d50cc6faa6084f55320dea1221be40cc3be63185f95130bf28683dd424cb78a8887710830dea9c81dc434cafaa190f7d0a30bea9c857e54043b887995fd5030ef996637e53906faa5205f55132bf2a6417e548c3ba64106fd0810deaa6217f504cb7c42207790d32de20441f9100437ca5205f54f42ef990657e548877ea9106f90010bea9c813e501037aa1a15f94742bf28883de438c378a1a15f94c30be2a065be54c86fca810dfd4d21bf284217e52106faa7a0d714e20fca80437e510837a84217790f32ce20461de408c3be652077d0b32bfa98217f540c7be6490df54443dfa00817f540cbbe84995f54a41f7900417d5010abaa6105f14943df20221bf42442fea488770c2109faa261bc511037ca3a177cc820cf990817c540c2fca2187754f21bf294219d32103f640905fd4121df286857e54883ba65205f54342bf29485dd218c33a84996f54c40dfa1a833e548
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x524423e64d4f21c715332482db6055132a798e429029e64144309758c54c831f4294030c794e40c831c54d4d2097d8d51d0a5e63151218f191524429e6310840c7151328831e5454f20d5d46304831c54d4d1097d8d50087374294420c754f42c869d64148308f997219031e5390020c7553320829e60d0932ab588531029c6350441d5546300832f52901109798e52906d5611533297594420c34c52cc910d9146204831c540c110a758c421025f6550c438f992510423e6015131c714f428829e6310a40a798f519029e64946308f992528c31d54ccb10cd144404823f6454d21cb549420c25e63d4141c795253c871e5350b10c7d4e539029d6314542d354a420c25d6394841a798c5150b3454d4520d6983538831d53d0841ce951500863e65d0910d54c8514831c6355031a758c429025e6394a10ae983428831e5454f108f592524423e64d41329d984530831c544c931971815310a3f6590020d3d8f52443345190120b6980540c38d424c821e3d8942cca3d6414c10b6980548c23e655091097596420c3645288510cb14b42442f160084108f19150cc65c6014d1097d8d544825d6510c31ad58750d0a9d6490932d9584524423d65900208f994321033a5494021c755332c869d64d41329799430482b66114a40a7593308c23f6454e218f99053c871c5414d108f592528c23f6550832c7549428c35a6014e20cb949420425d650c0209b189534425d6594c218fd91508c63d6414b10e6cca50102ba6014a40dc580514829d6210230c7d51328831f42943328fd91500ca5e63d41219d984540c3555354420c7150534825d639491097195410c36452841108f590530831d53d08208f99053087a54248421a798e521025d63d5210a7181428c23c65d0931ce191500863e6414e21c754d42c825f6550630c7d53534431d54cc832c7953320863e6414c108f993530825e63d4b10c755230c83375414520a7590310c31e5494f1097997324c3555114732ae18142c42b56114f4297994534425f6254f109798f54c829e63d4342c7d954310f1d52cca409ed95401025e63948409b98a544425e65084308f59421903994294030ae983511031e544cb108f992544429d6408630c750d5110e5f6254f40c7d4d425065c63542418f59252cc25e6314c219dd95310c6d66114a308f59053c86da60cc920c794d42c865e6394b10a7d91514ca5c63540418f982540865d6590c30b358a300823e64150318f990528432d52d084197597210c23f6454321a7993504cbd03044010d318f524425e6590830a718d411025f654c821a758c211031d5415332c795332c831f540c110c3549321023d6414d21ae980539023c64543329718d511029c604c840a7990328c25e658c110b5185504ca5d6394640c714d435072d52d0b41a758c51d0a5d6214d41
  | 1 => 0xcb1d5390c41c7942400c25d654cb409798e544831f5495230c714f435074f524c930c750d5210f395494021c7151324825e6314c20ce982501023c6055032c7d53324c2ae6214440d5144304823f654c440c755253c435453d45208f992520c29e64cc2308f58a54c423e65d0920c714f424829e60cca40b6983518c23d658ca40ae181321031c53905419798c54c825d65c86308f992520829d648c830a7992520c32c52101109718d544871c5450d319b988540c3655188420cb54b42d023d650c440b3988510c31d544cb108f191510c23f6454331c7d52304834c524c910c7553320865e65cc9419718153c869c6050c43c7d4d424431d5410c318f596540ca5d631522197d8d548823e6494821c794d420863d6414931a7592420c25e6590932c7550434cb4c53d49108f59654082cd6215332cb14a40442bb6048440a75924310e3c6454021a718142cca3e6510130c7953320ca9f6354142b3d89544cb8e524c840b6181328829d63144409d597210429e60d08309798e520823d6494831c754c400823f65504419b98a534425d6394a109b98854cc63c605502197597430c65d65cc8219e580530874e524cb41ad584521037151480208f994329025f654c832c755132c87645248510c754e400823d6494a10c794d42d029d64d4630ce983548825c65cc940c755253c872f54d49108f588544c63e60950329ed81544ca3e64d412197d8d50906ad62902209b994524423e65509318f99252c42ae6214c409758c520431d54ccb209758f5050a5c6550d328f99421902766194d209798c540ca5c63547429798f54842cd6295132c7951320863c64543218f99353c8398400c020b6980518c39932940408f590528431e53d08418f994311029e6314742a6181420c2d860508309b588540c23f6510020c794c40c831d524ca40b6983540c2d661d52308f597211031c535091097d8d5010b355110440f8886204425e63d5032a7191310c31e540c3109b588540425d65ccb10c7153324c31f540c2209d59421042b66114f42c795332082d96090430e3549420c23f64547328f592520ca5e6394620ab58853d0a3d62d51309dd85534831e54cca32a7590510c31c548c531b6980218c29d6314a408f99053c42d66114830d3d49324c71d544c8329758b534438f52509329b988530431d5314c40c795132c863f62550319d98754082b76154d42ae1815150ab86050920a759051cca5c6355120a7990310c31d5350b10c795132c831e5310020cd95151082d76154132a7d954310e9d6414a308f992544c63d65d0832a798e51902d66115332a7d894310f1d544c820d5cca510832f521011097d9532082ad62144408f593530863e6494620b5984540c23e658ca40d3549320423e64d4f10d3d49324423e60950319d185544823f6454031da58
  | 2 => 0x540c310cb150524425f65cc8419718d540427a6014c21c794d420832f52509109798c528434f53149109758c524431c5450c30c714f425023e6494832bc580218435b32540218f993530871e5350842da14a204425e6315021ced09500863c60553218f594319031e5454c2197997434ca5e6394b40e3d89420c2d56114a30c7d4f425025d63951308f191534863d6414910dc88550086d8604c810c3549420c23d659084097594210c2d461551329759532c43355114440c7551320863e64951309bd95320ca3e64150209d185534829c6354142b6983328829e63909429758e520865c6355220a7181424ca5d6314940d314c52442ba6014840a7993518c3354214520a7590318c2db6048430c7951320cad86055132c7553430c67a60d5021cbd49425025d6314b108f590524c39a60100309798c52442766115332c794f420cadb60545329e580540863d6414e21cb54942cc63f655084297980534429e6408430a758f5050b4d52484308f58b544c63e65d093097596320c31e5350e4097d9532c427661148109798e524429e6310440c795030c82756195120c754f411071f548c110cdd09510826f6548020c754c43106b46154142a758f40103986050830a798c521031f544c9309798c54c863e64d41319b189544423e64149108fd91518823e6495120c7952530871d544cb208f58a54cc35753d45209718d50d07573254420a758a400c35732d4520c795332cc32f64d4910ad587539023c6454e21a798c419023d64148108f197424c2d8604cb40c754b420c31f5414d20c754d411063d6295031a758e421031f53d0a209b988540423d6550b1097d95300c23d65d082097d95410c25c654c940b9185200823d6494410c755153c433742d4520a7992324ca3e6494d10a758e429029d640c830c754c43d0acd621503097d8d524423e6494b30a7993210c29c6454532c755153c825d6394b419b98a5244335511474297195434c69c64544309758e520431c5490d31c7550300831e544c820d3549420c25d6315310d618d500869f644c630cb9514210a9d6494630cd945419023d6494821ae980519025d654c8418f595420c75532944208f982548ca5c6354042c7151324c29d63d0240a7d8d511025d658c0208f59742c42ba60d4e4097d8d50d07365110020d3588538825c63549109798f5050b4e524c840cbd50524423f6255310cb549211031d52cc840e6181321031e5010030c754d420863c6454d109758c540429d63c8440d3d48304434f53d49108f59542cc32c54d4910a758c411025d63d50208f1974244356514c630c714d425063d62d5110cd94640082756115020cb588548838f6250932c7150308825f63544408f996404823c6454031a719151ccb1d54ccb308f592520431c53102209d58454cca9f6354342c7508504
  | 3 => 0x332f808620842d761551329758c5284398400c210a7590210c31c5390140ae980211038d424c920c7d4e405031d5494c21cb19352442b661d4e40a7181420c35932940218f191508c65e65cc9409bd95210873751946408f59353c431c5350a208f195424429e640c830c754c5350b555114430cd544400831f54cc93197d9732d025e63946409798e520425d6394a41c794f42c431f54d4d208fd97420c67561d5020a7191300c25c63540218f99352c431f5310120a758c521023e6494b31cb1494244298604c840abd895350b37519012097d8d51882cd620c22097995325039b604c840a7592520c34d52cc830a798c321027561150309dd85544829e6494a30a798f5050a3d64d4f218f19151ccb1d540c3208f592530c38e52508309758b535063e6494a10cb54b21102d8604cb108f195424831f548c220c795230c431f5390120c7d4c408825d6315020a7d91300c31e5450e308f992520425d639521097996304831f5390220c750a50ccb1f3294040d354b320c69e60d0a3097d9532d02ba60d4c4097d9732c425d6510630c795253c833751101208fd91508869d63d4342a799350cca3e65c8440d54c9510831d5350841a759350ccb1d5350820979825308798400c110ad98750d0a776544010c754b428c335519002097d95321075532d4520a7992320c2da60904308f596431063e64149318f594321023c6055232ae983521031d5494c209e583530863e658c8409798c54886b86050a2097996428c23d64d4131a7d9150ccb1f5414e2097997210c25d63151219ed95100427661d4c20a7592528c25e63d5321c714d4350b1d53d0b20c7950300829d6414532b6181321025e6094c41d5d46518c23d65100208f195424c65e6394d2097994410c23d6595021a7990528c35551145329bd89544427561d5230e6d0a500c31d5410f3297d8d50c86746155132c7152304431e54ccb21a7d91504ca9c6354542c7549321026d629511097197325071f54cc920e3d4b424cab56114c40b6980520c2ad6210220ced0a500863d64d4f208f990520425f63550109758b535033754d452097d8d544429c644c4319ed8153486ce6215030c715143cc71f53d0941c7d4f4248356510c020c754f42d031e53d0b219ed95300c23d65950319798f54c431f5410e318fd91538823d64948308f98254c865e6315020cb949420c23e6414f209ed95200825e6510a308f59251882cd62d53329798e548829e640c6308f191538831c540c1209718d50c863f65500409798c540c71d544cb30a7593210c23e651513097596530823d6494820c794d42c823e6414930c754f4290b1c539022097994420c23d6215110a7592324cb1c5310120aed815350ab56114a40c714e404832d52508109758f50486ad62900208f589540834c520c11097d94300831d
  | 4 => 0x755253c823e6515120d6982500c2786054d21ae980219023e65d0940c794c40c439b60508309798c520429e6408630a799051ccb8f624c8408f994319031f53d0910c758c544c74e534c832c750e5010e5d6395110ae181211025e6394821a758a408c3355494420ad1855350aad6210020ae1815350a5e65cc9108f59253842756114c20d3949320425e65086308f992528c69f6454430ad185425069e63144408f195311029d638c840c7553310c71c54cc910b358a308831d54150308fd89540823c6454032d618e500871e53d0821a7983321031e5454f219758f540869e64108308f593538429e64c8630d358b53882b9608c440d5146304831d5210230971815390b1e54cc83197994304425d6294f108f588544c355510c0209798f540825c6054c219758e548825f6550030a7993300c25e6394a40c74ca5010357510c120c7552300823f65d0b108fd95420c71e548c320ab58b53d0a3f6550b109758c54c872e5250b3197197324425d6510c3097588534431d5310320a7990424ca3d64d4c20c754e40c831d5290230b9189100438d424ca218f596321031e53508419dd85544cb5b32940219e98052043c532484219d987548c23e65101108f59252c425d6510a309e195204427661150208f59053c823d65d08218f59742cc27765484219e983530863d650ca4097996434c79a5010030b6181324829c6150c4397d95310c79a5090030b5587320c66f6254d10d594e510834f528c1108fd95420825e6394b41a7d8d411023d65d08318f99052c4355510c430b6181514cb1d5454c21a798f211023e65084409e583540863d64d4121cd150514831d5410c30b5185324c63f64544309758f54c42ba60d0920cb549321029d6390942c714f424429d648ca30c7d5132482ad6294d42b6980510c25c6354221aed81321031c548c220b5584540c25e6395210ced91500871d54cc83197994534825c654c920a7d8d419025f6355121c754d42d02e96008620a7588400c29e63c8640c794f42d02b86050b30dc546200825d6394b408f590514ca3f6454910a7990514ca5e65106309798c54c429d64cc03097d89530831d53d0b10a7191318c23e64946308f997435065e6094f2197983535067b605512197d8d5090b354294420a7d8d401023d6494d108f996404c371215402197594218c2746548510c754a400c31d42940309798c52c425f658c020c7150538825d65d0030a798e529025d6294f4097597321065c654c941a718d401031f54cc910cbd49425063f654c6408f992530c23f65d0b30c7548400c25e6094c429dd8552442b96008440c7551530825d63d41419758f54c82b96008640b6d81420c23f6454d20a718d50d0a9d63948408f191518823d6414f10d64c950086b66114840a798c529031c5450f32c795132cc2d561d4
  | 5 => 0x51ccb5653544208f997424c63f6454c10c7153328831d54cca32c794f4210a9e6010030c7151324434d524ca31b3588510c29e63084408f593504ca5d63946209b58854cc69e648ca30d5d4c514823e6494e10d3549328c2ba60d4640c7d5053442b86050830d6d8d500875732145209758e529031f5390110a718d51d0ada60d52308f990540867965840108f592528c65d6394410a758f519025d6315021c7d4d42482d661d4332c794f4290b1e544c831ce19250087365494420a798c219023f6454d10c7952300832d5250a41cdd0851483395454021a7d8d5150b1c548c130ae980531025d65ccb40cb58b548829d63106409718d50d0a3e6515131e3d89329023c64542219798c525031e5350832a718d511023d65c86409718d5090a9e639084097594410c23e65901108f994544433a6015220cb54a321023c6454c10aed815150a5d63145429e181544865c6355221c7549420c33542544208fd91500869d63946409b58a534423d6494e20e3549321034d6314910c7d4d428829c6454332ae9823110356518c0209d586534825f6354342c714c404433542d45208f992520c74d52ccb30a7d8d51d0a3e6494e20979825390a5d6294c4197195324431e54ccb10c754f420866f65508428fd95420871f544c931d6d8e500863d6494630c7152304829d640ca30c7d50304825e63145428f181540c71c5450d32cb590524425c65506308f195319031c5390110b5584520c2d960086309798e510423f6550c439758e544829d63c8640ae980511023e6494910d654d500865d63948408f180544423e6494d208f990530825e65cc920c7d50438c23e6414532a798f401034c528c110e6980408c31d5390310c754c40c42f06148210c795153082b860508108f590530863e65101209b588530423e6550930a758e52902776550441d654e500874e631491097589530831d548c310c7153324c78d424cb20b6983528c23f64542329798c540423f6255330e3d89428c276658851097596428c25f6354221c7d5332882cd620c02097d8d548863e6015110a798f4090276619512097d8d544c2da60d4430cb990524431f54d4e209e98054087b04044010a798342cca5d63d4b108fd9542cc35553944209798f540865d6394820c754c53d0b355114542c7952530823d6494d208f191534823e64150329e583548c6d96008430d694d500865d6214d40b6980528c31f544c910c754d4210ab761541429d587530829c6454132a7593218c23f645433297995325071c53d0941ad587421065d65cc8209798c525065e654c910c7d08504cb4d52c843097d89531065d6394b10c755153c875a5394021e610030c823c655093097d8d544c6da600843097994424cada60d4830c754d42c872d52d0840c714d424831e5390310d514c514834d524cb41c
  | 6 => 0x9c040060de1580881f0160700000e002008000220421f89fc20004004028580060000100302006c0288a1b602c000d9000008000222720980280e15a0000600f26a0780000700a0001800201205c0080e3881ac0001405e00001033008ae0199fc00098c88019002008188000220450780007c330ea00002c0108a00403c0000080095401c0080c000a84000010003b47c81b00e00400801006054040020d600c350000001f0048000040000981400600c018710cc000000070261b4038340020601380082a04401053000000018070060013f98700e0bc0e00f000d242180401b08c00014014000060010c60004880600e01004b8501c0241d0010000a00804100c0180b8040080040000215e0340502f008018080800260080a83d06065c3600601631c0600552607c0f8dc00c0245302100000c058001800c424000010014020060820003980200a0180b001024004d60000120280003a18e0b0010b00b2424009250de06c048210000003a80732a1300989500e3780180002a0a0000e50000784600526c035cf811022180030020040c0000430480000b80a0201900884702c00df48040042f1df80202a024000000006680780000a068280520000000c0200000202a80301c0517700008e00c0303101600c1304564a040069200520c800b9ca020e81201100000c0280000a058000000001a400023028000cc8010003880080f07e0080001a00409440805036008010220002580985f0000085e0140160080000211200001019012000000000100640d0050460042c80401c0142581e5420480080410e01c038231c00341401c0000141e8113120080203503c0001e8040260dc000000140e0030090780340280a03217c0017d0000100281f01e018018000d81063e6414d219e181544cb2d5250a40ced92500865e639484197181531065f63540418f59352c425c6355110c7d52304c25d6314941a718d419023d6508440c7153538829e64148308f59252cc71d5415132ad984531034d52ccb319e983548c74f52cc910c714d425034d524c84097997218c33554544208f993538429c604ca40c754f4210b1f5350940a7d91310c29d6308640c794f42c831d544c8319798e534425c6354620ae98352902d86048430b5587548c31d544c4319798e544431d5310c408f983544c7394294021ce509500865d63d5321c7d4c404431e53d0820cbd4b424429e609003097980535063c6454232a7d91
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x20c041010034002004458511180812800112140dc0012ac28300740812614001281000b1c0420b341400ca28e8a88a299689421813248306aa2c418041895895110020c1aa4302841861952181321030a2a0c299263855516115332c2aa8b0e6418e18531814288306a9ac429881435c85450c30c12a4302642060f545883088226b90caa08610e1c16550831a2ce9a8ca31849a70d8d511030ab22a228861431d5424c92085ae432a62206155358453d0b0a298c2a1283459c75394e40e12a4302642050d7294d42d0286b94a6a162192548604c840e10a4200608862952181321030ab1aa228881455c45450f32d80c4182200855070544514cb12b12a228881621c1424c920c2ac8a88a39960c655093248384a1264a8043435ca544c831e12a5b02642051671d50438c28ab88a8a1861459c75495230930e0b26421850d7295132c42c4b908018041261c16494830c30a8302651051673d46519028a39aa228a85835516215030c2aa6b08a62061563544411028c382842826585192514c630c32ca200601070952d81420c28a38aa629a85261c163c8440c28c728a832060d52181321028c382a629a8585591510c430e428490aa010e18531814248384a90c0a1061261c16394840a30e0aa0a89968952181321028a38aa821a65c15093214520a30e0a1ca021d1870550434ca86b94a89966191589510c0208b0e0b2a6420e0d6354b2110286b90a8a1e63915895114430c1ea6b1081106156354451d0b06a9ac420041a2588400c020ac4eb10c408861553587421068d386a821c63865486050830a60e0a10a29051471550544cb06b12a4200618694c6050b10e22a2200601050f7250d5210e98382a228a85825486050830a1ae529a8420ea0621011004344a90c0a1061541c13214520c30a8302649041c76551310c745290c09908186950604cb10e826490aa010e8a52181420c28cba88018041925486050830934e1b22a21861554584540c306b22a5908618a5486050830
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x2402020001b00805093214520a088058d52c8440d01421c13214520a0982950604cb10c0975588400c020a088059152c8430a098294c6050b10d0172544400c020c09655c8400c020e0162544400c020
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
  | 7 => 2*((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/23+packedAt s3K6 (768+(h % 23)*6) 6) % 48)
  | 5 => 2*((h/346+packedAt s3K5 (27459+(h % 346)*10) 10) % 1017)
  | 4 => 2*((h/469+packedAt s3K4 (51110+(h % 469)*11) 11) % 1345)
  | 3 => 2*((h/51+packedAt s3K3 (5488+(h % 51)*7) 7) % 112)
  | 2 => 2*((h/10+packedAt s3K2 (600+(h % 10)*4) 4) % 10)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffff81ffff83f07ffff83ffc1ffc0fcf9f3f3
  | 1 => 0xf03fffe07fffc3f83f07fc3ffe1fff03467cfc
  | 2 => 0xffc1ffff83ffffffc007ffc3ffe1ffff878f1f
  | 4 => 0x1fffffc0003fffff80003fffe0003f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x218408c5109040014b098044c022425818b171
  | 1 => 0x64889143212205281542a429521496094254b4
  | 2 => 0x821122080a44225280844a82254128a2850a0a
  | 4 => 0xcb2dc4924876ab9ce6d06223b9980c33e80fc0
  | 5 => 0xc31871c738733e738e77330311030c3f7e000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8e8e8e0e0eaeae8e8e8e8e0e0eaeae8e8e8e8e0e0eaeae8e8e8e8e0e0eaeae8e8e8e8e0e0eaeae8e8e8e8e0e0eaeae8e8e8e8e0e0eaeae8e8e8e8e0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40291
namespace PEqualNP.Outside.L_meta_40291
open PEqualNP.Outside.L_meta_40291.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x3100000dd32bc41dc43df43df30dc31be41dd30de31df32bd42bf42
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x3aca8665345150a38a8985654031
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
  | 5 => 2*((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt s4K4 (192+(h % 11)*4) 4) % 12)
  | 3 => 2*((h/8+packedAt s4K3 (108+(h % 8)*2) 2) % 4)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x3fffe07ffc1ff07ff03c3fff07fe07ef07e73
  | 1 => 0xfc0ffff81ffe07f83ffffc1fff81ff813f9f9c
  | 2 => 0xfff07fffffffffffc003ffe0ffffffffc1e3ff
  | 3 => 0x7fffe00007fffffc0000fffe0001fe03e0
  | 5 => 0xffff8000000007ffffffffff00000001fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x48612231448aa3014b50c1353433212c702e31
  | 1 => 0x19220450c90829281515440654914b04169694
  | 2 => 0x208448821221045280822a408944945181414a
  | 3 => 0xb2cb712483adb79ce6d82314ee790619fa03e0
  | 5 => 0xc30c61c71c31c6e738e3b39808601861edf800
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xece8ece8e0e0e0e0ece8ece8e0e0e0e0ece8ece8e0e0e0e0ece8ece8e0e0e0e0ece8ece8e0e0e0e0ece8ece8e0e0e0e0ece8ece8e0e0e0e0ece8ece8e0e0e0e0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40291
namespace PEqualNP.Outside.L_meta_40291
open PEqualNP.Outside.L_meta_40291.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x11c30400020000053c10011127413c2047001001dc43fc30fe21ff43fc42df43fd40fe42ff10fe41fc32ff42fe30fd32fc41ff21fe31fc10fd31dd31fe32ff30ff31fd10ff41fd42fd20ff40fc31fe10fc21fd41fe40ff20fd21df31ff32fd30fc43fd43fc40fe43fe20fc20
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x78000141800e1ca802a002080412a8a021450000b0293002c019a61400416202233002c000016baa7885795043af29c85d55110ebaa710e710c409faa263d65110ebea6a05d54443bc2828575519027ca810cf553109f2a0417b5050b388620f54c710bb288879c43906baa6085d94640af298633f544c27aa9194f952329f2a6215e53042aaa221d754443cf2a087d5414c6bca898d754e41bca84833f54482eca2185714d41af2a6637a5090678a8905e54021bba8a859c544c6b8a898d754e31bd280435d53106b8a998f590531ea98e435d53086eaa2185714d42ba28a855d51d0faa62885794e40ae29a815d53082bea6905d145209e2a2615d53902eca2105794e43afa9a857651ccb3ea898d794f10af29c433c544c73886a15794c419eaa0415e53907aea298c715131bba8a41d531086eaa3995794c21afa9a835d5390aeaa2106710f42af298415c534833887204f55021
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x80e511c000040019640000e070294644c721a558443907144394640a558443902956110f4295195414c6956110c40b4582414c6556194e42c610e50907156115131871915304294644c421d44c550086956110d42c5551310861e6495131c510c5150a556114d40a519131c4315544c7108719153887145490531a519131443184314142
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x60a3b2a898e21441d13154021c20a8b048298d117110e509060a3b2a898843445c44314142
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 6 => 2*((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s5K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/44+packedAt s5K4 (2430+(h % 44)*7) 7) % 90)
  | 3 => 2*((h/22+packedAt s5K3 (950+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/9+packedAt s5K2 (294+(h % 9)*3) 3) % 6)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf03fffc0fff83f07c3fff87ff83fc0fc3e7e73
  | 1 => 0xffc0ffff03ffc3f803f07f8fffc3ff02319f9c
  | 2 => 0xffff07fffffffffffc007ff07fffffffc1e3ff
  | 3 => 0x7fffc0003ffffff80007ffc0003fe03e0
  | 4 => 0xfffff800000003ffffffffff80000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x948610462891510140b298129a264258162e31
  | 1 => 0xa192248a19251728215a2c8b2e62960a309694
  | 2 => 0x420841104240005284004120408928a0c1414a
  | 3 => 0x8b2cb62490759b9cea6b040a77320c337a03e0
  | 4 => 0xc30c438e38622e7338c764c040030c3adf800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfae8e0e0fae8e0e0fae8e0e0fae8e0e0fae8e0e0fae8e0e0fae8e0e0fae8e0e0fae8e0e0fae8e0e0fae8e0e0fae8e0e0fae8e0e0fae8e0e0fae8e0e0fae8e0e0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40291
namespace PEqualNP.Outside.L_meta_40291
open PEqualNP.Outside.L_meta_40291.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x403403850310010c00800000064417410000000803820c00200000000c2000002547009007f10007fc4301ff50c07fe5301ffcc005fc32007f950017d52007fd0003fe21027fd4807fd32007f55001fe2001ff4c003ff10017f94809fc5400ff14405fc52017f10809ff51017f8c807fe43007f54007ff5301ff14c01fe50007f50803fe51007fd0407ff43007f84007ff32027fd5001fd21017f08007ff31005fd4801fd5100ff08407fd31007f54809fc5001ff8c003fc1001ff0c001fd1001ff54c05fe42007f50405ff2100ff10403fe31007fd0803fc31007f50005ff2000ff90409ff50007f90001fd20
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a4000ff58554025fccba0873ff2190003fd8842037ff94f4204ff887a00037c6550405ff90e8401bf99341027faa728103fc3195009fc282a002bf9895402ff8c91000bfe52d080b7e314a000bfd854203ffca688016fc6290053fea1a4205ff04140167fe60a080bff2048059ff31a821cff94a4002ffc809000bff424800bbe282a021ff54f4004dfecaaa05ffc215000b7fb1ca004bfd8150027fea6a8827fe63d007dff192a801ff8c61014dfac690816fe6090003ff98c2024ff9095001dfcc690017fe309000dff2922005ff5921006ffcc290003ff6454401fe9022000ff5434019ff820a10037d5210005fe2168439df9055202dfec910003f920840057e312a004ff15152017f842a1027fc61d00017fb2a4205ff58e2000dfec8a0807fe21d0413de2a4a804bf9951013ffc6528047fe538800bff1822001ff5061004ff8c5a0817fe505405f7eb1e8205bf1815405ffa8708003fd219000bfe32c2000ff99110177f865a0867ff5350075bf21aa415ff54c401bf7c87a1013fd5395013fda028000ffd952004ffac3a1027fe61d083bdf21c8000df19152005fec0aa00bff2188013fe3168009ff10a40026f8a728003fd60550017fb2a8420ff8cb40017fca4a9097fe6354005fe9928434ffd4d421d6fa60a9013ff505506fff9868405ffcc24002ffc409000bfe5288009bfb26a401bf1852001dbcc720017fe4084003f610a4205fe142500fff8a3a001ffe63440137e32e8206ff109101d6fec6a900b7f20d48017fb224202ffd092102ffc611000bff2048401bf2a2a402fe0812004ffec1a10affc525040fff9822000ff58954027fea4a80bbfc52d0401ffa142005ff84110007fec0908affc2050409ffa8aa800ffd894000ffa4288037fe514800b7fb1c203abfd8d5204ff280200cbfe6354409feaa4a000dfd4940027f8a32a00b7f32d4805bfa928409bfd8e541e6fe87a9067fd6350005ff10a4027ff90a5019ff8c2a1027fd54d0009ffa92a841ff8ca54025f8ca90027fe42d0075ff182a402df0855200fec428808ffe41540017fb122005ff18e20025fccb100137f5354805fe1924005ffc8210027fea0a80e77c1054829ff1908009ffd8e54017f88510016fe6084013feb168204ffd465017ff861a0817fd501000bff9844004ff951501d7fe86a9012fe658407dff312a802bfd8952117fea3a008ffc4154049fe312a009ff58a541d7fac6a9003fc6448003ff18a8202ff8c9521e6fa63a904ffc5110013feb0ca801bf98440015f8c52a00afe628400bff30ca002ff4862000ffca290802df6355003ff98a8205ff9434002ffac620097fd32540017fb22a225ff90d50025fcca90803fd6154813ffa0a8005ff18a5002ffec710013fc545440bfe30ca000b7d8d4102ff8412000bfc20d0801feb02a442bf58e54
  | 1 => 0x7fe4154803ff8828205ff14040007faa3a0017fd208400bfb0822009ffd504004ffea92a0eb7d5354815ff2942000df181520077aa8a0813fd5454035ffa8a8000ff5894100ffe82a08d7ff5150843ff9968009ffd01401f7f8c4aa00bfe42508017eb2a8205ff8c210027f8a0aa016ff65540017fb0aa802ff10921027faa6a80a3ff43940057f3148000b758e40005fec2a0006fc61d007ffeb1aa809ff18e54147fe6528003fe6054475fe982a421ff14f40027f8a72808ffc31540057f312a000ffd0620025facb28003fd6550803ff98e8202bfd9142026f8a2a9017fd629000bfe1024001ff5052104ffe87a00a7ff30484097e32a8423ff9855004ff8a920007fd218400b7e302a209ff1534200ffe4288016fc60504077e31a4209ff50b40007fa852806bff525000bfe284a000ffd89411d6fcc6a9007ff3148409ffa82a20aff10a10007faa22000afc62d0013fea1e820bbf58e10016fc64a9007be4150451fe98ca03affd8d52027fca8a8803ff6550011fe2a22000df5495002ffe6108003ff6254005be196a43ff718d5404ffccba100efe63d0003fe20aa202bf9891000dfcc328002fd6295005df2168401bfd8551005faca20017fe638404bfeb1aa03dff0c55410ffa63a0017ff65900657eb1aa215bf58c4004ffe872a002fd6195057fe3128200bf59110027faa6aa027fe545084bfe21aa032ff90d5104f7e85a01037e5195013fe2188039ff041520077ec8900cbfd30544077f31aa409ff95140017f842a9007f8104400bfea008004ffd4d52027f8a72a00afe62d0009be326a415ffcc8400d7fea0a0027fc415002bfe2988003bf18f42026fcc3a9037fe314804dfe18ca017ff90540077fe62900037d5454825fe2a44004ffd4550025facb2a012fe655083ffe18e8019ff90d4002ff8c908027ff4190005bf212a407ffd8d10167fca6a0816fc6588033fe9828005ff5925004dfcc908027fd4210013fe21ca800ff98142027f8a12a073be42900017eb2a8435ffd4142007fa8290002bc644800bff31ca005bfd961004ffec3a1027fc4150801beb22a433ff90542017f840908affe5250409bfa8aa402ff4c952167fc60a0827fc435501dfea1a4042ff4c654006faa528027fc60d0813f7a128400ff5891009ff86220007ff4144049ff312a034ff90d4202ffcc5280f37c30d480f7eb1a2005ffc4240006faa5a0067fd3250003fe10aa201df1455102ffcc4200dbff10d08137f3208009ff109411cef882a903bfc634800bfe1042000ef9514104ffac12a003ff655087bff30aa805efd0240127fc64a8026fc6444003ff28e8201ff041510077a822000bec5254803ff18a4205bf1884000f7882a0802fd6194051fe21ca004ff1455004df8c8a9003ff615503bff29c8005bf18e5000ffe20880a7fe63484097f3
  | 2 => 0x40157f8a8908cffc3150801ff2a44020ff14b400cdfec6a0017ff6488075bfa1aa4009fd95411fdfec6aa0cbfc435440bfeb14a001ef10741007f8c8a8013fd525407bfe30aa809ff9834102df8c7080137e63d480bfe9844000df54940167fea6a084ffe51100337eb24803cdfcc752016fe64a9002fd6588001efb1a822cff4c9410077e84a0013fc5294013ff304a811ff90e20067f8a908013fc51548037e30a802cbfd8d41027faa6a88a6ff6348413ffb068239df9855206ffe209000afd62d0813ffb2e8004ffd5150077fca690016fe609400bfe0848009ef9534102fde411000afc6255013fe21a8013ff8844002ffe2110016fc6048455ffaa2423aff98d52026f8a0a9103fe219504bfe98aa004bf195400dff84320003fd64544077e31a8014ff0c84001dfcc6a8107fc3295073fe20aa419ff54d4004ff885a0896ff6354013ffb2e8405ff0411004ff681200c7fe3254409ffaa4a004ffd4552027faa8a9017f81084001feb0a4000ffd8910017fc84a9013fd5154003fe10a2000dfd4941017fe4290017ff6310035fe32a8000ff58121007fac890807ff41484017fb0a4002bf98840007fac8a90dfff53d0809fea94a005ff8c1200effea720003fd6448009ffaa2a802dfd4a2001db8c6aa0d7fc655083bfe9948002ff94920016fea5a1002fd6095005fe9968404ff1465000dfcc3a00d3fd53508077f31ca035ff99542007faca908037f5290001fea12a025ffcc95002ff8211005ffe615000bff32c4009ffd82540a7f8a420013fc529500fffa9a2001ff1455104ffecba080afc62440037f30aa439df0c55203ffa6488002ff605040bfe3142000ff54b40017f843100cbfd6354401ff3224209bf9922018ffcc4a8807ff41840037f30aa000bf59250005facb08013ff505480bfe32c8001ffc412114ffc6090817fa4010013ff3168218ff8c94004ff8c1a0807fe31d0401ffb0a80049f19510007faa0a0013fd545442ffe28a8009bfd8f4104ff8c32a027ff54d0009fe29aa025ffd0d5014ffca690817fc301000bff30c8042ff0c254017fea4a900a7d62d4809ff2a2a402ff10920007faca90013fc5155023ffa9c4000bfd895002ff8c320027fc63d0413ffb1e8405ffc4210017fc64a100afe6294003ff90a4219ff98d40007fac2a0006fe61550037e30aa405bf18152017fa6510017fc5054001bfa92203aff90d5201dfcc7a08ffff63550076e31a8225bf58d50007ea42880cffc5150805fe90a4002ff9492100ffea2a8897ff635400bff2828001ffc861002ffcc928027fc5450413de210800bff94e101d6f886a9017fc6188009fea8ca02dff19541007faa420013fc535507ffe98aa82eff08341007fcc890003fd5450073be30aa41def10e400c7fc84a000bff5250813de21e8409ffd0d54136fca3280e
  | 3 => 0xf90ea409bf19151005fac5280b7ff52504137fb2e8034ffd8d42005fac1a1002ff615480bfb8842009bf1974200fdc4290827fd54d0801feaa4803aff4c5521affea8a1003fc6454865ff992a202ff90b4202ff82108002fd6550005be292a409ff59741017fc65100b3fe4350485ff98ca805bfd8a1009ffc6220013f7515440bfea844005bfd8e4002778a8aa057ff311000bff32c201effd46401f7fe40aa083ff20d0001feaa2203eff9095402ffe412801bfe42440037f30c4001ff08610005facba1027fc54d04077f31c4029ffd4d2100efca2a8803ff4294021fe28c4000ff1815202ffcc52000bfd3248473fe18aa400ff54540027f8a6a880efc63544037e30ca834bf58d4205ffea708007ff5144065ffa1aa239ff98552007fec2a8027fe545045bffa828205ffd8a5004ffa822000bff52d080bff3142004ff9465005ffa6508027fd4395001fea12a205bfd92100cffe64a0006fc61550037f30a8005ff9411000ffc82a080bfe428801d7eb1a4004ff9455003ffac68808ffe2154001ffa022002df10b5204ffe8620002fd61880097e32a2009ffd8f40027fea4a8803fd54880597eb1a8205bfd8c40077fec69000afe625003fff10e803cdfcc35204ffe86a0067ff635003dffa948000ff1911004ff88320017fc6588033fe29a8005ff98c401fdfac6aa00b7f52484057f312a217ff185401a5fec6a1003fd425007dfe192a82cff4c14102ff8c520003ff6448469feb1a8441ffc825402dfcc1a104bff5188009bfa92a209ff9074204ffe86a100efe6390013dfa08800fff1512002ff8a0a0012ff6455069fe29a8409ff95342027fca2aa00bff325080bff9008000ef5534102ffca110027f74150409bfaa2a409ff58f40007faa8a10ebfc4354813ffa108005ffd8a4002ffc8020017ff4088001bfa942010ff106201effc42aa017ff5090071ffa868419ff4c540007fac8a8013fc5254079bea1ea435ff1414200ff862a8827fc41d0837ff20c8001ffc8541005fac1a08137c53548077e31a2004ff9465404ffe85a0827fc4350801ffb0a8404ff54d5202ff88088007be41d0401ff2a2201dff90e401d6fa62a9023ff504402bfe9888009dfd525404ffcc52a007fe4144013ff30ca801ff105101a7fa62a1026fc645404dff10ca002ffd4a2000ffe21a0883fc32d0011ff32a2005ff0c15004ffcc7a1007fc2150403fe0828202fb1094213ff865280037d52544017eb2c8009ff19740026fac7a90dffd30d083fff28e8007ff90d1002ffea1100027f6544001ffa0a4005f798e4002ff88110067fc635002ffe18a8007ff4c110016faa4a1043fe418805fff29e8242ffcca54077fe6090013fc52550017fb222009bf19121005fac508007ff21d0405fe10e842fff8c341016f841a9026fe649400bdf2028005ff18c
  | 4 => 0x27fc609501bfe20a401bff0c64002ffca120013ff5454805ff992a405ff14220017ee429085ffe51500017eb0c8004ff14951005faca88017fe30100057fb024005ff59620217fc612a0137e60d48437eb1e800eff90d2000ffea30801bfc62440077e31aa409ff58b40167faa6a08137f63d4803fe18a2001fdc4121017fc42a103bfd3048013ffb14a817ff8854002ffca108017fe6484003fe0868205ff4c240015fec4a1002ff6548031fe2928018ff0c9401bdfac7a10037d529000b7f3008009ff58740016fe40a9016ff658800bffa042002df54b42006f8ca88002ff65500037f30a4015ef90c400edfac720003bd42d044bff98aa000ff5055014ffac6908037e6054813fe2108000df5491006ff8c290003fd65500037eb0c2009ff10a54007fa4220002ff604847dfe102a809bfd8f4000dfecaa880bfc3250801dea128032ff18d51177fca5a0817ff301005ffe9968209ff10e40217fe612a027fc43d0819ffa942002bf98a540effaa720017ee204807bff18aa810ff0c62017ffea7a0807fc4148401ffb2a4234ff98d4204ffa86200fffc3055003fe0824200bf59220007fca8908cbfc3054455ffa824202ff1494212ff8c6a8007fe414840bff3244003bf18d2012ffa86a801ffc434406ffea9e8400ffd912007ff8ca9001ffd534400bffb088005ff082501fff8c6aa073fe429000bfe1068005f758e4002ffecb08017fc3094003fe20c2032bfd8d51007fac0a08a7fe434840bfe2042009ffd8654016faa5100ffff315500b7fb124000ff9521002ff82090017f4104400bffa842001ff9061000ffa62a8817fd6110005fe10a4029ff4c121005feca88013fd5254469fe1828402bf18b41005fec2a8017fc305001dffa9a4000ff58550037fc64880eb7c30548017eb168205bf18e4004ff8c7a10037f52d0401fe3028205bf98254016fc43a907ffe31d004dff18ca00bff90e1010ffe63a0013fc5054823fe21c4001ffd4541027fea8a8803fd5450457ff2128203bf18f401fffa86aa017fd3084083fe104a834ff18d42147fe632800bfe32d0805bfb12a405ff54240026fcc9a9006fe6195031ff3128005ff0804000fe8a2a8806ff6248477bf886a400ffd09501cefca2a90dbfc51d0805fe9924005bf18c40016fc42a9047fd5388001fea0ca000ff54940016f864a900afe6250409fe29aa404bf99742016fea49006ffc5190003fe20a8228ff50e5002ff861a00e7fc6154809be31ea400bfd9541007faa0880137d64d4803fe28a2009ff90f4204ffe85a0093ff2054079bf186a403bf98d42017faa4a100efc6350869fe9828406ff9891002ffec70806bff5450005de2128409bf19120025fccb20013fc5054413fea1e8005ffd0240007fac888103fe3195011ffa922001ff08521157fcca90807fc21d0405b
  | 5 => 0x511004ffc85a08cffe6150843ff29e8004ff94d500cffe62a0027ff54d0805ff902a405bf1814217ffa61a0816ff6388049ff90aa005ff5961002ffcca2000bfd528800bfe1844009ff1874214ff8869080efc63d0409ff292a034ffcc542017fc6490016ff6144001bea942000ff99150007faa090027fc5410013fe2a4a804df5875202ffac310002fd6110067ff18a843dffc415414ffaa690816fc6484001ffa0ca02cff14d411f7fe42aa003fd415001bfe28a4002bf98b411def821a9067fd43500057e312802cffcc94102ffc60a8027ff4350401feb02a209ff99741005fac3a002ffc4384005be10ea403bf98c4004ffe84a00037f6550459ffb1a8207ff18d10005fac5a0017fe3094029df2108000ffd095100fe84290817fd6590009ff292a804ff94d5404df8cba0027fc63d0001fd1022000ff5094102ffe2128017ec2048005fd9044000ff546401a7fa86a100bfc325484fff90ca000ff5512004ffec3a007fff10d0017fea9c203fff8c154017fc84900fffe6355025ffaa44004dfd8752187fea5a0817ff62100097f32a8001ff4c54102ffc61a0016fe6088005be996a401ff54510157f8ca90803fd6254049fe212a000dfd9510006fec0a90c7ff2054405be102a405ff5022002ffc80a0027fe61d0009ff29ca001fd10541025fccaa0877fd3190013ff2a68200ef1912004ffe8720027ff43d0809ff28aa401ff1074107ffea29000bfe2154801fe90aa004ff94a5004ffe8220077ff3290041ff90e8000ffd9110017fe65a10c3ff50d0401fea02201dff14e401bff8a7a1003ff404800bff2824009ff5074004ffc87a0817fc50900015fb22400aff8ca1002ff8c928017fc611000fffa1a2000ff50a4000ff862a0807fe41d04077e31ca800ffd8141107fca5a00cbff63544077e31aa807ffcc9100c7fe40a001ffc5344013ff32e8005ff58e1006ffc8290003fd5188009be30ea43adfcc55202ffaa108027fc425500bdfa008002ffd492102ffe6128017fc50440017eb242009ff58f4117ffe61a083ffe654800bfe286803fffcc154017fe40a1017ff1010081ff884a837ff4c74200ff8a308027fe5490039ff1948000ff50910146fca72800bff5248013be2a2a800ff48650007faa90800bfc5254809ff29ca805ff08150007faa890816fc65840077e31aa000df549411defc63a9027fe6395003ff28aa20aff90a1008ffa6310027ff62d002bff2988001ff4c5101d6fa86a9047ff438804ffe214a001ffd452104ff8cba080bff3288059ee31a8200ef506400a7fe4220003bf4250483ff90ca811ff14e2007ffea090003fd21d0013fe2168001ff8855104ff886a0853fe5210001ff2a2400eff98d2019ffca2a1017ff65100077e31a8236ff0c74202ff880900ebfc3054805fea144021ffcc340027fca52a
  | 6 => 0x9bfa92a809ffd8f41026f8a32a016fc648806dff28e8400ffd8520197fe60a8813fc54940037eb0e8209ff98f4102ff82020103fc1095003ffa8e8204df1835216ffccaa0816fc628400bff1022034ff8c142005faca90817fa2084047fe30aa000ffd8151077fa62900037d52d040bff9044002df5492009ff84220002fd64484037fb0a8200ffd951003dfec68800bfc2054881fe10ca809df95154007f8c890867ff305001bfe18a4009ff10940006fac2a90d3be435080bff3088000efd0640026fea528027bf42d0403fe98a421bff94640026fec1a9017fd6488037ff10c8001bfd8110177fe41a0807fd51840237eb1c4009bf99121006fea5a0073fc3290013feb1ca804ff15150017f865a10a7ff4348401fe90a8015ffd4c40017f884a1013ff5395001bfb22a401ff94510017fe6490807fe2144073bf882a428bf58e500affa64200a7fc5348485fe994a805bf18440007facaa082fff328400dfe192202cff0c14104ffacba100b7f215480bff32c802fff54f4114ffec6908177f5094001fea928239ff8c552157f8a090812fc6548401fe3024200ff981411d7fe62a9002fd6244005fea124200ff54a4001dfcc72a0eb7e535480bfc1044005ff5021005ffe8708002ff62504037fb0a4209ff5834205ff8a70800afd6288013fe32e8405ffd8e40005fac890003bd4250403ff98aa202ff14b420e7f8a5200eb7e3054857ff1928205ff18e10005fac520016ff65100017fb22a405bf98341017f840a10c7fc205440bfe31c8004bf9974000ff8a2a080b7e5254805fe1944018ff18940087fca310003fd428400bfe284203aff50d52017fc431001bfc524406ffe186843bdf90752007fec2a9006fe61d08077f31a4200ff1814202ffac508006fe61508017fb02a229ff18d21017fc84908037e6454877be20ea409bf9911002ff86120017fe618801dfe21a4001ff4c61002ff860880b7ff545045dff1968200ff181510d7fccaa0003ff4154003fe18a4205ff58e50027dea4a9093fc3254047ff18aa025ffcc15002ff8ca200f37e43d480bffb0c8009ff59740007fcc0aa0b3fd63504017fb02a409ff1534002ff840a003bfd53480077f31a2002bf99342005fac3a1007fc51d0479be986a401ff8c55102df8c7100ebfc6354813de218801cef10a400267ea92a026ff63d08017eb2a4009ffd0740016f884a90037d605483dffaa48000bf597400bffc62a0027ff62d04077f31a8202ef10b42017f8a510017fd6210047ff882a001ff0c6101d6fe60a90eb7c635480bffb0c4004df58352017faa5a1017ff6494011fe32a2003bf98d5402ffcc720017fe63880077f31c2002ffd094204dfcc89000b7d5248403fe28a4232ff50d5104ffcc1a1026ff65d04093e32a8201ff54541007faa488027fd54d0473bf18aa408ffd
  | 7 => 0x90803fc605500bffb1ca001fec4110014fec4a90e7ff1054805f72168405ff0c120007fcc090817ff5094015fe194203fff90d54027fea32a017fe501003bff98c801bff8c640137f88328016fc6590001ff322a409ff583411eff842aa006fc615086dff18e843fff4c15400ffc4308013fe5494003ff28c2037ffcc74204ff8a8a10177e5054013ff2a68000bfd9150137fc8328016fc651000bfe082a009ffd094102ffe8020016fc6194005ff90aa401bf98640007fa832008bff50d000bfeb288005ff0822018ff8c4a8816fc6190003ff18a2001ffcc510007fec8a90f37c43d4813ff20e8002ff14921017faa4900a3fe4394047fe10aa001ff54741005fec4a0017fc6210075ff982a400bf59741017f884a9027fd43d085fff996821dff50e40007f240880136f6254801bfb0aa400ff58951017f6409000efe635002dffa90803fff4c954027fea52a026ff65d0813fe20ca805ff4c25007ffea8900bffc53d04077f31e8401bf1874210ffa61a0003df63550077f31aa201ff5051004ffc8620017ff6284001ffb028407ff50d1015ffe40a0807ff10544057e312a205ff04250027fea6a8013ff5394015fe2942004efd52541fffe64aa05fff105001dfeb1a4029ff0c12104ffac7a10137c5454821ff18c4004ffd425408ffe6310003ff605507bfe082a805ff58640017fc43a1027ff43d04037e30aa038ff1434204dfcc92a027ff42900017fb12a209ff950400177c84a1017ff501006fff1868404ff94d51027fea6aa003fd6544013fe2088011ff50e2004ffc8220003ff6454013ff20ca819bf58d4004ff8c52a007fd31d0461fe2868201ffc8551007fac2a1027fd42d041d7fb1a4004df146501b7f821a1017fc3084069ff9828404bf9944004ffc872a003fd4188001fea8a4004dfd4a54017faa4908c7fe425440bfeb1c8031ff1095102ffec908003ff4244065fe992a20cffd5210027fca4a88b7fc50504097e32a8242ff4c25402ff821a0003bd42d004dfe10ca005ffc8240016fc65a9017fe4044057ff3128202ffc834202ffa60200cbfe3054409bfa92a03adf58d520fff843a0067fe5350063fe192a233ffc4142015f8c4a0803fd5284003ff20aa209ff10f410c7fe42a0007fe5150403ff10a8200bf58840005fec4aa063fe5250005ff9924000ff58940027f6a12800bfe525080dff902200eff14d20016fc85a9016ff6590001ffb12a804fed4150007fa809003bff4348003fb20e8234ff94d42006fea42000bfe32484057fb2aa438ffd4742007fec0a9003fe6454401fe322a22bff0c94100ffaa29080bff2150813fe2a2a828ff4ca50007fecaa0817fe3050003fe18e8200bfd814202f7a8020017ff6588043ffa9e8005ff90220017fa849000bff4288043fe9968005ff14120007fac0a10eafd635480
  | 8 => 0x70080000500a004004000130000381c8020021ccb50bf00e798028000001b8088250220a8558010005482a892b440300384901603c000040020001e02c03c0240117d0000040280c00010acf0050573800104505e65002000602078008030020140401014e0081604b0000141486d0060000500203e000368010000000882100a010040620020bc00108032d2da100103596c2c802cb80380100900407808335064011908070002dc9880200c728088000201044a0070a4020020140be01c0080000201800006000020008020000040000402e01c088000064ddd000006e00400184000044008020340041980b0006841382c0080880080105e250000330a61602202900e000058000287880600100006c408da0522340805d00000010801006000000e101e00daa01301407c0101903c000158000d20440f85e0120000000100000c2d00108800802000001054c100500b36ce780093e0004c0000360280000608a4440000e0100400000400000003002020074018030520000880d000014000060000144800a00e0e4520110000b4020000020441600602a568000920b2168020009983200580808c00c0b0141b40f73080211a201208760000105f8140cc1080300037c1a40400003c0200980001e03003004000948090040040180a2850e20000500200005c170913620040080900002000004168640038050171c0500004724080780008e0442e9a10002440280000e0240d8032aa5180583d002010060290001181e81a00a0000002414a0500083300c0dc0784d0bc00d2c0001893a80100107e9601980c006000190340d816009007000011ff00e00a060000081c001400807012000000000482842480300801c0c008130918b482900a010190000600750800800200008006b8ab8c1c81501a084000090180788780c1000000501a0020106580937238c01a370382480280004e271e38603700040080a01200c03ad800a020011a503201801006000034010002560640f00000e004038180100000700e00c0000201337a000000000100046200002010c1987306a004238000020000300100002c008026be16800802016008070000080400080201c0000000504605800002045380009473901cc0080000002005ec73d2000058000420240080001c3580000800c09c0c03200408017a9705e02cc28000020000e003fd52d040bfeb0ca000bfd9120017f8a490003ff6254459fe31a8234ef10d4200ffc4290803fe605484bfe982a002df4c95202ffc4108013bf5455077be18ea404dfd415204ffcc5a0013ff5294013feaa08009ffd534104ffca8aa027fe4210009ff29aa42cff50d4104ffc852a016fc618800bfe31ca022ffd4b4002ff84088027fc415500bffb0ca03dff9055404ffc87a0027fc41d0013fe2a28016ffd4440017f864
  | 9 => 0xb00c004000000203180780000200000001008218000eb04c0040
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf75585400067f65551421167c65d0110007b87448210104ff705912002ef61058640037795248110397d741d8d4104cfc7654140204ff7559541004ff7358840024fe75d8940004fd75d854202eee20588400067f659814100774654851001cfc73588400167c6254a40004fc7650550024fe76d95410adbc73504400067e5358a500467e76d4910066f551d8550004fd73d95422273f4054a401367d70d951000cfc71d89540e6bf21d91200a4bf7650b402267c7654a4023e7c64d4a1007e7e65d9520004ff7158840004fd74d8950006be43d91100e6be72d912000cfc71d8154005bf7458520006de62d8d410067e62195100067d73d9541004ff73d9520004fd75d9121005dd73181520057c765494102cfc70d8910004ff735952000cfe76d8552006f820d81540067e6118152004ff735944004eef7258a54004f7715952001cfe7358a54004ff7158254004ff7359540006dc63d89540067e6199152004ff71595420257f72d8552006dc6398141005df7359151004fd70d8552006dc50d8d410067c65589412267f6554a4006ef451d852000cfe7654110006dc7258e40006bf6499152006dc635894104dbf76553411167f525974023779405484002cfc76486500247c75584400e6bf42d912038ede51d8d4130e7d6354b40136f441586500267c76d4b411d57e73d8152084ff72589101cf7621d85521eef651d85541367c51586500073d52506400067d535944001cfc735865404efb7058254006bc54d91201fedd75d8d5400cfe71d9510005fb7054b40006df6398141004fd7358840006bc645452046edc52d8d54006df72d8d412367f6499152006dd71d8d54004ff7358a100276f629515202feb7248110005dd739814219dbd72d09410f6be54d9150006bc43d9120006bf651912006ef710d85200267e6554940006de41d8d54375be76d09411067d6254b400067f65541102aebc20d91201d67c63549503467d52d9121004ff76486400079e73d91202267e765484027e7e30d95101d57e73591520076f62549512377b4054940006f9601815401cfe73d91522367f64951521cd7c71991522267d60181521d5dc735815204cfc76d055001cdc7359520006f751d8542006de61d8d5402cfe70d8542004ff73d9151004fc7654940195dc7359151004ff7259110007eb624811016f3c65551411de7f52d89510067d7654b40006bd6450a5023f3e40d494002cff705862038edd51d8d41006de42d8d5400d7c71549511867c505974100dbe715534104e7e64551521d67e6354b4102cfc70586400055f7355152006df5158e40006be71d9120006bf64551200067e43d9541005df7355140075dc735852004ebf7319120006bc6519120006dc63d8154005fb70552100167e62d4b41004ff72592100057f71581520267f6154951
  | 1 => 0x954004cfd72d8542004fd73595422257c7058552004ff7358b40006bf645452002efa76881100cddc735954004cfc769511011ef651d8550006dc7359110006bf65d91200067f20d95412aebf72d9120005f870585420267c6595110024fe76d954002cfe70d89540157c72181520057d7095152004fd76d06501773f4254b41004ff735921004ebc64d052016e7c50d9541004ff70587420067f7559510004fd7358254006f96018151024ff765411015e7f5259121004fd70d895104ebf6050940005bc74589100076f625495002eef7258840004fe76509101d67c63549510076f72591520577b524821004cbc74589100077b605815201cfc73d911002df87050a401bebc63d09402067651586540067f52587402a6bc5019120006fb50d8142006bf74595411cef410d855216e7c52d95410d67c51d954002cff7258840024fe7559220014fe7259110086ef21d89101d57c7395152256fa10d812102cfe70d9121004ff7654a4001cfe73d8121006bf7459542036ec42d89101cd7471581521d67c6354b4100cfe71d9542004fd74d855046f5f52d8d54004ff72595410067d43d95412067c71d95414076f62d85520067c65981410267f76d4b410d76f7254940004fd73d9110006ed3258840075dc735952004eef7258b4016f3f5255141005bf745414000777715915200df8714811000cfc765514104ef8405825402df8705054001cfe7358a100067e62d95410d57c7558540004fd73d81510267f76d4b400a67d625484013e7f52d9520004ff73d895402cfd71d89100067e765491000ef461505400167c62548400167e6254b412067f41d954104ebc64d062000dbe71d094101cfe73582543bf7741195410073d5454b4104cff76951200067c6119152006ef62d091023e7f62d4a4025dbc7050941014fc72d954002fe8205012040eed52d895102ede1058e40024fc7559120004fe76d05502267c6354a103b67f611954106ff221481100075c73591521ddef725952115f3f52d0941005df73551420057d741815225f9e635064037e7d635494104faf72509410067f6554910006dc21d8d540047e76549410067e6219541024fd72d81520067f6558941006dc52d8d4101cdc73591212257e701915200cfc71d95420167c625495001cfe73d855200cfc7159640037e4624851000cfe71583422267f615491004efb4058254004fd73d81540257f725495102ebf74592200267e6554941004fd7654840006be42d9150016bc62d0940005fb7054840004ff7650520004ff755864004ebf4258341006df20d8d41014fd75d85520057d7195152004ff7158a5400cfe74597411367d21d9510004df7359542007747158152346bf42d91210067f52d854038edf41d8d410067f645495100cfe76d854000cfe7159440004ff7358a540057
  | 2 => 0x67d53597410057f755891004cfe7458a5404cff72d95420067f32d951002cfe76d81521d55c7355152006bf6499110004fd72d915100dbc765514102cfe7695210014fe745974200cfe76d8554006dd5458e4018eee62d89510d67c65501100e6ee4258a40004ff75584402d67d63d4840005f771551410267c76d49414367f621915239dde76d8d410467f50d95102257c70551520267c76d4b400047f755891004ebe64191520065c63d95410a7b82019120024fe75d8941006fb70591100267c6554b41007bb744821024f7741d4941006bf42d814104eef4258b411cef461585520067f655412001cfc73d854001cfe7358650005fb7050a400065c631954102ef41058440006be73d91200167e62d494146edc51d8d540debf41d9110004ff765462027e7f651815100dbe719514106cfd76481101357c7154a5002dbc765094004cfe76d9120006df10d8d5404faf7250b400067d6319510005be76d09401de7f61d494102e7f75596200e73e4254a40005df735894104cfc74586540c67f525834204e7c7655152145dc735065004dbe7454b410267c655412002dbc7050b40016bc625094100cfe71d91102273e405494038edd41d8d41024fc75587401073f42d4b4024e7c64d49101d57e735855204cff7650120004ff7358620006bc65d912000cfd72d95211d57e731815223e7f75d895001cfc7358740004fd71d89402467f63d49100157c72d855202cfe76d81510dcfe7619110004ff73d8910006bf64991500bcfd7650110004ff76548400247c755912101cfc73d9121015ec725012022774105491001cfc73d81520157c7219152006f5614865000dbc71951411ce7e76549511ecff7159541006df2158e401457e7354a5000cfe71d9540004ff71596200d67f525954000ef661486401f67f5259742306dc4258e40014fc75d89500067e63195410065c65d8d410067e63d9541006dd73d91200167e6254b4002e7f75596400a6bc52191200eedc7458e4000df47155141005df73506501de7e61d4a4002edc2058e4002cfc7058a54014fc72591100a6bf2019120004ff7654b400065f65d8d411367d31d95100257e74951520047d72d95411d57e73551522de7f6354940024fc75d912023e7f64d4a10024fd72d8552004fc76509510467f5258650004fd7358742006be43d9120004ff73d8950004fd73d895141d7e76191524373f42191522367c5459542165dc73595410267c76d49400067d655434000dbc71553410267e655484002cfc7695210006be51191200edbe73d0640004ff755862001cfe7358440024ff7654120004fd72d9510006de72d8d5402ebe40592100067c32d9510006ee21d894002ff010d0110005f77159520006bd641911000cfc715922001cfe73597421bebe63d09400167c6254a500d67c655
  | 3 => 0xc745862000ebc6150440396df40d8d41105fb70591200067f30d951015eec20d89410273f7455152016bc76509400067c75d8941004ff74595104557f735515220cff755954211cff7159510004df7359741227787054a50006dd75d8d412aebf64181422067c31d9541006df72d8d540166e62548403cf7741d954100cfe71d8940004fd73589103b67f651915102df870484401cdf471591522b77920d81520257f72d91520e6bc52d912004ebd73191200067f7654910005ef72501201e65c63d49410debd41d911002df870487400067c75d891002cfd7059610005df73595410e4fe7619120004ff73d9150005df735911000cfc76d0110006bf6499151024fc7558a1004ebc64505200067d52d85400065f63d49410c5bd72d0940006bc64d852002ef71058a100047e7654910006df7158e400067d76549100267f76d49411a6bc635094101cfc7359610004fd73591101367e21d9510006bd43d912002cfe7695220006fb705954002feb7248210005bf7550b41006f4715954202df87055140267762119510006f53158650004ff73d9120004ff755912104ef74158742004fd73d9150014fc72d8154004fd76951211d55c735915213e7d52d95202267f6254a400d67f52d954035e7f52d952104ebc64d06500067c73d9541024fc7558742004ff7358a502367c645495024e7e64d49101cd7e71d9152004ff7655210006dd63546400073c6455152014fe7259640007f070485101fede6355240024fe75d812104cff7695121014fc7259541006bf64d05200e5be72d0640014fd70d952002cfc7058a1002cff7559440014fc7259250014fd74d854238ede71d8d41004df73591100077b70591520076f725815200cfc71597402357e741815201cfe73d895104cff76591210073c7458152024fc7559220004ff7358a4024f3c43d48402a6be50191200067e73d9510004fe7648550306df4258e4004ef7715865401cfe73d9110014fc72d815104ebe64191210976f629815200cfc71d89400667d76d4a10004fd764874004ebe6450a103b57e76d954101cfc73589102aebc50d912001cfe73d89400057d72195102267c6454a10006df54d8d410067f7559121004ff7358341005bc74585200067c72d9510004fd75d85200667f5259610006be51d912002dfb7248110206f6315865401cfe73d8542006f771589100067d6554b400073d54549410a73c42d48400067e72d9510006bf311912004e7f755974219eef2158b4104ebc6450620004fd7650a5002cfd74d8940306dc5458e400cddc73551402257e70d9152006bf7459121005df735522004eec4258b4100ef66148650004ff7059521006df73589101de7e61d4940004ff75587420057f75506500167e62d4a1004cff76d0620004ff73d81210257c75506500167c62d4b41
  | 4 => 0x865004ebc64d01200067f70d9541006de75d8d410167e62d48402367c6454910005f8705915202ff361481100c73f52d09400067e73d9541006ed6254840006bd631912022e7f6354910005f571d011019ef4615854218eee52d8951005bf7454a4041e7d75d91521167f52d8154004fd7358a540267e6054a5002dbc70509400267c6554a402d73e43d484002ef7715864004faf72509400067d6554940004fc76551203ce7c40d954104ebf65504400167c765495102edc5058e40014fe7258440005df73581211f67d5259742004ff7359542006dc62d8d410067e52d95101a5dc73595420057d71d91520e7b820d912000df87148210396de54d8d410157e7255152466dc41d8d541f4fd7655142006de5158e4023f7710d4a1004efb4058342006bf31d912001cfe73d9121006df63d855400cfc7648110056f521d85200e67d62d4a4001cfe73586200f67d76d4a40024fe75591202357f7319152004ff7258740006ed6248440006bd641915201cfe73d952002df47048510004fd73d91511167f505974016e7e76d49410067d52586501ce7e6154a402267f6454a101ce7c61585520a63f5219120036ef20d891001cfe735865446edf52d8d54004ff73d91523ce7f40d9541016f462485100a6be3219120026bc65951411b6ef21d894131e7f52d8151006df73595400257f7254a50014fc72d85540056f725915204cff76d09100567f52d8520006dc61d8d5404cfc76d0520004ff7458a50024fd74d8554006f7715912100cfd72d8121396dc40d8d41006bc3119120004fd765512007e7c5158a5001cfc735962002cfc705922002cfc76505400577952482102257c7398152004ff73d91100067c765491004ebc7119120004ff7159220005bd7550b411dd7f72549410167c62d4910004ff7358740006bd71d9120004fd75d814238edf71d8d410b67f5259440014fc76d012004dbf75d094102cff71d891001cfc7359120004ff74595210057f705915233cfe7619121014fe72587402357f739915202cfc7059210004fc76545401ce7c515952146edf74d8d54005fb705912115e7d525912102cfc76506501ae7c655091004cfd70d8540006dd72d8d5400cfd70d951000ef66148440004ff73d8550005df73581540057f75585200d67f5259250014fe7258650007777154a10006fb20d815401cfc73d81410057e765491000577715915201cfc735834114dde7318121014fc72d9541004fd70d85420067e32d95411a5dc7355142005f7715011002cfc76d0a100067d65552400067d52587400067e51d9542006fb6098152006f9601815233ebf41d912100cfc71588401de7e61d484000dbc71551411357e7619510024fc75d8142004ff76506200075f73551520066f62549500053c745815227e7e40d951001cfc735952004cf
  | 5 => 0x4ebe6450a500067c65d891002cfc7058a5001cfc735862000cfc715834201cfc73d85500057e76d49100fcff70591103fe7d635495104dbf7650b412367c7654b4000cfc715912002efb61881100057d70d91520a73f52191200167c7654950006de42d8d4102cfc70595420c4ff72591201067e64d484024f3f41d484022778705484004cff7695110024fd70d8950014ff71d952101cfc7359440004dd73d9120016be625094002d7c7654950004fd72d815404e7d5458a540067d70d95410067e42d9541004fd73d8121024fc75586201ce7c61d85520047e76d49100079f735044004ebc64951200377752485102677810195101cd7c715915204cfc74596100073f649515202edf2058e4001cfc735834233ebd41d91210067c75589101e67e63d494131efa50d81510273e7495152006be531912025ebc4059110005bf755094107e7c655952001cfc7359510024fc755864004dbc74486400067f7559110006df70d8d4104ef44158440006bd64d0a10007787054b400e6bf20d91201367e31d95100067c63195100a73c42548401d5de7318152005ef72551421867f52597410167c6254b411f67f52d895424e7f63d4b40006f8705954202ef410586200067d6554a10006f96018141024fe755834206ef661d85200267c76d4910016f662485100067f7559520014fe76541201347e761951002cfc76546200eedf7458e401ce7e61549401ce7c51d85521cef441d85521267f52d8950006bf64d85200e6bd72d9120004fd73586401cf7661d8552005f771595420067f43d9510116fa50d8154006dc7158e400167e6254a10004ff73d8152005df73589542667f60195101de7f75d89512b6fa20d8152014fe7259510006bf64d0110196de63546402bebe40d854035e7d52d95210157e721815202e7f75594400067c62d9541006dc5258e400057d73585522367d64191520167e62d4910004ff7058a5401cfe7358640004ff7558a100d67e76d49400073f745484004ebc7019120004ff71594400067c62195410067f65481102ce7d635484002cfe70586200076f72585521b4ff725912100cfe76481100067e53d954101cfc73591210067f655414007e7f50d9520006bf64505201f6ee42d895401cfc73592100a7bb201912015f3d52d094104cfd71d894101cfe735874001cfe7358910004fe76951210e6bd70d912045d7d7395152004ff73596100066d6254a5002cfe7655220004ff764874002cfc70597413267f6354950004fd7655210014fe76d8940004fd76547401073f4254b402373c43548400267e6554a401ce7f6154941004fd70d894116e7f54d954111cfd7654110004ff70591210167e62549412367c7654b410c67d52583421cd7c71d915204cfe74d8950306df4158e402067c61951522aebe50d9120136f6215
  | 6 => 0xd764864000cff765064018eec62589512267c5059520026be65551410a63d52191200067d52d8151004fd7358b402cf3e43548400c73d52d094004ebc6450120005df735854219cff715912100cbc745834100cfc7159742004ff76549400567d52d852038edc10d8d41014fc72d915144f5c73551522376d729515225fb661506402aebe70d912001cfe73d9510004fd75d891004ebc745834104cfc76951210267c76d48401ae7f54d954227e7c30d9510006bf64d0120004fd73592501cd7d72d494142f6f62181522067c74d95410057d73d8552024fe75d85200167c6254910005df73551210267e65952101c76f62991520057f73d8552004ff7059541004fb705912124f3e74d4b410c67f5259120126ec62589500067e51596401d57c73551521867d76d4b41006dd635064002ede5058e40006be42d911000cf4715954216d7e7598141124fd765412003ddc7359110007777154951016ec625094116f3c65951410067d7654a100067d6454a5002cfc7058a400067d655484001cfe73d81513af9c63951410267f76d4a10014fe72d951004cfe74d89512067f74d954129e7f52d81210167c62d4941006de73d912004fbb60d09402bdbd76d0640004fd735874000cfe7158a4004ebe75191200267f6295152014fc745834201cfe73d855402eee2058a40005f8705912102cfd75d9150004ff7654b412357c74585521773f42d4b411ce7e615484001cdc735911024e7f75d8954014fd75d9152004ff7259610014fc72d95101d57c73585521ce7e6154a50004ff7158b4008ddc73552202267c6354a50024fe755921000df8764811001cfc73d9152004ff76509101de7e61d4b40004ff7558a40006bd65d064002cfd71d91100057f755054004dbc73d06402c79c73504400067c63195410e63f52d912002cff7059610006ef725912104ebe721912000cfe7458b4100cfe71597400d57c7550540024fd71d91511267f5259620004fd72d85501d65c635494104ef84058342004fd74d89100067c7559110004ff735952113e7f5258a50004fe765452000cf8764811024e7f63d4b41005ef7258141014fe72d9151006ed6250a40006bf54d9120006bd63d9120005df73505400073f75504400065f6354941004fd735952000cfc71d954046edd50d8d541ce7d75d85520cddc735054004cfc76d095120eee5258a5418e7f525952104ebf75191200067d7654a4024e7e76d4b410079e54d8d410e6be32d91200073c75504402073c5195141006bc31d91201ecfd765514102ebc40592200057f7558941006bd64191201367f51d951023d7f72548402257e7095152004ff74595200067f655494002cfe70d89411d67e63549411a6be6350b400bdf97099110004fd76544400067f63195412367e64549101eef661d85540057d7498152
  | 7 => 0x96200067d6554b410c57f725494001cfe735974127e7c20d951012ddc73591500057f7055152024fc75d854016f3f5295141004fc764854004dbf70d06402a6bc1019120006bd65506400e6bc72d912001cfe73d854023f5d63d4a401267d52596200067c6198152024ff7655240006df635094102cfc7059121004df735891015eee62d8941004ff735974101cfe7358b401cd7e7199152004fd72d9540024fe75d912123f7a40d48400247c76d49410fdfb70591101cf7651d85521e67c63d4941007786588110004fd7654b410167e6254910004fd73592100567d62d4a1001cdc73597410067f655511000c7c76549512a7ae20191201cf747154a10006bd531912024f7b40d4a401de7e51d8951005fb70506400067c6559110005ed72d01201d57c735915200dfa7188110006dc72d8d5400cbc76509410067f6550941006dc7359121006f561484401267f6254950005f7714811001cfc73d91200067c63d954100cfe71592501557c75581210067c65d91101ae7c65509410257f7455152016f87648110006dc63d8554004fd75d91201cd7c71d8152024fc7558b4002cf8705954201cfe73d954204dbc72d0640004ff7058b412067c21d9541355f7715952104ebc43588402467d63d491004dbc7454a400467f53d95100e73f52d912002cfe70d954101cfe73d85201a6dc63509411dcff725952102cfe7654a10004ff7259510005bf74484400067f525844000cfe76d01100067d765494102cfd705862000cfc71594403b67f64195410067d74d9510006df5458e400167f7654a50007e762485102067c10d954100cfe7159742466df75d8d5402fe820541200167e625484002cfc70d911016df57199151024fc7558b4104cff76952102073f6595141006bf6495120004fe76549403867f63d4941004fd70d855404ebc4058341004ff745891000df47150941014fd71d95210973f549522000cfe76d8542006be53d912001cfe73d91510e67d6254a4006ef621d85200067f72d951002dbc70d094000cfe7158b400e7bb20d9120004ff7359110004fd73d95210467c53d9510006dd7558e401df7641d4b4102efa601814227e7e10d95100067d53d9541024fc75588402677b1019510004fd7358a4000cfe7158a5404fb77150640416bd54d9151014fe7259610014fc72d855025ebe40587400057c765491026f761019510004ff7648540014fe7258254006bc43d91510067e72d9541006fb609815111ef46158550006bf6450110005dd73d9120014fe72d911000dfa714811015dec72581410467d76d49100047c765491004dbf7150640227771054a101eef421d855400cfc71d89101eef641d855400dbc7150b4138ede41d8d410e5be72506400077b6548110036ee62d891038edc21d8d4146edd52d8d54014fe72d8554004f
  | 8 => 0x2cfd7058a10006dc72d8d41005ef72585401167c53597400c6bd42592202367e54595423567f62d8552006f5315844002cfd74d85402073e41d95410067f75584401de7f64d4941006bc6119120005fb7055140014fc72d95200057b70591522373c649515223f3f40d4840004fd73d89410d67d76d4940014fc76551421ce7d52595210067f63d95413679c63509412067f10d95411ae7e65d954238edc51d8d4104ebc655534125ebe6050440004fd73597400f73d74d4a402367f6354b41024fc75584400075f735815213e7d6254a501773f5250b4146edf50d8d541cdf471581520067c75591211ce7c61549500267c6554b4023e7e76d484023e7e76d4a4004ef741586540079f63509410067e5158a540167e62d49404357e7499152006f531d85522267f6554a10005fb704874021dfa7688110004ff73d952123e7e60d4a102373e5454b4102cfc705844002cfc705925011ef421d8550166de635064004cfd72d9542004fc7650520007f37048510004ff725844001cfc735864002ef61058650004ff7654a10006bf63191200067c42d9510006bf6450120006df635895400ebf76506401367f21d95101df3e41d4b412276d625484002ebe4059250024fc75583410e63d52d9120015ec72541200047e76d4941004ff765474001cfc73d854238f9e41d8d4102cfe76d0a101af6f625915202c7c76549502257d72d48400bebf4159210206f6515865432dfb7058950015ec7250620006bd645091041ebf42d915216f3e74d4941006dc70d8d41006fb609814202edc4058e4000dbc71d094127f7410d95102373c7454840007777154b4100cfc71582540073f525044004ebc4258840006df63585540065d63d4a40004fc7650910006bf745912002fba405434002e7e50596400063f64951520a73d52191202067e41d95410076f725515238edd71d8d41014fe7258654004fd75d814138edf10d8d411eef710d855424e7e76d4b4004ebf4158a541067e6454840004fe765494102ef86248210004fd71d89541df7621d49100ed9c73506400a6ee525884041f3d42d915201cfe73592200a6bc21191200467c54d95100067f65d091004cff71d954102cfe7650a100067e6319510004fd74d8552005bd75509412373f4154840004ff7259741024fe7558620004fd74d8121004fe7650950036ec625891023e7c61d4a400377552485101cf7631d855224e7e64d4a10006df7558e40006be75d912002ebf745921025dbe70d094104cfe74d8550004fd73595412267c7654a1002cfc70596200d67f50d954006ef4615852015fac625094102cfe70d89510067c65589100067c43d9510004ff7059742446bd54d91521f57f7259152004fd71d8950005df73589100edbe735064002e7d5058a502367f6354b4002cfc765514004cfc745
  | 9 => 0xc655954237e7f63549410057d73d915211ef710d855004cfd72d81422a6be20191201ce7e6154b4004e7c54597402057e76195410073d5250440004fd76d09500e73d52d91200067d52584400267c65549100e6bd42d9120014fc725844002cfe70d855423e7f63d48400c6ef20d89401cd7e7198152004fd7358a50024fe75d8141024ff76541402067f65991510067e43d95102267c6154a50166de76d8d41004ff7059741004ff7655110006dc635895422e7d6354910006de70d8d41024fd71d8951014fe7259541005df735511002cfc7695220006f751d85202377741549410157c7255152006bd3019120004ff75589100157e7219152004ff72596401cd7f7158552006f850d814200dbc715094102cfc705865401cfc73d952104eec4258a54005df73552400267c76d4a1000cfc75d855014ddc735512101cfc73d8151006bf42d854001cfe73595420e6bf70d912023e7f63d4a101367d51d95100e6bc21d912002eee2058a1004eef4258a54015ee72d0120006be41d912023f5e63d4a40004fd73d9120006bc51191202367e6454a1007e7c53d9520004ff7159520004ff735834216e7e761954101cfe735912104ebe731912000df671d01102357e74d8152004fd73591210267e6554b4102eef7258a501e65e63d4a40004fd7654b40004fd75d812102eee2058a502aebc10d9120004fd735865400df47154110006de4258e400057d73d81520f67f52d9150005dd73181511d57c731915223e7f6298152014fc725865011df471589500057f7550620006dc63d95410067f6454950004fd70d95212afae20d91200276f72549502073f74d95410055f7358152014fd74d954202e7c505964029e7d52d8121004fe7650520006de21d8d5404cfc74589100957c7550620006bf101912001cfe7359541004ff7359742006dc7558e40004fc765512108ddc735062002cfc7058b41004fd765522002edf4058e40006be4358840006bd53d9120006df65d8d410f67f54596400d5f9709915002cf87059121005fb7048440014fe72592500bef46158540004ff7650a50005df7359540005df7350620004ff73d95420067d30d954102cfe76d06502277a6018152005df7358520024fc7559121136f631586500057d75981413b73e41195410267c6554a102267e5059520004fd73d85540c67d52591200073f6550941004fd72d9541007bb7050640004ff764844001cfe7358a40004fd73d952004cfe74d95212367c54d9152024fe7558a4000cfc7158a40004ff73d95412067e71d954125dbf7050440006f56150640006bf75d912002cfc7654840006be43d9151004fd76d091001cfe73d81420167c6254941006dc65d8d41004fd75d85400067f765494100cfc71d9120306de5458e400267c65541100073c65509411d57e7358152
  | 10 => 0x8552004fd71d81541067f52d81420067f63d951002ef51058a100067f651911002d7e7054950006dc6358141004ff7358650096ed52d8950016bc625094046f9c54d8d5404ebf721912000d7e715495104ebf61551411fedd74d8d541cd7e71d815201cfc7359220014fe76d89500057f75585421367c71d95100267e6554b40004fd74d95100053f74581520057d7099152004ff73d8154014fe72d85401df7810d491023f3d40d4840006f47159520024fc75d911004eef4258b40016ee6254840134ff75595100057d711815202cfc7650a5019ef661d854220e7e76951520457c76d491004ebd7519120007f371481101367d71d95102067e5158654004ff715834204cfe74d89100a6bd32191200067d7558a50024fd72d915202cfe765521000cfe71d91201567e65d95211cf7621549101d5dc7359152004ff715964002cfc70d8520004fd73d8550006dc7359542024ff76551410075f73591520057d75991100057f7559110004fe76549101a6bc635094001cfc7358b410257f721815201cfc73d89411e67e63d4a103c4ff74595411e67c63d491000cfe71596402267c6154a4004ebf415884004cfe76d915101cfe73d89500247c76d49100267e655444000cfc7159620016ee62484401df3e41d49410c5ec7258540004ff73591200057e7654941006f960181210367f62d491007f6f625815201cfe73d81541cd7c715815206df97288110006de70d8d540457c75589102267c50d81520047f75591101deef21d895104ebf425874000cfc7459741006bc61d9120004fd7358b4115f3f525094102cfe705922023e7f63d4a40006df52d8d4102e7f5058a501e67e63d4b40004ff725825411e7f51596100073e5454941346bd42d91211cd7e71551521edf471589540057d74d815204cfd71d954100dfa714821000ef76048510016bc6250b4002cfc7654a4001cfc73591100bebd4159210024fe75589100247c75589100467c655951009ef621584400067d32d95412b4ff70595202277a40548401f76c725515204ebc6350b4001cfe73591203c6bf41d91510a73e42d484001cfe735834101cfc73d8520004ff73d9121165dc7358941024ff76595211cf764154b410567d6254a102377b4054a402275d6354a40006bd425834102cfe7059440006bf63d91201457c7354a5002cfe70d954224f3e74d4840004ff715954011ef661d85500065d6354a401de7f60d4910014ff7650a40004ff73596200c57d72d49401d67c6354941005bd72951411cd7e715915201cfe73d8152005bc745895001cde73d91202bebf65d0640004fd73d854204f3c5455141014fc765012002ff0105411034e7f51d95211cf7471549510c6fa20583420147f7654a5023e7e60d4b410267e65543400befa10583412067d74d95412067f31d95411ae7
  | 11 => 0x1cf747154b41004fd70d8954004ff7358254005df73505503c5bf7459541005df7359121014fe72d912000cff72d9521006bc645852023f7610d4910004fd71d9542016be62d094123e7e76d4a10006dc63d894102ebc40592102077441d954146edf51d8d541fdde739815402efa601812101cfc7358a40004fd73595100167e6254a50006df635814104e7c64551522267e76549501d67e6354950126ee62d895041cff7459542004fd75d9110004fd735974204ebe6419120005f77150941004ff735974004eef42588400bef661d854002cfc7655220005f771591521073f5250b40006f820d8141004ff7650650004fd75d89412277a201815225ebf655064004cfc7458254024fe76d952101cfc73587422aebe20d912019ef641d854204e7c5459742006df63d894123e7f62d4840006dc2158e40014fc74d8940016f8628811004cfe74d95401ce7f645494107d7c755852004efb70583422357c745815202dbe70d09400267e6555240024fe755884001cdc73595400075c63d954102ef7715862015eee42d89410667f5359610075de73d91200257d72d8152004ff7458650005f870589540075c631954100777615855204fb761d0941004fd73d95403b73d741954102cfc70595212adbf7450a401cd7e715815202ebf745925001cfc73d91510067d73d95100467c52d9510165de73981412fe7d63d4a4004cfe74d81510b67f51594400a6bf521912002eec20588400075c65d8d41004ff735891002cfe70d89101d57e731915238edd74d8d4104cfd74594400067c611815204e7f75597410067f20d951001cfc735974102cfe7058a1016d7c755894104e7f5458a540057d72d9541004fd71d954004ebf61d09411c5ef72591520167e62549402273f405484046ede52d8d54006bd30d91200067d43d951000cf471595200d67e65d9540036f52158620006ef7259542006de4158e400157e72d855204eec4258b40006dd6350a40006fb70595200b67d76d48400476f72549101567f53d952102df870506400457c755911002cfe705962004dbf7650b400f76f7254a401a6be63509400075f65d8d410077b7054a5027e7e70d951023e7c63d4a401fedc74d8d540067e63181522275d7318152006dc6358554006bc51d91201773d5250b41014fe72d814102edd4058e400067f65581412257f73981521367f41d95100367f52586202267e6054a1001cfc73d8154004fd75d89402067c41d9541006be65191201573f5495121004fd72d8540006bf10d91200e5bc72506400067c65581410247c755911038fd441d8d41005df73551202367f6554b40004fd72d911002ef410586400def6415864004cfd70d9540046f5515865004fb761551410fefa10d8141006f771595421de7c61d494001cfc73592500067f75586201cef621d
  | 12 => 0xf1058e4038f9c41d8d41006be761912025dbc70551411cf78105491023e7f62181520367f6254910006bc7459520006f761505400c67f5259220005fb70595422267f6354a4020e7f6299152004ff765512104ef771587404373d4219152006ef72595200077b7054b401ee7f51597412a6be3019120006bd64d0a500067c62d95101367d41d951000ef66154440015ec7255142006f9601814202cff7158440006df635494100df471481100bcff71591102bebf64d062000cfe71d89500067c72d954115f3d52509410247e76d9510006be65d9120006dc5158e40037f12188110006df63981541d67c6354910004fd73591200067c755844004ebc64d05500367d62d4910024fe75d81422657e76d951006df471595200067f73d95100b67f535944002edc1058e4038edd21d8d412357e7498152004ff73d855400d7471549510067e61191520a73e42548401cf3e4154941014fc76541202267e6054b4127e7c70d95101edbd75951412367f64191520067c76549400067e51597402073c41d95413fe7f635495101cde76d8d541d55c73581520def45158640024fe76d9520014fe72d815403ddc73551100377b52881101ce7f605491002cfe70d91521df7441d494109ef631584401be9c63d09410067f6555140006f561d06501de7e64d4b411067f62d4b400067d64d49100eddc73552401d57e73d9152024fe7558b410057f755055004cfd75d81540667c54596103b73c4119541006bd64191501d67e6354b400d6bd54592500077771581521867f52d85542367e6454a500067f64d4910004ff73d81510257c75505501367f31d9510005df7358141016fa62881101e67e63d491002ff3718811004cfc76547400067e30d95411cf3e4154b414675c54d8d5404cfe745865416e7f52d9541004ff7359250005bc74581520e6bd32d91201bebe63d0941006bd625044004ef74158740136f65158650004ff765454002cfc76552103b774411954112ddc73505500067c65d894125fb8705064001cfe73583420167c625495102cbc7650940014fc72d915004ebe64d09100067e74d951004eec42588400c6ec62589402257f7054a502267f6354840004fe7654540004fe7648540005f5719815438edc41d8d4100ff3604851002cfc70594401ae7c51d95423d6bf7650b410267c65548402267f6354a100067c76549410e4be76d09401567c54d95210067c61991521d65e6354a401cef631d855202ede7058e400073f64991521df3c41d4b410067f65d89410a6ef215884000cfd75d915107eed5258a5001cfe73595210edbc7350640006bd6419121006bf7459110004ff7358b412275e6354a402bdbc7055341006bd42d814100cfc72d8520004ff76551200067f6599110006de7558e400d67c53d9540004fd7650a101df7b10d4910
  | 13 => 0x4520014fc7259640004fd73d95411eef4615855401cfc73d895001cfc73d85540067e32d9510006dc20d8d5407e7c654811004cfc7654b410073f64591522276d6254a5002ef610584402267e6058152086f62158620004fc76549101df3c41d4941006dc73595411fede74d8d540667f52d8550005f77154a1004cfe74d95200473f5495110106ef2058b400467f54d95100067e62d95101357e7154a50075dc73551202367e7654b400257f7254950004ff70595420e67f52d9120014fc7259740006ef72591102357e74d855223f7810d4a10006dc71d8d5402df8705094001cfc73d915019cfd76991211de7c61d4b401fede75d8d54004ff75583410067f74d951002ebf4058840004f771595421367c31d9510006ef72591200257c7548650004fd7650910004fd764865000cfc71d91500a6bd211912002cfe76d81210e6bc4258a400c73f525094029efa20d81210067d76548402267c6354a401d57e73d855234e7d51d95210157d75d855204ebf711912004cfc7458a500367d525862004cfd71d8141024ff765514204e7c54594400047c76549411d57c73d855204ebf7019120007787054950004fe76951200055f7359152004fd73d89401cd7e71951521fedd54d8d540057d71d815204cbc74595201e67e63d48400057d7199152006bf645852015e7f62d49411767d62d4b410067e63981521e67e63d4a404557d73551520257e75d8552024fe7558b4000cfc7158a501067d52d81421cd7c7195152006ef62509410079f7355341004fd71d9152004fd76952200057d73981520267c65541400267c65549410067f655494102df87055110004ff7259540006bc631912004ef4415874202df870552402b5fb70595200157e72951520073f7458152006fb705912106eed2158a1023e7c61d484000ef661d06501767f62d4b4101cfc7359742004ff765491001cfc7358440006bf649912002df871881100257d72191521f6ec6258954004ff73d81421a6de6350a400077b705484000d7c765495101cfc7359740006dd70d8d54004fd76549100075c7358152006bc4358a40006bc41d91200067e51d95201cd7e76d8552014fe72583412273d405484002ede2058e40004fc765095002edd7058e40004fd76506501d67e6354a1004cfe76d912113cff7559520006df70d8d541d6dc63549412067d21d95410067c70d95410057f735815219ef451d8542006fb705954204dbf7250941005fb70591522376d729915201cdc73595422b57e7618152014fc745974202cff72d912001cfe735874204cfc745944002eef7258a10004ff71597420e6bf52d9120004ff7558342014fd71d81212b67d75d8152005df7355210006bc75d91200057771581520057d70d85520057f71591521ce7e6154950007b77150941006bc645412002ed
  | 14 => 0x4df73591212267c61548401cef661d85520067e53d95100067c73d951001cfc73595211cf7441549411f6ee52d895404e7c545974102ff01048110007af6250941004fd73d85400063f6499152005bc74595201ce7c6154940006bd31191202267c6054951004ff7158a401d67e635491002cff7058a100f67c515964000cfc7158a5404cfe76d9152014ff71d9121006bd6450a100057f7155152006bf6454120006bf6499121005bf74548401a5dc73585420a6bc32191201cd7c7155152004fd71d91203b5be769514101cfc73d89541d57c73d81520067f7559541024fd74d8954006df631815407e7c5358a50306dc4158e400067f65d8141024fc75d8941006ef725952127e7f71d95102ff3c43d4a4000cfe71d9152006bf73d91200267f76d49401aded729915216e7c6559541004fd70d9151004fd76546201d57e7395152006f771595410057d72195411f67f525954231dfb705855025ebf6450620014fc72d85400067f7654b400067c75586200057d70191522276e6254840006dc6359541006f7715951002cfe70d855200cfc74d85400067c65d8141006df5258e40126ee52d895027e7c40d9510006df50d8d411cf7b105491004cfd70d89401cf3c4154b410676f7254a1000cfc71d915200cfc71d8950005df735954202d7c705495002cfc765524001cfe735954004ebf60d0940006be6119120006dc63d814102cfe70d95100167c62d4b400067f7558742006fb6098141016ec625094004ebc64505500a6bf7650b4004cfe76d91101767d6254b410e73c42d4a400057d735915218f6c62549510167c62d4940014fe72586400d4fd76541401367e51586502277610549102067d31d954100cfc7654110466dc42d8d5400cfc71d9510006ef72589100257d72d9152014fe765514204efb7058341016ee6250a400257f72d815200ef66150640006df21d8d541e67c63d4b400267e655491000df471501100267c655494004ef771587420067f52583410057d739915204cfd75d89540067f65d0110026be659514100cfe7158a5001cfc7358a540067c32d95410167e62d4a40005dd7398141006dd65d8d4100ebe61d06401d57c73991523467f52d91211073d5250b401fedc75d8d540057d7319152007776548510006df7359741006df63d814102cfd71d951002cfc705874202cff71d91103875c63d494100cfe71d8954416be54d915101cfe73d9120004ff73d89412267f62548401cf7410d8552016ec624811032f6f62d815211e7d5159610004ff76509510c6ee42d894000fe772485101867f535974101cfe73d95210067f7654a4023e7f62d4a1002efb61481101d57e7398152006fb7059120024fc75d89402f67d6354a40466dc54d8d540a6bd521912004ebd76d064020e7f52d954204ebf4159742004fc765
  | 15 => 0xe76195101cd7e7119152004fd76d0a1026e7f61195102bebc40d85400eddc73506401d67e63548401873d74d4b4105ddc735521001cfe735921002dbe7050b40006ef6250940006bd65191200067d63d9510006fb7059510004ff71591200c67f62d494023f7a20d4a1001cfc735954004dbc745434006ff071481101d57e7399152004ff73d895100778654811015e7f625494100cbc765514104fbb40552400067f30d954104cfc7459510006dc735891002cfe76d06201ce7e61585522ff3e43d4a402267f65548401767f6254b4124e7c54d8954005df7358540006f8705912101cde76d8d41005fb70589411de7c51d895119fb471509412067e21d95410067e51d95400067f7654840005df7358950006fb7058910004fd7654a400d4ff75595400a6bf321912001cfe73d95400c6ee62d894004cfe74d9510004fd76d0520004ff7558b410067e42d951000cfd75d815146f9f54d8d5402ebd4058840004ff7259740024fe755912138edd10d8d411a6be6350b410075f635494102cfc7059640006df71d8d544476f62d9152006dc10d8d540257f72191522257e709815213eee5258a50005f771551100057f7458552006bf50191201567c6559521087f22188110005df735064034cff755952100ebe61506400e6bd21d912038ede21d8d4101cfe735961004cff76501102967d63d4a10165dc73581410057f7058552004fd70d91520e6bd52d91200067c63981521567c50d952146edd51d8d54466df42d8d5400cfc765094104cfc7654b400055d7318152026be655534102df8705484004ebe6419110005df73591500febf76504401fddc7358154005ef72541200167c62d4a1015df57199121016bc62d09410c67d525922016e7f50d95410075f63d4941006bc43d915000df471551102367e64591520277a6054a500067f659511001cfe7359510004ff7558840024fc7558a40004fd74d89511ce7e6454b41006fb20d814137f5c63549412373e6419152446be54d915202e7c5059610004fd73586500067f64549101df7b10d4a1004f3f75553410f6bd54d91500067d6454910005ef7250620004fd70d95420267e6554a10006bc63d9120006ec725911001cfc73d954201cfe73d8941004fd735952100cfe715962002cfd75d855015e7f52587421e67c63d494000cfc7159542006dc63981540367d62549101e67e63d49400467f52595102373e7454b4104cfe74d85201067f6254b400257d72d855207f3f549512001cdc735954101cfe73d915000cfe7650110004fd73d951002df87054b40004ff755922004cff76952200067d6554440014fe72d95200276f6255152006de7158e40115fb70591500a6be4258840006be4358a400079f7355141014fe74587420067f32d95411cf746158552037795288110005fb7050940
  | 16 => 0x550014fd75d81520e6bc32d912004ebe76951410276f72549510277b605495004f3f75551410079f73506401c67c65d0910004fd7655110466df41d8d54024ff765434001cfc7359542014fc7259741004fd7655121005bf745895002e7e505961025ebe40591101377621d951004e7e54597400067f72d95410e73c4254a40114ff705954016d7c76d4941004ff7458a100067d7654940006dd634864002e7c50594400167c6254b40005bd75d0941004fd769512002cfc7654440005df7350520004fd70d91210073d7454b41006f561544400167c625494002df8705521004ebc405874000cfc745834104dbf76504400073e7454941006bd641915101cfc73d9541005bc744811004ebe76d094046edc50d8d54004ff7258341006bf745891000dbc7650941006df635815400cfd74d8941227781054a10004df73595410167e6254a40006de62d8d5446ede51d8d541d67c6354b4020d7e7419152004fd7359610014fc725944004ebe70191201cd7c71191521267f5259520006f56148640004fd73d9121016f4764851004ef840583412257e70d85520057f7548650037e86248110004ff73d85421d67e6354a50024fe75d91102267f6254a100069d73d9120014fc725834100cfc76501102275e73181520f67f525964000cfe7159120006f810d81420077b6098152006bf3019120014fe72d85500066f62549510067f5258640274ff7059510004fd735862000cfd74d95411bebc63d09410ee9c7458e400067c7558742014fe76d89100267c65551101ee7d51597411d57c735815206cff71589100047f755874204dbf725094004eef7258b41004fd76d0550006bd62d06402f73c4354a40006de52d8d41004fe76d0950195de7318151014fe76d01201fdde76d8d5404efb405834120e7d52d95420067f755954204ebf4159440004ff735864000cfd7458440014fe7259740004fd73d855204dbc74484403e67d63d4b4104cfe74d81210067d52d85502aebe30d91201cf3c41549410a6be21191200067f7559540004fd7654a100067f52d81412067e6195152004ff73d8552005df7358152086ed21d89100e67d52d91200c6ec21d894002cfd74d954004ebe64d0a102067d10d95410067e70d95411ce7c6154b403ef9c7355341004ff73d95100067f65501100157c72951520c73d525094002ef77158650016e862481100147d75d855202edd5058e401276c6254950405f77158951006bc42d915002cfc7058650006be61d912002cfc70d9510006f731d85200077471591520057f7550640004ff72594400247e76d954116e7f5259541024fe75d85400267c6595121006df73595412047e7619541014fc72586402367e7654b4104cfc745952102ef771584400f57c755064000cfe71588400057f7559121004fd72d81410467
  | 17 => 0x2067f71d9541006dc7359741006ef32d89101b6f62158742004fc7648550004fd73d89541367c21d95100067d72d9541006dd7158e4002dbe7050940004fd74d952000cfe715825400cfc71d952004fb77150440004fd76506203367d6354a50024fe7559110004fd765464004ef741584400047f75584400057f73d8152024fc75d89100a6bd20191203a79c73551411cf7441d8552016be6250b40004fe76d05200e6be21d91202b77a20d8152005f77154b410073f52d0640004ff76485500067f73d954104cfc7458a1004cff76d0a100057f7550520004ff7558b40004fd735962004dbc74541400257d72181522067e31d954102ef6105862002cff705921002df6704851002cfd75d895004dbf715044009ef6515844002cfe70d915100cfc7458b4141dbf7459542004fd70d9541006bd65504400167c6254a1004ebe76d09410a5be72504402ef9c735064001cfe7358a501cf7b1054a103ce7f43d954115e7d525874202cfc7654a1001cfc73d8121014fc72d9110006bd65d91201ce74615855204cbe76d9120006bd31d91200c5f9709912002cfe76d0a50005f7715895401cfe73597401cd7e7118152024fc75d81412267e7654a4016f3d74d49412357f739515204cfd75d855419ded729912100ebe615044002cfc7058620024fc75583421f67d5259542016be62d0940014fe72d81512267f60981520147c75d89500056d7299152075dc73505201f4ff72595420067f65509100067d65549101dd7f7254910024fe755844007d7c755052004ebc64d0110016be6250b410073c75506400a6be52191201edf67198154024fc75d8121016ec62d0910004ff75591101ae7c5158a54004ff735922023e7e60d484028e7d6354a1000cfe71d8154014fe72594401cef651d85520067e53d95201367e41d95100a6ee3258840124ff72595200067d52583411ad7c755854223e7c50d89500067d53d95100067c6518141004ff73d95402276e6254a50004fd71d81520057e76d49410057d72d9510006df75d8d41014ff7648110024fc75d85422aebf649814238edc74d8d41024fc755891027e7c10d95100e6bf32d91201167d76d4b40006be6319120006df20d8d5404fbb6050940004fe76551100047d72d9510004ff73d8940004ff7358654006be43d9150006dc6318141036ec32d891001cfc7358b4001cfe73d855002efa601815400df47154a1026f741019510175f771591210047f7558620006bf50d912001cfe73592500673f549521000cfc71d81520057f735915204cff74594401d67c63549402257c731815201cfc73d95200067e535974004ebc6350b41004fd72d85541fddc73589540067e52d95411767f52d85420073d6419152005f77154110006dd6354a40006df63181411ce7e61d85520057f73d9152004fe765
  | 18 => 0xe74d8152006be3119120006dc70d8d54005dd73981541fddc73585540067c63d95100067c30d9541027776154951024fe75587421cd7471591520ad9c735044014ede634864023e7c63d48400067f75d8910004df73595201367e71d9510004fd76484400157e769515202eec2058a50005ef72591103de7d6354b4102eef7258a4038ede10d8d4101cfc73595410c4fd7650120004df73595400067f75595212257f7654a5001cfc73d89510cddc73585400067d64d4a10006be63d9120286fb7648210106fa20d814204ebe64d0a500073f5250640004fe76d0910004fd73d85202367c6454951006bf51191200f4ff74595400267f605495012ddc73589500057f735855201cfe73d81412bdbd70d06400bef710d854004ebe641915146ede50d8d54004fe769511001cfc73d8910005fb7055110004ff735912120e7f5258a5423e7c60d49411367f10d95100adbe73504400047f7559121005bf744864002cfe705865002ef41058650005bf7255341005fb7055240004ef72591101fede76d8d54004ff7558740004ff7458620254ff705891000cfc71d81420247c755874204e7e5459742004fd7359540275fb70595100073d745494127e7f6598151004ff765494114ddc7358121014fe76d894100cfe76d85500057f7458152004fd74d8151427792018152014fc725825404ef4415865404cfc74d9540006dc7359540006bc73d912000cfe71d95200057d7358152005bf74581210077960181521876f7254b4101cfe7359520004ff73d814101cfc73d9510006bf64d0550014fc725954002cfc7650620006f930d814204fac425514200cfd75d895102cfc70596102e67d63d49400067d52d81410c67f6254940004fd71d95200067f7654b4100cfc71595400067e5158a502257c7059152004ff7650a1002efa6018141004ff7358742005f8705894100cfd72d9121005bf74481100d67f54d954004fb7619514104ebe71191202f73e4354a400167e6254951004ff7650950004fd74d8520004fd73d89502277a2054a10006bd75d912001cfe73596402067f51d9541004ff7650550006dc63181540267c65551421ce7e515952102cfd72d952001cfe73d954102cff71d951004ebf6195141024fc75d91211d57c73d9152006df73595202aebc70d912002cfd72d91200bef641d854006ef431d85200079d73d9120006bf7459540024fe7558740016fa624821002ebe4059220006df7258e40014fc7259610006bf30d91200157c76551524675e54d8d54004fd73584400077870591520057d7119152004ff73595100e4be761912025dbe7095141006de72d8d4102e7e5059440006bd6250640024fc7559110004ff725864001cfe73d895404cfc765434002cfe70d911002e7c505962038edf51d8d4104dbc7454840004fd7359640
  | 19 => 0x91520067e765494046e5f52d8d54005f77158152006bc53191200276f7254a500067e53d95403577521d85522a6be1019120006dc75d8d411cd7d72d491018e7f62549512267e7654a1001cfc7358a5004dbf7555141006dc20d8d4102cfd72d8520007b87448110004ff725865002edd1058e40006be31d91200267c6555141396dc54d8d41396df42d8d4100dbe7150b41004fd735834202cfc7458740006df63d8954004ff7654440006bc71d912000ebc61d06401067d62d4b402267e60548400066d625484002ff0718811024f7b40d4940006bd425874002edf7058e40166de74d8d4102cfd705921002ede4058e401e67e63d4b41024fe76d95420073c7454a401fedc6355141006bf7459520004ff705865401cfc7358a10005df735514100cfd70d89100073f7550640014fe7259741006bf43d91200d6be545925019ef621d85421ccfd75d9521004fd73d814102ebf4058a400067c651911002efa6018152014fc74587420067f6319510004fe7655121004ff7158a5002eec2058a40004fd735834102df47648510006dc63581540073f7454a401d67e6354a40004fe765095100cfe7159542004fd74d81522267c63548401b5ef7259121005fb70589540057f7558141006dd7258e40005f771589500067d63d95412257c71981520263c65951410fef7105874004fba60d064004ebc731912016e7f53d9541005bf7458152006df63d8154004fd73d915216e7e65d95412a6bc3019120004fe76d095104ebe6050640024fe76d95100e5be7619120014fe72595402bf9d63d06400067f651814102cf476485100067d63195412067e10d954102edf5058e4016e7c53d954102cfe7059610006dd54d8d4101cfe73588400b73d74d48400067f75d89412a7ac2019120016f8624811046edf54d8d5443f6f62191520067d65549410067f76549400067d65952101767d52d8542024fe75d9120006de71d8d54014fe76d895402e7e50596201d67e63549400ee9f7458e400def62158640005bf725514104e7f7559740024fe75d854201cfc73d89400067d525864027e7e20d95102276d729815204ebd70191201ccff7159521026bc655514102ebc4059250004fd73d8152004ff73596402067c5158654006bd42d8540005dd73181210c7ac6250940014fc72d91200067e61981521267d525952023e7e50d895004ebc645011002edc7058e400267f76d4a401367f70d95100057d73181522257c7118152004fd7358a100067f6595121004fd73d81423f6bf7655341024fc75d8520004fd7695110014fe72d954004ebc751912004cfc76951202067d71d954102ff3618811004cfc7458a540067c631815202e7f75596100067f65d89101377810d95100e6be52d91200067d30d9510006bc7458910024fe7558a100067d6554a4004cf
  | 20 => 0xcfe71595400257e75d06500a67d62d4840016bc6250b410067f6559110006fa30d81421367c41d951016e7d76d4941005bc7458121006bc43d911006eef2158a10006fb609812125fb561506401873f52553410067f65d91100067e63d95100077b7054950024fd71d8151004ff715925004cfc7458650014fc725874000cfe71d89100267c65551400069e73d9120466de54d8d54014fe72d9150037f1214811004cfc76d095000cfc71d911032efa50d815202dfb7648210014fd70d85200079d54d8d4100cfe71d81523867d63d494100cfe71592200067c65991100e6be4258a400247c7558620007b77155141004ff76486500067e76549410467f52d951000cff72d91211d55e7318152014fe765012004fb761509412067f21d9541004fc765494123e7f61d4910014fc725865401cfe7358b41004fb705954223e7c63d4a1000cfe76551412a6bc2019120007af625094001cfe73596203ce7c42d95411167c51597404167f52d91512367f6554b4102cfc70595410147c76551522de7d6354940004ff745962004cfc76d09101377b10d951004cfe7459440006dd7458e40016be6250941004fd76d095102cfe70d95210067d72d9510004ff735954103ddc7358910006de5258e401efb47155141006df735911001cfc73582541d67e635495101cfc73596402b67f62d815219df47159542024fd70d85500377b5248110004ff7259250006de2158e4004e7e545944004ebc645512004cfe74d85523ce7e74d954127f7610d951001cdc73589100073f645515225dbf70506400167c62d4a4001cfc73586500067c74d9510016fa6248110006bd73d9120255fb70589103ce7f42d9541004bf7459520024fc7559210005fb70585420467e65d9510014fe72d9541466dc40d8d5416e7f525865402eec2058a10005df7359520006bf51d912002cfc764864014ddc73591210267f76d4910006fb10d814201cfc73d954004ebe6419150004fd72d9150006ef6248110006bf6450550014fc725951000cfc7158b4000df77248510006bf71d9120035ec725911000cfe71d91500067f75589101ce7e51d855216f6f72549413ce7c43d9541396dc42d8d4123f3f40d4a40004fe7655120006df7359542005df735915238edf21d8d4102efa6018151004ff7258654014fc7259210006dd70d8d4104ebd7219120004ff765452016d7c7558141006f721d85540067c20d95410057d75d0650014ec725911002cfe705921024f7940d484004cfc7648740466df40d8d5402cfc76509400167e62549501d6de6354a4038edf74d8d41005fb70505403167d63d4b4002cfe7058a5000cfc71592502073e519514100cfc71595202afac20d9120026bc76551410073d52d0640007b870509400067d32d95100febd74d8141006bf531912000578705
  | 21 => 0x5300800103f0008c701d00901e4b100000400901100516d0000010520010090530170167e62d4b400057f7558121024fe7558640006df6358941006f7715952002cfc74597400073f65d09411576f6258552004fd76d06200057d74d855223f7410d491002cfc705974200df47154b410b76f72548402067d51d9541004ff75591200067d5359610006dd72d8d4124e7e54d895415eec6258941004fd71d814204ef4415874004e7e5459741005bf74595201176f7254b400073c65d094102cfc7458b40004fd7359440006f5315865404cff76d06501a69c6350941014fe725921025f9d635064000dbe71509412e67f63d4940014fe76d89512267c76548402aebe10d91200267c76d4a4004ebd711912002cfc7058840005bf7454340004ff73d8540006f75158640024fe75d89100267f76d48400c6bf425922000dbe715514141e7f62d9152004ff71597400067d7654b41004ff75592100a5bc725044029dfb7058520006dc73595201557c7559121006dc62d8d54014fd71d912120f6e729515200ebc6150640004ff765522036f9c63d094100cfe76d8520004fc765511004cff76d0a501a6be6350941276fa10d8151006f721d8550006bf53d9120004fd76952100067c62195100267f62551522257e70991520e73e42d4a4004faf7250b412267f6354a5002cfc7648440006bc53d912002cfc76546400147e7695152004ff73d852004ebe6450910005bf74589100d6fa5058254004fd76d0a50006de7258e40165dc735514100cfe71d81420f73e74d4a40005df7358554004fd74d9521004bf74589102bdbc7050b41024fe755834125dbf765064002ebd4058a4004ebf6150941006bc42d911007e7c51d952002cff72d9520006df73591212267f60181520067f65589100073f65551411f6ee62d89540067d6454a10004fd7359220004fd73597410457e75991102bf9e63d06402267c6054941004ff765464000cbf7650640016bc7650941007bb7448110185f77159151006fb609815401cfe73594400079f63d0941014fc72d81411a5de73981420eede7458e403267d635495004fba60504400a6bf2119120004fd73d8910006f771595212257f7318152005f87059542006bd64d0910004ff745961004cfc745952001cfc73d855220d7d7299152126ef20d895004ebc72191200167c62d4840007bb705094001cfc73d81420077531d85520057d719815204fb441551413a79c63551410067f7654a10006de65d8d410d67f5258254004fd72d8151004ff73584400077b658811000cfe71595201e67c63d4b412aebc30d91200067f6555141006f7715911001cfe73591100067d7558a5402cfc7650a1001cfe73d891041f3f42d915202cfe70d85200067d53d9521014fd7458840004fd71d915002edd2058e4038edc71d8d41
  | 22 => 0x70050000031243100c300700424a02200007c497004006034a8711105613500000005f00500100000902900200020303d0cd01a0151ba04300031503f00402b01900f00201000005c0020020000120000005c301100900c00a02000300500702600002a02611400800300b00100002300d00000100200f0010084b701600806c0080010020020260181de00038c0010a90bc02500500400c00400001500009300103c07600a02814800300310b01009204400e00700000002300003703600703a00d00000401e02c09b01d01100100200401a03200012300800001300100000200400300000300a01900802b00500113300600100d01a01900100700007500b0000200480240140050930f200000004a00905202901e00206c02f02c01e00c0000040d301800300f01e0180dd00915e0030770080010060000073a00000831b00680b601f0021e600001700103507e00500000c01801a00400200200b03100002601000100d00209701b00401d00c0560020560bf00a0000130000a70390130f90000010210570220a400e33500900020001000102200201900d01a00500a00500400b00000b00000c00100800002a00301236900a00000300007301404f00004a00400300e00c03c08248608b03a00000900f00000c02401a0100090000640040ee0c500200a00100501300000003500000701b02d00608700206100000021c05600d0000c83b903500100901406100100000503b01103301e0260020000959bb00009e0190130060790030070000dc01700001b0000045c203700a00601e00101c00000c10800500403200302002329100e0c200000700001c01a04900000904e02b00201800401c0000a63770010bc07300000006c00808e00000201500200600d0080530b900f01100400100102a3e500601400902000c0000000000260000103cb0010024780000050030000060080030020280c000200e0130b70600e000000e00702501201408b00900000c02f00b00d00900300000008603d0e001900305001205101501700e00001001c01300200001300e00006c02402401e00e00300100500b00200000500300002602800009100200500200000001f00701100600000700104006700206a01200200700000706700900700700300600a00200706800001d01102400001b00000b00200000f11503c00000d00100400d00101b02109701b03900201100016000600400201d0021ea0030430c800900700a02f6ff01400000000101c12101000100107206600000000603e00701000000100000000100404e0190000f300c00b00900002800708154d1ed00f0d400a06700100800000100404400002d3f913e00e07b3d80040001cf01400304100502100001800904600c00103b023000005000001003003000109002003002e1b0000430020080
  | 23 => 0xd00002203102b00f0000000810180050030020010040000010221d30cf00002c00500100002708e0000a40010000470040010020e100307219c00101704025001700200000004016b33c0040c90350030700040100020000060e300000700701c06c00a00d10e00200403100000700000000f0070cd00a00b03211d0170020051860f102f0510020150070140003fc01000200414001a00800001200c17a0010240010690bd00000700b0020013c00fa00601301a00100a00f00003601504800100600400602e00306500500800002c00002800800100300c0740020000000b900d00400012904300d17902300100000101800517c00200100401600900100600400101200200100200e00f00014d00013713400101c0030050000da00001d00101003b08429f01b0240100000080190071c80c300002300001200900000003b00603901a00200200200000800200200010e0000000341ce00000100000300000000c8400000030301e500100000300001315800005307a00004b01400100000300007d00000a00000000200200b00f0b902205900700700600111128a0ff01002400801000201400010c00400800200019d00600106102e02b00b1450020080060870000060000000100130420000052e70000350000100140010560012a90000000530593a000800008f0160080f1013000bd00070000e500419a01500008400000202300b00b0342863200070020140000010180ef01300000711f00f01a08300000102203a06300d0040000bf1d403a03201900100002000501300703700000000702900c04200000003100500002000c00000400403501d000007bf604107300101083000800104200100800300108800000000902100001b11900800000201700000100000300500004903304c00400306502a0410d92b400403602501b00900a01a0000010121f701300600902100008300000a00b00100509000000000507a01c0082b000300002b00b01900000500500009503b00301600000404e0de01b4270000040060c700d00000400c06d00900000000901b0370050010280090d200808d00900900800400e00600000001700a00307f0120460030000000210410380190ae00c0030030df0340080060aa00100001600209b02000200004e00900700001001d3bf00200f0f111446d00124700fc4601900c0000f709001400000000000000a00100000300100100001602b0010000ab00007b00002107800002900200c00e00b00001200101700200000500000800000b00711e0000000050360000010090054ed00406c00600001901400400900200000c00000700900002a00
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8de8718d6055001a38e63aa82200023761c50d8d410243e42ae6b0e840087f855cf62504018f2403b2a48800297e0d7654a1000c5e422eda0a4000cd67118e605500147b09b2ca888002a7e117258e400047dc02e6b2a8400a6f825d952840090f90ab9ec4a000a3b209765511004c5f43e203224000a9c8359064544011bf06bb2a4200562fe1d30d912000c5e422e1b0a8434a9c8359142440011f70eb00c0909031d1c765551410052f418e5b2a200287d85dd9528400147908986ca88002b560420d8d410056cc04c3b1aa80587c87595521000147f0ab18c8900029e21530d81420047bc0aeca922000c3f429db5250401a6ee838ac0a90031ddc651596404662e3b6e6aa2a400a5f835935244001968e838aca90003175ce63981520046f43ec6b128200e6b62dc15254089c5a80b12a42000e37a1f73595400243e42ae7b122002aea86d8920440031e902b9ac89011a8f21176548400052ec1cc432a8200ab98408360504015ab02106c6aa0021fa1c65589100046f43841b1aa8038de86dcd605052357301318c89000335dcf71595200051ec24a2b2c800087d85dc162d04011bd0e086c6aa0021f61e631954100636b94a5b2a82008df835d954840e31bd0f216c6a080e37a0e76551100052fc1aeca968200c6c65dc960504892f100b9ac8a911b8b10d62548400043ec2ee7b024200cd963dc142900018eae2308c8a90028f61442d91500061ec3ec92a2a400c7465dc5204400317908bb682a80163d21d31584400046ec36e6a0c8044c5d7258f52900014df04b18ca8811f1ed8870591522ff0fc22c7a9480058f4874c5619400917d0fb22a8900121f21571d89402043f43c85b2a8226a76811cb654401317908b86c2a923697a1471d8d540056cc0042b1c8000e1f5394f64480011bf06bb2a9100028f215301912001536412c8a922000cd773dc565508011df04b9ac4880262f211735944046c6fc3aa8b1c8000d4f625cc6054801938e7b2282a80021fa1c65581414654f42041b1aa800a5e859cb635040b1f100b9aca90952aea0251191200063da96e0b2a84038de87dcd65480071bd073b282900031e48276d4910006b9b88e0b22a4008dd8708563900071b906bb242201c63721b73581410052ec1841b2a8200a9e8390b644402917f0ea16c0a08022fe1d64d091001c6fc3ae7b224000cf171d8260550011bb07ba2c5280034b1d372581520054ec1ee3b22400087e870cb654411b53b0838ec6aa002a7a0c71d91201fd2e42ae3b1aa892abb8059464480018d8e5b2ac88800297a0e42d9541006363a8e4b222079a3e841cb6550401acee5b8ac8a900297e0d6454910004b7c12e6b02a400c6f65dc95048081878edb2a84a08163b21d62484400043fc2ae9b122040a76811cf65504014f30a106c0aa00237a1c7359542
  | 1 => 0x906b2684880262fa1373d81520045ec26e7b02a24693c845c3615480117f0eb20c8a90029761770d8d4100746316c6a128200c3f75d9161480019b0c6382c4aa003171d4735891002e74382c490880a6e6461dc961548018dae4310ca880039a188654811046e2e32ee6aa22005cf0605c66055029d50c43a240880262f21173596200051fc2261b2a20738dc8758d41900011bb073b2a888002a7a0e7619120006ac39ee0b22a400e4f72d8d525048da58c8b94c8a9002b660c50d81420043fc3ac632a8200a6d829d952500014e902baac5280021fa18765491001c6e41aebb0a840387c8754d65d04e71bd0db9aa8a08021f61776509100043ec16eab0880008f7815d9544848187eedbaa832029f0fdd7745954204c5e422ed2a24000d5473dc5605489f4f70ab00c0a88173c1c1615064004c5f43ee8b1220008de8708363505335b700ba2c72017b471cd52506400145ec26e6b108000c76219db524400153b063aec89011f17dc96354a400061eba8ebb224000d2f645ca64548018dae4316caa08032e1d3705891001c6f43ee6b12200087d87c8365504011bf06bb4a8908128f219545494101c6f43ee6b2a820087f855cd65440291790eb12822000a1f617765484049c5fc22e6b2440008df835d954480090fd0fbaac4880063ea1b705511001c6e41aeda0aa0a6e6471d895254489cd0e0b12a4200121f21573592200046f438c6b128200ccc63dc96050401a38e9b9ac0a900353d8b735915224e1fb10e8b02a40287d85dcf615488f8bec4b98c0a900e1fe1d53d95210046f43ec6b12a800a6f8258f65440011bb0e106c6a0803361cc70595420062eb9ca7b2a4000cd763dc56255001c5ee8b12a4200121fa177458a100052ec2e43b1aa872c9c64dcd41480f3878c9baa82a8002a720d65191200053ac0ca7b2a2000c9c74dcd62440018dae4316ca880030f61f64991520066cb9ec13028403c9e73d0f64480c153d093aac7200ea9720d6554b410054f41eebb22400087f855c362504011bd0fb1ac2aa0023be0973591100243e42ae6b1220098be84dcf605440b1ed0db8a40880031ed9770589410145ec26e7b2a84008bf8759064480018b8ebb9ac48811b8bd0562548400064e39ec8aa24000a9d84085639000717f0ea1ec89011b4bd0572991521fc6e436e6b02a800c74411d952504051d904b9ac88811b8b1d162548400046f438e6b2a403997687dc5645480517908b9ec4a000327dd073591100243f42ee7b028400a5e859c563900011bd0e39ac4880028f610619915254e4fba0c6b0aa839a3c865d152504018ee823b2a4a08021fe1571d894001c6e41aebb0a4000ccf63dc960504014bd0730cc0a90031d48476549100047dc3ac0302a8058bc8759142840014bf06b2aa4a0003175ce631815201536412c9a922000
  | 2 => 0x27158e400054ec2041b1aa83aa5e86d8d525049717b0fa16c0a0803351cc71595420043ec2ceca0a4000c77761c560548018baa5b9ac4881028f61370d95410062eba8ebb1a8226a79801cb654400157108b00c0a90ef0f1d35258341006a7b16e6b02a400d6772dc560548018b8e7b2aa8a0802972157458e400053bc0aeca9220008fb875806054801c38c7b2a84a08024fa1f52506400056cc0043b1aa8058f8805cd6448401938e6322c29000237e0d76506500062e398cab122044e687058952940070ff0ea9eca880028fa1232d951001c6f41ee8b14a000c3c75191614800117f08b9acaa08121f215765062004c5f438a23224000d5773dc560548018bea5b9acaa08021fa1e42d95100052fc1acaa928200c3d421d952504090f90ab9ac8880028fe11659521000716b12a4a0880a7c3d72d9264548754b906b2aa4a00262fa137358b400046ec1eeab0c8000c5f52dcd644842b93ce139ec890002a7e117158e400054ec2041b1a8200a5e83dd365440018ec423b2a4880039918b654851001c6e41aecaa42000d4c73dc960548018bea5b9acaa10031d5977154b411363a38ecaa82200487c855cd64484011f700b9ac89080a1f21d6554b4046ea7b16e6aa2a471ad6810836350401cd0c5b2a408800e3720d76506500045fc22e6b2c4000c5c7518d605048d47b0fb24a8a90031d5c661991521ce1e3a2a4b068200d6762dc560548014df04bb2a5a0156aee1160181420accf43ee6a088000ceb721c16448401976e8382c8908031b5c862195410063c3aee0b224200a9d8318464480011bf06ba6c4a88121f21476549100047bc0ae6b122000c9f875cf64480752bd0fb9ac0a90262f21076505203b61e3b0caa128200cd4635c6605509b8e8ec32a42882329761472d8d540065dba0e0b2a8400c7b751c1644840517b09b9ec0a1002a7e0d65191200051fc2a60322400087f855cd64485290ff0ab9acb1028b8710463195410062e32ae7302825fd1c73d494190001998e6392c888003175cc73d95412361f2a6eca968290cbb7019161480f30ff0abb684a89125e20173585520051ec24a5b2a8200b2d829d1525040156f02b28c8900028fa1731191200062fa96e6b2a804fa75811cf654400b1d90e992c4200262f21173584400051ec26cb2a24200a5d8390b6544001938c9b9ac290002ae20164191520045fc3ac83224200c5d52dcd6448401878ea3a2c48800a1f21d6554b410145e43ac8a1220008ef825d942440018beea39ac88800317197735891004c5f426eca8a4000c5c73d9554500af37100baa85a0802a7e117558e400064e3a0e6b122000c5d52dcd655080153b0f39ec8900025de0573591520043fc2ae6b2a8200c5c75d8d605040b0f90ea9aca200021f61e63195104664e326e6aa24000c5f759d5639006f53
  | 3 => 0x5b2a2000c9f741cd624400165f04b20c8a90023de05765484016c3ec38c5b2a8200c5f751cd6448401878ed2a2a4a0803179cf659814100637b2ee4b222002a6c87d8952540011ef02bb2a89000336dcf7059121006363aee4b222000a5e851cb635040117f08bb2a48800297e157458e400052f41ce1b2a82008bf8759464480018becbb9ac0a08029be097654b410062eb9ca7b2a8200a6d821d762440011bd0e10ac720002976142158e400052fc1aeca928000c5c73195605040b0f90eb2aa5200028f21163195100061e3aee8b122000c7451dc562951398bae5b1ea4a0802bc60420d81540063bba8e2b2a4057ab88050960d040555904b2284880022fe11735912001c6f41eeab0c8000a9d83dd764480014bb07ba6ca880025ee1d601815200536412c632a2000c5f52dcd6244001a9ee7b92c0a900297a1770d8d410052fc1aeca908005ada800856390001878ca3a2408800317d9773551100243f42eeca1220038dc835d9544800187eca3a2c488002ade0563191203954f420ebb1a8200cf071dc165508014bb0b906c6a089a1f21d30d95100143ec2ee7b22a400c7865dc162504010fd0e32ac4a08063d205735952002c3e43acaa888000d3b75dc14190001a98e7b92a8a90023ee0173595210046f43ec6b02a800cd4731c5654800117f08bb284880031ddc461981520054ec2043b1aa81ccac72d91404800147b09196ca8823717d8b73551520062eb9ca7b2a2071a9d841cb63504019b0e7b82c890803171cf655891000cda40aeaa16820087d85dc562d00018eea5b8aca900028f61062195100062e31ceda92820087d870836550401ab0e6382c8a900297a172158e401e52f436c7a92829bc5f72d8d525040117b0e28ec890003179db63d49410045fc3ac8322200087d8794d62940054f50db82a4a811b0fddb64591520062fbaee6b224200a3e85dc764480014db05baec4880021fe1573d89100043fc3ac632a2000c6c65dc96444001acec5b8ac8a90031754b73595200061eb2ee8a948005cd87058d429000153b0638ec8900030fdd764505200070e31ecba128226a7980dd36544001a98e7b92c8a900355dcf71591520443ec38c5b2a200087d85dcf60504018f4413b6a48813e1f21b75589100063ab88c2302a40087d870cb655040b1f100bb2a890802a7a0e42d91500063a28ee2b14a000c9f74dcd62440054d905bb2a4200262f21173586200056b40841b1aa80487e87dd56444001a68e838ac0a923a1fe1d30d951000574412c0302820087c874c365504018becbb9ac488232a7a1072d8d540064e39ac4a088000c5c73d9560504011bb0db9aa92012e6e201755094138e4e3b6c6a128200cd47118d62550011bf06ba6c0908030f19474589105261fbaee8b2a824fc7476d9521440014bb0b396c6a0802a761
  | 4 => 0x44811b4bd0a106c6aa1c727ddb735064001c6e41aeca922060a9c845d563900130fd0f29acba00021f61c42d95100062fbaec6b1282008bd8798c64480018b8c6b96caa08022fe11735954000667b98e4b2220008bf875906454001c3ea4b9ec890002a76127558e4000c7a40aecaa2400087d8790b655051b1bd0f216c6aa0038dd04619915201556412c9a122000a6f82593524400153906b20c888002b66024158e400043fc3ac8a92203aa5c835955250401aa8e638ac0a913e1fe1576544400043f43ecab122000c3d841d952504014eb0b90ec2a800a1f6177654a400046ec1ceca0aa00487c855d92110001aa8e638ac8a90028f21530d91200063bbaea2b0c80008bf8758c644800117f08b9ec4a880317dd773591100051e42ac7b224060a9e849c563900090fd0bb9ec0a080297a1662d8d413054e422e2b1c8000c3c65dd162440894f100bb2a4a08029de0576549410045fc22e6b2a401c8bf8758b41900019b0c7b82c4a0802a7a0e51d91200062eb9ca7b2a8076c3f761d541900018eeea38acaa100e3720d76486504c46fc3aa9b1a82058f48758551100019aee638aca9011a4fa1373d81520046fc1ae9b02a460a9e8408563900010ff0abb2a8908021fe1d64d491038c6f43ac6a0c8049a6f825d5629507f4bd0b396c6aa0031dd4b715954251d1fc22c632a8200a5d82d9763504014bd0a106c6a08038718c655094101c6e41aecaa2428ca5d85dc363550071b906ba6c0a90532e1d874481102ce8e39aa4a088000a9d8394464480014bb0b906c6aa1331e1d8654811000697b26e4b22a400c757194765508019b6e7b82caa10034ed90705915200636396cab028200ab48158f644809f0ff0abb2a3100024fe1d64191520047dc02ecaa2420087d87c8365440014d904b1eca880121fa1f755874201c6e41ae9b12200487c855cd61100019b6c7b82c4a08029b60a7654941006b5b96e0b22a400a6f825d9524400147908b1eca88002a7a0c75d912000c3ec2ee7b02a2008dd8790b635500187eca3a240880021f61c32d95100043f43c65b2a2000a6f8259152440011bb0f28ac720003175cc61181520046ec3843b1aa839a7686d85615480165f04ba2a5a0802a7a0c61d91200074d200c63028200b38805d152d051f976ec3a241080030fd0876549410063d100eca92200087e869d9524400167100b20c8a900297a0e61181524646f438e6b2e8200a6f825d9525000153906b20c8a80038754973d912001c6e41aeca942000c7461dcd61548031ed0fb8aca9000317dd463589410043fc2aeda122000e6962dc152100090fd0fbaac31000317d4b735952002e6c302e730284008dd83dd162840050f90bb92ca88002976177158e4000657ba0e4b222000a6f825d9529004d0fd0f906ca880023760e76505200051ec20c
  | 5 => 0x800317dd773595410243f42ee0b1682008bf845d954480012790ea92832011b8b5cb64991520045ec26e7b024200a5e8390b654400157308106c0aa00327dd373595200045fc22e6b222039b34815d152d04011bf06baec2900062f61370587422ad5d400e3b2240008dd879cf6448001ad6e4382c8a90062f2117358341006abb98e2b02a426a76811cf654400127d0fa9282200021fe1576549100062fb2ee6b12824fc7870d9554440014bb06310ca880031ddd871591520046fc1ae9b12a000a5d82197635040b1790eb2285280023ee0176551200046ec1ceda0a40018bd84dcf605040147f08986caa080a1f6177654b400053b40cc7302a400c74755854190001ae0e3b82c8a923697a1721d8d54004b7c12e6b0aa400c5c751cd64484754b906bb2a4a0003271cd62506400070f3a0c632a8200c5f7558d41900090f90abb684880e65d20573581524c46e43aa8b1c8000ce872dc1644400117d0fb22c2900031b60a76549100045fc22e1b0aa40087c87549611000147b0b988c8900038718c65d094100637c2ee4b222000cd463dc5625512fc3908b1ea5200021fe1576509100052ec2841b1aa800c3c75d91414812dc3908b1aa5200030f54b745891001c6f43ee6b2a84008f7815cd65480090f90eb26a488072ae60071d91203054e422e4b1c800087f855cd61d08018bcebb1cc0a080297a0e51d95400061fb2ee8b12208da9d841cb63550019b6c7b82c4aa0032e1d370595200062fbaee6b12200487c855c362504050fd0fb2aa4a000e37a0e76d05200065bba6e2b2a4000e1f5394c64480019a8e7b8acaa10121f21576509102061e3b6caaa28200c5d75d8e6050401a38e7baa8320003175d463981410063db28e0b128200ada8008763550014eb0329ecaa0803275ca73d91200046fc3acbb1a820087e870836550401ccec5b8aa4a88039a58b7054a5000678388e0b2a8400c9f741cd65480f34eb0239ecaa0803171cf65589412a6d8080e89022044e2f405895210001c38cb2a6c6a08032b18874589100063c3a8e0b2242038de87dcd644400157300188c89000237a1e5158e400063cbb6e0a9680008fb805d942440011bd0e10ec6aa0532b18874481100046ec1cecaa242098bc845cf625440167100ba2a4a09e68f21130d95410059c422c0302a400d67721c560548014bb06396ca8800e37a0e76551201363c3b6ca90220a8c9f7418d60550b5a38e7a928220002a761310d8d5400597c12e8a928273c9d7418f605041317908b9ac4880031d5d561d065000c5ec26eca0ca000a5d8508363504071bd0db9ac0aa0268f21153594400046fc1aebb0a8000c6f751c9644400517908b9acba100237e0d765512138d4ec26e1b1a8200ce8621c1625040156902b28c89000e37a0f76549410045ec26e7b02a41d8bf874c06
  | 6 => 0x61fba8c8b0a4000cd7635c660550014bd0b212c7200262f21173595210e45f43886b1480038dc835d761500010ff0ab9ac31000297a142158e400046fc1ae9b1220058ec8758952100018b8e7b2aa88800a1fa1f65549410062fa96e6b2e82008ef825cd65440010ff0ab9ac910232a7a1021d8d540a55741486b108000cd671d8e60550014df04bb2a4a080297a147258e400062e3a8c6b1282038dc835d362540051d904b9aca88003171cc655911000679b8ee0b2a8400a3d84986645480317d0fb2282a80a25720d75d06500063bb88c3322a49ac9f7418d605044d8e8e3b2aa88800297e1571d8d540064e39ec8a0a400087e8754961100f347d08106caa08028fe1163195100061ebb6e8a94809de1d84197635049f4f500396ca880121f21573583420043ec2ee7b02841cea862dd1204400147d0b98ec890002ade0565d912000c5e422eda0c400087f855d941880018b8ebb9ac89080e37a0e76551214654f420e3b1aa80487e85dc562900032ed0fb8aa4a880297a0e5158a503cd1fc2ac8322a20587c875955284001ab6e7b82c8a9003171d463d89410062e3aac6a0c808da5e851cb635500127f08b86c2a900e3720d76551100062e318eca928200a5e8398b65504010ff0ab9ac8880031718e76549410055c402c83224200a9d841456390001958e9b92c4880022f61f10191200052ec18c5b2a2000a3d841cb65440014f700bb2a4a08031b1c8655814100c5f426eca9682038de83dd162840014ef02bb2a4a000297a177158e400046f438c6b12a80087f855cd60d0401998e7b92c488002976164258e400a717c22c4a9080058f48758521900010fd0fa92c22000327d9373505200053bc2a62b0ca8008bd87144644814b93ee831acaa08029e60263981520062e432e6302a439a74815d952500014bb07216caa08029d60652d95104fd2f430cbb1a820087c8759152440754b906bb2a5080163d21d61486500063642ee4b222000c3f751d162440050f90ab8ec4a80029761462d8d410054f41ee3b224000a3e841cb6544001998e7b92c8880121f21574d89100061fa96e8b122000c5e7319660504014bf06b2aa5a080237a1c63581410052ec2843b1aa800c5c65dcd60504018beea39ac488002a7a0c73d912000477c12ecaa22000a9c83597644800187eebb2282a800327dca73d91200062e3b6c7a928260e1e54d5163900019b6e6382caa10d2a7a1b63509410053a40aeab14a80587f8759654840130fd0fb2aa888003179db63549410145f424eda12200487d821d9525040187aebaa6c89000a1f21d655491000c5ec26eca0c4000a77815d952100012f700b9ac2a90e65da1f71581520045f438c8b0a40008dd839d954480018eecbb8aa0880021f6177158a4001c7bc3a63b0aa400c5e7518e605040147f08bb2a48
  | 7 => 0x5d731cf65440018baa4b9ec8900022fe1173d895000637b2ee4b028200a3e8418b654400187ecbba2a0a00028f61061191520143ec2ee7b02a4018f4815cd655081317908b9ac12a0022fa1c51d91200063a32ee2a1282008bf8759064544014f700bb2a4a00121f215735862004c5e422e6b2a400487c87d49611002917d0f21ac42000237e0d76506200046f438e6b22203cc5c7518f625507387eeca9283200029761662d8d410063ca96e0b224200a5e85c8363504018bcc7baa83201caa7a1370d8d410062e398cab128200c5c75d8d6250401a38e63aa832000237e0d76486500245ec26e7b02a84fc5f655cc60544010fb05baac8908028fe1563d912001c6e41aeca968254aba800c4644812bd1886992c420003331c86358141006d8388e89022000c5c76d8d525040155904b20c8880063d205765484001c6e41aeca122000c5f75d8d6050545c3c82318caa080237e0d765491004c5e422e6b2a2000c76101d952440018beea39acaa08163da1b71551100046ec3841b1aa800c9c73d9161480071bd073b282a80722fa1f10d91200063abaea3b0a840087e87d95625040147b09196caa08031b5c872d954104c5e422eca9220038dc835d36054401878ebb22c29000317d9773551410069bba6e2b02a400d6b62dc1645480153b073b0c8901e68fa1232d954125d5c40285b0282008fb8758060504752b906ba6c0a90029760e70d9541006aa39ee2b22a48ca5d851c763550010fd0fb2ac8880035c1c470591520045fc22e6b2a420087f855cf62500754b906bb2a4a080237e0d74d81510043f438cab2220558bf845db414800193ec9b9ac2900025be0973591520046fc1aeda0aa000c9f64dcd54480018beea31ac0a080e3720d74d81210051fc22c7b2a2000a5d851c963900090fd0b3b2829000e3720d76506200051f420c432a203aa5c8359152440131790e980c890003171d4735911000697ba6e4b02a400e6b621c15254001958e9b12408800a1f21d65549411bd4f436c7a12828da9d84dc363550090ff043b2a4a08025de0573581520062e31ae432a8200a9f835976448001acee438ac8a90031d18573585520055cc04a23224005ada8090563900011bf06bb2a8880022fe1173589100043fc16eab2242038dc835d952100014db053b2a4880028fe1530d91200043fc2ae6b224000c9f741cd65504752bd0fb9aa8a90021fe15735954001c6e41ae9b12a2008de8718d61550014bf06bb2a4a08024f61373d81522043e436eab028200c5c73d9564440050f90eb2aa4a000257e0d74d81520047bc0ae6b224040a3d841cb65504754b906bb2a488002a760c61d91200066c398e0b22423a95e87dcd64548014f30128acba024ea7e117458e400064e3a6e4b1c8000cdb631c162550070ff0ea9ecaa080347dd073581520
  | 8 => 0xf32ec6a0877271c273d91200070fa94e7b224000c7576dc552d04090f90ab9ac1a08031edd770591210243ec10eca9220028bc845cd61d08014bb0b90ac72000237a1c73595400043fc2ae6b1220018f687dc565508014bd07310caa08031bdd772591100062fb9ca6b2e8000e8c63d89425053d8bcec32ec6a08032d1d371595200063a3aee2b224200a3d8494765508031790cbaa84a08021fa1f65581410045ec3e21b22400093c8754941100090fd0bb8ac5a00029b60875d89412351ec3ec9322a44b8bd87d9340440090f90ab9ac89000237e0d7654a100055c422c030242098be84dcf605047347d09bb2a5a08029761642d8d540061fa96e8b2a4000ccf73dc9644400117f08b9ac3100022fe1173d89100052f42c85b1a8200d2f62dd160548018bea4b9ec8900062f21176d065002c7a43ac29088000e2c62d9542504018beea39acaa00121f21573d894104c5e422e7b122014e2c8458952100071b906bb4a890a8297a1665d8d410071721ac4a908000a7685cc761480090fd0bb9ec0a88163e20173595421ccba40ae6b22a40087f855d921100014bd06316ca88003271d073595200064fc22e7b224046c3e74dd952d04011bb0e086c6aa0032ddd0715952001c7dc3a61b028400e1d529cf6448001998e5b1ac0a08021fa1e32d954104c5e422e6b108000ab78158f64480018f0ca382c4a08034e1d360581520143ec2eeca9682098bc845cf62540c153d0828ac7200023ee1d60181511de1fbb6a4a0c80018be87d9141480011bf06bb2a5a08030f19774481100043f434eca92820087d878cb65440019b6e6382c8908028f61642d91500052ec1cc5b2a8200a7585c876155001ae6e3b82c8a90024fe11735815238d4e432a9b1a8200c3d52dd1654808f4df04baac5280121fa1f75591210043ec14eca922000cd471d8d62550014bd06310ca880028f61771d91200068e39eeaa088009ab4844c561100014bd0a316c6a0a3697a1720d8d540066c318e0b12820087f855cd61100014bb0b216c6a09e70f19375505200053ac0841b2a8200d5b731c1645491953d09b86c6aa00297a0c20d95410062e32ee6b2a8200cdb631c162504051dd0fb92c888003271d373595200063a080eca922000c6d829d952504018b8cbb9ac4a08ea5de1d31d855238c6e43aa9b1a8200a6f825d952100391790e986c8900022f61e65191200052ec2ce4b1c80098be87dd165480011bd0f212c7200030f5d074d95100068fba6e6b02a40587c8754d658409f4eb02396ca8823697a1770d8d54006a7b9ee4b22a400a5d859c563900014bd0728eca900030fdd774589100043f43e41b2a8260a9e849c963900014b906baac528287179db65d8d411e52e41ac9a9220008de87d8d60504019e6e2382caa10021fe1576551103970f2a6a9b1a8200c
  | 9 => 0x120240583500000030004002000203390103f8160610121043e0130044e00001500400d6c00402219c3e80100000c0006800c0100081002e1001904e092020144330240440280109625cd880e07c0201801301404c1a00218a0040001701601c0085823406000010092380018becbb9ac8880025ee0173591520062fb2ae73028200a3d85cc7644800156902b2ec89000237a1c73595410043ec16eab222039a74815d952100010ff0ab9ac1a100393dc96354a403954f420e5b1a8200c75219db52440011bd0e39ac8908022fe1173595100051e42ac6322400087f865cd60548018b8ebb9ac88824e2fe1173583413954f42041b1a8200d57731c5645480187a853b6a4a08024fe1173585522351e422eca92203aa5c835d952d04018eecbb8aa8880033618f70589540143e42ae9b12a000a9e8394464480011bf06bb242200121fe0876549100064eb9887b22400287e87d95524400517b09b9ec2a1002ad20563191200243f43eeab088000d3474dc56054801a5ec43a2c0a91129e20176548400045ec26eca8a4000c6c7219564440090f90a3b282a8002b6a0261d8d54006a7b9ee4aa2a44693c845cd60548015b306086c0a10021f61e42d95100062eb9cc2302a400c3c769d152504090fd0bb9ac5a00028f6125158a540066a39ee2b1220008df835d942440019a8e7b8aca9000317dd4735952038d4ec20ebb1a820087f874c365504018e8ebb8ac4880023ee1d60181422053b40841b2a8200cd873dc165508af1790ea12c1a08021fe1573595200053b40cc6302a400a5e8394565d003b33d0fb9a832028b875d063195410143e42ae7b12a00087d8718c605491b938edb9aa8a08029b60b75d89410064fba0e6b2a8000a9d849c963900018f2cbb82a5a00029760f76549411d52e41aeca90808ca9e84c43635509f4eb03ba6ca880021f6177458a100046ec1eeca9282038dc835d9548800153b0728ec8900121fa1773d81211d52f41eeca928205ce87058952100071bd0fb9ac89080e3d21d31586540052f42ce4b1c8000a5f835d9524400193ae621ac52023697a1421d8d540e65c3b6e89022004a6e87589521001317d09b9ec090802bc60420d81410062e32ee6b222000a9e8318464480018beec39ac0a900a2f21173583420046f438a1b1a8200a5d859cb635500187ecbba2408823697a1642d8d540253643ac4a90800087e870cb655040b1f100bb2a4200035ad8870591520043ec2ee6b1680038de87dcd65d04010fd0e216ca880023de0573595420063da96e0b224200cd7731c565508011bb0f216c6a0803471d073581520051ec2041b2a828dc5c65dcd54504011bf06baec2a100a1f21570d895102c7c402ecaa420058f8805d921100010fb0f196caa08029761472d8d412349e422e6b0aa45ee1f8458d52900011bb
  | 10 => 0x20f2000028050de0000600002c13c1b01400c218658070000089d8130180080100203a2280b0b4048190018010100000800308a230298360b62b47a80104a000028650000301b80014239000010016078688a80000000601600000c0c0000380000180f016064000c300a0640202a01800c3980d0422f00281702a0340500100a00c0b00200e0700482700c020000072460240381c1a41240580b004000058110020000105314613802879004000038100480040587f13e0840280a286010008000340ac55a180a40480081b0141a02603504c07c000350060cc000062600200007a0020ec168e3160040718110000180901700c090008ce002004000000000c401800000004000140380005081208a02404803034014018020020000180603201006801050174718000780ec0080f02202800005142004008030020380000200017804000038000000001780082480100000001001004008050130041b80580a010014d300c0060200f00300801c03043046008090490a60000000b0120002306722a048048032720504001e1ee1140002001800000033008284230020440fc118190140201908b0780b40600002a5d80502d0000e40d00a00000000039004028128010021e01380300008c000070040b4280210120042f00b0320f00100401e024000180180540100400a18c098040000186a01800c370068b317c3002600901e0080a8000962080001f00001c078000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x10407400061c200615cd615480105f985ce61181520041de6176dc552d040146592040765491000718485201d95244001c0c7358952504400060d210615cd615480185573a066318152
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x6
  | 5 => 0x1
  | 6 => 0x94b
  | 7 => 0x94c
  | 8 => 0x94e
  | 9 => 0x5
  | 10 => 0x124b
  | 11 => 0x124c
  | 12 => 0x124e
  | 13 => 0x98a
  | 14 => 0x98c
  | 15 => 0x98e
  | 16 => 0x128a
  | 17 => 0x128c
  | 18 => 0x128e
  | 19 => 0x10a
  | 20 => 0x10b
  | 21 => 0x10c
  | 22 => 0x10e
  | 23 => 0xa0a
  | 24 => 0xa0b
  | 25 => 0xa0c
  | 26 => 0xa0e
  | 27 => 0x130a
  | 28 => 0x130b
  | 29 => 0x130c
  | 30 => 0x130e
  | 31 => 0x180a
  | 32 => 0x180b
  | 33 => 0x180c
  | 34 => 0x180e
  | 35 => 0xa4a
  | 36 => 0xa4b
  | 37 => 0xa4c
  | 38 => 0x134a
  | 39 => 0x134b
  | 40 => 0x134c
  | 41 => 0xb0c
  | 42 => 0xb0e
  | 43 => 0xb8b
  | 44 => 0xb8c
  | 45 => 0xb8e
  | 46 => 0x184b
  | 47 => 0x184c
  | 48 => 0x184e
  | 49 => 0xbcb
  | 50 => 0xbcc
  | 51 => 0xd0a
  | 52 => 0xd0c
  | 53 => 0xd0e
  | 54 => 0x188a
  | 55 => 0x188c
  | 56 => 0x188e
  | 57 => 0xd4a
  | 58 => 0xd4c
  | 59 => 0x1a0a
  | 60 => 0x1a0c
  | 61 => 0x104a
  | 62 => 0x104b
  | 63 => 0x104c
  | 64 => 0x194a
  | 65 => 0x194b
  | 66 => 0x194c
  | 67 => 0x8a
  | 68 => 0xd49
  | 69 => 0xd4954
  | 70 => 0xd4d
  | 71 => 0x1a09
  | 72 => 0x1a0954
  | 73 => 0x1a0d
  | 74 => 0x150a
  | 75 => 0xb89
  | 76 => 0x14a
  | 77 => 0x2c9
  | 78 => 0x198a
  | 79 => 0x14c9
  | 80 => 0x4b
  | 81 => 0xd5254
  | 82 => 0x1a1254
  | 83 => 0x138b
  | 84 => 0x409
  | 85 => 0x1609
  | 86 => 0x198b
  | 87 => 0x1849
  | 88 => 0xb8114
  | 89 => 0xd4114
  | 90 => 0x1a0114
  | 91 => 0xd4a14
  | 92 => 0x1a0a14
  | 93 => 0xb9314
  | 94 => 0xd5314
  | 95 => 0x1a1314
  | 96 => 0x9cd
  | 97 => 0xd5814
  | 98 => 0x1a1814
  | 99 => 0x138e
  | 100 => 0xd4a54
  | 101 => 0x150e
  | 102 => 0xd5354
  | 103 => 0x160a
  | 104 => 0x148b
  | 105 => 0x164a
  | 106 => 0x19cb
  | 107 => 0x14cb
  | 108 => 0xd0b94
  | 109 => 0x188b94
  | 110 => 0x40a
  | 111 => 0xd4b94
  | 112 => 0x1a0b94
  | 113 => 0x18ca
  | 114 => 0x144d
  | 115 => 0x58a
  | 116 => 0x104b94
  | 117 => 0x194b94
  | 118 => 0x74a
  | 119 => 0x2cd
  | 120 => 0x1a8a
  | 121 => 0x14cd
  | 122 => 0x28b
  | 123 => 0xd5854
  | 124 => 0x1a1854
  | 125 => 0x105854
  | 126 => 0x28e
  | 127 => 0xd4bd4
  | 128 => 0x154e
  | 129 => 0x140e
  | 130 => 0x148e
  | 131 => 0x1a8b
  | 132 => 0x14b
  | 133 => 0x8e
  | 134 => 0x74b
  | 135 => 0x40e
  | 136 => 0x160e
  | 137 => 0x104d54
  | 138 => 0xd5054
  | 139 => 0xd5954
  | 140 => 0x1a4d
  | 141 => 0x18ce
  | 142 => 0x14c
  | 143 => 0x10053
  | 144 => 0x11393
  | 145 => 0x109d3
  | 146 => 0x11993
  | 147 => 0x1789
  | 148 => 0x17c9
  | 149 => 0xccd
  | 150 => 0x130d54
  | 151 => 0x131a14
  | 152 => 0x58e
  | 153 => 0x131814
  | 154 => 0x59312
  | 155 => 0x18da12
  | 156 => 0x18cd52
  | 157 => 0x758d2
  | 158 => 0x74592
  | 159 => 0x18d952
  | 160 => 0x18c752
  | 161 => 0x194592
  | 162 => 0x58752
  | 163 => 0x75792
  | 164 => 0x1a9952
  | 165 => 0x59a92
  | 166 => 0x1a0d52
  | 167 => 0x1a9953
  | 168 => 0x59316
  | 169 => 0x59496
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1807
  | 6 => 3749
  | 5 => 1374
  | 4 => 8
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/48+packedAt gbK8 (1612+(h % 48)*6) 6) % 62)
  | 7 => 2*((h/644+packedAt gbK7 (66859+(h % 644)*11) 11) % 1807)
  | 6 => 2*((h/1347+packedAt gbK6 (179952+(h % 1347)*12) 12) % 3749)
  | 5 => 2*((h/465+packedAt gbK5 (81066+(h % 465)*11) 11) % 1374)
  | 4 => 2*((h/9+packedAt gbK4 (560+(h % 9)*3) 3) % 8)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffc1f01ffff03fff03ff00ff033ef07c3e7e73
  | 1 => 0x3ffe001f80ffc3fffc0fff001cd13f9e319f9c
  | 2 => 0xc0ffffe000fffc0fffffffffe0e1c1e3c1e3ff
  | 3 => 0xffffffff00000ffff00000ff01fe03fe03e0
  | 4 => 0xfffffffffffff000000000fffe0003fffc00
  | 5 => 0xff0000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x55405005a5300453219902560106702c162e31
  | 1 => 0x26ca010a94564365648a56020c501696309694
  | 2 => 0x8014a6200088a8088a24a8a860a18140c1414a
  | 3 => 0x14e73b537602014ef3c80c0cb701fa037a03e0
  | 4 => 0x20b9cd9c58ef338040003030defa0003adf800
  | 5 => 0x38000e00600c22008300c0c0fbfdedf8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaece8fae8e0e0feeaece8fae8e0e0feeaece8fae8e0e0feeaece8fae8e0e0feeaece8fae8e0e0feeaece8fae8e0e0feeaece8fae8e0e0feeaece8fae8e0e0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40291
namespace PEqualNP.Outside.L_meta_40291
open PEqualNP.Outside.L_meta_40291.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 7 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 12 := bs0_4_0
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
theorem bs1_2_0 : Interval s1Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 10 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 60 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 165 := (concat bs1_4_0 bs1_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 50 := bs1_5_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 6 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 66 := block_range (n:=66) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 66 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 42 := block_range (n:=42) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 42 := bs2_5_0
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
theorem bs3_3_0 : Interval s3Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_96 : Interval s3Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 112 := (concat bs3_3_0 bs3_3_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_576 : Interval s3Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_672 : Interval s3Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_768 : Interval s3Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_864 : Interval s3Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_960 : Interval s3Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1056 : Interval s3Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1152 : Interval s3Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1248 : Interval s3Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_1344 : Interval s3Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1345 := (concat (concat (concat bs3_4_0 (concat bs3_4_96 bs3_4_192)) (concat (concat bs3_4_288 bs3_4_384) (concat bs3_4_480 bs3_4_576))) (concat (concat (concat bs3_4_672 bs3_4_768) (concat bs3_4_864 bs3_4_960)) (concat (concat bs3_4_1056 bs3_4_1152) (concat bs3_4_1248 bs3_4_1344))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_672 : Interval s3Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_768 : Interval s3Atlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_864 : Interval s3Atlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_960 : Interval s3Atlas 5 960 57 := block_range (n:=57) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1017 := (concat (concat (concat bs3_5_0 bs3_5_96) (concat bs3_5_192 (concat bs3_5_288 bs3_5_384))) (concat (concat bs3_5_480 (concat bs3_5_576 bs3_5_672)) (concat bs3_5_768 (concat bs3_5_864 bs3_5_960))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 48 := bs3_6_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 6 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 90 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 44 := bs5_5_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 8 := bgb_4_0
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
theorem bgb_5_960 : Interval gbAtlas 5 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1056 : Interval gbAtlas 5 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1248 : Interval gbAtlas 5 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1344 : Interval gbAtlas 5 1344 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1374 := (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat (concat bgb_5_288 bgb_5_384) (concat bgb_5_480 bgb_5_576))) (concat (concat (concat bgb_5_672 bgb_5_768) (concat bgb_5_864 bgb_5_960)) (concat (concat bgb_5_1056 bgb_5_1152) (concat bgb_5_1248 bgb_5_1344))))
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
theorem bgb_6_1152 : Interval gbAtlas 6 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1248 : Interval gbAtlas 6 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1344 : Interval gbAtlas 6 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1440 : Interval gbAtlas 6 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1536 : Interval gbAtlas 6 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1632 : Interval gbAtlas 6 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1728 : Interval gbAtlas 6 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1824 : Interval gbAtlas 6 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1920 : Interval gbAtlas 6 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2016 : Interval gbAtlas 6 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2112 : Interval gbAtlas 6 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2208 : Interval gbAtlas 6 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2304 : Interval gbAtlas 6 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2400 : Interval gbAtlas 6 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2688 : Interval gbAtlas 6 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2784 : Interval gbAtlas 6 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2880 : Interval gbAtlas 6 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2976 : Interval gbAtlas 6 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3072 : Interval gbAtlas 6 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3168 : Interval gbAtlas 6 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3264 : Interval gbAtlas 6 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3360 : Interval gbAtlas 6 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3456 : Interval gbAtlas 6 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3552 : Interval gbAtlas 6 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3648 : Interval gbAtlas 6 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3744 : Interval gbAtlas 6 3744 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3749 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 bgb_6_576) (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)))) (concat (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344))) (concat (concat bgb_6_1440 bgb_6_1536) (concat bgb_6_1632 (concat bgb_6_1728 bgb_6_1824))))) (concat (concat (concat (concat bgb_6_1920 bgb_6_2016) (concat bgb_6_2112 (concat bgb_6_2208 bgb_6_2304))) (concat (concat bgb_6_2400 bgb_6_2496) (concat bgb_6_2592 (concat bgb_6_2688 bgb_6_2784)))) (concat (concat (concat bgb_6_2880 bgb_6_2976) (concat bgb_6_3072 (concat bgb_6_3168 bgb_6_3264))) (concat (concat bgb_6_3360 bgb_6_3456) (concat bgb_6_3552 (concat bgb_6_3648 bgb_6_3744))))))
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
theorem bgb_7_1056 : Interval gbAtlas 7 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1152 : Interval gbAtlas 7 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1248 : Interval gbAtlas 7 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1344 : Interval gbAtlas 7 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1440 : Interval gbAtlas 7 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1536 : Interval gbAtlas 7 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1632 : Interval gbAtlas 7 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 79 := block_range (n:=79) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1807 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 bgb_7_288)) (concat (concat bgb_7_384 bgb_7_480) (concat bgb_7_576 (concat bgb_7_672 bgb_7_768)))) (concat (concat (concat bgb_7_864 bgb_7_960) (concat bgb_7_1056 (concat bgb_7_1152 bgb_7_1248))) (concat (concat bgb_7_1344 bgb_7_1440) (concat bgb_7_1536 (concat bgb_7_1632 bgb_7_1728)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 62 := block_range (n:=62) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := bgb_8_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 34, 42),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaece8fae8e0e0feeaece8fae8e0e0feeaece8fae8e0e0feeaece8fae8e0e0feeaece8fae8e0e0feeaece8fae8e0e0feeaece8fae8e0e0feeaece8fae8e0e0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808936 * 2 ^ 32 + 4209565920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40291.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,5]⟩,⟨.and,[0,6]⟩,⟨.or,[0,1]⟩,⟨.or,[3,7]⟩,⟨.and,[1,5]⟩,⟨.or,[0,2]⟩,⟨.and,[4,11]⟩,⟨.and,[2,8]⟩,⟨.or,[10,12]⟩,⟨.and,[9,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4209565920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4209565920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40291

open PEqualNP.Outside.L_meta_40291 in
theorem PEqualNP.Outside.L_meta_40291 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4209565920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4209565920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
