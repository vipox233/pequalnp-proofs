import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37263.Model
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


end PEqualNP.Outside.L_meta_37263.Model

namespace PEqualNP.Outside.L_meta_37263
open PEqualNP.Outside.L_meta_37263.Model
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

def SBf (j : Nat) : Nat := [7, 6, 7, 8, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37263

namespace PEqualNP.Outside.L_meta_37263
open PEqualNP.Outside.L_meta_37263.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x1036bd1960e342000000c003800000560512c509870000008803e243035c786242eb4a8f3a649294084d2704a82931628a084a00604024b0800001cc0417c0ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1d9a8361f3f0682432301d030442f10c4a633d0a822270120006553281072010a0000c5a22a14007d000c46e200005452723b0b4006f40800102b250000a001e8001a16000000079230b0128328974c87100000a86727a086a1e080d0000e2d9acb85f0390878192b89896001f800907b3682c8e590014c82613b884d80c340c0f05012130923605000660000000004e118b8004d371d4c428201c0003a111cca413000742e841f03cf8582b1a4002f33000fe380e0081810209098081804000018240410ac080828003c04300000002c082c00080098240808180c0c481000009e7ca721cf54a439ea8c873e5090e7ca621e794c439ea90873d5110e7ca021cf94f429ea8e853e50d0a7aa92157d4d42ae29a859f5350a78a6a16714d428e29a85af5250a7ea2a14f141429f2a0853f54cca78a9994f952329eaa4659c438caeca3195d546329faa2653c544ca7ca8194f55032ce218653e53d067aa5a0cf943419eaa4835f53506b8a6a0e7d4d419e29a839c5350638a6a0cfd4941dba8a833c505067ca820cfd53319e2a6633e548c67aa918e710e31b7294636d528c67ea898cf151319f2a0633d540c7388618cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710cf951219eaa2433e540867aa810f948421af29c815d539027ca7206794e408f29c819d539027aa5204f546409f284813e531027aa4204f544409f28081ba501027ca9984f55330ce21e613e548c27aa9184fd51309e2a2619c434c2dea4985b14930bba8a6174514c27ea8184f150309f2a6413d54c827ea9104f152209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209f2a6213d54c427ea9084f152109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x68049e81602ec0002670090000628800088000e01402cc90304000600aa80800000080000c80c68718d51d0a1e63943428d58454ccb14439463287594430ca8d6210c328718d52d061e63943418b58854cc70c4394a3187594430c6956110c318718d544863860551218718d540861c63548408718d511030c4314930c510c514c21e63d50308b588540c23561150308718d54c821e63d52208718d54c421e63d5210
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (864+((h/16+packedAt s0K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s0K4 (3970+((h/44+packedAt s0K4 (3618+(h % 44)*8) 8) % 161)*9) 9
  | 3 => packedAt s0K3 (1036+((h/8+packedAt s0K3 (988+(h % 8)*6) 6) % 45)*6) 6
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 2 => 0xc0ffffc0fff83fff07c1e0fffe1fe07fd13e73
  | 3 => 0xff03ffff03ffc1fff801ff07ffe1ff81e1cf9c
  | 4 => 0x3fffffc0001fffffe0007fffe0001fe0fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x44100888209000002942410900222a280650a5
  | 2 => 0x92299106492270cb0290a8d2b2154154d12652
  | 3 => 0xa4aa2121a46135550213a44d5419505618b18
  | 4 => 0x2cb344a49074a5a69cf4108769980619ba0de0
  | 5 => 0x30c38738e38739f8e739dce071111861fdf000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37263
namespace PEqualNP.Outside.L_meta_37263
open PEqualNP.Outside.L_meta_37263.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x25450a0070180258000190002400bf43bd43ef32ec32bf41bd41ee21ec21be40bc40ef20ed20
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x394c01a400020440a4c26aa3a1d994732c6a18651d53d069ca710e9504218ea9881355110298a6905914520
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
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (212+((h/4+packedAt s1K4 (192+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s1K3 (282+((h/3+packedAt s1K3 (270+(h % 3)*4) 4) % 13)*5) 5
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff83ffffffe07ffffffff03fffff1ff1ff
  | 2 => 0x83f03ffc1f83ffff870783e0ffc3c1ffea4e4f
  | 3 => 0xfc003fffe003e0fff807fc00fffc01e0f38f8c
  | 4 => 0x3ffffffc00fffff80000fffffe00fc0ff0
  | 5 => 0xffffc000000000ffffffffff00000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x80200088010000000808842210044422009095
  | 2 => 0x28c65910ca255865834323446642895c6a464a
  | 3 => 0x196aaa29474a89aab885e90abaa81586b38b8c
  | 4 => 0x528d34429460d2d355d04210cd333808dc0d60
  | 5 => 0x630e387318731cfc66e6739c0e222110ff6000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafaaaa0a0faaaaaaafaaaa0a0faaaaaaafaaaa0a0faaaaaaafaaaa0a0faaaaaaafaaaa0a0faaaaaaafaaaa0a0faaaaaaafaaaa0a0faaaaaaafaaaa0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37263
namespace PEqualNP.Outside.L_meta_37263
open PEqualNP.Outside.L_meta_37263.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xc00f8f0200d290000280008800028840090008c27007918e1aa80104874c8700300250800411504ce1b06ad315005800a402c9002e04f28300200208328e080ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x70004c92a404006a4a1600845c068200620000680000369838302e286454003e00b4000050001c004e000000888c5a3a2a007c3244a6b080121a0a56726600000000009a000000000000468a34523ca2000000000000000000000000006e7a420c58948e7602a00078001848862010085e9e60ac2400a89000002c009600ae401e0000b67e0022aa00000000000000006c0000b274000014269c00000e0000000009000001020000070003020902050f030000000003000309010607000100cea18876e5210edaa421d794c42aea98853e540ca7aa8195794f41aea9e836e52d06daa5a0d794e41aea9c836f52506d8a4a0cf953319eaa6636e52cc6daa598cf952319eaa4636f524c6d8a498db94621b6a84433e540867aa810d794c21aea98437a50086f2a010eb95021d6aa043ce530879aa610db94421f328843ea50086daa010fa54021b4a80436e52902daa52057d4d40ae29a815e53102baa6205b94840b6a90817651102eaa2205b94a30b6a94613f544c278a8984f950309eaa0616e520c2daa4185d94430baa88613e54c827aa9905794f20aea9e41ae54c835aa9907394f20e6a9e416e51c82daa5105b14520f5a82416e52082dea5885b14b10b7294216d52843d241084fd51109e2a2215f53442b8a6885bd4910b629221e9204427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x6e0024a80c010c350d5210f0d5454c21ca95150087295454021d294d50087495354021c355153c82686548110
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
  | 4 => packedAt s2K4 (2724+((h/30+packedAt s2K4 (2484+(h % 30)*8) 8) % 161)*8) 8
  | 3 => packedAt s2K3 (312+((h/2+packedAt s2K3 (304+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xc1ffff83ffff0f07f0fe1fffc3fff81e89f3f3
  | 1 => 0xfe1f0ffc3e1ffff87f0fe1c1fc383fff764c9f
  | 3 => 0xffe00fffc01ff1ff800ffe01ffc03fe1878f1c
  | 4 => 0xfffffe001fffff00001ffffc001f80fe0
  | 5 => 0xfffff000000001fffffffffe00000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x44020088040010008012024440488844009131
  | 1 => 0x88841110902a00283104208884111298324486
  | 3 => 0x144aaa290d548353888b54156a82a545858b18
  | 4 => 0x3954cc42a906a59d5aa11021b3270189d80ec0
  | 5 => 0x219888733198c9e66ccd993822040611ef6000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeaacc88eeeeeeaaeeaacc88eeeeeeaaeeaacc88eeeeeeaaeeaacc88eeeeeeaaeeaacc88eeeeeeaaeeaacc88eeeeeeaaeeaacc88eeeeeeaaeeaacc88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37263
namespace PEqualNP.Outside.L_meta_37263
open PEqualNP.Outside.L_meta_37263.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x15a4003c0004000980500021738140183a944030e24d9e2001080524468100580260018000240001f009ca94168d50034646024428700000010404011c70404c0003ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xe617d51cc3be6398774c730bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea9461bf428c37a851877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c3be6298774c530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa4186fd0830dea1061df320c3ba64185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20dfa1641ee42c837a85907b50b20d6a1641df32c83dc6590774cb20f699641cd32c82fca3905f54720f790e41ed21c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5106fd0a20dea1441df32883ba65105f94620bea8c41ee21883d843105f94220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c534837e84907b90920dea1241ed424835a849077cc920f719241dd32483da6490734c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4106fd0820dea1041df32083ba64105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43be6588774cb10fb20e21f541c43ec63887d4c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c528437e85086f50a10ef99421dd32842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa1221bd42443be6488774c910fb20a21f541443ec62887d4c510fb10a21f521443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c520437e84086f50810ef99021dd32042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xc525077e84a0ef50941ef99283dd32507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077a8620df94841bea9083bf421077a8420f7cc841ee990837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331efa1e63dc43cc6fca598fb94b31b7296637d52cc7daa598db54b31dfa1663bd42cc7be6598f74cb31bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718f790e31eea1c637e528c6faa518efd0a31dea1463df328c7ba6518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931dfa1263bd424c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf29863de430c7ba8618df94831bea9063bf420c77a8418f7cc831ee990637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21dfa1643bd42c87be6590f74cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510efd0a21f721443bd42887da8510eb50a21ef99443ee32887ba6510fb4ca21e6994437e51887de4310fdc8621bf284437d50886fea890df95121beaa2437c54486fea690df94d21bea9a437c534877e8490ef50921ef99243dd32487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410efd0821f721043bd42087da8410eb50821ef99043ee32087ba6410fb4c821e6990437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40ef99681dd32d02fca3a05f54740dfa0e81bd41d02faa9205f94e40bea9c81be439037887205f94a40bea9481bf429037a852077cca40ee994817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037e84a06f50940ef99281dd32502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206fd0840dea1081df32103ba64205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30dfa1661bd42cc3be6598774cb30bf28
  | 2 => 0x800800000800000000000000000c00400000000000800400000000400400000000000000000000000000800400800800400000000000000800800401000000000000c00afca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210fdca421db94843bea9087ed5210edaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7c87a16f50f42de21e857e51d0afaa3a15f94342bea8685bf53d0b7ca7a16f54f42de29e85bf51d0b7ca3a16f54742de28e85bf50d0b7ca1a16f54342de286857d5490a7aa9215f94e42ef29c855e5390afaa7217754e42aea9c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f90d42dea1a85bc4350bde84a16f90942bfa8a857c5150afea0a15f14142dfa9a85be5350b7aa6a16f14d42dfa9285af5250b7ea2a16f94542dea8a85bc5150b7ea0a16f94142dea8285bc5050afca8214f95042bf29885de5310abca6215f54c42eea98855d5310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a99977d0f32ef21e65dd43ccbb887996fd0b32dea16657e51ccafaa3995f94332bea8665df54ccbbca9997755332ee2a665df42ccb3e85997790b32eea16659d42ccbb8859977d4732ef28e65dd51ccbb8a39977d4332ef28665dd50ccbb8a1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32aea9c657e528cb7e85197b90a32dea1465ed428cb5a851977cca32f7994657e518cafaa3195f94232bea84657f544cafca8995f55132be2a265df434cbbc86997750d32ee21a65bf424cbdc84996f50932f6a1265ad424cbde6499778c932bfa8a657c514cafea0995f14132efaa265de544cbbaa8997715132efa9265cf524cbbe849967d0932ef21265ce424cbba84996750932e6a12658d424cbb8849977d4532ef28a65dd514cbb8a29977d4132ef28265dd504cbb8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32af298657e520cb7e84196f50832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d077c87a0ef10f41bf29683ee52d06dca5a0df54b41f6a96836d52d077e85a0ef50b41ef99683dd32d06fca1a0df54341beaa4837e53907bca720d794e41bea9c83dd53906baa720efd0e41dea1c837e52906faa520efd0a41dea1483df32907ba6520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837
  | 3 => 0x11480000000000000322ad00033f4ee19c0000062c0000000000000000000000000002dc00076162800000024d0b4100000055800000000000e80000000000000000000000000000001de000001540000000000000000000000000000000e3b470000000020e02c000000000000000011400000000345000000000000000000000043e000000000000000000000000000197000000b3af31d277d06b7600000000000000000001a600000000253000000000562fa0f56ca1e00000000000000d6999000000000ca00005800000000000d54000000000000000000000000062000001248000000009b8000003c8448005d49400007212a0000000000000000177000000000004f0a2d048000000006e8004ce984b2000000000002961b22f8000000e2001aa2024ecc6175941000000000000000000000000080c000002aa520000000d2295a198c00058c43000000000001bc000cc46d800000000000002840000000000074800000000358000000000000000051e00000000000001948005462000016b000000000000006ec000000000002c80000073c580002d2000001f00000000000000000000012000511818000000017e00017e53cf000019e00000000000144000000000000000061c3bc000000000000000051a3acf9000000b98e20a16dc0000000000056c0000054e0000000000000000000000001118000000000030a1dc0014a92a65a0000011f0000000000000000035a43000000d78000000005134b00000000000000de00000000000000130560bc476000000000002e3344000000000000000000000000000000000000000003d06c4002550000006580056a0000000000000000000000000fd8005620000019f0f0000000000002600000000041000000000400000000000000000000000000000000000000000800000000000000800800000000400800000000000000000000400000000400800800000000000800000000800800800000800000000c00000c01000000000001000c00001000000000000400000000000000000400400400000000000000000400400000000000000000000000000000c00000000000000000000000400000400000000000000000000400000000000400800000000000400000000c01400800800400000000000000000400800000400000400000000000000400000000400400000000800000000000000000000000800000000000400000800000000000400000800800000000000000400400000000400400000000000000000000400400400c00000400000000000400400000000400000000000400000000000000400000000000000000400800400000000800400000c00000400000000800000800000000800400000400c00400800000400400000000000c0000000000100040100
  | 4 => 0x80000000000000000850e50000000000000000000000000000238000000000000000000000000000000c040024030c00021800000a68d58000004a1500000000008722b000dc4968003389e45700000012c000000000014200000000000000000000000005b60b800242000000001232a0a70000000000000000000000000212000000001f91a20000000000000000000332000000000000000017905a000001530000013d0006000000000003486400000000000000c5116570001ac0005ec0033716a76802907000000000000000000017800000000000000000000000000000000069413102000218000a480000000000000000000002dd000d98000002b000000000000000000000000016001e0003f80025e00000000000000000c10000000000028000000000000000d40002cf000a90002df0000000029d5fc000000000007d1598000000000002020000000000000000001e200000000000000000199d600000000000000000000000000000014e0007b14f8000000000000041e00000000000000000000007acf08000000000036300000187a730008800000000000000000640000000002420000000000000125800000000000030000000000000000000000000c10000000000000036b2646cc0002b000000002060000000012021e000002691ee0000000000000000000000000e000000016c608b9000bf58e800000000001315da0018d9fd61200000000000d10000000007fc00000022000000000fa00000000000c2cb2800000000000000000000009d000c8c000006ba000fe0005dc000002c1000000000000000000000000000000000000001028000000000000000000000000000000dea2f0006b442b58000b9002288000000ea00000026400000000000002c400000000000000001a700048e000001a800000000000000000000d0046000000000a40000000018e00000000000598a90f55ac3880000000047800000000960000fb0000000000000000000000000001b900000000000000000000780000009896b800000000002a20000014800043630c00000000000000001fa000c00000005f00000038a00000000000b2c00000352000001d0000000000000000008aa5f2100000000036a0000000000000000000000000001560000000000000000024b3026c35cdf00000000000000348744000000000000000022e00000183000458002380003e85500029a1d905800000000000000a800000000000000000000008045a1e70000000021a000000000005740000000000000000000000a9800000000000000000004fc00217252000001b8000000000000000000008a0000008122700000000000000000000000da000000000000900000000000000000000000002da000000000000000000023b000b24d00000000000000
  | 5 => 0x61c000000002a0000000000000000000000000000000000000000000000015d000000000000000000017613e00000000000000000000000000027c5a80004f00000000000000000648c80210000015781831a000000002be0005b800000000000001201b8000000000000000048a0013d80000000000036000000000005940000014b000001a40003da000003174fe2d800000382000000000004f40000007e00000075192001ac80010e0880b80000000000000000118a50c800013800000000ae000241000001448003de000000000000000034d0008f4002f727898c1b800000000000404e884d10a9200039c000000000000000000000000000000001488004680000000032a64c00000000001b200047e00000000000000000000ee001618a90001080000000055c6a000000000000000000000010500000000000000000000000000000024d00000000000000000000e600000000000000000000000000000000000000000000000000000000000016f00000000017a6b0aa00126000000000d800012c0000000000000000000000000a300000000018000000000000001e200000000000998000002f400135000000000000f600062c0000024a0018e0000000000000000000000000000948000000000003f000000c889c00054a418000003ea000000000000018601b00000000000000000000000008580027015e0000000000000000000000980000000000000016e000000f30000000019f2c264e000000000008940e80000014c00000000000000000000015b00062a000b41ea0000000002a000000001fa0000007c1244b4000002fa0000000000000000000000000000001e3000000000002a230000000000000003331248f0000004ac5d40033900000000000000000000ea0000000000027693c00000000000000000000000000000000000000000000000000000004a2480d00014b9186744895f0000004280000069e00000041000de400000000b34000000009f8000003020000000026600000000000000002e10e8368ee8002d400000000564425b12bf2b2180a2984000000000006ac000002a90000000000000000000000000000308003aa000ff000000000000000000000019a000000cb0570000000000000000000198670000000006c25840000000000000236000000000000000000000025e000000003dcb30000005ceaf00008f39800000013000bd4000000000000000006200000230000000000000000000000001e000000000000008691a018000000000000000000000000000091000000000000000000000000072400000000000000000000018d3282de000000005fe000000000000019eaf40000007000000075c001c61020001a0000640000036a0003cc2f0000000000003a0000017db1f15a17d92
  | 6 => 0x7f8bc6420017402533600000367000281778636760016a8003e2c6400000000000000005d8000000000000000000046600000000000000000000000000000000000000000000dc000000000000002720000000000019a00053850000000000000000009f00005000000000032000000d300000000000000830d5000000000000ba07888814a990000006500024e000278840000010e800000c0982a943b600000000000000000000000000000000000000000000000000005a2000003260000011c8000000000000055800000000000614f4a930000009cb4200000000000000624000004da0000015a0000ecb9b680000017cad2000000002f6000000000000000006c00037e001568000000000006f0000000000000000052000000ddc000002e8000000002c4000000000000000028123837c000000000009601000000000000000d7c06800000000000000000000f8004fac3413271000001a88000000000002739c000001ba000000002c747c2e000228000000001cd3ee0000005a0000000000000000000000000d800000058c000672180000e40014c00000000235000001ba80000000044000000000002570000015d80000000000000000000bf8001f8cac000004dc000000000000000000000000000000000000000000001e8000ed0000000000000000000000000001082f800097000000138000000006b60000000000000000000000ab8000002567d8d915e626001a9000000000000004b200000000000000000004b67e09304d000000000000000014335c0000000019e0000000022a0006e4000000006d14d800000000ce9c8000348000000000000024e280000000000000000000000000100000000318000000001ec00000000001160000000014500000000000000000a38000000009b00000006a000000000900000036c1c600000000000c1859800000000002e2000000000000f2000000000042c846800000000000000000000007f000000000ac000b6000045000000729a75d20005e800202000000001b80000000000000000000000950000000000000000000000169a8c0ba00000000000000000644ca31023800000001089a50008c8000010000006f0000000000024600c4d40000000000000000698b40000000d4000000006800000018a000000f28006587651880053c000000000000000000000000000000000000bf0000000007200000024c7a00065e00122083000000002830000004d98f0000000000000000000000000000b00a61f2c40a38b100000000000000000000006de4e8000001180000000000000041000000000000000000000000000000000000000b20001b612e6200004a00087081b11000d7885800000000000000009d42c00060e001670000000000020a0000000022e00000000000000000
  | 7 => 0x1c000000000000000000000007c6380000000033000172000000001d35c00000000000070c00000000000000002200000000066a000000004c80000011d000001288000000011b919000000001e45540000000045a0000000063c00000000000ae4000000000000011200000088a986d2199b28c24de85400000000001038000000000000000046dba000556170050005e4001ab808000000002b7000000000000000000000035c0003296c000000002bd00000000000000a09a30bb0000380000000000000000016cd8038d50e00000025d00000142a26000a84000000009a00000000000104000000000000000e60000000000068c0000000072c000000008e800000000000ee000000000000000000000024a44800000000000000aa0005e000000000286cf00ab2e0000000000000000000000000000000002e21f000000000000002e56da00000000000000001132da7cd890006540000000000000000000000000708000000000000000000000353000000000002e000000000000000000380280004d0006100000000000000000000000000000000000000012e0000000000000028d8a000000000000000006dd9a000000001b9b240007089a2876920002206c000000000000000
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x2528423d6494a109798e528425d6394a108f990528423d6414a109798c528425d6314a10cb949428432d5250a10d3949328434d524ca10e350932843a94248210f24c9208423d62d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f58854443356115110c7d53534431c54d4d109758b534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534425d6214d10d5584534432f54d4910cb153524434f53d4910d314f524432f64d4910cb193524434f63d4910d318f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149109b994524432f5414910cb150524434f5314910d314c524432e6414910cb590524434e6314910d358c52443656114910da580524423e65d09108f197424431f53d0910c714f424432f52d0910cb14b424423e65509108f195424431f5350910c714d424432f5250910cb149424425e65cc91097197324431f54cc910c7153324434f52cc910d314b324425e654c91097195324431f544c910c7151324434f524c910d3149324438d424c910cd15241442d563905109d19541442b5648c510d514e3144274654c510d914a21443a54288510f14ca21442746548510da14a20443e221881109e19520443a94248110f24c920443e121481109798f540425d63d50109b98b540426d62d50108f596540423d62950108fd89540423e64150109798c540425d63150109b988540426d62150109d984540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c109758a530431e5454c10c7551530425f6254c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48108f992520423d64948109798e520425d63948109b596520432e5494810cb552520434e5394810d354e520432e6494810cb592520434e6394810d358e520432e5454810cb551520434e5354810d354d520432e6454810cb591520434e6354810d358d520423e64148108f590520425e63148109758c520426e62148109d984520427a60148108fd97420423d65d0810c794f420431d53d0810cb94b420432d52d08108fd95420423d6550810c794d420431d5350810cb949420432d525081097d97320425d65cc810c7953320431d54cc810d394b320434d52cc81097d95320425d654c810c7951320431d544c810d3949320434d524c810e3509320433554c4010d554f100436552c40109e596100436952840109dd9510043355444010d554d100436552440109ed9510043695244010
  | 1 => 0x82af6550b20cbd9542c832f5350b20e394d42c832d5350b20e354d42c830d5350b20c795332c831d54ccb20e350b32c82ad648cb20cb55232c831e544cb20c755132c838f424cb20e350932c832d544cb20d394d32c82cf654cb20d3d9532c834f544cb20e395132c834d544cb20e355132c830d544cb20cb50a51c834d3294720ab59321c82cd63c872097d8d548825c63552209798c548825d63152209d984548827561152208fd91538823c6454e208f990538823d6414e209d98453882756114e20e3509328823f64546208f191518825f63546209718d51882e9600862097d8d544825c63551209dd85544827461551209798c544825d63151208fd91534823c6454d209dd8553482746154d208f990534823d6414d20ab59242482cd63909209b195424832f6550920cb195424832f5350920cb54d42483ab6050920ea181424838d42cc920ab59232482cd638c920e3d09324838d424c9209b195324834f654c920d3195324834f544c920d355132483cb604c920f2181324823e64145208f590514825e63145209758c514832d4214520d34c8514826e65c8520ab59321482cd63c8520ea50b20483c932c81209798f540825d63d50209d987540827561d50208f596540823f62550208f589540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c2097d89530825d6254c208f990530823d6414c209798c530826e6214c209d98453082756114c208f992520823d64948209798e520825d63948208f597420831e53d0820c754f420823f6550820c794d420831d5350820cb949420825d65cc820c7953320831d54cc82097d95320831e544c820c7551320834e524c820e350932083365494420cd55251083565394420d554e51083374294420cd50a51083573294420d54ca51083365454420cd55151083565354420d554d51083374254420cd50951083573254420d54c9510826d6588420cb552210834d5388420d9546210832d5408420d354c21083655108420ba580210832d54c8020d354f200836551c8020dc546200826f6548020cb551200834d5348020d9545200827b6548020dc545200825e63d53109758f54c425e63953109758e54c426e62953109b58a54c423e64d4f108f59353c423e6494f108f59253c426e6294f109b58a53c423e6494b108f59252c425e6394b109758e52c423e6414b108f59052c425e6314b109758c52c432f5250b10cb14942c434f524cb10d314932c438d424cb10b558e41c42b5648c710e950a21c43c5328871097d8d548425c63552109798c548425d63152109b988548426d62152108fd91538423c6454e108f990538423d6414e109b988538426d6214e108f99
  | 2 => 0x5350840c754d421032e525084097d97321025d65cc840d394b321034d52cc84097d95321025d654c840d3949321034d524c840e350932103565394440d554e51103665294440d954a51103374294440cd50a51103573294440d54ca51103565354440d554d51103665254440d954951103364354440cd10d51103374254440cd50951103573254440d54c9511023d6590440a798e411031d5390440cb54a41103355190440c754c411032d5210440cd544411031d53d0040cb54b401033551d00408fd95401029c6350040c754d401032d5250040cd545401027b65500409b98854cc26d6215330c715143cc23e6494b308f59252cc32e5250b30cb54942cc34d52ccb30e350932cc23e64947308f59251cc29d64cc730b358b31cc26e62152309b588548c27661152309d584548c31f5410e30b3588438c23e6494a308f592528c32e5250a30cb549428c34e524ca30d3549328c38d424ca308fd91518c23c64546309bd89518c26c6254630a7992318c23d62d51308f992544c25f63551309b988544c26d62151308f994544c2ad6215130c758c544c32e62151308f588544c32d62151308b588544c25e6590d30c7152434c25c6550d30c7151434c23e64149308f590524c23e65d09308f197424c23e65509308f195424c31f54cc930c7153324c31f544c930c7151324c34f524c930e3509324c25e65cc530a7593314c31c54cc530b358b314c31c544c530c7152304c26e62d50309b58b540c27661d50309d587540c23d65950308f58a540c31c63550308fd89540c23e64150309798c540c26e62150309b588540c27661150309d584540c25d65d0c30c7553430c25d6510c30c7550430c2cd6210c308f992520c23d6494830cb952520c32d5494830cb992520c32d6494830cb951520c32d5454830cb991520c32d6454830d398d520c34f4354830d310d520c23f65d08308f597420c32e52d0830cb54b420c23f65508308f595420c32e5250830cb549420c31e54cc830c7553320c34d52cc830c7951320c31d544c830d3949320c38d424c830cd952510c3355494430d994a510c3655294430cdd0a510c3354294430d5cca510c3553294430cd951510c3355454430d9949510c3655254430d5d0d510c3544354430cdd09510c3354254430d5cc9510c355325443097596310c29e648c430c7552310c34d528c430d5546310c31d540c430d3548310c355510c430c7553300c34d52cc030d5547300c25f654c030a7191300c31d544c030d3549300c355514c0309ed95300c25e63d53209758f54c832e62953209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f20d398a53c831e5454f20c755153c823e6414f208f59053c831e53d0b20c754f42c82cd6390b20d354e42c831e5350b20c754d42c832e5450b20d354d42c
  | 3 => 0xa21d355132887c7614ca21f118532886ad64c8621b358f218863f64542218f191508865f63542219718d508872d4254221d34c9508865e63d51219758f544865e63951219758e544866d62951218f993534863d64d4d218f992534863d6494d219b58a534878d424c9218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540872e62950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c218f992520863d64948219798e520865d63948218f597420871e53d0821c754f420866d6590821ab59242086cd6390821d354e42086e561908218fd95420871e5350821c754d420872e5450821d354d42086af6550821cbd95420872f5350821e394d420872d5350821e354d420870d535082197597320871e54cc821c7553320878d42cc8219b59632086ad648c821cb55232086cd638c821b9586320865f654c821c7951320871d544c821e3d09320878d424c821cb551320874e534c821b3d95320874f654c821d3d51320878e544c821d3551320878d544c821c3551320872d4294421d34ca51086ad64c8421b358f21087a54288421f14ca210866f65484219dd9521087a74248421f1cc9210873a5494021ce552500875a5394021d654e50087a94294021f24ca500873b4294021ce50a500875b3294021d64ca500872d4254021d34c9500873a5454021ce551500875a5354021d654d50087a94254021f24c9500873b4254021da90950087394254021da50950087294254021d6cc9500876a3254021d64c950087693254021d24c9500876b2154021dc88550087692154021dc485500865e6394b409758e52d032d52d0b40d394932d034d524cb40e350932d025e63947409758e51d029d63d0740ab58b41d02ad6210e409798e529025d6394a40cb949429032d5250a40d3949329034d524ca40e3509329025f63546409718d519026f62546409b189519029e63906409758b535026e6214d409b58853502cd6214d40d3988535025d6214d40d3588535024d6214d408f997435031c53d0d40c714d435025e63149409758c525031f53d0940c714f425031f5350940c714d425032f525094097997325025c65cc94097995325025c654c940e3509325023e65d0540a758f415031c53d0540ab58b415031c5350540c714e405025d6294c4097d89531023d6590c40c754e431031d5310c40ab588431025e63948409758e521034e5394840d354e521034e6394840d358e521034e5354840d354d521032e6454840d398d521034d6354840cb90d521032c4354840c794f421031d53d0840cb54b421031e
  | 4 => 0xb94942d065f65ccb419759732d074e52ccb41d354b32d065f654cb419759532d074e524cb41d354932d078d424cb419b98a539066d6294e41b358a539074e6294e419758a539074d6294e419358a539065f6254e41c794f439071e5350e419798e529065d6394a41c794f429071d53d0a41c794d429071d5350a41cb549429065f65cca4197597329065f654ca4197595329078d424ca41a758f419071e53d0641ab58b419063e6510d41ab588435065e63149419758c525072f5250941cb14942506b46150941d3d49325074c524c941e3509325069e63905419798c505065d63141419b988505066d62141418fd95431065e63948419758e521072d52d0841ad587421074e524c841d3549321078d424c841a758f41106ad62d04418fd954110677655044197d8d501065c63540419b98b54cc66d62d53318f58a54cc71c63553318fd8954cc66e62153319b58854cc71d54d0f31c755043cc6cd6210f318f99252cc63d6494b31cb95252cc72d5494b31cb99252cc72d6494b31cb95152cc72d5454b31cb99152cc72d6454b31d398d52cc74f4354b31d310d52cc63f65d0b318f59742cc72e52d0b31cb54b42cc63f6550b318f59542cc72e5250b31cb54942cc71e54ccb31c755332cc74d52ccb31c795132cc71d544cb31d394932cc78d424cb319b98a548c66d6295231ab58a548c71d6395231cb98a548c63d6295231cb58a548c62d62952318fd89548c71e5490e31c7951438c63e6494a318f592528c63f65d0a318f597428c63f6550a318f595428c71e54cca31c7553328c71e544ca31c7551328c74d524ca31e3509328c69d64cc631c7953318c6cd62cc6319758e544c66e62951319b58a544c65e65d0d3197994434c71d5410d31b3588434c63e64149318f590524c72f5250931cb149424c74f524c931d3149324c78d424c931b5185324c69e648c5318f990504c63d64141319b988504c66d62141319798f540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c65d6590c3197d95430c71c5450c318f992520c63d6494831cb949420c72d5250831d354b320c6d561cc831e3509320c63e64944318f592510c69d64cc431b358b310c65f654c4319dd95310c63f64540318f191500c65e63d53219758f54c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c863e6414f218f59053c871e53d0b21c754f42c871e5350b21c754d42c871e54ccb21c755332c871e544cb21c755132c878d424cb219798f548865d63d52219798e548865d63952218f993538863d64d4e218f992538863d6494e21b358e428872f6550a21cb195428872f5350a21cb54d42887a76150a21e9185428878d42cca21ab592328878f424ca21e3509328874f654ca21d3195328874f544c
  | 5 => 0x50d0b4e6294e42c794f4290b1d53d0a42ab98a4350b1c5350d42ab9884350a9e6390942a758e4250a5e63d45429758f5150a5e63141429758c5050a7661141429d5845050aad6294d42ad9865350ab56194d42abd895350b1d5314d42ab58f5250aae61d4942ab5835250a9e63d4542a758f5150a9e6394542a758e5150b355114542a7d8d5050a9c6354142add855050ab46154142a798c5050a9d6314142ad9845050ab56114142c794f4210b1d53d0842d354e4210a3f6550842c794d4210b1d53508429bd954210b2e5450842d354d4210a7661d53329d58754ccb1c5450f32c755043cca3e64947328f59251cca3f64543328f19150ccacd62d5332b598754ccad561d5332c755054ccacd6215332e3d8942cca9e64d4732a759351cca9e6494732a759251ccb555114732a7d9150cca9c6454332a799050cca9d6414332b598450ccad56114332cb98a548cb2e5450a32abd95428cb2f6550a32c7953328cb1d54cca32cb50a518cb2d42542329d986544ca75619513297997434cace62d0d3297195434cb1c5450d32c7550434cace6210d32ab592424cace63909329b195424cb8f4350932e390d424cb8d4350932e310d424cb2f6550932cb195424cb8f6350932e318d424ca9e648c932a7592324cb8d428c9328f993514ca3d64d4532cb508514cb2d42d41328f990504ca3d64141329d984504ca756114132b358a544cad66195132b5586544cacf6255132c7550544cacd64d4932b3987524cacd60d4932e3d4b424ca5e6590932a7592424cace6590932d3996424cacd6490932a3592424cace6190932b3582424cb8f6250932e3d49424cace6550932b3195424cb8f6450932e3d51424cb8c5450932b3185424cacf6050932e3d95424cb8e6550932e3595424cb8c6550932e3d85424cb8e6150932e3585424cb8c6150932e3d81424cb8e6050932e3581424cb8c605093297994424ca9e6410932b3988424cb8d4210932a7993514ca9d64d4532e350b514ca9e6494532a7592514cb8d4294532e3509514cb8d4214532d5544514cb8d42d4132e350a504ca9f6454132a7191504cb8d4254132b5d85504cad46154132a7990504ca9d6414132e3508504cad66114132b5584504ca5e63d50328f596540ca3e64150329798c540ca6e62150328f992520ca3d64948328f597420cb1e53d08328fd95420cb1e5350832cb949420cb1e54cc832c7553320cb2d548c83297d95320cb1e544c832c7551320cb8d424c8329bd95320cb2d544c832d394d320ca5d6294f4197d8953d071d5390f41c754c43d06ad6210f419798e52d065d6394b41d394e52d074d5394b41d398e52d074d6394b41d394d52d074d5354b41cb99152d074e6354b41d358d52d072e4354b41cb10d52d071e53d0b41c754f42d072d52d0b41c794d42d071d5350b41c
  | 6 => 0xa1d794627b8990ef14a83d13b818a6ea7a03aa9b9868a38ea82196625125c9871db9ad9f61ed201a4e1072909a49efa118370128b22169998f4a88a769f48441a89508c398313f20fa961bd85d1ae22aa9d09b0f09f29f9023a0811c266a3d0958418eda2102a9c48f21f39e908a9b705211fa84851a62a279fd1d30f30580750dd1319cc1d724116c95e23c8a890a95c87483012608783b01699a156279a0080928305f89a28a26fa51860a488ed0000c8a160cb8d729199d80003626080300909a00000808000004030580040000301f02c014098090080040101006e008018010000240080c00a0180000100a0101903a000040040040120180581100207c0e0000100000200000600c1780702c000170010060100680101e0140e0300080000100000c0cc0200209a004018070000000380003a000028000000680a00203a004020120160100600203602c2e80000002c000000020480880402c0c40c00f00000400824032014010000000b80080700602c0000103601c058010020580080a0020040000a018004000040160100880f000090020000120000000103601c0200700e05c0400201a02000000000070020000160100780d0000000a8000420580000c0060200100802012c0280400c0101c0020040000000101005c0080000002c0500d00c0c80a018014024130000020100001b00400c0501900200c0000200000c098210000141580602e0200080001400401000006014000030020081400000c07c00002002000020030000a81780108a0980200c01a01c010050320040080500a0000300b000024080050040140700000404c0080e0020040100a00c0100200f0100000081700a01c0080701e0180100901005401000000018000260000140681d0000280100101c0a40f80900401000003030000050000280100601a018008030060060c4008070280080600000005c1e81600004000000000008028000260340d00500000005800022010010010600140002d01e010018010080601480a02a0000c00303a0000000400e024048000000140580101400c03802002060000000040080180000c0380500101200c14014000028070120040003b80000a048010019b98b5150e6d62d45439b9885050e6d62141439d9845050e756114143a75924310e3f6550c4397d954310e9f6550c43c7d954310e9f6250c43a7d854310e9c6050c43e350e5210f1d4354843e350d5210f2e6454843d398d5210f2f4354843d390d5210f2d4354843d350d5210f0d4354843c750e5110f1d4354043c754c43d0a5e63947429758e51d0a5f63543429718d50d0aad62d4f42ad98753d0ab561d4f42c754c53d0aad6214f42a798f51d0a9d63d4742a798e51d0a9d6394742cd54451d0a9f6354342a718d50d0a9e6314342a758c50d0ab66114342ad584
  | 7 => 0xec92f000107a691c01408078548c589792f9a38000001f124380023f9ad01e1b7919a21a6da6f15180d06f000103a0ba0f19b1be87911317aa951bb17124324592e806a0a98fa2a05510a0421f8055a2c8e48f18fc10f80e09e9eb1380fd8f881f04319ba5e86106a90b973a652809378f2a070c70049c30910918391b19da0d39f18cf2758b2a4b8fba869ac85105390e98aa9a96a9a6a1ea2909721a17820e9ee9bc9ca01c95fa3906c08703517f0159dc8a590910296315789095692110216c1d8a79019a34a9d96f00e9a803c0c99551468b812297c83783e9d004124c99c1249800aa1728b380f1b3971a011be0b682c80a8a4a86108246a8b0001ce8002182638000b880012e2921fe0b0a1095ba2717d81a91283389f9bc0d212b24f80996018b12a8000a916921380000b0000001a580007d8001c71670000000001991440268c40ea0fb0c914180016e9140459858fa0b611c89f08203f14484c910974159a5725d1118038e101521c00016b1de1a907f9f79f5a2b28289227620a05699208980018622c1ce06800009821999280507f00026a0001410000000b00001b58000498000798bc97917c21d82c29a15c1aa10323783229904380011a8cca5691a2590f794c0001b08c28951358251420000bf15a84e9ac05716202d12809a84b07e042a5614e1658001810ac8030648002958d4258293210181a9120d242038231a2028200019480002b99e13da3e8a20489010938130b7800265876a1c94ba501d18000e500004a0df953a0929c95f0001e88230669b003b9e410e29c07a97b9850da14da901492301cb1c61df0120000000e080000011b82080008da1e02a0f580008a00000007222480001d0000000000000000001cd1890000cf94c8a68000a00000000010000a08000001258bb8001d625a8002398001e38161c50001398998a829b1180000000000001170000809d49b40e28308310d0a4a14b02025d8000eb0002619b21c8954a890988002320000000000d52781d295b12184720406f8270e41b68e398d1fa1849cf152a3f10199819022f9c09b9a5f0e90000000000000000c4a3b1c40562980058001158de8e98000e586ca7b0002252620001ea0002810cd03a00000001780000000c8000000000001f08000f70ac1571c824f08e2371758000001d803400011e8b72222648fe966a238000f01af1c915a18205ca2898a0540171e123c0d29ab04d1ca9c280000017493a14f8892938000a410b04787096d24c00000010c00026a97f9b8a1b83317d12726b17b0d90658001e792d800150036a07a310eb8ce07013205e8d320310d024a5f85c28c96b80622e8001e31241731230291f00aa9fb2882052140101ba2720ee257972059082a732729612039289328530ba16985a9b90c693c0b126028e0141d9a8413414887
  | 8 => 0x18c100d9b113902d9e68001f5092a1f1c203e22693a8ab1388be9480c5136297a0b17681481d8c194a18e9938328d580028b9e591d1a780019700000018d8002681fc1a4164a702159499af80027e1968dc1479d58001438f41ae8002709ffa4618f0002170ec00009611f1148000de0e18000000000080000619369f71d39a31a00788638d6a00164129819116a149cda0c90699f23b86b14520488609c0882998000b58001a727d89c8138718a704e1cf87e840160a089279d127191506e17619619f8000b906300020e1c10c30948d00830001f68a1a7a96fa5c0001679139dea928f111da021bf8a98020001db17ea1205f00021306b9580ae05b24010c8000ca04f9950941ba9b815594d0088661370000af8240210000be26e04f00000019d00000000c0001a20481c58000f92190002338b32778ff0c001f8001bd0fa884a4d96e1b29fca1f87388b8001472971ec8001458001e28000001daa7ea4995d1e026c2382478aea5580009d00000000fa508001532630000001c79a0800118a298000000c81431ef0e31bf1fb8d48778cda3a8468f8158982a8a82586d17e05a13f8d79778e00bb00022b80002e2208e897717507c8bc25a0041b51e1a068000a60001958dd85014283480018e294120205a1d19a80004b800183a96a7c8001cb8dc9d68839e20000968db12087627f81b1dd1251220a79bba74000212a259a60759c180028f2419fa84097a0efa481e72260b526727727d086a7c23319108fa5b80728c15d80008003f8bf8000fc8002660ff80000000000025880000028d1b30000452748c09cca0626111016898092c80016818c800000105a2300025484c23a00006406880000000b822a1b00001e80000027380000000006292d0000ce8001f980000000000006e8600001628000002689521ab9c98000001ff0f38389238690ada0c0000df28980008b22f10400008c2110001f300000000000000004d9888002698319a98000000b192907100007d0f52151880a302f23280013387718c00000000023680000025980001819400000016da5e0e6a85800000134989a3d80a252a752440588e60460b990da67a3502802fa539a10028528d601a1651c6a6ca7893ea4098b91111607b22e13e0c7a4a9308889dc0001e62450bd000228287011800222a7f21a96a28d8001c38000000000002470001fe900926a49170a4b08f07313112a1511988da9ed9ee1f409e07c24d119000209a8e8000af0001f21a199182605b9931d09a525b1d419e82994e93ca800900620cb0fd1d516193301085985093d08d0a280007800023611799c9e991b0d98f608181b9e828f8e70d18f68c21a2a8392b9aa85793b08120d88c90615ea7106d8851df8000000ba8001e49351098698fe000159197a520ee82e8670ca80014022d8000d1170000
  | 9 => 0x39979a2411e26b8002389ec05d8000000a10278008001b600023e0652948289120000ad2540cc02b0000358ab80000000017884910f18424e8448e210483d86a0000d807b9dda189f884a81c14f2852819b49fd9088110db89da530000678e78742028e81d912c0841d21050d8a341300000b49002879639908000bd800187a2d2989eba3082208ea6d2552642358002179ea8000728b409ba449e085e09303c8859540002428f98a50000001e50c60
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x98e0d6358a548c70739ac52a463835cd6295231a1ae52a48718d0d72951438c686b94a999463435ca544ca31a1aeaa126518c1d76953318c686b94a998c638395162cc631c1aa8b108698d0d74149324c742a10c299263235ca648c531a1ae42a28618d1970151430c616b90c8a8063435cf6550a21a1ae9b2a6510e0f635095088707b2264a8443135ca63d512185ae5326a690d2970d4d4208686baca6a10438359542cc821a1aeba126410d4970d513208686baca899043c254d4294021e12a8994a010f09424ca5008695baa84a8043c294d4254021e12a6a12a010d4b754c950087852a264a8043c25513254021a92e7212a010d61719095008784a1664a80434a5d23254021ac2e3192a010f0b424c95008784a1264a80434a5d32154021a92e790aa010f214288550087a099442a8043c8d092154021e866490aa010c4d7298e51d0286b9ca4a1481235ca6390640c1ce8b10a6a060d745885350286b90a7a1a81435c85350d40a1ae429e84a050d7214d425030732a8499281435c853d0540c18a6b1682a050d7214d4150286b90a7202818354d6210c40a1ae529a842050d739494210307b2a8499081c15093294440a4ae421aa220705424c95110246b94c7208818398d5290440c2cc6a8c822048d7218d401030631aa4a00818518d5150040a1ae42a2879842d7299251cc307aa2c421c61435d2524ca3091ae5324631860d63588544c30739ac42a261835cd6215130a1ae42a4869850d72151434c286b90a999261435c8544c930a1ceaa12649841d76153314c286b90a998a618315162cc530a1ae42a2629850d72152304c286b90c6aa061835516210c30a1ae52a2641850d74949320c287baa8499061c15093294430a8ae421aa218705424c9510c246b94c91886107dd9548c430c1cc8a94621861664546310c246b90c898061071d9544c030c18c8a92601861464545300c286b98caa12410b1d95350920a48e2a9a84905a1711814248286ba0ca99241131d9544c920a88e2aa264905c1711813248306b1a8428a41835913214520a1ae7292841050d725513208286ba4a49904143dd5424c820c1ecaa126410705424ca5108382a1264a88418a5516008420c92a6b00421044d7298f54c4216b94c9a9e21435cc5250b10a1ae8292658844d7218d5484216b90c8a9c21435ce5250a10a1ae9292650860f64d8f5244306b22c6292218a5916014910c92c6b00a488661615805244286b90a6a1221435cc5250910a1ae42a2648850d7414932442873aa8499221431d5424c910c1ccaa12648860c6550932442923aa8510a21511d53288510c50caa124088648654c92044306b22c729021835916354810a1ae529a840850d739494204286b94a899021435d2524c810a1eeaa12640850d755093204307b2a849902183595424c810
  | 1 => 0x10e8b2a0f144ad2c9b9a2b542b2506303aa41620000090fad40588400ca001180073680a0000000034005515a4912c75418c0000000004a383b0013ad50011110363120536bd0d0018811630c548dc3d25c00be5286c0abf1989818d96f00c006400138de083f13400af1ea8c00343c234b60020874f6601bb887cb734ae000005004130a670000006b5900000003a00008db00121588e000e978b46ea4c007900801180017179a60024a0800ba0a800121f612e400b0391489471111f186002d160ba613508d9a2f6b14400006400024d21613000864facc3cd71db000e5071b6128324ab7c0056000e400004b12db4350c8001c4f4891ca60000000042a2003cb83f6097c869c5599c40005d800002d0015c00007080100aa00000fe133680000840a32c380632a7800cf000000000000002c2945060000a21000ee2700314d8ae5b000e099331a14ece54b31428f4d05c8a00820040d000000c0a0000c00060082000050000c040301804300b0001404020f00404010502814050000014160102000080080000140103802030780c0c030800804070801c0000028180a000080000000c0083a0091ae5b0a8621c8d721814310e4ab88c0a188743dc94354843a1eeaa1aa421d25719915210ea2b8cc6a908743dd94354843a1ee2a1aa421d0c7050d5210e8bb8a87288878354d6214f4291ae730ea4a148f735835250b06aa2c42a665831954350932a4ce3b2a849948d74987524ca47ba2c1a9265319c66550932b0ce3b2a849958571d95424cac338ccaa1265615c66550932c1aca32a849950e75d85424cb42b08c2a126561dc56050932b08e2b02849950e75181424cac3388c0a1265615c4605093291eeca16a29970542544514cb42a16c2a8265a1508615413291eeca10a09968542984504cb42a12c2282658354d6210f41a1ae529a85a0d0d7394942d0707b2a8499683839d16294e41c1ae8b14a720d0d7294f4390686b94a6a1c83435ca53d0a41a1ae529a8520e0d655093290686b94a7a0c838394d62d0641a1ae629284a0d84715093250646b94c720a83135c86354041a1ae431aa998e0d5458843cc686b94a899663435d2524cb31a1eeaa1265
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0xd190cb6000000000004402a000380000000000000501204000490581dd94354843905811c14354843a05819d16294e41a05819cd629523180d8795162cc631a05819d16214d40a058298d5190440a058218d5150040a05819cd621513080d8715162cc53080d87991528c430a0582991518c43080d87191524c030a0582191514c030
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 228
  | 2 => 14
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
  | 6 => packedAt s3K6 (788+((h/14+packedAt s3K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s3K5 (27582+((h/296+packedAt s3K5 (24030+(h % 296)*12) 12) % 3041)*11) 11
  | 4 => packedAt s3K4 (55826+((h/446+packedAt s3K4 (50920+(h % 446)*11) 11) % 1609)*12) 12
  | 3 => packedAt s3K3 (11856+((h/76+packedAt s3K3 (11172+(h % 76)*9) 9) % 301)*9) 9
  | 2 => packedAt s3K2 (864+((h/4+packedAt s3K2 (840+(h % 4)*6) 6) % 36)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfe1ffff0ffff87f83f0fc3ffe1fff83f44f3cf
  | 1 => 0x3fe1e1ff0f0ff87fc7f0fc387e1c3fc7bb4d33
  | 2 => 0x3ffe01fff00fff8ff800ffc07fe03ff8c38e3c
  | 4 => 0xc00001fffff0000fffff00007fffc000fc0fc0
  | 5 => 0xfffffe000000000fffffffff80000000fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x2000010000008000001004800240800001045
  | 1 => 0x84484222241500814310441122089286194512
  | 2 => 0x2884954442aa441a9888aa8255412530c28a28
  | 4 => 0xa1d55988aa83552cedaa220479938192ec0f80
  | 5 => 0x3119910ecccc664f36ccf32711020624f7e000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8eeeeeaeaeaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37263
namespace PEqualNP.Outside.L_meta_37263
open PEqualNP.Outside.L_meta_37263.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xb12000081233a8c500081020bf42bd42df32dd32bf41bd41de31dc31be40bc40df30dd30
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x801810c054818d424ca5aa5a0d354831aca80632d521026aa2205354b30
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
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
  | 4 => packedAt s4K4 (208+((h/4+packedAt s4K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s4K3 (197+((h/2+packedAt s4K3 (189+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf8ffffc1fc3e1fe1fc3f0fffc3f8387f4cf70f
  | 1 => 0xff0787fe3fffe1fe1fc3f0e0fc3fff87b349f3
  | 2 => 0xfff807ffc03ffe3fe003ff00ffc03ff8c38e3c
  | 3 => 0x7ffffc0003ffffc0000ffffc000fc0fc0
  | 5 => 0xfffff8000000003fffffffff00000000fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8110044004420002404012240488812041305
  | 1 => 0x10400888101002040841104404121204114052
  | 2 => 0xa22255108aa9106ac222aa08aa812560c28c28
  | 3 => 0x86b566252a0d54b376a88812f3258132ec0f80
  | 5 => 0xc4c64439b331993d9b33cc9c22060644fbe000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaece8ece8eeeaeeeaece8ece8eeeaeeeaece8ece8eeeaeeeaece8ece8eeeaeeeaece8ece8eeeaeeeaece8ece8eeeaeeeaece8ece8eeeaeeeaece8ece8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37263
namespace PEqualNP.Outside.L_meta_37263
open PEqualNP.Outside.L_meta_37263.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x80f0b30a0003023c38c20580002684d9234341064e5c0290010a2a4c54e8938011800a215a52229200007cc8e440400170801c1045040042ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x4617c548c2faa7185754e30bf294617d528c2fca3185f54630dfa0c61bd418c2fca11877cc230fd984617f544c37ea8984fd5130bf2a2617d544c2f8a8986f151309e2a261df434c3bc86987750d30ee21a617f524c2f8a49877cc930ef19261dd324c3b864985fd4530be28a61bf414c37a829877cc530ef18a61dd314c3b862987ecc130ef18261df544c33ea8987795130eeaa261dc544c338a89877d4930ef29261dd524c3b8a49877d0930ef21261dd424c3b8849877d4530ef28a61dd514c3b8a29877d0530cfa0a61de414c3ba82986750530ee20a61df214c3bc42987748530ee10a61df504c3b6a09877d0130ef20261dd404c3b880985fd5030bf2a0617d540c2f8a8185f94c30af298617e520c2faa4185f94430bea8861bf410c37a82185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3905f54720dfa0e41bd41c83de43907b48720ef98641dd30c82fea9105f95220beaa4417c54882fea7105f94e20ef29c415e53882faa7107754e20aea9c417c53882faa5105f94620bea8c41bf418837a83105f94220ef98441dd30883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20f721241ed42482fea2905f14520dfa0a41bd41483de42907b48520ef98241dd30483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2106fd0420dea08417e50083be6010774c020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa0e21f641c437a83887d50710daa0e21f621c43ea438877cc310ee986217f54842fca9085f55210be2a4217f53842fca7087794e10af29c217d53843baa7085754e10be29c217f52842fca5085f54a10be294217d518437e83086f50610bf28421df30843f46108774c210fc98421d930843f441087e48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c524437e82887d90510dea0a21f5414436a82887d88510fa90a21df30443f46088774c110fc98221d930443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2086fd0410dea08217e50043be6008774c010fb88021fa10043ea20087e44010
  | 1 => 0xe541067ca820df94c41bea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc6fca598df54b31ef99663dd32cc77e8398ef50731bf286637d50cc6fea918df95231df2a4633e548c6faa918ef552319eaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f78ca31ee194637e518c77e8318ef50631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa92637c524c7be6498f74c931dfa0a63bd414c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f7d0c31ee218637e520c7dca418db94831bea9063ed520c6daa418f78c831ee190637e510c77e8218ef50431ef98863f6310c7ba6218fd4c431bf28063fa500c6f4a018df54031fca806379500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c87dc6590fb4cb21dfa0e43bd41c86fca190df54321bfaa4437e548877ca910cf95221beaa443bd548867aa910df15221bfa9c437e53886faa710df14e21bea94437e518877e8310ef50621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21f719243ed324877e8290ef50521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e510877e8210ef50421f790843f621087da4210fd48421bf28043fa50086f4a010df54021fca80437950086fca7a05f54f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa4817e53903bca7205794e40bea9c81dd53902baa7206f90e40de21c817e52902faa5206f90a40de214817e51902faa3206fd0640dea0c817e509037e81207ed0240bfa9a817c53502fea4a05f14940dfa1281bd42502fea2a05f14540dfa0a81bd41503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52103dca4205b94840bea9081ed52102daa4206f90840de210817e51103eca2205d94440bea8881f551102eaa2206fd0440dea08817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc3be87987790f30eea1e61dc43cc2fca5985f54b30ef99661de32cc3ba6598770cb30bf28e617d51cc37e83986f50730ef98e61de31cc3ba6398770c730efaa661de54cc3baa9987715330efa9661de52cc3baa5987714b30efa1661de42cc3ba85987710b30efa8e61de51cc3baa3987714730efa0e619f41cc3bc83987750730cea0e61dc41cc3be43987788730ee90e61dc21cc3be81987790330eea0661dc40cc2fea9185f95230beaa
  | 2 => 0x1001004010010000020180000004a0080000000000405802000000058140140040600f0300080000700e0000482800000c008030000000080500801404801004040118000120000580701e0100280f0000200280100c05c008000040140181a054040078020040240000000a0240800e00600800801000078000040040002080e0160040080000400c0000600604800001000000028000060040180101e0341982e03200000010000014000040000000000401800400800016000018030000200102000e0000080f004008028000000000481a008008000240320000600100406c0400000004c038060140180201c006004018140060000681600600001012000000088010280040080e0020480d80d0280040180900e03c018080040580880300000801804000004000010000240d801bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7c87a16f10f42bf28e857d51d0afca1a15f54342beaa4857e5390bbca7215794e42bea9c85dd5390abaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42df21a85bc4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332efa1e65dc43ccafca3995f54732bf286657d50ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbe86997710d32f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef90f41dea1e83bc43d06fca5a0df54b41dfa1683be42d077a85a0ef10b41bf286837d50d077ea7a0ef94f41dea9e83bc53d077ea5a0ef94b41dea9683bc52d077e65a0ef8cb41de99683bc32d077ea1a0ef94341dea8683bc50d06faa920cf55241bf29c837d53906fca520df54a41bf28c83bf41907ee8320df94241bea84837f53507bea6a0d7d4d41be29a83dc53506b8a6a0efd0d41df21a83bd435077886a0dfd4941be29283bf425077c84a0ef50941de21283f7415077c82a0dfd4141be28283bf535073ea6a0ef94d41dea9a83bc5350738a6a0efd4941df29283bd5250778a4a0efcc941df19283bd325077864a0efd4541dba8a83bf505077ca0a0ef54141de282837
  | 3 => 0xb331bc900cdb0b18412800800000aa02491a52021800145112725508f221a000000000005f091307546000191bd20eb2c95000530a342d03500091d451f1450001568cf42a2598503e54ccc4070e10682fc2f8fb1be43c338f124e2dc3b2131d444400204410431920000001a94392d000c60002060000000023e136000000001045cd7a8000009913706d0009254b155000000000000000000007f0000001b9fa000000001054aa2314facd17c608ed0784b6000000d527e0000022457c53cce25f52aa096e1635f8751418da1c86192980029a8a5028002ca0018f25e4280683e0003b8000000000004e8a11cf4d2000bf9c80002a0002f914aa814582d4d60012d00025e68c0f930052c4cd40ee35e3b47e2e32666a821a20526504893275ae9cc26b2e32c65cb72595ec5596927b000030002213ca55d0b9e80004540e024000000cf0f300000000000000a5d181db3ee0000011d000a9c358595f4ae97000000005400201000001350003202e90e8003a6c8c000c414c000000005da5a13f2f800000000000216000000001d0910000b30005d4550005248d4c7b14316000a50bd510394840000329c88a00022e7d40015d000000a19dd19cc44b615f664400d287d00014d6c000650cb5318805fa260e0b0e3a00614cb08000698c08385541c48f800156c099016f00000100285606001890005eeafc002c6000350002f35a68fcb38f83be098809485386b9461ec50c284659ed48cacc5b2b653412048ae815c000bf0004644dcd120718c0012709200099c00126198789749e7000cbd4001e000000000b25c45e873994000000a627500071c000005f60010488d1264782315a2c4000000cd00830d8218c13e1dc000d20426240584b2320198d96139c13d3cab84ca06cfca2e2a8320419d21c64f52189a010ab000258000921091243aa0002e99d2928a8de000368b74001311b0000e00e00b0570a992b37e22c3a85b62e3404b93c308bb1848f928cca4ac0b90983ac1d070456a456d10a3e02d41f8d918a1ed1d2d0000000000004324a4518000007fc000630006e4f519562c095522275fc7cc0000000018998000000c98b89ac10a000bc8880a0000000000f20f0002b455cb086b82b000000900100c08452600a1605b484925000484a70995e4638f200058a000142c94623c0002392c8998001b05fe7d93d0143ac0cc0006f000000002bd44ab4411250062abd4e94741a3e8832ce544044000453c20018c80061e0c09c2f030a6c94dac73483fd5aa942b23d49c9ba5947119116657892811aa54e0001779bb1ba7309713e43e25496040470664a58660030060040180901800c0900d0020100801600a038008000060240d0030120100000e0000040100602203c0080700000001801028010018110040000480200000c000000000080
  | 4 => 0x5d0e51ad64a2b51e16b1089b41731f3aec540ba342e4859162cf0002892e8000000002b0545beb848727d3b060091ae73c69a0c5000178000002d931a9492885e000000fc00026aa04db21c2a43d95b869000aed1b97d18200000183000878990000008cd7880041c684000f42bc72cc915b0e692c000005a80015cb2c0ae0004a2891ac000001b5000001720000003bc000006562802721b00000058916000914000000007ed549c63d6154d89280e84d0210e6058290e69fe3301952b97730e8685a2c14069d8c98121fa2052b1104c0000002c356209c8db2a3f86a457a423d201c8e0b84fe04c7b9e051c000ec87a0007d069b0c000970001880fc0d80009c192000000005640012a00045e000362d600036c0780558893c0016a000408d3a6f0000ed752d54447bc600e960a904000a90008082396037088d8ea260c2c18001be4e282990a6c000c68001690009dd730dc0000000001600000000000000460000004c40000017045a00047aee194238101785805ec480e213a5458000033e4d80005c20834580a103846acf714400614404aab000a113e0001fc074bb1e60c8714cd00047a8eca006800000006a18000001478410009d01eade418b300006e000c34002c85e81c8000ac05e001268ec13c000001a00000018e1d10727c93c29e14e000001fd08821c450005606dc81991000985880bb0006cca823641e00800000000b95058c75b6000e1aeb054778898520000009d
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x7300825f654c020c7951300831d544c020d59453008355514c020cb553200836551c8020dc546200826f6548020cb55120083655148020f24c1200827b6548020dc5452008336619531097d8d54c425c6355310c7d8d54c431c63553108f99353c423d64d4f108f99053c423d6414f109b98853c426d6214f108f99352c423d64d4b1097d8d52c425c6354b108f99052c423d6414b109798c52c425d6314b10cd95141c42b76550710cdd9541c43976350710e518d41c42b56488710c795330c431d54cc310e550730c431e544c310c755130c4395414c3109798f548425d63d52109798c548425d63152109b988548426d6215210d6982538423f6454e108f191538431f6454e10c7191538425e63d4a109758f528423f6454a108f191528423e6414a108f590528425e6314a109758c528431e53d0610c754f418431e5350610c754d418435a534c210b6d95308435b654c210e6d913084398644c210e6d053084399414c210b658e208425f63551109718d544426f62551109b189544423f6454d108f191534426f6254d109b189534423f64549108f191524425f63549109718d524423e64149108f590524425e63149109758c52442b564905109d19541443376550510cd19541443976350510e518d41443b36050510ec18141442b564885109d195214439541cc110b658e30443b1418c110e55053044278654c110ec505304435b654c110d6195304439b644c110e619130443d3614c110f4185304439b414c110f49053044399414c110f45053044391414c110f488530443d1214c110b658e20443b141881109e19520443b14148110f848520443b141c4110f44c2104425e63d50109758f540426e62d50109b58b540423d65950108fd85540423d61550108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530425f6054c1097581530423e6414c108f590530425e6314c109b988530426d6214c109e980530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d53548108f990520423d64148109798c520425d63148109b988520427661148109e980520423e64944108f592510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb549410433651504109798e500425d639401097597300431e54cc010c7553300434e52cc010d354b300425f654c010c7951300431d544c010d3949300434d524c010d6941300433554c4010d954b10042796584010d654e100436952840109dd9510043355444010d9549100427b6544010d654d10043695244010
  | 1 => 0xc29d640c530c7150314c2ce620c530b3588314c2da600c530a7587544c29e6495130b6582544c2db6055130a7994544c31e6515130a7584544c31c54d4930a7992524c29d6494930b6582524c29f6454930a7191524c31c5454930b5d85524c2d46154930b6d81524c34d521493097996424c25d6590930b6d81424c2d86050930b6980424c2d96010930a7992514c29d6494530c7152514c2d96094530a7d91514c29c6454530b3d89514c2cc6254530b6d81514c29e6414530a7590514c31c5414530b3988514c2cd6214530a7997414c29c65d0530a7592414c2da6090530b6582414c25f655053097195414c31f6550530a7995414c29c6550530c7195414c21c6550530e5d85414c29e6410530b6980414c2d96010530a7992214c29d6488530b6982214c2d9608853097d95214c25c654853097994214c25d6508530a7990214c29d6408530b6980214c2d96008530c7d53504c31c54d4130e6d53504c39854d4130b6587504c39b41d4130e6507504c25e659013097994404c2ce6210130b3588404c2d66110130b5584404c39940101309798f540c25e63150309b988540c26d62150309d984540c27561150308f992510c23d6494430c794f410c31e5350430cd945410c335515043097d95300c27b654c030d694d300c25e63d53209758f54c823e64d4f208f59353c823e64947208f59251c825f63547209718d51c825e63d52209758f548825e63152209758c548827661152209d584548823f6454e208f191538831f6454e20c7191538823e64946208f592518831e53d0620c754f418831e5350620c754d41883365150620cd545418825e63d51209758f544831e63d5120c758f544823d61d51208f992544823e6515120cb588544823d61151208f992534823d6494d208fd91534823c6454d209dd8553482746154d20cb152424826c6550920ba181424823e64145208f590514825e63145209758c514823e65d05208f197414823e65505208f195414831f54cc120c7153304831f544c120c7151304825e63d50209758f540827661d50209d587540823d65950208f586540823f61550208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209d98453082756114c208f992510823d6494420cd95251083355494420d594e51083555394420cd99251083356494420cd95151083355454420d594d51083555354420cd991510833564544208fd97410823d65d0420c794f410831d53d0420cd947410833551d04208fd95410823d6550420c794d410831d5350420cd945410833551504209798e500825d639402097597300831e54cc020c7553300835651cc020d554
  | 2 => 0x53505218f990504863d64141219798c504865d63141219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530865d6094c21c7951530871d5454c2197d81530863e6414c218f590530865e6314c219b988530867a6014c219e580530863e64944218f592510863d65d0421c794f410871d53d04218fd95410871e5350421c754d410874d53c84219bd95210874d5348421e9505210867765484219798e500865d6394021ce95250087395494021d694e50087595394021d698e50087596394021ced0650087394194021ce95150087395454021d694d50087595354021d698d50087596354021ced0550087394154021dac8550087722154021da485500877121540219798e52d025d6394b4097d8d51d025c6354740cd54741d031d5310e40a798e429031e53d0640c754f419029c6350640c794d419031d5350640cd945419033551506408f99742503375150540c754e43102b96010c40d394e521034d5394840d394d521034d5354840cb90d521032c43548408f596421029e6390840cb54a421032d5210840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440cd99151103364354440cd10d51103364254440cd109511031e53d0440c754f411032e52d0440cb54b411033551d0440a718d411031e5350440c754d411032e5250440cb54941103365150440cb54b401033551d00408fd95401032d5250040cd545401027b65500409b98b54cc26d62d53308f99252cc23d6494b30a799232cc29d648cb30d354832cc23e64947308f59251cc29e648c730a759231cc29e640c730a759031cc2ce620c730b358831cc2ce62d5330b358b54cc2d960d5330b658054cc29e64d4b30a759352cc2d960d4b30a799252cc29d6494b30d354852cc2d96014b309799642cc25d6590b30b658351cc29e6494730a759251cc29e6414730a759051cc2ce6214730b358851cc2d9601473097d9541cc25c6550730c7d9541cc31c6550730e5d8541cc29e6488730a759221cc25f65487309719521cc25e65087309759421cc29e6408730a759021cc2da6008730b658021cc2ce6210330b358840cc2d66110330b558440cc26e62152309b588548c27661152309d584548c23e64946308f592518c3365150630cd545418c31d63d51308f587544c23e64951308f994544c31d63151308f584544c25e65d0d30c7152434c25c6550d30c7d50434c31c54cc930a7992324c29d648c930c7151324c34c524c9308f990514c23d64145309b988514c26d62145308f997414c23c65d05308f995414c23c6550530a7992314c29d648c530c7152314c2da608c530a7990314
  | 3 => 0x13297997434cace62d0d32a7992324ca3e64145328f590514ca7a60145329e580514ca5e63d50329d984540ca7561150329e980540ca7960150328f992520ca3d649483297d95320ca6f654c8328f992510ca3d64944328fd91500ca3c64540329798e52d065d6394b41a798e42d069d6390b41cb54842d065e63943419758e50d06ae62d4f41ab58b53d06b561d4f41ad58453d069e63d4b41a758f52d06b561d4b41a798e52d069d6394b41cb54852d06b56114b418f99632d063d658cb41a798e50d069d6394341a798c50d069d6314341ab98850d06ad62143419798e509065d639424197583535065d6014d41c714f435071f5310d41c714f425069e6390941a758e425071c5350941cb149425065e63141419758c505066e62141419b588505069d60d4d41a798e53506b56194d41add85535069e6514d41c7994535069d6014d41c714f525069e6394941a758e52506b56194941a7d8d525069c6354941c714d52506b76154941aed8152506b86054941cb548525063e658c9418f59632506b7614c941ad18532506b6610c941ad584325071f53d4541c714f515079753d4541e514f51506b560d4541a798e505069d6394141c714e505069f6354141a718d50506af6254141ab189505069e6314141a758c505071c5314141ab98850506ad62141418fd9541106776550441cd951411065e63940419758e501063e6494b318f59252cc63f64543318f19150cc71f6355231c7550438c69e648ca319b98a544c66d629513197d8d544c65e65cc9319b98b540c66d62d50319e983540c67960d50318f596540c71c63550318f990540c66e62150319b588540c67a60150319e580540c71d54d0c3197594430c6d56110c31cb952520c72d5494831cb951520c72d5454831d3d0d520c74c435483197596320c69e648c831d354a320c74d520c8318f992510c63d64944318f597410c72e52d0431cb54b410c63f6550431cb949410c72d5250431d354b310c65f654c431d3549310c795414c4319dd95310c73a5494031ce552500c76a5294031da54a500c73b4194031ce506500c73a5454031ce551500c76a5254031da549500c75a6354031d6d0d500c7584354031d68c9500c7583254031ced05500c7394154031d6cc5500c75931540319798f54c865d63d53218f99353c863d64d4f219798e50c865d63943218fd9150c863c645432197d8d548865c6355221c7d8d548871c63552218f993538863d64d4e218f990538863d6414e219e98053886796014e219798e508865d63942219798e544865d639512197d8d544865c63551219ed81544867860551218f993534863d64d4d21c7993534871d64d4d2197583534865e6394d2197994534874d6214d2197580534874c538c9219b19532486e4614c921c7d4f414871c53d0521c7d4d414871c
  | 4 => 0x40003a34a6551a0512ce5495426f000001900041549004a8c915aa7c5d96412c4bd3624e652194d79dc0006b9392152b2000339aa0e49f8c19fe3fa948682291648751917e32c698539bd622cd82bb6b20a9340094b59ca5da63695ca000039615526a52e0b9132ce1b50986a2735a92ad62c554ce01e4047758717c204869958421448cc2282511c8251e8a05c0bd87a878502b040026212e11c7d80009a7d5610004a06c0292da000000002180000ec0033b572d98919f004c9e1329ca3500004101b0dad843794438a1c1b80845008a1ab8006fa0dc058621be000002b80002f4002c7488231a10f00ec001061b60b45b9ac8142cc6e06430636a354bc28a020dc8bb8da01e8ac3e33e0b07852a33105ca392317a65e9797482c59850c7780041e98ca303f2201019fa53380d51af0003621ac903561fadc40019028051cccb6503e6055994d0e27cd171db1bc0015a1500009595218665071c0019e000000662f23de204002116f4c709e1f2000061a19136bac6d741150004e082021000dd5aaade178db4332e33280e400193252bbd7080c148d05afb276b82cc089b71fe955bc09e6964b863000000724732bd0007e0a62b6522634a29e42346f804ae726c00087ab742c8bc8b800000578cb8038160060000400100c0040700403200008804008010000060040040401f016000008000000500181b012044098050000000000100800401000004008000010020141100801a0040100700a038000150000000000105800c028010020000000d000018000020160140480000004c14000006018010040000c000003046000000000000743080600002401008008018000030060bc000040220040001101604405808002010038020020040580001a000008050040000600000e014038380180080080200a0100381b004038030000080080100b0000200a80101800800026014004008080dc0040602700400000011002000040020000240180000a02802800004098000020100640100000011c0680200e1040180e01a0600a8010160744c022012000028010140000700200e0202401c04c0040000e02e048030010020f41a0060de0540080c0080000000d0000000000002005c030000101740003a01001c010050080080280301c0900000e0100280500000201409000004010098040000100000100401400009000008048070060040000104c000020078fd954310e5f6550c439798e50d0a5d6394342975825390a5f6054e42c794f4290a5e63942429758e5090aae6290d42a798e4250a5e63141429758c5050a7661141429d5845050a3f65508429bd954210a5f63544429718d5110a5e63940429758e5010a7a60d53329e58354cca3e64947328f59251cca3d61952328fd85548cb1e54cca328f992518ca3d64946329d986544ca756195
  | 5 => 0x136a041b60f9069d61f8788e794a3d2710190f955c0001800051e0000018f24c8e000000000bc029800000000e631818e5255796d1cec5c0016a3b2a1c3d37b086de5278000004f474000000c1d4400026aa8800000386669ad00056a1f8e32823f2000c500000028c370000006b00021e3f8ce97a8a93905d40000d000d805ab32124914ae299216cb8091d42241a47904f006c0d788556ce6d0002ab672da18a85e3ccc9867890448020001745baa740017350a17c6b00002c709249eb5b2ddc000c20007800000003ab6098ac000c0002809325a3d99aa13000a107987333aaeca7b7c3a0a84000003dc818000f1000c4c002fa61892d6692b3660000002f4f2af1850000008a8002cb0007d1002923bc9d90395b000b41690ec0685b0e984b4e64715019f24a691bb1426c6cf4ac349276424542584401d14190d48ea340c8000c2a98fba5910c001a80f43ec8d90a122000ca8aa1374584212f8176048fc9f1ea460000489d20005586035343826cab8ed5a89ad1e2120feb545b89469e0000004c0fa95d3e8e33ca001b71894f4bac001416c875c8e8800b80e10434d4f6b88002943422e1348334625899229b4ee4e80a9e35605c45891631847d208832c65c0002ca3e279cb41ed666d014e3224d4bf0c394e5581b0272966de0d57c991094c348a2a559298013a266028f8000cb6162d933800000b450da3a0006212d2511a8c40222102a61ec0d2011680007c0003b4ac933119356000b592c00016537000078c6400000040ba8fd85463a000990fe1cab4c000006084904410a1b200000000038bb5070a50c8000000006b6bf8469016123b8002f7000a4d67875416174458dd4c246113ae61946143c8eb000001ba1cb444381050000005f4000ea07a4002400057e5c80000058cb596b87744a0b49a176158544608002f249da38af156c14000d13d0a40000fa000000570004e296c000001ee69c00133000284722175fe1056da751b8c20448e10000000016f13e4780017f0d4aa94f18e00000161a860007fda331f35ab9053268446a54d93341380009f82a336a6083aba260cdd5f27037e990001df40a70546000000bb815b2366040d10969690c51b99fa17c521960ba000594ec000188928dd0854907b06185b47636116822254d11a700e0260a02b2c55628dd5195a48434db109a4feb7d762892720157d831300028ddac42be68db6000004c789425d00090d6e16051662c8631a2229f03188764a000001ce1603148d80000000045184092d291a8005fa4397a1820d0d15640293440000008f2423a4001a0600000de2a719a0013a0365345ec6704665ac3dac0606786e5908004986487110613a00000000406000001985e674400000000574000d20008e400000624be10f9d51ae08c120bf00086
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2081000021801c98000197000015800000100000001300000e8004800016800000040d858c9600108911050e1491998f0b0a0786129208071e800aa0150b8f80189b9c1e1f03800c1b06831a9d829f8d19138017940009801a00088000801d2100020010900000701020c280020010100043010000a038b2e031aa22143571191500cb0c298c0a92834a1c15214941962e030a64a0d197014c505070629ac428283515c4435483192ae33246418e0e6454a320c782a928298863545c44354031a34e9192a018f11414c5500c670b80c299243079db5350521e0aa6a0a4210f21414855008694b8086a9081265c26390840c1cc6a9484205317010d511028b39c84a8881265c06350440c18c6a92822041d76150314c28ab88a818a6183151620c530c28a830aa49854471548524c268b88c0a1261455c45414530c18a8b10a29841e75995414c20e3aac910a61a25894010130d22c2a00809841c7654d4188270b88c0a1241079db544c120e12a89824010741514c1200820e3b2a898621251d9414c310838eca9a830849876505308430a328c6a0a21645c06350510b22e630282886906318141442d0b90c0a0a21251d9414c110960eca0a60886186519130442c8b88c898221645d0614c110d20c830a60885c17218530442c8ba48298221261d9414c1109a0eca0a60886937650530442c93b28298221641d9414c110d20eca0a60884907650530442c8ba44298221a458d4188110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x42d4000000030e01802d4b8a020806000009421a098014d6214141a0581991528c831911819d23254031a098098d5290840911809ce4254440a098018d5250440a0581151620c530a05811516214530c10655c06350510c80635c86050510c10655c4644c110c80645c8614c110892869d9414c110890865d2214c1108908758d4188110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 820
  | 4 => 894
  | 3 => 68
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
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (788+((h/14+packedAt s5K6 (704+(h % 14)*6) 6) % 53)*7) 7
  | 5 => packedAt s5K5 (25143+((h/273+packedAt s5K5 (22140+(h % 273)*11) 11) % 1083)*11) 11
  | 4 => packedAt s5K4 (37250+((h/298+packedAt s5K4 (33972+(h % 298)*11) 11) % 1073)*11) 11
  | 3 => packedAt s5K3 (3486+((h/22+packedAt s5K3 (3332+(h % 22)*7) 7) % 99)*8) 8
  | 2 => packedAt s5K2 (925+((h/5+packedAt s5K2 (900+(h % 5)*5) 5) % 26)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x87f8ffff07f1f1f878e3e3ffe3f070fe0cf70f
  | 1 => 0xf87f078ff8fffe3f80fc7c707c7fff0e3349f3
  | 2 => 0x7ff80fff01ffc7ff007f807f807ff1c38e3c
  | 3 => 0xff80000ffffe0007ffff80007fff8001fc0fc0
  | 4 => 0xfffffff000000007ffffffff80000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x90081101100222000820809120911024041305
  | 1 => 0x2104012204080410044242204242408114052
  | 2 => 0x652222244225400ab100490449024ac0c28c28
  | 3 => 0x3106b54894a06494daa90009724b02656c0f80
  | 4 => 0x4644c600e6c9892764d2724e000c0c89bbe000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeaece8feeaece8feeaece8feeaece8feeaece8feeaece8feeaece8feeaece8feeaece8feeaece8feeaece8feeaece8feeaece8feeaece8feeaece8feeaece8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37263
namespace PEqualNP.Outside.L_meta_37263
open PEqualNP.Outside.L_meta_37263.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x80a000c72652896a35480b1f5cbd9064a60a2c18fc0000449f0050dc5853a2089978e50847400080683c3804e00b9300f400956cdb0000d4e1e7690000006dc0d6000000625401a2c0008001044008214020800004a030e29000027fd5009fe54027f55009fc5401ffd4c07fe5301ff54c07fc5301ffd0c07fe4301ff50c07fc43027fd48097f52017f94809fd52005f54805fc52007fd0805fe42007f50805fc4201ffcc805fe3201ff4c805fc32027fd4409fe51027f54409fc51007fd0401fe41007f50401fc4101ffcc407fe3101ff4c407fc31017fc8401fe21007f48405fc21027fd4003fe50027f54003fc50007fd0003fe40007f50003fc4001ffcc007df3000ff8c007fd3000774c003fc30017fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x824005ffd971002dfecb88017fe65c40097f32e2005ff59710055facb88017fc65c400b7e32e2005ffd931002dfec988017fe64c40137f3262005ff59310005fac988017fc64c400b7e326200affd5310057fca98802bfd54c4015fe2a62005ffd8f1002dfec788017fe63c40077f31e2005ff58f10065fac788017fc63c400b7e31e200cffd4f10067fca788033fd53c4019fe29e200cffd0f10067fc8788033fd43c4019fe21e2005ffd8b1002dfec588017fe62c40057f3162005ff58b10005fac588017fc62c400b7e316200affd4b10056fea58802ffe52c4015fea962000df54b1005ff8a588003ff42c4017ff2162000ff50b1005ff88588033ff32c4017ff196200cff4cb1005ff86588006fe61c400bffa8e2005ff9471002feca388017fd51c4015faa8e2005ff1471002ffe8388017fe41c400bfb20e2005ff50710007ea8388017fc41c400bff98e2005ff8c71002ffa6388017fc31c400bff90e2005ff8871002fec4388017fd21c4001fa90e2005ff0871000dfac188007ff50c4003ff2862001ff5431000ff8a188007ff40c4003ff2062001ff5031000ff88188007ff30c4003ef9862001ff8c31000ffa6188007dd30c4003fe1862001ffc831000ffc4188007fd20c4003fe1062001ff8431000fec2188007fa10c4003fe0862001fd04310047feca88022ff6544001bfb2a20009fd9510047fcca88012fe6544011feb2a2008bf59510047f8ca88012fc6544011be32a20049f19510007fec888002ff6444001ff3222009bf99110007fac888002fd6444001fe3222009bf19110047fea888023fe5444011feaa22008ff15110037fec68801aff634400dff31a2003bf98d10037fac68801afd634400dfe31a2003bf18d10037fea68801bfe534400dfea9a2006ff14d10037fe868801bfe434400dfea1a2006ff10d10007fec488002ff624400fff3122002bf98910007fac488002fd624400ffe3122002bf18910047fea4880237f524400fff2922008ff54910006faa48801ffc5244001ffa122007ff90910007fa848801ffc424400dff9922007ff8c910037fa648801ffc32440037fb0a2008ffd451002ffca288023f65144011fea8a2008fd5451002ff8a288003ff414400bff20a2000fd90510007fa8288003f5414400bfe20a2006ffcc51002ffc628801bfd314400bfe18a2007ffc851002ffc4288003f62144001fe90a2000fd4851002ff84288006ff6044003ffa822001ff9411000ffaa088007fc5044003ffa022001ff9011000ffa8088007fc4044003ff9822001f7cc11000ffc6088007fa3044003fe9822001f74c110037f26088003d93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff104400bfd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x37d5250023fe2928009ffd09400077e84a0047fe4250001fea128000ef5094004ff884a004bff3250023ff1928012ff4c94008ff864a0003ff61500017fb0a8000ff98540007fac2a0003fc615000b7e30a8013ffd454009ffca2a004ffd5150027fe28a8009ffd05400077e82a0003fe4150001fea0a8000ef5054004ff882a004bff3150025ff18a8012ff4c540097f862a0047ff2150001ff10a8000ff4854008ff842a0006ff6050003ffa828001ff9414000ffaa0a0007fc5050003ffa028009fed014000ffc80a0007be4050003fe2028001ef1014000ff080a0007ff3050003ef9828001ff8c14000ffa60a0007fc3050003ff9028001ff8814000ff840a0007fe1050003fe0828010f7d9530087bcca98043dd654c021ee32a6000f7d9130007bcc898003dd644c001ee3226010f7d5130087bca898043dd544c021ee2a26000f7d893007fbcc498003dd624c01fee3126010f7d4930086bea49803fde524c021eea926000d75493007fb8a498003df424c01fef2126000f75093007fb88498003df614c001ef30a6000f758530007b8c298043df514c021ef28a6010f754530087b8a298003df414c001ef20a6000f750530007b8829803fdf214c001ef10a6000f74853007fb84298007df604c0036fb026003f6d813000fbea098007de504c003eea826001f71413000fbe8098007de404c003eea026001f71013000fbe4098007de204c003ee1026001f78413000fb42098007dc104c01dffb2a400ebfd9520077fcca90012fe654801dfeb2a400ebf59520077f8ca90012fc6548001ffb224000bfd9120007fcc890026fe6448001feb224000bf59120007f8c890026fc644801dffaa2400eff95120077faa89003bfc544801bffb1a400dbfd8d2006ffcc69000efe634801bfeb1a400dbf58d2006ff8c69000efc634801bffa9a400dff94d2006ffaa690037fc534801bffa1a400dff90d2006ffa8690037fc43480037fb124002ffd4920016fea49000bfe5248005f72924002ff54920016faa49003bed5248001b6a924002ff14920017fe849000bfe4248005f72124002ff50920007da849000bfc4248005ff9924002ff8c920017fa649000bfc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4005bf18520077fea29003bfe514801dfea8a400eff14520007fe8290003fe4148001fea0a4000ff1052006ffe6290037fe314801bfe98a400dff0c520017fe429000bef2148005ff10a4002ff48520007da429000bfc21480037fb024001ffd412000ffca090007fd5048003fe2824001ffd012000ffc8090007fd4048003fe2024001ffcc12000fbe6090007fe3048003fe9824001f74c12000ff86090007ff2048005fd9024001ff8812000fdc4090007fc2048003f61024001fe0812000ffc2090007fa1048003fe0
  | 2 => 0x210c7fcc69080efe6348431feb1a4218bf58d210c7f8c69080efc6348431ee31a4203b718d210c7fea690863fe5348431fea9a4218ff14d210c7fe8690863fe4348431fea1a4218ff10d2102dfec49080bff5248405bfa924202ff94921017faa49080b7d5248405fe2924202ffd0921017fc849080bfd4248405fe2124202ffcc921017fc649080bee3248405fe9924218fb4c921017f8649080aff6148433ffa8a4205ff945210cffaa290817fc5148401ffa0a4205ff90521007fa8290817fc4148431ff98a4205ff8c5210c7fa6290817fc3148405ff90a4202fdc852102ffc4290817ee214840bfe10a4205fb08521017e84290803ff60484017fb024217ff9812100dfcc090803fd604842ffe3024201bf181210cffea09085ffe5048433fea824217ff141210bffc809085ffc4048431ff9824218f7cc1210bffc6090863fd304842ffe1824202ffc8121017de409080bfe2048405fe1024217ff8412102ff82090827ff65d00137fb2e8009ff99740025fccba0027fd65d002d7eb2e8009ff1974004df8cba0006fe64d0013ffaa68009ff9534004f7ca9a0027fd54d002ddeaa68009ff1534004ffec7a0026ff63d0013ff31e8003bf98f4004ffac7a0056fd63d0013fe31e8003bf18f400affea7a0057fe53d002bfea9e8015ff14f4004ffe87a0027fe43d0013fea1e8009ff10f4004ffec5a0027fe62d00057f3168009ff58b40005fac5a0027fc62d00057e3168016ffd4b400b6fea5a0053fe52d002dfea968000df54b400a7f8a5a0027ff42d0013dfa168009ff90b4004ffa85a0003bd42d0013fe2168015ffccb400a7fc65a0057fd32d0029fe1968009ffd874004ffcc3a0016fe61d0013feb0e8000bf5874004ff8c3a005bff51d002dff28e8016ff547400b7f8a3a0027ff41d0013dfa0e8009ff9074004ffa83a0003bd41d0013fe20e8015ffcc7400affc63a0057fd31d002bfe18e8014ffc8740007fc43a0003fd21d0029fe10e8001bf5834000ffea1a0007fe50d0003fea868001ff1434000ffc81a0007be40d0003fd2068001ff1034000f7881a0007ff30d0003ef9868001ff8c34000ffa61a0007fc30d0003ff9068001ff8834000ff841a0007fe10d0003fe0868013ffd954009dfecaa00037f65500013fb2a8013ff99540025fccaa004ffd65500277eb2a8013ff19540025f8caa004f7c65500093e32a8001bfd914009ffea8a0027fe5450027df2a28013ff5514009f7aa8a0027fc5450025ffb1a8012bfd8d40097fcc6a000efe6350025feb1a8012bf58d40097f8c6a000efc6350025ffa9a8012ff94d40097faa6a004bfc5350013ffa1a8012ff90d40097fa86a0027fc4350001ffb128000bfd894008ffcc4a000afe6250001feb128011ff18940015f8c4a004fff5250027bfa928011ff9494009ffaa4a000
  | 3 => 0xf2828224ff5414110ff8a0a0887fe4050413fe2028223ffcc14111fbe60a0887fe3050447fe9828221ff0c141117fe40a0887fe2050443fe1028221ff8414102ff820a0817ff651040b7fb288205ff99441025fcca20817fd65104417eb288205ff1944102df8ca20826fe6410413ffaa08209ff9504104ffaa820827fc541040bffb188205bfd8c4102ffcc62080efe631040bfeb18821fbf58c4102ff8c620816fc631043fffa98821fff94c410fffaa62087ffc5310413ffa188209ff90c4104ffa8620827fc431040bffb108205ff98841015fcc420817fd62104017eb108205ff1884102df8c420883ff5210441bfa90821eff94841107faa4208037d521043dfe2908209ffd084104ffc8420827fd4210413fe210821fffcc8410f7fc642087ffd321043dfe1908205bf9844102ffea220817fe511040bfea888205ff1444102ffe8220817bf411040bff2088205fd9044102ffa8220817bd4110413faa088205ffcc44102ffc6220817fd311040bfe1888205ffc844102ff84220817ff601040bff3008201bf9804102ffac020802fd601040bfe3008201bf18041107fea020877fe5010441fea80821dff1404104ffc8020827fc401043fff980821ff7cc0410effc602087ffd301043bfe180821effc80410effc4020877fc201040bff0808205ff0404102ffecb10816ff658840bff32c4204bf9962102ffacb10872fd658840bfe32c4205bf1962102ffec910816ff648840bff3244209bf9922102ffac910802fd648840bfe3244205bf192210e7fea910873fe5488439feaa4421cff1522102ffec710816ff638840bff31c4203bf98e2102ffac71086efd638840bfe31c4205bf18e210dffea71086ffe5388437fea9c421bff14e210dffe871086ffe4388437fea1c421bff10e21015fac51080bff5288405bfa944202ff94a21017faa51080b7d5288405fe2944202ffd0a21017fc851080bfd4288405fe2144202ffcca21017fc651080bfd3288405fe1944205bf9862102ffea310817fe518840bfea8c4205ff1462102ffe8310817fe418840bfea0c4205ff1062102ffe6310817fe318840bfe98c4205ff0c62102ffe4310817ef2188405fb90c4205ff0862102fe84310817ff608840bff3044201bf9822102ffac110802fd608840bfe3044201bf182210e7fea11086bfe5088439fea84421aff142210d7fc811086bfc4088437ff984421bf7cc2210d7fc611086ffd3088435fe1844202ffc8221017fc411080bfc208840bff0844205ff042210cffeca90866ff6548433ff32a4204bf995210cffaca90866fd6548433fe32a4204bf19521007fec890802ff6448401ff3224209bf99121007fac890802fd6448401fe3224209bf191210cffea890867fe5448433feaa24219ff151210c7fec690862ff6348401efb1a4200b7d8d
  | 4 => 0x8b3ff52d0459bfa96822aff94b41167faa5a08037d52d0455fe2968209ffd0b4104f7e85a0827fe42d0413fea168200ef50b4104ff885a08afff32d0455ff196822bff4cb41157f865a08b3ff51d040bff28e822cff5474102ff8a3a08afff31d040bff18e822bff4c74102ff863a08abff21d040bfe10e8209ffd834104ffcc1a0806fe60d0413feb068200bf5834104ff8c1a0806fc60d0459ffa868229ff94341167faa1a08a7fc50d0413ff2068209ff1034115ffe61a08afdf30d0453ff186822bff4c34114ff861a08abff20d0453ff1068229ff0834114ffc21a0817fc10d040bffb2c8205bfd964102ffccb20812fe659040bbf32c82049f9964102ffacb208a2fd659040bbeb2c82009f5964102ff8cb20816fc65904477eb248228ffd524104ffca9208a3fd5490413fe2a48205ffd8e4102dfec720817fe63904077f31c8205ff58e4113dfac720817fc639040b7e31c8227ffd4e4113ffca72089ffd539044ffe29c8209ffd0e4113ffc872089ffd4390413fe21c8205ffd8a4102ffcc52080afe629040bfeb148200bf58a4102ff8c520816fc6290451ffa948228dfd4a41137fca5208a3fd5290401bea948226ff14a4104ffe852089bfe4290401fea148209ff10a4113ffe652089bfe329044ffe9948226ff0ca4102dfcc320817ff519040bff28c8205ff5464102ff8a320817ff419040bdfa0c8209fdd064102ffe6320817fe319040bfe98c8205ff0c64102ffe4320817fc219040bffb048205ff9824100dfcc120817fd60904017eb048205ff1824100df8c1208a3ff509044bff2848228ff5424112ff8a120897fe4090413fe2048227ffcc24113fbe6120897fe309044ffe9848225ff0c241137fe4120897fe209044bfe1048205ff8424102ff82120893ff65504497fb2a8224ff99541025fccaa0893fd65504497eb2a8224ff19541025f8caa0893ff5450449dfaa28209ff95141127faa8a0827fc5450449de2a28223ffd8d4111dfec6a0803df63504016fb1a8223ff98d4101dfcc6a088ffd63504477eb1a8223ff18d4101df8c6a088fdc63504076e31a8223ffd4d4111ffca6a088ffd5350447fe29a8209ffd0d4111f7e86a088ffe4350447fea1a8223ef50d4104ff886a0803ff62504017fb128222ff98941015fcc4a0803fd6250445fe3128202bf18941127fea4a08937f5250445ff2928224ff54941006faa4a088bfc5250413ffa128200efd0941117fc84a0803fd4250401dea128209ff1094111ffe64a088bfe3250447fe9928222ff0c941127fea2a0817fe5150449fea8a8205ff1454104ffe82a0827f7415040bff20a8205ef9054111ffe62a0817fe3150447fe98a8205ff0c541117fe42a0817fc2150401ffb028200bfd814110ffcc0a0806fe6050401feb028221ff1814100df8c0a0893ff5050443f
  | 5 => 0x8152016f840a90cf7e1054867be082a409ffd974204dfecba1027fe65d08097f32e8409ff59742195facba1027fc65d08137e32e8402bf9934204ffea9a1027fe54d0813feaa68409ff1534204ffec7a1026ff63d0813ff31e8403bf98f4204ffac7a10c6fd63d0813fe31e8403bf18f4218ffea7a10c7fe53d0863fea9e8431ff14f4204ffe87a1027fe43d0863df21e8409ff50f4204ff887a1027bc43d08057eb168402ffd4b42016fea5a100bfe52d0805fea968402df54b42017f8a5a100bfe42d0805df2168402fb90b42017f885a100bbc42d0805ff9968402ff8cb42017fa65a100bfc32d0813ffb0e8409ff9874202dfcc3a1027fd61d08017eb0e8409ff18742197fea3a10cbfe51d0865fea8e8432ff1474218ffe63a10c7fe31d0863fe98e8431ff0c742017fe43a100bfc21d0813ffb068409ff9834200dfcc1a1027fd60d08017eb068409ff1834200df8c1a10cbff50d0861ff2868432ff54342187f8a1a1027fe40d0813fe2068431ffcc34218fbe61a10c3fe30d0863fe9868430ff0c342017fe41a100bfe20d0805fe1068430ff84342187f821a10bfff655085f7fb2a842fff99542025fccaa10bffd655085f7eb2a842fff19542025f8caa100aff645085fffaa28409ff9514217ffaa8a1027fc545085dffb1a842ebfd8d42177fcc6a100efe635085dfeb1a842ebf58d42177f8c6a100efc635085dffa9a842eff94d42177faa6a10bbfc5350813ffa1a842eff90d421777c86a10bbfd4350813fe21a842eef10d42015fec4a100bff5250805bfa928402ff94942017faa4a100b7d5250805fe2928402ffd094204fde84a100bfe4250805df2128402ff109420177884a100bec4250805ff9928402ff8c942017fa64a100bfc3250801ffb0a8400bfd8542007fcc2a1003fd6150801fe30a8405bf1854217ffea2a10bffe515085ffea8a842fff14542177fe62a10bbfe315085dfe98a842eff0c542017fe42a100bfc2150801ffb028400bfd814216ffcc0a1006fe6050801feb02842dff1814200df8c0a10bfff505085bff282842fff5414216ff8a0a10b7fe4050813fe202842effcc142177be60a10b7fe305085dfe982842dff0c142017fe40a100bef2050805ff1028402ff0814216ffc20a10b7fc1050813ffb2e8209bfd974104ffccba0812fe65d0413bf32e82049f9974104ffacba08b2fd65d0413beb2e82009f5974104ff8cba0826fc65d0413ffaa6822cefd534104ffca9a0827fd54d0413fe2a68209ef1534104ffec7a0826ff63d0413ff31e8203bf98f4104ffac7a08aefd63d0413fe31e8203bf18f4115ffea7a08affe53d0457fea9e822bff14f4104ffe87a0827bf43d0413ff21e8209ff50f4115f7a87a0827fc43d0413ffb168209ff98b41015fcc5a0827fd62d04017eb168209ff18b41015f8c5a0
  | 6 => 0x8503122aa0fa98e0008c05da0000000000003760003f882e77407040609e9f42e00008a099817229e27400e7dc01a4041c247601e20851a10c63c4460a80001604c88082200000c676e3980007927f21ea8006ba79813e00000030aa7c00034a0001525900320001322a02d21c409824a52408641a10e0000004100000002c60000641ce83e0005800008589368020e80584ca26e85248674e454290a38a6803456c0784305d882c7a69a64a41e078222a2e60f03d20c4ab86b400000601001803032068078180160000280a00800c0000400c000060030000000000004c0280c0010380000180a0000280300c02e0000080100209c0000100600400008000000058010060840d8080360000000100000c0000000a0080000800200001000000014000000020180200400002c0200101e0040082e0000000000100a00410001020014118030041780400b01800c0900701800002004000000000000000001700300800c0001300e0040b002008074150020360200280303203c0080003600c00807008004100000000080880100600001001006000000000060040a0000140000d80801a0b803800000000008120000f4018010060180000100000802004004000028070060000a00000c0000200600801001001002000030010000340480201c020018080080000081e0000280200000e00c06006000020018040000000c0040000500202b0000180080100c0040280200003800000014008088010300040000b00000c0c80500400006000020018008160840000100d000004068260000080380f0440041e014006048000000000340080400200000005000000090000060040000000e0100201101c0001d800000044068020080180100d0000340000900600c0c00c00e000000080000240700300a00c000081a80080100b01a0281380001e02400010008004090000040040000405e0080300601400000000002000010000120140000d000010010130040000000000c0100080001c00001001000010030010000000000101e01c010050001240a80b0600000080500c00400000012000000020020200400000201009803002000070140040000100402c034028070080b00082b00200c028000020000182100200dfd9152006fcc8a90037d6454801be322a434dfd8d521a6fcc6a90d37d6354869be31aa434dfd0d521a6fc86a90d37d4354869be21aa402dfd8952014fec4a90136f6254805bf212a402df10952016fe64a900b7e3254805be992a402df0c952006fec2a90037e6154801beb0aa400df185521a6fe62a90d37e3154869be98aa434df0c552016fe42a900b7c2154801bfb02a433df98152006fac0a90cf7c6054867bf202a433df101521a6fe60a90d35f3054867bf182a434df4c15219ef860a900b7f2054805b7902a402df8
  | 7 => 0x81e4d20009f216a5e06da0b227c7528fe0000009ba00086e8685c42e4a283ac8ee000000000000000000a7200000057600092a0007fe0000000004ce4800000007320000000009ac000000000504000988000000000000000000000a144ae00089a00000064600000000068e0000001801824085baa980c000097e2bc0000000008f057e000000000256000000878000000000ab21362f29c08a20a60006e24822fe9c20004fa62425a69c8b64b661227200a92c87a6dc01c1226808100b09bc8e83a805c2a452076a7fc71a3aa8820006e02829480008a61120007440005fc6cc7cc7aaa56a8a8f82529fe2702b49405fa5c225417073c38230074a71244e0002d8a2088c03874c0009ea97c000258844a2442490a0002065562b200000062c5ca47804829c000000a8259a1580001f4120502a780004d67be00000028000000010a0000106f000059c896a84626a3007e2b00001e696800098400039a23211c04650a48e6620000005ac7ea0002160306bc8547a42ce7b889e1f64d83ca63866c5a462a3ea3487882a63cc14e7645b804223672a1ee8c83a4114696000a964e80003a6000a5a9124d06988c44e06e856068c1f200084c07459253452e0004ec1de90c9c803a1f03284f80000000009022e8a3e87e5e465c16e7e00000000004960000007ac00068600033494494e7b66d46440000009100006329780007089740008905702d65c6aaa22493aa6ca6250e73e0009b418c1e84ba1563b84263746fa45033275a8f488a2f61ca65631e7e82de9a41263660fc6784a8a0449e95e5067008be5dc07c5ce15e4908ae8489a033052692613484e56804ca643807164661280209e09ce37e2c28a49ee32aa480840009d68ce00c51c6c471816883a9fc05a4142ba8e41402308b24a07c204e73a7245828b46b2aa87f0a9c77628a7c461e5a86105cc960a424f414c86c6c85541d00ea06628c8ec7c8400a7a1fa85c1c091818a0f423e4e43f4372a52a945648946a87d2aa035ca4c7fa28e5b6a5e5d656a1fc07235a3185f847054260664aa660440120047de6a44a26668464f620c08a00011e0ec67400052a2fc22228851610200020478e44000049a2da66a3fea9e29a838474aa215a29678c5d003c3383ee37a11a00010895679e6b600080e8327781ba510a9a000000a368e054a3fca4433a02834e11608093050c17e93e23416604057800002e4b07065be7f80008c20f89f68d86689963203ce7ec4323f61bc94c34452c3d021a9e60a40000180006020000003642380004fea46a5c5620aa0001d60002be49845214477e0001386ae0000003021dc0008d277c00000048a7962cc6402768720883520000000000000000003540003e62508306b83404c07ce99043e4b836e05e1cc00000021829265214a178000a400009d24726500f2a5
  | 8 => 0x417454e5bc30e9d000000000000606e13c00000079c67c0001aa00049c1765a00000000004220000000001da02a00009a62e0ca96491a0000d21d45980000624bc7da000000814a543786ca09ca804dc2460007a00007d05ae92e80419c5ea4629f01b6a0e4ea0d88ac21e55a806aae72c53258aa904d49146725b220a9541d87ca7b40000004c4a886361300002b848424800031a7022d45f200070c8de3109e27340001540004ee000000000000a16748a229e47042a22f44fc0000000002ca00055000053a11005670a7143fa2861903be0ce81827a07a8120e260c36000000087c6aa9ec9580d054491c0c87428647e66923140363c067a38e9f80007b234c6a629400000068a3de71e3904607800000f6a027a899e0008e22026ce00038834600064c38a2b69ae22e2840004449a26ee12c01639c5f468200000000039e1e47280001c692400019a00000064e2780002c408e00000000079476266453c1242ec2f83c40526de3848161427300cc14659e65a96a96278682a9d4a863c28da2d01c886a3869be96e9324da342a120e004a000370a2c06821418e1943e85f61506700003a2a743269da6d66187c07e27563a02007d49343e058677006c976a3c1b01b40000001f854c9b661400000031c2260762c80ba60a65453e7d893c13a42c9523e45ee20e6f845a6b00000003c68f29e88bc6c62424283c88244186428d430884221c00008c00071067e5e245c0600ae6280005f07500007d6a3a55e2288fc8ea00078433e0002666c2000ab00000d60004126a0a002ee8a85305584c263e6d872271c3500005381960dea260003366d28fa41e0009920008400009b26209b80000009660005e890e58800012e0006f200035e0000000009040bc0007380000007f6000a1a12a8c6746a1e40e00036a7363b0a0843c0000540008269fa0000001ae66046ca181b20000000000000000002f03f200098000000000005000000000066e1980ac0b62682e2906a4a0006e60007260e60000000007c69c6000a0c3ec69a61c0d41a80000005fe0000008aa00098c6220be000000ab60003d80dc0960006ac8ca6846d00009381fe2ea0009b07f482878a2126580000006f600016c00086040a000a340005226947ba1929a80005de6c00000000003b4000000a7626a00000095087400094600040297a00000000076090041c0000000b877a90800000000000067600089c6305a68200000b400075442a00051e82233ca2a0002100000005940e400000000018400085a43600000000000000000047c96c00097200061a0000000000000002644e200046e00027ea4e3b60000005840000940c257c8b00000007720001a653695c6fc55c9dc88e60835891659600058c5e65eca8ea7e8f60000008620000000000000004b400069e00000091e4cc8e6768
  | 9 => 0x54036824024499a00200000081c48c7e452851846876c00888836200040c3922a80240920000005c83ae1a060443a30644a8b830c856870000a1c0001e200022c88000000079000086681a8cc3568ba50826c5749204423e200099483c17c32ca588365480000000000003226be000a701641bea0a37c38c00045600000000000000056e000000690188a6a0000a20004645d426298a0000000000004aca2e4f00003da00075899c00000036c2ae32400080c85e0000000001185b44a6a92a3257289860e3b224e60000000031670ea6e0004883ba5d2aa409055206a5aa3bc25e0006f41a4304416aa603e0004f200017a4be9280004204924aa0fe0002600000005467bc5120005141ac6ea4e6000ab49aa00000083446a0009ca79a75e42e47a45e43400019e02244c0a02dc3d66fe97084a0000003dc15c1ec6a27b09de0000000000000009420008d694a80a00025c39616200000045800092200023a65e5c095a72e740a100825a200063a1865b01b80140004486e41d258e24c2980009c40004de4c69820000007ee10600000087657a0da00000000000064888400000032e8d03f050010063489223c4386ec986a8c75c6161a2aac02c8865664b2720000a069d80ee02647e2ac4943d47663947ae1482fa6888dca607a20009cc2c01
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x574885100bdf57288510016f66288510016f4628851003f77528851003f75528851002ff3708851000df6708851000df4708851002ff0708851002ef7608851002ff360885100d7d730885100d7f230885100d7d530885101f7f130885100d7f22088510014ff764851000cfe76485100bcfd764851000cfc76485100067f65485100ce7c6548510005df7348510035dc7348510006ef6248510016ec624851002fe42148510005fb704851000df8704851002ff0104851000df47648510016f4764851000cf476485101edf775485101edf575485100077765485101e7746548510005f77448510005f57448510007d773485101dfd4734851002df7724851002fe77248510007e76248510016f66248510016f4624851003fe4624851003f77524851003f75524851003fe632485101dfe53248510007f3704851000df6704851000df470485100bff0704851002ef7604851002ff360485100bfd730485100bff230485100bfd530485101dff130485100bfe720485100bff220485100bfe52048510037db764c11001edb764c110037d8764c11001ed8764c1101d7db754c1101cfda754c1101d7d9754c1101cfd8754c1101cfdb654c1100075b654c1101cfda654c1101cfd9654c1101cfd8654c1101cf58654c110007db744c110007da744c110007d9744c110007d8744c110007db644c110007da644c110007d9644c110007d8644c1101cfdb544c1101cfda544c1101cfd9544c1101cfd8544c110007db724c1101c7da724c110007d9724c1101c7d8724c110007db624c1101c7da624c110007d9624c1101c7d8624c1101cfdb524c1101cf5b524c1101c7da524c1101cfd9524c11000759524c1101c7d8524c110007db424c1101c7da424c110007d9424c1101c7d8424c110007db714c110007d3714c1101bfda714c110037d9714c1101bfd8714c110007d0714c11000fdb614c11000edb614c11000fd3614c1101cfdb514c1101bfda514c1101cfd2514c1101cfd9514c1101cfd1514c1101bfd8514c110007db414c1101bfda414c110007d2414c110007d9414c110007d1414c1101bfd8414c1101c7db214c1101bfda214c110007d2214c110007d9214c110007d1214c1101bfd8214c11002df87648110016f8764811002cf876481100077b65481101af7865481101b5fb73481101b5f9734811000dfb724811000feb7248110007eb6248110016fa6248110016f8624811003fe8624811003f7b524811003fea524811003f7952481101afe9524811000769524811003fea4248110007e94248110007f3714811002dfa714811002df87148110007f0714811000efb614811000ff361481101aff251481101aff15148110007f24148110007f1414811003feb214811003ff22148110007e9214811003ff12148110007e12148110
  | 1 => 0x8910006bf7458910004bf745891004cfc7458910006bc745891004cbc7458910004ff7358910006df7358910004df735891001cfe7358910004fd735891001cfc7358910006dc735891001cdc73589100d4ff7258910006ef725891003e7f5258910264ff7158910006f771589100bcff7058910006fb70589100bedf30589100bedd30589100067f76549100057e76549100067e76549100047e76549100067d76549100057c76549100067c76549100047c76549100067f645491025e7e64549100067d645491025e7c645491024e7f63549101a67e635491024e7d63549101a67c63549102557f72549100476f725491003e7f62549100167e625491003e7d62549100167c625491000776715491000775715491019e7f615491019e7f605491019f5f305491019f7a305491019f5d305491024f79305491019f6f205491019f7a205491019f6d20549102477b105491019f76105491019f74105491019f78105491004cff76d0910004fe76d0910004fd76d091004cfc76d09100067f65d09101967c65d091004ebe64d0910006bd64d0910006ef62d0910016ec62d091002df671d0910005f571d0910004ff7650910004fe7650910004fd7650910004fc76509100067f655091017e7c655091004ebe6450910006bd645091000cfe76d051000cfc76d05100457e75d05100057d75d05100067f65d05101667c65d0510006bf64d051004ebc64d051000dfa70d0510005f970d05100edf6769051002ef6769051002df7759051002f76759051023df5759051002f75759051000575759051000777659051023774659051010df5749051004ef6649051004ef46490510005f5729051023777529051000775529051000df6709051000df4709051002ef7609051002ff3609051012fd7309051012ff2309051012fd5309051022ff1309051012ff2209051004cff765051000cfe765051010cfd765051000cfc76505100067f65505101267c6550510006bf645051004ebc6450510005df7350510035dc735051002fb44150510005fb705051000df8705051000df4765051004ef4765051000cf47650510225f77550510225f5755051000777655051021f74655051002df7745051002fb77450510007b7645051004ef6645051004ef46450510007b4645051021fb7545051021fb45450510007d77350510217d47350510217b74350510217b54350510005f7725051021f775250510007755250510007b74250510007b54250510007f3705051000df6705051000df4705051010ff0705051002ef7605051002ff3605051010fb7405051010fb5405051010fd7305051010ff2305051010fd53050510217f1305051010ff2205051020df6768851002ef6768851002df77588510205f575885100077765885101ff74658851002df77488510005f
  | 2 => 0x67e32d95100067d32d95100067c32d951026e7f71d95102767e71d951026e7d71d951026e7c71d95102767e41d95102767c41d95100067f31d95102767e31d95100067d31d95102767c31d95100067f21d95102767e21d95102767c21d951026e7f70d951026e7e70d951026e7d70d951026e7c70d951026e7f40d951026e7e40d951026e7d40d951026e7c40d951026e7f30d951026e5f30d951026e7e30d951026e7d30d951026e5d30d951026e7c30d951026e7f20d951026e7e20d951026e7d20d951026e7c20d951026e7f10d951026e7e10d951026e7d10d951026e7c10d951004cfe76d91100067f65d91100067c65d9110004ff75d9110024fe75d9110004fd75d9110024fc75d9110004ff73d911001cfe73d9110004fd73d911001cfc73d9110006be43d9110006bc43d9110014fe72d9110004fd72d9110014fc72d91100067f52d9110006be42d9110006bc42d911002cfe71d911002cfc71d911002cff70d911000cfe70d911002cfd70d911000cfc70d911012ebf40d911012ebd40d911012edf30d911012edd30d91100457e75991100057d75991100067f65991100067c6599110006bf649911010df571991100057f75591100457c75591100067f65591100067c6559110005df7359110035dc7359110005ef725911003dec725911014df77159110004ff75591100067f75591100047f7559110024fe7559110004fd7559110024fc75591100067c75591100247c7559110006bf7459110004ff7359110006df7359110004df735911001cfe7359110004fd735911001cfc7359110006dc735911001cdc7359110004ff7259110006ef7259110004ef7259110014fe7259110014fc7259110006ec7259110014ec72591100067f525911014cff7159110006f7715911010cff7059110006fb705911010edf305911010edd305911012cfe76191100067f65191100067c651911004ebe6419110006bd6419110014fe76d89100457c75d89100067f65d89100067c65d891003eee62d8910004ff75d89100067f75d8910024fe75d8910004fd75d8910024fc75d89100067c75d89100247c75d891004cfe74d8910004fd74d8910004ff73d891001cfe73d8910004fd73d891001cfc73d891003e7f52d891003eec42d8910006ef32d891003eec32d891002cfe71d891000cfd71d891002cfc71d891003eef21d891002cff70d891000cfe70d891002cfd70d891000cfc70d89100d6df30d89100d6dd30d89100d6ef20d89100d6ed20d89100057f75589100457c75589100067f65589100067c6558910005bf7458910005bc7458910005df7358910035dc735891003eec6258910265f77158910004ff75589100067f75589100047f7558910024fe7558910004fd7558910024fc75589100067c75589100247c7558910004ff745
  | 3 => 0xc415931010ebf405931010ebd405931010edf305931010edd3059310004ff7558b10024fe7558b10004fd7558b10024fc7558b10004ff7458b1004cfc7458b10004ff7358b10006df7358b10004df7358b1001cfe7358b10004fd7358b1001cfc7358b10006dc7358b1001cdc7358b1002eef7258b1005e7f5258b1005eee3258b10006ed3258b1002cff7158b1000cfe7158b1002cfd7158b1000cfc7158b1002eee2158b1002eec2158b100bedf3058b100bedd3058b100beef2058b100beed2058b1002efa1058b1002ef91058b100067f7654b102467e7654b100067d7654b102467c7654b102467f6454b1025e7e6454b100067d6454b102467c6454b102467f6354b101a67e6354b102b67d6354b102467c6354b102557f7254b100576f7254b102467f6254b100167e6254b1005e7d6254b100167c6254b10247767154b10007757154b1019e7e6154b10247764154b10247762154b1019e7d6054b1019f5f3054b1019f5d3054b1019f6f2054b1019f6d2054b1019f761054b1019f7a1054b1019f741054b1004cff76d0b1002cfe76d0b10004fd76d0b1002cfc76d0b1004ebe64d0b10006bd64d0b1002df671d0b10005f571d0b10004ff7650b1002cfe7650b10004fd7650b1002cfc7650b1004ebe6450b10006bd6450b1002df67150b1002df77650710006f776507102adf775507102adf5755071002fb7745071002fb7645071004ef6645071002ef4645071002fb4645071029fb7545071029fb45450710007d773507102a7d473507102a7b743507102a7b54350710005f7725071029f775250710007755250710007b74250710007b5425071000df6705071000df4705071010fb7405071010fb5405071010fd7305071010fd5305071002df77648710296f7764871028df7754871028df57548710005f77448710005f57448710007d77348710287d4734871002fe7724871002fe76248710016f6624871002ef4624871002fe4624871005f77524871005f75524871005fe63248710287e5324871000df6704871000df470487100bfd730487100bfd530487100bfe720487100bfe5204871027d7e76d95100467e76d95100247e76d95100067f63d95100067e63d95100067d63d95100067c63d95100057d72d95100067e62d95100067c62d951026f7771d951026f7471d951026f5f30d951026f7a30d951026f5d30d95100077930d951026f7a20d95102777b10d951026f7610d951026f7410d951026f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067e42d95100067c42d95100067f32d9510
  | 4 => 0x492019f6e305492019f6d305492019f4d305492019f6c305492019f6e105492019f6a105492019f6c105492000dec765092004eec765092000cec76509202ddef75509202dded7550920015ef7450920017af7450920007af645092004eee645092004eec6450920007ac64509202d7ae43509202d7ac4350920005ef7150920007eb705092000dee705092000dec705092016fe87050920016ef6050920017eb605092016faf405092016fad405092016fcf305092016fcd305092016fea105092002cfe76d85200076d52d8520004ff75d8520024fe75d8520004fd75d8520024fc75d852004cfe74d8520004fd74d8520004ff73d852001cfe73d8520004fd73d852001cfc73d852000cfd72d85202ce7f52d85202ce7d52d85202cef621d85202cef521d852000cfe70d8520014fd70d852000cfc70d8520266df30d8520266dd30d8520266f710d85200076d5298520006f7619852003df970985200057f75585200757c7558520005bf7458520005bc7458520005df735852006ddc73585200076d525852005dfb70585200757e75185200057d7518520005be7418520005bd741852006dde7318520005dd73185200076d521852002ef66118520006f56118520004fe76d0520004fd76d052004cfc76d05200757e75d05200057d75d052004ebe64d0520006bd64d0520015ee72d0520005ed72d05200076d52d0520007ad42d0520004fe7690520004fd769052002cfc76905200757e75905200057d7590520006bf649052004ebc6490520015ee7290520005ed72905200076d529052000dfa7090520005f97090520004ff7650520004fe7650520004fc765052004ebe6450520006bd6450520005df735052006ddc7350520015ee72505200076d5250520007ad4250520004fe7610520004fd761052002cfc7610520006bf641052004ebc6410520015ee7210520005ed72105200076d521052000dfa7010520005f9701052000dec764852002eec764852000cec76485202c5ef75485202c5ed7548520005ef7448520005ed7448520007cf73485202bfcc73485202beef63485202beed6348520015ef7148520017e77148520007e7614852002eee614852002eec6148520007e46148520007eb704852000dee704852000dec70485200bfe87048520016ef6048520017eb60485200bfcf30485200bfcd30485200bfea1048520004ff7559310024fe7559310004fd7559310024fc755931002ebf7459310006bf5459310006bc5459310004ff7359310006df7359310004df735931001cfe7359310004fd735931001cfc7359310006dc735931001cdc7359310006bf4359310006bd4359310004ff7259310014fe7259310014fc72593100067f525931002cff715931000cfe715931002cfd715931000cfc715931002ebe415931002eb
  | 5 => 0x7fcc628853007f5f528853007f5d528853020dde71885301bfcf218853007fd721885301bfd421885300d5df708853000dde70885300d7da708853000dda70885300d5dd70885301bfd97088530005d9708853000ddc70885300d6df60885300dfdb60885300d7d710885300d7da1088530005df7648530006df7648530004df7648530005de7648530005dd7648530005dc7648530006dc7648530004dc764853030ddf7548530085de754853030ddd7548530085dc7548530005df7448530305de7448530005dd7448530305dc74485300d5df724853007fce6248530007cd624853007f5f524853007f5d5248530265df714853007fd721485301bfce21485301bfcc214853007fd421485300bddf704853000dde704853000ddc70485300bedf60485300c7db60485300bfcf20485300bfda104853004cfe76d912006dde73d9120005dd73d9120004ff75d9120024fe75d9120004fd75d9120024fc75d9120006bf54d9120006bc54d9120004ff73d912001cfe73d9120006de73d912001cde73d9120004fd73d9120006dd73d9120004dd73d912001cfc73d9120006bf43d9120006bd43d912000cff72d9120014fe72d912000cfd72d9120014fc72d91202fe7f52d91202fe7d52d91202febf42d91202febd42d912002cfe71d9120004fd71d9120014ff70d9120014fd70d91202f6bf40d91202f6bd40d91202f6df30d91202f6dd30d912016cfd7699120006bf649912016ded729912008df9709912004cff76591200057f75591200757c7559120185ef72591200a5fb7059120004ff75591200067f75591200047f7559120024fe7559120004fd7559120024fc75591200067c75591200247c7559120006bf7459120004ff735912001cfe7359120004fd735912001cfc7359120184ff7259120006ef725912008e7f525912008e7d5259120004ff715912002cfc715912016cff7059120006fb705912016edf305912016edd30591202f4fe76191200757e75191200057d751912004ebe6419120006bd64191200776f76549200266f765492019f6c76549200266c76549200076f74549200076e74549200076d74549200076c74549200076f64549200076e64549200076d64549200076c64549202ef6f73549202e76e73549202ef6d73549202e76c73549202e76f63549202e76e63549202e76d63549202e76c63549202e76f43549202e76e43549202e76d43549202e76c43549200076f71549200076e71549200076d71549200076c71549202e76f31549202e76e31549202e76d31549202e76c315492019f6f70549200076b705492019f6e705492019f6d705492019f6c705492019f6870549200176f60549200166f60549200176b605492019f6f405492019f6e405492019f6d405492019f6c405492019f6f305492019f4f305
  | 6 => 0xe721853007dce7218530005dd72185301bfcd7218530005cd72185301bddc7218530006de6218530006dc62185300075f52185300075d521853036dde71185301bedf61185301bfd661185301bedd6118530007d5611853001ddf701853000dde701853001ddd70185301bfd9701853000ddc701853035edf6018530367db601853035fd7101853035fda101853035fd51018530305df76d0530005de76d0530005dd76d0530305dc76d0530305df75d0530085de75d05303075e75d05300855e75d0530355dd75d05303075d75d05300055d75d0530305dc75d05303079e64d05300079d64d053034f9f54d05303079c54d053007dde72d0530005dd72d053007ddc72d053034f5f52d05300075d52d05303079f42d05300079d42d053014ddf70d053000dde70d053014ddd70d053000ddc70d053014edf60d053015fdb60d053014f9f40d053014f9d40d053014fda10d05301bddf7690530005de7690530005dd76905301bddc76905301bddf7590530085de75905301bf5e75905300855e7590530345dd75905301bf5d75905300055d75905301bddc759053010ddd74905300079f64905300079c649053007dde7290530005dd72905301bddc729053033f5f52905300075d52905300edde71905301bf9f4190530307d7419053012ddf709053000dde709053012fda709053000dda709053012ddd70905301bfd97090530005d9709053000ddc709053012edf609053013fdb609053012fd7109053012fda1090530005df7650530006df7650530004df7650530005de7650530005dd7650530005dc7650530006dc7650530004dc7650530335df7550530085de7550530335dd7550530085dc75505300079e64505300079d645053032f9f545053032f9c5450530005df725053007dde725053007ddc725053032f5f52505300075d52505300079f42505300079d4250530307d741505301bf9e415053010ddf705053000dde705053000ddc705053010edf605053011fdb605053010f9f405053010f9d405053010fda10505301bddf7610530005de7610530005dd76105301bddc76105301bddf7510530085de7510530325dd75105301bddc751053014dde74105300079f64105303079c641053007dde7210530005dd72105301bddc721053031f5f52105300075d521053012dde71105301bf9f41105301bfd641105301bf9d4110530307d541105300eddf701053000dde70105300efda701053000dda70105300eddd70105301bfd97010530005d9701053000ddc70105300eedf60105300ffdb60105300efda10105301bddf7688530005de7688530005dd76885301bddc76885301bddf7588530085de7588530315dd75885301bddc75885301bddf7488530305de7488530005dd74885301bddc74885300bddd7288530007cf6288530
  | 7 => 0x493019f5c705493019f5f605493019e5f60549301a75b605493019f5f405493019f5e405493019f5d405493019f5c405493019f5f205493019f4f205493019f5e205493019f5d205493019f5c205493019f5e105493019f5a105493019f5c1054930305df76d0930005de76d0930005dd76d0930305dc76d0930305df75d0930085de75d093039ddd75d0930305dc75d0930395de74d09300079f64d09303079c64d093016ddd72d093007f5f52d093007f5d52d093007f9e42d093007fce42d093007f9c42d09301bdde71d0930005dd71d0930185df70d093000dde70d0930185dd70d093000ddc70d0930186df60d093018fdb60d09301879f40d09301879d40d0930187da10d0930005df7650930005de7650930005dd7650930005dc765093038ddf7550930085de755093038ddd7550930085dc75509302f5df74509300079f64509300079c6450930185df725093007f5f525093007f5d5250930307cf425093007f9e425093007f9c425093007fcc4250930005df71509301bddc715093016ddf705093000dde705093000ddc705093016edf6050930177db605093016f9f405093016f9d405093016fcf205093016fda1050930005df75d8530085de75d8530005dd75d8530085dc75d8530305de74d8530005dd74d853007dde72d8530005dd72d853007ddc72d8530006df62d8530006dd62d85300075f52d85300075d52d853001ddf70d8530387db70d853001ddd70d8530376df60d8530387db60d8530377d710d8530377da10d8530377d510d853037ddd76985301bddf7598530085de7598530005dd75985301bddc7598530305de7498530005dd7498530006de6498530006dc649853007dde7298530005dd72985301bddc7298530006de6298530006dc62985300075f52985300075d529853035dde71985301bedf6198530007d7619853036ddd70985301bfd97098530035d9709853036edf6098530067db609853036fda1098530005df75585300075f75585300055f7558530085de7558530005dd7558530085dc75585300075c75585300855c7558530005df74585300079f74585300059f7458530305dc74585300079c74585300059c7458530005df7258530007cf7258530005cf725853007dde725853007ddc7258530007cc725853007dcc7258530006df6258530006dd62585300075f52585300075d5258530007d761585301bede615853037ddf7058530007db7058530065db705853037edf6058530037db605853037fda1058530375de76185301bddf7518530085de75185301bf5e75185300855e7518530005dd75185301bf5d75185300055d75185301bddc7518530305de74185301bf9e74185300059e7418530005dd74185301bf9d74185300059d7418530006de6418530006dc641853007dde72185301bfc
  | 8 => 0x5dd75d9130085dc75d91300079f54d91300079c54d913007dde72d9130005dd72d913007ddc72d91300075f52d91301bdde71d9130005dd71d913001ddf70d913001ddd70d91303eedf60d91303ffdb60d91303ef9f40d91303ef9d40d91303efda10d91303f5dd7699130305df7599130085de7599130005dd7599130305dc75991303d5de7499130306df64991300079f649913007dde7299130005dd729913007ddc72991300075f52991301bdde7199130005dd71991303e5dd7099130307d97099130095d970991303e6df60991300afdb60991303e7da1099130005df75591300075f75591300055f7559130085de7559130005dd7559130085dc75591300075c75591300855c75591300079f6459130306de6459130005df725913007dde725913007ddc72591300075f5259130005df71591301bddc71591303f5df7059130007db70591300addb70591303f6df6059130097db60591303f7da10591303edde7619130305df7519130085de75191303075e75191300855e7519130005dd75191303075d75191300055d7519130305dc75191303e5de7419130306df64191303079e6419130306dd64191300079d64191300079f54191303079c541913007dde7219130005dd721913007ddc72191300075f52191301bdde7119130005dd711913001ddf701913000dde701913001ddd701913000ddc70191303d6df60191303dfdb60191303d79f40191303d79d40191303d7da10191303cdde76d8930005df75d8930085de75d8930005dd75d8930085dc75d8930305de74d8930005dd74d8930006de64d8930006dc64d89303a5dd72d893007ede62d893007fce62d893007edc62d893007f5f52d89301bdde71d8930005dd71d893007fcc21d893001ddf70d893000dde70d893001ddd70d893000ddc70d89303b6df60d89303c7db60d89303b7cf20d89303b7cd20d89303b7da10d89303bddf7658930005df7558930085de7558930005dd7558930085dc7558930005df7458930305dc7458930006de6458930006dc64589303b5df7258930007cf625893007ede625893007edc625893007fcc625893007ecc625893007f5f5258930005df71589301bddc715893007fcf21589303a5df7058930007db70589303addb70589303a6df605893006fdb60589303a7da10589300075f76549300075e76549300075d76549300075c76549300075f74549300075e74549300075d74549300075c74549300075f64549300075e64549300075d64549300075c645493007f5f72549302555f72549300874f725493007f5f625493007f5e625493007f5d625493007f5c625493007f5e425493007f5c42549300075f71549300075e71549300075d71549300075c715493007f5f215493007f5c215493019f5f705493019f5e705493019f5d705
  | 9 => 0xb60d09401879f30d094000cfc76509400067f655094017e7c6550940006ef6250940016ec625094004fac4250940005fb705094000df8705094000dbc7650940016bc765094000cbc765094043dbf755094043dbd75509400073f65509404373c6550940176be6350940176bc635094004dbf725094004faf7250940007af6250940016be6250940016bc625094008fac625094008f3f525094008f3d5250940005bf7150940007bb705094000dbe705094000dbc705094016fb8705094004ebf605094004fbb605094016f9f305094016faf205094002cfe76d85400067f65d85400067c65d8540004ff75d8540024fe75d8540004fd75d8540024fc75d8540004ff73d854001cfe73d8540004fd73d854001cfc73d8540014fe72d8540004fd72d8540014fc72d85400067f52d85400067d52d8540006bf42d8540006bd42d854004cfd70d854014edf30d854014edd30d854014ef710d854009d7e75985400057d75985400067f65985400067c6598540006f761985400057f755854009d7c75585400067f65585400067c6558540005df7358540095dc7358540005ef725854008dec72585400067f65185400067c651854002ef66118540006f561185400edbe76d054004ebe76d054004dbf75d054004f3e75d054042dbd75d054004f3d75d05400053d75d05400073f65d0540166be65d0540166bc65d054041f3c65d05401663c65d0540426bf63d0540426bd63d0540005bd72d0540006bf62d054041f3f52d05400073d52d054002ebe61d054002ebc61d054000dbe70d054000dbc70d054004ebf60d054004fbb60d054014f9f30d054000cfe769054009d7e75905400057d75905400067f65905401467c659054010dbd7490540006f7619054002ef4619054000dfa7090540005f9709054000cfc76505400067f65505401267c6550540005df7350540095dc7350540006f7615054002ef4615054004fb44150540005fb705054000df8705054000dbc765054002ebc765054000cbc7650540415bf7550540415bd75505400073f6550540126be6550540126bc65505404073c65505401263c65505400079f735054040f9c735054040ebf635054040ebd6350540005bf7250540006bf62505404073f52505400073d525054004dbf715054004fb77150540007b7615054002ebe615054002ebc6150540007b46150540007bb705054000dbe705054000dbc705054010fb8705054004ebf605054004fbb605054010f9f3050540004fe7688540004fd768854002cfc76885400067f65885400e67c658854004dbe7488540005bd7488540006ef6288540016ec6288540004ff7648540004fe7648540004fc76485400067f65485400ce7c654854004dbe7448540005bd7448540005df7348540095dc7348540005df75d9130085de75d9130
  | 10 => 0x74000dbe705074000dbc705074010f9f305074002cff768874004cfe7688740004fd768874004dbe7488740005bd7488740004ff7648740004fd764874004cfc764874004dbe7448740005bd7448740005df73487400addc734874046d7e76d954009e7e76d95400247e76d954045f3f74d954045f3c74d95400067f63d95400067e63d95400067d63d95400067c63d95400057d72d95400067e62d95400067c62d95404677b40d954045f3e40d954045f3c40d954045f7840d954045f5f30d954045f5d30d954045e7f74d95404667e74d954045e7d74d954045e7c74d95400067f73d95400067e73d95400067d73d95400067c73d95404667f43d95400067e43d95400067d43d95404667c43d95400067f72d95400067e72d95400067d72d95400047d72d95400067c72d95404667f42d95400067e42d95404667c42d95400067f32d95400067e32d95400067d32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95404667f41d95404667c41d95400067f31d95400067e31d95400067d31d95400067c31d95400067f21d95400067c21d954045e7f70d954045e7e70d954045e7d70d954045e7c70d954045e7f40d954045e7e40d954045e7d40d954045e7c40d954045e7f30d954045e5f30d954045e7e30d954045e7d30d954045e5d30d954045e7c30d954045e7f20d954045e7e20d954045e7d20d954045e7c20d954045e7f10d954045e7e10d954045e7d10d954045e7c10d9540014fe76d894009d7c75d89400067f65d89400067c65d894008eee62d8940004ff75d89400067f75d8940024fe75d8940004fd75d8940024fc75d89400067c75d89400247c75d894000cfd74d8940014fc74d8940004ff73d894001cfe73d8940004fd73d894001cfc73d894008e7f52d894008eee42d894008eee32d8940006ed32d894002cfe71d8940004fd71d894008eec21d894004cfd70d8940186df30d8940186dd30d8940186ef20d89400057f755894009d7c75589400067f65589400067c655894008eec62589400067f76549400057e76549400067e76549400047e76549400067d76549400057c76549400067c76549400047c76549400073e74549400073d745494019e7f64549404567f63549401a67e63549404567d63549401a67c63549402557f725494009f6f725494008e7f62549400167e62549400167c62549402467c615494019e7f605494025f7b405494019f3e405494019f3c405494019f78405494019f5f305494019f6f2054940395be76d094004ebe76d094004dbf75d094044dbd75d09400073f65d09404473c65d094018ebe63d094018ebc63d094016dbd72d0940016be62d0940016bc62d094008f3f52d094008f3d52d0940005bd71d094000dbe70d094000dbc70d094004ebf60d094004fb
  | 11 => 0x6de10d8d214a6dc10d8d21014fe76d0521014fc76d05210cd7e75d05210057d75d0521006bf64d052104ebc64d0521006df63d052115edc63d0521015ee72d0521005ed72d052104cff7650521014fe7650521114fd7650521014fc7650521006bf645052104ebc6450521005df73505210c5dc7350521006df635052111edc6350521005ef7250521015ec725052102fe4215052100cfe76d81210c5dc73d8121006df63d8121006dc63d81210befa60d8121004ff75d8121024fe75d8121004fd75d8121024fc75d812104cfe74d8121004fd74d8121004ff73d8121006df73d812101cfe73d8121004fd73d812101cfc73d8121006dc73d812101cdc73d812102cfd72d812100cfc72d812105e7f52d812105e7d52d8121014fd71d812100cfc71d81210bedf30d81210befa20d81210befa10d81210057f75581210cd7c7558121005bf7458121005bc7458121005df73581210c5dc7358121006df6358121006dc63581210bef86058121004ff7558b40024fe7558b40004fd7558b40024fc7558b4000cfe7458b40014fd7458b4000cfc7458b40004ff7358b4001cfe7358b40004fd7358b4001cfc7358b4004eef7258b400a67f5258b4004eef4258b4004eec4258b40004ff7158b4002cfc7158b4004ebf4158b4016edf3058b4016edd3058b4016eef2058b400067f7654b4025e7e7654b400067d7654b4025e7c7654b4025f3e7454b400073d7454b4019e7e6454b4025e7f6354b401a67e6354b4049e7d6354b401a67c6354b402557f7254b400b76f7254b400a67f6254b400167e6254b400a67d6254b400167c6254b400a73f4254b402467e6154b4025f3f4154b4019e7d6054b4019f3e4054b4019f7a4054b4019f3c4054b4019f5f3054b4019f6f2054b4004dbf7650b40496bf7650b4048dbf7550b4048dbd7550b40176be6350b4004ebc6350b4004faf7250b4004faf6250b40016be6250b40016bc6250b4004fac6250b400a73f5250b400a73d5250b40005bf7150b4000dbe7050b4000dbc7050b4016f9f3050b4016faf2050b40004ff7558740024fe7558740004fd7558740024fc755874000cfc7458740004ff7358740006df7358740004df735874001cfe7358740004fd735874001cfc7358740006dc735874001cdc7358740004ff7258740014fe7258740014fc72587400067f52587400067d525874004ebf4258740006bd425874004ef7715874004ef7415874004ef4415874010edf305874010edd305874010ef7105874004dbf7650740006bf7650740485bf7550740485bd7550740126be655074004ebc65507400079f735074047f9c735074004ebf635074047ebd6350740005bf7250740006bd62507404773f52507400073d525074004fb7715074004fb7615074002ebe615074002ebc615074004fb4615
  | 12 => 0xc75582210247c7558221004ff745822104cfc7458221004ff735822101cfe7358221004fd735822101cfc735822103e7f525822103e7d525822102cfe715822100cfd715822102cfc715822102eef215822102eed215822102efb70582210d6df30582210d6fa3058221006f930582210d6fa205822102efb105822102ef8105822104cfe76d91210cd7e75d91210057d75d9121006dc63d9121004ff75d9121024fe75d91210067e75d91210247e75d9121004fd75d91210067d75d91210047d75d9121024fc75d9121006be54d9121006bd54d9121004ff73d912101cfe73d9121004fd73d912101cfc73d912102cff72d912102cfd72d91211367f52d91211367d52d9121136bf42d9121136bd42d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121006bc40d9121006df30d9121136ef20d91210cd7e75991210057d7599121006bf64991210c5de7399121005dd7399121006dc6399121115f57199121005df73591210c5dc7359121006dc6359121155f77159121004ff7559121024fe7559121004fd7559121024fc7559121006bf7459121004ff7359121006df7359121004df735912101cfe7359121004fd735912101cfc7359121006dc735912101cdc7359121114ff7259121006ef72591211167f52591211167d5259121154ff7159121006f77159121004ff705912100cfe705912100cfc7059121006df3059121116ef2059121134fe761912104ebe6419121006bd6419121006dc63191214b5de76d8d210c6de76d8d2101cde76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d214a7cf72d8d214afcc72d8d214af5f52d8d214af5d52d8d214afd721d8d214a7ce21d8d214a7cc21d8d214afd421d8d21005dd70d8d21006de60d8d21006dc60d8d214afcf20d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d214a6df72d8d214aede72d8d214aedd72d8d214aedc72d8d214aedf52d8d214ae5f52d8d214aede52d8d214aedd52d8d214ae5d52d8d214aedc52d8d214aedf42d8d214aede42d8d214aedd42d8d214aedc42d8d214aedf71d8d214a6de71d8d214aedd71d8d214a6dc71d8d21006df51d8d214a6de51d8d21006dd51d8d214a6dc51d8d214a6de41d8d214a6dc41d8d214aedf21d8d214a6de21d8d214aedd21d8d214a6dc21d8d21006df70d8d21006de70d8d21006dd70d8d21004dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006de40d8d21006dc40d8d214aedf20d8d214aede20d8d214aedd20d8d214aedc20d8d214a6df10d8d21
  | 13 => 0x94102dbc7150941007b4715094104ebf615094104fb76150941005bf70509414cf9f3050941117af205094100cfe76d814111ddc73d8141006df63d8141006dc63d814110efa60d8141004ff75d8141024fe75d8141004fd75d8141024fc75d814102cfd74d814100cfc74d8141004ff73d8141006df73d814101cfe73d8141004fd73d814101cfc73d8141006dc73d814101cdc73d8141014fe72d8141004fd72d8141014fc72d81410067f52d81410067d52d8141006bf42d8141006bd42d814104cfd71d814110efa40d814110edf30d814110efa10d81410057f75581411257c7558141005df735814111ddc7358141006df6358141006dc6358141005ef7258141115ec725814110ef86058141004ff7558841024fe7558841004fd7558841024fc7558841004ff735884101cfe7358841004fd735884101cfc735884102cff725884102eef72588410f67f52588410f6ee5258841006ed525884104eef425884104eec42588410f6ee3258841006ed325884102cfc715884102ebf415884102ebd415884102eee215884102eec2158841004ff705884100cfe705884100cfc7058841006df30588410f6ef20588410067f76548412467e76548410067d76548412467c76548411567e64548412467f63548411a67e63548414be7d63548412467c63548414c57f72548411076f72548412467f62548410167e62548412476e62548410166e62548410f67d62548412476d62548410066d62548410167c62548412467e61548412473f41548412477641548412473d415484125f75415484119e7e605484119e7c60548414bf5f30548410f76f2054841004ff75580410067f75580410047f7558041024fe7558041004fd7558041024fc75580410067c75580410247c755804100cfd7458041004ff735804101cfe7358041004fd735804101cfc7358041004ff7258041014fe7258041014fc72580410067f52580410067d525804102ebf415804102ef6415804102ebd415804104ef5415804102cff705804102efb70580410eefa5058041006f9505804104efb405804104ef840580410eedf30580410eefa3058041006f930580410eefa205804102efb105804102ef81058041004ff7559221024fe7559221004fd7559221024fc755922102ebf7459221006bf5459221006bc5459221004ff7359221006df7359221004df735922101cfe7359221004fd735922101cfc7359221006dc735922101cdc7359221006bf4359221006bd43592211167f52592211167d5259221116bf4259221116bd425922102cfe715922102cfc715922102ebe415922102ebc4159221004ff705922100cfe705922100cfc7059221006df305922102ef71059221004ff75582210067f75582210047f7558221024fe7558221004fd7558221024fc75582210067
  | 14 => 0x6dc60d8d41006df75d8d41006de75d8d41006dd75d8d41006dc75d8d414f6df74d8d4111ede74d8d4111edd74d8d4111edc74d8d41006df54d8d414fede54d8d41006dd54d8d414fedc54d8d41006df72d8d41006de72d8d41006dd72d8d41006dc72d8d41006df52d8d410065f52d8d41006de52d8d41006dd52d8d41006dc52d8d414fedf42d8d41006de42d8d414fedc42d8d414fedf71d8d414f6de71d8d4111edd71d8d414f6dc71d8d41006df51d8d414f6de51d8d41006dd51d8d414f6dc51d8d414fedf41d8d414f6de41d8d4111edd41d8d414f6dc41d8d41006df21d8d414f6de21d8d414f6dc21d8d41006df70d8d41006de70d8d41006dd70d8d41004dd70d8d41006dc70d8d41006df50d8d41006de50d8d41006dd50d8d41006dc50d8d414fedf40d8d41006de40d8d414fedc40d8d41006df20d8d41006de20d8d41006dc20d8d414f6df10d8d41006de10d8d414f6dc10d8d41014fe76d8941006df63d8941006dc63d8941116ee62d8941004ff75d8941024fe75d8941004fd75d8941024fc75d894102cfd74d8941004ff73d894101cfe73d8941004fd73d894101cfc73d89411167f52d8941116ee52d8941006ed52d8941116ee42d894104cfd71d8941116ef21d894100cfe70d8941004fd70d894100cfc70d8941006df30d8941006ee20d8941116ec20d8941005df735894111ddc7358941006df6358941006dc6358941116ec62589410067f76549410067e76549410067d76549410067c76549410073f74549410073c74549414ee7f63549410075f63549410065f63549411a67e63549414ee7d63549411a67c63549414ef5c63549411a65c63549414ef3f43549414ef3d43549411157f72549411276f72549411167f62549410076f62549410066f62549410167e62549410167c62549411176c62549410166c625494125f7741549412473e415494119e7e605494119e7c60549414ef5f30549411176f2054941005be76d094104ebe76d0941125be75d094104dbc75d094104dbf73d09414e5bd73d09410079f63d094118ebe63d094118ebc63d09414df9c63d094118e9c63d0941115bd72d0941016be62d0941016bc62d09411173f52d09411173d52d094102dbe71d094102dbc71d094104ebf61d094104fb761d0941005bd70d09414df9f30d094102cfc7650941006df6350941176dc6350941006ef6250941016ec6250941005f7715094102df4715094102dbc7650941016bc765094102cbc7650941125be7550941125bc75509414d5bf73509414d5bd73509410079f6350941176be6350941176bc63509414cf9c63509411769c635094104dbf725094104faf7250941007af6250941016be6250941016bc6250941117ac6250941016ac62509411173f52509411173d5250941007b7715094102dbe715
  | 15 => 0x5415834104efb705834104efb405834104ef8405834114edf305834114efa10583411467f745964150e7e74596410067d745964150e7c74596410067f73596410067e73596410067d73596410067c735964150e7f43596410067e43596410067d435964150e7c43596410067f72596410047f72596410067e72596410067d72596410067c725964150e7f42596410067e425964150e7c42596410067f32596410067e32596410067d32596410067c325964102e7f715964102e7e715964102e7d715964102e7c715964102e7f415964102e7e415964102e7d415964102e7c415964102e7f315964102e7e315964102e7d315964102e7c315964102e7f215964102e7e215964102e7d215964102e7c21596410067f70596410067e70596410067d70596410067c705964150e7f40596410067e405964150e7c40596410067f30596410065f30596410067e30596410067d30596410067c30596410067f20596410067e20596410067c205964102e7f105964102e77105964102e7e105964102e7d105964102e7c1059641004ff7558a41024fe7558a410067e7558a410247e7558a41004fd7558a410067d7558a41024fc7558a41004ff7358a4101cfe7358a41004fd7358a4101cfc7358a4102eef7258a411367f5258a41136ee4258a41136ee3258a41006ed3258a4102cfc7158a4102ebf4158a4102ebd4158a4102eee2158a4102eec2158a41004ff7058a4100cfe7058a4100cfc7058a41006df3058a41136ef2058a4102ef71058a412457f7654a410067f7654a410047f7654a412467e7654a412457d7654a410067d7654a410047d7654a412467c7654a411167d6454a412467f6354a411a67e6354a415067d6354a412467c6354a414c57f7254a411476f7254a412467f6254a410167e6254a411367d6254a410167c6254a412467e6154a412473f4154a4125f774154a4119e7e6054a4119e7c6054a415075f3054a411376f2054a41014ff7650a4117e7e6550a410067d6550a41016ee6250a41006ed6250a4104fac4250a41005f77150a4102df47150a41004ff7558241024fe7558241004fd7558241024fc7558241004ff735824101cfe7358241004fd735824101cfc7358241004ff7258241014fe7258241014fc72582410067f52582410067d525824102cfc715824102ebf415824102ebd415824102efb705824112efa405824112edf305824112efa3058241006f9305824112efa205824102efb105824102ef8105824111dde76d8d4111ede76d8d4101cde76d8d41006df65d8d41006de65d8d41006dd65d8d41006dc65d8d414f79f74d8d4111f9c74d8d410079f54d8d410079c54d8d41006de62d8d41006dc62d8d410075f52d8d414ffd741d8d414f79e41d8d414f79c41d8d414ffd441d8d41005dd70d8d41006de60d8d41
  | 16 => 0x8142024fe75d8142004fd75d8142024fc75d8142014fd74d8142004ff73d814201cfe73d8142004fd73d814201cfc73d814204cfd72d81420a67f52d81420a67d52d814202cfe71d8142004fd71d814216efa40d814216edf30d814216efa20d81420057f755814217d7c755814216ef8605814204e7f74597411663f745974104e7e745974104e7d745974104e7c745974104e3c74597410067f73597410067e73597410067d73597410067c735974104e7f435974104e7e435974104e7d435974104e7c43597410067f72597410047f72597410067e72597410067d72597410067c725974104e7f425974104e7e425974104e7d425974104e7c42597410067f32597410067e32597410067d32597410067c32597411667f715974152e7e71597410067d715974152e7c715974104e7f415974104e7e415974104e7d415974104e7c41597410067f315974152e7e31597410067d315974152e7c31597410067f215974152e7e215974152e7c21597410067f70597410067e70597410067d70597410067c705974104e7f405974104e3f405974104e7e405974104e7d405974104e7c40597410067f30597410065f30597410067e30597410067d30597410067c30597410067f20597410067e20597410067c205974152e7f10597410067e105974152e7c1059741004ff7558b41024fe7558b410067e7558b410247e7558b41004fd7558b410067d7558b41024fc7558b4102cfc7458b41004ff7358b4101cfe7358b41004fd7358b4101cfc7358b4104eef7258b411567f5258b4104eef4258b4104eec4258b41006ef3258b41156ec3258b41156ef2158b41004ff7058b4100cfe7058b4100cfc7058b4104ebf4058b41006df3058b41156ef2058b4125d7f7654b410067f7654b410047f7654b4125e7e7654b4125d7d7654b410067d7654b410047d7654b4125e7c7654b410073f7454b4125f3c7454b4125e7f6354b411a67e6354b415267d6354b411a67c6354b4125f3f4354b415273d4354b411557f7254b411676f7254b411567f6254b410167e6254b411567d6254b410167c6254b411573f4254b4119e7e6054b4119e7c6054b415275f3054b411576f2054b4104dbf7650b410f6bf7650b41165be7550b41165bc7550b4104f3e6550b4104f3d6550b4151dbf7350b4151dbd7350b41176be6350b4104ebc6350b4104faf7250b41016be6250b41016bc6250b411573f5250b411573d5250b4102dbe7150b4102dbc7150b41005bf7050b415179f3050b41157af2050b41004ff7558341024fe7558341004fd7558341024fc755834102cfc7458341004ff735834101cfe7358341004fd735834101cfc7358341004ff7258341014fe7258341014fc72583410067f52583410067d525834104ebf4258341006bd425834104ef6415834104ef
  | 17 => 0x2467e61585520057f705855219d7e705855219d7c70585520075f305855256f6f20585525657e761855225d7e74185520057d74185520067f64185520067d64185522457f73185521a57e73185520057d73185522457c73185520257f72185520157e72185520257d72185520157c72185524c67f621855255f6f62185522457e71185522467f61185522477661185522467d611855200775611855224776211855255775211855219d7e70185520057d701855219d7c70185520067e60185520067c60185520075f30185525576f201855219d7e76d815225d7e74d81520057d74d81520067f64d81520067d64d81520057f73d81521a57e73d81520057d73d81521a57c73d81520257f72d815254f6f72d81520157e72d81520257d72d81520157c72d81525467f62d815254f6f62d81522457e71d81520057d71d81520067f61d81520067d61d815219d7d70d815219e7e60d815219f7a60d815219e7c60d815219f5f30d815219f6f20d815219f7a20d81525477920d815219d7f76581520057f74581520073f74581520053f745815225d7c74581520073c74581520053c74581520067f64581520067d64581520057f73581521a57e73581520057d73581521a57c73581525357f72581520076f725815253d6f72581525367f62581520776f62581520057f71581522457c71581520067f61581520067d615815219d7f70581520077b605815219e7e605815219e7c605815219f78605815219f5f305815219f6f2058152004ff7558742024fe7558742004fd7558742024fc7558742014fc7458742004ff735874201cfe7358742004fd735874201cfc73587421167f52587421167d525874204ef7715874204ef7415874204ef44158742116f62158742004ff705874200cfe705874200cfc705874204ebf4058742006df3058742004ff75583420067f75583420047f7558342024fe7558342004fd7558342024fc75583420067c75583420247c7558342014fe7458342014fc7458342004ff735834201cfe7358342004fd735834201cfc735834208e7f525834208e7d525834204eee425834204eed4258342004ff715834202cfc715834204ebf415834204efb705834204efb405834204ef84058342186df3058342186fa205834217d7e75d85420057d75d8542004ff75d8542024fe75d85420067e75d85420247e75d8542004fd75d85420067d75d85420047d75d8542024fc75d8542004ff73d854201cfe73d8542004fd73d854201cfc73d854204cfd72d85421567f52d85421567d52d8542156f621d854200cfe70d8542004fd70d854200cfc70d8542006df30d8542156ef20d854217d7e75985420057d7598542006f76198542005df7358542175dc735854202ef66118542006f5611854200cfe76d814216efa60d8142004ff75d
  | 18 => 0x380000000050010000002009000800c0060020098028000005002802000c000003804000600000400000000020057f73d91521a57e73d91520057d73d91521a57c73d91520067f63d91520067d63d91520257f72d91520257d72d915259e7f62d91525af6f62d915259f3f42d915259f3d42d91522457e71d91520057d71d915219d7e70d91520057d70d915219d7c70d91520073e40d91520073c40d91520075f30d915259f6f20d91525a57d76991525857e749915225e7f64991520073f64991520063f649915225d7f73991521a57e73991520057d73991521a57c73991525957d729915225f6d729915217d6d72991525967f62991521976f62991522457e71991520057d719915219d7e70991520057d709915219d7c70991520067e60991520067c60991520075f30991525976f20991520073f645915225e7e64591520057f73591521a57e73591520057d73591521a57c73591520067f63591520067d63591525a57f72591520076f72591521956f72591525a67f625915217f6f62591520057f71591522457c71591520057f705915219d7e705915219d7c70591520075f30591525a76f205915259d7e76191525957e741915225e7f641915225f3e641915225e7d64191520073d64191520063d641915225d7f73191521a57e73191520057d73191521a57c73191520257f72191520157e72191520257d72191520157c72191525867f621915258f6f62191525873f42191525873d42191522457e71191520057d711915219d7e70191520057d701915219d7c70191520067e60191520067c60191520073e401915225f3c40191520075f30191525876f201915225d7e74d85520057d74d85520067e64d85520067c64d85520057f73d85521a57e73d85520057d73d85521a57c73d85520067f63d85520067d63d85520257f72d85520257d72d85525667f62d855257f6f62d85525677621d85525677521d855219d7e70d85520057d70d855219d7c70d85520075f30d85525676f20d855256d7d769855225d7e74985522473e74985520053e74985520057d74985522473d74985520053d74985520067f64985520067d64985522457f73985521a57e73985520057d73985522457c73985525757d72985522476d72985520cd6d72985524c67f62985520e76f62985522457e71985522467f619855200777619855219d7e70985520057d709855219d7c70985520067e60985520067c60985520075f30985525776f20985520057f745855225d7c74585520067e64585520067c64585520057f73585520075f73585520055f73585521a57e73585520057d73585521a57c73585520075c73585521a55c73585520067f63585520067d635855256d7f72585520076f72585520e56f725855256e7f62585520cf6f6258552007776158552
  | 19 => 0x2c00600a0098040008009011800800401100080000060000048004014000001800c028000001800000c009001000403a000003001402800600d0004000000003006c00200400e000400001400100000040050000000000001000000c004007000800000a001000004c000001002003c026001001000400a00300b80700040010018004002000007000800801d009800c00c005000000800000000100000000040008010018004002802000600501d003000200d0038010008000002802400600300000000000100010004004000003800c00e032002806c03c00000300280040250000000000008006005c0240030010020014001002000000000400080540000000038000000000010800400000b00080540000000020000026001000000800a000005001001600c0008014000008013001000200d003000c0000080010000000002004800c0000020008000000000000000000000d00500180000400010000000027000800c000004010800800400b0000050018003001800c00000400a80040280200000008004001000001401800f000800802a008000000407e00000200200160010048024004000001800000c007005000800e00c00100000000000028004004000004801002200d000006400a01f000800c004003002800002000b0010034002001000000000200d002800000000501380040020180010008000001004001400600300c8004006000009004c006000000000800a011002003400a00000d001800e020000000400c00300500000080060008000000003005000000800000080000080020000034008006000001c004008000000c0140000028010014002005000c00800100000000040040000014000006000000c014002003009004204800e802400200900c800000c0010030004034000008001000c01b00000000080170008004000005000802800200100100180080000000004026004000805001000000100040020050130000004023006800c01a000001800401000100000480100000010000000001007003800e002000000001800e001000800000700380000080060000004000000004003800200b007802402c0000038000006003003800000e016004800400c001001009401e00000100000000080000000004003000800c004000000000400a00500b801c00000c0000000000000000000c00000a0008000000004000000000a0190150010032001001001c0180000020000000000002000c03400000100100300020038000000008000800c02000100a00340860010000040004008001801800000800600200020000238014000001002801c01c016003800c014003002809c0000050020010010005000002000a000000001800200a0078048010006005800800a00000500140020160000014008000008002c00000
  | 20 => 0xfe61b94e441a1e626a8000c9a77f071a4407861a907a816901673b367902801272548086c146a00023da730a0200000007c52888d423ab128aa400041b9bcc0004bd5df8001790000000000000000005f05c102e2bf00000007d40001b68d8800000000000003e600026019880000001909ce949000033a00009f80000001d6884691230a01c17b40000000000a5ca9c2f2b17518e7fe2ef9ca4f7432d00015d956e0000002a6453a000137a3c96f02ed470314016a3a000013940003f72e20cf989261b4b9889cd769142d9304cce4000436800067e23700000013200003fa000020c3e23be1808bfa07a030800137200016780003366220000a4043000000c800127c00000025480003333b6000003400000012d00007bd00000010240000190d3413e000183239c0880000000535416000474847c1e84e30000e28a323a5006113c22c0b6000101000000038704e12f4436413000a00800000d400c0040020018000003008000000400200a000400000300000000100010000088000008000000800800000000180020020030000000000000000c002000000801000800500000000040000008014010007007800002400e0008018006002005802c022009002000400000200000a800c006003001c010006001001000200500c8134002000000000001000c000805801a007000000400000200600cc00600500000380140000060008006002007801000a0000018034016000000800400e0000080040008000000006c0000010000008012009001001002400000100200280040018008000007000800000000d00200300020000038008004000029800000a002000002001401200f800802a00100480380080010010000006000000800400200100000000000000078000028001002000401800100000ac008005011802400c00700700140000040038000016000002800000a0070008000004002002002c0160070000008046000002800400401a001803400000500f0008000007003803400000000080100000020038044004021002800000000100380000280040000044014001008801000201c0020020008002000000805e000005806c0a000000100100040080008060006009000802c0040000000000000001001801c012004002006400000b000000400c002013800400e00100100000000010000004002002000000401e027002000000000200500100000240008000082000002801c0060000040008000001003000801e005000000800400000e8000000001000800c006000005006001600f009000002a0000000000000007003002000800d002802000a0000018118028000005001000e000001000000200f00080000060000038020000000001000c04c000003802c016037001000400a00b0040000000009000800400a00001080
  | 21 => 0x309071242c58b252059a2bb46f0000a201075992699640bf11e4a8e4b7a0b43d211dd77835d006a938000b906511f940005ca4cb896c88a907312af743ee9d033cac083ba0003fb2308000b1540cb1540006410001bd92e41d339a2e9d8640a93ed1c697e65db202a8e89424fe5562589394442612a23d68a91a2b3a44424a0001d329f87ae1652891edd70a0000ec16757d68650001c900008f83809e790e481500000004b8066360000153ab9a1ff13681d23022e70ae87b413661f230c07012a4c2836ca3e48c0a4215914295f35722e4be404a2368e8c00000056b8b1800052600000001f00004af0b480002b8057800100019c0000000c644b2026add85883581ec0788f522e326c9f898144bc1d4104800000000015c0000a8663000016081490820dd051848b079275d26e437181a05120096654c0d596c8b380818324fce66d20199ed7524d22541cf804835e12b8f017e83f03d727f116a92e1e0a2b5258c860f2800113c413586b250cb07923a91eb0f8a88238496541d64f13afa13d42c7d938396c08920b10000a4d580a895ab96f8076bb02ae2c645a80003c0909821c58700000013fa09c00000016d20002b88bd0ceab6d52a800000053e1e896318fa6de1cba0fd1500e721d1d195ce3cd00000000000004ef025586875b4452c6d3ec0000001c88fb83d01ca000126000035e00000000000000d04cb2000290800093000060c1ee131e000000307000001c4ea9461514c9b00000000000002e4238c00002a4078000000bb500024bcc2491b1bc0000bae000000000114c9a30000d6c9d60005158d8c00030c00026f54d2924000003c0007d462d930938000013588fcd8e0003469fbc00000055203a07328c93be9208394047593285c7c80000002fdd1a095d3530ca4000578000097ced468e00000000007cc0002fa904a0df36e2df552c0002a29a2506cc890340000f6aa745cb82000007c63fe836889636b000204400000041903b8e3e07157c916817000053f816548a0981648e4952a3190002178b68b6a3f3176470600064980000000304ad90cc00000032827a000077139791e8d4a49e000000000083524eaa046b200000031f13c8b254fa00011cc00015300000fc0000002b30000a9f51b1304498b390000000aaa00000000015861145e19a640000003c200005c000000000017320001fe9a108f0b374e71268000000000000008263e178a840000c3b59a191800031100013757a80000000000e14c780000000c348610001fac79492b5131dbc1720000002724dde00047680011a61da5e6800000000035a187804c23800020c4000c3000000000ee000000000187e0000002eb00000000c509cc0000000002ae800030844908f8e9ac0e3aca534e6e27403794883880f60000764000a2a03e98a40001b75bc918c0
  | 22 => 0x32a3536091b348600ca43fa6d0e8092d354990000e79c0000000b980001ee133c000a56000000108a1784ac00000000000459f442bc1d500027a8c78aeb38d9ef10a645f0a3121d85803e0900a113fc28541a32750145830000000d7e5e20002460000bde2b280006007042d02b602b696a36b9e2c0008aa0001974d6000000024857723090000d94aeeb7233484b4a088ac25c000191c67112c132590232328988f072a4a900017e4000806362a320c1264b4ffaa0c30c70f00000000008470000000000000516800000041f229000d0ec0004121c5c0967e84ef9ae40982c1597a9f523e4ee00018640000003899f900000001641b10b660cb000087c0000000001fb993237b11400004122554233024000a12463000113215c31f80001989c700013e800017e0b8ac854c895007302fd106b3b18e94a0000c85554000000031623118580000003b1a900ab010d00000015ea9f823400010f40000001da4ae6874094ab6d5a0011208000000010f0000d2827298803124a533669b0c1919d6800000df2aa89980003508e7cf600001f324884a6b945742b9172209105707b98bc4a20d09f400003b850da5d02807982be82f51340d63d5acf160c90358f9c9cfb097156c8000b84b8f1de98a8b620a109e89ed8d85b74458ac477c7b60000c9898a50626f12a80004b90d9969c6cebae1ad1c840005da38f006c0000000002a9c0006ed02a8c703ea48e531a3380004c84512744faaa8c3bb072428a05c24b06fd5646bd5d187c12645b800000017380000800b886987cb4a8afb4010a1c2f5033d6a031760b95b55f485f017116d46005338aa2e95963d90002bcce1600000020c11fa53a54396a8a0a00049a2e980008075850000000000000000000000000000003080000001b6400000003b0b7857c00a0eb24e09326fe00023cc3440fb17c30400002ef2858b54000c8a3d5088c66a49200000010ce2e960b00000003571339d60cfec4e49d29b47e6c2d20a23bcc6e3610f1b1084ba0045860ffc316000000255cf2886b5b580744cc13022f1a7950a38d502300103487c0002c4879e0001c88000d5e2c000012dc5c8b482dca0400001662fe2170f644f238430886e244144224d8b8a43b5a997d10561ab486824924ac6110700b00000000000000000ad32bda42cff44f00001e1485e7a11b401b895abc41bd0d7d85698c4f92254efcc03088270993841e000000034cbb311a80004dc00050180000806ff03200004f87565f80f6d140af7000327cb0c000000073c000a070000ee80a20000002b1d4e20004b6a539188c4400000014f64e20fc00002b00004b82994000c3c21c94a53ce0002191d9c00000000026d800000048780017c600061891800004b1168000175000000018d8c66c1f3b68e702f600002722cd036b8e14c29cd1f20000
  | 23 => 0x3ce8a8981679100000000000000000000d2c0020000000a9800037e000000096512d22fc1c40e04a0117400021c0000fbd83a0004cc9d306fa77200000000007a00002f7159a10c000181900a0005df10b400085833390700bc7af3222bb00000064fd2ffd3a89af09f88410a8b594f30490e5c5663ba8148000b2a1fa14557a01bd6119d5d79c48153a8a209acc8f64189fc0fe09a02808a40000003dcadcc00097e375000138286064f250515e1053289c3008459850307144c06a71fd95a046262b4cfa9455ec8c11eb00003c2000549846400085b07b908862a0004012dd4000c6f43b8b58a9c8d65458000318ab021a979800000057f1f24d40000458a7598706040000000c508db3358150c740000dc9f38aa672c2578fb0e842f0631815979e08d14018549cc00000000016a20001b4a604b2000000017a4f9ebb858880012401c664109d4cd49190ceaccca6e5cf3cb00bd3701613f0ac916980004401a145f25b60d2ae20dd00004c123d445ac6a11caba431c61c5689a0922cb9e04bb168c487b134589202da22e4d908a992477b04d9bb8fa46d010880dc4bc0ff4ad2d48c5c67a55f98452f8ae55482354ea80001a7820c0004c70001004fc01e92c4172c716c9800000007903930638a810082140dda0a40006ca2f61d110fc00000030183ceb44000269c00060500020740000002cd00005ca0003cc8648ad28eb4070ad4000000526800141ec743ed83c0c9c2590840000234bab00026d4b44a4b42b8b7d04e3285fd2f54aae60808a8e60da875107880013b423d06b80fc00000000000015664c339c96788d60c300019f00008e1204892c10844d0b100000007d63b70000000000307adc48d400006900054ee9172d21cf0cc600062bacd400029f00030047e446556a000040c69255109a40000005f90000d64aab14780001f855d239180c0000005209f7cd30000000232832c000220091000000039026697942914d68c8014800000000000001c832ba674b500006141ac4e7e7a642a80008a6ba25028000c14000000153c0b6000000000107c62663d0000b3e62700024a0a647190002948b0214f39b0000f2a9a210020850cc0003060fe84e269d0001544b1a0000001c700008d9500800098c2c20002ea80001c000024389480000029c0060299e1938000bc215200000000009490000adc0002d85cd847861656300025fc9ea4ca64880000003c63ef24ed674ad663c800000000058ea168b0a0000641e8d3400000001ed10f200053400000002ad17580000004975f300000003e50002a6800000000000000009565fcac606fe0000002474e8298637da2a471c992000000018c94f00007a80400000002ae4000b5b25fa7d45b240252a1fc0e308734d291c4678ae338e94240004f41572be17a600044b110d3e63732e49639
  | 24 => 0x92aa3440be9f5c0420000778000b0493c4931b581c8a425dd9b6d696b130002d9c7bebbd0d006080001ac63a89f94306a824780000001fe5bb86a00000004ee1fc48900001380de4000c4f23e8000af8bdf583800000086f399b1200002aa5b71190c5e000533869c58a000404306d4147f219900010541a44f88000aea0000000c68d980002939eb4c261b81c000014c20000003188cc894a401874051c1e400005a4000b81187a3350d037c61e80000006da00021740000005710000e94000000000038200050c9aac0ce852000000033400002f88bcf2ea9200006d0b7eb0f2742a3cff22894b790fd7ae987000058178c424049aff8ed04b33c685080008fe1d72d3d8cc06041e9cc50862a300004d0b789e04a280002020004841dad5680e5370800094c7f3638034d76e7110fa2a1065ca202afa9b127a51e24a8cdc0009c60219034000c1153c16a58c842a5e09490000a6600023d18983e900002140006b63228000000305311800000000000000003f4b7f3f600000004e00000c7d1fe00000000000000005372fb05ec9670002b100000005068994000c21368800188a00000000015e022c1952140e5a0000000001478a9e4529be5832aa000027640008d70000a680003380001d2073c3b33522d750f63ce2a82bb40009d31731588d9c0002c218d00002bd3b08858222a7600000391a29ed2a41a418a493558a00013cac362fb1fdd09089d168990910e000417a6a18b031221088c980e00008e09e41a059b2e686247f84c452607fc00020200000003a80001288000b7406b509a3740006d55fd80000000000a50d2082274300029f094eb5657a2c24eba00032a13d8b280dc3e00000c3a144428890442ebad50a13bd2989bf2e9ae198ac6f72ab04f96de48d634a93cec82361880ed911809621c14305f454d55487d82f2b9521882c04081eb5a509c8f8453847baed092211d014290c772a461b72f1d3601de4ac8000b8e68747d1d24cfac0d15914a8cb60000ba9e6849253357901a470a00056e9b0966023051704e91c40001a19cc11a44072b091e4e460c500000002a66475529628164b5e6480908a8000031a9cc88685493952f44a4600000015680007bf0000001050b104102a510f0bcb26b926caa8173036b13403c5e42f7a45400000001ea0b480c0004f09b20cb48445c014b4000bc51e2978c102b0e00000000001e820620f000033000000000009bb327a7dc00094762f94d41442475d9288d8f666e4d729c038e8ee273acb984e21b3a3a4a92fa1412f588813f22f22261ab42f41540001e9c00000009390746a04f90002f0000000005617457d20002d0800095c8013d2ad348b8c8b095ac0c00012311a00018fea2464b287d5620000000c1d4b00003b022b8d2e00000024cd67e1df28515bc3a20002518050bba0b3
  | 25 => 0x63a29eec0009632c7933544260e3700000000c082b604cc3f621d4b4a658044b663c406056fcc725bdaf6160053406c20b9316135000140cee6355250028d59e36000b9a3cd3e6fa4b20af000092732a86b8c002811d6021d0441dc60280000008983c7070c000000425800077e5d463b00000003e7115af912b8157595800192e4b661300000000005570000f8816704c8dd91560de00007097fa99c0932e24000a1d5fb0d9170e7063b3000111a00000000010c400027e90600566aa0b5a4fc14e0ce1fc8000504b4243ea800c205d65788fc42f82a1292800000065f00005fcad40000000000d4648a00000000003494f10000a1a0005938644de286a1d22fa02128164bd8000e24000000000000055b244acc468a00015a2f0890c3042d7b234000b0826809005fe00000027c0326bc95d205dc2ba0d50001064000bd60000000b4621e00000000003253ffa7740000003b280000006b50c40364d28ac1000301136600000030b80008ea03980000004ba000226c00010222a80000e41ec3c02ebc910b8b00014200624282f711c025c00043711508fc07b2a30e9c88e000615042819a0000001210d26b2823726f8000000300aa44000c4600000014b27ca1dd91cc68c1802c0000000000019880000008da2980e1c00000036c1f4d2722da0002721872c9a57721393b681f1490000bdaa271a5a2dc0000001ea8dbd56a1900760cec0000000000000cee79b61780000000000000048000a8d28eae4c8d200055e2c2ccc08fb29e8acd2c20002a215786d8000453809c00047c3bc11d94de51a00029e95760ba1d11cf468e00047600000000004d613a80000000000000a944294b6137101219557f9f744a0b41000081400000024fada0afc90930b8f1d16c4d44c69cace9600057d81180004f35911e2400094b394319c000c881a0224d1b8ada047a940f50b1c61d12f8fd4a6a4ca0fb91d08fc3292ba86722615cb2d94d821b2628af94f18a8e42496ecac03aa0002b98000b3d3102dd090a05d00000009d878734431f800000000000012d6a1514f00000002ca00000004340001008001762599089297184026a1e100011ec6d34388000000991361b1c400000000024148cc4800001bb0ccc0000000f7800000037a85682440000db25d90663b417f28451960f3107b1501766911671128a6c27833821294e41854f600000000002d700015aa0001d79fb4d963ab56290f402c00000000000006f80feb0d40001b55968000d7c0003691a057085b52b713e16be1a317d936c5dc8c50058e1830eb291559e08636bee21f0780332bd95a323602d03e056f16b4000ac93fd914546e0000002a20a560335a4934d50444400015c8000b3e0502f814b63b20960000796a5a40f0000000c8720786b4000b1e1e90cd048662d0e7312cf441db3bd2d6
  | 26 => 0x2cc607502a10edcf8e3d43f182412a85fb650837400066c3fe05540000000000ce84664df00000009c200056700000000000532104d342ac20419791e0000011a37d0e05ff1e61d898ee0000430a5c4180f900025d48000002bc9b9cc8606a2b200000002fc45d8000000be113600000000002271780ab2000170a4c4d7001031e9e3c00054131095ac0f200008c0000ef2a293aa8bf4f3e14764029798e688e607a8c852a3815b8093c2d800034a80000000000000000000000000000062818f11102a913e78a0f6800000003a25822c11200003a728d00005d0466093484e91c37eb254e2c9aa59b208c77808900000006b89795300000f900003c314fc25e000212a8ed7420d1512905c94a3e14212e0d88242e00004a13a47b339c2fd59402545042d88dcc6e5524820890666100019bd3de2a71a893fc71ea3f00000009b00003160b0c1826e2523932d74a9cd03a81b02e4ad262e116040663818f0cf4ca6592230a7105baafd03a050d1e226d22b86c4a045c35a39a0c5a61f24a100000000345072a98a389eb01e228d6465c61cb18619180001d488906a84ab51f1c08000ae11ce80000002b04061438000000491afbc000000070a134000000000000000000000000017b627a00000014c49021fc0000000b051542d8c44c02d098800171a0002e0000000032b0002a8c22e000557982c00070500000000000000000220000aa1000000000000000014b0bb0000000260055e0c410aaa6c00001f0002c5c856b8a288844d28cbe729004dc00049c00006781fa8694d880010265f828a09f4ba424655e898ceee9044c20f747dabf837817c02360292280a297f841b0098a647a698e06a000165807c63586a94ae607561108117888113102f0bbc27745c1f042c81d75a715fd55a36a50d0194d380ad4a9ab287d0474374911945e0004d0a8242762450248e20b160000002e600ae6b300009900006310bb199570400016b800059859300014ecce62ea63706bc7880006368e842de8402f9977014a0004d4933844a08a52980000003240001b1859600062000006300000000e6800052f37a0000000a6b4dd0a900005fa444000082a21245a0c4d23c000143067c0004b561480011ca00025d84c800000000005d000063b07d13a476a0004e7a2f88d8b9d00019e00000000000000000000145a300b828944bb96ad2260394e183a912e9e34b02270ff06ac02c3068000c020e688282b2c1e17410580009934428b6d8b27f52c4a390bce74f1c62bbd82854722b0c3957c8635b0065d0705964a18cd907414b19120ed458a315cf8a1d4509a42ce07317249985e60e089c86dd324825008a82c56f9250cfc7834c4a0e42acc4715b05b8bd09d81960634a621ba60600d469c29c276a13076049028d8dc06ea6800129344cec2831fb21d577490
  | 27 => 0x81c5bd00000000001b332100002f75aa813c0003900de2d718666ba01b0000000b7c0001dd0a0e5fe37183b52f09cb2a18c347c6a3d55c165c00020728b0a94fd20004db8000e6a21314d9f0c3f200028026ac0002a93a99dc04163ad287a22418400056401e05284ac38a1ef80000184b4192876237209e000081ca1e0a70bcc2be9ee0001068000000000065087822120582dc0006c94679c414947cd00000000000001040864e4c30a00009397a4c530002c684742523868001418a0229e0b1cdd647f52e800000086400027ec6a4ab600000002a008c0000000bee5f53722d84000121000145c0001630002b7013a4fb0540239466a5f5c60fac0006565ac042c0000c02f880015f886c1bf1a30cd004844300003960006340000c728b25a1800176c8594861a88d6e70322cae805b824a14697540c623b406a42903025651c0bb09eec653af0000f20342621969400016a5aa2b180000000cc26f14440002bd164552e0003241a287eac1514b07bc02a4935f10b9d6021fc13b0ae465e0001340544b4c57445e85314f209e00007493d20004c1a714de43843430ddc00039b448a290000ae030fa910c1a0ab5b61d70dbe98a32e0000c9846f17a9e4cb58a804b715
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xf51851c530440016a30a38a6088003d4d94714c110007a8328e29822037f92841c530440017a30838a60880dfe4610714c110005c8c20e29822037fc2821c530440017a30438a60880dff0608714c110005e0c10e29822000f53521c53044001ea2a438a60880e6d6a17414c110005acc2e829822000bd287905304406f7a10f20a6088076f4a1a414c1101bf69434829822037bd385905304406fea50b20a6088306f4616414c1101bfa8c2c829822000b51859053044001ea6cb20a6088303d4196414c11010de8c24829822000f93749053044001f20e920a6088002f460a414c110607a9a94829822000f515290530440013b70ea0a60880027621d414c1101bfc820a829822000dd38750530440017a50ea0a6088002f421d414c110006e843a829822001bd28650530440037a10ca0a60882fef4e15414c1105fde8c2a829822000f5365505304417dea0caa0a6088096f4e11414c1101bfc9c22829822000f92745053044001f22e8a0a6088003e4d91414c110007c83228298220bef9354505304417df20a8a0a6088002f4e09414c1105f7a9a92829822000f51525053044001f2684a0a6088003e4509414c110005e943c429822037bd08788530440837a50d10a60880dfb4a1a214c1101bde9c2c4298220bdbd1858853044001ea6cb10a60882f3d4196214c1101bde9c24429822000bd184885304402f7a30510a6088003f0dca214c1101c7e0394429822038f53528853044071ea2a510a608800276e1d214c110004ec43a429822037fc0214853044001ba70e90a6088002f4a1d214c110005e843a429822000dd08748530440037a50c90a6088006f4219214c1105dde9c2a4298220bbbd1854853044001ea6ca90a60882ebd4195214c110005e9c22429822000bd18448530440357a70490a60880dff0e09214c1101c7e1392429822000fc1724853044001f86c490a60880e3f0189214c1101c7a9a92429822038f5152485304409d8f0edb2a40880039ae195248110005b5432a49022000b68865492044001cd10ca92408800b9add95248110017343b2a49022000f62815492044001ec302a9240880cf9ad85524811019fb1b0aa49022000f6152dc520440016e30a38a4088002ec6107148110007b0a90e29022000b718590520440017c30520a4088003d854a4148110007b0a92829022000fa14250520440033d10e90a40880173a1d9214811002ef038a429022001be087485204400bbc10e90a4088006f8a19214811000df0432429022002ee0864852044005dc6ec90a4088017789d9214811002ef03b2429022002ee07648520441737c70a90a40882e6f86152148110007b1b2a4290220b8f606548520440017c70890a4088002f86112148110007e1c1a4290220b7fc083485204416dbc6e690a40882db785cd2148110
  | 1 => 0x90cb8aa488102d9e0971549100145f424eda12200087f855db42440090f90abb684880022fe1d64d091018d4e41ac9a122002aac8259342440031e90cb8e84880121fa1776509100043ec2eeca12200087f855d942440090f90abb284880022fe1176509100046fc1aeca1220038dc835d942440011df04bb2848800a2f21d64509101754e41ac8a122002aac82591424409f0f90cbae82881361fe1f65d05100043ec3ecba0a2047974865d641440012ef04bac82880171dd81759051002eb9b02eb20a2000d57305d64144001ae460bac8288003554c17590510006b8982eb20a2000d72205d641440012ef0fb2c82880025d61d52905100062e39ecaa0a2000c9c73d9141440018becbb9a828800317197735051026e3a3b6caa0a209fcd476dcd4144001bc441b9282880cf1d1d95250510006b3b92a4a0a2000c5c73d95214409dcc843b2a428800317d9773485100062e32ee690a2000ccc73d8921440031f50db8242881371d1db654851000732316ca90a200097585dd121440031e90cba24288257351db734851027dad436ca982203ae5a86d953044001cb6edb2a6088003961db654c110005acc16ca982204df5381d95304409bea103b2a608813796d87654c11026fa9b0eca9822037ada869d130440015b30d3a26088057361da744c1101bde940ce89822000bd1819d130440015b70cba260880deb6219744c110005adc2ae89822039b58855d130440017a702ba260880def4205744c1103de6c3b0e89822039b5a851d130440016b30a3a260880def4a04744c110005e8c08e89822039b5a8599130440016b30b3226088086f4606644c110034ec43ac89822000b5b8559130440736b10ab226088002f2e09644c1101c5e4412c89822029bd3815913044001d32c83226088002b6e19724c1101bd6c432e49822038dc8725c930440017a702b9260880def4205724c1101cdac42ec498220069d88758930440016b70ab1260880e6d6215624c110005cdc22c49822000b98845893044187d90c4b126088132f4e05624c110005ad432a49822000b58865493044069cb6eca9260880d3961d9524c110255adc12a49822039f4b825493044001ea502a926088003d4605524c11019f2db0aa49822033f5361549304406f7a503a126088002f4607424c11001d6dc36e29822001ad886dc5304406f9b0edb8a60881aef4a1f714c11000de9436e29822001bd086dc5304406fba4edb8a608830b741db714c110005e9c2ee29822000bd185dc53044001ea6cbb8a6088003d4197714c110005e8c26e29822000bd182dc53044001ba6e5b8a6088003745cb714c110007a9a96e29822000f5152dc530440dd7a50e38a60880df74a1c714c11036de9430e29822037ed2861c5304406f7a70a38a60880dfd4a14714c110005e8c28e29822037
  | 2 => 0x375591100046fc1aeab2220038dc835d564440011df04baac88800a3b20975591100043f438eab2220038de87dcd64440018beebb9ac888003171d773591100046fc06e6b2220008dd80dcd64440010ff0ab9ac8880121f21573591100045fc22e6b2220008ef825cd64440051d904b9ac88800237a1c73591100062fba8e6b222000c5c751cd644400193ee839ac88800a3ba1f725911000637baee4b222000c6c75dc9644400199ee7b92c888003331cf725911000637c2ee4b222000c6c85dc9644400199e61b92c888003334c3725911000637ba8e4b222000c6c751c9644400195ee8392c88800333dcc725911000666398e4b22200087e87d4964440090f90fa92c88800317dcf52591106262e39ea4b222000c6f72d4964440058d8e5a92c88813f1d5c465191100045fc3ac83222000a9c83590644400155904b20c8880029b60b75d891000536c10ebb12200087f855d362440090f90aba6c48800237e0d74d891001c6e41ae9b12200087f855cf62440090f90ab9ec4880022fe1173d891004c5e422e7b12200487e86dd5624409b0f90dbaac4880021fa1f65589100062e39ecab12200087e8719562440018b8e632ac4880030fd9774589100061e32ee8b122000c3f651d16244001878ca3a2c4880032b18874589100062fb2ee6b122000c5c65dcd62440090fd0fbaac48800317cc375589100062e986eab1220008bf845d5624401317908baac48800237e0d755891001c6e41aeab12200087e871d5624401317d0fba2c4880030fdd774589100061e3aee8b122000c3f52dd1624400187aa5ba2c48800327cc374589100064e986e8b122000c3f751d16244001878ea3a2c48800e37a1f73589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062fa96e6b122000c5d52dcd62440011bf01b9ac4880023760373589100043fc2ae6b12200487c855cd624400117f08b9ac4880262f211735891000477c12e6b1220008de871cd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd6244001958e9b92c488003331cf72589100043f434eca922000a6d829d952440010fb053b2a4880031b60a76549100062f984eca922000c5d309d952440018de413b2a4880031b48276549100051fc22eca92204ba3c845d952440014bf06bb2a4880d29720d765491000537c12eca92200087e861d952440090ff043b2a4880121f60876549100063ac08eca922000c76211d952440018ea423b2a48800317cc076549100062e980eca922000c6f201d952440018f4403b2a4880031b48076549100063c900eca92200087f8759152440010f90eb22a48800297e0d64549101a52e41ac8a922000a6f8259152440054d904b22a4880031d1da71549100059ac24e2a92203db65829c552440674e
  | 3 => 0xda0a40008dd839db41480594790ab2682900063b21972d0520004b7c3aa5a0a400096d8754b414800187cebb2482900063b2197290520004b7c3aa520a400096d8754a4148067ad4e0a9482900163e2197090520006b4a92e120a40038de839d941480011bb073b282900121fa1476505200043ec28eca0a40058bc8759141480494790ab2282900031bdd95250520006363b2a4a0a4000d4f7354941480b9a98e6a9282900032b1d942505202d6c639a84a0a400087f855d841480090f90abb082900022f61f641052000c76432e420a4000c6e7654841480018daeca9082900cf5a9c1521052002c7c432e020a4000d69525c041480012db0bba242900063b21974485204a6663b6e690a4000dc870dcd21480011bf06baac98800e3720d755931002c5f43ea8b262000c3f75d5164c40071bd0fb9ac98827a37a1c735931001e4e39e86b2620058bc8750d64c40018bee7a92c988313171cf52593100046fc1aeab1620038dc835d562c40090fd0bba2c5880021f6177458b1001c6f43ee6b162000c5f52dcd62c40018baa5b9ac588253368437358b104a66c886e6b1620948de871cd62c400b1d90e992c5880ce9da077654b102463b38eeca962000a5f835d952c40694b906bb2a5880029be097654b100052fc1ac8a962034a5c8359152c40014df04b22a58800a9b2096454b1062db3c12e2a962031a9c8359342c40090fd0bbb285880021f6177650b1000c7b40eeca1620008df835d942c40071b906bb285880162f21d6450b101754e41ac8a162002aac8259142c4001acee4a9283880025d61774487100043ec3cc7b2a200087f8758f654400147f08b1eca880028f21163d951000537c12c7b2a2000a6c8258f65440110fb0e316ca880028fa1062d95100051ec20c5b2a2000a5e8318b65440014bb06316ca880031b5c862d95102753c43261b2a2000c3f749d3654400187ae83a6ca8813a9da0474d951026d3ac08e9b2a204da7a801cf654409d4f30039eca880021fa1c43d95100043ec3887b2a2000c5f305cb65440018ba60b96ca880028fa1072d95100051ec20e5b2a2000a5e831cb65440014bb06396ca8813a9da0472d951026d3ac08e5b2a204da7a801cb654409d4f300396ca880021fa1e42d95100043ec3c85b2a2000a5e8390b65440014bb07216ca880021fa1c42d95100043ec3885b2a200087e878cb65440010fb0f196ca880028fa1232d95100051ec2465b2a200087e870cb65440010fb0e196ca881361fa1f21d95100043ec3e43b2a2000a9e8390b64440010fd0fb2ac888003171cf655911000636396cab22200087e8719564440018b8e632ac8880031b1c865591100062fb2ee6b222000c5c65dcd64440018decbb92c8880031b19772591100243f43eeab22200087d82dd564440018be61baac888003174c
  | 4 => 0x14c0013b301bb2429800317d4b76485300062ea96ec90a6000cd980dd9214c0019b421bb2429800237a1a7648530004afc2aec90a601095c855d9214c00133f08bb24298182672117648530004e7c12ec90a60009db805d9214c0212bd0a3b242980025761476485300062f428ec90a6000c5d851d9214c00199d043b242980033360876485300062fa90ec90a6000c5d521d9214c00199c423b2429800333084764853001c6fc00ec90a60038dd801d9214c00199e403b242980033348076485300066b880ec90a6000cda101d9214c0019aa203b2429804257a177448530004aec2ee890a60008df865d1214c0011b90cba242980de7321d6248530006663b2c490a6037bc481589214c19379700b12429800e37a0f75d91200046ec1eebb224000c3d75d53644800155b05aa6c8900023761e73d912001c6fc3ae7b224000c5f525cf64480018baa4b9ec89032237e0173d912007c6ec02e7b224003c9e73d0f644800717f0ea1ec8900021fe1571d91200243e42ae3b22400487e87dd564480010ff05baac8900021f60b75591200062f986eab224000c5d30dd5644800117f08baac8900021fa1c75591200061e3aee8b22400087f855cd64480090f90ab9ac8900023de05735912002c7a40ae6b2240008bf8759064480014790ab20c8900ce9ba1a745492000536c34e8a924032c6c769d152480676d5013a2a490002da6027454920006b4384e8a924000a6f865d152480674d90cba2a490002dae01745492019db4402e8a9240b1c6c761d15248001a5ae83a2a4900035a1c074549202e5a741ec8a924000b4d83d915248001c5ec9322a490046da6026454920004b7c3ac8a92400e96c8759152480296d700b22a49031e5ba1c645492019cb6c38c8a924000e2d6419152480676d101b8aa4900ce9ba1a715492000536c34e2a92401cc6c769c5524800165d0938aa490002cb612715492019db5404e2a924000b69809c552480014df0cb8aa4900ce9b2197154920005a7c1ae2a92405cb4c835c552480016d700b8aa4900ceda201715492055e363b0e2a924033b6a801c552480016d30038aa4900cedaa1f705492019eb543ee0a924002b6a86dc152480056d10db82a4900cf5a9db705492019eb43b6e0a924000d6b74dc15248001ad2e9b82a490002da6077054920006b5b8ee0a924000d6971dc152480b571d07b2284900025b61771509200045fc22ebb0a40098bc845d761480010ff0aba6c2900121f21574d852003eb4b82a530a400e96c875496148001a5ee8a92c2900034b1d15258520006a7b9aa4b0a405cd4c735496148017ad6e0a92c29031a5be1d521852019cb6c3aa430a4000d2e745486148001a5ae8a90c290173539cd5218520006a6b9aa430a40008f7875846148001ccaa4b08c2900162fa1276d052001c6f41ce
  | 5 => 0x8003335ca62185303ae6cb84c430a6000ccd72188614c19d9b2e0310c29804257e1f5218530004aec3ea430a6000d1e74d48614c001a3ae9a90c29803f539cb5218530006a6b96a430a604ad5a70d48614c189ab2e1a90c29800257e1d5218530004aec3aa430a6000d1e74548614c001a3ae8a90c29803f539c95218530006a6b92a430a60009d787584614c19b7a700b08c2980de67a1276d0530004edc02eda0a6069d1f845d7414c0c1a3908bae829800257e0975d05306662fb02eba0a6000d5b605d7414c0c1a3e80bae82980034750175d0530006ad082eba0a6069b1c85593414c19773700b26829804257a1572d0530004afc3aa5a0a600095d8754b414c0033b1013b4829800276e017690530004afc12eb20a60cac5f605d6414c001ab6c0bac82980df55c4175905301bead082eb20a6037d59105d6414c001a3cebb248298003479d46490530084af42ae520a600095f8754a414c0012bb0ea9482980cf569c1529053001ced432e120a60039d8865c2414c001b36c8b848298003661917090530006ada92e120a6000d59525c2414c06fb3682b8482980df665057090530004ecc06eca0a6000c5f52dd9414c0019b301bb282980033684376505300046f434eca0a600095f855d9414c0212b90abb2829800267e117650530004e7c12eca0a600f9cc825d9414c0013b700bb2829804257a147650530004aec28eca0a6000c5e851d9414c0018bb0a3b282980032761076505300064faa0eca0a6000c9c541d9414c0018bea43b282980032790476505300064e208eca0a60038df801d9414c0071bb003b2829800327d0076505300064ea00eca0a6000cd7101d9414c0019b4203b28298003354407650530004cf43cc8a0a6000c9c76991414c1037330132282980de6721d64505300064e3b2c8a0a6065b1c85591414c11f73700b22829800317dd952505300062e3b2a4a0a6000d4f72549414c01fa98e4a928298003271db42505301bcce43a84a0a6000c9c76509414c01fb18e4a128298006762027610530004afc2aec20a601095c855d8414c0c133908bb0829800276e017610530004cec3ec820a600fd4e72548414c001a9ae4a9082980cf569c1521053001ced432e020a60039d8865c0414c001ab70ab808298003562157010530006cdb22e020a6060d98645c0414c001ab6a4b8082980035654970105301becda0ae020a6037dd2415c0414c06fb3282b80829818374505701053000cec404ed10a600095f855da214c0212b90abb4429800267e117688530304ce422ed10a60009db805da214c0011bf0cba4429800237219748853001ced432e110a60039d8865c2214c001ab70ab844298003562157088530006e5b12e110a60c3dc8625c2214c187ab6a4b84429830f5654970885301bee590ae110a6037dc9215c22
  | 6 => 0x15a7c12e2a926033b5a801c5524c0016b30038aa49800257e1576d0930084ae42aeda12600f99c845db424c0013b700bb68498002766037650930004afc2aeca12601095c855d9424c0013af02bb284980de752057650930004edc02eca12601095e851d9424c0012bb0a3b2849803e67a1f645093007dc7416c8a12601095e85dc5424c0012bb0bb8a849800267e1175d8530304ce422ebb0a60d29db805d7614c0033b100baec29800257e1574d8530084ae42ae9b0a60159db805d3614c0eb3b700b96c2980de3761f62d853007e66392c5b0a60c4d5b70d4b614c00153d09314c29800333dc8629853068eacb86a530a6049d597054a614c185ba2e1b0cc29804257a1f7558530004aec16eab0a6000c5f60dd5614c001ab6c1baac298003568437558530006ac886eab0a600099f845d5614c0c133908baac29800273e09755853007ce6412eab0a60009db805d5614c0012bd0e3aac29800347dd774585300068e3aee8b0a6000c9f60dd1614c001b36c1ba2c298003668437458530006cc886e8b0a6000d1f751d1614c001a38ea3a2c2980032798474585300064e308e8b0a60ccc9f601d1614c001b36c03a2c298003668407458530006cc880e8b0a600f9ce87dc9614c001a9eebb92c298003531d77258530006c7ba6e4b0a6000d8c74dc9614c001a9f0bb92c29800353217725853000667b06e4b0a6000dcb60dc9614c001b9421b92c29800372443725853000667bb0e4b0a6000d4f751c9614c001a98ea392c29800363dd07258530006c63a0e4b0a60008de87d89614c001938e9b12c29803f331cb62585301bc6e43ac4b0a6000c9c74589614c01f998e4b12c2980deb52056258530004af43ea4b0a601095c87d49614c001a3ee9a92c298003471d35258530006a7b96a4b0a600fd4c72d49614c1a1ab6e1a92c29800257a1d5258530004ae43aa4b0a6000d1f74549614c001a38e8a92c29800353dc9525853007ea6392a4b0a6056d5b70549614c0033b50fb82c29800356dd77058530006ac3aee0b0a6000d9b74dc1614c001b30e9b82c29800372dcb7058530006e4396e0b0a60cfdd371dc1614c0012bf04ba8c29832b17d817518530006adb02ea30a6037d57105d4614c06fab420ba8c2980035544175185301beac882ea30a60cac9f609d0614c001b36c13a0c2980df6684274185301becc884e830a60cac9f605d0614c001b36c0ba0c2980df65c4174185301becd082e830a6000d95105d0614c06fb3220ba0c298003275d264185300056ac08c830a6000d4e855c8614c001a9b0ab90c29800333991721853000666322e430a6037ccf615c8614c06f99ac2b90c29832b33d817218530006e5b02e430a6037dc7105c8614c06fb9420b90c2980037144172185301bee4882e430a60008dd87988614c00153d09310c29
  | 7 => 0x3d7419661500090fd0dbaac2a022e1f21b75585400043f43ecab0a8000c5c73d9561500018d8e5b2ac2a00021fa1c65585400062e398cab0a8000c6c7219561500018becbb9ac2a000317197735854000637b2ee4b0a8000c6c65dc9615011b87ae8328c2a00023de1d61185401661fc32eba0a808593c865d741500598790cbae82a00b20f21975d05400049fc12eba0a8009c3f605d74150013a76c0bae82a000347cc175d05400049fc3ecba0a80daa3e86d9741500594790bb1682a00024f61d52d05400051e432a5a0a808d87c865d641501170ff0fb2c82a00021f61f65905400062e39ecaa0a8000c5f65dcd41500018b8cbb9a82a00928fa1b655054045e1e3b6caa0a809ec9c76dcd4150001c38cbb9a82a0003661c373505401251e42ec4a0a8000a3c865494150067878eca9282a00034bdc952505400071a32ec2a0a800087f855da21500090f90abb442a000237e0d768854001c6e41aed10a80018bc865d22150001878caba442a00121fa1776485400043ec2eec90a80038de839d921500011bb073b242a0003171cf654854000c5e432e890a8000c5f65dcd21500018b8cbb9a42a0002a761b54d91300068ebaea9b22600095f855c7644c0212b90ab8ec898367665c364991306c6acb86a5322601095e87dd5644c0012bb05baac89800317d837559130006adb06eab226000d5a10dd5644c00133f08baac89800276e017559130004af438eab226000d1c75d91644c0012bd0fa92c8980425721f52591306beadb86a4b226000d5b75dc1644c001ab0ebb82c89835b66dd37059130304ce422ea3226060d1c845d4644c0012bf04ba8c89833317d817519130006adb02ea3226060d1f405d4644c001a3a80ba8c898003568417519130004cfc3ac83226000b1c85590644c1ab73700b20c898003475d75419130084afc3ea4322600095d87d48644c0012bf0aba6c4980425721574d893007c6ec38c9b12600095f855c7624c0212b90ab8ec49800267e117558930304ce422eab1260009d7815d5624c06f3a902baac49800276e01755893007d67414c8b12600face86d89624c1a9b96e5b82c49834fb218b7058930005acc06eca926000c5f769d9524c00169b053b2a498002c7e1176549300058e422eca926000b4f825d9524c0016af02bb2a498002d52057654930005adc02eca926000d1f749d1524c0e369b053a2a4981ced3e097454930005adc02e8a926033b58805d1524c001a3ae83a2a49803ed3a0b6454930005a6c16c8a92600fb4e82991524c00169b05322a49822ad66026454930004afc3ac8a92600095c87591524c1276b700b22a49800257a1c6454930004aec38c8a926000b1e849c5524c00163b0938aa498186d360a715493019dad404e2a926000b59809c5524c0014bf0cb8aa4980029721971549303
  | 8 => 0xdb9a8290b7a37a1f63505214ac6e43ec6a0a42008df835d760484071b906baec09080237e0d74d812101c6e41ae9b024200ad980dcf60484015b30039ec09080e37a1b73581214a46e436e6b0242008de87d8d60484018beebb1ac090803171d763581210064fba6c6b024200c9c74d8d60484011bd0e31ac09080317dd463581210062e3a8c6b024200c9f7418d6048401938e831ac09080a2f6137358b400243f42ee2b16800087d85dc562d006747d09bb2a5a012f0f9d37654b4000537c12eca968000a3f865d152d0097878ecba2a5a0376cbe097454b400049ec2ee2a1680058bd84dd561d00011bf06baac3a000e3720d755874001c6f43ee6b0e809f8de871cd61d00015b30039ac3a000317dcf52587406262e39ea4b0e8000c5f7354961d00698b8e6a92c3a00031bdc9525874001636392a4b0e802ec9c7350961d0005958e4a12c3a00928fa1776507400064e39eeca0e8000d2f7254941d00011bf06bb443a000e3720d76887400243f42eec90e800087d85dd921d000317d09bb243a000237e0d764874001c6e41aec90e80008bf865d121d00010fb0f31ecaa00029ba0a63d954000536c14c7b2a800087f8758f65500014bd07316caa00029760e62d954009c3ec38c5b2a8000c6d7218b65500018be60b96caa0003174c172d95404651f420e5b2a808ba3d841cb65501170fd0f216caa00021f61e42d95400052f41c85b2a8000a5d8390b65500010fd0f196caa00021f61e32d95404651f42465b2a8000a3d848cb65500010fd0e196caa00021f61c32d95404651f420e3b2a808ba3d841c765500010fd0e18ecaa00021f61c31d95404651f42063b2a8000a3d840c765500014dd0418ecaa00029b60831d954045d3d40063b2a8000a79800c765500010fd0f90ecaa00021f61f21d95400043f43843b2a800087d87087655011947d0810ecaa00028f61021d95400052f41843b2a8000a5d8308765501174f50010ecaa00029e60021d954000536c16ebb128000a6d821d762500010ff0ab9ec4a00121f21573d89400145e422e7b1280038ef874cb62500010ff0ab8ec4a00121f21571d89400043f43ecab12800087e8719562501b987ee832ac4a00021fa1a765494000536c14eca928000c6d829d952500018be613b2a4a0003174c2765494000637904eca928000a3f845d952500014df04bb2a4a00030f61076549400243fc10eca92800487d821d9525000187e843b2a4a00030f50876549400061f200eca928000c3c401d952500018be603b2a4a0003174c0765494000637900eca928000c6d201d9525000147d0d3a2a4a00030f1da745494043d96c14e8a928033a3c865d15250001878ecba2a4a0226cbe09745494046716216caa12808bc3c76d954250001c58c5b2a84a00024f617715094002c5e422ebb0a80dbc
  | 9 => 0x75580410062e986eab00824e87e871d560104014db043aac0208021fe1573580410243e42ae6b0082098bc845cd60104010fd0fa92c0208121f21f52580410043f43aa4b00820087c8754960104058dce4a92c0208163e21d505804102c7c43a60b0082008df835d564884071b906baac9108162fa1f54592210061fbaea8b244200aad82d5164884071bd0fb9ac91080317d4b73592210062ea96e6b2442008dd80dcd648853d1bd0e39ac91080f271cf435922102c5e43a86b2442008de87cc164884071b90f982c9108121fa1f75582210062f986eab044200c5d30dd5608849d0fd0e3aac1108029b60875582210043fc2ae6b04420487c855cd608840117f08b9ac1108262f211735822102c7c43a60b044200c5e7518f64484018baea31ec8908021f61e75d91210243fc3aebb22429887f825d764484910fb04baec8908031bc8175d91210261f3aca9b2242048bf8755364484090fd0bb9ec8908021f61773d91210051ec2881b224200aad82103644840156b02206c890b7f179d730d91210062ebae61b224209c3c645d6644840187aebb24c890803179d463991210062eba8c732242008df835d564484071b906baac8908023ee01755912100c7c402eab2242038de87dcd64484018bea5b9ac8908031754b73591210046ec06e6b2242008de871cd64484011bd0f982c89080e3721f30591210045fc3ac832242008dd87997634840153d0932ec690802a761265d8d210046fc3acbb1a4200a5e85d9363484014bb0bb26c6908023761e64d8d210052f42cc9b1a4200a5d8599363484011bf0eb26c6908623761c60d8d210052f428c1b1a4200a5d85183634840153d08306c690802a761060d8d210066cb80c1b1a4200a9e84dd7634840153b09baec690803175d475d8d210052f42ee9b1a4200a5d85dd363484014bd0b3a6c6908029761674d8d210070faa4a9b1a4200a5f855c363484014b90ab86c69080317e1570d8d210062e42ae1b1a4200c5f525c363484018baa4b86c69080297a1470d8d210052ec28e1b1a4200a9e841c3634840153b08386c690a56b3a0870d8d214a566c10e1b1a4294ad6811c3634852b5ab02386c69080237a1e50d8d210046ec3ca1b1a42008de8714363484011bb0e286c690802a7a1050d8d210054ec20a1b1a4295ace82143634840159b04286c690a52b5a0450d8d210056ac08a1b1a42008de8790363484011bb0f206c69080237a1c40d8d210046ec3881b1a4200a5e8510363484014bb0a206c690a56b3a0840d8d2100566c1081b1a4294ad68110363484015ab02206c690a5637a1e10d8d210046ec3c21b1a4209c3c645d741484018b8c6bae82908b28fa1764d05210061ebaec9a0a4200c5e75d8f41484018baebb1e82908272b19172d05210066631ae5a0a4224a3e85d91414852d1bd
  | 10 => 0xb1a8200a5d8518b63505898bceda96c6a088e3761c60d8d410052f428c1b1a8200a5d85183635040159d04306c6a0802b360860d8d410066cb80c1b1a829fa9e84dd7635053d53b09baec6a0803175d475d8d414ff0f2a6a9b1a8200a5e859cb63504014bb0b396c6a080333dca72d8d410052f428e5b1a8200a5d851cb635053f53d08396c6a0a7aa761072d8d4170d2ec2ca5b1a82008dd8790b63504014bd0b216c6a08029761642d8d414f72b28ea3b1a8200a5e85c8763504014bb0b90ec6a080297e1570d8d410052e42ae1b1a8200c5f855c363504018b90ab86c6a080317d4970d8d410052f428e1b1a8200a5d851c3635053f53d08386c6a0a7aa761070d8d4100567410e1b1a8200acd821c3635053d5ad02386c6a0a7eb560470d8d410046f43ca1b1a82008dd8794363504011bd0e286c6a08023761c50d8d414fd4f420a1b1a8200a9d84143635040159d04286c6a0802b360850d8d414f56b408a1b1a8200ad58114363504011bb0f206c6a080297a1720d8d410052ec2e41b1a82008de8788363504011bb0f106c6a080237a1c20d8d410046ec3841b1a8200a5e8508363504014bb0a106c6a0a7ea7a1020d8d410054ec2041b1a829ead68108363504015ab02106c6a08023761e10d8d4102477c3aa5b12820087f855c362504090f90ab86c4a080237a1f63589410046f438c6b128234a5e83dd952504014bb07bb2a4a08029b60a76549410052fc1aeca928234a5c835d952504014df04bb2a4a08029ee01765494119d3c402eca928248a3e86dd1525040187cedba2a4a08030f5d874549411a52f436c6a928200e4c62d8d52505c18bee5b1aa4a080393dcb63549410052ec06c6a928200e4f20d8d52504054dd0db12a4a080393d8f62549410072631ec4a928204a6e87d8952504094d90fb12a4a08038bdd36254941007163a6c4a928200a6d80d895250401c9e61b12a4a08924fa1676d094118d4f436c7a12822493c855c3425045d53d0db1a84a0a7b271db635094100746316c6a128202aae86d894250401d18c7b1284a080237e0d75d814101c6e41aebb028200ad980dcf60504015b30039ec0a080237e0d72d814101c6e41ae5b0282c4c5c73d4b60504698b8e6a96c0a080b1b1c952d814118e4e39e85b02822ec9c7350b6050405958e4a16c0a080e37a1b73581414f46e436e6b0282008de87d8d60504018beebb1ac0a0803171d7635814100666396c6b0282008de8718d60504018beea31ac0a0803171d4635814100666390c6b028200ccf63dc96050401998c7b92c0a08163b21d525884102c7643a64b108202a6c82dd952104014df04bb2a4208129ba1d62548410253643ac4a908248e2f415895210491c5a82b12a4208029be01625484100727982c4a90820487e87dd560104010fb05baac02080317cc3
  | 11 => 0xd04018bee5982cba0b3387d03305974104d1f42460b2e8200a3d848c165d04c14bb07182cba08268fa1030597410051ec2060b2e820087e87c8165d04010fb0f902cba08268fa1220597410051ec2440b2e8200a5e8388165d04014bb07102cba08021fa1c20597410043ec3840b2e8209a3e8408165d040147b08102cba080297a0c20597410052ec1840b2e82a5a768108165d04014eb02102cba08268fa1210597410051ec2420b2e8200a5e8384165d04014bb07082cba092e1f61e7558b4125d36c14eab1682058bc845d562d05c74df04baac5a08121fa177358b410043ec2ee6b1682098ee87cc962d041355d09992c5a08121fa177058b410043ec2ee0b1682dfc5e75cc162d04090ff05bb2a5a08121f60b7654b4125e1fa16eca968200c3d42dd952d04018be61bb2a5a08031bc837654b412451e422eca96824bc3c745d952d04014df04bb2a5a092f0f2117654b4171c3fc12eca968200c6f825d952d049787e80bb2a5a080317cc17654b4100637902eca968200c3d76dd152d040b17908baac1a080e37a0f72583410046ec1ee4b068200a5f835d165904014b906ba2cb20b8a9de0574596414c63b886e4b2c820087e8790965904014bd07212cb208029760e42596410043f43c64b2c820087d878c9659054347d09192cb208028f61232596410043f43864b2c820087d870c965904014bd07382cb208029760e705964102d3b40ce0b2c8246a75819c1659054347d08382cb208028f61070596410052f418e0b2c8200a5d831c165904014dd04382cb208029b608705964102d3b408e0b2c8228a75811c165904014bd07202cb208029760e405964102d3b40c80b2c8200a758190165904010fd0f982cb208021f61f30596410062f43e60b2c8200c5d87cc165904018bee5982cb20b2b95c4330596411bd2ec1c60b2c8205a76818c165904014eb03182cb208169da0430596410053ac0860b2c820087e87c8165904010fb0f902cb2080297a0e20596410052ec1c40b2c8205a768188165904014eb03102cb208021fa1c20596410043ec3840b2c82a1a3e84081659040147b08102cb2080297a0c20596410052ec1840b2c8205a768108165904014eb02102cb209229b60a7558a414c537c12eab14820487e85dcd62904010fb0bb9ac5208163b21d3258a410243f42ee0b14820087d85dc162905bf8bceb982c5208121fe0b7654a410243ec16eca948248c3f41dd9529049187a83bb2a52080317cc37654a4100637906eca948200a6f825d952904018df04bb2a52080317cc17654a4100637902eca948248c77105d95290543c5884b2a85208163e21d30582410046ec3ccbb1a8200ace82997635040159b0532ec6a080237e1d65d8d414f54f436a9b1a8200e1f65d5363504014bd0b316c6a08029761662d8d410052f428c5
  | 12 => 0x3531cf725855277eb3b96c2b0aa40296c82dc161548012bd0f982c2a90d25721f3058552776a7b9660b0aa43296f825d061548970fb0fb20c2a912f0f9d364185520043fc3ac830aa4ec96f825cc61548052d904b98c2a90025de1d611855276db3c12c230aa400a3d8418061548014eb02300c2a90ca5be0974d8152014b6412e9b02a43387d87d93605489787ce9b26c0a90021fe1d64d8152764b7c12e7b02a40296c825cf60548012bf06b8ec0a90d25720d71d81520e4b7c12e3b02a40296c825c760548670fb0fb0ec0a91231d9c761d81520043fc3ac3b02a44b93e87dd1605480187ec5ba2c0a90034bd8b74581520068f986e8b02a400d1d30dd16054801a5e41ba2c0a90034b483745815225e1ec30e8b02a4e3c3f621d16054801a5ec43a2c0a90030f98074581520061e300e8b02a400d1f301d16054801a3a603a2c0a90034bc80745815200696900e8b02a40087e87d916054897878e9b22c0a90ce1f21d645815225e1e3a2c8b02a40093f845cd605489727908b9ac0a90025be097358152004bbc0ae6b02a448974815cd6054801a5ee9b92c0a90034b1d372581520043f43ec2b02a400c3c74d8560548670f90eb0ac0a90030f1d16158152014bd43ec0b02a4ebd6b72d81605480517908b9ac3a10121fa1f75583420062f986eab068400c5d30dd560d09190fd0e3aac1a10029b60875583420043fc2ae6b06840487c855cd60d080517908b9ac1a100e37a0f71583420046ec1ee2b06840487f875d7615080187f08baec2a10030f21175d854200637902ebb0a840487e85dcf61508010fb0bb9ec2a100a2f61373d85426fe2f3ae61b0a8400c5d75cc361508011ef0eb08c2a100a2f61373d81420046fc1ae3b0284038dc835c7605081347d0939acba0baa8f612735974174d1fc22e6b2e8209a3c845cd65d05c7878e9b92cba0b8f0fd03725974104d1f424e4b2e82e8a3d849c965d04014bd07392cba08029760e725974173d1fc22e4b2e8209a3c845c965d0497878e8b92cba08268fa1332597410051ec2664b2e820087e878c965d04010fb0f192cba08268fa1232597410051ec2464b2e820087e870c965d04010fb0e192cba0b9a8fe11715974152e1e3a2e2b2e8200a5f835c565d04014b906b8acba08028fe11315974104d1e42262b2e820087e87c8565d04010fb0f90acba08268f213705974104d1f424e0b2e8283a3d849c165d0519878e9382cba080297a0e70597410052ec1ce0b2e82e5a3f845c165d041347908b82cba08268fa1070597411651ec20e0b2e82dac3c741c165d04014bd06382cba08029760c705974100537410e0b2e8200a6d821c165d054b4ed02382cba08029d60470597410043f43e60b2e820087d87cc165d04018bd0f982cba08031761f30597417270fba660b2e82cce1c74cc165
  | 13 => 0x80000140a801c00000000001000401404c02405c01403803004002402800c00001800c03801003c00001800000005802c05003402c00800000800400002c00402c00400000402000800800800003402401801c00002000000403801003008400c0d001400c0000f402000003800c01000003403003800800000800009800c07000000000000001c0cc02804c00403400801401400001400002401007c0040b000805000c0bc0380500e80680080180440a80080100040d400000c00007c0000040000a400005400c00000000000402401801800806800003801801801003000000400800002001001802800c00000400400004000000c01c00400000c01c00800001000400809800804800400405803400000c0140100980381bc00800001c00800c00400000804c06400400000005000401806800400c01800400406402c00401800401406400000012c00002000804005000801c00401c00801c01c02400013001406006c03405801000400801002000001c00006001c01401002c01400800000807800806c038008088155d92df04b9ec8a900a5b20973d91521a43ec3ec7b22a44ba3e84d8f645480147b0d206c8a9002cb60a40d91520051ec3081b22a400b2d82103645480166b02206c8a93e34b5cb649915225d1ec3ec9322a400c3d87d9264549ef87ae5b24c8a912f8b5cb64991520051ec24c1322a400c7970982645480147b08304c8a90029d60460991520070fb2661322a4f6d4d72cc2645489747d0db22c8a912f0fddb6459152004b7c12e6b22a43487c8758d645489747908b1ac8a93d74bdd372591527a6a7b9660b22a40093f8759064549e765f04b20c8a912e8fe1d64191520061fc3ac8322a40083f8759064549c747f04b20c8a90038be0964191520051fc0ac8322a400a3c8059064549e5c5e40b20c8a900257e0d71191521a4ae41ae2322a41c96f825c4645480187ac8b80c8a90028f61060191520053ac08c0322a400a3f86900645480165b05200c8a90038759330191522443ec38c9b0aa400c3d7419361548914ed02326c2a912e4fa1373d85520049ec26e7b0aa40496d82dcf61548910fb0fb1ec2a92630fd8a749855200697b14e930aa448c3f619d2615489187ac33a4c2a90034bc8274985524c61fb12e930aa400d2f625d26154801a5e40ba4c2a91234dc41749855225e1f3a6c930aa44bc3e7459261549e3acae5b0cc2a90030f9d260985520051ec20c130aa400c3e7418261548014eb02304c2a9003479d330985520068eba66130aa4f0d4d72cc2615480187ee9322c2a90021fa1c64585521a4af43ee6b0aa400c5f62dcd6154801a9ec5b9ac2a9002576037358552006a7906e6b0aa40096f825cd61548012bd0e39ac2a90d3171cf63585522443e43ac6b0aa448a748158d6154801a9ee7b92c2a9
  | 14 => 0x15435a000000000000016881375865969b16b880adb5d80ca13a6f80000000000011829a89b9590000000002c59b58000000001c28002fe8000000000003a18000000003a10000000002e198a800000036800080009af58000001fc8c680002619d0002893500000002813621e425a1473a22a42b800010420080000007821586880011f0d02ac00015eb152941de8000ee39e9528191ed9e61bf23598b027855a4219fa7c2a103039300014c25f0000bda37abe94413e82db381dc0b1a6d8001c832700000038bb538e514f8a4a1a889017b3d943a87129847bafb830662cf1750000002368003018002090001b535e80012480033799681c37f2fe0b2b279052d12deafd0b0ba28ad06e0e90e28000a4286800000260a8982b1782478003140000f70aea8ca8e95580010f8a30002683a818e2fca558e81e284d91e800000355a6390c80029907b0000001f390e8000001e22a700004e312029016396a23886a78b1a80005a80032099a160b979038002a23ab02b8e693a0001c5a2da11b42ab1ad196cac536c0ff80008f91883380023ab31b0a9922340dfb4a97ab1b831b58bac28b35c1c1054ab517089124ea931e0a068cfb39b902ee3a03102c7b1d1c61d4aa31e3a8406c0f497d0dba6413b8c7b4d861002c00001402400006000400000400010c0000000c802004000001801c07400001800000801c00001c00001001001800000c03001804400000800001401405403403c02402401800000c00804000400401807000800000401001001c0c800000c0ac00000003802000002803400400400408400000800405400002001400c03000000403c00c09800000401401002400001000805004004000c02801c00c00800400c02803000000c02802c04400404400000001003c09c00000401800001400806401c0e80000000041200000400000000040000c801400c02c01c00400403000403400c04801c0000000e400c01000400000000401801004000400402002006c0040ac0540180000000080400d800401000000c00002c01000007c00c0080000000040200040000000d800c00401800000400003401c00400000001004000802c00000000000800c00406800007003c02000800003c05c01002c03c00000802001c00401800808400000c0040a000800000000000400004803000004c04801401400401008c00405401c00401412001000004002003000401001002400c00002400401c03000001804c02c02401c01001400000000000800400400400c07404000c03002805801402c04401000000000001003c00c0000180080b000000800c0100000000080040280040b003002408c01002c08408800000000401801c0000000040000240000000300240000000040180040000000180e807004403c000004000000
  | 15 => 0x1eaa03ae08000dc0000749aa913319ac010b0001ec9e02eb2ae178a620003410948a280029800008e30f0738000c99950000002b78001f40000761d780020216b32489932e1a1882aed8329d285180000037791c80028e00020e80006b16f933106aa4aa90000000000001d32351469ab10600000011b26787c1bf8000003520f58000003569e6a84b3601b8002adab0b2411c000043ac900a336950b73302197a0439e05232ba38b30a901f78deb4a05a2702e1328398b3b2b8a8822f20b97ca9d09000f1b20692c31b1078b76a04b7c8423a6034a5e10834787a265221b03a8c29c9fdb818180002bf8f9917357b8119321a37082f85c8b401a1fc31596f37a36a3920129942a28003753abb388b235f9dd0f7b87901b6ab80a3a38c2da0eebad1da22e8ac147b39272ad7162ac138d25c9a50000001b98d336b0000bc2e80000bf0e08d10000b38b100019389232d81d08500000010c3911b299e8002c1929270a46ab907319c000040b02880a9a06182000012200032e8fba54b089ad88b08f1a3a26373a953a708cbacb32a722b3857a781260001a71320e3a828a6012000084297a10a1f0a1a831461ca3a48baa4099a83ab2511ba5a8fa8000209be8361f700db9c0390efab99ba1380000aab9c9300002bd1a4ba3af1345b0010597200020c80031480000693980000000000000035f0000f00c39a40000f08000003678000002c2a8a8001c711a0ca00037d06a0131d982880037802386cb9432a8621071599810b738cb2a18c35b25831b0fc87ea7f38b000000000000251ad527918bb54b012c9904a178002d624c2ec927800000386973b5825895ca6a040262a541749c000037b85699b391a231520002aa00036baad08d382a0280026e218b4b0000afabb8000001bb80008800004e80006aa959cf8000f1143231a92b0813416d9c09028980d41f69661572cdada84982f13e04ab9b37db1fa480002fa0000240002dbb51b4b80035535a9f5a801e325609418528a2b600000030b090b3c2570001a7a270000fd9af800004aeea908003aa16785d29bb870b5183a2ab4e3670e189f21ea2cb00b9db2fa601e12718469079f9b95b7b13d3a6b0fa972d8130839a7e879263313163835a6d2fa8849e9b9f02aae7b418b8912021837a2b0d81b320307109995e0f211a86b9b0000313b6fa8f8002a0986b710032798cb20809680e97e0de0fc00000031d80038500030d800140af70003741e580038f0000000d22e72f1ace1b3825b343218003238003a30453908bb9cf1c5000115241a5b022156977af005eb46296136b8489db8a3291ba96332100016133d20faff800392ae32a390e04d2252e5ae61d5b952d58a8ad000014487d2f604f2ef09d3408a0325999ac820601e80021330700032b3948001548ba32c0139b78000edb1c00000
  | 16 => 0x1bc07d90d9091870ea8718003762f88001cb23934f81f3798b021916e11f8be96b8a0b9395a1f5047058101380378a3dab71499790001202a59809269aa2442b101e076a1621d190800299800000000241200371ad3afd8bd14d8ab9d715fba09d5074181a5097136e12a1e8b5d1a217b017088b7f9bd30c3899a98371b7365b68b0400aa473129ef84c226aa8166acfba59d20ed20514d093a4d9ab8001f298fa450ab31eb098c319e02a0e11ee3691858f6adf2228c1af32d98e595d21691e0cc36812d0f83400ac80000004400000034f03d0003068b926716820b30b80b0dc80802713f34228393da6ba309f8023304af40000598001cc83824b35435709a33f994a4f80000012b112ba92a8aefaa615dbaa8cdadb266af921c245a1103b24990b8ebb7e2e290092c9241ee9310060542e69e181a96a97434c0d52d69fb11088db63a7aa6f1ef0e9af0ae499180192e9420592a1aab9cd288ad280020d04a1a58040503a9a4303fb179192ae9c48d3b8a8c2800199077a5e8002e900021e1ce8000002969580dd17a0c58bb026938ae4348988acc27727a09a8e7a312380340102f29b189f8002400ec2590c00a918f3051450588b333ca6e8001ae1f49671973b020d91d9a3022b8e0d9b372dcaf98028002dc2f51d110233036c8822a6a751a28639acb3b9860059df32333e1daaba15aa28a4a2249c1811bad9ce25c15f2820c83a79be25515635ba302e5164a659a03471b9000066a819fa00029da8db3aad096c00000c27f94a9e806728f39d24e3630c133e9f0a3e16a2d497da32b5e2dd93c2b317bb1c86d0e41840871ad2c494b3192af80522a22fba88918001100000001c98000a206f80002d3330aa21513aac0ade26615bb603af0000c489e80023f9250961618d48648d1a69b7e8cf171b090fa165310a5fb72052a2e22bb2f3448432b49f00a70e03640e72280db2bf1a8979900116225a532170448001d6814800208acab699ed21498212c0000000a818d96581fa27b9823c8ce03a05f0d5b8609726c800184a9f1361b894a1d02988001d19d9008913b289142690248000000c514ea0e0002c8b4900000000002c0000001f19af0000b49fe08c0a399d80018a00730a000135158937a7e0000002c70000001eb94280000025b8000e6141a1c80033100028b800029b8f9ae94036491d2ba8f53999dda74831311acd085b1e25110a38d8142ec1faacca1dafb24ca7b97e8770c61ea03e80000033204b800000003818998a072c41b83452bc34303d9348108ec8f92210c8b5605704832c95124f0000d292e1358001eb34ca182e99f30cbb5cb18b0606e9de08b93700007592a8000000dd8c9072ab597c291a3f000000000201ad300039a303064148a1b2348a5b1a0550f88e493f931a3614b80001500008191130e287a6b
  | 17 => 0x18ca0a96900e00005d8d7ba43842079bd8002f68000000000532012d221b91480003e18e9d81bc89b3170000001e5000361922af830c84c89500000036d0000003498002d42bb12d80010a80000000013380000038eabe27d00000000000000033480030d0001ca87b8000af0b62240002cba8607ca85a48a3b8b780018d1199f600012386d85102ea199fd168ae20002ea0002cb0001c43532599c2000294af4b839cc038a7c8250860fe1f88000000000000001b412f80034413b24a83cb18335862b268f1955000048b1f0000f400035133f09299c8d9000000329b820703591e783f000000000322030a500b808a03200037700010d1890003650000001ec276079951b2d21000000007fb612370001b080027d948275a5d2df80000022c2a50838020000a980017f9db3b09ff9c7b9ab7c0ae02e19297f1db9898159d39a826aab01762bd9e49dcb0e800305b60928b50a292490000002eb89e0a69b48001b60d72a0067a73a059232f380029e1410c70eb1980978608df2688b5a80ac21ff0be10f14e175b992fc087807a0c24627b145a93b22a44ad7b3a153b6db261ac3160e88092ea8001802ac94f0d08d89622f20003890832538001b68002ca098953000070a1287f212243a7305c1492f7b0790322093288a87a8c20cea8500b8560680281c31f92ff1732912fbb203960e22e007529c2b69d42ed23b23995b0fd000050a429958000f605e04b2b201cb7aabc81d99f0caad93ae0003a529e9e725687e06f24b8000000002ab0d6000311095a9b0feb52800277a6481108e9e90e303c09c80fa6c0f396e9881d622233380d1a909c1c3aaf39712599b8ff1a121426105f9cd9d08652712c3a578da9f125d8bf94cb703889bb01b2a7ab41c88f2a2d0ea046116add164160359b43a61b74927252346a3e8a50930000001fe921b4e920a76b629910a12b29700008539772aaa3c2322099a61960cc9088c084f90995c2203668cd23d3ae9212a9b9b9f239f91580136ea299c92330199828b680011780020f0000bca8d1fbb661768490d6b350410000001c69a680005b2e880000019021f93c97285bad88da0000213859d88002743790fb1cb83320a0428000000001df80000034800007229f88996d12b8600c40698a79831391a08ef0002c615792803b8b9950041845a3392f25280002c80036f2e391180018780000000034d2c680024d0633728352cea920f30
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x8009c1a004c4e000068c6007290003c10a4b69e0000003088820400000200010001020201000000000100000600010003000306000206050000000200080048d6448059064548014389059170191520040f65f86900645480141f9759330191520060d9d18118261548014359118074581520050b259201d1605480182c7460870597410060d1d1811c165d045903c9761220597411640f25d8484165d040103f985d874549410050e241761d152505f344d929d463d91211640fe6175d934148401499901cf76507400050b64a401d9525000103d9810076549400050b648401d9525000143591100765494000706101301d95250001c493048076549400040f25985dc542501c981c86cc175d05406d40fa5b87d97415000103d9721952d05400060b21b72549415000111c98501751913000447e61741d1524c001518905d0745493000523648611d1614c0014989644074585300062520474589614c0014c5911917218530006265c284988614c00188e845ca621853035447261405d7414c00141e95904765053000526642411d9414c00149990104765053000507255401d9414c001c914044076505300060721476591414c00154992215701053000552648855c2214c0014c990884764853000433660211d9214c0014c990084764853000730481101d9214c001561911c274549200050b259741d15248001528905d0745492000558644701d1524800122f9859064549200050b25d64191524800182c76a1271549200045ae6174dc1524800906c985d952105200040fe61741d36544001c4930480765491000718485201d9524406f551938c175905100055464e205d641440018d076604744c1100052625d64191304400171194a05524c1105ddd064a81549304417b74392605524c110004e4e5185dc5304400135395613714c110004d4e49851c5304400135398d94714c110004d4660651c53044001b1365610714c110006c4195841c53044001b4295608714c110006d0655821c53044001b4365608714c110006d0195821c5304400135198d48714c110006c4613521c53044001b4182d48714c110004d4661521c53044001b1184548714c110006d0609521c5304418335096616414c110004d4e4985905304400135398d96414c110004d46615290530440013519521d414c11000664e10875053044001392989d1414c1101bce4261745053044001990875d1414c1105f5c4255745053044001b4382549414c110004d46548748530440019c38221d214c110004d465784485304406f3c0985c9214c1100067021d72485304406f6c0965c9214c110005c865281549204406766096605524811019cd8661521c52044001b21845487148110004d866152905204409dc6076d952148110004d865784485204412bac086e0d2148110
  | 1 => 0x8400b234587c762c007a020000000012cc00c85a006600320074008e00800000002a488a00004228926e00009a2000da561eba408cbe54000060bc00626a0000b0a600ae0000d89600524aaaacb40a000000460e44002494ca000000001c22641800a23e7000000000000608000cce00d086505e00261400003a16b80036a0005c04c0c47ed4c200006c7800382ed2a8d69
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x80a0006c240e00500486342482c8b80c8a9002c09a2101301d95250001608d0880980eca928000944684905d074549300058214aa02203b28298002521a1241741d1524800148952f0843a829822000c44254875d1414c110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x6
  | 5 => 0x2
  | 6 => 0x94c
  | 7 => 0x94b
  | 8 => 0x94e
  | 9 => 0x5
  | 10 => 0x138e
  | 11 => 0x138b
  | 12 => 0x138c
  | 13 => 0x98c
  | 14 => 0x98e
  | 15 => 0x9cb
  | 16 => 0x9ce
  | 17 => 0xa0b
  | 18 => 0xa0c
  | 19 => 0xa0e
  | 20 => 0x180b
  | 21 => 0x180c
  | 22 => 0x180e
  | 23 => 0xb09
  | 24 => 0xb0c
  | 25 => 0xb0e
  | 26 => 0x1409
  | 27 => 0x140c
  | 28 => 0x140e
  | 29 => 0x289
  | 30 => 0x28b
  | 31 => 0x28c
  | 32 => 0x28e
  | 33 => 0xb89
  | 34 => 0xb8b
  | 35 => 0xb8c
  | 36 => 0xb8e
  | 37 => 0x1489
  | 38 => 0x148b
  | 39 => 0x148c
  | 40 => 0x148e
  | 41 => 0x1849
  | 42 => 0x184b
  | 43 => 0x184c
  | 44 => 0x184e
  | 45 => 0xd09
  | 46 => 0xd0c
  | 47 => 0xd0e
  | 48 => 0x1889
  | 49 => 0x188c
  | 50 => 0x188e
  | 51 => 0xd49
  | 52 => 0xd4c
  | 53 => 0x98956
  | 54 => 0x94994
  | 55 => 0x9ca
  | 56 => 0x9c953
  | 57 => 0x9c956
  | 58 => 0x949d6
  | 59 => 0xb0954
  | 60 => 0xb0956
  | 61 => 0x94b16
  | 62 => 0x140954
  | 63 => 0x140956
  | 64 => 0x95416
  | 65 => 0x209
  | 66 => 0xb8954
  | 67 => 0xb8956
  | 68 => 0x94b96
  | 69 => 0x148954
  | 70 => 0x148956
  | 71 => 0x95496
  | 72 => 0xd4a
  | 73 => 0xd4954
  | 74 => 0x1a09
  | 75 => 0xd4d
  | 76 => 0x1549
  | 77 => 0x14c9
  | 78 => 0x134a
  | 79 => 0x2c9
  | 80 => 0xb1394
  | 81 => 0x138b16
  | 82 => 0x4b
  | 83 => 0xb9396
  | 84 => 0xb9394
  | 85 => 0x138b96
  | 86 => 0xd5394
  | 87 => 0xb0994
  | 88 => 0x98b16
  | 89 => 0x124b
  | 90 => 0xd0994
  | 91 => 0x98d16
  | 92 => 0xd4994
  | 93 => 0x98d54
  | 94 => 0x1609
  | 95 => 0x130b
  | 96 => 0x9cd
  | 97 => 0x9cb16
  | 98 => 0x9d416
  | 99 => 0x289d6
  | 100 => 0x9c296
  | 101 => 0xb89d6
  | 102 => 0x9cb96
  | 103 => 0x1489d6
  | 104 => 0x9d496
  | 105 => 0x1849d6
  | 106 => 0x9d856
  | 107 => 0x249
  | 108 => 0x4c
  | 109 => 0x1449
  | 110 => 0x16c9
  | 111 => 0xb49
  | 112 => 0x124c
  | 113 => 0x9cd16
  | 114 => 0x409
  | 115 => 0x9d896
  | 116 => 0xcc9
  | 117 => 0x150c
  | 118 => 0x1709
  | 119 => 0x15c9
  | 120 => 0x128c
  | 121 => 0x3c9
  | 122 => 0x589
  | 123 => 0x10c
  | 124 => 0x18c9
  | 125 => 0x1789
  | 126 => 0xe89
  | 127 => 0x130c
  | 128 => 0xb8a16
  | 129 => 0xb8a14
  | 130 => 0xa0b96
  | 131 => 0x184a16
  | 132 => 0x184a14
  | 133 => 0xa1856
  | 134 => 0xd0a16
  | 135 => 0xa0d16
  | 136 => 0x188a16
  | 137 => 0xa1896
  | 138 => 0xd4a14
  | 139 => 0x1949
  | 140 => 0x134d
  | 141 => 0x749
  | 142 => 0xb9816
  | 143 => 0xb9814
  | 144 => 0x180b96
  | 145 => 0x180d16
  | 146 => 0x10b
  | 147 => 0xd5814
  | 148 => 0x15ca
  | 149 => 0x144b
  | 150 => 0x24b
  | 151 => 0xd4294
  | 152 => 0x1a0a
  | 153 => 0xd0b94
  | 154 => 0xb8d14
  | 155 => 0x188b94
  | 156 => 0xb9894
  | 157 => 0xd4b94
  | 158 => 0x18ca
  | 159 => 0x144d
  | 160 => 0xd5494
  | 161 => 0xbcd
  | 162 => 0xd1854
  | 163 => 0x184d14
  | 164 => 0xd5854
  | 165 => 0x104a
  | 166 => 0xa4b
  | 167 => 0x128e
  | 168 => 0x198b
  | 169 => 0x150e
  | 170 => 0x2cb
  | 171 => 0x20e
  | 172 => 0x19cb
  | 173 => 0xbcb
  | 174 => 0x14cb
  | 175 => 0x154e
  | 176 => 0x74b
  | 177 => 0x40e
  | 178 => 0x194b
  | 179 => 0x1a8b
  | 180 => 0x104b
  | 181 => 0x160e
  | 182 => 0xb09499c
  | 183 => 0xb09895c
  | 184 => 0xb09895e
  | 185 => 0x9894b1e
  | 186 => 0xb09c95e
  | 187 => 0x9c94b1e
  | 188 => 0x1409c95e
  | 189 => 0x9c9541e
  | 190 => 0xb89c95e
  | 191 => 0x9c94b9e
  | 192 => 0x1489c95e
  | 193 => 0x9c9549e
  | 194 => 0x124954
  | 195 => 0x949d3
  | 196 => 0x1a0c
  | 197 => 0x139416
  | 198 => 0x99556
  | 199 => 0x99616
  | 200 => 0x168b
  | 201 => 0xb1514
  | 202 => 0x168a
  | 203 => 0x185814
  | 204 => 0x168d
  | 205 => 0x5394
  | 206 => 0x8c
  | 207 => 0x139254
  | 208 => 0x1a1394
  | 209 => 0x1a0954
  | 210 => 0x198c
  | 211 => 0x1689d3
  | 212 => 0x151294
  | 213 => 0x11814
  | 214 => 0x181314
  | 215 => 0x1a1814
  | 216 => 0x1a0a14
  | 217 => 0x130a14
  | 218 => 0x14d
  | 219 => 0x74b91
  | 220 => 0x75611
  | 221 => 0x181896
  | 222 => 0x24d
  | 223 => 0x168e
  | 224 => 0xb9a14
  | 225 => 0xb8d54
  | 226 => 0x149856
  | 227 => 0x1a0d
  | 228 => 0x169856
  | 229 => 0x185316
  | 230 => 0x185496
  | 231 => 0x185616
  | 232 => 0x184d16
  | 233 => 0x185796
  | 234 => 0x184e96
  | 235 => 0x151296
  | 236 => 0x170e
  | 237 => 0x21416
  | 238 => 0x169416
  | 239 => 0x155416
  | 240 => 0x168b16
  | 241 => 0x154b16
  | 242 => 0x104753
  | 243 => 0x41896
  | 244 => 0x169896
  | 245 => 0x189616
  | 246 => 0x168d16
  | 247 => 0x1a9953
  | 248 => 0x160d16
  | 249 => 0x3cd52
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1373
  | 6 => 3235
  | 5 => 1890
  | 4 => 110
  | 3 => 8
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (55828+((h/457+packedAt gbK7 (50801+(h % 457)*11) 11) % 1812)*12) 12
  | 6 => packedAt gbK6 (169294+((h/1078+packedAt gbK6 (155280+(h % 1078)*13) 13) % 4271)*13) 13
  | 5 => packedAt gbK5 (119070+((h/630+packedAt gbK5 (111510+(h % 630)*12) 12) % 2269)*12) 12
  | 4 => packedAt gbK4 (7988+((h/36+packedAt gbK4 (7700+(h % 36)*8) 8) % 176)*8) 8
  | 3 => packedAt gbK3 (656+((h/2+packedAt gbK3 (648+(h % 2)*4) 4) % 14)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xe0fffc3c0e1f87fff0fe0381ff0a299e0cf70f
  | 1 => 0x7f0703c00fe1f8703f0ffffe0f15d6683349f3
  | 2 => 0x7ff803fff001ff803ff003fff0e61871c38e3c
  | 3 => 0x800003fffffe00003ffffc0000f81f81fc0fc0
  | 4 => 0x3ffffffffffc000000000ffe001fff000
  | 5 => 0xfffffc00000000000000000000fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x80090804020200909012088022000082041305
  | 1 => 0x21021080042088210104a1280c00c228114052
  | 2 => 0x5ad02159900155022aa01255c0661850c28c28
  | 3 => 0x8404a6eab540004bcc9580462b81d816c0f80
  | 4 => 0x108083b34d99e64f0000601884df6001bbe000
  | 5 => 0x7ce4f003811044080881806108ffbf7c000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeeeeeafeeaece8feeeeeeafeeaece8feeeeeeafeeaece8feeeeeeafeeaece8feeeeeeafeeaece8feeeeeeafeeaece8feeeeeeafeeaece8feeeeeeafeeaece8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37263
namespace PEqualNP.Outside.L_meta_37263
open PEqualNP.Outside.L_meta_37263.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 26 := bs0_3_0
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
theorem bs0_4_96 : Interval s0Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_128 : Interval s0Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 134 := (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 (concat bs0_4_96 bs0_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 48 := (concat bs0_5_0 bs0_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
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
theorem bs3_2_0 : Interval s3Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 14 := bs3_2_0
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
theorem bs3_3_224 : Interval s3Atlas 3 224 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 228 := (concat (concat (concat bs3_3_0 bs3_3_32) (concat bs3_3_64 bs3_3_96)) (concat (concat bs3_3_128 bs3_3_160) (concat bs3_3_192 bs3_3_224)))
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
theorem bs3_4_1312 : Interval s3Atlas 4 1312 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1340 := (concat (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 (concat bs3_4_96 bs3_4_128))) (concat (concat bs3_4_160 bs3_4_192) (concat bs3_4_224 (concat bs3_4_256 bs3_4_288)))) (concat (concat (concat bs3_4_320 bs3_4_352) (concat bs3_4_384 (concat bs3_4_416 bs3_4_448))) (concat (concat bs3_4_480 (concat bs3_4_512 bs3_4_544)) (concat bs3_4_576 (concat bs3_4_608 bs3_4_640))))) (concat (concat (concat (concat bs3_4_672 bs3_4_704) (concat bs3_4_736 (concat bs3_4_768 bs3_4_800))) (concat (concat bs3_4_832 bs3_4_864) (concat bs3_4_896 (concat bs3_4_928 bs3_4_960)))) (concat (concat (concat bs3_4_992 bs3_4_1024) (concat bs3_4_1056 (concat bs3_4_1088 bs3_4_1120))) (concat (concat bs3_4_1152 (concat bs3_4_1184 bs3_4_1216)) (concat bs3_4_1248 (concat bs3_4_1280 bs3_4_1312))))))
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
theorem bs3_5_864 : Interval s3Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 890 := (concat (concat (concat (concat bs3_5_0 (concat bs3_5_32 bs3_5_64)) (concat (concat bs3_5_96 bs3_5_128) (concat bs3_5_160 bs3_5_192))) (concat (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)) (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 bs3_5_416)))) (concat (concat (concat bs3_5_448 (concat bs3_5_480 bs3_5_512)) (concat (concat bs3_5_544 bs3_5_576) (concat bs3_5_608 bs3_5_640))) (concat (concat bs3_5_672 (concat bs3_5_704 bs3_5_736)) (concat (concat bs3_5_768 bs3_5_800) (concat bs3_5_832 bs3_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 44 := (concat bs3_6_0 bs3_6_32)
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
theorem bs4_3_0 : Interval s4Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 7 := bs4_3_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 15 := bs5_2_0
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
theorem bs5_4_768 : Interval s5Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_800 : Interval s5Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_832 : Interval s5Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_864 : Interval s5Atlas 4 864 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 894 := (concat (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat bs5_4_224 (concat bs5_4_256 bs5_4_288)) (concat (concat bs5_4_320 bs5_4_352) (concat bs5_4_384 bs5_4_416)))) (concat (concat (concat bs5_4_448 (concat bs5_4_480 bs5_4_512)) (concat (concat bs5_4_544 bs5_4_576) (concat bs5_4_608 bs5_4_640))) (concat (concat bs5_4_672 (concat bs5_4_704 bs5_4_736)) (concat (concat bs5_4_768 bs5_4_800) (concat bs5_4_832 bs5_4_864)))))
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
theorem bs5_5_800 : Interval s5Atlas 5 800 20 := block_range (n:=20) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 820 := (concat (concat (concat (concat bs5_5_0 (concat bs5_5_32 bs5_5_64)) (concat bs5_5_96 (concat bs5_5_128 bs5_5_160))) (concat (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)) (concat (concat bs5_5_288 bs5_5_320) (concat bs5_5_352 bs5_5_384)))) (concat (concat (concat bs5_5_416 (concat bs5_5_448 bs5_5_480)) (concat bs5_5_512 (concat bs5_5_544 bs5_5_576))) (concat (concat bs5_5_608 (concat bs5_5_640 bs5_5_672)) (concat (concat bs5_5_704 bs5_5_736) (concat bs5_5_768 bs5_5_800)))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 8 := bgb_3_0
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
theorem bgb_4_96 : Interval gbAtlas 4 96 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 110 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96))
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
theorem bgb_5_1888 : Interval gbAtlas 5 1888 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1890 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672))) (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800)) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928))))) (concat (concat (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 bgb_5_1152))) (concat (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)) (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504)) (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 bgb_5_1632))) (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760)) (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 bgb_5_1888))))))
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
theorem bgb_6_3232 : Interval gbAtlas 6 3232 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3235 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))))) (concat (concat (concat (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960))) (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 bgb_6_1184)))) (concat (concat (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280)) (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376))) (concat (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472)) (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 bgb_6_1600)))))) (concat (concat (concat (concat (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696)) (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792))) (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)))) (concat (concat (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176))) (concat (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272)) (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 bgb_6_2400))))) (concat (concat (concat (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)) (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592))) (concat (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688)) (concat (concat bgb_6_2720 bgb_6_2752) (concat bgb_6_2784 bgb_6_2816)))) (concat (concat (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912)) (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008))) (concat (concat bgb_6_3040 (concat bgb_6_3072 bgb_6_3104)) (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232)))))))
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
theorem bgb_7_1344 : Interval gbAtlas 7 1344 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1373 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)) (concat bgb_7_576 (concat bgb_7_608 bgb_7_640))))) (concat (concat (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800))) (concat (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992)))) (concat (concat (concat bgb_7_1024 bgb_7_1056) (concat bgb_7_1088 (concat bgb_7_1120 bgb_7_1152))) (concat (concat bgb_7_1184 (concat bgb_7_1216 bgb_7_1248)) (concat bgb_7_1280 (concat bgb_7_1312 bgb_7_1344))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 64 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeeeafeeaece8feeeeeeafeeaece8feeeeeeafeeaece8feeeeeeafeeaece8feeeeeeafeeaece8feeeeeeafeeaece8feeeeeeafeeaece8feeeeeeafeeaece8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071594 * 2 ^ 32 + 4276808936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37263.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,2]⟩,⟨.or,[2,4]⟩,⟨.or,[2,5]⟩,⟨.and,[1,7]⟩,⟨.and,[4,6]⟩,⟨.or,[1,10]⟩,⟨.or,[0,3]⟩,⟨.and,[11,12]⟩,⟨.or,[0,9]⟩,⟨.and,[8,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4276808936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4276808936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37263

open PEqualNP.Outside.L_meta_37263 in
theorem PEqualNP.Outside.L_meta_37263 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4276808936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4276808936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
