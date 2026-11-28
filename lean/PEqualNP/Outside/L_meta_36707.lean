import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36707.Model
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


end PEqualNP.Outside.L_meta_36707.Model

namespace PEqualNP.Outside.L_meta_36707
open PEqualNP.Outside.L_meta_36707.Model
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

def SBf (j : Nat) : Nat := [3, 6, 7, 8, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36707

namespace PEqualNP.Outside.L_meta_36707
open PEqualNP.Outside.L_meta_36707.Model
def s0K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s0K2 (i*4) 4
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s0K2 (5+((h/1+packedAt s0K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffdfc7fff87ffe3f
  | 3 => 0x6bf878ff8783cc
  | 4 => 0x73ff80fff803f0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffff8041102888a8d5
  | 2 => 0x20b2245455522a
  | 3 => 0x1517459d461b4c
  | 4 => 0xe2476e66463b0
  | _ => 0
def s0Atlas : Atlas := ⟨2,rawDecor 30 s0Pos s0Neg, 0xccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36707
namespace PEqualNP.Outside.L_meta_36707
open PEqualNP.Outside.L_meta_36707.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x2c2a000020208603069380a00040df32ee32dd32ed32cd32be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2800000000001280988238c43029aa7195314132c6994818d321029aa41853d4e20a6a9841c5328438a64086c10010
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x204288604c840b018132043813210010
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 10
  | 2 => 3
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | 2 => packedAt s1K2 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (228+((h/4+packedAt s1K4 (208+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s1K3 (285+((h/3+packedAt s1K3 (270+(h % 3)*5) 5) % 18)*5) 5
  | 2 => packedAt s1K2 (117+((h/1+packedAt s1K2 (114+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x7f807f807ffffffff80fe07f03fffffe447ff
  | 3 => 0xf80007fff807f00fffff0007ffc1fc0ff878c7
  | 4 => 0xfffff8000007fff00ffffff80001fff03f80f8
  | 5 => 0xfffffffffff800000ffffffffffe00003fff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x848304850501121208b1628b1422c92499b5b
  | 2 => 0x4295529534a32a4a4740aa855435572ca445ad
  | 3 => 0x56c6a4e4a53548ec8bd581266d91998f3868c6
  | 4 => 0x64e4c6c6c6c68c88ede6cdb40921e3c63e80f0
  | 5 => 0x8707070707070f0f0e78f1c78e390208377600
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0a0a0a000aaaaaaa0a0a0a000aaaaaaa0a0a0a000aaaaaaa0a0a0a000aaaaaaa0a0a0a000aaaaaaa0a0a0a000aaaaaaa0a0a0a000aaaaaaa0a0a0a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36707
namespace PEqualNP.Outside.L_meta_36707
open PEqualNP.Outside.L_meta_36707.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1e52380803000022004c6213e1c79b2c0001d009d500003411c0c41223005c200220059234654264a0000a5621014000ca890a0c10410c0004100050103ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x2b29082d91000014000e9f85802587260d8b0000241583078f1f1c88820016060ca89c181a96ac0a8d1d97998e1e8f8000188011a82510002a15170005000000001a0392829d098a2c8481ad0c1b23012290a70400a9aaa3a193a6aba11900000927a220a01e24949300069b8b920002090024007060831336000800c58c80040c00414083970240188b7a92876c5250ebea6a15714d429faa2653c544cb9a64194f943419eaa4835f53506b8a6a0dbd4941b6292837b50506f0a0a0e7d4d41ce29a83af5250758a4a0edd4541dda82833c5050770a0a0ce141419f2a0836e52cc6daa598cf952319eaa4636e528c6daa518cf950319eaa0635e53c86baa790cf952219eaa4435e53886baa710cf950219eaa0435e53902baa7205b94a40b6a94819e539033aa7206b94a40d6a94813d519027ca1204f544409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2dca4185b548309f2a6413d54c827ea8904f15120afa9a415c53482eea2905d14520af298415d530827ca9884f55310dc206213f5484278a9084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa4086e10010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x8e0a0240c605a3191320cb0c5314941c6d4c50507185314141cad4850507285214141c394e52902396510010
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
  | 3 => packedAt s2K3 (312+((h/2+packedAt s2K3 (304+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffff81fffffe07ffffffffe03fffe3ffe3f
  | 1 => 0x3f81ffffffffffff81f03e07ffffffffc88fff
  | 3 => 0x3ffe03ffe03f81fffe003ff83ffc1f01f0f3cc
  | 4 => 0xc00003ffffc001ffffffc0003fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffc0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x84882808c489082016514a284a212954133615
  | 1 => 0x11245191091260c580a4148694c652a8c888ea
  | 3 => 0xa6149aa243a42b6aaa0927b227691c0d70d34c
  | 4 => 0x3459634492074db34d3d812439b38831bd03b0
  | 5 => 0x386183871c3871dc71ce39c701c210c1eeec00
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88cc888888eeaaaa88cc888888eeaaaa88cc888888eeaaaa88cc888888eeaaaa88cc888888eeaaaa88cc888888eeaaaa88cc888888eeaaaa88cc888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36707
namespace PEqualNP.Outside.L_meta_36707
open PEqualNP.Outside.L_meta_36707.Model
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
end PEqualNP.Outside.L_meta_36707
namespace PEqualNP.Outside.L_meta_36707
open PEqualNP.Outside.L_meta_36707.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0xf80542400b0045480000001d00546903c380000000000580000c2c816af5028012361411900000141e0170748002000000000005d12742000a53068180002000000ac0004c00000000000000009804670006000000080060008108040051a00002ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x617e510c2faa2186fd0430dea0861df310c3bc6218774c430ee188617e500c37c80186f10030ef98061fa300c3ba60187e4c030efaa061de540c3baa8187715030efa9061de520c3baa4187714830efa1061de420c3ba84187710830efa8861de510c3baa2185754430ee28861df410c33e82187790430eea08619d410c3b8821877c8430ef10861dd210c3b842187794030af28061da500c3be80187790030cf20061dd400c3b880186710030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20bf28e417d51c837e83906f50720ef98e41dd31c83de43907b48720df20641bc40c83bc6190770c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3106fd0620dea0c41df31883ba63107b88620f610c417e508837c81106f10220ef18441dc30883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a4174514837e82906f50520ef98a41dd31483de42907b48520df20241bc40483bc6090770c120fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841bf410837a821077cc420ee98841ee21083d842105f94020df20041bc40083bc6010770c020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c42faa5885f14b10dfa0e21bd41c43be6388774c710df20621bc40c43bc6188770c310bfaa421bf548427ea9085f95210beaa4217c5484378a9084f15210bfa9c21df53842bea7085f94e10bea9c217c53843b8a7085714e10bfa94217e52842faa5085f14a10bea8c21bf418437a830877cc610ee98c21f721843e843085f94210df20421bc40843bc6108770c210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa0a21bd41443be6288774c510df20221bc40443bc6088770c110fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821bf410437a820877cc410ee98821f721043e842085f94010df20021bc40043bc6008770c010fb88021fa10043ea20087e44010
  | 1 => 0x721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21dfa0a43bd41487be6290f74c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e510877e8210ef50421ef98843dd31087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e81de53d02bca7a05f54f40eea9e815d53d02fca5a05f54b40bf28e817d51d037e83a06f50740ef98e81dd31d02faa9205f94e40bea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd429037885205f94640bea8c81bf419037c83206f50640de20c81df31903ba63205f94240dfa0481fb409037ea7206f94e40dea9c81bc539037ea5206f94a40dea9481bc529037e65206f8ca40de99481bc329037ea3206f94640dea8c813d5190378a3206fcc640cf98c81be319037a6320674c640de18c81bf219037c43206f48640de10c813e50902fea6a077d4d40afa9a817c53503b8a6a05714d40bfa92817c52502fea2a05f14540dfa0a81bd41503be62a0774c540fda0281be40502fca8205f94c40bea9881bf431037c86206f50c40de218817e52102faa4206fd0840df21081bd421037884205f94440bea8881bf411037c82206f50440de20881df31103ba62205f94040dfa0081fa401037a80207e50040dfa9881be531037aa6206f14c40dfa9081be521037aa4206f14840df99081be321037a64206f0c840dfa8881be511037aa2204f54440de28881bf311033e62206f8c440de988819d311037862206fc8440df10881bd211037842206f940409f28081ba50102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc2fca5985f54b30bf28e617d51cc37e83986f50730ef98e61dd31cc37c81986f10330bfaa4617e548c2faa9185f15230bea9c61df438c3bc87187750e30ee21c617e528c2faa51877cca30ef19461dd328c3b865185f94630bea8c61bf418c37a831877cc630ef18c61dd318c3b863185f94230df20461bc408c3be61187ecc230efaa461de548c3baa9187715230efa9461de528c3baa5187714a30efa1461de428c3ba85187710a30efa8c61de518c3baa3185754630ee28c61df418c33e83187790630eea0c619d418c3b8831877c8630ef10c61dd218c3b843185794230efa0461de408c33c81187750230ee204619c408c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4985f14930bfa8a617c514c37e82986f50530ef98a61dd314c37c80986f10130fd98261de304c2fea8185f95030beaa0617c540c2fca61877d0c30ef21861dd430c3b886185f94830bea9061df320c3bc6418774c830ee19
  | 2 => 0xcbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef90f41dea1e83bc43d06fca5a0df54b41dfa1683be42d077a85a0ef10b41bf286837d50d077ea7a0ef94f41dea9e83bc53d077ea5a0ef94b41dea9683bc52d077e65a0ef8cb41de99683bc32d077ea1a0ef943419f28683bd50d0778a1a0df552419eaa4837e53907bca720d794e41bea9c83dd53906baa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83be435077a86a0ef10d41bfa92837c525077e84a0ef90941dea1283bc42507ee82a0ef90541bfa82837c505077ea6a0ef94d41dea9a83bc535077ea4a0ef94941dea9283bc525077e64a0ef8c941de99283bc325077ea2a0edd4541dfa8283be505077aa0a0ef141419e282837e541067ca820df94c41ef298835e53106faa620f754c41aea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc7be8798f790f31eea1e63dc43cc6fca598df54b31ef99663de32cc7ba6598f70cb31dfa0e63bd41cc6fca198df54331efaa663de54cc7baa998f715331efa9663de52cc7baa598f714b31efa1663de42cc7ba8598f710b31efa0e639f41cc7bc8398f750731cea0e63dc41cc7bea198f794331af28663dd50cc7b8a198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31aea9c637e528c6faa518df94631dfa0c63bd418c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7be8698f790d31eea1a63dc434c6fea498df14931ef99263de324c7ba6498f70c931dfa0a63bd414c7ee6298f78c531bfa82637c504c7bea898f795131eeaa263dc544c7bea498f794931eea9263dc524c7be8498f790931eea1263dc424c7bea298f5d4531efa0a639f414c7bc8298f750531cea0a63dc414c7bea098f794131eea8263dc504c6b8a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31af298637e520c6faa418df94431dfa0863bd410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21dfa0e43bd41c87be6390f74c721bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510df94621dfa0c43bd41887be6310f74c621f790c43f
  | 3 => 0x28fc3577b6724bbbf254421c8a18c020191e21637ee78000000422df91c00061e0000001a79250c8522a61a000bd800708fcda22ab5200017e3255f4f158eb7927696d7aa04022e50d51bb52a000003673be165f28000000007a000058de19eb8b000dec0022b12aa69caa4905e000002ad000dd8ee000000d980010c1a00006b039382a2525320108cd11c967172464b7a0d2220000010d00000000000170c48e0049224000000000008d867000000001a6bae000168000002e6000f82b63fe3a8001a500000600c0300f0060240400001001c008020080080001602602c000000040000181a04601800803026018020020000100081b0000040100500600800001002004000050120000400701000000000002008098000000380300301400c0200003c02001800002000010010000000280100600001802000000000000040100180100000800800008010000000000200081501a000000010060100000600a000000000080080000300601c0800000601402002000008000110000180d00a008000010000000040200100400000003012038010010000000400600e00c0100000a0000001200a0300180300601001801002008050040000000300b0020000a0040080440000500800c040060040000200000000c01802008020130020040000500100003801808000004030000020000000100000c0000000c01c0180c000044088050000140c003000004008010000000000200208000803002014048000320000000301800002000000000028000000180080900c018000020240000500e0000040600100c018018000040000000000c0180381700000403007000000028000020540000902c02400000008000008000020000000b00001404802002000000000000080000c004000018030040000280501606800df94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528
  | 4 => 0x40ed5d1e5196e7c743dd000b0dc896b0000014da4d4122f0c80000003f4cb1b63343ac001a810c0005d800000000000003484f0c08000006c8000002207099c000000001ab000700dcc00000000bec3b00011e2c9ec000598f458bbb20002ccdf0b60000005a83c436a14fe34004e000ad8800f4290748000fe93900ae021048cbf9312ae401f20c3024f38c8a71720f4c7333b770000300000005c8f7299000f2800257000000000da46000146bd41c4a389e800000000002101f0b083ba940004f9a3a31000f69fb08524c4080018900061dae8001aa1d195bc600000000083304000000b01ca7e40000000000171b10000d0d808230e42600021c28ced5ef000000f300000000000000000000480f18006e0fc00d8e075a0995ab9e47ea107b8000000000005b62871871979000001ac8401b2fb1ba3d003a95846b2c00000120948490080002e9000000cbb08000594a8a5a1a6001a787025a4cd353eb0bc2c435b1165a00153afe45a0e00012e59e230570000e68b98d14d726e04c31ce6840010a8dc1800f80036b10464d2a9ea3708597b279000304b40000002a800304414d68000c613e9d13700018a000360000004d00000013c189310d46eaaf4ff000000ac9adb4a2bc9f5540004401590e80030a4884738306a83c000ad4bacb8cfac81a2089f39cf7b80008aa12786741548894b2eb06c19c66400016b8512c3313202515000000144570b6cac1d25040012a0006de2acd1800714cd5981cb64639ddd9606366d000263000e6d5e0000000000026b2c20200000031aee80000056600000260442000000002dcd88003c20da0008b00050600000000426000000006d40010f1a72a4b54000001941d57fa8a136334a280022e000000004d8000e1800428d78fd2d4522d800004d3ce4bc79b6e0000012fb4b28422032a81562b396815401429c002c057c001578002daae41e800000501279d3000324000004f8120eb800000000eaac6000d04dab4620e56400000000a2d19800000001c91d13da1ec001010005f400000000555f739d0c60d9950005cac2503ada48c051859846525c5438c80a21a90300051e150578006c6c90003e000091c2380047c6a59e13f2421a514a655e25e1d133a28285c9bbef26a865d98023f607d36b7770c110980006b0000000000640000005d604349cb800000b98bf22328ef5c4e11e778a300035055cca00000033c000001a1606fd00019b0009dcbd0035ceba80024b000a99e00000004e800000704000939ef406000bb000000a7c002f439a000000000000000000079a7d45300076e911db000000f5989800066001770001b619d4c00047800000000000000f4800000e25698300c200140339468984003526a26bc02b2f03047cef17459a3e80018f05c5280020263c5690faa14445748226663e6
  | 5 => 0xfc2269f9551a2400aecdd353790280611880003d82b9704104607d9b70a4f3c8d1b118e0007f24c78e001c41996e27900e23553abe00015f000000000002f852c001da0009fd7236866ce30fb8005be000000002366000680020ab11fa80062ae71432ef56efb5d20df0f210400000000db1291eb0a09bc9c82960a00095b336928ec7fb8771e1f0001c40000000000072c0fdbe053264000fe83144cb75d28c435600133800000730002eb2c4a48000003b0b284884567e8bdb91bd00000170800000001f3000050d14003e901c1bdaa2d75c4e993b1b9000084000175d84b0000002a602c0030700094c370003d0d84000000002e8772d11ba00000296366091658be00c3d54f1284a0ec1608f135a2284e8000000005e9f13ac0a8000372cc698001c70000016c800248e9d441830ccb1c00000000000a79dd116ad1b2a70000001d1a400005d4003210000000000003c571989e6358000ab00f7d47880000000000116000000001938007348dd343370000ac000040000002600000089cde0433e601d79000448001a71384e4424001061d80017b9ec4160014e0a577c8680001624a0002a85800200000000000f8c0005c4eae64233bd450000001f64d2d21910000001e1af8000004a400000000970f90001bc660d00a15daafc0007e33a001e5baa1c2ea5d78a260c3b4002f3238bc1ae0e46323c00000013235cea000000000001bf3c26c12183a000001eab3e54a525ecaa019e000000007400000000064c000272d6000a4c000713906b800000094ba0000000002fc000000000000000000000087ba85b0000000002a00000037a4e60000000002a8152f0940000012138e26cb490c09a7a4db5d894c7d00018e000000e845a0b700003004af95faed15196400013c3eb690006504b800618000000004a2c01191ca5bc4a885a7a3b6895062dc0847d01a0920000000011d71a000003982d200000000000000001c552e17d1d0002d8c28003640000005490300000164800000000518ac77e960001d96aa1a0002ac62c00009800630539dc80061c204ca8007c23e4002a448a638002b07be9edfc34c1de000b510e6fa9e0c5890756838792c5096065bfa3d782fc4c90937c
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xc40842b56110210c7d52308431c548c210b5586308431f540c210c715030842d5610c210f808620842f06148210f8c85208423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544423e60151108f180544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534425e6014d1097180534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910da580524423e65d0510c7d4f414431c53d0510cbd4b414432c52d0510ae983414423c6550510c7d4d414431c5350510cbd49414432c5250510ae181414425e65cc510c7d53314431c54cc510d3d4b314434c52cc510b6983314425c654c510c7d51314431c544c510d3d49314434c524c510e550531442d8604c5108f996404431f5390110c714e404432f5290110cb14a404423e6510110c7d4c404431c5310110cbd48404432c521011097996304431f548c110c7152304434f528c110d314a304425e650c110c7d50304431c540c110d3d48304434c520c110da14a20442786548110d914a104425e63d50109758f540426e62d50109b58b540423d65950108fd85540423d61550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c1097d85530425d6154c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d5354810d9185520423e64148108f590520425e63148109758c520426e62148109e980520423e64944108f592510425e63944109758e510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb549410425d65cc410c7953310431d54cc410d394b310434d52cc41097d95310431e544c410c7551310434e524c410d3549310436552c84109d594210423f65900108f596400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010c794c400431d5310010cb948400432d5210010ad584400425f658c01097596300431e548c010c7552300434e528c010d354a30042d5618c01097d94300425d650c010c7950300431d540c010d3948300434d520c010b55843004398400c0109e596100436952840109dd9510042e462440109ed9510043695244010
  | 1 => 0x8398400c2208f587544823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544823d6115120c7d53534831c54d4d2097587534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534825d6114d20cdd53514833454d4520d5d4f514835453d4520cdd93514833464d4520d5d8f514835463d45208f990514823d64145209798c514825d6314520cdd5051483345414520d5d4c51483545314520cd99051483356414520d598c51483556314520dc580514823e65d05208f197414831f53d0520c714f414833751d0520cd147414823e65505208f195414831f5350520c714d41483375150520cd145414825e65cc52097197314831f54cc520c7153314835751cc520d5147314825e654c52097195314831f544c520c71513148357514c520d5145314826e65c8520d9147214836451485208f996404831f5390120c714e40483375190120cd146404823e6510120c7d4c404831c5310120cdd444048334511012097996304831f548c120c71523048357518c120d5146304825e650c120c7d50304831c540c120d5d443048354510c120e61003048364518812097d8d540825c63550209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209d98453082756114c208f992520823d64948209798e520825d63948208f992510823d64944209798e510825d6394420cd94541083355150420ae1814108356514c420d554531082d8604c4209b59621082e960084209bd9520082e46148020ea10120083c830480209ed95200825e63d53109758f54c425e63153109758c54c423e64d4f108f59353c431e5494f10c755253c431e5454f10c755153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6414b108f59052c425e6314b109758c52c431e53d0710c754f41c431e5350710c754d41c431e54cc710c755331c431e544c710c755131c4395414c710c794e40c431d5390310c794c40c431d5310310c795230c431d548c310c795030c431d540c310e610030c433561d5210ce983548425e63952109758e548425f63552109718d54843356115210ce980548431f54d4e10c7153538435561d4e10d6983538423e6494e108f592538423f6454e108f191538431f5414e10c715053843556114e10d6980538423e6494a108f592528425e6394a109758e528423f6454a108f191528425f6354a109718d528431f53d0610c714f41842ba60d0610c7d4d418431c5350610ae181418431f54cc610c715331842da60cc610c7d51318431c544c610b618131842f16008610c7d4e408431c5390210ad586408431f5310210c714
  | 2 => 0x605063097994418c25d651063097996218c25d6588630a7992218c29d648863097994218c25d6508630a7990218c29d6408630b6980218c2d96008630a7586408c31d5190230a7584408c31d5110230e6980408c23d61d51308f992544c25d639513097d8d544c23e65151308f584544c23e64145308f590514c23e65d05308f197414c23e65505308f195414c25e65cc530c7d53314c31c54cc530c7d51314c31c544c530d5d45314c23e65901308f994404c31f548c130c7152304c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c30c7151430c25d6510c30c7550430c23f64548308f191520c29f644c830a7191320c29e640c830a7590320c34d520c8308f992510c23d6494430cd945410c3355150430ae181410c35551cc43097596310c29e648c430a7592310c29e640c430a7590310c29e64cc030a7593300c25f654c030a7d91300c29c644c0309ed95300c2da60d5030c7550540c2ce6215030b3588540c2d66115030b5584540c2da6015030b6983520c29f6454830a7191520c29e6414830a7590520c34d5214830b5984520c2d56114830b6980520c2da6090830b6582420c25f655083097195420c25e651083097594420c2da60d4430a7992510c29d6494430a7990510c29d6414430b3988510c2cd6214430b6980510c31d51d0430a7983410c25e659043097596410c29d6490430d5546410c3555150430b6d81410c2d86050430e5d85410c3965150430c7545410c3955150430c5545410c39b6050430a7181410c3986050430a6181410c25e651043097594410c29e641043097996210c25d6588430a7992210c29d6488430d5546210c3555148430b6d81210c2d8604843097994210c25d6508430a7990210c29d6408430b6980210c2d96008430c7d06500c31d4194030d6982500c39b4194030e6506500c25d65d0030a7586400c31d5190030a7982400c31e5090030e6942400c25f6550030a7584400c31d5110030a7980400c39a6010030c7940400c39a50100309798f54c825d63d53208f58654c823f61553209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f209758653c831e5454f20c755153c825f6154f208f99053c823d6414f208f99251c823d64947209798e51c825d63947208fd9741c823d65d0720c794f41c831d53d07208fd9541c823d6550720c794d41c831d5350720ae18141c825f65cc7209759731c831e54cc720c755331c825f654c7209759531c831e544c720c755131c82d8604c720c794e40c831d5390320c794c40c831d5310320c795230c831d548c320c795030c831d540c3209798f548825d63d52209798e548825d63952208f993538823d64d4e208f992538823d6494e208f992518823d64946209798e518825d6394620ba580218
  | 3 => 0xe40c7d4e53902ba6014e40a798f529029d63d4a40ae983529029e6394a40a758e529032f5294a40ae980529023f654ca408f195329023e650ca408f59432902ba60d4640a798e519029d6394640a798c519029d6314640ab98851902ad6214640ae980519031d51cc640a7983319023e658c6408f5963190397614c640c7545319029c604c6408f994319023d650c6408f996219023d6588640a798e219029d63886408f994219023d6508640a798c219029d6308640ae98021902b9600864097587535025d6114d409798c515025d63145408f997415031f53d0540c714f415031f5350540c714d4150337515054097997315025c65cc54097995315025c654c540c7d4e405031c5390140c754c431025f63548409718d521029f6350840a718d421029e6310840a758c421032d52108409798e511025d6394440cd547411023d6590440a798e411029d6390440a798c411029d6310440d59453110355514c440b6181311029e63d0040a758f401023f6550040a7d8d401029c63500409ed9540102ba60d4c40c754c53102ae6214c40ab58853102b66114c40ad58453102ba6014c40ae983521029f6354840a718d521029e6314840a758c521032d5214840ad98452102b56114840ae98052102ba608c840ae582321023f654c8408f195321023e650c8408f59432102ba60d4440a798e511029d6394440a798c511029d6314440ab98851102ad6214440ae980511031d51cc440a7983311023e658c4408f596311029d638c440cd5463110335514c440aed8131102b8604c440e5d853110396514c440c75453110395514c440c5545311039b604c440a71813110398604c440a6181311023e650c4408f594311029e630c4408f996211023d6588440a798e211029d6388440cd54621103355148440aed8121102b860484408f994211023d6508440a798c211029d6308440ae98021102b96008440c7cc6501031d3194040ce982501039b3194040e64c6501023d61953308fd8554cc23e64947308f59251cc23f65d07308f59741cc23f65507308f59541cc2b86050730c795331cc31d54cc730d554731cc31e544c730c755131cc26e62d52309b58b548c31e5450e30c7d50438c23e6494a308f592528c29f644ca30a7191328c34e524ca30a7990328c29d640ca308f992518c23d6494630a7992318c29d648c630d5545318c29e640c630a7590318c29e64cc230a7593308c2ce62d5230b358b548c2da60d5230c7d52548c2da6015230a7993528c29d64d4a30b6983528c29e6494a30a7592528c34f5294a30b6980528c25f6550a3097195428c25e6510a3097594428c2da60d4630a7992518c29d6494630a7990518c29d6414630b3988518c2cd6214630b6980518c31d51d0630a7983418c25e659063097596418c3976150630c7545418c29c
  | 4 => 0x7590524c74d5214931b5987424c6d561d093197d95424c65c655093197994424c65d6510931e5d47414c69e60d053197996414c69d6490531e5d85414c7975150531a7181414c65e6510531a7990414c69e64d4131a7593504c69f6454131a7191504c6cf6254131b3189504c71f4114131c7504504c65e63d50318f596540c63e60950318f181540c63e64150319798c540c63e64944318f592510c63d65d0431c794f410c63f6550431c794d410c71e54cc431c7553310c65f654c431c7951310c71d544c4319dd95310c756534c4318fd91500c63c645403197d8d54c865c63553219798c54c865d63153218fd9153c863c6454f218f99053c863d6414f21e550531c863f64543218f19150c865f63543219718d50c865e63d52219758f548863e60952218f181548865e63152219758c548863e64d4e218f593538871e5494e21c7552538865e6094e21c7951538871d5454e2197181538863e6414e218f590538871e53d0621c754f418871e5350621c754d418871e54cc621c7553318871e544c621c7551318863f64542218f191508865f63542219718d508865f63551219718d544867b60551219e181544865e63151219758c544863f6454d218f191534867b6054d219e181534863e6414d218f590534863e64d41218f593504865e63d41219758f504865e63d50219758f540867a60d50219e583540863d65950218f982540863c60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c2197982530871e5454c21c7551530865c6054c218f990530863d6414c219798c530867a6014c219e580530863e64944218f592510865e63944219758e510863d65d0421c794f410871d53d04218fd95410871e5350421c754d410865d65cc421c7953310871d54cc42197d95310871e544c421c75513108795414c4219bd9521087a54148421f14c521086776548421ce95250087395494021d694e50087595394021ced9250087386494021d6d8e50087586394021ced0650087394194021d6cc6500875931940218fd91500863c645402197d8d500865c6354021ce95150087395454021d694d50087595354021ced9150087386454021d6d8d50087586354021ced0550087394154021d6cc550087593154021dac85500876921540219758653d025f6154f409798e51d025d6394740c794f41d031d53d0740cd54741d031e5350740c754d41d025f65cc7409759731d025f654c7409759531d02d8604c740c794d439025e6394a409758e529029f6350a40a718d429032e5250a40a798c429029d6310a409798e519025d6394640a798e419029d6390640cd545419029e6310640a758c419029e63d0240a758f40902ae62d4e40ab58b53902ba60d4
  | 5 => 0x51cca3f64543328f19150cca7a60d52329e583548cb1f5410e328f992518ca3d64946328fd91508ca3c64542328f587544ca3e60d51328f992544ca5f63551328f994544cb1d63151328f584544ca3e601513297996434cb1c5490d3297195434cb1c5450d32c7152324ca3e64145328f590514ca3e64d41328f593504ca3d65950328f586540ca3e6095032c718d540ca3f61550328f181540ca3e64150329798c540ca5d65d0c32c7553430ca5d6510c32c7550430cb1d54cc83297d95320ca9c644c832c7551320ca6f654c8328f992510ca3d64944328fd91500ca3c6454032c754c43d065f6354b419718d52d069f6350b41a718d42d069e6310b41a758c42d072d5210b4197d8d50d065c6354341ad58753d071d5314f41ab98853d06ad6214f41ad58453d06b561d4b41a7d8d52d069c6354b41a798c52d069d6314b41cb54852d06b56114b418fd9532d063c654cb418f99432d063d650cb41a798f50d069d63d4341ab98b50d06ad62d4341a7d8d50d069c635434197982539065c6054e41c794f419071d53d064197d8d509065c6354241c714d435065e63149419758c525069f6350941a718d425072c5250941a798c425069d6310941a798e415069d63905419798f505065d63d4141ad58653506af6254d41ab18953506b76154d41aed8153506b86054d41c754c53506b56194941a7d8d525069c6354941add8552506bb6054941ae181525069e6314941a758c525072d5214941ad98732506b561cc9418fd95325063c654c9418f994325063d650c941a798f505069d63d4141a7d8d505069c6354141abd8950506ac625414197982531065c6054c41c794f411071d53d04418fd95411071e5350441c754d41106776550441cd951411065f63540419718d501066e62153319b58854cc71c5450f31c755043cc63f6454b318f19152cc69f644cb31a719132cc69e640cb31a759032cc74d520cb318fd9150cc63c6454331b558754cc71d5415331b398854cc6cd6215331b558454cc6d561d4b31a7d9152cc69c6454b31a799052cc69d6414b31d354852cc6d56114b3197d9542cc65c6550b319799442cc65d6510b31a798341cc7976150731a718141cc69e64d4331a759350cc6ce62d4331b358b50cc71f4194331c750650cc69f6454331a719150cc63e60952318f181548c71e54cc631c7553318c63f64542318f191508c66f62551319b189544c67b60551319e181544c65e65d0d3197195434c71c5450d31c7550434c63e64149318f590524c69f644c931a7191324c74c524c931a7990324c69d640c931a7992314c69d648c5318f993504c63d64d4131b5586544c6cf6255131b3189544c6d76155131b6d81544c6d86055131c7550544c6d56194931a7d91524c69c6454931b5d85524c6db6054931b6181524c69e6414931a
  | 6 => 0xab9f89eb9041710f1169895a5d287920a3c9c28cda221e6a2b1a811a07b1e718c997a61a2ca9f8c8a898cb0b921a8b30da9aa00021b1fca23a1c99f96d18990a00b0cb8f80cc21a0dd90c20c846a380ec05189c8da1b822720b07821e2268c32450a596501ba438a42558209989e020b80200019c80005d0210441d326117b285959a341a6a489b1a068960000830611bd9fa11609007f86609212f9d2a0c14a2511d38030020680000a80e0000080200604206000008000008100090020000081b0000c4008000020000700a002060010000060740980b01a0141080101200006011042004000050000000601601a0000401001803800000020000078100000040000100c0000100a0000180380400c020098000000480000c01e0cc0c0050000000400200a04c0681500201805801002008010000000100600002c0000001900600c0000b0180000080b0100040400a0000500000500e0001281501605802805000000208010420100180208a0000480600a01c000160000000080700c00c0880900000000003048084000110040100280000004409800000000000070060000100e01c000000190040000480400801c1000300007c0380d006030040010000280300600403c008030da0040380600003400009000010038010000040d0020000180000000401c020120000040302c00e0200980301400c0000700200c0000c0000300181b0060280580300002c0f00000000408000002034008000000002401502600801000004010018000000000000c0040240100201601419000028000100000140181800900200000804004038030010000080281500408c0300905a06c02806000010000000020281f8000300040700000c02007003000000028050060000480801a028078090240140900100c00004000042014018040000000080101c000038080000580200200005c0300501a008000050040240980100e01000003016010160020020080580c014038200070220000200d000004000230040000100002601400004000014078000040100400406e00c08800006008000010060b8000070420002d8080000629d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9f6150c43a71814310f1d4354843c750d5110f1d43940439798e51d0a5d639474297d8d50d0a5c63543429798e5190a5d639464297d8d5090a5c6354242975875350a5e60d4d42975845350a5e6014d428f9974350b1c53d0d42c714d4350b1c53909429798c5150a5d63145429798f5050a5d63d4142975865310a5e6094c4297d855310a5c6054c428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f65508429798e5110a5d639444297d8d5010a5c63540429d98454cca756115332c715143cca3e64947328f592
  | 7 => 0x426f10d08697e98e04d89520486b000275a588000001a014821902686e864232171a0611c1d40d70750172481728ad0c382381891d19103180716696704b1b6919016a360e68de8f30158cf02e862059a260408d29dca0d24d9a408126522e8a002e0e71ce1520b08a89f52000588ef17a20d9008bb9178d31428000ed800231000073000111a8227f8fb2009dd272a1106819011529d97909e1950e29281ce96c85521da5f89d9271b51bf8011228a9a9e0c19f607f11009f16405c8f01fd00000c10987a1e89ec1350000708f9a390669c98a48891920389e48001e6000000000000262a649f319e0000001b400023e8451682120e60be0448338e02918ff1d680f21800011b9f70e3a129b907702d000061a460eb23380013791b027a409469200001ed0000e8a0587787ea108e993f1340ff8ed08c1b98f18ba1821019af0382719ad181236a659d70c50728308458220c5882a8d0a61a7a948fd1060c70df88aa0a0f712104a99191e1580ab0ce9771a10ca82fa3712a8d09761b700423785805909885aa078af9460baa8f9a227d10010d98016884c98699b9b8875a2280026300a23023f19297819c05c28395f0000001bd0000970000001578ad8000000cf8001551818000000e495c0000001e99e09e80000002541ba8000c026b0539311d81f400022016908e0f58b88800e22988a7924a020b283b04c05080025d9b586c19412313e0c2a4f800079a9210a83e80001185700011a80022c08ba689ed80020418d9c0218847a0fa501c70d400f8001b78d3a098391491220f691800026aa8b08702700000000001a13e8000a30001ee09180000000005b00029f00009b00000016b9148e10ac09980025f03aa3b2739ab29d02da279d50000788248e31531aea1506714990311d800000007a448d90eb88d8c404f8d98362091b297f0e79da89f83300002b28e0e82520bc2851858b4148a288f0a01967a5c28b8a908f8f38d6a4e80012f0fa11f8028d1a249df92e0a0a761a70000a185109e8a506988980014da2329a00026402aa468001f00eca5aa028ab97c8c78ee26381ca0a90e1a4837943a4b0289f11c500017527a0aa04994191118b14b0439559628001bb9540608000b598500022f8481441a90561de0219501842900b00e08a20351cb9390521d180000012d80008c80980025e8000f903ba470c9073915a829e3a1c036a7886d9e523f8851de9562550432911d211285fa35a9aa7b91f1eb269841080a579e400000004900013b0930198000540321bf017a4b8bf03d8fe1b0140277a4291415d1d598a1a9a0e131988a8a99614c9768e50250dc1db11c92d208a421f597d98395680023e214853298012960a2119e8000700260fc1519830000001f68ae82b8001301ea0b701489780010694a83017983d211a7021d10926a1e91
  | 8 => 0x8b1a5b1c308d24e25703f8948488691fe00000027c1b3a49119a30a40127a971c794e1d0a3b9f799682a20386e1ae00000009800008415f8470d8000165a2919d17420810c83480e97d00013200006592b1cc8000001c5800126835a928001c228a00e0f515a8001c11398630000000000e58db8000001611308000000190000001f28000370c688b1b610200000027a98f07616e0089da12b98c18717b9169ac2348299bc1c88000652690af23d02c9e29059ac9338cc92ea6c85a024125004a9392c29c0f216f24c943005a529ad91093f80000000013580020316624104d1b215ca931730c09cd0000001a8a7808e8000000fa8310000000000002950c61450db0d000c80019712c9048b228f11892a14b8558aa9c60769848000000001ef80000000000012580000018900000006aa9693881200000025316c000238800136a6b96d80028487e0001039c6a1f0939570878839af9788688f627118824c1e224195a14780a84e9fb26da298001331cb12886d01d8000fe9e309d00000000000000019927498780015b25917481a8c22708001c18001f49e58c4a8608f10e97c0001779fb98ea2e29080004219f09080000000022800000025e0a28139958b4a4aa1f8228d125680014c1130f8a539d9800034096a1389a80001c0001e78090080419a08f780000000010817a88180015e1a528ca2a10fa7991e9a604b9170001e180d08a07d0d5852a0f1b323980393c921a99944a6080000000000019307480012410b96aa6695121685492612901d22400027e26d0bc9ca9d61708b38b82771bea2500025986f80000019b0d60b107a9601dc1138002600de25c81104a2741fe962082000150a4323a19a1758000002350100ee884a7306a05e800288a8113aa8908585e0001fc140871a2d88893da791b107d80026c0001589370001dd8000018000000001298030001a28001cc03982802f1fda581458dc8f414d01b00022ba672819f81050001a30000001909faa172441619088000000232498f2a1780027c80003e00000029ea9c96e9f90ea85681628685f0001c40e900006387c0a3902a199471939f381401806c93b813232954a840001f080000000024a00001f0c100013619da560329538000291be0000000000000d89d79591a180000000000018fa9ba5b8ef80023c0dd1c380028e9d10df04e0000b692385d8678790ae1aa90f24789909b8ea17f84f09a2941c90a12960008c821419a9bb1948bf80014120e83f00b96b0000000710000d20002318000b99011b4a4d0f4a130b506f16388801e23da5a1ba21000d8000061f21cd9ca0429d48a7164864a620cd17022595d97390728083c0002801d90bd20526e1c49df0ce2548b78ca01ea209ec85ba1600002010b0fd98280000016f8000000000001c080001080006009122a80007
  | 9 => 0x21e94fa9598a80016322f0e193a26f8ac8e40d513d0001dba3a9ee9420460bb250a8815ea6e8629f18c9a7ea6782c07ca8d8000861e104027b2979862830002158002459d8a0113c1cf18ba9b2a0005006a6814e8720152721f98bda519980578002072218259329a597218080000000000015ba769ff1b08941a39d01bc938000107a1b9cf8001ef0001c80000000000d780026614f0a680015281f8001120001ea8be9ff80000016a0000000fb80028c28709c17e27f24f03ca9919983a22d0d486b87b8fca7d8b6134a7518d0500a8233092
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x3ebaaa3292bc6c68400000a09e00007238000074c80000beb496b24810440088182edc000090a202b0c2241cae2cc40000da007c000800cc8a62506042004e582886009c06b854d6ca9a300e261a14000000005e766636003a8c944c4a00b600008400d000ac00d40000de001ed8700c6aa83c785c4600827e34d2806400a620c0528e16a4002a6e56c604007ace985a0a2212000220020005000f1302030119010b010001000a00010705030400000000000a010305000403a2ee2a1aa221d187050e5010e8ab88a8a1e65469c35410e32838ecaa2641960d6354842d0706a9ac429e838358d5214b41c18c629284a0d0c7254c535068c382a629a83255c66314941a18e6a90a4a0d2870548525061c382ca19283435c85450f31c1ac8a906598e0d5458854cc706b22a429663431c95410d31a30e0aa08698e0c64149324c686392a82a263461c1541513192ae3320a498d0c74548524c6a4382a429263161c16510931a30e0a08a098f11414c55008790a0a42a8043d04c52154021a2ae329a83a060c639494290287396a729c81439cf5294a40c1ac6a908420651511813110306a9ac4298818554d6114c40934e1b1aa42060d635485210312a92c2290810d5c4654c840930e0b1ca220631511813110388a8ec09888185544604c440e22a2302622069251181311030ca88c098881a4544604c440c22a230262204987058e211030ab1aa310881455c6544c730a1ce5aa0871860c64949328c287396a92a461439d35294a30a1ae42a2861851571151430c306b22a4190618c5446050430c1aa8b10a81861554584540c24d386c8a9061835915214830c8aa4b08a41845571195420c24c382c928861945446050430e22a3b02821861551181410c388a88c0a0861a49446050430c32a2302821869151181410c308a88c0a0861261c16488430c2ac8a8c421861561544400c28ab8ca6a0e418694c6050720a2ae32a2639061a5418131c83882888018241a81844048020d80c2182401061853181418430c2a0c098c2185d4d6110210c2ea8b0861084e276c85208430c298c0a0a218a1486050510a28eaa0a62886146550531443822928298a21641c1414c510c30a83026288648521813144348a08c098a218554d6110010c4aa4b088008615545843004322a92c218021465d4400c010c32ca20060087095210030042c8b888018021a4584400c010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x13a00000c0649402000040010a108058d5188440a10805915188430a118194c6050720a1181950604c720d00521c1414c510e0052504604c510c11655c4400c010d01525c4400c010c1175584400c010e0152584400c010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
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
  | 6 => packedAt s4K6 (880+((h/16+packedAt s4K6 (768+(h % 16)*7) 7) % 99)*7) 7
  | 5 => packedAt s4K5 (31188+((h/339+packedAt s4K5 (27459+(h % 339)*11) 11) % 1477)*11) 11
  | 4 => packedAt s4K4 (56038+((h/448+packedAt s4K4 (51110+(h % 448)*11) 11) % 1615)*12) 12
  | 3 => packedAt s4K3 (5784+((h/37+packedAt s4K3 (5488+(h % 37)*8) 8) % 148)*8) 8
  | 2 => packedAt s4K2 (615+((h/3+packedAt s4K2 (600+(h % 3)*5) 5) % 17)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffff81ffff83f07ffff83ffc1ffc0fcf9f3f3
  | 1 => 0xf07fffe0fffffff81f07fc3ffe1fffff463c7f
  | 2 => 0xff81ffff03ffc3ffe007ffc3ffe1ff0387cf9c
  | 3 => 0x1fffffc0003fffff80003fffe0003f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x210c08c42890400165098044c022425818d1b1
  | 1 => 0x44109102412221280a422429121494a1422446
  | 2 => 0xa22522481a440652a084ca8265412a0a854a98
  | 3 => 0xcb59c4929076ab9cd3d06223b9980c33e80f60
  | 5 => 0xc61871ce38733e71ce77330311030c3f7b000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeae8eae8e8c8e8c8eae8eae8e8c8e8c8eae8eae8e8c8e8c8eae8eae8e8c8e8c8eae8eae8e8c8e8c8eae8eae8e8c8e8c8eae8eae8e8c8e8c8eae8eae8e8c8e8c8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36707
namespace PEqualNP.Outside.L_meta_36707
open PEqualNP.Outside.L_meta_36707.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe81bf41d037a83a05f55240bf29c817d539037c87206f10e40bf294817d529037e85206f50a40bf28c817d519037c83206f10640bf28481bf40903f681205fd4d40efa9a815f53502f8a6a07714d40ae29a81bf435037a86a05fd4940be29281be425037884a05fd4540be28a81bf415037a82a07ed0140df202817e54102fca6207794c40af298817d53103baa6205754c40df21881bc43102fca4205f54840dfa1081bd42102fca2205f54440df20881bc41102fca0206fd0040fd20081bd40103f280205fd5330bf2a6617d54cc2f8a9987790f30eea1e617e52cc2faa598778cb30ee196617e51cc2faa39877cc730ee98e617f548c2fca9185f55230be2a4617d538c3be87187710e30bf294617d528c3be6518774ca30bf28c617d518c3bc6318770c630bf28461df308c3f661185fd5130dfaa2613f544c2fca8985f55130be2a261bc544c278a8987790d30eea1a617f524c2f8a498778c930ee192617f514c2f8a29877cc530ee98a61fb304c3bc60985fd5030bf2a061be540c27ca8185f55030deaa0613d540c2f8a8185f94c30efa1861dc430c2fca4185f54830ef99061dd320c2fca2185f54430ef18861dc310c2fca01877cc030fd18061dd300c3f260185fd5320bf2a641be54c827ca9905f55320deaa6413d54c82f8a9905fd4f20bf29e41de53c82bca7905f54f20eea9e415d53c82f8a7905f94720bea8e41ef21c83da43905fd5220bf2a441be548827ca9105f55220deaa4413d54882f8a9105fd4e20bf29c41de53882bca7105f54e20eea9c415d53882f8a7105f54a20bf28c417d51883dc43107b08620bf28441ef20883f641105fd5120bf2a2417d54482f8a8905fd4d20bf29a417d53482f8a6905fd4520be28a41ef21483da42907ec8120f7102417f54082fca8105f55020be2a0417f53082fca6105f54c20be298417e52082fca2105f54420f710841ec21082fca0107bc8020fd10041ed20083f240107a48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd90621f820c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e50043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xf5350af8a6a17714d42ae29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997790f32eea1e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cbbe87197710e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997790d32eea1a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32efa1865dc430cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41ef29e835e53d06faa7a0f754f41aea9e83be43d077887a0df94b41bea9683bf42d077a85a0df94341bea86837d54906fca720f794e41af29c837d53907baa720d754e41dfa1c83bd43906fca520df54a41df21483bc42906fca320efd0641fba0c837e50906faa120dfd4d41be29a83be435077886a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf298837d531077e8620ef50c41bf290837d521077c8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998f7d0f31ee21e637e52cc6faa598f7ccb31ee996637e50cc6faa198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31ef21c63dd438c6fca518df54a31ef19463dc328c6fca318f7cc631fb98c637e508c6faa118dfd5131bf2a2637d544c6f8a898f7d0d31ee21a637f524c6f8a498f7cc931ee99263f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c7bc8618f750c31bf290637d520c7bc6418f70c831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52886fca310fbc8621fb90c437e50886faa110dfd5121dfaa2433f54486fca890df55121be2a243bc5448678a890dfd4d21efa9a435f53486fca690df54d21be29a43dc53486b8a690fdc8521f710a437f50487f6a090ded4121be28243f850486f0a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821bf28843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81bf43d037a87a05f94b40bea9681be42d037885a05f94740bea8
  | 2 => 0xe0b07a44902c3ca850aa9ec4d65c4e224d0c85588599c0063180b287000340000b7000540000001bc99cc420d056000ed800198648000002f6264000003088d1259a848c674d596e3c253000000000001101cc0000000009a46678c0028d00000000000000000000000007140000000000000000000a188200047c000000000000000017820a380de80036251c00000000000051a0000a54002650000000007730e194d626207852ce3a0b36400000000000000000740e24693d000000000be0001ca000f5000158000d100034e001060000000005d1b61360380000049450c00000000000c60003a053c00000000000da00000013c0023d22600088000246320e189633c000000000000002700017a000620000001b4458bc43a0007e0002da0c00009d2be82000000000000001bb000000002040007c8e98e72789ec002980000000005e0003d0001643820002ca0f0006500000017e0000013606600000000000000410000000000000007c9a8000002d000000000000000d202f0000004c27c0006146025d22484095986276770be85b3cc000f99c644e508241224e4000d489e00000000000000000000000005bc000000000008c000000000000002b01400001432a1c1288002b2000b98000000000000000000000000000000cc0000ba1ec00000000000000b5000001239e7000000000001d60002a000144000000004ee9f88483a5020000040100000401c0080000a0080100200e00c00800000008000040020040100100e00008000002028008000080000000100a00401000000004008010000000080500400c000000000000380400a000000000040180200000c02c0280c01400c01801008004008010000000080100200000003002004018000000000600000000c010000040540200700600c0100b000010018010020080080100400000800008000000070000080080100200c00000000018020020020000300001c0000080200600000800006004008010000100100100202c000000020140000100a01c000010000140000000000000004000000040060000040080100a0040180200e0000080401a00000801004000010000000000000200400c0381400200c00801006010000020000000080900e00000800000002fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855
  | 3 => 0x3d000258000b10ed00050030000000298b191900080418a6e000958001cd1400a547983000000000004760000000006c55000000000000000aa3208700000000096c00236202000000d60000000000031c434000b20000007c80000000000000000000001960000000d0e3000000000000000009494a000020fba4500063c9200000055c0024f0000000010f000000001c845e2a0720000000000004c0c40012e000000a242123c0008e0001aa00030c000000161b80002d0046440000020e000002400000000000021066c000001b41bc0621e000000000003e200000000160768888002c0868258002b62180009100e0013b000458684b2800000000001ca2cc0000012100000002800070a10000002ee000000000000014802124e010940172640711f920430000000000d0978fe0001267b4a088d51659c5d8000229e1270004e811c000001723147780000000014000000a2800000000000000000000011480003e0011221331607863a66000498000000002f8318000d600117000000000000000006f000000414634000004be000002372885e8c52610f00dc0000000000000000000a0c0000000068c00250266001000001e45a89f2971be45c8da6f0002ac4222b1e0000a400d2284dc001ff2d6000000000b8001248ad00060800000000000000000000000000004e000110004d295c6ca3100000000000000000001c0040000000b642a000b6000000000000a9000888001970000009a84d3a40749706c3ac354980e20000009c80000000009000000000000000945680021748200000000464a313680000014408000000000000f80004e00002e000000000000008e4001c90009c4002251a67e81c8000000005a0c23d6000cf8460003cc001b80000000007e0000000010a000214a89341fe64d3418100025c2b8003a23b0001a50003a1088000003380009c076000002791828b521025000001108001b6824800000a6418008dc4543c4f225252c4584603f2a6a4c96800000000ec000000001382880ec00045000498284efa5934c6b8000003fc7e43e00000000000000000000001720004708f80035a000002230000000010c0006cc4025304c7787f1030fa0000000000c00000000000000000000000009d05f33483807a851a4000228000000f40008e0001c9218e900000000000000000002800009b000254000001320003f6764688000000009880028c6bcf709f504474f406a0cc3346a1f651c0000000006a1fc00000000241038004fa3d4588443fa750048003ae7390d8ee3c4548598000ea774000fb000000000cb432920570320009cc001020ce000150cf000000e10000003e90f8000000000015c3c084800000000000dc94e000000001cf0007d400000000000001f800021c408000803dd490002fe000651b
  | 4 => 0x240c2000ba0e628a0012c0000b4000000001ba00000000000a454a000000968c00d8000000001760000000000000000000189110954000a40468189f8940005a40013d44c8e86b9490005e400000000000479610000000c8000005c00000036a000578950009d42180000098051800000000fa07914a04c000000000008a80042c00000205450438000c9030384000410d20000011e0000000001b00020c000004c6054db8b83de4bc2485529a5f8950523962247b0564061cc539b04fe6e8001d50000007e95d2bc001180003320001a0ea37e808baa993e00000012546a00122
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1300c27b654c0309798f54c825d63d53209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f20c795153c831d5454f208f99053c823d6414f20ba18121c825e63d52209758f548825e63152209758c548823e64d4e208f593538831e5494e20c7552538831e5454e20c7551538823e6414e208f59053882e9600862097d8d544825c63551209dd85544827461551209798c544825d63151208fd91534823c6454d209dd8553482746154d208f990534823d6414d208f990514823d64145209798c514825d63145209b99721482e8604852097d8d540825c63550209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209d98453082756114c208f992520823d64948209798e520825d63948208fd91510823c645442097d8d510825c63544209b59621082e960084208f992500823d64940209798e500825d6394020ba58a200826f65480209ed9520082eb6548020dad9520082e86148020da545200825e63d53109758f54c425e63953109758e54c423e64d4f108f59353c423e6494f108f59253c423f6454b108f19152c425f6354b109718d52c423e6414b108f59052c425e6314b109758c52c436b520831097d8d548425c63552109798c548425d63152108fd91538423c6454e108f990538423d6414e108f993528423d64d4a109798f528425d63d4a108f992528423d6494a109798e528425d6394a10da149208423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109ed81524426e6514910cbd50524432c5414910d3d4c524434c5314910da580524427a6588110da14a20442786548110da149204436852c41109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436860548108f990520423d64148109798c520425d63148109b988520427a60148109e597200436952c80109e594200436952080109e596100436952840109dd95100427b6544010ba18910043695244010
  | 1 => 0xc63d641493197997324c69c644c931a7992314c63e64141318f590504c65e63d50319b988540c66d62150319e980540c67960150318f992530c63d6494c3197596430c65f6550c31c7151430c63f64548318f191520c65d658c831a7590320c63e64944318f592510c69d64cc43197d95310c677654c4318fd91500c63c645403197d8d54c865c63553219798c54c865d63153218fd9153c863c6454f218f99053c863d6414f218f99250c863d64943219798e50c865d63943219798f548865d63d52219798e548865d63952218f993538863d64d4e218f992538863d6494e218fd91508863c645422197d8d508865c63542218f992544865e63951219758e544867a60951219e582544865f63551219718d544867b60551219e181544863e6515121c7d53534871c54d4d218f992534863d6494d219798e534867a6094d219e582534863f6454d218f191534867b6054d219e181534865e6514d21c7d50534871c5414d21ced53504873854d4121d6d4f504875853d4121ced5050487385414121d6d4c50487585314121da884504865e63d50219758f540867a60d50219e583540863d65950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c218f990530863d6414c219798c530867a6014c219e580530866f6548421ba18121086776548421ce95250087395494021d694e50087595394021ce95150087395454021d694d50087595354021dac855008769215402197d8d52d025c6354b40a758c42d025e63947409758e51d029d63d07409798e529025d6394a40a718d429025f63546409718d519029e63906408f997435031c53d0d40c714d435031c53909408f994425029d6310940c714c425023e65d0540a758f415031c53d0540c714d415031c53901408f596431031d5390c40c754c431031d53d08408fd95421029c6350840c754d421023d6590440a798e411031d5390440c754c411031d53d00408fd95401029c6350040c754d401027b65500409b98854cc26d6215330c715143cc23f6454b308f19152cc29d640cb308f99251cc23d6494730a759331cc26e62d52309b58b548c31f5410e308f992528c23d6494a30a7191328c23f64546308f191518c29e648c6308f992544c25f63551308f994544c31d631513097996434c31c5490d3097195434c31c5450d30c7152324c25e650c930a7590324c31c540c93097997314c29d64cc530c7153314c31c544c530c7152304c23d6595030c718d540c23e64150309798c540c25d65d0c30c7553430c25d6510c30c7550430c31d54cc83097d95320c29c644c830c7551320c25d658c430a7992310c31d548c430c7550310c31d54cc03097d95300c29c644c030c755
  | 2 => 0x24000000170000cd80028a00020000000648208001080a4000ae35251000000000000fa000038000ae0000000000000000000000000000454898ff000000001730000002a936364140408002f8000002002ca2707b000000000b60c4022258000ba00000000000000808000eb130000a580024c000000002248040000000000036176000000000003c6000000000000000000009629c000000000000000029400000000000598a7000000474000000002d832800000000000001d00000021f000000000000000020000000000200000800002004000040160080000000400400007002004010000000040000200000001000000000000020000000180100200000000000004020000060000000000000400002006004000000000000000000000000000004004010000040000180100001003800002000008010000040000300600001001000000000010020000180100200000000000000000000040000000100000001000000000008010020000100100a0000000100000000000004000030000000000080000200401001002000020000000040200100000001801004000000010000000180000000c000000080080100000e00400004000000000030000029d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9f6150c43a71814310f1d4354843c750e5110f1d43540439798e51d0a5d639474297d8d50d0a5c635434297d8d5190a5c63546429798e5090a5d63942428f9974350b1c53d0d42c714d4350b1c53909428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f65508429e98054cca796015332c715143cca3e64947328f59251cca3f64543328f19150cca7a60d52329e583548cb1f5410e328fd91518ca3c64546328f992508ca3d64942328f992544ca5f63551328f994544cb1d631513297996434cb1c5490d3297195434cb1c5450d32c7152324ca3d6595032c718d540ca3e64150329798c540ca5d65d0c32c7553430ca5d6510c32c7550430cb1d54cc83297d95320ca9c644c832c7551320ca6f654c832c754e43d071d5310f41c754f42d069c6350b41c754d42d071e53d0e41c794d439071e5390a41a758c429071e5310a41a758f419071e53d06418f994435065e63149419758c525063e65d0941a718d425069e63905419798c505065d63141418fd95431065f63548419718d521063d6590841a758c421069d63d04418fd954110677655044197d8d501065c6354041c718d54cc71d54d0f31c755043cc71d54ccb31a719132cc71d544cb31c758e548c71e5490e31c7951438c71e548ca31a7590328c71e540ca31a7593318c71e54cc6319758e544c66f62551319b189544c67b60551319e181544c65e65d0d3197994434c71d5410d318f990524
  | 3 => 0x12000018000000000010f0000009d00000000000000000000000000000000000000064c00000000094000000000000001a0008307e800000000cb0000000000000b14c00000000000000000440b400000000000000000004440000009233c61c000000003040000001e000000000000000011038e000000000000000000000000000000000384000002f6000000b3094040000001ac628001ec378348000003fe00000000000000000000000003f0000000008a0c600000000000000000000000140000000036c1ac5e00010c0000000000022c0000025468c70000198000368000000000000000000000000074000001af00073c0000000000000000414000000000003680000000036092000000688d706300000000000000000000800008647a8000004fc000000006f40000000000000000000000e080005e00000000000000f0800212000000cb2c80002a0ca0000009f00028200029000000010000053aa000000001da24483800000000000000000001616e00000105900000000268000000007f0e70000000000000048c15800000000000000000000012c00000000000000000000004220000000c00025c000001de000ed80000000000028000350aa80000000000000000000000ee118000000000000000000019a000001172b4560001370000000005826483c0011b2ac000840000000a8399473b0000e21a100000000000000000000000001fc000ce000500000132420481900017c7cc0001f2da00000000000018000000004387c0001484e400000000000fc80024e000000c90005640000000000000000000000001690de1c8439e60006640000000032092a03000000000000000007d94238608ce000029a4a4000000000000007b000000f211c000000790f0000144000000000000015e000000000e2000000000000000010a0000000000003e000000730000000005080036a14cd282100000000000000764000000007b40000009200097000000000000000e200000000000001048000000003e80038a0d000186000834001b913200000000000000fb220000000000000000005f96a0000000000000033cb58002d04c4000000000007c8b406c288001751b66ccd40e9358000001b436e7e8001350440005c800000000240000000000016200000000000000000cb9d010a878e983b29e2c83e0b0000720000ec000000000000000000000000067c03800000000000000000009e826000278f7a0e000000001e805a000e7000000000000330007780017200000000000000000000000002ac00000316000001800002b40000000024c00000000308000000c4250000000000002e80001c56caa0002e005cb38160bc1c0000003dc000000000000000019415847d080d93be5e000150000000000000000000000042a280f10000
  | 4 => 0x1ba000000002c0000000000000001712d0000009c00000000103000000000000002fa15c1885c222080000001a20000000000000000000000000000003e20000000040a0003700000000000000000020069aa0003a8000000000002f800370000000000000010b21d00079c001cb1e6130c280008c00000000000000000a9000000ed000000894bc9050e827400000000000000562066700017a0000009a0001064780a10431048800000266000fc08800000000000000000228000000000000021a0000000044c00000000000000001ad0007c8000000000000015f000000001a6000000000000004080010a00055c00000218640698001620001203c2e8000000000003d0000001122950d00000035c00000000890001c93fc0000008d072000d8000000000238000000d4f017f40842cfd9460000004a99503a000000003ba394f80b734e7dc000000006740a80000000400106000000c793c000000000000002d4cd000000000d2000000000000de0000004d000000000000690f06c40000039458cdd00000000000000436000eb8c0000000000000000000000007a0000000030487000000000000000e309c4586f8000ec00000000000634000002402382113000000000000000000000000f200000000000000000002ee0000012b0000010ba23232000000aa3fa00000000000574000d518a530000000003c400000000000000000000000000000000000000000000c88002e27500c8003841e80018e3ac000c480000000000000104884f5800000370000bd000000001523407d400000000000000000007f0578000000000000013e6ac0018c2920000c0660000000000039a000000003d400000000000000000270000000006800000000000000000001842900000006a0860010980000000000000000000f48002c2000000003ca000000001360006399800050c000000000000000000000000000000000000000000008d000424000000002fc00000000000000000000001d41f8fa0000005d8000000000004f4104bc000003a4000001cc0c019000000000390000a3000000000000c2164000000000001c000000000002180000010395306e00000000000000dd800000000000000000006806737e0003b80000000000000000000000000002280000038c0000001b00000000000000000df10100400094000000000000003a2000000001ee3f000000000000001182765440003000060c478003b80000016f3020006181e00016c000a80000000000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x44800000f0001540122901cb00018309310000024000e04034c00004082000001431c94354843a2ee2a1ca221d187050d5010e8cb80a8a1e65469c35410e32838ecaa2641941c7655132cc60ebb4a819463075da54cc631a18e4aa08698d1870550434c686b90a8a1863465c05450c31a1ae42a2879850e72d50438c20ebb0a819261075d854cc530838ecaa2641841f76552310c20e3b2a8980611a1d95244010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 666
  | 4 => 551
  | 3 => 21
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (i*5) 5
  | 6 => packedAt s5K6 (i*16) 16
  | 5 => packedAt s5K5 (i*27) 27
  | 4 => packedAt s5K4 (i*38) 38
  | 3 => packedAt s5K3 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (20424+((h/222+packedAt s5K5 (17982+(h % 222)*11) 11) % 1287)*11) 11
  | 4 => packedAt s5K4 (22951+((h/183+packedAt s5K4 (20938+(h % 183)*11) 11) % 1556)*11) 11
  | 3 => packedAt s5K3 (1071+((h/7+packedAt s5K3 (1029+(h % 7)*6) 6) % 36)*6) 6
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7fffc0ffffc3f07ff0787ffc3ffc0fdc1f3f3
  | 1 => 0xf83ffff07ffffff81ffff83ffc1ffffe7e3c7f
  | 2 => 0xffc0ffff81ffc3ffe007ffc3ffe1ff0387cf9c
  | 3 => 0xfffffe0003fffff80003fffe0003f80fe0
  | 4 => 0xffff0000000003fffffffffc00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x908644621448610165418264c1324258c0d1b1
  | 1 => 0x22080881209000280a0a0809040494a01a2446
  | 2 => 0x511291240d220652a084d4826a412a0b054a98
  | 3 => 0x65ace249483aab9cd3d04623b3980c33e80f60
  | 4 => 0x8630c38e71c333e71ce76730231030c3f7b000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xece8e8c8ece8e8c8ece8e8c8ece8e8c8ece8e8c8ece8e8c8ece8e8c8ece8e8c8ece8e8c8ece8e8c8ece8e8c8ece8e8c8ece8e8c8ece8e8c8ece8e8c8ece8e8c8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36707
namespace PEqualNP.Outside.L_meta_36707
open PEqualNP.Outside.L_meta_36707.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x4a3158e003118001a0000e9e2400c60af18014208ac00360174d5b0922a948828817555ec33116a1027d4098e00c9c26396404e010c054300291e5b7000000000562d2802e008a6005844002000448002084812e00001220050a360005ff53017f94c05fd53017f14c05fe43017f50c05fc4301ffd4803fe5201ff54803fc52017fcc803fe32017f4c803fc3201ffd44077f5101ff94407fd51005f54407fc51017fcc405fe31017f4c405fc3100ffc8401fe21007f48403fc2101ffd4007fe50005f94007fd5001ff140077c50017fcc005fe30017f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x142001bf98a10007fac508002fd6284019fe3142001bf18a1006ffea508033fe528401bfea94200cff14a10047fe6508033fe3284011fe994200cff0ca10055fac308037ff518401bbfa8c2004ff9461006ffaa3080037d5184009fe28c2008ffcc610027fc6308023fd3184009fe18c200cffc8610027fc4308003fd2184009fe10c2004bf9821006ffea108037fe5084001bf284200dff5421006ff8a1080377c5084011ff9842008ff8c210047fa6108023fc3084019ff9042000ff88210007f44108003fd2084001fc904200cff08210027fe2108003f71084009fd884200bffd951005dfeca880037f65440013fb2a200bff9951001dfcca8802ffd65440177eb2a200bff1951001df8ca8802f7c65440073e32a200affd8d10055fec688003df63440016fb1a200aff98d10015fcc68802bfd63440157eb1a200aff18d10015f8c68802bdc63440056e31a200affd4d10057fca68802bfd5344015fe29a200aff90d10057fa868802bfc4344001ffb122000bfd8910007dec488002ef6244013ff3122001bf98910007fac488002fd6244013fe3122001bf18910007d8c488006ec6244017ffa922009ff9491005ffaa488027fc5244015ff9922009ff8c910057fa6488027fc3244017ffa8a200bdfd4510027fca28802ffd5144001bea8a2004ff14510057fe6288013fe3144015fe98a2004ff0c51004ffe4288013fe2144001fe90a2004ff0851005ffea08802ffe5044001bf282200bff5411005ff8a08802f7c5044015ff982200aff8c110057fa608802bfc3044013ff9022000ff88110007f44088003fd2044001fc9022009ff08110027fe2088013fb1044001ff0822000fd84110027feca08012ff6504009ff3282003bf99410026fcca0800e7e6504009feb282007bf59410026faca080027d6504009fe3282004bf19410027fec608012ff6304009ff3182002bf98c10027bcc60800ade6304009feb182006bf58c10027bac608002dd6304009fe3182004bf18c10037fea60801bfe530400dfea982006ff14c10037fc860801bfd430400dfe2182004ffd8810025fec408013fe62040037f3102004fb9881000ddcc408013fd62040017eb102004fb58810005dac408013fc62040097e3102007ffd481002ffca40801ffd520400bfe2902006ffcc81002ffc640801bfd320400bfe1902004bf98410027fea2080137f5104009ff2882004ff54410026faa208013fc5104009ff9882004ff8c410027fa6208013fc3104009ff9082004ff88410027fa4208013fc21040117f3002007ffd401003ffca0080037e500400ffea802007ff1401003ef8a00801bff300400dff1802006ff4c010037f86008017ff2004001ff1002000ff4801002ff84008013ff1004009fb8802004ff84010027f42008013fd1004001fa8802004fe44010
  | 1 => 0x7fd5288003fe2944001ffcca2000ffc6510007fd3288003fe1944000ffd8620007fcc310012fe6188001feb0c4000bf58620007f8c310053ff5188029bfa8c4014ff946200a7faa3100037d5188029fe28c4013ffcc62009ffc631004ffd3188027fe18c4001ffc862000ffc4310003ee2188003fe90c4001ff0862000fd84310006fe6088029ffa844014ff94220006fca110053fd5088029fe2844014df1422009ffe611004ffe3088027fe9844013ff0c22000ffe4110007ef2088003fd9044001ff0822000ff0411004bff65480257fb2a4000dfd9520004feca9004bfe65480077f32a4012ff59520095faca9004bfc65480077e32a4012df1952001cf8ca90047ff63480237fb1a4011ff98d20015fcc690047fd63480237eb1a4011ff18d20015f8c690047ff5348023ff29a4011ff54d2008ff8a690047fe4348023fea1a4011ff10d2000dfec490007ff5248003ff2924001ff5492000ff8a490007ff3248003ff1924001ff4c92000ff86490003ff61480017fb0a4000ff98520007fac290003fc61480097e30a4012ffd4520096fea29004bfe5148025fea8a4000df54520097f8a290047ff3148023ff18a4011ff4c52008ff86290007ff2148003f790a4001ff8852000ffa4290003ed2148003fe10a4001bfd8120097fea09004bfe5048001bf2824012ff54120097f8a09004b7c5048023ff9824011ff8c12008ffa6090047fc3048003ff9024001fec812000ffc4090003ee2048003fe1024001fb0812000ff04090007e82048009ffb2e2004bfd9710027fccb8800efe65c4009bf32e20039f99710027facb88042fd65c4009beb2e20009f59710027f8cb88012fc65c4009ffb1e2004bfd8f10027fcc78800afe63c4009feb1e200fbf58f10027f8c788012fc63c401fffa9e200fff94f1007ffaa78803ffc53c401fff21e200fff50f1007ff88788013ff62c40097fb162004ff98b1000dfcc588013fd62c40017eb162004ff18b10025f8c588043ff52c401dff2962010ff54b10077f8a58803fff32c401dff196200fff4cb10077f86588013ff51c4009bfa8e2004ff94710027faa3880137d51c4009fe28e2004ffcc710027fc6388013fd31c4009fe18e2004ffc8710027fc4388013fd21c4009fe10e2010ffd4310087fca1880037e50c4021fea862010ff14310086f8a18803fff30c401fff186200fff4c31007ff8618803bff20c4001ff1062000ff48310077f84188037ff658401b7fb2c2000dfd9610004fecb08037fe65840077f32c200dff5961006dfacb08037fc65840077e32c200ddf1961001cf8cb08023ff63840117fb1c2008ff98e10015fcc708023fd63840117eb1c2008ff18e10015f8c708023ff5384011ff29c2008ff54e10047f8a708023fe4384011fea1c2008ff10e10007fec508002ff6284019ff3
  | 2 => 0x5101efec2a880e7f6154407bbb0aa21cdfcc551026fc62a88737d3154409be18aa21bdfc8551026f842a88037f6054401bf302a200df58151006f8c0a88027c6054439bf982a21cdf8c1510e6fa60a88737c3054437bf902a21bdf08151027fecb10812ff6588409ff32c4203bf99621026fccb1080e7e6588409feb2c421abf59621026facb108027d6588409fe32c4204bf19621027fec710812ff6388409ff31c4202bf98e21027fac710866fd6388409fe31c4204bf18e210cffea710867fe5388433fea9c4219ff14e210cffc8710867fd4388433fe21c4201bf58a2100ffea510807fe5288403fea944201ff14a2100ffe6510807fe3288403fe9944201ff0ca21025fcc310813ff5188409bfa8c4204ff94621027faa3108137d5188409fe28c4204ffcc621027fc6310813fd3188409fe18c4204ffc8621027de4310807f72188409fe10c4204fd08621027fec110813fe60884017f3044204ff58221005fac110813fc6088435ffa84421aff942210d7faa11086bfc5088435be2844219ffcc2210cffc6110867fd3088433fe1844201ffc822100ff84110807ec2088431ffb2a4218bfd95210c7fcca9080efe6548431feb2a4218bf595210c7f8ca9080efc654842fffb1a4217bfd8d210bffcc69080afe634842ffeb1a4217bf58d210bff8c69080afc634842fffa9a4217ff94d210bffaa69085ffc534842fff21a4217ff50d210bff88690812ff6248403ffa924201ff9492100ffaa490807fc5248403ff9924201ff8c92100ffa6490807fc32484037fb0a4218ffd45210c6fea290813fe5148431fea8a4200df54521027f8a29085fff3148409ff18a4217ff4c521027f86290807ff2148403fb90a4204ff88521027dc4290813fc2148409f610a4201fd08521007fec090802ff6048401ff3024200ff58121007f8c090802fc6048431ffa824218ff941210c7faa090863fc5048431be2824217ffcc1210bffc609085ffd304842ffe1824201ffc812100fde4090807fc204842dbfb1ca016df98e500b6fac72805b7c639402dbf21ca016df50e500b6f887280037f629402bbf314a000df58a500aef8c52805b7f329402bbf194a016df4ca500aef865280037f6194001bf30ca000df58650004fac3280037c619402dbf98ca016df8c6500b6fa632805b7c319402bbf90ca000df88650006fa43280577c2194007bf304a0039f9825001ef4c12805b7f309402dbf184a016df4c2500b6f861280577f209402bbe104a014ffd96200a5fecb10053fe65880077f32c4014ff596200a5facb10053fc65880077e32c4013ffd8e2009dfec71004ffe63880057f31c4013ff58e2009dfac71004ffc63880057e31c4013ffd4e2009ffca71004ffd5388027fe29c4013ff90e2009ffa871004ffc43880037eb144001ffd4a2000ffca51000
  | 3 => 0x36cfb000470a58000e24f47aefea6185a798008000000010197c0000004f1670001a8001a746570a7e00000000068e308000009b000000000002650008b42700012d0000000e8004e4bc8709aa000001a105162000000000788000000c952c97a7233c0012c21d0003d114e8303e0006424e000058ba28b1270ac7898c44440a18a742350003a000000000000000007dcea9e14400001b0000006d000000338a94891ec000000000000000008491d000000d2d31800a7cb5000000000002708000001b977800000bb24180065a7c80d00030c598b6d492d4f26872fb001200981a50000009880470f316802d9644162193d4a804d5a938d796808874028b92161108f852fa1210000000017040a7a53b0000162df3600000016cd90f50222588f0e3000000000000000002e9354f2000af13f000000498ac44229c002501fea89369e307e8f42224409a3910d1050c6000000000127750f4b91d400000000000a709180045ba6647000000000002395144b4002a600086c000000000001dc00000108149a21fa0000012e86028919d58000224a55894633a0c921316409d3e1cf3d6000000003865254a0918004a624c58546240b6c00414000c099523650800119000000000000000003de12000000548522974c4fd05037c0000013b0975dc0024480098e0021f000000a00000006065cc8300034f3414d0371063f80f13e7282025a2f07913bd35840001436661ac051389d41940000000200102200c048000060000280900000c0480200002400002002004010050000000100e00600406000014018050040020100080000000408804004000078010180040280200800c0080400000c04000006024010010020000200000c0000000300400c00000004000030020000000000000a0080080100000000800000008010030000000500200c010010030080080100f00c010038070080040000100e0000400402200c000000000040080100000800800000004040040000040480100200800801000000008000000000280300400c010080000380000b0020080080301e000000040000180000400c00000003006004000010000140080000a00403001010018000000000100080000200004005000024000000020540f00100606c0280100200c008000180100000000600800003002000010000040000080900000c00805000008000000020000300200c0000700100000002000004000028000060080100102e000000000000000300a0060080180300000401000002000018070180100d00300201800002000000020000060000180301a00c0080100000c01000016004000737f6354439bf31aa21cdf58d510e6f8c6a88737e4354439bea1aa21cdf10d51006fec4a886f7e6254401beb12a21bdf189510e6fe64a886f7e3254439be992a21bdf0c9
  | 4 => 0xb8001431f23015bcfbc43518982e31f539c5b4660251a10000026f800000001b045900092197800000118e6b710012ea170009ec32082000000f78cd000000000003d90008b800264000d512f800000000f34aa000dd8810006800000022c000628535041452683d8380000000000000151400000000000000c40000015314c538e45613ca5a1398682b98fd4d25400005c2090f08500095cc416072ac7a61000000c3000396282cb0944ea344a096e000898000f20008208520f000000300332650000000002a000de1e7000588000002a85eafda578005ae001e04e375f160c780024209a33460650e924a3fc1f85e93c00059802a58b34a4ab181abac001350fa3db3223e0001c203600281000000002270008d683800000762e215b0069e11d8000004360008d46a0fa000005360000009b0000000001e45d406001b94ac3a4224004ee0000018d18c0000012cd31918a28f615a702ad22ac522ec5189a54b5b04dd11000000000003b41980007653a1c6001b7000000000001ce0003580037a0010fc00000000000002ac0000000000000000000000a440015daa2210fc93800072f118000fa000000004c000000000096000000d025c1dc3d400000858af57bb9a9f4031c54bc000ba8002fda414200000025267000000660000003562294c80000069a3c03e000000ce800000000000000000013b5da8aa9b61c80c4ae276ae2704be7ba639f6a404c272470000834002105274b0dc14f00000000000000124c19c82007f61a9ac52a0015080051a000611b5bbc00000294b891bce3dfc0000000005c3930009380044100000000000000d687b0005fc000474620f21d8ee00000000000000000758003fd7c0b58cf5249206fa2a000818d28be08d628001640004d12ac003b24f813472bd04aa002364562b80012918b00034a0c0008bf21c0014a3aa75c003a20a8c80b8c0060839df8b48000478000000008c4004dd6d92c80000027eae9d72f100072ea403a0000004c00032539400238440b9800000000000003053bc0000000000099a982ae000000000001c4001a79b80002d00000010e0000052e19c7459b0003b6d79f9800000178002ff00000000496000001a88002a0df8f70005f805d300300d0000003eb4e800048808000000003b6000052931180010055200009f10ded4e99f8000000000000010b000860add198004d2d30ff8951e899c0036653257800000000cc80c8008907f20e4dc0f05887913210200179800000000001ca000a41dc000494000004844f4af8000000005b800000000001008000f4002690000000012a1c00000000e1251c8c2800154116000003c700000000000000ff800000000000005236d4369022568dd1e1c7000000500560000014440044a81c000003a06b9365ee4d6020b28d9000000000e3800
  | 5 => 0x25154d85751dc1b1c1cd429c000030400000000a6a000003be3b400000000000be9032104988989d21d0a06f216c500000000050f6da10946362000000000000000000004b000000570000000000000090cdd00012b4681fe2f0003a70a000170000000000441b80002e0c599c001140001642f8000006a08be891d835c309e2c04000000002f91f296c00000000ecc1a482716000000004540014d96c13cb7647000000000000000005e0ec8c70000000000000048a6f00000086960000000cf95539801c9b8191cf5c4000001cc0010f00000068d39d9484c0000000000025c190f0168248c21931380000006518000129a3e1f66de0010c0003bb0e26b9ba0004be645372667151803921852289c98272a1a0b1a85eccac123005313128e070254000241f0704250001a48c80001dc2a1788fa2b8000001d0002e400087c0000000147a7f4eb0000005420c214c394a0007080029e00065c0000000044200000156000000002f400094150000000000000000011a4c6bb006cc58484747c51a10e4b604032e454a41f727a56c922fc0008b1962e944122142000e49f311051c000450008246c0750007e0b48003a681023080000000360da208564a226300084ee65ffaed0004f400000000698004
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe4058c10006dd4058c10006dc4058c10006df2058c10006dc2058c10026df1058c10026de1058c10026dd1058c10026dc1058c10004ff755881001cfe7558810004fd755881001cfc7558810004ff7358810014fe7358810004fd7358810014fc7358810026ef7258810006ef525881002eee5258810006ed525881002eec5258810006ef325881002eee3258810006ed325881002eec3258810024ff7158810024fe7158810024fd7158810024fc71588100267f51588100267d5158810026ee2158810026ec215881000cff705881000cfd705881002cfc70588100067c505881002eec2058810026fa1058810026f91058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ee4358810006ed4358810006ec4358810026ef7158810026ee7158810026ed7158810026ec7158810026ef51588100266f5158810026ee5158810026ed51588100266d5158810026ec5158810026ef3158810026ee3158810026ed3158810026ec315881002eef7058810006ee7058810006ec7058810006ef5058810006ee5058810006ed5058810006ec50588100066c5058810006ef3058810006ee3058810006ed3058810006ec3058810026ef1058810026ee1058810026ea1058810026ed1058810026e91058810026ec105881006e7f769401006c7f769401001e7e76940101057d769401001e7d769401001c7d76940101067c76940101067f63940100b67e63940101075e63940100b65e63940101167d63940101075d63940100065d63940101067c63940101067f62940100ae7e62940101076e62940100ae6e62940100067d62940101076d62940100066d62940101067c62940101057f71940101077671940101057d71940100077571940100057571940101067e619401010d7e709401003f7a709401006e7e60940101077710940101077a1094010107791094010064ff7688010024fe768801000cfd7688010024fc76880100a67e65880100067d658801009ede6388010006dd638801000eee6288010006ed6288010025f67188010005f57188010066fa6088010064ff76480100057f754801003d7c75480100967e65480100067d654801008ede6348010006dd634801000eee6248010006ed6248010066fa604801002fe82048010025f77644010006f77644010004f776440100077775440100ef747544010027766544010027756544010007d773440100ffd47344010027d66344010027d56344010007e77244010007e47244010027e66244010027e56244010025f77044010027f370440100f6f66044010027f260440100077650440100eff250440100077250440100eff150440100ef745044010
  | 1 => 0x81101477b518811000779518811013fea218811013fe8218811000cff764811004cfd7648110024fc76481100057f754811005d7c75481100067f65481100967c6548110006df634811008edc6348110006ef624811000eec6248110005f77148110025f471481100077a504811012f78504811004fe82048110025f8764811000ef87648110024f876481100077b754811012f7875481100077b654811012f786548110007db6348110137d8634811004dfb7248110007eb7248110007eb624811000efa624811000ef8624811004fe8624811000ee86248110007f37148110025fa7148110025f87148110007f0714811012f7b514811000779514811004feb2148110007e921481100057f758411005d7c75841100067f658411006e7c6584110006df6384110046dc6384110006ef6284110066ec628411011f775184110007755184110025fa7084110026fb6084110025f67684110026f67684110024f6768411000777758411011f74758411000777658411011f746584110007d76384110127d46384110007e76284110007e46284110025f67084110026f76084110027f3608411000776508411011f745084110007f22084110007f120841100067f73594100067e73594100067d73594100067c73594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f32594100067e32594100067d32594100067c32594100267f71594100247f71594100267e71594100267d71594100247d71594100267c71594100267f31594100267e31594100267d31594100267c31594100267f21594100267e21594100267d21594100267c215941003e7f70594100067e705941003e7d705941003e7c705941003c7c70594100067f30594100067e30594100067d30594100067c30594100067f20594100067c20594100267f10594100267e10594100267d10594100267c1059410006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c10006de4258c10006dd4258c10006dc4258c10026df7158c10026de7158c10026dd7158c10026dc7158c10026df5158c100265f5158c10026de5158c10026dd5158c100265d5158c10026dc5158c10026df4158c10026de4158c10026dd4158c10026dc4158c10026df2158c10026de2158c10026dd2158c10026dc2158c10036df7058c10006de7058c10036dd7058c10036dc7058c10006df5058c10006de5058c10006dd5058c10006dc5058c100065c5058c10006df4058c10006d
  | 2 => 0x6ed51d891013eec51d8910006ef31d891013eee31d8910006ed31d891013eec31d891013eef70d891004eee70d8910006ed70d8910006ef50d8910006ee50d8910006ed50d8910006ec50d89100066c50d8910006ef30d8910006ee30d8910006ed30d8910006ec30d891013eef10d891013eec10d89100057f755891005d7c75589100067f65589100067c6558910005df7358910055dc7358910006df6358910006dc635891004eec6258910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7358910006df7358910004df7358910014fe7358910004fd7358910014fc7358910006dc7358910014dc735891004cff7258910006ef7258910064ff7158910006f771589100067f5158910074ff7058910006fb70589100067c5058910005ee761891004eee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc63189100076f511891004fe97018910166ef60189100076c5018910167eb1018910167e8101891001e7f765451006e7e765451005e7d765451005d7c765451001e7c765451001c7c765451015e7f63545100075f63545100065f63545100e67e635451015e7d63545100e67c635451015f5c63545100e65c63545100067f62545100076f62545100066f62545100de7e62545100067d62545100de7c62545100076c62545100de6c62545100257f715451005f7771545100267f615451002776315451015f7531545100277621545100077b70545100057c70545100077870545100057870545100267f60545100277b105451002774105451002778105451002770105451000cfc76485100067f65485100c67c6548510006df63485100bedc6348510006ef624851000eec6248510007755148510005fb7048510005f870485100057e76941100867e76941100847e76941101567f63941100075f63941100065f63941100b67e63941101567d63941100b67c63941101575c63941100b65c63941100067f62941100076f62941100066f62941100ae7e62941100067d62941100ae7c62941100076c62941100ae6c629411005d7d719411005d7e709411005f7a70941101077b1094110074fe76881100067f65881100a67c6588110006df638811009edc6388110006ef628811000eec62881100077a5088110147785088110005fa7688110076fa76881100077b6588110147786588110007db638811014fd8638811004df97288110007eb628811000efa628811000ef8628811004fe8628811000ee86288110025fa7188110025f8718
  | 3 => 0xc70d951001c7c70d95100067f30d95100067e30d95100067d30d95100067c30d95100067f20d95100067c20d95101067f10d951005e7d10d95101067c10d9510055de76d8d10056de76d8d10014de76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006de62d8d10006dc62d8d100075f51d8d100075c50d8d1016fdb10d8d1016fd810d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d10006df71d8d1016ede71d8d10056dd71d8d1016edc71d8d10006df51d8d100065f51d8d1016ede51d8d10006dd51d8d1016edc51d8d10006df41d8d1016ede41d8d10006dd41d8d1016edc41d8d10006df21d8d1016ede21d8d1016edc21d8d1016edf70d8d10056de70d8d10056dd70d8d10056dc70d8d10006df50d8d10006de50d8d10006dd50d8d10006dc50d8d100065c50d8d10006df40d8d10006de40d8d10006dd40d8d10006dc40d8d10006df20d8d10006dc20d8d1016edf10d8d10056dd10d8d1016edc10d8d1000cfe76d89100067f65d89100067c65d8910006df63d8910006dc63d891004eee62d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910004ff73d8910014fe73d8910004fd73d8910014fc73d8910006ef52d891004eee52d8910006ed52d891004eec52d8910006ef32d891004eee32d8910006ed32d891004eec32d8910024fe71d891004cfd71d8910024fc71d89100067f51d891004eef21d891000cfe70d8910024fd70d891000cfc70d89100067c50d891004eef20d891004dee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89100076f51d891013feb70d89100076c50d891013feb10d891013fe810d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ee43d8910006ed43d8910006ec43d8910006ef71d891013eee71d8910006ed71d891013eec71d8910006ef51d89100066f51d891013eee51d8910
  | 4 => 0x8a100067c7558a1001c7c7558a10004ff7358a10014fe7358a10004fd7358a10014fc7358a10006ef7258a100067f5158a10066ef2158a10024fc7058a100067c5058a10066ec2058a1001e7f765461001e7c76546101967f63546100e67e63546101967d63546100e67c63546100067f62546100de7e62546100067d62546100de7c62546100257f715461006f7771546100267d61546100077b70546100057c70546100077870546100057870546100267e60546100277710546100277b105461002778105461000cff76486100067f65486100c67c654861000eee6248610006ed6248610005fb7048610005f8704861006d7e769421001e7e769421001c7e769421001e7d769421018e7f63942100b67e639421018e7d63942100b67c63942100067f62942100ae7e62942100067d62942100ae7c629421006d7f71942100077671942100057d719421000775719421000575719421006d7e709421006f7a70942101067e60942101077b109421000cfe7688210024fd76882100067f65882100a67c658821000eee6288210006ed6288210025f67188210005f571882100077a5088210187785088210025f9768821000ef97688210024f976882100077b658821018778658821000efa6288210067ea6288210007e9628821000ef86288210025fa7188210007f27188210007f17188210025f871882101877b518821000779518821013fea218821013fe8218821002cff76482100057f754821006d7c75482100067f65482100967c6548210006ef624821000eec62482100077a504821017f785048210067e82048210005fb764821002efb76482100077b754821017f7875482100077b654821017f786548210007eb7248210007eb624821000efa624821000ef86248210067e8624821000ee86248210025fa7148210025f8714821017f7b5148210007795148210067eb2148210007e92148210005f576c4210026f576c42100277675c42100277575c42100077765c42101777465c4210027f260c42100077650c42101777450c421005d7e76d951005e7e76d951001c7e76d95100067f63d95100067e63d95100067d63d95100067c63d95100075c63d95100065c63d95100067e62d95100067c62d951005d7c70d95101077b10d95101077810d95100067f73d95100067e73d95100067d73d95100067c73d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f32d95100067e32d95100067d32d95100067c32d95100067f71d95101067e71d951005e7d71d951005c7d71d95101067c71d95100067f31d95101067e31d95100067d31d95101067c31d95100067f21d95101067e21d95101067c21d95101067f70d951005e7e70d951001c7e70d951005e7d70d951005e7
  | 5 => 0xdee708812000fea708812000dea708812000eef608812000feb60881200076e50881201a76c50881200067f73597100067e73597100067d73597100067c73597100067e43597100067d43597100067c43597100067f72597100067e72597100067d72597100067c72597100067f32597100067e32597100067d32597100067c32597100267f71597100267e71597100267d71597100267c71597100267f31597100267e31597100267d31597100267c31597100267f21597100267e21597100267d21597100267c21597100867f70597100867e70597100067d70597100867c70597100067f30597100067e30597100067d30597100067c30597100067f20597100067c20597100267f10597100267e10597100267d10597100267c1059710004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7358b10014fe7358b10004fd7358b10014fc7358b10026ef7258b10024fc7158b100267f5158b100267d5158b10026ee2158b10026ec2158b100067c5058b10076ef2058b10026fa1058b10026f91058b101057d769431005e7d769431005c7d76943101067f63943100b67e639431019e7d63943101067c63943101067f62943100ae7e62943100067d62943101067c62943101057d719431010d7e70943100877a709431004cfd76883100a67e65883100067d658831013eef628831000eec628831000cff7648310024fc76483100057f75483100857c75483100967e65483100067d654831000eee6248310006ed6248310005f77148310025f47148310077e8204831006e7e76d96100067f63d96100067e63d96100067d63d96100067c63d96100067e62d96100067c62d96100077571d96100077a70d96101077b10d96101077810d96100067f73d96100067e73d96100067d73d96100067c73d96100067e43d96100067d43d96100067c43d96100067f72d96100067e72d96100067d72d96100067c72d96100067f32d96100067e32d96100067d32d96100067c32d96100067d71d96100067571d96100067f31d96101067e31d96100067d31d96101067c31d96100067f21d96101067e21d96101067c21d96100067e70d96100067a70d96100067f30d96100067e30d96100067d30d96100067c30d96100067f20d96100067c20d96101067f10d96100067f65d8a100067c65d8a10066ee62d8a10004ff75d8a1001cfe75d8a10004fd75d8a1001cfc75d8a10004ff73d8a10014fe73d8a10004fd73d8a10014fc73d8a10064fd72d8a10006f571d8a100067f51d8a1013eee21d8a1013eec21d8a10006fa70d8a100067c50d8a10066ef20d8a1000cff7658a100057f7558a1006d7c7558a100067f6558a100067c6558a10066ec6258a10004ff7558a100067f7558a100047f7558a1001cfe7558a10004fd7558a1001cfc755
  | 6 => 0xb20942200af7820942201ad7e76d95200967e76d952001c7e76d95200067f63d95200067e63d95200067d63d95200067c63d95200057d71d95200af6f21d95200ad7c70d95200af7b20d95200af6c20d95200af7820d95200af6820d95200067f73d95200067e73d95200067d73d95200067c73d95200067e43d95200067d43d95200067c43d95200ae7f72d95200ae7e72d95200ae7d72d95200ae7c72d95200ae7f32d95200ae7e32d95200ae7d32d95200ae7c32d95200067f71d95200067e71d95200067d71d95200047d71d95200067c71d95200067f31d95200067e31d95200067d31d95200067c31d95200ae7f21d95200ae7e21d95200ae7d21d95200ae7c21d95200ae7f70d95200967e70d95200ae7d70d95200ae7c70d95200067f30d95200067e30d95200067d30d95200067c30d95200ae7f20d95200ae7e20d95200ae7d20d95200ae7c20d95200957c75d85200067f65d85200067c65d8520067e820d8520004ff75d85200067f75d852001cfe75d8520004fd75d852001cfc75d85200067c75d852001c7c75d8520004ff73d8520014fe73d8520004fd73d8520014fc73d85200067f51d8520006f731d8520006f431d8520066f621d8520066f521d8520024fe70d85200067c50d85200957e75985200057d75985200067f65985200067c6598520006f7619852004df97098520077e820985200057f75585200957c75585200067f65585200067c6558520005df735852008ddc7358520075fb705852004fe820585200957e75185200057d75185200067f65185200067c651852008dde7318520005dd7318520026f66118520006f5611852002fe820185200067f76545200057e76545200067e76545200047e76545200067d76545200057c76545200067c76545200047c76545201d67f63545200e67e63545201d67d63545200e67c63545200de7f62545201cd7f71545200977771545200067f61545200267e61545200267c61545200df6f21545200057c70545200de7f60545200df7b20545200df6c20545200df7820545200df682054520024ec76485200076f65485201c76c654852000def714852000fe77148520007e76148520026ee6148520026ec6148520007e461485201c76f51485200076d5148520007eb7048520005ec7048520007e87048520005e8704852000eef604852000feb60485201c76c50485201ad7e76941201be7e76941201ac7e76941201b67f63941200b67e63941201b67d63941200b67c63941200ae7f62941200057d71941200067f61941201067c61941200af6f21941200076d21941201ad7e70941200977a70941200ae7f60941200af7b20941200af6c20941200af7820941200af6820941200076f65881201a76c6588120005ed718812013eec61881201a76f51881200076d5188120
  | 7 => 0x86500067f32586500067e32586500067d32586500067c32586500067f31586501067e31586500067d31586501067c31586500067f21586501067c215865005e7e705865005e7c70586500067f30586500067e30586500067d30586500067c30586500067f20586500067c20586501057f73186500b57e73186501075e73186500b55e73186500057d73186501075d73186500055d73186501057c73186500ad7e72186501076e72186500ad6e72186500057d72186501076d72186500056d72186501057c72186501057e71186501067f61186501077661186501067d611865000775611865006d7e70186501077a701865006d7a701865010e7e601865003f7a60186501057f76886500057e76886501067e76886500047e76886500057d76886501067d76886500047d76886501057c76886501057f73886500b57e73886501fd7d73886501057c73886500ad7d72886501057e71886501067d61886501076f21886500af7721886501077421886500057e70886500057d708865010e7e60886500d77a60886500af6c20886500057f76486500057e76486500057d76486500057c76486501f57f73486500b57e73486501f57d73486500b57c73486501057f72486500af6e62486500076d62486500ad7f71486500067d61486500af7721486501076e21486501076c21486500af7421486500057f70486500057c70486501ae7e60486500c77a60486500af6f204865002dfa70d86200a57e75986200057d7598620006f76198620004ff755862001cfe7558620004fd755862001cfc7558620004ff7358620014fe7358620004fd7358620014fc73586200067f515862004ef6215862004ef5215862013eec2158620024ff70586200067c505862004eef20586200a57e75186200057d751862009dde7318620005dd7318620026f66118620006f56118620065fa70186200067f76546200067e76546200067d76546200067c76546201ee7f63546200e67e63546201ee7d63546200e67c63546200076f72546200df6c72546200de7d62546201cd7f71546200a77771546200267e61546200067d61546200267c615462013f6c21546200057c70546200de7e60546200df6f20546200df7b20546200df78205462013f6e758862013f6d758862000dee718862000fe6718862013fe6618862013eed6188620007e5618862013f6f518862013f6d518862013fea7088620005ed708862013fe9708862000eee608862000fea60886201e76c50886200ae7f769422001e7e769422001e7d76942200ae7c76942201de7f63942200b67e63942201de7d63942200b67c63942200af6e72942200076d72942200057d71942201067e61942200067d61942200076e21942200af6c21942201ad7e70942200a77a70942200ae7e60942200af6f20942200af7
  | 8 => 0xde7d765452101e7c765452120e7f63545210e67e635452120e7d63545210e67c63545210076f72545210df6c72545210267f62545210257f71545210c77771545210267f61545210df7721545210276e21545210276c21545210277421545210276421545210057c70545210df6f20545210277710545210c57e75d81210057d75d81210077850d8121004ff75d812101cfe75d81210067e75d812101c7e75d8121004fd75d81210067d75d81210047d75d812101cfc75d8121004ff73d8121014fe73d8121004fd73d8121014fc73d8121024fd72d81210067f51d81210067d51d8121006fb50d81210067c50d8121006f850d81210067850d8121076fa20d8121006fb60981210057f75581210c57c7558121005df73581210bddc7358121006f96018121007785018121004ff751812101cfe7518121004fd751812101cfc7518121004ff7318121014fe7318121004fd7318121014fc7318121024fd72181210067f51181210067d5118121166ee2118121166ec2118121006fb50181210067c5018121006f8501812100678501812102eef201812102ef920181210057f73d8a500b57e73d8a500075e73d8a500b55e73d8a500057d73d8a500075d73d8a500055d73d8a500b57c73d8a500067f63d8a500067d63d8a500ad7d72d8a500ae7e62d8a500af6e62d8a500ae6e62d8a500ae7c62d8a501057e71d8a500057d71d8a502057e70d8a500077a70d8a502057a70d8a500a67e60d8a500a77a60d8a500ad7f7658a500057f7358a500b57e7358a500057d7358a500b57c7358a500067f6358a500067d6358a500076f6258a500ae7e6258a500ae7c6258a500af6c6258a500057f7158a501057c7158a500af6f2158a5001d7c7058a500967e6058a500977a6058a500af6c2058a500057f73d86500b57e73d86500057d73d86500b57c73d86500067f63d86500067e63d86500067d63d86500067c63d86500ad7e72d86500057d72d86500ad7c72d86500067f62d86500067e62d86500067d62d86500067c62d865003d7e70d86500077a70d865003d7a70d865006e7e60d865006f7a60d865005d7d76986501057f73986500b57e73986500057d73986501057c73986500ad7e72986500057d72986501057c72986501067f619865000777619865010e7e60986500877a60986500057f73586500b57e73586500057d73586500b57c73586500067f63586500067e63586500067d63586500067c63586500057f72586500ad7e72586500ad7c72586500067f62586500067e62586500067d62586500067c62586500077761586501067e615865005e7e605865005f7a60586500067f73586500067e73586500067d73586500067c73586500067e43586500067d43586500067c43586500067f72586500067e72586500067d72586500067c725
  | 9 => 0xf73581510055f73581510e57e73581510057d73581510e57c73581510075c73581510e55c73581510057f72581510076f72581510056f72581510dd7e72581510dd7c72581510076c72581510dd6c725815106d7f715815100777715815106d77715815105e7f615815105f7761581510077b60581510067e60581510857e76181510057f73181510e57e73181510057d73181510e57c73181510067f63181510067e63181510067d63181510067c63181510dd7e72181510057d72181510dd7c72181510067f62181510067e62181510067d62181510067c621815103e7f611815103f7761181510067f60181510077a60181510067d60181510077960181510077b20181510077820181510067f73181510067e73181510067d73181510067c73181510067e43181510067d43181510067c43181510067f72181510067e72181510067d72181510067c72181510067f32181510067e32181510067d32181510067c321815103e7f711815103e7d71181510067f311815110e7e31181510067d311815110e7c31181510067f211815110e7e211815110e7c21181510067f30181510067e30181510067d30181510067c30181510067f20181510067b20181510067c201815100678201815110e7f101815110e7c10181510067f73596210067e73596210067d73596210067c73596210067e43596210067d43596210067c43596210de7f72596210de7e72596210de7d72596210de7c72596210de7f32596210de7e32596210de7d32596210de7c32596210267f71596210267e71596210267d71596210267c71596210267f31596210267e31596210267d31596210267c31596210267f21596210267e21596210267d21596210267c21596210067f70596210067e70596210067d70596210067c70596210047c70596210067f30596210067e30596210067d30596210067c30596210de7f20596210de7e20596210de7d20596210de7c20596210267f10596210267e10596210267d10596210267c1059621004ff75982210067f759822101cfe7598221004fd759822101cfc75982210067c759822101c7c7598221004ff7398221014fe7398221004fd7398221014fc7398221024fe71982210267f51982210267d5198221026fa70982210067c5098221066f92098221026fb1098221026f81098221004ff75582210067f75582210047f755822101cfe7558221004fd755822101cfc75582210067c755822101c7c7558221004ff7358221006df7358221004df7358221014fe7358221004fd7358221014fc7358221006dc7358221014dc7358221024fc71582210267f51582210267d5158221026ef2158221026ed2158221026fb70582210067c505822104efa205822104eec2058221026fb1058221026f8105822101e7f76545210de7e7654521
  | 10 => 0x300805901e00000500100000600000a00000000600000000300100400100200300500900000800b00c00801b00000900500000000a00702401200400400f00a00601900000000300701b00300000a00100400301200a00500001002600405a00600500400001100100a07200100300c00800800c00100402300000400001001300600d00100100f00700801001f00000900000000100000200200600f04802300200300300300007400000e00300200600200100200200300000400800100200b00900f01b01500000000000200100700200000200900200202500100200000302a00d00800200000000800000102d00401d02c00501800400400501400300102401500007801100001d01200500101a00e00800100101000000a03000501b00000b00400c00b00100800002e00d00000500100200000e00700700300100100900001c00000000c00500e00000200101e00100c01300c00202800402900000d00000000200000000900a00800200601a00101000100000d00201200000700500801500a02401f00b00400300200a00400a00000000400000f00c00100800002b00600300200000100400000d00200100400000200400000000000000100000100a00400000c00e00200200700000100a00100800100500801200300000000201100100300600000301d00100400900000000000000300000500200400600400a00100000100200500f00700b0010050100000010000020000000090000dd7e76d89510057f73d89510e57e73d89510057d73d89510e57c73d89510067f63d89510067d63d89510de7e62d89510df6e62d89510de7c62d89510257e71d895101d7d71d89510d67f61d89510d77761d89510df6f21d89510057e70d89510057d70d89510df6c20d89510057f73589510075f73589510055f73589510e57e73589510057d73589510e57c73589510075c73589510e55c73589510067f63589510067d63589510dd7f72589510076f62589510de7e62589510de7c62589510df6c62589510de6c62589512157f71589510077771589512157771589510c67f61589510c77761589510057f70589510077b70589510057b70589510057c70589510077870589510057870589510057f73d81510e57e73d81510057d73d81510e57c73d81510dd7e72d81510057d72d81510dd7c72d81510867f61d81510877761d81510077b20d81510077820d81510057f73981510e57e73981510057d73981510e57c73981510067f63981510067e63981510067d63981510067c63981510dd7e72981510057d72981510dd7c72981510067f62981510067e62981510067d62981510067c629815105d7d719815100775719815105d75719815106e7f619815106f77619815103d7e70981510067f60981510077b60981510057f73581510075
  | 11 => 0x4dc3fc0f5ce5c00000b329f6bbf053a8100015c0007b268d05cbf400000000041a1060000007840007ad858cb4748000adcba605100000000047f50e2c00002c88b67cb0008ae210687cf39de0f654f0ac00033c7d26fa00008a000b1f0760000d08180004b833a00000019a624cf5b6657b23c39eaacca45168cf1323385f400002144a7a23cc6c209cd4970f1ea788000c3a00094e0002204f40004155f60000000003a60268f00006d9000212b0c590d7d6040004e427363000049063a32e82732428200027400069833e00037c172c257fab94d23de64fcd7279237483637a484d74c641309ae438000000c72d0e9900004366f20009b60004985b6134000b963c4000000000ae00002c600014200000086c6f400000000000000045876abb83ca6ef1580003f90004560000000008a8362bd800073a000b1db5200000000001a000000dca0009e2000707bfeb3600072568b000000000674000000c509350005650000000000000000000000de000000cc6b0e000c34dc929e6a4d9c922c4a3dfa36abd1e40a23e33ea53240c0935b4454a6083c250d607e80ca0083b0b16ae404c22675005491e03b3ce5ec74ed38be2b623328ec08d5ba61000000100500b00200b00301000000000800c00000100000000400a00001600300000001b01100200100000000001c00000700800300000801301500200100101302300100201400100600200100300a00000100a00000700100d00100900000901300200a00600001200200000500100000300200000500f00a00a02900100000000c00101000300800600400700000000000000200200a00800101900401300200000400c00000d00000000100000500200100f00001f00002e00800500002c00001002201d00000000400200400000100200700000e00200000801100000000700200200f00000500600b00000300101600600b00005600000400300000200200500800502400300a00700100000200000900001800000000600000000900200a00200400000200000000000000500f00900002100100100300400100100100400001e00200000000000500000000100a00700100100400000b02800600300000500000800102000100000001c00100000201000400003a00b00100400902200000004500200500100100003400200500601d01101a00300200900100004c00900100000400800a01300000000600000900001900c00200801f00300400300e00500700200000000000000a00400200100300000200100104400200100200200400700000001100101600301a00001200700200401200601700600000703e00201600000201d00201000500001900300d00600101500000600600100400500a00100901c00300000300d00e00001500000100000700b00600600100e00000a00000000
  | 12 => 0x143e19096bebde2b636e000a4a6163c04aa000dd10001b8a002e80ea473dc100064aa64884c8d000c06000000b56000af222a53859c4a61a0bfb000793a9a9660000529fe78a933726000000820d160007620000403e8baa800122c240000001f88fe0000002ee9b800012900018caa304205e01098430249600c3b374c00000000000039c0000000002ea2ec000d8a000000a983ad0000000000004149f20eed95c608dac8291b47a1ff452102428a0a7100f44506d2656a027380f393a05acd507070ab7e7edadb864b100868dca8adc7c2100019c6e4c9d0004ae2d195e000230d0825220d93496f000cb70eb0000004b400084ac122d2daa00056a7ee000000a845e4000000c32000000384a7c8f2bea0006a830a8ba58e330bf83f5b23cb8350d5000000096a000c96089ccc8f47c9ba445c104000660ad8b76dac000a663beb1aae60008ef268000b580000000003e4000c74000430b38000372000d7c67cce190d0a88500003709d27b344cde077382a83ac76c524c6c54d2e01866ebe492e9ba0007b89262980005dc00ac71a9caa4050000bb000000094c964000d21c91000000000000b020d80007af00081e29a00026ad7900000082282c85cd002d83f2cc818ea860920003c86b49311bc95aab95cc000000a4400003acca4be0003b5c62c220000ae170596c9849a89e20476648800000082482d00082e58f1c23bac08b3f096000cc52f565e564ae83c2d8cdda2d40b40001cc000b6342a4e000013e00038e224cd90008c5000b7370582800046cdb80000000005a30008bc0000007719e8000ce6577000000b430001967b40000006f5d814b6b34a0e99a000b17000bf9ba3dcb7fe00028a328d0a0000f0aea68a293971a8f1d2c7a0a4c4e354afe00035256200004a34c000000000df36e6af0af929454ac0a79a000232574aa7becd14d5792c0006f100024600000000e000421678bca728d92aba95cb844a4000000000deb000a92000000188d946d7af60001ee000a4cd76c4493843fd7b4ca7c70009f053c918880445000000090502a3fddcc5c9d4942bc4cb5cae61a4061d4dc87efda08901281fe936c9a1c808cd4c14ca2c2bdb6e0f10c8b88a68b70996914a464d48c649c29c26c0f90380b01c4b7a9bca7241f893c1c75891f0e0d962be1dea5a7bcb0043d2384f0b90234d5212c466566378a7e7780d65377a090e47e9e6d851f069682b958578a9bceacf29ac6902fdb677d7a3da17826c280a092d0e62083040ce3001e8ca10304f2adf93e3bc546816626a108a4434a1ca422fb68cd107de9e4d7e296402cde20adae0e82548a6000d18535c0c1a8310229afa1549fa0c41b2caf88666c4720007705c20008fc00024e654c4cbb631c582408288000703bac50c192000dde432abe96d01c0007b0d5e98885a000c1b06e
  | 13 => 0xb1d10b9802380d460787b10200000000c6000382000702000000ad400090270eda21cd682d1e0b5bc17d90242dc8cac8099eb1ec40558044d42746592650d973cbad2d542726ea6acbf7000000000000000000222000000796bf600000000076fb470000000005f2dc6000c860000000003d013a0608a22b2a8c0000005b22b8dd09e7c3e58a960a7600080e2b08e45005941945d6dc000079511ede82ae65c63cdcd6a3d4f0001ac4bc00000067eac80c20006025fa2283faa5e852651a1600057680c00000000027e8480bc000000cf87f800064b1da7ea2e4854cce0006c000097691c93288e3348758c000000048c0000003b6c2ebc03512e0af4000000a34cf43d425a59a2e26f369f7c500068068947c000dbf00057d3579dc0000006b0000000000768711c9e72324900038cd2638ac20a7d5fe00000000072ebee982c4b000000000dee00097cc020009b4000dc362ea4e1e724a5b08cd7b658bb12b5e1370cdaf5abc2e6a4087ed77522d22000291ad952834f3d2992d822c2608000000000b14000aca00072c483a4800000097e96c180dd44c05de00042e000b5a84ca78ce20005cad4b000aa80000009da0005e0a880006d0b9a0001407942020000003f4a8062cdd80fe7642cc3680a61120001dc0005200007301bea0c04614800000000075400046838664f1fb43b8420008ac31a688016b65782cb39b25c0bfc164125d6600046f000ab2266000211dd6a260009120000007016b856c000514c105911f20009a8a9e0006062644814d20002bb39600000090b1cb423d20116262464612d4063eab400006600000031399c6340000009c8b201bac463dcd2c3cf8a1cda0000d40b80b6cb224c97a3b1d581ceb6d1f47ec336a52a06d782fec588f641ec8f54c78ed1d7729c4da46d34ccb711d03140000000002000000008f50b30004762f12f35a8b6f000000b1c000791000000000000000000000973d0493c0005a18f10000d1000798a121eb59f46a35a5c625e556b8add2000000000830000000000c7700000075c3ee63685691652ecd7aa00001c0846c737c0a7758d1f6734b2c1aac783b80dc14eae20aa14aa43a94dcf00066634a8083f600000083e348000470000000000d6480400000016cd5380a0000004f67d0000493000ccb19819eb28000b600006c8b3a3f0000d7ac92da817e0625be7567e2b06d3c000494000000379c1ed868fa37f00081428e443000441000732dea57c5da032cc700006c000760000000000ac4548b54448a220009fca3a00044600001f544000cf62b49f898a4c853ec2cd1a94084e2f6000d48316000684214000d1f23e271891de9cfc53a000b2aa507d85a467a377dc56babe0d34739000000786000000000000000588a30000000d846fc000ce84b258685e20c0003d6568d240000004176
  | 14 => 0x7f0d55a9dc2a569a7f780000888b74afb8b80fa152cd00008de00008441dde2000000d62b2434dcc491a9085108746f87120e2a7a72a6de78c5e84126ec0009494d806400060c2479c0080c8ca966ae42c8795514da71a6e82d0d5164821c8e69506bca048e89446645fcd4abe811a5543a9812b6a9bb000bbe206072056ba2b3c22ec9c9cec6846e51ec3c00000036000054d4de000704d3600000045e75200000000000001eaa571c000422000b687ca00000000083200015a69a0000000000003924757eb00092f160c6aacc0004c2cf900000000071e4164ba000000270a1d6009cf000cd4abb7f409500041bbba00000000008f73613ba8e000ce00000f7dc200096edec1200007cc6281a29ec000dcc30648577e4130006d60000008f3c1421a000cbe000d27000000af8a906c40000004e6c38014add86277a55a91d1623acdba000a8b0003a200000010048000000081c1749ea8d4aa10001380000008d2000a3c000872d6ec7598e000000c51000000a240000000008ce5bc5d08773319a01e0114bf5c9f000311bbcace7140000000002169e944edf273e4a09b08443557062f887cda66a5353bfa16aa79cb62de9207f2000593945ad65a656ea1a00088a7c43081442aa46075a213c4dbdac425679e02a2000000400dbecc93ab0000007fc7d5000db4000000000b8e118ca66e27279b719052652400029202ece300000000052aaec676d68000000068000df000000000098c9700da36652ca3803e074088907632444462244a087c2000b42540000000b910000009d05063de55e00010e1261fc2ca2a6000c1d0000000007ac1505c849113cc18000000af7424d7f17c5aa1685aec8b5f020fb5cab08388100d25796aad1b4390003756dab486f600035c6722ac4a89cda3e437aae358ba155c4f8097ae10f2000418aee0000edcb00000002bcc0427800000000000000025cab666a8b24e217850a99891000070000000000062a00027aa41000000000000000b6b54e42069c8b40004b000095287332f0009e3aa2000bf206a26e550cd39c6000d98708b78a1b8c318400070d146b98b690000000006ca7c600000000000064eb9ed022f42fc54b2fa7d6b215a2c270009e589a474d9902cb4aaa99307a8a2e4ea6fe53697456b02a0000005343ae50841945a215b1b8d60000005526ee6d40000000000004783da598000b41d88d1c23a0002da24074a0008a030e0006a10008d86cccbc000b3ed90a83542a6e43cdc4ab700040ed8e48a0063fe000000260bf00001e900035e3f8dce31e8b04c40000000cfb4076e000000000b45000a6a000000cfe0006d8000000000b18000000c360000009470009722cf398000000530166620b6c882512410000000000b2500037d2560000000004acb4c48e00028c5f8868c1ab300c000065a37
  | 15 => 0x6a2a7b0009f40284d0d800000001230000008ccb920391f95801b07978d018a28676c90058c7d4b440000000000000fb692ca088c0003568f89682802d627600000000027cc6e000000000186000b3dc9434bc660e4d063af9562481e290a3491d87db0b2928980c84b463641cac16729a206465d860a000bbb000c7e000000c56000aa6a19000774000840236d2a0f80009bda182ce92a0003e6b2e3ec584bd0a5c5e209e73ccaccaad3ece47e98e051cc8e09472200000000000051acc2cec00012a000000000000000776d44cba0006428987448e21ecc0e4863a8000618df1d3a720bdc8a35c400086e8be000284000000000000b9c622829000a82d5c5b8000d6cb7279c89c775db66589be66865287a16ecf08600003f7091b8d2a404e6d5cee6a670cd5621ecd673dbd632264d1e608b0cc43e9c2db20001fa986000426644124ada000b827e034e2ff2f9482000d30108000db07373c6ab85a98065a7bd4a144e890c7134faca81c607c61e57e000a854a2a1e2f75d4d4ea2803cae34fe0fc49ec7cded034b8c6cec4fcf70005607a47f6a627212a8b5031240a1b4aaa000000a540983d879069e000000182b226c6c90c1fb861ae3408929d84ce0001b6b2611000038831877c0004715a5686718d12c23139b4e000cfb36cd25a6c7ae4d609a6e086a11c978716a9fabf5e66700000000003463b2bce81a00217a3cd94808e01dc5e000a2a0005046943a761c7dccdc1fd5d26621273e201bad70ef742d29c5a0b75181cfdef344cd8894b7c2908c464cdbcbc83e0afc004ac075e5cea91342d6a3ddc26be63739063aa8962428aabd257295457abcc94a5702a0962ba8d70a8d63868e8ea73b49210c0be1d607ebb4a562c4d9e9a6d9bc29d0c7bab80135000cfa9a4d4d37e0006dc00043a0003a0442a329b93fb000440b93a74000bc600020e00064000007a082bbd9461a63710ec0009197f13a4c8a12e0360000009cc7da0007241a4d83c6c4eed9a41c0007aa00094b3943900002ba6f0a70404d2822bdf4b08d329047be136c48a587a63c983432abc279e6b2c9b32cac222ccc060ec30b8fb04b75ba02f25ee5ea5ac8ee000b64058000ade00039a000000baecb1000876994000bb24ec7409d60007ce0002580cb1761e5c88000cd210a0009ee9aa9a28c20007e47c80000000483262f0ad0924000000c700003b40006a06b6000000000d5a0008c88660009ca59e5a0320ac6878000cdf0ba7e600000000036a000de40008c915600000030c15eb19870012000b0a0222188cbae5ca2376
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa9e84149630400153b08292c60800237a1c4258c100046ec3884b182000a5e8510963040014bb0a212c60811eb56067058c100256b408a0b182000ad58114163040434bf02282c60808795a045058c1010d2ec08a0b182000e558114163040014ab02282c60808297a005058c100052f42e80b182000a5d85d0163040011bf0ea02c60801a3721d4058c100052fc2a80b182000a5c8550163040011bd0e202c6080023761c4058c100346f43e40b1820008dd87c8163040014bd0b902c608002976172058c100054f42640b182000a9d84c8163040095ad02102c608002b56042058c100047c402eab1020048f4815cd62040091dd0fa92c4080123b21d525881000574402a4b1020048ee87cc962040091d90e992c4080029d60450588102363c380a0b102046e682014162040015d700baac408002ba201755881000567418eab102000acd831d562040015cf02b9ac408012b9205735881000537428e6b102000a6d851cd620400155d0839ac408002ab610735881000727a9ca6b102000e8d4310d62040095cd02282c408002b9604505881010d37c08a0b102021e668114162040434db02282c40800399604505881000532c08a0b102020a6e80141620408dcd6e0282c4080039a1c0505881010f35080a0b102021e691014162040014dd0b982c4080029b617305881000537c2a60b102000a6c854c1620400155f08982c408002ab21130588100055742060b102000aad840c162040095cd02182c408002b960430588101062fb8ac72802020c5d7158e50040438bce0b1ca008003969c1639401010637b8ac52802020c6d7158a50040438dce0b14a0080039a9c1629401010735082c52802020e691058a500408b8eeecb8ca0080825de1971940100063bc32e32802020d56635c65004041aaac6b8ca008083599897194010106b2b12e32802045c76605c65004041ae4c0b8ca0080123be1d628801000672b12e3100201287d86dd520040018bcc7baa40080571b98b75480100043f43aca900200787c875952004001cd040b2a400800317dd563480100062e3aac69002000ec82058d20040018deeab1240080031b1d5624801002d74402c49002000c7475dd910040019a8e7bb220080031de1776440100063a42eec8802000cd783dd910040019a907bb2200800339e0b764401000672416ec8802000c7450dd910040018eeedbaa2008082dc20375440100066bbb6e68802000ce776dc910040019ceec3922008003711cc724401010cbb43ca08802000c777694110040436e50f28220081135ca1e5044010105b9c34a08802020b71869411004041ae6ed28220080039cdda5044010007a9b9ca08802043f50739411004041ea4c72822008083d458e5044010007b1b94a08802000f60729411004041ec4c52822008083d858a5044010
  | 1 => 0x6c2382a2880629d21951485100de3a3b2a290a201be646254521440018f0cbb8242880031e194704851000675b10e090a2000d71511c121440018b8c73b4a08805a97a1b63941100062f3b6c72822000e1f64d8e5044001c38c9b1ca088003175c7639411027e2f386c72822000e5a70d8e504402b4dd0db14a0880031b9db629411000727b1ec52822000e4c63d8a50440018dae3b14a0880031b9c3629411000735386c5282200087f8758a50440014bf06b14a08805a9720d629411000537430c52822000c6e7618a5044001c9ec6314a0880039318c62941100af34314a11022000c78659da2044001cd0c5b2c4088003b218b638811000d75436c51022000cea76d8a2044037cd0c4a8c40880135c1c5518811013fb110aa3102202187e86dd520440018b8c7baa40880571b18b75481101ac3f43eca902202087c87d952044001cd041b2a408800317dd763481100062e3aec69022000ec820d8d20440018deebb1240880031b1d7624811013e7238ec49022001aea80d8920440019a8c7b8a40880831e1da50481100af34314a09022020d7071941204402b8f0edbaa40880579a18b75481101063c3b6ca9022000e6862d95204405b9b0edb1a4088003b218b634811007575436e49022001ce876dc920440035d50db12408809f3a1db6248110006b9ba8e29022027de3721c520440012f10ea8a40880131e1d951481100df34312a29022004d707154520440093d10e90a4088006ba2192148110026743b2429022004de0714852044001ec2a290a408800e1fa1b75841100062e31eeb0822000c6c62dd610440432f501bac208800e1fa1f65841100062fbaec70822000c5c75d8e10440018deebb1420880031b1d762841100263b3b2a30822004d7270546104401b4ed0dbac20880831d9db7584110005b9406eb0822020c7676d96104405b9acedb1c208809f399db628411000e733b0c50822000ec46318a104409d4ed0d284208800f1d9da50841100062fb9ce6b282000e1d4310d650409b4f700b92ca080029e20172594100052f418e4b282000a5d831c965040010fd0e192ca080021f61c32594100051f42064b282000a3d840c965040994eb03382ca0812f1e1c2705941003c3f43e60b28200087d87cc165040010ff0e982ca0801e1f21d30594100051fc2260b282000a3c844c1650400147d08182ca080028f61030594100253b40860b282000a75810c1650400f0fd0f902ca080021f61f20594100052f41e40b282000a5d83c8165040958f0e1902ca080129da0420594100053ac0840b282049c787008165040018beeb3aac608003275d07458c100070faa4a8b182048ad7815c963040095a902b92c60800297a147258c100052ec28e4b182000a9e841c9630400153b08392c60800237a1c5258c100046ec38a4b182000
  | 2 => 0x773589100062e32ee6b122000ccc62dcd62440011bd0fb1ac48800317dd763589100062e3aec6b122000c9f74d8d6244001938e9b1ac48800237a1c63589100062fba8c6b122000c5c7518d624400193ee831ac488003271d0635891001c3f43eeab12200387e80dd562440011bf06baac48800a3720d755891000477c12eab1220008fb805d562440010fd0e3aac48800a37a1f73589100062fbaee6b122000c5c75dcd624400193ee9b9ac4880021fe15735891001c3e42ae6b1220008bf845cd62440ab17908b9ac4880023be0973589100047bc0ae6b1220008de871cd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd62440018deebb92c4880031b1d7725891000667b9ee4b122000ccc73dc962440019a8e7b8ac4880021fa1f515891001c3e43ea2b122000c5f73d4562440a98b8e7a8ac4880031e1d770589100043f438a0b122000c5f7314162440a78b8e6282c48814b1edc05058910006373b6ca3122000e6970d9462440011db0f328c4880029ba1665189100056741cca3122000acd8399462440011df0eb28c488002b3e0d65189100056641aca3122000aeb8059462440014dd0c328c4880031b9d865189101ad36400ca3122000e6a701946244001cd2e0328c4881479ac40651891028f34080ca3122000cce76d8c6244001c9ecbb18c48800393197631891000747b26c63122000ec970d8c62440011db0f318c4880029ba16631891000536c2cc63122000aae8498c624400155b09318c488002b3a0e631891000477c3ac63122000a6f8558c62440014d90ab18c488002abe11631891000556422c63122000ae78158c624400159d0c318c488003339d8631891000727b28c63122000e4c6518c6244001d1ec8318c488003a3190631891000765380c63122000ec97018c62440014dd0da88c4880029b21b511891000727b1ea23122000e4c63d4462440016d501a88c4880029ba18501891000727b18a03122000e4c6314062440a3cd6c0280c48814297a1b63545100062e3b6c6a8a2000e1f64d8d5144001c38c9b1aa2880b7d4043635451016e2fb8ec6a8a2000e5771d8d51440594dd0db12a2880031b1db625451000727b1ec4a8a2000e4c63d89514404fec021b12a28809f1bdc7625451000733b8ec4a8a200087f8758951440070f90eb12a28800297e0d62545100e52e41ac4a8a2027a6e8618951440018d8ec312a28800393d8c625451000726318c4a8a202cf60101895144001cd0c5b82a2880821fa1870545100062fb18e0a8a2000c5c631c151440018dec4382a2880031b188705451000734310e0a8a202097a861c151440018f50c382a28800356d8c7054510006ac318e0a8a2000d6b621c151440018f4c4382a2880031e1887054510006b4310e0a8a2000c68621c151440438f
  | 3 => 0x1b2a2000c5e76d9763440011bb0f32ec68800297a1665d8d100054f424cbb1a2000a9d84997634400159d0532ec688002b360a65d8d100046fc3acbb1a2000a9f84597634400153908b2ec688002b3e0965d8d1000566412cbb1a2000a5e8619763440018bcec32ec68800387d9764d8d100070e32ec9b1a20008dd8799363440014bd0b326c6880029761664d8d100054f424c9b1a2000ace82993634400159b05326c68800237e1d64d8d100052fc2ac9b1a2000a5c85593634400159f04b26c688002b320964d8d100054f430c9b1a2000c9e761936344001c3eca326c6880038719464d8d100052f42cc5b1a2000a5d8598b634400153d09316c688002a761262d8d102862f3b6a3b1a2000e1f64d476344001c38c9a8ec688002d6a0351d8d100052f430a1b1a2053c5e761436344001c3ec8286c6880038719050d8d100062eba8ebb1a2000c9f749d36344001c3ea92a6c68800297a1672d8d100052ec2ce5b1a2000a9e849cb634400153b09396c688162b6a0072d8d1016d6cc00e5b1a20008de8714b63440011bb0e296c688002a7a1052d8d100054ec20a5b1a20008de8710b63440011bb0e216c68800297a1442d8d100052ec2885b1a201fada80dc7634405b4bb03a8ec68800297a0351d8d100046f43e83b1a20008dd87d0763440af4bd00286c68800297a1740d8d100052ec2e81b1a20568df87503634405b1b90ea06c68800297e1540d8d100052e42a81b1a20008de8710363440151bb0e206c6880b637a1f20d8d100046ec3e41b1a2000a5e85c8363440014bb0b906c688002a7a1320d8d100054ec2641b1a20038ef8754b62440051df0e996c488002b3a0e65d891000566c1ccbb122000acf83597624400159906b2ec48800393d9763d89100072632ec7b122000e8f64d8f62440014dd0b31ec4880029b61663d891000557424c7b122000aad8498f62440014df0ab1ec4880029b21563d891000557c22c7b122000aac8458f6244001c9eca31ec4880039319463d891000747b20c7b122000e8c6418f62440598dceda8ec48800393d8f51d89100072631ea3b122000b6a80d4762440014dd0c286c48800393d8c50d891000726318a1b122000ace839d7624400159b073aec4880029ba1673d891000536c2ce7b122000aae849cf624400155b0939ec48800393d4e53d891000746a1887b122000a6e80d47624400155d0998ec488002ab61331d891000537c2ae1b122000a6c855c3624400159f06b86c488002b320d70d89100053742e61b122000a6d85cc362440014df0a986c4880029b21530d891000557c2261b122000aac844c3624400155d08186c488002ab61030d891001c3f436eab122000c6c62dd562440010fd0fb2ac488003171cf65589100043f438cab122000c5c7319562440051bd0db9ac48800317d9
  | 4 => 0x5840014bd07316cb080029760e62d9610006b8b8ce1b2c2000a7581dcf65840014f501b9ecb0800317dce73d96100051f420e7b2c2000a3d841cf65840018bae639ecb080029d60473d96100053d400e7b2c2000e1d4310f65840014bd07b96cb080029760f72d96100053ac0ee5b2c2000a7a80dcb65840014bd07396cb080029760e72d961000637b94e5b2c2000a75811cb65840014f500396cb080021fa1c32d96100043ec3865b2c2000a3e840cb658400147b08196cb080028fa1331d96100051ec2663b2c204cc75719c365840018f4e5386cb080031e1ca70d96102663cb8ce1b2c2000e71719c365840010fb0f986cb080021fe1d30d96100051fc2261b2c2000a3c844c3658400147d08186cb080028f61030d96101053b40861b2c2000a75810c365840010fb0f906cb0800297a0f20d96100052ec1e41b2c2020a768108365840014eb02106cb0800a37a0f75d8a100046ec1eebb142000a758114362840432f501baac5080021fa1f6558a100043f438cab14200387e87dd562840430fd01baac5080021fa1c7558a100043fc2ae6b14200387c855cd628400117f08b9ac5081562f2117358a100043f43ea2b14200087e8714162840070f90e282c5080029d6045058a102dc3e43ac4a8c2021c79861c151840018f4c4382a3080031e18870546102d6b8c08e0a8c2000c7865dc121840018f0ca38243080033a58870486101bc3fc3ac5284202087c8758a50840412f100b8ca1080831de197194210106b9c02e32842045d70805c650840418ecc0b8ca1080831e5da50882101063cbb6cb1042000b7181d9620840098f2eca8c41080021fa1f654821000734106ca90420048ee87d89208402bcd0c528241080031e19776482100af34316ea904200097a87d952084001cd0c5b2a4108002dc6076548210005f0c0ec49042000978875452084037cd0c4a8a41080127a21d214821000d74432429042000c74655db10840012eb0fb2e21080031d5db65c421010db9406cb88420239758794310840010fb0f31eca880028fa1263d95100051ec24c7b2a2000a6e8298f65440014db0531eca880021fe1d63d95100051fc22c7b2a2000a3c8458f65440014df04b1eca880029b20963d95100070e320c7b2a2000c5d7118f65440014bd07316ca880029760e62d95100062eb98e7b2a2000e1d4310f65440014bd07396ca880029760e72d95102cd3d400e5b2a2020a79801cb65440010fd0e196ca880021f61c32d95100051f42065b2a2000a3d840cb654403b4f501b8eca880028fa1331d95100051ec2663b2a202087e87cc365440010fb0f986ca8814e1fe1d30d95101043e43a61b2a2000a3f844c3654400147908986ca880028fa1030d95100051ec2061b2a202087e87c8365440010fb0f906ca8800297a0f20d95100052ec1e4
  | 5 => 0x28f61331d95200043f43c63b2a400087d878c7654800147d0918eca900028f61231d95200043f43863b2a400087d870c7654802b0fd0f986ca900021f61f30d952029c3fc3a61b2a401587c874c3654800147f08986ca900028f21130d95200051f42061b2a4000a3d840c365480014eb03baec2900029d60475d85200043fc2ae7b0a400387c855cf614800117f08b9ec2901562f21173d85200055b42663b0a400087e8714361480014eb02286c2900035a081759852029734100cb30a400387e86dd56148001ad041baac2900021fa1f65585200062e39ecab0a400087e8719561480018b8e632ac29014b1edc065585200062fb2ee6b0a4000c5c65dcd6148001b9041b9ac2900035a08175185200943ec3eca30a4000c5e73d9461480014eb03b28c290003179cc65185200053ac08ca30a4035c7970194614808dcd040328c29000317d9573185200062e32ae630a4000dc8205cc61480011ef0eb08c290002b520d611852000734106eca8a400087e869d95148001ad0413b2a2900029d60676545200063ac0ceca8a4000a5f835d951480394b906bb2a2900029be0976545200053bc0aeca8a4000a7b805d95148001ad0403b2a2900039a080765452000637908eca8a4000c7b201d951480018d8403b2a2900031e080765452000634100eca8a4000d68201c15148001cceca30a42900029b2195148520026363b2a290a4004e646154521480191dd0c38242900035a1407048520064f5430e090a4000cea861c12148001ad6ca38242900035a1947048520006b5a88e090a4000d69511c121480410f90cb8ca0900831d1857194120006b4102e3282400087f87d8650480018eae3b0ca0900d71b9d92194120005b4402432824015c6e76d96204802bad4e1b2c40900063b219718812013e7230ae31024000a6c865462048037ad4e0a8c40900d69ba1a50881200aeb5384a11024000a3e849cd65c400147b0939acb8800317dce73597100062eb98e6b2e2000e1d4310d65c40014bf06b92cb880029720d72597100053dc02e4b2e205ca78805c965c40014bd06392cb880029760c725971000636b90e4b2e200087e870c965c40010fb0e192cb880028fa1032597100051ec2064b2e2000a5f835c165c40014b906b82cb880029be09705971000536412e0b2e202ea77815c165c40010fd0f982cb880021f61f30597100b43fc3a60b2e205387c874c165c400147f08982cb880028f21130597100051f42060b2e2000a3d840c165c40010fd0f902cb880021f61f20597100052f41e40b2e2000a5d83c8165c40011bf06baac58800a3720d7558b100043ec36ea906201587e8759520c406b0f90eb2a41880039a08165483100043ec3cc7b2c200087f8758f658400147f08b1ecb080028f21163d96100051f420c7b2c2000a3d8418f6
  | 6 => 0x43ec3ec7b0ca016c5e73d8f61940018bee731ec32805b171cd63d86501043ec38c7b0ca000a3e8418f619400147b0831ec328003175cc63d86501053b408c7b0ca02087d87d8b61940014bd07b16c3280029760f62d86500ae37396c5b0ca000a5e8398b61940014bb07316c32812b1e9c262d86501053b408c5b0ca05ea7a8018b61940938f4e0316c328176dca0361986501043f43cc6b0ca000c5f7398d61940414ed0331ac3280821f21d63586500b62e39ac6b0ca000a3e8418d619400147b0831ac32800297a0f62586500052ec1ec4b0ca02087e8798961940014bd07312c3280029760e625865000637b94c4b0ca020a768198961940410f90eb12c3281669ea0062586500edb9406c2b0ca000a3e849cd619400147b0939ac32800317dce735865000537414e6b0ca000a6d829cd61940014eb0339ac3280029de0573586500062eb98e6b0ca000e1d4310d61940014bd07392c3280029760e725865000637b94e4b0ca000a75819c961940014ef02b92c3281669ea0072586501053cc00e4b0ca00087e870c961940010fb0e192c3280028fa1032586500051ec2064b0ca020a76810c961940014eb02192c3280028fa1331586500051ec2662b0ca02087e87cc161940010fb0f982c3280829da0730586500053ac0e60b0ca00087f874c161940410f90e982c3280028fe1130586500051e42260b0ca000a77814c161940414e902982c3280028fa1030586500051ec2060b0ca02087e87c8161940010fb0f902c32800297a0f20586500052ec1e40b0ca020a7681c8161940014eb03902c32808317d8573186501062eb0ae630ca021c5e605cc6194001ab4c0b98c3280831bd85721865010636b0ae430ca021c6e605c86194001ad4c0b90c3280025de1d611865022eb9382c230ca00097a809da21940018f5013b443280831bc8576886501063690aed10ca00387c805da21940018d840bb443280861fe197088650004afc1ae110ca01695c835c221940018f4c1bb2432805a57a0e7648650004aec1cec90ca000c6e629d921940012f5013b243280025ea0076486500063d300ec90ca02096c8758921940011ef0eb08c31007297a0e76546200052ec1ceca8c4000c6c729d951880014eb033b2a3100029ea0276546200053bc0aeca8c4027e662158551880591df0cb8443100025b61e2194220005b4c0443284400087d8798f65480010ff0eb1eca900028fe1163d95200051e422c7b2a4000a778158f65480014e902b1eca900028fa1063d95200051ec20c7b2a4000d68205c765480018bee739eca900028fa1073d95200051ec20e7b2a4000c5d731cf6548001c3a8621eca9000e1f20171d95200052f418e3b2a4000a5d831c7654802b4dd0438eca900029b60871d952017d3d400e3b2a4015a79801c7654800147d0998eca9
  | 7 => 0x3d84cc460544c78eae2988c0a88028fe1130181510051e42260302a200a3e840c0605440147b08180c0a88869da0430181510053ac0860302a200a5e83c8060544014bb07900c0a88029e61f20181510063cc3e40302a200e5a83c806054401cb307900c0a88029e60720181510073590e40302a221a768108060544014eb02100c0a88029e61c20181510073541040302a200e6a720806054401cd2e4100c0a88039ca0420181510053cc0840302a200e718108060544c5cd442100c0a898b9a08420181510051f424e6b2c4200a3d849cd65884018bee739acb10803175cc73596210070ea1886b2c4200a5f835c165884014b906b82cb108029be0970596210dd36412e0b2c4200c7b201c165884018f040382cb108871e44070596210043f43e60b2c420087d87cc165884010ff0e982cb108021f21d30596210051fc2260b2c4200a3c844c1658840147d08182cb108028f61030596210253b40860b2c4200a75810c165884434f501bacc1108829ea0075982210043fc2ae7304420387c855ce608840117f08b9cc1109562f21173982210053ac08a1304420387e87dd560884011bf06baac11080a3720d75582210146f43ee6b044200c5f75dcd60884018b8ebb9ac11080327dd3735822116e2fa8ee6b04422dc5d51dcd60884010ff0ab9ac11080e1f21573582210045fc22e6b0442558bc845cd60884018beea39ac110803171d473582210064fba0e6b044200c9c741cd60884410fd0e282c11080317dcc505822129e2e398a0b044204b6681dc95148401ad640382a290802dc60450d812101c3fc3aebb02423987f815d760484018f700baec09080e1fa1773d81210043ec2ee7b0242558be84dcf604840117b09b9ec09080e1fe1f51d81210043ec3ea3b02420787f8754760484370fb0ea8ec0908029e20151d81210063cba8a1b024200a798714360484018f30e286c0908029e60450d81210047dc3ac03024200a788558060484016e302280c0908131b5cb51181210053c402a23024200a758114060484015d304280c090802bc60450181210063cc38a03024246e6a821406048401cd304280c09091b9a9c8501812100739408a03024200a79811406048401ce302280c0908029c604501812128f35108a03024251e682114060484c327d09b9ec5280024f61373d8a50004bd406e7b14a00095d879cf6294001a3ce939ec5280039398a73d8a500b4afc3ae7b14a000d1e745cf6294001a3ae8b9ec5280039398973d8a500062f302e7b14a000d5a605cf629402b0fb0fb1ec52805b179cf63d8a500ad37416c7b14a016c5e7358f62940018dcc4b8ec528003569ce70d8a50006acb9ce1b14a060e6a629c3629402d8bce7b1ac5280561f21d6358a500b62e39ac6b14a015c6f76d8962940bf6d501b12c5280025ea0373d86501
  | 8 => 0xe39ac4a880347dd073589510068e3a0e6b12a200e4c621cd62544398b8e7b1ac4a886e1f21d63589510e62e39ac6b12a21ba6c8258d62544374dd0db12c4a880355dcf7158951006aa39ee2b12a267d6772dc562544cdcc8c5b8ac4a880356dcf7058951006ac39ee0b12a200e6862dc16254401ae6e3b82c4a88031e61b70589510063db0ee0b12a200d7361dc162544018d8c4382c4a880356dcc7058951006ac398e0b12a200e68621c16254401ae6e2382c4a88031ee1870589510063db18e0b12a200c79631c16254401ad6c4382c4a88031e98870589510063c310e0b12a200d68621c162544018d0c4382c4a88031ed847058951006b9b08e0b12a26493e84dcf605440127b09b9ec0a8802dc60420d8151004bac0ee7302a21cc5c73d8e605440147d0931cc0a88028f61263981510062eb9cc7302a200a798098e60544390ff0eb1cc0a8873179cd63981510062fb98c7302a200a5f8358a60544014b906b14c0a886f1b9c962981510053dc02c5302a200a5e8318a60544014bb06314c0a89975c5c760981510e4af43ee6b02a200d1f74dcd60544018bec3b9ac0a880355d8773581510043fc32e6b02a20093f845cd60544c927908b9ac0a88025be0973581510dcb6412e6b02a200977815cd60544012bd0e39ac0a880347dd073581510068e3a0e6b02a21b96e87dc96054401a9ee7b92c0a8803531cf725815100637b0ee4b02a200d6761dc96054401a9ee6392c0a8803531cc7258151006abb9ee2b02a200d5473dc56054401acee5b8ac0a8803591cb7158151006b4396c0b02a22ed7371d8160544018bee7302c0a8803171ce605815100637b94c0b02a200c6c7298160544390fb0fb18c0a8873179cf63181510051f424c6302a200a3d8498c60544010fb0e318c0a8803175cc63181510dc3ec3ec4302a200a7980d8860544014bf06b10c0a88029720d62181510053dc02c4302a200a5e8318860544014bb06310c0a88031b5c86218151265b8c0cc0302a20087f8758060544014bf06b00c0a88029720d601815100537c12c0302a200a6c8258060544012f70eb00c0a8802da20960181512d5b9c0ac0302a200a7986c806054401ad2e4100c0a88039ad8820181510073431040302a200b718108060544014f501b98c0a880317dce73181510051f420e6302a200a3d841cc60544018bae6398c0a88029ba08731815100536c10e6302a207a75811cc60544014f500398c0a88029ee0143181510053c40286302a200e1d4310c60544014f501b90c0a880297a0c72181510052ec18e4302a200c6d721c8605440f4eb02390c0a88029ea0072181510053d40664302a200a7980cc860544014f700990c0a88029e20132181510043f43864302a20087d870c8605440147d08190c0a88028f61032181510051f42662302a200a
  | 9 => 0xc0004a533c00023c000000154370000f02000f50764cc90680000000002500002800fc1cca70000000000000d2c000000000f9017000000000000030ec7e0000000000003c0000000000000000000000000000cd8e1c646000000000000efc9f4ea06d0000000000d587263b0000aa8ba4000000c3000009405c7120006040000013946000000000000006e12a8000dc00160003d06a0001204ae0ec40e528200001600400200000800400c00000000200a00600000200600400201200000c01401801a01201000000e00000200600800000a00400400000600002001600000200600000200000e01200600000000a00200000200a00400400200201401200000000000200000000200000c00200200000e01000600000400a01000200000800400401001200e00400e00400001400201000200600e00600200400a00400200000200201400000000600000401000200400000800400400200200a00600001e00200000600400000600600001400000200800600200c00200000800a00000400000000000c00000000400400001400800e00200000200400000c00800801001600c00000400a00000600000600400000200200200200000200400800000000802a00200c00600200800600000800000800600001800600400000000800000200200400401a00000000200000400c00201400e00c00200000600200002800800000200000000000002a00800400e01000600400400400600400000000000000000000e00c03600e00201000000200c00200000400000000e00400e00000000001000801a00000400000002800400000000000400200400000600000000e00000200600002400000000400001000401800a00800000001400000000e00000400000c00400c01400000000400200203601400800a00000802600000000201202600e00400000200e00e00002400800200000200000200000400400601400600800200201201001800400e00000000e01600200600000c00200001400200000400000a00200400600200200000600600a00200600000200000200000400c01200400800000200000400200000200200003e00800200200a00200601200a00000e01800000002400000000400600802a00000000000c00800000000c00c00000e00801000600000000000600200400a01800e00000200001600000000e01200200200800000600000000a00600000400200200000400401e0020000000000080040021b87d87d8f62544398bce7b1ec4a8873171cd63d8951024bb40ce1b12a20b975819c362544012bf06b86c4a88725720d70d89510e4af43ee6b12a200d1f74dcd6254401c98c5b9ac4a880317d877358951006abb0ee6b12a20093f845cd62544c927908b9ac4a88025de057358951004bdc02e6b12a200978805cd62544012bd
  | 10 => 0x6c40012f0f20dcc0008a44f01110a85c80002013b45e01d4000000000d2516c0000001440002c8b50000870db4c1c538db8214f7a000da044c0000000010391366103c46d452e8f4904a385e60127ec5cc0000008d050e3ed1684ecaec06000000000057a0000000000002a4000d840000011e80ca000000000000000000000000d9c000114010e1924d0ad0c40840005d0631278204b640006dc000e3c000b9110c00000000001e0000012ba31edd8000000b38a60000000000b84f4c46012ce6902038ce0c0983a0f04000000e248e0b66074c540013181492dd32e5ae74e5a2001235090ff8c0870e000000000000000c0c00000135e3f259ede0000000de8000000ed800000002c7d86880000006d817e3786b4320ea82580003bca5c3869b8f180007bc908514000bbc4252a0b0aed4b60000cfc00000050c000000578df11ac4780591f531f241184c43032000000ed000014c9cc0000000012980000004e889849e000bc80d91cc00126d2fc000b3c000000000000000a9c2bca78ba8614a971113c0ca802527001c3f4309284ec27d444090662e88c62ac88a0095122866ab5851c00000108000045d0b4840064ea40005db059128728c800010e000115c6f074c54cd7106ac9487852c6984980a0000a20e740000000011b800048e1a0820808674da4b627140006640007840000000000000010d8d080000002e0978f7c00000000021000085800029cf78000001199308694a1c000348d640003d800137928000031c0010087e8188000d8910000000064509800032410092927c0500003100dc58061cf80fdd19cb48000000000a68001254a248100011243440001c00000009ec0000012b070ca8c0000001d0000000001374bdcefa5900010600000000000002e80006c8001212854000554004000a2e4b800112b3700000012f44d8b06000e00000000260cf8bf4568000d1c16800048d238828558f0c384284c7abec000ccc000fe00011dcaf4be4dae9a8520fc085cab80393a400122d25a0302293991b4a0404f074ef89f125f04ca647b48f908832cb0449c02907d0da0acd38a9433417b1c92c0998b787ac0008b4e4c000000c2600000000000068a000000066164000c60000804f54d8212000077cbe0968000b727a9348dfc608fb45fc0006a40009d020ce940c80004fa000001288000830c2c000000000c70954df4774000000000000000430dc538cb00000ff4e300000002449d885e6c2000184e021b117c00118e5404105010300002393a11e0a800000000000012448f0cb90943dcfbc178ebc001266f68af80000000007f82fc920bb000067c000000000000ad40000012620000008c004c0a6e5c0005761b87d01a4000eb2a882dad000f400000100c000cc06192e0585076960a992749b49c80000000002ba5a
  | 11 => 0xc7c0000000003f676800000000000000000019cee0adc23126000000071e2ec000001044000000000d9e0000007c40880011506f80c6414b8c864c144ccd60000000bc4a3cfed014b2cd4c7086923b679d0d4afd224001328270000789208913050c4f2ca0010d13545a4a312d403cebe0010a00000000c45ec000000f8d2c88810d6f2c730e4079815c0000f11920f91e4c0486810821cd1ac50000d111a84bcedc834000000d5400040931ca50c3c000b20818000000bcc48471c27400057200000000000000050a000000000b543610c8000d80532e78eb92a4a10000a75104eccce90cc240000f74668902c632500000000004a800013104257cc440008ccbc000000118905c6800012912bca2cc2800101c01a398ac85fece51d5300d7c472534444b25390da89741d8f6c7022c40000bc000f090108882ac6725b800099c83689c0010700008840e80e0ca0a3272266000000063c0006f62645c4000000000cb06b8000000000000000000000000754e88ced072fb0f24f00418354000000000000420000000000000b8930453ce760010f8ad80005704ae160d780000690f00008240005b4000ef6000000000000598000464bd000000121c3386c600118ccc40000480004e4d4000125c000000a180000003b482d1902dcc5293438913cce0d44a1e000f440000002b094818c000df8000f3c000000794000000000d1e25cd48f94471310000f1c958000000000700656fd04e0a493809a41c4b5c020b803a867078c67e66d1a4000ee80005e40000009b04b10c13653888ed09c0001051090280004dc26b20a50805448a000000530d8c1e400008c5b0248000000000000ad2000984c6a0011790540c00002f4134b76000000000f14000acceb09a01241bc000000001264000000a4c0012e87400000180004f4000000000ca4944000000b740000008d40000000012b86f5000b34f52000f8800040ee733c83150fd06c00000000000072134c2be0004013a80002f8000000380000c6464c3f08a86353b80001180000011f0000aaca84aa4000ae46510ec00068cf700000000007f13340004509c0001154000fe42cca7c174080000f28a143047e03d47780012ac000000000000938b701f5165352bb8bd4000000000000ffcfb8000000000aa0e54e84c40254c2a8ae9d439c0010400006cc000000dbc076000d740000000000000010b00001fc0000000000000003e85c6000000000000c6c0013507709ac0003ace10f5c0000000000000002c009200000000000000000000045400040c000fa474800000080000000000000108cc1000000000000000000112c518000001024001248000d04364e28000488000db00907593c43a332484c00035800012800013cb4400000000000083929400000063895c80c000000c99114
  | 12 => 0x600046800000027c0000000005880009809911582f11ec6c01807dc0000000000004a00d07240004c45f426d1949165f10180006242b4ef0490e2c5040000000009fc0000000000009e91440000008b84c0000c20000ef4000000915332678138d68001230294000c74000ab4001362000eec0000000013689005444b4cdc000000c9000033c000000000000140b7c0000003e00433600013307a44382a8524480bf90dc15883c0011d8b984b207ce8cfc44951f60007900006bc000da2000000b687c0000268564602cf00006071f200000000097cd7eb94b30b1537c4d40004340a536c0000000000006e45d6738000000000000000000000000780c49206e14000ee426e000000000b409e40000004fe1ac00073c00000134400086c11c0000006b0d1435c8140008b052ae612b4718ec09dca292f8000000e7c0006fa000fa0000b1800102ef10000a08374c8c3907b02d0c384c859c000000a44000b9c000dd4ddd30c00000062c00000000062800000093c000000ae8a551f85c0fa8000a910645d8000ec91b0f4e9f80013b12100008e921846ef38af0a34941005383120000000b4a6fe000000044014000000000dec65ede4000b4691cb02000e6c0000008aca92350000cd0d350460000000013ad034a580005e80011c4288000d902991a00000001c82d424c72c000c871401ec000000988704e500004fc000000e48000d200008b3216b2934e9246540000000000011d07b80000003f9138000040000752000001126000000f3400139cfac000550cd4000000290000000d3c2e400019800000000121428c0006a80000b4000e08dd036c6427c87606904d019400000000000000000043c1b4a2292ca6c00123d03e0000005f8000c788d80005caf98d1855d384d6d1600013380000010f49e000000103c9188500000000000003e6000000cf4911180a409c5134fc8e6458cad120c528ac529c8a06ac3945dd2200000013400013148c4894daa0009bc0012cc0000000000008fc000e587f5358eb61e09647a022c8443c842ec18e350e4f582a1130ad713a0b000098c0003192ec208aa2dfe2240000007fc750000e9d24600000046cb0c474000000000000c4c000000bfc40a9947452426fc000000f64000000000000000bd8000e8065cd5c0006589708c800000000000010c890f072770a4eb41e92b71bc0000000002b84cf272c8e81c0000000012590bc00000000030069d3b6000b4ce050783300006ec4ac3e43411c075e00cabc34c00056cd0d3b2000734000000000000000dc80b8e7000102cb6cc9cf48000b0800075ccb4220e900005a019000000015047d28cbf05bc2350e862000114c00000000000000042c000f30000000fe85ea00006c000fcc37c000001321048bb4ba0b0e000d50000000d312c490cf406407cc2780
  | 13 => 0x11184480005d5170c680000012d8848000cac5ee000c24eacc000d43b8574e2042894d14856000076cbac0004f800000000041c0000000003e33bc0012000000cc000be80008dc0ed31a000ab07620004580a80012c6000fd8ac10664a207911c75a68487cc5c00000000009c8bcb11174000f9ce44f60dac00000075636800030c000ff01a8436e3806a008000d945aa32807000051060c000e983fc5492e4682930fd400000040400000000017c000000a0cf84aa65a80003cc7100000000008e416c2d896c7e40000001f0d980000000010845951fc3a40010b80000000340000001dd2d0c340000002180008604ca6488740000001f8000c58000000000000000000c84cbd32c000d28000000000000b1c0000000000006e800000000000000135d26852
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x8c995118807130d20218168674027800d9f970000094e0f0000195e800000001b0000179e088000000000129a298000110022101ac1002913a400000005a1002b890c0000001d268b2a121a80000000000000000000000000000028800024800000000000000e8000001c800a99800000000300282700001600000080108200002628c01c0016aa80000000190000000022a09f189b818000180007a58b86959d8400294fac000504aac00a0000000000002a4014800000000000000000000000000000230002a3c000000c86252380039400004080c041014000400000800000430102004040c000000040800040404040800040144e9718b7358951007031d0621cd625440146a97188705895100712dcc621c16254401c487318870589510051a249631c1625440145993188705895100712a4c621c16254401c49931887058951004176637318e605440184d835c86218151006585c9810806054401a6062604201815100417e61731cc6054401855815cc7318151006135cd821cc60544016189050c43181510061360d721c86054401865815c8721815100686a1283c8060544c5a6021604201815100698a0981080605440105f985cc735962128d1aa5b201c1514844386572604501812128e988858114060484a3a6021604501812100698a09811406048401a6182604501812100698e49811406048401a60926045018121006989c9811406048401c0e7498a73d8a500051365e625cf629400105f985cc63d86500061360f72989619400184f7360a735865000417e61731cd619400184d83dca72586500061a98a809d9219400186872a02765462000417e61731cf6548001561910817518520006980818119461480015c19108173185200059864420dd9514800156191082765452000558644201d9514800166191080765452000519644201d9514800147191080765452000718a44201d9514800146991080765452000718644201d9514800146191080765452000558644501c121480014689654470485203461a9d880486504800186a70219518812000417e61731cd65c400105f985cc73d96100051aa43729cb658400186a8708365482100051c64465dd9208400186a8718b65482100059864462d9520840018686221d51482103149aa5a80d4462440a3c60101d8625451000706190631c15144001c4b6318870545100071218c621c151440018686221d51481100055825d5148520440099608754521481100de98219514852044009c607654521481103161aa0062dd6104400187070604505881000698081811416204001a6290604505881010e98641811416204001a6370604505881000698604701416204001661919c162940101051ca4085dd91004001c5376dce504401000718ddb7294110040c5962871ca5044010
  | 1 => 0x2b
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xd00008040000d0265193188705895128d0c34e49302280c090802861a708181194614800183143b22316ca9042000c18218975452148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x4b
  | 6 => 0x4c
  | 7 => 0x4e
  | 8 => 0x124c
  | 9 => 0x94b
  | 10 => 0x94c
  | 11 => 0x94e
  | 12 => 0x124b
  | 13 => 0x124e
  | 14 => 0x138b
  | 15 => 0x138c
  | 16 => 0x138e
  | 17 => 0x98c
  | 18 => 0x98e
  | 19 => 0x128c
  | 20 => 0x128e
  | 21 => 0x134b
  | 22 => 0x134c
  | 23 => 0xb0c
  | 24 => 0xb0e
  | 25 => 0x140c
  | 26 => 0x140e
  | 27 => 0xbcb
  | 28 => 0xbcc
  | 29 => 0x94056
  | 30 => 0x95254
  | 31 => 0x94054
  | 32 => 0x134a
  | 33 => 0x14a
  | 34 => 0x134054
  | 35 => 0x124956
  | 36 => 0x124954
  | 37 => 0x98956
  | 38 => 0x98954
  | 39 => 0x128a
  | 40 => 0x128956
  | 41 => 0x128954
  | 42 => 0x134954
  | 43 => 0xbc954
  | 44 => 0x8a
  | 45 => 0x12ca
  | 46 => 0x139256
  | 47 => 0x99256
  | 48 => 0x129256
  | 49 => 0x135254
  | 50 => 0xbd254
  | 51 => 0x135394
  | 52 => 0x128996
  | 53 => 0x14b
  | 54 => 0x134994
  | 55 => 0x150e
  | 56 => 0xb0996
  | 57 => 0x19cb
  | 58 => 0xbc994
  | 59 => 0x135294
  | 60 => 0x141296
  | 61 => 0xbd294
  | 62 => 0x134b14
  | 63 => 0x135414
  | 64 => 0x8e
  | 65 => 0xbcb14
  | 66 => 0x154e
  | 67 => 0x1349405c
  | 68 => 0x5396
  | 69 => 0x95256
  | 70 => 0x14053
  | 71 => 0x4954
  | 72 => 0x5554
  | 73 => 0x8056
  | 74 => 0x150056
  | 75 => 0x124056
  | 76 => 0x4956
  | 77 => 0x5516
  | 78 => 0x125396
  | 79 => 0x94154
  | 80 => 0xca
  | 81 => 0x14092
  | 82 => 0x15393
  | 83 => 0x14c
  | 84 => 0x19cc
  | 85 => 0x5
  | 86 => 0xcd
  | 87 => 0x95354
  | 88 => 0x95294
  | 89 => 0x95296
  | 90 => 0x5256
  | 91 => 0x20e
  | 92 => 0x138096
  | 93 => 0x138056
  | 94 => 0x125296
  | 95 => 0x98096
  | 96 => 0x15353
  | 97 => 0x134d
  | 98 => 0x8152
  | 99 => 0xb4e
  | 100 => 0xbcd
  | 101 => 0x138956
  | 102 => 0x19cbd3
  | 103 => 0x155416
  | 104 => 0x4153
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 47
  | 7 => 679
  | 6 => 1787
  | 5 => 1267
  | 4 => 89
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
  | 8 => packedAt gbK8 (1369+((h/21+packedAt gbK8 (1222+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (28500+((h/307+packedAt gbK7 (25123+(h % 307)*11) 11) % 1470)*11) 11
  | 6 => packedAt gbK6 (94752+((h/748+packedAt gbK6 (85776+(h % 748)*12) 12) % 2964)*12) 12
  | 5 => packedAt gbK5 (80645+((h/491+packedAt gbK5 (74753+(h % 491)*12) 12) % 2351)*12) 12
  | 4 => packedAt gbK4 (6494+((h/33+packedAt gbK4 (6230+(h % 33)*8) 8) % 213)*8) 8
  | 3 => packedAt gbK3 (409+((h/1+packedAt gbK3 (405+(h % 1)*4) 4) % 10)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffe07ff80781fffc0fffc03fd19f3e7dc1f3f3
  | 1 => 0xfff80fffffe07fff03fffffee68d18e7e3c7f
  | 2 => 0xf07fff0007fff83fffc1ffc03070e1f387cf9c
  | 3 => 0x7ffffff800003ffffe00003f80fe03f80fe0
  | 4 => 0x7fffffffffffc0000000003fff0003fff000
  | 5 => 0xff80000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10a00b2841804a4c0252409580830634c0d1b1
  | 1 => 0xd0280530a2204911024952a062850881a2446
  | 2 => 0xa055550084d59026ac812a80b050a153054a98
  | 3 => 0x8479e69dd010c23bcf3803033b80fa03e80f60
  | 4 => 0x87e78e6e779e70086100c0c3dfd0003f7b000
  | 5 => 0xce10400700610403082030303f7efdec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeae8ece8e8c8eeeaeae8ece8e8c8eeeaeae8ece8e8c8eeeaeae8ece8e8c8eeeaeae8ece8e8c8eeeaeae8ece8e8c8eeeaeae8ece8e8c8eeeaeae8ece8e8c8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36707
namespace PEqualNP.Outside.L_meta_36707
open PEqualNP.Outside.L_meta_36707.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 1 := bs0_2_0
theorem alls0 : ∀ k ≤ 2, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 3 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 10 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 13 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
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
theorem bs4_2_0 : Interval s4Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 10 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_64 : Interval s4Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_96 : Interval s4Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 112 := (concat (concat bs4_3_0 bs4_3_32) (concat bs4_3_64 bs4_3_96))
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
theorem bs4_4_448 : Interval s4Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_512 : Interval s4Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_544 : Interval s4Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_608 : Interval s4Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_640 : Interval s4Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_704 : Interval s4Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_736 : Interval s4Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_800 : Interval s4Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_832 : Interval s4Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_864 : Interval s4Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_896 : Interval s4Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_928 : Interval s4Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_960 : Interval s4Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_992 : Interval s4Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1024 : Interval s4Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1056 : Interval s4Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1088 : Interval s4Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1120 : Interval s4Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1152 : Interval s4Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1184 : Interval s4Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1216 : Interval s4Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1248 : Interval s4Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1280 : Interval s4Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1312 : Interval s4Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1344 : Interval s4Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1345 := (concat (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128))) (concat (concat bs4_4_160 bs4_4_192) (concat bs4_4_224 (concat bs4_4_256 bs4_4_288)))) (concat (concat (concat bs4_4_320 bs4_4_352) (concat bs4_4_384 (concat bs4_4_416 bs4_4_448))) (concat (concat bs4_4_480 (concat bs4_4_512 bs4_4_544)) (concat bs4_4_576 (concat bs4_4_608 bs4_4_640))))) (concat (concat (concat (concat bs4_4_672 bs4_4_704) (concat bs4_4_736 (concat bs4_4_768 bs4_4_800))) (concat (concat bs4_4_832 (concat bs4_4_864 bs4_4_896)) (concat bs4_4_928 (concat bs4_4_960 bs4_4_992)))) (concat (concat (concat bs4_4_1024 bs4_4_1056) (concat bs4_4_1088 (concat bs4_4_1120 bs4_4_1152))) (concat (concat bs4_4_1184 (concat bs4_4_1216 bs4_4_1248)) (concat bs4_4_1280 (concat bs4_4_1312 bs4_4_1344))))))
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
theorem bs4_5_608 : Interval s4Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_640 : Interval s4Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_704 : Interval s4Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_736 : Interval s4Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_800 : Interval s4Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_832 : Interval s4Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_864 : Interval s4Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_896 : Interval s4Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_928 : Interval s4Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_960 : Interval s4Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_992 : Interval s4Atlas 5 992 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1017 := (concat (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 bs4_5_96)) (concat (concat bs4_5_128 bs4_5_160) (concat bs4_5_192 bs4_5_224))) (concat (concat (concat bs4_5_256 bs4_5_288) (concat bs4_5_320 bs4_5_352)) (concat (concat bs4_5_384 bs4_5_416) (concat bs4_5_448 bs4_5_480)))) (concat (concat (concat (concat bs4_5_512 bs4_5_544) (concat bs4_5_576 bs4_5_608)) (concat (concat bs4_5_640 bs4_5_672) (concat bs4_5_704 bs4_5_736))) (concat (concat (concat bs4_5_768 bs4_5_800) (concat bs4_5_832 bs4_5_864)) (concat (concat bs4_5_896 bs4_5_928) (concat bs4_5_960 bs4_5_992)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 48 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_3_0 : Interval s5Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 21 := bs5_3_0
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
theorem bs5_4_544 : Interval s5Atlas 4 544 7 := block_range (n:=7) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 551 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96)) (concat (concat bs5_4_128 bs5_4_160) (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)))) (concat (concat (concat bs5_4_288 bs5_4_320) (concat bs5_4_352 bs5_4_384)) (concat (concat bs5_4_416 bs5_4_448) (concat bs5_4_480 (concat bs5_4_512 bs5_4_544)))))
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
theorem bs5_5_640 : Interval s5Atlas 5 640 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 666 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 (concat bs5_5_512 bs5_5_544)) (concat bs5_5_576 (concat bs5_5_608 bs5_5_640)))))
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
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 89 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_1248 : Interval gbAtlas 5 1248 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1267 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248))))))
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
theorem bgb_6_1760 : Interval gbAtlas 6 1760 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1787 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760))))))
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
theorem bgb_7_672 : Interval gbAtlas 7 672 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 679 := (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 (concat bgb_7_192 bgb_7_224)) (concat bgb_7_256 (concat bgb_7_288 bgb_7_320)))) (concat (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 (concat bgb_7_448 bgb_7_480))) (concat (concat bgb_7_512 (concat bgb_7_544 bgb_7_576)) (concat bgb_7_608 (concat bgb_7_640 bgb_7_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 47 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 3 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeae8ece8e8c8eeeaeae8ece8e8c8eeeaeae8ece8e8c8eeeaeae8ece8e8c8eeeaeae8ece8e8c8eeeaeae8ece8e8c8eeeaeae8ece8e8c8eeeaeae8ece8e8c8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372968 * 2 ^ 32 + 3974686920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36707.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,4]⟩,⟨.and,[3,4]⟩,⟨.and,[2,5]⟩,⟨.or,[1,8]⟩,⟨.or,[2,5]⟩,⟨.or,[2,7]⟩,⟨.and,[6,10]⟩,⟨.and,[1,11]⟩,⟨.or,[0,13]⟩,⟨.or,[9,12]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3974686920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3974686920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36707

open PEqualNP.Outside.L_meta_36707 in
theorem PEqualNP.Outside.L_meta_36707 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3974686920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3974686920) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
