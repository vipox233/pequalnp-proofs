import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36637.Model
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


end PEqualNP.Outside.L_meta_36637.Model

namespace PEqualNP.Outside.L_meta_36637
open PEqualNP.Outside.L_meta_36637.Model
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

def SBf (j : Nat) : Nat := [7, 3, 7, 7, 6, 6].getD j 0

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

end PEqualNP.Outside.L_meta_36637

namespace PEqualNP.Outside.L_meta_36637
open PEqualNP.Outside.L_meta_36637.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x90a0099c247439e2a0109f56116204a4412d4ca4a171c040165e8d38b14b83001ea0d804400c00480002a106480c0600d0d000e48002ee00000030e800080ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20ee20fd20fc20ec20ff10fe10f610fd10fc10f410
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xf05d36184ee3f228b40012478d4f200448002a5b46074040924a3400001206490750a0ac00130e0a41c6336968002a2707c003e0293c006f139883633101cc3c533815d0476161d1144400088004d12a10bc552a19cf8003ea38141700000d4811183c304703820b00b2e0bcd2861e9e800510320c22000010c4c7106801004c3d964646e42900787221128fe0c018680034258006e0417004cc4100220ca87000d800000000000001c918c81000148628b0b1a0ac21359405060180e0767e2f800740c0701000007010004030501031e060005110a00113201030100310e000600042b0c0c0002070b020204000700040203b7296876d52d0edca521db54a43cea18875e53d0abaa7a15794e42aea9c85ad4210a7ca9994f553329f2a4653d548cb9a641957d4d41ae29a836f52506d8a4a0ded4141bc282835e53106baa620db94841b6a90833f544c678a898dbd4931b6292637b504c6f0a098cf950319eaa0636e520c6daa418cfd51219e2a2435f53486b8a690ded4121bc282433e540867aa810d794c21aea98435e53d02baa7a05b94b40b6a96817651d02eaa3a04f94240afa9a815c53502dea4a05b14940bba8a8174515027ca0206e940409f2a6613d54cc2dca5985b54b30bb28e617551cc2bca1186790230ce204613f544c278a8985bd4930b62926177514c2e8a2985794030ed280619e400c33880184f953209eaa6415e53c82baa7905d94720baa8e416e508835c81106b10220e718441cc308827ea8904f15120afa9a415c53482eea2905d14520b728041ea500835c80106b10020e718041cc300827ca9884f55310af29e215d53c42dca5885b54b10dc20621d830c43d041885d94210db20421b440843ac6108750c210f310421e4208427ea8884f15110afa9a215c53442dea4885b14910dc20021d830043d040085d94010f928021f3400436c80086d10010f820021b040043e66008758c010ea18021f030043a060087cc8010f310021e420043e040087808010
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x72480218041638c01401e10a600222692000407c388400c020b498f40042e262d0010ac98240042b264cc010b898b30042d2608c010e41023004392400c010e410030042b264c8010b498f20042e26088010e810220043c03088010e890020043a04008010f08c020043c03008010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 144
  | 3 => 19
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
  | 4 => packedAt s0K4 (4272+((h/48+packedAt s0K4 (3888+(h % 48)*8) 8) % 173)*9) 9
  | 3 => packedAt s0K3 (752+((h/6+packedAt s0K3 (722+(h % 6)*5) 5) % 23)*6) 6
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffc07fffffffffffffe03ffffffffff87fff
  | 3 => 0x1fffff803fe01ff00fffffc07f01fc07ff98c7
  | 4 => 0xe0ffffffc0001ffff00fffff8001fff80fe0f8
  | 5 => 0xffffffffffe000000ffffffffe00000fff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x8412c092492145112122a2c58b522d4a93ab5b
  | 2 => 0x825742492528a2a4a45502ad5a556952855ad
  | 3 => 0xb04995762394d348ec89f560663198c7cd98c6
  | 4 => 0x1d8e26473b1b1c8c88ee79b340c1e3e18ee0f0
  | 5 => 0xdef038783c1c1f0f0f0f9e3c78f903060f7e00
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000ccc0c0c0c0c0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36637
namespace PEqualNP.Outside.L_meta_36637
open PEqualNP.Outside.L_meta_36637.Model
def s1K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (i*4) 4
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (5+((h/1+packedAt s1K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffdfc7fff87ffe3f
  | 4 => 0x6bf878ff8783cc
  | 5 => 0x73ff80fff803f0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffff8041102888a8d5
  | 3 => 0x20b2245455522a
  | 4 => 0x1517459d461b4c
  | 5 => 0xe2476e66463b0
  | _ => 0
def s1Atlas : Atlas := ⟨2,rawDecor 57 s1Pos s1Neg, 0xaaaaaa00aa00aa00aaaaaa00aa00aa00aaaaaa00aa00aa00aaaaaa00aa00aa00aaaaaa00aa00aa00aaaaaa00aa00aa00aaaaaa00aa00aa00aaaaaa00aa00aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36637
namespace PEqualNP.Outside.L_meta_36637
open PEqualNP.Outside.L_meta_36637.Model
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
end PEqualNP.Outside.L_meta_36637
namespace PEqualNP.Outside.L_meta_36637
open PEqualNP.Outside.L_meta_36637.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x15a51a440001000ba8003021b0c800002498503122ce212600aa352507813400000007c3800058022309cc8000015003c74702480080500000040401007043100043ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x171095169c880e1aac1985802900089c2c91862600030022280012a5ab8f022980002b238b28808d000020a00900068001249804219f190285110b962d1300159e22aa1a23142d8a1d1f97800192240c849da78d870a8009a693802700189b9000078eaa948f80038c21251e80001b0305000170d0010009080011d0040e820a0088004001000420102b7a92876c5250f3a8621d7d4d42ae29a853f544ca78a8995b94b41b6a96835f53506b8a6a0dbd4941b6292837b50506f0a0a0d794c41aea98836e52cc6daa598cfd51319e2a2636f524c6d8a498ded4131bc282633e540c67aa818cf952219eaa4435e53886baa710eb95221d6aa443ce538879aa710db94621b6a84436e51087cca210db54021af29e815d53d02bca7205754e40b7294816d52902dca4205b548409f2a6613d54cc27ca9184f55230b7294616d528c2dca4185b54830b728e416d528827ea8904f15120afa9a415c53482eea2905d14520d7aa241ac544839ea6907314d20f3a8a416c51483c8a2905914520f5a82416e52082dea5885b14b10b7294216d52843c843084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa4087908410
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2084ca06e00000a31894310f0e5494e21c315053483275414520c915051483475314520d114c51482656508410
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (788+((h/14+packedAt s3K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s3K4 (2694+((h/30+packedAt s3K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s3K3 (312+((h/2+packedAt s3K3 (304+(h % 2)*4) 4) % 16)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xff81fff81fffffe07fffff03ff03fffe7f8e3f
  | 1 => 0x3fffffffffffffff81f01fffffffffff88ffff
  | 2 => 0x3ffe03ffe03f81fffe001ffc1ffc1f01f0f3cc
  | 4 => 0xc00003ffffc001ffffffe0001fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffe0000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x84a42888c48928601652a52125213954338615
  | 1 => 0x110851110912408580a40a464a4642a88838ea
  | 2 => 0xa6149aa243a42b6aaa0a93a913a91c0d70d34c
  | 4 => 0x3459634492074db34d3cc0c21cf38831dd03b0
  | 5 => 0x386183871c3871dc71cf1cf380c210c1eeec00
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeac8c8c8c88888eaeac8c8c8c88888eaeac8c8c8c88888eaeac8c8c8c88888eaeac8c8c8c88888eaeac8c8c8c88888eaeac8c8c8c88888eaeac8c8c8c88888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36637
namespace PEqualNP.Outside.L_meta_36637
open PEqualNP.Outside.L_meta_36637.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x51000100c70940342562500bf43bd43be42bc42be41bc41ee21ec21bf40bd40ef20ed20
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x21a096292871d531063aa7a05914520
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
  | 3 => packedAt s4K3 (111+((h/1+packedAt s4K3 (108+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7ffc1ffffffff03ffffc0ff83fffffe7e31ff
  | 1 => 0xfffffe07f03ffffc1e07fffffc1e07ff93fe4f
  | 2 => 0xf81ffff8003f07ffe007ff07ffe00781e3cf8c
  | 3 => 0x1fffffffc007fffff80007fffff801fc0ff0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x9044444122084100a4494848812294a4261095
  | 1 => 0x218888324452822c0a8291932414215890e64a
  | 2 => 0x52d51490eaa44d556144ea45cb40560d634b8c
  | 3 => 0x651a21248c06969a5390308672996011d80d60
  | 5 => 0x861c39c70f38e7e39de73ce063118461ffb000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeac8eac8ea88ea88eac8eac8ea88ea88eac8eac8ea88ea88eac8eac8ea88ea88eac8eac8ea88ea88eac8eac8ea88ea88eac8eac8ea88ea88eac8eac8ea88ea88, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36637
namespace PEqualNP.Outside.L_meta_36637
open PEqualNP.Outside.L_meta_36637.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xe45010000409018a0189608007bf43bd43be42bc42be41bc41ee21ec21bf40bd40ef20ed20
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x3280096292871d531063aa7a05914520
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
  | 4 => packedAt s5K4 (212+((h/4+packedAt s5K4 (192+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s5K3 (111+((h/1+packedAt s5K3 (108+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7ffc1ffffffff03ffffc0ff83fffffe7e31ff
  | 1 => 0xfffffe07f03ffffc1e07fffffc1e07ff93fe4f
  | 2 => 0xf81ffff8003f07ffe007ff07ffe00781e3cf8c
  | 3 => 0x1fffffffc007fffff80007fffff801fc0ff0
  | 4 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x9044444122084100a4494848812294a4261095
  | 1 => 0x218888324452822c0a8291932414215890e64a
  | 2 => 0x52d51490eaa44d556144ea45cb40560d634b8c
  | 3 => 0x651a21248c06969a5390308672996011d80d60
  | 4 => 0x861c39c70f38e7e39de73ce063118461ffb000
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xeac8ea88eac8ea88eac8ea88eac8ea88eac8ea88eac8ea88eac8ea88eac8ea88eac8ea88eac8ea88eac8ea88eac8ea88eac8ea88eac8ea88eac8ea88eac8ea88, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36637
namespace PEqualNP.Outside.L_meta_36637
open PEqualNP.Outside.L_meta_36637.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x202c0031c8001c800121e2648000341c0163d99080000010edc9286b187430a225d629be1156eda7740f126d115283e09f80012a7d4011a94e715c0230001951352c00a0002690601c0020004f01020848b3a00001000c380400001fe54007f55001fc54007fd0c07fe43007f50c07fc43007fd0805fe42007f50805fc4201ffcc805fe32007f4c805fc32007fd0401fe41007f50401fc4101ffcc401fe31007f4c407fc31017fc8401fe21007b88401fd21017f08401ec21007fd0003fe40007f50003fc4001ffcc003fe30007f4c003fc30017fc8001ef2000ff88001fd20007b48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x824001ff0c12000ffe409000bfb2048003ff1024001fb8812000ff84090007ec2048003fc1024001ff8412000ff82090003ef6448001f73224000fb59120007d8c890003ee5448001f6aa24000fb15120007dec690027ee6348001f6b1a4009fb18d20007de8690027ee4348001f6a1a4009fb10d20007dec290003ee6148001f6b0a4000fb18520005d8c290003ef4148001f720a4000fb50520007d88290027ef3148001f718a4000fb4c52004fd86290007ef604800377b024002fad812000fde8090007ee4048003f6a024001fb1012000fde6090007ee3048003f69824001fb0c12000fdc2090007ec1048001ffb262000bfd9310007fcc98801afe64c4001feb262000bf59310007f8c98801afc64c4001ff2a62000ff55310007f8a988003ff63c40017fb1e2008ff98f1001dfcc788003fd63c40017eb1e2008ff18f1001df8c788003ff43c4011ff21e2000ff50f10047f88788003ff62c40017fb162000fbd8b10005dec58801ffe62c40057f3162000ff58b10005fac58801ffc62c40057e3162000fb18b10015d8c588003ff42c400fff2162000ff50b1003ff88588023ff32c400fff1962000ff4cb1003ff86588006fe61c4001ffa0e2000ff90710007fa8388003fc41c4011ff98e2000ff8c710007ec6388003fd31c4001fa98e2008ff0c71003ffe4388003fe21c4001f710e2000ff4871003ff84388003ec21c40037eb062001ffd031000ffc8188007fd40c4003fe2062001ffcc31000ffc6188007fd30c4003fe1862001ffc831000fde4188007fe20c4003fe9062001fb4831000ff84188007fe10c4003fb0862001fe8431000ff82188007f410c4001ffb222000bfd91100077ec888002bf6444001ff3222006bf99110007fac888002fd6444001fe3222006bf1911000778c888002bc6444001ff2a22000ff55110007f8a888003ff63440017fb1a2000f7d8d10005bec688017fe63440077f31a2000ff58d10005fac688017fc63440077e31a2000f718d1001db8c688003ff434400bff21a2000ff50d1002ff88688003ff62440017fb122000fbd8910005dec488013fe62440057f3122000ff58910005fac488013fc62440057e3122000fb18910015d8c488003ff4244009ff2122000ff50910027f88488017ff3244009ff1922000ff4c910027f86488006ff6144001ffa0a2000ff90510007fa8288003fc414400bff98a2000ff8c510007ec6288003fd3144001fa98a2005ff0c510027fe4288003fe2144001f710a2000ff48510027f84288003ec21440037fb022001ffd011000ffc8088007fd4044003fe2022001ffcc11000ffc6088007fd3044003fe1822001ffc811000fde4088007fe2044003fe9022001fb4811000ff84088007ff1044001fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fd6150001fe30a8000bf18540007fea2a0003fe5150001fea8a8000ff14540037fe82a0003bf4150001ff20a8000ff505400077a82a001bfc415001bff98a8000ff8c540007fa62a0037fc3150019ff90a8000ff88540007dc42a0003fd2150019fe10a8000fb0854000dfec0a0007ff5050003ff2828001ff5414000ff8a0a0007ff405000dfda028001ff9014000f7c80a0007fc4050003de2028001fe1014000ffe60a0007fe3050003fe1828001ffc814000ffc40a0007fc2050003ff0828001ff04140007fec898002ff644c001ff3226006bf99130007fac898002fd644c001fe3226006bf19130007fca898003fd544c001fe2a26001bfd8d3001ffe869800ffe434c007fea1a6003ff10d30007fec498002ff624c017ff3126002bf98930007fac49802ffc624c0057e3126000ffd093005ffc8498003fd424c017fe2126003ffcc93001ffc649800ffd324c007fe1926000ffd8530005fec298003fe614c001feb0a6000ff18530005f8c298003ff414c001ff20a6000ff50530007f8829800fff314c007ef98a6003ff8c53001ffa6298003dd314c007fe18a600bffc8530007fc4298003ee214c001fe90a600bff08530007d84298006ff604c003ffa026001ff9013000ffa8098007fc404c003ff9826003fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007ff204c003ff1026001ff0813000ffc2098007fc104c005f7b264002fb99320017dac99000bec64c8001f72a64000fb55320007d8a99000bef63c8005f731e4002fb58f20017d8c790003ef43c8015f721e4000fb50f20057d8879000bef61c8005f730e4000bb98720017dac39000bec61c8001f7a0e4000fb90720007da8390003ec41c8015f798e4000fb8c720007da639002bec31c800376b064001fbd032000fdc8190007ed40c8003f62064001fbcc32000fdc6190007ed30c8003f61864001fb8432000fd82190003ff64480017fb224000ff99120035fcc890003fd64480017eb224000ff19120035f8c890003fe5448001feaa24000ff15120007fec690002ff6348013ff31a4003bf98d20007fac690002fd6348013fe31a4003bf18d20007fe8690027fe4348001fea1a4009ff10d2000dfec49000bff4248001f7a124002ff90920017dc849000bfd4248001f6a124002ff10920017d8849000bff3248013f79924002ff8c920017dc649000bfd3248001f69924002ff0c920017d86490003ff61480017fb0a4000ff98520007fac290003fc61480017e30a4000ffd0520007fc8290003fd4148001fe20a4009ffcc520007fc6290003fd3148013fe18a4002ffc8520017de429000bfe2148001f710a4002ff48520007da429000bfc2148005f610a4001bfd812000ffe8090007fe4048003fea024001ff1012000ffe6090007fe3048003fe9
  | 2 => 0x21017fa649080bfc32484057fb0a4200ffd0521007fc8290803fd4148401fe20a4214ffcc521007fc6290803fd3148429fe18a4202ffc8521017ee429080bfe2148401f710a4202ff08521017d8429080bf42148401ffb024200bfd812109ffcc090806fe6048401feb024213ff1812100df8c09084ffe4048427fe2024214ffcc12109ffc609084ffc3048405ff9024202fbc8121017fc409080bfc2048427ff0824213ff04121017dec81080bee6408405f6b204202fb19021007dca810803ed5408401f62a04202fbd8c21017dcc61080bed6308405f63184200fbd0c21097dc8610803ed4308425f62184202fb98421005dcc21080be66108401f7a084200fb90421007da8210803ec4108425f79884200fb8c421007da621084bec3108405f7b004202fb98021017dac010802ed6008405f63004211fb9002108fd8801084bef3008423f71804211fb0c02108fdc2010847ec100840dffb2e8006ff99740075fccba001bfd65d00017eb2e8006ff19740035f8cba0006fe64d000dffaa68000efd5340037fca9a001bfd54d000dfe2a68006ef15340037fec7a001bfe63d00077f31e8006ff58f40005fac7a001bfc63d00077e31e8000ffd4f40087fca7a0003fd53d0021fe29e8006ffd0f400377e87a001bfe43d000dfea1e8000ef50f40037f887a001bff62d000dff3168002bf98b40037fac5a0002fd62d000dfe3168002bf18b40007fea5a003ffe52d0001fea96800fff14b40037fe85a001bfe42d000dfea168006ff10b40087fe65a003ffe32d0001fe996800fff0cb40037fec3a001bfe61d00017f30e8006ff58740005fac3a001bfc61d0001ffa8e8000ff94740007faa3a0003fc51d000dffa0e8006efd0740037fc83a001bfd41d0001dea0e8006ff10740087fe63a0003fe31d0001fe98e8010ff0c74007ffe43a0003fe21d0001f710e8000ff4874007ff843a0003ec21d00037eb068001ffd434000ffca1a0007fc50d0003ff2068001ef9034000ff481a0007fc40d0003de2068001ffcc34000ffc61a0007fc30d0003ff9068001ff8834000ff841a0007fe10d0003fe0868000ffd9540005fecaa0003fe655001d7f32a8000ff59540005facaa0003fc655001d7e32a8001bfd9140007fea8a0003bf545000dff2a28000ff55140037f8a8a0003bc5450001ffb1a8000bfd8d4006ffcc6a000efe6350001feb1a800dff18d4001df8c6a0003ff535001bff29a8000ff54d4006ff8a6a001bff4350001dfa1a800dff90d40007fa86a0003bd435000dfe21a8000ffd8940005fec4a0033fe62500057f3128000ff58940067f8c4a000afc6250001ffa92800cff94940007faa4a0033fc525000dffa12800cff90940007fa84a001bfc425001bff992800cff8c940007fa64a0033fc3250001ffb0a8000bfd8540007fcc2a000
  | 3 => 0xeb046219ff1823100df8c118867fe408c433fe2046203ffcc23101ffc6118867de308c407fe1846203f70c2310d7fe4118867fe208c433fe1046219ff842310cff82118803ff644c4017fb226200ff99131035fcc898803fd644c4017eb226200ff19131035f8c898803fe544c401feaa26200ff1513101dfec69880fff434c407ff21a6203ff50d3101ff88698803ff624c4017fb126200fbd8931005dec498863fe624c4057f3126200ff589310c7f8c49880afc624c401f63126202bb18931007fe8498863fe424c401fea126218ff1093101ffe649880ffe324c407fe9926203ff0c93101dfec298803ff414c401ff20a6200ff50531007f8829880fff314c407fb98a6203ff8c531007bc629880ffc314c407ee18a6203fd0c5310c7fe4298863fc214c401ffb026200bfd81310bffcc098806fe604c401feb026217ff1813100df8c09885ffe404c42ffe2026203ffcc13101fbe609880ffe304c407fe1826218ffc81310bffc409885ffc204c42fff0826217ff04131007fec910802ff6488401ff3244206bf99221007fac910802fd6488401fe3244206bf19221007fca910803fd5488401fe2a44200ffd8e21005fec71085bfe63884077f31c4200ff58e21005fac71085bfc63884077e31c4200ffd0e210b7fc8710803fd438842dfe21c4202bf58a21017fe8510803ef4288405ff2144202fb90a21017fa8510803ed4288405fe2144202fb10a21017fe651085bef3288405ff1944202fb8ca21017fa6510803ed3288405fe1944202fb0ca21015fcc310803ff4188401ff20c4200ff50621007f8831085bff3188401ff18c4200ff4c6210b7f8631080bff2188405f790c4202fdc8621017f8431080bf42188401ffb044215ff9822100dfcc110803fd60884017eb044215ff1822100df8c110857fe408842bfe2044216ffcc2210affc6110857fc3088405ff9044202fbc8221017fc4110857ee2088405fe1044202fb082210affc2110857fc1088401f7b244200fb99221007dac910803ec6488401f72a44200fb55221007d8a910803ef638842df731c4200fb58e210b7d8c710803ef438842df721c4200fb50e210b7d8871080aee6188401f7a0c4200fb90621007da8310803ec418842df798c4200fb8c621007da631085bec3188401f7b044215fb98221007dac110802ed608842bf63044215fb902210afd8811085bef308842bf71844215fb0c2210afdc2110857ec1088401ffb224200bfd9121007fcc89081afe6448401feb224200bf59121007f8c89081afc6448401ff2a24200ff55121007f8a890803ff63484017fb1a4214ff98d2101dfcc690803fd63484017eb1a4214ff18d2101df8c690803ff4348429ff21a4200ff50d210a7f8869080aff6248405ffa124202ff90921017fa849080bfc4248405ff9924202ff8c9
  | 4 => 0x887fe1090443fe0848200ffd9541005fecaa08037f65504013fb2a8200ff99541075fccaa0803fd65504017eb2a8200ff19541075f8caa08037c65504013e32a8200ffd5141037fca8a0803fd545040dfe2a28200ffd8d41005fec6a0883fe63504077f31a8200ff58d41107f8c6a080efc6350401ffa9a8220ff94d41007faa6a0883fc535040dffa1a8220ff90d41007fa86a081bfc4350401ffb128200bfd8941007dec4a0802ef625043fff3128202bf98941007fac4a087ffc62504057e3128200fb18941015d8c4a0803ff525043fff2928200ff549410fff8a4a081bff425043fff2128200ff50941037f884a0883ff325043fff1928200ff4c9410fff864a0803ff5150401ff28a8200ff54541037fe82a081bf74150401ff20a8200ef90541107fe62a0883fc315043fff90a821fff08541007fec0a0802ff605043dff3028201bf98141007fac0a087bfc60504037e302821eff941410f7f8a0a087bfe405040dfe2028220ffcc1410f7fc60a087bfc305043fff902821eff881410f7f840a087bfe105043dfe0828206ffd9441035feca2081bfe651041d7f3288206ff59441005faca2081bfc651040d7e3288206bf99041037fea820803bf541040dff2a08206ff55041037f8a82081bbc541040dffb188206ff98c4101dfcc62081bfd63104017eb188206ff18c4101df8c620803ff531043bff2988200ff54c410eff8a62081bff431040ddfa188206ff90c41037fa8620803bd431040dfe2188206ffd8841037fcc42080afe621040dfeb108200bf58841037f8c42080afc6210401ffa90821cff94841007faa420873fc521040dffa108206ff90841037fa842081bfc421043bff990821cff8c841007fa6420873fc32104017f3088200ffd4441007fca220803fd5110401fe2888206ffd04410377e822081bfe411040dfb2088206ff504410077a822081bf5411043bff988821dff0c4410e7fe4220873fc211040dffb008206ff9804100dfcc02081bfd60104017eb008206ff1804100df8c02086ffe5010437fe2808206ff900410df7c802081bfc401040dde200821dffcc0410dffc602086ffc3010439ff900821bff880410dff8402086ffe1010437fe0808200ffd9231005fec918803fe648c40d7f3246200ff59231005fac918803fc648c40d7e3246200ff95231007faa918803fc548c4077eb1c6203ffd0e3101ffc871880ffd438c407fe21c6200ffd8a310d7fcc51880afe628c401feb146200bf58a310d7f8c51880afc628c401ffa14621aff90a31007fa851886bfc428c407ff9946203ff8ca3101ffa651880ffc328c4077f30c6200ffd0631007fc8318803fd418c401fe20c6203ffcc63101fbe631880ff7318c407fe18c6203fd0c6310d7fe431886bfc218c401ffb046219ff9823100dfcc118803fd608c4017
  | 5 => 0x4142147f8a0a10a3fe405080dfe2028429ffcc142147fc60a10a3fc3050805ff9028402fbc8142017fc40a100bfc2050851ff0828428ff04142007fec899002ff644c801ff3226406bf99132007fac899002fd644c801fe3226406bf19132007fca899003fd544c801fe2a26402bfd8d3201ffe869900ffe434c807fea1a6403ff10d32015fec49900bff424c805ff2126402ff50932017f8849900bff324c807f79926402ff8c932017bc649900bfc324c805ee1926402fb0c932007fec299002ff614c801ff30a6400ff58532007f8c299002fc614c807ff98a6403ff0c532017fe429900bfc214c805f610a6400ffd8132005fec09909ffe604c8037f3026400ff5813213ff8c099006fc604c84fff2026427ff1013201ffe609900ffe304c807fe1826402ffc8132017de409900bfe204c805fe1026427ff8413213ff8209901bff65d040dff32e820ebf99741037facba0802fd65d040dfe32e8206bf19741037fea9a081bfe54d040dfeaa68206ff15341037fec7a081bfe63d04077f31e8206ff58f41005fac7a081bfc63d04077e31e8200ffd4f41137fca7a0803fd53d044dfe29e8206ffd0f41037fc87a081bfd43d040dfe21e8206ffd8b41037fcc5a080afe62d040df73168202bb98b41037fac5a0802fd62d040df6b168200bb58b41037f8c5a080afc62d0401ffa968225ff94b41007faa5a0897fc52d040dffa168206ff90b41037fa85a081bfc42d044dff9968225ff8cb41007fa65a0897fc32d0401ffa8e8226ffcc741137f863a0897ff21d044bfe10e8206ffd8341037fcc1a0806fe60d040dfeb068200bf58341037f8c1a0806fc60d0449ff2868224ff14341037fc81a081bfc40d044dff9868224ff8c341127f861a0897ff20d0449ff1068224ff08341127fc21a0893fc10d0401ffb2c8200bfd9641007fccb2083afe6590401feb2c8200bf59641007f8cb20802fd6490401ffaa48200efd5241037fca920803fd549040dfe2a48200ef15241007fec72088ffe63904077f31c8200ff58e41005fac72088ffc63904077e31c8200ffd4e4111ffca720803fd5390447fe29c8206ffd0e410077e872088ffe4390401fea1c8200ef50e41037f88720803ff6290445ff3148202bf98a41007fac520802fd6290445fe3148202bf18a41007fea52088bfe5290401fea948222ff14a41037fe852088bfe4290401fea148206ff10a4111ffe652088bfe3290401fe9948222ff0ca41035fcc320803ff5190401ff28c8206ffd06410077e832081bf74190447ff98c8223ff0c641117fe432088bfc2190401ffb048221ff9824100dfcc120803fd60904017eb048221ff1824100df8c120887fe5090443fe2848221ff9024110f7c812081bfc4090443de2048223ffcc24110ffc6120887fc3090445ff9048221ff8824110ff84120
  | 6 => 0xdff286862eff14343037fc81a181bfc40d0c07ff9868603ff8c34301ff861a18bfff20d0c5dff106862eff08343177fc21a18bbfc10d0c01ffb2a8600bfd9543007fccaa183afe6550c01feb2a8600bf59543007f8caa183afc6550c077fb228600ffd51430077ea8a181bfe5450c01feaa28606ff1514300778a8a180eff6350c07ffa9a8603ff94d4301ffaa6a180ffc5350c07ffa1a8606f7d0d4301ffc86a180fbe4350c07fe21a8603ef10d4301fb886a1803ff6250c017fb12862dff98943015fcc4a1803fd6250c5bfe3128602bf1894316ffca4a18b7fc5250c5bff2128606ff1094301ffe64a180ffe3250c07fe1928600ffd8543005fec2a1803fe6150c01feb0a8600ff18543005f8c2a180fff3150c07fe18a862dffc854316ff842a1803ff6050c017fb02862cff9814300dfcc0a1803fd6050c59fe3028601bf18143167fca0a18b3fc5050c59ff2028606ff1014301ffe60a180ffe3050c07fe182862dffc8143167fc40a18b3fc2050c59ff082862cff04143037fecba101bfe65d081d7f32e8406ff59742005facba101bfc65d080d7e32e8402bf99342037fea9a101bfe54d080dfeaa68406ff15342037fec7a101bfe63d08077f31e8406ff58f42005fac7a101bfc63d08077e31e8400ffd4f4215ffca7a1003fd53d0857fe29e8406ffd0f420377e87a101bfe43d080dfea1e8400ef50f42037f887a100afd62d0805ffa968402ff94b42017f8a5a100bfe42d0805df2168402fb90b42017f885a100bbc42d0805ff9968402ff8cb42017f865a101bff61d080dff30e8400bf98742037fac3a1002fd61d080dfe30e842bffcc74215ff863a100bff21d0805fe10e8402fb08742037fec1a101bfe60d08037f3068406ff58342005fac1a101bfc60d08037e306842aff94342157f8a1a101bfe40d080dfe206842bffcc342157fc61a10abfc30d0805ff9068402fbc8342017fc41a100bfc20d0855ff086842aff04342007fecaa1002ff6550801bfb2a84009fd9542007fccaa103afe6550801feb2a8400bf59542007f8caa103afc6550801be32a84009f19542015fec8a1003ff545080dff2a28400ff55142037f8a8a1003ff63508017fb1a8429ff98d4201dfcc6a1003fd6350853fe31a8403bf18d42007fea6a10a7fe5350801fea9a8429ff14d42037fe86a1003bf4350853ff21a8400ff50d420077a86a101bfc43508057fb128402ffd4942017fca4a100bfd5250805fe2928402ffd0942037de84a100bfe4250805df2128402ff109420177884a100bec4250805ff9928402ff8c942017f864a1003ff61508017fb0a8400ff98542007fac2a1003fc61508017e30a8429ffcc54214ff862a100bff2150805fe10a8402fb08542007fec0a1002ff6050851ff3028401bf98142007fac0a10a3fc60508037e3028428ff9
  | 7 => 0x1802fd659500d7f324a806ffd52540777ea92a0033f549500dffb1ca806ff98e5401dfcc72a01bfd63950017eb1ca806ff18e5401df8c72a0e3fe539501dfe29ca806ff90e54037f8872a01bff629500dff314a802bf98a54037fac52a002fd629500dfe314a802bf18a541bffca52a0df7e529501dfe294a837df14a54037fc852a01bfc4295071ff994a837ff8ca541bff8652a01bff619500dff30ca800bf98654037fac32a002fd619500dfe30ca838ffcc6541c7f8632a0dfff219506ffe10ca806ffd8254037fcc12a006fe609500dfeb04a800bf58254037f8c12a006fc609506dff284a80eff14254037fc812a01bfc4095071ff984a836ff8c2541b7f8612a0dfff209506dff104a836ff082541b7fc212a0dbfc109500dff2a2a806df95154007fec6aa002ff635506bff31aa803bf98d54007fac6aa0d7fc63550077e31aa835ff90d54037f886aa003ff62550017fb12a834ff98954015fcc4aa003fd6255069fe312a802bf189541a7fc84aa01bfc425506bff992a834ff8c9541a7f864aa003ff61550017fb0aa800ff98554007fac2aa003fc61550017e30aa835ffcc5541aff862aa0d3ff2155069fe10aa800ffd8154005fec0aa0cffe60550037f302a800ff5815419ff8c0aa006fc6055067ff202a806ff101541affe60aa0cffe3055067fe182a834ffc815419ffc40aa0cffc2055067ff082a833ff04154035fcc82a01bfe541500ddf2a0a806ff550540777aa82a0033d541500dffb18a806ff98c5401dfcc62a01bfd63150017eb18a806ff18c5401df8c62a01bfe431500dfe218a806ffd8854037fcc42a00afe621500dfeb10a800bf58854037f8c42a00afc621500dff210a831ef90854037f8842a01bbc4215065ff990a831ff8c85418ff8642a01bff611500dff308a800bf98454037fac22a002fd611500dfe308a832ffcc454197f8622a0c7ff2115063fe108a806ffd8054037fcc02a006fe601500dfeb00a800bf58054037f8c02a006fc601500dff200a806ff10054197fe602a0c3fe3015061fe180a831ffc8054187fc402a0c3fc2015061ff080a830ff04054037fecba181bfe65d0c1d7f32e8606ff59743005facba181bfc65d0c0d7e32e8603bf99343037fea9a1803bf54d0c0dff2a68606ff55343037f8a9a181bbc54d0c077eb1e8603ffd4f4301ffca7a180ffc53d0c07ff21e8603ef90f4301fbc87a180ffc43d0c07de21e8606ffd8b43037fcc5a180afe62d0c0dfeb168600bf58b43037f8c5a180afc62d0c5fff296862fff14b43037fc85a181bfc42d0c07ff9968603ff8cb4301ff865a181bff61d0c0dff30e8600bf98743037fac3a1802fd61d0c0dfe30e8603ffcc74301ff863a18bfff21d0c5ffe10e8606ffd8343037fcc1a1806fe60d0c0dfeb068600bf58343037f8c1a1806fc60d0c5
  | 8 => 0x100380000580200000080100180400080d00580000180700280180000480080180080080400a02200000180280000200200100080080200200800280580580f00000180480080000000100000080000001200800000180200a01180280080300000000100180580100380400d00300300000680300080300980081700500000380180080000080100300100100100580000280500100780080000001080680100000580180780100280a00000300380580100300000100a00200000700100200080a80880100100080002d80080400501180081200000200000300600000000500000380180081680400501180180200000080000100100080c80000001e80500080100300080080000000a00380180480100100000400180180180180100800000000480000180300200280000200000000180180300280100000080180000080000382200100300f00100900400500200e00080280000000080281100500000000000080180000480d00200500c00300300d80000300100000d00000000000100000000200180500100080400100580000180400180100380280300000800600600480e81b00480080480500400300080180100100100280300280000180380000000180080000100100000000380d80a00080080200f80380000780200280080000000000000400180680000083a80000100280000680300300000181480000400080c00000500800380280200400080000000000380000500000400000400500300800780500080100080080080000500600380000280380000080700480300c00000d00080080000700080980100080180200000100000000800000300000000a80200000280000380000300380080080080780080380080280100000000000c00000080100500180000600580000c80580180380380080200000400080080180280000000380000000000000300000180080280c00280080a80080000000800800000780180300000600000400000480300600280100200080580180000100b00000500880000200580080400100200000b80180100280280800100200300980080980000300e80400000000180200200380780400000a81080280f00100081680000300180100180000480000100180100000780280100000600800100180280500300100000000180000080380080000380a00000080400300500000f80280100600100000580300500200000100f80b00500000001b00300100500481a00080300100200080100100700600600300401100f80400a80400300380500300000080380a80180080000000000000100781200000000100100000600080000600000080500480700700300300080100000300180380000280000180a00000080200100000000080200280880200000200200701c01380100080000a8
  | 9 => 0x1fe4b46bb4a06ac0000370002548001980000006040005184fd2050074180c80dc094dd7383c3e1ec133a0d0002ce8000900002433dd0000610006e70000000000000c300000000000000063b8003130000000000000005fe6a35950d41b4800000189ba300009580022a56935918200000005b0000d800000000000000046d1e4ddd62e0002be30e03b00011e0000004e900039141e3360005c528115c0003630006c700066c0d66101da959afa31bea0209e881f50a381290d95035b1f00000004c00000005830c22f780033a3499b65605e14ab464176c95b8000000000000000015a4ce1615ba0000000000000d304a00022c4454c700010eb6487b8000005540005722fc48e304d20b7c33000025c5c72bd6d13c95664bf4696cb6e3321d150c43e71db31e2ea000183cbb3c74272e53a29cd496c2c27080025216d0b19592093d3c4a48251babba1a45b0002e34fa33117f35acad2183791225df5da6be3cb8004c820100008226028a29c2448000000000006b80005d848cee911c05380023b27e1ad52d0248003db3500f2e582572d545f56e23d4c43d60000006640005ff0000005e519b4bc0005411f42d600046f0005080000000005d61a40000005f200000063d6ea26d4f400009c60e00000067352b1edd9a30b4f20000004e43bd64e2701e2b32055a9b3b457e3441155b443a1f30004210d15621026e600069000044827ea973af63ab962f83608d0ae009840625e5e82d24df0bde5c000175ad6c7d6aa65b348e1812b06d1e16b26bc4922f23b517126e30b8000000420212980005c36860a9a9c80000000039cdb800000038400038180054c0006a200022f2618001480452680005122ec4850160004cf5800004a90000001a2e2700000000032d956c080000000000005280005cb3114ef12b80500049941615e2c34200000000005470f71d335e5a9265c6c1873c7c94d9c41c55066912d53a55600000059437153f0ba5f40522e20005128000000004f84ff55e0002d780057036f6c50000000850000000721e75e64c928f42506b1b32b2d1f6d05094d93153761b40592db1ea41d67a8000004e00000000a33ef8000000002de00000000000045a3c50005f53df050a7c2a35f90002716b114e06bb0ee522c15026a732849452a25866f5dc40c22e4574622932dc08c1888560003a0afb3c43f321428b0994d6a4c0844f13f0b8d0006b04e500019a058ded5840000ea26764c08010818bcfb03c6adcd40004e16a952500030f8e24046545331df57c4be4ec1960004b90882da62f0353852aee3b64a1303821a63e6c77085a02edb04daab02568c00000200000180000a00380480000000100680180400000000180d00500e00800000f80280000080180280780000100000300000180980180000000100000080000480100
  | 10 => 0x93212d1b01543331dca86916313bc1bc677bd36d429468d07903d34c59029182600066a3002429b2000637b089da25000001761519e00008d18a4806d311d2411e65a1051a5523c0574ae1b8564a3886e014ecc3de3a023e34a52939da4f68f13c000459000059d2032e5b315f40a2d00005a695838aaf41773864c149e69661748f4f008f3d582ca71a7d42f05c5053780f020c03609e24201c2693f23e65321363c335331fccb5d00c600018d61c27b44419953e18e2669328b3c1714593551e87e6acde22df2204783c6b719d00e563890583e8000004b60004c52340002154700002ae0002c400001463a146e343662ba04457d3491762678a2c7f39c24d0000002a93ad0000001c632ea4e129172158b4558600012100057b29d0006638005c10b75bb45d1be6b52dd2ed5ac41449700040565f4ea3f732016500011b69e2c80000000004032354e634ac3d62b2d7177b9d6e43460940003940001271730005270003ca2784dc00019f0002920000004a72b108a5bd0b336b3d20c780007d00064ca9dc3c51c4ee240a5f8a1a8c0001a707ab0d0001af6bf2d30000000000001ca69a8005260001e511400067a0005ca4a36970005130001a88000002b40006245ea0004ed0000000000005ef0000000005780003b14af02bc5561f42200000000011a90d50b3642325f00275962c614142a3344f72d43bf59d684d8a4d6069640636e425a33f116433c5bc4d709b20360c3d80675520701336d227a32c3040f42002c9db904f8f19945146ad648057811c4c1553dc4116ce4e3ace4262251c7c2b0000000000000196394a20006bd0001880001bf96944903304d0002756710973410000002081038006660000006c00000000002f98540fb0000000003f936a00000046557a546437ba969c5e30e056b0a8a300000000b0c9c00004f6510000000863730470002cf21000068041a9ab2a09572cb9850006060003690de35c0005911254542382445756dd4020000e80000000000000004e71bb00055c0000c027406300c0000ce0d287b0002a180066280051d8003eb0868000002af5db000120ce8124447612073479bfe33f6e1471da61670a74530002f60322d10750001170005674bd2ee2290001933951ed33329e35a35d1f96471862aa10a3b84370002cd6dc3fc1e80003481751ac9523428005743239835a718c0a213c96ab230000000000000004c619200000001e00e5af0000006460b60f2483292a645365e0522e7f2493a48ec566a05ba83c110a81f1136c125413d8651235e738e438000365245a243fd08b1b6db700000000059e0003068000000000000003f550121c357ba70cfac253c000000605000000180ec30005e454005e1d100000054900066d50700067e26c00a08700000042680008e2990ad03f0002b55380b81e39a0
  | 11 => 0x53051bf1a14632130003525e951964d8000000006232fab9001a0716b300056f00000002d00044e00054260b0001048a10001d8ba1c8d17834b4d10130002b73cf1c82776d561400000049300051a6659c00006af0fc3f63228003b26603430000413cb5060005642b23b31b780012f00017912616821f4c3b2234037000027660d5482cdacce858002ca00031217b30dd5716034b8e097880033750f00016b3d400002c62610738300051725d3cc4bbdf8d770e90640f60006a100000001382869400011a00069b8b2000000000000122dfa0000006985764582b600000000009d00000004000065a19d6de4006256ae29f00000048a82db160006201ac00000000056800000039a0290005580001e02b4c0e0000003291a68380000002b180000015100030f5148581970000003ff00000064b18d90507646ea1b0002800000b28003250660002ef2c7ad81b10fd3810db07744049559f272d710000001dc49100014b47c206b4d0001ce18b55f0000000a90001c9b9b000107c6000038a444e1e0000000003ac68336e66830793b40961142e6a83c206211cbbe0ff2f3432181e35000555398384c7412a8005d22730001e3358be80000205fc5160891b580000067be2d5034dd6d82a71e94f93026cd6090ee3f45394960dd4fe488222266293a1da25810000000354206359cd04b83959ae46e23f18291103905f32467418f14a024259310a6f9fd61a26167554e0923ef68b5b65ec000510800664d3b0fa21600065e25ed871e400064f5fb0000003d70005000006783209c20000000000001b74fc1d624a0b966300055347ba460d90006370002e90002474e080065d50d55b0120001425ab09316258504b5f798418e8af5352214891ff0d7340b753611de46128630c56e968bf021d0bf29013486a8002535614195178000bd3ce0002b30f80000000000000003c800063e0003e200000039760f60069a1d72260223b611fa510000005043516d600066de3862828762239fce1a1e11604c0b16ab305a0a8005fd0034d8b7a5feafd1545510000cc10c2e868902b34717468756d1ba025b6c00000000042958c59203e3e4c8600000047900038b8000000000005f859949a0e18003e30000a5d8822b3350b54d237d5236e231d4ca2e5c134684662956a3c4b1312b5edf6cf26b3c8ec80bb214b081123fb80004607cce31d45430002b054d4de0a602f2bc31b23966e1400003e90000006320cd51e50fb3d6b705003ba5f6706532eb20a10300100000050a0001a50000c7000189398e550be80052f0005c41a23e000044ba418000080000001f80006a505348400000022d0002adba20004f480055bdc20001c730600020f5f32fe1aa563aa81204aa2e10b42a06a40c480065749846b56511e8002bccdb48c0f3b183ba5d518ceb91d240f6013
  | 12 => 0xc525b1d1d396c1f13e5d10e72e75a8e8e41a157b773ea4350001950000ef4816491ab80b0000230005d300047e000397d4563f4c306a0a461602eda54b76410001bd09f0d181b50e0df04eb670002b383049f19101d1395aa00000048a0cb000645056e6b2632316c40f50515f72620004906a61093aa0f32a42a11b95f11cc0002842c567b2d9e8113b9dd4360002110003a62d924507a48b4510002125f4a5380000000000036680031c00028833b1d84d8000000204b62e070bc1098a017d0c904e05d69240b13f0e100067d32b26f0833828eb00d11800000000039e1d929b8965a207d80028d0002af9e6800169b4199000666e80000000000000000064400060300028326a0000040e43173e40001fa00000022780000058900043413724813d31c8001700f14198003095f58003e518acb200053100058e1f703144d2e6389000093dde550ba56302045c81196765d903cd3d40d58b5f1c1011b8ac05a6a49042a292c8000002138000f48000004b155d1b510f00000067c4246500090602404c233e441e1d54a5a02a6399633498dd42d5cba1100ab21947312e00241260203d93a1665c630717a21762c3fb0003b75f62ff2cc2235cd0a8273d1152e5820000d02e6cf537e31eda814894f3f83c63381cb35f3ed0000f916c25b15b0000004ac0002c69c120e12c00010cd3709544290b0000c5e612c900034e0da309a330006d90c693e8004cc0006e82074393f3ce230122700000000000000000023a16e09a06f000439dc06190000aa523bcd00006c823a9ac310000000000005105300000003143742960004501498002d88000004f58000848000000911460000000000002bb00043f00069900007435500049d5ae2bf2560006b60000004f654f0a790e00027d8005440000005f3ca62b90000000d26216725c9000000511d9b2891f602a0003d950c0000006676b463c0000005930cf2850e638c2ad0002f56da1fb0bc86c0e3906800000000000000372000000096ae40004b30001813580000001f22b0c2300000000000000041b0000000003fa00067900057f6d756a0ed2651eb1a48005b23a3af027f47630a3426e52f95985ce04935ec5c187a3640716a33fe9338f1678000ca00031f12980000051c90100000000000000038b5b53618d52790e338700000000069f365dbf03400058d000372ac76c20001474f314510f9a81ee2370553191c427252c44364d2f130ae6569d6c90528a497c19c5731f137f6e054b3395b3bec5be15611f46a32d521b8cc754a51ef1380000000480004cd00000038857900011d883c712c045e18f80032a0004a424b2f715300000040100007f3d000028e00015d14780058f0000006ca3b93103620c116f3b069b0a5054ee7e131c3069ca10003f2c7a31a260ba45636593da0000002b847268
  | 13 => 0xa69a7b8dacb0229633ae000000363e9532f37b0000810000006ba5591281e261b28200000003a44600000068425a5ee5cc0002910000001341a3106515c283ab0003600001e7b2120b0000c54151490e28004d558117e0430fe1c560a55a49b534516c7b6825b042d52412a4670ceb4f0112f8c873272ac3a152100029a44f14d1fc4eb0bbbee1b00be6082a520251fa94800000108a688000002a200f00043036d14344110062a0783d10186772280006620006c60000005eb1c932614c1a90006560001d55b0d6c0004da0003926431cf0006360000003680000000000004d35b1303522629000000000000068424d972c893200035668a5cf4565a45ad3c00b041c8004c5a36a9f87c00039f121c4235fb9e82e4b0499bd53ee9443bb00000043b000679be11803574b50ae559a15935
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc6510510006bf6410510036bc6410510006df63105100eedc6310510006ef62105100e6ec62105101e4fe768c510006bf648c510006bc648c5100cedf638c51001edc638c510006ef628c5100d6ec628c5101e5f6768c5101def6768c510007b7648c510007b4648c5100bdf5738c5100cfd7638c51001ef6638c51001ef4638c51002fd4638c51001ed4638c510007e7628c510007e4628c51000df6708c51000df4708c5100cef7608c5100cfd6308c5100cfd4308c5100cfe7208c5100cfe5208c51001cff764c51000cfe764c5100bcfd764c51000cfc764c510006bf644c510006bc644c510006df634c51001edc634c510005ef724c510025ec724c510006ef624c5100c6ec624c51002fd4314c510005fb704c51000df8704c51000df4764c51001ef4764c51000cf4764c510007b7644c510007b4644c5100cdf7734c510007d7734c510007d7634c51001ef6634c51001ef4634c51002fd4634c510007e7724c510007e4724c510007e7624c510007e4624c510007f3704c51000df6704c51000df4704c5100bff0704c5100bef7604c5100bfd7304c5100bfd5304c5100bfe7204c5100bfe5204c51008cfe7688510006bf6488510006bc6488510006df63885100b6dc63885100aeef6288510016ee6288510006ed6288510016ec628851008dee7688510006ee768851008cee7688510006ef6488510007af6488510006af64885101d6ee6488510006ed64885101d6ec6488510007ac6488510006ac6488510006ef6388510007cf6388510006cf63885100b6ee6388510006ed63885100b6ec6388510007cc63885100b6cc638851008dee71885100aeef6188510007e63188510007e531885100adef70885100aded70885100aeef60885100afe610885100afe410885100afe81088510014ff764851000cfe764851009cfd764851000cfc7648510006bf6448510006bc6448510006df63485100a6dc6348510006ef6248510016ec6248510005fb704851000df870485100adee7608510026ee76085100acee7608510006ef6408510007af6408510006af64085101ceee6408510006ed64085101ceec6408510007ac6408510006ac6408510006ef6308510007cf6308510006cf6308510096ee6308510006ed6308510096ec6308510007cc6308510096cc63085100adee7108510027e6710851008eef6108510007e63108510007e5310851008def700851008ded700851008eef600851008fe6100851008fe4100851008fe8100851000dfa76c411000efa76c411000cfa76c4110007bb64c4110007b864c4110007db63c4110007d863c4110007eb72c4110007e872c4110007eb62c4110007e862c411000dfa71c411000ff271c411000efb61c411000ff361c4110007f231c4110007f131c4110007ea21c4110007e821c4110
  | 1 => 0x8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef43d8910006ee43d8910006ed43d8910006ec43d89100aeef71d8910026ee71d8910014ee71d89100aeed71d8910014ec71d8910006ef31d8910006ec31d89100aeef70d89100acef70d89100aeee70d89100aeed70d89100aced70d89100aeec70d89100aeef40d89100aeee40d89100aeed40d89100aeec40d89100aeef30d89100aeee30d89100aeed30d89100aeec30d89100aeef10d89100aeee10d89100aeec10d8910005bf7458910005bc7458910006bf6458910006bc6458910005df735891002ddc7358910006df6358910006dc6358910026ec62589101edf77158910004ff7458910006bf7458910004bf7458910034fc7458910006bc7458910034bc7458910004ff7358910006df7358910004df735891001cfe735891001cfc7358910006dc735891001cdc73589100acff7258910006ef72589101ecff7158910006f77158910026ec215891009cff7058910006fb705891009eef205891009eed20589100adee7618910026ee76189100acee7618910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc631891008eef611891008eef601891008fe6101891008fe4101891008fe81018910034ff76d0910004fe76d0910004fd76d0910034fc76d09100067f65d09100067c65d0910006bf64d0910036bc64d0910006df63d091015edc63d0910006ef62d0910016ec62d0910004ff7650910004fe7650910004fd7650910004fc76509100057f75509100057c75509100067f65509100067c6550910006bf6450910036bc6450910006df635091014edc6350910006ef6250910016ec6250910004ff764c910004fe764c910004fd764c910004fc764c910006bf644c910006bc644c910006df634c91001edc634c910006ef624c910016ec624c91000cfe76d051000cfc76d05100067f65d05100067c65d0510006bf64d0510036bc64d0510006df63d0510136dc63d0510025ee72d0510005ed72d0510006ef62d051012eec62d051000dfa70d0510005f970d05100dcfe76905100067f65905100067c659051010ebf6490510036bc6490510006df639051011edc6390510006ef6290510116ec6290510034ff765051000cfe76505100f4fd765051000cfc76505100057f75505100057c75505100067f65505100067c6550510006bf6450510036bc6450510006df6350510106dc6350510005ef7250510025ec7250510006ef62505100feec6250510005fb705051000df8705051010cfe76105100067f65105100067
  | 2 => 0x6de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006de62d8d10006dc62d8d100cfd771d8d100cfcf20d8d100cfcd20d8d100cfd610d8d100cfd410d8d100cfd810d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006de42d8d10006dc42d8d100cedf71d8d1002ede71d8d100cedd71d8d10006df21d8d10006dc21d8d100cedf70d8d100cede70d8d100cedd70d8d100cedc70d8d100cedf40d8d100cede40d8d100cedd40d8d100cedc40d8d100cedf20d8d100cecf20d8d100cede20d8d100cedd20d8d100cecd20d8d100cedc20d8d100cedf10d8d100cede10d8d100cedc10d8d10005bf7458d10005bc7458d10006bf6458d10006bc6458d1002edc6358d10005ef7258d10025ec7258d101f5f77158d10004ff7458d10006bf7458d10004bf7458d10034fc7458d10006bc7458d10034bc7458d100ccff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d10014fe7258d10014fc7258d10006ec7258d10014ec7258d101f4ff7158d10006f77158d100bcff7058d10006fb7058d100beef2058d100beed2058d100cdde7618d1002ede7618d100ccde7618d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10006de6218d10006dc6218d101e7d57118d101e6df6118d101e6df6018d101e7cf2018d101e7cd2018d101e7d61018d101e7d41018d101e7d81018d10034ff76d0d10004fe76d0d10004fd76d0d10034fc76d0d100067f65d0d100067c65d0d10006bf64d0d10036bc64d0d10006df63d0d1001edc63d0d1017eec62d0d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d100067c6550d10006bf6450d10036bc6450d10006df6350d1001edc6350d1016eec6250d10014fe76d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910026ee62d8910034fe74d8910004fd74d891001cfe73d8910004fd73d891001cfc73d8910026ee42d8910026ec42d8910006ef32d8910026ee32d8910026ec32d8910014fe71d891000cfd71d8910014fc71d8910026ef21d89100acff70d891000cfe70d89100acfd70d891000cfc70d89100aeef20d89100aeed20d891008dee76d8910014ee76d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89100afe610d89100afe410d89100afe810d8910006ef74d8910006ee74d8910006ed74d8910006ec74d
  | 3 => 0xd7399110025ee7299110005ed72991100f5f571991100057f75591100057c75591100067f6559110005df735911002ddc7359110005ef7259110025ec7259110125f77159110004ff75591100067f75591100047f7559110074fc75591100067c75591100747c7559110006bf7459110004ff7359110006df7359110004df735911001cfe735911001cfc7359110006dc735911001cdc7359110004ff7259110006ef7259110004ef7259110014fe7259110014fc7259110006ec7259110014ec7259110124ff7159110006f771591100f4ff7059110006fb70591100f6ef20591100f6ed205911010cfe76191100067f6519110036be6419110006bd641911010dbe7619110006be761911010cbe7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006be6319110006bc6319110006be6219110006bc62191100dfaf20191100dfad20191100dfb610191100dfb410191100dfb81019110036bf7519110036be7519110036bd7519110036bc7519110036bf7319110036be7319110036bd7319110036bc7319110006be5319110006bc5319110036bf7219110036be7219110036bd7219110036bc7219110006be5219110006bc5219110006bf3219110006be3219110006bc3219110036bf7119110036bd7119110006bf3119110006bc3119110006bf2119110006bc2119110036bf7019110036be7019110036bd7019110036bc70191100debf50191100debe50191100debd50191100debc50191100debf30191100debe30191100debd30191100debc30191100debf20191100deaf20191100debe20191100debd20191100dead20191100debc20191100debf10191100debe10191100debd10191100debc1019110034ff7695110004fe7695110004fd7695110034fc76951100067f65951100767c6595110006bf6495110036bc64951100073f54951101c6dc63951101beec6295110004ff7655110004fe7655110004fd7655110004fc7655110006bf6455110036bc64551101aedc63551101a6ec6255110034ff7615110004fe7615110004fd7615110034fc7615110006bf6415110036bc64151100073d5415110196dc631511018eec6215110005f67115110005f5711511001cfe76d8d10006bf64d8d10006bc64d8d1002ede63d8d10034fe74d8d10004fd74d8d1002ede43d8d1002edc43d8d10014fe72d8d10004fd72d8d10014fc72d8d1002edf32d8d10006de32d8d1002edc32d8d1001cfe71d8d1000cfd71d8d1001cfc71d8d1002edf31d8d100ccff70d8d1000cfe70d8d100ccfd70d8d1000cfc70d8d100cedf30d8d100cedd30d8d100ceef20d8d100ceed20d8d101e5de76d8d1001cde76d8d10006df64d8d100079f64d8d100069f64d8d10
  | 4 => 0xc7101f4ff764c710006df634c71001edc634c710005ef724c71003dec724c710006ef624c7100c6ec624c710047d4314c7101f5f7764c7101fef7764c710007d7734c710007d7634c71001ef6634c71001ef4634c710047d4634c710007e7724c710007e4724c710007e7624c710007e4624c71000df6704c71000df4704c7100bfd7304c7100bfd5304c7100bfe7204c7100bfe5204c71000cff7688710014fe768871000cfd7688710016ee6288710006ed628871000dfa7088710005f970887100aeef7688710016ee7688710016ed76887100aeec7688710006ef64887101d6ee6488710006ed64887101d6ec6488710006ef63887100b6ee6388710006ed63887100b6ec63887100aeee6188710007e63188710007e531887100afea70887100aded7088710007e97088710005e970887100afe610887100afea10887100afe410887101ecff7648710006ef6248710016ec6248710016ef76087100adee760871003eee760871008eed7608710016ec7608710014ec7608710006ef64087101ceee6408710006ed64087101ceec6408710006ef6308710096ee6308710006ed6308710096ec630871003fe6710871008eee6108710007e63108710007e5310871008def700871008fea700871008ded700871003fe97008710005e9700871008fe6100871008fea100871008fe41008710034fe76d9110074fe75d9110004fd75d911001cfe73d9110004fd73d911001cfc73d9110006be43d9110006bc43d9110014fe72d9110004fd72d9110014fc72d9110006be42d9110006bc42d9110034fe71d9110034fc71d911010cff70d911000cfe70d911010cfd70d911000cfc70d911010ebf40d911010ebd40d911010eef20d911010eed20d9110034be76d9110006bf65d91100073f65d91100063f65d9110006be63d9110006bc63d9110006be62d9110006bc62d911010faf20d911010fad20d911010fb610d911010fb410d911010fb810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006be53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006be52d9110006bc52d9110006bf32d9110006be32d9110006bc32d911010ebf71d911010ebd71d9110006bf31d9110006bc31d9110006bf21d9110006bc21d911010ebf70d911010ebe70d911010ebd70d911010ebc70d911010ebf50d911010ebe50d911010ebd50d911010ebc50d911010ebf30d911010ebe30d911010ebd30d911010ebc30d911010ebf20d911010eaf20d911010ebe20d911010ebd20d911010ead20d911010ebc20d911010ebf10d911010ebe10d911010ebc10d91100057e75991100057d75991100067f6599110006bf649911002dde7399110005d
  | 5 => 0x9cfd72d8b1003eee42d8b1003eec42d8b10006ef32d8b1003eee32d8b1003eec32d8b1008cfe71d8b10006f671d8b1003eef21d8b10006f970d8b100aeef20d8b100aeee20d8b100aeed20d8b100aeec20d8b10006ef64d8b10006ee64d8b10006ed64d8b10006ec64d8b10006ef63d8b10006ee63d8b10006ed63d8b10006ec63d8b1008dee71d8b10007e671d8b1008de671d8b10007e970d8b100afe610d8b100afea10d8b100afe410d8b10006ef74d8b10006ee74d8b10006ed74d8b10006ec74d8b10006ee54d8b10006ed54d8b10006ec54d8b10006ef73d8b10006ee73d8b10006ed73d8b10006ec73d8b10006ef43d8b10006ee43d8b10006ed43d8b10006ec43d8b10006ee71d8b1008cee71d8b10006e671d8b10006ef31d8b10006ec31d8b100aeed70d8b10006e970d8b100aeef40d8b100aeee40d8b100aeed40d8b100aeec40d8b100aeef30d8b100aeee30d8b100aeed30d8b100aeec30d8b100aeee10d8b100aeec10d8b10014ff7658b1003eec6258b10004ff7458b10034fc7458b10004ff7358b1001cfe7358b1001cfc7358b10006ef7258b10014ff7158b10014fd7158b1000cfc7158b1003eec2158b1009eef2058b1009eed2058b1003eee7618b10006ef6418b10006ee6418b10006ed6418b10006ec6418b10006ef6318b10006ee6318b10006ed6318b10006ec6318b100adee7118b1003fe67118b100ade67118b1008eee6118b1003fe97018b1008fe61018b1008fea1018b1008fe41018b10034ff76d0b10004fe76d0b10004fd76d0b10034fc76d0b10006ef62d0b10016ec62d0b10004ff7650b10004fe7650b10004fd7650b10004fc7650b100057f7550b100057c7550b10006ef6250b10016ec6250b10004ff764cb10004fe764cb10004fd764cb10004fc764cb10006ef624cb10016ec624cb100f4fd76d0710006bf64d0710036bc64d071003dee72d0710005ed72d0710006ef62d071012eec62d071000cff769071000cfd7690710036be6490710006bd6490710006ef6290710116ec629071000dfa7090710005f97090710124ff76507100057f75507100057c7550710006bf6450710036bc6450710005ef725071003dec7250710006ef62507100feec625071000cff761071000cfd7610710034fc7610710036be6410710006bd6410710006ef62107100e6ec621071000dfa7010710005f9701071000cff768c71001cfe768c71000cfd768c71001ede638c710006dd638c710006ef628c7100d6ec628c71000dfa708c710005f9708c71000df5768c71001ef5768c71000cf5768c71001ef6638c710047d6638c710007d5638c71001ef4638c710007e7628c710007e4628c71000df6708c7100cff2708c710007f1708c71000df4708c7100cfd6308c7100cfd4308c7100cfe7208c7100cfe5208
  | 6 => 0xf318c52004fe7318c52004fe4318c52000dee708c5200cded708c52000dec708c5200ceef608c5200d7eb608c5200cfce308c5200cfcc308c520005ef764c520006ef764c520004ef764c520005ee764c520005ed764c520005ec764c520006ec764c520004ec764c520005ef744c520205ee744c520005ed744c520205ec744c5200cdef734c5201f5ef714c520006ec614c52004fe7314c520007ce314c52004fcc314c52004fe4314c5200bdef704c52000dee704c52000dec704c5200beef604c5200c7eb604c5200bfcf304c5200bfcd304c5200ddf671d9310074fe75d9310004fd75d931001cfe73d9310004fd73d931001cfc73d9310014fe72d9310004fd72d9310014fc72d93100dcfe71d9310006f671d9310006f970d931010ebe40d931010ebc40d931010eef20d931010eed20d93100f4fd7699310006bf649931003dee7299310005ed7299310034ff76593100057f75593100057c7559310005ef725931003dec7259310004ff75593100067f75593100047f7559310074fc75593100067c75593100747c7559310006bf7459310004ff735931001cfe735931001cfc7359310004ff7259310006ef7259310004ef7259310014fe7259310014fc7259310006ec7259310014ec7259310034ff7159310034fd71593100f6bf40593100f6bd40593100f6ef20593100f6ed2059310036be6419310006bd641931010df67119310034ff7695310004fe7695310004fd7695310034fc76953100067f65953100767c65953100073f54953101beec6295310004ff7655310004fe7655310004fd7655310004fc76553101a6ec6255310034ff7615310004fe7615310004fd7615310034fc7615310006bf6415310036bc64153100073d541531018eec6215310005f67115310005f57115310046de63d8f101e5f671d8f10034fe74d8f10004fd74d8f100bcfd73d8f10014fe72d8f10004fd72d8f10014fc72d8f101e4fe71d8f10006f671d8f10046df31d8f10006f970d8f100cede30d8f100cedc30d8f100ceef20d8f100ceed20d8f1001cff7658f10046dc6358f10005ef7258f1003dec7258f10004ff7458f10034fc7458f10006df7358f10004ff7258f10006ef7258f10004ef7258f10014fe7258f10014fc7258f10006ec7258f10014ec7258f1001cff7158f1001cfd7158f1000cfc7158f10046dc3158f100bedf3058f100bedd3058f100beef2058f100beed2058f10034ff76d0f10004fe76d0f10004fd76d0f10034fc76d0f10006bf64d0f10036bc64d0f1017eec62d0f10004ff7650f10004fe7650f10004fd7650f10004fc7650f10006bf6450f10036bc6450f1016eec6250f10005fb7050f1000df87050f1003eee62d8b1008df671d8b10034fe74d8b10004fd74d8b1001cfe73d8b10004fd73d8b1001cfc73d8b10
  | 7 => 0x852008fe51018520006ef7418520006ee7418520006ed7418520006ec7418520006ee5418520006ed5418520006ec5418520006ef7318520006ee7318520006ed7318520006ec7318520006ef4318520006ee4318520006ed4318520006ec4318520006ef3118520006e73118520006ec3118520006e4311852008eef701852008eed7018520014ed701852008eef401852008eee401852008eed401852008eec401852008eef301852008eee301852008eed301852008eec301852008eee101852008eed101852008ee5101852008eec1018520205ef76d0520005ee76d0520206ee76d0520004ee76d0520005ed76d0520206ed76d0520004ed76d0520205ec76d052020dee75d0520005ed75d0520205ec75d052004dee73d0520005ed73d052004dec73d0520007e761d0520006ec61d0520007e461d0520006e461d0520125ef70d052000dee70d0520125ed70d052000dec70d0520126ef60d052012feb60d0520127af40d0520127ad40d0520005ef7690520005ee7690520005ed7690520005ec7690520005ef759052020dee7590520005ed75905200f5ed7490520007af6490520007ac6490520007af5490520007ac549052004dee7390520005ed739052004dec7390520007af4390520007ad43905200ddee7190520006ec6190520007af4190520207e7419052000dee709052010ded709052000dec709052010eef6090520117eb609052010fae409052010fac4090520005ef7650520006ef7650520004ef7650520005ee7650520005ed7650520005ec7650520006ec7650520004ec7650520005ef75505200076f75505200056f755052020dee7550520005ed755052020dec75505200076c75505200056c7550520005ef735052004dee735052004dec7350520006ec6150520207e74150520007ae41505200f5ef705052000dee705052000dec70505200f6ef60505200ffeb60505200f7af40505200f7ad4050520205ef7610520005ee7610520005ed7610520205ec7610520205ef751052020dee7510520005ed7510520205ec7510520125ee7410520007af6410520207ac6410520007af5410520207ac541052004dee7310520005ed731052004dec7310520207af4310520007ad431052010dee7110520007e76110520006ec6110520007e46110520006e46110520207af4110520207e64110520007ad4110520207e541105200ddef701052000dee70105200dfea701052000dea70105200dded7010520207e97010520005e9701052000dec70105200deef60105200e7eb60105200dfae40105200dfac4010520005ef768c520005ee768c520005ed768c520005ec768c520005ef748c520205ee748c520005ed748c520205ec748c5200bded738c520007cf638c52004fcc638c5201e5ee718c520006ec618c52004fc
  | 8 => 0x4fcc43d8d20005ee71d8d20005ed71d8d2004fcc31d8d20015ef70d8d2000dee70d8d20015ed70d8d2000dec70d8d20236ef60d8d20247eb60d8d20237cf30d8d20237cd30d8d2023def7658d20005ef7458d20007af7458d20005af7458d20205ec7458d20007ac7458d20005ac7458d20235ef7358d20007cf6358d2004eee6358d2004eec6358d2004fcc6358d20005ef7158d20007e77158d20005e77158d20005ec7158d20007e47158d20005e47158d2013def7058d20007eb7058d20005eb7058d2013eef6058d2005feb6058d20205ef76d0d20005ee76d0d20005ed76d0d20205ec76d0d2020dee75d0d20005ed75d0d20205ec75d0d2022dee74d0d20207ae64d0d20007ad64d0d20007af54d0d20207ac54d0d20165ed73d0d20007cf63d0d2004fcc63d0d2004fae43d0d2004fce43d0d2004fac43d0d20005ee71d0d20005ed71d0d20175ef70d0d2000dee70d0d20175ed70d0d2000dec70d0d20176ef60d0d2017feb60d0d20177af40d0d20177ad40d0d20005ef7650d20005ee7650d20005ed7650d20005ec7650d20005ef7550d2020dee7550d20005ed7550d2020dec7550d20225ef7450d20007ae6450d20007ad6450d20007af5450d20007ac5450d20175ef7350d20207cf4350d2004fae4350d2004fac4350d2004fcc4350d20005ef7150d20005ec7150d20165ef7050d2000dee7050d20165ed7050d2000dec7050d20166ef6050d2016feb6050d20167af4050d20167ad4050d20205ee74d8520005ed74d852004dee73d8520005ed73d852004dec73d8520007e731d8520007e431d8520015ef70d8520015ed70d85201eeef60d852021feb60d85201efe710d85201efe510d8520205ee7498520005ed7498520006ef6498520006ee6498520006ed6498520006ec649852004dee7398520005ed739852004dec7398520006ef6398520006ee6398520006ed6398520006ec639852008dee7198520006ef6198520007e761985200aded7098520007e97098520005e9709852003feb6098520005ef7458520007af7458520005af7458520205ec7458520007ac7458520005ac7458520005ef7358520007cf7358520005cf735852004dee735852004dec7358520007cc735852004dcc7358520007e76158520006ee615852009def7058520007eb7058520005eb7058520027eb60585201edee7618520205ee7418520005ed7418520006ef6418520006ee6418520006ed6418520006ec641852004dee7318520005ed731852004dec7318520006ef6318520006ee6318520006ed6318520006ec6318520006ef6118520007e66118520006ed6118520007e56118520006e56118520007e73118520007e43118520015ef701852000dee7018520015ed701852000dec701852008eef6018520217eb601852008fe7101
  | 9 => 0xc764852000cec7648520005ef7448520205ee7448520005ed7448520205ec7448520005ef734852004dee7348520005ed734852004dec7348520015ef7148520017e77148520007e76148520006ec6148520007e46148520006e46148520007eb704852000dee704852000dec704852009fe87048520016ef6048520017eb604852020dee75d9120005ed75d912004dee73d9120005ed73d912004dec73d9120007ae43d9120007ac43d9120005ee71d9120005ed71d9120015ef70d9120015ed70d9120266ef60d912026feb60d9120267af40d9120267ad40d9120145ed769912020dee7599120005ed7599120255ee7499120206ef6499120007af649912004dee7399120005ed739912004dec7399120005ee7199120005ed7199120155ed7099120207e97099120005e97099120156ef609912007feb6099120005ef75591200076f75591200056f755912020dec75591200076c75591200056c7559120007af6459120206ee6459120005ef7359120007cf7359120005cf735912004dee735912004dec7359120007cc735912004dcc7359120005ef7159120007e77159120005e77159120005ec7159120007e47159120005e47159120145ef7059120007eb7059120005eb7059120146ef6059120067eb6059120265ee761912020dee7519120005ed7519120155ee7419120206ef6419120207ae6419120206ed6419120007ad641912004dee7319120005ed731912004dec7319120007ae4319120207ac4319120005ee7119120005ed7119120015ef701912000dee7019120015ed701912000dec7019120256ef601912025feb6019120257af4019120257ad4019120205ef7695120005ee7695120005ed7695120205ec769512019ded75951200076f65951200076c6595120185ee749512020faf54951200072f549512004dee7395120005ed739512004dec7395120005ee7195120005ed71951201b5ef709512000dee70951201b5ed709512000dec70951201b6ef60951201bfeb60951201b76f50951201b76d5095120005ef7655120005ee7655120005ed7655120005ec76551202076e5455120005ef735512004dee735512004dec7355120005ef7155120005ec715512019def705512000dee705512019ded705512000dec705512019eef60551201a7eb6055120205ef7615120005ee7615120005ed7615120205ec76151201b5ee7415120007af6415120207ac6415120207ae541512020fad54151200072d541512004dee7315120005ed731512004dec7315120005ee7115120005ed7115120185ef701512000dee7015120185ed701512000dec7015120186ef601512018feb6015120187af4015120187ad401512024dee76d8d20205ee74d8d20005ed74d8d2013ded73d8d2004eee63d8d2004fce63d8d2004eec63d8d20
  | 10 => 0x920036ee6450920036ec6450920007ac6450920005ef735092004dee735092004dec7350920007af4350920007ad4350920005ef7150920005ec7150920007eb705092000dee705092000dec7050920147e87050920016ef6050920017eb605092000dec764c92001eec764c92000cec764c920005ef744c920205ee744c920005ed744c920205ec744c920015ef734c920017cf734c920007cf634c92001eee634c92001eec634c92004fcc634c920005ef714c920005ec714c920007eb704c92000dee704c92000dec704c92013fe8704c920016ef604c920017eb604c920034fe74d8520004fd74d852001cfe73d8520004fd73d852001cfc73d852000cfd72d85201eeed72d8520006f731d8520006f431d852021ef621d852021ef521d852021eec21d8520014fd70d85201eef710d8520006f76198520025f97098520005bf7458520005bc7458520005df735852004ddc735852003dfb7058520006f56118520034fe7418520004fd741852001cfe7318520004fd731852001cfc731852008eef721852000cfd721852008eed7218520006ef4218520216ee4218520006ed4218520216ec4218520006ef3218520216ee3218520006ed3218520216ec3218520006f73118520006f43118520216ef2118520216f62118520216f5211852008eec211852000cfe7018520014fd701852000cfc701852008eee201852008eec201852008ef51018520004fe76d0520004fd76d0520034fc76d0520015ee72d0520005ed72d0520015ec72d0520006f761d0520006f461d0520004fe7690520004fd7690520004fc7690520006bf6490520036bc6490520015ee7290520005ed7290520015ec7290520004ff7650520004fe7650520004fc76505200057f75505200057c7550520005ef7250520015ee7250520015ec7250520004fe7610520004fd7610520034fc7610520006bf6410520036bc6410520015ee7210520005ed7210520015ec7210520006f76110520006f4611052000dfa7010520005f97010520004fe768c520004fd768c520004fc768c520006df638c52001edc638c520015ee728c520005ed728c520015ec728c520004ff764c520004fe764c520004fc764c520005ef724c520015ee724c520015ec724c52000dee76885200aeee768852000cee7688520005ef7488520205ee7488520005ed7488520205ec7488520006ef64885201d6ee6488520006ed64885201d6ec6488520005ef738852004dee7388520005ed738852004dec7388520006ef63885200b6ee6388520006ed63885200b6ec6388520015ee7188520017e67188520006ef6188520007e76188520006ec6188520007e46188520006e4618852000dee70885200afea7088520007e9708852000dec7088520016ef6088520017eb608852000dec764852009ee
  | 11 => 0x67c75591200747c7559120006bf7459120004ff7359120006df7359120004df735912001cfe735912001cfc7359120006dc735912001cdc7359120154ff7259120006ef7259120066ec4259120004ff7159120006f77159120004f77159120004fc7159120006f47159120004f47159120066ec2159120144ff7059120006fb7059120264fe7619120036be6419120006bd6419120034ff7695120004fe7695120004fd7695120034fc76951200067f65951200767c65951200073f5495120015ee7295120005ed7295120015ec72951201bf6e52951201bf6c5295120004ff7655120004fe7655120004fd7655120004fc7655120005ef7255120015ee7255120015ec7255120034ff7615120004fe7615120004fd7615120034fc7615120006bf6415120036bc64151200073d5415120015ee7215120005ed7215120015ec721512018fae421512018fac421512001cfe76d8d2004ede63d8d20015ee72d8d2000ded72d8d2004fcf32d8d20034fe74d8d20004fd74d8d2013cfd73d8d2004edc43d8d2000cff72d8d20014fe72d8d2000cfd72d8d20236ed72d8d2000ced72d8d20014fc72d8d20246df32d8d2004eef32d8d20246dd32d8d20246ec32d8d20004fe71d8d20004fd71d8d2004edc31d8d20246ec21d8d20014ff70d8d20014fd70d8d20236df30d8d20236dd30d8d2001cff7658d20005bf7458d20005bc7458d2004edc6358d2023def7258d20005f77158d20005f47158d20275fb7058d20004ff7458d20006bf7458d20004bf7458d20034fc7458d20006bc7458d20034bc7458d20234ff7358d20006df7358d2023cff7258d20006ef7258d2004eef3258d2005eec3258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d2005eec2158d2013cff7058d20006fb7058d20034ff76d0d20004fe76d0d20004fd76d0d20034fc76d0d20036be64d0d20006bd64d0d20006df63d0d2001edc63d0d20015ee72d0d20005ed72d0d20015ec72d0d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20036be6450d20006bd6450d20005ef7250d20015ee7250d20015ec7250d2000dee76d0920156ee76d092000cee76d092020dee75d0920005ed75d0920205ec75d0920015ee74d0920017ae74d0920206ef64d0920007af64d0920206ed64d0920207ac64d092004dee73d0920005ed73d092004dec73d0920207af43d0920007ad43d0920005ee71d0920005ed71d092000dee70d0920157ea70d0920207e970d092000dec70d0920016ef60d0920017eb60d092000dec7650920036ec765092000cec7650920005ef75509200076f75509200056f755092020dee7550920005ed755092020dec75509200076c75509200056c7550920015ef7450920017af7450920007af645
  | 12 => 0xd73d0720055ec73d0720006ee61d0720125ef70d072000dee70d0720125ed70d072000dec70d0720127af40d0720127ad40d0720115ef7690720015ee7690720115ed7690720015ec7690720005ef7590720285ee7590720005ed7590720117ae6490720117ad6490720007af5490720007ac5490720055ee7390720005ed7390720055ec7390720007af4390720007ad4390720006ee6190720007af419072027fe7419072000dee709072010ded709072000dec709072010fae409072010fac40907200fdef7650720006ef7650720004ef7650720015ee76507200fded7650720015ec76507200feec7650720014ec7650720005ef75507200076f75507200056f7550720285ee7550720005ed7550720285ec75507200076c75507200056c7550720005ef7350720055ee7350720055ec7350720006ee615072027fe74150720007ae41507200f5ef705072000dee705072000dec70507200f7af40507200f7ad40507200e5ef7610720015ee76107200e5ed7610720015ec761072027def7510720285ee7510720005ed751072027dec75107200e7ae64107200e7ad6410720007af541072027fac5410720055ee7310720005ed7310720055ec731072027faf4310720007ad4310720006ee611072027faf411072027fe64110720007ad411072027fe541107200ddef701072000dee70107200dded701072000dec70107200dfae40107200dfac40107200d5ef768c720015ee768c7200d5ed768c720015ec768c720005ef748c72027dee748c720005ed748c72027dec748c7200d7ce638c7200d7cd638c7201e5ee718c720006ee618c720057cf318c720057e7318c720057e4318c72000dee708c7200cded708c72000dec708c7200cfce308c7200cfcc308c7200c5ef764c720006ef764c720004ef764c720015ee764c7200c5ed764c720015ec764c7200c6ec764c720014ec764c720005ef744c72027dee744c720005ed744c72027dec744c7201f5ef714c720006ee614c720057e7314c720007ce314c720057cc314c720057e4314c7200bdef704c72000dee704c72000dec704c7200bfcf304c7200bfcd304c720034fe76d9120074fe75d9120004fd75d912001cfe73d9120004fd73d912001cfc73d9120006be43d9120006bc43d912000cff72d9120014fe72d912000cfd72d9120266ed72d9120014fc72d912026ebf42d912026ebd42d912026eec42d9120004fe71d9120004fd71d912026eec21d9120014ff70d9120014fd70d9120266bf40d9120266bd40d9120144fd7699120006bf6499120145ed7299120065f97099120034ff76591200057f75591200057c7559120005df735912004ddc7359120155ef7259120005f77159120005f4715912007dfb7059120004ff75591200067f75591200047f7559120074fc7559120
  | 13 => 0x8530006ef6108530007e76108530006e76108530006ec6108530007e46108530006e46108530097cf3108530007cd310853008def700853008fea700853008ded700853005fe97008530005e9700853008eef6008530097eb300853008fce300853008fcc300853008fe830085301bdef7695320015ee76953201bded7695320015ec76953201bf6f65953201bf6c65953201bfae64953201bfad6495320287af54953200072f5495320055ee7395320005ed7395320055ec7395320005ee7195320005ed71953201b5ef709532000dee70953201b5ed709532000dec70953201b76f50953201b76d50953201a5ef7655320015ee76553201a5ed7655320015ec76553201a7ae64553201a7ad645532027f6e5455320005ef7355320055ee7355320055ec7355320005ef7155320005ec715532019def705532000dee705532019ded705532000dec705532018def7615320015ee761532018ded7615320015ec761532018faf641532018fac641532027fae5415320287ad54153200072d5415320055ee7315320005ed7315320055ec7315320005ee7115320005ed7115320185ef701532000dee7015320185ed701532000dec7015320187af4015320187ad401532017def76d0f20015ee76d0f2017ded76d0f20015ec76d0f20285ee75d0f20005ed75d0f2027dec75d0f2022dee74d0f2017fae64d0f2017fad64d0f20007af54d0f2027fac54d0f20057ae43d0f20057ce43d0f20057ac43d0f20005ee71d0f20005ed71d0f20175ef70d0f2000dee70d0f20175ed70d0f2000dec70d0f20177af40d0f20177ad40d0f2016def7650f20015ee7650f2016ded7650f20015ec7650f20005ef7550f20285ee7550f20005ed7550f20285ec7550f20225ef7450f2016fae6450f2016fad6450f20007af5450f20007ac5450f2016fce6350f2016fcd6350f2027fcf4350f20057ae4350f20057ac4350f20057cc4350f20005ef7150f20005ec7150f20165ef7050f2000dee7050f20165ed7050f2000dec7050f20167af4050f20167ad4050f20006ef7498720006ee7498720006ed7498720006ec7498720006ee5498720006ed5498720006ec5498720006ef7398720006ee7398720006ed7398720006ec7398720006ef4398720006ee4398720006ed4398720006ec4398720016ee7198720016e67198720006ef3198720006ec31987200aeef70987200aeed70987200aeef40987200aeee40987200aeed40987200aeec40987200aeef30987200aeee30987200aeed30987200aeec30987200aeee10987200aeed10987200aee510987200aeec109872012def76d0720015ee76d072012eee76d0720014ee76d072012ded76d072027eed76d0720004ed76d0720015ec76d0720285ee75d0720005ed75d072027dec75d0720055ee73d0720005e
  | 14 => 0x34ff7615130004fe7615130004fd7615130034fc7615130036be6415130006bd64151300073d541513001dde7315130005dd7315130014fe76d893005eee62d8930034fe74d8930004fd74d893000cfd73d8930014fc73d893005eee32d893028eed32d8930004fe71d8930004fd71d893005eec21d893001cfd70d893023eef20d8930005bf7458930005bc745893005eec6258930005f77158930005f47158930055fb7058930004fe76d0930004fd76d0930034fc76d0930004ff7650930004fe7650930004fc76509300057f75509300057c755093005dee72d8530005ed72d8530034fe74d8530004fd74d853000cfd73d8530014fe72d8530006ee72d8530014ee72d8530004fd72d8530006ed72d8530004ed72d8530014fc72d85301def631d85301def531d8530006f721d8530006f421d853001cfd70d85301f6ef20d85301f6ed20d85301f6f710d8530006f7619853002df97098530005bf7458530005bc7458530005ef725853005dec7258530045fb7058530006f56118530034fe7418530004fd741853000cfd73185301e6dd7318530014fe7218530004fd7218530014fc72185301fedf31185301fef631185301fef53118530006f72118530006f4211853001cfd70185301e6de30185301e6dc30185301e6ef20185301e6ed20185301e6f51018530004fe76d0530004fd76d0530034fc76d053005dee72d0530005ed72d0530004fe7690530004fd7690530004fc7690530006bf6490530036bc649053001dde7390530005dd7390530004ff7650530004fe7650530004fc76505300057f75505300057c7550530005ef725053005dec7250530004fe7610530004fd7610530034fc7610530006bf6410530036bc641053001dde7310530005dd731053000ddc764c5300bedc764c53000cdc764c530007cf724c530007cc724c53001ddf714c53001fd7714c530007d7614c530006dc614c530007d4614c530007db704c53000dde704c53000ddc704c5300bfd8704c53000dd8704c53001edf604c53001fdb604c530004fe7688530004fd7688530004fc768853001dde7388530005dd7388530006ef6288530016ee6288530016ec6288530006ef7688530006ee7688530006ed7688530006ec7688530006ef64885301d6ee6488530006ed64885301d6ec64885300b7ce7388530007cd73885300aeef638853008dee7188530006ef6188530006ec61885300b7cf3188530007cd31885300aded70885300aeef60885300b7eb30885300afce30885300afcc30885300afe83088530004ff7648530004fe7648530004fc7648530016ef760853005eee760853005eed7608530016ec7608530006ef64085301ceee6408530006ed64085301ceec640853005fce730853005fcd730853008eef63085300adee710853005fe6710
  | 15 => 0xc7250540035bf7150540037b77150540007b76150540006bc6150540007b46150540007bb705054000dbe705054000dbc70505400f7b87050540036bf6050540037bb6050540004fe768c540004fd768c540004fc768c540035be748c540005bd748c540006df638c54001edc638c540004ff764c540004fe764c540004fc764c540035be744c540005bd744c540005ef724c540065ec724c540004fe7688540004fd7688540004fc7688540035be7488540005bd7488540006ef6288540016ee6288540016ec6288540006ef7688540006ee7688540006ed7688540006ec7688540006ef65885402a6ee6588540006ed65885402a6ec6588540007ae7488540007ad74885400aeef6488540007af5488540007ac5488540006ef63885400b6ee63885400b6ec6388540007af4388540007ad438854008dee7188540006ef6188540006ec6188540007af4188540007ad41885400aded70885400aeef60885401d7eb40885400afae40885400afac40885400afe84088540004ff7648540004fe7648540004fc7648540016ef7608540066ee7608540066ed7608540016ec7608540006ef650854029eee6508540006ed650854029eec6508540067ae7408540067ad740854008eef6408540007af5408540007ac5408540006ef6308540096ee6308540096ec6308540007af4308540007ad43085400adee7108540067e67108540006ef6108540007e76108540006e76108540006ec6108540007e46108540006e46108540007af4108540007ad410854008def700854008fea700854008ded7008540067e97008540005e9700854008eef60085401cfeb400854008fae400854008fac400854008fe84008540034fe76d91300057e75d91300057d75d9130074fe75d91300067e75d91300747e75d9130004fd75d91300067d75d91300047d75d913000cff73d913001cfe73d913000cfd73d913001cfc73d9130296bf43d9130296bd43d9130014fe72d9130004fd72d9130014fc72d9130006be42d9130006bc42d9130004fe71d9130004fd71d913001cff70d913001cfd70d9130226bf40d9130226bd40d9130226ef20d9130226ed20d9130164fd76991300057e75991300057d7599130006bf6499130165dd739913006df97099130034ff7659130175df7359130085fb7059130004ff7559130074fc7559130006bf7459130174ff7359130006df7359130004ff7259130014fe7259130014fc7259130004ff7159130004fc7159130164ff7059130006fb7059130224fe7619130036be6419130006bd6419130034ff7695130004fe7695130004fd7695130034fc76951300767e65951300067d6595130006bf6495130036bc64951300073f5495130004ff7655130004fe7655130004fd7655130004fc7655130006bf6455130036bc6455130
  | 16 => 0xd4001ebe6350d4001ebc6350d4006f9c6350d4001e9c6350d40005bf7150d40007bb7050d4000dbe7050d4000dbc7050d40167b87050d40036bf6050d40037bb6050d40014fe76d8940066ee62d8940074fe75d8940004fd75d894000cfd74d8940014fc74d894001cfe73d8940004fd73d894001cfc73d8940006bf43d8940006bd43d8940066ee42d8940004fe71d8940004fd71d8940066ec21d8940034fd70d8940156ef20d89400057f75589400057c7558940005df735894006ddc7358940066ec6258940005f77158940005f47158940004fe76d4940004fd76d4940074fc76d4940004ff7654940004fe7654940004fc7654940005bf7454940035bc745494000cfc76509400057f75509400057c7550940006ef6250940016ec6250940037ac4250940005fb705094000df87050940004ff764c940004fe764c940004fc764c940065ee72d8540005ed72d8540074fe75d8540004fd75d854001cfe73d8540004fd73d854001cfc73d8540014fe72d8540006ee72d8540014ee72d8540004fd72d8540006ed72d8540004ed72d8540014fc72d8540006f721d8540006f421d8540034fd70d8540126ef20d8540126ed20d8540126f710d8540006f761985400057f75585400057c7558540005df735854006ddc7358540005ef7258540065ec7258540006f56118540074fe7518540004fd75185400debd7418540006bf5418540006bc541854001cfe7318540004fd731854001cfc7318540006bf4318540006bd4318540014fe7218540004fd7218540014fc7218540006f72118540006f42118540034fd70185400debe40185400debc40185400deef20185400deed20185400def51018540004fe76d4540004fd76d4540074fc76d4540065ee72d4540005ed72d4540004fe7694540004fd7694540004fc76945400067f65945400767c6594540035be7494540005bd74945400073c5494540004ff7654540004fe7654540004fc7654540005bf7454540035bc7454540005ef7254540065ec7254540004fe7614540004fd7614540074fc76145400067f65145400767c6514540035be7414540005bd74145402af3c54145400ddbe76d0540036be76d05400dcbe76d05402adbe75d0540035bc75d0540005bd73d0540037ae72d0540037ad72d0540006bc61d054000dbe70d054000dbc70d0540036bf60d0540037bb60d054000cfe76905400f5bd749054010ebf6490540006f76190540006f4619054000dfa7090540005f9709054000cfc76505400057f75505400057c7550540005ef7250540065ec7250540006f76150540006f46150540005fb705054000df8705054000dbc76505400f6bc765054000cbc76505400073f75505402adbe75505402adbc75505400073c75505400053c7550540005bf7350540007af7250540007a
  | 17 => 0x6ee6108740006ed61087401cfaf4108740007ad410874008def700874008ded700874008fae400874008fea400874008fac4008740074fe76d9540034fe74d95401b6bd74d9540034fc74d954001cfe73d9540004fd73d954001cfc73d9540014fe72d9540004fd72d9540014fc72d95400067e52d95400067c52d9540004fe71d9540004fd71d9540034fd70d95401b67f50d95401b6ef20d95401b6ed20d95400067f659954019dbd749954006dde7399540005dd73995402cdbf7459540006bf7459540004ff735954001cfe735954001cfc7359540004ff7259540014fe7259540014fc7259540004ff7159540004fc715954019cff7059540006fb70595401b4fe76195400767e65195400067d651954000cfe76d514000cfc76d51400067f65d51400767c65d51400373e54d514000dfa70d5140005f970d514000dbe76d51402cebe76d514000cbe76d5140035be75d51402aebf65d51400073f65d51400063f65d51402aebd65d51402af3c65d5140005bd73d51402d6be62d51402d6bc62d5140005bd71d514000dbe70d51402cfba70d51402afb970d514000dbc70d5140036bf60d5140037bb60d5140074ff765514000cfe765514019cfd765514000cfc76551400067f65551400767c65551400373c5455140005fb705514000df870551401b5be7615140036be76151402cdbe75151400373e75151402aebf65151402af3e65151402aebd65151400073d65151400063d6515140005bd731514018ebe621514018ebc62151402c73e52151402af3c5215140005bd711514000dbe701514000dbc7015140036bf6015140037bb60151401873f50151401873d501514001cfe76d8d4006ede63d8d40074fe75d8d40004fd75d8d4000cfd74d8d4001cfc74d8d40006bf54d8d40006bc54d8d4006ede53d8d4006ede43d8d40014fe72d8d40004fd72d8d40014fc72d8d40006de32d8d4006edc32d8d40004fe71d8d40004fd71d8d4006edc31d8d40034fd70d8d40176df30d8d40176ef20d8d40176ed20d8d4006edc6358d40004fe76d4d40004fd76d4d40074fc76d4d400067f65d4d400767c65d4d402af3c54d4d4006f5e53d4d40004ff7654d40004fe7654d40004fc7654d400067f6554d400767c6554d40005bf7454d40035bc7454d400073c5454d40006df6354d4001edc6354d4022dbe76d0d40036be76d0d402adbe75d0d40035bc75d0d402bebe65d0d402bebc65d0d40165bd73d0d4001ebe63d0d4001ebc63d0d40005bd71d0d4000dbe70d0d4000dbc70d0d40036bf60d0d40037bb60d0d4000cfc7650d40006df6350d4001edc6350d40005fb7050d4000df87050d4000dbc7650d4001ebc7650d4000cbc7650d402adbe7550d402adbc7550d402b6be6550d402b6bc6550d40035bf7350d400379f7350d400079f635
  | 18 => 0xe65d4b400067d65d4b40004ff7654b40004fd7654b40034fc7654b400767e6554b400067d6554b40005bf7454b40035bc7454b40004ff764cb40004fd764cb40034fc764cb4001ede634cb40006dd634cb40074fe7598740004fd759874000cfe7498740036be749874000cbe7498740006bf5498740036bc549874001cfe7398740004fd739874001cfc7398740036bf4398740006bd4398740014fe7298740004fd7298740014fc7298740036f67198740036bf4198740036f74198740036f4419874010ebe4098740036bc409874010eef209874010eed209874010ef51098740004ff7558740074fc755874000cfc7458740004ff735874001cfe735874001cfc7358740004ff7258740006ef7258740004ef7258740014fe7258740014fc7258740006ec7258740014ec7258740036f77158740036f74158740036f441587400f6ef20587400f6ed20587400f6f71058740074ff76d4740034fe76d4740004fd76d4740035bc74d474007dee72d4740005ed72d4740004ff7694740034fe7694740004fd76947400767e65947400067d6594740035be7494740005bd74947402ef3c5494740004ff7654740004fd7654740034fc7654740005bf7454740035bc7454740005ef725474007dec7254740074ff7614740034fe7614740004fd76147400767e65147400067d6514740035be7414740005bd74147402e73c5414740035bf7650740006bf765074010cbf76507400073f75507402ddbe75507402ddbc75507400073c75507400053c7550740005bf7350740007af7250740007ac7250740037b77150740006be615074000dbe705074000dbc7050740004ff768c740034fe768c740004fd768c740035be748c740005bd748c74001ede638c740006dd638c740004ff764c740004fd764c740034fc764c740035be744c740005bd744c740005ef724c74007dec724c740005fb704c74000df8704c740004ff7688740034fe7688740004fd7688740035be7488740005bd7488740016ee6288740006ed6288740016ec6288740006ef76887401d6ee7688740006ed76887401d6ec76887402a6ee6588740006ed65887401d6ec65887401d7ae7488740007ad74887400aeee6488740007af54887401d7ac54887400b6ee6388740006ed63887400b6ec63887401d7af4388740007ad4388740006ee6188740006ed61887401d7af4188740007ad41887400aded70887400afae40887400afea40887400afac4088740004ff7648740004fd7648740034fc7648740016ef760874007eee760874007eed7608740016ec760874029eee6508740006ed65087401ceec650874007fae740874007fad740874008eee6408740007af54087401cfac5408740096ee6308740006ed6308740096ec63087401cfaf4308740007ad430874007fe67108740
  | 19 => 0xc4210d7e6618c421007e7418c421007e4418c421097cf318c421097e7318c421097e4318c42108dee708c421005ed708c42108dec708c421317ce308c421097cc308c4210c5ef764c4210b6ef764c4210b4ef764c421005ef744c4211cdee744c421005ed744c4211cdec744c4210d5ef734c42130def714c4210b6ee614c4210c7e6614c421007e7414c421007e4414c421097e7314c421007ce314c421097cc314c421097e4314c421097c4314c421005ef704c42108dee704c42108dec704c421097cf304c421006ef7458021006ee7458021006ed7458021006ec7458021006ee5458021006ed5458021006ec5458021006ef7358021006ee7358021006ed7358021006ec7358021006ef4358021006ee4358021006ed4358021006ec4358021006ee7158021006ef4158021006ee4158021006ed4158021006ec4158021006ef3158021006ee3158021006ed3158021006ec3158021016ef7058021016eb705802108eee405802108eea405802108eec405802108eef305802108eee305802108eea305802108eec305802108eee105802108eec105802108ee810580210367f7559740034fd745974000cfc7459740036bc745974000cbc74597400367e54597400367c5459740036bc54597400363c5459740004ff735974001cfe735974001cfc73597400067e53597400067c5359740004ff7259740014fe7259740014fc7259740004ff7159740004fc715974019e7f505974019eef205974019eed2059740035bd76d53402debd76d53400373e75d5340036bf65d53402debd65d5340005bd73d53402d6be62d5340036bc62d5340005bd71d534000dbe70d534000dbc70d5340004ff7558f40074fc7558f4000cfe7458f4001cfd7458f4000cfc7458f40006bf5458f40036bc5458f40036df7358f40086dc5358f40036df4358f40036dc4358f40004ff7258f40014fe7258f40014fc7258f40086df3258f40004ff7158f40004fc7158f40086dc3158f40166df3058f40166ef2058f40166ed2058f40074ff76d4f40034fe76d4f40004fd76d4f400767c65d4f40035bc74d4f403073c54d4f4001ede63d4f40006dd63d4f400875e53d4f40004ff7654f40004fd7654f40034fc7654f40005bf7454f40035bc7454f402ff3c5454f40035bf7650f402f6bf7650f402ddbe7550f402ddbc7550f402b6be6550f40036bc6550f400379f7350f4001ebe6350f4001ebc6350f40005bf7150f4000dbe7050f4000dbc7050f40004ff7558b40074fc7558b4000cfe7458b40014fd7458b4000cfc7458b40004ff7358b4001cfe7358b4001cfc7358b40036bf4358b40006bd4358b40036ef7258b40036ef4258b40036ec4258b40004ff7158b40004fc7158b4007eec2158b40146ef2058b40074ff76d4b40034fe76d4b40004fd76d4b400767
  | 20 => 0x1cdec75d0c21345ee74d0c2117fae64d0c2117fad64d0c21007af54d0c211cfac54d0c2116ded73d0c21097ae43d0c21097ce43d0c21097ac43d0c21005ee71d0c21005ed71d0c2117fe661d0c2108dee70d0c21005ed70d0c2108dec70d0c2116def7650c21015ee7650c2116ded7650c21015ec7650c21005ef7550c2129dee7550c21005ed7550c2129dec7550c2133def7450c2116fae6450c2116fad6450c21007af5450c21007ac5450c2117def7350c2116fce6350c2116fcd6350c211cfcf4350c21097ae4350c21097ac4350c21097cc4350c21005ef7150c21005ec7150c2116fe66150c21005ef7050c2108dee7050c2108dec7050c21006ef74984211d6ee7498421006ed74984211d6ec74984211d6ee5498421006ed54984211d6ec54984210b6ef73984210b6ee73984210b6ed73984210b6ec73984210b6ef43984210b6ee43984210b6ed43984210b6ec4398421016ee7198421016e671984210b6ef31984210b6ec31984210aeee70984210aeed70984210aeec309842112ded76d04211ceed76d0421004ed76d042129dee75d0421005ed75d04211cdec75d0421095ee73d0421005ed73d0421095ec73d04211d6ee61d042112fe661d042108dee70d0421005ed70d042108dec70d0421337e610d0421337e410d0421115ef7690421115ed7690421005ef759042129dee7590421005ed75904210fded7490421117ae6490421117ad6490421007af5490421007ac5490421095ee7390421005ed7390421095ec7390421007af4390421007ad43904210e5ee7190421006ee6190421117e66190421007af41904211cfe7419042108dee7090421005ed709042108dec709042132fae409042132fac40904210fdef7650421006ef7650421004ef7650421005ef75504210076f75504210056f755042129dee7550421005ed755042129dec75504210076c75504210056c7550421005ef7350421095ee7350421095ec7350421006ee61504210ffe661504211cfe74150421007ae4150421005ef705042108dee705042108dec70504210e5ef7610421015ee76104210e5ed7610421015ec76104211cdef751042129dee7510421005ed75104211cdec751042112dee74104210e7ae64104210e7ad6410421007af54104211cfac5410421095ee7310421005ed7310421095ec73104211cfaf4310421007ad4310421115ee71104211d6ee61104210e7e661104211cfaf41104211cfe64110421007ad41104211cfe5411042108dee7010421005ed701042108dec7010421327ae40104211cfac4010421327e61010421327e410104210d5ef768c421015ee768c4210d5ed768c421015ec768c421005ef748c4211cdee748c421005ed748c4211cdec748c4210c5ed738c4210d7ce638c4210d7cd638c42131dee718c4210b6ee618
  | 21 => 0xe63d8d21034fe74d8d21004fd74d8d210d4ff72d8d210d4fd72d8d210d6df32d8d210d6dd32d8d21014fd71d8d210a6df31d8d210d6ec21d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d210a6dc30d8d210d6ef20d8d210a6dc6358d2130df77158d21004ff7458d21034fc7458d210d4ff7358d21006df7358d210c4ff7258d21006ef7258d210b4ef7258d2130cff7158d21006f77158d210c6ec2158d21004ff7058d2100cfe7058d2100cfc7058d210c6ef2058d21034ff76d0d21004fe76d0d21004fd76d0d21034fc76d0d21006bf64d0d21036bc64d0d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d21036bc6450d21014fe76d0521014fc76d0521006bf64d0521036bc64d0521015ee72d0521005ed72d05210e4fe7690521034ff7650521014fe76505210fcfd7650521014fc76505210057f75505210057c7550521006bf6450521036bc6450521005ef7250521015ec7250521114fe761052131cfe768c5210d7e4218c52101cff764c521014fe764c5210c4fd764c521014fc764c521006df634c52101edc634c521005ef724c521015ec724c5210c7e4214c521006ef64885211d6ee6488521006ed64885211d6ec6488521006ef63885210b6ee6388521006ed63885210b6ec6388521015ee7188521017e67188521016ef6188521017e76188521005ed70885210aeee60885210aeec608852100cfe76d812109efa60d8121034fe74d8121004fd74d812101cfe73d8121004fd73d812101cfc73d8121006ef72d812100cfc72d812100cec72d8121014fd71d8121006ee21d812103eec21d812109eef20d812109efa20d812109efa10d8121005bf7458121005bc7458121005df73581210a5dc735812109ef860581211bdef7695021015ee76950211bded7695021015ec76950211a5ed75950211bf6f65950211bf6c659502118dee74950211bfae64950211bfad649502129faf54950210072f5495021095ee7395021005ed7395021095ec7395021005ee7195021005ed71950211bfe6619502108dee7095021005ed709502108dec70950211a5ef7655021015ee76550211a5ed7655021015ec76550211a7ae64550211a7ad64550211cf6e5455021005ef7355021095ee7355021095ec7355021005ef7155021005ec71550211a7e66155021005ef705502108dee705502108dec705502118def7615021015ee761502118ded7615021015ec76150211bdee741502118faf641502118fac64150211cfae541502129fad54150210072d5415021095ee7315021005ed7315021095ec7315021005ee7115021005ed711502118fe6611502108dee7015021005ed701502108dec701502117def76d0c21015ee76d0c2117ded76d0c21015ec76d0c2129dee75d0c21005ed75d0c21
  | 22 => 0x6210adec7010621357ae40106211d7ac4010621015ef768c621015ed768c621005ef748c6211d5ee748c621005ed748c6211d5ec748c6210b7ce638c621007cd638c6210b7cf318c6210b7e7318c6210b7e4318c6210adee708c621005ed708c6210adec708c62134fce308c6210b7cc308c621005ef764c621096ef764c621094ef764c621005ef744c6211d5ee744c621005ed744c6211d5ec744c6210b7e7314c621007ce314c6210b7cc314c6210b7e4314c621005ef704c6210adee704c6210adec704c6210b7cf304c6211d5ee74d8221005ed74d8221006ef64d8221006ee64d8221006ed64d8221006ec64d82210b5ee73d8221005ed73d82210b5ec73d8221006ef63d8221006ee63d8221006ed63d8221006ec63d8221007e671d822103fe661d82210aeee60d82210afea60d82210aeec60d8221005ef74582211d5ec7458221006ef6458221006ee6458221006ed6458221006ec6458221005ef73582210b5ee73582210b5ec7358221006ef6358221006ee6358221006ed6358221006ec6358221015ec7158221026ee6158221027e66158221007eb60582210aeee60582210aeec60582210afe860582210afe81058221006ef7458221006ee7458221006ed7458221006ec7458221006ee5458221006ed5458221006ec5458221006ef7358221006ee7358221006ed7358221006ec7358221006ef4358221006ee4358221006ed4358221006ec4358221026ee7158221014ec7158221006ef4158221006ee4158221006ed4158221006ec4158221006ef3158221006ee3158221006ed3158221006ec31582210aeee40582210aeec40582210aeef30582210aeee30582210aeec30582210aeee10582210aeec10582210aee81058221034fe76d9121074fe75d9121004fd75d912101cfe73d9121004fd73d912101cfc73d9121114ff72d9121114fd72d9121116bf42d9121116bd42d9121116ec21d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121006bc40d9121116ef20d9121006bf64991210fdf571991210057f75591210057c755912112df77159121004ff75591210067f75591210047f7559121074fc75591210067c75591210747c7559121006bf7459121004ff735912101cfe735912101cfc73591210fcff7259121006ef7259121004ef725912112cff7159121006f771591210feec2159121004ff705912100cfe705912100cfc70591210feef2059121114fe7619121036be6419121006bd6419121034ff7695121004fe7695121004fd7695121034fc76951210067f65951210767c65951210073f5495121004ff7655121004fe7655121004fd7655121004fc7655121034ff7615121004fe7615121004fd7615121034fc7615121006bf6415121036bc64151210073d541512101cfe76d8d210a6d
  | 23 => 0x5ec76552211d76e5455221005ef73552210b5ee73552210b5ec7355221005ef7155221005ec7155221005ef70552210adee70552210adec70552211d5ef7615221005ee7615221005ed76152211d5ec76152211d7ae6415221007ad64152211d7ae54152212a7ad54152210072d54152210b5ee7315221005ed73152210b5ec7315221005ee7115221005ed71152210adee7015221005ed70152210adec70152211d5ee74d8e21007ae74d8e21005ae74d8e21005ed74d8e21007ad74d8e21005ad74d8e210b6ee63d8e210b7ce63d8e210b6ec63d8e21005ee71d8e21007e671d8e21005e671d8e210d7e661d8e210adee70d8e21005ed70d8e210adec70d8e21005ef7458e211d5ec7458e21007cf6358e210b6ee6358e210b6ec6358e210b7cc6358e210b7cc4358e21015ec7158e210c6ee6158e210c7e66158e210b7cc3158e21005ef7058e210adee7058e210adec7058e210b7cf3058e211d5ef76d0e21005ee76d0e21005ed76d0e211d5ec76d0e212a5ee75d0e21005ed75d0e211d5ec75d0e21007af64d0e211d7ac64d0e21007af54d0e211d7ac54d0e210b7ce63d0e21007cd63d0e210b7ae43d0e210b7ce43d0e210b7ac43d0e21005ee71d0e21005ed71d0e210adee70d0e21005ed70d0e210adec70d0e21005ef7650e21005ee7650e21005ed7650e21005ec7650e21005ef7550e212a5ee7550e21005ed7550e212a5ec7550e21007af6450e21007ac6450e21007af5450e21007ac5450e211d7cf4350e210b7ae4350e210b7ac4350e210b7cc4350e21005ef7150e21005ec7150e21005ef7050e210adee7050e210adec7050e21005ed76d06211d6ed76d06212a5ee75d0621005ed75d06211d5ec75d06210b5ee73d0621005ed73d06210b5ec73d06210adee70d0621005ed70d06210adec70d0621015ef7690621015ed7690621005ef75906212a5ee7590621005ed7590621007ae6490621007ad6490621007af5490621007ac54906210b5ee7390621005ed73906210b5ec7390621007af4390621007ad4390621007af41906211d7e741906210adee7090621005ed70906210adec709062135fae409062135fac4090621005ef7650621006ef7650621005ef75506210076f75506210056f75506212a5ee7550621005ed75506212a5ec75506210076c75506210056c7550621005ef73506210b5ee73506210b5ec73506211d7e74150621007ae4150621005ef70506210adee70506210adec7050621015ef7610621015ed76106211d5ef75106212a5ee7510621005ed75106211d5ec75106211d7ae6410621007ad6410621007af54106211d7ac54106210b5ee7310621005ed73106210b5ec73106211d7af4310621007ad43106211d7af41106211d7e64110621007ad41106211d7e541106210adee7010621005ed701
  | 24 => 0x77150a21007e47150a21016ee6150a21017e66150a21005ef7050a210adee7050a210adec7050a210b5ef764ca2101eef764ca2101cef764ca21005ef744ca211d5ee744ca21005ed744ca211d5ec744ca21015ef734ca21017cf734ca2101eee634ca210b7ce634ca21007cd634ca2101eec634ca21005ef714ca21007e7714ca21007e4714ca21016ee614ca21017e6614ca21005ef704ca210adee704ca210adec704ca210fcfd76d0621015ee72d0621005ed72d0621015ec72d0621014ff7690621014fd7690621036be6490621006bd6490621015ee7290621005ed729062112cff76506210057f75506210057c7550621005ef7250621015ee7250621015ec7250621014ff7610621014fd7610621034fc7610621036be6410621006bd6410621015ee7210621005ed7210621014ff768c62101cfe768c621014fd768c62101ede638c621006dd638c621015ee728c621005ed728c62130cff764c6210b5ef724c621015ee724c621015ec724c6210aefa60d822100cff7658221015ec72582210aef860582210afea2058221004ff7458221034fc7458221004ff735822101cfe735822101cfc7358221006ed7258221006ef4258221026ee4258221006ed4258221026ec4258221006ef3258221026ee3258221006ed3258221026ec3258221014fc7158221026ef21582210aeef20582210aeee20582210aefa20582210aeec20582210aef810582212a5ee75d92210076e75d92210056e75d9221005ed75d92210076d75d92210056d75d92210b5ee73d9221007ce73d92210b5ce73d9221005ed73d9221007cd73d9221005cd73d92210b5ec73d9221005ee71d9221007e671d9221005e671d9221117e661d92210adee70d9221005ed70d92210adec70d92212a5ee7599221005ed75992211d6ef6499221007af64992210b5ee7399221005ed73992210b5ec7399221007ae43992211d7ac439922112eee619922112fe661992210adee7099221005ed70992210adec7099221005ef75592212a5ec7559221007af64592211d6ee6459221005ef73592210b5ee73592210b5ec7359221007ae4359221007ac43592210feee61592210ffe66159221005ef70592210adee70592210adec70592212a5ee7519221005ed75192211d6ef64192211d7ae64192211d6ed6419221007ad64192210b5ee7319221005ed73192210b5ec7319221005ee71192211d7e67119221005e671192210e7e661192210adee7019221005ed70192210adec70192211d5ef7695221005ee7695221005ed76952211d5ec76952210076e65952210076d65952212a7af54952210072f54952210b5ee7395221005ed73952210b5ec7395221005ee7195221005ed71952210adee7095221005ed70952210adec7095221005ef7655221005ee7655221005ed7655221
  | 25 => 0x9221004fd73d9221006dd73d9221004dd73d922101cfc73d9221006ed72d9221116ec42d92210e4fe71d9221006f671d922100cfe70d9221004fd70d922100cfc70d9221116ef20d92210fcfd7699221006bf6499221034ff7659221004ff7559221074fc7559221006bf7459221004ff735922101cfe735922101cfc7359221006be4359221006bc4359221006ef72592210febf42592210febd42592210feec4259221004ff705922100cfe705922100cfc70592210feef2059221036be6419221006bd6419221115f67119221034ff7695221004fe7695221004fd7695221034fc76952210767e65952210067d65952210073f5495221015ee7295221005ed7295221015ec72952211bf6e52952211bf6c5295221004ff7655221004fe7655221004fd7655221004fc7655221005ef7255221015ee7255221015ec7255221034ff7615221004fe7615221004fd7615221034fc7615221036be6415221006bd64152210073d5415221015ee7215221005ed7215221015ec721522118fae421522118fac4215221005be74d8e21005bd74d8e210b6de63d8e2131df671d8e21034fe74d8e21006be74d8e21034be74d8e21004fd74d8e21006bd74d8e21004bd74d8e210c4fd73d8e21006ed72d8e210b6ef32d8e210d6ec32d8e2131cfe71d8e21006f671d8e2100cfe70d8e21004fd70d8e2100cfc70d8e210d6ef20d8e2101cff7658e210b6dc6358e21015ec7258e210b7cf3258e21004ff7458e21034fc7458e21006df7358e210b6dc4358e210b6ef7258e210c6df3258e210b6ef3258e210c6dd3258e210c6ec3258e21014fc7158e210b6dc3158e21004ff7058e2100cfe7058e2100cfc7058e210b6df3058e210c6ef2058e21034ff76d0e21004fe76d0e21004fd76d0e21034fc76d0e21006bf64d0e21036bc64d0e2101ede63d0e21006dd63d0e21015ee72d0e21005ed72d0e21015ec72d0e21004ff7650e21004fe7650e21004fd7650e21004fc7650e21006bf6450e21036bc6450e21005ef7250e21015ee7250e21015ec7250e211d6ed76d0a212a5ee75d0a21005ed75d0a211d5ec75d0a21015ee74d0a21017ae74d0a211d6ef64d0a211d7ae64d0a211d6ed64d0a21007ad64d0a210b5ee73d0a21005ed73d0a210b5ec73d0a211d7af43d0a21007ad43d0a211d7e671d0a21005ed71d0a211d7e571d0a21016ee61d0a21017e661d0a210adee70d0a21005ed70d0a210adec70d0a21036ef7650a21034ef7650a21005ef7550a210076f7550a210056f7550a212a5ee7550a21005ed7550a212a5ec7550a210076c7550a210056c7550a21015ef7450a21017af7450a21036ee6450a21007ae6450a21007ad6450a21036ec6450a21005ef7350a210b5ee7350a210b5ec7350a21007af4350a21007ad4350a21005ef7150a21007e
  | 26 => 0xc6ee32d89310b6ed32d893101cfd71d89310c6ef21d893100cfe70d8931004fd70d893100cfc70d89310c6ef20d8931006ee20d89310c6ec20d89310c5ee76d8931014ee76d8931006ef64d8931006ee64d8931006ed64d8931006ec64d89310b7e731d89310b7cc31d89310b7e431d8931005ed70d8931006ee60d8931006ec60d89310b7cf30d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ee54d8931006ed54d8931006ec54d89310b6ef73d89310c6ee73d89310b6ec73d89310b6ef43d89310b6ee43d89310b6ed43d89310b6ec43d89310b6ef71d89310c6ee71d89310b6ed71d89310b6ef31d89310b6ee31d89310b6ec31d8931006ef70d8931006ee70d8931006ed70d8931004ed70d8931006ec70d8931006ee40d8931006ec40d89310b6ef30d89310b6ee30d89310b6ed30d89310b6ec30d8931006ee10d8931006ec10d89310c6ec6258931365f771589310b5ee76189310c6ee7618931006ef6418931006ee6418931006ed6418931006ec64189310d6ef631893130eef6118931097e73118931097cc3118931097e43118931005ed7018931006ee6018931006ec6018931097cf3018931004fe76d0931004fd76d0931034fc76d0931006ef62d0931016ec62d0931004ff7650931004fe7650931004fc76509310057f75509310057c7550931005df735093101ddc7350931006ef6250931016ec6250931005f77150931005f4715093101cfe76d053101cfc76d0531006bf64d0531036bc64d053101dde73d0531005dd73d05310c5ee72d0531005ed72d0531006ef62d053112eec62d0531137d431d05310ecfe7690531036be6490531006bd6490531006ef6290531116ec6290531034ff765053101cfe7650531104fd765053101cfc76505310057f75505310057c7550531006bf6450531036bc6450531005df735053101ddc7350531005ef72505310c5ec7250531006ef62505310feec625053111cfe7610531036be6410531006bd6410531006ef62105310e6ec62105310efd43110531007cf628c531007cc628c53101dde718c53101fd6718c53101edf618c53101fd7618c531005dd708c5310cede608c5310cedc608c53100cfe76d8131006ef62d8131006ec62d81310befa60d8131034fe74d8131004fd74d813100cfc73d8131006ef72d8131014fe72d8131004fd72d8131014fc72d8131006ec72d813101cfd71d81310bef840d81310befa30d81310befa10d8131005bf7458131005bc7458131005ef72581310c5ec7258131006ef6258131006ec62581310bef860581310057e75d92210057d75d92210b5de73d9221005dd73d92210e5f671d9221074fe75d92210067e75d92210747e75d9221004fd75d92210067d75d92210047d75d922101cfe73d9221006de73d922101cde73d
  | 27 => 0x67119231034ff7695231004fe7695231004fd7695231034fc76952310067f65952310767c6595231036be6495231006bd64952310073f5495231004ff7655231004fe7655231004fd7655231004fc7655231036be6455231006bd6455231034ff7615231004fe7615231004fd7615231034fc7615231006bf6415231036bc64152310073d541523101dde7315231005dd7315231005be74d8a31005bd74d8a310d6ee62d8a31095f671d8a31014ff7658a310d6ec6258a31004ff7458a31034fc7458a310d6ee3258a310a6ed3258a3101cfc7158a310d6ec2158a31004ff7058a3100cfe7058a3100cfc7058a310d6ef2058a31034ff76d0a31004fe76d0a31004fd76d0a31004ff7650a31004fd7650a31004fc7650a310057f7550a310057c7550a31005f77150a31005f47150a31104fd76d06310d5ee72d0631005ed72d063101cff769063101cfd7690631036be6490631006bd649063101dde7390631005dd7390631134ff76506310057f75506310057c7550631005ef72506310d5ec725063101cff761063101cfd7610631034fc7610631036be6410631006bd641063101dde7310631005dd73106310cefa60d823100cff765823101ddc73582310cef860582310cfda3058231004ff7458231034fc7458231004ff7258231014fe7258231014fc725823101cfc715823102edf31582310cede30582310cefa30582310cedc30582310cef81058231034fe76d9131074fe75d9131004fd75d913111cff73d913111cfd73d913111ebf43d913111ebd43d9131014fe72d9131004fd72d9131014fc72d913100cfe70d9131004fd70d913100cfc70d9131006be40d9131006bc40d9131006bf64991310c5ee7299131005ed7299131105f571991310057f75591310057c7559131005ef72591310c5ec7259131135f77159131005fb70591310bdf87059131004ff75591310067f75591310047f7559131074fc75591310067c75591310747c7559131006bf7459131104ff7359131006df7359131004ff7259131006ef7259131004ef7259131014fe7259131014fc7259131006ec7259131014ec7259131134ff7159131006f77159131004ff7059131006fb7059131004fb705913100cfe705913100cfc7059131006f8705913100cf8705913111cfe7619131036be6419131006bd6419131034ff7695131004fe7695131004fd7695131034fc76951310067f65951310767c65951310073f549513101dde7395131005dd73951311beec6295131004ff7655131004fe7655131004fd7655131004fc76551311a6ec6255131034ff7615131004fe7615131004fd7615131034fc7615131006bf6415131036bc64151310073d541513118eec6215131014fe76d89310c6ee62d8931034fe74d8931004fd74d89310c6ee42d89310c6ec42d8931
  | 28 => 0x4c4101ede63d4c41006dd63d4c410ef5e53d4c41004ff7654c41004fd7654c41034fc7654c412fe7f6554c41005bf7454c41035bc7454c412ff3c5454c41035bf7650c41136bf7650c4136dbe7550c4136dbc7550c412b6be6550c41036bc6550c41035bf7350c410379f7350c4101ebe6350c4101ebc6350c41005bf7150c41037b66150c410ddbe7050c410ddbc7050c41004ff7558841074fc7558841004ff735884101cfe735884101cfc7358841036bf4358841006bd4358841036ef7258841036ef4258841036ec42588410e6ec2158841004ff705884100cfe705884100cfc70588410e6ef2058841074ff76d4841034fe76d4841004fd76d48410767e65d48410067d65d4841004ff7654841004fd7654841034fc76548410767e65548410067d6554841005bf7454841035bc7454841004ff764c841004fd764c841034fc764c84101ede634c841006dd634c841074fe7598441004fd7598441376bf5498441036bc549844101cfe7398441036bf439844111ebd4398441014fe7298441036bf4198441036f74198441036f4419844100cfe7098441036bc4098441004fd76d4441035bc74d44410e5ee72d4441005ed72d4441004ff7694441074fd76944410767e65944410067d6594441035be7494441005bd74944412ef3c5494441004ff7654441005bf7454441035bc7454441005ef72544410e5ec7254441034fe7614441004fd7614441034fc7614441035be7414441005bd74144412e73c5414441035bf7650441006bf7650441004bf76504410073f755044136dbe755044136dbc75504410073c75504410053c7550441005bf7350441007af7250441007ac7250441035bf7150441037b77150441006be6150441037b66150441007b65150441007b551504410ddbe70504410ddbc7050441004ff7558041074fc755804100cfd7458041006bf5458041036bc5458041004ff735804101cfe735804101cfc7358041036bf4358041006bd4358041004ff7258041014fe7258041014fc7258041036bf4158041006bd4158041036fb7058041036fb40580410debe4058041036bc4058041036f840580410defa20580410def810580410edf671d9231074fe75d9231004fd75d9231006dd73d9231014fe72d9231004fd72d9231014fc72d92310ecfe71d9231006f671d923100cfe70d9231004fd70d923100cfc70d9231104fd7699231006bf6499231034ff76592310057f75592310057c7559231004ff75592310067f75592310047f7559231074fc75592310067c75592310747c7559231006bf7459231106bf4359231106bd4359231004ff7259231014fe7259231014fc7259231006be4259231006bc4259231004ff705923100cfe705923100cfc70592310057e75192310057d7519231036be6419231006bd641923111df
  | 29 => 0x6ed6318941006ec631894112eef61189411cfe741189411cfe44118941005ed7018941006ee6018941006ec6018941004fe76d4941004fd76d4941074fc76d49410067f65d49410767c65d4941006ef62d4941016ec62d4941004ff7654941004fe7654941004fc76549410067f65549410767c6554941005bf7454941035bc7454941006ef6254941016ec6254941014fc76509410057f75509410057c75509410067f65509410067c6550941006ef6250941016ec6250941005f77150941005f47150941004ff764c941004fe764c941004fc764c9410067f654c9410067c654c941005bf744c941035bc744c941006ef624c941016ec624c941034fe76d4541034fc76d45410067f65d45410767c65d4541035be74d4541005bd74d45410fdee72d4541005ed72d4541006ef62d454138eec62d45410067f65945410767c6594541006ef6294541386ec6294541007775194541004fd7654541034fc7654541005bf7454541035bc7454541006ef625454137eec62545410067f65905410067c6590541006ef6290541116ec6290541035f671905410073f6590541376be6590541376bc65905410073c65905410063c6590541006bf6390541007af6290541007ac6290541035be7190541037b76190541005bd709054110ebe609054110ebc609054100cfe76d81410067f65d81410067c65d8141006ef62d8141006ec62d81410f6fa60d8141074fe75d8141004fd75d814100cfc74d814101cfe73d8141004fd73d814101cfc73d8141006ef72d8141014fe72d8141004fd72d8141014fc72d8141006ec72d8141034fd71d81410f6fa40d8141006fb30d81410f6f830d81410f6fa10d81410057f75581410057c75581410067f65581410067c6558141005df7358141105dc7358141005ef72581410fdec7258141006ef6258141006ec62581410f6f860581410367f7559441034fe7459441034fc7459441036bc7459441034bc74594410367e54594410367c5459441036bc54594410363c5459441004ff735944101cfe735944101cfc73594410067e53594410067c5359441004ff7259441014fe7259441014fc7259441004ff705944100cfe705944100cfc7059441035bd76d504136ebd76d5041035be75d50410373e75d5041036bf65d504136ebd65d5041005bd73d50412d6be62d5041036bc62d5041005bd71d5041037b661d50410ddbe70d50410ddbc70d5041004ff7558c41074fc7558c41006bf5458c41036bc5458c41036df7358c410eedc5358c41036df4358c41036dc4358c41004ff7258c41014fe7258c41014fc7258c410eedf3258c410eedc3158c41004ff7058c4100cfe7058c4100cfc7058c410eedf3058c41074ff76d4c41034fe76d4c41004fd76d4c413067f65d4c410767c65d4c41035bc74d4c413073c54d
  | 30 => 0xe20195410067c20195410067e10195410067c10195410067f65d51410767c65d51410373e54d51412d6ec62d5141005f671d5141005f571d5141074fc76551410067f65551410767c65551410373c54551411a6ec6255141005f77155141005f47155141037b4415514101cfe76d8d410067f65d8d410067c65d8d41106de63d8d41074fe75d8d41004fd75d8d41106de43d8d41014fe72d8d41004fd72d8d41014fc72d8d41034fd71d8d41106df31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006de30d8d41106dc30d8d410057f7558d410057c7558d410067f6558d410067c6558d41106dc6358d41005ef7258d410fdec7258d41005fb7058d410f5f87058d41004fe76d4d41004fd76d4d41074fc76d4d410067f65d4d410767c65d4d41035be74d4d41005bd74d4d411075e53d4d4139eec62d4d41004ff7654d41004fe7654d41004fc7654d410067f6554d410767c6554d41396ec6254d4101cfc7650d410067f6550d410067c6550d41006df6350d4101edc6350d410379c4350d4116eec6250d41005f77150d41005f47150d41014fe76d89410067f65d89410067c65d89410feee62d8941074fe75d8941004fd75d894101cfe73d8941004fd73d894101cfc73d89410feee52d89410feec52d89410feee42d8941006ef32d89410feee32d89410feec32d8941034fd71d89410feef21d894100cfe70d8941004fd70d894100cfc70d89410feef20d8941006ee20d89410feec20d89410fdee76d8941014ee76d8941006ef65d89410076f65d89410066f65d8941006ee65d8941006ed65d8941006ec65d89410076c65d89410066c65d8941006ef63d8941006ee63d8941006ed63d8941006ec63d89411d7e741d89411d7e441d8941005ed70d8941006ee60d8941006ec60d8941006ef75d8941006ee75d8941006ed75d8941006ec75d8941006ef74d89410feee74d8941006ef54d89411d6ee54d8941006ed54d89411d6ec54d8941006ef73d8941006ee73d8941006ed73d8941006ec73d8941006ef53d8941006ee53d8941006ed53d8941006ec53d89411d6ef43d8941006ee43d8941006ed43d89411d6ec43d89411d6ef71d89410feee71d8941006ed71d89411d6ef41d89411d6ec41d8941006ef31d8941006ec31d8941006ef70d8941006ee70d8941006ed70d8941004ed70d8941006ec70d8941006ee50d8941006ec50d89411d6ef40d8941006ee40d89411d6ec40d8941006ef30d8941006ee30d8941006ec30d8941006ee10d8941006ec10d89410057f75589410057c75589410067f65589410067c65589410feec6258941005ee76189410feee7618941006ef65189410076f65189410066f6518941006ee6518941006ed6518941006ec65189410076c65189410066c6518941006ef6318941006ee6318941
  | 31 => 0x641005bd73d0641037ae72d0641037ad72d0641037b661d0641007b651d064110dbe70d0641035bc70d064110efa60d824110ef8605824110fba4058241004ff7558241074fc7558241006bf5458241006bc5458241004ff735824101cfe735824101cfc7358241006bf4358241006bd4358241004ff7258241014fe7258241014fc7258241034fc7158241006bf415824110ebe405824110efa405824110ebc405824110ef8105824101cfe73d9541004fd73d954101cfc73d95410067e53d95410067c53d9541014fe72d9541004fd72d9541014fc72d95410067e52d95410067c52d954100cfe70d9541004fd70d954100cfc70d95410067e50d95410067c50d95410067e63d95410067c63d95410067e62d95410067c62d95412ef7741d95412ef7441d95410067e60d95410067c60d95410067f74d95412ee7e74d95410067d74d95412ee7c74d95410067f73d95410067e73d95410067d73d95410067c73d95412ee7f43d95410067e43d95412ee7c43d95410067f72d95410067e72d95410067d72d95410067c72d95412ee7f42d95410067e42d95412ee7c42d95410067f32d95410067e32d95410067c32d95412ee7f71d95410067d71d95412ee7f41d95412ee7c41d95410067f31d95410067c31d95410067f21d95410067c21d95410067f70d95410067e70d95410067d70d95410067c70d95412ee7f40d95410067e40d95412ee7c40d95410067f30d95410067e30d95410067c30d95410067f20d95410067e20d95410067c20d95410067e10d95410067c10d95410067f65995410fdee7299541005ed7299541005ef72595410fdec7259541006bf7459541004ff735954101cfe735954101cfc7359541004ff7259541006ef7259541004ef7259541014fe7259541014fc7259541006ec7259541014ec7259541004ff7159541006f77159541004ff705954100cfe705954100cfc7059541004fe76195410767e65195410067d65195410057e76195410067e76195410047e76195410067e63195410067c63195410067e62195410067c62195412e77741195412e77441195410067e60195410067c60195410767f74195410767e74195410767c74195410767f73195410767e73195410767d73195410767c73195412e67f43195410067e43195412e67c43195410767f72195410767e72195410767d72195410767c72195412e67f42195410067e42195412e67c42195410067f32195410067e32195410067c32195410767f71195410767d71195412e67f41195410067d41195412e67c41195410067f31195410067c31195410067f21195410067c21195410767f70195410767e70195410767d70195410767c70195412e67f40195410067e40195412e67c40195410067f30195410067e30195410067c30195410067f20195410067
  | 32 => 0x4ff705964100cfe705964100cfc70596410767e65196410067d651964111dde7319641005dd7319641036f741592410767e65d52410067d65d52410373e54d5241005f671d5241005f571d5241376bf65d52413773e65d5241376bd65d52410073d65d52410063d65d5241005bd73d52412d6be62d52412d6bc62d5241377b671d5241005bd71d5241377b571d5241005b571d5241036be61d524110dbe70d524110dbc70d5241074ff76552410767e65552410067d65552410373c5455241005f77155241005f47155241037b74155241005bd7615241036bd76152410373e7515241376bf65152410073f65152410063f6515241376bd65152413773c6515241005bd731524118ebe621524118ebc62152413a73e52152413773c5215241005bd7115241037b6611524110dbe7015241035bc701524111ede63d8e4111edc6358e41004ff7558e41074fc7558e41006bf5458e41006bc5458e4111ede5358e4111ede4358e41004ff7258e41014fe7258e41014fc7258e41006de3258e4111edc3258e41034fc7158e4111edc3158e41004ff7058e4100cfe7058e4100cfc7058e4111edf3058e41074ff76d4e41004fe76d4e41004fd76d4e410767e65d4e410067d65d4e413773c54d4e4111f5e53d4e41004ff7654e41004fd7654e41004fc7654e410767e6554e410067d6554e41005bf7454e41035bc7454e410073c5454e4101ede6354e41006dd6354e41005bd76d0e41036bd76d0e41375be75d0e41035bc75d0e412bebe65d0e4101ebe63d0e4101ebc63d0e41005bd71d0e41037b661d0e4110dbe70d0e41035bc70d0e4101cff7650e4101ede6350e41006dd6350e41005f77150e41005f47150e4111dbf7650e4101ebf7650e4101cbf7650e41375be7550e41375bc7550e412b6be6550e410379f7350e4101ebe6350e4111f9e6350e4101e9e6350e410079d6350e4101ebc6350e41005bf7150e41007b77150e41007b47150e41036be6150e4110dbe7050e4110dbc7050e410057e75d8a410057d75d8a4111dde73d8a41005dd73d8a41116ee62d8a41116ec6258a41004ff7558a41074fc7558a41004ff7358a4101cfe7358a4101cfc7358a41006bf4358a41006bd4358a41116ee4258a41034fc7158a41116ec2158a41004ff7058a4100cfe7058a4100cfc7058a41116ef2058a41074ff76d4a41004fe76d4a41004fd76d4a41004ff7654a41004fd7654a41004fc7654a41005bf7454a41035bc7454a41014ff7650a410057f7550a410057c7550a41016ee6250a41006ed6250a41037ac4250a41005f77150a41005f47150a41004ff764ca41004fd764ca41004fc764ca41115ee72d4641005ed72d4641034fd7694641035be7494641005bd74946410073c5494641005bd76d0641036bd76d0641375be75d0641035bc75d
  | 33 => 0xc5459741004ff735974101cfe735974101cfc7359741004ff7259741014fe7259741014fc7259741004ff705974100cfe705974100cfc70597410067e50597410067c5059741004ff7558f41074fc7558f41036df7358f41136de5358f41036df4358f41036dc4358f41004ff7258f41014fe7258f41014fc7258f41036bc4158f41136df3158f41004ff7058f4100cfe7058f4100cfc7058f41036bf4058f41006de3058f41136dc3058f41074ff76d4f41034fe76d4f41004fd76d4f410767e65d4f410067d65d4f41035be74d4f41005bd74d4f411375e53d4f4139eee62d4f41004ff7654f41004fd7654f41034fc7654f410767e6554f410067d6554f4101ede6354f41006dd6354f41396ee6254f41004ff7558b41074fc7558b41004ff7358b4101cfe7358b4101cfc7358b41036ef7258b4112eee5258b4112eec5258b41036ef4258b41036ec4258b41006ef3258b4112eee3258b4112eec3258b4112eef2158b41004ff7058b4100cfe7058b4100cfc7058b4112eef2058b41006ee2058b4112eec2058b41006ef7558b41006ee7558b41006ed7558b41006ec7558b41036ef7458b41036ee7458b41036ec7458b41036ef5458b41036ee5458b41036ed5458b41036ec5458b41006ef7358b41006ee7358b41006ed7358b41006ec7358b41006ef5358b41006ee5358b41006ed5358b41006ec5358b41036ef4358b41036ee4358b41036ed4358b41036ec4358b41006ef7158b41006ed7158b4112eec7158b41036ef4158b41036ee4158b41036ed4158b41036ec4158b41006ef3158b41006ec3158b41006ef7058b41004ef7058b41006ee7058b41006ed7058b41006ec7058b41006ee5058b41006ec5058b41036ef4058b41036ee4058b41036ed4058b41036ec4058b41006ef3058b41006ee3058b41006ec3058b41006ee1058b41006ec1058b41074ff76d4b41034fe76d4b41004fd76d4b41016ee62d4b41006ed62d4b41004ff7654b41004fd7654b41034fc7654b41005bf7454b41035bc7454b41016ee6254b41006ed6254b41004ff764cb41004fd764cb41034fc764cb41005bf744cb41035bc744cb41016ee624cb41006ed624cb41035be74d4741005bd74d474138eee62d4741006ed62d4741004ff7558341074fc7558341004ff735834101cfe735834101cfc7358341004ff7258341014fe7258341006ee7258341006ed7258341014fc7258341036fb7058341036fb4058341036f84058341126fa105834101cfe73d9641004fd73d964101cfc73d9641014fe72d9641004fd72d9641014fc72d9641006f671d964100cfe70d9641004fd70d964100cfc70d96410067f65996410067f7559641004ff735964101cfe735964101cfc7359641004ff7259641014fe7259641014fc72596410067e52596410067c5259641
  | 34 => 0x85421ceef7218542034fd72185421ceef42185420e6ec42185420e6f5211854200cfe7018542004fd701854200cfc70185420e6ef2018542006f61018542006f4101854200cfe76d81420067f65d81420067c65d8142146fa60d8142074fe75d8142004fd75d8142014fd74d814201cfe73d8142004fd73d814201cfc73d8142006bf43d8142006bd43d814227eef72d8142034fd72d814227eef42d814207eec42d8142004fe71d8142004fd71d814207eec21d8142146fa40d8142146ef20d8142146fa20d81420057f75581420057c75581420067f65581420067c6558142005df735814214ddc7358142005f77158142005f47158142146f86058142034fe76d9132074fe75d9132004fd75d9132014ff73d9132014fd73d91323aebf43d91323aebd43d913201cff72d913201cfd72d913233ebf42d913233ebd42d9132004fe71d9132004fd71d913233eec21d913200cfe70d9132004fd70d913200cfc70d9132006be40d9132006bc40d913233eef20d913216cfd7699132006bf649913216ddd739913214ded7299132034ff76591320057f75591320057c755913217ddf735913215def7259132004ff75591320067f75591320047f7559132074fc75591320067c75591320747c7559132006bf745913217cff7359132006df735913216cff7259132006ef7259132004ff7159132004fc715913216eec2159132004ff705913200cfe705913200cfc705913216eef205913233cfe7619132036be6419132006bd6419132034ff7695132004fe7695132004fd7695132034fc76951320067f65951320767c65951320073f5495132004ff7655132004fe7655132004fd7655132004fc7655132034ff7615132004fe7615132004fd7615132034fc7615132006bf6415132036bc64151320073d541513201dde7315132005dd7315132015ee7215132005ed7215132034fe74d8532004fd74d8532014fd73d853201cfd72d8532366ed72d8532366f631d853230ef621d853230eec21d853200cfe70d8532004fd70d853200cfc70d853230eef20d8532006f610d8532006f410d8532005be7498532005bd7498532006f76198532006f56118532034fe7418532004fd7418532014fd7318532096ef721853201cfd7218532096ef321853231eec3218532096f5311853231ef5211853231eec211853200cfe7018532004fd701853200cfc701853231eef2018532006f61018532006f4101853200cfe76d813213efa60d8132034fe74d8132004fd74d8132014fd73d8132056ef72d813201cfd72d8132056ef32d8132276ec32d8132004fe71d8132004fd71d8132276ec21d813213efa30d813213eef20d813213efa20d8132005bf7458132005bc7458132005f77158132005f4715813213ef860581320367f75597410367e54597410367
  | 35 => 0x18e7f321954218e7e321954218e7d321954218e7c32195420767f71195420767e71195420767d71195420767c71195423b67f41195423b67c41195420067f31195420067c311954218e7f211954218e7e211954218e7d211954218e7c211954218e6c21195420767f70195420767e70195420767d70195420767c70195423b67f40195420067e40195423b67c40195420067f30195420067e30195420067c301954218e7f201954218e6f201954218e7e201954218e7d201954218e7c20195420067e10195420067c1019542014fe76d5142014fc76d51420067f65d51420767c65d51422d6bf64d51420373e54d5142015ee72d5142005ed72d5142074ff7655142014fe76551421a4fd7655142014fc76551420067f65551420767c65551420373c5455142005ef7255142015ec7255142037ac425514201cfe76d8d420067f65d8d420067c65d8d4214ede63d8d42074fe75d8d42004fd75d8d42014fd74d8d4214ede43d8d42034fd72d8d4217edf32d8d42004fe71d8d42004fd71d8d4214edf31d8d4217eec21d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42006de30d8d4214edc30d8d4217eef20d8d420057f7558d420057c7558d420067f6558d420067c6558d4214edc6358d42004fe76d4d42004fd76d4d42074fc76d4d420067f65d4d420767c65d4d4214f5e53d4d42004ff7654d42004fe7654d42004fc7654d420067f6554d420767c6554d42345be76d0d42036be76d0d420073f65d0d422bebe65d0d422bebc65d0d420073c65d0d420063c65d0d4216dbd73d0d4201ebe63d0d4201ebc63d0d42015be72d0d42015bc72d0d42036bf62d0d42037af62d0d4217fac21d0d4217faf20d0d42014fc7650d420067f6550d420067c6550d42006df6350d4201edc6350d42005ef7250d42015ec7250d42015bc7650d4201ebc7650d42014bc7650d420073f6550d422b6be6550d422b6bc6550d420073c6550d420063c6550d42035bf7350d420379f7350d420079f6350d4201ebe6350d4201ebc6350d4214f9c6350d42007af7250d42015be7250d42015bc7250d4216fac7250d42015ac7250d42036bf6250d42037af6250d4216fac2150d4216faf2050d420067f65d85420067c65d8542074fe75d8542004fd75d854201cfe73d8542004fd73d854201cfc73d8542034fd72d854212ef621d854212eec21d854200cfe70d8542004fd70d854200cfc70d854212eef20d8542006f610d8542006f410d85420057e75985420057d75985420067f65985420067c659854214dde7398542005dd7398542006f761985420057f75585420057c75585420067f65585420067c65585420067f65185420067c6518542006f56118542074fe7518542004fd751854201cfe7318542004fd731854201cfc7318542006bf4318542006bd431
  | 36 => 0xf2098742004ff7558742074fc7558742014fc7458742004ff735874201cfe735874201cfc7358742036f77158742036f74158742036f441587420fef621587420feec2158742004ff705874200cfe705874200cfc70587420feef2058742004ff7558342074fc7558342014fe7458342014fc7458342004ff735834201cfe735834201cfc7358342036bf4358342006bd4358342006ed7258342036ee4258342036ed4258342004ff7158342004fc7158342066ec2158342036fb7058342036fb4058342036f84058342156ef2058342156fa2058342074fe76d954201cfe73d9542004fd73d954201cfc73d95420067e53d95420067c53d9542034fd72d95421be7f52d9542004fe71d9542004fd71d95421beec21d954200cfe70d9542004fd70d954200cfc70d95420067e50d95420067c50d95421beef20d95420747e76d95420067e63d95420067c63d95423bf6f42d95421bf3e42d95421bf3c42d95421bf6c42d95421bf6c21d95420067e60d95420067c60d95421bf6f20d95421be7f74d95423be7e74d95421be7d74d95421be7c74d95420067f73d95420067e73d95420067d73d95420067c73d95423be7f43d95420067e43d95423be7c43d95421be7f72d95421be7e72d95421be7d72d95421be7c72d95421be7f42d95421be7e42d95421be7c42d95421be7f32d95421be7e32d95421be7d32d95421be7c32d95420067f71d95420067e71d95420067d71d95420067c71d95423be7f41d95423be7c41d95420067f31d95420067c31d95421be7f21d95421be7e21d95421be7d21d95421be7c21d95421be6c21d95420067f70d95420067e70d95420067d70d95420067c70d95423be7f40d95420067e40d95423be7c40d95420067f30d95420067e30d95420067c30d95421be7f20d95421be6f20d95421be7e20d95421be7d20d95421be7c20d95420067e10d95420067c10d95420067f65995421a5bd74995422d6bf64995422d5bf7459542006bf7459542004ff735954201cfe735954201cfc73595421a4ff7259542006ef7259542004ff7159542004fc71595421a6ec2159542004ff705954200cfe705954200cfc70595421a6ef20595421bcfe76195420767e65195420067d651954218ebf64195421bd7e76195420067e76195421bc7e76195420067e63195420067c63195423b76f421954218f3e421954218f3c421954218f6c421954218f6c21195420067e60195420067c601954218f6f20195420767f74195420767e74195420767d74195420767c74195420767f73195420767e73195420767d73195420767c73195423b67f43195420067e43195423b67c43195420767f72195420767e72195420767d72195420767c721954218e7f421954218e7e421954218e3e421954218e7d421954218e7c421954218e3c4219542
  | 37 => 0x51430067f65551430767c65551430373c5455143005df735514301ddc73551430379c43551431c5be7615143036be76151433d5be75151430373e75151432b6bf65151432b73e65151432b6bd65151430073d65151430063d651514301dbe731514301dbc7315143036bf63151430379f63151431973f53151431973d5315143005bd721514318ebe621514318ebc62151433cf3e52151432b73c5215143005be7115143005bd7015143014fe76d894316eee62d8943074fe75d8943004fd75d894301cfd74d8943034fd73d894316eec52d894316eee42d894316eee32d8943004fe71d8943004fd71d894316eec21d894300cfe70d8943004fd70d894300cfc70d894316eef20d89430057f75589430057c755894316eec625894316dee72d8543005ed72d8543074fe75d8543004fd75d8543136bd74d8543034fd73d8543014fe72d8543006ee72d8543014ee72d8543004fd72d8543006ed72d8543004ed72d8543014fc72d8543136f631d854300cfe70d8543004fd70d854300cfc70d8543006f761985430057f75585430057c7558543005ef725854316dec7258543005fb7058543165f87058543006f56118543074fe7518543004fd7518543006bf5418543006bc5418543034fd7318543014fe7218543004fd7218543014fc72185430eef5311854300cfe7018543004fd701854300cfc701854300cfe76d8143166fa60d8143074fe75d8143004fd75d814301cfd74d8143006bf54d8143006bc54d8143034fd73d8143014fe72d8143004fd72d8143014fc72d8143004fe71d8143004fd71d8143166fa40d8143166fa30d8143166f810d8143166f860581430367f7559742014fc74597420367e54597420367c5459742004ff735974201cfe735974201cfc73597421a67f5259742004ff7159742004fc71597421a6ec2159742004ff705974200cfe705974200cfc70597421a6ef2059742004ff7558f42074fc7558f42014fe7458f42014fc7458f42036df7358f42036df4358f42036dc4358f4216edf3258f42004ff7158f42004fc7158f4216eec2158f42004ff7058f4200cfe7058f4200cfc7058f4216eef2058f42074ff76d4f42034fe76d4f42004fd76d4f420767c65d4f4215f5e53d4f42004ff7654f42004fd7654f42034fc7654f42005ef7254f42015ec7254f42035bf7650f423c6bf7650f422b6be6550f42036bc6550f420379f7350f4201ebe6350f4201ebc6350f42015be7250f42015bc7250f4216fac2150f4216faf2050f42074fe7598742004fd7598742014fe749874201cfe7398742004fd739874201cfc7398742036bf4398742006bd4398742006ef7298742036ee4298742036ed4298742036f67198742036f74198742036f44198742116f5219874200cfe7098742004fd709874200cfc7098742116e
  | 38 => 0x36f840580540367f755974301cfc7459743036bc745974301cbc74597430367e54597430367c5459743036bc54597430363c54597431ae7f5359743004ff7259743014fe7259743014fc7259743004ff7159743004fc7159743004ff705974300cfe705974300cfc70597430067e50597430067c5059743035bd76d53432bebd76d53430373e75d5343036bf65d53432bebd65d534301dbe73d534301dbc73d5343005bd72d53432d6be62d5343036bc62d5343005be71d5343005bd70d5343004ff7558b43074fc7558b4301cfe7458b4301cfc7458b43036ef7258b43036ef4258b43036ec4258b4317eee3258b43004ff7158b43004fc7158b4317eec2158b43004ff7058b4300cfe7058b4300cfc7058b4317eef2058b43074fe7598743004fd759874301cfe7498743006bf5498743036bc5498743014fe7298743004fd7298743014fc7298743036f67198743036f74198743036f4419874311ef5319874300cfe7098743004fd709874300cfc7098743004ff75587430067f75587430047f7558743074fc75587430067c75587430747c755874301cfc7458743036bc745874301cbc7458743004ff7258743006ef7258743004ef7258743014fe7258743014fc7258743006ec7258743014ec7258743036f77158743036f74158743036bc4158743036f44158743106f63158743004ff705874300cfe705874300cfc7058743036bf4058743004ff7558343074fc755834301cfe745834301cfc7458343006bf5458343036bc5458343004ff7258343014fe7258343014fc7258343004ff7158343004fc7158343036fb7058343036fb4058343036f84058343176fa3058343074fe76d95431c6bd74d9543034fd73d95431c67f53d9543014fe72d9543004fd72d9543014fc72d95430067e52d95430067c52d9543004fe71d9543004fd71d954300cfe70d9543004fd70d954300cfc70d95430067f65995431adbd74995433d5bf7459543005ef725954316dec7259543006bf74595431acff7359543006df7359543004ff7259543006ef7259543004ef7259543014fe7259543014fc7259543006ec7259543014ec7259543004ff7159543004fc7159543004ff705954300cfe705954300cfc70595431c4fe76195430767e65195430067d651954301cfe76d514301cfc76d51430067f65d51430767c65d51430373e54d514301dde73d5143005dd73d514301dbe76d51433d6be76d514301cbe76d5143035be75d51432b6bf65d51430073f65d51430063f65d51432b6bd65d51432b73c65d514301dbe73d51433d79e73d514301d9e73d51432b79d73d514301dbc73d5143036bf63d51430379f63d5143005bd72d51432d6be62d51432d6bc62d5143005be71d5143005bd70d5143074ff765514301cfe76551431acfd765514301cfc765
  | 39 => 0xd72d8554014fc72d855400cfe70d8554004fd70d855400cfc70d8554006f76198554005ef72585541a5ec7258554006f561185542e67e541855436ebc541855401cfe7318554004fd731855401cfc7318554014fe7218554004fd7218554014fc721855400cfe7018554004fd701855400cfc701855400cfe76d815419efa60d8154074fd74d81543f67e54d81542debc54d815401cfe73d8154004fd73d815401cfc73d8154014fe72d8154004fd72d8154014fc72d8154004fe71d8154004fd71d815419efa40d815419ef860581540373f76550540353f76550540063f76550540043f76550540073f73550540053f73550543ef3e73550540073d73550543ef3c73550540373f63550540373e63550540373d63550540373c63550540073f72550543e73e725505418d3e72550540073d72550543e73c725505418d3c72550540373f62550540373e62550540373d62550540373c62550543ef3f32550543e73e32550543e73c32550540073f71550540073e71550540073d71550540073c71550540053c71550540373f61550540373e61550540373d61550540373c61550543ef3f31550543ef3c31550543e73f21550543e73c21550540073f70550540053f70550543df3e70550540073d70550543df3c70550540373f60550540373e60550540373d60550540373c60550543ef3f30550543df3e30550543df3c30550543e73f20550543df3e20550543df3c20550543df3e10550543df3c1055054034ff7358c54036df7358c54036df4358c54036dc4358c54004ff7258c54014fe7258c54014fc7258c54196df3258c54004ff7158c54004fc7158c54036bc4158c54196dc3158c54004ff7058c5400cfe7058c5400cfc7058c54036bf4058c54196df3058c54004ff735885401cfe735885401cfc7358854036bf4358854034ff7258854036ef7258854036ef425885418ebe4258854036bc4258854036ec4258854036ac425885418eee3258854004ff7158854004fc715885418eec2158854004ff705885400cfe705885400cfc705885418eef205885401cfe7398454004fd739845401cfc7398454036bf4398454014fe7298454004fd7298454014fc7298454036f67198454036f74198454036f4419845400cfe7098454004fd709845400cfc7098454004ff735845401cfe735845401cfc7358454004ff7258454006ef7258454004ef7258454014fe7258454014fc7258454006ec7258454014ec7258454036f77158454036f74158454036bc4158454036f44158454036b44158454004ff705845400cfe705845400cfc7058454036bf4058454004ff735805401cfe735805401cfc7358054036bf4358054004ff7258054014fe7258054014fc7258054004ff7158054004fc7158054034ff7058054036fb7058054036fb4058054
  | 40 => 0x400000280020000000000000200480000010003000c0010024001000400c000000f001c01a001800b00000090367e5459654036bc54596540363c54596540373d76d52540763d76d52540373f63d52540373e63d52540373d63d52540373c63d52540373f62d52540373e62d52540373d62d52540373c62d525440f3f32d52544073e32d52544073c32d52540373f61d52540373e61d52540373d61d52540373c61d525440f3f31d525440f3c31d52544073f21d52544073c21d52540373f60d52540373e60d52540373d60d52540373c60d525440f3f30d52543ff3e30d52543ff3c30d52544073f20d52543ff3e20d52543ff3c20d52543ff3e10d52543ff3c10d5254034fc7458e542b6bf5458e54036bc5458e54036df7358e541c6de5358e54036df4358e54036dc4358e54004ff7258e54014fe7258e54014fc7258e54004ff7158e54004fc7158e541c6df3158e54004ff7058e5400cfe7058e5400cfc7058e54006de3058e541c6dc3058e54034fc7458a54004ff7358a5401cfe7358a5401cfc7358a54036ef7258a541be7e5258a541beee5258a541be6e5258a541be7c5258a54036ef4258a54036ec4258a54004ff7158a54004fc7158a541beec2158a54004ff7058a5400cfe7058a5400cfc7058a541beef2058a54034fe7498654376bf5498654036bc549865401cfe7398654004fd739865401cfc7398654014fe7298654004fd7298654014fc7298654036f67198654036f74198654036f4419865400cfe7098654004fd709865400cfc7098654034fc7458654004ff735865401cfe735865401cfc7358654004ff7258654006ef7258654004ef7258654014fe7258654014fc7258654006ec7258654014ec7258654036f77158654036f74158654036f44158654004ff705865400cfe705865400cfc7058654034fc74582542aebf5458254036bc5458254004ff735825401cfe735825401cfc7358254004ff7258254014fe7258254014fc7258254004ff7158254004fc7158254036fb70582541b6fa5058254036fb4058254036f8405825401cfe76d8d541aede63d8d54074fd74d8d543067e54d8d542bebc54d8d541aede43d8d54014fe72d8d54004fd72d8d54014fc72d8d54004fe71d8d54004fd71d8d5400cfe70d8d54004fd70d8d5400cfc70d8d541aedc6358d54005ef7258d541a5ec7258d54014fe76d89541a6ee62d8954074fd74d895401cfe73d8954004fd73d895401cfc73d89541a6ee42d8954006ef32d89541a6ec32d8954004fe71d8954004fd71d89541a6ec21d895400cfe70d8954004fd70d895400cfc70d89541a6ef20d89541a6ec62589541a5ee72d8554005ed72d855401cfe73d8554004fd73d855401cfc73d8554014fe72d8554006ee72d8554014ee72d8554004fd72d8554006ed72d8554004e
  | 41 => 0x4007005800600040000000000000000400080060020000001c0060008008000800000380010040004000000b0080007001c00c0074000001c0010018000000000000080000014005003400a0008008000c001000c000000400200080090004001000400700400060004003002c006001c000001c0010050002000000a00300070048001000400000000020020004001c0010004000001c0090008002001c00000400000000005000400d00080000038001000000d000c004001c018004400000000030004000001000200040000028001001000200d8001000000100100010000000000000400180080004016001401200140000004004005000300000000008000003c003000c0020008006000c000000000f00340040000004001800000040000004003000800b004c000000800400d00010028005002c0070000008002c0000000000002c00100180010014001002400d0000030000c033001000800000050000002008c0040038004000402400000010000000002c0070028001000400e00100040000014000000f001000c003c0000010005011000300000000000000000000000200140018000001001400380100030003001c00e00040020000003004400c000401a0000006003c003001c002000c00500a4000002800a00000000024002000c0000000004004c00100400050008000000000600000030018000004c01400080030018000000c007000c0000004013000001e002401b00040010004006000000500340060008007000000300040020000005000400b0000002000c00900f80010038003002000000cc001001c0030000004000000000000000008000000c002001000000000000004000001c0040000004008c01200080070000010000000300200030014009000c0000000000003c00100640090008001000800100200070008004003c00100100070014001005800000440020028004000800400000030000001000c0030000042000c009003000b000800800080020000000000401100d801400100030028001000c0000014001001c00f0008009000c001001000c00080010000003000400200100080000002000c0010030003000002500540030000000000c0000044001001800600040090158005001000300100140040002000400b000400200100090000001005c001000802900080010004000000800100000000008013001c003000001e00200000004007000000500040020020001001000400140020008000000c000000800200100030004000000400a00240020020008003c0000000004000800100140080010001001000100000010008016003000000040000000000002c00000840010078003000400000000020020002004801600180000000002003000300040010004002000000600680020098001002
  | 42 => 0x400100040000010004000000f001c001000c00000c800400200070018000002c00a007001400f000000300050000003002000500000030058002000400500ac00a0008001000801200380040004001004400000140020008000003c00000140000018000000c001003c002000c0000010000000000a0008009004c006000c0060018001000c00d006c030001000600000010018002000c002009c0100024006001000700480000018014000000400080000000020006c002000c0070024003002c00c00040200004002002400a0000003001c00c0018000000c00400700000014004000001400a804d000000200000180004005000400300040010000003003400300c8016001000c0014000000002b00080000034007002c004001c00c0000001000c004002c00200040010008008000000f0010034000c0010004005001c01700d80080000000001c002004000e000400d0048000000001a0000000000000a000000000140000068006000000a000c00c001000800040000034002001c002003c004002000000000030004002003c00400400060010012000800000000020010007000800500000020010001002c001002001200040090010009001800e003000d0008005000c000000000a00200010000002000801500000060018016001400700800000010000007000d00080010048000000402100000040048000002800000000020014004001c024001801300000020018009000000000000000000000000400700000040000000000000200140040014001000800d0004006003000000080000000000004400400000010014000001c003000c005000c0220004021001c00200140150004008004800d000000200000170084001001801700100040000001007000700000000008001002400000000050018003003c00100080030000003001000200340050010007000c000001400100080000004002000400300180020000011000400000100030024007001c001003800f004c001000001d000c00b00000050008004000c0000000001000c00200100000004000000800000180070004000000400c0004000000400c0008005000000b0000000008c0020028001000000100000000058000000800d001400100000010020000000c00e00200000020007000000300140040014000002c0010000007000000d000000d000c00100200010028017000c00000740040000005002801d000c00100080000000000001c03f000800c001c01f000c009000000100440040004012004000000540170004003002c01000140010028002000000100140000008001000005c00000170018000001400400300020000004002000000140000010005000c0080004000003c001000000100340010008012000000b00000010014005000000e0000000000c00
  | 43 => 0x140014016001800a0020006003c00600100010008001002400e000002f0000001000401500000020010003000c00300000030004008000400100240000008000001c00400000170004000000c01600000060000005003c00000300000010003004000a00000060014006000c0000028002000400600000000024001000c0040000000000000c0008000005c0050028002001401b000000100140030014006001800100140030004002000000b0000008000800c0000000001c00f000c0120010000000400a000400600240000000000000400000040080008000000000600000010010003000c004000800300040030018001000800c000000000280050000010003000100a401000180000000001002c01e00b00000000000000000a0008015000400c0000001000000000680000018000000400a001c0030010001000c000000400500080000048008000c005000000100340000014006007c00300040080008002000000000100070000009000c000006c002001400800040020008000003000000200010008004000400b0000007000c0120050001001800b0010005000000100000100014002006c003000001000140000018005005c00800000000004002001c000000400900000030004003000801b0000002005000000040000004000007c0050088008007800d000400f00200000008008000402d000800100000070004000000000400e0008000800d00080010018000000c00100380010004002000c002001c000000000200000010018000004400f0004001001c0010008007000c033000c0000004000001000000080120030004000000e002000000000000004003000c00300300000038005005c0000004001000400800000230014000002c01e00140090000028002800200040000018006000801c0010003000400500000080010004000800100140370000005000400200000000000000000000000000040000005000000b001400300140000004012000400600300000014008000000400000020000006000c001000c0020054001000000b00040230030007000c00e0008000001800000380100004000003801c00040050018009001800200140050020002002800900000010030002000000600080010040000000c0030000008000000000100080050010003400500740030014001001800800040000000002000c00e005c003002000700080050020002006c0020038004000800400000030028001001c00000200100000007007800000140120010000003000100340000010008000c00c0014005000c017000c001001400900000040008005005000400040000068001000400000200000044003002c002000c0000004002007c00c000400100000020004002001000100100010010000001005300940060008003005803700
  | 44 => 0x1000401e00000050010009000400000040020004010000400200040000008007002400000040010004001001000e0010000008000000640000000000002000700100030004001000c002000000d00280050028002000c00700040040000001000c000000800000000020000002006c009000000000000100000002004c002000400200040070004027002800a002400200000110030001001c0020000006001000a000400800840020000000000c006001000f00300080000002000800000000000000003000400000600070004008000000e000c00600280010068000000c0010004005000c007000000c000000300040000000003000000100100000018000000c0030004001003c004004c0090024005000c00a000c0000010000000c00e000800a001400a000000000100000000000000000e003c0050004007001402b0004000001400000080000004001000801c0004001000c00a000003f00080030000003000401900000090000002004c002001c000000c00000100110000000000800000000090000006000000900140000018004000000500000000024005000800300000000000004000c0000000000007c009000400000040090004004002800e0004000000800000080000004006002800000100000088013003c0020048001001800100140080000015000800a001c0070000011001800b00240040000003001000200140020008001001800100040020010001000c0020000002000000200080080020002000c00300000020010004001400b00100030004000000000200bc000000800200200260000006006c004003000e00080000018000004800100000010008005003c0000038010000400800040030004018000c001001c0000000000000c00300200040000002000000000000060030013000400f004400300080040004004001000000200000038013003000000080020020005000c003000001b0010038000c0080000004001000e00700010000007004002900000030000004006c0000000008000800a000000000040030008000000000000000030018000002400300040000000002002800f000c0020044002000400200200010000009003000000080010010002001800100100020000000000000200040090000008001000500140000008008001000400000000020002000c00200000000000001005000700780080004000000c0080008000000000c0004001000400400200020024019001800600000010020001003000000140030028036001003d000001c0000000002c002000000400ac022001c00700540030008003001800700100140008002000c000001000800d8007002c001000800200080020004003001c0020014006000c00000080050000000000c00000000000004002000c021000400000cc0
  | 45 => 0xf960000d306dc2726286dc0c00018ce652000052c97620001d40000000040b80000002f5e32700007c682a80695ea63211a5209d000000019ce5384e56000027c023919900001434d307951cfc20e000159a0000000a5b94427e59c2599400000002fac5119cd0886ec320299dde0001d2a2db2908c208000524400000014540000f605068a6251b443b0000000534000000000004ae8000d9d000077ec00076c88d6cb5a0cc94d1d80a831e66c522d7e2a45c2780f2fbe1490aaa7b830fab34a582bdea9b77b38124a428ba41c9809600000006b880000002a78677117e188211e80021f1100000046f8000b5f007053ee2150000e74d48800004788d4000170e00021e49b600008489996bd32d5c55b99c20bb2eb8bdb800000000002e4800092180001bd1bc70d5c00000013745501c50b382abc00000008f0ac26000241a29d00008eb1b549ae1ccea2c87905c3359cb9ab65819b106681f8000000000000029c408120d40002ad47ca80007f294f2c8aae4a2cad5705f6263736d80004d045d3ac710c6b579d220003038a08ad483f20b251c6b3c9ab907305e81ca46048d16b4724397462756726b54333ca7a0af61f5d3ea9f8ec65b67c831b22000012b05818ea8ab400006a9091cd40800087eb5ba000031877b27e200000000000000000000000000000148002000000a001000c0004003001c006000c0260018005000400300140020014008000000900040010004000001c0050044023000c001000000d000801100040030004012001c000000c004001800000040010000006000001700180070060001001000500040000000009000c006000400c0040002000800a002800000040060000001002c005001c02400280060030000001c003000c000003000300000040018003000c001005c000000400a00540000008000006c00c000400300440060018000002400500700080018000002c0000004005000000300000070034006003c00b0030005003000800000020080000002400a001c000000000c00040010058002000000100100000000006000400700440050000003001801e00040290014000000c00100040090004004004c00000000020028004000000600140030004003002c001001404c002c0010000000000c016008c016004400100080120000000007c004000402500180030014004002c00500140020004008000c00a000000000000000004002000000700080010074001000000000000010000004000000400000030028003000800d000400300000000000006003800d0000000000400000100070008000000001200700080000003000400900040230000000001c001002001a00000000044000000000a002000e002c0000004000000800500000030024000001c03600040010010000001c00b000000200000050
  | 46 => 0xa2f00000002277224d85b38a9413152000000000029e2b17b1d287dc00015287e4776075ab5ecf68a6aaf501858a414f48ad8774320431a83648438000b1032cabe412260002ff2acc0bf800005eeda58000000000060d80000001d3ec0c889fae100006f1236a8408c1e36000000878eec00030a01c41d20a92338c64119e40fe96ca24a07f4783307cd2b17160002f8c0001f77b8fb62c000035234700000002c348c3000099c026ed89800051c1b121640cdcbe99176d1591502f7c000c858d22719107665a800096aa11c00000000a54000c6d000078f6e087963446af59a6aa4fd2843073284af096baa0017f01a8048899659a01f6279ac56252003810a4cb70a6c6b21ce2500eabfc0c18f207aa3e042f11ba5080a443b09cda597818227184d2da2144436717f4bdf8b7808b9b647cc12e2a672216c91292832c859e843094613d52b43e51ff29c52caa15eb3965e48000bbb800019eaefa2f9400085de02c1bc8d90d99caa5305298c2dd2e880000000bad80004d680008a8000000014c2c5811e200018b895ab0da1ce73c41938000711593cb8c2e160001bf00000000000246a32900539101a43ab195687d42d60a0d8b034fa11869a019583d90c06d323499d682d2e5dbf1101ab800033fa860000338200033c10000000b67352789033ff6e5120a12da30622d00006e5941600024babd2100a286862605569a0095ad610a2278ad1d2fc00f11da69ad9d4e0002f084d7041c7b7b59e3b809deaacadf1086870ea8e800080590406f08ef0b129aae00000002ca4000000332800000006d68ab68f940000002a403d0e530411982c704b52070c082d000217015f80007a934541298906cfda3d83c3800098faff8881a65e0fe4000691400079a00004ed8d1a05c82f92a080007c8800034d0b400729a56b58f404a79184c4b982730df02c9000054221e00005f4992eb714c9a6d6078800010fc93e2ec036d07762ee9aca9d732ee0002cae5e11d28b3c2f6300f0f4911b0d4405d15b696f05da00e15022fda74ecab00007721320000289e00000000001ffd98d13fe7dc124652813c40001f5e9f7a6ac0152a740ac4d5040500000000000926123349e1906a0ead6a02956d4b5c8000d07968000018ac000000097a2dc20001a681c62eca9ef1afa9673513092c000000356619729be0001a8e0002e32bd65b1420c0000713330c9f2a1d8085db915298e70000004400000002e300000001cb80000ef2502a84000010d000021ae000134600029ea8870f80cd3800004d2522b51905e52ee71e63649c0cc54000116e618089a190abd8634934251709dc00000000009e32fd67c717600302196be780005c103aa45701c29b423108edb64675d060ab1aa5ca41a136a4de96e219d0e6e0ca000000000000e480000002d2000000d40000
  | 47 => 0xb5b8bca11e40000000000617294181687744aa1c3600002ae48d00002c7b1ead87a50667226a8a261e9f112745e72fb4a001d1f9c1af0000aefc000cdd9a360000000330069ab5d0000000043a0001d0c24a80000990000000000006c800000000008ca2040af6c00049b1ce40000000b719f201d912e446b6df2377b3ac26d87344eb1ce6000123c14d90d200009a4bf4a36e2f898101ba33ea573f1c856903f2cc9281422f98c40000b5054e87ae5ff88d0000000000002a6c451f5c5a726cc0000000799507072c218c81d8dfa3e49c6e2b900005a91ad80001a4f00000005ea6cb2580000000000000002b2000004ef7932dec0ce80000002dd1ad7367aae68f70741800000000001a280021320f268f104d8d5f1e3f7bb748a000219c8b6400000021c20000bac000004e7f30000000205ed1d923150c0000cde8000000039c71c0000d0d9886000000057380006f24ef4277000000000000000000a369f52b33ac12d0b8000b149ff01de245000012dc00022b894b0000b1f3574d60800000015806e54568a28b5da488892f7a52fde7f1cf2c61f800093980007e901020b18b4900000009a709e63b00000cfb28dc0000800609b5926ec8032b3e9ade27b00000002708000000000000004dc80004710000000099100010e43f5a47a78780004c91582000138b92920c25930bd87a816bc2cc193f5593318515b4524a50a2a7799bba3989dc661200c30002da45331fc148d87de9bb8000c6bb3d4b6e90f40f7890e1a10000c93887e3d180005b9ab381eadeb48b9315420d82190002b340001838371a50ac73a1e25e5c2ad000286e9ff0000603ef76c6f87585fa000090e00009ce1a06000025d9ed10fe6da000000000000002c9a0000bfc52f2f7000035c6cb361e09118902a2d29a8a20b0188c482d6af380a09b841082fb344a0fb26030e7800000c00000002b0c1b20000cc7800030a00000001d8c9a7d69ece60000000000000000000001946a91b49e0001f4d1e6624494f03fb280299e2e3906acbb1938a9e914a2e116f79c5e7b685b97fcb04673000000000000c9084925a89148150a12a81ebc09bf5afa80189c393ae87b8eb62ea85b2ce880867e284fa66a000084e8000b721e1c0001b3e6740000397ec80000149eb7faeb0cd680000000000a700000000000099e00008c100009548f908188000b3e057600000007d12bf2375b46fb881d46b640000cee23f8832b43457e800092fa0723bf2e9860505a88f898c30000f3c000025097a969251e90b22bb14a419c33d00000d64000053a95e269700022aa00024b437a26c40f60000cef1847a3800005d9ae1494dc000000342c6dd9e0600000000001f2682e11f60000000bdd00000000ed6c8c94fc8a9b4d070e98ba4518000b11c000000000000019a200024e00000000
  | 48 => 0x61e8d568ac899ab87229c0f8c00042d800000025e0496037282b0b589de0bda000000016e00000f700004a983b4000302e1d308e433f045e67d8000766285243547af2cb6972bc99104a0614049a999927afb5329cd06780cd0c7a79b0c3a4f52d963ee9a988ee20d200315ac2f6ec0e54a8e7d6330000000000046d958c7859db60000000000000000000006bc9ec23d58000a840bd200000008f3047e79ab17075306383b7962e7d2b51a861b5a333d000078e40007a58802397400094a8000a693238cc801b582f20687ee879250f0fe8b6380ab2252ebe2ec1726686012e9b51a9242a810b97c858e404aa60507400069281e69571d30b121644000077c3619f79000060ca3ad2f62f860f8bc3800000000005a88c128a011fc01faed8620a0ba77bce785de03064b299087854000a951f6e197c000c3600006ad90840000000aa418b2055ac76b27349464a80000de013a919a1ec39480004b216ac0000000000000000000000000000829848000000000002dea554000049fa722000000039280002048bb23a3089699a1fbc789199dcdfab100000000000081c00009e00000000000000000000000000000d4a260dd171426c4e8f3e018a88a389a3fc00028ec0000000a3a1bd500000001c20c62d97a57e00020967a22fb9000292630c000000008076e00000b0b1b6c0f480ce00017ea136b168000125fbd70fa631280001b684983158000c9e8000d619c8c3cfc1e9430142e622a7c68a634c67edad00ca49a6435f0ce44e185165ae2de0c2a006cd579b0abc64286189082e26a1a0a077b1c276e2a56d5f9cc300008f859d2c24010080c00007a2ca2231ecfc2ab458529a21b3aeec4f9157626c206c0001a3c993a7c8af21c49000000000910dc000000085380007f9993400024ac0459e9a582982218a965c8dc31441e5822424823e4a81893435000000000602a3180001660f45873aa3ccbd800000030bc55e1c580000a52ad79abb68c2fd0762892c52ab5101c825b200025d00c032c40000990000035d00000000bf0acabdb2fb60001b8200017e4979339000000000000000000000088405601251b0066b800046ac000231b69000000000c50000469c34000000000000000889c000d2222d67d5cf182980000000000055f231800000000000fb09c64e1d00000001d281d8c65509471f00000000000cff22462b880007d7f4683e1a77a65a12523e7845ab0c000072843f4a4dcbc42b11df5b5916301ed2844b1b00008528a9f295927c0001962196aca0d70a550492a9cabcb80927b684ca0beaace9372b4060a000000000008c39b21687a52e0000000000222592b80000001c0e6f4279c2d71264b7ea88e2c2999ca2d886272396345bb83ae4000d2c3708870d37811a884b02481198d4598019c4950000663800019802f2000
  | 49 => 0xbb5ca0000157000272000007e1a3c31aa00000000002d120000b3a4a732ae4d4245810a92ce5f8a7000dfa73cc5306a414c9d75d29800099d96b617600006ee130e69c06d635b18deb492f49000027a073036073e1c220f914b82dea6fc6e8f1e099980000000000d461fd853d87722602f84630858a32e8b4e2fa9ebc30818da30000000001da000000000000000cdb8000c14846ecd887522a58f8e1e2800081c03ba57b13c65cd0714ba10b62629a0f621491dece91944b4c06221270cfa5561c520d41a6010bdefa00000000000000b530000466a7ce89c1e742284000d10130070d05022c018667bf80003cd800000009c8cb9ceac00020640e1d5e0d05a39f91800000bd89d8b808000000352c99908a46a411d00003086000000000024b918940000000000d380ed40000000a09133213a0f88113157e04ce35400000ad1f3a5c6698dec44a00aa44610dda39419980bd19d69532b3c07b225b052d61a21292a22788d8b575ad6cc60122d3a89bc00002e7e90112d8b60b48cb7980006d1325e76fa3c8951800054910080003312d82000035f953600000009f5ca4200011587d0b4c249e8a7a1e700000000000cbc1fde0002da600014f801e0e604fa82904f99de803916be6deaaf4784a6bc92490ed030b1d80e580005e30a3a5bf0000c95892e120a9c8b4d800000019ee3411a870000f0c106a26400032303c080003d73273d9900000001c23d1f06f69f72e580001c92c68844eaae0658000355c00000009b98b7e80189d19feaf6077b97ba00003b38302dbc0f3d0ded241786a5f1c5abf2a7bd7fb84b2c13885e44b87dcd20a4bc1cb0000000021859901a72ac9fac83c00004848000ab5f06c3a5a3d106a912ac19c000bfb865b26222c09c135625f682485df72367304898448dd9c7259d5b05e9d5a01bc3f775229040002606526000068595b79c4c7e29f91a67c1929903238000b8a00003dd8000b758000cb9aaee0000b9617e12da056b2a81470f7828ca8f8b465d9a5571f0869b295a07b44520c38fbeae79b8a6ba0a943092cba9660ca04549562a6d91aa3699a6e8a0936288c8e8e282ce1fb8300bab32ae64b5c000ad122e9a00000dc2c80b478abb30887fab6a88a632e1aa2be005a8000000000000029f81a4284c00000001840decac630c86f19aec1ae1d340d7c0000001e77c4d9d64987b364bc6a574a9a16f67f7c000c41b68558707c359b9d04784f29a362ada1b8407428cb020a00000599c40000d9d9c2c413831a0ef05b400000007321bf70000000065f5a8abe200ca0a96e97312060be190649d783b70002eae46f1f4e000002a3c18000b42a6b00000000000000000015b80059bee0718629c6eade94a18000d69276814000000001166000000034f00000000e040000000000000058e1610ce52da8000000
  | 50 => 0x9589e1753200002e880000000e9859e00007912e8a00000009bc0000000346694580000003386000221ad04494c9dd1824751110c967883c422855200033fa7b20000000357696480006a882130e82220b41a44e8bb85ae6f604a200016a64640000000228c0000c9453102b22b717c174ca988add29703388ac819f8055a5196cca1d2e50b712dbea1600aa000262491e2aca0001e8624017b4192000000000008dc810a8bd126e93c1ba900003dacfe0000032ae0e5dea1cc00010370000a80a838c32d4a4000c0325ff85605e3c412a240001eaa7fa07da86214683ce0e8a6068af4792800097c2ba67282ff6c291f5a330933458f91126e99197d501a0c3f714ee513099ebed2602d0f8000238938c000000005480005458eeeb58a332d9e14e3aab04426a9a358d77b132ab7a0aa830c7dd678c000d73af3043301d917b200e54f9b4d317d46e5e0178a53d004c8ae9b560001954ade8a8fbf618bd6999dd27a6eea80e1357a19c9508d8006ee00018c8479811405c130234080000000000318300f41b20dc95e80004aee29a00000000000000ca000002121b2e4a832860002c8a000000041a512494540000b69d8e63a8000571763e353552f5410000b5104354cc5d24d6d8414b4c897a4f0d82528b288890380000a11178d45800073f8e30494c0fe029c5df814b1268ce93ba7a49776d8c8d4b0849928592901a8e633ee3aa90e633e1abe34b80003382e3a746993a65d9ad03ff80000003198000213049d9bca00005488edef16a511de03e4ef005769d60860b20e3431398a39a980ac59c8820d32c86149a5acba2a5c00000005f9976e30f99975df22e8052b11a9721fc99908bfa954c000000032c0108000a706afa8769902987023c0002148313a8a0101133029b95b00be0000a5380003f6aa1c00027580000d5e40e24d20000000000035c0001e640000000000009ea1906be5bb00007020c680001fb47c600004a294150ea17b2d6bb587000002e0e292ed80f9f11a7b275a77f862c0e7dfc35dcb29c3923194d7128b0cd59c29aee350cd3d81eea4f1ef80000c0c10f800015b14b600006b612c1c1c00005ba84fd7ae000072a03ab3506b98000acb82a21032f640002b800001974ac6ab3691cad5200017dec180000000000000009b27e880000001230a4fa361c328000000363a70e1a7834aaf2400000008eb8deaa9c8c7056c66e2c1e9b3085031280002a8c3102bb20949eacb152cea00008863b3800000003e1cad1b3454c00000001fe3c3526580000ffc23984f040cacc217ab0f22e82e5635dad58b67cb280002078b188b3e5f0af8027d87810001fe2ad22aba0002942bda919ca05800000000003d99a1274480949dc8359900eef80000000867831b016d02220780000000211000059aae42712c8082ba000239d2a
  | 51 => 0x1d85be6f30000d8317309f4181e7de2ae09e404a415f1c4a07ac26282ca01cb359500427aba49df18fa63904e625b80000000cb84ef80000002a0ad0cabe60000b04685000000000000000000000000070419b000000005861703000342a0310c2b46b2ed28cd1f682b30000ab670564e249f137616c83789ef6632ec8c00007f200005b00c0722e0000a29d9735300c432b20000000000167c29380000cc902600035e650daf8ab652dd4220073c5e700e2905a25e00030485a3943a8de8000c47b51e0000d5a56982681418000000000000032d20000000875c000a0b9c20545000074b80000000000c1970c0337ae5e000000059a22420001761000000000012b8000000002a65d682a207c79b902015e0321d78800000000005238000cb3010c116752488080004649854000166c00009be03a23e61c331ec84f000063f80002fc23382861e621f08b0c84c80000ad07462b3a104077e3e38ff937f23e800009d4000285000000020b4000244c46a73703c4a53abc51b3a0000000393801c0001d36cdf15985cf3334ad897882a2a346b891a4c0001602b2e0000000000000003e50001b36c690bb33a800000002390841aba8c6e14807f3800010ce21466cb450000000017d87280000000a360000b74c1ac3ba2ee6000024cb20924e00000000000a486bf2bee65f800088c05129e9000064b00000cc56b0da66e808f18dd92b74439b371bac001141088f90c721c945284d0000000000046e00002ed2538379dd10051b3c675db56461603c8aa901e200027a86b100000001fdc8f434ae898a7a6c768ed24bab34c8ea00000002f889e75df08a5b4704f589e8224800093d94e009c055e0000680c9218ae4e70b1a0000000719f16c00000000000d54cf2800000031564729c3eb899932249908eb700ffa0c8849ed5e00009fd0020b74000000016e8c6080009fa8b5ac5d342500000000000000000000075cc000342000055a87500000d8ec830000000249c7c131dc56180006bd25941fec41298ca78874eabdc0e507ec9a8ab6c89d1b110000e2a26319702558b12bb20000b11685413e54710d6e83c5da1d7067e9f0063545bc8ba93c21ef4000aaec88ebeb6b240a609b5b91b3481569a9667d14bea3c6884b16995cd439c6841b400000025a200000009d080000160000bb39ed216db02cd1f8f198e04f50ad2838f00000000002ef600017362d5000033131869a6df3854380006b3871e000107e000234a97000000000000b1900000001862b77224e944000003b204e00035040001d3c00000000002a260618e3164500000000000c4a8e3ed0214ae00000000001b28bab1dda00003df000000059d80006cfc9788064f1a4eca8aeda24000ceb90900001fa771700003b20000000000052d1ff6b2d80001092bfc85d80007029ab700000
  | 52 => 0x4c01f013b80020000083f0661ef90f6559a8a86c7ab1e09e42b87eb8000c9c80000000000595800000000008da400018b8e9c572232200000000002326acf83ac0b4088c4988000d6a939600000000000000000000000000001658ee461391f48379dd600016888359ed4bd617021081f582e0a6b524c32de7920e7a9ac71c6422110000000008c913da49c309868f800088b1a7e197717e283892da5d060496682c0aea8d520000dbb9b21baad34a2849daa5f75be9f54ae89ca27479486c52851a3659224d6f8000a61b5d2a468000000000035a80009982d38d1a800020980009681dc06812e4e0000000a848ab051f03cc0000da0d2909ca66dac0438e35508cf5ada8ad8f1323814c071aaaa669f6d9a68bef962b02dfcc3da9029bd2a22d2c1f12d568e0e3a0cf44c59332e05b09ba9a2d9229e16f5a1e61fc60a03612070355210993902950d7413d9d9287034eacbe0c80053f5940001be2291c0002214000000141eb1bb2a287d2a92aadc6c086b08443fd1eea56d246ebf20000aac18ca5be1144995b4dc5fe21d41370666b2c1e00a6b86765ef291611922cc0d1094022b05460bc177e41722da1bcc00000000008a1800000003c287180000000000000000087200000002f1004f8d91b6da43ed0e16460001b4f78a19de03bf460230866aa93018c8db2f6814c1c864b7833540d314e4ca954ccc588ea18f832039a2f123a9b4145b6994200000000000c3c7f148a85abac5c00014d872d800087f00000002e90c6312f890c97a483232b50001b930000f72000040a68ce62c9730000000131093c9e3e00000007308000000012200030745bc00000000000000048e4ec4e540680000a4e81583930000000030200000008f3470900029066730000680b2fc3808fb805829541cbdf9d1d9c50e21d0000aee8000a1701e8afa1fbf00030ec7e685626fd92504d4958e525263f471a5f4697b26e0a49f6400000005038000000116237290d60002934904c00027c0df600023e7596a9f22870b1439fda1c484247ca71983267690ea41f267ccd4abae000222ed6e064a4e9142c37bc4bc0002c4b6fa0d14000000002fb5dcbf5195a5f39dfd1b1b6656dfa360bb18aa017596280002b78729a12cb64940c0b3a82c1d11542368b2c20002782940b2a9b469074a610000220b2d04ab1f13be3a3cb4d98000797c000d08369344b265a78c163cabf00000000000342a76000008d8a88056439ca9ac858a2a422c81904ea3246c9b236665e994d2213260a60a76e8ea9a729816672082136822ea56c7973282015d57a0198f7c067caac0000000ad696f294c80000000000868800059228fe83822c829716aace383822cf2746a92ae003a034a22e7aa1ed4195de85998318be35fe230000067b2607000000000000000000266a5b0000b0422b4a
  | 53 => 0x8700004d024d44a68b180000f0060b8f08000099688a80005c9000067500000001208000000000026d20002f560001f92c9fc0008fe800062dc398cf0c0004ec22d2000000027caaae1da1424c93158abaf2f98b6ca2240d4c8467df9a1a1a72c1cb3403e65bfb012ce71a3493d19e62b517be352068242d1ee8356032e4578cbccb380000000fd4000081b012134d12e07c6a570edcc0fdc1eaa380000003100000000000000009fc086a79eeee40698dc848080007844cac000000000016f43c51b326f911d4314800002a000060100008f286e20000000d168a7ed2f80000000000bad07ad0002e386ff17227bc93f532aa9fa421b4d43ed2f380000888c1509a55e51b2c00000000000b568dda5e600000006b021cace980000001e3400000003909e0100000000000000b610d780000000000000057d151234480000002ecccca85490000000cde084f00030e08440e5a0bab56887265eca65317c00029d6000325a897c838d22ed76349ae9e82502584b5a2ebb7c00008fb80004d616e03026b7234f96b4476b12e874951c8240000ced92162bc1354d3b18e0000256e1ac84be44a19c4ada2a3036ea7a16f7a3dc000280a5b02ca4000000077880007ea400013e000000019500a68bde99d0f740000000c35800000000000b600007c52b7092508b99fb0000883809a000010600000002d0943e7f68000b36000098105a40c750971e318f44855c8474b22354fc14c7000182043ca50846816424ca101c7bf1f669ba0931c998000000183cb7a00000000000c348a40ae20000d061290da6b01e00024c870515a03f40cd8c58800085d1b8e05380000001ac290023ce26080006a111a275b09420001f360000000000000000022d44c690c961c000000003cec54000069ef42851ca3200002daa38900008a7a30b500a2280abc35a000292cd66ae7620526924de23be0001741c7a28be1f4349a8bd81365b0abda07485802a6800086d00002560000000000077c8d628b7000080d000000022264739fc000028621cd91720000000bcf82cf58b0558a098a7c412ad0e4269816a29988c4b0292ea1188163e0db04265c4731101bd60e2c0008ec83d60002a88254a5b8ae51a2a864a4ea000189402cb2fe08e2ed0cb8800000029120000000692e12854446276d794d4695186a9690297173109c29a2a626f4a797000366a8ec093a00006003d0ad053a7a27c9a19de490155072e7d6edd0040c1d3608273cd214492580004cd87ea93118ee31c93f73960be03b1962a0c2a9b000000000000914d4200000003234b9e0efa6e725da03425427f40000711a1a8000312200000005c480006aa96580c8efba4db1d86b8f0ff6c9a001fb2d000000013de3a51b4e1598cd65b1aefeb0680003c9300eb0215900000d5c00000000000000a9389760002
  | 54 => 0x3330b9b43a00018609051c7411a0e447330c7d000357270100007e080000002f360000000000003a20e9466187951ea8689c47e62e8eccf2d1e0000000092aaa20000000000000070a8000073418b57a8000000301c432aa046bd80000001f7c0002136028b3b4bcf2fc226a96b3000000028c23ba97126e00e3a38808b000069d81da00000008b8114200013e9000034200005e80000e466498000c624000adf94481619874000024088d1b78485f31ac252a346a2103658815a7ba92e7268e00000e92976892a6520d540000000000d9ee8080002a94d81a4fc7bb2662142a69a5f400123fe2fa39c934b2cbd091e5620b9c5fb8cf0013d6860000000a04800046c8fe47ff87a800009bd0001b0eadf175ea6e8000b631754135322c000000073c0cb400026ca765b4c00fa32180002efc4a9191ea2e104800017907fd29d8b378d3a0a6f3fe00017500e7598b06f04a0d064636078e9de0ed552eb6e3313578b326c9500006e6286c00000004f700009ca8ac61db31f2b9d0d8d99b00002d9082a0000ebe777160ed1c400019528cc77d2f2c27bdc48b4a051ebee252b00000ee111124cc57198297e40003ba9194000271606200006ed9eca0000000000000000000002df272c9268000483089e000000028bb31c0000000d9b80b647a9cae273830d79c80000002740000113409c8000b8d23680000000000151f5f824ec1f16eea571800000033a800015527ccb49b0001e78371295000000004af32628e380001150408b9bb1e4666c0006a18a8c4df22becec32760002fae8681dcc9d28410441a690b4ea4c6c1e15d928580a135c02caac1982a1b8170613c8109c898000160adf4426dda80d50b80abb2526aeb0b6ed069e52ca5953238e82e0a7b98d61b4a3006ba9096b528f10000000000004600000741000186fd3d0000c7e8000d7d087600000000000000000000000032baccfa54454d17f2993400000000006f6b04672601548745a22d90a1684780000c38a038a73a5e24968000c3d30acaf8abc08bea2d070ba7b80000cbe8aa00da833aea09618000000000011db014060020c3ef06fc0002aaa66a8df262789b86ffa35610c1f40424837ab748ba640f15e4063a0a2c128000000321a94481d7447a38a90c1b1c9ab8f0469735fa3a22434901b5b090a13e2d448e165002f940002bbc1f7de609a1061a1bf80561e00f6e316a8d64ff18b45731e54234a14ccd0a44a00031d6afc290c6a2ea2a80a0b10224000075298d893b873817a5b2661a5e7600000000000000000000000027e63f00000c6c80002d119590000000c3180000000276000230a8ac3340aff80009330000d23897c455b1f6d81210a43695bb2411a7a3d880001c0800066ea630900b3e4095125d7b02afed42927491c2a7e7e502ee48c800000016629fa299a
  | 55 => 0xf000321ea6580001a4800000011480ee40000000000b7910542d2006ac0880009e1238c0ffa9b212b877a4cb9ed659f80005182bec32da16a6f991fa73b9ad2493d4ce8b61afe1f5ac00cb61a5896da036793b5b4a8c9ee45aa2db0da2e2c61ac05720589758c273270068a032cdb15f802d0450b7ad30a48e20faa9417ed2a8c75c2dd98a8000000010d9748a8f62e630400008158628284800076a93042bab2ef64687ee0b561607bb9ba54631bec00025c2d6a633696d00008e9000019000003af238594317fa48e8db022c0b7f298f30e074117faf4db9a974a6969e4a09800000009f4a265bdc83d400002b61bc000034414d6258676600000005d38c0f0c4ac8eb0eb480c2e000000009d6c64c000c3b80002a200007068000a03167a63b00007c9000079e800000000005648000000000051b03a63608d1ed694000d8e0000123113ac6380000000000000239287100009029b026630000920000000000510000000504834e269daee1dc00d662c131e5d2c54437f0000000000013d24c2c6800000002b9600028e229d442200034aa00000722af90a83886ec4597516444e0c020002a4200025d4000052a0000e5ec11208a0e2736a000335c065826a827258c6b1a7ee7ab80000000fd28878b6a0003412c788000b94a8eaad568e4373963a1e689644539ae0000033b9561f6c37d2488154065e1c12ef22131bb0d450000000000089e93f600030f003d36865751052b31a25640427862fcb2b01ec06a2786ab141851834ae0973a1d1d0f071b1a4730c41f09ffa4e8172b47706c096683880004350c2f000000054956549cb80001e0800020391830000000c109e56c463374000342718701f38449fd6577261fad407e62ccb624b59993eb92058805a125c00000003c1ced8257a25a91880000d3113e057039b0000000000000e8982fe66304b02c3380005940000ba09ba481529d00001c02000000029e408c9c540a38d9c27e58d8000a6d05fe0002af05ba921841091a638791800001154000359051e0aa2923053eafd1770096a85e01800005178e34b2f19c02830b38b4883e29b7005014d000078621f80000af80e2000004e000000000000002a52907800013589da3ab94170000b082a783fc0000a76a748f8c000000018480005d080007ad80000000cda31980007ec89127cf000087d80000000000000016f000000071f8ccc00000002541450ca6248a65b0b9444f2142a5498a0ca289e423fa58431d305006602bc000175619300006c83682798c000c66801e3491cec6e791a8b4580000000c22894b1f03d7afda0771c9f84ee9f042faee825d10a08e6a268cfca1ea1b79c763e7637e194a2c43e7d2828d300000e8800017e9ef49278000a5f9c3cc222744aa11dae66d00008668b1c000000000011cd37320820002184505
  | 56 => 0xd58967543644d4f14ac23f000000034fa0001c4013832947e32d3c0400518000060892ec000ac8a95e000212a946b4810aa73f47ae80003f108200000000050b5bc000085854ee688c700fc278ec000d66000088e2a6c30db44e69227ac473e764d5b054cca413389fc9d1437c21aabf1800068e89ea06f882c1daa9fc0001e380d4584665c80000000ab4d6222d30003020a0123b40000c500321c56443a3b9cb744f31f809fe5efe31c87408b65004046000361072c8000c288e3d0000da4000008800000002e2b63c53280001912276d7e00000002bb3a039d7e7201d56296187c4709a40c0d807677501d4bfe800000000004cb01180002b8672fc0000000000cd280000000000ba526f8118ab8e00000004ed00000003422546148c1ec82d7000000000000000000434b9300000000eba0001cbd5d3310c49780009dfb2064531c5e000187300000000002e6200016260000000be49c323649e5a7579af8000000000002002594178000222b000000073c80000000960000000000000000000000000000050a00001b996969e025406d800001909b3c08d9bf2962929600007628fd030c00031f8877800095500000000000d4a800000000000ca81c4000000000023480001ff88f48000995000000018e800000006ca80000000000a292960d9a23022b580000000000c7fb138d2f27f6000145a75ba382b9a1d5c000200a00000003e891fd73e84665890000000009895207fe0001da400000000000000000000092a80003818000000315acc28000d760c8c000000024f220ca8a1ec635c87b8a7f87c100000001a1aeba705aca6000000000020ee6760a06c850000833c32489334868b0b346066800000028c8000000081216db80a94dec3ac000701b19c1f50000000185666992eeda2929e04a251e8fb0d4e00035846ef2b4ca8fe614a47a63c8041db0a9d84c69b7915a0ff5fec495a99829317b679fb5e47b313e79d4988e4910ecc89c8ef8a32a126000189acd60c5dbd3b2e031e1b0602119ead8a303e6c6000005ba4b0c6c23c00002d425708000b4097d60089b5c6e40aa797d800000019160001df600006ac806e4ce0001413bc60000d7c8000a99a5002ebb07e8bf8000000354e4d3b0580000000000268a4c9800090a979e0002e406c8860694db3b266b0315c40917ac48000062b496abdf00ae000000002e332cb4a87a4c0d098a1742218671a6b2be740002e2000041c93e0464e380000000097272ea953660bb1330e862d800043b8000ac380004a485c0a0c340675eab445a244f10002ea249c8000000000091b0000467987682f4b7029c0000366000000000006d980007f49a8a00004900000a92d08cf323a18a8b2aa000042980008c52ac2690575a253a5bac0aa71a000359698985fcd18b3aa00022a28091f460001e0
  | 57 => 0xf000000008200000b2b0000535c0000000000426000091db13e0dba1e6c6da930c342d5a00000002898fcd0000eda90c40001218000000000083b000000000dead7e3f65d729f60a2800055c8f20d3c2a142329d1c8cc07ca7c41cf4d751b6a588b660156e4e4c8f8000000033882b8000c01000028900000d782d4ba194e4c2d9a825b4318a4b82bd400000000001bb4c26b27525c81a8b332920788000061922f200000008b394847c311db6e3c00081aad9e593b0261570000000000000000003e1118a6b58303768863a000000014f0f3a28f8000d1b4000935801a00025a60001dce0000000857974668b00005fb356a000153846bc000da6c00063c21a44500b16d030000b4521be000239e6bec91060610b025b00008e110e82752b6e01364823e1452e7ca12b676f11684f60be8612826126d0aff2f92c9491797aac0180000000000c398a846028e663888000d7a832b7228bc223b1ce058308cca3edd00788a576c230385b310ad7a30b6871c18c5c17c97c723c000046399d76548000735218ea1eb4ba75500000000000000243a0003622000100c743da4e00017b0d69909dadda4480001d829dc00005b1351c6b300001ea8cae0b466160002878b3b0000a1c3672305b3ba292a71c34e1fc411e0ee278526e7b2101f4000173e0001b8892983b26fd2b42a491f3e000000000000004c1886c0002ee000027760000000bd280000001ba8761000000018306a699e800000000000000000000000032fa00015b20002638b6b2146000281a0cc35410000f8a000329e1cea4fe1019eb2634ad54c9f99369d35f7a73700004f23675000298a0002bd00e6a15051395d8237938e0fe317605f18508d11ecf4ecce28c43984947230ae6300000027eb02a072a8ab1382c8cc12892991ae2a45b956ccf60da843f54c6c9712fa53b059c31f94747ee1df12671c284c212e836c921a572a94031f1842a63aca2c69a32aa3eafe2c1b81123d200004bc0f5a97fb28e000000011c663a03980004e508f689211d69aa8000b601ae4b218b6949082474cfade206119f08bb2dcc1c88000000000010b0f22a0e20a4c908e1819920d061b1ea8c72980ed92206e288000086023bc00020bf8f3e8d20002fa26530000d902088000101600000346bc0dc00000000000260800011a4a168d427dd8d32ab98d4a382a2941f21732b3021562991e5b42e00fcda371d4c902c7e0b91e8a16100008e9ab9277cc3b600028f4a86270690317d4c7418d05a6b3e01b2b5d6794194a53f400000027ba00005541a215fe0afaa38bca8eb49802fb092a21bd65f190e2a70f6a00026a48770c11cf68000174800000000008f500000000508d9ac148c59b43c1ae8f7aa3d89c200000000bdd42266e000056a0000a8d9ba2ad38b4c5e688dcc002a5a5418b240000aeeaa
  | 58 => 0x48aec21c48b015020f309099006178ac70afe13ee112328ccfa2eded11404a31781e067e221745b260e97700000000a3c1942572a7500000000000000093600000002ffaa7c229800027f0c965849e3c4d8000000030cc5f1364c4498e1a00017a6000000085040002656e9c0001c26d2a00000f280006598000ccc1fa000000000000000000289c000000000015440001ba00000000a7087a0742847c0b7a6ba00002142150fe631634f20000000100d554000243c231000000018e62df468ed4e00000001bf84110e087978dd09329d05419c74ec2e86c4a5a02d3b54122fc170000cf300000fa8000a310000bd191322181bab69080002e8f0eaac498bc9582a9a08e85dc37b8000a820000016a444210a1d6000256667c800028798fcaf4926804c07fd5192fcc494479382385e60001df8b07ae540002be54b309b7ca8067c94b40000000b22000001d735afa400000003f60000d0000000000000000212000001fc9c319fc50c80000270e5c0001e82af78af6d2d35a2000000000001710924000bcea3420002b580000000c0f209e1e134e600029e0b90b0961488a50cf88aba000136400017dc378289000003be257000025a019e31200000001e2600000004fe10580000eb952890c41aa8000a991dffcf98d9e894076000012c4bac8f7e177b4840001e10000269400000007708a28000305acc880009171cc600000b00000000a26aa16c3f047400010c80002d2c327a5aeb971056c17910a0002c61473213d9ce8000cb9036ad11cd6852a2e18c8f1078c12c1fab5e88641d99c213ec80f0a768797506000009e0fa863733c20634b663c15151073c25cd495a3122f201e638566a0a81dac12a00ac7651a24d6311ff0000cee1cbb6526dd0145bfa9f8b2748000bb6a26600000000002f34322580631d8000115aed40000000cb18d7a0002da0329a3bd2f008a20000794058400037911f836101f6c62000029174421ef0000d13000000000005528eb225c154e13b1faa371d5ee73a0000000137028e08040c7828e150000000012d46f735cc5ee149054b0916000000053a1cca55213a6780823e21bab28d7c255e98a80000003010b24149a0001b7c2e180004ab971e92c9b4c302a9350170e12810abc7cc188322f5b2b8571213e4bf241036b36506d2239c0000000000251800525fc183908203b4daead49fbe28d887abeaebb6062a5be314cb9a5dd198a00000004bd12bea1383620000000000000000000fa302c000570e76c070c000379b4feb1615f600014ea0472564000000000000007f7617e00001810002d860001b6e0002d040002c149a39fea86e1200b0e00000003228000183e00008ae0000000bc303d0000000000033be7cb8e848af22deb1e0000d629495351a02200000000002407a2a9728d32a978aef69589f0ae
  | 59 => 0x9860001a8d45c09ccd2d9ffc590c000d1ac000000102cd38800000000000002f4400003dd0000000000000040e9e808fa048ad520e33882948ad6c9a9444d8ae8000261aaaa1ec16940b0600000000001f3abc793aa743912fae6075e4f30a6608556dc00008eed40241100000009d5235c0000000326000044502609910fae46223e1a34053878216d8407affc000252400000000001062259c0003530afe767a588000025f62400000001aaca19a18a9ad000088e85aa51281b4557800000000000000000c27986e00000001d84000a4e000072b2e2ebef00004d2ab9f00000000000ddcc9a87a63e70000ac0000042b90ba0b8985a0000000000000024904e200000bc00030b4b058cce000258e0001f348140feed1915d210140006a800009a600000002d3e00019bcd35b4442cbe47e00032b10000000000000000001640000000b062fa000000000000840d1e836800000000000000caf21bf2650000d870000000185e956b62040f9e7d5702ce82c9b430b24ab540001c6027866a06936abe4e02ee28bc000007f8c18aa0340e0000f0a00029cc9ec143838806ead5125d87a12b59c5794dc00002160001b5000006941a5a6ec000043c90d822ac730b36aec0000000090a5c297830000b72c4c196ead1a3d60000c6331185744e4a37c48a03c0430a26e0938d06000191c77e8bc817931a8c648000229e894d9c35eed7d9d530a6530cd4e84280002fdc081ab04bcc9b84caa9b860000000069000021380001ed800036140005c00abc73a8000091ad40d02a31a87c0000000000063256ce00000004458000000081052c0000000148241800006a309f48160bb9000294a00000004469879048000033a800000004ce7a41a891c90c9290612fe8451b420a32a5e00000000002db400000000001661b9f00000000bce00000005fd628e643098ed8d0fec00000000002d56828294c8d3a7d6ce80f4a8570809c5cb451da33542c1db3ded8baf22ccda1bc1862c201302af280497a2b1bdb080000000000000000028f20c20126acb21b24f38336711c00083374e4a598282000000000004de94e5f604fcb1f4a2b2dd800036308e51a7c000233c47022787e99c729c6026c8a21c83c22a8865b4b1bc19a000048b84ee48503741e38d200002ce20000000c77a15a7e219ca15c1d513eb2a96aceaa7078ba05ca4a99003ac1d5d3800b6b04b07a9b98333277a8af268a0a461dfa6ce00003705eb20e67dc8e7cc2c80008874000031a57c5ca45ce191ac7200025231d9485c16889983ca9dbad80926087c80001b52e0aa3b946a0002bcaa9b80000000000d5614f0809b1ee8d4a0742d8124079f367e7e78866c2c17409e0cb460002647b2f928878c800079e664c84e30920000d947c18f1f997000094850bb1170e1c0579ed8d9520ea66f8e3c5
  | 60 => 0x2433000049a4606e1231b0399a0f916a4e7b65aa1400009af800000001c81061956d5c161e6d2b31400017a1d868bc6d3f1e70c43653ead9014c5172b2a2f416de758a350b39aae1524911ca3f176c448046a36a9f8538300d84f01855c5e278ed25ace429de204000017e44206ec388c402ba993d068b800000005a0017a41c7710000b19aac0000052c093486867a60929865cf6727b60e8e89e400b492b5cccc386bd0869866795c1268b3884ae6e964f46eaaab880f67138bcca8017106e9c000246b6141e79e460002a021cf9d31cc4308085f262e0000ded00005f49b00afacc01f4846d0b2700018004d5e1a6000176400000003e92c9e4b08000149a2ca000117c55827876984b689c2b68024609a60000a5ebc8260a7b70ed0000000000000000000234d2715106d8b36078a8132b9e9add000000000001ba6164000d700000000000000000009005275b9b288c000287c77282459eba789ce0209a2e953fa83112484f4ccb029cb19000000000000000000366c0000000a50ea9c8f240009ea9b8c6912c3c90900007c3a0b09e51348c30888ad782cf42b6d640b968b980001382a25b2a32f5254a8a283ff00029220b110ce00000002b54000cbc800000021b64658f280000000000000069880002ae0000b42000000000003d480009f6308e0000000000324a599a54bd51800000000000001e42549800000000008f7838c4b9c00000006f842000009e5b4ee33b00000000700171159cbfd0f2e2a3b5ec6221a32da1029490897384bad2b2af11d789f68000bbd2cf61f32dda1c29d4225289ac8952be738fc1442fd10ac8e80000000044b00000008460000c5b836c89b00000000000ce100001be80005c631ac090800000000000002fb20000000af3148834603f63bd806e6fe8e6c00011b0cb507f600015aeab2062b43616042b7d1e459c8ada5f01c4475a81104d58d51507000049aafe85a41608c02a69e00000007dd0d00d8619805f329dca4d98aa6eb9aeb75f288000022224266258c8880003152c44d49878600020e80001f160002c88928b5c8c6119a40000000000000040609624fb0000c49000000000000001f736880a34807d50a0003498000000048f8504000212e5a8339a00033c000024840c980007e1ad4eb0a0000b998000c7f030b00025561ee8c2e65900007360b0e00004d0d331d15207703a0000e1094a00005c6800081334e80c5908c000000021d40000000cd000035fc130800000000000001b6d000167000034020000b77984413c220f55600019d200003804ef00000000000ac2852800006dcb3fb1400002d0f24f9cba00004cc7f84000000000000004e4af0e8c068213ca0002e3600022ac0f361980002c0698e5e610002d26536ac0a198485048384163a488b8000203074e000062240006578
  | 61 => 0xfc785e8d28000000087a19105188000c448c82a351f1e6483028c2aada937e13226ae8be6bc11a2674bd5a25348f4c8c5645a7a651eca0802cc806997801e9a460d9b01ac9e14f9d69dee278dcdfeac9a4fb95c02ac18cab8c551825eaa0800092d829e43827509e7a02033da21f6ac858cd09955a0001e2c3349ec300000009151930a44000000000008822ad83320000a9a83b09470fe20000ce8a0d000039008082b808daba4a7d4b6ba26a3852da78d78f4e0003458000242e98d99405fd8ec41750c2630cd1316d002b062004015c227c413dcbdc01c4000bf10000000000000009a000024fa8d56503264d89cd4fa7ccd8d8202124b4da7ea2219ba32331000000000010ec0001b1a9882ff07a71f4c1311574ae2ab320000bdd4581c54680286aab480003f7a5490a7233e27e80006c913bfc799528846800066c400024880008400000cd525ac62888222809a9e0002d34718a03a6fab04000022e99fe2387000133ab323258000250e2cd000039aadf64aa800038da2373993062a8f969446b9e9e47f996099e8f82c00904c7060c042742f1c034a3749f86c96c8498e23582acc08cb4c42090fc64cf1318742242c1a32964198a1943d6031cbc182e888da90e0d2affe9a318081b08be3b119a80000191254311f20439d680000000000000085b0000ae70000bb718be06480000000000000000000000000000000000000000000002d780000000ff0000000030b03e039d92b71c5636440f5a103038c7fbf80fe0339b39297e02cbac2056ab18d0047b9a6c612b012a5271adc0ee172acdc9fe0928215208c1344525833c00417e727baf9a78d94344fd0ad900f86cc0000d36d999c825a60000c1c0f40a55b478c9d0ee6c1a00003d07210216b2b68008c64000105a5d280008020db9d58000000008aacc3400045d25909e8adf80001f6a9021ef06ac368ead80c443599e8e20687e35e6095ac4f22d1aa7a01469d0908cf3aada05a4000561138436f8000c50ad180001751098c4ba4873208b3f16e492385e0d0400000000000c67b34400004ea1259fd400001b72c14a6a9840d4f99200000000000000000000000001452da2565000091088ce7828000ab5a9f491d0000c393366737a3f2741c000610135ec68400000020fe0000a431cca7489ef80000002d7d28420f400000000000000000172e000368300000009158c3800003c6bf9316a3d1cf9a00030f800007564e817c6ad99c7866232c06efac2e0b72cd44c722e2155b2644ba6d8a21f08565398f9100007d260701850002e70071d68424e2c5500180cc5434fc530b5892595e728c1a9b0c3db122c5e38afd24ae38675c808240088289e6085100001040840090000168c6d4a38347c26f6694754ac3f992400000000000000d2495e8000000007580000000000a588000
  | 62 => 0x280135801c59e4163e321c20fb36800000008d001ae3dfc0005a2a01d38c938856ea66e00024204a3142a0000a981d22378d9e4ad00001868d531b38c310c79000325200036980aac00000004323ae2514059800012d0000d9a4c4cb3c8aa634380000880000a6494400001aa546613428e58390a9624b86788bb6812869e000274c37dde9da008000b1a2178226a07a6dc800000002fe11c95d3b0d8000091159ec5eae06000008011e800026b8000aa84000953a78f7215e98000273652eaa2e7198000000093256f80000000a900dda628aad8f5400027c0666928e0002c5000029e83f2a6ea00008a00001266700000022dc6e4d5badca116000000033d2af189449cfaa985c7035600005c200000009888d8fafe9fc20000ba801f0000a1f8fa01ff00000001220642ae223d562003a6800000014adb0ab12cb3b850525f8000252267e000000000033c80001ad400000000000d8c4b1ac4283f0ff29c09bce0001d904655030a1caaa00fc136e2b0a60cc8015202d2a6d61dfd7442ee269dce7a02e938938a4b42e1a56a8b073f3100e9b688735559298b1e9f02a0a0000823041ed7a0c6eb622c0c38b00000001cc0d1b863072a9977179d7cad9de856a5eaf522321986258da9c23cb60a99a8f5771e83489360754264959648795bc9ecac6087d757f438a464477102a366b0de10e35ac8fc00649bc9f2caf3c43140900008c5a4da4e8b11c000044abeaa0d88f6800086c18f6b440f1c2b99ed053ea018086f662d3e2292bd99fb04bc91d82a180004e6ac490001aa81a98c424b4800097eb30262900000002f540000000b2a2ed69f801f86642dde0000a8d25500000001f800001bd4320c0003624000000235a000000060329a67240d836d1b536073b1c4c370000d8aac56651c2cd96020257548000c518000000310877f0eca0000346a1204fea0180007ac00003c5800029691109379e8ccd7918500011306ad6a44c021aa706e04702ef32da821af4052e741ca04223c62610fa5798cca57f26fa00987e886eafec41b84fca109b169b92ae84c58e906e480008a420da5ac800000000001fc168200007bf8212d0c3fa8b2e57416d6a8b2945da5176761e040e29ec000121000028897520cf81943c7824fcaee7ed000000075ee918000000000026150000000aef8a196bb5c2458c94589a0af9c153a76200000000001fc800002a4c8eb3d627e08e8b7ba9145ea32a679741353a90d881699cd200028ba00018c600029bc3a040003318000000000000028326650db874588f461caadc000000000000001fe80006f21ab80000000da4537608a1884c1cb20a7d58000322aba900000f24c480008bf176a6111db4924227e3a0a8bcadbc446a7849840001f0a82d80001fe107a1b96dc3afa6e440888c0800007c49b08000d1b352e227
  | 63 => 0x50c1cdc0004bb1122603686839f8bbe474871c1b600002cb1e3a1eb2f785c82b561442c98000017626f306bca44efe0000dd2756000000023ea2b49a0e07c98028390000830713420602c232880007270068172065600000007ae00004818000a7980007f93424bca080a0000000778f3dc81986d0282800089732be00010f8306aba037503580000000b810d6ec2115f010bb0a600000002ca951a57c856e0001f4b0000000759a308000063c00029480e35d023e627327e12d98aed2640b0f906b4408000460876ea4c9ca86c41714842291c0000ca8d2e00360000000d741c428592c2203e20f212ab58e72d00002b79cbcd9381e40874592afd80002ffec022fb8000aa19abcc9f25ee000000030a8000000355400032a46f825ce697c0000000000da3c00053f8a78165029606d80009779c942e41e04000246800017c80002fce295594e40a310a1d8c2aa4142172c45afa84288000000184500006b40000000678090ca6e2f826610afc0000000779400000000a416b1314d9285c681128de17c333a00026fea5ec0006996cda60eac74c241d26361c000cce1d88000030432180008d8ae2cb878a08201802cda49ab46ae65b0000178700000007e4137e0fb80001d023bb82fb4cea5a800000019fe5858e2ec13122a904800028128ce00032b30002ac4000179630d2d6851f8520000111800011ee0500000783800073f172c95a14e25e0b0be4df4000d1cb016d9591e82a8553c0002116b5e0000335066ebd880000000dbca400000000259600a2aea00000002d4808ad4d000048100007fea64a51d8fb60002be4b73800085500003f3800000019185019ea29848c88c942f0a7d8965
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xccc63dc941440731dd0fb1282880563b21f625051000637baec4a0a2000c6c75d8941440019b0c7b828288003a518f648c5100074a318c918a2000ec463d8a31441059ccec3146288003a9190628c51000762318c518a2000cac72d913144001958e43226288003a50c4644c5100de5c380c898a2000ccc72d8d31440339b0e1b1a62880463ba1b724c51000657b26e498a2000cac64dc9314400199ec7b92628805b3318f724c5100947743ec498a20158ec87d893144001970c9b8262880872d1db644c5100de5a3b0c898a2000e946319131440079a8edb9a6288067741c3734c5100ce6a3b6c698a2016ce476dc931440259c8ec3926288003781c0724c5100ae723b6c498a2011ce4761893144001d48c83126288003b118c624c51000c77c3ac510a2000aaf8458a214407555908b144288002b3e0d62885100b56641ac510a2002ae4819da21440cb95cedb2442880038bd97648851035e57b86c910a206bcad70d9221440011df0eb2442880029be1564885102a53642ac910a2000acf83592214402d59906b2442881932b9d8648851000717b28c910a2000e2c6519221440d595ee032442881ab2b5c064885100b567436c710a2062cce76d8e2144001d1ec9b1c4288003a3193638851034e67b86c710a2069ccd70d8e21440011df0eb1c4288002abe1163885101d556422c710a2083cce7618e2144001d1ec831c4288003a319063885100b76231c6310a2015ae4864c6214402b9d0e1b1242880063ea1b70485101cd57436c810a206bcae76d902144001c5ecbb2042881af2b9c764085100075338ec810a2065caf70d9021440cb95ae1b2042880023be1d640851000537c2ac810a2053a6c85590214400159f06b20428804ab320d640851044573c0ac810a2087aae8619021440d595cec32042880038bd94640851000716328c810a203acae711902144001d4ce232042881932bdc0640851032656b80c810a2064ea61019021440c9d4820320428804ab3a1b630851034e673b6c610a2000e8f64d8c2144001d18c9b1842881a7339c763085100076338ec610a2062ccf70d8c21440c599ae1b1842880023be1d630851000557c22c610a2039aac8458c214410d5cf02b184288216b3a186308510426673b0c610a2000e8f6418c2144001d18c8318428820fb1d846308510415734346210a2000ea4648c42144025d88c71884288046b92193108510007523226210a2012ec4634c421440237c10098842880872e9db64c41100365d3b0c98822019cda76d8f10440079b4ec31e2088003a619063c411008d75436e58822015cea76dcb10440237c503b962088056baa1872c4110016753b0e58822015be2811cb104402b9d4edb16208800b3a9d862c411008d75434438822002cea76887104402b5d50c10e208800b3a9d821c4110
  | 1 => 0x8e9b9ac48800333087735891000667906e6b122000ccd20dcd624400193ee839ac488003271d0735891000657ba6e4b122000cac74dc9624400199ee7b92c488003331cf72589100065a3a6e2b122000cd473dc562440d795cedb20c4880038bd97641891000476c3cc83122000a6e8599062440014db0b320c48822eaba1264189100056741cc83122000acd8399062440011df0eb20c4880029be1564189100053642ac83122000acf83590624400159906b20c488222b9e05641891043d57430c8312206acae761906244001c5eca320c4880038b194641891032753080c83122064ea41019062440d399cedb18c488003a3d93631891000746326c631220008ed8798c624400155d09318c488002ab61263189104156741cc631220008ef8758c624400155f08b18c488002ab211631891043573c0ac63122085ace8618c624410999cec318c488003a3d90631891000746320c63122083ec58118c624410799ee0318c48820f335c0631891041f63080c63122083ec41018c62440010ff0abb6848803a1f21576d09100145e422eda1220008df835db42440071b906bb6848803a1fa1776509100043ec2eeca1220038de83dd942440011bb07bb2848803a1fa1676509100043ec2ceca12200087f855d9424401d0f90abb284880022fe1176509100046fc1aeca1220038dc835d942440011df04bb284880023de0576509100043f436eaa122077c3c64dd542440018b8c7baa84880df1b18b75509100043f430eaa122076c3c641d542440018b8c63aa84880c71b18875509100043f43ecaa12200087c87d9542440010fd0e32a848803a1f21c65509100145f43ec8a122000c3f75d914244001878ebb22848800317dd763509100062e3aec6a1220068ee87d8942440018deebb1284880031b1d762509100345f426ec99220008bd84dd9324400117f08bb2648801a2f211764c9100046fc1aec99220008ef825d932440011ef02bb2648800a37a1f634c91001c7743ec49922000c6e72d9741440018dce432e82880032b9cb64d051000667396c7a0a20118ec865cb41440018decab9682880031b19572d051000657b22e5a0a2006cac645cb414400199ec6b9682880033318d72d05100ac77c3ec5a0a20008ed87d8b41441150fd0dbaa82881770f19375505100062e31eeaa0a2000c6c62dd541441130fd0c3aa82881730f19075505100062e318eaa0a2000c6c621d541440b90fd0fb2a82882261f21f655051000636396caa0a205d87e87195414401d0f90e32a82880031b1c865505100061fbaec8a0a2000c3c75d914144001958e5b2282880872e1c364505100062fbaec6a0a2000c5c75d8d4144001998e5b1a82880463ba1b725051000637b2ee4a0a2000c6c65dc9414400195ec9b9282880eb2b193725051000667b1ee4a0a2000
  | 2 => 0x76458d100061e3aec8b1a2000cac72d91634400117d0e322c6880030fdd46458d100061e3a8c8b1a2000cac72191634400195ec9b92c6880032b1937258d100066631ee4b1a20068be87dd1634400187eebba2c6880032bc837458d1000656906e8b1a2000c3f751d16344001878ea3a2c68800327dd37358d100064e3a6e6b1a20028ee87dc9634400195ee9b92c6880032b1d37258d1000667b9ee4b1a20008ef80dc963440011db01b92c6880032bdd07258d10006563a0e4b1a2000ccf731c963440019c8e5b8ac6880032e1d37058d1049e4f3b6c831a2000e1f65d906344125d2ae3b20c68824ba3c836418d1049746906c831a20008dd8799063440014bd0b320c688002976166418d1048d4f424c831a2000ace82990634400159b05320c68800237e1d6418d100052fc2ac831a2000a5c85590634400159f04b20c688002b32096418d104854f430c831a208fc9e761906344001c3eca320c688003871946418d104774ab88c831a208ee8f20190634411dd1a40320c68823ba60406418d100054f424c431a2000a9d8498863440010ff0abb6868803a1f21576d0d1001c5e422eda1a20008ef825db43440051d904bb6868803a1fa177650d100043ec2eeca1a20028ee82dd943440011db05bb286880021fe157650d100743e42aeca1a20008bf845d943440011bf06bb286880023be097650d1001476412eca1a20008fb805d9434400717d0fb22868801a37a1f6350d1000717b2ec9b122000a6e8599362440014db0b326c488002b3a0e64d891000566c1cc9b122000a6f8559362440014d90ab26c488002b3e0d64d89100056641ac9b122000e2f651936244001c58ca326c488003a3d9363d891000746326c7b122000aae8498f624400155b0931ec488002abe1163d891000556422c7b122000e8f6418f6244001d18c831ec488213b160463d891042667b80c7b122084ccd7018f62440014dd0bba6c4880029b61774d891000717aa4a9b122000e2d54153624400155d0939ec488002ab61273d891000573408e7b122015ae5811cf62440014dd0b21ec4880029b61643d89100ac7743e63b1220008ed87cc7624400155d0998ec488002ab61331d891000656316e8b122000cac621d1624400117d0fb22c4880030fdd764589100061e3aec8b122000c9c73d91624400117d0e322c4880030fdd464589100061e3a8c8b122000c9c73191624411b96ee2322c48800327d9373589100064e326e6b122000ccc62dcd62440011bd0fb1ac48800327dd363589100064e3a6c6b1220008de8718d624400193ee831ac488003271d063589104666bb88c6b1220068be87dd1624400187eebba2c4880032b087745891000657906e8b122000cad20dd1624400187eea3a2c4880030f1d4745891001c6f43ee6b122000c9f74dcd624400193
  | 3 => 0xab222000c6d20dd5644400187eebba2c8880030f1d7745911001c6f43ee6b222000c5f75dcd64440018b8ebb9ac88800327dd3735911000667906e6b222000ccd20dcd64440018beea39ac888003171d473591100064fba0e6b2220028ee87dc964440018deebb92c8880031b1d7725911000657ba6e4b222000ccf73dc96444001998e7b92c8880023be03725911000476c06e4b222000c6f751c964440018d8ea392c8880032bdd0725911000667b98e4b222000ccc731c964440019c8e5b8ac888003361cf70591100045fc3ac83222000a3f8559064440014790ab20c888002a7e0d64191100054e41ac83222000aaf82590644400155904b20c8882630f9db65191104bf17906ca3222097e2d20d94644400117b0f328c88825a8fa1665191100054f41cca3222000a9d83994644400155d05328c888002ab60a65191100045fc3aca3222000a9f83594644400153906b28c888002abe09651911000556412ca3222095c3e761946444129c5e40328c8882538b48065191100051f42cc63222000a3d8598c644400155d05318c888002ab60a63191100051f42cc43222000a3d85988644400153d07310c888002a760e62191100345f43ca632220008bd8794c6444001c3ea7298c888002ada0732191100055ac0e6432220068be870c8644400117b0e190c8880028fa1432191100051ec286432220068be87cc4644400117b0f988c8880028fa1731191100051ec2e623222000aae82cc4644400155b05988c88801a2f21176951100046fc1aed2a220038dc835da54440011df04bb4a88800a3b20976951100051ec26cb2a22000c3e76d52544400d878edaa4a8882078718f549511040716316a92a220038de83dd954440011bb07bb2a88800a3ba0b765511000476c16ecaa220008bf845d954440011bf06bb2a88800e3720d765511000477c12ecaa220028ec825d9544401d17d0fb22a88803a8fa1764551100345e422ec2a220008df835d854440071b906bb0a8880023be09761511001476412ec2a2200093f87550544400147d0caa0a8880028f21954151100061f3b2a82a22006c3c7655054440fbc38c6aa0a8881f38b18954151100365a324e22a220018f4865c4544400d968c8b88a8880021fe1574d8d100743e42ae9b1a2000e1f65d936344127d1e41b26c68824fa348364d8d100052f42cc9b1a2000a5d85993634400159d05326c688002b360a64d8d100052fc2ac9b1a2000a5c85593634400159f04b26c688002b320964d8d100070fb28c9b1a2000e1c65193634411fd1e40326c68823fa348064d8d100054f424c5b1a2000a9d8498b63440014bf0aba6c6880029721574d8d100070faa4a9b1a2000e1d54153634400153d09396c688002a761272d8d100064e31ee8b1a2000c9c631d1634400117d0fb22c6880030fdd
  | 4 => 0x2c40010fb0b3b2858800e37a0e7650b100046ec1ceca1620008f6819d942c40010ff0abb2858803a1f2157650b1000477c12eca162037c6c62dd542c40638d8c43aa858801a3ba1f6250b1000637baec4a162000c6c75d8942c400d17d093b265880022f612764cb100047b40cec99620008ef825d932c40071dd0fb1265880023b61f62d07103357340ec5a0e206ea3c8559241c40018d8c5baa83881730f190755071000636310eaa0e20018be87d9141c4001878ebb2283880023ba1f625071000637baec4a0e2000c6c75d8941c400117f0eb2083881b68f21564107103257340ec420e2015cea70d8841c40019d6c4b808388057395db628c71008e72bb0c518e2000ec66318a31c40031bd0fb1a63880023ba1f624c71000ceb43ec698e2000bd180d8d31c41339ceec392638800279a1f624c710004f3438c498e2086ce77618931c4001d88c63126388056b9205628871012c77c3ac910e20158ec8759221c40014df0ab2443881529b215648871030c77c3ac710e20158ec8758e21c402b5cb0d18c43880573ae1970887100ae74432e110e2015de3815c221c402bbc102b8443880573a98570887100aef130ae110e2000de2315c221c4001bc262b8443880063ba1f62487102157340ec490e208bae681d9021c40011df0eb20438800a3b21d640871000537c2ac810e2053a6c8559021c41055cd03b1843880023be1d63087100147643ac610e2011ae5868c421c4025d8cc7188438821ab9e1931087100976231a6210e2002ceb865c021c40059d10cb8043880033ad91700871000674b22e010e2000ceb635c021c40019d2c6b80438804778e05700871008ef040ae010e2011cea615c021c4023bc4c2b804388003788c57008710006f098ae010e2000a3e8590f644400147b0b21ec8882638bc8365d91104c716906cbb222000a3e8598f644400147b0b31ec888002aba0a63d911000556c14c7b222000a3e8598b644400147b0b316c888002a7a0e62d91100054ec1cc5b222000c3f759d7644400187aea3aec8880028fa1473d91100051ec28e7b222000ab6811cf644404356b0239ec8880022fa1e53d91100045ec3ca7b222000e1f5394f644400147d0bb96c8880028f61772d91100045f43865b2220008bd870cb644400147d0a196c8880028f61432d911010c5f43e63b2220008bd87cc7644400147d0b98ec8880028f61731d91100055741663b222000aad82cc7644400d878c93acc88801b0f19175991100062f39ecb3222000c6e72d96644400187cebb24c8880030f5d764991100064f39ec93222000cae72d9264440018becab9cc88800327d9173991100364e322e73222000c6f655ca644400195ec8b94c88801b2b19172991100062e39ecab222000c6c72d9564440018becbb9ac8880031bd97725911000637906e
  | 5 => 0x1036ad057010520006d4a0ae020a40409ae84dda314800135b09bb4629000279a07768c520004f4c06ed18a40009eb805da31480012df0aba462901065b215748c52000763988c318a40009e980dd931480019d301bb262900023ba1a764c520004d7c22ec98a40409ac845d931480013cf02bb262900027ae01764c52000673988ec98a4000ccc311d931480019c8623b2629000a3be00764c52001476c00ec98a4000ccf301d9314800199a603b2629000339c40764c52000672880ec98a40008ef865d131480011d90cba262900025be15744c52020cb642ae898a40009eb805d131480033d100ba26290003b10c4614c52000ce743c6298a4000ccc768c531480018de41baac9880031b48375593100061e3aee8b2620028ee87dc964c40018deebb92c9880031b1d7725931008c7740ee4b262000c6f751c964c40018d8ea392c9880022fe1d64193100051e42ac832620008ef825da54c40051d904bb4a9880028f613659531040716316a92a620028ee82dd954c40011db05bb2a9880022fe11765531000477c12ecaa620028ec825d954c400d17908bb0a9880023be09761531001476412ec2a6200093f8755054c400147d0caa0a9880028f21954153103e716312a82a620018f5869c454c400d968c8b88a9880021fe1574d8f100743e42ae9b1e20119e681dc963c40051dd0fb92c7880463ba077258f100043fc2aeda1e200e87c855db43c400717908bb687880023be0976d0f1001476412eda1e20028ee82dd943c40011db05bb287880021fe157650f100743e42aeca1e20008ef825d943c40051d904bb2878800e2fa1f6450f1001d4f41ec8a1e2000ae681ccb62c40cd9cce3326c5880029be1564d8b100053642ac9b162064ce67119362c400155d0931ec588002ab61263d8b104de7338cc7b162083ce67118f62c4001bc4e2b86c5880029ba1774d8b1000536c2ee9b162000ace83dd362c400159b07ba6c588002b9a0774d8b1000574c06e9b162000ae6811d362c40015d3003a6c5880038bd5254d8b1000716aa0a9b162000aae84dcf62c400155b09b9ec588002b9a0773d8b1000574c06e7b162000aae849cf62c400155b0939ec588002b9a0473d8b1000574c00e7b162000a6e8590f62c40014db0b21ec5880473961e71d8b10006733a4e3b162000ce4749c762c40019cce738ec588003391ce71d8b104e672b84e3b1620008ed87cc762c400155d0998ec588002ab61331d8b104de7338e63b162083ce6710c762c402b5d50018ec588002ba60031d8b100067538ae1b162000ee2715c362c41355cd03b92c58822eb9a076418b1000476c3cc831620008ef8759062c40014df0ab20c5880029b2156418b104157340ec631620008ed8798c62c400155d09318c588002ab6126318b1000477c3ac6316200e87e859d94
  | 6 => 0x556c266230a4000ae587cc461480019cb0f988c290002b9a133118520007534266230a4000aa684cc46148001d4b09988c29021ab9e03311852043572c066230a409bec730cc46148137d8a61988c290046baa00311852000574c006230a4000ae5870c461480015cd08188c290003b1a0c3118520007633986230a4000ec5730c46148107dc500188c29020ab9600311852000770c006230a4083ec6300c46148107d8860188c2901032b10676d052001477c04eda0a40028ed809db414808195e813b682900032b50276d0520004f5c02eda0a4000ce7815db414809f1df00bb682900033ae0176d052000673bb0c3a0a4000ce57618741480015cb0e30e82900033961c61d0520006733a8c3a0a4000ce47518741480019cce630e8290003391cc61d052044673b80c3a0a4088ce5701874148111d4e8030e8290223a950061d052020cb742eed20a400096d85dda414801339d07bb482900027360f7690520004f4c06ed20a40009eb805da4148001a5aebaa48290002e9607549052000697ba8a920a40099af8750e4148013b1ce6a1c8290002aba1b41905200075230e8320a40009e980dd941480019d301bb282900023ba1a765052020cb742ceca0a400096d859d941480012df0abb282901065b2157650520004e7c1aeca0a40099cc835d941480013cf02bb282900027ae01765052000673a08eca0a4000ce4411d941480051df003b2829000a3b600765052000657a00eca0a4000cad401d941480018deedbaa82900031b1db755052000637b06eaa0a4000d6b60dd541480011df0cbaa82900023b2197550520004b7438eaa0a4000c6f761d541480018d8ec3aa82901431bd807550520006b5b00eaa0a4000d2f401d54148001a5a803aa82900031bdd46150520006363a8c2a0a4000cac769054148001a58eb20a82900067a2027610520004b7c2aec20a404196c855d8414808135908bb0829000273e0d761052004ce641aec20a40009eb805d8414808135908ba882901034b151751052008e75380c220a40009e58718441480019caec3088290003a9d90611052000752320c220a4000ce58718441480019ccea3088290003391d4611052000753420c220a4000ea5841844148001d4ce83088290003a9d506110520007522a0c220a4000ce67318441480019c8e63088290003a9d0c611052000752a18c220a408bee27018441481179cae03088290003b85c0611052045f53200c220a408bea440184414800135f0ea088290002ab21941105200059642a8220a4000ea46150441480053d50cb80829000a7a21970105200ded5c22e020a401bda8845c04148001b56c8b8082901036a1917010520006d5aa2e020a4040da8545c04148081b5686b8082900036a50d7010520006f1b0ae020a4000ce8615c04148001bc0c2b80829
  | 7 => 0x6c855d9434800135f08bb2869000273e0d7650d20004f3c0aeca1a40009e4815d943480013d700bb286900023be197550d2000476432eaa1a40009ae8799143480017530132286900266b21d6450d20006563b2c8a1a4000b2c85591434801371906b228690002e92056450d20005d5c02c8a1a40099ae87d514348001a5eebaa28690026e3a0f5450d2000696ba8a8a1a40008ee86dc543480011db0db8a86900067aa007150d20004f4c00e2a1a4000ba684cc761480017c30018ec2901023be1d649852000537c2ac930a4000a6c85592614800159f06b24c290002b320d649852004c77c3ac730a4000aaf8458e614800155908b1cc290002aba10639852000556c20c730a4000de3615c26148001a5eebba2c2900036ad83745852000697ba8e8b0a4000d2c751d1614809f95ec03a2c2900036ad80745852004ce743ee6b0a4000d8f74dcd6148001b18e9b9ac29000372d837358520006c7ba0e6b0a4000d8c741cd6148001b48e9b0ac290003711cf615852000657ba4c2b0a4000cac74985614800199ee730ac290003331ce6158520006d5ba6e0b0a4000da874dc16148001b96e7b82c290003721cf705852000cf4436e0b0a4000de361dc161480012df0aba0c2901065b215741852020476c3ec830a4000ae581d9061480014df0ab20c2900029b215641852000567c1ac830a4000acc8359061480015cf02b20c290002b9604641852004c76c3ec630a4000ae581d8c614800155f08b18c290002ab211631852000573c0ac630a4000aae8418c614800155b08318c290002b960463185204ed72c34c230a4000be18098461480011df0eb08c290002abe11611852000556422c230a4000acf83584614800159906b08c29000279e1d61185204e573c32c230a4000ba484584614800178906b08c290002f8e01611852000573c3ac230a4000ce7875846148001d4f08b08c290002b9211611852000752422c230a4000aa4845846148001d8f06b08c290002b920d61185200076241ac230a4000ac483584614813b5cf00b08c290003b8e01611852000573c366230a4000ae586cc4614800174d09988c290002b9618311852000763b186230a4000ec4630c461480017c300188c290002b9a07741852000537c2ae830a4000a6c855d061480014dd0a3a0c2900029b614741852000567418e830a4000acd831d061480015cd023a0c29010aba600741852000717aa4a830a4000ae68195061480015cb032a0c290002b9e0554185200057240aa830a4000e2d5415061480015cd03b98c290002aba10731852000556c20e630a4000ae6811cc61480855d300398c290002b9a07431852000572c0e8630a4000a6e8590c61480014db0b218c290002b9a06431852000572c0c8630a4000ae78150c61480015c902a18c290002aba1331185200
  | 8 => 0xc8b84c8901036ad0d709912000637b06eab224000d6b60dd564480a18dec03aac8900035ad807559120006963aec8b2240099ce87dcd6448001a9eebb9ac890003531d7735912000667b06e6b224000dcb60dcd6448001a9eea39ac890003531d47359120006c7ba0e6b224000d6775dc56448001ac8ebb8ac89000371dcf7159120006e239ee2b224000ce760dc56448001bc6c1b8ac89000359dd47159120006b23a8e2b224000dc7731c56448001b88e638ac89000339e187159120006d3b20e2b224000ce6641c564480019c8c838ac89000339d807159120006f1b00e2b224000d6b75dc16448001ad0ebb82c89000372dcf7059120006e439ee0b224000de371dc16448001bc0e3b82c8900036ad937059120206962a2ea32240009af8759064480016590ab20c890002e320d6419120005d240ac83224000bab80590644800165d0b218c8900025be15711912020cb642ae232240009eb805da54480018daedb2ca890002cb613659512020e96c3ea92a2404fe2f60d525448101e56c1aa4a8900023be19719512000476432e32a240009e980dd9544800135f08bb2a89000273e0d765512004ce641aecaa240009e7815d954480013c902bb2a8900027ae01765512000477436e2aa240008ed86dc554480033d50038aa8900027a6007155120204d6422ec2a24040cac645d8544800139f06bb0a8900267320d7615120004f3c0aec2a240009e4815d854480013d700bb0a890102cbe1d541512000697c3aa82a2400092f87550544800165d0caa0a890002cb219541512000597c1aa82a24000b2c81550544813f65f00aa0a89027ecb601541512027f17b02a82a2407cf2b6055054480011df0cb88a8900023b2197115120206d220ae22a2400096f855d363480832d90aba6c6900067aa0271d8d20024f4c04e3b1a40009af845c7634808135908b8ec6901026ba1f7458d2000697baee8b1a4000caf60dd16348001b56c1ba2c6900034bdd47458d20006963a8e8b1a4000d8c631d1634809f95ec03a2c6900036ad807458d20006c63a6c6b1a4000da774dc56348001b48e9b8ac6900033961b7158d2000673b06e2b1a4000de360dc56348001b4ee838ac690003691d07158d2000673c30e2b1a4000dc7631c563480019ccc638ac6900033918c7158d20006e2318e2b1a4000ce7601c56348001bc6c038ac6900036add37058d20006d43a6e0b1a4000de371dc16348001bc0e3b82c69000372d8f7058d204f6e431ee0b1a40099ae849db43480013d700bb686900266b21175d0d20206962a2eba1a40009af8759343480016590ab268690026e320d64d0d20005d240ac9a1a4000bab8059343480011df0cb8e86900023b21971d0d20004b7c2ae3a1a404196c855c7434801335908b8e86900027a6037650d20004b7c2aeca1a40419
  | 9 => 0x7458d200065610ee8b1a4000c3f751d16348001878ea3a2c690003271d37358d200065bba6e2b1a4000cb474dc563480019cd05b8ac6900033960b7158d200065bba0e2b1a4000cb4741c563480019aee638ac69000339dc87158d2000673c10e2b1a4000ce4821c563480019ce6438ac690003390c87158d2001c5f424eda1a40018ed829db434800117f0eb26869015e8f21564d0d2001d4e41ac9a1a4000ab48159343480031d90cb9686900021fe157650d200743e42aeca1a40008bf845d943480011bf06bb286900023de057650d200047a40aeca1a40038bc8759143480ad4790ab22869000ea720d6450d200055a40ac8a1a40018ee86dc943480231d90cb8e84900c65ba1f75509203be363b6eaa124000d6870dd5424806f8dec1baa84900df5ad83755092000c76432eaa12403796e871d542480ed8d8ec3aa84900c74bdd0755092018e37b00eaa124031d6b601d54248001a58ebb2284900034b1d46450920006963ae86a1240029ac8750d42480015590ca1a84900034b1d5435092008c77436e2a124000d6b75dc14248001ad0ebb8284900063b219744c920004b7c2ae8992404196c855d132480231dd0db8a6490002ada1331d85200047bc3ac230a4000ab48458461480015a906b08c290272b9e0961185200043fc2ae830a400e87c855d061480231d90ea10c2900029be1542185200053642a8430a4000ae78150861480015c902a10c2900463b21d321852000573c0a6430a4000ae4814c8614800156d09988c290002b960b311852000572c106230a40018ed829db41480051d9053b682900063b21972d052000672b90c3a0a40018ec865ca414801d0fd0b3b282900021f616765052001476410eca0a40018ee86dc941480031db053b082900021fe1576105200743e42aec20a40008df835d841480071b906bb082900063b219721052000672b90c220a40028f8865c041480031d90cb94629000a3b208764c52000c77436e498a40018ee86dd221480832dd0bba442900025b617748852004ce741ee910a40009cd83dd221480011df0eb2442900029be1564885202a53642ac910a4000acf83592214802d59906b244290002b9205648852000c77436e710a40409ae84dce214800135b09b9c42900023be1d638852000557c22c710a403aaac8458e21480015c902b1c42900123b61f618852021573436c310a4000ce67418621480019c8e830c4290003399cc618852000672398c310a409cee2701862148001dc0c2b8442900063b2197448520004b7c2ae890a404196c855d121480031d90cb9a42900067a201734852003c77438c290a4007ae68718521480019cd0e30a4290003399d06148520006723a0c290a4000ce67318521480019c8e630a4290002cba1643d9120024f4c04e3b224000dab645c26448081b50
  | 10 => 0xa1e40028ec865c743c80012df0ab8e87901425b21571d0f20054d6422e3a1e40008ef865d543c80051d90cbaa879002a6ba1f5450f2000697baea8a1e400ab8e83d5143c8001a5aea2a2879000a3ba1b7150f2000476c36e2a1e4000a6e85dd261c80014db0bba4c390002b3a0f749872000566c1ee930e401cae681dd261c80455cd023a4c3900038bd52549872000716aa0a930e4000aae84dce61c800155b09b9cc39018eb9a07739872000557424e730e4000aad849ce61c80355cd0239cc3900029ba16439872000536c2c8730e40188ed87cc661c800155d0998cc390002ab613319872027e5620aeda0e404fcaf405db41c800195a80bb6839007e3b61e61d072000696baea920e4000ba581d5241c8001a5eea2a4839002a6be1d4390720056c739a8720e4000aad86d0641c800195e81bb283900032b503765072000637bb6eaa0e4000c6c76dd541c80011df0cbaa839000a3b219755072000637bb0eaa0e4000c6c761d541c8001a5e803aa83900034b500755072012c7743cc2a0e4000c6f7598541c80018d8eb30a83900032bdda4150720006963ac82a0e404fd2c545d441c800135f0ea088390002abe1941107200059642a8220e400096f855d231c80a12d90aba4639000a3b207764c7200066618eec98e4000ccf30dd931c800199a61bb2639000339c43764c72000672886ec98e40008ef865d131c80051d90cba263900025be15744c720284b642ae898e40009eb805d131c80033d100ba263901863ba1e614c72000ce743c6298e4000ccf768c531c800147d0b21ec8900031b08775591200061e3aee8b2240038de87dcd64480018beebb9ac890003171d773591200066610ee6b224000c5f751cd64480018b8ea39ac89000327dd073591200063bbaee2b224000c7475dc564480019aee7b8ac890003351cf715912000673416e2b224000ce582dc564480018eeea38ac8900031d1d471591200065bba0e2b224000cd7731c564480019a8e638ac89000339dc8715912000673c10e2b224000ce4821c564480019ce8438ac8900033910871591200045fc3ac83224000a3c85590644800153906b20c890002ad205641912000c76c14ed2a24000a3d84d9654480031d90cb94a8900031bd9572951200045fc22ecaa240008df835d954480071b906bb2a8900023de0576551200047a40aecaa240018ee86dc954480031db053b0a89001a2f21176151200046fc1aec2a240038dc835d854480011ef02bb0a8900023d20576151200049fc3aa82a24000a3e8655054480014790caa0a8900c6cba09541512018d96412a82a240018ec865c8544800d958c8b90a8900021fe1574d8d200743e42ae9b1a40008bf845c7634800d17908b8ec69000a3b20971d8d200064e318e8b1a4000cd4631c5634800d17d0fba2c6900030fdd7
  | 11 => 0x50001b5686b8042a00036a50d7008540006f1b0ae010a8000ce8615c02150001bc0c2b8042a0003381857008540006d5a0ae010a8000da9415c021500018de40baec8980031b48175d913051e1f3ac85b2260a2c3e7510b644c0011df04b8ec89800a3b20971d91300361e322eb3226000a3e85d92644c00187aebb24c8980028fa17745913001477416e2b2260008ed82dc5644c00117f0eb20c89801a2f21176951300051fc22cb2a2600ea3e85d92544c00117b093b2a8980023be09765513001476412ecaa260008f7815d9544c0011e902bb2a89803a2fa1f64551300751f42ec8aa260068be849d8544c00117f0eb20a8980024fe1d54151300051fc32a82a26000a3d86550544c00187cecaa0a89801b0f1d9541513000c6e432e62a26000ce4621c5624c01d0fd0b3b284980021f616765093001477c3ae5b0a600a8ef805cb614c0019cae410ec2980023de1d611853050d6bc1ac230a6000ae482584614c0010ff0abb4829803a1f21576905300743f428ed20a600087d851da414c0dd47d0bb2482980063721973905300743f42ceca0a600087d859d9414c0051dd053b282980023b60a765053036d1f42ec820a60018dc865cc414c00d938c8b988298003331db724c530006e4386e498a6000ccc761c9314c001b90e0392629802237a1c614c53000ced43ee098a60018dc865ce214c0033b100b9c42980eaaba13768853000556c26ed10a6000ce6719da214c0015cd023b442981529ba17648853000536c2ec910a6015acc865ce214c02b79100b9c429804a73e1d31885300ad664326310a6015bc8804c6214c0a74dd0bb2042980029b617640853000573c0ac810a6000ae481590214c0015cb0fb0842980033961f61085304de73b86c210a609bce570d84214c0015cf0e3084298283b1a0c610853041f62c18c210a60a0ec673184214c001d8ae6308429820fb89c0610853041e72b80c210a6000ee170184214c107d8c60308429820fb10c061085300b4e7c3a6210a6011acc864c4214c001d88c29884298046f2201310853001675c32e010a6002ce8865c0214c0019d6c8b8042980033a5917008530006e5c1ae010a6000dc8835c0214c0239d6c6b80429804772d8d7008530006f1b0ae010a6000ce8615c0214c001bc0c2b80429800372cc57008530006e498ae010a6050d2d87d5254c8081c5ac1aa4a9900023be19719532001476432e32a640028ee86dc554c80011db0db8aa99013ecbe1d541532000697c3aa82a6400092f8755054c806365d0caa0a9900c6cb219541532027e97bb2a82a6407cd2d7655054c800165f06aa0a990002cb20554153204fd97c02a82a6409fb2d8055054c8081c5ac0aa0a9900023be19711532001476432e22a6404fda4415c454c801535908bae879013f4b15175d0f2000477c32e3
  | 12 => 0x1facee0165151405351fc3aca2a28000c3f87594545000107f0eb28a8a00028fe0d651514018d1f412ca2a28031a3c82594545000147902b28a8a01fa8fe0165151400071dc02ca2a280038bc845d7635000187aea2a6c6a00021fe1571d8d400743e42ae3b1a80038bc845c763500011df04b8ec6a000a3b20971d8d4000c5ec24eda9a800387c855db53500ab878a8bb6a6a000e1fa1f6554d4000c5f436e8a9a8000c3f65dd1535001d1bd0fb1aa6a0003871536354d402ac9e42ae3a1a8003a9e86d8d435003717d0db8a86a00033918871589400345e420eca9280018be86dd152500051df0eb96c2a0003395c821d85400047bc3ac230a80a5ab78458461500015c904b08c2a00022f61c54185400061eba8a830a8000ab581150615000117b0fa18c2a0002ad607431854000578c004230a80018bd849db51500011bf06bb4a2a000e3720d769454001c6f418ed28a80008dd831da51500031790cba4a2a00030fd95749454001477414eca8a80008ed829d9515000d179083b2a2a00062fa1b74545402ae1e2a2ec28a80018bc865d0515001d878caba0a2a0003391cb615054000672390c2a0a805593e87dd54150001878edbaa82a00034e1c375505400061e3b0eaa0a805cc3f601d541500b9a76c03aa82a00032b1db7250540006963aee4a0a8000cac761c94150001a58ea39282a00030f1d461505400069c3aee0a0a800087f855da315001d0f90abb462a003a1fa14768c5400043ec28ed18a80018bc865d231500ab2790aba462a000a3ba0a764c54000476c14ec98a80018bc865d131500ab2790aba262a00066e201744c54000c5e432e910a8054a6e85dda21500014db0bbb442a005ab3a0f768854000566c1eed10a8000ce6719da21500015cd023b442a0056ab21974885400ad57436a910a8000e2f65d522150001c5aca2a442a0056ab21943885400b74631a8710a80a4aae86d06215002b5590ca0c42a0002cb215418854000573c0aca10a8000ae481594215002355d0daa042a00038bd97540854000716b28a810a8011aac8650c2150025d18c6a1842a0002b961f610854000672c3ec210a8066ce770d8421500cd9cae1b0842a0002b9e1c610854032752c20c210a8000ea6741842150001d4ae830842a0003a9d506108540007522a0c210a8000ea7431842150001d4a8630842a0193b89c0610854032672b80c210a8000ee17018421500c9d4c8030842a0193a91006108540004d6c3e8210a808baae86d042150001d48c3a0842a00026be1d410854008d564328210a8000b2c855042150001d48c2a0842a000b3ae19700854001674432e010a8000ceb655c021500019d2cab8042a00036ae117008540006d4422e010a8011ceb645c02150023b56c8b8042a00036ad517008540006d42a2e010a8000ceb635c021
  | 13 => 0xf5520482b0042008ef8750560084231d90ea0ac0108029be1541580210053642a82b004200aeb8050560084235d100a0ac010846baa00415802100574c0082b004264eaa4010560084c9dc02020ac0108463ba1f315802100476c3e62b004200aae84cc5600840155b0998ac010846baa03315802100574c0662b004211ae8808c560084c5d946118ac0108023be1d315802108c7643a62b004200aeb804c560084235d10098ac010803b14c4315802108d7540062b004200ae9800c56008507d946018ac0109830f15373597400351f424a6b2e8000c5f7394d65d00c10fd0e29acba000a3ba0b715974000476c16e2b2e805cc3c541c565d000717b09baac7a003a1fa177158f400043ec2ee2b1e80038bd84dc563d00051dd05b8ac7a00023b60b7158f4001c3e42aeda9e80018bc845db53d00c1878a8bb6a7a000297e1563d4f403070e2a2c7a9e800387d85dd953d000317908bb2a7a017f0f1517654f4000477c12eca9e80028ec825d953d00b517f08bb2a5a00062f2117654b400143e43acaa968006c3c7459552d00051b90eb1a65a00022f61f54987400061ebaea930e8000ab581d5261d000117f0ea1cc3a000f279cd43987400147743ee4b0e80018bc845db51d000317d09bb4a3a01770f153769474044d1e422cb28e8006c3e7459651d00dd17f08bb2a3a00062f211765474000477c12eca8e80028ec825d951d00b9878a8bb0a3a022a8f21165147400061fbb6eaa0e8000c3f761d541d000195eedb9283a00034b1d7725074000657bb0e4a0e8000d2c751c941d000317d0f30a83a00030f1d6615074000c5f426ed18e805b93c855d231d000d93ce8b1c63a00062fa13764c74000477c12ec98e80028ec825d931d000117f0cba263a016e4f215744c74000cdc402e898e800e87e85dda21d00010fb0bbb443a00062fa13768874001c6f41eed10e80008dd83dda21d00a94dd0bbb443a00029b61776887400ad57426ed10e8016ace83dda21d000159b07bb443a0002b9a0776887400ad56422cb10e803ae2c5459621d002b55d0930c43a00e63be1d61887401ccd7c3a8310e80a8aaf8650621d00016590aa0c43a00ea3be09764874008d56422ca10e8039e2c5459421d002355d0930843a00e7a9d0661087401d477c3ac210e803a9af8750421d010f55f0ca0843a0002cb21541087400051ec24a5b2a8000c6d7294b65500011df04b8ecaa000a3b20971d95400062fb2ae732a800ec5c655ce65500aba38a8b9ccaa01ff0fdd7745954001477416e2b2a80008ed82dc565500010ff0eb28caa029b0f1d165195405343ec3ecbaa28006a3c84d97545014da70a8b86a8a01568f61f65d51400061ec3ecbaa280a7e2f20d97545014fc5a41b2ea8a006e2f21971d51400351f426caaa28055c3f74d95545000127f0eb28a8a0
  | 14 => 0xf825d943484011f700bb286908063e2017650d2101c5f43ec8a1a4200caf645cb414840d958c8b9682909730f19075505210061e3aec8a0a4200caf64dc94148475958c9b92829085b3318f724c52103477c3ac910a4200a6f8559221484a94d90ab24429080e3be1d638852101476432e110a4215ce8605c221484010ff0aba6c09083a1f21574d812100c76412e9b0242018ec825cf60484015d30110ec09094f4b61f54950211d71730ea92a04280f2661d5254084751df0cb8ca8108023b61b71550211cd97c3aa82a04200d2f87550540840125f0eaa0a8108c6cba19541502118d96432a82a04239d2f7655054084f9a5aecaa0a810802cbe0d54150210059640aa82a0427cf2661550540840165f00aa0a8108ea3be1971150211ced220ae22a042009e7815c054084013c902b80a81084a6b21175d0c211ce962a2eba18423a8ef865c743084012df0ab8e861094e5b21571d0c21094d6422e3a1842008ef865d543084051d90cbaa861084a6ba1f5450c2100697baea8a184212b8e83d514308401a5aea2a286108023b61b7150c212a53742ee93084200a6d85dd2610842d59d07ba4c210802b360f74984210e57340ee9308423ae2c54552610847395882bb682108023be0176d042100696baea92084200ba581d524108401a5eea2a4821084a6be1d4390421096c739a872084200aad86d0641084011db01bb282108031bddb7550421006b330eeaa0842008ef865d541084012dd0e3aa82108031bdd87550421006b3308eaa0842258ee8798541084018deeb30a82109531b1d6615042100657bb482a084200d2c75905410847335908ba882108e74b1517510421004d7c3a82208423aaaf8650441084016590aa0882108025be15748c42129cb642ae918842129e58710631084011df0cba262108025be15744c42129cb642ae898842009eb805d131084233d100ba2621084a79a1f414c421095e341e829884216ccf768c5310842578d0318a6210832ba602745802100537c2ae8b004200a6c855d1600840159f06ba2c010802b320d74580210057240ae8b00420faeb805d16008401c5ea92a2c010846baa02545802100574c04a8b004211aea805516008401c5aa82a2c010846baa00545802100574c00a8b00420bae9809cd600840155f08b9ac010802ab21173580210057240ae6b00424eaeb805cd600840155d0839ac010802ab610735802100573408e6b004211ae5811cd60084235d501a1ac010802ba60343580210053742c86b004200a6d8590d60084015cd0321ac010802b9606435802108d7540486b004200ae98090d60084235d500a1ac010846baa00435802100574c0086b004204ae9809c560084231dd0fa0ac0108023b61f415802108d7540682b004200ae980d0560084cddc021a0ac010846ba202415802132
  | 15 => 0x8bb6871085a6b21175d0e211d6962a2eba1c42009ad87d93438840165d0bb26871085ae3a0f64d0e21005d340ec9a1c42398ef865c743884012df0ab8e87109525b21571d0e210b4d6422e3a1c425496e859d943884012db0b3b287108026b6127650e21004f340ceca1c42009e6811d943884011df0cbaa87108023b2197550e210b4d743ec8a1c4200caf76d91438840165d0bb22871085ae3a0f6450e21005d340ec8a1c42009ae87191438840174d02322871085a6ba1f5450e2100697baea8a1c4216b8e83d514388401a5aea2a287108034b5d75490621005d2c0ea920c4200d2f75152418842d35f0ea1c831085b639cd439062100637bb6eaa0c4200c6f761d54188401a58eb20a83108eb4b1517510621004d7c3a8220c4200b2c8550441884012df0aba463109525b215748c621004b7c2ae898c425496c855d131884013d700ba263108567a201744c62109667bb46298c42158ed87d9360884014dd0bb26c1108029b61764d82210056741ec9b044200acd83d93608842b5d500326c1108563b61f63d822100557426c7b044200aad84d8f608840155d0931ec110802ab61263d82210ad75400c7b04425496e85dd160884012db0bba2c1108029ba17645822100536c2ec8b044200ace83d91608840159b07b22c1108563ba1e64582210ac7643ac8b044200aae84d8d608840155b09b1ac1108563ba1e635822100557424c6b044200aad8498d608842b1d90eb1ac110802b9a0463582210053742ee8b044200a6d85dd160884014dd0b3a2c1108029b61674582210056741ce8b044200acd839d160884015d3013a2c110802bae01745822100717aa4a8b044200e2d54151608840155d0939ac110802ab612735822100574c04e6b044200aeb805cd60884015cd0239ac110856b960473582210053742c86b044200a6d8590d608842b1dd0fa0ac110856baa03415822100574c0682b0442158ec8750560884014df0aa0ac1108029b215415822100575c0282b044215ae880505608842b1dd0f98ac1108023b61f31582210055742662b044200aad84cc5608842b5d50198ac110802ba603315822100477c3a62b0442158ec874c560884015d70098ac110856ba20131582210051f42c81b224200aad82903644840155b04206c8908031b087755912100637906eab224200c3c75dd164484018deebb92c8908031b1d772591210045fc3ac83224200a3c8559064484751df04bb4a8908028f613659512100476c16ecaa242008bf845d954484011df04bb2a89081a2f21176151211d477c12ec2a2420093f87550544840147d0caa0a8908028f21954151210043fc2ae9b1a420e87c855d363484010ff0abb6869083a1f21576d0d2101c5e422eda1a423a8ef825db43484011db05bb286908021fe157650d210743e42aeca1a42008e
  | 16 => 0x2952210045ec24ecaa442038de839d954884011bb073b2a91081a2fa12761522101c6f41cec2a442008dd839d8548840127f0eaa0a9108028fe1954152210051ec32a82a44231b2e82550548846365904aa0a91081a3be19721522103657322e42a44200c9e639d3638840187ceb3a6c71081a2fe1d74d8e210061f3aae9b1c4200c3d755d3638840195e40ba6c71083a1fa177458e210043ec2ee8b1c4200a9e84dcd63885555ad03b9ac71080e2f21176d0e210045ec3ec9a1c4257a3e85d93438840753d07b26871081a3be1972d0e210743f42ceca1c420087d859d9438840117b093b287108023760e7650e2101c5f43ec8a1c4256a3e85d91438840753d07b2287108963be1971d0a2118cb743eeaa144277c6f76dd5428846f8dcc3baa85108df599877550a211bcb7438eaa144276c6f761d54288463a5ee83aa85108c71b9847550a2118eb3308eaa144200d2c759914288401a58eab2285108034b1d74350a21014d643a86a144200aaf8650d4288401a58eaa1a851087e3b61b7150a21006b3baee2a144200d67751c54288401ac8ea38a85108025be15744ca212a4b642ae899442188ed86dc532884c73cd0fb8a651088a7920572906210d4f240ae518c420e87e85dd160884010fb0bba2c110802abe11725822100556422e4b044200acf835c9608840159906b92c1108029be1542582210053642a84b044253c6e619d76488401accc33aec9108031b98575d9221006b330aebb244200d4e759cf6488401a9aeb39ec910803539d573d9221006a6baae7b244200cce615cf6488401b8cc2b9ec910803599d671d9221006b2bace3b244200dc6739c76488401b8ae738ec9108eb4b15175992210059742ec93244200b8e83d92648840174d03b24c910802cba1643992210059742ec8b244200b8e83d91648840174d03b22c910802cba164359221004d7c3ac8324423ada6649c46488401b4ac9388c9108eb69d0e7119221004f340ced2a44200c6e76596548840165f08b2ca9109534b61f54952211cf1730ea92a442398ef865c6548842d39d073b2a9108027360e7655221004f340cecaa442009e6811d9548847595cc93b0a91085a73a0e7615221004e6c1cec2a442009e6819d8548847565f0eaa0a9108034be1d541522100497c3aa82a44200b2f86550548840165b0caa0a910802cbe0d54152210059640aa82a44239e2e61550548840165f00aa0a9108e63be1971152211d6d220ae22a44200d2e759d36388401b1cc73a6c7108e72b98674d8e21006d330ce9b1c423a9af875d36388401a5ceaba6c7108034b5d574d8e210065730ae9b1c4200da6615d36388401b4ce938ec710803695d271d8e2154ee331ce3b1c425496e85dd163884012db0bba2c710802e3a136358e21005e340ec6b1c42009e6819db438842d3590
  | 17 => 0x226200c7875dc1644c4019d6e5b82c8988033a1cb705913100675c16e0b226200ce882dc1644c4018f6ea382c8988031e1d470591310065dba0e0b226200cdb731c1644c4019d6e4382c8988033a1c870591310045fc3ac83226200a3c85590644c40157100b20c8988023be09769513101476412ed2a26200a3d84d96544c501c58c5aa4a89881a3721973951310062fb2ae72a262009d4815ce544c4051dd05bb2a8988023b60b76551310045fc22ecaa262008ef825d9544c4051d904bb2a8988023ee01765513100c7c402ecaa262068bc845d8544c4011df04bb0a89880a3b20976151310047dc02ec2a262018f8805d8544c40127f0eaa0a8988028fa1954151310051e432a82a2627ce2c62550544c4014df0ab26c4988029b21564d893100575c02c9b126200ae880593624c4311db0e306c498802aba1060d893100556c20c1b126200ce970183624c4014dd0bba6c4988029b61774d893100566c1ee9b126216ae581dd3624c401c5ea92a6c4988038b55054d893100557420e1b126200aad841c3624c42d59d06386c498802b360c70d893100573408e1b126216ae5811c3624c4011dd0f206c4988023b61e40d89310053742c81b126200a6d85903624c4011dd0e206c4988023b61c40d89310b47743c21b1262008ed87843624c4011dd0e086c4988623b61c10d89310055742021b126200aad84043624c42d59d06086c4988023b61e641893100477c3ac83126200a6f85590624c4014d90ab20c498802bae01641893100574402c83126200aae84180624c40155b08300c4988033a5c060189310743f42ceca12620087d859d9424c46f8d8c5baa84988c71b188755093100637baec4a126200c6c75d89424c42d998e7b12849880e3da1b715093100673b10e2a1262128ec865cb414c42d1df0fb1682988023b61f62d05313751e42ac920a6221ab880592414c4018d8c5baa82989730f190755053100636310eaa0a6200c3c75d91414c4251dd0db9282988e63ba1f62505310b47643ec4a0a6200c6f75d89414c4018d8ebb1282988022fe1d641053136d1e42ac820a621bab880590414c4071b90cb84629886736181708c5310043fc2ae9b02620e87c855d3604c4011df04ba6c09880a3b20974d813100574c06e5b026200ae9801cb604c401970c03a2c0988623b21b72581310047743ec4b026200caf74d89604c401958e9b12c0988023ba1c625813100657ba0c4b026200cac74189604c5579cee2312c0988031bc8175d92210062f3ace7b244200c5d759cf64884071bf0eb9ec910803179d573d92210062ebaae7b244200ccf205cf64884019aae738ec9108028fa1764992210054f41ec93244200a3e85dd1648840153d07ba2c9108028fa1643592210045fc3ac83244200a3f84596548840d1df0cb94a9108031b5957
  | 18 => 0x41d0fd0bbb264a08021f617764c9412e61e3a0ca9928200c3c65dd132504071dd0fb1264a08032bdd3624c9411d6563a6c49928200c6e72d97515041d878caba6a2a08e63b21972d454100637b2ae5a8a820ec6c655cb51504011db0fb16a2a0976cda13519454101476412eca8a8200c3f65dd151504dd878cbba2a2a08032b18b745454129c7743ec4a8a8200caf74d895150475958e9b12a2a09778dd8765905410071632ec520a8200e2c6518a415040d1790cb8482a08030f195709054110e5c302e120a82018bc845d760504011df04baec0a080a3b20975d814100477c12e7b0282028ec825cf60504015d301b96c0a0802ba60072d81410043f43ecab028200c5c73d9560504018d8e5b2ac0a08021fa1c65581410062e398cab028200c6c7219560504018becbb9ac0a08031719773581410fc76436e4b028200c6f65dc960504018d8cbb92c0a08023ba1f625814100637baec4b028200c6c75d89605040199ee7b12c0a0803331cf625814100477438c4b028200c6f7518960504018d8ea312c0a080333dcc625814100666398c4b028260c3c54dcd651040d47d0929aca2080317dce53594413043f438a6b28827ec3c54dc165104dd96cc2b8ea82080e1f21576d4c410345e422eda988260c3c545db53104014bf0ab1ea6209838715163d4c4101c3ec2eeca98825fc3c545d953104011df04bb2a62080a3b2097654c410143e43acaa908206c3c7459552104051b90eb1a64209bb0fd5175984412ee1e2a6ed2888206c3e7459651104b9878a8bb0a2209724fa1f75504410061fbb6eaa088200c3f761d541104b9a6b023aa82209734d984755044100657bb6e4a088200d2c75dc9411040195eec39282208034b1d472504413761e3acc2a088200cb77694541104dba68eb28a822081a6d21d51504410065bbb2a2a0882018bd84dd5601043717d0faa2c0208030fdd754580410dc5e43a86b008203c9c7350d60104371790ea0ac0208028f21541580410dd5c40282b008200cd5739c7648c401878ebba2c918a8f0f1d642592315161e3a884b246206c3e645d4648c40117f0eb20c9188028f21564192310061ebaac832462068be849da548c40147b09b2ca91883a8f215649523101477414ecaa462008ed829d9548c40117f08bb2a91883a2f21d64552310751e42ac8aa462068bc845d8548c40117b0fb20a9188024fe1d54152310051f432a82a46200a3c86550548c40d87eecaa0a9188030f5d954152310346fc32e62a4620087f855d9428c41d0f90abb2851880e3d6187150a313751e42ac920c626da3c85590418c40d93cc8b9883188028fa1640d91310061e3aee8b2262028ee87dc9644c4018deebb92c8988031b1d7725913100476c06e4b226200c6f751c9644c4018d8ea392c8988063ea1f70591310063dbaee0b
  | 19 => 0x29ba0a101954100536c142032a820e87e8704065504b947d08080caa080297a0c10195410052ec182032a8200a6e8204065504014db04080caa083b1d19671d51412ee9b2a4e3aa28200c77651c554504010fd0fb2ac6a08031b1cb6558d410063c386cab1a820087e8719563504018d8e432ac6a08031e1c06558d4100637b2ee4b1a8200c6c65dc963504018f6cbb82c6a08031e1977058d4101c3e42aeda9a826e8bf845db53504011df04bb6a6a080a3b20976d4d410761e32ae9a9a82028ee82dd953504011db05bb2a6a080e1fa1f6554d4101d2f41ecaa9a825de1c43d95435040155b09106c4a08029ba1663d894100536c2cc7b128200a6f8558f62504014d90ab1ec4a0802bae0163d894100574402c7b128200c6f655c362504018d8cab86c4a08029ba1660d894100536c2cc1b12821f8ed8718362504019d2e0306c4a0802ab61375d89410053742ee9b128200a6d85dd3625040159d07ba6c4a0802b360f74d89411d7172a6a9b12823ae2c54553625040155b09b9ec4a08029ba1673d894100536c2ce7b12821faae849cf625040155b0939ec4a08eaaba1253d894100556c24a7b128200e4f5394f62504014dd0b21ec4a08029b61643d894100476c3e63b128200a6e85cc762504014db0b98ec4a08eaaba1331d894100556c2663b12823aaae841c3625040155b08386c4a08023ba1e50d894100476c3ca1b12823aaae84943625040155b09286c4a08023ba1c50d894100476c38a1b1282008ed8790362504014dd0b206c4a08029b61640d89410047743c61b1282008ed878c362504011dd0e186c4a08023b61c30d89410053742861b128200a6d850c3625047555d08186c4a0802ab61030d89410057340861b128200ae5810c362504011db0f086c4a08023ba1c10d89410fc76c3821b128200a6e8504362504014db0a086c4a08eaaba1010d89410056741821b128200acd8304362504018d8c5baac4a08031b18875589410043f43ecab12820087e8719562504018dcedb28c4a08023b61e65189410053742cca31282008ef8759462504014dd0c328c4a08031b9d8651894100476c3cc63128200a6e8598c62504014db0b318c4a0802ab612631894100572c0cc631282008ef8758c62504014df0ab18c4a08029b215631894100575c02c63128200ae88058c62504018decab80c4a08031b19570189410053742cc03128200a6d8598062504019d2e0300c4a080a1f21576d49410143f43ecaa92825dc3c74d95525040187ecbba2a4a0a8f0f19774549412d656316e8a928200caf74d895250475958e9b12a4a08021fa1b75509411be36316eaa12820087e861d542504638d8c43aa84a08c61fa1f65509411bc3e43ecaa12823787e87195425041d0f90e32a84a08031bdd76250941006363aec4a128200ce7621c5425
  | 20 => 0x5fc32e3aa482009b7865c754904db96f0cb8ea92080369e0971d5241006d2412e3aa4826ec3c655d8549040d96cc2bb0a9208024f61f65152412e59b40eca2a4825da3d87d94549040187b0fb28a9208020f61f65152410051ec1eca2a48231a3e82d94549046347905b28a9208038da0765152410051ec06ca2a48200c3f7515163904070fd0b3b6a7209bb0f15276d4e4101c3e43acaa9c8200c3d65dd15390401c38a8b1aa7209ba4f21571d0e4101d4fc32c6a1c8200c3d655d251904bba68eb28e83208862fa1c54582410061fba8a8b048221aba80151609044317d0fa1ac1208862fa1f415824110d5d40682b048200a3d8494f65504018bae729ecaa08028f61250d954100537414a1b2a8200a6d8294365504014dd04286caa08029b60850d954100537414c7b2a8200a6d8298f65504014dd05306caa08029b60a60d954100537410c1b2a8200a6d8218365504018bee739ecaa09768fa1073d95410051ec20e7b2a8200c5d731cf65504010fb0f21ecaa08028f61372d95410043f43865b2a820087d870cb65504bb47d08196caa08028f61032d954100537c12e3b2a8200a6c825c765504010fb0f98ecaa09768fa1331d95410051ec2663b2a8200a6e82cc765504014db0598ecaa08029ba0a70d954100536c14e1b2a825da3e841c3655040147b08386caa08029ba0870d954100536c10e1b2a820087d8790365504014dd05206caa08029b60a40d95410053741461b2a8200a6d828c365504010fd0e186caa08021f61c30d95412ed1f42061b2a8200a3d840c365504014dd04186caa08029b60830d95410053b40861b2a8200a75810c365504014dd05086caa08029b60a10d95410043f43821b2a825da3e8404365504014bd06086caa08029760c10d95410053741021b2a8200a6d8204365504018dce5b2ccaa08031bd9572995410763632ae532a8200caf74dc965504011db01b92caa08032bdd0725954101477416e2b2a820087f8759465504014df04b28caa08029b209651954100537414c632a8200a6d8298c65504014dd05300caa08029b60a601954100537410c032a8200a6d8218065504010fb0f218caa083a1fa1c32195410043ec386432a825ca3e840c8655040147b08190caa08021f61f31195412e51f4266232a8200a3d84cc465504014dd05988caa08029b60b31195412e51f4264232a8200a3d84c8465504010fb0f200caa08029ba0a401954100536c148032a825ca3e848c0655040147b09180caa08029ba0a301954100536c146032a820e87e870c065504010fb0e180caa09728fa1030195410051ec206032a8200a6e820c065504014db04180caa08029da0430195410053ac086032a825ca3e84880655040147b09100caa09728fa1020195410051ec204032a825ca3e84840655040147b09080caa08
  | 21 => 0x855c061508011bf06b80c2a100e3720d701854200572c142030a8400ad58304061508b517f08baec0a103a1fa1671d81420043ec2ce3b0284038de839c760508011bb0738ec0a10021fa1f65581420062e39ecab02840087e87195605095987ee832ac0a1003171cc65581420062fb2ee6b028400c5c65dcd60508018eecbb8ac0a10031d19771581420063bb28e2b028400c74651c560508019c84338ec8990028fa1640d913200556c1481b226400aad82103644c8018d843baac8990031bc8375591320061e3aee8b226400c6c75dc9644c80117f0eb20c8990028f21564191320051ec26cb2a264008bf845d9544c8011df04bb2a89901a2f21176151320049fc3aa82a26400a3e86550544c8014790caa0a89900a3721973151320364e322e62a264038ec865c8544c80d958c8b90a899002b560c10d853200572c1021b0a64008f787584614c9535cf04b08c2990021fe1574185320743e42ae830a64008bf845c0614c80d17908b80c299002b960a10185320056ac182030a640087f855d3604c81d0f90aba6c09901a2fa1271d81320045ec24e3b0264018de839c7604c8031dd0538ec0990063b20971d81320351f424a0b2e827e87e8714165d04db17f0cba6a7a080e1f21d6554f410355742440b168206aac845d562d04015cd0339ac5a0802b96067358b4100537c2ae6b168200a6c855cd62d040d55908b9ac5a08029ba147358b4100536c28e6b168206aae841cd62d044b55b0839ac5a081aaba125358b4100556c24a6b168200e4f5394d62d04014df0ab8ac5a08029b2157158b410047743e62b168200a6e85cc562d04014db0b98ac5a081aaba133158b4100556c2662b168200a6e859c162d04014db0b382c5a081aaba127058b4100556c24e0b168200ae7815c162d04011dd0f282c5a08023b61e5058b4103557424a0b168200aad8494162d04011dd0e282c5a08023b61c5058b410047743c60b1682008ed878c162d04011dd0e182c5a08023b61c3058b410053742860b168200a6d850c162d040d55d08182c5a0802ab6103058b410057340860b168200ae5810c162d04011dd0f082c5a08963ba1c1058b4100476c3820b168200a6e8504162d04014db0a082c5a081aaba101058b4100556c2020b168200ace8304162d040159b06082c5a096b2b98b7454b4100657ba2c4a968206cac7458952d04010ff0abb265a083a1f215764cb4101c7643ac49968200caf7458932d040d958e8b1265a08023be1d62d474101477416eab0682008ed82dd560d04051dd05b9ac1a08023b60b735834120574c04e4b06824faeb805c960d040147b09292cb208031bdca52596410043fc3aca32c820ec5e655cc65904018bacab98cb209bb4715173196412ec3fc3acbaa4825dd34549c754904dd47f0eb2ea9208030fe1d65d524136c
  | 22 => 0x286caa10031e5c250d954200536c10a1b2a8400a768198f65508014eb0331ecaa11de8fa1073d95421bd1ec20e7b2a8400c5d731cf65508010fb0f21ecaa10de8f61371d95423bd36c16e3b2a8400a6f825c765508010fd0f98ecaa10021f61f31d95423bd1f42663b2a8400a3d84cc7655086f4dd0598ecaa10029b60b31d95421bd37414e1b2a8400a6d829c365508ef47d08386caa10de8f61070d95421bd37410e1b2a8477a6d821c365508018f2e0386caa10021f61e40d95421bd3741481b2a8400a6d82903655086f4dd05186caa10029b60a30d95420043f43861b2a840087d870c365508ef47d08186caa10028f61030d95421bd3741061b2a8400a6d820c365508014ed02186caa10029d60430d95421bd3741421b2a8400a6d8284365508010fd0e086caa10021f61c10d95423bd1f42021b2a8400a3d8404365508014bd06086caa10029760c10d95421bd3741021b2a8400a6d82043655090187eebba2caa10021fe1d651954251d1fc22ca32a8479a3d8498c65508014ed03318caa10029d60663195422c51ec24c032a840e87e8790c65508010fb0f218caa103a1fa1f31195420043ec3e6232a8476a3e84cc4655080147b09988caa10c69ba0b311954200536c166232a8476a3e840c4655080147b08188caa103a1fa1e40195420043ec3c8032a8431a6e8290065508014db05200caa11da8fa1330195420051ec266032a8431a6e828c065508014db05180caa103a1fa1c30195420043ec386032a8476a3e840c0655080147b08180caa10c69ba08301954200536c106032a8400a76810c065508014eb02180caa10c69ba0a101954200536c142032a840e87e8704065508010fb0e080caa11da8fa1010195420051ec202032a8400a5e8304065508014bb06080caa10c69ba08101954200536c102032a845acaf645cb545086f8d8e5b2aa8a116a2fe1175d8d420043fc2ae3b1a840e87c855c763508010fd0fb2ac6a10021fa1c6558d425861fba0cab1a840387c855db53508070fd0fb2aa6a12bf0f9d865d0d4218e1f390cba1a8431c3c72197435095dc584232e86a12bb8bc8065d0d4218e36390caa1a8400c6c65dc943508ad47d0db2a86a10df0f1db6550d420070e31ecaa1a8437d2c72d954350863878ec32a86a10c74b1c86550d423b61fb98caa1a8476e1f73195435086387ce432a86a10c70f1c86550d423cf16390caa1a8431c2c7219543508f3c584232a86a11e78bc806550d420070e32ec6a1a84029ae87dc94350801c58cbb9286a1002ad61010d85420056ac1821b0a8400ae58204361508018bce7b2cc2a12b70f5d065985420062f398cb30a8400c5f655ce61508018b8cab9cc2a1003355cf61985420043f43ecab0a840087e8719561508e987ee832ac2a10023de1d61185420043fc2ae030a840e87c
  | 23 => 0x550540061fbb2e6aa0a800b2f825cd54150f965904b9aa82a0c64fa1f72550540061fbb6e4aa0a83193f875c9541500147f0cb92a82a0030fdd972550540061fbb6e2aa0a87cb2e82dc5541500165b05b8aa82a0028f61a71550540061fbb4e2aa0a800a3f865c5541500187eecb8aa82a002cbe0971550543e596412e2aa0a800c3f761c554150b927f0c38aa82a1724f61871550540049ec18e2aa0a83193e821c554150632790438aa82a1734d98471550542e69ab08e2aa0a80093d801c5541500187eedb82a82a1fa4fe1b70550543f49ec36e0aa0a80093d83dc1541506327d05b82a82a0c64f20b70550540049f40ee0aa0a87ed3a60dc154150fda72c1b82a82a0028fe1970550540061fbb2e0aa0a8028ee82dc563150011db05b8ac62a00a3ba1f72584541d6563a6e4b08a83aea441dc961150011db01b92c22a0e72b1d072584541cf52208e4b08a8028ee82dc560150011db05b8ac02a00a3ba0b715974300476c16e2b2e865cc3c541c565d0cfd878a9b82cba181a8fa1250597433f43f438a0b2e865a8bf865cb54d0cb595cc4b96a9a18021fe1570987430743e42ae130e865dc3c74dd561d0cb9878e83aac3a180a3ba1f725874300637baee4b0e8600c6c75dc961d0c75958e9b92c3a18023b603725874300637ba8e4b0e8600c6c751c961d0c73958e8392c3a180a3ba0b715834300476c16e2b06860e87e851c560d0c010fb0a38ac1a18028f61252d954300636b94a5b2a86008ef825c76550c051d904b8ecaa18031d94571d954340e1fbaee8b2a86028ee87dc96550c011dd03b92caa18023b603725954300657ba0e4b2a86028ee82dc56550c011db05b8acaa18021fe1d65195432fe1e3a2ca32a8600a6c825946550cbf0fb0fb2ea8a197f4715173d51432b51ec3ecbaa28600c3d87d975450cad87ee9b2aa8a180317d9773551430049fc3aca2a28660b1f835945450cf365904b28a8a197e8fe1d65151430061fc3aca2a2860083f875945450cc147f06b28a8a180387e0d651514300717c12ca2a28631a3e825945450c6347904b28a8a18038b209651514318d16412ca2a28600a3c815945450c0147f00b28a8a18c62f219721514318e56312e42a2860399e839c45450c0733906b80a8a18031bd4975d894300636310eab128600cad749cb6150c051df0eb96c2a18032b5d172d854300477c02e5b0a86008f7875846150c011df04ba8c2a180a3b20975185430061eba8a830a86008ef825d76050c051d904baec0a18030f5d454d814300477c12e3b0286028ec825c76050c070f90abb6a7a100e1f6177654f4201e4f39a8730e8439ae681dca61d0807938e6a1ac1a1002b9205725834227d75c02e4b068400ce421dc560d08019c84238ac1a10028f61253d95420062eb9ca7b2a8400a3d8494365508014db05
  | 24 => 0x10004000001000000a00180100240000000010000005005800c000001002800800600300000040160020008004000010003800c0160030030004000002000800000c001000000000000c00080080020080000018006006000000800a00400000140000000000000014001003000400a0000000020000003001800400000400000080000020008000006001001000000200000280180020000048000004000000000000000000180000020010000004002002000800000000000300000000010000010006000005001800200a0000008002003000000001600100000000100000018008000006000800002a0010000008000000001000000a00000000180000020008000008006003000000600200080000040020010000004000001802400c006001802400200b0000000002000000000000400000080040160010018000000003001000002000a0008014000000000801400200000280080000130000010000002000802000000600280000000030008000000000001801c0000040008008002002000000400200000280180000060008028008000000000000000200000180020000060004000000001000000600400080000000080010000004001000006c004002000000000000400080000040000070004000000000002c00800000200180060000020000008003006001000600400000180000010000014010002000800000400300200a3ba0b7158e5400476c16e2b1ca800a5d858c163950011bf06b84c32a00e3720d70986540147743ee4b0ca8008ed80dc961950051dd05b8ac12a0023b60b715825401c6f418e2b04a8008dd831c560950011df04b8ec6aa00a3b20971d8d5400477c02e5b0aa8008f78758461550011df04b98c2aa00a3b209731855400477c12e7b02a8028ec825cf60550011df04b8ec0aa00a3b20971d81540361f43eecaa0a800c3e73dd95415001878e7bb2a82a0030f9cb76550540061e396ecaa0a800c3e70dd95415001878e1bb2a82a0030fe0f76550540061f41eecaa0a800c3d83dd9541500187907bb2a82a0030fe0b76550540061f416ecaa0a800c3d82dd9541500187905bb2a82a0030fccb76550540061f196ecaa0a800c3c32dd9541500187f03bb2a82a0030fa0776550540061ec0eecaa0a800c3c81dd9541500187e63bb2a82a0030f0c776550540061f90eecaa0a800c3c21dd9541500187f01bb2a82a0030fa0376550540061ec06ecaa0a800c3c80dd9541500187e61bb2a82a0030f8c376550540061e186ecaa0a800c3f20dd9541500187c41bb2a82a0030f08376550540061f086ecaa0a800c3c10dd9541500187eedb9aa82a1824fe1b73550543049ec36e6aa0a860d1e63dcd54150c1a3ac7b9aa82a0c64fa0b735505418c9e416e6aa0a80093e81dcd541500127b01b9aa82a0028fe1973
  | 25 => 0x10000000000800c00200000000000000010008020006004004800c00200300080000000060018000012003000000400600100100000020010020000008001001000000200400000000060000020000002001000000400a00600000140240000008004012000009800400000000100040000000020008000001000000c00e0060000004006006000000400c000000001c000000000000c0040010020028000000000000001200000080000040030010000000003000800000000e001000800c0020018008000001001000001a0010000000008004000002803200a0008000000009000001800000700000040100000010000004001000000c00000200300000320030008008008012000000c00000600180040020000010000006003002800000800100100040000010008000002003000800000000000100480000030058000008000000802400e00800000000000070048000000000000800c000000001802000c00000300080000000030000002000000000000200500200000000050000004002002000001800e000001801c0020070000000000002004801401a00600100040060040028004000000002800800200a0010000002001005000000000000000000000020000004002007000800c006005000800400600200080280000000018030006008000000400000100400000080000000000000001001000c0000080018008002000003000c00000200000080160010098004000001000000800400500180000000010000010004000001000000200900080040000020000000002007000800c00000b00500080060030008000000000000000000600d00d000000400000080040060000008004000000006003800e0060008008000002004800c000003002000c002001000802000000400180080000030000000004000000000801200000000000040010008000004002000000c010001002000000800000100000060010008004004000000800000000000000040080000000008002003002800c000003000000c002006000800400a0000000008006000000000c00a00200300140000000020018000000000000001200200080040000080000030008004000801c000003000004c0020000020004002009000000400c00000400040000130018000000001000001400000700300080000000020000000003000001001a0030000010000000000001c00a000002001c002001000003401800300000200100010000000000000000000c0000000018004000001000800400e006000006c00200d0000014008001000003c00000000000000000040000008004005000001c00200200000000000000008000000000000000000c00000000080000000010008000010000800000c002007000000200e0048004006000004800400200700200100
  | 26 => 0x9b47da4d53f02774008a2640687b08b224f43da828d986232079992a3440404610d4c4a00037d91c42346915228f7c28b0000000000c1a000000000073c0b94ac2fb570c0002699c000000003d20001964ab407400000000000002380e94b420000821a606e898b0da800017b248800180a74200020e96bfd000e511b26f20000000000000000000329000000000010391e8c6c000117c000b0f61031e0000000000000000000033a000117c00000030100003bdb84000116200030b0000176032000000000000017a00000000000000ed0c40c3880018c00006c30700000000000188000112a58e049b3080000000000000d0277f32727852041674fd0140af41525c18000000822000000000000000029c80000000001d187de02035c2b2c23eb43000223800019ba1780005140000ae10740008ae6189498e960001550000000000000000128e00000000002d000000005e400000049faadc95f35a23a9f8c390b6b00022dc1f80e609ece5107e0003672a28000cf8000000177d3328000bb80001a814a00000004dc103b27146ec141492cac8fcbc780000000000000490000000a6c34580000000005c09455330b7c00009f8280000196a9a882447b5f8000167e1850898000fd886715b80009b40140002850000ac80000000b6c9dc9b7050cfdec3a0000000000aee29c0afc3dc2230000e11890cba0000000aec2d58000a1578219a6810000fc80000000000000b550d500000000002038000000000802001200500080040000080018010000000000000800a0020018008014000000800402a003002000c00000200180440020010000000000000000000400400100000080000050000000004009000000c00000100000000000050000014000000002000000200000080000000000018018008000000000000600a004000c0000000008020010000000002c000005006001400e002000000c006008000000c00000800200080020000000030006003000000000000e001003c000001001800c01a00100000080040120038004004007000001c0060000008000006000000001c0080010008004004015004000c0000020000010000000000000001e001000800000000a000800c00a0080028000000002006000000000a000000000000000000000040000038004000000000000800400100000040100010000000004002000800000000d00180040040050000008006001000001800e0010010004004001000000c000001001800400c001000002400400000380000000090008004000002001001400000400180040040060000044002004000000c0020040000000014000005000000c000006000001400700080000060010008004006000002001000800000100000000050000010008014003000c00200100e800c00000100200000000020
  | 27 => 0xa09000195d0fa1330000c90c3682c00000005587931239a343ae6a758d800178ac7b00000015b272a0ac00000bc0004b22178bbf23d5e1abd117481c000174cdb4d2a00024941a40000000001762000000000000095e1cc103690d2960da2b780000006a20000000a5e5e980000006130002318000d484bae3e80000000ce8000aa200000012880000001644a1da4a00016dadd4b6a4243f8b47d86a369000000044e00000000006d800000011d01ac076b62038cbde00010c0000000a0c0001ac008b0005ee9628faa52e89a000000000000000000000005740000162000000302400039a000000000004b0000000000c580000000624a8c459a6d80000003af000184473769f1b600000002bc80012ba0004510001a46572000000000000000014c80000000002c79458111e120000956000442000000000000034b4000000153800000000000000009dc4443688000000a7b55d84c12800ee08606d41481b006790d314e1716850a300000004c900011384f80000f78000000084a87400063c562a9f00000003ea0000000432452000000086680000017b00000002e1470600000000001f381202ca1e885000000005d4c9000001e80000009a500000640002044ce00000006fa000000000000000000000000000000000000723000152896a000557b4380007e500000000000005749b3d13ccad000000000058f09c247d312c1617a82806647331fc9fa58ea06c000073c8090435b29fe800000000000018ca8c500013e8000b0b00026b5a52bf9000111c000000000000000000000021dd1ec00041a2b1110400039b000000000000000000008192cf00000000003828000000000000000152c1f507228ad736b8965615244f2398bef1b6d27244339c80000000000000000e340004531e440cec32000000000098f80016e004bd190d32dbc96615e100420c0000000000000000000000000000000000000000007243168001a4c96e0000aa163473814d9c60000000000000000000000000000009440c780015a400005a0000000a1e00000000000000001a8c00000000000016ee000000073400054c39fa7084c400000000004560000001280000000342632000000000000012e2000000000000000000002ad4b20000bb2dd8222000489a1600000002e7a8a4ce2000000000000046c3b4800000094900016303dabda050800000013c80001d0000000000201000078d178800000000000000000008fb140ab9d05a00029986e0d327120000b68534cea5e3800000052b03e9b1400026c52800000005ea392b154000000000000000000065428c184663a336abdc67b6540db800070000000000012f06be000032959c000000000000011800002e609e8ca000000075c0000002ae0ad500000000014090001e60692bd8a06000130d09e5440668
  | 28 => 0x141a00000000000000000a464240000001d600000002690000768aa6a285d380009ec4f580022b57f680a0000f175040003d434f476664b443000000000000026cb1920003358f95276c4b272800000000041880003d0000000000000000000000000000000000000000000000000035e0ecb0f0000e745030000000000ae5270a1480000000e20970dea5b459b2ea0000d050b70804c7912917d9660efa0001d0222400000009e8854175cd400021a40000000a4162000000058306c4000000000000000000008cc001954c4101288c000055f0002724000000000000000000000000000007904d8317000000017031fd9042ab0001940dd850d00021500000000cf1efc00038c00000005ca0000001e26010000000000104ac3340d88d4f6a0000002e1182200000000000000000000000000000645800098000000026159ac3d9000000000000057d13a00000000230000000cf536108e149a0002cd198c0a29e600000000002e90002fcc00000040400000000000320084000000000000034a39d00000000000000000000000000000000072e22f2e29120000a7d5f4e268ff77580000000000000000032c00000031600000000000002cf0000ac130111a800000000016c97a00000b5c000ab83f24da9b8c0005a300000003ca20900000000003b937ac0007a8000000000199c0000001a78068c5a00012c871e7eb0001a004d11d667400000009900002a3c00000000018a07ba11e19610c479ec9b000158163861d11b9be0a5c87500021f80000000000374000000000160000000048686c800085f000235529a0003cc000096162f0e1a30102c00026800011280003e1085d6585d9400959a63815703a9fdcd2a000511000034854722005147103ee643150a874b495b6b1f13c47e648ea66961a0af50fb34878467221b91ac5b55e433dad68c923302af1d58c80cc300034dc82c3c0000169400013c000000144a0472912c380000002440000690bf138e000000077b000000020260b000174119e0003d8009000000057590700001770000000b1200000000000009d60e980019781278fe40002d50006a08300294acf40d0ce93de02f55f264d1001febc5878c5227a55c61034000af50000000000000000112800000022aac6491400034e0000000cec2b4aef731600068f0c6cc8201fd6a00019140000001e5144214b8cc83d10fe8851b402647c03e600016c400034c20c05c82c2a0e5f5a8919c6ad542480009240000000000000a170000000ea20000000000a4081400000003416e506f9fa00004e66869b18000bb433c92597a250b69080000000006372350000000144000033e9e00622fd8a100003adaa2580e00067f000115e0000000000c241d237f5eb8000000290f18cb5200000026a4d2000067733e87f301f1e73020000
  | 29 => 0xb2f59da9dcddc4f4283207c3ec0de000089400000008ca5f41de4af000000111624e000004200000000000000000000000000952a762f929501ee188579339821c000000000000000062f25fd516563174600135e0530273200cd809710b02e35c81820000b74b043598000c3520e00000009c8f3e0004c6000083d35c8000774ade0000000001a448fe18207ac000000606291c3f8c5100000000004fe0300000b8c4d7265000000000000000016740006268000ad00000000158b4c1fa00d0000e62aff000000000000028986ae0001e70001f3d49c000000000181a6853d6e1411140001e82ffd89ec2620898d8f34b394e80a98fb3c1e4fb248ae0c0000000ec508a0001c495600002fd0b60000000000000000012c0000000dd075254e00000014940003a612e0000000105049c00037b00009d887d8ce00000007820001449b2400000000017e000020c00000000000000000000b0f0000dfc00000000068d12953bcc3f667896051abc25892bf800000000000003ff46e2b89450f76563d93278d84a8ed000000029640b45c0bfc00033845828b40e40005f900012ed7bd000021000000000000015fa33131500007a68cb3420000e2a6ba0000e1c6bc70268480012be000000000000000000000016ba00000000006e60334fa0636b20369dcf8cf893a1f941eb1c486b02b22d21d21e02cf3d8b40c366135db41d35a022bc00000000001050038000d82000000145d85c0000d570f54c20005cb94f59f200002b800084badf0a98924ae60003b01b998ba9176689360724b1849e1df15e2bfd646000030900036e89280000001288000da4000000000000000000000000009f91d22a14de61cc489c00152e897283a5bc0000002060000000000343af3d8704e933d23f14784841db283d4be18d27581f99ce91e386800000000000000004c842138491cd55c0000a78c8c0000005dbc8340008bd48313219e20000001b4c0000c124d0b00000194032c0004cc97e5dd043b9ec103174305c000b7d03b1984bfcca546f13a85045004878000000192bbb000000000000000005400005d9000000000000000000000004c085f97b6ca135ea66c8b82fa0000c2611a000000000000012f8002ca80000405241618000b730001db4f7069600030080002130edc00000000013d2118d5a7a943cac8114261028eeee114a02e000000000060f000000000000035105cc9da6d400010d0000c4e4df84e40003bd24ba8fc19c00000017980000003aa91eea4e88104a000197c00000000000000003c2aa70a9000000000000d252f000000000000055eae7800000000000000000001d240000002e44681a6c29500000005353448f51a92a94420cb50f4813600086261480000000000000001832ce9000000000000031200018783633e4ac100b4b67000
  | 30 => 0x480000000000000b51a78000000000026100000007880000000002f320000000001080000b1f00024ea00069d1b5b44983686aaef20c2000000000265171cc9200000000001253a3a8713723b52e0b518bee7f34bf4000000c6d000016d9ae67d32311ae0000004d53310000000000000023867c00000000004d65a0a11e0000004698000000000000281ceba00036b00000000001661eb1268a94000000069e0000000000000000000253d46200024c00000007fd1fb00015de000000000000000000000000000002db9ef800023620a015000000000032c4d6e12090a000166449fb3b0b44000000639800000000000022740000b80329cd000000043b19fc67d94115cc0001d10a2431abe153a5da67b80000000000000000000000000252f2380180b200005840001e480006e204480010f44fe000000000000052c00280000003e20002180000000000000066a46d00000000001f300016f000000000000018163ad00028460008f780032bd41606300000000004bf000000028c0005d200017a4000000000093667340640000007590001b1c00000000000019b80000001ec8bae00000000000009360000000000000000298c0000003b180000001700002eec00009e000000000094b14c318483c000000000000076b00000005ee0583a401f000000000000004f60004ed8000b800000002f58000000563a14c0000000000000a520000000000000030b9780000000001200c3c59a88c1ed800000082760080000004c225880000000000000000b9c00000000000001d980000000000004120000000683434c00000007f216b38074e6aa3789ed0d640000000000a122a225e0001a200000002d7c41c0001a6a4dc8e9bce8c18f1a000ceb5b20511940a9b62021040000000f9260c022832525ada44342422678e08000bbf321b21c0000004ea868cdae36766590a6551360509b3f0000ac600000006e01bc2a000009de5a84e500000004460000000000000000058c0000000000f6916a8df09b8b847970005328d2874497500017f4a36867800205c7e25210001688dfc00000033c96a40000000000000000000000000009b1ab1fe0c645eb00000000000d400000019c280f15a9f016488eb2ca1c5800063538f08e58249b40002628b407fb0001d3c000000241934800044b313000000000000000016b870417300004be00042b00000003f680000010aa2833570c840006ed00010953908b90640000000556000000000027d00001ac00000000000006540000c464540001ad000139c938b6c000299068600058b80004d6b270001a39814000477902a00000022900000000000000ce532f98600000013ef00000000000000000001cc18ee00000000009f50005d817280003ec61a000041e84328b2450d78a3860188718209034d31d39a3
  | 31 => 0xc014d6add000248c0008f05862ac400047807a40006b019989400014660000000132fce00010d800000000031100000008ee3c4800000000020649800002bd000000044843e471109b2b87c80002a9000000000009bd4b62ef5d7000000072d00000005681fb25080008ae60e80000000000000000000000a160000b5c0004bb501ac9548214c45d836ca963d78b32c449c09533f12ef41382f600000000000001f811e85ac0006680001382bd9603102040c00062100000000000002bb44a48030c7000000053a0c206b95a66a5040932439c5fc0c9007a60c7683e88000000c8e20100000729cd4cc54650d00e20b012a8de80005f720453d6c0035b1d0c22411d0c84a742b2bc809a800000000017680000007700002f9839b7db000088800000059e80005fc000087800000000000000000003af000114027e72e000080d5e059d000178c0000003188000dd658aaec40015b030c800000000000000000000003d88000000000c1c8001d94e067a6000000000000000024284050000001d1000000026600000008023f700014544df32b000000000000000000007570000000000d144468000ce00000c80001358000114310d96038120513fc07079e000000168aa5be2cb3786f8c6a263919851c00000001dcfae47a8002410f5a01200597e54d200000000000000000000000000c6600000000006a44f91ea84c665905800000009a355c800124f53700017e893c54d0e10000000000313800073e1200001548cb642c2ba000000000068b21c4000c89000017c0000004590000000000000289c6526420000ba8000c6465d800000000000000f0d070002950000000d0700018dca1c7b1da88000000a0100000009a80000000de84f0aad06130840000000fa171000000046629fc0000000000000a3e0000001f8a0000000000000000000000000000000000000000000002401ec326f00030a9fb4000b9c47b8e4400012a52b07007f8000000152229da7a0002f9d27300000019bda620004d20001574000000000068a0000000c1d357cfd0350000000c3b5a7a2400000ec2c0a281440b7961400000000000000000000b4400000004ea00038a0000000a7805b13c41d497300000000008445088000000c1d35a91046c4c9300001c6c0252800015ca00036600000000000002a11ff0b5624500000000006bb000000000000000000009b60005ad86e80848d9000000000074980033b40006f2413224c000a4448584281016d90df80018a81fd0c01448b840000000001534acd000158922c0002de82b8036c690b598285903e84be000043a7bc000000000000022daf5507c0000000dff0f000001311600002310000898ef00002d5322020c0005682f793d4780331400138e0ad66680006ca0001912d200000000ce41bc00000021
  | 32 => 0x550000000000000000000031c8f61156bbc0002f8000058d0000780416755a91800000053080009b80000002850c2c000000594800183400000000003be8e36961195a744f9192a918000be22f7160c4962566229cf098a5c74ff84ad7ca9e90000000000000000253a0000680000000d284b467da46c548000007e76b60900001429a00001d90000f8547c000415a1de1f2337640a6b90690b54e6000068002a00000009ed0000000bcc00005200000000001bb33a800000041f8b8c00000000061580000000000000000e420000000aa4afe6d9d8a872c0001260000b26eeea0f8000000006000024400000042a00000000008aa00000000000fe0003070000000000000173448d000042f7c20000000000e2e00000000012a40004a700000000002d20000f9cca34ff0000000aa20000af83ee96c5bdac002460001ce1d480000000002c1a00000000028f418600000015688c09e74a295194640005cc8000000a5500013793c8aa011495b40e25d2956a4bc872cef0ce0001a2e5ed32e0e3878c9a6d710000614bb892a9216778c6f39d81207ae0000a3ef3484c4670002f01468320000197800057c6079e0c18c5b34ab1ac50b37d31498000c76b925c82d8131d8ec39900000006d02114000e7c468000020001979b3f0800000000000027860000003c40ec0000aa15b180001b03a5000000000000029cb3600000005808000000000102800000000037c9cb04240e50001b2c000000000000031400039e80004900000002530000271000000140400000000000002d800000014768f13e188a932e0000000001a8a79d50a8ca000050c000000024400000000005a40ff1d9177adb80000f800000007c450d8000012a403a815a20000000f88e540009da00027b00000000001bbe0000004e300000000000000000372bd40000c60000aa3000000000000032380010ed2af13986ac04e0000000000e22000000107d0cc00040819b800000000000000000000002eac0007fe3b700000000005118fd56c40003cb08ec00000000000000008cd00018680000000002c2400000065994f094c000000096542000000000016f020033b800000000000000005466ff4b4906cbe6682087d478bec0cc00686973e60004fd808c027b6a5c11eacc9a00008d800000072761600000003c50003314d5205c25728e956404443ac3ac0000000001c7400000065a24b40000000000e2cff200000000000000000000000ad612b80017fc00000000000008c400000034557f465d000000000010400000000000003858000000754237a5acf184fc3e8000136100000000000002cb140000057600016cad340000005eb9ffc488000000000142412380000007944a7148000000000000011c8eb800040280001aa0005d000009ea8d760723a40005e712624a40
  | 33 => 0x540005fa00300000000001eb2f980004d3805a5d6b1d3c380000000004fbae607fe00a0002d306be0000002f312b200000000002c40002f42dc000000000002b000095464c12e461031700000012b68ea00007f800000000003c95f260924a99883a0b8f430a030d1029c00003d80003a809654956bcac93061ca07e63c78000000afa00000027f000000019f800000000010f0918000a79327800000098f00002f15e60002e8800097c00066480000923ea6488f5400000000011a400000000000000000000000dd860600000000015d88da613ab6879a896162259c7ac8bc00004ec9480001f58018000000659cc09670000000000000000054680011ba0000002eb000000000000000006f600000000000611c82a4c6ae121cc70000000187dc980881220004c69c880000000000000aaa0004e28000b360003e500001d200000000001b2309000000000000000000012696e92b140014cc3aa00010f19340000ee004c000219664039e00078ad21a080d4c01abec80000003866698b4c63a0002ce095cb865cd00000000000000002b3b15000032229d0000000000000022b00049d00000008f8c196bf000000045a1134000adc000000000077500000000005d65e50000aea00009700006ba000000000174470f0c4a7b40007cb66d20a0ee50002b2800000076f00000000005c96570c304220000001e64e203cb00000000000000000368000000631099c72c00000018cc000196000258020000000000000000000002ab0000a4200000019e67d1acf8b3a01c7f462600000000000000001a504823302439628c152b60a180000002df26c44d071969030f971439302602142160004f880000009c4596897400000000025b556000000000000000000000000000c365a8000170e1e6200aeb400057e6280000c0042b00026c87fabc9642953c000c5354c00010ba00000031a13bb72b59a029cd9aa8e0de800002ab61484181925c00000000000007af3898000ec40002ef80018e4aa75d50985290678322a12c85583536f08807577a75b91f1c0e00a864f00012306930eaa8b901fcf40ec26654e22a12d82484dd0ae1018908886023f0f0ad290526f7417848429284857b26f90804ad2c3800000015500000007a2000000000000050f41bac84000be948812d80005350000a5400000000000018ce0001d18294000c42c361a18a04098439344c8a67012e90e643c800000013f4f04669000000056018cc2380000002c30000000cd0928000165880c05532600013fabdf1ee0000ef28f82e58000000000000000100c02d1198de28675e280000001e10000f5349c000764498216c53e0005399e1878806182e80006210000001ee8000d40000023d2180000000000000000000111400000000000001a06a02f08000bcaca60000d108f20000
  | 34 => 0x69c1fd407ecb91c680000000003a48574fb0353211997c000000258133828e40397184925b80f117819afa72d321ff6588a863465688968f8c0000000000000ac031f1867a3637f00000001ea6670000c50000d472ec25ec6e449440c14104f80000002864000000000000034000018ab158f66463243066360e0f3acc909e634000000000000023201340003b64c10002b08000ae60000ef97160006098001a3a33c672af3f1585b91e91a7c4d497656b0b3f34292b000156c9460000000000b2e00023b959e0000000000000d800006238bc8000a5263a000117e00018ca5186b87cd00009c100e9220002f3924c00027ec8086f09cb65c00010ca0000001e10be8a5700011c15941564fa91092642b60000000ed81f800000002f80004ad2601136b60d2d00000002ae1268000000cc606380011b80004cb0000000000000005c0008230003304000bb70000000d5800030c9df8c5625325d00014dcb3734b96840009ee00001e0aba15b00028152a280e5d09f49510d080e5c0004a80000002e8d0d68a911d1b288705db23e80000002b911701e405800018f196026256a19b25412cc0005f7ae7400070a2689440000000548b0bc56234e37780000000005a716bca3800028e86a5944a673170000000355409800000000060f800192c000000255c59c0000000000000000000000000077a0c980000000000000000d420a92f893dc50832646210cd2549b861b8000f42bc60000f0d5f678e0011d1467a48124826dce3697a0923118000000043a3480000000d3a4f428d00065b8ac85bc7658000000000000000000000000029a00018725a7000011465643b00018636204490000001554000443adf2ca49f00002b0c0000004fc041c0000000000000000c7e000027496e607000109d33e7d5a988d841f66170000cb80006e1187252b58529e110964d23479700023c801e53f55b0be56ac2df0e88000000000418000000000000000000000000002e34000b0257529b400034b1f380010ae7a30000568ee828f0000218676419000000197e00008a8000000000000315d262603000000146c83c3f8067ec527410002b5d350d0649aaa548ba000000235800009a000000032e0001fc14450e80000000cce85ca394e729f9184000000236c901767000000000000000021bd9b1000598aea400044e0b280000000000000c1400000069b2cc0000bf80000f8c00001e00000000007350000000000bb54900208000000672000137400000028000000be0000071606333036800000000000034cd64600000000013d00003721b540cc8e72e400000003476861dcc4b6b965661e880000000b69968f8a0004e795dc35f00042896026b76c83c78298000c9f0002e20fec8385480001a1eabc5940000000cdd154c0000000000000000e0e14100005bd
  | 35 => 0xccaa2ba4b180012e4062e4780000dc00000000000007814350df94340a36921a4885f605000000053d2b30db0d25a220000e2800000008e67f80000000000000000b7e557000000000088f800000086d0bd0002244000d2e00000000000000000000000000000314800000020b80000005180ef27653402505972b8000078a2b8f50c000000000234400000000004414e0000000000025847615c71100000000000001a165dd3ca8000f7200040e800109a00000032f40000005d780017ee69a07d000000097900000000000000000000ec20000000000000377000027c00000000013c81e322c000000025176a07c00000000000000000000030000000000000000000000004f3102c8b4000b050000240000a925548b9cc220000003264ac83e4076c0003a500033f0000000c8d00022d6000000000000000000000000000000000a6677c00011455a80000007260b50000000000000000000075a30f9884fd5035480335509804d5a59ca46b60004ee100d0b27b623e2d1c00000000000003fe3fe1b6ade80000000000000000cb60000d08000a58378138c00063be8200001770001650d05322b530000000e1c89f000127c000000419a5c000064a23ce5d0ccc00000003b40009bb000000000000054f000000083b06e00000004f000000000005f000000001ae00045185a50423f7c05a1b80000001aa2448b08409b32871891ec1816b499e31842399781897d8c6b03d80009b28d800008f8d72000000000000000052600f8000000000062c00093e517b0a949e00062fa6f402cd2b00000000006fc000000150c8c10000000000a5d0002d657223114732cf81a663f4eb9e713a23a631a2dfc4821913ed121c00000000002a938055966531c127063d29f0751286ca70bc2a0c31f6ab000032525800000016b400000023f81df1300002b71d992aa23400000012d003b16080000000000000000000299537a49cbf6a805b302c909c58564bb36435800000000d86fac842b080019280005ff00010b85ba04502e80004fea82b20c000000000000000000050c2d0097a536000000000094200000000002e9beeaf1000021f62da6ac5705e20f7a9718c0a814f29b80af08f35042b6c00053b00000000003ccc6a4000002110a9818387db4e45d30000ee275f000000000000045a4a940006e20000000000000000219025e55445b0ee14c40000000000fb800000000000000004b50001a762f8274736d61400000024040000000000001222592000039c21013655faf90714d352b38000b22a5116ccc04a0200000007ea820000029eff06a01be209800108490535f8b1cdfabe35df0508b2a00000e80013a6b082f00000000a53ddb00008a80001ac800000025e30c0000d18b464251a281a28b096484d20000b709f000000068f63b00009d8c30
  | 36 => 0x90f80010240000000002dc47914610000000e80000226000000000000000000000000000001892c790002a1c98c17a5ca261146a00001d025400070c3d008f02e8b330000000000000256298000000020a80000005ac00000000004a9c7eb1f59b70000000cd0000000000000000036f0afa6cc0004759fd26f0000029145852690a000000000000008800000000006b30000000000517800000000077200020253a48b9b739c7d5565414cf0000000b1627d949073646400004e98f40000000000b160002f0e7500001c9245800000000000000000003850000000d3094a000000016600000000011100005caa60800000000000006c83f880004c90728c300029465c407a000000103ca9f335010533a7d600000000000000000000a5a0004caaa640007b708b82253b08c74bb82fd1f2aa62448000774000000312800092466f8000bb3a531631fa802000000000019e0375000000000014e000000000000000000000000003f90000000ae3334c000000019800000022dc9d000138891c9330e08000000870070800011688341b0e8400000024c80012ff7c1000000129b0000000435492000000000000000066000000000000d1000000000036f92300000000a800015660000000000000000000000000088f0000000000000000000195600000000009f77531760000d688e859100011c885a5fa95414086ea69f95152323b700013116a86af00023849264a8168000108d5cc023ceecfa985898f800192a0370000000000bb3000347000000000022640000000000000000614554297200043f0cc03cc58a2433900b5538600000000000000000000000baab350bfadd0fbe2773448d440000000250000000ca92fa8000ae0297000159800037b800000080a988328939e7f66385ab80000000006480000d5017d200331c00018100001cd1fe5ae1d5800033641a000000000000000000011248d580010d80001da80017700000001dfa05425a00000000000000001f4800018a000000000000000033200019c40000002595a5e00000000000001020002f700000000002fa0af63f7000000000000013280017d445e00000008ac00019380002a2ba50000000000c2d189aee44e87eb80000010da3c700000000000002ea00000000000000bf0000000000000000044f417061cc0887c5bf16ed30e1950001d82000d3430e0000000608439ac4c1fa45153a800000000054206180001c70002e0000096100000016b079208b194c342d425b717a59983f4266a3940003c8000132c9ba0000002f2
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x6303f9761252d95400060bc8387594545000182d20e1d65151400060ee1f80594545000122f9859454885400048be6165150215000162491594540854000589255741842150001ca2745c06108540007285d1701842150001a2485185410854000538245655c021500234aa96d5170085400070ad97545c02150001c2965151700854032728d90615c021500c9ca194185700854000728e10615c02150001ca084185700854000728d50615c02150001ca054185700854000728d0c615c02150001ca143185700854045d2aa5b415c02150001ca061d05700854008d2a259415c0215000152895505700854000728185415c0215000103f97619541513018c8b24986550544c0012349161954151300040fa6276550544c001cc1735c061085300051a657645c0214c0014e091591700853008d70644835c0214c107cc363185700853041532a5b315c0214c0231c8984c5700853008d32259315c0214c001cc0614c570085302060b5838755054c800112f985d45450f2018d0b2597515143c800122f9855054987200044b6637515241c800103d97a1954151200060b2187550d42480014a6949cc618852000529a527318521480018a464205761512027e0bd8387550544800192b60e1d54151200044b65e86550544800132990205541512000629104865c4544800182c762156450d20006291d881591434800112f985d45450d200050b259751514348001264956046418520004a925181d8c614800186785e1d611852000689e14845846148001a24852116118520006a1213835846148001a878420d6118520006a12108358461480012a694e1b3118520004a9251860c461480012c59818c3118520006b018d800c4614800122f9855054185200058924554150614800126495607431852000689a1684cc46148001a26856133118520006b0a0d800c4614800146695dd861d052000531a4f7618741480014c6931d461d052000519a5473187414800112d98dd45490520005192557618441480014c4935d861105200052965c6418441480014e1901d4611052000589255841844148001466959cc611052000629e1c615044148001a2485185411052000728d04615c04148001ca06418570105200052a259415c0414800152895505701052000532640311d931480014e1900c4764c520007304c1101d931480014c6970c4614c5200060b18b8755054c400103d97a195415310006299c68498f62c400122f9855054d8b1000529a52739c762c40018a671a1331d8b1000531a5c6318931c41174e291d9170087100051ae55645c021c400103f985d475d91100040fa5b87550544400181c63e1d54151100060b18b87550544400103d97a1954151100040f26276550544400121f9855054d8d100048be615415362440c9aa0801913108510
  | 1 => 0x2b000015a72000000000000011e00240016a003116128ab448000000358019864530011c8c1e0a2006a18c0000452e0000000000000000270cafe000018c00003c1f1581900001320000000665d0006ce6000000000002d8a000002000000910000152294e024008406004ca570009c0000002c000000000000001000040000100002000030000000401000000000400000004010000001000004000000000001000060000000403000010080101c0000000000030040000000000030000201800000000000100c00000010000000000000042fc0f66273dd9541514d03d989c376550540050ba4a70dd9541500142d929c376550540050ba4870dd9541500142d921c376550540040fa6032dd9541500103d980cb76550540050ba4b81dd9541500142d92e0776550540050be4981dd9541500142c92607765505400507a4c81dd9541500141d9320776550540040fa6331dd9541500103d98cc776550540050ba4b31dd9541500142d92cc7765505400507a4f80dd9541500141d93e0376550540050ba4a80dd9541500142d92a0376550540050ba4880dd9541500142d9220376550540050ba4a30dd9541500142d928c376550540040fa6030dd9541500103d980c376550540050ba4830dd9541500142d920c376550540050da4430dd95415001435910c376550540050ba4a10dd9541500142d9284376550540040fa6010dd9541500103d98043765505400507a4c10dd9541500141d9304376550540050ba4810dd9541500142d9204376550540060b20b765cd541500182f76e09735505418c0fa63765c9541500182e82ddb71550540060bdd982dc5541500182c82dd971550540060bddb825c5541506312c9260c71550540040fe59801c5541506312c9260f70550540040f65a81dc1541500d03c97e19705505418c0fe5d8494b6550c0181f87e0d651514318c8ba63825945450c0182f87e0965151430060be1c825945450c6342c925d4541854318d0b249751536050c6322c92610311954218c8b24984cc0655086382e871977250d420040f65e86550544c86303c9761252596410060d61e81d9454904bb03c98595749464100417e61731cf655054d03d98dd754580410040f65e86550548c46322e92a1954152310040f26176550548c40182c62e1d54151310040f65e86550544c40122f9855054d89310040fe5d86550548840182f861d54350a211ce0b98787550548840112f9761954152210060bdda85d91438840112f985d45450e210050be5975151438840112d98dd454906210048be6154151608840103d97a1954151211d60b98787550540840192661e1d54150210044be6175151430846342c965d45450c210044b66375152410840122f98550545802141d3125d310c56008401ac13160031580212ec0fe6175d5261d0
  | 2 => 0x5000000000000000000000000a1000c3460019c0000000000000b300134a20000000000021c0000b2000017800000b800c95d2f9682d030000000002dd8a695f9c000003d8000000000000060210e4009a0017da2003327c980038800006842b1902670ab2000af18295440054090383b002f53c4f000000000000000013283100046431b410763c91000230000000000000000493b8000000000000056480e81437000017200000000000000007a2f0000068000000000000012c0000000d40035800003a000000000001304400ce1f94d1400638e0009200000001a0000004000000000226500094000002c005a000000000000000000000000000001540075208007c0000000000700000000d600018200000000093000019e00668000000002a96c0000000a40023a5c5804001e8008d308000000000003c003607c00740000000378003c008758800547e0b000006e0000000000000c00000000000170000104000026c000dcc000000000000000000308008b0000000003e8617614000000000000006c000000000000025800b800000200000000000000000de002f0000000002000000000012a000000000002a03800d000000000000001969d0001400006180089002c80000a4000014e0018800002f8010c00005720c4a001908400880900040000000000000000000000000000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x4100008c0083a3029d3160031580210058414aba2e030842a000242ba9594545c0215000161050aca2a2e010a8000d08254615057008540
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x94b
  | 5 => 0x94c
  | 6 => 0x5
  | 7 => 0x138b
  | 8 => 0x138c
  | 9 => 0x98c
  | 10 => 0x150c
  | 11 => 0x9cb
  | 12 => 0xa0b
  | 13 => 0xa0c
  | 14 => 0x6
  | 15 => 0x180b
  | 16 => 0x180c
  | 17 => 0x209
  | 18 => 0x20c
  | 19 => 0xb09
  | 20 => 0xb0c
  | 21 => 0x1409
  | 22 => 0x140c
  | 23 => 0xb49
  | 24 => 0xb4b
  | 25 => 0x1449
  | 26 => 0x144b
  | 27 => 0x289
  | 28 => 0x28b
  | 29 => 0x28c
  | 30 => 0xb89
  | 31 => 0xb8b
  | 32 => 0xb8c
  | 33 => 0x1489
  | 34 => 0x148b
  | 35 => 0x148c
  | 36 => 0x1849
  | 37 => 0x184b
  | 38 => 0x184c
  | 39 => 0xcc9
  | 40 => 0xd09
  | 41 => 0xd0c
  | 42 => 0x1889
  | 43 => 0x188c
  | 44 => 0xe89
  | 45 => 0xe8b
  | 46 => 0x18c9
  | 47 => 0x18cb
  | 48 => 0x749
  | 49 => 0x74b
  | 50 => 0x74c
  | 51 => 0x1049
  | 52 => 0x104b
  | 53 => 0x104c
  | 54 => 0x1949
  | 55 => 0x194b
  | 56 => 0x194c
  | 57 => 0x20d
  | 58 => 0x140d
  | 59 => 0x124c
  | 60 => 0x249
  | 61 => 0x1549
  | 62 => 0x16c9
  | 63 => 0x4c
  | 64 => 0x98d
  | 65 => 0x98e
  | 66 => 0x4b
  | 67 => 0x124b
  | 68 => 0x1789
  | 69 => 0x589
  | 70 => 0x15c9
  | 71 => 0x1709
  | 72 => 0x12cb
  | 73 => 0x3c9
  | 74 => 0x409
  | 75 => 0x10b
  | 76 => 0x1609
  | 77 => 0x130b
  | 78 => 0x168b
  | 79 => 0x150d
  | 80 => 0x150e
  | 81 => 0x128c
  | 82 => 0x130c
  | 83 => 0x20e
  | 84 => 0x140e
  | 85 => 0xa0e
  | 86 => 0xe8e
  | 87 => 0x18ce
  | 88 => 0x74a13
  | 89 => 0x1a89
  | 90 => 0x1a8b
  | 91 => 0x180e
  | 92 => 0x2cd
  | 93 => 0x14cd
  | 94 => 0x10c
  | 95 => 0xecd
  | 96 => 0x1a4d
  | 97 => 0x16cb
  | 98 => 0x144211
  | 99 => 0x24b
  | 100 => 0x28211
  | 101 => 0x148211
  | 102 => 0x184211
  | 103 => 0x178b
  | 104 => 0x58b
  | 105 => 0x145411
  | 106 => 0x29411
  | 107 => 0x149411
  | 108 => 0x154c
  | 109 => 0x28e
  | 110 => 0x148e
  | 111 => 0xbcb
  | 112 => 0x14cb
  | 113 => 0x19cb
  | 114 => 0xecb
  | 115 => 0x1a4b
  | 116 => 0x75493
  | 117 => 0x160c
  | 118 => 0x44d
  | 119 => 0x164d
  | 120 => 0x40c
  | 121 => 0x74e93
  | 122 => 0x1a8c
  | 123 => 0x104751
  | 124 => 0x104753
  | 125 => 0x104754
  | 126 => 0x198d
  | 127 => 0x1a9951
  | 128 => 0x1a9953
  | 129 => 0x1a9954
  | 130 => 0x20251
  | 131 => 0x24211
  | 132 => 0x25411
  | 133 => 0x21451
  | 134 => 0x216d1
  | 135 => 0x21491
  | 136 => 0x21851
  | 137 => 0x14c9
  | 138 => 0x2c9
  | 139 => 0x20291
  | 140 => 0x25551
  | 141 => 0x29551
  | 142 => 0x28251
  | 143 => 0x29451
  | 144 => 0x25491
  | 145 => 0x24291
  | 146 => 0x148251
  | 147 => 0x149451
  | 148 => 0x2c291
  | 149 => 0x2d491
  | 150 => 0x282d1
  | 151 => 0x14c291
  | 152 => 0x14d491
  | 153 => 0x20054
  | 154 => 0xb0211
  | 155 => 0x16c211
  | 156 => 0x21411
  | 157 => 0x20b11
  | 158 => 0x150994
  | 159 => 0x75051
  | 160 => 0x4214
  | 161 => 0x25451
  | 162 => 0x40e
  | 163 => 0x160e
  | 164 => 0x140291
  | 165 => 0x29491
  | 166 => 0xa4d
  | 167 => 0x195a91
  | 168 => 0x141491
  | 169 => 0x21414
  | 170 => 0xb4253
  | 171 => 0x21254
  | 172 => 0x75313
  | 173 => 0x74b93
  | 174 => 0x758d3
  | 175 => 0x74593
  | 176 => 0x75793
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 47
  | 7 => 1771
  | 6 => 6990
  | 5 => 3401
  | 4 => 210
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
  | 7 => packedAt gbK7 (74275+((h/729+packedAt gbK7 (65527+(h % 729)*12) 12) % 2889)*12) 12
  | 6 => packedAt gbK6 (372914+((h/2671+packedAt gbK6 (335520+(h % 2671)*14) 14) % 10580)*14) 14
  | 5 => packedAt gbK5 (216870+((h/1247+packedAt gbK5 (200659+(h % 1247)*13) 13) % 6575)*13) 13
  | 4 => packedAt gbK4 (15430+((h/73+packedAt gbK4 (14700+(h % 73)*10) 10) % 565)*9) 9
  | 3 => packedAt gbK3 (409+((h/1+packedAt gbK3 (405+(h % 1)*4) 4) % 11)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3fe03fffff00ffc07fffffffd09fcfc67e31ff
  | 1 => 0xffffc0f01fffffff80f807ffef62327f93fe4f
  | 2 => 0xc0ffff001fff03ffff0007c0307c3c79e3cf8c
  | 3 => 0xffffffe00003fffffff8003f803f81fc0ff0
  | 4 => 0xfffffffffffc00000000003fffc001fff000
  | 5 => 0xff00000000000000000000003ffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x920052125082440290a9654800cc4c2261095
  | 1 => 0x7242c0520a51c99480d020ab0722121c90e64a
  | 2 => 0x88b56b0513aa22e97a005701b05c2c69634b8c
  | 3 => 0x10d9b29e4030433e54e560023b803b01d80d60
  | 4 => 0x20fe3cef9cfcf00c1841820c3df74001ffb000
  | 5 => 0x3c10200800c08030608604303efbbff6000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeac8eac8ea88eeeaeac8eac8ea88eeeaeac8eac8ea88eeeaeac8eac8ea88eeeaeac8eac8ea88eeeaeac8eac8ea88eeeaeac8eac8ea88eeeaeac8eac8ea88, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36637
namespace PEqualNP.Outside.L_meta_36637
open PEqualNP.Outside.L_meta_36637.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 19 := block_range (n:=19) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 19 := bs0_3_0
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
theorem bs0_4_128 : Interval s0Atlas 4 128 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 144 := (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 (concat bs0_4_96 bs0_4_128)))
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
theorem bs1_2_0 : Interval s1Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 1 := bs1_2_0
theorem alls1 : ∀ k ≤ 2, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
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
theorem bs3_3_0 : Interval s3Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 8 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 92 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
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
theorem bgb_4_192 : Interval gbAtlas 4 192 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 210 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192)))
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
theorem bgb_5_2624 : Interval gbAtlas 5 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2656 : Interval gbAtlas 5 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2688 : Interval gbAtlas 5 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2720 : Interval gbAtlas 5 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2752 : Interval gbAtlas 5 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2816 : Interval gbAtlas 5 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2848 : Interval gbAtlas 5 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2880 : Interval gbAtlas 5 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2912 : Interval gbAtlas 5 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2944 : Interval gbAtlas 5 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2976 : Interval gbAtlas 5 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3008 : Interval gbAtlas 5 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3040 : Interval gbAtlas 5 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3072 : Interval gbAtlas 5 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3104 : Interval gbAtlas 5 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3136 : Interval gbAtlas 5 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3168 : Interval gbAtlas 5 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3200 : Interval gbAtlas 5 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3232 : Interval gbAtlas 5 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3264 : Interval gbAtlas 5 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3296 : Interval gbAtlas 5 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3328 : Interval gbAtlas 5 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3360 : Interval gbAtlas 5 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3392 : Interval gbAtlas 5 3392 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3401 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))) (concat (concat bgb_5_608 (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800))))) (concat (concat (concat (concat bgb_5_832 (concat bgb_5_864 bgb_5_896)) (concat bgb_5_928 (concat bgb_5_960 bgb_5_992))) (concat (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 bgb_5_1216)))) (concat (concat (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)) (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 bgb_5_1440))) (concat (concat bgb_5_1472 (concat bgb_5_1504 bgb_5_1536)) (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 bgb_5_1664)))))) (concat (concat (concat (concat (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760)) (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856))) (concat (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952)) (concat (concat bgb_5_1984 bgb_5_2016) (concat bgb_5_2048 bgb_5_2080)))) (concat (concat (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176)) (concat (concat bgb_5_2208 bgb_5_2240) (concat bgb_5_2272 bgb_5_2304))) (concat (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400)) (concat (concat bgb_5_2432 bgb_5_2464) (concat bgb_5_2496 bgb_5_2528))))) (concat (concat (concat (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)) (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720))) (concat (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816)) (concat (concat bgb_5_2848 bgb_5_2880) (concat bgb_5_2912 bgb_5_2944)))) (concat (concat (concat bgb_5_2976 (concat bgb_5_3008 bgb_5_3040)) (concat (concat bgb_5_3072 bgb_5_3104) (concat bgb_5_3136 bgb_5_3168))) (concat (concat bgb_5_3200 (concat bgb_5_3232 bgb_5_3264)) (concat (concat bgb_5_3296 bgb_5_3328) (concat bgb_5_3360 bgb_5_3392)))))))
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
theorem bgb_6_5248 : Interval gbAtlas 6 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5280 : Interval gbAtlas 6 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5312 : Interval gbAtlas 6 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5344 : Interval gbAtlas 6 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5376 : Interval gbAtlas 6 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5408 : Interval gbAtlas 6 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5440 : Interval gbAtlas 6 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5472 : Interval gbAtlas 6 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5504 : Interval gbAtlas 6 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5536 : Interval gbAtlas 6 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5568 : Interval gbAtlas 6 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5600 : Interval gbAtlas 6 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5632 : Interval gbAtlas 6 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5696 : Interval gbAtlas 6 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5728 : Interval gbAtlas 6 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5760 : Interval gbAtlas 6 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5792 : Interval gbAtlas 6 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5824 : Interval gbAtlas 6 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5856 : Interval gbAtlas 6 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5888 : Interval gbAtlas 6 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5920 : Interval gbAtlas 6 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5952 : Interval gbAtlas 6 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5984 : Interval gbAtlas 6 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6016 : Interval gbAtlas 6 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6048 : Interval gbAtlas 6 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6080 : Interval gbAtlas 6 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6112 : Interval gbAtlas 6 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6144 : Interval gbAtlas 6 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6176 : Interval gbAtlas 6 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6208 : Interval gbAtlas 6 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6240 : Interval gbAtlas 6 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6272 : Interval gbAtlas 6 6272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6304 : Interval gbAtlas 6 6304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6336 : Interval gbAtlas 6 6336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6368 : Interval gbAtlas 6 6368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6400 : Interval gbAtlas 6 6400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6432 : Interval gbAtlas 6 6432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6464 : Interval gbAtlas 6 6464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6496 : Interval gbAtlas 6 6496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6528 : Interval gbAtlas 6 6528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6560 : Interval gbAtlas 6 6560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6592 : Interval gbAtlas 6 6592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6624 : Interval gbAtlas 6 6624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6656 : Interval gbAtlas 6 6656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6688 : Interval gbAtlas 6 6688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6720 : Interval gbAtlas 6 6720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6752 : Interval gbAtlas 6 6752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6784 : Interval gbAtlas 6 6784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6816 : Interval gbAtlas 6 6816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6848 : Interval gbAtlas 6 6848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6880 : Interval gbAtlas 6 6880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6912 : Interval gbAtlas 6 6912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6944 : Interval gbAtlas 6 6944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6976 : Interval gbAtlas 6 6976 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6990 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608))) (concat (concat bgb_6_640 (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832))))) (concat (concat (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024))) (concat (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)) (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248)))) (concat (concat (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)) (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 bgb_6_1472))) (concat (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568)) (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696)))))) (concat (concat (concat (concat (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792)) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))) (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 bgb_6_2112)))) (concat (concat (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)) (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 bgb_6_2336))) (concat (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)) (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 bgb_6_2560))))) (concat (concat (concat (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)) (concat (concat bgb_6_2688 bgb_6_2720) (concat bgb_6_2752 bgb_6_2784))) (concat (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880)) (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 bgb_6_3008)))) (concat (concat (concat bgb_6_3040 (concat bgb_6_3072 bgb_6_3104)) (concat (concat bgb_6_3136 bgb_6_3168) (concat bgb_6_3200 bgb_6_3232))) (concat (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)) (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 bgb_6_3456))))))) (concat (concat (concat (concat (concat (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552)) (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648))) (concat (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744)) (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 bgb_6_3872)))) (concat (concat (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968)) (concat (concat bgb_6_4000 bgb_6_4032) (concat bgb_6_4064 bgb_6_4096))) (concat (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192)) (concat (concat bgb_6_4224 bgb_6_4256) (concat bgb_6_4288 bgb_6_4320))))) (concat (concat (concat (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416)) (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 bgb_6_4544))) (concat (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640)) (concat (concat bgb_6_4672 bgb_6_4704) (concat bgb_6_4736 bgb_6_4768)))) (concat (concat (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864)) (concat (concat bgb_6_4896 bgb_6_4928) (concat bgb_6_4960 bgb_6_4992))) (concat (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088)) (concat (concat bgb_6_5120 bgb_6_5152) (concat bgb_6_5184 bgb_6_5216)))))) (concat (concat (concat (concat (concat bgb_6_5248 (concat bgb_6_5280 bgb_6_5312)) (concat bgb_6_5344 (concat bgb_6_5376 bgb_6_5408))) (concat (concat bgb_6_5440 (concat bgb_6_5472 bgb_6_5504)) (concat (concat bgb_6_5536 bgb_6_5568) (concat bgb_6_5600 bgb_6_5632)))) (concat (concat (concat bgb_6_5664 (concat bgb_6_5696 bgb_6_5728)) (concat (concat bgb_6_5760 bgb_6_5792) (concat bgb_6_5824 bgb_6_5856))) (concat (concat bgb_6_5888 (concat bgb_6_5920 bgb_6_5952)) (concat (concat bgb_6_5984 bgb_6_6016) (concat bgb_6_6048 bgb_6_6080))))) (concat (concat (concat (concat bgb_6_6112 (concat bgb_6_6144 bgb_6_6176)) (concat (concat bgb_6_6208 bgb_6_6240) (concat bgb_6_6272 bgb_6_6304))) (concat (concat bgb_6_6336 (concat bgb_6_6368 bgb_6_6400)) (concat (concat bgb_6_6432 bgb_6_6464) (concat bgb_6_6496 bgb_6_6528)))) (concat (concat (concat bgb_6_6560 (concat bgb_6_6592 bgb_6_6624)) (concat (concat bgb_6_6656 bgb_6_6688) (concat bgb_6_6720 bgb_6_6752))) (concat (concat bgb_6_6784 (concat bgb_6_6816 bgb_6_6848)) (concat (concat bgb_6_6880 bgb_6_6912) (concat bgb_6_6944 bgb_6_6976))))))))
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
theorem bgb_7_1760 : Interval gbAtlas 7 1760 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1771 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)) (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 bgb_7_416)))) (concat (concat (concat bgb_7_448 (concat bgb_7_480 bgb_7_512)) (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640))) (concat (concat bgb_7_672 (concat bgb_7_704 bgb_7_736)) (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864))))) (concat (concat (concat (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)) (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312)))) (concat (concat (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536))) (concat (concat bgb_7_1568 (concat bgb_7_1600 bgb_7_1632)) (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 3 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeac8eac8ea88eeeaeac8eac8ea88eeeaeac8eac8ea88eeeaeac8eac8ea88eeeaeac8eac8ea88eeeaeac8eac8ea88eeeaeac8eac8ea88eeeaeac8eac8ea88
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 6 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372936 * 2 ^ 32 + 3939035784) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36637.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,4]⟩,⟨.and,[4,5]⟩,⟨.or,[1,3]⟩,⟨.or,[5,6]⟩,⟨.and,[3,7]⟩,⟨.or,[7,8]⟩,⟨.or,[2,10]⟩,⟨.and,[1,12]⟩,⟨.and,[9,13]⟩,⟨.or,[0,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 3939035784) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 3939035784) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36637

open PEqualNP.Outside.L_meta_36637 in
theorem PEqualNP.Outside.L_meta_36637 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 3939035784) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 3939035784) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
