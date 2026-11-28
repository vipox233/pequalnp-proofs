import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36793.Model
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


end PEqualNP.Outside.L_meta_36793.Model

namespace PEqualNP.Outside.L_meta_36793
open PEqualNP.Outside.L_meta_36793.Model
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

def SBf (j : Nat) : Nat := [4, 6, 7, 6, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36793

namespace PEqualNP.Outside.L_meta_36793
open PEqualNP.Outside.L_meta_36793.Model
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
  | 2 => 0xfff01fffe03ffffffc07ff81ffe07ffff38e3f
  | 3 => 0xfffe01fffc03fc07ff81ffe07ff81f01cf3cc
  | 4 => 0xf000001fffffc0007fffe00007fffe001f03f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x12108144220484901058a2a288a8a2154534d5
  | 2 => 0xa4aa528a51a9292a2e055511554455aa928a2a
  | 3 => 0x88c954d294a3b20aceac19d4467511c0d8d34c
  | 4 => 0xce8d9b1d193223b377367061879e78831f03b0
  | 5 => 0xf0e1c1e1e3c3c3c7bc79e79e418610c1fec00
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36793
namespace PEqualNP.Outside.L_meta_36793
open PEqualNP.Outside.L_meta_36793.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x40038000600002886d019680008000140480000060bf43bd43ee32ed32f631f531be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xa18d434cb2a8698f14c931
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
  | 4 => packedAt s1K4 (244+((h/4+packedAt s1K4 (224+(h % 4)*5) 5) % 30)*5) 5
  | 3 => packedAt s1K3 (83+((h/1+packedAt s1K3 (81+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x1fc07ffe01fe07ff03f07f07ff07c07e91e67
  | 3 => 0x1fff80fffe0007fffc007ff83ff8007f1e387
  | 4 => 0xfe00000fffffff80fffff80003fffff83e03f8
  | 5 => 0xfffffff000000000fffffffffc0000003ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xc04102022424008014508b084308530426cab
  | 2 => 0x54aab4c651d48ad2782b45546ad46856a91665
  | 3 => 0xa932656a9491d364bae0866d236d20a731a386
  | 4 => 0x31a3468d19191a46dcb2d408438e72c23c0350
  | 5 => 0xc1c3870e1e1e1c78ef3ce78e720843043fd800
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aaaaa000aaaaaaa0aaaaa000aaaaaaa0aaaaa000aaaaaaa0aaaaa000aaaaaaa0aaaaa000aaaaaaa0aaaaa000aaaaaaa0aaaaa000aaaaaaa0aaaaa000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36793
namespace PEqualNP.Outside.L_meta_36793
open PEqualNP.Outside.L_meta_36793.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x9800a000001a0402800000202294f00361ce8000010943200d0018a40021c8d3063e55100541058f30008032e0120a569c9001070496000012cd0010010400102c4ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xa1eae3c245a80968e7000783e5600a2281c8a007634007e6a00940054463a840044b24c009cb08c14a00086a64a504e00527290127440007a686c98a40082ac00006600009e203200082c162200609242640eaa18361038067c58482a5c30621a880c9a6e5e000402262e00a80a48080041c004000000000006021080389120c0920a1820904267ca5a1cf55243b7a92876c5250f3ea6a1ebd49439e29287ac5250e58a4a1cf950439ea9c853e5290abca6215754c42cf298853d5310b3aa6214754c429f29085ae5210a7ca9994f55332cea1e65ac42ccaeca3995d547329faa4653c548ca7ea8994f15132cea1a653e540ca7aa8196b10832b7a92836c52506bca620d754c419f2a6633d54cc73a8798db94b31b6a96639d434c67ca818cf550319f2a4433d54886bca710d754e21d6214433f5448678a890eb10821af29e815d53d02dca5205b54a409f2a6613d54cc33a87184f950309eaa0619d430c2dca4185b54830bb2886175510c35885904f952209eaa4413f5448278a89057d4d20ae29a41ac42482eea2905d145209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x26a621ca2a12c000b9e58e300022524810000600486c0028000058b044080170c6254c42a318943cca8d6310b32c910a51ccb15435473287195434ca2d6510832a318943cc70d4354b31a3189434c62c6255031a358c428870e5310a218758c544868d63108218b18954cc28c6250e30a3189430c30d4354830c550d510c28d6310b208758e548828d6310920c314c42483244214520
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x2a6084e282b988528e65411c9435473281aed2988510d047250d510c206bb0a621241415cc4214520
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | 2 => packedAt s2K2 (i*49) 49
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (788+((h/14+packedAt s2K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s2K4 (2640+((h/30+packedAt s2K4 (2430+(h % 30)*7) 7) % 109)*8) 8
  | 3 => packedAt s2K3 (998+((h/8+packedAt s2K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s2K2 (300+((h/2+packedAt s2K2 (294+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffff83fffffff03ffff83ffc1fffffcf1f1ff
  | 1 => 0xf07fffc0fe0ffffc1e0ffc3ffe1e07ff4e3e4f
  | 3 => 0xff81ffff000fc3ffe00fffc3ffe007038fcf8c
  | 4 => 0x1fffffff003fffff00003fffff803f00ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x2004088824020000a41280444022914810d095
  | 1 => 0x451891064894a12c0a852429921422b146264a
  | 3 => 0xa32d22921d2906556109ca82e540541a8b4b8c
  | 4 => 0xca51c4249181ab9a53a0622339996023e00d60
  | 5 => 0xc618738e1ce33e39dce7330311180c3fdb000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaee88eeaa8888eeaaee88eeaa8888eeaaee88eeaa8888eeaaee88eeaa8888eeaaee88eeaa8888eeaaee88eeaa8888eeaaee88eeaa8888eeaaee88eeaa8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36793
namespace PEqualNP.Outside.L_meta_36793
open PEqualNP.Outside.L_meta_36793.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xa006288e30000a5a480600bf43bd43be42bc42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x403040008ea98852c525065ca5205554430
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
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (208+((h/4+packedAt s3K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s3K3 (112+((h/1+packedAt s3K3 (108+(h % 1)*4) 4) % 10)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 1 => 0xc3fffc1f83fffff0783fe1ffe1e07fffa63c9f
  | 2 => 0xfc1fffe003ff87ff803ffe1ffe007fc1c7cf1c
  | 4 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8040888500808002904c02240229109408d131
  | 1 => 0x10891048252442502a11214921422528a22486
  | 2 => 0x895229034a480ca58426541654054a85454b18
  | 4 => 0x2a9c4252606d57394e83111b99960309f00ec0
  | 5 => 0x3318739c738e67ce773b998311180c31ffb000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36793
namespace PEqualNP.Outside.L_meta_36793
open PEqualNP.Outside.L_meta_36793.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d02fca5a05f54b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21c817e52902faa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c53502fea4a05f14940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea9081bf421037a84205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa51877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861df430c3b886185f94830bea9061df320c3ba64185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c217e50843f441087e48210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea68877d4d10afa9a217e53442faa6885f14d10ee29a215c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0x228820028020680c15804091560980a00824005f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbdc85197b50a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbbc86997750d32f721265ed424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41ef29c835e53906faa720f754e41aea9c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331efa1e63dc43cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa
  | 2 => 0x8d243e0f43180032c0000001c00062d078c11a67840010435866c9c09d000000d712f0000010b1ee00052c001902420c4a91de2c20011a1480d65543801f0704188483b39c35c8d133000000c00003a28e4bf0004b00000002c15263cf49453703886e80015c8fc000090002f006000000828ae08a0fe0004218e1182b4000000000005280000081874091402238a4a381369309d0d5000001118a700084451898000000000f700089c370033fc8f0aa230082000bb86500092cc2000000130be00000080d0d93f22e540fd1c614045044a0b3868688f9914a015d0695d04a6280a140092000852150b61a45105529c000968051d20007e8000bc5bcfa09a0f46bc201882787d4178003ec000000003e2058ab1bd000448002410ec790000db3ac68456000096660a0880042001241371de0000024a45a670020b80544d80002e4ac7ecf623133a3652b8000005287013228c57c4f80028e2200004d46c3851d1c824a5e4e68ba3b63b0f40664401e4881e328856cf39e010c3500005638a4a8250f40a4498000000000000000009000093800000078000a80f0724000ca0260891a8003721bc340120643001f24736819c000bd12a0c0fe13e1384809609909c38cfc8ed1dc400d917b3828ecb00000002cc5b0f304e470c08d8432171120000005c43e00018453c3202b4568243f10136a895091ba2dc954bfa4f48c2141a0de3d68a86d1ff14864c1b0fb396678d500116e2eccc8bf3b07dd1421412e4b92715709e888921b323210c28113104564ba1bc1d416061a213ca9249da531ca0008b0003a8000df1dd0a82e5160234261b4b59073e06b400033000430000cc07e0a01698700000000176480000000eb01a59c2c9782840f02f98311e6a4490c60005c80a90b190000d28003243900000038e399228810300449e80002e00103a290ea2c864975000000810000004c0668003624751ea02000434360b00001f4bea2f0002c4ca8000e22f85794d1f21c90e0440843fd2a0000480007c0610ba1804589623c838d316a3e4000310002225b4b41293a6000ec83a3567480001942e4d51b81d3ae0a465a4d3aa6184980043a240b4a100107a90f0c501c0180e0281001800010000001a06800120080080407006088041300c008060080a0980201000000001d80800000000a80e97a0e8060400e040020284c010120202400800000000001a00800058120000016000068000e05e0c0160200005000000000081e1280800816000040100001016060100200400800098000501005004138000015a008020201601816000000f80402006000020780c0190e0081403804010340100600030058240b012068020000a01012000fa198000301809000000500001a0580001006010140a002098100300202818148040b80001864010000080400002010
  | 3 => 0x58f00149449188719e728ca2083341dc792052f4370038064307bd171052bc2d4cb9b02a220cb31392c846c4696c0e85305a00030431c912332867980792b0d4594081b73da3e8fc0f51544c52184648468d2216239e0dc62204142788dda3e1e237ce21730347406b18d4a406cc290e4185686884701c6a0d210840069c101fd37e7cc879da19c340ef98933e5c02d0000047007b15308a630db1a0206000b18261566884f1c23981ec0005114c0007f0352503f0ee05344c39c1c9580e64d04a0004644608a
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xd500876b2154021da485500865e63947409758e51d02ad6210e409798e529025d6394a40a718d429032e5250a40a798e419023e65d0540c714f415031c5350540c714e405031d5310c40ab588431029c63508408f596411029e63904408fd95401029c63500409ed95401026e62153309b58854cc23e64947308f59251cc26e62d52309b58b548c31f5410e30b3588438c23e6494a308f592528c29c644ca30d3949328c29e648c6308f992544c25f63551308f994544c25e65cc530c7153314c31c544c530c7152304c26e62150309b588540c27661150309d584540c25d6510c30c7550430c2cd6210c30a7191320c25d658c430a7992310c25f654c030a7191300c27b654c0309798f54c825d63d53209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f20c795153c831d5454f208f99053c823d6414f209798f548825d63d52208f993538823d64d4e20ba580218825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d185534823e64145208f590514825e63145209758c514826e65c852097d8d540825c63550209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209d98453082756114c208f992520823d64948209798e520825d63948209b59621082e960084209bd95200827b65480209798f54c425d63d53108f99353c423d64d4f108f99052c423d6414b109798c52c425d6314b1097d8d548425c63552108fd91538423c6454e108f992528423d6494a109798e528425d6394a108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e6515110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910da580524436852881109e19520442f061481109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109e98052042796584010da54a100427765440109ed9510043695244010
  | 1 => 0x23c0040800002004100080501000000040000101800000020001e03c0300800030020040000401028000001500c070000000c04000000700500c0001400014010240001c000000b0140b0000a00000010020180f01801020000080d02008008040080001800000000140000c0003004018040000400c0003415014020000000001010090000a01c11028000480100406008130300000801008010140000400018010040500003a75924310e3f6550c4397d954310e9f6550c43c7d954310e9c6250c43a7d854310e9c6050c43e350e5210f1d4354843e350d5210f2f4354843d390d5210f2d4354843d350d5210f0d43548439798e51d0a5d639474297d8d50d0a5c6354342ab5884390b4d6214d428f9974350b1c53d0d42c714d4350b1c53909428f5964310b1d5390c42c754c4310aad6210c42c754f4210b4d53908428fd954210a9c6350842c754d4210a6f6550842d354d4210b1c5450f328f99251cca3d64947328fd9150cca3c64543329e983548ca7960d5232c7d50438cacd6210e32e310e428cacc6350a32e3d0d428ca3e649513297d8d544ca3e6515132c758c544cb2d621513297996434cb1c5490d3297195434cb1c5450d32cb152424cb8e43909329b195424cb8d4350932c7152324ca3d6595032c718d540ca3e64150329798c540ca6e621503297597430cb1d54d0c3297594430cb1d5410c32b3588430cb1d54cc832cb552320ca5f654c832a7191320cb1d544c8329bd95320cb2d544c832c754c43d06ad6210f41a718d42d071e53d0641ab588435065e63149419758c525069c6350941cb149425069e63905418fd954110677655044197d8d501065c63540419b98854cc66d6215331c755043cc6cd6210f31a719132cc71e54cc6319bd89544c66c62551319ed81544c678605513197997434c71d5410d31b3588434c63e64149318f590524c69c644c931d3149324c69e648c5319798f540c66e62150319b588540c67a60150319e580540c63e64944318f592510c65f654c4319dd95310c63f64540318f191500c65f63553219718d54c865e63153219758c54c863f6454f218f19153c863e6414f218f59053c865e63d52219758f548863e64d4e218f593538863f64542218f191508865f63542219718d508865f63551219718d544867b60551219e181544863f6454d218f191534867b6054d219e181534865e63d50219758f540867a60d50219e583540863d65950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c218f990530863d6414c219798c530867a6014c219e580530866f65484219dd95210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654
  | 2 => 0x2047b00033800001ceb9000000ac24212042fa87a0691000ae800000007d0000022200000000003916e00000000000029a0009cb68001d1dc0000000070a806400000048000023235884008be159180c1947b97a3d800a60000007c0d0005f26868b0400134002785a842001361b9b64e1926121001066630cc88300b98b87c100171a0b50000012e980004399e0002800000001f80000085000b000000102a013c000d20000000124002a4bd800b2800000000030abe0a47080000236a318a83000558e6600aa3c314000da001ae000000029c5896620800001be000b600088002900000000000000082800000000a7ac4000967ca2800000a0a882f0f84309e5fac6548406592c761c4a1a26341067daf00f0009b1fa9c93296800001540014000000718e0bc97600000870b20013e019e28d1208b16051000001ca14a56000003aa1a0000000000000007a0001c80061a840006a00000000000000000000000000011626164002de29800000ca0031000000b300000000798f4ab2a67427e1e0ecaa8baad02c448e230a3eac8009f0a2150de4288a4c0c0c491aa58000e0d82300006942000000020e111d20013a3a0180824ab884e698940884ab204853190bd2e803816000000011c57a944100000000000000004c000000c81e000008592aa3800002eeb38001600ab0b08950000000000174001d678000000004a25c001c8990600027651800af982002d00026e960140024c1f9de8b9a800000808c8541b866aec1eaa26aa4662000b828a3f922ab9bab60b40018e420680a800940920994ec30a8002d200000829a418800310fcbf1e45280c17a24b708e47afe4999c9a95a900000023a000500015c002d6660000000000000000006c1720024e21800001d40000090a527aaea8c0006f000002180b9580022a16a7a001fe820000000000000371147f2b6001c0920006ca66989da0000044000000ae00270002bc000d400168000000006c318fa8e1ac52292ae03e0003600000000000008000000001cc0e800002743c81cc1a5ec58006d170802a800000ac09a2c17800302090760030e00000000ee000005b00000046000000
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xd0086cf0d20985495005c044711a28b00000115319939031c0161440050218a181431c94354843a18eca1aa421d0f7150d5210e8638286a9087469c35410e32c1ea8b10871948e76d0d428cb06b1ac42a265439d64390932c18caa1a849960d54588430ca0e3b2a8990658354d6210f41a1ae629284a0e0c631494250706aa2c421e63431c95410d31a30e0aa08698e0d54588434c686ba0a49926383190524c931a1ae7292852060c639494290306a9ac421881439cb5410e30c1ea8b10871850d74949328c306324a499461835516210c30
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x800c020a0a80d516210e32a08805516210d3180d87190524c93180d87192524ca30
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 601
  | 4 => 396
  | 3 => 29
  | 2 => 4
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
  | 5 => packedAt s4K5 (18227+((h/200+packedAt s4K5 (16227+(h % 200)*10) 10) % 722)*11) 11
  | 4 => packedAt s4K4 (16368+((h/132+packedAt s4K4 (15048+(h % 132)*10) 10) % 632)*10) 10
  | 3 => packedAt s4K3 (1475+((h/9+packedAt s4K3 (1421+(h % 9)*6) 6) % 35)*6) 6
  | 2 => packedAt s4K2 (244+((h/1+packedAt s4K2 (240+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc0ffff03ffff0f07ff0ff0ffe1ff81fa39f3f3
  | 1 => 0xff07fffc1ffffff81ff0ff0ffe1ffffdc63c7f
  | 2 => 0xfff81fffe07ff1ffe000fff1ffe3fe0607cf9c
  | 3 => 0x1fffff8001ffffff0001fffc0007f80fe0
  | 5 => 0xffffe000000001fffffffffe00000007fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x5210c1188512100165013012602484b018d1b1
  | 1 => 0x84410220482400280a10410482092940c22446
  | 2 => 0xa22544903488352a0889aa135425416054a98
  | 3 => 0x2cb59892520ea59cd3aa0881d9901867680f60
  | 5 => 0x30c610e39c70c9e71cccecc811006187b7b000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeee8eee8e8c8e8c8eee8eee8e8c8e8c8eee8eee8e8c8e8c8eee8eee8e8c8e8c8eee8eee8e8c8e8c8eee8eee8e8c8e8c8eee8eee8e8c8e8c8eee8eee8e8c8e8c8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36793
namespace PEqualNP.Outside.L_meta_36793
open PEqualNP.Outside.L_meta_36793.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xc817e52902faa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c53502fea4a05f14940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a9081bf421037a84205f94440fb288817651102faa2207d54440baa8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef19661dc32cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c3dca5185b94a30bea9461ed528c2daa51877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930ef19261dc324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861df430c3b886185f94830bea9061df320c3ba64185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53883bca7105794e20bea9c41dd53882baa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f721241ed42483de64907b0c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb20a21f541443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd5090afea6a177d4d42afa9a857c5350bb8a6a15714d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310bbca6215794c42bea9885dd5310abaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbdc85197b50a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbc86997750d32f721265ed424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d077c87a0ef10f41bf29683ee52d06dca5a0df54b41f6a96836d52d077e85a0ef50b41bf286837d50d06faa920df94e41ef29c835e53906faa720f754e41aea9c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331efa1e63dc43cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c63de438c7ba8718df94a31bea9463de328c7b86518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498fbd4931b7a92637c524c7d8a498db14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618f790c31eea18637e520c6faa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fb90a21f6a1443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043ee42087da8410fbcc821f6190437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d02fca5a05f54b40bf28e817d51d037e83a06f50740beaa4817e53902faa7206f90e40de21
  | 2 => 0x341f800135000a08ba0000f00f1200001a40006d9810001f47ca5f384000000003d40d400000000000059634102386a0000004a800140000000002432a40012e000068654fa8c61d434405000390000001ab1600388a8003c8000000000008f4000130002603d86a46a001078001549e118000000000000000003f800000000190091ac4a43e8000000000009e8001746810d2362982cd278d900000000000000890fe1db000160cd0000006f04422c2f45c90208010223c4b9200000000000000057d2c00019e3840000000051400000000000159090000000028524a000e680017c7c400000000000180c948298408938010471480f83281fcd91645061bc000000004040016a1b88dc001c30b22c80007729e56c0012c0000000000000e00000000000001261b8000000000ce194000001a14da00000000000814000000003682a0000004dc000003f0788000003141e80026c4385500000009e000240000b491d0ba46226000000e73de018538b502c3213987325e00140000000000001861f6000000000d63100000000069471a7d5246d0d71c60008300f00000000000000284000000003d618c198004f6074000000000006b0002480003a94110c000000004004187998f2dc0000000000000000000230000fb800114000f8000140000e60000002f4000464ee69c00000218000001fb0000010124a00000000114234000000000000006080000102a0040000000600000000002000010000020000180200000001804002000008020020040000200200401800004004010020000000380000000000000000000000000000000080000200003001000000018000000040180000800000000000004028000000000080700200000000004000038030040040000000000c038000020000000300e0000080200a01000802002004010010020000380100000001802000000008010020240000000200400006000000000000020000180100000c0000100e00000803000008008010020100000000000801000000000000050020000100000c00001001000008000010000040000200400000800000000000000060000300a00601400000000004000020020000080200200c000060000000180000000c0000200e01c0080000000004800bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857
  | 3 => 0xf2000100000002ac07871000000a8800000000000000000000000004600012800360140e00820000012e80033e534001be000000d4267528000000000000900021428e564000e83c0000000001fa0011f0004d20000000000081caa9b60005d40010b00000000062000000000c70009c40000000080c000002e600000000000000000003a000062800000000000001069e4000000002b4290000003a4bc800064579071fd4208b4000b4000000d30f60006a46ea21256000000d7000000cc0431e86340003100000d1c8000005b40028c00095c0028b124000000a30d07f8000000000000014e000000002954a62ec002334ac9f8001ee4780000012d000131228000006cc7326e4cc00000000000000002252ac4480000000061400000000000002740bc000e5a8a000000d8804000600000000000000000000015c002195088a0000000000000015d15c2a00000045403400000318254de8bc28c3c11106c00000082a23000174390000000002e00044e0002524d000000980d0000000000000ec001048152ee355438e200000075a8803ea3c3e000000000d50002ca8c8000003b275c001040e08ec22800000728000000440014300000076000000096000000140000000021845c0000016000000000000032334001890000012203b304000c9056000000001bb0000000000033a1107f8c20001354b000320000002544de000002490ce73c000002e2968000001984ed281b50002c4301ce2d0000000000000000000021c0000000007e0000027c000000000b72940007880000081800000000000a98850000000000026429400000000000000000000004200000021c0002d13a000000000000011024e054000000000003f0f19c94160f80000004c7b0160000004880000043c2348c8294fe41c17889148000001310007c80017f00000000000000000ad00008e000000005220001c000484a04000000be9453200000000000000000620778000002680000000000000000000000000004b600000148266000579e50008a481800000001341ed00079c6f8f71280a0000000000000020d000000fb1e60a600000000374000cb8000005e03a0a10000009318e3b800400166000805468a24700007200000071c0000042a000560000000f400000000000000662207482a9a300000000051000584001c5000000001230000012f2160dc8e80027600045800000000000658000005f8c5a3127e9a8ab800000000000003bc0000000012077c00289336001498910000000011d00000000000000000000000004d8761ff4c0428000001ea954329f90000006c0000000000024835e0000000000000000000250001088000000009e069000000000000364448f800000000f08000009e8001f3000000d200000024c0283700
  | 4 => 0x1210004f80021b000124001992d60010fa704b24340000022e2a4cb0003b4378c20183a818472902074000000000000000000030e400a494b456001050000820000b8400005f01c8000005ecdc89b0044e5318000007445b00000050c0000000000000000000000ce1293f4270000002ce00000000000000001c4018000000ee25c43c0022600074cb7800000000a20000000008da6b000000001d6000000001930b6000c195c2c45d8f40000004e8000000000011f8000008754b9a2424300cf22f000000000c30000000000000000139108118380000002d2754a80001720000004e12c92c0021304e00000000000000000000000004c800000000000001700000000036e0000000000000000000038000ac1ad00000000170000000000a60000000004200049cf4a340000013109e0000013a8000004d04f800000000000210005f45f800000000c88d3382024000001da0d8000000da4781728e0009940000000000000000000000459f40003c8b61dd020000000000006fc00000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x5320c26f62544309b189510c25d658c430a7992310c25f654c030a7191300c27b654c0309798f54c825d63d5320cb98a54c825e63153209758c54c823e64d4f208f59353c831e5494f20c755253c831e5454f20c755153c834c6254f208f99053c823d6414f20d354e42c832e5450b20b318d42c834d5350b20d354f32c82ad640cb20b318d21c825e63d52209758f548825e63152209758c548827661152209d584548834e5388620d394c21882e96008620d394f208825f63551209718d544827761551209d185544825e63151209758c544823f6454d208f19153482776154d209d185534826c6550920b318d42482e860509209b99732482ad640c9208f990514823d64145209798c514825d63145209b99721482cc6348520b398e204825f63550209718d540825e63150209758c540826e62150209d984540827561150209b98b530823e6414c208f59053082766114c209d584530823e64948208f592520825e63948209758e520825f63544209718d510826d6588420ba580210825e63940209758e500826f65480209ed95200825e63d53109758f54c425e63953109758e54c426e62953109b58a54c423e64d4f108f59353c426f6254f109b18953c425f6354b109718d52c423e6414b108f59052c425e6314b109758c52c425f63552109718d548425e63152109758c548426e62152109b588548426e62d4e109b58b538423f6454e108f191538425e63d4a109758f528423e6494a108f592528425e6394a109758e528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f99454443356115110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910da580524433454905109d195414436852881109e195204425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109e980520433554c40109e596100436952840109dd95100433554440109ed9510043695244010
  | 1 => 0xc65e65d0d3197994434c6cd6210d318f990524c63d6414931cb990524c72d6414931d3d0c524c74c431493197997324c74c52cc931d3149324c69e648c531d314a314c65e63d50319b988540c66d62150319e980540c679601503197596430c65f6550c3197596320c69d640c8318f992510c63d649443197d95310c6cc624c4319dd95310c63f64540318f191500c65f63553219718d54c865e63153219758c54c863e6414f218f59053c865e63943219758e50c865e63d52219758f548865e63952219758e548863e64d4e218f59353886cc6350a21ab590328863f64542218f191508865f63542219718d508865e63951219758e544866d629512197d8d544865c63551219ed81544867860551219798e534866f6254d2197994534874c53885219798f540865d63d50219e983540867960d50218f596540872e62950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c21d3189530863e6414c218f590530865e6314c219e98053086796014c219b596420874d5390821cb95142086cc6350821d354d420874d53cc8219b59432086ad640c8219bd9521086cc63484219dd95210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500876a4254021da509500876b3254021da0c9500876b2154021da485500865f6354b409718d52d025e63947409758e51d02ad6210e409798e529025d6394a40a718d429025f63546409718d519026f62546409b189519029e63906408f997415031c53d0540c714d415031c5390140c754e43102ad6210c40d394e521034d5394840d394d521034d5354840c754f421029c6350840c754d421032e5250840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440cd90d51103344354440cdd09511033542544408f596411029e6390440cd54641103355110440cd547401023f6550040a718d401033551500409ed95401026e62153309b58854cc29d640cb308f99251cc23d6494730b318931cc26e62d52309b58b548c26e62152309b588548c27661152309d584548c2cd6210e308f992528c23d6494a30cb992528c32d6494a30d3d0e528c34c4394a30d394b328c34e524ca30a7992318c34e528c630d3948318c34e52cc2308f992544c25f63551309b988544c26d62151308f994544c31d6315130cb988544c32d621513097996434c31c5490d3097195434c31c5450d30c7152324c25e650c930a7590324c31c540c93097997314c31c54cc530c7151314c2cc624c530c7152304c2ce628c1309798c540c26e62150309b588540c27661150309d584540c25d65d0c3097594430c2cd6210c3097d9
  | 2 => 0x105481c000dc0005440f18b0000009a94a3b4000760000002bcb48d210c13c0000038e000920e80000c4df900272000000003ce000610002ae494129a21ca6540d1f74281104d0552ce2309e16a2bc15cb78220422503e9f317a3bc669b61683c4af9d140a000931f641c0000007c30840c870002c62705580000049c308002104143d0f4000274001100e256c1a8582862483818030666cf093f37a408600000001fc390181082980009104c0006791131a710000ca3ba4b0290fe20e2842c9ec0501b07500035037c5b162358750001b90000000014116e214ab1fc1ae000fc1c30a68000904a416000000000000000000033c00073009000000700000004484c00039272ca017e0000000002b0020000011a202748f29a62a0038339c02260000900007000010002500c060580100005018010040702c020140002403000070001d0000a00c0400800008010c00d00006004040000000c010240100402000000300b00801060050281c008020000a000060080500c0e0000000c0000c050400600005000000040d01c0003403004030040001808018010080a00402000030200000010008000000c000000201f020010b80d02002008030000001c0300003018020100001c0101c000000201400038010100001c080040a00805030030380b00c000240002004014070140101c00028080000301400000000100a00c0000a6f62546439b1895190e6e62942439b58a5090e3f6550c4397d954310f2f4354843d390d5210f2d4354843d350d5210e5e63947429758e51d0a5f63543429718d50d0a5f63546429718d5190a5e63942429758e5090b4d6214d42c714f4350b1d53d0842d354e4210a3f6550842c754d4210a6f6550842d354d4210a3e64947328f59251cca3f64543328f19150cca7a60d52329e583548cacd6210e32b318d428cb8f4350a329d986544ca75619513297d8d544ca5e6590d3297195434ca6c6550932e350d424ca3d6595032c718d540ca3e64150329798c540ca6e621503297597430cb1d54d0c3297594430cb1d5410c32b3588430cb1d54cc832cb552320ca5f654c832c7551320ca6f654c832cb551320cb1d5390f41ab58843d074e5394b41d354e52d074e5354b41d354d52d071d53d0b41a718d42d071d5350b41cb94942d071e53d0641ab588435065e63149419758c525069c6350941ad185425069e63905419798c505065d63141419b988505066d621414197d8d521065c63548418fd954110677655044197d8d501065c63540419b98854cc66d6215331b358843cc66e62943319b58a50cc66e62952319b58a548c71d6395231cb98a548c72d6295231c7952438c71e5450e31c7952328c69d640ca31c7950328c71e54cc6319758e544c66e62951319b58a544c66f62551319b189544c67b60551319e181544
  | 3 => 0x97000000000001b42fc400000004c8cb8160984f80196b3d22b42b09b2707b89d9d31ce7f8b69492cc6508e9681fa7e8001464024785720a00062497906338384ea9740003e83b92830c26463a080001a8eb1eb322000cd0f635246cf100038a4ac9080035a38c001220006b8320000006f87200011e3fca590b4041708a05a3046944587506e6d0e11e3262014f503f0a21880000c1b27c8a60003f6000680000000006b10c182538e68f804654c00000000534000000003500001d3ae114d881b2fa80c00000196410fa849198000c7836000198bb0c30000000000000064c6d8fb1d22402f8c817000000000158728698462f86d4ee0004320003a1182846e0000ce40c0b4001920000000000000e73c6206d40824c17155000640000a92660810c0000007bc8a8690006c0001b20000004381f0000005a9191ea0181800003279859800000458001aa12c11c5e09f0d609c9e8eb0ca0000000028a000f81870000010b800000138210a52ee174201ed000000440003767910b0e21b0000000001bc2f8001ce1ba6140010d15015104800000830000001da000e30080005e4000000d018c6288a29e000000002dc234089811482e82683b2fe1b82803c090000cf8000000d0ac19d0001bc058150001f8a41e028e000d195d0700a4d3a0f000584b99de366000000602c00007916501a29c001d0212840c60000000000021a1602810a9ab1766288792a4267048505e26e324000142f45d4000f0000208fa09e0260009b15922e7647e0d10861e08e03931047ce41ba0000081995218c20c12095154848d012d11c05cd08102b43cc179bc28803cdb9700f27c47b9640ec0009717241a7309d1781aa480d79292b82c8ec1e83be4c0ed93407a028001960b63b8398000005b0bd81c33048d089a43fa288c70893320101d02c1727fc3d9f92e25501903e0823e4000b10960005188
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x38834f00500a54030b4c05804141c90064980c15d10840151840418cd835516210c32c1ac6b14a918d0d72951438c60ebb4a819463435d0524c931c1cc82946298d0d7418953086263b2a6a1043521cd4254021a52e8192a010d48734855008692b9086a8881451cd4254440c2cc6a8c8220614635454010286ba4a49946183992528c630c1ac6b10a89850d72151434c20ebb0a81926183150624c530c18a9314609850d7418953c82263b2a6a16419294d6008620
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x283080d87990528c53180d87992528c63080d87150624c53080d87152628c130
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 5 => packedAt s5K5 (20359+((h/221+packedAt s5K5 (17928+(h % 221)*11) 11) % 1408)*11) 11
  | 4 => packedAt s5K4 (22272+((h/179+packedAt s5K4 (20482+(h % 179)*10) 10) % 711)*11) 11
  | 3 => packedAt s5K3 (1265+((h/8+packedAt s5K3 (1225+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s5K2 (243+((h/1+packedAt s5K2 (240+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x83ffffc0fffe1e0ff87f0ffff87fe07d19f3f3
  | 1 => 0xfc1f87ff0ffffff07f87f0e07f87fffee64c7f
  | 2 => 0xffe007fff07fe3ff8007ff007ff8ff83078f9c
  | 3 => 0x7ffff8003fffff800007fff0003f80fe0
  | 4 => 0xfffff800000003ffffffffff80000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x884300460104200188090123180921180891b1
  | 1 => 0x11040888242800503082104420824a60624446
  | 2 => 0x28895512435106a68445aa094d50950b058a98
  | 3 => 0x72d66624aa1d4b3b5d50881276640633b80f60
  | 4 => 0x43184438cc6193cc6666cc9c04401843d76000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeeeae8c8eeeae8c8eeeae8c8eeeae8c8eeeae8c8eeeae8c8eeeae8c8eeeae8c8eeeae8c8eeeae8c8eeeae8c8eeeae8c8eeeae8c8eeeae8c8eeeae8c8eeeae8c8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36793
namespace PEqualNP.Outside.L_meta_36793
open PEqualNP.Outside.L_meta_36793.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x111500028d763169d5401b0000ccd1e00817b91285b801e0400a586402600183ae6a219343689480487c5ba0601c302a0022b289493c6240b964660e002639e804e181810110040002a004801008700263c180017fd50057f54017f95005fd54015f55005fc5401ffd4c07fe5301ff54c07fc53017fd0c05fe43017f50c05fc4301ffd4803fe5201ff54803fc52017fd0803fe42017f50803fc42007fcc803fe32007f4c803fc3201ffd4407fe5101ff54407fc51017fd0405fe41017f50405fc41007fcc401fe31007f4c401fc3100ffc8401fe21007f48403fc2101ffd4007fe5001ff54007fc50017fd0005fe40017f50005fc40007fcc001fe30007f4c001fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a200cff1951001df8ca880337c65440073e32a200bffd911005dfec888003bf64440015fb22200bff99110015fcc88802ffd64440177eb22200bff19110015f8c88802fbc64440055e322200bffd511005efea88802ffe5444017feaa2200bdf5511005ff8a888003ff63440017fb1a2000f7d8d10005bec688003fe63440137f31a2000ff58d10005fac688003fc63440137e31a2000f718d10005b8c688033ff5344019ff29a200cff54d10067f8a68802fff4344017ff21a200bff50d1005ff88688003ff62440017fb122000fbd8910005dec48802bfe62440037f3122000ff58910005fac48802bfc62440037e3122000fb1891000dd8c488033ff5244015ff292200cff54910057f8a48802fff4244015ff212200bff50910057f88488003ff3244015ff1922000ff4c910057f86488033ff5144009ff28a200cff54510027f8a28802fff4144009ff20a200bfd9051005ffa828802ff54144009fe20a2000ffcc510027fc6288003fd3144009fe18a200affc8510027fc4288003fd2144009fe10a200cffd4110067fca088033fd5044019fe282200bffd011005ffc808802ffd4044017fe2022000ffcc110007fc6088003fd3044001fe182200affc8110007fc4088003fa2044001fe9022000fe48110057f84088013ff1044009fd8822000ff84110007ec2088013ff65040097fb282004ff9941001dfcca080137e65040073f3282004ff5941003dfaca080137d65040013eb282004ff19410025f8ca08013ff64040097fb202004ff99010015fcc808013be64040055f3202004ff59010035fac808013bd64040015eb202004ff19010025f8c80801bff540400dbfaa02006ff95010037faa80801b7d540400dfe2a02004ffd8c10025fec608013fe63040137f3182004f798c10005bcc608013fd63040017eb182004f758c10005bac608013fc63040097e3182007ffd4c1003ffca60801ffd530400ffe2982006ffd0c10037fc860801bfd430400dfe2182004ffd8810025fec408013fe62040037f3102004fb9881000ddcc408013fd62040017eb102004fb58810005dac408013fc62040097e3102007ffd481002ffca40801ffd520400bfe2902006ffd081002ffc840801bfd420400bfe2102000ffcc81002ffc6408003fd320400bfe1902004bf98410027fea208013fe5104009fea882004ff14410027fe8208013fe4104009fea082004ff10410027fe6208013fe3104009fe9882004ff0c410027fe4208013fe2104009fe9082004ff08410045fcc00801fff500400fff2802007ff5401003ff8a00801bff400400dff2002006ff50010037f88008003ff3004001ff1802000ff4c010007f86008017ff2004001ff1002000ff4801002ff84008013ff1004009fb8802004ff84010027f42008013fd1004001fa8802004fe44010
  | 1 => 0x7ef2148003ff10a4001ff48520007da4290007fc21480037fb024013ffd412009ffca09004ffd5048027fe2824012ffd0120097fc809004bfd4048025fe2024000ffcc120007fc6090003fd3048001fe1824001ffc812000ff64090007fe2048001f71024001ff0812000fd84090007f82048009ffb2e2004bfd9710027fccb8800efe65c4009feb2e2011bf59710027f8cb88012fc65c4009ffb262004bfd9310027fcc98800afe64c4009feb262010bf59310027f8c988012fc64c4021ffaa62010dfd5310087fca988043fd54c4021beaa62010ff15310027fec788012ff63c4009ff31e2009bf98f10027fac788002fd63c4009fe31e2004bf18f1008ffea788047fe53c4023fea9e2011ff14f10087fe8788043fe43c4021fea1e2010ff10f10027fec588012ff62c4009ff3162001bf98b10027fac588002fd62c4009fe3162004bf18b1008ffea58803ffe52c4023fea96200fff14b10087fe858803ffe42c4021fea16200fff10b10007fe658803ffe32c4001fe996200fff0cb10027fea388013fe51c4009fea8e2004ff14710027fe8388013fe41c4009fb20e2004ff50710087ea8388013fc41c4009ff98e2004ff8c710027fa6388013fc31c4009ff90e2004ff88710027fa4388013fc21c4023ffa862011ff9431008ffaa188047fc50c4021ffa062010ff90310087fa8188043fc40c4001ff9862000ff8c310007fa6188003fc30c401fff9062000ff88310007fa418803ffc20c401dffb2c200ebfd9610077fccb0800efe658401dfeb2c200ebf59610077f8cb0800efc6584011ffb242008bfd9210047fcc90800afe6484011feb242008bf59210047f8c90800afc6484011ffaa42008dfd5210047fca908023fd5484011beaa42008ff15210007fec708002ff6384001ff31c2009bf98e10007fac708002fd6384001fe31c2009bf18e10077fea70803bfe538401dfea9c200eff14e10047fe8708023fe4384011fea1c2008ff10e10007fec508002ff628401bff3142001bf98a10007fac508002fd628401bfe3142001bf18a10077fea508037fe528401dfea94200dff14a10047fe8508037fe4284011fea14200dff10a10007fe6508037fe3284001fe994200dff0ca1005dfac30803bff5184009ff28c200eff54610027f8a308023ff4184009ff20c2008ff50610027f88308003ff3184009ff18c2000ff4c610027f86308037ff2184009ff10c2000ff48610027f84308012fe608401dffa84200eff94210077faa10803bfc5084011ffa042008ff90210047fa8108023fc4084001ff9842000ff8c210007fa6108003fc308401bff9042000ff88210007f44108003fd2084001fc904200dff08210027fe2108003f71084009fd884200cffd9510065feca880037f65440013fb2a200cff9951001dfcca88033fd65440197eb
  | 2 => 0x300c7fea41805bfe520c031fea906016ff148300bffe841805bfe420c02ffea106016ff1083004ffe6418027df320c013ff1906009ff4c830007ba6418027fc320c013ffb086009ff98430025fcc218027fd610c0017eb086009ff184300c7fea218063fe510c031fea886018ff144300bffe821805ffe410c02ffea086017ff1043004ffe6218027fe310c001ef1886009ff4c43004ff86218027dc310c02dff9086000ff88430007fa421805bfc210c0337f3006018ffd40300c7fca018063fd500c031fe2806017ffd00300bffc801805ffd400c02ffe2006009ffcc03004fbe6018027fe300c013fd1806009ff4c030007ba6018027f9300c02dff9006016ff080300affecb10056ff658802bff32c4003bf996200affacb10056fd658802bfe32c4003bf196200a7fec910052ff6488029ff3244002bf992200a7fac910052fd6488029fe3244002bf192200a7fea9100537f5488029ff2a44014ff552200a6faa910053fc5488001ffb1c4000bfd8e20007fcc710026fe6388001feb1c4000bf58e20007f8c710026fc638802bffa9c4015ff94e200affaa710057fc5388029ffa1c4014ff90e200a7fa8710053fc43880037eb144001ffd4a2000ffca510007fd5288003fe2944001ffd0a2000ffc8510007fd4288003fe2144001ffcca2000ffc6510007fd3288003fe1944000ffd8620007fcc310012fe6188001feb0c4000bf58620007f8c310057ff518802bff28c4015ff546200aff8a310053ff4188029ff20c4014ff506200a7f88310003ff3188001ff18c4000ff4c620007f86310007ff2188003ff10c4000fb8862000ffa4310007fc2188003f610c4001bf982200affea110057fe508802bfea844015ff142200a7fe8110053fe4088029fea044014ff10220007fe6110003fe3088001fe9844000ff0c22000ffe4110007ef2088003fd9044001ff0822000ff0411004fff65480277fb2a4013ff9952001dfcca9004ffd65480277eb2a4013ff1952001df8ca9004bff64480257fb224012ff99120015fcc89004bfd64480257eb224012ff19120015f8c89004bff5448025bfaa24012ff95120097faa89004b7d5448025fe2a24000ffd8d20005fec690003fe63480137f31a4000ff58d20005fac690003fc63480137e31a4013ffd4d2009ffca69004ffd5348027fe29a4012ffd0d20097fc869004bfd4348025fe21a4001bfd892000ffea490007fe5248003fea924001ff1492000ffe8490007fe4248003f72124001ff50920097da8490007fc4248003ff9924001ff8c92000ffa6490007fc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4004bf1852009ffea29004ffe5148027fea8a4013ff14520097fe829004bfe4148025fea0a4012ff10520007fe6290003fe3148001fe98a4000ff0c52000ffe429000
  | 3 => 0xf32c601eff596300f5facb1807bfc658c0077e32c6019ffd92300cdfec918067fe648c0057f3246019ff592300cdfac918067fc648c0057e3246019ffd52300cefea918067fe548c033feaa46019df552300cff8a91806efd638c03dffa9c6009ff94e300f7faa718027fc538c033ffa1c6009ff90e300cffa8718027fc438c001ffb14601dff98a3000dfcc518003fd628c0017eb14601dff18a3000df8c51807bff528c03bff294601eff54a300eff8a518067ff428c03bff2146019ff50a300eff88518027ff328c001ef994601dff8ca30007fa6518003dd328c013fe1946000ffd8630007fcc318012fe618c001feb0c6000bf58630007f8c31807bff518c03dff28c601eff546300f7f8a318067ff418c033ff20c6019ff506300cff88318027ff318c001ff18c6000f78c630007fa6318027fc318c001ee18c601dffc8630007fc4318003fd218c03bfe10c6009bf982300f7fea11807bfe508c03dfea84601eff142300cffe8118067fe408c033fea046019ff1023004ffe6118003df308c013fd984601dffc82300eff84118073ff654c0397fb2a6000dfd9530004feca98073fe654c0077f32a601cff595300e5faca98073fc654c0077e32a601cdf1953001cf8ca9806fff644c0377fb226000efd91300057ec89806ffe644c0057f322601bff591300ddfac89806ffc644c0057e322601bef1913001578c89806fff544c037bfaa2601bff951300dffaa89806f7d544c037fe2a2601cffd4d3004ffca698073fd534c013fe29a601bffd0d3004ffc869806fde434c037fea1a601bf750d3004ff88698003ff624c0017fb12601aff9893000dfcc498003fd624c035fe3126001bf189300e7fea49806bfe524c039fea92601aff149300dffe849806bfe424c037fea12601aff1093004ffe649806bfe324c001fe9926009ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298012fc614c039ffa8a601cff945300e7faa298073fc514c037ffa0a601bff905300dffa829806ffc414c013ff98a6000f7cc530007fc6298003fd314c001ee98a6009ff0c5300d7fe4298003fe214c001fe90a601aff085300e7fea098073fe504c039fea82601cff141300dffe809806ffe404c037fea02601bff1013004ffe6098027fb304c001ff1826000f78c1300d7fe409806bfc204c013ffb286009bfd943004ffcca1800efe650c013feb286018bf5943004ff8ca18026fc650c013ffb206009bfd903004ffcc81800afe640c013feb206017bf5903004ff8c818026fc640c02fffaa06017dfd50300bffca81805ffd540c02fbeaa06017ff1503004dfcc618027ff530c013ff2986009ff54c3004ff8a618027ff430c013ff2186009ff50c3004ff88618027ff620c013ff3106001bf9883004ffac418002fd620c013fe3106001bf188
  | 4 => 0x807ff4288403ff2144201fb90a2100ffa8510893ed4288403fe2144201ffcca2100ffc6510807fd3288403fe1944204bf98621027fea310813fe5188409fea8c4204ff14621027fe8310813fe4188409fea0c4204ff10621027fe6310813fe3188409fe98c4204ff0c621027fe4310813ef2188403fb90c4204ff08621027e84310813ff6088409ff3044200bf98221027fac110802fd6088409fe3044225ffd422112ffca110897fd508844bfe2844224ffd0221127fc8110893fd4088449fe2044201ffc822100ff84110807ec2088447ffb2a4223bfd952111ffcca9080efe6548447feb2a4223bf5952111ff8ca9080efc6548445ffb224222bfd9121117fcc89080afe6448445feb224222bf59121117f8c89080afc6448445ffaa24222dfd5121117fca89088bfd5448445beaa24222ff15121007fec690802ff6348401ff31a4209bf98d21007fac690802fd6348401fe31a4209bf18d2111ffea69088ffe5348447fea9a4223ff14d21117fe869088bfe4348445fea1a4222ff10d21025fec490807ff5248403ff2924201ff5492100ff8a490807ff4248403ff2124201ff5092100ff88490807ff3248403ff1924201ff4c92100ff86490806ff6148447ffa8a4204ff9452111ffaa290813fc5148445ffa0a4204ff90521117fa8290813fc4148401ff98a4204ff8c521007fa6290813fc3148403ff90a4201fdc8521027fc4290813ee2148409fe10a4204fb0852100fe84290803ff60484017fb024200ff98121007fac090803fc60484017e3024223ffd412111ffca09088ffd5048447fe2824222ffd0121117fc809088bfd4048445fe2024201ffc812100fde4090807fc2048413ffb2e6009bfd973004ffccb9800efe65cc013feb2e6021bf5973004ff8cb98026fc65cc013ffb266009bfd933004ffcc99800afe64cc013feb266020bf5933004ff8c998026fc64cc041ffaa66020dfd5330107fca998083fd54cc041beaa66020ff1533004ffea798027fe53cc013fea9e6009ff14f3004ffe8798027fe43cc013ef21e6009ff50f30107ba8798027fc43cc013ffb166009ff98b3000dfcc598027fd62cc0017eb166009ff18b3000df8c598087ff52cc03fff2966021ff54b300fff8a598083ff42cc03fff2166020ff50b300fff88598027ff32cc013ff1966009ff4cb3004ff86598027ff61cc013ff30e6004bf9873004ffac398002fd61cc013fe30e6021ffd473010ffca398087fd51cc043fe28e6020ffd0730107fc8398083fd41cc041fe20e6009ffcc73004fbe6398027fe31cc013fe98e6000f74c73004ff8639807fff21cc001ff10e6000ff487300fff84398087ff50cc043ff2866021ff5433010ff8a198083ff40cc041ff2066020ff50330107f8819807fff20cc03ffe106601effd96300f5fecb1807bfe658c0077
  | 5 => 0x8231027f8c1188bbff508c45dff284622eff54231177f8a1188b7ff408c45bff204622dff5023116ff881188b3ff208c459fe104622bffd953115dfeca988affe654c4077f32a622bff5953115dfaca988affc654c4077e32a622affd9131155fec8988abfe644c4057f322622aff59131155fac8988abfc644c4057e322622affd5131156fea8988abfe544c455feaa2622adf55131157f8a8988afff534c413ff29a622bff54d3104ff8a6988abff434c413ff21a622aff50d3104ff88698803ff624c4017fb126229ff9893100dfcc498803fd624c453fe3126201bf1893115ffea4988a7fe524c457fea926229ff14931157fe84988a7fe424c455fea126229ff1093104ffe6498803df324c453ff1926200ff4c931007ba6498827fc324c457ffa8a6204ff9453115ffaa298813fc514c455ffa0a6204ff90531157fa8298813fc414c413ff98a6209fdcc531027fc6298813de314c453ff90a6204ff08531007fec098802ff604c401ff3026200ff58131007f8c098802fc604c457ffa82622bff9413115ffaa0988affc504c455ffa02622aff90131157fa80988abfc404c453ff9026229ff08131027feca18812ff650c409ff3286203bf99431027faca188a2fd650c409fe3286204bf19431027fec818812ff640c409ff3206202bf99031027fac81889efd640c409fe3206204bf1903113ffea81889f7f540c44fff2a06227ff5503113efaa81889ffc540c4137f3186209ffd4c3104ffca618827fd530c413fe2986209ffd0c3104ffc8618827de430c413fea186227f750c3104ff88618813ff620c409ff3106201bf98831027fac418802fd620c409fe3106204bf18831147fea41889bfe520c451fea906226ff1483113ffe841889bfe420c44ffea106226ff1083104ffe6418827fe320c413fe9906209ff0c831025fcc218813ff510c409ff2886204ff54431027f8a218813ff410c409ff2086204ff50431027f88218813ff310c409ef9886204ff8c431027ec6218813fd310c409ee9886209fd4c431027fe4218813fc210c409ffb006204ff98031005fcc018813fd600c4017eb006204ff18031147fea0188a3fe500c451fea806228ff1403113ffe801889ffe400c44ffea006227ff10031137fe401889bfc200c409ffb2c4204bfd9621027fccb1080efe6588409feb2c4225bf59621027f8cb10812fc6588409ffb244204bfd9221027fcc91080afe6488409feb244224bf59221027f8c910812fc6488449ffaa44224dfd5221127fca910893fd5488449beaa44224ff15221027fec710812ff6388409ff31c4209bf98e21027fac710802fd6388409fe31c4204bf18e2112ffea710897fe538844bfea9c4225ff14e21127fe8710893fe4388449fea1c4224ff10e2100dfac510807ff5288403ff2944201ff54a2100ff8a510
  | 6 => 0x5fe2a26401bfd8d3219ffea699027fe534c867ef29a6433ff54d3219fbaa699027fc534c865ffa1a6409ff90d32197bc86990cbfd434c865eea1a6409ff10d3200dfec499007ff524c803ff2926401fb9493200ffaa4990cfed524c803fe2926401ffd093200ffc8499007ee424c803fea126432fb5093200ff88499007ff324c813f79926401ff8c93200fbc6499007fc324c803ee1926401fb0c932007fec299002ff614c801ff30a6400ff58532007f8c299012fc614c867ffa8a6433ff9453219ffaa2990cffc514c865ffa0a6432ff90532197fa82990cbfc414c803ff90a6401ff08532007fec099002ff604c801ff3026400ff58132007f8c099002fc604c867ffa826433ff9413219ffaa0990cffc504c865ffa026432ff90132197fa80990cbfc404c803ff9026401ff0813204ffecb98826ff65cc413ff32e6203bf9973104ffacb988c6fd65cc413fe32e6209bf1973104ffec998826ff64cc413ff3266202bf9933104ffac9988c2fd64cc413fe3266209bf19331187fea9988c37f54cc461ff2a66230ff55331186faa9988c3fc54cc413ffa9e6209ff94f3104ffaa798827fc53cc413ffa1e6209ff90f3104ffa8798827fc43cc413ffb166209ff98b3100dfcc598827fd62cc4017eb166209ff18b3100df8c5988c7ff52cc45fff2966231ff54b3117ff8a5988c3ff42cc45fff2166230ff50b3117ff88598827ff32cc413ef9966209ff8cb3104ffa6598803dd32cc413fe1966231ffd4731027fca3988c7fd51cc409fe28e6230ffd0731027fc83988c3fd41cc409fe20e622fffc8731027f84398827ff60cc413ff3066200bf9833104ffac198802fd60cc413fe3066231ffd433118ffca1988c7fd50cc463fe2866230ffd0331187fc81988c3fd40cc461fe206622fffc833117ff84198813ff658c4097fb2c6204ff9963101dfccb188137e658c4073f32c6204ff59631175facb188137d658c4013eb2c6204ff19631025f8cb18813ff648c4097fb246204ff99231015fcc918813be648c4055f3246204ff5923116dfac918813bd648c4015eb246204ff19231025f8c9188b7ff548c45bbfaa4622dff9523116ffaa9188b77d548c45bfe2a4622abf58e31177fea718827fe538c45dfea9c6209ff14e3116ffe8718827fe438c45bef21c622dff50e3116fba8718827fc438c409ffb146204ff98a3100dfcc518813fd628c4017eb146204ff18a31025f8c5188bbff528c459ff294622eff54a31167f8a5188b7ff428c459ff214622dff50a31167f88518827ff328c459ff1946200ff4ca3104ff86518812fe618c409ffa8c6204ff94631027faa318813fc518c409ffa0c6204ff90631027fa8318813fc418c409ff98c6204f7cc63104fee6318813ff218c409fe10c6204ffd8231027fcc118802fe608c409feb046200bf5
  | 7 => 0x500100100200200100300100000000400000100300000100000400a00000300100200000000000100200800100000000000500600000800100200100800100000400000600100100100000000300000900700302100000000200000000000400100200000100300000000000100000400100100000000000600000100300000000100100400100000000200500000400300500000100400100100000200000000200300000300200600000200100300000800100200200200100100000100100100000500100000000200100000100800000100000000300000200500000100600200100100f00900400400000300200600000300100100000200000000800000000100400000000000100e00000a00000300500100200000000900400400000100000100000000200500100100100100000000000000100000100000300300100000000c00100300000a00400200000100100000100000100000600000100000400000400500100b00100100000100100000400200300000000200500300100000000300500300200100200000000000300100100600200100000300000000300400000300300000000100000000000000000100300d00000000000000200000000600000000500100000000000000300000000400100000100000000000200100000200000200200000200400200400000300300000000000000400200000000400000000200100000500500300000000004ffecb99026ff65cc813ff32e6403bf9973204ffacb990d6fd65cc813fe32e6409bf1973204ffec999026ff64cc813ff3266402bf9933204ffac9990d2fd64cc813fe3266409bf193321a7fea9990d37f54cc869ff2a66434ff553321a6faa9990d3fc54cc8037f31e6409ffd4f3204ffca799027de53cc813fea9e6435f754f3204ff8a799027ff43cc813ff21e6409f790f3204ffa87990d3dd43cc813fe21e6401bf58b3200ffea599007fe52cc803fea966401ff14b3200ffe8599007fe42cc803fea166401ff10b3200ffc6599007de32cc803f71966401ff0cb3200fb86599027ff61cc813ff30e6404bf9873204ffac399002fd61cc813fe30e6435ffd47321affca3990d7fd51cc86bfe28e6434ffd07321a7fc83990d3fd41cc869fe20e6401ffc873200ff84399027ff60cc813ff3066400bf9833204ffac199002fd60cc813fe3066435ffd43321affca1990d7fd50cc86bfe2866434ffd03321a7fc81990d3fd40cc869fe2066401ffc833200ff841990cfff654c8677fb2a6400dfd9532004feca990cffe654c8077f32a6433ff5953219dfaca990cffc654c8077e32a6433df1953201cf8ca990cbff644c8657fb226432ff99132015fcc8990cbfd644c8657eb226432ff19132015f8c8990cbff544c865bfaa26432ff95132197faa8990cb7d544c86
  | 8 => 0x1c8000000320000000000000b2241214000000048ca2800000036c00000000000000000000000000049000013e150000b0e000ae03be0000000000000ac61a53e00019c4e6000a32000516000000000000896000cde1200009042e651c3024cc00058a0000008100920000000000000004f49c40005020000006ac00000053a1849342e24b64d800000000026e0000008509a60004960a6000618954726000000000c326060000000000d253c0000000006300009648300000380000000000000000000000000000000008b6000000000b5698a00016800000000000078a0001cc00075cbc8708ad4000364b388822120003942c2000000000000000000c7eaec8fc646000000000000000000000000ac071400043600000072400000000063800017400000000000056c000b008c83d82406fc8a4564876c001f80007e8000000000b4e0000002aacaa0000007ec0007d80001e07dc68ebf8000b8a2b620200018c672b6269490274e210a88000bc600067629c5a8122a78a46000a8c000c7ca7c000b243301eaba20e04580000000000000000006e2c5800000000099410e0000009200000000000b40000000005c8000980000c6200000091a0005c0000000000000000000b78000000000b443320000000000008a64d0b200000000000000000003fc000b5a5ba00039a00000045472c5f03f89c80005e2406000000000602ce400049ea12000a6600009e000000000000000000af238c0003928d60000000000000000000000000001dc0ce51800000000000000000000055e4aa1a051e4fc75800000050000000000080859000000000013a0000000003babb0ae60000003700000006bc000a38000310000000000000000b46ab8356000c2a00092a9cc0000009a42a00bc8a25bc6e600037c38a0000f80d80006ee7c4bcc0005ea8c00000000001f4000754000000000360000000b729403122c60000000009880009b600059c00000083e00016c0001e22e400073800000000300100000100100200a00000100000400200200100000000900100100000000000000000800000100000000000000000000100000100100000300000200000000000100000200000000000000000000e00b00000100700100700400000000100300000000000100000200100400000000200200000400400400100000100000000000000500000000200200000000a00400300100000400100000000000000100300000000000000000700000100000100000000000200200000300000700300100100000100700000200300300000000000000100000300200000200100000000000000200000000000500000200000000300200000600100200400000200000000000100000100000000000300a00200100100000100200000100000000200000000000700
  | 9 => 0x900000000003ac0000004768ae000000000788a148ea55a36ebd21fe2cc0009d0942ae2b7000091881c0005fa0005a20009460009320009364e29d63d40008a035410600000000000000000000093e1a200004063a0000000000004820005380000002f800012c0000002ae000a3000000000000000000000000002a00014a0009f60002980724840000009ca89200000000000000000000023e2b82cac280040008dc0000e200000000000043e00056200000000000060a2a277a0060000000000000000007623dc88e23a000000000000000000ade4240000000000000000009260008d00000ee000000000000be295ea440000000000000000f60000000000000007c200000000000000065826a0eac248045de5fcc061d61c0cce86c65a0000009f8000922cb06aa3ce9726b8056a04b32a6a85a0005da00000061c0008f0378000ab40000000000001040c600000000000000000000029400000000028a000000000000000a24000000000b30000014000000000000000756000000000000b6c000400ad200000000045e0000000008f4b9642a1929600000004beaea00000000000000066809a176088000000af800000000054e00079600000098400000000000000040e9f40007b60423ea7acb0a000000000000c420000000007520008bc0000000000006520000000000004b00000000004e486889e29aa585960005428ec000ca847a02e000000b8691689a5a406083a97455cbfe036000956000000000000000588adc440000344c3a0000003f40003e400000095200000000000000000000000087e162000000000a020000001ce0002d20000000000000007320006820002d6c682c49104f24682c8000000434000000000000000a3cb68000000000000842000000000000000000000000a204b8706b401360cc00000000006c0000000008f86b0180764000a64000000000b3e0000000000620008b200000025a4dc000000c4007c00000000000000000000013400000000057000000000000095c00000000000000018e1f6244bb800084a0007e0000c08bf40000b0c6e1b800090e00046aaa0b1c0006448becb267a924272000000000000002000000000000000000a809000000000000000000000004720004a200010a00058c8000000000004a600000000081e0000000000000006b400000049a00079865cb5e68caac88030057870005e0005b20002841887d07deae46920000005368e428e7bead600066a85e5dc7a817a6780da0000005be5ec0000000000000006ea3caa7e83c996000000018b6a78e00064e000000116000000000000a541eeba6000000000000000466000000000000000c5c000000000000000c4a000000000000000000cd00000701724ce50400000057c
  | 10 => 0x24c20001f0ba89e400000091c0000001b295a3f29c0c5e00096e0000008ba00098e15e8ac0001ba0e800013800000000000000000045254440800013c00012a0009e28a812e0000000000000200000004c64a8a1e0000007f60000004fa322b7481673a3bc16400028800000069e5e8000000000080000000000000000662000000000000a960000000006dc0000000000000000000006120000ae8260000006f40000005269b441a000078b140004ea0003c856021c6cc000276be0b66000b4c000000000cee000ac8000c9677e00044e00000091200090a000000000000b480007660000000000000b80a40000005b80000ba4984ae0001da2e8b9a4040007f20d671c3801c2860000000c500000000000006265c600079487ab1800000000069a000000000000000000000366000000000c0a246a9200016e8528ca6220005ee59a000cb40002ea744a1a5280000f200070c0002084ecaf0bbe582050000000aa8a2c000000000c740000009f21d2000a405a65b6000000000b5863c000000000000000c66a0c9f0510000a0855600000058e000000000052226000000bf0bd6bba000b101fc00000017ca68c9e0000000000000009d2c70000730000000000000000196c8c000c3e000822258000b7cb023a000004e0000000000000000000000000007466c82821ae9a00aa00000000000045a000890ac452493a00000095851200000000000000098c000000b52000000000000000270000b5000000000035017000000014c00000000000044ca107760264c80000007c8000bf20002ac1a62281489667cc494bd00000002fc000000856ca00000009c20003c00000005e4000000664000000000a36b7a000000928aaaaf60008869388c2000000000382a1c266000000c20aa40008aa000236000000420a62cca9060000000007420000000000e60000000000000000000000340000000000000001561280005520006328647b83ae0000000000003760009d400000000058675a0000000000000000000007bc232ada08eb060000be22484ebee000c9c00005c0002520009b82a68740003d60008c683878c000432110000000000b2800000000027abb605a00000011c256000b8c0003400001deb4a0005ca00000068082a102c6ccdc4ee5ce33c4805b00000000000005b46d003e000000000000000000000854c864640005e600077230c0c2000000acc3b0000000000342000462ab2000000840534000000cda0000006ae86226c33e000000000000000000afe00000000000000000000000000000000032843c0008d43e000030e0009ea000262c1c3fa000000cc639800048a962b803f6084000000000000000000000000000000a9e09670e00000000000000000084800000000000000039032a0009aa000000000b045c40000000000000
  | 11 => 0x112386000000000686000000c1e26416a00000033600077c5143b4000000000cc8000b8800000008a0000000000000000000002925a08b07c601000000000000000000000000000000015a00000065e1a80000005060000000000006200009ba000000000000b82550c6487c00088a00000080c0002fe00000086ec1247ca2e000348000716000cbc85834cb2e7f06c00000dcbd43749ac2c00000007e4000ad0000abc0006980007ee81800000000097e0000b2338bec4da000a9073684c0008de00069600000000000000015810ca8e430000b5c7d2000000000b342de0000002800000000002b235ca48000000000b3a00066c000000728000000000000000a7275ea4221808cb2c00033a00077049cbdc0000680000000ca00000000006ab08c9000060c0005f4000000bae4e80000000640003de00000000000000000081400000000000000021407abca7920000008026da0000008f26fec02cacc804a026054a094c1a48e47047e4a46b66d800000049250ecc400083600000052227eab04ca2e03f000000000000023446c0000a800000068800000052000000000080e0000000d46140000000000001ec9b0ba48f60000000000000006c2000000000c5a00031e0004f600078600070aabe0000009da0000000000009fc0000002303aa0000000000000000000001320002500007d400000000000002c00000000000000000086aaee76cc8a66e03abb4278000aa60000006427ae2543d2ce28ee6c4a747401fa00001e894afc9862dc00096c62865400016689839c88411473ec84888000000540000000000a5a0000004269a8000846624c3806e24c0fe314c14000a00000cd81a4438296cbe11e71813000000038e222bea000000c9a0000000000000004183da000000a3a00000010822054cbe67347b44b43e860e000000b90c980000000000003160000000000000000000000003960000009ae000204000b369be8fa0000000000000000000007ea000b3cb26690000362bdeb2a6e07c00005320004f8000760c94000000000c3031a00056a000000000914000000000a8a000598000a220a00000000004de0000007a00002be0005f632400000000000064076ea848cc0000000d00000000000facea0000000000008b8aa2242a4cc04022000a60000000456cae80661e0003720000000000000000000000000000000006ba0003263fe04625e0000007d60002b4576000000000000ab6000580000000670066a6e3c671a00024e8e0c16000a76cd6000000000000000cc000041c8e63a823cc2600040c0000000000000007f40007020000000003a40000007ba7ca44451a1525928d881a17800000010069cb6463423800020689c66046ebbc000000000a9400037e00ea6cc720001aa0000000000000000000de000012000c480009a
  | 12 => 0xcc20000000000005940000000004228da00017e0002f2000000000bac000000000000000000000000268c220000fc00076a74c0000006e4000ccc000be800000000000096a0000000000000005e02d0000000748000000c4c0000000c40000000000000003e6000b941b6000000000000cd200000027c4e000000000000000000022e24ac10bfc2ce4f02f4000000000000978790ca6cba000bb200000000031800056e0004d222abf6000000000566000000000190000b76ca20005cc00082c0007a63c2000000af468400a0982f600000012479e000000000186000000b8404c00000092e64c2a4000c880000000000007da000000000000a52000ce057e00000000000090c0000007fa6740000000007feae8000784704000c340000006a2000a7a00008203200000000011a7120006e8000000a9a6f05f844a0000000003ccc3601a0006f6000ace000000b160000003e21c65ae04a00003ca2a0000002b03a600000000000000079c1f2a3e990baa00099a9e862aa0a024000000200c6047475042e00014e63e414a060000009ee0000749dc9d819a1e4304000b9ca4a5d60000000003c459e0003b6c520000000e42da43a97a448000b1a0000004d60000009440006d40000001544883b22d841e0000000000007a4c2e2ec1820000000000004fe00000048600000000000099e64a0000000001ac00000087052c2ba0000008fea500000008b400000000072e000ce80000001b40001980160000000000008242ee0000000f41600000000000000006d60009701bc6ca0000000000000000000000005d80000009300000008340c8ac600025c0000000000006fa0006a80004c0000000000000000000000000b7ecd40004100002fa000000000000000000000000ce6000720608000000c92000a16000368000b1e00000000000000074a00000094eb6000037a91e000000b5400009c85c1e8ba0000000c5618a00001c8664d435a000306402000530000000000000000568000afa20c000000bc2000000000000000000000000000c78c46c2c5d422c000bfa00000000040a000000ca40000000006f2000000bce0000000541c4008c825544162bc000a26216000a700000007e6058000044000000bda048844000000000000000000000c8e00068a2a8000000000000000000950000000000a860004b2000b981d00005740000ec7e2820b0cc4e9987821d85c26f800045c000000000a184467b200067c0009fe4601ca44200000000019e000000a829820006c600000000000000050caae0009fa6de000ac2000610cec000c18a342740000000000000007746040000000001e67aab9e0003344bc72ab8e000000000000c5400000065000000000099c9c635e00000000000000088c36a00082e000a560000001b04ba2d494c000000000
  | 13 => 0xad800082834600071e73c6ec45042832c00015c72293c00c126c4457234a6ce9680008c45fe3b800000000000000097caca0f00000000000000000000005d200062c000000000000c7a1beb4228c21a00000020eb125d054621e14420a80abe47fc6d2bc0118c0ebc432e6be0008d2c76290c3c000780cb80009080006a43527f89bc0000000005aa000a9caba6b2000000000000000000000bd80006a000007e0000006160000003d0000a9881257a030000000000000c6a00000000000000008629e0000000000000000004ac00000000062e0003080760000000000000000008720000000006a60000000000008ce00087800000055800067e0005f2832b92a5e14634eb6e76831c0b642c0a27109e03ee0000000004c400000047830a0000003580000000009760000000000000000000000000006361943ec0000000000008e894a0007b099200000050a52e6005488e200079aa0e2489e67ce000948c0c000000656000000000cb60000007a266652a9ec1d439ea5c0280000000000009de0000000009ce3a200038492c6482f03880000000000000007780000000005ac000508000000a4e9b20c01420000002860000000005840000000000000000000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc5358810006ef4358810006ee4358810006ed4358810006ec4358810026ef7158810026ee7158810026ed7158810026ec7158810026ef5158810026ee5158810026ed5158810026ec5158810026ef4158810026ee4158810026ed4158810026ec4158810026ef3158810026ee3158810026ed3158810026ec315881002eef7058810006ee7058810006ec7058810006ef5058810006ee5058810006ed5058810006ec5058810006ef4058810006ee4058810006ed4058810006ec4058810026ef1058810026ee1058810026ea1058810026ed1058810026e91058810026ec105881004cff76cc810024fe76cc810004fd76cc810024fc76cc8101ae7e65cc8100067d65cc8101a6be64cc810006bd64cc81004ede63cc810006dd63cc81000eee62cc810006ed62cc810004ff764c810024fe764c810004fd764c810024fc764c8100057f754c81003d7c754c81019e7e654c8100067d654c810196be644c810006bd644c81004ede634c810006dd634c81000eee624c810006ed624c810005f7714c810025f4714c810004fd76cc01010e7e65cc0100067d65cc010106be64cc010006bd64cc01004ede63cc010006dd63cc0100feee62cc010006ed62cc010004ff768c01004cfd768c0100f67e658c0100067d658c0100cebe648c010006bd648c01004ede638c010006dd638c0100eeee628c010006ed628c010025f6718c010005f5718c010004ff764c0100057f754c01003d7c754c0100e67e654c0100067d654c010005bf744c010035bc744c0100debe644c010006bd644c01004ede634c010006dd634c0100d6ee624c010006ed624c01004cff760c010024fe760c010004fd760c010024fc760c0100c67e650c0100067d650c0100bebe640c010006bd640c01004ede630c010006dd630c0100b6ee620c010006ed620c010025f6710c010005f5710c01006cff7688010024fe768801000cfd7688010024fc76880100ae7e65880100067d65880100a6be6488010006bd6488010006de6388010006dd638801000eee6288010006ed6288010025f67188010005f5718801006efa608801006cff764801009e7e65480100067d6548010096be6448010006bd6448010006de6348010006dd634801000eee6248010006ed624801006efa6048010025f77644010006f77644010004f776440100077775440101b7747544010027766544010027756544010007b774440101c7b47444010026f76444010027b664440101c6f56444010027b56444010006b564440101c77754440101c7755444010007d77344010007d47344010027d66344010027d56344010007e77244010007e47244010027e66244010027e56244010025f77044010027f370440101bef66044010027f260440101b7f250440101b7f15044010007f23044010007f13044010
  | 1 => 0x8c10026df4198c10026de4198c10026dd4198c10026dc4198c10026df2198c10026de2198c10026dd2198c10026dc2198c1004ede7098c1004edc7098c10006df5098c10006de5098c10006dd5098c10006dc5098c10006df4098c10006de4098c10006dd4098c10006dc4098c10006df2098c10006dc2098c10026df1098c10026de1098c10026dd1098c10026dc1098c10004ff7558c1001cfe7558c10004fd7558c1001cfc7558c10004ff7458c10014fe7458c10004fd7458c10014fc7458c100067f5458c100067d5458c10026df7358c10006df5358c10006de5358c10006dd5358c10006dc5358c10006df4358c10006de4358c10006dd4358c10006dc4358c10004ff7258c1000cfe7258c1000cfc7258c10006de3258c10006dc3258c10024ff7158c10024fe7158c10024fd7158c10024fc7158c10026de3158c10026dc3158c1004cff7058c1004cfd7058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c100065f5458c10006de5458c10006dd5458c100065d5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c10006de4258c10006dd4258c10006dc4258c10026df7158c10026de7158c10026dd7158c10026dc7158c10026df5158c10026de5158c10026dd5158c10026dc5158c10026df4158c10026de4158c10026dd4158c10026dc4158c10026df2158c10026de2158c10026dd2158c10026dc2158c10006de7058c10006dc7058c10006df5058c10006de5058c10006dd5058c10006dc5058c10006df4058c10006de4058c10006dd4058c10006dc4058c10006df2058c10006dc2058c10026df1058c10026de1058c10026dd1058c10026dc1058c10004ff755881001cfe7558810004fd755881001cfc7558810004ff7458810014fe7458810004fd7458810014fc74588100067f54588100067d5458810004ff735881004cfc7358810026ef7258810006ef525881002eee5258810006ed525881002eec5258810006ef425881002eee4258810006ed425881002eec425881002eee325881002eec3258810024ff7158810024fe7158810024fd7158810024fc7158810026ee2158810026ec215881000cff705881000cfd705881002cfc705881002eec2058810026fa1058810026f91058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef54588100066f5458810006ee5458810006ed54588100066d5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006e
  | 2 => 0x6bf6484110046bc6484110006df6384110006dc6384110006ef628411006eec6284110025fa7084110026fb6084110025f67684110026f67684110024f676841100077765841101d77465841101bdf774841101bdf57484110007b764841101cfb464841101cf7754841101cf755484110007d76384110007d46384110007e76284110007e46284110025f67084110026f76084110027f36084110007f22084110007f120841100067f74594100047f74594100067e74594100067d74594100047d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067d42594100067c42594100067e32594100067c32594100267f71594100267e71594100267d71594100267c71594100267f41594100267e41594100267d41594100267c41594100267f31594100267e31594100267d31594100267c31594100267f21594100267e21594100267d21594100267c215941003e7f70594100067e705941003e7d705941003e7c70594100067f40594100067e40594100067d40594100067c40594100067f20594100067c20594100267f10594100267e10594100267d10594100267c1059410006bf7559010006be75590100063e7559010006bd75590100063d7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006be3259010006bc3259010026bf7159010026be7159010026bd7159010026bc7159010026bf5159010026be5159010026bd5159010026bc5159010026bf3159010026be3159010026bd3159010026bc3159010026bf2159010026be2159010026bd2159010026bc2159010036bf7059010006be7059010036bd7059010036bc7059010006bf5059010006be5059010006bd5059010006bc5059010006bf2059010006bc2059010026bf1059010026b71059010026be1059010026bd1059010026bc105901004edf7598c1004ede7598c1004edd7598c1004edc7598c1004edf7498c1004ede7498c1004edd7498c1004edc7498c10006df5498c100065f5498c10006de5498c10006dd5498c100065d5498c10006dc5498c1004edf7298c1004ede7298c1004edd7298c1004edc7298c10006df5298c10006de5298c10006dd5298c10006dc5298c10006df4298c10006de4298c10006dd4298c10006dc4298c10026df7198c10026de7198c10026dd7198c10026dc7198c10026df5198c10026de5198c10026dd5198c10026dc519
  | 3 => 0xf62cc91000eec62cc910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c9100657c754c9100067f654c91019e7c654c910006bf644c910196bc644c910006df634c91004edc634c910006ef624c91000eec624c910004fe76cc5100067f65cc51018e7c65cc510006bf64cc510186bc64cc510006df63cc51004edc63cc510006ef62cc51017eec62cc510005fa70cc510005f970cc51004cfc764c5100067f654c51015e7c654c510006bf644c510156bc644c510006df634c51004edc634c510006ef624c51014eec624c510005fb704c510005f8704c510027f0104c51000cfc76485100067f654851011e7c6548510006bf6448510116bc6448510006df6348510006dc6348510006ef624851000eec6248510005fb7048510005f87048510024fe76cc110024fc76cc1100067f65cc11010e7c65cc110006bf64cc110106bc64cc110006df63cc11004edc63cc110006ef62cc1100feec62cc110025f671cc110005f571cc110004fe768c1100067f658c1100f67c658c110006bf648c1100cebc648c110006df638c11004edc638c110006ef628c1100eeec628c11004cff764c110004fd764c110024fc764c1100057f754c1100657c754c1100067f654c1100e67c654c110005bf744c11005dbc744c110006bf644c1100debc644c110006df634c11004edc634c110006ef624c1100d6ec624c110005f7714c110025f4714c110004fe760c1100067f650c1100c67c650c110006bf640c1100bebc640c110006df630c11004edc630c110006ef620c1100b6ec620c11007cfe76881100067f65881100ae7c6588110006bf64881100a6bc6488110006df6388110006dc6388110006ef628811000eec6288110005fa768811007efa76881100077b65881101ff786588110007bb64881101f7b864881101f77b54881101f7795488110007db6388110007d86388110055f97288110007eb628811000efa628811000ef86288110057e8628811000ee86288110025fa7188110025f871881101f7f241881101f7f141881101efea21881101efe8218811000cff7648110054fd7648110024fc76481100067f654811009e7c6548110006bf6448110096bc6448110006df6348110006dc6348110006ef624811000eec6248110005f77148110025f47148110057e82048110025f8764811000ef87648110024f876481100077b65481101e7786548110007bb64481101dfb864481101df7b54481101df795448110007db6348110007d86348110055fb7248110007eb7248110007eb624811000efa624811000ef86248110057e86248110057ea42481101dfe94248110007f37148110025fa7148110025f87148110007f071481101dff241481101dff14148110057eb2148110007e921481100067f65841100767c6584110
  | 4 => 0x89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d89100076f54d89100076d54d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910007e641d8910007e541d89101efeb70d89101efeb10d89101efe810d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d89100066f54d8910006ee54d8910006ed54d89100066d54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d89101eeee71d8910006ed71d89101eeec71d8910006ef51d89101eeee51d8910006ed51d89101eeec51d8910006ef41d89101eeee41d8910006ed41d89101eeec41d89101eeee31d89101eeec31d89101eeef70d8910056ee70d8910006ed70d8910006ef50d8910006ee50d8910006ed50d8910006ec50d8910006ef40d8910006ee40d8910006ed40d8910006ec40d89101eeef10d89101eeec10d89100057f75589100657c75589100067f65589100067c6558910005bf745891005dbc7458910006bf6458910006bc6458910005df7358910005dc7358910006df6358910006dc6358910056ec6258910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc74589100067f54589100067d5458910004ff7358910006df7358910004df735891004cfc7358910006dc735891004cdc7358910054ff7258910006ef725891006cff7158910006f7715891007cff7058910006fb7058910005ee7618910056ee7618910004ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac64189100076f54189100076d5418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc6318910007e64118910007e54118910057e97018910206ef6018910207eb1018910207e8101891004cff76cc910004fe76cc910004fd76cc91004cfc76cc9100067f65cc9101ae7c65cc910006bf64cc9101a6bc64cc910006df63cc91004edc63cc910006e
  | 5 => 0x657c7558d100067f6558d100067c6558d10005bf7458d1005dbc7458d10006bf6458d10006bc6458d10005ef7258d10055ec7258d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d100067f5458d100067d5458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d1004ede6318d10006dd6318d10005de7618d10006de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d100075f5418d100075d5418d10006de6218d10006dc6218d10007d64118d10007d54118d1020fdb1018d1020fd81018d1004edf7518d1004ede7518d1004edd7518d1004edc7518d1004edf7418d1004ede7418d1004edd7418d1004edc7418d10006df5418d100065f5418d10006de5418d10006dd5418d100065d5418d10006dc5418d1004edf7218d1004ede7218d1004edd7218d1004edc7218d10006df5218d10006de5218d10006dd5218d10006dc5218d10006df4218d10006de4218d10006dd4218d10006dc4218d1004edf7118d1004ede7118d1004edd7118d1004edc7118d10006df5118d1020ede5118d10006dd5118d1020edc5118d10006df4118d1020ede4118d10006dd4118d1020edc4118d10006df2118d1020ede2118d1020edc2118d1004edf7018d1004edd7018d10006df5018d10006de5018d10006dd5018d10006dc5018d10006df4018d10006de4018d10006dd4018d10006dc4018d10006df2018d10006dc2018d1020edf1018d10006dd1018d1020edc1018d1000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910056ee62d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d89100067f54d89100067d54d891004cfe73d8910004fd73d8910006ef52d8910056ee52d8910006ed52d8910056ec52d8910006ef42d8910056ee42d8910006ed42d8910056ec42d8910056ee32d8910056ec32d8910024fe71d8910054fd71d8910024fc71d8910056ef21d891000cfe70d8910024fd70d891000cfc70d8910056ef20d8910055ee76d891000cee76d8910006ef65d89100076f65d
  | 6 => 0xd75d9110006bc75d91100063c75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006be32d9110006bc32d9110006bf71d911021ebe71d911005ebd71d911021ebc71d9110006bf51d911021ebe51d9110006bd51d911021ebc51d911021ebe31d911021ebc31d9110006bf21d911021ebe21d911021ebc21d911021ebf70d911005ebe70d911005ebd70d911005ebc70d9110006bf50d9110006be50d9110006bd50d9110006bc50d9110006bf20d9110006bc20d911021ebf10d911005ebd10d911021ebc10d911004cfe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d100067f54d8d100067d54d8d10006df53d8d10006de53d8d10006dd53d8d10006dc53d8d10006df43d8d10006de43d8d10006dd43d8d10006dc43d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10006de32d8d10006dc32d8d10024fe71d8d10024fc71d8d1004cfe70d8d1004cfc70d8d1004cde76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d100075f54d8d100075d54d8d10006de62d8d10006dc62d8d10007d641d8d10007d541d8d10217db10d8d10217d810d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d100065f54d8d10006de54d8d10006dd54d8d100065d54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d10006df71d8d10216de71d8d10006dd71d8d10216dc71d8d10006df51d8d10216de51d8d10006dd51d8d10216dc51d8d10006df41d8d10216de41d8d10006dd41d8d10216dc41d8d10006df21d8d10216de21d8d10216dc21d8d10216df70d8d10006dd70d8d10006df50d8d10006de50d8d10006dd50d8d10006dc50d8d10006df40d8d10006de40d8d10006dd40d8d10006dc40d8d10006df20d8d10006dc20d8d10216df10d8d10216dc10d8d100657e7598d100057d7598d100067f6598d100067c6598d1005dbe7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d10055ee7298d10005ed7298d100057f7558d10
  | 7 => 0xca10005f7714ca10025f4714ca1004ede63cc610006dd63cc610005fa70cc610005f970cc61004cff764c61004ede634c610006dd634c610005fb704c610005f8704c61000cff764861000eee6248610006ed6248610005fb7048610005f87048610006df63cc21004edc63cc210024fd768c21004ede638c210006dd638c210025f6718c210005f5718c2100057f754c2100757c754c210005bf744c210045bc744c210006df634c21004edc634c210024fd760c21004ede630c210006dd630c210025f6710c210005f5710c21000cfe7688210024fd768821000eee6288210006ed6288210025f67188210005f57188210025f9768821000ef97688210024f9768821023f7b548821023f79548821000efa628821006fea6288210007e9628821000ef86288210025fa7188210007f27188210007f17188210025f871882101efea21882101efe8218821002cff7648210006ef624821000eec624821006fe82048210005fb764821002efb76482102377b5448210237795448210007eb7248210007eb624821000efa624821000ef8624821006fe8624821006fea4248210237e94248210025fa7148210025f8714821006feb2148210007e92148210005f576c4210026f576c421022ef764c421022ef564c421022f7754c421022f7554c4210027f260c42100657e76d95100667e76d951001c7e76d95100057f74d95100057d74d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100067e62d95100067c62d95100077641d95100077541d95102277b10d95102277810d95100067f74d95100047f74d95100067e74d95100067d74d95100047d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067e32d95100067c32d95100067f71d95102267e71d95100667d71d95102267c71d95100067f41d95102267e41d95100067d41d95102267c41d95102267e31d95102267c31d95100067f21d95102267e21d95102267c21d95102267f70d95100667e70d95100667d70d95100667c70d95100067f40d95100067e40d95100067d40d95100067c40d95100067f20d95100067c20d95102267f10d95100667d10d95102267c10d951005dbe76d911005ebe76d9110014be76d91100073f75d91100073c75d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be62d9110006bc62d9110007b771d911005fb471d911021fbb10d911021fb810d9110006bf75d91100063f75d9110006be75d9110006b
  | 8 => 0x67f5458f100067d5458f10026df7358f10004ff7258f1000cfe7258f1000cfc7258f10024fc7158f10026de3158f10026dc3158f10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b10014fe7458b10004fd7458b10014fc7458b100067f5458b100067d5458b10004ff7358b1004cfc7358b10026ef7258b10024fc7158b10026ee2158b10026ec2158b1007eef2058b10026fa1058b10026f91058b1004cff76ccb10024fe76ccb10004fd76ccb10024fc76ccb1004ede63ccb10006dd63ccb10004ff764cb10024fe764cb10004fd764cb10024fc764cb100057f754cb1008d7c754cb1004ede634cb10006dd634cb1004ede63cc310006dd63cc310025f671cc310005f571cc310216df638c31004edc638c31004cff764c3100057f754c31008d7c754c310005bf744c310085bc744c31004ede634c310006dd634c310005f7714c310025f4714c31020edf630c31004edc630c310054fd76883101eeef628831000eec628831000cff7648310024fc764831000eee6248310006ed6248310005f77148310025f47148310004ff75d8e1001cfe75d8e10004fd75d8e1001cfc75d8e10004ff74d8e10014fe74d8e10004fd74d8e10014fc74d8e100067f54d8e100067d54d8e1000cfe72d8e10004fd72d8e1000cfc72d8e10006f571d8e10216de31d8e10216dc31d8e10006fa70d8e10004fd7698e10006df6398e1004cff7658e100057f7558e100757c7558e10005bf7458e10045bc7458e10004ff7558e100067f7558e100047f7558e1001cfe7558e10004fd7558e1001cfc7558e100067c7558e1001c7c7558e10004ff7458e10006bf7458e10004bf7458e10014fe7458e10004fd7458e10014fc7458e10006bc7458e10014bc7458e100067f5458e100067d5458e10006df7358e10006de4358e10006dd4358e10004ff7258e1000cfe7258e1000cfc7258e1004ede6318e10006dd6318e1006eee62d8a10004ff75d8a1001cfe75d8a10004fd75d8a1001cfc75d8a10004ff74d8a10014fe74d8a10004fd74d8a10014fc74d8a100067f54d8a100067d54d8a1004cfe73d8a10004fd73d8a1006cfd72d8a10006f571d8a101eeee21d8a101eeec21d8a10006fa70d8a1006eef20d8a1000cff7658a1006eec6258a10004ff7558a1001cfe7558a10004fd7558a1001cfc7558a10004ff7458a10014fe7458a10004fd7458a10014fc7458a100067f5458a100067d5458a10004ff7358a1004cfc7358a10006ef7258a1006eee4258a10006ed4258a1006eef2158a10024fc7058a1006eec2058a1004cff76cca10004fe76cca10004fd76cca1004cfc76cca10006df63cca1004edc63cca10004ff764ca10004fe764ca10004fd764ca10004fc764ca100057f754ca100757c754ca10006df634ca1004edc634
  | 9 => 0xf6398d200d5f97098d200057f7558d2009d7c7558d20005bf7458d20095bc7458d20005f77158d20005f47158d200fdfb7058d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d20014fe7458d20004fd7458d20014fc7458d20006bc7458d20014bc7458d200067f5458d200067d5458d20006df7358d20006de4358d20006dd4358d200d4ff7258d20006ef7258d200d6ee4258d20006ed4258d20004ff7158d20006f77158d20004f77158d20024fc7158d20006f47158d20024f47158d200fcff7058d20006fb7058d200ecfe7618d2004ede6318d20006dd6318d20004ff75d852001cfe75d8520004fd75d852001cfc75d8520004ff74d8520014fe74d8520004fd74d8520014fc74d85200067f54d85200067d54d852004cfe73d8520004fd73d852006ef621d852006ef521d8520024fe70d8520006f76198520055f970985200057f755852009d7c7558520005bf7458520095bc7458520005df7358520005dc735852007dfb705852009d7e75185200057d7518520095be7418520005bd7418520005de7318520005dd7318520026f66118520006f56118520004fe76cc520004fd76cc52004cfc76cc52004ede63cc520006dd63cc520006f761cc520026f461cc520004fe768c520004fd768c520024fc768c52009d7e758c5200057d758c520095be748c520005bd748c520006df638c52004edc638c52000dee728c520005ed728c520005fa708c520005f9708c520004ff764c520004fe764c520004fc764c52004ede634c520006dd634c520004fe760c520004fd760c520024fc760c520006df630c52004edc630c52000dee720c520005ed720c520006f7610c520026f4610c520005fa700c520005f9700c520024ec764852025def744852025ded74485202576f54485202576d544852000def714852000fe77148520007e76148520026ee6148520026ec6148520007e46148520007eb7048520005ec7048520007e8704852000eef604852000feb604852000cfe76cc12000cfc76cc120006df63cc12004edc63cc12000dee72cc120005ed72cc1200b4fe768c12004ede638c120006dd638c12004cff764c12000cfe764c1200d4fd764c12000cfc764c1200057f754c12009d7c754c120005bf744c120095bc744c120006df634c12004edc634c120005ef724c12000dec724c1200ecfe760c12004ede630c120006dd630c12024def748812024ded74881202476f54881202476d5488120005ed71881201eeec618812000dee708812000fea708812000eef608812000feb6088120004ff7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f10014fe7458f10004fd7458f10014fc7458f10
  | 10 => 0xc03004edf644c030276dd644c0302775f544c0302775d544c030005df724c03020ddc714c030006dd614c03004ddf704c03004fdb704c03026ede604c03004fda604c0300ad7e75d8e200057d75d8e200b5fa70d8e20004ff75d8e2001cfe75d8e200067e75d8e2001c7e75d8e20004fd75d8e200067d75d8e200047d75d8e2001cfc75d8e20004ff74d8e20014fe74d8e20004fd74d8e20014fc74d8e200067f54d8e200067d54d8e20006ed72d8e20024fe71d8e20004fd71d8e200b4fe70d8e20006fa70d8e200d4fd7698e20006df6398e2004cff7658e20004ff7558e2001cfe7558e20004fd7558e2001cfc7558e20004ff7458e20014fe7458e20004fd7458e20014fc7458e200067f5458e200067d5458e20006df7358e20006df5358e20006dc5358e20006de4358e20006dd4358e200d6df3258e200d6dd3258e20004ff7158e20024fc7158e2004ede6318e20006dd6318e200edfa7018e2002dfa70d8620006f76198620004ff755862001cfe7558620004fd755862001cfc7558620004ff7458620014fe7458620004fd7458620014fc74586200067f54586200067d5458620004ff735862004cfc7358620006f64158620006f54158620056f62158620056f521586201eeec2158620024ff7058620056ef20586200ad7e75186200057d75186200a5be7418620005bd7418620005de7318620005dd7318620026f66118620006f5611862006dfa701862004cff76cc620004fe76cc620004fd76cc62004ede63cc620006dd63cc62000dee72cc620005ed72cc620024ff768c620004fe768c620004fd768c6200ad7e758c6200057d758c6200a5be748c620005bd748c620005fa708c620005f9708c620004ff764c620004fd764c620004fc764c62004ede634c620006dd634c620005ef724c62000dec724c620024ff760c620004fe760c620004fd760c620005fa700c620005f9700c620266ef6488620266ed64886202676f54886202676d548862000dee718862000fe671886201efe661886201eeed6188620007e561886201efea7088620005ed70886201efe9708862000eee608862000fea60886200d4fd76cc22000cff768c22000cfd768c22004ede638c220006dd638c22000dee728c220005ed728c2200fcff764c2200057f754c2200ad7c754c220005bf744c2200a5bc744c22000cff760c22000cfd760c22004cfc760c22004ede630c220006dd630c22000dee720c220005ed720c22004cfe76d8d20004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20004ff74d8d20014fe74d8d20004fd74d8d20014fc74d8d200067f54d8d200067d54d8d200ecff72d8d2000cfe72d8d200ecfd72d8d2000cfc72d8d200eeee42d8d20006ed42d8d200eedf32d8d200eedd32d8d20024fe71d8d20004fd71d8d20006d
  | 11 => 0x5fb704c530005f8704c530024dc764c5300075f654c5302bf5c654c5302b5df744c5302b5dd744c5300079f644c5302af9c644c5302af5f544c5302af5d544c530006df624c53004ddf714c53004fd7714c530007d7614c530026de614c530026dc614c530007d4614c530007db704c530005dc704c530007d8704c53004edf604c53004fdb604c530004fe7688530004fd7688530024fc76885300067f658853012e7c6588530006bf6488530126bc648853004dde7388530005dd7388530006ef628853000eec6288530004ff7648530004fe7648530004fc76485300067f654853011e7c6548530006bf6448530116bc64485300067f658c1300f67c658c130006bf648c1300cebc648c13004dfa708c13004efb608c1300075f658c1302a75c658c13026ddf748c13026ddd748c1300079f648c13029f9c648c13029f5f548c13029f5d548c130006df628c130005dd718c130216dc618c13004dde708c13004edf608c13004fdb608c130004ff755883001cfe7558830004fd755883001cfc7558830004ff7458830014fe7458830004fd7458830014fc74588300067f54588300067d545883000cfd735883004eef72588300b6ee5258830006ed52588300b6ee4258830006ed425883004eef325883004eec3258830004ff7158830024fc71588300b6ef21588300b6ec205883004ddf764c8300fedf764c8300075f754c8302975c754c83004edf654c830296dd654c83004edf644c83028edd644c83028f5f544c83028f5d544c83004ddf724c83004fcf724c83000ede624c83000edc624c8300b7ce524c830297cd524c8300b7ce424c83028fcd424c83020ddc714c830005df704c8300eede604c83004fda604c830004ff755843001cfe7558430004fd755843001cfc7558430004ff7458430014fe7458430004fd7458430014fc74584300067f54584300067d5458430004ff725843000cfe725843000cfc725843004edf3258430006dd325843004ef77158430006f65158430006f55158430006f64158430006f5415843004ef7315843004edc315843004ef4315843004edf305843004ddd768c43020edd768c430004dd768c43020f5e758c43020f5d758c43020f9e748c43020f9d748c43004edf648c430286dd648c4302875f548c4302875d548c430005dd728c43004dde718c43004fd6718c43004edf618c43020edd618c430005dd708c430216de608c43004fda608c430024ff768843004cfe7688430004fd768843020ddf738843004ddc7388430026f66188430006f56188430004ff7648430004fd764843004cfc7648430005df734843004ddc734843000eee6248430006ed6248430026f66148430006f5614843004ddf764c030006df764c030004df764c0300075f754c03027f5c754c0300079f744c0302779c744
  | 12 => 0xd73d91302debc73d9130006bf53d91302debe53d9130006bd53d91302debc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bd52d9130006bc52d91302debf32d9130006be32d91302debc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bd51d9130006bc51d91302debf31d91302debc31d9130006bf21d9130006bc21d91302debf70d91300debe70d91300debd70d91300debc70d9130006bf50d9130006be50d9130006bd50d9130006bc50d91302debf30d91300debd30d91302debc30d9130006bf20d9130006bc20d913000cfe76d89300067f65d89300067c65d8930006bf64d8930006bc64d89300d6ee62d8930004ff75d893001cfe75d8930004fd75d893001cfc75d8930004ff74d8930014fe74d8930004fd74d8930014fc74d89300067f54d89300067d54d893000cfc73d8930006de43d8930006dd43d89300d6ee32d8930024fe71d8930004fd71d89300d6ec21d893004cfd70d89300d6ef20d89300057f75589300e57c75589300067f65589300067c6558930005bf74589300ddbc7458930006bf6458930006bc64589300d6ec6258930005f77158930005f4715893000cfc764c9300057f754c9300e57c754c9300067f654c93019e7c654c930006bf644c930196bc644c930006ef624c93000eec624c93004fcc324c930005fb704c930005f8704c9300067f65d85300067c65d8530006bf64d8530006bc64d8530004ff75d853001cfe75d8530004fd75d853001cfc75d8530004ff74d8530014fe74d8530004fd74d8530014fc74d85300067f54d85300067d54d853000cfe72d8530004fd72d853000cfc72d8530006f721d8530006f421d85300e57e75985300057d75985300067f65985300067c65985300ddbe7498530005bd7498530006bf6498530006bc6498530006f761985300057f75585300e57c75585300067f65585300067c6558530005bf74585300ddbc7458530006bf6458530006bc6458530005ef72585300d5ec72585300067f65185300067c6518530006bf6418530006bc6418530026f66118530006f56118530005de76cc53004ede76cc530004de76cc5300075f65cc5302d75c65cc53004ddf74cc5302cddd74cc5300079f64cc5302c79c64cc5302c75f54cc5302c75d54cc530006df62cc530026de61cc530026dc61cc530005de70cc53004edf60cc53004fdb60cc5300e57e758c5300057d758c5300067f658c5301767c658c5300ddbe748c530005bd748c530006bf648c53016ebc648c5302b5dd738c530006f7618c530026f4618c530005fa708c530005f9708c530024fc764c5300067f654c53015e7c654c530006bf644c530156bc644c530006f7614c530026f4614c530
  | 13 => 0x8630006dd3258630006f64158630006f541586300f57e75186300057d75186300cdbe7418630005bd74186300edee7218630005ed7218630026f66118630006f561186300f57e758c6300057d758c6300cdbe748c630005bd748c630026f6618c630006f5618c630005fa708c630005f9708c6302175e758c6302175d758c6302179e748c6302179d748c630306df648c630306dd648c6303075f548c6303075d548c630005dd728c63004dde718c630217d6618c630216dd618c630007d5618c630217da708c630005dd708c630217d9708c63004ede608c630024ff764c630026f6614c630006f5614c630005fb704c630005f8704c630005dd760c63004edd760c6302fedf640c6302fedd640c6302ff5f540c6302ff5d540c630005dd720c63004fd6710c630216dd610c630005dd700c63004fda600c630024ff7688630004fe7688630004fd7688630215df738863004ddc7388630004ff7648630004fd7648630004fc7648630005df734863004ddc734863000eee6248630006ed6248630005dd76cc23004edd76cc2302f6df64cc2302f6dd64cc2302f75f54cc2302f75d54cc230005dd72cc230215de71cc230006dd61cc23004fda60cc2302efda50cc2302efd950cc2300e57e76d95300e67e76d953001c7e76d95300057f74d95300057d74d95300067f64d95300067e64d95300067d64d95300067c64d95300073c64d95300063c64d95300075e43d95300075d43d95300067e62d95300067c62d95302e77b30d95302e77830d95300067f74d95300047f74d95300067e74d95300067d74d95300047d74d95300067c74d95300067f73d95302e67e73d95300e67d73d95302e67c73d95300067f43d95302e67e43d95300067d43d95302e67c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95302e67f32d95300067e32d95302e67c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95302e67f31d95302e67c31d95300067f21d95300067c21d95302e67f70d95300e67e70d95300e67d70d95300e67c70d95300067f40d95300067e40d95300067d40d95300067c40d95302e67f30d95300e67d30d95302e67c30d95300067f20d95300067c20d95300ddbe76d91300debe76d9130014be76d91300073f75d91300073c75d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d91300079f73d91300df9c73d9130006be62d9130006bc62d91302dfbb30d91302dfb830d9130006bf75d91300063f75d9130006be75d9130006bd75d9130006bc75d91300063c75d9130006bf73d91302debe73d91300deb
  | 14 => 0x5bf7458121115bc7458121005df7358121005dc7358121006f96018121004ff751812101cfe7518121004fd751812101cfc7518121004ff7418121014fe7418121004fd7418121014fc74181210067f54181210067d541812104cfe7318121004fd7318121024fd7218121206ee2118121206ec211812102eef201812102ef92018121004ff7558b3001cfe7558b30004fd7558b3001cfc7558b30004ff7458b30014fe7458b30004fd7458b30014fc7458b300067f5458b300067d5458b3004ede4358b30006dd4358b3004eef7258b300feee5258b30006ed5258b300feee4258b30006ed4258b3004eef3258b3004eec3258b30004ff7158b30024fc7158b3004edf3158b300feec2158b3004edc3058b300feef2058b30004ff755873001cfe7558730004fd755873001cfc7558730004ff7458730014fe7458730004fd7458730014fc74587300067f54587300067d5458730004ff725873000cfe725873000cfc725873004ef7715873004ef7315873004ef4315873004ddf764c730006df764c730335df744c730335dd744c73032f5f544c73032f5d544c730006dd624c73004fd7714c730026de614c730026dc614c730005dc704c730024ff768873004cfe7688730004fd768873004dde7388730005dd738873000eee6288730006ed6288730004ff7648730004fd764873004cfc76487300f57e75d8a300057d75d8a300eeee62d8a3000cff7658a300eeec6258a30004ff7558a3001cfe7558a30004fd7558a3001cfc7558a30004ff7458a30014fe7458a30004fd7458a30014fc7458a300067f5458a300067d5458a30006ef5258a300eeec5258a300eeee4258a30006ed4258a300eeee3258a30004ff7158a30024fc7158a300eeef2158a3004cfc7058a300eeec2058a30005dd76cca3004edd76cca30326df65cca30326dd65cca3031edf64cca3031edd64cca3031f5f54cca3031f5d54cca3000ede62cca3000edc62cca30215de71cca30005dd70cca3004fda60cca3000cff764ca300057f754ca300f57c754ca3000eee624ca30006ed624ca30005fb704ca30005f8704ca300eddf764ca3000edf764ca3000cdf764ca300075f754ca303175c754ca30316df654ca30316dd654ca3030edf644ca3030edd644ca3030f5f544ca3030f5d544ca3004ddf724ca3004fcf724ca3000ede624ca300efce624ca3000ece624ca30007cd624ca3000edc624ca300efce524ca30317cd524ca300efce424ca3030fcd424ca30215dc714ca30005df704ca30007db704ca30007d8704ca3004ede604ca30006f76198630004ff755863001cfe7558630004fd755863001cfc7558630004ff7458630014fe7458630004fd7458630014fc74586300067f54586300067d5458630004ff725863000cfe725863000cfc7258630006df325
  | 15 => 0xd545803104ede4358031006dd4358031004ff725803100cfe725803100cfc7258031026df3158031026dd3158031026fb7058031006fa5058031006f95058031006fa4058031006f9405803104efb305803104edc305803104ef83058031026fb1058031026f81058031004ff7558e2101cfe7558e21004fd7558e2101cfc7558e21004ff7458e21014fe7458e21004fd7458e21014fc7458e210067f5458e210067d5458e21026df7358e2114eee4258e21006ed4258e2114edf3258e2114edd3258e21024fe7158e21024fc7158e21026de3158e21026dc3158e21004ff7058e21004fc7058e21004ff759822101cfe7598221004fd759822101cfc7598221004ff7498221014fe7498221004fd7498221014fc74982210067f54982210067d549822104cfe7398221004fd7398221024fe7198221026fa709822106ef92098221026fb1098221026f81098221004ff75582210067f75582210047f755822101cfe7558221004fd755822101cfc75582210067c755822101c7c7558221004ff7458221006bf7458221004bf7458221014fe7458221004fd7458221014fc7458221006bc7458221014bc74582210067f54582210067d5458221004ff7358221006df7358221004df735822104cfc7358221006dc735822104cdc7358221056ee4258221006ed4258221024fc7158221026ef2158221026ed2158221026fb7058221056fa2058221056ec2058221026fb1058221026f8105822104cfe76d8d21004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21004ff74d8d21014fe74d8d21004fd74d8d21014fc74d8d210067f54d8d210067d54d8d21006df53d8d21006dc53d8d21006de43d8d21006dd43d8d21024ff72d8d21024fd72d8d21166df32d8d21166dd32d8d21004fe70d8d21004fd70d8d21006df6398d2114df57198d210057f7558d2111d7c7558d2117df77158d21004ff7558d210067f7558d210047f7558d2101cfe7558d21004fd7558d2101cfc7558d210067c7558d2101c7c7558d21004ff7458d21014fe7458d21004fd7458d21014fc7458d210067f5458d210067d5458d21006df7358d2114cff7258d21006ef7258d2117cff7158d21006f77158d21004ff7058d21004fc7058d21164fe7618d2104ede6318d21006dd6318d2100cfe76cc52100cfc76cc521006df63cc52104edc63cc52100dee72cc521005ed72cc52104cff764c52100cfe764c52114cfd764c52100cfc764c521006df634c52104edc634c521005ef724c52100dec724c521004ff75d812101cfe75d8121004fd75d812101cfc75d8121004ff74d8121014fe74d8121004fd74d8121014fc74d81210067f54d81210067d54d812104cfe73d8121004fd73d8121024fd72d812107efa20d8121006fb60981210057f755812111d7c7558121
  | 16 => 0x893114eec52d893114eee42d8931006ed42d893114eee32d893104cfd71d893114eef21d8931004fe70d8931004fd70d893114eec20d89310057f755893115d7c755893114eec6258931005de76cc93104ede76cc931356df65cc931356dd65cc93134edf64cc93134edd64cc93134f5f54cc93134f5d54cc93114ddd72cc93100ede62cc93100edc62cc931025de71cc931025dc71cc93104edf61cc93104fd761cc931005dd70cc931024fc764c9310057f754c93115d7c754c931006ef624c93100eec624c931005f7714c931025f4714c931025dc764c93100edc764c931024dc764c9310075f754c9313475c754c931346df654c931346dd654c93133edf644c93133edd644c93133f5f544c93133f5d544c93104ddf724c93104fcf724c931007cf624c93100ede624c93100edc624c93114fcc624c93100ecc624c93114fce524c931347cd524c93114fce424c93133fcd424c931007d7714c931025de714c931025dc714c931007d4714c93104edf614c93104fd7614c931005df704c931004ff75d813101cfe75d8131004fd75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d81310067f54d81310067d54d813100cfe72d8131004fd72d813100cfc72d8131006fb60981310057f755813115d7c7558131005bf7458131155bc7458131005ef725813114dec7258131006f96018131004ff751813101cfe7518131004fd751813101cfc7518131004ff7418131014fe7418131004fd7418131014fc74181310067f54181310067d541813100cfe7218131004fd721813100cfc7218131006df3218131006dd321813120ede311813120edc3118131004ff755883101cfe7558831004fd755883101cfc7558831004ff7458831014fe7458831004fd7458831014fc74588310067f54588310067d545883104ede4358831006dd4358831024ff7258831026ef7258831136ee5258831006ed5258831136ee4258831006ed425883104eef325883104eec3258831024fc7158831026df3158831026dd3158831026ee2158831026ec2158831004ff7058831004fc705883104edc3058831136ef2058831004ff759803101cfe7598031004fd759803101cfc7598031004ff7498031014fe7498031004fd7498031014fc74980310067f54980310067d549803100cfe7298031004fd729803100cfc7298031026fa7098031006fa5098031006f95098031006fa4098031006f9409803104efb309803104ef83098031026fb1098031026f81098031004ff75580310067f75580310047f755803101cfe7558031004fd755803101cfc75580310067c755803101c7c7558031004ff7458031006bf7458031004bf7458031014fe7458031004fd7458031014fc7458031006bc7458031014bc74580310067f54580310067
  | 17 => 0x267f41596310267e41596310267d41596310267c41596310267f31596310267e31596310267d31596310267c31596310267f21596310267e21596310267d21596310267c21596310067f70596310067e70596310067d70596310067c70596310067f40596310067e40596310067d40596310067c40596313667f30596313667c30596310067f20596310067c20596310267f10596310267e10596310267d10596310267c1059631006bf7559231006be75592310063e7559231006bd75592310063d7559231006bc755923116ebf735923135ebe7359231006bd735923135ebc7359231006bf535923135ebe5359231006bd535923135ebc5359231006bf7259231006be7259231006bd7259231006bc7259231006bf5259231006be5259231006bd5259231006bc525923135ebf3259231006be325923135ebc3259231026bf7159231026be7159231026bd7159231026bc7159231026bf5159231026be5159231026bd5159231026bc5159231026bf3159231026be3159231026bd3159231026bc3159231026bf2159231026be2159231026bd2159231026bc2159231006bf7059231006be7059231006bd7059231006bc7059231006bf5059231006be5059231006bd5059231006bc505923135ebf305923135ebc3059231006bf2059231006bc2059231026bf1059231026be1059231026bd1059231026bc1059231004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a31014fe7458a31004fd7458a31014fc7458a310067f5458a310067d5458a31006de4358a31006dd4358a31026ef7258a31166ee3258a31024fc7158a31026df3158a31026dd3158a31026ee2158a31026ec2158a31004ff7058a31004fc7058a31166ef2058a3100cff764ca310057f754ca311757c754ca3119e7e654ca310067d654ca31196be644ca31006bd644ca3100eee624ca31006ed624ca3104fcc324ca31005f7714ca31025f4714ca31004ff759823101cfe7598231004fd759823101cfc7598231004ff7498231014fe7498231004fd7498231014fc74982310067f54982310067d549823100cfe7298231004fd729823100cfc7298231024fe7198231026fa7098231026fb1098231026f81098231004ff755823101cfe7558231004fd755823101cfc7558231004ff7458231014fe7458231004fd7458231014fc74582310067f54582310067d5458231006de4358231006dd4358231004ff725823100cfe725823100cfc7258231024fc7158231026df3158231026dd3158231026fb7058231026fb1058231026f8105823100cfe76d893114eee62d8931004ff75d893101cfe75d8931004fd75d893101cfc75d8931004ff74d8931014fe74d8931004fd74d8931014fc74d89310067f54d89310067d54d8931024fd73d8931006ef52d
  | 18 => 0x761985320057f755853219d7c75585320067f65585320067c65585320067f65185320067c6518532026f66118532006f561185320067f65d81320067c65d8132004ff75d813201cfe75d8132004fd75d813201cfc75d8132004ff74d8132014fe74d8132004fd74d8132014fc74d81320067f54d81320067d54d81320fedd73d8132006de43d8132006dd43d813204cfd72d81320feee42d8132006ed42d8132024fe71d8132004fd71d81320fefa20d813219d7e75981320057d75981320067f65981320067c6598132006fb60981320057f755813219d7c75581320067f65581320067c6558132005bf7458132195bc7458132005f77158132005f471581320067f65181320067c6518132006f96018132004ff751813201cfe7518132004fd751813201cfc7518132004ff7418132014fe7418132004fd7418132014fc74181320067f54181320067d541813204cfd7218132024fe7118132004fd71181320b6f92018132004ff7558b3101cfe7558b31004fd7558b3101cfc7558b31004ff7458b31014fe7458b31004fd7458b31014fc7458b310067f5458b310067d5458b31024fc7358b3104eef7258b3117eee5258b31006ed5258b3117eee4258b31006ed4258b3104eef3258b3104eec3258b3117eef2158b31004ff7058b31004fc7058b3117eec2058b3104ddf764cb31136df764cb310075f754cb313775c754cb3104edf654cb31376dd654cb3104edf644cb3136edd644cb3136f5f544cb3136f5d544cb3104fcf724cb3100ede624cb3100edc624cb3117fce524cb31377cd524cb3117fce424cb3136fcd424cb31025de714cb31025dc714cb31005df704cb31004ff759833101cfe7598331004fd759833101cfc7598331004ff7498331014fe7498331004fd7498331014fc74983310067f54983310067d5498331024fe7398331024de739833100cfe7298331004fd729833100cfc729833104edf3298331006dd3298331216de319833104edc319833104efa709833104edf309833104efb309833104ef83098331004ff755833101cfe7558331004fd755833101cfc7558331004ff7458331014fe7458331004fd7458331014fc74583310067f54583310067d5458331024fc7358331004ff725833100cfe725833100cfc725833104efb705833104efb305833104ef830583310067f74596310047f74596310067e74596310067d74596310047d74596310067c74596311767f73596313667e73596310067d73596313667c73596310067f43596313667e43596310067d43596313667c43596310067f72596310067e72596310067d72596310067c72596310067f42596310067e42596310067d42596310067c42596313667f32596310067e32596313667c32596310267f71596310267e71596310267d71596310267c7159631
  | 19 => 0x800000800b000000c000012000003400400c001000001000200000cc002015003000000a002004ff755873201cfe7558732004fd755873201cfc7558732004ff7458732014fe7458732004fd7458732014fc74587320067f54587320067d545873200cfc735873204ef7715873204ef7315873204ef4315873214ef62158732004ff7058732004fc7058732004ff759833201cfe7598332004fd759833201cfc7598332004ff7498332014fe7498332004fd7498332014fc74983320067f54983320067d549833200cfe7398332024fe7198332004fd719833204efa709833204efb309833204ef830983320eef92098332004ff75583320067f75583320047f755833201cfe7558332004fd755833201cfc75583320067c755833201c7c7558332004ff7458332006bf7458332004bf7458332014fe7458332004fd7458332014fc7458332006bc7458332014bc74583320067f54583320067d545833200cfc735833204edc735833200cdc735833204ede4358332006dd4358332004ff7158332024fc715833204edf315833204efb705833204efb305833204edc305833204ef830583320d6fa205833238d7e76d953219e7e76d953201c7e76d95320057f74d95320057d74d95320067f64d95320067e64d95320067d64d95320067c64d953237f5f73d953237f5c73d95320075e43d95320075d43d95323876f72d953237f6c72d953237f6e42d95320076d42d95323876f32d953237f5e32d953237f5c32d953237f6c32d95320067f74d95320047f74d95320067e74d95320067d74d95320047d74d95320067c74d953237e7f73d95323867e73d953237e7d73d953237e7c73d95320067f43d95323867e43d95320067d43d95323867c43d953237e7f72d953237e7e72d953237e7d72d953237e7c72d953237e7f42d953237e7e42d953237e7d42d953237e7c42d953237e7f32d953237e7e32d953237e7d32d953237e7c32d95320067f71d95320067e71d95320067d71d95320067c71d95320067f41d95320067e41d95320067d41d95320067c41d95323867f31d95323867c31d953237e7f21d953237e7e21d953237e7d21d953237e7c21d95320067f70d95320067e70d95320067d70d95320067c70d95320067f40d95320067e40d95320067d40d95320067c40d95323867f30d95323867c30d953237e7f20d953237e7e20d953237e7d20d953237e7c20d95320067f65d85320067c65d8532004ff75d853201cfe75d8532004fd75d853201cfc75d8532004ff74d8532014fe74d8532004fd74d8532014fc74d85320067f54d85320067d54d853204cfd72d8532006f641d8532006f541d853217ef621d8532004fe70d8532004fd70d853219d7e75985320057d75985320067f65985320067c6598532195be7498532005bd7498532006f
  | 20 => 0x400400d0000004000000000000a000000001002a0000020030008000000800400001800000240000010080004004071009000000c0170068078020000007001c0a00000008020026006000000c0040030170024000000008000000000100f002403c00400e0058000000005001c002012006801400a028005808802e002003803c03a002000000400200900100000040030000008000002001806802a014005800401a0040068004002000006800800a0020000000000007000000000400a00180180000080000000002000000000000c008002000000000600000000360030000004002000000000400a004000803000a0080098008000009003000c000001003000800400a000000801e000000001c00400f00100080000090008000000000002000000002300100200000000140060002000001000400c00d001001400000b002000800000100b004c0000090008004004000000803c00000500200000080010000010000008000001800205a0048000018019002806400000600280040020020008000000003000800001800b000000402801000c00140020060050024012000000000400c000002000801600400b0000004006000000400000000000d0006003007800c00600600280340bc00b002803800e007001800400a00a0000058010000001808401a0030018000006003005800c00000400d800c01a0000018050002001024802000600002b802800000b000003c016005007000800e000001802000600000480100000060060000004019003004000a022000000000c000000000801a015000007400c0130028064006001001800003c0000010004006002000000800e0020010000016000008800c022010000000c00000300980000000110000010012000000009c000000002000c00c00a000802000e003001000400403000000140000040010008000010021003000000000000000000030000058002028000800401a001000005c012000000001400600100580380240000000000006002007000002400c0030004004006000000802e00400000000080050000018010010000800800400a00200780100030010018000003000000400001400180240020110030018010000000800c00600100180000000040000008002003003001400e00501400440000000000010010000000000c050004000800800a005000000401400d0008000000000006801402a0000020040000000000002000c001006001400000200000000020070000018012002003000006400400000100200060030008006000002800000000600b0000010000000800800a000004800400203e00a801804c00b00180380100010000018000000002004401000100780000000050000018004000000000001200000000180020080000014004000000000000a02300
  | 21 => 0x929bae199143a43be23f0000000000083c0000000000cd00000000002bf8d1c00021f328822c43140821bc65a7b200000000004a13750aa57f60000000000000000144800000042b0000001a4cb273232e8487e36d214000178e66a0000c692c45dd5f5075d73226636c00000000003d98001926b9a69dafb40004bf0e5a91c00000018b0a752e86225b20c9c0000b11ae8000ff6000000000023e0000000000000bd50960000000cd60000d2d90e0003a180011740000000000e8800840386e95ce7cf21480012729c107480000000004eb90e43ca000663a9ad39a6053451064000d245c6813532600008700005a4753000402000200480000060000060014000016002001c0020050010060000007008000400400100f000002a0030088000010003008800800e000002000800200000080140200020070048008000000800000e0020010000018009003801800200000280180120010008034006001000802c00c007000003400401000200000020050000000024004000000000000d000801c008000001000800c000000800c00000300200000040000008008012002002801800a0060018000020000000804005c000007001c00c00900200080040140010000028018002001400600600000300000080000010004004005800c0100010008008002000000003c000033003000c00a00a000800801400f000802000000c002802c00000000c8000012001001000000c0020000008000007000811c00200100500140000060018014000021000001800000c000000c022004005800c0020000030054006003002800001c0000010000000010000800800a001004002800000a00600540060000020008000010000000802200800080040000010068000000011000815c00000700880b000200a000800000400e0038000002001000802c00600d0000000002004009001000000700000040000040000004002016006800403c00300081100000040000004000013000000401a003000001000000800000180120060000000004002006000c02001a0010018004007000004c02000600680000080070000000000004000000001000500900000260030008000000033002001c000006009806805a00b00300000120010018004006009003000400a002001000000000200100000120080008000002001004001000600f0008044000000000000003e001032801800200100400240000000000054010001003800c0020120000048000001000000400000a008000000000200000100200040000010006004000800000e00b001000400000000200180040100008000000001000802c000003000001000800400080340020180010010008000001003000400000b80480080010058034004003002001c01400400b80f800c00a0060004000002006004c0
  | 22 => 0x103000000000064b00016b24732b61f4000024f175a0340be17e3e997917b634600028711361040ec93952b0c78129000000000000000003820001f61020000a5703aac540007613140f15a2852917c8654e5e0001e900008f400000008bcce44b33b6800128a0002e20e049347f502e26940009670000d3c27038d4dd81c40002bf2fd8001112cb66978e94000257253b0e8f925171cb80000007f8177048c586c043c3042d99a89e58707517a273a36e09c4fb200048780018148673179f30b26a2019280000001972fc00002ec00035000000006c4000000000018c05c2d786ea0001170000e786695e02c8cfd65ec000055952e10c6139d7502e0001d78ea800094f0a6a5180009c6000000157200000023e40002cf000337d6acb8e59b0eb888a205610a9940001813a7a958d6ca520003399a1856439c029000077907617d4332b5a198864d03c46f4f587b84dc000000156d30672b1c49dac000cdc621982ccaad0d4fdb5215662e438f9a0428242730a119d0a40003908000c707e763432710cc905426a788a6269b65a8000dc21b64b8104115a0b95a9000120067b65300006c000015c000000009159d16240009d839a8224dc4c1b32c2538de806a000000195c0000001f8817600046794f49f47b558880000602b600022f54d498a4240ef80000002079fa40842ce1ae22d02d250600005a06861c831d00000f27cd0002764c76bf25528ba15d09112610001a404bb48386f95a04010ed2384f8600001200000002453eda2c4ba61610000b600000005fc2b1ce1e36a5a18f1c19eb204361924db21bf190800182244b2d9981800048f0000000d4a8bb660882000048940b00012528e351095159028c42ed0a200006540002fb005298861833b46b4b3d46d8aed11063f1122c64e1c72d49da574b8200c1e78fdcad03ef20ea67d95620a0e9b23d40253b2f00bfc5388f2028ac404ca57706231d5718cc9484b1987fc96843416c19aa80a3c9130d77a08429392e845a47f593173d33489c3eba774b04ae13c6935c0fc53f17b15296484411d91db177c1253042f0c0742045f4a5cc5b655c59606ad87e0af0832e50cf0acb12f144c2e2b8a0001109a2c63113b0000000c26000000000000000000015de5142a3110c37a1216209ef000001e5671fc448c19d4f9ac0c3d861000014a86de2952d38f780001805482db8000cc622802382f28b05952284c9c6bb1ba2ff146224d34a233904c08848a32d00007bd00008954f600035b80000001f80002cc88224983c41cd0bbc5ae01602e8000cf45b31e9c00020003e80000008e8415800000000011f80000000000000000e0a00011a80000000003b834054e09330002f8000030766f00008909a3568a4d400000000010bd9aebe25de0a6946c04500007e800060f63a06e055e5
  | 23 => 0x2980c7806e00047f000000000000034e8b9623d0001a9c00000000000000000000000000782a6c0001f00688a41000000092cc161911cfd18aaec1f5a1f000036e1922ca000020228f218168eba24e188c8e048015d629a0310ae926588601da1b120b154431cc4c4ba96dd39818245112a43fa563267278ce4495c000028834e0fa6a000018944bd1732a98546b7729a99e8000189000141d6c420c3bb8000000000317000009e00000023bc00000000000000cc0000000ab0aec1363c5b1896660000a1b1b923479d00004640000000001f60f7283c000326d4bc4a53f4000175c52f0001311264662215273d5f00006a4ae20f2ea3c1e59824b1c352543146934e0a72f99eb83bcb0634a84998c0a4d694a410a2ab9609034292dc3c62960000142cf847592f16ca000000000000095700000014b09474d724908be2c92ec2c314480f05c785097cc00000009200000002c8af14372000407000083000036326cc000bb20001461662458000284c0220000001a2430e33207c2e9590819e00021d8252227636352c49285a2aca8e8b0ec063d58000210bd42aa80018e2057036081c0006795aeac4d00892a61c8270690b3048bb2958780b44c72a34c021510000000ab00003ba0a04d7400046c88c000001a2be350c10a0006040000000000000225c0000003490b5cebc0c5595b20c0a4aab0001f5558848c50f8be80003d05ad8000054a330002ed19c485800009ed5f20000002790826ac944a80000000000000610b3e8c009d12f890e000617000000066530e80000000006600000000000000290d9c800000010091540001bc8000dea00000000008ea00031813fc040be3047a0603ea0000000000000aba35a2b998a6376524abc800083f00023c42ea15c2a7ad449f6abe54d96a8fbac9554f171868009d583a344b187e1659a2355804801a6a6c860800000011d9a369f501f0ec15123fb0002bb82883ca61129e0000000021a36832213b2efb15c00004e4ef00017de00059c8c60a3600009e0f7c3de000000095989c2702fe0a5863a0000b1b5281300004112c3c3f2ba442f13b5a543b35b0b4780aa6ed350b4d019a6873400014f4249400005c049c00062a800024800062c98a530e6330000acd89000000000000000000000358000000195b3c11c087a0001118f36d2200033310227a932511740007950002f6509e00f000000065e0004ed8fa078015f4b294c8e6e0000001ff110c4fe000024965c94c18505dd8b663d491938cef66da2daa6f81ca6f6077af78eb409b41188a80f65963fd0e01a0ea4846c244c3480003f20ca41a65ed4bc8000e9ca3741780000004ae000079cbd080200033c8efe46000011c80009e522025ecd380000f829802ba42c45f9d980002972bdb4448c400000000014c2a6e00001a10ac16d0000
  | 24 => 0x2d5531ec173b9991c9ce3bc268b25ce4e2e31d1800000000059e03700000000001d5c00015e56d34d80008f561022a000000049b1318dd0b9800007d80003724bf2a2c55a31760a237150031c00000012380de3cb000000097d59aa1715c00001ed8ec49de1e020f84493f27f6600244133039f21b9495624bd769fa025a886ce20626f10e00004e732017162332cf02f8000a9839030400000d52e42df0000c5d07a80008007695570000f94af45130d54ef420d6018b1061c0a9262800000000000b00000008e6000000162c0f607d825ce7aade0000001a3028f47680000002a6000068d166d301761ec073a9a142c800090600027caad900a1ff4b8a9cc80633a6760eb400056d0358000fdc49f02b0b340000005c0b03000000000009084f074a4a21b1424ebdd224934c65490b3eb10504be3c263b0000000146272200d7fc3421571080000ab855900016522836a280007ea83140780017c800065eab280000005810000c9858b17788859b22e56818d9c87895200019a000000000a0000e5ca3f33f2b4d93096155222802e48631ea22f00ec03641a1a90c4c838376000122c5f20000ac400061722a80000004ec0002dad3ac66307a14e079c1d600013cc000a9c23d9094aeaad93240b687bad270242ffcc404612b488780c21f40f933a06f40742a1845c2b684114c8cc10fc00025c9734f0a81c4979e614525946239da80b63350868e580e07d41c70c8d6aeaaf5202d0162825116ea15cd309e0000037583408d368abd499a4c73b421912107102ff0b805ea7556382c249c2aed20ba4b00000000cdab5919a55a5a7965483c42e372959da1c66e5679a3469244435ea9d90dc6dd5ed02d400051100e91509f0c054280f350949af1c11e290da5900c5800000000033e9f987aa9c55b40000962000006800074e5084dd16f0c466a900000000000d916099580de00056633697ac71b615975995e05a5c1831d3ecbd8445000127abfa0b2800047228d45cb1509be3f2121a4398f6a7d1bd8000fca64156a053014a09e09588b02c000046f2c295d45105dc0ea5a5a26a480a35018071400b9e381fc9552ba307d23c0d838c8a1c54200018100018f82140402848000a091ed1f457fa0ae3b9088908659b6708d4c3d03a100002f56de4075c9b284f200001321c5800000000028bc4b634e5389df4d50a0f14d800000020300013740000000000000000a3d1f48be0c7c8b861baee909c0000002bcc000b9165b8000c220004a4b414d6600002f2a4cc9a9aa481a98c1f299952a00019164740889b9835e4fc5781ac19b0bdf05fade0178c8d65829380000e33f19634a7c500258199d7c20005b80985236542256b02c3e2a3405198b0c6acbb558a7e1a34892000272cf1888f00018dd51c7da416b2c800066d2d61a883be0000038060000
  | 25 => 0xa77182aea13fe0000172f4c00000000000000000000000000000000000000000000000000000000004caa828eaca960000e317840000000000a140000000000c6408747d8688950bf9000297cd5ec120a3a8b40445fa56da520cba66f24886817622600e816b40000000001b24000a53434a1540000000002b54000000000000000015423ca7c5400b9552110113ce3590000f5c0008ac4f693240006a60001a1106cbd04af80012ee57e0bd1e0572097f42e986c5846043f680004708474a89ee876808262116f84c6cf56848d1c7f055f6771b580000004ca2cdc00037d20926fc000c99000000000000033822589241ce3f925804f26d700020c96da21300002293728b61892bd85aa3372d186515f4a790988001a5600000026105c247c0003380b9c82948a9c100000000c91a190280942cc04548e0b6938910e000000012e011c0002a50501e500000600000000000a071738001a468ca0a52194e983b9653a324272a5d3fca1fc50a76449324f950e9bd000281083615262f0f889dccce20510145a08546472bc48381624388000b326ab35882cd6e629319c108538ebee1cc8000a422a81f28000f0021c4c89178cc80b722780d43d46d32409dd44f4ab73ac8d30a9a82c0ee1a087086991ada93c9e43e759da5409ecc5f2cd000000024b45f1a41740c462eb95041201784d5a0b98d236c0e4b230b9857804326dcafe742183007037857a0001ef86d27df374b0d8f3460300012d8c426c7029a21581a3835803530d5c5d04059914e107a2026285d0c28843fa140d63eccb0b7a1f467c3771631b3d1287ea03295a87d4bf6178800000000062680000004db47d00015180003a5afdc6b000024baa5000048d0851ff89c01b23e404cc00096c3e209f80000002a5800000000000000000007a61df99706ca00033600000000000002c74000d1c096ab485d20004ad96fc2f60005e2280958a1005dd9d6c3aa725000170ce2e00322db34c72248430c80112d47bf24c9725984cd44a19018f400334d312bc88e9825b38ff43205d4000012d10e058494288cd3e00025a81914342fb036a99d8fc000000000000043d60c8001a6a000000009c000bf03b715400007de13a8000000d0f15f2ebc000000300351cd102291b18adcabc25d0000cb80002cb05680013d08270000000a3a00000018340008b5508000000000000030c876e6aa06dafd554226f561800000075f2dc0b780002551a51bbd29a7820f58525a5c3c4219b13cbec2942b89968a4cbf12821784e2208100004fc00017f2a4800000000034d3220f468f627aadf92a624c6320e14c04aa90000000bdc81323303296b861353f80000000000002e1000000000010917362540001680ca00545e733480f8b9c19b20800003f600007f800000057229886be35617e03ad6108f8622
  | 26 => 0x5900000e89edc4e47280a2a3740008810000a30ac200000024ad48c000375b4c8000ab02c229d1924a2e38d0000d2c000000285169c2df2c50000d2e2a409531dc64cb85281063c30c23b68b89a520c43632d800105416c4ff0cfc54001f0559ca4e8a59c37227b800043a3b8a5789b8a6d01927a80006c80001349974be7184084426000037e00005a812e556a46071400034595cc0006e30a787f0000a3e5e5800184859d299905568221631a0000000674000163d13a1d20be009943637330d05402aa81256310d16fa4f4428a8a16c6c7d2911eb17a403c3b02fac5564d44c5a12d4aa2360002ad0f50000501b4092240000000f70f9c0005420f8d41a000000000000000000000014f85d95332fccbcac290000000000290000000000083500000c4000c850000e78894adc3f7ac1073400041423f4f5a35e39819999fe5206a321305a685b0000ac944a0004c480006d6846000000199000000022984780003e3091c1969c00cc121404a21b0000000000b4d2c32b7527e9e636d800159acad60731680000000000f31a624534acadfd87cc940ec0ba83806c000010c844c65710b8cf10bed1206b800000014e50e8000fd824100034959fc0e0000000136c1b400000000000000001b7c000b1816000018b0000005800170e000618abf4ac07480001ca800099c0000000de448a180122d0ee6fa00011b152222068f80012145ca3060ea0da498d5ac05d14541a113fa52c5e68b72ff97558ced134aa200183c0e402e9c9091c0df2f58d841c400003920f81e29205b0194c000000053344070ea7e1368d98366bdc5df800029683d064abeceeca5a4c0800026e83a461b0713c20004cbb2440007060ce067d4b60005b92dd46f08ea000076cdbc00000000000000005bd800172e0000002860000000380b1c80006ac000000000000000030d415837e06d000000000000002a82500000001afc0001c447706a8ea80000000000000000000000000092e02323c08e251911d234173cb794fd21140004f162b00001cc00052818a858ec285d832fd670a6406413291a40000ac1748b0a700100a2ac00000000000014180003d50001042280404085555870d5a423cc00004900034001fa5662f48000000b2142227a40c400000000000000006309d8800000000000008602b00001d608da46428700000008a74e2000139464f0000000000000259000000000047380012323ba00000008d02314b300003861100000824000cb80a98000000b05145348588aa990b593785a2abc0070cec228b3e37824c54584ac51d8105a1681a3cc943cbce8a509e96e80f0c890e506d52deca345192554d200013399f0b48671000024c1dc29e0b98000b023200ee8000c6c3100001d440000005b50000ca20120000b30000000000000103a99d4d8000074
  | 27 => 0x9e9421cc0305348c2c35c80000d25160b31ce53204e93d2a6b000053a1a897c40000005cf80007f4b4a15c91f8f3e61526813651ac0003a480005e003b37da0189544575ce8d889fa8246841430b240000000000622d1d000000011800000021d13b88e9000000119030d5a991485fc9f200015300000fc00003cc0008cc00032a04b4c52248000000000013a000054e39352505f4360000000151d4607840000eac0000d418600015763fc1b4000035a0006200dfc000b4b2f1abf062600935a87b53b4339315800000003958f0d40a800000002200d0a8f74fb81fcf768980003534650bb96368000602000000000000000000000001ce0d000025ac434000542b2a4e765a10002bdc000000000000000000023280000000004489bb976a2823b7b2a87a61cf472142c00038800016899f28ae2411bf87da21f59f9f09106a350200ef4d5a6cd5d6a648a02d33541800141060765c80bc8d6b1738e31e858a5725d32a9d4a233d234b29171246300030e021ea2b00013dc0000002ab882d3900001ca14140009644c283380000005412f3416c000129a81800064b1abab8924e0001f3227d16402341800011c4691083800000070b27800000002dc00000010760000000000b6418d00000000000002da1ccd550c9d41c9d000002e21e4b03da8413514227515d603f2759d0400000000000003cc580490860d27400068200010e4cac00024b43e669d14c27480001e20001158b7a4b41cd80001fe07700080013500005a600017461b760a8c3cb5e2b535c16acf8e5566328fc433412f1491620b06250609a0949cc9630f48e2d21849c43c171d56a9d357181400007d216526815feceb000019d9a0a920003170000000000059000083709a000000024a1c917089463a21360ee126e78328686b10a63c81b82814fe087304f97e40000c63200c6c9b40000000000000cef38a800000044c0ad32c58540004698000616cf15bd148c0001323db2a3d48a5d137388ac0004a427100005e41fb00000000002bc00000015bea7a1998164000d1926c0ffc00006e3ee13540003d169f000018400000000000000006412304000d0643c8384000000145a6b52f00000002c950800001552d409823f3000000187a0005aa1ed118c0002fe9a8d47079169c80000000000002a28000000000286565a9721b221ec4d0cfa14f848800000031e34e168ca723122c719ee8c266db1a92785a56168874000c0263980b4b8057d5db8000c1c5972b79170f7097a20482c91266ca17bb14074c01948fa2387e096900000007c800051117d000000044c80000004cc631af94adc4513d20f8081aa395af9b500423f405834541a435450b2dd8a5ad3c4a099cd392a2769ead1186649b12c337553e61c560800000055363587304204d62f31e25066b2f4982f24846b7400
  | 28 => 0xcca4dc1df800096d47a000000000000019ac1989ec0000000dfe4ab000000103e1c60c2800000000022700d000000000000018126445a11de18a20d146fb39c7acc9f2dda3943c8bc66128000cea90d0d72cd0000980399000000000000019d8bb64b836603a0e14000000000034cb0b17e800190c47701416d8a4898c3128000a2400000821ad280234000020c4f8b4900000013fa2bd21d8df046e55227504688b4000000000199ece56798e188163d82aa266d02ac0760eb1e45da7930000054e8c5363f9800050c9d007b9b2c00021200026a4000c3b1071ff54988490000b588440004bb15899f672c5b88fb8834a6f4c30ed40000000002408df23ac5d59a3d1fe00030c1b540006bc3cf0000cb2aaa243189ce305c5694071d03261200000000e689a000312d59011c361a8c9502ce3148a8792b438f3b198b570011b3b28ed8d7c7c53919d41018c342f826593de74d65e0000bd43903590f0c8b23955d39038cbcaa367b27088f09b400029700000135728000e12000000000020497c00031252444a22bc8f64a7800043512815ae6e060c1f053449560e68910b52bb300301e80001c25d493a00007132aea474f38bf418f84f979428e07500015b0a4400db0059f89d501eac68b4c096054065800000018c8000fee7ff15d000086a0c347614d0000b4546a997c37608b00009ac0007cb34f00017542b44929c7854449e67527440140002f787159fa5391b89511934223216a32c0004b765f000000000026004250ea0000000000f6200042106a4000736393282cdeebe824409f4c3eabd37eb34553452b0f1af31a58c2f0fbac04000b223ae18297825e20001b41294aa263f80006286832498110c841592a70500b7232c321841400000004aa7d172400036083c9a9cb1b53a800153a303378800976c52e3d78bd08d48c728e055ce3a04a0b3aafc776cc3445b280de62d94f81859152a593a3af219201a833f96a00c649d611a2407f266133ba4d00009b5381a92c0000005e780010c422823728456d839c34999483c211811f06953f86393c385a8e7c88c04d0d058de9b149c1c1c000000089840c4c444d0002e08000000264235c8fa7e0662a29020200013995ac4b2aa03b380004ee00037c0d146125dc0b71098000b0d0001cc400000018ab4dc432c9e5072a555843e130f28550366c26620474a500002fb80e0aca68c38633a515e7520a40478a3e548000000000000000016c431478f00015c11040000000000000d41120277c94c02b4cf0000000a8833002649
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe6a1055162040e7cd220aa2c4081ca9ba14545881000537c2ae6b102000a6c855cd62040095c902b9ac4080029ba14735881000536c28e6b102000aae841cd620400155b0839ac40800393d4e535881000477438a6b1020008ed8714d620400155d0829ac408002ab61053588100053742e86b102000a6d85d0d6204001c5aa9a1ac4080038b55143588100047743886b1020008ed8710d62040014dd0a21ac4080029b614435881000557426a0b102000aad84d4162040095cd02282c408002b960450588100053742e80b102000a6d85d016204001c5aa9202c4080023ba1c405881000476c3880b102000a6e8510162040014db0a202c4080038b55040588100056741880b102000acd8310162040095cd02202c408002b9604405881002477c3ac5990200387c85dd932040091d905bb264080021fe15764c81001c3e42aec99020048f4815d932040010fb0dbaa64080030f993754c8103862f31eea990206fc6e62dd532040010fd0eb2a64080021f21d654c8100061fbaac89902000c3c755913204009968e2b2264080123721d634c8100062fbaac69902000c5c7558d32040091d90eb1264080031bdd5624c810006363aac49902000cb564dc532040019aac7b8a64080033958b714c8100265b38ac91802000cb5645c630040019aac6b8c600800e1f217764c0100145e426ec98020048dc83dd930040390fb0dbaa60080030f993754c0102e62f31eea9802000c6e62dd530040010fd0eb2a600801e1f21d654c0100061e3a2ca980201b8bd86dd1300400187ccbba260080030f597744c0102de4f31ee89802000cae62dd1300400117d0eb22600801a2f21d644c0100061fbaac89802000c3c7559130040018beeab1a6008003171d5634c0100064fba2c69802000c9c7458d30040018deeab1260080031b1d5624c01000657ba2c49802000cac7458930040091bb06bb060080131d9c5650c0100265b38ac81802004ce67158830040018eacab8860080032d591710c01004e6b31ae21802000ce5625c4300400996ce2b2440080123be1d62880100065ab22e31002000ce5625c620040018e8ebbb220080032d1d376440100063bc2eec8802000c7485dd9100400196f09bb220080032d21376440100063baa6ec8802000c7554dd910040019af07bb220080033520f764401000673c16ec8802000ce482dd910040018eeedbaa20080032dddb74440100055b43ac88802038ab4875911004001c6d0ab2220080038d61564440100071bbaac88802000e3475591100400996ee0b222008013acdc164440100066bbb6e68802000e9564dcd10040019aeec39a2008003a5590734401000673bb6e48802000ea564dc910040019ceec3922008003a95907244010006e2398e48802000eb1648c110040016e70a9822008003ac5913044010
  | 1 => 0xb0e214c60800297a144298c100052ec28853182000a9e84d42630400153b09a84c60800297a174098c100052ec2e813182000e1d5490263040131bd0e204c6080023761c4098c100052f428813182000a5d851026304001c3aa8204c608002b3a084098c1000566c10813182004ad68110263040015ab02204c60802637a1f2098c100046ec3e413182000a5e85c8263040014bb0b904c608002a7a132098c100054ec26413182002c3e74551630400187ae8aa2c60801237a1f5358c100062fbaea6b182003c5e7594d63040091b90ea9ac608002a7a105358c100054ec20a6b182000ace8214d630400159b0429ac60801237a1f4358c100052f42e86b182000a5d85d0d6304001c3aa9a1ac6080123721d4358c100070eaa286b182000a5e8510d63040014bb0a21ac608002b3a084358c1000566c1086b1820048de878c963040014bd0a192c608002976143258c100054f42064b182000a9d840c963040018beeb3aac608002a7a107558c100054ec20eab182000ace821d5630400159b043aac60800297a167458c100052ec2ce8b182000a5e851d163040014bb0a3a2c608002b3a087458c1000566c10e8b182073a5d859516304001c3ea92a2c60800387e115458c100070f3a2a8b182000e1d7455163040e7c3e82aa2c6081cf875055458c103952f428a8b182000a5f855c963040014b90ab92c608012b52057258c100052f428e4b182000a5d851c9630400153d08392c608002a76107258c100046f438a4b1820008dd87149630400153d08292c608002a76105258c100052f42e84b182000a5d85d096304001c3aa9a12c608003875514258c100046f43884b1820008dd8710963040014bd0a212c608002976144258c100054f426a0b182000a9d84d4163040095ad02282c608002b56045058c100052f42e80b182000a5d85d016304001c3aa9202c60800237a1c4058c100046ec3880b182000a5e8510163040014bb0a202c608003875504058c100056741080b182000acd8210163040095ad02202c608002b56044058c100046f43e40b1820008dd87c8163040014bd0b902c608002976172058c100054f42640b182000a9d84c8163040095ad02102c608002b56042058c100161f3a2a8b102000c3d7455162040091dd0fa92c4080123b21d52588100247743e84b102000a6e85d0962040014db0ba12c4080038b55342588100247643a84b102000e2d54509620400155d083aac408002ab610755881000567418eab102000acd831d562040014dd0b3a2c4080029b616745881000537428e8b102000a6d851d1620400159d063a2c408002b360c745881039735086a8b102072e6910d5162040e74db0b2a2c4080038bd52545881000717c22a8b102000e2e745516204001c5ae8aa2c4081cf8bd05545881039f16a0aa8b102073
  | 2 => 0xb72481101ee743b6c49022000bb1841c5204407bbc6e438a40880127a21d2148110026743b2429022004de07148520440898ecedb2c208810f2d9db64841102166b3b6c70822009cd67618e104407b9ccedb142088007399d8628411000762318c5082207387d879d1650400187ee93a2ca080030fe1174594103943f438e8b282000c5f739cd650400147d0839aca080028f610735941000537410e6b282000a6d821cd65040010fd0fa1aca080021f61f43594100061eba686b282000c3d7450d65040010fd0e21aca080021f61c43594100053741086b282000a6d8210d650400147d08392ca080028f61072594100052f418e4b282000a5d831c965040010fd0fa12ca080021f61f42594100061eba684b282000c3d7450965040010fd0e212ca080021f61c42594100052f41884b282000a5d8310965040010fd0e192ca080021f61c32594100051f42064b282000a3d840c965040ed4eb03382ca0801e1fa1f40594100043ec3e80b282000c3d7490165040010fd0e202ca080021f61c40594100061eba080b282000a5e8310165040014bb06202ca080029ba08405941000536c1080b282004a768110165040014eb02202ca0801e1fa1f20594100043ec3e40b282000a3e84c81650400147b09902ca0800297a0f20594100052ec1e40b282004a768108165040014eb02102ca080030fdd6755901039d1ec3ceab202072e37109d5640400187f0ebaac8081cf0fdc5755901039e1eb8aeab202000c3c705d564040e7c6e20baac8081ca8fa1475590100051f42ee6b202000a3d85dcd640400187aebb9ac8080030f5d573590100051f428e6b202000a3d851cd640400155d0439ac808002ab60873590100070fa9ca6b2020008be8714d640400117b0e29ac808002aba08535901000556c10a6b202000a3e85dc9640400147b0bb92c8080030f5d772590100061ebaae4b202000a3e851c9640400147b0a392c808002a7a0c72590100054ec18e4b2020008be87149640400117b0e292c808002a7a0c52590100054ec18a4b2020008be870c9640400117b0e192c8080028fa1432590100051ec2864b202000c3d759c164040eb56b03382c80801a2fa1f50590100045ec3ea0b202004ab681941640400156b03282c808012ada0450590100055ac08a0b2020068be87c81640400117b0f902c8080028fa1720590100051ec2e40b202000a9e83c81640400153b07902c808012ada0420590100055ac0840b202073a5d859526304001c3ea92a4c60800387e115498c103a70f3a2a93182074e1d7455263040e7c3e82aa4c6081cf875055498c103952f428a931820098de8714a63040011bb0e294c608002a7a105298c100054ec20a53182000a5e85d0a63040014bb0ba14c608003875534298c100070eaa28531820098de8710a63040011b
  | 3 => 0x83122000acc8359062440014dd0a320c4880029b614641891000557430c83122000cae761906244001c5eca320c4880038b194641891000717428c83122000e2d851906244001d4b02320c488003aa9c0641891000754b80c83122000a6e86d5062440014d90daa0c4880031b9db541891000717b26a83122000e2c64d5062440014dd0caa0c4880029b2195418910006373b2a83122000e2f645506244001c58c8aa0c488003339db631891000727b2ec63122000e4c65d8c6244001d1ec9b18c488003a3193631891000727aa6c63122000e4d54d8c6244001d92e1b18c4880023b61e63189100053742cc63122000a6d8598c624400155d09318c488002ab61263189100056741cc631220008ef8758c62440014df0ab18c4880029b215631891000557c22c63122000aac8458c624400159d0c318c488003339d8631891000727b28c63122000e4c6518c6244001d1ec8318c488003a3190631891000727aa0c63122000e4d5418c6244001d92e0318c488003a919241189100076231c823122000ae4865046244001d48c8a08c488003c955141189100076231a82312200087f855db32440070f90abb664880022fe1176cc9100145e422ed99220018dc835db32440070fd0bbb264880021f617764c9100145f426ec99220008bd84dd932440070fd0b3b264880021f616764c9100043fc2aec992200387c855d9324400117f08bb2648800a2f211764c9100046fc1aec99220008f7815d932440070f90a3b264880021fa1b754c9100061e326ea9922070c5c63dd532440df8d8c5baa64880021fa1f654c9100043e43eca9922000c3f75d913244001878ebb22648800637a1f634c9100062fbaec69922000c5c75d8d32440131dd0fb1264880031bdd7624c910006363aec49922009cd8639c331440019b6c638262880033ad8870485100043fc2aec982200387c855d9304400117f08bb2608800a2f211764c11000477c12ec98220018ec825d930440f50fd0dbaa60880030f193754c1102e62e31eea9822000c6c62dd530440f30fd0fb2a60881121f21f654c1100061e3a6ca98220788be86dd1304400187ecbba260880030f197744c1102de4e31ee89822000cac62dd130440ef17d0fb22608810e2f21f644c1100061fbaec89822000c3c75d9130440018beebb1a6088003171d7634c1100064fba6c69822000c9c74d8d30440859a8e3b1a60880031bdd7624c110006363aec49822000caf74d893044001958e9b1260880033918b714c11000734316cb1022000ea862d922044001d90c5b1c4088003b2188638811000d75436c51022000cea76d8a2044001cd041b2a4088107351c463481101ee7238ec49022000cd463dc520440898f0edb2a40880039a18b654811021e5c3b6c89022042cd876d8d20440839b0ec31a40880073a1d
  | 4 => 0x2440014d90ab86c488002abe1170d891000556422e1b122000acf835c3624400159906b86c488002aba1350d891000556c26a1b122000a6e85d0362440014db0ba06c4880038b55240d89100047743881b12200a8ed8710362440014dd0a206c4880029b61440d891000716aa081b122000ace83103624400159b06206c4880f6b9a0440d891000572c0881b12200387e86dd562440018d8c5baac4880021fa1f65589100061e3a6cab12200087e871956244001878e832ac48800a2fa1b74589100061fb2ee8b122000c3c65dd16244001958c5ba2c4880022fa1f64589100061fbaec8b122000c3c75d91624400117d0e322c4880030fdd464589100061e3a8c8b122000c5f65dcd62440018b8cbb9ac48800327d9373589100064e326e6b122000ccc62dcd62440018beca39ac4880031719473589100064fb20e6b122000c9c641cd6244001998c439ac48800237a1f63589100062fbaec6b122000c5c75d8d624400193ee9b1ac488003271d363589100046f438c6b122000c5f7518d62440018b8ea31ac48800327dd063589100064e3a0c6b12200387e87dd562440010fb09baac4880022fe1175589100145e422eab1220008df835d562440131b906baac4880023be0975589100043f438eab1220028be87dd1624400187eebba2c4880030f1d774589100061fc2ee8b122000c3c85dd162440010ff0aba2c48800e1f21574589100046fc1ae8b1220098dc835d162440011df04ba2c4880022fa1c74589100061fba8e8b122000c3c751d162440010fd0faa2c48800e1f21f54589100061fba6a8b122002c3c74d5162440f78b8e7aa2c4880021fa1d54589100043e43aa8b122000c3f745516244005878e8aa2c4881d3171cd545891004c6f43ee6b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f54dcd62440018baa9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880031bdd77258910006363aee4b122000caf74dc96244001958e9b92c48800333dcf72589100066639ee4b122000cd473dc562440018dcedb28c4880029b613651891000734b86ca31220008ed8799462440014dd0b328c488002aba12651891000556c24ca3122000ace83994624400159b07328c4880023be1d651891000557c22ca3122000aac84594624400159f06b28c488002b320d651891000537430ca3122000c6e7619462440014db08328c4880039a9c0651891000734b80ca3122000cae76d906244001c5ecbb20c4880038b197641891000717c2ec83122000e2c85d906244001d52e1b20c4880023b61e64189100053742cc83122000a6d85990624400155d09320c488002b3a0e641891000566c1cc831220008ef8759062440014df0ab20c4880029b215641891000567c1ac
  | 5 => 0x8002b360b4118d100070eaa28231a2000a9e84d40634400153b09a80c68800297a174018d100052ec2e8031a2000e1d5490063440131bd0e200c6880023761c4018d100052f4288031a2000a5d851006344001c3aa8200c688002b3a084018d1000566c108031a2041ad68110063440015ab02200c68802637a1f2018d100046ec3e4031a2000a5e85c8063440014bb0b900c688002a7a132018d100054ec264031a2000a5f8544063440014b90a880c688002a7e111018d100054e4222031a2000c3f745536244005878e8aa6c48800e3be1d52d89100053742e85b122000a6d85d0b6244001c5aa9a16c48800a3be1d42d891000716aa285b122000a6d84d97624400155d0932ec488002ab61265d89100056741ccbb122000acd83997624400155f08b2ec488002ab21165d891000567c1acbb122000acc8359762440014db0832ec4880038bd9764d89100071632ec9b122000e2f85d936244001c590bb26c4880029ba1664d891000536c2cc9b122000ace83993624400159b07326c4880029be1564d89100053642ac9b122000acf83593624400159906b26c4880029ba1464d891000536c28c9b122000e2f651936244001c58ca326c4880038ba1464d891000716c28c9b122000ea58119362440014dd0daa6c4880029b21b54d89103ee373b6a9b122000e2f64d536244001c58c9aa6c4880029ba1954d891000536432a9b12207cc6e765536244001c5ec8aa6c4880038b19154d891000727b2ec7b122000e4c65d8f6244001d1ec9b1ec488003a319363d891000727aa6c7b122000e4d54d8f62440014dd0b31ec4880029b61663d891000557424c7b122000aad8498f62440014df0ab1ec4880029b21563d891000557c22c7b122000aac8458f6244001c9eca31ec4880039319463d891000747b20c7b122000e8c6418f6244001c9ea831ec4880039355063d89100075232483b122000f2554507624400155d093aec488002ab61275d89100056741cebb122000acd839d762440014dd0b3a6c4880029b61674d89100056741ce9b122000acd839d362440014dd0a3a6c4880029b61474d89101ed73408e9b122000ae5811d36244001c5ea92a6c4880038be1154d891000717ba2a9b122000e2c7455362440014dd0bb9ec4880029b61773d89100053742ce7b122000a6d859cf624400155d0939ec488002ab61273d891000727a9ca7b1220008ee8714f62440011db0e29ec488002aba1053d891000556c20a7b122000a6e85d0f62440014db0ba1ec4880038b55343d891000716aa287b1220008ee8710f62440011db0e21ec4880029ba1443d891000536c2887b1220008ee87d0762440011db0fa0ec4880029ba1741d891000536c2e83b122000e2d54d07624400159d07a0ec488002b360f41d891000716aa283b122000a6f855c36
  | 6 => 0x656396c8b1a20008be87191634400187eea322c6880030f1d46458d1000656390c8b1a2000c6f65dc963440018d8cbb92c6880032bd937258d1000656326e4b1a200087d84dd5634400117f08baac68800a2f2117558d100046fc1aeab1a20008ef825d563440031d904baac6880030fdd77458d100061e3aee8b1a2000c3f85dd163440018790bba2c6880021fe157458d1001c3e42ae8b1a20008df835d163440011df04ba2c6880063b2097458d100061fba8e8b1a2000c3c751d163440010fd0faa2c68800e1f21f5458d100061fba6a8b1a2002c3c74d5163440fb8d8e5aa2c6880021fa1d5458d100043e43aa8b1a2000c3f745516344005878e8aa2c6881f31b1c95458d100062fbaee6b1a2000c5c75dcd634400193ee9b9ac688003271d37358d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000667b9ee4b1a2000c6f54dc963440018daa9b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d1000672396e2b1a20008df8758c63440014bf0ab18c688002972156318d100054fc22c631a2000a9c8458c634400159f04b18c688002b32096318d100062f3b6ca31a2000a5d84d9463440011bb0f328c688002a7a126518d100054ec24ca31a2000ace82994634400159b05328c68800237e1d6518d100054fc22ca31a2000a9c84594634400159f04b28c688002b32096518d100062f3b0ca31a2000a5d84194634400193cedb20c68800387d976418d100070e32ec831a2000e1f85d906344001c390bb20c6880023761e6418d100052f42cc831a2000a5d85990634400159d05320c688002b360a6418d100046fc3ac831a2000a5f8559063440014b90ab20c688002b3e096418d1000566412c831a2000a5e8519063440014bb0a320c688003279d86418d100070fb28c831a2000e1c651906344001c3d0a320c688003876146418d100074ac08c831a2000a5e86d5063440014b90daa0c688003179db5418d100070fb26a831a2000e1c64d5063440014bd0caa0c688002972195418d100062f3b2a831a2000e1f645506344001c38c8aa0c68800297a166218d100052ec2cc431a2000a9e84988634400153b09310c688003a51924118d100078aaa28231a2074a5d859506344001c3ea92a0c68800387e115418d103a70f3a2a831a2074e1d7455063440f74bd0a2a0c68802637a1c5218d100046ec38a431a2000a9e84148634400153b08290c68800297a174218d100052ec2e8431a2000e1d54d0863440835ad03a10c688002b56074218d100070eaa28431a20098de8710863440011bb0e210c68800297a144218d100052ec288431a20098de87d0463440011bb0fa08c68800297a174118d100052ec2e8231a2000e1d54d04634400159d05a08c68
  | 7 => 0x9f84597634400153908b2ec688002b3e0965d8d1000566412cbb1a2000a5d841976344001c3ecbb26c6880038719764d8d100070fc2ec9b1a2000e1c85d9363440014bd0b326c6880029761664d8d1000567414c9b1a2000acd8299363440014bf0ab26c6880029721564d8d1000567c12c9b1a2000acc8259363440014bd0a326c6880029761464d8d100070fb28c9b1a2000e1c651936344001c3d0a326c6880038761464d8d100074ac08c9b1a2000a5e86d5363440014b90daa6c68800387d9354d8d100070e326a9b1a2000a5e8655363440014b90caa6c68800387d9154d8d100070e322a9b1a2000a5e8598b63440014bb0b316c688002a7a1262d8d100054ec24c5b1a2000e94649076344001e2aa8a0ec688002a7a1275d8d100054ec24ebb1a2000ace829d7634400159b053aec688003175d475d8d100052f42ce9b1a2000a5d859d3634400159d053a6c688002b360a74d8d100052f428e9b1a2000a5d851d363440855ad023a6c688002b560474d8d100070faa4a9b1a2000e1f845536344001c3ee8aa6c688003871d154d8d100052f42ee5b1a2000a5d85dcb63440014bd0b396c6880029761672d8d100054f424e5b1a2000a9d849cb63440015b500396c68810ab660072d8d100046f438a5b1a20008dd8714b634400153d08296c688002a761052d8d100052f42e85b1a2000a5d85d0b6344001c3aa9a16c6880038755142d8d100046f43885b1a20008dd8710b63440014bd0a216c6880029761442d8d100046f43e83b1a20008dd87d0763440014bd0ba0ec6880029761741d8d100070eaa683b1a2000ace82d07634400159b05a0ec6880038755141d8d100054f426a1b1a2000a9d84d4363440014bd0ba06c6880029761740d8d100070eaa481b1a20008de8710363440011bb0e206c68800297a1440d8d100052ec2881b1a2000e1d54103634400159d04206c688002b360840d8d102156b40881b1a2000ad58110363440851bd0f906c6880023761f20d8d100052f42e41b1a2000a5d85c83634400153d09906c688002a761320d8d1004e2e31aeb31a2000c3e74d9663440018dce5b2cc6880030f9d06598d1000637390cb31a2000c3f655d26344001878caba4c6880272718d7498d100061f3aec931a2000c3d75d92634400195ce5b24c6880030f9d46498d100061eba8c931a2000cae7219263440018bcebb1cc688003175d76398d100064f3a6c731a2000c9d74d8e634400199ce5b1cc6880031bd957298d100063632ae531a2000caf645ca6344001958c8b94c68800333d8d7298d1004e6631ae531a200087e87d956344001878e9b2ac6880031b1cb6558d100043f438cab1a2000c3c7419563440018d8e432ac6880030fd977458d100061e32ee8b1a20008be87d91634400187eebb22c6880030f1d76458d100
  | 8 => 0x396ca881129e60072d95100043f43e85b2a200087d87d0b654400187ee9a16ca880030fdd142d95100043f43885b2a200087d8710b65440014bd06216ca880029760c42d95100043f43865b2a200087d870cb654400147d08196ca880028f61032d95101b53d406e3b2a200087e87d0765440010fb0fa0eca880030fdd341d95100052f41e83b2a2000a5d83d0765440014dd05a0eca880029b60b41d95100061fba283b2a2044e344150765440890fd0fa06ca880021f61f40d95100043f43881b2a200c87d8710365440014bd06206ca880029760c40d95100053741081b2a2000a6d8210365440894ed02206ca880029d60440d95102243f43e41b2a200087d87c83654400147d09906ca880028f61320d95100052f41e41b2a2000a5d83c83654400147d0dbaec8880030f9db75d91100051f430ebb222000c3e761d7644400187cedb2ec8880022f61e65d91100051f42ccbb222000a9e83997644400153b0732ec888002aba0a65d911000556c14cbb2220008bf87597644400153f06b2ec888002a720d65d911000557c12cbb222000aac82597644400147d0c32ec8880030f9d865d91100051f42cc5b222000a3d8598b644400153d07316c888002a760e62d911005d5b436e3b222000d3775dc7644400187ae3baec8880030f9c375d91100061e386ebb222000a3e859d7644400187aea3aec8880028fa1c75d91100061f438ebb222000c3f75dcf644400147d0b39ec8880028f61673d911000557414e7b222000aad829cf644400147f0ab9ec8880028f21573d91100061fbaae7b222000e1f5394f644400117d0e29ec8880022f61c53d911000557410a7b222000aad8214f644400187eebb96c8880028fa1672d91100051ec2ce5b222000a9e839cb644400153b07396c8880028fe1572d91100051e42ae5b222000c3f755cb64440fd57500396c88810eae60072d91100045f438a5b2220008bd8714b644400153d06296c888002a760c52d91100045f43865b2220008bd870cb644400147d0a196c8880028f61432d91100061fbaee3b222038aba80dc7644408717d0fa86c8880022f61f50d911021c5f43e41b2220008bd87c83644400147d0b906c8880028f61720d91100054f41e41b222000a9d83c83644400187ee8aa6c68800b0f1d154d8d100062ebaea7b1a2003c5c7594f63440071bf0ea9ec688002a7a1053d8d100054ec20a7b1a2000ace8214f634400159b0429ec68800297a1743d8d100052ec2e87b1a2000e1d54d0f63440051bf0ea1ec6880038755143d8d100052f42887b1a2000a5d8510f634400159d0421ec688002b360843d8d100052f42865b1a2000a5d850cb634400153d08196c688002a761032d8d100052ec26cbb1a2000a9e84997634400153b0932ec688002b3a0a65d8d1000566c14cbb1a2000a
  | 9 => 0x61185200056a41ac230a40048de839db31480095a902b1e62900123e219708c5200246e43ac698a4004ad48158d31480010ff0abb0629000e1f215760c5200045fc22ec18a40028bc845d831480011bb0fb1862900123e219700c5200267830ae018a400d8ee861c121480031bf0eb1c609010ab5205638c1200046fc3ac61824041ad48158c30480031d90cb8c40900f739185718812000477c12eab1e20018ec825d563c400587ce8aa2c7880030f5d15458f100046fc1aeab1620098dc835d562c400587ce8aa2c5880030f5d15458b100043fc2aec996200387c855d932c40091b90eb1a6588006b3209634cb1020c6fc3ac798620018ee82dd763840011db05baec7080030fdd154d8e100161e3a2a9b1c200387e87dd563840010fb09baac7080022fe117558e100145e422eab1c200087e871d5638400517d0fba2c7080030fdd77458e100061e3aee8b1c2000c3f85dd163840018790bba2c7080021fe157458e1001c3e42ae8b1c20008be871d1638400187eea3a2c7080030f1d47458e100043f43ea8b1c200387c87d51638400187ee9aa2c70800b0f1d35458e100043f43aa8b1c200087c87551638400187ee8aa2c70800b0f1d15458e100164e3a486b1c20028dc8750d6384005938e8a1ac708003875514358e100046fc3ac631c20098de83dd762840011bb07baec5080030fdd154d8a100161e3a2a9b142000c3f745516284005878e8aa2c50800a3b21d4258a1000716aa284b14200087f855db32840070f90abb665080022fe1176cca100145e422ed99420018dc835db32840070fd0b3b265080021f616764ca100043fc2aec994200387c855d9328400117f08bb2650800a2f211764ca1000c6f43ec69942001ace82d8d32840851bf0eb1e630800237e1d630c2100247743ec49042000be181d8920840093d10e90a41080021fa1b74d951001c3fc3ec9b2a2000c3d74d9365440010fb0f326ca8800297a0e64d95100052ec1cc9b2a2000a6e8299365440014db05326ca880021fe1d64d95100052fc1ac9b2a2000a5c8359365440014df04b26ca880029b20964d95100643ec38c9b2a2000c3d74193654400187b0e326ca880038d60464d95100051f424c5b2a2000a3d8498b65440014bd07316ca880029760e62d95100071a32483b2a2000d37745076544001c68c8a0eca880021f61e74d95100061fc22e9b2a200087e871d3654400187ae83a6ca881129da0474d95100053ac08e9b2a2000a3e849cf654400147b0939eca880029ba0a73d951000536c14e7b2a2000c5d731cf65440010fd0fa1eca880021f61f43d95100061fba687b2a2000c3f7450f65440010fd0e21eca880021f61c43d95100053741087b2a2000a6d8210f654400147d09396ca880028f61272d95100052f41ce5b2a2000a5d839cb65440ff4f5
  | 10 => 0x182605bc9e76d92304c0131b90cb8c609810b35185718c1300161f3a2a8b106000c3d74551620c0131d90ea92c4180263b21d425883000716aa284b1060098dc835d5610c0011df04baac2180063b209755843004c6e41ae8b086002c3e74551610c00187ae8aa2c2181063721d325843000e6639264b0860098f487545610c0131e90ea0ac2180038d55141584300062faa2ed1886000c5d545da310c0010ff0abb2421800e1f215764843004e6639ac490860018f487585210c0018b8ebbb26018003271d3764c0300062faa6ec9806000c5d54dd9300c0018beedbaa601800327ddb744c03020c6e43ac29806041cd471585300c0010fb0f3aec7100028f61275d8e2001c3fc3aebb1c400087f845d763880070fd0bba6c7100021f61774d8e2001c3fc3ea9b1c400087d87d5363880010ff0eaa6c7100021f61d54d8e200061fba2a9b1c4002c3c7455363880018dceab96c71000297a176398e200061fba2a8b1c4002c3c7455163880014bd0bb9ac71000237a1f5358e200062fbaea6b1c4000a9d8414d638800159b0429ac71000a3721d4358e200164e3a286b1c4000e1d5450d63880011bf0eb18c7100030fdd154586200161e3a2a8b0c400387e85dcd61880010fb0bb9ac31000a3d21d41586200071aaa282b0c4004cb6615d061880011ef0eb08c3100032d5d1611862001c3f42ced98c400087d859db31880091bd073b663100273398d72cc6200247cc34e118c40048f9869c031880811df0cb8443100273398d720c22000476c16ebb1a4000c3f745536348005878e8aa6c6900038b55142d8d2001c3f43eeab1a400087d84dd5634800117f08baac69000a2f2117558d200047bc0aeab1a40048f4815d563480010fd0e3aac69000a2fa1f7458d200061fbaee8b1a4000c3c75dd1634800187f0bba2c6900030f2177458d200043fc2ae8b1a400387c855d163480011ef02ba2c6900123d2057458d200045f438e8b1a4000c3f751d16348001878ea3a2c6900021fa1f5458d2001c3e43ea8b1a4000c3f74d516348005878e9aa2c6901cb1d1c75458d200043f43aa8b1a400087c87551634800187ee8aa2c69000b0f1d15458d2039e3a38aa8b1a4002c9c7490d63481059a8e321ac69000a3721d4358d200164e3a286b1a4000e1d5450d63481039a8e2a1ac69000a3b21d4258d2000716aa284b1a4000e8d4350963481019c8e2a12c6900031ddd77158d200063a3aee2b1a4000cb774dc56348001968e9b8ac6900031dd537158d200063aaa6e2b1a4000c77751c563480018e8ea38ac6900032ddd07158d200065a3a0e2b1a4000cd7731c563480019cee438ac69000237e1d6318d200056a40ac631a4000c3f745536148005878e8aa6c2900021fe1573d852001c3e42ae7b0a40008bf845cf614800517908b9ec2900023de1d
  | 11 => 0x4c00187eebb96c8980028fa1672d91300051ec2ce5b22605ba9e839cb644c00153b07396c8980028fe1572d91300051e42ae5b226000c3f755cb644c00117d0e296c8980022f61c52d91302dd4f418a5b226000a9d8314b644c00187eebb8ec8980028fa1671d91300051ec2ce3b226000a3f855c7644c0014790ab8ec8980030fdd571d91300054fc1ae3b22605ba9c835c7644c00155f04b8ec898002ab20971d91302dd4f418e3b226000a9d831c7644c00117d0e28ec8980022f61c51d91300045f43843b2260008bd87087644c00147d0a10ec8980028f61421d91302dd4f41843b226000a9d83087644c0015750010ec898002ae60021d91302dc5f43ea1b2260008bd87d43644c001c76a1286c89816e2fa1f20d91300045ec3e41b226000a3e85c83644c00147b0b906c89816ea7a0f20d91300054ec1e41b226000c3f74553624c005878e8aa6c49800b271d143d89300070eaa287b12600087e87d95624c001878e9b2ac4980021fa1c65589300061e3a0cab126000c3f65dd1624c001878cbba2c4980022fa1f64589300061fbaec8b126000c3c75d91624c00117d0e322c4980030fdd464589300061e3a8c8b126000c7765dc5624c0018e8cbb8ac4980032dd9371589300065a326e2b126000c77651c5624c0018e8ca38ac4980032dd9071589300065a320e2b126000ce4621c5624c0010fd0dbaa64980030f193754c93038c3f43eca992606f87c87d95324c0b9c9865b2a64980030fdd7644c9300061e3aec8992605be8c32d91324c00187ee8aa6c29800b0f1d154d85300056ac1843b0a6000af180087614c00187ce9b2cc2980030f9d065985300061fb2ae930a6000c3c655d2614c00187cebb24c2980030f5d764985300061f3a8c930a6000c3d75192614c0070fd0dbaac2980021fa1f65585300061e3a6cab0a6000c6c72d95614c0010fd0e32ac2980030f1d0655853000636390cab0a60028be86dd1614c00187ecbba2c2980030f19774585300045f43ec8b0a6000c3f75d91614c001878ebb22c2980032b1cb64585300045f438c8b0a6000c3f75191614c001878ea322c2980032b1c8645853000637b2ee4b0a6000c6c65dc9614c00195ec9b92c2980032b19372585300047bc3ac230a6000ae482584614c0018b8cb3b662980032719276cc5300062faa4ed98a6000c5d549db314c0018bcedb2e6298003279db64cc5300043e432eb18a6000c3c645d6314c0010fb0fb2c62980030f9d3658c5300045e432e918a6000c3f655d2314c001878caba462980022f61f648c5300061f3aec918a6000c3d75d92314c001caeca30a62980021fe15768853001c3e42aed10a60008bf845da214c00517908bb4429800e1fa1776485300043ec2eec90a60028be84dd9214c00117b09bb24298173179db658c1302e72db06cb
  | 12 => 0x263b21d5258b3004c7643a84b166000e2d5450962cc001d1a86a12c59800b0f9d154587300061eba2a8b0e60418df865ce21cc00187ee8aa2c51800b0f1d15458a300147643a84b146000e2d54509628c0031bf0cb8665180031b1d5624ca3037e2fbb6ea994606fe4e62dd5328c00359f0cb12651800356dd7704ca300061fba2a8b0c6002c3c74551618c0851bd0f992c31800a3d21d41586300071aaa282b0c6004cb6615d0618c0011ef0eb08c3180032d5d161186300265b30ae918c6000cb574586318c0851bf0eb0e611810b359c561cc2300043f436e9b2a600387f87d93654c00187ae9b26ca980021f61e64d95300043fc3ac9b2a601c87d87193654c00187ae8326ca980029ba0864d953000536c10c9b2a6000c3d87193654c001c3b06326ca980038ba0864d953000716c10c9b2a6000e1c6490f654c001a3ee8a1eca980038719143d95300051f424c5b2a6000a3d8498b654c0010fb0f3a6ca980030fe1174d95300043f438e9b2a6000c3d741d3654c0b94bd063a6ca980029760c74d953000537410e9b2a6000a6d821d3654c0014dd05b9eca980029b60b73d953027d3d406e7b2a600087e87d0f654c0010fb0fa1eca980030fdd343d95300061fba287b2a605ca5e83dcb654c0014bb07b96ca980028fa1272d95300051ec24e5b2a605ca5e839cb654c0014bb07396ca980031bdca72d95300043f43e85b2a600087d87d0b654c00187ee9a16ca980030fdd142d95300043f43885b2a600087d8710b654c0b94bd06216ca980029760c42d95300051f424e3b2a6000a3d849c7654c0b94bd0638eca980029760c71d95300043f43e83b2a600087d87d07654c00187ee9a0eca9817297a0f41d95300052ec1e83b2a6000a6e82d07654c0014db05a0eca980030fdd141d95300043f43883b2a600087d87107654c0010fd0e10eca980021f61c21d95300051f42043b2a6000a3d84087654c0b94bd0610eca980029760c21d95300053d40043b2a6000a7980087654c0b90fd0fa06ca980021f61f40d95300043f43881b2a601c87d87103654c0b94bd06206ca980029760c40d95300053741081b2a6000a6d82103654c0014ed02206ca980029d60440d95302e43f43e41b2a600087d87c83654c00147d09906ca980028f61320d95302e52f41e41b2a6000a5d83c83654c00147d0dbaec8980030f9db75d91300051f430ebb226000c3e761d7644c00187cedb2ec8980022f61e65d91300051f42ccbb2260008bf87597644c00147d0c32ec8980030f9d865d91300dd4f436e7b226000d1f75dcf644c00147d0b316c8980028f61662d91300061eb9eebb226000c3e70dd7644c001878e1baec8980028fa1675d91300061eba8ebb226000a3e871d7644c00187d0e3aec8980030fdd773d91302755d406e7b22605be1e53d4f64
  | 13 => 0x47dc3ac03026202c3e74550604c40187ae8aa0c0988263720d75588310161f3a2a8b106200c3d74551620c401c3aa8a1ac4188123b21d52588310247643a84b106200e2d54509620c401d1a86a12c4188030fdd154980310161e3a2a930062048f987942600c4091f30f204c0188038e552409803101c3f43eeab00625cc5c73dd5600c4010fb09baac0188022fe1175580310145e422eab006279c5c731d5600c40517d0fba2c0188030fdd774580310061e3aee8b00625bc9c73dd1600c40187f0bba2c0188030f21774580310043fc2ae8b00620387c855d1600c40187eea3a2c0188030f1d474580313be4e398e8b00620087e87d51600c4070f90faa2c0188030fdd354580310161e3a6a8b00620087e87551600c4010f90eaa2c0188030fdd154580310161e3a2a8b006202c9c7450d600c401c3aa8a1ac01880f1e1d650580310247c43aa0b006202cb874901600c401c72a9202c01896fa690e40580310247c43a80b006202c3e74551638840187ae8aa2c7108038b5514258e210061fba2a93044202c3c7455260884010ff0ab9cc11080e1f21573982210045fc22e730442028bc845ce60884070fd0fbaac1108021f61375582210045fc22eab0442028bc845d560884011bf06baac1108263720d75582210145f43ee8b044200c3f75dd16088401878ebba2c1108030fe1774582210061e42ee8b04420087f855d160884070f90aba2c11080237e0d745822104c6e41ae8b044200c3f751d16088401878ea3a2c1108021fa1f545822101c3e43ea8b044200c3f74d516088405878e9aa2c1109ef171cf54582210043f43aa8b04420087c87551608840187ee8aa2c11080b0f1d154582213a62e39aa8b044200c5f75dcd60884018b8ebb9ac11080327dd373582210064e3a6e6b044200c5f54dcd60884018baa9b9ac1108033390b73582210062fba8e6b044200c5c751cd608840193ee839ac110803271d07358221016563a284b044200e2d54509608840199ee6a12c11080b0f9d154d8d210061eba2a9b1a4200c5d75d4f634840153b0829ec690802b360853d8d210146fc3a87b1a4202c9e7450f6348401c3aa8a1ec69080e1fa1f7558d210043ec26eab1a42008df835d563484011df04baac6908021fa1c7558d210051ec20eab1a420087f855d163484070f90aba2c6908023ee017458d210047c402e8b1a420087e87d5163484070f90faa2c6908021fa1d5458d210043e43aa8b1a4202c3e74551634840187ae8aa2c690803171d77358d21006363aee4b1a42008df8758c63484014b90ab18c6908273318d72cc5210161f3a2a9b024200c3d7455360484011f70eb00c09080b0f9d154181210061eba2a8302420087f855cc60484070f90ab98c0908263720d7558b300161f3a2a8b166000c3d7455162cc001c3aa8a1ac598
  | 14 => 0xe839d1658c4014bb073a2cb188029ba0a745963100536c14e8b2c6200c3f845d1658c4e50fd0e3a2cb188029be09735963100536412e6b2c6284a77815cd658c4010fd0fa1acb188021f61f43596310061eba686b2c6200c3d7450d658c4014bf06b92cb189b29720d72596310051f420e4b2c6200a3d841c9658c4d94bd06392cb188029760c725963100636b90e4b2c620087e87d09658c4010fb0fa12cb188030f5d342596310061eba284b2c620087e87109658c4010fb0e212cb189b297a0c42596310052ec1884b2c6200a3e84dc1658c40147b09b82cb1880297e0d70596313652e41ae0b2c620087e87d01658c4010fb0fa02cb188030f5d240596310043f43880b2c620087d87101658c40187ae8202cb189b297a0c40596310052ec1880b2c6200a6e82101658c4014db04202cb188129da0440596310053ac0880b2c620087e87c81658c4010fb0f902cb188028fa1320596310051ec2640b2c626ca5e83c81658c4014bb07902cb188129da0420596310053ac0840b2c6200c3f759d5648c4e747b0f3aac9188030fe1d75592310061fb9aeab246273c3f715d5648c4e787ae2baac9189ca8fa1475592310061ebaae6b246283ab7815cd648c4d7c3ca7a9ac9188028fa1772592310051ec2ee4b246200c3d75dc9648c40187aeab92c9188028fa1472592310051ec28e4b24626ba9e831c9648c40153b06392c9188022fa1c52592310045ec38a4b24626ba9e83149648c40153b06292c9188028fa1770592310051ec2ee0b246200c3d759c1648c40153f06b82c9189aea720d70592310051f428e0b246200a3d851c1648c40187aea382c9189aea7a0c70592310054ec18e0b246200aae821c1648c40155b04382c918812ada04705923116d5ac08e0b2462008be87d41648c40117b0fa82c918812ada0450592310055ac08a0b2462008be87c81648c40117b0f902c9188028fa1720592310051ec2e40b24626ba9e83c81648c40153b07902c918812ada0420592310055ac0840b246202c3e74551628c40187ae8aa2c51880b279d14358a310070eaa286b14620387e85dc1628c4010fb0bb82c51880a2fa137058a310045ec26e0b14620087d86dd5328c40187cc9baa65189be1fa1d654ca3138c3e43aca994626ce4c32595328c40187eeab2265188030f1d5644ca3135f46192c89946204cb471591328c40196ac9b8a65188030fdd154982310161e3a2a93046200c3f74551608c405878e8aa2c1188038755143582310161f3a2a9b126200c3d74553624c4051df0ea16c4988038b55142d89310043fc2ae1b12620387c855c3624c40117f08b86c49880a2f21170d8931006363aec4992626fc5c76dd5324c4dfc98c5baa6498806b3a1b624c931006abba8e299262418de86dc1324c40587ce8aa6c0988030f5d154d813100
  | 15 => 0xfb26ca990030f5d364d95320043ec3cc9b2a6400c3f74993654c8014ed03326ca990029d60664d95320043fc3ac9b2a6400c3f74593654c8670fb0e326ca990030f5d064d953237d2e43287b2a6400d1f7450f654c801c38c8a1eca991c29b21942d953200697ba285b2a6400e2c6450b654c801e1a86a16ca990030fd0b74d95320061ea16e9b2a640087d879d3654c80187ee93a6ca990030fe1174d95320043f438e9b2a6400c3d741d3654c8e14bd063a6ca991be9760c74d953237d37410e9b2a6470a6d821d3654c8df0fd0fa1eca990021f61f43d95320061fba687b2a6400c3f7450f654c8e1c3886a1eca990028fa1271d95320051ec24e3b2a6470a5e831c7654c8df4bb0638eca990021fa1f41d95320043ec3e83b2a6400c3f74d07654c8e14bd07a0eca990029760f41d953237d3741683b2a6400a6d82d07654c80187ee8a0eca990021fa1c41d95320043ec3883b2a6470a5e83dc3654c8df4bb07b86ca990028fe1170d95320051e422e1b2a640087e87d03654c8010fb0fa06ca990030fdd240d95320043f43881b2a640087d87103654c80187ee8206ca991c297a0c40d95320052ec1881b2a646fa6e82103654c8014db04206ca990029da0440d95320053ac0881b2a6400a3d84197614c80587ce8aa6c2990030f5d154d85320147bc3a83b0a6400e3554507614c8070fd0b386c2990021f61670d85320061f3a6cb30a6400a3d84196614c80187ce832cc2990030fd9574985320061e32ae930a6404cb4615d2614c80196ae9b0cc2990021fa1f65585320043f438cab0a6400a3d84195614c90d8bee632ac2990028f610651853238e2eb98ca30a64008f787584614c80147b0832ec0991c7175cc65d813200c6ec1eebb0264018dd83dd3604c8fb8bae7aa6c09900b0f9d154d81320061eba2a9b02647cc5d73553604c8011bb0f21ec0990038755143d8132016573a285b026400e2d5450b604c80399ae6a16c099003a350d42d81320051ec20cb3026485c5d73196604c8070fd0dbaac0991be1f21b75581320043f43ecab026400c3c74d95604c8010fd0e32ac0990028f61065581320061e3a0cab026400c3f65dd1604c801878cbba2c0990031dd9771581320063a32ee2b026400c77651c5604c8018e8ca38ac0990028f61065181320047dc3ac03026402c3e74550604c80187ae8aa0c0990021fe15711813201c3e42ae23026402c3e7455162cc40187ae8aa2c5988263b21d5258b3104c7643a84b166200e2d5450962cc4070fd0bb82c5988021f6177058b310145f426e0b1662008bd84dc162cc4091bd07bacc1988063ba0b759833100476c16eb30662048de83dd260cc40187ee8aa4c19880b0f1d1549833100e67392653066200c3f7455160cc405878e8aa2c1989ce1f61e74596310061fba4e8b2c626ca5
  | 16 => 0xa0000000010000004001000800800000000000000020000000000000000000000400300000000020010020000000000000000000000000000100000000010014006000002001000600100000080000010018014000000000000c002000000000c0000000000000000000000800400400100080040000010008000012000000000400000000100000140000008000004001000000c004000001000000200300000000120000028004000005000000000a007000000800a0020008004004000000000000000000080000060000000004000001000002000000000080000020000008004004004002001c00400100680080000000040004004000000801000200100000180000000000000000000001001000000100200000020010000004004000000000000400000100080000010008000000000002000000000100000040040010018000000000000800000402900000000000010000020006000003000800200300080040000060000014002002000000000200600080000060000010004002003004800000000a0000000000001000800c00000100080340000030020004002001000001800400400000140000000018000006005000800400200000180140000000008000004000000000c000000000000400000300000000040030008010000001000000400000000680000060020000010016002000000c002003000000000800200080000100000018004004002000800000200000000040060000000000000000000800800800000000040020020000004000000001000401400e0000000000002000000c00c00000080080040000000000002000000000c00200b0040004000001001000000600500480040060000000008000000001000000000000280000000000030010000000001801400000200000000000000008000010000000000000000000300080000030040004000000000800000200100080040060000000000000001000000000a001000000000600200100080020020010014000000000800000200c001800400002c3e7455161cc80187ae8aa2c3990030fdd154983320161e3a2a9306640387e87dd560cc8b98b8e7baac1990021f61375583320045fc22eab0664028bc845d560cc8031b906baac1991e7171cc75583320145f43ee8b066400c3f75dd160cc801878ebba2c19916f271cf74583320061fc2ee8b066400c3c85dd160cc8010ff0aba2c19900e1f215745833200c6e41ae8b066400c3f751d160cc801878ea3a2c1991df271cc74583320043f43ea8b06640387c87d5160cc80187ee9aa2c19900b0f1d354583323ee2e39ea8b06640087e8755160cc8010f90eaa2c1990030fdd154583320161e3a2a8b06647cc5c7355160cc8011b90ea1ac19900b271d143583320070eaa286b06640087e86dd3654c8070ff0
  | 17 => 0x28e985c4240000000000000384410800000000000000000000003498000000000000000000052c3730000eb4261000000085884715e800000000043b1f380000000000000000000067070800000000000006f000000000010720000000000000297000203c0000db000000047e00000020b8f5800032f8a28df085718a1470b5200000005180007d40001684dd67343e90828436000000000079e000000204c00088d1d9800000000023da2608a200027c0e180003953eb8db800000015213ac0005a80000ad8da27e30ca00000004bd000000101a23a000000000077700000006620002ef000075800000000007ee82c0000000fe000000003580000000d990980000004248e04aec041000223cc8a22000000000000000000000b7a000000123c000000000000000009909684ec8600000dc158c000000000000000024000017fc00000016101740001e40030f4491a85e00007e400000031e1bfc0000000000000000000000000000000000000000000002898000000842000060801400033f82044567091c900004fa1361c500000000000000000e345ea466000063a0000c38b7c29800000023084ea000436800114c000036232000015200000010dc76c000000078c511000000000040e00002508fa0000449ed48b43260520000ae614f20695602c200000000000000c303f000094009d2528c8400000000002780000000001a103480000000000e3c000408800020e0000000000f5063f12900003966024488002000001000000200000080000000010028004008001000801400800500100040000000000000000001001000000200400000100000060000008002000000000000000000100000000010038000008001000000c00800300000000000030000004002002000000000c000001000000e001000800000200000200080000000000004002003000000000e004000000800000000000000000000000000004003000001400a000000000c0020020000000000001000000800000100000000000020010004010000000800400e005003800000400100280040040010000004002003001800c000000005001800c0040008000006000000000400000000000040020000000004000000000000000600100100140000010000004008004000000000200300180040000000000000000000000000000000000100140000000000000006000001000800c001000800000400100100000020030018000000001002800400000500000080060090000000000000000001400000300100000000000000004006000000800000200000380040000000010000004004004002000000000000100080020008000002000000000c002000000000000000300100000020010070000002000004800c00000000080000020000018000000000000002400
  | 18 => 0xc3228c0002d600000000006fd0ae000000073b000041118682f0d500000000c521a8000b12000000000000046f000000000000000000000006d000000000000000000000928000274800000000003197c07b83ca000000033400000000009fe00000000000000d12e70000c663a00000aa800021c3f900007226300000494de057c0000000000000000000000030e0000eec00000013f000000000000019acb561b41b400001b21d5000000000000000019180000000000000000000000000000000000020d84dc0000dc90845b0488323800107c06919a95500000000000978b0c000000000000000000000011645a344212d000059e0000000ef6000000000000000000000000000071df03cc8521f83e2992500219c0001e30f260001e980000000000e8117400006100022e4000000000000099e1fd0000000000756005800000085900000007363ea2d900004a0000000000000054d00015b40000000000d400004df34500000000000001920000000000000097000025983dc8a871609307042d28aa3431ad4eb22e0000000000059f00000000008c1000000000000000000000b00002ac8368f068d02618fd00000000000000000000000000000000022f00000000000001d3c000000000000000000010817d85c8147000000000000000014280001671da12bc00000000000000008580000bd800000e1660748000533000000000000019d14b50820000001e900000003f4022c00086f000044c0000004630000e3e000000000011800027180000008bd000000000000000014940004b233c1bd818000038a00009e4277038000000079000000b80000003cf0000c0e000000000049a00000016b00000000001f44b8a00017f8000ef02f00b0178c0e24613af9b885fc00000000011780000001c200000001c7800000023000000000006890000a583141c600000000000000001448f5643c1f0149c7b44f50ca80003d00003321d0c3bc1e214d1ec03d447e3f29520000272000000013856e3789a002b200000000000000003cb00001c401f0cba03800037c000000107861440f8210a840000001a7400000037a015c000436000000000a00000000000003561e38220d980000000c58e7e1ed00014882248103c100000000002b50c7cf98000073000000000000013300000000000000000031000000017e0001471390000000028800000036a0000a0c1260001dc8c280fe00000010400000f832e21ec6701a900000005a24fd000000109a3770a5000000032d00008d00002ad000000000076b2ba1c0cc568b01ab800000000000000000007e9000107c0000dc00000000000000001000b0e7ea0f704acf9a39e00000008f45c20001fcc00075b24080003f40002d780004e8000000169c000000000000000000000019bce8a00
  | 19 => 0xf407eb1f4000104a00040921a40005a5225025400087d34b1f3cea60001ee98c400000000000000000000000000f7a7b20d71c040003aa00006fc60a31833180005da7613c400004c606d0001d0915255c00015e400077d0001ff10060001b09ea40003340ee800027845500000000002a319e0e9cea402c1c5910917e0ec34c800009c00040a8000000000000000000000000000006f200000000007ec00019e99f400001714118b0e424b13571de88407fd00000000000000001aa43e666900004e45d2046000000000000000000000006de00000000001740fd8000b6e000000000096a6d328c80b44ac61138795e875074a3c285080000003e3000043c00037600000000001ff00007c60503fb000041a2ea00000000000000000800e042660000208c7a00000013f000051001c8000000000458976000074e00000000007280000a7074839a000045c8b000013e05c0000000000143c00000000012f8000000000000107a00000022cc00000008f206c00069c0620008daa3cc0c68000000000000000072c0000ec1498e2031705c00a00000000001630e2e000000043c00000000010682900d219780000000003b40000000000000153c6984d30000000042000000000017400000011d4aa48ad0001f9c69e0000428000000000000000000000008ea000000000000000000000000022789e60000000000000000000096c522340000000000000000006a066086000020d400038d000000000000000000000000001541418ad85fa0000000a080000000000e4800000000000000002398fec6d800012109807605c810282dc4481383f7000000018f000000000000000005a8000337000000000000000000000008ca00000003ec0003e000000000cd2f58000da816443504d0e2a0000000000a46000127132800067b00000000000000000000000000000000064a8310000000080000000000000074c000000020c000000000012458e2770000cae1ff29f00000000000000000f4e00000013980a84271aa00001620003ff80000007dc000000000085b00005c80000002199558084581000025c71c73d1718000c1287c000000040429f3ca80009d425d0000b380c800028a800040e03417380000006ee0c7000000000000010c800065625e11dc9720000000000000000000000000000027a1c6ce14000000000000073112501140000000000adc93c7910001978c1c2761511ae06da88e1341d74ff62ba3309b7c00032c0000000aa25280001b600000000001f6848200025217908080001d1815888e14b0d8901c0007ad0001b280b20000000000c860000000000d2200000000011121142e4800000000017a000004a54003b15f80003240db000000000006080000007f935180000000000001d50e88000031000023000000000
  | 20 => 0x324e242f139f000000000037014e0a760af00000000000000509edc00000000000009d80003260000000567000042834a1ca4480f8400018314a8b0073e00100018f81f40000001ca8d2e49d00000000000b5000135000000030c800000000000000000002a740c00004180a82318000000000285983c00000000000000000000000000000000000000000000044ca1300000003f018340007f80000fe800049c1f589300d456038e000000000044a000000063b1a214500008c739589cc000000000135800035809d17000b4733232800000065000000000000000000000e4e0002d000007fa0000001d24f160000000dcc0000000000c8c42200000000000000001eb00000000000000000000000111a12c00082a0000000ba40d70bc00000006a40000260d76413000000053c0000002214000000000169051a00000000000000000000000f306e8000000000000000000000004820a70000312000000000000046900000000002db0000000000000000048000000000000000006383b3066c00007a0909f10d4400043100000005df12f88ec7dc00006a1ee85e4181156026c00004f00000010e40000400354000000000146c6fa3522d818800008020001a2c4fe5990000f480000000d78ffc6520bc3ee800000000001900005c2000000000083600003c80000008b70f90f380000000000000b5c7a61958544f8401037b80000004e205e80000003b7105a2d4000185000000068c3c02a71a6c29a75c00000000001ab072800000000000012600005ef00000000005f13408e240000180001964c746401fa8f2d196000449000000000000000000006f300003f40001d406f80003b66fc0000000a6e0004200000000545131188c0001b0000047c000000389800000000027c89bc3ae6ed0001e24d9e0000d180002cc2cf236922800000000000001a685f0c59c880860003eb0e09088822000000091600000000000265f500000000000000a800000005bc000199406a000172800000000000023340004c4011a098000075000000000000035f80000000001808a040000000000000000000000000000000000000007ae0000000000000568000193c0d00001af02380006f20ba839ccd400021f072000000000000000000000001e8ceae000000000000008d0000ae1104000000130800000000004a00000000000fc8f6c61e00000006ec0000001af80000001bd80000001ce00014340000000000000aa667e274205c00000000000000000000000000d180000000000bee00001019d80000003b900005160a21070000000000000000000000003b8000ac200000000000000e831284c40000003a400000000002298000cc453025d84c8c08499147a2b00008ce00000006fe00000000000000000002220000000000000000069e00000000000
  | 21 => 0x2d30ab89ee000429000000000018e00002d84a9000038400000000000000005d02c690dc0003f93a3057400024600000007cc2af41390040000002ce81e0ae225422c8000a5c00011e80004b800020e00000006d90001b7089600025f999827a4021a6816cd6263500000003302873a819c4aa0000000000000000017b80f88161ac2b9121092e8ba0298dc801e4a70e295d40005cb00018a400020f00000000000000000000000000450800000000014400000002d000000009b43c50be0000b36000000000000000000000000005340358000bfc000000000090e00010a12b0a48022000077c0000003b110780000000000000c94000353000045a0000000000000233000137400000000020800007b300b000000000000000000006183172190000000000000020200000011a80004cd00003f075e0000000000b5a00000000000000ac00006740000000000000b761d100000002fc0d03690d984c829b44e214cc420000000c8803489f3cc8000df4345000043000000000008e000050143f80000000002499becba664b01f90482be00000000004108280000eacd600002b4800034e0003b380004b200000000f40003b22e09614f3e7af13600000001630000000ec651f202800037a6921ca06f8c720001819af400000002fa16906e816000040c8be7d03c795fc0003ad00005ec0000000000aa442a0003528000e1a0001998000ed444037297980001f031b80000007360001a0848e0003130cb800000000000000000001fe1b9000000000000000000000000000000000000146000000045200005427a10000000d9000000019e40000000000390d64000000000025800000013e800000035522e000000000015780003e2000041405e867000000000058044d000009800000000009ec59110980000004241dc140000031e058048ca9800000000003741b51a489100de5a2008800000000000000000001c40000000aca00032880000000001e480008b612a4500b1400000000005cc00000000001c8000000000000112e20100000000000000e98bd400076e07c800059600041f80000004672ea0c100000000000000ab40000000b707a000000015040000000eb1d9432252a30a800090a00037c812cb1e2c43b8800000044100000000000c21da86780002651f8a1500000001b78dd4000000000000000000000022f86a2000000000043e466000000000069424b00009bc78000020503240000000734000000000000000000000000000000001b200000000260000000000000000000000000000000000003273080000dfc36900014ac00000036480000000002629acc2de0000f593b4baa4f0169935c00062d0000000ee000000000007a8000000000044400000000000000000000000000000000000101200002519b40000000001
  | 22 => 0x80000000000000000bd2000000000000000000003c000028020b9c64e6a00005b2300a7e00000000000000000000000e5804400019c0d1047126a85d8bf042500000005788080000fa40001400000ec4fee7bb00a80005a8000000000000000000000000007111ac9de400000000000008123090000000000000423000038078d41587dc0006c5211000000000000000000000740000a4800000009700005a4000000000000000000000000000000000a8088c00000000000003a21c4000000062f0001dbc0000000000000ee870029b00000560000000000e300000001f5400000000008b0000225449878c00036513580004f080a000000000000000000001e400034f9598778737393000000000000000000005023c300009420000801b3803a052000072400021800000007822b40001e5c0008bb00000001560001189cc000015500000000000002bb956c00035b10e8000a864602e38dac6220f112891c800023e000000075200015a800100869000000000000001ad20c8dce4150001abc00000043580000000cc22700000000001c18a109ce2c30001e685300002531934990000000000082c0000000000000000000000000086341c14c87e039c3c505108f21a600000008c80000000000b9847f43d00000006003fa8000eea6541c9800000000000000010f200000000000000002c1000068662800017288ae000000066400000000000000000000a29b6c0000000ad8d1cf7261323b09e80007ef00005f463681a0000000000000000000000000000000e862a85c35080000005ba28b00000007320bb800059437a0b280003760002da8000d5084e00000909b800000018141dc00000000008a47e108497680000000000000000000115000000000000000000003e4129996c7320000000e407862f309f82d0cdc2703be13c40000000000000a0e0000f7800000000000000003d8286000226d1a46d60000000028000000000000000000017b80003d800000000006773a8800015c87321a0000000000000068400000000017e40000000000c3000000008d1d906200001bf023c5204ab00000000000000000000db47470000ed837886535e0000d4e0000300cf83d20c722490ac0000002269b2c0000000001cbc000000000000000000000011f000087100000002f4000000000000000000015180000000000dc40000f5000175846c89d0000000ca600012480004ce6b6189936c000000000000109400000000005723620001828fe20000000000d1c00045700000002ee00000000000002c2000021c4503ce00000000001c3800000000000000000000000000000a345ec305800077a0001ef00001721b2000000000000032214200000002e180000000002dc8000000000298800000000004180000002f8000000036e0002f993045b2
  | 23 => 0xf0200000002283b40001ef9b34000000000000114430800011c0000000006892c00000000000000000e33d7000000079b000000000000015900009220000d68000d1e0ea0001cb80004452d980000000001ea80000005cf000000073a32a000000000027b43ba19800000000015ac0005fc00018740000000001ce47de3670000000cf8000000037463400000000000002372cb000000000025b80000000000000000000000000126cd841cc41180000ce7aa0001ce832c3a1000000045e56f000000000000032d02a400000000011d10ac3600000000bca53528b9394038000000000000000017e800000000000008a00000000b100010aa6410241bbd14a0000019554f8e8433b48a4c95c81c10b0accf8254934d220cb2443b34a827c7b22a50f3987cbc23bf09a80003cc0003292114c9c88b0c99060f9034b32c1f98dae24325500010485fb00004f8b263530001c945d8000000000000007300000000000000000458000000000000000000000c9df8000000000000000000000000000fa0000000a240005940000e9800000019d96c40006c31f2800000053d00000000000000000000000000304000112c0000000000000000000000000000040ca29c7f01fe2fa000000000021500ec0000000000fcc000000362155c4122bf3558e5c81434a3aa8f34ce4704000000105215a000000006618c0841db400004d297800000011030300009fc8950000a7400000023116f8e182cd251128d00e22900002cc03c00024000000005c431902ed03c000088862000000021780000000000000000fa600000013ec000000000000105a2710001b8c00000005f000000001b000000081e16d00003283e20000000e000000000d0132c000000000000000000046280000001dc11a83f80004d00000914c0600000021840000000c8000000025a000000000000000000006647bc346800000000028296a80000000001c38a9415414a00009602dd19410b461600000007d5102000000028c60c8c40001f7c00066c312009d10c1c340280000004ba10d0000d3000045b000000000042e80002ac0000000000000000000110c89026d0bc80010d054b00000000002fb000000082800007b000055653a113000006c48c3a589a8b7e00000012b400000031100208723001ed9cf0a4055d00000000000000000000ba20000ab99d400042800008102325971b813800000000000000fc85980001c8087a158000000000058b00000000000000001f8919e00000022280000c64180000e461530700e300000000000000b700000001c1469049a00021d10fc0123e51ee0000000000000000000000000001bc0002db162800000000014311a200000001980002c1074800000000000000000000001a08d380000000000000bba0000001e50562000085
  | 24 => 0x3800000000016a800000023900000005bc00007680000000000000000cce0002480cd84aa00000000000006e1000029884628c3bb173422a8af00000000000000a08000000000000143800000000000000000000000000000000000000000084f000089cec00000b590740002c600002580000000f083ece700002c81ef85f812741d99d000015e0001f0cd0e3ec3ed850c00000000014f000000036380008d01d90000000000492321000087400024f800000000000000000000003a01adcc3400000008f0dd40001ae8000000000000000000000000000000000000020b1c5c4302000000000000000000000005f23a0a0182e206508d9590c6c87802a811c42e5c61ae157d0a046b000000000022e39490c4bae57b000032087e00000000010160004540000000000000000000000000000c11005701240d8c21a000000000000061c000000000000034194e4b340000000000000257294800000000000000000004d219f9e100003421ba0bac0005fd2f0012400052119c800000000000000000000001730aec1960000001980d740002a3800014a2c926c05b800065d0000e94f4a72d000207400000001e00007ce2991e21f6119240837a8000ee600043622d00000000001f7800000000012d80000003e5903000012f18785a0fb274d30b00e10906c100004a46be05c0001c2c0006a000000000006b400013840000000000000d0a000000000054c17f2261ae426062a000000000009a0000000000000000000000000000000000000a00000818d5875800018040000004199344000486000000000078e0000000c360000001e1c0000003da00007301242ce00000000001d71c180000000001fb00000001aa8f080000000cf800010c00000004880000d826708644f20000000000624000000140c26662735691b838e00027780000005dc00000000001a23e4800030800033d0001156090158000019e30d227800000000002f0794052000383800000002a22e00000002c800000dcafa48e0000000000000000100c3e85b4183800044200041a1fd00000000000000000000000000000000036e80250742582361ff8b102fa0001fb4bc475e17c9dfc0f64441348000000509000000000000000000000003ed00000000005620000000f4400018c800000079d000000070a4380f022302388870c003ac00000000000000000000000000000000339800000000022b176c00000000005244060c92f68c80000000127800000042e000000000000003e03fc0000002ec8ee80000000fe00000002be00011e01e800032a9364f7e5e820c800012248326014781540000000ba0b0649542895101de80c09b9830d8c0000000000000000263931800000017780000002da0e788c80004a8000000000061200000000002d743800000000002ca800000
  | 25 => 0x10188220000000000204000000000000008705900000000003d899a0e3a7923fd0030af08750371224d80634000179c50a0ad00000000003c8000000000000000000000000000000000dd2000000000000000005
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x8f9c0d7355142d8132006075cd84196604c80103d981d065581320040fa6065dd1604c8014359419771581320050d650651c5604c80184d835c87259631006075d183101658c40182d7460840596310060d605751c1648c40181d7560c70592310060b5d5821c1648c40103d981d5644ca310160be1d5450b624c40142d941d7624c9310050725d5450d600c4014389755240580310050b25d545096088401c0d54dcd425822101607e1d5450f634840703c985d15458d210050e24174551634840141d941d77358d210050b65075dc9634840121d942156318d210160b21d54509628c00142d941d5624ca300160d21d54505618c001a0d8360864d953000507a5b7450f654c00160d9219143d95300061360f729cb654c00181f7460f41d95300060bdd182d07654c00142d929db75d913000507a5b75dcf644c00141d939c375d91300050b64a70dd7644c001435919c375d913000607dd7835c7644c00182f75e0971d91300040fa6075d91324c00703e98dd154d8e200050b652755cb638800121d94a176398e200048765285dcd638800581c875514358e200160d21d54505618800141c975514358d200160721d5450d6348113c14715514358d200160b21d545096348111c24715514258d200162321d43509634810fc847150d4258d200050725d5450d638400581c875514358e100160b21d54509628400181f7460f41d95100060bdd182d07654400141f935c775d91100050be4971dd7644400141d939c375d91100050b64a70dd76444001435919c375d911000685615811936344001615911d154d8d100048765285dcb634400181e8755341d8d100068355182d07634400181e8755040d8d1000683551821036344001a155460440d8d1000685615811906344001a15546074218d100060761d54d046344001a0d5460b4118d100060761d541006344001a0d546084018d1000685551811006344001a258560464d89100058964474553624400122d94a1773d89100060ba1d54d076244001a0d5460f41d89100060ba1d541036244001a0d5460c40d891000689551811036244001a2585604641891000589259545046244001a248655141189100078155063504624400103d94a1f654c9100040fa6075d91324400141d941d7634c9100050b65075d89324400181d7460c40594100060b5d182101650400141d931c175590100050b648705d56404001435911c175590100060761d541026304001a0d546084098c100068555181102630400121d942157258c100060761d541016304001a0d546084058c100068555181101630400122d9421573588100060b61d541016204001a0d5460c40588100068955181101620400103d9421d654c8100040f66075591320400141d941d5634c8100050b650755893204001c85641cc7244010
  | 1 => 0x1b8e83b00198003a2e168226c00048003d000001400000000000151ac72001400000003f9c4120000000e6000009c004a030f8005800078fc00380000035000004c00000010c0000000003f3488456341c130de25041410400009e8f8232f00000463c858080000000881f2d9ec2a0000000001c0004cba004003cec1a00000da000d920860b228400e630000000001000000670000c6484320005e00000001c00000b86e40000000018069a800492a000d0810003000653a94800362894c8200010b458311e00000333921452222c91c001d4397c0a003e890c4000000000000013caa4b0015c0000000000000001e08400418502e4e00134c2000c9dc000000158000030000003000000000300000400000500000100030106000c020301000100020d020000090c010504030000000005040800050105020050725d5450d60cc80181c8755143583320060ddd181993654c80703e98dd164d95320040fe6174193654c8df60c9650d42d9532386832194350b654c80103f985d074d953200607dd183d07654c80182f7460b41d953200607dd183103654c80182f7460840d95320060ddd181103654c8058378755141d85320040f66274196614c80103d94a1f655853200607dcd84195614c80181d736106518532006075cd84197604c
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x4b
  | 6 => 0x4d
  | 7 => 0x4e
  | 8 => 0x124d
  | 9 => 0x4
  | 10 => 0x94b
  | 11 => 0x94d
  | 12 => 0x94e
  | 13 => 0x124b
  | 14 => 0x124e
  | 15 => 0x138b
  | 16 => 0x138d
  | 17 => 0x138e
  | 18 => 0x98d
  | 19 => 0x98e
  | 20 => 0x128d
  | 21 => 0x128e
  | 22 => 0xcb
  | 23 => 0xcd
  | 24 => 0xce
  | 25 => 0x12cd
  | 26 => 0x9cb
  | 27 => 0x9cd
  | 28 => 0x9ce
  | 29 => 0x12cb
  | 30 => 0x12ce
  | 31 => 0x168b
  | 32 => 0x168d
  | 33 => 0x168e
  | 34 => 0xb0d
  | 35 => 0xb0e
  | 36 => 0x140d
  | 37 => 0x140e
  | 38 => 0x24b
  | 39 => 0x24d
  | 40 => 0x24e
  | 41 => 0xb4b
  | 42 => 0xb4d
  | 43 => 0xb4e
  | 44 => 0x144b
  | 45 => 0x144d
  | 46 => 0x144e
  | 47 => 0x16cb
  | 48 => 0x16cd
  | 49 => 0x16ce
  | 50 => 0xccd
  | 51 => 0xcce
  | 52 => 0x170d
  | 53 => 0x170e
  | 54 => 0x94056
  | 55 => 0x95255
  | 56 => 0x94055
  | 57 => 0x124955
  | 58 => 0x124956
  | 59 => 0x98955
  | 60 => 0x98956
  | 61 => 0x128a
  | 62 => 0x128955
  | 63 => 0x128956
  | 64 => 0x8a
  | 65 => 0xca
  | 66 => 0x12ca
  | 67 => 0x130a
  | 68 => 0x134a
  | 69 => 0x139255
  | 70 => 0x99255
  | 71 => 0x129255
  | 72 => 0x128995
  | 73 => 0x99295
  | 74 => 0xb0995
  | 75 => 0x98b15
  | 76 => 0x141295
  | 77 => 0x9d2d5
  | 78 => 0x9c0d5
  | 79 => 0x9c0d6
  | 80 => 0x1440d5
  | 81 => 0xcc0d5
  | 82 => 0xcc0d6
  | 83 => 0x12c9d5
  | 84 => 0x12c9d6
  | 85 => 0xb49d5
  | 86 => 0x9cb55
  | 87 => 0xb49d6
  | 88 => 0x16c9d5
  | 89 => 0x9d6d5
  | 90 => 0x16c9d6
  | 91 => 0x130c
  | 92 => 0x134c
  | 93 => 0x1692d6
  | 94 => 0x1692d5
  | 95 => 0x252d5
  | 96 => 0x1452d5
  | 97 => 0xcd2d5
  | 98 => 0xcd2d6
  | 99 => 0x1712d5
  | 100 => 0x1712d6
  | 101 => 0xb5695
  | 102 => 0x168b55
  | 103 => 0xccb55
  | 104 => 0xccb56
  | 105 => 0x170b55
  | 106 => 0x170b56
  | 107 => 0xb8c
  | 108 => 0xbcc
  | 109 => 0xcd6d5
  | 110 => 0xcd6d6
  | 111 => 0x17cb
  | 112 => 0x164c
  | 113 => 0x5cb
  | 114 => 0x1a8a
  | 115 => 0x104a
  | 116 => 0x104c
  | 117 => 0x4955
  | 118 => 0x4956
  | 119 => 0x10c
  | 120 => 0x10a
  | 121 => 0x14c
  | 122 => 0x14a
  | 123 => 0x1a8c
  | 124 => 0x104b
  | 125 => 0x1a8b
  | 126 => 0x95295
  | 127 => 0x95296
  | 128 => 0xd0a
  | 129 => 0xe8a
  | 130 => 0x178a
  | 131 => 0x1456d5
  | 132 => 0x1456d6
  | 133 => 0x5c9d3
  | 134 => 0x5d453
  | 135 => 0xe8d12
  | 136 => 0x104d12
  | 137 => 0x104e92
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1656
  | 6 => 3407
  | 5 => 2259
  | 4 => 136
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
  | 7 => packedAt gbK7 (67896+((h/552+packedAt gbK7 (61272+(h % 552)*12) 12) % 3517)*12) 12
  | 6 => packedAt gbK6 (178291+((h/1135+packedAt gbK6 (163536+(h % 1135)*13) 13) % 4497)*13) 13
  | 5 => packedAt gbK5 (143070+((h/753+packedAt gbK5 (133281+(h % 753)*13) 13) % 4800)*13) 13
  | 4 => packedAt gbK4 (9880+((h/45+packedAt gbK4 (9520+(h % 45)*8) 8) % 238)*9) 9
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3ff03ff03fc0fffff83ff807f49e8e7d19f3f3
  | 1 => 0xc1ffc0ffc1ff07807fc1fffffb69718ee64c7f
  | 2 => 0xfe1fff0001fff8007ffe3ff80c7181f3078f9c
  | 3 => 0x1ffffffe0000007fffc0000f81fe03f80fe0
  | 4 => 0x1fffffffffffff800000000ffe0003fff000
  | 5 => 0xffe0000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2200310024008a318024812600206340891b1
  | 1 => 0x4141406440910504204092a581283088624446
  | 2 => 0xb41aad02116ad0094eb425502c518153058a98
  | 3 => 0x101cf6bab408401277390060ce81da03b80f60
  | 4 => 0x211f38cf39bce65c021001810ffc0003d76000
  | 5 => 0x3988200c20308460042006060fffedec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeee8eeeae8c8eeeaeee8eeeae8c8eeeaeee8eeeae8c8eeeaeee8eeeae8c8eeeaeee8eeeae8c8eeeaeee8eeeae8c8eeeaeee8eeeae8c8eeeaeee8eeeae8c8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36793
namespace PEqualNP.Outside.L_meta_36793
open PEqualNP.Outside.L_meta_36793.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 6 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 25 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 90 := (concat bs2_4_0 (concat bs2_4_32 bs2_4_64))
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
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
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
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
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
theorem bs4_4_384 : Interval s4Atlas 4 384 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 396 := (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160))) (concat (concat bs4_4_192 (concat bs4_4_224 bs4_4_256)) (concat (concat bs4_4_288 bs4_4_320) (concat bs4_4_352 bs4_4_384))))
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
theorem bs4_5_576 : Interval s4Atlas 5 576 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 601 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 bs4_5_96)) (concat (concat bs4_5_128 bs4_5_160) (concat bs4_5_192 (concat bs4_5_224 bs4_5_256)))) (concat (concat (concat bs4_5_288 bs4_5_320) (concat bs4_5_352 (concat bs4_5_384 bs4_5_416))) (concat (concat bs4_5_448 bs4_5_480) (concat bs4_5_512 (concat bs4_5_544 bs4_5_576)))))
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
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
theorem bs5_4_512 : Interval s5Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 539 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96)) (concat (concat bs5_4_128 bs5_4_160) (concat bs5_4_192 bs5_4_224))) (concat (concat (concat bs5_4_256 bs5_4_288) (concat bs5_4_320 bs5_4_352)) (concat (concat bs5_4_384 bs5_4_416) (concat bs5_4_448 (concat bs5_4_480 bs5_4_512)))))
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
theorem bs5_5_640 : Interval s5Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 664 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 (concat bs5_5_512 bs5_5_544)) (concat bs5_5_576 (concat bs5_5_608 bs5_5_640)))))
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
theorem bgb_5_2240 : Interval gbAtlas 5 2240 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2259 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)))) (concat (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))))) (concat (concat (concat (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 bgb_5_1216)) (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)))) (concat (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 bgb_5_1504)) (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664))))) (concat (concat (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 bgb_5_1792)) (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952)))) (concat (concat (concat bgb_5_1984 bgb_5_2016) (concat bgb_5_2048 bgb_5_2080)) (concat (concat bgb_5_2112 bgb_5_2144) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240)))))))
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
theorem bgb_6_3392 : Interval gbAtlas 6 3392 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3407 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))) (concat (concat bgb_6_608 (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 bgb_6_800))))) (concat (concat (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 bgb_6_1664)))))) (concat (concat (concat (concat (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760)) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856))) (concat (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)) (concat (concat bgb_6_1984 bgb_6_2016) (concat bgb_6_2048 bgb_6_2080)))) (concat (concat (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176)) (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 bgb_6_2304))) (concat (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)) (concat (concat bgb_6_2432 bgb_6_2464) (concat bgb_6_2496 bgb_6_2528))))) (concat (concat (concat (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)) (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720))) (concat (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816)) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 bgb_6_2944)))) (concat (concat (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 bgb_6_3168))) (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 bgb_6_3392)))))))
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
theorem bgb_7_1632 : Interval gbAtlas 7 1632 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1656 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))) (concat (concat bgb_7_608 (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800))))) (concat (concat (concat (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)) (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)))) (concat (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408))) (concat (concat bgb_7_1440 (concat bgb_7_1472 bgb_7_1504)) (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 bgb_7_1632))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeee8eeeae8c8eeeaeee8eeeae8c8eeeaeee8eeeae8c8eeeaeee8eeeae8c8eeeaeee8eeeae8c8eeeaeee8eeeae8c8eeeaeee8eeeae8c8eeeaeee8eeeae8c8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008373992 * 2 ^ 32 + 4008372424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36793.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.or,[3,6]⟩,⟨.and,[0,1]⟩,⟨.and,[0,7]⟩,⟨.or,[1,9]⟩,⟨.and,[3,6]⟩,⟨.and,[0,4]⟩,⟨.or,[2,12]⟩,⟨.or,[8,13]⟩,⟨.or,[11,14]⟩,⟨.and,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373992 * 2 ^ 32 + 4008372424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373992 * 2 ^ 32 + 4008372424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36793

open PEqualNP.Outside.L_meta_36793 in
theorem PEqualNP.Outside.L_meta_36793 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373992 * 2 ^ 32 + 4008372424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373992 * 2 ^ 32 + 4008372424) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
