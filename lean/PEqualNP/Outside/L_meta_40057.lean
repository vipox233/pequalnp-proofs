import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40057.Model
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


end PEqualNP.Outside.L_meta_40057.Model

namespace PEqualNP.Outside.L_meta_40057
open PEqualNP.Outside.L_meta_40057.Model
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

def SBf (j : Nat) : Nat := [6, 6, 8, 7, 5, 6].getD j 0

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

end PEqualNP.Outside.L_meta_40057

namespace PEqualNP.Outside.L_meta_40057
open PEqualNP.Outside.L_meta_40057.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xe0004c00314811480025630000819be43bc43be42bc42ef32de32dc32ec32cc32be41bc41bf40bd40
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x41258a38030000000010218000021e68050061c0000000000002a7294658e420cb1884196390c32c6218658f540cb18a8194794e4197294838c32907186420e30cb408e29a812c525031864a04d14540
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xc40800a1987540ca0f650ca418319432503043214540
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 16
  | 2 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | 2 => packedAt s0K2 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*2) 2
  | 4 => packedAt s0K4 (220+((h/4+packedAt s0K4 (208+(h % 4)*3) 3) % 22)*5) 5
  | 3 => packedAt s0K3 (442+((h/5+packedAt s0K3 (432+(h % 5)*2) 2) % 33)*6) 6
  | 2 => packedAt s0K2 (153+((h/1+packedAt s0K2 (152+(h % 1)*1) 1) % 6)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffffffffffffff81fffffffffffff87ffff
  | 2 => 0x1fffffffe07fffffffe07ffffe03fffff8fe3f
  | 3 => 0xe01fe03fff80fe01ffff83e03ffc0fc07f33cc
  | 4 => 0xffe0003fffff0001fffffc003ffff0007fc3f0
  | 5 => 0xffffffc000000001ffffffffc00000007ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x2424228a241224a0500594aa4ac514550354d5
  | 2 => 0x949451443244948a96029549422aaaa38aa2a
  | 3 => 0x5d1189a6890e906b3aaa826627688f035d334c
  | 4 => 0x919d163912481d8dccd34c1839b3c20c6ec3b0
  | 5 => 0x1e1e183e1c70e1f1f71c739f01c30c3077fc00
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0fcc0c0c0ccc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x54818000000000002000a00001000e0018000000018000400000000002c00000480df43be43bc43dc439c43f741f441f731f431f721f421f710f510
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x401a40251220071628000c61e0063807203e8f29c87975110f28a221e510f41ca218839443cc7288618cd95321ab29e439443c87288610e510f109a2a22154534432886885914910
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x408c000a198b5110e176510f218519443443044314910
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 16
  | 2 => 4
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
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*2) 2
  | 4 => packedAt s1K4 (216+((h/4+packedAt s1K4 (208+(h % 4)*2) 2) % 52)*5) 5
  | 3 => packedAt s1K3 (452+((h/5+packedAt s1K3 (432+(h % 5)*4) 4) % 21)*6) 6
  | 2 => packedAt s1K2 (153+((h/1+packedAt s1K2 (152+(h % 1)*1) 1) % 9)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffffffffffff81fffffffffffff87ffff
  | 2 => 0x7f03fc07f80fe01ffe0fc07c0f81fc07b8ccc
  | 3 => 0xf8003fffffffffffffff0007fffffffffc0fff
  | 4 => 0xffffc0007fff0001fffffff800ffe0007ff0f0
  | 5 => 0xffffffff80000001ffffffffff0000007fff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x481082450892244828052ca949292a5501b555
  | 2 => 0xc2a59693390e48daf96055a2d85b1e833b8ccc
  | 3 => 0x968a250a5224919152aa0204b296552a5c0aaa
  | 4 => 0xe4c3362c64481d1d9cd39b3020e7860c6ed0f0
  | 5 => 0x70c38307870e1e1e71ce3c73c041830776f00
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaaa00aa00aa00faaaaa00aa00aa00faaaaa00aa00aa00faaaaa00aa00aa00faaaaa00aa00aa00faaaaa00aa00aa00faaaaa00aa00aa00faaaaa00aa00aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x4060000000001e0000000000000000000230000000009400000003800004780000030000000003a14014000000036ac021000c0291c111002698ba8009041a1800000002c00a004000000000003e000002c000003200000000000000001090044a800000012540000d000002700000000000e00000000000000030001512a0ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x881be501027ca0206e94040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc37e85986f50b30ef99661dd32cc2fca3985f54730df20661bc40cc2fea9185f95230beaa4617c548c2faa7185f94a30bea9461bf428c37a8518778ca30ee194617e518c2faa318778c630ee18c617e508c37c81186f10230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4987bd4930b7a92617c524c3d8a4985b14930dfa1261bd424c3be6498774c930bfa8a61f7514c2eea2985f14530fa28a6174514c37c80986f10130fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea9061bf420c37a8418778c830ee190617e510c2faa218778c430ee188617e500c37c80186f10030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20dfa1641bd42c82fca3905f54720df20641bc40c82fea9106fd52209faa4417e54882faa9105f15220de2a4413c54882fea7105f94e20bea9c417c53882faa5106fd0a20dea1441ef32883d865105f94620bea8c41ee21883d843105f94220df20441bc40883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20dfa1241bd42482fea2907dd4520bba8a417c51483e8a2905d14520df20241bc40483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf29041bf420837a84107bcc820f6190417e51083eca2105d94420bea8841f551082eaa2107b88420f6108417e500837c80106f10020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43ec43887d48710df20621bc40c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c528437e85086f50a10bea8c21f731843e863087dc8610fa10c217e508437c81086f10210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea68877d4d10afa9a217e53442faa6885f14d10ee29a215c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c524437e84886f50910fb10a21f5214437c80886f10110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c520437e84086f50810bf28821f731043e862087dc8410fa108217e500437c80086f10010fb88021fa10043ea20087e44010
  | 1 => 0xd529077e8520ef50a41bf28c83bf41907ee8320df94241bea84837f53507bea6a0d7d4d41be29a83dc53506b8a6a0efd0d41dea1a837f52506f8a4a0efd0941dea1283f7415077c82a0dfd4141be282837e54106fca620df54c41df21883bc43106fca420df54841dfa1083bd42106fca220efd0441fb20883bd41107ea8220df94041bea80837f54cc6fca998df55331be2a6637e52cc6faa598efd0b31dea1663f741cc7e88398df94331bea86637f548c6fca918df55231be2a4637d538c7be8718f710e31bf294637d528c77e8518ef50a31ef99463dd328c6fca318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898dfd4931be29263bf424c77a8498fdcc531ef18a637f504c6f8a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31efa1863dc430c6fca418df54831dfa1063bd420c7be6418f74c831bf28863f7410c7e88218f7cc431fb18863dd310c7ea6218f54c431bf280637d500c6fea990df95321df2a6433e54c86faa990ef553219eaa6437c54c86fea790df94f21ef29e435e53c86faa790f754f21aea9e437c53c877e8590ef50b21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510efd0a21dea14437e51887ee6310fd0c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21dfa1243bd42487ee6290fd0c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53086faa610df14c21bf29043bf420877a8410df94421f790843f621087da4210fd48421bf280437d50086fca7a05f54f40bf296817d52d037e85a06f50b40bf28e817d51d02faa9205f94e40bea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd429037885205f94640bea8c81bf419037c83206f50640de20c817e509037e81207ed0240dfa9c81be539037aa7206f14e40dfa9481be529037aa5204f54a40de29481bf329037c65206f4ca40de19481bf519037ca3206f54640de28c81bf319037c63206f4c640de18c81bf219037c43206f48640de10c813e50902fea6a05f14d40bfa92817c525037e84a06f50940bfa8a817c51503f680a06f90140bf2a0817e53102faa6206fd0c40df21881bd431037886205f94840bea9081bf421037c84206f50840de210817e51102faa2206fd0440df20881bd411037882205f94040dfa0081fa401037a80207e50040dfa9881be531037aa6206f14c40dfa9081be521037aa4204f54840de29081bf321037c64206f4c840de19081bf511037ca2206f54440de28881bf311037c62206f4c440de18881bf211037c42206f48440de10
  | 2 => 0x272bb80001d4cc0181211b3283a80000047247c9b2b60004fc0026a000131219e854e4a1741a2612050d00002e2964000e941a9a400000572a0cc0a1f00e12c8e022320454aa16a00019400000000000000001bc028d806860691c0018d0009b000000000a38080002b05640000038a718000000003a000000000c70000002620000023c000204458000a20010129308e360000001a6000002060000000000000081c530005549782a0000008540000059c00000258000000000000c6000802460000000000018880380000000320020388020003d080a40082900001084a0100000000000800034000000008426480001800008801088011010200006099030080008001008201804040060000211882200821184000800008c2301461204a30000108800090011004018141000200004018440180420010209000000030000c00444080400004108000000430140001082014600004201ca01000129c4210440000000800100403100021df94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543fba8a87775150ef8a2a1fd14543ba28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7c87a16f50f42de21e857e51d0afaa3a15f94342bea8685bf53d0b7ca7a16f54f42de29e85bf51d0b7ca3a16f54742de28e85bf50d0b7ca1a14f94342dea8685bc50d0afaa9214f55242bf29c857d5390afca5216fd0a42f7a14857e5190afaa3215f94242bea84857f5350af8a6a16fd0d42df21a85bd4350b7886a17bd0942df212857f5150af8a2a15fd4142be28285bf5350b7ca6a16f54d42de29a85bf5250b5ea4a16fd4542df28a85bd5150b78a2a16fd4142df28285bd5050b78a0a14f14142bf2a0853e5410afca6215f54c42bf29085bf4210bdc84216f50842f6a10857e5110afaa2215f94042bea80857f54ccafca9995f55332be2a665bf42ccb7a85995f94732bea8e657e50ccafaa1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32bf29465bf428cb7a851977cca32f7994657e518cbeca3195d94632bea8c65f5518caeaa3195f94232bea84657f544cafca8995f55132be2a265bf424cb7a84997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cafca4196fd0832dea1065df320cbdc6419774c832f6990657e510cafaa2195f94032bea80657e53d06faa7a0efd0f41dea1e837e52d06faa5a0efd0b41dea16837e50d06faa1a0df55241bf29c837d539077c8720ef10e41bf294837
  | 3 => 0x70000a8d2a9d0001742c1b95c0bf8001da000000002d800000000000000000d60000004e0e8b0d4c2a6801053000900000003306e0002d10008b40020a59623c000005d8000e78bd0009c1280005c8000228c418a000000e14f6331400000005a0000005ac0000030f000000000985305e45e23a000001372b8176000a4800000000000282bc00087af91ee0000d800000968000000006e8ec03d000000000695ea28149000000240001630000013200000000000000000000002ea000a6cc00005f809400000000000ef9d92560000aa6b000494000ed19c3cd888001ea6551530a4c45700000009c230f61f25be00000000150000061cc63a00041ab10d8374a3a385040000014d4d0000002634a4000bd800000000001172ec72000000000038002480e20000029f44c000d90000000000000002e000000000003c0758002549105f1860000000019d4682a8000003140000000000075099a6f16c8c800000000a2000000290420ee21900087000000000000000003620000001606600177975000934000b9408a2400000000000002174b829033800452544a0a0f3acbfc001854064040000907e0001c3130000601b1aa000980000000000006b92c0000ac0002f0aa10810000448ab490000000b4800000460000722d900003c000000000000000011a000000dc00067800000000b1d1d800600664002202d6c545198358c224e20750008455d000000000000000007b800307000914ff800000000b92b4000064002db3c000029000000000000005e6c14002c53cc3455a80011c7400988a0000016d00006a8d40018e000788968e2342000918005cab31820005027540006f000724000000003f0001d227a00c001de000458c9a2e4b67f0562715229cc000000004383f16d000611649265608dd5900054a0f0000d90000000010b3e60018580015a000c599200012400000000aa5118000000000000000000000092000304f386e180000b38004aa16c7621d000000001a30006d85c000000000000da000000ad8000b20000007001a0000000000000176800000c30a100059e17c8f0000000000029e000318000000000000009c000000000002ae00000000430c80000000001fd5209b000878921be5e4000650ae4fa0003980500071c0028600000000000000af55e00000054043000000000c88405f40000004d00000000000628000ee9fd0cc000002ca0d439d4522b000000000004a60005d0003ae11800030000824000000000012e80055621c0028f46633c001a600000000208296c5c058000000005a8944965b8e68a73c6440ed81a1fa37c0000050a00000162380000000210004853baf45460000000058600000000312c20168004f2120bc0000006f000295000000000fb0000000024e000000001ea44200097b18000000002f70
  | 4 => 0x5200000000000000000000000000000000000000000000067cf8800000000000002f4b7000000550630002a24e8001461641a49040000000000063800000708000000000015f0000004140015f000000000000000000000000000000000104408df8000000011b0000089253f1610000013900039463c002563e81d0000881867bc8e8003d6000000000f00000021a5a8c7c000000000016000035e9fd0d800000000000c939c5b08cae200000127834000000c12842a40007c8790008f95300028ac08000c8400000da800000000002af1640004201f0000009906259a1ad561fe072001260000000012100000024c302780000014a000000b845f800416afc598db000000a787d0007e8000002780e800000000000000003680008880004c000003190000000400015227cc40003500000000004600000000038888bb8002349d88515a2523c8000005e000016000000450a0000000001289ae42c0000000000000000212000838000000004d4fa80000000000000000000000002ac00183001402c6c001b71fe92800000000000be0a23ca54c000ef0000000007700004400000000190000000002bcb82650009b4000003482692f8005c6000001270000000012e0000000000013c214000cd0e4b988207c37a00173800000000000560000001f000000be0588000000005280012ca5d1400000000000000000000000fa6200000004a00000150800000000000003c2000700000000000000000000000000428bf54c93e000894000002cc594000000000007c00000069cae8000008b0000005167e0002d7334000000440000006b00009e6ac4c800000000000000005100000060200113a31366000000000000006a955000000b00000002c0000c247a0014e05e20e3d8508915ec0a4000000000008980000000169876000460d6800000000b9930000000a500000000000000218c782187a634394f680005c8fd610271e272c000003e00000000000000000000000c3800000000b550619600000000000000000fb9970008140000042650c000b4588aed4680028c170368414ce184c38fe100254001c152c9d56e8313f600000000024000001121dc488002f1000000001744a8000002d029c000bf00000000000000590000000d027653159800000000bf8ab00000000000000000e99031966700016f3f2a1c000000b40000000037642400000000ba40013a0005a4cda7c00000000000000ab80021000000000000000000000000000000000000000000000000000002fb62c0013d1e400070c00312000000002570000009a0000007a4001a93ec000000f40644346a0001c6078000005d60001d80020c0000017d45eb78000500002dc0009d1cc15c0000000000000000000b041b800000adc00097000a803d93
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xc540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530834c6254c208f990530823d6414c209798c53082766114c209d584530823e64948208f592520823d65d0820c794f420831d53d08208fd95420831e5350820c754d420834d53cc8209b59432083365494420cd55251083565394420d554e51083374294420cd50a51083365454420cd55151083565354420d554d51083374254420cd509510836551884208fd96400823d6590020c794e400831d5390020ab58a40083365190020cd546400823f65100208f594400831e5310020c754c40082ad6210020cd944400833551100209bd9520082cc6348020b918520083a840480209ed9520083ab42480208f58a54c423f62553108f99353c423d64d4f109b98b53c426d62d4f108f99053c423d6414f108f99352c423d64d4b109798f52c425d63d4b108f99252c423d6494b109798e52c425d6394b108f99052c423d6414b108fd9742c423d65d0b108fd9542c423d6550b10ae18142c425e63d52109758f548423e64d4e108f593538423e6494e108f592538423e6494a108f592528423e6414a108f590528425e6314a109758c5284357530c610b598f218423d62d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f588544423e60151108f180544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d4910cbd93524432c64d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549108f990524423d64149109b994524432f5414910cb150524434f5314910d314c524432e6414910cb590524436561149108f997424423c65d0910c7d4f424431c53d0910cbd4b424432c52d09108f995424423c6550910c7d4d424431c5350910cbd49424432c52509109d99621443545388510d914a21442746548510d514d214436452485108f996404431f5390110c714e404432f5290110cb14a404423e6510110c7d4c404431c5310110cbd48404432c5210110d514e104436452841109798c540425d63150109b988540426d62150108fd91530423c6454c108f990530423d6414c109b988530426d6214c108f992520423d64948108f990520423d64148109798c520425d63148109d984520432e5250810cb54942042b860508108f992510423d64944109d5943104355530c4109d59721042d663c84109d594210427965840109dd9510042d46344010b9189100427b6544010
  | 1 => 0x23e650c8408f59432102ba60d4440a7d8d511029c6354440a798c511029d6314440ab98851102ad6214440cd54451102ba60144408fd95311023c654c4408f994311023d650c440e54c4311023e65c84408f597211029e63c8440a758f211032d52c8440cb54921102bb6048440ae181211023e65084408f594211033a60940408f58a54cc23f62553308f99252cc23d6494b309d98652cc2756194b308fd9742cc23d65d0b308fd9542cc23d6550b30ae18142cc27661d52309d587548c23e6494a308f592528c2d6618ca308f992518c23d64946308f58b544c23e64951309b98a544c26d62951309d986544c27561951309bd89544c26c62551309dd85544c27461551308f994544c23d6215130cbd53524c32c54d4930cbd93524c32c64d49308f990524c23d6414930cbd50524c32c5414930cb990524c32d64149308f997424c23c65d0930cbd4b424c32c52d09308f995424c23c6550930cbd49424c32c525093097997324c34c52cc930d3149324c33754d4530cd153514c36752d4530d914b514c33742d4530cd50b514c3375414530cd150514c3675214530d9148514c3374214530cd508514c3573214530d54c8514c23e6590130cbd4a404c32c5290130cdd46404c33451901308f994404c32f5210130cb148404c3375110130cd144404c34c528c130d5146304c26e62150309b588540c27661150309d584540c23e6494c308f592530c23e64948308f592520c32e5250830cb549420c2b8605083097596320c2d6618c8308fd91510c23c6454430d5544310c25f654c030b3189300c2d4614c0309ed95300c23e64d4f208f59353c827661d4f209d58753c823e6414f208f59053c832d62d5220ce983548832d6215220ce980548823e6494e208f592538823f6454e208f19153882776154e209d18553882ba60d0a20ae181428823e64946208f592518823f64546208f191518825f63546209718d51882ad6290220ab588408823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209bd8953482776154d209d185534825e6514d20c7d50534831c5414d208f997424831f53d0920c714f42482ba60d09208f195424831f5350920c714d42482b86050920cdd53514833454d4520d5d4f514835453d4520cdd0b514833542d4520cdd5051483345414520d5d4c51483545314520cdd08514833542145208f996404831f5390120c714e40483375190120cd146404823e6510120c7d4c404831c5310120cdd4440483345110120d314e204836451881209798f540825d63d50209d987540827561d50208f596540823f62550208f589540823e64150209798
  | 2 => 0x524ca318fd91508c63c64542318f58b544c63e60d51318f992544c65f63551319dd85544c63e65151318f588544c63e60151318f990524c63d64149318f997424c63c65d09318f995424c63c6550931cd153314c71c548c5318f993504c63d64d41318f596540c63d62950318f982540c71c63550318fd89540c73461550318f181540c63e6415031c7553430c65d6510c31b5584430c63e64948318f592520c63f65d08318f597420c63f65508318f595420c6d561cc831cd553410c79743d04319d594410c6d56310431e510c410c6d5638c43197d95310c69c644c4319dd95310c6b4644c431b5d95310c757654c431e5d91310c6d6644c431b5191310c794644c431a5191310c796544c431e5551310c6d7624c431e5d09310c795424c431b5181310c63f64540318f191500c66f62540319b189500c65e63d53219758f54c863e60953218f18154c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c863e6414f218f59053c871e53d0b21c754f42c871e5350b21c754d42c863f64543218f19150c865e63152219758c548863f6454e218f191538863e6414e218f5905388755530c621b598f218863f64542218f191508865f63551219718d544867b60551219e181544863f6454d218f191534867b6054d219e181534863e6414d218f590534867665cc521b998b3148755530c521b598f214863e64d41218f593504863d65950218f982540863c60550218f990540863e64d4c218f593530867661d4c218f990530863d6414c219e98053086796014c218f992520863d64948219798e520865d63948218f597420863f65508219bd9521086776548421e9509210863f64540218f191500865f63540219718d500872d52d0b40c794d43902b76150e40ad185439032d5250a40a7d8d419029c6350640cd94541902b661d4e40ad58753902ba60d4e40c7d4e53902ba6014e40ae983529029e6314a40a758c52902b66114a40ad58452902ba6014a408f996329023d658ca40ad98632902b5618ca408f994329023d650ca40a798f519029d63d4640ae98351903375194640ae980519023f654c6408f195319023e650c6408f5943190395310c6408f997219023d65c8640a798f219029d63c86408f994219023d65086408f997425032f52509409dd8553102746154c40add8543102b46150c40c754c431032d52d08408f596421025f63544409718d511029f6350440a718d411033551104408fd95401027b6550040ae98353102b76154c40ad185531031d5314c40ab98853102ad6214c40ad98453102b56114c40ae98053102ba60d4840a798c521029d6314840ad98452102b56114840ae980521023e658c8408f596321032d528c840ad98632102b5618c840cb54932102bb604c840ae181321
  | 3 => 0x6990580043e0002e00034e880de95a23a9fc000001e8bfd342881364d060800000360000001104d8001415b09f55a2653dc6802326c4f222c2600010c00000000112b000000036ebacc4812000000468c633e00000000000000000005c84acb319c000000001f209eb88a580055a0000000000079cdf1700e2a392da75604ba451927104758698003e60000c0810004100024a164af44fa6223e0004c8000000011a000000000001494d483800286000770001ba2c80005e8002fc29400220440cc0402001820000004400010040410020010a500200000920800a0460041420800451ce20500010108000800200000000100204014000010104614d0000c20410421000411090802830850402402194400800c11c00041ca00b0401000400020c000300808e2c208204500120508b0020030031840860013100c10010010c300109010100308304908200d08304100b0401000070000001000810030000040431c10800860813410c610300100120a0040c60880020450441c308418004004103574314543cd90c5150e3f6550c43ad1854310e5f6550c43b51854310e776154f429d18553d0ab76150f42ad18543d0b1d5310f4297d8d51d0a5c6354742ab58b53d0ab76154f42ad18553d0b1d5314f42ab58853d0ab66114f42ad58453d0a9f6354742a718d51d0a9e6314742a758c51d0b355114742a798f50d0a9d63d4342ad98750d0ab561d4342c714d4350ab76150d42ad1854350aad6294d42abd895350ab76154d42ad1855350abb6054d42ae1815350b1d5314d42a7d8d5150a9c6354542aed815150ab86054542cd5445150a9f6354142a718d5050ab76154142ad1855050a3f65508429bd954210b2e54508429d98454cca7561153328fd9151cca3c64547328fd9150cca3c64543329d987548ca7561d52328f982548ca3c60552329d984548ca756115232cd952518cb355494632cdd0a518cb354294632d5cca518cb365454632cd551518cb374254632cd509518ca3f64542328f191508ca7761551329d185544ca7b60551329e181544cad6618c9328f990514ca3d64145328f993504ca3d64d41328f596540ca3e60950328f181540ca3e64150328f992520ca3d64948328f597420ca3f655083297d95320cb8d424c8329bd95320ca3f64540328f191500ca7761540329d185500cab46150f41cb54b42d072d5250a418f997435071c53d0d41c714d43506b46150d41c7d4f425071c53d0941c7d4d425071c5350941cbd4942506b46150941d514f415071c53905418f596431072d52d0841ad587421063f6550441a718d41106776550441b518d411066e62153319b58854cc63e6494b318f59252cc72e5250b31cb54942cc63f64543318f19150cc66e62152319b588548c63e6494a318f592528c72e5250a31cb549428c74e
  | 4 => 0x1680000000000083c000002347a02200048600147800000001332a800eb300009d306810001b9000000ebae558c0016ca210007486b8b927a000002c400000041800000754002fc4140016880049a000002014a46e0438de4540809f08c000000000004bcb210901a0f86b466800000450db1870d4ae0000431e2000028001ca000000000000b036ab142a0000000000015c001300000000006f0000540022c42642ca12e7000000868fa0f0000000e60000000000026e6888629d274484e79c460c0000028c0000008b800000000000000002dc000000001c0af0dc38e3a82d87b384000001ce0febe0000004dabdc39800000000000000000007f1032241596900032e00177800000000000003c47200d8000903dc360310000017e800000000001fa2440000000004ab81548a05a84bd380002786183c87a2c4bd9318000008a5840003667ac000005560000000000032c53000382091851b100000056ae64e2740000500000016980005641d4f8635320d4579541860009311500000165000000a98000005b60013a2502f8a11060000000a800000068b74538e410886c001cd5da980f48003268c41d8000007c165829000491370b03f672c7586000003c7c000000bd445100386924178000009dc0f83a376000ef9f4000604f60f95d40000a000606000000001d289065246092a1c3211118e128f89bc4f800101000516000002cd2c0000000002ae85800000000000002be122270000fd0003f0bd0e22c6944c703c4703752119e4e42e84986906c36c2919842e0000000000000000000000a14000004ac7512a0f031871406afa0380000f0005d80000000003aac8778ce1d87bc001e1000000002450220017da25000000628e7000000fa8000000006900000088c00000000528002c1000268c5af02ec8ac00000000001208ed5020000025a450650000000009d8000000001f871a0952a28804244360000000000000000025312448c000000000005d8000000011e1882b6b7ca18cf304a60f6a935e695c7b11e0007197f00b2b03d54530b5360080014f0ba0012393b0003c86891601235884a002640011e8fb0004e0a415c000000000000000000007d1d00000012a0cc12c001a3512000002af0000005484e0003cc0000000000000000000000001470000002685910a384000cc12846c000000000000000041000132000500000001aa000284cb000464000d624f0000000000000004cd498d000000002da0003b8000001fe5b0000002401940023f0425105f88004c938c50a4262bc4f001925c4b51d0b521e4142c26100057c0012c1500000000015c000002bb07e0b4022ac2e6b38e6000000b8d138455604a01e8e04fc59c620003bcc316f00000080c5f2b316c5bc0024041a2549a876322000da0000000005e000156000d4000
  | 5 => 0x4a4ec975280a691722d000000000000005dcb924b2a0418640b30008711f2364be9ad491f6592b0c552bc2aa0001121e0001dc000002d00006000036a7a8000003361010305f0000c0a71ca334001398000008dd6816a1a0898a2a940002b0ee80059e000002f22ac9bcf180000047000000064261198004b000000000000000df800000ab8000005425840019021035413817298ae4ff0004f60e152a8d58e2592e1d80ce178c78002da7e56b9ab006000000000001853482340e11ca98000000011a800162a8c6a000000000000002305955fa1a020c04000000dc0012ab0033a5b8000c230a3648721820472400152490a44a8a9e498000199d1000bd00000052e845028512d21a14180e4f0c14000000000000b2dc050564cc8000846840017b3a60006d00043a6909fa3007cadc000000000014e0391920012caee00000003000540c1d521ff00000020800000000000000008ec001fc226798d7890000238001f8000c253d0000000015aab65d05fd5114d57400047800000c10ca8005ac0010a222000a40000002f0b84b5800018000c90740004cd552f90005c42d0003ca6b817000000465410720008402a80013c8bc0000006e000d28df364768311fd4ce5d0a311000014c000002fa0054b000300a9c2a0004ba0000007500000000000000000bc800000000fb8004721ac00184000000001e40000000000021425d629db3804056aa195842e005125272000ae8
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x2c6d80f28c400850691802e1da092610933422870300000100a000240055a806ed80803e011005c2d79e647000056b0e91320128d0ca8c024ca40204eb400c001071010932400430211c1282002a28e2a9887a15147154c53d0b0aa9ac229e85451cd5114742c2ac6a88a3a1614531854350a8a38aa629a85461c15314d42a28e6a88a2a1530705445150b0a298c2a1283251cd61d0841c28c630aa818c3870595420c64a3a2c399063259d2644c43192ae43226218c9670191310c64a3b4a898863251d9544c431928eda126218d1575d09310c64a3b28498863451d1530c621a28e8a986290d507054c314870b298c2a1c818518e5150640a2ce3a9ca72051673d46519028bbaa6218c81451c55310c40a28e6a8882205147154c5310306a9ac4298818554d6114c40c4aa4b0c642051473544511030ab1aa22888189589511444085ae432a6220514754c4311030ab2a62188818358d52c8440c52a4302841851474544310c314b14c1aa4418614c6050920a60e0a10a29060d535884008312b12a220041a218c4048020d40c2202401051674d4c3184314a90c0a1021451d1530c410
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x20810029838885821da544c431814865d7424c431a048154d6214c40c04735895114440905821d5310c44081487595310c440
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (i*5) 5
  | 6 => packedAt s2K6 (i*16) 16
  | 5 => packedAt s2K5 (i*27) 27
  | 4 => packedAt s2K4 (i*38) 38
  | 3 => packedAt s2K3 (i*49) 49
  | 2 => packedAt s2K2 (i*60) 60
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (6+((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 2)*2) 2
  | 6 => packedAt s2K6 (760+((h/14+packedAt s2K6 (704+(h % 14)*4) 4) % 140)*7) 7
  | 5 => packedAt s2K5 (22962+((h/267+packedAt s2K5 (21627+(h % 267)*5) 5) % 1628)*11) 11
  | 4 => packedAt s2K4 (31238+((h/260+packedAt s2K4 (29678+(h % 260)*6) 6) % 1270)*11) 11
  | 3 => packedAt s2K3 (2852+((h/18+packedAt s2K3 (2744+(h % 18)*6) 6) % 73)*7) 7
  | 2 => packedAt s2K2 (366+((h/2+packedAt s2K2 (360+(h % 2)*3) 3) % 10)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffff81ffffffe07ffffffff81ffffc7ff1ff
  | 1 => 0xf80ffffe03ffe0ff83f07c1fffe1fe03a27e7c
  | 3 => 0xfff03ffffc0ffffffc007fe0fffe1fffc38f8f
  | 4 => 0x3ffffff000ffffff8000ffffe003fc0ff0
  | 5 => 0xffffc000000000ffffffffff00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8a1008c4882400014b09421280222a80cb0b5
  | 1 => 0x926299143924896581542d1a5b215419a2565c
  | 3 => 0x2144aa20906918aaa8084b4895541952c30b0a
  | 4 => 0x858b34492241d2d34e6d0210e6998063740de0
  | 5 => 0xc60c3871c38e1cfc738e739c07111183fbe000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88ee88aa00eeaaaa88ee88aa00eeaaaa88ee88aa00eeaaaa88ee88aa00eeaaaa88ee88aa00eeaaaa88ee88aa00eeaaaa88ee88aa00eeaaaa88ee88aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x83400380280000000088982e54000000052652000004201583324c60f0c00b280801280007c02c542470d3a910000014023000001c00005a2007890036413815a0048ec8063209ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1a1a46c0001c800014c00011968a4f4a0008cb4880110ed30399dbc7974043cd04860c464c11c007d649ce80071b1880d50104c000019990d5c1408cd79600001d0012000f958356c8000580114a9b8300001a981013c0001481c00d5ccc97054512c00442594e4b02d7c5d29acbdc4290898fc01900001840085054000000000ac0154d800742095b490dcf0e1c000693538018c4144b9242160081167044064ac08418128808018028a80c19628409e39830410005ed4143bc282879d4310ebca7215754e42bd28485795090a7ca9194f55232bd2846579508cadca5a0db54b41afa9a835c53506dea4a0db14941bda82837850506bca620d754c41b7296636d52cc67ea898cf15131b7a92636c524c6f6a098de141319f2a0633d540c6dca310cf950219eaa0435e53086baa610de94021bca8043ae540875aa810f394c21e6a98436e51087cca210fa94021f4a80435e53d02baa7a06b88640d610c813e50902bea6a05714d40b7290816d521035ca4206b54840d710881ac211027ca0206e940409f2a6613d54cc37081987388630e610c615e508c33c811867102309faa2613c544c2dca4185b54830dc20061ce520c39aa4187388430e6108615e500c3b4a01876d0030cf200619c400c3b0801866100309f2a6413d54c82bca7905754f20dc20441d8308827ea8904f15120afa9a415c53482eea2905d14520dc20241d8304827ca9884f55310af29e215d53c43708188760c310b7294216d52843c843084fd51109e2a2215f53442b8a6885bd4910b629221e421043708008760c010
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x40848000000078002800008000070c000580000000a8600010000000002c68e00002600060000002200000002000002e00052400000028084a61814310e586054c418e181540c7295454021d254d500862d6508440ca548400c24d6508430a6982400c2c96210030e2988400c3896210030e2948400c3895210030e2884400c3882110030c614c40483305110120c61503048350510c120c694c40c431a540c310e808440043c0210c010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x400800c0a12eb310801848976948400c244bb04220061425d42110030
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | 2 => packedAt s3K2 (i*49) 49
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*2) 2
  | 5 => packedAt s3K5 (781+((h/15+packedAt s3K5 (736+(h % 15)*3) 3) % 75)*7) 7
  | 4 => packedAt s3K4 (3393+((h/39+packedAt s3K4 (3159+(h % 39)*6) 6) % 153)*8) 8
  | 3 => packedAt s3K3 (920+((h/8+packedAt s3K3 (912+(h % 8)*1) 1) % 77)*6) 6
  | 2 => packedAt s3K2 (197+((h/1+packedAt s3K2 (196+(h % 1)*1) 1) % 9)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xff01fff01fff01e0ffffff03ff03ff007f9e7c
  | 1 => 0x7fffffffffffffff03f01fffffffffff88ffff
  | 2 => 0x7ffe07ffe07ffffffc001ffc1ffc1ffff0e38f
  | 4 => 0x800007ffff8001ffffffe0001fffe001ff03f0
  | 5 => 0xfffff800000001ffffffffffe0000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x94c3111c5122a602cb2a7212721390c338e3c
  | 1 => 0x221442224824408501540946494642548834d5
  | 2 => 0x4c2895448348a96a540a92a912a91ca970c30a
  | 4 => 0x68b16689120ecdb39a6cc0c21cf38831dd03e0
  | 5 => 0x70c1870e1c70f1dce38f1cf380c210c1eef800
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeac8c8c8c8c0c0eaeac8c8c8c8c0c0eaeac8c8c8c8c0c0eaeac8c8c8c8c0c0eaeac8c8c8c8c0c0eaeac8c8c8c8c0c0eaeac8c8c8c8c0c0eaeac8c8c8c8c0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
def s4K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s4K4 (6+((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 2)*2) 2
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1ffe07fffff81c1fffff03fe0fffff007e73fc
  | 1 => 0xfffff81f81ffffe0f81ffffff0780fff93fccf
  | 2 => 0xe0ffffe001ffffff001ffc1fff800fffe38f0f
  | 3 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xc22231451041240529272126048a690c26315c
  | 1 => 0x444450c8229208a05a09464a9050a25490d4c5
  | 2 => 0x8aa8a2035525154b0512a9152d014ca9630b0a
  | 3 => 0x14d1049260365a729640c219ca658031d80ea0
  | 5 => 0x18e1c71c79c79f9ce79cf3818c4608c1ffe000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xeac8eac8eac0eac0eac8eac8eac0eac0eac8eac8eac0eac0eac8eac8eac0eac0eac8eac8eac0eac0eac8eac8eac0eac0eac8eac8eac0eac0eac8eac8eac0eac0, s4N, s4R, (fun _ _ => 0), s4I⟩
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x24a680008bf42bd42be41bc41ee21ec21
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x40268a2a16910421
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | 3 => packedAt s5K3 (i*27) 27
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*2) 2
  | 4 => packedAt s5K4 (100+((h/2+packedAt s5K4 (96+(h % 2)*2) 2) % 8)*4) 4
  | 3 => packedAt s5K3 (55+((h/1+packedAt s5K3 (54+(h % 1)*1) 1) % 3)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1ffc0fffffe0c1ff87fe0ff0ffffe018e73fc
  | 1 => 0xffffff03f07fffe0ff83fffff0701ffe73fccf
  | 2 => 0xfe0ffffc007fffff0003ff0fff801fff838f0f
  | 3 => 0xfffffff800ffffffc000fffffe003fc0ff0
  | 4 => 0xfff0000000000ffffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4c244628a41094052824e8930494d21886315c
  | 1 => 0x14408a1900a400a058812125102144a830d4c5
  | 2 => 0x28ad14406d498d4b04625a8aad029953830b0a
  | 3 => 0xb14a2092480d2a729548100cca4b0063580ea0
  | 4 => 0xc18c38e38e71cf9ce6739cc08c0c1183efe000
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xeec8eac0eec8eac0eec8eac0eec8eac0eec8eac0eec8eac0eec8eac0eec8eac0eec8eac0eec8eac0eec8eac0eec8eac0eec8eac0eec8eac0eec8eac0eec8eac0, s5N, s5R, (fun _ _ => 0), s5I⟩
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1ba200b0baa2649980000002746b990000a0002707c0ad00c500b340020f3a0000d002403a1cbc3297664018106c534068489e389582672d42942031b2b00543800090b0000b34000082051541100206c82b007fd5001fe54007f55001fc54007fd4c05fe53007f54c05fc53007fd0c05fe43007f50c05fc4300ffd4803fe5200ff54803fc5200ffd0803fe4200ff50803fc4200ffcc803fe3200ff4c803fc32007fd4401fe51007f54401fc51007fd0401fe41007f50401fc41017fcc401fe31007f4c405fc3100ffc8403fe2100ff48403fc21007fd4001fe50007f54001fc50007fd0001fe40007f50001fc40017fcc001fe30007f4c005fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x8c2000ff4c61001ff8630802bff2184007ff10c200aff4861001ff84308012fe6084009ffa842004ff94210027faa108013fc5084009ffa042004ff90210027fa8108013fc4084009ff9842004ff8c210027fa6108013fc3084009ff9042004ff88210027f44108013fd2084015fc9042004ff08210027fe2108013f71084007fd8842000ffd9510005feca88003fe654400f7f32a2000ff59510005faca88003fc654400f7e32a2000ffd9110005fec888003fe64440017f3222000ff59110005fac888003fc64440017e3222000ffd5110007fca888003fd5444001fe2a22000ffd8d10005fec688027fe63440057f31a2000ff58d10005fac688027fc63440057e31a2000ffd4d1004ffca688003fd5344013fe29a2000ffd0d1004ffc8688003fd4344013fe21a2008ffd8910045fec488023fe62440037f3122008ff58910045fac488023fc62440037e3122008ffd4910047fca488023fd5244011fe2922008ffd0910047fc8488023fd4244011fe2122008ffcc910047fc6488023fd3244011fe1922000ffd451001ffca288003fd5144007fe28a2000ffd051001ffc8288003fd4144007fe20a2009ffcc51001ffc6288003f63144001fe98a2000fd4c51001ff86288023ff2144007ff10a2008ff4851001ff84288003ff5044009ff2822000ff54110027f8a088003ff4044009ff2022000ff50110027f88088027ff3044009ff1822000ff4c110027f86088023ff2044009ff1022008fe88110047fa4088023f92044009fe1022003ffc411001ff62088013fe1044009fb0822004ffd9410025feca08013fe650400f7f3282004ff59410005faca08013fc65040097e3282004ffd9010025fec808013fe64040017f3202004ff59010005fac808013fc64040097e3202000ffd5010007fca808003fd5404001fe2a02004ffd8c10025fec608013fe63040057f3182004ff58c10005fac608013fc63040097e3182000ffd4c10037fca608003fd530400dfe2982000ffd0c10037fc8608003fd430400dfe2182004ffd8810025fec408013fe62040037f3102004ff5881002dfac408013fc62040097e3102005ffd481002ffca408017fd520400bfe2902005ffd081002ffc8408017fd420400bfe2102005ffcc81002ffc6408017fd320400bfe1902003bf9841001ffea20800ffe5104007fea882003ff1441001ffe820800ffe4104007fea082003ff1041001ffe620800ffe3104007fe9882003ff0c41001ffe420800ffe2104007fe9082003ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff4004009ff2002004ff50010027f88008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802003fe44010
  | 1 => 0xafd624c01dfe3126001bf18930077fea49803bfe524c01dfea92600eff14930077fe849803bfe424c01dfea12600eff10930017fe649800bfe324c005fe9926002ff0c930007fec298002ff614c001ff30a6000ff58530007f8c29800efc614c001ffa8a6000ff94530007faa298003fc514c001ffa0a6000ff90530007fa8298003fc414c005ff98a6002ff8c530017fa629800bfc314c01dff90a600eff88530077fa429803bfc214c0057fb026000ffd4130027fca098003fd504c009fe2826000ffd0130027fc8098003fd404c009fe2026002ffcc130017f66098013fe304c009ef1826004ff0c130027b8609800bf8304c01dff9026004ff88130077fa4098013fc204c007ffb2e2003bfd971001ffccb8801efe65c4007bf32e20009f9971001ffacb88002fd65c4007beb2e20009f5971001ff8cb8800efc65c4007ffb262003bfd931001ffcc988002fe64c4007feb262000bf5931001ff8c98800efc64c4001ffaa62000ff95310007faa988003fc54c4007ffb1e2003bfd8f1001ffcc78800afe63c4007feb1e2000bf58f1001ff8c78800efc63c4001ffa9e200dff94f10007faa788037fc53c4001ffa1e200dff90f10007fa8788037fc43c4007ffb162003bfd8b1001ffcc588006fe62c4007feb16200cbf58b1001ff8c58800efc62c4019ffa96200cff94b10067faa588033fc52c4019ffa16200cff90b10067fa8588033fc42c4019ff996200cff8cb10067fa6588033fc32c4007ffa8e2003ff9471001ffaa38800ffc51c4007ffa0e2003ff9071001ffa838800ffc41c4007ff98e2003ff8c71001fec638800ffd31c4001fa98e2003ff0c71001ffe438800ffe21c4007fe90e2003ff08710007fea188013fe50c4001fea862004ff14310007fe8188013fe40c4001fea062004ff1031006ffe6188013fe30c4001fe9862004ff0c310067fe4188013fe20c4019fe9062004ff08310027fecb08012ff6584009ff32c2007bf99610027facb08002fd6584009fe32c2004bf19610027fec908012ff6484009ff3242000bf99210027fac908002fd6484009fe3242004bf19210007fea908003fe5484001feaa42000ff15210027fec708012ff6384009ff31c2002bf98e10027fac708002fd6384009fe31c2004bf18e10007fea70802ffe5384001fea9c200bff14e10007fe870802ffe4384001fea1c200bff10e10027fec508012ff6284009ff3142001bf98a10027dcc508006ee6284009feb14200abf58a10027dac508002ed6284009fe3142004bf18a10057fea50802bfe5284015fea94200aff14a10057fe850802bfe4284015fea14200aff10a10057fe650802bfe3284015fe994200aff0ca10045fac308003ff5184007ff28c2000ff5461001ff8a308003ff4184007ff20c2000ff5061001ff8830802fff3184007ff1
  | 2 => 0x40027f8ca20012fc65100277f3208000ffd5040097fca820003fd5410025fe2a08004ffd8c40027fcc62000afe6310009feb188000bf58c40027f8c620012fc6310001ffa988011ff94c40007faa620047fc5310025ffa188011ff90c4008f7c8620003fd4310025fe2188011ef10c40027fec420012ff6210009ff3108001bf98840027dcc420006ee6210009feb108010bf58840027dac420002ed6210009fe3108004bf18840087fea420043fe5210021fea908010ff14840097fe8420043fe4210021fea108012ff10840087fe6420043fe3210021fe9908010ff0c840027fec220013fe61100077f3088004ff58440005fac220013fc6110001ffa888000ff94440007faa220003fc5110025ffa088000ff90440007fa822004bfc4110023ff9888000ff8c440007fa6220047fc3110021ff9088010ff88440087fa4220043fc21100097f3008004ffd4040027fca020013fd5010009fe2808004ffd00400277e8020013fe4010009fd2008004ff500400277a8020003f94010009ff9808004ff0c040027fe4020013fe2010009fe9008004ff08040027fecb18012ff658c009ff32c6007bf99630027facb18002fd658c009fe32c6004bf19630027fec918012ff648c009ff3246000bf99230027fac918002fd648c009fe3246004bf19230007fea918003fe548c001feaa46000ff15230015fac71800bff538c005ff29c6002ff54e30017f8a71800bff438c001efa1c6002ff90e30017fa871800bfc438c005ee21c6004ffd8a30025fec518013fe628c0037f3146004ff58a3007dfac518013fc628c0097e314600fffd4a3007ffca51803ffd528c01ffe294600fffd0a3007ffc851803ffd428c01ffe2146002ffcca30017fc651800bfd328c005fe1946004ffd8630027fcc31800efe618c009feb0c6000bf58630027f8c318003ff518c001ff28c6000ff54630007f8a318003ff418c001ff20c6000ff50630007f8831800bff318c005ff18c6002ff4c630017f8631803fff218c01fff10c600fff4863007ff84318012fe608c009ffa846004ff94230027faa118013fc508c009ffa046004ff90230027fa8118013fc408c009ff9846004f7cc230017f66118013fc308c009fc1846004ffc8230027fc4118013fd208c009fe1046000ffd9530005feca980037f654c0013fb2a6000ff9953003dfcca98003fd654c0017eb2a6000ff1953003df8ca980037c654c0013e32a6000ffd9130005fec898003bf644c0015fb226000ff99130005fcc898003fd644c0017eb226000ff19130005f8c898003bc644c0015e3226000ffd5130007fca898003fd544c001fe2a26004bfd8d30017fea69800bfe534c005fea9a6002ff14d30017fe869800bfe434c005fea1a6002ff10d30077fec49803aff624c01dff3126001bf98930077fac49803
  | 3 => 0xe2168013ffccb4009ffc65a004ffd32d0027fe1968012ffd8740007fcc3a000efe61d0001feb0e8000bf58740097f8c3a0003ff51d0001ff28e8000ff54740007f8a3a004bff41d0001ff20e8000ff50740097f883a0063ff31d0001ff18e8000ff4c7400c7f863a004fff21d0027ff10e8013ff4874009ff843a0003ff50d0009ff2868000ff54340027f8a1a0063ff30d0009fe1868013ffc8340027fc41a004ffd20d0009fe1068004ffd9640025fecb20013fe659000f7f32c8004ff59640005facb20013fc65900097e32c8014bf59240007fea920003fe5490001feaa48000ff15240027fec720013fe63900057f31c8004ff58e40005fac720013fc63900097e31c8000ffd4e400bffca720003fd539002ffe29c8000ffd0e400bffc872005fbe4390001fea1c8017ff10e400bf788720013ff62900097fb148004ff98a4000dfcc520013fd629002d7eb148004ff18a40025f8c52005bff529002dff2948016ff54a400b7f8a52005bff429002dff2148016ff50a400b7f8852005bff329002dff1948016ff4ca400b7f86520013ff6190009ff30c8003bf98640027fac320002fd6190009fe30c8000ffd4640007fca320003fd5190001fe28c8000ffd0640007fc8320003fd4190001fe20c8017ffcc640007fc6320003fd319002ffe18c8016ffc86400b7fc432005bfd219002dfe10c8004bf98240027fea120013fe5090009fea848004ff14240027fe8120013bf4090001fda048004ffcc240027f86120013ff2090009ff1048004ff48240027f84120003ff65500017fb2a8000dfd9540004fecaa0003fe655000f7f32a8000ff59540005facaa0003fc655000f7e32a8000df19540004f8caa0003ff5450001ff2a28000ff55140007f8a8a0003ff63500017fb1a8000f7d8d40005bec6a0057fe63500057f31a8000ff58d400aff8c6a000afc6350001ee31a8002b718d40007fea6a0057fe5350001fea9a8015ff14d40007fe86a0003bf435002bff21a8000ff50d400077a86a0057fc4350029ffb128014bfd89400a7fcc4a0006fe6250029feb128014bf589400a7f8c4a0006fc6250029ffa928014ff949400a7faa4a0053fc5250029ffa128014ff909400a7fa84a0053fc4250029ff9928014ff8c9400a7fa64a0053fc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8003bf18540007fea2a0003fe5150001fea8a8000ff14540007fe82a0003fe4150001fea0a8000ff105400affe62a0003fe3150001fe98a8015ff0c5400a7fe42a0053fe2150029fe90a8014ff08540007fea0a0013fe5050001fea828004ff14140007fe80a0003fb4050009ff2028004ef901400affe60a0013fc3050029ff9028004ff881400a7fa40a0013fc2050009ffb288004bfd9440027fcca2001efe6510009feb288000bf594
  | 4 => 0x13ff2094009ff104a004ff48250027f84128003ff64540017fb22a000ff99150007fac8a8003fc64540017e322a007ffd5150007fca8a8003fd545400ffe2a2a000ffd8d50005fec6a8073fe63540057f31aa000ff58d500e7f8c6a800afc635400fffa9aa000dfd4d500e7fca6a8003fd5354001bea9aa007ff14d50007fe86a8073fe4354001fea1aa01cff10d500dffec4a806eff6254037ff312a001bf989500dffac4a806efd6254037fe312a001bf1895003ffea4a806ffe5254037fea92a007ff149500dffe84a806ffe4254037fea12a01bff109500dffe64a806ffe3254037fe992a01bff0c950007fec2a8002ff6154001ff30aa000ff58550007f8c2a800efc615400fffa8aa000ff94550007faa2a801ffc5154001ffa0aa000ff90550007fa82a8003fc4154039ff98aa000ff8c550007fa62a8073fc3154037ff90aa01bff885500dffa42a806ffc215400fffa82a007fed4150027fca0a80137e5054039ff982a004ff0c1500dffe40a8013fe2054037fe902a004ff0815003dfcca28013ff6414009ff320a000bf99050027fac828002fd6414009fe320a007ffd505003ffca8280037e541400ffeaa0a007ff1505003ef8a828013ff6314009ff318a002bf98c50027fac628002fd6314009fe318a004bf18c5003ffea62801ffe5314035bf298a007ff54c5003ff8a62801f7c5314001ffa18a01aff90c50007fa862806bfc4314009ffb10a004bfd8850027fcc428006fe6214009f7310a001bb98850027fac428066fd6214009f6b10a000bb58850027f8c428012fc621400fffa90a007ff948500cefca42801ffd521400ffe290a007df148500cffe8428067fe4214033fea10a019ff108500cffe6428067fe3214033fe990a019ff0c850027fec228013fe61140077f308a004ff58450005fac228013fc611400fffa88a007dfd445003ffca22801ffd5114001bea88a007ff14450007fe8228003fe4114001fea08a000ff104500d7fe6228003fe3114001fe988a01aff0c4500cffe4228067fe2114033fe908a019ff08450025fcc028013ff5014009bfa80a004ff94050027f4a028013fd5014009bea80a007fe54050027fe6028013fc3014009ff900a004ff88050027fa4028013fc2014025ffb2e8000bfd9740007fccba001efe65d0001feb2e8000bf59740097f8cba001efc65d0001ffaa68012ff95340007faa9a004bfc54d0025ffb1e8018ff98f40015fcc7a0003fd63d00017eb1e8012ff18f40015f8c7a0003ff53d0031ff29e8000ff54f400c7f8a7a004bff43d0001dfa1e8018ff90f40007fa87a0003bd43d0025fe21e8012ffd8b4009dfec5a004ffe62d00037f3168013ff58b4009dfac5a004bfc62d00037e3168013ffd4b4009ffca5a004ffd52d0027fe2968012ffd0b4009ffc85a004ffd42d0025f
  | 5 => 0x4d31017faa69880bfc534c405ffa1a6202ff90d31017fa869880bfc434c443ffb126221bfd8931007dec498802ef624c443ff3126201bf9893110ffac498886fd624c443fe3126201bf1893110fd8c498806ec624c443ffa926221ff9493110ffaa498887fc524c443ffa126221ff9093110ffa8498887fc424c405ff9926202f7cc931017fc649880bfd324c443ee9926202ff0c931015fec298803ff514c407ff28a6200ff5453101ff8a298803ff414c407ff20a6200ff5053101ff8829880bff314c405fb98a6203ff8c53101fbc629880ffc314c407ee18a6202fd0c53110ffe429880ffe214c443fe90a6203ff08531007fec098802ff604c401ff3026200ff58131007f8c098812fc604c405ff9826202ff0c13110ffe4098887fe204c443fe9026221ff0813103ffec9a801ffe64d40017f326a007ff59350005fac9a801ffc64d400fffaa6a007ff9535003ffaa9a801ffc54d400fffb1ea007ff98f50015fcc7a801ffd63d40017eb1ea007ff18f50015f8c7a801fff53d400fbfa9ea007ff94f5003ffaa7a80037d53d400ffe29ea000ffd0f50107fc87a8003fd43d4041fe21ea007ffd8b5003dfec5a801ffe62d40037f316a007ff58b500fdfac5a801ffc62d40037e316a007ffd4b5003ffca5a801ffd52d400ffe296a01fffd0b500fffc85a807ffd42d403ffe216a01fffccb500fffc65a807ffd32d403ffe196a007ffd875003ffcc3a800efe61d400ffeb0ea000bf5875003ff8c3a801fff51d400fff28ea007ff5475003ff8a3a8003ff41d4001ff20ea000ff50750007f883a8083ff31d4001ff18ea000ff4c750107f863a807fff21d403fff10ea01fff487500fff843a8083ff30d4009fe186a01fffc8350027fc41a807ffd20d4009fe106a01bbf59650027fec928013fe64940017f324a004ff59250005fac928013fc649400fffaa4a000ff95250006fca928003fd549400ffe2a4a000df15250027fec728013fe63940057f31ca004ff58e50005fac728013fc63940097e31ca007ffd4e500f7fca72807b7e5394001fea9ca007ff14e500f6f8a728003ff439403dff21ca000ff50e500f7f88728013ff62940097fb14a004ff98a5000dfcc528013fd629403b7eb14a004ff18a50025f8c52801fff529403bff294a01ddf94a500effaa52801ffc529403bbe294a01dffd0a500effc8528077fd429403bfe214a01dffcca500effc6528077fd329403bfe194a004ffd8650027fcc32800efe6194009feb0ca000bf58650027f8c32801fff5194001bfa8ca000ff94650007faa3280037d519400ffe28ca000ffd0650007fc8328003fd4194001fe20ca01effcc650007fc6328003fd319403dfe18ca01dffc86500effc4328077fd219403bfe10ca004bf98250027fea1280137f509400ffda84a004ffcc250027f86128
  | 6 => 0xdffa128226efd0941137fc84a089bfd425044ddea128226ff10941137fe64a089bfe325044dfe9928226ff0c941007fea2a080ffe5150401fea8a8203ff14541007fe82a0803f74150407ff20a8203ef9054113ffe62a080ffc315044dff90a8203ff88541137fa42a080ffc2150401ffb028200bfd8141007fcc0a0803fd6050401fe3028204bf1814113ffe60a089ffc305044dff9028226ff88141137fa40a089bfc2050407ffb288203bfd944101ffcca2081efe6510407bf32882009f9944101ffaca20802fd6510407beb2882009f5944101ff8ca2080efc651044b7f3208200ffd50410077ea82084bfe5410401feaa08212ff1504100778a82080fff6310407ff3188202bf98c4101ffac620802fd6310407fe3188203bf18c41007fea620893fe5310401fea988224ff14c41097fe8620893fe4310401fea188212ff10c4101ffec42080eff6210407ff3108201bf9884101ffac42088efd6210407fe3108203bf1884111ffea42088ffe5210447fea908223ff14841097fe842088ffe4210447fea108212ff1084111ffe642088ffe3210447fe9908223ff0c84101dfcc22080fff5110407ff2888203ff5444101ff8a22080fff4110407dfa088203ff9044101fec822080ffd4110407dea088200fd5044101ffe622080ffc3110407ff9088203ff8844101ffa422080ffc2110407ffb008203ff98041025fcc02080ffd60104017eb008203ff18041127fe6020893fc3010447ff9008223ff8804111ffa402088ffc2010407ffb2c6203bfd963101ffccb1881efe658c407feb2c6200bf5963101ff8cb1880efc658c407ffb246203bfd923101ffcc918802fe648c407feb246200bf5923101ff8c91880efc648c401ffaa46200ff95231007faa918803fc548c4057eb1c6202ffd4e31017fca71880bfd538c405fe29c6202ffd0e31017fc871880bfd438c405fe21c6203ffd8a3101dfec51880ffe628c4037f3146203ff58a31115fac51880ffc628c4077e3146222ffd4a31117fca51888bfd528c445fe2946222ffd0a31117fc851888bfd428c445fe2146202ffcca31017fc651880bfd328c405fe1946203bf9863101ffea31880ffe518c407fea8c6203ff1463101ffe831880ffe418c407fea0c6203ff1063101ffe631880fdf318c405fb98c6203ff0c63101fe8631880fff218c407ff10c6203ff4863101ff8431880fff608c407ff3046204bf9823101ffac118802fd608c407fe3046202ffcc231017f8611888bff208c445ff1046222ff48231117f84118803ff654c4017fb2a6200ff9953103dfcca98803fd654c4017eb2a6200ff1953103df8ca98803ff644c4017fb226200ff99131005fcc898803fd644c4017eb226200ff19131005f8c898803ff544c401ff2a26200ff55131007f8a89880eff634c405ffa9a6202ff9
  | 7 => 0x288affc32144077f308a203ffd445101efea22880ffe5114407fb288a203ff5445101efaa22881ff55114407ff988a203ff0c45101ffe422880ffe2114407fe908a203ff0845101ffec02880ffe60144097f300a203ff58051005fac02880ffc6014459ff980a22cff0c05115ffe40288affe2014457fe900a22bff08051097fecba0802ff65d0401ff32e8207bf99741007facba0802fd65d0425fe32e8207bf19741007fea9a084bfe54d0401feaa68212ff15341097fec7a08abfe63d04057f31e8200ff58f41005fac7a084bfc63d04057e31e8200ffd4f41157fca7a0803fd53d0455fe29e8212ffd0f41157fc87a0803fd43d0425fe21e8212ffd8b4112dfec5a0897fe62d04037f3168225ff58b4112dfac5a084bfc62d04037e3168225ffd4b4112ffca5a0897fd52d044bfe2968212ffd0b4112f7e85a0897fe42d044bfea168225ef50b41097f885a0897ff32d044bff1968225ff4cb4112ff865a0803ff51d0407ff28e8200ff5474101ff8a3a08abff31d0407fe18e8225ffc874101ffc43a0897fd21d0407fe10e8212ffd8341007fcc1a0812fe60d0401feb068200bf58341097f8c1a08abff30d0455fe1868225ffc834112ffc41a0897fd20d044bfe1068203ffd964101dfecb2080ffe659040f7f32c8203ff59641005facb2080ffc65904077e32c8226bf59241007fea920803bf5490401ff2a48200ff55241007f8a920803bc5490407ffb1c8203ff98e41015fcc72080ffd63904017eb1c8203ff18e4101df8c720803ff5390453ff29c8200ff54e4114ff8a720803ff4390453ff21c8200ff50e4114ff8872080fff62904077fb148203ff98a4100dfcc52080ffd62904517eb148203ff18a4101df8c5208a3ff5290451ff2948228ff54a41147f8a5208a3ff4290451ff2148228ff50a41147f885208a3ff3290451ff1948228ff4ca41147f8652080efe6190407ffa8c8203ff9464101ffaa32080ffc5190407ffa0c8203efd0641007ee832080fff3190407fe18c8203ffc864101ffc432080ffd2190407fe10c8203ffd824101ffcc120812fe6090407feb048200bf5824101ff8c1208a7ff3090453fe1848228ffc8241147fc41208a3fd2090451fe1048200ffd9541005fecaa08037f65504013fb2a8200ff9954103dfccaa0803fd65504017eb2a8200ff1954103df8caa08037c65504013e32a8200ffd5141007fca8a0803fd5450401fe2a28200ffd8d41005fec6a089ffe63504057f31a8200ff58d4113ff8c6a080afc6350401ffa9a8227ff94d41007faa6a089ffc5350401ffa1a8227ff90d41007fa86a089ffc435044dffb128226bfd8941007dec4a0802ef625044dff3128201bf98941137fac4a089afd625044dfe3128201bf18941137d8c4a0806ec625044dffa928226ff94941137faa4a089bfc525044
  | 8 => 0xf50b5118ff885a88c7ff32d4463ff196a231ff4cb5118ff865a88cbff31d4407fe18ea231ffc875101ffc43a88c7fd21d4407fe10ea207ffd835103ffcc1a8812fe60d440ffeb06a200bf5835103ff8c1a88cbff30d4465fe186a231ffc835118ffc41a88c7fd20d4463fe106a22dbf5965101ffec92880ffe64944017f324a203ff59251005fac92880ffc649440fffaa4a200ff95251006fca928803fd549440ffe2a4a200df1525101ffec72880ffe63944057f31ca203ff58e51005fac72880ffc63944077e31ca207ffd4e51187fca728803fd539440ffe29ca200ffd0e51187fc8728803fd4394461fe21ca203ffd8a5101dfec52880ffe62944037f314a203ff58a5117dfac52880ffc62944077e314a207ffd4a5117ffca5288bffd529440ffe294a22fffd0a5117ffc85288bffd429445ffe214a22fffcca5117ffc65288bffd329445ffe194a203bf9865101ffea32880f7f519440ffba8ca203ffcc65101ff8632880fff2194407ff10ca203ff4865101ff8432880fff6094407ff304a204bf9825101ffac128802fd6094407fe304a230ffcc251187f861288bfff209445fff104a22fff4825117ff84128803ff64544017fb22a200efd91510057ec8a8803fe6454401feb22a200ff19151005f8c8a8803bc64544015e322a207ffd5151006fea8a8803fe5454401feaa2a200df5515103ff8a8a8803ff63544017fb1aa22eff98d51015fcc6a8803fd635445dfe31aa202bf18d5103ffea6a88037f535445dff29aa200ff54d51006faa6a881ffc5354401ffa1aa22eff90d51007fa86a88bbfc435445bffb12a22dbfd8951007dec4a8802ef625445bff312a201bf9895116ffac4a88b6fd625445bfe312a201bf1895116fd8c4a8806ec625440fffa92a22ddfd495116ffca4a88b7fd525445bbea92a207ff1495116ffe84a88b7fe425445bfea12a22dff1095116ffe64a88b7fe325445bfe992a22dff0c95103ffea2a881ff75154407ff28aa203df94551177fe62a880ffc315445bff90aa203ff8855116ffa42a880ffc2154401ffb02a200bfd8151007fcc0a8803fd6054401fe302a204bf18151177fe60a88bbfc305445bff902a22dff8815116ffa40a88b7fc205440f7f328a203ffd905101ffcc828802fe6414407feb20a200bf5905101ff8c82881fff541440fff2a0a200df9505103ffaa82881ffc541440fbe2a0a203ffd8c5101ffcc62880afe6314407feb18a200bf58c5101ff8c62880efc631440fffa98a207ff94c5103ffaa62881ffc5314401ffa18a22cff90c51007fa86288b3fc4314407ffb10a203bfd885101ffcc428806fe6214407feb10a22bbf5885101ff8c42880efc621440fffa90a207ff9485103ffaa42881ffc5214457ffa10a22bff9085115ffa84288affc4214457ff990a22bff8c85115ffa64
  | 9 => 0xc037e312a607ffd49531affca4a98d77e5254c6bfea92a607ff149531aef8a4a98d7ff4254c6bff212a635ff509531aff884a980bff3254c05ff192a602ff4c953017f864a9803ff6154c017fb0aa600ff98553007fac2a9803fc6154c077e30aa602ffcc553017f862a98d7ff2154c6bff10aa635ff485531aff842a9803ff6054c017fb02a600ff98153007fac0a9803fc6054c097e302a602ffcc153017f860a98d7ff2054c6bff102a635ff481531aff840a984bff65d0c017fb2e8600ff9974303dfccba1803fd65d0c017eb2e8612ff1974303df8cba180afe64d0c01ffaa68612ff95343007faa9a184bfc54d0c057eb1e8602ffd4f43017fca7a180bfd53d0c05fe29e8602ff90f430177c87a180bde43d0c05fe21e8602ef10f43097fec5a18d2ff62d0c69ff3168601bf98b431a7fac5a18d2fd62d0c25fe3168601bf18b431a7fea5a18d3fe52d0c69fea968634ff14b43097fe85a18d3fe42d0c69fea168612ff10b43017fe65a180bfe32d0c05fe9968602ff0cb43097fec3a1803fe61d0c077f30e8600ff58743005fac3a184bfc61d0c05ff98e8602ff0c7431a7fe43a18d3fe21d0c69fe90e8634ff08743097fec1a1803fe60d0c097f3068600ff58343005fac1a184bfc60d0c05ff9868602ff0c343017b861a18d3ff20d0c69ff1068634ff483431a7f841a1803ff6550c017fb2a8600ff9954303dfccaa1803fd6550c017eb2a8600ff1954303df8caa180aff6450c01ffaa28600ff95143007faa8a1803fc5450c057fb1a8602ffd4d43017fca6a180bfd5350c05fe29a8602ffd0d43007be86a180bfe4350c05df21a8602ff10d430177886a180bdc4350c67ffb128633bfd894319ffcc4a1806fe6250c67feb128633bf5894319ff8c4a1806fc6250c67ffa928633ff9494319ffaa4a18cffc5250c67ffa128633ff9094319ffa84a18cffc4250c05ff9928602ff8c943017fa64a180bfc3250c01ffb0a8600bfd8543007fcc2a1803fd6150c01fe30a8603bf18543017fe62a180bfc3150c67ff90a8633ff8854319ffa42a18cffc2150c01ffb028600bfd8143007fcc0a1803fd6050c01fe3028604bf18143017fe60a180bfc3050c67ff9028633ff8814319ffa40a18cffc2050c0fffb26a207ff99351005fcc9a881ffd64d44017eb26a207ff1935103ffea9a881f7f54d440fff2a6a207ff55351006faa9a881ffc54d440fffb1ea207ff98f51015fcc7a881ffd63d44017eb1ea207ff18f51015f8c7a881fff53d440fbfa9ea207ff94f5103ffaa7a88037d53d440ffe29ea200ffd0f51197fc87a8803fd43d4465fe21ea207ffd8b5103dfec5a881ffe62d44037f316a207ff58b5118dfac5a881ffc62d44037e316a207ffd4b5103efea5a881ffe52d440ffea96a231df54b5103ff8a5a88c7ff42d4463ff216a231f
  | 10 => 0xa8aa003ff63550017fb1aa83bff98d54015fcc6aa003fd6355077fe31aa802bf18d541dffca6aa01ffc5355077ff21aa83bff10d541d7fec4aa0eaff6255075ff312a801bf989541d7fac4aa0eafd6255075fe312a801bf1895403ffea4aa0ebfe5255075fea92a807ff149541d7fe84aa0ebfe4255075fea12a83aff109541d7fe64aa0ebfe3255075fe992a83aff0c954007fec2aa002ff6155001ff30aa800ff58554007f8c2aa00efc6155077ff98aa83bff0c5541d7fe42aa0ebfe2155075fe90aa83aff08554007fec0aa002ff6055001ff302a800ff58154007f8c0aa012fc6055077ff982a83bff0c1541d7fe40aa0ebfe2055075fe902a83aff0815403dfcca2a0e6fe641500fffaa0a807dfd5054097fca82a01fbe541500ffeaa0a800df5505403f7aa82a04bff631500fff318a802bf98c5403ffac62a002fd6315025fe318a802bf18c5403ffca62a01ffc5315071ff218a812ff10c54097fec42a01eff621500fff310a801bf9885403ffac42a0defd6215025fe310a801bf1885403ffea42a01f7f521500fff290a807ff548541befaa42a01ffc5215025ffa10a837efd08541bffc842a0dffd421506fdea10a812ff108541bffe642a0dffe321506ffe990a837ff0c854097fec22a01ffe61150077f308a807ff58454005fac22a04bfc6115071ff988a838ff0c4541bffe422a0dffe211506ffe908a837ff08454097fec02a01ffe60150097f300a807ff58054005fac02a04bfc6015071ff980a838ff0c0541bffe402a0dffe201506ffe900a837ff08054015fccba981fff64d4c0fff326a600bf9935303ffac9a9802fd64d4c0ffe326a607ffd535303ffca9a98037e54d4c0ffeaa6a607ff1535303ef8a9a980afd63d4c05ff29ea602df94f53017bca7a980b5e53d4c05fe29ea602df14f53017fc87a980bfc43d4c0fffb16a607bfd8b5303ffcc5a9806fe62d4c0ffeb16a636bf58b5303ff8c5a9806fc62d4c0fffa96a607ff94b531b6fca5a981ffd52d4c0ffe296a607df14b531b7fe85a98dbfe42d4c6dfea16a636ff10b53017fe65a980bfe32d4c05fe996a602ff0cb5303ffec3a981ffe61d4c077f30ea607ff58753005fac3a981ffc61d4c05ff98ea602ff0c7531b7fe43a98dbfe21d4c6dfe90ea636ff0875303ffec1a981ffe60d4c097f306a607ff58353005fac1a981ffc60d4c05ff986a602ff0c3531b7fe41a98dbfe20d4c6dfe906a636ff08353015fecaa9803ff6454c017fb22a600ff99153007fac8a9803fc6454c017e322a607ffd5153007fca8a98037e5454c01feaa2a607ff15153006f8a8a980aff6354c05ffa9aa607f7d4d53017fca6a980b7e5354c05fe29aa602df14d53017b8a6a980bfe4354c05fe21aa635ffd89531adfec4a98d7fe6254c037f312a635ff589531adfac4a98d7fc6254
  | 11 => 0x8402400400844118001484201842010001000810002520c11004000050018041004430004010000180061884208001010008840401c0000024100c01080100400410a0080413a420000200002300440180030980330001000431042010840080440800000c07000824050100c41080841800100403080c000801308020844139402388400002100000000020800000c2200045008a1080001000100c44004010048209c29400000002518020000c000000000000200020406080462886000c2610020124012880400400000401000010c630802100a000006f30061580000182308084214400046408c44001600080501c2010002008210800108000002e4090012062110821080001842100880004050046008001008e00886200c0010c000006020402180420802400580015600280010021d28a1000400000008820000000010102c0001802084020040000864104400000000400098250004000000000010800010005318401800000420084011840000925080000000008d03014008802200001008e40800001c020004000c210002418c810140099000188025386200c20000000080100827384c401c000000228403000203800400480080200902059c0100021301fff63d500fff31ea802bf98f5403ffac7aa002fd63d500ffe31ea802bf18f5403ffca7aa01ffc53d507dff21ea83eff10f5403ffec5aa01eff62d500fff316a801bf98b5403ffac5aa0f6fd62d500ffe316a801bf18b5403ffea5aa01ffe52d500ffea96a807ff14b541effe85aa0f7bf42d507bff216a83dff50b541ef7a85aa0f7fc42d507bff996a83dff8cb541effa65aa0f7fc32d500fffb0ea807ff9875401dfcc3aa01ffd61d50017eb0ea807ff187541f7fe63aa0fbfc31d507bff90ea83dff887541effa43aa0f7fc21d500fffb06a807ff98354025fcc1aa01ffd60d50017eb06a807ff183541f7fe61aa0fbfc30d507bff906a83dff883541effa41aa0f7fc20d50757eb2ca807bf9925403ffea92a0037f549500fdfaa4a800cfd5254097fec72a0f3fe63950057f31ca800ff58e54005fac72a04bfc63950057e31ca83cff94e5403ff8a72a0f3fe4395025fe21ca812ffd8a541cdfec52a0e7fe62950037f314a839ff58a541cdfac52a04bfc62950037e314a807ffd4a541cefea52a0e7fe5295073fea94a839df54a5403ff8a52a04bff4295073ff214a839ff50a54097f8852a0e7ff3295073ff194a839ff4ca541cff8652a04bff6195001ff30ca803bf98654007fac32a002fd6195025fe30ca83cffcc6541e7f8632a0e7ff2195073ff10ca839ff486541cff8432a04bff6095001ff304a804bf98254007fac12a002fd6095025fe304a83cffcc2541e7f8612a0e7ff2095073ff104a839ff482541cff8412a01fff545500fdfaa2a800ff95154006fc
  | 12 => 0x265000071a0001f98a2c0000000368e7e74b48000000000e800000005a600000003b800000000021609ea484281a018acc079000000044232e02f00000003700000d6c376000420800103e000000000128680034085e423a7d72cb800000000023400007300003010000c7c69021d21ec2942ae118163c8ec0002718e44c141ba00000000000004b6011c00046a0000000c0612b259921c00000030f00012420004aa800000005f000000000000000000007cc50025a8db0000000000000000056045700000000002ada37cf0638d4bb10700009b10001d500000003d180000000000000000abe000221000123a00021b041d2c27c500020a40003b627f0000ade0650000000b34000000000129c06604f00011d600042516483d6000320a3c4a4016500024d467400000000000000000000000e1c91938b95480000000000a793cc7a7000000114800000000005b06c4000000000030500000000000002698000c768ab4cc84d925a3f40000000856000000278872400000014789c00000b700000004c92b61becbac0004ac11e40009cb2bb86e400000000001f0000000000000000000019b80000005c31b6899c0003ef39880000000000000001308000000000000000000006e0130000278000051850100010f00005b100014ac00089500000008c492900020ec50e00000016e4ca8000000000105000000016c808400000000000000002539970b9038932a979933497b127012c0000003b21c95304954335800000032a0000050d9e7f929180000000000002214248000000000000000000011cc00015b0000000e5660607601680006e4000000093e00000000000000004532750000284000033400069c4c40000dc04300ce00006d603f41a8ef80000000001cec95600034c8000000000000125104200000000000003b400008a000094400024940000002990000d9200024b80001144e80000000d8678d000126cf1200002314dc00000000007cc4941392f0800000000000000000002f048280000221c938b00004e68173e580000005c02411c4c5865d14e2000000000001a00000000000002094e6e97705e85ec9b83a80000000000000247000131600011200000000000001ebc000000000171c00000000027180000000001550e0412206c8cc90620003b6a6fd284000040000010a0000001184d725aa3658fb800000037d0f9d1b411808f021000000024f1ecc8c6897039a734bfa99c44709983c451244e87c01267ac000000127e9cc15989d127a00018e21545700000000000000361007886000040d2102454000084000100118023004010148038060000000000121800200220044010002514600086208001104000104008060008a2000420802329000084e400801080212808120400080201840300020000c0080214
  | 13 => 0x22f00001510001ca40000000001cc044e0000000b500005880000000000736000000000000000006b80da0003e912988902620000f6c000000000000100200012b96ec00005200024dc0000000001ee40002d700e80000000000001ea8efc65e14280000000000000000ce80002ca07bc00000002000008ac5f70001bc920c9f5000000000045a1ec800000032800000000006a912180000000003f200000009fa08a8f4492600a00004b000000019b00000007a60000000c9023e000226800c5752b495100006f84b48000000000000000000000000012a51dc7ec000153020a3473a98d652f000021187f000059e1b2000000000000012f4da483349405cc37e8d44d027ac0f400006982240000004810000902000345889800008f00023b47480003b113b08661630000000dee92400010fc33c62a000000037c0003ba800121a72111a80003402af13887a05840000000dcc00000008100000002c80190d389a412a000155ced86560000000506000000000000000000000000006dc14e00000005b3059000000000034a00000000000001ec8d2a00000000000000000000c885289981d800000004b938880000000002aa80000000001ed014112615236313181a043900008e400000047a8fdc9fe4d543312e8a204694d500000009bc00003cca300a4359000000000000021510960000000000c2e5a33820000000000000000042c86342d000000000000000000000003250000ede00048b1aec3685c40000000bc400016f800000049a1f5000000000031700013dc3d809b80000767b50a30000e68000000137c00000003f09e02983634d30df40000001178d3cb5226b2171c7d06c00000000000000001b280b0bf8095453800000000029f800019c7182a3800000000000000000000002bd1c3509e0004b30010000000000000000000024006104ec691000211ca6258c4fc0000c720000000000d0e3f346b80000000000000000000000000000000000043800000000000000000000000000000000000000000000004500000000bd69080002440000000000000105c0000001e180000004639bd800077f000260c0000370001eac00000005608402c2795000065800000022b9f200000004ea92d00000000001ca00000004ef03304c80000001f6411a0000000df86f29e505a97a43960000000a9800000000000000005e400000000dc00007a00000000000000000000000000000021c0000000000000000000252898613b163000000021c46500000004534e800000000002f717640005f131b000038c2a33589b8c00000041c000000000000000003a47414730270e8a67c3fe00000000000000000000353000000077a0000000a2c83e000000230c000000000260400005b4c780003a200000000000002f3000000000000000000000
  | 14 => 0xf0400030b153d1a044d27680000001ca0900e08a844552640a3400000000000006fe00000027140007c4000000061e00000023fc00009914b24e42ee0aa00011bc1e281000025580000002b80000c3200030d800000000001c80003c00000000874000000000000000000000005c00005a402600000000004f080000000000000000000000000000000064b0ef80000008f93ca1df0000000000044c0000001a21b9800000000000000000000851d404320000001a74dde5f3170a4bc2fe78b3e113e05ce47f0c19ba077e0003ba1a940000004ac9bf80000000001a780003cd00000000006b517c20d0000000000223c0003c112c00000007ce00000007c400020b800000019400f00000000000000000000380000103840e00047d8c74d26000000000000000000000000000000001d24e440001cb8000c8a3ff216000117c5960000000000000000000000074c2e498f52be7880758000e860000000000000291000000000075900019b000004d000000031000000000000000002391f2800060500000000000003a3800000000000000000007580000ba934600000000000009804b800003ec6350fe97c00000000000000000316000263116200000000002aa00000000000000a22561c2c9780003218c3400073d000000000087d13a800089400000022287a043800000006a400000013ac000000332000000000003a0000000000000000000000000000000000002300b748ca75211617ec000000000000017860000016180007eb0000d689a28522ff9190eec61040b1da8000000154920c3485c21d611f4772000000000013e00000000000000000d8a7f00000000000000000556000000034a7bb294000000086512f8700dd2000000000000056537600012ae7a019ca65404a0001d000005b225600000006aa80b2b594bcd4200038c800000001c00021d80000001e5000000000003880000000004370000ff0000000103ca4c000000000000000004a00008f000048898340000000000b94000692000000000000044110dc00000037c96d522e0000000a952400000001c400000000af8000a589273bc0000cb000000009fc0002cd000000009400047a100c00000000000007ec00000000000002044362008f7c1314a680000000004ee13b800000045500000001fb000000000000007e800000000020d8a68be498700018a050c5800c4800000083000017806d24e700001040de7e51f48c380006094ee80000003760ae169c0000020001ff465e3853b996bcba036a28e8be89ee3a13850ce11420fe32700001f65ae00019484900001248b88a4a3b8251067c32682b42f96f89ca65100000000005c60081ff93208fc17f15cc8523ba0000000cc29504b88b38000000000258025c00000000000000001190ebcd004fb0ab19d80000000
  | 15 => 0x52e45da5303426ae2879e4d2681dd0000bd800007d41790283229fe1c986d8e7478000021b5246000000000095a00000000000000a000018b0bba0000000fc457a447000000000000008823908b000000000005fa9bb00000003fe2b10d48000000000000000000080c0af00006e406a09199d44028b316d80000000004db1e14ec0064000000000000013c80f02d027021d800023224608f8000ee09d640412400621b313e18940007c70000a840008600000000dba000271112c000000000000000000000004b4f6c3ad0001a586120000001fdc00000000027b476200033980004ee00000000000001d8243000014c0003598000dae00029680004f434645b80011224a500023780000000000e506c424200013580004bf1b380013581d7000000000000904905d00000000000d9800073300016949e600039716d06f67680000d5c0002150000000b7400032604e867683e1f0995c1f20e405980e000053918d19740009f60000b2c1720db3bc857400059d00000000008fe3fd00000008ef058000000066a000000000000000009480000000000000f7e000000000024e0000000060000000000000000000000003dcc180003dd07b12061e74b28600526000177000000022b0000db89423780279ab4000000421a3e0000000000000000000000000000000000000a607e0000152146c00000000000011580004e891d42fa92e00018200000003cf9d3cdce85d05b8000a8c5cf144000000000022a17bd0ee2f133400013e233d40d010c00067200021ac78005c00002300000003ab1dac0007e808207dc00053600000000000003cb000000095d0cb8000e1e14f031000131c00043a80010267b1106000127c22e00024f112c6c53ed0fe40002c500000000008241fa80012dc00000021e8580000000000000000000000000009c90678000b5a94000027cc000000084891c00029026105982da000000000032065000000000000001b780000000000000000452000443000000000000001200005d3000000000000000000008b60000000a540000002fc0180000000029a2c11ca0001f00000a2a10c4af000000000000025ac0000003688e0517e73c0000000ee400000000010ae00006e000000068a00000002b200000018a4000000218a44c7460c000015f8b4083f08180009640004eca65800097f25ba67d3d2000000000000000000026951b0000118a1182924b62080000b7000029f0eb80060000648d70fa20c346300009960000000000cb600023e0000b36000000000000000000000000000004df00000007b80000000c8400000022e000000000000000000002c8913caf66d400017a80000000000000910000000187c000000346800000000022297a000000000018740000001d302a08860000001f8c
  | 16 => 0xbea0000001b4031800040380000003240641e30dfe00031c256cd1296429080000007ae18c1b346966b61d10cd12d41d51e18f8c0000000faa7dc32a000000000103089f3e81d6cd080000001ac00001ab0000000fe8000000203400000000024600000000001c8c0000004958000000839000000000051f000000000000000006a800000048f8ff818200006b9235012000282988c00009b000000134400007a80003d40003f0800000000016900000009d808789800000000b2000000011200015f480e9481a0a0548260004dd009800000013681fc3307d60000000000261000000000002e0b78000000000000000050257200023f4e120270000001234899000000007a0002448cc126651144a12b86ea1063b3130456462000000000000001ef931c00000000000008440001ab24e800000005f0000c8e000000000015a000000233c00000000000000000000000fb1014000000000111000000000000000002d580000000000001fa4000000000000040a8ba3950f7460c000189000000073917580004240000000000e804e10001d1000082323f000053661148e0818304504000000000022237580000001d0462a4c40006440e09f9c00000029c000000057c00000000000000001a800008b200000007920000000ff400075f190a43c39e00025f1b313608710001528e7c4de000000116800000000000000001ae8000e1861c00000000005cd09e1abc000533000000000000040d80000000000000000ce0000000000000000043900000000000000000692000209093d19652212d800000074e3c0986810c6e100a9de80ae41401091b92d06183c3a32000018634d0b4400090b00000000000000001a6c0f63b74a885a8f809ab331a00cf860001de00000006f400017280007c92a880000000000000eec8da6ab11d0ae4000000135025ccda00000000007a80002b700002f400000000000562b03db800000000008d000000000000000006a23de384162c00000000000000000000000000000387000000000000000000003e800018888cc0000004500000400000000000000000000000000000002c28c4cde25bf0000000000000454000000000049610a000079c3540f70a1866236c00000000000000eac79e42f01a800000074d0001408d6800047082852b4000000000098a00000000000000003f106b441e00000000011e484c0000000000000000000095453c0000154e3a949177800110200000000000002dc00000007f800000000000000000a1a14c00000000000000e0000000000080425a104000000000008b04e00000000000000000000000000000000000008fcad00200000a7400025c22e17e40004713520cacb1c604193a73800002200011dc0000dd305877800000000000006a019d3ea0000e4888b3b18688000000
  | 17 => 0x40913e8e386df00000000006ea1050000d306f000006340007691c40c280007fb34f8000000000000000076600c1328be40006a61e400012fa00014c934079c7d50002374000000000000061000024e80010740002ce18c00000000000358a0e00000000000000000002678000000000000078e0002e580000005090488000e4c303000000000000000018c80008d60000000fbc000000000000066e0000df012c00000005c800000000011b00000003af0000b320000e700013c00000b10cc45948a52c984f80004444cb8000c805430c500000009a822700011aa0ff12980000008b938285000001cd00000010ce80400c80000000000000000d7800000027ec0000690e41d4523c3eb23a181c0004464740000000000000054c0000000000000000000000000000000000003500009c2000038000000012615e000000000000000005591500000a34000000000000000000000480000000000150000979000258c9d400000000010b80002de80000000003c902d8a8000003b80000000630000000000660000000000000000000000000003e787e01d48e34dba2000000000000000332000428000000000005786b00004f20a700000002ac0001fd80001b22a6977068a401000000000000000000000000000000000d84000000136c00038633f80012de000000000000000041e8bb400086200000003e2000000000000000000000001464093aa800085a0000001018000000334800000000000000000000000000470d4e000000000137a000000000024c00011e000139e00046680000000003770b7800088300013f0c5600000000000002e4000135cd460b10000000daa55a17a00000008481e600011804f900010103a800014b94d4d1c9b417e0f10b6e678149071c0000001d3800000000000000013de874000000009c65a00000001be000000074c000236000199c0009e801d04d0000000000038516c3073fa8000000582000000000098a00000000006e21af14c00000001b880000004cc000000000016c1bba1bc000000000240400000000000000000000000000000761000000000000000000000004854fc800000000000000000007203cd26b800000000000000000000000a380002ff00022713906de49b00000000001168580c684dd1209060fbe00046880000006974568000000000004000000042510f0ec8fa6000000087c0000000000000000000000106501e000000094089843441380000000000000000ba49a94210b6834e0f00000058f2e87c3608e5400033f00000000000001f6800000000000000000000000000e393a400000008680000000001f6c0000000d3000000000000000000000000000000b500002b0800000000000000000009c30000000360000055a30448879e2cf8f4cab01e6000075862e00000585e
  | 18 => 0xe40000012b380009327f0316800054483c1ba1655038000000000000000000000004800002a082fc5044b0266a2600009c006891c000e0001258e3cdb464f00000012da4d801f000063c10d3f706f52a40000ee00000000000929084bce9b800000002fc0000000000aec9af000000000000000024880000000001e400004a800006f00000000ed80000000003cc800000000000000003504f40998000000986043800000000024900000b068f00000000000000001f7451408e420221c0000002ed8000000890341a1a81100000538274e068e00000794000000000000000000000019f857444035d088c0003e802ea32431687e208933d146000163905818e7910000000250000000000057600005495706403fb20a8b581f800000000008ce6010001c18dac3aa0000e4085455e30a9328000904000001400000022ea1380005fa0001c0000049617318cc0002e01e104840009c74b3a6c86580002e085500006b7294800000000000003e8a1a00000000000000001f20000c261112ec0bdc0005170002278e640000001e603d250e01b14a89d200000019ec476000000000000000042c8c40000000000000084e8921968c54fb852713499191a48d94ba9db90d2805000000101c00018a0158fe40000001bd40008140a200000003040858ca40009db00000a8d587b40a5800000000000025f000000000015b47aa1450000001394000000123083c5f40ad0000c446d903a8000000000000189d2e639e42898dc5c608200000005d2000000000000039a063000000000000000000000000000000f4486400000000002cf000131000000000000000000004950000b1a8e715500000002b512c8c9800000008a00000000d50e289780000003c5022ca9201f1c189745aa953012266c41c0003ffa310b600000001f3483a2720000934324023416082400000047d1698000033112994c02600000027f400000000000000000001fd00000000003268b100000000001ea4000000252000000000000000001949c122f00000000000002790a1090a00007086368cc13e80000b25533f7800000000024527d017674825d988400039f0000000000000000000000000000016403fc8322c2258888239b137936840674200000000003334460000d0c0303331148bda000101000000027b000144cbbe18f3a304c83e413f10b800000054e0ab8000000914267102ceae00000000000001b7022a1580000002e600000007383be9e7400000000015fc0000001289e10000384000020400094700019bc00038c000000000000027b0000000000000020c0000e53d685200007c600000000005240000cf81da0003f98d6000000000000000000e62ea8000568000000000000000010a0000000100000000000000000026740002b649d91ec500000000183c00000
  | 19 => 0x1e3c000000000241c0000000001dc41840001ce0000d9425513411246d00e74111bcc7e426e3130d0c00001b000116400090e014800031c33c1af8534d540b801797d8ae28894c8800000094500023a40003d2000000000000029d000000000000000000000000000d2000049c2ea0000c5e000000175c2109d72e2a3092367122f180000000002a4000000000000000005e4175363a4c0cf4000000145000000017a80000003f80000000b7800038aa7a800089b00003a40000780cda1a091e00000000003f400032f989000000035ea7c11080004d088349622bc0001cb038642408b814400021337e00000008440000000b020004d980005122ad00010145820000000e2c73a90900000000886e5416800030a0001a0000000000003900003021e43f8800025200033c80007ae23d0000000d105984f380000004c037688d00000002a5a1e09cc00000012613e463f0000000d440de18080001c60280f18a9c51e0003ae8f2c00000000000000006c0000038878a8db00000012b8000000000000041a27e80001a400000003c800046b0ed0c8c0009ad00016880008a900008dc2f884944680000008204860d3000022a000000060000000000013c65e500000000007a10ec961c14a6490da800000040c000000047000000000006c05da0001540000000034000000000000004d4000000000263400000000019f400000036d80000000000000e280000000000000000000077859cac40000000000e365452c523dc0001cc0000000f1c56a00000000005ce00000000000000000d500005631a10000af28a24a580000000004bd04bcc7867104d12e04d8000000088000000000002b88cc0000000ea405a245000000000000043f800095e00043c8000000714185a0a8f4a75a007234d28c63146e00000000000000000f7892600000005d88e220000000007ea00017f800000021a800000000000024e0000000000269c0000000000000eca00038f0000d0400000000000000000000f582b034d000000035e00048900000000004e9902119c00000000006f40000000000000000000061d04c0cb33b800000000000000000000001088000ece00000000000000670000000000000174000000000029a07b40000000001afc000017000000000000000000689404d94dca6244a88af245a1cc7328ea2191c1c00000017d81d887c29f00000000008f00000cd4000000422800000000000000012e80002ba000060400010da53ca7a8190000000000000000000000000022f957400016b39680000002ab0000000000000000000000077b4ed1cd400034a000000000000000000000005890359cbc2e20d800000000009933a50c649de00000005d800000000016840007c14b900000004f10001f30000000000098c00000000007
  | 20 => 0xadc9c81e124880000002a83ae20dcb6c426000000128277716600000000000000000000000000000000000000019640c200000000000000000000000d9c1470001ef40000001681ea0000000000068c000811000000000020b4d202400000001cb0000d7c0c437e94183347ed0628000a16000080800136a99200003e00000000001ec109a6140000000a140000000000ac847a3808000c1c1ee1da8000f362c928e1b4c0006b82518c7c92a00d45a8000618000000000103c3e547600000006c842f000064a8f60001f80a7600000003d800000009e90f40009ec05a0508d18000309000000000026a000117a3a5000050530a0ba31d0afc000000000000000000000004c00006654bf1a142a00000000000e4e04900011444fc2be2f6000078c86100000000005193d223cc0000000000000bbc9df0e2160cb580000000000fb000000005a526485b03620742360
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf744c110005bc744c110006df634c110016dc634c110005f7714c11001df4714c110024ff75594100267f7559410004ff7459410094fc7459410004ff7359410014fe7359410014fc7359410004ff725941000cfe7259410004fd725941000cfc72594100067f52594100067d525941001cff715941001cfe715941001cfd715941001cfc715941001e7e515941001e7c5159410024ff7059410024fe7059410024fd7059410024fc70594100267e50594100267c505941003cfe7599010004fd7599010024fe7499010026be7499010014fe7399010004fd7399010014fc7399010094ff729901000cfe7299010004fd729901000cfc7299010096bf4299010006bd429901001cfe719901001cfc719901001ebe419901001ebc4199010024fe7099010024fc7099010026be4099010026bc4099010004ff75590100067f75590100047f755901003cfc75590100067c755901003c7c7559010024ff7459010026bf7459010004ff7359010014fe7359010014fc7359010004ff725901000cfe7259010004fd725901000cfc7259010006bf4259010006bd425901001cff715901001cfe715901001cfd715901001cfc715901001ebe415901001ebc4159010024ff7059010024fe7059010024fd7059010024fc7059010026be4059010026bc405901003cff76d5010024fe76d5010004fd76d5010024fc76d501003e7e65d50100067d65d5010094ff7695010024fe7695010004fd7695010024fc76950102067f659501003e7c6595010096be6495010006bd64950100073f5495010004ff7655010024fe7655010004fd7655010024fc765501003e7e65550100067d6555010006be6455010006bd6455010094ff7615010024fe7615010004fd7615010024fc76150101fe7f651501003e7c6515010004ff7558c1003cfc7558c10004ff7458c10094fc7458c10024ff7358c10026df7358c10036de5358c10036de4358c10004ff7258c1000cfe7258c10004fd7258c1000cfc7258c10036df3258c10006dd3258c1001cff7158c1001cfe7158c1001cfd7158c1001cfc7158c1001ede3158c1001edc3158c10024ff7058c10024fe7058c10024fd7058c10024fc7058c10026de3058c10026dc3058c10026f71058c10026f51058c1003cff76d4c10024fe76d4c10004fd76d4c10024fc76d4c1003e7e65d4c100067d65d4c100375e53d4c10004ff7654c10024fe7654c10004fd7654c10024fc7654c1003e7e6554c100067d6554c10016de6354c10006dd6354c10005fb7054c10025f87054c10094ff76d0c10024fe76d0c10004fd76d0c10024fc76d0c10096be64d0c10006bd64d0c10004ff7650c10024fe7650c10004fd7650c10024fc7650c10006be6450c10006bd6450c10016de6350c10006dd6350c10005fb7050c10025f87050c10
  | 1 => 0x8d10024fd71d8d1001cfc71d8d1004edf31d8d10024fe70d8d1001cfd70d8d10024fc70d8d1004edf30d8d100057f7558d100057c7558d10005bf7458d10005bc7458d1004edc6358d10005ef7258d10045ec7258d10004ff7558d100067f7558d100047f7558d1003cfc7558d100067c7558d1003c7c7558d10004ff7458d10006bf7458d10004bf7458d10094fc7458d10006bc7458d10004bc7458d1004cff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d10004fd7258d1000cfc7258d10006ec7258d1000cec7258d1005cff7158d10006f77158d1006cff7058d10006fb7058d1003cff76d4d10004fe76d4d10004fd76d4d1003cfc76d4d1003e7e65d4d100067d65d4d10006df63d4d10016dc63d4d1004f5e53d4d10004ff7654d10004fe7654d10004fd7654d10004fc7654d1003e7e6554d100067d6554d10094ff76d0d10004fe76d0d10004fd76d0d10094fc76d0d10006df63d0d10016dc63d0d10004ff7650d10004fe7650d10004fd7650d10004fc7650d10024fe76d4510024fc76d45100067f65d451003e7c65d4510025fa70d4510005f970d4510024fc76545100067f655451003e7c6554510005bf7454510005bc7454510005ef7254510045ec7254510005fb7054510025f8705451001ff01054510024fe76d0510006bf64d0510096bc64d0510025fa70d0510005f970d0510024fc76505100057f75505100057c7550510006bf6450510006bc6450510005ef7250510045ec7250510005fb7050510025f87050510005f6768c51001ef6768c51004df5738c510016f6638c510016f4638c510025f6708c510025f4708c51001ef7608c51001ff3608c510217f2208c510217f1208c510024fc764c510006df634c510016dc634c510005ef724c510045ec724c510005fb704c510025f8704c510025f4764c510016f4764c510024f4764c51001df7734c51001fd7734c510007d7634c510016f6634c510016f4634c51004fd4634c510007e7724c51020fe4724c51004fd7324c51020fd5324c510007f3704c510025f6704c510025f4704c510007f0704c51001ef7604c51001ff3604c51020ff2204c51020ff1204c51001cfe76d411001cfc76d41100067f65d411003e7c65d411001df671d4110005f571d411003cff7654110004fd765411001cfc76541100067f655411003e7c6554110005f7715411001df47154110027f0105411001cfe76d0110006bf64d0110096bc64d011001df671d0110005f571d0110094ff7650110004fd765011001cfc76501100057f75501100057c7550110006bf6450110006bc6450110005df735011004ddc7350110005f7715011001df47150110027b84050110014ff764c11004cfd764c11001cfc764c1100057f754c1100057c754c110005b
  | 2 => 0x67c53d9510004ff72d951000cfe72d9510004fd72d951000cfc72d95100067e52d95100067c52d951001cfe71d951001cfc71d9510024fe70d9510024fc70d95100067f6599510005bf7459510005bc7459510005df735951004ddc7359510005ef7259510045ec72595100067f7559510004ff7459510006bf7459510004bf7459510094fc7459510006bc7459510004bc7459510004ff7359510006df7359510004df7359510014fe7359510014fc7359510006dc7359510014dc7359510004ff7259510006ef7259510004ef725951000cfe7259510004fd725951000cfc7259510006ec725951000cec7259510004ff7159510006f77159510004ff7059510006fb705951021e7e505951021e7c5059510004fe761951003e7e65195100067d651951003cfe75d9110004fd75d9110014fe73d9110004fd73d9110014fc73d9110006be43d9110006bc43d9110004ff72d911000cfe72d9110004fd72d911000cfc72d9110006be42d9110006bc42d9110006bf649911003cfe7599110004fd7599110094fe7499110014fe7399110004fd7399110014fc7399110094ff729911000cfe7299110004fd729911000cfc7299110004fd7199110096f57199110004fd7099110096f970991100057f75591100057c7559110005df735911004ddc7359110005ef7259110045ec7259110004ff75591100067f75591100047f755911003cfc75591100067c755911003c7c7559110006bf7459110004ff7359110006df7359110004df7359110014fe7359110014fc7359110006dc7359110014dc7359110004ff7259110006ef7259110004ef725911000cfe7259110004fd725911000cfc7259110006ec725911000cec7259110004ff7159110006f77159110004ff7059110006fb7059110004fe7619110006bd641911003cfe7519110004fd7519110096be7419110014fe7319110004fd7319110014fc7319110006be4319110096bc4319110094ff721911000cfe7219110004fd721911000cfc7219110006be4219110096bc421911001cfe711911001cfc7119110024fe7019110024fc701911003cff76d5110004fe76d5110004fd76d511003cfc76d5110006bf64d5110006bc64d5110094ff7695110004fe7695110004fd7695110094fc76951100067f659511003e7c65951100073f5495110004ff7655110004fe7655110004fd7655110004fc7655110094ff7615110004fe7615110004fd7615110094fc76151100067f651511003e7c6515110006bf6415110096bc641511001df67115110005f57115110014fe76d8d1004ede63d8d1003cfe75d8d10004fd75d8d10094fe74d8d10004fd74d8d1004edc53d8d1004edc43d8d10004ff72d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10006de32d8d1004edc32d8d1001cfe71d
  | 3 => 0xe7695210004fd7695210024fc769521003e7e65952100067d65952100073f54952101ceee6295210004ff7655210024fe7655210004fd7655210024fc76552101d6ee6255210094ff7615210024fe7615210004fd7615210024fc761521003e7e65152100067d6515210096be6415210006bd64152101beee6215210004ff7558e1003cfc7558e10004ff7458e10094fc7458e10026df7358e10004ff7258e1000cfe7258e10004fd7258e1000cfc7258e1005edf3158e10024fc7058e10026de3058e10026dc3058e10026f71058e10026f51058e1003cff76d4e10024fe76d4e10004fd76d4e10024fc76d4e1003e7e65d4e100067d65d4e1005f5e53d4e101b6ee62d4e10004ff7654e10024fe7654e10004fd7654e10024fc7654e1003e7e6554e100067d6554e101aeee6254e10094ff76d0e10024fe76d0e10004fd76d0e10024fc76d0e10096be64d0e10006bd64d0e101a6ee62d0e10004ff7650e10024fe7650e10004fd7650e10024fc7650e10006be6450e10006bd6450e1019eee6250e10006ef7558a10006ee7558a10006ed7558a10006ec7558a10006ef7458a10006ee7458a10006ed7458a10006ec7458a10006ef5458a10006ee5458a10006ed5458a10006ec5458a10006ef7358a10006ee7358a10006ed7358a10006ec7358a10006ef5358a10006ee5358a10006ed5358a10006ec5358a10006ef4358a10006ee4358a10006ed4358a10006ec4358a10056ef7158a10226ee7158a10006ed7158a10226ec7158a10226ee5158a10226ec5158a10226ee4158a10226ec4158a10006ef3158a10226ee3158a10226ec3158a10026ef7058a10026ee7058a10026ed7058a10026ec7058a10026ef5058a10026ee5058a10026ed5058a10026ec5058a10026ef4058a10026ee4058a10026ed4058a10026ec4058a10026ef3058a10026ee3058a10026ed3058a10026ec3058a10026ef1058a10026ee1058a10026ed1058a10026ec1058a1003e7e65d46100067d65d461018eee62d4610006ed62d461001f7651d4610025fa70d4610005f970d461003cff765461003e7e65546100067d6554610005bf7454610005bc7454610005ef7254610055ec725461016eee6254610006ed6254610005fb7054610025f87054610096be64d0610006bd64d061012eee62d0610006ed62d0610025fa70d0610005f970d06100057f75506100057c7550610006be6450610006bd6450610005ef7250610055ec7250610136ee6250610006ed6250610005fb7050610025f87050610014ff764c610024fc764c610016de634c610006dd634c610005ef724c610055ec724c61010eee624c610006ed624c610005fb704c610025f8704c61003cfe76d9510094fe74d9510004fd74d9510014fe73d9510004fd73d9510014fc73d95100067e53d9510
  | 4 => 0x531001cfc76d531003e7e65d53100067d65d5310094ff769531001cfe7695310004fd769531001cfc769531003e7e65953100067d65953100073f5495310004ff765531001cfe7655310004fd765531001cfc765531003e7e65553100067d6555310094ff761531001cfe7615310004fd761531001cfc761531003e7e65153100067d651531001df67115310005f57115310004ff7558f1003cfc7558f10004ff7458f10094fc7458f1001edf7358f1006edc4358f10004ff7258f1000cfe7258f10004fd7258f1000cfc7258f1006edf3258f10006dd3258f10024fc7158f1001ede3158f1001edc3158f1006edf3058f1003cff76d4f1001cfe76d4f10004fd76d4f1001cfc76d4f1003e7e65d4f100067d65d4f1006f5e53d4f10004ff7654f1001cfe7654f10004fd7654f1001cfc7654f1003e7e6554f100067d6554f10005fb7054f10025f87054f10094ff76d0f1001cfe76d0f10004fd76d0f1001cfc76d0f100067e65d0f100067d65d0f10016de63d0f10006dd63d0f10004ff7650f1001cfe7650f10004fd7650f1001cfc7650f100067e6550f100067d6550f10005fb7050f10025f87050f1001df7764c710036f7764c71001f76654c71001f75654c71001fd7734c710016f6634c71001ef4634c710007e7724c71022fe4724c71006fd7324c71022fd5324c710025f6704c710025f4704c71003e7e65d43100067d65d431001df671d4310005f571d43100277a50d431003cff765431003e7e65543100067d6554310005f7715431001df471543100067e65d03100067d65d0310096be64d0310006bd64d031001df671d0310005f571d03100057f75503100057c75503100067e65503100067d6550310006be6450310006bd6450310005df735031006ddc7350310005f7715031001df47150310014ff764c31001cfc764c3100057f754c3100057c754c3100067e654c3100067d654c310005bf744c310005bc744c310016de634c310006dd634c310005f7714c31001df4714c310027d8304c3100267f7559610004ff7459610094fc7459610004ff7359610014fe7359610014fc7359610004ff725961000cfe7259610004fd725961000cfc7259610024fc70596100267e50596100267c505961003cfe7599210004fd7599210026be7499210014fe7399210004fd7399210014fc7399210094ff729921000cfe7299210004fd729921000cfc7299210024fe7099210026be4099210026bc4099210004ff755921003cfc7559210026bf7459210004ff7359210014fe7359210014fc7359210004ff725921000cfe7259210004fd725921000cfc7259210024fc7059210026be4059210026bc405921003cff76d5210024fe76d5210004fd76d5210024fc76d5210006be64d5210006bd64d52101eeee62d5210094ff7695210024f
  | 5 => 0x6bf6450130006bc6450130005df7350130015dc7350130027d8305013003e7f749971003e7e749971003e7d749971003e7c749971003e7f739971003e7e739971003e7d739971003e7c73997100067e43997100067c439971003e7f729971003e7e729971003e7d729971003e7c72997100067f42997100067e42997100067d42997100067c42997100067f32997100067e32997100067d32997100067c329971001e7f719971001e7e719971001e7d719971001e7c719971001e7f419971001e7e419971001e7d419971001e7c419971001e7f319971001e7e319971001e7d319971001e7c319971001e7f219971001e7e219971001e7d219971001e7c219971003e7f709971003e7e709971003e7d709971003e7c70997102367e40997102367c40997100067f30997102367e30997102367c30997100067f20997102367e20997100067d20997102367c209971001e7f109971001e7e109971001e7d109971001e7c109971001e7f7559710004ff7459710094fc7459710004ff7359710014fe7359710014fc73597100067e53597100067c5359710004ff725971000cfe7259710004fd725971000cfc72597100067f52597100067e52597100067d52597100067c5259710024fc715971001e7e515971001e7c51597100067f74597100067e74597100067d74597100067c74597100067f73597100067e73597100067d73597100067c73597100067e43597100067c43597100067f72597100067e72597100067d72597100067c72597100067f42597100067e42597100067d42597100067c42597100067f32597100067e32597100067d32597100067c325971001e7f715971001e7e715971001e7d715971001e7c715971001e7f415971001e7e415971001e7d415971001e7c415971001e7f315971001e7e315971001e7d315971001e7c315971001e7f215971001e7e215971001e7d215971001e7c21597100067f705971021e7e70597100067d705971021e7c705971021e7e405971021e7c40597100067f305971021e7e305971021e7c30597100067f205971021e7e20597100067d205971021e7c205971001e7f105971001e7e105971001e7d105971001e7c105971003cfe7599310004fd759931001ebe7499310014fe7399310004fd7399310014fc7399310006be4399310096bc4399310094ff729931000cfe7299310004fd729931000cfc7299310096bf4299310006bd4299310024fe719931001ebe419931001ebc4199310004ff755931003cfc755931001ebf7459310004ff7359310014fe7359310014fc7359310006be4359310006bc4359310004ff725931000cfe7259310004fd725931000cfc7259310006bf4259310006bd4259310024fc715931001ebe415931001ebc415931003cff76d531001cfe76d5310004fd76d
  | 6 => 0xe7655130004fd7655130004fc76551300067f655513003e7c6555130006bf6455130006bc6455130094ff7615130004fe7615130004fd7615130094fc76151300067f651513003e7c6515130006bf6415130096bc6415130015de7315130005dd73151300067f65d85300067c65d8530006bf64d8530006bc64d853003cfe75d8530004fd75d8530094fe74d8530004fd74d8530024fd73d8530004ff72d853000cfe72d8530004fd72d853000cfc72d853005ef631d853005ef531d8530006f721d8530006f421d8530024fe70d8530024fc70d85300057e75985300057d75985300067f65985300067c6598530005be7498530005bd7498530006bf6498530006bc6498530006f7619853004df970985300057f75585300057c75585300067f65585300067c6558530005bf7458530005bc7458530006bf6458530006bc6458530005ef7258530075ec725853006dfb70585300067f65185300067c6518530006bf6418530006bc641853001ef66118530006f56118530004fe76d4530004fd76d453003cfc76d45300067f65d453003e7c65d4530006bf64d4530006bc64d4530004fe7694530004fd769453001cfc76945300067f659453003e7c6594530006bf6494530006bc6494530004ff7654530004fe7654530004fc76545300067f655453003e7c6554530005bf7454530005bc7454530006bf6454530006bc6454530005ef7254530075ec7254530004fe7614530004fd761453001cfc76145300067f651453003e7c6514530006bf6414530006bc6414530015de7314530005dd7314530004fe76d0530004fd76d0530094fc76d05300067f65d05300067c65d0530006bf64d0530096bc64d0530004fe7690530004fd769053001cfc76905300067f65905300067c6590530006bf6490530006bc6490530004ff7650530004fe7650530004fc76505300057f75505300057c75505300067f65505300067c6550530006bf6450530006bc6450530005ef7250530075ec7250530004fe7610530004fd761053001cfc76105300057e75105300057d75105300067f65105300067c6510530006bf6410530096bc6410530015de7310530005dd7310530025fa7010530005f97010530014fe76d4130014fc76d41300067f65d413003e7c65d4130006bf64d4130006bc64d4130015de73d4130005dd73d41300277a50d4130027d830d413003cff7654130014fe76541300e4fd7654130014fc76541300067f655413003e7c6554130006bf6454130006bc6454130005df7354130015dc7354130014fe76d0130014fc76d01300067f65d01300067c65d0130006bf64d0130096bc64d0130015de73d0130005dd73d0130094ff7650130014fe76501300acfd7650130014fc76501300057f75501300057c75501300067f65501300067c6550130
  | 7 => 0x913024ebe20d9130006bd20d913024ebc20d913024ebe10d913024ebc10d91300057e75991300057d75991300067f65991300067c6599130006bf64991300adf9709913003cfe75991300967e759913003c7e7599130004fd75991300967d75991300047d7599130094fe749913008cbe74991300c4fd7399130096dd7399130094ff729913000cfe7299130004fd729913000cfc729913001cfe7199130004fd71991300acfd7099130096f97099130246de3099130246dc30991300057f75591300057c75591300067f65591300067c65591300c5fb7059130004ff75591300067f75591300047f755913003cfc75591300067c755913003c7c7559130006bf74591300acff7359130006df7359130004df7359130004ff725913000cfe7259130004fd725913000cfc7259130004ff715913001cfc71591300c4ff7059130006fb70591300bcfe76191300067f65191300067c6519130006bd641913003cfe7519130004fd7519130096be7419130024ff7319130014fe7319130024fd7319130014fc7319130096bf431913008ebd4319130094ff721913000cfe7219130004fd721913000cfc7219130096bf4219130006be4219130006bd4219130096bc421913001cfe7119130004fd711913023ede301913023edc30191300bdbe7619130006be76191300bcbe7619130006bf65191300073f65191300063f6519130006be6519130006bd6519130006bc65191300073c65191300063c6519130006bf6219130006be6219130006bd6219130006bc621913008fbb301913023f9e301913023f9c301913008fb83019130096bf7519130006be7519130006bd7519130096bc7519130096bf731913008ebe731913008ebd7319130096bc731913008ebf531913008ebe531913008ebd531913008ebc5319130096bf7219130006be7219130006bd7219130096bc7219130006bf5219130006be5219130006bd5219130006bc521913008ebf321913008ebe321913008ebd321913008ebc3219130096bf7119130006be7119130006bd7119130096bc711913008ebf311913008ebe311913008ebd311913008ebc3119130006bf2119130006be2119130006bd2119130006bc2119130096bf701913023ebe701913008ebd7019130096bc701913023ebe501913023ebc501913008ebf301913023ebe301913023e9e301913008ebd301913023ebc301913023e9c3019130006bf201913023ebe2019130006bd201913023ebc201913023ebe101913023ebc101913003cff76d5130004fe76d5130004fd76d513003cfc76d51300067f65d513003e7c65d5130006bf64d5130006bc64d5130094ff7695130004fe7695130004fd7695130094fc76951300067f659513003e7c6595130006bf6495130096bc64951300073f5495130004ff7655130004f
  | 8 => 0x25e7c10d95300067f6599530005be7499530005bd74995300e5f97099530005bf7459530005bc7459530105fb70595300067f7559530004ff7459530006bf7459530004bf7459530094fc7459530006bc7459530004bc74595300e4ff7359530006df7359530004ff725953000cfe7259530004fd725953000cfc7259530004ff715953001cfc7159530104ff7059530006fb70595300f4fe761953003e7e65195300067d65195300f57e76195300067e76195300f47e76195300067f62195300067e62195300067d62195300067c62195300d77b30195302575e30195302575c30195300d778301953003e7f741953003e7e741953003e7d741953003e7c741953003e7f731953003e7e731953003e7d731953003e7c73195300d67f43195300d67e43195300d67d43195300d67c431953003e7f721953003e7e721953003e7d721953003e7c72195300067f42195300067e42195300067d42195300067c42195300d67f32195300d67e32195300d67d32195300d67c321953003e7f711953003e7e711953003e7d711953003e7c71195300d67f31195300d67e31195300d67d31195300d67c31195300067f21195300067e21195300067d21195300067c211953003e7f701953003e7e701953003e7d701953003e7c70195302567e40195302567c40195300d67f30195302567e30195300d67d30195302567c30195300067f20195302567e20195300067d20195302567c20195302567e10195302567c10195300067f65d91300067c65d913003cfe75d9130004fd75d9130024ff73d9130024fd73d91300bebf43d91300bebd43d9130004ff72d913000cfe72d9130004fd72d913000cfc72d9130006bf42d9130006be42d9130006bd42d9130006bc42d913001cfe71d9130004fd71d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d9130006bf62d9130006be62d9130006bd62d9130006bc62d91300bfbb30d913024f9e30d913024f9c30d91300bfb830d9130006bf75d9130006be75d9130006bd75d9130006bc75d913024ebf73d91300bebe73d91300bebd73d91300bebc73d91300bebf53d91300bebe53d91300bebd53d91300bebc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bd52d9130006bc52d91300bebf32d91300bebe32d91300bebd32d91300bebc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d91300bebf31d91300bebe31d91300bebd31d91300bebc31d9130006bf21d9130006be21d9130006bd21d9130006bc21d91300bebf70d913024ebe70d91300bebd70d913024ebc70d913024ebe50d913024ebc50d91300bebf30d913024ebe30d913024ebc30d9130006bf20d
  | 9 => 0xc76952302067f659523003e7c65952300073f5495230004ff7655230024fe7655230004fd7655230024fc7655230005df7355230015dc7355230094ff7615230024fe7615230004fd7615230024fc76152301fe7f651523003e7c6515230245dd76d0e30006dd76d0e30015de74d0e300179e74d0e30246df64d0e302479e64d0e30006dd64d0e302479d64d0e30247da70d0e30245dd70d0e30007d970d0e30016de60d0e30017da60d0e302479f40d0e302479d40d0e30004ff755863003cfc7558630004ff7458630094fc7458630004ff725863000cfe7258630004fd725863000cfc7258630026f7715863004ef6315863004ef53158630024ff7058630024fd7058630024fc7058630026f61058630026f4105863003cff76d4630024fe76d4630004fd76d46302367f65d463003e7c65d463001cff7694630024fe7694630004fd7694630004ff7654630004fd7654630024fc765463021e7f655463003e7c6554630005bf7454630005bc7454630005df7354630015dc7354630005ef725463007dec725463001cff7614630024fe7614630004fd7614630094ff76d0630024fe76d0630004fd76d063001cff7690630024fe7690630004fd7690630015de7390630005dd7390630004ff7650630004fd7650630024fc76506300057f75506300057c7550630005df7350630015dc7350630005ef725063007dec725063001cff7610630024fe7610630004fd76106300057e75106300057d7510630025fa7010630005f9701063003cfe76d9530094fe74d9530004fd74d9530024ff73d9530014fe73d9530024fd73d9530014fc73d95300f67f53d95300f67d53d9530004ff72d953000cfe72d9530004fd72d953000cfc72d95300067f52d95300067e52d95300067d52d95300067c52d953001cfe71d9530004fd71d953003c7e76d95300067f62d95300067e62d95300067d62d95300067c62d95300f77b30d953025f5e30d953025f5c30d95300f77830d95300067f74d95300067e74d95300067d74d95300067c74d953025e7f73d95300f67e73d95300f67d73d95300f67c73d95300f67f43d95300f67e43d95300f67d43d95300f67c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95300f67f32d95300f67e32d95300f67d32d95300f67c32d95300067f71d95300067e71d95300067d71d95300067c71d95300f67f31d95300f67e31d95300f67d31d95300f67c31d95300067f21d95300067e21d95300067d21d95300067c21d95300f67f70d953025e7e70d95300f67d70d953025e7c70d953025e7e40d953025e7c40d95300f67f30d953025e7e30d953025e7c30d95300067f20d953025e7e20d95300067d20d953025e7c20d953025e7e10d9530
  | 10 => 0x8840026ee4058840026ed4058840026ec4058840026ef3058840026ee3058840026ed3058840026ec3058840026ef1058840026ee1058840026ed1058840026ec1058840004ff755844003cfc7558440004ff7358440014fe7358440014fc7358440004ff725844000cfe7258440004fd725844000cfc7258440026f77158440096f74158440096f44158440026f61058440026f4105844003cff76d4440024fe76d4440004fd76d444003e7e65d44400067d65d444018eee62d4440006ed62d444001cff7694440024fe7694440004fd769444017eee6294440006ed629444001ef66194440006f56194440004ff7654440004fd7654440024fc765444003e7e65544400067d6554440005bf7454440095bc7454440005ef7254440085ec725444016eee6254440006ed625444001ef66154440006f5615444001cff7614440024fe7614440004fd761444015eee6214440006ed6214440004fd7690440146ee6290440006ed6290440004ff76504400057f75504400057c7550440005ef7250440085ec7250440136ee6250440006ed625044001cff768c440024fe768c440004fd768c440095be748c440005bd748c440116ee628c440006ed628c44001ef6618c440006f5618c440004ff764c440004fd764c440024fc764c440005bf744c440095bc744c440016de634c440006dd634c440005ef724c440085ec724c44010eee624c440006ed624c44001ef6614c440006f5614c440005fb704c440025f8704c440025fb7650040006fb7650040004fb76500400077b7550040007787550040025fb7450040027bb7450040096fa6450040027ba6450040097ba5450040007b95450040007db7350040007d87350040267ba4350040097b84350040027ea6250040027e96250040097bb4150040007b941500400267f7559630004ff7459630094fc74596300e67f53596300e67d5359630004ff725963000cfe7259630004fd725963000cfc7259630004ff715963001cfc7159630024fe7059630024fc70596300267e50596300267c505963003cfe7599230004fd7599230026be7499230096bf43992300c6bd4399230094ff729923000cfe7299230004fd729923000cfc729923001cfe7199230004fd7199230024fe7099230024fc7099230026be4099230026bc4099230004ff75592300067f75592300047f755923003cfc75592300067c755923003c7c7559230026bf7459230006df73592300aebf43592300aebd43592300aedc4359230004ff725923000cfe7259230004fd725923000cfc7259230004ff715923001cfc7159230024fe7059230024fc7059230026be4059230026bc405923003cff76d5230024fe76d5230004fd76d5230024fc76d5230015de73d5230005dd73d5230094ff7695230024fe7695230004fd7695230024f
  | 11 => 0x57e75105400057d75105400067f65105400067c6510540006df6310540126dc6310540004fe768c540004fd768c54001cfc768c5400067f658c5400067c658c540006df638c540016dc638c540004ff764c540004fe764c540004fc764c5400067f654c5400067c654c540006df634c540016dc634c540005ef724c5400a5ec724c540004fe76d4140094fc76d41400067f65d414003e7c65d4140005be74d4140005bd74d4140006df63d4140106dc63d41400277a50d414003cff7654140004fd765414003cfc76541400067f655414003e7c6554140005bf7454140005bc7454140006df63541400e6dc6354140027b840541400067f65d01400067c65d0140025be74d0140026bf64d0140006df63d01400c6dc63d0140024fa76d01400077b65d01400077865d0140025fa74d0140026fb64d0140027bb64d0140007db63d0140007d863d0140097bb43d0140007b943d0140024ff75594400267f755944003cff7459440094fe745944003cfd7459440094fc74594400967e54594400967c5459440004ff7359440014fe7359440014fc7359440004ff725944000cfe7259440004fd725944000cfc7259440004ff715944001cfc7159440024fe7059440024fc70594400267e50594400267c5059440004fd76d50400973e54d50401eeee62d5040004ff76550401d6ee6255040004ff7558c4003cfc7558c40014fd7458c40026df7358c4008ede5358c40096df4358c4008ebe4358c4008ebc4358c40096dc4358c40004ff7258c4000cfe7258c40004fd7258c4000cfc7258c40004ff7158c4001cfc7158c4008edf3158c40024fc7058c40026bf4058c40026bd4058c40026de3058c40026dc3058c4003cff76d4c40024fe76d4c40004fd76d4c4003e7e65d4c400067d65d4c40095be74d4c40005bd74d4c4008f5e53d4c401b6ee62d4c40004ff7654c40004fd7654c40024fc7654c4003e7e6554c400067d6554c40005bf7454c40095bc7454c40016de6354c40006dd6354c401aeee6254c40005fb7054c40025f87054c400c4ff7650c4024dbf7450c400c6be6450c400979c4350c4019eee6250c40006ef7558840006ee7558840006ed7558840006ec7558840086ef7458840096ee7458840086ed7458840096ec7458840006ef5458840096ee5458840006ed5458840096ec5458840006ef7358840006ee7358840006ed7358840006ec7358840006ef5358840006ee5358840006ed5358840006ec5358840096ef4358840006ee4358840006ed4358840096ec4358840006ef7158840006ee7158840006ed7158840006ec7158840096ef4158840096ec4158840006ef3158840006ec3158840026ef7058840026ee7058840026ed7058840026ec7058840026ef5058840026ee5058840026ed5058840026ec5058840026ef405
  | 12 => 0xc6518d400065c6518d400af9d7418d4023edf6418d4023e9f6418d40006df6218d40006de6218d40006dd6218d40006dc6218d4023f9e4018d4023f9c4018d40004fe76d4d40004fd76d4d4003cfc76d4d400067f65d4d4003e7c65d4d40006df63d4d40016dc63d4d400af5e53d4d40004ff7654d40004fe7654d40004fc7654d400067f6554d4003e7c6554d40006df6354d40016dc6354d400bcfe76d0d400067f65d0d400067c65d0d40016dc63d0d40005be76d0d400bebe76d0d400bcbe76d0d400073f65d0d400073c65d0d400adbd73d0d400079f63d0d40016be63d0d40016bc63d0d400af9c63d0d400169c63d0d40025be70d0d40025bc70d0d40096bf60d0d402479c30d0d40024fc7650d400067f6550d400067c6550d40006df6350d40016dc6350d40005fb7050d40025f87050d40025bc7650d40016bc7650d40024bc7650d400073f6550d400073c6550d400adbf7350d400079f7350d400079f6350d40016be6350d40016bc6350d400af9c6350d400169c6350d40007bb7050d40025be7050d40025bc7050d40007b87050d40025b87050d400067f65d85400067c65d8540006df63d8540006dc63d854003cfe75d8540004fd75d8540014fe73d8540004fd73d8540014fc73d8540004ff72d854000cfe72d8540004fd72d854000cfc72d8540006f721d8540006f421d85400057e75985400057d75985400067f65985400067c65985400adde7398540005dd7398540006df6398540006dc6398540006f761985400057f75585400057c75585400067f65585400067c6558540005df73585400addc7358540006df6358540006dc6358540005ef72585400a5ec72585400067f65185400067c6518540006df6318540006dc631854001ef66118540006f56118540004fe76d4540004fd76d454003cfc76d45400067f65d454003e7c65d4540006df63d4540196dc63d4540004fe7694540004fd769454001cfc76945400067f659454003e7c6594540006df6394540186dc6394540004ff7654540004fe7654540004fc76545400067f655454003e7c6554540005bf7454540005bc7454540006df6354540176dc6354540005ef72545400a5ec7254540004fe7614540004fd761454001cfc76145400067f651454003e7c6514540005be7414540005bd7414540006df6314540166dc6314540004fe76d05400067f65d05400067c65d0540006df63d0540156dc63d0540024fe76905400067f65905400067c6590540006df639054014edc6390540006f7619054001ef46190540025fa7090540005f97090540024fc76505400057f75505400057c75505400067f65505400067c6550540006df635054013edc6350540005ef72505400a5ec7250540006f7615054001ef46150540005fb7050540025f87050540004fe7610540
  | 13 => 0x95400067d62195400067c62195401ff3e40195401ff3c401954003e7f741954003e7d741954003e7f731954003e7e731954003e7d731954003e7c73195400067e43195400067c431954003e7f721954003e7e721954003e7d721954003e7c72195400067f42195400067e42195400067d42195400067c42195400067f32195400067e32195400067d32195400067c321954003e7f711954003e7e711954003e7d711954003e7c71195400067f31195400067c31195400067f21195400067e21195400067d21195400067c211954003e7f701954003e7e701954003e7d701954003e7c70195401fe7e40195400067d40195401fe7c40195400067f30195401fe7e30195401fe7c30195400067f20195401fe7e20195400067d20195401fe7c20195401fe7e10195401fe7c1019540024fe76d5140024fc76d51400067f65d514003e7c65d51401f6dc63d5140025fa70d5140005f970d5140004fe76951400067f659514003e7c65951400073f54951401e6dc6395140024fc76551400067f655514003e7c65551401dedc6355140005fb7055140025f87055140004fe76151400067f651514003e7c65151400073d54151401c6dc6315140014fe76d8d400067f65d8d400067c65d8d400aede63d8d4003cfe75d8d40004fd75d8d40024fd74d8d40014fc74d8d400aede53d8d400aedc53d8d400aede43d8d40004ff72d8d4000cfe72d8d40004fd72d8d4000cfc72d8d400aedf32d8d40006de32d8d40006dd32d8d400aedc32d8d4001cfe71d8d40004fd71d8d400aedf31d8d400aedc31d8d400aedf30d8d400adde76d8d40014de76d8d40006df65d8d400075f65d8d400065f65d8d40006de65d8d40006dd65d8d40006dc65d8d400075c65d8d400065c65d8d402479f74d8d40006df62d8d40006de62d8d40006dd62d8d40006dc62d8d402479e40d8d402479c40d8d40006df75d8d40006de75d8d40006dd75d8d40006dc75d8d40246df74d8d400aede74d8d40006df54d8d40006de54d8d40006dd54d8d40006dc54d8d40006df72d8d40006de72d8d40006dd72d8d40006dc72d8d40006df52d8d40006de52d8d40006dd52d8d40006dc52d8d40006df42d8d40006de42d8d40006dd42d8d40006dc42d8d40006df71d8d40006de71d8d40006dd71d8d40006dc71d8d40006df21d8d40006de21d8d40006dd21d8d40006dc21d8d40006df70d8d40246de70d8d40006dd70d8d40246de50d8d40246dc50d8d40246de40d8d40246dc40d8d40006df20d8d40246de20d8d40006dd20d8d40246dc20d8d40246de10d8d40246dc10d8d400057f7558d400057c7558d400067f6558d400067c6558d400aedc6358d40005de7618d400aede7618d40006df6518d400075f6518d400065f6518d40006de6518d40006dd6518d40006dc6518d400075
  | 14 => 0xcfe7258640004fd725864000cfc7258640026f77158640026f61058640026f4105864003cff76d4640024fe76d4640004fd76d46402367f65d464003e7c65d464001cff7694640024fe7694640004fd769464003e7e65946400067d6594640004ff7654640004fd7654640024fc765464021e7f655464003e7c6554640005bf7454640005bc7454640005ef72546400b5ec725464001cff7614640024fe7614640004fd761464003e7e65146400067d651464001ef66190640006f56190640025fa7090640005f9709064001cff76506400057f75506400057c7550640005ef72506400b5ec725064001ef66150640006f56150640005fb7050640025f870506400057e75106400057d751064001cff768c640024fe768c640004fd768c640005be748c640005bd748c64001ef6618c640006f5618c640004ff764c640004fd764c640024fc764c640005bf744c640005bc744c640005ef724c6400b5ec724c64001ef6614c640006f5614c640025f976d0240096f976d0240027ba74d0240097ba54d0240007b954d024003cfe76d9540094fe74d9540094fc74d9540014fe73d9540004fd73d9540014fc73d95400067e53d95400067c53d9540004ff72d954000cfe72d9540004fd72d954000cfc72d95400067f52d95400067e52d95400067d52d95400067c52d954001cfe71d9540004fd71d954003c7e76d95400067e63d95400067c63d95400067f62d95400067e62d95400067d62d95400067c62d95402073e40d95402073c40d95402067f74d95400067d74d95400067f73d95400067e73d95400067d73d95400067c73d95400067e43d95400067c43d95400067f72d95400067e72d95400067d72d95400067c72d95400067f42d95400067e42d95400067d42d95400067c42d95400067f32d95400067e32d95400067d32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95400067f31d95400067c31d95400067f21d95400067e21d95400067d21d95400067c21d95400067f70d95402067e70d95400067d70d95402067c70d95402067e40d95402067c40d95400067f30d95402067e30d95402067c30d95400067f20d95402067e20d95400067d20d95402067c20d95402067e10d95402067c10d95400067f65995400adde7399540005dd7399540005df73595400addc73595400067f7559540004ff7459540006bf7459540004ff7359540006df7359540004df7359540014fe7359540014fc7359540006dc7359540014dc7359540004ff725954000cfe7259540004fd725954000cfc7259540004ff715954001cfc7159540004ff7059540006fb7059540004fe761954003e7e65195400067d65195400057e76195400067e76195400047e76195400067e63195400067c63195400067f62195400067e621
  | 15 => 0xd7654f40094fc7654f400067f6554f4003e7c6554f40005fb7054f40025f87054f40025bd76d0f40016bd76d0f40024bd76d0f40016be63d0f400979e63d0f400979d63d0f40016bc63d0f40025be70d0f40097ba70d0f40097b970d0f40025bc70d0f402479c30d0f4008cff7650f40005bf7650f4008ebf7650f4008cbf7650f400979f7350f40016be6350f40016bc6350f40025be7050f40025bc7050f40096f7619874001ef46198740005ef725874009dec7258740096f46158740004ff755874003cfc7558740024fc7458740004ff7358740014fe7358740014fc7358740004ff7258740006ef7258740004ef725874000cfe7258740004fd725874000cfc7258740006ec725874000cec7258740096f74158740096f4415874003cff76d4740094fe76d4740004fd76d474003e7e65d47400067d65d474001cff7694740094fe7694740004fd7694740004ff7654740004fd7654740094fc765474003e7e65547400067d6554740005bf7454740095bc7454740005ef725474009dec725474001cff7614740094fe7614740004fd7614740095be7414740005bd74147400057f75507400057c7550740005ef725074009dec725074001cff768c740094fe768c740004fd768c740004ff764c740004fd764c740094fc764c740005ef724c74009dec724c740005fb704c740025f8704c74003e7e65d43400067d65d4340095be74d4340005bd74d434003cff765434003e7e65543400067d6554340005bf7454340095bc7454340027ba40543400267f7559640004ff7359640014fe7359640014fc7359640004ff725964000cfe7259640004fd725964000cfc72596400067f52596400067d5259640004ff715964001cfc7159640024fc70596400267e50596400267c505964003e7e65d52400067d65d5240025fa70d5240005f970d52402067f659524003e7c65952400073f549524003cff765524003e7e65552400067d6555240005fb7055240025f870552401fe7f651524003e7c6515240004ff7558e4003cfc7558e40026df7358e400bebe4358e400bede4358e400bebc4358e40004ff7258e4000cfe7258e40004fd7258e4000cfc7258e40004ff7158e4001cfc7158e40024fc7058e40026bf4058e40026bd4058e40026de3058e40026dc3058e4003cff76d4e40024fe76d4e40004fd76d4e4003e7e65d4e400067d65d4e40005be74d4e40005bd74d4e400bf5e53d4e40004ff7654e40004fd7654e40024fc7654e4003e7e6554e400067d6554e40005bf7454e40005bc7454e400acfd76d0e4023dbe74d0e40016dc63d0e40014ff7650e4024dbf7450e40016de6350e40006dd6350e400bf9c4350e40005fb7050e40025f87050e40004ff755864003cfc7558640004ff7358640014fe7358640014fc7358640004ff7258640
  | 16 => 0x8850026ee3058850026ed3058850026ec3058850026ef1058850026ee1058850026ed1058850026ec1058850004ff7458450094fc7458450004ff7358450014fe7358450014fc7358450004ff725845000cfe7258450004fd725845000cfc7258450026f7715845003ef7515845003ef45158450026f61058450026f4105845003d7f76544500067f76544500073f74544500057c74544500073c74544500053c74544500067d64544500d57e73544500d57c73544500067d63544500076f72544500cd7e72544500cd7c72544502876c72544500cd6c725445003e7f625445003f6e625445027e7d625445003f6d62544500066d625445003d7f715445003f77715445001e7e615445001e7c615445021d7f705445021e7e605445003f7a6054450094ff76d0450024fe76d0450004fd76d04500057f75d045003d7c75d0450096be64d0450006bd64d045012eee62d0450006ed62d045001cff7690450024fe7690450004fd769045003d7e75904500057d75904502773c5490450146ee6290450006ed629045001ef66190450006f56190450004ff7650450004fd7650450024fc76504500057f755045003d7c7550450006be6450450006bd6450450005ef72504500cdec7250450136ee6250450006ed625045001ef66150450006f5615045001cff7610450024fe7610450004fd761045003d7e75104500057d751045026f3c541045011eee6210450006ed621045001cff768c450024fe768c450004fd768c45003d7e758c4500057d758c450116ee628c450006ed628c45001ef6618c450006f5618c450004ff764c450004fd764c450024fc764c4500057f754c45003d7c754c450016de634c450006dd634c450005ef724c4500cdec724c45010eee624c450006ed624c45001ef6614c450006f5614c450005fb704c450025f8704c450096be74d9740014fe73d9740004fd73d9740014fc73d9740094ff72d974000cfe72d9740004fd72d974000cfc72d974001cfe71d9740004fd71d9740096f970d97402067e50d97402067c50d9740004fd76997400967f65997400967c659974003cff76597400967c65597400967f7559740024fc74597400967e54597400967c5459740004ff7359740014fe7359740014fc73597400067e53597400067c5359740004ff725974000cfe7259740004fd725974000cfc72597400067e52597400067c5259740004ff715974001cfc71597400973e54d53400973c5455340014ff7658f40096dc6358f40004ff7558f4003cfc7558f40024fc7458f40096df4358f40096dc4358f40004ff7258f4000cfe7258f40004fd7258f4000cfc7258f40004ff7158f4001cfc7158f400c6df3058f4003cff76d4f40094fe76d4f40004fd76d4f400067f65d4f4003e7c65d4f400c75e53d4f40004ff7654f40004f
  | 17 => 0x4fc76505500057f755055003d7c7550550005ef72505500ddec7250550004fe7610550004fd761055001cfc761055003d7e75105500057d7510550006bf6410550096bc6410550004fe768c550004fd768c55001cfc768c550006df638c550016dc638c550004ff764c550004fe764c550004fc764c550005ef724c5500ddec724c550024fe7499050026be749905003ebf5499050096bc5499050014fe7399050004fd7399050014fc7399050094ff729905000cfe7299050004fd729905000cfc729905001cfe7199050004fd7199050026be4099050026bc4099050026bf745905003ebf545905003e7c545905003ebc545905003e3c5459050004ff7359050014fe7359050014fc7359050004ff725905000cfe7259050004fd725905000cfc7259050004ff715905001cfc715905003e7f5159050026be4059050026bc405905003d7d76950500067d769505003d7e749505003f3e74950500067d64950500d57e73950500d57c73950500cd7e72950500cd7c729505003e7f629505003f6e62950502967d629505003f6d62950500057d719505028e7e61950502057d70950502067e609505003f7a6095050014fd7558c50004ff7458c50094fc7458c500067e5458c5003e7c5458c50024ff7358c50026df7358c5003edf5358c500d67e5358c5003e7c5358c5003edc5358c500d6de4358c50004ff7258c5000cfe7258c50004fd7258c5000cfc7258c500067e5258c5003e7c5258c50004ff7158c5001cfc7158c5003e7f5158c500d6df3158c50024fc7058c500267f5058c500267d5058c50026de3058c50026dc3058c50094ff76d0c50024fe76d0c50004fd76d0c5003d7e75d0c500057d75d0c50096be64d0c50006bd64d0c501a6ee62d0c50004ff7650c50004fd7650c50024fc7650c500057f7550c5003d7c7550c50006be6450c50006bd6450c50016de6350c50006dd6350c5019eee6250c50005fb7050c50025f87050c5003eef75588500ce6f755885003eee755885003eed755885003eec755885003e6c7558850006ef7458850006ee7458850006ed7458850006ec745885003eef545885003eee54588500066e545885003eed545885003eec545885003e6c5458850006ef7358850006ee7358850006ed7358850006ec735885003eef535885003eee535885003eed535885003eec5358850006ef4358850006ee4358850006ed4358850006ec4358850006ef7158850006ee7158850006ed7158850006ec715885003eef515885003e6f515885003eee515885003eed515885003eec5158850006ef3158850006ec3158850026ef7058850026ee7058850026ed7058850026ec7058850026ef5058850026ee5058850026ed5058850026ec5058850026ef4058850026ee4058850026ed4058850026ec4058850026ef305
  | 18 => 0xe768c650004fd768c65003d7e758c6500057d758c65001ef6618c650006f5618c650004ff764c650004fd764c650024fc764c6500057f754c65003d7c754c650005ef724c6500edec724c65001ef6614c650006f5614c650014fe73d9150004fd73d9150014fc73d9150006be43d9150006bc43d9150004ff72d915000cfe72d9150004fd72d915000cfc72d9150006bf42d9150006bd42d915001cfe71d9150004fd71d9150006bf6499150005df73591500e5dc7359150006bd6419150014fe7319150004fd7319150014fc7319150006be4319150096bc4319150094ff721915000cfe7219150004fd721915000cfc7219150096bf4219150006bd421915001cfe7119150004fd71191501fe7e50191501fe7c5019150024fe7695150006bf6495150096bc649515003f3f5495150025fa7095150005f97095150024fc7655150006bf6455150006bc645515003f3c5455150005fb7055150025f87055150014fe76d8d500e6de63d8d50024fd75d8d50014fc75d8d50094fe74d8d50004fd74d8d500e6de53d8d500e6dc43d8d50004ff72d8d5000cfe72d8d50004fd72d8d5000cfc72d8d500e6df32d8d50006dd32d8d5001cfe71d8d50004fd71d8d500e6dc31d8d5003cfd70d8d500e6df30d8d50005bf7458d50005bc7458d500e6dc6358d500057e76d4d5003e7e76d4d500f47e76d4d500067c64d4d500e57d73d4d500167e63d4d500167c63d4d501b67e62d4d501b67c62d4d500257e70d4d500257c70d4d5003e7f60d4d5003f7b60d4d50024fc7654d50006df6354d50016dc6354d50005fb7054d50025f87054d500257c7654d500167c7654d500247c7654d500067c6454d5003d7f7354d5003f5f7354d500075f6354d500167e6354d500167c6354d500e75c6354d501ae7e6254d501ae7c6254d500077b7054d500257e7054d500257c7054d50007787054d5003e7f6054d5003f7b6054d50004fe76d0d50004fd76d0d50094fc76d0d50006df63d0d50016dc63d0d50004ff7650d50004fe7650d50004fc7650d50094fe74d8550004fd74d8550014fe73d8550004fd73d8550014fc73d85500067f53d85500067d53d8550004ff72d855000cfe72d8550004fd72d855000cfc72d85502367e50d85502367c50d8550006f76198550005bf7458550005bc7458550005df73585500e5dc7358550005ef72585500ddec725855001ef66118550006f56118550024fe7694550006f7619455001ef46194550025fa7094550005f97094550024fc7654550005bf7454550005bc7454550005ef72545500ddec7254550006f7615455001ef46154550005fb7054550025f87054550004fe76d0550004fd76d0550094fc76d0550004fe7690550004fd769055001cfc7690550006bf6490550006bc6490550004ff7650550004fe7650550
  | 19 => 0x52502077a70952502057d709525000779709525000579709525003e7e6095250006be6455250006bd6455250005fb7055250025f8705525003f7b50552501fd7d761525003e7d761525003f3e74152500067d64152500f57e731525003d7c73152500ed7e721525003d7c72152501fe7f62152502c67d62152502bf3f42152502bf3d42152500057d71152502b67e611525003d7f70152501fd7d701525003f7a6015250004ff7458e50094fc7458e500067e5458e500067c5458e50026df7358e500f67e5358e500f6de5358e500f65e5358e500f67c5358e50004ff7258e5000cfe7258e50004fd7258e5000cfc7258e500067e5258e500067c5258e50004ff7158e5001cfc7158e50024fc7058e500267f5058e500267d5058e50026de3058e50026dc3058e50014ff7654e5025d7f7554e50016de6354e50006dd6354e50005fb7054e50025f87054e5003f7b5054e50094ff76d0e50024fe76d0e50004fd76d0e5003d7e75d0e500057d75d0e50096be64d0e50006bd64d0e50004ff7650e50004fd7650e50024fc7650e500057f7550e5003d7c7550e50006be6450e50006bd6450e50004ff7458650094fc7458650004ff7358650014fe7358650014fc7358650004ff725865000cfe7258650004fd725865000cfc7258650026f77158650024fc7058650026f61058650026f410586502357d76d465003e7d76d46500057e74d46500067d64d46500f57e73d465003d7c73d46500067d63d46500ed7e72d465003d7c72d46502367f62d46502ae7d62d465001e7e61d465001e7c61d465003d7f70d46502357d70d465003f7a60d465001ef66194650006f5619465003f775194650025fa7094650005f9709465003f7b509465001cff7654650005bf7454650005bc7454650005ef72546500edec725465001ef66154650006f56154650005fb7054650025f8705465001c7f76546500073f74546500057c74546500073c74546500053c74546500067d64546500f57e73546500f57c73546500067d63546500076f72546500ed7e72546500ed7c72546502a76c72546500ed6c725465021e7f625465029e7d625465003d7f715465003f77715465001e7e615465021f76615465021f75615465001e7c615465021d7f70546500077b70546500057b705465021f78705465003e7e6054650094ff76d0650024fe76d0650004fd76d06500057f75d065003d7c75d065001cff7690650024fe7690650004fd769065003d7e75906500057d7590650006be6490650006bd64906500073c5490650004ff7650650004fd7650650024fc76506500057f755065003d7c7550650005ef72506500edec725065001cff7610650024fe7610650004fd761065003d7e75106500057d7510650096be6410650006bd64106500073c541065001cff768c650024f
  | 20 => 0x6ef6258131006ec6258131006ef6218131006ec6218131026fa6018131006f96018131024fe7599350096be749935003ebf5499350096bc5499350014fe7399350004fd7399350014fc739935003e7f5399350006be4399350096bc4399350094ff729935000cfe7299350004fd729935000cfc729935001cfe7199350004fd71993502067e509935003e7c5099350024fc755935003ebf745935003ebf545935003ebc5459350004ff7359350014fe7359350014fc7359350006be4359350006bc4359350004ff725935000cfe7259350004fd725935000cfc7259350004ff715935001cfc7159350024fc7558f50004ff7458f50094fc7458f5003edf7358f5003edf5358f5003edc5358f50106dc4358f50004ff7258f5000cfe7258f50004fd7258f5000cfc7258f50004ff7158f5001cfc7158f50106df3058f5003d7f7654f500d67f7654f500d47f7654f500067e6454f5003f5f7354f500167e6354f500167c6354f501ae7e6254f5003e7c6254f500257e7054f500257c7054f50094ff76d0f5003cfe76d0f50004fd76d0f50016de63d0f50006dd63d0f50004ff7650f50004fd7650f5003cfc7650f50005fb7050f50025f87050f50024fc7558750004ff7458750094fc7458750004ff7358750014fe7358750014fc735875003e7f53587500067d5358750004ff7258750006ef7258750004ef725875000cfe7258750004fd725875000cfc7258750006ec725875000cec725875003ef7715875003ef7515875003ef4515875021e7e505875003e7c5058750094ff76d075003cfe76d0750004fd76d075001cff769075003cfe7690750004fd7690750004ff7650750004fd765075003cfc76507500057f755075003d7c7550750005ef72507500fdec725075001cff761075003cfe7610750004fd761075003d7e75107500057d751075001cff768c75003cfe768c750004fd768c750004ff764c750004fd764c75003cfc764c750005ef724c7500fdec724c750005fb704c750025f8704c750026be7499250014fe7399250004fd7399250014fc7399250094ff729925000cfe7299250004fd729925000cfc7299250096bf4299250006bd429925001cfe7199250004fd7199250024fe7099250026be4099250026bc4099250026bf7459250004ff7359250014fe7359250014fc7359250004ff725925000cfe7259250004fd725925000cfc7259250006bf4259250006bd4259250004ff715925001cfc7159250024fc7059250026be4059250026bc4059250096be6495250006bd649525003f3f5495250025fa7095250005f9709525003d7e74952502073e64952500067d64952502073d64952500063d64952500f57e73952500f57c73952500ed7e72952500ed7c72952502067f62952502ce7d62952500057d719525028e7e619
  | 21 => 0xf4319131126bd4319131094ff721913100cfe7219131004fd721913100cfc7219131024fe7019131004fd701913103cff76d5131004fe76d5131004fd76d513103cfc76d5131006bf64d5131006bc64d5131015de73d5131005dd73d51311eeec62d5131094ff7695131004fe7695131004fd7695131094fc76951310067f659513103e7c65951310073f54951311ceec6295131004ff7655131004fe7655131004fd7655131004fc76551311d6ec6255131094ff7615131004fe7615131004fd7615131094fc76151310067f651513103e7c6515131006bf6415131096bc64151311beec621513110dee76d893110eee76d893100cee76d8931006ef65d8931006ee65d8931006ed65d8931006ec65d8931006ef64d8931006ee64d8931006ed64d8931006ec64d89312d7cf73d893110fcc73d89312dfe731d89312d7ce31d89312d7cc31d89312dfe431d8931006ef75d8931006ee75d8931006ed75d8931006ec75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d8931006ee54d8931006ed54d8931006ec54d89312d6ef73d893110eee73d893110eed73d893110eec73d89312deef53d89312deee53d89312deed53d89312deec53d89312deef43d89312deee43d89312deed43d89312deec43d89312deef71d89312d6ee71d893110eed71d89312d6ec71d89312d6ee51d89312d6ec51d89312d6ee41d89312d6ec41d89312deef31d89312d6ee31d893110eed31d89312d6ec31d8931006ef70d8931006ee70d8931006ed70d8931006ec70d89312deef30d89312deee30d89312deed30d89312deec30d89312d6ef10d89312d6ec10d8931014fe76d4531014fc76d45310067f65d453103e7c65d4531015de73d4531005dd73d4531006ef62d453118eec62d453101f7651d453103cff7654531014fe7654531174fd7654531014fc76545310067f655453103e7c6554531005bf7454531005bc7454531005df7354531015dc7354531005ef725453110dec7254531006ef625453116eec625453101fd43154531014fe76d0531014fc76d0531006bf64d0531096bc64d0531015de73d0531005dd73d0531006ef62d053112eec62d0531094ff7650531014fe765053113cfd7650531014fc76505310057f75505310057c7550531006bf6450531006bc6450531005df7350531015dc7350531005ef725053110dec7250531006ef6250531136ec6250531006ef62d8131006ec62d813103cfe75d8131004fd75d8131094fe74d8131004fd74d813101cfd73d8131004ff72d813100cfe72d8131004fd72d813100cfc72d813106efa30d813110dee7298131005ed7298131006ef6298131006ec6298131006fb60981310057f75581310057c7558131005bf7458131005bc7458131005ef725813110dec7258131
  | 22 => 0x5231094ff769523101cfe7695231004fd769523101cfc769523128e7f659523103e7c6595231096be6495231006bd64952310073f5495231004ff765523101cfe7655231004fd765523101cfc765523103e7e65552310067d6555231006be6455231006bd6455231094ff761523101cfe7615231004fd761523101cfc76152312b67f651523103e7c6515231004ff755823103cfc7558231004ff7458231094fc7458231004ff725823100cfe7258231004fd725823100cfc725823101cfc715823101efb705823104efa3058231006fa2058231006f9205823101efb105823101ef8105823103cfe76d9531006ec62d9531094fe74d9531004fd74d953101cff73d953101cfd73d95311867f53d95311867d53d9531004ff72d953100cfe72d9531004fd72d953100cfc72d9531024fe70d9531004fd70d95310067f659953110dee7299531005ed7299531006ec6299531175f57199531005bf7459531005bc7459531005ef725953110dec7259531006ec6259531195f77159531005fb7059531005f870595310067f7559531004ff7459531006bf7459531004bf7459531094fc7459531006bc7459531004bc7459531174ff7359531006df7359531004ff7259531006ef7259531004ef725953100cfe7259531004fd725953100cfc7259531006ec725953100cec7259531194ff7159531006f77159531004ff7059531006fb7059531004fb7059531024fc7059531006f87059531024f87059531184fe761953103e7e65195310067d6519531006ec6219531006ec62d913103cfe75d9131004fd75d913101cff73d913101cfd73d913114ebf43d913114ebd43d9131004ff72d913100cfe72d9131004fd72d913100cfc72d9131024fe70d9131004fd70d9131006bf649913110dee7299131005ed7299131006ec629913113df5719913103cfe7599131004fd7599131094fe7499131154fd7399131096dd7399131094ff729913100cfe7299131096ee729913100cee7299131004fd7299131096ed7299131004ed729913100cfc729913113cfd7199131096f57199131024fe7099131004fd70991310057f75591310057c7559131005ef725913110dec7259131006ec6259131155f77159131005fb7059131005f87059131004ff75591310067f75591310047f755913103cfc75591310067c755913103c7c7559131006bf745913113cff7359131006df7359131004ff7259131006ef7259131004ef725913100cfe7259131004fd725913100cfc7259131006ec725913100cec7259131154ff7159131006f77159131004ff7059131006fb7059131004fb7059131024fc7059131006f87059131024f8705913114cfe7619131006bd6419131006ec621913103cfe7519131004fd7519131096be741913101cff731913101cfd7319131096b
  | 23 => 0x2fdbd76d504126ebd76d5041095be75d50412febf65d50412ff3e65d504126ebd65d50412ff3d65d50410063d65d50412febf62d5041306bd62d50412fdbf71d50412fdbd71d50412febe61d50412ffb661d50412ff3f51d50412ff3d51d5041004ff765504103e7e65550410067d65550410973c5455041095bd7615041096bd7615041004bd76150412fdbe75150410973e7515041096bf65150410973e651504126ebd65150410973d6515041096bf62150412f6bd621504126f3f52150412ef3d5215041095bf7115041097b671150412b5bd7115041097b57115041005b571150412b6be6115041097b661150412b73e51150412b73c5115041004ff7558c4103cfc7558c4101edf7358c41096df4358c41096dc4358c41004ff7258c4100cfe7258c41004fd7258c4100cfc7258c41126df3258c41006dd3258c4101cfc7158c4101ede3158c4101edc3158c41004ff7058c41024fc7058c41126df3058c4103cff76d4c4101cfe76d4c41004fd76d4c4103e7e65d4c410067d65d4c4126f3c54d4c411275e53d4c41004ff7654c41004fd7654c4101cfc7654c4103e7e6554c410067d6554c41005bf7454c41095bc7454c410073c5454c41154ff7650c410067e6550c410067d6550c4101df77650441006f77650441004f7765044100777755044100774755044101f76655044101f75655044101df7745044101fb77450441096f6645044101fb66450441097b65450441007b55450441007e772504412e7e472504412e7b64250441097b44250441004ff755804103cfc7558041004ff7358041014fe7358041014fc7358041004ff725804100cfe7258041004fd725804100cfc725804101efb7058041096fb4058041096f84058041006fa2058041006f9205804101efb105804101ef8105804101e7f7559631004ff7459631094fc74596311767f53596311767d5359631004ff725963100cfe7259631004fd725963100cfc72596310067f52596310067d525963101cfe715963101cfc715963101e7e515963101e7c5159631004ff7059631024fc705963103cfe7599231004fd759923101ebe7499231096bf4399231156bd4399231094ff729923100cfe7299231004fd729923100cfc7299231096bf4299231006bd429923101cfe719923101cfc719923101ebe419923101ebc4199231024fe7099231004fd7099231004ff75592310067f75592310047f755923103cfc75592310067c755923103c7c755923101ebf745923113ebf435923113ebd4359231004ff725923100cfe7259231004fd725923100cfc7259231006bf4259231006bd425923101cfe715923101cfc715923101ebe415923101ebc4159231004ff7059231024fc705923103cff76d523101cfe76d5231004fd76d523101cfc76d523103e7e65d52310067d65d
  | 24 => 0xe73d8141004fd73d8141014fc73d8141004ff72d814100cfe72d8141004fd72d814100cfc72d8141006fb30d8141006f830d81410057e75981410057d75981410067f65981410067c6598141135ee7298141005ed7298141006ef6298141006ec6298141006fb60981410057f75581410057c75581410067f65581410067c6558141005df735814113ddc7358141005ef7258141135ec7258141006ef6258141006ec62581410067f65181410067c6518141006ef6218141006ec6218141026fa6018141006f960181410967e74994410967c749944103e7f739944103e7e739944103e7d739944103e7c73994410967f43994410067e43994410967c439944103e7f729944103e7e729944103e7d729944103e7c72994410967f42994410067e42994410067d42994410967c42994410067f32994410067e32994410067d32994410067c329944101e7f719944101e7e719944101e7d719944101e7c719944101e7f419944101e7e419944101e7d419944101e7c419944101e7f319944101e7e319944101e7d319944101e7c319944101e7f219944101e7e219944101e7d219944101e7c219944103e7f709944103e7e709944103e7d709944103e7c70994410967f40994410967c40994410067f30994410067c30994410067f20994410067e20994410067d20994410067c209944101e7f109944101e7e109944101e7d109944101e7c109944101cff755944101e7f7559441094fe7459441094fc7459441006bc74594410967e54594410967c5459441004ff7359441014fe7359441014fc73594410067e53594410067c5359441004ff725944100cfe7259441004fd725944100cfc72594410067f52594410067e52594410067d52594410067c525944101cfe715944101cfc715944101e7e515944101e7c5159441004ff7059441024fc70594410967e74594410967c74594410063c74594410067f73594410067e73594410067d73594410067c73594410967f43594410067e43594410967c43594410067f72594410067e72594410067d72594410067c72594410967f42594410067e42594410067d42594410967c42594410067f32594410067e32594410067d32594410067c325944101e7f715944101e7e715944101e7d715944101e7c715944101e7f415944101e7e415944101e7d415944101e7c415944101e7f315944101e7e315944101e7d315944101e7c315944101e7f215944101e7e215944101e7d215944101e7c21594410067f70594410067e70594410067d70594410067c70594410967f40594410967c40594410067f30594410067c30594410067f20594410067e20594410067d20594410067c205944101e7f105944101e7e105944101e7d105944101e7c1059441004fd76d504103e7e65d50410067d65d50410973e54d5041
  | 25 => 0x514101cfc76551410067f655514103e7c65551411d6ec6255141005f7715514101df47155141004fe76151410067f651514103e7c65151411beec6215141014fe76d8d410067f65d8d410067c65d8d4113ede63d8d41006ec62d8d4103cfe75d8d41004fd75d8d4101cfd74d8d4113ede43d8d41004ff72d8d4100cfe72d8d41004fd72d8d4100cfc72d8d4113edf31d8d41024fe70d8d41004fd70d8d4113edc30d8d410057f7558d410057c7558d410067f6558d410067c6558d4113edc6358d41005ef7258d41135ec7258d41006ec6258d41005fb7058d41005f87058d41004fe76d4d41004fd76d4d4103cfc76d4d410067f65d4d4103e7c65d4d41005be74d4d41005bd74d4d4113f5e53d4d411b6ec62d4d41004ff7654d41004fe7654d41004fc7654d410067f6554d4103e7c6554d411aeec6254d4114cfe76d0d410067f65d0d410067c65d0d411a6ec62d0d4101cfc7650d410067f6550d410067c6550d41006df6350d41016dc6350d4113f9c4350d4119eec6250d41005f77150d4101df47150d41135ee76d8941136ee76d894100cee76d8941006ef65d89410076f65d89410066f65d8941006ee65d8941006ed65d8941006ec65d89410076c65d89410066c65d8941317af74d8941137ac74d8941006ef63d8941006ee63d8941006ed63d8941006ec63d8941317ae41d8941317ac41d8941006ef75d8941006ee75d8941006ed75d8941006ec75d8941316ef74d8941136ee74d8941136ed74d8941136ec74d8941006ef54d8941006ee54d8941006ed54d8941006ec54d8941006ef73d8941006ee73d8941006ed73d8941006ec73d8941006ef53d8941006ee53d8941006ed53d8941006ec53d8941006ef43d8941006ee43d8941006ed43d8941006ec43d8941006ef71d8941316ee71d8941136ed71d8941316ec71d8941316ee51d8941316ec51d8941316ee41d8941136ed41d8941316ec41d8941006ef31d8941316ee31d8941316ec31d8941006ef70d8941006ee70d8941006ed70d8941006ec70d8941006ef30d8941006ec30d8941316ef10d8941316ec10d8941004fe76d4541094fc76d45410067f65d454103e7c65d4541005be74d4541005bd74d4541006ef62d454118eec62d454101f7651d454103cff7654541004fd765454103cfc76545410067f655454103e7c6554541005bf7454541005bc7454541005ef7254541135ec7254541006ef625454116eec625454101fb441545410067f65d05410067c65d054101dbe74d054101ebf64d0541006ef62d054112eec62d05410077765d05410077465d054101df674d054101ef764d054101fb764d0541007e762d054130fe462d0541097b742d054130fb542d05410067f65d81410067c65d8141006ef62d8141006ec62d814103cfe75d8141004fd75d8141014f
  | 26 => 0x67d52d95410067c52d9541024fe70d9541004fd70d954103c7e76d95410067e63d95410067c63d95410067f62d95410067e62d95410067d62d95410067c62d95410076c62d95410066c62d95410073f42d95410073d42d954128f3e41d954128f3c41d954128e7f74d95410067d74d95410067f73d95410067e73d95410067d73d95410067c73d95410067e43d95410067c43d95410067f72d95410067e72d95410067d72d95410067c72d95410067f42d95410067e42d95410067d42d95410067c42d95410067f32d95410067e32d95410067d32d95410067c32d95410067f71d954128e7e71d95410067d71d954128e7c71d954128e7e41d954128e7c41d95410067f31d954128e7e31d954128e7c31d95410067f21d954128e7e21d95410067d21d954128e7c21d95410067f70d95410067e70d95410067d70d95410067c70d95410067f30d95410067c30d95410067f20d95410067e20d95410067d20d95410067c20d954128e7f10d954128e7c10d95410067f65995412febf6499541135ee7299541005ed7299541006ec6299541005ef7259541135ec7259541006ec62595410067f7559541004ff7459541006bf7459541004bf7459541004ff7359541014fe7359541014fc7359541004ff7259541006ef7259541004ef725954100cfe7259541004fd725954100cfc7259541006ec725954100cec7259541004ff7159541006f77159541004ff7059541024fc7059541004fe761954103e7e65195410067d65195412b6bf6419541006ec62195410057e76195410067e76195410047e76195410067e63195410067c63195410067f62195410067e62195410067d62195410067c62195410076c62195410066c62195410073f42195410073d42195412b73e41195412b73c411954103e7f741954103e7d741954103e7f731954103e7e731954103e7d731954103e7c73195410067e43195410067c431954103e7f721954103e7e721954103e7d721954103e7c72195410067f42195410063f42195410067e42195410067d42195410063d42195410067c42195410067f32195410067e32195410067d32195410067c321954103e7f711954103e7e711954103e7d711954103e7c71195412b67e41195412b63e41195410067d41195412b67c41195412b63c41195410067f31195412b67e31195412b67c31195410067f21195412b67e21195410067d21195412b67c211954103e7f701954103e7e701954103e7d701954103e7c70195410067f30195410067c30195410067f20195410067e20195410067d20195410067c20195412b67f10195412b67c101954101cfe76d514101cfc76d51410067f65d514103e7c65d51411eeec62d514101df671d5141005f571d5141004fe76951410067f659514103e7c65951410073f54951411ceec629
  | 27 => 0xc7654f410067f6554f4103e7c6554f41124ff7650f410979c4350f4103e7e65d47410067d65d4741095be74d4741005bd74d474103cff765474103e7e65547410067d6554741005bf7454741095bc7454741005ef725474112dec725474101fb64154741096fb6098341026f860983410057f75583410057c7558341096f86058341004ff75583410067f75583410047f755834103cfc75583410067c755834103c7c755834101cfc7458341004ff7358341014fe7358341014fc7358341004ff725834100cfe7258341004fd725834100cfc7258341096fb4058341096f8405834101e7f7559641006bf7459641004ff7359641014fe7359641014fc7359641004ff725964100cfe7259641004fd725964100cfc72596410067f52596410067d525964101cfc715964101e7e515964101e7c5159641004ff7059641024fc705964103e7e65d52410067d65d524101df671d5241005f571d52412fdbd76d5241276bd76d52412febf65d52412ff3e65d5241276bd65d52412ff3d65d52410063d65d52412febf62d524132ebd62d52412ffb671d52412fdbd71d5241277b571d5241005b571d52412ff3f51d52412ff3d51d524128e7f659524103e7c65952410073f549524103cff765524103e7e65552410067d6555241005f7715524101df471552412b67f651524103e7c65152410073d54152412b5bd7615241276bd76152412773e75152412b6bf65152412b73f6515241276bd65152412b73c65152412b6bf6215241326bd62152412773f521524131f3d52152412b5bf71152412b5bd71152412b73e51152412b73c5115241004ff7558e4103cfc7558e4101edf7358e4114ede5358e4114ede4358e41004ff7258e4100cfe7258e41004fd7258e4100cfc7258e4114edf3258e41006dd3258e4101cfc7158e4101ede3158e4101edc3158e41004ff7058e41024fc7058e4114edc3058e4103cff76d4e4101cfe76d4e41004fd76d4e4103e7e65d4e410067d65d4e412773c54d4e4114f5e53d4e41004ff7654e41004fd7654e4101cfc7654e4103e7e6554e410067d6554e41005bf7454e41005bc7454e410073c5454e41016de6354e41006dd6354e4113cfd76d0e41014ff7650e41016de6350e41006dd6350e41005f77150e4101df47150e4101df576d0641096f576d064101fb674d0641097b654d0641007b554d0641004ff755824103cfc7558241004ff7358241014fe7358241014fc7358241004ff725824100cfe7258241004fd725824100cfc725824101efb7058241006fa2058241006f9205824101efb105824101ef8105824103cfe76d9541006ec62d9541014fe73d9541004fd73d9541014fc73d95410067e53d95410067c53d9541004ff72d954100cfe72d9541004fd72d954100cfc72d95410067f52d95410067e52d9541
  | 28 => 0x8151026fa6018151006f9601815101cfe749905101ebe749905103ebf5499051096bc5499051014fe7399051004fd7399051014fc7399051006be4399051096bc4399051094ff729905100cfe7299051004fd729905100cfc7299051096bf4299051006bd429905101ebe419905101ebc4199051024fe7099051004fd709905101ebf745905103ebf545905103e7c545905103ebc5459051004ff7359051014fe7359051014fc7359051006be4359051006bc4359051004ff725905100cfe7259051004fd725905100cfc7259051006bf4259051006bd425905101e7f515905101e7d515905101ebe415905101ebc4159051004ff7059051024fc705905103d7d76950510067d76950510047d769505103d7e749505103f3e74950510067d649505103e7f62950513367d629505128d7d719505128e7e619505103f7661950512067e6095051004ff7458c51094fc7458c510067e5458c5103e7c5458c5101cff7358c5101edf7358c5103edf5358c5103edc5358c51166dc4358c51004ff7258c5100cfe7258c51004fd7258c5100cfc7258c51166df3258c51006dd3258c5101cfc7158c5101e7f5158c5101e7d5158c5101ede3158c5101edc3158c51004ff7058c51024fc7058c51166df3058c51094ff76d0c5101cfe76d0c51004fd76d0c51016de63d0c51006dd63d0c51004ff7650c51004fd7650c5101cfc7650c510057f7550c5103d7c7550c51004ff7458051094fc7458051004ff7358051014fe7358051014fc7358051004ff725805100cfe7258051004fd725805100cfc725805101efb705805103efb505805103ef85058051006fa2058051006f9205805101efb105805101ef81058051096be74d9741014fe73d9741004fd73d9741014fc73d9741094ff72d974100cfe72d9741096ee72d974100cee72d9741004fd72d9741096ed72d9741004ed72d974100cfc72d97410067f52d97410067d52d9741096f571d974128e7e51d974128e7c51d9741024fe70d9741004fd70d9741004fd76997410967f65997410967c65997412febe649974103cff76597410967c65597410967f755974101cfc74597410967e54597410967c5459741004ff7359741014fe7359741014fc7359741004ff725974100cfe7259741004fd725974100cfc7259741004ff7059741024fc70597410967f65d53410967c65d53410973e54d53410967f65553410967c6555341014ff7658f41096dc6358f41004ff7558f4103cfc7558f4101cfc7458f41096df4358f41096dc4358f41004ff7258f4100cfe7258f41004fd7258f4100cfc7258f41156df3158f41004ff7058f41024fc7058f4103cff76d4f41094fe76d4f41004fd76d4f410067f65d4f4103e7c65d4f41095be74d4f41005bd74d4f411575e53d4f41004ff7654f41004fd7654f41094f
  | 29 => 0x1b67c62d4d513576c62d4d511b66c62d4d5101d7e71d4d5101d7c71d4d5103e7f61d4d5103f7761d4d5121d7e70d4d5101cfc7654d51006bf6454d51006bc6454d51006df6354d51016dc6354d511aeec6254d51005f77154d5101df47154d5101d7c7654d510167c7654d5101c7c7654d510057f7454d510073f6454d510067c6454d510073c6454d510063c6454d5103d7f7354d5103f5f7354d510075f6354d510167e6354d510167c6354d511775c6354d5134d7f7254d5134d7d7254d511ae7e6254d511ae7c6254d5134f6c6254d511ae6c6254d51007777154d5101d7e7154d5101d7c7154d51007747154d5103e7f6154d5103f776154d5121d7c7054d51004fe76d0d51004fd76d0d51094fc76d0d5103d7e75d0d510057d75d0d51006bf64d0d51096bc64d0d511a6ec62d0d51004ff7650d51004fe7650d51004fc7650d5103d7e7550d510057d7550d51006bf6450d51006bc6450d5119eec6250d5116dee76d895116eee76d895100cee76d895133f6f75d895116f6c75d8951006ef64d8951007af64d8951006af64d8951006ee64d8951006ed64d8951006ec64d8951007ac64d8951006ac64d89510076f54d89510076d54d8951006ef63d8951006ee63d8951006ed63d8951006ec63d89510076f53d89510076d53d8951347e751d895133f6e51d895133f6c51d8951347e451d895133eef75d895116eee75d895116eed75d895116eec75d8951006ef74d8951006ee74d8951006ed74d8951006ec74d8951346ef54d8951006ee54d8951006ed54d8951346ec54d8951006ef73d8951006ee73d8951006ed73d8951006ec73d8951346ef53d8951006ee53d8951006ed53d8951346ec53d8951006ef43d8951006ee43d8951006ed43d8951006ec43d8951346ef71d895133eee71d895116eed71d895133eec71d8951346ef51d895133eee51d895116eed51d895133eec51d895133eee41d895133eec41d8951006ef31d895133eee31d895133eec31d8951006ef70d8951006ee70d8951006ed70d8951006ec70d8951346ef50d8951346ec50d8951006ef30d8951006ec30d895133eef10d895133eec10d8951006bf64d8151006bc64d8151006ef62d8151006ec62d8151094fe74d8151004fd74d8151014fe73d8151004fd73d8151014fc73d81510067f53d81510067d53d8151004ff72d815100cfe72d8151004fd72d815100cfc72d8151006fb30d8151006f830d8151005be7498151005bd7498151006bf6498151006bc649815116dee7298151005ed7298151006ef6298151006ec6298151006fb6098151005bf7458151005bc7458151006bf6458151006bc6458151005df7358151175dc7358151005ef725815116dec7258151006ef6258151006ec6258151006bf6418151006bc6418151006ef6218151006ec621
  | 30 => 0xf52191510067d5219151096bf4219151006be4219151006bd4219151096bc42191512b67e51191512b67c5119151024fe7019151004fd7019151005be7619151006be76191510073d7519151006be6319151006bc6319151006bf6219151006be6219151006bd6219151006bc6219151007ac6219151006ac62191510073f52191510073d521915126fb751191512b73e51191512b73c511915126fb45119151096bf751915126ebe7519151096bf7319151006be7319151006bd7319151096bc731915126ebf5319151006be531915126ebc5319151096bf7219151006be7219151006bd7219151096bc721915126ebf52191510063f5219151006be5219151006bd52191510063d521915126ebc5219151006bf3219151006be3219151006bd3219151006bc3219151096bf71191512b6be7119151006bd711915126ebf51191512b6be51191512b63e5119151006bd51191512b6bc51191512b63c5119151006bf31191512b6be31191512b6bc3119151006bf21191512b6be2119151006bd21191512b6bc2119151096bf7019151006be7019151006bd7019151096bc701915126ebf501915126ebc5019151006bf3019151006bc3019151006bf2019151006be2019151006bd2019151006bc20191512b6bf10191512b6bc10191510057e76d515103e7e76d51510047e76d51510073f64d51510967c64d51510073c64d51510063c64d51510057d73d515103d7f72d51513657d72d51513676c62d51513673f42d51513673d42d515101d7e71d515101d7c71d515103e7f61d515103f7761d515121d7e70d515101cfe769515135d7d7595151006bf6495151096bc649515103f3f54951511ceec629515101df67195151005f5719515101cfc7655151006bf6455151006bc64551511d6ec6255151005f7715515101df4715515101c7c765515103d7f745515103f3f74551510073f64551510967c64551510073c64551510063c64551510057f735515135d7f725515135d7d725515135f6c625515100777715515101d7e715515101d7c715515100774715515103e7f615515103f77615515121d7c7055151014fe76d8d51006bf64d8d51006bc64d8d51176de63d8d51006ec62d8d5101cfd75d8d51094fe74d8d51004fd74d8d51176de53d8d51004ff72d8d5100cfe72d8d51004fd72d8d5100cfc72d8d5103cfd71d8d51176df31d8d51024fe70d8d51004fd70d8d51176dc30d8d51005bf7458d51005bc7458d51006bf6458d51006bc6458d51176dc6358d51005ef7258d5116dec7258d51006ec6258d51005fb7058d51005f87058d510057e76d4d5103e7e76d4d510057d74d4d510073f64d4d510067c64d4d510073c64d4d510063c64d4d511757d73d4d510167e63d4d510167c63d4d5103d7f72d4d513557d72d4d511b67e62d4d51
  | 31 => 0x525128d7d719525100775719525100575719525103e7e61952512067e6095251006be6455251006bd645525103f3c5455251005f7715525101df4715525103f7751552512b57d761525103e7d761525103f3e74152512b73f64152510067d64152512b73c64152512b67f62152513767d621525136f3f421525136f3d421525103d7f71152512b57d711525103f7661152511fe7e6015251004ff7458e51094fc7458e510067e5458e510067c5458e5101edf7358e51186de5358e51004ff7258e5100cfe7258e51004fd7258e5100cfc7258e51186df3258e51006dd3258e5101cfc7158e5101e7f5158e5101e7d5158e5101ede3158e5101edc3158e51004ff7058e51024fc7058e51014ff7654e51016de6354e51006dd6354e51005f77154e5101df47154e5103f775154e51094ff76d0e5101cfe76d0e51004fd76d0e51004ff7650e51004fd7650e5101cfc7650e510057f7550e5103d7c7550e51004ff7458251094fc7458251004ff7358251014fe7358251014fc7358251004ff725825100cfe7258251004fd725825100cfc725825101cfc715825101efb7058251006fa2058251006f9205825101efb105825101ef81058251006ec62d9151014fe73d9151004fd73d9151014fc73d9151006be43d9151006bc43d9151004ff72d915100cfe72d9151004fd72d915100cfc72d9151006bf42d9151006be42d9151006bd42d9151006bc42d9151024fe70d9151004fd70d91512ff3f75d9151006be63d9151006bc63d9151006bf62d9151006be62d9151006bd62d9151006bc62d9151007ac62d9151006ac62d91510073f52d91510073d52d9151277b751d91512ff3e51d91512ff3c51d9151277b451d91512febf75d9151276be75d9151006bf73d9151006be73d9151006bd73d9151006bc73d9151276bf53d9151006be53d9151276bc53d9151006bf72d9151006be72d9151006bd72d9151006bc72d9151276bf52d9151006be52d9151006bd52d9151276bc52d9151006bf32d9151006be32d9151006bd32d9151006bc32d9151276bf71d91512febe71d9151006bd71d9151276bf51d91512febe51d91512febc51d9151006bf31d91512febe31d91512febc31d9151006bf21d91512febe21d9151006bd21d91512febc21d9151006bf70d9151006be70d9151006bd70d9151006bc70d9151276bf50d9151276bc50d9151006bf30d9151006bc30d9151006bf20d9151006be20d9151006bd20d9151006bc20d91512febf10d91512febc10d9151006bf649915116dee7299151005ed7299151006ec6299151005ef725915116dec7259151006ec6259151006bd6419151006ec6219151014fe7319151004fd7319151014fc7319151006be4319151096bc4319151094ff721915100cfe7219151004fd721915100cfc72191510067
  | 32 => 0x5fb7058543005f870585430057e75185430057d751854301ef66118543006f5611854303cfe75d8143004fd75d8143004ff72d814300cfe72d8143004fd72d814300cfc72d814301cfe71d8143004fd71d81430c6fa30d8143006fa20d8143006f920d814324ebf6498143006fb60981430057f75581430057c755814324ebf6418143246df631814319dee7218143005ed7218143026fa6018143006f9601814301cfe759935101c7e7599351096be74993510967f549935103ebf549935103e3f5499351096bc5499351014fe7399351004fd7399351014fc739935103e7f5399351094ff729935100cfe7299351004fd729935100cfc729935103e7f52993510067d529935128e7e519935103e7c5199351024fe7099351004fd709935103e7c509935101cfc755935103ebf745935103ebf545935103ebc5459351004ff7359351014fe7359351014fc7359351004ff725935100cfe7259351004fd725935100cfc7259351004ff7059351024fc705935103d7f76553510067f765535103f3f74553510967e64553510057f735535138d7f725535138d7d725535101d7e715535101d7c71553512357c705535101cfc7558f51004ff7458f51094fc7458f5103edf7358f5103edf5358f5103edc5358f51004ff7258f5100cfe7258f51004fd7258f5100cfc7258f51196df3158f51004ff7058f51024fc7058f5103d7f7654f511667f7654f510057f7454f510067e6454f5103f5f7354f510167e6354f510167c6354f513857f7254f513857d7254f511ae7e6254f5103e7c6254f5101d7e7154f5101d7c7154f512357c7054f51094ff76d0f5103cfe76d0f51004fd76d0f5103d7e75d0f510057d75d0f51004ff7650f51004fd7650f5103cfc7650f5103d7e7550f510057d7550f5101cfc755835101c7c7558351004ff7458351094fc7458351004ff7358351014fe7358351014fc735835103e7f53583510067d5358351004ff725835100cfe7258351004fd725835100cfc725835103efb705835103efb505835103e7c505835103ef8505835101ebe7499251014fe7399251004fd7399251014fc7399251094ff729925100cfe7299251004fd729925100cfc7299251096bf4299251006bd429925101cfe719925101ebe419925101ebc4199251024fe7099251004fd709925101ebf7459251004ff7359251014fe7359251014fc7359251004ff725925100cfe7259251004fd725925100cfc7259251006bf4259251006bd425925101cfc715925101e7f515925101e7d515925101ebe415925101ebc4159251004ff7059251024fc7059251096be6495251006bd649525103f3f549525101df67195251005f5719525103d7e749525128f3e64952510067d649525128f3d64952510063d649525128e7f629525137e7d629525128f76719
  | 33 => 0x66118553006f56118553094fe74d8153004fd74d815303cfd73d8153004ff72d815300cfe72d8153004fd72d815300cfc72d815301cfe71d8153004fd71d8153106fa30d8153006fa20d8153006f920d815325e7f6598153006fb6098153005bf7458153005bc745815325e7f65181531adee7218153005ed7218153026fa6018153006f96018153094fe74d9743096be74d9743096dd73d9743094ff72d974300cfe72d9743004fd72d974300cfc72d974301cfe71d9743004fd71d9743024fe70d9743004fd70d97431dcfd76997430967f65997430967c659974303cff76597430967c65597430967f7559743014fe7459743014fc74597430967e54597430967c54597431de7f53597431de7d5359743004ff725974300cfe7259743004fd725974300cfc7259743004ff715974301cfc7159743004ff7059743024fc70597431dcfd76d53430973e54d53431f4ff76553431df9e4355343096f7619874301ef46198743096f46158743004ff755874303cfc7558743014fc7458743004ff725874300cfe7258743004fd725874300cfc7258743096f74158743096f4415874313ef63158743004ff7058743024fc705874323ebe6498343096fb6098343026f86098343096f86058343004ff755834303cfc7558343014fc7458343004ff725834300cfe7258343004fd725834300cfc7258343004ff715834301cfc7158343096fb4058343096f840583430aefa3058343246dc305834303cfe76d9543094ff73d95431e4fd73d95431e67f53d95431e67d53d9543004ff72d954300cfe72d9543004fd72d954300cfc72d95430067f52d95430067d52d954301cfe71d9543004fd71d9543024fe70d9543004fd70d95430067f65995431ddbd74995431f5bf7459543005fb7059543005f870595430067f75595431f4ff7459543006bf74595431dcff7359543006df7359543004ff725954300cfe7259543004fd725954300cfc7259543004ff715954301cfc7159543004ff7059543006fb7059543004fb7059543024fc7059543006f87059543024f870595431e4fe761954303e7e65195430067d6519543014fe76d5143014fc76d51430067f65d514303e7c65d5143015de73d5143005dd73d51431c4fe769514303e7e65951430067d65951430073f54951430979c439514303cff7655143014fe76551431dcfd7655143014fc76551430067f655514303e7c6555143005df7355143015dc73551431df9c43551431e4fe761514303e7e65151430067d6515143015de74d0d430179e74d0d43016df64d0d430179f64d0d4303cfe75d8543004fd75d8543004ff72d854300cfe72d8543004fd72d854300cfc72d8543156f631d8543024fe70d8543004fd70d8543006f761985430057f75585430057c7558543005ef725854319dec7258543
  | 34 => 0x935303ebf5499353096bc5499353096bf43993531e6bd4399353094ff729935300cfe7299353004fd729935300cfc729935301cfe7199353004fd7199353024fe7099353004fd7099353014fc755935303e7c75593530147c755935303ebf745935303ebf545935303e7c545935303ebc545935303e3c54593531debf4359353004ff725935300cfe7259353004fd725935300cfc7259353004ff715935301cfc715935303e7f5159353004ff7059353024fc705935303d7d76953530067d769535303f3e74953530067d64953530157e73953530157c73953531b57e72953531b57c729535303e7f62953533ae7d62953530057d719535328e7e61953530057d70953532067e6095353014fc7558753004ff7458753094fc7458753004ff725875300cfe7258753004fd725875300cfc725875303ef7715875303ef7515875303ef45158753176f63158753004ff7058753024fc7058753014fc7558353004ff7458353094fc7458353004ff725835300cfe7258353004fd725835300cfc7258353004ff715835301cfc715835303efb705835303efb505835303ef850583530e6fa30583531f67d75d915303cfd73d91531f6bf43d9153004ff72d915300cfe72d9153004fd72d915300cfc72d9153006bf42d9153006bd42d915301cfe71d9153004fd71d9153024fe70d9153004fd70d9153006bf6499153005fb7059153005f87059153006bd6419153094ff731915303cfd7319153096bf43191531c6bd4319153094ff721915300cfe7219153004fd721915300cfc7219153096bf4219153006bd421915301cfe7119153004fd7119153024fe7019153004fd7019153014fe7695153006bf6495153096bc649515303f3f5495153015de7395153005dd73951530157e76951531e67e76951530147e769515303d7e74951530067f64951530073f64951530063f64951530073c64951530157e73951531e75e73951530075d73951530157c739515303e7f639515303f5f63951531ad7e72951531ad7c72951533a67f62951533a67d62951530057d719515328e7c61951530057d70951532067c6095153014fc7655153006bf6455153006bc6455153005df7355153015dc73551531f57e761515303e7e76151531e57e741515303f3e74151530067f64151530157e73151530157c731515303e7f631515303f5f63151531ad7e721515303d7c721515339e7f621515339e7d62151533973f42151533973d42151530057d71151532b67c61151530057d70151531fe7c6015153094fe74d8553004fd74d855303cfd73d8553004ff72d855300cfe72d8553004fd72d855300cfc72d8553196f631d8553024fe70d8553004fd70d8553006f76198553005bf7458553005bc7458553005ef72585531adec7258553005fb7058553005f8705855301ef
  | 35 => 0x67f5458654004ff7358654014fe7358654014fc7358654004ff725865400cfe7258654004fd725865400cfc72586540067f52586540067d5258654096f74158654096f44158654004ff7058654024fc70586540073f5498254096fb6098254026f860982540073f5458254096f86058254094fc7458254004ff7358254014fe7358254014fc7358254004ff725825400cfe7258254004fd725825400cfc7258254004ff715825401cfc7158254096fb4058254096f8405825403dbe749515403ebf64951540957e74951540967f649515403f3f649515403e3f64951543c67f62951543c67d62951540057d7195154014fe76d8d541dede63d8d5403cfd74d8d540067e54d8d541dede53d8d541dede43d8d54004ff72d8d5400cfe72d8d54004fd72d8d5400cfc72d8d5401cfe71d8d54004fd71d8d54024fe70d8d54004fd70d8d541dedc30d8d541dedc6358d54005fb7058d54005f87058d54014fe73d8554004fd73d8554014fc73d8554004ff72d855400cfe72d8554004fd72d855400cfc72d8554006f721d8554006f421d8554024fe70d8554004fd70d8554006f76198554005ef72585541d5ec725855428e7f65185542febf641855401ef66118554006f56118554014fe73d8154004fd73d8154014fc73d8154004ff72d815400cfe72d8154004fd72d815400cfc72d815401cfe71d8154004fd71d8154006fb30d8154006f830d8154006fb6098154005df73581541dddc73581542067f65181541d5ee7218154005ed7218154026fa6018154006f960181540957f76550540067f76550540047f76550540957f745505403f3f74550540967e64550540973e64550540057f73550543bf3e43550540973c43550543b57f72550543b57d72550540973f42550543b73d42550542b57c71550541fd7c7055054096df7358c5403edf5358c5403edc5358c54096df4358c54096dc4358c54004ff7258c5400cfe7258c54004fd7258c5400cfc7258c54004ff7158c5401cfc7158c54004ff7058c54024fc7058c541c6df3058c5403e7f54584540067d5458454004ff7358454014fe7358454014fc735845403e7f5358454004ff7258454006ef7258454004ef725845400cfe7258454004fd725845400cfc7258454006ec725845400cec725845403e7f52584540067d5258454006bf4258454006bd4258454096f7715845403ef7515845403e7c515845403ef45158454096f74158454096f44158454004ff7058454024fc705845403e7c5058454004ff7358054014fe7358054014fc735805403e7f5358054004ff725805400cfe7258054004fd725805400cfc7258054004ff715805401cfc7158054096fb705805403efb505805403e7c505805403ef85058054096fb4058054096f84058054014fe7599353014fc7599353096be749
  | 36 => 0x2182820404102081002c24000030e4c0830014b0122042850415a8b003400d10080030a8402d182018e127800010000220e05a8a000c0000008006040c01d0094210082c0010e28a0f0804380083c51c0e0029a000c3140a00000030cd8404202030a140020024080121420000000a9086049a0e00681020c1030a141090a04b25001080104081820400000020800504000000e0eb820018905061c20302741010a00107a400180000c00444041050008006040410b023030e0000180000428120880031424002260028b0a08000005c4000604000000000106486832028092021c19606182820200001140c180004c10200043000c00013024c29700040060008005000c0003418c870260c8016000010640884020150003e7c5458f5403edf7358f5403edf5358f5403edc5358f541f6de4358f54004ff7258f5400cfe7258f54004fd7258f5400cfc7258f54004ff7158f5401cfc7158f5403e7f5158f541f6df3158f54004ff7058f54024fc7058f541f6dc3058f54004ff7358754014fe7358754014fc7358754004ff725875400cfe7258754004fd725875400cfc7258754006bf4258754006bd425875403ef7715875403ef7515875403ef45158754004ff7058754024fc7058754004ff7358354014fe7358354014fc7358354004ff725835400cfe7258354004fd725835400cfc7258354004ff715835401cfc715835403efb705835403efb505835403ef850583540957d76d525403e7d76d52540973e64d52540057d73d52543d73e43d52540973c43d525403d7f72d52543cd7d72d52540973f42d52543cf3e42d52543cf3d42d52540973c42d525428d7e71d52542057e70d525403f3d76d52540053d76d525403e3d76d525403f3f73d525403f3e73d525403f3d73d525403f3c73d52540973f63d52543d73e63d52540973c63d525403f3f72d525403f3e72d525403f3d72d525403f3c72d52540973f62d52543cf3e62d52543cf3d62d52540973c62d52543cf3f32d52543cf3e32d52543cf3d32d52543cf3c32d525403f3f71d525403f3e71d525403f3d71d525403f3c71d52540973f61d52540973c61d52543d73f31d52543d73c31d52543cf3f21d52543cf3e21d52543cf3d21d52543cf3c21d525403f3f70d525403f3e70d525403f3d70d525403f3c70d52540973f60d52540973c60d52543d73f30d52543d73c30d52543cf3f20d52543cf3e20d52543cf3d20d52543cf3c20d5254014ff7658e540073f5458e54096dc6358e54094fc7458e541e6de5358e54096df4358e54096dc4358e54004ff7258e5400cfe7258e54004fd7258e5400cfc7258e54004ff7158e5401cfc7158e54004ff7058e54024fc7058e542b6be64986540073f5498654096f7619865401ef461986540073f5458654096f46158654094fc7458654
  | 37 => 0x81841a1c000060c001001430200180172c1410c0e08108721438c080440208000823a101050a0c59f200418e00001011a1000e4004282024c102383000110781822604182002c5010004000000000f002c286040010622008844654081023800000100000604082040060d0000003140d9801000381000918004fc583142800b202810800140050c00302020c282400408600001000000082061040228000a2121819b0208105040c5000c2530604002860e00900084c201020071c021c300024c2820e0038100001030032302021c0050c00a050e000004001b85000828200040810a005000000104264c00202645862604302000808816040820c006810608100004050504000021e002850019302052c4051c0408e040000500282834a0010e26006820410100080420410001892a88e8400040020000007260060b0e102000028200040c220029c780121478e040c00404006030a88000000c000001420500082000000101007c180082418f001000d0000110003c000000018110009001c04594003ce8000701080c0001304000020200708127438008241830000583000008304000000a00501060450c10101020409407081818d0a081020a001940a043070810000197c000043000f020c285005c0000014107000c28004004850c3c201001800c1828107027c08d220048108100023e001000000004000018100040010400100042878d00040800218b8000482040000600020000e0a3c0010210603000001720001830004005024888004e00091e10100003808302b418700004800e240811600815040418946100830054387164c0040211580061858014042950e0c0801a642040414001020c180020070300201013e20002080410148041000e0890516007138c0000200ac304020c08200005020078100321c280001d18006205963e009870600100060849b083408002000800a0120f0a3418008040860c405800000001182c0001c240040a14102024c40200002aa0a1c0101234c800610080081c086281c003003010a200c00002144020224200021c2853224002020038a0008e0a0c00d010234007083020906008050250203061020b001800b0014680160460006083803e00384000008b120480000000010c180880228589120408400e8080009c00b02240020000200060c58b165c481001000002440310e042800e281060210584042c004120418f08341060e0808008041010c001800a100853e140050830086220400204640020000006000010c2e74b8a30101860e150b9360c0030204f00020c4020804000020c012021070d12980000210100001030f0018313001030302382800e0cca7060030c0418028002810004681831224386264488002008870c0c1000054188001c50704182820038480000449346781831c00080
  | 38 => 0xc600000001338000137c0000000000000000015674600c793c900005dd800000002710000e744a54000000030d51900000001090456400050cc00050dc1b92ecd0bb00000005fb000047a45f40000249000090732c86e945d0000000136b00000001b440003ed8000533cf8200000000000a5500011f9000000012f5210311800021d800000000003b0d5e9571919340c56265444f511334bb75300c3a4be94b257b4a1a270d7b510185ca26d8df04a04df42c8c0002cfc3e22694de73fc119b530c03902ac671001cd7a229c6a260f18053ff0bf320357c008a067f4494c3916e17473f7d22f420033407c091417dcbaf1bf00000000e685968add4f102624e10a4f23ac0d74a14a2732d47f20f3d24153ccbdc4cb0a8c080ca96000045600000dc20789550b50e78523400029f40005dc8000569984e0ea14843474000048900b4a9507514301262af062451694782d2400057393cf1ef80001c94a360a6c0003ef0bec39457a937fc000519800000015b34064d00330855d1fd51de18d81e852d061e22191164b001782c640000000ddf000087e3928cfd218c79f000181d00000002b38bc8021048b24ad0230000642000002e0680d67000173316f0ffe00005e95174000000000000007ca00000002858ac20000000000000009a406d04fc5fa02f4b6431500004278d790e04000240400003042490e1a001040e10200000428200740003a0ce81020410a0a24ab200201043a00802000c02c001800124080991208080022402d1a18508229c0010e14680000018f000468206100020040002028810022540000204401280c381140008300002000000000084408204040000814201180011422142821e140103214004002c08008048870808098120438c080c0801c2812a0000001061c2800618102080c2070808280020c0010254a011204101121d0070018003003038404180020a24402042400002001151e3c002040028408000000404686120420a0e540140054003060408078000000830581003c78100080820600214081008f003c4900e04000020001e187c4830618d0f02c40040000184241c2830404000143418100000861a0000010141b802401101210707101430b160488b100008002000800228004180800904081800490782000c085020c211121020f100000200240800c0078902000001200008043808400000831450101105848712001830e4ca86002930300000071800004067c00d120010e0008405040431a0808015042410000340022619c0700040990830505041c19f080c0810248200020800300103af200828400045001a4408808041811698b840004e94024c1122800311060c0801810602000018006341864c040832e380000000308001c2110000000003058100584800818107224c2010e281832804307026
  | 39 => 0x7300000ab318c0aa61b7817b4e341b22e34be74cd06d236380000894fbe2630f9c2e9958b44c50fb5de0000609c14f2f4c5ad0000000305000015580001e496e65180a2f23b86a9212c5516170adb1c98fa00c6545608ac4ba27b881a38d118908b51a542105835b515b133113ba2d28000299c00013d0925000071200001f23300000554400045200004f2c0000000000000000052f42ec00000000001342066486a51053cd4dbc0994b894753d711f652890db27a93fc000147607e859e00007d44ffc00010f002025997122991190475d505047cb20332496717308e429d80000cbd540000129f5905563349900a3578ac62680c6701b051108a481201d40a41aad19f00016a520a4c090cb4d1600009ed484c03b19107083ae050e411847c21cc2875a5098d000098109c03c010dc9e45ef80000000bf929d40911080000000000000011a15f484fa0000bc028ccc7518753282114f2300000000000c3d3f6c0bc3180cf74a08b090b14e04000000005ad50000010f800000005540f0b4fad39b17a00000000b2c0b4c2450478986455c6f038a02cb0e014700fcd01432940000570000000122d000130a0000cbe26c074f1c3800053c44ab0d951055909659151d1c1498c3a541a00005c4163319dd70b17e070d0000000122400000016d6066953e4524a4e00017b10308b2836cd44d000000059e97bf000151a00010590000580000000000000005f7000022f07745284c5b0acc00123113df398067d44f138a52e4443281c1684f489f5417125e49250560bf4d7d56200d904153bb320d643567d4fa000038b434d50e00014ac54b4d69224d47914d88172ea8958211865f30f0dfa50491fc5fe49363d3028135cd03c2aa983959580004eac00002300e73a183a92f509760fc4d0d168c51e00000003bcc4ef02dd7ae14fc4380d7cfdc2aa181b2bd457536fc0002600bcc1e441a107406cb5390b1f5a24000420877a038000023140003e4c5a70a88ed943897f42488000000000037a15240f98885000000011bc0000000f8639040001b3457d00c11585e5414b3d8d7de34ec0c31328000535545500000000000dba0000000000000500013b92a690ac0ec400a21b119d4cec56c4ca4be4220466d10540214d14b4b4dd8c1a095d1325688f56000184f00011ed5960e5205600000a50fac15f0acd00013ed4fe4b6a000054f000000000002aa5aa979726541cf23a49382c98a523d744d008d10d03670a481a4c00035243fa0000f7200015f507fc78e344cf6d28301ea000000000013ae576000000000000000000044cb325ae800055649d820740000001280469c000519c000338158149f89b8159c0004ae84e117c8266000000055618240000cf9000000030484aa44fc80430bc0002a513673ed4000000000047a821156a530500000002
  | 40 => 0x8243f52cb4c642b907d8453ccdc000000000000005b240004f4416f0000eb7156cd1403b57fc00017a313c40002cad6093b8822f000000042ac00021c49930d697351498d8d4d283eb1c683681d8c49b5c901962518cca34dc43a22681eb38593c90000a1335a152300013250e4c27b3c1c000000000043a11015854000408000000009d000000003a806f25da163a0000cb049c1469614823c103446100012b72c9400037608af0e745162c2c5cf4d1cf402f6949e35f12c300f8f9e505834a000015d5f5c5e13ab4a7300008ef076000000011a64f740002e80000214c59744f400030b89484b953c000015b25f5830636a00002c58a795775065000821e4b1c7fb1efc00054f46cc608122c4ef00003df4957508128433b44360000e914214a723da0e653ce940b00017802be96381f7c93d2d05151570ccce16a85f944dc17623ec840020816056a94fc29609944f4181242184ee3cb000051c570460581cc2d94b8c28b002c4224dbe45b139409c853b00005ba5c692710000db14db12763b784fe5e3d09b4730aea4bf809748758760584e372210d9915253320a452192d586d31b614f0310c94d172446733305d8002573123086ac24812df5e584b917ad67000007470a4067a00001151264ad6000067c0000d6f3fece492ff12d44c44f08088856933990c93159651000092a430105400003b02665874000000025a8c580174c3600000005d0040015dd672267d247000168d296cae2275000013dc50a607cecc000000000009f30000000000111a00002e80000bc400000452f241a841f970e3f6527340ac7904d791e430ed6b21ccd14b1440d4759945c0003529e57fc342194c5e3428c14906b446911f8159099c05b00000001fc0fd4000000000000000000bdf54300005420000000158e01c00000000cd41f840002cd4000381800016687a815f89512f85620182ccd53fdcbb13f850ad0d7476736f04b0362012e5ca131b288542e2dd0c7736b433008e567e000107a4af8000045921a0fb97c55c504c32055657576964e5329143061c3a21f989f849f400036843f70000f28441cc6d380000000000005cb000056e00002704c8e150447228d42b55c34d0e01907046178000000154a2fbc81633a93f700000004de40000dcce43000000019cc0005bb000000012f450c00d2000119a1bdc000142d22407154cc232c6f13dbc3d9242ca6317050f226f8c4804656a62bf517b2a9064b3e0c0a15f451fb039111b0000fc93a4182505c8144605400023410701e04d240f244b50000000309c0002b509ff3e04aa23f155325a9c0ca55814b00f310621d5476536945090cf50da353421b00012991bd125d3d6056324797d50f182424b70c1b2754eb645d96a9000000005c06e75378dc411487b20001546000143900013bd0b44000154c
  | 41 => 0x8ae636b80a30000bd6176d20f264858400015bb00003a700006880000e930000f8e00008200000b5f3de42d549c80e1000024e000110d1e306950000ce400000000000d075c7843d4fd0ebe48e8d0a31cd57f00000005e0433e35d8ae80e70d7e4418b5200009cf53255f3314d41f2d400001db00f3000015f00009ce5ca8000453479700017175ce8686586c8dd32f0a3f31c474055b53b417888b706fd2371d0c5e652484900f848f13eed61c246088c42c00002e6903630dc5330c716f51eec0c50ad12574848edb0cb018b57b8a4a1628aa542d90790dc4df70db4d0916a440715315472d017c205913980000000615c0002dc00000944000067c00009f48fa24e800009300000694efe10c8066101134e0ee91d040082804a2078a4b3d6dd000071818653f35b94185463c7214c240005e8400032ac0002134a1f0228d444f994a800010934c5000028612072904ba33b98bed1b392a00f802b12a2400043dd41a4e780000000000000000000008df279400004012a200017af000000007742023610000000000000000005b34000000000032cc5b54a9d1af0000000326c000000000048058140000b020d5102129015f701180004a6c00000014b70000000111183e1bb558648d43ad59ad8711f7400000017c100007800ef878630a8e792c4100e112c000495800000004de3794fdd195cdb04aa0aaf2220c083d0c9110c113402190d821b950384bc0f1254e8b0d4de955732b8135300171821a578c2ab46c6259464a53883490f4d16260b84a35018910273551c60ec00000005be1f394fe2e8506e000000039757071e6ced60000000542541b0000f000e611210f581f80c7511c06f94ed25295de3aa8dc91138bc10410d2a12d13b600002ac3d09387000c1ba339c00029f94ec544079c5edc0005fe03851568a0d000000000002a305d4061000075618e17c33c2400000000003f587c803e0000000187b5dd012c26d40cb000004400000001d3565f3dd000033401890d0c31f0000ed200006a7553c95c4dd009a20a044a3fc91032e38e501e7492856d4df931ac0001580f034cb40002db574d210d6fe00014f5597983f4dfd07208986b84ae07713f011e60974a7f1fb81922e6c000000062749348be46a07af5f2c0001eac65b000174305400f709516271cf879538f828442dc00020e45de15c49b200002cf188831a03241460000e2e000109d4504000000120c0000ea6000000053fc000380d6442c3929a2148c74552c000000175211f40140f100004e5cd080000f4f30900004fc51c3000070000000005bcc7eb49bc1c817c514e58a43d0000000024b540c4070bab28e506f32683270261678104923d5be130f0cad81309190a74a306cf00009e70000d8520f1136500945f46b055061e8dc75034b800000000494d02631281a4
  | 42 => 0xf33ccee855396121cf520d0000b4e216c0005460a5603a126b00002c3581400000000004bec9de5c94da4288c06b2bc551d04b4a0f45cc9612d617444061822465529c127ced85cc14181480e27128800008b144e17b017423795e21e211fe5fc541d2660000000000014e503e13b00000d98000000068d0000802402551647446be448c00051c800025890064abcf300e296c0617ce1c59840003dccabf3e3c5313d04000000033c335c0003d780005ce100c00017cf0000000257454a260818447fc0fd000075f000066b3b5400047b000058b872704ec01a56dca6e1840b9161b8000577033b4acc2d600003a60000000285c38f0000000000180d0000000000127f000002a1b8400020f858e42c80000000edf28f062a00000002548c50100d37000000001ba837f1a596241eb000020d045e38f040a3c190322c483e900e8bf75ef15e500000000f091975e3902d5fd53d755b87061e6438213ec5421f44ad145dcf36334c13a0df03d20568f8933a063b20c06404c6891a21f56ce46505875ae400000008f500002ca2fa54035afc0003e8c68707641c349a40001edd1d423c91f11ed459500009c70018000000000000008bb31a880710cc0000001152000030c498873b00011985dcc0000000e7719bc00000016620270000579cc13000069c61400000c606ef1e248b9230d2ee5ef40005af14f852906c83bfd83d0ae10ea4c9c00048a000003694db195552052257225e188f80064f9b1f2d544000000031a002d3edc000369c9eb0514b0c120c000000142104a4b7158acf0d4930a0b4f685fe45c92d94550369020c00037bc5c8227c0001920d295dc0c620b380005c3d27c12580000b00477519508855dc21f1dcc3ea000116835d020b60c81711a64000000169c00002cc2874000000000000000000001120249c0001a8c0000000feb41fc6e20001039308cafc2ce45214cdc68f0d4c51d00d800000015cc51ec8951ee56b55a600695b1085a3f902b029880001c2d4b514205964df51f34fb95800000e762864317569001527c84084f8108a0abc75113146da27a12ae549c7e00a54d9438d953c35b03fc13f120230e074647c0d92453075a5de96e15e984b637283f947d0e1b0001459439000000000005e4ce593344e4c00001104e956be327168a454c41c183073a53b8000193893312b41f3613485802c90af077187219600000000e1100002e4103d03000014f600000005c456a30000b460000000000124005880002fb891741e04475e70b2e570084400005bf45bc00028b40001dc91d31bd885558283792e1cbcf42a4a80545000054a8000438400040940004ec00002638f0430440003ee169a50ac00000018194724000000000000003df5fc800032297e62324000193ce5536b01775e3400033140002d88545427124b559
  | 43 => 0x94de20164f660b7c683049c0004f1c0000e306845e482a7314800053a573c19680004980a2a000000018f489d23893444c202e94d604400000bd04f384b129ec000000022321bcff90000cc81914759230450700003572200000000000000012c82cbcb1418453a61cb000008eca775ce5004000025a00018384d403b656340000000e9d000042d2dac63e5df86b707b80ac41315eb10b8214274d4000000e625ca4b3c00016194a4d3ac616000007181fe000096d2e0c0002318000000000003396ae56d17452f7489b000029d0274c9e45f000000000002a7166619d07310000000251cc9803a800026a0da3314436f234c0000a391a30afd8493c14f370c487f9302c2a00fa007921c139d0a30faa48c0000000069e38ccf3e2ab8de30de80000000d972ad0a9b3e903c129b4a316154e5301302db34655c41f7916313f46df5c303860d913c303957c93318092468863c25b94d340a86151c4d33f3e300001ff062358bcf6e2ffc0005a4c000146c00000018655078000525456e0594000069c8b34a38fb23a84be3571d1b6064410158597a237e06c124fd821116576f485c0954d7484e00392ed4d0c0cd0d402592b0ce6f09cd10022e15d100013d4000000000018735f840d1425ccf5356c5af4a1cc7d22fc01239910c64cf5221599d4012c4437205fd7542d1544217b8b0a5928b1c3a2405c38c836214ad3a30e8505034d8000000126558f400036a800043594e00af0000000012121f07db2d200003f98000619000054d40003d647375fc028500009e30a918535dc400000001de5144000000000033049c5000000000011cb535c24a000000000000001a5000000007871ed800052bd0e6069800045680000000000000072f54c010200000000000fa8000000000007024ab400000008cf000000000010484b6c00000000005d312de34d17162d711c41e2c5a258c520b27992e6000000029e0ef651e91b00d78d182a841da00017190000000000000056f0000000000033fd65458ec0004bdc000000175d61880003ef40000000ca11f186b148102fa49d4000317d42900000003c397ed3558f76129c000591c00000016a05aecc6c11612bb46f1122034d38b5c20f610aa40003514ab7229400000000d82dfc000000000000003bc2ad4b3b3730e19000117000005340534c0e4f6c8a91f582eb2a7cd5d104c8335b64fbf216496003f107702c072b4334ba211e86140de0a8838a43745b68af9003d4462e210a425656060001818000162c33f8000575cbc635808000c78000619c4f92040181441124a181d02f345c72019b00001dac6c42028b8925108e5000042a00002ad4ebc0002360bd701449024328c7246096230c3944a1d9130e450888214648050b10afe49e00003c2920a5f3851228915871d2c87918d4c32170d36927ecb8
  | 44 => 0xe254e4d9a0e809e000010df00004d550c46924cb87f3511cca7000000000000000000ca00000f85000000000000004344ab226c4f5216e43bb0c244c81be000005543522698314529d28637146e61a4075d511000056782f64fa55ca30740001bf85290001436354c000000000045e8e0c55484092e107a051484f634b45a841f0c4d1074dcb202c0001be800056456ac47a14945eec8ce1ec00005b2c00028441510000e0b0000000000170a56fca6a00005ab014c487499c1af57e42d01cd45a6102c00040796b6000045f1894e98000000049ed1f500003de00008dc0000503000049c21453c24bad71b108566f162d5fc433d3934d8515b1d4c1404d8d45817652fc55257152568e5b25a024325241bb0b0490c0fd0d5239355d05df0bb907bce44174154d471c00010d09040000000430c0a83224ac03880e7b32e0b2111b1596000098441144e4000149d3a68b3604d97ca06a4b950f0d5f42f9800000000000e54000000000057343a324f8c8d00000001038000097181144084d13ed13ad15d8b8a0000024060d0d20001851521c00000000000000000000086e000030f000000036180000000c870000ac8000000043d800013a400000000003e000002b2981c000073f2bb8fa925c41b42d815c100008ca14b40005d8094e001113b5f5164c34acf1c5bf0b9e367576a2030adc565c5240948497000098324740004a2943c000117d505081325cc0005c8052c34f0000138800012a4c2800010de59d02e259182f0000029e4be4c2d00000005a2cd0404d0cde5a44c0f0744000169101f00000000000000322d0d80000000000118738b48a3554cf9f1684000000122e07080004000fa226780000d3400000000001804000114d76d29516ad00000000000000370465d0000f7e2e5050500000000000dc0163000019650512c5c45b30b000060c159500016ca0000000000000052a800030316c71fdd05f00015e300013462e4800031b8afb0000ca900016df510c0003404000592426a00004ff12b8af343d537b297839611d0d773dec000000180424c0179287800054ad42700012e91c40ee72dd88a61e84caf147cd232f5459b1f6891c50d4b7e0b600db5784dd504a8d653bc946d3e6475022ad699027cab641b50ae14f8f4760cceed0a853640ce01a238bcd8300001a300000005a7c4705e6802b5b807bd04a0514257800020ac5cd40b11db3d7c000583084751780001de10152060000004c0000000701077d094439400000000001df8631294d80e5ffcff438908b5096c000000092c00016fb0000b865d640005184000089cd96550c00027e960e43bc3891b5c59f17084c90b5cc0d3f181e605e800000010420000000000187027100004b3800000000005d6d4f90af465c525873c5024000512163e00617ad4c3077646a4f9538
  | 45 => 0xd1a44a969e5fec0000000418000128d61503240ab8000431000045b400029180003cec98a382400046fc000000026b0000e5f00016003f6000053412b061645ef35600c600000002b8d66c2414fe8254d55d00000005648f1d21b401f3b006285b4c0005310000498400050bc48834e45a5000000035694930be480300003370000e5a2c3d6a256301803a6573f17b4000000014a000174f16c000003052e8000000000000003d5564000011b211ac33149a96ea083513406412460b94058137c0002ce000048a858d238000000011c600000000000aa052300000000000449c00000000005af44e80d60eb25b0d179181000028380001144c255ea80003e5852a53854eb015c6e422a17b65ee4d324b10f331f64f9d31fc613000089132c4256000000013800001348db600000a92b7c0000000000000129d000000000217e04a5c5c7000000003b159311514051a996eb27dc70a60a44682d780005a6d36602cc00058dcb01046ccfa59b8000000071c110819d57e0b293a3cebb00011ce23c12903ba5057336c000152000053357cd00000004fa8bea3eb918d4cd80800000b472240d7b5f74ef53dc540f46e8000100515f175d6af0000000568000004953a248f8000539491515cd7fe5f1978a000157935c9528000001b0000c34393c21705a49a75e242bb52a45f0000000044ccdb861bc937350003536d49c04e180001a2cce913580005d7800000000006130000000150d08840000000000000114440a0909000000034449262c154df3c64a4725f87f60000a4b000136500000002a154242490e3a2eb11d901a8e4721040000294f8a384d3603248929083172b37c81ce165182f10e525c408800051a8d8a2c9c0005d680002400f202b301f4000064944a400034a00004b48000198c5d130193315cf42470000a2861a01e94ca80005bd8d270880000259006e00002a6000080f0800c59000148012a14542cf983514e89f0579039f00c400000012894a8400000013b83978e6648fd220286d59d000034e56b133e3ba971f3cb488e53dc00019e10ee000165d243c0001fe0ac53f0ca100ce4000172c0000000aed0910faf2df000032f45a00c441ed18bc53d0b64237042cfe51c0cd5103e45893d3956f18686b4319918c1bb0f4d40a4000000000000000000000ba800013fe4c48a5f08d46652e0573b0000b315db91a00dac8cd00000004c0400032880004b84dee04f145b3ab93c549a15a53395199000000048cc0001674b5b0d713550a292ac01389e9261cb225bc80004004000563d84500000000000d211ee0aab12911662a787055e792b91ce0000000104726dc0000000ea71da1215343cb69095400000012480000000244ce050d101d5000000000008570000000000060653140e36018e1f00014be3b3565b229047519d8f
  | 46 => 0x848433977d000000048792224af4bcd13656112354000000000016180000001362572d40a2ca93131208322000080600000000b1d56b000000000000000ff582a381ca6f315c34f338d52f56689dd3d24bf4236d2e44f7068e61748f73bdca32363049d59b4c991b0903703d8a980db83af0d546ae4b68d551d247853c412310388c051769060131cc9f49b022e2824c171534cd844bd3b309d47a4180c3d75b9c0be30c4ec15f943d40258c6312cc3610ee133339ad54821c893100001820000a9008740000b7843e1b0d1861e596320000000464400000000003c8568434cc0d65370b1500017002d980002d64fd20000000000000015840003bf40000000000000000015e400024d0ddb2b655d300013f600014a52f44a6903e89781b8ce9255500003aa400019ed5b90000fee616921c5374cba4ed56035338a0a5d381b12685490000060e4e9004113985e004280770000e8e2c1c0000eac32e00000af037c01c00e0a3e0634682010ccf102fd0a055a036322804e310787c72ab03130e9086100007bc60ad72e00000003c5529800002b615c8ccd0000ef453d106a38b029a09052584d64ac75624ab81f8820437ccbbd000049a5bd1732000000052cc0001abc00000001f9417400057d8000225cf485aa0e6c5d040000db0000000083510bc84818b549836a4f293af071f00010a10001027000094529980fb442577f58849ef26b11e207907a644a09c61dec9d20dd53b137d844f391400039609232eb925502e82c84ec94d13b747292d1101324b88770194445267431b4b4031600000004aa40c00fe110a000175100014a60000bb84af118827d8000175496300013952c7458f00012e00000000000000054cd32400016cf4d58ee036bcd03523800000006c00000000128039e5ba029f19580000000e7c3cf4e9700000000000000000071b00000003b240005888000000000058940002d4c0005c18c7b000000000016b73f4510e20bd4323bb134144551e30f446ee26b4cfb08ccea506cd5f21410896512494326b98264ad89fc1980e1d44e41f516ccd62221cf25419896b58046371f309aa59c44bf4cc08942df58175a016ff1db8ea81dfc39761d51b505a84bc01ec0000f1c0003bc423d2b78f1823f07a34f04e9516f522955d445037900b80a2c9af451498832b06521eb4c81606836a35c5044313820731090c15c14cdd4b087ae545479a0a950fc16d916500005593f2d4ba5f11755375c70c00007c50550a6b5d40f64000000000007934e382e05f1cd950480c293e9cdd62f4980159155e82af472d27f522b443cf7c00000000000000000071451dcfef1ad80004c3576b000143f0cd829658e4fc4000108b27d0000206cbf6420d0aa222d2644de0f67000000049e96730000bf539d40000000000000046258500000a350350
  | 47 => 0x582c00000000001f047390c846f9070511454d0347000083a070175c000139a4c0982c00000003c0400038a90c758d03c50f8c00000000000a648e856b415253f504f22a851a03fd3f20f61841575923c000168e505d6ef15bc0002f140ef00015643bf095b0c9947323a8a651c58578342d4573b8d3d9321800041f53a8000108d15793be0c2011a000000041490582bd1266000000019b86c54d680000001438002c3100000000041d53100005700000e943738562000000002a80001c8c000438c72e2ec088336f4b7900016d80001391526cebf1e78862043c6db00000004b155b62a658775640a8e51f0752560c00000000005a204ed275c78453a9869185c06200000006000942496cc331f241483da800000002975f30500000048d0f707943be8e020ae50d400f4000403c0005fe903d39a8a340000bbe3b6800021e80003c440001990bfa0000000145c91f50e86bb2c6821c000000006ac854000000005780000000f600000000105d2f24db403f5d5955a07b00000000000000000054e0e9b46ac56617914c71308b3312850c800012ef000068c44ac0004b5d08e5d087983e946a42ed827a538ce1253182a80710d643cc84d422b0c1940744111c5cd6661990f4190c484345400046ed10b00009a9000026d3de973e58f06b50bd40004a597ac1ac07ec352898f0ec90a545d580b5cbd79f541046518853e445a8df518ac44128055f10000f1330880005948ce2000182309845c500006a142c57795a545dd524400017d876d3dfc8372dd400034b800043702fb610d17f02247a717a948a04e40f04c18d024e0400000000000e503fe00011a4526503f000106100012423950fba4c98000584137e0ddcecb301cf1a20c47d2205014e085400000009c8056c000033000023cd2d35eac087487c000000010d048c0000d9c97d00000000000d6113950672ac15b0149c00000010551404d38000049329f0000000000000000000000eb930803461d807a23040ba500000003ac400000011103b280000000000479468955a82e720216dc000150b493ce9c5f8ca5944b10eb353000006c042c294111d58a8caa000000000014bf19e57f3246c17c4e14000428896f012cdb73a0543d4c78a3708484a55e8152500003db07895c50b34000092c0000000dec000000041381380000ba933d11124ce40f2268c5c62a053720f38000075000029808d65e640002e9d351000000042d40000000d4e3e51686385cd22325d66342ccefb2ac506b602467e3be4e6d38696e31f10b6e29104b7159477d4754476213c2e14fc07e70a4d77b1560e2337780004bfcf90000063420651b94aac27800001b856a13fa47ad45321284db5ac513a26d11dd000052238981bd4fbd79004605683f9cfd53384000000034c26e80003c78c4f3f20ac90d001d304dd
  | 48 => 0x563f36800b157e80005d7d377155c00001590ba00012dd4afcf0200008a148ec8ec0a711d219c8a6c5504d8939fd67600c943b21254835ecc00051d000009e43070000e101da41661fa02dc5cd818c13d57fd42e164d4824db4546cca647152920000cc34e240003fa4a8b00000001ee8000000000009b000000000000828d9b2de95370c08a03472064c585c4643c7c21a0e1ce14586882443e4473064c7e459fd57a000018648203bf3e84300000000006710c50df514a0000c7e3b5ca1c00000005e94e8861189cb324006f000050600003b93db08215a1c23000000eb5a40cb43a880005e2d0924ea4cc71408e4e2f792d62aecccb0d056f74f94eee3f3c000324c000320802f00004301860000107d3d6000176541d0bca150111f541c51854ec1674728000230099a581c7701304c0a2aa46851b400000000481000000049dc00051002ea00017a74f20000000045a2dcd1f800016811bfd35b0dd826f00003355e1d236000014100000001330e7320b8beb0a18000000000000012390000e9e1f707cd0c9523400000004d307b1000000018208012a4c73617f40003f8c0002baca8d0b98e3500010b95bb54c25448f2b321134f282094c0b68b04265d7374c654c856ad3e259a96f94910d1c1bacd4236786bc09b918b4efca820000ed40ac800057544cf46285c433ad315000000009d1808000008d3a15425568c457611c000000065149640005fdc00000000004e8400005f80003d6c000535076f00000340f20fff5a0c0005114000000103b06f021814dcc4145f810637a470f576c95f20a86fb3440f8b071c8cc3e112cc2e64f53217ca7a0ecca9d290884c21d49d909013cc0000fc702b4a1242f57463b09411000082d5ed07660001388000000000000000000ad000011da0000e3b2a193800000d46000086b00005520000c012f0c000000052822258615ee8a433ab0c7c1a74711113000000000002108865000000000006460728e800fc00000000000079536833bc000026c0000000ff53cd000008400003e44670000081c22d80d000001111bf55741f3c00000015af11ed4e74f540000b48d902758b240000000355c94b5b14912000000037f14fb267155600000000000000618cd6b3ae80000001753335818e2fc579d072c00000000000000e0f00012b500013a0479d4b14c8442b0000000000000032fc00000000005bb8ad3000000000009063b3c198477125f00006a836e54a33d14000078cbb50000000573d2d12e600003e4872a483977513e0c471608f4401c4b5a5a1561d3af555525ec970017861c20d8b134c7404a000000c3100b512cc000000006c931d808f6028be20000af0000007d00007ef2505348105168228e141c3070bbc21d139021e0f5050a800000014d80000d7f439d04b3c5c0000000d20421cfb3
  | 49 => 0x20a2533c10a1608333d60422b98424c8d2a32688e3f406800001f12252e2c0005ba43f250209d11fe86020218e2b13c000046480000000000382108c39f4715137500d15a95764a50bad4709650084c86016c812f105851512306050d142b732ec000000167d1de400018018561d14c692b5cfca5b1971c36049dc0000b96414c54460c4a3b56f4000000000015ec000000167500000000d6c00039200000000b7234bc19518c83cb2be05905a595fe2368af20dc09961008bba569d2b255cd7980e446544938000600d6d744987a52d3c43b3168f273abc3da58c01b748e0b854134e6918a4e8c544d0ff43c01f75fd92c60e10c0357514810374ff10000000239d22601a09190000000504c6b90f906d938c0555063c05f56144785f882083eb40005bf56c824f142d4d5136a0000c0452acaef01411e14c0040c00001434d34460350d7033114564000000000000003fcd4c133f0ae11fd00004db80c425d4bb2040c7d0000000045705d418e90030bb8e8d0780029000170200005f34058000486c00011988f4557868a049000000000003f5c33f000023828e857f0001522357076a3804000412492103f81885218783018c03c2d8c435076c01d577c6913fd940e0ffd2d53ca956c07c419b378482537f816333b142600000002c200000001223008ca224819679508859c0980eb334f41565628bce24c8d5026914cb5c9c8fe4d70bbf540848f0ea96b40d650cb4380cd9410c54e3b851404364da23bbc6b31d708d9443151e0e349ca148c0005c4c000000091626cc0004fed033362cec4164400037c5748508cd1b5db00002434b9d00000001e0871d5fbc9ec272447f2fa01301b583bd31e000044c04985be80005f2000000005742fe005442046e0009d83a00013de5a90000143400054a517131bd12d4638f2e00007e9000000000000000000e8461016600000000000176300014e808c8974231d669527030b319566413183b700012ec5348732281140700015f028980003ce11470f954853da56a10e208fd3aac53804acb3a00000004d5c903093d3c65e0c000459002618985ac4cbc13111c400058b40005cd0000336905b000085c1a043ae459d3aa000132b108c00000000001360f5742a06d4000075e4dd40000000e0a618021941a4fc200cd0101bd49bb23513d815ad38328f497a4e64b7b4c604af3780d0c000061b5d892504dc4eb53be12a6000000030788e60000b9f01cc83b41cd58256f8000398c75b523c09e22b54101ecc1085cb569d00007e50f34dc20000000584c46d5f6041b45809400000d2500000001d380003f4176705b0c701ffc35142f111e51403560bd121800000902a8c0001d30af660080000000000401c00034e800007f0dcd1248dc3423d84a2c007342d54b4c136898549d0fa618b807819a519c32e
  | 50 => 0x706800b8c82c3b9180c03d01422b3d7db222800030d42dd4fa00003c3c30341ecc8038c48ba00005ff0fd94d65e20f6551f8000125000026e40000000b542bfc9e218246aa55c57a446dd44b000000025fc0004e3c546328c3ca00000004c2c000000115651ac6e84c114da6078d5400015362d3578216490f337400673d181aa1174292364400024e55171a80dea000000025584f200005f5425465e0000d412c182fc0000000475971d404800055080005bc1488152c6983b4455442f88264100a6804396921ab40004ac4a8f0000000000182d208c00046f955c000141914f0d934260acb05cceeb27f800041040003ee52540001303360000000007f1135c1e700006201a6c2f20f540000000c304b2c00052080003130a20000128f000000029c4000405d2a40000000418c0004d7d0051d84000000000007f4bc2583464d2d74dfb3c989df3cc4a5d08c4a915fb801700000253d512fd00012ca00016e23cfc29828c16022e0986b12287420298000101455f0000a4901d03b414c8000227109a4d251b104485fc553000032d86dd14d40a00c80e5c28157773ff4de65780d052fecfcc035549a38890fd12b179b21ec00040d0d3543a4000022045c5f6400044b800000000000000b6700003b545b8c020e3800042588e155f837b000078d00004953fe0d592f60055347c0001238c8f00000003b4045547f400000002c900008d13f34000406d150000184b209d0bf2fc8d4f53bd7091d60a02000059948c86dc38e50991ff417d081400000008920000ae7132cc15000083f2420e8718b044d00007a90d80fd30c54000000000000009915f4ceb42cdc3ef4f4ce4000008c800013521a948d22a48b4302d178537716c22c6d5212b497013a8c0000000be0121866101086ca00000000000253000069f2f9557d00000a200000002fc000054b8bdb1ed00005954b904edc39239c542c38e007f5ea09c2540505a2968a29208920332dcf0c5054e8b518c7d55bc43330100e8250d0ec64584e5632215783a594ae5b903ed20c8d3f000066a0398f982ed02760ce926e098c9f9317545c00011380000332491458845a400000000000000000276c00000012f31bcc9ab3e20000543d30736600000c04ba42784a875aad87923d8b933ec0dda204400059f0b773dc000043c400048015453058000386000000009cc473c4ea000000000012142541764000089921fd064202400032456de43e8f3546b4c553ec40000a0d78404f80001d2820e000032a3fb40005588dcf4c58a2500447095fa0047262c000177c754291516b3258000375000035c00003110cd239b91844e9d3e750a12f631853ec5ee00f1235d1b308f80005c8c24d00000000000000023808100000003de0a4d5ac04274e0950a4c4064134f861200000e91ea82be52b45ce253d0c
  | 51 => 0xee3c500ae14bc000000000009400000000d06054c00001684791fa85bb51fc1090fecc9551b0093367c1b553646335f40b6c2bdcf9700000004b9c00000a05ae075cd124e48d4b0000d6e0c281d60960016164cc265664264083c0d4525c0000bc40100a2018a50100005920ee530ac1ac4a0c43f5f681ae5d85837592d5ea0e6c049576561e19a020119408660001291134c5dc0001570214077c074918100000005a3ca8a29c0000179d59407ecd6a2dbd6b800008b12cf4a0610898441300fc126f1628000175816d0f1b000016d0890431000000000015031748000000005243b51f23854c5e61b049e022c00012f800033c86390000000131000004cc00051bc00027c57690000b343ce557b0bdc8f9490d5844760d2c36acdc64e3000006500f517ec00000004b20531155357d2f80e0c00000015fb0000dd9143c28f07246bf1988b6101d84f30000f5a3cbc2ab60417660c8c00060d000041b00000c1400044f86c72bb15652c780002ba400040b957c3a28aba144c5b7363c32903205d343316d04c70ef028ac0001c90b685d5d0111ae869a46b8abe24bcdd10bbc4ce57081323918647029c2c64460085099489e56603ec2e7088d3f380b502e499b412826849b4d750001076460cffa36ec000111915d1c7893b1d8934b0000e4249448682e5cad8000080e018000000013e112000ee199cf8d09dd2c94dccc9d46d11df000174a00000002d5c3995b440000000000442099010914a000002f8601c000000059859ec00000003ac4678048031cfda30fc2ff57f4f875b5400007848e35ec8744307c27f4b611ee5e44000593ce4b0000728000002249e52ea0b087775acc0000d2172635b57e410400003f817eb527ca1437b423f033d5195e5131f57b0000000000043740004e7027e00012b4000000008d80b6556c5250000000000019e50f961f1dd4a513b20000182842500dc89836c813d1098ddd000152c00007d30000000586000000007e34c5c0003b38419000000000000003b4d5c900005e533e0114000163639c8dfd00000de065c9bd0430697317000025a55ba2b690d75b3078f4844cf029713fd085900811a8a8351b8ec739e855c183c00001f963522d096c2eec000325085d38387222d0903a478081f52ed82859a117851887c34244d8704715e600000005fa49bf150d85b106851c00014b800017e7000000001c800000000004e597490000c4b00000000000000603c00018fc27c457800043b000000000005398485000000000011fa0000f9a0000000000000043f86160000ab911b8e1e481546820f565c3d2800013ac4bb2a9d1245b480000df860d000000002ec9722a112520000a150000bcb39f87194cd41f6295cea434c4fea2b0568c00008b0161555f16c4000594cf3c42d0f4b0000000374967714b8a2e13
  | 52 => 0x186a000025f0000000358c00000003903ac06b247bcbfd3ddd6db1ff87d700015ef2b9400005b88ff30f81cd1120a00399d1f746a951f11242f34a2cf620ca11cd124415706d95d21604e210ae953f000000000004635a5c90e00792f5262439a2a5cca432140003eac000199822a09210a60d2d322000000000007412a5544c0134147337c23a4bc556108190d523b587822f4c2135202fe3124bd924284e72de09793dac757445c000276857a0474d1e39c14f22c0c000583c2ed32a07ed29d1119187d721395cf7555c8856298400025dd22725f111100014bc3a7c8a23698cf64b04838374c0000f748672b5409461b49354e7d1851b54d784b8c00030600004fe007a12e15a1566c85e37217b03f7959c00000000000e61000000000000000f9d3e356b925a013cc7a44d58361c1d1b85499196045c0000978e8329310712f1c7480000429000174b4aa8ec5444c0003231353513d09f00008b219d4f2252d97ea000088f00007c234c15c800004a63c58e0d1af4bfe5b040004178e3d175800054192cd37ad47d000053000000001f0056d409133a0000cad5f7c0000001216255000047013f52b81320522c0003fb11bd55a42824f280004518edc2b10c
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xce472dc564440019b0e7b82c8880022fe1d64191100051e42ac83222000a9c83590644400155904b20c8880028fa1643191100945e422e43222000a3e85908644400147b0bb26a8880028f61365951100046fc1aecaa220028dc835d954440011df04bb2a8880063b20976551100046fc1aec2a220028dc835d854440011df04bb0a8880063b20976151100247a432e22a22012cb4645c454440010ff0aba6c68801e1f21574d8d100043fc2ae5b1a200787c855cb63440018b8c63aac6880032718c7458d1003c3f43eeab1a20128be87dd1634400187eebba2c6880030f1d77458d100061fba8e8b1a2000c3c751d163440018b8ebb9ac688003271d37358d1000c7743ee4b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a200087f855c9634400f0f90ab92c6880022fe117258d100945e422e4b1a20008df835c963440011ef02b92c6880023ba1c7258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a2000ce472dc563440018f0ebb82c6880032e1d37058d100143f42ceda9a200087f87597534400147908b2ea68800a9720d65d4d101b536412cba9a2000a5d85d8f53440010ff0abb2a6880022fe117654d100945e422eca9a20008ef825d953440031d904bb2a6880023ee017654d100143e43acaa9a2000a3c8459553440054b906b2aa6880d69b2096554d100043fc2aeca1a200787c855d9434400117f08bb286880023be097650d1000c76412eca1a20008fb805d943440018d8e5b2aa2880030fd94745451026e1e328e8a8a2000c7b65dc15144001878ebb2282880032b1cb64505100061e3a8c8a0a2000cac721914144001998e5b1a628816f391db724c510006f0390e098a204387d87d97504400117f08bb2a08804a2f21176541100046fc1aeca8220028dc835d950440011df04bb2a0880063b20976541100063bb2ee2a82200087f855d9404400f0f90abb2808800237e0d76501100146e41aeca0220008ef825d940440031d904bb280880030f1d764501100064e39ec8a022000c3c751914044001938e6322808806b1718c754c11008e4e318e89822000c5c75d8d3044001938e9b1a60880123da1b714c1100243e43aa4b28200087f855c9640400f0f90ab92c80800e3d20572590103e61e3ae84b2020048bc8750964040f7878eaa12c80800ead20542590101fc3fc3acbaa02007a3c8559254040810ff0abb2a8080121f21d65550100245e43ac8aa0200787c855d854040071e902b92c6080123721d3258c100045fc22eca9820128bc845d953040091f100bb2a6080121f21d6554c100246e43ac6a982004cd87058d53040010ff0abb2860801e1f2157650c100247c402eca1820048bc875914304009970e0b2286080123721d6350c10
  | 1 => 0x8e732a81880021f21d65503100062e39acaa062000c9c7399140c4001938e6b2281880031799773503100062eb2ee6a06200087d86dd530c40010fb0c3aa618807a1fa1e654c31003c3e43cca9862046e583099530c403d0fd0eb2a618806a1f21d654c3100061f32ee89862000c3d65dd130c400187cca3a261880030f594744c31008e4f318e89862047d98301d130c4001938e8b1a61880122f21175992100245fc3ac9aa42000a3f8559354840090ff0eb2ca9080028fe1165952103cf17316a92a4200787e85dd163840010fb0bba2c7080121f21d6554e100245e43ac8a1c2002a9c83591438400155d09baac508002ab6137558a1000637baceab142000a6e85dd162840014db0bba2c5080029ba167458a1000536c2ce8b142000ae7815d162840895c902ba2c5080038bd525458a100053742ce6b142000a6d859cd62840015cf02b9ac508112b92057358a1000727a9ca6b142000a6e8590d62840014db0b21ac5080029be157158a100053642ae2b142000aaf845c5628400155908b8ac508002b3e0d7158a100056641ae2b14207faeb805c56284089ccca2b16a3080032b98b745461026e1f328e8a8c2000c3d651d1518400195cc43a2a3080023b61b72546103447743ac4a8c207e8ec87589518400195ee8b12a3080032b1d1625461000637316eaa0c2000c6e621d54184001878eb32283080030f1d5645061000476c36e4a0c20008ec8758941840018deeab1283080031b1d562506100266c382c698c20008ed86dc931840b71dd0eb1263081f63b21d624c6100062eb9ca7b2a2000a758194f654400147d09296ca880031b5ca52d95100053cc04a5b2a2000c3f751d1654400187ca03a2ca880030f14074595100064fba6e6b2a2000c9c74dcd65440018beea39aca8800327dd073595100064e3a0e6b2a2000caf74dc96544001958e9b92ca8800333dcf72595100066639ee4b2a200087f855c9654400117f08b92ca8804a2f21172595100046fc1ae4b2a20028dc835c965440018deea392ca880032bdd07259510006563a0e4b2a2000ccf731c96544001998e6392ca8800e1f617705951021e3d286e0b2a2000cd873dc165440010ff0eb28ca880028f21165195100052e41aca32a2000a6c82594654400147d0b21ec8880028fa1642d911000477c12e332220018ec825c664440010ff0ab84c88801e1f21570991100061e3aee8b222000c5f75dcd64440018b8ebb9ac88800317dd473591100062e3a8e6b222000c9f741cd64440018deebb92c8880031b1d7725911000667b9ee4b222000ccc73dc964440010ff0ab92c88801e1f21572591100045fc22e4b2220008df835c964440051b906b92c8880023de05725911000637ba8e4b222000c6c751c9644400195ee8392c88800333dcc725911000666398e4b222000
  | 2 => 0x7765053003c3f42ceca0a600087d859d9414c0031dd053b282980023b60a76505300945e420eca0a600087e86dd5414c0010fd0c3aa82980021fa1f65505300043e43ecaa0a6000c6c72d95414c0010fd0e32a829801e1f21c655053000636390caa0a6000c3f75d91414c001878ebb2282980032b1cb64505300061fba8c8a0a6000c3c75191414c001958e432282980031bd9772505300063632ee4a0a6000caf64dc9414c001958c9b9282980021fe15761053003c3e42aec20a60498bf845d8414c0010fd0d3a8829804b0f19275105300043e432ea20a6012c3c645d4414c0010ff0fb2882980021f61f651053003c3fc38ca20a600087d87194414c00187cebb2082980030f5d764105300964e322e620a60038f8865c0414c025970c8b8082981278e94364d413008e4f398c9a826047e9830193504c001938c8b9ea09807b171cf655413008e4e398c8a826000c5f65dcd504c001938c9b9aa09804b2719173d01300d43f436eaa02601e87e861d5404c07fab0603aa80980021fa1f65501300f43e43ecaa02601ec5c73d95404c0010fd0e32a809801e1f21c65501300d62e398caa026000c3f75d91404c001878ebb22809805f271cf64501300061fba8c8a026000c3c75191404c08f938e6322809811fa60c064501300062fb2ee6a026000c5c65dcd404c001938c9b9a809801e1fa1e43997100043ec3c8732e200787e8790a65c40010fb0f214cb8801e1fa1f32997100043ec3e6532e201d87f8748265c400f0f90e904cb8800e1fa1e53597100062fb9ca6b2e200387e8794965c400147d09292cb880028f612525971000637b94a4b2e200387c8754965c40038d8e4a92cb880030fdd2745971000537414e8b2e2000a6d829d165c400187ae83a2cb880028fa1273597100051ec24e6b2e2000c5f739cd65c40014dd0539acb880029b60a735971001d3b40ce6b2e2000a75819cd65c40014f700b9acb880021fa1e43597100043ec3c86b2e2000a3e849c965c400147b09392cb880031bdca725971000636b90e4b2e200087e8790965c40010fb0f212cb880021fa1f32597100043ec3e64b2e2000a3f845c165c400147908b82cb8800297e0d70597100052e41ae0b2e2000a6f825c165c40014d904b82cb880761fe1d20597100cc3e43a40b2e20038bc845ce64c400717d0f21ac98800e2f21d425931000e5639284b26200387f8759654c400147f08b2ca98800e1f21d65553100951e422caaa62007c76655c454c400f0fd0bba2c7880021f6177458f1003c3f42ee4b1e200087d85dc963c40071b90e992c78800e1f2177654f1001c3e43acaa9e2043c787059553c40071bf0eb1e878811b1e1c26550f100063d32ee0a1e2007c76655c750c40018eacbb8aa1880021f61b75503100043ec30eaa06200087e8799540c40018b
  | 3 => 0xa3226088e1c30d94644c00117b0f328c89820e8fa1665191300045fc3aca3226087abb80594644c10d47d0c328c8982170f9d8651913041f1d980ca3226084e1e30194644c109c3860328c89820f8e0c065191300045ec3cc43226000a3e85988644c00147b0b310c89820aae60262191300045fc3ac43226000a3f85588644c0014790ab10c898002ade0562191300055a40ac43226012c3f759d4644c00147d0b390c8980028f616721913009656392e432260128be87948644c00117b0f290c8980038bd4a52191300051fc2ae23226000a3c855c4644c00155f04b88c898002ab20971191300945f4384232260008bd87084644c00147d0a108c8980028f614211913008d4f418423226000a9d83084644c08f57500108c898002ae600211913008d4f41e403226000a9d83c80644c00147f0a900c8980028f21520191300054fc1a403226011a9c83480644c08fd3060900c89804a1f21576d51300051ec2ec9aa260128bc845da544c00147b09b2ca8980028fa1b549513003d1e436a92a26000c3e76d52544c025878edaa4a8980021fe1576551300045fc22ecaa260008df835d9544c0011f700bb2a89804a1fa1f655513003c5f43ec8aa2600787c855d8544c02517908bb0a8980123721973151300964e322e62a26000ad583087614c0015e30010ec2980030fd9674985300061e32ce930a6000c3f655d2614c001878caba4c2980030f9d764985300061ebaec930a6000c3e75192614c00187aea324c2980021fa1f655853000636396cab0a600087e87195614c0018d8e432ac2982071edc065585300061fb2ee8b0a6000c3c65dd1614c00187eca3a2c2980030f19474585300045f43ec8b0a6000c3f75d91614c001878ebb22c2980032b1cb64585300045f438c8b0a6000c3f75191614c001878ea322c2980032b1c864585304065db80c8b0a6000c6f65dc9614c0018d8cbb92c2980032bd93725853000656326e4b0a60008f787584614c0015c904b08c29800e1f21576d45300045fc22eda8a60128bc845db514c00117f08bb4a29804a2f21176945300945f426eca8a60008bd84dd9514c02517d093b2a2980022f612765453000c77414eca8a60008ed829d9514c00f0f90a3b2a2980031b1cb65545300045f436e8a8a6000c3f65dd1514c09d878cbba2a2980022fa1874545300061fb28e8a8a604dc3c651d1514c00117d0fb22a2980022f21f645453000656396c8a8a60008be87191514c0251790e322a2980032b1c8645453000637b2ee4a8a6068c6c65dc9514c00195ec9b92a2980032b193725453025c3fc2aec28a60008bf845d8514c02517908bb0a298047279cc64145300064e322e628a60049d8805cc514c0010ff0abb6829801e1f21576d05300043fc2aed20a600787c855da414c00f0fd0bbb282980021f61
  | 4 => 0x18c0010ff0abb2831801e1f215765063000477c12eca0c60018ec825d9418c00147d09296ca980028f61252d953000636b94a5b2a600187f8754b654c00147d09316ca980028f61262d95300051fc22c5b2a6000a3c8458b654c0014ef02b16ca980029d20562d95300061eba0e9b2a6000a6e821d3654c0014db043a6ca980028fa1072d95300051ec20e5b2a6000c6d721cb654c0010fd0f216ca980021f61e42d95300051f426e3b2a6000a3d84dc7654c0014dd05b8eca980029b60b71d95300043f43843b2a600087d87087654c00147d0810eca980028f61021d95300f52f41843b2a6000a5d83087654c0974f50010eca980029e60021d95300cc3fc3a41b2a601d87c87483654c00187ecb3a4ca9801f0f19674995300061fb2ae932a6007c3c655d2654c00187eebba2ca980030fdd474595300064e3a6e6b2a600087f855c9654c00117f08b92ca9804a2f21172595300047bc0ae4b2a60038f4815c9654c001970e9b82ca980021fe1d65195300051fc22ca32a6000a3c84594654c0010fb0f310ca980028fa1262195300051ec24c432a608ba7980988654c0010ff0eb10ca980028fe1162195300051e422c432a6000a7781588654c0014e902b10ca9801e1fa1e42195300043ec3c8432a600787e87084654c0010fb0e108ca980028fa1021195300051ec204232a601aa5e83084654c0014bb06108ca9812a9ea0021195300053cc004232a601aa5e83c80654c0014bb07900ca980761fe1d201953003c3e43a4032a6000a3e8590b644c00147b0b216c8980062fe1d42d913000e5739285b226000a3e8598b644c00147b0b316c8980028fe1562d91300051e42ac5b226000ab78158b644c00156902b16c8980030f5d475d913000657b94e5b226000a3e851cb644c00147b0a396c8980022fa1e52d91300045ec3ca5b226000e2f5294b644c00147d0bb8ec8980028f61771d913000557416e3b226000aad82dc7644c00147d0b38ec8980028f61671d91300045f43843b2260008bd87087644c00147d0a10ec8980028f61421d91300bd4f41843b226000a9d83087644c0935750010ec898002ae60021d91300051fc2a41b226000a3c85483644c025878c93acc89804b0f19175991300061f3aec93226000c3d75d92644c0010fd0fb2ac8980021fa1c65591304563db80cab226000c3f75dd1644c001878ebba2c89800317dd773591300062e3aee6b22600087f855c9644c00f0f90ab92c8980022fe1172591300046fc1ae4b2260008f7815c9644c0071e902b92c8980031e1d770591300045fc3ac83226000a3f85590644c0014790ab20c89804a2f211721913009656212e43226000a3e85908644c00147b0b210c8980021fe15711913003c3e42ae232260008ef825c4644c0031d904b88c8982270f9db65191304470f186c
  | 5 => 0x21fe1f65105400043ec3eca20a800787f8719441500010fb0e32882a0003179d763105400062ebaec620a800087f855da315000f0f90abb462a001e1fa17764c5400043ec2eec98a80018ee829d931500011db053b262a00031b1cb654c54000636390ca98a8000ccc72d8d31500018decbb9262a00031b197724c54000667b1ee498a805bccc63dc931500818f4a13b6a0a001f0f19674d41400064e31ce9a828040d3a509d35050001938c6ba6a0a01239694363d41400146e41aeca828000c3f65dd15050001938c7ba2a0a00030fd9474541400064e318e8a828040c7a76d974050081c76c9b2e80a001f1e9d865d01402466d3b6c7a028002cda7618f4050001cb0ca31e80a023e6ee1d43d01400247c402eca98800487c875955310025878e8b2aa620013361c16354c4009557426eab108010aad84dd562100018deeb3aac42004b8b95354588400053742ce6b108000a6d859cd621011d55f08b9ac42004aab211735884000727a9ca6b108000aaf8454d621002555908a9ac420002bae01535884002574402a6b108000a6e8590d62100014db0b21ac4200029be1571588400053642ae2b10808daaf845c5621002555908b8ac4200029ba14715884000536c28e2b108012aae841c5621002155b0838ac420002b3a0c715884000566c18e2b108004aea801c562100215d30038ac4200029ba14315884000536c2862b10800087f855c9611000f0f90ab92c2200063b20b76544402fc5fc22eca8880008ef825d951100031d904bb2a22004b0f1d1655444000657316e8a8880008ed86dc951100011dd0eb12a2200023b21d625444000657ba2c4a888012cac7458951100031d905bb282200031b98b755044000637310eaa0880268ed86dc941100011dd0eb1282200423b21d625044000637baac4a088000c6c75589411002595ce8b1462200032b5d1628c44000c76416ec988800087f855d9311000f0f90abb262200023be09764c44000c76412ec9888004cd87058d31100011db0db9262200023ba1d624c4400047643ac498880048f4875853110025974a9bb280200031eddb75500400063dbb0eaa008000cbb7655140100019b6edb9a802000336dd87350040006ac3a8e6a008047d9b741cd40100016770aa0a80202321fe15725963000477c12e332460018ec825c6648c0018beebb9ac918003171d773592300043fc2ae4b24600787c855c9648c0011ef02b92c91800e3d205725923003c6fc32e7aa4604087f855d9548c00f0f90abb0a91811e37e1d64d0e300043fc2ae4b0c600787c855c9618c00117f08b92c31804a2f211725863001c3e42aeda8c600387d85dd9518c00117f08bb2a31804a2f211765463000477c12eca8c60018ec825d9518c00187eca3a2a3181370f19474546300043fc2aeda0c600787c855db4
  | 6 => 0x52fc2a41b1a8000a5c8548363500018b8c7baac6a00031718c7558d400043f43ecab1a800087e8719563500018bcedb28c6a0003875d36518d4048f0f206ca31a8091e1c40d9463500011bb0f328c6a000297a166518d400046fc3aca31a8000adb8059463500014bd0c328c6a0003179d86518d400070eba0ca31a8090e1e401946350121c3880328c6a00023761e6218d400052f42cc431a8000a5d85988635000153b09310c6a0002b66026218d400046fc3ac431a8000a5f8558863500014b90ab10c6a0002a7e116218d400056bc0ac431a8000ad48158863500018bca73b6a6a000a1f21576d4d400152e41ecba9a8000a5d85d8f53500050fd0fb2aa6a011f2718e76d0d400061f3b6cba1a8000e1c63d97435000187cec32e86a00038718c65d0d400154f436c7a1a8000c9e76d8f435007f8f0e032a86a0123361c36350d400063c32ee0a1a8040c3c76d954350001c38c7b2a86a01034e1c36550d401fe1e3b0caa1a8000e1c63195435007fa70e032a86a005ea7a1b7350d400164e3b6e6a1a8002a9e86d8d4350091938edb1a86a0123661c36350d40024dd43ee0a1a8048d9b731c1435000156b0810ec2a0002bc60021d85400062f39ecb30a8000c5e7319661500018becab9cc2a00031719573985400062f3aec730a8000c5d75d8e61500018bcea31cc2a0003175d463985400043f43ecab0a8000c5c73d9561500018d8e5b2ac2a00021fa1c65585400062e398cab0a8000c6c7219561500018becbb9ac2a00031719773585400046f43ec6b0a8000c5f75d8d61500018b8ebb1ac2a0003331cb63585400046f438c6b0a8000c5f7518d61500018b8ea31ac2a0003331c8635854000637b2ee4b0a8000c6c65dc9615000199ec7b92c2a00033318f72585400047bc3ac230a8000ae48258461500070f90abb6a2a000237e0d76d45400146e41aeda8a80008df835da51500051b906bb4a2a000a37a0f76545400046ec1eeca8a80018ee829d951500011db053b2a2a004a2f210765454000636396caa8a8000c3f65dd1515009d878cbba2a2a00032718f7454540024dd406e8a8a8000c3f651d1515009b878ca3a2a2a00032718c74545400064fba6c6a8a8000c9c74d8d5150001998e5b1aa2a00031bd9772545403463632ee4a8a8000ccf63dc95150001998c7b92a2a000237e0d76145400146e41aec28a8007c3c659d05150001938c73a0a2a00032718d74145401fc3f436eaa0a8000c5c63dd541500810fd0c3aa82a00031718c75505402b43f43ecaa0a8000c6c72d9541500a30fd0e32a82a00031b1c865505400062fbaec6a0a8000c5c75d8d4150001998e5b1a82a00031bd9772505400063632ee4a0a8000ccf63dc94150001998c7b9282a0003391cb61505400066c31ee0a0a8000c5c639d441500018b8c6ba882a
  | 7 => 0x3d65dd153900070f90abb6a3200029de05659464001c3ec2eeca8c80008ef825d951900031d904bb2a3200030fd94745464026e1e328e8a8c804687f8759451900011df04bb263200063b209764c6400247a43ac298c8000a3d8494f65500018bae729ecaa00028f61252d954000636b94a5b2a800187f8754b65500014bd07316caa00029760e62d95400052fc1ac5b2a8000a5c8358b65500014ef02b16caa00029d20562d95400051f420e7b2a8040a3d841cf65500018bae639ecaa00029ba0873d954000536c10e7b2a800087d8790f655000147d08396caa01028f61072d954000636b90e5b2a804087e8790b65500010fb0f216caa00038b50842d95400043f43e65b2a800087d87ccb655008147b09b8ecaa00029ba0b71d954000536c16e3b2a800087e870c765500010fb0e18ecaa00021fa1c21d95400043ec3843b2a8000a3e84087655000147b0810ecaa000297a0c21d95400052ec1843b2a8040a7a8008765500014f30010ecaa00661fe1d20d95400ec3e43a41b2a8000c5e73d9665500018becab9ccaa001f1719573995400062fbaee6b2a8000c5f751cd655000193ee839acaa00021fe1572595400046fc1ae4b2a80028dc835c965500011ef02b92caa000e3d20572595400066c39ee0b2a800087f8759465500014bf06b28caa00029720d65195400043ec3cc432a8000a5e8398865500014bb07310caa00021fe1d62195400052fc1ac432a8000a5c8358865500014ef02b10caa00029d20562195400043ec3c8632a800787e8790865500010fb0f210caa001e1fa1f32195400043ec3e6432a8000a3e840c8655000147b08190caa00028fa1331195400051ec266232a800787e870c465500010fb0e188caa001e1fa1c21195400043ec384232a8000a3e84084655000147b08108caa000297a0c21195400052ec184232a803fa7a8008465500014f300108caa00028fa1320195400051ec264032a801d87f87480655000f0f90e900caa004a8f21365d51402051f436a92a2807ae1c63d52545008167501aa4a8a01031e1c365551400049fc3aa82a28007a3c8655054500efc38c6aa0a8a00021fe1572d8d4003c3e42ae5b1a80018df874cb63500014bd0b316c6a00029761662d8d400052fc2ac5b1a8000a5c8558b63500015af02b16c6a0002b520562d8d400062eba8ebb1a8000e1f5495363500014bf0ab96c6a00029721572d8d400054f424a5b1a8000a9d8494b6350001c9ea5296c6a000297a1642d8d400052ec2c85b1a8000e8d4210b635000159d05b8ec6a0002b360b71d8d400052f42ce3b1a8000a5d859c763500011bd0e10ec6a00023761c21d8d400052f42843b1a8000a5d85087635000153d0810ec6a0002a761021d8d402456d40043b1a8000ad98008763500014bd0bb86c6a00029761770d8d400
  | 8 => 0xeb22862801f0f1d56450c500265c382c8a18a007a6e85dd162140334db0bba2c42801e9ba1674588504b536c2ce8b10a07ce2c549d1621412b4df0aba2c42801e9b21574588503df162a2e8b10a000ae7815d162140015c902ba2c42801e9b21474588500cd3743ca8b10a019a6c87951621400f4dd092a2c42801f8ba12545885000536c0ca8b10a007a6e859cd62141294db0b39ac42824e9be15735885003d3642ae6b10a007a6e8590d62140014db0b21ac4280029be15435885003d3642a86b10a000aeb8050d62140095d100a1ac42801e9b217715885003d3742ce2b10a050a6d859c562140d18d8eb38ac42824a9be15715885003d3642ae2b10a000aaf845c5621400155908b8ac42801e9ba1471588500cd36c28e2b10a07ec6c751c5621400155d0838ac428002ab610715885000567418e2b10a000acd831c562140095d50038ac428066ba600715885003d3742862b10a000a6d850c5621400f0f90ab92c2280022fe1172584500945e422e4b08a000d2c72dd1511400187eec3a2a2280034b1c874544500061ec30e8a88a04dc3f621d1511409ba5cc43a2a2280030f588745445026e96b10e8a88a056c3e611d151140ad878c23a2a2280030f980745445026e9d300e8a88a000c3c7459151140350f90eb1aa2280030f1d1635445000636392c6a88a01996e87dc95114001a58e9b92a2280671be1d62544500053743ac4a88a04fa6c8758951140338d90eb12a2280661b21d625445000717ba2c4a88a000c6c745895114001c58e8b12a2280030b1d1625445003e37b8ac4a88a007e677158951140332dd05bae822801f0f1d564d045000637baac5a08a007c6c7558b411400f8dceab1482280031b5d56290450277162a2c5208a0018ec82dd941140a30ff0abb282280023be09765045000c76412eca08a000c6e62dd5411400f878eb322822801f0f1d5645045000476c36e4a08a0008ee8758941140011d90eb1282280031bdd5625045003e363aac4a08a00387d855d8411409b878a8bb082281364f211751045000637312ea208a007c6e7558841140018daeab1082281378b151621045003e373aac5188a000c6d7558a31140031d905bb262280022fe11764c4500945e422ec988a0008ef825d931140031d904bb26228013361c1634c45000476c36e4988a0008ee8758931140011d90eb1262280123d21d614c45002678382c2988a000c5f7394d65d00250fd0f292cba004a8fa12525974000637b94a4b2e800787e85dc963d00010fb0bb92c7a000a1f21576d4f400043ec3ecba9e800287e87d9553d00011df04bb2a3a00063b20976547400961e3a2caa8e8000c6c7259551d00011df04bb263a00063b209764c7402043fc3acba86800487c87549659007f0ff0eb2ea92001f0f99574d4e400243e43acaa9c8000c
  | 9 => 0x64505313ec77436e4a0a62008ee87d89414c4b71d90fb1282988031bdd76250531006363aec4a0a620787e85dcb604c4010fb0bb96c0988063ba1b72581312d476436e4b0262008ee87d89604c4018deebb12c0988031b1d7625813100657ba6c4b026200cac74d89604c4011dd0e312c0988031bdd46258131006363a8c4b026200caf74189604c401958e8312c098a5f39dc462581313ee72b88c430262008fb87580604c4014f10ab00c098802ae211601813103d1f42c87326a00787e85dc963d40012f30bb8287a80d71b1c9535875000c7743ee4b0ea00487c855d941d40011df04bb283a80063b209765075000477c12ec98ea0018ec825d931d40011df04b8cc9280063b20971992500245e43a84b24a000a3f85509649400147f0eb24a9280ff0fe1d6495250204bdc32e12a4a000c7b865c254940ad0ff0cb88a9280765b20971152502b63b30ae22a4a01e87e87151639400187ee82a2c72807a97a0c5458e500051f424a4b1ca01e87e87149639403d4bd06292c72812f17dd56354e500266c382c6a9ca012c3e645d743940012f301baa87280122f21d6450e500061fbaac8a1ca002a9c83591439400187ce8b26a32807a1fe1d63d46500f62f39ac7a8ca05fc3f76dd15194001a58e5ba2a32815b0fdd8745465000696390e8a8ca000d38701d1519400187d0c3a2a3280030f61874546500061fb10e8a8ca000c3d621d151940ad87cc23a2a32815b0f18474546502b43e43ac8a8ca000c3c745915194001878e8b1aa3280031b1c963546500ecb743ee4a8ca067c6f76dc95194001a58e9b92a3280034edd370546500069c3a6e0a8ca000d6b72dc15194001ad0e5b82a32810e5e61b70546500063cc36e0a8ca01d96e82dd741940012f301bae83280025ee0175906500061ebaac920ca0008ef825d941940031d904bb2832804b0f99175106500061ebaac820ca000b358115041940012f700bac63280023be09764c65000c76412ec98ca0048f487585319400147b0b21ec8a80062fe1d42d915000e5739285b22a0008bf87590645400153906b20c8a80028f616431915000477c12e2322a0018ec825c464540050f90aba6c6a800a1f21572d8d5000c6fc3a65b1aa000c9c631d163540011ef0eb08c2a80063ba0a765055000476c14eca0aa00787c851d941540070f90b3b082a800237e0d76105500146e41aec20aa000c3d75d9041540031dd053b262a80023b60a764c55000477c12e3320a0018ec825c664140f9878a9b92c82801e1f21572590503de1e2a2e4b20a0008f7815c964140071e902b92c82801f0f9d1769505028c3fc32e32a0a051c76615c654140050fb0bba2c62806a1fa1e5458c500061fba4a8b18a01aa5e8395163140050fb0bb92c62801e1f2157258c500d43f43ca4b18a000a3e849496314009179
  | 10 => 0xb24620787c855c9648c4071e902b92c9189f30f1d7425923101c5e43a84b24627bc3c75509648c403958e4a12c91880ead20542592312b43fc3acbaa46207a3c85592548c4a30ff0abb2a91880e1f21d655523101c5e43ac8aa4620787c855d8548c4010ff0ab92c11881e1f215725823101c7c43a40b046200caf74189654c401958e8312ca988033a18b705953100674310e0b2a6200c3f751d1654c4031dd0fb92ca988032bdd37259531006563a6e4b2a62008bf845c9654c42517908b92ca988023ee0172595310247c402e4b2a62008ee871c9654c40195ee8392ca988032b1d072595310065dba6e0b2a6200cb874dc1654c4019d6e5b82ca988033a1cb70595310063dba8e0b2a6200cbb741c1654c401970e8382ca9880336dcc705953100675b90e0b2a6200ce8721c1654c4010ff0eb28ca988028f21165195310053c402ca32a62028f581dcb644c4018deea312c8988031b1d4625913100674316e0b226200ce8621c1644c401878ebba2c8988063ba1f725913100637baee4b226200c6c75dc9644c4010ff0ab92c89881e1f21572591310047dc02e4b2262048f8805c9644c4011dd0e392c8988031bdd47259131006363a8e4b226200c7b75dc1644c4018f0ebb82c8988033adcb705913100674396e0b226200c7b751c1644c4018f0ea382c8988032edd070591310066db98e0b226200ceb721c1644c4019d0e4382c8988022fe1d64191310051e42ac83226200ab880590644c4010ff0ab80c89881e1f215701913100477c12edaa262018ec825db544c40147b0bb26a89880e3721973d51310064fb22e7aa262008ef825da544c4031d904bb4a8988028f61365951313cf16316a92a262018ee82dd9544c4011db05bb2a8988021fe1576551310045fc22ecaa262008ef825d9544c4031d904bb2a8988023ee0176551310247c402ecaa2620787c855d8544c42517908bb0a8988023be09761513100c76412ec2a262008fb805d8544c4091f100bb0a8988023b61e65d893100477c3acbb126200aaf84597624c40155908b2ec498802bae0165d893100574402cbb1262008ed87993624c4011df0eb26c4988029be1564d89310053642ac9b126200aeb80593624c4015d100b26c498802abe1175d893100556422ebb126200c6d751d7624c4b55cd03ba6c49896eb960774d893100537c2ae9b126200a6c855d3624c4014dd0a3a6c4988029b61474d893100717aa4a9b126200a6e85dc3624c4014db0bb86c49896ab9a0470d89312dd72c08e1b12625ae6651d8b514c401958c5ba2a2988030fd94745453126e1e328e8a8a6200cac621d1514c4018becbb9aa2989f63ba1b72545313f47743ec4a8a625b8ec87d89514c40195ee9b12a2988032b1d3625453100636316eaa0a6200c6c621d5414c401878ebb2282988030f1d4
  | 11 => 0x504018becbb9ac0a080317197735814100c77436e4b0282628ec86dc960504018decbb92c0a08031b19772581410047743ec4b028200c6f75d8960504018d8ebb12c0a080333dcf62581410066639ec4b0282008ee8718960504018deea312c0a08031b1d4625814100667b98c4b028200ccc7318960504011f70eb00c0a0802b620d601814103c3f43c87328820087d8790e651040f0fd0f214ca208021f61e429944103c3f43e65328820087d87cca651040f0fd0e184ca208021f61c30994410951f420613288200a3d840c265104014dd04184ca208029b608309944101d3b408613288200a75810c265104010ff0e904ca2081e1f21d20994410062fb9ca6b2882128bc845c965104071e902b92ca2080e1fa1e52594410951f424a4b288200c6f7294965104070f90ea92ca2095b0f9c474594412b61e388e8b288200c3c74dcd651042547d0939aca208028f61273594410062fb9ce6b288212a3c845cd6510401878e8b9aca208029ee0173594410053c402e6b28820087e8790d65104010fb0f21aca208030f1d372594410951f424e4b288200a3d849c965104018dee5392ca208028fe1172594410951e422e4b288200c3c745c965104014ef02b92ca2080e9d20572594410043f43c84b28820087d879096510425c5e85212ca2084b8b10942594410043f43e64b28820087d87cc9651042547d09382ca2084a8f21170594410052fc1ae0b288200a5c835c16510401878e8382ca208029ba08705944100536c10e0b28820087e870c165104010fb0e182ca2084a8fa1030594410051ec2060b288200a6e820c165104014db04182ca2080e9da0430594410053ac0860b28820087f8748165104010f90e902ca2097f2d90576d50410951e422caaa0825fc3f74595541042587d0abb0a82084b0f615761504126e1fa92ec2a08200c3d525d854104ad87ca2bb0a82095b0f1457615041094dbc32e22a0824ecb7865c454104ada6f0ab88a82095b4d21571150410969b32ae22a08212d35655c4541049ba6ea6b88a82080369e097115041006d2412e22a0824dd37525c45410401a6aa4b88a8209374d141711504103c3f42ee4b18820087d85dc963104071b90e992c6209370f15176d4c4126d1e422cba9882008fb805d953104091f100bb2a62080e1f21d6554c410961e3a2caa988200c3d65dd1531040147b0c2a2a620802cd6045454c4100672396eca088200c7785dd941104018e90bbb2822084b2d95376504410063bbb6eaa088200c77761d541104ada6ee83aa8220803591c875504410065bbb2a8a088200ce776dc941104010ff0ab92c02081e1f21572580410046fc1ae4b0082028dc835c960104071f10e902c02084aae211205804101d7840a40b00820387c87549658c4010ff0ab84c91881e1f21570992310043fc2ae4
  | 12 => 0x95a8fe1141195410051f4266232a8200a3d84cc4655040147d09908caa08028f61321195412b71a20e4232a8200a3f84484655040147908908caa081e1fa1c30195410043ec386032a8200a3e840c0655040147b08180caa08029ba08301954100536c106032a8256a76810c065504014eb02180caa08028fa1320195410051ec264032a8200e2d42c8065504010ff0e900caa081e1f21d201954100716a124032a8200a3e84080655040147b08100caa097f2dd9171d51410965a20ced2a28251a3e86d52545049d87cedaa4a8a09e78b18b549514128d9b40ea92a28251c7471d9554504019c8c5b8aa8a08021fe1572d8d4103c3e42ae5b1a820087e87d9563504018d8e5b2ac6a08021fa1c6558d4100636390cab1a8200c6f65dc963504018d8cbb92c6a08031bdd46258d41006363a8c4b1a8200c7b65dc163504018f0cbb82c6a08033a18b7058d410063db28e0b1a8200c78651c163504019b0c6382c6a08033a1887058d410143e42aeda9a82008ef825db53504031d904bb6a6a081f0f19674d4d4103e1e32ae9a9a82018ee82dd953504011db05bb2a6a080a1fa1f6554d410070e21ecaa1a8200c6e76d9762504011db0f32ec4a08029ba1665d894100477c3acbb128200a6e8619762504018dcec32ec4a0a678bdd065d8941007163a0cbb128299e2e411976250533c588232ec4a08023b61e63d89410053742cc7b128200a6d8598f62504011df0eb1ec4a08029be1563d89410053642ac7b128200aeb8058f62504015d100b1ec4a0802abe1175d894113556422ebb128200c6d751d76250401c5ea92a6c4a08029ba1473d894100536c28e7b128200e4f5394f62504014dd0b21ec4a08029b61643d89414c557426e3b128200a6e85dc362504014db0bb86c4a08023ba1c30d894100476c3861b128200a6e850c362504014db0a186c4a0802aba1030d894100556c2061b128262ae6810c362504015cb02186c4a09471d94676d45412b45f434e9a8a8207c3c659d351504a3a6ca33a6a2a081f0f19574d45413173328ec5a8a82008ef825d951504031d904bb2a2a08031b1cb65545410061fb2ee8a8a824ec3c65dd15150401958c5ba2a2a08030fd9474545412b61e328e8a8a8200cac621d151504011dd0db92a2a08031bd9772545413463632ee4a8a827e8ee87d8951504d11d90fb12a2a08032bdd36254541006563a6c4a8a8256c3e7419741504a3c6ec9b2e82a08039918865d054103c3f42ee5b02820087d85dcb605040157308186c0a0802bc60430d814100637396cb3028200c6e7219660504018decab94c0a08031b1957298141006373aec53028200c6d75d8a60504018dcea314c0a08031b5d462981410043f43ecab028200c5c73d9560504018d8e5b2ac0a08021fa1c65581410062e398cab028200c6c7219560
  | 13 => 0x47743ec4b02a200caf74d896054401958e9b12c0a880333dcf62581510066639ec4b02a2008ee87189605440195ee8312c0a88032b1d0625815100667b98c4b02a200ccc731896054401cd4a0310c0a88023ee1d60181510056c41ac0302a2038bc845ce641440f47d0b21cc82881e1f215725905101c5e43a84b20a203ab48150964144071b90e992c6288023ee017650c510247c402eca18a20087d86dd543145190ff0ab92c02880e3e21d205805100e37396a5b2e820187f8754b65d04038dce4a96cba080a1f21576d4f411b537416cba9e8207c3c655d353d04050fd0fb2aa7a080a97a0f6554f411ad37416caa9e825187f8759751d04bf17f0cba6a3a084b0f1d165547410043fc2ae4b06820787c855c960d04070f90ea92cb208028fe1152596412b43fc3acbaa4824ea3f8759754904ad87f0eb2ea92097e6de1971d524126e5bc32e3aa4825fc3f74595549040127f0eaa0a92095acd205541524101c6e43a64b1c820387c87595539040187acbba2a7208021fe15725824103c3e42ae4b0482038f88748160904018bae729ecaa08071b1cb52d95410051ec24a5b2a8200c6d7294b65504030ff0ea96caa08029ba0a63d954100536c14c7b2a8200e2d8418b6550401c58c5a16caa09468f21942d95410071631285b2a8251b348150b65504018bae639ecaa08021f61e43d95410051f420e5b2a8251a3d841cb65504018dae4396caa09461fa1e42d95410043ec3c85b2a820087e87ccb65504010fb0f996caa08029ba0b71d954100536c16e3b2a8200a6e829c365504014db05386caa08021fa1c30d95410043ec3861b2a8200a3e840c3655040147b08186caa08029ba0830d954100536c1061b2a8251a76810c365504014eb02186caa08021fe1d20d95410043e43a41b2a8200c6e72d9665504018decab94caa081f1b195729954100637baee4b2a8200caf74dc965504010ff0ab92caa08022fe1172595410047bc0ae4b2a8200c6f751c9655040195ee8392caa0803391cb71595410043fc3aca32a8200a6f8259465504014d904b28caa08029ba0a631954100536c14c632a820087d8798865504010ff0eb10caa08038b61062195414df17208c432a829be2c41188655040147d0da10caa08038b18b42195412b51e4328432a8200e2f625086550401c58c4a10caa095acd20542195410043ec3c8632a8256a3e81d0865504ad47903a10caa0a6b8b88742195414d71610e8432a820787e8790865504010fb0f210caa09ee8f61242195410053bc0a8432a8256a74815086550401c5f04a10caa08038de0542195412b51f40a8432a8256a3c815086550401c6902a10caa095a8d20542195413e51f4208432a820787e87cc865504010fb0f990caa08028fa1232195410051ec246432a8200a3e840c8655040147b08190caa0
  | 14 => 0xc76d915454401c58c4322a8a88028fa1c64551510961f438c8aa2a200c3f72191545440187ae4322a8a88030f1c064551510061e326e6aa2a25fd37741c5545440117d0fb22c6a88032b1cb6458d510045f438c8b1aa200cac72191635440195ec9b92c6a88032b1937258d5100657ba0c4b1aa200cac741896354401976c9b82c6a88032e1937058d5100674316e0b1aa200cbb641c16354401970c8382c6a88033618c7058d5100674310e0b1aa200e2c62d93535440187ae8326a6a88030f9d864d4d5100716310c9a9aa200c3d87193535449b87ee4326a6a88030f5c864d4d512b61f388c9a9aa256c3c71193535440187ce0326a6a895a1fa1b7454d512fe1e3b6c8a9aa200e1c63d915354401c58c5b22a6a88030fdd06454d512b61e3b0c8a9aa200e2c62191535440187d0e322a6a893787dcc6454d510061fb90c8a9aa200c3d7219153544ad87ce2322a6a895b0f1c46454d510061e380c8a9aa200e1c64d8d5354401c98c5b1aa6a880a2f21176d0d5100477c12eda1aa2018ec825db4354425878c8bae86a88063ba0b7650d5100476c16eca1aa20387c865d543544872f100baa86a880a2fa1f6450d510154f41ec8a1aa24dc3e75191435440187aea32286a88032b9db64d895100476c3cc9b12a200aae8499362544011df0eb26c4a8802aba1864d8951006573b0c9b12a200e2d85193625453bc5eea326c4a88038b1d464d89514ef17288c9b12a29de2c5119362544014dd0daa6c4a88038b19354d895133d36432a9b12a200e2c6455362544011db0f31ec4a8802aba1263d895100556c24c7b12a2008ef8758f625440155f08b1ec4a8802ab21163d895100575c02c7b12a200ae88058f625446d8dceda9ec4a88038b19353d895133d36432a7b12a235c6e7654f6254401c58c8a9ec4a88029be1574d895116d3642ae9b12a268a6e851d362544cf4db0a3a6c4a89a38bd5254d895134537428e7b12a267a6d851cf62544d1c9ea729ec4a89a29ba1643d895100536c2c87b12a268a6e85dc362544cf4db0bb86c4a88023ba1c30d895100476c3861b12a268a6e850c362544014db0a186c4a8802aba1030d895100556c2061b12a267ae6810c362544015cb02186c4a8a731b5d462d815121c3ec3ea7b02a243a7a80d4f60544350ff0ea9ec0a890e9e20153d815103c3f42ee5b02a200a7985cc360544014f30a186c0a8802bc60430d815100657396c9302a200cae72192605440195ec8b94c0a88032b1917298151006573a6c5302a200cad74d8a605440195ce8314c0a88032b5d062981510045f43ec8b02a200c9c73d916054401958e5b22c0a88022fa1c64581510064e398c8b02a200cac72191605440193ec9b9ac0a880327193735815100c77436e4b02a2678ec86dc9605440195ec9b92c0a88032b193725815100
  | 15 => 0xca96c8a88038b18952d91510064fb9ce7b22a24ea3e851cf64544bf47b0a39ec8a893b87d4e53d91512751f428e5b22a25fa3d851cb64544bf17d0f296c8a88022f61e52d915127717a94a5b22a24ea3e85ccb645440147b0b996c8a897e8f61770d91510054f41ee1b22a200a9d83dc3645440155d05386c8a8802ab60a70d91510065db84e1b22a2008be870c3645440117b0e186c8a893a8fa1430d91510051ec2861b22a200aae820c3645440155b04186c8a897eada0430d91510055ac0861b22a200a3f85483645449d4790a906c8a88032b9cb649915100657b22e5322a212cac645ca645440117f0eb20c8a8802abe09641915100556412c8322a29cc6d75188645442593886b98c8a88028f61643191510051ec26a4322a200a3f84548645440147b0b210c8a880237e0d70191510146e41ae0322a212cb8405c0645440155d05318c8a8802ab60a63191510045ec3cc4322a2008bf875886454401c5b0a310c8a88038b5d462191514ff53a88c4322a2a0e2e511886454541c58a2310c8a8a7fa914462191510051f436a4322a200e2c62d4864544ad4790ca90c8a88038bd89521915100716312a4322a24da3e859cc645440147b0b398c8a884b271cd731915126f0fa9ca6322a24da3e859c8645440147b0b390c8a88028f61f52191510051ec1ea4322a256a3e81d4864544ad47903a90c8a8a7b8b88752191514f71610ea4322a200a3e80d48645442517d0f290c8a88022f61e521915126f17a94a4322a200ab78154864544ad56902a90c8a88028fe1d52191510051fc1aa4322a24de2f825486454401c6f02a90c8a895a8fa0552191512b51e40aa4322a200e3481548645440147900a90c8a89368fa1732191510051ec2e64322a24da3e858c8645440147b0b190c8a89368fa1432191510051ec2864322a200aaf825c4645440155904b88c8a884b2d1c5711915126d1f42e62322a200a3d85cc4645449b47d0b908c8a88028f61721191510051fc2a42322a24da3c85484645440147f0ab80c8a8802a7e0d70191510054e41ae0322a212cb8705c0645449b47d0b980c8a88028f61730191510945f43860322a2008bd870c0645449b47d0a180c8a88028f61430191510055741060322a200aad820c064544ad56d02180c8a8802ad604301915126d1f42e40322a200a3d85c806454401c5aa5900c8a88028fe15201915126d1e42a40322a200e2d52480645449b47d0a100c8a88028f614201915100636314edaa2a256c3f849db545440187e853b6a8a88030f50a76d51512b61f20cedaa2a256c3c419db545440187cedb26a8a895b0f9d864d515100716310c9aa2a24dc3f72193545440187ae4326a8a895b0f9c464d51512b61e388c9aa2a200c3e701935454401878c8b9ea8a897f2d1c7645515100672316e2aa2a25fc3
  | 16 => 0x1d85540047bc3ac230aa800ae48258461550011df04b8ec0aa0063b20971d81540053cc2861b02a800ab9840c360550818decab90c0aa0023ee1d60181540056c41ac0302a807c3f84dd9541502587909bb2a82a0030f90f76550540961e21eecaa0a812c3f42dd9541500187a85bb2a82a04b0f10776550540961fa06ecaa0a85687c8755161150ad4e902aa2c22a04b8d105545845400c7743ee4b08a868c6c75dc961150fd8d8ea392c22a15a1f21d525845400e36392a4b08a801cac72d0961150ad1790ea12c22a0072b1c942584542b55a40a84b08a8008ef825c664d4c031d904b8cc9a99f30f15372593530143e42ae4b26a67bc3c545c964d4c011ef02b92c9a980e3d205725935303e1f3a2ed2a6a607c3e7459254d4ca30ff0cb8ca9a99471d98571953532043fc32e12a6a60295c835c254d4c818f4c0b84a9a980a1f21572587530045fc22e4b0ea6128bc845c961d4c050f90ab92c1a98063ba0b715835300476c16e2b06a60287d85dcb6454c0317f0ea16c8a98028fe1542d915300e5739285b22a6008bf875906454c0157100b20c8a98023be09711915300c76412e2322a600a3d87d925454c0187b0fb24a8a986a1f21970951532b43e432e22a2a63596c825c45454c7f0f90cb80a8a980a1f61772d85530047bc3ac230aa60287d85dcb6054c011df04b8ec0a98063b20971d815300c7dc3a41b02a6008fb875806054c974f70ab00c0a9802ae21160181530043fc2ae4b0e860787c855c961d0c0517908b92c3a181e1fa1770587430043ec2ee0b0e860087f855c960d0c0f0f90ab92c1a18063ba0b715834300476c16e2b06860187f8754b6550d4387eebba2caa18023de05725954301c7a40ae4b2a86008fb805c96550c091f100b92caa18031edd470595430065dba0e0b2a8600cdb731c16550c010ff0eb28caa18029e20165195433d51fc22cb2a28640a78805965450c018becbb9aa8a18021fe1d65151431fd3c402ca2a286028bd84dcb6150c010ff0ab86c2a181e1f21570d85430047bc3ac230a860787e85dcb6050c010fb0bb96c0a18023be0971d814300c76412e3b0286018fb874836050c014f10a906c0a18023ee1d60181430053c42ac03028649abb845806050c0147f08a94c9a881f0fdd376553510061fba4c8a9ea20387e85dd943d448d2f100baa87a891a1f21d53583512353c402a6b06a20387c855c960d44071790ea12c9288028fe15425925100e5639284b24a2568bf87592549440147f0eb24a92895b0fe1d649525128cbbc32e32a4a200c77865c654944bf17d0f322a9288030fdd05458e5101c6e43a64b1ca20097581dd543944071f10e902c1288028f61643d91510051ec2c85b22a2018bf8750b645440155d0531ec8a8802ab60a63d915100716c28c5b22a200e2c62d4b64544bf4790
  | 17 => 0x11d20000002344ca291f168a5200005df187a3580000000001810000520000000000000000022000005b40001d2028e00039992080000000000000a944c300000000000000000980f5a7c0000000000000000022f4afc00006708ac5ce4753dc179caba3aa00000000006452448000f182c423a154c1a20003fc00000000000000c8cbc88180000000944593000000000000017280003c881200007183a24a5000000000043700021cc0002f000006d80000000001ca80000004299cb000085100000000000000001cc400000000000000000000d18128000000000091c00000045313d8f6e00000013d400051e0000000000741000073400001f2bf80000008b3100801043a2b22d80d2c1e400041d177432c6ec3bf15c4b5200000005942726192582360e9a000000000000000000000008a40d80000000d7c47600000000000000110403100020090008040084022840200d801880018c8000829400e01804008166100c20042400804110c0000020084110400018000980100500000200148100c4101c60104000000041c20000e0010200000510960000021906019442080420002010c00082c0088000800000040014001080000003000060186000c00084603800609042080000048020001000a0014400842209441004272044109404000200042310000004a00000218803100401804000003008221006200400004053006211821004003a840284221008108c0309000188000882200049280c009c0510400200a528021094c0084040140003c00108230a00000440080001102418060014010004009440094e2004c0199b208480000c00042261400084420018340520284270840000000a8427004600804200420000260bc0138400000810882218022105a428c0020040000000000000806180010044911401118230002000400090a31000408002140001042000009004231000200043108830040a180211802138421084003088018c0001802000c0008000006050180100011040400421199410802009040088440040300c403840018400000804040008000000200002008020004650148500400100c01800010426180613800310408004a0194000380401406000031002900c001002008041218022fc5f43e84b0ea801cac72d0961d50bf56d03a12c3aa04a1f215725835400c77416e2b06a8008ed82dc560d50f5a3c86b9ea92a0030f98d76d52540961e31aedaa4a812c3f625db549500187ac4bb6a92a04b0f18576d52540961fb02edaa4a800a3d86d5261950a30fd0faa2c32a04b0f1d3545865428d3b40ea8b0ca85187e87d4961950038d8e5a92c32a1469da0752586540051ec36a8b04a8018ee82dc560950011db05b8ac12a01e1f219719515428e3a30ae32a2a800cd8631c163550014eb0a10ec2aa002ad6102
  | 18 => 0x2685dc00010bc000000441800000000035b13b400000000000000000000ef9c184f058817e09c43928e63ff22dc0363863478b488e07780001fcd23800000018d40000002558000000000000084caaa000000150800c37d160a44800021e3c78c943780000000000000947000000000000000014e416e0004990efc0766c00000078f4447d41f0000ec400000000000000001f21a9d23c0d2000000000050604b01bc00010749b800000040b18a8000f7a00000000000000000000000000000000000015000000000010840000000000000495000000000000000000000001cf0000eb000000046092980123ef0000fa500e0001b3000102a000488800128c35818b0d6447a0fc1088ab800078100000000003a700025389ce0000001a20000000000195000061f00000006560000000a480006e21c400003628230000ec928a0004128000f8e000000000000000000000000001a90d609d02702082502484b003170000000000044000060c2e000030e97e815656d0000b7896a82b00000000000003e18000fc81e6000207400000000000000002d010e00000000000aa000000000043e23740003cb0001c6c0001921400f780000000000000000373000006517882c33380000006890000000bac0000000dd80000000000000000000000000000000000000000000000ab80000000003e2a08400000000006a8000000000000000028d0000d1400000000000000c00114368b740008bf00004ec0000002b400010540003929184c8e04d30f07700006fb000168c0000003330000b8657918c00000000001c0a1d81ba0fd079800000000000000010c81944830000000189000000000065600000012486bf4230000998773000000017862039414e8fe41451fa97140008b100000000000000000000000000000000000045c0000000c6c212000000000000000006b8fa6000000131c000000000025c15c3331398000da60000000000c6861a1251c1c000898000000118000000020a000005800000012362443a71aac4fc58e000000007859b09e9b1851e000000000049a0002a700000000003fc80000000002bd8d8000092e0001c0800000000000000002ab0000000a9a00000011347ec07b00a94209200c200000009ae0000000000da40003198000baa0000ed000000000000021b8c800003ed21f40007bb21d1020e3875021296142403791ea217c3000000001730a2a00000000004c450d40f0d8cd32000000216018e0173c88000458701498800000063f00004dcc2c0000001f18f4c84e0e58eb80460f40000000e52658000062c00000000022d4000713000000082e5b82ac8aa000000040780000004de000177800000006d000120492000004080007a1052000000000000000000000000001a1c5b600000019200003b706c84405ae4590
  | 19 => 0x850000201085486a8b40000a202348fb36b23e485623b0001b642e269137e233c0b60af0000000b0200025b8c4470610d31797641685bf0001698256000000000000095300000dce8033b48c00000000000001a940000000a7921c4b0000000000096268d2c480000000e22320000f32000000000000008c0b38000ad86fd0001d8d18c00040b00000005b7000000106c34a1d00e5cce20001e8800000005f00002842503be0b68e48000000000176c0000002c9244c4f645f000000000000012d800000073744e947ce880001c78764450000318800026000000000000003b1000000085a86748b873100a365223a41c00000031517f910a8340000d4400000c0ba994c00055c000166874a0002b82128ca0000000000000000000000009ca0000001bfc0003280bf00000000000001e180006591bf8a2d11e17a41800000000000001a480000000000000c1c00000006f817e4f30000000f340001360c0476a0003f38000e2000000000000001de0008000aa2000000155800000000000000006dc00013f40005462d78000c923d60950028000000418949800041c00024c00000003b000000003ec1a200000000000a5800000007d0ba112cc9c73c00000010d000014a000000053d000000000000000000000fc6c747780000006ef24c1ed43aa4ea3300a0800051100000000000410000d680000000000f4808a27f00000000000000e18f8c0002cf1e80000000405000173925e00000000000000000000000580000000000070000034f0e287ce000000040089826547e050864e6394548f84dea0002b011ecf1043f12598e10c00001a100000000000000000cfc67d000000000018800000000000ba0000b0c00000000019e80000000000000000493229a28c00000033a00000006a43b38f25196000075000059672243f83e924c58f00000000007d5001800030806123100000003af0000000370038408844c0004880001374ed86110000af40000000000b88ea26c82a6000000048c0870ba83c6000356800000023600000002420001a308180000002e08cd80000000000bd800000029414c8b3e7ca000000000000000000000001040a88be033c0000000000000000000000000070f000000003a0000001344b5c26b334000000000040c800084c00042a95bc74c04e17f0d045dc0000fa800080c000133986ca4e3681fc99844b84ee0eb0704c44000000000000000044380012320001538000cd80000000000a2000000000008ba0000ad136c0001f61ec8e1488881c0000d405740000a49d1c30405c018245525891d287997c2067d93b2093c05232132d800000000000017100000000002258000000417000000094300020f00000002b097b400000002f00000000001c20000000126477000000078404380605760421af0639
  | 20 => 0x25e00008287b865c000002c8000000001fd42ba6d4000000000042e1108a842b800000000000003df3428000484000000042800024e292a3ac68600009e05806700001e2000000000000000000005772fc2354f4a000083000000012300000000000000002234000000000000000025f000000000071f468115cf3e2f33b793c80008b80000000000404260800000000000005b800000000000003da26d000195c0000004a917804d04b40d0880cfdc48f00008250d849b03586040007ba0001b84176000000000000000034315691a438e0de8000534000000000000000000000012460000000000fd00001b100002f8000000000000050200000000006bb40a00000000000000914fd80002338a140008f00000cdcba25ca373000111281300000000000002fc818800000000000000000000000f0c00000000000011940000c893c115000000017a0e4043b40d0c100000000000001048000106800000000000000000004c2000000000015e22280000000000000000e3a6240000000f847df0c29100d4677008c938800000028e8000b8c00000000000007e100000000000001330000a300cb14a9b10ace098000168521200000000000000ff1b51ac80005f52a48f20f200003b716e40000000bc1f7400000000000000000001f30a98b960000000000000000000179800000000000004dc65e24f00000005b642800000000000000dc800000037400000000004840bc8906000000000000067611a800000000015480000001a50000e7c0000000000000000000000000018c00000015d80000003a580000000000000000f1a000192000000029100007800006050000c283d451404580000000000000000c6e4df000140490800000000000000004408000a680000cb80000000f72539320b9e27639d00008e41ad02d225d1220001280000890286000000000000027c8c1400000000000000006cd042162cb2c5fb041800000056a42082d82480000000000000000000000000000000000000000003408accdf000016d00003e800000000000008ec2a800000005eb00000000000000d410280001eb000239000080b0482430b780ac1ab23d018a393375a3d80006c2000000000000000000002c290400005b000066200000000006dd00000000000001fd0000f640b819e0000000000000000000079d1d212850881ba03a800000000000000004ee4bd00008c81404cb0ca800000090316c800028855b3d49ec40002400000000b7c0002450c0023c5192048e090924110bb97b000058311f0abc3140002af87c80003e51ca800000047e251843c0e81ff1ed00007281e739c181c00000000000000000160070378bc60003e48000cc81120001b8c00079e396a21065a04c36500000002e60000000e140000000bec00000000000000004fa
  | 21 => 0x238400000044400005d058d00010f800063202800003ca31f04d88e90366bc3fe8000000000000000000073f24084cc00000000000006fc396000001c000257000000077600024590f49b8117464800000084d00002680000000000000e00000000000000016429c08a4f308ab3cb105867a00000000005be000000000084e00000008dd0ba00025696b40000000000000000283000000073c44115280000004c449f90d0f9e38746f10c8ef439c13502e400091000000003a60003b08394e4652f000100400000000019e03f036e42a0000000000000000000032e2340c6c00061224b12a0ee40000000000000361000000000000000000001f05741e0800062400010b85e400000007c8ac000021a3e69f989c630e4a89a4034875c076000046249c02b8adc4a869306a80008d841f4471ed08205130a60000cd25870000ee8dec8710000000000000000000057200037b87100000003ad8f4c45c00040f8000000000000141c000000000000000000020900000005040788a3805640c316071c0481433e80bb0000080277800000000049d90a90e885a3f180000001f7221800114a00040b80004f80003f68000c0490d08d906400000000000000004c930a80000008c400000000008690002228074000000000000000017fa4385e2000000000000000000021ac00000000019f000085900018e80000000df80000000001e3000101c00000000010120001eb80d40000001120000000000438253c3dc0004490c7083600000002740000004002198000000093a1140c600000000000000000000b1464c4600000000000000000000031a00013c800000083937700006342892eb800052e39000010608a88dc000000025c0793c9800000086332680000000004a5800000000046f9470fb60880002308d5000038180000000d700000000000000001654ee85370201820000000000000000081000006ec47e89438a800093a00000000000000002c21da4000782000000000056e18e9cb82a42cc00000000000001ae23ccf142220000000000000000000000000000000007da53e0000000852000000000000037b00000009a619d29080002a60000000000a867970590000000000000000000000018f00000d40000000cfc0001fb0000af0b4a0001bd19ac00000000000000002022379a10000000000000062000005180000000000001da000000000008d000019b0000000000021000013c0001981cc083c00000000000004460002358000000000038000000013147380011d400029a8000e760000c980000004f4183140034e644000226400000044d8208c5c8030000000d1c000143800107e15621190785c87800001650ef2000000233400000003b94480000000001250f2405930017206908ba0be800000000011300000007040000ff
  | 22 => 0x2c05843c00005541823ee000000000000000000009fc0002b5800000a0000001384264000000192c17a0000001158a5c45a32d07bc00071116a80000006ba49a800043e00001f000034c0000000000478000000000055a26f341842466a73903b00000000000a68000000000000000000000002980007f6000000000000003f1841b38de400000000010a47e517d1ee4f7c5c00000e6c000523307800081a6e5000000000000033517846260001cc800000074c0000ef40007d40000000fe80002c11fc4000822000061800000000000000000000001b7c9f80000000000f6600000000000000000000ba4000000065234c00000000014cc00000000000000003d80069dc40000000000000e1854530080002c646635100005140a621c8dd0ffe00039a000000003d0001ddc58e0cf000166000011d2b1800000041500000010de00000000000000000000a70f2893c0d7800000000049585fc00000000014240000000000b5853059d0001cd400057c1070000000000000003c00000044113983a083b35000000003a100000000009050f88ff8d62000000000081e00000000000005fd0d80001292000000000000000000000000005c21eda16c1b603400001a00000950000d3400000000022f80660001978864d6e00025b000000010100021f80007cc296876d1727a33749c248d40e700011540000000001b244a260d3df800000000000000000000000000000cf60004a6800000000000000006d80000000000cda00000010b000052409b1c352728fe3661678b480cd462a284fee16b00024e008c00000000000000001b7800021667f15186300000001f580000003573e200000006803ec0000cea0000a08000fc000038a00000008ad2678a101fc0002251da80005f3464000059044928623e11185300e0210106e0003ef000006c01a045174067450300000000008a0000000088400038919080003ff0000000cee0000000000bc400000000000002930ee85280007ac1f89d945ea0000961a74fac0000e280000000001ad951c0003491f024000005ef000235cdb600000000007fa0004711ae0ea4000000000000066500000006580000001d5000000000000003684853d80000000000000000000000000017340007dc0001d7c00000000000009544313380b50da200024018188600000001e70aa432a0db9af400000014f96c848200000000000000002bd015000008e0da9318e1c7a834c1d5906423907688c000001c0000f549c00b100012380000000000dad0f20be000000039c02a1d680003340002692240c8c2dc000000000008d0000000000000000000091a0000000000000742000000000000000018ec828000000000000000000010d8ca40000001e9061600018600000008bb1a3800000000000017b8d1800006183a497c00
  | 23 => 0x2ca0001d2419200000005c800094c0000000f067fa00012440000001f91c84ae675931680004e007f0000c0d2665b125da29000000000000000000000000d900d84d00001c6400087800015d4000000000000056800000000000000001d410e00000000ff00002b600000000000000000000000a34122000101c50258c453800000000035480003c400014600b800060345798300862161e000003446d50000ab04f491a38580002ec5861101894f6c7300ac84a4e8c5e946c8000000000451141400000000000000000001248000000169413990c274000000000125029023e0fc0e5e00002b01cc00009100000000000000000000000000000000000000000013ac00000000004702c40001912270000000175a11c00000007da4881a85da1d800000003890001d14d2a0c01698000df27bc06e04bc00000000003c0a5425310d800000000000025100000003fb000000000000000000008b0150168800009f1dc188c128000000000045e8260000000000000000009800006700003d80000000000000b586cf0000000000099000000000000046391ccdc800047f94d8f365d2000038078a0003c480000006ae000000014e0002ac000000000000012bc00039d00021a8d5406d27200009ee66f000000000000000021780007a02cba2b00000000000000372000000000000000008c0000b14065000000101a000000000000000000000000005721a780000000001ba97dc000838000000000000000000000000000000000000000000000000000000000006ba0000000f1c9ac26145b24d92147ae183800000053c00000004c80002371d685f28e00001a280000002b209a40000000001f200000000000000d2800039b000000000006800000000000001d3c0e451b0001b68000000000000000000000000000008e5000084000000000004f89b4354000000000000020720f521e0003208000000000000083025a00000000000005a000011c48a2000496800068024800015880000000000000000296000155c0004d532614580000003e9000000000000000002e600019900000001341021a2ceec829259995495c45037000000001680000000000000000000000000000000000005b30001cc80006fa0001f0400000018c800000000029d889c3e63f7000000000000000000000e2000000000000000000000000001d838d0000000726000000058400000005bcbe400030a0000cba7ab3829a71098000033000115476d15b000000087b3ac12a510c2e30c8000000000024f800000000000000011d000000000000000000000000d040000001c200000000000000be24a40000000d9600039f00011da00000000000005f43be024c0000ef395a10c0000000001350b560e836280000000000000000e2c00014c80010b883329881
  | 24 => 0xba800000000000006d0427984c6124b9000057c48c000000000014a4d82f50b249d23530001ba800052c234800010c5bd32780011ee0000001fbc00011507300000000000000000498000000000090c000028a0300004ba22d8c3400001426c9b7800063e425800128400000004d44700000000000efe314075918c0000a20000fd005a59007096a05de629267072000046d07204140000000000bdc000000432a3680000000001c7883a1f944f00000007e900000000000000000afc00000000018a0ce64220001fa800000000987f022800000017601dc012000000000000046d800000053f3fe00011e45f6000022400084800001e0000000139142c0002be00000008068c331598f000000034f8c800000001b68f88ff66c3056800129400044980000005441fc113c5b0000000000033e0000000d7cba607c0000954f4e54000000000000001a913290c4000000249489c3a235aa4f8c4e02200016442900001e6800000088b000000000000000016d424a8770000a880006e700000002f60691b891e80000000000000a9e00040080000000003c2800000057d49d000056a60b0c780e4d584993a98ef0b9200028b800076600000022547344582aa1194000000000033002000000000012021a00002330000000000000000052b0a8000000000000000000f40000000a7400000047a88cc050000000000000000024b800013c6632a41bc438406e1c89b6000037000000000007d12ff80000000001c59e2c000000000000000000006fa0281c600042b93004a40000001c60000000000034c000000000000000000023b80000009290b3245858c50e48a11e000000000000006aa8e30f42184ecc7e2170a1d40001110f4a01000064a000000041600000011e40005bb34d0a9000000048580000003b63b58000000031000000027e25d08b067016a00000000012540003ae80000000003ca800084220000007500000001c68cc4d8294049e931445a00030ba0188fe4e840105003e004800000006f04b210280c83660004178f08efa00017e824859a0a929480008bc82d0ac1fac000000000000092463000013fc00072400000000002630000000c208b20b507f4c385c708418244866b419c800021805500006c91a800000000000003dd1f992fca440002f800004ea064000208019000000000000006fe155000000000010c1bcc00000005500000003a914da15879800034b88940000000000850eea8fa0000ac423e8ae000000000000000000000005ba000000000000000000000004f81e7000000000046700000000000000000b320000002268000000000000000062600000000000000000000cf20000001d5c00075e000000000000000000000000001a7000000078700000000000000000000aca7ce0000000dae2b826683100000
  | 25 => 0x12c80000000003a51ae400050a0010a784fa0000000cf81665e52788000a8200000000008340001c613ec0000000001ac030e22a4a82020d4c6723c70c089d80472101ebcfae05225e00006600000000000000743000078400092743d000000000017000000000000000000000000000111906a3b93f8000000000000000000000000000204a963a30000ed000037707a9828d364ac00000008267cb00002c00000001d59a58d5e5a73768000e4e000000000000000000000006ce0000000000ef602544f8fa80000000001acc00000000000003a459c1e50bb40006f038b988411e000000000029c0003508bd0e7a05d0000000000000000000005e0003d500003560202d515a40000084390fa079e61800002140000000000000bf863d19499b83f41d73aa9bd059c00021201240000002bc081c0000004a080006d20000a3000000000000000000000000000000abc1ca00000009700000cc80000000002b3000000037c12d0d303d8027219895866800000012680008f10000000000000000035813800047e8
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x6c0991e00700227c6803a2cd180470b00064c0001410014001c4970c1481e1820015004800010900024c244f689e0881548645440142d921c064551512b50d24572191535440142d921c06454d510050e241751914354535a2481d8942195414de892046250865504ad23698e0542195414d689e0881508655054d6249150b201954152d892454248065504018387420173594412b60d204745c9651040182c7460870594414fe49214825c454104ad1349854971150412b50da47621d15194001a245420574588500cc1ba5e87589511400182c87dd162544500060ba1c74589511400182c871d162544500cc1ba637558b411409b42c945d562104500060718f875505450149c187018c6550d4051e860c085480644c08f898801917314530487060c075191404c00103f985d074597100041be61721c965c4145c1830994744c310
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x2
  | 4 => 0x1
  | 5 => 0x4b
  | 6 => 0x4c
  | 7 => 0x6
  | 8 => 0x94b
  | 9 => 0x94c
  | 10 => 0x124b
  | 11 => 0x124c
  | 12 => 0x1b4b
  | 13 => 0x1b4c
  | 14 => 0x9cb
  | 15 => 0x12cb
  | 16 => 0x10b
  | 17 => 0x10c
  | 18 => 0x5
  | 19 => 0x1c0b
  | 20 => 0xa0b
  | 21 => 0xa0c
  | 22 => 0x130b
  | 23 => 0x130c
  | 24 => 0x1c0c
  | 25 => 0x14b
  | 26 => 0x14c
  | 27 => 0xa4b
  | 28 => 0xa4c
  | 29 => 0x134b
  | 30 => 0x134c
  | 31 => 0x1c4b
  | 32 => 0x1c4c
  | 33 => 0xb4b
  | 34 => 0x144b
  | 35 => 0x28b
  | 36 => 0x28c
  | 37 => 0x1d8b
  | 38 => 0xb8b
  | 39 => 0xb8c
  | 40 => 0x148b
  | 41 => 0x148c
  | 42 => 0x1d8c
  | 43 => 0x2cb
  | 44 => 0x2cc
  | 45 => 0xbcb
  | 46 => 0xbcc
  | 47 => 0x14cb
  | 48 => 0x14cc
  | 49 => 0x1dcb
  | 50 => 0x1dcc
  | 51 => 0xe8b
  | 52 => 0x208b
  | 53 => 0xecb
  | 54 => 0x20cb
  | 55 => 0x74b
  | 56 => 0x74c
  | 57 => 0x194b
  | 58 => 0x104b
  | 59 => 0x104c
  | 60 => 0x194c
  | 61 => 0x224b
  | 62 => 0x224c
  | 63 => 0x749
  | 64 => 0x1949
  | 65 => 0xb4953
  | 66 => 0x144953
  | 67 => 0xbc9
  | 68 => 0x98a
  | 69 => 0xb5b53
  | 70 => 0x1dc9
  | 71 => 0x589
  | 72 => 0x2089
  | 73 => 0x1789
  | 74 => 0x5c9
  | 75 => 0x17c9
  | 76 => 0xa0114
  | 77 => 0x28e
  | 78 => 0x148e
  | 79 => 0x14bd3
  | 80 => 0xbc153
  | 81 => 0x194a
  | 82 => 0x15953
  | 83 => 0x134bd3
  | 84 => 0xbd353
  | 85 => 0x135dd3
  | 86 => 0x74a
  | 87 => 0x75353
  | 88 => 0x134753
  | 89 => 0x135953
  | 90 => 0x1eca
  | 91 => 0x140c
  | 92 => 0xb8293
  | 93 => 0x74293
  | 94 => 0x28753
  | 95 => 0x224a
  | 96 => 0x2a253
  | 97 => 0x1d8b93
  | 98 => 0x1f0a
  | 99 => 0x75493
  | 100 => 0x148753
  | 101 => 0x14a253
  | 102 => 0x2d953
  | 103 => 0x1f4a
  | 104 => 0x140e
  | 105 => 0xecbd3
  | 106 => 0x20cbd3
  | 107 => 0x104bd3
  | 108 => 0x224bd3
  | 109 => 0x754d3
  | 110 => 0x14c753
  | 111 => 0x14d953
  | 112 => 0xeddd3
  | 113 => 0x105dd3
  | 114 => 0x74ed3
  | 115 => 0xec753
  | 116 => 0xed953
  | 117 => 0x20d953
  | 118 => 0x104753
  | 119 => 0x104754
  | 120 => 0x105953
  | 121 => 0x225953
  | 122 => 0x225954
  | 123 => 0xd0e
  | 124 => 0x1f0e
  | 125 => 0x20c
  | 126 => 0x20e
  | 127 => 0x1b5253
  | 128 => 0x1b4114
  | 129 => 0x1b4154
  | 130 => 0x98114
  | 131 => 0x14114
  | 132 => 0x5c591
  | 133 => 0x130154
  | 134 => 0x134114
  | 135 => 0x1c4114
  | 136 => 0x17c591
  | 137 => 0x131354
  | 138 => 0x1c0154
  | 139 => 0x98154
  | 140 => 0x1649
  | 141 => 0x148113
  | 142 => 0x178113
  | 143 => 0x10a14
  | 144 => 0x74591
  | 145 => 0x194591
  | 146 => 0x14c153
  | 147 => 0x17c153
  | 148 => 0xec153
  | 149 => 0x194153
  | 150 => 0x104153
  | 151 => 0x124214
  | 152 => 0x28b93
  | 153 => 0x75f12
  | 154 => 0x1f0752
  | 155 => 0x40752
  | 156 => 0x44a
  | 157 => 0x75f52
  | 158 => 0x1f4752
  | 159 => 0x20296
  | 160 => 0x44752
  | 161 => 0x196254
  | 162 => 0x1dc591
  | 163 => 0x44591
  | 164 => 0x58751
  | 165 => 0x98752
  | 166 => 0x1b8752
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2559
  | 6 => 6268
  | 5 => 2388
  | 4 => 32
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
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*2) 2
  | 8 => packedAt gbK8 (1660+((h/20+packedAt gbK8 (1560+(h % 20)*5) 5) % 79)*7) 7
  | 7 => packedAt gbK7 (98948+((h/853+packedAt gbK7 (94683+(h % 853)*5) 5) % 5198)*13) 13
  | 6 => packedAt gbK6 (315487+((h/2089+packedAt gbK6 (300864+(h % 2089)*7) 7) % 8149)*14) 14
  | 5 => packedAt gbK5 (144872+((h/796+packedAt gbK5 (140892+(h % 796)*5) 5) % 4851)*13) 13
  | 4 => packedAt gbK4 (2290+((h/10+packedAt gbK4 (2240+(h % 10)*5) 5) % 42)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfe0ffc07ff01ff03fffffe00013f9f9d8e73fc
  | 1 => 0xfff07ff81ffffffc07803fff0ec464fe73fccf
  | 2 => 0x7ff80001ffe0ffff8003ffff0f878e3838f0f
  | 3 => 0x7ffffffe0000fffffffc000ff007f03fc0ff0
  | 4 => 0x7fffffffffff00000000000ffff8003fff000
  | 5 => 0xf80000000000000000000000fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4a0294012710930148a9b2060019898c86315c
  | 1 => 0x90502d8809432544050284aa0644243430d4c5
  | 2 => 0x46a5804312b48aabd005395470b858c3830b0a
  | 3 => 0x85394ad640200cf2a6560018bb007603580ea0
  | 4 => 0x7ce73679cf9c020c0181060ddee8003efe000
  | 5 => 0xe000038400c100c304602180eff77ff8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeac8eec8eac0feeaeac8eec8eac0feeaeac8eec8eac0feeaeac8eec8eac0feeaeac8eec8eac0feeaeac8eec8eac0feeaeac8eec8eac0feeaeac8eec8eac0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40057
namespace PEqualNP.Outside.L_meta_40057
open PEqualNP.Outside.L_meta_40057.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 16 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 13 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 16 := block_range (n:=16) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 16 := bs1_3_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 6 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 56 := (concat bs2_3_0 bs2_3_32)
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
theorem bs2_4_128 : Interval s2Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_160 : Interval s2Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_224 : Interval s2Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_256 : Interval s2Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_320 : Interval s2Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_352 : Interval s2Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_416 : Interval s2Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_448 : Interval s2Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_512 : Interval s2Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_544 : Interval s2Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_576 : Interval s2Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_608 : Interval s2Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_640 : Interval s2Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_672 : Interval s2Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_704 : Interval s2Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_736 : Interval s2Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_768 : Interval s2Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 781 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bs2_4_0 bs2_4_32) bs2_4_64) bs2_4_96) bs2_4_128) bs2_4_160) bs2_4_192) bs2_4_224) bs2_4_256) bs2_4_288) bs2_4_320) bs2_4_352) bs2_4_384) bs2_4_416) bs2_4_448) bs2_4_480) bs2_4_512) bs2_4_544) bs2_4_576) bs2_4_608) bs2_4_640) bs2_4_672) bs2_4_704) bs2_4_736) bs2_4_768)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_64 : Interval s2Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_128 : Interval s2Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_160 : Interval s2Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_224 : Interval s2Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_256 : Interval s2Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_320 : Interval s2Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_352 : Interval s2Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_416 : Interval s2Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_448 : Interval s2Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_512 : Interval s2Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_544 : Interval s2Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_608 : Interval s2Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_640 : Interval s2Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_672 : Interval s2Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_704 : Interval s2Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_736 : Interval s2Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_768 : Interval s2Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_800 : Interval s2Atlas 5 800 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 801 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bs2_5_0 bs2_5_32) bs2_5_64) bs2_5_96) bs2_5_128) bs2_5_160) bs2_5_192) bs2_5_224) bs2_5_256) bs2_5_288) bs2_5_320) bs2_5_352) bs2_5_384) bs2_5_416) bs2_5_448) bs2_5_480) bs2_5_512) bs2_5_544) bs2_5_576) bs2_5_608) bs2_5_640) bs2_5_672) bs2_5_704) bs2_5_736) bs2_5_768) bs2_5_800)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 44 := (concat bs2_6_0 bs2_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_7_0 : Interval s2Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_7 : Interval s2Atlas 7 0 1 := bs2_7_0
theorem alls2 : ∀ k ≤ 7, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
  · exact alls2_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 24 := bs3_3_0
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
theorem bs3_4_96 : Interval s3Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 117 := (concat (concat (concat bs3_4_0 bs3_4_32) bs3_4_64) bs3_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 46 := (concat bs3_5_0 bs3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1 := bs4_4_0
theorem alls4 : ∀ k ≤ 4, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 2 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 6 := bs5_4_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 32 := bgb_4_0
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
theorem bgb_5_2368 : Interval gbAtlas 5 2368 20 := block_range (n:=20) (by decide +kernel)
theorem ggb_5_0 : Interval gbAtlas 5 0 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) bgb_5_64) bgb_5_96) bgb_5_128) bgb_5_160) bgb_5_192) bgb_5_224) bgb_5_256) bgb_5_288) bgb_5_320) bgb_5_352) bgb_5_384) bgb_5_416) bgb_5_448) bgb_5_480) bgb_5_512) bgb_5_544) bgb_5_576) bgb_5_608) bgb_5_640) bgb_5_672) bgb_5_704) bgb_5_736) bgb_5_768) bgb_5_800) bgb_5_832) bgb_5_864) bgb_5_896) bgb_5_928) bgb_5_960) bgb_5_992)
theorem ggb_5_1 : Interval gbAtlas 5 1024 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_5_1024 bgb_5_1056) bgb_5_1088) bgb_5_1120) bgb_5_1152) bgb_5_1184) bgb_5_1216) bgb_5_1248) bgb_5_1280) bgb_5_1312) bgb_5_1344) bgb_5_1376) bgb_5_1408) bgb_5_1440) bgb_5_1472) bgb_5_1504) bgb_5_1536) bgb_5_1568) bgb_5_1600) bgb_5_1632) bgb_5_1664) bgb_5_1696) bgb_5_1728) bgb_5_1760) bgb_5_1792) bgb_5_1824) bgb_5_1856) bgb_5_1888) bgb_5_1920) bgb_5_1952) bgb_5_1984) bgb_5_2016)
theorem ggb_5_2 : Interval gbAtlas 5 2048 340 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_5_2048 bgb_5_2080) bgb_5_2112) bgb_5_2144) bgb_5_2176) bgb_5_2208) bgb_5_2240) bgb_5_2272) bgb_5_2304) bgb_5_2336) bgb_5_2368)
theorem allgb_5 : Interval gbAtlas 5 0 2388 := (concat (concat ggb_5_0 ggb_5_1) ggb_5_2)
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
theorem bgb_6_6240 : Interval gbAtlas 6 6240 28 := block_range (n:=28) (by decide +kernel)
theorem ggb_6_0 : Interval gbAtlas 6 0 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) bgb_6_64) bgb_6_96) bgb_6_128) bgb_6_160) bgb_6_192) bgb_6_224) bgb_6_256) bgb_6_288) bgb_6_320) bgb_6_352) bgb_6_384) bgb_6_416) bgb_6_448) bgb_6_480) bgb_6_512) bgb_6_544) bgb_6_576) bgb_6_608) bgb_6_640) bgb_6_672) bgb_6_704) bgb_6_736) bgb_6_768) bgb_6_800) bgb_6_832) bgb_6_864) bgb_6_896) bgb_6_928) bgb_6_960) bgb_6_992)
theorem ggb_6_1 : Interval gbAtlas 6 1024 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_1024 bgb_6_1056) bgb_6_1088) bgb_6_1120) bgb_6_1152) bgb_6_1184) bgb_6_1216) bgb_6_1248) bgb_6_1280) bgb_6_1312) bgb_6_1344) bgb_6_1376) bgb_6_1408) bgb_6_1440) bgb_6_1472) bgb_6_1504) bgb_6_1536) bgb_6_1568) bgb_6_1600) bgb_6_1632) bgb_6_1664) bgb_6_1696) bgb_6_1728) bgb_6_1760) bgb_6_1792) bgb_6_1824) bgb_6_1856) bgb_6_1888) bgb_6_1920) bgb_6_1952) bgb_6_1984) bgb_6_2016)
theorem ggb_6_2 : Interval gbAtlas 6 2048 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_2048 bgb_6_2080) bgb_6_2112) bgb_6_2144) bgb_6_2176) bgb_6_2208) bgb_6_2240) bgb_6_2272) bgb_6_2304) bgb_6_2336) bgb_6_2368) bgb_6_2400) bgb_6_2432) bgb_6_2464) bgb_6_2496) bgb_6_2528) bgb_6_2560) bgb_6_2592) bgb_6_2624) bgb_6_2656) bgb_6_2688) bgb_6_2720) bgb_6_2752) bgb_6_2784) bgb_6_2816) bgb_6_2848) bgb_6_2880) bgb_6_2912) bgb_6_2944) bgb_6_2976) bgb_6_3008) bgb_6_3040)
theorem ggb_6_3 : Interval gbAtlas 6 3072 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_3072 bgb_6_3104) bgb_6_3136) bgb_6_3168) bgb_6_3200) bgb_6_3232) bgb_6_3264) bgb_6_3296) bgb_6_3328) bgb_6_3360) bgb_6_3392) bgb_6_3424) bgb_6_3456) bgb_6_3488) bgb_6_3520) bgb_6_3552) bgb_6_3584) bgb_6_3616) bgb_6_3648) bgb_6_3680) bgb_6_3712) bgb_6_3744) bgb_6_3776) bgb_6_3808) bgb_6_3840) bgb_6_3872) bgb_6_3904) bgb_6_3936) bgb_6_3968) bgb_6_4000) bgb_6_4032) bgb_6_4064)
theorem ggb_6_4 : Interval gbAtlas 6 4096 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_4096 bgb_6_4128) bgb_6_4160) bgb_6_4192) bgb_6_4224) bgb_6_4256) bgb_6_4288) bgb_6_4320) bgb_6_4352) bgb_6_4384) bgb_6_4416) bgb_6_4448) bgb_6_4480) bgb_6_4512) bgb_6_4544) bgb_6_4576) bgb_6_4608) bgb_6_4640) bgb_6_4672) bgb_6_4704) bgb_6_4736) bgb_6_4768) bgb_6_4800) bgb_6_4832) bgb_6_4864) bgb_6_4896) bgb_6_4928) bgb_6_4960) bgb_6_4992) bgb_6_5024) bgb_6_5056) bgb_6_5088)
theorem ggb_6_5 : Interval gbAtlas 6 5120 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_5120 bgb_6_5152) bgb_6_5184) bgb_6_5216) bgb_6_5248) bgb_6_5280) bgb_6_5312) bgb_6_5344) bgb_6_5376) bgb_6_5408) bgb_6_5440) bgb_6_5472) bgb_6_5504) bgb_6_5536) bgb_6_5568) bgb_6_5600) bgb_6_5632) bgb_6_5664) bgb_6_5696) bgb_6_5728) bgb_6_5760) bgb_6_5792) bgb_6_5824) bgb_6_5856) bgb_6_5888) bgb_6_5920) bgb_6_5952) bgb_6_5984) bgb_6_6016) bgb_6_6048) bgb_6_6080) bgb_6_6112)
theorem ggb_6_6 : Interval gbAtlas 6 6144 124 := (concat (concat (concat bgb_6_6144 bgb_6_6176) bgb_6_6208) bgb_6_6240)
theorem allgb_6 : Interval gbAtlas 6 0 6268 := (concat (concat (concat (concat (concat (concat ggb_6_0 ggb_6_1) ggb_6_2) ggb_6_3) ggb_6_4) ggb_6_5) ggb_6_6)
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
theorem bgb_7_2016 : Interval gbAtlas 7 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2048 : Interval gbAtlas 7 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2080 : Interval gbAtlas 7 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2112 : Interval gbAtlas 7 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2144 : Interval gbAtlas 7 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2176 : Interval gbAtlas 7 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2208 : Interval gbAtlas 7 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2240 : Interval gbAtlas 7 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2272 : Interval gbAtlas 7 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2304 : Interval gbAtlas 7 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2336 : Interval gbAtlas 7 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2368 : Interval gbAtlas 7 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2400 : Interval gbAtlas 7 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2432 : Interval gbAtlas 7 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2464 : Interval gbAtlas 7 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2496 : Interval gbAtlas 7 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2528 : Interval gbAtlas 7 2528 31 := block_range (n:=31) (by decide +kernel)
theorem ggb_7_0 : Interval gbAtlas 7 0 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) bgb_7_64) bgb_7_96) bgb_7_128) bgb_7_160) bgb_7_192) bgb_7_224) bgb_7_256) bgb_7_288) bgb_7_320) bgb_7_352) bgb_7_384) bgb_7_416) bgb_7_448) bgb_7_480) bgb_7_512) bgb_7_544) bgb_7_576) bgb_7_608) bgb_7_640) bgb_7_672) bgb_7_704) bgb_7_736) bgb_7_768) bgb_7_800) bgb_7_832) bgb_7_864) bgb_7_896) bgb_7_928) bgb_7_960) bgb_7_992)
theorem ggb_7_1 : Interval gbAtlas 7 1024 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_7_1024 bgb_7_1056) bgb_7_1088) bgb_7_1120) bgb_7_1152) bgb_7_1184) bgb_7_1216) bgb_7_1248) bgb_7_1280) bgb_7_1312) bgb_7_1344) bgb_7_1376) bgb_7_1408) bgb_7_1440) bgb_7_1472) bgb_7_1504) bgb_7_1536) bgb_7_1568) bgb_7_1600) bgb_7_1632) bgb_7_1664) bgb_7_1696) bgb_7_1728) bgb_7_1760) bgb_7_1792) bgb_7_1824) bgb_7_1856) bgb_7_1888) bgb_7_1920) bgb_7_1952) bgb_7_1984) bgb_7_2016)
theorem ggb_7_2 : Interval gbAtlas 7 2048 511 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_7_2048 bgb_7_2080) bgb_7_2112) bgb_7_2144) bgb_7_2176) bgb_7_2208) bgb_7_2240) bgb_7_2272) bgb_7_2304) bgb_7_2336) bgb_7_2368) bgb_7_2400) bgb_7_2432) bgb_7_2464) bgb_7_2496) bgb_7_2528)
theorem allgb_7 : Interval gbAtlas 7 0 2559 := (concat (concat ggb_7_0 ggb_7_1) ggb_7_2)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 28, 60)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 56, 60),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeac8eec8eac0feeaeac8eec8eac0feeaeac8eec8eac0feeaeac8eec8eac0feeaeac8eec8eac0feeaeac8eec8eac0feeaeac8eec8eac0feeaeac8eec8eac0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808392 * 2 ^ 32 + 4006144704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40057.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,2]⟩,⟨.and,[0,3]⟩,⟨.or,[0,3]⟩,⟨.and,[6,5]⟩,⟨.or,[1,9]⟩,⟨.or,[2,9]⟩,⟨.and,[1,11]⟩,⟨.or,[7,12]⟩,⟨.and,[10,8]⟩,⟨.and,[14,4]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4006144704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4006144704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40057

open PEqualNP.Outside.L_meta_40057 in
theorem PEqualNP.Outside.L_meta_40057 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4006144704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4006144704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)