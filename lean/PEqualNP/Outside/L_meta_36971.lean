import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36971.Model
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


end PEqualNP.Outside.L_meta_36971.Model

namespace PEqualNP.Outside.L_meta_36971
open PEqualNP.Outside.L_meta_36971.Model
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

def SBf (j : Nat) : Nat := [6, 5, 7, 6, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36971

namespace PEqualNP.Outside.L_meta_36971
open PEqualNP.Outside.L_meta_36971.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x400025a809184a031c800c7be42bc42de32dc32bf41bd41de31dc31be40bc40df30dd30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1180c400940418c420ca58a4a0ce14141a7294632e5290298a4985514530
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
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (208+((h/4+packedAt s0K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s0K3 (197+((h/2+packedAt s0K3 (189+(h % 2)*4) 4) % 10)*4) 4
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
end PEqualNP.Outside.L_meta_36971
namespace PEqualNP.Outside.L_meta_36971
open PEqualNP.Outside.L_meta_36971.Model
def s1K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2280180010000080b7996c32dc43b0877906d20
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x4c004000a641cca390e218c43482910520
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*4) 4
  | 3 => packedAt s1K3 (i*15) 15
  | 2 => packedAt s1K2 (i*26) 26
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (5+((h/1+packedAt s1K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s1K3 (98+((h/2+packedAt s1K3 (90+(h % 2)*4) 4) % 14)*4) 4
  | 2 => packedAt s1K2 (108+((h/1+packedAt s1K2 (104+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 2 => 0xffffffffffffffffffffffebfc79ffe387fe4f
  | 3 => 0x72ff81cffc070f8c
  | 4 => 0x7cfffe0ffff80ff0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa018100104912095
  | 2 => 0x142322862122c64a
  | 3 => 0xd49751b48546b8c
  | 4 => 0x38241ac92608d60
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 29 s1Pos s1Neg, 0xfaaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0faaaa0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36971
namespace PEqualNP.Outside.L_meta_36971
open PEqualNP.Outside.L_meta_36971.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xd5a11612148402a0aa1397404401c2a4d20e3c9800200500161e1c00b006401d004062934ac31f44004a31000c010694d910034c00032c1004051002ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1e6a1f5d353a00000009583600006b2500005b5701506d32521628722a3c2e003138001b0000003f5a00006f00000000482200240d111274734254684e5c5f5600411a170047004d002d646c000f003753133b676000614b5e2f55270b14304a003e0c4446000e7066080019000321062951591d0043200a004c2c3400404900006e33150002071c7100392300000005003d004f0000000000004500266500002b046269001810006300000080808380018400008085808080800080028103818000040382018180820000810480800002db94a43b6a9487765190eeaa321ddd4542ba28a85ad4210a7ca9994f55332bb28e657551ccadca5a0db54b419f28c836f52506d8a4a0d794c41aea98839e531073aa620cf94441db288833e54cc67aa998db94b31b6a9663b4418c67ea898cf15131b7a92636c524c7688298ded4131bc282633e54c867aa990ed10721b728c43ae41887588310cfd51219e2a2435e53086baa610ed10421e729843cd53086dca210f994421f3a0843ae41087588210f910421d220843e631087ca6210d794f40aea9e815f53502b8a6a05bd4940b6292817751502e8a2a05b94840b6a90819e418c33883187388630e610c615e508c27ca8184f55030b7290616d520c2eca2185d54430cf2a0619d540c39ca4187354830eb28861d5510c33c82186710430e710861cc210c2bca0187694030af29e415d53c827ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca7885754f10ec186213e548427aa9085b94a10b6a9421b441843c843084fd51109e2a2215f53442b8a6885bd4910b629221b441043c84208760c010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x308b8661c00090008a4a201e58002000000098000002ca1400e4000046aa0402001c6000a91854210b245210531cc104504c7155310421a998641086c56310421e198c41087856310421e194c41087855310421a919131086e0604c4219918552103844108630c5551510c345525443087594410c24d6508430e1104210c2346155020c994841843265408610e410430043c0210c010
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x65000000a0aeb3188210c857694c4108682ba88210861815944108430
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => packedAt s2K5 (826+((h/15+packedAt s2K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s2K4 (3471+((h/39+packedAt s2K4 (3159+(h % 39)*8) 8) % 170)*8) 8
  | 3 => packedAt s2K3 (960+((h/8+packedAt s2K3 (912+(h % 8)*6) 6) % 40)*6) 6
  | 2 => packedAt s2K2 (200+((h/1+packedAt s2K2 (196+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xff01ffffffffffe07ffffe03fffffffe3f1fff
  | 1 => 0x7ffffff01fc07fff83e07fffff03e03fc9fe67
  | 3 => 0x7ffe07ffe0007ffffc007ffc1ffc003ff1e387
  | 4 => 0x800007ffffff81ffffff80001fffffc1fe03f8
  | 5 => 0xfffff800000001ffffffffffe0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x14c11124488104014a49641234429a2130cab
  | 1 => 0x2a146221c912a4a581682a964d234294c87665
  | 3 => 0x4c28b54483ab496aac144d5916e9053971a386
  | 4 => 0x68b1468912320db34a59019218b39611ec0350
  | 5 => 0x70c1870e1c3c71dc739e71e380c21821bfd800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaacc88aaaa8800eeaacc88aaaa8800eeaacc88aaaa8800eeaacc88aaaa8800eeaacc88aaaa8800eeaacc88aaaa8800eeaacc88aaaa8800eeaacc88aaaa8800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36971
namespace PEqualNP.Outside.L_meta_36971
open PEqualNP.Outside.L_meta_36971.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x6485674080a0000419400283bf43bd43bf42bd42df32dd32be41bc41be40bc40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xd004009a28a851d531066ca3205354830
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
  | 4 => packedAt s3K4 (208+((h/4+packedAt s3K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s3K3 (111+((h/1+packedAt s3K3 (108+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 1 => 0xc1fffc0f83ff87f0f83fe1ffe1e07fc1a67d9c
  | 2 => 0xfe1ffff003ffffff003ffe1ffe007fffc78e1f
  | 4 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x840088a200808002284c02240229109408b0b1
  | 1 => 0x9449186425240a505a15214d21432584a25594
  | 2 => 0x89221014a4844a50422541254044a29450a0a
  | 4 => 0x295c4249606d57399683111b99960309f00f40
  | 5 => 0x3198738e738e67cee73b998311180c31ffe000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36971
namespace PEqualNP.Outside.L_meta_36971
open PEqualNP.Outside.L_meta_36971.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x260120000000000679789586c38628140255498f8f00580110000000005402700b870000a440240840042000000342d1970200000567001900000004460ead000000d000000a0000928000000c000400480020000c04180010600000ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41be41fd41fc41bc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x4617c548c2faa71877d0e30ee21c617e528c2faa5186fd0a30dea1461df328c3ba65185f94630bea8c61be418c3788318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c37c82986f10530ef18a61dc314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830bea9061bf420c37a841877cc830ee990617e510c2faa2186f90430de20861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20dfa1641bd42c83be6590774cb20bf28e417d51c837c83906f10720ef18e41dc31c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5106fd0a20dea1441df32883ba65105f94620bea8c41be41883788310778c620ee18c41ee21883d843105f94220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c534837e84906f50920ef99241dd32482fea2905f14520df20a41bc41483bc6290770c520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4106fd0820dea1041df32083ba64105f94420fb288417651082faa2107d54420baa8841be41083788210778c420ee18841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43be6588774cb10df20e21bc41c43bc6388770c710fb10e21f521c43f641887e08310bfaa4217e548437ca9084f95210beaa421bd548427aa9085f15210bfa9c217e53843bca7085794e10bea9c21dd53842baa7085f14e10bfa94217e52842faa5085f14a10dfa1421bd42843be6508774ca10bea8c21be41843788308778c610ee18c217e50843f441087e48210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea68877d4d10afa9a217e53442faa6885f14d10ee29a215c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c524437e84886f50910ef99221dd324437c82886f10510ef18a21dc31443ec42887d48510fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810dfa1021bd42043be6408774c810bf28821be41043788208778c410ee188217e50043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xc508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498df14931dfa1263bd424c7be6498f74c931df20a63bc414c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618f7d0c31ef21863dd430c7b88618df94831bea9063bf420c77a8418f7cc831ef19063dd320c7b86418df94431df20863bc410c7be6218fd8c431ee98863f5310c6fca018df54031efaa063de540c7baa818f715031efa9063de520c7baa418d754831ee29063df420c73e8418f790831eea10639d420c7b88418f794431af28863d6510c7be8218f790431cf20863dd410c7b88218e710431efa8063de500c7baa018f714031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21dfa1643bd42c87be6590f74cb21df20e43bc41c87bc6390f70c721bf286437d50c86fea910efd52219faa4437e54886faa910df15221de2a4433c54886fea710f7d4e21afa9c437e53886faa710df14e21ee29c435c53886faa510efd0a21dea1443df32887ba6510df94621df20c43bc41887bc6310f70c621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21dfa1243bd42487be6490f74c921df20a43bc41487bc6290f70c521fb90a43ee21486fea090fed4121bda82437c50487f0a090de14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043bf420877a8410f7cc821ee990437e510877c8210ef10421ef18843dc31087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40ef99681dd32d02fca3a05f54740df20e81bc41d03bc63a0770c740beaa4817e53902faa7206f90e40de21c817e52902faa5206fd0a40dea1481df32903ba65205f94640bea8c81be41903788320778c640ee18c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037e84a06f50940ef99281dd32502fea2a05f14540df20a81bc41503bc62a0770c540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840bea9081bf421037a842077cc840ee990817e51102faa2206f90440de20881de31103b862205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30dfa1661bd42cc3be6598774cb30bf28e617d51cc37c83986f10730ef18e61dc31cc2fea9185f95230beaa
  | 2 => 0xafaa6217754c42aea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccbbe87997790f32eea1e65dc43ccb7e85996f50b32bf28e657d51ccafca1995f54332efaa665de54ccbbaa9997715332efa16659f42ccbbc85997750b32cea1665dc42ccbbea3997794732af28e65dd51ccbb8a39977d4332ef28665dd50ccbb8a1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32aea9c657e528cb7e85196f50a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbe86997790d32eea1a65dc434cb7e84996f50932f799265de324cafea2995f14532bfa82657c504cbbea8997795132eeaa265dc544cbbea49973d4932efa12659f424cbbc84997750932cea1265dc424cbbea2997794532eea8a65dc514cab8a29977d4132ef28265dd504cbb8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32af298657e520cb7e84196f50832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d06fca5a0df54b41dfa1683bd42d07be65a0f74cb41bf286837d50d06faa920df94e41bea9c83bf439077c8720ef50e41de21c837e52906faa520efd0a41df21483bd42907788520f7cca41ee994837e519077e8320fdd0641bf284837d509077ea720ef94e41dea9c83bc539077ea520ef94a41dea94833d5290778a520efcca41cf99483be329077a6520e74ca41de194833e519077ea120ef94241dea8483bc50906fea6a0f7d4d41afa9a837c53507b8a6a0d714d41bfa92837c525077e84a0ef50941ef99283dd32507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077c8620ef50c41de218837e52106faa420efd0841df21083bd42107788420f7cc841ee990837e511077e8220fd90441dea0883f541106fca020df54041dfa9883be531077aa620ef14c41dfa9083be521077aa420cf54841de29083bf321073e6420ef8c841de990839d32107786420ef944419f28883b6511077ea020ef94041dea8083bc50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc6fca598df54b31dfa1663bd42cc7be6598f74cb31df20e63bc41cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63df438c7bc8718f750e31ee21c637e528c6faa518efd0a31dea1463df328c7bc6518f74ca31ee194637e518c77c8318ef10631ef98c63f7318c6fca118df54231efaa463de548c7baa918f715231efa9463de528c7baa518d754a31ee29463df428c73e8518f790a31eea14639d428c7b88518d794631efa0c63de418c73c8318f750631ee20c639c418c7bea118f794231eea8463d
  | 3 => 0xe0c6307000e5df9079000cd8f60003b6ec9a394c000fdc2d0103ce0011780944e000000000009140034c596d854f3b360a3bcd41b9240a50e30ff678b29692147e69a59fb5f68259130bb7742b7d8b9901c0895960c47cad8151800374cf8ea09b78e5692133110222826997000ca593b5159a9f05d1355488ad730c05380bd8eb1621c000ff8000f05156d3a8000e811a97a434ea81180000000000144000001a20000000012d80071c0fc000b8610d6c0008d000abc00000000bbd331e81a4000000000000000141480000e00c0080301601c0080301a0000000000e0000000700800c0000801e0000100400400002007008008008010040380000b00a01001002000018008000280000180100400c030020040040280b00001005808000050028010060340180e002000030110000000000301a0180100000200000000000010030090080000200100000c0000000c0280000f0000080080000600400009002018038020040140f01a0040040700f00400401804000008038060040400e0000220180080901a004048000000000000000e0240100402a0000000200000000003000010140000020000000900602001802000004098290080300200b00c000040080020000000004a00800000006014020010000080081000003c0100200600c0080800e0000280500c00403800000004008000000040200301a0080600500001c03000000000030000020080180200000401002000010000030000040000202a000028000000280780e0000340000400202c0000000000c00001012000008020000d4008000000080300100e0000080800200c008030180180c8000020000180100000c000010060280380602a00802005000008010020040280f80b0240040000100a00803020006004000020000040280500403c00df94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f90f42dea1e85bc43d0afca3a15f54742bf286857d50d0b7ea7a16f94f42dea9e85bc53d0b7ea3a16f947429f28e85bd51d0b78a3a16fd4342df28685bd50d0b78a1a15f552429eaa4857e5390bbca7215794e42bea9c85dd5390abaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85be4350b7a86a16f10d42f7a1285be4250afea2a15f14542bfa82857c5050b7ea6a16f94d42dea9a85bc5350b7ea4a16bd4942dfa8a85be5150b7aa2a16f145429e28a85bf5050b7ca0a16f54142de282857e5410a7ca8215f94c42ef298855e531
  | 4 => 0xe43141bf10004892cbdd26ce057c940690d18c4000000000e0800160000698001aa000000000002100000058600000000000408000000000005794601ebd0002e7000c18000000002f50c32a20cc90e58000fe001ec27e1ecb101294a7a2905218000641b51881b4741d5d11c2738615548000e4280000000000000025c7a8000918eb126a11f20b3000ee800000000001780007987d4003d35fa000e9800000a59d480033a000000001908fc001e2208900818ec4b0858be20533875499b683fa65472281256f6832247000628000bf7ecb65da178000ac96a3bf61a0003b80024a00000000000730ecb320000016636c0000015081963e3a0c310874ab6c55800794d74b18fd00042914b8d7bc8a8b5ac7592fc116815642069c01af5568c071a4d34a0000027661c0008f84b06c09863b25380f3d10bec4e87403e901000c28dc1104ae060d8beb11e0009f2be6da7608d80019e001740f71e2b554bbc90be1494d0885ee3091b1990943c8170000f80009b8003349808bb6f4ca4a8a885e194854c0876068000000226b8c10e7bc3000c6c000000000000029f304cbc349570007d8000543282555d27a000000fa21c000928000971f02480006264c000c38002f6d992a9e6000000908550001f9039bc120c2dca800056d51278613ba59894ad6696c449d0ea582f9c0018f762f71010003ae739c633b000318bfab6000790000000ca2080000034e548aa2125ba000000000007bc003c455a000000004d6435a800029a00000160000951902090004bdbe37a000019b98000000900033914a87c4e00a098aa1e308b6c8c40003b049671c782a25d80000026f000c08d100063400000213000001aa8000000000013b1120000029d00051d1e20300056c6b0004eea340026c3009180000008e7b80000000037de000000028d3ea0f178001459df50c10c000004dc0015980000094000159000000370335d270c0003e2e28105ba7f2aa558001624f00000000000000000270000498000d70007c1ac95333e5b4000570008b0000007dc001bf8580e6000162bf5dcb140002136c5d45b1ea13eda91997407a1182e1e1000414000003480018998436e3a568a91018e697f1ae23c7a4c4be0000ed5572f6600fbc001c87463e4013496507dcf88171e60e9eb983000145c2107092dc9313305700008586f000dd40018d04ea1c463ac5a001d1c000158eed6c29351250db4bf4572001533b63f6a017c34a0063f1998ed75c910dd887432710000000000000000000000000066000000002b400000000000674000000000000010400074e6d1d324e000324000a23d6f2c003d62d816d2480035800110000000d3c0022218600195896000830e91a05ea0000039d000000001730284b8431120004c4000007302b5c8ad7638a148a11c2cef6c960e65627
  | 5 => 0x1bf4145d80000043c000002510002c8001910003880000020039c003cd000c891e80016a0000000029e001a70980005b9c9a9837c0000021d22a4f5059a10000004192421edc4af2f25903458c394000f3800000000f415aa3213c969fab52000159a2b7e5d4074668007da0dc38961292c78069cd70c845708fb576a489f87469a6adb3a006fa4e09394806a7687f3420d6725600f4346cf4000001680012b38729c000be800000000003740008f970000336c8c0036300000181800000000ae0000000ec003e95dae6d41063264f080e2a52eedac003880907e8098040008ed0b8003f8f21470000000015e97200032c4282815c001f328c000000000000003680000000038507390000374000001221e800000000be80f00005a9d400000000000942342963513c800000cb400389000a9c000a7000464000000001ed8a85d000931391b05c8001c291d000000000160000000017077c648059bd000fa80036e0d8000b500033097c002cf6b40000037b19c000000425e60a40fafb1f45e5788000b20e45f1346ca86c6c3775b8ab04a1fe0007c8b40005f80014a8005a6049f1860000285e2996002001cf808000000280003f20001e0000d0b8dcc8000000001000038a1c1319a93b83b8001ed5145080013c520001de8004e6000003bc4bcf544d334000af1c789956e364d98cc61837108378670504681e30003140000009c9a9e08302cae0888b09000f64550b96ae0140008e000000c5b0f000000000000005a422000000000000000001000000059c000588000000000000000088c001aa2a0e288d10951e9a1a0000000000ef000000a6d9a8801487cd033015fee492932e000458d906a7a4b94003e8000305ab000000000540a9706000003797488359b80000000022a9909e000000004da9c40037000067800319272000af800326891dc2a0000a20e882a450d78000006a68dd00b76000000000000002ec1c2480005f98a2c634c14d6f00044c000002640009ecf280e13a759d69585608e4003622ba63800000000461ac3b9624045611ca756bad298f52606d472800000001ef9e0000fe03380072c29933ae21b6aa86f12d7c26b4b7b432269751739e716105f103175
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x121c42f16108310f888420c425e63d52109758f548423d62952108fd89548425e63152109758c548423e64d4e108f593538431e5494e10c7552538425d6294e10c7951538431d5454e1097d89538423e6414e108f590538423e64d4a108f593528425e63d4a109758f528423e6494a108f592528425e6394a109758e528423e6414a108f590528425e6314a109758c528423f65d0a108f597428431e53d0a10c754f428423f6550a108f595428431e5350a10c754d42842b46150a1097d97328425d65cca10c7953328431d54cca1097d95328425d654ca10c7951328431d544ca10b5185328431e5390610c754e418431e5310610c754c418431e548c610c7552318431e540c610c7550318423d62d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f588544423e61151108f184544431f54d4d10c7153534425d62d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d1097588534425e6114d1097184534432f54d4910cb153524434f53d4910d314f524432f64d4910cb193524434f63d4910d318f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109ed81524423e64149108f590524425e63149109758c524426e6514910cbd50524432c5414910d3d4c524434c5314910cb990524432d6414910d398c524434d6314910d9584524436960149108f997424423c65d0910c7d4f424431c53d0910cbd4b424432c52d09108f995424423c6550910c7d4d424431c5350910cbd49424432c525091097997324425c65cc910c7d53324431c54cc910d3d4b324434c52cc91097995324425c654c910c7d51324431c544c910d3d49324434c524c9108f996414431f5390510c714e414432f5290510cb14a414423e6510510c7d4c414431c5310510cbd48414432c521051097996314431f548c510c7152314434f528c510d314a314425e650c510c7d50314431c540c510d3d48314434c520c510e5104314436452885109d195214427a6588110da14a20443e221881109e19520443685248110da14b104425f63550109718d540425e63150109758c540426e62150109b588540423f6454c108f191530423e6414c108f590530426e6214c109b588530423e64948108f592520425e63948109758e520423e64148108f590520425e63148109758c520427661148109e980520432e5250810cb54942042b46150810d3949320434d524c810b5185320423e64940108f592500425e63940109758e500427965c80109e59420042f161080109e596100427765440109ed9510042e86244010ec10510043d03144010
  | 1 => 0xc356510c430b6580310c31d54cc03097d95300c29c644c030c7551300c27b654c0309798f54c825d63d53208f98654c823c61553209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f209798653c831e5454f20c755153c825c6154f208f99053c823d6414f20c794f42c831d53d0b20c794d42c831d5350b20c795332c831d54ccb20c795132c831d544cb208fd9151c823c645472097d8d51c825c63547208fd9641c823d6590720c794e41c831d53907208fd9441c823d6510720c794c41c831d5310720ab58841c825f658c7209759631c831e548c720c755231c825f650c7209759431c831e540c720c755031c82cd620c72097d8d548825c63552209798c548825d63152208fd91538823c6454e208f990538823d6414e20e3509328823f64546208f191518825f63546209718d51882e9600862097d8d544825c63551209dd85544827461551209798c544825d63151208fd91534823c6454d209dd8553482746154d208f990534823d6414d208f993514823d64d45209798f514825d63d4520ab58841483375110520cd14441482cd620c520d5d443148354510c5209798f540825d63d50209d987540827561d50208f596540823e61950208fd89540823d62550208f185540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530825e6194c20c7951530831d5454c2097d89530825d6254c2097185530823e6414c208f590530825e6314c209d98453082756114c208f992520823d64948209798e520825d63948208f597420831e53d0820c754f420823f6550820c794d420831d535082097597320831e54cc820c7553320825f654c820c7951320831d544c820e350932083365494420cd55251083565394420d554e51083376494420cd19251083576394420d518e51083374294420cd50a51083573294420d54ca510823f64544208f191510825f63544209718d51083365454420cd55151083565354420d554d51083376454420cd19151083576354420d518d51083374254420cd50951083573254420d54c9510837060544208fd96410823d6590420c794e410831d5390420cd946410833551904208fd94410823d6510420c794c410831d5310420cd9444108335511042097d96310825d658c420c7952310831d548c420d59463108355518c42097d94310825d650c420c7950310831d540c420d59443108355510c420d9546210837151880209bd95200827b6548020ea50920083c93248020dc545200825e63d53109758f54c425e63953109758e54c423e64d4f108f59353c423e6494f108f59253c423e6494b108f59252c425e6394b109758e52c423e6414b108f59052c425e6314b109758c52c4394410c710bc18
  | 2 => 0x658c421c7952310871d548c421b358a310865f650c42197594310871e540c421c755031086cd620c421e5104310866f6548421ba18121086776548421ce95250087395494021d694e50087595394021ced0a50087394294021d6cca50087593294021ce90650087384194021d68c650087583194021ce95150087395454021d694d50087595354021ced0950087394254021d6cc950087593254021ce90550087384154021d68c550087583154021dc885500877121540219798e52d025d6394b40cb54b42d034e524cb40d354932d025f63547409718d51d033651107409798e529025d6394a40cb549429025f63546409718d51903365190640d59443190355510c6409758b535025e61d4d4097588535025e6114d408f997435031c53d0d40c714d435025e63149409758c525031f53d0940c714f425031f5350940c714d425032f5250940ae181425025e65cc94097197325025e654c94097195325025e63d45409758f515031f5390540c714e41503345190540ae982415031f5310540c714c415025e658c54097196315025e650c54097194315031c53901409758a531025e6194c4097d89531025c6154c408f596431031d5390c40c754c431025e63948409758e521031e53d0840c754f421032d52d0840ae583421031e5350840c754d421025f65cc84097597321025f654c84097595321025f63544409718d511031e5390440c754e411031e5310440c754c41103365110440ae580411025f658c44097596311025f650c44097594311031d53d00408fd95401029c6350040c754d401027b65500409b98854cc26d6215330c715143cc23e6494b308f59252cc32e5250b30cb54942cc34d52ccb308fd9151cc23c6454730d594431cc27661d52309d587548c31f5410e308f992528c23d6494a30d3549328c23f64546308f191518c3365110630cd544418c356518c6308f58b544c23e61d51308f992544c25f63551308f994544c31d63151308f588544c23e611513097996434c31c5490d3097195434c31c5450d308f990524c23d64149308f997424c23c65d09308f995424c23c6550930c7d53324c31c54cc930c7d51324c31c544c930d3d49324c2d8604c9308f993514c23d64d45308f996414c23c65905308f994414c23c6510530c7d52314c31c548c530d5146314c2da608c530c7d50314c31c540c530c7152304c23d65950308f58a540c23e6195030c718d540c23f62550308f185540c23e64150309798c540c25d65d0c30c7553430c25d6510c30c7550430c23e64948308f592520c23f65d08308f597420c23f65508308f595420c31e54cc830c7553320c34d52cc830b6583320c31e544c830c7551320c23f64544308f191510c23f65904308f596410c23f65104308f594410c31e548c430c7552310c31e540c430c7550310
  | 3 => 0x31a7590500c6ce6214031b3588500c75950140319798f54c865d63d53219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f21c795153c871d5454f218f99053c863d6414f21c794f42c871d53d0b21c794d42c871d5350b21c795332c871d54ccb21c795132c871d544cb21e350932c871e5390721c754e41c871e5310721c754c41c871e548c721c755231c871e540c721c755031c8794410c721cb58b548873661d52219798e548865d639522197d8d548865c6355221cb58854887366115221c7d53538871c54d4e21d358b538875661d4e218f992538863d6494e218fd91538863c6454e21c7d50538871c5414e21d358853887566114e21c7d4f428871c53d0a21ad987428871f5350a21c714d42886b46150a21c7d53328871c54cca21b5987328871f544ca21c715132886d4614ca21c7d4e418871c5390621ab58a418871f5310621c714c41886ad6210621c7d52318871c548c621b358a318871f540c621c715031886cd620c6218f992508863d64942219798e508865d63942218fd91508863c645422197d8d508865c63542218f992544865e63951219758e544867a60951219e582544865f63551219718d544867b60551219e181544863e6515121c7d53534871c54d4d218f992534863d6494d219798e534867a6094d219e582534863f6454d218f191534867b6054d219e181534865e6514d21c7d50534871c5414d218f997424871f53d0921c714f42486b661d09218f195424871f5350921c714d42486b4615092197997324871f54cc921c715332486d661cc92197195324871f544c921c7151324878d424c921b5185324863e6590521c7d4e414871c53905218f994414871f5310521c714c414865e658c521c7d52314871c548c52197994314871f540c521c7150314873b54d4121ce153504875b53d4121d614f504873b42d4121ce50b504875b32d4121d64cb504873a41d4121ce107504875a31d4121d60c7504873b5414121ce150504875b5314121d614c504873b4214121ce508504875b3214121d64c8504873a4114121ce104504875a3114121d60c4504876a21141219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c218f992520863d64948219798e520865d63948218f597420871e53d0821c754f420863f6550821c794d420871d535082197597320871e54cc821c7553320865f654c821c7951320871d544c8218fd96410863d6590421c794e410871d5390421ab58a410863f65104218f594410871e5310421c754c41086ad621042197d96310865d
  | 4 => 0x754c53106ae6214c41ab58853106b66114c41ae98053106b96014c41ad987521069e6394841a758e521069e6314841a758c52106b66114841ae98052106b96014841c754b321069e61cc8418f996321063d658c841a758e321072d528c841cb54932106b7614c841ad185321078f624c841e3949321071d524c841e3549321070d524c841e5d85321069c614c841e51853210694614c8418f994321063d650c841a798c321071f3294441c74ca51107366194441e5cca51107953294441a7d8d501069c6354041a798c501069d6314041ab98850106ad6214041ce540501063d62953318fd8954cc63e6494b318f59252cc63f65d0b318f59742cc63f6550b318f59542cc6b46150b31c795332cc71d54ccb31d354b32cc71e544cb31c755132cc67a60d52319e583548c71e5450e31c7d50438c63e6494a318f592528c69e648ca31a7592328c74d524ca31a7990328c69d640ca31a7993318c69d64cc6318f992508c63d6494231b5987548c6da60d5231b6583548c71f5495231b5984548c6d661d4a31a7992528c69d6494a31a7990528c69d6414a31b5984528c6da6014a31b6580528c71d52d0a31a7987428c65e6590a3197596428c78f6250a31c7549428c69c6150a3197994428c65d6510a31a758a418c71d5290631a7588418c71d5210631e5984418c69e64d4231a7593508c69e6494231a7592508c75b50942318f58b544c63e64951319758e544c65f63551318f994544c63d62151318f990524c63d64149318f997424c63c65d09318f995424c63c655093197997324c71f54cc931c7153324c71f544c931c7151324c74f524c9318f996414c63e6510531c7d52314c71c548c5319b988540c66d62150319e980540c67960150318f992530c63d6494c3197596430c71c5450c3197594430c71d5410c318f992520c63d6494831cb949420c72d5250831ad185420c74d52cc83197596320c69e648c831a7592320c69e640c831a7590320c69e64cc431a7593310c65f654c431a7d91310c69c644c4319dd95310c63f64540318f191500c6d661d5031c7550540c6ce6215031b3588540c6d66115031b6980540c6d96015031b5987520c69e6494831a7592520c69e6414831a7590520c6d66114831b6980520c6d96014831c754b420c69e61d083197996420c65d6590831a7592420c74d5290831d3549420c6d76150831b5185420c78f6250831e3949420c71d5250831e3549420c70d5250831e5d85420c69c6150831e5185420c694615083197994420c65d6510831a7990420c71f4294431c750a510c7566194431e5d0a510c795429443197597410c69d6290431c754a410c69e6190431c7946410c796519043197d95410c69d6210431c7548410c69e6110431e5984410c71e5110431e5944410c69f6454031a7191500c69e6414
  | 5 => 0x5350a9e63d4542a758f5150a9f6354542a718d5150abb6054542ae1815150a9f6354142a718d5050ab76154142ad1855050a9e6314142a758c5050b395014142979865310a5c6154c42c794f4210b1d53d08428fd954210b1e5350842c754d4210a6f6550842cb9514210a5f63544429718d5110a7a60153329e58054ccb1c5450f32c755043cca3f64547328f19151cca3f64543328f19150ccacd62d5332c755054ccacd6215332b698054ccad96015332a798742ccb8f6250b32a718542cca9e64d4732a759351ccada60d4732b658351ccb1f4294732c750a51cca9f6454732a719151cca9f6454332a719150cca9e6414332a759050ccb5950143328f986548ca3c6155232c7953328cb1d54cca328fd91518ca3c64546329dd85544ca7461551329ed81544ca78605513297997434ca5c6550d32c7151434cb1d5410d32a7992324ca9d648c9328f993514ca3d64d45328f990504ca3d6414132b358a544cacf6255132b5d85544cad46155132b6d81544cad86055132c7550544cb8f52d0932a7987424ca5e6590932a7592424cb8f6250932e3d49424ca9c615093297994424ca9e6410932a7993514ca9d64d4532a7d91514ca9c6454532b6d81514cad86054532c7d08514cb1d4214532a7d91504ca9c6454132b5d85504cad46154132a7990504ca9d6414132d6540504ca5e63d50328f596540ca3e61950328f185540ca3e64150329798c540ca3e64948328f592520ca3d65d0832c794f420ca3f6550832c794d420cb1e54cc832c7553320ca5f654c832c7951320cb1d544c8329bd95320cb4e534c8328fd91510ca3c64544329758a53d065f6254f419798e52d065d6394b41c794f42d071d53d0b41cb54b42d071e5350b41c754d42d065f65ccb419759732d065f654cb419759532d06d4614cb41c794d439065e6394a419758e529069e6390a41a758e429072d5250a41a798c429069d6310a41a798f419069d63d06419798e509065d6394241ad98753906ba60d4e41ae583539071f5394e41ad98453906b661d4a41a798e529069d6394a41a798c529069d6314a41ad98452906ba6014a41ae580529071d52cca41a7987329063e658ca418f596329078f624ca41c7549329069c614ca418f994329063d650ca41a798f509069d63d4241a798e509069d6394241ced42509065d62d4d4197588535065e63149419758c525063e65d0941c7d4f425071c53d0941c7d4d425071c5350941cbd49425065e65cc94197197325065e654c94197195325071f5390541c714e415071d5310c419798e521065d6394841cb54b421063d6590841a798e421069d6390841a798c421069d6310841d3949321074d524c841b5185321069e63d0441a758f411063f6550441a7d8d411069c63504419dd95411065f63540419718d50106b661d4c41c
  | 6 => 0xe93b000049a9c19807481280000000013100008780000000021e1c21b727a00007880000016a80000000000000013880000000000004d0000000001390000001d88000008c02420b18850170440b41210ad12b8000000000000001da1da80024c9db80880014d28e1a5925800402000000000000800c02400c00003800000800c00000000002400000400404c00000800400000c00000401800000000000c00801001004000000400800000801400000c05801c00000800000000800800400800001800800001400000000000400000800000001000802800001000800002001c00400000000800800000400800c00400000000400400001001001c00000400c02800000800000400002400403000001800000000001000000000000400000000800c00800c01800000000800002c01001000000800000400400000400c00000800001400000c00401800000800400800000000800000400802400c00000400400000c00000000000000400000800400000800000800802000000c02801800401400000002c00002000400000001804801000001c00000800001000001000400800000c00400001800400401c00401000c00000004c00400000401401400401002400400000801000c01c03002400000000400000000000000000000000400000000000000403c00400000000400000800c02c00000c00400800000000000000c00c00000400000400800400800c00400400402000c00000c00000000c00403402400400400000000c02800000400000000000800000400c00400400401401400002400000000400001803400000000001801c00800000001000000000000800c00c00400400000000002000000000000000001001000400001400803401c00400002400400001400400000001000400400400000c01800400002000000c00002000000400000801000000400000400003800001c00403c01400400002400800400000800000000000401000000801000000800000804000c00000400400000001c00002001000000c00c00400400c00000400c00800c01001401000400004c01001001000803000c00000a9d6490c438fd954310e5f6550c43a7d954310f1f6550c43a7d894310e9c6150c43a71814310f1d4354843c750e5110f1d4354043c754c43d0a5f63547429718d51d0a5f63543429718d50d0aad62d4f42c754c53d0aad6214f42ae98053d0ab96014f42a798f51d0a9d63d4742ae98351d0ab960d4742a7d8d51d0a9c6354742a7d8d50d0a9c6354342a798c50d0a9d6314342ce54050d0a5e6194e42971855390b1e53d0a42c754f4290a5f63546429718d5190b1c5350d42a798e4250a9d63909429798f5150a5d63d45429798c5050a5d6314142ab58a5350aaf6254d42add855350ab46154d42aed815350ab86054d42c754c
  | 7 => 0xa9099da061c8a4e8000581580000000000d710e9cc8001f38772958001c117e980a3480016b8970518a180025f0002940a58000031df0000bb9f98000b380002700022780000009f0000040000ea0000000001cf000191a1ea7300004a9340002829c28b0a3300d00020f1f580e19208da0099018f06d8001f00001648001318000001d126414580008807b9500000000950bb0001ad80019700000008204a00000027780017a9a780003b0000000000000000000000000002128002430000000000000000000001638000e980000017200000000000022d0001fc00016f15e850a1d8001730e10000000000002459a894f0000488430d68f98418e2a7005f11c0000e404c9a300025b2240000000001d280000005c27d2150c088b19627f024973a6b99f0000000b30001420c1a5800000000014180015d95c14483f8bd13380027a9ad0000000c605e05108d01f01313006880014ca3f9481fb000000071a3a0791c59c01f30868001531ee8251a18aa25aa11800033a8f8002838000f029a93495b91a9931289e900008e000193a8b1941110002789ef0050001f7a9e00005612c87f8ae0a68000bd8000002360628000000000f90000001b20002370d30da90780018608300000007580000000001e0000000000001bb228167a5d82ba5080000b0fe80000000000000000014a8000710002350000000000000000760000000000000001aea6d0530000568cc0000000aa8001698000002200000faa9503b87791d01900017d000292a0280017a02e00000000022200000000027e80012b03e0e616189f837940000000289126a5617c8298000000f2a15a1a0d80b69260c79b6a4c09000000009899780001c00000028328600014e0001d90001cea99a6f23800000012e0000000449f48000001209aa0000a00000d380000000000000020a9130f58001028b700000000001b2579282639ca22c02b0c58001958000ad9d500010f00016e19980000b8001779240ac0001d80000000001ec8001468b01068d58000000000000000001fa0738fca080000000000000000000000990000078908000e180000000000000000001a0000000001780f610c80000000000006b80001200000012d80000000021f0269bf0001ff000259a1124800000021316fa9f231800000057800000000216000000188872a770000000000000000000001c4a2f0858798c702c8cda5688082a8c400000018b0002292070000000000000f780018800010207b1c700000000010a8000000000ea8000000000001751b880006000000019a9868000002358000000000000000001bb80006928d80016a18c00998b93200027c80000000007e80000000000027080000000000000000000000000002e8001db1df8000ca8a499129200020680000000000000000000000000005
  | 8 => 0x310000000000001a811f0000000f500003000000000000000f10d000179866a4a8000001988000000000e70000cb0ec00000015d00000000014a0000ee80000000000000c8551dc0000001bc00000000019ea6e0000000000af940a62000281a3781a8000340000751a080022b0001552168000000fc0000000000001950001040b580019d21928b8001090000001990000000001e800000000020f8229b500009225700013980000015ca1b00000000000000011180000011a00026912f9048e903da100c3858a05a530000001baa630000001c90001f682123111588e8f7000298a610000000000238000002811d380024e1f913aa511d323a8002438521a29ab80000017b8ba0dfa8825b91400024720ba7480000000000027fa36a9d1669c322484600011b0000620001180000000000000000eb9c620c9641680000000000001f080000024080027b000000000018a5900029680000023911600018f80000000000002800007d20b26980012a084127000000265a87800000000000017a2980004224116091886e20d8001010000001fe9d58a70000000898000000d417b16215e0450001a023e1cb80000000017900004022326a8000370ffa7986e8d996c9bd17d8001d206f2038b91bfa020cd07c13094c0000000000002660000001d60002790a305a8ae80002a0000000002981360810f18000700222199660de08490e25ea258998f3a4615890b8f80138000b88d0a5c91b85fa452588000000bf99c9219b496ea6c000000218089135a5e03e8001ed23d09a8000000001671aa9b809691680011e9e41c980003c08b84680d8c50001e2a1a8fb8c202fa178000000328001600000cf2518001a480000009e8290c480000000024280000016b0001a997e00000014fa8401b9b600011200009481d8001c800020480014e8c69969ea80000016100000000029a0000a7a2a9b404b0000001428001b18000000c88000000000000d90000000001dd1719dc97580028c0001139548e818529b1a20c91440002091038001f600024a00000013f00000000023014d8408be8071e180000000006b00000000000000028898580002d04c015000000010a5200022700000000000026b00000007200024b0000001380e380025a000000000000000000172a0e000000122800000000000000226826047a6d9b58000fa0000dc8f68002808ec8768e68080000980000000000000000dc00000001c9e08d194b2050160000001370bc05b89d0200df23f0838000000001ec00182c0000001d423888a000123800000043a8515b0001fe2671a700028200000021880018a00000019c08027100000000000024400018e01180029c87c9fd8001e58000000000000000000000cc80026f8000000000e090b105148800000000000000246a94a8e800000000127
  | 9 => 0x700004596899b1058ee0ef0a2a5f9080dba7609a00022625384900000015f98a8001a3909a3b88889e0000198000002a01089f88679fa8962848e30a900000000000017000009328d20d00028f00000009b04b9ff8c125500000000009c14710712912f01406996280000f8361f108f8000000000000000218000a09838001e601100000000000027683900003500000000021722e99b8480c800000000018011ca0880000029fa250b780015a0638000000941eb2448000b803d1bd8e019f8000e509b9be80000000026512001d0000828000000f20000000000000001822869101d719083200026680000000026a00015407e02097c17081fa1d1ef8000000000000000381a50230000001830000a983c9f400000c0001590001d98870000001b100000016d2688eb1818fb27d8da13e1498000001eb8000000000000000000000dd07824d000031a21000095a3e9060000000001c18f313c1f28978001f2297a919fca75a1f96c0308000001bc9af80000004ea8a0c2a729742148000000001a41a90001ed8000fe0000000258279e6a6e98ca7b80000000000000000000028580013b8001692608000000590b10001b094606c8a81871c098129120a0001e50000399220b49518a60d61f50000001f804100008f0000000001d6a2b99480006f8000002098001198000000f10fd9d48000000389430640241a12900000be159a529fb83a01480007a8ba80000011e16300000025c0001cd2019cd80011500017f25418490a0001a60000001cf8f400011498e9d192a80000000000000000000000000006106a8000939b2a7380023ca030330000e59ee0ed85c8429760fd19e06c0a106d17490f8a3a339e10e88158b61570648b51439410001b984d90d8731c7a3980a07a0000001b32228000090000000000000001caa1c0000d789180017100000000000000000000029b80000000000008c1032121108000001350670d10000001ea00000005b223a9e80000000000000000011d805800123000000000000101a478b2932a5d1cb00005d98d00013300000018d8818000001e980000016d8000e788c8000000002718ca1009829002010000000000d2a990169f189c9e780003595a800000000000000000091187a4f8000000348002040ac8010068060b984f0f48000000000000000001c68000001b382f0559ce01005400000000022c9cc25595600015395200000000005980000000023b068136861a1417f80000000000000000017691fa488ab13e80008a9568000000000000bc87f0c325015100023d85d0000e49490002288001890002930001aca340ce27809280200012980005485729d9ba1d09250001e200000013a00022080023291284714780000000012e984280000207853a2e01800013780000024027c00004e0d50d48000000
  | 10 => 0x1248001f707402884f8000000a522da218000000002750000000000000861ac0db21b82d80aa6c8002720000cf80022a0000002740000ab8000001d780000014b93f8ff000145230804860a4f0001770001b913c8ef992800065978a548001be00000000000007d80e8001e88e205028a8a20d8a9627e29712c22f8001e380000011919a10c05a03a9af2682490000c9a8c8001b00f89178369579de8ed0d00a42898650dd8cb8001dd8000000000000001de0000000001fd1e7052a0e9e000006624b8002498001c40000bf1d000000000000026180023c2648000000709b79e480000000000000021080003f0002000000002320002678000000ce80026280012d0000000000038000002601508001e316524d80013d8028002870f09a68af1658000000000b200000006a2138630000000de8a88000d200021c80000024181ea0c0002939ae09d9528001ab0000001c518980000000000000015580013d00000015f0000000001c391
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xce00b2000a001ac000307ac27cd800009668002400006a9200661600000000a0b80000003600880000186c607284c844088aa2122e8c5c0ed676483486be2c6e140000c678262842001e70da3c00d25600000000d02a52b4945e3a029e6450ac620004009c00dccc00bc98aacac4ae06408046a422d4581c8e000032a6000c9a824a90ba10544e745ab63e007e00de384ca8b020000027140002000804040010040d010a11010007090804060004001604070e030100000200a1ee4a1aa421d147150e5110f0ca9ac029e858658d5014342a28e2a98a6a15187054c5350a8c39aa0282854c1c55014142a32e02a287996195458054ccb0cb22a028665451c55410d32a30e0aa0869951471550544ca8c382a82a265451c54214532a30e8a80a09955071540504ca86b94a6a1683469c35394e41a34e7a84a120e45521853210706a9ac4298838654d6014c41928e2b1ca420e25521853210782a96c29908383548614c841e0aa430a6420e8652185321070aa90c299083a1548614c841c0aa430a6420e19635405010714b12a028083435ca544cb31a34e1aa08718d1a70d52548c68d3a6a128463435c85450c31a32e02a28618e2552185420c706aa2c42a063865516015031928e2b24a418e4552185420c782a96c2a1063835486150831e0aa430a8418e8652185420c70aa90c2a1063a15486150831c0aa430a8418e0d62548410c70cb22a028063925895014031c28a630a8510e14541853288707a9ac420c4383d51620c621c28a630a8490d0c75509324870632a8499243611c5424c921c28a830a6490e8542185324869838a8428243c25093214121aa0e2990a090e0d535884108706aa2c418843455d4410c421c2aca2086210d85721043108742b1082188434a5c84154021a92e418aa010f10410c5500870c298c0a12818614e6090540a2ce3a9882a044d72194315030ca9ac1a1081435ca53508408a8e2b2a6420619535804110286b90a8a1e61459c75410e30c30a8302649842d72194414c30c2a4c118a61459c7540c530868e2b2a841861954583320c286b94a89906186551600c430838ecaa260185147154c41c8306a9ac420e41451c5540c720c1aa8b106390705424c95108390a12a290041d04c95148020a1ae529a8508616531854284286b94a89942185950614ca10e08a420862886626588620443503108288021b01883144010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x8018a011023024e005b00815093214121d01421c53214121c05655c8410c421c0575588410c421b01821043154021d01721043154021a048154d6210720a0481551620c720a058294c6150a10a0582950614ca10
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
  | 6 => packedAt s4K6 (880+((h/16+packedAt s4K6 (768+(h % 16)*7) 7) % 90)*7) 7
  | 5 => packedAt s4K5 (31188+((h/339+packedAt s4K5 (27459+(h % 339)*11) 11) % 1477)*11) 11
  | 4 => packedAt s4K4 (56486+((h/448+packedAt s4K4 (51110+(h % 448)*12) 12) % 2362)*12) 12
  | 3 => packedAt s4K3 (5784+((h/37+packedAt s4K3 (5488+(h % 37)*8) 8) % 148)*8) 8
  | 2 => packedAt s4K2 (612+((h/3+packedAt s4K2 (600+(h % 3)*4) 4) % 16)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffff81ffff87f07ff0787ffc3ffc0fdc1f3f3
  | 1 => 0xf03fffe07fff83f83ffff83ffc1fff027e7cfc
  | 2 => 0xffc1ffff83ffffffc007ffc3ffe1ffff878f1f
  | 3 => 0x1fffffc0003fffff80003fffe0003f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x218488c51090a1014b418264c1324258c0b171
  | 1 => 0x6488114321200428150a8809440496081a54b4
  | 2 => 0x821122080a444252808454822a4128a3050a0a
  | 3 => 0xcb2dc49248756b9ce6d04623b3980c33e80fc0
  | 5 => 0xc31871c738673e738e76730231030c3f7e000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xece8ece8e8e0e8e0ece8ece8e8e0e8e0ece8ece8e8e0e8e0ece8ece8e8e0e8e0ece8ece8e8e0e8e0ece8ece8e8e0e8e0ece8ece8e8e0e8e0ece8ece8e8e0e8e0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36971
namespace PEqualNP.Outside.L_meta_36971
open PEqualNP.Outside.L_meta_36971.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xc817e52902faa5206f90a40de214817e51902faa3206fd0640dea0c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c53502fea4a05f14940dfa1281bd42502fea2a05f14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440fb288817651102faa2207d54440baa8881bf411037a82205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef18e61dc31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa518778ca30ee194617e518c3eca3185d94630bea8c61f5518c2eaa31877cc630ee98c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930ef99261dd324c2fea2985f14530ef18a61dc314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861df430c3b886185f94830bea9061de320c3b864185f94430bea8861df310c3ba62185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3905f54720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3105f94220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53483dc84907b50920bfa8a41f751482eea2905f14520fa28a417451483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2105f94020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ee63887d0c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10ef29c215e53842faa7087754e10aea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843f441087e48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec82887d50510fb98a21f431443ec42887d48510fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xe5390bbca7215794e42bea9c85dd5390abaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42df21a85bc4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332efa1e65dc43ccafca3995f54732bf286657d50ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7197790e32eea1c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132efa1a65dc434cbde6499778c932bfa8a65f7514caeea2995f14532fa28a6574514cafea0995f14132bfaa0657e540cafaa8195f15032bf29865de430cbba86195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63df438c7b88718df94a31bea9463de328c7b86518df94631fb20c63f5418c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7bc8698f750d31bfa92637c524c7be6498f74c931fb20a63f5414c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f7d0c31ee218637e520c6faa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21fb20e43f541c87ee6390fd0c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e51087ec8210fd50421fb98843f431087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d02fca5a05f54b40dfa1681bd42d02fca3a05f54740beaa4817e53902faa7206f90e40de21
  | 2 => 0x20c188002960011a9d148e608578dc1206e49716600047c0000034c96c00000174644000000f460c118b13dc478000001e86f03a00021a97c00169126000f99130000000016707e6c00000022c9f80024d0008e11286b428520000000000000000400072400000288140000000009080004503c00055000418000000002208a8000004080000000000028c001fc000000000e120c3bc000d9000000000003bc6844a8001968dc0015503e00000000000518d61a54765e0000004404481e8b222e130001500009a800000526154002292600000019d3c60013aa6800020800000182000ea80051a3a0ba2700009885a8003120003988f000885358bc00043c000003ea9cc0006449c10402a2b000330bd8000000012e800000000001f652e98cf813b160000631752941fc001b6000000a68795060dc0014000095c0000033223400000000000e18000000013a0702de0ac9e9423b0374f7800000000001081d60009111952a99d2624a3022642fa613684000028a00081c000c03409bd29921374a10cd82622a6000000000049c000000006ac0019600029000000004000000000000008200001c00012000000a442400029200000000036000d90cf0000008e0383b60013e02e06c3081106f3ee4e0e400a3cc7b4dc000000000000000000000017d0002a06d00020e5dc7fa5a37e17800000000424000000000008580008c5680017124a6b40023f1940480000000100002002000002000010000060100180002c000010020020000000000800801805014000000000000040000000001402006002000018000000000980200c00400002002000020000020180000300a00001000004000000000120100080a00000402800000020000010000100080300001c0080e0040100000200002c0100100001004007014008010000280140080200e000020080060000080300000000004006008030010000040500800600000804000000000090000080300200000400002000008028010060000680100a00004006000008028020060000080000e00002005004000020040020340180600000c000050080140780000000c018000060240081d0020000000000e0080000a004014010020000040080000000000004000004040020060200080000200000000bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf28887f65110eeca221df54443faa8887755110efca021df54043bf29e85de53d0abca7a15f54f42eea9e855d53d0b7c87a16f10f42bf28e85f651d0aeca3a15f54742faa8e857551d0afca1a15f54342beaa4857
  | 3 => 0x1683e8940a7000000da8330008691f000112000001312b60003f000000110000000002ccfa21700000000212000000000083a4000850004a0565388002e61680009f13654d3d9cd3148047c9203ba8900a1f1218a3cec9be1ca38d2c00016e00000000000000000000001b4e98004f00000000000000c000000ce000000520000c03c00000000000000000000000000000013c800096000000004609011a0f5000000002280000004600034e770c98a6000000000003380002100012c288000003ce5ac000720740000017a21c1a8298810000001f152228320002600009b11d0004b84ac799bd2bc9e85f1af00040ceb89d0c61d9471a936646c0007d02e2100e1c400000000213052000000003fe324250001cc5c00005c3ca4440c8fc01a9190c0473d28c48d2720645f800000000000508000000006b2650000014600028a9240016e1520ece000029e61c10a1d0409541c800000000e09a30008e416800034000000001dc001330002ae000001da00000000000204000702903c486d348cd2f869030000000000000003983f4b005715aa50e389a0d80000012300000000000000000000000002b94424f0001740009145a100c28011703549925900082c9f800414000ae1393203906ba5419c7f5220000008449e0000000000024b0005e52b0062ac188b2a10000001070003d0000978713e4000aa0691ee378a8818000000000001d489c7d8000006dc3e02700000144935384000ca18b18e000000a039c0009216c0ee000af8002300014921540a000000150000004299740c3c8001e1000000000002ec150128fe00000000000258000000003d4a1cd500047a000a08e93500000014e03a3602c8003c07b0000ab3f40013b0160000000000048a000000000000000013e000820bfa2f1b68640018e13c0a8340df0000000000000004c000f809c03c00137128000000001a42e496a48000634000002d077c038000000000000000088d3b947396728000001a62ec0000026c0b0089ae4c8000000000005a80498f0209fd4b164186000331bb14a7e4e300012e001068280005c8ac0981163103aa1f00000000000504220c90610000000000050c824a1a1620aa2cfc03c000000e295d0009b41a8001c400000000000218628000008d8000000002005607b4bc14400000000610e78000007ec000f101800000000000001370000000005f9261a8000c30000000000000000000000000000000248002984a8000003d680cca8000000005e8003a05b4001880b039c000000002380000000000094a320000000028133c0000002f4445842b13444c3c000000000248cc2333a83d9162850009f49984d00000121a801380005b03447867d078653c8405170001d800000000114000000000000000016200021c3711d016668002411da8700000000
  | 4 => 0x16c2180036200027a512c64e9001fe31887868000000759290d1344000000000008080000000000000000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x5520c274615483097596320c29e648c83097d95310c25f654c030a7191300c27b654c0309798f54c825d63d53209798e54c825d63953209d98654c827561953208f99353c823d64d4f209dd8553c82746154f2097d8d51c825c635472097d8d548825c63552209798c548825d63152209d984548827561152209d987538827561d4e208fd91538823c6454e208f992518823d64946209798e518825d63946208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e6515120cb588544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534832c54909209b195424833754d4520cd153514835753d4520d514f51483375414520cd15051483575314520d514c514837160145209798f540825d63d50209d987540827561d50208f596540823e64150209798c540825d63150209b988540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510832d54c8020dc546200826f6548020cb551200827b6548020dc545200825e63d53109758f54c433661953109798c54c425d63153108f99353c423d64d4f10c795253c431d5494f10c795153c431d5454f10d518553c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6414b108f59052c425e6314b109758c52c43555390710cd95141c42d46350710d554d41c435553cc710ad59031c42d463487109798f548425d63d52109798c548425d63152109b988548426d62152109798f528425d63d4a108f990528423d6414a109798c528425d6314a10d594f21843565308610bc58021842f06148210d594f108425f63551109718d544426f62551109b189544425e63151109758c544423f6454d108f191534426f6254d109b189534423f64549108f191524425f63549109718d524427761549108f990524423d64149109798c524425d63149109d19541442d46350510bc181414427665cc510ad590314427665885109d19521442d463485109e19520442d6638411097d8d540425c63550109798c540425d63150109b988540426d62150109d984540427661d4c108f990530423d6414c109b988530426d6214c1097d8d520425c63548108f990520423d64148109798c520425d63148109d984520427a60148108f992510423d64944109798e510425d63944109d59721042756508410bc580210425e63940109758e500427965840109dd95100427b6544010
  | 1 => 0xc79743506319b98a544c66d629513197d8d544c65e6590d3197195434c65e65cc931b5185324c6746550531e550d414c63d6595031c718d540c63e64150319798c540c676611503197597430c71d54d0c3197594430c71d5410c31b5584430c65d658c831a7992320c71d548c831c7550320c71d54cc431cd552310c65f654c431c7551310c677654c431cd551310c65e63d53219758f54c865e63953219758e54c863e64d4f218f59353c86d46350721ad59031c863f64543218f19150c865f63543219718d50c865f63552219718d548865e63152219758c548863e6414e218f590538865e63942219758e508865e63951219758e5448675619512197d8d544865c63551219ed81544867860551219798e53486776154d2197994534875453c85219798f540865d63d50219e983540867960d50218f596540873661950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c21d5185530863e6414c218f590530865e6314c219e98053086796014c219d59641087555390421cd95141086d46350421d554d410875553cc4219d59431086b5640c4219bd9521086776548421b518d210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d50087724154021dc50550087733154021dc0c550087722154021dc485500865e6394b409758e52d025f63547409718d51d02b56110e4097d8d529025c6354a409dd8552902746154a40a798e429025e63946409758e519029c63506408f997425031c53d0940c714d425031c5390140c754e43102b56110c40d394e521034d5394840d394d521034d5354840cb90d521032c43548408f596421029e6390840cb54a421032d5210840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440c754f411032d52d0440a718d411031d5350440cb54941103365150440cb54b401023f6550040a718d401032d52500409ed95401027661153309d58454cc23e6494b308f59252cc2d4614cb30a759031cc27661d52309d587548c26e62152309b588548c27661152309d584548c2d56110e30a7992328c23e64946308f592518c3366494630cd592518c3574394630d510e518c3563294630d50ca518c35651cc630d5945318c35651cc2308f992544c25f63551309d984544c27561151308f994544c31d6315130cd984544c335611513097996434c31c5490d3097195434c31c5450d3097997324c31c54cc930c7151324c2d4614c930c7152314c25e650c530a7590314c31c540c530c7152304c2d6618c1309798c540c26e62150309b588540c27661150309d584540c25d65d0c3097594430c2d56110c309dd8
  | 2 => 0x370000772607680002e0cc000c4a19000000000002b2284c50000000e8000ad0c0000000bb0000003c8000fc244461b73aa28ca183b3de4241e1f800000000024000000df00010a0008d8002cc4700004441e0006c00029012cbb8000000003186f000000001a3000000740000004f47a8300001acc10004203d8b10000dc0647f0003c00001180021a000e804a248000be8000006b4f7000000000000000ec52c00000000000111b511a62c4a87409e21cb40521c60005a800000264cb8df000000a8165000428000003724dc8180821e440aa0411622e8fea16028414871b43827d08c9aa3a209800000000304dd9dc39a6390916c000380f39b30007acfb0f90005a400000000000421d7244078938940000000009f2800000000000001c02004030080000c000000000000020020080b00002038050080000c0000c0203401000020000100001038060140000000004030080a00406000000000c03404004020080b0041200800030080000b0000b004010100201806008030000000004000020100701002010010000a05c050040000c000400400c0101c040000001809004020000e008010080000400004030000200001004020440e0000201c0901c000340401c030040000000010080040e0101a00001004000040500003018000040301c000040300c0b0000200400008000080a00000000010080000000002776154a439d1855290e7661942439d5865090e3f6550c4397d954310f374354443d590d5110f354354443d550d5110f1d5390f42ad58443d0b565394742d554e51d0b565354742d554d51d0b1e53d0a42ad5844350a9e63909429798c5150a5d63145429798c5050a5d63141429d9845050a7561141428fd954210a6f655084297d8d5110a5c635444297d8d5010a5c63540429d98454cca756115332b558443cca7661943329d58650cca7661952329d586548cb1d6395232cd986548cb356195232c7952438cb1e5450e32c7953328ca5d63951329d986544ca7561951329dd85544ca7461551329ed81544ca78605513297997434ca5e6510d32b5584434ca9e648c9328f990514ca3d6414532cd990514cb356414532d5d0c514cb544314532d58c8514ca5e63d50329d984540ca7561150329e980540ca79601503297596430ca5f6550c328f992520ca3d649483297d95320cad4614c8329bd95320ca3f64540328f191500ca5e6394b419758e52d069d63d0b4197d8d50d065c635434197d8d529065c6354a419798e509065d6394241d5584535071c53d0d41a758f425071c53d0941ad987425071c5350941cb149425071d53d0441d554e411063f6550441c754d41106776550441d554d411063e6494b318f59252cc6d4614cb318fd9150cc63c64543319e983548c67960d5231b5584438c69e648ca31b518d418
  | 3 => 0x560004c09b3e600090a082e27483980038a054bf186374804c98a74302b8de0000703983d988022070001fa0000009902c00072c028002ac0000015c000000188002547c02d00f20e330eb00002c2f4059b10c8204472171aa548c783d400134aa90c00000000000000458478f71d4000511ea0000000014600010000000000000b38d20060000014c000000ca8542821b000000000478001af000000000000004ec4901d25c0002280004269c7a0a90a0000139730d47b4391020ba0a8678c4052418611601a806c098ab13c2ccb21762520000001019a6a0820b93061a0400002da0e4002130000007e9e23c24e8649390025c8769e8000000000d100066cc204222e5e400000000068001d80000001b00000042c00000148000000430b60000000000031c00191000184a29a000024000000000000000002f800000000352000001ae406400650e41d2658c3957330000000001b4000d200037e3cc00000000000ce9b20000000000033c19423846000444bd20a2bc6880000000000000000064000cd0000002d0001db1065109f1d40003e0000fa3ca4744401833e7009305709c00000000000000580000000007e142342000311c80b20000014d18a0000012c000000000d900e0004494a10c4b4b08000aa6c0ee8ef41a000db1cc3383acfe1f50f8000241510001245f1df0d200000000000000000170000305916b3fe469038000000940f98c3f24bc640e512c5d0ca13f1582f03d20b3e40a0000931f669845133134010de856000298000000007180015b0000005f8750000004b8d30007dc000122027a4000000b03c8a980000036c00113000338c811f18c179049ca1e0001070090be614ae8b71bc7788c0e1000480f889c14a5fc9b1e329257c00114000000001cf15e83000206000664000002dc000001c305e4ad011c4278814000003023000012338e000789081d8000288d7000000000353705600000e000028068ff39c51c770e21164d0001ac0002a000000434080c00340b84486e9700e0000000671702744114e34a1b4001c900058cff0d63d80003c1d300000000000000494e120400000000000000000989380004a05b000098000001921a00003f8000000000016f31a7641f1153f6854f20aa0004d4000000001f400000000000bc0c32b4798000000008440000000000029800000000a78cb35600073a14000000000002ea008000002d40b4bd80606e1c4198a007e0000000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x751558b00001101300500000100034000928048c0040003830004002000000000000000065c00003d8080001001820018558d6195232a2ae32a28719516748c8514ca4aba0c299263855516110c3183eecaa46418d1574185530862a3b2a6a0843541cd4154021a62e818aa010d50734855008692b8886a90818398d5290840c18c6a92822060c63549401028b3a46528c61455d2514c630c2ac6b08a89851571151434c30a2a0c299261075d8540c530c28a930c60985157418553c422a3b2a6a0e219494d6008610
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x800000340815869d23214532815869d2329463081587150614c93081587152618c130
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
  | 5 => packedAt s5K5 (20359+((h/221+packedAt s5K5 (17928+(h % 221)*11) 11) % 1164)*11) 11
  | 4 => packedAt s5K4 (22272+((h/179+packedAt s5K4 (20482+(h % 179)*10) 10) % 860)*11) 11
  | 3 => packedAt s5K3 (1273+((h/8+packedAt s5K3 (1225+(h % 8)*6) 6) % 57)*6) 6
  | 2 => packedAt s5K2 (244+((h/1+packedAt s5K2 (240+(h % 1)*4) 4) % 13)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x83ffffc0fffe1e0f0fff0ffff87fe07c39f3f3
  | 1 => 0xfc0f87ff07ffe3f00f87f1e07f8fff8226ccfc
  | 2 => 0xfff007fff87ffffff007fe007ff0ffffc70f1f
  | 3 => 0x7ffff8003fffff800007fff0003f80fe0
  | 4 => 0xfffff800000003ffffffffff80000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x88610046100420010189022318112118085171
  | 1 => 0x19224c8a3229065086c391452c8a4b0a22c4b4
  | 2 => 0x20841110415000a61004240841209460c50a0a
  | 3 => 0x72cb6624a51d4b3bab508112764c0633780fc0
  | 4 => 0x430c4438c66193cccc66c99c04081843b7a000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfaeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36971
namespace PEqualNP.Outside.L_meta_36971
open PEqualNP.Outside.L_meta_36971.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1200719000c62652856804878a1d34bd906005892c40fd5000441f2e50dc505002079778e4f8474880a5683439b4e00a9100f59a35601b0000d401c76000000001c0b6000000624c01811000800104040821400f800004a031428900017fd5005fe54017f55005fc5401ffd4c07fe5301ff54c07fc53017fd0c05fe43017f50c05fc4301ffd48077f5200ff94807fd52005f54803fc52017fd0803fe42017f50803fc42007fcc803fe32007f4c803fc3201ffd4407fe51005f94407fd5101ff144077c51017fd0405fe41017f50405fc41007fcc401fe31007f4c401fc3100ffc8401fe21007f48403fc2101ffd4007fe5001ff54007fc50017fd0005fe40017f50005fc40007fcc001fe30007f4c001fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42004ff10210027fe6108013fe3084009fe9842004ff0c210027fe4108013fe2084009fd1042004ff48210007f24108013fc2084009ff8842004fdc4210007f62108037ff654401b7fb2a2000dfd9510004feca88037fe65440077f32a200dff5951006dfaca88037fc65440077e32a200ddf1951001cf8ca88033ff64440197fb22200cff99110015fcc888033fd64440197eb22200cff19110015f8c888033ff5444019ff2a2200cff55110067f8a888003ff63440017fb1a2000ff98d10055fcc688003fd63440017eb1a2000ff18d10055f8c688037ff534401bff29a200dff54d1006ff8a688033ff4344019ff21a200cff50d10067f88688003ff62440017fb12200bff9891000dfcc488003fd62440017eb12200bff1891000df8c488037ff524401bbfa92200bff9491006ffaa4880037d5244017fe292200cffd091005ffc8488033fd4244017fe2122000ffcc91005ffc6488003fd3244017fe192200dffd451006ffca2880037e514401bfea8a200dff1451006ef8a288033ff4144019ff20a200cfd90510067fa8288033f54144019fe20a2000ffcc510007fc6288003fd3144001fe18a200bffc8510007fc4288003f62144001fe90a2000fd4851005ff84288037ff5044009ff282200dff54110027f8a088033ff4044009ff202200cff50110027f88088003ff3044009ff1822000ff4c110027f8608802fff2044009ff1022000fe88110007fa4088003f92044009fe1022000ffc4110007f62088013fe1044009fb0822004ffd9410025feca08013fe65040077f3282004ff59410045faca08013fc65040097e3282004ffd9010025fec808013fe64040057f3202004ff5901003dfac808013fc64040097e3202007ffd501003ffca80801ffd540400ffe2a02004ffd8c10025fec608013fe63040157f3182004ff58c10005fac608013fc63040097e3182008ffd4c10047fca608023fd5304011fe2982007ffd0c1003ffc860801ffd430400ffe2182004ffd8810025fec408013fe62040037f3102004ff58810005fac408013fc62040097e3102008ffd4810046fea40801bfe5204011fea902000df54810037f8a40801fff420400dff2102007ff50810037f88408003ff320400dff1902000ff4c810037f86408026fe6104011ffa882005ff9441002efca208023fd510400bfe2882005df1441003ffe8208017fe410400ffea082005ff10410007fe6208017fe3104001fe9882005ff0c410037fe4208017fe2104001fe9082005ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff4004009ff2002004ff50010027f88008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802000fe44010
  | 1 => 0xffc4148001ff98a4000ff8c520007fa6290003fc3148003ff90a4001ff8852000ffa4290007fc21480037fb024014ffd4120027fca090053fd5048009fe2824013ffd0120027fc809004ffd4048009fe2024000ffcc120027fc6090003fd3048009fe1824001ffc812000ff64090013fe2048009f71024004ff08120027d84090007f8204800bffb2e2012bfd9710097fccb8800efe65c4025feb2e2012bf5971002ff8cb8800efc65c400bffb262009bfd931004ffcc98800afe64c4013df3262002af9931004ffac988026fd64c4001deb262000af5931002ff8c98800afc64c4013ffaa62009ff9531004ffaa988027fc54c400bffb1e2000bfd8f10007fcc78802afe63c4001feb1e2000bf58f1002ff8c78802afc63c4025ffa9e2012ff94f10097faa78804bfc53c4013ffa1e2009ff90f1004ffa8788027fc43c400bffb162000bfd8b1008ffcc588006fe62c4001feb162000bf58b1002ff8c588006fc62c4025ffa962012dfd4b1008ffca58804bfd52c4001bea962011ff14b1004ffe8588047fe42c4013fea162011ff10b10007fe6588047fe32c4001fe9962011ff0cb10097fea388017fe51c400bbf28e2012ff5471002ff8a3880177c51c4013ffa0e2005ff9071004fec8388027fd41c4013faa0e2005ff10710007fe6388017fe31c4001fe98e2005ff0c71008ffe4388017fe21c4001fb10e2000ff48710007ea4388017fc21c4025ffa862004ff94310097faa188013fc50c4013ffa062004ff9031004ffa8188013fc40c4001ff9862004ff8c310007fa6188013fc30c4023ff9062004ff88310007fa4188013fc20c4009ffb2c2004bfd9610027fccb0800efe6584009bf32c20039f99610027facb08042fd6584009beb2c20009f59610027f8cb08012fc6584009ffb242004bfd9210027fcc90800afe6484009feb24200fbf59210027f8c908012fc648401fffaa4200fff9521007ffaa90803ffc5484009ffb1c2004bfd8e10027fcc70802afe6384009ef31c2000b798e10027fac708002fd6384009eeb1c2000b758e10027f8c708012fc6384021ffa9c2010ff94e10087faa708043fc538401fffa1c200fff90e1007ffa870803ffc4384009ffb142004bfd8a10027fcc508006fe6284009feb142000bf58a10027f8c508012fc6284021ffa942010dfd4a10077fca508043fd5284001bea94200eff14a1007ffe850803bfe428401ffea14200eff10a10007fe650803bfe3284001fe994200eff0ca10065fac308043ff5184021ff28c2000df94610087faa308043fc5184021be28c200fffd061007ffc830803ffd418401ffe20c2000ffcc610007fc6308003fd3184001fe18c200effc8610007fc4308003fd218401dfe10c2004bf98210027fea108013fe5084009fea842004ff14210027fe8108013fe4084009fea
  | 2 => 0x300cffea4180677f520c02fff2906019ff54830006faa41805ffc520c031ffa106017ff908300c7fa841805ffc420c015ff990600aff8c830057fa641802bfc320c009ffb086004ff98430005fcc218013fd610c0017eb086004ff184300cffea218067fe510c001bf2886019ff544300cff8a2180677c510c031ffa086018ff904300c7fa8218063fc410c015ff988600aff8c430057fa621802bfc310c02fff9086000ff88430007fa421805ffc210c0097f3006004ffd4030027fca018013fd500c009fe2806004ffd0030027fc8018013fd400c009fe2006004ffcc030027be6018013fe300c009fd1806004ff4c030027ba601802bf9300c009ff9006004ff08030027fecb10012ff6588009ff32c4003bf99620027facb1005afd6588009fe32c4004bf19620027fec910012ff6488009ff3244002bf99220027fac910056fd6488009fe3244004bf192200affea910057fe548802bfeaa44015ff15220027fec710012ff6388009ff31c400abf98e20027fac710002fd6388009fe31c4004bf18e200b7fea71005bfe538802dfea9c4016ff14e200affe8710057fe438802bfea1c4015ff10e2000dfac510007ff5288003bfa944001ff94a2000ffaa5100077d5288003fe2944001ffd0a2000ffc8510007fd4288003fe2144001ffcca2000ffc6510007fd3288003fe1944004ffd8620027fcc310002fe6188009feb0c4000bf58620027f8c31005bff518802dff28c4000df946200b7faa31005bfc518802dbe28c4015ffd06200affc8310057fd418802bfe20c4000ffcc620007fc6310003fd3188001fe18c4001ffc862000ffc4310007fd2188003fe10c4004bf98220027fea110013fe5088009fea844004ff14220027fe8110013fe4088009fea044004ff10220027fe6110013fe3088009fe9844004ff0c220027fe4110013ef2088003fd9044004ff08220027f04110053ff65480297fb2a4014ff9952001dfcca90053fd65480297eb2a4014ff1952001df8ca9004fff64480277fb224000efd91200057ec89004ffe64480057f3224013ff5912009dfac89004ffc64480057e3224013ef1912001578c89004fff5448027ff2a24013ff5512009ff8a890003ff63480017fb1a4000ff98d20055fcc690003fd63480017eb1a4000ff18d20055f8c690053ff5348029ff29a4014ff54d200a7f8a69004fff4348027ff21a4013ff50d2009ff88690012ff6248003ffa924001dfd492000ffca490007fd5248003bea924001ff1492000ffe8490007fe4248003f72124001ff5092009fda8490007fc4248003ff9924001ff8c92000ffa6490007fc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4000bf185200a7fea290053fe5148001bf28a4014ff545200a7f8a2900537c5148027ffa0a4013ff9052009ffa829004
  | 3 => 0xfb246004ff99230015fcc918013fd648c03d7eb246004ff19230025f8c91807bff548c03dff2a4601eff552300f7f8a91806efd638c03fffa9c600aff94e300fffaa71802bfc538c03dffa1c600aff90e300f7fa871802bfc438c009ffb146004ff98a3000dfcc518013fd628c0017eb146004ff18a30025f8c51807fff528c03fbfa94601dff94a300fffaa5180037d528c03bfe294601effd0a300effc851807bfd428c03bfe214600affcca300effc6518003fd328c015fe1946004ffd8630027fcc318002fe618c009feb0c6000bf58630027f8c31807fff518c03fff28c6000df946300fffaa31807ffc518c03fbe28c601effd06300f7fc831807bfd418c03dfe20c600affcc630007fc6318003fd318c015fe18c601dffc8630007fc4318003fd218c03bfe10c6004bf98230027fea118013fe508c009fea846004ff14230027fe8118013fe408c009fea046004ff10230027fe6118013df308c015fd9846004ffc8230027f84118073ff654c0397fb2a6000dfd9530004feca98073fe654c0077f32a601cff595300e5faca98073fc654c0077e32a601cdf1953001cf8ca9806fff644c0377fb226000efd91300057ec89806ffe644c0057f322601bff591300ddfac89806ffc644c0057e322601bef1913001578c89806fff544c037ff2a2601bff551300dff8a898073ff534c015ff29a601cf794d300e7faa698073dd534c015fe29a601bffd0d30057fc869806fde434c037fea1a601bf750d30057f88698003ff624c0017fb12601aff9893000dfcc498003fd624c035fe3126001bf189300e7fea4980737f524c035ff292601cff54930006faa49806bfc524c037ffa12601aff909300dffa849806bfc424c015ff9926000f7cc9300d7fc6498003fd324c001ee992600aff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c039ffa8a601cff94530006fca298073fd514c039fe28a601cdf145300dffe829806ffe414c037fea0a601bff10530057fe6298003fe314c001ef18a6000ff4c530057f86298003dc314c035ff90a6000ff88530007fa429806bfc214c039ffa826004ff941300e7faa098013fc504c037ffa026004ff901300dffa8098013fc404c015ff982600afecc130027fc6098013de304c035ff9026004ff08130027feca18012ff650c009ff3286003bf99430026fcca1800e7e650c009feb286019bf59430026faca180027d650c009fe3286004bf19430027fec818012ff640c009ff3206002bf99030027fac818062fd640c009fe3206004bf190300c7fea818063fe540c031feaa06018ff15030055fcc61802bff530c015ff298600aff54c30057f8a61802bff430c015ff218600aff50c30057f88618013ff620c009ff3106001bf98830027fac418002fd620c009fe3106004bf188
  | 4 => 0x817fe3188401fe98c4205ff0c62100ffe4310807ef2188403fb90c4205ff0862100fe84310817ff6088401ff3044204bf98221007fac110802fd608840bfe3044226ffd4221137fca11089bfd508844dfe2844225ffd022112ffc8110897fd408844bfe2044201ffc822100ff84110893ff65484497fb2a4200dfd9521004feca90893fe65484077f32a4224ff59521125faca90893fc65484077e32a4224df1952101cf8ca9088fff64484477fb224223ff99121015fcc89088ffd64484477eb224223ff19121015f8c89088fff5448447ff2a24223ff5512111ff8a890803ff63484017fb1a4200f7d8d21005bec690803fe63484157f31a4200ff58d21005fac690803fc63484157e31a4200f718d21005b8c690893ff5348449ff29a4224ff54d21127f8a69088fff4348447ff21a4223ff50d2111ff88690806ff6248403ffa924201dfd492100ffca490807fd5248403bea924201ff1492100ffe8490807fe4248403fea124201ff1092100ffe6490807fe3248403fe9924201ff0c92100dfec290893ff5148449ff28a4200df94521127faa290893fc5148449be28a4223ffd052111ffc829088ffd4148447fe20a4200ffcc521007fc6290803fd3148401fe18a4201ffc852100fee4290807fe2148401f710a4201ff0852100fd84290807f42148401ffb024200bfd8121007fcc090803fd6048401fe3024204bf18121127fea090893fe5048449fea824224ff1412111ffe809088ffe4048447fea024223ff1012100ffe4090807fc2048415ffb2e600abfd9730057fccb9800efe65cc015feb2e6022bf59730057f8cb9802afc65cc015ffb26600abfd9330057fcc99800afe64cc015feb266021bf59330057f8c99802afc64cc043ffaa66021ff9533010ffaa998087fc54cc015ffa9e600aff94f30057bca79802bfd53cc045eea9e600aff14f30057fe879802bfe43cc015ef21e600aff50f3010fba879802bfc43cc015ffb16600aff98b3000dfcc59802bfd62cc0017eb16600aff18b3000df8c59808bff52cc045bfa966020ff94b30117faa5980037d52cc041fe2966021ffd0b30107fc8598087fd42cc041fe216600affccb30057be659802bfe32cc015fe9966000f74cb30057f8659802bff61cc015ff30e6000bf98730057fac398002fd61cc015fe30e6022ffd4730117fca3980037e51cc045fea8e6022ff14730116f8a398087ff41cc043ff20e6021ff5073010ff8839802bff31cc015ff18e6000f78c730057fa639802bfc31cc015ee18e6020ffc8730007fc4398003fd21cc041fe10e6022ffd4330027fca19808bfd50cc009fe2866021ffd0330027fc8198087fd40cc009fe2066020ffc8330027f84198013ff658c0097fb2c6004ff9963001dfccb18013fd658c03f7eb2c6004ff19630025f8cb18013ff648c0097
  | 5 => 0x4d31057f8a6988b3ff434c415ff21a622cff50d31057f88698803ff624c4017fb12622bff9893100dfcc498803fd624c457fe3126201bf1893116ffea4988b77f524c457ff292622dff54931006faa4988affc524c459ffa12622bff90931167fa84988affc424c415ff9926200f7cc93115ffc6498803fd324c401ee992620aff0c93116ffea2988b7fe514c401bf28a622dff5453116ff8a2988b77c514c459ffa0a622cff90531167fa82988b3fc414c415ff98a620afdcc531007fc6298803de314c457ff90a622bff08531007fec098802ff604c401ff3026200ff58131007f8c098812fc604c45bffa82622dff9413116ffaa0988b7fc504c459ffa02622cff90131167fa80988b3fc404c457ff902622bff0813102ffeca1882aff650c415ff3286203bf99431057faca188a6fd650c40bfe328620abf1943102ffec81882aff640c415ff3206202bf990310577cc81880abe640c415feb206228bf590310577ac818802bd640c40bfe320620abf19031147fea8188a3fe540c451feaa06228ff15031055fcc61882bff530c415ff298620aff54c31057f8a61882bff430c451efa18620aff90c31057fa861882bfc430c415ee2186205ffd8831057fcc418806fe620c415feb106200bf5883102ff8c418806fc620c453ffa906229dfd483113ffca4188a7fd520c401bea906227ff14831147fe841889ffe420c451fea106227ff10831057fe641882bfe320c44fef190620aff4c831057f8641882bdc320c4557f3086229ffd443102ffca2188177e510c453fea886205ff1443102ef8a2188a3ff410c40bff2086228ff5043102ff8821882bff310c415ef9886205ff8c431057ec621882bfd310c401ee988620afd4c43113ffe4218817fc210c40bffb00620aff98031025fcc01882bfd600c4017eb006205ff1803114ffea0188a7fe500c453fea806229ff14031147fe80188a3fe400c451fea006228ff1003113ffe401889ffc200c40bffb2c4226bfd962102efecb108027f658844dff32c4203bf99621137facb1089afd658840bfe32c4203bf1962102ef8cb1080e7c658840bffb244225bfd922112ffcc91080afe648844bfeb244225bf5922102ff8c91080afc648844bffaa44225ff9522112ffaa910897fc548840bffb1c4200bfd8e21007fcc71082afe6388401feb1c4200bf58e2102ff8c71082afc638844dffa9c4226ff94e21137faa71089bfc538844bffa1c4225ff90e2112ffa8710897fc43884037eb144201ffd4a2100efea510807fe5288403fea944201df54a2100ff8a510807ff4288403ff2144201ff50a2100ff88510807ff3288403ff1944201ff4ca2100ff86510806fe618844dffa8c4205ff9462102efca31089bfd518840bfe28c4205df1462112ffe8310817fe418844bfea0c4205ff10621007fe6310
  | 6 => 0x7bf214a234df50a5119ef885288037f3294467bf194a200df4ca5119ef865288177e61944073f30ca203dd986511a6fe83288177e4194469bea0ca205df1065119efe43288177c219440bbfb04a200df98251006fac1288177c6094469bfa04a234df902511a6fa81288d37c4094467bf904a233df08251057fecb9882aff65cc415ff32e6203bf99731056fccb9880e7e65cc415feb2e6232bf59731056facb988027d65cc415fe32e620abf19731057fec99882aff64cc415ff3266202bf99331057fac9988c6fd64cc415fe326620abf1933118ffea9988c7fe54cc463feaa66231ff15331057fea79882bfe53cc415fea9e620aff14f31057fe879882bfe43cc415fea1e620aff10f31057fec59882bfe62cc4037f316620aff58b31005fac59882bfc62cc4037e3166232ffd4b31196fea5988c3fe52cc465fea966200df54b31187f8a5988c7ff42cc461ff2166231ff50b31187f8859882bff32cc415ef996620aff8cb31057fa6598803dd32cc415fe1966232ffd4731197fca3988037e51cc465fea8e6232ff14731196f8a3988c7ff41cc463ff20e6231ff5073118ff883988c3ff21cc461fe10e620affd8331057fcc198812fe60cc415feb066200bf58331057f8c1988cbff50cc465ff2866232ff54331197f8a1988c7ff40cc463ff2066231ff5033118ff881988c3ff20cc461fe1066205ffd963117dfecb188bffe658c4077f32c622fff5963117dfacb18817fc658c4077e32c6205ffd9231155fec9188abfe648c4057f324622aff59231155fac918817fc648c4057e324622affd5231157fca9188abfd548c455fe2a4622cbf58e3117ffea71882bfe538c45ffea9c620aff14e31157fe87188abdf438c415ff21c622aff50e31057f887188abdc438c40bffb14622eff98a3100dfcc518803fd628c4017eb146205ff18a3100df8c5188bfff528c45fbfa94622eff94a3117ffaa5188037d528c45dfe294622affd0a31177fc85188abfd428c45dfe214620affcca31177fc65188bbde328c401fe994620aff0ca31177b8651882afe618c45fffa8c6205ff9463102efca3188bffd518c40bfe28c6205df14631157fe8318817fe418c455fea0c6205ff10631057fe6318803df318c415fb98c622effc863102ff84318817ff608c401ff3046204bf98231007fac118802fd608c40bfe304622fffd423117ffca1188bffd508c45ffe284622affd0231157fc81188abfd408c455fe204622effc8231177f841188b7ff654c45b7fb2a6200dfd9531004feca988b7fe654c4077f32a622dff5953116dfaca988b7fc654c4077e32a622ddf1953101cf8ca988b3ff644c4597fb22622cff99131015fcc8988b3fd644c4597eb22622cff19131015f8c8988b3ff544c459ff2a2622cff55131167f8a8988b7ff534c415ff29a622dff5
  | 7 => 0xa90e77e6454873beb22a439df19152006fec6a90037e6354801beb1aa400df18d521cefe86a90e77e4354873bea1aa439df10d5200efec4a90067f6254807b7b12a401dfd095200efc84a90077d4254803be212a401df8c95200ef864a90037f6154801bf30aa400df58552006f8c2a90027c6154873bfa0aa439df905521cefa82a90e77c4154803bf90aa401df08552006fec0a90037e6054801beb02a400df181521cefe80a90e77e4054873bea02a439df1015200efe40a90077c2054815ffb2e640abfd9732057fccb9900efe65cc815feb2e6438bf59732057f8cb9902afc65cc815ffb26640abfd9332057fcc99900afe64cc815feb266437bf59332057f8c99902afc64cc86fffaa66437ff953321bffaa9990dffc54cc8037f31e640affd4f32057fca79902bfd53cc815fe29e640affd0f321bfbe879902bfe43cc815fea1e640aff10f32057b88799006fd62cc803ffa966401dfd4b3200ffca599007fd52cc803bea966401ff14b3200ffe8599007fe42cc803fea166401ff10b3200ffc6599007de32cc803f71966401ff0cb3200fb8659902bff61cc815ff30e6400bf98732057fac399002fd61cc815fe30e6438ffd47321c7fca3990e3fd51cc871fe28e6438df147321bffe83990dffe41cc86ffea0e6437ff1073200ffe4399007fc21cc815ffb06640aff98332025fcc19902bfd60cc8017eb06640aff183321c7fea1990e3fe50cc871fea866438ff143321bffe81990dffe40cc86ffea066437ff1033200ffe4199007fc20cc86dffb2a6436bfd95321b7fcca9900efe654c86dfeb2a6436bf595321b7f8ca9900efc654c86bffb226435bfd91321affcc89900afe644c86bfeb226435bf591321aff8c89900afc644c86bffaa26435ff951321affaa8990d7fc544c8037fb1a6436ffd4d32057fca6990dbfd534c815fe29a6435ffd0d321afbe869902bfe434c86bfea1a640aff10d321afb88699006ff624c803ffa926401dfd493200ffca499007fd524c803bea926401ff1493200ffe8499007fe424c803fea126401ff1093200ffe649902bef324c803ff1926401f78c93200ff86499007dc324c803f61926400ffd8532005fec299003fe614c801feb0a6400ff18532005f8c2990dbff514c86dff28a6436ff545321b7f8a2990db7c514c86bffa0a6435ff905321affa82990d7fc414c803ff90a6401ff08532007fec099002ff604c801ff3026400ff58132007f8c099012fc604c86dffa826436ff941321b7faa0990dbfc504c86bffa026435ff901321affa80990d7fc404c803ff9026401ff0813202efec9288d37e6494469beb24a205df1925102efec7288037e6394401beb1ca205df18e511a6fe87288d37e4394469bea1ca234df10e5102efec5288cf7e6294401beb14a2009f58a5102ef8c5288d37f429446
  | 8 => 0x3420004fc6febbe710000d8a4022e600090e0003ba5525c200053e68e722000000000654000d70218000c60a3e0000000000009ae0000962de02022a37816254e000af26d2524166bb09360024c2000000000b4c00000095aa7c284c844bcdbc000ae20007ba34c000000532b140f8cc200003a0008b853cb1e000122d760009fc57c5b28e600100000c00800900002a00000201b00100000001e00000e00300000200100000000200000000000000200600400a01900800400000100000000000e00000200a00000400c00200000200f02000600200300800300400300100100000d00a00500002e00000c00000000000202700000002300500c00200200100200100e00c00d00000200000900200000a00300100502100300100100006500201401300100600200900301100200000200400400600600a00300b00900001d00000500600700101600400700400f00000000601a00400100e00000400100200a00500b00c00700200100100100000700000300000000300500600000302500300500e00401900700500b00500900000100800100301200700200200600100000400100800800000500100802800d00200800101201900100200302500c00800d01400001d00400000100700400000000100001e01800c00000100100000404f00200a00000d00100300001603900200200100f00300100100300000600000700100000200100500100100200001100501100000000c00000000500400500000100400000000700100500000000000200000200500000500300901c00000000300301200200000800000903100100200901b00100a02e00000200300000300000700300000e00c00600400000a00100900400200001100100000500300000d00000500000f00600100200a00200100400200000000500600702600000301800c00b00e00b00900300000900602000000100d00700600100000000500000000301000000001200300e00000100900000000e00700a00501600000e00500402700100901900400500a00000200000000400400000000600400400000c00400400000000100100000201700400200500200400100000000200200a00103800100200000500400500200100000100300600000d00000200700400400000100a00200600200200000100e01200700800000100200000100000c00100800400000d00800700100300b00400100300400500401000200a00300300201300000000400000001900000f00600400000000200000400100501501000100703300000b00700100b00000c00000800600000000700c00000d00000202301700000100000000000200100100100100800f00400000100000100000300000f00500200100800100000000100501a00800f0060020000050010030020080090000021cefec8
  | 9 => 0x7a000082a322000808d0cab400000009e920bd00e019016a30894ab5600084a000b16bf62766c274494ed7aa1cc0e49000000031c0f65da6c800000074000009aa68a56000762c440002acd2a000b640002202da5e084ed048fc5bc8a0000752000c1e7900004322ce4986f095e0007881749ea1de000a3c2ca67e0008a68aed26000440000438000000000000dba000000d62d6a96cb668d21560000000003f65861b246e3c6000000b2442000000035200097cbf4882290b74c62c060001ca3fe00054283856266aa4eb22000b800008400000000000000000000000000ec0002160ce45c3e00008c0d52000ceead8000a64cd8daa91cd7491236ac645728ba4f830424ab5e0b26dc000d7e44c08c050b82000d5a0009a6000ccc90a11800063a288baac1000082823806c000b9e772b547fa4c8000d12b2c996368564cc465e2d24ba6180003449c893e816c8aac619c22492c4e45580f05b86cc47460843c374958148b1a1be00c9a07368aa19e8d89e6a8257ab2aa50cf2254b42000bdc6f8382ad4abe26040c9c67848cc4685fed20128ba45562988c800014400053aaee760398c029b60004641e4000caa0000005cc000000684000000aa2000c4000011a12e5f8a28c1c5825e40000000c6d88c18d660b0c527a877a0c4546886d146de0000001c2000000000424d34662ada88a0000000000002824d844e0cc0003b80009aa932cdc01ecc8ad229aa66000d440e20d88580000000000002d80002c81f6334a845cab489109547b8d9a7706a0000000360a1261431000030087e4fe000c589a29082f834041c3201e6370000000000180a1a0001fc686c5c0000000000006a68d04b8036476a4032e46cac24dc61050c000000000af4d9c000bf00000000000000009f47020000007e01b4c46ae80de0000009e2ae4000034b9a1aacae0000000003cc51a0000120000003eea26040000000000000072000db07dca2c00015456ebe442c55c0000000006c00000005209dc4aa04eca67ea73a766864500d504aeaa6718116d5e0aa35400000063600000085a17000000014e86a7f805a63c0000000008d689ad1000045819880436e10c7165d007ed48dc24cc24c9a81b0dd072679e4160dc7d4076bc8132576508ce600074c97415ea1661e4bebac900a7ea4673473c6caa9e472c24d38222962c222bcba662e8348c6adc3f4d84a3a0846e42f61e24628e8aec5a62d6bda5faa36484000b6a616cf816c24649c8206827966c42eab5821c02c6d87c660c3320000007c8c5ac1600e5e85b625294cc565ae03ca8085200082ea7a74e1ae15c6aa266000b629f8bc22007b46503fc9d2cac1c840a5ce6fa7e60000006ec000d58000000000594000230d80c687785447ae3d29be000000cd08da0009cc0000000000005d49f00000004a80004ac00
  | 10 => 0x8fa3fabe6b882066b00000000002cca903960002b8140cfa9dedca5d800000000078a00000000093c494386000622dae000c66b52560ca28e4b00602c54742b0a786000000afe07a000c9648088097a0000000001a20e6ac428025a41e0006320006d400083ad901760b4bca640056c9264691659a6ee584570bd8ce85485040009345ac000580000000000000bf252ad008b23b200000080098a18c37644464c000d78000ab6000b4a00018e000000000000000000c503a03f03a61000004b4b5ada20008bc038000b90884000c0cad60000004220000005780003ea1b8bc0d060000009d05f40a20fe27c000000b2065800074646014cdd40da21422ed0811010a4c67e204603e8468c4a5a48e0bad68b0235e2f2c4806a5389cece026e7e8c888f811c0d47b0a1858e7f06b88b46700c82b4c9a5f20008ca1d0126026b1000044681430ec144660002ec0005a878c0007c0c76000aa04d2d6e71c0000006f6000abc644c82c382aad2e000356058dd67829901ce00020ec1aa0827a2d07241acd7c66e72c000414b600000008660523aa1da802a0467aaca21291475e98058851270acd2000b96c36a6c1509b20007aa9bc7fc1e8d9e000000a8ab86dbe1a6688000a720004b2aa4000bb4390db801030ad4a69ebbc1f49f20f4b344ea5c60d231e87250a366db474a3d456a19a6bc2fa106042000cf60000708f2c2e146ca04049d84107ecca44e8388738952a5ece4b320641eeae0074000000000d1a23681a000cc00604f4c9062448c80e4a26068e247e14256cacc6e8a06cb621e0b685c6c6bd4ae680a5029d6350406b40d647281944420ac79839c02a0806348b01d6a1eda41c61888fe8dc3b049a1a464851866664e00099a3e6478764d8c0005b495686c7a40780927c46760e8000bc6bce758a8c0003c2b3e9f602e87800aaba7548cea2a3da45640e4e2c28c7a46a000000000000574ceac3e00000030610429602296e59c2c09b048ad4e6be76800054098e00000000017e7bc70ebea76a9480be000922a32944b7634626a068bb24b0000000d460004f04e0000000000000a74dcc000a20000000b940008f04c081261c492a3800000000699e1ba000af80007ca8ea0000ca00065a00048673e0008540002a066800030c000000b0e000000000000706032000000af6000ac88301d49503d06742a6cb47cec722b2a100000005105a400060a75c000000592c9eb1cb060000002d4000000000000000000000000d94c0a0005ba0000000006e228ccfc0000000000000007d03e23c04a0aea652098a9801c39edb286e2501967de3843ae4d4be038ec3cc7e26406ed249301522c27765f6362714cd445491e178696a5c0a69c05306ea33625ed4c8be596b462be4ee05e1120000005d281808e692dc830200048800000072045a000aaa
  | 11 => 0x6ae7ee946bec01833000038a000c94a4c2a40d66601c0942a4a0009280002e86e059e00000003029260000055a89e00000000027462656677c4301f239a4ec10e13c4fa38c00099cbfa7d8000d0a69c130550c2088e42e38089272a12c1ec0543a4a542580bc68cbfe000d425aa4f20a80000008a89ac0003e8000000000000d3643a5c8000d3258a4a684c52813ea246124c4d8ebaea608b676eda817a9669a41a87124482e44da5ec34e9ba868c00b449260001600f2000896a42b6ea9a8c2ba82dc0ae08a8560005dc45e1dcbba20a61a6b467c0240c2cf45167920006a428600092e9880000008261fe7be9c2be2cb0326cfe6a81fa000506c12000316000c3a2a20eab8e00047a0000007b200000013400000000004a00000033800022c8decec000c6c3de00000000032800026c34aab818a7f4426cbeca80000001c471a6647802fcd2c708d3a888028bd2c80c2a0006b67fe5689b44f63bc8768ee24e1a052e8a4436408a768747c2522c42004cd6c98be888c14aac000089051e000bb681c20cdb63b437c318a8679c3b67303d80fa05c0b8000ace8629ec210a92b3000055e0001bc33cd8200000065c0006ac80606234800020204c000d6cade7cc000b2e7f670c0007483a8906c300000004de000dd280c3e4000000000cb8000c080000000e4924cba0008f6b5c79416416860e5c0d724a46ba0fc62a1cc008000a0ab2809487c01a6fc0005ea75041a2322f013a00015aa780004340000007562b066cb086048329762e0c32a6e00012ad408a26e679a4d6732234628beea880c0000b26b7a7ac17221aa14d30a943c4aa8a96000d60526000000000d5618427e000a2200000000063e0009ca000000000ba0000000ab27a62946561b68ecdc6dac4ca452428a2ed1e972ba200000091a9b801664a3f8ab0000000000000000208cda9940000888243c86b20009c4000dc0c8ca304e695cbb8bde1f8242c86964000312cce2286a240076c3ca2489046986d000098ca7050ecc60006da9e4048000b6c000d86a580001920a400058cbf8082000938186000268b920000008f400089c0000007f2000b0c000a9c2f44d039484881e9fab4e4960147d2000d0200028a9787d6cbc06600032400000000052c9e85f08e0a0e7b677e000870c6a47c810c9c970c2c3a231457eb7e51c11eaae5a21588acb0454a000b1872e00064243eb785542b6d5485e78ea8e774000000000138000272000000d160a023e000000aacc4c5a03d636c000412000000d3e000c046f428e37275a7003f25b009c4508984b609084200099296037acdecca42a5be000000000000536000b68b980009e03ac82c0000d0986000000918694000b9c000850c745d60009ee982bfc7a235a5c490225c1ea2262c600049eb8c6ce69068a17c00062c000c5e0
  | 12 => 0xc7cce236496800024044a7e448232a000b705ee4700003ecd288d400033a0002fe000d968604ce92a5e289400000032cc7893ad1ccb2000182b3c29e5de70400054c0000000009da0003dcc4a000a0c16e000844000d92000b3ab50000000102000c26b7c638000a0071e29c00031a5342a82782ae9fe0005980000001080001f097e114000d5c00069aa44000dc4d22da0136c6e23a000b84a6a3be33ecf09d4d0ea48000bd696a2ba984a3400090c358d3c620a62a02c4e8360ee23c3ce000000270bccb8a6f2bc483eb38b72afc2c400000099807cdce000000086a520000005905fc630256afa9400001d224412437e87ac70262672b36da66d6000b123924185e61d8ad00008222e21201e0c34044c8e7da51400000083c678680d98af00002ee00000000020435cd1800
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xa76c41100077b65c411020f7865c411002fba74c411002fb974c411002dfb72c4110005f972c411020f7b52c41100077952c4110025fa71c4110026fb61c4110027f361c411002f7a51c411002f7851c411002ff241c4110207f141c411002ff221c4110007f121c4110004ff7558c100067f7558c100047f7558c1001cfe7558c10004fd7558c1001cfc7558c100067c7558c1001c7c7558c10004ff7458c10014fe7458c10004fd7458c10014fc7458c10024ff7358c10026df7358c10006de5358c10006dd5358c10006de4358c10006dd4358c10004ff7258c1000cfe7258c1000cfc7258c100067f5258c10054ff7158c1002cfe7158c10054fd7158c1002cfc7158c1002e7e5158c1002e7c5158c1002ede3158c1002edc3158c10024ff7058c10024fe7058c10024fd7058c10024fc7058c10026de3058c10026dc3058c10004ff755881001cfe7558810004fd755881001cfc7558810004ff7458810014fe7458810004fd7458810014fc7458810004ff7358810054fc7358810024ff7258810026ef72588100367f5258810036ee5258810006ed5258810036ee4258810006ed4258810036ee325881000cff715881002cfe715881000cfd715881002cfc715881002e7e515881002e7c515881002eee215881002eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810026f71058810026fa1058810026f510588100067f76548101e67e76548100067d76548101e67c76548101e67f64548101ce7e64548101fe7d64548101e67c64548101e67f63548101f67e63548100067d63548101e67c63548101ed7f72548100476f72548101e67f625481000e7e62548101e76e625481000e6e62548100367d62548101e76d62548100066d625481000e7c625481000777715481002d7e715481002d7c715481000774715481002d74715481008e7e61548101e67e60548101e77710548101e77a10548101e7751054810054ff76cc810024fe76cc810004fd76cc810024fc76cc810056de63cc810006dd63cc810004ff764c810024fe764c810004fd764c810024fc764c810056de634c810006dd634c81000eee624c810006ed624c810005f7714c81002df4714c810004fd76cc4100457e75cc4100057d75cc410004ff764c4100057f754c4100457c754c41008cff76484100057f75484100457c7548410005df7348410005dc734841008ef66148410025fb7644010006fb7644010004fb76440100077b75440101df787544010026fb6244010006f962440101df7b5244010007795244010025fb7144010027f3714401002efa6144010027f2614401002f7a514401002ff2514401002f7251440101dff1514401002f7851440101d7f3414401002ff0414401002ff22144010007f12144010
  | 1 => 0xc51017e7c658c510056de638c510006dd638c510024fc764c5100057f754c51006d7c754c5100067f654c51016e7c654c510006df634c510056dc634c510005fb704c510025f8704c510004fe760c5100067f650c51014e7c650c510065be740c510005bd740c510056de630c510006dd630c51002f74510c510074fe768851002d7f758851002d7c75885100067f65885101367c658851002f76518851002f745188510005f67688510076f6768851002f77758851002f74758851000777658851024f746588510245f77488510245f5748851005df5728851000ef6628851000ef4628851005f77528851005f75528851002ff37088510025f67088510025f4708851002ff0708851002ef76088510024fc76485100057f754851006d7c75485100067f65485101267c6548510005df7348510005dc7348510006ef624851000eec624851000776514851023f745148510005fb7048510025f87048510025f4764851000ef47648510024f4764851000777754851023f74754851000777654851023f746548510235f77448510235f57448510007d77348510007d4734851005df77248510007e77248510007e7624851000ef6624851000ef4624851005fe4624851005f77524851005f755248510007f37048510025f67048510025f47048510007f07048510004fe76cc11002cfc76cc1100067f65cc1101167c65cc110006df63cc110056dc63cc110005f671cc110005f571cc110054ff764c110004fd764c110054fc764c1100057f754c11006d7c754c1100067f654c1100e67c654c110005bf744c110065bc744c110006df634c110056dc634c110005f7714c110005f4714c110005fa7688110026fa76881100077b658811022f78658811005df9728811000efa628811000ef8628811005f7b528811005f795288110027f3718811002dfa7188110027f07188110026fb6188110027f361881100077a518811022f785188110227f24188110227f1418811005ff2218811005ff1218811000cff764811005cfd764811000cfc76481100067f65481100a67c6548110005bf7448110065bc7448110006ef624811000eec6248110005f77148110005f47148110027f0104811005df8764811000ef8764811000cf876481100077b654811021f786548110007bb7448110217b87448110025fb7248110027eb7248110007eb624811000efa624811000ef8624811005fe8624811005f7b524811005f79524811005fea4248110217e94248110007f3714811002df87148110007f07148110026fb6148110027f361481100077a514811021f785148110217f24148110217f1414811005ff2214811005ff121481100067f65c41100967c65c4110065be74c4110005bd74c4110025f671c4110026f761c4110025fa76c4110026fa76c4110024f
  | 2 => 0x14bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d100067f5258d10004ff7158d10006f77158d100067c5158d10004ff7058d10006fb7058d10004fe7618d100067f6518d100067c6518d10056de6318d10006dd6318d1000cfe76d891006d7c75d89100067f65d89100067c65d891005eee62d8910004ff75d89100067f75d891001cfe75d8910004fd75d891001cfc75d89100067c75d891001c7c75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d8910054fe73d8910004fd73d891005e7f52d8910006ef42d891005eec42d891005eec32d891002cfe71d8910024fd71d891002cfc71d89100067c51d891005eef21d8910024fe70d891005cfd70d8910024fc70d891005eef20d89100057f755891006d7c75589100067f65589100067c6558910005bf7458910065bc7458910005df7358910005dc735891005eec6258910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df7358910054fc7358910006dc7358910054dc735891005cff7258910006ef725891005e7f5258910074ff7158910006f771589100067c515891008cff7058910006fb70589100067f76549100057e76549100067e76549100047e76549100067d76549100057c76549100067c76549100047c76549102767f64549101ce7e64549102767d64549101ce7c64549100067f63549101f67e63549100067d63549101f67c635491005d7f725491006f6f725491005e7f625491000e7e625491005e7d625491000e7c625491002d7c71549102777641549102777541549101e7761054910054ff76cc910004fe76cc910004fd76cc910054fc76cc9100067f65cc9101c67c65cc910056de63cc910006dd63cc910006ef62cc91000eec62cc910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101b67c654c910056de634c910006dd634c9100057e769451002e7e76945100847e76945102667f64945101a67e64945102667d64945101a67c64945100067f639451026e7e63945100067d639451026e7c63945100057d72945100067f629451019e7e62945100067d629451019e7c629451002d7e719451002f76719451002e7f619451002f76419451026775419451002e7f609451025f76109451002f741094510024fe76cc510024fc76cc51006d7e75cc5100057d75cc5100067f65cc5101967c65cc510006df63cc510056dc63cc5102577451cc510025fa70cc510005f970cc510004fe768c5100067f658
  | 3 => 0xc75886101367e65886100067d6588610006de6388610006dd6388610025f8708861000cff7648610024fc76486100057f75486100857c75486101267e65486100067d6548610005df7348610005dc7348610006de6348610006dd634861000eee6248610006ed6248610005fb7048610025f87048610025fb7648210036fb76482100277a6548210027796548210007bb744821028fb87448210027da6348210027d96348210027eb724821000efa6248210026f862482100777b5248210077795248210077ea424821028fe9424821002df871482100077a5148210287785148210025f976c421002ef976c42100277a65c42100277965c421002fba74c421002fb974c4210027da63c4210027d963c421002dfb72c4210005f972c421027f7b52c42100077952c4210027f271c421002f7a51c421002f7851c421006d7e76d951006e7e76d951001c7e76d95100067f64d95100067e64d95100067d64d95100067c64d95100057d72d95100067e62d95100067c62d951002d7c71d95100077641d95100077541d951025f7610d951025f7410d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067e32d95100067c32d951025e7f71d951006e7e71d951002c7e71d951006e7d71d951006e7c71d951002c7c71d95100067f41d95100067e41d95100067d41d95100067c41d95100067f21d95100067c21d95100067f70d951025e7e70d951006e7d70d951025e7c70d95100067f40d951025e7e40d95100067d40d951025e7c40d951025e7e30d951025e7c30d95100067f20d951025e7e20d951025e7c20d951025e7e10d951006e7d10d951025e7c10d9510054fe76d8d100067f65d8d100067c65d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d10006df43d8d10006dc43d8d1000cfe72d8d10004fd72d8d1000cfc72d8d100067f52d8d10006de32d8d10006dc32d8d1002cfe71d8d1002cfc71d8d100067c51d8d10024fe70d8d10024fc70d8d1006d7e7598d100057d7598d100067f6598d100067c6598d10006df6398d100057f7558d1006d7c7558d100067f6558d100067c6558d10005bf7458d10065bc7458d10005ef7258d1005dec7258d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10
  | 4 => 0x8e10006dd5258e10006dc5258e10006df4258e10006de4258e10006dd4258e10006dc4258e10006df7158e10006dd7158e10006df5158e10006de5158e10006dd5158e10006dc5158e100065c5158e10006df4158e10006de4158e10006dd4158e10006dc4158e10006df2158e10006dc2158e10026df7058e10026de7058e10026dd7058e10026dc7058e10026df5058e10026de5058e10026dd5058e10026dc5058e10026df4058e10026de4058e10026dd4058e10026dc4058e10026df2058e10026de2058e10026dd2058e10026dc2058e10026df1058e10026de1058e10026dd1058e10026dc1058e10004ff7558a1001cfe7558a100067e7558a1001c7e7558a10004fd7558a100067d7558a1001cfc7558a10004ff7458a10014fe7458a10004fd7458a10014fc7458a10004ff7358a10054fc7358a10026ef7258a100767f5258a10076ee4258a10006ed4258a100067c5158a10076ef2158a10024fc7058a10026ee2058a10026ec2058a10026f71058a10026f51058a101e57f7654a100067f7654a100047f7654a101e67e7654a101e57d7654a100067d7654a100047d7654a101e67c7654a101e67f6454a101ce7e6454a1029e7d6454a101e67c6454a101e67f6354a101f67e6354a101e75e6354a100065e6354a100067d6354a101e75d6354a100065d6354a101e67c6354a101ed7f7254a100876f7254a101e67f6254a1000e7e6254a100767d6254a1000e7c6254a10007777154a1002d7c7154a10007747154a10005747154a1005e7d6154a101e67e6054a101e77a2054a101e7771054a10054ff76cca10024fe76cca10004fd76cca10024fc76cca101c67e65cca100067d65cca10056de63cca10006dd63cca10004ff764ca10024fe764ca10004fd764ca10024fc764ca101b67e654ca100067d654ca10056de634ca10006dd634ca10005f7714ca10005f4714ca1025d7d769461002e7d769461006c7d769461025e7f64946101a67e64946102967d649461025e7c649461025e7f639461026e7e639461025f5e63946100065e63946100067d639461025f5d63946100065d639461025e7c63946100057d729461025e7f629461019e7e62946100067d629461025e7c629461002d7e719461002f76719461002e7e609461025f7a209461002f77109461002f7810946100857e75cc6100057d75cc6101967e65cc6100067d65cc610056de63cc610006dd63cc610025fa70cc610005f970cc61017e7e658c6100067d658c610056de638c610006dd638c610054ff764c6100057f754c6100857c754c61016e7e654c6100067d654c610056de634c610006dd634c610005fb704c610025f8704c61014e7e650c6100067d650c61007dbe740c610005bd740c610056de630c610006dd630c61005cfd768861002d7f758861002d7
  | 5 => 0x56de634c310006dd634c310005f7714c31002df4714c31000cff764831002cfc7648310005bf744831004dbc744831009ebe6448310006bd644831000eee6248310006ed6248310005f7714831002df471483100067f74596100067e74596100067d74596100067c74596100067f73596100067e73596100067d73596100067c73596100067f43596100067e43596100067d43596100067c43596100067f72596100047f72596100067e72596100067d72596100067c72596100067f42596100067e42596100067d42596100067c42596100067e32596100067c32596100867f71596100867e71596100067d71596100867c71596100067f41596100067e41596100067d41596100067c41596100067f21596100067c21596100267f70596100267e70596100267d70596100267c70596100267f40596100267e40596100267d40596100267c40596100267f30596100267e30596100267d30596100267c30596100267f20596100267e20596100267d20596100267c20596100267f10596100267e10596100267d10596100267c1059610056df7598e10056de7598e10056dd7598e10056dc7598e10056df7498e10056de7498e10056dd7498e10056dc7498e10006df5498e10006de5498e10006dd5498e10006dc5498e10056df7298e10056de7298e10056dd7298e10056dc7298e10006df5298e100065f5298e10006de5298e10006dd5298e10006dc5298e10006df4298e10006de4298e10006dd4298e10006dc4298e10056df7198e10056dd7198e10006df5198e10006de5198e10006dd5198e10006dc5198e100065c5198e10006df4198e10006de4198e10006dd4198e10006dc4198e10006df2198e10006dc2198e10026df7098e10026de7098e10026dd7098e10026dc7098e10026df5098e10026de5098e10026dd5098e10026dc5098e10026df4098e10026de4098e10026dd4098e10026dc4098e10026df2098e10026de2098e10026dd2098e10026dc2098e10026df1098e10026de1098e10026dd1098e10026dc1098e10004ff7558e1001cfe7558e10004fd7558e1001cfc7558e10004ff7458e10014fe7458e10004fd7458e10014fc7458e10026df7358e10006df5358e10006de5358e10006dd5358e10006dc5358e10006df4358e10006de4358e10006dd4358e10006dc4358e10004ff7258e1000cfe7258e1000cfc7258e100067f5258e10006de3258e10006dc3258e100067c5158e10024fc7058e10026de3058e10026dc3058e10006df7558e10006de7558e10006dd7558e10006dc7558e10006df7458e10006de7458e10006dd7458e10006dc7458e10006df5458e10006de5458e10006dd5458e10006dc5458e10006df7258e10006de7258e10006dd7258e10006dc7258e10006df5258e100065f5258e10006de525
  | 6 => 0xf7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f10014fe7458f10004fd7458f10014fc7458f1002edf7358f10006df5358f10006dc5358f10004ff7258f1000cfe7258f1000cfc7258f100067f5258f10024fc7158f1002e7e5158f1002e7c5158f1002ede3158f1002edc3158f1002cff75d8b1001cfe75d8b10004fd75d8b1002cfc75d8b1002cff74d8b10014fe74d8b1002ebe74d8b10014be74d8b10004fd74d8b1002ebd74d8b10004bd74d8b1002cfc74d8b10054fe73d8b10004fd73d8b1008cfd72d8b1008e7f52d8b1002ef671d8b1002e7e51d8b1002e7c51d8b1002ef970d8b1000cff7658b10006be6458b10006bd6458b1002eec6258b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b10014fe7458b10004fd7458b10014fc7458b10004ff7358b10054fc7358b1002eef7258b1008e7f5258b10024fc7158b1002e7e5158b1002e7c5158b1002eee2158b1002eec2158b1008eef2058b100067f7654b100067e7654b100067d7654b100067c7654b102c67f6454b101ce7e6454b102c73e6454b101ce3e6454b102c67d6454b100073d6454b100063d6454b101ce7c6454b100067f6354b101f67e6354b100067d6354b101f67c6354b1008d7f7254b100976f7254b1008e7f6254b1000e7e6254b1008e7d6254b1000e7c6254b1002d7e7154b1002d7c7154b102c7764154b102c7754154b10054ff76ccb1002cfe76ccb10004fd76ccb1002cfc76ccb101bebe64ccb10006bd64ccb10056de63ccb10006dd63ccb10004ff764cb1002cfe764cb10004fd764cb1002cfc764cb101aebe644cb10006bd644cb10056de634cb10006dd634cb100957e75cc7100057d75cc71018ebe64cc710006bd64cc71002f7451cc7100057f754c7100957c754c710166be644c710006bd644c710025f5768871002ef57688710024f5768871002f77758871002f74758871002df774887102bdf5748871002fb6648871002fb5648871000ef6628871002fe6628871002fe5628871002ef4628871008f77528871008f755288710025f6708871002ff2708871002ff17088710025f47088710034ff76487100057f75487100957c754871011ebe6448710006bd6448710005df7348710005dc734871002f76514871002f745148710005f77648710036f776487100077775487102b77475487102adf774487102adf574487102a7b66448710007b56448710007d77348710007d4734871002fe7724871000ef6624871000ef4624871008f77524871008f755248710025f67048710025f4704871010ebe64cc310006bd64cc310056de63cc310006dd63cc31002df671cc310005f571cc310054ff764c3100057f754c3100957c754c310005bf744c31004dbc744c3100debe644c310006bd644c310
  | 7 => 0xc520004fd76cc520054fc76cc5200a57e75cc5200057d75cc520006bf64cc52018ebc64cc520006f761cc520006f461cc520004fe768c520004fd768c52002cfc768c520006bf648c520156bc648c520006df638c520056dc638c520025fa708c520005f9708c520004ff764c520004fe764c520004fc764c5200057f754c5200a57c754c520006bf644c520166bc644c520004fe760c520004fd760c52002cfc760c52009dbe740c520005bd740c520006bf640c520146bc640c520006df630c520056dc630c52000dee720c520005ed720c520006f7610c52002ef4610c520025fa700c520005f9700c52000cfe76cc12000cfc76cc120006bf64cc12010ebc64cc120006df63cc120056dc63cc12000dee72cc120005ed72cc120054ff764c12000cfe764c1200d4fd764c12000cfc764c1200057f754c1200a57c754c120005bf744c12009dbc744c120006bf644c1200debc644c120006df634c120056dc634c120005ef724c12000dec724c120027e8204c12002dbf765931004ebf7659310014bf765931002ebf6559310006be6559310006bd655931002ebc655931002ebf635931002ebc635931002ebf6259310006be625931002ebc62593100073f525931002fb6715931004fb5715931002f3e515931002f3c51593102cfb6105931002fb41059310006bf7559310006be7559310006bd7559310006bc7559310006bf7359310006be7359310006bd7359310006bc7359310006bf5359310006be5359310006bd5359310006bc5359310006bf7259310006be7259310006bd7259310006bc7259310006bf52593100063f5259310006be5259310006bd5259310006bc5259310006be3259310006bc325931004ebf715931002ebe715931004ebd715931002ebc7159310006bf515931002ebe515931002e3e5159310006bd515931002ebc515931002e3c515931002ebe315931002ebc3159310006bf215931002ebe215931002ebc215931004ebf70593102cebe7059310006bd70593102cebc7059310006bf50593102cebe5059310006bd50593102cebc50593102cebe30593102cebc3059310006bf20593102cebe20593102cebc205931002ebf10593102cebe105931002ebc105931002cff75d8f1001cfe75d8f1002e7e75d8f1001c7e75d8f10004fd75d8f1002e7d75d8f100047d75d8f1002cfc75d8f1002cff74d8f10014fe74d8f1002ebe74d8f10014be74d8f10004fd74d8f1002ebd74d8f10004bd74d8f1002cfc74d8f1000cfe72d8f10004fd72d8f1002cfc72d8f100067f52d8f1002ef671d8f1002e7e51d8f1002e7c51d8f1002ef970d8f10004fd7698f100957e7598f100057d7598f10006be6498f10006bd6498f1002edf6398f1002edc6398f10054ff7658f10006be6458f10006bd6458f1002edc6358f10004f
  | 8 => 0x4ff74d8d20014fe74d8d20004fd74d8d20014fc74d8d20006df53d8d20006dc53d8d20024ff72d8d2000cfe72d8d20024fd72d8d2000cfc72d8d200ee7f52d8d200ee7d52d8d200eedf32d8d200eedd32d8d2002cfe71d8d20004fd71d8d200067c51d8d2009dbe7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d200d5f97098d200057f7558d200a57c7558d20005bf7458d2009dbc7458d20006bf6458d20006bc6458d20005f77158d20005f47158d20105fb7058d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d20014fe7458d20004fd7458d20014fc7458d20006bc7458d20014bc7458d20006df7358d200d4ff7258d20006ef7258d200d67f5258d200d67d5258d20004ff7158d20006f77158d20004f77158d2002cfc7158d20006f47158d20004f47158d200067c5158d20104ff7058d20006fb7058d200ecfe7618d200a57e7518d200057d7518d20006bf6418d20006bc6418d20056de6318d20006dd6318d200a57e75d85200057d75d8520006bf64d8520006bc64d85200077451d8520004ff75d852001cfe75d85200067e75d852001c7e75d8520004fd75d85200067d75d85200047d75d852001cfc75d8520004ff74d8520014fe74d8520004fd74d8520014fc74d8520054fe73d8520004fd73d8520024fd72d85200767f52d85200767d52d8520006f751d85200067c51d8520006f451d85200067451d8520076f621d8520076f521d852009dbe7498520005bd7498520006bf6498520006bc6498520006f7619852005df970985200057f75585200a57c7558520005bf745852009dbc7458520006bf6458520006bc6458520005df7358520005dc735852008dfb7058520006bf6418520006bc6418520006f5611852000774511852002cff751852001cfe7518520004fd751852002cfc751852002cff7418520014fe7418520004fd741852002cfc7418520054fe7318520004fd7318520024fd72185200367f52185200367d5218520006f7511852002e7c511852002ef4511852002e74511852002ef62118520036f52118520024fe701852002ef97018520024fc701852002e7f76945200067e76945200067d769452002e7c76945202de7f64945200073f64945200063f64945201a67e64945202de7d64945201a67c64945202df3c64945201a63c64945200067f639452026e7e63945200067d639452026e7c639452019d7f729452019d7d729452025e7f629452019f6e42945202df6d42945202d57e71945200a77671945200067f619452002e7c61945200077a709452000779709452019e7f609452019f7b209452025f6e209452025f6c209452019f782094520004fe76c
  | 9 => 0xd5298620026f6719862002e7c519862002ef64198620006f5419862002ef6219862008ef52198620024fe7098620026fa7098620024fa7098620024fc7098620026f61098620026fa1098620026f41098620004ff75586200067f75586200047f755862001cfe7558620004fd755862001cfc75586200067c755862001c7c7558620004ff7458620014fe7458620004fd7458620014fc7458620004ff7358620054fc735862005e7f525862005e7d5258620026f771586200067c5158620006f64158620006f5415862005ef6215862005ef52158620024fc7058620026f61058620026f4105862002e7f769462025e7e76946200067d769462002e7c769462025e7f64946201a67e64946203067d649462025e7c649462025e7f639462026e7e63946200067d639462025e7c639462019d7f729462019d7d729462019e7d62946202fd7e71946200b776719462002e7e61946200067d619462002e7c619462025f7a709462000779709462025e7e609462025f6f209462019f7b209462025f782094620054ff76cc620024fe76cc620004fd76cc6200b57e75cc6200057d75cc62002cff768c620024fe768c620004fd768c620056de638c620006dd638c620025fa708c620005f9708c620004ff764c620004fd764c620024fc764c6200057f754c6200b57c754c620005ef724c62000dec724c62002cff760c620024fe760c620004fd760c6200adbe740c620005bd740c620056de630c620006dd630c620025fa700c620005f9700c6202f5be76d912009ebe76d9120014be76d9120006bf65d9120006be65d9120006bd65d9120006bc65d91202e7af72d91202efac72d91202ef3f52d91202ef3d52d91200073c51d91202efbb20d91202e7ae20d91202e7ac20d91202efb820d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006be53d9120006bd53d9120006bc53d91202e6bf72d91202eebe72d91202eebd72d91202eebc72d91202eebf52d91202ee3f52d91202eebe52d91202eebd52d91202ee3d52d91202eebc52d91202eebf32d91202eebe32d91202eebd32d91202eebc32d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bd51d9120006bc51d91200063c51d91202eebf21d91202eebe21d91202eebd21d91202eebc21d91202eebf70d91202e6be70d91202eebd70d91202e6bc70d9120006bf50d91202e6be50d9120006bd50d91202e6bc50d91202e6be30d91202e6bc30d91202eebf20d91202e6be20d91202eebd20d91202e6bc20d91202e6be10d91202e6bc10d9120054fe76d8d20006bf64d8d20006bc64d8d20004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20
  | 10 => 0x48301e67c76548301e67f64548301ce7e64548303167d64548301e67c64548300075f73548301f75c73548301067e63548301ed7f72548300cf6f72548301e67f625483000e7e62548300be7d625483000e7c62548300057c71548301e67e60548301e75f30548301e77a30548301e75d30548301f779305483002cff759843002e7f759843001cfe7598430004fd759843002cfc759843002e7c759843002c7c759843002cff7498430014fe7498430004fd749843002cfc749843000cfe7298430004fd729843002cfc72984300067f52984300067d5298430024fe7198430026f6719843002e7c519843002ef64198430006f54198430056f7319843002ef43198430026df3098430026dd3098430026f61098430026f41098430004ff75584300067f75584300047f755843001cfe7558430004fd755843001cfc75584300067c755843001c7c7558430004ff7458430014fe7458430004fd7458430014fc7458430004ff725843000cfe725843000cfc72584300067f52584300067d5258430026f771584300067c5158430006f64158430006f54158430056f73158430056f43158430026f61058430026f4105843025d7f769443002e7f769443002c7f769443025e7e769443025d7d76944300067d76944300047d769443002e7c769443025e7f64944301a67e649443030e7d649443025e7c649443026f5e73944300075d739443026e7e63944300057d729443019e7e62944300067d629443025e7c62944302fd7e71944300cf76719443002e7e61944300067d619443002e7c619443025e7e609443025f5f309443025f7a309443025f5d309443026f79309443002cff7688430024fe7688430004fd76884300057f75884300cd7c75884301367e65884300067d658843002ef66188430006f56188430004ff7648430004fd7648430024fc76484300057f75484300cd7c75484301267e65484300067d6548430005df7348430055dc734843000eee6248430006ed6248430006f66148430006f56148430004ff7558e200067f7558e200047f7558e2001cfe7558e20004fd7558e2001cfc7558e200067c7558e2001c7c7558e20004ff7458e20006bf7458e20004bf7458e20014fe7458e20004fd7458e20014fc7458e20006bc7458e20014bc7458e20026df7358e20006de5358e20006dd5358e20006de4358e20006dd4358e200d67f5258e200d67d5258e200d6df3258e200d6dd3258e20004ff7158e2002cfc7158e200067c5158e20024fe7058e20024fc7058e20026de3058e20026dc3058e2002cff759862001cfe7598620004fd759862002cfc759862002cff7498620014fe749862002ebe7498620014be7498620004fd749862002ebd7498620004bd749862002cfc7498620054fe7398620004fd739862008e7f529862008e7
  | 11 => 0x7d4618c53031f5e518c53031f5c518c530025de708c530007da708c530007d9708c530025dc708c530056df608c530057db608c530024fc764c5300057f754c5300e57c754c5300067f654c53016e7c654c530006bf644c530166bc644c530006f7614c530006f4614c530005fb704c530025f8704c530005de760c530056de760c530055df750c530345dd750c5300075f650c53032f5c650c530055df740c5300579e740c53033ddd740c5300579d740c5300059d740c5300079f640c530146de640c530146dc640c5303379c640c5301469c640c530005dd720c53013ede620c53013edc620c53032f5f520c5300075d520c530325de710c530057d6710c530006df610c53031f5e510c53031f5c510c530025de700c530025dc700c530056df600c530057db600c530004fe7688530004fd768853002cfc76885300057f75885300e57c75885300067f65885301367c6588530006bf648853012ebc6488530005df7388530055dc7388530006ef628853000eec6288530004ff7648530004fe7648530004fc76485300057f75485300e57c75485300067f65485301267c6548530006bf644853011ebc6448530005df7348530055dc73485300067f74594300067e74594300067d74594300067c74594300567f73594300567e73594300567d73594300567c73594300567f43594300567e43594300567d43594300567c43594300067f72594300047f72594300067e72594300067d72594300067c72594300067f42594300067e42594300067d42594300067c42594300567f32594300567e32594300567d32594300567c32594300067f71594300067e71594300067d71594300067c715943002c7c71594300067f41594300067e41594300067d41594300067c41594300567f31594300567e31594300567d31594300567c31594300067f21594300067c21594300267f70594300267e70594300267d70594300267c70594300267f40594300267e40594300267d40594300267c40594300267f30594300265f30594300267e30594300267d30594300265d30594300267c30594300267f20594300267e20594300267d20594300267c20594300267f10594300267e10594300267d10594300267c1059430004ff755883001cfe75588300067e755883001c7e7558830004fd75588300067d755883001cfc7558830004ff7458830014fe7458830004fd7458830014fc745883000cfd7358830024ff7258830026ef72588300be7f52588300beee4258830006ed4258830056ef3258830056ec3258830004ff715883002cfc71588300067c51588300beef2158830024fc7058830026df3058830026dd3058830026ee2058830026ec20588301e57f76548300067f76548300047f76548301e67e76548301e57d76548300067d76548300047d765
  | 12 => 0xf654c9301b67c654c930006bf644c9301aebc644c930006ef624c93000eec624c930005fb704c930025f8704c930025dc764c93000edc764c930024dc764c930385df754c930385dd754c9300075f654c93036f5c654c93037ddf744c93037ddd744c9300079f644c9301aede644c9301aedc644c9303779c644c9301ae9c644c930055df724c930057cf724c930007cf624c93000ede624c93000edc624c9300d7cc624c9300d75f524c9300d75d524c930005dc714c93036f5c514c930007db704c930025de704c930025dc704c930007d8704c930056df604c930057db604c9300e57e75d85300057d75d85300067f65d85300067c65d8530006bf64d8530006bc64d8530004ff75d853001cfe75d85300067e75d853001c7e75d8530004fd75d85300067d75d85300047d75d853001cfc75d8530004ff74d8530014fe74d8530004fd74d8530014fc74d853000cfe72d8530004fd72d853000cfc72d85300067f52d85300067d52d8530006df32d8530006dd32d85300067c51d8530006f721d8530006f421d85300e57e75985300057d75985300067f65985300067c65985300ddbe7498530005bd7498530006bf6498530006bc6498530006f761985300057f75585300e57c75585300067f65585300067c6558530005bf74585300ddbc7458530006bf6458530006bc6458530005ef72585300d5ec72585300e57c75185300067f65185300067c6518530006bf6418530006bc6418530006f5611853002cff751853002e7f751853001cfe7518530004fd751853002cfc751853002e7c751853002c7c751853002cff7418530014fe7418530004fd741853002cfc741853000cfe7218530004fd721853002cfc72185300067f52185300067d521853002e7c5118530006f7211853002ef4211853002e7f76945300057e76945300067e76945300047e76945300067d76945300057c769453002e7c769453002c7c76945303667f64945300073f64945300063f64945301a67e64945303667d64945301a67c64945303673c64945301a63c649453031f5f739453031f5c73945303675e43945303675d43945300057d72945300067f629453019e7e629453019e7c62945300075f32945300075d32945300e57e71945300e77671945300067f619453002e7c619453026f7b309453025f5e3094530024fe768c5300067f658c53017e7c658c530006bf648c530156bc648c530006f7618c53002ef4618c530025fa708c530005f9708c530024de768c53035ddf758c53035ddd758c5300075f658c53034f5c658c530325df748c530325dd748c5300079f648c530156de648c530156dc648c5303579c648c5301569c648c530005dd728c530176de628c530176dc628c53034f5f528c5300075d528c530055de718c530006df618c530007d7618c530
  | 13 => 0x95303c67c10d95300ddbe76d91300debe76d9130014be76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d91303b79f73d91300df9c73d91300079e53d91300079d53d9130006be62d9130006bc62d91300073f52d91300073c51d91303bfbb30d91303b79e30d91303b79c30d91303bfb830d9130006bf75d9130006be75d9130006bd75d9130006bc75d91303b6bf73d91303bebe73d91300debd73d91303bebc73d9130006bf53d91303bebe53d9130006bd53d91303bebc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d91300063f52d9130006be52d9130006bd52d9130006bc52d91303bebf32d9130006be32d91303bebc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bd51d9130006bc51d91300063c51d91303bebf31d91303bebc31d9130006bf21d9130006bc21d91303bebf70d91303b6be70d91300debd70d91303b6bc70d9130006bf50d91303b6be50d9130006bd50d91303b6bc50d91303bebf30d91303b6be30d91300debd30d91303b6bc30d9130006bf20d91303b6be20d91303b6bc20d91303b6be10d91303b6bc10d913000cfe76d89300e57c75d89300067f65d89300067c65d8930006bf64d8930006bc64d89300d6ee62d8930004ff75d89300067f75d893001cfe75d8930004fd75d893001cfc75d89300067c75d893001c7c75d8930004ff74d8930014fe74d8930004fd74d8930014fc74d8930024fd73d893000cfc73d89300d67f52d89300d6ee32d893002cfe71d8930004fd71d89300067c51d89300d6ec21d8930054fd70d89300d6ef20d89300057f75589300e57c75589300067f65589300067c6558930005bf74589300ddbc7458930006bf6458930006bc64589300d6ec6258930005f77158930005f471589300067f76549300057e76549300067e76549300047e76549300067d76549300057c76549300067c76549300047c76549303ae7f64549300073f64549300063f64549301ce7e64549303ae7d64549301ce7c64549303af3c64549301ce3c64549300075e73549300075d73549303af5e43549303af5d43549300d57f72549300e76f72549300d67f625493000e7e625493000e7c62549300057c71549301f77b30549301e75e3054930005de76cc930056de76cc930055df75cc9303a5dd75cc9300075f65cc93038f5c65cc930055df74cc93039ddd74cc9300079f64cc9301bede64cc9301bedc64cc9303979c64cc9301be9c64cc9300d5dd72cc93000ede62cc93000edc62cc9300d75f52cc9300d75d52cc930005de71cc93038f5c51cc930025de70cc930025dc70cc930056df60cc930057db60cc930024fc764c9300067
  | 14 => 0x4fd749863002ebd7498630004bd749863002cfc749863000cfe7298630004fd729863002cfc72986300067f52986300067d5298630026f67198630006f7519863002e7c519863002ef4519863002e74519863002ef64198630006f54198630024fe7098630026df3098630026dd3098630026f61098630026f41098630004ff75586300067f75586300047f755863001cfe7558630004fd755863001cfc75586300067c755863001c7c7558630004ff7458630014fe7458630004fd7458630014fc7458630004ff725863000cfe725863000cfc72586300067f52586300067d5258630026f77158630006f751586300067c5158630006f45158630006745158630006f64158630006f54158630024fc7058630026f61058630026f4105863002e7f769463025e7e76946300067d769463002e7c769463025e7f64946301a67e64946303d67d649463025e7c64946300075e73946300075d73946300e67d63946300057d729463019e7e62946300067d629463025e7c62946302fd7e71946300ff76719463002e7e61946300067d619463002e7c619463025e7e609463025f5f309463026f7b309463002ef6618c630006f5618c630025fa708c630005f9708c6300057f754c6300fd7c754c630006f6614c630006f5614c630005fb704c630025f8704c63002cff7688630024fe7688630004fd76886300057f75886300fd7c758863002ef66188630006f56188630004ff7648630004fd7648630024fc76486300057f75486300fd7c7548630005df7348630055dc7348630006f66148630006f561486300e57e76d95300e67e76d953001c7e76d95300067f64d95300067e64d95300067d64d95300067c64d95300073c64d95300063c64d95303c75f73d95300e75c73d95300075e43d95300075d43d95300057d72d95300067e62d95300067c62d95300057e71d95303cf7b30d95303c75e30d95303c75c30d95303cf7830d95300067f74d95300067e74d95300067d74d95300067c74d95303c67f73d95303ce7e73d95300e67d73d95303ce7c73d95300067f43d95303ce7e43d95300067d43d95303ce7c43d95300067f72d95300067e72d95300067d72d95300047d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95303ce7f32d95300067e32d95303ce7c32d95300067f71d95300067e71d953002c7e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95303ce7f31d95303ce7c31d95300067f21d95300067c21d95303ce7f70d95303c67e70d95300e67d70d95303c67c70d95300067f40d95303c67e40d95300067d40d95303c67c40d95303ce7f30d95303c67e30d95300e67d30d95303c67c30d95300067f20d95303c67e20d95303c67c20d95303c67e10d
  | 15 => 0xf754cb30425dd754cb3041ddf744cb3041ddd744cb301aede644cb30056dc644cb30057cf724cb3000ede624cb3000edc624cb301075f524cb301075d524cb30005dc714cb304175c514cb30025de704cb30025dc704cb3002cff759873001cfe7598730004fd759873002cfc759873002cff7498730014fe7498730004fd749873002cfc7498730024fe739873000cfe7298730004fd729873002cfc72987300067f52987300067d529873002ef6719873002e7c5198730056f7319873002ef43198730004ff75587300067f75587300047f755873001cfe7558730004fd755873001cfc75587300067c755873001c7c7558730004ff7458730014fe7458730004fd7458730014fc7458730024fc7358730024dc7358730004ff725873000cfe725873000cfc72587300067f52587300067d5258730056df3258730006dd3258730056f771587300067c5158730056f73158730056dc3158730056f4315873002e7f769473026e7e76947300067d769473002e7c769473026e7f64947301a67e649473040e7d649473026e7c64947303e75f73947303e75c739473026f5e439473040f5d43947300057d729473019e7e62947300067d629473019e7c629473026f5f32947300075d32947304057e719473011776719473002e7e61947300067d619473002e7c61947303e75c3194730055dd768c730006dd768c7303fddf758c7303fddd758c7303f5df748c7303f5dd748c730156de648c730056dc648c730005dd728c730176de628c730056dc628c7303ef5f528c7300075d528c730057d6718c730006dd618c7303e75e518c7303e75c518c730025de708c730025dc708c73002cff7688730054fe7688730004fd76887300057f75887301157c7588730005df7388730055dc7388730004ff7648730004fd7648730054fc76487300057f75487301157c7548730005df7348730055dc7348730004ff7558a3001cfe7558a30004fd7558a3001cfc7558a30004ff7458a30014fe7458a30004fd7458a30014fc7458a30026ef7258a300ee7f5258a300eeee4258a30006ed4258a300eeee3258a30004ff7158a3002cfc7158a300067c5158a30024fc7058a30026df3058a30026dd3058a30026ee2058a30026ec2058a300067f7654a301e67e7654a300067d7654a301e67c7654a301e67f6454a301ce7e6454a303de7d6454a301e67c6454a300075f7354a300075c7354a300d67d6354a301ed7f7254a300ff6f7254a301e67f6254a3000e7e6254a300ee7d6254a3000e7c6254a300057c7154a301e67e6054a301e75f3054a301f77b3054a3000cff764ca3000eee624ca30006ed624ca30005fb704ca30025f8704ca3002cff759863001cfe7598630004fd759863002cfc759863002cff7498630014fe749863002ebe7498630014be7498630
  | 16 => 0x8d21006df5018d21006de5018d21006dd5018d21006dc5018d21006df4018d21006de4018d21006dd4018d21006dc4018d2113edf2018d2113ede2018d2113edd2018d2113edc2018d212d57e769452102e7e76945212d47e769452143e7f64945211a67e649452143e7d64945211a67c64945210067f63945210075f63945210065f639452126e7e63945210067d639452126e7c63945210075c63945210065c639452102d7f729452119d7d729452102e7f629452102d7e719452102f76719452102e7f619452119f77219452102f6c219452102f74219452102f64219452125e7c609452100cfe76cc52100cfc76cc5211257e75cc5210057d75cc5210067f65cc5211967c65cc521006df63cc521056dc63cc52100dee72cc521005ed72cc52113cfe768c5210067f658c52117e7c658c521176df638c521056dc638c521054ff764c52100cfe764c52115cfd764c52100cfc764c5210057f754c5211257c754c5210067f654c52116e7c654c521006df634c521056dc634c521005ef724c52100dec724c521174fe760c5210067f650c52114e7c650c52111dbe740c521005bd740c521006df630c521056dc630c52102f6f758852102f6c75885210076f65885214376c6588521007cf6388521007cc638852102dee718852102fe6718852102eef618852100fe7618852102f6e518852102f6c51885210067f65d81210067c65d8121006df63d8121006dc63d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121004ff74d8121014fe74d8121004fd74d8121014fc74d8121054fe73d8121004fd73d812108e7f52d812108e7d52d81210067e51d81210067c51d8121006fb40d8121006f840d812108efa20d81211257e75981210057d75981210067f65981210067c6598121005de7398121005dd7398121006df6398121006dc6398121006fb60981210057f75581211257c75581210067f65581210067c6558121005bf745812111dbc7458121005df7358121005dc7358121006df6358121006dc63581210067f65181210067c6518121006df6318121006dc6318121026fa6018121006f96018121004ff7558b3001cfe7558b30004fd7558b3001cfc7558b30004ff7458b30014fe7458b30004fd7458b30014fc7458b30024fc7358b30056ef7258b301067f5258b30056ef3258b30056ec3258b30004ff7158b3002cfc7158b300067c5158b30106ef2058b300067f7654b301f67e7654b300067d7654b301f67c7654b301f67f6454b301ce7e6454b3042e7d6454b301f67c6454b301f75e7354b300075d7354b301f75e4354b3042f5d4354b301057f7254b301176f7254b301067f6254b3000e7e6254b301067d6254b3000e7c6254b301075f3254b300057c7154b301f75c3154b30055df764cb300bedf764cb30425d
  | 17 => 0x65c65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d211775f52d8d211775d52d8d210075c51d8d21177d721d8d21177cc21d8d21177d421d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d21176df72d8d21176de72d8d21176dd72d8d21176dc72d8d21176df52d8d211765f52d8d21176de52d8d21176dd52d8d211765d52d8d21176dc52d8d21176df42d8d21176de42d8d21176dd42d8d21176dc42d8d21176df71d8d21176dd71d8d21006df51d8d21006de51d8d21006dd51d8d21006dc51d8d210065c51d8d21006df41d8d21006de41d8d21006dd41d8d21006dc41d8d21176df21d8d21176de21d8d21176dc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006df40d8d21006de40d8d21006dd40d8d21006dc40d8d21176df20d8d21176de20d8d21176dd20d8d21176dc20d8d211257e7598d210057d7598d210067f6598d210067c6598d21006df6398d2115df57198d210057f7558d211257c7558d210067f6558d210067c6558d21185f77158d21004ff7558d210067f7558d210047f7558d2101cfe7558d21004fd7558d2101cfc7558d210067c7558d2101c7c7558d21004ff7458d21014fe7458d21004fd7458d21014fc7458d21006df7358d2115cff7258d21006ef7258d2115e7f5258d2115e7d5258d21184ff7158d21006f77158d210067c5158d21004ff7058d21024fc7058d21174fe7618d210067f6518d210067c6518d21056de6318d21006dd6318d21175de7618d21006de7618d21174de7618d21006df6518d210075f6518d210065f6518d21006de6518d21006dd6518d21006dc6518d210075c6518d210065c6518d21006df6418d21006de6418d21006dd6418d21006dc6418d2113f5f5218d2113f5d5218d210075c5118d2113fd72118d2113fcc2118d2113fd42118d21056df7518d21056de7518d21056dd7518d21056dc7518d21056df7418d21056de7418d21056dd7418d21056dc7418d21006df5418d21006de5418d21006dd5418d21006dc5418d21056df7218d21056de7218d21056dd7218d21056dc7218d2113edf5218d2113e5f5218d2113ede5218d2113edd5218d2113e5d5218d2113edc5218d2113edf4218d2113ede4218d2113edd4218d2113edc4218d21056df7118d21056dd7118d21006df5118d21006de5118d21006dd5118d21006dc5118d210065c5118d21006df4118d21006de4118d21006dd4118d21006dc4118d2113edf2118d2113ede2118d2113edd2118d2113edc2118d21056df7018d21056de7018d21056dd7018d21056dc701
  | 18 => 0xf7558e210067f7558e210047f7558e2101cfe7558e21004fd7558e2101cfc7558e210067c7558e2101c7c7558e21004ff7458e21014fe7458e21004fd7458e21014fc7458e2102edf7358e2115e7f5258e2115e7d5258e2115edf3258e2115edd3258e2102cfe7158e2102cfc7158e2102e7e5158e2102e7c5158e2102ede3158e2102edc3158e21004ff7058e21024fc7058e2115cfd76cc6211357e75cc6210057d75cc62102e7f65cc62102e7c65cc62102edf63cc62102edc63cc621184ff764c6210057f754c6211357c754c62102e7f654c62102e7c654c62102edf634c62102edc634c6211357e75982210057d759822102e7f659822102e7c6598221005de7398221005dd739822102efb6098221026f860982210057f75582211357c755822102e7f655822102e7c655822102ef86058221004ff75582210067f75582210047f755822101cfe7558221004fd755822101cfc75582210067c755822101c7c7558221004ff7458221014fe7458221004fd7458221014fc7458221004ff7358221054fc735822105e7f525822105e7d525822102cfc715822102e7e515822102e7c515822105efa205822102efb105822102ef810582212d57e76d95211267e76d952101c7e76d95210067f64d95210067e64d95210067d64d95210067c64d952102d7c71d952119f7721d952119f6c21d952119f7421d95210067f74d95210067e74d95210067d74d95210067c74d95210067f73d95210067e73d95210067d73d95210067c73d95210067f43d95210067e43d95210067d43d95210067c43d952119e7f72d952102c7f72d952119e7e72d952119e7d72d952119c7d72d952119e7c72d952119e7f42d952119e7e42d952119e7d42d952119e7c42d952119e7f32d952119e7e32d952119e7d32d952119e7c32d952119e7f71d95211267e71d952119e7d71d952119e7c71d95210067f41d95210067e41d95210067d41d95210067c41d952119e7f21d952119e7e21d952119e7d21d952119e7c21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f40d95210067e40d95210067d40d95210067c40d952119e7f20d952119e7e20d952119e7d20d952119e7c20d9521054fe76d8d210067f65d8d210067c65d8d21004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21004ff74d8d21014fe74d8d21004fd74d8d21014fc74d8d21006df53d8d21006de53d8d21006dd53d8d21006dc53d8d21006df43d8d21006de43d8d21006dd43d8d21006dc43d8d2102cff72d8d21174fd72d8d211767f52d8d211767d52d8d21176df32d8d21176dd32d8d210067c51d8d21024fe70d8d21004fd70d8d21054de76d8d21006df65d8d210075f65d8d210065f65d8d21006de65d8d21006dd65d8d21006dc65d8d210075c65d8d21
  | 19 => 0x883102eec2158831004ff7058831024fc7058831056df305883113eef20588310067f76548311f67e76548310067d76548311f67c76548311f67f64548311ce7e64548311f73e64548311ce3e64548314567d64548311f73d64548310063d64548311f67c64548310075f73548311f75c73548311867e63548314575f43548311f75c435483113d7f725483114f6f725483113e7f625483100e7e625483113f6e625483100e6e625483113e7d62548311f76d62548310066d625483100e7c625483113f5e325483113f5c325483100777715483102d7c715483100774715483102d7471548311767e61548311f75f31548311f77631548311f77531548311e67e605483102ddf764c431006df764c431004df764c4310075f754c43144f5c754c431145de744c431145dc744c43102f9e644c43102f9d644c43113dde724c43113ddc724c431006dd624c43144f5f524c4310075d524c43102ddf714c431057d7714c43102ede614c43102fd6614c43102f5e514c43102f5c514c43102fd6414c431447d5414c431005df704c431004ff75580310067f75580310047f755803101cfe7558031004fd755803101cfc75580310067c755803101c7c7558031004ff7458031014fe7458031004fd7458031014fc7458031004ff725803100cfe725803100cfc72580310067f52580310067d525803102e7e515803102e7c515803102efb7058031006fa5058031006f95058031056fb3058031056f8305803102efb105803102ef8105803102e7f74d962102e7e74d962102e7d74d962102e7c74d962102e7f73d962102e7e73d962102e7d73d962102e7c73d96210067f43d96210067e43d96210067d43d96210067c43d962102e7d72d962102e6d72d962119e7f42d962119e7e42d962119e7d42d962119e7c42d962119e7f32d962119e7e32d962119e7d32d962119e7c32d962102e7e71d962102c7e71d962102e7671d962102e7f41d962102e7e41d962102e7d41d962102e7c41d962102e7e31d962102e7c31d962102e7f21d962102e7e21d962102e7c21d962102e7f70d962102e7e70d962102e7d70d962102e7c70d96210067f40d96210067e40d96210067d40d96210067c40d962119e7f20d962119e7c20d962102cff75d8e2101cfe75d8e21004fd75d8e2102cfc75d8e2102cff74d8e21014fe74d8e21004fd74d8e2102cfc74d8e21006df43d8e21006dc43d8e2102eed72d8e211767f52d8e211767d52d8e21176de32d8e21176dc32d8e2102cfe71d8e2102ef671d8e2102e7e51d8e2102e7c51d8e21024fe70d8e21004fd70d8e2115cfd7698e211357e7598e210057d7598e2102e7f6598e2102e7c6598e2102edf6398e2102edc6398e21054ff7658e210057f7558e211357c7558e2102e7f6558e2102e7c6558e2102edc6358e21004f
  | 20 => 0x7cf624c93100ede624c93100edc624c93115fcc624c93115f5f524c93115f5d524c931007d7714c93102ddc714c931007d4714c931056df614c931057d7614c93146f5c514c9310057e769453102e7e76945311947e76945314667f64945311a67e64945314667d64945311a67c649453102e7f63945310057d72945310067f629453119e7e629453119e7c62945310075f32945310075d329453102d7e719453102f76719453102e7f619453126f77319453102f74319453125e7c60945310067f658c53117e7c658c531055f6718c531056f7618c5310075f658c53145f5c658c531156de648c531156dc648c531005dd728c531176de628c531176dc628c53145f5f528c5310075d528c53102dde718c53102edf618c531057d7618c53102f5e518c53102f5c518c5310067f65d81310067c65d8131004ff75d813101cfe75d8131004fd75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d813100cfe72d8131004fd72d813100cfc72d81310067f52d81310067d52d8131006df32d8131006dd32d81310067e51d81310067c51d8131006de31d813116d7e75981310057d75981310067f65981310067c6598131006fb60981310057f755813116d7c75581310067f65581310067c6558131005bf7458131165bc7458131005ef725813115dec72581310067f65181310067c6518131026fa6018131006f96018131006bf7559031006be7559031006bd7559031006bc7559031056bf73590311469f7359031056be7359031056bd7359031056bc73590310569c7359031056bf5359031056be5359031056bd5359031056bc5359031006bf7259031006be7259031006bd7259031006bc7259031006bf52590310063f5259031006be5259031006bd5259031006bc5259031056bf3259031056be3259031056bd3259031056bc3259031146bf715903102ebe7159031146bd715903102ebc7159031006bf515903102ebe515903102e3e5159031006bd515903102ebc515903102e3c5159031056bf315903102ebe3159031056bd315903102ebc3159031006bf215903102ebe215903102ebc2159031006bf7059031006be7059031006bd7059031006bc7059031006bf5059031006be5059031006bd5059031006bc5059031056bf30590310569f3059031056be3059031056bd3059031056bc3059031006bf2059031006bc205903102ebf105903102ebc1059031004ff755883101cfe7558831004fd755883101cfc7558831004ff7458831014fe7458831004fd7458831014fc7458831006df4358831056dc435883102cff725883102eef725883113e7f525883113eee5258831006ed5258831056ef325883113ede3258831056dc3258831056ec325883102e7e515883102e7c5158831056df315883102eee215
  | 21 => 0x551cc63102f5c51cc631005dd70cc63117d7e75982310057d759823102efb6098231026f8609823102ef86058231004ff755823101cfe7558231004fd755823101cfc7558231004ff7458231014fe7458231004fd7458231014fc7458231004ff725823100cfe725823100cfc72582310067f52582310067d525823102cfc715823102e7e515823102e7c515823102efb105823102ef8105823116d7e76d953116e7e76d953101c7e76d95310067f64d95310067e64d95310067d64d95310067c64d95310057d72d95310067e62d95310067c62d953102d7c71d953126f7731d953126f7431d95310067f74d95310067e74d95310067d74d95310067c74d95310067f73d953126e7e73d953116e7d73d953126e7c73d95310067f43d953126e7e43d95310067d43d953126e7c43d95310067f72d95310067e72d95310067d72d95310047d72d95310067c72d95310067f42d95310067e42d95310067d42d95310067c42d953126e7f32d95310067e32d953126e7c32d953126e7f71d953116e7e71d953116e7d71d953116e7c71d95310067f41d95310067e41d95310067d41d95310067c41d953126e7f31d953116e7d31d953126e7c31d95310067f21d95310067c21d95310067f70d95310067e70d95310067d70d95310067c70d95310067f40d95310067e40d95310067d40d95310067c40d953126e7f30d953126e7c30d95310067f20d95310067c20d953100cfe76d893116d7c75d89310067f65d89310067c65d893115eee62d8931004ff75d89310067f75d893101cfe75d8931004fd75d893101cfc75d89310067c75d893101c7c75d8931004ff74d8931014fe74d8931004fd74d8931014fc74d893115e7f52d893115eee42d8931006ed42d893115eee32d8931054fd71d89310067c51d893115eef21d8931024fe70d8931004fd70d893115eec20d89310057f755893116d7c75589310067f65589310067c655893115eec62589310067f76549310057e76549310067e76549310047e76549310067d76549310057c76549310067c76549310047c765493147e7f64549311ce7e645493147e7d64549311ce7c645493115d7f725493116f6f725493115e7f625493100e7e625493100e7c625493102d7c71549311f77731549311e67c6054931005de76cc931056de76cc931174de76cc9310075f65cc9314775c65cc9311bede64cc9311bedc64cc93115ddd72cc93100ede62cc93100edc62cc93115f5f52cc93115f5d52cc93102dde71cc931056df61cc931057d761cc9314775c51cc93100cfc764c9310067f654c9311b67c654c931006ef624c93100eec624c931005f7714c931005f4714c93115ddc764c93100edc764c93100cdc764c9310075f654c93146f5c654c9311aede644c9311aedc644c931055df724c931057cf724c931
  | 22 => 0x8b3101cfe7558b310067e7558b3101c7e7558b31004fd7558b310067d7558b3101cfc7558b31004ff7458b31014fe7458b31004fd7458b31014fc7458b31056ef7258b311867f5258b31056ef3258b31056ec3258b310067c5158b31186ef2158b31004ff7058b31024fc7058b311f57f7654b310067f7654b310047f7654b311f67e7654b311f57d7654b310067d7654b310047d7654b311f67c7654b311f67f6454b311ce7e6454b314a67d6454b311f67c6454b311857f7254b311976f7254b311867f6254b3100e7e6254b311867d6254b3100e7c6254b311875f3254b31007777154b3102d7c7154b31007747154b31005747154b311e67e6054b31055df764cb3113edf764cb3113cdf764cb310575e654cb310575d654cb311aede644cb31056dc644cb31057cf724cb3100ede624cb3100edc624cb311875f524cb311875d524cb3102ddc714cb3149f5c514cb3126d7d769473102e7d769473116c7d769473126e7f64947311a67e64947314967d649473126e7c649473102e7e63947310057d729473119e7e62947310067d629473119e7c629473126f5f32947310075d329473102d7e719473102f76719473102f76319473102f5c319473125e7e6094731004ff755833101cfe7558331004fd755833101cfc7558331004ff7458331006bf7458331004bf7458331014fe7458331004fd7458331014fc7458331006bc7458331014bc7458331004ff725833100cfe725833100cfc72583310067f52583310067d5258331056df3258331006dd32583310067e51583310067c5158331056dc3158331056fb7058331056fb3058331056f8305833100cff7658a31055dc7358a3102eec6258a31177ce3258a31004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a31014fe7458a31004fd7458a31014fc7458a31006df4358a31006dc4358a311767f5258a31176de3258a31176ee3258a31176dc3258a3102cfc7158a3102e7e5158a3102e7c5158a3102eee2158a3102eec2158a31004ff7058a31024fc7058a310067f7654a310067e7654a310067d7654a310067c7654a3148e7f6454a311ce7e6454a3148e7d6454a311ce7c6454a310075f7354a310075c7354a3115e7d6354a3148f5f4354a3148f5c4354a311757f7254a3117f6f7254a3100e7e6254a311767d6254a3100e7c6254a311775e3254a311775c3254a3102d7c7154a3113e7e6154a311f7773154a311e67e6054a3100cff764ca31175df734ca3100eee624ca31006ed624ca31005f7714ca3102df4714ca3102ddd76cc631056dd76cc6310575e75cc6310575d75cc631155de74cc631055dc74cc631175de72cc631055dc72cc631006dd62cc6314875f52cc6310075d52cc63102fd661cc63102f5e51cc63102fd651cc63102f5651cc631487d
  | 23 => 0x67f7058a510067e7058a510067d7058a510067c7058a510067f4058a510067e4058a510067d4058a510067c4058a5119e7f2058a5119e7c2058a5102e7f1058a5102e7c1058a5126d7f76cca5102d7e76cca510057d76cca5102d7c76cca5126d7f74cca511a57e74cca514c57d74cca5126d7c74cca5119d7e73cca5126f5e63cca510075d63cca514bf5f43cca5126f5c43cca5119d7d72cca5119e7d62cca5119f5e32cca5119f6e32cca5119f5c32cca5102d7e71cca510057d71cca5102d7c71cca512d67e61cca511c77661cca5125d7e70cca510057d70cca510057f764ca5102d7e764ca510057d764ca5102d7c764ca514b57f744ca511a57e744ca514b57d744ca511a57c744ca5119d7f734ca510075e634ca510075d634ca514af5f434ca514af5c434ca5119d7f724ca5119e7d624ca5126f6f324ca5119f5e324ca5119f5c324ca5119f6c324ca510057f714ca5102d7c714ca512d67e614ca511b776614ca510057f704ca5125d7c704ca5102d7d769825125d7f74982511a57e74982510057d749825125d7c749825126d7e739825125f5e73982510055e73982510057d739825125f5d73982510055d73982510067e639825102e7c639825119d7e72982510057d729825125d7c729825102e7f62982510067d629825102d7e719825102d7c719825102e7e619825102f76619825102d7e709825102e7f609825102f7b609825102f78609825102f7b109825102f78109825102d7f76582510057f74582511a57e74582510057d74582511a57c745825102e7f64582510067d64582510057f735825126d7c735825102e7f63582510067d63582510057f725825119d7e725825119d7c725825102e7f62582510067d625825102d7e715825102d7c715825102e7e615825102f76615825102d7f705825102f7b605825125e7e605825102e7c605825102f78605825102f7b105825102f7810582510067f74597310067e74597310067d74597310067c74597310567f73597310567e73597310567d73597310567c73597310567f43597310567e43597310567d43597310567c43597310067f72597310047f72597310067e72597310067d72597310067c72597310067f42597310067e42597310067d42597310067c42597310567f32597310567e32597310567d32597310567c32597311967f71597311967e71597310067d71597311967c71597310067f41597310067e41597310067d41597310067c41597310567f31597310567e31597310567d31597310567c31597310067f21597310067c21597310067f70597310067e70597310067d70597310067c70597310067f40597310067e40597310067d40597310067c40597310567f30597310567e30597310567d30597310567c30597310067f20597310067c2059731004ff755
  | 24 => 0xd751853202cfc751853202cff7418532014fe741853202ebe7418532014be7418532004fd741853202ebd7418532004bd741853202cfc741853202edd7318532006df4318532006dc4318532054fd721853213e7f521853213e7d521853213ede321853213edc3218532006f7511853202e7c511853202ef4511853202e74511853202ef64118532006f5411853202ef6211853213ef52118532024fe7018532004fd7018532004ff75d813201cfe75d8132004fd75d813201cfc75d8132004ff74d8132014fe74d8132004fd74d8132014fc74d8132054fd72d81321067f52d81321067d52d813202cfe71d8132004fd71d81320067c51d8132106fa20d8132006fb60981320057f75581321b57c7558132005bf74581321adbc7458132005f77158132005f471581321b57e75181320057d7518132026fa6018132006f9601813202d7d7698e5126d7f7498e511a57e7498e510057d7498e5126d7c7498e5102e7f6498e510067d6498e5102d7e7398e5102e7f6398e5102f5f6398e5102e5f6398e5102f5c6398e5126f5e4398e510075d4398e5119d7e7298e510057d7298e5119d7c7298e5102e7f6298e5102d7e7198e5102d7c7198e5102e7e6198e5102f766198e5102f5e3198e5102f5c3198e5125d7e7098e510057d7098e5102e7c6098e5102d7f7658e510057f7458e511a57e7458e510057d7458e511a57c7458e5102d7f7358e5102f5f6358e5126e7e6358e5102e7c6358e5102f5c6358e5102e5c6358e510075e4358e510075d4358e510057f7258e5119d7e7258e5119d7c7258e5102e7f6258e5102d7e7158e5102d7c7158e5102e7e6158e5102f766158e5102f5e3158e5102f5c3158e510057f7058e5125d7c7058e5102e7f6058e5102d7f7658a510057f7458a511a57e7458a510057d7458a511a57c7458a5102e7f6458a510067e6458a510067d6458a5102e7c6458a510057f7358a5126d7c7358a5102e7f6358a510067e6358a510067d6358a5102e7c6358a5102d7f7258a5102f6f6258a5119e7e6258a5102e7c6258a5102f6c6258a5102e6c6258a5102d7e7158a5102d7c7158a5102e7e6158a5102f766158a5102f6e2158a5102f6c2158a510057f7058a5125d7c7058a5102e7f6058a5102e7c6058a510067f7458a510067e7458a510067d7458a510067c7458a510067f7358a510067e7358a510067d7358a510067c7358a510067f4358a510067e4358a510067d4358a510067c4358a5119e7f4258a5119e7e4258a5119e7d4258a5119e7c4258a5119e7e3258a5119e7c3258a5102e7e7158a5102c7e7158a5102e7c7158a5102c7c7158a510067f4158a5102e7e4158a510067d4158a5102e7c4158a5102e7e3158a5102e7c3158a5119e7f2158a5102e7e2158a5102e6e2158a5102e7c2158a5102e6c2158a51
  | 25 => 0x81520073f74581520053f74581521cd7e74581520057d74581521cd7c74581520073c74581521cd3c74581520067f64581520067d64581520057f73581520075f73581520055f73581521f57c73581520075c73581520055c73581520067f63581520067d63581524e57f72581520076f72581520b56f72581524e67f62581520a76f62581520057f71581520077771581520057771581520057c71581520077471581520057471581520067e61581520067c61581520077b60581521e67e60581524dd7e76181521e57f74181521cd7e74181520057d74181521e57c74181521f57e73181521e75e73181520055e73181520057d73181521e75d73181520055d73181520067e63181520067c631815201d7f721815200d7e721815201d7d721815200d7c72181521ee7f62181524d76f62181520057e71181520057d71181520067e61181520067c61181521e57e70181521e67f60181521e77a60181521e67d60181520077960181521e77a20181524cf79201815202cff759873201cfe7598732004fd759873202cfc759873202cff7498732014fe7498732004fd749873202cfc749873200cfe739873202ede739873200cde739873202cfc7398732006df4398732056dc43987321767f52987321767d5298732176de3298732056dc329873202ef6719873202e7c519873202edf3198732056f7319873202ef4319873202ef62198732176f52198732024fe7098732004fd7098732056df3098732004ff75587320067f75587320047f755873201cfe7558732004fd755873201cfc75587320067c755873201c7c7558732004ff7458732014fe7458732004fd7458732014fc745873200cfc735873215e7f525873215e7d5258732056f771587320067c5158732056f73158732056f4315873215ef62158732004ff7058732024fc7058732004ff75583320067f75583320047f755833201cfe7558332004fd755833201cfc75583320067c755833201c7c7558332004ff7458332014fe7458332004fd7458332014fc745833200cfc73583320d67f52583320d67d5258332004ff715833202cfc71583320067c5158332056fb7058332056fb3058332056f830583320d6fa20583321b57e75d85320057d75d85320077451d8532004ff75d853201cfe75d85320067e75d853201c7e75d8532004fd75d85320067d75d85320047d75d853201cfc75d8532004ff74d8532014fe74d8532004fd74d8532014fc74d8532054fd72d85321867f52d85321867d52d8532006f751d85320067c51d8532006f451d85320067451d8532006f641d8532006f541d8532186f621d8532024fe70d8532004fd70d8532006f761985320057f75585321b57c75585321adbe7418532005bd7418532006f5611853200774511853202cff751853201cfe7518532004f
  | 26 => 0x50d7d76985520057f74985521cd7e74985520057d74985521cd7c74985520067f64985520067e64985520067d64985520067c64985521f57e73985520057d73985520067f63985520067e63985520067d63985520067c639855219d7d72985520076d72985521256d729855219e7f62985521376f62985522d57e71985520067f61985520077761985521e57e70985520057d70985520057f74585521cd7e74585520057d74585521cd7c74585520057f73585520075f73585520055f73585521f57c73585520075c73585520055c735855250d7f72585520076f72585521356f725855250e7f62585521276f62585520077761585520067e61585520057f70585521e57c70585525057e76185520057f74185521cd7e74185520073e74185521cd3e74185520057d74185520073d74185520053d74185521cd7c74185520067f64185520067e64185520067d64185520067c64185521f57e73185520057d73185520067f63185520067e63185520067d63185520067c631855201d7f721855200d7e721855201d7d721855200d7c72185522d67f62185524ff6f621855219d7e71185520067f61185520077661185520067d61185520077561185520077641185520077541185522d77621185522d77521185521e57e70185520057d701855202e7f741855202e7e741855202e3e741855202e7d741855202e3d741855202e7c741855202e7f731855202e7e731855202e7d731855202e7c73185520067f43185520067e43185520067d43185520067c431855202e7f721855202e7d721855201c7d72185522d67f42185522d67e42185522d67d42185522d67c42185522d67f32185522d67e32185522d67d32185522d67c321855202e7f411855202e7e411855202e76411855202e7d411855200675411855202e7c411855202e7f211855202e7e211855202e76211855202e7d21185522d675211855202e7c211855202e7f701855202e7e701855202e7d701855202e7c70185520067f40185520067e40185520067d40185520067c40185522d67f20185522d67e20185522d67d20185522d67c20185520057f74d81521cd7e74d81520057d74d81521cd7c74d81520067f64d81520067d64d81521f57e73d81520057d73d81520067f63d81520067d63d815201d7f72d815201d7d72d81524de7f62d81524f76f62d81520057e71d81520057d71d81520067e61d81520067c61d81524df7a20d81524df7920d81524e57d76981521e57f74981521cd7e74981520057d74981521e57c74981521f57e73981520057d73981520067e63981520067c63981524ed7d72981521e76d72981520a56d72981521ee7f62981520b76f62981520057e71981520057d71981520067e61981520067c61981521e57e70981521e67f60981520077b60981520057f745
  | 27 => 0x100080180000020000000006001001004400a000004000c00600a001000000200000000000020080040000004006001000800201000d000000a001001001000000000300000000150030024006002001004c000007003000400000c001002000a0000248024008001000001400000900d800800600800a0008018001005803800000b007800402000c0048000006000000804000c000000001800c000001000401200400080040080000000000000000001000800a0070000010002006001800c00c00001200240000090038014002009001808804a000001000800000000f811002a001001802000200c003000000e0000050010002006000000002000f001803000a0190010018002000000801400201f001800801e00e00b802c004002007800c004002007001000a00200080080020040058010004000000803c00200300100180100000000048004000004008402600400000000180020000014000007006002c008000000000000a001000000c0020000028004006010000002400c00100080140020430020004006000001800401800200c80380060040018004000001006000405a00a009003000000301e000c0020050057f74d8d521cd7e74d8d520057d74d8d521cd7c74d8d520075e43d8d520075d43d8d5201d7f72d8d5201d7d72d8d525367f62d8d525476f62d8d525375f32d8d525375d32d8d520057e71d8d520057d71d8d521e57e70d8d520057d70d8d5253d7d7698d521f57f7498d521cd7e7498d520057d7498d521f57c7498d520067f6498d520067d6498d5251d7e7398d521f67f6398d520075f6398d520065f6398d5252d7d7298d521f76d7298d521b56d7298d5252e7f6298d521c76f6298d520057e7198d520057d7198d521e57e7098d520057d7098d520057f7458d521cd7e7458d520057d7458d521cd7c7458d520075f6358d521f67e6358d5253d7f7258d520076f7258d521c56f7258d5253e7f6258d521b76f6258d520057f7158d52007777158d52005777158d520057c7158d52007747158d52005747158d520057f7058d521e57c7058d525357e7618d521f57f7418d521cd7e7418d520057d7418d521f57c7418d520067f6418d520067d6418d5252d7e7318d521f67f6318d521f75e6318d521f67d6318d520075d6318d520065d6318d521f75e4318d520075d4318d5201d7f7218d5200d7e7218d5201d7d7218d5200d7c7218d5251e7f6218d525276f6218d5251f5f3218d5251f5d3218d520057e7118d520057d7118d521e57e7018d520057d7018d520057f74d85521cd7e74d85520057d74d85521cd7c74d85521f57e73d85520057d73d855201d7f72d855201d7d72d85525067f62d85525176f62d85520077641d85520077541d85525077621d85525077521d85521e57e70d85520057d70d8552
  | 28 => 0x20004000001800800000100a0008008004007001800400200000000000010068034006000002800c000008002800000800b00080000240010068010000001001002401200000000ac018002000800401e000000803000c008000800801e000001800c008007002000001000c000805001c0000000004010002001800402800700180640020000000028000000003000400200000c000000000600100080040000010004008003002800001e001001802c00e0000018000004001003002c00800d0000008004003003000c008001000000800200f005003402a004000001800400e0010010002000000000000c007005800001600f001000c014023001006c024006000003400a0000020000006002000002c008000001000c00a0050008000006011003000000200d0008014000002000000c00000600180040060020038000004001001000c0000030028040014016000000400c002003000c0020000060000004000000002400400800180540060010000000012001000000c00c009001800001a0100018000022006004800800a00e002000000000300f8000004014015800000c000000001000201d002000c00e009002000c01000000000000100000010000008003001800c0120030008000000013001805800000000c800800200400f004c000001000008000200800680040060130010008002002001800400200f000002c008009000800003c00500e80000000030010000006024008803000000a0038044000002000000000001d001000000a0010000000002005005001000601700500000000000010000012000003000800803c004801400c0010018000010011001001c00c003000004803c00300180100200080000058008002000000000001000380480080040000004004000006001400600000000040100020008010002004001000c000005006004400400600000040000010000004000001001805c04e00600000900000100000004000004015800000000500200000040000000004000001007802c006001001800401a01200a802c042001001801c010000000800400000100e800400000100000000000060058024002001011001c008000005006c012005001003000c001001800002000500280240540040030008012001001000800401200a00040040050010000008000000001c00e0020028008000018000000000200c009001c0060000078008000006002004401000100000280280000070008008000009000c000006000001800000000080240140020108008034005001000801400301a0018018003000001800e00300a004c0000000128018000002005800000400000080100000010018000004006001800000200400200040020010000000000004003800001a00b000000000600701c0090002007003009c02e01
  | 29 => 0x400380000200020098000004007000002c006000001001404e00400100080000020018004000001002800001a0030008010000000000000001c004005800400000a002800000e00100000000020160008000012000000800002202e000003c00e003000003800200500000240160000028010000006001001c000000001000803e00100000080160000000004004001005000800000000f800800c004000001401a0060000004004003003000002a00100700000120000018014012002000000001a00d001001000002a004804800600300000000040000028008000006008004801600100600000240000000054004000007801000c0000010010004000000000000400100000000080120028004004000006800800e00100e8010008000002007400000300300180000090030000036000000002000400300580100160080048000000000000800000201000b801801c00200000500020020020024000002000000400000d00400480120000020004006002001802c01e0000008008012005001001002c029000001000400300000000000000088010000001001000000200000b8010004009009000402e0000040000058004002003401000300d800001200300000040160000008008000001000001002001d000801c00000e00000240420250018000000008000000401200d0050004012000008800001000b00080100080020020000000003000004400c005000000801000100000180000010048008000001028801000000c00780000080010038054002005000001403600d005800800000b0008000004008000002400e00100100140000000000014002003000001c00000600480b800600400d800800601300000140000060000040016000007800400000f00000040000070018000080002000000c00e0020000004022031000000c0020020030000006017000801800c000007006c00400e000000003a00b00d01000020020140088006003000001c014015001000001000300200000020000000010002017002800000a000011004400000900300240000010020018046000000000000e02700a8000012004000001c004004003002006800300000000000090000000000003003000400600600280000060080018004000000000001801c005001804c012001000001002600200000040000070020008004002012001400400100100000060010008008004000000800000000500d80100100070020008004000009800401200d0028014040005001002c008000000000003400400500000020030008010000003006800000e007001000001600d005805401600000e80080000030000008002000019004c00200a000011c000001000005400a00800b0000000003000801400c017007800801200e0028038000001001000000200200000
  | 30 => 0xce3591a586c106a011119f61451bf042995885159dec051005a0b48cb832e8b7a16c0f1016589de8e694e82971cd207d83de551085e4bb1de269f881c64295c432d1a18000001652d9cac1e10f4a4fc96f25800cca0001f0a000019a000126800008587ef9eb600000000fe800040a05da00017f0920200252b99ca56f20566ce82402019b762248000000000056611526cd000090d17240e00000854807e18282b45dd000085f800000023425048520640950878d1f3c0e6053600000007db1b7c14880002639e4e000000000017dc72c9e7c84b0f764d3042846387ca00022462c0152e0001d1c000000060e83903500edc1f98e5e2bd800063609ce6f29ebc0150000000000000022e047694280001a4200006ec0d40d943789f18850800048b173e6cb13085a80f866c61ac41978f5a7f5a12864e95568c20b04700924024180000000c9e7c78d6a000000010a81f000000000db07500000af4000225849c000000000000001bea00023e231b206092f844868c19b80fb000009e95cc152865810c08f01c080007721b6c0000e6a28524946f895605fe89482dc18484c185064e61dd481f893200017e217d98be34000002d217380e105982f30b6c000236065a08323f98e7208a80006a41d460860d043e0040042422805270dee6a49cf62238ccc86c908c22585dc5e413c83f580b254b00000d610760dd098416421c400012da000000015a886274f993451498fa3dd00006109f048db8e688e7853a1cc9fec248831a03f1c6476c00001499b6672280001d0204c2fe800079700008b29f86750a0d25779a988aa00008c982f488287f843980008588cf2787800069d82125758aa07b114683d88d6c8501ad890500008329c2e18b8c1e5918ed48b018c25d78482000000021b11f48609e0e07ba06c083947800011c85c280005e60000000000068388563bd8000000087000000004da81381ee03540000126572807c20e081a1ab1dfa7359f6000010e43ae0bc000014aa000000027880004c48000744800090b0000000106a83e86303ac1c42394091c1a100001291f285e121c07dc0bca25b905a2ed800088f800080322b000010686f712ca6b2000018a22f27f8032c8c81c0a2bf897e0ff00002729bb041200005830f0c00022ae15c800087402a20001f6637f00e200000000000a308cc1f0c000000030d195a486a08a21e9a4455ea0da0000000271800087c8fe42b18ec60000c4a178a3ba000185c00001042209938000000000014e40001b1c000111c00001c2000045468300000000000133000064187005c50000137800000007b21e9a0e229a9c7800023b40cb893e002001001400c0020000000004000800000c0020038004002000000000000800100b000402c000000000800000700f801400a002000005800c00700100000000
  | 31 => 0x168c3d204123ec0d3a56c000014d0e8a0000b2000000002c8983261e872a62a86cc1c11e3c0c500000000000509972a31f0000000000025c0ef0000000000000002d1a2bc378093c085800082a801e6461a085411e14000000088ca138000212a000198236b0c620bb99ee02100002eb182669588da000000000000006c09e2c000000000021da80200008fe84585a99b5c0000cf07e61f342731a860000d680000000000000000020bc00000000001c3e00000008491ce420122ec000000057b1c0487900001e2222c229196c467803a4a095643369c24609066e27f1ef24730e265f6800088901544d6897c0c3a30c1c80512538000088604406330f3a1b50e520731882219119a321861c0001ba62401e1c00021ce477803e00f131c266183e45da39862d065450d0e563b089a84af01521da94be4531bd418d92147231b2a6b58e585f50e3836614c20f68d0888a9930000238e80916f0000000050a800000000008469afa0001f4a466201a487962005680000ee1d2400000ca3b111dc6fc80524b1115c2e100007571dbe000154241f80f28be07ec0002410000149276d800022c18623760ab2000240a5ca23123561bd800004a20c618d03d786385b10cdc000141e1f305163541fde16b80005870ba2546a3960000000051884e000000000000005f9883c0a2876247e8fae2b50db07a81a9417d00005f6000048a1cd800016be0000c0a7e2800030422cc2df929e0158aca00023c21a2824c1e3858488e9c508d919a847100003e6800059c0e6c8801ee43b389888f39ab04b404e6047028c4521e2637e06dc36e06ca08223f004d00d0057012255312d419d23a227a050470d0ff68ad127289580000fc879c602863a0421e944b187b00eea1786f800400b500824ee90be64f80000000c7607e9f1a7a8a25a67e800084611ca84d92080000de44cc88f81231f0839e02dc8760496422917a6600fac784833a6530c9a68b80008f194861c411c60ce08cc42a0b720e8817808c80001311788242800000000000001f2a0000da60000dca0000000000000086d23be7f4077610f163200000002939efa000150014c868650501863458e965d612cc6b70b8257016184d71f4854a00002528af0000000017204d200003a43ea00002268fb6000000090b800015602345549e4c7739154063244c417929403a000009c800000000002580000000000040e944e86d800026080000a480005bb8efc00017400001a6486a9a8a4a980000531bd600000000000f0a000128800000d406f1ca4000009c6a3112046f166c0000bb463c8000000000071680007e8000067300000000000919078a36d949e000101c4500000309000038095780f88094603a2ba155186000011f6000075e74595400001206909216a1fa1a025868772277183414f244e08b18
  | 32 => 0x25c9e7e5d120863cc85660001984240a1fe7b200001c588d609e04fe3eca19c0000000364136000008b61bd12464998ce200020ee0b900001d080007441c5c00024523fe916c3338000000000000018b873a000000000007d51010556a1165a12100898829000000000b680000000000000000000019d6000022800000000000a1202b1b06000221c7818000000000030880001fba3dc36794b20000936000138400019d253b800000005c26c58bde000140600004f26f907c21668ff07400e4e26518b212d8b2a06480005431aea19c9a0a4ce0942000000070580005b78be600007fa4b000000000ef82e59b962862064000000016e9bb86d30000000078000021764caa37c27622f60000ee667d0daa7da000012f97b60000800371000000000000001d5e07916c611d9dfe2cd127e00016c20000b6600004d61d117366a8a4068ba80004a912582d608fa2a58e9c82c04fc922a4b0000074c45605b2052239c423917070b1afe00000000000d0640815b80000f1889985466638e7e2ba08b200013742669448574902c0000b3c66fa2f43e51ca61e4800060304865ad9da26c7800022819e45a0000030e0bc64b2001a5fa800050b9b7850b041e00004c60001eac7701e8a0c70c468fa9df60000660000000000014a64aaa0be3c92264000000007515324ca220e000225e0000c8a8ca89a668d038c6e413b068a18521f6830a79d201c37a822041b1a800001ca083d14d048395c239b975a00005d4076089c0748ad80000000000000079e00006d59e8c74300006d88000000014e502932e27580004c697421ce0e740002386000208c1ca02d650f0184000000074c810a7c90cbc000209617580000000b3a42d8a385e396282220000000234864a0000000000000000002f0999c00000007e41ff20001bbe5849c00000000000000008931f160fa940e407a1e86d6a4887fe08d26ea01ce00018ae5d51ed03220c7275f828452b21a20e5893400014d81d8219e1409c200269e1667a87be644000000004d011d15a26b1900c000245045d23468fd82c21900fa046500007591fc4000127c3c5000000003647cc9cf862e8000595012e7cc0b5a1138000024924a4fb24901170e1a383000058797d661a80007ce8000000019400016d000001b837987142ec002a0001e5a06b8962888087c16991567468cc20001c2651f24ba34d88e6611a42a04483866f49546370a36c000000026a97aa130151647c9a544161b365928e9867695e049495a089800000000000000000069320100001e2867084200a208a223c8d8e000236825792648691a8e19e9a6223ba46259f09ae1e30eb41fd172692e07fc1eb037a3b917a459d8bfe13904e24cd0cd05c1204e1fa800000010e0861943828988360000a6e22f8000000135623d0000726800061980000
  | 33 => 0x2009cc06f386fe0c093ce000000000000000000000000000005f1d1833223f869d00000001e703f89c1c00010d6000046000019a200015d400000004b091380001ee61578678062800080b1bf6000000000022e40c90f441c48000000000091b00002c79e0a88f072c00011ec2d51a1a7b78afc47c23e40001ffe4368028146912265813ae2951e420898a7e7561ee222e13724211624928847821990144d6000000001d05838d4843ba45a55d8eaa74b20545020b1800018ee000010c00005a200015660d480000001fba67017a074e97ae0000000315a1948fd0da200012780001d1e000125675d845039687dc0298dc04a421ac1c687d432000001af00002e3988a862123054500000000e043de1ce06981d8e55a0004003825038e81de832200a30e9ad421c800083f0eea0001eee0f09a460000b8c18b1d502a080006020000665869c659924809b9dca000000089b9f6e81180003778c3637715da12c0000000110467800003bc80007fe825a2af0c901a48000000231e0df00002f58000000033e000241e635020a7d7000063e04660000000533800002f800071da41c17a976608c00002049a8800000000001636000086a0000000000000030c8000000165600024b261580005fb8fda0000000847068c00000000000000000000012a00001e1879091980000000000442119065b800079892d600016645ba11c03f70e0a00000000000c06699894e73f0d0e327000067e0dec5b6106652203d400009f6000000000002a05179af071d00ee00001f44311abc7791fa200000006f1927a00009a0000168a0af00003c89ff62590000000000000000004250e2800000001ba14f016f80004c0079629a1b541268c925d380008b70000000000013d222e114800061c9f100001bae0001b9a777856079180001e7a268000000065c195844080cc2e61bf45088b6a096104e37d8e5422b054475814f25f1106040f849275515201b3a09c00006e64848000000002400001ec35f83a688da2d255c8ede01b09b441ea0a400004d44bf83dc6ad059e00011aa33900005ae80005b200000e0800000009d07b397ac73100008cd86fc000000055b9aaa00020168d7905634e083e1ae826224a0f1c31806fa00016588581d22000000059a14ea000037217c97a87f319785978000002804629da25c7f185a46f780008269d0666793465c8870c000000057a211e0001776881001c5bf9fdc7cd9196000050e03e00005000000262956c409943a7180eee1098000000199800023c081607f01f4867c5e703100851430156a2100000ebc10393ea00000002180cc0000000011c90324b381da6550e8e64902be79d90b4000000000000008b89e3646e8000567800000000004ce8b6800000008fa0114000000208897080001cbe14706be0001b8666b00009150
  | 34 => 0x243e0001d4c5d91a3c00016085a61a163fa0aac000102e24403ee84c19d475589305ec8ae67b1810600000b615c08ec15f00000000000164843a408923600000001d61a044db8fe033f807473e8000000210a16d0a8a0d89df21638c9459f93f62c58d880000ea0000202217b13d612b18ac790060e1dba19000000004880000000000035800000000000374000000006aa00017d20000da80000fca57c10042a70000547025402c0000481023a1f18e066eb0dd63fe1a780030b7c00000000758ab81a500002e99c6a11590a4611069a0f10706000074e830000070e230e3ce000008084707dc80000000a6400010ba6231124000041000009da0000000110800023a13be36f80004df804c8cd10f465006900de14cc65e80000000000000000000002c400001a43139e9a48c800072408c20000a2c60806267b010c86d08d823880646459a27845409e03c38e220001c7c02a09f2000000054d800014915a46dc1c145df05b63a119427c9800011f04da17819c64d0854c00000003ff00000000854086800055a92f63921e040000000563a4308600f900000000000000000000000000000000000057624ae5449a2a2b596a41b1862006780000000ebe0000d18000111602206c4841a3748cc912a75a065a2b4a2c85b30bbe3030000000077466980aa3b00c4c00000da7e50f683670000028000072c02ce00001ac5f404f630109781dc0b9e63b1da80001a1c89280000fd9b000000c500002000616181064210b80001c3a7e0106e5bf105c7ae93e871f8000443084891a1f8e50616168b0807a3839ec252391e61f0103c3530e6274b8a2401997603bb0f266f40ce01d48b9061d0000430800000012f42a5000002390c6000039e09809fe3ca96108571ab835c0174000144c09a936644f877a7ea21080050000000167412f21ae75892983da800067ca4a080e800078f8d86390a0b60eb8d3400016ec461186c8e08df00000d444e81cca0c1232277e18140000f727710f8e5bd23c828d8000000205000000000000e3424582e20830c3c1a7973434ca310000107c0d180002c090e85e51af844ea1922fb12ea60605008f290387bf000036f168e731a3d800018f046c025c00023c400009a42af92623f408168da80007b48f1e00001fe335940276c83d818d0b3e25b0c4492701e8253203280499e26261ed68d6a1dc8d31e246a711a02d4a1f8714816e3cf11ae48a9950000006e5a200002fc9d36000062a0000b640dd913400002f048310964591bb400020e8344a4765a51404759a0180001e9c0c318e4512800033b89ba52080001ed8f500000000625800015f81a2000000000009b83a699145ef8a581f119e6000000000000001f917ca00019ec69c8db4640202e00010628fb1eca0541030193a4120000000168096800000000000164
  | 35 => 0x488c0c180001aac00000005d180001428da4652800004e82ae0000000478170c03c200e4a000000509e68375090c000000020880001f8a3182fe1dd0167058a1169078210000000000000001cea00000000001abe0001dbc00013da230000034a004800006d600015847630a4088680000000dc84bc83c00000e826e38e080ba0000871962683d89a201780003f798b043c195216a80ba00011865550fcc73084ca795856e6ec800005c0e1c7b322400c18000000216800000000001e6e0000510000163a21a05e600005183e48a524d89a3a8d11202443914a6bd969a85797f83a505d8231090e1f200005e9800047f15ee3ed0f6e4289f9c0001c0893080004ba00006388000666813009796ca1b7800014200003c4800000022a202d0000000051e28022486db800079108dc39c000000000063288000000000000000003ff9d48508150e5d31f7603205ce0d000007161aa012aa49a38b887845a20764e7800000020d00000c1c410125a8f5195e7f4996445390d22ee800062209c471280225d2a3a607a86da1e8a47a85b85c0048046855381180000000558955e25183b67d8800007709d230814540000b1263a18dc4de8000000000083380000000000890870e00000003d812e60001cb400006a63b880003730ac4000122666d800034f9a9e2f500005e01b9234080007af800027d20404f794fe0000000000206a681800075c8ef42821df41b882b22061ca2020228c6970ee84dc143251716d44e49534000076c1831678000008a000112e4db00000002052645809e04a22b666a8cc40001c10254931e0000d5231f9ef691b844a0002356619000054780008f4095c8240000000000076411ea3570e10739800000000002c190c010b000000020ac8fc800010e0000000000082012422b79e6669c0000286950a89c80001a59a6a00004a01a20944288000082e822e4109b3e1b2057a01a04980001aee0000e9239f14844b49e8264f240c15d00000000a9083805408d9832077b8e8c0001c563428c283a1a04860896386ee9b521630f7e743914480196c06dd0bce0361bee3dc126c768078257e190486f09e68d51a1e3481f5268e0c1a887971223d8f6c51c8000424a1200fd0afa7df00004d515024d11da600008b4000159c0001c220000000460800093000000ef0000000000052800006da0000000000059700004a2978c00000008c00000764a4b600016aa00000000002066063a3da8e3000068c81e664b22863e10e4a7da8c147f90000780a14a36ca0cc51b205e82ba35c43899928a9172e09c11a4538970212523900001a9a0001936000000032b1b840109a220f9a2b2894899c433918878a98d683c1e202830e9e620158289b1f2c2fd879a6c2907051824204fd0000000011a2930b361b803082099e301370f1a0000e6412d
  | 36 => 0x400002d1192000000007bb004e19320ec31a8fc84e007b42ae88aa1a021c26c8133c1fc873090d800022611366f1004a46705ca8ae184a044000041c88d082e1c4e6ff9b240a98000000000089d0a1c8398dfa5f302de0ac0a4800022500001cb828080003f50356596800000000000001e886740d1a3630c7a72f17002c3926a00000003fd033214b000009b0488865835e6de834c21114d681f0316000012c6d7810e63786b676283120000000000230664b982816206e40c98ce64a8000000014b82b213b81ea15945f780000001dfc2ac000030a92fc00008ba24e0d8a0b81bc01f5800001100001be000027c21ee0001424552a1f40000e2400000009068c3e06f8c6e00013a623a8a0e0579672171a48e70c238a6e71b1032100005a58d7a1b4a04a000041c1d2946e000000007888c84d00000591101609a161420392b68e21244357947a00021e018600000000a32055875c5c80d9680d000000000000000676000000000003f000000000001f4e0240000000000000000004a680f6000159a00010d443f000009f80004f5229000000005790778604966e1e91fa665a9e58000000017b9d9c4e300008c908e01730ca0184088648d1aa436005d037c969e00007e000003ca3ac85382ec8000000146a61f970e5070000773000021d023c0000000353a2d6000000000000000a600005fc800060c12968cea08e00000000001d042499b7e92a8f4e82c8f643490f2c3b68c5c47ba1582108e7a7eca43252a0436720a49e094846e827885029893269060ac000005a825d1b408d00cb28ab11fe1c20fa455d1bfc27b0bc85188424000127402300007f2936400017967350fb806a00121ae083064390f22aa9580059800070c80008d61a50474800016e000068480005419d9a4c9092c7b701621ad16ac25600005d5987c84ba2263d609200001f8200009e41ef000000000000c8834864980000001782830920a73321d46238b303e78ca8009948c387a1b02b883be1b409bc65d0f7c83e0c2c00017b05739ed88cb014a46308520db88bc89ea2341c980004ac83280000be20000ecc2cb09566ca10463d5857600001a62540a3a29e845e00020201f613bc15b0d147bd15900258e468540000696a49657d800005002aa36b800067f80001999b6000016028b199ae903853e8439b0c00000007039cf454a80007211e485b383f82c98a4237f937c825237a2919018350800024688907c08fce2a980006e5133e61a0a780000e806c200000001cee3a21490192075a74f24746e8987059895e28c1128c77609407ef0a0684d0cd2078060416f1c4c7121e1091e019c6bf1e1847890864840e3073c877c40a80321d5a14e0b99d943c81f143518b0865f8000047953c0d9a2d00001f001cb8000000175c00004d85a097ba28780000000904632231
  | 37 => 0xea34b000083c9fb005800000001c9e7f60b9a01e098654c00a427e8000000000038b000057d065218f0cc68ec88ce537800080511a86b423764b89ab256980007a9800017f1e6c414077e095838e5da1dd600000000001c280000a104a700008168000882030062700008a483b400017e00000000000160400000000000000000160a00018c0000066c000000000010a06ef21f03739f8483793a28ea0acc4ae9aba160048a61394e676d1b0e76a87240ab10ea0be8698845043492091e43fb21743f604ec92480182dd8ed244617ce106082087588a65030b108b98b2e3559ea82e805fe420887644c92fa18f94ec384a3803e223022e20b625069d0a565824a55714d42e196e27e696b034c17c2754a0d47800c16000000014311e832d94bc00000002959f406b81bec85c00000001fee1fda1442600000632812a0000c7860b1fb491f18400da98003361fe27ee05f02020000000013c4f40000000007675a80003a880004a885d20f300006680406000000090880000000b4a000000050f96d632c0a347c38d4a57a8d6223f095a8209a4a8c28a844a49de64440cd429c2384625046477704a63098fc24fea0a20bf8dd24f30008000104482982946d9056451616303f10b326d611d67e90d781a884fa02f03d216b0a9800b930c866800000021ec46e0cbe85500008818000000000000012ee000000020e8000000087e44a15be4e682b65ba800000000000000af246d93480000bc40000bd827517e8000000047400001c6202a0002298000226a8e50faa03d1c0647e04ae0e70cf626b04464578000092224e6840cde41298a68eb173c1e80d1c32a94660491912000000075d15924890e2a2d821ca4f7000046b191c00000008ff83b26cc800061780006a080002a193882db800074c00006479d7066ea07491c8000000000000001a00000fbc84f16e400014c08f4945a00000008bf13e0000234a0000000000068e127862411a867e06d00384ad0d1e27e0d10629082c6b29f9e2f680004b600000d0998633e203e5200f527d4000027010bc19400008830000000177e464888a51c0e9000016dc000233e5d491a67c1817a811020672595b600000009180f96000000057f89664200e1460191123d08a8e510000029285860000b740000000000135e00000000001aa60001fac1cd0a9e35505fa0001b2244011d877a032a5dca37e63982ca473839a20799b231003c81c780d21e502645c68200000000000018f60001c3c672123a3719c5408e0c5e0a0981e0e297861ac0b1a7a40fee5920dda0a723b82d59994404866a00000006ea99468a380365fd00000000000300000010896668ec084c6e0039486122da000000008780004ac000000000005059cde79aa03660d800023284b229c8eae8660f4c29d016a7248000000000000001c443
  | 38 => 0x5682fc1ac87ae06d800000015b25d21a5280c0adc0001d8081c1d8400022f00a79d9e0000d92000000014c138e1d900000000a8074514944eb00e600024004de1a6c00000004a1a17200005e4000000085f000079c84326e6177a00015d069b8aa27df93c484fa4a660081361ea8c422810e3e4479c860000000325a16c23f9ea42ce15f2801043e84105e818493364cb0b94581945043e94f80358b782d793a800000008361b725b819568d41faa10200e4157198874997c0451917e548800048f9b142f91948000218c1a096b219a1b8c5118a6c0001de036800008de0000000084a75e005074814da2e4800000012b800007d016092ae869888084e8c5a00020843a90d6e689834442b80004801f3871a07684e5176c88580003d012dc2f41db86c6a0a02e912760f38d5a498110a669112c9161bfa54e8de85371ae291c15fa25d83d6297a0e41f38ff20001f228a096428ca08106bca33c00021220381a7a4e19fea6e90d9a4ff1c94852067009d00007a480000191b4692d000061422ce24a8e66000195c8fb92be5cc19728ea9b440188fa27c493220bda07a2a90f342679e7a6f991c2030a49801c9e540001bc200000000aa00001850c8c2ea000020b8fc600008d4401982e0000c0e2911d407fc1eaa22306222c2976e0001cdc3cf8e0066280001c7134a4ff9dda59494f600015247a7800045f1eea000247e000098c8849fda770a29c53107fe000000051da36270a8000000000086e116a2d712f81559ad20661d3810581c039d9ade000092e80f0aae1588be800000004151b9e00000005190ae000013d801a800000015508cb8000000105200006ea000157000022de92a1c70000000042c800013a000000011b4000169269000008731fe68639f64017217a7ba16ae4e4122e06c12e063d1f5840080002fd125407c971c751118a4689cda6fa047a4c0842e5e4a068711821c3ca00867948000000109a20d11300000cfc6210000000245e00017c8000183c2031ace62a0aec03795c6238870a50409907e48c485b6955856b958a4dd91783021c1248f02c64ec99c44c801c80001f4c13c00000001238000242800000000001a5e74a80008f5800000000002b9013224900006b0a0c40000000000000000018ea00000003150c660cc16408d48000000023685580005ef0000000158c8099c8e00001fc6e20cea0001cc8000240200013d26f680001e61ac04c39ae413e12de2ea81727a100003e986f60000b4c2a686c20cf17e43e3244821190fe0000a2a60e14fc63f860061b89b22d09cd000002ec22522c47990f7a00c21fa65398b60ae9d96774800081b9ed47b8000065d9c0c123a14c244a0921bc824e56e90007e302806bb1a245b980000000b241d194f47f522be4a1000012102ea1988ed072e8aa820293c07f00b402fc09
  | 39 => 0x61a73b16bc00005503499b8a760800068014fa0000eac5ff83340b2015807e09b0807935008f90f6526881400016a22460b8a4a3800026da0d604f8000000125e8dc00000001f2053290d802624868a20000606846200023e071b19d8000000012e000041900000001dea664172c5d88d0c22a000040d13960f4000000000000f90d720001f427e205f831618a08170824000207860a9f5e6cb8e4c63f109e8c580ea3d71518532213272a000077c1ffc0000e6003706ae8a68c2e09f1b6a47519f03b298da8ff227675b882892903364cc0be00001eae65f1e387eb8e367a0000010302445ae060887f024635d131848618a20600f548c70ea604015aa4509b4837d00000000000717885a00020b40000a60000000000003b000000000000000000000006c8eb600000000a39dc6000022474d24bc000000035980000002444000000000006a400012f027200002ba865c598000080e20a87408a3e00007223c1a23800000003f00000000108858b80006fe04ea0001c9c00014b06e800001ee8000000000006e8000497000068500007c70ca60289d982b083881509cf068d896a6430f164aa000000000000000b8000000000641c8800010dc4f29dae000000000000000338000613000051d0000000139c69f1efe000000000021e246014b45b4835c0eaa42656d000031c13e600007de4fe0ab600004ee43b00000002404000093a0ff966a000192a4ed22944da0f981b020dc5c402c01d9841a00022a63d99c1a6aa211239718e02b39718862963c66f22a0000243c6cf0e167ad0a164091f4621b829a81882a428b834e6b68b504f88cec8bf94c67e58548756985415a00000eb21be0080e4011f8b1400010aa66318c400000fa00003923049e085f1a44674223e655f873c000163e1910000000210292316b400004ce00014367cf82d01b60d7c5e69316692000002e15a8752800001612e40001e3a0001e9867780008dc8954000000091700000000000792800000008ae3b81ff464c8a5a000153e3149c7200416864e287367f09bb649380004f08eba0000d841aa00005ed010276902cc5de00004e9024288898d251f99fc8109c620000f0057f00001bb90b03e099dc0001b126b30000849944200000005770c8218c840438c80000000000000000000000008749c1e6d41962761912678c80000000ed60000000000000041d00005dc10ac11b00005be09c25be9bc82a49a2089f097a3c0a416626a2d83b20efa7dd23bc59e90081548266000116005b000045b800000003a00001fc80000a508e4909c84416340000c6854e0d2e000124c0000bae859061e6241a4e6b9a3b652ea3cc31d101a3e28ce8288a28a000209872aa1ea00022fa6e091142279eb02ad0bea8a5a0ea282a3de494162c180a484192a10c8779e6091a9a9666d11624
  | 40 => 0x71008c600000006d2800000009be7a380000df9e2e706157c00015480000b1c85193c60001b262e7036000013f05da80008b515860000b0c6ce02d84f91cae5fb01c63c21eb889c17fc2450a3c03f98765aa14985ce9c7a0000f9c3ee87540001d888569f565cc9a3e92b18046468ea8000000013090cc5bd8b4e2391f5a8ce24404c5073e66c04805349650485800005f80004d494a41320fd200b1d28000085c13810f82a3017600017a21ce8ad02ee00c4891181c3b6040a000065602b8e3c045a1ba065944414a8f46062178a00000000a58c0273f800087d80009129c6623600009108210299a1a875e866476ea34e7ed80006218000000028652880002f7231a720040283192ac88082b83cc0a28000175086800003cda2aa2b68000000003490e80000000a8857200000000e187a18bfc00003c60001a6867a0cfa2210c30153800032b9c6e5e79f4418182766ab8e447cb9fce0da113c7de9dac27ba2e820a95e61650000060931026480006d39d7c5a411b217100007260bd270d9ce2185a43880a23a049b981656b0aee648930a26580c60c780002be0c64000162a915a27e7bc169c01c03a80f8034a3cb81aa43280ec177a2847fa049c7940f0468b00000001e0c7de000000000000dc0000000000034aa166105185a15e104c0d6800005a20fe4038d76788800048709083ef8ca414a00000181ae840d99ce89510980fa18c675b091e62f00000810000522911a0001af48eb80000000bee0002072124000058880008e902f8437800000021c8000151079792220001878348a40833d1e1a4d386f088a1ab600002f24ea8c984028d3c6a1170603006426510efe62797f67339d4e822229e4c113b64fb88de7be1c4472d8fea29f000000011be11318925ee14962ef164c88507487ac9eda5c79bcc8bb93826cc000045c81ca7a5852e323952687984ba5c591060000dba000164e2ca0
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87f87d8a51440018dae5b14a2880021fe1d62945100051fc22c528a2034a3c8458a51440014bf06b14a2881369720d62945102fc3e432eb98a204b87f87d9731440010fb0fb2e628801237e1d638c5101554e422c718a202eacc8258e31440bf0fd0dbaa62882021fa1f654c51025c3e43eca98a20048de839d8314400187ce9b2862880030fd95740c5100061e32ae818a2005d34515d031440011bf0eb1862880a2a7211630c51013d66412c618a200587e87d96214400b0f90fb2c42880031d19676885102fc3f436ea90a205a87e87d9521440970f90fb2a428800317d9773485100062e32ee690a2000c5f651cd21440018b8ca39a428809f331887348510006aa288e690a2000ccc73d8921440978e8ed28a42880cf9918a514851025eb8384a290a2033c7476dd521440978e8edb2a42880039918b65485101766a3b6e690a2027cd4761cd2144001aa8ea39a42880035cdd470485100043fc2aec982200387c855d9304400117f08bb2608800a2f211764c11000477c12ec98220018ec825d930440010fd0dbaa60882a61fa1f654c1103cc3e43eca9822000c3c74d95304400187ecbba260880030f197744c1100064e3a6c6982205fa7a86946204400bae0e328c40880030f1d365481100061fb2ee89022000c3c65dd12044001958e9b1240880123da1b71481100063a32ee29022000c74651c520440018f0edb2a40880039a18b65481102ee5c3b6e89022000db0741c520440a14f50d28a40880171e1da514811002eb838ca29022000c3e74d97104400187ecaba620880030f19574c411025e3d3b6cb8822005de2215cb10440038f4eca96208800e1fa1f7558c100043ec16eab18200587e81dd5630400b0f903baac6081e21fa1c7558c100043fc2ae8b18200387c855d163040078b8eb29ac6080123721d5358c100246e43a86b18200087e87d4963040070f90fa92c60800237e0d75588100546e41aeab1020058f4815d562040091f100ba2c4080123b21d52588100247643a84b102001a6c82dd952040014bf06bb2a4080fa9720d765481000537c12eca90200087f8758d52040010f90eb1aa40800e9ba1d625481001d3643ac4a902005c6e71589520400b8d8e2b12a4080f399c4162548101e735082c4a90203ce6510589520400b2ed0fb8aa4080039958b71548100053ac30e2a902005c76761c55204001ccac438aa408002dc60071548100043fc2aed990200387c855db32040010ff0abb2640800e1f215764c81002c7a40aec99020048dc8758d32040091d90eb1264080031e1d7764401002f3928eec8802000c7b52dd9100400b8f4a3bb220080171e14776440100063dbb6ea8802005b7081dd5100400bce4a2b122008017b888562440100063dbb2a48802000e6962549100400b6e502a922008002dce152144010
  | 1 => 0x8e9a92c6880031bdcb5258d1000e36396a4b1a200387e85dc563440010fb0bb8ac688003391cb7158d100043f438a2b1a2000c3f741456344157878e828ac6880031bdc85158d102d636390a2b1a20008df8758c634400153908b18c688002b32096318d1000536c16ebb122000a6d821d762440010ff0aba6c48800e1f21574d89100046fc1ae9b12200a8dc835d362440010ff0ab9ec48800e1f21573d89100045fc22e7b1220028bc845cf62440010fd0e28ec4880029b60851d891001c3f436eab12200087e87d956244001878e9b2ac4880021fa1c65589100061e3a0cab122000c3f65dd16244001878cbba2c48800317d9773589100062e32ee6b122000c5f651cd62440018b8ca39ac48800333188735891001c3f43eeab12200587e81dd5624400117f08baac48800a2f21175589100046fc1aeab12200a8dc835d562440011ef02baac4880021fa1c75589100145f43ee8b122000c3f75dd16244001878ebba2c4880030fd4b74589100061ea96e8b12200087f855d162440070f90aba2c48800237e0d74589100546e41ae8b1220008ef825d162440011f700ba2c4880022fa1c74589100061fba8e8b122000c3c751d162440151bd0fb9ac48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac48800317d4b73589100062ea96e6b122000c5f751cd62440018b8ea39ac48800327dd073589100064e3a0e6b122000cac74dc96244001998e7b92c4880031d1d771589100066a39ee2b12200087e87145624400187ee828ac4882af0f1d051589100062fb98a2b122080c5c7314562441558eee228ac4880032e1d370589100043f434eca922000a6d829d952440010fb053b2a4880031b60a76549100051fc22eca922039a3c845d952440014bf06bb2a4880fa9720d765491000537c12eca922000a77815d952440010fd0c3b2a48800e1fe08765491001c3ec10eca92200587c811d952440018ec823b2a4880031d50476549100063b108eca922000c75211d952440018f4403b2a4880031e48076549100063b080eca922000c74101d952440010ff0eb1aa4880021f21d63549100051fc22c6a922039a3c8458d52440014df04b1aa4880069b209635491000c6f41ced992200087f855db32440070f90abb6648800237e1d63cc9101bd4e422c79922001acc8258f32440070fd0bbb264880021f617764c9100043fc2aec992200387c855d9324400117f08bb2648800a2f211764c9100046fc1aec99220008f7815d932440031b90eb1a64880d6a7211634c91000d66412c6992200587e869da514400b8f6c13b4a2880175c04276945100043fc3ac728a2000a3f8458e514406947908b1ca2880029be09639451019d36412c728a203387c865ca51440678d8c4b94a28801759885729451002eb8082e528a2000
  | 2 => 0x1650c6100061f32ae818c2000c3d655d0318401593cc6ba06308003279d1630c6100064eba2c618c207cc5f7598e21840f98b8eb31c430818f17dd5638861031e2e3aac710c200087d86dd521840670fd0eb2a430816a1f21d65486100046ec36e690c2000c5e65dcd21840018bacbb9a43080023761873486100062f328e690c2000c5d651cd218405d1bd0f31a430802a3721e63486100062fbacc690c2000c5c7598d218405d1bd0eb1a430809e3721d63486100062fbaac690c2000c5c7558d21840874f30d28a41080021f61e64d95100043fc3ac9b2a2000a5f8359365440014b906b26ca880029be0964d951000536412c9b2a200d87d8718b654400147d08316ca880028f61062d95100052f418c5b2a2000a5d8318b65440018dae4316ca8812e9d21941d95100071a32283b2a204bb7080507654400187ae83a6ca8800297a0c74d95100052ec18e9b2a20afa76811d365440974eb023a6ca882ba9da0773d951025d3ac0ee7b2a2000c5f739cf65440018bae639eca880021fa1f43d95100043ec3e87b2a200587c815cb654400147d08396ca880028f61072d95100052f418e5b2a2000a5d831cb654415b4ed02396ca8812e9d60472d951025d3d400e5b2a2000a79801cb65440010fd0f216ca880021f61e42d95100052f41c85b2a2000a5d8390b65440010fd0e216ca880021f61c42d95100043f43c65b2a200087d878cb654400147d09196ca880028f61232d95100043f43865b2a200087d870cb65440970fd0fa0eca880021f61f41d951055c3fc3a83b2a204b87c8750765440014bf06a0eca880029720d41d951025c3f43e43b2a200087d87c8765440010fd0e10eca880361f61c21d95100051f42043b2a2000a3d8408765440014bd0610eca880029760c21d951025d3d40043b2a2000a3e84dc3654400147b09b86ca8800297a0f70d95100052ec1ee1b2a203ba7681dc365440010fd0f906ca880021f61f20d95100247ac0eebb1a2000a9e848cb63440bf8eae228ec6880021fa1f6558d100061e3a6cab1a2000c6c72d9563440010fd0e32ac6880030f1d06558d1000636390cab1a2000c3f65dd16344001878cbba2c6880031bd977258d100063632ee4b1a200087d82dd5634400117f08baac68800a2f2117558d1000477c12eab1a20018ec825d5634400187eebba2c6880030f1d77458d100043fc2ae8b1a200387c855d163440011bf06ba2c6880023be097458d1000c76412e8b1a2000c3f751d16344001878ea3a2c688003271d37358d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000637c2ee4b1a2000c6c85dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c6880021fa1f5258d1001c3e43ea4b1a2000c3f74d49634415987
  | 3 => 0x6b1c2002c9c7450d63840091bd0f192c70800297a163258e100052ec2c64b1c2000a9e848c9638400153b09192c70800297a143258e100052ec2864b1c2000c5f759d5638400153d093aac708002a76127558e100052f42ce8b1c2000a5d859d1638400193ae83a2c70800387d525458e100052f42ce4b1c2000a5d859c9638400153d09392c708002a76127258e100256d404e4b1c2000ad9809c963840015af02b92c70800297a147258e100052ec28e4b1c2063a5e81d4963840794bb0b292c70800237a1e4258e100046ec3c84b1c2000a5e8590963840014bb0b212c70800297a144258e100052ec2884b1c2004ada8010963840015b300212c70800297a177158e100052ec2ee2b1c2000a5f855c563840014b90ab8ac708002a7e117158e100054e422e2b1c2000acf825c5638400159904b8ac70800395d465158e100054f420a2b1c2000a9d8414563840c7c3d0828ac70818f876105158e100052ec10a2b1c204ba5e8114563840014bd0ba0ac708002976174158e101546fc3a82b1c20288dc8750563840014bf0aa0ac708002972154158e100052f42e42b1c2000a5d85c8563840011bd0e10ac7080023761c2158e100052f42842b1c2000a5d85085638400153d0810ac708002a76102158e100256d40042b1c2000ad98008563840790fb0f3aac5080f29b60a7558a101ed37c12eab14200387e85dd162840010fb0bba2c50802a37a0f7458a100046ec1ee8b14200387e85dcd62840010fb0bb9ac5080123b21d4258a100043ec38a2b142000a6d8214562840070ff05bb2a50800e1f60b7654a101e63d106eca942000c7920dd952840014df04bb2a5080f61fe097654a1000637c12eca942000c77815d9528407b8bee531aa50800393dca6354a103e62e38cc6a94203dc5f7258d5284001c9ee4b1aa50818f171c56354a1002cbb43ee2a942000e5663dc552840018eaec38aa5080039598c7154a10004bac30e2a942005c75861c5528400ba6d0838aa5080174d6107154a100063bb20e2a942000c75641c552840018ecc638aa5080035598c7154a100062b318e2a942000d55631c552840018e8c638aa5082ab1dd887154a105563ab10e2a942005d72601c55284155ae44038aa5082ab5c4807154a100246e43ac69942000c7665dc532840018ecca38a65080033558c714ca102fe2f38cc728c207ce567198e51840bf8bce2b1ca30818f959c5639461019c3fc32e528c2000c5e635ca51840018bac6b94a3080cf1b98972946100043ec3ac528c2000c6d7258a51840010ff0cbae630802b1798d75cc6100043fc3acb98c2000c5e7558f31840018baeab1e630802b3698d70cc6100043ec36ea98c204dc5e63dd5318409b0fd0eb2a63082021f21d654c6100062fbaac698c2000c5c7558d31840019b2c7b8263080030f9d
  | 4 => 0x3c400b1bd0fa9ac78800317dd75358f100061fa92e9b162000c3d525d362c400b87ca2ba6c5880170f14574d8b1001c3f42ee6b16200087d85dcd62c400517d09b9ac5880022f6137358b101cd1f424eca962000a3d849d952c407d4bd073b2a5880029760e7654b1000536c14eca962000a6f825d952c407347d083b2a5880028f6107654b101cd1fc32c8a9620b6c3f7259152c4001c5ee4b22a5880170f9c56454b1002e1e38ac8a96200087e87d8d52c40010fb0fb1aa5880e68fa136354b100051ec26c6a96200387e85dd932c40010fb0bbb265880163721d634cb100061f322eb98e2000c3e7559331c400187aeab2663880030f993754c7100061fbaac898e2000c3c7559131c400187cc9baa43880030fdd564487100061e3aac890e2000c9e64dcd21c400193ac9b9a43880032799073487100064eb20e690e20b5d54511cd21c41699aeec39a4388003551d473487100061f326ea98620008bd86dd130c40ef17d0eb2261882ce2f21d644c3100061fbaac89862000c3c7559130c40018b8eab1a61880022f61b74483102ec5f43ac8906205e8bc8759120c400187ee93a2cb0800317dce73596100043f43e86b2c200087d87d0d65840018dee5392cb080129ea0272596105953cc04e4b2c2000a77815c965841634e902b92cb080021fa1e42596100043ec3c84b2c2000a5e8390965840014bb07212cb080021fa1c42596100043ec3884b2c200087e878c965840010fb0f192cb080028fa1232596100051ec2464b2c200087e870c965840010fb0e192cb082c29ee0171596100043f43e82b2c200087d87d0565840690ff0ea0acb082ae1f21d41596100052fc1a82b2c2000a5c8350565840010fd0f90acb080021f61f21596100843f43842b2c200087d87085658400147d0810acb080028f61021596100052f41842b2c2000a5d8308565840094f50010acb080029e60021596100070faa4a931c207ca5e81d4a63840794bb0b294c708002b5e055298e100056a40aa531c200a8de8790a63840011bb0f214c70800297a164298e100052ec2c8531c2000a5e8510a63840014bb0a214c708002a7a105198e100054ec20a331c207ce1e8414663840f9c3b0828cc708002976085198e1025d2f408a331c205fe571014663840bfcaa2028cc70800297a174198e100052ec2e8331c202a8df8750663840151b90ea0cc70800297e154198e100052e42a8331c2000a5e85c8663840014bb0b90cc708003951472198e100546f4384331c20008dd8708663840014bd0a10cc708002976142198e100054f4204331c2000a9d8408663840f9ca8a210cc708012b6a002198e100056cc004331c20048de87d4d63840018beeba9ac70800f179d65358e100246e43aa6b1c20048de87d0d63840014bd0ba1ac708002976174358e100246e43a8
  | 5 => 0x31d61c51d85200071b420a3b0a4000e358414761481794ef0428ec2902f29d60851d85200145f436e8b0a405c8bc86dd1614800117d0fb22c2900030fdd764585200061e3aec8b0a40008be87191614800187eea322c2900030f1d464585205de5db80c8b0a4000c9f64dcd6148001938c9b9ac29000327d9073585200064e320e6b0a405ecb97019061480011ef0eb08c2900029d21561185200056a41ac230a4000e37641446148001c68c8288c290002d960851185200043fc2ae630a400387c855cc614800b4ed0ba88c2900031d9c676945200051fc22ed28a4034a3c845da514806947d0db24a2902eb0fdcb64945205d61eb96c928a40b9c3e71d925148001c6ce3b24a2900021fe1d639452002c3e43ac728a4000a3f8458e514806947908b1ca2900029de05639452002d3a40ac728a4005a78865c2514800117f08bb6629000a2f21176cc5200061e322eb98a4000c3e75d93314800187aebb2662900031d9d761cc5200063b3a8c398a400387e859da31480010fb0b3b462900022fe11768c5200145e422ed18a40058f8865c2314800517d09bb262900022f613764c52001c3f42cec98a400087d859d93148001878c9baa62900030fdd7644c5200061e3aec898a40028bc849d831480010ff0abb0629000e1f215760c5200045fc22ec18a40028bc845d831480011790cba062900022fe1f640c5200045ec3ec818a40058f8865c03148001878c9baa60901e35a083754c1202f45f436e898240b38be87d9130480bb1790fb2260900030fdd7644c1200061e3aec89824000c5c75d8d304800147d0b312c9880028f616625931002d5b40cc4b2620acc3f76d4964c400187eeb3aac988002a7a0e75593100054ec1ceab262000a3e85dcd64c400147b0bb9ac9880028fa1673593100051ec2ce6b262000e1f5394d64c400147d0b392c9880028f61672593100054f41ce4b262000a9d839c964c400b56d03392c988156ad60672593100055dc02e4b262059ab8805c964c400147d0a392c9880028f614725931000656b90e4b262005a3e81d4964c400b47903a92c9882e28f61652593100045f43c64b2620008bd878c964c400147d0b192c9880028f61632593100051f42864b262000a3d850c964c400b56d02192c988002ad604325931002d1f42ea2b262005a3f8554564c400147d0b90ac9880028f61721593100051fc2ae0b262000a3c855c164c400153f06b82c988002a720d705931000557c12e0b262000aac825c164c416f56f02b82c9880028fa1720593100051ec2e40b26200087f825d763c400b87ca2ba6c7880170f14574d8f1001c3fc3ea5b1e200087d87d4b63c415987ce9a96c7880030f5d352d8f1002cba40aeb31e2000c3e7599263c400187aeb324c7880030f9d56498f100061ebaac931e20048f4815d56
  | 6 => 0x1c3e42ae8b0c40008df835d161880151b906ba2c31012e1fa1c51586200247a43a82b0c400087f8758e518800b0f90eb1ca3100028fe1163946201a51e422c728c405f87f87586518800117f08bb6631000a2f21176cc6201554e422c718c400087f855d931880070f90abb263100022fe11764c6200145e422ec98c400087f855d831880070f90abb0631002b2798d740c6201454e422c618c4000c9d7458c318800117b0f32ec8900022fe1d65d91200054fc1acbb224000a9c83597644800156f02b2ec890002ad20565d912055e1f3b0a3b224000b2d82147644800187aea3aec890002a7a0c75d91200054ec18ebb224000a3f855cf64480014790ab9ec8900028fa1473d91200051ec28e7b224000e1f5394f644800147d0bb8ec8900028f61771d91200054f41ee3b224000a9d83dc7644800147f0ab8ec8900028f21571d91202e55d400e3b22405dab9801c7644800117d0e28ec8900022f61c51d91200061f438a3b224000c3d87147644817347f0428ec8902e68f60851d91205d51f408a3b224000c5d75d4f63480010ff0ab8ec69000e1f21571d8d2000536c10a3b1a40008be87d91634800187eebb22c6900030f1d76458d200045f438c8b1a4000c3f751916348001878ea322c6900032dd937158d200065a326e2b1a4000cb7641c56348001968c838ac69000e1fa1f7558d200043fc16eab1a400087d82dd5634800b0fd03baac6900022fe117558d200145e422eab1a40008df835d563480011ef02baac6900163d2057558d200043f438eab1a40028be87dd1634800187eebba2c6900030f1d77458d200061fa96e8b1a4000c3d52dd163480010ff0aba2c69000e1f2157458d200047bc0ae8b1a40058f4815d1634800117d0e3a2c6900030fdd47458d200061e3a8e8b1a4000c5c75dcd63480070fd0bb8ac6900021f6177158d200063bbaee2b1a4000c7475dc5634800196ee9b8ac6900032d1d37158d200063b42ee2b1a4000c7585dc563480018eea5b8ac6900031d54b7158d200063bba8e2b1a4000c74751c5634800196ee838ac6900032d1d07158d200066bb98e2b1a4000ce7721c5634800b8ef0a38ac6900171d2147158d200063ba90e2b1a4000c75521c563480010fd0e28ac6900161f21c5158d200061fba0a2b1a40abc3c7414563480014db0428ac6900031ddc45158d2002e3a388a2b1a4000c3e75d90634800187aebb20c6900030f9d46418d200061eba8c831a40008df8758c63480014b90ab18c690002b52056318d200061f3aec9b0a4000c3d75d93614800187cea326c2900030f5d464d85200071bb20a3b0a4000e346414761480016cb0428ec29000e1fe1d75d85200063bc0aebb0a400387e85dd361480010fb0bba6c29002a37a0f74d85200046ec1ee9b0a4000c757514761480014eb0e28ec29
  | 7 => 0x3d841c5650c00b8ece238aca180021fa1f41594300043ec3e82b28600087f87505650c0010f90ea0aca1800297e0d41594300552e41a82b28600087e87c85650c0010fb0f90aca180171d1c721594300043f43842b28600087d87085650c00147d0810aca180028f61021594300552f41842b286000a5d83085650c00b8e8e210aca180129ea0021594300053cc0042b28603c87d879d5620c0794db053aac41802a3720d75588300047bc0aeab1060058f4815d5620c07b4df04baac4180029d205755883001c3f42ee8b10600087d85dd1620c0031bb07ba2c4180123b21d425883001c3f42ee2b10600087d85dc5620c0010fb0e28ac4180029b60851588300063bb88a2b106005c7471145620c0070ff05bb2a41800e1f60b765483002c3f40eeca90603ea5c835d9520c07d8b8e6bb2a4180029be0976548300053bc0aeca906000a74815d9520c07d8b906bb2a4180f61fe09765483000637c12eca906000c77815d9520c00b0f902bb2a4180031d205765483002c3a40aeca90603cc5f305d9520c0798ba60bb2a4180029761b73548300062ebb6e6a90600087d861c5520c00b8e8c238aa4180161fe1575984300043fc2ae9308600387c855d2610c0010ff0ab94c21800e1f215729843002c3f43ea5308600587c87d4a610c00b0f90ea94c21802ab520d419843001c3f43eeab08600087d82dd5610c0010ff0aba2c21800e1f21574584301546fc1ae8b08600a8dc835d1610c0010fd0fa92c21800e1f21f52584300043f43aa4b08600087c87549610c0970fd0e28ac2180123d21d41584300043fc12ed288600587e815da510c00b0f902bb4a2181f297e19739443002e2fbb2e7288600087f865ca510c0678dcc4b94a2180021f61d629443000636b92c5288605f87f87586510c0010ff0abb4421800e1f21576884300043ec36eb108600587e87596210c00b0f90eb2c421800e1f21776484300043fc2aec908600387c855d9210c05d1bf06bb242180021f61b75484300043f43aca908600087c87595210c0158b8e6b2a42180031799773484300062eb2ee6908600acd473985210c0091e90eb0a421800e1fa1f7558e2002c3f40eeab1c40008bf845d5638800517908baac7101e21fa1c7558e200145f43ee8b1c4000c3f75dd16388001878ebba2c7100030fd4b7458e200061ea96e8b1c400087f855d163880070f90aba2c7101da2fa1c7458e200061fba8e8b1c4000c3c751d163880078b8eb29ac7100123721d5358e200164e3a486b1c40048dc8750d6388005938e8a1ac71000e1fa177158e200043ec2ee2b1c400087e87145638800b0f90e28ac7100030fdd05158e2055e1e3a0a2b1c4000c3f525d2618800187aa4ba4c3100170f945749862002e1e28ae930c4002cb67450661880070fd0fbaac3100021fe1574586200
  | 8 => 0xea320c2980023de1d611853000572412c230a600087f855d0614c0070f90aba0c29802a3720d74185300043fc2ae430a600387c855c8614c00b0fd0fa90c2980161f21f521853002d3b40ea430a600587c87548614c0038dce4a90c2980031b5c9521853002d3a40aa430a6000c3c649da514c0974bb073b4a29818f17dce769453031e2f41ced28a6000c5d839da514c0018bc873b4a2980031750e76945300043ec14ed28a600587e819da514c00b0f9033b4a29818f178c6769453031e2e18ced28a6000c5e309da514c0018b8613b4a2980028fe1176945301a51e422ed28a600087e861da514c001878c83b4a2980d28fa1b64945300061f3b6c928a6000c3c76d92514c18387ce3b24a2980038d9c764945300043e432e528a6000c3f645ca514c001878c8b94a2980021fe1f62945300062f3b66528a6097e1c64cca514c0974b90c994a298003179d932945304af0e3226528a6078c5e76d96314c001c38c9b2c62980aaa7a1b648c5303b64f3b6c918a6000c9c645ca314c0014b90ca94629824787191528c53031f2b28ec318a6000e5765d86314c001d28c830c62983021fa1b754c5300061e326ea98a600087e87d95314c00187eebb2262980030f1d7644c5300062e32cec18a6000e1c64d94314c0c76ad03b2862980a327e19740c53033cce432e818a6028c9c865d0314c0511390cba0629800347d95740c5300068e32ae818a6000d1f525d0314c0c7a3ca2ba0629818f47145740c5300564fb02e818a600ad9b605d0314c00133f0fb2062982cea7a1b640c53013c6e432e418a6000c9c645c8314c0014b90ca906298003475d1520c5304570e322a418a6000d4d72548314c0c76a902a90629800e1fa1676885300043ec2ced10a600087f855da214c0070f90abb442980022fe1176885300145e422ed10a600087e86dd6214c001878c9bac42980161fa1f658853002c3e43ecb10a6000c3f75d92214c001878ebb24429801237a1b73885300064e326e710a600387e85dd9214c0010fb0bbb2429800a2fa1376485300045ec26ec90a600387e859d9214c0010fb0b3b2429800e1f21476485300546e418ec90a600087e86dd5214c001878c9baa42980021fa1f65485300043e43eca90a6079c5c73d95214c00187eebb2242980030f1d764485303be4e39ec890a6000c5f65dcd214c0018b8cbb9a429800327d9373485300064e326e690a6000c3f749d1650c17f4bf06ba2ca1802a9720d745943002c3f40ee4b28603dc5f30dc9650c07b8ba61b92ca182fa97e0d72594300552e41ae4b286000a77815c9650c0014e902b92ca180021fa1e42594300043ec3c84b28600aa5e83909650c0014bb07212ca180021fa1c42594300043ec3884b28600587e87dc5650c0154bd0738aca182f69760e71594300051f420e2b286000a
  | 9 => 0x75d893000536c10ebb12600087f855d3624c0070f90aba6c4980063720d74d89300043fc2ae3b12600387c855c7624c0010fd0e28ec4980021fa1f65589300061e3a6cab12600087e87195624c001878e832ac4980030fd9774589300061e32ee8b1260008be87d91624c00187eebb22c4980030f1d764589300045f438c8b126000c3f75191624c001878ea322c4980031dd9771589300063a32ee2b126000cb764dc5624c001968c9b8ac4980031dd9471589300063a328e2b126000cb7641c5624c001968c838ac4980033918871589301cd1f426eca926000a3d84dd9524c0010fd0d3b2a4980030f192765493000536c14eca926000c6d829d9524c00b0fd033b2a4980028fe1176549301cd1e422eca926000a5f835d9524c0014df04bb2a4980029de0576549300053a40aeca926000c3c641d9524c0018bb063b2a4980031790c76549300062ea18eca92600387f821d9524c0070fb043b2a49800317cc876549300062e990eca92600587e811d9524c0018bc603b2a498003170c076549301cd1f436c8a926000c3e76d91524c001878edb22a49830f0fdcb645493000717b96c8a926000a5e869cd524c0018b8ed39aa4981c2d360a73549301e52e432e6a926000c5c765cd524c0e969f04b9aa498002d520573549300043f430e2a926000c3f641c5524c001878c838aa4980031719676cc9300070e326cb99260b3a9e86d93324c001938c938e64981e3171db654c9300070e326ca9926000e4c62d95324c06b53d0db2264981db271db644c93000746326c4992600099d841c5324c001938c838a649818f55144714c9300e43ec3ecbb0a6000a7681d97614c1818bae632ec2980029da0465d85300061f3aec9b0a6000c3d75d93614c00187cea326c2980030f5d464d85306164eb98c9b0a600087f825d7614c0070fd0bba6c2980021f61774d853001c3fc3ea5b0a600087d87d4b614c0014ed03a96c2980021fe1d52d85300043ec3aa5b0a6000a748154b614c0015ad03996c29809e37e1d32d85300056a40a65b0a6000ad583087614c0015e30010ec2980030f9d365985300061f3a0cb30a6000c3f655d2614c001878caba4c2980030f9d764985300061ebaec930a6000c3e75192614c00187aea324c29800e1fa1b75585303c43e436eab0a600087e87d95614c001878e9b2ac2980031b1cb65585300043f438cab0a6000c3c74195614c0018d8e432ac29800a2fa1b74585303b45e436e8b0a6000c3f65dd1614c001878cbba2c2980022fa1f64585300061fbaec8b0a6000c3c75d91614c001958e5b22c2980022fa1c64585300061fba8c8b0a6000c3c75191614c001958e4322c2980031bd9772585300063632ee4b0a6000caf64dc9614c001958c9b92c2980169da07651853002d3b408ca30a6000c3c75d90614c001878
  | 10 => 0xb0c60048f487505618c0014e90aa0ac3180031d9c5769463031d2ec34e728c6005c5c769ce518c00b4bf0cb9ca31801717dd973946302fc3fc3ac328c6000c7475985318c0018e8eab0a63180021fe15768863001c3e42aed10c6000c7475586218c0010ff0abb2431800e1f21576486300063a3acc290c6000cd773985218c0091e90eb0a43180031d1d561486300043ec3cc9b2a600087f87593654c001c3b06326ca980038719243d95303c52e43287b2a6000e1c6450f654c001878c8b96ca980028fa1262d95300051ec24c5b2a601c87d8718b654c0018dae4316ca980030f19271d95300061eba0e9b2a6079a5e831d3654c0f14bb063a6ca980029da0474d95300053ac08e9b2a607887e87d0f654c0010fb0fa1eca980161f20572d95303cd2f418e5b2a6078a5d831cb654c0010fd0f216ca980021f61e42d95303cd2f41c85b2a6000a5d8390b654c0010fd0e216ca980021f61c42d95300043ec3c65b2a6000a3e848cb654c00147b09196ca981e697a0f71d95303c52ec1ee3b2a6000a3e849c7654c00147b0938eca980171d9c471d95300043f43e83b2a600087d87d07654c00b8ece320eca980021fe1d41d95300043e43a83b2a6000a5f83507654c0f34b906a0eca980171d9c541d95300043f43e43b2a600087d87c87654c0010fd0e10eca980021f61c21d95300051f42043b2a6000a3d84087654c0f34bd0610eca980029760c21d95303c53d40043b2a6000a7980087654c0f30fd0f906ca980021f61f20d95300061f3b6cbb226000a3d82d97644c00147d03b2ec8980022f61e65d91300051f42ccbb2260008bf87597644c00147d0c32ec8980030f9d865d91300070ec18cbb226000a3d82197644c00147d0232ec8980038719653d91303b54e432a7b226000a3e8598b644c00147b0b316c8980028fa1462d91300051ec28c5b226000a3e86d4b644c15987ceda96c8980028fa1851d913055e1f3b0a3b226000c3d751d7644c0ef53d063aec8981daa760c75d91303bf0f29ea7b226000a3e859cb644c00147b0b396c8980028fa1472d91300051ec28e5b226077a9e831cb644c0ed53b06396c8980028fa0752d913062d1ec2ca5b2260008bd878cb644c00147d0b196c8980028f61632d91300051f42ee3b226000a3d85dc7644c0ef53d07b8ec8981daa760f71d91300051fc2ae3b226000a3c855c7644c00117d0e28ec8980022f61c51d91300061f438a3b226000c3d87147644c00147b0428ec8983128fa0451d91300051f42e43b226000a3d85c87644c00117d0e10ec8980022f61c21d91300051f42843b226000a3d85087644c0ef53d0610ec898002a760c21d91303b55d40043b226000ab980087644c0edc74a1a86c8980028fa1720d91300051ec2e41b226000c3c75d93624c001878ea326c4980029b60b
  | 11 => 0x4856bcace231ca29096a1f21975cc5210562e31aeb98a423387f87d9731484010fb0fb2e6290803179d763cc5210062ebaec798a425a87e86dd5314849b8b8c7baa6290a021fa1f654c52119c3e43eca98a4200c5f75d8d31484018b8ebb1a62908bb331cb634c5210061f3a6ca18a4200c3f655d03148401878caba0629082b2718d740c5210064f3a6c618a4200c9d74d8c3148467ccec3b2c4290802ba60840d812100578c0881b024200c5f659ce60484018b8cb39cc09080317d9573981210062e32ae73024200c5e75d8e60484018baebb1cc090803179d463981210062eba8c7302420387e86dd560484670f90dbaac0908021fa1f65581210061e3a6cab02420087e871956048401878e832ac090aab1ddc465581210061fb2ee8b024200c3c65dd160484018becbb9ac0908031719773581210062fb28e6b024200c5c651cd60484011bd0fb1ac09080317dd763581210062e3aec6b024200c9f74d8d6048401938e9b1ac09080237a1c63581210062fba8c6b024200c5c7518d604840193ee831ac090803271d0635812163e6bb88c6b02425ac757119460484011f70eb00c090802ae211601812101c3f42ee2b16600087d85dc562cc0014db0428ac5980f297a0f7654b301f62f39eeca966000a6f825d952cc07d8b8ecb9aa59831ad3e097354b30005aa40ae6a96607cd54311c552cc00133b0838a65981f355144714cb3002d3a40aa530e600387e87dd561cc09b8b8e7baac3980021f60b75587300246e41aeab0e6080c5c731d561cc0010ff0aba2c39800e1f21574587300246e41ae8b0e600087e87d4961cc0070f90fa92c3980021fa1d52587300043e43aa4b0e6000a748154961cc0015a902992c3981361fa1c515873025d2e41aed28e607cc5c735da51cc1010ff0eb0ca3981f3950c561947301746fc32e518e600087f855da21cc0070f90abb443980123720d76887300043fc2aec90e600387c855d921cc0091b906bb243980123b21d4258a3001c3f42ee2b14600087d85dc5628c0014db0428ac5180029be097654a300062ebb6e6a946000c5e761cd528c00193f06ba4c3180032720d749863002e1f28ae930c6005c3c515d2618c0b393e60ba4c318167274c174986305661f3a6a530c6000c3d74d4a618c00b4e903a94c3180e70f9d152986300061eba2a530c6005a748154a618c00b4ed0ba8cc3180029d21541986300165b3a28330c6000ad783506618c0070fd0fbaac3180021f60b755863025e3ac0eeab0c600087f855d1618c0070f90aba2c3180021fa1f525863001c3e43ea4b0c600087e87549618c0010f90ea92c3180029d20552586300063bbaea2b0c604b87e87145618c0018eeea28ac318002ad610515863025d3b438a2b0c6000c7687145618c001c6d0828ac3180038d61051586300053ac10a2
  | 12 => 0x8029d60440d95210062ebaea7b1a4203c5c7594f63484071bf0ea9ec69080297a1743d8d210052ec2e87b1a42028df8750f634840593ce8a1ec69080297a1664d8d210052ec2cc9b1a4200a5f8559363484014b90ab26c690802b6e0164d8d210056c402c9b1a42cba5e8614763484018baea3aec690802a7a1075d8d210054ec20ebb1a4200c9f749d363484014bd0a3a6c6908029761474d8d210070faa4a9b1a4200e5751947634840153d0828ec690802a761051d8d216570f420a3b1a42cae1d8414763485954bf0428ec690b329760851d8d210052f42e83b1a4200a5d85d0763484511bf0ea0ec6908ba3721d41d8d210052fc2a83b1a4200a5c8550763484014bd0bb86c6908029761770d8d210054f426e1b1a4200a9d84dc363484014bd0b386c6908029761670d8d211756ac08e1b1a42008de8714363484011bb0e286c69080237a1c40d8d210046ec3881b1a4200a5e8510363484014bb0a206c6908bab3a0840d8d2100566c1081b1a4200ad68110363484015ab02206c69082b1718d7598d210062f3aec731a4200c5d75d8e63484010fd0fb2ac6908021fa1c6558d216963bb88cab1a420387e87dd563484010ff05baac6908021f60b7558d210046fc1aeab1a42008f7815d563484010fd0e3aac6908021fe157458d2101c3e42ae8b1a42008df835d163484011f700ba2c6908123e2017458d210062fbaee6b1a4200c5c75dcd63484018e8ebb8ac6908021fa1c5158d216963bb88a2b1a42008df8758c63484014bf0ab18c690802972156318d2168e2f3b6ca31a42008dd8799463485934bd0b328c69080237e1d6518d216856bc0aca31a42c8a5e86194634859f8bcec328c690b3795c846518d2166f2a108ca31a42008dd8799063484014bd0b320c690802976166418d216756ac0cc831a42008df8759063484014bf0ab20c690802972156418d210056dc02c831a4200ad88059063485914bd0c288c69080387d525418d210054f420a231a4200a9d84144634856bc3d08288c690ad7876105118d215ad2fc10a231a42c9a5d82144634859bcae42288c690ad7950845118d210052f42e8231a4200a5d85d04634844f59d05a08c690802b360b4118d211546fc3a8231a420a8dc8750463484014bf0aa08c690802972154118d210056b40ca031a4200ad58194063484151bd0e280c6908023761c5018d210546f4388031a42008dd8710063484014bd0a200c690802976144018d2113d674108031a4200acd8210063484015ad02200c690802b56044018d215ad2f436c728a42ccc5e76d8e5148595e8843b1ca290b2b17dcb639452165e2eb96c728a42cac5e71d8e5148595cace3b1ca2908021fe1d63945216552f430c728a42c9c5e7618e514856be884231ca290ad717dc863945216462eb90c728a42b5c5e7118e51
  | 13 => 0xd5b408e0b206228ab5811c1640c41553d07282c818802a760e505903102d5b40ca0b206200ab581941640c41553d06282c818802a760c50590310051f42e40b206200a3d85c81640c40117d0e102c8188022f61c20590310051f42840b206200a3d85081640c41553d06102c818802a760c205903102d5b40840b206200ab581081640c4151b906baac4188163d20575588310546e41ae8b1062d5c9c435d1620c44f1bd0fa1ac4188163b21d525883100d36416eca90623ea5c835d9520c47d8b8e6bb2a4188029be0976548316a70fc1ac8a90623ee1c83591520c47dc38e6b22a418b4f0fdc9645483100717b92c8a906205c3e71591520c40b878e2b22a4188170d1c564548311f70f982c8a90623ec5e76dcd520c401c3ac9b9aa41880e9ba1d625483101d3643ac4a906227e4f83589520c44fc9906b12a41880393dcd62548311f72639ac4a906200e4f43589520c47dc9886b12a4188171b9c5625483102e3638ac4a90623ee4f31589520c47dc9e60b12a4188165da1f71548310071ab26e2a906200e6562dc5520c4014eb0c38aa4188171d9d871548310071ab20e2a906200d57731c5520c401aa8e638aa4188039958871548310062e3aeec9886200c5f52dd9310c40b8bca3bb2621881717147764c4310062fbb6ea98862278dc87589310c44f998e4b1262188025721d524c4310062fbb2a49886200e4d62549310c40b6a902a92621880e1fa1f75580310043ec16eab00620087f855d1600c4070f90aba2c0188021fa1f525803101c3e43ea4b00620087e87549600c4010f90ea92c01880f1e1d6505803102c7c43aa0b00620587e87d0f65884010fb0fa1ecb108161fa1c40d96210043ec3881b2c4200a5e8310365884014bb06206cb108ce9ba0840d962100536c1081b2c4205a768110365884014eb02206cb1080e1fa1f7558e2102c3f40eeab1c420587c81dd563884010fd0e3aac7108021fe157458e2101c3e42ae8b1c42008df835d163884f98becb39cc1109f317196739822131e2fb2ae73044263c5c655ce608840b2ed03baac11080e1fa1f755822102c3f40eeab04420587c81dd560884010ff0aba2c11080e1f21574582210046fc1ae8b04420a8dc835d160884010fb0f326ca9080297a0e64d95210052ec1cc9b2a420087f8759365484014bf06b26ca908029720d64d95210053dc02c9b2a4200a7880593654840187ae83a6ca90803175cc73d95210043f43e87b2a420087d87d0f65484670fd0fa0eca908021f61f41d952155c3fc3a83b2a423387c8750765484014bf06a0eca908029720d41d95210052f41ce1b2a4200a5d839c365484ad4ed02386ca908ce9d60470d95210043f43881b2a420087d8710365484014bd06206ca908029760c40d952119d3741081b2a4200a6d8210365484014ed02206ca90
  | 14 => 0xd848cb654c49b0fd0fa0eca988021f61f41d953155c3fc3a83b2a624d87c87507654c4014bf06a0eca989369720d41d95310071aa0883b2a624d87e87c87654c4010fb0f90eca988021fa1c21d953116c3ec3843b2a6200a3e84087654c40147b0810eca9893697a0c21d95310053d40043b2a6200a7980087654c49b4bd07b86ca988029760f70d953126d2f41ce1b2a6200a5d839c3654c4010fd0e206ca988021f61c40d953126d2f41881b2a6200a5d83103654c4014dd04206ca988029b60840d95310053b40881b2a6200a7581103654c4010fd0f906ca988021f61f20d95310043f43841b2a620087d87083654c40147d08106ca988028f61020d953126d2f41841b2a6200a5d83083654c4014ed02106ca988029d60420d953100536c16ebb126200a6d821d7624c4010ff0aba6c49880e1f21574d893101477c3a85b12620087e87147624c4014db0428ec4988021fe1570d893101c3e42ae1b12620087e87d95624c4010fd0e32ac4988021fa1a765493100536c14eca926200c6d829d9524c4014bf06bb2a4988029be0976549310053bc0aeca92620387f821d9524c4070fb043b2a49880317cc876549310062e990eca926200c77311d9524c4018e8623b2a4988031719676cc9310062f3b6cb9926200c7465dc5324c4018e8ca38a6498803171db654c93100726316ca9926205c5f639da514c4670f90cb94a2988cf1b18972945310043fc3ec528a6200c6d72d8a514c56b4bd0d994a298a03179db329453102d2e4326528a6293c5e764ca514c49bcaec3b2c629882a37219728c53117666312e518a6200a5c8654a314c4070fd0dbaac0989361f21b75581310043f43ecab026200c3c74d95604c4018d8e5b2ac0988021fa1c65581310061e3a0cab026200c6c72195604c40187ecbba2c0988030f197745813100637b2ee4b026200c6c65dc9604c4011f70eb00c0988030fdd675590310554f41ceab2062dca9d839d5640c5b753f06baac81882aa720d75590316d64e39ee4b206200a3e859c9640c40147b0b392c81882aa7a0e72590316cd4ec1ce4b2062d8a9f835c9640c41553906b92c818b57271cd72590310051f428e4b206200a3d851c9640c5afc3ee7a92c818b4f871cf525903102d1f40ea4b206205a3c81d49640c5a7c3e61a92c8188fa8f61652590310054fc1aa4b20620aa9c83549640c40156f02a92c818816ad205525903102d1f42ea2b206205a3f85545640c40147d0b90ac8188028f617215903102f1a28e42b20620aa9c83dc1640c41553d07382c81899aa760e70590313be4e39ce0b206200a3f855c1640c4014790ab82c818b5aa7e0d70590310554e41ae0b206200a3e851c1640c40147b0a382c81882aa7a0c70590311454ec18e0b2062b3c9c731c1640c40155d04382c818802ab608705903102
  | 15 => 0xe212cb988021f61c42597314852fc1ae2b2e620087e87d0565cc4010fb0fa0acb988d21fe1d415973155c3e43a82b2e6200a5f8350565cc4154b906a0acb988021fa1f21597310043ec3e42b2e623287e8708565cc4010fb0e10acb988028fa1021597310051ec2042b2e620aa5e8308565cc4014bb0610acb988029ea0021597310053cc0042b2e62dfa76819c165cc4014eb03382cb988028fe1170597310051e422e0b2e62dea5f835c165cc4154b906b82cb9882a97a0c70597311952ec18e0b2e620087e8710165cc4010fb0e202cb9882a97a0c40597310052ec1880b2e6200a6e8210165cc4014db04202cb988029da0440597310053ac0880b2e620087e87c8165cc4010fb0f902cb988021fa1c20597310043ec3840b2e6200a3e8408165cc40147b08102cb9882a97a0c20597310052ec1840b2e6200a768108165cc4014eb02102cb988fa1f61e7558b311f536c14eab1662d3a6f825d562cc4070fd0bba2c5988021f6177458b310546f41ee8b16620087d8714562cc4014db0428ac59880e1fa177058b310043ec2ee0b16620387f82dd952cc4070fb05bb2a5988fb17ccb7654b310062e996eca96623ec5c31dd952cc4014df04bb2a598b4e1fe097654b3100637c12eca966200c77815d952cc40b2ed0fb8aa5988031d5db7154b310063abb0e2a966200975861c552cc40b8eb0c38aa5988174da107154b3102e9ac20e2a966200c77641c552cc4018eac838aa5988175598c7154b316963bb10e2a9662d2c75621c552cc5a5aae6438aa598b4b554c87154b310063b300e2a96623387f865ca51cc4678dcc4b94a3988021f61d629473100636b92c528e62caa5f864ca51cc51b8baec994a3988022fe1175583310145e422eab0662058dc835d560cc40517d0fba2c1988030fdd352583315661e3a6a4b066200c3f7454960cc473878e8a92c1988d7271d132583310061fba4a2b066234c3c7494560cc40187ee828ac198aaf0f1d051583311746f43886b14620387e85dc1628c4010fb0bb82c5188029b60a7654a3100537c12eca946239a3e841d9528c40147b083b2a518803175db7354a310062f3b0e6a94622e8df8758b318c45d99ce4b16631880257e1d52cc631154ce422e198c620087d87993654c4014dd05326ca988029b60a64d95310043fc3ac9b2a6200a3e8498b654c40147b09316ca988b61f61c62d953100636b90c5b2a6200c3d741d3654c49b4bd063a6ca988029760c74d95316ed3b408e9b2a624da75811d3654c5134ed03b9eca988021fa1f43d95310043ec3e87b2a624de1c4350f654c49b4bd06396ca988029760c72d953100636b90e5b2a620087e8790b654c4010fb0f216ca9893697a0e42d95310052ec1c85b2a620087e8710b654c4010fb0e216ca988021f61e32d95310051f42465b2a6200a3
  | 16 => 0x1d85320071ac20a3b0a64e6a7782147614c9cd4eb0428ec29900a3de1d41d85320053a42a83b0a64008bf845c3614c80517908b86c2990023de1d61185320053a42ac230a64e5ad783584614c995caec6288c299002d960851185320064fc1ae830a6400c9c835d0614c80187ea4ba0c2990030f549741853202e1f28ae830a6405c3c515d0614c80193ae9a18c299002b560743185327272a28e8630a64008dd8710c614c80193ae8218c299002b5604431853271f2a2888630a6405a7685d44614c8014e90aa08c29900b2d9d141185320056bc1a8230a6400e9743504614c8010ff0ab80c29900e1f215701853200c6ec1ee9b02640087f855c7604c8070f90ab8ec0990029b60851d81320047dc3ac0302643487f87592639446987ce8b24c72880297e0d6498e5102d2f4328731ca200e1d6450e639440127f08b84c7288d24f2117098e5102cae41ae131ca263c5f635c2639440b2b90ea1ac728816972194358e5119c3f43cc8b14a200c3f7499162944674dd05322c5288ce1f21d6458a511a61e3a2c8b14a233a6c8259162944670fd0f31ac52880317dce6358a5119d37414c6b14a23387c8758d629449b8b8e6b1ac5288ce9b2096358a510061fba4e8b14a200a6d829d162944014df04ba2c5288030f5d07458a510062fb9ce6b14a200a6d829cd62944014df04b9ac528803175cc7358a510043f43e86b14a20087d87d0d62944670fd0fa0ac5288021f61f4158a5119d3741682b14a200a6d82d0562944010ff0ea0ac5288ce1f21d4158a510052fc1a82b14a200a5c8350562944014df04a0ac5288ce9b2094158a510052f41ce0b14a200a5d839c1629440147f08b82c5288028f2117058a5102d3b408e0b14a233a75811c162944010fd0e202c5288021f61c4058a510052f41880b14a200a5d8310162944674dd04202c5288029b6084058a5102d3b40880b14a200a7581101629440b8b8ecb1e6528a021fe1971cca510043fc32e1994a20587c865c332944018ecc3bb26528817179da634ca5102cae43ac6994a205c5c7658d32944f98bec539cc12897f1798673982513e6ab30ce7304a263c5c865ce60944c78bec4b9cc12897f17985739825131eab30ae7304a24bc5f605ce60944978bac0b9cc128803175ce63982510053cc04c7304a23387f8758a60944018bce6b14c128803175cd629825119e37392c5304a200c6d7258a60944970f90eb22c1288d30f1d1645825125c3e43ac6b04a24dc5c7358d60944970f90eb12c1288031bdc9625825119e36392c4b04a200c3f749d165cc4154bd073a2cb98b8a9760e74597310051f424e4b2e6200a3d849c965cc4154bd07392cb98b869760e72597310053bc0ae4b2e62e0a74815c965cc4010fd0f212cb988021f61e42597310552f41c84b2e6200a5d8390965cc4010fd0
  | 17 => 0xaa400a5e8310061548014bb06200c2a916a9ba08401855200536c108030aa405a768110061548014eb02200c2a90038d50440185521e43ec3ec9b02a439c3e74d9360548790fb0fb1ec0a90fb179cf63d81520053a40ac7b02a42496d829c760548012bf06b8ec0a90fa5720d71d81521e43ec38c3b02a400a3d84187605480b8ece230ec0a90031d5c461d81520062eb9cc7302a400a798098e605487327d0938cc0a90024f612719815202e3b38cc3302a4e9d6972d82605487327d0fba2c0a90030fd8b745815200697b16e8b02a40095f835d1605487d2b906ba2c0a90025be097458152004bbc0ae8b02a400974815d1605480127d0e3a2c0a90e70f1d364581521e43e43ac8b02a439c3c7459160548794f100b22c0a900347dd373581520068e3a6e6b02a400c5f62dcd6054801a9ec5b9ac0a900347dd073581520068e3a0e6b02a400c5f641cd60548018bac839ac0a934f17d887358152006a7b10e6b02a400c5e601cd60548018b8c039ac0a90021fa1f63581521f62e39ec6b02a43ec5c7358d60548014e902b1ac0a90034bdd37258152006963a6e4b02a400d4f73dc96054801a98e7b92c0a90034ddd371581520069a3a6e2b02a400d5773dc56054801aa8e7b8ac0a900359dcb71581520063bb16e2b02a400d6762dc56054801a6ee838ac0a90034d1d07158152006abb98e2b02a400d54731c56054801acee438ac0a90171de1871581520063bb20e2b02a400c75641c560548018eec638ac0a90031d58c71581520063bb10e2b02a400d67621c560548018ecc038ac0a90031d18071581520061fba4c2b02a400c3c7498560548018bee730ac0a9003171ce61581520063bb8cc2b02a405c7471985605480147b0830ac0a90030fdd061581520061e3a0c2b02a400c5f7318560548018b8e630ac0a90031ddc4615815202e3a388c2b02a4e8d6b72d81605487b8bec5398c0a900353d8a73181521ee2fb12e6302a400d4f625cc60548798bec0b98c0a90f31758173181520043ec3cc6302a400c5d7398c60548018bae6318c0a9003179ce61181520062eb9cc2302a400c5e7318460548018bae6308c0a90171d9c46118152004bdc3ac0302a4e7b6b8258060548011bb0fa1cc399002b5607439873201c3f43eeab0e640087f855d161cc8070f90aba2c3990063720d745873226c3f438a2b0e64028be84dc161cc80117b09b82c39900e1fa1f755833202c3f40eeab06640087f855d160cc8070f90aba2c1990063720d745833201c3f42ee2b06640087d85dc560cc8010fd0e28ac1990161f21c5158332005b2c10a3b0a640387f875d7614c8018ef02baec29900e1fa1774d85320043ec2ee9b0a64018dd83dd3614c8018eaeba8ec2990031d5d451d85320055ac20a3b0a6400a7587147614c8018eb0e28ec2990038da105
  | 18 => 0x48016a902b18c6a90fa97e1d6318d520062fc3ac631aa40085f8758c63548014bf08b18c6a934e97e096318d5200727c12c631aa400e578158c63548014b902b18c6a9003952056318d520052a40ac631aa400a5c8058c63548014bb0ca18c6a90024fe117018d521cc9e422e031aa400c5d635c0635487d2bd07ba6c2a90025760f74d85521ccbbc3a83b0aa405c767650761548016a906a0ec2a90024fe1170d85521cc9e422e1b0aa40096d82dd2615480b8e8c2ba4c2a90030f5d264985520052f41cc930aa400a5d83992615480b4ed03324c2a90029d60664985521cc3fc3ac930aa439c3e74592615480b4e902b24c2a9003175ce639855202d3b40cc730aa400a758198e615487d8bce6b1cc2a90169d205639855202f3230ae530aa4efd6572d8661548010ff0cba2c2a900257e0d74585521f4ae41ae8b0aa40096f825d161548012f700ba2c2a90f25e20174585520062fb16e6b0aa400d4f62dcd61549a78bec439ac2a900353d887358552006a7b9ee4b0aa400d4c73dc96154801aa8e7b0ac2a93bb59dcb61585520062fb9cc2b0aa400c5c73985615480127b0f3a0c2a90178d98674185521cc9fc3ae830aa405e36615d061548018790cba0c2a90030fd89741855200697b12e830aa405c3e615d0615480b878c2ba0c2a90e61f61f64185521ce1f3a6c830aa405a7681d90615480187ae9320c2a900297a0e64185520052ec1cc830aa405a768199061548014eb03320c2a90e70f9d164185520043ec38c830aa400c3d74190615480b4ed02320c2a90029d60464185521f43ec3ec630aa43ec5e73d8c615480b4ed03b18c2a90029d60763185520061eba4c630aa400a778158c615480b4e902b18c2a90030f5d063185520062eb98c630aa405a768118c61549db6cb05308c2a90021fe1d61185520052fc1ac230aa400a5c8358461548012ef0eb08c2a90169de196118552005aa41ac230aa4ecb678258461548732eb0f208c2a90169de1a41185520053bc328230aa439d36745046154801c6cc8a08c2a90038d5914118552005aa41a8230aa40587e87d0c61548010fb0fa18c2a90169da0743185520053ac0e8630aa4e4e5431d0c615480b4e903218c2a90029de05431855202d3a40a8630aa405a768110c61548014eb02218c2a938f950c4431855202d3bc3a8230aa400c7787504615480b4ef08a08c2a90178de11411855202f1b3a28230aa405e35745046154801caf06a08c2a90029d20d41185520072a41a8230aa400a54835046154801c6e86a08c2a90038d50d411855275d3bc128230aa4eba758250461549d5c6e84a08c2a93ab8d50941185520053a4028230aa405a7681d0061548014eb03a00c2a90169d20640185520071aa0c8030aa400a7781500615480b4e902a00c2a90161fa1c40185520043ec38803
  | 19 => 0x400000500080280060020008008032000000001c002001003800400600300000000020020000010000002001000000c00f00080180000000070008000001000800003a001001802803800400300000000010020010014000005802401000000500040000000010000004001001801001c002000000400600000000200040020008010000002002001802000500280080060010000010002009002800000600300200040020020010000000001004000003a004000800c000000000000400400100080040000030018038000003002005c000000001000c0160040018000000005000000800001300080c80000020000004000002003004400c00000080040220000010030000002006002800200300a000000600600200040040000000000004004001000000000c00500000000030010000000001004000000000100080040000010088004008000000000801a00000000280000030000014000004001801400000400080000000000038004000001000000000000c005800400e00900100140120080000004002001000006400a000002800400a00000800040020000058000000000000000000001200080000120030018004000000002802000000a000802800c000000801800200100100000000030000018000001001000000000200080040060060000000010000000000001000400000040020000030008000009000000c00000000080080000000000010004002000000401200400100100020040000010000001000800000201c0000000006004000000000800300100000000000000010000005001805000000000a800400000000080080040000010028002001002801401e005000800c0080000000004000002000001401c000002001002a0090028004012010000001800c007001002801e000006006c00a00200080040000010008010000000000000000200100080000000000000004002001002800800600100180040040000000000000005001000000000300a00000000010000e657e1d43d8d520052fc3287b1aa439d1e7450f63548492db0538ec6a90e61fe1d6498d520052fc1ac931aa4f3d4d72d8e635487d4bb0fb1cc6a90031761f6398d527962eb96c731aa43ee4d72d8e63548018bec738cc6a90025be097458d52004bbc0ae8b1aa400974815d163548012f700ba2c6a90f25e2017458d521f52f436c6b1aa43ec5f76d8d63549e3a9ee7b92c6a900359dcb7158d520063bb16e2b1aa400d6762dc5635487327d0838ac6a90024f6107158d52006b3b90e2b1aa405c77861c56354801a6d0838ac6a90034d6107158d52006abb18e2b1aa400c76631c563548018e8c638ac6a90031dd887158d52006b3b10e2b1aa43987d87d90635487387ce9b20c6a90029760f6418d52004afc3ac631aa4f0b4f8258c635
  | 20 => 0xa3456849f00015e1194a40000057caf883a49325109f68295398000f0200000027e91e84fa000000013c41400000000464854550afd45000028e81d8000000000000000046413780000006f0239089000060e3c4000028200000013ace8200000019f80000000001e2cba441600006a400000041500000000000e18000750000000299c00093551080014c60000000000f7e9e80000000da800000000009525323ca0dccc927eb164029862000002e83ecd6c0002d40000000000000087929e23228b21e4000000000000044098a096000055e000268000000083f3af800000067136716080003c0219116881408903489ed1881e000019fc0004b100d000082a0000000000000000000000134c0000001c0000031a00000012327a43d6000000000000000000000000000000dfa97052f17c00000000024006000000801c008000000001000602c0000020006000000005c00000400480000000080008008004004002800c00800000900040060000000000002002000801c000000001801400000400000000020000000008000000001000400200f002803c000002001000000000f0008000000005000000801c0010018000002000000000000200300600140080010000000010009000000c012000001001400601d001000800e009000001c000000003801001a004001800401400100000000020030000004078008000000000001c0000000012002000003800e0000008000000007000800c00200a0010000002002000003c000007003006400a00b002001400000000000080360020008008000000000000400000200000000020000018008008004000800000000d00000040040020040000008004001800400000700000000000040010014000003002802c000002000001000400200a8018000008000802c00000000000080000000008000004001000803c0000090038010002000000001c01800a0010000000000000000000e0010050020002012001800400c00000180080000050080000006001006800800000a0000000000003000000c00200b0008000000004000800000600000080100100000000008008009008800000000500180200000020050000004003000801400c003004000800a0000038000000003003000c0000180018004002004003000c006001001800400000100700040060000068008000000003000800200100000000000040008008004003000800000000400180000020010000004004000001000c000000000001c0020060010000012001002800000000000280080020060008018004002000801000c0060028008002004000801400000b0008004022001001000401800300100280080010028004000000000000000001e00200040000050070048004000001802800a0000028000002002000002c0000
  | 21 => 0x95c4bc00019d927a68f1e9800000000043214e47489af4478000000000000000000072b00000013124c5000263000030b449800040e0002a580000000000001de087a0c600008c40000004009ca4000062000000000000039b0c340005744909288d420000c20000c7225f0bd8000d9a0a44b000014a077527e95dc81c55b1b915749ac0000000000bc011100000000003f3384a0dc68613403d9cb86d206e38229740000000001b040003d52c38998d344da0000000d3e00000000012ae14500000000000002ba8000000940000000000000000001540fe0000000f5800000000000000002dc000000009819b0000000f6089435a2198cea63f000184400033d00000013160000000000000643504254800000037600000000000000000000a640490ca0b464cf07288e12723363f1067846a7bc26600008bc9581bc1465482000000027c73a0ff10a8ee8bf665d1b416f4f4e0000001c5c08a88e0d5a47c0007f03a91f14b6888b209a1a101c2880332390b84267338000134a0000911064ea224a000000000037d0000000c4e00000013f00007772768b04f52000000026800000000019640000000001890a886bc390a8b00000000001bd00380001b11ae00000000001cfc00000000015c0ce801818f000000000137fa9340006d60000000a3e00016213085ec00016d028947e58c4e124ec4c483840d8cc80002c50000c907020002ea9d649b800000004f4f262612740000a8a4e0000000000000010c00000008f803c80000000000000001354774000000000023303e80000000000002070000000239a4c0000a1945b8cb00000000000bdc0006fb00000001e04de17c83108cc7672558e9400000041c878829aa0651a000000038a0ea800129801200000000009da2f40000000000431000017a36e2cb8f2458678c31e80ecbf49752269d503d81d3099800126856f43d8bb801aa261d099481768004ee821c00000038c80000005860dc8ed4a5c53e00001a8fdc9be00016b800000000000009a64f100000991464b54f6a8f01d6000405a19c6f225c42ba97128a4d4534800067e764102954502a8c94e9240106a1e72d5176cbd64c712a8c4ceda79838721649121dd12301f875400015811810064cd29590040000b700000003be000000195c0000000000000e9c87300022e082e000000267c000677000046800000000000000000000000000a0215315180000081462a51ae447832043081e802033002d1904c8c000000000000089b0000ae4d16000000234800000015a80004268d041b06ec0000002258000b381a60000df8da69100000000964000403800019463c5308000a4e6b143288f80008103488750d2a25e06c05e4be857a1660000000136000056c0008ef42d9454528188146212cbf000016ba97c8d814f00017d459c6fa0
  | 22 => 0x42184bcca84513b417cc71852307988d145662b28780014626ab000000000094b0f280002c6000000000020800000000a8f960003f894d8e300743e2126883c2eb24e859c6fe7480de018cc1a5200cd0314c288ff2339f80318000442044c8785904afa4800000000000000db86d928880000000000001cf800000049396e84b600031825d80000002cd0000ac83340c796bc49279b000000000000011f80004000003f080012fe79041680000008bd50600001863392d2000000084a00024b50287441700a98aaa62e1e11c500000000000000000000450800106228f31b966cb8c0b10000000000033000278c8e016f388a71921a4900aa00dc096795121000000000010092e80003e200000001384d20540000e5a000000178c0000003d900000008a600000000000154a48000000000000000000000000013640008ad282000089c9d80000000574000000000000000000017c800000044e1fa409e7c00f681584248e85229b95360000000065800000037429a00007db000182911a7f600000000000000002995218a3d00000001e27cd0001cd00003f700027bc00000012e89a08aca6c00000003162840000000000951016a2f80008ec0739bcc2d46bb000014812000001022fc42057d0000000e1a1ca44b0c6c8187d82de013504c796002a6c50588162ce95b4522000000000000064c000032c000000000000000071616a8000dc6000000000127053a25323813ea7ea2c4a43d3d690752c214c0009cd0000c8400033e0000000a9273b0000b847e40001e607114843e5422000116260c0779c20fce0000000fb0d002a9000000000000000006240008f60000b4000000000024088f4359000095c0006c600000009c80002ef193800085f14c1f28da02f416f910d17498f039a6ec000000000000008074648e0e9d13017a28812111908921f593a8000000362a40525411b00010acff024d31612d00001a106380010ea4260001738000851209000000098d00011a80000004ff24f000048e000000000016b00021b470c000000000000000000000c13a600042b000091a17605702280007de00010fccd200017d0000000000000000000000042a953939c0000000000d600000250d5c0005ab2870ddc00084d0f805e0622a4344ca880c2400a35b8e3c0002300ab000147c2250000000bbe1f210d06640002ac30e99f0cde18337089c46389fc31980c88e81ad000000000053124510e4a0063800000007901fa436138c00000000001240009ac50b80009ce4b613580000000000000bec5ca344120928c1468272c5000000000000000004363d05220000ca000000006442b400015389414360000000bf00000000000fd50447ef0d7825878800004e80000007a00001f0c000725000221c71600015b29c0ecc40827800000063f13078000
  | 23 => 0x12fc3850df233c0004b82b906b0f5c98100006a0000805377000000079d30580000000000001fed42064d228000111800000000000000004988000f220af000019ce382a231a14d0ffc66614b97680da0003a490ccdfc3e150683f488829f0c30000f560001ae1fdc00075b000000000000046600000003c30d88e6cdb600053794a80c200000013a40000000000ef8000000245800107856c4e81a3000c4ad4e525eccc45c345a0b2c10830f4a68a9066e83e00004c852c27d00e87dd3f03543b280390660004888f1545c50b4611724e747891ac098142a0000001cbc0009800000000c7c77c2c59af4a0c6f20001a0c4ea4af16c1ba80007a10001888000000000000000000050e9e704e8120000000000085d49b8adcf6a00000003e926600031d800000000014ea3180008f709500011aa2524f91d280002d600007ec000000000000000000000000009e60002d6107c996a460000ded3d8000000000000000000000000000004d7154cc26a0f1499080360a070000a2d44447f252813800046f00008a00008b3000000078291416680009d82a14a394cc48800037695ec00000021d811d2f01300001dacb3c0001348000efc5842b1000000008c3bd918442e0000001a980000003ae800000028031b000122a00046a000075aa4904400000000000000000a50785302000108aa7407a1ee8000000000000000043002a036c6d437a35f800073892f34c8e8cbba000066845519a17c0001840eec000000272c27200051280013ec11004b807c0000005120001412000333a1a800087e21b800072e0000000000ab824e0c012a01ba7831baa96d43803f0c10a48000000000000000008248902d004a3ac0c800009487350fa8d1c0503014aa000000000017c0ed0000a722869284d5e77d2f080008381e100000000000001c71b242ae01b0b71c1c6949b40db800000000000022041786f942d28ccd300001018000b1c0aa4410000eaa000000140c0006f701600000000003ee000108e411000000073e6864358d6901a00000000000003a245813000000002400bf88d61512e89b5cd3a0ea000000000000000004f800000000001600000000000000cc00000000000000000383065437014700020bc0627ec4f2a5dc1584584b38000f6e00010e94b4f9c712533000000000000000000000001be09b45942fd0001884acc00000000000000002d10b882b227022500000000f20da0000ce4000000000000000023407983c80001b2041ccb41ff47a8c8d1dc6e41b8837ce842b12c08a7935a1551178b6c00015200000000160000001c4cde25144300000d0a0003b5278823000023b0ff05d8000000090c49e61900020d00001dc4e29b314b259300024d800001700000014225542e828b50a06812318b983de5b745b09944b400027104f0d2e2f3
  | 24 => 0x200000007305a900022b8b5a3e40001244000000505800024c6554ad1f7c8aa8de1b388e820c000000000000000000000000c05401cb17dcf8c0e63b017500006cb00006700001aa05b000039a00000000000008760358000f4400033d928000038d50a020c242211000160d4ae00000000011c615024c00010b800000000011cc7244eb8675056723085a3953e200023c8680000644396000123a00000000014023d100022194140002cf9d0c0000003fa000149060621a80e4bcc5940400f8c0003421de9dc82e600000014980184420000f800000001fe80000006e70d1a66880882016103546ac60700023151d20c84b527a8ac23ed05985901646314b707445142210002540fca6e90e287cd274a6b1b600000900702d0a5e88ee2d900019000000000000000902000000000000000000000452c8000000000031c0000001230c8e7d000000010426c80000000d4a0003e78478ee07f946e906000072700005280005f646b800000011646d000000000033c963c0001cb000000000055800a000000022e00000005d45462d0000000000000008ac2500d700019a80000000000b742fe4ac0001b7c6c20000ae1898000065000000130605f0001698000000000000000007700000000000000000d0000000000000013be0000000e083281a200025a0ace0000000c285785b92581bbd424a4e2c00000000143000267400040300000000009d622908111da0000558e2108c69b3eb058807c6b54db15a40001c02b500012a68632cc00000009993d88c740000000001f44000615000000046c0000001f0800075a0d9a13077617e1568000cd61710000fd0fe400000017f54dc45b05d04749fc0593b497211145cc1bb000000062d31180004e40000001f2400000000020913b856845280000003b04be033c03260114da288452309080a4900001fe13b125481a00000000009b671b074809c7225d60000d45050a1800018686968044910000000000000000000000001d205c20071a22a1cc80005b23b980011003d838500000005910001fe80000003a98f78dcc00007200004fe74b332a944d1400045c80013042e82bb00a4c6a00000014d400088506896d438234c0000bd4a7a6aa0000000f0c9f724ba61810aa2743b80000001930001e1c0000003618d8c79a0005098c989cc6ae4480000db07371320000000117000000120a0000708fb80000000001d5c80c9c90ed26894e255a047251801053c000270c000000000185875c0001438f1cac67c8000227c0005ff48400000009e046027f509e0003a62061282000071800123031700026480006dd36880000000b90001de400000000028dcaa000026480000004b30a1000000000044ba80c0000001ff00001306a03ec8000000000000000000065f42413dd2e80001c38370666000000000
  | 25 => 0x10d949e00036399600001bd38a80000000000a580000009f407c8fec00081a0000000e3c000000000000000001100000000001b01e109e80004ca02840000001d9a6a0d58038000000064a1e90c68090ec4000381a7312d20004388000000445000173cb62000095929c0000005291e9459e8bc4b60ac80004bd1c81eec0000005022028000a53000000000000000000004121ce0cb8000e8a505181800005611c0001c1528614044e94892940c20001ea000092900000000000000000000e4c00049f10854d46682688340ad69633c119b8bd85ed26f93289107aa08127005e47e64de90b9342254039130c85223716393551c221600005844ac00045a800059220e24780004f28e72851a9cd660132a921012b20993b78ec493889e1861cc400046d000000000053800011000008eb000156473431826b80009f0000314a6f000096b0939c88820000000000000000021403a0000000000000028800017227989285b349414bc0c80003c0174c00020f243257400085e4d39e7cf242d446e0d6c1166562c405b532664f1e31ce08363b92fe000034e69622784145349e900000000005c7000000000000024f0d343d0000000000133800000000003c60004d49db814a0004f8201800015e000145c000a29349853841400009ba0240005730000000d20000000146c042000195975c0000000eb10c4b2aa0e51d0d250f0281000056000000039e014c34a00000004501282a04f71ed0fe69d1046996c65c4820ec0d9474c61829f80012c400000001b0fba90a00003dc000131000188000010d4500000c101a447980000004ef00000011e4825000000000001e3ed0aec6001c92000000000000000000000066c00000000000004d580003dc9a400024790de000000266cf7c9850001120000000000000131000000000000000000b290b006845f1690000af200730f909c00041a00011301fc47d1010ae03fa00000002a400000000015fcef400030e000142c0000000000b7e18122b8000a9a2ff27082e0a244ce3de829c47a16800000000000000000000000000000155c0000003521bf0d8479e00009cc0000b53cb80000ae00050d28c848e00000000000000000001c08a986da3fa800019822d36f00000005f11cf000000031f1a70000bca0003e395780006450000c640006a92f20a387265ca18b207d0182a800000006769fb4c380000003480f500003b20005028a4002c00013500008e24872e28efd364000157273c000000000000112a869000000060a00000000000000000000fa00f03cb00000000000c023727500006d2000000000000016887480002e912c241005e00000018c800000000029887f03150000f980000000001ccc000000523a46cd80a3b1e925949241c826300003a00001e712f8972000000298134681
  | 26 => 0x6629200011fa00009186c82fa000211800088e0004561f4800092c4af034c0003cf19780012c20000848000c365e200023e50f480f46da4c88f61ba2039db053228616313106ba83d12983b87a817410a000079400003e16d8000a233d31d7800000000013d80003df04d80004540000000944ae200034121c80000f5448998d0225ef000124c444095264214800096d37b00009dc0001ed09e06bc3ff28d000138800000000000000000000aa80000000000000000000000000110600000000000008cb000037800000018a0000e9a00000000002520001fc8920ffe2850000d48000499000003c0000001a300006d600005f9c7c0005254df823c44e4d82d29014000000290a6607b200034f07e050620d08fa64546000009200000000000000000d287d42bf00000001bf0879124000000517824c0000000769dfc08873033d0af46443b83369b88fc62082e6a34c9ba00032887ac8ca000000292810c00000001bc868000000000033e2630001970bce13b000000081e3700000c20b769de4a10000e9e22600000b8b702590000d413908b213e06610266a208704482c023b02320751e20003569460bf20f818328a932c2d31b7a5713b62061f39990a3c44147e19085c603c1d5887c4d805014a9d1d374a4b03a87f069e99732980003e836629801090840d94dc09f80e200000010092264690001a48bd280840c8a7000000000005b01606b22a120c04800001eea0090460004b3016d40400016000011b06840000ed919c0001118000ac030e48300000008fe00000009ca0004c81f900863920000fc000000045423c00000002ec8000ec64ff0928000cbc979314120cc0a0000001aa0c9000000000013c869c000000000010819e0c1ceb072a03409dc29087c155a2ec6a645940f268136a000000000035c4622849e8d21664a000126cb2c3291938000a3878f16f23881c07b33809eb52e20e242710a89ea3a01a08339148000390000084867343fa638604000500000000087d4a4000000000000000010b03b700013e4c00000000061cf981494dc82f8778000000000000060347d0c488ba3db45485c0cfa1b621f075d0e00ad0001be000000000005dc00000020580000007b812600000000c90000000000a390e399840005c01778000b32a54000171000000000003b00000003cc80001ac95600000000001de41704641823ef0000574d749f93150000a5212d3e09a1cf140002a780000005473c7000000013f19d00000002390e108b12de0002c6800000000009c00000000004e0800070600029d90e866a0000000000000000455800860854101a8870000374000000000000009d17700000000e3000000039452a8acc06c0002898000ec2903000000039e83b00021d0a6e0093012930c2e92b0000000b6097d000000000020b00000
  | 27 => 0x1a2132a0004b98000c9628942080008f83dc00023440000d200022240000000ba800043224b22980002180000001704d1c1f623f13c800042f3b89094c1216936203d830a0002e59ce400000000018953aa0000501c74dd647500022688f0a560000000eac5651d79f5524aa1f3a00d153086d51ca9cf53ce00021c29b4d9400038816481f85561412764b4e7af1aa8bb483a04147500000003f60488bc1092000211256c662507000040c00075019527cc00050246b000000070b097000136e3fa2a187e400091617384d44dc8322609420fd08c122e17612e450c0409ed936600051b00000004bf0b9000000099e00000000009c700000000002f11eb902400000000024b915e62f34697b87000002c28000ff81db152a424a9000000001780001f11968e240007fd3f680000000004a700011be000000231c48a2be1cc8fa53fe9e125b9878dc08883dca968cf095534480000006a331d03511864964538000f3400000000000000001c217a89546f508517f92466cf00008300000000001ca0000a3521680000003b23ae000097600001ea1b80000000000144abe4464870db400005c3eba3647d4338000000000027a35f03680003a90002468fa670c0001e340000002b7000122e854387800039800050f000147035f296062836a14c47d96f800000049f80003241
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x8062a0f2300250fa726801cab2a8181000000139a86800a80000280000b1f9d8a329604b0a40000080016801205249f10000da00e0012a09a0015a78c02002c00000022089b2d9933298d00001818809d00002d29228e91070080c002c0000200c38080000101c000000080804180020000c0408000c000c0004240b834866107158d5200615e1f8158c635480121d942056318d5200615e1c8158c6354801a16942056318d52006856508158c635480105f976194318d52004952458650c6354801258906194318d5200515245635c063548014589058d7018d5202e0da0574992615480b836815d26418552006075d28399061548012549360464185520058564e6450461549c7a159420d411855271e859d08350461549c7a157420d411855200685d08835046154801a154220d41185520068520f4350461548012549360740185520058524d4190061548018358750440185520058524d411006154801a1583504401855200689609411006154801454935c461d815200516241641cd60548018547320563581520051c241641c5605480145593180715815202e0d1c584185605480103d981d061581520060761073185605480b8667660851d853265691d8d82144614c80b43491549741853271e151458710c614c80103f985d07458a5100417e61731cd62945c745693d907154b3100417662761cd528c40188c73608705903102c8d24585c81640c40b83687593715483100705593731c5520c401855861cc715483100705590731c5520c401c447358871548310061321d62549310c401854762057354b3000417662761cd528c001456919d87354a3002e0d2057454a618c00105d980c07654930006151d8815cd524c001c1431190715493000427259841c5324c00109d98190714c93000705144641c5324c00142d921d764185300050b64875190614c0c705d980c2769453000685a0464d94314c00181c86d95740c53031d45a47655d0314c00181c86195740c5306be0721b525d0314c16709e96e1f640c5304550725974548314c00181c865d1520c53031e4520574548314c001c0c645c9520c53002e1c1c580085650c00b864716085158830006151cc815d9520c0018548320576548300051524576dcd520c00b074916187154830144272617458c318800b06c976085158d2002e191c582145634800103d989d464d85200048d66064147614800b8667660851d85200048d660641446148001a27646085118520006891918214461480f9a44216085198e103e69414580086638400b872606187154a1000515a4f641c552840f9c168498c7154a103e705612631c552840f94569318c7154a1000417e61731cf654400147090504765491000718485201d9524400146592040765491000698589801c5520400ba62815895244010
  | 1 => 0x17800c9b800900142b800031000011970030000000000000000000000026002f00002eb1801c000003098014a1003223838019a1a8878005802590802e002c931eaf841e15000ba
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x5206430100080030158724d41100615480190249b04a088030aa400a2268073608705903100482b52188c838aa49800301598144641c5324c001602d10a2320e29926000c05a4486d95740c530
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x60059868851190714c930
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x2
  | 6 => 0x4b
  | 7 => 0x4d
  | 8 => 0x4e
  | 9 => 0x138d
  | 10 => 0x4
  | 11 => 0x94b
  | 12 => 0x94d
  | 13 => 0x94e
  | 14 => 0x124b
  | 15 => 0x124d
  | 16 => 0x124e
  | 17 => 0x138b
  | 18 => 0x138e
  | 19 => 0x98d
  | 20 => 0x98e
  | 21 => 0x128d
  | 22 => 0x128e
  | 23 => 0xcb
  | 24 => 0xcd
  | 25 => 0xce
  | 26 => 0x9cb
  | 27 => 0x9cd
  | 28 => 0x9ce
  | 29 => 0x12cb
  | 30 => 0x12cd
  | 31 => 0x12ce
  | 32 => 0x168b
  | 33 => 0x168d
  | 34 => 0x168e
  | 35 => 0xb0d
  | 36 => 0xb0e
  | 37 => 0x140d
  | 38 => 0x140e
  | 39 => 0x24b
  | 40 => 0x24d
  | 41 => 0x24e
  | 42 => 0x144d
  | 43 => 0xb4b
  | 44 => 0xb4d
  | 45 => 0xb4e
  | 46 => 0x144b
  | 47 => 0x144e
  | 48 => 0x16cb
  | 49 => 0x16cd
  | 50 => 0x16ce
  | 51 => 0x14cb
  | 52 => 0x14cd
  | 53 => 0xccd
  | 54 => 0xcce
  | 55 => 0x170d
  | 56 => 0x170e
  | 57 => 0xd4d
  | 58 => 0x94055
  | 59 => 0x94056
  | 60 => 0xd49
  | 61 => 0x1a09
  | 62 => 0xd4c
  | 63 => 0xd4055
  | 64 => 0x138955
  | 65 => 0x138956
  | 66 => 0x98955
  | 67 => 0x98956
  | 68 => 0x128955
  | 69 => 0x128956
  | 70 => 0x94b15
  | 71 => 0xb0956
  | 72 => 0x95415
  | 73 => 0x140956
  | 74 => 0x16c956
  | 75 => 0x14c9
  | 76 => 0x14c955
  | 77 => 0x14cc
  | 78 => 0xd4955
  | 79 => 0x139256
  | 80 => 0x99256
  | 81 => 0x99255
  | 82 => 0x14d255
  | 83 => 0xd5255
  | 84 => 0xb1395
  | 85 => 0x138b15
  | 86 => 0xb1396
  | 87 => 0x139415
  | 88 => 0xd5395
  | 89 => 0xb89
  | 90 => 0x2cb
  | 91 => 0x14c995
  | 92 => 0x1609
  | 93 => 0x130b
  | 94 => 0x10b
  | 95 => 0x2c9
  | 96 => 0x14d295
  | 97 => 0x14c0d5
  | 98 => 0xd40d5
  | 99 => 0x9ca
  | 100 => 0x9d455
  | 101 => 0x249d6
  | 102 => 0x249d5
  | 103 => 0x9c255
  | 104 => 0x9c256
  | 105 => 0x1449d6
  | 106 => 0x1449d5
  | 107 => 0x9d456
  | 108 => 0x14c9d5
  | 109 => 0xcc9d6
  | 110 => 0xcc9d5
  | 111 => 0x9ccd5
  | 112 => 0x9ccd6
  | 113 => 0x1709d6
  | 114 => 0x1709d5
  | 115 => 0x9d715
  | 116 => 0x9d716
  | 117 => 0xd49d5
  | 118 => 0x1789
  | 119 => 0x130c
  | 120 => 0x17c9
  | 121 => 0x134c
  | 122 => 0x14d2d5
  | 123 => 0xd52d5
  | 124 => 0x168a
  | 125 => 0x145696
  | 126 => 0x169455
  | 127 => 0x169456
  | 128 => 0x2cc
  | 129 => 0x14d695
  | 130 => 0xcd696
  | 131 => 0x168cd5
  | 132 => 0x168cd6
  | 133 => 0xd5695
  | 134 => 0x140b16
  | 135 => 0x14cb15
  | 136 => 0xb4255
  | 137 => 0xb4256
  | 138 => 0xd4255
  | 139 => 0x144b56
  | 140 => 0x14cb55
  | 141 => 0xccb56
  | 142 => 0x170b56
  | 143 => 0xd4b55
  | 144 => 0x16d456
  | 145 => 0xd5455
  | 146 => 0x14d6d5
  | 147 => 0xcd6d6
  | 148 => 0xd56d5
  | 149 => 0xcd4d5
  | 150 => 0x14ccd5
  | 151 => 0x1714d5
  | 152 => 0x14d715
  | 153 => 0x14b
  | 154 => 0x8e
  | 155 => 0x198b
  | 156 => 0xa4b
  | 157 => 0x134b
  | 158 => 0x150e
  | 159 => 0x20e
  | 160 => 0x19cb
  | 161 => 0xbcb
  | 162 => 0x154e
  | 163 => 0x5cb
  | 164 => 0x3ce
  | 165 => 0x17cb
  | 166 => 0x1a4b
  | 167 => 0xecb
  | 168 => 0x15ce
  | 169 => 0x14c
  | 170 => 0x2d253
  | 171 => 0x2cd
  | 172 => 0x1a0d
  | 173 => 0x95416
  | 174 => 0x94256
  | 175 => 0x95496
  | 176 => 0x125396
  | 177 => 0x124216
  | 178 => 0x124996
  | 179 => 0x10c
  | 180 => 0x24053
  | 181 => 0x3ca
  | 182 => 0x139a15
  | 183 => 0x139255
  | 184 => 0x138d55
  | 185 => 0x1302d3
  | 186 => 0x1314d3
  | 187 => 0x11393
  | 188 => 0x1242d3
  | 189 => 0xcb56
  | 190 => 0xd5d6
  | 191 => 0xd8d6
  | 192 => 0x5c9
  | 193 => 0x9c2d5
  | 194 => 0x589
  | 195 => 0x9da15
  | 196 => 0x9d4d5
  | 197 => 0x9cd55
  | 198 => 0x169716
  | 199 => 0x25253
  | 200 => 0x254d3
  | 201 => 0x242d3
  | 202 => 0x15ca
  | 203 => 0x1454d3
  | 204 => 0x1442d3
  | 205 => 0x2c253
  | 206 => 0x24b93
  | 207 => 0x2d453
  | 208 => 0x259d3
  | 209 => 0x14d453
  | 210 => 0x2d6d3
  | 211 => 0x1a0c
  | 212 => 0x24d55
  | 213 => 0xd0c
  | 214 => 0x252d5
  | 215 => 0x1a0255
  | 216 => 0x255d5
  | 217 => 0x24cd5
  | 218 => 0x188c
  | 219 => 0x25a55
  | 220 => 0x24ed5
  | 221 => 0xb5496
  | 222 => 0x16d2d6
  | 223 => 0x16d396
  | 224 => 0x16c216
  | 225 => 0x16ccd6
  | 226 => 0x16ce96
  | 227 => 0x58a
  | 228 => 0x18ca
  | 229 => 0x25453
  | 230 => 0x16c2d3
  | 231 => 0x9296
  | 232 => 0x151296
  | 233 => 0x150996
  | 234 => 0xb82d3
  | 235 => 0x2cb93
  | 236 => 0x21416
  | 237 => 0x20b16
  | 238 => 0x155416
  | 239 => 0x154b16
  | 240 => 0x3d716
  | 241 => 0x1715d6
  | 242 => 0x1a57d3
  | 243 => 0x15ccd6
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1772
  | 6 => 4706
  | 5 => 2677
  | 4 => 103
  | 3 => 7
  | 2 => 1
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (72644+((h/590+packedAt gbK7 (65564+(h % 590)*12) 12) % 2339)*12) 12
  | 6 => packedAt gbK6 (246272+((h/1568+packedAt gbK6 (225888+(h % 1568)*13) 13) % 6212)*14) 14
  | 5 => packedAt gbK5 (169539+((h/892+packedAt gbK5 (157943+(h % 892)*13) 13) % 4275)*13) 13
  | 4 => packedAt gbK4 (7482+((h/34+packedAt gbK4 (7210+(h % 34)*8) 8) % 163)*8) 8
  | 3 => packedAt gbK3 (575+((h/2+packedAt gbK3 (567+(h % 2)*4) 4) % 10)*4) 4
  | 2 => packedAt gbK2 (93+((h/1+packedAt gbK2 (92+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff0780fffc0fffff83ffe01fc0cf707c39f3f3
  | 1 => 0x3ff800f81ff0f807fc1fffe007349f9e26ccfc
  | 2 => 0xc1ffff001fff0007ffe0fffff838e1e3c70f1f
  | 3 => 0x1ffffffe0000007ffff00003fc0fe03f80fe0
  | 4 => 0x1fffffffffffff8000000003fff0003fff000
  | 5 => 0xfe00000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x5200801a24010a31813120498041302c085171
  | 1 => 0x252808690d90d052a40a4ac08314069622c4b4
  | 2 => 0x80533100122a00844a4095161828c140c50a0a
  | 3 => 0x119ddab740804127739c01832dc0fa03780fc0
  | 4 => 0x21e66cc59bcce5c02008060437be0003b7a000
  | 5 => 0x3800700603088600431018183efffdf8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaece8faeae8e0feeaece8faeae8e0feeaece8faeae8e0feeaece8faeae8e0feeaece8faeae8e0feeaece8faeae8e0feeaece8faeae8e0feeaece8faeae8e0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36971
namespace PEqualNP.Outside.L_meta_36971
open PEqualNP.Outside.L_meta_36971.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 6 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 24 := bs2_3_0
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
theorem bs2_4_96 : Interval s2Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 117 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 46 := (concat bs2_5_0 bs2_5_32)
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
theorem bgb_2_0 : Interval gbAtlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 1 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 7 := bgb_3_0
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
theorem bgb_4_96 : Interval gbAtlas 4 96 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 103 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96))
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
theorem bgb_5_2656 : Interval gbAtlas 5 2656 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2677 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat bgb_5_576 (concat bgb_5_608 bgb_5_640))))) (concat (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 (concat bgb_5_768 bgb_5_800))) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)))) (concat (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120))) (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)))))) (concat (concat (concat (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472))) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)))) (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792))) (concat (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984))))) (concat (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144))) (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304)))) (concat (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464))) (concat (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)) (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656)))))))
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
theorem bgb_6_4704 : Interval gbAtlas 6 4704 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4706 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992))) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))))) (concat (concat (concat (concat (concat bgb_6_1184 bgb_6_1216) (concat bgb_6_1248 bgb_6_1280)) (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)))) (concat (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568)) (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728))))) (concat (concat (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 bgb_6_1856)) (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016)))) (concat (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176))) (concat (concat bgb_6_2208 bgb_6_2240) (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336))))))) (concat (concat (concat (concat (concat (concat bgb_6_2368 bgb_6_2400) (concat bgb_6_2432 bgb_6_2464)) (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)))) (concat (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 bgb_6_2752)) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912))))) (concat (concat (concat (concat bgb_6_2944 bgb_6_2976) (concat bgb_6_3008 bgb_6_3040)) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200)))) (concat (concat (concat bgb_6_3232 bgb_6_3264) (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360))) (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520)))))) (concat (concat (concat (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 bgb_6_3648)) (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808)))) (concat (concat (concat bgb_6_3840 bgb_6_3872) (concat bgb_6_3904 bgb_6_3936)) (concat (concat bgb_6_3968 bgb_6_4000) (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096))))) (concat (concat (concat (concat bgb_6_4128 bgb_6_4160) (concat bgb_6_4192 bgb_6_4224)) (concat (concat bgb_6_4256 bgb_6_4288) (concat bgb_6_4320 (concat bgb_6_4352 bgb_6_4384)))) (concat (concat (concat bgb_6_4416 bgb_6_4448) (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544))) (concat (concat bgb_6_4576 bgb_6_4608) (concat bgb_6_4640 (concat bgb_6_4672 bgb_6_4704))))))))
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
theorem bgb_7_1760 : Interval gbAtlas 7 1760 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1772 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)) (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 bgb_7_416)))) (concat (concat (concat bgb_7_448 (concat bgb_7_480 bgb_7_512)) (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640))) (concat (concat bgb_7_672 (concat bgb_7_704 bgb_7_736)) (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864))))) (concat (concat (concat (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)) (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312)))) (concat (concat (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536))) (concat (concat bgb_7_1568 (concat bgb_7_1600 bgb_7_1632)) (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaece8faeae8e0feeaece8faeae8e0feeaece8faeae8e0feeaece8faeae8e0feeaece8faeae8e0feeaece8faeae8e0feeaece8faeae8e0feeaece8faeae8e0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808936 * 2 ^ 32 + 4209699040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36971.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,5]⟩,⟨.or,[2,3]⟩,⟨.and,[1,7]⟩,⟨.and,[3,4]⟩,⟨.or,[0,9]⟩,⟨.or,[8,10]⟩,⟨.or,[4,8]⟩,⟨.or,[2,6]⟩,⟨.and,[0,12]⟩,⟨.or,[13,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4209699040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4209699040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36971

open PEqualNP.Outside.L_meta_36971 in
theorem PEqualNP.Outside.L_meta_36971 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4209699040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4209699040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
