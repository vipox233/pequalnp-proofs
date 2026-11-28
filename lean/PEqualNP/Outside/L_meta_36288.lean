import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36288.Model
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


end PEqualNP.Outside.L_meta_36288.Model

namespace PEqualNP.Outside.L_meta_36288
open PEqualNP.Outside.L_meta_36288.Model
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

def SBf (j : Nat) : Nat := [6, 6, 8, 7, 8, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36288

namespace PEqualNP.Outside.L_meta_36288
open PEqualNP.Outside.L_meta_36288.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x14c38610228d00f20724b0010c04000081006ddf43be43bc43dc439c43bf42bd42df32dd32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x610a74800b30d000880a012524794e438ea90871d5110e3ca021c714d428e2a6651c544ca38a6a0c7153318e2a2631e539023ca9184715030
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x308808558454cca0d621533183588540c2156115030
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 13
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
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (297+((h/5+packedAt s0K4 (272+(h % 5)*5) 5) % 21)*6) 6
  | 3 => packedAt s0K3 (371+((h/4+packedAt s0K3 (351+(h % 4)*5) 5) % 17)*5) 5
  | 2 => packedAt s0K2 (155+((h/1+packedAt s0K2 (152+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffff07fffc1ff83ffff07ff07ff07fe7cf3cf
  | 2 => 0xf07fff83fffe1ffc1f07f87ff87ff83fa33cf3
  | 3 => 0xff83fffc1fffe1ffe007ff87ff87ffc1c3cf3c
  | 4 => 0x3ffffe00001fffff80007fff80001fc0fc0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x8108111084820000a5090089008902940c5145
  | 2 => 0x24112209091030940a42485248525028a12492
  | 3 => 0x4222442052210329408495049504a501428a28
  | 4 => 0x6b5b894a43b555ce73d0c447e660318df40fc0
  | 5 => 0x8c630e739c3999f39ce7e660c440c631fbf000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcc0fcc0fcccfcc0fcc0fcc0fcccfcc0fcc0fcc0fcccfcc0fcc0fcc0fcccfcc0fcc0fcc0fcccfcc0fcc0fcc0fcccfcc0fcc0fcc0fcccfcc0fcc0fcc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36288
namespace PEqualNP.Outside.L_meta_36288
open PEqualNP.Outside.L_meta_36288.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x40c092002b2984051c00203bf43bd43be42bc42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x100c0008008ea98852c525065ca5205554430
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
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
  | 4 => packedAt s1K4 (208+((h/4+packedAt s1K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s1K3 (112+((h/1+packedAt s1K3 (108+(h % 1)*4) 4) % 11)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 2 => 0xc3fffc1f83fffff0783fe1ffe1e07fffa63c9f
  | 3 => 0xfc1fffe003ff87ff803ffe1ffe007fc1c7cf1c
  | 4 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8040888500808002904c02240229109408d131
  | 2 => 0x10891048252442502a11214921422528a22486
  | 3 => 0x895229034a480ca58426541654054a85454b18
  | 4 => 0x2a9c4252606d57394e83111b99960309f00ec0
  | 5 => 0x3318739c738e67ce773b998311180c31ffb000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0faaafaa0faaaf0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36288
namespace PEqualNP.Outside.L_meta_36288
open PEqualNP.Outside.L_meta_36288.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x4817e53902faa7206f90e40de21c817e52903dca5205b94a40bea9481ed52902daa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037c84a06f10940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea9081bf421037a84205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa51877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830f7290616e520c2faa4187b54830b6a9061df320c3ba64185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20f7a1641ec42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f7a1241ec42483dc64907b4c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb18e21f531c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb18a21f531443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f721465ed428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbdc84997b50932f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41ef29c835e53906faa720f754e41aea9c83bf439077a8720df94a41bea9483be42907788520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa9283ef52506dea4a0df14941f6292836c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620efd0c41dea18837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331efa1e63dc43cc6fca598fb94b31b7296637d52cc7daa598db54b31ef99663dd32cc6fca198df54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f621443ee32887da6510df94621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043ef42087d88410fb8c821f6990437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037c85a06f10b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x6824f213a000000000000004ec000002c47dceb17521e5dcc920b0000000001f0006c0000002c6000000001ce9510315b23e2f042a6a000000001be00063055012142785171e62a01f8130604ae6c5201733ce001460473ba728000000005a80000019c020880000f02b400000004001158514ca000668553340c0b88b94ce760001434bca38e49373b23f93a8da3e22cd0919b2082e8001c5408864c39fb0007d0cea973de924c200004625141a111967d8170d1152000000f2482419430003f2000002850000004000038c0000025647c4a4e6083000058029a518824400000000000000004d6434408ca000590000000ec388000000000000000000000123800000000001a1000000000d80981690a8742421a0c11cb49a384258d918a16c319390146e4031ba000801381934ec1081c800468660000190622c8001ce3821289e05300062c000004587cc588002a6000d300047a0000003d0007f8000670000000006b4c4001118e94fc53c00000034138772210000000000015e000000003faa351880024a47400000000470f708c00000119a1008a000c783f00669106800472940310b6526000001d132c000000000002944f015000150cf2642669bc0000018273cd9155470000cb8be000034f18f94400000020248c000000000004500009c000524eb80009a0007c0000d85b88d81d2a85110e8001d60000009a000a1c00089230000b903a28e000891c00020000040100000e004020050020140800000201000800002000000000000040000800a0100000300000c00001004008000030000080000000002c03804004008000040000000000702400400800000004030000000200080000000000800000000040000000200580000400c0100100200c008000020041480500801400007002020008000000040180002400403000010008008270000040200300000008009000018000010020040002a000008000000000200000501000000011008028008020000140000000a010028000020240080000600400807000000028010000080b00301000002802000070000020000000000a04c0040081a00c00004000014008040010000000080002400c00000012000010020080000080200200c000030000080000200a0100300200000800804bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0x4fc000004dc000829740009ec00098064000000f50921cc2e259000080b483c00000000000000288002140ba0000000039a930c7000000238000c90000006e000350000a88004b62909782c28c4c80000000000080010000000000001204c0001024d8000000000003a00022600030c000000000000000042e0000020337e00104123000598da8ff2fa620000004a4749488750005d8001810184444100025031c3b84143e7206d8582f0060bc8f72b00a525a8047624cf91df5203d92791e384894f4a6827c5f81d82f1585bc000003142ec0025c0882ac0007c0008dc038001a019043800000000e18000000000028f5020002c80000049c5a8001d800106000038000a68001da4d109a63000000000000009440006a0000000001e3a6000138000c20b4902893003f42314c000000002710009382b8110be4f411122160000f4000000000000c04b4644c193614e6ed3b98525804c00000000000000000001bcab8714c20040028b444000000001aa770000000000000022f0000000000035a000000724c0458a417b0000008c93116827c1514a282000000340002640012d090000000000000000000000026d210000006a43e8004cc94c7a0000003984696b448000530002ac001241b41400a00025f3d852c0012e000778b822833222cb40861a86b83287a4f800000167000000000000000007995d33e000ed8b828082800000000308491ff0009140008a0004542b21e18c76800000366000000000000dc001d04ba9f4000001109e11d03e4e49108d205216570540140000acbd00b000000f29172a490c0000043481c280000002f4048ea2548703314500000051a300001b41209545a0010c03512e7a8000cc44e568278e52145b0000002708c87da9400033d1f8e300006c0022a000a20fd23c0002b8db00e0007f1348e416ea080028441e25936a552bc001071f836e688f692b2c20007880446a5b43f80017e000b28d7000710001e20003e86f279356580de1590006f43480001e00000000000000000c8108928000000000000000000000000000000000ca84000085800000000000a70002489fc838f04e600000000354148931a300000000000000178d607900040cd78d30000000000028408484817000000000003400001b09d3d6094fa8330e0618700003709d0af9d5000650000001be9e83d80034e000840383c086c001d41f8000c690c21c001452013385f047800524000c82290009611b17f0dc4d46e9013e0358c49c71a400000000000000778000000014a800226a580000008
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x2310c355518c430d5544310c35551cc03097d95300c29c644c030d5545300c27b654c0309798f54c825d63d5320cb18954c825e63153209758c54c823e64d4f208f59353c831e5494f20c755253c834e6294f20c795153c831d5454f208f99053c823d6414f20cb55342c82cd6310b20cb55232c82ac644cb20cb55132c834e534cb20ab19121c823e64d4e208f593538823e6414e208f59053882766114e209d584538832e5488620cb95021882e96008620cb953208825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d185534823e6414d208f590534826e65d0920b358c424826c654c920ab19132482e8604c9208f990514823d64145209798c514825d63145209b99721482ac6448520ab992204826e62d50209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209b98853082766114c209d584530823e64948208f592520825e63948209758e520823f64544208f191510826d6588420ba580210823e64940208f592500826f65480209ed95200825e63d53109758f54c426f62553109b18954c423e64d4f108f59353c423e6494f108f59253c426e6294f109b58a53c423f6454b108f19152c423e6414b108f59052c425e6314b109758c52c426e62d52109b58b548425f63552109718d548423f6454e108f191538423e6414e108f590538426e6214e109b588538423e64d4a108f593528423e6494a108f592528425e6394a109758e528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c715053443556114d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910da5805244354538c5109d195314436852881109e195204425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109e980520435553c40109e596100436952840109dd95100435553440109ed9510043695244010
  | 1 => 0xc66f62551319b189544c67b60551319e181544c65e65d0d31b3588434c63e64149318f590524c69c644c931b5185324c69e648c5318f990504c63d64141319b988504c66d62141319798f540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63f64548318f191520c63e64944318f592510c65f654c4319dd95310c63f64540318f191500c65e63153219758c54c863f6454f218f19153c863e6414f218f59053c863e64943218f59250c865e63d52219758f548863e64d4e218f593538863e6494e218f59253886cd6310a21ab191328863f64542218f191508865f63542219718d508863e64951219bd89544863e65151218f992534863d6494d219b58a534863f6454d218f191534867b6054d219e181534872c54885219798f540865d63d50219e983540867960d50218f596540872c62550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c21cb553420866d6510821b358c420866d658c821cb55232086ac644c821cb551320874e534c8219bd9521086ac64484219dd95210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500876b4254021da109500876a3254021da4c9500876b2154021da485500869d6310b409798e51d025d6394740ab18941d02ad6210e409798e529025d6394a40d398e529034d6394a40cb90e529032c4394a40cb94b429032e5250a40a798e419032e5290640cb948419032e52d02409b988535026d6214d40d3988535034d6214d408f997435031c53d0d40c714d435031c53909408f994425029d6310940c714c425023e65d0540c714f415031c5350540ab189415031c5390140ab98a405023d6590c40ab588431023f65508409bd89511026c62544408f596411029e63904408fd95401029c63500409ed95401026e62153309b58854cc23f6454b308f19152cc23e64947308f59251cc26e62d52309b58b548c2cd6210e308f992528c23d6494a30a7191328c23f64546308f191518c26f62546309b189518c29e648c6308f992544c25f63551308f994544c25e65cc530c7153314c31c544c530c7152304c26e62d50309b58b540c27661d50309d587540c23d6595030c718d540c23e64150309b988540c26d62150309d984540c2756115030c7553430c25d6510c30b3588430c32e5494830cb552520c32e5454830cb551520c31d54cc830a7191320c31d544c830d3949320c3365494430cd552510c3665294430d954a510c3365454430cd551510c3665254430d9549510c3574354430d510d510c3573254430d54c9510c25d658c430a799
  | 2 => 0x80b43145e00025e83c0008734600008a112342445d1863ae04cb5800000000000000002d48900e1a0348ea8000007907d0000001e0c19370000000000011a000000000007e90700027c00000000000000000ad0001c8251fc000600950000464e80016d0dc308001f80aa3a0000000001b4130ed0006405419a1ce1480000000000000135000000000001164048e1af326298ac000000000bd1913147a80d8f03d282c7100000000000000000650d00f20004ec001442365ec00000000220498000008606d800000024869b10001c0000ac0006d44f90e42c514ec9f40000001a1b60c87b0fb000052000000d10fc001030cf0e2804be8001085cc0000000009000109424524a31f305c354e4000000000858000000000001c0003cc001000000000200806014010040401001000010100000401034000180500001004010040200801064060000102405024010000201c02010010000001405008030040600004014000080a0040204014018010040001000000010040000001000080080103400004100000200400008030000100c0000402028030000401000000060000700001004030580000800000000000000000000000040200009008050000000001014140300001c0302c000000000007014000080100403000030000200002000010000402c03008000280601c00000000100000001000030000300000004000066f62547439b18951d0e6e62943439b58a50d0e3f6550c4397d954310f2f4354843d390d5210f2d4354843d350d5210e5e63947429758e51d0a5f63543429718d50d0aad6210e428f9974350a3d6590c42c754e4310b1d5310c42ab5884310b1d53d0842d354e4210a3f6550842c754d4210a6f6550842d354d4210a7661d53329d58754cca3e64947328f59251cca3f64543328f19150cca7a60d52329e583548ca3f64546328f191518ca3e64942328f592508ca3e64951328f994544cb1d6315132cb588544cb1c5490d3297195434cb2c5490932e390e424ca6c6550932e350d424ca3d65950328f990540ca5e63150329b988540cb1d54cc832cb552320ca5f654c832c7551320ca6f654c832cb551320caad6210f419b98a50d066d62943419b98a539066d6294e41d398a539074d6294e41c794f439071e5350e41c794e429069d6310a41c794c429071e53d06418f99443506ad6210d419798c525065d6314941d398c525074d6314941cb90c525072c43149418f997425072c52d0941cb149425069e6390541cb14a415063f6550c418f596421069d63108418fd9541106ac62504419dd95411065f63540419718d501066e62d53319b58b54cc71c63553319b98854cc66d6215331c755343cc6cd6210f31cb95252cc72d5494b31cb95152cc72d5454b31c755332cc69c644cb31c755132cc74e524cb31c7953318
  | 3 => 0xa50003de7dc6f80033c170ad8a00801ccea00d0000010100001e690000001f0000d285f06a2d800000000728ff00005459cd0800000000000000001d8000820003d09e8bd0007fc0016a0003c4000000425b800000006158058ff1cc174620c92045581f12c272000f58ca218830000bb3ac820258b13d054459170090228000000003e503a1942e37000002286088aa0000004b80005b3440000003f39c29c0018b3a2508f08000005880018f0004fc7b80000019400000000798ee0000c2390000002b4000000000001440005e0005904c8000000000010f3b471ce61ae0000c4bf1a731a000000de30e1185a0003ea2e4428002e45949b0001360003f8003a6270000000d8000000001d8000958c3400000001110000003780023c3580005319600074800396000c601f000000df214112360340d733a2900007b380394000000000009980000000000119000000f8877084028e91f0000000002131b4001050000c45a49116f22e53c609893fa268d69060ae450000000880000015e000000000000003d4e09e00405e00004c3e45b0cc00024a658001ed2c22cc248003243b8a70002ae23c0000000000000000000000000000000001780004e0000000024e1d0000e1000000001e32604d000000074000ae83c36e020198fd0a83200014037e58c0009700280c23950000000001600007740019922a2043312412a00003800000000ed8003780acf39c40000c03183d17c000339c5000000ef80014400000000310001021f9000868c28b71a66c80000011c4b4000e03708341c0453686b0c70aa0d64981b93812c05067000000724001c60000003c9a823e0b06008c00048c988d93c4610548cd2262500014d1a820c0f0ae3842fc949b902c048000000005d400181000164000001f82c0fda092cc28ce18580000000019700000000000000000000002fe54ca40f605041003000000654881de1300101b000170000431163560004017c2100140018234c530000904203ec2804d0006c0528003ca000d481700067c0000000073c001ee0f45d80003b000460001cd3a01800001509c13cbc9d80ea278a3941206000941770186f4000000000000010503010c660e320e000190002963743510a18c6cc000ef2be54820a050f85640000005a5d0001203760e4000ab00000000000374094000c71d4068000002641a4490a11fc2750a87d0004f09095c0006700c80003a66c0811d0005c4001aa15e3acaa96
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x3d84003950c80801d648628b4453131005c00000490143480012010db8358d6215132a1ae529a8720d0d731494250707318a520a83435c86355331838ecaa26598d0d7318954086163b2a899043525cc4254021a50e8992a010d28744855008686b9ca4a14818398e5290640a1ae429a86a060c53189415030629cc520281435c86355030838ecaa264185457210d510c28a3a264a886185991518c430c28c8a8a601850d7318954c82163b2a8996418a9516008620
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x6020400080d8798c529054180d8798e529064080d8714c625054080d8714e6290140
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 7 => packedAt s2K7 (6+((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s2K6 (718+((h/13+packedAt s2K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s2K5 (20359+((h/221+packedAt s2K5 (17928+(h % 221)*11) 11) % 1059)*11) 11
  | 4 => packedAt s2K4 (22272+((h/179+packedAt s2K4 (20482+(h % 179)*10) 10) % 860)*11) 11
  | 3 => packedAt s2K3 (1265+((h/8+packedAt s2K3 (1225+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s2K2 (244+((h/1+packedAt s2K2 (240+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x81fff83ffffe1e0ff87f87fe1fffe07d19f3f3
  | 1 => 0xfe1fffc1f87ffff07f87f87fe1c0fffee63c9f
  | 3 => 0xffe0fffe007fe3ff8007ff8ffe00ff8307cf1c
  | 4 => 0xffffff8003fffff8000fffff0003f80fe0
  | 5 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xa402088850102002900980920252212808d131
  | 1 => 0x884110480a400502882082420844a50622486
  | 3 => 0x144aa290354906a58444d50b540a950b054b18
  | 4 => 0x5954c425240d4b394d50440d992c0613b00ec0
  | 5 => 0x61988739c67193ce7667664110301863dfb000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeeeee88eeaacc88eeeeee88eeaacc88eeeeee88eeaacc88eeeeee88eeaacc88eeeeee88eeaacc88eeeeee88eeaacc88eeeeee88eeaacc88eeeeee88eeaacc88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36288
namespace PEqualNP.Outside.L_meta_36288
open PEqualNP.Outside.L_meta_36288.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x8c031300002b007c1004a18000002d2225884e9a08bc19700b4f001a986301454e20365872e0e50400520000920002800000000500138000000910000000006499200a878000080000b000410102244000c18000ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x812e12c6a1636138b46f0994caa0000000003f001f0bc000722c0e000624492153e81846174718444922f86d44003d9c808390015098011b14942374a9b4005d23918c4023000048420a21c9008221343c000e000829f201dc5c9a0e92868053c0a44e650810c42a31d801180a2b848a02b3c9f840000c24d40660787d380000000000000211482a42a001698480e8002800000066b169c4002f00274001a34000000013000003c338240000001652e2c0018c009900000d2740023c003d0c9d4e60d4b13c8a00000c40000199fc005b2c1e87c7041990ac51001d93c6a002080000452340000001b8609b4a21822881c0c9122500818000000001808481070000028180000082859900800105001102098280008102018102800082120000808202018206118002000886cf94e439ea94873e5190e7aa121db94843b6a90873e5310f3ca621eb948439ea9087ad5210e5aa421cf944439ea80873e53d0a7ca3a14f543429eaa4855e5390abaa7214f14d42d7a92853c5150a7ea0a14f95042af298855d5310a7ea9994f15332cf21e659c43ccb3ea9996715332cfa16659d42cca7ca9194f55232aea9c65ad428ca7ea8994f15132cf21a659c434cb5a849967d5132ce2a265cf524cb3e84997390932cea1265cd424cb1a84994f950329eaa0655e530cabca720d754e419f29c839e539063ca720e754e419ea94839f329073a6520cf946419ea84833e531067aa420e7cc841ce990833e511076ca220cf540419f2a6633d54cc7388798db94b31b6a96633e548c67aa918cfd51319e2a2639c434c67ea818cf150319f2a6433d54c86bca790d754f219faa4433c548879a6510cfd51219e2a2433e540867aa810d794c21aea9843cd32086f4a010de540219f29e813d52d033e65a0674cb409f28e813d54902bea6a05714d40cfa9a813c5350338a6a04714d409fa92819f325033a64a04f14540dda82813e541027ea9984f153309f2a4613d548c33887184fd51309e2a2613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f20e6996413e548827aa9104f951209eaa241cd324827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xcd39a00ec1802e70000280000000a1b92406d48b4a4180042c402d1ed00082c00c8018097910e980350054e8000009b6000053a00000803c1992a0801c8e307c038560160046b80051a900094400284000008303000820102381040000580c394d5210f0e63548438798e51d0a1c63543428d98754cca8d62d5332a598754cca8d62153328b195424ca8d6490932a3995424ca8c6550932a3185424ca8f60509329358a539062d6294e41a358a539070e6294e418758a539070d6294e418358a539061f65cca4187d95329070d524c8418718d501068d6210f31c310d52cc68d6210d318798f540c62d62150318e580540c61e63d5221c3d51328861e63d5121c355132087493254021c354932d021e639474093588535022d6214d40a3588535030e6214d4087588535030d6214d4083588535021c65cc94087195325022d6215330a3588438c21d6510c30a3588430c30c4354830c510d510c30d544cb208718d548821c63551208d185544830d544c9208798f54c421c6355210
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x290003990248c200101282b8cc6a9087219c6655093281ae431aa020c0d7298f5448606b94c728e81415c84354430818ecaa26490504715513248206b94c7aa621035c86355210
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (912+((h/16+packedAt s3K5 (800+(h % 16)*7) 7) % 80)*7) 7
  | 4 => packedAt s3K4 (4895+((h/55+packedAt s3K4 (4455+(h % 55)*8) 8) % 218)*9) 9
  | 3 => packedAt s3K3 (2420+((h/20+packedAt s3K3 (2280+(h % 20)*7) 7) % 88)*7) 7
  | 2 => packedAt s3K2 (502+((h/3+packedAt s3K2 (490+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xf07ffc3ffffc3fc1fe1fc3fe1fffc1fe8cf3cf
  | 1 => 0xff87ffc1f0ffc3fe1fe1fc3fe1c1fe1f733d33
  | 2 => 0xfff87ffe00fffc7fe001ffc7fe01ffe183ce3c
  | 4 => 0x7fffff00007ffffe0007fffe0001fc0fc0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x14000408402040004402404802504088045045
  | 1 => 0x212108848148040a0a20841220849414312512
  | 2 => 0x421251102a9220d4a1112a8554092941828a28
  | 4 => 0xb556225281aa96733542207992c0c45d80f80
  | 5 => 0x8c6643b9cce33279dd99f32110303199eff000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeee8e8eaeae8e8eeeee8e8eaeae8e8eeeee8e8eaeae8e8eeeee8e8eaeae8e8eeeee8e8eaeae8e8eeeee8e8eaeae8e8eeeee8e8eaeae8e8eeeee8e8eaeae8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36288
namespace PEqualNP.Outside.L_meta_36288
open PEqualNP.Outside.L_meta_36288.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0xd804e20000003d32a00000195a4c58e343000000000000000014147162f482401000ac105000141200b86874060200007801d00540232e000a12c00180000000000a52804400000000000000440003e00006000000080020008608082860000001ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x4617f544c37ea8984fd5130bf2a2617d544c2f8a8986f151309e2a261df434c37c86986f10d30ee21a619c434c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c37e82986f50530ef98a61dd314c3f680986f90130de20261f8404c37080987ecc130ef182617f540c37ea8184fd5030bf2a0617d540c2f8a8186f150309e2a0617e530c37c86186f10c30bf290617d520c37e84186f50830bf288617d510c37e82186f50430bf28061be400c378801877cc030fd18061dd300c3f26018764c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20df21e41bc43c837e85906f50b20bf28e417d51c837e83906f50720f790e41ed21c837c81906f10320bfaa441bf548827ea9105f95220beaa4417c5488378a9104f15220bfa9c417e53882faa7105f14e20df21c41bc43882faa5106fd0a20dea14417e51882faa3106fd0620dea0c417e508837c81106f10220fd18441f930883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20df21a41bc434837e84906f50920bfa8a417c514837e82906f50520f790a41ed214837c80906f10120fd18241f930483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20df21841bc43082fca4106fd0820dea10417e51083eca2105d94420bea8841f551082eaa2106fd0420dea08417e500837c80106f10020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10df21e21bc43c42fea5885f94b10bea96217c52c437e85886f50b10dfa0e21bd41c43ec43887d48710df20621bc40c42fea9086fd52109faa4217e54842faa9085f15210de2a4213c54842fea7085f94e10bea9c217c538437c87086f10e10bfa94217e52842faa5085f14a10dfa1421bd42842faa3086fd0610dea0c217e508437c81086f10210fd18421f930843f441087e48210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea6885f94d10bea9a217c534437c86886f10d10bfa92217e52442faa4885f14910dfa1221bd424437e82886f50510fb10a21f5214437c80886f10110fd18221f930443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c530437c86086f10c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810dfa1021bd42042fca2086fd0410dea08217e500437c80086f10010fb88021fa10043ea20087e44010
  | 1 => 0xa500c6faa018fe54031bca80637f54c86fca990ef953219f2a6437d54c877aa990cf55321be2a6437f53c86fca790df54f21be29e43be43c87788790efd0b21dea1643ee32c87da6590efd0721dea0e437e50c86faa190dfd5221bf2a443be548867ca910df55221deaa4433d54886f8a910dfd4e21bf29c437d53886f8a710ef90e21de21c437d528877e8510ef50a21bf28c43bf418877a8310fd8c621fa98c43ef21887ee4310df94221bea84437f54486fca890ef951219f2a2437d544877aa890cf55121be2a2437f53486fca690df54d21be29a43be43487788690efd0921dea1243ee32487da6490efd0521dea0a43f631487ea6290fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610ef90c21de218437e520877e8410ef50821bf28843bf410877a8210fbc8421fb10843ed21087ea4210f948421bf28043fa50086f4a010df54021fca80437950086fca7a05f54f40df21e81bc43d02fca5a05f54b40dfa1681bd42d02fca3a05f54740dfa0e81bd41d02faa9205f94e40ef29c815e53902faa7207754e40aea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd429037885205f94640bea8c81bf419037c83206f50640de20c817e509037e81207ed0240dfa9c81be539027ca7206794e408f29c81bd539033aa7206f14e40dfa9481be529037aa5204f54a40de29481bf329037c65206f4ca40de19481bf519037ca3206f546409ea8c81bc519037e63206f8c640de98c81bc319037e43206f88640de90c81bc219027ca1205fd4d40be29a81be435037886a05fd4940be29281bf425037a84a05fd4540be28a81bf415037a82a07ed0140df202817e54102fca6205f54c40dfa1881be431037a86206f10c40bf290817d521037e84206f90840dea1081bc42102fca2205f54440dfa0881be411037a82206f10440bf28081bf40103f480206f50040fca0081bf531037ca6204f94c40dea9881bc531037ea4206f94840dea90813d5210378a4206fcc840df19081bd321037864206fd4440df28881bd511027aa2206f14440df98881be311037a62206f0c440df90881be211037a42206f08440df280813e5010374a0205fd5330bf2a661be54cc27ca9985f55330deaa6613d54cc2f8a99877d0f30df21e61bc43cc3b887986710f30bf296617d52cc37e85986f50b30ef99661dd32cc2fca3985f54730dfa0e61bd41cc3be6398774c730df20661bc40cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7186f90e30de21c617e528c2faa5186fd0a30dea14617e518c2faa3186fd0630dea0c617e508c3f681186f90230de20461f8408c370811877cc230fd98
  | 2 => 0xb7ea2a14fd4542df28a85bd5150b78a2a16fd4142df28285bd5050b78a0a14f14142bf2a0853e5410afca6215f54c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332dfaa6653f54ccafca9995f55332be2a665bc54cca78a9996f90f32de21e65bf42ccb7a85995f94732bea8e657e50ccafaa1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32df21c65bc438cafca5196fd0a32dea1465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8996f90d32de21a65bf424cb7a84997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cb7c86196f10c32bf29065bf420cb7a841977cc832f719065dd320cbda64195f94432fb2886576510cafaa2197d54432baa88657e500cbf4a0195e94032bea8065f9500caf2a0195f94f41bea9e83bf43d077c87a0ef50f41de21e837e52d06faa5a0efd0b41df21683bd42d077885a0df94341bea8683bf53d077ca7a0cf94f41dea9e83bc53d077ea5a0ef94b41dea96833d52d0778a5a0efccb41df19683bd32d077865a0efd4341df286833e50d077aa1a0ef14341beaa4833d54906fca720df54e41df21c83bc43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837e50906faa120dfd4d41be29a83bf435077c86a0ef50d41de21a837f52506f8a4a0efd0941df21283bd425077884a0fdd0541df20a837f50506f8a0a0efd4d41df29a83bd5350778a6a0cf14d41dfa92833f525077ca4a0ef54941de29283bf325077c64a0ef4c941de19283bf515076ea2a0efd4141df28283bd5050778a0a0cf14141bf2a0833e54106fca620df54c41df21883bc43106fca420df54841dfa1083bd42106fca220efd0441fb20883bd41107ea8220df94041bea80837f54cc77ea998cfd5331bf2a6637d54cc6f8a998ef153319e2a663be43cc7788798df94b31bea9663bf42cc77a8598f7ccb31ee99663bf41cc77a8398df94331bea86637f548c6fca918ef952319f2a4637d548c77aa918cf55231be2a4637d538c77c8718ef10e31bf294637d528c77e8518ef50a31bf28c63bf418c77a8318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898ef90d31de21a637f524c6f8a498efd0931dea1263df324c7ba6498efd0531dea0a63f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c77c8618ef10c31bf29063ee520c6dca418df54831f6a90636d520c77e8418ef50831bf28863bf410c77a8218f7cc431fb18863dd310c7ea6218df94031fd280637
  | 3 => 0x5881c72000000000000081262c18025e6a60000c21e22820be6ec66c0cc7ac06469e22c2126b43b83442f83e82a239600851c0000000000000005047760000001ec7543a23001b85b20000002a075863000015e60638c28c1a63b408a40c00c034000020080100000100c000000030080040080000200c1d0080080140000300e0080100a0000040180100a01c010030060000680000200c000030000340200100a004010040020000000000a01c0000100803c00804000004020000000000000101200800800004000000050000180300200202c0080a00000800004002004008000000040380200400800806002000010090000040000600601002000012004000030060180700a010004000020020240180d0020040080000c000000000000040280900400c008000040600f8000000040000000200001806004000000010020100300900000001000000000000010140040100400002000801000000008010180040100100e0000000000000000001004000000000000080200100e008000120060100000d0080040000402800003000014004000060160000100000e02402000000008008000000040600000001c008000040000001c0000000000200000c0000000002c06000000010010080020080280100400c0180200600000000000000000000020180000001000800808000000080010000180300000c00000001024014008000040000200000004c00003006098000020000100300800a00c0100000a008008000000000300100000c0000000e008008040040080200abf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121fe94243bd284877d5090ff2a121de542439f29c87bf5290f7ca521ef54a439ea9487bc5290f7ea321ef94643dea8c873d5190f78a321efd4243df284873e5090f74a121ce94243dea8487b95090f78a121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210efaa421df94443bea88877e5010efaa021ef94c439f298879e5310f7ea421ef94843dea90873d5210f78a421efd4443df28887bd5110e7aa221ef14443dfa8087be5010e7ca021ef54043de280877e53d0afaa7a16fd0f42df21e85bd43d0b7887a15f94742bea8e857e50d0afaa1a16fd4f42df29e853e53d0b7aa7a16f14f42dfa8e85be51d0b7aa3a14f54742de28e85bf50d0b7ca1a14f94342dea8685bc50d0afaa9214f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42be29a85bf4350b7c86a16f50d42de21a85ef4250b7c84a15fd4542be28a857f5050af8a0a16fd4d42df29a85bd5350b78a6a14f14d42dfa9285af525
  | 4 => 0x64800005e808617674c0006c465e29e00070a52c6cc3d473a0006b80000ec3360004ac4040005020d200000048e5d20ca1286ea00000028413c00002600048a6380500004347860000007660000000a439c05a5e000055a0005ea3dc0002420000003e410e0e42cc58a0000e05503c61cc6b60003c84de66274e02855c8226540003400683c064a0000001de0000000a600000066408c2467fc37a0007687c800014e0000040006244362d04bc3a04582687b67ec0000000006786f600004a0000d657800069c7f85a200000028615c4380000000000101c21c46021be0004446344f857471800000051000000048800065a0f200032031a0000000001d019c0002b221c78042607620a27c00035a7d419a3e000028854e2ac37e00010611c32c0004320004100000002160000924ee47048200010005e7be00000077c0005f834a00075c0000b85b823410a00017a56821e6903880000004c04b42de03a19000000025072c00009800000000000013600000039e0706362205420000004242ea0000000000000002e80dc00000000058e7fe0006440006c803000033c2f645271c1d806c1fc6fe0fe2064d00c80001447aa2d26aa07800000000000007e0006c626000000012e0005cc4e846677481644c56027e06207c0000000480000002be22a3d25a04d25260005d40000000000005d059445a41e00008200009623c0000000000006fa0007d00006d254a00000060847a2fa0007b87f20002ae0001b415400000049a5aa2700006da17423e42c0007c640e0fa7da00072a56e6d40000004f634800017225a4ae2221660003780005980005240000005724460000005ec0001180ea5302a800000006a0740001244e400000c0000003da0000000006b26ca3a46ce2c601e0b64dc6886e65ee4900c07e03900000002aa6f07384fe53200000008e00000000000000081e50c00000080802e3240000001f82d81b263267c62246c00000041c7841843cc61e3d81103843120003ec1a43a80000000006201940002365564b00004620000000d00000000000002ca3860000e83ce21065c4000002260000005a876a3725880000000000002fc0000d871a59e5ae8142f07a227a4720000004080000008003ca4141ac20467e0140000000001c80544407525c00000007ba4c67e444257c02200011a0da4504b80005402e20000000005ca1ca5124020160003140f80000000005f26a429435e0001162dc7bc0004200000000000006bc1c65dc0005f01e800079000000000000000000000000056432a1f40000000000b244a0000002ce3767b404c7cc13e72824e19600000000000000061200052e66a0366ac3580002bc6745be7360000000407984c430c00000000019837079633850a5fe80400000000034e0000003427827f40006a836c43c05c0001
  | 5 => 0x17c35062a2923b67400000000ae6a23a610c05600063c0000004b60003e60000000000002d681800038a7d600000016c7341047480000006843b253e1da0001642440000000000000000002c40006180003c26be4ec00001c55e3d600079a6460000007f04aa00078c0461081380800000900000000000002e03620001ae7ee00009a0000a25960005700000000000000000000000000de36e0000007221bc15615a0000000000006de2b06560e62185143ee00000000013202a0000000000000840020000001ea0003561ce4c82240180000004b20000001024ba2143aa5c24a00001f60000002e47600000007641924ca00000071e3fe0004f40aa00000000025616a00000000000000000000000006e0004fc00061a00000000069822e0003660008066ae0000004120000000000007504d600000055800079e00000000023000000019e3fc44e7260001b60003f05ac0006b07b06603f400000000000014000000042a5220000000006c200064000004471201a00000000051e00063e18c3bc00053429a00044834c03c0003d052830a62e5b40000005060000005626f25c60b000041a54c00029c63a02c00000000052a77875e54600020077207266841800000030200050800000000000031e00080a17000035c1e67ca0007ae5445d839870860a46820200043a0000fc70c0000007d25540003185160005903220a847468a0000a03c400000000000082414c4be00000046a6c01a02286520382800000000006003742c216e0000002ee7ea00068c00000000000014266e3460001aa0000000000bc00025258461600000000043000007a0000002c00000007e26f42f40000d40000000004c261400000000000037c5bc58600e39a56c00049c5921c068273c0000000002960004a61d27a63606f84160004f00007a80006e07b26941262da0000000000000002c80007c27000ac0007880000000000000003b00001f252000073e0000000005ba12a2fe00017800000075a0007941a833223a1346e23061680002900008020000002d42ba4e671639282000074216018e4e05c40000000000000002ec47e0007a43ba6287065d67e600000000000000000030400076c1b00000006ba00000016265833a0ce4ea67a40a25c57a0000000000000c466674a6d62480002a600071000014a27478e3105366e800a0004a44cc79213a1ee1ba00000076200031c0000005a464e0940604602640003ea00069600067000000004232e0000000000000ee1fe72e5fc00081000000000000000000000069a00078a5f423200012c70277a53c1822b46863f800053876e00057e00061002426e7140000000f47e820e1e44d400059a00038226c00000038e18a0003fa21a56a3301467c02e643e0883947320f00000000003ae6dc0007ce2720001500004563f
  | 6 => 0x6664845e04e0005827dc3ac02033e0004ce26a00000060400000000060e70400020c36a4840004943641d42382987462760000004fa00050e77028e0000000006760002580000000000000000001f00007564543f230e42881a27800000000000000018820849e5b00007246e47a00e23801120003285b60000004d800003e0000341522627306ee46e59c3341dc4962a46925ce80e77e57670e4788267f680c0525005e224c3084e200000068e0000007de5c800051a1fa64c5da2f26d04986a04da61c11e0001a228a5fa1483e23160583265527fa0000121e02543684a249246448c45c5185660f65e440662609c24a58c0b40000003521221200000006500001866d809e67247c47664260c6fc0000000007c40000062b80005a62401d64f23de4220ba0007444860000000000004a80002665483540000006800c60000001305de00079c3be17e7d811400058042e5f65e60000000320002b600000000000053a000
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x3538423d64d4e108f992538423d6494e108fd91538423c6454e108f996438423c6590e10ae982438423e6510e108f194438431e5310e10c754c43842ba6010e108f992528423d6494a108fd91528423c6454a108f990528423d6414a109798c528425d6314a108f997428423c65d0a108f995428423c6550a10ae98341842b86050610a798e40842b56190210ad5844084338548c210ce1513084358534c210e610d308423e63d51108f58b544423e64951108f994544423e63151108f588544423e60151108f180544423e64d4d108f593534423e6494d108f592534423f6454d108f191534426f6254d109b189534423e6590d108f19643442ba6090d108f994434423c6510d10ad58443442ba6010d108f992524423d64949108fd91524423c645491097d8d524425c63549108f990524423d64149109798c524425d63149108f997424423c65d09108f995424423c65509108f99741442ba60d05108f19541442b860505109d195214436452485108f996404429e63901108f9944044338548c1109e1953044338544c110d614d3044398434c110bc18530442786548110f8485204425e63d50109758f540426e62d50109b58b540423d65950108f98e540423d62950108f18d540423f62550108fd85540423d61550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7d92530431c6494c108fd91530423c6454c10c7951530431d5454c10c7d91530431c6454c108f990530423d6414c109798c530426e6214c109b588530427a6014c108fd96430423d6590c10c794e430431d5390c10ae982430423f6510c108f594430431e5310c10c754c430423e64d48108f593520425e63d48109758f520423e64948108f592520426d6594810cb952520432d5494810d394e520434d5394810cb992520432d6494810cb90e520432c4394810cb951520432d5454810d394d520434d5354810cb991520432d6454810cb90d520432c43548108f990520423d64148109798c520425d63148109b988520427661148109e980520423f65d08108f597420431e53d0810c754f420432e52d0810cb54b420423f65508108f595420431e5350810c754d420432e5250810cb54942042b860508108f992510423d64944108f597410431e53d0410c754f410432e52d0410cb54b410423f6550410c794d410431d5350410cb949410432d52504108fd96400423d6590010a798e400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010c794c400431d5310010cb948400432d5210010ad584400436552c40109e59610043595384010da54a10042776544010d954910043b240440109ed9510043595344010da54910043b14144010
  | 1 => 0x823f64546208f191518823e65d06208f195418829e6390220ab58a40882ad6210220ce1523088338544c220d614d3088398434c2208f98f544823d61d51208f992544823e65151208f98c544823d61151208f993534823d64d4d208f992534823d6494d208fd91534823c6454d209dd8553482746154d208f996434823c6590d20ae982434823e6510d208f19443482ad6210d20ae980434823e65d0920ae983424823c6550920ae181424823e64145208f590514825e63145209758c514823e65d05208f197414823e65505208f195414836451485208f996404829e63901208f9944048338548c1209e1953048338544c120d614d3048398434c120ba189304825e63d50209758f540827661d50209d587540823d65950208f98e540823d61950208f18d540823f62550208f589540823f61550208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7d92530831c6494c208fd91530823c6454c20c7951530831d5454c20c7d91530831c6454c208f990530823d6414c209798c53082766114c209d584530827a6014c208fd96430823d6590c20c794e430831d5390c20ae982430823f6510c208f594430831e5310c20c754c430823e64948208f592520823d65d0820c794f420831d53d08208fd95420831e5350820c754d420823e64944208f59251083365494420cd55251083565394420d554e51083366494420cd59251083364394420cd10e51083374294420cd50a51083365454420cd55151083565354420d554d51083366454420cd59151083364354420cd10d51083374254420cd509510823f65d04208f597410831e53d0420c754f410833651d0420cd547410823f65504208f595410831e5350420c754d41083365150420cd54541082b860504208fd96400823d6590020a798e400831e5390020c754e40082ad6290020cd946400833551900208fd94400823d6510020c794c400831d5310020ab58840083365110020cd544400836551c8020d654e200837151880209bd9520083655148020ea901200827b6548020d654d20083a94248020dc545200823e63953108f58a54c423c63553108fd8954c423e64d4f108f59353c423f6454f108f19153c423e6414f108f59053c426e6214f109b58853c423f6590f108f59643c42ba6090f108fd9443c423d6510f10ad58443c423e64d4b108f59352c423e6494b108f59252c423e6414b108f59052c425e6314b109758c52c423f65d0b108f59742c423f6550b108f59542c42b86050b10d914921c429e63903109798f548425d63d5210a798f548423e63d5210c798f548421e63d5210c758f548423d62d5210cd587548433a60d52108f98c548423d6215210cd584548433a60152108f99
  | 2 => 0x62d51308f587544c33960d51308f992544c23e65151308f98c544c23c63151308f588544c23d611513097997434c2da60d0d308f996434c29e6390d30ae982434c23e6510d30c7d50434c29e6510d30c7994434c29d6210d30a7584434c39b6010d30a7980434c3986010d308f990524c23d64149309d984524c27561149308f997424c23c65d09308f995424c23c6550930a718d424c2b86050930a7193324c29c644c930d3149324c2d8604c9308f990514c23d64145309b988514c26d62145308f997414c23c65d05308f995414c23c6550530a718d414c2b86050530a7193314c29c644c530d5145314c2d8604c5309e997404c2da63d0130e610f404c23e6590130a798e404c2ba60901308f994404c33b5410130e6d0c404c3984310130ae994404c33a6510130e6d8c404c2ba6310130e618c404c2b96210130e6cc8404c3993210130ae584404c39b3110130e64c4404c2ba64cc130e610f304c29e648c130e6102304c25e63d50309e983540c23e63d5030c798f540c21e63d50308f58b540c23d61d50308f983540c33a60d50308e983540c26e62150309b588540c27661150309d584540c2ad6215030ad584540c23e6315030c798c540c32e62150308f588540c32d62150308b588540c33661150308f584540c33561150308d584540c23e6015030ce980540c23e6494c308f592530c2ba6090c30c794c430c2ba6010c308f992520c23d64948308fd91520c23c64548308f997420c23c6550830cb949420c32d52508308f992510c23d64944308fd91510c23c64544308f997410c23c6550430cd945410c33551504308f992500c23d6494030a798e400c23e65100308f194400c29e6310030ce940400c31c54cc030ce152300c2d9638c03097d95300c31c544c030e6901300c398404c0309ed95300c338544c030e690d300c398434c030b6d95300c35b654c030e6d91300c398644c030e6d51300c35a544c030d6151300c398544c030c6151300c359524c030e6d09300c399424c030d6545300c39b414c030e6505300c23e63953208f58654c823c63553208fd8554c823e64d4f208f59353c823f6454f208f19153c823e6414f208f59053c82766114f209d58453c823f6590f208f59643c82ba6090f208fd9443c823d6510f20ab58843c823e64947208f59251c823f65d07208f59741c823f65507208f59541c82b86050720a798e40c825e63d52209758f548829e63d52208f98f548831e63d52208798f548831d63d5220cb58b548823d61d5220ce983548823e6315220cb588548823d6115220ce980548823e64d4e208f593538823e6494e208f592538823f6454e208f191538823e6590e208f19643882ba6090e208f994438823c6510e20c794c438831d5310e20ae98043882ba60d0a20ae181428823e64946208f592518
  | 3 => 0x640a798c519029d6314640c794c51902ae6214640ab58851902ba60146408fd97319031e53cc6408f996319023d658c640c794e319023f654c6408f195319031e534c6408f994319023d650c640c794c31902ae620c640ab58831902ba600c640ae580319023e65c86408f597219031e53c8640cb54b219023e65886408f596219031e5388640cd546219023d6548640c794d219032d5248640cd545219023e65086408f594219029e6308640a758c219031e5308640e948421902ba6008640ae580219031c5390d40ae982435023e6510d408f997425032f52509408f99741503375150540a798e40502b96090c408fd95431031e5310c40c754c43102b96010c40cb54b421023d6590840cd547411023d6590440b658e401023f65500409ed9540102ba60d4c408f58a531023d6194c40ce982531031d5314c40ab98853102ad6214c40ad98453102b56114c40ae98053102ba60d48408f18d521023f6154840a798c521029d6314840ad98452102b56114840ae980521023f65cc840c794f32102ba60cc840ae583321023e658c8408f596321032d528c8408fd95321023c654c840c794d321032d524c8408f994321023d650c840ad98432102b5610c840ae98032102b9600c840ae983511023c63544408fd89511029e6314440a758c51102ae6214440ab58851102ba60144408fd97311031e53cc440ae98331102b960cc4408f996311023d658c440cd546311023f654c4408f195311031e534c440cd545311023e650c4408f59431102ae620c440ab58831102ba600c440ae580311023e65c84408f597211032d52c84408f996211023d6588440cd546211023d6548440cb54921103355148440aed8121102b860484408f994211023d6508440a798c211029d6308440e948421102ba6008440ae580211029e6394040a758e501031e6394040c758e501033a6094040e698e50102b96394040e658e501029963940408f58a54cc23d6195330c718d54cc23f62553308fd8554cc31d54d0f30ae98243cc2ba6010f30c799443cc31d6510f30a758843cc29d6110f30a798043cc39a6010f30e658043cc23e6494b308f59252cc23f65d0b308f59742cc23f6550b308f59542cc29c6350b30a719332cc29c644cb308f99251cc23d64947308fd9741cc23d65d07308fd9541cc23d6550730a718d41cc29c64cc730a719131cc29e63903308f58a548c23d61952308fd89548c23f6155230ce181548c23e6494a308f592528c23f65d0a308f597428c23f6550a308f595428c2b86050a308f992518c23d64946308fd97418c23d65d06308fd95418c23d6550630ae181418c33954d0230a798e408c29e6310230ce994408c2b96510230ce594408c2ba6310230e698c408c3996310230ae588408c2b96110230c7953308c2ba64cc230c758f544c23d
  | 4 => 0xb19532486e4614c921ab58b414863f65505218f59541486af62505219d19531486e4624c521f14c9314863e64d41218f593504863e64141218f590504865e63141219758c504865e63d50219758f540867a60d50219e583540863d65950218f98e540863e60950218f18d540863c60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7d92530871c6494c218fd91530863c6454c21c7951530871d5454c21c7d91530871c6454c218f990530863d6414c219798c530866e6214c219d984530867a6014c219e580530863f6590c218f596430871e5390c21c754e43086ba6090c218fd94430863d6510c21c794c430871d5310c218f992520863d64948218f597420871e53d0821c754f420863f6550821c794d420871d53508218f992510863d64944218f597410871e53d0421c754f410863f6550421c794d410871d5350421d354f21087555388421b958a210866f6548421d354d21087a74148421e950521086776548421d554d21087a74248421e950921086e76548421d9d9521087a66448421e959121087a65448421e955121087675348421f194d21087655348421f154d21087455348421e990d21087a44348421ce95250087395494021d694e50087595394021f8486500873b6494021ce192500873a4394021ce10e500873b4294021ce50a500873b4194021ce506500863f64540218f19150087652154021ce95150087395454021d694d50087595354021f8485500873b6454021ce191500873a4354021ce10d500873b4254021ce509500873b4154021ce505500876b2154021dc88550087692154021dc48550087612154021ae98243d031e5310f40cb54b42d033551d0740c7d92539031e53d0e40c794e439031e5350e40c754c439031e53d0a40c754f429031e5390a40c794d429031d5350a40cb549429031e5310a40c794f419031d53d0640c794e419031e5350640c754d41903355150640c794c419031e53d0240d654f40902ba60d4e40c7d4e539023d6294e408f586539031f6294e40c798a539031d6294e40c718a539031f6194e40c7986539031d6194e40c7186539031e6094e40c7182539031f6554e40ae980539029e63d4a40a758f529031e53d4a40c754f52902ba60d4a40c794e529031e5354a40c754d529023c6354a408fd85529029e6314a40a758c529031e5314a40ad98452902b56114a40ae980529023f65cca40c794f329023e658ca408f596329031e538ca408fd95329023c654ca40c794d329023e650ca408f594329031e530ca40ad98432902b5610ca40ae98032902b9600ca40a798f519029d63d4640c794f519031d53d4640ae983519031e5394640c794d519031d53546408f18d519023f6254
  | 5 => 0x548c63c6055231ae982438c63e6494a318f592528c63f65d0a318f597428c63f6550a318f595428c69c6350a318fd91508c63c64542318f58b544c63e60d51318f992544c63e65151318f588544c63e60151318f996434c6ba6090d318f994434c63e64149318f590524c67a60149319e580524c63e65d09318f197424c63e65509318f195424c63e65d0531a798f414c63c6550531a718d414c63e64d41318f593504c66e62d50319b58b540c67a60d50319e583540c63d65950318f58a540c63e60950318fd89540c63c60550318f990540c66e62150319b588540c67a60150319e580540c63f6590c318f596430c6b56190c31ae982430c63f6510c318f594430c6b56110c318f992520c63d6494831cb952520c72d5494831cb992520c72d6494831cb90e520c72c4394831cb951520c72d5454831cb991520c72d6454831cb90d520c72c43548318fd97420c63d65d0831cb94b420c72d52d08318fd95420c63d6550831a718d420c72e5250831cb549420c63e64944318f592510c63d65d0431cb94b410c72d52d04318fd95410c72e5250431cb549410c74d52cc431d954a310c65f654c431d3549310c795414c4319dd95310c796434c431d9549310c73a5494031ce552500c76a5294031da54a500c73b6494031ce192500c73a4394031ce10e500c73b4294031ce50a500c73b4194031ce506500c63f64540318f191500c73a5454031ce551500c76a5254031da549500c73b6454031ce191500c73a4354031ce10d500c73b4254031ce509500c73b4154031ce505500c75b3154031d64c5500c63e63953218f98254c863c63553218f18154c863e64d4f218f59353c863f6454f218f19153c863e6414f218f59053c867a6014f219e58053c863f6590f218f59643c86ad6290f21ae98243c863f6510f218f59443c86ad6210f21ab58b41c86af62507218fd9150c863c64543218f98e548863e60952218f18d548863c60552218f993538863d64d4e218fd91538863c6454e218f990538863d6414e219e98053886796014e218fd96438863d6590e21ad58643886ba6090e218fd94438863d6510e21ad58443886b561d0a21add85428863f64542218f191508863e63951218f58a544872d62951218f586544873561951218f982544865f63551219718d544867b60551219e181544869c6355121ae181544871f63551218f18d544871c63551218718d544863f6255121cbd89544863f6155121cdd85544873b60551218f181544873860551218e181544863e64d4d218f593534863f6454d218f191534867b6054d219e181534863e6414d218f590534867a6014d219e580534863f6590d218f59643486ad6290d21ad58643486ba6090d218fd94434863d6510d21c7d4c434871c5310d21ab58843486b56110d21ad58742486b761509219
  | 6 => 0xa3d64946328fd91508ca3c64542328f587544ca3e60d51328f992544ca3e65151328f584544ca3e60151328f996434caba6090d328f994434ca3e65d0932a798f424ca3c6550932a718d424ca3e64145328f590514ca7a60145329e580514ca3e64d41328f593504ca7661d50329d587540ca7a60d50329e583540ca3d65950328f586540ca3e60950328fd85540ca3c60550328f990540ca7661150329d584540ca7a60150329e580540ca3f6590c328f596430caad6290c32ae982430ca3f6510c328f594430caad6210c328f992520ca3d64948328f597420ca3f655083297d95320cb8d424c8329bd95320cb8e434c8328f992510ca3d6494432cd952510cb355494432cd992510cb356494432cd90e510cb344394432cdd0a510cb354294432cd951510cb355454432cd991510cb356454432cd90d510cb344354432cdd09510cb354254432d5cc9510cb663254432d54c9510cb653254432ce952500cb395494032dc946500cb715194032ced92500cb386494032ce90e500cb384394032ced0a500cb3942940328fd91500ca3c6454032ce951500cb395454032dc945500cb715154032ced91500cb386454032ce90d500cb384354032ced09500cb394254032d6cc9500cb5932540329e98253d06796094f41ae98243d06b96090f41c794c43d072d52d0b419798e50d065d6394341ad58753d06ba6094f41ae58253d063d6294f418f98253d073a6094f418e98253d07396094f41ad58453d06b561d4b418f18d52d063c6054b41ad58452d063f65ccb418f99632d063d658cb418fd9532d063c654cb418f99432d063d650cb41ad98432d06b5610cb41ae98032d06b9600cb41a798e50d069d63943418f98e50d071e63943418798e50d071d63943418f58a50d071e5390e41ae982439072d5250a418f997435071c5390d41ae98243506b96090d41cbd49425063e6510941ad58653506ba6094d41ae58253506b76154d418f588535063e6014d418f98f525063e60d4941ad586525069f6354941a718d52506b76154941aed8152506b860549418f197325063e658c9418f596325071c538c9418fd95325063c654c9418f994325063d650c941c714c32506b6610c941ad58432506ba600c941ae580325069e6394141a758e505063e63141418f588505063d6590c41ae982431071e5310c41cb54b421063f65508418fd9541106776550441cd951411067a60d53319e58354cc6ba60d5331c798f54cc63d62d5331cd58754cc63e60d5331ce98354cc63a60d5331ce58354cc71e63153318f58854cc73561153318f98054cc6b56190f31ae98243cc6b56110f318f99252cc63d6494b318fd9152cc63c6454b318f99742cc63c6550b31a798f41cc69c63507318f99250cc63d64943318fd9150cc63c64543318f58a548c63e60952318fd89
  | 7 => 0xe0000000e00200c0000e0000040080100a0000080101204c0080601a0240282e0000080083200801000007002038010450080280380a000018020030220000004502c0140e00600a01c010180000100081700202c0d8000000380100a0000100781000001c0480100201c0181600201400000042008008010060000580200202006015000010088020040400f01d0240280480a00a0000080000800000007008084018140000000200e01e0080000300002809010004040020060140100000000202005800032078000000500240700b0180000080600200c0080200a01c04008002004018280060040180b0100080000f094008000000020100180100a0473b6494243ced0e5090f5b4354243ae9835290eb960d4a438fd855290e3c6054a43ad9845290eb56114a43ae9805290eb96014a43ae9835190eb960d46438fd895190e3c6054643ab9885190ead6214643ae9805190eb96014643ced425090e3d62942438f5865090f3b5294243ce94a5090f395294243ce14a5090f3b5194243ce9465090f395194243ce1465090f386394243ced8a5090f3a6294243ce58a5090f386294243ced865090f3a6194243ce5865090f386194243ced955090f3b5254243ce5495090f3b5154243ce5455090eba6090d43b65824310e3f6550c4397d954310eba6094c43ae5825310f1e6394c43ce9825310f396094c43e69825310e9d6094c43e65825310e996094c438fd855210e3c6054843ad9845210eb56114843ae9805210eb960148438fd895110e3c6054443ab9885110ead6214443ae9805110eb960144438f58a5010e3d6194043ab9885010ead6214043ad9845010eb56114043ce5405010e7a6094f429e58253d0aba6090f42ae58243d0b1e5310f429798e50d0a5d6394342ab58b53d0aba6094f42ae58253d0a3d6194f428f98253d0b3a6094f428e98253d0b396094f42ab58853d0a3c63547428f18151d0a9e6394342a758e50d0a3e6394342c798e50d0a1e6394342c758e50d0a3d6194342c794e4390aba6090e428f9974350b1c5390d42ae9824350ab96090d42ab58a5350aba6094d42ae5825350aaf6254d428f5845350a3e6014d428f98f5150a3e60d4542a7d8d5150a9c6354542aed815150ab86054542a798e5050a9d63941428f98c5050a3d61141428f5964310aba6090c42c794c4310a3f65508429bd954210b2e54508429e98354cca7960d5332ae98354ccb1e63d5332cb58b54cca3d61d53328f98354ccb3a60d53328e98354ccb3960d5332c798c54ccb2d62153328f58454cca3e6015332ab58a43ccaba6090f32ab58843cca9e63d0b32a718d42cca3e64947328f59251cca3f64547328f19151cca3e64943328f59250cca3f64543328f19150cca3d61952328f982548ca3f61552328f181548caba6090e328f992518c
  | 8 => 0x26149d408d843bd6911918015b4e816648bccf14e402908cb2142098147c1a83850312010f8a9428d8b429ce584443dc9c5218a840f40c4a9138d578d04a30ef03e4155748000000000d959103455c47854980007bc96c2b15d830d9dc0010003b94d19c8c6d108a5c000c294bce1464cba52a86c40c8000420b0894198001831800098851542d6fcf84b640018240ec3d493c92c5440017e80006740013249a0000e6c000000e3575c6fd55d034db09040010840016442e00000019900000000000009a52ac000000628000468000000f3c000000e40000a040018c4e280000000012800011497f07d40000015c090c16956491d14c69910c3d00006dd538b8166c358cd4689a0cc109291c96148fc9e8af4350ea81410cd8b84e82d00794609bce1044cc60b687609193c5465079361938aa0e7cb4c9dc8299291a8ae14ec27027933c0cd845594dc47702ac0000002fcdb56e035d1e83100885f97a48c46bd9a4b285dd1e07a83e92b00440013ec0004780d44c80016ad3cc8600014497590443cc0016c1390c588595a4dc14951f0ed03795d467c4d000000000178c2a90959e11f8d40dd497c2043f162c3743acd48e8c5e11d4f90000354d15248b0031c0a972165063c9547381b4fd8ac595d560268084d50148d0c224aed6480007e022d87c0007951b98c07b01018f966086d03c934df921d86598c921008e656240b400c050020040001f00f00002c000000300040080100a0000600108e0400000002e088028030020000000300600003014002124020040060000b82001c0000c800002040028090160080a81a00404c02005002004048010340041700502a1100002b00c0600400400802c050030200180000000a03801806006010030010200940100400801c000070180040080000601000000000014058010000500080700000c00818004000320000000000180104a0080480d004000020000080b00480106a0000100100a000000010021d004000016000188220020480300000a008000110000000080e0040080100104c01c038000060040581204a038028100240000f80201400c010330000580300100203c000720020000000003c0740000400a0dc0380202601c0000000c0040101e0000040101001a0000c8030000702d0280080140000600600803002016000000040080100186300e00c010000020542f00006c01c0000000403800000004054000010020100184400a0240381601a0000000102a0200581800002c020040100140200001a028000010020540281a01604802000004110000260100a80780000c0600c806052000018060380040100100002c0300e00c02000000000008068060180400980d006034030030000040000600000c050020040400800100a054008080200000400d0040000400600a0280880300
  | 9 => 0x143586cb10000c0184982c558000b1c000c7c00000000000038c2ec0001e46140012992d07107c50f0000c2c00000185d7e4ee88ec0651dc2555ec8700000000007148a4d0000042c000000a215a8b90f68670000d399000013b15290900000000012c05c40016dd2f00011b0f211d92b8fd14a171507cea11100e01217013d47a0939709419a10d58370000e609095e0a192885f40b8d20a640009c80016100018acfb96cd9b12a4a08880c5c0005051fd104930690000115860e500017847458d1840d690d0fa17f91680000008dc961100abc07d188d6520545c58d65912546cac84a9220a504ecf549712e8848c1c4b8b607c996478cf41668348c08e390d88e07917a0a4c0e4879588a283645b447d1408e41986b41d43e18f4fec2741f8fe46a54103fc3889f4fe19a92fd255634fccdbcc8d1e552000ce046c8cc54c412cda55015250f46a0425128474d3426c984bb93510254dd3200e96bd9984a050053009c5a9164a3861c5101802e8d9d9214f47cc4109b4f0960cc8545469c7f4ffd2ece745bcb40f44a014785a4d80609098b35470be19888684389652f982877c54085106d7b10bd74c8a171c59ce90bd0e2c1dc0582bd00400075d34151800180c09800159cb480002344e47d80013380f0000f9918d8686f4bfc8f16747ac62c03cc4c648bc81e07f09959b59484dc788d9083cf6d4f97b99d5301154cdd0709ed63c0000000002f4000d19851114ee069537cf0d8d41a4ab04408205cc264c202f86d80acbcce48054a34f5845d24cc709e56a96f4a48eb8038e4cb54ad93689fc88d36c7089796a09c08a8a1d5912080019c19f0c68f3935879d8cc00049565c001424c9c000cc0000001744fac000c14000ac018c0212b4000d55430000aac00077475151481c39c40c069904230000588560e0c00074938973000000000024c4198596180017904912dd5700000006ac1ed6213b41f0f700019d0d09924a24578c980000012c44cd2e4acc888948195134bd836c5d1a14df4650e20a61604f016306c0e797ac1d14409f056d6d1170ab40000017e00019180008b170c4fc000de89cd24076c00122c000000244d280014a80012680011815ad41cd1d3e8d78b0d02d91c0000000019ad69c0015e8489878000000ec4000620518b9948c0017d80011ec000000f04ddd7c0508cd8e9d2e098cded0600fd7759fd765958fd4000f798dd4598742d4e89780280398f5d2148e82e439559819c4ac83072d8b01fc0513a43340014f00001756d44f0800b50525585414b14550bd40014cc0000600006d51a00040000000011c4bf54ac5b00018112cc000664034000af8810944341a043b08f87b91a57f40011b4950000df00f81c043d96181ca8c090764000000000125835688000e19820f9cef96806619cc460258c7489c288a6d
  | 10 => 0x4be800074000000000000000158c6240000015b86102c0000d9923c00000021c7804bc000564be4000000cf474c00061834c968a71229144bc557472065400154c0495b040199d8e0000000000e94591380d601ad9f400183c0004b505c7780000002f15100012100018956953288945d528c0010516c50a05e575104023964094d32d97d8a5395740e686cc2dd6785d93a04098fc4f540ccb977c00000190d96d00c6f9789308c0c3a93300000000000000018381f513930c95c000c24e099a00081519093dc79931d76cf110e46e50c5818c94ff572cced6857a8bad1783d92842a4ed97291f539913c4583241900002a01380018d8d5cf5071c80d2508f4640ae56b55e4924f14ce8d4505813c298818dfcab8ea4a994b8d895f88349d04c4ca4e440005acd2d79c04d8a0c64dcd52c06c0011bd6541bc5f19d9194b5c47192c9b8a555547e400015c000af00004297d11d139c001348fdd5a0ee465c84c001a08430000030000000edc01c7680002c40019e919d2744553ac000b9c4802b8cb40000000014500006a8b396b80004d4bb4104000001400000ca0e85a18484c54f4d44d629951968ff80019798f02b4215738000000000000000a101c87e8aa93c81584655497610a833d174d319e43397fcd8cc81224eec0002081c40004149594fc1cc0014b411c0000000000010b50b8000000000000000c3c00044839144509c0400008d4dac00135cafc5752f4f35279638dd887c4a4f759c4ba10c8ebd5d0580000b7000002c5e94750814398bc210db8000000ec8fb57bc000f30000000705600dc80011ad8e47250c0000000011490c04c78a7c0019141196f070c9154d8a147eceb452d57ccf89107f8bbc68c3f517c3b52c8b8c538824000fe8001010b8450ce981b0aa40000015314812d8d3c134000000000f2d16ced46683a164d4897c40b0b74da12a01a15810398713f81b800037d954a400013d0fc89b000063420c5540c09d80005ed5047b40000017c8bf88b817cbed27099cb318848c87fd4c98090e93653705a16f97693f13a8f2853d01c2858046580000006780004b0000000000d74000000094d6c2486ed43c00000041c55cb78f80e2432810cc3184c1290ec7d032c0000001880bc2cc5941710d556d7051853e1698e1d2347c0b3cc51880164b2c0000dd9408086b0528cd000194436800000150d5bc0000000000000013e40248cc000fc4b444f8001259854e00a3ca58ecc73cf94c44571238d1106808d9b96704c13c00000003ec5480018141783c1934fc0f600d05693b88989982957b4884000ad17190a42d9054b6c315898360ef46819ed770c889007190b10195dc7dc5202900013f448d9f920d984000da8000730a68fa97cce5cc40a74dd01d93d92657dc23d25cf654a49d4e54ce18e88555f10149915580000
  | 11 => 0xb8857d7ed0ad8a824051d4b0eac2288055c8684330f4931066c8c1994b7d6c8c180016b046d734754e30a88efd5f40012bd3fd378f7c8901e919967cce46e825c3205c0de0735374250599890d7cad48ad244220fb0144a9d5cca780a414c001384451334218de4ff0000bf00000009a8000000add93c00000112d404000f88ca8cacb5800151c0d8cb19758ecae973c49994ccfc7596e84e14e154005d484261794000d70a2d8886f14281309f91610480006b8308b058c9021231315290fa57113548149ac600b240016a4000cc8a0cd4c5853bcc34ba80000015fcbb00016e4304ccc00000054c00016d26c2014d527c0146e188d609508000001535150e710fc00104c000f19089a014e82c83c483968ceb07a40743c929534ca80638604b197784049e00805b8534c4911c0013456ed29d15c001318f1d4c06448650640008d08b4cbd544bdcbc000000111843583084193011175530555113063000161c0010dc001568fbcec19bc27d468e3c00070153cf8c5fc85cc90a44300729028f24161158d241852d48457256d800112082c0004d80003a40000705c90743f8b9449c0006d17d40001090e11c00a0380c399700008d860d1cc87579989c00097
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x2041f7558c219020fbb4a610c81075da5308640c4aca908432068563484219038329a4210c818694e6008640c34a6b0043206a1215802190306a9ac4298818554d6114c40932e7306a4204357118d521021ab88ca99081265ce60d444085ae431aa22042d72195311020e39aca90881265cc6048440c52a43024220631511812110312b2a4210881a158d2108440d4242b00422049870588434c24c382c221a61469d46010d30b12e4300869859171180434c2a2b88a499261515c8514c530c34ca21e809851a75d8c404c28d3a8c620261625c86310130b22e2318809849873588404c24c3b26420261a25893210130930e6b088098498764c4404c348b0a62202618398d6215030c4ac5308a81861663584540c313312c22a061895896115030c52c5300a81863161980540c21ab88caa10610b5c86550430a1ae42a6601851571153300c294b90a9180614c5c4548c03083cec2a2601850d72151300c28ab88a8980610e9d8544c030a52e42a2601853171151300c28d3a6ca98061269db544c030a34e92a2601854972151300c2a8b88a898061269d8544c030b12e42a2601859171151300c28d3b0a898061869d8544c030e14e42a2601851972151300c384b90a898061425c8544c030e24e22a2601851971151300c388b88a898061445c4544c030a30e8a92601851875509300c384a928498061461d1514c030a30eaa0a601871151505300c20e39acaa0e418658e60d5220a32e7300a91062962980548821ab88ca21c41079ce65d0620a30ea21a61104357119443482163aac421a41515cc5148520a30ea21a60905897210d3048270b88c4982410e9c26395020a34e1b24a61051a70d91530821cbacc1218418654e6090c20952e530486105327090e5108298382c8a88414c9c24354420c32a630282104a9721814108318a88c0a0841079cf659002083aeb31c801041f7694e400820fbb2a7200418598e5190020c2cc6a8c8010625625464008306a9ac420041895895110020b14e72024010721519012008384a9a8490041c85095148020838e6b2a85885457314921c430cb1cc1aa421465ce6015210c62c3300a90842d72194438420f39ccba1421079ce6550a10a30ea21a610841e73980544421d380cb21a210b5c86510d10868eab08868854573149214428c3a88698221645c4434c1109c2e430a608866065485204421d384c72a021469c36494c10a34e1b22a60843975982430430ca9cc1218212c5c66090c10a54e121ca40852870591520429538486a90210e5d46050810c32a63028408629521814204258b88c0a1021079cf659001083aeb31c800841f7694e400420fbb2a7200218398e5290010c1cc6a94800862552586400430aa9ac220021895496110010b24e72022008721529011004388a9a8288021c85494144010
  | 1 => 0x5090f14b10c5284874c9c46294243a62e2314a121d1a731865090e95390c3284874a5c86194243c62c230ca121c3a76d495090e1d3b6a2a84870d5c4605484385ae4302a221e29625405010f18b0aa028087465c25310f42c30a6b0486a143a7098f5150a0f39cc1a8a858698d60d5332a32e1318a99960e6358854cca1cbacc121865629c2434c832a64e121ca21951473591510ca92b9486a88654c9c24354432a4ae421aa219705424c9510cb8321a64a8865469cf6494032a34e7b22a01943a7690d500ca94b9086a8065c25093254032a32e129887a0c3a70d9732d070c29ac121a830e9c263d494183ce7306a4a0c38705963250686b90a6192838514d610c941c30a6b0064a0e1a6358354cc68cb84c62a6638598d6115331874e132e8598c3870595428c61cbacc1218634a9c24394831a18e6b22a418d257190d520c69538486a9063495c4435483192ae231a8418e0c63549420c782a928298863649c2434c431e0c86a926218d1a73d92500c68d39ec8a80630e9da4354031a62e221aa018d1873509500c788a0a62a80630e9c2639532183ce7304a990c3a70d9643c861d384c72a443079ce6095221874e1b2c8710c3a7098e544860f39cc12a2438618f6055121c36c6302a890e1863181544861c382c9a9a430e9c36590d21870e0b288690d197014c434870629ac421a438514d6110d219c2e030a6490c1c735954148670b80c498a43071cd64d4121874e131ca810c1e73982540868d386c9298430e9c36454c21a34e1b22a610c3a70d96430861cbacc1218438694e6090c21c32a73048610f0553d052108782a9a8290843c154f4248421e0aa6a124210d25759912108693baac890843611cd6448421b40e0b224210d6170d4d21086a2baca690843c19515348421e0aa8a9a4210f077454d21087823a2a690843c19915348421e0ac8a9a4210d257590d2108782a9c8690843689c24348421a4aea21a4210f055310d21087a0a9a4328043469cf6494021874ed21ca010c1e73d9150087912a242a8043c85512154021e84a690aa010f4153485500868d39ec8a80430e9da4354021e468290aa010f21414855008791a1242a8043c85092154021e44e890aa010f21744855008791b2242a8043c81912154021e448690aa010f20434855008706b10c529c81459c46294e40a2ae2314a72051a7018a5390287390c329c81435c86194e40c2ac230ca72051a701865390287390c129c81435c86094e40a2ce2304a72051571182539030ca9cc1a9481075da5314a40c2ca7308a520616535845290286b94a6194818594e610ca40c2ca6b08652061a53580329030ca9cc1a8c81075da5314640c1ca7310a32060e53588519028ab8ca618c818394e620c640c1ca6b10632061a53580319020f39ccb90c81079ce658864083ce732843
  | 2 => 0x250ca070130003d0ac0000000024003613f098563f8902800012c000010e2f05a03c00334c02c4001c8003d45b1311a454694b47e1145c0007f4c08c19c2351c793e4a4134005506c000103f48d001403c11636c470006d2d11b0013e450000e8fa00095000f40000050800188d30008309c5031d340007154800038d20fc123bd092b0d53dc5d245242fc000011f000004203e0005232c0017800558005240039400000004740000000000000b8dc0000a1cc000000011800000ea000893b52f020e93112300088000de4ecc20000c4301905c0049c5354c4f014000004e2c0d00808f000d9258540006e40c650002c3e037210870042d0015018ce30f132180d61e01a1001f4852b1214f144442889c128af4a48e018150bcae388353c8b9154da320b8265203b944011282f54b4883810897545113fd0f4b09249821415190d0fc0e48a528b32000d0ec00345253ac85190e12f90415cdf260822d5134f5453ec6f124c9198ce284a50a1460d800000030741826c1100030398b72a07b428314a8b2478ec000ad0010b275011d86a305315347a090f14e0004600000043000000a402000000000035c0017c00409550000006c00000334d53c0000030c0044000538000000b000161d0aa001373cc612e89e000d4000dd001362a4581d5125307d521174e414318a7078cf000e747143418e424c0022c0009422000ab2ece8105074e8e027c0020486000001a06b28d2e314a63307c400000002a505331dc00000001c09a00007000f6000002d83200000164004340b000e80c000081086030c04014050c0d00000018001a000581000000100c1a4b0682c020e0000038340080004500000844030302c62070001030000100c0601048000a0000000622001800160c2589454090080804040000000000200c7600000100e000080c0e000280800000004806160202002040480014050580c020106d327114a5090e98b88a5284874a9c85194243a52e428ca121d2a7218e5090e94b90c7284874c9c46394243a62e231ca121d1a7318a
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x1a000e150f1716133d001000353e282a2f02093f23313c250a0021372714300b2d22391f1c203b2e12050300003a240419010711000c000d3326001e0000002c293436061b38322b181d00000800400d14080810c04010480c0024400d060070a80c21625c46294243c21725846194243a098098d6215332909859c2434c832b028090d3254432a058214d610c941a098214d600c941a118098d6115331a058118d5250831911859c2434c431b028090d524c431911811cd4254031a098014d6210d21a118014d6110d21b0280dd15348421904875915348421b00805915348421921859c24348421d01539c24348421a20865d12154021b00835d12154021b0283d912154021a228690d2154021c05625c46294e40c05725846194e40a058294d610ca40a098294d600ca40a058194d620c640a118194d600c640a078558d2108640a058694d2108640e02534856008640c09735486048440c11735446048440891811c16210d30889821c16110d30891811cd6210130891811d93210130889821cd6110130889821d93110130d01729c4544c030d02725c4544c030d01725c4544c030911811d5424c030909821d5414c030c097358a6015220911811d4434c220911811d4434c120908855c8434c120c09535ca6090c20921829c24354420c09535c86050420c21725446050420909859ce4048020d02735464048020c11735866015210909821d4434c210909821d4434c110910855c4434c110c11535c66090c10921819c24354810c11535c46050810c21525c46050810911859ce4044010d027354a4044010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1044
  | 4 => 1671
  | 3 => 343
  | 2 => 65
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
  | 5 => packedAt s4K5 (32016+((h/348+packedAt s4K5 (28188+(h % 348)*11) 11) % 1666)*12) 12
  | 4 => packedAt s4K4 (69625+((h/557+packedAt s4K4 (63498+(h % 557)*11) 11) % 2006)*12) 12
  | 3 => packedAt s4K3 (17833+((h/114+packedAt s4K3 (16807+(h % 114)*9) 9) % 453)*10) 10
  | 2 => packedAt s4K2 (4047+((h/21+packedAt s4K2 (3900+(h % 21)*7) 7) % 79)*8) 8
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf0fe3ffc1e3c7c7e3c78fc7f1c3871fe1cf90f
  | 1 => 0xff1fc3ffe03fff8fc07f1f8fe03ffe1e6331f3
  | 2 => 0x1ffc3fffc07ff1ff801ff1ffc07fe183ce3c
  | 3 => 0xffe0003fffff8001ffffe001ffff8001fc0fc0
  | 5 => 0xffffffc000000001fffffffe00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x16028884444898800c182413048910cc0c5905
  | 1 => 0x20441008809020104021088420122410212052
  | 2 => 0x8880111080140029080112049004900828228
  | 3 => 0x42012aa250200925254a400192a50045540d80
  | 5 => 0x8cd1b3039d3a7249fa749e4803060d99fbf000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfee8fee8fce8fce8fee8fee8fce8fce8fee8fee8fce8fce8fee8fee8fce8fce8fee8fee8fce8fce8fee8fee8fce8fce8fee8fee8fce8fce8fee8fee8fce8fce8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36288
namespace PEqualNP.Outside.L_meta_36288
open PEqualNP.Outside.L_meta_36288.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x2800015002e9450e3cb55860a451005805000007ce19046d20f4cbcb1812490a352006ae161c4130000e954e40a1a06100001818424a08804b0020c0000067ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x3c001704800078009830288488e2f431902e87051e0d642248a80221081a43471000ec00003f800de48339740000039b09434000146a45001f000683ca086c430692cae000014800760d800285f17000b06a0004c6e7e00000e404399f4c4312085902001d19900262988c4e831298400023d178ca54018010a3d1c0a412003a0441800058a0ee4e318183870278c8f61d3016c4055168e47e19371004444160008c0e001685618000f86600368203c1f2b054b250421d49a010003130b00021d111500000008000104030200110800000705010001141a0f0500000d080003072100020403bd28487795090e7aa3a14f943429eaa485af5250a7ea2a14f141429f2a0853e548ca7aa9194f950329eaa06576510caeaa2195e94032bca80653d52d067ca1a0cf552419fa9283b75150678a0a0cf950419f2a4633d548c67ca818cf55031b7290636d520c6f4a018de540319f2a6433d54c867ca910cf552219f2a2433d54486bea690d714d219f2a0433d54086bca610d754c21f2908437a50086f2a010d794e40aea9c819e539033aa7204f54a409ea8c813e50902bca6205754c40b7290816d52102eca2205d54440cf298819d531035ca4204f54840d6a90812d521036ca2204f54440daa888135511027ca0206e940409f2a6613d54cc33ca9986755330cfa16619d42cc33e83986750730cf206619c40cc2baa7186e102309faa2613c544c370809867d5130ce2a2619f424c33a849867d0530cea0a61db504c3b680986790130ce20261d8404c33080985794c309f2a6413d54c835a85904fd52209e2a4415e53882baa710764c2209faa2413c544835a8490764c1209f2a0413d54082bca6105754c20bb2884175510827ca9884f55310daa0e213f5484278a9085794e10aea9c21d9308427ea8884f15110daa0a21d9304427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x3800ba41c012af52013005600280001800040018003400e8c06640270000002003448b00608120000995505108054c4f2d2c005221e8c42e221cf80021161b000000480001c70230004810a480868d5845050a2d62141418e18154486596014d21d154d21087612154021c394d521030d5354840c954a51103165354440c554d51103265254440c954951102996394040a358840cc2956110330aa588408c2b16110230aa588404c2b16110130a6181424c2986050530a6993504c21e6590130a6982404c21e6510130a3588404c2956110130b2588404c2d16110130a6994404c31a6510130e2988404c2996210130e2588404c2896210130e4984404c2996110130e4584404c29161101308d5845488318544c2208b1954248318544c120e2509304822d6215210c615130842346550510c61513044391414c110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x20a0801800629c049245c46050930912e4302829868162984404c341312c220261a05896110130a22e22a26110508755093048284b90a898421441d5414c110
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
  | 4 => packedAt s5K4 (4032+((h/45+packedAt s5K4 (3672+(h % 45)*8) 8) % 164)*9) 9
  | 3 => packedAt s5K3 (2012+((h/16+packedAt s5K3 (1900+(h % 16)*7) 7) % 73)*7) 7
  | 2 => packedAt s5K2 (453+((h/3+packedAt s5K2 (441+(h % 3)*4) 4) % 12)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1e3f9fffc1c71e3f1c71f1ffe3870e3f0cf90f
  | 1 => 0x1fc7e1e3fe07ffc7e07e3e383c07ffc73341f3
  | 2 => 0xe007fe03fff81ff8ff803fc03ff80ff8c38e3c
  | 3 => 0xfff80003ffffe000ffffc0003ffff000fc0fc0
  | 4 => 0xfffffffc00000000ffffffffc0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x428084404408244004104048a0912212041905
  | 1 => 0x84110804881208082022121104024484114052
  | 2 => 0x1220089108050014880248209200920428228
  | 3 => 0x488055522504049295548004b254a012ac0d80
  | 4 => 0x9134598039a69924fa6939270060c1a4fbe000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeeafce8feeafce8feeafce8feeafce8feeafce8feeafce8feeafce8feeafce8feeafce8feeafce8feeafce8feeafce8feeafce8feeafce8feeafce8feeafce8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36288
namespace PEqualNP.Outside.L_meta_36288
open PEqualNP.Outside.L_meta_36288.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x24719000c6244e816804478a1d00bd906005892b34fd4000441f2e4cdc505582079778e4f8474000a3683439b4a84a9100f40335401b0000d401c76000290001c0b6000000624c01811000800104040821400b800004a03122890001ffd5007fe5401ff55007fc54027fd4c05fe53007f54c05fc5301ffd0c05fe4301ff50c05fc4300ffd48037f5200ff94803fd5200df54803fc5200ffd0803bf4200ff90803fd4200ef50803fc4200ffcc803fe3200ff4c803fc32027fd4401fe51007f54409fc5101ffd0407fe4101ff50407fc41017fcc401fe31007f4c405fc3100ffc8403fe2100ff48403fc21027fd4001fe50007f54009fc5001ffd0007fe4001ff50007fc40017fcc001fe30007f4c005fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a200eff19510025f8ca880037c65440093e32a200dffd911006dfec888003bf64440015fb22200dff9911001dfcc888037fd644401b7eb22200dff1911001df8c888037bc64440075e322200dffd511006ffca888037fd544401bfe2a22000ffd8d10005fec688033fe63440057f31a2000ff58d10005fac688033fc63440057e31a200effd4d10067fca688003fd5344019fe29a200dffd0d10067fc8688037fd4344019fe21a200bffd891005dfec48802ffe62440037f312200bff5891005dfac48802ffc62440037e312200bffd491005efea48802ffe5244017fea92200bdf5491005ff8a48802fff4244017dfa12200bff9091005ffa848802fbd4244017fe212200bffcc91005ffc648802ffd3244017fe192200effd451002ffca288003fd514400bfe28a200dffd051002ffc8288037f6414401bfea0a200dfd5051002ff88288033ff314400bff18a2000ff4c51002ff8628802fff214400bff10a200bfd8851005ffa428802ff5214400bfe10a200effd4110037fca088003fd504400dfe282200dffd0110037fc8088037fd404400dfe202200cffcc110037fc6088003fa3044001fe9822000fe4c110037f8608802fff204400dff102200bfe8811005ffa408802ff9204400dfe1022005ffc411002ff6208801bfe104400dfb0822006ffd9410035feca0801bfe65040097f3282006df99410024fcca0801bfd65040017eb282006df59410004faca0801bfc650400d7e3282006ffd9010035fec80801bfe64040077f3202006ef9901001d7cc80801bfd64040137eb202006ef590100057ac80801bfc640400d7e3202009ffd501004ffca808027fd5404013fe2a02006ffd8c10035fec60801bfe63040057f3182006f798c10015bcc60801bfd63040017eb182006f758c10005bac60801bfc630400d7e318200affd4c10047fca608003fd5304011fe2982009ffd0c10047fc8608027fd4304011fe2182006ffd8810035fec40801bfe62040037f3102006fb9881000ddcc40801bfd620400f7eb102006fb58810005dac40801bfc620400d7e3102007ffd481003efea40801ffe520400ffea902007df5481003ff8a40801fff420400fdfa102007ff9081003ffa840801fbd420400ffe2102007ffcc81003ffc640801ffd320400ffe1902005bf9841002ffea208017fe510400bfea882005ff1441002ffe8208017fe410400bfea082005ff1041002ffe6208017fe310400bfe9882005ff0c41002ffe4208017fe210400bfe9082005ff08410035fcc00801bff500400dff2802006ff54010037f8a00801bff400400dff2002006ff50010037f8800801bff300400dff1802006ff4c010037f8600801bff200400dff1002006ff48010037f8400801bff100400dfb8802006ff84010037f4200801bfd100400dfa8802005fe44010
  | 1 => 0x3ff404c00dff2026018ff50130037f8809800bff304c005fd9826006ff8c130037bc609801bfc304c00dee1826002fe0c1300bffe409801bfe204c02ffd1026017ff481300bff2409801bfc204c00bffb2e2005bfd971002ffccb88012fe65c400bfeb2e2000bf5971002ff8cb88016fc65c400bffb262005bfd931002ffcc98800efe64c400bfeb262015bf5931002ff8c988016fc64c402bffaa62015ff953100affaa988057fc54c400bffb1e2005bfd8f1002ffcc78800afe63c400bfeb1e2000bf58f1002ff8c788016fc63c402dffa9e2014ff94f10007faa788053fc53c402bffa1e2014ff90f100affa8788053fc43c400bffb162005bfd8b1002ffcc588006fe62c400bfeb162013bf58b1002ff8c588016fc62c4027ffa962013dfd4b1009ffca58804ffd52c4027bea962013ff14b1009ffe858804fbf42c4027ff2162013ff50b1009f7a858804ffc42c4027ff9962013ff8cb1009ffa658804ffc32c400bffa8e2005ff9471002ffaa388017fc51c400bffa0e2005ff9071002fec8388017fd41c402bfaa0e2005ff1071002ffe6388017fe31c400bfe98e2005ff0c71002ffe4388017fe21c400bfb10e2005ff4871009fea4388017fc21c402dffa862006ff94310007faa18801bfc50c402bffa062006ff903100affa818801bfc40c4029ff9862006ff8c310007fa618801bfc30c4027ff9062006ff8831009ffa418801bfc20c400dffb2c2006bfd9610037fccb08012fe658400dfeb2c2000bf59610037f8cb0801afc658400dffb242006bfd9210037fcc90800efe648400dfeb242011bf59210037f8c90801afc6484023ffaa42011ff9521008ffaa908047fc548400dffb1c2006bfd8e10037fcc70800afe638400dfeb1c2000bf58e10037f8c70801afc6384025ffa9c2010ff94e10007faa708043fc5384023ffa1c2010ff90e1008ffa8708043fc438400dffb142006bfd8a10037fcc508006fe628400dfeb14200fbf58a10037f8c50801afc628401fffa94200fdfd4a1007ffca50803ffd528401fbea94200fff14a1007ffe850803fbf428401fff214200fff50a1007f7a850803ffc428401fff994200fff8ca1007ffa650803ffc32840177eb0c2012ffd461002ffca308003fd518400bfe28c2011ffd061002ffc8308047fd418400bfe20c2010ffcc61002ffc6308003fd318400bfe18c200fffc861002ffc430803ffd218400bfe10c2006bf98210037fea10801bfe508400dfea842006ff14210037fe810801bfe408400dfea042006ff10210037fe610801bfe308400dfd1842006ff4c210007f2610801bfc308400dff9042006ff88210037f4410801bfd208401ffc9042006ff08210037fe210801bf7108400bfd8842000ffd9510005feca880037f65440013fb2a200eff99510025fcca88003fd65440017eb
  | 2 => 0x50027fca2a8013fd5154001bea8aa004ff145500fffe82a807ffe415403ffea0aa01fff105500f7fe62a8003fe3154001fe98aa01eff0c5500effe42a8077fe215403bfe90aa01dff08550025fec0a8013ff5054009fda82a006ff94150036fca0a801bfc505400dbe282a004fe141500fffe80a801bfe405403ffea02a006ff101500f7fe60a801bfc305403bff902a006ff881500effa40a801bfc205400dffb2c6006bfd9630037fccb18012fe658c00dbf32c60049f99630037facb18002fd658c00dbeb2c60009f59630037f8cb1801afc658c00dffb246006bfd9230037fcc91800efe648c00dfeb24601bbf59230037f8c91801afc648c037ffaa4601bff952300dffaa91806ffc548c0057eb1c6002ffd4e30017fca71800bfd538c005fe29c6002ffd0e30017fc871800bfd438c005fe21c6006ffd8a30035fec51801bfe628c0037f3146006ff58a300d5fac51801bfc628c00d7e314601affd4a300d6fea51806bfe528c035fea94601adf54a300d7f8a51806bff428c035dfa14601aff90a300d7fa851806bbd428c035fe2146002ffcca30017fc651800bfd328c005fe1946006ffd8630037fcc318016fe618c00dfeb0c6000bf58630037f8c318073ff518c001ff28c6000ff546300e7f8a31806fff418c037ff20c601bff506300dff8831800bff318c005ff18c6002ff4c630017f8631806bff218c035ff10c601aff486300d7f8431801afe608c00dffa846006ff94230037faa11801bfc508c00dffa046006ff90230037fa811801bfc408c00dff9846006f7cc230017f6611801bfc308c00dfc1846006ffc8230037fc411801bfa208c00dfe904601afe48230037f84118003ff654c0017fb2a6019ff99530025fcca98003fd654c0017eb2a6019ff19530025f8ca98063ff644c0317fb226018ff9913001dfcc898063fd644c0317eb226018ff1913001df8c898063ff544c031ff2a26018ff551300c7f8a89801aff634c005ffa9a6019f7d4d30017fca69800bfd534c005fe29a6002f714d30017fe869800bfe434c005ef21a6002ff50d300c7ba869800bfc434c02fffb126017bfd89300bffcc498006fe624c02ffeb126017bf589300bff8c498006fc624c02fffa926017dfd49300bffca49805ffd524c02fbea926017ff149300bffe849805fbf424c02fff2126017ff509300bf7a849805ffc424c005ff9926002f7cc930017fc649800bfd324c02fee9926002ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298016fc614c033ffa8a6000ff94530007faa298067fc514c031ffa0a6018ff905300c7fa8298063fc414c005ff98a6002f7cc530017fc629800bfd314c001ee98a6002ff0c5300bffe429805ffe214c02ffe90a6017ff08530015fec098067ff504c00dff2826000ff54130037f8a09806
  | 3 => 0xe2926223ffd093111f7e849888ffe424c447fea126223ef5093111ff8849880bff324c405ef9926202ff8c931017fa649888fdd324c405fe1926202bfd853112ffea298817fe514c401fea8a6205ff14531127fe8298817fe414c449fea0a6205ff10531017fe629880bf7314c40bff18a6205f78c53102ff86298817dc314c405fa18a6223ffc853102ffc429888ff6214c447fe90a6223fd4853102ff84298803ff604c4017fb026200ff98131007fac098803fc604c40d7e3026225ffd413112ff8a098893ff404c449ff2026224ff50131127f8809880bff304c405ef9826202ff0c13111ffe409888ffe204c447fe9026223ff08131025facb2801bff649400d7fb24a006ff9925001dfcc92801bfd64940457eb24a006ff19250035f8c928013ff5494009ff2a4a022df95250027faa928013fc5494009be2a4a006ffd8e50037fcc72800afe639400def31ca002b798e50037fac728002fd639400deeb1ca000b758e50037f8c72801afc6394009ffa9ca004dfd4e50027fca728013fd5394001bea9ca004ff14e50117fe8728087fe4394045fea1ca021ff10e50037fec52801aff629400dff314a001bf98a50037fac528082fd629400dfe314a006bf18a50027fea5280137f5294009ff294a004ff54a50106faa528013fc5294041ffa14a020efd0a50107fc8528083fd4294041dea14a020ff10a50107fe6528083fe3294041fe994a020ff0ca50037fec32801bfe619400b7f30ca006ff58650005fac32801bfc6194009ffa8ca004ff94650006fca328013fd5194009fe28ca004df14650117fe832808bfe4194045fea0ca022ff1065010ffe6328003fe3194001fe98ca021ff0c650107fe4328083fe2194041fe90ca020ff08650035fcc12801bff509400dbfa84a004fed4250037f8a12801bf8509400dffa04a006ff90250037fa812801bfc409400dff984a006ff0c250037fe412801bfe209400dfe904a006ff08250035fecaa807fff645403f7fb22a000efd91500057ec8a807ffe64540077f322a01fff591500fdfac8a807ffc64540077e322a01fef1915001d78c8a8013ff5454009bfaa2a004ff95150027faa8a807f7d5454009fe2a2a000ffd8d50005fec6a807bfe63540057f31aa000ff58d500f7f8c6a800afc6354009ffa9aa004ff94d500f6fca6a8013fd5354009fe29aa004df14d500fffe86a807bfe435403ffea1aa01eff10d500effec4a8076ff625403bff312a001bf989500effac4a8076fd625403bfe312a001bf18950027fea4a80137f5254009ff292a004ff549500eefaa4a8013fc525403bffa12a01defd09500effc84a8077fd425403bdea12a01dff109500effe64a8077fe325403bfe992a01dff0c950007fec2a8002ff6154001ff30aa000ff58550007f8c2a8016fc6154009ffa8aa004dfd45
  | 4 => 0x813ff5454409ff2a2a22bdf95151027faa8a8813fc5454409be2a2a200ffd8d51005fec6a88abfe63544057f31aa200ff58d51157f8c6a880afc6354409ffa9aa204dfd4d51027fca6a8813fd5354401bea9aa204ff14d5115ffe86a88abfe4354457fea1aa22aff10d5114ffec4a88a6ff6254453ff312a201bf9895114ffac4a88a6fd6254453fe312a201bf18951027fea4a88137f5254409ff292a204ff5495114efaa4a8813fc5254453ffa12a229efd095114ffc84a88a7fd4254453dea12a229ff1095114ffe64a88a7fe3254453fe992a229ff0c951025fec2a8813ff5154409fba8aa205ff9455102efca2a8817fc515440bbe28aa204fd1455115ffe82a8817fe4154457fea0aa205ff10551157fe62a8817fc3154453ff90aa205ff8855114ffa42a8817fc2154401ffb02a200bfd8151007fcc0a8803fd6054401fe302a206bf18151027fea0a88137f5054409fe282a22bffd015115ffc80a88affd4054457fe202a22affcc151157f860a88a7ff2054453ff102a229ff4815114ff840a8817ff658c40b7fb2c6205ff99631025fccb18817fd658c4017eb2c6205ff1963102df8cb18817ff648c40b7fb246205ff9923101dfcc918817fd648c44f7eb246205ff1923102df8c91889fff548c44fff2a46227ff5523113ff8a91880afd638c405ffa9c6202ff94e31017faa71880bfc538c405ffa1c6202ff90e31017fa871880bfc438c40bffb146205bfd8a3102ffcc518806fe628c40bfeb146226bf58a3102ff8c518816fc628c44dffa946226dfd4a31137fca51889bfd528c44dbea946226ff14a31137fe851889bbf428c44dff2146226ff50a311377a851889bfc428c405ff9946202ff8ca31017fa651880bfc328c40b7f30c6205ffd463102ffca318817fd518c40bfe28c6205ffd063102ffc8318817fd418c40bfe20c6205ffcc63102fbe631880bf7318c40bfe18c6205fd0c63102ffe4318817fe218c40bfb10c6205ff48631137ea4318817fc218c40bffb046205ff98231035fcc118817fd608c4017eb046205ff18231147fea1188a3fc508c44fffa046227ff9023113ffa811889ffc408c405ff9846202ff0c231137fe411889bfe208c44dfe9046226ff08231007feca98802ff654c401bfb2a62009fd953112ffcca98812fe654c401feb2a6200bf5953112ff8ca98812fc654c401be32a62049f19531127fec898892ff644c449ff3226203bf99131127fac898892fd644c449fe3226203bf19131127fea898893fe544c449feaa26224ff1513102dfec69880bff534c405ff29a6202ff54d31017f8a69880bff434c405ff21a6202ff50d31017f8869888fff624c4477fb126223ff9893100dfcc49888ffd624c4477eb126223ff1893100df8c49888fff524c447bfa926223ff9493111ffaa49888f7d524c447f
  | 5 => 0xe000060000120000000000c028000090060100380500209c020000100040000002c00c000000000041100001200001807010070018020021fc0600001405c030050000280301100201c0480700001c028010300040001101c004000000180040b01400c02c0287d0020000000700000406801038004030400160040100000002403801015fecaa98c3ff6454c617fb22a630ff9915301dfcc8a98c3fd6454c617eb22a630ff1915301df8c8a9813ff5454c09bfaa2a604ff95153027faa8a98c37d5454c09fe2a2a602bfd8d53017fea6a9813df5354c05ff29aa602df94d53017f8a6a980b7c5354c05ee29aa602ffd0d53017fc86a980bfd4354c05fe21aa62fffd895317dfec4a98bffe6254c037f312a62fff5895317dfac4a98bffc6254c037e312a604ffd4953026fea4a9813fe5254c09fea92a62fdf54953027f8a4a98bfff4254c5fdfa12a62fff9095317ffa84a98bfbd4254c5ffe212a602ffcc953017fc64a980bfd3254c05fe192a600ffd8553005fec2a9803fe6154c01feb0aa600ff1855302df8c2a9813ff5154c09bfa8aa604ff14553187fe82a98c3fe4154c61fea0aa630ff10553017fe62a980bfc3154c5fff90aa62fff8855317ffa42a98bffc2154c01ffb02a600bfd8153007fcc0a9803fd6054c01fe302a606bf18153027fea0a9813fc5054c09be282a630ffd0153187fc80a98c3fd4054c61fe202a602ffcc153017f860a98bfff2054c5fff102a62fff4815317ff840a9812fd659440bffb24a205bfd925102ffcc92880efe649440bdf324a203af9925102ffac9288bafd649440bdeb24a200af5925102ff8c928816fc6494409ffaa4a204dfd5251027fca928813fd549445dbeaa4a204ff1525102ffec728817fe63944057f31ca205ff58e51005fac728817fc639440b7e31ca204ffd4e51027fca7288b77e5394409fea9ca204ff14e51026f8a7288bbff439445bff21ca22eff50e5116ff88728817ff629440b7fb14a205ff98a5100dfcc528817fd62944597eb14a205ff18a5102df8c528813ff5294409bfa94a204ff94a51027faa5288b37d5294409fe294a22cffd0a511677e85288b3fe4294459fea14a22cef50a51167f885288b3ff3294459ff194a22cff4ca51167f86528816fe619440bffa8ca205dfd4651027eea328817fc519440bfa28ca205ffd065102ffc8328817fd419440bfe20ca205ffcc65102ff86328817ff219440bff10ca205ff4865102ff84328817ff609440bff304a206bf9825102ffac128802fd609440bfe304a204ffd4251027f8a1288137c509445dffa04a22eff90251177fa81288bbfc409445bff984a22dff0c251167fe41288b3fe2094459fe904a22cff0825102dfecaa88afff64544577fb22a22bff9915101dfcc8a88affd64544577eb22a22bff1915101df8c8a8
  | 6 => 0x10000000ab00008100000005c14838f48a1903a11cf45c13c42e1810df48b0680ae3692885104632f509244a3763a34480294310004f90b12403ef5031033e22ef1c914410d4394193e90341640350002d137712b2db34812200009901020a3404ba00704200017330d1e024d26b4150f73303aa29a4a31b63c71f61d106d2d73b41f31b93f906b25f0804c10aa0511f835d3681a114947949d0610ff29226426f42d17026d1080c135418921537b13d11c0003fb0000000003880004053fe49146500042301e11d4de0002862091500004cf4902783b84a61450003c504a18c14d2c93242b92a434a31c2010fa2bc0120001234713b64782bd3250d600000000048d1bf0764d84e00b50b91d74ae48e4ce00031833a3571e70c015d44410a00000043c2fb01a0231b53634453f82e21e42fc3794b64f117521c4ff3f32d003721a00000010437a23e19500021403847441f08533e4f309f0004cc4d64204a43172850154b737c2f811425143819f2f108d3261cb1d60e20693eb1c310c2f91281830f63c30e441d2ed44c09417103f1e30022a532d3af0f325d08f09d06c39c36518544902529023b2ec50c3e306e4c73ce49206205217647c4134855052bb1b33e64e548947d4124fa35f3bc01f0004fe41e00046449900029c29e3a60004b24bd00001134900013837100022b0004af46102f0000000003670000b82b021914b2a20004b82222610273850000472040000002694c80002f605745434604313419740a22327406f11800e0ce0f000000a000008000000500240781c0000100081a0120240080e00c0500081d0000000980300600c09805036000018060a201000005012010100020220180100a0020000100701401c02800004028028040000000980205806c0400f020020098000940000001201000400004002000020060240c43600d00a02c028000020280482000a05c0000a01c000000020680000000000c054018040040100402b00000c0003b00002c1782000000c0000f0020100100800c00c0300201a000000090940040d80902002400803004014010060000400500e02a0080000304200401802000014068710000180000e002000010080180c80100100601c000040000ec0180509a008048100000100680201a000008050000040100100a0000080901a0680c03b02601c0281200a0080d00100000800004000004078050080040000700400c0b01a00801c070000220280101a0140000180002002c0880a0000000702101c004020000020300000000c008088040040000b00103c018010060040a00000d000008008010380000380000202000808010000000040360000200400e0180180000000800023006000098030020040080000200000800000068008000020300880801a0000280800602005001000008000040
  | 7 => 0x2300000000000463593da4593872ac00000000027d00016322a0000490002760000004b42371e13f20091fe3421d400028049500000000023c0003822461051d53bd3050000d13020eb17427500000030013f3ae5133e14d204d1132d40c84c532b07a4dc0a215400016d4250000001880002e01294c612000003b28e2d94471511dd2c340327139907735a0f247539b07f2733943ee0b42be11050948406000000019431b4f50001e20000c30000003f650a27f0000000003600202840004b03ca09825525c4551980000000003d50003a40004e14ca19e1820003700003d602e49a3ab28a0d84ec12c29321e4810000ed3142f01ac4ed0004c22ae0001840000000004bb3dd2af0002352e70934964b538617814f20041612102b28336c49f26a2d21c804800000d2391150892fe49e17b0c53df50233840945f3b700000033640c22c4370004f708a0003e700032e2950000f138926e26c2961112280cc4d72c53040da00a1f50751660282332d815f34304b11635604f45230f4862273ad28f0004c42b22e30a104e35c2123105110ac1ab1da03c06329813a05d2dc3724241774b12a60860302e63950ad42f3c437f3ba1b20004302ba0000790000dc34f40629927e3d80004ef3ff19c4f01eb3d94d04820001bb00000000000005500029b23100027b2f21320c700000039e2114084870010ea3014584462ff00000000000036e32132232a02c08e0be1ed22503147b0e709518d1861372260003c600035e0000d00b32562b61ea3732e52cc44113b41c1c40002411a80000004423f00003fa25e4db45d4330880002913c02591b031a4d33fc4a937d15230323a2aa2174aa2b42f716c2ee1bc3f13133c909c0d710f3121ec3d03413960080b00911333c82ad3e44140af0e90e02024e705000640f3ac41b46a4d916138d3e00004324fb05a0b20ee0e54da1d84c308b20e0003a915c09a29f2eb00000000000028b4361e54fd1460644c015a16a38000033f1e62b11b82fa4802f30734a105e1aa1a70003373f40003f500022f20c00036b09e0004f23ed19a0560002a934521600050809646020d39f1fc0000003a00000672424f40004cd00046e0c202a2d63a20000000000002fd00030a0004dd3d700b3440001014172501c72583d42e40d900017f0a70db31e1fa04116812e42a0f820b1a54eb23f0a02e10bb42214743e0870002b84d12c80f92621593dc1ba4ee3192684070000002c10b637e45708413946b0000002534733bb1c51871724042d34663c24c925b3de1961cd33438b4672c21c233518a1e92181e84d53d334b14c10e18e0cf35b00029727c0003b001c2454691194a21931a32440cb4ac45000000011a0130f50000000004514ad4ea0e84cb0001bd00000012f0003974a530e26648f28d00032707447f01429428900031
  | 8 => 0x34d0001f20a54ab2e907131d1fd11b09b00048c2d52bf2ea13000041a2033313083b22c02da2722791d343b2483e51063db32927040108c23d50e21f38e33219d05b3c143d40b1b71001d03200ba0d41dc0172134e62490d506a4d42de3cf44d0c92a742800044e0000bd14246c16f4b30ef00013550407d0000400004401c600003337500043500c11739d25414e06520633c1c10364113780002632c70003cc3b34763390004721311d21a90001241ce4e31c02e848845b4fc2a33ea22d1654f60000003580000000000004b90000e100036100000011e20825a0212a801b50f3fd0e32f43e83a74be0fc00000000012600022124b24c50000023800035031637412d3b92775010971603090440700320584df41814307c44b34e26747e00000032c00000003d0722290a61563d12324291a63b51252050f41cc3062072c64e80de2ca10b1be0002cb2b300031f1574970000b70000004a03f700019940e46d1d91de03943f3901f40e619b0a30bc3cd1f92241791ae32300045333d11f1020044261ff45a3831b12df04516e04c38a0830000cd0fe4621a417e4e400015323417a0000d23d235100024e3be0660bf4930531090002650fd14a07e21044336d2874e90002a150b40234722e43a00f27a0003664a700000002630b0003920000900003280000c44340000004703a50d322024338129d0054f80a84bc0000000002b747a01d14023625741015b46f42b0001a218b3bf1923550001623ec08220f00301921d00050600030700050718f0000001ca2cf3640003531ad0243151ef1070184561df5120a433b03e2b51550000000000000000000fb00030c1693331804bf39828c42700012700000003a39a0002822602811121910a905f50d13615e3913b125200012a42c15849417c1db32f1f73cb0004770000c64e20000ec00017d0001413a840d4682dd13e0002ce00049b0002cd1b41672471ee07b3622ab21b2a03524984830224211fb4a81af00024a05449c16b0dd2c440034c00036a1f001636f0ca1a01f107824f02d05938c45e44f384393
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf7258c1000cfe7258c10004fd7258c1000cfc7258c100067f5258c100067d5258c10006bf4258c10006bd4258c10046df3258c10006de3258c10006dd3258c10046dc3258c1002cff7158c1002cfe7158c1002cfd7158c1002cfc7158c1002ede3158c1002edc3158c10034ff7058c10034fe7058c10034fd7058c10034fc7058c10036de3058c10036dc3058c10036fa1058c1002ef91058c10006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c100065f5258c10006de5258c10006dd5258c100065d5258c10006dc5258c10006df4258c100069f4258c10006de4258c10006dd4258c100069d4258c10006dc4258c1002edf7158c1002ede7158c1002edd7158c1002edc7158c1002edf5158c1002ede5158c1002edd5158c1002edc5158c1002edf4158c1002ede4158c1002edd4158c1002edc4158c1002edf2158c1002ede2158c1002edd2158c1002edc2158c10036df7058c10036de7058c10036dd7058c10036dc7058c10036df5058c10036de5058c10036dd5058c10036dc5058c10036df4058c10036de4058c10036dd4058c10036dc4058c10036df2058c10036de2058c10036dd2058c10036dc2058c10036df1058c10036de1058c10036da1058c10036dd1058c1002ed91058c10036dc1058c10004ff7654c10034fe7654c10004fd7654c10034fc7654c100267e6554c100067d6554c10186be6454c10006bd6454c10016de6354c10006dd6354c1017eee6254c10006ef7558810006ee75588100066e7558810006ed75588100066d7558810006ec7558810006ef7458810006ee7458810006ae7458810006ed7458810006ad7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec435881002eef715881002eee715881002eed715881002eec715881002eef515881002eee515881002eed515881002eec515881002eef415881002eee415881002eed415881002eec415881002eef315881002eee315881002eed315881002eec3158810036ef7058810036ee7058810036ed7058810036ec7058810036ef5058810036ee5058810036ed5058810036ec5058810036ef4058810036ee4058810036ed4058810036ec4058810036ef3058810036ee3058810036ed3058810036ec3058810036ef1058810036e71058810036ee1058810036ea1058810036ed1058810036e5105881002ee91058810036ec1058810
  | 1 => 0x94100567f53594100067e53594100567c5359410004ff725941000cfe7259410004fd725941000cfc72594100567f52594100067e52594100067d52594100567c5259410006bf4259410006bd425941002cff715941002cfe715941002cfd715941002cfc715941002e7e515941002e7c5159410034ff7059410034fe7059410034fd7059410034fc70594100367e50594100367c50594100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100047f72594100067e72594100067d72594100047d72594100067c72594100067f42594100063f42594100067e42594100067d42594100063d42594100067c42594100067f32594100067e32594100067d32594100067c325941002e7f715941002e7e715941002e7d715941002e7c715941002e7f415941002e7e415941002e7d415941002e7c415941002e7f315941002e7e315941002e7d315941002e7c315941002e7f215941002e7e215941002e7d215941002e7c21594100367f70594100367e70594100367d70594100367c70594100367f40594100367e40594100367d40594100367c40594100367f30594100367e30594100367d30594100367c30594100367f20594100367e20594100367d20594100367c20594100367f10594100367e10594100367d10594100367c1059410006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bc5359010006bf7259010004bf7259010006be7259010006bd7259010004bd7259010006bc7259010006bf52590100063f5259010006be5259010006bd52590100063d5259010006bc5259010006bf3259010006be3259010006bd3259010006bc325901002ebf715901002ebe715901002ebd715901002ebc715901002ebf515901002ebe515901002ebd515901002ebc515901002ebf315901002ebe315901002ebd315901002ebc315901002ebf215901002ebe215901002ebd215901002ebc2159010036bf7059010036be7059010036bd7059010036bc7059010036bf5059010036be5059010036bd5059010036bc5059010036bf3059010036be3059010036bd3059010036bc3059010036bf2059010036be2059010036bd2059010036bc2059010036bf1059010036b71059010036be1059010036bd1059010036b51059010036bc1059010004ff7558c10024fe7558c10024fc7558c10004ff7458c1001cfe7458c10004fd7458c1001cfc7458c10034ff7358c10036df7358c10006df5358c10046de5358c10046dc5358c10006df4358c10046de4358c10006dd4358c10046dc4358c10004f
  | 2 => 0x5ef7258d1005dec7258d10004ff7558d100067f7558d100047f7558d10024fe7558d10024fc7558d100067c7558d100247c7558d10004ff7458d10006bf7458d10004bf7458d1001cfe7458d10004fd7458d1001cfc7458d10006bc7458d1001cbc7458d10064ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d10004fd7258d1000cfc7258d10006ec7258d1000cec7258d100067f5258d100067d5258d10006bf4258d10006bd4258d10066df3258d10006dd3258d10084ff7158d10006f77158d10006f62158d10006f52158d100a4ff7058d10006fb7058d10006fa2058d10006f92058d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d100267c6554d10006bf6454d10186bc6454d10034fc76545100067f65545100267c6554510006bf645451015ebc6454510005fb7054510035f8705451002ff01054510034fc764c5100057f754c5100757c754c5100067f654c51012e7c654c510006bf644c510126bc644c510006df634c510016dc634c510005fb704c510035f8704c510024ff7654110074fd765411002cfc76541100067f65541100267c6554110005bf745411006dbc7454110006bf64541100febc6454110005f7715411002df47154110037f01054110005fa768c110036fa768c1100377a758c11003779758c1100077b658c11000778658c110007bb648c1101b7b8648c110065f9738c110016fa638c110016f8638c110035fb728c1101bdf9728c1101aefb628c1101aef9628c1101af7b528c1101af79528c1101afbb428c1101afb9428c11002dfa718c110035f8718c110036fb618c110037f3618c1101b7f2418c1101b7f1418c1101aff2218c1101aff1218c110014ff764c110064fd764c11002cfc764c1100067f654c1100ce7c654c110006bf644c1100c6bc644c110006df634c110016dc634c110005f7714c11002df4714c110037d8304c11002df8764c110016f8764c11002cf8764c1100077b654c11000778654c110007bb644c110197b8644c110035fb734c110037db734c110007db634c110016fa634c110016f8634c110067d8634c1101a7db534c110067d8534c110067da434c110197d9434c11019dfb724c11019df9724c11018efb624c11018ef9624c11018f7b524c11018f79524c11018fbb424c11018fb9424c110067db324c11018fd9324c110007f3714c11002dfa714c11002df8714c110007f0714c110036fb614c110037f3614c110197f2414c110197f1414c110067db314c110007d9314c11018ff2214c11018ff1214c110034ff75594100367f7559410004ff745941001cfe7459410004fd745941001cfc74594100567f54594100067e54594100067d54594100567c5459410004ff7359410014fe7359410014fc735
  | 3 => 0xf4259510006bd4259510094ff7159510006f771595100b4ff7059510006fb70595100057e76195100767e76195100047e76195100067f64195100067e64195100067d64195100067c64195100073c64195100063c64195100067e63195100067c63195100757f72195100057d72195100067f62195100067e62195100067d62195100067c62195100073f42195100073d42195101de7f61195100077641195100077541195100077621195100077521195101d67f60195100077a20195100077920195101d77b10195101df7610195101df7410195101d778101951006dbe76d911006ebe76d911001cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d9110005bf72d9110005bd72d9110006bf62d9110006be62d9110006bd62d9110006bc62d91100073f52d91100073d52d91101c7b771d911006fb471d9110007b621d9110007b521d9110007ba20d9110007b920d91101cfbb10d91101c7b610d91101c7b410d91101cfb810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bc53d9110006bf72d9110004bf72d9110006be72d9110006bd72d9110004bd72d9110006bc72d9110006bf52d91100063f52d9110006be52d9110006bd52d91100063d52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d91101c6bf71d91101cebe71d911006ebd71d91101cebc71d9110006bf51d91101cebe51d91101cebc51d9110006bf31d91101cebe31d91101cebc31d9110006bf21d91101cebe21d9110006bd21d91101cebc21d91101cebf70d91101c6be70d911006ebd70d91101c6bc70d9110006bf50d91101c6be50d91101c6bc50d9110006bf30d91101c6be30d91101c6bc30d9110006bf20d91101c6be20d9110006bd20d91101c6bc20d91101cebf10d91101c6be10d911006ebd10d91101c6bc10d9110014fe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10066de63d8d10024fe75d8d10004fd75d8d10024fc75d8d10004ff74d8d1001cfe74d8d10004fd74d8d1001cfc74d8d10004ff72d8d1000cfe72d8d10004fd72d8d1000cfc72d8d100067f52d8d100067d52d8d10006bf42d8d10006bd42d8d10006de32d8d10066dc32d8d1002cfe71d8d10034fd71d8d1002cfc71d8d10066df31d8d10006f621d8d10006f521d8d10034fe70d8d1002cfd70d8d10034fc70d8d10066df30d8d10006fa20d8d10006f920d8d100057f7558d100757c7558d100067f6558d100067c6558d10005bf7458d1006dbc7458d10006bf6458d10006bc6458d10066dc6358d10
  | 4 => 0xc210037db734c210037db634c210016fa634c210036f8634c210037d8634c21020fdb534c210087d8534c210087da434c210207d9434c2101fdfb724c2101fdf9724c210036fb624c2101f6f9624c2101f77b524c2101f779524c2101f7bb424c2101f7b9424c210087db324c2101f7d9324c21002dfa714c21002df8714c210087db314c210007d9314c210024fe76d95100767e65d9510006bc64d9510004ff74d951001cfe74d9510004fd74d951001cfc74d95100767f54d95100067e54d95100067d54d95100767c54d9510014fe73d9510004fd73d9510014fc73d95100767f53d95100067e53d95100767c53d9510004ff72d951000cfe72d9510004fd72d951000cfc72d95100767f52d95100067e52d95100067d52d95100767c52d9510006bf42d9510006bd42d951002cfe71d9510034fd71d951002cfc71d95100767f51d9510034fe70d951002cfd70d9510034fc70d95100767f50d95100757e76d95100247e76d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100067e63d95100067c63d95100057f72d95100057d72d95100067f62d95100067e62d95100067d62d95100067c62d95100073f42d95100073d42d95100077641d95100077541d95100077621d95100077521d95100077a20d95100077920d95101ef7b10d95101e77610d95101e77410d95101ef7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100047f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067f42d95100063f42d95100067e42d95100067d42d95100063d42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95101e67f71d95101ee7e71d95100067d71d95101ee7c71d95100067f41d95101ee7e41d95100067d41d95101ee7c41d95100067f31d95101ee7e31d95101ee7c31d95100067f21d95101ee7e21d95100067d21d95101ee7c21d95101ee7f70d95101e67e70d95100067d70d95101e67c70d95100067f40d95101e67e40d95100067d40d95101e67c40d95100067f30d95101e67e30d95101e67c30d95100067f20d95101e67e20d95100067d20d95101e67c20d95101ee7f10d95101e67e10d95101e67c10d95100767c6559510005bf745951006dbc7459510006bc6459510074ff75595100067f7559510004ff7459510006bf7459510004bf745951001cfe7459510004fd745951001cfc7459510006bc745951001cbc7459510004ff7359510014fe7359510014fc7359510004ff725951000cfe7259510004fd725951000cfc72595100767f52595100067d5259510006b
  | 5 => 0x35de704c530035dc704c530007d8704c530016df604c530017db604c53021fda204c53021fd9204c530024ff7654130014fe76541300f4fd7654130014fc76541300067f65541300267c6554130005bf74541300c5bc7454130005df7354130015dc73541300f75c5354130037d8305413002e7f7559710004ff745971001cfe7459710004fd745971001cfc74597100067e54597100b67c5459710004ff7359710014fe7359710014fc73597100b67f5359710004ff725971000cfe7259710004fd725971000cfc72597100b67f52597100067d5259710006bf4259710006bd4259710034fc715971002e7e515971002e7c51597100b67f5059710004ff7558f100067f7558f100047f7558f10024fe7558f10024fc7558f100067c7558f100247c7558f10004ff7458f1001cfe7458f10004fd7458f1001cfc7458f1002edf7358f10004ff7258f1000cfe7258f10004fd7258f1000cfc7258f100067f5258f100067d5258f10006bf4258f10006bd4258f100a6df3258f10006dd3258f10034fc7158f1002ede3158f1002edc3158f1002ef62158f10006f52158f100a6df3058f1002efa1058f1002ef91058f10004ff7654f1002cfe7654f10004fd7654f1002cfc7654f100267e6554f100067d6554f10024ff765431002cfc76543100267e65543100067d6554310005bf74543100adbc7454310005f7715431002df47154310014ff764c31002cfc764c310016de634c310006dd634c310005f7714c31002df4714c3100367f7559610004ff7459610006bf7459610004bf745961001cfe7459610004fd745961001cfc7459610006bc745961001cbc74596100967f54596100067d5459610004ff7359610014fe7359610014fc73596100067e53596100967c5359610004ff725961000cfe7259610004fd725961000cfc72596100967f52596100067d5259610006bf4259610006bd42596100967f5159610034fc70596100367e50596100367c5059610004ff7558e10024fe7558e10024fc7558e10004ff7458e1001cfe7458e10004fd7458e1001cfc7458e10036df7358e10006df5358e10086dc5358e10086de4358e10006dd4358e10004ff7258e1000cfe7258e10004fd7258e1000cfc7258e100067f5258e100067d5258e10006bf4258e10006bd4258e10086df3258e10006dd3258e10086df3158e10034fc7058e10036de3058e10036dc3058e10036fa2058e10006f92058e10004ff7654e10034fe7654e10004fd7654e10034fc7654e102167f6554e100267c6554e10024ff7654610034fc76546100267e65546100067d6554610005fb7054610035f87054610014ff764c610034fc764c6100057f754c6100957c754c610016de634c610006dd634c61002fd4314c610005fb704c610035f8704c610035fb764c210046fb764
  | 6 => 0xd76946300267e65946300067d65946300ddbe7494630005bd7494630035fa7094630005f97094630004ff7654630004fd7654630034fc76546300267e65546300067d6554630024fe76d95300ce7e65d9530015de73d9530035dd73d95300cf5f53d9530004ff74d953001cfe74d9530004fd74d953001cfc74d95300067e54d95300ce7c54d9530034ff73d9530014fe73d9530034fd73d95300cedd73d9530034dd73d9530014fc73d953010e7f53d95300cedf53d953010e7d53d953010edc53d9530004ff72d953000cfe72d9530004fd72d953000cfc72d95300ce7f52d95300067d52d9530006bf42d9530006bd42d953002cfe71d9530004fd71d95300ce7c51d9530014fd70d95300ce7f50d95300ce7c6559530005bf74595300c5bc74595300f75c5359530235fb705953010cff75595300067f7559530004ff7459530006bf7459530004bf745953001cfe7459530004fd745953001cfc7459530006bc745953001cbc74595300ce7f54595300067d54595300f4ff7359530006df73595300cedf53595300f67e53595300f67c53595300f6dc5359530004ff725953000cfe7259530004fd725953000cfc72595300ce7f52595300067d5259530006bf4259530006bd4259530004ff715953002cfc71595300ce7f5159530234ff7059530006fb70595302167e50595302167c5059530024fe75d8530004fd75d8530024fc75d8530004ff74d853001cfe74d8530004fd74d853001cfc74d8530034fd73d8530004ff72d853000cfe72d8530004fd72d853000cfc72d85300067f52d85300067d52d8530006bf42d8530006bd42d8530086df32d8530006dd32d8530086f631d8530086f531d8530034fe70d8530034fc70d8530006fa20d8530006f920d8530006f76198530065f970985300057f75585300cd7c7558530005bf74585300c5bc7458530005ef72585300bdec72585300a5fb70585300cd7e75185300057d75185300c5be7418530005bd74185300bdee7218530005ed721853002ef66118530006f56118530004fe7694530004fd769453002cfc76945300067f65945300267c65945300c5be7494530005bd7494530015de7394530005dd739453016f5c5394530035fa7094530005f97094530004ff7654530004fe7654530004fc76545300267e65545300067d6554530005df7354530015dc73545300cf5f5354530034dc764c5300075f754c5300cdde754c5300cddc754c5300075c754c5300cd5c754c53022ddf744c53022ddd744c530225df724c530225dd724c53021edf624c53021edd624c53021f5f524c53021f5d524c53021f9f424c53021f9d424c530015df714c530017d7714c530007d7614c53002ede614c53002edc614c530007d4614c53002ed4614c53021fd6214c53021fd5214c530007db704c530
  | 7 => 0x8550006f561185500347c76545502557f74545502557d74545500073f645455015e7e645455015e7c645455024f3c645455015e3c64545500f57e73545500f57c73545500067f63545502457f72545502457d725455023e7f625455023e7d625455023f3f425455023f3d42545500257f715455002777715455000777615455002e7e615455002e7c61545500077461545500077b70545500357e70545500357c70545500077870545500267f60545500277b6054550004fe768c550004fd768c55002cfc768c5500257e758c5500057d758c550006bf648c55013ebc648c550004ff764c550004fe764c550004fc764c5500057f754c5500257c754c550006bf644c550126bc644c5500367f7559630004ff745963001cfe7459630004fd745963001cfc74596300e67f54596300067e54596300067d54596300e67c54596300f67f53596300f67d5359630004ff725963000cfe7259630004fd725963000cfc72596300e67f52596300067e52596300067d52596300e67c5259630006bf4259630006bd4259630004ff715963002cfc71596300e67f51596300e67c5159630034fe7059630034fc70596300367e50596300367c50596300067f74596300067e74596300067d74596300067c74596300f67f73596300f67e73596300f67d73596300f67c73596300f67f43596300f67e43596300f67d43596300f67c43596300067f72596300047f72596300067e72596300067d72596300047d72596300067c72596300067f42596300063f42596300067e42596300067d42596300063d42596300067c42596300f67f32596300f67e32596300f67d32596300f67c32596300067f71596300067e71596300067d71596300067c71596300067f41596300067e41596300067d41596300067c41596300f67f31596300f67e31596300f67d31596300f67c31596300067f21596300067e21596300067d21596300067c21596300367f70596300367e70596300367d70596300367c70596300367f40596300367e40596300367d40596300367c40596300367f30596300367e30596300367d30596300367c30596300367f20596300367e20596300367d20596300367c20596300367f10596300367e10596300367d10596300367c1059630004ff7558630024fe7558630024fc7558630004ff745863001cfe7458630004fd745863001cfc7458630004ff725863000cfe7258630004fd725863000cfc72586300067f52586300067d5258630006bf4258630006bd4258630036f77158630006f64158630006f54158630066f63158630066f53158630006f62158630006f52158630034ff7058630034fd7058630034fc7058630036df3058630036dd3058630036fa2058630006f92058630036f61058630036f4105863002cff7694630034fe7694630004f
  | 8 => 0x34fe768c650004fd768c6501ed7f758c6500257c758c650016de638c650006dd638c650004ff764c650004fd764c650034fc764c6500057f754c6500257c754c650016de634c650006dd634c6500fdbe76d91500febe76d915001cbe76d915026f3f75d91500ff3c75d9150006be63d9150006bc63d91500073e53d91502773c53d9150005bf72d9150005bd72d9150006bf62d9150006be62d9150006bd62d9150006bc62d91502773f52d91500073d52d91502773f51d9150277bb50d915026f3e50d915026f3c50d9150277b850d915026ebf75d91500febe75d91500febd75d91500febc75d9150006bf73d9150006be73d9150006bd73d9150006bc73d9150276bf53d9150276be53d9150276bd53d9150276bc53d9150006bf72d9150004bf72d9150006be72d9150006bd72d9150004bd72d9150006bc72d9150276bf52d91502763f52d9150276be52d9150276bd52d91500063d52d9150276bc52d9150006bf32d9150006be32d9150006bd32d9150006bc32d9150006bf71d9150006be71d9150006bd71d9150006bc71d9150276bf51d9150276be51d9150276bd51d9150276bc51d9150006bf31d9150006bc31d9150006bf21d9150006be21d9150006bd21d9150006bc21d9150276bf70d915026ebe70d91500febd70d915026ebc70d9150276bf50d915026ebe50d91500febd50d915026ebc50d9150006bf30d915026ebe30d915026ebc30d9150006bf20d915026ebe20d9150006bd20d915026ebc20d915026ebe10d915026ebc10d9150014fe76d8d500257e75d8d50006bf64d8d50006bc64d8d500f6de63d8d500f75e53d8d50034fd75d8d500347d75d8d50014fc75d8d50004ff74d8d5001cfe74d8d50004fd74d8d5001cfc74d8d500e67f54d8d500067d54d8d500f67e53d8d500f6de53d8d500e6dd53d8d500f67c53d8d50004ff72d8d5000cfe72d8d50004fd72d8d5000cfc72d8d500e67f52d8d500067d52d8d50006bf42d8d50006bd42d8d5002cfe71d8d50004fd71d8d500e67f51d8d50024fd70d8d502667e50d8d502667c50d8d500f6df30d8d50005bf7458d500fdbc7458d50006bf6458d50006bc6458d500f6dc6358d500f75c5358d5025dfb7058d50006bf64d8550006bc64d8550034fd75d8550004ff74d855001cfe74d8550004fd74d855001cfc74d8550014fe73d8550004fd73d8550014fc73d8550004ff72d855000cfe72d8550004fd72d855000cfc72d85500967f52d85500067d52d8550006bf42d8550006bd42d8550096f651d8550096f551d85501e67f65985500fdbe7498550005bd7498550006bf6498550006bc6498550006f76198550075f97098550005bf74585500fdbc7458550006bf6458550006bc64585500b5fb70585501de7f6518550006bf6418550006bc641855002ef6611
  | 9 => 0xf7258e5000cfe7258e50004fd7258e5000cfc7258e500ce7f5258e500067d5258e50006bf4258e50006bd4258e5010edf3258e50006de3258e50006dd3258e5010edc3258e50004ff7158e5002cfc7158e5010edf3158e5010edc3158e50034fe7058e50034fc7058e50036de3058e50036dc3058e500cede7558e500cedd7558e5010edc7558e50006df7458e50006de7458e50006dd7458e50006dc7458e500cedf5458e500cede5458e500cedd5458e500cedc5458e50006df7258e50006de7258e50006dd7258e50006dc7258e500cedf5258e500ce5f5258e500cede5258e500cedd5258e500065d5258e500cedc5258e50006df4258e500069f4258e50006de4258e50006dd4258e500069d4258e50006dc4258e50006df7158e50006de7158e50006dd7158e50006dc7158e500cedf5158e500cede5158e500cedd5158e500cedc5158e50006df4158e50006de4158e50006dd4158e50006dc4158e50006df2158e50006de2158e50006dd2158e50006dc2158e50036df7058e50036de7058e50036dc7058e50036df5058e50036de5058e50036dd5058e50036dc5058e50036df4058e50036de4058e50036dd4058e50036dc4058e50036df2058e50036de2058e50036dd2058e50036dc2058e50036df1058e50036de1058e50036dd1058e50036dc1058e502157f7654e500167f7654e500147f7654e501157e7454e501157c7454e502167f6454e502a67d6454e500257f7354e500275f7354e500167e6354e502175e6354e500165e6354e502175d6354e500167c6354e5029d7f7254e5029d7d7254e502167f6254e502967d6254e502973f4254e502973d4254e501ed7c7154e502157f7054e500077b7054e50217787054e500267e6054e500277a6054e50004ff745865001cfe7458650004fd745865001cfc74586500067e54586500767c5458650004ff7358650014fe7358650014fc73586500767f53586500067d5358650004ff725865000cfe7258650004fd725865000cfc72586500767f52586500067d5258650006bf4258650006bd4258650036f77158650076f65158650076f551586501ee7c5158650006f64158650006f54158650006f62158650006f52158650034fc70586500367f50586500367d5058650036f61058650036f410586501157e74946501ef3e74946501153e74946501ef3d74946501ed7c74946501e67f649465028e7d64946500057d739465016e7e63946501e75e639465016e5e63946501e75d63946501e67c63946501ed7f72946502857d72946501e67f629465027e7d629465027f3f429465027f3d42946500257e71946500277671946501e67f61946501e77661946501ee7d61946501e77561946501e77a70946501e57d70946501ef7970946500267e60946500277a609465002cff768c650
  | 10 => 0x953116f5f30d95310067f74d95310067e74d95310067d74d95310067c74d95312c67f73d953116e7e73d953116e7d73d953116e7c73d953116e7f43d953116e7e43d953116e7d43d953116e7c43d95310067f72d95310047f72d95310067e72d95310067d72d95310047d72d95310067c72d95310067f42d95310063f42d95310067e42d95310067d42d95310063d42d95310067c42d953116e7f32d953116e7e32d953116e7d32d953116e7c32d953116e7f71d95312c67e71d953116e7d71d95312c67c71d95310067f41d95312c67e41d95310067d41d95312c67c41d953116e7f31d95312c67e31d95312c67c31d95310067f21d95312c67e21d95310067d21d95312c67c21d95310067f70d95310067e70d95310067d70d95310067c70d95310067f40d95310067e40d95310067d40d95310067c40d953116e7f30d953116e7e30d953116e7d30d953116e7c30d95310067f20d95310067e20d95310067d20d95310067c20d95312c67f10d95312c67c10d953112e7c65595312bdf7715953116cff75595310067f7559531004ff745953101cfe7459531004fd745953101cfc7459531154ff7359531006df7359531004ff725953100cfe7259531004fd725953100cfc725953112e7f52595310067d5259531006bf4259531006bd42595312bcff7159531006f77159531004ff7059531034fc705953116d7e761953112e7e761953116c7e76195310067f64195310067e64195310067d64195310067c64195312b67f631953112d7f72195310057d72195310067f62195310067e62195310067d62195310067c62195310073f42195310073d42195312af5f32195310075d32195312ae7f61195312af7731195312b75e31195312b75c31195312af7431195310077621195310077521195312af5f3019531024ff7654531014fe7654531154fd7654531014fc76545310067f65545310267c6554531005df7354531015dc735453102fd431545310067f65d81310067c65d8131024fe75d8131004fd75d8131024fc75d8131004ff74d813101cfe74d8131004fd74d813101cfc74d813102cfd73d8131004ff72d813100cfe72d8131004fd72d813100cfc72d81310067f52d81310067d52d8131006bf42d8131006bd42d81310a6df32d8131006dd32d8131006f621d8131006f521d81310a6fa30d813112d7e75981310057d75981310067f65981310067c6598131006fb60981310057f755813112d7c75581310067f65581310067c6558131005bf7458131125bc7458131005ef725813111dec72581310067f65181310067c6518131036fa6018131006f96018131004ff7458e5001cfe7458e50004fd7458e5001cfc7458e50036df7358e5010ede5358e500cedd5358e50006df4358e5010ede4358e50006dd4358e5010edc4358e50004f
  | 11 => 0x6de32d8d51156dc32d8d51024fd71d8d51156df31d8d51034fe70d8d51004fd70d8d51156df30d8d51156dc6358d512e5f77158d5102d7c7654d510167c7654d5102c7c7654d5115d7e7454d5115d7c7454d512de7f6454d512de7d6454d510257f7354d510275f7354d510075f6354d510167e6354d510167c6354d511575c6354d512d57f7254d512d57d7254d512ce7f6254d512ce7d6254d512cf3f4254d512cf3d4254d51007777154d5102d7e7154d5102d7c7154d51007747154d510267f6154d51027776154d510057f7054d512167c6054d5102cfd75d8151004ff74d815101cfe74d8151004fd74d815101cfc74d8151014fe73d8151004fd73d8151014fc73d8151004ff72d815100cfe72d8151004fd72d815100cfc72d81510b67f52d81510067d52d8151006bf42d8151006bd42d81510b6fa50d8151155de7398151005dd7398151006fb6098151005bf745815115dbc74581511e67f6518151036fa6018151006f9601815102e7f7559631004ff745963101cfe7459631004fd745963101cfc74596310067e54596311467c54596311567f53596311567d5359631004ff725963100cfe7259631004fd725963100cfc72596311467f52596310067d5259631006bf4259631006bd425963102cfe715963102cfc715963102e7e515963102e7c5159631004ff7059631034fc70596311467f5059631004ff75582310067f75582310047f7558231024fe7558231024fc75582310067c75582310247c7558231004ff7458231006bf7458231004bf745823101cfe7458231004fd745823101cfc7458231006bc745823101cbc7458231004ff725823100cfe7258231004fd725823100cfc72582310067f52582310067d5258231006bf4258231006bd425823102cfc715823102edf315823102edd315823102ef62158231006f5215823102efb7058231066fa3058231006fa2058231006f9205823102efb105823102ef81058231024fe76d953112e7e65d9531004ff74d953101cfe74d9531004fd74d953101cfc74d953112e7f54d95310067e54d95310067d54d953112e7c54d953102cff73d953102cfd73d953116e7f53d953116e7d53d9531004ff72d953100cfe72d9531004fd72d953100cfc72d953112e7f52d95310067e52d95310067d52d953112e7c52d9531006bf42d9531006bd42d9531014fd71d953112e7f51d9531034fe70d9531004fd70d953112e7f50d953112e7c50d95312ad7e76d95310247e76d95310067f64d95310067e64d95310067d64d95310067c64d95310057f72d95310057d72d95310067f62d95310067e62d95310067d62d95310067c62d95310073f42d95310073d42d953116f5f32d95310075d32d953116f7731d95312c75e31d95312c75c31d953116f7431d95310077621d95310077521d
  | 12 => 0xd75d81532367d75d8153004ff74d815301cfe74d8153004fd74d815301cfc74d815325e7f54d81530067d54d8153024fd73d815325edf53d81532367e53d81532367c53d8153236dc53d8153004ff72d815300cfe72d8153004fd72d815300cfc72d815325e7f52d81530067d52d8153006bf42d8153006bd42d815302cfe71d8153004fd71d815325e7f51d815325efa50d81532167c50d8153236fa30d8153006fb6098153005bf7458153185bc7458153036fa6018153006f96018153176bf7559251176be75592512eebd7559251176bc7559251006bf7359251006be7359251006bd7359251006bc73592512eebf53592512eebe53592512eebd53592512eebc5359251006bf7259251004bf7259251006be7259251006bd7259251004bd7259251006bc72592512eebf52592512ee3f52592512eebe52592512eebd52592510063d52592512eebc5259251006bf3259251006be3259251006bd3259251006bc325925102ebf715925102ebe715925102ebd715925102ebc715925102ebf515925102ebe515925102ebd515925102ebc515925102ebf315925102ebe315925102ebd315925102ebc315925102ebf215925102ebe215925102ebd215925102ebc2159251006bf7059251006be7059251006bd7059251006bc70592512eebf50592512eebe50592512eebd50592512eebc5059251006bf3059251006bc3059251006bf2059251006be2059251006bd2059251006bc205925102ebf105925102ebe105925102ebd105925102ebc1059251004ff7458e5101cfe7458e51004fd7458e5101cfc7458e5112e7f5458e510067d5458e5102edf7358e5116e7e5358e5116ede5358e5112edd5358e5116e7c5358e51004ff7258e5100cfe7258e51004fd7258e5100cfc7258e5112e7f5258e510067d5258e51006bf4258e51006bd4258e5116edf3258e51006dd3258e5102cfe7158e5102cfc7158e5102e7f5158e5102e7d5158e5102ede3158e5102edc3158e51004ff7058e51034fc7058e5112e7c5058e5116edf3058e51004ff745825101cfe7458251004fd745825101cfc74582510767f54582510067d5458251004ff7358251014fe7358251014fc73582510067e53582510767c5358251004ff725825100cfe7258251004fd725825100cfc72582510767f52582510067d5258251006bf4258251006bd425825102cfc715825102e7f515825102e7d515825102efb7058251076fa50582511e67c5058251006fa2058251006f9205825102efb105825102ef81058251014fe76d8d51156de63d8d5102cfd75d8d51004ff74d8d5101cfe74d8d51004fd74d8d5101cfc74d8d51156de53d8d51146dd53d8d51004ff72d8d5100cfe72d8d51004fd72d8d5100cfc72d8d511467f52d8d510067d52d8d51006bf42d8d51006bd42d8d51
  | 13 => 0x300300000000500000001300700000000000400300000d00c00400100000000600400000100000200002000000000500000300400000800300000100000000300000200000000100100c00200200000300a00300500300100400000000a00100000200000000800100400000000100800400000200000000200000000200600001800300000100500101600b00001900000002f00100000100000100000000500000400000800000601000000000000000200100200f00000c00e00700401a00900500000500c00000300700c00200000200100000101200300000000100000100400200100700100600000000200000900400500200500000100300400000500000100000300300000100100000000100500100000200101000000200300900000d00900700000200000400100400000100500200000100100300000600100000000500300200000000000600300000000003000000100100f00100800100001a00500400700100000400100000200d00a00000000100400100200300900000000500200100f00200200000000000000000100000500400200400000100400200601700000200100e00e00000600300300300000c00f00000000000300900200a00300300400100000100200100001600000000500100100000400400800b00600300100400000200500300000000600500b01100200200000200600b00200900100100400000000000400300500400600000100500100a00700500003000600000000200100600700000000000000200f00200400600100200000200000200000000000600400300100700000500100500f00400000300300000000000100100b00000300200000200c00000600e00600300000600500f00100400000000400000100200700100400200400100000100000100000c00000000000100000200200100900a00000200a00100100200b00000200000100200100000100300100100d00400000600400000000200e00000300600800100501500200f01400000800000000100d00300100400100300200000300400000100000100100000000100300000200100500600400000301300200000000000000100300100000000000000000200100100600200600a00000000100000000c00100200000001600d00000600200300000000000800a00800000100000200500500300800300002cfe76d8553014fd75d8553004ff74d855301cfe74d8553004fd74d855301cfc74d8553024fd73d8553004ff72d855300cfe72d8553004fd72d855300cfc72d85532e67f52d85530067d52d8553006bf42d8553006bd42d85532e6f651d85532bef631d8553034fe70d8553004fd70d85532c67f6598553185be7498553005bd7498553006f761985532c67f651855302ef66118553006f56118553034fe76d8153014f
  | 14 => 0x6fe29992b886c000000000000085c2cc000000079800015a40007d10d3a2683ca7e50529fbcdd60000000b3c8e83bf046000007a7a10001c7c0000000251dd4ea8000063a1fc00000000000002860e826104e4748238000000000038c2c38000e2400000000000e6000000000000028b39522acf00000100800000006d00021b40000d200000000c20260771b6859a00044b0484000000196902c0002a3000000000015b000000000000002e0b8829e000000000092042e0001eb8b9800000004e87140000000000b801d02d700000000000000000000000000154c0002f2000000000000000000000002ee00014180005783fb88f800021e33b21b89b43640000000d4849702d18c10ea02e1ec00003ce71008305a415e0000a600009f000e3611d54ca686100012f8cf65801931728ee440d01810e40000003848000d4078700000000000000001d345bc5cd3479e582b211123b057117000018c00005d4000000072800076c0001618d9a8070000a6c9e44f606600005ac79b42611a83a848f36902f000009000011407a803345880007522bb0000000d9400035989f106a6a6000000000029a00000000000ea000113488e7f40a2130000039700007c8d300000ab0000d0a776036178ca1654126591b417e07d17c0608e8c7d200018f80f046926384b800048200022e90c82a92808eccd703c30339ed0d9e68d00019b4ac289c0c79aa517e02910496346a600042685248ea66a0000000000000000000000000012d80010ca16a0000f000008c23ce800000055c000158800017b000078800000008780004e2000000000000080818194080001c30000000584000000000000088500000000002d9000000000002a0bb91b02d0413000077ce1a00025d8634d82000393837c0003c528d18a00003930000000000000000204c2ca0aa18f16bc29a5d32c088410667261c400007c200000000011601ee24a8838000000000000000000000021a909c89100000007b60002f492e80008260f2181409e000039212c84680b1c200002ea668018800060c00004d02a400000000000200400300000300000100200000200100000000000200800200400200000000300100000200000000600001b00000000000001200000100000200100200200000200000100100500001000100000000100400201400600b00000000300400000200000000000000300100300000300000200400200301100100200200000000200000800600000400100100000100000800900200000000000000000000000000300200000300600200100701801000700100100200300000000001a00100000000200400400a00000600200600000000000300000900500600300200100000900600400200000600100000000b00200000f00300d00200000300200000100e00000
  | 15 => 0x895f049000000000000000003578f309ce3800060000f560002d0000000021d18122b0dce87d1d91e9036e7a900d89910bc04122c14eccd820a00000000007f504010d0b1200036f0e388620000fc80000000140000f807f2000000000039200042480000008122a3000000000000000000000001aa80011307b500000011860000000c108fe74b27e000000047100004d4c400003d60000000000000000000010529b00005a6000000000000054d000000102a272000000000055500022d000024c1768cc40000000002050000730027000085e0ed0000e0c95e0000000000c2400000009dc7ee00000000000006c4000000080400000000000000004408000000000000000000000025403bc848000160967cf866e826211b8000000000000117a83e000008885887920806b8f3400000000000000000000fe046e37f000084865c000278a2781384aa22113fc59c49b25b88d0c523613048854000133382948c32a0003f488a075061325888c01e84461378904ae80b242212445d66692ea21c406e000000000000000000000000000002cd0c486e23c9224884c56600000000000000002d6000023071400000005022500001460c5a3110001b24b623660001d4c00087700002c0e082e90000b940004d6000016c0005b815592103b47e3311190463200016000000000001a9148428e15700516303ae4b40000a1000007914909080000002ab16107160163571f789c20000000cac0002f107d1df000000000000000000f30001d64ab0035000000004a0003c687a8d6e0001d3224c0000a11de03c0c5e2f42961ff8ce007725a83280000000000e7800000039092e095a000000153117c5962fc9b500004b9397800000024b00000000000003db0e40ea00d800000000000000001c54b3a09b0fb983000000003f8ce40001dc0001fb8a848b51ba8bd40000002ad8228a7800000014904e80003df80006540000000000326000000122800000000000000000ac28a980093a5bb0000dc8000614000000000000000000000007a50fb000000082c22080000000000aa000000000026f87000001bb14300005f400022917a0c4e2313ad0698b8454f2eca1080005e6202004c00010d00000000001ec05686a50e42980d280080001082318ddc0000002a90b80fb6000000000000000008b8000a328461b780000000000000000000098313000081e0000000000e6825f3ce129cef421f2509d745cc00000017b01f20db00300000007e1320000000069639b80000007c714e2228d265a91b11d9c7c468b2e400000008b21f295241047c2452895907286739c851450a0e22499edc2a22ad3c10fd8bdc0000000f40000000000199800028d3020c345626612da20f075c37b31c00000000001ec98fcfba2b70b189c000045620d0288d382890c50b84
  | 16 => 0x8945202ee0cbcf8c10040c9a7d10c53a08998383d03d32470ee468886601a14f8a5c000000000000051e0000e6c3b03401d58000bae7484240e54b241b80000224b4a2ac24280b40000cf1a50000598000000138034814a0002038b2a0000000ab800046500000005b4000000000114018c0e880004dc1bf1b389ec32866500000000000000000000c981f005888ac45a67d3ab9d7c00000012380000004ef34b97bc6d2000000000000000008a0000000000000000000065d4551fb40bc0000000000f7666f00000000000003d001644b22220001b0c000847000058800000038d1b6445e0c203a121800019c23d18680008a900014c80000000001a0800000030a800000000022e8a81120130000000000000029382d400045743480000000000000000d6800043d00000002bc128871c7400000001f14000000315a1c00000000000ec053e4160001fe04640003839be0d36554134080867600000000009aa0000000b7c0007a80000d940006e0444800000000000007cc00004400008cc00000000496b445c000000000000078830880000007410000cd8000565000000032061813f94a444000017219150767632a39f68d565e713984a893c530000000020263d21e94290305db000000000035e00021d82c27a639e129842e04200020e000052b2c881bcad01ed21c193456c6ec2e90754b7a2a20521894f9013b3bf18d83a64c143012acea474211b1ebc11e1fb00002801507442d99e48bbe5032fb176861280c0001260a800cb1908b28000000000000064e00000002200000000000ef405683d3a280000000001f200003966ee3eb8db112841b1f986d4d4e81b3bf8cd000065e21d93a076c00016a80008321290000000000000000000000003a0001af403800000015a8b388100531dec00000000000000000b702398d400017e3c2229c4163ac3e61a2400000004a00ec0001243109c4c0fc729000060cd203fe06683442fa25a00000010000000001d9800009d000000000061600004d00002613ef821800006604a975864488c000187cdda000000000027a88b3192210b1642800009a400085a000177489e00032b00006480002878000d022ff00019540000003b11528c3a3de3ca89607e40000000000eb80002cd86248420000bf88110568370ac1f04d3a8af3b81c4400050724e000025a0000000000de200018d99f0000000408800000027600001246b257e251a1e0a121f100000007284920c310a4da67f137e0894b1e0001d1a08867a5f730e03b02207f90a0000000020f276067400042d2770000cce00018980000000000001ca082851f046a27c0008451940000f2e32c17d800000071e000000018c000000000086e02f00001800004dd0001ecc60a0000001da41f668c1f70d451360ba3038de49b079f0000f983ea000
  | 17 => 0xa1a300005a04262a80ae82f404b418a21c0646e207f00000a480432706e88ee0da278040c8146082028738f260000002200cb83be00000000006541e5963800045c03a800000057a000183473e40e4048c802ba2f93ee0000dca49a199a17cb0a2242a29ba8fac0000001ad800000036d9538d06407000116cde60b91a09a783721c60e900009f46a31b6a034ee228028e8d5c91a05f1b1935070e65f286041d06039a0af110c9ea4bd2ff16505a800029a00000000004218000cf44440080000ca43f432d8fbc23a2b93ff99809a023b004115116e8a127186cc10a00046200011484c823c00006d66cc0138ac000024f2d0800000000029684bcc7834e000000008a0000000000a96000000000041822917e1ef0a2c7f318b80000000000000ff000029001f8f1c00075e032996000000000000000000000c90000f7400000011cc08c0000000000ae666b0000000b2600000000000000000c58e640000000000c5896475b21013900002750000f0884e2451479e78aae0002289a68000000000130c7c60001c31e04030000451986c0008230a413f516c7c02e599d4cae817358800053c3df34a800074a7a7000114c00000020013b40001910000f5400000010c9f64fec7320b20000e041e128000007383c6000000000000015f000000000021e10a80004013e5170400012c22580a00000002129f98c9e000000000082e0000000000bea0000000000000000000000000038d000077400025c27d962083a77d3989b984fa0b821a8238f920de26e21282821a33d180006dc0621e795d4b060004600ee891800000000007b42bf44ba074ff60000000a5511000000005680000002d5800000000015412d80005fd00000040000001fd13440002f62d40000e7000000000007ea1bd00006b023480207080002702832d21c583f40000000054f9c5b61c79bec0000000000cdcd9058a0000000000623000000000078b00000005b633e0000000e1e00000000008bc000000000035400000009481d60002e280000003a144c98e40003a71f4047000000000013f826c87e24402b84801192ef1dac0004b03b41a381926343d51cf4dec5b735e1bc00005bf0001c749920000000eec7ce0000628ee000000027c85c07f685b38c83040000001a4800000072c034800009a0000b595ac00000006a19c85fc0000ec8000edc1762fc061c000543305848089006300215e400013e3f593d079000000011380007730001e4000016d0001db433e691072876c6b00000000518554000000119088a2bd42012a40000003078834ce20003630ca40004ca241800000088d0000000a1a5fc17b8000000806441080c3fa0000000000e5a000000000044213c00009ac00001206a91f44581250e086c800000005980010b000034522a0000104000090cc968ae000000
  | 18 => 0x50ba00000000008180000000000b6a28e16e0000000841049000c04600040e16f8c8429945e050839021c10d1ef50de00023e000000019936f81ad03e0003d68c68fa8000360133cd106a22b7042c000000000000000000031b80000000000000fb40000003c79f8800e00000000010f87cd0001a946200000000b8cab44060ff8001002000070152101e10925292fc51873313393480d404c2f11cfd0ae774297866cf14096073a2e43446cb01e17b48608a6284000000072b40f05480000000002154ce835a07c00000007b9069800000010e34c9b3890e494381a1444723d72698de83d286226717fc9160001029fe8a542d22d80ba013e66401c0b2498a0171038a1d0065a223d9f3c00a17c1e91e300002af1629498de48730d68d80a6222a244873cbe059033c000000030800000005ae2911e098b00000000001578da074312a9fb08de5373ea9bbcabe0000000edc788000000067864a1eb3310a50000694000052c4da05d26b846c83061e04215c48985bc43180008e435b00011540ec3073ab049cab200b0f000001263ca0000448f600002829c00e2e5ce1ff87e00aa26a0db127c2f031516c0358a501e32b68b440d00bb0000dc01ae5e53971d8004261035d11e4be208345d825c08682700000000000000000e4400000000000000000000000000c5400000008f40f61a014e80008ce1cc000000106457200000004d80000000000c7400000000000003ad00020280000000fa19cc7041793420e580000001ba00005e600033f90f8aa200036e80000002821ee0001048570000000013200024019b8000000000171800051419d07147e08c53b78638bc2184000000000000005e8000fc030c06e00000000002d300003fc00007e0000a720003248454eca00000015d854a85200000008d608b30b820400011600000003305a72d18cc015628805a0000e300241591494c9045a3c3118069800006000000005771fe800000000000001004ba0001c080000000003fe8b1835682a11d1aa89784ac0b78000a2400031d8000dfa04835a8000000599000000000062400000001cc55d00000002e419738da068dee27a1a680000006bf00000001864a414b90fc81270629116a827e6472f991c00a065913c80d823e8a207e9d84bf41e63198ae11240001a804dce380001ae8000000000127027818800002b000000000005f1e0c9d40000000e480000001878988b740000000000000000000000000057d00003fc03c7640000000db02ec00005b000057f000000000025400012cc000000000000083c0003f206f08cc00000000000000001130000e1000000000009d200028d80004ae2600000b9d0b20001498000e4067700000003420002ec032003a34320419683bc7471e8958105a2160000408000000000000000000043d8d58ac807
  | 19 => 0x3d1000000000025000007ac000000000049412b00020d80003b14280a9098c31f000000000000000013cc000000000000036234f3f400005e04991040fac1ba6e315a80000005c322fa0d080672331880f86d45eb0000000d0e8743a600000000000790f7463a0000d80d2c76a2c429c00000000000000850218000000000067e3aa42980006f85c921599280000000001d0023c53520e1f9c00000000001440e051c2b18000000000240a20ca202a61a400005fa16e0b89c390a84a200000005de84f3cc89989bc3f105b00000405e414b029c58e73a39f136c6fa816317081860000002a15101c64612bd8000d8a2783c715b083e88f41d003c56810a22ca0143f82493c88b2058600022022cccf28210389b58da20002870000f70000000000000060220a8cf00007cb03e00000003ce374854c0000e926c8758f62504185a158ace0a307a85cceb0000000000000070c02b8fb001a0003b5000000025e37a1d2400002c1da06002500000cb1be40000000000de000000036380e50d02cb0000da029c00002c089c1ee1b40299f100000000000000000181000230447849600000000000001a280000005cf21d0dcc000000122000031012637f848800074a29f9aa105c00018a057c0001cd3280000000000153a0946843760001ac0d64000300800000000000017100000000001b7000066327580000007f20000e74000566000145c0000000b380000c84f70e2007c86683f340000037c000000000000000000000009c40000000000e9e0000000d7c0000003030000ba00003e98d1cfe0185098800000000037d00004222a10001b540dc0000001a847d20001aa00002cc00033f17d00000001918f348d00004358000b725e00f79e5000089d4148c0400019a13f1088dae7be29e8000e765fb00000000006443e804c81c83ea000167848c47e0000000c061550001e144466863bb800075e0000001de0000000000208000000035f1d446fc31c2c122540000001c48e1400000000005800002633491754dea0000000000ade0003561828122000000000049a30e3bc8e880000001ae10c8c860002728cc80007362661744c320000d7800000000035c85400004e60000364000000000000105070b00c9ec84360003ec16c8fd46463288000e487fc00d1ab48240d04178cd42e828a00017c83841a81cc00000000002cb89944306e409180000000000001cd40000000000000000789000000000000011a80000000000000b744a600000000000000f64360000400000000000111c411289800115a4623911d38e140ce1850000bd400035d80000000f10001c9447e0000000000b8e0003709334a2208719c1c
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe2f82549640400187ee4a92c8080030f5c952590103271b882a4b202064e3510549640400117d0e292c8080022f61c52590103151f428a4b2020008be878c9640400117b0f192c8080028fa1632590100051ec2c64b2020008be870c9640400117b0e192c8080028fa1432590100051ec2864b202005ab6810c9640400156b02192c80801aaea0032590100055cc0064b20200087f855d163040090f90aba2c60801a37a1f5358c100346f43e86b1820068dc8750d63040014bf0aa1ac608002972154358c100346f43c64b182000a5e858c963040014bb0b192c608002a7a123258c100054ec2464b1820068dc874c9630400153d083aac608002a76107558c100052fc2ae8b182000a5c855d163040014bd0a3a2c608002976147458c100070faa4a8b182000a5e859c963040014bb0b392c608002a7a127258c100054ec24e4b182000a5e851c963040014bb0a392c608002a7a107258c100054ec20e4b182005ad6811c963040115ab02392c60801ab6a007258c100456cc00e4b182062e5a10d4963040cbcb221a92c608192976165258c100054f424a4b182000a9d849496304001c9f04a92c608193968415258c1031f2c882a4b182062a5e85149630400153d08292c608002a76105258c100070fa9684b182000e1d52d0963040bdd3421a12c608187a64434258c100052f42c84b182000a5d8590963040c153b09212c608003a3e094258c100070fa9284b182000e1d5250963040c1d1e40a12c608183a34814258c103074d08284b18205fe991050963040014bd0a212c608002976144258c102f54f42084b18200687c85dd9530400d1b907bb2a60801a1f21d6554c100346e43ac6a982000aae84dd5620400155b09baac4081929b61e755881031733884eab102062e6a109d562040c5cca213aac4081979a442755881000637c3aeab102064e67105d562040c9cd420baac40819399441755881031f34882eab102062a6e851d5620400155d083aac408002ab61075588100053742ee8b102000a6d85dd162040c155b0f3a2c4080038b9d6745881000716bace8b10205eea7109d162040bdd54213a2c40817ba9442745881030f54884e8b102000caf875d16204001c5ceaba2c4080038b5d5745881030657b82e8b102060cad705d162040c1d4e20ba2c408183aa841745881030752882e8b10205fea9105d162040014dd0a3a2c4080029b61474588102f557420e8b102000e2f5495162040014dd0bb9ac4080029b617735881000557426e6b102000aad84dcd62040014dd0a39ac4080029b614735881000557420e6b102000aad841cd620400b5cd0239ac40801eb9604735881003575400e6b102007ae9801cd620400155d0829ac408002ab610535881000537c2a86b102000a6c8550d62040014dd0a21ac4080029b6144358810
  | 1 => 0x90ea92c6880030fdd15258d103561e3a2a4b1a2000c6f7254963440038d8e4a92c6880022fa1f4258d1001c5e43e84b1a2000c3f75d0963440d3878eba12c6880032bdcb4258d1000e5639684b1a20008be8750963440011790ea12c6880030fdd54258d103461e3aa84b1a2000caf725096344003958e4a12c6880063721d3258d1000e6639264b1a2001ce47288563440031e90e90ac688007391c92158d100076299242b1a2001ce87288163440031f10e902c688003aa5092058d100077090a40b1a20038be84dd9534400117b09bb2a6880021fe157654d100045fc22eca9a20038bc845d953440011df04bb2a6880063b2097654d100243e428eca9a200287e87d9553440798f0e1b2aa2880ee1fa1b754c5100061e326ea98a205587e87d9531440790f90fb2a62880030fdd7644c5100061e3aec898a2000c3c74d95504407b8e8e3b2aa08819e2fa1b74541100061fb2ee8a82204ec3c65dd150440cd17d0fb22a0880e62f21f64541100071c320cb182203ce5830d95304400d1ed0db8a60880f71e1db654c1100072c31eca982203ac78761953044001c70c832a60880e72e1db644c110005d8c20e29822000be1821c5304400d3b10e98a6088017361d9314c1101a5ac42a629822005dd0714c5304400d0fd0f2a2ca080030fdd254594100343e43aa8b28200687e8794d65040030f90bb92ca080031bd4972594100343f43ca4b282000a3e84949650400147b09292ca0801a1f21d525941000637b92a4b282000c3f749d1650400147d0839aca080028f61073594100043fc3a86b28200087c8750d65040010fd0e21aca080021f61c43594103243ec3ce4b282000a3e849c9650400147b09392ca080031be0972594103143f438e4b282000a3e841c9650400147b08392ca080030fdcb42594100061eb9684b28200087e8790965040010fb0f212ca081828f612425941000717c1284b282000c3f72509650400187ae4a12ca081838bc8142594103071690284b28200087e8710965040010fb0e212ca0817a8fa1042594100043f43c64b28200087d878c9650400147d09192ca080028f61232594100043f43864b28200087d870c9650400147d08192ca080028f610325941002d3b40864b282000a75810c9650400d4f500192ca080029e60032594100061fbaceab202000a3f855cd64040014790ab9ac8080028fa1473590100051ec28e6b2020008be8714d640400117b0e29ac80817b2dc4372590102f65a886e4b2020608bd879c9640400147d0b392c8080028f616725901000657c12e4b202060cb7105c964040c196a20b92c80817a2fa1c72590100051f428e4b202000a3d851c9640400187ee5a92c8080030f5cb52590103171b886a4b202062e3510d49640400117d0f292c8080022f61e52590103251ec2ca4b202000
  | 2 => 0xb52d911035e1f3b6a5b222000a3e8654b64440014790ca96c8881ab0f9d952d91101c55a43243b222000ea46248764440735710c906c8880036adc920d9110007d090a41b222000c3d751d7644400147d0bb9ec8880028f61773d91100051f42ce7b222000a3d859cf64440715750039ec8880e6ae60073d91100045f438a7b2220008bd8714f644400117b0f396c8880028fa1672d91100051ec2ce5b222000caf825cb644400117d0e396c8880028fa1472d91100051ec28e5b222000a9e831cb644400153b06396c8880e6ada0472d91101c55ac08e5b222038aba801cb644407357300396c8880030fdcb52d91100061eb96a5b2220008be8794b644400117b0f296c8881b68f61652d911000717c12a5b222000c3f7254b644400187ae4a96c8880022fa1c52d91100045ec38a5b22206ca3e8514b644400117d0f196c8880022f61e32d91100051f42c65b222000a3d858cb644400117d0e196c8880022f61c32d91100051f42865b222000a3d850cb644407356d02196c888002ad60432d91101c55d40065b222000ab9800cb644407117d0f90ec8880022f61f21d91100051f42e43b222000a3d85c876444073d484290ec8880e62fa1f30d91100045ec3e61b222000a3e85cc3644400147b0b986c8880e62fa1f20d91100045ec3e41b222000a3e85c83644400147b0b906c8880032bdcb20d911000657b9241b22200487e85dd363440010fb0bba6c688007391c921d8d100076319243b1a2000ea9424836344001dc242906c6880f21f21b7558d100043f43ecab1a2000c3c74d9563440018d8e5b2ac6880021fa1c6558d100061e3a0cab1a2000c6c72195634400717d0dba2c6880e22f21b7458d100061fb2ee8b1a2000c3c65dd1634400117d0fb22c6880030fdd76458d100061e3aec8b1a2000cac72d91634400117d0e322c6880030fdd46458d100061e3a8c8b1a2000cac7219163440018decbb92c6880031b1977258d1000657b26e4b1a2000cac64dc963440090fd0fbaac6880021f60b7558d1001c5f43ee8b1a2000c3f75dd16344001878ebba2c6880022f60b7458d100043fc2ae8b1a200487c855d163440011df04ba2c6880063b2097458d100045f438e8b1a2000c3f751d16344001878ea3a2c6880063ba1f7258d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000637c2ee4b1a2000c6c85dc9634400195f09b92c6880032b2137258d100043fc2ae4b1a200487c855c9634400117f08b92c68800e2f2117258d100046fc1ae4b1a20008ee871c963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c6880021fa1f5258d100243e43ea4b1a2000c3f74d4963440d7878e9a92c6880031bdcb5258d1000e36396a4b1a200087e8754963440010f
  | 3 => 0x5b2a2000a5d831cb654407b4ed02396ca880f29d60472d95101e53d400e5b2a203da79801cb654400187ee5a16ca880030f5cb42d95100043f43c85b2a200087d8790b6544001c5f04a16ca880030fdc942d95100061eb9285b2a200087e8710b65440010fb0e216ca880021fa1e32d95100043ec3c65b2a2000a3e848cb654400147b09196ca880021fa1c32d95100043ec3865b2a2000a3e840cb654400147b08196ca880f69da0432d95100053ac0865b2a203ca7a800cb65440014f300196ca880f21fa1f41d95100043ec3e83b2a203c87e87c8765440010fb0f90eca880028fa1321d95100051ec2643b2a203de642148765440dd0ff0ea06ca880f61f21d40d95101ec3f43e61b2a200087d87cc3654400147d09986ca880028f61330d95101ec3f43e41b2a200087d87c83654400147d09906ca880028f61320d951000716a1641b2a2000e2d424836544079cd040906ca880030f197745951001c5f43ee8b2a2000c3f75dd1654400117b05ba2ca880030fd4b74595100043fc2ae8b2a20008be871d1654400187eea3a2ca880021fe1572595100045fc22e4b2a20038bc845c965440011bf06b92ca8800a3720d725951000c3e43aa4b2a2000c3f7454965440d5878e8a92ca880031bdc952595100045f43e84b2a20038bc87d09654400117d0ea12ca880022f21d42595100043ec14ec32a200087d8799065440010ff0eb20ca880028f60864195100061fb90c832a2000e3581190654400147d09318ca880028f61263195100061e322e432a200087f87d8865440018dae5b10ca880021f61e62195100051f424c432a2000a3d8498865440010ff0eb10ca880028fe1162195100051e422c432a2000a5f8358865440014b906b10ca880121fa1c62195100043ec38c432a2000a3e84188654400147b08310ca8800297a0c62195100052ec18c432a2000c6d72188654400147d0da10ca880028f21b42195100061f3b68432a2000a3c86508654400187ceca10ca880034b5c942195100071a3248232a203ba748650465440774e90c908ca880039918921195101d53c4324032a2000f29424806544001ec242900ca880030f9db65d91100051ec16cbb2220008bd87997644400147d0b32ec8880022fe1d65d91100051f430cbb222000c3e76197644400147b0432ec8880028fa1663d91100051ec2cc7b2220008be86dcb644400187ecbb96c8880030f19772d91100061fb2ae5b222000c3c655cb644400717f0fb16c8880032b5cb62d91100045ec3cc5b222000a3e8598b644400147b0b316c8880022fe1d62d91100051fc2ac5b222000a3c8558b644400153f06b16c888002a720d62d911006c5ec38c5b222000a3e8518b644400147b0a316c888002a7a0c62d91100054ec18c5b222000cad7218b644400147d0da96c8880028f21
  | 4 => 0x14c0019cae4b08c2980030f9d3659453002c7c432e128a6072d58535c2514c00b0f90eb2aa2980ae8f2116554530034ed406e6a8a605595e87dd5314c0b18b8edbaa629816395187754c5302b62e3b0ea98a6056e54611d5314c00b5ad0db0a6298002f1608614c530006ac3aee098a6000d5b751c1314c001878e9b2aa0980161fa1e54597100061fba4a8b2e20008df835c965c40051b906b92cb880161f21d525971000637b92a4b2e200487e87dd563c40010fb05baac7880021fe157458f100243e42ae8b1e200087f855c963c40090f90ab92c7880021fa1f5258f100243e43ea4b1e200087e8754963c40010f90ea92c7880030fdd74258f1034e1e3ae84b1e2000c3f7550963c40d1878eaa12c7880032bdc94258f1000e5639284b1e20058dc874c963c40039c8e490ac788003b14c92158f102c43fc2aeca9e200587c8759553c4001878e8b2aa18806697215634c31002e6a38ac698620038be87dd1658400117b05ba2cb080030fd4b745961038c3fc2ae8b2c204d8be871d165840e187eea3a2cb0801a1f21d545961001e1e3a2a8b2c200687e8794d65840df878e929acb080022fe11725961001c5e422e4b2c200687c87549658400187ee8a92cb081ab0f1d1525961000637b92a4b2c20008be87d0965840071790fa12cb080022fa1d42596100045e43a84b2c200087f855d163840090f90aba2c70801a37a1f5358e100346e43a86b1c2000a5c8550d638400d1b90e992c708007331c93258e1000754a1240b1c200287d85dd9538400117f08bb2a70800e2f2117654e1015d1e422caa8c2000c5c7558d318400d3b10e98a6108106d6215314c21002ee838a629842000c3d7495365440014eb032a6ca8800e1fe1d54d95100051f424a5b2a2000a3d8494b65440030ff0ea96ca880031b5c952d95100051ec10c9b2a2000e3581193654400147d0931eca880028f61263d95100061e326e5b2a2000c3c645cb65440018dae5b16ca880028fa1262d95100051ec24c5b2a2000a3f8458b654400147908b16ca8800297e0d62d95100052e41ac5b2a200e87d8718b654400147d08316ca880028f61062d95100052f418c5b2a2000a5d8318b65440018dae4316ca880028fa1b42d95100051e43685b2a2069c3e76d0b65440014790ca16ca881a30f9d942d95100071a32483b2a203ca748650765440794e90c90eca880039918921d95101ed3c43241b2a2000e68624836544001e5284906ca88003d848520d95100061eba0e9b2a203da76811d365440794eb023a6ca880028fa1273d95100051ec24e7b2a203ca7a801cf654407b4f30039eca880021fe1d43d95100043e43a87b2a200087e8710f65440010fb0e21eca880028fa1272d95100051ec24e5b2a2000c6f825cb654400147d08396ca880028f61072d95100052f418e
  | 5 => 0x81d30f9d464d8d503861eba8c9b1aa00487e85dd363540e90ff0eaa6c6a800f0f1d154d8d5000e5739285b1aa000cad7250b635400117d0fb22c6a80022fa1c6458d503861fba8c9b0aa00587c855d3615400717d0dba2c2a81362f21b74585500045f43ec8b0aa0008be8719161540e787cea320c2a81c30f5d464185500047bc3ac230aa02ba3e86d91515409b878edb22a2a815a1fa1f63545500071a326c2a8aa0008bf845da315400717908bb462a80030f191758c55001c5f426ec98aa0008bd84dd931540090f90a3b262a80030f193754c5500061fbaec898aa04ec3c75d91315400d1f100ba2cb1801a1fa1e54596300061fba4a8b2c600687c87551658c007878e8aa2cb1801a1fa1e52596300051f424a4b2c6000a3d84949658c00d0f90ea92cb180031bdc952596300061fba4e8b2c6000a7b805d1658c00d4f100ba2cb180030f5d074596303243ec3ce4b2c6000a3e849c9658c00147b09392cb1801a9ea0272596300053cc04e4b2c6000c6f825c9658c0c50fd0e392cb180028fa1072596300051ec20e4b2c6000c3f72d09658c00187ae5a12cb180021fa1e42596300043ec3c84b2c6060a3d84909658c001c5f04a12cb180030fdc942596300061eb9284b2c6060e2f20509658c0c1c5a40a12cb180021fa1c42596300043ec3884b2c605ea3e84109658c00147d0938acb180028f61271596300353d404e2b2c600087e87d05658c0010fb0fa0acb180021fa1e41596300043ec3c82b2c6006a7a80105658c0014f30020acb180021fa1f21596300043ec3e42b2c6000a3e84c85658c00147b0990acb180021fa1c21596300043ec3842b2c6000a3e84085658c00147b0810acb1807a97a0c21596300052ec1842b2c6000e6521085658c00d4f50010acb180029e60021596300243f42ee8b0c600087d85dd1618c00d1e90ea0ac31801a3d21d215863000e7239242b0c6000ea942481618c001dc242902c3180030f9d165946302ee1f32ae928c6000c3d655d2518c0018f2cab84a31801a1f21776546300346ec1ee9b2a60028f980dd3654c00187ae92a6ca980029760e54d95300346ec1ee5b2a600187f8754b654c0c98bae6a96ca980031b5c952d95302f64eb9e85b2a6060c9d7350b654c00717d0fba2ca980022f60b74595300061fa96e8b2a600087f855d1654c00117d0e3a2ca980030fdd4745953001c3e43aa8b2a6003c3c74551654c00117f08b92ca9800e2f21172595300047bc0ae4b2a60058f4815c9654c0030f90ea92ca980030fdd152595303561e3a2a4b2a6000c6f72549654c00117d0fa12ca9800e2f21f42595300045f43a84b2a60008bc87509654c00117f08baec29800e2f21175d85300043fc2ae9b0a600487c855d3614c003998e4996c298003aa50920d853002e7330ae430a60008f7875846
  | 6 => 0x56b408e4b1ca000ad5811c9639400d5b500392c728086b66007258e503152fc12a4b1ca019e4f8254963940efc3ea5a12c7280038754b4258e500cd2f42c84b1ca000a5d859096394001d1f04a12c7281db87d494258e500070ea9284b1ca060e8f2050963940c1d1a40a12c72806697a144258e500052ec2884b1ca000a5f855c563940434bd0a38ac728002976147158e500054f420e2b1ca000a9d841c5639400159d0438ac728002b36087158e500066ab88e2b1ca006ada801c563940435b30038ac72806697a174158e500052ec2e82b1ca019a5e8590563940014bb0b20ac72801ab6a004158e500056cc0082b1ca019a5e85c8563940014bb0b90ac728002a7a132158e500054ec2642b1ca0008de8708563940011bb0e10ac72806697a142158e500052ec2842b1ca000a9e84085639400153b0810ac728003b14842158e500356d40042b1ca000ad9800856394097ab6e7b82a7280021fa1e54586501ed3b40ca8b0ca05587c8754d61940014eb0b20ac32801a3d21d41586503af1a2a282b0ca0068f48748561940039c8e490ac3280021fe19739465016e2f31ae728ca0068dc83dd9319405b8bcc7baa6328067171d5634c65002d6a40ac698ca06fc3e7694f645400117d0db96c8a800e2fe1f62d915000656b96c5b22a0008bd8798b645400117f0eb16c8a807e2f61c62d915000656b90c5b22a04da3c8654b64540d587ceca96c8a80038bd8952d91502751f42ee7b22a04da3d85dcf645403f47d0b39ec8a80028f61673d91500061fa96e5b22a0008bd879cb645403f47d0b396c8a80028f61672d915000657b94e5b22a000caf825cb645400187ea4b96c8a80022fa1c72d91502751f428e5b22a04da3d851cb645409d47f04a96c8a813b8be0952d91500061fb92a5b22a000c3d7254b645400117d0f196c8a80022f61e32d91502751f42c65b22a000a3d858cb645400117d0e196c8a80022f61c32d91502751f42865b22a000a3d850cb645400156d02196c8a8002ad60432d915026d5d40065b22a000ab9800cb645400147f0ab8ec8a807e8f21571d91502751f428e3b22a04da3d851c7645400117d0e18ec8a80022f61c31d91502751f42863b22a000a3d850c7645400155d0418ec8a8002ab60831d915026d5d40063b22a000ab9800c7645400117d0f90ec8a80022f61f21d91502751f42e43b22a000a3d85c87645400117d0e10ec8a80022f61c21d91502751f42843b22a000a3d85087645400153d0610ec8a8002a760c21d91500075290843b22a04daba8008764540015730010ec8a813a2fa1f30d91500045ec3e61b22a04ea3e85cc3645400147b0b986c8a813a2fa1f20d91500045ec3e41b22a04ea3e85c83645400147b0b906c8a80032bdcb20d915000657b9241b22a04dc3d75d936354001c3ca7b26c6a
  | 7 => 0x798018b654c4d387ceda16ca989a30f9d942d953100717b1285b2a6200e2c6250b654c4b14b90c996ca988039318932d953116d3a43243b2a6200e6462487654c401e8a6490eca988030fdd274d95310061eba0e9b2a620087d879cb654c40147d09396ca988028f61272d953100637c12e5b2a6200a3e841cb654c40147b08396ca988b697a0c72d95312c52ec18e5b2a6258a76811cb654c45b4eb02396ca988029ea0072d95310053cc00e5b2a6200c3f72d0b654c40187ae5a16ca988021fa1e42d95310043ec3c85b2a6200e2f8250b654c40187ee4a16ca988030f5c942d95310043f43885b2a620087d8710b654c45b0fd0fa0eca988021f61f41d953116c3f43e43b2a620087d87c87654c40147d0990eca988028f61321d95312c73210a43b2a6200a3e84dc3654c40147b09b86ca989629760c70d95310043fc3a81b2a620087c87503654c4010fd0e206ca988021f61c40d953116d2f41881b2a6200a5d83103654c4014dd04206ca988029b60840d95312c53b40881b2a6200a7581103654c4010fd0f906ca988021f61f20d95310051f42641b2a6200a3d84c83654c401c5a85906ca988038b50920d95310043f43841b2a620087d87083654c40147d08106ca988028f61020d953116d2f41841b2a6200a5d83083654c4b14ed02106ca988029d60420d95310043fc2ae8b2a620087f855c9654c4011bf06b92ca988061f21d525953100637b92a4b2a6200caf72509654c403958e4a12ca988021f61e641953100537414c832a6200a6d82990654c4010ff0eb20ca988021fe1f621953100636b96c432a620087d87988654c40147d09310ca988028f61262195310043fc3ac432a6200a5f83588654c4090fd0e310ca988021f61c62195310051f420c432a6200a3d84188654c4018dae4310ca988029ea0062195310053cc00c432a6279c3e76d08654c4f187ceca10ca988038bd894219531007163128432a6256a5c864c8654c4ab4e90c908ca98803991892119531007a29924232a622dc5c73d95514c4090fd0bba6c0988021f61774d813100657b9285b026201cac7250b604c4039c8e490ec098803b14c921d81312c43e436eab02620087e87d95604c401878e9b2ac0988031b1cb65581310043f438cab026200c3c74195604c4018d8e432ac0988030fd9774581310061e32ee8b026200c6f65dc9604c4018d8cbb92c098957179cc65181310047dc3ac030262068dc8750d63940014bb0b192c728002a7a123258e500054ec2464b1ca0068dc874c96394003998e4992c72800297e157458e500cd2e42ae8b1ca021a5e851d163940014bb0a3a2c72806697a167258e500052ec2ce4b1ca000a9e849c9639400153b09392c72808697a147258e500052ec28e4b1ca000a9e841c9639400153b08392c728003335c87258e500
  | 8 => 0xebb04c0a99eb365cf60981530047dc3ac0302a600a3f855cd64944bb4790ab9ac9288ba8fa1473592510051ec28e6b24a200c3f52dc964944bf17b0f392c9289768fa1672592510051ec2ce4b24a200caf825c9649440187ea4b92c9289862fa1c72592511751f428e4b24a200a3d851c964944cb47f04a92c9289778be0952592510061fb92a4b24a200c3d72549649440117d0f192c9288022f61e32592512ed1f42c64b24a200a3d858c9649440117d0e192c9288022f61c32592512ed1f42864b24a200a3d850c9649440b56d02192c928802ad60432592510055d40064b24a200ab9800c9649440147f0ab82c9289768f21570592511751f428e0b24a200a3d851c1649440153d06382c928802a760c705925100557410e0b24a200aad821c1649440b56d02382c9288baad60470592510045f43e60b24a2008bd87cc164944bb47d0b982c9288028f617305925102d5b40860b24a200ab5810c1649440117d0f902c9288022f61f20592512ed1f42e40b24a200a3d85c81649440195ae5902c9288032b5c920592510045f43840b24a2008bd8708164944bb47d0a102c9288028f61420592510054f41840b24a200a9d83081649440b56d02102c928802ad60420592513a43e43aa8b1ca203c3e74551639440195ee4a12c7288072b1c94258e5102c6e43a64b1ca2038be84dc1639440117b09b82c7289ba1f21d54582510043f43ca6b04a23ca7a8094d609440b1f10e902c128803aa50920582510052ec2c65b1aa20287c855c3635440117f08b86c6a880e2f21170d8d511d43f436e0a9aa20487e85dd360544011f70eb00c0a88161fa1e54596310061fba4a8b2c620587c87549658c4018dee4a92cb188121fa1f75582310062f41eeab046200c5d83dd5608c4010fb05baac11880e2fa1f74582310061fbaee8b046200c3c75dd1608c40117b05ba2c1188021fe1574582310243e42ae8b046200c3f751d1608c401878ea3a2c1188021fe1572582310243e42ae4b0462008bf845c9608c40717908b92c1188021fa1f52582310243e43ea4b046200c3f74d49608c4d7878e9a92c1188021fa1d52582310043e43aa4b046200c3f74549608c4d5878e8a92c1188022fa1f425823101c5e43e84b046200c3f75d09608c4d3878eba12c1188022fa1d42582310045e43a84b046200c3f75509608c4d1878eaa12c118807391c9215823102c7c43a40b046200ea942481608c401dc242902c1188030f5d254d953101c3fc3aa9b2a6203c3e74553654c40147d09296ca988028f61252d95310052ec1ca5b2a620187f8754b654c4018dae4a96ca988029ba0a64d953100536c14c9b2a6200c6d72d8b654c40147d09316ca988028f61262d953112c3ec38c5b2a6200a3e8418b654c40147b08316ca988031b5c862d95310053d400c5b2a6200a
  | 9 => 0x786394607f23f9f680013700027095da7011fa2f1ac1601588cc8dfa0a95405d9938eb92e94e83697990624f1d1a6498f0f01201ed9970cd21621d1760f600026800000021da4c1ab97a0bd9951b69c98ac1318b79dfa638000d51910001f887f906a1f01a190108971800215a2280026120c0b52038e11269430000000c100013f972a4d27485c9bd87e81f1568df1e7a3f2582559a11400e314416a9a31bb84c9f781d8f103395c8b608c109a3512a05aa3b07d248a33a621030048608a0a1aa5a09680e2120c989fa092729290389cc8b086c8b913da650000000291131c095f0cb098a6d0001c38000000990000d4216a5e86010ba1c9670001e8a4e9a98000b686190a25405992785000026280000000015018587882824712a8e88b707618614c07b26405b8bc83a1af26318808890a9d899217a8470000228e5a0420500000009497515612c9f21d59f31d015e80015900007680016213980010722b93f00000017114b80022600014800020591992f1e69d48f50649b28060090060000780000005c008030080040080201c0380b81400000405801036000020030120040101802a0000580600805c040050020000880000804401800010004000080000000780400e0240100004203c0081400001c0101a016018088090020200100500601c00802008028018040020000080800200001841018000098010100240c00400a0280c8020140040181203a00c000040040901400f000014018000160000380100a014058180140a40001b00001c03000000024008010320040002b000008038080080600f0010020000081d0180280b809016008018090000001700000a00009008030018068010040180080200a0040081301a03001803026018070010000700400e0040180181802a0000200801e0000100900000c0580100a0240581407c0080480601c0c80001001001400000032004000010060200480000e010008120060340000a00e004018020080040680501800c018000080000480000e0400080c0000000200402a054000090020000280e06c0640000800801c0600000000c00004000024000010040000100902c0181a80000c0001b000002020018010180180000003c000148000000100280203c0140000800000006001000000010010000b80181401a0000a80c0120080680101e1840280001e020200340020040001200804c00002012000040000100b006800024044000000020040280007c06801801002000158020180780000200a0180000b0140041180800a04c0380202e00400001028048010000000000001703c0080100000a01c000000007f87f855d36154c011ef0eb08c2a99629de1561185530143ec2ee9b02a66e87f875536054c050fb0bb96c0a99fa1f61d52d81533ee1ebae85b02a67cc3d7550b6054cf78f2
  | 10 => 0x12fa679b600f8000bf20b0919b4a4f847991a2100011f00013527407d8a40000a39aaa3a19b26a80004315b05a1b513409c80002e8ef80009d0001d90000d38a4a428238878000000000002098001e7000000059212a550000f1a340ac8820eb0000001cd8000b388487485b0ed1b019919c1e01239410a28002448001b20120dc0198061ef0318620ea25c9f1a2214b0758ec8f78c20e69dc9701d280011412d97e89e174159a1b95525d03f1a509600985f912a1b0e780018b00000d96f19f9d69c716c1e39850d60000001429fe273a010001538000aba3d1949eba178af0310e0a6c0000c725784f80000022f9330811a705613796d10580c8972349b90000001629f000026e06a99b9e599e9cf16f88a80024a2118979f482e19a17913a18924a91d1d41968ce00023000001c9e80659ad8fa1c217c10f09c0d994c8a880702b01d1101c61e30230c40bf87187ca1000000008b9820000ca8a32029a29e40000000000c484480016780012880012c02608f8001fa80004407306c2328000571f0a0480004e2078000000000ef00000000004b08692b8001bc0c91ee887068000186a240001ce23a80017098e00800024311b8000001359f908822d0529d601e81317b1770000000da2198d69b185e8000000000001d125c2481db0950c080026b8000000001512598f311ea151211cc1fb99e0001ff23193c92d1eaa1f98489d82006f1c884c0b015322a97f0db15b960a392400e52478ba8001020842698fc98c202000225883a5b9698518220959a093086782597da539a924e16e845a000000e70de0d817c83e8ae0428001260111578162548a18078c88a7a1818d0352131a224b8001d81a89ae89ea0c998a6c91180007c0938000670bb8000a202a8168390001339958808000000000000000001b12370000000ff18300020697d22a11c1818000002108000c38000000000000000248001108001f400080025280004200013b80021a0d884f00016908580000025b22703c00018a0000091899739c910382180019297480a00000012183300024196c86996b0001cb00018c9d980016e1cf8000001310d30c32280bd235a289b9a192268270b2077039a239631ee0e600013906500000010793b0001b3a1713d0d0a412601ad2141ed00027508d8f206400025690e2019da00000000017e00020d81f8c51a7a110382589cd06d88b119164082a6d82c0d20400000000fa8001ac9259ae26900014180006100009a1ab1812608000000001329669c00898300000000ad1521df22b09806d20080003781a8720c58c694680006f82895c0dd8000fd1e50a10690158fc20b8001581e20001b78000751d72688000bb00002b9ca81b0f299082400020e0a580000007e26e8e408d0178438ce9872670c810823c0aa8320a716386e82ca2981c0d905
  | 11 => 0x25a80580521e07a92703604680006b117a4900026610b11224d8001be00000d0000002188b10000c79651688000188781a610419607b8000b194a9680010d10001518000001ea0000490e39c7a3e99a8fd9f817218b8e48c61111c48aa0191a80b410018d8f92520022231449bc9209dd1931c103a8cd9ec8550fb1888dba2e89a93c01723890d0209980a610d95486288f05d22790c11b0e000ba458329be9ff81186896482500310f8e81008cf9f117813894389993e0c280288623b9181c51841d50fb91d8000000001e985f27195d16a00019f00c1c8030a1e9300278de8be8aea5720813218fa399dd8000e98040fe0f38a504897b9029280c18cc12b19c8480ff8a99da8000901fd243890a291978ee23324682f90ea2c8268000000000d4a060850001878001e9129a2c250220a3680023c84d8001e18dc82102d14727304a9241451158e18039789660ca1c59d212505226f0831d39010911eb0cba32008a712139f60e211e0d1a5197f9f282f03592e24623d8138342201b88b8a2e04b9421d7a5f00011691502a1f391a0d00a821c0181fe8711db9fa0001a4001853050893161a2d80009289f1a000009b0e91ef91a8ad9fc800149a0f1f50f6a4ca2515a1479a18418d2a378000d798a936853a0a0001d325d94a19d1769658001f9a6a0148141171d09cb9ba95290c8b48739e62362590000a001006a03b104a499af8ed8ec2409f5849914a5300b1940779dc0f888e8f98be0f70540d59759e12149fb11889ba0f81086ba668581c28ab20d16b88e23e08a0f80f583e1f71488ea9730151a393a8940002420cf0408ee8000452308ba0001361c183b800066a0300018e9fd85495a8001cea3814920880012300000004e9a6a218af80024b13e9c6a450f0916101a0e9bf8c01ca15f8da9b826b02d94f25f94e1838661b580e8370001ba06e2561de1fc0700b590907a25101ba6181294583c9bd0b29e482985c140a5e0348588000000411a58fe8631c41b31570d710503f8741999bf07923100026f80f00a9809800569ec0709b41e093494f8a90002248b31de80680007294d8000a692200012480012288003d00011c97788ca5095e0890001b08b8150a071828e28bc1bb00005595580005e0461a483d9b71138f413827219d8f480000001e000081a659e28b996d85104a04d07994d1aa0920001610000002440dd1c3
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x140000480000402000589a10078e00001489a2a744000011290160000a00013921a60f8c1e8c1001c6c0190001322000c0074818b8128c0041c100400000302e3821d21481608c4016299018942d95310059864062487654c4b1644964c921d953116e9121932487654c40103f985d074d95310061a5c980188654c4016299018942195310059864062484654c4ad644964c92119531006315c9811c963940018c5825c47158e500063161d210856394001ac1216002158e50006a160d210876454001aa12160021d91500040fe61741d1658c0e1438905d074596300069160d21085658c001a6121600215963002d3125d3248563c400142d9219372d95100059164c6248765440016289650920d95101e59825921483654407ba608648520d95100050b648645c8654400182d845c862195100061360d72188654400182c865c942195100059164c624846544075a608648520195100050b64865dcb64440016859318921d91101cea82192148364440034c4974c92158d1000e3121d3248563440014a8975092058d1000e2a21d4248163440038e0874852058d10
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x2
  | 6 => 0x1
  | 7 => 0x4b
  | 8 => 0x4c
  | 9 => 0x4d
  | 10 => 0x4e
  | 11 => 0x94b
  | 12 => 0x94c
  | 13 => 0x94d
  | 14 => 0x94e
  | 15 => 0x124b
  | 16 => 0x124c
  | 17 => 0x124d
  | 18 => 0x124e
  | 19 => 0x138b
  | 20 => 0x138c
  | 21 => 0x138d
  | 22 => 0x138e
  | 23 => 0x9cb
  | 24 => 0x9cd
  | 25 => 0x9ce
  | 26 => 0x12cb
  | 27 => 0x12cd
  | 28 => 0x12ce
  | 29 => 0xa4b
  | 30 => 0xa4c
  | 31 => 0xa4d
  | 32 => 0x134b
  | 33 => 0x134c
  | 34 => 0x134d
  | 35 => 0xb4b
  | 36 => 0xb4d
  | 37 => 0xb4e
  | 38 => 0x144b
  | 39 => 0x144d
  | 40 => 0x144e
  | 41 => 0xbcb
  | 42 => 0xbcc
  | 43 => 0xbcd
  | 44 => 0x14cb
  | 45 => 0x14cc
  | 46 => 0x14cd
  | 47 => 0xecb
  | 48 => 0xecd
  | 49 => 0x9c953
  | 50 => 0x9c955
  | 51 => 0x949d3
  | 52 => 0x9c956
  | 53 => 0x12c953
  | 54 => 0x12c955
  | 55 => 0x952d3
  | 56 => 0x1489
  | 57 => 0x130a
  | 58 => 0x14a
  | 59 => 0x2c9
  | 60 => 0x14c9
  | 61 => 0x134a
  | 62 => 0x9d253
  | 63 => 0x1249d3
  | 64 => 0x9d255
  | 65 => 0x9d256
  | 66 => 0xec9
  | 67 => 0xb49d3
  | 68 => 0x9cb53
  | 69 => 0x9cb55
  | 70 => 0x198c
  | 71 => 0xbca53
  | 72 => 0xa4bd3
  | 73 => 0xbca55
  | 74 => 0xa4bd5
  | 75 => 0x168e
  | 76 => 0x1a49
  | 77 => 0x1a89
  | 78 => 0x130e
  | 79 => 0x14d353
  | 80 => 0x1354d3
  | 81 => 0x14d355
  | 82 => 0xed353
  | 83 => 0x134ed3
  | 84 => 0xed355
  | 85 => 0x2cc
  | 86 => 0x5ca
  | 87 => 0x19cc
  | 88 => 0x17ca
  | 89 => 0xecbd3
  | 90 => 0xbced3
  | 91 => 0xecbd5
  | 92 => 0x16ce
  | 93 => 0xb8e
  | 94 => 0x1889
  | 95 => 0xd0a
  | 96 => 0xd09
  | 97 => 0x188a
  | 98 => 0x1a09
  | 99 => 0xd4a
  | 100 => 0xd49
  | 101 => 0x1a0a
  | 102 => 0x10e
  | 103 => 0x10a
  | 104 => 0xd0e
  | 105 => 0x188e
  | 106 => 0xd4d
  | 107 => 0x1a0d
  | 108 => 0x95a15
  | 109 => 0x94d55
  | 110 => 0x14d
  | 111 => 0x17cd
  | 112 => 0x749
  | 113 => 0x1949
  | 114 => 0x949d6
  | 115 => 0x19cd
  | 116 => 0x5cd
  | 117 => 0xb8956
  | 118 => 0xd09d6
  | 119 => 0x1889d6
  | 120 => 0xd14d4
  | 121 => 0x1894d4
  | 122 => 0x1689d6
  | 123 => 0x198a54
  | 124 => 0xd0c
  | 125 => 0x188c
  | 126 => 0xd4c
  | 127 => 0x194c
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1300
  | 6 => 2246
  | 5 => 1259
  | 4 => 40
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (52863+((h/433+packedAt gbK7 (48100+(h % 433)*11) 11) % 1561)*12) 12
  | 6 => packedAt gbK6 (116784+((h/748+packedAt gbK6 (107808+(h % 748)*12) 12) % 3587)*13) 13
  | 5 => packedAt gbK5 (78890+((h/419+packedAt gbK5 (74281+(h % 419)*11) 11) % 1511)*12) 12
  | 4 => packedAt gbK4 (2878+((h/13+packedAt gbK4 (2800+(h % 13)*6) 6) % 63)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfe1fc7070fc3fff8e070383ff1461cf0cf90f
  | 1 => 0xf0fe1f807f0fc380f007fffc1f2b86333341f3
  | 2 => 0xffe3ff800ffc00fff803ffe0cc183cc38e3c
  | 3 => 0xff0003fffff00000fffffc0000f01fc0fc0fc0
  | 4 => 0x3ffffffffff0000000000ffe000fff000
  | 5 => 0xfffffc00000000000000000000ffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x1202410101004a2821108814a0020c5041905
  | 1 => 0x10420880210441041002512814018212114052
  | 2 => 0x954124800aa80824a00252804c0828428228
  | 3 => 0xaa0002595aa00012c954a80042b01540ac0d80
  | 4 => 0x881103ee6ccf325c0060301884fec000fbe000
  | 5 => 0xccf9900c088220600180c06318ff7fbf000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefee8feeafce8feeefee8feeafce8feeefee8feeafce8feeefee8feeafce8feeefee8feeafce8feeefee8feeafce8feeefee8feeafce8feeefee8feeafce8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36288
namespace PEqualNP.Outside.L_meta_36288
open PEqualNP.Outside.L_meta_36288.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 13 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 17 := bs0_4_0
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
theorem bs1_3_0 : Interval s1Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 4 := bs1_3_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
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
theorem bs2_4_512 : Interval s2Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 539 := (concat (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96)) (concat (concat bs2_4_128 bs2_4_160) (concat bs2_4_192 bs2_4_224))) (concat (concat (concat bs2_4_256 bs2_4_288) (concat bs2_4_320 bs2_4_352)) (concat (concat bs2_4_384 bs2_4_416) (concat bs2_4_448 (concat bs2_4_480 bs2_4_512)))))
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
theorem bs2_5_640 : Interval s2Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 664 := (concat (concat (concat (concat bs2_5_0 bs2_5_32) (concat bs2_5_64 (concat bs2_5_96 bs2_5_128))) (concat (concat bs2_5_160 bs2_5_192) (concat bs2_5_224 (concat bs2_5_256 bs2_5_288)))) (concat (concat (concat bs2_5_320 bs2_5_352) (concat bs2_5_384 (concat bs2_5_416 bs2_5_448))) (concat (concat bs2_5_480 (concat bs2_5_512 bs2_5_544)) (concat bs2_5_576 (concat bs2_5_608 bs2_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 40 := (concat bs2_6_0 bs2_6_32)
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
theorem bs3_2_0 : Interval s3Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 10 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 60 := (concat bs3_3_0 bs3_3_32)
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
theorem bs3_4_160 : Interval s3Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 165 := (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat bs3_4_96 (concat bs3_4_128 bs3_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 50 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_32 : Interval s4Atlas 2 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_64 : Interval s4Atlas 2 64 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 65 := (concat bs4_2_0 (concat bs4_2_32 bs4_2_64))
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
theorem bs4_3_96 : Interval s4Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_128 : Interval s4Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_160 : Interval s4Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_192 : Interval s4Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_224 : Interval s4Atlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_256 : Interval s4Atlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_288 : Interval s4Atlas 3 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_320 : Interval s4Atlas 3 320 23 := block_range (n:=23) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 343 := (concat (concat (concat bs4_3_0 bs4_3_32) (concat bs4_3_64 (concat bs4_3_96 bs4_3_128))) (concat (concat bs4_3_160 (concat bs4_3_192 bs4_3_224)) (concat bs4_3_256 (concat bs4_3_288 bs4_3_320))))
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
theorem bs4_4_1344 : Interval s4Atlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1376 : Interval s4Atlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1408 : Interval s4Atlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1440 : Interval s4Atlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1472 : Interval s4Atlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1504 : Interval s4Atlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1536 : Interval s4Atlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1568 : Interval s4Atlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1600 : Interval s4Atlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1632 : Interval s4Atlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1664 : Interval s4Atlas 4 1664 7 := block_range (n:=7) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1671 := (concat (concat (concat (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160))) (concat (concat bs4_4_192 (concat bs4_4_224 bs4_4_256)) (concat (concat bs4_4_288 bs4_4_320) (concat bs4_4_352 bs4_4_384)))) (concat (concat (concat bs4_4_416 (concat bs4_4_448 bs4_4_480)) (concat bs4_4_512 (concat bs4_4_544 bs4_4_576))) (concat (concat bs4_4_608 (concat bs4_4_640 bs4_4_672)) (concat (concat bs4_4_704 bs4_4_736) (concat bs4_4_768 bs4_4_800))))) (concat (concat (concat (concat bs4_4_832 (concat bs4_4_864 bs4_4_896)) (concat bs4_4_928 (concat bs4_4_960 bs4_4_992))) (concat (concat bs4_4_1024 (concat bs4_4_1056 bs4_4_1088)) (concat (concat bs4_4_1120 bs4_4_1152) (concat bs4_4_1184 bs4_4_1216)))) (concat (concat (concat bs4_4_1248 (concat bs4_4_1280 bs4_4_1312)) (concat (concat bs4_4_1344 bs4_4_1376) (concat bs4_4_1408 bs4_4_1440))) (concat (concat bs4_4_1472 (concat bs4_4_1504 bs4_4_1536)) (concat (concat bs4_4_1568 bs4_4_1600) (concat bs4_4_1632 bs4_4_1664))))))
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
theorem bs4_5_992 : Interval s4Atlas 5 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_1024 : Interval s4Atlas 5 1024 20 := block_range (n:=20) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1044 := (concat (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 bs4_5_96)) (concat (concat bs4_5_128 bs4_5_160) (concat bs4_5_192 bs4_5_224))) (concat (concat (concat bs4_5_256 bs4_5_288) (concat bs4_5_320 bs4_5_352)) (concat (concat bs4_5_384 bs4_5_416) (concat bs4_5_448 bs4_5_480)))) (concat (concat (concat (concat bs4_5_512 bs4_5_544) (concat bs4_5_576 bs4_5_608)) (concat (concat bs4_5_640 bs4_5_672) (concat bs4_5_704 bs4_5_736))) (concat (concat (concat bs4_5_768 bs4_5_800) (concat bs4_5_832 bs4_5_864)) (concat (concat bs4_5_896 bs4_5_928) (concat bs4_5_960 (concat bs4_5_992 bs4_5_1024))))))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 40 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_1248 : Interval gbAtlas 5 1248 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1259 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248))))))
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
theorem bgb_6_2240 : Interval gbAtlas 6 2240 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2246 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)))) (concat (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)))))) (concat (concat (concat (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216)) (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)))) (concat (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504)) (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664))))) (concat (concat (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 bgb_6_1792)) (concat (concat bgb_6_1824 bgb_6_1856) (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)))) (concat (concat (concat bgb_6_1984 bgb_6_2016) (concat bgb_6_2048 bgb_6_2080)) (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240)))))))
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
theorem bgb_7_1280 : Interval gbAtlas 7 1280 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1300 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 (concat bgb_7_576 bgb_7_608))))) (concat (concat (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 (concat bgb_7_736 bgb_7_768))) (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)))) (concat (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat bgb_7_1216 (concat bgb_7_1248 bgb_7_1280))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 34, 50),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefee8feeafce8feeefee8feeafce8feeefee8feeafce8feeefee8feeafce8feeefee8feeafce8feeefee8feeafce8feeefee8feeafce8feeefee8feeafce8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075688 * 2 ^ 32 + 4276813032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36288.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,5]⟩,⟨.or,[2,5]⟩,⟨.and,[1,7]⟩,⟨.or,[1,2]⟩,⟨.or,[0,3]⟩,⟨.or,[0,8]⟩,⟨.or,[2,4]⟩,⟨.or,[6,12]⟩,⟨.and,[11,13]⟩,⟨.and,[9,10]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075688 * 2 ^ 32 + 4276813032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075688 * 2 ^ 32 + 4276813032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36288

open PEqualNP.Outside.L_meta_36288 in
theorem PEqualNP.Outside.L_meta_36288 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075688 * 2 ^ 32 + 4276813032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075688 * 2 ^ 32 + 4276813032) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
