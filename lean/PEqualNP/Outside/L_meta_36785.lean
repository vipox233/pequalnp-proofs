import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36785.Model
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


end PEqualNP.Outside.L_meta_36785.Model

namespace PEqualNP.Outside.L_meta_36785
open PEqualNP.Outside.L_meta_36785.Model
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

def SBf (j : Nat) : Nat := [4, 4, 8, 8, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36785

namespace PEqualNP.Outside.L_meta_36785
open PEqualNP.Outside.L_meta_36785.Model
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
end PEqualNP.Outside.L_meta_36785
namespace PEqualNP.Outside.L_meta_36785
open PEqualNP.Outside.L_meta_36785.Model
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
end PEqualNP.Outside.L_meta_36785
namespace PEqualNP.Outside.L_meta_36785
open PEqualNP.Outside.L_meta_36785.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xa437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d02fca5a05f54b40dfa1681bd42d02fca3a05f54740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c53502fea4a05f14940dfa1281bd42502fea2a05f14540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc3be6598774cb30bf28e617d51cc2fea9185f95230beaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c3be6498774c930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620bea8c41ee21883d843105f94220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53482fea2907dd4520bba8a417c51483e8a2905d14520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb10a21f521443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0x180a00020018000481c008260208600002055f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543fba8a87775150ef8a2a1fd14543ba28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310bbca6215794c42bea9885dd5310abaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbc86997750d32f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d06fca1a0df54341beaa4837e53906faa720ef90e41de21c837e52906faa520efd0a41dea14837e519077e8320fdd0641bf284837d50906fea6a0f7d4d41afa9a837c53507b8a6a0d714d41dfa1a83bd43506fea4a0df14941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31fba0e63f441cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63df438c7b88718df94a31bea9463df328c7ba6518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131ef21a63dd434c6fea498df14931fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf29863df430c7b88618df94831bea9063df320c7ba6418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9
  | 2 => 0x3f000074968e944000024933306610039822343f4fa18f2986140000000000000000000000080000003050a00013e198798002cc1050e0b928a6b08800033e5010c80000037c0b19200887c0007e030814f603c3e607076a2b3ea390c7096000494e720d43a000000533a2000109700000004e87717a394001fa17e2c8579473a87a400040000000fb95f3e0138000000000002305f066740db80034c5880000007c3b05220f0000000010849c200e9178464050bf0280645c8bf9541a2554f702527820c7923003c499248a03128446605a1ce74c788862001840013f3721400012f000000000002863d5151c804e8210c24a2bc1801222e2c21f04e0b30324c8eb8902ca62c2e02339488802a340f26b4b79211c4770150f917c8ec160002827ac4f09b4ae4ecda08523643c4400126a204e08004848a000111000724ada4d000224bc9cf0b63a8f911d43c000cb1672dc0005b13836c8bc56844426894261150001fc000264980a46490316a0000010122c0d4d40003be06cb62440000007594e1b442cf68d51d00349f0f00004f49b23f18c6ecad159016360cf17b3700008b80038a7100000e4a0024d50003c45b4000fa478000218d948241c810000008000024f000828531c72d21b8ed8c541c120000d319e89846884000000960003d00d8ac0003f00007f9751420007b85e4065c4000000007007c13a0608a4000aa17432cec949448790088001f62a03825145a04c0007300052c9b8db3de0011c800130774d7191328778459e136a7fd2b1cd262000f51562ae288499c23624381d92335670c6806d1e85347004a1a4604391972f853c6b9243666808f16042c2f02aa071601d4b212a37492d0a8380c48d4f38b8416230c6a313422292396805a72c9425214a4b8718394743110b95134a7805d9f64b089c8223d3cc4884a9440c84308692b2fa3744918c1946f8b1999128690b50081681bc25934290030de8024026601b8d60002a4228c808469c7f129360148601f132618cde0dc0568b03284700076817800000918778003f654c7e15c23862035000486818001303c61744380035e688df8674a8448288121ec6541a0173208d8899d60160c00c00806008000e00003804020000000000000050000300600000000181c8c20403400006070000080a0200806002008660800205804020320a0080001a01024028040080201800010080001a028000180a00852008040380e0f83a0200600804000060480800802000100000e000040000e2484e0000600802000020783c178000000604000000080102005800000060480403804098080285a00016018040180602800080080c0201a80e0980a0300001802030000400601010000280000000002048000a0020480e018220b00e010000a00001012030043e8200c00e0382204814010
  | 3 => 0x6694a4360000008e03e7612a9b219c49c170714902b08c95d07a1d01890512223c3b015284914000a3338378559d530e450a319b0d65d0360e60ae0007096b314840d483a0347e44110a3ca8e0349fc334900b99501dc830001fd0f41a1298c34668842c8990000003c1fe47c25c00237000000030000000006380038c68c00020424460c31762127310480000003c4d0002ee0010d0a7006810000000002dc000582721ec900c22f488c6a0ae33a0003e85420c0282795223e000c0000044000268001628082b
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xd511025c6354440a758c41103355110440a758f401023f65500409ed95401031d54ccb30c755132cc27661d52309d587548c31e5450e30b5185438c29d640ca30a7590318c29d64cc2309758e544c26f62551309b189544c27761551309d185544c23e64149308f590524c25e65cc9309b988540c26d62150309d984540c27561150308f992530c23d6494c3097596430c31c5450c30b5185430c25d658c830a7590320c23f64544308f191510c29d640c430d5544310c29d64cc03097d95300c27b654c0309798c54c825d63153208f99053c823d6414f209798e548825d63952208f992538823d6494e208fd91518823c645462097d8d518825c63546208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e6515120c7d53534831c54d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f19153482776154d209d185534825e6514d20c7d50534831c5414d20cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d9146204825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d51083655188420ba580210826f6548020b9185200827b65480209798c54c425d63153108f99053c423d6414f108f99352c423d64d4b109798f52c425d63d4b108f99252c423d6494b109798e52c425d6394b109798f548425d63d52109798e548425d63952108f993538423d64d4e108f992538423d6494e108f990528423d6414a109798c528425d6314a108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e6515110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524436561149109d996214436452885109d19521443645248510d914a104425e63150109758c540426e62150109b588540423e6414c108f590530426e6214c109b588530423e64148108f590520425e63148109758c520427661148109d597210427565084109e59610042776544010b9189100427b6544010
  | 1 => 0x480000c080040300003000060000000000010010000100000000030040201c000181500400008060140200800008060140200800000000000303c00004010000001000010000080000c0c0000f0000200c0000404004000080300c0000008044020040600400008010000002c0000001008000180303801004000000200c04094030100100001000010000101c000080000c000080000000010010100100407004000100000400d5d0c5150f364314543a75924310e3f6550c43ad1854310e5f6550c43b51854310e9f6550c43c7d954310f976150c43a71854310f946150c43a51854310f1d4354843c750d5110f1d4394043ad18543d0a5f63547429718d51d0a5f63542429718d5090b1c5350d42ad1854350b1d53d08428fd954210b1d53508429bd954210a7661153329d58454ccb1c5450f32b518543cca3f64547328f19151cca7661d52329d587548ca3f64542328f191508ca7761551329d185544ca7b60551329e181544ca5c6550d32c7151434cad46150d328f596540ca3e64150329798c540cb1d54cc83297d95320cb1d544c8329bd95320cab46150f419798e529065d6394a4197d8d509065c63542418f997435071c53d0d41c714d43506b46150d41d514f415071c5390541d5185531063d6590c41c754e431071d5310c41c754f42106b561d0841c754d421071d53d04418fd95411069c6350441c754d41106776550441b518d411066e62153319b58854cc71c5450f31b518543cc79543d0731b558c41cc7964310731c7d50438c63e6494a318f592528c63f64542318f191508c63e649513197d8d544c67761551318f994544c71d631513197996434c71c5490d3197195434c71c5450d31b5185434c73454cc531c7152314c63d6595031c718d540c73461550318f990540c65e631503197597430c71d54d0c3197594430c71d5410c31c7553320c6d561cc831c7551320c73554d0431e5d0f410c6756510431e510c410c71d54cc43197d95310c69c644c431c7551310c677654c431ad191310c65e63d53219758f54c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c863e6414f218f59053c865e63152219758c548863e6414e218f590538865f63551219718d544867b60551219e181544865e63151219758c544863f6454d218f191534867b6054d219e181534863e6414d218f590534865e63150219758c540867a60150219e580540863e6414c218f590530867a6014c219e580530863e64948218f592520865e63948219758e520866f65484219dd95210863f64540218f191500865f63540219718d500871d53d0b40c754d42d031e5350e40ad185439029d6310a40a758c419029d63d02409798c525025d63149408f99742502b46150c408f596421029d631084097d8
  | 2 => 0x119de3b8007a8009a21e592fa74ab80024c00000b0202001c2510002e06cba9803c1b44399076194311fa4a000169a0c2ac6af2987b2562f0004400a448209193a25a3c5b000040c6000000f20c20a2c001a49795000000003166cac4b0800000a800060000449e80000100a48baa205648018358007d88ca40000b18400000588001496ec00006ea4a899f02708600182c3000002e0089b8c500038ae253036138be0000051814a78002115e34800ac0f800000ab000ab9c45695c351b600a0000000bd00000000002fe0000000000000000017c660000025ac18006980090a7471864000500009a6f000a0000038005f800770008d8007318856260000681000084adc960000000000000791a20000030800552aa7983e8e0000013c000002a8006b00024264000a09b000002a2002184080c000003a80000000000000000047a6e00074000d0b485ead20e38000780000014e171d0941d6678000e282bd8004f80000000c20669f0000d01e000001f0000026623800000000019a00000b523200000558e4828000000000000b216a7a1340000037a6a5e1403d0003e8009f8007f00064a3e1daa65a00058000a502846b125c2ba7fa78a299c618000000094a06bf0ac00000b90006c0008d062810cc701a8002a4048fcb789e0000052892291ae000003c86a0000000000001f8000004a8ce00132950781e8707283225000002ec36000000000006e0000000000001f40000000000002da72000b428665936b5ab6000a29891c598000003a7b8002d270000263f80000000b2a1c001ce00000a39aa0ba2e00000a70dc6fa4e092b20000049000000000000085000001f20008a41000c08002b800000b22c000000002d80000000002ce069760000000000000008a000000e8000580000063800010ec41a484511697138002242002a78800c3972a1108121267681c0000042a10822721c8c80003000000a6af8a5808bb97a0012c9d92e00000bc85486a3a220ca0022aa301690118632f0b9a20000005204a00000000f6002be85942398da4c1746287ec1222912ccb604c00098c40000180029800000c0ba0428c000431d448800aa2a05
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xc58325b48504029101818f01c54d20e4c22c05d400701968401020784300014003855d46150c43a28e2a1aa421d147150d5110e8a38a87280878514c6150d42a2ae22a287996145418543ccb0a2a0c2a1a65251cd61d0841c2aa6b0e8420d0d7215143cc70a2a0c2a1e63255da4310731c28a830a8698e1463185540c64a3a2c3990638555161cc831a2aeba1e8218e156510c410c60e3b2a8988638594c6150e40a28e6a88822061563544411030b2a0c2a1c61435c85450c30a2ae22a2861861454185430c28a3a2a21886185591510c430
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x30420a05821506150f318148755161cc831a05821506150c3081487591510c430
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 601
  | 4 => 396
  | 3 => 29
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
  | 5 => packedAt s2K5 (18227+((h/200+packedAt s2K5 (16227+(h % 200)*10) 10) % 722)*11) 11
  | 4 => packedAt s2K4 (16368+((h/132+packedAt s2K4 (15048+(h % 132)*10) 10) % 632)*10) 10
  | 3 => packedAt s2K3 (1475+((h/9+packedAt s2K3 (1421+(h % 9)*6) 6) % 35)*6) 6
  | 2 => packedAt s2K2 (243+((h/1+packedAt s2K2 (240+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x3ffff81ffffff81fffff07ffc1ffff9f1f1ff
  | 1 => 0xfc07fffe03ffe1fe0fc1ff87ffe1fc068e7e7c
  | 3 => 0xfff81ffffc0ffffff001fff87ffe1fff0f8f8f
  | 4 => 0x1ffffff001fffffe00007fffe007f00ff0
  | 5 => 0xffffe000000001ffffffffff80000007fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x4850808c4882400052c250089402255030b0b5
  | 1 => 0x19314914392482960550b4852d21483286565c
  | 3 => 0x20a252209069112aa02129504a5412a50b0b0a
  | 4 => 0xb2c59c492241d5cd39b40c44739980c7d00de0
  | 5 => 0xc3061871c38e19f1ce39ce6603110307ede000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaaee88ee88aa00eeaaee88ee88aa00eeaaee88ee88aa00eeaaee88ee88aa00eeaaee88ee88aa00eeaaee88ee88aa00eeaaee88ee88aa00eeaaee88ee88aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36785
namespace PEqualNP.Outside.L_meta_36785
open PEqualNP.Outside.L_meta_36785.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x52640082400696002c09b1478a98046950012809971cac61c00b800046143805a848833a3d11400b14243e113af4c008250c18000181b2c500e441090005ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x61dd320c3b864185f94430bea8861df310c3bc6218774c430ee188617e500c37c80186f10030ef98061fa300c3ba60187e4c030efaa061de540c3baa8187715030efa9061de520c3baa4185754830ee29061df420c33e84187790830eea10619d420c3b8841877d4430ef28861dd510c3b8a21877d0430ef20861dd410c3b8821877c8430ef10861dd210c3b842187794030af28061da500c3be80187790030cf20061dd400c3b880186710030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20dfa1641bd42c83be6590774cb20bf28e417d51c837c81906f10320ef18641dc30c82fea9106fd52209faa4417e54882faa9105f15220de2a4413c54882fea71077d4e20afa9c417e53882faa7105f14e20ee29c415c53882faa5106fd0a20dea1441df32883ba65105f94620bea8c41ee21883d843105f94220df20441bc40883bc6110770c220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c534837e84906f50920ef99241dd32482fea2907dd4520bba8a417c51483e8a2905d14520df20241bc40483bc6090770c120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4106fd0820dea1041df32083ba64105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020df20041bc40083bc6010770c020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43be6588774cb10fb10e21f521c437c81886f10310ef18621dc30c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c528437e85086f50a10ef99421dd32842faa3087dc8610fa10c217e508437c81086f10210ef18421dc30843f441087e48210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea68877d4d10afa9a217e53442faa6885f14d10ee29a215c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c524437e84886f50910ef99221dd32443ec42887d48510df20221bc40443bc6088770c110fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810dfa1021bd42043be6408774c810bf28821f721043e842085f94010df20021bc40043bc6008770c010fb88021fa10043ea20087e44010
  | 1 => 0x721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21dfa1243bd42487be6490f74c921fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043bf420877a8410f7cc821ee990437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e81de53d02bca7a05f54f40eea9e815d53d02fca5a05f54b40dfa1681bd42d03be65a0774cb40bf28e817d51d02faa9205f94e40bea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd4290378852077cca40ee994817e51902faa3206fd0640df20c81bd419037883205f94240dfa0481fb409037ea7206f94e40dea9c81bc539037ea5206f94a40dea94813d5290378a5206fcca40cf99481be329037a6520674ca40de19481bf519037ca3206f54640de28c81bf319037c63206f4c640de18c81bf219037c43206f48640de10c813e50902fea6a077d4d40afa9a817c53503b8a6a05714d40bfa92817c525037e84a06f50940ef99281dd32502fea2a05f14540fda0281be40502fca8205f94c40bea9881bf431037c86206f50c40de218817e52102faa4206fd0840df21081bd4210378842077cc840ee990817e51102faa2206fd0440df20881bd411037882205f94040dfa0081fa401037a80207e50040dfa9881be531037aa6206f14c40dfa9081be521037aa4204f54840de29081bf321033e64206f8c840de990819d321037864206fd4440df28881bd5110378a2206fcc440df18881bd311037862206fc8440df10881bd211037842206f940409f28081ba50102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc2fca5985f54b30dfa1661bd42cc3be6598774cb30bf28e617d51cc37c81986f10330bfaa4617e548c2faa9185f15230bea9c61df438c3bc87187750e30ee21c617e528c2faa5186fd0a30dea1461df328c3bc6518774ca30ee194617e518c2faa31877cc630ef18c61dd318c3b863185f94230df20461bc408c3be61187ecc230efaa461de548c3baa9187715230efa9461de528c3baa5185754a30ee29461df428c33e85187790a30eea14619d428c3b8851877d4630ef28c61dd518c3b8a31877d0630ef20c61dd418c3b8831877c8630ef10c61dd218c3b843185794230efa0461de408c33c81187750230ee204619c408c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c37c80986f10130fd98261de304c2fea8185f95030beaa0617c540c2fca61877d0c30ef21861dd430c3b886185f94830bea9061bf420c37a841877cc830ef19
  | 2 => 0xafaa6217754c42aea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccbbe87997790f32eea1e65dc43ccb7e85996f50b32bf28e657d51ccafca1995f54332efaa665de54ccbbaa9997715332efa16659f42ccbbc85997750b32cea1665dc42ccbbea3997794732eea8e65dc51ccbbea1997794332af28665dd50ccbb8a1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32aea9c657e528cb7e85196f50a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbe86997790d32eea1a65dc434cb7e84996f50932f799265de324cafea2995f14532bfa82657c504cbbea8997795132eeaa265dc544cbbea49973d4932efa12659f424cbbc84997750932cea1265dc424cbbea2997794532eea8a65dc514cbbea0997794132eea8265dc504cab8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32af298657e520cb7e84196f50832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077e85a0ef50b41ef99683dd32d06fca1a0df54341beaa4837e53906faa720ef90e41de21c837e52906faa520efd0a41dea1483df32907ba6520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa92837c525077e84a0ef50941ef99283dd32507ee82a0ef90541bfa82837c50506fca820df94c41ef298835e53106faa620f754c41aea9883be43107788620df94841bea9083bf421077a8420f7cc841ee990837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31dfa1663bd42cc7be6598f74cb31bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518efd0a31dea1463df328c7ba6518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131ef21a63dd434c6fea498df14931dfa1263bd424c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf29863df430c7b88618df94831bea9063bf420c77a8418f7cc831ee990637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21dfa1643bd42c87be6590f74cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510efd0a21dea1443df32887ba6510df94621f790c43f
  | 3 => 0xfc00000000b300024e000804968005142f4000e8244d2d35bc72e649d493cc41c001808003dc9d955899000001bf8210000017b2b32e03bc723626704ddac8712468c07c0f2580620860007ac0004023127e5c83a8002be32ca2064790c3c002ec716ed1f78ec000b1de0353000001831f616e0005c2555406cca02ac592064003a83041807e94d000e940031c000f280028d09a464000003c600006800354d04c7b302a40000d22a1ee000001e6000c94c60e578c638eba515b0000c90000001f5d0baa000000008018030020100000001c0180d0080080240080200000002800000000018030020080000000c06005006002004008020040000280900a004010060120000000200c000000000000100081a0000040080c0020000080000c0180200100a0100200300000c0000200000c00010002000000040000080200501a00405000012000008040000000080c000008008010020000080500a000000020180240000300201c06000000014020030060000380000605004005002014000090020080d0080060000b8000000000100200e004040000060600000400400004018002000008010040040000400a004000030280040000f00000c0080000c0280080a02603c0200000c0040000100200401003008000000070000000280600c00002800008000028000080140000100600c01804004024008030040000301f0020240000b004000020030040040000700e0280001b006014000250020100000100001802004008018048010000000180000200c01000000004000000040000080400203800003000000008030000100000c00400000004000000018000000140100200e0c4018250020340280000001c00000002000000090000000001600000c0200001e03c02003008000000030040100280100000c005f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f90f42dea1e85bc43d0afca3a15f54742bf286857d50d0b7ea7a16f94f42dea9e85bc53d0b7ea3a16f94742dea8e85bc51d0b7ea1a16f943429f28685bd50d0b78a1a15f552429eaa4857e5390bbca7215794e42bea9c85dd5390abaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85be4350b7a86a16f10d42f7a1285be4250afea2a15f14542bfa82857c5050b7ea6a16f94d42dea9a85bc5350b7ea4a16bd4942dfa8a85be5150b7aa2a16f14542dfa8285be5050b7aa0a16f141429e282857e5410a7ca8215f94c42ef298855e531
  | 4 => 0xa08cce3273bc000450005680014e000000b3c653e502c3312502f74050c8d963000000000000e8000000004164a4e0bdf16a4e544bad5828dce00004300fd729f80000017000030a320000006d8000ab00057899073286264694fe2403feb2d520af2b81bc7db8063e6b9fa9ba4001384b00017800111bd12228207b17d00000115bea79a6886080000000000000000f98998007280018d0480008d570a4c2fc2cdb3000000000ed395000db57c00002ae4cfa0006deadc5939f0000000009e000c90f380019c0000000000000070800000080003863d61a40001d5a6a04000005228edf60e3000000000926be71000000000a5000000216d0ca8add71e2f9c3a907ba000e5136000000001be0001240032c276d08002a9000001c6a2f070000003c9736001f41746ca988c003b2602e40e05d0be001c40fc3724f8da2b94dc00009ab80188856f000000001e1ad5000375be9762f400179376050001fbb5c0009416b800278000d80f54fc000030000000003d0fe69c2441b01e000001b9aff0000b5bb80038a69800000028ea400000000e25ea0000005903d91a000aa1713d70001c99990500000000385000a95af0d73f4de15eb121feed4b3b5877c02d0234f316001571e21b48a1739fe4580012b0a52ee0017c80020643c230000520018b01f588d8403800084001f08000003591200076c78000000096ac8000004d2284f63b8412148cc012600f14008243589e95b0004da0006c3cf078001cc8000b29ec001680001a1ad80000036d1cb363360000025c000354003bd6e2314003e9778de400000000a11dcad4000000b52800003459309a1bcc38002ad3ba9dc0034a000141b53da000f08003505d40c0d000025e531b18c9000c4c00000000e0800000000000f90003c21100034667e001d604038cb98000004cc0018c8002080000020200056d9f28b714000002fe008001438003a6978138004740004234021255d95800000628d899012a418289e5724651443484fa000d48ad154c29c18580120011288d748000cc832000115bd80054e000002c34640014d1a13aaac5aa06e0007208902a3b6ca041297000829918000000000014239600000000000000c19b80008f0002170aa5e11b1b516c7ddf71d96a24400026801c274000004b05b80023d7c000122800000000f7adc022000002d94a44a80034d0003e4ef80021c0000000000047ca706c000e5c1c80000000000000432645c08005740000020c0825b17ba70106ebc188002f69040023800083c000636aa7ec8ab057c84e90da4d000000b580072039c368003500003b000000000c21480007a0d200000003c001c24526180004f5f400000000610000d78002301fd29adf2140018c2c65b4594000001504d5d10ac1529e4000ab000001ce01b698000003f4128000350d4140e
  | 5 => 0x658000004900000c000618551580004b4fe047ad60000015d85b5daaa99a0547e41c03e10859467c8b8883f28b4173d939c2b88036b674185aba2e282898001593e0371e721500054121000640000000981743ccdb91d2aac745d8006c82990b1ea0000006026c57ea396900017e9a800000000b14198470000002e335654000481fd65a0019b80061af41771975321300021d4ba2d066b960569e03f3eb5e28354b3703d2c88e7b2e4e4674003b123c37c630792c2964713de4244d0d1a606dc00000086000000001d2000a08868003a0abdaea757ec29d2a3c4000000002be6a400000000000724a780000000000000000021ed80000015c962610bcbac97000000f60001217e0ec04e000000c44000001c022c002202de604940006f40000000069284cd3b2924889c0031b67a00141ae3112000752f451800063a73386d680000002e97c002140007580280012600000000782001f9878000001478a32b49fccab746f80282195d000001859d80008cc0000011c0000000012e0012783e0ccb098bb446e4000a33d5226b90520c3000edc0038c0d64952b9bc63c744f6aa247c3650e0002b0730001660000b0002065d2000002db2960000000048c3b90389f24c3090d0250b4cf00004a06a3ad23800000001810f10000f59d800000001cd29d56aee88a2655e6bf00017c0000001b800000000012cd642a797a8000000001d3a30000006200028eb40d5853334a6c8b3454e219c00203118001c238e43e0010800077600001a43160001e92e85a2a8c00169664c5137800000bc0003ae0000018aa4b10e15800000000cbd8180074e0000006233c734a53756c0f71cf000000001e980020e4acb895e4887cd98bcb526288003a6000f8c399201a4bf4000cf000fb4f8b6704c4049e938620000c3a1e5f64098227c73a0011a2ef50ab39640ed1d25fdf38812922c5bf1bd000e61c8b682f2088ea1bf3125d4000f068e6b47d1f561264c3b8000008440000054cec81a0007c40000001038e470b02981a60019c8000009d0001450ca5b498a630000018398d4ce0014aa9f0006c8003694b6ecc00000000a84db1dc37600000000444eac683f11e89240020500054c4d962000d58f223f10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x352c425e63d4b109758f52c423e6494b108f59252c425e6394b109758e52c423e6414b108f59052c425e6314b109758c52c423f65d0b108f59742c431e53d0b10c754f42c423f6550b108f59542c431e5350b10c754d42c42b86050b1097d9732c425d65ccb10c795332c431d54ccb1097d9532c425d654cb10c795132c431d544cb10b618132c431e5390310c754e40c431e5310310c754c40c431e548c310c755230c431e540c310c755030c425e63d52109758f548425e63952109758e548423e64d4e108f593538423e6494e108f592538423e6494a108f592528425e6394a109758e528423e6414a108f590528425e6314a109758c52842f16008610e610030843e02188210bc185208423d62d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f588544423e60151108f180544431f54d4d10c7153534425d62d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d1097588534425e6014d1097180534432f54d4910cb153524434f53d4910d314f524432f64d4910cb193524434f63d4910d318f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524423e64149108f590524425e63149109758c524426e6514910cbd50524432c5414910d3d4c524434c5314910cb990524432d6414910d398c524434d6314910d9584524436960149108f997424423c65d0910c7d4f424431c53d0910cbd4b424432c52d09108f995424423c6550910c7d4d424431c5350910cbd49424432c525091097997324425c65cc910c7d53324431c54cc910d3d4b324434c52cc91097995324425c654c910c7d51324431c544c910d3d49324434c524c9109d996214436452885109d195214436452485108f996404431f5390110c714e404432f5290110cb14a404423e6510110c7d4c404431c5310110cbd48404432c521011097996304431f548c110c7152304434f528c110d314a304425e650c110c7d50304431c540c110d3d48304434c520c110e610030443685288110f888620442786548110d914a104425f63550109718d540425e63150109758c540426e62150109b588540423f6454c108f191530423e6414c108f590530426e6214c109b588530423e64948108f592520425e63948109758e520423e64148108f590520425e63148109758c520427661148109e980520432e5250810cb54942042b86050810d3949320434d524c810b6181320423e64944108f592510425e63944109758e510427565c84109d59421042f160084109e59610042776544010b918910043b04044010f40c1100427b6544010
  | 1 => 0x831f544ca20c715132882d8604ca208f992518823d64946209798e518825d63946208fd91518823c645462097d8d518825c6354620ba580218831f5390220c714e40882ad6290220c7d4c408831c5310220ab588408831f548c220c715230882cd628c220c7d50308831c540c220b3588308823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534823e65d0920c7d4f424831c53d0920ae983424823c6550920c7d4d424831c5350920ae181424825e65cc920c7d53324831c54cc920b6983324825c654c920c7d51324831c544c920e350932482d8604c920cdd53514833454d4520d5d4f514835453d4520cdd0b514833542d4520d5ccb514835532d4520cdd5051483345414520d5d4c51483545314520cdd0851483354214520d5cc851483553214520dc580514823e6590120c7d4e404831c5390120cdd46404833451901208f994404831f5310120c714c40483375110120cd144404825e658c120c7d52304831c548c120d5d463048354518c12097994304831f540c120c71503048357510c120d5144304836451881209798f540825d63d50209d987540827561d50208f596540823f62550208f589540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530825f6254c2097589530823e6414c208f590530825e6314c209d98453082756114c208f992520823d64948209798e520825d63948208f597420831e53d0820c754f420823f6550820c794d420831d535082097597320831e54cc820c7553320825f654c820c7951320831d544c820cd95251083355494420d594e51083555394420cdd0a51083354294420d5cca51083553294420cd95151083355454420d594d51083555354420cdd0951083354254420d5cc951083553254420d9546210823f65900208f596400831e5390020c754e40082ad6290020cd946400833551900208fd94400823d6510020c794c400831d5310020ab58840083365110020cd544400825f658c02097596300831e548c020c755230082cd628c020d59463008355518c02097d94300825d650c020c7950300831d540c020b35883008356510c020d55443008398400c020dc546200826f6548020b9185200827b6548020dc545200825e63d53109758f54c423d62953108fd8954c425e63153109758c54c423e64d4f108f59353c431e5494f10c755253c425d6294f10c795153c431d5454f1097d8953c423e6414f108f59053c423e64d4b108f59
  | 2 => 0x655063097994418c25d651063097997218c25d65c8630a7993218c29d64c863097994218c25d6508630a7990218c29d6408630b6980218c2d96008630a758a408c31d5290230a7588408c31d5210230e6980408c23d62d51308f992544c25d639513097d8d544c23e65151308f588544c23e64149308f590524c23e65d09308f197424c23e65509308f195424c25e65cc930c7d53324c31c54cc930c7d51324c31c544c930d3d49324c23e65901308f994404c31f548c130c7152304c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c30c7151430c25d6510c30c7550430c23e64948308f592520c32e5250830cb549420c2b86050830d354b320c25d658c830a7992320c29d648c830a7990320c29d640c8308fd91510c23c6454430a7d91310c29c644c430a7990310c29d640c430d5544310c29e64cc030a7593300c25f654c030a7d91300c29c644c0309ed95300c2da60d5030c7550540c2ce6215030b3588540c2d66115030b5584540c2da6015030b6983520c29e6494830a7592520c29e6414830a7590520c2d66114830b5584520c2da6014830c754b420c29e60d083097996420c25d6590830a7592420c34d5290830d3549420c2db6050830b6181420c38f6250830e3949420c31d5250830e3549420c30d5250830e6d81420c29c6050830e6181420c298605083097994420c25d6510830a7990420c2da60d4430a7d91510c29c6454430a7990510c29d6414430b3988510c2cd6214430d5544510c2da6014430b6982410c2d9609043097d95410c25c655043097994410c25d651043097997210c25d65c8430a7993210c29d64c8430d354b210c34d5248430b6d81210c2d8604843097994210c25d6508430a7990210c29d6408430b6980210c2d96008430c7d0a500c31d4294030d6982500c39b4294030e650a500c25d65d0030a758a400c31d5290030a7982400c31e5090030e6942400c25f6550030a7588400c31d5210030a7980400c39a6010030c7940400c39a50100309798f54c825d63d53209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f20c795153c831d5454f208f99053c823d6414f20c794f42c831d53d0b20c794d42c831d5350b20c795332c831d54ccb20c795132c831d544cb20e350932c831e5390320c754e40c831e5310320c754c40c831e548c320c755230c831e540c320c755030c8398400c320cb58b548833a60d52209798e548825d639522097d8d548825c6355220cb588548833a6015220c7d53538831c54d4e20d358b538835a60d4e208f992538823d6494e208fd91538823c6454e20c7d50538831c5414e20d3588538835a6014e20c7d4f428831c53d0a20ae983428831f5350a20c714d42882b86050a20c7d53328831c54cca20b6983328
  | 3 => 0xe40c7d4e53902ba6014e40ae983529029e6394a40a758e529029e6314a40a758c52902b66114a40ad58452902ba6014a40c754b329029e60cca408f996329023d658ca40e3d89329031d524ca40a7181329023e650ca408f594329029e63d4640a758f51902ba60d4640a798e519029d6394640cdd4651902ba60146408fd95319023c654c6408f994319023d650c6408f997219023d65c8640a798f219029d63c86408f994219023d6508640a798c219029d6308640ae98021902b960086409758b535025d6214d409798c525025d63149408f997425031f53d0940c714f425031f5350940c714d425032f525094097997325025c65cc94097995325025c654c940c7d4e405031c5390140c754c431025e63948409758e521032d52d08408f596421029e6390840a758e421029e6310840a758c421034e524c840d354932102d8604c84097d8d511025c6354440a7d8d411029c6350440a798c411029d6310440cd544411029e63d0040a758f401023f6550040a7d8d401029c63500409ed9540102ba60d4c40c754c53102ae6214c40ab58853102b66114c40ad58453102ba6014c40ae983521029e6394840a758e521029e6314840a758c52102b66114840ad58452102ba6014840c754b321029e60cc8408f996321023d658c840a758e321032d528c840cb54932102bb604c840ae181321038f624c840e3949321031d524c840e3549321030d524c840e6d81321029c604c840e61813210298604c8408f994321023d650c840a798c32102ba60d4440a7d8d511029c6354440a798c511029d6314440ab98851102ad6214440cd54451102ba6014440ae98231102b9608c4408fd95311023c654c4408f994311023d650c4408f997211023d65c8440a798f211029d63c8440cb54b211032d5248440aed8121102b860484408f994211023d6508440a798c211029d6308440ae98021102b96008440c7cca501031d3294040ce982501039b3294040e64ca501023d62953308fd8954cc23e6494b308f59252cc23f65d0b308f59742cc23f6550b308f59542cc2b86050b30c795332cc31d54ccb30d354b32cc31e544cb30c755132cc27661d52309d587548c31e5450e30c7d50438c23e6494a308f592528c29e648ca30a7592328c34d524ca30a7990328c29d640ca308f992518c23d6494630a7d91318c29c644c630d5945318c29e640c630a7590318c29e64cc230a7593308c2d661d5230b5587548c2da60d5230c7d52548c2da6015230b6983528c29e6494a30a7592528c29e6414a30a7590528c2d66114a30b5584528c2da6014a30c754b428c29e60d0a3097996428c25d6590a30e3d89428c31d5250a30a7181428c25e6510a3097594428c29e64d4630a7593518c2da60d4630a7992518c29d6494630d5d46518c2da601463097d95418c25c
  | 4 => 0xf990524c63d64149318f997424c63c65d09318f995424c63c6550931c7d53324c71c54cc931c7d51324c71c544c931d3d49324c6d4614c931c7152314c63e64d41318f593504c63d65950318f58a540c63e6095031c718d540c63f62550318f181540c63e64150319798c540c65d65d0c31c7553430c65d6510c31c7550430c63e64948318f592520c63f65d08318f597420c63f65508318f595420c71e54cc831c7553320c74d52cc831b5587320c71e544c831c7551320c71d54cc43197d95310c69c644c431c7551310c677654c4318fd91500c63c64540319798f54c865d63d53218f98254c863c60553219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f219798253c871e5454f21c755153c865c6054f218f99053c863d6414f21c794f42c871d53d0b21c794d42c871d5350b21c795332c871d54ccb21c795132c871d544cb218fd9150c863c645432197d8d50c865c635432197d8d548865c63552219798c548865d63152218fd91538863c6454e218f990538863d6414e21e3509328863f64542218f191508865f63542219718d508865f63551219718d544867b60551219e181544865e63151219758c544863f6454d218f191534867b6054d219e181534863e6414d218f590534863e64d41218f593504865e63d41219758f504865e63d50219758f540867a60d50219e583540863d65950218f982540863c60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c2197982530871e5454c21c7551530865c6054c218f990530863d6414c219798c530867a6014c219e580530863e64948218f592520865e63948219758e520863d65d0821c794f420871d53d08218fd95420871e5350821c754d420865d65cc821c7953320871d54cc82197d95320871e544c821c7551320878d424c8219bd9521086776548421e950921087c53248421ce95250087395494021d694e50087595394021ced9250087386494021d6d8e50087586394021ced0a50087394294021d6cca500875932940218fd91500863c645402197d8d500865c6354021ce95150087395454021d694d50087595354021ced9150087386454021d6d8d50087586354021ced0950087394254021d6cc950087593254021dc885500877121540219758a53d025f6254f409798e52d025d6394b40c794f42d031d53d0b40cb54b42d031e5350b40c754d42d025f65ccb409759732d025f654cb409759532d02d8604cb40c794d439025e6394a409758e529029e6390a40a758e429032d5250a40a798c429029d6310a409798e519025d6394640a7d8d419029c6350640cd945419029e6310640a758c419029e63d0240a758f40902b661d4e40ad58753902ba60d4
  | 5 => 0x5350a9f6354542a718d5150abb6054542ae1815150a9e6314542a758c5150b355114542a798f5050a9d63d4142a7d8d5050a9c6354142add855050ab46154142979825310a5c6054c42c794f4210b1d53d08428fd954210b1e5350842c754d4210a6f6550842cb9514210a5f63540429718d5010a7661153329d58454ccb1c5450f32c755043cca3f64547328f19151cca3f64543328f19150ccacd62d5332c755054ccacd6215332b598454ccad56115332a798342ccb8f6250b32a718142cca9f6454732a719151cca9e6414732a759051ccb555114732a799350cca9d64d4332b598750ccad561d4332c7d0a50ccb1d4294332a7d9150cca9c64543328f982548ca3c6055232c7953328cb1d54cca328fd91508ca3c64542329dd85544ca7461551329ed81544ca78605513297997434ca5c6550d32c7151434cb1d5410d32a7992324ca9d648c9328f990514ca3d64145328f993504ca3d64d4132b358a544cacf6255132b5d85544cad46155132b6d81544cad86055132c7550544cb8f52d0932a7983424ca5e6590932a7592424cb8f6250932e3d49424ca9c605093297994424ca9e6410932a7d91514ca9c6454532b6d81514cad86054532a7990514ca9d6414532d5544514ca9e64d4132a7593504ca9f6454132a7191504cad76154132b5185504cb1f4214132c7508504ca5e63d50328f596540ca3e60950328f181540ca3e64150329798c540ca3e64948328f592520ca3d65d0832c794f420ca3f6550832c794d420cb1e54cc832c7553320ca5f654c832c7951320cb1d544c8329bd95320cb4e534c8328fd91500ca3c64540329798e52d065d6394b41cb54b42d074e524cb41d354932d065f63543419718d50d065e6394a419758e529072d5250a4197d8d509065c63542419758b535065e60d4d4197588535065e6014d418f997435071c53d0d41c714d435065e63149419758c525071f53d0941c714f425071f5350941c714d425072f5250941ad185425065e65cc94197197325065e654c94197195325071c53905419798f505065d63d41419758a531065e6094c4197d89531065c6054c418f596431071d5390c41c754c431065e63948419758e521071e53d0841c754f421072d52d0841ad587421071e5350841c754d421065f65cc84197597321065f654c84197595321071d53d04418fd95411069c6350441c754d4110677655044197d8d501065c63540419b98854cc66d6215331c715143cc63e6494b318f59252cc72e5250b31cb54942cc74d52ccb318fd9150cc63c64543319e983548c67960d5231c7d50438c63e6494a318f592528c74d524ca318fd91508c63c64542318f58b544c63e60d51318f992544c65f63551318f994544c71d63151318f588544c63e601513197996434c71c5490d3197195434c71c5450d318
  | 6 => 0x6488f87496019f1d98ca90a0328001cf8e6270a04a1291802e800284800000000024a3985d80000020989609785700010da5da4e0b196700027f00000000028518980000021a8002039fa8fb903a64052a9e23329927913d8da8231ec167a80a811a21ca9b580000000000000a96284880000a04693d0162769541849040001c89fe9c085309c8001c28930000ff096815a6b80f97700000023b1e69f629c14a965a9a006002008010000030100200100100a004040020180000200f008000028000060280580001801c0000400000c008020020040680100600c0a8020080240480203400c0380100e0180000201600000001010018078050000040100300200c0080000400802006000008008000000000080000c000020000060000300100401c00803002000058010000000000200601c0a80000000c070000000040080d018028020040040200482300c028008000040580001400000c0401501c00401803030004018030020000000b03e004060020000080600000c0000000800401800805000000000030200100000e00c05000004002000010010000500000400a00403800008020028000040700981b0060040203c00e0140000100a00c00000032010000070220040180003001c0000002e0080100400801400000002000040010080080000500c0180800300001402004000004000010000000a8020060200280000a008000020020000480000404c0000b0080180000b0100001100000000001806002020000050000240d0000040200000b0000280300f01e03c0a8060000a801017000004020090000a801002006038010020000400480602003c0001300600c0100204a0240380002e07400003000030030050060200000201600000011010000030030000080381a00a00c00001000008008020060400002200000006801042028038010000040000000002000800000004028000720200300000205000004008000018000240080180f00403c008000000000080800400c0700e002020010000100040200a0240240000500200401001002008008090000000900e00c0140c82401600c0000001201e9d6490c438fd954310e5f6550c43a7d954310f1f6550c43a7d894310e9c6150c43a71814310f1d4354843c750d5110f1d4394043c754c43d0a5f63547429718d51d0a5f63543429718d50d0aad62d4f42c754c53d0aad6214f42ad98453d0ab56114f42a7d8d51d0a9c6354742a798c51d0a9d6314742cd54451d0a9e63d4342a758f50d0ab661d4342ad58750d0a9f6354342a718d50d0a5e6094e42971815390b1e53d0a42c754f4290a5f63542429718d5090b1c5350d42a798e4250a9d63909429798c5150a5d63145429798f5050a5d63d4142ab58a5350aaf6254d42add855350ab46154d42aed815350ab86054d42c754c
  | 7 => 0xb24f87c1e885804c00000010b00013e11da1c8000000000001ba00000000b80000003824800000000019c00029d27222e99d07380015b15b80000000009f256800204157277a4990113321129d89904919ca2100014c80009d1ca037a1784b9a680021b1318cb1698a29cc2538858411d792400008886d1f409197da5800893f90a8001dd8018a78d700000027a1d103e88d9c21f002824480b26715c2228001f3a391f30002740b480026295780028d1c8228180000226a828b10e281aa94a41a3500026a947817a5c11e8d10690001300b587a99807f90295294c23000013c8279b116ba0593e8001280000002312739958f524223081009415a0000000e080010ca7e00000000000000026a0df25914680000018304580000002619300001e8000891509278e68750000000000f2a488001e98c300013c1ac1ff9cb1db0340000001e900017006a1d624900019880000000000012f9a924780000001da620002860ba8400002218001ba9131559d680000010300027d252213a788a110b84f1a3a9626f20192120b80c917298a089560ea0418758f71ed2598951642530ae80000000017c8dc80000025118690580026794a08a13f0c09fa04b0e717d00000004603f1e403224728ba24886a4c9b3959025a919018000a308200008c10205901b0010000801d88d48001d00448000db92480000000017ea9502212d0e314b21187985980018a1f89bd9978002010078000000198000000001588de80000026080000005a00000021d0000001a58958000001f714b8f202c0000000001d1a9f9b6a222871151680c52772239949a800004fa6503c9b7a638f30d99a88000000a02270002898000000ee8a880026da6900011a27aa0024a1fc8ed297805a6111b00000602a0ad04285c9aa87f1b323689209e96f162233a65800000047a2c0d59ed9340cb8b32172830b713a85d09a9ad8bf86b97b25ba35a63029a7d83609082ba021d80c39888cc9051a30c607b0af8ac0fd24624a8f10fc9ee0d81880b20c7a920ca29b80d10f8c817f92a0000760030241f5a180641fd08780028c8000000000d50000b786b0618bd91215c9750e4a9806623d1a714813293b8000000000000000002230000002411be8000c11d22878bc8001ea98d00028400028fa5489d9418000420e581e1c980000099b85527c23808520e9b80000001a497986aa3e80000000020a06d8000840000001cb94f9810000f18002140dd0b927ba8e8318040000b98001c180019b0aa0001322208000efa2c8648988000000000a9048176a1693796195fa0091798522623c9189550001740002901441459ae1910001a00001878be0190e189b9b20651a29eb982a2a0dc2278000d60001710a7232a191c40001bb2710002728540000000cda1b90d08998e8000b08781788f98000002
  | 8 => 0x9fd94f0cd0188db1e198f96a00000000000000003307a11600017a80005f1d40ee1261c91f50000ec80024680023a0000b685b81700727b02d15126b18b22b1820f0078a0826c8c901a26fa5e1c11292798aa8f41e202082c87e1ac85c24f16fa8900000014500000009000000004ca99a3a84a0000548600fb04500010992c0ea9548a99e48fd80000000024b0849bf00e0000a60000608b416c8000f89990001840e780000028f24e9e598580029080025b0be84312b26e83903c07d8002371818f61972258cea540a385119eaa00c70bb2201088000f088e000281a7c8000000a681216d8500659400d911481080000004e00f16684d8000000778000000001bc9e78c6861000000153066a7511002e20788080009980021c00008c8e38e800020c19a1b48c491b98ca8386203b1660558d2a430f789483396480006ca589d48000000000200729192199c48d893107080028a00c2148c980000000023d9780002858001d50b50000001630218a09ad16898a80000002107d0000fa05a8509b60001ce2730000000ef252a1f1728000000a40000001650000001941c301692da5d0b805b00000003a8350110bd0001f180020d03d15d95a88d1f69231430000001361609348141580838001c600000000025ea9e9109129fb8000980000128da0dd8f48e215f2560000731b18000000fc1b900026698f0a48cc1141bc1732030d329c80000020925f1370ae00000000000024091c0002928f392a80020e1e70048348a229714105f99203e14910082919680d82f8001998560c420b00021f8002701568052459288c28000000000d194e180a3e17492180028026d1ff00025a0ce2680001b411a82d9d280388a8fe8309860000828698e026c0000239cd1ce80000016b000081a4d17ba5594992e1b89db922851a93800237a2e27599a9168831e080022f1cc835a2a8fe0499918000ed8001c392ba241e306f1c69f98002029090001e280021085783021a0021691cd8eb1b0a251350000251a080011e0001fe1c5009a821070871dfa5fa348228928588000000000e123fa189d310810f0cf00009723c2388001202100000001f80002318000e88000001c5a06a9f1da043a150000150001e600800007901d29324b80000000000000e9470aba8d80000028a95d26980002b0000001599a400010e9368740c001c97a122000104a9100000000021da0f8311429610388eba8c1ef9dc0000a18ac8130b287b8f58000000b39ae9079f20812578001d08b610616e1f280014d08b8c1a2da3b94605e00006280019016c0002158138bc10e20f08ea4c0271e122b9938001b5229053a5700000006312716d0710ab1f095e243a131cf13386c1409a982f05ea958001ea0f6a881ef1c000018c0b00001bd09a0001d38a580000017794380016e8000000001e
  | 9 => 0xb89bf86e0de28e0ba17f06890c14e814a718d783a1e01420701fc1b999512516382aa3f19086e9d906f9dc9ec9ab00009e19fa5a93919e1af9c70cf9e51891a12689489aa0000001358000002320001de0000000002749110000000000000000000000860d00000000a500000000000025c87c80000000011995391d2450001928001870939b002884d261a0c8000e420501c0180442518000001761258768d08880720ff92089127609c00017913b25098e0e984096a86711f8770000fa97193097e29a80000022f8df80000024280000017580020a80000000001f86809f80000003689b1139299709d5a7e8001f126e1f48d412f1738000e50269af04ea2980001f0000e901b8000001a78639960679502501389002550001381dd1a19e80d398383f8c883ba0d8f914d92c8718a817c24d91f0119448bf056a6620615188b18da341b71de9e387ea1611c9239068000f80001c78001fb1158ec0c200000018b8000002600000af0002942969a60000bba8b2121b28000001df0068ad8d20370001be1d70c58d699da4011193a00021e1ab9f9236286a0705222895221e9399daa2d00004727800927f8001a51269bba441ee839a9b15e80284a9f788f03d92e972288
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x762c66b44a62006cc6380074b2060094c42ea80000000a00003c54ae46081e829ebc0040003a000004d21ac2445e6a00009c427a00207000000022dc000012000096acbaa02a3618341660008c7e0000b6a4dea6ce90aa98d6808e005000248a4c688856525a6484c07210c84eccdacaa20000000000301c6e2628780c140000b848d8007cd43e9a86b00e00d0589200be5c023207130900020b04000005001b1608090204020403000412080a010c01000005020704000000a1ee4a1aa421d187050e5010f0aa9ac229e858558d5114742a28e2a98a6a15187054c5350a8a39aa228a854c1c15114542a2ae22a287996155458454ccb0ab22a228e65451c55410d32a30e0aa0869951471550544ca8c382a82a265451d15114532aa0e0a88a29951870508504cb0a298c2a12838554d61d0841a1ae529a8420c58705953210686b90a8a1e63469c35410e31c28a830a6498c3870595420c70aaa2c399063435ca544c831838ecaa26218f09424c95008790a1242a8043d04c92154021a1ae529a85a061463945419028b38ea729c81459cf5194640c92a43026420615635444110306a9ac4298818554d6114c40930e0b1ca420629521813210384a96c09908183548604c840e12a4302642068a52181321030ca90c099081a2548604c840c12a4302642049a70d8d511030ab1aa22888189589511444085ae432a62204987058f2110306b1aa590881435ca544cb30a2ce3aa0871861464945318c28b38ea92a461459d35194630a1ae42a2861851571151430c314a90c0a106185591510c430c1aa8b10a81861554584540c24c382c929061925486050830e12a5b02841860d52181420c384a90c0a1061a29486050830c32a4302841868952181420c304a90c0a1061269c36454430c2ac8a88a21864562544510c226b90caa0861261c164c8430c1ac8a96421860d62548400c30c298c0a144186150604ca20c1ea6b10811060f54588308830c298c0a1241431d5424c920c18caa12649058870509324830c2a0c099241a2508604c920a60e0a10a290705424c851482a83826428a418354d6210020c4ac4a88801060d545883008322b12a218041465d4400c020c32ca2006010589721003008344b108018041c4544400c020a1ae529a858861a5318142c4286b94a89962186950604cb10e10a420060885627588620443503108088021b01883044010
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x801ca3000c020920004000820a088058d52c8440a088059152c8430b00805093214520d01421c13214520c09655c8400c020c0975588400c020d0172544400c020e0162544400c020a098294c6050b10a0982950604cb10
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
  | 6 => packedAt s3K6 (864+((h/16+packedAt s3K6 (768+(h % 16)*6) 6) % 58)*7) 7
  | 5 => packedAt s3K5 (31188+((h/339+packedAt s3K5 (27459+(h % 339)*11) 11) % 1477)*11) 11
  | 4 => packedAt s3K4 (56038+((h/448+packedAt s3K4 (51110+(h % 448)*11) 11) % 1776)*12) 12
  | 3 => packedAt s3K3 (5784+((h/37+packedAt s3K3 (5488+(h % 37)*8) 8) % 148)*8) 8
  | 2 => packedAt s3K2 (615+((h/3+packedAt s3K2 (600+(h % 3)*5) 5) % 17)*5) 5
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
end PEqualNP.Outside.L_meta_36785
namespace PEqualNP.Outside.L_meta_36785
open PEqualNP.Outside.L_meta_36785.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2a4402a2e205804018d1f0000000007402d1825296000002b1c0cd941aa531000012120a6009c00282003c011802688782321d3a8000002c42000c000060418012000013810080ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x146800705684306e9a7202440a9ebc9460a490482246a2000034408a58acc0740c001c0e82ba9c800086267800968e628850000052b0c46c2854aa104a122ca0ae4c1a1636925a2a5c76423208b20698640038a6b43e4e00003ab88c66a8c23c04207e181eb67c6a00005e0000002400007a00be00002e121cba9000cc8b0a240501218016024840068041000080082043c0000f6e5210edaa421cf947429eaa4855e5390abaa7215dd4542ba28a85af5250b6ea2a14f14542da28a85345150a7ca8215794c42aea98859f42ccb3a85994f952329eaa4655d538cb5a85196b50932e7a92659f424cb9c84996750932e6a12658d424ca7ca8194f55032af298653d529073e6520e74ca419f28c833d521073e6420e74c8419f28883b6511067ca998cf55331b7296636d52cc67ea898cf151319f2a6433d54c86bca790d754f21da20e433f5488678a910f34ca219faa2433c544867ca810cf55021af298435d530879a6410ed10421bd280437950086eca3205d54640afa9a815c535027ea8984f151309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f55320af29e415d53c839a6590734c9209f2a0413d54082bca6105754c20bb2884175510836883884f952109eaa4213f5444278a88857d4d10ae29a216f52442d8a4886d10510
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x4463524000005000020002c000c0093c000000e00000701314000000000000000020a1000000000000010000000000000c00000000000000800202946150b32a9185428caa46150932a3592424ca946150932b1185424cb876150932a3185424cb846150932a1185424cb0d524c841c3d51328870d544c8218d59441087853210421d24c9500873041540219358853502346155320c355132c83245210510
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x1002000605654c8410878099082a8043411c5544cb20
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | 2 => packedAt s4K2 (i*49) 49
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (841+((h/15+packedAt s4K5 (736+(h % 15)*7) 7) % 67)*7) 7
  | 4 => packedAt s4K4 (2904+((h/33+packedAt s4K4 (2673+(h % 33)*7) 7) % 119)*8) 8
  | 3 => packedAt s4K3 (847+((h/7+packedAt s4K3 (798+(h % 7)*7) 7) % 79)*6) 6
  | 2 => packedAt s4K2 (150+((h/1+packedAt s4K2 (147+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x3fff07ffffc3e0ff87f87fe1fffe07d19f3f3
  | 1 => 0xfc1fff81f0ffc3f0ff87f87fe1c0ff82e67d9c
  | 2 => 0xffe1fffe00ffffff0007ff8ffe00ffff078e1f
  | 3 => 0x1ffffff0003fffff8000fffff0003f80fe0
  | 5 => 0xfffe0000000003fffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x4840111440204002280980920252212808b0b1
  | 1 => 0x1944230c814804505882882620864b08625594
  | 2 => 0x208944202a9222a50444550954089453050a0a
  | 3 => 0xb2958849281aab399550440d992c0613b00f40
  | 5 => 0xc3190e71cce333cee667664110301863dfe000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeee8eee8eae0eae0eee8eee8eae0eae0eee8eee8eae0eae0eee8eee8eae0eae0eee8eee8eae0eae0eee8eee8eae0eae0eee8eee8eae0eae0eee8eee8eae0eae0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36785
namespace PEqualNP.Outside.L_meta_36785
open PEqualNP.Outside.L_meta_36785.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x7220002c4000214240011a52000153c58998142d12800190851c98e0c46a801b00ac090320cea55a3c00d1090fa71200b811a021d0041000012c30c7ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x3c0000015968a17834c400000000cc007c00893904544c000000152800000071304920000000b00000000000000084017000ece430000000014d0d8824000964000148000000000001440000c80114a40000000000000184006c00002c00015400d8000045417d2480000000000000000000000094009cb40050008c0040f0000000e00010a87400213468c064793c580000ac0000000000180000011c00bc010800e80000000000000000f40000b800900000005c00000000f800000001600000d56c0c6180dd1950fc00000000002801015c39112c00017400000098d0000004001c0000000000000000020a00060002000000000a0202020c000202020600080e02096e5210edaa421cf947429eaa4855e5390abaa7215dd4542ba28a85af5250b6ea2a14f14542da28a85345150a7ca8215794c42aea98859f42ccb3a85994f952329eaa4655d538cb5a85196b50932e7a92659f424cb9c84996750932e6a12658d424ca7ca8194f55032af298653d529073e6520e74ca419f28c833d521073e6420e74c8419f28883b6511067ca998cf55331b7296636d52cc67ea898cf151319f2a6433d54c86bca790d754f21da20e433f5488678a910f34ca219faa2433c544867ca810cf55021af298435d530879a6410ed10421bd280437950086eca3205d54640afa9a815c535027ea8984f151309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f55320af29e415d53c839a6590734c9209f2a0413d54082bca6105754c20bb2884175510836883884f952109eaa4213f5444278a88857d4d10ae29a216f52442d8a4886d10510
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x50001800e000a000062927a499000401c3005800008886808000800401800800e946150b32a9185428caa46150932a3592424ca946150932b1185424cb876150932a3185424cb846150932a1185424cb0d524c841c3d51328870d544c8218d59441087853210421d24c9500873041540219358853502346155320c355132c83245210510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x200080605654c8410878099082a8043411c5544cb20
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 5 => packedAt s5K5 (826+((h/15+packedAt s5K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s5K4 (2937+((h/33+packedAt s5K4 (2673+(h % 33)*8) 8) % 227)*8) 8
  | 3 => packedAt s5K3 (840+((h/7+packedAt s5K3 (798+(h % 7)*6) 6) % 36)*6) 6
  | 2 => packedAt s5K2 (150+((h/1+packedAt s5K2 (147+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3fff07ffffc3e0ff87f87fe1fffe07d19f3f3
  | 1 => 0xfc1fff81f0ffc3f0ff87f87fe1c0ff82e67d9c
  | 2 => 0xffe1fffe00ffffff0007ff8ffe00ffff078e1f
  | 3 => 0x1ffffff0003fffff8000fffff0003f80fe0
  | 4 => 0xfffe0000000003fffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4840111440204002280980920252212808b0b1
  | 1 => 0x1944230c814804505882882620864b08625594
  | 2 => 0x208944202a9222a50444550954089453050a0a
  | 3 => 0xb2958849281aab399550440d992c0613b00f40
  | 4 => 0xc3190e71cce333cee667664110301863dfe000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeee8eae0eee8eae0eee8eae0eee8eae0eee8eae0eee8eae0eee8eae0eee8eae0eee8eae0eee8eae0eee8eae0eee8eae0eee8eae0eee8eae0eee8eae0eee8eae0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36785
namespace PEqualNP.Outside.L_meta_36785
open PEqualNP.Outside.L_meta_36785.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xc401c58100320c76b809d10f20107cd9201141568d4aab86e01e4b9841751156ac4d8030b542800000494c7349e64033bb0a550b8a1ab07c88c4700d951a009a40000e80490c042070408080000028d1e280010218685000007fe54007f55007fc54017fd0c05fe43017f50c05fc4300ffd0803bf4200ff90803fd4200ef50803fc4200ffcc803df3200ff8c803fd3200f74c803fc3201ffd0401fe41007f50407fc41017fcc405fe31017f4c405fc3100ffc8403fe2100ff48403fc2101ffd0001fe40007f50007fc40017fcc005fe30017f4c005fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1c2002bf18e10067fe8708033fe4384019fea1c200cff10e1003ffec50801eff628400fff3142001bf98a1003ffac50801efd628400ffe3142001bf18a1003ffe850801fbf428400fff2142007ff50a1003f7a850801ffc428400fff9942007f7cca1003ffc650801ffd328400fee9942007ff0ca1004dfac308037ff4184001ff20c2000ff5061006ff88308033ff3184019ff18c200cff4c610067f8630801fff218400fff10c2007ff4861003ff84308012fe608401bffa042000ff90210007fa8108037fc4084019ff984200cff8c210067fa6108033fc308400fff9042007ff8821003ff4410801ffd208400ffc9042007ff08210007fe2108003f71084001fd8842000ffd9110005fec888003bf64440015fb22200bff9911001dfcc888003fd64440017eb22200bff1911001df8c888003bc64440075e322200bff95110007faa88802ffc5444015ffb1a200abfd8d10007bec688002df6344015ff31a2002bf98d10057fac68802afd6344015fe31a2002bf18d10057b8c68800adc6344015ffa1a200aff90d10057fa868802bfc4344013ffb122009bfd8910007dec488002ef6244013ff3122001bf9891004ffac488026fd6244013fe3122001bf1891004fd8c488006ec6244013ffa122009efd091004ffc8488027fd4244013dea122009ff1091004ffe6488027df3244013ff1922009ff4c91004fba6488027fc3244017ffa0a2000ff90510007fa828802ffc4144015ff98a200aff8c510057ec628802bfd3144015fa98a200aff0c51004ffe4288027fe2144013fb10a2009ff4851004fea4288027fc2144017ffa022000ff90110007fa808802ffc4044015ff982200aff8c110057fa608802bfc3044013ff9022009ff8811004ff44088027fd2044013fc9022009ff08110007fe2088003fb1044001ff0822000fd84110007fec808002ff640400dff3202003bf99010007fac808002fd640400dfe3202003bf19010037fca808003fd540400dfe2a02005ffd8c1002dfec608017fe63040057f3182005ff58c1002dfac608017fc63040057e3182005ffd0c1002ffc8608017fd430400bfe2182004ffd8810025fec408013fe62040037f3102004ff58810025fac408013fc62040037e3102004ffd08100277e8408013fe4204009fea102004ef50810027f88408013ff3204009ef9902004ff8c810027fa6408013dd3204009fe1902008bf98410037fe8208003fe4104001fea082006ff1041002ffe6208017fe310400bfe9882005ff0c410027fe4208013fe2104009fe9082004ff0841003dfcc00801bff4004001ff2002000ff50010037f88008017ff300400bff1802005ff4c01002ff86008013ff2004009ff1002004ff48010027f84008003ff1004001fb8802000ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0x3fe5190001fea8c8016ff1464001ffe832000ffe4190001df20c8003ff5064001ff8832000fbc419002bff98c8015ff8c6400affa6320057fc3190029ff90c8014ff886400a7fa4320053fc21900077f3048016ffd4240007fca12005bfc5090007ffa048003efd024001ff6812000ffc4090007fc2048015ffcc2400affc6120057fd309002bfe1848014ffc82400a7fc4120053fd2090029fe1048000ffd9540005fecaa004bfe65500277f32a8000ff59540005facaa004bfc65500277e32a8003bfd914001ffea8a000ffe5450007feaa28003ff1514008ffec6a0046ff6350023ff31a8002bf98d4008ffac6a0046fd6350023fe31a8002bf18d4008ffea6a0047fe5350023fea9a8011ff14d4001ffe86a000fbf4350007ff21a8003ff50d4008f7a86a000ffc4350021ffb128010bfd8940087fcc4a0006fe6250021feb128010bf58940087f8c4a0006fc6250021ffa928010dfd4940087fca4a0043fd5250021bea928010ff1494001ffe84a000fbf4250007ff2128003ff509400877a84a000ffc4250021ff9928010f7cc940087fc64a0043fd3250021ee9928010ff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a0002fc6150025ffa8a8000ff94540007faa2a004bfc5150007ffa0a8003ff9054001ffa82a000ffc4150023ff98a8011ff8c54008ffa62a0047fc3150021ff90a8010ff88540087fa42a0043fc21500077fb028012ffd4140007fca0a0003fd5050025fe2828003ffd014001ff680a000ffe4050001df2028003ff1014001f7880a000ff84050023ff9828011ff8c14008ffa60a0047fc3050021ff9028010ff88140087fa40a0043fc2050001ffb262000bfd931007ffcc98800efe64c4001feb262000bf5931007ff8c98800efc64c401fff2a62000ff5531007ff8a98803bff63c401d7fb1e200eff98f10015fcc78803bfd63c401d7eb1e200eff18f10015f8c78803bff43c401dff21e200eff50f10077f88788023ff62c40117fb162008ff98b1000dfcc588023fd62c40117eb162008ff18b1000df8c588023ff42c4011dfa162008ff90b10047fa8588023bd42c4011fe2162008ffccb10047be6588023fe32c4011fe9962008f74cb10047f8658803fff41c4001ff20e2000ff5071007ff8838803bff31c401dff18e200efd8c710077fa638803bf531c401dfe18e2008ffc8710047fc4388023f621c4011fe90e2008fd48710047f8438803fff40c4001ff2062000ff5031007ff8818803bff30c401dff186200eff4c310077f86188023ff20c4011ff1062008ff48310047f84188003ff64840017fb24200dff9921001dfcc908003fd64840017eb24200dff1921001df8c908037fe5484001feaa4200dff15210067fec708032ff6384019ff31c2002bf98e10067fac708032fd6384019fe3
  | 2 => 0x410d7f8c520806fc6290435ffa94821adfd4a410d7fca52086bfd5290435bea94821aff14a4101ffe852080fbf4290407ff2148203ff50a410d77a852080ffc4290435ff994821af7cca410d7fc652086bfd3290435ee994821aff0ca4101dfcc320873ff5190401ff28c821cff1464101ffe832080fbf4190407fba0c8203ff1064101fe8832086fff3190437ff18c821bff4c6410dff8632086bff2190435ff10c821aff486410d7f84320803ff6090401ff3048200bf98241007fac120802fd6090401fe304821cffd42410e7f8a12080fff4090407fe2048203ef102410dffe612086ffe3090437fe984821bff0c2410d7fe412086bfe2090435fe904821aff08241007fecaa0802ff6550401bfb2a82009fd95410cffccaa084efe6550401feb2a8200bf595410cff8caa084efc6550401be32a82139f1954101dfec8a080fff5450407ff2a28203ef9514101ffaa8a0803bd5450407fe2a28218ffd8d410c5fec6a0863fe63504057f31a8218ff58d410c5fac6a0863fc63504057e31a8218ffd4d410c7fca6a0863fd5350431fe29a8203ffd0d4101ffc86a080ffd4350407fe21a8217ffd89410bdfec4a085ffe62504037f3128217ff589410bdfac4a085ffc62504037e3128217ffd49410befea4a085ffe525042ffea928217df549410bff8a4a080fff4250407dfa128203ff9094101ffa84a085fbd4250407fe2128217ffcc9410bfbe64a085ffe325042ffe9928217f74c9410bff864a080eff6150433ffa8a8200ff94541007faa2a0867fc5150407ffa0a8203fdd054101ffc82a0803be4150407fe20a8203ef1054101fe882a0863ff3150431ff18a8218ff4c5410c7f862a085fff215042fff10a8217ff485410bff842a0803ff60504017fb028200ff98141007fac0a0803fc60504017e3028219ffd41410cff8a0a080fff4050407fe2028218ffcc1410c7fc60a0863fd3050431fe1828217ffc81410bffc40a085ffd205042ffe1028200ffd9640005fecb2005bfe65900277f32c8000ff59640005facb2005bfc65900277e32c8003bf5924001ffea92000ffe5490007df2a48003ff552400077aa92000ffc549002bffb1c8015bfd8e400affcc72000afe639002bfeb1c8015bf58e400aff8c72000afc639002bffa9c8015ff94e400affaa720057fc5390007ffa1c8003ff90e400af7c872000ffd4390007fe21c8003ef10e400a7fec520052ff6290029ff3148001bf98a400a7fac520052fd6290029fe3148001bf18a400a7fea5200537f5290029ff2948014ff54a400a6faa520053fc5290007ffa148003efd0a4001ffc852000ffd4290029dea148003ff10a400a7fe6520053df3290029ff1948014ff4ca400a7ba6520053fc3290001ffb0c8000ff98640005fcc320003fd61900017eb0c8000ff186400b7fea32000
  | 3 => 0x4f6210001681fe3300000031a39403000000be8000001420000020a32c0000000041c00000000000000000000001201200200000c00000200000600000400200600400200a00400200000400000a00201000600600600000000200000400600400a00000000000200000601000200600400400600400400000400000001200200200400401400000401400000000000000600800000a00000400000200400000000000800000000000a00000400000000000200000400400200400000200000000000000000000000000000000800200400200000400400400000000800200400200200400200200000000000400400200600000000000000200000000000401400000000200000200000200000200000000e00000000a00000800000000000000000200800000e00800000200000200000000000200000400400000000200800600000200000200200000000000200000000000c00400000600400000001000200000001000200200800000000400400000000600000000000000800000000000000000000200000000400000400000400000201000600000000000200000800000400000000000000200000000a00000200200000400000200800000000600400200000400a00800200000200000000000000000000000200600800000000000a00400401200000a00000a00400600003bfd915401ffca8aa00f7e5455007fe2a2a803ef1515401e78a8aa07bff635503d7fb1aa81eff98d54015fcc6aa07bfd635503d7eb1aa81eff18d54015f8c6aa00fff4355007dfa1aa803ff90d5401ffa86aa07bbd4355007fe21aa81dffd89540edfec4aa077fe62550037f312a81dff589540edfac4aa077fc62550037e312a803ffd095401f7e84aa00ffe4255007fea12a81def5095401ff884aa077ff325503bef992a81dff8c9540effa64aa077dd325503bfe192a800ffd8554005fec2aa003fe6155001feb0aa800ff18554005f8c2aa00fff4155007dfa0aa803ff105540f7fe62aa07bfe315503dfe98aa81eff0c5540effe42aa077fe215503bfe90aa81dff08554007fec0aa002ff6055001ff302a800ff58154007f8c0aa002fc6055007ffa02a803ff1015401f7880aa07bff305503dff182a81eff4c1540f7f860aa077ff205503bff102a81dff481540eff840aa003ff65904017fb2c821cff9964109dfccb20803fd65904017eb2c821cff1964109df8cb2080efd6490407ffaa4821cefd524101ffca92080ffd5490407fe2a48203ef152410dffec72086eff6390437ff31c8202bf98e410dffac72086efd6390437fe31c8202bf18e410dffea72086ffe5390437fea9c821bff14e4101ffe872080fbf4390407ff21c8203ff50e410df7a872080ffc4390435ffb14821abfd8a410d7fcc520806fe6290435feb14821abf58a
  | 4 => 0x1310001887f0a00047783f8053dc001309dd2980014280038a000e0000000000000b9000040001410080000003842c000000000004d0002a64da00000000000000000000000001b40044e0000012300000000246000001260000000000018d8002500000025d11c0000000000034800000000000000008bc00000000000dc80000000000000494544000be0e48c89f8000000000000044000000230000000c80000005900000000032176800000000001d20007f800074a2aa25120000000000000055469474c77880bf077800000000b60ca8d97b40000000000121875b42b14a1a7819b234b7afaa5c5607d8c18dea48e405260e5b4070cbd867ccd49d91aeb231b0d10000000000026e0cc0000015400000161000314000001110001700000000000000000a1800029000b48001c9000108001823de36a00000000000dc00033c000698000000000000000000000000000000001bb00000017a2808f3b0000002ee0000000051a00000000000001281070000011b80000000000000000000000f100000000000428001570000f4b1c428facfab5d188000001cc0000000000000000000000511f900086cb29d300000172800000734648000000000000044a000000662040849a9e900000000000000000000000ed000db80000000173cbc2485e0a79a71a83321b0a28825b836035000001755dc0004be12000000789594000001c174591458550000c13cea60002a3000000001ab000b0000121000b897d8002c426a800c6000000afaa5000000000f90000010e0a30000000004e000c237c4000000000008a0ee0000000000000000000000076000a500000000000000000001690003340000033000000000000000fc0000001f8244000004bced09f20a2d8001ae0000000029d000000000f70d600015c00000000001f5000000fe000000000091a4000000a9a96180000000000be9000000000000000000000000000005cc00000000000000ce23c578908df00004e0002400000099c5040000010e00000000292000000b61356a88914c000ea8000000009900007800174e5d2fe001548000009145988780092d460db0000a00000056400000000000272000000000015c81c818000c08001b300000000000b8c001eb00007e002f68004d2000004920006e8f88004940029b000000000000890000000000023068032000358000000000000000000000000000000000002ea00000000000000000002040000000000000000000000000000000ea0000b2000000948680002c1be730000d2000000cc800000000000000000014200000000115a3500000075a4f03e0002c8002ec000914f500000000000000046001aa312a809693d5624654f0b150e0007980006b0007bc003ae000000000ec000000000000012faa202a25c000000000000000
  | 5 => 0x14e60000000000000000000000739790000000016d000000000000301d945c00000000744d19f08003b77b0000006e9820f648e73c002b75eb000c50001cf000000000000000000000066800257292b44e18000a2000000000007b1810000f800000000000268898000000000022d2582a4f200037804200000000001560003fa0000027c000c20710003b00000012a000000002620000012c800000000000000009b00007807683c00000000000000004dc0000025b11e0000018500000000050000b50000001ce5a8000ce00000000000000b380000026cb3539000150000498000000002f000000000001c7000000068000003805b83107126cc317529442d660005de10cf8ac20000000580000000007c0000000000000000c1a0009d35e000002a1418864900005be7409580023e00087000000000ffa760001260b000000000001b600000104000000000000000007a00000025000000000000bc4e2000000888001338d400000000556000000000000000005400000040952000000000ee17e000001730bb000000ac000240001384f2000845e6092000000b580072ca42de2610004101b000000002696020008c00000000000000000000000200ca0000000004a000000000000000000022b8fc000005d6000ae800472848000000003e8001b40000015f8000000004a80004f000002d90007dc00000000000002dd0000000002a800950888000002216801e80000022c288c600096d1d000000000000000002e0002fa7ec000081b40010a94d044509578ba00046c000000009c17f0000002d0000003c264c892050000000000006f00025958bc60000000020f3d0de800000000000680000009810a9d500000000000410000eb8007500000000000000000000000000005b05402d0000000005e80000000000000000000002c100000000000000500000b25930014c80000000000000000000001ea0008e000000000000000000000000011680000000026000458002660000000000054e00026099000000002b300000000000000001322bd0000008526b000000001578000012b0190000007cc000000010c00005368000000000000001840009d48fc7b000000000000000000f0000006d4000fd11c000000000004c77c00000016e0000004600169800000000e51f007c000002974b00000009228c5d059eee0000000000000000000000000000000000000000025a3ac0000000000080c254000880e92202a0005e4000000009453d0000009a000000000804000d55fa81c000005ac00000000000404002880006480000023c00000000000b200005800000000000113290000004220000eaba0002608e0002782c02b29011660c2d5c21da36f41800000000c71721e4000732935f34e9408ae10051400000165c1800291000b1e00
  | 6 => 0x2f780000000000000000000000008820000000000000000382000002233660017a0000000000000000000000000000286cda530000000c0000000002980047c6a15c1060009354a23d000898000000000000015e4d41b8998ab0000000003d000000878000000004cc00000000000000000000000a2c0000620860000000021710e4464b2ad00056d450390001c40019756a00000000000000be0d93184d6bd0e41b0452b18000004986380043e42782512d8cc00000000009bc000000005f800000516000000003c03c04f50c000b2c0000035aad94026500000000248000000000005d2001410000008cc0000000000090c6b800b70002060000000000000000000000000000000002ae00000000181000000c30000000000000027e0000049d000000000f100051e290006c0fa0ee80004d290000004682e8ce9d10014a98b0005c0159a251e0003e800000000a20b50000011d8000000000000000e0000009b8008a9270000e83713f93e5e6118880001318092e000000878dd4000008857081453e598002b019439a0018f00038d520000000000000000000000103097000228000ea0013a2f760abd489e9c000000000005c83a435457000000b38de00032c0000021200036ef927682c338e817f000ab0af07e00000000000000868000005651a0c2800270fd00045c000001478000015d81c5b3000001881c261c001b25fe000000000000000009e43a024000000000008a0004ee00127c00373b28000128f35700002d000aa03c8000000000024100000000000000000b880000033e002712d6b6d080cf32a1b400000000bae000000000000000000017294a635920000000008d554840001840000029a10d67d5a17b3ca244a38004bc2d2000000007be001f24743f06c46033a6000000060f69973800106c0c000000008240014b0000000000009e2e01ba0d3be000000000000012a817000000001ac426000088f83b600053800000488002e800000000000000000000003ec000000005b1b10904002b40016780000600000000000000002da8000000000057c00032000000001001bf00000000000000000000000340000000029c000000bb000bc0000000000000012736203c0000006800147000000000994004c00000009d800001701c60aa00000000000000002ec8000000027e328bb03080000000056939000000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x4638411011df7728411011df57284110007e7628411015fe4628411015fb7428411015fb5428411015fd7328411015fd53284110007f3608411015ff2208411015ff12084110036be64d901009cfe75d9010004fd75d901009cfc75d9010034fd74d9010004ff73d9010014fe73d9010004fd73d9010014fc73d9010004ff72d901000cfe72d9010004fd72d901000cfc72d90100067f52d90100067d52d9010036bf42d9010006bd42d9010006df32d9010006dd32d901007cfe71d9010006f671d901006cfe70d9010006fa70d901001cff7659010036bc6459010004ff755901009cfe755901009cfc7559010006bf7459010036be5459010004ff7359010014fe7359010004fd7359010014fc7359010036bf4359010006bd4359010004ff725901000cfe7259010004fd725901000cfc72590100067f52590100067d5259010036bf4259010006bd4259010006df3259010006dd325901001cff715901001cfd7159010034fc7159010036bc415901001cff705901001cfd7059010034fc7059010036bc4059010004ff7655010004fe7655010004fd7655010004fc765501001ebe6455010006bd64550100373c545501007cff769041001cfd769041001ebe6490410006bd6490410005fa7090410005f9709041007cff76504100057f75504101557c755041006cff769001001cfe769001001cfd7690010034fc769001001ebe6490010006bd6490010005f67190010005f5719001006cff7650010046f576c401014ef763c401014ef563c4010146f762c4010146f562c4010147b742c4010147b542c4010147d732c4010147d532c4010135f5718401012ef66184010025f9768401003ef9768401000cf9768401013efb628401013ef9628401013fbb428401013fb9428401013fdb328401013fd93284010135f9718401012efa6184010007f26184010004ff7644010005bf7444010035bc7444010005df734401002ddc7344010005ef7244010025ec7244010005f77644010006f77644010004f77644010007b77444010007b47444010007d77344010107d47344010106f76344010106f56344010007e772440100ffe472440100fef762440100fef562440100ffb742440100ffb542440100ffd732440100ffd53244010125f7704401011ef66044010007f24044010007f14044010107f33044010107f030440100fff220440100fff12044010005fb7644010006fb7644010004fb7644010007bb7444010007b87444010007db7344010107d87344010007eb72440100ffe872440100fefb62440100fef962440100ffbb42440100ffb942440100ffdb32440100ffd93244010115fb7144010007f3714401010efa6144010007f26144010007f24144010007f14144010107f33144010107f031440100fff221440100fff12144010
  | 1 => 0x8d10006dc42d8d10006df71d8d10056de71d8d10056dd71d8d10056dc71d8d10006df41d8d10006dc41d8d10006df21d8d10006de21d8d10006dd21d8d10006dc21d8d10006df70d8d10056de70d8d10056dd70d8d10056dc70d8d10006df40d8d10006dc40d8d10006df20d8d10006de20d8d10006dd20d8d10006dc20d8d10056dd10d8d1004dee76d891004eee76d891000cee76d8910007af74d8910007ac74d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910007cf73d8910007cc73d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910007e771d891004fe471d8910007e631d8910007e531d8910007eb70d891004fe870d8910006ef74d8910006af74d8910006ee74d8910006ed74d8910006ec74d8910006ac74d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006cf73d8910006ee73d8910006ed73d8910006ec73d8910006cc73d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d891004eee71d891004eed71d891004eec71d8910006ef41d8910006ec41d8910006ef31d8910006ee31d8910006ed31d8910006ec31d8910006ef70d891004eee70d891004eed70d891004eec70d8910006ef40d8910006ec40d8910006ef30d8910006ee30d8910006ed30d8910006ec30d891004eed10d891006cfe76905100067f65905100e67c6590510006bf649051001ebc6490510006df63905100dedc6390510006ef62905100d6ec629051001cfc76505100057f75505101857c75505100067f65505100ce7c6550510006bf645051001ebc6450510006df63505100c6dc6350510006ef62505100beec625051005fb44150510005fb7050510005f8705051007cfe76901100067f65901100b67c6590110006bf649011001ebc6490110006df63901100aedc6390110006ef62901100a6ec629011001cff765011005cfd765011001cfc76501100067f65501100967c6550110006bf645011001ebc6450110006df635011008edc6350110006ef6250110086ec6250110005f77150110005f47150110006bf64c411007ebc64c4110006df63c4110076dc63c4110006ef62c4110046ec62c4110007bb64c4110007b864c4110007db63c411017fd863c411010dfb72c411010df972c4110007eb62c4110177e862c4110177bb42c4110177b942c4110177db32c4110177d932c411017ff231c411017ff131c4110177f221c4110177f121c4110006bf648411006ebc6484110006df6384110066dc6384110006ef628411003eec628411004df67684110007b76484110007b4648411016df7738411016df57384110007d76384110167d
  | 2 => 0x6bd52d91100063d52d9110006bc52d9110006bf32d91100069f32d9110006be32d9110006bd32d91100069d32d9110006bc32d9110006bf71d911005ebe71d9110006bd71d9110006bf51d9110006bc51d9110006bf31d9110006be31d9110006bd31d9110006bc31d9110006bf21d9110006be21d9110006bd21d9110006bc21d9110006bf70d911005ebe70d9110006bd70d9110006bf50d9110006bc50d9110006bf30d9110006be30d9110006bd30d9110006bc30d9110006bf20d9110006be20d9110006bd20d9110006bc20d91100057f75591101857c75591100067f655911005ebc6459110005df7359110055dc7359110006dc6359110005ef725911004dec7259110006ec6259110004ff75591100067f75591100047f755911009cfe755911009cfc75591100067c755911009c7c755911005cff7459110006bf7459110004ff7359110006df7359110004df7359110014fe7359110004fd7359110014fc7359110006dc7359110014dc7359110004ff7259110006ef7259110004ef725911000cfe7259110004fd725911000cfc7259110006ec725911000cec72591100067f52591100067d525911005ebf4259110006bd4259110006df3259110006dd325911006cff7159110006f7715911007cff7059110006fb7059110005be761911005ebe7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006bf6319110006be6319110006bd6319110006bc63191100079c63191100069c631911005dbf7219110005bd7219110006bf6219110006be6219110006bd6219110006bc6219110007ac6219110006ac62191100073f52191100073d52191100079f32191100079d3219110007b63119110007b53119110007b62119110007b52119110007ba2019110007b92019110004ff7655110004fe7655110004fd7655110004fc7655110006bf645511001ebc645511005f3c54551100f6dc63551100eeec6255110005f77155110005f47155110055de76d8d10056de76d8d10014de76d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10005df72d8d10005dd72d8d10006df62d8d10006de62d8d10006dd62d8d10006dc62d8d10007cc62d8d10006cc62d8d100079f42d8d100079d42d8d10007d771d8d10057d471d8d10007d621d8d10007d521d8d10007da20d8d10007d920d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10004df72d8d10006de72d8d10006dd72d8d10004dd72d8d10006dc72d8d10006df42d8d100069f42d8d10006de42d8d10006dd42d8d100069d42d
  | 3 => 0xf72d921000cfe72d9210004fd72d921000cfc72d92100067f52d92100067d52d921006ebf42d9210006bd42d9210006df32d9210006dd32d9210006f571d921006ebc41d9210006fa70d921001cff765921006ebc6459210004ff755921009cfe755921009cfc7559210006bf7459210006bf545921006ebc5459210004ff7359210014fe7359210004fd7359210014fc735921006ebf4359210006bd4359210004ff725921000cfe7259210004fd725921000cfc72592100067f52592100067d525921006ebf4259210006bd4259210006df3259210006dd325921006ebf415921006ebc4059210004ff7655210004fe7655210004fd7655210004fc7655210006bf645521001ebc645521006f3c545521005cfd7690610006bf649061001ebc649061001cff76506100057f755061019d7c755061001ebe6450610006bd6450610005fb7050610005f8705061001cfe769021001cfd769021001ebe6490210006bd6490210005f67190210005f57190210034ff7650210005f576c4210006f576c4210196f763c4210196f563c421018ef762c421018ef562c421018fb742c421018fb542c421018fd732c421018fd532c4210005f976c4210006f976c421012dfb72c421012df972c421018fbb42c421018fb942c421018fdb32c421018fd932c421001cfe76d911005ebe64d9110006dc63d9110006ec62d911009cfe75d9110004fd75d911009cfc75d9110006bf54d911005ebe54d911005ebc54d9110004ff73d9110014fe73d9110004fd73d9110014fc73d911005ebf43d9110006be43d9110006bd43d911005ebc43d9110004ff72d911000cfe72d9110004fd72d911000cfc72d91100067f52d91100067d52d911005ebf42d9110006be42d9110006bd42d911005ebc42d9110006df32d9110006dd32d911001cfe71d911005cfd71d911001cfc71d911005ebf41d911001cfe70d911005cfd70d911001cfc70d911005ebf40d911005dbe76d911001cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bc65d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100079c63d91100069c63d9110005bf72d9110005bd72d9110006bf62d9110006be62d9110006bd62d9110006bc62d9110007ac62d9110006ac62d91100073f52d91100073d52d91100079f32d91100079d32d9110007b631d9110007b531d9110007b621d9110007b521d9110007ba20d9110007b920d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110004bf72d9110006be72d9110006bd72d9110004bd72d9110006bc72d9110006bf52d91100063f52d9110006be52d9110
  | 4 => 0x854000cfc72d85400067f52d85400067d52d854006ebf42d8540006bd42d8540006df32d8540006dd32d854006ef641d854006ef541d8540006f7619854005df970985400057f75585400957c7558540005df735854008ddc7358540005ef7258540085ec725854007dfb7058540006f5611854009cfe7518540004fd751854009cfc7518540004ff7318540014fe7318540004fd7318540014fc7318540036bf4318540006bd4318540004ff721854000cfe7218540004fd721854000cfc72185400067f52185400067d5218540036bf4218540006bd4218540006df3218540006dd3218540036f64118540036f54118540036bc4018540004fe7694540004fd7694540004fc76945400067f659454009e7c6594540004ff7654540004fe7654540004fc7654540005bf745454001dbc74545401ccfe769414009e7e65941400977b509414001cfe76541401c4fd765414001cfc7654140005bf745414001dbc7454140006bf6590140006bd65901401bdbf73901401bdbd73901400aebe63901400aebc63901401b5bf72901401b5bd72901401aebf62901401aebd62901401af3f52901401af3d52901401af9f32901401af9d3290140006bc619014001dbe709014001fba709014001ebf609014001fbb609014007ebe64d931009cfe75d9310004fd75d931009cfc75d931007cfd74d9310004ff73d9310014fe73d9310004fd73d9310014fc73d931007ebf43d9310006bd43d9310004ff72d931000cfe72d9310004fd72d931000cfc72d93100067f52d93100067d52d931007ebf42d9310006bd42d9310006df32d9310006dd32d9310006f671d9310006f970d931007ebc40d931001cff765931007ebc6459310004ff755931009cfe755931009cfc7559310006bf745931007ebe5459310004ff7359310014fe7359310004fd7359310014fc7359310006be435931007ebc4359310004ff725931000cfe7259310004fd725931000cfc72593100067f52593100067d525931007ebf4259310006bd4259310006df3259310006dd325931007ebc415931007ebf4059310004ff7655310004fe7655310004fd7655310004fc765531001ebe6455310006bd645531007f3c5455310005f77155310005f4715531001cfd769071001ebe6490710006bd6490710005fa7090710005f97090710034ff76507100057f75507101a57c755071007fb4415071005cfd7690310006bf649031001ebc649031001cff765031001cfc765031001ebe6450310006bd6450310005f77150310005f4715031019d7e75d92100057d75d921006ebe64d921009cfe75d92100067e75d921009c7e75d9210004fd75d92100067d75d92100047d75d921009cfc75d921006cfd74d921006ebe54d9210004ff73d9210014fe73d9210004fd73d9210014fc73d9210004f
  | 5 => 0x9cfe7598640004fd759864009cfc7598640004ff7398640014fe7398640004fd7398640014fc7398640004ff729864000cfe7298640004fd729864000cfc72986400067f52986400067d529864007ebf4298640006bd4298640006df3298640006dd3298640006f75198640006f4519864007ef6419864007ef54198640006f63198640006f53198640006f62198640006f52198640004ff755864009cfe755864009cfc755864005ebe5458640006bd5458640004ff7358640014fe7358640004fd7358640014fc7358640004ff725864000cfe7258640004fd725864000cfc72586400067f52586400067d525864005ebf4258640006bd4258640006df3258640006dd3258640006f75158640006f4515864005ef6415864005ef5415864005ebc4158640006f63158640006f53158640006f62158640006f52158640006f5611864006dfa7018640004ff7694640004fe7694640004fd769464009e7e65946400067d659464001dbc74946401ff3e5494640004ff7654640004fd7654640004fc7654640005bf745464001dbc74546400073d5454640005bf7590640005bd75906400e6be65906400e6bc65906400adbe73906400adbc73906401f6bf63906401f6bd63906401edbf72906401edbd72906401e6bf62906401e6bd62906401e73f52906401e73d52906401e79f32906401e79d329064001dbe719064001fb67190640007b66190640006bd6190640007b56190640007ba7090640005bd7090640007b9709064001ebe609064001fba609064009cfe769424001cfd769424001dbe7494240005bd74942400073d54942401dfbb409424009cfe76d95400967e65d95401dcff74d954001cfe74d95401dcfd74d954001cfc74d95401de7f54d95401de7d54d9540004ff73d9540014fe73d9540004fd73d9540014fc73d95400067e53d95400967c53d95401debf43d9540006bd43d9540004ff72d954000cfe72d9540004fd72d954000cfc72d95400967f52d95400067d52d95401debf42d9540006bd42d9540006df32d9540006dd32d9540004fe71d9540004fd71d95400967c51d954001cfd70d95400967f50d95401debc40d95400967c6559540005df735954008ddc73595401d5fb70595401c4ff7459540006bf7459540004ff7359540006df7359540004df7359540014fe7359540004fd7359540014fc7359540006dc7359540014dc73595401c6bf4359540006bd4359540004ff725954000cfe7259540004fd725954000cfc72595401c6bf4259540006bd4259540006df3259540006dd3259540004ff7159540004fc71595401d4ff7059540006fb70595401c6bc405954009cfe75d8540004fd75d854009cfc75d8540004ff73d8540014fe73d8540004fd73d8540014fc73d8540004ff72d854000cfe72d8540004fd72d
  | 6 => 0xd765454101cfc7654541005bf745454101dbc74545410073d5454541237b44154541005bf7590541005bd75905410073f65905410e6be65905410e6bc65905410073c65905410e63c659054122ebf639054122ebd6390541225bf7290541225bd729054121ebf629054121ebd629054121f3f529054121f3d529054121f9f329054121f9d329054101dbe719054101fb6719054101ebf619054101fb761905410067f65d81410067c65d814109cfe75d8141004fd75d814109cfc75d8141004ff73d8141014fe73d8141004fd73d8141014fc73d8141004ff72d814100cfe72d8141004fd72d814100cfc72d81410067f52d81410067d52d814107ebf42d8141006bd42d8141006df32d8141006dd32d814107efa40d81410cd7e75981410057d75981410067f65981410067c6598141006fb60981410057f75581410cd7c75581410067f65581410067c6558141005df73581410c5dc7358141005ef72581410bdec72581410067f65181410067c6518141006f9601814109cfe7518141004fd751814109cfc7518141036be5418141006bd5418141004ff7318141014fe7318141004fd7318141014fc7318141004ff721814100cfe7218141004fd721814100cfc72181410067f52181410067d5218141036bf4218141006bd4218141006df3218141006dd3218141006be4118141036bc4118141036f940181410b67e65d9640005f671d9640005f571d96401cdfa70d9640004ff73d9640014fe73d9640004fd73d9640014fc73d9640004ff72d964000cfe72d9640004fd72d964000cfc72d96401debf42d9640006bd42d9640006df32d9640006dd32d9640004fe71d9640006f671d9640004f671d9640004fd71d9640006f571d9640004f571d96401ccfe70d9640006fa70d964009cff76596400b67c65596400067f75596401c67f54596401c67d5459640004ff7359640014fe7359640004fd7359640014fc73596400b67f53596400067d5359640004ff725964000cfe7259640004fd725964000cfc72596400b67f52596400067d52596401c6bf4259640006bd4259640006df3259640006dd3259640004ff7159640004fc71596400b67c515964001cfc70596400b67c50596400b5bf765524009ebf765524009cbf765524001dbf755524001f3f755524009ebe65552400b73e655524009e3e65552400073d655524009ebc65552400adbe73552400adbc7355240216bf6355240216bd63552400b73f53552402173d535524020dbf725524020dbd7255240206bf6255240206bd62552400b73f52552402073d52552402079f32552402079d3255240005bc71552400b73f5155240005bf7055240007bb7055240007b8705524001ebe605524001fba60552400b73c50552400b57e75d86400057d75d8640035fa70d8640006f76198640
  | 7 => 0x9541006df32d9541006dd32d954101cfd71d95410ce7f51d9541004fe70d9541004fd70d95410ce7f50d95410ce7c50d954123d7e76d954109c7e76d95410073f74d95411ff3c74d95410067f63d95410067e63d95410067d63d95410067c63d95410057f72d95410057d72d95410067f62d95410067e62d95410067d62d95410067c62d95411ff3f42d95410073d42d95410075f32d95410075d32d95411ff7741d95411ff3c41d95411ff7441d95411fe7f74d95411fe7e74d95411fe7d74d95411fe7c74d95410067f73d95410067e73d95410067d73d95410067c73d95411fe7f43d95411fe7e43d95411fe7d43d95411fe7c43d95410067f72d95410047f72d95410067e72d95410067d72d95410047d72d95410067c72d95411fe7f42d95411fe3f42d95411fe7e42d95411fe7d42d95410063d42d95411fe7c42d95410067f32d95410065f32d95410067e32d95410067d32d95410065d32d95410067c32d95411fe7f71d95410ce7e71d95411fe7d71d95411fe7f41d95411fe7e41d95411fe7c41d95410067f31d95410067e31d95410067d31d95410067c31d95410067f21d95410067e21d95410067d21d95410067c21d95410067f70d95410067e70d95410067d70d95410067c70d95411fe7f40d95411fe7e40d95411fe7d40d95411fe7c40d95410067f30d95410067e30d95410067d30d95410067c30d95410067f20d95410067e20d95410067d20d95410067c20d95410ce7c655954125df77159541234ff7459541006bf7459541004ff7359541014fe7359541004fd7359541014fc7359541004ff725954100cfe7259541004fd725954100cfc7259541236bf4259541006bd4259541006df3259541006dd325954125cff7159541006f77159541004ff7059541004fc70595411fd7e76195410ce7e76195411fc7e761954123f3e74195410cf3d741954123e7f64195410067f63195410067e63195410067d63195410067c63195410cd7f72195410057d72195410067f62195410067e62195410067d62195410067c621954123f3f42195410073d42195410075f32195410075d321954123e7f611954123f77411954123f3c411954123f7441195410cdbc765514109ebc765514109cbc765514101dbf755514101f3f75551410073f655514109ebe655514109ebc65551410cf3c655514109e3c6555141256bf6355141256bd63551410cf3f53551412573d535514124dbf725514124dbd7255141246bf6255141246bd62551410cf3f52551412473d52551412479f32551412479d3255141007b77155141005bc7155141007b4715514101ebf615514101fb761551410cf3f51551410cf3c505514123cfe76945411fe7f659454109e7c659454101dbc74945411ff3e54945410cf7751945411ffb4419454101cfe7654541234f
  | 8 => 0x6bd42d8154006df32d8154006dd32d8154004fe71d8154004fd71d81541d6fa40d81541d6bc40d81541df3c5498154005f67198154005f57198154006fb60981541c73c5458154005df73581540f5dc73581541cf3c5418154006f9601815409cfd7418154004ff7318154014fe7318154004fd7318154014fc7318154004ff721815400cfe7218154004fd721815400cfc72181541cebf4218154006bd4218154006df3218154006dd3218154004fe7118154004fd71181541cef940181540e67e65d96411ff3c54d964123df671d96411fe7e54d96411febc54d96411fe3c54d9641004ff73d9641014fe73d9641004fd73d9641014fc73d96411febf43d9641006bd43d9641004ff72d964100cfe72d9641004fd72d964100cfc72d96411febf42d9641006bd42d9641006df32d9641006dd32d964123cfe71d9641006f671d96411febf41d9641004fe70d9641004fd70d96411febc40d964109cff76596410e67c655964101dbc74596410e73f54596410067f75596412367f54596410e6bf54596410e63f54596412367d5459641236bc5459641004ff7359641014fe7359641004fd7359641014fc7359641236bf4359641006bd4359641004ff725964100cfe7259641004fd725964100cfc72596410e67f52596410067d5259641236bf4259641006bd4259641006df3259641006dd325964101cfc71596410e67c5159641236bf4159641004ff7059641004fc7059641236bc405964109cfe769464101cfd769464101dbe7494641005bd74946411ff3c54946411ffb74194641006fb609824109cfe7598241004fd759824109cfc7598241004ff7398241014fe7398241004fd7398241014fc7398241004ff729824100cfe7298241004fd729824100cfc72982410067f52982410067d529824106ebf4298241006bd4298241006df3298241006dd329824106ef94098241006fa2098241006f920982410057f75582410e57c7558241004ff75582410067f75582410047f755824109cfe755824109cfc75582410067c755824109c7c7558241004ff7358241014fe7358241004fd7358241014fc735824105ebf4358241006bd4358241004ff725824100cfe7258241004fd725824100cfc72582410067f52582410067d525824105ebf4258241006bd4258241006df3258241006dd325824105efa405824105ebc4058241006fa2058241006f92058241006f9601824109cfe76d95410ce7e65d95411fcff74d95411fcfd74d95411fe7f54d95411fe7d54d9541004ff73d9541014fe73d9541004fd73d9541014fc73d95410ce7f53d95410067e53d95410067d53d95410ce7c53d9541004ff72d954100cfe72d9541004fd72d954100cfc72d95410ce7f52d95410067e52d95410067d52d95410ce7c52d95411febf42d9541006bd42d
  | 9 => 0x100100000200100e00a00100600700100e00700600700d00c00800001700200000201c00200000400c00000900000100700a00000000c00100000e00200000000001600001d00000600000c00100100700900000300100300200800000500300701700400200100000100900500f00000000000800000400200300000000100300000000300100500000100000500000400b00600c00000200c00200000000200800c00b00600d00000200c01100200000100b00000000000100200000300700000900600100000400100000101300800000b00500000800100300100100000000100200200300b00000400201000000400200500200200200100100300800500200600300000000000000000100500200102000100000000100000000000200000000300000100c00800801000000100000000000002000200100600000100300400100000000500200800200600900200700600000000000200400100400000100200400200200000000400500000200a00000001100400900600200900100500400700000100000200300500000000300300400500100500000100000900000a00101700000000501a00200000000000900800300802200b00000100300e00100000100000000000300100000000400c00200200200d00200100701300100a00000200000000300000000000700100100f00000601300000100200000801500000100100000700800d00000000200000400100f00000100200201400401200000200101301e01100000000b00000200200500000000100100000400500000400000500000000200100400000300000000200402302100300200300000200101d00000401a00000300000300400200501200000000200001400100100200025f3c54d855409cfd74d8554004ff73d8554014fe73d8554004fd73d8554014fc73d8554004ff72d855400cfe72d8554004fd72d855400cfc72d855425ebf42d8554006bd42d8554006df32d8554006dd32d855425ef641d8554006f721d8554006f421d8554004fe70d8554004fd70d85541ff3c5498554006f761985542373c545855423f3c5418554006f5611855409cfd741855426ebd741855423e7e541855423ebc541855423e3c5418554004ff7318554014fe7318554004fd7318554014fc731855423ebf4318554006bd4318554004ff721855400cfe7218554004fd721855400cfc721855423ebf4218554006bd4218554006df3218554006dd321855423ebf411855423ef54118554006f72118554006f42118554004fe7018554004fd701855423ebc40185541d73c54d815409cfd74d8154266bd74d8154004ff73d8154014fe73d8154004fd73d8154014fc73d81541d6bf43d8154006bd43d8154004ff72d815400cfe72d8154004fd72d815400cfc72d81541d6bf42d8154
  | 10 => 0x2688bc200059c0009ba9acbfc0000004c46800000000002d200065a7a25260000000000002321a528040c0003f815867a69e000a36000000000262c0800000095e2d60546dc46c3446377860000004d0000000000000aaec6e66096c0ec3b21d02789be1b8bd6a740c6650b781e9bc064da8c0009a43b600009c000ace00000000000028800000000083c739c106318ce45c656480c587c630c9243aa86a8bc5463f61842382d0c44b0ac3c90a1cac6a0eab2c75400816c5d203c23e07e3566f431234c000030a407de7f076c4300000000008a800076400056400000045059e08460e93400057e588ad00660000164766b80000008fa2da98400000082800013ea880008ba7b6000c0a0000000002180000007ae000000000510000462ad300000000045a000b3e4bb48e858b8a9f8000000000845000300893000538b7684e64796a0005e8000034973672000b329880005366550000002f0c7000000071abdc000000b1287e3a487c0002bc0000a2000916962614000ae621f4b937a0d2c189429600005286080006bf4e6a0800000048c5d09cb1d618d18bb428918d41be39e1620000465aa00000077fac4000334aa400012a000838be6213000000c485966c86f66e4000a326109d49d86062e20000000000000008e4000208092948a6b7760000000c433800000069a89a51c5b619c0000000004ae00000000000000073ac4f40a05a65c0006c477925629000019ab38ac6000578000572000000a562ac26a052086000000000000360000188000b0207f3be000b5ac6b3683b5302576ba29ee7a4a7244abc161845e0001e60009a2355bf609a000000a760001548149689a83f4000af88c0b96bae2c980c000802458221710bb01cc877bab2f217c19250207d27157a1b47b2267be824e85cbc85d6642c69000000c548733a002bbb20290007c4a5800a00000000000013895700000000000000000000071e0a8c000000000000002980007f890c00000000000083e49439a8089965f00000000006a28ee00c00053e2f80000004967b0c465dcb1a00300000a00300100700200000000100000400d00200f00c00000600000200300300400000000500000900300100c00b00500300000100400300100301300000c00300700100301200600600100f00200500300000400d01300200a01100000100000400100103300100000000a00100600900000500100200100000600400f00400300200000200400501200a00400200000700000600200b00b00000500000400200400000400000200000400300500600000000000700a00000000000200200000c0010070150010000080030000000100000000040090000030000030050000030000000040160000000050000000050040000020000050110000040010010040060090190000000010000
  | 11 => 0x732000000a66817000000b28616910a30b187e60001860006008a0750000b4e49822e000000bf50000005c60000000000000005f200055e842000bc6b08adc6d20000e40000000000000369024520008c66483980005fc000000000000000b20000c290000009fac0d6d662200062a00000000000037e8e800000000038600005d0008e635453205b0005483160008000068b400000000000097c7d265235000026d00000000000034a0000004c2aaab8492875812c2e40001aeac00006cf9df0d74903482dc2aa4e8acf44e69223cb061641821bb000000be00000004425ac000c4a37601200024cc7a0005949d601e1f25126ba0c7000000110000c1d2e84730022520006e86cdb2a000be274ec2a4b62f605846e11c9ddb565ea024000c0c14062e29f57072f4da88e74a8f229672e8f03c227361e0f6269c722ee47ea5aa902cd0000009c2000a2237247418c956bbb000c400000008c20009710009947cc2a028c330b0498eb70624674b7a000bdaa060000000003e250a000000048000b9c5c05d40005e07dca8686000014800035c7ce61cba97824d84f43705922c4000000000af462c1ce000abcaf29128f80941b67d442600000076e0000000003d82894c80007046265824664fa00077d9269f40007561aca4200064a6be1eab803360001aa4be94e41615c77a0000000002b200000000000000077454c0009460006f056c00023b0000008bec524f20000b64fe0001d3c6607a196b6698a5a800060482ea1a0003d4000aa200040897a42000081e17e0003da2fe7a00000002702dd000000000000a2467e54a000bdf80e85402a00020299d8203cca8e0009c026f84643626ba04516b450008ea6b62658ca1a47e297800029e7aab47000a64b14000afa2a400081c00082c5ee25e00085e102000886c120002db7347774f86aaa680008e00ba0000008fec380007b4b1c00000010c00060aa50a9a00051400e0008220008a5a840001424e40000009b6000000bea52e8d0a543ce0003110000006c230f0000005ec7c000043e0e8000049222000000000000a4a25ab93aa60000003660005626ae000000bd83280000004b299c91800095122400006c00000094f0dc86c9060000950000000000000000007384aa2390008b80000003920470000205b266c000000830970678ba68164e22c20008d60002a9000b6ebde694598000000c327281182720930005a100035a9dc6ccbb8000a2c000166a0a00050800042a3eaa2002e6d99a6000b2e2000d04ba47866eb8d00068c97e0001f422c91a49e2a85681e479021c38e1c85deab677e14e892b160fea62456a384c06bc410bec72a794b980766e06f10d9a34c3d0108829e0c62c562cb30688a8dc000000144c221908da0002c5a7a1789d294900007236c000c6c000c2469800063244ca0
  | 12 => 0x2c1b00fa0006b0000b4cc3e2a6a9879e6020000007680000fc448af07a835953c00000000074300000000078f000852000762b22000000c3105c3e65569d09f00000000184b067c3180000000000003d60090001061f000000052c0001ee00000000049c15f78c1521a215d2e02545a45500000000000003c678a8deadeaac3e00009922668130005bcc2f2b84ce63e7401991976fc028b7c2fcc7e0009da7ec8110006ca0000009fc2b0000566c1e3260b09582a2c4bc4903a0004a200470e716000000000000ae8a3a0005a20000000000008c85868f672921e8065da28a3ca00000011e2502045ae000114c7d2b31e82e60ee2ca00027e5b08a4000000700156b5400000000000027ab3c00000061200000061a48270c04e9cc9320000005600007ba00036a9aa00019472096e1dbc76422a78000000b10c0ea5c91432e0000000000000c20000000001f62ad00030a0f80007d8c1cb9e14a55400046b00043c000adaa5e2c7060000180628bc40000002c02afbf3ba4000000000000c7410428e78e0006204d4000000b269222105a31764706d84ca06f9938d2876b5c3dc06d0e12ea8721a808c000c04000a4822a0003a21b2c4e43a406952268000bfa01c9b8000888b0ebee464b410000005cc000b9269c31a8943f23ee0000400000bc00068ea0ebce544bca216772a6e3aeab45fe4bca2a1de1dc0821329c480a6f8b2422365e00059000073c97681a990346aca8742ba0003c4000286b64bbc26eb742b1000b4a0000a058c72c21a00086e9e606a8b0000000000c1658a424000722ab874c3f00007e40ae46f00050e432ab000000000000054e000000126201122b0c6c00003fa0009000002ab5e69e20223a86f2000a6c8ac382486c5ec60000000000736ab279800000003b19e89e000c1a00000000b0a431084a0000000144a678833c0000df062000276000120a6aa8a41aa120000000009bc00000000071c000864000000920000938b9f00000000000004400086814b3b46ed9e400048435135293676647c0005ca000c2e5040002d8000000000c270009c66fe0000000e0c3b4a429d16a0904cb0b853a7120d69fec0680f13463d91eae4428b9091c39c320b9d530b3a48851800014983498c86200087a42e0007023400b4c7c520000bb93ba0b2be4ac89de6cebb700000000000028200026000027700012e0004c9434a4e0d42465f82f45341ad02c7da000358000792000a5200034e0006829c8000308a920000000000000001f1000b7bafcb88000000b6a70821200000000000013a5f63d0000000242230000bd0000c144a85006380c80007e800042ca80000a14abe0004180006468129b27ee2f12fbb687469ae36e810314258a7c3e800007400000040e8cc1d4b8c9f18980000000001bc9045f4b589f600017000089c000
  | 13 => 0x6b435e0000000cc32a4461b71ec00040406800015e000000c2c5e401a00000000000000000000095c0000000000000000000000000005b80000000502c8b349ea7261980002de52a6ec3783b0a1cac295077c7846304b826c215000112af6000264b7200083a0003fe99a0007f2000000b5000083500000000000089004200000017d0000004000000007701fa20e0000004a09648c4ad8a1ea1873e000aea8503224fc0000009f3000000c1723f93cc0133a08ec78b400004ac7c813c00041ca4c0008a2000a9c1087067bcb865a60002366dbbb66a60007a617b00073f124b8e1c630e29c1ff6402ce000796364bff7fa0002be6680005581e272427c00000078014cb83b44000000000c3a0006847f40000aa00000000000000079c0000000004020006e20006a40be880396c2018e908b303c084c0008ec000c4d438c5c00051a00000000000006e05e6661cf000000000bf83ac274000bd4000000000000000000b5e0d800007c506000a16c6816d388654c191601729f54720002b6ad456ec4216b00031eb1e00003e0007fc01b5d80000003fc55a0000327ea0000000000000000006da37cbcc7ac00000009e21400000052432400020a1a071868600008a000000c5abba6acb94bf2304000150412aa88567420da8663849ca0192ae0000e2a96000bd2000a2855200064496d4ea2f70acafec4cb52bb459a6c64de730aee0004cc60c00000000000031c6582ec0002435c49301681f80008aead249a3e45c858058438a0000002c67522d411a6960f00000c08b2000064a9e1e0000000963000000000000a3ea820000009b43745e223d1d810e94aaec1c016e10a47a1da9862481c282a980824bf41168845b451e4546d08362fd4dc0703bc69023a7f60000002f34d66d4b007be3941742404fd80d36299ea103902340001460387480006ea67034298284368ab9a56a088a2e000000ba04b4000128000944c026a8c30000a7e22893e0006de82604c000a949b04ff88c896a704140c99a0b62080000000000634b82a464609984c641e357000bbe0001ba0561d2b3600073d840098b4600058eabaa3c03d4f00000005be292870000237a606e663c33e0000000001c40000004ee000000000000ae090ebcd000000b6066a8a696f3b822617a3326b2c283ec241844aa00000005225fa0007b8000000c367d67fe38c492206b7e24abfe3de8d800070a8aa0009540ca63a9f20003a615a000000c0b3c80004f61a19ecbcb2fa6760000006a0acc0006622f900047793a00092e7e028476aba8bf018a64cbac63575e2f51e5ad60002b44d22ef000000000c500000781301fe5cec340007c2c6400000064e000000c633d28fc760b4857cae2000244000444225636000000848714a0c00095a57475c4ec1c30f24e08e20a69ce4637ca9
  | 14 => 0x74422087885a96675a92a20c8f46648046ee9404401000de29a54246a2942cc13604a3800e6a000f41fc6ef25c000000000000a440000007d09e802632c99b972832baa6fa81897428b000b6c0000005c200000000000000055c00000009627594c778000000000c26b4b0000cea268b60000005400000005ba00000000050c1a679a46848a5a000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe8c6418f6244001d1ee831ec488003a31d063d891000762c08c7b122009ae686dc76244001d88c718ec488002f820131d891004d75436e1b122000dcb73dc36244001c5eebba6c4880029ba1674d891000536c2ce9b122000aae849d3624400159d073a6c488002b360e74d891000537c2ae9b122000a6c855d3624400159f06ba6c488002b320d74d891000557438e9b122000cae871d36244001c5eea3a6c4880038b1d474d891000717aa4a9b122000e2d54153624400195ee9b9ec48800333dd373d891000747ba6e7b122000c8f74dcf624400199ae9b9ec488003a31d373d89100066738ee7b122000ccc71dcf624400199ae1b9ec488002aba1273d891000556c24e7b122000ace839cf624400155f08b9ec488002ab21173d891000657ba2e7b12204eae6811cf62440015cb0239ec488002b3a1c73d891000667438e7b122000e8f741cf6244001d18e839ec488003b1a0473d891000762c08e7b1220008ee8710f62440011db0e21ec4880029ba1443d891000536c2887b12201faea80dc762440014dd0a20ec4880029b61441d89100047743e63b1220008ed87cc7624400155d0998ec488002ab61331d891000667b9ee1b12201fae681dc362440014dd0ba06c4880029b61740d891000557c2261b122000aac844c362440011dd0e186c4880263b61c30d89100055742061b122000aad840c362440015cd02186c488002b960430d89100043f436eaa0a203fc3c64dd541440018b8c7baa82880031b18b755051023c3f43ecaa0a203f87c87d954144001c6883b2a82880030fdd764505100061e3aec8a0a2000c5f75d8d41440018b8ebb1a82880031bdd76250510006363aec4a0a2000cbb641c1414400196ec838a808802f2d9db648411001e5b3b0c9082200acd676d8e10440139ccedb1420880071b9c952d901000636b92a5b2020018bf8750b640400395ce4a16c8080032b5c942d901000e6739265b202000ccd724cb6404001c9aa4996c808003a350932d90100043fc2ae6b20201387c855cd64040051790ea1ac8080062f213725901000c5e43a84b202000caf72509640400399ce4992c808003335c9325901000726a9264b202000e8d424c964040011ed033b2a80800a37a0c76550100046ec18ecaa020018ee821d954040011db043b2a80804e2f21d645501009d1e42ac8aa020018f5869c6400400196ac938c8008003351cf764401000672396ec8802000cb742dd9100400196a85bb2200800335ccb76440100066a996ec8802000cb776dd1100400196eec3a2200800335ddb734401000673bb6e48802000cd873dd910040019d0e5bb220080032ed0b76440100065ca16ec8802000cdb32dd910040019b265bb220080032eddb74440100065dbb0e88802000cdb76dcd10040019d6edb922008002dce154144010
  | 1 => 0xceda16c68800387d9742d8d100070e32e85b1a2000e8f62d0b6344001d18c5a16c688002a7a1942d8d100054e43285b1a2053c9e7650b6344001c3ecaa16c6880038719542d8d10006c7b9285b1a2000e8f6250b6344001d18c4a16c68802ab5a1b71d8d10105e9406e3b1a2000ec4628876344001d90c5106c688003f088620d8d10006e5b9241b1a2000a5e859d363440014bb0b3a6c688002b3a0a74d8d1000566c14e9b1a2000e1f549536344001c3aa82a6c6880023761e72d8d100054f424e5b1a2000a9d849cb634400199f04b96c68800237a1c72d8d100054f420e5b1a2000a9d841cb63440a55ad02396c688002b560472d8d1028d6d400e5b1a2000ad9801cb634400193ee5a16c688003275cb42d8d100070fa9685b1a20008de8790b63440011bb0f216c68800297a1642d8d100052ec2c85b1a2050a9d8490b634400199ee5216c68800333dc942d8d1000747c1285b1a2000c9f7250b6344001d1ee4a16c68800323dc942d8d100064eb9285b1a2000e8c7250b6344001c3ea4a16c6880038754942d8d100046f43885b1a20008dd8710b63440014bd0a216c6880029761442d8d1027d4f42085b1a2020ada80dc763440014bd0a20ec6880029761441d8d100046f43e43b1a20008dd87c87634400153d0990ec688002a761321d8d100046f43843b1a200a8dd87087634400153d0810ec688002a761021d8d100056d40043b1a2000ad980087634400153d09b86c688002a761370d8d101056b40ee1b1a2000a5e85d0363440014bb0ba06c68800237a1f20d8d100046ec3e41b1a2000a9e84c83634400153b09906c68800333dcb20d8d1000667b9241b1a20008de8708363440151bb0e106c688002a7a1020d8d100054ec2041b1a2000ad68108363440015ab02106c688002aba1b74d8910006573b6e9b122000aae861d3624400195cec3a6c4880032b9db64d891000717b2ec9b122000e2f75d936244001c58ebb26c4880023b61e64d89100053742cc9b122000a6d85993624400155d09326c488002b3a0e64d891000566c1cc9b1220008ef8759362440014df0ab26c4880029b21564d891000567c1ac9b122000acc83593624400155d0c326c4880032b9d864d891000717b28c9b122000e2c651936244001c5eea326c4880038b1d464d891000567436e7b122000cce76dcf6244001b1ee9b9ec488003a3d9373d891000746326e7b122000dc471dcf624400159d0c39ec488003339d873d891000747b20e7b122000e8c641cf624400199cedb1ec488003a3d9363d891000746326c7b122000e8f74d8f6244001d18e9b1ec4880023b61e63d891000557424c7b122000aad8498f624400159d0731ec4880023be1d63d891000557c22c7b122000aac8458f624400159d0c31ec488003339d863d891000747b20c7b122000
  | 2 => 0x463191100070e328c63222000a9d8218c644400193ee4318c888003a560463191100061fb2ae43222000c3c655c86444001938c6b90c8880022fe1f621911000656b96c432220008bd87988644400147d0b310c8880028f61662191100054f41cc43222000a9d83988644400117f0eb10c8880028fe1562191100051e42ac43222000a9f83588644400153906b10c88800e2fa1c62191100045ec38c43222000a3e85188644400147b0a310c888002a7a0c62191100054ec18c43222000cad721886444001c5eca310c8880038b194621911000746318c43222000cad871886444001c5d0a310c8880038b614621911000747418c43222000e8d831886444001d4b02310c888003aa60062191100051f436a43222000a3c86d48644400187ceda90c8880038718f521911000717b16a43222000e2c62d48644400147d0ca90c8880028f21952191100061f3b2a43222000e1c635486444001c5ec4a90c8880038b18952191100054f436643222000a9c86cc8644400193ced990c88800387d9732191100070e32e643222000e8f62cc86444001d18c5990c888002a721932191100064f3b2643222000e1f654c86444001c38ca990c888003635c9321911000747b12643222000e8c624c86444001e1aa4990c888003a518e31191100055a432623222000bb0804c46444001d48c5108c888003e14ca21191100055a432423222000ea4624846444001d50c5100c888003e888620191100055c432403222000f893248064440051bd07bb2a8880023760f765511000c77416ecaa220008ed82dd95444001878a93b2a8880022fe1176551100046fc1aecaa220028dc835d954440011df04bb2a8880063b20976551100061e2a0ecaa220138be87d91544402747d0bb22a8880023da1b715511000672316e2aa220009f280dc5544400196ec838aa8881574d150715511000672310e2aa22000c9e76d936344001c3ecbb26c688002a760b64d8d100046ec3cc9b1a2000a5e8599363440014bb0b326c688002a7a1264d8d1000567414c9b1a2000acd8299363440011bf0eb26c68800297e1564d8d100052e42ac9b1a2000acf82593634400159904b26c688002a7a1864d8d100064f3b0c9b1a2000e1f651936344001c38ca326c688002a760864d8d100046f436e5b1a2000c9f64dcb6344001938c9b96c68800327d9172d8d100064e322e5b1a20028df87d8b634400199ae5b16c6880023761e62d8d100054f424c5b1a2000a9d8498b63440011bf0eb16c688002a7e1162d8d100054e422c5b1a200a8dd8718b634400153d08316c688002a761062d8d1000666b90c5b1a2000e8f6418b6344001d18c8316c6880033361c62d8d1000747420c5b1a2000e8d8418b6344001d8b02316c688003b260062d8d100054f43685b1a2000a9c86d0b63440a993
  | 3 => 0x1b222000aad820c3644400156d02186c888002ad60430d91100045f43e41b2220008bd87c83644400147d0b906c8880028f61720d91100054f41e41b222000a9d83c836444001d1a65906c888003a34c920d91100045f43841b22200b8bd87083644400147d0a106c8880028f61420d91100054f41841b222000a9d83083644400156d02106c888002ad60420d91100061e326eab222000c5c73d9564440018d8e5b2ac88800a37a1b73591100062fb2ee6b222000c9c64dcd64440018beea31ac888003171d4635911000666390c6b2220018ee86dc964440018decbb92c8880032b19372591100066631ee4b222000c6f7518964440018d8ea312c88800333dcc625911000666398c4b22201387e87dd564440010fb05baac8880030fd0b75591100061fbaee8b222000c3c75dd164440051bd0fb9ac88800317dd773591100062e3aee6b222000c9f74dcd64440011bb05b9ac88800327d0b73591100043fc2ae6b22201387c855cd644400117f08b9ac8880023be09735911000c76412e6b2220008de871cd64440018beea39ac888003171d473591100064fba0e6b2220018ee87dc964440018deebb92c8880031b1d7725911000657ba6e4b222000ccf73dc96444001998e7b92c8880031be1772591100063642ee4b222000caf84dc9644400195909b92c88800333e0f72591100066641ee4b22200087f855c964440270f90ab92c8880022fe1172591100046fc1ae4b2220028dc835c964440011dd0e392c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc72591100043f43ea4b22201387c87d4964440018bee7a92c88816b171cf525911000637b96a4b222001c6c72d4964440010fd0ea92c8880021f21d52591100062fb9aa4b222059c5c7354964440018dee4a92c8880071b1c9525911000c5e43a84b222000c3f7550964440b1878eaa12c88800327dcd425911029e4e39a84b222000caf725096444003958e4a12c88800237a1f32591100146e43e64b222000c5f75cc964440af8b8eb992c88800333dcb325911000e6639664b2220008de874c964440011b90e992c88800317dd532591102b62e3aa64b222000ccf724c96444003998e4992c88800393549325911000746a1264b2220008bd829d8644400187cedb28c8880028f60b65191100061fb96ca32220008bd87994644400147d0b328c888002a7a0e65191100054ec1cca3222000aae82994644400155b05328c8880022fe1d65191100054fc1aca3222000a9c83594644400155f04b28c888002ab20965191100061f3b0ca32220008bd8798c644400147d0b318c8880028f616631911000557414c63222000aad8298c644400117f0eb18c8880028fe1563191100051e42ac63222000aaf8258c644400155904b18c88800387d9
  | 4 => 0x444001d4b02316c888003aa60062d91100051f436a5b22205fc3e76d4b6444001c38c7a96c8880038bd8b52d911000716316a5b222000a3e8654b64440014790ca96c88817b0f9d952d91100070e31aa5b222000e2f6254b6444001c58c4a96c888002a7a1b32d91100054e43665b22205dc9e76ccb6444001c3ecb996c888003a3d8b32d91100074631665b222000a9c864cb64440b993cec996c88800387d9532d9110006c7b9265b222000e8f624cb6444001d18c4996c888003c354932d91100074a31c63b222000bb0804c76444001d48c510ec888003e14ca21d91100075431441b222000fa2218836444001f1264906c888002ad60775d91100061fbacebb222000c3d751d7644400147d0b39ec8880028f61673d911000557414e7b222000aad829cf644400156d0239ec888002ad60473d91100070fa9ca7b2220008be8714f644400117b0e29ec888002aba0853d911000556c10a7b222000a3e859cb644400147b0b396c888002a7a0e72d91100054ec1ce5b222000caf825cb644400147d0a396c8880028f61472d91100054f418e5b222000a9d831cb644400156d02396c888002ad60472d91100055d400e5b222000ab9801cb644400187ee5a96c8880030f5cb52d91100045f43ca5b2220008bd8794b644400153d07296c888002a760e52d911000717c12a5b222000c3f7254b644400187ae4a96c8880022fa1c52d91100045ec38a5b222000a9e8314b644400153b06296c88800327dcb32d91100064eb9665b222000e1f52ccb6444001c3aa5996c8880022fa1e32d91100045ec3c65b222000a3e858cb644400147b0b196c8880032bdca32d911000716a9465b222000caf724cb6444001c5aa4996c888003a3e0932d91100064fb9265b222000e8f724cb644400191ee4996c888003275c932d91100074639265b222000e1f524cb6444001d1ca4996c8880038754932d911000746a9265b222000e0d524cb644400117d0e196c8880022f61c32d91100051f42865b222000a3d850cb644400147d0bb8ec8880028f61771d91100045f438a3b22200b8bd87147644400117d0f98ec8880022f61f31d91100051f42e63b222000a3d85cc7644400155d0598ec888002ab60b31d91100045f43e43b2220008bd87c87644400147d0b90ec8880028f61721d91100054f41e43b222000a9d83c876444001d1a6510ec8880022fa1c21d911005c5ec3843b222000a3e85087644400147b0a10ec888002a7a0c21d91100054ec1843b222000e8d3208764440015750010ec888002ae60021d91100051fc2ae1b222000a3c855c3644400117d0fa86c8880022f61f50d91102dc5fc3a61b2220158bc874c3644400147f0a986c8880028f21530d91100045f43861b22200b8bd870c3644400147d0a186c8880028f61430d9110005574106
  | 5 => 0x14f271cd425954000657b9284b2a80008de87cc965500051b90f992caa000237a1d32595400046e43a64b2a8001cce724c9655000199ae4992caa0003a3509325954000e6739265b0a8000ccd724cb6150001c9aa4996c2a0003a350932d85400047bc3ac230a8001cce724c8615000199ae4990c2a000393549321854000746a126430a80038bc841d9515000187ecbba2a0a004e2fe1d65901400ad4e41acb202801387e85dcf64c40010fb0bb9ec98800a2fe1d43d93100164f39a87b2620018bf8750b64c400195ae4a16c98800333dc932d931000e6639265b262000e4d524cb64c4001d1a84996c9880022fa1e435931000c5e43a84b262000caf7250964c400199ee4992c988007331c9325931000726a9264b262000e8d424c964c40051bd073b2a9880023760e765531009c5e43ac8aa62013a3c8559154c40c1a68a838aa98804e1fe1d75d92100043fc12ebb242000c3f425d764840270fd0bb9ec9080021f61773d921009c3f42ee5b24200087d85dcb64840270ff0fa96c9080021f61f52d92100043fc3aa5b24200087d8754b648400317f0ea16c9081630f9d542d92100061ebaa85b242000cad7250b64840af8bceb996c908003175d732d92102b62f3aa65b242000c5d754cb648400399ce4996c908003335c932d921000726a9265b242000e8d424cb64840018eceab8ec9080028fa1774592100061fbaea8b2420028bc8750d6484005938e6a1ac9080062f21d425921000657b9284b242001cce724c9648400199ae4992c90800393549325921000746a1264b242000c3c54dd9548400117b093b2a9080030f151765521009c5f43ec8aa42013a3e85d91548403947d0bb2483080030f1d564506100061ebaea9b2220028bf8750f644400195e85b96c8880028fa1642d91100051ec2c85b222000a9e8390b644400153b07216c8880062fe1d42d911000656b9285b222000ccf724cb6444003998e4996c8880039354932d91100074721265b222000e8d424cb644400153d0732ec888002a760e65d911000557414cbb222000aad82997644400147d0b31ec8880028f61663d911000557414c7b222000aad8298f644400147f0ab1ec8880028f21563d911000557c12c7b222000aac8258f6444001c3eca31ec888002a760863d91100074ac08c7b222000c9c63dcb644400187ecab96c8880032718d72d911000656b96c5b222000a3e8598b644400147b0b316c888002a7a0e62d91100054ec1cc5b222000a3f8558b64440014790ab16c888002a7e0d62d91100054e41ac5b22200b8bd8718b644400147d0a316c8880028f61462d91100054f418c5b222000a9d8318b644400195ae4316c8880038bd9462d911000746318c5b222000cad8718b6444001c5d0a316c8880038b61462d911000747418c5b222000e8d8318b6
  | 6 => 0x9d1f436caaa28219c3c76d95545047f17d0c38aa8a091f0f194715514123e9bba8e2aa28200c3f65dd15150439878cbba2a2a084e8f219545454101e1e3b2a8a8a8200b3481551515042717d0dbac82a08730f197759054101c5e432eb20a821cc3c655d6415048f47d0db2c82a08ff8dd87659054109c3f42ee7b02820087d85dcf605040199ee4996c0a0807331c932d814100726a9265b028200e8d424cb60504ab8eae232cc0a08fe1f21b75581410043f43ecab028200c5c73d9560504018d8e5b2ac0a08021fa1c65581410062e398cab028200c6c7219560504018becbb9ac0a080317197735814100637b2ee4b028200c6c65dc960504011f70eb00c0a084f0f1d554181410043fc2ae6302821387c855cc605040717908b98c0a08071b9c9521814100636b92a43028201cce724c8605040199ae4990c0a080393549321814100746a12643028200c76659c765900011ed03b9ecb200023d60773d96400047b40ee5b2c80008f581dcb659000317f0ea16cb200032b5c942d964000e6739265b2c8000ccd724cb6590001d1a84996cb200032dd0a71d96400065aa14e3b2c8000cd7329c765900019aa6538ecb200032dd0971d96400065aa12e3b2c8000cd7325c765900019aa64b8ecb200029da0775596400143e43aa6b2c8000a3f8454d65900030f90ea92cb200031bdc9525964000e6739264b2c8000ccd724c96590001c9aa4992cb20003a3509325964009d1fc32caaa4804dc3e651c5549007117b0db82a9200029da17619864009c3f42ee730c800087d85dce619000199ee4994c320007331c9329864000726a926530c8000e8d424ca619000156b0828cc32000a3d61e31986400055ac246330c80018f5878866190001d8a6510cc3201362f21d545864009e1f3aaa8b0c8000ab481551619000195e85b92c3200031bdc9525864000e36392a4b0c8000ccf724c96190003998e4992c32000393549325864000746a1264b0c8000ab584d456190001c6aa9a8ac320002ad61051586402af1b2a0a2b0c80028f4874c56190001d8a6510ac3200063d21d21586400047bc3ac230c800393c87551519000187eecaa2a3200730f997759064006c5fc3ac320c800f8bf865c2419000127f0ab8483200030f595749424009d1fc32a92848003c3d76552509000167700aa4a1200028f61253d95400062eb9ca7b2a800187f8754b65500018dae4a96caa0007339c932d954000666b9265b2a8000e4d524cb6550001d1a84996caa000e2fa1271d95400146f43ee6b2a80008dd82dcd655000193e85b9acaa00022fe1173595400046f438e6b2a8000c9f741cd655000159b0439acaa000a2f21d43595400164e39a86b2a80008df835c965500051b906b92caa00023de0572595400047a40ae4b2a80018bc87509655000193ee6a12caa
  | 7 => 0x5d731cf655040187e85b96caa08021f61e72d95411fd1f424e5b2a8200a3d849cb65504014bd07396caa08029760e72d954100637c12e5b2a8200c3f425cb655047f47d08396caa08028f61072d95410052f418e5b2a8200a5d831cb655047f47f04a16caa08ff8be0942d95410061fb9285b2a8200c3d7250b65504018bee5996caa0803175cb32d95413270fa1665b2a8200e1d42ccb65504010fd0f196caa08021f61e32d95411fd1f42465b2a8200a3d848cb65504018dee5196caa08038b50a32d954100637b9265b2a8200e2d424cb6550401c9f04996caa080317dc932d954100727b9265b2a8200c4f724cb65504018bae4996caa0803931c932d95413170fa1265b2a8262e4e424cb6550401c3a84996caa098b9350932d954100706a1265b2a820087e870cb65504010fb0e196caa08fe8fa1032d95410051ec2065b2a823f87e87cc765504010fb0f98ecaa08fe8fa1331d95410051ec2663b2a8200a6e82cc765504014db0598ecaa08fe1fa1f21d95410043ec3e43b2a823fa3e84c87655040147b0990ecaa080297a0f21d95410052ec1e43b2a8200e4d3288765504010fd0e10ecaa08661f61c21d95411fd1f42043b2a8200a3d8408765504014bd0610ecaa08029760c21d95410072699043b2a8200a7a8008765504014f30010ecaa08028fe1170d95411fd1e422e1b2a820087f874c365504010f90e986caa08028fe1130d95411fd1e42261b2a820087e870c365504010fb0e186caa08fe8fa1030d95410051ec2061b2a8200a6e820c365504014db04186caa08029da0430d95410053ac0861b2a820087e87c8365504010fb0f906caa08fe8fa1320d95410051ec2641b2a8200a5e83c8365504014bb07906caa0803934cb20d95410072699241b2a820087e8708365504010fb0e106caa08fe8fa1020d95410051ec2041b2a8200a5e8308365504014bb06106caa08029da0420d95410053ac0841b2a82008bf845cd655040117f08b92caa08023de05725954100c5e43a84b2a8200caf72509655040199ee4992caa0807331c9325954100746a1264b2a820087d8798c655040147b09318caa08029ba0a631954100536c14c632a820087f8758c655040147f08b18caa08730fd9172195410043fc3ec432a8200c6d72d8865504010fb0f310caa08028f61262195410052f41cc432a8200a5d8398865504010ff0eb10caa08028fe11621954132d3bc0ac432a821387e8718865504010fb0e310caa091e8fa1062195410052f418c432a8200a5d8318865504018dae4310caa08028fa1942195410051e4328432a823fc3e765086550401c5ec4a10caa0802cd20542195413262f3b66432a8263e1f64cc865504c58bcec990caa098787d913219541006a6b926432a8200e4f624c86550401c98c4990caa0803c350932195410
  | 8 => 0xa8b90c2aa1622f61d421855426d1e42a8430aa803c3d75508615500156f02a10c2aa15f275d332185543570e2a66430aa856c9d744c861550d3c38a8990c2aa007339c9321855400666b926430aa800e8d424c8615500156b09908c2aa1a38d153211855433f1a2a04230aa800ec53208461550015e300108c2aa00237e0d70185540146e41ae030aa8138bd84dcf60550b717f0ea1ec0aa00f0f5d543d815409c5ec26e5b02a8588bd8750b605500787aeaa16c0aa15f275d332d81542b64eba265b02a801cce724cb605500199ae4996c0aa003a350932d81540069a2a4e3302a800d34545c66055001a38a9b9ac0aa0023ee1d601815400e6739264302a800ccd724c86055001d1a84990c0aa0023ea0373d96410047cc06e7b2c82028bf8750f65904394790aa1ecb2080b279cd43d96410061e2a6e5b2c82008f681dcb6590401878a8b96cb208062fe1d42d96410e51e42a85b2c8200cad7250b65904c9c38a9996cb2098b8715132d964100667b9265b2c8201ccc724cb6590401d1a84996cb2099b8d15271d96411fe1e3a6eab2c8200c3f54dc9659040187ea8b92cb208061f21d52596410051fc22a4b2c8200c6f72549659043947d0aa12cb2098f87d53325964130f0faa264b2c8200ccf724c96590403998e4992cb2080393549325964100746a1264b2c8200c3d655d2519040399ce4994c120803335c9329824100726a92653048200e8d424ca60904031f30f104c120803b24c9209824109c3f43eeab048200c3f43dd560904010fb05baac1208030fd0b75582410061e206eab04820087f855cd60904270f90ab9ac12096e2f21d43582410061fbaa86b048200caf42dc960904010ff0ab92c12084e1f21572582410043f43ea4b04821387c87d4960904010fd0ea92c1208021f21d52582410061fbaa84b048258c3c7550960904018beeb992c12095f171d732582410062fbaa64b048256c5c754c9609040199ee4992c120807331c9325824100726a9264b048200e8d424c960904031f10e902c120803b24c920582410047dc3ac03048200c5d7394f65504050ff0ea9ecaa08028f61252d95410052f41ca5b2a8200a5d8394b65504030ff0ea96caa08031b5c952d954100667b9265b2a8201ccc724cb6550401c9ca4996caa08039354932d954100746a1265b2a82038bc845c365504014dd0531ecaa08029b60a63d954100636b96c5b2a8200a5e8398b65504014bb07316caa08661f61c62d95410052f418c5b2a8200a5d8318b65504018dae4316caa091f0f9d942d954100717b1285b2a8200e2c6250b655040166902a16caa095f179db32d95412b62f3b265b2a8200d4f724cb6550401c9ec4996caa08039318932d954100786a1265b2a823fa3e849cf655040147b0939ecaa08029ba0a73d954100536c14e7b2a8200c
  | 9 => 0x2d34b3a438d4d68000000001321c52e00220480694a22d2120b4100010b4290348000000001071b312eada0001ab94517b1f015333c22100a0d91b22cd4cb3f92d02100002c422b0fd2871cf0f314720435b3170002494991050cdbf144040846b08102b173121b5a25a0001340000002320002d517d0003e00000a0c533f60000000e10000001df0003140000003c70004da8000f934c80040e4d63ac31d4050980dd4c52aa4ee07a36e3820000c409bb062de112c163084390714e50004d10000000002ef80035f19a8000a71ad3523434183072bc0000003a3113b5829f0000342f1a410000d3084018a880ce000024bf415e00048100003d05549d0f194428606818900033012e116c1900000405c020070040080800500400819001000000000000020140081100e05000800000014028000060300280101000000002010018040000000040180e0100140500000002801801006024008000000440500201a008000120000140182000800c07802002030018020140080180001604c030010040100700701a03c00803004000018060020080280000800c0180001a000050000060180080d00202c0180500200c00008000018000020040040280203a0000000402600c0200a00402c0580105a00c0380a002000028060000001200d0120080b0040020040300000a0000000000e000038070001100e80001a01c058030080080080800c0380380201402002000008000038020040b40080700200c028070120000c006006010008000340140a00d018000000030000080500300600c0000000000c0000a0000040080000802001002000028000060020000080000e0280780800004009802014010018010100080a80701200003802000034090000020000d80000e00003002000008008000000000080700c00c0400200003c02804008064028060000000080000002003812008004020010000180080301a000008000060000b8000100000101500601c0080600201408800000000008010020000b80000000401001000000008010220200300900600000002028004020080060140080200c00800009006008028060040040180a0000000280001200c0280000c00c00805002000040050020400200000600004807006010008010260000001a00400000800006008018040020080100700e05c0080a0000fc000010020000000100201c0000001a000008120060200300000201000001000040008080040000080001a004090010000181000b02c028020030000000180101600c0200c00601cce724cb615500199ae4996c2aa003a350932d85540055ac2043b0aa800ec53208761550015e30010ec2aa0023de1d611855435d5bc22c230aa8138bd84dcc615509b4790aa18c2aa00f0f5d5431855409c5ec26e430aa800c3c54dc86155001878
  | 10 => 0x1b800025d20605e8001b42204eb00000000047704543342c0001610003771cd4cd0000ae0a50000010cc34528a0000001e827f1e500015a12427049b00000000000044e0003af0000ac06b1fc0032d83bc0e209e4090002a505180000005f4664ad9840612933d93c340412800043b27741b0002470003de22d0000000b038cb360000c34a00000000e03b54070000000000000002052df38e0002583200100003180000000172d13c908700011621605b0002a20003cc19c00000000043a4e80003802462e6064c242483ef90a9e40003a2000166003b7b00049a2340003034230004b43fd00001426241700000030018709500000031110c8000004ad0001ff00000018c2bf070b6017413d1b60e911ea7127d4d73f503245900000049f3ff0493023bb0e6ceba8f1670ea3fc14026a4dc9a14b943e26500003e8001b100008d0000001141fb0004d311a1554b2b943cf08f99e24a2b600029e18e1990002b13fb2fd00049c12337a3dc07e10a0000000000003ef07f0002ac0001a425513c06c3f01d810f11a9f330b00000000014a8ee0bfb6c3ce0160003a94140000000000000000000001ba00021e0f80003a14320004c81713723cb0002ff26734d05d0e64ea0c09ac07d0974880001be2a90000b228e1118000313e314f12a42511e39900011b8a180032400026e4af4aa0000be1d40600901e60002cb0001854b24c49d30500334504b334e18b43812d10c0800001eb24e00036a17a96680027e06625719319100000046240c00036b0ef49e0004bc0000978004d400000030f01f4e344c1bd0000b116e0270bc124bd10c59183e13a80000e72fe0b800025b09f1ed0a4bdd0000c94310f44e700049118000000493106d1aa4dc2252e833a25f08eba03b9344033b3e1393d69f600000031235e0df09a00039d4c00e892daee1cc3b24c42d31b88521dc06580024d48936132745e0eb29b0004b02374bf35400038a1c74542ae47f0002f42811a31761c00ab18144602634923139b3374823f589f80001e3b70004a40003ca0000004c91b52dd3664d595421204b37e40b4db2cdb5c11c393a9c0c5000000068b810b60a609ac5b26f34c0003d00d480030135bb9f0000fe4953460534ce84e04c0391f500022f00046e4701902272fb004008a2938503f4e0b9e0003c000017c000185ce41af88c21a38b0000000000000003d436947220200010bbbe24b2f347e145bb60401b00000469690001c801d34191914b1e94853ee4e38004550000ff24c45847337311f00037d4280002602394120001153930000bb3bf3871e31b732ec6447410d4b500005902123b2912cf4d52a01834c600000000000044940f00021f46f06e01b1203ed46846a10dabe0060d40f0063098b8407300000000000023c45d4d00370002ad00f07b0b5a3f20a089c
  | 11 => 0x3d380000039c00018d000329000175811b1541045a2db00019f0000004a636400c32d0000000000052424c10623eb27434242044848d1510c03c21a60001db34d8003210000002b50a59111264710938002e91bf00013a0004574bb1b90440003673e80000ca0000bf3483923f2cb727b2003c603028b00031300005c25243f15f0000001a93c444339a1301148000001f40004134602334ba4630673863531480b737440d2232f12ed3e20000110000d81943aa00000038f31f4a83700004340000002e448b0000000000002c00000004a13d700000000029a00040341d2514e695c38c00b4373d80002530003ec00000000000000000019600000031912100006ec930003b800033d0003f200d2970003ae00002d00013e06380000025000020d0000002352c104d3100000679792c700000000000043d0000004de46714d092c9445141f1001fa00047630e26901919704f00012f31e4a700944f1020000478000001460001a80002b000000000000016c21505411701c3621f72090003050fb92ca4f00043c0000002ae80db3b08b8000000a34e22ab3e50a130c40200006d8001d24ce3752642380080000002920642261270000001680000b42a81da1a00000004210fab1b32c3044b816d00023e4ae1b78003763df3320000b30f602f0c80003780000000b6800000149000071c4a2c24cc25c00035900004719a10980000047a1ef1d72ca0cd00000000047c0003da0000b50da2a427300000025614200000000018800007600000020100000025e0000000002f60ba0000000ccac52950509cb2a129603c0001de0e19430000001d60000003c100045c0000f082531a12c0002f208b3650000d617e0004b63500000aa0200000002b745627923002c32a4920990000e4963178000000299000338b163354e046c2664cb9090580b922e1f829d1c42824e60704bd81a2224450000ec2401ae0000004150002030c6c6516c9c110320b34a00004630a00036f2360db3958002183ea2d714a0000003a73d300027a1011700e580047b4ecc792612451c311d110c352750fa2c30434a50f220e057088ae14694423831a08000003ab0f6b8842202920f09411200026d0a2398abd00000ea6c0152d64dd4c7a3d41a0004ca9ea22a165096b4f3380410e44b13400650c23b012522807546d4bd3d182409c27c0f7807ba54ed1822f00f10000a83633340790758020513b139511dad92ce2543890000001e24841c623580000013b1f90000001374ec0c744d32b00027643626848719b2f904a0e52c93561ec0004e90000003ba0e2c8a1f100005a3d200008902800035544100008521139847504b8cf11308f23a2f73910f735d06f9a200033340142f00e2980000004c217500016000000000045f3970fb0002083f72940000129e00c139080700
  | 12 => 0x2780002c80002130d18000000000720000002800a930d3c54a94c71278130002e30000e84ca0004112a70000000353901b69d12f80000d51361594000d20a00d0150095b4a9924e78dc2b213288e06a4523472b818a3d500000012387440a00021c00000042630941c00019d3510120001fd00009b0001d010421d1223c48e380003a11b33900048f1352850004471861772ea31c3792720003f6b2f2d42af1e10830af4df4cf0000882ec2b926b4ac46117217a1101fe1ca21b2194300000de09202a3e709d13f2894da1ab33115702e4064962140001d93179060004be00015206c8f53f307c2e210e0963e63db00016f1bc03641e2a62cc3b40002ef33fa8428d0a789103e05d9f21380bd07820c3d62b43250d5b710fc0000001c942a0e34d80002c64271980001950183230002430a44a322432e3a5a5932844b4ab16a48e4d903828c13300000012900042e2f50000d73a637f2a300032636809300015815618f48c0d08422fa1af00042b0002e70000002ba3e407722c0ed04a9d548012b2e515088a0d10004974e14981adc9006f08233f0002071bb1ce4860c61080002bb17f00000016236d2fc0000001ee2633e7cc33223e90e9c7d44416415d37c3b305e0003bd0ad0563fa1e7023394886126aeb0004834784d23f83570004c880000000012b96b1413c82441c23fe3ad1a529003b21715b0cb1dd14c2b338f9a708ab962833cd14e2dc000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x40184d835c8621954137c8d2448650865504c3c0f645c9321954100513e5f624c8655040144d97189321954100583a59424c8655040160c965093219541317039d9424c8655040170491509321954123e0d1d881551515040348f9750932d964000721509329c76590001c85424c971d96403748de6154d45619000344f9754932d954000623dd1821cd65500050cc985c9325954000531245724c9655000188e87509325954000d2325d424c964c400144f9754932d92100051365d524cb648400348f9750932d9210367039d5424cb6484001c0d7550932d92100040f66054dd9548400103e98151765521000583656424cb644400148d9218f72d9110006836158318b6444001a898360062d9110005836486354b644400160d9318952d911000583654624cb644400160e9654932d911000583259524cb6444001a0c8654932d911036f039d9524cb6444001684964ca21d9110005a225932483644400103f985d475d911000583654724cb6444001686911c932d9110005a2640724cb6444001c0f72d4932d911000523a5e524cb6444001c0f7254932d9110007035c9524cb644400188e874c821d911000683615320876444001a893260021d911000623a1d32c836444001a0d854cb20d911000613e1783dc9644400188f84e0f725911000513a5d524c9644400144c97549325911000613a1d524c9644400184c87549325911000d2325d424c9644400188e8750932591100062321d424c96444001c0f755093259110367031d5424c9644400148d9218d72191100062360d72188644400188d8760c621911000683615831886444001a898360062191100058364863548644400160d93189521911000623219724c86444001c0f655c9321911000703195724c8644400148f97d8932191100052365c624c8644400160d95189321911000583a59524c8644400160c96549321911000683219524c86444001c0e765493219110005a1259328846444001688964c92019110006a221932480644400103d9815276551100040fa60541d9544400143591150765511000709150621c5544400148d9219372d8d1000523a5b7250b6344001c0f65dc942d8d10007031977250b63440014ca96dc920d8d1000487e6154153634400184d85dca42d8d1000523a5c7250b6344001c0f72d4942d8d1000703dc95250b634400188d84dcb20d8d100052364e76dd3624400148d949db73d891000523a5b74dcf624400188e86dd373d891000703dd764dcf6244001c0f7519373d891000631a1871dcf624400122f9855054d891000703dd774dcf624400144f955d373d891000703dd474dcf624400148d949c773d89100053264271dcf624400148f945c373d891000623a1f741cf624400348f9750932d90100072150932dd91004001c89424cb7644010
  | 1 => 0x1061140000520000000000e128003480118000019832932601c00000027ae62d345507e000cdbc00002380000004f0e9320017800bc863b9d92c03800000000080012a004c09f0e00000000000078c000001395cf6000000024158a68cc2000020000004d00000128027c00230023c9e00001c00000210013668000000000000cc005f140426e1d36945383900288009203400b803321b8e8161482d140038d80000000160000d800940000001960000020002a0000000000000000000007638440a0d1acf200069f0000000168002000000008800000006c00000f47d0dca80000390003500031a8a58b41800aa2b0028400001b00000000c1040000000240000001fc0000000785c0000050a456000007a00000ae0063070006a173c214007500128000031400002400000004e0007c641324000621b00175088d000711200028000001a00000004800000034000014900000ecd30000084005b00000a64400000000033a448650001180026001240007cb800ca6d8026704111e134104b001880059000000400000000171500f800004e9f8000048001020016032000000000000381c0200000000403020040c000000000000001430000100002000280400020000408020000c02010080400060000000020180400000080410020000026030300000070100801a85844c821d8554006b04c980087615500103d9815372185540050b64854dc8615500103d98151721855400703151724c861550e148d9750932185542e7035d5424c861550e3e04544c821185540068c151800846155001ac13260021185543852365d424cb60550b9c0d7550932d81540050da58549c6605500143696151719815400507a5854dcd605500183454a0772d96410040f660545cb659040142d9215172d964100703153724cb65904014c691dc932d96410040fa6354dc9659040142d92d5372596410040fa63545c9659040103e97e11525964100703d53724c9659040344c97549325964100583e51524c9659047f03c98595749464100513a5d524c9609040144c97549325824100703dd5424c960904d9c0c75509325824100e3221d32481609040160d9494932d95410058364c6250b65504d3c0e7650932d9541005c1245424cb6550401c0f42dc932d954100583650724cb6550401c0f7250932d9541007035c9424cb655040184e874c821d954100683611320876550401a493260021d954100613a1d32c836550401a0d844cb20d954100d2325d424c96550
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x4520100360100240da9151724c86155001510d10a8c004230aa800e80151326002118554006808a948ee4996cb2080240ea9d53724c9659040120753f28a9264b2c8272981284965093219541
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x4b
  | 5 => 0x4c
  | 6 => 0x4d
  | 7 => 0x124b
  | 8 => 0x138b
  | 9 => 0x94b
  | 10 => 0x94c
  | 11 => 0x94d
  | 12 => 0x124c
  | 13 => 0x124d
  | 14 => 0x138c
  | 15 => 0x138d
  | 16 => 0xa0b
  | 17 => 0xa0c
  | 18 => 0xa0e
  | 19 => 0x6
  | 20 => 0x130b
  | 21 => 0x130c
  | 22 => 0x130e
  | 23 => 0xb8b
  | 24 => 0xb8c
  | 25 => 0xb8e
  | 26 => 0x148b
  | 27 => 0x148c
  | 28 => 0x148e
  | 29 => 0x104b
  | 30 => 0x104c
  | 31 => 0x94053
  | 32 => 0x94054
  | 33 => 0x95393
  | 34 => 0x5253
  | 35 => 0x95253
  | 36 => 0x5393
  | 37 => 0x125393
  | 38 => 0x4953
  | 39 => 0x124053
  | 40 => 0x138053
  | 41 => 0x138054
  | 42 => 0x4e
  | 43 => 0x124953
  | 44 => 0x124954
  | 45 => 0x95254
  | 46 => 0x138953
  | 47 => 0x138954
  | 48 => 0x94e
  | 49 => 0x139253
  | 50 => 0x139254
  | 51 => 0x124e
  | 52 => 0x138e
  | 53 => 0x130a13
  | 54 => 0xa1313
  | 55 => 0xa1314
  | 56 => 0xa4d
  | 57 => 0x14d
  | 58 => 0x198d
  | 59 => 0x134d
  | 60 => 0x149313
  | 61 => 0x131493
  | 62 => 0x149314
  | 63 => 0x14cd
  | 64 => 0x105313
  | 65 => 0x131053
  | 66 => 0x105314
  | 67 => 0x148b93
  | 68 => 0xb9493
  | 69 => 0x148b94
  | 70 => 0xbcd
  | 71 => 0x2cd
  | 72 => 0x104b93
  | 73 => 0xb9053
  | 74 => 0x104b94
  | 75 => 0x19cd
  | 76 => 0x180e
  | 77 => 0x28e
  | 78 => 0x95453
  | 79 => 0x95894
  | 80 => 0x94d14
  | 81 => 0x95294
  | 82 => 0x95414
  | 83 => 0xd0c
  | 84 => 0x188c
  | 85 => 0x2c955
  | 86 => 0xcce
  | 87 => 0x170e
  | 88 => 0xd0e
  | 89 => 0xd4c
  | 90 => 0x1a0c
  | 91 => 0x10c
  | 92 => 0xccd
  | 93 => 0x170d
  | 94 => 0xd4d
  | 95 => 0x1a0d
  | 96 => 0x2d395
  | 97 => 0xcd496
  | 98 => 0xcd4d5
  | 99 => 0x171496
  | 100 => 0x1714d5
  | 101 => 0x2d555
  | 102 => 0x2d4d5
  | 103 => 0x202d5
  | 104 => 0x1542d5
  | 105 => 0xcc2d5
  | 106 => 0x1702d5
  | 107 => 0x29496
  | 108 => 0xd0cd6
  | 109 => 0xd4cd5
  | 110 => 0x942d5
  | 111 => 0x2c215
  | 112 => 0xccd16
  | 113 => 0xcc202dd
  | 114 => 0xcc2c21d
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 47
  | 7 => 777
  | 6 => 1600
  | 5 => 1263
  | 4 => 165
  | 3 => 7
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
  | 8 => packedAt gbK8 (1376+((h/22+packedAt gbK8 (1222+(h % 22)*7) 7) % 80)*7) 7
  | 7 => packedAt gbK7 (32433+((h/307+packedAt gbK7 (28749+(h % 307)*12) 12) % 2153)*11) 11
  | 6 => packedAt gbK6 (84072+((h/606+packedAt gbK6 (76800+(h % 606)*12) 12) % 2643)*12) 12
  | 5 => packedAt gbK5 (79775+((h/478+packedAt gbK5 (74517+(h % 478)*11) 11) % 1893)*12) 12
  | 4 => packedAt gbK4 (12126+((h/64+packedAt gbK4 (11550+(h % 64)*9) 9) % 371)*9) 9
  | 3 => packedAt gbK3 (575+((h/2+packedAt gbK3 (567+(h % 2)*4) 4) % 9)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3ff03ff03fe07ff83ffff807f49f467d19f3f3
  | 1 => 0xc1ffc1ffc1ff83ffc1c03ff80b68b99ee67d9c
  | 2 => 0xfe1ffe0001fffc3ffe003ffffc70c1e3078e1f
  | 3 => 0x1ffffffe00003fffffc0000f80fe03f80fe0
  | 4 => 0x1fffffffffffc0000000000fff0003fff000
  | 5 => 0xffe0000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x22004500260044802548812a003022c08b0b1
  | 1 => 0x414140b440a88298408192b021281894625594
  | 2 => 0xb41aaa0211156826b40225454c50c143050a0a
  | 3 => 0x101cf32ab4042037392b00604e80ec03b00f40
  | 4 => 0x211f3dcf39de7302100c01818ffd0003dfe000
  | 5 => 0x3988200c20184204203006060ffef7f8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeee8eee8eae0eeeaeee8eee8eae0eeeaeee8eee8eae0eeeaeee8eee8eae0eeeaeee8eee8eae0eeeaeee8eee8eae0eeeaeee8eee8eae0eeeaeee8eee8eae0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36785
namespace PEqualNP.Outside.L_meta_36785
open PEqualNP.Outside.L_meta_36785.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 29 := bs2_3_0
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
theorem bs2_4_384 : Interval s2Atlas 4 384 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 396 := (concat (concat (concat bs2_4_0 (concat bs2_4_32 bs2_4_64)) (concat bs2_4_96 (concat bs2_4_128 bs2_4_160))) (concat (concat bs2_4_192 (concat bs2_4_224 bs2_4_256)) (concat (concat bs2_4_288 bs2_4_320) (concat bs2_4_352 bs2_4_384))))
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
theorem bs2_5_576 : Interval s2Atlas 5 576 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 601 := (concat (concat (concat (concat bs2_5_0 bs2_5_32) (concat bs2_5_64 bs2_5_96)) (concat (concat bs2_5_128 bs2_5_160) (concat bs2_5_192 (concat bs2_5_224 bs2_5_256)))) (concat (concat (concat bs2_5_288 bs2_5_320) (concat bs2_5_352 (concat bs2_5_384 bs2_5_416))) (concat (concat bs2_5_448 bs2_5_480) (concat bs2_5_512 (concat bs2_5_544 bs2_5_576)))))
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 21 := bs4_3_0
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
theorem bs4_4_96 : Interval s4Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 99 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 46 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
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
theorem bs5_4_96 : Interval s5Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 99 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 46 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_4_96 : Interval gbAtlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_128 : Interval gbAtlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_160 : Interval gbAtlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 165 := (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160)))
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
theorem bgb_5_1248 : Interval gbAtlas 5 1248 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1263 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248))))))
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
theorem allgb_6 : Interval gbAtlas 6 0 1600 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))))) (concat (concat (concat (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960))) (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))) (concat (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344))) (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568))))))
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
theorem bgb_7_768 : Interval gbAtlas 7 768 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 777 := (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat bgb_7_288 (concat bgb_7_320 bgb_7_352)))) (concat (concat (concat bgb_7_384 (concat bgb_7_416 bgb_7_448)) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))) (concat (concat bgb_7_576 (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768)))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeee8eee8eae0eeeaeee8eee8eae0eeeaeee8eee8eae0eeeaeee8eee8eae0eeeaeee8eee8eae0eeeaeee8eee8eae0eeeaeee8eee8eae0eeeaeee8eee8eae0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008373992 * 2 ^ 32 + 4008241888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36785.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.and,[4,5]⟩,⟨.or,[6,7]⟩,⟨.and,[0,8]⟩,⟨.or,[0,6]⟩,⟨.and,[1,4]⟩,⟨.or,[2,11]⟩,⟨.or,[5,12]⟩,⟨.and,[10,13]⟩,⟨.and,[1,14]⟩,⟨.or,[9,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373992 * 2 ^ 32 + 4008241888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373992 * 2 ^ 32 + 4008241888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36785

open PEqualNP.Outside.L_meta_36785 in
theorem PEqualNP.Outside.L_meta_36785 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373992 * 2 ^ 32 + 4008241888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373992 * 2 ^ 32 + 4008241888) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
