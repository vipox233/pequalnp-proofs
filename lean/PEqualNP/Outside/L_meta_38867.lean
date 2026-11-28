import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_38867.Model
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


end PEqualNP.Outside.L_meta_38867.Model

namespace PEqualNP.Outside.L_meta_38867
open PEqualNP.Outside.L_meta_38867.Model
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

def SBf (j : Nat) : Nat := [8, 5, 5, 7, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_38867

namespace PEqualNP.Outside.L_meta_38867
open PEqualNP.Outside.L_meta_38867.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x400012400800c000004d0c92010023000002c0004fc41fd43fd40fc31fd10fd32fc32fe32fe31fd42fc10fe10fd21fd41fe42ff42bc40fc21fe30fe40ff31ff43fc30fe20ff10fc42fd20fe41dc31fe21de31ff40ff20fc40be40ff21fd31fc43ff30ff41fc20ff32fd30fe43
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x285bc53902f8a9195f94843f799465f7415077e83205f95320bfa9a217d54086fea0a1df54a20bf280417c53082faa221d754e10ee29a217d54442fca3a15fd5331ee994637e54107de8410df94840efa90637e52cc6fca4217dc4210efa84637c5350ad8a4884f55021afa9a437e50cc7bc63205f14c21efa1c637e520437c63205f94e42bf28465be42903bea6a0f70c410efa0863be52102fca1215f14931bfa92617d538877ca5205f94431bf2a44374514837c80905bd4910ef18843de520c7f040086f90840df18881bf52902fea299670c640be29281de430cb7e8621df54b30fc282837f51482fea2a15f94c20bea8e81bc40482f6a0a0df54843fb082217f54882fca6205f54420de18881de528c6fca9105f54d21bf288617e520cbbc6290df54e41ee21c63de510c6fca5205f94440bf28087f731842faa690778c932bf2a4635f53443bc8418f70c520df2a6617c53c82f8a7887dc8521f790041fa300c2f8a918f714831ef996617e5110fbc62205f94040bea9e215e510c6fca5a07b08620bea88813e54c82fea2a05fd4c20dea8881ec52443de8521774cb30dfaa2417d5090efca321ef94440be2a2657d53042f8a2a0678c440bf2a243bf425077c64205f15330be28285dc53507da4210fe50040dea1a83be51902fca6905f54f42af29841de314c3f240107754e10bea86857f524c7e863085f54241bfaa2617c5250efca6186f90330bf29083ee21882faa5a0778c831df200217c54c43bc63a05f94640ee19461dc428c6fca4885dd4530bf2a241be40083bc62185fd5221b7a9283bc51902f8a9905f94732bea98837d540cb7ea890df95321bea8687bc40cc37ea8985f94b41bf28441bc544437880105fd5010bf28c65de438cafaa1217d08610df990817d5310afaa3184fd5130bf28421be40c42f8a2985f94442be28a857e52cc3b863987ed0140bfaa043dc31082fca2086f95031f710841bc400437883205f54442aea9e857e540877aa32077d0631bf28683de31c86fca2107790e31eea1865bf42d06fea4885f54640de20621bc42106fca410f714d21ef28463dc53482fca8184f95021be282837d53087eea2986fd0a42ef190617d51842faa1196fcc640bf29e85d431842fca618f754f21fba8a41de318437a87a0efcca40ef18e41dc31c437c83206f90110bfa9c417d529077a85205fd4f10faa0883df528c7ee43085f95031afa9a83f7314c77863207bc8220bf29e81bc41102fea0997ed4121ef99063ee320caf8a8885fd5320ef21e617e54cc2fca320df54221de20441be411037e8720770ca31de202217e50d0af8a8985f94f219f2a0637d500c7be60185f55221de99481f820c437e62205f14d10bfaa2637f54c86fca8085f94630df204417e5410efca7087710431f7908433c54443bc8218dfd4f21
  | 1 => 0xe53486fca6216f90210bf296217c548c3baa418f790c31dfa0883de500c6faa8985f54831ee18e437c53486faa420f754231be28a877e50042f8a818fbc8621de206417c50487e8a2906f10210ee284637e50ccaf8a6a0df15020df204617e54c42f0a0a0efd0240ae29a417f544caf8a8087790c43beaa0215e53d0bb863a05f54743bf2a041df318c77ca810f70c720bfaa063bf53102faa898f74c030ef18a41be54c42faa0216f14440de29081dc318437e80204fd5121ee2a063bc53102eea2905fd4c21be2a663f731042faa9907d44010bfa82837f514c2fca3215f94e20be2a061dd530837c43205f94b439eaa665d6510c6faa7a0df15021bf28061ba50102fca91977d5031cf18c81df4350fdc40905f95042bf290637c540cb7ea8885f55030de204617f520427aa9907d14530dfa14817e51086baa7a0fec8010bfa9287fa10043baa518ef90140bea9c857e5010afca6885fd5231ef21a617c530437c42207ec8310de19081ef4250afca5086f50e40beaa621dc548c6faa8905f54830dfa1081fa40103b863187ec4210bf2a2615e53c87ba64195f55231fda0621f641107b86310fed0010dfa1a837f53483be64197bcc820deaa0637f52506faa9985b14930bf29e836f524c3f661184f553109eaa661de548c7b8a018df94343bf284877d53c82b8a6a0df94e41f621043f431042f8a898f78ca31efa10637e50c86fca520ef95332fa10821ef42886fca5195f15220beaa2657d549037ea7206f50c43beaa243de304c2faa921df94a43afa9a41bd40102faa4885f54041beaa483bd41902fca020ef4c640bea90217d53083bc63886f90a41dea18817c544837865205f55031f629261bf419077ea4205fd5110ba28a61bf4210afca888770c540bfa82857c53c86faa7a05f54840bf29843de31cc3ba6218ef50440be2a6657d53102fea6a14f15120ceaa063fb20883ba8618ef548409faa221bd53103bc62106f90841bea9463dd4310efaa718f78c410bf2a065bc52903ec4210cf55031eea0863d431042faa021df15321de988815e53d07baa818dfd4d41f7a92617d51cc3dea4885fd5030dea1885be32903ba8518df54732ef29841dc320c7bea690dfd4d40cea98813e54c43f260187794f42bea9c41bd54c82faa7085f55232f7210857e51c837aa810df94032bf28883de328c2fea790774c831ae29a437d5290f7e82206fd0e42ee19061df328cafea090dfd5230eea98817f534877e87a0ef50b41bfaa0653e54ccafca9997bd4941bfa9c215d53103de65105f54a10beaa485f721043bea6885f14143bea84637e548c37ca7205f94241aea98417d50ccafea710f78c620ee20c63be4350ef8a098f750d30ef20c637e53c83be6518df14e21bf29c81ef324cbd842105fd4940be29261de31443f681205f55020df21
  | 2 => 0x20080e8082c0334ac369f40201c11008f901d64088090800309c020080508019008000e8af82c02119cc0001203069008340080b058000000213407014000201b004000042e7080100c1e010000152b0003e0b80c38c001f00500dcf00000004000140d36805088000285b22000160002dc855a80f060040a00402c020024354401000360054f5782813cdd000001445a238060bc00254100005a0382009009028160ad87018000000f0180e0000f078743623c0080e0202701804014160d405014206e42f6e9092681858cfe1a8102cc07000000bc140300300c0009000000010001b760346902e0cc4f01631350c600002034070dc300a80267c00028190108b00004030000000205c054f008004070580c0583d0280e00000000e108038000a10002809426000f0000010ac09074c3bea9c65de314c7bca818dfd4131ee294637c53503bc63186f08440dea10813c544c3be6218df14532de99081dc31882fca998f70c510df28081bd21103f220085f55230eea10633e54cc2faa190f754f42f6190417d5190efea890df94f10bda8243bf43103bea690778c621de90c817d52d0f788520dfd4543fc206217c5284378a89077d0a31be28a417c52506fea8105fd5330bf29463dc31486fea6087ec4110eea80637e53107f0a090ef15130ae29a217d518837a872177d0c31de10c81de53d06faa510df54720de21c817d54c86fca318fd4c431fd10041de31502bca7085f94621beaa6637e544c77e42205f94e43ee18c81bd42507ba8718ef10c40af298817f54c4338622077cc930fb90c43dd548c7ee8320cf94040bea8065be53102f8a4085f94240dfa1885bd4210af8a9087ec8120bea8e857d54ccbdc4290df94c32ef29881df548c6fca110df55220be29221df308c2faa1a0cf94240dfa88817e510cafaa5a0df54331ee21863dc31087b862205f94743fda8283f7318c6d8a4a0ef90030ee992617e5290afaa790df54a30be29c417e53886fca3107750631f619441be439037885205f54e30bf28e817f54482fca1186f55330de202615e518c6faa2196f90130bf280637e528c37e8721f794f21bfa96217d510c2f8a5887b50842be29c21f521087da64195f94021de20061bd54ccb7884205f948309faa2417e541037e43205f15221cf29881bd53902fca9086f54a40de2a243dd53d06f0a090df54b10bf2a265f840042f8a6905fd5332beaa4217d53442faa598df54a40bf28e61bd54c43ba87197b14941bea8c857f548caf8a890f70c430dfa8c817c504cafaa3195f54021df2a6417d53903b88418f70c530eea1e617e508c7be8721fb10a21bfa9421be41506baa790dfd5210bf29887b840043bca7084f15121dea0883be431037c81907dc4010bf29821f6310c7da40106e10310efa8063fb304c3bc8518e795031bf290417
  | 3 => 0xf002004c0ac45f0090d08405008040080006413034a8028009101d0983c2ac05108160
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x54210a9e6314c409e594400423f64549109bd95210863e60953329798e544823d6414c109d185544c25e631532197194314831e6395021aed8121902776155132ec084400423e6494a10d314a304c23c65484408f5942110275650c41097d94311023d6414e218f994544c33754d4520cdd46404823f6548640e68c440042756508410d594431cc2b960c8440d390c524c25e6394241c7d50534823e6494d109718d518832c54149308f990538873b42141419e580530865d65d04319b18954442766194d208f992518c2f0604842197987534833854c4110c754e52103d03108010ae583411025f6355131e5952510c75a3114121ab98b519026c625403197984534825d63d4520a759332cc23d6414f108fd91508c63e65151208fd9153486756115020ec984400429d63c8440a759031cc2d663c8610c714e404823c60151109798f548423f6454221da148505063d6494410a7990528c67960d53318f592518c31f53101109d185534832f5414910e50c6408431d548c720d554431c832d5214840e60c440c429c64540319ed81534876452841109e181534865c6354740e6101300c29e63d0a40b5984548c6776154d209b189534425f65504319758e524431c548c510a7d8d519031f6555031cbd53524c3d031d0010d3d48314c2b9600c8408fd91510835543145308f994211023d65cca408f593504ca9d63d0842d9d48514c355510c740e654e501025f6550c438f992544c23e64150219ed81524425c6154f4297185531026d62d4f109758f5150a7a60951218f996404431f540c5218fd9150cc71c540c521ab988539032c6255021c7952510c65c6354021c754e421026d6215231d3d48314426e62d52109798e534831c53101109798c540427661d4f208f993528429c63546408f9925308395640c4109e98354c871c53d0d419dd85524423d64145329798e540876852d41418f19150cc67b6055121b6181434c23f6454d20b9185200825e63d4542cbd48404c23e60151108f996404c29d64d4231cb548421026f6255110c754c400826c6255130a798f511031e63953108f592528423e650c440d6d4c50486cc6250431c794d43d071d54d4031c7d4e40442ba60144408f593528423e6095031d50c6500423e64d4b109ed95200823e6494e10a718d211032f5210110d5d44314c36852c41109758e544426d650c8209bd89500c73754d45309798c5050a5d6314810c7d50314425f635464097596310834f5314941d5d8c514c29d64cc8329ed81544ca9d64cc930e5552510c65d63141428f990530865d6510c31ab58b4310a5e6315030cb153524c23d6494910a7590314c3954110431c7550320c79031100108f59352c429d658c440d6d4f50506b66114840dad4b50506ba60c8440ce508505063d6494c3097596430cb3854d4121
  | 1 => 0x4337541453097d95310c6ba6014640a7993520c63d64d4121a758f429023d64d4f1097996314865f63547409798f54c86786054442cb14a41506ba60d4840d518c514827561152329718d52906bb6050440d3148314c2d96014831d5144314823c6454810ce594400425e650c520a7593500c73b54141218f59052c42746155132d3d4a314c32d43149419d58653482786055131a7990520c6b86050441d5146304c33454d4520e68c440c425e6395320c755031c431c548c521cd144404c31c5414d109e98354cc74f5294a318f992530cb385414121cb9494290339541031097596430c66e6295110ea1012008357510c52097994534865d63d5020a7d91500c65c658c520c7150534831f548c5218f592534423d6494f21e658c4004395640c6108f994219026f6255130d598f514831f540c5209bd89534431c63550319718d51d0a9f6350440cd14440482b56114840cb153524429d6314840ae983519029c63544408f994404c3396510310b3189500c756431453097d8d511033451901309dd9510042746155120c7150314c26c62551319e181544873751101209d58753c833454145309798c548825e63d4b109e980530865f63551109dd85544c31c31940409758c540426e6294d10d60c7504874c5388120d614f505067b60551319798e520871f548c5108f596540c69c6454a31d5d4c514831e548c730c7592530823c6454d10a7d94311025f63540219b588540425d6395310c7592538423e641481097d9431082ba600c8409b98b54cc756518c630c7d4c404825d63951328f992544833754145209718d51c826e6294910b518d100431d54540318f592530cb3a6094040d354f320823e6414c109798e5088756510c430ec103100425e63d45209dd95411069e6095031b5d85420c71e540c421ae983529034c52cc930b358a430ca3e6494410d3d4c524423d650c440cb149425065e658c520a798c51102cf6254031d614c505071e650c440a7d8d419031c5490d308f594319033451901209b98b53c427b654401097994534825c6354420d5d85538435563d4520cbd50524c3645214530a718d419029e63d46409718d511023f6550c439798c52842776154032a7185531023c64549109e583540cb3b43141419798c54083b331100109798e54443d031c8010c7d5353486cf62506319758e509063d6595021d514c514831f54d4d209758f52c425c6114d10c755031cc31c54d4d21c754d411035453d4520d314c524425e650c521c714c404825d6315321e50c4408423e64949108f99053c4357510c540ce994400425d63951219dd95310c63e6494820aed81211032c5210130e5990310431e53940408fd95411073b6414141c7d4e40482b8604c840a7590528c75753d45208f982540867b6055110a718d411032c52901309bd9
  | 2 => 0x548c520b5984520c63d65cc840a7d96311027b654c030b3988548c67b6054442b5185300c25f63551208f980544871c548c530c794e408423e65901208f592538423e64d4f20ec0c4400429e64cc831ae181219025e650c510b3588548c71f5414d21b598631042d661d4a31d314f525067a6094d21a798c521026e6215010ae980529029c6354a408f99052c439a6310010c794e400823d6494d208fd91520425e639531097996314423c60550318f993504c71c5414d2197d8d5448757518c520a758f519025f635444297d8d51d0b1f5414d10ae99320043545384110c78c6501025f654c8329e58354c869f63544408f99053882ba6014c40b6980520c71e5350c40bc185200831e6494c20cb553420869e6414031d5d8c514829f6348440c7150314832f54d4910d9d4b514c23e6510120c7992538431e548c421a7593328cad561108318f593530865e63d50209d986544826d62951309bd8954487566194431ae982400431d5390c40d3149324c39a5394040c7553430c69e63d0440d68c7504871d5390210d314a314c23c645422197997324c31e63953209bd89511025c6355120d554431cc26d62d5331e658c40c429d63d0b41d3148314421d650c440a7593320c7983194040c7594311025d63d4a1097594311029d65950319758e544c65e63152218f596421071d531484097d8d52906b46150d419ed95401023e65cca40a758c5290355530c610c795031c429d6414031a798f521025f6354420b5987540c63d6494620ba181210869d6314440a7993508c63f6454d10e5990318432c521011097d8d5190a3e64946209e59420042bb604c440ab588511023e65101109758c548431e5450f30a798f211031d650c6408f195219031d548c730a798f219023d6414e209bd95200825d6315220a758f42102d66094431ce59350486e561108218f993530875b53d4121cd150514826e62951309b18951102ba6014840a7986311025f63548108f592520825e6394010ae983311023f65500409798453442b8604c4408f590530865e6314c209758e54c825e63d4a10c7d95531031e540c720a7d8d219031c54d4d20d5cc8514c29e63d06408f592534865d63d5210a7d91528c69e64d4031b6d81410c65c6354810b3189300c23d64d41319b588530423d6414f2097d96311036451881209798653d0a3d6508640a798f421031d53544408f191510831d540c421b6181410c63e6495110ae983539035b53141419758e500423e6414f20a7593520c65e63148108f99431902d661d48318f990540c71d53d4440d3949328c756510c720a7191508c7d03184010c7552520c7d1600c410c71535344355650c4108f191528c25e63d4540c7d50314c2d5650c6109b98b540c3b161100109d586544831d5310840ced8154c434f528c510cb14a404
  | 3 => 0xe4097d8d51c833b6414121ae19110042766115232c795031cc32c5488521c798e540c6d86050631a7993328c75853141219718d544869d6594c409758f51502796584010a718d219039a3194040c754f411031f548c530d350c524c34c528c5108fd91500cb2f52901109d986544c25e6514d10a7593328c7c431484218fd91528c6af6250440d3189530831d5494431b318d200823e64d4f1097d95300c394311001097d8d518831c548c520c758e540871e548c7109bd89544c63c6454d21ce904505069c6055031ce99350486ce62d4231cd153514c39a6310310cb150524423e64145329718d5110a3c6454231d614f504874c5314941d60c450486ba6194040ae99320c42ac6250640c758c544c23c6454a31b3d89410c63f64543329bd95320ca6e6215231f8084200425c63546408f19153482776155120e60c4400423d64d4f209798e52c42e9600c820ab58b519023f64543219e582534867461540328f590520433943141418f191500c63e64951219b58a544429d63d0640d3548320c6bb604c840cdd46404c33864141219758c528423e6494c308fd91528c2af62544409798e534427765484218f1815408796610c440c755031c825c6354642d3d4f525071e548c720b3588500c65d6394821c754e501023f6548440d5994310426f6254d209798c548425f6354a40a758f52102786055132b6d81418c67a60d503297596530833a5110010c7552310865e6394d21a7594311023e65cc84097d9631083b32110010d914b514c31d6494f21b598f210429d63d04409758e508865d65d0a318f19150c865f6354910d594431d03943190010cbd0c52506b960cc4409b994524437321141218f9945448754518c530b9189100425d639502197594310825e6394910a7590520c6d661d5231d3d4f524423e6494d20c758e54c823c6454232a758f511029e610c440b5984528c65d658c830ae181211035532145309d586544c2ac6448421c7550520c71c540c510f4980310425d658c440c7552320c6e86244010d5146314823e64d4132c7994319025d65d08319b58b540c355650c6109b594420863f6454031ab18951102d66115031a758f42506b965103109758e544837051c8120cbd4a529032c52d0941c794c408423f655084297986531025d63d5321a7990540c65c6354a40a798c5290396610c640c755231c423e60d5121b5185420c66d62d5210b3988500c71e5310020ae983531023e6515110c799253c863d6494c209798e54486766115020a758f4290a776154d109758c54886796095121c798e54cc2af625064097195434c36a21141218f993504863e6494f218f18154ccb4c53d4910c7d53534423e6494d21ae983511023f6454232c758e54c423f6454021d3548520c6ba6014e4097986530831d5310210a7d91508c71f
  | 4 => 0x14425008770000612c1300016020000480d1603e4085a00c2543023000030000100c0100c1006c04004020500100422248000880602000004060880501088010472bc2f000000000414c0000c0c024220206505c050040f000002c8030083518c2f00000000000ac0803800040ca0386a0080000032000000461131821010020340002c1913dc51f80105c02058a10683b05c041fc012e40003c2503007054010040b01c0000800030200040f018210300c0008a0100104c0504800000020000d048030900004406038050f00000804000090c049000000180102809004530040f8e82f00404034420000007005004020196d2b4300646300809018010045701403000000440800008000000b4170001f001d50004a00c460380300616005bb00c000bc0303c2001c0d010120640380018000000008a0ec010000600c040e0000180100402024000004b0280e850000fd31000dc028050680e0000202004034b714c1420c000000389404020074081b010010403d124091090600c41010500dc0009c0201402000020d80001802084080ec010004200400000c91381300c0c01c0a028030040e8901797997428c6ac625044097185530825e65d08319758e52c4354510c540b3189418c6cd62d4231c714e404433b54d4121b5984420c63c6454332a7986531025d6315020c7951430c6ae62144408f19150087d03110010cbd4a404c26d6294d10ab189411065c63551109718d524426e6214c10a7d8d529029d63c86408f191500cb375110130dad48505071d53900208f99742506ad6214
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x458e046808008540800600000020118702040038224103000048400000000e000020000681000000500000020024003040430392aec188810843870590514cb0caa2c029063641d1600c410d22c6b088008499760c4400420ebb4a620421381c1611082183aed2a063904e071580320820ebb4a620041a218c4048020d40c22024010499760c440c42c838ac620021a1190314842183aed2a06210cb1760c440042c939e4220021701c9600c410b40e4b0880084d070584420c712a92c229081491c54314941a28e2a9a822060d5318951102c8bb06220021a499031c8010930e0b26649860d6414b324c2c839ac220021075da650c440c1ac829062985307150c50506c83828220863a49d83110010b08e4a088218d93760c4400428a38aa6a8881521c143149308a8e2b18a0a159070590310424a38ac7a1283465cf4214141d10c4202601864952580520c70aa9ac229081a45d83110010c1aa8312a018d1574cc8514c20ebb0a818a612c1c5600c84083aeb31e4220592718c4400430ab2ac818821b00c46048421a30e0aa2a018c91760c44004348b22c0188218358c52d0941aa0e0a18a2986196558c40043483088098061261c1640c53083aed2a0638860d53189411024abb06220021345d83110010
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xc3052c000000070001a08805506254031a0880590520c5308918799031c8010c81641c9600c410c81631c96110010c11651c56310010891869cf2110010a048158c52d0941a048154c6250440a048154c6254440a088059052cc930c11651c1640c410891879d83110010910815cf4214141910805d33214530
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 820
  | 4 => 894
  | 3 => 68
  | 2 => 15
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (i*5) 5
  | 6 => packedAt s0K6 (i*16) 16
  | 5 => packedAt s0K5 (i*27) 27
  | 4 => packedAt s0K4 (i*38) 38
  | 3 => packedAt s0K3 (i*49) 49
  | 2 => packedAt s0K2 (i*60) 60
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 7 => 2*((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/28+packedAt s0K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/273+packedAt s0K5 (22140+(h % 273)*10) 10) % 820)
  | 4 => 2*((h/340+packedAt s0K4 (33972+(h % 340)*10) 10) % 894)
  | 3 => 2*((h/64+packedAt s0K3 (3332+(h % 64)*7) 7) % 68)
  | 2 => 2*((h/19+packedAt s0K2 (900+(h % 19)*4) 4) % 15)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffff01ffffc0fffffffff80ffe3ffe3f
  | 2 => 0x1fffc07fffffffffff03ffc07fffffffc71fff
  | 3 => 0xe03fff80fffe03fffffc0fff81fff03ff9e3c7
  | 4 => 0xffc00000fffffc07fffff00001ffffc1fe03f8
  | 5 => 0xffffffff00000007fffffffffe000001fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x224a450a211c4891402cb2d2a25886521a6e1b
  | 2 => 0x8909314522491228b01554854ab18a4c514ed
  | 3 => 0x5a230a2694483a44d55409ab1135a23969a346
  | 4 => 0x933a2c58e8912077669a603261c6cf11be03b0
  | 5 => 0x1c3c3060f0e1c387b8e38e3c78070c21f7d800
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0f0c0c000fcc0ccc0f0c0c000fcc0ccc0f0c0c000fcc0ccc0f0c0c000fcc0ccc0f0c0c000fcc0ccc0f0c0c000fcc0ccc0f0c0c000fcc0ccc0f0c0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_38867
namespace PEqualNP.Outside.L_meta_38867
open PEqualNP.Outside.L_meta_38867.Model
def s1K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x140400076906f32d843b8877906c32
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0xa441482310d208e43886990732
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
  | 4 => 2*((h/1+packedAt s1K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt s1K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt s1K2 (104+(h % 8)*2) 2) % 4)
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
end PEqualNP.Outside.L_meta_38867
namespace PEqualNP.Outside.L_meta_38867
open PEqualNP.Outside.L_meta_38867.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xac42
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | 3 => packedAt s2K3 (i*16) 16
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/1+packedAt s2K3 (16+(h % 1)*1) 1) % 1)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xe07fffffffffffc0fffff01fffffffff1f8fff
  | 1 => 0xfffffc0fe03fffff0781fffff03e07ffe4fe4f
  | 3 => 0xff81fff0003f03fff801ffe0ffc007c0f8f38c
  | 4 => 0x1ffffffc003fffffe0000fffff800ff03f0
  | 5 => 0xfffe0000000003ffffffffff00000000fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x29044482440840802912520914429452098495
  | 1 => 0x421888648952914b02a0a4b2623422ac643a4a
  | 3 => 0x852d5121d5a456d558513ac8be905706b8d38c
  | 4 => 0x1651a24919069b6694e40c90cb396208f60360
  | 5 => 0x1861c38e1e38e3b8e779cf1c0c218430dfec00
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaacc88aaaa8888eeaacc88aaaa8888eeaacc88aaaa8888eeaacc88aaaa8888eeaacc88aaaa8888eeaacc88aaaa8888eeaacc88aaaa8888eeaacc88aaaa8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_38867
namespace PEqualNP.Outside.L_meta_38867
open PEqualNP.Outside.L_meta_38867.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x2c18a0400000000cb000100100541000000185180000fc41fe21fc30fd31be41bf40bc42fe31fd40fc40fd42fd30fd43fe43ff30be42ff21ff43fe30ff10ff31fe32fe20ff20fd20fe41ff41fc42fd21fe40ff40fc10fc31fc43fd32bd43fe42fe10bd40fc20fc21fc32ff32bc41bf43fd10ff42fd41
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x8000048080814001420a81400740c00c4240c000800200000000058540408301c083c540004380408006820000000080400000000180804002008584400141130180448000801cc0000000800144a78a4a1cf55020cea1e639d5310a7aa9204f94642cea1c613e540427ea8994f150219f2a0815f53442b8a6904f94b439e28a873e5210a7aa910cfd41438ea98853f544c67ca9994f15310af29841b6511067ca9185d94430baa88615d530827aa8184f151319f28e873f54c42bca6214fd52329f2a0416c524433a86185d14520afa9a413d50d0e7ca9104f950439e2a2215e53042eca3995b94b319f294853d54cc2dca4185754f21bba8a419d434c73ea6a1cf15232cea1e655e53886eaa2106794c41aea9c433d531063aa7a04f550109f2a6633c544827ca320d754c419f290833c548c67ca220cf94a419f2a063ae5210abca790cf540429eaa4873f544867ca9984f54241aea98859e5310a7ca990cf553319ea80833f548c67aa720db548309f2a2613f544427ca8194f55332af29e813d540ca7aa6215714d109e2a2439e53d03ca4210cf952109fa9a819d434caeca2104f94b40dda82816f524427ca2215b948108ea98835d53042daa4084f55321af298833e5488678a2a05754f409e292813c544ca7aa7a04f55031b6a96633d5090a7aa9084f552209f28e817551ccb3aa7a04f153209f2a0613f54c827ea8904f552309ea9c853d544c33aa620cfd5021
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x100800040200048000224000487d8d5090a1d63952208758c525031543547328758c51502946150d318758e5190a1d6394a418758c54c821c6550d318758c544861f63542418758c54c430d43548308d987548ca1d63150218e5805408634615513087195434ca2c62551308b98b548c68c6250d328758e548430d4354b31c550d510c21d6395130
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s3K5 (768+(h % 30)*6) 6) % 48)
  | 4 => 2*((h/79+packedAt s3K4 (3618+(h % 79)*8) 8) % 134)
  | 3 => 2*((h/22+packedAt s3K3 (988+(h % 22)*5) 5) % 26)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffff0ffffffff81ffff07ff07fffffe78f1ff
  | 1 => 0xf07fff03f07e1ffe1e0ff87ff878383fa73e93
  | 2 => 0xff83fffc007fe1ffe00fff87ff803fc1c7cf1c
  | 4 => 0x3ffffff8001fffff00007ffffc001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x800010208010000044120088008a0a10085025
  | 1 => 0x2519221924a430960a854853485090aca32692
  | 2 => 0x432a44486949032aa109950595012585458b18
  | 4 => 0x6a5388924c0d55cd33a0c446e6658109f00dc0
  | 5 => 0x8c630ee38e7199f1ddcee660c4460631fef000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_38867
namespace PEqualNP.Outside.L_meta_38867
open PEqualNP.Outside.L_meta_38867.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x20001c008014400105800018c78c000080684ff21fc41fd30fd20fe20ff10fc10fe41dc31ff20ff32fe43ff41fc42fd31fd21ff40fe32fc31fe40fc32df30fe10fc30bd40fc20fc21ff30ff43de31fc43fd10ff42fd41bc41ff31fd32fe31fd43be41fd40fe30bf40fe21fd42dd30fe42fc40
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x65dd53103be62986f54940fd906217e54cc37c84a17714a31ef20863f651082dea4885f95210bfa92817e51902faa0196710431f710241bf54442d8a4887790530af29e839c31d03f640085f94210aea9e43be41087f6a090dfd4e10de2a2437e5390efaa3205f94232bea9c85bc32d02fca8205f55021bea9421bd540cb7c8398df54b43cf18e81be43906baa7a0f750b30ce20c637f504cbbca8984f55210f7904415d53042fca9184f55010be29e217e548cafaa020f790c31be298217d52103b86288770c421fb88421bc41503f6611877906319f2a041bf43503bea418f78cb30de190837c53c83be6110778c421fb90c437d548c7ba83985f94d21bf29881de314437c82885f55110bea9a21bd40042f8a498fb4c832aea9c817d53486fca3986710530beaa061ee21883baa018e7d0130ef21661be52906fca2086fd4140ef98641bf52502bea7885f94221bf288637f548c37e80185f54f40ee18e433c544cbb863186ed4140be29c437d52886f8a4a0f790d32be29a415d53083be86a1ef10621de20e433e54cc6bca6186f10d409f28e81bf21d03bea818df94021ef21a61bf53906fca418f708530ee98221bd548c3f44010778c630df29883be418c2fca9106f50441df21681d6510c6faa010df94841afa9a85de21cc27ea8996f14e41efaa4637f544877a81886f54a41ef29c21bd540c2faa7186f4c940bf284417e544c6f8a2a1f754c10deaa0215f53442bca790df54f10bea8887de31cc2faa3196f8c540dea18833f54c43baa70877d0831eeaa261dc31cc2faa32177cc831de20a63df410c6faa021f7cc120bf2a021bd43d037a8621ef4c740cea0661de304c3be8518dfd4f20de296817e52042f8a4086f14a41dfa1483bf4350afaa5986f55020bf28081bd51502f8a09977cca31bfa8263fa300c2fea9905f94c20bfaa021bc53503b8a4986f8ca41df292817d54c87be8318df95130df99483df53486f8a6a05f15031bfaa261df43cc2fca1a0dfd4543bfaa4417d5090f7a80986fd0320dea00417c548877aa9105f94743dfa0c83f920083be60085fd4141dea10837c514c3be84985f54910efa8a61bd42d027aa9106f90610ef28063be51d03bc63085f14940bea8085df40cc2fea90877d0530ef29c81ef20083b883985f94442bea8685de420c7b887986f90140bfa98437e53d02faa5a05d54420ef992617f544cafca4206f90c42be2a2217e53887b863085f942419eaa643f741906f8a9196f8cb40dea0e817d54cc2faa1217714730df190837d51c83f040086f10720dfaa621f5310c77e81106f55331de20c415c53443b8a5987710831de90a81de508c7bca9986f90841bf2a2417d50887be86195f94a30be2a021bc52502fca9995f54c41de21483dc320c7be61885f94343ee18a81bc4390bb862206f95020
  | 1 => 0xd404c37ea620efd0a42dea8e813e540c37e63a077d0c31ee98241bc21d03b8a6885f14532bfaa263dc42cc37ea8995f95320be29a21f521c42fca4186f50030bf29421dc534877864a06750c43bc28243de52cc3be8718efd0e41df28883be43d02fca620d794c209e2a2437f5050b78a7a077d4031be2a663bc41087b88218f754730f721085bf40442faa910f78c410beaa487bf50106fca3185fd4c20ee20661bc41442fca910dfd4f21df20e81dc430c7f6210877d4a31ef18e81dc418c7ee82a0df14141ef990657e52d0fb8a018d714530efa96617e5090afaa8085fd4121bea8c87dc53c42fca0105f94443dea10857e52442faa9085f54e31de28e81df434c3788720df15020ee20a617e54082faa920df54c40be29621f510043d842105f14520bda8243bf52907da4210ef15131bf29e417c504c77ea890dfd5020bfa9263dc31c43f48020774c010bea9c437e52c42baa018df94632de20c61ee320cb7e811877d0130ef288637d520c77e87a1778c710fb98c63be410c77ca9185fd4520beaa641dd40cc2faa1a1f754f21ee99063fb40502f8a9906f90710efa9a837d5210efea2995fd5331bf28e817c544c37c8318df14910ee21a617651082fea9995f54d20dfa10837d510cafaa1996f4c540bf294877e5190afca918fecc130dea1a817d5490afea4985fd4d40dfa08837d54ccafca6214f55331ef29063dd514c37e85a0770c530bfa9221dc310833c83986fccb40ee29a857e53d0afea910f755231bf290657e54cc7b86598774ca31bea8663dd30c42fca0216fd0740ef18a61bd32907bc62105fd5310fd904417e52902bea6a0df14d21df990837d5110bbca6216f15310df20a617e5210b7c82105754c42bf28665dd43ccbba64985f54231bf29041bd41502fca7105fd4540de21083dc31902faa7195f55232df19281bf544c7de43907bcc932bf288815f534877ea6a06f50940bf29483bc31502f8a6a16f54841ee29a83de31903be60187715031bf29681bc42d037ea3a07754e20ef29261be41903ba63985f54b41bea94617e5304278a898f70c521de284833d54902fca810f7d5130be2a463dd30082fca210f78c521bea9e85be548437ca2a05f94631dea04417e53087be43987bc8621bea88417d544837a81906f90940ef21c63f9300c37e81085f94041fc282437e540c6fca320df54e41df20a437e53842fea710efd4540eea1e617c54086faa521ef10610ef20261fb204827aa120f794f21df10a815d53883be8721f7cca32be2a265de530827aa81077cc631fa90843bf40103ea428877d4d42ef988637d53842faa5105f55220db28883bf40cc2bca7206f15110f790a41bc41cc3ba42986f501209faa263bc41103baa6216f94241de21885bd4350bb8a2987715231beaa065bc410c2f8a9105f950439eaa
  | 2 => 0x83b862185f14540dea84837f540c6fca0185fd4941be282857d529077842a06f50110de20c637d53882f8a990df15032dfa00217f548c7788208778c540beaa2617c5150ab8a6a15f54b10be2a621f621c437c82a06f10c41bf2a061bc31d03de84a16f10740df20861ee21486f8a790df15210ee990655e530437ca990f790f32ef29c417e53903788218d794c42eea1c633f54486fca3106fd0310bf29a21bd50106fca8217b94810bf28e41be41c87bc6390f754831bfaa661bc51502f8a6105fd5120bfaa6437d51cc3d8a4887750130eea18877f514c2fea7104f95010dea0461ed214837a65a05f95310bfa8287dd300c37aa6a05794e20fc880217d53902fca6196f15132bea9e437e54106fea6905f94f41bfaa465dd310c7b8a418f755330eea1863bd53d037883885794e10efa1c657c540c3eaa2106f95030df18e817f5150b7c86a1ef50a41bea9e837e51083d843105754e10ef90a617d53043ee6298efd0940ef18a637f5250efaa3a1df54a40bea9e41dd528c6f8a9187dc4010df20a637e544437a8720e710730ef98e61de428c73e81987715330beaa6217e53c437a80205f94b30df29a81bf32502faa120f708730df29083dd314c3bc87987750a31bf29c836d52042faa3997ec4110ee21c657e500437ca998efd0540dfa02617e50cc77e80105f54321eea1063bd32106fea4086f109409e2a221bc414c2fca6906f10420eea1a61de41cc3ba869977cc110df20a833e54c87bc63907754930bf28463dc31882fea5885f94f219faa2217e52d07ba8218df54c20df2a0217c5050efea7885f54841ef190637e5290b7e81205f95132bf298617d54cc7bca6085f15120bf28643de328c778832077d4d10beaa265dd418c7be61185f94240bfa9a85dd508c77c8721770c720ef29e83be429077c83105fd4c10dea1e85de31883ba84985714f10bea98437c5250e7ca8197715130dfa8483bc53106fca021df54341eea0a61be41c82fea6887bd0a42de20a435e518c6faa898ef48740dfa90837e5210fbaa7a0ef50210df20c437e510c3de65197b508429eaa461bf4390fbca918df14a10efa92617c53843bc64985f14121bea84657c544c7bc6310f78c932bfa94215e53103b86310df943429f288835e510c77a81985f14c21df29e817d52cc77aa5a0774c220bf29463de424c2bca3985f14d41bf29465de540c6faa818f7d4730deaa421ed520437c82907790c43dfa9e81df42cc2fca410f74c320df21883df54cc3ec8220f70c740fb10a217d5310b3862a06fc8540bea8c61dc31483be65985f55240bf28c875d538c2f8a9996f90410bea9463bd53906fca1185f55020dfa9681bc41cc778a020f70c410fb10843fa10043be61084f15310beaa243bd53107be839877885309e28a819e31503b88718df94243ef18a419
  | 3 => 0x2b80600802000100481c1f0000080040a00280262b800010362cacc00002018001080e00012020280b806058b42406a0200a0030601816000160500c04018260b20002000010000ea01804008006f96e21102018040084a000400401200800170000d0aeca800000fa3d810099203985e1581a1580e0f0360000a0d08c030000185a0b0180d8223d0161087e0384c018000281408024078e02580c000528104c2bc183104c2a02e3eb9405812000542c1c2288001b8102100a0789c0001a04808020000b82803022040003b0140181c260020083600a4e0001d6002c00016008a0008040700c06800018020900a26004001122302a020400180024870008203f996008020601a0500c03b44010100900000876000da03004ab8840101c000100881418802270a4ed8040580405800008000311002872070244804c0f80a030160192e0d01607800102ee060024a80a09058050022982a018000483800010028660000e008000100c2b80a0280007826060ff7903a128521e0060000a0201804000130020000000804178082188e000020580606008001e808ac00980009802000149901e03092008784c018000000400a0a0000c062020000000c02084258680680a108601602a23802007710a31deaa6437e51d0afea8885f94432ae29a83de31103bca3985f54740bf29863f5411067ca320fed02409f2a0817d520c37c83986f90440bfa9a83f610442fca0194f95230efa9e21dc508c6fca8194f95210df296817d51883b884985754c40ef29881df504c37c43a077cc020bf298877c54486fea8197754c20efa8463dd308437ca8195714d219ea8083dd53903b88619774cb30de21e817f540c2fca990ef14841fc106217d51842fca310ef94041de20a417c54cc3bc62186790431df98a81ee21082dca4085f54810eeaa063dc404c3de4210fdc8521bfa9a43be43502fca220e790530bea88617e54486faa9186fd01209eaa061dc324c37ca9106790631ee90e61de528c7f280205fd5021df29c837d51d0bbc81985f94732bea8063dc328c7b6a0985f54440aea8463de514c3da43907754b30bf280637c538837e87a04f95220fb18863bf4210b786520efd0c43be292617e5390b7e8620fbd4910bf29663ed200
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xd525025e63150208f99050487375110520ad98740c4354510c5409e580540c71f5495231ad185525034f524c110c755231042b960d4b40c755330042b96010710c7953308c25f650c420c7950318825e63153219758e544423d64d4f218f994414872f5250110a798c52502b96008540cb548521063e64150328f185540ca9d64148318fd954310e3e6414e10d60c7504865e658c521c7952318c31d544c030ab988501071e53d00109d185544c23f6454432b3189514c35451d0530c754e419027a6094d21a718d515029e63d4a41abd89515025e63d50209e980540c63e6414a10b6580319039661106318f994544423c6454f20a759351cc25d63d48108f19151cca5f6354b408f592508c65c6548730b6580214c2ad6214f40a718d415023e6415020d614f504865e6395310e60c750502b96094d40ad987529065f63551329718d521063e6515121d594e510831c540c5109758e50c873854d41218fd95315023e64d4a109d98753082bb6048540e598441cc31e544c2208f986540cad9600c6209758f515029f6350441c7550434c23c654c940d5144414c33b5414121a7993528c72f52905108fd91510831c53905418f19531d029d6314041cd14641502d4614c3109798e548871e54cc0108fd9153442ba6014841e5144315039b6050130a798e529063d65c87408f992538865e65d053097596318825d6395310e6980414c2d9608c410971855310a9e6310841c7952310427860551219758c544825e6315220d314a314431f531071097d8153c872c5210510b6d81214c23e6195020c7952538823d6510430b6580540c72d54948109798f514829e63d47408f990504c63e64d4e10ced93504871d5494c20cd547400829d6310b40c7151304431c5390942c794740cc29e63c8740c7151434cb3960d5310c7553308c29f6550c43a7d8d425023e6494030ce907504865f6354420ad987404425d63949108f99353082ad6214c418f59252442db60545309dd85534825f63550218f593520431c4154031d518e51082b96094940c794e410823d6595010a7d9152cc25d6014d21b398b51cc23d6494321b5987528c6da6015031a758c525027a601533297d8d524429e640c8319b988540423d6494e21c7552318c29c644c832f888420c423d64943319798c505063d6510420a758f41d031d5310f409718d5190a3f65104208f592534439960105309758e500863f654c740aed81535035960d4f10c754c418823d65106308f19153482b46154d408fd91524431d5454c10c7d5231c42ae6214f408f5905348356518c630c7d5330c423e65c854097d95320ca9f6348740c7d50314425c6354742cb952520429e648c1308f994325031e540c42097d8d52c425c6354720a719131cc25e6194e20a7990324c2da6010530cd986511071e53d0030
  | 1 => 0xc31e5390440c7551308825d6094c4297d8d51d0adb60487308fd8154cc73a54500408f590504ca5e6315320ce10750486b960d4740c794c410835a31d41218f992534431d5410f30c714d40c436552c4010c7153534423e6495121c7153304439b6050330975805350a5f65508318f996414871c540c710c7153534869c644c930c7152314423d650c841cd951510825c635532097d8d521065e63d522197d9542cc29f645493097994404c25c6355120c794d408823d60d51218f593538829d63148418f596540c2d66114a318f992528c63d64141319758e50042b96014c41ae58051d0399404c320c794e41c871c5450f3097d9521cc31d53500409798c544827561d4c208f19151cc23e65d0540b3988540c65d63150209758e50d065f6355120a7592528c65e6194e40ab588509063e65c87409dd9541106b960105208f590530825d658c4409d185544831e53500208fd96418825f654c431ad986321071c5390710b6580315025d6014d41b5987540c66c6254d109798e529063c6454b308f987544ca5d6094f41d5d8d510826e62d4c108f992508c7c930480208fd9521d023e64940209d987548ca5f6354642d3d4c524425c6550a31c7552530431c53501109b99452442756114c20f10c5210865d6315021b3d89514c31e5454e10c715130c429f63507408fd91534831e5390620cdd91510829d64d4530c7152314c69c6150c438f59053087a94048020ad185404423d650ca41a799032cc31d5494e209798c525031d5390440b3988500c66d62d5231d3d48314431d54cc832c7d5353c429e640ca318fd9151cc23f6454831b658351cc2ba6008540b59873044394410c52197594430c6ae6214241a758e509065c63551109ed95100431d5454e10c7150314863d65c8540a7592508c63d64d4c108f191510829c6354841cb548525029f6350841c7d53304432c52d0110c715053486f06048710c754c53106e862440109ed81524431e548c420975835350b1c5414f10a798c42d031e54cc020c7d53534434c52cc110d6d4f504869d600c74097597300434e524ca318f992544423f6550040c7d52314425e6314c2097994424c29f6448730c7d5353486da60085308f992500ca9d608c7409dd95100423d6494a31b658052cc25f650c4409bd89544429c6354940c714e414431d5390610c754d408429960105309758c525029c6354b40cd144414835b63d41219718d54c431d540c430c7d4f40c431d53d0240a7582414c31f5410e31ce990504865f6354640c795253042d66114831cb551520423e64d4f218f594418831f5394e41d9584524425f658c6208fd95400429c6448530b6580310423e6494f10d9549100432e5454810b6d81524c2ae62d4740c754c4310b1d53d02209758e508865d63152108f59052843365110740a7d8
  | 2 => 0x6054c108f59654082d9600c710c7950318432f54149109798e50886786054d218f597400829c63547408f185548c2766115020a7d8d515023e65cc54097996404c36952c80108f99250ccab76154940d598453c425d658c420ba18121482b5618c8419798c504869d6394a419798c540c31f5390521a718d41d029d6010530c7550318435451c85308f993514cb1e5494f21d694d300c33864d4121a798f411063e6414e20c7145404c23f6548540ae980531063d60953319718553882cd6215031d5944310c2bb6048740d3548520c65e63948218fd94410c3a441484218f592500829e6314041e5104318871c5310510a7590500c756510c4208f19532d025c6354910c5144315031e53d00208f992544ca3f6454630a7582410c71d5390410a718d215023e6494331a7984410c65e6394041c7944410c71c5390521c7951308429d6090730d554e510826d62d50109719542cc29e64d47308f195329065e63d5321a718d425025f63551218f59731d029e618c54097d96310823d6095321c7551308423e6494221a7582418c63e641481097d95414c25c6354440a719121cc29f6354841cd94540082d96095130a7d8d52d029f644c43197195434c23f6590430c7152314865f650c41097597410c63d6494d219718d51d032d5214b40c7d52314871c5190530b5586420c63d650cb40cd191510825e63d4542e5144414c29e63d454097d8d51c825e63940208f580544cb56535442097583535071d53106409719541cc25e65cc530a719151cc34d520cb30c5144414c31d540c420c754c418423f6510410cd552510829d63d4740d5d44315032d52108419bd89534429e6494231a7592404c31e5350040e5984315029c6454b30d5945300823d64d4530c754d400826e62d5010c7553300c39b5050130d3d4b304431d54153309758e509069c6350a419b988540c6d9608c710ab189515031d548c430cd946410831e548c6209758c5488338541412197594424c23f64547329758f548429f6350b4097594319029f644c53097d8153d065d65d05308f99432d031d540c620bc58420c42ce62142319d587540825d65d0c32b5987520c71d5390420aed81525034f53d49109798f528439a600c5409758c520432f5210510d3d4a31442b46150310a7993514c31d5454c20b598730c429c644c831c7953308831d544c0208f996414439a41d41309798e524429e63c8540e6501300831d5410c319798f548825f6054c428f986540c25d63153209718d52c425e6394d10e68c7505025d63d45429b58a53443965190431ae580414c23e61151328f9974044397510c540a7992528c65f658c4408f994414c65e63150108f19153c429e6110530a7d9151cc2d960d53309798e500869c6350441a7590508c66e6214c10cd944411035763944208f597400
  | 3 => 0x842b5984540c63f6055321c794f408836551c8020c754f401026d6214c109798f540c356518c420c714c414869c6350841a758f215031f548c5318fd91518833651104208f593528423d6414f208f185548835651cc020a758f415023d6590410b5185524c25e6394342ced53504871f535011097994534863e6494821c794d400c25d6394a419e596100434d5394810a7984315025e650c510a7d814310f1d53104208f195215032d5290410c754e4310a9f644c730d3549300431e5350210d5144214c29e64149308f99250c863f6454c21979875350b1c5450f32d658053c429f644c8319ed95200825e6114d42e658031502b86048540c7553300823c65501108f596418829d63d4a41a758e501065d6395221a798f419065f650c620b6580314829d6490c43c7553430cab661d4e419718d544863f65508428f191520c65d6594c10e5944410c76a2114121a798e509071d53d08428f992508cb34510c540d60c4504871d548c420c794e418431c5350d42c754e41c865d650c420a7d91324c2d86048530a758c52d03585314121c714f404429d6494031c794e410c3365190640d594431cc36551480209718553902776155120e6107504c31e5310440c7d4e414425c635444297185531029c644ca318f992500425e63141428f19532106cd62d5231c7946410c66d62d4c109e58253486d960945308f19153486da6014831ad987521063c6454620ae582410425d650c4108f191530863d6494010d3948310431d53d0210c7553308825f6355110a6580315025c6548530c7552318823e641413297d94319029c644cb30cd144414c32c5414910aed8151502d96014831c758c544ca3d60950328f191510ca5f6355310c794c41c86cd6214031d698c504866d6295110cd98754c432e5250010c794431d02cc62551309759721cc33a41141218fd81540ca3f65500308f992534871e540c7219bd95320ca5c6114d109e58254487e121c831097594430ca3f65106309798e50d072f5294a41c7951538825e6394d2197d95214c29f63485408f59053042cd62d473097d95410c74f5294a31a798e405031c53107109d9845204354518c5309758e50d0a5d63951218f993514c2796014c218f986548c3566194431b6582524c27a60951218f581540436852c4110a798e501063f654c841a7580410c63d65cc5409758c504874e524c010c7550544c25d650c4409758e501071e53106208f994544c69c6454831ba18121c829e61d013097195420c6ad62d4e41cbd4b404423d65904308fd96418c25f63547409758f540831c54cc3109798f51502b66114e41c754c535031d5350010d354852cc31d5310440cb94a410423e611511097596530826c6255110cb54842d029e64c8530c715231c431e5390640ab988531063d65906308f994414425d
  | 4 => 0x5986420c6cf6255130b618121cc23d6494f108fd9152c431d53502209758e52c425e63d4810a7d91328c6b960d4f40b6983424c23d64d45208f195315025e63152108fd9541106b96014b40ad984529063f65904209798f548423f6454f20cbd53524423c64546309dd95310c71d5410c32e5d44414c31f53907109798c54086ad62d4740abd89535027765484219758c54c863d6414e10d394a310425d63d52208f19152c423c6155030c7950311031c548c932a718d21d025d63d5321a718d42d025e6114d10c7d954310e5e6194c4297d8d511025c6354420c7d5130c429d640c8318fd95329069d6314241cd947400829e64140319d1855348396610c7409b596520431e540c43097994428c6796015021a798c509065d65c85309758f514831e5350010c7551538825e65c8730c795231c874e52cc010ce590504871d53d0020d5544310825d63d522197594428c63e6494031cb94841042b9600c5408f19151c82d960d09309b98854cc31e5454f21d9546210831d53906208fd9532d025e6394241ae582515035661d4f109758e544c65d6394821c754c53d029e61d0330a759052cc23d6494c319759741cc31d540c721c794631d025f6054c10ae580418834d53548108f99053c869e64cc431c794c419025e6514d1097195424c29d608c5409798e5010b1d544c832a7990404c27561d5232e650130843355150020d554d510823c6115110a7d8d51d023e64d4c10a7185404c29d640c9309798e500425f658c640add85535029d631094097596319025f6550730c794540cc31e51907309758f528425e6590d32d618f504863c61550208fd94418829d601073097d954310f355454420c715353c425e6394321cd147215039b50d01308f597400429d6010631b5984548c71f5414f10d3548320c6b661d4c41c714f4350b596314121c754c410425e6394242ae98332502b661148419bd9521086cd62142318f994544ca3d64141219718d518831e54cc210c7152434ca7b6054d219ed95401031e41542318f99731d025f654c010c7550540c69d64c8530d314c524426c6255130b5d85544c355514c020a7993314c29e61905309e594200423c6454632c7952530823d64d4c20cdd92510831e548c610cd546410829c6350842d6d4c504869d6310a41c7552318425e65c85309bd95200831e53904109ed81544871e5494e108f580544c69d64cc5309799431486766114c208f994321071c5110530c7951300c31d54cc210d3548310431d5494f21a7986410c69e64940318f592500c69e6314b40a7593310c67a6014c218fd95325026e65c85209798c520431c53d0310c7552538432c5250940a798f415032d5250010a758f419063e61952208f992500866d6588420ab98b53906b960cc9408f59252c426e62148108f593538431d5350
  | 5 => 0x314829d640ca31c794f401031e540c630c7d51304423d6414810c794f408423c6454d10a759321cc34e53548108f99252c431f540c521d3149324c23f6454b30c7550310431e5454c109798c528425e65d0730a718540cc2ac6254d4097d95424c25f658c410e5104318425c6354b40ce10450486db6055130a799052cc31d5454f21c7d50534871e5450e319758e5090a5c65505309758c528431c518c54097d8d54c831c41542318f994329065d658c430c794c41042d96014730d5547300823d6494032c755231c87346494420c794441cc25d650c6209718d519023d649403097195304429e64cc730c754c4310735511042097994420c6b860487409ed95300c355518c420cdd44414c29e64cc63197996314425d63d501097997434c26e6295110c7150534425c6355021e5984410c6d960105308f594325025e63d50108f590538826f6550842a7593528c73451cc540a7990520c63f6590410b658352cc2ce62d52319b98a534431e54cc030c7551300425d65cc020cb949429069f6448530b5d85524c31e548c4309b588540425d6394020a7590524c29d64cc730d3148314423e64951319d584540826f62551308f990540c31c510c540c7d50438cb1e5310610c7151430c71d43944439758253c871d4354043a798c521063e64d4e20a7d8d415032e52d00109798653083396015310c7950310429c645493097596430c63f64547208fd91518cad960153309b58854cc37060544209759442cc23c654874097594420c74d52149308f592508ca5f654c0208fd9153c423f6454430cd144215031d540c63097583534869f64548318f596540ca3f6550020c794f409029e6310940e5984414c23d6494221c7d4e415072c5250110ae58241c423d60d5132c750d5210f94410c410d354b300431f53503108fd81540429d63d044197185530834d528c410b5987548c72d521041097d95428c63e65d0d428f191510c34e5394810ae980315025e63951218f990530423e64d48108f580544869d648c130cb153524431c63550328f993514831e544c010c7d50534423e6414930c754c41c871f5310510ae580410429d64cc6318f5964310ace621533097997304423d6510410d3149304425f63544428f596411031d53d00108f99053c831e5310430ba181210863e6414c2097d8d5188399404c1109758c505065c6550d328f59353886776155130a7580315029e64142319798c53043366115310a7191514c23c6454910a7d9132cc25e63951108f592520871f540c7109d195214429c644c5308f992530c63d65904208f992524431c51d0130ae580521072c5290510a7191310c69c6250c43da181520425d658c410a799321cc29d6390140a798c429063e6590531c7905500c63d6414f21ad984531076452885109b98b548c75a3114121b
  | 6 => 0xf43180d0000080780004e00000002042638050e3000000a404701a0000000c01c0042a81009e710023270020880002000e082608000221180701b1e8000002730020002280304a0181280103801001807074810020190000341482f07400400008578000410110020004a1fb0063f992000014020018760000300100800c0340082b002064180089e447008001014f401a00315c9900a8050280880280e002010008060000140100104e01c2800000026800022050000000140000100601e29c0040002804c0080280100e0202880400e0950081b0120000600301a0081304e0160701304f63c084b60110020c00000607c018000080480057b1180020100002e0020588402c1d4010001cd002000140000007600083b0240940002101e0003400f002004138007d60cc00824018014069590160102d0480060100100a0001ec1000101e0400200f0220080a8001da02c128100460d40d8510c61380281a008284000002c04b13000304e0100106d0044380100e00a05c0484a02e0500700d0073250f0082aa0200100500c0e41304e1480080a02e02012c000000000a0048040020ac0580b0040000400d0880240480a0400100602c0760040bbe60000001580001805007800002028010130160300000005a05c04804000004088d300008c0106300206000013008004040110040400d004002d0021800004088260040300000000c0000000101700201000008028008068691bc00429806000068000010025a48e00b0520300280c0920280a80408c0000b0000342b8008231580080192d008048028450000811c357008004000040c40040201c00c00401334012028098178f64dca080105e03c0180602403419800026004428090000202f0080040107f0070020001f81f00000813820006028238010ce00c0a0000940080000102c00829800006020018180200965e6510b308f990530873654944208f593514ca3d60d5131a798f41d029d63d4540ab588501069d640cb309798e52c432d52d00109758e5010a5d631501097d8d544c6cd62153308f990534823d64940219b98a524429d63c8740d514431482d461551309e58054cca7661d50208f590524c31e5350e41ae580418c34c53d49108f59250cca7a6015021c714d43503546354420a7d91514c2d4614c110c7151434c25d6314142a758c421063f6454d21d9544210823e641501097d95300c31e544c0209798c540cb1f5310521ae58053d031e5454c208f993538871f53d0110a7d8d429065e6194c409b588540c71e548c440d5d44
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x1c61540003404045000800004000100604284000000702000050ebc0010002c0100041000008034002c1040218000082000000140000400682141c00104081810000291c18c72928520e10515803150287396a729c83925496014831c1ac6a90a5a060d635485210706324a499463461d5404c110c1aa8b10a99851970105500c68b38ea821c65435c85450f30b22e0208620850e72d52548c6a238aa429261a81046048421c28c228a809845471594424c314a92c0290830d1c5650c940a18e4aa0a89869061501304430b318a390a81265c264c8530ca0a2b008298439701953210686392a629a81835915214831e82a2982401050e72d50438c706320a49926183591520cb30c1ac8a906418e1051580414c28cb80a8a186385594410c4108b2e032a8418d147150e5110f12290c2a0221431c95410d3092ce3b22a418c997098c525030a298c2a0621439d35294a31c32a6b00831071051980414c31828ac018a81431cd5214940c28a2b0062a060d6354842106c838a8098221c1548410c410a28e2a98832061865501304434828ac018a81c4146600c540a28e2aa0631063051580414c34820ac01882185150614c110e42a2a02401051575104310428739ea5294838654d6014c41a36e0a1aa021e1664147214c30c28ac018a8186d4d6010710a1ae42a28618e19535804104306b22a4296618a5496010410c1aa6b10a620e935158031503882086228243c2149404c110932e131e42a061451580414c24cb84c9a8a618514c6150110c28a830a618849671d8d5210706aa2c42a06392549600c4109c2ed1084188644521853044306318a4a128186551600c410a28e2aa0a89861954580540c749a8ac020a61431d15214930e22a2a02601049970990524c29238aa4292818354d6214f40d80623024210f1051580315028a38aa629a81265c263d4540c1ac6a9085a061b5458031c430caa2c018c41861456010530ca0a2b0062a05197015143cca8a38aa818c61c41456010530a28e2a98831069051580414c20e3b2a899065451c55410d30
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x608000100030e0152105600c410a118098c51c8540a108154d6010620c11655c0410c410a1185105600c410d01525c0410c410e0052185404c110a1081551600c620a118099051c8530d00521c5404c110
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
  | 7 => 2*((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/30+packedAt s4K6 (768+(h % 30)*6) 6) % 48)
  | 5 => 2*((h/367+packedAt s4K5 (27459+(h % 367)*10) 10) % 1017)
  | 4 => 2*((h/497+packedAt s4K4 (51110+(h % 497)*11) 11) % 1345)
  | 3 => 2*((h/79+packedAt s4K3 (5488+(h % 79)*7) 7) % 112)
  | 2 => 2*((h/17+packedAt s4K2 (600+(h % 17)*4) 4) % 10)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1ffff83fffffff03ff0787ffc3fffffdc0f1ff
  | 1 => 0xe07fffc0fff83ffc1ffff83ffc1fc0fe7f3e73
  | 2 => 0xff81ffff03ffc3ffe007ffc3ffe1ff0387cf9c
  | 3 => 0x1fffffc0003fffff80003fffe0003f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x208888820922100a541026481325450c050a5
  | 1 => 0x491411064920402c0a0a8809440482a81b2652
  | 2 => 0x852522121a4406554084d4826a412a0b058b18
  | 3 => 0xd659c4a49076ab9a73d04623b3980c33e80de0
  | 5 => 0x18618738e38733e39ce76730231030c3f6f000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xece8ece8e8a8e8a8ece8ece8e8a8e8a8ece8ece8e8a8e8a8ece8ece8e8a8e8a8ece8ece8e8a8e8a8ece8ece8e8a8e8a8ece8ece8e8a8e8a8ece8ece8e8a8e8a8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_38867
namespace PEqualNP.Outside.L_meta_38867
open PEqualNP.Outside.L_meta_38867.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x958200000200000a08104114080438f005007000ff43fe21fc30fe41fc42fd31fd30fd40ff10ff41ff42fc32fe30fd32fc41ff21fc10fe31ff30fd21fe32fd20ff31de32fd10dd30fd42fc31dc32ff40fe10fc21fd41ff20fe40fc20ff32fc43df30fd43fc40fe43fe20fe42
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x665ef21482f8a4a05f55332fd180615c535077aa808774c431efa8e61df508cafca321f7d0c32dfa0c83dc32087f640905f94832ef980415d53102faa3087d94420fb108435d53903be65987754e20be2a641dc43cc2fea9085fd4c20df2a0637d5090fbe61907d50721eea02617f52c43da40107ed0240fb10e21bf4310efca318df94242beaa461dc524c3bc62987754232bf28685bf40103eca221d794a32ef992617f504cbb884985f55110af29e857c5050b7c82a0df54a10fb208437c54c437c85a0f74cb30ee196217f54cc2faa718df94c21bea8e41de42cc2fea4a0fb50b20bea8e877d53487f440107b94810bf28c837c540827ea8905714d21b6a9081de53d0afca918774c120ee202617e5090fbca0195f54830f721085bf41d03bc83985f14c20bea96215f5350afea0a0f7d0832ef21865bf4210bf680a0770cb41beaa2615d500cbbaa2985f54840bfaa665dd53902faa898f7cc110ef196615e53082fca020f7d0e31faa8881de32487ec83886f95010bfa9263de548cbb883985f54b30fd080217e53c867ca910df15120f721241de524c3bea8985fd4542ee98441fb20883b8a9987714f20ee19481f6418c6f8a710df54c10eea1a61de304c3b86598ef15120eea98837e50086fca021f790f31dfa08837d52d077c84a0df54843beaa661dd53886fca420dfd4520be28a41df54cc2f8a90877d0330bea9e41de328c6f8a2a1df94040be29843df414c2fca620774c730afa9a41dc31cc3ba85197bc8621faa88877e53c42faa1197750832eea9881dc328c7be86985fd4142bfa82437f54483b8a2985f94f41bfa9a857c52842fea819770c930ee210657d51882faa510df54c20ef298837e53886fea898ef50740ee98061df53482f8a6885f94640ee2a2617e528c7be42985f94f40bf2a263dc32503bea9197b48421deaa0637d5310a7ca818dd14520f7904417d53106fca2185fd4540ef190437751483f220085fd5331ef21a61dd414c2fca690f794432bea88617d53086f8a9985f15121daa0883dd54cc3b86490770c840f790e417e54882bca4195f94c41ee980213d54082fca6185f54341beaa6417e53c837a8220df54440bf28687dd53843da6419778cb10be29a417f548c3f660987755232eea1865df4350efca918fb54840eea1a63bf54482faa8905f94331fb90c437d53d06fca3995f94a43ee192833d54886fca220774c210ef29c41de214c2faa918df14d40bf28063df428cafca8885f54831be29e21de53842fea4885f54630bf280657c5250f7e81207ecc230bea96637e53903b86408770ca30ef20a61dd30083ee4208774c320bea9e85db504c2faa8995f54a43be2a441dd518cbb88718ef50842be29e41dd52cc2fea4a1f748730f719065de32cc7ee43085f94a10bf2a443dc52cc2faa7a07794c10
  | 1 => 0xe51882fca5216f50040ef21a637e52d0f7ca910f70ca41bb288877e53842eaa221f70cb40ef298817d54843baa8985d54742faa0a63de40cc2fea910f7d4632ee192217d53102faa3a05b94810beaa4817e510cafca598f794832ef19643dc438cafca7217754f42be2a6437f53486fca2217790e32efa96617d53843bca7205f14132ef28a617f53886fca4205f94c10bf290637d53443b885985f14141bf2a0877c53883bc63985f94b40eea1661f6414437885a0d714d20ef192837f544c3bca9985f95040efa1863de32043be65197d54742bf2a621de32842fca4085fd4f20bfa94217f53442faa998fdcc531bf29885f940102bea6a0fb88521bf28e61dc32107ba42985f94e20bf28061dd40cc3bea6a15f94742ef190617d50d0e7ca8085f95210bfa90217f54087da84217d90441efa82617c54042f8a9197714032bea8665bf41502faa818778c841ef19041df30482faa190efd0b40bf292215d538837aa8105794b30bf2a265fb10843b881985fd4e20efa9a437e54106fea9887b50920fb20a635d53886fca0105f14810f7908437e54086fca9906f90942ef284657c52442faa7207dc8521ae29a857d54486faa7885fd4143ee28c65dc5350afaa818f708530bf2a6437c54cc77e85215fd5030beaa021bd54886faa3987b48720dea1e83dd43cc2faa4885f54b43be29a837c54886faa021df94a32de21283f741506faa8195f54432dea1a83f7318c7be6118778c932bf29043de428cbbc65905f94232bf29e857d52d02f8a690dfd5231ee29a417f514cafca1185f54732df214817651d0afca210f7d4930df2a041ee52103bc6520f7d0730bf28421de21cc2fea790f754c10ae292617d5110afaa790f790f30beaa4837c540cafaa91077d5032ee28465bd41502f8a8985f14941bfaa243bf43d07be61105794e10ef19221dc430c77c86a1f7d0f30fd882217e540cafaa420df94010fa98863f651d0afaa0195754e30bf2a4657c544caf8a2a05f94c20bfaa0417e52d07b8a21977d4d41bea94837f54c83bca8987e4c030bea94637e50882faa810df94d10ee19661df424c2faa018f750f31faa8841f5418c6fca588774c310ee19243df300c2bea690df14f21fa10821bf4390efea6a07754730bf29865dc53486bea79077c8730bf28e87f541086fca5185f14c10eea9261f710842f8a2986f90840be28a85ee20482fca890df94e43bfa8263de324c6baa7085f54231ef19681df30042faa7195fd4c21ef190637e52902fca120f754c20bf2a021bf43507f240107794e21ef98c637f534837a8621f790130af29c417f54043ba83984f15120bf290857e52083ba849877d4530bfa9821df500cbde852177cc530fa90a217c5050f7a85a077cc210af29821ed52042fca220fd50710fa10c21de51cc2fea8887dc4010bf2a
  | 2 => 0xa812018580280e468141501013852038402985c110000791800800030000001e000060580400028250360302a6b024060ca000000784a0280e002923682a028aa3580007814030040001a0181a7c8001d0040100007936050040d0040900c0185a0e034199022c000000e20682c058021982c890020081c0209a0009a2c18002000000740001a0d0e06d0061a0521302e0002e0280058802190ba038005b006c68244f3f20010a4400012830090a2008200081001804112103a94000000048720502403030088ae1d8140100005804008100204e00866f18040501c84076328940c8ac030022e8000000001aee05000088080088e060681d0260284e0b808088b62c20c01032010020a88c078480f89ec5802048e400816190000280a1ca0601000000c00002a650361c00001802060000da620800000020010100180603b640b03c0407a0a07e1d0000009408774c530ef99065de32902faa010f710d309f2a0416e52102fca998df54042bfa9261f6310c7b882985d54440bf2a061f521087b865105f94332be282437d51083be8721df94a41be2a6655d508cafca720df94642ef18a63f751482fca3a05f54e21aea9821de424c3ba64985f15030ef192817e54482f8a5885f94830f790041ef324caeca2207d48710bf288217e530c7ee8320df94843ef28c65dd30442faa020df94621bfa8a877d50906baa620df54a30ef19441dc32c87b885195794c40f690a417d53483bc64907790832be292637d548cafaa1a15fd4d41faa0883dc51cc2fea8995f94321bf288417e518c3be6218df54640eea1887de324c3baa2195fd5232eea80657e508c77e84a05f55310ee2a065ee42c82baa6107bcca32af29c437e5410bec8390ef10a40bfaa4417c54087bca8197714d41bf29661dc320c3e8a2905fd4940ef19081df53c83b843985f54e20be29c217d5190bbe6398770ca10be282635e530c2fca99877d0b30beaa0417551082faa3194f55010bea9c61dc32886faa910f70c820be29a857d53906fca1205fd4530be2a263df404c37c80a05f54a40bfa9e217c548c3bea219770c831ef19683f510042f8a918df55321bfaa6437e5110efaa3a15f55242be28a65dd438cbf480205f94042bf2a261dc314c2fca8107d50510bea84437d52043b886195b54810ef29661dd540cafaa198f78ca30ef21887dc32c83eca2205d94420ef98621f6104437a84a05f94341af298833d540c7de84a15fd5031ee2a4657d5190ef8a818df95031bf28e417e5310efca110df54443aea9e855e53903ba64195f14930beaa487bc42102fea7085f94d20ef298417d52882fca218fd88510bea8485dc324c6b8a7905f54e42be2a221df438cb9ca4195f94632ef194437
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x8530426f62551109798f548825d63d532197583535072d5290840b5984434c29d641403297d963290355539474297d8d544425d63944218f191524431e540c820d50cb514835a534c030cd50d5110e5e65cc1209dd95100431d5454e2197d8d524425f650c8209d185544835451cc120b318930482db60551309798e5190b946350441d5d4f514825e63942429ed95200831d548c820b6582544c25f63551219798a530425c6354a40d3d8e520425e6314c20d354a320431e54cc02097597430c65e6314121b5584434c3543214520d354b30042d56110c31d3d8d521031e548c8209b195424834c6394840d50ca510825d6510530b658051cc35632d45209b189544435751cc120c754f411072d54c802097d96320435753145209798e501065c63551219758c520434f6394840d554e511027465505109798f540425f650ca109d984548c25f654c0109bd954210a6d62d4c10d58c8514823e6494632d554d411074c528c9319718d52c42d66195232ad58742d025f6354a419758c544434e520c840b3d89544c25c6354910d58ca51082776550441d5947300834d5394810c7951300425d6315010b6582524c25d63953219d586544cad661d08328f191534434e520ca41c7550430ca5f658c820d394a321026e62951319d185534827b60551218f593530434c63948109798c54086746154a4097597420ca756115330ad5874210a75619512097594329025e63152218fd9153482ce6210330b658232c825d6594c109758c548865d6315020b398b30c825c6254c1097d8d52842d661d4b309d587540823f6550c43cb15242482d661d0b30a7590508cad661d0a3297996324865e63d48109758c504865e63d502097d96321065e6314142d994a511025f650c8109d986544833765504418f59053c42d9608c820d5547300831d5494c20b5984430ca3e64d4f218f993530435432544209798f528425e6394321b3d89514c29e6414432c7952530825d63943219758c548825c6354b409798c540425d63d4941b658351cc34e520cb41d35483290797635044197594321066e62150308f99251086d46350631d9547200827661d523297d81531071d54d0c31cd95141c865e639424197997434c23e6415031d314b424c25d65d0930a799352cc25e63d532197596214c26e62d5010d58c9510834e5394810c7952320c7555354440d354d52102b561d0a42d354d520429d64d4632b6980424c2d960153309758253887565394420b5984404c25f635444297d95300825f6354840c7150534825d63d49409b988520425e65d0b309798a531025e63d4910c7d50534823e649512097996404c25e6314c108f993520423e6414f10c7950328865c658c941c554d411065d63940219d984544c25e6394d209798e500865f6550832b598443cc2d56114232
  | 1 => 0xc25d6510c31b558742cc25d6014d419d597210425c6550730cd553100426f654c832c7d50324831e5450e32d5945300825d6395132d550d5110e3e6414121d5145304825f650c841d58c9511034e6294832d354a32103954110730b358840cc29d6488730b6580214c2d9600ca1097188534825e6314a10b6580324425d6315210cd151418c71e540c83197d9432902db60549309d5845050a5f6550c4397994414c35553944209d98454cc25d6314540cb952520425d63942419d987540825e63150308f590530863e64150109759632042d96014b30d5d46518ca746550531cd94941106d561153309798e54c82cc62545309ed9540102756115220f10c9210865c6354840c795253043655148020b3988404c23e6414a10a799051cc2d661d0930b5584438c76451c85209d98454cca5d650c820b5986324c6d46155130a799221cc25c6354b419798e534865e63953219bd89544c34c520c9409d98654c826d62141419799441cc2d960945309d586548ca9e64946329719542cc29d6414730cb551520423d64d48109758c54c426d621503097596320c2d960d533097d95300c31c540c920c755043cc25d63141429718d54c825e6315220a799031cc25d63d502097d9521cc25e631481097988534825f654c431d394832043355444010c7952328865e63d49419758e5010b345450710a7590514c335548c4319d58454cca5f658c84097d8d51d023e64d4e21c7551310c6d661d52329b988548c355514c020b398b548cb2d52d00408f593538871d540c831cd15141087565394742cd553218873551d004097d943210355535442097d8d54c825e63d4b10a7993518cb1c54d4d20cd55021043596014f208f592518ca6f6254d10c7d52548ca9f6454530c755032887655254440d394a32042da600853097d8d520434e52cc0108fd95411065d63943419d984540cad7615513097994534825e6514d21c7152324831f54cc1209719521cc32e5454810c7153304825c6354a41c7552328871d5350441b5587420ca766588510975835350a5f6355120b6d81514c25f6054c1097195414c2b561d0940c7552320c71e5454e219758e508865e63150209d584530826d62d501097d8d529023d6494d20d394e52102b76550441a7990508ca5f658ca10a759031cc2d960144329d984540425c6254e109799632506d66114232b5984500cbc93048020b958a41087955350441c718d540c76552c84109b58a544c65e63d5210cb588544826e6214c10cd10951102d561d0a329e980540cb4e520cb3197189531071d54cc020b6980510ca5e6214d41e58c9411074e520c830cb548421025d6014d42e50c9411063d6414e2197580534865e6394221d3d8d520425d639512097583534869e64140329b58b548c74d520c810c7551300431d540c8209b58
  | 2 => 0x5350441c7953300425d6094c419d594210431e548c8108f19152842b564885109798a538423d6414c109798e50d06d9600cb209798c515025f6550b309758f540434e528ca31b318930c82b564884219dd85529035432944409799432483364254440b5586548ca5d639434297d9541cc23e6414c209d9845050a5e6588730975943284275659042197997324c34c52885308f99251c827a6015021d314a324c2cc625513097997424c27465485109d984540c29e64885309b189534425f65485309798c544426e6215020d394a328c25d658c820d954b100425e6588530b5984540ca9e640c530a7590314c34c52085308f59353082776155120c7952538867461551308f990538865e6294c41d554e411074e62d4f209b98854842d661151309798c505065e650c921e3508420ca756195320a7592518cb555114530cdd0d5110e756194d209798e544865f6054f429798f52503345450510d318d521034e524c010b5584500cb1d5494e21c7d52324823d64d4f21c715130482d960150328f590514c29e6414530b6580329026f6548020d398853c836461548108f590520436552440109758e500425e6394010d58ca511025c6355021cd151414c71f544c1208fd954210a5d65cc010b5d85524c23e6494d208f590504876552084108f990520425d6054c10c7551530429d6414432b6980540cb3654944209798c540c65d658c841cd552510829d64885309798e51c835653544409798e510865d6594c20b5587548ca3f6454d109b988505071d5410c3197194325066c6255130c755153082d661103309798b535065e6510130c7550544c2ce62d503297195434c67561150209d587530832d5448020b5587424c27761551309b588540425f63551319b588548c2d5611513097d8d52c43555354742c7551300829c645493097189539025d63d4810c7550540ca5d650c810d954a511027b654c0308f99053042776548421b6580424c25f6355310d354e52102796015032c714f435065f65505309798e5010a5d6590c32b3988548ca5f63550218f99352c425d658ca40d554431cc25c6354a10cb552520434c52109309759432102b6619094197d8d52d032d5250040d5d45304835960d4f20b5584540ca3e65d09409758f524431e5454c109d986548ca78605512197996434c66e62d4c108f59251c825c63548419758f548865c6355120d5145314c3565354742e5504414c279601502197d8d521071d5494c10d354930043564354443e594d411065d658ca109b98854043365454420d50c9511031f54d4d20b5584320c7355150040d3548321025e63943429798f548871d5415330c7951300823f6454910c7951530823d6595010cd551510825d6510c3297195424c27661150319758e501065e658c9209759730082ce62cc120b558440c
  | 3 => 0x6d9c0000100028014050080b0081600016084130040c088090080d0601b0080000408000000040000c0000035278002bc0006c040081e075610180307c05000030580407957000000282610c06024005dc000100002012004020000b0080b00800008000b4070002e000ce0018f1189d01800019a331400128210280101d651b80a0480058c000042400c0302c0200861004000002103c0000cf2010071a00000c07988580a4550000004011004020bc0b0d8110000201c6803019018e41b401114ec005270040b000081181402c3703c440e40d00034014be0000205801000070000403401014020143d0340411416968000907a1a4730b800034ac00400000010680c0980a0080e1280702810008002a8000040009802000370100305443004b7044270145e050263900016c45000030080004c1500000000057c00100c12008090680005405000000001d0000404c6b008277181500001000950004209c2d0642a0041a33c0204d9d000020c1ac00185000000000100c0000c040082c004080125d63947208f99454483ca3248020cd50550106776154d20c7550320434d520cb419798e544825e650c9419e596100423d65950319b588548429d64d4b309d584540ca756115130cd553210431c5450d3097d8d544ca3d649442197d8d51c827561951219d584548c27561150309d98753082ce6215032b658352cc25c654c1209718d51c836652544409718d520425d63946428f990514c25d6395320b558752cc23e64d4c209ed95100425e639402097d95424c34c520c9108fd95401025d63141419718d5110a5d6314a1097596321025c63551109759621cc23c6454d209d587548ca5d63942429798f540c31d54cc431d554451cc23e6414c21e5d0d418c6796014c219758f528435653544209d98454082d66110e329798c54c42766114c2097189531025d65d0b30d3d4832442d56110c32d394d521023d65950208f59352c431d548c810d394d52042766115220c755330042d9600c9409d986544ca5c63553109759441cc25d63d4b10b3588404c29c645453097195214c27a6014c219758c540865d63d5220d514c514825d6394020b5584404c25d6094f429798c548425d6395121cd551310c6d66115330e550d414c7565394440ad59221c435453d4520ad592411073454d452097d95320ca6d65948108f590530823d6414a10d5544510ca3d65908409758f54842d56110e32cdd53514825c6550d308f99054082d56110f3097d8d52d074f520c9409dd85524425f6054e21b5185524c2766114810c7950320425e6294e40cd145415034e520cb308fd91528433454145209dd95310c72d5210b419d986534826f65484219718d51d029f6454930d558453507375414520d3948320c6d9600c820ad185435074c63548109b98b548c735
  | 4 => 0x44000000201400008002e000014110c8b1
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x50c17c200000910000024000000b000002000040000268200000300003000007001000007207040a2ce3aa4a919551700c9510822cb80ca1928385591510c730c2ac8a88a39844c72594414c322310a298241431c95415130a28e2aa0a898709544c1200828ab98a8a0e21855935194632a28eaa1a8298e156550441cc28ab88a8a1a61929896014f20a2ceca9a8220e1754586548cb24292c019281259da3250441c88a530e849861564544514c24aba4c319263855516115032c2acaa08829853170151410870aaa2c221863455cc5150540e82a2982401060e6414a214c30aaa2c22a261455cc5450510a2eeb1928220d15750c9411070caa2c02a06583150624c120c2aa8b08861951573151410870caa2c019041511c95114530c2ac8a88a2196155458454cc28bb82a6a0883451d15114530ca2a2b00a21951574145314c30aaa2c219063451d95350441c2aa8b08879851674d46518cb24292c019221455c65450e32a28e4a9a8220d1475504414c28ab9ca8a0e43255ce6190941
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x80010a04825516115130906829d95350441a0482595411053081686dd63250441c05641c95114530814875954110530
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
  | 7 => 2*((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/28+packedAt s5K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/267+packedAt s5K5 (21627+(h % 267)*10) 10) % 801)
  | 4 => 2*((h/323+packedAt s5K4 (29678+(h % 323)*10) 10) % 781)
  | 3 => 2*((h/53+packedAt s5K3 (2744+(h % 53)*6) 6) % 56)
  | 2 => 2*((h/9+packedAt s5K2 (360+(h % 9)*3) 3) % 6)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xe1fffff07fffff81e1ffc3fffc3ffffc38f1ff
  | 1 => 0xfe07e1ff83ff8ffe01e1fc783fc7f07e274e73
  | 2 => 0xfff801fffc1ff0fffe01ff803ff87f83c78f9c
  | 3 => 0x1ffffe000fffffe00003fff8003f80fe0
  | 4 => 0xfffffe00000000ffffffffffc0000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x202080110001000020220088880892100810a5
  | 1 => 0x44915322194a189610d0e4511645216a234652
  | 2 => 0x8852444428d4012ac201490224904d08c58b18
  | 3 => 0x1d65998952872acd75742044bb260633780de0
  | 4 => 0x1186110e63184cf19999b26702040843b6e000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfaeae8a8faeae8a8faeae8a8faeae8a8faeae8a8faeae8a8faeae8a8faeae8a8faeae8a8faeae8a8faeae8a8faeae8a8faeae8a8faeae8a8faeae8a8faeae8a8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_38867
namespace PEqualNP.Outside.L_meta_38867
open PEqualNP.Outside.L_meta_38867.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x100241800e00000000408300102000204000000000a160000004200b6040000000040850e1000504680001200000063408200ff0c0097c51007f8c805fe53017fcc409ff52017f14c03fd1001ff50c07ff4300ffd0001fe3100ff08009fd5200ff50001fd2101ff90803ff5000ff48005fc32027f54c05ff32027f94403fc4001ff95003fe1001ff50805fc4300ff88003fd50007fc8407fc42005f94403fe40027f14403fe5001ff50403df3001ff55003ff30007f4c4037f5001ffd0409ff5100df54003dd30007f4c807fc4101ffd0809fc52017f90c03fd30007f88403ff2001ffd5003fc1000ffc4009fd5101ff90407fc54027f94803fc50027fd4c05fc3100ff8c001fc21
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xa44205ff194210affe859086ffd428c40ffe1964209ffd502103ffe421083bff314840bffb284203bf99231037fcc01088ffe408c801ff90c420aff54821007fec69080afc6308417ff9844200df94721007fa42108777f3094405ff1926220df5413205ff8a11086efd648c40ffe3046405ff19021065fec19080bfc308c413feaa0420dff08121005fac790803fe2148427fea944200df9452102ffc8318833ef20c84177fb044216df9972110dfac8990127e61944017f3146217ff90131006feca990767f60944037e306421affd4231006feca90833ff50c841dfe1924202ffd0d320affe839088aff654c84bfe28c6405ff04021017fa8719017ff608c401ee31a4205df18a510c7f8c898806fc600840bbe084a207ff0832110ffa8499003f72148405f61946407ff19232037fe6010887fe414c81fffa124205ff0422103ffec19082ffd408840dff180420dfbc812102ef8c72880afe618c405fea1a6201bf9823108ffcc71080aff634c439ff32c6217ff581310ddfec918862ff644c40dfe2804222ff59532017f86099033ff40c84057e31a420fbf5912103ff8c190897fe658c839fea8c6200ff8ca2103ffe419081bfd4008419ee986420bff8c221004feca9881afd6008447ff3046402f7cc13202ffca310803fe31c8425ff324421ddf8c2510adfac990887ff544c80bff2884223ffc42320affca990837dd304841bffa02420bbf5822107ffca8908777d1094421fe32a4200bfd8c21117faa29907f7d439440bfe20c421ddf5025105ffa2110812fc65484077f3204202bf58e320dffaa91881bfd10084037e3026407ffd9632037fc801080efc6488401feb146204bf195310b6f8a390802fd638842fff882621cff54a3102ff821188177c4194421ffa8a4215bfd932102efec128887fe644c837ffaa46205ff10421077f8c69081ffe320842dffa96420fff591210bffc409881ffc328c82f7fb026210df1452102ff8a210817ff658c435ff2846216ff54f2106ffe409080aff624c82bfeb26421aff44231007fc629084efd658841bffa824200f78c932017fe629883fff4148405fa18c621bffd0a310fefcc928837fd5048441feb02640dfb48121065fac190803fd32c8401fe9884210ff54d21067faa1908127c654c80bff28c6215ff15321067da4190837fd30484097e32c620bff90221067fa619085bff51c843bbf204a210ffd492104dfac81081fff64c8401bf28a6200f78ca31007fa6310837f510484077f324640fff15121125fec91900bdf328c801fa9084203bf19121097fa8710853fc43c84337eb2a6202ff0c93103ffca59081ffc208c845fea926409ff50c210977cc910883fe504c835ff1046202ff14d31017f8a699033fd60c8401bfb2a6202ffcc231007fa649085fff604c421fe2924206bfd8021
  | 1 => 0x3fe43084097f32e420cff14321017fa609908bff524c805fe21c6220ff54132017fe6518833fe30c8411ff298420dffcc1210d5fac118847fe438840bfe32c6222ffd4532005fcc319083ff204c833ff32a6202ff10d320077ac910887fc544c8097e32c641edf90e51087faca9080aff634c81bff3024211ff94e2106ff8a09085bfe51c8419fea064200fd8842102ffec91884bfd4188417bfa844204bf995210fefa8328843fe51484437fb22640affd4c2106ffa8090817ff628c411fe298420dff4412103ffec119033fd10c842dff32e4206df54021017be6119042ff65484057f31e4202bf58e3108ff8a710873fc528c405ef9826205ff0c631007fac319023fe6308449feaa46419ff5453106ffc609086ffe428c42f7eb02620bdf5422103ffec31901ffe32c8445ffb2a6420ff10132017f8629904bff4388449ffaa46403af99221017e8629888bfc524c827ffa9c4223ff04232057faca10827ff4308447ff2846400ff58c210eef8612886bfe108c41ffe20a4222df1953212ffaa519003fe3248413fea104200ff98931117fca49907f7f4394431ffaa26201bf9813210ffc849900efc644c419ff206421bf7d0e3101df8c919043fe6548437fe2146219ff54931006fac72886bfd208c425fea144217ff941310cdfeca98806fc608c801fe98a420dff901210bff82098843ff654843fbea14a206ff0c021007de421088ffd108c80bff2084204bf996210d6fea118802df6348401ff30a6403bf1932102efc8328803ed2108441fe3026409bfd9021017fe6119003ef2188417fe1844216ff147210eefcc128817fe41884077f3264215ff50f210cffeca98883fe104c847ff1046421ffd9132107fcc099063fd544c44b7eb2c6402ff94e3100df8c110803ee214841ffea1a4202fdcc63103ff8cb19012fe658c80bbfb1ca205dfd8a51007fac7908037d6294405ff21c6223ff14232017fe63190777c209440bffb244221ff10932097faa910812fc65c8441fe902640cffc4321007f8c49886ffd418c4037f3046402ff14e31007bec690843fc5148405ff9826207ff1932112ffca31900bdf308c4057fb0a6219ff1453111ffa8119057fe64c8401ffb126214ff98f21007fac29902ffe6088401bf194a223bfd8232035fcc31082fdf30884017e30a6413bfd9621004feca90837fe204842ffe282621adf54231057faa21080bfe308c833ff28a6202ffd4d3205dfcc210833fe20c840ffe32e4204bf19532005fec69080afc638841bff8824202ffd0e310f6fcc72885ffd404c40def9804202ffd4e3110ffa829900bfe434c801ff30c6413ff54621017fc60988127e65c8417ff2844205ff1923102ff8c118853ff31c8431fe20a621dd7cc251017fca6990837f504c82ffe8826202ff8c231037fca01080adc6348425ffa
  | 2 => 0x32117f8a2990777d3094425ffa0c4205ff8c62107ffa8490803ff614c815fea984221ff5913202ff8c01080bdc538c805ff98c621abfd823111ffc211903fff434840bbe288421fdfd065112dfecb1908ffd208c801feb1c4205ff8c4210ecfac128837fc604840ffe2146406ff4c02105fea211087f7d6494413ffa08420cff0c32103ffecb9084aff648840bbe28c4206ffd402112fbea7190027d65c8441ff8826415ff9072102efca31884fff52884097f32c621ddfc82510bffc209882fff508841fff3224205ffd8c2103ffe4010863fd644c415ffa90420bff5822109ffaa71088ffd608c821fea8a4209ff150210bffa4098812fe654c4077f3226406ff54021107fc4099093fd648c8417eb02640dff58121057fea21082fff2088417fea844202ffcc53210ff8c899003fd3288437ff3246213ff5962111efea11900bfe534c425fe2a44218ff9913100dfcc11082ffd308841bef9824213ffd4621006facb90803fd32084457eb2a6424ff506320d7f8411880bfe434c41fffaa24208ff10c210dffca91881ffe520841b7fb024221ffd093202ff8c9108037d3294423fe21c4200bf58a31017fc8719006fe60084017eb0c6422ff19532017ee6298847ff328843dbe21ca200bfd8f210d7ba6118832fe62084397fb2c6208ffcc82106ffca09080bef324c847bea846420bfd8132017f86499063fd414c413feb204216ff547210f6fe652886bff408c417fe204420cf7cc32106dfac51085f7d504c42ffe3026204bf19421037fac01085bfd52c8413ff3204202f710e3107dfec890837ff604840dfe2004202ffd4e3201df8c810833fc10c843bbe204a21aff9823102ff8621084ffc5288401bf314a215ff1072103ffec790883fc204c8157fb284205ff0c6210affaa99081ffe4208433be32a6200ff4c721007fe4290857ff54c84017fb126205df0c65102ffec010817ff6388449ff2a46407ff14821107ba60990177c518c401ff314620cff94321127fa851904bfe42884057f31c421fdf90a51085faca90802fc624c401fe30a6403bf19132107fe8099072fd658c435ff9046212ff59221017f8a71900bff434c40ffe2104202ff0c232037fc20108137661944097f32a6402ff54e31087faa49084bfc4288439ffa946218ff509310d7faa118817fc628c405fe9946217ff98131037fa40108777e109441fffb22420bff8422106ff8209080bfd534c843ff2a26403bf992210c7fc829886ffc548c43fbe214a202ffcc932057fcca108777d6094413fea084202ff0c1310eefa412882ffd2088439ffa8c6202ff4c23107ffaa89080afe628c849ff20c6424ff1063202ff8cb1082ff71088439ff2946222df14532005fec29908efd608c819ff9864206dfd402100dfcc090897fd518c843ffa0a6420ffd41320d7f8811882
  | 3 => 0x80813c002601f01c000940108c0501857070071162b01402000000000906c0201429008980042b050330040d04c000e81e4280000dc2000290040100c0013c000bc4808cd9114750dc000104c008e002c1b007bc6298802ff638840ffe2964214ffccb21077f88690806fe60c84017eb1a421bffd0631095fac91086bfd408c40bfe28c421aff1423102ff8831888fff408c82ffe1026223f74c232017be6318893ff428c839feb2c6202bf18f2110ffaa89903bff324840bbf30ca219ff1493102ffec810883fc104c835feb046218ff10931067f8819080bef328c829fe18e4218bf59131087fca49084ffe65884097f328421bff5923112ef8a31901ffc618c805ff9826405dfc42510b5facb908337f50c841bfe2024217f74c13102ffe201083ffc644840fff2164202ff54e320bffe80988177c6494447ffa846424ffd0632015fcc69083bfc3148431ffa126225ff59632127f8a919017ff1088445ff32a6406ff88021017fc651883ffe4248441fe2826420ff5013202ff8c110812fc6588429ff21e4218ff9513108ffe6310823ff310843bbf104a20fff1092103ff8c790883ff604c833be28a620cff8432106ffa409080efe644c4015eb24420bff88221117fca299017ff658840ffe21642049f19531017b8631907b7f319440fff9046425ffd4a32125fac919033fd20c841bff082421aff902310b7facb9080bfe304c80bbf28c4205df94421017fc629888ffd508c8037e3026220ff4413202ffc421081ffc320841bfb8824218ffd0531017b8651885fff504c417ffa044221ff105320bffaa0988177f6494405ffa9a6202ff4c232017faa69883bfe63484093e32a420cdf54321077fca69080bdc314c419ff3064202ff4c131007fac690867ff524c433ffa8a6217ffc8131017fc649901ffe528c801fb90c421edf0ca51017fa871880afe63084037f3026211ff0ca210c7f8a89880bfc438c841ff202640ddfd412112ffea319067fc654c40ffe100420dbf581210a7fca790817fc6308405fe21a6202ff4c9310affa8390817fc518c405fe1946202ffcca3206ff86090817fc6388401feb126214ff14f2101df8c91884ffe528842ffe20262009fd953200df8c11883ffd4148417fe1044200bf58c2104ffe8410827fe540840bbe304a201bf18121127fcc91904bfe5488405fea1a640eff90d21037fe801083bfc5348447fe204640ddf541210affa859080bff324c4157eb284206f74c021086f8ca90817ff6088431ff2126207ff90a3203ffec91905f7f504c405fe18c6418ffd913102ffe211885bff53c843bbfa04a216bfd97210eeba612887f7f4294417ee9844202ff0c53107ffc829080bff438c833feb2a6202fb0c932097fe851081ffc528c821ffa9a4219ff9493101dfcc890857ff43c8405ee1926402ff94e
  | 4 => 0x180100c06010171080075c0e0180203800d2817064015b41203c1a0000700c15060c30002a01c2319c0000c0400c0107c9a02c010001600033038008a4010080500025000b104c1100405640041b80102c2c03441078d01300c000290d415034030008b07000014050003000cfa014580041800803054000000602026138041300605068068010480400c0000c0300802ca0150b0b00481d000100fc0f02800a840f084250340917800010000c80b0000900002010663901b0080105416024060140f024005dc180580f000000004f030683442b001f21946a09c160100b0708200c260001602006074fd0140f028e400030064071b8380b82e0000101400138050086a078030862b35801060020ac38158020d00300c000255d0381b0200400
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc6358d210a4fd73d8f21005dd7018d21006df638c9210247c7558c210067d40d953101cfe7458a3102fe710885210075d30d953202e7e5158e210065d30d95320076d75c86210075f3059721006bd3059221014de76d8d21016dc634c9210065f63945210067e305972100cfe7058f2102d7f7258a510067f10d95210067f50586320a6dc63c852123d7d704ca510057d70d95320057f755893102f766198a51006bd20592210247e76d95310067f41d9531007d51018d21007cc63885210fd7e7458a510067c6558931004ff75d85320067d105972101cfe7458632004ff7058d2102e7f62945211bfe551c86210047d70d95320067f40d9531004ff70d8d2115f6f50c84210067f65d893112ede658c93222f5c518ca310067e40d9532004ff7458e211cf6d20947210047d70d953124e7f608ca510067e10d9521006bd644c62121f5f508ca31046f531185322167e618ca510047f7059721006bf5159221005bd7498931004ff745863202f6c6258a51006dd74d8d210fd7c748ca51076de53d8d210075d5018d210b57c754c721006bf505922102f6c51c8421006bf30592210067e10d953114fe5524842102ebc5159221024fc7558a311afcd30c86210076f75484210067d658c721007ce628ca310067c42d95310f57f724ca5102eec2158a3120e7f6494531006df54d8d21006f776484210067c42d9521006ee20d89310067d30d952103cfe72d8c2103eee42189310067e70d95310e67c658c521006ed6218931006dd634ca2103fe66248421006dc628c53103cfe72986320247c75586320067f70597210ed7e708ca510067e60d9521007d4734842103cff7418931006dc54d8d2113fe73148421024fe75d8c210f67d30d95310f75f308ca5103f6f20597210f67c43d95310067c43d95210067f509863203e7c21597210247f76597210f67c31d9531006f541d853200cfc709863208cff7258d2102e7c51986320067c7558c2103cfc7598a310067c51d8f21006df71d8d210a6df30d8532046ed32189310067d6458a5102ebf1059221007cf2018d210067f40d95210067f50d8f2103fe432484210067d20d95320067c60d95320b67e71597212367d604ca51006b710592211fe7f609453127e7d72d953202ded71c84210f75f30d953127e7f30d9532076de71d8d2102cff701853203e7c7259721006dd54d8d21006df638ca2102e7c5158e210067c305972103dec724c72102e7f6098a51006de41d8d210067f30597210065d3059721004ff70d853202d7e7198a5103eee3298a3102e7e5158a310f75c324ca5103ede3258c2100cfc705863201cfe74d8931006df6388521006de6518d210ddde748ca310067f41d95210f67c639472102f3e5159221006dd50d8d21006dc6018d2102e7e6198a510067e71d95320077651c8521
  | 1 => 0x972102e7d769472103cff74d8f210057f7458a510067c70d9521006dd53d8d210057f7458e5100cfe70d8931225dd708ca310057d7398a510067e40d952127e7e30d95320067e43597210067e74d9521006dc75d8d210ce7e71d9531006bc73592210067e40d953102cfc75d8c210057c7258e510f57c7358a510067d10d95320f67c63945210247e76d952102cff7418532006dc50d8d210ee7c609453102ebc2159221004fd74185320067c6558d2103ef461586320057d718ca5102f5e3158e5103e7e725972102f6e51c84211776c6588521004ff7058f2103ef571d8f210067d64d95320057d7458a510067d20d952102e7f6358a51006bc305922123d7f704ca510067d20d95310067f71d9521006f541185320067c41d95320867e71d952102e7e6158a5124f5d308ca510ce7e654c72102ebe51592210f57f734ca510067f30d9521004fd7498a3102d7e764ca510b67c65c8521004ff7458d21004ff7458a3103cff7598a310f67f30d9531004fd7518532137d5304842102e7e6158e51006dd30d8e210067e6558f210057f7558c21017d6618ca3102fe651c8621006bf73592210067f64d9521006de20d8d2103cfc7518931044ff764cb210067d71d95321ff5d3094531006dd3058c210f77731d9531005ec724c521006df53d8d21024fe755863202d7c7158a5102d7e718ca51006de64d8d2100cfe7058d2102ef671d8c21005f576c86210fd7e744ca510067f325972119d7d70945211af6d50c86210075f658c53102fe66288421006bd755922103ef761986320067d60d9521004fd7058e2102fae64c86210067f654c5210075f50d8d210069d3059221007cd20d8d21006dc70d8d2114f74754842102cff7498632004fd7098a310cd7e75989310f67d31d95310075c51d8d21004fd759863200cfc70d8c21017d7618c531016de634ca21004fd7558c210057f754c82112edc658ca31006dd301853201cfe74d85320075d4358e51006dd41d8d21006dd3018931004fd75d8c21004fd7058a3102f7671945310557c754c821006df43d8d21024fc75d8532076de7618d2127e7c30d9532006dc41d8d21004fd74d8c210ed7e7098a510065f6518d210067f42597210057f768ca510057d7058e5103e7f605972108edc5358e2111776614ca51006dd71d8d2100cfe7098a31076dc3258a31004ff7058a3102cfc7158a310067d40d9521006bd51592210065f305972102d7f7658a5101cbe74d8f210067f10d95310067d42597210057f7498a512147e769453102f7651c86210067f639472102e7e51d8c210f75c31d9531006dd5358c210067f60d95310067d6358a51014fd7158c210067c72d95310067f65989311de7f64947210067c5158632006bd72592210867c72d9521006ed42189310067d43597210067f5018931076d
  | 2 => 0x10ebe644ca210067c65985320067d5058d210067c20d9532006bf325922102d7c764ca510047d75d8e2101cbf7659221024fc7558f210067f5058f2102ef63198632006de52d8d2102ebe31592210057d768ca510aebe64c86210fd7e748ca510fd7e7458e510067e64d95320a6df3158f21006bd655922102fae7488521137d7304842102fe77248421006dd60d8d2102fe43148421024fe75189310057f754c4210067d6098a510067d6058e510067f315972103e7e42597210067c5158f2108edf30d8e2127e7f32d9532006df10d8d210f75e4358e510867c71d952102cfc71d8d2103eee72d8f2127e7d43d953202cfc74d8c2101cbe74d8e210f67c71d95310f75f3094531004df70d8d212775c518c9320a5f771589310057d75d8532006dc42d8d21006bd7059221076ed3258a310f75f328ca51046df3058c2103edc3258f2102e7c5198a31006b510592210057d75985320067f65185320f67e63947210fd7c744ca5102ef631185320ed7c708ca51024fe75986320047f70d95210069f305922103cff7018931157d530884210067c64d9531006de10d8d210067d60597210067c30d9521004fd701853200cfc7018532007cf73484210047d75d8532046df301893113775504842101cbe7498632005bd7498632007d5718ca31046df30185320067d654cb2103ef76048421004fd74d8e210067d72d95310075f6518d2102df5768842103cff7098a310067f42d953202fad64c86210065d30d95210067d50d8e2127e7e31d95320b67d72597210067f5098a3100cfc70d8e210a6dc31d8f211aeed60c86210dedc648c5310067f7459721004fd75d89311afcf30c86210065d30d95310f75f304ca510067d5058c21006be305922103cfc741893121edd608ca31007d463c85210063d5059221006dd30d8d21024fe7558d2127e5f30d95320f75c3258e51006de60d8d21006df6018d2103fe720484210067d5018931006dd3058d2102edc6358e2102ebe74d8e21006bd105922103cff7498a3103cfc72586320067e60d95310067f74d95210067f64d953100cfe70d8e2103e7f215972102def76484210fe7e6494521006dd628ca3102ebd749863226ddd708c9321976d20945210067f50d893102cfc7518532076dc43d8d210067d50185320067c51d89310075f63945211376f5048421006df41d8d21007d6718ca3102edc3158e2102cfc75d8e21006df40d8d21075de76d8d2102d7c7158e510067c70d95320047d75d8f210067c65d8d2102e7d75d8e21004fd7458d2103e7c6059721167cd30885210857c754c5210067d64d952102f6c5148421006f610d85320057f7098a510067d75d8532006df65d8d21004ff7458c2103e7c3259721004fd7058f2102eed72d8e21006dc6518d2122f5e518ca311167c654c92103e7c205
  | 3 => 0xe75d853202e7f6458a51006be705922102cff75d8c210067c105972117fd530c852100cfc7058a31006bd644ca211577550884210067d63947210f76f324ca510f65c639452102e7e5198a310057d7694721017ce728ca3102ef71098632075df7018d21006de40d8d210057f70d9521006bd5259221266df608c9320067e42d9532225df708ca310067c7558d2102cfc7158c21157d73088421024fe7598a310075e324ca5102fd6718c5310057d75c852102ebc655922103cfc7258c2100cfe7058c2102f5c6358e510076f2058a51004fd7558e2102e7e75d8e21006dd20d8d21004ff75586320047f7558c21014fc764c9210067d42d95210ed7e7058a510067f6558532006df5358e210075d30d9521006bd64c86210857e76d952102ef671d8e210067f73d95210067c65185320f76c324ca510065f30d95210067e6258a51006bf31592210067f42d952102d7f70945310f65f30d9531014ff7258c212675f508c93201cfc7458632076df30d8d2102f665148421006bc52592212857e76d95321967d609452127f5f30d9532006dc51d8d210067d42d9531006bc2059221136f560484210247e76d95320077710d952100cfe7058e2101cfe74189310067d42d9532006df50d8d2102ef760884210067d43d952102ebf63592210067f64d95320067d70d953208cfe768c92127e7d32d95320f67d43d95310067f75586320f57c7398a51006df64d8d210067e30d9521006bc325922102fb674884210076d2098a510067d74d95320067c65989311157c7558532024fe7558f2102e7e769452103eee3218931076df3058d210067c65585320075d3058a510f67e30d95310e67e658c721004ff75d8d21074fd768ca210247c7558d2112edc658c93224e7d608ca51167cf30885210047d70d9521074fd768c72118f7465c8521006df634c5211676d5088521266dd608c9320067d10d95210067f62945310067c755863225d7f748ca51167e5108852102f5f6358e510067d50d8d210057f754cb210ed7e704ca5127e7f31d95322557d708ca510067d64d953103cfc75d8f21016de618ca31076dc3158632004fd70d8f21006dd30d85320b57c754cb2102f6e51484211167e72d9532006dd40d8d21004ff7058e21004fd74986320067c64d95210067c405972102e7f751853202cff70986321157e75d85320f57e7398a5102f5c518c5310067f7558c210067f658c521004ff7558e2102eee61c8421016dc638ca210067e72d953108edc63885210ee7e609452116ded7088521006df70d8d2110dbe74985320067f65985320047f70d953127e7e43d95320247e75d85320f67e31d953109d7c754c621004fd7098632006ed2098a3102d7e71945310867d72d95210057f75586320f67c30d9531006dd65d8d21125be74986320057f7548421
  | 4 => 0xca3100cfe70d8c2102cff70d8e210077510d9521004fd75d8d2100cfc7058d210247e75d8f21004fd70d8c211cf5d30947210067d70d95310067f655893100cfe70d853203f7575c862101cfc7458f210067f65d8532006ed42d8931005df7348421004ff74d8d21014fd7258c210057f754c9210867d71d9521007b510592210ed7c7058a510079f30592210067e74d9531024fc7558c210f67c32d9531007e7618852117fd730c8521075f57198931006ed76c862103e7f64597210067f65c8521076df3058a3102d7c7198a510057d70d9521147e741484210067e6398a510057d705972103cff75d8f210067f31d95210ed7e7058e51006de51d8d210f67f31d95310057f7058e5102cfc7198a3103e7e7598a31006dd3058e210057d75c862103e7d75d8f21006bd60592210857c754c92100cf576884210057f75585320067c315972102e7f6058a510067e63d95210057f764ca51074fd764c5210dede648c53102eee6148421006dd30d8f21006df51d8d210857c7558d210067e41597210073d50592210067e735972102edf618c531006dd4358c2100777754842103edc6358f211a67d64945210076d20597210067c32d95211afd530c862100cfc70d893102f6c2198a5102fb57488421024fe75185320067d5058a310ed7c704ca5102f7671947211bfe552c86210067e43d9521006bf52592210ee7e609472103eed76c84210047f7558d210067c65d8532076dc30d8d21007cd2018d21007d710d8d21024fe75d89310067f7558d210076f20d9521156f560884210f67e43d9531014ff7158c2108ef531986320b67f7159721004ef764842102f766158a510057d7498a5102e7c6398a511eddd708c53102fad748852103fe720c8521014ff764c52102f6e2158a51024fc75586320075f3058a511157e7598532015de728ca311de7d64947210247e75d8e210075f5018d210067f735972102f6f6258a51006bc75592210f777319453102ede3158c210f67e6358e5103cfe72d8d2103ebe74d8f21006f56118532024fe7558a31004bd74d8f21006ef2058a310067c40d9532006f710586320b67f725972107dbe7488521006dd51d8d211a67f6494521014ff7658c210fe7e649472103df572884210f67f32d9531004fd70d8d21004fd7598a310847d7694721096be72592210067c60d952102eec2198a31006ee201893102cfe7158c2109e7c65885210f77431d9531006dd64d8d210067f6518931004fd7458c2102d7c71d95310065c65d8d21004ff75d89310a6f631d853202fe44148421044fd73d8c210057f7258e51005df70d8d2103f7575c85210ed7c7058e51016dc638c92103e7c635972127e7c32d95320067d50d85320067d10d95310067c764ca5102fb710592210075c5118d2102c7c764ca51024fe7558c210067
  | 5 => 0x22f5c318ca5102cfc74986320067d7459721006be50592210f67f71d95310067d50986320067c735972102ef421986320067c41597210067f435972102cff75d8e210063f505922106dee768852102eee2158a31076df32d8d21005ef724c7210067f5058c2103fce728c9320065d50d8d2102e7c5158c21006de54d8d210a6df30d8f21006ef7258d210067c74d95310067f5018532007cd628ca31006de65d8d212057d70945310fe7c649452127e7f73d953203fe652484210fd7e7498a511afd730c862102e7c51185320067c511893102cff74d8c210067f32d95210f75e638ca5102e7e629472102ef41018532004fd74d853227e7c31d95320057f754ca2108edf3058e21076ee3258a310067c40d95311cf6f20947210057f7558d21006ef76484210b47e769452103edc3258c2102d7d7698a510067d60d95310067e41d953208edc32d8e2109d7c754ca2103f6d75c842103e7e3259721006df75d8d2102e7f6298a51006bf205922102fe7104842102eef6298a310067c70d953102eef60c862102cfc74185320067c65d8931006df42d8d210067d50d8f210a4ff7158d2101cfe7458e210067d50d8c210067e42d9531007cc7348421096bf7259221006dd42d8d21004ff7558f21006de6018d21005f4714c92117f7550c85210067f74d953102e6c6258a5102ebe7498632004ff70586321bf6e75c8621046de4358c21006f761985321e6dd608c53102ebc105922103edf7358f2103cfc7498a310067c10d953202cfc74d8e2100cfe70d8d210067d5058e210067d73d9521006de30d8d21006dd43d8d210a4fe768c5210075c65d8d21046dc3218532006dd305863202f5e518c5310f67f73d9531006ec20d89310067c20d95210f67d32d9531006dd30d8c210076f65885211167e654cb2103e7d7598a3102df772484212375d304ca510057f7358a5102def708852115fcd30c84210fe7c649453101cfc7458d2102dde718c5310067e42d95210067f65d8d21017cf628c93227e7e73d9532006bc535922103fe4424842102eec6258a31004ff7558a310057f754c72102f6c6298a5101cfe7458f210075f30d952102f77109452102e7f6258e5102dbf76592210075c6394521005bd7488521004fd70d89310067d74d95210067f20d9532006dd10d8d21004fd74d893125d7d748ca5100cfc7058e21006df6518d21006dc64d8d2101cfc74d853202e7c6358e51074ff7358d210057f70d9532006df638c52103df770c852101cfe7458c2101cfe74d8d2103d7f765972103e7f63597210067f654c92127f5c32d953202d7e768ca5101cfe74d8f21006de6418d210867e72d952102f5c3158e510067f6558d2112e7c658c921006dd30986320047f70d95320ce7e76d953102cff70d8c211af6f50c86210ee7e609453121edf608
  | 6 => 0x510d8d210067c70597210057e7694521024fe75d853227e7f43d95320067f60d9532007cf638852103cff70d8f210067e70597210ee7c60945210067f70d95210067f764ca5102d7c768ca5100cfe7058632006dd6418d2102ef5768842102cfe71d8d21006bd7359221006dd30d89310067c435972101cfe74d8c210067c629453100cfc7098a310057e71d953202c7e71d9521185f570c8521004ff7458f2102d7c714ca5127e7e32d95320067f40597210dddc748ca310067c51d8d21006be5359221004fd75d8f210075d638ca51137cd304842103ebd74d8f212157e7694531004fd7418931076df305863202ebe715922102f74319453108edf30986320067d735972114f6c754842103dde728c932006f51058632006df63c85210067f20d9521006dc52d8d210857e75c852108cff764c4210fd7c7458a51076df31d8d212367f604ca510f67d71d95310067e205972103cfc74d8f2102ded76c862102ef641185322167e614ca5101cfc7458c210067c10d952102e7f639453103cff751893103ede3258f2102e7c75185320067c10d9531004fd7558632006f510986321af7550c8621006df6418d2102f6651c8621126be648ca210067f5058d210077765c8521004fd75d8e2115fcf30c84211f75c658c53101cfe74d8e21076f63158632137e520484210067c5158d21076de43d8d21004fd75d853202c7e71d95321e6df608c53102f6c51885211676f5088521006df4358f21007d77348421076de72d8d2120e7d649453100cfe70d8f2102e7c6258a511e75f508c531006df72d8d21016dc634c521006dc20d8d211ce7f6094721006bd6458e2121f5d508ca31004fd7458a31006be65592211975d30945210067e70d95322157e76d95310057f754c521006dd70d8d2102d7e71947210067d505863227e7c73d953202d7e7298a51007cf20d8d210067f60d952103cfc764c72102ebc63592210867d21d95210867e76d95210067c20d95310057d70d953108eed32d893103ef421586322457d744ca510067d60d95320f76f328ca51024fe75d8d210067e73d952112d7c755863203df776484210f67e73d953115f6d50c842102eef60c842102f74514842102ebc3159221006bf705922102ebe215922102e3c5159221006bd505922127e7f72d95321167e76d9532006dd6518d2102ebf655922103ddf708c93203ef662484211cf5f309472102f6e51c8621006ee42d8931074fd72d8d210067e70d95210067f50d8e2102edc6358c21096bf7659221006dc60d8d2101cfc74d8d210a6ed3298a310a4ff764c821137775048421004dd70d8d2102f7671945210067f74d95320067d415972102e5c6358e51006dd6018d21006be6458e21046df30d8c21006f77158d210067f42d95311c7b664c8621024fc7558e2102e7c51d8e21
  | 7 => 0x8a310075d30d9531004ff7648421006bc505922102e7e76945310067e64d9531004fd74d8d2102d7f70945210075d3098a5112f76618ca510057d764ca51004ff7058c210557c7558c2103f7675c862127e7c43d95320067f639452102ebc715922103cfc72d8d210557c754c4211975f309452102def71484210067d6558f210f67c73d953103ef72198632045dc7348421024fe7558e210067c74d952102cfc75986320f76c328ca51005bd74985320067c64d9532004bd74d8e21004fd7558d2102d7e71945210067f72d95210c5be749893102d7e7158a5102ddf708c5310067f70d95320067f41597210067c71d95320067d71597210067f41d95320067d70d9521004fd7058c211376d5048421006bf535922102c7c71d952102cfe71d8c21004ff7558c21006be20592210f57d738ca510057f705972102eef60484211b5f570c8621006de70d8d2119775109452101cfe7498a310ce7c654c5210067d6394521004fd7458f2102e7f61945210fe7e649453100cfe7058a310067f50d8d2102f6e51885210067c74d9532006dd3058a310067d4059721006be6359221006f410d8532007d71018d210057d7598931006dc40d8d21007b564c862109d7e75c8621006dd3058f2102ebc605922102fe6514842102e7f6194531006df52d8d210067c73d952102cff7358c211157c75185320067e63597210067c51d85320067e20d95320067f105972102c7c75185322457f744ca51006df74d8d210057f7058a510067f50d8532004ff74d8931014ff764c7210075d50d8d210ee7c60947210067f72d9531096bd71592210047d70597210067c40d9521024fc75d89310057f754c6210067e41d9531004fd70d8e210f67d73d95310067c31d95210a6dc4358f210075d3058e51006de74d8d210067e105972102f7651484210f67e639452102cff7598632005dd70d8d21005f7714c9210057d7458e51016de634c7210ed7c7098a510067f658852127e7d73d9532006df638c72101cfc74d89310065f65d8d21024fc7558d2101cfc7458e21004de7618d21004fd7058d210067f70d9531014fc764c52102ebd74d8e21006dd75d8d2103e7e75d8f21006df634c9210065c6518d2102df4714ca2103cfe7258c21006be60592210067e41d9521076de63d8d21005ef724c521006de42d8d2102ede3158e2102e7e51d8e2103ef66288421006dd52d8d2102ebf605922112ede658ca3115eed60c84210067d7059721006bd648ca21006de50d8d211976f20945210047f764ca5103e7c4259721044ff764c6210e57e7598a31006dd3098a310067d41d953202cfc764ca2108cfd73d8e2115777508842102f766158e51006df7358d210b67f76597210057d7598a3102e3e515922102e7e5158c21077d4314c52114fe5514842103f7675c8521007d
  | 8 => 0x247e7598a310fe7c64947212557f708ca5102f6e2198a510075f3098a511967f609452102d7c71d95210cd7c75589310067f5058e210067f71d95320047d7598a3103eec20189310067d5058f2102e7f6058e5102f6f6298a51006dc74d8d2102d7f70947210057f714ca510fd7c7498a5103edf628c9320067d74d95311ce7d609472112e5c658c9320557c7548421004ff74d85320065f50d8d210067e64d95210065c51d8d210067c41d952101cfe7458d21004fd7558f21024fc75d8d210067e20d9521014ff7658f210067d6058a510079d30592210075f658c9320a6df3098a310a6df3058f2113fe73248421006be1059221006df20d8d2127f6c32d95320067d20597210067e20d953101cfe741853203ef576c862102edf7358e211e75d508c531006dd72d8d2100cfe709863202f5c3194531004fd701893102eee72d8c212775c658c932076dc53d8d2127f6f32d953202edf7358c210075f65d8d2127e7c72d9532136ed60484210076d20d95210067d50d89310067d40d953218f7451c852102cff74d8e210f75f3058e510075c6518d21007d763c8521096bc72592210057f70d9531024fe75d8f210c6be644c62103ef72158632004fd70d8532006dd634c7210067d41d95210073f50592210067e40597211fe7d609453103f6e75c842117fe520c8521006de75d8d210067f10d9532004fd75189310067f43d9521014fe76d8d21004bd7498632006ef6298931006ed2058a310067e74d95320067c60d95310067d41d9531004fd7558a310f67f43d9531006dc10d8d21147e742484210067c41d95310f57e7358a510076f2098a51004f776484210f57e728ca51014ff764ca21004fd7458e21096bf71592210067e60d95320067c63d9521004ff70d8931004ff7558d21014ff7658e210067f658c9210b67c715972100cfc70d8f2100cfc70d8d2102eee2198a31006dc6418d21006bf75592210067f40d953203df770c862102edc3158c2102d7f7358e5100cfc7058f2100cfc70189310067e10d953200cfe7018931005f7714ca21006df60d8d21024fe75d8e21006bc7059221004fd74586320057d7098a5101cfc7458a3102d7e7158e5102fd4314c6212675d508c9320067d64597210067c74597210067e6459721005de7618d2127e7d30d9532006f641d8532016dc638c7210f67e32d95310067c42d953203eef2098a310057d7058a51004fd74d8f2108edf30d8931006be7359221074fd71d8d21016dc638c521006bd53592210fd7c7458e5102f3c5159221137e5104842102cfe7198a31005dd718ca310067f20d953108edf3258e21046dc3118931006dc65d8d2117f7750c85210067f5058a3103e7c6459721137cf30484210076d2058a510067d654c72100cfc7058c2102e7c5158a3102cff75185320067d509
  | 9 => 0x16c0484301a0dc018010000001882906c0000001201a01c2980a0c84a4010cc01a044000060060000a8091620087a01c3a01280001b0222300c81304800808001000068008380001ac0301807a4c00280ba56004060d2120008b60054380043f8ac0060600000001614c06000010024008250060093780917ab384a8270021e40100003068c0101c16abe80b0430000680303f0080782b80103601c3609a00006404814004000018020000240287733802c060010229100200001a00025c37000024e10000040481700206a04c0b3fd000070000000101083280000407809bb300223c048012b409c060183467182c8110140004700202e02c0880404c0ec038000a61340080c038008a9042016154e201204817c1b81a28c01007341010020003bb0000a81b0000040048580700ad396a8000da000250001440080201b048002ea0094920e8100011ea0c8030010041249e80003605c000060040080680403200c02006006000000040340180304d00e0840100e03e0100100d00019c0f800044008000570060054e80c028008038070740085604001a001bb01f0020380080623800805807000064013ca56201c0320700802c06b1707c0840c0020140240001d00e0085c00f01002165064a520140280101204a25027076064c483311a0180001802200d938000020701d8092f82542200000c02c0200503c00c0880f0080000001300420c08a6206e028130020267140c807002039b98000441447982502e100010000140080001705e00000809006024568090180500301100a01c0082236c26c2200201a00c0000b00000c000be0040002a9400060306301013e0500f81a19e12c000366401640303b00803c000050020000483d0000549a00c0240083480f01007c04002006154000350260ac0083902a000050000de0a0000050640280580300000400000004018dc0080020080000000200c0080604a0000000609cefc170090040600881900e0000e00102801000830030048c300003601802b740067f50d8c21004fd70586321d57d70947210067c6518931006f6101853202e7c51d8c2103fe652c862102f7451c862102f6c2158a510047f7558632006be525922100cfc70d853208eee32d893100cfe701853201cfe74986320075d30597210067d305972127e7d31d9532006be755922102f6c51c8621006de32185320067e745972103e7f2059721046de5358c211af7750c862102d7f7658e510067e6059721
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa6d821c3654848b4b90b886c69080317dc130597210062eb8261b2a6200a5d85dcb63484014bd0b306c690802ab608705922102e3328eec90842078de87d0d63c84a34bd0db1ca2908021fa1f43d95210043f43c21b2a4200a6e82043654842d0fd0f302cb9099b1718d7058e510052ec1c21b2a420087f855c0614c8038f4e0a86c6108121f21570185320f52f41ee5b2a6200c5e75d8f2148401c690a882c91085237e19718ca3100536c1080b2e421ea5e83103654c4010ff0cb82cb908029760c40d952103d3741020b2e4200c5f305d763c840187eeab22651083a3761c60d8d2101c5e422e0b1a4200a5d8310165c84014bb063a6ca9880a3720d74185322162f3b261b2a620087d8754363c840159b07100c4988121fe1f50d85320074b98620b24424287c8759531c84010fb0ea86c29900297a195018d210043f43841b2a6405c76711c7654c80b5a902982c61085a1fa1c10597210053ac0ce8b2e4200a5d8384165c84010fd0e28ac690807369c130d8c210043f436e1b2a6200c3d74d4363c84010fb01baac69080637e1d30d8f2100567410e1b1a4200e3541107654c80717908b82c51880297e0d41d95310062f982e1b2a6205cb4615d2614c8014eb02386ca90802a760c20592212843f43eca9924200c5f70cc165c843d0fd0fa0eca988169da04651853228d2e408ca31a42048df8754f634843d8b8c7baa62908031b54376484210052f42e87b1a4200a9e83081648840bccca2bb6431080297e156018d210043ec3c41b2a6400a6c8258d62944015b100b20c69093e97a0e70d95320055ac08a0b244200c7970d8365484014e902b06ca990030f5d150986320052ec1821b2a6200e1f5394d64884018b8c7baac690803175d475d8d210052e42ae3b1a421ea5e831c3654c4534dd05b8eca90817a50c5644c6210064eba26130c6400c9e74d8e214843d0f90fb2a62908023be1d621893112d2f42ec71944205c3e515d2618c8b54bb07186ca908029761474d8d212ec3e43a82b2e42118df8758a328c43f27d09bb465288421f61c60d95210043fc3ac1b2a640087f855d163484014bd07086ca909870f9d350d8e210fe1e3a2c8b14a24f87c87d9532484014ed03326ca990173994776484210071bc2a20b244205eb38044164884010f90ea82c6108030f5d150d8e2102c3e40eec994a200a9d83981648840147b08086ca9080297a1474d8d2102c3f40eeab18420087d87043654c8019b2e1b00c6908170f94574d8e210062e3aac69944200a5e8390365484071ef0ea0ec299003275d130d8e210052ec2c21b1a420087f855d0614c80147d0a182c9108028f61610592212962f3aa61b0a6400c7550dd921084010fd0e32ac2990171d94776484210043fc3aa1b0a6459a5e830c365484090fd0fbaac61080327cc17498632
  | 1 => 0xb02106ca9094b171d53058d210052f42cc831a4200a5d8590363484010ff01bb2652880317cc175d85320062ebaa61b0a64008f7815c163484014bb07b96ca908038754130592213655bc0ae4b24420087d878c3654840187eeab22631080317dd77358d213370f28a60b24420487f87d83654c82556b02382c9108030f5d350986320052ec06ca31a425ca6e821c3654840bac8433b4a2908165d20570597210043ec3c21b2a42058dc8754d63084019b2e0986c6908029760e64d95210056ac1821b0a6400abb805c964884090f90aba0c2990021fa1c10d953202c3fc3e21b2a6407cac625d2624c43d4bd06086ca988030f5d074d952102d5bc0220b244200a3d85081648840147d0818eca9080237a1e40d8d210052ec2841b1a4200c7475dd921084014ed02206ca9080237e1d6418d210243f43ac0b2e4200a5d83083654c8d1c3ca3982c91080317dd530586320045ec3840b244200a5e839c3654840153906b92c910802b6e0164d8d210055ac0c40b2442008de8794363484014bb0ba0ec6908121fa1774d85320043ec3ce1b2a6200e3541107654c4010fd0e382cb90802a7a1371d8d210053a40aa1b0a644fa5e83083654c80147f08b06ca908038754330592210f43f43c21b2a6200c7750dd921084019b6e0982c79080317e0d7598a31016673b0c710a420595c874c1639440147d0818acb90802b5e0d41185320f52f41c41b2a6266e1c514c164884014ed02202cb908172dc41749863201e5b3a283b0a64018ec87481628c4011bb0f106c6908031b1d7764842102d5b40c40b24424fe5b804c3654c8090ff0ebaec2990029e20164d952102c3f43ea030a640587e81dc365484090fd0dbaac4988021fa1f5058d210072ba8ca3b1a4200a5e8614463484014bf0ab26c69080317cc375586320062e3aec6992420087d8710b654c4014bb0a306c6908021fa1f6558d210046ec3ca1b1a420087d8798365484018bcedb1ca2908431b9db658852102f1b28ea2b24420087e8784165c840b47d03a82c9108031bd4376484210051ec2ee6b24420087e87903654c401878eab2265108021f61c30d952100572c1021b0a6445a5e81d4363484014bb07206ca9080317dd75358e210cc3ec38c1b2a6200a9d831c164884019b700b86c6908028fe1572592210062ebaa61b1e4205a7681d94614c8010fd0f182cb908029760e20d95210062ebaea7b1a4200c3e7559321884018beebb1a649094b179d530d8e2102e37b14ed28a4200a5f83593654840196ae9b0cc29900317d957018d212b62f3b2a1b1a4268e1c51cc1648843b8f4e0b04c5288023761c50d8d2135d56412e0b24421d87c8758163944014ed0232ec2990169d20550185320070faa4a9b1a420087d87843654c40195ae9b14c4988168f20750592210051fc22c1b2a6400
  | 2 => 0xd41597210045fc22e0b184200a7581103654c8018eeedbaa42108121f2157458c2102f33b14a390a4205a5c8650d63944010fd0f106ca90802a760e10592210043f43c81b2a42008bd84dc3624c4010ff0aba2c3190031bddb7548421005674364031a4200cd7631c532484010ff0eb26ca9880339547764842102c3e40ae1b2a6400c9c835d2618c8018f6e1302cb90816d920775484210056b408e1b1a4200a5e83983654840f4dd05382cb908030f19574989310052ec1841b2a6200a5c86d4063484018bee739acb908172d1c5644ca210f52f41841b2a6200acc864806348401c6ea1882c9108021fa1f65589310066cb8261b1c4200c6d765d721884018bceca80c6908030fdd675592212962e3aa60b0c6400e58604c3654c8db93eed982c910816ada0630592210051f42020b2e4200c6d721cb654c40147908b06ca990028fa1020d95210746ec3841b1a4200a3e8404365484090fd0fbaac69080297a166518d2100536c1081b2a426aa3d85941648848b4bd0c31ca2908178d14564c86210f52f41ce1b2a6200c7970540614c8df4bb07182cb908028f61031d95210052f41cc0b2e4200a9d839d564884011bb0f300c6908029761440d8d2100567c12c031a420087e87043654840147b0818acb9080297a1b30d952102d1fc2aa2b2442008de87883634840187cc9baa631099ea760e30592210062e196ec994a21087d8704365484af8bceda86c69080237e1d6018d210056741081b1a4200ad48644063484014bd0a086c6908a69da0772d95210056ac0cc831a4200a5d831c3654c40153d07082c910803a54c310592210052e42ac031a420087e87083654c4014db04082cb9080237a1c50d8d2100556c2041b1262058f4815c1630840153d06382c910802972156418d210051ec2ce0b244200a5e8384165c84018bae1b1ca2908028fa1660592210043f43e63b2a4200a9e839c164884014bb07202cb908028fe1120d952122e2f38ec728a4200a5f8558363484010ff0eb06ca9880297a1950d8d2132d4f41860b244200a3e85cc564884014b90ca80c69087a1f21d6358a510072db0261b2a6200a6c8259162944c187ce8a84c31907b96e0130d95310051ec2cc0b244200a9d8404363484014ed02106ca9080a3720d751893122f2b38ec728a4200ad88059363484014db04086ca908028fe1120597210054fc22c031a4200c7b805c365484011bf0eb28c6908168fa1751592210052f436a031a4200a6e82993654c4010fd0f106ca9887a9d60474d95310052f42885b1a4200a3d859cd648840156f02a92c9108121f21f5058c210ec3fc3a20b2e4200ab8805c964884010fd0fa82c6109a31718f7058e510062fbaec698a4200a5f835c565c840b0f90f886ca908039618130d95312dd3b408e1b2a4200ad58110363484014e
  | 3 => 0x1b2a6200a5c86543634840b56d03282c9108021fa1c6558d210056b40881b1a4200a5d8304365484014b90ab26c6909770f9d051d8f2100572c0841b126261c3e74d42618c8010fb0f98acb908028f21572592210051ec2021b2a6200a5e85d0763484014bd0c328c6908029de05705972100c6e43a60b1c420087d87d4363884010fd0dbaa64908029760c10597210062e41aeb314620087d8788165c840153d09b96c690802a7e1160d8d210043f43aa0b184205ab6819c164884010fd0e206ca9080297a1b50d8d210043ec3e82b2e420087e8790165c840f9cca5bb24210803365c130d8c210062e31aeb90a42008de87103634840187ce9b2cc49885a1fa1e20597210052ec1c40b2e4200a3c8448165c84010fb0f082cb908021fa1d654cb2101c77c3a85b12625fc9e744c2618c8010ff0eb06ca9080336dc13058c210062ebaa61b1c4200a9f835c9648840147b0a192c91080297a1640d8d210051ec2021b2a6400aaf825c164884090fd0bb86c2990121f21f50586320071aa8620b244200a5d80d97634840187ae9a86c7108030f993754ca2100c6fc3a61b1c4200a3d850c164884038f4e0a80c29900297e0d60d95210062eb8261b2a6452c5f764c165c840196ae8884c3190121f2157058c210066bbb0e69084200c75711c7654c8011bb0f086c6908021f61e40d953102d5b40860b244200a9d83941648849f4bd07086ca990021fa1f41d95210052ec2c41b1a4212aae821c164884010fd0fa0acb908063d21d10586320051ec2041b2a42008dd879946348401c3ea0982c910803175c130597210052f42c41b1a4200a3d8588164884010fd0e216ca98803365c130d8f2101c5e422e0312620087e86dd531484010ff0ab82c61080297a1664d8d2127d2fc0261b2a6400c7b805c165c849f4bd07206ca9904a2fa1c20592210051ec2e62b24420087f855d1630840196ac9b8a6510803175c330597210062f982ebb1c420087e87541618c8010fd0e086ca9880297a1630d8d210243e43ea0b1a4200a9d83881648840199eec39a42108121fa1f75586323061fbb2a0b24425ec5f76cc165c848bc3d0828ec6908028fa16205922100c7c402e8b1a4205ab68114164884018be60b86ca99002b360840d8d21076673b6c710a4200ace82043634840147d0b182c9108028fa17735922102eb310aed28e4200a3c84483654840b4b90c982c72893f93d8b658c9320052ec1cc0b2e420087e878c365484090f90ab82c6908039a18120d95210043ec3e83b2a4200a5c8350765484bf93eec982c9108021f61f50d8f211143ec3885b2a6400a5e831836548401c3ea1982c91080297a1851d8d2100c6e43a60b1a42038bc845c1630840156b03282c9108029ba0840d953200c6e43a60b1e4205c6e625da51c84014bb06386ca908029720
  | 4 => 0x2c841d1bb0e086c69080297a1771d8d210f62e39ac6b14a200a5d85990634840153d08086c6908028f61470592210ee2e38e61b2a420087d8710365484011bd0e106c69080f279d143d8d212c62f38a61b2a4200a5e8388165c84010ff00baec29919b931893058a510243fc3ea13146200c3e74d96614c8014ed03a86c29900637e1d30d8d2127d2f41c41b2a6400a3e850c9648849f4bd06086ca990021fe157058d210062f986e1b2a64648bf87481648840bc68a2882c91093e1fa1e20d95320061eba0e9b2a6261c3f76d4164884018bee0a86c69087e4f2117058a510074b98220b24421ea5e83843654c401cb700986ca908121fa1b755853203c76412e0b18420487f87d4363c84018be61bb265288023761c6018d210043ec3881b2a6205ab48154964884010fb0f326ca9080297e0363945210843ec3865b2a4200a9e8418063484010fd0e106ca9080317dc330d952102c3e432eb90a421ea5f804c3654c4018bae0a86c6908761f21d6058a510043ec06eab0c6400c5f754c1634843d4bd07206ca988029b60840d95320045fc22e0b1a4200a5d80d8e514840b0f902b86ca908029760c70597210052ec2885b1a4200a5d83103654c4014bb07206ca99163179c730d95210072db0261b2a641e95e83dd26294401ce0c0886ca908029721560d8d213472631660b14a200a5c86d43634840153f08906c6908023761c40d8d210146f438c031a4200e5b804c165c84010fb0f386ca990021f61e20d952102c3f40aeb3146200a5d851c3634840159b04086c6908028fa1663592210062f3b6a031a4260c3e7454363c84014bb0b300c690816ada0470592210066db8260b1a4200c5e76194634840b0f90fa80c2991c29d20570597210051f426e5b2a420587c87540614c83f47d09b1ca3909a68fa1450592210053741021b2a6400ad681083634840153b09b8ec6908028f61070d952102d3b40ea030a6400c5f768c932944014eb02206ca988169b21b2058a510062e28ee1b1a4200c3c655d221484bf93ce8986c7908029760e10d95320052ec1c41b2a6400c5d731cd65c840b56d02102c91080317cc37558d210054f420a3b1a4200a6e82103654c40147d08386ca908031714570d8d210052fc1a83b2a424f87c86dd5614c8e94bd0db2c6499002b560420d8d2102c3fc3e21b2a4273a76811d3654c4014bd06206ca90802a7a0e60592210054ec20ebb1a4200a3e8418365484014ed03b2ec29919b171d5301853202cae43a86b1ca20087d879c165c840156b02102c91080297a1440d8d210fc9e422e0b1ca262ab5819c1648840b0fd03bb265288021f61f5098a310052f41880b2e4250c5e764c3654c88baaca2b8c651880297e0d4159721005aa40a61b2a6200c797054363084014bd0a386c6908029b60a64d953100536412c
  | 5 => 0x80317dd53058c210066cb80c1b1a4200a5d859c363484014ed02206ca988030f99175c86210051e422c1b2a6266c5f754c0614c80147d08106ca990029da0440d953231c5e43a40b244200a9e839d5648840147d08086ca990023de1d61185320043f438e1b2a4200a5e85180634840b2bf0eb1c65288028fa16105922101c5f426e1b12621f87c87507654840153d08386c6908030f9d065985320052ec18e1b2a640087e87843654c8011bd0f086c6908029760e40d95310052ec00ca31a4262ab58184164884a3e8ca239a42108029d60664d95320043f438e1b2a6400a9d8314164884010fb0f206ca990029761630d8d210f43e43a83b2a620093f845c163944014bf0a886c6908021fa1c764ca510f52e41ac0b1ca200e6765d8621484018bcedb28c6908032d99176c86210043ec2ee9b0a6407d64215d721484011bf06baac69086e3721d41d8d212c43e43a20b2e420087d8754363884018bee0328c69080317cc37558c210054ec2041b1a4205a6e82989629440bd6620b02c9108028fa1470592210076430241b1a42008fb805d163484014dd04086ca988161fa077558d2100566c1841b12620087d87983654c8014bb06306ca90802ad60630592210051ec2c60b244200ad686c40634840187ecaba442908028f21160d95210052e41ac1b2a42018dc83dc163084011bd0e086c6908028fe1510592210043ec3ec728e4200a5d83883654c40147b08306ca9080336dc13058e210062ebaec790a424287e87d9531484014db04086ca990030f5d564c86210063cb82c1314a20087d87d0f65484010fd0fa1acb9087b179db658c5310043ec36ea98e4200a6d82103654c43d0fd0eb2a6390803174c3764ca510053b40841b2a6400a7581083654c8010fd0fa82c319002a761372d8d210ee2e38a61b2a4200c7970183654c4014bd06086ca908161fa0770d953200667b18e498a4200ab584043614c8ab1bf0ea96c6908031e5c360d95320051fc22c1b2a6200c7b7058165c8401c6aa0882c9108178d94510592210046ec04ec31a420587e87540614c8010fd0e3aac69080237e1f6018d210051f42ce0b244200a5e8304165c84014bb07086ca988023761e6418d210066bbb6e6908420087f805d763884014b90aa0ec69080317dc130d95212c43fc3a21b2a4271a6d829c165c8401c6a8220eca908021fe0175d8f210052ec1ee5b2a6200a5f83507654c8010fb0f106ca98803a54c110592210043ec3881b2a640087e8710b654c80196aecb2643108178de1710592210054f42041b1a420087e870c165c840153b08386c69080297a0e20d95210071aa0882b2e4237a6f825c565c84014bb06206ca9914f710c4724c5210243e42ae8b1a420093f845c1629440b1b90ea1ac61099b179c530d953200667bb6e6908421687c875953
  | 6 => 0x56ac08e1b1a420087e870c365484010ff0ab82c3190029760e74597212c43fc3a21b2a6200c9d744c363c84010fd0fb2ac2990029b60810d953100672a96ec9084200c3d741d3654c80153b07382c91080317dc36518d210064fba4e9b1a4200c3c655d2614c88bc3b0828ec6908021f61f41d95320054f418a0b24420087f87507654c80159b05320c6908021f21d5058d210043fc3aa1b1c420087e870cb65484010ff0eb1ca2908421f61c42d95210071ba8220b244200a9f8354964884010ff0ea84c51880297a1670d8d210074dc0260b2442008df835c1634848b8b8eb190c2990022fe1170189310045fc22e0b146200a3f84483654c4014bd07b96ca9080237e0d7458d210043ec38a3b1e4200c3d7414763c84bd8bced986ca909830f9d150d8e210061fba4e8b2e425d87f87507654c4014bb0b326c6908021fa1c7558c210243fc3ec1b2a6200cd970d8363484014db0531cc52897f279d130d8e210051ec2041b2a640087e87195624c4010fb01baac6108031edc16058e510043ec3c81b2a4200c9f305d363c84010fb0e182cb908963721d52d8d2102c3e40eeab184200c7970d83654c4014bd073a2cb9094b179d53098a310043fc02eb314621d87f8758262944031dd0db92629080297a0c70d95210062fb8261b2a6200a7681083654c4018f700b86ca988029761771d8d2100537c12c1b2a620087f87443654c80187ecaba4c4988021fa1c42d95210054e41aa4b24421d87c87443654c4450fb0e306ca990021f21d41d95320051e42241b2a6400a5d8308365484018b8cbb86c6908161f61f65c852102e2f3b2c7194a200a5e85dcb63484a91bf0ea0ec690802a7a1060d8d21006adb8260b1ca205a3c81541648848b8bee1b1ca2908030fd9574985320053ac0841b2a6200a5e8308365484018b8cab86c6909870f9d350d8f2102c6f43ea6b1c4200c5f70d43634840b47d02a82c91080317cc370d95310043f43aa0b1a421ea5e831d3654c4014bb0ba1ec690802a72116018d210052ec28c031a4200c5d704c36548401878eab2263108030f9d365885210243fc3ea1b1c4200a5c85443634840147f08906ca99002b560e10185320043ec3cc9b2a622287d87d97614c80153908906c69093e9720d41d95320052f41cc9b2a420087e87903654c8018bee0986ca990165b21d2058a510052ec2cc1b1a4200c5d70d4363484010f90e886ca99002b360870d8d210051e42a20b244200a5e8584363484014bb07386ca98802a7a0e50592210043ec3c80b2e4200c6e755db21884090f90ab82c3191169720550d8d210054ec20c031a4205a6c86481629443dcaec3b2c62988032718d74885210062e3aec698a420087e87cc565c840b8eced28e4290803175c330d95210043ec3aa1314620087d87083654c43753d09b1c639
  | 7 => 0x7f8759365484010f90ea82c3190179994776484210043f43881b2a6400a5e8390165c84018becbb86c6908024f613768ca510062ebaa613146200c9f835d2618c8010fb0bb86c299002a761051d8d210062e32ae031a4200adb8059063484019aa61bb242108170f1457498632004aec1ee9314a200a5d839c3654840b8dca3bb242109ba97a0c30597210043ec3880b2e420487f87d836548401cb700a86c6908031e5c060d95210054e422c1b1a4200a3e849c7654c8010fd0e206ca988028f61372d95210051ec2041b2a6200c7b70581629440187ce832cc4988161f2057598a310053741081b2a4200c9d74d8e214840147b0938eca99002a761060d8d210071dc02a0b24420487e86dd563484014bb0a086c6908029d60440d952102e1e28ae9b1c420087d87cc7654840f4dd04202cb908023be097058d210064f982e9b1c4200a3d8598d64884018ef02b82cb908029760e70597210051e42241b2a6200ccd30dd921084014bd0a306c6908661f61c10d95313953b40ce8b2e4200c5e7618e514840156b02182c9108029d60440597210843ec3841b2a4205c7451dd921084014bf0ab20c6908021f61e30597210053bc0ac1b2a6400c5f655c363484014bb0032ec69087e1f21d6458a5122fa328ee6908420087d80dd932944019ae61bb24210802a7a0e20592210043ec3ea1b0a642287d87083654c8019b2e0300c6908031ee0170d95321143ec36ea9964205c6c51dd9210840bc690b882c9108029ee0164d95210062f982eb314621ea5c83507654c49f4bd06206ca99003a550441d8d210051ec2020b2e420087f8754363c84010fb0fa1acb908029760c10d95320063a40ae0b2e4200a5c835936548401c9ea5296c690803175cc73d95212962e3aa60b184200c5c75dcd63484071bf0ea1ec690802a7a1075d8d210043ec3e83b2a620087d87983654c4015af02b00c6908021fa1b70d95210051f42ce6b24420087d8704165c84014b90c986ca908029760051d8d210052f418e0b2e4200a5d83983654840b968e8a08c29900297a166018d2100667986ec9084200a5e8508363484014bb07386ca990028fa1420592210043f43e83b2a640087d87993654c83f0ff0ea0acb90802b520530189310052fc2a83b1a420087e871c3654c4014d904b02c52893e97a0c70d95320046ec3c81b1a4200a5c835c565c843b0f90e886ca909761fe1d41d952127e2e31eea99242018dc874c1630840187ae8a86c79080637e1d30d8c210051f42041b2a6200e6920083654c8010fb0f386ca9094b179d530d8f210243e42ae8b0c6452c5e764c3654840147d08086ca988021fe1d64d95320051ec26c728e420087e86dc3654c8018f2e0306ca9900297a0e70597210056a40a61b1e420087e8710165c84014bf0ab8ec690803175ce6398a510
  | 8 => 0x30100014048a76000000210e20b6004170050080000002d000000000080040000000518a0000087300002800000002000218000260000980f00011c030000340040100900000000004000090750012a80940580300601c0281c21a000000050000080b00400a05c0001d00000c3102900e0004e00e02001c020000040200b9692780601220b0182d43300002002404000038044048030025480094b03604c0481d0300a000800002078050000040506f1e90180542780002a0000100202402c0080100c01c078220000b40000000e7c40c89e0002000880000a06055812010c786e932004002070030000040000326e000b080a00017c09803002008029d600201c0100000000000000000034060000160140a81a0000000000600063c0500400a00803033000010100210000382580c00019402029024008068220580240119f0261001381503e034080050100141b82000200c010110003440000002400802000004008008600000280000504a020000ce01e01401803326a001a000000010698001a2014000170000b00585208a00c010040020180000c022ef4000040000004e00b0a80080000204402c0008a02a004008110323cc0027d01a1b00a80000204402002014008001211020600080c020000000080000080e80600400c500000000006a1c30cc0000ca6c0000000d00081c000000a9016018000040028080d0010209400804a00a0040185e05e0001a800038060018000140a80080002c009240390220000080000200c5c80605e004880530200080103101c02c008192f8000008ed0100000580800e01403000000030018600120001800700003c0b82200a0241200929604002803000018000020000e00001308a000158060080240000800a0680100f0060000f00608268c030165b61f2098a510043ec3c21b2a64008
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x41803001003471194730dd9210840b078985c1501853202d19a4750dd9210840b86481ddb75484213371194530dd921084a3c4651dd873484210051664051dc3634848bc4651ddb73484210078454130441648840105f985cc7359721
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x2
  | 6 => 0x209
  | 7 => 0x3
  | 8 => 0x20c
  | 9 => 0x20d
  | 10 => 0x20e
  | 11 => 0x1409
  | 12 => 0x1549
  | 13 => 0xb09
  | 14 => 0xb0c
  | 15 => 0xb0d
  | 16 => 0xb0e
  | 17 => 0x140c
  | 18 => 0x140d
  | 19 => 0x140e
  | 20 => 0x154c
  | 21 => 0x154d
  | 22 => 0x154e
  | 23 => 0xb49
  | 24 => 0xb4d
  | 25 => 0xb4e
  | 26 => 0x1449
  | 27 => 0x144d
  | 28 => 0x144e
  | 29 => 0x14c9
  | 30 => 0x14cc
  | 31 => 0x14cd
  | 32 => 0xcc9
  | 33 => 0xccd
  | 34 => 0xcce
  | 35 => 0x15c9
  | 36 => 0x15cd
  | 37 => 0x15ce
  | 38 => 0xb0211
  | 39 => 0xb0214
  | 40 => 0xb0215
  | 41 => 0xb0216
  | 42 => 0x140211
  | 43 => 0x154211
  | 44 => 0x140b11
  | 45 => 0xb1411
  | 46 => 0x140b16
  | 47 => 0x154b11
  | 48 => 0xb1551
  | 49 => 0x154b16
  | 50 => 0x14cb11
  | 51 => 0xb14d1
  | 52 => 0x14cb15
  | 53 => 0x155411
  | 54 => 0x141551
  | 55 => 0x155416
  | 56 => 0x155415
  | 57 => 0x14d551
  | 58 => 0x1554d1
  | 59 => 0x14d555
  | 60 => 0x144b51
  | 61 => 0xb5451
  | 62 => 0x144b56
  | 63 => 0x14cb51
  | 64 => 0xb54d1
  | 65 => 0x14cb55
  | 66 => 0x2cc
  | 67 => 0x15d451
  | 68 => 0x1455d1
  | 69 => 0x15ca
  | 70 => 0xcd4d1
  | 71 => 0x14ccd1
  | 72 => 0x14ccd5
  | 73 => 0x15d4d1
  | 74 => 0x14d5d1
  | 75 => 0x14d5d5
  | 76 => 0x15ccd1
  | 77 => 0xcd5d1
  | 78 => 0x15ccd6
  | 79 => 0x164c
  | 80 => 0x44c
  | 81 => 0x3ca
  | 82 => 0x9ce
  | 83 => 0x20b14
  | 84 => 0x24d
  | 85 => 0x3ce
  | 86 => 0xa4c
  | 87 => 0x198c
  | 88 => 0x2c9
  | 89 => 0xb1696
  | 90 => 0xb09d6
  | 91 => 0xb1396
  | 92 => 0xb1516
  | 93 => 0x2cd
  | 94 => 0x168e
  | 95 => 0x9cd
  | 96 => 0xa4d
  | 97 => 0x198d
  | 98 => 0x140955
  | 99 => 0x409
  | 100 => 0x1609
  | 101 => 0x141695
  | 102 => 0x9ca
  | 103 => 0x1409d5
  | 104 => 0x168a
  | 105 => 0x141995
  | 106 => 0x140a55
  | 107 => 0x140095
  | 108 => 0x141555
  | 109 => 0x168d
  | 110 => 0x155696
  | 111 => 0x1549d6
  | 112 => 0x154056
  | 113 => 0x154996
  | 114 => 0x155496
  | 115 => 0xb5496
  | 116 => 0x5cb
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 66
  | 7 => 868
  | 6 => 1563
  | 5 => 1113
  | 4 => 10
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
  | 8 => 2*((h/57+packedAt gbK8 (1716+(h % 57)*7) 7) % 66)
  | 7 => 2*((h/296+packedAt gbK7 (32116+(h % 296)*10) 10) % 868)
  | 6 => 2*((h/535+packedAt gbK6 (75024+(h % 535)*11) 11) % 1563)
  | 5 => 2*((h/476+packedAt gbK5 (65667+(h % 476)*11) 11) % 1113)
  | 4 => 2*((h/10+packedAt gbK4 (700+(h % 10)*4) 4) % 10)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffc0f01fff03ffffc1ffffffc0cf703c38f1ff
  | 1 => 0xfff001e07fc3e03fe0ff01fc7349fce274e73
  | 2 => 0xf07fffe007ffc003fff07fe03838e1f3c78f9c
  | 3 => 0x7ffffff8000003ffff80003fc0fe03f80fe0
  | 4 => 0x7ffffffffffffc000000003fff0003fff000
  | 5 => 0xff80000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x948010028800428880989489004130140810a5
  | 1 => 0x94b010c4364341152052056831406ca234652
  | 2 => 0x20156620058a802265204b409828c160c58b18
  | 3 => 0x8466bb57d020104bb9ce01832dc0fa03780de0
  | 4 => 0x878cd9966f339701004020437be0003b6e000
  | 5 => 0xce000e0180c2218021880c183efffdbc000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaece8faeae8a8feeaece8faeae8a8feeaece8faeae8a8feeaece8faeae8a8feeaece8faeae8a8feeaece8faeae8a8feeaece8faeae8a8feeaece8faeae8a8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_38867
namespace PEqualNP.Outside.L_meta_38867
open PEqualNP.Outside.L_meta_38867.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 15 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 68 := block_range (n:=68) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 68 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_192 : Interval s0Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_288 : Interval s0Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_384 : Interval s0Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_480 : Interval s0Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_576 : Interval s0Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_672 : Interval s0Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_768 : Interval s0Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_864 : Interval s0Atlas 4 864 30 := block_range (n:=30) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 894 := (concat (concat (concat bs0_4_0 bs0_4_96) (concat bs0_4_192 (concat bs0_4_288 bs0_4_384))) (concat (concat bs0_4_480 bs0_4_576) (concat bs0_4_672 (concat bs0_4_768 bs0_4_864))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_96 : Interval s0Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_192 : Interval s0Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_288 : Interval s0Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_384 : Interval s0Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_480 : Interval s0Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_576 : Interval s0Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_672 : Interval s0Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_768 : Interval s0Atlas 5 768 52 := block_range (n:=52) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 820 := (concat (concat (concat bs0_5_0 bs0_5_96) (concat bs0_5_192 bs0_5_288)) (concat (concat bs0_5_384 bs0_5_480) (concat bs0_5_576 (concat bs0_5_672 bs0_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 44 := bs0_6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_7_0 : Interval s0Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_7 : Interval s0Atlas 7 0 1 := bs0_7_0
theorem alls0 : ∀ k ≤ 7, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
  · exact alls0_7 i (by omega) hi
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
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 26 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 38 := block_range (n:=38) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 134 := (concat bs3_4_0 bs3_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 48 := bs3_5_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 10 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_96 : Interval s4Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 112 := (concat bs4_3_0 bs4_3_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_864 : Interval s4Atlas 4 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_960 : Interval s4Atlas 4 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1056 : Interval s4Atlas 4 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1152 : Interval s4Atlas 4 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1248 : Interval s4Atlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1344 : Interval s4Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1345 := (concat (concat (concat bs4_4_0 (concat bs4_4_96 bs4_4_192)) (concat (concat bs4_4_288 bs4_4_384) (concat bs4_4_480 bs4_4_576))) (concat (concat (concat bs4_4_672 bs4_4_768) (concat bs4_4_864 bs4_4_960)) (concat (concat bs4_4_1056 bs4_4_1152) (concat bs4_4_1248 bs4_4_1344))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_864 : Interval s4Atlas 5 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_960 : Interval s4Atlas 5 960 57 := block_range (n:=57) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1017 := (concat (concat (concat bs4_5_0 bs4_5_96) (concat bs4_5_192 (concat bs4_5_288 bs4_5_384))) (concat (concat bs4_5_480 (concat bs4_5_576 bs4_5_672)) (concat bs4_5_768 (concat bs4_5_864 bs4_5_960))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 48 := bs4_6_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 6 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 56 := block_range (n:=56) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 56 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_192 : Interval s5Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_288 : Interval s5Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_384 : Interval s5Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 781 := (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 bs5_4_288)) (concat (concat bs5_4_384 bs5_4_480) (concat bs5_4_576 (concat bs5_4_672 bs5_4_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_96 : Interval s5Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_192 : Interval s5Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_288 : Interval s5Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_384 : Interval s5Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_480 : Interval s5Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_576 : Interval s5Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 33 := block_range (n:=33) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 801 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 bs5_5_288)) (concat (concat bs5_5_384 bs5_5_480) (concat bs5_5_576 (concat bs5_5_672 bs5_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 44 := bs5_6_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 10 := bgb_4_0
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
theorem bgb_5_1056 : Interval gbAtlas 5 1056 57 := block_range (n:=57) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1113 := (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat bgb_5_288 (concat bgb_5_384 bgb_5_480))) (concat (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)) (concat bgb_5_864 (concat bgb_5_960 bgb_5_1056))))
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
theorem bgb_6_1536 : Interval gbAtlas 6 1536 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1563 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 bgb_6_672))) (concat (concat (concat bgb_6_768 bgb_6_864) (concat bgb_6_960 bgb_6_1056)) (concat (concat bgb_6_1152 bgb_6_1248) (concat bgb_6_1344 (concat bgb_6_1440 bgb_6_1536)))))
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
theorem bgb_7_864 : Interval gbAtlas 7 864 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 868 := (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 bgb_7_576) (concat bgb_7_672 (concat bgb_7_768 bgb_7_864))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 66 := block_range (n:=66) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 66 := bgb_8_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 34, 42),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaece8faeae8a8feeaece8faeae8a8feeaece8faeae8a8feeaece8faeae8a8feeaece8faeae8a8feeaece8faeae8a8feeaece8faeae8a8feeaece8faeae8a8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808936 * 2 ^ 32 + 4209698984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_38867.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,5]⟩,⟨.and,[1,4]⟩,⟨.or,[2,6]⟩,⟨.or,[1,4]⟩,⟨.or,[0,7]⟩,⟨.or,[6,10]⟩,⟨.and,[2,11]⟩,⟨.and,[3,8]⟩,⟨.or,[0,13]⟩,⟨.and,[9,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4209698984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4209698984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_38867

open PEqualNP.Outside.L_meta_38867 in
theorem PEqualNP.Outside.L_meta_38867 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4209698984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4209698984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
