import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40507.Model
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


end PEqualNP.Outside.L_meta_40507.Model

namespace PEqualNP.Outside.L_meta_40507
open PEqualNP.Outside.L_meta_40507.Model
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

def SBf (j : Nat) : Nat := [7, 7, 3, 7, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_40507

namespace PEqualNP.Outside.L_meta_40507
open PEqualNP.Outside.L_meta_40507.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x70011550c33470000c00400e84c1380282bf43fc43fd41de31bd42fd40fe41fd43fe30ff42fc41fc32fe32fe21bc40ff30bc41fc31fe43ff10fe20fd31fd30ff21fd42ff20ff43ff32bf42fd21be41ff31dc31fc30bd43fc42fd10fe10be40fe42fc40fc20fc10ff41fe31fc21ff40fe40fd32fd20
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x829303900a8d8800091405ad01018406010f83802a948180029901010382aa01808022838501910780060a800c068089a117802700062d0100000600800001000201408007ab2d028c0a15cf553309faa2219d434c33aa7a15794e109eaa0653c54482bca7a14f94640dd2808176518cb3e8718d7946319e28a855e531027aa998dd544209f28e853e54c867ca8994f94441d7a92855f53482baa7a0e78c440af288633e51d0ebaa7a14fd4d429f2a6633d544ca7ca821cf548419a28a873f54487688218d794f41bba8a419d420c67ca12067152319ea90819e410c67aa7205794f219faa021b75150f3a86194f54c419f2a4653e54ccae8a2905754e109e2a4633e54086eca2104f14143afa9a433c5150e78a9104fd5221ce18c813c548867ca8195bd49309ea96873d540873aa6204f55320cf29e85b45150e7ca2204f940419f2a061745150f3862206750c319eaa6433f544c6b8a6904f55031b7a92213c548c2baa6105714d109f286859c410c73e8418cfd49439ea94813c544c678a8984f95320b6292219f5350e7ea9104f95310ceaa0633c544867aa8186795031eb28863d4314867aa720e750a31bba8a873d54ccaf0a090e7d5231cfa18633d5490abca61075d04319eaa0413d54c427aa91967d0a319e2a2213f548c7a88218d714d41db288833d53d0abaa790cfd5230ea18c433d53103288218d754c40afa9a219e531033a8718cf94241ba28a619e319027aa9084f943439f2a4216c524c27ea8986750f309e2a0213f54483a862084f54a419f2a0639c418c6f6a090ddd45308ea9e853e540827aa921f50c6109f2a0853c5050b3a871957d4d418ea98819e418c6b8a690dd546329f28c833e54cc3688398cf94040
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x2338700000a2410501000001c901a0800001068010c00810121810404004c0a5987548c6946150d308758c54882546154c408758c540423565104318718553d0a2d6215231a5185420c6956510431a5185438ca966010431a5185430cb14540c62187997428c714540c521c550c514c297651043185185531031753145438758e540869661904318d18553102946154c4087185531021d65d08318758e54c821c6550d30c515031042946150f30a3588548c61d639424187d8d52902946154f42c518553102146154f42c550e518ca546154f42c5d85531021d6395310c5d8553d0a3461551328d987548c30d43149308e181544ca1f6354a41a5984548c69562104318758c5050b50311412187d963110316540c610c518553d0b1763145438758e544ca2d62150108d18553d0a1d6315221875943110316510c640
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xc0c80060a38ac72a043415c8540c410a0ce5b18a2a1c1576150310420b38ec6a9481051c56314142828e2b18a9105047150c524c20a38ac72a641215cb6510431
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | 2 => packedAt s0K2 (i*49) 49
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/23+packedAt s0K5 (800+(h % 23)*6) 6) % 50)
  | 4 => 2*((h/76+packedAt s0K4 (4455+(h % 76)*8) 8) % 165)
  | 3 => 2*((h/41+packedAt s0K3 (2280+(h % 41)*6) 6) % 60)
  | 2 => 2*((h/10+packedAt s0K2 (490+(h % 10)*4) 4) % 10)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0xf01ffffe03ffe07fe0ffe07fffc1ff01ce7e7c
  | 3 => 0xffe07ffffc0fffffff03ff81fffe0ffff38f8f
  | 4 => 0x7ffffff0007ffffc0001fffff001fc0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x1142108c48824810052ca8a25012915414b0b5
  | 2 => 0x24c52914392484a960556454b6412a0cca565c
  | 3 => 0x42894a209069144aaa0255112aa40ca9630b0a
  | 4 => 0xb1674492241d974d3981861cd39c031bc0de0
  | 5 => 0x8c187871c38e1e7f1ce39e780e3188c1ffe000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00fcc0ccc0fcc0cc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40507
namespace PEqualNP.Outside.L_meta_40507
open PEqualNP.Outside.L_meta_40507.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x604000100f74c1441c08c300c3c4780fd30fd40fe20fe43fd42fc30fd41bc40fd43fe21ff41dc31fc43fe31ff40fd21de31ff21ee21fc40ff43fd32fe32fd10fc20fd31fd20ff30fc42fc21ff32fe30fc10fe10fc41fc32fc31ec21be40fe42ff42ff20fe40fe41ff31ff10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x1b137018094057b93ad84aa040c1020084500541c00a0410f000c0ab8f0e0038b1978002222220b047008006140dbd4910ea188435f53486b8a690db94b41cf29881cd320cb5c43205ed4141ceaa0636d52d0fcca210ed94440aea9e4377514caf0a0a0cfd5110af298417551d0adea4a0db54a10dc20621d4310427ea898710c421f210821ad540873aa6206b08640b6a96837451483ac8218db14930e7188437551d0fc86210f30c421e718c435d531033c63205794e10ba28a615e531035ca810db94a10af29e439e31102dca4186b08440d710881b8400427ea8905754f429e2a2413d54cc2bca7a0dd944409f2a0636e51086dca310cf94040d729081e5410873ca818f30c6219e2a2619c3190278a8885bd4930af29e853d54c42d8a498d754c20b6a90617651d0edca5a1f9086109f2a6415f53506dca4204f95021ce188813d540c76aa2205714d41ba28a656e52cc7ce6210d794631d6a90813e54cc374a02057d4d10eaa08637551102bea6904f55021b6292213e54c42daa4204f94240bb28e853d54c82baa7085714d20b6a96635d53d07a863085dd4520bba8a61e641086d8a4a0d794431eb288635c53443a86390dbd4931
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xcc0008006a10119000c95495110385540c421951855308385640c421c554d5110315540c421b118d41086e06050421e10c421103843108640e19503108786640c42199185520c2d060504318759431103903110010d194c21842c6618c421a9590310862d6508440b1189410c746520c610b1185320cba02110010
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0xc0aca1884220485769503108682ba86210881415d6640c421
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => 2*((h/22+packedAt s1K5 (736+(h % 22)*6) 6) % 46)
  | 4 => 2*((h/53+packedAt s1K4 (3159+(h % 53)*7) 7) % 117)
  | 3 => 2*((h/15+packedAt s1K3 (912+(h % 15)*5) 5) % 24)
  | 2 => 2*((h/8+packedAt s1K2 (196+(h % 8)*2) 2) % 4)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffff01fffe07ffffffffffc07fe3ffe3f
  | 2 => 0x7f01fc07ffffffff83e07c0f80ffffffc933ff
  | 3 => 0x7ffe0007ffe07ffffc007ff000fff83ff1c3c7
  | 4 => 0x80000007ffff81ffffff800000ffffc1fe03f8
  | 5 => 0xfffffff8000001ffffffffffff000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x914284011c104200c628c508e2c425212561b
  | 2 => 0x224c518b224a28c581a8350d12558ca4c930ed
  | 3 => 0x4c289ad54487516ab4125b64249ad23971c346
  | 4 => 0x68b1636689141db35adb024848e36711be03b0
  | 5 => 0x70c183870e1861dc631c638e70038421eda800
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000faaaaaaaf0a0a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40507
namespace PEqualNP.Outside.L_meta_40507
open PEqualNP.Outside.L_meta_40507.Model
def s2K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s2K2 (i*4) 4
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 2 => 2*((h/1+packedAt s2K2 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x5fc7ff3c7ffe03fc
  | 1 => 0xffffffffffffffffffffffeff8e7ff8e0ffccf
  | 3 => 0xfffffffffffffffffffffff7ff07fff00fff0f
  | 5 => 0x7bfff83ffff00ff0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x2072404c1262615c
  | 1 => 0xffffffffffffffffffffff90960a1484a4a4c5
  | 3 => 0x920d42921494b0a
  | 5 => 0x60486b249818ea0
  | _ => 0
def s2Atlas : Atlas := ⟨2,rawDecor 43 s2Pos s2Neg, 0xeeaaeeaacc00cc00eeaaeeaacc00cc00eeaaeeaacc00cc00eeaaeeaacc00cc00eeaaeeaacc00cc00eeaaeeaacc00cc00eeaaeeaacc00cc00eeaaeeaacc00cc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40507
namespace PEqualNP.Outside.L_meta_40507
open PEqualNP.Outside.L_meta_40507.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x1050027420c100bac5241045049006054041fd10fc40fc41fe30ff42fd42fe41f421de32ff32fd43fe31ff40fd32dc32fc32fc30fe20ff41dd43fd41fd20fc10ff31ff20fe32fc43fc31fe40fd21fe21ff21ff30fc42fe10ff10fe42fc21fc20fd30fe43f721de43ff43fd40fd31
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1e911008121060c384040152b000000200100b108180327060012086c301017800002c018f0064184015e53d02bca620d714943baa8e85d432c86f0a0a1758cb21b7296839e540caeca3a16750f42aea9e815e53d06bca6215794e20ea190435f5350abaa710d754c10b6292636d52d06bca608710c821f3290435e520cadea4885794f42cea1a855d531073a87205755032af298815c534867ea88857552439faa2417651ccbce6410d7d4d21e6190435e5310eeca3105dd4520af294876c52442eca2184f15110af29c435f53442b8a6904f15120eb21e43d643087ac6410ddd4532bb288817451483c843105714d10aea9e85d543c86daa4205754f41ba28a655d53103cc8410dd94821f2a1043e432086b8a6a17550c21afaa4657551882baa7104f95032afa9a4176518873a86205bd49319f2a6613d540cabca5195d14542cfaa2876e52102eaa3995755232afaa0659d540caeea2a14755032baa8881ce520cb986510cf55330bda828575510c2baa6217908420
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x188042c80800000033854350821c650c5050ae0605082187596540cb86640c821a1590320868d640c821a95903208695640cb21b1d90320870d4354840b118d4208746530862099189510c2c46250c21b198a3208785640c821875925388295640c821b1590320868d640ca21
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x5057494c2188242bb4c819043a050c6050821
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/29+packedAt s3K5 (736+(h % 29)*6) 6) % 46)
  | 4 => 2*((h/47+packedAt s3K4 (2673+(h % 47)*7) 7) % 99)
  | 3 => 2*((h/14+packedAt s3K3 (798+(h % 14)*5) 5) % 21)
  | 2 => 2*((h/8+packedAt s3K2 (147+(h % 8)*2) 2) % 3)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xe07fffffe03fff81fffff07ffffe07fcf8fe3f
  | 1 => 0xff80fe07ffc0fffe0f81ff87c07ff83f6733c7
  | 2 => 0xffff0007fffffffff001fff8007fffff87c3ff
  | 4 => 0x7ffff03fffffe0000007fffc3f803f8
  | 5 => 0xfffffff8000003ffffffffffff800003fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x230a144023820880318a30094716426428561b
  | 1 => 0x452628ca448e519606a8d485892aca296332c5
  | 2 => 0x8a144d148914a22ad0416950124d149285c16e
  | 4 => 0x1c58b1e712283bcd6b6c0c452471e723f803b0
  | 5 => 0x1060c1861c30c3718c718e6638018403d6a800
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae0e08080eaeaeaeae0e08080eaeaeaeae0e08080eaeaeaeae0e08080eaeaeaeae0e08080eaeaeaeae0e08080eaeaeaeae0e08080eaeaeaeae0e08080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40507
namespace PEqualNP.Outside.L_meta_40507
open PEqualNP.Outside.L_meta_40507.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x2d80410000001802000801c9001000000240082ff42ff32ff31fe31ff41fe30fd30fc43fc41ff43fd40fe42fc30fc32fc31ff20fd21ff40fc42fe32fc10fd10fd42fe21fd20fe10fe41fc20fd31fd43ff10ff21fc40ff30fd41fc21fe20fe40fd32fe43
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x8817f54086f8a6a15f54b31fb98843f541442f8a898df54e41bea94613d540c7ee4290fed0320bfaa6437e50cc6faa4085b94840df2a0637d54882f8a4a1df94e41df210817c54cc6f8a9187b54b41bea9e81ee52d06faa418df94a31bea80637e53103daa421fb50b20bf2a085ef21086fca7105f94632be29021bd41107dc85907bcca32beaa2217d5310afca8205f54342fd184215e53102f8a8195f55332deaa063ee52102fca618df15010be29c43ec21882fca118df94c10ef29e837e501077ca9985f54e20be28285de5310afea2907b4c921fd982617f5448778a8885f15130aea98857f54cc2daa418df55231bea9c437e5390efca918dfd4530bfaa265bf4350afaa9205f94841dfa0481de310c3bc8618df15321fb88021ee21486fea690df94243bf28865de43cc2fca1997b10820bf29a217c514cb7a87a15f14f10bea9a437f540837e87a0dfd4d10bfa8285bc54482f8a890df14540bf2a6417e54083f280205f94040bf298837f51502fea710df55321bea94437d5090efaa6205f54f41df202817f54882faa7905f94d21ef98863ef32886b8a690df14a10dfa08837d51902faa921f7cca32be2a665fa40103ec82885f55010fc206415f53486f8a6105e54031eea1e617c505077aa8195f54610bf290877e52907da8410df54e10bfaa641f920083f220085f94b40bf29041fa500c6faa7a15f14d40bf28421de434cb7a8421778ca31bb28881bd43902faa5a0ef50c43ee98061ee42087e8a2997dd4532be2a0437d520c2faa2205f14132bea8465be540cafca418fb10a20dfa00817c51483d86410df14d10fb88421be41506fca2106fd5120ef990657f5350afaa6105f54021fb188637e53d06fca1195f14c21bf28c81f731c86f8a8105f55320bf298657f50487e86210df54041dfa1e857e50902fca3185f54b10bfa9283ee32082f8a4887e8c030bf294815d53102fca5985f14d20be2a421fb40083b86518df94c43bfa9261bd40102fca890d7d4d10bea8c617e52c4278a890770c430bea9421df53442fca3905f54e40b6292217f53843ea8220df94321beaa6637d5090afea0a1f78c531bea9a417f548c6f8a8907b50842bf280217d50cc7f420086f90942bfa9e417e52d0efca6907b14931bea88876e520c67aa8195fd5230beaa0657f5150f7a86205f94e40bf292217e53c42fca218df94b31efa9a43ee4210afaa021f78c6309f2a0637e51886f8a498df14542bf2a06374514cbdca421df94c20df21a877c53042fea6a0fb88420bf28e8577514ca7ea8905f54642bf28c857e53d0afea4a1df55132bfa98437d508c77e8320df54840bfaa241ee32882faa518df54720bf288617c5150efaa1a1df14d21f7296617e50907eca2205f95221eea18875e53d06faa818fe4c110bea9e43ee32c877aa9985f54e30
  | 1 => 0xd54086fca1a15f95043be282637c540c6f8a4986fd0842be29e43df300c2f8a5887e10020dfa1c817e520c2fca610fdcc531f6900417e5090afca8194f95032fb108437c54c42f8a990778c831bea8643ed428cafca9185fd4f21bf28e817d52906fca8995b14931fba0a837e50883d8a4885fd4a10be28a616d52102faa8105fd5032bfa9841bf4310fec8220dd54440beaa2437e5290afea9195f94443bfa9c417d51d027ca9985bd4940bf28c83ee428cbe86390f754c40ef182617d54906faa1995fd4c109eaa6617e54cc3bc8621df55210fc282857e538437883207b8c832fd984617f540c2faa2215f54910f690843ef42082fca621770c831fc984217a500c7dc40907b4ca20dfa1c87bc42903f641105f94230be2a265ee21883b8a6885f54341b7a92217f54442fca4195f95021f790c437e52843da6590fec4110bf296837d52106dca5987ed4142bfaa0217c540c27ea8885fd4d20f7a9281dd43ccafaa9985f54743dea1a83ee424cafea910fb4c832beaa2417e54ccadca5a0df94020ef29881f641c42fca2087750e31beaa2637f504c6fca318df94821fa880217e54107ba6218efd0c40f7214437f53c42fca7217d54440bfaa2617d52d0efea5885f54032bfa8a85ed424cafea998df55030bea9843ed42887dc84905f94031bea9821dc53487de85105f94221dfa1485ec328877ea8885f55310fba0c83dd5310afca998df94341be29c21de324cbdaa418fb50920ee18c61ed52cc2fca7905f54b40f7a9263ed52103be86a1dfd4d40bea8865bc41102faa9217d48421bfa92637d51d0afaa2185f95321de210817e50087dea4887790f32fa988637f54c42fca220fd84110bea9661fb10842bca6215f95120f799043f9500c7de40105f95210bea8c417d5190efca4215fd5131be28287dd434c2f8a4a07dc8621bf28e657e5110afca710f790e31bf2a4417c50486fca9195f94a32bf28065dd320cbbaa7a0fbd0942beaa4437d51ccaf8a910db54843bfa90217e5010efca3986f90640bc282857e53d03ba86997bd0a42bea94877d53c42faa5206f50f41bea8841be42902faa8985f55232bf2a621df4390ff260185f94840bf28687ee520c7dc6490ef50d42bea80857d518cafaa120fed0140ef98c637d51cc2fea9997bcc932bf294877f514cafca898fe8c110fd902417d538cafaa6885f55230bea90876f524c6baa7a0df14941bf298616d52cc2fca4085f94421bf2a0217e53c86fca5185f95110b6292817d538c6f8a7907ed0240f7904417e5190fba8618df95030fd100417c53882fca2205f54a20be29a836d52d07bc86985f54e42bf28c417c54cc278a8887b14940bfa82837d53106fca0185f15232be2a4637c54442fca0215f94743ef984617f504caf6a0a15b94843dfa1a83f7318c7d842105f54221df20
  | 2 => 0x40053fd1402801014030100200c24000020000b0c83100c00380000942e05c013b400098000e455004040b4140000100c02210000fc00018010000301c000000e0882b0000401c000040500000434031e0082fc66010020011d0005001807034983f4020001a000040d827000e0008030180e08c30088010280600c6e0300209803321490180004cf80180200c0a3f44306c0401c0101c0903803150090000c000010000002c950a00706c061e41d000020c82a000072102a000280044c008000140606008038022f01902400004271340201400000000243f0140800401014050580601036028000082c01a4400c030241b4d41c01c0001c4e1100e0281900408009990009500001598120103306c0002c01000180740a020040c81101006000010400101c040a0000000dfaa0e217f52503da64105fd5210bfa92217c54882b8a6885f95130bfaa0637
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x8540c32d548c832c7553320cb565394440cb50d521027960150219d584548825f63551218fd91534423f6550441d350d5210e6d6590821dad085050a6d6295231cb50d5210e5d63150218fd91508c66d65cc821d9908514cb2c5450920d390d5210f1e63151209bd89544425e6395121d9cc8514ca3e64150329bd954210b686054840ae580411026e62d5330b5185320cab860508428f990530871e5350f41d354e521033943141429bd89508c65e6315220cb55252cc34e53948409b988548423e64150319bd95320ca7965840109b98a524426d62153319b98a548c6e86050b209798e544426e6215331b918532486776154d21ab590320866d62951219d185544cb596014d109718d519027a6014c219b99642482e96008420cd546411027561d4e209b98853086766115010ce153204825f654c431d594d51103555354440ba58840c832e54948318f59253442756114c209b594320866f6254d219798c540ca5e63152109ed95300c23f6454021d390d52cc26d6215010cb54a421031d6414d219e980530426e65149108f19152442d56190c319b189534432d6215120da549500c66d629531097d95300c26e62150209b189508c74c538c9219b98b538423e6414f109b988540c66f6254430d690d500c67a601502197d8d5190b6652944409d195414435943540318f99053c86e4614c832d390d520c65d63d4a109718d544432e5494b30ea108400826c6254041b9185320832c5490920da94a500c74e53548408fd91508ca3d6494e20d9549511027765504419bd895190f6852d01409d98454882e860508429b588540c72d54548319798c544834c528c5318f990538863c64542329b98a534433a54940318f99254442e4614cb219e58354ccae5620c7219b988540cb6552944408f59053c869d63108408f59053886cd6310820c795143cc34d4354b309ed81544ca3e64148108fd95401027661150308f992538834d6214d219b58b53842e860508219b596320823c6454d209798e534429d640ca31d354d52102e4614ca208f59053c825e63150218f590534863f65508429b98a54c427860551219d986544ca5c6354910cdd0d51102ac6250040c794d431026f62551309b988540c25e6315320ae19120083c6320c7219b98854cc32d4354b419758e544866c6254643d9949511023e64d4b108f590530427761551329b195324863f64549109b18950d0f4c53149109798c54c866e62951109758c54843563214532d314f52442ac64480208f590530826f6255131b3189310c63e6515110c754f4210a7a60d50319d584548c32c5414910cb153524423d6414f109b189544c72e5450a21d354a320c66d62d53309d185544c3aa421032097195434ca7661152308fd91534831d544c8329dd95310c65e6394910b358c428825e63d4a10
  | 1 => 0x71001c0e110a820662e1f880241230860000e038040e1341010126005854000a118404e340000400184cacc041d0e29c0200040088002090701003638006e3a06c3c04f6298886a4d0183c0000110800217cbd53524425d63152209ed81544c66c6550920cbd50524427a60d5332c7951430c63d6494d209798c540431d6315120979945348758538c110cbd0d52d066c62551109b588535066d6214c10da54a500c755510c4309e181544cb8d4350932cb951520c66f62551209758c54c8675650c4219b58a544434f53149109e580538865e6514d109ed815448734549051097d95320cb2d5454b309d584540827960d5221ae583431026c62544309b58a539034e5394b418f592538426e62d53109b99632486cc6348421ce551500c66e6214f108f990530426f6548421d354e4210a5f63546408f596540ca746154d208f59352c426c65509329b58b540c6e860509329b189519027965100208f99053c826e6294e40cd584544423e6515120c799053486d9600c630c798e54cc34f53d491097596430c63c64540219d984530831c5414d108f992524431d5350842cd50d511026d6510820ce552500c65d6395110ba189401032c54881209d987538823e6414c209b988530426f62543438f592524426d65d08208f191508c67960150319758c540832e5454b308f992534426f65480209dd95210871e63950319b98853506e4624c4319e583540c65c63551219758e54886e86050a219758c520423c6454d1097d954310e5e6394d21cb551320ca3d6494c30c7d50534425d63953108f992538434d53508429e983548866e6294e109e58053086756195132cbd0d521026f62540419b988548c25e63953109798c540823e6414d218f992544825e63952219758c54c825c6550d30b518d210874e5354b41d354e52d076542145328fd954310e7860551319b98a544c66d6215230d554e511025c63546429758c54482e860509209ed815448278654c110d514f214867b65480209758c540426d62d53109758e524426d6294d209b58854cc32f43548439b58a538426e6215010c7d53534423d659503197d8d510827a6014e219b58a534423d6414c21f10c831086ad640ca21ba181428cb6a52540319758e544c71c54d4d108f992530c26d62951319798c540c33a54540319d98454082776154d209b98b540c74d4354831ce9085050a3e6494d209e980540c73b43141429798c520425f63551109b189544c27761551309718d510832d54948319d584540c29d6310a40d354d52d067b65440109b588544c26f62546409ed95401036452cc5319b58853c435543145329b5885484277654401097d8d524434e534ca208f59052043646154831d590c514ca9d640c8319b988544c3655108420cb14a405034c534c921d314e214866f6254d109b58
  | 2 => 0x3d0001076106c0040274169001a1d000040200088081d010c001804f04874607304a480a000007440070001c240c0895c041a578044a1b02138000e07878156a1780012030c8e4088
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xc021820188013a878a1506050920ac0e0a10a2994a8745802108286ba4a6994419114c614c921c1ac6b10a890544735442108306b22c429a43615d0320c421950e4b00822061554185320cb24a98c0a10858654c6050842d1286302849950d7414d32486c4b98842004189550614c832988e4b0c8618ca8725834310286b98a8a1241c150d4214532c8ca630a651062a541814288686b9ca8a1443511c9510c430
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x41a09831506050920a09839506050a21a058494c614ca20d01431c14214532a058414c614c921
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 616
  | 4 => 414
  | 3 => 25
  | 2 => 5
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
  | 6 => 2*((h/27+packedAt s4K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/240+packedAt s4K5 (16632+(h % 240)*10) 10) % 616)
  | 4 => 2*((h/138+packedAt s4K4 (15732+(h % 138)*9) 9) % 414)
  | 3 => 2*((h/15+packedAt s4K3 (1225+(h % 15)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s4K2 (300+(h % 8)*3) 3) % 5)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffc07ff0fc1ff0ff87ffff0fe03a63f3e7
  | 1 => 0xf01f87ff83ffffe0ff0ff8701ff0fffd9ccc7f
  | 2 => 0xffe007fffc00ffff000fff801fff003e1f0f87
  | 3 => 0x7ffffff07fffff000001fffffc7e00ff8
  | 5 => 0xfffff800000007ffffffffffe0000007fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x614500470821100330118091cb0122882151e3
  | 1 => 0x24c20889194040a051068822451049908cc42d
  | 2 => 0xc28b551230eaa56d088b550496aa0526170e86
  | 3 => 0x8b14662442883656aaa0440918cc9607600b50
  | 5 => 0xc184438630cc798cccc664e00881807daa000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaec80ec80eeeaeeeaec80ec80eeeaeeeaec80ec80eeeaeeeaec80ec80eeeaeeeaec80ec80eeeaeeeaec80ec80eeeaeeeaec80ec80eeeaeeeaec80ec80, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40507
namespace PEqualNP.Outside.L_meta_40507
open PEqualNP.Outside.L_meta_40507.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x11020000008800000c2041100444327085001241fc30fe21bc42fe30fc42fd30fd40fe42ff10fe41ff42fc32fb20fd32ff21ff43fe31fc10ff30be42fe32f820ff31fd10fc41fd31fd42ff41fc31ff40fe10fd20fd41fc21fe40ff20ff32fd21fc43fd43fc40fe43fe20fc20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x865fa40082faa9995b948319eaa4417b5050af8a090df55321bf2a621be5310afaa7907d90441bfa9c217c5350bf041086f10e42dfa0883fb40c82faa8997e94c20de216637f54c86faa6086fd0d41df2a443bd4210afea4a07bd0942f5290417e54ccbdea4a05d14532df210617d518c2f8a990ef10b10bf2a463f854082fca021fe0c720bf2a443be42d06faa9885f55221bea9461bc420c6faa8885f14943bca8443bd54886fca9087d4c431ef98061f942c837aa3216f90a32be29c437e50cc6fca1206f95030dc216417e520cafaa2205f54021bf2a6417d5110efca690df94332df214837f54842f4a018df14a10fca04215f534877a87216f10a31bfa9421bc42042fca5217ecc720be28a85f843083f487907dcc531bf28687fb20c42fea8185f94a30be29e4378504cb788510dfd4d42fc29841bc42882f8a098df94220fca98417f524c6f2a020fe90230fc982217e528cb78a1216f90b32be2a043be42103f043906f10821fc98041fb20042fca8106f94242be2a261fb30c82f8a4087e8c720bf29687bf5190bea20085f94243fd184217f504c6f8a610fec8220bea9e83de320c77e87a05f54d21f6908437d51903f443905fd4532bfa82657d5010bf4a1996f94642fc18041fb21c835084105f54730fca02617d51843788420fed0420bea90637f53086faa421d714d21be28283ef4290afaa121df95331f710a437d54c82faa6216f94842bc28243be54882faa898df94232bf280437c5050efea6907b4c832fd208417c53882fca8985f94321de2a265f943082faa420df94430bea9c637e510837aa8185f54a31be29a83bd5110afca5087ed5020bfa9a837e518c37885205fd4143bea90817f53c82faa521df15120ef194637d53d0a7ca4215fd4141bea84837d54082f4a021fe10720bf28c87bd4310ff0a2105fd5332dea0e81ee20483ba6218df55240be2a641bc42842fca518dfd5231fd28083bf5310bf485907ecc8209eaa443fa50d0af8a9995f94620f7a14417e5110af8a9085e94332bea8c877c5150ef8a9195f14f20de21265fb51c827ca818fe90320efa1c877e5410efaa720df95032fc10221f840082fea9985fd5032fda8841bd43d077c84106f90910bea9021dc320c67aa8187e8c030f621041bc428cbf4a7905f54f21beaa6637e500c2fea8987ec8210fc21041f610442fca421f78c531bf29c416f52503f6a0a17dd0641fda0481f7514cbb86518dfd5232fc21e417e544cafaa7215f54432fd284437c525077886216fd0641fc99641f940102faa510774c0309faa265be424c6fea910ef90832fd190417d54883ba8621fe14142beaa483ef328cbf4a8107e54332fca1e417e5110ff064107e94720de212617f53043da6490df95042be296217b504cafea9905f55021fca8087be40502faa3905f94831
  | 1 => 0xc53502fea61077cc431fca0461bd43502faa8195f15310bfa8a617e52106fca990df54321bea9661bf544827ca9106f10931bea8e87f4310867aa9995fd4e20f699643f953c837aa0214f94a42dfa1e837c524c37ca818fe8cb20bf29c857e53d0bf4a4105f95031bf28843bc42443f2a020ef10820dfa1c8777514cafaa01977d0d43bf29883bc420cafaa520fdc8621bf28c437b504877e83a05f14530bd29041ee32486f4a1a16f14642ef98c63bf40902f2a021ef55220bea8685fb204437ea890df95110bf28443df328cb7c84a16f50040bf2a043f4514caf2a018de94221de212817d5190bbc60986f90b10bf28041ed20083f065905f15131df21663ef420837c87215f94b31bf29a417e50906faa3a05f54242beaa461ee4210bf2a9905f55231bf28c837d508cbf480985f94642bfa82857e539077c8418df94440be28a41df320cafaa3195f94842bf2a061be415077ea0215f94632bf29e81be42887ee21086f90810fc98421f931c83f680106f90a31beaa4657e50103f6a7907e54420dd21641bf4310af8a6087e14132f790041f854c82fca3a05f95121bea9a21bf4210afca820ef94e42bfaa2217a50107f040085f14142fca1041f853c82f8a9187e50320fd88221fb40503aa6218ef90b21bf2a2633c544837885185f94e40fcaa041ed4210afca0086f94042bfaa2657d5010778a890fe90c20df21043fb310837ea8997e08310efa9a437e52442fca7a0ef54242fc188417d524437884907ed0f20bf290217d54842faa3107d8c431bf28683bc42507f6a0997ed5320de298857f54486f2a1996f90a40bf296617e53082fca3987e44010bea96817d50d07f461905f14d20dc21041be5110b7280205f94a40fd18841fb30083f6a6106f90841bea96837f544c6faa710fe884209eaa0637e51c82f2a1a15f94a41de212437d520c2faa110df55030bf29e43bd43d02f8a6105f55121fd90241be42882fea690db14940fd20081f941c83f642105f54c41bfaa0417f524c2fca018df94e43fc108417c53c43f260185fd4d40bea98417e54043d684107ed4121fc28e417d538c2f8a0995fd4941bfa8a85fb42c83dc6590ef54c42bf28685be54043f2a3906b10820fc90e41de4310ef8a9105f54b43bfa9a217e548837885a06f90d43fd210417e52d037c85085fd5120bf29c21bf43503de64996f90930deaa021fa40442f8a498df54732bf28485fb308c2faa6905f55330be28a817e508c3f2a018fe10420bfa9c43be424cb788590ef10b30bf28c81bc42c82fca610df15221bfa9621fa20083daa418df15020bf2a661fa5010ef0a0a17e54342dfa00817d54042faa7a07b14940bf28883bc54482fca6087e4c820be2a265bd41502faa598df95120df218857d5490efaa7085f54331be2a6617c54486fca4207b10a20bf29
  | 2 => 0x2008060e8100b00000302010b6010081a800020002d01e04800030183481e000caa90001e02c0000e12812000ac7b8312d00a07072018000000e1980a1f80829804058021a852058ae180001c8040e80e0501e2c002050100f80c018000000201058710000c000011f6090200001001878001381281a0d80098808113b32980e0c0100283a37122388aa0704c080000f06a148c2078004e8080489001856298000000056800118be0005201002001c82f13e080880685241008018042900004020000002a04e0a028218000080e0a0221280017a84078c0052822301601000310000599e20806000001284a048201890e248003282e000a0890000000a0580200d862901006056038700c06a0e02e010aa000602d0721c0120003e0e0c40a0360a12e0203e2780400000200080001c060101f1861e0001a80e090025402a0e006070417a508837c84a07bc8220bfaa0637e51d0e7ca8187dd0541bea9443bd41107f261905fd5230df21661be54ccb78a0215f94b41beaa2417c53843ee4290fe84010be2a021de324cb7aa818fec4210f421041bc42ccb7885a0fdcc421bf28e85df308c37e87215f54e20bfa9e21bc420c27ca8087e14121be2a6637e510cafaa818df15031fa908433f54487f262106f54e42be2a463f5411077c85185fd4810be2a221ee520c6faa3a17bc8621fd20e41fa51082f8a8197e50110dfa9c85bd4310afea8085fd4f21de29c857d5110b7c84a0df94042de210813e548867ea8905f94c43de214837f54c42faa018fe0c320bfa9221fb32c82fea090ef90920be29281f940082fca7885f94b10fda0e417e52082faa021df54a10ee29a43be424877e8621fbc8421f7190657e50106f8a2996fd4442bea88417d538cb7a86a0cf55010dfa1485ba42083f686105f94d10bf29487bf5090afca118df94210fd28063bc5110afaa5205f54430d7290857f51503f282105f95040fd182217e520c2faa720774c832b6a9063fa300835885105f94032bf2a4657d53103f2a110dfd4543be292217d50d0efea810dfd5220bfa92877d50ccafaa610df94732deaa6657e53103ee20085f54231fb98c637d5490afca9185f15030bea96217d544c27ca9997e48020fd982617c53486fea2905f94e21bf298857e530c678a8997d0c721bf298617d53c43f081905f94431fc216417e51042f8a6887e95320df216417e52087f242107e90210fb98e433c54486fca318ef90b40dfa0a817e53c83f684105fd5331fb108437
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x15210eea62150209ed9540102ba60d0842ae181435027860551329e59431c827a60d5031ae19132083a842080109d98454082786550110ce153204823f6454d21ce90a508873854502308fd9152442786054a41c7150534867a6095132b958831c87a84214420ab9885310a3e6415010ce151408432d5210b10b658c51082ea620c7209e58054887aa62108208f59253c865d63d4a10d614c50487a8424c020ce10b504872e5210b418f19152042b8644cb209e195404c27a60145439ed81534833a4214142ea10a40083aa6210b20ea948420836a52c83108f19152c433a4294332ea90c42082eb624c4209e18152106796095121ae181415026d6510820ae9825390a3f6454d10ad986425073a5494221c714e424867960952328fd91520c33b5495320ea109320827a6015032ea10a200823e64d49319b98b540c6776154d20ba988310832e5290a409e189501063d6414c10ea50c420823d6595031ea184420835853d41219e980540c2b96014c42b5584320c63f65500409dd85544ca5d63951219e5805350755530c421c7d4c42487a8428c4208f19153483395494031ea508420827a60150109e181534869e6314442ba189401025f654c8329b98853c43a842084209e58253482b96094e428f59642042e86250230dcd4651c823c6454a30ce90b504cb3454d4532cb94842cc3686094831ea94c42083a84210420cb952520c7a96010820ae59220082ea6214f208f594420c35a534c320ead8c42082ae62d4c42cbd48424423d64d4931ce10a500c71c53109218f990504c69e6314042dad80525027a60153329d984530823c6255030aed95401023f6590830cbd92520c67b6054b419758c54086796510f208f992508ca7b6054b43ea10940083a853108209d584530827a65107209e1815290eeb6250020cb94a420c6e96290c20ce10a508876b60948319e98054cc67a6510c20ea980420832d5410a20dc147504ca9d6314042f1949310c6eb6250c208f98a540c33954440109e18052442e9620c420ce10a50cca786054b318f191520c67661951328f596420c33b5414132b698c54082d463484218f990530865e63d4a109b58853c423d6414f108f99254486ea6214c20ce909508874c538c9219ed8152042ac62500408f994544ca3e64148109e994310827960946429e58353886e9620c720ea594420837351141328f59253c82786054b41cb948421027b60551329e98354cca3e64d4a109dd9521086ba6494f20b658c540832e5454831cb54a420c63e64150309dd85534873954543328f590514c3384214132ce95140c832c64548318fd954210a3e6415031ce151400825c63551109758c548433b41540419bd89544433a4214132ced0d5010e3f65108309e59420042b46150d41ea10a21082aa6290820da94a500c72e5210b10
  | 1 => 0x82ea62d4f209e596100432d65108209e99720442b864484209b19532486b661140428f99253c87384254041e5109310c6ba640c420ea10b51082756115230ea10920083a842d04209ed95320826f65480209ed81528c7ab5310820ae19121c833842d41328f59352042ba640c7208f189540425e63150209e580540867a60952329bd89544c2796014e218f59352c43d1310c420ead8442082e860508428f99253c823c64548309ed815290e3f6550c438f189540c66f6548421aed9120082ba62108208f59053842b96010c428f993538827b6548420ced425090a3d6414e219e5835250f6a52540319e58253486786054831ae590510825d63150209dd9510042b96094642bcd8532c833954150209e580544c7384254332ce15050487a84290420ce94a42082ba6488420ea994420827960145438f99353886f3614c8208f191524426e62150319e59742082786055121ae1814210aba6010c42cb552520c7a842504209e98253c86ba6488720cd10b514ca5f654c030f44c431c826f6550842ce10a501066d62d5310cd5445110a3f6454a309e1895010edb6348420ae590300823d64944219d58454083a84208310ae59030c833a42141219b58b54cc3a86250040e5909310c66e62d53309718d544866f62551318f592508ca796095132cd908514ca7960d5031d58c8514cb3854d4132cb54842d03395454221f44c6500c739544c0309e181544c6b9640c720ce55210043a842544209e982544877051141328f99053082b9640c420ea108204423d6494c32f18c831c863d6414c208f99053c433642d4532b6d8d21c836a5208010ae9834290a75650c4218f59250083a8420c020ae59253c82796095120ea984420831c54d4d218f596540423c6454d109798e544869d63144428f19152cc6e960d0820ce90b504872e5210b409e19530442796588420ea109210823e64d4b10d9185520c7aa52908209e58253c875b53141218fd9152042d7654c4319ed95200823d6494720ae98a420836952540319ed95300c23f6454b30ea108310836960d49409bd95320ca7561d4e208fd91528432c52109309d185544ca3e6494c329ed8152cc6da63144208f994544867a6294041ce94842082e965d08208f594420432f5210930ba99042082ba64947209e58354cca7a60d5221ea10b31082b864480209e98054887a842d0020ae9805110aeb65108208f594420c6b56114c429e98353886e862502109b988530433a42940319e98254c863e6494020c7d4e424873a54940319bd89534423d64d4c108f98a540427a6094632b618d210826d6214c109ed81544c7a953108209b189544427b6055120ae9825190a796510c20d6d4f50486ea62d5020ce10850486a86250040ce151404433954100209e59441c8395544c431b618d21c827661150329ed8
  | 2 => 0x5394f20ced50504873a5454031cbd48425034d6214d21ea10b320827661152309b189544c23d6590831ea19442082786054843ce95320882ae62d4e42ae99030c827a60d49318f98a540c6e8624c420ce552300c2e862504208f18854482ea62d4c20da54a500c7aa5410820cb54842cc2d4624c431e5951310c73a42540319d185544c3d13154031ab9825210a786054a319e9825190a5e6314810ba98a42082b960d0a42bc984540823e6494720ab9885390a7a60d4810d614d304423e6494632ea108320823d6414e20ce90b5050a79658c0209e59440083ab6250040ba58a410833b5410320ba189404c36852d01408f990538871d5310c42da597420825f6550c438f994424ca786054b438f99642482b862500409e9825390b3a54080108f590504c65e6394d21ce94940102b964900409e580540c73b54d41218f99254482b96014442ea109310823e64d4930aed9132c827a60d4943ced53504ca7a6014c21ce150504ca3d64d4e20cdd465190b2f62552209e594410833a54c8010ba59442082ba6090940ea10820842b56114042bc584530827a6510f20ea584420832c5290941ea990420832c5210910ea10c420827661d4e209e98053507395350040bc987204426e62d5310ba98b54c823f6454d20ae990300823f6454b108f992544ca3f65504419ed95420833954540318f994424867b6054d219e980548c6b96010840cb98a5210aae62908209d18553483384254031ce909501063e6414530da181520c73b6550040aed91320827960d5221cb192520c63e64d48109e5825390a6d62d5031d5d4c31c865d6314810dcd47504cb3454145328f993530431f5414d21ad9845310bab6510820ce55250ccb395150040ce552508871f54d4d21ad584421073442145328f191534872f64548318f592518ca6d6215031ce15350486f161080109e580548c66e6214c21cb10a5008277654c4318fd91520c6b96010e42dc54451082f26114c209e189500c63e6494d21ea10840082b960d0842d654c53083a8428c020cb14a425023e6414e108f59352842ba6010e429e58254c867b60548319ed95100426c6254d10d5d95310c6ac64480209e58054cca776550441da948208432c5290140ab594428827b6055121dad81520c67a62940438f99250c87a95410820bad89410827b6054a41ea10a320832e52108418fd94420c67761551309e58053086ba6414420ce90a50107a842c84208f191528c63d64d49109e980544c6bb60508428f990534433a54943329e98053886d4614c832ce50d5010f2c52109318f996424873a4254332ead0c420832d4314940c794d4390b2c54881209ed815210679650c020ba99252083a84294420b918532c867a6015031ced53204832d6510a20d354a320c63d6414d10ba98854c823e65909329bd89544
  | 3 => 0x8a4a80004f0900c02c010081b4845504c00004be004030d808004090881e004010ecf0028020c82e0096e0280f03c5b02001020000140202c000c0bd00c050080aab0180041039d01004430840b0e80100402004a20f808084000d800014300b40c0f40620c0402c0006c1a00421000012bc21018130a4000140404c170000a17d79048060007a0a8000001e045300340419c45021670f40204c020540000009000030040b004021001101802020000300000c0727c1010003038e0004000340000421000002940203d6d00006114050000f010002c0230980505c0a07e730002100003048010501d0180101013004002bc00000140041d05002090141c81200401000007480208c002240303d294ac6203800000313bc1d00001080080c41c1965503c100542403c000ec0036c15004080c00300801001057bc0b0b0e2014cc04c5401c02000011dc040900500c21000121f01e9e983525063e621512097d8d544432f43149409e596400823e64d49108f59250c876b42141428f994424833a54542219e58352507a842cc020c754c5310b3854501308fd9152cc6f16115020ae990530827a650c720cbd48424c65f6354910ce95150ccb1f5394e428f59052042b96488420ae59332082e86250c20b558e310c67960153318f992534827b6054910ea98c4208279650c4209e98a500c63d6494d21cb14b415036852c8110cb994420832e5210831f1549310c65f654c431ba98a410823e65151208f99251086e86250110ce50550106b96414c20ce5405010a7a6015021cdd53514cb6a6294820ea18c42082756115032ce550200423d6414c219d586544cabb64487208f99053882ba6014c42ae59332c82f0614c8209e597320823f6510810cdd50514caf0614c1109e583524c63f6590831c714d43506ea6290c20ce553200423f6454a31ae59221c823c6454b308f191528426c6255131cb548420c6f0614cb20ae99332c827a6094d218f596540c25f6355121d654c30082ba6488020ae993320832f64149408f593524c3a963108209e582518ca5e6514d218fd96420427960150329718d524435453c85219e98053042e96290020cb149415025e6315021ae59251c82bb6448420ce553208823e6414c109e994410823d6494d20cb551520c7384254221cb94a429065e63152108f593538875b
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x12d00141010020000020428000040330008000980040010004000a0c0000000000232948006080000e00180000218000004000000300160420100000000414000000018000000007209400021c08007685c45310820d16c62124210651535845308254392c8188414a1c15210831c50c4a8a802062854189404c295396a92a6418554d6114c42a50e02908488531711514008318aa2c22a0418a5946510820c50a530484a05a27119442082d0b88c6210414a5d46110820c56ca31280206316454451083153288420841865516315020c32c8a9860106285418940443423108498863689c46310820950e8b10621062a6510831082d1388a621041625cc6110820c50c8302a418d29751084008318b0aa0280858658d5014042c32c8a98a61062862109500c698b8884a80838a594420c420e4084a88a210688631092108254bb0a621041629cc6510820956ec2106210615635445110b18a8ac0288858a1486050540a50e0a18a4a06a1611844208294392a810021629cc6110820c50c52928020628541894084314a98c4a00812a9d85310820d408430a64104aa74d89310828cb98a8a0421455d4424c431b80e498862107095314c4208350216c2990418c5516108010952ec210621062854189408c295ba884100218654d6010c42e82a498aa018d2a70d48424c728b2a62188418a1906094831b42e23288410689631085108382aa2a4988634a9d46310820858e4b20a098d89731944208344b18c6210414a5d46310820a62e22a281185197315140083c021262188419458d5114420c56ea3128020619535805310a34392c02a263a298c4214420
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x6901000100020033200c21755846110820e0165109310c420a20825516108010c81635c46310820a21811506250230d01535c45310820c21655c46510820c097558c6310820e01631095114420c0575188424c431a8186109310c420c097654c5310820c81735846110820c09655cc6510820a09831506250210
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 779
  | 4 => 754
  | 3 => 85
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
  | 7 => 2*((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/28+packedAt s5K6 (704+(h % 28)*6) 6) % 44)
  | 5 => 2*((h/259+packedAt s5K5 (21033+(h % 259)*10) 10) % 779)
  | 4 => 2*((h/272+packedAt s5K4 (28652+(h % 272)*10) 10) % 754)
  | 3 => 2*((h/91+packedAt s5K3 (4165+(h % 91)*7) 7) % 85)
  | 2 => 2*((h/19+packedAt s5K2 (900+(h % 19)*4) 4) % 15)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf81fff01fff07f83f0f83f0ffc7fc07c6473e7
  | 1 => 0xffe03ffe07fffffc00fffff07f87fff87f8c7f
  | 2 => 0xfffffffff8007fffff003ffffff8007f87ff87
  | 3 => 0x3fffffff81ffffffc0007fffff87f80ff8
  | 4 => 0xffffc000000001ffffffffff80000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8ac2b11c512c9580b83e0b8cac4e454c6431e3
  | 1 => 0x1049922432442094004a5594148293502d842d
  | 2 => 0x21850448a0e1482d5100262159100a2182de86
  | 3 => 0x8516289104880d4a6a94800862652c06d00b50
  | 4 => 0xc61830e1c70e71f38ce738ce004630477f6000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfce0ec80fce0ec80fce0ec80fce0ec80fce0ec80fce0ec80fce0ec80fce0ec80fce0ec80fce0ec80fce0ec80fce0ec80fce0ec80fce0ec80fce0ec80fce0ec80, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40507
namespace PEqualNP.Outside.L_meta_40507
open PEqualNP.Outside.L_meta_40507.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1f0001c01d337a0c408a04808340306b94005c04700ff84001fd20007f48405fc3102ffd4009fe42007f8c80bff5202ff54c03fc40007fc8009ff41026f1080bfd5200ff90005fe2102ff54003fe30006f90807fe4302ff14809fc4202ffd4409ff42027fd0c01fd32027f55007fc4301ff0c801fd31027f50803fc30017fc4009ff4001ffcc809fe5401ffcc00bfd51027f50c01fd30017f90405fc41027f50405fe31017f14407ff3102ff94803fe50027f15003fc1001ff94c01ff21017f94409fd4002ffd4c01fd1000ff14005fc2101ff14c09ff5400ff88003fc20
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xa4021ff55132017fc829880bfd4148405ff18a6203ff10d32107f842990a7be5390803fe982401ebf5953105ffea89001aff6544011de2122002fb887210edfac89880bff4144003ff1064003bfd8d3211ff8411905ffd5248429ff202420bffd912013f7ca1210a7bf3090833fe31e4202fd085210aff8649080afc61c801fff98e4003ffcc132017f84290806fe6048407fea1c6403fdcc53101ff8609888ffe608c803ff9022001ff141101477e2121093fc518c805ffa8e4200ff58910077f8639007aff654c431ff206421dbfd9131107fca29900efe63c842dffb224216bfd9121087f8c990012fe64484037f304640fff98f2002578c899003ff618c801df2126200ffd8530115feca9901bfe5244007f61926401bfd811006ffacb9000ffc434c003f6102401eff99531047faa88809bff528c803ff1826006fd5451000ff4419000ffe434c82bff21a420dff54f20015fcc29907ffe504c805f710a4201ff8412001dfcc51900bfd514400ffe29a2001ff5013002df8ca9800af4614c84b7fb246402fd887210d7fa8590812fe648c831fe2064200ffc852005ffcc89000fff304c405fa18a6218ff1832112ffe851900efc63c8003ff9822003ff0c23201ffc631900afc614c805ff98a621bbf59721007fcc488043fe54c800fff29a201cff8813103ffcc688037ee52c8011ffa1a2006bf59510107fc829900afe62c8421fe2a64001ffd4120017fea29087bff524c403fe0826003bf18d2000dfcc09885bff4348417fe2124021ff5053214778432108bff654c841ff8826405bf9951006ffea790003be428c853de1948412ff509300cff8879082ffd6448055dea948411ff10530107fcc299043bc42c802bff31a4226bfd963200ff0a190053fc4048435fea064218ff08321017fa6288003f4614c831ff1864203ff0c932007fac79088bfd524c8013fb2a2003ffd0d320aff8869080fff534c425ff2126000efd8e4200fbc6098007fc2048055dfa8c8400bf5823202578c89005fff6548403ff2822003ff54e32107f8c299043ff41c8003ffa826001bf183210d7fa8790847fe514c01fff29e4005bf996320d7f88590837fe52c8017fea1a4019ffccb2109ff8a498037fd51c8037ff32e4201ff1432001ffe631900ffd534c419fe32a4000bf58d100effca898827fc5148003ffa026023ff8823200ff0409000efc63440077f31a4227ef982421577ecb21003bd6190805ff20a2002ff043210bdfeca9087ffe404c80b7f32e4013ffd953000ffaa09000bfd4144005fe20e4210ff5932000df8c119077bc424c42ffe32a4214ff8c12100ffe208809fbe3090805fe0824216ff509210d7fc859086bfe64c842dfea024200bfd8d1003ff8648800aff6248419ff32a400fff14f20007fc648804bff544c007ff29c641bffd9721
  | 1 => 0xffd65c842dde2124201ffcc130025f8c89909fbe2090807ff994640bffd0d200effe80988abbe65908097f3226401fb0832010ff8a899007fe10c804bfea146403fecc130025f8c990807ff50c80017e3126017ffd4d21127f8831905bfc544842fff32a4219ffcc3210effea89888ffc108c855deb2c8425ff90a32007fe439009bfc528c8117eb222001ff1012001db8c690807fe4048011ffa122003ffcc532017faa3908167c6548001ffb1e4203ff4c530127fcc3190a3bc3190801f71964201ff0c1100d7faa99087ffe204c80b7e32c6401bf983210cffca790843fc42c8001feb026401ff94130007fec19084bff644c043de3226409ff8852001ffc64980abbf5290801df2122002ffd0521087fa8790002ff6348013ff30a4000ff5812105f78c890012fc64440013fb2a4003ff8c932117fea499002fd60c84017eb1e4004bf191300cff8659085ffe52484357fb264202ff8c510127fca319007fc404c03ffe0826425ffd023209fbaa698016fc654c423ff20a6014ff1412106ff6a190002ff61480095f3148400ffd82320f7f8ca9880bfe104c4057e30a6012ff50530017fe628807bfd504c403fe1064000ff4872000ffa809001b7c6544045feb2a641dff15131017fa639082bfc434800b7f32a4203ff14d320aff8a69083bfc51c8055dea9c841effd4131017faa29085bfd5448401deb1c8403ff0c93010ffca899007fe3048005f610e4225ffd5232025f8c898802fd6244031ff2864213ff5493004ff8c290042fd64c80017fb126201ffd01200affe60908abbf5390803ff1022000efd864209ff8ca98057fe5348405fe18a2000bf586320a7fca090847fe214c001ff1964202ff8872101ffe649802ffe4248007ffa9a6401ff54320037fea488087ff414c807ff21a6000fb8c9210eff8849884aff644c023fe10a6002ff0c531057fe6490006ff6048017fea124021ef1093201fb8649900bfd41c8433ff31e4200ff98930017fe2190833fd6548001feb1e401fff141321577ca521002ff63c8413fe20a4023ff84232017fa6290807fc1048005fe28a6203bf98d10025f8c89000ffe304c845fea8a6400bf989100077c8590043ff42c8003f7106400aff98d2000ff86190023fe5444027ff32a6003ff50d3101ff8631900bfe414841bffb2e4002ff885210dffaa590823fc6444005f610a4202ff08721047fac88809fbc5090833ff21e4214ff98121007f8c498806ff604c01bffa964006ff54d10137fea11900ffe534c807ef29a6010ff99320117fca49904fff514c04b7eb246403ff4c9310d7fe8790807fe404c005ff882420cff1492001ffe8698097fc428c84dfea84640eff8c72004ffca29000fdf328c80dffa9a2000ff5853000dfac190003fd32c802dff322422aef54642047f8a888002ff604c401fe9
  | 2 => 0x1006ffccb90037fc65c80077e31a4208ffd9110017f8a28802ffc6448017feaa24000ff5893001ffe629800bfe5144027feb2a6002bf5872100ffc4098033fd514800b7f32a400bbf5912013f7c2121003ff624c439ff2026224ff08632057fca690087fc424c801df2164202ff8c7210bffaca90803fb2048039ff3026217ff54121097fac898007f610440057e30c6408ff99110007fac098803fd32c844bffb246401bf98b20087fa859004fff524c003ff982401dff509310057ec899003fc624c01ffe21e4002bf985300077ac121003fd3248403ff1864016ff591211577ea12109bff658c803fe9822000bfd81320cfee6390843ff54c8007ff21c6405bf19510117fea099013be6290811ffaa22016ffd092115778cb2103fff32c8005fa18e4200ff8c920067daa490003fd3148005ff98e4200bf1893105ffa8290053fc3048407fe18a642aef54242025fcc898007fe504802d7eb224210ffd93200bdfaca9080bfe214c44fde3048427ef082420b778c89084bfe544c04dffa8c6424ff88632077f88390003f93044007fea9a6002ff0c7210077c849080fff534c003fe0864000bfd8532025fcc990007fd30c8007fea1a6402ffc8510097f8a89808ffc408c83ffe1026402ff90721047fa86880a3be6190801dfb22641bffd4b2100ff8a09806ffe52c841dff30e4001ff841100057ec89000ffc434c451de28c840aff0c920007fec099027fe414803ffe3026423ff9023211ff8c119007ff104c023fe30a600dbfd972001ffc609884bbc424c021ff2164002ff04131107f8a299087fe644c8017fb126000ffd8910097fe8298007ff10480077eb1c6402bfd8d3100fb86098002fd6348007f79946401ffd4110017fe6290812fc648c829ff1024201ffd0320007fac390016fc654801bfe296401abf59321117faa09903bfe51c8025feaa26029ef18e420d7fca99086ffd53c8405fe18a4200bdd8532137fccb19012bc644840b7f32a6205bf19532067faa490023fc4244045ff32a6403ffcc931097f8c8980a7bc53908197fb2a400cffd4520017fa428800ffc438c801ffb1e4013ff94930057fc869000bfc414c435ffb26421cff1813101ff8a6980167c654404fde1848421ffd093204ff84290003fd60c8437ffa9e4222bf5953200ff84088077fe644c401feb126226ff5963212ff8a919063fe60c8415fe31a4003ff0c1320d7788590877fe424c42ffea9a4225ff50232015fec298803dc6348401ff1924213ff5453009dfaca9800ffe308c801feb04641eff1493100dfec49001bfc654400b7f32a640dbf59720007fec29900efe63c8001df2126400ff4c91001ffca698012fc64c8005ffa0e4222ff19532007eec29904afd644c031fe2864203ff8c5320b7fca890807fd5044043feb226402ff945310cff8a79086
  | 3 => 0xf90a6002bf1852014f7cc7210a7bf3290807f7992640cffd9520107fc429900fff538c8377fb2e420cffd49200b7fc8490803fd31c801bf6a964001bf181320d7fea990842ff64c8007fe29a6200ff989310effe8498807fe50c8005fea8a6216ff1912100ffa4088002fd61c803bfeaa26217ff1492101dfec499087ff644c83dfeb2a6225ffd0632017fca29083bfc61c8051df28c8401fe84130005fec090802ff634840b7f32a6016ffd0121017fea288006fc604c415ff98a4002ff843211477c6321003bf6448003ff8864003bf98d20097f88498012fe644c403ff1024000efd912104ff86290012fe64c841dff20e4000ff58d10015fcc31905bff5448403ff2022021ff50132017fc2090832fd6548047fe2846400ff8cb20017b8629881ffc6344021fea0e4000bf58d21137fca519022ff6444001dfb048401ff1011000ff84098093de318c801fe90a6002bf98720007fac690003de324c8097e3224205bf19721005fac790803ff6344001ffb026203f70c63215778a521047fe614c01ffe31e4003ff50d3001ff8a71903ffc32c804bfeaa46403ffcc9320e7fca09880bfe2144017fe2a24026ff546320dffea190847fc514c04fde0848421ff509320dffaa190877fd644c41bfea964007ff10d1000ffaa0980037f6544035fe2a64200bfd8f20107f88299053fc604843dffb2a6213bfd9530066f8ca9003bfc21c8017ff2a24002ffc852101ffe6119003fc62440177fb22400cff54d20067dca490002bf6448443ff212640dffd47200effec89884bff424c0037f3026400fdc85210077c8498003ff6348001bfb2a4004bf99110007fac29900ffd534c803ff182200fff90f2012ffac91900bfd414c435ffa164200b7d8d2100ffa8088003ff61480037e302420eff88720017fe2098877fd404c443ffaa2641fff98132067fea69000fec328c845fe2926400fb4cb2105f788490087ff404c851de30c8403ff8c931017f8a29085bfc42484037fb0a2012ff9913001ff86498807fc304c001ffb126002ff1472100ffe409006ffc65c8401f69924217ffd41210f7faa498803fd6148047ff2846414ff08121127f8c31901fff3244031ff1064229efcc6420e7f8809882fff4148003fa0822001fe8c1100fffc2099007f8304c007ff18a6003ff0ca32047fa8488063fc30c8403fe0822010ffd0f20015fec29080ffd324c005fe10a6204bf99120017fc6290803df6348403ff2064002ff10510017fea298897fe648c803ffa02201aff19321127fc8319057fc6348415fe29a4001ff141200275cc521033fe52480437eb226403ffd0d3101ffc869881bfc5244005fb28a2024ffc423212ffa8319023fe4244039fe1026216ff50d2101ff86298002ff6244003fe2064021ff19132137faa519007fd40c8035feb264201fe041
  | 4 => 0x16018000a40702801000030f743606a00200a0e8083380117c0483c110102a3243e068090380e0d8180dd05028000c806368141c00804c040003c15009020030540f01457050020984c640110240353c1900c0707c02014000080a6b49f01ca7058060001c000831200000418088010d8030080000002000010181900c0201c120482907c2a02c680545c0e80408c6f0001e10c1800c0200802002610d0da0e40d0012f034233ac15004054140101c4d040831e8420f8020b00302c0f18400005104384d00005000ba05807000000100d5300300cd91080606c0005c3504c090641d020090c00001400310031cdbb01400004030702906c090001105c0202c0001c1002c0706404064060006406000008c501401180000b804020012304e0cc090f47701c0b0d82510285008034f00406806028710041a180000283700c3612801000000000611c100041a0180206c074e0010b8012a3004340401c134a0004940b0085d23400000190021c0180c0100608c0c32c00000340100300407004070740000005048057f30a4015ffcc9210077c849006bff40c8421feaa64001ffcc32005ffe849009bfc658c8037fb1a6006ff54910117fea29906ffc52c844d7eb2c6400ffd872001df8c790807ee204802fffa924202ff1052110dfec899002ff614c003fe1824002ff94721005f8c48800bff414c405fd8822002f78c531007fa6490003ff634844bff2a46406ff99510017f84288003ff604840b7e32e4006ff5951002df8ca9081bff6544007ff29a6200ff58d210f7fca498877fc644c405ea18a6209ff8c52012ff8c91907ffc404c84bde2146400ff5863200ffc2098073fc504c40fff21a2005bf997211477c432100fff438c801f
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc725813100dfa72c812000fdb734c110004ff74d85300069f6418d21156bc65909312067e20d9520005bf745853219cff7158d10006dc64d8d2111ef86058232006ed6218910007ae424cb21004fd75d8f2113ebc60909210e4fd73d8d100079d7390a32006be53d912101ddc7348530014fe76d8520004ff7558f21005bf735864213ebc60d8242006bf6158242146be10d912113fb82058242175be76d9120004ff7558232126dd71d8d21005fb704c9200afcc638c92102cfe75d8121005bf744872011cff70d8d20007b46418532006ee52d893118eed20d8910006bd769093101cfc73d8910006f76518532024fe745891013fb61090910007b57190b210057f7558530147ac2190b21007b76418532006f665d853204ef621d8520006df54d8d2110ebc644c920126dc10d8d21155bc75d8642006bc4258910175be7290910006de70d8d2114ebc53d9132145be7158e42006be74d8910004fd7558910006df75d8d2101cfc72d8d20106f451d8532024fc74d81210c4fe721891014fb73190931006f640d8532006dc74d8d21146bc71d9121126de71d8d21005f7714cb200cef731d8f210cedc6358f21006ee20d8931006bf53d912012ebe62d8e42007e632c852100cfc7018931006de60d8d2114f9f3290a32106f661d8532004fd75d89300cfce638cb210e6fa60d8131024fc7418931007ae428c92101cfe73d85201c67c41d9510006f652d8532006dc42d8d21006f452d8532146bf51d91210067f42d95100067f65d85202067f20d9520004ff7058d210fcfd73d8f20107e4714cb21006de31d8d20006bc42d893101eec638c921004fd71d893013ebf72d9120005f7714c910004fd74d8f200aede72d8d2110dbc7458532006bc75d9120106f676185320073f6590920006bf6358242004fd7458910006bc42189100067f32d951014dbf7658e42006f620d8532126de315863201cfe73d89101dfe952c812013ebd10d912010ebe76d913213ebc70d91201bf7610d9510006dd75d8d210a4ff7058910006bc65d9121085bc7448720005bd7558242004fd72d8530006bc51d9120007b76158642006dd40d8d21006ed6218930106f461585320a6f710587202067e10d9520155bc7558e42006bf64585200067c655891013ebe6290b201efae5290920006bc52d9120004ff7558d21006bc42d85201cd7e76d95101fdef7258d2013fae2090920024fe7458d10004fd74d8532014ff768cb21006be52d912000cff7658321014fc72d8520007cf634c92114ebe6390b20006b7641853202cfc75d89100edbe74d89310e4ff7058d10024be76d91201be7d30d9510025bc725824201cff764c92000cfe7058f21006dc735891001cfe7358910006bd65d9120006dd638cb200067c755823214f9c32d9132126df10d8d21004bf7458d21
  | 1 => 0x8632147ac2190921006bf6458d20015ee714cb21145bc7158e420057f75581310067f65c8520146be6158642006bc42d8f200067e63d952014ebd72d9132126dd72d8d2114faf32d913214f9c6358e42015ec714cb211be7d40d9510146b661d86422e6bf6590a32006bc61d912001cfd72d8532004ff764853014ebe53d913214dbe735864201eee638cb21156be6590a32005bf744cb200067c6558d10286ef21d8931004ff7458d10006bf64581211e6ed2018930006bc42d812100cfe70d8d10004ff741893002cfc75d8d20004fd741893002cfc7558d210fefa30d8132006be52d91210fef850d813200cfa76c8120015f6718cb2114ebc6358e4200df87048520146bc51d912102cfc7558d10004fd7558232004fd7558d10006f770d853201cfc735891009d7c7558930007ac4218931006bc52d9121006be71d913226dbe7290b211367c658c910006de74d8d2114ebe6358e42004fd7558d20186ef2118910085bc744cb200067c6598910006bd65d8242146bd10d9121006bc42d813114f9e7390a32004ff70586320cfe432d8532024fe74d89301be7f10d9510006bf65d9120006bf65d9121006df64d8d211c67e21d951006efa65c81200aedc6358d21147b67190b211be7d70d9510007ae72d864216ebf659091002cfc7558f21156be6590b200073f755824202cfe755863202cfe7558f202df9e3190a32006be20d9121156bc6590930006f574d8532006ac42d89100fedf3058f20236ed3218930006f460d8532006bc425863213fba7090b20296ef764cb2100cfc7258f2004ef431d852013fac2090b20006de6418d2113f9c3090930006bf65d9132146bc6190930006be42d853202cfc75d8f21006be63d91200cdf7714cb2114dbc7358242014fd7258720006bd50d9121014fc7158f2002cfe75589100cef753d85320067d42d9510004fe7648530107d4315893101ecc638c92101cfd70d8530107e4714c9211c67d31d95101c67e31d95100a6fa60d81210067f6558520006bc7458d100c6f86058321056dc31d8d20006bf51d913200cfd768cb20014ff70d89102067e40d9520005bf715824201cfc73d8121005bf7458530006dc6018d21024fc749891022ebd6590930006bf64c8520006bc6458121004fd75d8f20006ec2118930006bd6390921126dc31586320d6be62d8642006f660d8532006ec4218931006bc7458910014fc71d8d200c6f710d8520147b661d8642006bd65d9132146be6190930005ef7258d101c67d41d9510147ae21d9121024fc7458632006f564d8532016f461c8530004ff74d853214ebc6390b21004fd74d8910045bc7458910146bf72d91212067d10d952001cff764c9210667e72d95200fcfd764c920095be74d8930004fd739891003ede63d8d100067d73d9510024fe7458632005e
  | 2 => 0xcef773d8532186ed2118910006df40d8d2102cfe75d8d2000cfc70d8f2113ebe60582422077820d9520285ef7258d21006be42586320067f6558d20006be65d91320cef632d8532006df73589100067f658c920015ec718cb21006ef7258d1013ebc30d9120006df7358d1013fb8605824219ef710d8530127d4318cb21004ff74d8910147b42158642006bf64d81212067d70d9520006bf6390920006dd65d8d210057f75582320067c61d9520004fd73d8520005f5718cb2126dbe7290921006de65d8d21004fd74d8121014fd70d8910004ff75d893107dfb7058930145be71d8e4202c7e76d9510006df638c910007ba42c8120024fc7458720006be74d8930005bd73d8642155bc755824213ebe609092125eee32d8931006bc51d9132006be61d9132006f465d853201cfc735832112ebc648c9210067f74d9510005bf744c910024fe74d813122f9d5390930014ff765872014ebf73d913200dfa708cb200aedc53d8d21005f7714c921006bc61d913213ebe50d9120025bc72586420aede7618d210b7ae62586420afcc634c921004fd74d813101cdc7358910005df7358910226f531d8530005bf745813100dfa76c812008ef631d8530007d763c85210079f6390921006be20d9132005bd73d824214ebe6290a32004ff764c52014dbe73d8642006bf6290930024fc74d8930006bc4258d20045bc744c91014dbc73d8642004ff768c910004ff75d8910014ec764c921006bc4258d10147b46158642266df6218d210067c64d9510024fe74d8f20004fd7458d20006f970d8f20006bd71d913202cfe7558d20006bc64d812101cfd7258f20005f970c87201be7c10d951000cfe76d813114f9c3190a32146bd72d912100cfe70d8532267cc2118d210c6fa1058321006bf64485200cfe7318cb2113dbd70d824213ebc72d9120006f7615813213fb820d9120006ee7218910146bf6390931006bc42d8530006f774d8532007ac4218910004fd751893100cfc73d8131006bf6558242146be6190a320cef772d85320067d64d9510004ff745891013dbe70d8e42016f762c8521007e532c8521006be61d9120006bf6390921014fc71189100067c74d9520007ae424c92100fea72c8120004fd71d81321c67c31d9510024bc7458d10004ff74189100357c7558d10006bc4298910146bf71d912114dbd73d8e4202cfc75d8f20006f654d8532006be10d9132014fe71d8f202067c72d95201563c6590920006bf648c9200067c32d95100addc73581210067c42d9510006bd50d9132006bf53d912113ebe60909310073f65909100cedc3258f21004ff74d8d21004ff7558720124ff71d8d21147b421d91210063c64d952013ebf609091013dbc70d8e4208ef46158530017e672c8521006bc4258f20025bc7258e42015ec764c921004fd755
  | 3 => 0x642d853200cfe70d893113ebc605824202cfc7558f202c5be72909320067c7558d10006bd53d9120004fd741891000cfc70d8d100edbc7458931024fc7458321014fd73d8931155be75586422bf9c428c93200ff3614c11013fb85090b20006bc629093007ede63d8f2002cfe75d8d21006bd6390b21004ff75d81210067c65d8d10006bd74d8931014fd73d81310073c64d9520004ef7258d10024bc74589100067c65585200fcff7058d20126de10d8d2102cfc7518930006f76418532024be76d91212f5ae72d86420067d43d95200067f43d9520006bd63d8242004ff74d8d20006f670d8532006bf7458d21146bf21d9121126de41d8d210cdf67618532024fe74d8532015f47158f212067c30d9520006ee21d89301efad5290920024fc74d8910006bd52d9120004fd7458d210aede53d8d2102cfe7558f21006bc70d9121014fd72d812114ebf6290932087ae7290b20004fe764c52014fac32d9132006f47158d20004ff7458d210ccf77158d21006be4258232004ff74d813113ebd20d9120006dc6418d21005bf744cb2101cfd70d8930106f672d853213f9e30909300067c65d85202067c70d9520004fe764c9100067f73d9510006de6018d21004fd7558f20024fe74d8530004fd755872002cfc7518931126ef618c92102cfc75d8520006be63d9121006bd51d9120004fd75d8532006ef42d8910024fe74d8520126f661d8632006bf644c920007d632d8532006f464185321ef3c65909200067e71d9520127d431d8f21006be75d91210067e42d95200cef730d8532004fd74d8d21006bf62909100b5bc7458121004ff7558f20004fd75d8121156be6590931296f7311893126dbe76d9121024be72d91200d5bc744cb21055dc7358520006bc21d9120156bc6590b21156bc6590a32006dc65d8d21006bc7458d21006be60d91321a4ff7358d1014ebf72d9132145be7158242126df51d8d210cef543d8532006ef6298931006ef32d8910264fe72d8f21015f8764c1100cef743d8532014fc73d8530004ff7458f200cef572d85321be7d71d951000cfc70d893100efb62c8120155be7558e42015ee714c9210067f6548520006bf648c92100cfd72d8520076f4615872001eee634cb2108ef661d8530015ec714c921004fc764c910006fb50d8132006bc42d8f21006bc71d913214ebf53d9132024fc7458d210067e61d9520006bf6358642004ff7458f21004fd764c91004df97098910297d43218532216bd6590b2001eec764c921106dd3158f2113ebf30d9120026bd7690a32006bc52d9132146bf6290921014fc7258f21006bd74d8910006f650d8532126f46158632026be7690b20004fd71d8f20004fc764c7200079d5358e420067f65d8910156be6590930014fe7158232004ff75189102c5be7290a320069f6390921
  | 4 => 0xb21006bf644c921006ac42d89310a5f57198910005bf744c921146bc6190b20156be65909210067e73d952013ebc6090b21146be61d8642004ff7358720006ac42189100af5d7518d21276bd65909210cef473d8532004ff75d8132005bf75d864202c7c7558d10006bc65d9132006bf75d9120006bf75d913201edf628c932006bf6558642006be74d8931006de40d8d21007b64218532005df7358121004ff7558321024fe74582321c67e41d9510004fd7458232125ef734c9211bf7771d9510006bf73d91200b5bc744c921007b642c8521006f9709891014ebc6390921155be75d8242006bc4218931127d421d8d210cef463c85210067e43d952000cfc7058f2114ebc72d9132006df635812113fba3090910006de52d8d210063f65d9120004ff7558d20024fc74d8131004fd768c9100063f6590910006df65d8d21006ed52d893111efa60d8232006dc52d8d21126dc51d8d21005bd71d82420de7c65c8520014fe71d8d20006be52d9132006bd73d91210a6fa10d8121006b442d85321a6df30d8d10006bc60d9132006bf73d912114dbe7358242147b4319093102cfe759891013dbe70d864202cfe751891005dbc7448520086be62d8242004fd70d8532004ff7458321047ae7290910005bf745893114ebc63909200cef553d8532006bf71d9132004ff735832105dbc745852012fae62d8e420067f654c9200fedd3058f20006de20d8d21014f47158d202067d20d9520024fc7458232006f571d8f21004ff764c72000cfc7018910024fc74d8f21004ff7358910146bd21d91210e6fa10d813101eee638c92110ebc644c92100dfa70c872001cff7658f20006bd76909100eebc644c52000cfc7648520004fe72d8d10004fd75d8132126f431d8f21006bc30d912113dbc70d86421bf7a30d951014f9c3290932006f56518532004fd745872014ebe32d9132006bc64581320cef430d8532005bf75d8e4205fae6258242006bc65d912001cfd72d8132004fc764c52001cfe7358720006f551d853201ede638cb20004fd70d8d2114faf3290a32045be74d89101be7f40d9510014fe7118930006dd50d8d21024fc74d8132146bc72d9121004fc7258d10146b4619093206d7e75d8720015ec718c92117eed2018910006dd64d8d21006be50d9121007ae72d8242006bc73d912122ebf6590930006bf31d91200047f75582320067c21d9520004ff7498910004ff715823213ebf70d9120127d431d86320cfe7314cb21006bf76909310cef643d8532155be7558242006df6418d21004fd70d89312067f30d9520005df7348720005bf75d824225eed32d89312067f70d9520175be72909201167c654c910005f7714c92013dbe7058e42006df43d8d10006f454d8532006f552d853202cfe751893101eec634c921127ce21d8d21006f
  | 5 => 0x13ebf6190910026be7690b21006f561c8720004fd75d8d2013ebf60909202c5be76d913202cfe75d8f20266f43118931004fd764c7200be7c65485200079f648c932006be4258720006f570d8532006bd71d91202cebf659093213ebd30d912002cfc7558232014f8764c11005dbc744c9201553c755824218cff7648720015f4714c9102067e70d952005ebe76d9120024fe74d8d20024fc7458d10006df63d81212067f72d9520006dc6518d21007ba424c1102aebd6590b21006bc21d9132006f664d8532126f42158632024fe74d81210cef443d8532006f77158d20024fc74d8d20006bf52d91201f6be769092013ebe70d91200067f74d9520006be51d9120006be425832114ebf30d9132146bc6158642146bf31d9121004ff74d8520014fd768cb21146bd51d9121004ff75d8d20007cf734cb2114ebe6390b21006f741d8532006be70d91210067c6558d200073f65d9120006bd52d9121006bd53d91210067c64d9520104ff7158d21126df21d8d2111efa3058232024fe7458d21005bf7558242004ff75989100af5e7518d2101cfe7398910145be71d8242006bd75d9120006be76909100ced463c852114e9c6390921006bc42d8d10104fd764c921156bc6590b20006df53d8d21006f554d8532006f771589101be7f20d95101be7e10d9510075fb705891002cfc75d8131006fb7058910007ae52d912013fac209092000cfd73d8930006bd6558242006bc64d8d20005bf744852013ebc20d912002cfc75d8d21006bd75d9121004fd71d8d200d7ae7290b21024fc74d8d10006de6518d2113ebd72d9120156bc6590921014ff70d8d1014ebc30d9132006f761d8132014fe76d853004df47158d2001cfe768cb21006ee211893000cfc70d8d21006bc42d8132155bc7558642006f450d853213fae20d912014ebc6390910155be75d864202cfc75d8930006bf63d8642005bf7158e42147943190931004df7358910217bb5090b200c5f77158910006be50d91321367c658c920005bf7558642007b442d8532095bc7458530006dd6518d210a6fa20d812113fba10909302cebd6590932004fd7018931024fc74d8f20004ff74d8d100667e76d95200063c42d952000cfd76c8720127e6718cb211adfb7058d10006ee52189310067f31d95201357c755823200cfe76d8121004bd74d8930006bf30d9121105f47158132004fd76c85301d7b864c81200077b654c1101b6df31d8d10007d463c852101cff7258f20024be76d9132006ec42d89100067c63d95100079c6390921126dd10d8d21006f674d853213ebe30d9120006ec32d8910297e73218532014fd7318931006bf6458132006f575d853213ebc50d9120006ee2018931146bc21d91210357e75989100d7ae62d8642156be6590920075f4714cb2016fb55190910147ae219
  | 6 => 0xb7058d1002cfe75d8f21006bd6290910004ff75d8131004fd75d89100057f7558d10024fe74d8f21006bd61d8242174be769092000cfe70d8d21014fc7158d2013eba60d8242146be6190932147b42190921006ef42d893102c7e76d9520004ff75d8d21006de42d8d21005ef72585300367e76d9510005bd74d8910055f97098930125de7618d2101cfe72d8d20006f77158d21015f4714cb210067f75589100fef8605813228fac424cb212067c20d9520004ff7558d100b7ae729092102cfc755891013ebc6090a321a6dd30d8d102067d30d952014ebc7690a320c6fa60d8321006ef3218910014fc711893014ebf31d9132276bf6590921006be70d91321bf7471d95100067c41d9520004ff74d8121006dd6418d21026bd7690b21287d431d8931296ee3218931005bd75d8e422067e30d95201c77b10d9510014fd701891014ebe6390910004fd70d8f21006f46018532126df638c9210057f755891003fd8634c110004fd75d8d212076e20d9520006f742d85320067e64d9520007b97090b200067e7598910006f750d8532105ed738c92103edc43d8d1014ebd53d91322a7b73190b211fcff7258d200aede63d8d2102cfe75d8d10267ce2118d21006bc6290910006bf6290931006be30d91210067d71d9520006b464d8532006f571989100edbc7458131006f66018532004ff74d8132006bc50d91211be7e40d9510006bd6358242127e4318cb21004fd73d891014ebc6390b20124ff7358d21004fd7518910007f3714c110175be7290930005bd75d864213ebe6090a320067f655891000cff71d8d10014fe7118910006bf7458d20006bf71d912014ebc73d9132005bd7558642006f440d853207ddc7348720156be6590b210067c43d95201be7d10d9510006f66518532004fd74d8d101c67e71d9510006bf7690930004ff75d8532257ac428c92100cfc71d8121007cf734c921147ae2190921056de63d8d2013ebf50d9120006be42d8520006bd70d9121007e5718cb21004fd7458f20006bd52d91320067d72d9510014fe7158f200067f41d952007edc3258f2013fba60d8242006f5641853202cfc7518910004fd74d8d202fdbe72d8e421be7e20d95100cef530d8532017e762c8521004ff75589101fcff764cb20004fd7458321006f752d853201cfc7358720126df72d8d2111ef82058232014fc7158232077d4314c720005bf744c92002c7c7558232006bd51d91320067e63d95100cfd73158f21006bf32d9120006bc73d9120006ec20d89312bf9c648c932014fc71d8d10005df73585200067f651891014faf3290932265ee72d8f21024fe74d8d10005ec7258d10106f651d853201cfe73d812112fae7290a32014ff76586320073c42d952029fac428cb21106ef614c92114ebd32d91322edae72d824214fac3290a32
  | 7 => 0x8910006bd655864214f9e63d8e4213fb81090910005bf745891006ef865c812016f3c659091005fae729092009d7c7558530107e4314cb21007bb64c81201479c31909310067d42d952002cfe75582320067d64d9520146bf6190921155bc75d8242006bf70d9121024bc7458d20006ec7258d100067f658c910006dd638cb210067f659891004ef4615852013fae2090b200073c42d951013ebe6090b21024be74d89310067d41d9520005bf745813210fae729093202cfc75d853002cfe7558d102c4be7690932006bf50d9121146bc6190a3214fac329093201cfe73189100aedf30d8d21007af648c92102c7e7598910126dc31d8f21006bc60d9121126dc21d8d211feef20d893014ebe6390920006bf52d9121006ee72d8f21005bd7558e42006f420d8532006b764d853201cfd7118931007b764d853200cfe7058d21006bf32d9121024fe74d813213ebf10d912013ebd70d912014ebc63d8e42124fd71d8d2102cfe7558d21006df43d8d21146bc7690b210067c71d952019df77158d10004fd7458d10006bc70d9132284ff764cb21006bc50d9132005bf7558e42006f76148520006f775d85320067f73d952002cfc7558d2013ebc609093214ebe30d9132006de50d8d21006bf64d8132006f541d853208df471589301bf7810d95100cfe772d8532006bc6458d21014fe71d8132127c4318cb21005bf7458d10006ef4218910004fe768c91001ddc7358632126f76318532006be21d91200cdf7715893104ef661d8520006df70d8d21006bc7690931024fc7458910006de54d8d21006f542d8532106f631d853218cfe761891001eee634c921006df7358d20005bf744853013ebe6090932124de7618d210067c7558910006f765d8532266ed2118931004ff7458720146be71d91210aedc30d8d2100cfd7318930146bc6190932156bc6590910026be7690a3201cfc7318910006df6518d21005f77158132006dc63581212067c40d9520267d42118d210357c7558910004bf7458d201479e319093103fda534c110006bf65d8642126df71d8d21014fc7258321004fd7558f21146be51d91211167c654c92001cfe7358321155bc75d8e420067f7558d2020d7e76d9520007b464d8532006bc64d81320067f42d9520004ff75d852000cfe70d8520004f77158d2011cff7358d20147b65190910006be31d9120024fc7418930006bc42d8532024fc74189102d6be7690932006bc4258d21004ff7518931147bb1090910006bc7458d20006bf644c5200cef73158f210cef732d853214f9c3258e42266d43118931024fc74d8520145bc71582420067f32d9520156be65909321eebd6590920024fc74d8931006be73d912000cff71d8910014fe71d8d10024fc74d8d21024be74d8910006bc20d9121004bd74d893100cfd73d8530006f
  | 8 => 0x26bd7690b20006bc64d8532024fe7458f211be7c70d9510006ef7258d21155be75d8e42004fd7598910007d632185320069c42d8d21004fd74d893001ef8764c110004fd75d8520146be21d9121006bc42d8910014fe71d893002cfe7518930007af744cb21024fc74d8532127cf72d8d21126f631586320079c64d8d21056dc6358d20015ee718cb21006bc64585320067c42d9520006ed5218931146bc6190920006be769093103edc32d8d101dfea52c812014ebd73d91320cef630d853214ebf32d9132126df31d8d21024fe74189310077b65c8120004fc768c910006f442d8532004ff74d8f210067f7558d10004ec7258d10106f410d853213fb82090920006bf63d82420cef663c85210067c74d951001edc638c921006dc54d8d2105dbc7458d20006df74d8d21024fe74587200053f7558242006df634c92014fbb3090930006bc42d8d2014ebe63909210067e42d95100057f7558d20146bd31d9121127d6315863214e9e63d8e42006ec421891011cfd70d8d2000feb62c8120006ec3218910014f676d853228fac744cb21005bd74d8930005bf7458d200c6f82058321257ac648c921024fe7458321217ae5290b20015ed768cb21006bd6390910006ec42d893124fac644c9211c67d21d951001ef8634c11000cfd71d8d10006f761c85300057f7558132004fd75d853000df8704c920006be42d8530006bf52d9132006bc64d8d2118eef20d8910006dc63d8121126d431d8f212067d72d952013fb83090930024fe7458f20014fc71d81320aede43d8d211c67f21d9510266de311893101cfd71d8931006be75d9132006dd43d8d21004fd72d81310067f64d95202c5be76909320079c42d8d2114ebf639093201cfc73d852001dde728c9320067e74d9510006be62909101d7b842c8120004ff75d8d1011edf30d8d2013ebc10d9120106f673d8532004fc76485300047f7558d200067d74d9510126d76318532006bc31d91202067f10d95200067e21d9520095bc744853013ebf6290920006dd52d8d211eebf6590920024fe7458d201e4fe72d8f20005ef7258131006bf64d8d20006f540d8532126dd51d8d21006df634c921014fd72d8d210cef432d85322076c72d9520104fd73d8f21106f621d8532006be42d812105ebe72d9120006bf6458d21005df734852005ebe6258242004fd7318910006bc32d912015ff1514c11014ebe73d9132006dd74d8d21007ae72d8e42024fe74d8d210067f654c520076f42158720015f4714c921266df6118d21005bf7058e42146bc61d8642006bf74589100067f6558d1024fac424c921006bf6390b20004fe72d853002cfc75989101b6dd31d8d10004ff74d8930006bc42d8930006f46518532156be65909101e4fe768c920006be42d81310067e31d95202e6bd6590a3202cfe75d
  | 9 => 0xf10d9132006bd74d893001ede638cb21006bf64d85320b6be76d91210dd7e75d8321004fe76c85300069f64d8d21127ce318c9210067f75582321be7f70d9510014fc764c921004fd7458632016f46148520004fd75d8d101be7d20d9510006bc7690910006bf6390b210067f72d951014f9e5390930107e57218532006f474d85320079e428c93201cde76d8d210cef77158f21146bc10d912113ebf6090930175be7690920004fd7458f21006bc63d9120006bc75d91210047f7558d1002cfc7558632006bf50d91321c67c21d9510147b62190b2101efa634c110005bd71d8e42006dd54d8d21006bc4218930006bc4258f210079f64d8d2114ebe31d91320cfd432d8532004ff74d89312edbe72d8242006bc76909300fefa60d8132006ef6298930006be60d9121266dc3118931146bc31d912102cfe75d8131146bf7690b21005fb704852013fb41090910006de75d8d2101cfe76d8d100067f654c910006bc32d9121005f771589302b6bf659093100cfd71d8910127d43198931006be75d9120006de30d8d210067f64d9510006bf75d9121004bd74d891002cfe75d85302aebf6590b21006dc50d8d2100efb614c110006bc20d9132006bc6458520127cc318cb2100cfc70d8532004fd74d813203edc6358d10024fe7418930296ed321893101cfe76d8d21006dd70d8d21004fd72d8d10024bc72d91200bd7c755812100cfd7118910146bf10d91210b6be72d91212067c10d952002cfe7558321264fe768c92125eee768c9210047f7558910024fc74d85301be7f30d9510004ff75d853001cfe76d8d20006ef7258910265de76d8d21006ac421893114ebd30d913200cff7118910006f77158d100069c64d8d21004ff75d8930006f731d8520014ff7018910004fc76c853004df4714c92008fd43158131146be31d9121006bc75d913201edc638c91014dbc7358642006bf61d82420067c31d9520006bd63909200057d7598910146be619092002cfc75d85321e5ee72d8f20156bc6590932006bf7458d10007e7714c92101eed768cb210067c32d9520007ac42d8931006be51d913201cfd701893000cfc764c9200fefa20d813213dbf7658242145bc72d912117cfe76c85201bf7410d9510006bc42582320e6f86058131004fd7558321005bd75d8242105f676d853202cfe75d8532004ff7458232006dd53d8d2110ebe6258e420067c65d891013dbe70586420067d43d95100067f71d9520004ff7158d2001cfc7398910007af644c921006bf64585320067f65d8d201be7c30d951000dfb734c11001eec638cb21087ae62d82420067f43d9510006bd63586422067d40d9520014fd70d8d10004fd711893010dbc7458132006bc64d8520006bf64d8d210057d75d8720006f46158132006bd70d9132004fd74d8f21006df7358f21
  | 10 => 0x893002cfe75d8931006bc71d9120156bc659092012ebc648c92015f78654c110006df50d8d212067f40d95202fdae72d8e4213fba2090b20106f641d8532126de618c93201cff7658d10006f565d853226dbe7690921006be71d91200079c4218d21006bc10d91320657c7558520146bf6190931006ef629891017cfe7298910147ac21d9121006fb7058d200067d7598910004fd73d812102cfe75d8132106f43158f21006b642d853213fac20d91200b6be625864201cfd71d8131007ac42d891001cfe768cb2002cfe75d8930126dc618c93202cfe75d852014dbc73d82420cede63d8f210073c75582420067e73d951008ef421d853007edc6358f2006e7865c81200067c63d95200f67c654c52000cfc7058632006de64d8d21006dc70d8d21004ff75d8f21004ff7058f210057f7558121016f661c872002c7c7558d20055dc73485200aedf32d8d2113dbc7058e42006f475d85321c67f31d951010fae6258e42126dc41d8d21126de31d8f21006f461d813201eec634cb21247b442c8521006bd6390b20005bf705864200cff7658232024fe74d8910006bf6390910015fa714c11014ebc31d913201cff7658f2127ebe7690921005df7348530006ec20189310c4ff71589100067c73d951001edc634c92102cfc7558720006bd61582420a6f8605812110ebe72d9132004fd74d893114ebc32d913200cfe7058632015f8714c1101563c659091002cfc7558321005bd70d86420cef453d8532024fc7458f200067d73d9520127ce318cb2113ebf7690b20147b43190b21285ef764cb21006dc40d8d21006f66418532146be6190b2004fd4314c520126de51d8d210a6f850d81212b6bd6590931146be6290b21015ee718c921145bc71d8e4200efa76c8120196ef21d891008ff2514c110006f764d853200cfc7058d210d6bc64c852001edc634c920006be65d9120006ef7258d2000cfc70d85200073c65d91200063c65d9120097ae7290930004ff7158f20145bc71d8242014ed768cb2113dbc72d91200067c72d9510006bd76909300a4fd7198910004fd75d8931126df41d8d21005bf745812114f9e5358e42005bf7458930007ad52d9120004bf7458d10006bd65d864214ebf7690a32004fe72d813124fac744c921145bd71d8642216bf6590b20005f77158d200adf5719893114dbc72d9132007af744c9210067c7558d20006bf70d9132006bc53d91200067f65d8d100057f7558520265ee768c92102cfc75d8121267cd7218d210067e43d95101be7f71d9510004fd74d853001fcf628c93213ebc609093102c7c75589100e6fa30d8131006be21d91320c4fd7098910106f710d8532145bf7658642024fe749891002cfc75d8d10024fe741891002cfc75d813223eee32d89300aedc43d8d21024be74d8930006dc20d8d21006b
  | 11 => 0x13ebe20d9120005f9708cb2017eef20189100079f6418d210067e72d9510004ff75d8f2002cfe75587201be7c71d951014ebd31d9132006f740d8532006b46418532007db634c110126de21d8d210069c6418d21175be7290b2003ddc7358910007b44218532006be65d91210067c6518910286f76218532006bf7690910127cc21d8d21297e432185320cfe732d853201fce728c93200cfe76d813214dbe73d8242005bd70d8e42005bf7358242006f550d8532006bc4258720045bc7458d10005ec72585300067c65d8d20006df7358f20004ff7458d2002cfc75d89312076c20d9520006bd65d91210067c73d952023eed32d8930004ff7418931126dd31d8d210f57c7558131006be7690930007b642d8532236ee321893000cfc72587200cfe7714cb21006be73d912100cfe764c9201be7c20d9510006bc53d91210067c43d9510005bf7458d2113ebf6390930006bc42d8d21006f610d853213ebd50d9120006dd42d8d21126dd41d8d210b6bc6448520126dc71d8d2101cfc7258232007b764c8521006be42d8132196ed21d8910004fd75d8131006bc63d9121024bc7458d21006bc4258321006bf64d8520006ed6218931024fc7458d201df7865c8120014fc71d8f20006ec21d89300067e41d95200cef653d8532006fb50d812113ebe60d8242004ff7518930007bb60582420efae7290931217ad5290b20004ff74d8f200079c6418d21006ef42189311c67f41d9510006bd63d86421afd431d8131005bf74585200657c7558d20167b8424c1100063f6590920284ff7258d21024fe74d8931006f754d853214ebe63d8e42056df32d8d20006ee72d8f20106f441d8532015e4714cb210067e64d9510004fd741893126dbe729093116ebd65909100b5bc7458d2113ebe10d9120006df52d8d21006df42d8d21004fd7558d21006bf51d9120006bd75d9132006bf65d82421157c7558132006bc6458d20004ff745863213ebf20d9120007ae428cb2126cbe769092100cfe7018931106df3158f21014fe764c921004ff7258d10267d4311893100cfd72d8d20127cf638c921004fd7518930015f672c85210a4fd7698910006dc60d8d2113ebc7690b20006be53d91201be7e30d951000cfe70d8f21004ff764c9102076f72d95200057d75d8321004fd74d85202f5be72d86421be7e70d9510004ff7558632014fe7158d2021dfb7058530024fc7458f21006f464d8532247b464c852100cfe70189100079f6358e42005bd74d8931127cc318c92100cff768cb20006df7358d2111edd30d8d20014fe76d85320063c42d9510006f470d8532007cd638cb21006f751d853213dbc7058642006dc75d8d21076f661d8720095bc7458930006f675d8532014fc71d8930004bf7458910006bc629093108ff0714c1100067e74d95200057f755
  | 12 => 0xa00300102905000200e0210040000c004800706b00300906200200000d18e05d0172c700200500700d00e01001100000000006b00900004900e00002e3fa0000200020200120a600700c0020010a900801601100e00200000000d00100000500000105900003200000201200900e00204900006e00002400800000403600a00d02600b00707300c09f01205500c00001419f01202f00000000107d0a001203100214822f00300101408907102f04504801d00022a00901001100201b0000700ce00000100003a0020140000110d501200000000602000125008c1ed01302400100000200710303600200000001100e06501d0b300400600800200a01400000400000200a04f00700000b0c803700e00300000500b00000400900001801e1bd02a00000700000200100500500000201200c0b40080660030011bf00500000300100000000500201502d10e00211a0130080070221530190cc00300300007800700211600902d00900713102a1690020040cb00000000000303e0040250160a200001801e03e10d00c01300501d00b00303e01408f00205e00200f00901000000100a01300101501f00200506200400600000300100100100e01f04c00500100000901100000108500f05500001f0062dc00300100a06700000801100001802600a01300703701203602500100a02a0cf0040520a305101300000100501900702900000002e04500702300e01800802206c03202e05a0160000680b901a0004df06b01201400005100800100005900300400400600801601000000901800118004d0000ab00400900005001b00109a0000110af0b300034200100000504f04c00f00900000000500300113603e01100000000004e00300f00802600000200200a00001e2ab00000000001800200028b24704700900000b00200103405600b0030ed04200d04500c01000000000105100102c01a00901101107000005238203100401a00100707e00001702100002200b00700600003a03400400c00300000300000000700300500202e0000390070050350060092ff01b01200000102602f0150002760f501a04b0000000070de00202b0030020180b735d00002500600200400000806401909306e00200100c28405e00e00001403300800103819603b00201525900000700101203a0040020000620021b000001600000103500a00501901000100600f0c802f00002000200500505000404601e01203200405a00508900a03d00219200100000a0600060a328f00902100d03c00004800607003c07d0000a402000500028e00c0000c602013505603c2d100513600501004701b00900a00600d00b01a0000001e30210150040000067d74d9520006bd73d912015fd9534c110004fd749891001cfc72586320047d7598910146bd71d91211be7c40d9510
  | 13 => 0x100300500006a02503000200602400536c1ed0000070010110000da00c00200300500600c01d00063f05701401000302f0030090320980000010200ab00200006100000000201e0060160060000050001f60
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87f8759365480014790ab86c8990022fe1d65d9120126663b6c69924228ab48158e424800917d09baec488003171cc65585200055bc22a5b0a6400a9d84980634840117f08b96c688002bc20152d853241753990c830a6438a7980dcb65440014ed0ba06c2990ab0f1d565586420045ec3ce9b12200587e87dd5634400117d0e286c8908030f61c42d951000656c3885b122000cae84dc96344051970ed2126088002a7a1265d8d21006363aee4b1a2000e2e8510b62440c7d5500210c4881ba8fa1665d91200043f43ecab1a4000c5f65dcd62440014ed0a216c2990028f61263d952034e1f396cb21240008bd84dd931480018bae639eca900032b9c876909100046ec38a1b1a42048bc82dd16244001938e6322c2901af8e08065d912041752b90c830a64278bc87d9132480018dae4396ca880e29e60074d95100064fb26e6b0a4000ab684983614c80187ecbba26490002ab61c42d89100056dc02ca31a4200a3e850cb6448001878ebba2c6880028f61730d91210061e3a0cab122064ea681108624400155f04b1c84880032be107258d100065bb26e2b1a40048bf875d3624c11d56d0c216c29900387d4e53d91210051f424c7b2a4027aba800c764480011ed0fb0ac09900a3da1f7158d200061e3a6cab122000a3e8418f654412b74d05b0ac3210038b9cb65909100054ec18a1b22420093e871d5609093371d05b1ac7210a72b1db744c9210054f418ebb224000e2e85108624400187eebb22c29000317dd463581212a55bc0ac72124269c3e76d97644800117d0e3a2c6900022fa1c4258d210061e3a0cab1a20008be871916148001878cbba2c488002ab21162189310054f424c031a4200ab684d4b614c8011df04ba2c6908a6ab60b70d91320062fba8e6b122000a9c845976348401ccea5296c2990028fe1563909201445f43ea5b224200cb7741c5634800199ee6392c6880171b9d652189310061fb2ee8b122061cae72d8a424400135d05baec3210032d1d37158d200046f438c6b024200ad583980614c801938e831ac0908030f1d36558d100064e3a0e6b122000c77751c563480015cb04286c2991970f1d442582320064fba0e6b1220008be871d163484cb17f0ea96c8991dbb10c442189310055b424c030a6440a7a800c7654800153d09a96c6908aa4fa1f75582420043ec2ce5b1a2000c3c751d163480010ff0ab86c6908161f21570189310056bc0ac831a42018ed879c8624400155d05bb484988aa8f215769091000c7b436e299220298be87883644c801c3aebb20c690802aba1220d89310065bba6c2b02642aa3c8558a424400155d0418ec8900022fe11711893014e4f39ec7b048400c9f7418d6048401968c9b8a64908030fdd77458d200051f42665b2a20008bd849d932440011df04bb2648800387d4e53d9120
  | 1 => 0xeea322c29000237e1d6418d210065a38ec89924000caf741c9634400193ec9b9a4290003a960442189100046fc1aeab1a4200ab781597644c8554790abb484980063e2017558d214455b430c830a6424ad68114363484ef53d0c210c69080e3e60375d89300056ac18a1b0a647facf83588624c40117d0fb22c6901632b5c842d81320061e32ee8b0a40048be849d9324400147908b96ca880032d1937158d200075341085b0a64008bd87887644c84f1790eb0ac12100237e0d7458d211551f42cc521220008bf845d5634800117f08bb26488003271d37358d100055dc02a5b224000ab681143644c8018deea392c6880030f197744c910106723b6e29924262c3e72d9642440014b906b26ca880028f61662909100045f43884b1a2074c9e76d8e4248451958ed2126490802ad60665d91323d746b96c831a4200d2e62dd5609080195ce43b484989cb2bdc8645812102c3f42eec98a4000a9e841d763484091790e212c688003a5d9232185320061e3a8c8b1a407ae9421d90634840187eebba2c488003271d3735891000747396c7212420087e8710b654400917d093b642980030fd97744c9100062fbaee6b1220008ef87588624c4ed95ce4216c790867b118d32c85212c64e39884b122000c9f74dcd62440b153904320c6908022fa1c30d91211455b410c830a642aa3c8558e424400b0f90abb46488003aa60042189100051e422e7b2a2000cd473d85214800187eea3a2c488002aee0165d91321561e3ac84b046400c7471d9532480019a8e7b8ac488002bc20165d853214e4e31ee899242008bd879d3624c0cb17f0ea96c8900021fa1c32d95200051fc22e5b2a2000c9f64dcd60484011bb0f320c6908030fdd561582420045f438a1b2264008ef87588624c00155d05bb484980022fa1f64585200043f438cab1a4000cac7210963440011d904ba2c6880022f61f32d91204be57392cbb0c84008f7815d16348001878cbba242900122fa137258d1000574402a5b1262008bd849db214c00917908b96c2980028fa1463d912102c3f42ee0b1e4200a9d84d4b634840117b0fa96c89022fa50cb64185323f557410e7b22426be2d821976448127d54c1396c1210028fa1432d912114d4f418a1b2264008be87d4f644840153d08286c6908032dd93714c9210063c32ee090a4027cbb76d816090801878e832ac69009e2f21f644852002c3fc3aeb3122000e1e7519063484031f100ba8c48800317d97734852014d4f418ebb22640087d879d6624400117d0fb22c090803171977358910125e241ae31964200ae481588624c0edd1ec4210c6908022f61c10d91323cd67c12c831a4200e976418f214840917d0dba2c0908161fa1f75582320061fbaec8b024200a3d8598f644800917908bb264880032d1c464581320063a3aee2b1a4000
  | 2 => 0x375d89313b74a188843126200c7865dc1324805117d0f106c8908163b61e521893126c5f43ec890a4000e2c65108624400147d0839eca880032d1d361581320043ec3cc9b2a2065c3c7510963480011dd05bb464880030fdd47458d1000579c02cbb0a642ac3c75d956090905d1d06210c4989069ea1b65c81200065a38ec8b1a4000c7875dc1624410d5cf02b10c4988032d1d061581320043fc2ae8b1a209ae8e639cb639080147b0a196c8900030fdd4425891014e4fbb6c6b1c8400c9f73109624400147b0a31ec8908032d10b7158d2026c5f436e899242008ef825d1634400155908a90c49880e37a0f74989103b746188843126200ad583990614c80196ec9b8ac0990030f1977458d1013d5d406c7b048428cb776d856190801c5eca210c488003391cb7158d100051ec26e5b2a20008be871916048401878e9b2a4290002a7a1353d8d210055b40cc1b226419ad683143614c8a355d0438ec8990032dd93714c9200045ec38a1b2242008bf845d563484011bb0f328c6908038ba1442189310045ec3c41b226427aba80d8760908018b8ea39ac4880030fdd76458d200062eba8ebb1a422eaba8690b204800187eebb0ac1210029e60031d95200046fc1ae8b1a20009ae82dd76090851968e3b2264908021f61c42d95100055b424ca30a6400ab880597644c8071b906baac488003550c775581312c65639084b0464278bc8759560908011df04ba2c4880028fe1570d91320061fb2ee8b1a20008be87147644c80153b09386c6909f32bdc86458d210054ec18a1b226400ab5849c3614c8031bd0db9a42981031e9db65c81200061e3aec8b026400abb8054b64484010fd0e3aac1190030f1d7645852000477c3ac4312200087f8759365440718e8e3b2a64880032be0974d89310055b40ccbb226400e1d8510b6348401878e832ac290002ad61220d853200578402ca30a6427aba80d9760908018e8e3b2ac6901e3a5d8c42185320063bbaec2b026400cad7410b62440018eecbb8a64900029b61442189310051ec24c3b2a4078e943110b63c840917d09baec4980032b9ca76909310061e3a8c8b0264048bc845cb63440f9f0862216c498802ada1050d853232e1f3b085b2a2000abb8059764484018b8cbb9ac29000e3b60b74d813200557410ed2122000cad87108624c401c3aea320c69096f279db6418d210054ec24ca31a4200c3c74d9532480edd1c62210c4988029721570d8d2100579c02ca30a6476e8431108624c40117b0f3a6c4988023ee017558d210045fc22e031262048bc845cc62440010ff0aba2c4881f6a7a1842d8d21006ca18ee8b026200aae8214364484015b100b28c690a32b960a65185320063c3aee0b1a4000cad871086244001938c9b9ac29009e2fa1e21d91200245e422e23126028ab681d8f619080187
  | 3 => 0x430a64048be849da3244001958e9b92c690802ae60031d912013c5ec3ec7b048476ea681108624c4018e8ea38ac6900031d1d761581323dd66c14ca31a424dab68690b21484018eaea3aec299002a7e116518d2141753988843126200c9e635d7639084f974edb2640900122f21175589100046fc1ae8b122000e2d8510b624c40917f0eba6c4880a6a720d629091014d4f436c72124200e94648c8614c801878ea3a2c4880022f612768c91014c5e43aa5b226400c5c75dcd624400b0f90aba2c690002b56066418d210062e3a8c6b024200c9c64dcd214800117b0fa96c8990161fa17764c9100056ac1cca30a6400aae82143644c8011db0e210c4880030fa1c42d95202c54f4348519264588be87d91324840147b0b30ec8901be8fa1842d95200061e32ee89924087ce772185604c801d1ce4320c69080ab921932c852114f4631c851924200a3e84dcb654405d17d0dba24290003710c772581310045fc22eab1a2042e386590b204800153b09306c6908161fa1b75589100045f438a3b224000c6c751c963440015cb02210c4880029da1770d85320043ec3865b2a2000c7765dc53244001c5ea5296c8900a22f21d63586420045fc22eab122000c6c65dc9634400195f04ba6c4880029761740d8d210054ec2441b1a423787c86dd562440718f0edb2a60880022f61e21d912001c6f43ee6b122000cad7410b624c40b1ef0ea8ec2990023b2097558d100061e3aee8b12200587c855c363484015af06b28c29909eab21952d912039d4f424c831a4200c9c7319160484011df04baac6880022f21d6390910126e238ee69964200a3e8498765480499aced196c299207b10c620189312dfc218c8519642008bd84dd7624c40153b0732ec8908038d61442d85323af4bb088431a4200adb805976348401968e838ac690003271d363581214276218aa4312622a93c855c363908018decbb92c688003350c6764c5201445e43acab0c840093f855c3639080117b09b92c68825ba998672d86420245f43ee8b1a40008f687143614c8edd1c42320c690803271d37358d210047bc0aeab1a4000c9f74d8d60484018e8ea30ac0990032718f7458d2100656c26e4b1a2000c3f65dd163480018e8cbb8ac6900022f61f32d91210063a32ee299220038dc831d9214c00917908baac6908030fdd47458d200055b424cbb0a6400a9e84983634845353d07bb484880023ee017558d200061e3aec8b02420087e87d9562440d555d043aec8900de9ea0073d95103661f3b0cbb2240008de87d8d60484df878e5b2ec8900021f61c31d95200051f42e61b2242048bf875d3624c4010fd0fb2ac688002a760c75d91200ce6a31ee29924200aae84880624c52195ce4b1ec121002b56066518d210061e3a6ca9922000ad8805976348401c5eca216c4880023e60
  | 4 => 0x24800147d0910eca900030f1d47458d1000556c1063b224065c3c7510962440fbd2863b1c85908028f61063d9510006ca18ae9b1262278be87ccb64480014bb0a216c6908a32b5da428cb210051fc2ae1b224200ab78158e424800153b08286c690802aba13321891045573c12c830a644cad686d8f21484499a8e3b1a649080327193735812120735b16cb9024000a3d85dda4244033d88c719642908aa8f21563909200245e422eab1a20048be86dd161480b117d0fb2264900023ee01755891014e4f39ec7b0c8498cae72d97619084f55b043aec8900022fa1c10d91320062eb98e7b2a20008be82dd16344001c6d0a216c2990038b61442189100054ec26a7b1a4270c3d8710b654812995ce5b1ec1210030f5d074d95100065a388c8b1a4000aac8258e42440019a8623b262900031e5d750d81320056dc02a5b1a4200c3f75191604840155d043b48498002a72116518d211266a38ee6b1e4200ab784594614c8018e8cbb8a64900021fa1c655852042f6218ca43126200ace8214363484051f301baec4880032ddd37158d20006ca18ee8b12624dab482190614c8051e902ba2c690002ae20152d912102c3f42ce5b1a2042b38855c242c800153d07306c8908032d1d37158d210065db84e1b226400c3d741d365480011bf06bb264880aa8fa1b65909100043f438eab122000a7585d03614c801b48e3ba265908a62fa1e21d91320071632885b122071ccf7218d60484e993ce5b1c84908032d193714c9200066639ee4b1220008f7815d56348401c5ce5b2c84900029b60831d95200043fc2ae8b046476f8431108624c40187eea322c6900022fa1c6458d210061e3aee8b1a4000c3f75109634406f4f501b96ca880028f61432d91210245f43ee8b122000cac841c9634400156b093aec2990030fdd442582320043ec2eed19220008bd87147644800147b0a39ec890802b5e056518d2100557416ed2122000a3e849c76548001958e9b92c688002ba20152189310055dc02a5b226400cb464dc5604c801878caba6c4880321f61c32d95200051f42063b2a4076e8c21190634840159906b10c4880023de05764c9100061eba8ebb2242048be87dd1634400b0f90aba2c119002ab60850d91210056ac08a1b1a4200c5f75d8d6048401878ea322c2900122fa13768c9100045f438e8b12200087f855c0624c40117b09baec4980022fa1f53d91200055ac08a1b2264048be849d9214c00117f0eb2ec8990a22f61f63d86420043ec2ee931220048be84dd931c800187ecaba6c4880028fe1173d95100063abaea3b0a6400ab6849d7614c80b0fd0fbaac6900022fa1f6458d210051f42cc3b224000c5c65dcd21480cf47d04216ca8809eae20152d91200245f43ee8b1a4200a3d850c764480cb87ce432ec8900038bd4a52d91212df4bb1c8
  | 5 => 0x9002aba0876909310047ac3cc830a6400e2f5294b644c801d4ce4320c2990122fa0b745891000637baee4b1a2000c9f74dcd63484a9d28c72164290a26ada1264185320055ac20a1b0a64298bc86dd1604c8014bf06b26ca880031ddd461581320062e3aec6b024200ab484597614c80153d09386c6908029be0964d95100061e32ee8b1a4000c3f65dd1214800156b09300c2990028fa1663d91203e657b9084b1a42658bf8754b64484071b906ba2c488003a50c7644c52001c76412e8b046400a3e850c7644800153b07bb484880122f21172d81310071c32ec9902408fab68690b614c8015e700a96c2990030f1d36558d200245e422eab1a402aa3e86d96424800153d09328c6908029d61770d853206cbc42ae119640008bf8758e42480edd2842320c690803171cf65585200072a18eca98a4000ab6849c3614c801b8862392c0988e29e60073d95100045fc22e5b0a60048df8750f63484553390ea9ac7210a62fa1f52d913200657394ed2122000cac74dc962440019c8c2392c2980030fdd44258d200147a40aeab1a4000a6d8510b624c40117d0e322c6900023d61c50d85320043ec2ee0b1e42008bd87997644c8018b8e7b2a42900022f61c31d912026e5a38884b1a400087e87195624400193cc7baec721003271d3634c9211445ec3ecbb0c8400caf72109634400b0fd0bbb464881dba35c86418d210054e422a5b1a4200a3d841cf654400153b07306c890802ad20565d913202c77c3aa5b12620087f855d163480010fd0e216ca9020ba90c864185320045fc22e5b026200c9f74d8d324840117f08b98c4881cf279d863909210045fc3ac72124200a5e85d03634852355d043aec8990063ea0375d893113c5e43ac6b048400aad8710b624c40156b03306c899002ade1165d85320065a38ec8b026400a9f8359764484011bb07ba4c488002ab21162189100043ec2eec98a40009ae82dd7639080117d0e322c299002b56066018d210043f438cab1a206da3e86197644800153b0932ec6909d72ddc44258d210047bc0ae8b1a4280ec431080624c40187cc5baac1210032ddd061581320043fc2aed1922000c5d75d4f634840155d09996c4880022fa1c645813214556c10e7b2242008bf8758e424400153d0732ec890802ad21165185320051e422e7b2a4000ae682143614c80147b09996ca900a22f21b74581210046fc1aeab122000c3f75dd1634400187eebb22c099002a761075d8d210046f438a1b1a4254cb676d90614c80117b0e186c8908022f61f53d912044d5b4348430a6400a3d848876548001c5b0a216c4880031ddd77158d2000673b90e2b1a4000a9f8358a4244049b88e3b9a64908028fe1562909100053ac2885b0a6400e2e8510b624c45d17d0dba2649009e2fa1f52d912002c3f436eab0a4000cd471d8d3
  | 6 => 0x174a190c830a64048be86dd1604c8ffd8863396c7908023de1d641853200556422a5b1262008ee82dd363c84018becbb9ac2900028fa1473d91210054fc22a5b1a4200c3c75d9163480411e90db8ac0990030f1d464581210052f42885b1a4200ab584997614c8015b100a96c6908a3691c6424cb213363db80cab1220008be87d91604c8010fd0e3aac6900161fa1f75589100047bc3aca30a6465c3e7510a624400117b0f106c8908038b614421893102c3e42aec9922000a9e8314364484010fd0e18eca900022f61e65d91210045f43ec8b0a64008bd87d8a42440014dd0418eca900028fe1563909100045ec26ed192200087d8799365480b753d0c31c849080297e1570d8d210045ec3ea5b2242278bc8754b6448001d4b02210c4988038b19652d91200055b42441b0a64048be84dd7624c52155d05b86c8990030f5d442989100051fc2aed212200087f855d93244001968c3ba2c2990030f1d365585200055c402cbb2242288be87ccb64484018b8e632ac4881dea7a186418d210054fc22cbb1a4260cae7218a4244001938e7b22c0908022f61375d891000656c3885b126200e8c63d9232484efd286231484989d72d9d864185320051e42ae1b2242008bf8758a424400159b04286c6909f3a9d8842185320247bc3a83b0a6400c3f75909608c8511790fb2264908030fdd4645813201e663b6e699242008f587994614c80b0f90aba2c488002ad21152d85320055c402a5b226400c3e74197624405547d0bbb484880022f61c51d91320062e39ecab122028ab681143644840187ecbba2c2900022fa1c7458d1045f52b96c830a64008bd879976448001998c6392c68800393d4a52d8d2132e1e3a884b1a2000c3e74d976244001c3d0a216c690a0fb10c742189310051ec2665b2a2000a3e84ccb65480190fb0e216ca90003271cf64585200043ec2eec992200587c855d163440511790ea96c8908022fa1c4258d2014d56c10ebb226400a3d840c7654800153906b2ec8908031b1947258d101bd3d400e9b2a2000caf74dc963440051e9023b264880022fe1d65d91210063a388cab1a402ac3c755956090801d28c831e4290802ad61265185323c64f3b0c831a42008bd84dd931c804f17b0fb2ec12100387d5254d8d210051fc2aed21260048be84dd9314800187aea3aec8901a32bdc864585200055ac26a5b0a640087e870cb654400147b0938eca900a2ada0765d86420045f43863b22400087e87d95614800153b063aec8990a32b1db644c92100637b28e4b1a200587e85dd2624400117b0fa9ec8908021fa1c7558d100051fc22e7b2a40008bd87143644c80917908b80c498803271cf64485200045ec24ec90a6028cb671d8760908019aee638ac69009e2f61f61d82420071baa4a9b0a6400a9e84883634840155b04286c89
  | 7 => 0xe8000001e00400018cd036018820082e050020b17801964018469f96006594010000482200062fc80236000186ae000000b80203800010000a01600004000285407a0307a5c0060088f8ea843900208974030ba028072d08c160b202002020fe0401419802000124b06a388797a8000600c2889204804170000e6fa0380002426c12e20c0060580a7e8040e011060040000808810000262789c3201804048000160580a1080004896015c0398701884c0008e4307e0700005802578023400201804029061482a190000080010884028000502600918548001384c0800c0e004013002d0420009601028018160a0099500427014050403c8073c01271006008662d80000862120d60580c00006000140021423810008782f0000187e0600400838005c01702c2e9be028100309e1580a00090438180000605899680100f0980600204cae0a03e0d8200003608052000015700052330b48a00004204816178001200409002050122c8102181c0003e580060d82000000028098a8105194c030001c0080400e041be01000182160f804058022780008000010000a96c056000030c0ab225e003418023da1c6158132006563a0e4b1a2029aad821c7644c801c3cebb20c69080237e1d6518d210056bc1ac830a64248dc86dcd604840156b02286c8908031dd977158d2046e57b90c8b0a64058df8754f634840187d0e216ca88222ada1842185323b752188843126200a6c825936544001d1b06210c498802ad61260d8532495d5416c0b048400c3d751d7644c8d387cedb2c84900032ddd37158d214
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x80002b00008066415a124d81108624c401a858360442189310040f66274197624400182d8761442189100068a615801086244001aa1816004218910006a10c484548624c401a25856044218931007810c585108624c401a25856044218910006a10c684880624c40122d981944218910007810c685108624c40122d9819442d891000683a0d85108624c401a443161442189313b5a124583108624c401ac0312015218931
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x2008738a12a583604421893100640926c2b02210c498802a05a80c585108624c401502d40634288431262008b06a4312015218931
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x94e
  | 7 => 0x94c
  | 8 => 0x94d
  | 9 => 0x98a
  | 10 => 0x98c
  | 11 => 0x98d
  | 12 => 0x98e
  | 13 => 0x150e
  | 14 => 0x150a
  | 15 => 0x150c
  | 16 => 0x150d
  | 17 => 0x9ca
  | 18 => 0x9cd
  | 19 => 0x9ce
  | 20 => 0xb09
  | 21 => 0xb0c
  | 22 => 0xb0d
  | 23 => 0xb0e
  | 24 => 0x1549
  | 25 => 0x154c
  | 26 => 0x154d
  | 27 => 0x154e
  | 28 => 0xb49
  | 29 => 0xb4d
  | 30 => 0xb4e
  | 31 => 0xcc9
  | 32 => 0xcca
  | 33 => 0xccd
  | 34 => 0xcce
  | 35 => 0x15c9
  | 36 => 0x15ca
  | 37 => 0x15cd
  | 38 => 0x15ce
  | 39 => 0x1609
  | 40 => 0x160a
  | 41 => 0x160c
  | 42 => 0x160e
  | 43 => 0x9c956
  | 44 => 0x9c955
  | 45 => 0x160956
  | 46 => 0x409
  | 47 => 0x209
  | 48 => 0x8a
  | 49 => 0x1409
  | 50 => 0x128a
  | 51 => 0x16c9
  | 52 => 0x1449
  | 53 => 0x168a
  | 54 => 0x12ca
  | 55 => 0x14c9
  | 56 => 0x134a
  | 57 => 0x2c9
  | 58 => 0x150995
  | 59 => 0x150996
  | 60 => 0x3c9
  | 61 => 0x160996
  | 62 => 0x128d
  | 63 => 0x1709
  | 64 => 0x1649
  | 65 => 0x449
  | 66 => 0x161516
  | 67 => 0x138c
  | 68 => 0x124c
  | 69 => 0x1609d6
  | 70 => 0x8c
  | 71 => 0x128c
  | 72 => 0x154b15
  | 73 => 0xccb15
  | 74 => 0x15cb15
  | 75 => 0x140c
  | 76 => 0x3ca
  | 77 => 0x40a
  | 78 => 0x160b16
  | 79 => 0x140d
  | 80 => 0x170a
  | 81 => 0xcd555
  | 82 => 0x20c
  | 83 => 0x15d555
  | 84 => 0x161554
  | 85 => 0x161556
  | 86 => 0x160b56
  | 87 => 0x15ccd5
  | 88 => 0x40c
  | 89 => 0x160cd6
  | 90 => 0x170d
  | 91 => 0x1615d2
  | 92 => 0x1615d6
  | 93 => 0x8d
  | 94 => 0x20d
  | 95 => 0x3cd
  | 96 => 0x20411
  | 97 => 0x140411
  | 98 => 0x14c411
  | 99 => 0x40211
  | 100 => 0x40092
  | 101 => 0x40e
  | 102 => 0x15512
  | 103 => 0x14d611
  | 104 => 0x41411
  | 105 => 0x164411
  | 106 => 0x99655
  | 107 => 0x45611
  | 108 => 0x44411
  | 109 => 0x161651
  | 110 => 0x160451
  | 111 => 0x165611
  | 112 => 0x40996
  | 113 => 0x3d292
  | 114 => 0x41292
  | 115 => 0x3c412
  | 116 => 0x15c412
  | 117 => 0x41554
  | 118 => 0x403d2
  | 119 => 0x3d612
  | 120 => 0x415d2
  | 121 => 0x3d892
  | 122 => 0x1603d2
  | 123 => 0x3cd52
  | 124 => 0x41712
  | 125 => 0x15d612
  | 126 => 0xb15d5
  | 127 => 0x3d5d2
  | 128 => 0x83d2
  | 129 => 0x1283d2
  | 130 => 0x40214
  | 131 => 0x1883d2
  | 132 => 0xd43d2
  | 133 => 0x1643d2
  | 134 => 0x21554
  | 135 => 0x21294
  | 136 => 0x21614
  | 137 => 0x20414
  | 138 => 0x21894
  | 139 => 0x160214
  | 140 => 0x20d54
  | 141 => 0x41414
  | 142 => 0x155614
  | 143 => 0x154414
  | 144 => 0xcc095
  | 145 => 0xcd655
  | 146 => 0x98095
  | 147 => 0x41611
  | 148 => 0x15c095
  | 149 => 0xb0215
  | 150 => 0x41612
  | 151 => 0xd4215
  | 152 => 0x164215
  | 153 => 0xcc3d5
  | 154 => 0x41614
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 938
  | 6 => 2056
  | 5 => 993
  | 4 => 18
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/27+packedAt gbK8 (1612+(h % 27)*6) 6) % 62)
  | 7 => 2*((h/312+packedAt gbK7 (34706+(h % 312)*10) 10) % 938)
  | 6 => 2*((h/706+packedAt gbK6 (98688+(h % 706)*12) 12) % 2056)
  | 5 => 2*((h/338+packedAt gbK5 (58587+(h % 338)*10) 10) % 993)
  | 4 => 2*((h/13+packedAt gbK4 (1260+(h % 13)*5) 5) % 18)
  | 3 => 2*((h/8+packedAt gbK3 (405+(h % 8)*3) 3) % 5)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff07e03e03f03ff87fe00f067d31fc6473e7
  | 1 => 0xf803f8003fffffc0ff83ffff19b2ce607f8c7f
  | 2 => 0x3ffffc003fffffffc000fe1c30f8787ff87
  | 3 => 0x3fffffffc0000fffffff0fe03f007f80ff8
  | 4 => 0x3ffffffffffff00000000fffc0007fff000
  | 5 => 0xfffc00000000000000000000fffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x287b01620e60b219582720a9021410ac6431e3
  | 1 => 0xb089280012a5564828814a6a08b046602d842d
  | 2 => 0x1105aac400268a2b548014461430b8182de86
  | 3 => 0x22294d6a5480010c6729580b603b006d00b50
  | 4 => 0xa443e71b39f38f3c00230608dffc00077f6000
  | 5 => 0xc780001c01800c2004401800fdebed50000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafce0ec80feeaeeeafce0ec80feeaeeeafce0ec80feeaeeeafce0ec80feeaeeeafce0ec80feeaeeeafce0ec80feeaeeeafce0ec80feeaeeeafce0ec80, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40507
namespace PEqualNP.Outside.L_meta_40507
open PEqualNP.Outside.L_meta_40507.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 10 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 60 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 165 := (concat bs0_4_0 bs0_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 50 := bs0_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 24 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 117 := (concat bs1_4_0 bs1_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 46 := bs1_5_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 1 := bs2_2_0
theorem alls2 : ∀ k ≤ 2, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 3 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 21 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 99 := (concat bs3_4_0 bs3_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 46 := bs3_5_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 5 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
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
theorem bs4_4_384 : Interval s4Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 414 := (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 (concat bs4_4_288 bs4_4_384)))
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
theorem bs4_5_576 : Interval s4Atlas 5 576 40 := block_range (n:=40) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 616 := (concat (concat bs4_5_0 (concat bs4_5_96 bs4_5_192)) (concat (concat bs4_5_288 bs4_5_384) (concat bs4_5_480 bs4_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 40 := bs4_6_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 15 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 85 := block_range (n:=85) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 85 := bs5_3_0
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
theorem bs5_4_672 : Interval s5Atlas 4 672 82 := block_range (n:=82) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 754 := (concat (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 bs5_4_288)) (concat (concat bs5_4_384 bs5_4_480) (concat bs5_4_576 bs5_4_672)))
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
theorem bs5_5_768 : Interval s5Atlas 5 768 11 := block_range (n:=11) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 779 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 bs5_5_288)) (concat (concat bs5_5_384 bs5_5_480) (concat bs5_5_576 (concat bs5_5_672 bs5_5_768))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 5 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 18 := bgb_4_0
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
theorem bgb_5_960 : Interval gbAtlas 5 960 33 := block_range (n:=33) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 993 := (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 (concat bgb_5_576 bgb_5_672)) (concat bgb_5_768 (concat bgb_5_864 bgb_5_960))))
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
theorem bgb_6_2016 : Interval gbAtlas 6 2016 40 := block_range (n:=40) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2056 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 (concat bgb_6_576 bgb_6_672)) (concat bgb_6_768 (concat bgb_6_864 bgb_6_960)))) (concat (concat (concat bgb_6_1056 bgb_6_1152) (concat bgb_6_1248 (concat bgb_6_1344 bgb_6_1440))) (concat (concat bgb_6_1536 (concat bgb_6_1632 bgb_6_1728)) (concat bgb_6_1824 (concat bgb_6_1920 bgb_6_2016)))))
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
theorem bgb_7_864 : Interval gbAtlas 7 864 74 := block_range (n:=74) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 938 := (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 bgb_7_576) (concat bgb_7_672 (concat bgb_7_768 bgb_7_864))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 3 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 32, 33),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafce0ec80feeaeeeafce0ec80feeaeeeafce0ec80feeaeeeafce0ec80feeaeeeafce0ec80feeaeeeafce0ec80feeaeeeafce0ec80feeaeeeafce0ec80
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4242599040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40507.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,2]⟩,⟨.or,[4,5]⟩,⟨.or,[0,4]⟩,⟨.and,[2,8]⟩,⟨.or,[1,9]⟩,⟨.and,[0,7]⟩,⟨.and,[3,10]⟩,⟨.or,[6,11]⟩,⟨.or,[5,9]⟩,⟨.and,[13,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4242599040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4242599040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40507

open PEqualNP.Outside.L_meta_40507 in
theorem PEqualNP.Outside.L_meta_40507 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4242599040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4242599040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
