import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36969.Model
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


end PEqualNP.Outside.L_meta_36969.Model

namespace PEqualNP.Outside.L_meta_36969
open PEqualNP.Outside.L_meta_36969.Model
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

def SBf (j : Nat) : Nat := [6, 7, 5, 6, 8, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36969

namespace PEqualNP.Outside.L_meta_36969
open PEqualNP.Outside.L_meta_36969.Model
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
end PEqualNP.Outside.L_meta_36969
namespace PEqualNP.Outside.L_meta_36969
open PEqualNP.Outside.L_meta_36969.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x14d005a0000720000000000e22282871b324940c26c509f465d5ac000000000012801e0002708053003c18aaf10594805c0180348348aa0080000302c4823a00000001c00105020c0810218014ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xf11487290782071091bc003800000000005944ac894889034a4471b4061f40a0c6e002283c3831001780013041e0766500108b6231f858547333000dc00312140000469353c01149ad0400000886800000005c692f95c001b3a818000518174e47a3e855180036138b0003da40560003a60d4000027c002f4d950b821500342e183194c92681f0cd429a1e99c969601169164a4a288fe111aa18867e490e88239190281c2627a4c080c001011e4c3800110140000108804a800c0270ea64c2003211c0000168a088002a89490503b025469d4e1648c973c9dce87c100b0323601000104830005030480090c890111800600018200038101000583800e81870000828209000000828000038000818092880800000509045b94b43b6a9687ae52d0e7aa5a1eb54b4396a96873e51d0e7ca1a1cf55243cfa9a873f5250e78a2a1cf141439f2a0873d53d0a7ca3a14f943429eaa485775150ae8a2a14fd4d42d7a9285b75150a78a2a16d145429a28a853c5050a7ca8214f953329eaa665ad42ccaeca3995d547329f2a4653d548ca7ca8994f551329f2a0653d540cb5a84195b94b41b6a96833d539067aa520cf946419f284836f52506d8a4a0cf54c419ea90833e511076ca220cf940419f2a6633d54cc6dca598db54b319faa4633c548c67ea898cf15131b7a92636c524c6f6a098de141319f2a0633d540c67ca990cf55321da20e433f5488678a910ebd0a21d6a1443af5488758a910ebd0e21d6a1c436e518875c8310eb106219faa2433c544867ca810cf55021d7a1043ad42087688210eb95021d6aa043af430875a8610db94421f328843e7410875c8210eb10421f220843a441087cc6210f94c4219ea9c813d529027ca3206b88640d610c813e50902dca4205b548409ea9881ae521027aa4206b5484096a90813e511035c42206b084409f28081ba501027ca9984f553309faa4613c548c27ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f55320d6a16413f5488278a9104fd51209e2a2415f53482b8a6906b50920bba8a4174514827ca8104f550209f2a6213d54c427ca9084f55210b7294216d52843c843084fd51109e2a2215f53442b8a6885bd4910b6292213f5404278a8087908410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x789140003722d4f806000a80008548530016002cec0000098027045001c64017ba5669180401150b1c004005000c92180001e3600000009403348e58ad4401c135c7401768d83030e008011a000010104002810014280021460002000849918552d0e346154b43a918552d0f276154b438b18552d0f246154b438918552d0e2d6214143c9d485150b276214542a918542ccb2542947328b58a544ca3461551328e181544caa461508328bd89539062d62942418b588548c62d62950318758c54886a661d5221a358c54886a661152218b997438863565104218b59743086a46150c21a998641086a76510421a959441086a56310421a998041086a4648c421a919131086e0604c4218bd89539032651086409918552102346154840a9185521032761548408b1855210324615484089185521022f65884408b594211022d62953308b588548c2a46150b208d987548822c6550920c314d42482a46150920c9508514822d6295310c9950218421d63150108b58854043245408410
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x40804601c0040c09280021238ac428287419cf621454290ae7b288210c2575192310861338ec4a9c81091c56295330848e2b10a918604531854248212bb0a810821415cc5408410
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (912+((h/16+packedAt s1K5 (800+(h % 16)*7) 7) % 73)*7) 7
  | 4 => packedAt s1K4 (4895+((h/55+packedAt s1K4 (4455+(h % 55)*8) 8) % 199)*9) 9
  | 3 => packedAt s1K3 (2420+((h/20+packedAt s1K3 (2280+(h % 20)*7) 7) % 88)*7) 7
  | 2 => packedAt s1K2 (502+((h/3+packedAt s1K2 (490+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0x7fffffe03f81fffe0f81fffffc1e03fc9fe67
  | 3 => 0x7e07ffffc001fffff001f81fffe003ff18f87
  | 4 => 0xf8007fffffffe07fffffe001ffffffc1fe0ff8
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x3021088c48910408052925923012299212b0ab
  | 2 => 0x5246311439222931605a0ae4d64142a4c95665
  | 3 => 0xa48b5a289075525aab0513316ab40539718b86
  | 4 => 0xc614644122460364d29640418d299601ac0d50
  | 5 => 0x7187871c3879c7f1ce79c780e311831ffe000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaa0a0faaaa000faaaa0a0faaaa000faaaa0a0faaaa000faaaa0a0faaaa000faaaa0a0faaaa000faaaa0a0faaaa000faaaa0a0faaaa000faaaa0a0faaaa000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36969
namespace PEqualNP.Outside.L_meta_36969
open PEqualNP.Outside.L_meta_36969.Model
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
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s2K3 (17+((h/1+packedAt s2K3 (16+(h % 1)*1) 1) % 2)*1) 1
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
end PEqualNP.Outside.L_meta_36969
namespace PEqualNP.Outside.L_meta_36969
open PEqualNP.Outside.L_meta_36969.Model
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
end PEqualNP.Outside.L_meta_36969
namespace PEqualNP.Outside.L_meta_36969
open PEqualNP.Outside.L_meta_36969.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xe81bf41d037a83a05f55240bf29c817d539037c87206f10e40bf294817d529037e85206f50a40bf28c817d519037c83206f10640bf28481bf40903f681205fd4d40efa9a815f53502f8a6a07714d40ae29a81bf435037a86a05fd4940be29281be425037884a05fd4540be28a81bf415037a82a07ed0140df202817e54102fca6207794c40af298817d53103baa6205754c40df21881bc43102fca4205f54840dfa1081bd42102fca2205f54440df20881bc41102fca0206fd0040fd20081bd40103f280205fd5330bf2a6617d54cc2f8a9987790f30eea1e617e52cc2faa598778cb30ee196617e51cc2faa39877cc730ee98e617f548c2fca9185f55230be2a4617d538c3be87187710e30bf294617d528c3be6518774ca30bf28c617d518c3bc6318770c630bf28461df308c3f661185fd5130dfaa2613f544c2fca8985f55130be2a261bc544c278a8987790d30eea1a617f524c2f8a498778c930ee192617f514c2f8a29877cc530ee98a61fb304c3bc60985fd5030bf2a061be540c27ca8185f55030deaa0613d540c2f8a8185f94c30efa1861dc430c2fca4185f54830ef99061dd320c2fca2185f54430ef18861dc310c2fca01877cc030fd18061dd300c3f260185fd5320bf2a641be54c827ca9905f55320deaa6413d54c82f8a9905fd4f20bf29e41de53c82bca7905f54f20eea9e415d53c82f8a7905f94720bea8e41ef21c83da43905fd5220bf2a441be548827ca9105f55220deaa4413d54882f8a9105fd4e20bf29c41de53882bca7105f54e20eea9c415d53882f8a7105f54a20bf28c417d51883dc43107b08620bf28441ef20883f641105fd5120bf2a2417d54482f8a8905fd4d20bf29a417d53482f8a6905fd4520be28a41ef21483da42907ec8120f7102417f54082fca8105f55020be2a0417f53082fca6105f54c20be298417e52082fca2105f54420f710841ec21082fca0107bc8020fd10041ed20083f240107a48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd90621f820c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf288217e50043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xf5350af8a6a17714d42ae29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997790f32eea1e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cbbe87197710e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997790d32eea1a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32efa1865dc430cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41ef29e835e53d06faa7a0f754f41aea9e83be43d077887a0df94b41bea9683bf42d077a85a0df94341bea86837d54906fca720f794e41af29c837d53907baa720d754e41dfa1c83bd43906fca520df54a41df21483bc42906fca320efd0641fba0c837e50906faa120dfd4d41be29a83be435077886a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf298837d531077e8620ef50c41bf290837d521077c8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998f7d0f31ee21e637e52cc6faa598f7ccb31ee996637e50cc6faa198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31ef21c63dd438c6fca518df54a31ef19463dc328c6fca318f7cc631fb98c637e508c6faa118dfd5131bf2a2637d544c6f8a898f7d0d31ee21a637f524c6f8a498f7cc931ee99263f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c7bc8618f750c31bf290637d520c7bc6418f70c831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52886fca310fbc8621fb90c437e50886faa110dfd5121dfaa2433f54486fca890df55121be2a243bc5448678a890dfd4d21efa9a435f53486fca690df54d21be29a43dc53486b8a690fdc8521f710a437f50487f6a090ded4121be28243f850486f0a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821bf28843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81bf43d037a87a05f94b40bea9681be42d037885a05f94740bea8
  | 2 => 0x59310cd0006e09f117000000000cb24e928f385902e2cd1e8e10960194c8f211e5c82ba7c4d869cf612300000000000000000b406b000001228003f60012b1c800078c000000000000018000000000000000120000001fc0010708c496000000c70000010a0000d400068800000a3c86819152380750001823480023500000000000000864001a80003bcde9e6454978e79d00647e400000348000c309049e77cc211f27a564c38893c83b8c78913223ac3f0af0f84d80e9493808253e8022765940020013000c000b74706347da8c1325f4600000b4760d30001ac530002250008b4d68973bc8cd0089523c0e1261f32a01514418842c45108031000000521e81740000018e21e000040864ca0001105d2646740001f1ee000621bf0de4e000000258854001b30007154a00030a3a4381d400072c000cf0000000000046e0007b0002dc000001540f67085513f0aa1e05b04e0421c432000000000000000220000015106a668002050000009d0a80000004500009e588001344f4874000e8000521101ca1243b48d02e04c97c509e021c000000bd1e28f8f09b50be66c0016631608c5c81b1581b1290941a8640aba5a4d421ce182713c0000b17738c00000000232000000000fa4c45da6d068130a18000000004d8000006301403a256a0d398ff000a18581671c6360159c13c495c93281014000d887a000000cb09a2302741b9cc24828049a542f87e80000039a2ac001ef0004f03b000436001121a10000005a00009c0100402000030041c04c11008070000100000000210240a070020040a0000c0100504c040000604c120100400c010000401c030000105c020180c0040001407024030040000c0e01c020040a0200101c09010000001400c0d014030340201400004120300a000000000005804010090001702c0302407018020100908000040060040a000090300000000020050140100c0e0040704c00024050000600000018030281408004000030000c0080100020004070340004c02040000080100800018000280f0000000404094030140106400078040701e0140f004000300001c0000002018000242200002010060000400018014140000e004000280000002008080000000c01000030080100407004010000001efca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855
  | 3 => 0x450b8000e3981000000000005249d812a750ea91c5e0a64885693a0734925707c8393d67d0711634807592d91326a0710f8be48485c211700c6a0820130040844b883e242980ca80b1c88ac62a6f0000c0218000008085280d2967112888b00000081000254000150002a681d1e0dc49c090001693140f0ae97b000885401fd05e0005a9a222c2e042a0a43c7d5069f048c118f48442ea318e99b70666b13819e0002fd2088825e8b8000000002b9359b00000a408104000368001030e85a89999c472148341394ce41cbb14f33051c0703f0943e8a121c4c20d8a090b0007f889000000000000000c436c001ea000000000df19c1352a96d44c5fc0a9e502672545a9839c8a46123a07a00046800000000f68002c89c89691c000000000000004312e222000000002590004dd2986500090caf0001e860c728000006bd1f9bb0ee98ca20de34a6c8369be51c820d59d92361fc3483b3ae5cc0480050a8607301e3288b020a3b1a6000928002f299917a9341699040a903322c91894d0b619824879034960000000007b8681602d644453a7b000000bd0003460600009f4fe84c000004467dc5695b352000ffa272025e08828a34055458a0c46c3ccbf10a3725153c27e42419c0009c52a000c98c819803d3b94a3740306e85124465ceea87460000001dc0003f4b7884000584001b63a48d02802d4ba7e0f88002d89a101804000a34470c3250a44400f800067c000831046090d1fc12c1614b0a340862400248000754028ca22a0003000000000003a2835c3c0a000000014caf9742104b90311d1d85380010020a9b8fb0002b000000250058518f9129508a5ced8003249a4510471f86a8002890ac000a910919239c092322400013c9bc368364e89da000184390000003543700041e0040a10649a9c47a8d70bc5
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x1300c27b654c0309798f54c825d63d53209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f20c795153c831d5454f208f99053c823d6414f20ba18121c825e63d52209758f548825e63152209758c548823e64d4e208f593538831e5494e20c7552538831e5454e20c7551538823e6414e208f59053882e9600862097d8d544825c63551209dd85544827461551209798c544825d63151208fd91534823c6454d209dd8553482746154d208f990534823d6414d208f990514823d64145209798c514825d63145209b99721482e8604852097d8d540825c63550209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209d98453082756114c208f992520823d64948209798e520825d63948208fd91510823c645442097d8d510825c63544209b59621082e960084208f992500823d64940209798e500825d6394020ba58a200826f65480209ed9520082eb6548020dad9520082e86148020da545200825e63d53109758f54c425e63953109758e54c423e64d4f108f59353c423e6494f108f59253c423f6454b108f19152c425f6354b109718d52c423e6414b108f59052c425e6314b109758c52c436b520831097d8d548425c63552109798c548425d63152108fd91538423c6454e108f990538423d6414e108f993528423d64d4a109798f528425d63d4a108f992528423d6494a109798e528425d6394a10da149208423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109ed81524426e6514910cbd50524432c5414910d3d4c524434c5314910da580524427a6588110da14a20442786548110da149204436852c41109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436860548108f990520423d64148109798c520425d63148109b988520427a60148109e597200436952c80109e594200436952080109e596100436952840109dd95100427b6544010ba18910043695244010
  | 1 => 0xc63d641493197997324c69c644c931a7992314c63e64141318f590504c65e63d50319b988540c66d62150319e980540c67960150318f992530c63d6494c3197596430c65f6550c31c7151430c63f64548318f191520c65d658c831a7590320c63e64944318f592510c69d64cc43197d95310c677654c4318fd91500c63c645403197d8d54c865c63553219798c54c865d63153218fd9153c863c6454f218f99053c863d6414f218f99250c863d64943219798e50c865d63943219798f548865d63d52219798e548865d63952218f993538863d64d4e218f992538863d6494e218fd91508863c645422197d8d508865c63542218f992544865e63951219758e544867a60951219e582544865f63551219718d544867b60551219e181544863e6515121c7d53534871c54d4d218f992534863d6494d219798e534867a6094d219e582534863f6454d218f191534867b6054d219e181534865e6514d21c7d50534871c5414d21ced53504873854d4121d6d4f504875853d4121ced5050487385414121d6d4c50487585314121da884504865e63d50219758f540867a60d50219e583540863d65950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c218f990530863d6414c219798c530867a6014c219e580530866f6548421ba18121086776548421ce95250087395494021d694e50087595394021ce95150087395454021d694d50087595354021dac855008769215402197d8d52d025c6354b40a758c42d025e63947409758e51d029d63d07409798e529025d6394a40a718d429025f63546409718d519029e63906408f997435031c53d0d40c714d435031c53909408f994425029d6310940c714c425023e65d0540a758f415031c53d0540c714d415031c53901408f596431031d5390c40c754c431031d53d08408fd95421029c6350840c754d421023d6590440a798e411031d5390440c754c411031d53d00408fd95401029c6350040c754d401027b65500409b98854cc26d6215330c715143cc23f6454b308f19152cc29d640cb308f99251cc23d6494730a759331cc26e62d52309b58b548c31f5410e308f992528c23d6494a30a7191328c23f64546308f191518c29e648c6308f992544c25f63551308f994544c31d631513097996434c31c5490d3097195434c31c5450d30c7152324c25e650c930a7590324c31c540c93097997314c29d64cc530c7153314c31c544c530c7152304c23d6595030c718d540c23e64150309798c540c25d65d0c30c7553430c25d6510c30c7550430c31d54cc83097d95320c29c644c830c7551320c25d658c430a7992310c31d548c430c7550310c31d54cc03097d95300c29c644c030c755
  | 2 => 0x27a0001a43c20d8769c218a000390480cc30cd599e0001081c82b358330219570000000006f000044520ee000000488824180003000011047c148003546bd120053521fc3710e27c6382fa2222425ce90612c28205e0380007e8001a32323104a0ea2fc40c8b8ec02a4fca617209c2644a8e8316724869d342c4e0b7a1836a81c049cf2fe000d098001049816a1e3900945c049000560079041e4771100000000f03998d0004a40c0003a83046a0002f2840b70ce2948840000000052c268503ee88c598920064849715a03c288400000006dc7b83d36865c150103e2564c51d90b802c02000000080b008000001d0002c00000024020140700000014020141214401030050001100c050280205c0002c010140c01c0305800000070101c004060041800000034000340800830000010b4010080000c08000120040a0140000004000150b804000010002b00002004000b4170100702c120480100c00070170040401401010060180a01804010000080800400000000740503c0100c000006207c0104809054000180d0740300000088071441704400008010080000004070000f800008040b8120380000006038010140103c0b03400004100040001800080020040b030000029d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9f6150c43a71814310f1d4354843c750e5110f1d43540439798e51d0a5d639474297d8d50d0a5c635434297d8d5190a5c63546429798e5090a5d63942428f9974350b1c53d0d42c714d4350b1c53909428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f65508429e98054cca796015332c715143cca3e64947328f59251cca3f64543328f19150cca7a60d52329e583548cb1f5410e328fd91518ca3c64546328f992508ca3d64942328f992544ca5f63551328f994544cb1d631513297996434cb1c5490d3297195434cb1c5450d32c7152324ca3d6595032c718d540ca3e64150329798c540ca5d65d0c32c7553430ca5d6510c32c7550430cb1d54cc83297d95320ca9c644c832c7551320ca6f654c832c754e43d071d5310f41c754f42d069c6350b41c754d42d071e53d0e41c794d439071e5390a41a758c429071e5310a41a758f419071e53d06418f994435065e63149419758c525063e65d0941a718d425069e63905419798c505065d63141418fd95431065f63548419718d521063d6590841a758c421069d63d04418fd954110677655044197d8d501065c6354041c718d54cc71d54d0f31c755043cc71d54ccb31a719132cc71d544cb31c758e548c71e5490e31c7951438c71e548ca31a7590328c71e540ca31a7593318c71e54cc6319758e544c66f62551319b189544c67b60551319e181544c65e65d0d3197994434c71d5410d318f990524
  | 3 => 0x2f4085b4000742ec080710002206c45f1542e8490060003083e0f98c038a0002003a22a404000af37876cb404f0005184c0b91ae2a4899650000840d1473863e464916102150001e64047a45911e2a66e90d92a000104c78282000880000023a7b0f79ce0007d09780d2306f8d30001381600f80014c7884399d3fa0006505b42a384001f906a58c7987c33457838800000000810001080280000028283cce000000144000521684b4000dd0003c02ca0d2680009e2050a60000003000053c638900000009818c1ec08c9b97030a470700ad08804c5292715c3ec3d8001c85f056000266580b62062ba84ca9143306774ef9a819a2ac259751d24290b9bf08e2f48292c0e006cc0800058008311451768042b08332609c0000029c4e491a090d4064172263c84c8cda1143e278d99da1743602a8fd1c66ec841ea000644f59b9340510f38aa000228cc00000c7d8e204c0000006b000000000349900004680000017e3642b800000190000000002c4000cf11250043000428828000260ca00000000000558000003ae000ea8002181290d1783945ccff1b020e344f29cd2407000b83f0ea59c0005a0006d8c48003967187d17b01c268aa9113b022d1296b0247c8e89bd2d2654fe13b38201c361943f0258f013a34e7b81ba0b26a19cc30014322a03e9480160c8bd14d0003540e0001b43bc7395f1cc450e612b0003f82310b2ee3fca48b71f87c0988cb07c6b8c39663fe0d0cc9a21b86204710f0c65a8341921403d1018a31a47ec680003c627c4e8c81844f47a8a72b63945808c0006b46308d2e24a01d8931b61743b1d02c84d80e97d1366e0a887741c758ae05e38e870cb0eb10a2d4021220007d4d90000007790e87e20c46c3680030400069a120661e000000400508120b63da4940a19f02c000000f1000540479091421e4000df08a000b10de0f46940006b06
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x14280604396a1a4a280c724988000086790600882081431c94354843a2ee2a1ca221d187050d5010e8cb80a8a1e65469c35410e32838ecaa2641941c7655132cc60ebb4a819463075da54cc631a18e4aa08698d1870550434c686b90a8a1863465c05450c31a1ae42a2879850e72d50438c20ebb0a819261075d854cc530838ecaa2641841f76552310c20e3b2a8980611a1d95244010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 666
  | 4 => 551
  | 3 => 21
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (i*5) 5
  | 6 => packedAt s4K6 (i*16) 16
  | 5 => packedAt s4K5 (i*27) 27
  | 4 => packedAt s4K4 (i*38) 38
  | 3 => packedAt s4K3 (i*49) 49
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (6+((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s4K6 (731+((h/13+packedAt s4K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s4K5 (20202+((h/222+packedAt s4K5 (17982+(h % 222)*10) 10) % 880)*11) 11
  | 4 => packedAt s4K4 (22768+((h/183+packedAt s4K4 (20938+(h % 183)*10) 10) % 662)*11) 11
  | 3 => packedAt s4K3 (1064+((h/7+packedAt s4K3 (1029+(h % 7)*5) 5) % 26)*6) 6
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7fffc0ffffc3f07ff0787ffc3ffc0fdc1f3f3
  | 1 => 0xf83ffff07ffffff81ffff83ffc1ffffe7e3c7f
  | 2 => 0xffc0ffff81ffc3ffe007ffc3ffe1ff0387cf9c
  | 3 => 0xfffffe0003fffff80003fffe0003f80fe0
  | 5 => 0xffff0000000003fffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x908644621448610165418264c1324258c0d1b1
  | 1 => 0x22080881209000280a0a0809040494a01a2446
  | 2 => 0x511291240d220652a084d4826a412a0b054a98
  | 3 => 0x65ace249483aab9cd3d04623b3980c33e80f60
  | 5 => 0x8630c38e71c333e71ce76730231030c3f7b000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xece8ece8e8c8e8c8ece8ece8e8c8e8c8ece8ece8e8c8e8c8ece8ece8e8c8e8c8ece8ece8e8c8e8c8ece8ece8e8c8e8c8ece8ece8e8c8e8c8ece8ece8e8c8e8c8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36969
namespace PEqualNP.Outside.L_meta_36969
open PEqualNP.Outside.L_meta_36969.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x113c00a80001c2141808ba9008c01600990aa161920500949831c48ea738680a058ac010302802d3e3c688006cca800884820087c80122001c20c11c8ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32de32fd32fc32dc32ff41bf41fe41fd41bd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xc4b80000008e98424e2a90527400147e582e86bea824ba480078b48a22800a023c10005e3ac0aec29aa4a00008000088681a30760e1e56b000001246a200004a0050706c82009644069c7a92b26e846a8c5c343e3866202c7c281c3204a65400bc260c6272b69e00400018ac605aaa169400364c006400022c1000a045810000183020c08006080040c04f011a48700002c00403765110eeaa221d794f42aea9e857651d0aeaa3a157d4d42ae29a855e528cabaa3195794832e7290655d510cb3c65a0e70cb419eaa4835e53906baa720e78c941ce19283b7515067ca820d794c41aea98835e52cc73e8398e7507319f2a4633d548c6baa718ed50631b7a92636c524c76a8298f3d4931ae29263cc524c698a498f5d4531cfa0a63d6414c73a8298f550531caa0a633e540c67aa818d794c31afa9e435c53c876a8390cf952219eaa4435e53886baa710f30ca21afa9a435c534867ca810cf55021af298435d53087986410ed50421bd280437950086bea6a05714d40af298815d53102dca4205b54840bb288817551102dca5185b54a309faa2613c544c39865905794e20aea9c413f5448278a89057d4d20ae29a41cc32482eea2905d145209f2a6213d54c42bca7885754f10daa0e21b5414427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1000021602400050468072800018000098030000a01282200000278038060000300b0000a95610c941c9149414c70c52d0531a5592414c7445290531c3149414c7445250531e1d49414c7145250531e1149414c7045250531c5d4d41c864d650c821c554d41087843250421d20c9500873141540218d584544c34432145209318953c43155350710
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x81000505750c9410878019282a8043411c95350710
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
  | 4 => packedAt s5K4 (2904+((h/33+packedAt s5K4 (2673+(h % 33)*7) 7) % 119)*8) 8
  | 3 => packedAt s5K3 (840+((h/7+packedAt s5K3 (798+(h % 7)*6) 6) % 42)*6) 6
  | 2 => packedAt s5K2 (150+((h/1+packedAt s5K2 (147+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7ffff81fffc3e0f87ff0ffff87fe07c39f3f3
  | 1 => 0xf83f0ffe1ffffff00787f1e07f8ffffe264c7f
  | 2 => 0xffc00fffe0ffc3fff807fe007ff0ff83c78f9c
  | 3 => 0xfffff0003fffff800007fff0003f80fe0
  | 4 => 0xfffff000000003ffffffffff80000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x1086008c0208400180890223181121180891b1
  | 1 => 0x220899104852225043429144248a4a62224446
  | 2 => 0x5112222486a004a68805240949209508c58a98
  | 3 => 0xe5accc49543aab3b55d08112764c0633780f60
  | 4 => 0x8630887198c333cc6666c99c04081843b76000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfaeae8c8faeae8c8faeae8c8faeae8c8faeae8c8faeae8c8faeae8c8faeae8c8faeae8c8faeae8c8faeae8c8faeae8c8faeae8c8faeae8c8faeae8c8faeae8c8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36969
namespace PEqualNP.Outside.L_meta_36969
open PEqualNP.Outside.L_meta_36969.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10054f028d223179e0001c0000d4d1f00018a2128d6001e045395c0002840183b06e21a3636915994c845bb0601d322a0022d289c91d6640b004a60e172639e8052181810106040000e0c4800c087002640180017fd5005fe54017f55005fc5401ffd4c01fe53007f54c07fc53017fd0c05fe43017f50c05fc4301ffd4801fe52007f54807fc52017fd0805fe42017f50805fc42007fcc801fe32007f4c801fc3201ffd4403fe51007f54403fc51017fd0405bf4100ff90405fd41006f50403fc41007fcc403fe31007f4c403fc31007fc8403fe21007f48403fc2101ffd4001fe50007f54007fc50017fd0005fe40017f50005fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc2000ffc4001fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x4004ff10020027fe6010013fe3008009fe9804004ff0c020027fe4010013ef2008009ff1004004fe88020027fa4010013ed2008001fc9004004ffc4020027f82010013ff65840097fb2c2004ff9961001dfccb08013fd65840017eb2c2004ff19610025f8cb08013ff64840097fb242004ff99210015fcc908013fd64840117eb242004ff19210025f8c908023ff5484011ff2a42008ff55210047f8a908013ff63840097fb1c2004ff98e1003dfcc708013fd63840017eb1c2004ff18e10025f8c708027ff5384001ff29c2000ff54e1004ff8a708023ff4384011ff21c2008ff50e10047f88708013ff62840097fb142004ff98a10005fcc508013fd62840017eb142004ff18a10025f8c508027ff5284001ff2942000ff54a1004ff8a508023ff4284011ff2142008ff50a10047f88508003ff3284001ff1942000ff4ca10007f86508006fd6184003ffa8c2001ff9461000ffaa308007fc5184003ffa0c2001efd061000ffc8308007fd4184003dea0c2001ff1061000ffe6308007fe3184003fe98c2001ff0c61000ffe4308007fe2184003fe90c2001ff08610025fcc108013ff5084009ff2842004ff54210027f8a108013ff4084009ff2042004ff50210027f88108013ff3084009ff1842004ff4c210027f86108013ff2084009ff1042004fe88210027fa4108003f92084009fe1042004ffc4210027ee2108007fb1084009fe0842004fe04210007feca88002ff6544001bfb2a20009fd9510037fcca8800efe6544001feb2a2000bf59510037f8ca8800efc6544001be32a20039f1951002ffec888016ff644400bff3222002bf9911002ffac888016fd644400bfe3222002bf1911002ffea888017fe544400bfeaa22005ff15110007fec688002ff6344001ff31a2007bf98d10007fac688002fd6344001fe31a2007bf18d10037fea688003fe5344001fea9a2006ff14d1002ffe8688017fe434400bfea1a2005ff10d10007fec488002ff6244001ff3122000bf98910007fac488002fd6244001fe3122000bf18910037fea488003fe5244001fea922006ff1491002ffe8488017fe424400bfea122005ff10910007fe6488003fe3244001fe9922000ff0c910025fec288007ff5144003ff28a2001ff5451000ff8a288007ff4144003dfa0a2001ff9051000fec8288007fd4144003dea0a2005fd505100076a8288007fc4144003ff98a2001ff8c51000ffa6288007fc3144003ff90a2001ff8851000ffa4288007fc21440037fb022006ffd4110027fca088003fd5044009fe2822005ffd0110027fc8088017fd4044009fe2022000ffcc110027fc6088003fd3044009fe1822000ffc8110027fc4088003fa2044001fe9022000fe48110027f84088007ff1044003fd8822004ff84110027ec2088013fc1044009fa0822001fe04110
  | 1 => 0x6fe6188009feb0c4000bf58620027f8c310012fc6188029ffa8c4012ff94620007faa31004bfc5188027ffa0c4013efd0620097fc831004ffd4188001dea0c4012ff10620007fe631004bfe3188001fe98c4012ff0c620007fe431004bfe2188001fe90c4012ff08620025fcc110013ff5088009ff2844004ff54220027f8a110013ff4088009ff2044004ff50220027f88110013ff3088009ff1844004ff4c220027f86110013ff2088009f79044000fec8220027fe2110013fc1088001ffb2a4000bfd952008ffcca9000efe6548001feb2a4000bf5952008ff8ca9000efc6548021ffb224010bfd91200077ec890002bf6448021ff3224002bf99120087fac890042fd6448021fe3224002bf1912008778c89000abc6448021ffaa24010ff95120087faa890043fc5448001ffb1a4000bfd8d20007fcc69001efe6348001feb1a4000bf58d20007f8c69001efc6348023ffa9a4000ff94d20007faa690047fc5348021ffa1a4010ff90d20087fa8690043fc4348023ffa924000ff94920007faa490047fc5248021ffa124010ff90920087dc8490043fd4248021f6a124010ff10920007fe6490003fe3248001fe9924000ff0c920007fec290002ff614801fff30a4001bf98520007fac29003ffc61480037e30a4011ffd452007ffca290003fd514801ffe28a4010ffd05200877e829003ffe4148021fea0a4000ef5052007ff88290003ff314801fff18a4000ff4c52007ff86290003ff2148001f790a400fff88520007fa4290003ed214801ffe10a4011ffd4120027fca090003fd5048009fe2824010ffd0120027fc8090043fd4048009fe2024000ffcc120027fc6090003fd3048009fe1824000ffc8120007f64090013fe2048009f7102400fffc4120027f82090013ff65080097fb284004ff9942001dfcca10013fd65080017eb284004ff19420025f8ca10013ff64080097fb204004ff99020015fcc810013fd64080197eb204004ff19020025f8c810033ff5408019ff2a0400cff55020067f8a810013ff63080097fb184004ff98c2003dfcc610013fd63080017eb184004ff18c20025f8c610037ff5308001ff2984000ff54c2006ff8a610033ff4308019ff218400cff50c20067f8861003afe620801bffa90400aff94820007faa41002bfc5208019ffa10400aff90820067fa841002bfc4208001ff990400aff8c820007fa641002bfc3208009ffb084004ff9842000dfcc210013fd61080017eb084004ff18420025f8c210037ff5108017ff2884000ff5442005ff8a210033ff4108019dfa08400bff90420067fa8210003bd4108017fe2084000ffcc42005ffc6210003fd3108017fe188400affc842005ffc4210003fd2108015fe1084004bf98020027fea010013fe5008009fea804004ff14020027fe8010013fe4008009fea
  | 2 => 0x3003ffaa61801ffc530c00fffa186007ff90c3003ffa861801ffc430c009ffb106004ff98830005fcc418013fd620c0017eb106004ff188300cffea418003fe520c001fea906019ff148300c7fe8418063fe420c031fea106018ff1083003ffe641801ffe320c00ffe9906007ff0c830027fec218013fe610c0037f3086004ff58430005fac218013fc610c0097e3086019ffd44300bffca218003fd510c02ffe2886018ffd04300c77e821805ffe410c031fea086000ef504300bff8821801fff310c00fff1886007ff4c43003ff86218003ff210c02fff1086000ff484300bff84218012fe600c009ffa806004ff94030027faa018013fc500c009ffa006004ff90030027fa8018013fc400c009ff9806004f7cc030027fc6018013fa300c009fe9806004f74c03003ff26018013ff100c009fe080600affd9720005fecb9005bfe65c80077f32e4000df9972001cfccb90003fd65c80017eb2e4000df59720004facb9002bfc65c80077e32e400affd9320075fec99003bfe64c80057f326400eff59320075fac99002bfc64c80057e326400effd5320077fca99003bfd54c801dfe2a6400affd8f20005fec790003fe63c800f7f31e4000ff58f20005fac79002bfc63c800f7e31e4016ffd4f20007fca790003fd53c802dfe29e400effd0f20077fc879003bfd43c801dfe21e4016ffd4b20057fca590003fd52c8015fe296400effd0b20057fc859003bee42c801dfea16400efb50b20057f88590003ff32c8015ff1964000ff4cb20057f8659002bff61c802bff30e4001bf98720007fac390002fd61c8015fe30e4001bf187200b7fea390057fe51c8001fea8e4015ff14720077fe839003bbf41c802bff20e400eff507200077a8390057fc41c8001ff98e4015ff8c720007fa6390057fc31c8015ff90e4000fbc87200affc4390003fd21c8001f690e400aff087200b7fea190013fe50c8001fea864004ff14320077fe8190013fe40c801dfea064004ff10320007fe6190013fe30c8001fe9864004ff0c3200affe2190013fc10c8009ffb2c4004bfd9620027fccb1000efe6588009bf32c40039f99620027facb10002fd6588009beb2c40009f59620027f8cb10012fc6588009ffb244004bfd9220027fcc91000afe6488009feb244013bf59220027f8c910012fc6488027ffaa44013ff9522009ffaa91004ffc5488009ffb1c4004bfd8e20027fcc71001efe6388009ef31c4000b798e20027fac710002fd6388009eeb1c4000b758e20027f8c710012fc6388029ffa9c4000ff94e20007faa710053fc5388027ffa1c4013ff90e2009ffa871004ffc43880217eb144014ffd4a20007fca510003fd5288029fe2944013ffd0a2009ffc851004ffd4288027fe2144000ffcca20007fc6510003fd3288001fe1944004ffd8620027fcc31000
  | 3 => 0xea866004ff1433010ffe8198013fe40cc043fea066004ff10330107fe2198013fc10cc009ffb2c6004bfd9630027fccb1800efe658c009feb2c6000bf59630027f8cb18012fc658c009ffb246004bfd9230027fcc91800afe648c009feb24601ebf59230027f8c918012fc648c03dffaa4601eff952300f7faa91807bfc548c0377eb1c601fffd4e3003ffca718003fd538c00ffe29c601effd0e3003ffc871807bfd438c00ffe21c6004ffd8a30027fcc518002fe628c009feb146000bf58a30027f8c51807fff528c001ff2946000ff54a300fff8a51807bff428c03dff214601eff50a300f7f8851801fff328c001ff1946000ff4ca3003ff86518013ff618c009ff30c6001bf98630027fac318002fd618c009fe30c6004bf186300fffea318077fe518c001fea8c601dff146300f7fe831807bbf418c03bff20c601eff506300077a8318077fc418c00fff98c601dff8c630007fa631801ffc318c001ff90c601dff88630007fa4318077fc218c0097f3046004ffd4230027fca118013fd508c009fe2846004ffd0230027fc8118013fd408c009fe2046004ffcc230027be611801ffb308c009ff8846004ff04230007feca98002ff654c001bfb2a60009fd95300e7fcca9800efe654c001feb2a6000bf595300e7f8ca9800efc654c001be32a60039f195300dffec89806eff644c001dfb226000afd91300dffcc89800afe644c037feb22601bbf591300dff8c89800afc644c037de3226002af191300dffea89806ffe544c037feaa2601bff151300e7fea69801ffe534c001ef29a6000ff54d30007baa69801ffc534c037ffa1a6007ff90d300dfbc869806ffd434c037eea1a6007ff10d30007fec498002ff624c001ff3126000ff58930007f8c498002fc624c039ffa926000ff94930007faa498073fc524c037ffa12601bff909300dffa849806ffc424c00fff9926000ff8c930007bc6498003fd324c00ffe1926000f70c930007fec298002ff614c035ff30a6001bf98530007fac29806bfc614c0037e30a601cffd45300d7fca298003fd514c035fe28a601bffd05300df7e829806bfe414c037fea0a6000ef505300d7f8829801fff314c001ef98a601aff8c530007fa6298003dd314c00ffe18a6000ffc85300d7fc4298003fd214c035fe10a601cffd4130027fca098003fd504c009fe282601bffd0130027fc809806ffd404c009fe2026007ffcc13003ff66098013fe304c009ef182601affc4130027f82098013ff650c0097fb286004ff9943001dfcca180137e650c0073f3286004ff59430005faca180137d650c0013eb286004ff19430025f8ca18013ff640c0097fb206004ff99030015fcc818013fd640c0317eb206004ff19030025f8c818063ff540c031ff2a06018ff550300c7f8a81801efe630c00fffa986007ff94c
  | 4 => 0xffc529404dffa14a026ff90a50137fa852809bfc4294001ff994a000ff8ca50007fa6528003fc3294009ffb0ca004ff9865000dfcc328013fd61940017eb0ca004ff18650025f8c32800fff5194007ff28ca025df9465001ffaa32800ffc5194007be28ca026ffd06501377e8328097fe419404dfea0ca000ef5065012ff88328003ff319404bff18ca000ff4c65012ff86328003ff219404bff10ca000ff4865012ff84328012fe6094009ffa84a004dfd425001ff6a128013fc5094009fc284a004ffd0250027fc8128013fd4094009fe204a004ffc4250027f82128012ff6554049ffb22a024bfd9150127fcc8a800afe6454049feb22a024bf59150127f8c8a800afc6454007ffaa2a003dfd515001ffca8a800ffd5454049beaa2a003ff15150007fec6a8002ff6354001ff31aa000ff58d50007f8c6a801efc6354007ffa9aa003dfd4d5001ffca6a800ffd5354001bea9aa003ff14d50127fe86a8093fe4354049fea1aa024ff10d50007fec4a8002ff6254001ff312a000ff58950007f8c4a8002fc6254007ffa92a003ff94950006fca4a800ffd5254007fe292a003df14950127fe84a8093fe4254049fea12a024ff10950007fe64a8003fe3254001fe992a000ff0c950007fec2a8002ff6154047ff30aa001bf98550007fac2a808ffc61540037e30aa003ffd455001efea2a800ffe5154007fea8aa000df5455001ff8a2a8093ff4154049dfa0aa023ff90550127fa82a8003bd4154047fe20aa000ffcc55011ffc62a8003fd3154047fe18aa000ffc855011ffc42a8003fd2154047fe10aa003bfd815001ffea0a800ffb5054009ff282a004df94150027f8a0a80137c5054007fc282a024ffd0150027fc80a8093fd4054009fe202a023ffc4150027f820a801fff65cc00f7fb2e6007ff9973001dfccb9801ffd65cc0017eb2e6007ff1973003df8cb9801fff64cc00f7fb266007ff99330015fcc99801ffd64cc0437eb266007ff1933003df8c998087ff54cc043ff2a66021ff5533010ff8a99801fff53cc00fff29e6007f794f3003ffaa798003dd53cc00ffe29e6007ffd0f3003ffc879801fde43cc00ffea1e6021f750f3003ff8879801fff62cc00fff3166000bf98b3003ffac598002fd62cc00ffe3166022ffd4b30007fca598003fd52cc045fe2966021ffd0b3010ffc8598087fd42cc043fe2166007ffccb3003ffc6598003de32cc00ffe9966007ff0cb3003fb8659801fff61cc00fff30e6001bf9873003ffac398002fd61cc00ffe30e6001bf18730117fea398083fe51cc001fea8e6020ff1473010ffe8398087bf41cc041ff20e6021ff507300077a8398083fc41cc00fff98e6007f7cc73003ffc639801ffd31cc001ee98e6007ff0c730007fe4398083fe21cc001fe90e6020ff08730117fea198013fe50cc001f
  | 5 => 0x13115ffc80988affd404c457fe2026201ffc413100ff8209882bff65c84017fb2e422aff9972101dfccb90803fd65c84017eb2e420aff1972101df8cb9082bff64c84537fb264229ff99321015fcc9908a7fd64c84537eb26420aff19321015f8c9908a7ff54c8453ff2a64229ff5532114ff8a99082bff63c84017fb1e4200ff98f2103dfcc790803fd63c84017eb1e420aff18f2103df8c7908abff53c8401ff29e4200ff54f21157f8a7908a7ff43c8453ff21e4229ff50f2114ff88790806fe62c8455ffa96420aff94b21007faa59082bfc52c8453ffa16420aff90b2114ffa859082bfc42c8401ff996420aff8cb21007fa659082bfc32c84037eb0e4201ffd472100ffca390807fd51c8403fe28e4201ffd072100f7e8390807fe41c8403fea0e4201ef5072100ff88390807ff31c8403ff18e4201ff4c72100ff86390807fe21c8403f710e4201fd8872100ff84390807ec21c8415ffb064200ff98321025fcc190803fd60c84017eb06420aff18321157fea1908abfc50c8453ffa064229ff9032114ffa81908a7fc40c8403ff8864201ff04321007feca90802ff6548401bfb2a42009fd9521147fcca9080efe6548401feb2a4200bf59521147f8ca9080efc6548401be32a42039f1952113ffec89089eff644844fff3224202bf9912113ffac89089efd644844ffe3224202bf1912113ffea89089ffe544844ffeaa24227ff15121007fec690802ff6348401efb1a4200b7d8d21007fcc69081efe6348401feb1a4200bf58d21007f8c69081efc6348401ee31a4200b718d21147fea690803fe5348401fea9a4228ff14d2113ffe869089ffe434844ffea1a4227ff10d2100dfec4908a3ff5248401ff2924200ff54921147f8a49089fff424844fff2124227ff5092113ff88490803ff3248401ff1924200ff4c921007f86490806ff6148403ffa8a4201ff9452100ffaa290807fc5148403ffa0a4201efd052100ffc8290807fd4148403dea0a4201ff1052100ffe6290807fe3148403fe98a4201ff0c52100ffe4290803f72148403ff10a4201fb8852100ff84290807ec2148403fa10a4200ffd8121005fec090803fe6048401feb024200ff18121025f8c0908a3ff5048451fe2824227ffd012113ffc809089ffd404844ffe2024201ffc412100ff8209080efd6594009ffb24a004bfd9250027fcc92800afe6494009feb24a026bf59250027f8c928012fc6494007ffaa4a003ff9525001ffaa92800ffc5494009ffb1ca004ff98e5003dfcc728013fd63940017eb1ca004ff18e5001ffea72800ffe5394001bf29ca003ff54e5001ff8a72800f7c539404dffa1ca026ff90e50137fa872809bfc4394009ffb14a004ff98a50005fcc528013fd62940017eb14a004ff18a5001ffea52800f7f5294007ff294a003ff54a50006faa528
  | 6 => 0x1fe302a204bf1815101ffea0a880f7f5054407fe282a230ffd0151187fc80a88c3fd4054461fe202a201ffc415100ff820a8803bf655045fdf32a8200ef5954117f78caa0803bf6350401df31a8200ef58d4100778c6a08bfbf5350401df29a8200ef54d4117f78a6a0803bf6250401df3128200ef5894100778c4a08bfbf5250401df2928200ef5494117f78a4a0803bf3250401df1928200ef4c9410077864a0807bf61504035fb0a8202edd854100f7ea2a0807be5150403dea8a8201ef1454100f7c62a0807bc3150403df10a8201ef085410077ec0a0803be6050401deb028200ef1814117f7ea0a08bfbc5050403df8828201edc414100f7820a081fff65cc40f7fb2e6207ff9973101dfccb9881f7e65cc4073f32e6207ff59731005facb9881f7d65cc4013eb2e6207ff1973103df8cb9881fff64cc40f7fb266207ff99331015fcc99881ffd64cc45b7eb266207ff1933103df8c9988b7ff54cc45bff2a6622dff5533116ff8a998806fe63cc40fffa9e622ef7d4f3103ffca79881ffd53cc40ffe29e6207f714f3103ffe879881ffe43cc40ffea1e6207ff10f3103ffec59881ffe62cc4017f3166207ff58b31005fac59881ffc62cc45dffa966200ff94b31007faa5988bbfc52cc45bffa16622dff90b3116ffa85988b7fc42cc40fff9966207f7ccb3103ffc659881ffd32cc401ee9966207ff0cb3100dfac398807ff51cc403ff28e6201ff5473100ff8a398807ff41cc403dfa0e6201ff9073100ffa8398807bd41cc403fe20e6201ff8c73100fbc6398807f631cc403fe18e6201f70c73100ffc4398807fc21cc40fffb066207ff98331025fcc19881ffd60cc4017eb066207ff18331177fea1988bbfc50cc45bffa06622dff9033116ffa81988b7fc40cc403ff8866201ff04331007feca98802ff654c459ff32a6203bf99531007faca98802fd654c459fe32a6203bf1953115ffec8988aeff644c457ff3226202bf9913115ffac8988aefd644c457fe3226202bf1913115ffea8988affe544c457feaa2622bff1513100dfec6988b3ff534c459efa9a6207ff94d31007faa69881ffc534c459ee29a622bffd0d3103ffc86988affd434c40ffe21a6200ffd8931005fec498803fe624c401feb126200ff18931005f8c4988b3ff524c401ff2926200ff54931167f8a4988afff424c457ff212622bff5093115ff8849881fff324c401ef9926200ff8c931007fa6498803dd324c40ffe1926201bfd853100ffea298807fe514c403fea8a6201ff1453100ffe8298807bf414c403ff20a6201ff5053100f7a8298807fc414c403ff98a6207fdcc53100ffc6298807de314c403fe18a6201f70c53100fe86298807fe214c403fe10a6200ffd8131005fec098803fe604c401feb026200ff18131025f8c0988b3ff504c459fe282622bffd
  | 7 => 0x990dbff644c86d7fb226436ff99132015fcc8990dbfd644c86d7eb226436ff19132015f8c8990dbff544c86dff2a26436ff551321b7f8a8990dfff534c80fff29a6400ff54d3203ff8a6990dbff434c80fff21a6436ff50d3203ff886990dfff524c801ff2926400ff549321bff8a4990dbff424c86dff2126436ff509321b7f8849901fff324c80ff79926400ff8c932007bc6499003ff614c8017fb0a6435ff9853200dfcc299003fd614c86bfe30a6401bf185321bffea2990d7fe514c86bfe28a6436ffd05321b77e82990d7fe414c86dfea0a6435ff105321affc629901ffc314c86bff10a6435ff08532007fec099002ff604c801ff3026400ff58132007f8c099012fc604c86fffa826437ff141321b7fe80990dbfe404c86dfea026436ff101321affe20990d7fc104c815ffb286407bfd943203ffcca1900efe650c80fbf32864039f9943203ffaca19002fd650c80fbeb2864009f59432057f8ca1901efc650c815ffb206407bfd903203ffcc81900afe640c80ffeb206432bf59032057f8c81901efc640c865ffaa06432ff95032197faa8190cbfc540c80f7f3186407ffd4c3219fbea61901ffe530c80ffea986407ff14c3203fb8a61901fff430c80fff2186407ff50c3203ff886190d2fe620c867ffa90640aff94832007faa41902bfc520c865ffa10640aff90832197fa841902bfc420c80fff9906407f7cc832057fc641901fee320c80ffe9906400f74c83203fda641902bff610c80fff3086401bf9843203ffac219002fd610c815fe3086401bf1843219ffea2190c7fe510c863fe2886432ffd04321977e82190c7fe410c865fea086431ff1043203ffc62190c7de310c80ffe1886407f70c43218ffc421902bfc210c815ffb006407ff98032025fcc01901ffd600c8017eb00640aff1803219ffea0190cffc500c865ffa006432ff90032197fa80190cbfc400c863ff8806431ff0403200dfecaa88c3ff64544617fb22a230ff99151015fcc8a88c3fd64544617eb22a230ff19151015f8c8a880fff5454407ff2a2a203ff5515101ff8a8a8803ff63544017fb1aa200ff98d51007fac6a8803fc635440f7e31aa203ffd4d5101ffca6a88037e5354407fea9aa203ff14d5101ef8a6a88c3ff4354461ff21aa230ff50d51187f886a8803ff62544017fb12a200ff98951007fac4a8803fc62544017e312a203ffd495101efea4a880ffe5254407fea92a200df5495101ff8a4a88c3ff4254461ff212a230ff50951187f884a8803ff3254401ff192a200ff4c951007f864a8806ff6154403ffa8aa203fdd455100ffca2a88077e5154403fe28aa201df1455100fe8a2a8807ff4154403dfa0aa201ff9055100ffa82a8807fc4154403ff18aa201ff0c55100ffc42a8807fc2154401ffb02a200bfd8151007fcc0a8803fd605440
  | 8 => 0xf98d52007fac6a9003fc635480f7e31aa400f718d52005b8c6a900fff5354807bfa9aa403ff94d5201ffaa6a90037d5354807fe29aa43effd0d521f7fc86a90fbfd435487dfe21aa403bfd895201ffea4a900fef5254807ff292a400df9495201ff8a4a900f7c5254807f6292a43effd09521f7fc84a90fbfd425487dfe212a400ffd8552005fec2a90f7fe61548037f30aa400ff585521eff8c2a9006fc6154807ffa8aa403dfd455201ffca2a900ffc515487dffa0aa43eefd05521effc82a90fbfd415487bfe20aa43dff8c5521eff862a90f7fe215487bfe10aa400ffd8152005fec0a9003fe6054801feb02a400ff18152025f8c0a900fff5054807fe282a403df141521f7fe80a90fbfe405487dfea02a43eff101521effe20a90f7fc105480fffb2e6407bfd973203ffccb9900efe65cc80ffeb2e6400bf5973203ff8cb9901efc65cc80fffb266407bfd933203ffcc99900afe64cc80ffeb26643bbf5933203ff8c99901efc64cc877ffaa6643bff953321dffaa9990effc54cc80fffa9e6407ff94f3203ffaa79901ffc53cc80fffa1e6407ff90f3203ffa879901ffc43cc879ffa966400ff94b32007faa5990f3fc52cc877ffa16643bff90b321dffa85990effc42cc80fffb0e6407ff9873200dfcc39901ffd61cc8017eb0e6407ff1873200df8c3990f3ff51cc875ff28e643aff147321dffe83990efbf41cc875ff20e643bff507321d7f8839901ffe31cc80ffe18e643aff887321d7f8439901fff60cc80fff3066404bf9833203ffac199002fd60cc80ffe306643cffd43321e7f8a1990efff40cc877ff206643bff503321dff881990ebff10cc875fe086640affd9632005fecb190e7fe658c8077f32c6400ff59632005facb1902bfc658c8077e32c640affd92321a5fec9190d3fe648c8057f3246434ff592321a5fac91902bfc648c8057e3246434ffd52321a7fca9190d3fd548c869fe2a46436bf58e321cffea7190e7df538c80fff29c6400ff54e3203ff8a7190e7dc538c869ffa1c6407ff90e321a7fa871901ffc438c80f7f3146439ffd4a32057fca519003fd528c815fe2946434ffd0a32057fc85190d3fd428c815fe2146407ffcca32007be651901fef328c815ffb0c6438ff9863200dfcc319003fd618c8017eb0c640aff1863200df8c3190e7ff518c871ff28c6438ff146321a7fe83190d3bf418c871ff20c6434ff506321c7f883190e3fe318c871ef18c6407ff0c6321c7b863190e3fe218c815fe10c640affd8232007fcc119012fe608c801feb046400bf58232057f8c1190e7ff508c873fe2846434ffd02321a7fc81190d3fd408c869fe2046438ffc42321c7f82119003ff654c8017fb2a6400dfd9532004feca990dffe654c8077f32a6400ff59532005faca990dffc654c8077e32a6400df1953201cf8ca
  | 9 => 0xc0fee29ca607ffd0e5303ffc872981ffd4394c0ffe21ca607ffd8a5303ffcc529802fe6294c0ffeb14a600bf58a5303ff8c52980fff5294c07fe294a603df14a53227fe8529913fe4294c89fea14a644ff10a5303ffec32981ffe6194c037f30ca607ff58653005fac32981ffc6194c037e30ca603ffd465301efea32980ffe5194c07fe28ca644ffd06532277e832990ffe4194c89fea0ca643ff1065303ffc632981ffc3194c87ff10ca643ff0865303ffec12981ffe6094c097f304a607ff58253005fac12981ffc6094c07ffa84a603ff1425301ef8a129913ff4094c89ff204a644ff50253227f8812990fff1094c87fe084a607bfd9553217fec8a990aff6454c85ff322a602bf99153217fac8a990afd6454c85fe322a602bf1915301ffea8a980ffe5454c07feaa2a603ff1515301dfec6a980fff5354c07efa9aa607ff94d5303efca6a981ffc5354c0fbe29aa603f714d53217fe86a981ffe4354c85fea1aa607ff10d53007fec4a9802ff6254c01ff312a600ff58953007f8c4a9802fc6254c07ffa92a603dfd495301ff8a4a990bff4254c85ff212a642ff50953217f884a9803ff6154c017fb0aa641ff9855300dfcc2a9803fd6154c83fe30aa601bf1855301ffea2a980ffe5154c83bf28aa603ff1455301ef8a2a990bff4154c85dfa0aa641ff90553217fa82a9907fc4154c83ff18aa607ff0c55320ffc42a9907fc2154c01ffb02a600bfd8153007fcc0a9803fd6054c01fe302a604bf1815301ffea0a980f7f5054c07fe282a642ffd0153217fc80a990bfd4054c85fe202a641ffc415320ff820a980efd6594815ffb24a440bfd9252207fcc92900afe6494881feb24a440bf59252057f8c92900afc6494807ffaa4a403ff9525201ffaa92900ffc5494815ffb1ca400ff98e5203dfcc729003fd63948017eb1ca40aff18e5201ffea72900ffe5394801bf29ca403ff54e5201ff8a72900f7c5394881ffa1ca440ff90e52207fa8729103fc43948077f314a403ffd4a5201efea52900fef5294815fe294a403fb14a52207fe852902bfe4294881fea14a40aff10a52057fec3290fffe61948037f30ca400ff58652005fac32902bfc61948037e30ca403ffd465201ffca3290ff7e5194807fe28ca403df14652207fe8329103bf419487fff20ca440ff506521fff883290fffe319487ffe18ca43fff88652057f8432902bff6094801ff304a404bf98252007fac129002fd6094815fe304a403ffd425201efea12900ffc5094881ffa04a440ff90252207fa8129103fc409487fff884a43fff0425201dfecaa90fbff645487d7fb22a43eff99152015fcc8a90fbfd645487d7eb22a43eff19152015f8c8a900fff5454807bfaa2a403ff9515201ffaa8a90fb7d5454807fe2a2a400ffd8d52005fec6a9003df63548016fb1aa400f
  | 10 => 0x680000100200200000000180a80000100100000200580300800000000000d00000000200000000400100100480000080480000580000080200000001600700200280380080001100000000680200000500380780080180500081500380180100680100680280a00500900000280700080600680000000200080680380300080180a00280a80500000100080000680080200080600580200380000000180000000280080600a80700600300180000100280000101600000200100480080080000200400000000100480180380100000100000080280580000000100580100000500880200080780100200180700000600100200300300100680080000100080000100280280000580000680080280080080080080500000880000480000000c00200400380000000080080b00100601200200300000480380000000280000100380400300080200200100080000000080000100780080000000000300000080000200000000080d00000080080000080080000000680c80380180000780100480000380400380301180000380000080000000000a80000300000f00200300480380000700580000180500000000180000e00000280080000000000180400980201180300280000380080b80000080480000300180280180f80780880000080e00400880000280080200000000200100400580d80000780200180500000280180200600080080080000080180200380780000000300700000080480200580300400080001381700000000100000000001200000100400180000000000100100000280880700000180400100780180780100c80180800080500280300000180880900000300800e00480080200100180000180480280080000200000000000080180400000000180000080200280000000200401400000480180200680000300180080081500000480080000200000000100000100500000000100000080200000180000300000001300400080180100080080000380000780200000080280100680e00880000080980680080180180000a00481600180600400200100800001100180100100280280000300080380080080000000200700a80000200100080c00100100000000300000280100500100180200400000000280400b80080200000100080200200380400900000000180100000100200180600380380080980480000080100280000000100700100d80500200100281300500000100080080280180580480580000000680000b00000600380100280000000380c00200480302380efd6594c0fffb24a607bfd925303ffcc92980afe6494c0ffeb24a644bf5925303ff8c92981efc6494c07ffaa4a603dfd525301ffca92980ffd5494c89beaa4a603ff1525303dfcc72981fff5394c0fbfa9ca603f7d4e5301ebea72981ffc5394
  | 11 => 0x10e3f90948dd0075000037824060625e20980d002c11e8c5c0000002a900010787712c38000e920001de951c0001920000da8c441da179a1050dc42031989207fa32140b86d90020001411744b7833f27d80708c0687126800061a0000001790c884e10001aec1ba00025700000000003d7801ca3a3c80000b142d63350bd98dc0005e03a406f82427503e000000000333260c040006f00c300006fa41b0000e7c2141e8385a0c448a00020500a84d41f20000000d443cc3429c0065078c0001e001ac26d05000006d20000000f991182ce433089c1b483b39b972c00010b30213bc6847400cb9e287646300c800f899418132a91240003ef0001db899e5912b61494e082330000254d6c000000057800033342e8a90522000000126807871d4169714ccc68d32f10f80000000000d78fc85af02080000005922179964ff46d400007f00001ac08480000000000001c6c9162ec03b1fa400000033718f47567171c605190ee76d02f0c6cb3081402a1e98c105222cf92540005ca06807d89fc06243e8af8e4e00030f8524d8664108f90e0e8c0fc41b9020a267e539914cc3ce289000000022063e09914d8dfe8041668bf838269b000131400000022e92100007da4290000aaa5d42840d680000df3b980000a62202289298efa56809409e043a2b13a503d47b815943a8258fda1dd3cea0f8a7821a2f78af400087e452114ceba51816e80000000001c400005a4000346201c6d80002e09064baa00016a82240004d00000000f9052d03e98f0b2e1f8068800015c3ae35b80003be0000e58000000378000162006c52b411916c78887a00009990e83a612790c058604a28a83e8bf84980000efc0001673d91444b0c7f10000000f5a33e45a129c5524b52d0090444c64b1c1800000034506c883821e82503e1a549f8479008a1900088323769b685c243b0aa0c3914270a3fb1670ee405d2a797d8c946ae4499148f704d41dc17ec5a039c2c780086ae0000df88d800000025c0000000000000000094800020081b0f9e3610f704b089e22324513b44788b500c8ff02680fb3dd061c63a145076000009c07920e976c15600030089b0d5a5a514a8980cba11e3be0294ae00000189de43ac7f045d2070b6431820d22683541a723b1f246ec472206a1ed11e00000180080180000000100080000000880180080180100000000000680100080080000380380400200800800000080300000200080000080000000380000680300000700000000000980180080080100480380300380100680180080100000f80000180000500080080080e80180000180700300100200080000200400080300380000580000000880080100080000000080380180380600600300780380080100000000380100800c00180900000080080000000b806000805800801801801
  | 12 => 0x95187fe38e33ba154b5842600001709e455723f020cd26000069805c03600000020741746880001764204000420057cbe43f20001bf45365bd17a11b4ecc8363d886bc00055415621cc40600004e9344c9039000018e000015015a8d38e1873318300a40000002b982c4e6032310297cc00006f000000007000022e08709580001938e350e245e0898000d9a0003cd810c0000662fc00007b084803d8000f0c0651bf00007583721ed9f60cf611c086215c79a035000068066411a0bf8000a3200027896d8bcc2a13bb9dbc0da0001929b44dba00000006b80006aa000213800060a3128d1c24800000013e89aa4aa3f50b448ae7fd3ec80003c02240c680149bc37100000006720003cf8260f7c65f00808290d23440bd1090c866ac3830c1018e66725c8b048f855b3bd8000200286299110c5ee00000000000000002b48ea033e85c27b1c705300000de818490e8132141e2000046430a89e400004c25888d47d848023b9cfcd3a1841d38abc5980003591c3c6380002fb897836647300013a89380770f3166c78a5ce2208fe84761c90000844a420e800000004aa421308006078083d24309f4b1c88423283ac5ca4fd00000001a484f0001e78fa01a61f420300000001e093d0eac475000228072c00037280000000d500003200001dc00005901180001d000000000002cb070000000042614f4c3687f34f8000f2200014096b819232410085c11306831b794a00002d9000000036228c44a0000e9a0000000b0800000000012c0e622bf08c80000e65a92e4048c00062d3ca000000013933d118c42053811f80004886c41d799bc00000000000001360003faa06400001e33c139454479a35e0dcc00000009780000003ce00015147fc7d13b5945c7144b71679884b702492700b2515c77a00000004007eb0838b9800086d10f8f9114443627206000000001771acc1940003519a1892626f0000000e2c33c0001bd4000471261814000032a0ae8b8c1782153738000f421de36782b01ec00000020bc0000283af22786264072f897a04f48611581c687b47d316d0000af43142cc9b98f883cb09100000005aa10381ac0005c3000000000071f2b7000093c6b500006e49d20d715c04d4e0e72d2a215acb128032fd0a10ea227e1d680000000002e78888b4e3313e5a29c0000003ff934800030807202647946d83c09b8113e6f93da0000a003641098058c000000000000d3853132c1a283c80003779534d8a0000130a8cf2a1d20f5852ca1a7cd0f180002c66f70ac0158a923b6000220c3740003e0800070281e31d20e05805dd30391549521c3000190800029c14980010a04da000000000000019100003a0000202021c000657000061509408a0000000060015366000066000029d0d709663b92339a7843c4d837b066c77816000020141d4
  | 13 => 0x88222a09898f9c5841fd81207262d62db900032856011d053c4560e70b312b49ea5ed358a0a05e261a441000018400000000000005c92379d508284103399164ce24e7000160d0481791c1058800057f3dd903000045f0d9130400006a15b04045e00241a69cd8e4008811a000000077e1aa9c503480210ea93c000082c00000004ca5d3079000000000002ba10816a0001d085d000064600000000005e32881d6c0002a01e30000000138000221800085f35295f48f430f349000035a83016f975818672a1cc800030660d28090780005241749bb000042c35d000065a44c1e116d045e243250991c11e2572ac94a86ba1f534c903800000015a102c8067653d107101660000001c78fc080d3f304a80002d73c200007ec00000000000006e42b503f40006970000000000125217086475279817c1c3823679939282d90bc43513596b40007210a00ed086448f00000000000000000af02842d33ef802910a8af3bb1248f263c935f1604be003a0400000cc800019d90a41884f3000134cb264690d28684000000000000000000034709c817a3c72dd0000d2268004700010f018f255800042830b1f49408000796000158c3460b40001ec06d004b0f8979c00000035a0000c7e58510218a400039743381fc9fe1b01a4a0288d659d14680009cc1c51f899580005b10000bac12e3920000e88000161000000110200000000009120000000ded040363107851c00000030280003846540498d602228b03709af4a4e10417b18708244bd0231f0cbfe156000016ced07a408c115000051c33908a09506030001c0d0100000000e904c66703eb00006fe7742dc821800054835819e400017e37f1f7497473a03883707a46450cd0a744e265c444010093a0c53971e801468152211d1caea14e13f8b2908a09a1a984a45fe00030600004a20cf29c98907ba7b300000000000003a286310200911e80aac0000000001eb04c4000188081876024726f9f845004e33520808f5c00000009300000002a19ae42283ed00020440007f701585d40002763d5000000069807f80009ac0001dd21883440000000000f8c41100004f80002123670fe003473c26580010d60000dc1214cd03f40000000b840520be08a4e1039e2ab22b000000034b1b011522692bc800029a00033003180000000000ef800000026400000000d819a0094e2a4c605202ecc2c000000000044a0003308a3800685a05c8a0c64c38b0f504f458c0000f10000f0e000174203c00240200009d09d64050ae000084e0002b28000cfc03700000000000000001058e1a49143800008684af000045c8c247f0768cbc3f600026600002a458c3c91844c4e0003fe06a000067c17d9d5c6ce059000000000000041a0d8097c896000201800000012e0c08f1202f0001b7c0000002340d182885770f6
  | 14 => 0xf85f407246c3888e1055c3b5000000089a06921e0720a1860e05b8000c5014a00007f84166023b2008c5fa23005696989322f242300000007a82e683340006de0f780001e27970170a946e828a00015d03260003ff0418f723c31ca000069075a41c8750b485060540000ed44dd1e980000000000eba2e00001761b593dc39e0000fe80000001030c48b8000038900600000000000cf12ec00000000000004362994449d9c000854000170066e2ef42b0d98b6a7ef36c86d108e37a000000000050f36397d000072b2bc02e03786f126207d090678b00000000000db4401edc00003f0001cd400046e0491300cb60ce0fd0edce265c700022e462a3982919aa445a68f2978b6cde80001281590000294294935c1082c4000182c2d05f90000e8c70e534434176007a24202c200000000000014800000001ec968ca162c800000000000000e70000f7e2d8184800000005f2461634f1e73444b82343307ca023a1bc2e224b3a794b8ec042211613e4bae01f1d29e8c1c66c10099f542b60002649d8c00000003180006be1d942192d0e984c72e209f0d7000000007dc00080b2f6027851e58a27707c08f06a040d9024b286651f0146854e3b317c95d8ba05e9379185054c012445929514a04222804b90122750b60cac46431f0d592c86a856100000008cc6502af000000089131787fc0c87ab0f0899c0006c8319000067047d0bc133417e2160000000000000000000084a66a00000000007a9173820410a3120001b480000003e29ef4e4688713812fc63c5720c59f8c87a00027403a483e55a23d811113200f211905c0001330001d546da23830c000000029a000146c12089216a00000003df0c1000000040f2ae9ed912a52c0000000000287000000000089c04f96ace5e53500000010d8000000112cc3c4450a89cf800000041581807e04a02820270fa40001a88f3cace1f911894f90b67ee1cd80ec1e01413a70300000000459000000053b3941528a601c71d89d64ba470212c05dcebe0cb2cf1a50ff26692b880007ca00600014380008b61ea2274d7e5a102789a02982642fa81b90546d31b80000fd08533bf81e869438f324985c53e42b3540fa88305dc02486383a27391eb838441a02d32d0c6425a81f3681d0852063b00a0db916628812d059448083318b1424c122a817a8d590f2273311988000000022212500003f31f1173086e0ef000177c23a000000111c7228b70000b1c00033606080009108a80001ced0b000015d8730ef0758388000050a3952b31d10b7c7b50661718640008331820800000044d904c0001260001c14f0a0e001380006186eb2d8184c27e0fe000193c28600000000000004a34249d2cc6267d22700002aa7d740c1fe0f840002b7800000030037183d0a6e00015d09743d8000428800000000e00019b04a
  | 15 => 0x2ae59a09886446f20670000000000000000049cca67e7000000101c0000000d3cab800015921c882a00d0510e744be7e22a100010c068422308b8e4423e0000d001521d317e0c683ca6d7426800000054000000006144741888e1870062e2a9800046e89003800000005b3348000080c00043e06ed0ec3ee00020d4d4e69a24102982da00000002c0fa8148389194911442d2f120a473413b3f61bb85d4022365896c1f22920000350a06000125000000064000020fcdac10803f16fcf38000000209c6b209400017f80002aa02695451560001108d30f981d83b618d8d1251f0001aac38c70136300008b000027c0000c9c0aa09d082422c4b63f9802465c5fd4108448f8e7fb01a076c25628b2711ce0a3c6c9039112000063900005c8ada6dc1720000ac477500006d436e00017d1abc0006c212b1d887c600000015300000f800000000008a600000000000001060f546863de219800000016a000157c57249040b000026e0000f49158dd2000000000032c07814b99d421a00000000003e60af0000ddcafc7700000eec0000002471c600aa04513080000005a813b8acc00000000000003103032930000aa00002c819b4b766fb0000d40e5200040d00000000000000000c3a000000000000000045885a4c1e43a2c119886747a524ba0e81160001fb80000006fa1838d4855a57c0000d6c5bc58b0000adc0001302bd800017c5da36d910069661222d0ea80005803c180009d884429f94289b85eb019000000084b00014500007db129800047200011505bccec00000000000a20f31f380000001cd00009640005e51be06a4d9413c34086747ac75c00000009b60000728a580003d1000085cd4c7191b1045449c15332896888387264011e4098475319e9b890c63412f0807487262a3b092588e000000018d4e7a7520ad000004000037503b80160004091a2c0003050ce0b70bdc3e116598d10ca29e23103dc7f286a3161934000481123216400038500009b800042a19480004100740000fac93e00022517a8fbc000000041511a5070508000ed205a2890fd46587244551e380005160001f7087e7f40000654f4e2ed2ac126c0001360001ef03326f800000000008ad1710000a960000b707280000003359654d42365059029c0000000001d04d040001ba886099c48d26c8000de643123500003148a33c69cb0e866d528297781c4709417186511c54e07319d0f0427b25105ccc566fc33
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf620c910056ec620c91000df6710c910005f5710c910025fa700c910005f9700c91002fb77650510016b7765051002fb47650510016b47650510007b77550510247b67550510007b57550510247b47550510007b76550510007376550510247b66550510007b56550510247b46550510007346550510007b77350510007b67350510007b57350510007b47350510007b76350510007b66350510007b56350510007b46350510247b75350510007b65350510007b55350510247b45350510007b77250510007b67250510007b57250510007b47250510007b76250510007b66250510007b56250510007b46250510247b75250510007b65250510007b55250510247b45250510007b73250510007b63250510007b53250510007b43250510007b77050510007b3705051023fb6705051002fb5705051023fb47050510007b0705051000fb7605051000eb7605051000fb36050510247b7505051023fb6505051023fb4505051023fb6305051023fb4305051023fb6205051023fb4205051001cff765411000cfe765411011cfd765411000cfc76541100067f655411001e7c6554110005f7715411000df47154110007b54154110027f0105411000cfe76cc11000cfc76cc1100067f65cc1101167c65cc110006df63cc11003edc63cc11000df671cc110005f571cc110007b541cc11003cff764c11000cfe764c1100d4fd764c11000cfc764c1100057f754c1100357c754c1100067f654c1100e67c654c110005bf744c11002dbc744c110006df634c11003edc634c110005f7714c11000df4714c110007b5414c11000cfe76c811000cfc76c81100357e75c81100057d75c81100067f65c81100b67c65c8110006ef62c8110056ec62c811000df671c8110005f571c8110007b541c811005dfa7688110026fa76881100277a75881100277975881100077b6588110007786588110027da7388110027d9738811007df97288110056fa6288110056f8628811000dfa7188110025f87188110026fb6188110027f36188110097bb4188110097f24188110097b94188110237f14188110007b14188110054ff764811000cfe764811007cfd764811000cfc76481100067f654811008e7c6548110005bf744811002dbc7448110006ef6248110006ec6248110005f7714811000df47148110007b54148110027e8204811000df8764811007ef8764811000cf876481100077b6548110007786548110007bb744811022fb87448110025fb7248110027eb7248110007eb6248110056fa6248110056f86248110007e8624811022fea424811022fe94248110007f3714811000dfa714811000df8714811007ff07148110026fb6148110027f3614811007fbb414811007ff2414811007fb9414811022ff14148110007b1414811007feb214811007fe92148110
  | 1 => 0x4d100067f6594d1001e7c6594d100375f5394d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d1001e7c6554d100067f65d89100067c65d891001cfe75d8910004fd75d891001cfc75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d891003cfe73d8910004fd73d8910006ef42d8910006ec42d8910024ff71d8910024fd71d8910096bf41d8910096bd41d8910096ef21d8910096ed21d89100357e75989100057d75989100067f65989100067c6598910006ef629891007df9709891001cfe75989100567e759891001c7e7598910004fd75989100567d75989100047d7598910054fc7598910054ff7498910014fe7498910004fd7498910054fc749891003cfe7398910004fd7398910054fe72989100acfd7198910056f571989100aebf41989100aebd419891007cfd7098910056f970989100057f75589100357c75589100067f65589100067c6558910005bf745891002dbc7458910005df7358910005dc73589100adfb7058910004ff75589100067f75589100047f755891001cfe755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df735891003cfc7358910006dc735891003cdc7358910006ef725891007cff7158910006f7715891007ebf415891007ebd41589100acff7058910006fb7058910094fe76189100067f65189100067c6518910006ed621891001cfe7518910004fd7518910054fc7518910054ff7418910014fe7418910004fd7418910054fc741891003cfe7318910004fd7318910056ee7218910006ef4218910056ec4218910024ff711891000cfe7118910024fd711891000cfc711891005ebf411891005ebd4118910056ef211891005eed2118910024fe7018910056f97018910024fc7018910054ff7694910004fe7694910004fd7694910054fc76949100067f659491001e7c6594910025fa7094910005f97094910004ff7654910004fe7654910004fd7654910004fc76549100067f655491001e7c6554910005df7354910005dc735491003cff76cc910004fe76cc910004fd76cc91003cfc76cc9100067f65cc9101e67c65cc910006ef62cc910006ec62cc910054ff768c910004fe768c910004fd768c910054fc768c9100067f658c9101ce7c658c910006df638c91003edc638c910025fa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c9100357c754c9100067f654c9101be7c654c910054ff760c910004fe760c910004fd760c910054fc760c9100357e750c9100057d750c9100067f650c91019e7c650c910006df630c91003edc630c910006e
  | 2 => 0x12f7641d951012f3d41d95100077541d951012f7b10d95102677610d95102677410d951012f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95102667f71d951012e7e71d951012e7d71d951012e7c71d951012e7f41d951012e3f41d951012e7e41d951012e7d41d951012e3d41d951012e7c41d951012e7f31d951012e7e31d951012e7d31d951012e7c31d951012e7f21d951012e7e21d951012e7d21d951012e7c21d951012e7f70d95102667e70d951012e7d70d95102667c70d95100067f40d95102667e40d95100067d40d95102667c40d95102667e30d95102667c30d95102667e20d95102667c20d951012e7f10d95102667e10d95102667c10d95100367c655951025dfb705951012cff75595100067f7559510004ff7459510014fe7459510004fd7459510014fc7459510004ff735951003cfc7359510004ff7259510054fc725951011cff7159510006f7715951011ebf415951011ebd415951025cff7059510006fb705951012d7e76195100367e761951012c7e76195100067f64195100067e64195100067d64195100067c64195102567f611951024f3f411951024f76411951024f3d411951000775411951024e7f601951024f7b101951025776101951025774101951024f78101951003cfe76d8d100067f65d8d100067c65d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d10006df43d8d10006dc43d8d10054fe72d8d10004fd72d8d10024ff71d8d1000cfe71d8d10024fd71d8d1000cfc71d8d100eebf41d8d100eebd41d8d100eedf31d8d100eedd31d8d10024fe70d8d10024fc70d8d100357e7598d100057d7598d100067f6598d100067c6598d10006df6398d100d5f97098d100057f7558d100357c7558d100067f6558d100067c6558d10005bf7458d1002dbc7458d10005ef7258d10005ec7258d10105fb7058d10004ff7558d100067f7558d100047f7558d1001cfe7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d10054fc7258d10006ec7258d10004ec7258d100d4ff7158d10006f77158d100d6bf4158d100d6bd4158d10104ff7058d10006fb7058d100ecfe7618d100067f6518d100067c6518d1003ede6318d10006dd6318d1003cff7694d10004fe7694d10004fd7694d1003cfc769
  | 3 => 0xe7694e10004fd7694e10024fc7694e1027e7f6594e1001e7c6594e1003ede6394e10006dd6394e1004f5f5394e10004ff7654e10024fe7654e10004fd7654e10024fc7654e1001e7e6554e100067d6554e1003ede6354e10006dd6354e1001cfe7598a100567e7598a1001c7e7598a10004fd7598a100567d7598a100047d7598a10054fc7598a10054ff7498a10014fe7498a10004fd7498a10054fc7498a1003cfe7398a10004fd7398a10026ee7298a10056ee4298a10006ed4298a100aebf4198a100aebd4198a10056ef2198a100aeed2198a10024fe7098a10026fa7098a10024fa7098a10024fc7098a10026ee2098a10026fa2098a10026ec2098a10004ff7558a1001cfe7558a1001cfc7558a10004ff7458a10006bf7458a10004bf7458a10014fe7458a10004fd7458a10014fc7458a10006bc7458a10014bc7458a10004ff7358a1003cfc7358a10026ef7258a10006ee4258a10006ed4258a1007ebf4158a1007ebd4158a1007eef2158a1007eed2158a10024ff7058a10024fe7058a10024fd7058a10024fc7058a10026ee2058a10026ec2058a10054ff7694a10024fe7694a10004fd7694a10024fc7694a1001e7e6594a100067d6594a10025fa7094a10005f97094a10004ff7654a10024fe7654a10004fd7654a10024fc7654a102767f6554a1001e7c6554a10005df7354a10005dc7354a10005f77154a1000df47154a1003cff76cca10024fe76cca10004fd76cca10024fc76cca10054ff768ca10024fe768ca10004fd768ca10024fc768ca1003ede638ca10006dd638ca10025fa708ca10005f9708ca10004ff764ca10024fe764ca10004fd764ca10024fc764ca100057f754ca1004d7c754ca10005f7714ca1000df4714ca10054ff760ca10024fe760ca10004fd760ca10024fc760ca1004d7e750ca100057d750ca1003ede630ca10006dd630ca10025fa700ca10005f9700ca10025fb7648210006fb7648210007bb744821026fb87448210027eb7248210027eb6248210056fa6248210026f86248210027e8624821026fea424821026fe9424821000dfa714821000df8714821007fbb414821007fb9414821007feb214821007fe9214821001cfe76d95100367e65d9510004ff74d9510014fe74d9510004fd74d9510014fc74d95100367f54d95100067e54d95100067d54d95100367c54d951003cfe73d9510004fd73d95100367f53d95100367c53d9510054fe72d9510004fd72d95100367f52d95100367c52d9510024ff71d951000cfe71d9510024fd71d951000cfc71d951012e7f51d951012e7d51d951012ebf41d951012ebd41d9510024fe70d951000cfd70d9510024fc70d95100367f50d951024d7e76d951001c7e76d95100067f64d95100067e64d95100067d64d95100067c64d951012f3f41d9510
  | 4 => 0x4820005dc7354820004fd76cc820004ff764c8200057f754c82006d7c754c820004ff75584200067f75584200047f755842001cfe755842001cfc75584200067c755842001c7c7558420004ff7458420014fe7458420004fd7458420014fc7458420004ff735842003cfc735842000cfd7258420026f7715842005ef6515842005ebf415842005ef64158420006f5415842005ef63158420056f72158420056f42158420024ff7058420024fd7058420024fc7058420026ef2058420026fa2058420026ed2058420026f61058420026f41058420004ff7654420004fd7654420024fc765442001e7e65544200067d655442000ef66154420006f56154420006bf765042023ebe7650420006bd765042023ebc765042023ebf655042017ebe6550420006bd655042023ebc655042023ebf6350420296be6350420006bd635042023ebc6350420007af7250420007ac72504200aebe625042028dbf7150420067b7715042023ebf615042000ebe615042023fb6615042000eb6615042005ebd615042023fb56150420006b5615042000ebc6150420007bb705042023fb8705042023ebe605042023faf205042023fba205042023fad205042023fb7105042003cff76cc420024fe76cc420004fd76cc42006d7e75cc4200057d75cc42003ede63cc420006dd63cc420004ff764c420004fd764c420024fc764c42003ede634c420006dd634c420005ef724c420055ec724c42000ef6614c420006f5614c4200acff76484200057f754842006d7c7548420005df7348420005dc73484200aeee6248420025fb7648020006fb7648020004fb7648020007bb7448020287b87448020025fb7248020027eb7248020056fa6248020027ea6248020057ea5248020007e95248020287eb4248020057e84248020057ea3248020007e93248020006f96148020287bb4148020007b94148020057eb2148020007e921480200267f7559610004ff7459610014fe7459610004fd7459610014fc745961004e7f54596100067d5459610004ff735961003cfc735961004e7f5359610004ff7259610054fc725961004e7c525961011e7f515961011e7d515961011ebf415961011ebd4159610024ff7059610024fe7059610024fd7059610024fc70596100267e50596100267c5059610004ff7558e100067f7558e100047f7558e1001cfe7558e1001cfc7558e100067c7558e1001c7c7558e10004ff7458e10006bf7458e10004bf7458e10014fe7458e10004fd7458e10014fc7458e10006bc7458e10014bc7458e10026df7358e10006de4358e10006dd4358e10004ff7258e10054fc7258e100d6bf4158e100d6bd4158e100d6df3158e100d6dd3158e10024ff7058e10024fe7058e10024fd7058e10024fc7058e10026de3058e10026dc3058e1003cff7694e10024f
  | 5 => 0x7faf41c852007fad41c8520057eb70c8520025ee70c8520025ec70c8520057e870c8520056ef60c8520024fc76485200057f754852008d7c7548520006bf644852013ebc6448520005df7348520005dc7348520006f7614852000ef46148520005fb7048520025f87048520025ec764852000eec7648520024ec76485200076f75485200076c75485202adef74485202aded7448520007af64485202a7ac6448520007cf7348520007cc734852007def7148520007e77148520007e7614852000eee614852000eec614852007fe4614852007faf414852007fad4148520007eb7048520025ee7048520025ec7048520007e8704852001cff765412008cfd765412001cfc76541200067f655412001e7c6554120006bf6454120126bc6454120005ef7254120005ec7254120027e82054120004fe76cc120054fc76cc120006bf64cc12010ebc64cc120006df63cc12003edc63cc120005ee72cc120005ed72cc12003cff764c120004fd764c12003cfc764c1200057f754c12008d7c754c120005bf744c120085bc744c120006bf644c1200debc644c120006df634c12003edc634c120005ef724c120005ec724c120027d8304c120027e8204c12008d7e75c81200057d75c8120006bf64c8120076bc64c8120025ee72c8120026ef62c8120024fa76c81200577a75c81200577975c8120007bb64c812029fb864c8120025fa72c8120026fb62c8120027eb62c8120057ea42c812029fe942c8120005f971c812029fbb41c8120007b941c8120057eb21c8120007e921c8120024ff75594200267f7559420004ff7459420014fe7459420004fd7459420014fc745942006e7f54594200067d5459420004ff735942003cfc735942006e7f535942001cff7259420054fe725942001cfd7259420054fc72594200567e52594200567c5259420004ff715942000cfe715942000cfc715942006e7f5159420006bf4159420024fe7059420024fc70594200267e50594200267c5059420004ff7558c200067f7558c200047f7558c2001cfe7558c2001cfc7558c200067c7558c2001c7c7558c20004ff7458c20014fe7458c20004fd7458c20014fc7458c20024ff7358c20026df7358c20006de4358c20006dd4358c2003cff7258c20054fe7258c2003cfd7258c20054fc7258c20056de3258c20056dc3258c20004ff7158c2000cfe7158c2000cfc7158c20006bf4158c20024fe7058c20024fc7058c20026de3058c20026dc3058c2003cff7694c20024fe7694c20004fd7694c20024fc7694c2027e7f6594c2001e7c6594c2003ede6394c20006dd6394c2006f5f5394c20004ff7654c20024fe7654c20004fd7654c20024fc7654c2001e7e6554c200067d6554c2003ede6354c20006dd6354c200b4ff76548200567f65548200567c6554820005df735
  | 6 => 0xf4158d20004ff7058d20006fb7058d20004fe7618d2008d7e7518d200057d7518d20006bf6418d20006bc6418d2003ede6318d20006dd6318d2003cff7694d20004fe7694d20004fd7694d2003cfc7694d200067f6594d2001e7c6594d20006bf6494d20226bc6494d2008f5f5394d20004ff7654d20004fe7654d20004fd7654d20004fc7654d2001e7e6554d200067d6554d20006bf6454d20216bc6454d20005ef7254d20005ec7254d200a4fe769492001e7e65949200067d6594920006bf6494920206bc6494920024fc76549200067f655492001e7c6554920006bf64549201f6bc6454920005df7354920005dc7354920005fb7054920025f87054920024fe76cc920024fc76cc920006bf64cc9201debc64cc920006df63cc92003edc63cc920025fa70cc920005f970cc920004fe768c920006bf648c9201a6bc648c92003ede638c920006dd638c920024fc764c9200057f754c92008d7c754c920006bf644c9201b6bc644c920006df634c92003edc634c920005fb704c920025f8704c920004fe760c92008d7e750c9200057d750c920006bf640c920196bc640c92003ede630c920006dd630c920007cd320c92000cfe76d8520085bc74d8520006bf64d8520006bc64d852007ef661d852001cfe75d8520004fd75d852001cfc75d8520004ff74d8520006bf74d8520014fe74d8520004fd74d8520014fc74d8520006bc74d8520014bc74d852003cfe73d8520004fd73d8520024fd72d852000cfc72d8520006f751d852007ef451d852007ebf41d852007ef431d852007ef621d8520024fe70d8520024fc70d852007ef710d85200057f755852008d7c7558520005bf7458520085bc7458520006bf6458520006bc6458520005df7358520005dc735852007ef46158520004ff7654520004fe7654520004fc765452001e7e65545200067d6554520006bf6454520186bc6454520006bf7650520005be7650520006be7650520004be7650520006bd7650520005bc7650520006bc7650520004bc7650520006bf655052017ebe6550520006bd655052017ebc6550520006bf6350520296be6350520006bd6350520296bc6350520007ae7250520007ad725052007dbf7150520087b7715052007ebf615052000ebe615052000ebc615052023fae205052007fb71050520004fe76cc520004fd76cc52003cfc76cc52008d7e75cc5200057d75cc520006bf64cc52016ebc64cc52003ede63cc520006dd63cc520006f761cc52000ef461cc520004ff764c520004fe764c520004fc764c520006bf644c52015ebc644c52003ede634c520006dd634c520094fe76c8520006bf64c852014ebc64c8520005ee76c8520096ee76c85202bdef74c85202bded74c8520007af64c85202b7ac64c852007ded71c852000eee61c852000eec61c8520
  | 7 => 0x9520054fe72d9520024fd72d9520054fc72d952008e7f52d952000cfe71d9520004fd71d952000cfc71d95200067e51d952008e7c51d9520006bf41d952008cfd70d952008e7f50d952008e7c6559520005bf7459520085bc7459520006bc6459520005df7359520005dc7359520005f7715952007df4715952008cff75595200067f7559520004ff7459520006bf7459520004bf7459520014fe7459520004fd7459520014fc7459520006bc7459520014bc745952008e7f54595200067d5459520004ff7359520006df7359520004df735952003cfc7359520006dc735952003cdc735952008e7f53595200a4ff7259520006ef725952008e7c5259520004ff7159520006f77159520004f7715952000cfe715952000cfc7159520006f4715952000cf4715952008e7f5159520006bf41595200b4ff7059520006fb70595202767e50595202767c5059520085be76d9120086be76d9120014be76d9120006bf65d9120006be65d9120006bd65d9120006bc65d91202c7af72d9120087ac72d9120005bd71d9120006be61d9120006bc61d91202c7ae20d91202c7ac20d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006bc53d91202c6bf72d9120086be72d9120086bd72d9120086bc72d9120006bf52d9120006bc52d9120006bf71d9120006be71d9120006bd71d9120004bd71d9120006bc71d9120006bf51d9120006be51d9120006bc51d9120006be31d9120006bc31d9120006be21d9120006bc21d9120006bf70d91202c6be70d9120086bd70d91202c6bc70d9120006bf50d91202c6be50d91202c6bc50d91202c6be30d91202c6bc30d91202c6be20d9120086bd20d91202c6bc20d9120006bf10d91202c6be10d91202c6bc10d912003cfe76d8d20006bf64d8d20006bc64d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20004ff74d8d20014fe74d8d20004fd74d8d20014fc74d8d20006df53d8d20006dc53d8d20054fe72d8d20054fc72d8d2000cfe71d8d20004fd71d8d2000cfc71d8d20006bf41d8d20006de31d8d20006dc31d8d20085be7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d200057f7558d2008d7c7558d20005bf7458d20085bc7458d20006bf6458d20006bc6458d20005f77158d2007df47158d20004ff7558d200067f7558d200047f7558d2001cfe7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d20014fe7458d20004fd7458d20014fc7458d20006bc7458d20014bc7458d20006df7358d20004ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d2000cfe7158d2000cfc7158d20006f47158d2000cf47158d20006b
  | 8 => 0x4fd7654e20024fc7654e2001e7e6554e200067d6554e2003ede6354e20006dd6354e2008cfd7694a2001e7e6594a200067d6594a20006de6394a20006dd6394a200a76f5294a2001cff7654a20024fc7654a2001e7e6554a200067d6554a20005df7354a20005dc7354a20006de6354a20006dd6354a20005fb7054a20025f87054a201e67e65cca200067d65cca2003ede63cca20006dd63cca20025fa70cca20005f970cca201ce7e658ca200067d658ca2003ede638ca20006dd638ca2003cff764ca200057f754ca200a57c754ca201be7e654ca200067d654ca2003ede634ca20006dd634ca20005fb704ca20025f8704ca200a57e750ca200057d750ca2019e7e650ca200067d650ca2003ede630ca20006dd630ca20004ff755862001cfe755862001cfc7558620004ff7458620014fe7458620004fd7458620014fc7458620004ff735862003cfc7358620026f77158620096bf4158620096f64158620006f54158620096f62158620024fc7058620026ef2058620026ed2058620026f61058620026f41058620004ff7654620004fd7654620024fc765462001e7e65546200067d6554620006de6354620006dd6354620006bf765062023ebe7650620006bd765062023ebc765062023ebf655062017ebe655062023f3e655062017e3e6550620006bd655062023f3d65506200063d655062023ebc655062023ebf6350620296be635062023f9e63506200069e6350620006bd635062023f9d63506200069d635062023ebc6350620007af7250620007ac725062007ebd625062028dbf715062009fb7715062023ebf615062000ebe615062023fb6615062000eb66150620096bd615062023fb56150620006b5615062000ebc615062023ebe605062023faf205062023fb7105062023fba105062003cff76cc620024fe76cc620004fd76cc6200a57e75cc6200057d75cc6201767e65cc6200067d65cc62003ede63cc620006dd63cc620004ff764c620004fd764c620024fc764c6201667e654c6200067d654c62003ede634c620006dd634c620005ef724c620005ec724c62007cfd76c86201567e65c86200067d65c8620006de63c8620006dd63c8620025f870c862000cff76486200057f75486200a57c75486201467e65486200067d6548620005df7348620005dc7348620006de6348620006dd634862000ef66148620006f56148620005fb7048620025f87048620025f976c8220056f976c82200577a75c82200577975c82200277a65c82200277965c8220027da63c8220027d963c8220027ea72c8220057ea52c8220007e952c8220005f971c82202cfbb41c8220007b941c822001cfe76d952008e7e65d9520006bc64d9520004ff74d9520014fe74d9520004fd74d9520014fc74d952003cfe73d9520004fd73d952008e7c53d
  | 9 => 0xf41596200063f41596200067e41596200067d41596200067c41596200067e31596200067c31596200067e21596200067c21596200267f70596200267e70596200267d70596200267c70596200267f40596200267e40596200267d40596200267c40596200267f30596200267e30596200267d30596200267c30596200267f20596200267e20596200267d20596200267c20596200267f10596200267e10596200267d10596200267c105962003edf7598e2003ede7598e2003edd7598e2003edc7598e2003edf7498e2003ede7498e2003edd7498e2003edc7498e20006df5498e20006de5498e20006dd5498e20006dc5498e2003edf7298e2003edd7298e20006df5298e20006dc5298e20006df4298e20006de4298e20006dd4298e20006dc4298e2003edf7198e2003ede7198e2003edd7198e2003edc7198e20006df5198e20006de5198e20006dc5198e20006df4198e200069f4198e20006de4198e20006dd4198e20006dc4198e20006de2198e20006dc2198e20026df7098e20026de7098e20026dd7098e20026dc7098e20026df5098e20026de5098e20026dd5098e20026dc5098e20026df4098e20026de4098e20026dd4098e20026dc4098e20026df2098e20026de2098e20026dd2098e20026dc2098e20026df1098e20026de1098e20026dd1098e20026dc1098e20004ff7558e2001cfe7558e2001cfc7558e20004ff7458e20014fe7458e20004fd7458e20014fc7458e20026df7358e20006df5358e20006dc5358e20006df4358e20006de4358e20006dd4358e20006dc4358e20004ff7158e2000cfe7158e2000cfc7158e20006bf4158e20006de3158e20006dc3158e20024fc7058e20026de3058e20026dc3058e20006df7558e20006de7558e20006dd7558e20006dc7558e20006df7458e20006de7458e20006dd7458e20006dc7458e20006df5458e20006de5458e20006dd5458e20006dc5458e20006df7258e20006dd7258e20006df5258e20006dc5258e20006df4258e20006de4258e20006dd4258e20006dc4258e20006df7158e20006de7158e20006dd7158e20006dc7158e20006df5158e20006de5158e20006dc5158e20006df4158e200069f4158e20006de4158e20006dd4158e20006dc4158e20006de2158e20006dc2158e20026df7058e20026de7058e20026dd7058e20026dc7058e20026df5058e20026de5058e20026dd5058e20026dc5058e20026df4058e20026de4058e20026dd4058e20026dc4058e20026df2058e20026de2058e20026dd2058e20026dc2058e20026df1058e20026de1058e20026dd1058e20026dc1058e2003cff7694e20024fe7694e20004fd7694e20024fc7694e2001e7e6594e200067d6594e2003ede6394e20006dd6394e200a75f5394e20004ff7654e20024fe7654e20
  | 10 => 0x8720004ff7458720014fe7458720004fd7458720014fc7458720004ff735872003cfc7358720024fc72587200aebf4158720056f72158720056f421587200aef71058720004ff7654720004fd7654720054fc765472001e7e65547200067d6554720006bf7650720006be7650720006bd7650720006bc7650720006bf655072017ebe65507200073e655072017e3e6550720006bd65507200073d65507200063d655072017ebc6550720006bf6350720296be6350720006bd6350720296bc6350720007ae7250720007ad72507200adbf7150720077b7715072000ebe61507200aebd615072000ebc6150720007bb7050720007b870507200afb7105072003cff76cc720054fe76cc720004fd76cc7200b57e75cc7200057d75cc7201767e65cc7200067d65cc72003ede63cc720006dd63cc720004ff764c720004fd764c720054fc764c7201667e654c7200067d654c72003ede634c720006dd634c720025ed76c872000eed76c8720024ed76c87200576e65c87200576d65c8720055ef74c87202dded74c872000eee61c8720057e661c8720057e561c872000eec61c87200afaf41c87200afad41c8720025ee70c8720057ea70c8720057e970c8720025ec70c872005cff76487200057f75487200b57c75487201467e65487200067d6548720005df7348720005dc7348720005ef764872005eef76487200076f75487200076c75487200076e65487200076d65487202d5ef74487202d5ed7448720007cf7348720007cc7348720057e7714872000eee614872000eec61487200afaf41487200afad4148720025ee7048720025ec704872001cff7654320054fc765432001e7e65543200067d6554320005ef7254320055ec7254320027ea20543201167e65cc3200067d65cc32003ede63cc320006dd63cc320055ee72cc320005ed72cc32003cff764c3200057f754c3200b57c754c3200e67e654c3200067d654c320005bf744c320075bc744c32003ede634c320006dd634c320005ef724c320055ec724c3200267f7559620004ff7459620014fe7459620004fd7459620014fc74596200a67f54596200067e54596200067d54596200a67c5459620004ff735962003cfc73596200a67f53596200a67c53596200a67f5259620004ff715962000cfe715962000cfc71596200a67f51596200067e51596200a67c5159620006bf4159620024fc70596200267e50596200267c50596200067f74596200067e74596200067d74596200067c74596200067f73596200067e73596200067d73596200067c73596200067f43596200067e43596200067d43596200067c43596200067f72596200067d72596200a67c72596200067f42596200067e42596200067d42596200067c42596200067f71596200067e71596200067d71596200067c71596200067
  | 11 => 0x14fe7459720004fd7459720014fc74597200b67f54597200067e54597200067d54597200b67c5459720004ff735972003cfc73597200b67f53597200b67c5359720024fc72597200567e52597200567c5259720004ff715972000cfe715972000cfc71597200b67f51597200067e51597200b67c5159720006bf41597200b67f50597200557f76597200b67f765972001c7f76597200567f64597200067e64597200067d64597200567c64597200567f63597200567c63597200576e42597200076d42597200567f61597200067e61597200567c61597200073f41597202776e20597200576c20597200067f74597200067e74597200067d74597200067c74597200067f73597200067e73597200067d73597200067c73597200067f43597200067e43597200067d43597200067c43597200b67f72597200567e72597200567c72597200067f42597200567e42597200067d42597200567c42597200567e32597200567c32597200067f71597200067e71597200067d71597200067c71597200067f41597200063f41597200067e41597200067d41597200067c41597200067e31597200067c31597200567f21597200067e21597200567c21597200067f70597202767e70597200067d70597202767c70597200067f40597202767e40597200067d40597202767c40597202767e30597202767c30597200567f20597202767e20597200567c20597200067f10597202767e10597202767c105972001cfe75d8f200567e75d8f2001c7e75d8f20004fd75d8f200567d75d8f200047d75d8f20054fc75d8f20054ff74d8f20014fe74d8f20056be74d8f20014be74d8f20004fd74d8f20056bd74d8f20004bd74d8f20054fc74d8f20056ee72d8f2000cfe71d8f20004fd71d8f2000cfc71d8f20006bf41d8f20056f970d8f20004fd7698f200067e6598f200067d6598f20056df6398f20056dc6398f2003cff7658f200067e6558f200067d6558f20056dc6358f20004ff7558f2001cfe7558f2001cfc7558f20004ff7458f20014fe7458f20004fd7458f20014fc7458f20056df7358f20006df4358f20006dc4358f20024fc7258f20056de3258f20056dc3258f20004ff7158f2000cfe7158f2000cfc7158f20006bf4158f2003cff7694f20054fe7694f20004fd7694f20054fc7694f2001e7e6594f200067d6594f200b75f5394f20004ff7654f20054fe7654f20004fd7654f20054fc7654f2001e7e6554f200067d6554f20005ef7254f20055ec7254f2006cff7654b2001e7e6554b200067d6554b20005df7354b20005dc7354b201e67e65ccb200067d65ccb200057f754cb200b57c754cb201be7e654cb200067d654cb20057cc324cb2000cff76587200067e65587200067d6558720056f46158720004ff755872001cfe755872001cfc755
  | 12 => 0xd20594300267c20594300267f10594300267e10594300267d10594300267c105943001cfe7598830004fd7598830054fc7598830054ff7498830014fe7498830004fd7498830054fc7498830024fe7298830026ee7298830056ee4298830006ed429883003eef3298830056ec329883000cfe7198830004fd719883000cfc7198830006bf4198830026df3098830026dd3098830026ee2098830026ec2098830004ff755883001cfe755883001cfc7558830004ff7458830014fe7458830004fd7458830014fc7458830026ef7258830006ee4258830006ed425883003eef325883003eec3258830004ff715883000cfe715883000cfc7158830006bf4158830026ee2058830026ec2058830054ff7694830024fe7694830004fd769483001e7e65948300067d6594830004ff7654830004fd7654830024fc765483001e7e65548300067d6554830005df735483003ddc7354830004ff755843001cfe755843001cfc7558430004ff7458430014fe7458430004fd7458430014fc745843000cfd7358430004ff7258430054fc7258430024ff7158430026f771584300bebf41584300bef64158430006f5415843003ef7315843003ef431584300bef62158430024fc7058430026df3058430026dd3058430026f61058430026f41058430004ff7654430004fd7654430024fc765443001e7e65544300067d6554430006bf765043023ebe7650430006bd765043023ebc765043023ebf655043017ebe655043023f3e655043017e3e6550430006bd655043023f3d65504300063d655043023ebc65504300079f73504302979c7350430106be6350430006be6250430006bd625043028dbf71504300c7b7715043023ebf615043000ebe615043023fb6615043000eb661504300bebd615043023fb56150430006b5615043000ebc615043023ebe605043023f9f305043023fba305043023f9d3050430297b9305043023fb71050430054ff76c8430024fe76c8430004fd76c84301567e65c84300067d65c8430056ee62c8430006ed62c8430004ff7648430004fd7648430024fc76484300057f75484300cd7c75484301467e65484300067d6548430005df734843003ddc7348430006ee6248430006ed624843000ef66148430006f561484300b4fd75d9720054ff74d9720014fe74d9720004fd74d9720054fc74d972003cfe73d9720004fd73d9720056ee72d972000cfe71d9720004fd71d972000cfc71d9720006bf41d9720056f970d97200047d76997200567f64997200067e64997200067d64997200567c64997200567f63997200567c63997200567e62997200576e42997200076d42997200567f61997200067e61997200567c61997200073f41997202e76e20997200576c209972001cff76597200567c65597200567f7559720004ff7459720
  | 13 => 0xc530006df62cc5300d5dd71cc53000ede61cc53000edc61cc5300d79f41cc5300d79d41cc530025de70cc530025dc70cc53003edf60cc53003fdb60cc530024fc764c5300067f654c5301667c654c530006bf644c53015ebc644c530006f7614c53000ef4614c530005fb704c530025f8704c530025dc764c53000edc764c530024dc764c530005df754c530005dd754c5300075f654c530166de654c530166dc654c5300075c654c5301665c654c5302f5df744c5302f5dd744c5300079f644c5302ef9c644c530005dc724c530006df624c53003ddf714c53003fd7714c530007d7614c53000ede614c53000edc614c5300d7d4614c5300d79f414c5300d79d414c530007db704c530025de704c530025dc704c530007d8704c53003edf604c53003fdb604c530004fe76c8530004fd76c8530054fc76c85300067f65c85301567c65c8530006bf64c853014ebc64c8530005df73c853003ddc73c8530006f761c853000ef461c8530004ff7648530004fe7648530004fc76485300057f75485300e57c75485300067f65485301467c6548530006bf644853013ebc6448530005df734853003ddc734853001cff76541300e4fd765413003cfc76541300067f655413001e7c6554130006bf6454130126bc6454130005df735413003ddc73541300075d5354130027d83054130024ff75594300267f7559430004ff7459430014fe7459430004fd7459430014fc74594300ce7f54594300067e54594300067d54594300ce7c545943003cff735943003cfe735943003cfd735943003cfc735943003e7e535943003e7c5359430004ff7259430054fc72594300ce7f52594300ce7c5259430004ff715943000cfe715943000cfc71594300ce7f51594300067e51594300ce7c5159430006bf4159430024fe7059430024fc70594300267e50594300267c5059430026df3059430026dd30594300067f74594300067e74594300067d74594300067c745943003e7f735943003e7e735943003e7d735943003e7c735943003e7f435943003e7e435943003e7d435943003e7c43594300067f72594300067e72594300067d72594300067c72594300067f42594300067e42594300067d42594300067c425943003e7f325943003e7e325943003e7d325943003e7c32594300067f71594300067e71594300067d71594300067c71594300067f41594300063f41594300067e41594300067d41594300067c415943003e7f315943003e7e315943003e7d315943003e7c31594300067e21594300067c21594300267f70594300267e70594300267d70594300267c70594300267f40594300267e40594300267d40594300267c40594300267f30594300265f30594300267e30594300267d30594300265d30594300267c30594300267f20594300267e20594300267
  | 14 => 0x75d5354930024fe768c9300067f658c9301ce7c658c930006bf648c9301a6bc648c930006ef628c930056ec628c930025fa708c930005f9708c930024de768c930005df758c930005dd758c9300075f658c9301cede658c9301cedc658c9300075c658c9301ce5c658c930315df748c930315dd748c9300079f648c9303279c648c93003dde728c930006df628c930007cf628c930007cc628c930005dd718c9301c6de618c9301c6dc618c9303279f418c930025de708c930007da708c930025da708c930007d9708c930025dc708c93003edf608c93003fdb608c930024fc764c9300057f754c9300e57c754c9300067f654c9301be7c654c930006bf644c9301b6bc644c930006ef624c930006ec624c93003fcc324c930005fb704c930025f8704c93003fd8304c930005de760c93003ede760c93003ddf750c93003f5e750c930005dd750c93003f5d750c9300055d750c9300075f650c93019ede650c93019edc650c9300075c650c93019e5c650c93003ddf740c93031ddd740c9300079f640c93030f9c640c930315de720c93003fce720c930006df620c930005dd710c93018ede610c93018edc610c93030f9f410c930025de700c930025dc700c93003edf600c93003fdb600c93000cfe76d85300067f65d85300067c65d85300ddbc74d8530006bf64d8530006bc64d85300d6f661d853001cfe75d8530004fd75d853001cfc75d8530004ff74d8530006bf74d8530014fe74d8530004fd74d8530014fc74d8530006bc74d8530014bc74d8530024fd73d853000cfc73d8530054fe72d8530004fd72d85300d6bf41d85300d6f631d85300d6f421d853003cfd70d85300d6f710d85300057f75585300e57c75585300067f65585300067c6558530005bf74585300ddbc7458530006bf6458530006bc6458530005ef7258530005ec72585300d6f46158530004ff7654530004fe7654530004fc76545300067f655453001e7c6554530006bf6454530186bc64545300075e5354530006bf7650530005be7650530006be7650530004be7650530006bd7650530005bc7650530006bc7650530004bc7650530006bf65505300073f65505300063f655053017ebe6550530006bd655053017ebc65505300073c655053017e3c65505300079e73505300079d73505300079e53505300079d5350530006bf6250530006bc62505300079e32505300079c32505300d5bf71505300dfb771505300d6bf615053000ebe615053000ebc6150530297bb305053023f9e30505300d7b71050530005de76cc53003ede76cc53003ddf75cc53003f5e75cc530005dd75cc53003f5d75cc5300055d75cc5300075f65cc530176de65cc530176dc65cc5300075c65cc5301765c65cc53003ddf74cc530305dd74cc5300079f64cc5302ff9c64cc530005de72c
  | 15 => 0xf53d913035ebe53d913035ebc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006bc52d913035ebf32d913035ebc32d9130006bf71d9130006be71d9130006bd71d9130004bd71d9130006bc71d9130006bf51d9130006be51d9130006bc51d913035ebf31d9130006be31d913035ebc31d9130006be21d9130006bc21d913035ebf70d9130356be70d91300debd70d9130356bc70d9130006bf50d9130356be50d9130356bc50d913035ebf30d9130356be30d91300debd30d9130356bc30d9130356be20d9130356bc20d9130006bf10d9130356be10d9130356bc10d9130005de7694d3003ede7694d300e5dd7594d300075f6594d3001ede6594d3001edc6594d300e75c6594d3001e5c6594d3003ddf7494d3034ddd7494d300079f6494d303479c6494d300e75f5494d303475d5494d30005de7294d300e75c5294d30005dd7194d300e75f5194d303479f4194d30025de7094d30025dc7094d3003edf6094d3003fdb6094d3027f5e5094d3027f5c5094d30024fc7654d300067f6554d3001e7c6554d30006bf6454d30216bc6454d3003f5c5354d30005fb7054d30025f87054d3003fd83054d30025dc7654d3001edc7654d30024dc7654d3003ddf7554d3003f5f7554d300075f6554d3001ede6554d3001edc6554d300e75c6554d3033ddf7454d3033ddd7454d300079f6454d3032f9c6454d30005dc7254d300e75f5254d30005df7154d303375e5154d300e75c5154d3032f9f4154d30007db7054d30025de7054d30025dc7054d30007d87054d3003edf6054d3003fdb6054d300e75f5054d300067f65d89300067c65d8930006bf64d8930006bc64d893001cfe75d8930004fd75d893001cfc75d8930004ff74d8930014fe74d8930004fd74d8930014fc74d893000cfe71d8930004fd71d893000cfc71d8930006bf41d8930006ee21d8930006ec21d89300e57e75989300057d75989300067f65989300067c65989300ddbe7498930005bd7498930006bf6498930006bc6498930006ef62989300057f75589300e57c75589300067f65589300067c6558930005bf74589300ddbc7458930006bf6458930006bc6458930005f771589300d5f471589300067f65189300067c6518930006bf6418930006bc6418930006ed621893001cfe7518930004fd7518930054fc7518930054ff7418930014fe7418930004fd7418930054fc741893000cfe7118930004fd711893000cfc7118930006bf4118930006ee2118930056ec2118930004fe7694930004fd7694930054fc76949300067f659493001e7c6594930006bf6494930206bc64949300075e5394930004ff7654930004fe7654930004fc76549300067f655493001e7c6554930006bf64549301f6bc6454930005df735493003ddc7354930
  | 16 => 0x95300e67e65d9530006bc64d9530004ff74d9530014fe74d9530004fd74d9530014fc74d95300e67f54d95300067e54d95300067d54d95300e67c54d953003cfe73d9530024fd73d953003cfc73d95300e67f53d9530054fe72d9530004fd72d95300e67f52d95300e67c52d953000cfe71d9530004fd71d953000cfc71d95300e67f51d95300067e51d95300e67c51d9530006bf41d953003cfd70d95300e67f50d95300e57e76d953001c7e76d95300067f64d95300067e64d95300067d64d95300067c64d95300073c64d95300063c64d953027f5f73d95300075e43d95300075d43d95300067e61d95300067c61d95300073f41d95303777b30d953027f5e30d953027f5c30d95303777830d95300067f74d95300067e74d95300067d74d95300067c74d953027e7f73d95303767e73d95300067d73d95303767c73d95300067f43d95303767e43d95300067d43d95303767c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95303767f32d95303767c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300063f41d95300067e41d95300067d41d95300067c41d95303767f31d95300067e31d95303767c31d95300067e21d95300067c21d95303767f70d953027e7e70d95300067d70d953027e7c70d95300067f40d953027e7e40d95300067d40d953027e7c40d95303767f30d953027e7e30d953027e7c30d953027e7e20d953027e7c20d95300067f10d953027e7e10d953027e7c10d95300e67c6559530005bf74595300ddbc7459530006bc64595300e4ff75595300067f7559530004ff7459530006bf7459530004bf7459530014fe7459530004fd7459530014fc7459530006bc7459530014bc74595300fcff7359530006df7359530004ff7259530054fc7259530004ff715953000cfe715953000cfc7159530006bf4159530114ff7059530006fb70595300057e76195300e67e76195300047e76195300067f64195300067e64195300067d64195300067c64195300073c64195300063c64195300e75d731953036e7f63195300075e43195300075d43195300067e61195300067c61195300073f41195303667f60195303677b301953036f5e301953036f5c30195303677830195300ddbe76d91300debe76d9130014be76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d91303579f73d91300df9c73d9130005bd71d9130006be61d9130006bc61d913035fbb30d91303579e30d91303579c30d913035fb830d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130356bf73d913035ebe73d91300debd73d913035ebc73d9130006b
  | 17 => 0x75d5354330027da30543300267f7559630004ff7459630014fe7459630004fd7459630014fc74596300fe7f54596300067d54596300fe7f5359630004ff7259630054fc72596300fe7c5259630004ff715963000cfe715963000cfc71596300fe7f5159630006bf4159630024fc70596300267e50596300267c5059630026df3059630026dd305963001cff7654e30024fc7654e3001e7e6554e300067d6554e30005fb7054e30025f87054e3003fdb3054e3001cfe7598a300567e7598a3001c7e7598a30004fd7598a300567d7598a300047d7598a30054fc7598a30054ff7498a30014fe7498a30004fd7498a30054fc7498a30026ee7298a30006ef5298a30056ec5298a30056ee4298a30006ed4298a3000cfe7198a30004fd7198a3000cfc7198a30006bf4198a30024fe7098a30026df3098a30026dd3098a30026ee2098a30026ec2098a30004ff7558a3001cfe7558a3001cfc7558a30004ff7458a30014fe7458a30004fd7458a30014fc7458a30026ef7258a30006ef5258a30006ec5258a30006ee4258a30006ed4258a30004ff7158a3000cfe7158a3000cfc7158a30006bf4158a30024fc7058a30026ee2058a30026ec2058a30054ff7694a30024fe7694a30004fd7694a3001e7e6594a300067d6594a30004ff7654a30004fd7654a30024fc7654a302767f6554a3001e7c6554a30005df7354a3003ddc7354a30056ee628ca30006ed628ca30025fa708ca30005f9708ca300057f754ca300fd7c754ca30006ee624ca30006ed624ca30005fb704ca30025f8704ca30004ff75586300067f75586300047f755863001cfe755863001cfc75586300067c755863001c7c7558630004ff7458630014fe7458630004fd7458630014fc7458630004ff7258630054fc7258630026f771586300eebf41586300eef64158630006f541586300eef63158630024fc7058630026df3058630026dd3058630026f61058630026f41058630004ff7654630004fd7654630024fc765463001e7e65546300067d6554630006bf765063023ebe7650630006bd765063023ebc765063023ebf655063017ebe6550630006bd655063023ebc65506300079f73506300079c73506300d6bd6350630006be6250630006bd625063028dbf71506300f7b7715063023ebf615063000ebe615063023fb6615063000eb661506300eebd615063023fb56150630006b5615063000ebc615063023ebe605063023f9f3050630297bb305063023fb7105063000cff764c63000ef6614c630006f5614c630005fb704c630025f8704c630054ff76c8630024fe76c8630004fd76c8630056ee62c8630006ed62c8630004ff7648630004fd7648630024fc76486300057f75486300fd7c7548630005df734863003ddc7348630006ee6248630006ed624863001cfe76d
  | 18 => 0xe51597301167c5159730006bf41597301167f505973003ddf7654f300cedf7654f3003f5f7554f3003f5f6554f3001ede6554f3003edc6554f3003f5c6554f303b5df7454f303b5dd7454f30005dc7254f301175f5254f30005df7154f303af5e5154f301175c5154f303a79f4154f30025de7054f30025dc7054f301175f5054f3001cfe7598b30004fd7598b30054fc7598b30054ff7498b30014fe7498b30004fd7498b30054fc7498b30024fe7398b30056ee7298b3003eef3298b30056ec3298b3000cfe7198b30004fd7198b3000cfc7198b30006bf4198b30004ff7558b300067f7558b300047f7558b3001cfe7558b3001cfc7558b300067c7558b3001c7c7558b30004ff7458b30014fe7458b30004fd7458b30014fc7458b30024fc7358b30024dc7358b3003eef7258b3003eef3258b3003edc3258b3003eec3258b30004ff7158b3000cfe7158b3000cfc7158b30006bf4158b3003edf3158b30054ff7694b3003cfe7694b30004fd7694b3039e7f6594b3001e7c6594b3003ddc7394b3039f5e5394b30004ff7654b30004fd7654b3003cfc7654b3001e7e6554b300067d6554b30005df7354b3003ddc7354b300075d5354b3003ddd768cb30006dd768cb30005df758cb30005dd758cb301cede658cb3003edc658cb30395df748cb30395dd748cb3003fce728cb30006dd628cb30005dd718cb301c6de618cb3003edc618cb3038f9f418cb30025de708cb30025dc708cb30004ff755873001cfe755873001cfc7558730004ff7458730014fe7458730004fd7458730014fc7458730024fc7358730004ff7258730054fc725873003ef77158730106bf415873003ef7315873003ef43158730106f71058730004ff7654730004fd765473003cfc76547303867f655473001e7c655473003dde73547303875e5354730006bf7650730296be7650730006bd7650730296bc7650730296bf655073017ebe6550730006bd6550730296bc65507302979e73507300079d73507302979e53507300079d5350730006be6250730006bd62507300079e32507302979c3250730105bf715073010fb77150730106bf615073000ebe6150730106bd615073000ebc61507301079f3150730107b7105073003ddf764c7300bedf764c730005df754c730005dd754c730166de654c73003edc654c73037ddf744c73037ddd744c730005dc724c730006dd624c73003fd7714c73000ede614c73000edc614c7301079f414c7301079d414c730025de704c730025dc704c730054ff76c873003cfe76c8730004fd76c8730005df73c873003ddc73c8730004ff7648730004fd764873003cfc76487300057f75487301157c7548730005df734873003ddc734873001cff765433003cfc765433001e7e65543300067d6554330005df735433003ddc7354330
  | 19 => 0x8950054fc741895003cfe7318950004fd7318950056ee521895006eed521895000cfe7118950004fd711895000cfc7118950006bf41189500247e76949503d57f74949503d57d74949500057d739495039e7c639495001d7e729495001f6e72949500067f62949500076f62949500066f62949500076c62949500057d71949501fe7e61949501fe7c61949503cf3f41949500257e70949500077a70949500077970949500257c709495001e7f609495001f7b6094950004fe76cc950004fd76cc95003cfc76cc95001d7e75cc9500057d75cc950004fe768c950004fd768c950054fc768c9500057f758c95001d7c758c950006df638c95003edc638c9501cf5f538c950004ff764c950004fe764c950004fc764c9500057f754c95001d7c754c950004fe760c950004fd760c950054fc760c95001d7e750c9500057d750c950006df630c95003edc630c95019f5f530c95000cfe76d855011ef661d8550024fd75d855000cfc75d8550004ff74d8550014fe74d8550004fd74d8550014fc74d855003cfe73d8550004fd73d8550054fe72d8550004fd72d855011ef651d855004ef551d855011ebf41d855011ef421d855001cfd70d855011ef710d855011ef461585503c5fb70585500257c765455000e7c76545500247c76545503bd7f74545503bd7d74545500057f73545503867c63545500057c72545500067f625455001d7f715455001f77715455000777615455000e7e615455000e7c615455011f74615455011f3f41545500077b70545500257e70545500257c705455000778705455001e7f605455001f7b6054550006bf7650550006be7650550006bd7650550006bc765055017f3e75505500073d755055023ebf6550550006bf6350550296bc635055017f3f53505500073d5350550006bf6250550006bc62505500073e525055017f3c525055011dbf7150550127b7715055011ebf615055000ebe615055000ebc615055011f3f515055011f3d515055025ebf605055017fbb505055023f3e505055023f3c505055017fb8505055011fb71050550004fe76cc550004fd76cc55003cfc76cc55001d7e75cc5500057d75cc550006df63cc55003edc63cc5501775f53cc550004ff764c550004fe764c550004fc764c55001d7e754c5500057d754c550006df634c55003edc634c5501675f534c550004fe76c8550004fd76c8550054fc76c85500057f75c855001d7c75c8550006f761c855000ef461c8550004ff7648550004fe7648550004fc76485500057f754855001d7c7548550005df7348550005dc734855003e7f7559730004ff7459730014fe7459730004fd7459730014fc7459730024fc735973003e7e535973003e7c5359730004ff7259730054fc72597301167f5259730004ff715973000cfe715973000cfc71597300067
  | 20 => 0x56ee620ca50006ed620ca50004ff7458650014fe7458650004fd7458650014fc7458650004ff735865003cfc73586500067e53586500367c5358650004ff7258650054fc72586500367f52586500067d5258650026f7715865012e7e515865012ef65158650036f5515865012e7c515865012ebf415865012ef64158650006f54158650024fe7058650024fc70586500267f50586500267d5058650026f61058650026f41058650006bf765065023ebe7650650006bd765065023ebc76506500073f755065017f3c755065011ebd6550650296be6350650006bd63506500073e535065017f3c5350650006be6250650006bd625065017f3f52506500073d525065028dbf7150650137b7715065023ebf615065000ebe615065023fb6615065000eb6615065012ebd615065023fb56150650006b5615065000ebc615065012f3e515065012f3c515065023ebe605065023f3f505065017fbb505065023fb8505065023fb7105065003cff76cc650024fe76cc650004fd76cc65001d7e75cc6500057d75cc65003ede63cc650006dd63cc6503775c53cc650004ff764c650004fd764c650024fc764c6500057f754c65001d7c754c65003ede634c650006dd634c6501675c534c650054ff76c8650024fe76c8650004fd76c865001d7e75c86500057d75c8650056ee62c8650006ed62c8650004ff7648650004fd7648650024fc76486500057f754865001d7c7548650005df7348650005dc7348650006ee6248650006ed6248650024fd75d8d50004ff74d8d50014fe74d8d50004fd74d8d50014fc74d8d500fede53d8d500fedd53d8d50006df43d8d50006dc43d8d50054fe72d8d50004fd72d8d5000cfe71d8d50004fd71d8d5000cfc71d8d50006bf41d8d5027e7f6598d50006df6398d500e5f97098d50005bf7458d50125bc7458d50115fb7058d5036e7f6518d5003ede6318d50006dd6318d500247c7654d503e57f7454d503e57d7454d5001d7f7354d5001f5f7354d500075f6354d5003e7e6354d5003e7c6354d500075c6354d500057c7254d500057f7154d5020e7e6154d5020e7c6154d503df3f4154d500077b7054d500257e7054d500257c7054d50007787054d5001e7f6054d5001f7b6054d50024fd75d8950004ff74d8950014fe74d8950004fd74d8950014fc74d89500a67f54d89500067d54d895003cfe73d8950004fd73d89500a67f53d89500067d53d89500a6ee52d89500a6ed52d89500a67c52d895000cfe71d8950004fd71d895000cfc71d89500a67f51d8950006bf41d89502e67e50d89502e67c50d8950006ef629895008df97098950005bf7458950125bc7458950005df7358950005dc7358950005f7715895011df471589500b5fb7058950006ed6218950024fd7518950054ff7418950014fe7418950004fd741
  | 21 => 0xe74d8121004fd74d8121014fc74d812103cfe73d8121004fd73d81210aebf41d81210aebd41d8121006fb40d8121006f840d81210aefa10d81211457e75981210057d75981210067f65981210067c6598121005de7398121005dd7398121006df6398121006dc6398121006fb60981210057f75581211457c75581210067f65581210067c6558121005bf745812113dbc7458121005df7358121005dc7358121006df6358121006dc63581210067f65181210067c6518121006df6318121006dc6318121026fa6018121006f96018121004ff7458e50014fe7458e50004fd7458e50014fc7458e50026df7358e500e6de5358e500e6dd5358e503767c5358e50006de4358e50006dd4358e50004ff7258e50054fc7258e500e67f5258e50004ff7158e5000cfe7158e5000cfc7158e500067e5158e500e67c5158e50006bf4158e50024fc7058e500267f5058e500267d5058e50026de3058e50026dc3058e5027e7f6494e503f67d6494e5001d7e7394e5001f5e7394e5027e7f6394e5027f5e6394e503767d6394e5027f5d6394e500065d6394e500057d7294e5012d7e7194e5012d7c7194e503f73f4194e5027f7a7094e5027d7d7094e50377797094e50005797094e5001e7e6094e5001f7a6094e5027f5f3094e50054ff7498a50014fe7498a50004fd7498a50054fc7498a5003cfe7398a50004fd7398a500067e5398a500b67c5398a50026ee7298a500567f5298a50056ee5298a500b6ed5298a50056ee4298a50006ed4298a5000cfe7198a50004fd7198a5000cfc7198a500067e5198a500b67c5198a50006bf4198a50024fe7098a50024fc7098a500267f5098a500267d5098a50026ee2098a50026ec2098a50004ff7458a50014fe7458a50004fd7458a50014fc7458a50004ff7358a5003cfc7358a50026ef7258a5008eee5258a5008eed5258a50006ee4258a50006ed4258a50004ff7158a5000cfe7158a5000cfc7158a50006bf4158a50024fc7058a50026ee2058a50026ec2058a502767f6454a503ee7d6454a500075f7354a503757c7354a500075c7354a500055c7354a500067d6354a5001d7f7254a5001f6f7254a500567e6254a502776e6254a502776d6254a5012d7e7154a5012d7c7154a503ef3f4154a502757f7054a500077b7054a50277787054a5001e7e6054a5001f7a6054a5003cff76cca50024fe76cca50004fd76cca503757f75cca5001d7c75cca50006ee62cca50006ed62cca50054ff768ca50024fe768ca50004fd768ca5001d7e758ca500057d758ca5003ede638ca50006dd638ca501cf5c538ca50004ff764ca50004fd764ca50024fc764ca500057f754ca5001d7c754ca50054ff760ca50024fe760ca50004fd760ca5001d7e750ca500057d750ca5003ede630ca50006dd630ca503775c530ca50
  | 22 => 0x8d211d4ff7258d21006ef7258d211acff7158d21006f77158d211aebf4158d211aebd4158d21004ff7058d21024fc7058d211c4fe7618d210067f6518d210067c6518d2103ede6318d21006dd6318d211c5de7618d21006de7618d211c4de7618d21006df6518d210075f6518d210065f6518d21006de6518d21006dd6518d21006dc6518d210075c6518d210065c6518d21006df6418d21006de6418d21006dd6418d21006dc6418d2118f9f4118d2118f9d4118d2118fce2118d2118fcc2118d2118fd42118d2103edf7518d2103ede7518d2103edd7518d2103edc7518d2103edf7418d2103ede7418d2103edd7418d2103edc7418d21006df5418d21006de5418d21006dd5418d21006dc5418d2103edf7218d2103edd7218d21006df5218d21006dc5218d21006df4218d21006de4218d21006dd4218d21006dc4218d2103edf7118d2103ede7118d2103edd7118d2103edc7118d2118edf5118d2118ede5118d2118edd5118d2118edc5118d2118edf4118d2118e9f4118d2118ede4118d2118edd4118d2118e9d4118d2118edc4118d2118edf2118d2118ede2118d2118edd2118d2118edc2118d2103edf7018d2103ede7018d2103edd7018d2103edc7018d21006df5018d21006dc5018d21006df4018d21006de4018d21006dd4018d21006dc4018d2118edf1018d2118ede1018d2118edd1018d2118edc1018d2103cff7694d21004fe7694d21004fd7694d2103cfc7694d210067f6594d2101e7c6594d21006df6394d2103edc6394d211475f5394d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d2101e7c6554d21006df6354d2103edc6354d213fcfe76949211fe7f659492101e7c6594921006df6394921006dc63949211476f5294921057e4219492101cff765492100cfe76549211ecfd765492100cfc76549210067f655492101e7c6554921005df7354921005dc7354921006df6354921006dc6354921005f7715492100df471549211efe4215492100cfe76cc92100cfc76cc9210067f65cc9211e67c65cc921006df63cc92103edc63cc92100df671cc921005f571cc92118cfe768c9210067f658c9211ce7c658c9211c6df638c92103edc638c92103cff764c92100cfe764c9211acfd764c92100cfc764c9210057f754c9211457c754c9210067f654c9211be7c654c921006df634c92103edc634c921005f7714c92100df4714c9211c4fe760c9211457e750c9210057d750c9210067f650c92119e7c650c921006df630c92103edc630c9210077765c85210077465c8521007d763c8521007d463c852100df672c852100fe672c852100ef762c852100fe762c85210067f65d81210067c65d8121006df63d8121006dc63d812101cfe75d8121004fd75d812101cfc75d8121004ff74d8121014f
  | 23 => 0x1fe7d31d95211fe7c31d95211fe7f21d95211fe7e21d95211fe7c21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f40d95210067e40d95210067d40d95210067c40d95211fe7f10d95211fe7e10d95211fe7d10d95211fe7c10d95211467c6559521005df7359521005dc7359521405ef72595211fcff75595210067f7559521004ff7459521014fe7459521004fd7459521014fc7459521004ff7359521006df7359521004df735952103cfc7359521006dc735952103cdc7359521404ff7259521006ef72595211ecff7159521006f771595211eebf41595211eebd4159521004ff7059521024fc70595211fd7e76195211467e76195211fc7e76195210067f64195210067e64195210067d64195210067c64195213fe7f62195213fe7f61195213ff3f41195213ff3d41195213ff6e21195213ff6c21195213ff74211952103cfe76d8d210067f65d8d210067c65d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21004ff74d8d21014fe74d8d21004fd74d8d21014fc74d8d21006df53d8d21006dc53d8d21006df43d8d21006de43d8d21006dd43d8d21006dc43d8d21054ff71d8d211c4fd71d8d211c6bf41d8d211c6bd41d8d211c6df31d8d211c6dd31d8d21024fe70d8d21004fd70d8d2103cde76d8d21006df65d8d210075f65d8d210065f65d8d21006de65d8d21006dd65d8d21006dc65d8d210075c65d8d210065c65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d211c79f41d8d211c79d41d8d211c7ce21d8d211c7cc21d8d211c7d421d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d211c6df72d8d211c6dd72d8d21006df52d8d21006dc52d8d21006df42d8d21006de42d8d21006dd42d8d21006dc42d8d211c6df71d8d211c6de71d8d211c6dd71d8d211c6dc71d8d211c6df51d8d211c6de51d8d211c6dd51d8d211c6dc51d8d211c6df41d8d211c69f41d8d211c6de41d8d211c6dd41d8d211c69d41d8d211c6dc41d8d211c6df21d8d211c6de21d8d211c6dc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006dc50d8d21006df40d8d21006de40d8d21006dd40d8d21006dc40d8d211c6df10d8d211c6de10d8d211c6dd10d8d211c6dc10d8d211457e7598d210057d7598d210067f6598d210067c6598d21006df6398d211aded7298d210057f7558d211457c7558d210067f6558d210067c6558d211d5ef7258d21004ff7558d210067f7558d210047f7558d2101cfe7558d2101cfc7558d210067c7558d2101c7c7558d21004ff7458d21014fe7458d21004fd7458d21014fc7458d21006df735
  | 24 => 0xc505972101cfe75d8f21004fd75d8f21054fc75d8f21054ff74d8f21014fe74d8f21004fd74d8f21054fc74d8f21006df53d8f21006dc53d8f21054fe72d8f21056ee72d8f21056f571d8f211c6bf41d8f211c6bd41d8f211c6de31d8f211c6dc31d8f21024fe70d8f21004fd70d8f211acfd7698f21056df6398f21056dc6398f2103cff7658f210057f7558f211557c7558f21056dc6358f21004ff7558f210067f7558f210047f7558f2101cfe7558f2101cfc7558f210067c7558f2101c7c7558f21004ff7458f21014fe7458f21004fd7458f21014fc7458f21056df7358f2100cfe7258f2100cfc7258f21056de3258f21056dc3258f211aebf4158f211aebd4158f211aedf3158f211aedd3158f21004ff7058f21024fc7058f2103cff7694f21054fe7694f21004fd7694f21054fc7694f210067f6594f2101e7c6594f211575f5394f21004ff7654f21054fe7654f21004fd7654f21054fc7654f2101e7e6554f210067d6554f21404ff7654b210567f6554b210567c6554b21005df7354b21005dc7354b211efe62154b211acfd76ccb21056df63ccb21056dc63ccb211d4ff764cb210057f754cb211557c754cb21056df634cb21056dc634cb211557e75983210057d7598321005de7398321005dd7398321056fb6098321026f86098321005bf745832114dbc7458321056f86058321004ff755832101cfe755832101cfc7558321004ff7458321006bf7458321004bf7458321014fe7458321004fd7458321014fc7458321006bc7458321014bc7458321004ff735832103cfc735832100cfc725832107ebf415832107ebd4158321056fb2058321056f8205832107efa105832101cfe76d95211467e65d9521004ff74d9521014fe74d9521004fd74d9521014fc74d95211467f54d95210067e54d95210067d54d95211467c54d952103cfe73d9521004fd73d95211467f53d95211467c53d952100cfd72d95211467f52d9521054ff71d95211fcfd71d95211fe7f51d95211fe7d51d95211febf41d95211febd41d9521024fe70d9521004fd70d95211467f50d95211467c50d95213fd7e76d952101c7e76d95210067f64d95210067e64d95210067d64d95210067c64d95211ff3f41d95211ff3d41d95211ff6e21d95211ff6c21d95211ff7421d95210067f74d95210067e74d95210067d74d95210067c74d95210067f73d95210067e73d95210067d73d95210067c73d95210067f43d95210067e43d95210067d43d95210067c43d95211fe7f72d95211467e72d95211fe7d72d95210067f42d95210067e42d95210067d42d95210067c42d95211fe7f71d95211fe7e71d95211fe7d71d95211fe7c71d95211fe7f41d95211fe3f41d95211fe7e41d95211fe7d41d95211fe3d41d95211fe7c41d95211fe7f31d95211fe7e31d9521
  | 25 => 0x89310057f75589311657c75589311657e75189310057d7518931006ed621893101cfe75189310567e751893101c7e7518931004fd75189310567d75189310047d7518931054fc7518931054ff7418931014fe7418931004fd7418931054fc7418931056dd7318931006df5318931006dc5318931006ef5218931056ec5218931056ee4218931006ed4218931054ff711893103cfd711893118ebf411893118ebd411893118ede311893118edc3118931056ef211893118eed2118931024fe7018931004fd7018931004fe7694931004fd7694931054fc76949310067f659493101e7c659493103dde7394931005dd73949311675c5394931004ff7654931004fe7654931004fc765493101e7e65549310067d6554931005df735493103ddc73549311675f535493118dde76cc93103ede76cc93118cde76cc931165de75cc93103ddc75cc931056dc62cc93100dde71cc93100ddc71cc93103edf61cc93103fd761cc9311d79f41cc9311d79d41cc931005dd70cc93100cfe768c9311addd738c9311c6df638c931006ef628c931056ec628c93100df6718c931005f5718c93100cfc764c9310057f754c9311657c754c931006ef624c931006ec624c931005f7714c93100df4714c93100ddc764c9311aedc764c93100cdc764c9310075f754c931165de754c931165dc754c9310075c754c9311655c754c93103ddf724c93103fcf724c931007cf624c931056dc624c931007cc624c931006cc624c931007d7714c93100dde714c93100ddc714c9311afd4714c93103edf614c93103fd7614c9311af9f414c9311af9d414c931005df704c93101cfe75d8131004fd75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d8131054fe72d8131004fd72d813103cfd71d8131106bf41d8131106bd41d8131106fa10d8131006fb60981310057f75581311657c7558131005bf745813115dbc7458131005ef7258131005ec72581311657e75181310057d7518131026fa6018131006f960181311ecfd75d9721054ff74d9721014fe74d9721004fd74d9721054fc74d972103cfe73d9721004fd73d97211567c53d9721054fe72d9721056ee72d97210567f52d9721056f571d97211fe7e51d97211fe7c51d97211febf41d97211febd41d9721024fe70d9721004fd70d97211567f50d972101cff76597210567c6559721005df7359721005dc73597210567f7559721004ff7459721014fe7459721004fd7459721014fc74597211567f54597210067d5459721004ff7359721006df7359721004df735972103cfc7359721006dc735972103cdc73597211567f535972100cfe725972100cfc72597210567e52597210567c52597211ee7f51597211ee7d51597211eebf41597211eebd4159721004ff7059721024fc70597211567
  | 26 => 0x3eef3298b31056ec3298b311c6bf4198b311c6bd4198b311c6de3198b3103edc3198b31056ef2198b311c6ed2198b31024fe7098b31004fd7098b3103edf3098b31004ff7558b3101cfe7558b3101cfc7558b31004ff7458b31014fe7458b31004fd7458b31014fc7458b3100cfc7358b3103eef7258b3103eef3258b3103eec3258b311aebf4158b311aebd4158b311aeef2158b31004ff7058b31024fc7058b31054ff7694b3103cfe7694b31004fd7694b3101e7e6594b310067d6594b3103dde7394b31005dd7394b3139f5c5394b31004ff7654b31004fd7654b3103cfc7654b3101e7e6554b310067d6554b31005df7354b3103ddc7354b311775f5354b3103ddf764cb31006df764cb311c4df764cb310075f754cb31175de754cb31175dc754cb310075c754cb311755c754cb3103f5e654cb3103f5d654cb3103fcf724cb31056de624cb3100dde714cb3100ddc714cb311af9f414cb311af9d414cb31005df704cb31004ff755833101cfe755833101cfc7558331004ff7458331006bf7458331004bf7458331014fe7458331004fd7458331014fc7458331006bc7458331014bc745833100cfc7358331004ff7258331054fc72583310d6bf41583310d6bd415833103efb705833103efb305833103ef830583310d6fa105833101cfe76d95311667e65d953103dde73d953100ddd73d95311675f53d9531004ff74d9531014fe74d9531004fd74d9531014fc74d95311667f54d95310067d54d953100cfd73d953121edd73d953100cdd73d95311667f53d9531166df53d95311665f53d9531166dc53d9531054fe72d9531004fd72d95311667c52d953103cff71d953103cfd71d953121e7f51d953121e7d51d953121ebf41d953121ebd41d9531024fe70d9531004fd70d95311667c50d95311667c655953140ddf73595311675c5359531005ef7259531005ec725953121cff75595310067f7559531004ff7459531014fe7459531004fd7459531014fc745953140cff7359531006df7359531166df53595313867e53595313867c5359531166dc5359531004ff7259531006ef7259531004ef7259531054fc7259531006ec7259531004ec72595311667f525953120cff7159531006f7715953120e7e515953120e7c515953120ebf415953120ebd4159531004ff7059531024fc70595311667f505953101cff7654d3100cfe7654d3120cfd7654d3100cfc7654d310067f6554d3101e7c6554d3140ddf7354d3103f5c5354d31005f77154d3100df47154d3101cfe75d8931004fd75d893101cfc75d8931004ff74d8931014fe74d8931004fd74d8931014fc74d8931006ef52d8931006ec52d8931006ee42d8931006ed42d893103cfd71d89311d6bf41d89311d6bd41d89311d6ef21d8931024fe70d8931004fd70d8931006ef629
  | 27 => 0xf755814117dbe755814117dbc75581410073c755814117d3c7558141005bf73581410079f73581410059f7358141295bc73581410079c73581410059c7358141005bf7258141007af7258141005af7258141005bc7258141007ac7258141005ac725814142dbf7158141007b77158141045b7715814142ebf615814102fb76158141007bb605814123ebe605814142fb71058141425be761814117dbe751814123f3e751814117d3e7518141005bd751814123f3d75181410053d751814123dbc7518141295be731814123f9e73181410059e7318141005bd731814123f9d73181410059d7318141006be6318141006bc6318141005be721814123fae7218141005ae7218141005bd721814123fad7218141005ad7218141006be6218141006bc6218141015bf711814100dbe7118141015bd711814123fb5711814100dbc711814128ebf611814141fb7611814123dbe701814123ebf601814123fba601814123ebd6018141007b96018141006b9601814123fb7101814123fba1018141417b9101814103e7f7559731004ff7459731014fe7459731004fd7459731014fc74597311767f54597310067e54597310067d54597311767c545973100cfe735973100cfc735973103edc735973100cdc7359731176df535973103e7e535973103e7c535973103edc5359731004ff7259731054fc72597311767f52597311767c525973120e7f515973120e7d515973120ebf415973120ebd4159731004ff7059731024fc70597311767f50597311767c505973103edf30597310067f74597310067e74597310067d74597310067c745973103e7f73597311765f735973103e7e735973103e7d735973103e7c735973103e5c735973103e7f435973103e7e435973103e7d435973103e7c43597310067f72597310067e72597310067d72597310067c72597310067f42597310067e42597310067d42597310067c425973103e7f325973103e7e325973103e7d325973103e7c325973120e7f715973120e7e715973120e7d715973120e7c715973120e7f415973120e3f415973120e7e415973120e7d415973120e3d415973120e7c415973103e7f315973103e7e315973103e7d315973103e7c315973120e7f215973120e7e215973120e7d215973120e7c21597310067f70597310067e70597310067d70597310067c70597310067f40597310067e40597310067d40597310067c405973103e7f305973103e5f305973103e7e305973103e7d305973103e7c305973120e7f105973120e7e105973120e7d105973120e7c105973101cfe7598b31004fd7598b31054fc7598b31054ff7498b31014fe7498b31004fd7498b31054fc7498b3100cfe7398b31056de7398b3100cde7398b3100cfc7398b31006df5398b3103edc5398b31056ee7298b31056df3298b31
  | 28 => 0x4941295bc73549410079c73549410059c735494117f3f53549410073d5354941405bf725494117faf52549410073e525494117f3c525494117fac52549411edbf7154941007b77154941005b7715494100dbe715494100dbc71549411efb4715494100db471549411eebf61549411f7b761549411ef3f51549411ef3d5154941005bf705494123dbc705494117f3c50549411efb71054941295bf76cc941005be76cc941005bd76cc941295bc76cc941295bf75cc94117dbe75cc941005bd75cc941295bc75cc9411d5bf71cc94100dbe71cc9411d5bd71cc94100dbc71cc9411d6bf61cc9411dfb761cc9411d79f31cc94123dbe70cc941005bd70cc9411d7b710cc941005bf768c941005be768c941005bd768c941005bc768c941005bf758c94117dbe758c941005bd758c94117dbc758c9411adbd738c9410079f638c9410079c638c94144f9f538c94144f9c538c94118dbe728c9410079f328c941297af328c94100dbe718c9411c5bd718c94100dbc718c9411c6bf618c9411a7b7618c9411c79e318c9411c79c318c94123dbe708c941005bd708c9411c7b7108c941005bf764c941005be764c941005bd764c941005bc764c941005bf754c9410073f754c9410053f754c94117dbe754c941005bd754c94117dbc754c9410073c754c94117d3c754c941297af324c9410079e324c9411adbf714c941007b7714c941005b7714c94100dbe714c94100dbc714c9411afb4714c94100db4714c9411aebf614c9411b7b7614c941005bf704c94123dbc704c9411afb7104c941295bf760c941005be760c941005bd760c941295bc760c941295bf750c94117dbe750c9412973e750c94117d3e750c941005bd750c9412973d750c9410053d750c941295bc750c9411d5be730c9410079f630c9412979c630c9414479f530c9412979c530c9411c5be720c9412979f320c941297ae320c9410079d320c941297ad320c94118dbf710c94100dbe710c94118fb6710c94100db6710c94118dbd710c941297b5710c941005b5710c94100dbc710c94118ebf610c941197b7610c94118f9e310c94118f9c310c94123dbe700c941005bd700c94118fb7100c94117dbe75d8141005bd75d814117dbc75d8141295be73d8141005bd73d8141005be72d8141005bd72d8141015bf71d814143fb771d8141015bd71d8141426bf61d814143fb761d8141427b710d8141427ba10d8141427b910d814142dbd769814117dbe7598141005bd759814123dbc7598141295be7398141005bd7398141006be6398141006bc6398141005be7298141005bd7298141006be6298141006bc6298141435bd719814123fb5719814102db5719814128ebf6198141047b7619814123dbe709814123ebf6098141007bb609814123fb71098141005bf75581410073f75581410053
  | 29 => 0x2973f5394d4117f9f5394d4117f1f5394d412979c5394d41005be7294d41005bd7294d4117f3c5294d4121dbf7194d4100dbe7194d4121fb67194d4100db67194d4121dbd7194d41297b57194d41005b57194d4100dbc7194d4121ebf6194d41227b76194d4121f3f5194d4121f3d5194d4123dbe7094d41005bd7094d4117f3c5094d4121fb71094d41005bf7654d41005be7654d41005bd7654d41005bc7654d4121dbf7554d410073f6554d4117f3c6554d4140dbf7354d410079f6354d410079c6354d4117f9f5354d412973e5354d412973c5354d4117f9c5354d41005bf7254d41005bc7254d4117f3f5254d4120dbf7154d4100dbe7154d4100dbc7154d4120ebf6154d41217b76154d4120f3e5154d4120f3c5154d41005bf7054d4123dbc7054d4117f3f5054d4120fb71054d4117dbe75d8941005bd75d894117dbc75d8941295be73d8941005bd73d8941015bf71d8941015bd71d894146ebf61d894147fb761d894146faf21d894146fad21d894123dbe70d8941005bd70d894146fb710d8941475bd769894117dbe7598941005bd759894117dbc7598941295be7398941005bd7398941455be7298941006bf6298941007af6298941465bd7198941007b5719894113db57198941466bf619894114fb7619894123dbe7098941005bd7098941467b71098941005bf75589410073f75589410053f755894117dbe755894117dbc75589410073c755894117d3c7558941005bf73589410079f73589410059f7358941295bc73589410079c73589410059c7358941007af6258941006be6258941475bf7158941007b7715894114db77158941476bf615894113fb76158941005bf7058941007bb7058941005bb705894123dbc7058941007b87058941005b87058941477b7105894146dbe761894117dbe75189410073e751894117d3e7518941005bd75189410073d75189410053d751894117dbc7518941295be7318941005bd7318941465be7218941006bf6218941007ae6218941006bd6218941007ad6218941015bf711894100dbe7118941015bd711894100dbc7118941456bf611894145fb76118941457af2118941457ad211894123dbe7018941005bd7018941457b71018941005bf7694941005be7694941005bd7694941005bc76949411edbd75949410073f659494117f3c6594941295be7394941005bd73949410073e539494117f3c53949413fdbe729494117f3f529494117faf529494117fac529494100dbe71949411fdbd719494100dbc71949411febf6194941207b761949411ff3e51949411ff3c519494123dbe7094941005bd709494117f3f50949411ffb71094941005bf7654941005be7654941005bd7654941005bc76549411fdbf755494117f3e65549410073d6554941005bf73549410079f73549410059f735
  | 30 => 0xc538c951004ff764c951004fe764c951004fc764c9510057f754c95101d7c754c951004fe760c951004fd760c951054fc760c95101d7e750c9510057d750c951006df630c95103edc630c9513875c530c951006ef620c951056ec620c951024fe76d815100cfd75d8151004ff74d8151014fe74d8151004fd74d8151014fc74d815103cfe73d8151004fd73d8151054fe72d8151004fd72d815101cfd71d815125ebf41d815125ebd41d81513c6fa50d815125efa10d81512667f6598151006fb60981512667f6518151005de7318151005dd7318151026fa6018151006f960181514e5be76d95414bdbd75d954117ebe65d954117f3e65d954117e3e65d954117ebc65d9541295be73d9541005bd73d954117f3f53d9541005be72d9541005bd72d954117f3c52d9541015bf71d954100dbe71d9541015bd71d954100dbc71d95414cebf61d95414dfb761d95414cf3f51d95414cf3d51d954123dbe70d9541005bd70d954117f3c50d95414cfb710d95414d5bf76595414cdbf75595410073f655954117ebe655954117ebc655954117f3c6559541005bf7359541295bc735954117f3c5359541005bf7259541005bc725954117f3f52595414bdbf7159541007b771595414c5b771595414bebf6159541187b761595414bf3e51595414bf3c5159541005bf705954123dbc705954117f3f50595414bfb7105954117dbe75d8d410073e75d8d4117d3e75d8d41005bd75d8d410073d75d8d410053d75d8d4117dbc75d8d41005be72d8d41005bd72d8d41015bf71d8d41015bd71d8d414a6bf61d8d414b7b761d8d414a79f31d8d414a79d31d8d4123dbe70d8d41005bd70d8d414a7b710d8d414adbd7698d4117dbe7598d412973e7598d4117d3e7598d41005bd7598d412973d7598d410053d7598d41295bc7598d4148dbe7398d41296bf6398d410079f6398d41005be7298d41005bd7298d4149dbd7198d41297b57198d4115db57198d4149ebf6198d4116fb76198d4123dbe7098d41005bd7098d4149fb71098d41005bf7558d4117dbe7558d4117dbc7558d410079f6358d41296be6358d41005bf7258d41005bc7258d414adbf7158d41007b77158d4116db77158d414aebf6158d4115fb76158d41005bf7058d4123dbc7058d414afb71058d414a5be7618d4117dbe7518d41005bd7518d41295bc7518d4149dbe7318d41296bf6318d412979e6318d41296bd6318d410079d6318d41005be7218d41005bd7218d41015bf7118d4100dbe7118d41015bd7118d4100dbc7118d4148ebf6118d41497b76118d4148f9f3118d4148f9d3118d4123dbe7018d41005bd7018d4148fb71018d41295bf7694d41005be7694d41005bd7694d41295bc7694d4120dbd7594d4117f3e6594d410073d6594d41485be7394d410079f6394d412979c6394d41
  | 31 => 0x843218ebf415843218ef64158432006f5415843203ef7315843218ede315843203edc315843203ef43158432056f72158432056f42158432004ff7058432024fc705843203edf305843218ef71058432004ff755803201cfe755803201cfc7558032004ff7458032006bf7458032004bf7458032014fe7458032004fd7458032014fc7458032006bc7458032014bc7458032004ff715803200cfe715803200cfc7158032006bf4158032056fb7058032006fa4058032006f9405803203efb305803203ef83058032056fb2058032056f8205803203cfe76d8d5100cfd75d8d5140e7d75d8d51004ff74d8d51014fe74d8d51004fd74d8d51014fc74d8d5150ede53d8d5150edd53d8d513867c53d8d51054fe72d8d51004fd72d8d5150e7f52d8d5101cfd71d8d5140e7e51d8d5140e7c51d8d5140ebf41d8d5140ebd41d8d5140edf31d8d51024fe70d8d51004fd70d8d5150e7f50d8d51006df6398d513875c5398d51165f57198d511675c5358d51005ef7258d51005ec7258d51175f77158d5103ede6318d51006dd6318d5100d7e7694d5121e7e7694d5100c7e7694d515067f6494d515067d6494d5101d7e7394d5101f5e7394d513867f6394d510075f6394d510065f6394d513875c6394d510057d7294d5100d7e7194d5121f767194d51387757194d5100d7c7194d5101e7f6194d5101f776194d5121f3f4194d510057d7094d5127e7c6094d5100cfd75d8951004ff74d8951014fe74d8951004fd74d8951014fc74d895103cfe73d8951004fd73d89514feee52d89514feed52d895101cfd71d8951406bf41d8951406bd41d8951406ef21d8951024fe70d8951004fd70d8951006ef6298951145f57198951005df7358951005dc7358951155f77158951006ed621895100cfd75189510567d7518951054ff7418951014fe7418951004fd7418951054fc741895103cfe7318951004fd73189510067e53189514f67c53189510567f5218951056ee52189514f6ed5218951054ff711895101cfd71189513fe7e51189513fe7c51189513febf41189513febd4118951056ef21189513feed2118951024fe7018951004fd70189514f67f501895100d7c76549511ee7c765495100c7c76549514ee7f64549514ee7d64549510075f73549513857c73549510075c73549510055c73549510067f635495101d7f725495101f6f72549510076f62549510567c62549510076c625495100777715495100d7e715495100d7c71549511ef74715495101e7f615495101f7761549511ef3f41549510057f70549512767c6054951004fe76cc951004fd76cc95103cfc76cc9513857f75cc95101d7c75cc951006ef62cc951006ec62cc951004fe768c951004fd768c951054fc768c95101d7e758c9510057d758c951006df638c95103edc638c9511cf5
  | 32 => 0x24fe70d8532004fd70d85321aef410d85320057f75585321bd7c75585320067f65585320067c65585321aef461585320067f65d81320067c65d813201cfe75d8132004fd75d813201cfc75d8132004ff74d8132014fe74d8132004fd74d8132014fc74d8132006de32d813200cfe71d8132004fd71d813200cfc71d8132006bf41d81321bd7e75981320057d75981320067f65981320067c6598132006fb60981320057f75581321bd7c75581320067f65581320067c6558132005bf74581321b5bc7458132005f771581321adf471581320067f65181320067c6518132026fa6018132006f96018132054ff75594320567f7559432004ff7459432014fe7459432004fd7459432014fc745943219e7f54594320067e54594320067d545943219e7c545943203cfe735943203cfc735943203edc735943203cdc735943219edf535943203e7e535943203e7c535943203edc5359432054fe7259432054fc72594320567e52594320567c5259432004ff715943200cfe715943200cfc715943219e7f51594320067e515943219e7c5159432006bf4159432004ff7059432024fc705943219e7f505943219e7c505943203edf30594320067f74594320067e74594320067d74594320067c745943203e7f735943219e5f735943203e7e735943203e7d735943203e7c735943203e5c735943203e7f435943203e7e435943203e7d435943203e7c435943219e7f72594320567e72594320567c72594320067f42594320567e42594320067d42594320567c425943203e7f32594320567e325943203e7d32594320567c32594320067f71594320067e71594320067d71594320067c71594320067f41594320063f41594320067e41594320067d41594320067c415943203e7f315943203e7e315943203e7d315943203e7c31594320567f21594320067e21594320567c21594320067f70594320067e70594320067d70594320067c70594320067f40594320067e40594320067d40594320067c405943203e7f305943203e5f305943203e7e305943203e7d305943203e7c30594320567f20594320567c20594320067f10594320067c10594321ccff765483201e7e65548320067d6554832005df735483203ddc735483219f5f5354832055df764c832006df764c832004df764c8320075f754c83219dde754c83219ddc754c8320075c754c83219d5c754c8320575e654c8320575d654c832055df724c83203fcf724c832056de624c832057ce624c832057ce524c832007cd524c83218dde714c83218ddc714c83251f9f414c832517ce214c832057cc214c832005df704c832004ff755843201cfe755843201cfc7558432004ff7458432014fe7458432004fd7458432014fc7458432006df535843203edc535843203edf3258432006dd3258432056f7715
  | 33 => 0xc7258232004ff715823200cfe715823200cfc7158232006bf4158232056fb2058232056f8205823201cfe76d95321be7e65d9532004ff74d9532014fe74d9532004fd74d9532014fc74d95321be7f54d95320067e54d95320067d54d95321be7c54d95321bcfd73d95321be7f53d953203cfd72d95321be7f52d953200cfe71d9532004fd71d953200cfc71d95321be7f51d95320067e51d95321be7c51d9532006bf41d9532024fe70d9532004fd70d95321be7f50d95321be7c50d95321bd7e76d953201c7e76d95320067f64d95320067e64d95320067d64d95320067c64d953239f6f32d953239f6c32d95320067e61d95320067c61d95320073f41d95320067f74d95320067e74d95320067d74d95320067c74d95320067f73d953239e7e73d95320067d73d953239e7c73d95320067f43d953239e7e43d95320067d43d953239e7c43d953239e7f72d95321be7e72d95320067d72d95320067f42d95320067e42d95320067d42d95320067c42d953239e7f32d953239e7c32d95320067f71d95320067e71d95320067d71d95320067c71d95320067f41d95320063f41d95320067e41d95320067d41d95320067c41d953239e7f31d95320067e31d953239e7c31d95320067e21d95320067c21d95320067f70d95320067e70d95320067d70d95320067c70d95320067f40d95320067e40d95320067d40d95320067c40d953239e7f30d953239e7c30d95320067f10d95320067c10d95321be7c65595321bcff75595320067f7559532004ff7459532014fe7459532004fd7459532014fc74595321ccff7359532006df73595321ccdf73595321e4ff7259532006ef7259532004ff715953200cfe715953200cfc7159532006bf4159532004ff7059532024fc70595320057e76195321be7e76195320047e76195320067f64195320067e64195320067d64195320067c641953252e7f621953252f6f321953252f6c32195320067e61195320067c61195320073f411953201cfc7654d320067f6554d3201e7c6554d32005ef7254d32005ec7254d3203fcc3254d321e4fe76949320067f659493201e7c65949321bf6f529493201cff76549321bcfd765493203cfc76549320067f655493201e7c6554932005df735493203ddc73549320067f658c9321ce7c658c93203dee728c93203eef628c9320075f658c9321cede658c9321cedc658c9320075c658c9321ce5c658c932055de728c932056df628c93203fcf628c932005dd718c9321c6de618c9321c6dc618c9325279f418c93200cfe76d85320067f65d85320067c65d85321aef661d853201cfe75d8532004fd75d853201cfc75d8532004ff74d8532014fe74d8532004fd74d8532014fc74d853203cfd72d85321aebf41d85321aef641d8532006f541d85321aef631d85321aef621d8532
  | 34 => 0x973203e7e535973203e7c53597321e67f5259732004ff715973200cfe715973200cfc71597320067e51597321e67c5159732006bf4159732004ff7059732024fc70597321e67f50597321bcfd7694b3239e7f6594b3201e7c6594b3201cff7654b3203cfc7654b3201e7e6554b320067d6554b32005df7354b3203ddc7354b32004ff755873201cfe755873201cfc7558732004ff7458732014fe7458732004fd7458732014fc745873203ef771587321d6bf415873203ef7315873203ef431587321d6f62158732004ff7058732024fc7058732004ff75583320067f75583320047f755833201cfe755833201cfc75583320067c755833201c7c7558332004ff7458332014fe7458332004fd7458332014fc745833203edc3258332004ff715833200cfe715833200cfc7158332006bf415833203edf315833203efb705833203efb305833203ef830583321ccfd75d9632054ff74d9632014fe74d9632004fd74d9632054fc74d9632056dd73d96321cedf53d963239e7e53d963239e7c53d96321cedc53d9632056ee72d96320567f52d963200cfe71d9632004fd71d963200cfc71d96320067e51d96321ce7c51d9632006bf41d9632024fe70d9632004fd70d96321ce7f50d963201cff76596320567c655963203ddc73596321cf5f53596320567f7559632004ff7459632014fe7459632004fd7459632014fc74596321ce7f54596320067d54596321cedf73596321ce7f53596321cedf53596321ce5f53596321cedc5359632054fc72596320567e52596320567c5259632004ff715963200cfe715963200cfc71596321ce7f5159632006bf4159632004ff7059632024fc70596321ce7c505963201cff7654e32054fc7654e3201e7e6554e320067d6554e321cddf7354e3203f5c5354e32005ef7254e32055ec7254e3203fcf3254e3219cff7654a320567f6554a320567c6554a321cddf7354a3203ddc7354a321cf5f5354a32055dd76cca3203edd76cca321cdde75cca3203ddc75cca32057ce62cca32057ce52cca32007cd52cca321c5de71cca3203ddc71cca325379f41cca32005dd70cca3200cff76586320057f75586321cd7c755863203ddc7358632056f461586321c7d63158632004ff75586320067f75586320047f755863201cfe755863201cfc75586320067c755863201c7c7558632004ff7458632014fe7458632004fd7458632014fc7458632006df5358632006dc5358632054fc7258632006df32586321c6bf41586321c6de31586321c6f631586321c6dc3158632056f72158632056f42158632004ff7058632024fc70586321cd7e75982320057d7598232056fb6098232026f86098232056f86058232004ff755823201cfe755823201cfc7558232004ff7458232014fe7458232004fd7458232014fc7458232054f
  | 35 => 0x6dc6418d5219f5f5418d520075d5418d5219fcf5218d5219f5c5218d5219fcc5218d52006de6118d52006dc6118d5219f5f5118d520079f4118d5219f5c5018d5203edf7518d5203ede7518d5203e5e7518d5203edc7518d5203edf7418d5203ede7418d5203edd7418d5203edc7418d5219edf5418d5219e5f5418d5219ede5418d5219edd5418d520065d5418d5219edc5418d5203edf7218d5203edd7218d5219edf5218d5219ede5218d5219edd5218d5219edc5218d5219e5c5218d52006df4218d52006de4218d52006dd4218d52006dc4218d5203edf7118d5203ede7118d5203edd7118d5203edc7118d5219edf5118d5219e5f5118d5219ede5118d5219edd5118d5219edc5118d52006df4118d520069f4118d52006de4118d52006dd4118d52006dc4118d52006de2118d52006dc2118d5203edf7018d5203ede7018d5203edd7018d5203edc7018d5219edf5018d5219ede5018d5219edd5018d5219edc5018d5219e5c5018d52006df4018d52006de4018d52006dd4018d52006dc4018d52006df1018d52006dc1018d5203c7c7654d525557f7454d525557d7454d5201d7f7354d5201f5f7354d520075f6354d5203e7e6354d5203e7c6354d520075c6354d5203e5c6354d520076f7254d520557c7254d520076c7254d5201e7f6254d5201f6f6254d520057f7154d5220e7e6154d5220e7c6154d5254f3f4154d522757c7054d520557f74949525457d74949520057d73949520075f639495239e7c63949520075c63949520065c63949520557e72949520576e72949520567f629495201f6f62949520057d71949521fe7e61949521fe7c619495253f3f41949522757e709495200cfe76d8552006df63d8552006dc63d85521eef661d8552004ff74d8552014fe74d8552004fd74d8552014fc74d855203cfe73d8552004fd73d855201cfd72d85521eef651d85521eebf41d85521eef641d8552006f541d85521eef621d8552024fe70d8552004fd70d85521eef410d8552005df7358552005dc7358552006df6358552006dc63585521eef46158552006df63d8152006dc63d8152004ff74d8152014fe74d8152004fd74d8152014fc74d81520b67f54d81520067d54d815203cfe73d8152004fd73d81520b67f53d81520067d53d81520067e52d81520b67c52d815200cfe71d8152004fd71d815200cfc71d81520b67f51d8152006bf41d81520b6fa50d81522767c50d8152005de7398152005dd7398152006df6398152006dc6398152006fb6098152005bf74581521f5bc7458152005df7358152005dc7358152006df6358152006dc6358152005f771581521edf47158152006df6318152006dc6318152026fa6018152006f9601815203e7f7559732004ff7459732014fe7459732004fd7459732014fc745973203cfc735
  | 36 => 0xc5358e52054fc7258e521be7f5258e52056de3258e52056dc3258e52004ff7158e5200cfe7158e5200cfc7158e520067e5158e521be7c5158e52006bf4158e52004ff7058e52024fc7058e521be7f5058e5255e7f6494e5255e7d6494e5201d7e7394e5201f5e7394e5239f5e6394e5239e7d6394e520075d6394e520065d6394e5239f6e7294e520057d7294e5239f6d7294e520056d7294e5201e7e6294e5201f6e6294e521fd7e7194e521fd7c7194e5255f3f4194e520057d7094e5227e7e6094e5200cff765865201d7c7558652056f461586521ff765158652004ff7458652014fe7458652004fd7458652014fc7458652004ff735865203cfc73586520067e53586521467c5358652054fc72586521467f52586521fe7e51586521fef651586521fe7651586521fe7c51586521febf4158652056f72158652056f42158652004ff7058652024fc70586521467f5058652005de7398252005dd7398252056fb6098252026f86098252056f86058252004ff7458252014fe7458252004fd7458252014fc7458252004ff735825203cfc7358252054fc7258252004ff715825200cfe715825200cfc7158252006bf415825208efa5058252056fb2058252056f82058252004ff74d8d52014fe74d8d52004fd74d8d52014fc74d8d521cede53d8d521cedd53d8d52006df43d8d52006de43d8d52006dd43d8d52006dc43d8d5200cfe71d8d52004fd71d8d5200cfc71d8d52006bf41d8d52006de31d8d52006dc31d8d52024fe70d8d52004fd70d8d520075f75d8d521cf5c75d8d52006df64d8d52006de64d8d52006dd64d8d52006dc64d8d521cf5f54d8d520075d54d8d521cfcf52d8d521cf5c52d8d521cfcc52d8d52006de61d8d52006dc61d8d521cf5f51d8d520079f41d8d521cf5c50d8d521cedf75d8d521cede75d8d521cedc75d8d52006df74d8d52006de74d8d52006dd74d8d52006dc74d8d521cedf54d8d521cede54d8d521cedd54d8d521cedc54d8d521cedf72d8d521cedd72d8d521cedf52d8d521cede52d8d521cedc52d8d52006df42d8d52006de42d8d52006dd42d8d52006dc42d8d52006df71d8d52006de71d8d52006dd71d8d52006dc71d8d521cedf51d8d521cede51d8d521cedd51d8d521cedc51d8d52006df41d8d520069f41d8d52006de41d8d52006dd41d8d52006dc41d8d52006de21d8d52006dc21d8d52006df70d8d52006de70d8d52006dd70d8d52006dc70d8d521cedf50d8d521cede50d8d521cedd50d8d521cedc50d8d52006df40d8d52006de40d8d52006dd40d8d52006dc40d8d52006df10d8d52006dc10d8d52006df6398d521bded7298d521e5ef7258d5203ede6318d52006dd6318d521cdde7618d52006de7618d5219f5e7518d520075d7518d52006df6418d52006de6418d52006dd6418d52
  | 37 => 0x8a5303eef3298a53056ec3298a5300cfe7198a53004fd7198a5300cfc7198a53006bf4198a53024fe7098a53004fd7098a5303edf3098a53004ff7458a53014fe7458a53004fd7458a53014fc7458a531be7f5458a530067d5458a5303cfc7358a5303e7f5358a5303e7d5358a5303eef7258a531beee5258a531be7c5258a5303eef3258a5303eec3258a53004ff7158a5300cfe7158a5300cfc7158a531be7f5158a53006bf4158a53004ff7058a53024fc7058a531be7c5058a53004ff7458653014fe7458653004fd7458653014fc745865303cfe735865303cfc7358653166df535865303edc5358653004ff7258653054fc725865303ef7715865321ef6515865321ebf415865321ef64158653006f5415865303ef7315865303ef43158653004ff7058653024fc705865303edf3058653004ff7458253014fe7458253004fd7458253014fc74582530e67f54582530067d545825303cfc735825303e7f535825303e7d5358253004ff7258253054fc72582530e67c5258253004ff715825300cfe715825300cfc71582530e67f5158253006bf415825303efb70582530e6fa505825327e7c505825303efb305825303ef8305825303cfd75d8953004ff74d8953014fe74d8953004fd74d8953014fc74d89531e6ee52d895300cfe71d8953004fd71d895300cfc71d8953006bf41d8953006ee21d8953006ec21d8953024fe70d8953004fd70d8953006ef6298953006ed621895303cfd7518953054ff7418953014fe7418953004fd7418953054fc741895319edf531895352e7e531895352e7c531895319edc53189530567f5218953056ee521895319eed521895300cfe7118953004fd711895300cfc71189530067e511895319e7c5118953006bf4118953006ee2118953056ec2118953024fe7018953004fd701895319e7f501895300cfe76d855301d7e75d855320ef661d855320f7651d855303cfd75d855303c7d75d8553004ff74d8553014fe74d8553004fd74d8553014fc74d855301cfd73d8553176df53d85535667e53d85535667c53d8553176dc53d8553054fe72d8553004fd72d85531767f52d855320e7e51d855320ef651d855320e7c51d855320ebf41d855320ef631d8553024fe70d8553004fd70d85531767f50d8553005ef7258553005ec725855320ef4615855303cfd75d8153004ff74d8153014fe74d8153004fd74d8153014fc74d8153054fe72d8153004fd72d815300cfe71d8153004fd71d815300cfc71d8153006bf41d8153116fa50d8153005ee7298153005ed7298153006fb6098153005bf7458153215bc745815327e7f6518153026fa6018153006f96018153056df6398e52056dc6398e52056dc6358e52004ff7458e52014fe7458e52004fd7458e52014fc7458e521bede5358e521bedd5358e5239e7
  | 38 => 0x240020014007000400a0014000001400000000040024002000000000040000000003000000d0008001003400f00080010014000000000f003000000500030000000000400c00040030004005000000000080000024008004400000040000038005000001100300020010002000000800180000028005000000d000000c00000020070000000000d0000012000000000000000004006000800000240130028008005400c00040110018004000800c00040110004012001800100040200028022001400a006000000040050000008001800200140020000002000000f0000001005c0010000005000000600580020008000000c00600000000024008000000100000000000003000c003012000d0008003004400400180000018000001400d00340000018001000c0100080004004c01e000000800cc00900000080008001001c001000c00700000040004004006400500100050000003000000100080000000000001c01200700000000002001800200000010068003004800000040030008003000400500100000000000000000a000400b000c0000028002000400700000010000000004801c000c00000000030000009000c000000400200000030000001001c002001400100000010020009009400100380000000001002800000000000004000000000f00640010000000000401100000020014004000c0030000000000000a0000000000800000000040014003000000300040000084000000000d0058002008000100580030004000000400b0000005006c0070004000000000500a0004001c002001c00000140100000000000c00500000150050000003800400400060004000002400000100020000000000000100200000000000003400d0004001002000a00400000000013000000b0000003001400a005c00200000030000005000800200040010014002002000300040000018002000000a000001d00000000000001006000a0094003001400600180420000002000000300280020000006008000000000000000001000400f00140000028000007c00400140010004008002400b0000003000c000000c00100080080010007000400000180020008004000000200800020024000000c0010000009003c0050014004002400200140140064002000000400180000000000008400100080000008003000c00100000010020005000800100100280000001000000000040000020000000000200080000000000000000100280030008000000c0030004003000c002001400000140040014001001c01100140030004000001c002009800500080050000000003000e0000003054ff7498a53014fe7498a53004fd7498a53054fc7498a5303cfe7398a53054fc7398a531cedf5398a5303edc5398a53056ee7298a53056ee5298a531ceed529
  | 39 => 0x1c02b000000000240000000002000000a00240000000004000c00000140010004001000000300180070000006001000b000400000180040054004000000500000000000005000c000001c00c000400000540010008003000c009000001400cc002006c00000740000014001003c0030028001005800900040100008000001c0090000009000403d000c0020034008001400100000000000000000c00100480130008000002c0100054000002c007000000400000020010015000c0020000000000400d00140030000001001c000000000000040060018007000001c002800200c00010014006003800100040000018003000c000002001300000010004019000000200380010000005000400000000040028039001c000002800a0008006004000400380000020000002c00100100000000003000001600040020010000003400300040030008008001c0000008022000400a00240080048000002000000180000008014002c02200180030008004001000a001400200080030010013000801900d0002000000100780000004000000001a001000100bc0010000000006c007000001b00500010000001000000c001400500ac0010000000000400100540040088014001c006000400200240030004002000c02300680000038002000806400140000000001005000000040000018001000400300180000004000004c00000000010000002001400400300010040001000000600040020044003003000d0008013003800000100120004005000000b00140120050004000000200000070050001008c008002800a0008000000c00100080030064012006000000f400100040000000003002c0010004004005400300000040048004000c00a0064039000000700000000000003000c00d000000000140000008004000000000340020020041000400c0000003000800300200060014004001c001000000100080000000002002800c00400010004006000000300280030000006001c004000c006001802b0000000004801a0004000000000200000060014000000000200040000000000000c0050008001004400300280030084000002c02100340000004005000400400140070004001001400000040000028003000800c001c005000c013005c000000400200100000024003001000f0020000002800a0000005008c000002800300080000014006000000300780030000000000000000000020010002000c0070000002000c010001800c001001a009400000000080010000000400100140000000006000800000040050000001000400f00040090020016000c002002800a000c00f0024000003000800040010004001002400a0000001002001000140020000002003c00d00980090004000000000200000040004002001000200000020000015001c0
  | 40 => 0x3001800000000000008005000000200140070010002007c002000400a00000140000000000000500a8000000000200140040008003000400a000000f0038006000800500f80040000019000400a003400100000010000000005000c00040050014000001000000480170000005000800600180000018000011c0010020001000000200300050024008000c003002c0020010001002c0010004009003c0070014000003c013001000a00100000000008000c003000400d000000100000040040000005c001002001d00300020004007000c0030004003000c003004000000000000004001000002e0004004000800000100000004000000801d00040070048000000000200000000018005000400c000400500d4010000000100300040000006000c00200240000008000001c006000000e00d00030018001001000300080080008000000000100000000068000000400c00140010010007000000100040100000001003c002001400000040080050003000c00400040050000000000000b00dc003000800300000010030003008c0000000000000c0010000000000401c0008004005801f000000600140000004007004000200300010054020000001f0000000000c0080014007000000500100020024001001000400000050004001000400000200000038008001c00200000010010012000000a000c0050000006000000c00080000000003000800100000030000001000000000100000000000001c0040000000002400100040280004000000000100080000014006000400000000050008003006c00500000000004002006000200b000a004000600000100014000001800000340000000001000c004001c000000000700140090004001000000000000000000002002400f005c000003800f0020000000000b00600080014006000400e00000000000009000c0140028002000800e00140070020006000c00700040000000001000800500040000010009000c006001000e004c00300080070000019000c004007c000003c00000000030050007005001600200020008000000800200040030010002005802d00040170020000001c0000024002000400100240000000000005000a00080370034006002800000000000030000000c010001800100040010000000007c00400180040000002000c000003c0010000000000000400000030080000000c0010018000001c00c0004001003c002000000000040030008000000000000040020000005000c0020020030009800d002c0000000004002c0030038006003c002000c00801cc00000a80070000005001000400000000000001000800d000000c00000010000003000800000c8000000c0050020002000800a0034000000400c00280000040003000c002000c00a0000000000400500040000
  | 41 => 0x522a09832eada80ae951a382869e5aba6fe886947600023f896f1ba0a1094f8baea27251f844a3e08d5ac96a4a070c803ac7c00006748000a1c2e3cb0880000000000a6480000000a20000000000003f000019d43b98dc87791238bb31a18af726f6b68065e34c85d6a8b0000419861800023a2a4e0000000294415380003e30000abb800000025f422e9162000000000029c04418b980bc170017900babd4000a6098f5a5660a760000000b03ae4600017d44db255e254b06481b80004218322869829c53a0ad80002ef860400009ac902600000008c680001402c3a0002522688a4e8b1a8ce2b152e9a0cb007269d0d420e080020014003002c000000400400240000008000001c00c0014000001000200400000000000000800300080080004002004c004000000d00040090000000007401a004000000000050000000000c00200000000064000000c001004800a00000070004000000400800040140004011005c0030000001002c00100100080000000000400000000040020009000c00200000170000002001401e000c00400040090000003000000000600010018003006000b000401000240010008000000801d00000070000015003400000000030018000000000200000000038003000800000180010010001000400300180000008000000c007000c00300200240000008003800e00200010014002000401700040030000000000801f00040030040002000c006000c000003c001000c0070038004000c0030068001000400300000000034007001000500000000000000012c006000003e000000b00000090000034000000500280010044010000400c0008004000c00a00bc00a00000040034001001000000000000034001000c000000c000000001a0044000000000f00080000048023000001b004800200140020020002000800d0008000000400d00000010010042000000f0014001000000d0030004001c00b0014000006400200000070010006000401a0014000005c0000038019000c0000010000000000b00000040020000000c00b000400d00000050014000001801f001000400200050034003000c0010000002002c00000040090010004003c000001000400200000000000001c000000c004000000c00680070020000000000d000800200000030000020003c03b00000040064000000000600140020068005005400c000800300100030008002000c006000c003000800a0010000000000f00100070024000002c01500100000000000000000000080010010009003000000080060000000001800b0038000003c0090014000000800100080070000002000800100380030008007000400b000400700e400e0004002000c001005001800200030004006001400000200000008003000800200040020038017000c0000008
  | 42 => 0xa9323ed01a6878831284f1110c8512880000000374893cb4c02a8249323e5c3aa34b989f0e3432f9482409323c016a894f00003a700000000000bb0a98800013a63a984f6bc699e404c3282be4800096a80008c9000000000009b582960001a7a81985421d7adb0b2d0000c75944884429621e00a5c9b703ec219156466708100b801c2000255c312057e9588ade3999c1c9999c5a94c0dba06d80000000000c45051c5b18000000000000001d03f5000005526b02b800000000000332800000000000000000b1f8b7653d8d1aad50e280000ef80000000000000071a17a63e41df2bdf9692000032000010b82c4a4d61163212931000013f139c015a0a219c095c9f6ad4e20c0000bfb84346eb1ccc00014c0c8e80001628f200bf134c26c0000cad1c8e2399234574825e54b8a9eaa515c0825000000011447cd000000000000001c085da0000286800090104981531e86631a5b0031314800028567db08c8a9d92f2786214a7b181ba833800000021f890620e61e1adae000157e91a00000002cdc3e500008810ea8b64b0ea0002102994a4142e1851e4baa41a5cea210bd200005e19b747589eacc771874a6a00000000d68000000098b934a0001c84ad39764755a2d86649c1069a0000000000036c1c3cc0ab05621f21d05169c600000eea00021a43bf8000bb70a6e021079abca1266914097a78a0000579973c00000003fe8526a121a5c0002bfe6a226f07e58000000059400004280001dec000076a8749e842fea3427e8000c6cd2c120000000c672622597161455d067c5f42c2a85f19ac4549c56c5f800000000009e1a2261e3166ebaf310466cabf834d1df813580008090000bc9000074000001228000000180a749000069300000001e340dc016800021a031428cc4fca9966470000810000026a000027d24be66d800055832b8000000000007d4652a48200015a000000007f580009508000000167c65ea30a000000000013dabb9a89a54d209290c83c8b76067481507be39711725619b027d48000a489f209a1836600009fe0000adc00000a8c4089960188c6e63125080b992fa0001956a8388680001fce89c000025f00000000198bd8938a152b276a9aa02600000000000000ac319582fb23660629d3418002d08d80a921ac11f872022b2083908439297623380c680cd800000029364de91e68aa800054e240c60f2cfa000294241a9af231d31d400000000000000be380004b8916a000022cc9e8000751853abc892e61d2235a000148856d0a18ab88000aa2a94ab1ba9dc00019000c094f0b05855e3fc9f2e30c81128368dfe4ca2f42879a4b2074afbc06028c40000102c372d7e27700007d400003e900006c000001be99d000000000100000000023204c85ae00019d80000de6b640000625800033600005278000c7b8000
  | 43 => 0xc665193200030e2734894400026d8000000046e0ed64a2ae640001d44adf000045f800000006886a6873e2b41a3416431267a0859ec952d32000000096311cc9241c4e8600000aae98ee736000048b8000b9022302600000000000097680000000000af88000000181c000000030c2f6a98aa39c0000f40000127e1e8800000000000000daa3320e08c41800000000009d030ac1a4888a00019a25f31d2e993966ca5400d26ee97d672b80001468000b7dac94484001484802de6e131724040a165730a62afd000075b80000002daa6f3329800015c864100000001ad2000208a85680006b68000b148712c8aa65e3501770726000065091e89252c8a019a90e38c000000000009cdac1a908a88e02882dc6611e8091681de7f52310a3c92ce7f600deb928fe82578b9c00012124de0282ab0156a0001e521de146609e80008ec0aa66b71e1443924469458000c339de68d611e286288d0873aa6854831fc3d985fe0d591e44092f4680d90e01bd078413a2efc99b02260000000000169817c8378000033e00006600a78000867864a000000018680008f4000000000007f18000c1e0000b098000387a0b676710e2564800011c8e2052f0000c5508e049105b65c9886c11500005920e72000000000028940000000000000000000007efacd2000000092927dc00000000001f900000a3276608d24fe921e53a8000648060aa4d1d6a74a8bf608f0f0600014b63d71cf6b6e80001f0885a127a2b05f292dc0000000bce9e24a2d2a18c33259ab45843e6db82b063885582581a724df83aea62912abb827949dd09304e6800076d80003a391fc7f22958b96000000000000000000000000035a8000c3b96125fb00000002a0276100ce88f800012d95368c310b60002ec4b3a000004787240462aa49c2926c485800081eac2e8e28000000000072a00003eb0a3c09383de1eba06c6309386225800092aa48c0000d2c9ae000073100000000e14a5c27d8ae123b671e800095ba4e25de9fea761a9ca2450bea377b248607ab5cc7211e0b820f3438d2aae0471f1200000008fca25c311800037ea948000271064c00005059bb4000105215d12d29ad259ca6100008a7003255b92c458f800024f8272518a46695690760da2ae4c07000041e000096a197c00000006c30000592830800018d440c8b9475484e6b6584c800005700ec9c040001e0ac1f80003ec00003b689900000000000113eac0834cc8622e47dd800057e800054f84dc0000000c5ea2bc726941887a89a0cab000083bb27485d06844cc959a30fab94b18167609fb16230809e89c80d6ea18acb251a00363a409d24a0800060faeb64c1867e8a627008862a50bc518040cbb0c233d82feaaf253654992486f8ac002d0000000000004cf0a2829fa03c44595e2529877e8dca4ec73c82445d7
  | 44 => 0xaa242b7787cc13502922062b8c34da5861e9320a00000009c4800000017f8b04000088d07b6000274c57b1e8c5408accbda2bd81821caa042064630b8ab2b611f24342a6f22e089da88eb20e77d8d1200017f051298ec72e920a00019f48302c9ec64805e33100000002038a8010d20001b90000000032500008f38000ad610a29a131805460000324af906b0aec6143a4da00001f6c022356c73ab6c000000056f0dd070891588de2ece7d32ade41a0a8e00030023e59a6461384be0002fe8000155a10da75897b20bc1ea8000bb7835ca4e9d0e01e0000000000000000000000d0e00001160000a228bc80000000000000000040500eec1324f61a686a2ac382a2b1410cc3a600000000000b98083e8fd28faca283a87e2a1fe2588000b8e000000029fc06b000000018a800007e80000000b158caebe780000000000a980dbc70a08d85071e2e697a500897a27c01e9e04c540fa89361f26557a4bc8458fd0b8a81e000000003ae0000000000000017ce1410a0a8ff80be7888a9a00026460002b8e28d02e800000000f28000af7961a50395ea1f89b2eb53102e72c18640000000000000000026fc2fd0394000094e3762a16000085c0000922bea8e52490280a5331dbca5e82528281aec00023bea89a6ea45780007ad847ab4e800000000000d7a10e26600000811e8e1cb940a760a63ca000a364229c400000390af3814c3602cf460d0a0e0000c9e0000e684121a6a0f4800033c83aa690a5380002f0a0000ffc97c92a615bae561702cae94fa3f698518669b7a6509f0a9a291e13d44eea8a274400008ad0ca8c6b96347291aea29c206829b226a000155459e23e25339f1613692c2bab1b1a3d6062eb4983e60ce839c0d896b26e6ac9c69282166938e60610958c2221e6201105f41921d3c0a82318709ab1a85b05320c585ea22506bec01ad74a572d280000d4e05712967a2a4e6979312800010aac7880761f117f22328530000000051c2d0ca3480008e911da2ba300a62d170200014e0b090000917222e47fa41e67c00009d813a2792100000fa27a45e89e63c091227bd800000000000d0800026319109b08e2405da6206a11a0e87a168630092467531fb636398be25e0b526b80ba0b0812f8843107c6bf21c0aeb800000024520001b964b5a1e4688000084895847b69ba82a70e18c98135c0001ee600000000000738c4913b86b197249ee0d94762000075e0f9c4e10b5c07b800031730f0725a3fac7422a883b18227a911b024707602942f4a00010e6acb186000000004e50000000000071f1398000000040f13ae44c000082a05620d20000909000000014e600000000000000649000000028f6a92936016ab24e00019882721bf00000f36022113c8bfb14e0000fc01d913c2000107e00029740000000a872d4271da8241c7234
  | 45 => 0x9c6cd9e5c50c186a2afa7387450e22949a50e80b83e80000b542948000b6c9450575028ebc802640000c2a8b599e66c100008573294278057a96ca4f2b54962e00000001d0016a520047c10495500000d7eba18000201a8584c50000a889bec12d1bbe6fd8328000018c00030b0000235cbf49d8c8490104547af040000000a7621f20001ad0aa400000002b860002b629738000000000000008fc8a80000000159e0000f301aeb19046fa60e82ba2946e380000000000000000000000001cc000092a30300002bf20000a2a013000000023d24a49a8c0d1107a00000004172eb20001006c73301e4dd8f0ac1e97ea4c32dc000027ba98c000037d00000000ff0432000054e913a5e2ab3e1cc926296d000041600001f800000002e5e0000000bc321620002ee81f3800062c326c04b892c5b5a32000000bc6ce9504b892b9ac488e88a4a23e01e48000be724c60b30eb43b607b08160518000122a00028604060e269ff9dfe9650000000094655d8318c669b4a000136e6b01a3a000269000029563001b4887580009fb000000000000000a5a8b08000baf80006ba00001329eb84771d7247c9a940002d2c00031f4a06040eafa13368d4236e0002e420000000000000026190360000caa0002a6200031a8000000011a8000a101a3c68106e812500006df93540f38314677290436922207ec238cc63aa9a67aade8000291841386060000586603800000025409db0000006a3880968c0cc698d1695600000001f820e92d4800000004d098560000000000000000021fc2871ac40001b6200001fe51e31c22b51bc40001fdc9d90000a579c869f428e2bd3911286a0f785db06860000bc41e280000919ffcc47a6cc7318000718800000f119c0000000bdb9eeac18171e4882d8e0002fea06091600da8000b999c00000000000000003a0af8074498367c6afdaa9b2eb02d322c469d86bc09badf27681b1667e8ef4015276663a06b46d19bfe00028b079bac8c01b915616e84de28513d80c90d4cae8034680ab0963f69944b4711360001e9e02a80000000000c248000431328697a00009ec0bf26d0800099682e22369178000000000000000000000000000078c1bfc6b9000099e0e7800004aa8a380000000848ab60000000000011e129a90e0880ad00cb88da1cdebb8ac5e95c9e00562259045b316cc4b967a00017828a9114cca22f3c000000000021787d7b1326da8000b882ce6295074c3a5000032b1962000303a00000000000000465000080015e807b0d72000000038d80000000000230000000013464939460a1195820fa9e26955800085a1208000035a8b6a7e67372472786a92491aab2a16e0000a67990e00025e60002ac6035a44aa0c908202724a6299289019a1908000094c95f16625fe92f6bc09e060003046000268e000193a4a
  | 46 => 0x8fa73c60b000050f00003b90000b938e6a81323ea00000001db03fa2ce867840c000000025b6b9d8c10000000000032022ad84a673400004e4ac34000197048198006ac8000000104c0001b3200031f894329166aaaeec42caea65d39a5240225ea2d61f320c027e24dc21be0881ba4c1697c82998d22a6ca5884b41fba2d697b611b04acadead46c221cf004a9660834a7c0be92b6a55b03dc8e5828a3ac013e000315a0c9b25e2438ba8a6b1c4a68580004ec8b9600000005b38ddac2309745f900000d2ad542701d50b1106b204e05fa10b000036d2de24a70edc25629c47122afa6e98d74ba2b2bc2e4a73e8328d561c6866a0001e36adda074b6f86a0bf10000636a3ca1a380008f000005de225449a0a96000196456500000d38000863ac04859a45601a000000025d659f817c3e98000ca3a72643b27a84640dae00001c07eb1d5c0002f72000302c79a11c09a511fa93f26547e31d40a4c11003f10000b679022323943400000000001f740001050000096e000000000015628d4a7e41951e54aec00001b09080c18800079e0de2c460f4aabf13c81b7a66e3fd0a26b40131e0000000739a11c00021f000012860001a10b7d14e2b7b00001b0062480608c2afbacbe5a688fe84c29e4210802e9629dd020ca44023d16b60000ed200013cc02b04f000000d4000285c1c582663021fa825d800044129d45230000af319daa220d2053f8d5400000008b700004590f8a805830a976000000000005d480007278af0bf0ab366d303544928afabd721c6b608000a6818a20001784b3b19820000000853a60a6de9600406aff892b800000005569a21c704800000c54b0c47fe006c000000000025349260be010799d6bff024a18414de12317e885190ca6460a8a0469f9c5962ca03dd8e448a4917445b8d8a4cea6ee7fb2b3201601a213e2734a230000b108000b1ca65c9da9fe05ff2bb81dc9dc4896ab34a708d5c1f41dea4680720c198ab404310f02e2271cc4c2458bc1906e1082cc08f5b28475f082a51b1d601b481e411986fe7538c1e00013e011d14d60000000b8b09d0000321055a000000000004e080005bc1446a6d844e5e000000e58000ac8205a2ca995c2f58e5eb70acfc0000000000244ea3900000000000cae800000016aa54300000000fa0271280c7d08000000272e000208c00007067ce8000000000000000007d20e1279d1490abd00002213110aaca892000000000000005640c769f530a65bd0000000280407e2c924f016fe8b780009e40afe8c1261ac6c102031c0d661d2a53ab3c076e637b0385d80060660304e88c8e104690b0e46aab786a700008ec9bf48e516e43d79ee06290aca3f18a0c4fbad6294ba72a79387548d52dc858986429609b1c98eab4c5318bb6328149476a99c633fadfc78c9e4612a29605b88c
  | 47 => 0xc98061858437320c233681f04648000000196639d263485000000371ebe0001b800000f0ebc404160001dce170800000000000002ef65b71efe53700000fe2e90923ad3400018fc2d588f0380043232c83c4670a5486d7915a3d42d7c3318152244292a56b1b587d6aa5e0000000036000068b8000200b2401b3005a2e91556ca81820095ae0063e238e8f18b10aa08000b69021cbab8000b8c938c235aea0c1085d0bc98fa28e08000b528d64764850a0000bd0a78813c98a1f0a15900009b1000050f800000000000000eec142322ea2a01922dcb018211a1e0322abc627ba8266878a8672cae721bb1fa226b313a0caa35e8c4a5ee61b30d00001daea7a8d7661da6aa5b5313c8be80f60aa905617700000001298c6ab1823708f6a90e800074600007480000000152c0002cda000000082c2306772974a70600002c200007cf0b64000000000000007752ab0b268b900001a6e00000000001e2a000194046b8000c7693e600027e86048c06178176613b26b65a7ac786210000c068eaa3048000000141a8a08bbc83c00380000082000165a8ef2cbc3a58000059ab4ab9fab4226ba46e24d14c25859c3e3df8cbe4ef03a023500003d39d683230000000150051610fa000294000000988f619bebad27c82e69e5e23a17144c88f3ca8b8f7000000000001c8a080a05655496c0000000011304020002ea2a8c86826fbab244fb1e1c39d86409d2a6d284130a805c14122a62cb02af07e4000000009d800080707880000000a6680003b2aa2018700000001bc6937a0ea5b2821a9a331c6b35934879c000001f1ea0000248400016088c7215e84b80003812fa61e0af000b219260000000000000000018725709ade000000008b80000bb1cf83f58ada2032ed84c02f7a8ae2d70af10000942a84a0001f70000000021780000002dd6000000066900008daa0d4000000000000009bea2f00002e7a000000083d0000000188c00000000001e92000075ab628000c100000c85b032b7c056c9a9000012b80000000000000164e17600000000662b72865c0bd862caeb18b2a4680005a800005ef0cd26a3800078b000042eb0be0bd179a00031a284280009a5b09cbdf0aec000266827f081600000000000ac450900003a017a221a9a8000022f422e110a00006ac0001bf2532000000016184af8000c030f1c8e40fe462700005eea9d264097a8bbc2a381b2903e0000ec0b5c9c3a99888744c2839243e0aa09b9928400002221ee00007a580006e200004f88000000009200000000000000b42000044e00009b88c64000000058400007e608f6b4b8a027d898249fa800009aa69e3c9a7f09b000005ffa33a25599a8000121a3630eba22f000000025325d180006f98000bbf95dc00016e6bba978c551aa145f10d100000124000116600031c40000d1ca
  | 48 => 0x16230b1af4364b18c9e60046aef1bb66061dde2c5a12a20d0d9e1202d026bc096c59c0b7c0002fae3fb99ae5c18ba27be845e9dd97387a611841be08cc534125285c0000000009e6c983e0101b14a0000ec255004f40000e8a3e4a5d43ce294698e2b1839b24ca00000000001bd44970000c3a00001208c660d480000090000bf50b2e000098e000000000000002e7a552b07800073a0b346f78602a0a0918acc00002908b30a949d087930718a4b202821413b0bc6168e0e6184c02911c2b2a11d418815a42cd944cb84a742000251843632a60dca8dc4f2800052e158abf780003d0ad6c38b1c200000000c62006a38e997e7c5102c09d273200026640002b2842317ac0000000426870c0951410b3f826038316cc0002a087de2812514a4cec98b24c00026bcae0000002ba708a798000000288a588800022400006cf0936b3c8000b46000083e10900002e82be3219ca60040800000006578c24c9995aabf41eba227935200000001d9a9c8877261e00000000000eceb3780006ae8000000305822a9d5a0000258a322c6400006388ca19c40000d90a8c1ee2c11327c756000000021fa0a326068f9b19636f82701c9800000013627a9946a6c2000000000000001ec8afb1b2a49d000000000003f38f1a0000000000000000000000000000790aea8a9d162a7bbb0505a33258ace2d768ce2aa615d9e7e1c404c401712941ef1ca6365800000020b293726442a096ac3bf224c00000005e380008c78dc4125aef4a4700000000b7e18f00003699bbc0d90000ae280000001d64000217200005da0000000045000054927c67e4800093e00000002554416808ca3b00000f5979c000045051380009269892000322600000003a68636000279c5d3284e00013d60001eb40000f1491f275cbf292deadf9fc06669fa6aa60982aedae70341325c30e175a9afa04200028f81b1846800020801dea048645147429f20ba41b000018caad482684e0559a58e65b0aa807119fe65ca9009e58d863c596f252906305dba95a6e51512b412b6807e820a0d426980001d0241c80002b900000000000ca59cb800000000002d7a63280000000000485000061c102800013de0002160bc5aba200000000001b50995a7509482e6cc81aecabef831a4bf2e800000fbc450958e28e01647f994d20752c62055870405e86ea29d2fa844b9fc219600002b003ba000044600020b859c85503a7883c1848cf455380001fea9aa20d8fd8a2622529fbac367990e02c619654ab9942036b29109899b56284987a94b0a407509f5c0fcb1e85d72268c87895a3d3045c95d8c883f485f863c9c06261194c5c4b1b40000000aad224a70789ec162049aa6e25f00002488a360cbc24ea762a0da2ae9b2a87e77728220f092acb13ac82aa896c8be5865a54a96deba90
  | 49 => 0x9374bca934419bb06e6a7a13200027bc158234e000000000001ae8040dfc99600000af9c9499f000026d26800000000b3a8ea400000000000000b5800002ff80000001302c32800046a00006c90000b561d8063f9b8a9f3205c000091a8f72efa1099bb042d1a40000070a2cc93f489590a008799221fc9912460800012c28024351bae1bd800089b0b0cbf19cacc8d8000c35b03ebe8228a52a0b38870800000028bc80d12b863598cc8330000270a5a4c701d90206942e8eb8000a16b252953800000014ae0af18ae1b11d066699ff2af488f200009005ca016c83eaec0ab488dc0002eee87205280b2a07262200000000000114a88433029120000000b3d8000a0a900a8d028beb69a9b0b9d023a0000bbea429deeb9e000018300001c89704b0f1e90aa7a7e03752c3097f138e46c9f1e2eb28c20000ed05d207daa1f000081900000000000000110cbe629540000000a0b000000026e4241037a3f731ea00000001b700002c00fb61cd83f40000a6862e82789e6ad123ee000000020f2c30000032880008e10000aa000001a400009e39a662ee8000a91aa1a9c9000057600000001d8a000272200000000001168058000000000000002a56000316800012e822d23a6000211a9d681360f91492a90000000025c294180000000000000000002d99cc000142a3fd80000000000000000000026c84e408ee17f0bee00001269861c6cc48000005b8e320001a44a590d5049301b29321d66aa822f61c780009ea8c0400016c26348000000036c000000099d000092d00006ab0000be88c860000000aa200000e181e231a920c56e89aac559dd80001e6a09a1276000000090d07c600000007858000a2918e48f21f58afe8ae200023ac0002be697d80007840f46c121a600a91998af0902a0738f680f8800000000000000000000296e0000000000318a1c0b12cb2a84380001aa648887ea34982da97f994e7301ab64638d44c3f17368fa177cc0b9620686a7a6014a398b2200000002e6e3358f809f58cf02f9a808ae2240ac4e1604aea9b825e58c9000000480002b6623aaf08656800009030681fb2b2e5ec01507fc042275c1b60bf00c5a7d922ce881aa10c77a1c442f018425a98fa58e00002820f0c7f28c8400009d8224a3c2a59aabebdd934ec9431e4b81a3c4a82935e2961f9a41c29867d594d85352aa8a54a19a711907400013eaa7cae1090b03f64890000b338ebe7ca18dc6a4a164c0a056627a8c22144aa78545000000028d000009d49c11498c4facd0c7e8cce12ca1940eda0a402c2c6c46f1b9e684861e41509f86852b1c6050c40228899aa498cf835488ceb56ade437c0000000310c00000009c6014000013dc543800000022487b4000019c9cee7691ec000000007678000b65000048c290654a29ae5b82b6e3b815a20388c18
  | 50 => 0x228c194663390e80000000c00086000009540000dca8a580000000634188a9c6216257e000251c00027ae9f1281626e00009e0236c00003765ecab82b198000a27070014d8dd6adc0000c51826c1cb0c80a640306afa923a0000798cad9004000000044a30fec0991d00002f6400021b0000055229e2fdc622b1b80f1a9ecad4a968a3010b080b03740000cd01f7800007700000001280309ac1c2939cbe5012d3c0000000625310e81c09e4bb52a2a8542154612800049baaec000038800009c6209131600021eea7e23262fe0000a1e80006a8000091e80000001b227e027a44058e64221952268c98ac6778854ac5abca0a61fe8a6d1948ab3808e8648000226a68298f82b67d10000b42a2d0b711c3000012420ee16f80ac98826892fba778a57487d15dec26a52a367231600000003cca8fc4ae91debb22ba894a08b2a6323860001d6ca1d800031e1ea800013d07c194e489f800074fb23817b00007bc0000594838c0000e38000000049500000000000c2500000000f1074988220000fae00010cea47b10a7b614ba49aa978a75b1940000000c82000019b251200015ee68991d8ba509660002b5e00000000000fe6465ade616003fcae610c26988e423dea4d20001d1c92b2bb48ca888ea818ca420207a600000000000de87bf00004d980da000143a000009488a90be8e793c40001720c32000000000001ff1baa1631272965ab6400000000000000695000000000001ea0000be284108558fde03a81a8c57002613314382d8873c96f96460001ede62410f617993a84b695a888f0218b201ef200017c2b6020dc11b8000795976a6958000131a5fa1441ae66c4053eb9f0000c3e22083db0000bce270200011ea9228030a1521900001b2c1da031c9c3050c16c965e00aa6d4b8b969c78317c03c12872a14876235822beac500000000742616030c85a9b6c60596448eaa1f686d8e3e2b187941a50c3c0e28b2898080000f021ba1ae1b6686d000000028fe8b895fc000305c0480018000000020483ac4ce220c08d2e442521ace796303c42380001b80000000000064e32920002c6840e15160000000b298000a5a800021380000000000000000000028d600014ec00000000002806954314462630045ed28f006900004a92a3a30d1ed6a198000ab709082aeac4a2779b30af52dda68c0000706996a8848c5e5658750ca696ba3e10d3e28109261bcb1b20a00f7c7c126e066e249e392279e1682dac064151c10607f8736ab4680211f4c0d0d78c749edc22d800089424926429bce9512214b0b000024192c600012c80001ba2ab81d2c687229e00000ca0001dfc1d5b1607be0000b688000861af3276c868c4cfa6ec000145c000000068f8000000000067000004179976b7b80005870000b2d86ee00017b800000000000000000119876f
  | 51 => 0x11716a7d8000880aa7277c2b907b299c8000103400017f48ff00000002a928918000b4380000000e7e4fc044219eae8e5cd3024a5cae52ac4000000007ac36e0f3ea0b8e464a793d28d294326af9640000084ab2b00000000ee84abad9c80e9b28000290273b1b4e18fa78c000000015530aa85ea5980b5a6a820284a03b52e28000025c8c201720000000808947ab01a22c00000003e18df800000000002d780000000000015841080005bf0000a95000036dad6e1a0000000010fc00021ec00d0fecaf6912426792fe683193e1308c7a7af298e52130de4ad8d1400011c4b38a42867380000001fcc75513c68b2ae4c9e2800065517da0000c82a8329ceb6d17ae00002fa2758ffeb73b072763a94ea9f92e00000fba5b62d680000bc622fa0de53ca56666c2facb5713642a91868ab21440a90a28c8b1a69aac230706a612608e81510ab0adfa33792b024ba0c8c1b06280202f58000048e52c80d0c6b11d290f85689bd01940002cb80f42ddcbfcac0c00000000000000ae988440002c7a23e1b7c73f80000001a6c010841ab858000000000003c1db421b914a24a000000030b20001c4404e94421bf13ce22800004301b720001b98000289600028783f31bc8000229000000000000ce8c4006e216d000000001340b0000000020be8211862626ad869e12f88912135000000000000708c1d143645401cc5ba109626d83b09ed04fe526801c1349e4a935081c26cad567c21f4a5bd8096325b17000000e40ce16fab941ec479f2882000094ac88ac844c91f1c0001dac748935671500005a900009ed98022e29d320000f8e5a21d745e90456c2e23de745987cc24237e78e955861fb15e15724809719132004a0e21b582f204180001c3800000000006a080005238000001a64cb8da70e70b8000836234431f800000028740001270a8daf740000000085000000000000000000b8d00004ca9c0c000269218582ae000313476696ec0000b440001f66062147c7a700000659e7a000051463a8df681da6ce0002dd46ab8000b31a196a741fd27412e0a5e6000000000009259656082233c3f8000000029f0000069cc8b2e1c2cfb0e0a66244c37915a600025d00000000000009a714b05400019f600000000000e580001c5000004e400000000000ddc6d72df86828000593264a2cb134000017227e508a676899288b229ba3611b5a1f4800000028ba0000000692074e1b9261600024084180d6c0001ceaa7b9b9200002300002d2220b1ca0ba4918a3160a8c48625101eca11e71ca546aa317102651c364538000a5f992e4c9800080120fc15e2392a04155cbf9a14c00000002ac12b2000000096b8eee752000092d9bca00004ee0002ae894900000001cc800000001ad80000000ea2000210800031a40301fae000000000020b40000000000163
  | 52 => 0x91db16a5d626a60d000000001ad6a0e17503f882ac9532c38b74b0209a829fe0000000239000000029ccba58000617047e38a800049927520001ef47d1abfc269a830900042a00027fc9a8abd61f980000000000b468a56000317469f1808314ac9047c2c7caf905bc47280000000d060ef800000028d4000000081124c27388ef26ac00000001d945218000c4d990680517ee1aa229a21d94ee00028200000eb68e028ae724800067b80006d5139ec351548a9925e20000aac0001a020002f368d198381ed12566c5101e91080000ed286428916ee8a89570311200620b9fdeb1c1318a42198e2bf2b748512d445cb11b4b8524e4a2a8d5829e88402f089fa70593e48bb8c0e51c82d24871eceaa18400bc792d40000a94b7f999000022e80000a848cb32682f8800014bb2ae7c0aa4c702a46cc048aaa0000dea5940828b7400f23ef8dec66a800063d10447aca920a9602841ff800056db2b2c910c4e340a7d2a1a82c690a894000031ba4270492337059c60a2f440002b6095a89f27f912b40001c0200000fa0001c4201d196ebf6000000025786bbb1bebd000007b091467da237abf8959ca3a81c8ba3044801c24126d106d08ea15322c694da70b01b800000003bd996882195b0050af8235ea2666f80334024170c70a8000a201dc85af13a491100008380000a9b9f8e000300e00014b46fe23368cf9cf462980000000d24000000000000000001bfa6e70000b02000081a8146231a5023a82d36000329c1cd25148221e386da05ce000243600000009082a4400000000893158000000000011a2615166a000119a00000009191f8600022389de9c5ebcf800000005f016f841c1fd960cbd310ac92ea200051000033528e84bc00009c7af52000002000031f6849957c2c09beaa32a3f0a922d1022930d8b101bdc9b190d629aafb6330819c08d95c69eb2d886f01ff43bc275600031403150148b1726aeaeea00e9f79c34bb58000305059a000000074a0bb8000098a2271c5c45f163c00585a20000f6400005e2000111e2c90ace7f8843ab89b11a82b2afe4c3b1ca51ba1b277e80005ca8da826f1cca00000000002364000088c84a000036685c6000171a7fe80000002cc449621580000000ab5800000020967cc1f0c41880007ac2db80000d380001e3c0000f9a4252504854af700d601aa0001cd41838000771928ca281c4ca5db0f4000326a5818e4c0000f2c081ac9819310eaa78268a5839c3852b1832390270658783fe127224425c0a9002d000000029140e79bc2a971f3e00000007190cecb029af85ccad3e2b090de62785de00018788179c90c2085a800009647ca800084b248600000000002bc02e30b468462e482ff06a67199f4e9f2acee57380000000000c260de0ae9000000004b886618060000e54aa10000a8
  | 53 => 0x681f1836c82c4a0d324a52884ba2f217182c8801e0000304b480e7044b15ae00014145178000a27a83a07d0548bd98c6c5d09f547209b186321aca1b52b56b288f1e743113400100007cd9ea20331848b8100004da0fc81e8117637396ea57120f6c5bafcc7ec80004550aae0000bc02ec240ec530000509b1bc0001aa2ab40ce45192c7423b01c6c6810886540538bfd1a78984a6ba665afe4b350a5e04a30c632d021079425c8bcd310843b8b3cc8831ecaf42d6630294a015a93f6471894277d2eda8fb13fc20987762be21aec9c11263af02a667a08980f6169625c96c4ca8877c6aa06525d0140c4b905a4ac9954c22ba42e9c52ca46b52d6a8dd29f4a2e0aa2bd79b787878a2e0488bdac8932be000197476594aa0000b660000c4200022580dfa8680000e560a52f2e0001602961122622a099c3b7885266e9f8860c177ebf22ac467e32281a9104088d84888d888c446225acc0588567f693201e706f017a2e545f7000085bb20438593f892713340b094be9e881747901a863ca8000254204aafd84ea52c00002eb80002a223d48dc20fe58a201e0402a70af216b091c29de76c0000ae4927c899304a00003ee4601744000084c81826706cf8eb27468f5293ba72800000005e49f600000000326a43c5e42e9ca8a000026881b084e15f493e800e90090ae99a80000000ae6aad84d80001ab8000007e00005c4c39218c0000000000000000025920001236b4a8000000111c56c95da582ae6a788000077308040000000c4700001751ffe0001fc474d95f05ae083a000000033f27f67231cc23cb8000b71800030a000012197e600025a6b3300000002746407057c5781d0a00021da00000002c81e024b320c6a699e0e64a88208c098e09ab22ba00016420000000aeca2868c00e62396aacc10518aa00000005a10d98481203275d9064b86063a2b4a90c4cc1b0699e81b424a80a68ee0ff857f8bb49cc2a9c000010e2b22b5a03fac480ef09123fa83808e6a17e8f691481aa84ce00005920001308bcb162426908660000000000000000027f41dd0f60804af1c0000000bdb141e0c42d1e00021b800012f4000000000028446111580a130b5eaa3b010620296c59a00006238b6075280b85ef84fa5152f5aa4f82886c800000000a1e69180001ce8f2247580f814921caa8f25708c39e6049780000000000525800074e80006b8a5e00000000a178000c36800087530bc00021d8000319e00000000e98a44000058207a18d8000004a0001dd60000000c2e93a016c273a14f00000000a3a7c0000000000000002e3a000000082ab0b600016a6ad4281a9830e0600027729de000008f80ec8be31f2c1aa182c50817e4c7217647d89ba4b600002a0325605e0000000000086b1f22173316662dace42da1c6a799918cc1d91ecc909c1437180
  | 54 => 0x7483609fbc140a33000b2c32057986eac4b0a40e89a50a21a2d268220d000010a628b23ee8eea9824d6b0ae00202e473916d011103da467ab3c3069666885860431287c0b451a5840494004daa47e89397722730b78c3ca564a691e3ea6faa1e614221e340275ebfd9e5a0001ed2a3d0ee20000af6411800017480000000814b73000034aa2eaa968000b0a000004b15080001f409e08bd8572953c1f20b6c030a80e9db9eec80331848a100860000000000090282980c648f000000000000000000845090a06f1d303ec800000a0000000182a00030a03838000394000099d800000000005dd00007ba26e84460dee0002c140002cd80001f72000122cb381da6000308abb4a0025018000a1b00006030286368277e39e9be4a31800000000000728000a5300000001b7045c0efa000207c48f887ac76142c43f801020380001340ab83ca316409214fa08001be00000009ec8000000000022b000000000008358000000311657d8758076b2aa6f6000097e2b0000006c80001b3800019521991408000328c68a00000a6892021c8746c2d221c3a48a72a8480000ae0000000000000009f600017f678480000000000000120e95b000018503d40001cbc01385a698030d20000fca000167434b9002393800073e862629211ce791115ca8918b8a14043031889be329aee400012500280a00c23ad9807630805f4ae0cc28991a48a11087ababbe0cc81eab9a19bc5cf82ce000277053d0e6e00026da58b0000000154400032a4bed2462c0522409a71a5a1d48000b419afa00000009fe0544bae11020000000981271a0cf06da2e11abc80c1b0ac5e1de0ba7969400027882ecb0ec000000033988de25f82d400005c83e600000000000000087886f17aac5f00004bb80001aba2240000968b1da64215004f27a20cb000001e6818800000019fcbfeac3e0be13aa6398fc2ac10b6a774a81c0001f7cc8f010abb430840000000138957a14805161180000000057200024306629a2abe18000b13059800003301658d48973000076eaa7a628000019382120000f4871d0b4e80f8938a9396d20b610dab87814e728a5602c78e7c00012a80002078850800098400002d400007db8ecc00000004eb19b44fa257a93f937c8cb800003980000d81afe32d82ea0e1204e000000000000000002c960f30b268ed0d706ee17e0862227400000004c682b49d50000128800000000000000bd200002ee0000000cac00000000b740000000b6310981998be89da049084f8af48c8af5664f0000000305e43c968077a1304a2b12a0b86affe00000000002ff034f0676000292e00011868271e762c28e86bd82b22000199e0001b5203a2aca1d7125a000208200030e65af9bd60001cce1fc08000001092000299c0002bf05dd8b80bc48d4a00000007b3000096894286
  | 55 => 0xc0887dc2b5839a68e15720001d1e00000005f8a4f400019360002af281f80003d5a348000086298c8000c8c9f8497713b440eb11298b21aa1f621489d10000c3d89e200001f24a40cea99c985a0001dc02de890c6b2149c703a260bcc17de72d079e11015d012f2cc2c9fa7921d125c0658020c8391d387a51b0e9b4197872211407cb22e6000142231c9ed4c78000084480001dc19e00001396c8d1f7a4cb19f20001b7600027160000bd40000000982000058e8bf034200000000000c830bca901a58000008b0c9ba8b2bee193497280006179fa47b900000002fb01e40f445d50000b6da8143ab210000000002bc80004722dbca5f1be800007d6aaa9cd6599000000006964341202a76ae8446b0a6092c110eae580009d38000977800072da7fa00000002f7127a0df00006a925a000027f284e8000a1b8000bec8000888a54aba20cee30da8de3b200003868000000000042900001ca19ec71faf9a36892ca60bb2640000ec40002ab82622e98987198c7c40dc03331ab400026240003200000000000000005f6091e3a327a000000005e8000000000000001916ab680008bb329e1168064b3e000096e0000067a2b60000000be100008b32eaa2931840437251a53f0aea000055a052862a1fd00006340000000241ca65220e08aaaf0c1f2b3a38b8e3c0002d243132334c9e0c56281a8a611d9a06000172e6e19a7014b1d5e1ca80e000000000908000000181a5c280000000000130205227289f0000000014a800000028ce89e1ce08238c161e5ae0289ba8ee6f40d5ea7a2c5a34c281eb7811b609f12c01a61a00a3804848a993b64468a461959a7eae795309678000abd99cac9c9e6cc919114a4f00006f6984693a800000025ba6a5a09ebf5899279ca0c4172ad3863022c09923086541819a3dc800000024c0877800034a0d182d231e650092a281416b48df25c4a36840a46e9d7e0000000109228820e00003518b4a17d9f7e008ac4611c000093802282c60a1060ead647e7a1a20000546b21a0e85a88aee7768c1c273a56853290c6a2d80f43e7a83c579220a8b513580003198427878ec6da00a7822e0e58c0ec643d0000ad10000a99a4b834e81d693c1c12347818e2e390a854280c85311b64c4a8522909b280b540cfa58d800073f00009042b0600000001030bce57e0000898ac580000ba60000000b8fb1760002fe064b00005529eaa84192ec00000000569b8cbde0b7000000007daaf5464780005c2157800002627270a3e0000000bfb068a6430baa7ee22fcc279f3875e9e9a76e2af88dd81107fd9986621968a3dd1b128f923cc16b29faac784a493307ee8a000005c715b8b66800071b80000002b9c000000000027ce00007ca03f00002c1800061480000002046a9f0b1c49e0506a3980000000050000218437c800099fa
  | 56 => 0x3d5123200026f829297947091fee4030000118acc8bbc80003c20be4b00829076a000071e100e0db80000000d624dc8f6e00000000002dea0000000678800077080006ec8000c1494560001a8a00030fa000000035f321a0001b408b80b14000091600000007f4030ec8712bc00013800002b0a119038e000227684d2a96022a636b969a363d8ad5e00000000002aea23e979e9058c60ca415be88a0d882f3000091500029982c186b3065000011a6c7f8f883c4a77c6c7acba47b800000000002db8eae5d588e297486d8bc380003c608709340000000000014d00005a080009179a2c62f031e31f0238550a3142d0ac8e9ef80000002b72c8c08825b680008730000b8897884c400001c5024c3a1000041280000000bde1b38f247ea881e9cb148209414440002d40806ab486a40b040000f3a30ea2ac9902e5c6bd887e6b615f217ba3324ef80006f48000000000000032a84cbb036000246007f0e1c00000009478000b8c17c6808043caab1120191058e4a387baaf818f67ed0faa4c4a474575a13610ba83e63c00001b99c584e2000092880004ff840400000005cc00b2a6f2fce0681690b328000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe956318d414400156d0d29a8288002ad61a53505102478ba9ca6a0a2047ab6869c9414400156b0d39282880a72d1da725051023dd9404e4a0a2000bb1809c9414400156f0cb92828811ead21972505100059bc2ae4a0a2048b34855c9414400172f06b928288002e520d7250510005d9c02e4a0a2047bb0805c94144117968ec3928288122cda1472505100059ac28e4a0a2047bb2801c94144001763003928288122cda1662505100059ac2cc4a0a2000e3465989414401f7630131282880166d21d62505100059bc2ac4a0a2048b3485589414400172f06b128288002e520d62505100add9c02c4a0a2000e3465189414408f765012928288002ec60252505100055bc32a4a0a2000ab486549414400172f06a928288002e520d525051023dd940464a0a2000bb1808c9414400156f0c9928288002ad21932505100059bc2a64a0a2048b34854c9414400156d0c1928288002ad61832505102459b42864a0a2000b35850c9414408f765001928288002ec60032505100155bc36e0a0a2001ab486dc1414408f968edb82828811eeca1f705051000dd9436e0a0a2001bb086dc1414408fb64edb8282882b76c1db705051000799b2ee0a0a2000f3065dc1414400176305b828288212eca1c705051023ed9438e0a0a2086bb2861c1414408fd650c382828811fcca14705051023f98c28e0a0a2000f33651c14144001e60ca382828811fe4a0c705051023fc8c18e0a0a2047fa2821c1414400176304382828811fe86087050510005d0c10e0a0a2000db2721c14144001b60e438282880971d1c765541100063bb2ee2a82204987e86dd530440d90fd0fb2a60880961f21f654c1100061e3a6ca9822000c3f65dd13044001878cbba26088003271d3634c110004db43a8298220009b4875053044001a6eeaa0a60881234d1d5414c11024c3e432eb902202587f87d9720440010fb0fb2e40881234d9d541c81100069abaa839022000db387506204408fb610ea0c408802f6c9d9418811023f593b2831022047f3275506204408fe62eaa0c4088003ccd9541881100079832a831022047f9273506204408ff22e6a0c4088003e8e094188110007d041283102200fdb1725062044001878e9b2a40881339a08365481100061fb2ee89022000c3c65dd12044001958e9b1240880032b1d062481100247b436e29022000c7465dc5204400136d0ea0a40880026d21d414811023fd0102829022025c7876d9520440938f0ec32a40880032e1db744811000735b28c49022000db38750520440017650ea0a4088002ec21d4148110006d843a8290220009b0875052044003b64eca0a40880076c1d9414811000799b2a829022000f30655052044001f4504a0a4088003e8609414811023ed9b92829022047fa3725052044001f46c4a0a4088003e81894148110
  | 1 => 0x8e9b2ac4880021fa1c65589100061e3a0cab122000c3f65dd16244001878cbba2c48800317d9773589100062e32ee6b122000c5f651cd62440018b8ca39ac48800e1fa1f75589100061fa0eeab122000c3d41dd5624400517d0fba2c4880030fdd774589100061e3aee8b1220008bf81dd1624400117b03ba2c4880021fe15745891001c3e42ae8b1220008df835d1624400f1b906ba2c4880023be0974589100047dc02e8b1220008be871d1624400187eea3a2c4880030f1d474589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100064fa0ee6b122000c9d41dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd6244001958e9b92c488003331cf72589100063a3aee2b122000cd473dc56244001970e9b82c4880023be1d621891000556422c43122000acc8358862440151d904ba0c4880021fe15731891001c3e42ae6312204cc7a70d9652440031f10cb84a48801e37a0e76549100046ec1ceca92200087f855d9524400117f08bb2a48800a2f21176549100046fc1aeca9220078dc835d952440011ef02bb2a48800e1f21476549100543f43ecaa922000c5f65dcd52440738b8cbb9aa48800317d94735491019e2e328e6a92200087f855db32440070f90abb664880021fe15768c91001c3e42aed19220018f8865c232440070fd0bbb264880021f617764c91001c3f42cec992200087d859d932440010ff0abb2648800e1f215764c9100045fc22ec99220028bc845d932440011bf06bb264880023be09764c9100047bc0aec992200387c851d932440010fd0dbaa64880021fa1f654c9100043e43eca992200387c859d832440010ff0abb0648800e1f215760c9100045fc22ec19220028bc845d8324400f1b906bb0648802a3b209760c9100043e432ea192200087f87d9432440010fb0fb2864880123d219710c91000c7c432e01922007cd8635c032440159d0c4b806488002ade19755051023d5a432eaa0a2000bb3805d5414408f76100baa82882bb8d997655051024d9b436caa0a2000e3776d954144001c68edb2a82880978dd83655051012f99b06caa0a204bbb380595414404b66d0c32a82881238da1865505100071bbb0caa0a2000e34761954144093c6ec032a8288127ccd8065505102459b42ee6a0a2000b3585dcd414408f56d0d39a8288002ad61a735051016e5a3b4e6a0a2048b36859cd414400166b0b39a828811eeca027350510005d8c04e6a0a2000ab7865cd414408f5690cb9a8288002ece01735051023dd8402e6a0a2092cb4761cd4144001c68cbb1a8288122cda1663505100059ac2cc6a0a201abb18098d414400b3690eb1a8288002cde1563505102459a42ac6a0a2000e346558d414400174f04b1a8288002e92096350510105d9c02c6a0a2000
  | 2 => 0x77558e100145f43ee8b1c2000c3f75dd16384001878ebba2c7080021fe157458e1001c3e42ae8b1c206a8be871d1638400187eea3a2c7080030f1d47458e100164e3a486b1c20048dc8750d6384005938e8a1ac70800e972156394e1027c3fc2aeca9c20008bf845d9538400517908bb2a7080121f21d6554e100246e43ac6a9c2000c3f415d6628400187a82bacc50800a2fa1f7458a102c45f438e8b142002cac7490962840091d90ea12c5080121fe1d6594a1000537c12cb294200a87d85dd9528400117f08bb2a50800a2f2117654a100046fc1aeca9420078dc835d952840018beca39aa5080cf171947354a100043fc2aed994200387c855db32840091bf0eb1c65080e697215638ca100266d382c7194200087f855d932840070f90abb265080022fe11764ca100145e422ec99420008bf845d8328400517908bb0650801f1798d750ca1019d2e42ac61942000c5d7558c3284001970e9bb241080030f5d254d95100053ac0ca9b2a200287f8755365440014bf06b26ca880029720d64d951000537c12c9b2a2000a6c8259365440994e90ca0eca880038d19141d95100061eba0e9b2a2000a5e831d365440014bb063a6ca880969da0474d95102653ac08e9b2a2000c5f739cf65440018bae639eca880021fa1f43d95100043ec3e87b2a2000a5e83dcb65440014bb07b96ca880969e60072d95100043f43885b2a200087d8710b65440010ff0aba2ca8800237e0d745951003c6e41ae8b2a20008ef825d165440151d904ba2ca880021f61e64195100043fc3ac832a2000a5f8359065440014b906b20ca880029be09641951000536412c832a204aa748650465440010fd0fb2ac6880030f1d36558d100043f438cab1a2000c3c74195634400187ecbba2c6880030f1977458d1000637b2ee4b1a2000c6c65dc963440018deca392c6880031b1947258d1001c3f43eeab1a2000c3f41dd5634400187a83baac68800a2fa1f7458d100061fbaee8b1a2000c3c75dd1634400117f03ba2c6880022f6077458d100043fc2ae8b1a200387c855d163440011bf06ba2c6880023be097458d1005476412e8b1a20008be871d1634400187eea3a2c6880030f1d47458d100064e3a6e6b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000caf41dc9634400195a83b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d1000657a08e4b1a2000cad411c963440019c8e5b8ac68800237e1d6318d100054e422c631a2000acc8258c63440014bb07b2ca6880021fe157654d100045fc22eca9a20028bc845d953440011df04bb2a68802a3b2097654d1003c3f43ecaa9a2007a5e83d95534400187e82bacc4880030f50575989102643e436eab12200087e87d95624400187
  | 3 => 0xd98a40028bc845db3148001878c8bae62900030f9d764cc5200061ebaec998a40008df8758f314805d4b90ab1e6290006b520563cc5200063b3aec398a40028be84dd9314800117b09bb2629000e1fa14764c5200043ec28ec98a40018dc8758d31480594b90ab1a6290006b5205634c52000656324ed90a4000c3c64dd5214800187eebb2242900030f1d764485200064fb26e690a4000c9c64dcd214800193ec839a429000327190734852018e6a308e690a4000c7475d8521480019a8e7b0a42900032e19370485201fe363b6ea90a407fc6c761d521480b1958edb2242900e3331db734852018e663b0e690a4000d4c751cd2148001ad6ea382429000372dcc704852000637b2ee4a82400087f855d930480070f90abb260900022fe11764c1200145e422ec98240018f4815d93048001878c9baa609013f5a083754c1200045f436e898240b18be87d9130480d71790fb2260900030fdd7644c1200061e3aec89824000c5c75d8d3048001878c8bae409002b5a08175c81200061f3aec99024000c3d75d9320480b1974edb26409002b78c8571c81200055c432839024001cba7650720480011bf06ba2ca1001e3720d74594200243e43aa8b28400387e87dd563080010ff0aba2c61000e1f2157458c200246e43a86b184000c3f75d056308161878eba0ac61000e972156394c2027c3fc2aeca98400487c8759553080091b90eb1aa6102bf17d94735482057e2e328e6a90400087f855db32080070f90abb6641000e1fa1f75584200061fa0eeab084000c3d41dd561080010ff0aba2c21000e1f21574584200046fc1ae8b0840078dc835d161080091f100ba2c2100123d21d41584202643fc2aeca88400487c8759551080091e90eb0aa210006ad20776504200051fc2aeca08402fa3c855d9410800153f06bb2821014aa720d76504200055bc0aeca084047ab8805d9410808f970e0bb282100028fe15635042017d1e42ac6a084000aad86dc9410800155b0c39282100036a1c072504200155b43ac2a084002ab4875854108001c6f0ab0a82100038d215615042000753b92c2a084000ea472585410808fd60e0b0a821011fa9c81615042023f59102c2a084047ea5205854108001d62c3b82821001f1798d75cc4201752e42ac79884000c5d7558f31080010ff0abb2621000e1f215764c4200246e43ac6988402ca5c8558d3108015998e4b1a62100032e1d376480200063d42eec9004000c7985dd920080159d4a5bb240100032ed0776480200065dbb6e89004000ceb76549200800179706a924010002dae1532480200577190ac290040009b8875052008001976eca0a4010003ac5854148020005b5c2a429004000bcb8348520080011bf06ba2cb0801e3720d74596100243e43aa8b2c200387e87dd5638400187e83baac7080030f50
  | 4 => 0x34800196ee9b8ac6900032d1d37158d200065bc26e2b1a4000cb484dc563480018eeea38ac6900031d1d47158d200065bba0e2b1a4000cb4741c563480019aee638ac69000339dc87158d200045f43e82b1a40028bc87d05634800187eeba0ac6902c30f1d74158d200065bb8e82b1a4001cb471d05634800187cebb20c6900030f5d76418d200061f3a8c831a4000c3d7519063480011bf0eb18c690002972156318d200056a40ac631a40008bf845da534800517908bb4a6900029760f6594d200070fa9ec929a40028be84dd9534800117b09bb2a6900022fe117654d200145e422eca9a40008df835d953480011ef02bb2a6900063d2057654d2003c3e43acaa9a4007a5c8359553480834e902b2aa6900123ba1b7254d20024f5406e4a9a400487f8759652480e74b906b2ca4900529be0965949201fd3a40acb2924000c9f64dcd5248001938c9b9aa49000317d94735492019e2e328e6a924000c9f641cd5248001938c839aa49000e1fa16768c9200043ec2ced19240048df8758e32480734b90ab1c64900e2b5205638c9200061e326ea9924000c3f75d913248001878ebb226490003171d7634c9200246f41cec1924000c3c645d4324800187cebb2064900030f5d7640c9200046fc3ac61924033a5c8558c32480635a902b1864902cad3215320c9200045fc22ebb0a40028bc845d761480011bf06baec29001e3720d75d85200055ac0ee9b0a4000ab5811d361480010ff0ab9ec29000e1f21573d85200045fc22e7b0a40028bc845cf614800517d0dba2c2900022fa1f64585200061fbaec8b0a4000c3c75d91614800117d0e322c2900030fdd464585200061e3a8c8b0a4000c9f64dcd6148001938c9b9ac29000327d9073585200064e320e6b0a4000cd4611cd614800517d09bb2a2900022f613765452000c3e43acaa8a4070a5c8359551480034e902b2aa2900022fa1a76505200055ac0ceca0a4000cb5819d9414800196e213b282900028fe15765052017d1e42aeca0a4000a9f835d941480a553906bb28290002abe0976505200055bc0aeca0a4000abb805d9414805f47d0a3b282900028f61476505200061f428eca0a4000c3d851d9414800195b043b2829000a2fe0476505200145ec08eca0a4000caf211d9414800195a423b282900032b880765052000656100eca0a4000cb7101d94148001974203b282900032e44076505200045fc3acaa0a40008bc87595414800153f06b2a829014aa720d65505200055bc0acaa0a4001ab481595414800117f0eb1a82900022f21d63505200051fc2ac6a0a402fa3c8558d414800156f02b1a8290006ad205635052000557434e4a0a4000cac769c941480ab74b03392829011eab2197250520006563b2e4a0a4057ba7815c9414808f75100b92829000637a0e76cc5200045fc22e
  | 5 => 0x31799773486200062eb2ee690c40008dd861cd21880018bcca39a43100031759473486201c46f43cc690c40078dc8798d21880018beeb31a4310003171d663486201c46f43ac690c40318dc8758d21880018beeab1a4310003171d563486200052f41ca3b2a4000a6d829476548001968e2322ca900032719373595200062e328e6b2a4000c9c641cd6548001968c9b8aca9000a2fa1f74595200045ec0ee8b2a40008df835d1654800f1b906ba2ca900023de05745952000c7a40ae8b2a40008be871d165480050f90eaa2ca9000b0f1d154595205a62e39aa8b2a4097c7471551654800f1bd0fb9aca9000327dd373595200064e3a6e6b2a4000c5f751cd654800193ee839aca90003271d0735952000c7b43ee2b2a4000cb774dc56548001968e9b8aca9000335dcf71595200066a39ee2b2a4000cb784dc5654800196909b8aca900031ddd471595200065bba0e2b2a4000cb4741c565480019aee638aca90003351cc71595200045f43e82b2a40028bc87d05654800193ee7a0aca902cf271cf41595200065bb8e82b2a4001cb471d05654800117b0f32ec8900022fe1d65d91200054fc1acbb224000a9c83597644800156f02b2ec890002ad20565d91200845ec38c3b224000a3e85187644800147b0a30ec890002a7a0c61d91200054ec18c3b224000cb571187644800187aea3aec890002a7a0c75d91200054ec18ebb224000a3f855cf64480014790ab9ec8900028fa1473d91200051ec28e7b224000a3f855c764480014790ab8ec8900030fe1571d91200061e42ae3b224000a3e851c7644800147b0a38ec890002a7a0c71d91200054ec18e3b224057aae821c764480b155b0438ec890162aea0071d91200055cc00e3b2240008be87947644800117b0f28ec890002a7a0e51d91200054ec1ca3b2240008be87147644800117b0e28ec8900022fa1e31d91200045ec3c63b224000a3e858c7644800147b0b18ec8900022fa1c31d91200045ec3863b2240008bd87887644800117d0e10ec8900422f61c21d91200051f42843b224000a3d85087644800153d0610ec890002a760c21d91202c55d40043b224000a3e85dc3644800147b0bb86c890002a7a0f70d91200054ec1ee1b224050aae82dc3644800117d0f886c8900022f61f10d91200062ebaea7b1a400087f855c763480070f90ab8ec69000297a1631d8d200045f43ec8b1a4000c3f75d916348001878ebb22c6900032d1c76458d200045f438c8b1a4000c3f751916348001878ea322c6900032d1c46458d200065bb26e2b1a4000cb464dc5634800187eebba2c6900030f1d77458d200045ec0ee8b1a400087f855d163480070f90aba2c6900023de057458d2000c7a40ae8b1a4000c3f751d16348001878ea3a2c690003171d77358d200063bbaee2b1a4000c7475dc56
  | 6 => 0x256d4004331c4000ad98008663880091bd0fa9ac71000317dd75358e200246f43e86b1c4000a5e85d0d63880014bb0ba1ac7100123721d4358e200164e3a286b1c400387e85dc563880010fb0bb8ac71000297a163158e200052ec2c62b1c4000a9e848c5638800153b0918ac710002a7a103158e200054ec2062b1c4000c5f759d5638800153d093aac710002a76127558e200052f42ce8b1c4000a5d859d1638800193ae83a2c71000387d525458e200052fc2ae4b1c4000a5c855c9638800153f08b92c710002a72117258e200056bc0ae4b1c4000ad4815c963880014bd0a212c710002976144258e200052f42ee2b1c4000a5d85dc563880014bd0b38ac710002976167158e200054f424e2b1c4000a9d849c563880095b50138ac710002b66027158e2000567c12e2b1c4000a9e841c5638800153b0838ac71000237a1e5158e200046ec3ca2b1c4000a9e84945638800153b0928ac710002a7a105158e200054ec20a2b1c4004ada8014563880015b30028ac71000297a174158e200052ec2e82b1c4000e1e85d056388001c3b0ba0ac71011ea76124158e200054f42442b1c4000a9d8488563880011bd0e10ac7100023761c2158e200052f42842b1c4000a5d85085638800153d0810ac710002a76102158e200256d40042b1c4000ad98008563880018bea6bb4a7100121fe1d6594e200052fc1acb29c4003a5e8558e53880090f90eb2aa7100123721d6354e2000727a92c729440008dd86dcd52880738bccbb9aa510003175977354a200046ec30e6a944033c5e651cd52880018baca39aa5100e637a1e6354a2003c6e43cc6a9440398de8758d52880671b90eb1aa5100031e5977054a2003e6d31ae1994400087d86dd532880e78bcc7baa65101ce1fa1d654ca2052c3e43aca9944000c5f7558d32880018b8eab1a65100033658f704ca2019c3fc32ea1944007c5e635d432880290ff0eb286510003179d5630ca200062ebaac619440078de83dd561880011bb07baac31000e1fa1773586200043ec2ee6b0c40048f48750561880090f90bbb2a3100121f21d655462000d5a40eeca0c4000ab7815d941880a387ee2b2a83100038ddc5655062023f1b882caa0c4047e351059541880a393ee331a8310003a5dc6635062023f4b884c6a0c4047e951098d41880a393ee2b1a8310003a5dc5635062023f4b882c6a0c4047e951058d418800556d0eb0a831000aad21d615062000753b92c2a0c4000ea472585418808fd4e40b0a831011fa9481615062001c3f42aed98c400087f865d7318800f8bcc6bae63100021fe1d65cc6200043ec3acb98c4000c5e7558f31880018baeab1e63100123721d634c6200063732ee498c4000c6e651c9318800199ac639263100021f61b75486201fc3f43aca90c407f87c8759521880011bb0db9a431
  | 7 => 0x5e65dcd52c80018bacbb9aa5900cf179947354b200062eb28e6a96403787d86dd532c802d0f90eb2a659002b930c9654cb2001c3f42ee6b0e400087d85dcd61c800517d09b9ac3900022f61373587200543e42eeca8e400187c8759551c805f47d0b3b283900028f61676507202954f41ceca0e4000a9d839d941c800156b033b28390002ade05765072017d1f428eca0e4000a3d851d941c800147b0d32a8390002ade05655072000d5a40acaa0e402fa3f8659541c8001c6f02b2a83900038d20565507200061fb8acaa0e4000e377159541c8001c6e20b2a83900022fa1f63507200045ec3ec6a0e402fa3e85d8d41c800147b0bb1a8390002ade05635072000d5a40ac6a0e4047aad869c941c80b574b03392839016ee9e05725072023dd4402e4a0e4000cba761c141c80017530438283900036a9c8705072001c3f42aed98e400087f865d731c80010ff0eb2e63900021f61d65cc72000c6e43ac698e402887d86dd521c80010fd0eb2a439005a1f21d65487200062f32ee690e4000c5d65dcd21c80018bcca39a43900031759473487205ae67bb0e690e4000d4c751cd21c80018dacbb92a1900021f61b754c3203743f43aca986406c87c8759530c8001878e8b2a61900030f997744c3200061eb2ee89864000c9c7458d30c80090fd0f2a2cb100030fdd254596200243e43aa8b2c4000a3e84945658800147b0928acb1000297a0e51596200052ec1ca2b2c4000c7771945658800187ee93a2cb1000317dce73596200043f43e86b2c400087d87d0d658800147f08b92cb100028f21172596200052fc1ae4b2c4000a5c835c965880014ef02b92cb100029d20572596200a43f43884b2c400087d87109658800147d0938acb100028f61271596200052f41ce2b2c4000a5d839c565880018eee338acb100129ea0271596200053cc04e2b2c4000a3e841c5658800147b0838acb100021fa1f41596200043ec3e82b2c4000c3e87d05658800187b0fa0acb1011e8f61241596200043f43c62b2c400087d878c5658800147d0918acb100028f61231596200051f42062b2c4000a3d840c565880094f50018acb100029e60031596200051f42442b2c4000a3d8488565880290fd0e10acb100021f61c21596200051f42042b2c4000a3d8408565880014bd0610acb100029760c21596200253d40042b2c4000a79800856588001c3ea92a4c71000297a144298e200052ec288531c40078de8794663880011bb0f28cc710002a7a125198e200054ec24a331c4000a9e84146638800153b0828cc71000297a174198e200052ec2e8331c4000e1e85d066388001c3b0ba0cc71011ea76124198e200054f4244331c4000a9d84886638800f1bd0e10cc7100023761c2198e200052f4284331c4000a5d85086638800153d0810cc710002a76102198e200
  | 8 => 0x738aca180028fa1071594300051ec20e2b28600087e87d05650c0010fb0fa0aca180030fa1f41594300061ec3e82b286051e1f30d05650c0a3c3a61a0aca1811e8f61241594300052fc1a82b286007a5c83505650c00147d0910aca180028f61221594300043f43842b28600087d87085650c00147d0810aca180028f610215943003d2f41842b286000a5d83085650c0094f50010aca180029e60021594300043fc2ae3310600387c855c6620c0091d90ea12c4180e637e0d765483003e2e39acaa906039c5e65dcd520c0018bacbb9aa4180063760f755843003c6e41ae8b0860048f487505610c0090f90bbb2a2180121f21d655443000d5a40eeca086052a9c835d9410c00156f02bb2821814b871cd655043028e1fb8acaa086000e3771595410c08fc3e60b2a821811f874c1655043023f1b882caa086047e3510595410c00153b0db9a82180038759773504300155b43ac2a086002ab487585410c001d2ee6b0a821814ba51cd615043023f4b982c2a086047e9530585410c0070f90bbb242180021fe15764843001c3e42aec90860388df835d9210c0010fb0dbaa42180021fa1d65484300043e43aca9086007c5c73595210c0018bccbb9a421800317597734843003e6639cc490860048ec87589210c00f998e6b12421802a9ba0a64997200051f424c332e4000a3d8498665c80154dd0530ccb9002a1fa1e54597200061fba4a8b2e400a87c8755165c800147d0928acb900028f61251597200052f41ca2b2e4000a5d8394565c80154dd05322cb9002b8b90a64597200051f424c2b2e4000a3d8498565c80154dd0530acb9002b99c8661597205861fbb682b2e4000c3f749d165c80014bd073a2cb900029760e745972005537414e8b2e4000a6d829d165c80014ed033a2cb900029d60674597200062fb9ce6b2e400aa6c825cd65c80018bae639acb900021fa1f43597200043ec3e86b2e4000a3e849c565c800147b0938acb9000297a0e71597200052ec1ce2b2e400aa6e829c565c80014db0538acb900028fa1071597200051ec20e2b2e400087e87d0565c80010fb0fa0acb900030fa1f41597200061ec3e82b2e400087e878c565c80010fb0f18acb900028fa1231597200051ec2462b2e4000a3e840c565c800147b0818acb9002a9ba08315972000536c1062b2e4000a3e8488565c800147b0910acb900028fe1170597200051e422e0b2e4000a5f835c165c80014b906b82cb900029de0570597200053a40ae0b2e4000a3e84c4165c800147b09882cb900022fe0574d8f200145fc3e83b1e40008bd87d0763c816187ceba0ec7900030f5d741d8f200546f43e86b1e400387e85dc563c80010fb0bb8ac79002a1fe1d6594f200052fc1acb29e40048ec825d953c80150f90eb2aa79001e9720d6554f2000636b2ee4a9e4039c
  | 9 => 0x76505300065b884eca0a6000a3f855d9414c05f4790abb28298002a7e0d765053000557c12eca0a6000aac825d9414c00156f02bb282980032760c76505300145fc08eca0a60028bd811d9414c00193e623b28298003274c476505300064f180eca0a6000c9c301d9414c00196e203b28298006ada0765505300055ac0ecaa0a602fa3e86d95414c00187cedb2a82980030f1db65505300071b40ecaa0a6000e3581d95414c00187ee3b2a82980038ddc765505300071b886caa0a60008bf87595414c0011790eb2a82980028fa1865505300061f3b0caa0a6000c3c76195414c00153d0d39a8298003271da73505300058ec2ce6a0a605eb95819cd414c08f5390cb9a8298003271d97350530305cbc0ae6a0a6047b98805cd414c001938ed29a82980bf871965350530005cac0ca6a0a6047a9c8654d414c001938eca9a8298006ada0462505300055ac08c4a0a6000c9c768c9414c113c38cb192829811ee6a0232505300064e3b064a0a6000b1d850c9414c111c38ca1928298002e560432505300064e324ed98a602e8dc865d7314c05d8bf0cbae62980bb1721975cc5301742e432eb98a6000d1c645d7314c0cda3e82bae629819b4750575cc53003e2fb02eb98a6007d5b605d7314c0012bf0fb2e62981b297a1b65cc530004aec38cb98a6000e1c64197314c001a3aebb2662980038719764cc5300062e32ce598a60049da809cb314c0598b8cbbaa629801237219754c530004e6412ea98a602ca5e86d95314c09f8b8edb2a629800395187654c53036e2e3b0ca98a6000e1c64195314c0d5938edb22629800387197644c5300074a30ec898a600095d851c9314c0018b8ca39262980c637a1f624c53000666396c498a6000e5465d85314c0010ff0abb6429800e1f21576c85300045fc22ed90a60028bc845db214c0091bd0db9e42980031719773c8530024ed406e790a600387e85dd9214c0010fb0bbb2429800a2fa1376485300045ec26ec90a600387e859d9214c0010fb0b3b2429800e1f214764853003c6e418ec90a600087e86dd5214c001878c9baa42980021fa1f65485300043e43eca90a606ec5c73d95214c00187eebb2242980030f1d7644853035e4e39ec890a6000c5f65dcd214c0018b8cbb9a429800327d9373485300064e326e690a606ec5c73d95504c0018becbb9aa098003271937354130024ae43aa6a826004a5c8654d504c0096b100a9aa09801e3720d74594300243f43ca8b286000c3f74951650c0090f90eaa2ca1801e9720d54594300051f424a2b286000a3d84945650c00f4bd0728aca180030fdd274594300052fc1ae8b286007a5c835d1650c00f4b906b92ca1801e97a0e42594300052ec1c84b28600087e87109650c0010fb0e212ca180028fa1271594300051ec24e2b286007a5e839c5650c0014bb
  | 10 => 0xa9a604fc5c76d95534c0d5938edb22a69801e576177154d3027eadba8e0a9a60b6c9d73193624c00159b0610ec498002ba60021d89300061f3a6cb3126000c3e74196624c00187ecaba4c4980030f19574989300061f3aec93126000c3d75d92624c00187cea324c4980030f5d464989300043f43ecab126000c3c74d95624c0018e8e3b2ac4980021fa1c65589300061e3a0cab126000c7471195624c00187ecbba2c4980030f19774589300045f43ec8b126000c3f75d91624c001878ebb22c4980032d1c764589300045f438c8b126000c3f75191624c001878ea322c4980032d1c464589300063bb2ee2b126000c7465dc5624c00196ec9b8ac4980032d193715893000477c3ac43126000ae481588624c0010ff0ab88c49800e1f21571189300045fc22ed29260028bc845da524c0018bced29ca49800a2fa1376549300045ec26eca9260078dc831d9524c0dd8b8e7b2aa4981af271cf64549300062fb2ee6a926039c5c65dcd524c00193ec9b9aa498003271937354930024ed406e6a92600795c8754d524c0074b90ca9aa498003171d953549300246f436eb19260049da80dd6324c0738b8cabac64980e697a1b658c93027e2f3b6cb192604fd5a70d96324c0db8bcec32c649800387190658c93036ead380cb192606ac9e76d92324c001c38cbb2464981ab669c3648c93000727b2ec51926000e4c6518a324c0012bf0ab8c649800317195718c930024edc3ae1192606d87e86dd5324c001878c9baa64981cf560c3754c9300043f43eca992606ee4c32d95324c00187eebb2264980030f1d7644c9300064e324ec19260338dc865d4324c0678bf0cba864980cf17219750c93019c2e432ea1926000d1c645d4324c001a3e82ba8649801f17d81750c93003eadb02ea192600095f87d94324c0d94bd0db2864980025761c650c9300070e320ca1926000d1d75d90324c001c38cbb2064980c637219710c9300062e32ae21926000c3c74d97614c001878e832ec2980022fe1175d85300145e422ebb0a60018dc835d7614c00156b03ba6c298002ad60474d85300045fc22e5b0a60028bc845cb614c09f0f90dbaac2980021fa1f65585300061e3a6cab0a600087e87195614c001878e832ac29800a2fa1b74585303545e436e8b0a6000c3f65dd1614c001878cbba2c2980022fa1f64585300061fbaec8b0a6000c3c75d91614c00117d0e322c2980030fdd464585300061e3a8c8b0a6000c6f65dc9614c0018d8cbb92c2980032bd93725853000656326e4b0a6000c6f651c9614c0018d8ca392c2980032bd90725853000656320e4b0a6000ce4611c9614c00517d09bb2a2980022f613765453001c3e428eca8a600187e87d95514c0018b8ed29aa2980be8fa1776505300051ec2eeca0a60008be869d9414c00156b033b282980032d606
  | 11 => 0x4c0050ff0eaa6ca980028fa1251d95300051ec24a3b2a6000a5d83947654c001c3b06326ca980028f60464d95300070e32487b2a604fa5c8650f654c001c38c8a1eca980028fa1261d95300051ec24c3b2a6000a3e84187654c00147b0830eca980028fa1b41d95305861f3b683b2a6000c3d741d3654c0dd4bd063a6ca9813e9760c74d95300053b408e9b2a6000a75811d3654c09f8b8e6b9eca9813e1fa1f43d95300043ec3e87b2a604fa5d83dcb654c0010fd0e216ca980021f61c42d95300051f424e3b2a6000a3d849c7654c00147d0838eca980028f61071d95303752f418e3b2a604fa5d831c7654c0010fd0fa0eca980021f61f41d95300061f43e83b2a6000c3d87d07654c0010fb0f18eca980028fa1231d95300051ec2463b2a6000a3e84887654c00147b0910eca980021fa1c21d95300043ec3843b2a6000a3e84087654c00147b0810eca981ba97a0c21d95300052ec1843b2a604fa7a80087654c0014f30010eca9813f1e1c170d95300051f42621b2a6000a3d84c43654c001878cbba2ca9800a2fa1f74595300061fbaee8b2a60008bd81dd1654c0010ff0aba2ca9800237e0d74595300045f438e8b2a6000c3f751d1654c001938e9b9aca980022fa1f41595300145e43e82b2a600087d87990654c0010ff0eb20ca9800297e0d64195300070ec18c832a6000e1e73190654c001c3ae6320ca980028f60464195305bf0f180c832a60b7e1c30190654c0014bd0d218ca9800387192431953036d2e4328632a6000e1c6450c654c00147d09308ca980028f61261195300052ec1cc232a6000a3e84184654c00147b08308ca980028fa1b41195300061f3b6cbb2260008bd87997644c00147d0b32ec8980022fe1d65d91300051f430cbb226000c3e76197644c001c3b0632ec8980030fd9571d91300061e32ae3b226000a3e85987644c00147b0b30ec89806e2f61c61d91300065ab88c3b226000c3d751d7644c0d753d063aec8981aaa760c75d913035f0f29ea7b22606ba9e83dcb644c0d553b07b96c8980028fa1672d91300051ec2ce5b226000cb7719c7644c00147f0ab8ec8980028f21571d91300061fc2ae3b226000c3c855c7644c0d753d0638ec8981aaa760c71d91300045f43ca3b2260008bd87947644c0d753d0728ec898002a760e51d91300045f438a3b2260008bd87147644c00117b0f18ec8980028fa1631d91300051ec2c63b2260008be87887644c00117b0f10ec8980022fa1c21d91300045ec3843b226000a3e85087644c00147b0a10ec8981aea7a0c21d91300054ec1843b22606aaba80087644c0015730010ec8981ab8e94350d913035c5f43e21b2260008bd87c43644c001938c93b4a69800e97a1b6594d300062f3b6cb29a6000e1c65d92534c0738b8cb394a6980b3171957194d3027e3c386ca
  | 12 => 0x121fa1b758c95001c3e428ec992a00a87c859d8325400117f08bb064a800a2f211760c9500062ebaec6192a00187c855cf615400117f08b9ec2a800a2f21173d85500045fc22e5b0aa0028bc845cb61540db0fd0db9aa2a81721fa1872545503fc3f43ec4a8aa000ab5819d9415400147f0abb282a8002a7e0d76505502954e41aeca0aa000aaf825d9415400155904bb282a8002ade05765055023d1e432eaa0aa0b9b37815d54154001c5ec529282a801e1f21676cc5500045fc22ed98aa0028bc845db31540031b906bb662a8003175d763cc5500243e432ea98aa00096c825d531540031bd0fb1a62a80022fe1176c85500145e422ed90aa0008df835db215400f1b906bb642a80121fa1b75c855003c6f41cec90aa0008dd839d921540070f90a3b242a801e97a0e51597300043fc2ae3316600387c855c662cc0070fd0fbaac5981cf171cf7558b3052e2e398eab16600087f855d162cc0070f90aba2c5980123720d7458b300061fbae82b1660b0c3c75d0562cc0091b906bb4a5981cf1794d7694b300246e41aeca966007c5c7359552cc00f8b8eca9aa5980e697215768cb301cc6fc32eb1966039c5e655d632cc0734b90ab1465980e237e19718cb30004afc2ae319660028be84dc961cc00117b09b92c3980061f61776547300246f41eeca8e6070c5e53dd951cc05f47d0bbb283980028f617765073023d4f41eeca0e6000ab7815d941cc17172f02b9a83980028fe15625073017d1e42ac4a0e6000ab78158941cc00356902b1283980b23761b754c7301662f32eea98e60009cc825d531cc0012bb0a39263980b297215624c73000666392c498e600087f855db21cc0070f90abb643980123720d76c87300043fc2aec90e600387c855d921cc0091b906bb243980125721d53543300243e43aa8b2c6000a5f83551658c0018bf06bacc5180031720d7598a3005636412eb314604ec5f305d6628c09d8ba60bacc5180031b5d75298a305861f3ae833146000c3d75d06628c0018deeba92c5180123b21d4258a3000537c12cb294600a87d85dd9528c0018d8eb31265180031b1d5624ca3001c3f43eeab0c6000c5e83dd5618c0018bb07baac3180030fd0775586300061ea0eeab0c604cc5f30dd5618c0998ba61baac3180021fe15745863001c3e42ae8b0c60048f487505618c0990ff0abb2a3180121f21d655463000d5a40eeca0c6000a3f855d9418c05f4790abb28318002ade05765063017d1f42cc4a0c6000a3d85989418c00556d0eb0a831800aad21d61506300071bc2ac2a0c6000e3485585418c001d2ee6b0a8318003a51cd615063023f4b982c2a0c6047e9530585418c0010ff0abb2431800e1f2157648630006363acc490c6000ccf73989218c0091d90eb1243180031b1d562486300061eba4a9b2a6000a5d8395365
  | 13 => 0xc6e438c6a92427f87e86dd532484e78b8c7baa6490a961fa1f654c9211fc3e43eca9924200c5f75d8d32484018b8ebb1a64908e3351c7634c92119c3e432ea1924207c5c635d432484010ff0fb2864908a21f61f650c9210062f3aec61924200c5d75d8c324847fccec5b2e4290802ba60840d812100578c0881b024200c5f659ce60484018b8cb39cc09080317d9573981210062e32ae73024200c5e75d8e60484018baebb1cc090803179d463981210062eba8c7302423f87c86dd560484010fd0fb2ac0908030f1d365581210043f438cab024200c3c74195604840187ecbba2c0908030f19774581210062fb2ee6b024200c5c65dcd60484018beca39ac0908031719473581210046f43ec6b024200c5f75d8d60484018b8ebb1ac09080327dd363581210064e3a6c6b0242008de8718d60484018beea31ac090803171d463581210064fba0c6b024200c9c7418d604857599ee431ac0908023ee1d60181210055c422c030242048dc8750d63940014bf0aa1ac72800b271d14358e500043f43ca2b1ca06ea5e8394563940dd4bf0eb1ca7281b717e1d6394e500070fa0ac729ca00087f865ca539409f2f70cb84a7281b31ee197094e500069da0ae129ca00087d8794e62940010fb0f28cc52800297a0e5198a5000536c14a3314a0048ec875096294001ab0e039aa5281bb17a187354a503762ec30e6a94a000c5f641cd52940018bac839aa5282bf179887354a50006a7310e6a94a000d4d621cd5294001a3e8239aa5281b3179807354a5019ead300e6a94a00087c8758d52940dd8b8e6b1aa52800356dcf7054a500062ebaac7194a06e95c835d4329400f8bcc6ba86528003175d5630ca5000636baac4194a0008df835d1619400f1b906ba2c3280021fa1e53586500043e43aa4b0ca000a5c8354961940091e90ea0ac328006ad20776506500054fc1aeca0ca052a9c835d9419400156f02bb283280030f5db75506500070eb1ca6a0ca025b368194d41940016730129a8328002c720d525065012d9a40aa4a0ca002ab68758541940055690eb0a83280978de15615065012f1a42ac2a0ca000e3775585419415dc68eab0a83280038d94d61506505771a29ac2a0ca0aee37525854194001c6aa4b0a832811f8dd41615065023f1aa82c2a0ca02595c835d7319400f8bcc6bae6328003175d563cc6500246e43ac698ca000c5f7558d31940dd2b906bae432800237e0d764865003c6e41aec90ca000c6f759892194001998e731243280123b21d62486500066639ac490ca000a5d85d0f63540011bf0eb18c6a8002a72116318d502e43f430e4a9aa04a87e86dc5535414b0ff0ea9ec4a81bb17d94735895000477c3ac4312a06d87c865ce52540230fb0fb14a4a80469b61f629495000636c3ec5292a000e2f41d8a52540950f90cb8ca4a8
  | 14 => 0xc651cd65484010ff0aba2ca9080237e0d745952103c6e41ae8b2a42008fb805d165484091f100ba2ca9081e37a1f73595210062fbaee6b2a4200c9f41dcd654840193a83b9aca9080317dd473595210066639ee4b2a420087d8799065484014bd07320ca908029760e64195210053ac0cc832a420087f8759065484014bf06b20ca908029720d64195210053dc02c832a4200a788059065484018baeba9ec69080297a1743d8d210052ec2e87b1a42028df8750f634840593ce8a1ec690b0b87d0765d8d216170ea0ecbb1a42bde1f41197634857bc3a8232ec69080297a1664d8d210052ec2cc9b1a4200a5f8559363484014b90ab26c690802b6e0164d8d210056c402c9b1a4200c5d751d7634840153d083aec690802a761075d8d210064fba4e9b1a4200a5e851d363484014bb0a3a6c69080387d5254d8d210052f42885b1a4200a5d8510b63484014bd0bb86c6908029761770d8d210054f426e1b1a4200a9d84dc363484014bd0b386c6908029761670d8d211c566c10e1b1a42008de8714363484011bb0e286c69080237a1c40d8d210046ec3881b1a4200a5e8510363484014bb0a206c690802b3a0840d8d2100566c1081b1a4238ad68110363484015ab02206c69081f1718d7598d210062f3aec731a4200c5d75d8e63484010fd0fb2ac6908021fa1c6558d2161e37b90cab1a420387e87dd5634840187e83baac6908030f5077558d210043fc2ae8b1a420387c855d163484011bf06ba2c6908023ee017458d210247c402e8b1a4200c5f75dcd63484018b8ebb9ac6908031b1d77258d210046fc3ac631a4200a5f8558c63484014b90ab18c690b0b179db6518d2160f0fa0eca31a42c1e1d41d9463484011bb0f328c690b0297a166518d210046fc3aca31a42bfacf82594634857d4bd0c328c690af7179d86518d215e70fa08ca31a42bce1d411946348579c9c42328c690af3930846518d210046ec3cc831a4200a5e8599063484014bb0b320c690aeeb360a6418d210046fc3ac831a4200a5f8559063484014b90ab20c690802b6e016418d210056c402c831a4200e1f5495063484635ad03a10c690802b56074218d210052f4288431a4200a5d85108634840f1bd0e280c6908023761c5018d2103c6f4388031a42008dd8710063484014bd0a200c690802976144018d21005674108031a4200acd8210063484635ad02200c690802b56044018d210062fa9ced29a42078dc835da53484014bb07b2ca69080e972176394d210043fc2aeca9a42008df835d953484011df04bb2a69081e1fa1f6554d2101c6f43ec6a9a4200e4f52d8e524847f8e8e3b2aa4908c637a1b73549210062fb2ee6a924239c5c65dcd52484711bd0c39aa49080317d94735492119e2e328e6a9242338de87d8d52484711b90fb1aa4908e637a1c635492103
  | 15 => 0xfbaa659880317ddb754cb310062fbb0ea99662028be87dd160cc40156b023a2c19880e1fa1772583310043ec2ee4b0662018dd83dd3654c4050ff0eaa6ca9880297e0d54d953100636328e4b2a6200d4c531c9654c4011df04ba2ca9882a3b20974595310047dc02e8b2a62048f8805d1654c58d8beebb9aca988032bd07725953100656a0ee4b2a6200c6f751c9654c40199ee6392ca9882b1ba14725953100667a98e4b2a6200c6e531c9654c4018d8a6392ca988033314c725953100637288e4b2a6200c6c511c9654c40195e82392ca988032b504725953100637a80e4b2a622cc5f73d95534c559aa8a7b8aa6988031b5d752d893101477c3a85b12620087f855c3624c4070f90ab86c4988023be1d62189310053642ac431262c5acf83588624c4151d904ba8c49880317e0d75189310062e41aea312620ac6c825d4624c40187e82ba8c4988030f50575189310062ebaea631262008dd8714c624c40159b04298c498abf93148531893100636baea43126200e4f53d48624c40117f08b80c49880a2f211701893105674102e03126200a6d82d96524c4031b90cb9ca49880317d9573949310062fa98eca92620a87c87595524c4e18b8e6b2aa49882a9b209655493100c6f436e6a92622c95c855c3324c4018d8ebb1264988031b1d4624c931164af43eea9926200c5c76dd5324c55f8beec3aa6498803171d8754c93105567436c49926200d4c75d89324c401a98ea3126498802b3a1c624c93105667438c4992620ae4e85189324c415c9b0a312649880393dd4624c931006673a8c49926200ccc75189324c401c98ea3126498803131d4624c93162747a08c499262c4e8d41189324c401aa8ebb8a64988021fe1572d813101c3e42ae5b0262008fb87580604c55f8b8ca39acb9080237e0d745972103c6e41ae8b2e420a87c8755165c85698b8e6aa2cb9081e37a1f73597210064fa0ee6b2e4200c9d41dcd65c855f8beea39acb90803175d753d8f2101c3f43eeab1e4200c3f41dd563c840187a83baac790abf17dcc7558f210043fc2ae8b1e420387c855d163c84014bb07b2ca7908021fe157654f210046fc1aeca9e420a87c8759553c840f4b906b2aa790abf17d947354b2157e2e328e6a9642028be87dd160c840156b023a2c1908030f5d254d95210143fc3aa9b2a4200a5e8399365484014bb07326ca9080297e0d64d95210052e41ac9b2a4200a7b8059365484014f100b26ca908030f5d074d95210062eb98e7b2a420087e87d0f65484010fb0fa1eca908021fa1c42d95211443ec3885b2a4200a5e839c365484014bb07386ca908fe9b60870d95210043f43881b2a420087d8710365484014bd06206ca908029760c40d95210053741081b2a4200a6d82103654847f4ed02206ca908029d60440d95210062e32ee6b2a4200c5
  | 16 => 0x3581410068e3a8e6b0282b3c9f611cd6050401b2ec239ac0a08032798073581410064e300e6b028200d97101cd6050401b2a2039ac0a08034bdd77258141006963aee4b028200d8f73dc96050401b18e7b92c0a08032bd877258141006d3b0ee4b028200da710dc96050401b4a21b92c0a08034bdd47258141006963a8e4b028200d8f731c96050401b18e6392c0a08032bd847258141006d3b08e4b028200cae601c96050401958c0392c0a080369c407258141006d2880e4b028200d3775dc56050401a68ebb8ac0a080365dcf7158141006ca39ee2b028200da772dc56050401b48e5b8ac0a091eaea1b6058141006d4396c0b0282c9db371d8160504a387ec2ba8c0a08034dd85751814123e9b882ea3028247d35105d460504a393ec3398c0a080365d86731814123ecb884e63028247d95109cc60504a393ec2b98c0a080365d85731814123ecb882e63028247d95105cc605040193ae7318c0a0802ae600631814128e57b0ce43028200da7619c8605048fb4e21390c0a091f69442721814128e57b0ae43028200da7615c8605048fb5100b90c0a091f69c41721814123ed5082e43028247da5105c86050401b5220b90c0a08032b5ca62181410055cc00c430282009bb87580605040175104b00c0a0b22ece05601814123d5dc3ac03028200cbb875806050401c770ab00c0a08038e215601814123f1d3aac03028247e39755806050401d3706b00c0a0803a620d601814123f4d39ac03028247e99735806050401d5704b00c0a0802ae209601814100754412c03028200aa882580605048fd54e4b00c0a091faa5c9601814128d5dc0ac03028200eb381580605048fd64e2b00c0a091fac5c5601814100c6e41ae8b2e620787e8795165cc40187ee92a2cb9881e1f21d545973103d2e41aa8b2e6297c5c7355165cc58f8b8e7ba2cb988030fdd2745973103d2f41ce8b2e6200a5d839d165cc4014bf06ba2cb9881e9720d74597315a62e39ae8b2e6207a5e839c965cc4e78b8e7392cb9881e9720d725973152e2e398e4b2e6207a5e8390965cc4014bb07212cb988021fa1c42597310043ec3884b2e6207a5c83dc165cc40f4bd07382cb989bb171ce705973100537414e0b2e6200a6d829c165cc40147f08b82cb988028f211705973103d2e41ae0b2e6207a5e831c165cc45d4bb06382cb989b3171cc705973103d2f41c80b2e6200a5d8390165cc4010fd0e202cb988021f61c405973103d2f41880b2e6200a5d8310165cc4014dd04202cb988029b608405973120d3b40880b2e6200a758110165cc4011bb0fa9cc598803175d75398b3100566c16a7316620387e85dc162cc4010fb0bb82c5988fe9720d6594b310062eb2ae72966200c5f53dd952cc4031b906bb2a59881f171cd6554b311ce2f32ee6a966200c5d65dcd52cc54b2bd0
  | 17 => 0x9282009b581dd952504a533d073b2a4a08026760e76549410049fc2aeca92820099f835d952504a533906bb2a4a08026de057654941004ddc02eca9282479b8805d952504012790eb2aa4a0b32cde0565549414be9a38acaa928200d9471dcd525059793ec3b9aa4a080365d877354941006cb886e6a928200d94711cd52504a5a3d0a39aa4a0a234799473549410068eb28e6a928288d1c521cd525056793ec239aa4a080365d8473549414468fa88e6a928200d1d511cd5250511a38a039aa4a080365c4073549412949e43aa6a928252d1c7354d5250483a68e2a9aa4a0803471ce52549411fe9a38ca4a9282019b687dc55250401b2ee7b8aa4a0803651cf7154941014db436e2a9282029b486dc5525040136b01b8aa4a08066d207705494117c9f42ced992820093d859db325040136f02bb664a08024fe1570cc94117c9e42ae199282009b581dda325040127f0abb464a08be4f215768c941004dbc0aed192822f93e851da325040127b0a3b464a0a2747d4d758c941004dbc0aeb19282019b4815d6325051363d0bb1c64a08026d607764c94117c9f42cec992820093d859d9325040127f0abb264a08be4f215764c941004cfc1aec99282009b7815d9325040137700bb264a091e6e201764c94117c9f43eea9928200d3471dd5325040187ec3baa64a08034dd87754c9410069b886ea99282ca99f835d5325040136f02baa64a08066d205754c9410049f438ea9928200d34711d53250513a38eb19264a08e3651c6324c94100cdb43ee29928200d3775dc53250401a68ebb8a64a080a6da1b714c941014da436e299282009b580dc5325040336903b8264a08066d206760c941294ce41aec1928252c9c635d8325040136f02bb064a094a6720d750c9414468fc1aea1928252d1c835d432504a5a38c6ba864a0acf0fd85750c9410069bb0aea1928252d1f305d43250401a6e20ba864a0a22c7a17630c9410068ebaec6192820099f874c832505116390a99064a08c6e5205320c941014db432e219282029b4865c43250463b2f06b8864a08c76520d710c941006cbb1ae21928252d94635c43250401b2ea6b8864a094b6514d710c941296cb992e21928200d95325c4325040136f00b8864a094b65cc1710c9410045fc32e019282008bc865c0325040336d02b8064a0a626de0575d814116cdbc0ae7b0282279b5819cb605040127f0ab96c0a08be4f21572d8141004cfc1ae5b02825299c835cb605045336f02b96c0a08024fe15739814117c9e42ae7302822f93e859ca605040127b0b394c0a0ab76c5c7609814117c9f43eeab028200c3f61dd56050401a6ec3baac0a08034dc4375581410069a886eab028200d1f75dcd6050401a38ebb9ac0a080327d877358141006cbb0ee6b028200d9710dcd6050401b2a21b9ac0a080347dd47
  | 18 => 0x44e18b8e7b1aa4a8803531cf6254951006a6398c4a92a200d5473dc552544930fd0db82a4a88061f61676cc9510043fc2aed192a20187c865d632544018baebb1c64a88061fa1b754c95100c3e432ea192a27095c835d432544018baebb1864a88031b5d7620c9510046fc1ae5b02a2078dc835cb60544998becab98c0a88023ee1d60181512653dc2ac0302a22fc3f76d9565505ada6eebb8acaa0a626de0575d8d4117c9fc3aebb1a8200d37815d76350401a6902baec6a08030fd8575d8d410069bb0aebb1a8200d37105d7635044f36b03396c6a094b4718d7598d4159e1fb0aeb31a8200d37615d663504a5a3e60bacc6a08034dc417598d410068ebaec731a82d5d9571d8e635045f27d0a392c6a08024f6147258d416a6cbb9ee2b1a820099f8758c63505a772f02b18c6a08024fe157218d4117c9e42ae431a82299b7815c8635040127f0ab80c6a08be4f2157018d4100cda40ced29a825299c835da535040136f02bb4a6a0802c7e0d6594d416959bc0acb29a8297d3671596535045f63d0bb1ca6a080a6da197194d41014da432e329a8200d97635c653504a5b28c6b8ca6a0b4765d4d7194d41296ca29ae329a82009b7805c653504a5b2e60b8ca6a08066da057094d41004dac0eeca9a820093d859d9535040135f04bb2a6a08026b2097654d41004dbc0aeca9a82009bb805d9535048f37100bb2a6a094a4fa1f6554d410061fbb6caa9a822f99e87d8d535040127f0ab86c4a08be4f21570d89410049fc2ae7312822f93c855ce62505a1b4ae3b14c4a08be4fa1f75589410061fb0eeab128200d3761dd56250401a6e21baac4a080347dd773589410068e3aee6b128200c9f61dcd6250401b2ec3b9ac4a080365c4373589410068fba8e6b128200d1c751cd625056793ec239ac4a080365d847358941006cb880e6b128200d3775dc56250401a68ebb8ac4a080365dcf7158941006ca39ee2b1282cfda772dc56250401a76ebb82c4a08034e1d77058941006cdb9ee0b128200d9873dc16250401b66e3b82c4a08036ce077058941006d840ee0b128200cbb61dc16250401b66c3b82c4a08034edd470589410069c3a8e0b128200d9b731c16250401b30e6382c4a08036cdc47058941006d5b10e0b128200cba621c1625048fb6502382c4a091f6c604705894128e5db08e0b128200db3611c1625053136f02ba8c4a08be4fe1d75189410069bc0aea3128200d34815d4625040187ec2ba8c4a08034dd8575189410069b882ea312822d9b7815cc625059d74b03310c4a08022fe1d62189410055c402c431282009af87588625059b74f02b10c4a0802ea2016218941004dac0eed292820099f835da52504a533906bb4a4a08026de0576949410061ebb6cb2928200b2d82d965250401a3ae729ca4a0802cb60a53949411fd9b40ca72
  | 19 => 0x317195718c9321c66a30ae319264028f787507614c80117f08b86c29900a2f21170d85320043f43ecab0a640087e87195614c8e70f90dbaac0990021fa1f65581320061e3a6cab026400c7471d95604c8010fd0e32ac0990030f1d065581320063a388cab026400c3f65dd1604c801878cbba2c0990031dd9771581320063a32ee2b0264008fb87580604c80f1b906ba2ca1902a1fa1e54594320061fba4a8b28640a87c87551650c80f4b906aa2ca192d3171cd54594320051f424a2b286400a3d84945650c80f4bd0728aca1931f171cf74594320061fba4e8b286407a5e839d1650c8014bb073a2ca1900297e0d745943203d2e41ae8b2864b4c5c735d1650c9598b8e7b8aca190028fa1271594320051ec24e2b286407a5e839c5650c8014bb0738aca1901e9720d715943205536412e2b286400a3e841c5650c80147b0838aca190021fa1f41594320043ec3e82b286400c3e87d05650c80187b0fa0aca1936787dcf415943259f0e39e82b2864b3e1f30d05650c8014bf06a0aca1901e9720d41594320051f42442b286400a3d84885650c80f4b907b82ca1901e97a0e705943205537414e0b286400a3f845c1650c80147908b82ca1901e9720d705943203d2f418e0b286433a5d831c1650c8d98b8e6382ca1901e97a0e40594320052ec1c80b28640087e87101650c8010fb0e202ca1901e97a0c40594320052ec1880b28640aa6e82101650c8014db04202ca190029da0440594320053ac0880b286400a3e84c41650c80147b09882ca190021fa1c10594320043ec3820b286400a3e84041650c80147b08082ca1901e97a0c10594320052ec1820b28640aa6e82041650c8014db04082ca1901f171cd65548321ce2f32ee6a906400c5d65dcd520c8018bf0bbb2641900317217764c83205667296ec9906400c9f41dd9320c95f2bd0fbaa641900317ddb754c8320062fbb0ea99064079cc87549320c80199eeca92641901e3720d745843218c6f43ea6b086400c5f75d4d610c8635ad03a9ac2190c63721d32584320052e42a64b086431ad4814c9610c8151e90ea0ac21900a2fa1f74580320045ec0ee8b006400ab5811d1600c80117d0fa0ac01900a2f21f41580320165c3a480b00640a8f887501600c8030fb0bba6c6a8b63175d76398d51006a6298e4b1aa2008df8758c635440159904b18c6a88b25761f6394d513852ec3ec729aa200c5d87d8e535458dc3e83b1ca6a8b1b875076394d513fc3e432e529aa24987c865c253544011df0eb10c4a8b5e9be1562189510056641ac4312a20087d8794c62544018b8edb9aa4a8803171d873549513862f430e6a92a270c5d861cd52544018bec839aa4a880317590735495157e2e310e6a92a2acc5f611cd5254467aaec239aa4a880347d0473549510062e300e6a92a20087e87d8d525
  | 20 => 0x5fc22e1b0aa4028bc845c361548011bd0fb1ac2a900237a1c63585526de67b90c6b0aa46c87f8754f60548070fb0f296c0a913a9ea0252d815259666b90c7302a4008de87d8d605480193ee9b1ac0a9003271d363581520066a38ec6b02a4008de8718d605480193ee831ac0a9003271d063581520066a388c6b02a400cd763dc560548019a8c7b8ac0a90023ee1d601815203d2f41ca2b2e6407c5c7359552cc80517d09b82c3990022f613705873201c3f43eeab06640087f855d160cc8070f90aba2c19902a3720d74583320061fbae82b0664b0c3c75d0560cc8e74bd0728ecb190031d5c651d96320543e43aa8b2c6400a5f83551658c9b5c3ea7a0acb190e717dcd6554e321cce7c3aa5994643995c855c3328c8070fd0fbaac31900317dcf75586320062f41eeab0c6400c5d83dd5618c80187e83baac3190030f50775586320062fb98eab0c640087f855d1618c8070f90aba2c31900317dd753586321c46f438a6b0c6438ad68114d618c8711bd0f992c3190e2b5a0732586320145f426e0b0c64008bd84dc1618c80187ae92a6ca9900a1fe1d54d95320051f424a3b2a6400a3d84947654c8014bb0728eca990031d5c651d95320053b40cc9b2a6400a7581993654c80147d0930eca990028f61261d95320051f420c3b2a6400a3d84187654c96187ceda0eca990030f5d074d953239e2e39ae7b2a640087e87d0f654c8010fb0fa1eca991cf8710d43d95320043f43885b2a643787d8710b654c80147d0938eca990028f61271d95320051f420e3b2a6400a3d841c7654c8e74bd0638eca990029760c71d95320063ab88e3b2a640087e87d07654c8010fb0fa0eca990030fa1f41d95320061ec3e83b2a640087d878c7654c80147d0918eca990028f61231d95320051f42443b2a6400a3d84887654c8010fd0e10eca990de1f61c21d95320051f42043b2a6400a3d84087654c8e74bd0610eca990029ea0021d95320053cc0043b2a6473a5e839c3654c8014bb07386ca990021fa1c40d95320043ec3881b2a6473a5e83103654c8014bb06206ca990029ba0840d953200536c1081b2a6400a7681103654c8014eb02206ca990028fa1310d95320051ec2621b2a640087e87043654c8010fb0e086ca990028fa1010d95320051ec2021b2a6473a5e83043654c8014bb06086ca990029ba0810d953200536c1021b2a640087f855d1654c8011bf06ba2ca990021f61e64195320052ec1cc832a6400a7681990654c8014eb03320ca990021fe1d64195320052fc1ac832a6400a3e84984654c80147b09308ca990029760e61195320051f420c232a6400a3d84184654c9b5c3ec7a08ca990031bd947254d3239d36c16cb2926473c5c73d95524c8018becbb9aa4990e717197735493257d2f436cb1926473e4f62d96324c80f1b90cb8c64990
  | 21 => 0x8510b635480153d0938ec6a9002a761271d8d520052fc2ae3b1aa439a5e851c763548014bb0a38ec6a9002a7a1071d8d520054ec20e3b1aa439a5e85d0763548014bb0ba0ec6a936b87a1741d8d520070ec2e83b1aa400a9e84887635480153b0910ec6a900237a1c21d8d521cd2f42843b1aa400a9e84087635480153b0810ec6a9002b6a0021d8d520056cc0043b1aa400a5d85dc3635480153d09b86c6a9002a761370d8d520052ec2ce1b1aa400cdb709c363548011bd0e206c6a90023761c40d8d521cd2f42881b1aa400a5d85103635480159d04206c6a9002b360840d8d520056b40881b1aa400ad581103635480153d09886c6a9002a761310d8d520046f43821b1aa4008dd8704363548734bd0a086c6a90029761410d8d520054f42021b1aa400a9d84043635480159d04086c6a9002b360810d8d520046fc3ac631aa407a5c859d863548011bb0f320c6a9002b5a066418d520056ac0cc831aa4008df875906354801c3ec8aa0c6a9002a7a126118d520054ec24c231aa400a9e84184635480153b08308c6a92d297e1d5418d5263d2fc22a831aa433e1f84550635495f4b904aa0c6a900297e055418d520052e402a831aa433a5e85d0863548014bb0ba10c6a92be972164218d520052fc2a8431aa433a5c8550863548674bd0a210c6a9002976144218d5219d2f42e8231aa400a5d85d0463549b3c3ea9a08c6a9003875534118d526cf0f42e8231aa400e1d85d046354967c3ceba08c6a93678714b4118d526cf0fa8e8231aa4d9e1c50d0463548674bd0b208c6a9002976164118d5219d2f42a8231aa4dce1f545046354801c3aa8a08c6a90ce97a144118d520052ec288231aa433a5e8588463548014bb0b108c6a9002a7a122118d520054ec244231aa4078de8708463548674bd0a108c6a9002a7a102118d520054ec204231aa400ada8008463548015b300108c6a90ce97a174018d520052ec2e8031aa433a5c8590063548014bf0aa00c6a90ce972154018d5203c6f4388031aa4008dd8710063548674bd0a200c6a9002976144018d52005674108031aa400acd8210063548015ad02200c6a9002b56044018d5219d2f42e2031aa400a5d85c40635480153d09880c6a9002a76131018d5203c6f4382031aa4008dd8704063548674bd0a080c6a9002976141018d520054f4202031aa400a9d84040635480159d04080c6a9002b36081018d5203d2f436c6a9aa433d4f731c953548010fd0db8aa6a92b31718f7154d5201c3e432e7292a473c5c635ce525495f4bd0db1ca4a90e793d8b639495257e2f438c7292a473c5d8718e525495f8bee831ca4a9003175d0639495257e2f390c7292a4afe4e7218e5254801c3e8231ca4a9003179c0639495201c3e432e3292a400c5c635c6525487f8e8c2b8ca4a900a3de1d41d8552004
  | 22 => 0x4006008000800801a0050038014004000005000c0060050038010016002003801000600100080200040140020000000001004002000600b005802000400500200000000000018004000007002003c00600c000000000000000080000000220010004022000001000c0020000008008008000003800000c000001000000000000880040060020080018004002002800c000000000800c00a0050000008000003000000000a006002805400c00700300000020010008068000004000800800a0030028004000000005000c0000000018010004002000000c000000001000000e0000040000002000000001802c0030008000000000001804800a008003000000a009004001000600800000000040010000004002001000800c00a000000800401400300480340000010008000038008003800000000600080100000000000000004001000000801e0030000000000001000000000a008021004000400300580100000000000008028016001000c018004001000400002b0028004014000000000c00000000380000000060008008016004000800c024000000800000a00d00000100140000000008002001000000000c004008001400001001d001400000400080040000020020010002007000800400e00b000000003c00d002000000200900280080040000008000000010002000400000100100080000020008008012007005800400e000008800c002004000001400400000300080000000018000006001001000c00e00e000000400200700000000200030000000008008000006c012004002001c0040030078000018003002800400a00300b800801001000180180060050000004034000000000000200000000080000000018008012008000000000200a00300380000020018004022000003801000200303c6e41ae8b0ca6078f4875056194c014db0a10ec4a9802b360c21d895300574c0043b12a6008ef875886254dbb59f06b10c4a98021f61e511895352d2f41ca2312a6008bf845c06254c0517908b80c4a980e3760f74d85530045fc22e1b0aa6028bc845c36154c9f8decb394c0a98023ee1d60181530043f43ca2b1ca473a5e83945639495f2bf0eb1ca7291ce97e1d6394e520062fc3ac729ca400e1f4158e539494b0ff0cb94a7290f25be197294e5252e37c32e529ca400d2f415ca53948010ff0cb84a72900237e0d745865203c6e41ae8b0ca40087e8794d619489d8bacab9cc1290029761743d8d520146fc3a87b1aa402c9e7450f63548014bb0b18ec6a9002a7a1231d8d520054ec2463b1aa400a9e840c7635480153b0818ec6a9002b5a0664d8d520056ac0cc9b1aa400a9e84987635480153b0930ec6a9002a7a1061d8d520054ec20c3b1aa400c9f749d363548734bd0a3a6c6a90029761474d8d521cd2f42885b1aa400a5d
  | 23 => 0x93d57c800000300400000040050008000006001000000c00c004006000000201400380280260060000008002000000000800a00a0000008006005001000400801d000000000c000000002c006004000000c00401200480b8014004009800800000000000080060200068000006001000800c00e0020008020016002000001801000d00180140060080000010014005009000004a0000020008002001001001c0000050000000006000000801000000b0000008000000000800000000b00000040120020028000000007000005002a000001001c000003005000000000100400040040000008008000000001000c000021000803c00000001500000040040000000032005000004800200200600000060000018004004000000000400000d0028014000000002000801200d0030004006003001001c004003000000000e000000003c00a007008000800e00000900080000020000000000006000800801200100a0000000002001806001e0000018050002000005800000c004000803c00000000900100020000198018014002000800400c003001800000a0010020034004001001000000400a0018010000002000001801001c0000000000001000000000a003003804400e000001002000000500600000000010020004000001000000009e0020050000016000000800000004f000800000e001001802400200e002801c000015001000400200500000000000000000010000000000800c002000000001c01400a00000000000000038024004002003001c00200100000040040000000008008001000803c000003001802002e00600b8004004001000004c012003000800c0000090000014004000003803c004001000800800200000800000020000008018006000002001800c000007002000600400080dc00600c0000004000007006800401e014000000000000000e80000000150040000002001000000000a000000800c00000c00b800400000c00000000000020000004000001001800c00400200380000000040030024000002001000000e0000000000006003000002c0060020010000000002003801000000500080080240010010000008002003001800600300200080000030000000000002000000400a002000800401c0000028010004003000003c00200000f0004006000004000000401000200080020050000010000004004801c000001000000803e0000030020002003003000800800800080080440000010004008001002800800400b0008000000000003800000400d000001000400200000000000350010008014000000000000a0090000014000000001002800a0020000000000001005001c0000060020000000009000000801a007001800001a004000000c008000000802001800d00080000040010008000002007000000
  | 24 => 0xf877400000000025b400000032c16151f057742e1404f3692d07181e8548b6b4f62a3550e51c0cd1edd21e000000000068c0000000000c5c1cb10780003260000000a24c0a00000000000403e7485a35000000020205c00b84420e7800000000000004cd75003a14180006dc03057c14e96346491ff930c00017b00000992481fe158828c210b630fe8000000000000000165c7cf00011c89922ff50a800174e0004278000daa36b0d405d1388000596263863a0001b9880028a1f10e716bcd30a824aa0110ff27e05c023446401501ad1c306d40003f19d049940f210c23d882a04357a26f4498a790ed91d8022a47000000000006a0ec100c0004ab586a5006ac70d1df8f0000055a00003a946e1f015e92dc0ca7c34780238ecebfd42a84dc000bea0b02e690820002f41b28b48385564800000007c0001ad00000000ad92a87a87293300000cecad70001ee00004de23d132d18600041c0b144a8bba00005296e600055027583f09be0b6861c93caa84a897a54baa855e900003f60003b42bd4000ad5245affd0caaee179000000000020f21187286350ef0000000c190002448c162983f78000000000000088c55420116125f940e7033ee800000000000017b8de860c02780000001b71a081fc1aa96f2358c9907c0cf2c416f0000c16421192019696e2c31cd14e40000001424c6085600000007aa374334800139e0005078fc46444f55591720000b782df80005144823338e543d4000000002d7c637e2cdb044d340e11fc2e640000002d3a1a423a71542d06f06cc0003ba9bdc0008fb4f2800000000005d8000000000001055801e18057400000008a62bf80005280000be8dc03f200025c00000009bf3ccaad509431a08b80006a2000361a9b400000034300c400000050b00000004770001c2c000000571860424a0005df97b0000000395931545e0001cf80010fcb6c000000000000037600002c6000521800000000000002d40e40002a31cb017054011b172441a8bb0498d3042200028380016cc00012b8000dccc010001d510f03e90001e5961653f4cfb0781a207d000097c00000000002b80006b854c000062612140b0af81e02884000208aa006311f80014647b50b7264c46a0001be25a8a469a41c792c800081a1e780ac000840164a7c4da2ad0412939103a55d57091140006ee5e18000000000000000048c3f705ca3a49ca0003550e6400052d529800000019038f000000055e5ef8d9076a0005148f1572c28f4919de08a66f137f07f058600027b0a04fec51b212261c9880001d98000782a2552a9e20d188824f50000cf00000001a6c000c003d08258c8889418b13cc2ae99700022040008c50000000ac206c1a1800130c8a722097bcade3eb000143d7a27f400000000000000000000d4a00a45c99040006a9000000000
  | 25 => 0x24000160c00000002fce6e8124ab1b3548483f09c29205d20281630e94000b77205a0c40003635bf119d3960a60fd000039a4c757e800012e2fd0000c306f289f000000000000000000102aa726186800000000049e057505840f00019c400016700010fcf0a0002541a0cc1400037ea0300004b326c00014580003bc80000000000dd83640000000000000596266000000076e3b8000236c0000005750a8142819700003e4c9e7303fd93ec2d8b3f4b191810a400017980009789060000000d1e00047a192d5244f834881bd5944830001d1cef40000000f74000000000000000000000000000004a20002860f8c7c400029807cc24b00011840007cb5df0db12905c35ca80a4000ad9269aa0d6682c43c4a7653143371298400a068e758281a400003532e0b4d65a3a4330800000044b1e9a664774887111024800000044280000001980001198b70000609281165482336a1bfc00052c5fb12d4d5c5f0000258421475b5c3a5307261bd475000033691910d9e440000000000000000000000000046294b2978be80002374e28001168be255e9cec00018d000000000087d00006d02400000000000c0e00000005015fc00003f23b51d8a4b0000000d7a00016d8000d82000544ae9400000060e979000000023a00004ce5e72a5901800056d000101cbe23a6260aab85700a258216380005aa0a680010381300f40b28e867215c786cc7ca30b00000dcdb2000000000000087000000c948a00003085dc0000000000000000bc000000016465f321684d163cad11512c58822b4f0000000000b2b0002ed80000004b8a1dc0000000d10000000a0000000000007765010234b82000000000106a0001de000000037f0000001834bfa26000016f49730000de0fee9c711a0000000000000000141c00025a13996b85d03898c28bf67c0606af38e54000000114000080a0000000000000000000000056e0001e9069a0001872d6c000a71000000000000006814c15420002fe00012106cc58880009e861b03a80000007480001494db87091780ba10102c81a48f8c0ba00045700000009b0096800000062932d00000000141fe8ce41b6182112800035228e5d989000000004f324dc5be0005d1259400041200001d03321ad27680000e200000012491c20945d48434b403451d4041cd960000000a0007cb075188a5d2766325730c0479cb6118a9428538b3619aa2540000223828000c80000253800071c0000001e7c000000000002525000000006bc826b5e52d9a6400074a00022584aa000000008506e36d52c800085c6002e589616b0b3744d000064686113611b8094a3500025d880a0001e8916800061a000000000000047400000009a800000013980000002d1020a26f3fe800108e39a0000000e4000004225d0ec8000224913555a00015
  | 26 => 0xf80009e40000002540000000130822c9b40ce58528c08c66552119d4033a00000016517b4b8416895ccc6c7980af92584a465e026ac9cf4698014f80003c84d54b90fc0cf400039fa8e57061eb534181161247826e0000000ad440ca6d8d6076200018e8796c1034095209ba448490a0b4346a36016a3600261042bd00008342490000b007168b3000275d16027b07e2da800069229225e47b802a08f1e50a9e00029300000000005ee2488d2c000000129400025c00c8a0800039e3a2000093a03b2f5220d58602f26400010401962c814a83ae72534396453aa2b52f0800000094731a01b40001d50000000000b8253c0fa80001c500021cc6045eb3ce1d18db644e48e0e81098538122262cf2429960622006647ad4f3954407a45d042ad286c06541fb09e920459652c29a4b000830000000dc800000012016a800016f16997fc71d0002cbcc040000b58049156185113a19c018985288863cc9467f2188c7901e8970001a913d20000c580015ca587397ad48222284000000000000036ba6101ec4fa27b9b206ca47d410af6438649437089440009010000000fc4b2116907815a495815696b4000af02cc8f345760000e2108440e03903c800045600000000017e090710c8000dea2851f691a42981462bb11a81fa29d33106c8652c0e1310e345b805a51188145b4b0100021a0b040000000f406100005ef23c867ea410002d5d45619e3b3155d16299a1019834a6a00024c2d900000fa3291a8483a000000257cad40000000000fce00000002455080000c92db40007023e516340008da33c96b018e0005b8911000066531f0000d000002610dd8d4600022180000009200520fd465000000000543127cd0000000000a8b4c7800134e00039b15c0a9a935319a6ad6a099800012f4000409000046c00037706b1d1400000003200000000000000000000451000000000064d000098cf2a89b3ecaaacbfc00000000000000002ce0000000b9000000013202242b10bd8000a0341e15640009694498a540003df000000000000060592650d613c487029400000000000003c4b25374921420c00033bad2c4f0000380800075878f3f8a2f50f290a535a724d586a84452d397100005e68ee57dc569000000069c1881e400000007e4000000000096c42b9220000000000000133c3f94029974000000244800000000046e00007b287517083ed65293e171009d78e39b44c1958d8e1540372b1024475819e0b1d4029af05ea1ec1dc83d225209cdd4000022af4c35650c13511a037c8f91df049cfb600014326504d075a0002ff0a923ee0651e4c0005342d2a5dcc58ba64e18c5000000049f800000092f0a580017680003d72588000b3c4ea1acc0004b60000000000000000000000000009604a40000000000000000ab900000000002642d929680
  | 27 => 0x7cc54700000000005f880014360461a900006ce6e31a518e48e68f5496196566627737021b500e0b63132868b1e10313997c915e2af2478108c444335ab1038f7608a2aa22443feb592e2164c6084fc364aa2821e20c57d12193528025e2808c000739345a28ccbeb0248d9b14354a7d0000d00000ad8000000000017f0000938000b9e00022741c4b600a9add42460eb569800040c0000000000b747180c22eb0000a050568618000b1f0069d0828476e4fc800111a00018009650e8926236921d7020c3148934400000044600000000004848000b140005f9800000000000011f800000000022b0ae45b500010e93ee37100014b800000000023540009e25faaf2d5b813506d2c916060005bd9d254e6b3200023dc000b425c48e889fc00000021d81c055b46e95289e091f3e11fe83949811c38b50c101d407413e45a095b000000000000000000000000000000000f0c00001e193000081700000013a00001dd976488014813280004e41e3000000161c00029b10317f200000021a8d5a56c04d0914520c1557fa17400026b00008405647ba00009740000361c88b997162026010000e385a85ce9648154b8d00000014ca6b726b9df0ba8000317800015e0001f0000161e00007f07cc39242245d08b56502ac000000109c7ce00000001f034b0001464dac5f443780000002cc27f8000f7c3e21d680014765144098ea859a71f06b8f1c234751105896d7de08628d1e0419033d08c81886c2b9f0002e854ea95700000000000000001840c6e00051ea4e91240005660bdc000903526a7710368ff41212bc2c86e7553016c2de57930c1b0000066e0000f300009495792a8c8de6d2035a57483245e36991b0534ac71f21cb40007f3504a5f06c4a1c248a1909183fc4c8974ccc89383378e316fe4285b900005780f1000000026200014f1cf17ba82f3ef00000a459f000000139a01800014dce2496b00000000000002f027f0a0415a149a8800006a000d000000000000000000000000000da40000000d380000000005de0000000000000000000000000029180007dc39214ac00094500016540007321951580000ad60000000000000000000000092b0002e915b4b9857da9d80000000000000b5c00037100004f20000000ec400000002b068413021e271a64850e0001a20000eee6ab1242c3013a1720f7232081a37b00021400001cc223a4d97148c934700004528330e010803de000509000180e7e633f1a5c4e06e530f2a3c4247520000000000b6200011c40000002e12eb909220906900000005780000001576ae20870f6d3768d30002e70efe0004511bf075600000000013a400000000000000001959ea4a20adf0ec8cf873a6f602a18580007c55381e883a0000000086941000030f97e000097a284000088c000309114971cb394
  | 28 => 0x4c600195ee6951971d355e2a4f480000000091d59d00000824a600029d00700000002378b9a5da19821c8000bc9311ae4c6f400037785cd1c8541046000167600051f937d53a85b300906100264546300000002e70001b0898c0001ba86e4bea000460a45400000029428789b200029d884ca9cbc11469df8fb05220000e1005c0872e88dc81921c75ba2511068a9c4ff928cbbe97d36d1130e1e3a130b853cee032c54b8b80868add1a1000000650b080810000077d000160c9c400000000005ba69e301800000000000024e557c00044400000000003eb93857d0a6423e049884a42c0000a313eca6742f202400000015400000000000002d94000b8c3b680005da91a17190f055600000000001ce8c45142ae01cc0005289760ca2000379000000093200000010c02ec0001bcc4e200054a2458aaa269000268c00013b2d4800083858c5ae8c6454ec1707209281cab695539ebceba0005153024000aef00014c800036f0000c0ce2200058d92b000000026817d80f000046f87b44788cd2008378ca65133eaa8447000be4ce0a6c11048111515ec66c58b11e827c00063f2b40000836000529000000a42f000000000013600000000000004fd0001552bd053d2afc00000003002cc18ab304d900003a4acb3d2a14465a312000276877a94600017e8000acf0001af168043b000020460c7bd5fd800154800036790d40002f116c8448000a3e0298c1d68c000473000000000052e1c197b0ac83d5276159a0000000000ed60000000798000000000000027c1715c905e91c621d000300d3808a800012100006dd21b10ac27400041b000028e8fa00015493425ca00000004b40000000a496407c819894487a41d60000001558000274800000000021b80002ca35c561000099e08f5060000b6e5db45500000005581c900000009b85890000dbc9d35a89cd57c21f216a9ce0e369fb60c2950ffe2ea17593b86b0175000000166a000089800000000025f957ce62000431064536828b4e502acf7e1ba3d416f80000000000000ffcaed2d12534ec22d700014e53e8000269000000000000023f09d600008b271801c4fd304a59045e9b12c228183ea00000019b436a00000026954a00000000000fa29300002c50ae23d800003bce440000a71d8139c2c10862f5c476ae95608000238b224f088f91de000310000000086e00000000009141cc000000000032dafad2b450e07693341582cf47710a57cc9050ac9ac4c549824ff2930752a6f40215d57287830002d4cd1285921c2c00000a24000047cc483c90000588b3c4ef000000000000000003108ea79d0000c151949df33ea82c0006720001e693d05b41c48000000aa50008001566a1f11c88e80000003f6917c9ac61400001ecc849e40000fb00000003fc0f1800078700028341a6ab74c40000
  | 29 => 0x2cc0001c080002f00005629758d285213d61a7c42c0000001e0000064e49880009d40005da800000048e0000000000000000000119e0005cbafb0000b1700009b476400000000010fe71932380780001d32ba00000000554d6000000000000000000000001d826b800044f00e000000015228680000000000000f680007844331f848e0bf700000000001a000028e0c7878a345000075e707436244054c5bb3498e7000000024808b809cafc00028d0c4e00048ba340b8e774000151c00000025f2928d9c00000011940000c600005f822054c000243158000000000000480000002bac00053100003a575e00015280000007c90001098acabab12797740003fa000210c0006bf00014f0cf60000000000000000000000000000000004b800073a52200010e27972e0000118e00057b267550c0000e88c2474ebb130a86c00001c60002ce032a0000fa0bbc00062b6028000baa00000000016dc94a000088400000006091543d801d3f4800025e56600b04c89720c006e2b389a815e000057162a23800006e00ee8eb4a08bf92c032f0000000f2000025d0ae400011457600011701615248000d7289e2761ca1076b180002bcd83675510a1460cea00000000000000000000000ff80703b4a17c0002b60000904f6882b5aa800071073e05800000000005bc8000292000000000042e2b43380870bcc92a000000000000058c829c0009c220ba2f800000000012b4e142265dc8000bfe0003d3800158c5163b8a6e4a7a98d5ea0670bae000000000015275734228741be78e53b8cec0001a55841af98389043620178000bb03fa9284000000000149c0003d71cb87a519650438b89b88b00593ae091c8206900002e6c7fc5ce42288a07884a40001d8d0501e71aa2888786000000000000000000000000000d80002f9495c6b53741be91e6ae712b16840001b127400009c0000000000000067c0000001776000607800000032500000000000000002cc400081e314254d0888a5000000180c09c000276c0001584cb2c98000983558800000056b2d580008f20000000000cd88e54592308000bcf20b1b400006ed36c10c8f608e2351000021297f24d80003b40000000000318822339a9ecc32000000000000000017c80000002434ac8f2864e7eb0000e0c0000003dc8000e288d9081000000001b3a9800142e27d0000000000bad31080009b681504f1d3c000772000000000076544200016e0933444a2fcd8c58918e00000000004a72f6d2aaa571c51fa16ec80b1ae8c7c42a6b64ae1e9836c93451d1d013743fb2469158e344f117c238146600056da78c38276c549af9d7aa40a1ac9a98ba469c187ad3003ea5600000fc0000004da877c8b68140002d680000000509bed24a0000952a0579024d17a9164c382e500020a53ea7593d91ccc6be000
  | 30 => 0x6b0952000299a1f000008940c000167c00000000000000005e50001754b1c2f69ef1336000406800000066b3d000007d00001f780000007d4040019d67a0005b780001502600588000ace00041d0bf00002044972f18e102ba4470b38fa600000006500000004d508c8b028d74d3250c1e83a3505000096012b06686fc86047f4b4019800000737c80017708033d88adc00075e3db0c8555eb852b1800168e7df1ef177116c3c20c52e8c16e21f000067d3ba1393088a58e9c60e00000000005f900024a50725454bc2c7505c00011980011389eb44c984c934008000013144ea9a0161a356821dc3f701d93908bc3c5a038fac52951680001689e00e100000b055609fa8b8fd868812f09fc0000001c129008b861d34e800000020a0b50ac0af86af37c000116e95252707211989ad4242ad972245400019180003680000c5c0000000002ef4ccc9a20000ab956000045480011e20001a41c8c81031804809413828265be125404a35b40302e8938be90002c40000aaa5318000c860490001570bca43e000212ccc65fd5a6a24153235713a1eac00085800000014be2ee45026dc00035500026cc9260000000ccc00091107a80cc6703f23d980000000006042d7c0be00000b9bacca090d4f9af80a8657e1882df40003342a129f8622b4938807dce087275441dcd4d473d3cf0040ede88b000000000051f0a089f0bee43d2d82fc980850600000000003502ce80014dc00000027bc0008100d2305000000000000017840000001a140007c13af90a95bc4640f0a44c7aca105f6800092e14306616c470ca213f280000000575b38000e5ca9e35d1c5800013d0bc8a854267004fe8e5923078206e8b615364002662b8012a00000016e4000be432b80012f65cc4479f480006b20001a9c7e69422800000976a95110171876c1284152a44b2e9ee000000000000043d2f30b3420e0b419a05c8b434f9000000000053e01cc00000000000008f635e00018f49628b5023800129e0000000000000a6600000011fc00000029b099c27e00000000008fd31c274400046237803cc63695e3e38bd000037d06100000003240002348aa6a620d3173cfb48a154f8a8c0000005899510000b6800000000004021a3959115a2fb316afd00000001f0aa3143288628e945400011508c2e180d086300000000000003e800000003b411600000000002139fc01a8abc0be0fd14fe0005308000000000000042c000aa2000000000092760988c0e9876a0002d14fe4000318a7e08ae75600000001fe96607621353bcbb755d22918141e53c6851069e6bb02586385524a00501ded2ce9954089714dbe09b29f168c0a05b646b23382d227621c8b58410051419178d3e041454025c0a3c5985a416f57ac8c051e000134049f282800000041f000000178833a000000
  | 31 => 0x5e23f50000b663900002a59764a5e33a09d400000048f1818f180003350001740c1f00025d50601ae00002642a20000000acc0000f7000214c00000028b890800000005907d93da000000000000063b00000000005de000000000048a0bb00009ce9bc00000015c8000000000000000029000000009890c19d2d44c6822beaad0e1c12454802f10a862501a0eb86a6000000183d7f000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1010003040d0014060100020400000001010205000302001c02020041765c80550635480105d989c0639495219c17a5f83505650c86705c9760e405943200513a58531c9635440105d9818073549514d44da63615d763505a351695d8d7194d414d44da63615d462504015179159473549416e447e6175d8c325040151695d8d710c94118c65261325c43250401514954c9710c94100525259101cd60504014a49644072581410060ee1f855806050401a188520d60181410068ae14825806050401a28852096018141006a2e0c825806050401a88832096018141004aae5c8258060504012a99720960181410068a9d4825806050401a29752096018141006a29cc825806050401a89732096018141006a89c4825806050401aa17120960181411741725d8390965cc40184c73a0a70597311741725d8390165cc40144e93944725953157e13208835d4624c55f44e959d4624c93157d13e6075189324c55f44d981d4624c93100703d0475189324c401c0d411d4624c9310048da625358541940012349854961506500058524d52585419400184c851c9624c73057e13208835d6628c16fc1a70190658c93000417a5b855c6324c00105e98195718c93057e130ca87d95324c1b381c86d05750c93036417a5b87d94324c00181d87190650c9300050765c65d90324c00141d95cc4765053000525646301d9414c00141d950c0765053000525644301d9414c00123598dc76550530006071d9859cd414c1a3a146560653505306e487259850c9414c00181c76614325053000685195810c9414c0014959119276cc53036417a5b87d97314c00181d8719065cc5300058564464197314c00141d9719764cc53000417259851c9314c00105d98194724c53000417e61731cd65c815f44c925cc73597200048da637159541c80014a591880765052000529644201d94148001ca321440765052000728485101d941480018a5811da72505200062a200765c941480018a9861c07250420007281c072585410805d05c985d563cc4200062c21d61505200806705c985d5630ca1000417e61731cf65440012349661773505100060d21c6558d4144001a246520963505100052525d6318d41440016849258c63505100048d259851c941440018b07660072505100142d25d860c94144001b23656087050510006c8195821c141440019a1829c8705051024d0da5b755053044093434965d541c8110006680808750520440011b297a1d414811000668dc88750520440019329521d41481100064c6548750520440019a19221d41481100064c21f65505204400193087195414811024f0c1d86550520440015a297a0941481100066821e82505204408f5a09760941481100066821d82505204408f6a09660941481100066821f6250520440019a0871894148110
  | 1 => 0x6c8026740000a68e24003e8a409c065eb42a62aa3a1670a45aa00058567aca1e4e000046dc98443c00c6bc66ba880ce254d4d0ae1c001896e0127cd6509a6a2ca252ced88284b0762eda4cac5c6eb686040234a8d2903008008c00cc2848689ebe00c21a0e60104a000022b8007e00320000c0941472b220000042c83800de6492c400360a000000780f0000050002060504010c0
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x50003089975cc825806050401850cbae2412c03028200c28258876094148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x94d
  | 6 => 0x94e
  | 7 => 0x4
  | 8 => 0x124d
  | 9 => 0x124e
  | 10 => 0x3
  | 11 => 0x8a
  | 12 => 0x8d
  | 13 => 0x8e
  | 14 => 0x150d
  | 15 => 0x98a
  | 16 => 0x98d
  | 17 => 0x98e
  | 18 => 0x128a
  | 19 => 0x128d
  | 20 => 0x128e
  | 21 => 0x150a
  | 22 => 0x150e
  | 23 => 0xca
  | 24 => 0xcd
  | 25 => 0xce
  | 26 => 0x9ca
  | 27 => 0x9cd
  | 28 => 0x9ce
  | 29 => 0x12ca
  | 30 => 0x12cd
  | 31 => 0x12ce
  | 32 => 0x168a
  | 33 => 0x168d
  | 34 => 0x168e
  | 35 => 0xa4a
  | 36 => 0xa4d
  | 37 => 0x134a
  | 38 => 0x134d
  | 39 => 0xb0d
  | 40 => 0xb0e
  | 41 => 0x154d
  | 42 => 0x154e
  | 43 => 0xb4d
  | 44 => 0xb4e
  | 45 => 0x16cd
  | 46 => 0x16ce
  | 47 => 0xb8e
  | 48 => 0xbcd
  | 49 => 0x3ca
  | 50 => 0x3cd
  | 51 => 0x3ce
  | 52 => 0x15cd
  | 53 => 0xcca
  | 54 => 0xccd
  | 55 => 0xcce
  | 56 => 0x15ca
  | 57 => 0x15ce
  | 58 => 0x170a
  | 59 => 0x170d
  | 60 => 0x170e
  | 61 => 0xd4a
  | 62 => 0xd4d
  | 63 => 0x164a
  | 64 => 0x164d
  | 65 => 0xeca
  | 66 => 0xecd
  | 67 => 0x17ca
  | 68 => 0x17cd
  | 69 => 0x98955
  | 70 => 0x128955
  | 71 => 0xb89
  | 72 => 0xb8956
  | 73 => 0x14a
  | 74 => 0x2c9
  | 75 => 0x198a
  | 76 => 0x14c9
  | 77 => 0x99255
  | 78 => 0xd49
  | 79 => 0x17c9
  | 80 => 0x98095
  | 81 => 0x1849
  | 82 => 0xb8c
  | 83 => 0x150995
  | 84 => 0xb0995
  | 85 => 0x98b15
  | 86 => 0x154995
  | 87 => 0x99555
  | 88 => 0x1609
  | 89 => 0x151295
  | 90 => 0x150b15
  | 91 => 0x151555
  | 92 => 0x1a09
  | 93 => 0xb49d5
  | 94 => 0x9cb55
  | 95 => 0x16c9d5
  | 96 => 0x9d6d5
  | 97 => 0x3c9d5
  | 98 => 0x9d5d5
  | 99 => 0x9c3d5
  | 100 => 0x15c9d5
  | 101 => 0xec9d5
  | 102 => 0xec9d2
  | 103 => 0x9ced5
  | 104 => 0x17c9d5
  | 105 => 0x9d7d5
  | 106 => 0x1789
  | 107 => 0x130c
  | 108 => 0x14c
  | 109 => 0x5c9
  | 110 => 0x134c
  | 111 => 0x168b55
  | 112 => 0xbcc
  | 113 => 0x15d695
  | 114 => 0x1695d5
  | 115 => 0x164c
  | 116 => 0xed695
  | 117 => 0xed692
  | 118 => 0x168ed5
  | 119 => 0xa4bd5
  | 120 => 0x138e
  | 121 => 0x164a55
  | 122 => 0xa5655
  | 123 => 0xeca55
  | 124 => 0xa4ed5
  | 125 => 0xd5355
  | 126 => 0x17d355
  | 127 => 0x44a
  | 128 => 0x1a0a
  | 129 => 0x1a4a
  | 130 => 0x10a
  | 131 => 0x4d
  | 132 => 0x180a
  | 133 => 0xa0a
  | 134 => 0x130a
  | 135 => 0x138d
  | 136 => 0x3cb96
  | 137 => 0x15cb96
  | 138 => 0x40a
  | 139 => 0x20d
  | 140 => 0x160a
  | 141 => 0x188a
  | 142 => 0xd0a
  | 143 => 0x140d
  | 144 => 0x5ca
  | 145 => 0x58a
  | 146 => 0x24d
  | 147 => 0x178a
  | 148 => 0x18ca
  | 149 => 0xe8a
  | 150 => 0x144d
  | 151 => 0x104a
  | 152 => 0x19cd
  | 153 => 0x194a
  | 154 => 0x1a8a
  | 155 => 0x14cd
  | 156 => 0x74a
  | 157 => 0xd4bd5
  | 158 => 0x20e
  | 159 => 0x140e
  | 160 => 0x17cbd5
  | 161 => 0x144e
  | 162 => 0xcc3d2
  | 163 => 0xcc3d5
  | 164 => 0x15ccd5
  | 165 => 0x44c
  | 166 => 0x1715d5
  | 167 => 0x164d55
  | 168 => 0xd5655
  | 169 => 0xecd55
  | 170 => 0xd4ed5
  | 171 => 0x17d655
  | 172 => 0x19cc
  | 173 => 0x138955
  | 174 => 0x94b96
  | 175 => 0x5cb
  | 176 => 0x184e
  | 177 => 0x10c
  | 178 => 0x3c996
  | 179 => 0x184c
  | 180 => 0x104c
  | 181 => 0x3c092
  | 182 => 0x589
  | 183 => 0x585d1
  | 184 => 0x1696d5
  | 185 => 0xa59d5
  | 186 => 0x3d292
  | 187 => 0x3cd12
  | 188 => 0x443d2
  | 189 => 0x455d2
  | 190 => 0x3d652
  | 191 => 0x3da12
  | 192 => 0x3c452
  | 193 => 0x1643d2
  | 194 => 0x1655d2
  | 195 => 0x45712
  | 196 => 0x3ccd2
  | 197 => 0x3d5d2
  | 198 => 0x1a57d2
  | 199 => 0x1a8c
  | 200 => 0x5255
  | 201 => 0x139255
  | 202 => 0xb95d6
  | 203 => 0x15d856
  | 204 => 0xd59d5
  | 205 => 0x21555
  | 206 => 0x20b15
  | 207 => 0x155415
  | 208 => 0x140b15
  | 209 => 0xb4b96
  | 210 => 0x17d9d5
  | 211 => 0x256d5
  | 212 => 0x16d455
  | 213 => 0x144b55
  | 214 => 0x19d4d5
  | 215 => 0x45652
  | 216 => 0x1a4ed2
  | 217 => 0x1843d6
  | 218 => 0x1855d6
  | 219 => 0x3d416
  | 220 => 0xb83d6
  | 221 => 0x3d5d6
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2235
  | 6 => 6496
  | 5 => 3104
  | 4 => 114
  | 3 => 3
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
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (91635+((h/745+packedAt gbK7 (82695+(h % 745)*12) 12) % 2951)*13) 13
  | 6 => packedAt gbK6 (342118+((h/2165+packedAt gbK6 (311808+(h % 2165)*14) 14) % 8575)*14) 14
  | 5 => packedAt gbK5 (196578+((h/1034+packedAt gbK5 (183136+(h % 1034)*13) 13) % 4506)*13) 13
  | 4 => packedAt gbK4 (8284+((h/38+packedAt gbK4 (7980+(h % 38)*8) 8) % 137)*8) 8
  | 3 => packedAt gbK3 (246+((h/1+packedAt gbK3 (243+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff07c07ffc0fffff83ffe01fc0cf707c39f3f3
  | 1 => 0x3ff800781ff0f807fc1fffffc7349f8e264c7f
  | 2 => 0xc1ffff801fff0007ffe0ffe03838e1f3c78f9c
  | 3 => 0x1ffffffe0000007ffff00003fc0fe03f80fe0
  | 4 => 0x1fffffffffffff8000000003fff0003fff000
  | 5 => 0xfe00000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x5200c00a24010a3181312049804130340891b1
  | 1 => 0x252804310990d042240a4a960314068a224446
  | 2 => 0x80535880162a0094ca4095409828c150c58a98
  | 3 => 0x119dad5f40804127739c01832dc0fa03780f60
  | 4 => 0x21e636659bcce5c02008060437be0003b76000
  | 5 => 0x3800380603088600431018183efffdec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaece8faeae8c8feeaece8faeae8c8feeaece8faeae8c8feeaece8faeae8c8feeaece8faeae8c8feeaece8faeae8c8feeaece8faeae8c8feeaece8faeae8c8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36969
namespace PEqualNP.Outside.L_meta_36969
open PEqualNP.Outside.L_meta_36969.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 10 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_32 : Interval s1Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 60 := (concat bs1_3_0 bs1_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_128 : Interval s1Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_160 : Interval s1Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 165 := (concat (concat bs1_4_0 (concat bs1_4_32 bs1_4_64)) (concat bs1_4_96 (concat bs1_4_128 bs1_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 50 := (concat bs1_5_0 bs1_5_32)
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
theorem bs4_4_544 : Interval s4Atlas 4 544 7 := block_range (n:=7) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 551 := (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96)) (concat (concat bs4_4_128 bs4_4_160) (concat bs4_4_192 (concat bs4_4_224 bs4_4_256)))) (concat (concat (concat bs4_4_288 bs4_4_320) (concat bs4_4_352 bs4_4_384)) (concat (concat bs4_4_416 bs4_4_448) (concat bs4_4_480 (concat bs4_4_512 bs4_4_544)))))
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
theorem bs4_5_640 : Interval s4Atlas 5 640 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 666 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 bs4_5_192) (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)))) (concat (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 (concat bs4_5_416 bs4_5_448))) (concat (concat bs4_5_480 (concat bs4_5_512 bs4_5_544)) (concat bs4_5_576 (concat bs4_5_608 bs4_5_640)))))
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
  · exact alls4_7 i (by omega) hi
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
theorem bgb_3_0 : Interval gbAtlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 3 := bgb_3_0
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
theorem bgb_4_96 : Interval gbAtlas 4 96 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 114 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96))
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
theorem allgb_5 : Interval gbAtlas 5 0 3104 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504)))))) (concat (concat (concat (concat (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600)) (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696))) (concat (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792)) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)))) (concat (concat (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)) (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080))) (concat (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176)) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272))))) (concat (concat (concat (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368)) (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464))) (concat (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)) (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656)))) (concat (concat (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752)) (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848))) (concat (concat bgb_5_2880 (concat bgb_5_2912 bgb_5_2944)) (concat (concat bgb_5_2976 bgb_5_3008) (concat bgb_5_3040 bgb_5_3072)))))))
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
theorem allgb_6 : Interval gbAtlas 6 0 6496 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768))))) (concat (concat (concat (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960))) (concat (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)))) (concat (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344))) (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568)))))) (concat (concat (concat (concat (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664)) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760))) (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)))) (concat (concat (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))) (concat (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240)) (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 bgb_6_2368))))) (concat (concat (concat (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464)) (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560))) (concat (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)) (concat (concat bgb_6_2688 bgb_6_2720) (concat bgb_6_2752 bgb_6_2784)))) (concat (concat (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880)) (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976))) (concat (concat bgb_6_3008 (concat bgb_6_3040 bgb_6_3072)) (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 bgb_6_3200))))))) (concat (concat (concat (concat (concat (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296)) (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392))) (concat (concat bgb_6_3424 (concat bgb_6_3456 bgb_6_3488)) (concat bgb_6_3520 (concat bgb_6_3552 bgb_6_3584)))) (concat (concat (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680)) (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776))) (concat (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)) (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 bgb_6_4000))))) (concat (concat (concat (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096)) (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192))) (concat (concat bgb_6_4224 (concat bgb_6_4256 bgb_6_4288)) (concat (concat bgb_6_4320 bgb_6_4352) (concat bgb_6_4384 bgb_6_4416)))) (concat (concat (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512)) (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608))) (concat (concat bgb_6_4640 (concat bgb_6_4672 bgb_6_4704)) (concat (concat bgb_6_4736 bgb_6_4768) (concat bgb_6_4800 bgb_6_4832)))))) (concat (concat (concat (concat (concat bgb_6_4864 (concat bgb_6_4896 bgb_6_4928)) (concat bgb_6_4960 (concat bgb_6_4992 bgb_6_5024))) (concat (concat bgb_6_5056 (concat bgb_6_5088 bgb_6_5120)) (concat bgb_6_5152 (concat bgb_6_5184 bgb_6_5216)))) (concat (concat (concat bgb_6_5248 (concat bgb_6_5280 bgb_6_5312)) (concat bgb_6_5344 (concat bgb_6_5376 bgb_6_5408))) (concat (concat bgb_6_5440 (concat bgb_6_5472 bgb_6_5504)) (concat (concat bgb_6_5536 bgb_6_5568) (concat bgb_6_5600 bgb_6_5632))))) (concat (concat (concat (concat bgb_6_5664 (concat bgb_6_5696 bgb_6_5728)) (concat bgb_6_5760 (concat bgb_6_5792 bgb_6_5824))) (concat (concat bgb_6_5856 (concat bgb_6_5888 bgb_6_5920)) (concat (concat bgb_6_5952 bgb_6_5984) (concat bgb_6_6016 bgb_6_6048)))) (concat (concat (concat bgb_6_6080 (concat bgb_6_6112 bgb_6_6144)) (concat bgb_6_6176 (concat bgb_6_6208 bgb_6_6240))) (concat (concat bgb_6_6272 (concat bgb_6_6304 bgb_6_6336)) (concat (concat bgb_6_6368 bgb_6_6400) (concat bgb_6_6432 bgb_6_6464))))))))
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
theorem bgb_7_2208 : Interval gbAtlas 7 2208 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2235 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800)))) (concat (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928)) (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)))))) (concat (concat (concat (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)) (concat (concat bgb_7_1248 bgb_7_1280) (concat bgb_7_1312 bgb_7_1344))) (concat (concat (concat bgb_7_1376 bgb_7_1408) (concat bgb_7_1440 bgb_7_1472)) (concat (concat bgb_7_1504 bgb_7_1536) (concat bgb_7_1568 (concat bgb_7_1600 bgb_7_1632))))) (concat (concat (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760)) (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 (concat bgb_7_1888 bgb_7_1920)))) (concat (concat (concat bgb_7_1952 bgb_7_1984) (concat bgb_7_2016 bgb_7_2048)) (concat (concat bgb_7_2080 bgb_7_2112) (concat bgb_7_2144 (concat bgb_7_2176 bgb_7_2208)))))))
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
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 34, 42),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
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
def fullWord : Sig := 0xfeeaece8faeae8c8feeaece8faeae8c8feeaece8faeae8c8feeaece8faeae8c8feeaece8faeae8c8feeaece8faeae8c8feeaece8faeae8c8feeaece8faeae8c8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808936 * 2 ^ 32 + 4209699016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36969.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,5]⟩,⟨.or,[2,6]⟩,⟨.or,[1,4]⟩,⟨.or,[3,5]⟩,⟨.and,[3,7]⟩,⟨.or,[0,10]⟩,⟨.and,[0,9]⟩,⟨.or,[1,12]⟩,⟨.and,[2,13]⟩,⟨.and,[8,11]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4209699016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4209699016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36969

open PEqualNP.Outside.L_meta_36969 in
theorem PEqualNP.Outside.L_meta_36969 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4209699016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4209699016) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
