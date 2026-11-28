import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_38845.Model
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


end PEqualNP.Outside.L_meta_38845.Model

namespace PEqualNP.Outside.L_meta_38845
open PEqualNP.Outside.L_meta_38845.Model
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

def SBf (j : Nat) : Nat := [7, 7, 5, 7, 5, 8].getD j 0

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

end PEqualNP.Outside.L_meta_38845

namespace PEqualNP.Outside.L_meta_38845
open PEqualNP.Outside.L_meta_38845.Model
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
end PEqualNP.Outside.L_meta_38845
namespace PEqualNP.Outside.L_meta_38845
open PEqualNP.Outside.L_meta_38845.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x3040003ce0800002c00410054420a105f00090000000dff10ff20bc43fc40fc30ff31fd21fe43fd32fe40bc40fe42fe30fc31be43fc10ff21bd41fd43fc32fd30ff43fd41ff42fd10fe21fe32ff32fe41bf41ff41fd20ff40bf42ff30fe31fd40bd42ef32fc42fe10fd31fd42fc20fe20ec32fc41fc21fc43be40
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xe8082999100808000808e00938081038380800104b48b07008280802c00800000079901058000820009000680800001818d81800403802c0000040700018702030080929481888200090182db14943d72a0653e54886b8a6904fd5110d7a1065cc320c278a0a15d14520afa9a853f54cca7ca1a0cf94c40b7294633c548427ca810eb0cb419f2a4653d54c839ca6196b90f329e2a2656d52d0f5886194f553309faa421ad52d067aa990cf151209ea88873e54c4278a8884f552219fa8a85ad540cb3ea6a14f550219ea8e853d54c427aa8086b0c9419eaa063cf430cad8a4984fd5132b7a92876d521027ca721db14931d7a16659c438ca78a898d714d429e2a6633e50d0a7ca0204fd51319e29a85af32d0678a9104f54840d6a12413d54082dca5a0eb54840b7290219c5350ab8a6884f95320aea9c43ad42086eea2986bcc941af298213e548c27ca621edd4541e619663cc430ca7aa9214f94e408e29a856e528c33ca621cfd5130b729081cc324c678a6a0cfd50309eaa4616e52d0edaa5184f1533296a9081ad420cadaa5a0d7d4d209ea888174514c27aa421f30ca309faa2413f52506dca5196710c329f2a065ae430ca7ea9106bd53329e2a2613e5410a7aa5206b0c840c6218653e5448678a8185bd4930d62a6653f54cc67ca820cf950319e28283ac32902dea4884f55231d7296833e54cc27aa3204f54b41bba8a413e53d0a7aa521cf95321b7a92633e5010e7aa9195754c10d7990813e54042f0a098cf552419f2a0416e530ca7ca121d7d4d10d621e653d5190ef6a098cf55032d6a1665ad42c835ea4a14f952319f29e836d528c65aa5a0eb94840b6292215e53886daa4084f55121d799481ad428867ca1206e94040
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x26d00204400000138100110f04000900000000125e0c01c01450001920800040400000000001c00028bd9732d070c530c9418b588505068c63508218b588540c28c6354840c314d424820c63548408b58854cc70c6354b41c315032cc70f63548408b58a54cc28c6350b209318d52d063561153328b58a54c428f6510c328718d52d070c540c9319318d521021c6354840a958454cca8d6110c32c318d521022d6215210a3980430ca8c6350a218718d544862f62546438d584540c30e530ca408b58a544868c6354b41a398f54cca2d62942438b18d52d062d650cb41a398e430ca2c6354840c3d885350b0c53d4942c3950328c22f65cc840c3d8d52d062c65509208bd89519030c540c830d20c8504c63860551218b58a540c62d650c840a3594430ca8e6315332c394d428872542145208798f548828c635092087594430ca0c6354b41
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x80000000e0868239a8428a41031cd6215210818e6b14a890c0e73d89519020639ac52a621215c76510c32818ec29a849040c735885050682b88a819061419c76214d42
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
  | 6 => 2*((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s1K5 (800+(h % 30)*6) 6) % 50)
  | 4 => 2*((h/76+packedAt s1K4 (4455+(h % 76)*8) 8) % 165)
  | 3 => 2*((h/55+packedAt s1K3 (2280+(h % 55)*6) 6) % 60)
  | 2 => 2*((h/17+packedAt s1K2 (490+(h % 17)*4) 4) % 10)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0xffffffe07ffffffe07c0fffffc1ffffc8fe3f
  | 3 => 0xfc07ffff80fe07fff800f81fffe1f01f0cfcc
  | 4 => 0xf0007ffffff0007ffffff001ffffe001ff0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2045088c4122440805949292501229541350d5
  | 2 => 0x448a31103244983160290564a64152a8c8a62a
  | 3 => 0xa9135a2490e90cdaaa8289b13ab41c0d70cb4c
  | 4 => 0xcc2c64492481d164d34f2041cd298031ad0db0
  | 5 => 0xe307871c70e1e7f1c73ce780e3118c1fef000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaa0a0faa0a0a0faaaa0a0faa0a0a0faaaa0a0faa0a0a0faaaa0a0faa0a0a0faaaa0a0faa0a0a0faaaa0a0faa0a0a0faaaa0a0faa0a0a0faaaa0a0faa0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_38845
namespace PEqualNP.Outside.L_meta_38845
open PEqualNP.Outside.L_meta_38845.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xd830
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
  | 0 => 0xfff80ff01fff00f83fffffe03e07ff803ff27c
  | 1 => 0x3ffffffe07fffffc0fc03fffff81fffce3f8f
  | 3 => 0x3ffffffffffffffff0003fffffffffff03fff
  | 4 => 0xfc000fffff8000fffffffc003fffe000ffc3f0
  | 5 => 0xfffff000000000ffffffffffc0000000fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x184a6311c51235380b2cd4e60e433c8616f23c
  | 1 => 0xa950a522432454594055512a52c90d2a4e1685
  | 3 => 0x52214a448848a0a295028254a5165254b0295a
  | 4 => 0x63458c89120ec6cce69b181839e58418eb43e0
  | 5 => 0x83860f0e1c70f8f738e3e39f01861860fdbc00
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaacc00ee00cc00eeaacc00ee00cc00eeaacc00ee00cc00eeaacc00ee00cc00eeaacc00ee00cc00eeaacc00ee00cc00eeaacc00ee00cc00eeaacc00ee00cc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_38845
namespace PEqualNP.Outside.L_meta_38845
open PEqualNP.Outside.L_meta_38845.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x51426c04420051811811090c1100416fd41fe31ff43fe21fd31fd32fd42fe41f421fe40fd43fe30fe10f721f510fc42fc10fd10ff40ff30fc21fe43ff41fc40fd21ff21fc43fe32ff32fd20fe42fc20ff20fc32f710fc31fc41fd40ff10ff42ff31fe20fc30fd30
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x2000090c6448002001857060000001410608200270200189022c585100400e0c196a00405027bba8a413e54c86eaa3205d54620aea98857551842e8a2905754f40f2292217652442b8a6885d94b10f9a82215f53442b8a6a0d7d4d41ba296213c544ca7ea8885d94430af29e813d54cc278a8907994821f210c415c5350aeaa3995d54440bba8a657551d0aeca2205d14542da2a22178504caeaa190f9d4910ba28a655e53c867ca8194f55230bb288215d530836ca990ded4142bb28c813f544c6bca7204f55020ea29a21d753442bea6a15d54430af29885b554c867aa990dd94821baa804375518c36ea8884f95230bda82655c534827ea8905754e40ba28a877651886eca3105e14142b629221d553c87c842104f95020eb29e437651082c8a4885d946309f2a6617651ccabea6904f15110cea18876f52442eea2a15794c20ba29221775150eeaa2104f550329e2a2635d53c867ea8995d94742
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x38d114c52443475314910c915052442946150c43c9d5052443165494f219998a52443145414d10
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
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/21+packedAt s3K5 (704+(h % 21)*6) 6) % 44)
  | 4 => 2*((h/44+packedAt s3K4 (2484+(h % 44)*7) 7) % 92)
  | 3 => 2*((h/9+packedAt s3K3 (304+(h % 9)*3) 3) % 8)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xff81fff81fffffe07fffff03ff03fffe7f8e3f
  | 1 => 0x3ffe03ffe03f81ff83f01ffc1ffc1f01b8f3cc
  | 2 => 0x3ffffffffffffffffc001fffffffffffc0ffff
  | 4 => 0xc00003ffffc001ffffffe0001fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffe0000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x84a42888c489286014b2a521252139541b8615
  | 1 => 0x950c999143922ae581568b650b651a0cb8b2cc
  | 2 => 0x221052220924410aa808128a528a44a940596a
  | 4 => 0x3459634492074db34e6cc0c21cf38831ed03b0
  | 5 => 0x386183871c3871dc738f1cf380c210c1f6ec00
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeae0e0e0e0a0a0eaeae0e0e0e0a0a0eaeae0e0e0e0a0a0eaeae0e0e0e0a0a0eaeae0e0e0e0a0a0eaeae0e0e0e0a0a0eaeae0e0e0e0a0a0eaeae0e0e0e0a0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_38845
namespace PEqualNP.Outside.L_meta_38845
open PEqualNP.Outside.L_meta_38845.Model
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
  | 4 => 2*((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7ffe07ff81fffc1ff81f07fe1ff80ffef233cf
  | 1 => 0x80fff81ffff81fe0fffff81fe0ffff013fccfc
  | 2 => 0xffffffe001ffffff001fffffff000fffc3ff0f
  | 3 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa62314432530c053b05432a09c8a9547211c5
  | 1 => 0x262450c9108124a0492b490620526a0c16c45c
  | 2 => 0x148882834524116a04129455520144a9816e0a
  | 3 => 0x58d1241260365a53964086199ca58031e80ba0
  | 5 => 0x60e1c71c79c79f9ce79ce78118c608c1ffb000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xece0ece0eca0eca0ece0ece0eca0eca0ece0ece0eca0eca0ece0ece0eca0eca0ece0ece0eca0eca0ece0ece0eca0eca0ece0ece0eca0eca0ece0ece0eca0eca0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_38845
namespace PEqualNP.Outside.L_meta_38845
open PEqualNP.Outside.L_meta_38845.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x6877e520c3eaa2105f14530bf28c65f840c82f8a6a05f94040be29c43bc4390afaa521fb4c832bea8e617f53483ee4310df94e40f7a92817f548c2fca1195fd4940ef98c63bd42502f8a0a15f15332df21081ee320cafaa6905fd5021dfa0481ed4210bda40105fd4910bfa8a857e54086fea0a17e94031bf28887fb40c82fca2085f94241beaa663f830c83da6490df94c31beaa4417f54cc2f8a810778c130bea8e41bc54482faa7215f94e20fb28c617f52c43ee21087ecc320bfaa4637e52cc77c86215f94032bea80837d54cc2fca4886fd09409f2a0417c53042fca521df94720bfa9e437e53d02f8a4a0fbc8220ef1926576518c2faa6105f95120fa18e217d53086fca5185f94620de218837f524c2eaa2106f15132fb10e217e518877ca910df55210ba28a657d540c2f0a0a15f54e21dfa08837e548c2fca420df55242bf28841fb20483de8510774c431bda8285f940842faa2195dd4543be282657e53906fca110dfd4a10faa08837d540cafca518df14f20bf28c837e518c7be64195fd4931fb98a217e528cafca3a05f94430bf2a2637c544c7b88618df54342dea1887bd42d02f8a818dd14543fb20883f431087ea6218df54630bf284637f504cafea890df54f20bf29041f731c86faa4087d10431eea9841be43502fca8216f50441dfa1681f651102faa690df54b40beaa6657e540cbdc6490df55130deaa021f641c4278a8907d88421fca02217f540c2fca198fdd0731bf29e837e50842fca910de54041bfaa0217c548c6fca5985f15221be2a0617d50906fca5215f54a21baa88817f52506faa718df94831bd28443df4390efca9885f54642bfaa6417c54c87d885105fd4d41f710a43f7318c6faa8105f94732bba8a657f51482f8a61077d4d41fda02817c544c2faa3995f54e32ef18a637e54cc2faa7105fd5120ee996617f5350afca990fd50710bf29883bf544c6fca710df14943bfa9821f5100437c85206f90f40be29e217c52502fea8886f90e41bea96837d54c42faa1195ed4132bfaa0417f53503f6a0a14f95230aea98417c54842fca8085e14132bf28c817e5310fbc8621fe14142bf286877c5150afea9885f54f21be292217e53102f8a8995e94031de216837d52c42fca6215b54831fa90a21be540c6faa4206fd0e43be294217e500c6faa898dfd5220beaa641dd324c2faa1216f10840bfaa6657d5210efea998df15320fca00817d53d037886216fd5120bf29861fa20082faa3a1df54e41df21a877c53883f2610877cca32de21283ef324cb7aa8105f95232be2a4616f52502fca0105fd4e20f6292817f53442fca9907e08210df2a4617651102f8a098df94010be29843bf4290af8a090df94341bea96637c54442faa1a1df94042bea9e21be4250afea2a07b94831beaa241f950106fea9195f94c32
  | 1 => 0xf41502fca918fbc8421bf298417e50c86f8a9107e4c110fc102217f544c7e8a2994f95221f7a10417c54c42faa9207e54031bf280437f514c37e8320d7d4d41deaa443f731c4278a898df94041bfa8287bc43502f8a4985f95121bfa9e41fb10843eca2107bcca32bf2a4417c548cafca210fd84110bea8c217d5010afca818df94b41be2a0217c520437c82a0df95132bfaa421bd41502faa910cf55020bfa90217d51d0afca021ef50040bf29e217e53c87f2a110cfd5120bf29a217d52902fca610df55031ee29a83f9300c2fea098df94630fc90041bd43506fca998f7ccb30fd184217c53842faa8995f54c40bfaa2657d50ccbda6590f7d0e31beaa2217d510827ca8087d0c510dfa0e817d5310bbe60185f14532be29a43f7514cafca220df54f42bf2a0837e510c6f4a020ef10e41be29a417f5150ff660105f55010bf2a081fb304c2faa010df95110fb10a21fa40842fca1a17710e31fc180417d548c3f680105f14d41bf29081ec420837a87a0efd0f41f7102417c53c87de85215f94230beaa6437651082faa620df54640bf2a0877c5150efaa6885f94e43bea90617d52907f080107e8c110dfa1887df4350efaa2217750c43de21e8175518c2fca321df14931bf28481f7410c6faa920dfd4121beaa487fb504cb7e86a0df54620bea9661bd41d03ee4290ef10a40fc28265f6310c6faa321f7cc930dfa00817e52d03f480884f15132faa8c61dd320cafea8197d90510ee980617d52842faa7087dcc421bf288857f5250efaa221df54440bea80637d52882faa3195f94c10bfa9c43fb10443de84a15f94a41bf290857e5090efaa7185f94220bea98217d50886f8a810dfd4532fa20e63de53083dc6590dfd4c20f790c437e53842faa198df94b10fba0c837c54cc7f460185f94d20fd984617c52c43f641106fd0842df218833e540c6f8a6a15f14d10bea94617e51d0efaa118fb90842faa0a217c540cbf641084fd5132bf2a0417d510c2fca7906fd5132beaa463df310c7eaa2205b14940bea92217d54486fca7a15f54e40bf2a6657e5190afea610dfd4e10beaa043fa50107ee20084f55230df20281ed21087f681205f95210bf286657e5390bf4a110fd48710fd080217d5010efca8185f94821fd20081f45150ef8a0a1df95130dea10855e530827aa910df54243ae29a83bc544c77ca8105b94831bf29a43f7314c67ea898df54740be28a41f75150efca3985f141419eaa0633d54042fca4085f94a10fd902217d50c86fea690dfd5221fba0a837d52d0efca421df94030bf288817f544c37c87216f95010bea806579500c6faa420ef90b41bf28865ed520c6fca5205f15121fa18e43f521086faa1a0df94742bfa9e21f910042f8a8905e54221ef984617d528c77aa9185f54831bea9e83be42506faa9195f94832bf29
  | 2 => 0x10230030280110006044390402e0241c01c001180502c0304c0b0000204c030340606c01000b10240c0044502406038000011c01406004020100001400020000c806004190d8000040001477000450a0070280203c03000020000005c0300008000000040030802089b200408060000084a0001f0053f000010082a1680e5781f0180506c0700000004180344e01464020000000304c000140c000030d405054060003300003000370a00501c0800800000000000978c5b00004000000040100c000bcb74681014c0001960010310c80007c000f0011f00000016000001602d010007880500000000000010200489018240006b2c00c034000100100413000090580000ccf00c0005c306fc000082c10400000090b4040340002c040180500001175391500609c0200000020000ecc200c0314401000020140702800174be4e013020000240618c001cc3d0101000000000150000400000efa18637e5090b7aa818df14540bfaa6437c54cc2fea0a0fbc8020bfaa063b
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x540442786054b419b98b54c427461551328f596431063e64145309e181534863d6590840cd547401027960150319b988540c65f654c431c714e425067661152208f59352042d463505108f99352c431e5494c209d18553d027b60548438f191524425f654c0309d594410c66d6214c10dc147504ca3d6414c219b98853c423d64940309e98054086f2618c110d5d0c5150ef2600c510cd551510823e64940309e1815210e7661150108f191528432c43149408f593530426f6548020ae18142d02786054b319e580540ca7561942439b18953442776155131cd551518c25d6314810ce55150886796014e219e982544cb365494630ced0550106746154d208f99353c873860550209b98b54cc26d62d5310e5d0f410c67a60946428f593530823d659502097d8d524427765440109ed8154482796094642da94a500c67761551309d987548c23e6494d209d984530826f654c832cd951518c26f6255110d514f41506d46150c438f993538871c5350d419d98650ccab46150f419bd8953443646154831ae1814210a9c63505409d5845050a6d62d5330bc58440082776154d21cd153514ca7465485109d584548c2e5620c7109798f540827a65c8110dc5845050b395444010ea108400823f6454830ba588300825e6314a10ce952500c63f6454f10da54a500c67b654c0308f990504873843540418f590514c27965840108f990540426d6215030dc982510837151500409758f54c863e64d4c208fd954210a3e6415020b658c208433654544209bd95210877151900409e594400835953cc020ae181425035653944209e983548863c6454d219ed95401027461551308f990530823e6414e218f59053042796014c219d987530423e6414f10a718d41d031d5310c42ba1814210a7661150329bd954210a3f6550441ae191200827665cc5109e98054042b46150c43ba18940842f26108110dc505501065f63551108fd954010355530c7108f191520c2796015021ec50540442766114142bc58440c823e64d4c10cdd53514cab5640c7108f994544ca9c63504419dd855310b1c5310941cd10951102776154f20dc9845050b1c6355031b9588314427561d5020bc982214425d63150209d587548c25d63d50209b988530433551500409e983538863e64150319d195414423d6414e21ce552500c63f6454d20cb952520c67a6014543cb14b4250275650c421ad59221c423d65950108f593538866e6215030dcd44504ca3f6454c219ed95100423d649463297d8d544c6b66190941ead0b4008279650c0208f990520423c6454b319e583540c63d6494331da14b405023e64943328f59352c42746154c42ce952508863e64951328f993520426f6255130cd552510823d64d4e109d986544cb3854141329758c540863d64943329ed81544ca3e64d4e10
  | 1 => 0x4830145609afc06002386400340002c041401204d0160180016052b0094e00300085e001385506023d0000e00018000c0706028080006074121401800500a000200a220013098010502402014183458029e181544ca7561d52329718d544865f654c832dc9805150f2e431494097d954310e3e65d0d41b658c204425d6510c31cb951520c6b9648c2108f59052042f160107318f19153c82b5640c5109e983540c76a52540319b189544433454cc5318f99251c827561d4c209dd95310c6766114810cdd50514ca7960946329dd8553d023e6495131ce15320483695208210dc144504ca7561150329e980530423d6414f10ad592214423e64951209b58b540c67b6054b41ba189404433941540418f99250cc63d64d4e20ae590208433b5414132cd185540c73a54540319d984548c27b6054d21ce551500c67a60152218f191534832d5494831ab191200837160145439758f548425e6315020c7553430c6796015221dc982518c36952540319718d54442756115220cb149415027a6014e219d58650cca3c6454d109dd85544ca3c6454c218fd954310e6c6255130cd553410c71d5454c20ae982435032c52509409d98753883365494420ad191310c67960d53328fd9153442756115030e510c410c65c63549109ed81534827561d4e209e583538873954d0020ce9085050b7351d41329ed81544863e65d09408f99053086ad6210c429798c540872d5454831cb189540833554c40109798c520432c5488120d554d510827765484219798f54842d8604cb309759653083555394420cd150514ca3f6454f2097d8d544867b6054b31dc90550107395494221cb553420823e64944218f590504867a60152319d984540833a43540418fd91524433a5454221d554c310872c52901409e5805150e7661942438fd9152cc67a60150319b988530873b54d4132ae592304433554946309e980540cab46150d41b958831c871d5494c20a7191310c6e862500409798f54c867a6014c219d987540827765504418f59251c826d6510820cd90c5150ed463507108f992518ca7b65480208f994544c63d6494d20bc580410c67661150309d987548ca756114c20c714e415073642544408f19153c427661d4c20c795153082746154f208f590528423e64d4e20dad085050a3e6515120d594d510831c53d0d419b195324873954840108fd9153486786055121ae590204433554440109e98352042776154d208fd9152842d463504419e580548c6ac62500409d586544ca3d6494421cb14b415025e6314c209d584540827a60946328f99053043586054c209b588540c67a60d53328f596540c6e4614cb219758c528423e6414a109e195304427960d5221ce153504ca6e62d5031c7152314c63d64d4f219bd89544826d6214f108f590530827960951329e19
  | 2 => 0x13c261e1980c565810810360b0181874c503010000f020000e3001000b8030314e824500004045e0a03c029e019c00009038000005030002e163285400130209c28002a8208c05010b86403448013e23160240c001280c02031c0000a00110c8c62
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x6c3105406d83981895150040a30e6a0aa020e145398642506a839a82a80832c5c46050940962e030a86a0e9043580410c68a3a2a618e212c5c66090d40c50c4302a8104a8745883008254382c421885891895150040b20e6a0a80885147454c310868a38aa6218858318c5250540a50e8a9041086a0625054044298b88c0aa041a81096110020c28c630aa818d2a7090c5250258b84c3212834c5c06155031
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x100921819c24314940c10635c06155031c20625c46055020c80731894150110c10535c26190941
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 616
  | 4 => 414
  | 3 => 25
  | 2 => 5
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
  | 6 => 2*((h/27+packedAt s5K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/275+packedAt s5K5 (16632+(h % 275)*10) 10) % 616)
  | 4 => 2*((h/159+packedAt s5K4 (15732+(h % 159)*9) 9) % 414)
  | 3 => 2*((h/15+packedAt s5K3 (1225+(h % 15)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s5K2 (300+(h % 8)*3) 3) % 5)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf07ff81ffe1ffc1f1f0ff87f8fe03ff89e33cf
  | 1 => 0xff80ffe07fff87e01ff0ff87f1fffc00e3ccfc
  | 2 => 0xffffffff801fffffe000fffffe003fff03ff0f
  | 3 => 0xffffffe007ffffff0007ffffc007fc0ff0
  | 4 => 0xffff0000000007fffffffff800000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x150a88c51125440507892c4a8322a5508e11c5
  | 1 => 0x2126914325084ca009985cc19149a830a2c45c
  | 2 => 0x4214220a0c52016a20009115240512a3016e0a
  | 3 => 0xa5844904803125352220006489600c5540ba0
  | 4 => 0x8c60871c719c679c9ccce66001182306fbb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0fee0eca0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_38845
namespace PEqualNP.Outside.L_meta_38845
open PEqualNP.Outside.L_meta_38845.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xc8004004008001a00100200000680049102a2c000000000000e000080002100003388701007080000000004080100005f54c01fe32007fd0005ff1001ff90c09ff5000ff88005fc41007f50c09fd52007f90809fd51007f44005fc31017f88409fe5400ff08001fd42017f94403fe50007fd0c03fc3001ff14c01fd2000ff8c007fc43007fd0807ff32017f14401fd21007fd0405fe31007f4c403fe10007fc8001fd32027fd4401fd30007f50405fc21027f14809fd50007f500097f5301ff0c803fc40027f94805fe41007fc8401fc4201ffcc409ff5400ff90009fc54027f55003fc10027fd4c03fc5001ff94c09fd53027fd4807ff30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x868208ff0c920007fcc888003fd624c403ff9824000ff50f210f7feca98857fc5410807ff98e8603bf98a32137fc8299003ff42484017eb226203ff14d3100dfec098003fd21c8005fe18a8209ff54d20005fec4a000ffe314c001de3224033ff98d421dff8a0a1827ff54480057e30a860eff88530017fc839080af4614c861feaa68409ff94920017f8a2a0807fc30500017eb0e8602ff8c510005fac898002ff635083dfea926200af1912001efaa6a180fff4350c05ff90a4200ff1913100ff0609800bec2148405fe20a422cff9444201fd86499003fd3248401ff216803bff04143057f8c62100bfe2144001dea12802fffd424207ffeca98063fe534845f7eb2c8400bfd912101dfcc7a080bdc314c401feb1e8400ff50941007fcc4a184bfc6550001fe3128034ff19542077f8c29800fff538c885bf882a600dfd9542005fec09900bfc1048475ff31e8427ff551320e7faa9908bffd5390873ff10e8417ff14121007fe869082bfc329081b7fb2e4034dfd4d4215f7880210cfff315082bfe32e8005ff18d1001ffc64980e7fe31d082bffb068414ff0cb4001ff860988d3ff52508017eb168603ff90d4305ffc6390012fc655087fff20e8637ffcc242005fac9190027d6510815fe1088403ffcca32025f8ca98803fd61c8001ff1922000ffd9110057fca521036fd65c8001fbb0a6402bf5874100ffea1a0002fb60508017fb12862fffd5242057f8cb19003fd63c8401fea0a4000ff5813105ffc43900bbfd501081ffea926004bf19742057fec99084ffe61d002bfe2168203ff14d30007fec690012fe658c803f61024002ff8872118ff880a1083fc4350401ffb226000bf189300fff840a08277f53480077f31a8409bf59520007f884a000ffe314c8017fb1a4040ff5534304ffaca9010b7c6154c05ff18e4209ff19520004feca88017fc5344031ff21a4226ff8853215ffc202101bfd5244057ff1808401ffcc340025f8ca9000ffe3150c43fe32a820dff99720147f8211905bff54d005ffeb2c8400ffd0a32007fac2990dfff319087fff10e8600ff99121005fec6a000ffc3150c1bfea964000bfd9131057fc659005bfe52d00057e30a802edf994420b7faa7a002bfe32c8461fea968442df0855300ff8809004bfd5150053fe20c6426ff18532177fea22102bfc611086bfe2048409ffd4920025fcca988027f65508037f326803aff14f421e7f8a2a180bfc3148405fea8e8203ff8c743167fcc221007fc30440017eb0c8403ff94e32015fec298803fd614c003fe1826026ff9853201ffc649900f7e3054c077eb1e8601bf18321057fec990002fd6090801ff212822fdfd4e42006faa6a00d3fe5450811ff98a4000df54f4120efc20a988bfe40d04017eb0e840cff14f20007f88498806fc6090803fb0822000ff58f20
  | 1 => 0xbfe544c405de20e822aff152320a7fc87a004bfd5450001dfa128000dfd95200affec1a0803fd63d001fffa926000ffd81321a7facaa100bfe104840fff30a4000bf18931007fa839007ffe6050405ff20a6202ff5072101ffe61a1803ff4250403fe2022002bf98520007fcc5a0012fe6550007bfb1aa62fbfd9642004feca90092fd65d040dffa92203bff88143007f6c0a1102fd65d0c07ff98a6040ff94b43047f8869000bfc41504037eb064040ffd5343025fcca9807afd654c453ff28c6403bf993431b7f8a3210377f53c8005ffa8a4201fe08340006fac0a9802fe644c405ff18a6201fb0832000ff84090043fe21500057f30a6000ffd8121005fcc5a080bfe21d0407fea9e8615ff9534200dfcc59000bfe31d04073fb1aa600df5895301efe64a9883fe53504697eb2a8402ffcc510006fec2a9803fd3250405fe98a4210ff8c540216f882a987bfd544c461ffa968400ff909420bffc40909077c1054c27fe18e802aff542320e6fea790807fc40c802bfe32e8203ffd4d430aff881a1003ff6150c01f7a14840fff9513006ffea59000f7f534c83ffe2828203dfd4f43007fec09881bfd65440017f3168600ff50d10025f8cba182bfc218c84fffa926400bf58f4109ff8a3a0002ff648c807fea1a6003bf98f200d7f88190847fc635000dff2a22003f7cc930005fec6880bbfd51108097e32a822fbf98842007fac3a1072ff65c8405fe08282049f19510007fac3a1803fd64c8001dfa1e8204bf99721057fecb2100bfd214401dff20a6000ff9092001ffe64a18ebff31d0801bea98840aff1823215ffc8021003ff435044bfe202640cffcc720007fc65a0812fe6548001fea168019ffd4d210e7fea590827fe65480017f3246402ff90510007fc64a00dffc439087b7eb2a860aff08242015fcc2a002bfc52108617fb2e8412ffd95401effecaa18a3fe208c8037f3068600bfd8141005f8c4a1807ff4048051ff0846400ff4853010dfecaa0857fc43d0005ff98e4211ff14d401a7fea0a1083fe435041bff2a64003bf18d210aff8c5a18cfff30508097e32e8000ffd894107ffaa8980cffc3250805ff10a620affd8e42007fcc4a000afe61d0807ff98a6418ffcc921007fa87a1057fc62d0469ff2928400bf1913011ff8a7a0806ff605000dfeaa22039ff90742007fa8790007fc20d006bdf2048412ff54940127faa5a0857fc63d0417ff20e4004bf19442167fe2021037fd54c8069fea9a8400ff5912101ffa869902bfc60c8401ee9926034ffd51420aff881a186ffe63c8455ffa8c6400ffd8d420e7fca99080afe61d0017ff30e4040ffd4b43007fac1a0802fd618c883be302a63cff1054320efc80a990b7e6154c57ff2808403ff8c93113ffca899007ff5048053ff30c6401ef9034001db8c6a080ffe5350c45fe1
  | 2 => 0x21057f84190897fc204c8017fb0a8002ff841410fffc60a0803ff4350803fe2824001ffd013001efc62a98937f53d0477ff2828600ffd8d40067fcc79002bfc6390807bfa9a6200bf5912000ffe808800eff6450c01f6996420aff90b20007fe85210cbfc3150803fe0824000ffd913101df8c7210f7fc5450c01feb226020ff98d41005fac9908ebfc32d0867ff21a843bff98143007fec290007ff5044005ffa8a8203ff0c9301bffca72100afe6150805fb10a2001ffd41300affecba10aaff658c849ffa968214ff94f40007fac1190dbfc419082bffb0e8600ffd0d20007fc8499053ff32d0005fea0a6215ff1034100ffe6098007ff50c8077fe302863eff083430e7fccb9083fff544c003fe2028017ff9412120efcc0a987bfc654c4077fb1a8612ffd49401e7fca2a1817fc3244007fe21e8601ffcc110007ee42908037c6454c15ff2164242df88553017fe2090803fd62d0c097f32e820fff949300fffc40a0823fe4348015ffb2e4200bfd85200cff8a89080ffe3050c0dffaa22015ffd0b4000ffe81900027d65c84097f32a842eff5484201ff864990d3fe6550865ff30a8406ff9491016ff8a62100bff31d04017f3224206ff54d101aff8a121003bd435047b7fb2a8611ffcc540005fcc5a00e7fe61d08017fb128200bfd913201ffe6099003df63504037f302640affd84421f7fcc1a1807ee2048055fea8c6400ffc874000fbc6098007f82048005ff28a4215ff10740187fea1a108ffe63d0439ffa86423cff08543007fa65a000f7d538c815fe294643dff99543005fac7a000bbe4150465fe28a8401bf983210f7fea49880afc61c8057fe180840aff0cb2000ffe6190057fc65d0c25ff2a28021ffd4d4100ff0819001ffc3148051ff2046415ff953410eff880988f7fd5050c61ffaa68400bf59110007fa86a0003ff43908097e32c8430ff54f42175feca2102bff6010833fea824200ff50f4106ffea990007fc50d0001feb16821eff99531187fca5a1003bf6448015fe1964200ff18930005fec498803fd414c015ff2964027ffd4132017f84290812fc65c841bfea9e4037ff90e42017ec439080efe63484015fb224007ff14520017fa8288043fe4150005ff20e8203dfd4d3000ff821a006fff30c8477ff082860aff1863201ffaa69900f7c3054c07ff1846402ffcc5310e7fea990803f4614c825feb2a8040ffd43430077a84210037f654404fffaa26400ff58141007fa42a0057ff43d0015ff2964227ff949320aff8cba1006fe6048405ffa0a4206dfd4d10057fecb900cffc4350815fe32c8400ff5894101ff865a1883ff32504697eb248400ff509200e7faa790807fc404c07bffa8a8629ffc42321e7fcc2a185ffe3048461bfa9e8436ff0c642127faa9a080ffd434c451ff2846404bf1953206ffacb9007
  | 3 => 0xe3068602bf9863214ffc4319003fe425002ffe1824200ffd0f21015f8c2a10d3ff5350807ee21a8601ff88120007dc84210fbfc50d0c49fea9e8202ff145101af78812105bff53d005bff9888400ff1912100fdc4190003fd424c07dfe0868604d7d8d53175faca21006ff62480013eb2e8021ff1494100ffaa1a006ffe43c8407ff21a6435ff8424209ff843a0057fe5410811ff31a4001fe1014001dfec4990e7fc51d08037f3008403ef10d43025f8ca980d7fe2090801beb2e4203ff14e32007fac09090b7e4154c077f31a4041df10153057fec31900efe6390801fea122002fd10541147fcc1190cfff3250803de206800bff0c720005fac69005b7e65d0003ffa028015ffd0740007fec899027ff5348001fea188403dfcc55302fee62880bfff51908097e32c6400ff5854200ffea0a0003ff625004bff3026400ff5844200ffc61a0003fd63480017f3226000bfd85430fffca0a0802fe64c8005ff882822cff90442035feca88007fd3048001ff212620fff9953001ffc87a182ffc51c807bfe32a861aff9832101ff88698007fe10d0023fe1928000ff58943137f8a29900ffc314c85dff3288400ff58e42005bec6a0893ff50d0403fe9022023ffcc34100ff8409803bfe614c033ff32a422aff54a3211ff865a0803ff4250815fe30e4001ffcc140015f8c3a1002fd644845dfeaa08402ff147211a5fecaa104bff5450001fea164005ff10d1000ff84088012fe6544001fe2124208ffcc92001ff66098002fc644c82dffa8e8001bf18343127fea9a082bfc601087bfea8a8600ff58d40025fccb2104bfe5250075ff9868403ff0c9310077e8421093fe52d04817fb2e8612ff54d40005fac1a1806fc604c8017e3246420ff18d4101dfac719003fd31d00037f3028200ff50540007f8c8980cbfc4150801fea126430bf99042017ec828801b7c654404ffe32a6400bfd8530007fe84900effe4050c71fe1068401bf1834101ffaa6980cffe53508037fb024002fb88521005fac621007fe20d0003ff9024003fbcc932007f6819000ffc308c8057fb0a4200df59740067f88790003fe424c007fe18e861effd41310cffaca9080bfc21504017f3226400dfd9153007fc8488003ff6050c01feb00843fff147431eff8a4a180bfd5148401fa90a2031ff1414200ff84190003fd60508017eb064201bf1813110ffacaa080fff304c40ffe20a4015ff95343087f8c2a00037d53484097e32e4004bf997431bffcc721003fd644c401be312a602ffd0541015fcc9a0803fd3248025bfa9a8008ff94d20007fe42900c7fc105083dffaa2622cff8c4420bffc8090892ff65d0443fea82822fff99642007dc64908dfff3290801feb22402cff884420cff8a49082bff608c807fea9a6240ff597431e7fe20a1803ff6344007fe21a641bff10f
  | 4 => 0x6fe604c46bff204840aff14a4204ff8a8900f3fe2150c13be32a4002ffc8510005f8c4880127c654805bff9808403ffd0d3103ff8c290003ff42c806dff30c8400ffd8d21007fe429809efd654c83ffe1828202ff0c74101ffca698006fc6050805f610e4210ff0c54003ffca2900d7fe609080bff29a200aff94842005f8c890006fc6050c03ff1824016ff5474001ffa649800bfc41440057e30e8638ff14342177fea82100bfe214847dff1068601ff54120015f8c321007fe50d00097e32a2004bf99541006faa7a0003fd3244055feb2c6400ff19120087f8a2a00bbfd5310819ff29e4001bf98342017f8a3a080bfe3148403fe2826000ff50940197f842a1003fd604c803ff206802aff9523201ffa8719003fc644c8077e31a8201bf9814318ffc20a1057ff63d0863ff1828400f78c932017ee209080fdf328c837ff9964201ff14110015f8c290003fd424c407ff9926403ef90d4300ff82098007fc104405ffe2a48401bf182320b7f8a5a000fff53d0c01ff3168603ff0c143007fa85a0857ff60d0c0ffe10a4029ff90632057f8cb90067fc6548407be192a615ff1074201fd865190dbff1090807bf982a603ffd0d3001ffe65a180ffc5350c01ff322641bff94f2105ff88390003fd32c8075ff29e8400df59153006faca2100bfc314c475ff21e8425ff18132007de84a1003ff424c801ff1924202bf98b21007fec49882bff21c8025ff32a8001ff841201effaa4a1807dc304c001ffa1a2000ff58d21057fec621006ff634c06dff28c842aff55232137f8829900ffe434c02bffb1e8200fed014000dfac1a000efc63c8043ff32a8200ff1094100ffa8090003ff4148069ffa8a8402ff14531024fccba0007fc50c8045fe1068224ff59741015fec2a080bfc41c840bff21a2031ff88142007fa65908e3fc10d0801bfb2a8201ffc4340015fcc2a1857fc43d0423fe21a802edfd4c4200ff840a000efc63c842bfe2a68001bfd8510017faa2a0857ff43d0803fe0864002ff945410cffeca90857ff65d0c3dfeb2a6200ff59321007fa859086ff731c84017fb12203ff78c743007fcc5a0863fc5348481ff32e8619ff549211aff8212100efe63504057f3088403ff8c632007fac190803f54144035fe2864225ff141320affec5a180bf641d0403df2028000bf58e4217ffaa12104ffe51d0001ffa1e4002bf18442017e8429082bfc219082bfe2008400ff58f41017f8639080bfc10c8413ffa8a4003fdcc531005fec09080ffc314c001feb222025ff041320eff84098887fc5450401bea9a8215ff10f42007f8c498803fe42d042bfe20e8615ffd8742067fc879005ffc6048421ff30a800aff19721007fcc89880bfc3144007ff29e8600ff4c5200f7fca49887ffe405042bffb1e8034ffd9542007f6409003bfc514c02bf
  | 5 => 0x4342157fea11908fff32d0405ef18a6215ff187400affe85a0803fd6250073fe10e8403ffd4d31057f843900fbfe50d0c01ff312820aff94a320e5facb90807fe204c003fea864030ff597420a7f8a7a003fff514c011fe31a4038ff8c34201ffe611905bfd52d0015fe31e4002ef10541007fec48800efc634802bfe2a68615ff10c42157fea9190d7fc3090807ff98a8600ffd07201effca8a1803ff4250005ffa8a2017ff10121007f0c0a1057fc60d0433ffa924202ff10741017f8439080ffd314c003fea064003ffcc931017e86390803fc4248055ffa946401ff8c3200077c84a1012fe6550c013fb2a8203ff54e32005f8c88800bfd3144069fea8a8438ff84342057f84021003fd62d0021fe20a8004bf9952100ff861a0057fc62d0005ff18a8200bf587400aff8c3a18fffe51d0c1bffa8e4027ff5413218ffc80a1007fe10c80017eb046400bf5913211ffca7a0873fd50c8401fe9928000ffd0d4000ffc4088003fd32d0423ff29a8003ff8c132007fe42a000bff314841ffe32a6000ffd8540017fe839086bfe30c842bffa1e8203df10d5300df0c0a100fff534c005fb8828215ffd9741007fac1a1867fe5448403fe0828003bf98d10007fcc8980c3ff51d0879ff20a8627ffd4532057f8c790827fd5148045fe2868219bf5952100ff8a0a00afbe4010801dea168004bf9953218ff840a1097fe104c87ffe10e8602ff8432101ffe8699003bf43504017f3122000ff8c9411a7f8a4a1007fa40d0001ffa126200df54d20007fa6390006fc60d0807ff29a642effd4842037fea6880c3ff53d0805ffa8e4202ff043410eff8a098807fe4048071ff1068400f7d0d43037feca8802bfe421087bfeaa28606ff99510007fa86909077c2054c3bfe3026201bfd914000ffa608800bfc414c401fe3128201ff88320207faa1a1827ff6548005ff20a422aff9963200dfcc12100f7f538c8437eb2a8224ff99741007fac4980cbfc6150807fe9926203ff94d31006fac2a9883fc5350403fc0822021ff5494104ff8a4900c7fe50508057e30c640aff19232005fec0a180ffe30d0c05fe98e4200bfd8532057f8642100fff324c039ffa9e4225ff8813204dfeca9008ffe43d0401ffb0a6011ff90d40197fe20a10fbfe10d0c2bfe2168034ff15142007fe8590833ff32c80077f31a800eff1053018ff8c0a1006ff604400bff9922002bf986420d7fc4190803ed421085ffea8c8415ffd8b4106ffea7900d3fd5050851fe2046402ff04131005fec790903ff51d0c43be32a8203ff90d31007fe8498003fd6150007fe21a6200ff99320007ee82a0812fe65d0801bea9c8419ff5512100ffe2090007fe5048001feb0e8001ff4c320005fcc9908127c655085dffa808435ff9424200ffe408802bfc65108037f3068203ffd4d32007fe8488
  | 6 => 0x5ff28a6200df54f20127faa1a084ffe41d0001dfa148406ff14910015f8c29809ffd514c81f7fb2a6025ff90132007fa43a000bfd51c8401ffa0a802bff1404201df8c68800fbc43d0c017fb26400aff0823200f7880a000ffc3250c03ff282603dffd414301df8c7a000efc6350001bea9e8415ffd8b40015fcc29900bee21c84017eb1a4204bf195210b5fecba000bff51d0415ffb0e4003ffcc14301ff88719007fe105001ffe2a26001ff90320017fc21a0812fe65c8001feb028621ffd494113ffcca990cffc5350879fe30a863dff94943057fec3210d3fd5250803ff8826003bf18d420fff880a080ffd5350c0dfe2a22001ff941100b7faa9a0007fa304402bffa188400ff1891000ff4209801bfc6544001dfa168012bfd9540005f8c4a080bfc214c4017fb222001ffc411000dfcc1190c3fc52d0801bea9e4202ffcc5411b7fc632100f7d534c815fe2964012ffd4540137fe209902bff60c8431fe1924219ffd41211b7fc432100bfe104c42dfeb2e800aff14b210d7fc819087bfd504c45bff2188402ffd05310affec3a003bfe514c031ff9824201ff88140007dc6590867ff5448413fea924000ff4c540047f8a69004ffe31d0059fe1888403bf18f41117fc41a0866ff6548403fa0822030ff997421cffca3a100fdf304c8017e3264227ff149320cffca49080bfe5144007ff1826200bf58f20057fec919057fc60d0803ff2864000bfd913001dfcc6210e3fe50d082bfe2a68419ff54d21005fac1a082bfe428c815ffb1e4202fd0c531007fec890903fd51d0c07ee1926439ffc434201df8c62100efc63d0801dea1e8221ff95141006fcc4a9837fc54c8003ff886400aff10a3201efaa7a186bfe50c8405ff8864200bf58b400affecba0003ff6250c037e30242049f9972109ffc43a0003fd4350401ff324643eff90343005f8c9900ffff10d0c03fe1824002ef907410aff8c3a103bfc214c081fe2968602ffd4531017fa8290893ff53d0471ff3068402ff9054101efea6a184bff5350001ff3264225ff94132005f8c89080bfc2144039fe2a64203df90d53005f8c4a0002ff63c804ffeb2a6400ffd0530057feca21007fd504c0097e32a800affd824205ffca39002bfc6190805ff28e4227ff1513200ffa8098003fd4210859fe2888415ff18f40017fe8288003ff6448003fea822004bf195431bff8a721003fd61480017eb12201dff88131005fac688003fd618c803ff1826000bfd893007dfaca98007fd4044001ff1968000ffd8d410fff8c0a0803ff6150833bfa9a4200ff59232005fec890007fe1044015fe1946403ffcc632024f8caa0807fe104c077fe2028627bfd9532017fc42a0807fe304404dff28a6401fe88320007f260880f7ff5250c05fa18a2021ff55141005fec2a100f7c3154c23ff9928030ff5
  | 7 => 0x104844805008018004000040000d4000000280080e0040060a5850005a037c040000201d402803ff624c003ff202800fff59530005fac990003ff6050401fea1a8432ff8c54210ffecaa0807fc40d00617eb2e843affccb42015fac3908cbfe4150851fe284643fff98743007fec0a1057fc63d0801feb1a2003bf98f2115ffc40210bbfd6510815ffb2c6400ff58910127f8a5a08e3fe40d0801ff3126002ff14521175fcc521063fe6348437fe29e4212ff14940035faca88047fe6350001feb0c842abf5963204ffca89000ffc534c84ffea92641cff54b21006fec4a9803fd41d002fff302422bff9804201fbc87a18b7fe6310803fe186400aff19320057f8c990803fd6090871fe1868400ff50d20007fa8490812fe65d005fffa948403ff10d43017faa298802fd62d0477fe102862effd4c420b6fea7a000fff438c807bea9a6200bf58442117fcc1a080efe63d002bfe2a68239ff0c74201f7c87a1803fd60d0807fe1826400bfd8142007f88498002fd60d080fff20a4034ff55142117fca1a0803dc6350405ff8868200ff58d4110ffea0a082bfc60908057fb228201ff941400effc809880ffe438c85fffa9c8420ff0c941015fcc3901077e2054c6bff1848420ffcc14100ffe20a002bff63c80097f3288403ff14f43097f8a8a0003fd63508037e3028200df54d42207faa5a1803fc4244065ff28a841aff0c3210b7fea5a0087ff5450431fe21a4231ff98142007fa4290003fc6444007fe18c641eff1493118ff860a10127e65108037e3008412bf5954010ffca4a089bfc214c807ee18e8600ff989311effacaa1827fd5448043fea9a8200ff109320bff840908b7ff321085fff2a48400ffd8532017f620880737e65c8421ff28a8022ff8c341006fec0a98d37c655086dff20c8403fbcca32017fca3a0802ff63504017fb026203ff0c343007fa8721077fe604c41ffea8a6001ff8c140005fec69080efe63d08017e3226214ffcc740007fac621017fe6344015fe2164203bfd8d32007da649080afc61d0015fe2164032ff88542017faa288002fd63d082bffa108403df54d30007f8c4a1857fc41108017bb0a6416bf5974000dfcc0a1077fe504c439feb2e4200df54d1013ffeca99002fe64440017eb008401ff90130007fcc890003fe3248001ff3122002ffc4131005fac79080afc614c801feb0a8629ff146320f7f8a898802ff64c841bfea8e4000ff50f400b7fccba0002fe6448003ff2022002ff0874115ff820210c3fd51d087bffaa28607ff8c5200affca9a000aff634c45ffea948418ff18d21087f842a00b7fe5310801ff2124214ff98f400f5feca9880aff6248401feb226407ff8852007ff8a498003fd428c801bf322a633ff18d42015fcc3a18877f53504017eb0e402fff55242025f8cba0807fd505000
  | 8 => 0xd000c7c00007e02c0700403e8a4b680101802403800022000058000460542084d2e800dd90071b404db180b0080015780e09a0201080301e115180080001700000533607c00000000114050200240280080904006c0600307a090000000220180980402e0040400400203c188000000000980e004000008070101880000000002c0003100003c070210001001400018a0840080200000c1500001421825801064070000000aa0001100900201c0051000a0242f8000120543102a0000040480f43a00c8e80000602c048140081b4050171b0000020010540000080001c0040480000213c0100461c0580c00b01803403008014068000290da0400380905e000008070d2044000020060000481200006400000012370228000000000001000e0a0090101f403c0181306c0000800008a008000030000180000900a004308000440dc0480000c0bc0004802002800013964024008140c661c07002000024000220360400003d0121580580101eae00080507824c0400500001000001038048020000ae04c0000e01204400011008020028060000215001100200419019022038020001e40380600a01c0181280402a00008000006a043080101c0000200003c0180002d06e0003e8060080184584003a0000003a002014008050ce05c0180f0b60100e8540860240283d0de004030010380046100401c0300700201402809896046044020070040140000503a00c100030040444d8030020000080000c008010320549183b8160960400c8000440380483003e3e80180e010000020050780000180f0840000000f00a3001100007c0200001d046118018290600000500e06401c0080a06601c008110020281200001e0002682100009802848264050008010080b0060010000101680403000c020110240180280301c0180e0000060280180001802c9480d0020d860b2501608b2c80b0fe184e68010221a400009086038000180440040180000605c0780a006000018140c0110028460000996881b0240006e800002338a700200001c020011860580d005000034008002300040280002435c070ff1300f45200064a00c018032d05d4120000000500105903a0040080003c000040110049700000000208c0b0010ce0000100c0000c4000130120840183d0000500001d0480200e80f0660cc0081901e0d00f8070060c4038000060000005800201805800094024008
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd75d9132004ff7259130397d44118d410067c75d8d42006bf64d09310aebc64d092038e7f1059721135f676d85321067f53591310067d53d8520056bc64593200aebd76d0b400c76f534c9211267c65d05201ff9e41d8d41394fe76d0d410067c6558d20004fd7558e4211e7d6354f410247e76d9541006f46158132056f42158442004fd701912115ebd20191200aebf7019120054fc7318910004fd75d854020e7e6054d211bcfe7610932006f862d01401c7e820d09201ee7c6550d1031e7f53d91300ae7d75991200067f7559131056ec6290940005fb7050b213ce7c31d95410567c60594420067e43597400067d65587402df7b53d0320056dc3258f2102e7f5358d10024fe7519321004fd72d8530024fe75d91301fedc3158743006bd6419110056dc6358f210c67d535863219ded72991320063f65d91202157c71191530acfc76d093001cfc73582421073d5350d41006f952d8142006bf6499121056ec4298b410047f7558d200aebf43191310357c755091038e7e7159721014fe7199120006be431911001ebe63d0d4101e7e6354c4201edc6350d4020f7a30d8153004ff7458d200067c73594420067f75d8d20004fd74d85321a67c72d954200cfc7650540054ff75193200467d6354d201c4fe761094002dd473505101e5f4715894300cfe76d8121024fc75d89100067f65909410067d53586420257d731895302e7f6354d10006bc41d912015eb82019120006f971d8142395be76d0d4100feb62c812012ef840d8132006f731d8520014fc71d8f2000cfe70593212a67e21d9510004ff7458f21046df32582321ffd431d0d10015ec764c921316bd40d91300067c6059153004fd73d9110024fc75d85432157c719895320f6c2054f2020e7f6054d4019cfd7699232014fc72d8520006f660d85320975f7354d402167f6154d4100df4764851000dbc7650940006ed6218931024fe7598b41004fd7018931004fd76d0930006f731989100067c7654e42054fc72191200067e71d95200067575d85320acfc7458d101ee7c6550d41006bc71d91201ed7e75189430057f7654f40007d63218532006df63d81414176c65d09420067f5398b410067c6598910006f442d853211e7d5399131006ef625094111e7d53d85430057f75585202167e6154d20054fc7598b410567f20594420567c2159721004fd73d89400067f6598941217747154d100fff070505101afae20d91200573d6550842007cd32485300057c745895300cff7118910014fc7458f410acfc764cb40144fd70d8d20006f873d81420aebe7419110004fe76d0910004fd71d81420acfe7499132007cc624c9300def530d85320067675d85321fddf7359131054ff75189400acfc759912100cfc7258f200acfe7499110024fe75d91320077765d0541004fd70d8532
  | 1 => 0x8d202176e2154d21004fd7398b411c6bd40993200c5f57198931054ff7019120004ff7358910004ff7558e42024fc75d911001edc634c921164fd7119121006be5219120015f4714cb4115ebc40189400057f7550740004ff75d8121014fc711893029e7d40d9510054ff75d9232054fc76d0f20054ff70d8d201dcfd769913020d7c70589530067e73d9510005fb7050920006ec624c94000cfc70193210b57e7558f400073f755094000cfc70d8543015bc71d0f41004fd7518910004fc76509102ce7f30d9520005fb7058941004fd70d92320a67f5358f40004fd76d05200aebf72191200247e75189430c6df32d8d2120e7f6454d40006dd65d8d411ee7c6550d2000cfe70591320067c6199153056dd73d93210247e76d95100fdf8705094101cff7658d1015ebf50191200aeef4298b4100cfc7058f21056ee7219232006bf64109100047d73d9541054fe7650f21024fc75d81210acfc76d0d21056f82058242304fe76d0d40014fe71d9232014fe76d092138e7d725972100cfd73d8930076f43158d10054fe729913008e7d53583430567f215972134e7f10597400067f53d81422167c6154f40004ff7058442024fc7558f4100dfa76c81201c4ff7259120056ef2198b410067c65d85201aebf20d9120014fe7158f2011df7715913101cfc739911034f7820597401a67e74d954201e7e6354d21374ff764cb21006f675d85320067d5398910004ff7558d210067e10d95421fede41d8d41004fd765072013e7c654c920004fd74d81320063c6454d2001e9c63d0d41006df7359131014f47159132006bc43d91100067d7654f41004ff73591100bef840d8121006f963d8142217762154d100567c42597210067c21597400567c605972100cff76583410057d75109410def773d8532054fc75d8f2101ddc7350932004ff745891015ebd5019120006f420d8532004ff755834300cfe70991320acff76d0720006be73191200acff72593200067d71597400aeec6258b41006be65d912040f3c6590942014fc71d923200cf4765051004d7e751092000cfc7458b4003ef621583211dddd7399130054fe72d93210067d70597210acfe7498910024fe75d894335eed32d893114cff7358d21004fd7299131024fe7558f2000cfd71d91100067c43597210af3e65d0b401def860581431bede5358e42024fe75d8d200067e72d9510024fe7598b430067f7559120007cf624c930024fe75d89300567d75189430057d7219153004fd75d8d42005fb7050842366ed211893116cfe7690932006be63d91200def743d8532006df7358d210067c72d9510006bc63191200bdf8705912119edc31d8d42006bd71d912000cfe7058c420acfc75991100067c74d95100067f7059442024fc7558e420067c7559232024fe75d8f20166f71058442004f
  | 2 => 0xfefa10d814120d7c7099153024fe75d89400aebc5419120054fe7219232006fa52d814215dbe7050842006f575d8532056bc42592322167c6154d40014fc7118943016f764d05413979c4118d411b6f641586422177b1054d1000cfc7098b410aebf4119121006bd5319120004fe764c5200067f65d0d420067f649915313e7e654cb21004ff7058c420247e76d95201075e7518d41194fd769932115ebe10191200ae7d75991300067d65c874000cfe7019121005dd73109300247e75189400067e6558442014fc7159232006f771591310057d75c8520014fe7158d200247c75d8d41056f97019320006f751d8532006bf6450520004ff7158d200067f539912113d7e75d85320067e43594420957c7550940005df7358121006df7358910004fd7559132007777154f41056bf6499320195ed72991210057d75d85321be7f53d92320057f7558131024fe759913201edc638c94119edc6350941005df73509320acfe74d81210257f73189530067d53d8910014fd70d91100247e75991200067e31597400f67e654c7400aebc6410910006fb50d8142056df32d8f2005df47158f200067e315944200cfe7299320024fc7558b4020d7c70d85530ae7c43597400acfc7458720056f721584421aebb64181420957c7558940006bf65d9120004fd75991300aeef6298b400067d7159442004fd71d8d200067953d8142004fd71d89301aebe40582420057f705855320d7e70991530067f5358042004fe76d0d2101e7e6354d420067d65d0b21006fb64d0320017b764d0541004ff764c7400b57e75c8740006be76191200aebf43191300067e7654f420057d71d9153056f4615872033f3c7550b401c7b820d0b40004fe76509100aedf4358f4002f7b534c1100067c65d85420aedc4358f42004fd70d8f21196bd41593210067f53993200073f6550d410067f658c920004ff7058d2101cfe73d89410aebc431911001cfc73d8941136f451d85320067d7558f2129e7c10d9510086f641583410047f7654f40005f7725051034f3e40597400aedd7399131005f7714c9100063f53d9120006be751912001cfe76d8d410067f654c9413ce7f71d95411fedc31991310067f7558d10004ff7650d1000cfc709923201cfe735804200cfc70991320acfe74d8910004fe7650931056ef2018930004fe76d05200057d73d9510004fd72d9131007f37050510054fc7319320006bc40d912101cfe731912011f3f53d0f41006bf5219120004ff765072000cfc70d9132004ff7558d20005bc7458930004fd75d89401a57c75585420067c65d8910024fe75583430067f75592320567e75189300063c6519120004fd75d8d210c75c6354d21006dc735912100df8704c92001e7c6354f210057f7550930004ff755864201cfe73193200ae7c635974001cfe76d
  | 3 => 0xf5399321006be31d91200fdf87058941004ff7359320054fc7598b430067d6559321006f953d8142006be43d9120005ef72585300aeec6258b4300db87050b40004fd761093100cfc70191310067e7159442004bc7458910006f854d81420067c65d81410067c75589100073d53d0b401ccfd719912103ef461585200067e70d95420067d64d89530057d75d91300067f32d952018efa10d8142054ff75d8f20055bf725084229e7c30d9510106df30d8d41004fd764c910024fc75580420573e65d084215df870508420d5f87050b210247e7558f40004fd70d8d21056ec62109102075f63991530fef820d8141054fe72d854001cfe7398b41004fd7099232015f47150d1026ef431d81310076f65d0942014fc7158f40004fd7118943024fe759912000cfc70d8520014fe71d89300247c7558742076f631d85300057c74585531cef71058742006bf53d912000cfc70591320067e75d913001d7c73d855329f7610d9510004fd73189400067e6258953007db704c93016e7d53192320047c7654d1029e7e30d9510024fc7558343004fd7558b4101cfd71d8131005be74c85401aebc40d9320006bd64191322e67f53d8131006fb52d8142005f771509210247c75d8d4201cfe73991211b4ff7650b410076f755084201e7c6354f202df7a75d03200067e7654d40006be41992320067f10594422ce7c40d9520006bc65191200067c32d95410067e72d954101d7c73189530b67f76597400aefb4058342014f676d85321aebf72d9120056f860583210067f531891020e7e6054f42014fc7650941105f5719913100cfe7258f200067e61d95420067c7654f42004dd73d93210067c20d954200cfe701932100cfe705874315ebd30191200067f53193212057c7558743054fe72d8d100067c64581530067e70d954100cfe7099131004ff7558b401ee7e6550f21006be43593210aedf4358c420def653d8532054ff75d9320087b44150540006dc40d8d41004fd70189410047d7599110006bd73d9120006bf64909300073f7454d400067f7654d42014fe7158e420057d71d8953006bd54d91301acfe7619120234fe76c85200567c2159442056bc625094017f5f7354e422c6ef20d89300acfc75992324355f7358153006ef7259120006bc5119120077f0314c110004fd76109300067f6558542014fe7158c420cd7c755912100cfc76d0920006df7359121004ff735834201cfc7358720024fe751912020f741054d10004ff75d9130166f63158442006be71d91201e6f641d85430065f75d8d410067e40d9541004ff7458321006f864c8120024fe7518943136df3158f210dfd73158f210067d7654d41136f621d8532004bf76508420fefa60d8141004fd7399121006f852d8142004fd72d8d100067f655092020e7c6054d410ae7c4259740
  | 4 => 0x81310dfe772d85321f6fa3058343024fe75191210c67f5358d21004fd7559232024fe75593200073f65909422157c7118953004fd768c940006ec62d091000dbc70509400047f75593200067d6454d201fdbf7350d41006bf64509210bef71058720006df63509410067e705972138e7e105972101cfe76d0932054fc75189431275f7354f4109dfb70591101aebc4098b40056f970d932001cfc73d91201767d7259442136f410d85320067c6454d21054fc7518940196f71059121005fb705093000cff71d911000df87090b40005f77158d200067f659091015ebc2019120014fc7158343004fd7599110006fb70591320067c60d95410afad62d0b400aded74908420adbc70d08420def453d85320077b53d8142316bf40d91301adbf7650b40007e46248510004fd71d8d400057f71589530acfc7599131005bf745852000cfe764c920056dc6358c42005f9709094000cfc70189430567f21594420067c41d9520004ff71592321c6fb62181420bef8605812100df87050540006f9631814200cfc705863219ede63d8d421fedd74d8d41006bc21d91200247e7558f21076f421d85300af7975d01400acfc75993210057f7654c42056ef618c92125ef710d8530005bf7458d200067c63d9510015fa714c11001ddf724c93039e7f53191310247f7659721007bb74d8142006df75d8d4101cff7658f200047d75d853200cfe7058e421ff9f74d8d41004ff72583430df773154f2101e7e6354d403ce7f41d954104d7c75d8d20065dc7350720005f7714c9400af6e6550842006bc53191200567c4259442005ec72581410057e7654d410067f6550d411be7d6354e4208ede63d8d4016e7f531894320d7e7058553006f851d814219d7f7354d420057d7598941054fc725874001cde73d93212cf6e20d9520054fc73189410067c715944220f7a2054f20054fe72d853002edc32d8d101ffd441d8d413ce7c74d9541055de728c9321ed7e75d8143056bf6450b200057f7550910006df638c94129e7e20d95101cdef7259121004fd76d09310247e75d8532004ff7159120056f461586420aebc64d0d20006be40191210ae7c625974023ef4311891000cfe70d8f210067c7159740007bb70509400e67f7259721054ff7598b40024fe751894007d7c75585300ae7c43594421dcff705913009df4714cb40014fe71189430067f6548520024fc75d8d41006df6350d40016f4614852006d7c7559320006f765d85324073e4054c420067f6558520014fc71582420067d53582420067d7654d210ae7f42597400cd7c755812120e7c6054f41004fe764c54000cfc7098b430047d759913043e7f63d81530a67d53991300067d53d8540006fb7058910056ef211891007d7e751093034e7d205974018dbd74909400acfe74d8520136dd3158f210067
  | 5 => 0x276df31d8d10006f965d81420f67c654c520005f7715094100cfc70593212157e71589531757e7558c420067d7654f400dfd432d85320067d65584422167c6154e42004fd75d85320567f6059442014fe71192320067c6558d100aeee6450842006fa61d814201ebc63d0f410afb571d0f41004ff7058b41006f950d8142024fe75d8532007cd32c85300067e73594420057d7510920024fe75583420067f7159442054fe7299131004fd75d9121006bf641092015efa105804219cfd7299132106df32d8d410acfc76487400057c7258553014fe7650921045dc73585202e5fb7058530004ff73582422ce7f20d95200047f75591210067c64189532157e711915318efa72d8142004fd73993200def77158f2136d7f7354d210067e6558f40017e672c8521004fd74d893115ebd101912020e786054d420057f73597400576d658cb212ce7f72d95200067d53d8141004fd7598b430b75f7354f401fcff7359131056bf64992320afb970d0b40006f853d8142054fc72587433f76f5390842006bc43d9120006ef628c940006ec725911031ebd43d913048e7f6358953007b76450510374ff7258d21004fd7198b40004fd70d8931006ec625094120f782054d201bedc3158e42006f961d81423ce7f31d95410067c655912000cfc70189100057f7558232004fd76c85400057f75581420afbb42d01401a57c7558d421a67d72d954201cfe7358342056ed768cb210aebc64d09320067e21d9542004ff76509310067e63d95200067f5358321054fc75d932100cfc70192320057d75c85300bcfd71989103aebf43d91310eefa10d8131004fd71991300aebe7419120005f970109301aebf10d9120004ff75d8520004ff75d89101aebe6490b40006f551d8532004fd75d8542194fd76509210067c72597400247e75d81430dfe432d853200cfd7318930004ff7158342024fe7558632006f871d8142056dc634cb20056bc4259321054ff71d8d21056be42993200067d73d9510006fb43d81421aebd72d9120014fe71d8d42006ed6218943056bc64d0b20004fd7558d10004fd7319320024fe7558f40236ed20189104bd7d7699153005df73581412a67c31d9510054fc7598b40054fc769093038e7c71597210067c75593201d67f53d8943006dc63d8941056ec21189300057f7558910007e632485100567d75189400acfe74d8f21004ff7158c42006bc54d91310fdf57199110054fe7650f2019cfd7650932007eb7050842397d71018d41024fe75d8543004fd75593210acfe74d8f20014fe715834215cfe76d0940024fc755874225cff7158d10004fd764c720006be51d912000cfc7099121006de75d8d41006bc40d9132006bc4359321006f47158d20054fc76c854000cfc701913200df87050920106de63d8d41056f42158720014fd73d
  | 6 => 0xf3058f200067c65d8d4202edc6358d10004fd72d8d41005fb705054034e7d30597400ae7e745944200cfe70d8931004fd73191210aebc5419132306bd4019130137e4714c921054fe72d93200de7f53d85320057d7518940006f764d85320067f65d81413ce7d31d9541006bf64d0920056be625084200cfc70d8941054fc768c9100067f53d89410067c10d9542004fe76c8540006dc63581410057f7558141166ed2118941006f761c853001cfe73989100067f654c9100357c7558d10217743154d1031e7d53d91302167f6454d41024fe75d8143014f47158d200567c2059721024fe75d8141004ff7458d101acbf7650b400df6f534cb210aebf4099320387e7321853201cfe7398b40217747154f41007b864c8120005fb7050910006be531912018df87058d420067f65989100057d7018953004fd76c853000cfe70d8d21004fd75582321067d53591310067f65191201fedc41d8d41015be71d0f41004fd74d8f212176e2154f2100cbc76509400047d75d8f210047d75193210073f6499153086f641d85400567f6359721054fe72d91310acff75992322157c7199153056be6250b40006ef72591320057d749895320d7e70d85530af9e63d0f412a67f41d95100067e70594420057f75509400047d73d9520006ed6218940006f460185320acff759911001e7c6354f420357e7598910014fc7158f4202e7d6354d10006be21191200067f65d8d1000cfc7058c42004ff75d8930015f67190910004fd74d8530006fb72d81420073f7550b40054ff76909100def430d853230e7f53191301e6df3158f4149d7e7499153006bc52d91203577753c85210357e759911000fea62d03200067d7459721004fd76d0530056f721587201e6f661d85430aebc7119120004ff7559320007b46450510004fe764c94004d7c7558d2018cfd72991200247c7558b43024fe75d8d210c76d534c9210067f7654f41006bf6450932146df30d8d2000cfc70d89310067d65d0f2120e7c60d815302ef73158d10014fe7119130056dd7318930004fe76d0d100acff7650920056be4299321056de3258f202173e4154d41006ec21d893020f6e2054f200077953d0320005f771591321ffb710d0d4101cfc74d8d40006f674d853201cfe7358b41056be7419232004fd76d09101fedd21d8d411ff9c41d8d410357e7510910006bf511912029e7f40d9510005ef7258d10006ef6250940056bf649932141f6f53d0a4210d7c755894120d7c70d89530067e7259740024fc75d8530024fc7559130006df73591101c4ff7650b200067f7459721056fb2058232004ff7558720006bd52d9120015ee714cb210067f65d85420067d5398b4120f6c2054d20006bf64c8520024fe7558f21007eb42d81420073f7454e421acfe76109201fedf74d8d41015f67110931
  | 7 => 0xd40016f762c85211ee7c6550d4245f7531d85531aebd50d91200afb44150740005df7350720004ff75d8132004fd75193210067f5358b410063f6454d2000cfc7648520005f970109102167c6154c421b6bd41d9121024fe7558740054ff75189100257f73d895301cfe73d8142004f771591320acfe74d89310067e60591530067f7654d200acff7519110017b674d054115ebd40191200acfc745823211f3d53d0f410067c32d9510314ff7650f402167e615855310d7c75581411a67e6550b402beed201893001cfc73191210077b53181420067f7259740024fc7558b43007d632d85320aebf4199321006be54d91303cf3e41d95411b6f710d912115ebe405804200efb64d0140054fe76d0f20006fa53d8142276dd31d8d1000fdb734c11038e7d1059721004fd75d8d41136f673d85320adbe74c8740004ff7158b401d67f5358f42004ff764c720054fc75989100acfc751912102ff3314c1100067d53d81420057e72d9153004fd71992323ce7f74d9541004fd768c94112fda104c93000cfd71d8d10056f86058242004fd7558642004fd75d8943014fc765092118fb870509400257d73d9153006bc63d91203e7ad5250842004fe76c85300057c7654d410aefb40583431c4fd7099120024fe7558f41004fd74d8d210ae7f43597400aedf4358f4221f78654c110135f671991320047f73597400aebf43191320aef441587430def630d85320073f7454f400067c7654f201ceef21d89410c6dc43d8d21366f431189310067c7654d40004ff745863212cfd73d8f204757d739895301eee634cb210057d75d8143004ff764c520135f471581320067e61d895329e7e40d9510005f77158930014fc71191200067d7654d20024fe75d8542004ff75d8941024fc75d913100df470485102557f7354f200067f6550d10014fe71191322a77621d95102167e61d8553006f642d8532004ff73583411aebc6090942006df63d8941004ff755844244d7f7358553004fd7558c42014fe7118910014fe7198b43004fd7650f21005bf7458930006bc64d8d20014f671991320057d71191534767f63989530067f75d8d421767f72594421adbe761912002ddc735911001cfe739932113d7c7550932005777159153006fb51d8142056ef2118931004ff75591210b57c7550b40006f554d85320047d7654c420e67f7659721006f77158f200067f5358910006fb42d81421257c7550b41005f771589430067f6550520004fd71d8143007ba42d81420047e7654d20014fc7158f20004ff75d91200d6fa10583212fe7f53d8930056f82058042004fd7399321056ee3298b4300cfe70d89430067e6454d2103ef4315832101eec634c921024fe7559130005bc74585302f67f53189303e73f535084229e7e70d9510006f620d853200cfc7058f4212ed
  | 8 => 0xcf47648510054fc72992321fdde7618d411ff9c31d0f41004fd75591300067d6558b40054ff70d91202c5ef7258d200067f539911034e7d10597402ce7f10d95200067c6454f21014fc71d932007d7c75589300ddf67618532006bc6490930054ff7598b410067c21d9520004fe76505200067e20d95420067f62d8153056f820583212157f7658553006f770d853219fcc3250932005f7714cb41004fd73d9121006df7358d10004fd7558f200aebf41191310067c755911001cfc73991210aebc4199232014fd70d89102a77b10d9510004fd7559121006f96118142004ff75d8943006bd5119120006bc6119120006bd5419130005f7714cb400067c651891000dfa76d01400067d73d954216edc6310941014fc7158c420067c61191530047d7518930006be76d09403aebe76d0d41005ef72581410ae7f625974000cfc7058b43004fd73d89101a67c6550941024fc75d8141014fe7119320004fe7610910364fe768c9210acfc7458d21006bf52d91200047d75d8143006f73118910015be7150f41004fe76d09300067d74d95200567e7518943006fb61d8142004fc765053001ebd76d0f410067e31d95200acfc75991200067f65d8910196ef2158b410073c7454c42006bf64991300067f5359320005f571109100acfe768cb4136d7f7354d41006f761485200063d6419153054fc75d932038e7e2159721057ce728c9320057c72591531f6f860d0d420047f735944234e7e10597400067c609895341fad54d0a42006f665185320067c30d95420065f53d8d410073c7458553004fc764c91002fd8634c110006be52d91201ffd710d8d412157c7159153004ff7650d210afae6450842056bf7459320006f875d8142004fd7119232054fc725913001edc6350d421b4fe7619121024fe75d8121054ff75189304b73d43d91531a67e76d954200cfc7258720046df32d8d20004ff7058f4115ebc10191200067e1059442054fc7650f211567c658c94100df870509300c7cc634c921056dc3258e42004ff70587430057e74189530067f6558d411fedc61d0d43056de3258f210067e30d95420057d75989100567e75193210567e72594421e5dd73991312e6f731d8131007e870508420067d5358042004fd768cb4001cfe73991200067f53191201bcfe76d0d4220d7e70d8953194ff71591210067f7654c42007e972d0320004fd721913100df870d0b200067f7654d41056f6624851026dfb7058d1018ebd4059320056ee72d8f20006fa21d81422167c6154d4201dde7310931006fa73d81420067e73597400573d65d0842006f771589100067e43d952002f79534c1101aebf50d91200067e6454f20014fd70191100dedf3058f2119ebf4359232006bd6519120014fe71d8f20144ff7358d20014fc71193200067f755911000df8705
  | 9 => 0xe7158042004fd7319110006bc65d91200567c20594420067e7654d41054ff768c9100047d73d954201cfe731912100dbc7050b4001edc638c910005df7358520006ef7259110057ae525084200df8705091001cfc74583430af7a405974001cfe73d9321024fe75591201d6dc63d094101ef8764c1100047e7654d421aebd30d9120006f731583210057f7558d4119eee3258b43005ec725853000cfc70d93211567e658cb40024fc7558b4115ebc3019120006dd6350e42004fd76d0f21004fd719932003df970989100047f7558743024fe75584420067c43d9520006f951d81420067c31d95420c76f538c92100cfe76d8131006be401913101cfe73d8940004fd71991200067e21597402167e6154f4201eec634cb2101ebc63d0d410067f53587400a67d6354f4002df473505100067f535911015ef840189400ffb840505400def543d85320057d75989310067f7654f4218ebf60509401be7e6254c42006bf64991321be7d53d9232006bc51d912001cfc7358b40395de76d8d4101cfc745874301e7e6354f4201edf64d0d4315ebe301912039ebd43191310957e75109400247e75d8f21006fb74d81420af3c4059740024fc7558f400067f65909422a67f31d951001cfe73189400047d759912001cff7658f410ae7e74597400067f73d95421a67c65509100aebe7419121006dc63189410067e6454f210057d7510930006bd53d9120006bc54d9120024fe751891001cfe7359110014fe76d852016e7d53189430065c6518d41004fd72991101aebc40582420aeef4258b41005bf7458910004fd75589100057d70989530067f75587431bf5e6354e4201ebe6350d410075d7398953006f843d81420ae7f435944201cfc735874217e7c659094220e7e6454f4000cfc70584420acff7599120006f754d8532194fd76d0b21024fe75586421567c658c9100067e7654f211aebe10d9120006fa6118142014fd731913118ef810d8142005bc7458d1005776215972101eee634c921006ef6298930014fc7158b40005ed76d0a4215cfe76909200dfd730d85321ff9e31d0d410247e7519232007eb4218142014fc7159130005fb70509400047f7359721004ff7158e420acfe74189312e67d53d81310057e72d815301cfd71d91310acfc76d0931004fd71d8d420247c75591200aef86058341164fe76d0941054ff768cb400eef8605813101d7c73d81530067f74d9510004fd72991303ae7f53d91310067d5318910004ff75d81430063c65d9120054fe72d8543004ff75d8d20004fd75d8f2100dbe705094008ddc735854016e7d6354c420ce7e654874029f7410d95101c6ef20d894001cfe7498b4300cfe70d85200af6d65508420067e7558f40054fc7650f20007777159153054fc72592320aef84058342004fd70d9321014fe7258f21
  | 10 => 0x91018ff271181422167c6154f42004fd7599120004fd71d923221574715895329e7c70d95100057d72d915311f3f5350f41217744154d410057f7550932014fc7650d411d67d53d8943024fe7519232006bc53d9120056be4259320004fd7098b43006f96518142005f571d09100057f7550b41006f761581320073d6550b400067c75d8d20006bf54191310def432d85320dcf77158d2101e5c6354d41006bf7650842006ef7258d21004ff735912001cfe7358242054fc75193210aebe7419131004fd75583410067e7654f41054fc768c94119cfd76d0a32004ff75d89401f4ff7359130054ff75189310567c6359442004ff75d813100cfc7458740005bc74581320067c75587430af9d63d0f41006bf64d0d20006bc6490920056be7498b40024fe7558910054fc7610930077f2414c110004ff7650d20217742154d21005fb704c9200047d73d95100067c65589100c67d6354d211a67c6550920006bc7458d20006fa75d81420076d5390842006ef6298910006bd541912018efa30d8142004fd73d85420667f53d8132005f57190941006bc73d9120004fe761093000cfc70d8d10024fe7558d100067c6558d411e7b47150d413ce7e41d9541004fd751913120d7f70581530067f53d91100057d75191320567e75192320067d7359721054fe721913104e7e72d95200057b7058953014fc71d8940006bf54191201aef840d9320024fc75d9121006de72d8d41007db634c1100077953d814200cfe709932120e7c6054d4201cfe76d8d40024fe75d81420aebf40191300aef57199132007d9324c11002f773154d1000cfd73d85304a75f631915301cfc73d8520004fd75d9232024fc75d81310057f75591323867f5318931005f77150d412167e6154f20004fd7558f210afba70d0b40054fc76d0f21137e4314cb210065f6354d210057d71989530def772d85322157c71581530acfe74d853200cff7658042007ba421814238e7c1059721017f360485100067f65d8d42014ff7658740006df6358141004fd75189300ae7f42594420067f65c852039e7d531913102ddc735891015ebe20191200aebf751912029e7d71d9510006fb70591212157e7158153004fd74d8131045dc735052028ebd40d911018cfd76d0b203efae4090842005f570d054134e7c2059740024fe75993201567c658c9201aefa40582420057e7299153024fc755912000dfa74d0140046de63d8d20006fb7058b4000cfd73d9130004fd701913214ef763185320afae62d0b40014fe7159130106de43d8d410057c7654d420067f6510920006f640d8532005fb7050f2019e7d6454e42004fd721913001cfc7358642007bb7050b400057d75c854035eee32d89310057d70d9153004fd75d81430057f7654f210aefb40583411f6df30d8d4001e9c6350d41014f
  | 11 => 0xce7c654852001cfe73193210c6dc6358d21006ec32d8910006df638c9100067f6550d4201cff7658f21014fe71d8d100057e72d8553004ff7158b4313d7e7519132006f863d81420067f73597212167e6454f410057e7219153004fd7558720006bf649912007d7e7518930006f56518532004fd70189430067f73d95410067c30597211fef71058743024fc7559321014fc7198b4025df77158d10024fe75d9320106de74d8d41007ea72d03202157e71d815319e7f535923229e7d70d9510006fa42d81420567e751932036d7f7354f210aef74158740004ff7558f200067c63d95200067f5319110005fb704852006d7c7550720014fd73d91310067c65581420067e6599321015b47150d410076d53d0a42054fe7219120024fc75586422f67d5318930004fd74d8121006fb54d81420067f6419153006f865d81420067d73594420067e30597211fef42158743396dc3119131024fc755832116e7f53191322a67d31d951001cfe73d9110007d4714c93000df670505100067e2159442376f7621853201cfd70d893010e7e655074016d7f7354c4200cfe72593200bff07048510014ff70d911020f6e2054d2034e7c10597400acfe7419232006f954d81420acfe74d8d100067f75d8d411cef62158742004fe768c941004fd7119130006ec62509400467f535823219cfd76d0e421fef631587430acfc75191320acff7599121014fc711913234e7d70597402167d6154f21014fd7318931005bd748c940266df30d8d100aeef6298b431ccfe76109412173c4154d410aeec4258b41007b74350510375ef7258d210acfe74d813101edf604c930054ff751923204d7c755852000cfc70d89430067f73597400067e73d95420067d53589100067c75591200acfc764c7401a57c75d8d420aef970991300257d731915301d7e7318953004fd71d913201cfe73583413cf7441d95410067f53d8121006dd53d8d210067c40d9541004ff7258f4048d7d7698953004ff7558743054ff71d91210067d6558f2120d7e70d9153056bc62d0940006df53d8d4101cdc7359121006f654d853230ebd43191301fede51d8d41136f461585321fedc21d8d410067d62189531aebc20d912034e7d40597400073f6519120004ff75d8d420067c65d8941015bc7650d410afb671d0f410067f658c941006dd70d8d410057f7550b4000cfe70189430067d53583210067f65d092001cfe76d8d100057f7558943006be41d9130196f46150932217771054d210acff7519120007f3704851027ebd4019110006bc3119120004fd7019131054fe7219320006dc6518d4100cfe7018910014fd73d8931006bf54d91310aebc401912101e7e6354d41024fe75d8f21005bd7090942056ec628c9401fedf10d8d412177661d855300cfe70d8d101bcfe76191320057d751
  | 12 => 0xd75d8d403ce7d21d95412ce7d70d9520006fb73d81420fefa40d8141014ff70d8910024fc75d8540004ff765093001cfd72d85324757e7218953006be21d912034e7e305974001cfe735912100cfd72d8d20004fd70d85420067f7654f210067e63d9541004df735912101cfe7358642056be74d8f210567d7519320006bc64d852002fd731d8d10006df63d0d210067f7654e423d57e76d9541004fd764cb4100cfe70d8941006ec20d894100cfe7098b43164fe76909210aebe541913019edf32d8d422fe7d53d8930014fc71d8930056bf64d0b2001ddc7350530006df63189410567e425972100fba74d0320004bc7458d200065c65d8d410067e615974001e7e6354d200c67f53d8d210067e65587400afb84010940057ac20508420aef46158740005f972d0320004fd73d932042e7f6358153006de31d8d20024fe7518931004fd75d8d1001cfc73d91210f57e759893142d7f73581531c5be74109400073d53508422ce7c72d95200acfe74d8930014fd701891019e7f53591320067d53d894120e7c6054c420067d7558c422a67e41d95101e6f710d85430de7d53d85321b6f71058642024fe7599131006786518142004ff75d89310df6d534cb2100cfc7458f40006bc6450921007d4735051015efa30580422277753485100077553c85210567f6459721007ba64d0320004ff75d8d21054fe72592320dfe7314cb2118efa20d81420073f6459153006dc52d8d410afae54d0a420067c32d954201dde73d0932006bf649913119cff7359132004fd7558f410065f6518d4101cfe7358720134fd73d8f21005f57448510006bc644c9200247c75582320067e73d952015ef820191200067f5318941387775318532004fd73d93211fcfd719913118ebf4059320056ec20189310067f6558d100bdf5719891035eee768c92100df870485200067e20597210057f7558742004ef76508423867d5318931056f421586420067f6550941006fa64c81200047d7654f2112ef860581320aebc64d05201a67e6550b210047f755913201cfe76d8d42014fc7119130006bc6458d200576c215972100cfe70587420afaf4350842006ec21d8940016f461507400073f53191202157e71d915318fb87050b400067e40d95420acfe741913130e7d5319130006f870591210aebf40191202055f7359153005ec7258d10015f8764c1100f57c75509311aebd10d9120056ee72d8f2112fe8204c920114fd7099110006be6119120024fe7598b400ae7c7459442024fc75d813214ef63158632056f970d8f2000df87050940054fc72583432a77431d95102ce7d20d95200acff76d0d10024fc7558f42054fc73989101ed7c75585430eefa30d813100df8704cb40386f73118931006fb50d813201cfe73d9320006fb6118142006bf64d09210067c6558520
  | 13 => 0x931006ef7259121004fd72d9130006f973d81420077b654c110006be40d9131015bc7150f410067e6459153024fc7558720004fd7519132006dd50d8d41024fc7558232004ff7558f2118eef2058b401d4ff7650a32004fd7319321006f771591210247e751913234e7f7059740006f47158f200073e41d91531079c63d0d41024fe7558b400ddf7715893138e7d71597210057c7654d20136f676185320067f53d8940005bd74c85404867f63d89530067f5319320006bc32191203ce7c41d9541004ff7558f41006ec52d8940056f86058232244ff76487200057d70d8953015f6715091020d7c70d91531ee7e6550c4234e7e2059740004fd7558343056f72158642014fe71d8d40004fd73d8142006bf5419132005bf7458530006f650d8532054ff7518943004ff75591320acff75991322167c6154f20005f571d0f21006bf64d8d20005f77150f210d4ff71589100067d5358b410047f75589100057f755854201cfc73583410067c615895301edc63d0d410057d73d95411e4fd7399131004fd71991320befa10d812101cff7658c423aebd43d91310aef8405834105df4714cb201e7b71050d4100dbc70d0940054fc75d8f20004fc7650520375ef764cb21054fe72189102ce7e10d9520217764154d100067f7558232005df7350520054fc751894100779531814200cff7658342006ee211893001cfc73d81210aedd739913007d7e759913049f3f4319153004fd7598b4014cfd71d8d21004fd71d8943024fe75d8530004ff764cb410567e7598910004ff7650530004fe765053015ebc501912015ebe70191201d67d53991320057d7418953006de6018d41014fc74d854020e7c60581530067e63d95421e6f421d8543105de73989410667f53d8f2020f781054d1045e7f63d855300cff71d891008e7f5359130264ff7358d10006bc7458910006bf6490910065fb7058930005fb70509323a5bf7650f41004fd70d91323277b53d01400acfe7418910006be53d9120005fb7050b411a67c74d954238e7c31597210067c70597214073c4054c4201cfe73d8520024fe75189411d67d6354f420fef4765051000cff73d91300047d75189400067d71d9542007bb64c812001e5e6354e42004fd75191210067e7654f400247c7559131004ff7158232004fd71189301ccff7650b2100dbe7050b40006f976d0320014fd74d814100efa76d014034e7c30597400067e6558321006bc6450d2001cfd7258f2013d7e751093220f3e4054d400067e63597210067f32d9541006df63d0941004fd70193210067b65d8142004ff764c910017f360505100d6f710d8520005bc7458121056ef21189410057d75109401b4fd71d912112cfd764c920004ff75d853020e7f6054d20054fc7690931137e4714cb211aebe60909422557f7354d20004f
  | 14 => 0x65c75d8d4101cdc7359110006f87059132015e4714cb211e4ff715913129e7f30d95101aefb64181420067f755874201cfd7458f40015f47150921056dd73d92320075f73585530067c7059442007e7714c921006bd641913146e7f6318953004f77158f200057f75591210aeed72991320067d7654f4215ebc4058042014fc7199320015ec718c921014fc7158e42006f832d81420067c6559110006df52d8d411aebf70d912010e7c65505200acfe74d8530005df73589100e67e65c87400247e75991100067d75d853228ebf40d9110024fc755913101dde7390930004fd75d9110006f460d8532054fc7518910004ef7258d10014fc71d81321c5ef72591201075d7518d411aebc10d912001cfc7358b41056be62d0b40054ff7519321004fd765091000cfe70991210dfe732d8532004fd75189400247f765944200cfc7058e420067f53d9120006de52d8d41014fe7199232054fc768c9400047d75d9130054fe72d8d20296bf41d911000cbd76d0b400057d72d8553006bf64d0932006bf71d9120006bf7650b400057f75507200065f6354d4118ef830d81420067e75d853217d7c7558242014fe7158b40006bf745913200df571d8d10004fd75992320067f70d9542004fd70d913116edf3158c420067f65d91200acff7599321004fd7019232054fc761091012efa60d8132056ef20189400577675c85210067f31d954220f784054f201fedf21d8d411aebd40d91204876d32d8953006dd52d8d41006fb65d8142015ed768cb210067c105944218ef850d81421a75f7354d42045f9709893018efa40d8142015bc71d0d411be7f5398b4301e7c6354f41056be42592320b67f74597400067f7654d1000cfe70191100067c3159740006df50d8d410acfc76d0d100067d654cb2100cff76583431f4fd70991302177441d8553054fc75192322ce7d30d95200053f74589530067c755912100cfe70d8d41007b942d032038e7f415972100cfc70d8d2120f7a3054d102167d6154f41056bc429923201cff764c921024fe75d9131014fe7159320054fc7398b4139ebf7650f41054ff75d93210067f7654f20056f72158632004fc7650d200057d75c8740004fd71d9320086f46158540005df735911004e7e76d95200067c755913201cfe73d912101ebc6350f410067f65d8941365ee768c9210067f5359321006bd65d9120014ff76586320aebe74191300067f7359442014ff7019110017e762c85210057f7559120196f661d85420067c6599110004fd764c740015f772485100067d6454f20056dc624c9300def463c85210567e75d9321005ec72591100067c7654d41054fe72d8141006bc6490910015f8714c1103a6bf41d91310067c65d81420067c6454d20006dc63589410067c655814134e7d74597400067d6590b40004fd769
  | 15 => 0xc6359721005ec72585400057f75593200067f655091001eee638cb21056df7358f20006df6518d41056de3258e42004ff7058f420067c7654d2020f782054f400057f75509311fedc51d8d410065f65d8d410247c7558743056f820582323ce7d41d95410067d654cb4000cfc70d9131004ff74587200df6f538cb210567c3259721006fb6318142014fc71591200567e425944200cfe70592320057c72581530aef840583430067c6018953196f621d8542014fc7158b43004ff735874200cfd711911001cfc73d85400cf5f7354d2101cfe7318910005bd748cb4000cfc70189410067e7459721004fd75591310077b7054f2000cfe70586320067e6454d103cf3c41d95410067d72d95413cf7710d954100cfe76d81410067c65d91100dedc4358f21006f76150540054fe7299110014fd72d812101cfc73993211acfd70d912013f5f6358953005bf7458d100067d5358740006dc54d8d4100cfe70d9232006fa54d81421767d74594420acff7519121024fe75d8d40014fc7159132004fc7650d21014fe76d8540006ee21d8930005dd73d09321767f7459442004ff76508420067d6454d101555f7358953024fe7559121054ff71189310ae7f41597400067e60989530067f655814246f6d3218953006bf31191201fede10d8d410aebf4119110006f771591100a67f53d8143004fc7650930004fd74d8d1000cfe701923201cfe76509320067f53584420c76d538c9210067e4059721004ff7558c42006bd51d91202ce7c20d95200067f658c9100567d751932132f3f5350940006de31d8d400ae7f40597401bedf3058e42007f1214c1100aebf4019110004fd7650d100067f70d9541006fa63d81420067e2059442004fd7558242005dd7398941106de7618d410567d75d932122f775350510014ff7319131244fe7618910136f641d8532054ff76109100acfc75191310067f5358742024fc7558d2120d7e70189530067f71d95203ae7d53d9131004ff764c54000cfe7058b41217771054d41004fd7559120004ff7159320024fe751913218ff171181420075f75d8d410567d75989101d57f7354f4237f6e654cb213ff3f53d0842004fb7059120004fe7690910005f774485100def663c85210057d7654f40056be62d084200dde704c9300247e759891029e7c40d9510004ff7648540024fc7558743006f86318142006f865181420067d6550f2115cbe74991200057f70589530075f735915338f743159721006bc61d9120056ec4298b4320e7e6054d420067e60594420247c7558d1000cfd73191300067f6518910004ff7558910006fb63d81420aebe5419120014fe71d91320067c30594420067e7654d10014fc71192320067c70d9541004fd73d8520006f475d85320aef74158442004fd741893100cfa76c8120006bd5459232
  | 16 => 0x91200acff76d0f2034e7e405974015ebf641094035e7f53d893120f3e4054f4020d7c701915300cff71191100067f7559320024fc75d91321067f53d8d410067e43d9541007af7250940004fd7558d21076f461585300067f7654d210047f75592320067f62581530067f53587200057d71d8153004fd75d8d20006bd64191200acfe7419130004ff7358b40054fc73d9321056f970989100ae7c6159740024fc7559232006be41191300067f5359121014fc71189401767c6510910054fc725863200cfe7058f2114fe4318cb21006fb7059130004ff7358720005fb7059132114ff71591101aebe20d91200aebc4019131006f461d81320acfc74589100de7f53d8f21015f671d092119ebd4359232004ff75d8142166bd41191210aebf60d09400067c73d9520004fd71d9130056be4259321006bf51d9120004fe76909310067c651894111f3d5350f41006bd75191200247c7559232014fe7118940014fe7158b430067c6519120005ef7250e4234e7c705974012df87050932024fe7558d200067c65191100aedc6358f410067d70d9542006bc41d91300aebf73191201e6f46158543006f465185320aebc731912001d7e73191530067f65d0d20004ff75d91102ce7d10d95200247e76d9542006f470d8532006fb31d81421a57c75581420077731d9510024fc7558d1000cfc705913105dfb70589101ff9f63d0d41115f87050b41014fc71d8d40006bd731912019f9c4350d42006f665d85320acfc76d0d2015fb82019120056bf74593212ee7f53d8530014fc71d8143055ec7250e42005bf7458132056be741932120e7f6054d100067f7558b43014fe71d8943024fe7598910005df735854000df87050b400357c7558910006f664185320acff76d09100acfc76d0910054ff73191320af7a75d0140015f47158f21024fc75d8520014fe71189300067d6550f4001e7c6354f40014fc73d85300067b65181421aebc30d91200047d75191320067f6454d1016ebd4319132005dd7310931006bd42580420aef5711911010d7c75d8d4100cfd74d8d40024fe7599110004fd75d9130004ff75d8d400aeef4298b430057f75591100f57c75591314b67f63d915301eec638c921015bd76d0f410067c31594421cef431587421adbc70d0a423e76f5350842024fe7558d210c6de53d8d210667d53d8132024fc7558342116f710d85400057f7558b43006bf7459121006ef52d894015dbe76d09402167e6254f210067f65991201aebe30d9120056f5711891015dbe70d0842024fe75d9110054ff70189300067f6458953005df73505300067c7459721007d77350510024fc755874020d7c7098953004ff7558f421767c6510941006f77158d200ae7d7599110006bf7458d20006dc75d8d4100ddc764c9301073f53d0d4101efa634c1100567
  | 17 => 0x4bf745891001cfc7358740004f77158d201767c6510920004fe76d053015fac2019120006ee20189310067d7654e42007cf734c9213ce7f10d954120d7c70591531557c7550a3200cfc70587420247c75d8d201867c65d0910014fe71993201fede31991310067c71d95420073c6454d20004fd7498910006f46418532376ef21d8931006f975d8142166f46110932006fb7059120024fc75d814318efa50d8142004ff7258d104273e4054e42014ff70d8d102a67c41d9510004fe7690930004fd764874013d7c755813201cfe73d85400067f65d81423ce7c21d9541004ff764cb40004ff7059232006fb6518142024fc75d8943054fc725834118cfd76509200f57e75109310247e75d932100cfe76909400057e7654d422167f6154d2101fcf628c932006bc31d9120005f570c85210567e72597210057e7654d10005ef72581311867c65d094118ebc7650940004fd75d89100067f53991200def730d853215ebd7219120004ff7558321014fc7258f210afb840d0d4038e7f315972100cfe70d913120e7c6054d21004fe764c9410aeec4258b4300cfe70d8d4214ef431d8f21004fd75586320067e6359442016f461505400067c755913101cfe731894100dbc70d0b400067f74d952019e7d53592320067c3259740056ec211894000cfc7058d210057d75109320047d7654f40006bc54d9132056ee721891001cfe7358742004fd75191201d4ff7650c420057d72d8153004fd75d8930024fe75d8d101a57e76d95420067d72d9510006f440d8532006dc20d8d410077b65c81200067c7654d210047d75989100053c7458953024fe759912106f5f7354f200067c6454d100467d53582320057f7558d200afac409084244e7f635855300cfe70586420aef741587420ae7f41594420c7cf304c921014fe76d8532006de31d8d420067f629895304d7c755052020d7e76d8153006f670d85321fede31587430acfe74991211575f63989532a67d21d9510054fe72d81311def86050d4201cfc731912020e7c6054f210057d73d9542006bc644c5200067e41d9542006df635894108ddc73505400aef641991101fedf63d0d4101cff70d9130024fe755874200dfa72c81201aebf649092019e7f5358b43007af62509400057f7558242106dc53d8d41014fd70d8d10004fd731912016eed32189430067e21d95200057e74d89530067f65589100067c60d91531bcfd73d913216e7d53191320067c7654f410073f65d91200077865d8142004fd71191320067f32d95100057f7558530004fc7650d1001d7c73191530073c7454d4019ede43d8d4200efb62c812015ebe501912001ebe63d0f410357c7559110006bd54d91203ce7e31d9541006bf54d91200067f7654d40054fc72591310067e3059442056f462485100067d53d8121006bf75d
  | 18 => 0xf73591300067f53583420667f5358f200567c3259442006f474d8532014fe71582320aebf439923202df4734851001cfd71189310067d7654d42004fd7558f401e6f451d854329e7f20d95101cef461d09322ce7c10d9520004fe7650d20146dd30d8d200567c7259442006f564185320067f65109410057d70991530257f73d85531fedf51d8d41006bf6458d200067d75d913001e7e6354d10006dd72d8d41014fe71d81422bcfe768c9200067f3159740006ef7258d1000dbd76d0b400067d535844220d7e7098953006bf644c9202157e71d89530357c75d8d1029f7810d9510006fa631814200cfa76d814200cfe76d8132054fc7398b40015f671d8d100067c6454f20006bf64d0520006ef6290941054fe72191300067f73d9520057af7450842054fe72193210067d53d8940004fd7098b410067c7558242006be61d91200aeef4258b4308ede43d8d4020e7e6054f410067e40594421aebf40d9120014fe7159120056ef2098b403ce7c71d9541057e6718cb2104d7e75991203979d7418d41014fe7198b400067c43d9541054fc73189402ce7d40d95200aef67199132006be411912001ebc6350d41077f0714c1104176f53d0942137e7104c921006dd53d8d413e7ad545084207d7e75d91301d67f5399132196bf41593211dedf3058f4000fbb64d01400075d73991530a5fb705913008edc6358d40004fd76d07202177710d8553024fc75d85320073c6519120004fd759891000cfd72d85201bebf43d9132006ef62989412157d71d85530067f53189400057f755854000cfd71d8910024fc75d912000cfc765092000cfc764c92000efb614c1100067c7558d202177421d8553004ff7058f210077731597210057f755894101cfc73d91100c67f6354d21056dc3258c42006bc64509311fedd10d8d4101eee638c921007f1414c11019e7d5359132004fe7650930007b964d03200057f7259153004fb7059132056ec32189100067e6199153006be40191320067e64d8153004fd76909103dfae20508421d5ef725913200dfa70909400063f6499153387755318532006be545923215ebe401932000775534851000cfe70189410c6dc30d8d21004fd75d9120054ff76c8740014fe71582420cd7c75509210067d6258153006ee20d89410567d7518930004bc7458d102157c71d915318fb974181420def632d85320067d73d9520004fc764c520056ec20189410067c61d954200cfe7019131055bf7650842056bd74d8f210e67c65c8520006de30d8d21024fe7558232004bf7458d2012edd3058f20005ef72591100067f65d8d202557f7354d100fcff70591100bef47648510015f4714cb21006ed62189410f57c75581311fedc71d8d4101cfe73991100057f72581532277465485100247c75582422177631d8553004fd71d8940
  | 19 => 0x85430247e7558c420e57e7558f2107d7c755053018cff70591200067f30d954120e7e6054f210067f65d094100cfe7099232004fe7610931014fe71191200067f30d9542006f77158d21014fc7158042024fc75d89301aebc70d912006d7c7550b20005f571909100067d6454f2120e7d6054f200067c7654c420067f53d9121014fe71d91300aef86058342006dc6398941004fd70d8943024fe75d8d420077471589531557c75582320067c7359721007777154f21004fd7559320007af62909420557f765972133f3f5350b40004ff75d9132007e532c8521015be71d0d411def820d8143015ee718c9210aef64119110005f77150d100aef97099110004fd76d0d202157e7198953004fb7059121057e5718cb21005fb705894300cfe70d854200cfc701912101cfe76d8d210aefb40580420247c7558d20136f661d853222f74755051003df4714c920004fe7650d210067d5318941015f4714c92101e7e6354f400067d6598b4001cfe73993200aeec6258b400ae7f63597400067f5358b402f6ed321893018ded729912020f3c4054d400067f53d8542024fc7558242006fa41d8142006bf6450d204857e7618953004fd74d8d20006dd75d8d4112efa30d8132005f970d092019ddc73585420aeef4258b40006fb75d81422d57e76d952000cfc7650940004ff70586320067e73d9541007d7714c9302a77641d9510006ed62189300057f7558d10004fd7099121004fd75d91311aebc50d91200467f53d8d20006bd76d0a420acfe74d813201cdc7358910014fc7458b410057e74d85530047f7654c4202edc43d8d10014fe7119110106de53d8d41006bf64d852019edc6358d421e4fd7699131004fd7599320024fc75d8d2001e7c6354d412157f71585530077b70589530073c41d915301cfc76d0932054fe72191100567c7259721004ff7648530056f57198910054fe76d0f210067c61d9520006bf425824220e7c6054f4201eec764c9210057f725855300cfc725932038e7d3159721004ff705932110f5f7354d410aeec4258b400067c7558d103ce7f21d9541024fe75583210af3d65d0b4020d7e70191531acff7650b400067c7359740024fe75d8131006fa71d81422b77b53c8120004fd71193200acfc75991300ecfd73d8d10004ff7458f20005f571d0d10056bc6459232014fe71d894001cfe735912001cfe7358b400957c75585401fede21d8d41004fd75d85300047d75d9321004fd7418910006bf74591310075f7358153005fb70509310077953d014001cfc73d8141007d463d054101e7c6354d20006be7119120135ed738c9210acfc7458f21024fe75d93210075f6354d210067e7654e4208e7d535913000cfc70d8542006f542d85320667f6354f20005bd74c87401867c65d0920004ff7558f400073f53d9120006d
  | 20 => 0x4d7e75c85200067c65d9120006dd63d0f21006bc40d91310067f7654f4000cfc70d8d422ce7e20d9520015ec718cb210067c74d95200067f31594420077b60581532167c615855315cfd70191200de7f5358f21054ff768cb410057d7654c420067c72d95411fedc10d8d410047d7519232015f671d0f2100cfc70d8d41024fc75d8d21024fe75d8520006df65d8d410aebc64d0921006dc65d8d41006bd711912020e7e6058153006de60d8d411e5bd73d0d412067c65d0d410067e6558b400067f73d951020e7f6154d10005df735054001dde74d0d43005bc745813101cfc73d85420057f7558930006fb7058d10014fc71d8d4201e5c6354d21004fc764c9411acbe7619120004fd72d8d4000cfe7058f411767f76594420067c7654d42004ec7258d10005ef7258540006df634c921015f6718c910056f571d8f210aebf61d0d410047f7558242014bd76d0f410067e6558042014f8764c110004ff73587400567f6359442006df631094146d7e7298953146fa305823238e7e41597210067f64d89531a67d42d9542004fe7648540015f4714c9411867e65d0b210067f65991100c5dc73591210afb743d0541014fc72993210257d73d855338f6e215972122f7465505102ce7c30d95200d5f77158910004fd75d814100cfc7058f410067d654c7400df7753d85320057f7159153056de3258c42004fd75d93210073f7458553004fd7599131006f861d8142004fd7099131005bc7458520006ef7650842006f565d8532006ee21d89400075f53d8d41314fe76191302feed32d89300aebc7019120006b864c8120196f431d8542004ff7258740024fc75584420067f53d93200067f6454d200067f6558141024fc7558f213c73c65d0d41007786518142057cd638cb210067f6518941386ed321893112efa20d8132006ef7258d200057f755052034e7e705974000cff71d8d102ce7e30d9520005f5718c910006bc32d9120007ad4210932004ff7559321014fd72d8d2101cfc7359121014fe76d8542004ff75592320567f60597211dcfd73991300ae7c7459740007b5435051020e7e60d8153014ff765874315eed2018940004fd75993210aeef6298b412a67d41d951029f7a30d951001cfe73583210067d6419153197b441509410acff76d0d2120d7c70189530067d74d95101bedc6390941005f7714c9210057d75991301be7d5398b43004ff7648740004fd7650d213ce7d74d954100df67048510004fd7558d200073c7454e420057f7550a32217764154f4115ebd70191203e73c755084216edf3058c420057f7558d420acff7650921014fe7299321005f57110931006f964d0320056ec638cb210aedc4358f41005dd73c8530004fd74d8520017e772485100067f6218953054fc73d9320014fe7259321006df7359132004fd72d
  | 21 => 0xe719913200cf87059121014ff76587420e75f7354f212a67c21d95100067d73d95410acff751913120e7e6054d41014ff76584420057f7550921054fc751893129e7f71d95100067c31d952016cfd73191321073d53d0d411f5df73591300076d5350842006bc7458d101c6f8209912001cfe735844228cff7650740005df7359121054fe729891000cfe70584420eefa60d8131004ff75d913101cfc73584420acff7519132024fe7558042024fe75d92320067c755874201edc634c9410c6de63d8d210aedc6358f4200cfc73d8131024fe759923220d7e7059153024fe75d912001e7e6354f20004fe768c910004fd76c8740056dd731923210e7e76d9541056f421586320067c73d954114ef71058632054fc7258232006f471591320067f32d954200df87050720005dd708c9321bede4358e42136f441d8532006f775d85321cebd41993210def473d8532396df6118d412067c65d0d100def572d8532056fb2058242006f450d8532004fd71189400bff23048510054ff711912115db87050842015f471509410df6d538cb21137e572185320067c655894101e7e6354e42004fd7119120054fe76d072000cfe70d8543005f7714cb200077975d0320056ec52189400a5dc7350740006ef5218940005df7358542006f943d81420057f7558940057e8208c920014fe76909410075c6518d41024fe75191101fedd51d8d4118efa74d814200777615855301cfe73d91200edf870509310dfe7714cb21006bc648c920006ef72589100dfe7318cb21014f47158f200067f65909200ecff7058d10054fc751893000cfe70d85323dfae40508422167c61d855301cfc735832103ef621d8520056df634cb2001edc634c9200073c7454f4001cfd70d85300067f65591100067c65d8d412a67e31d95100067e649895300cfc701911018cfd7690b401aebd70d91202557f7354d400057d71189530acfe7419320004fd7558042046dc6358d20024fe75591100067f7558242004fd72d91100acfc745832124eed21d8910004ff7058b4301cfc76509320afaf7250b40054ff73d9132004ff735912102ede63d8d100a67d53d81430067e7654f200067e43d951002fdb324c1102ce7d72d9520004ff76509100073d53d0842014ec764c921024fc7558d2001cfe73d85420073d5350940054fc76c8530014fc71d9130056df7358f21014fc7158d200befa20d8121006be54d9120056f6219891015ebf3019120266f571d8d100053c7458553024fe7519130006de6518d41024fe7558c420073e4059442007ad43508420047e7654d41007755350510005f7715813202df67348510014fc719912010d7c7550941016f461487200067d5358742006fb71d8142024fe75593211ed5d739915300cfc7058743006ef32d89100af9f7350f41004fd768c910
  | 22 => 0x8f412067c65d0d200077b65d81420067f65d05201bd7f7354e42014ff73d9131014ff7658720006de20d8d410acfe768cb400acfe74d8d210067f6558d2000cf571d8d1001cfd7119131014fc7198b4312ef850d81321557c75592321d67f53992321ff9c31d0d410acfe76c874001dde73c853020e7e6254f20024fe755824201cfc7358042004ff74582322ce7f40d95200567c64597210067e61d952048d7f73589531075c6354d41004fd75d89310f75f63585530057f755812112fd8704c93018cfd7259320004df735911000df470505103b77753d0541004ff75d8d4129e7c71d951033f3e6550b402157471591530067d6558f401875f7354f42056f461586320067d53587202167e6154d421067f6354d41006ec20d89310067f53d93210067d7558f403ce7e71d9541004fd70d9121004fd75192321a67e655084235e7d53d893100df476505100247e7518930007ac62509400077775505100257d73d81530afae545084201edc63d0d10006dc72d8d41007bb42d03201079c6350d410057d7510931014fd74d8d414273c4054e42004fd75d81420067f5398b40004ff75d85430067f71d95420acfc764cb410067f7558910005be748c940004ff7058642004ff7059131024fc75d8142106dc30d8d41006bf645093101edc6350d41006ef62989310de7f6354f210067d6454d21396bd4119131015be7150d41005fb7050a320acfc75191300067c40597212ee7d53d85300067c41d954200cfc70d85320acfc745863201cfe73d8121056f4615844210e7e74d9541006be4159232007d763d05411ffd63158743004ff7159132004fd75189410067d73597401be7f53d91320067d7654d100aef840580423ce7e10d9541006de30d8d41014fc71d81422167661d855318ef82058b40054fe72d913001cff7658f42006f66018532006fb30d8142004ec72591100067c7654d10004fd75189310067865d814249f3d4319153006fa51d8142006bf6410930387d43218532054fc72d8d20015f674d05411775f7354c420067e71d9542006f831d8142054fe72d92320567d75192320de7753d85322176c2154d2100cfe7098b4100cfe70591210ae7f40594420067e6558c42056ee7219321054ff75d8f210def732d8532006fb7058d202173e4154f410acfe741932108e7f53d8d40004fd72d8143006ef62989400067f65d911016e7f5358c420067c63d95411d67e6454c42006f664d85320067e415974000cff7658232024fe75587202167e6154c42004ff764c940054fc75d923229e7f10d9510005fb704cb400acff759932001cfd71d89310067e6559321006bf31d9120004ff755824220f787054f20006bc645092000cfe7019132004fd73189104b57e76191530def731d8f210067d6550c42136f43158f210aebc4119130014f
  | 23 => 0xaef571991210aeef4298b40057cf734cb21005fb70507201fedf71d8d4118fb82050b40004fd721911001ede63d0f210af9c4350f42004be74d8f21006f7715913201cff7258f20005f77158d4211e7f53991310075d6354e4219e7f53d8d4214edf31d8d2101dde7310930006bc75d9120054fc7258d100aebc41191200067e60d9541056ee72d9321195f47158d421b6bf41d91210def643d85321067f53587430aebc40191320067f65d0d410047c7654d423373f53d0940004fd7318941005ec72581312157c71d81531fede71d8d41004ff7650f200576e658cb21266dd30d8d10014fc76d0921004ff7358442004fd76d0d210067e6119153006f86118142005f7714c941006df6398941006be6519120024fc7558341006bf644c520004fd71d8f200067e415944201cfc73591200ae7c40597404ae7f63991530067f53583410067e6454d200def753d8532006bf7459130006ee20189410067e735972100cfe7058f420057f7550b2020d7c7058553004fd75191300067f65d8520056f57119321057ce638cb212ce7e70d95200567e32597210acff759913115ebe4018940115f7715911001cde76d8d4101e7c6354c420067d5358b4007d7e75c853001cfc73591100057e7654d20006df6350d4201edc63d0d21016f760485100076d53d094240f3f5390942006df54d8d410073f65d0d41014fc7259321005fb70487402eef531d853020d7f7658153004fe7650d100dfcf304cb2101cfc7650d4200df87048740004fd768cb4100cfd7118910056ec4298b40004fd7558342004df7358910006df63909412a67f21d9510015f672c852101ddc735874318efa76181420067d659932118ef86058142134fd764c9210075f7358953006bd75d9120006bc6448520006bf74591200aef44158740056bc4299320024fe7558e420067e74d9510004ff75d85400073f74589531d4ff725913219e7d5358b431aebe50d91200ae7e7599120004fd73d89410067e60189530aebf71191200067f6519110006be4399321015ec714c9210247c755932004f5f7354d20006dd54d8d410befa60d81212157e76d85530067f6510910006f774d85322ad7e76d95100073f755084201cff71d9131076f661d8530004fd75d8f2000cfe76d81420057d7019153024fc7558c4200cfc70592322ce7f70d952003df47158d2000cfe70d9121004fd74d8f20006bf3219120105dc7358941004ff73583210057f7550530004ff7059132006bc64585200067c75d8d4107f5f635815301cfc7399320005fb7050d400057d7654f210d4fd709891015cbe76d09400057d73d95200576e6590842024fe75d8d411afb820d9120054fc76507200067f30597210067f654c9200acfe7499131004fd72d8540246ef20d89100067c43d9510005fa7618142004ff725
  | 24 => 0xc7559320004fd73d81210057f755854336d7f7354f41014fc71d913201cfe73d8141014fe71d81430067d53583420c67f53586320acfe74991300aebc439932100cfe7058d21004fd75584420067e60d915300cff76583210067d70d9541004ff7558b410247e7519320004fd7599121006fa65d814212edc764c9300067e63d9510056bc42993210247c75589100aef66450510006ef62909400aef571991310047f75591100057f755094100ff3614c110006ec7258d10054fe72d91100567c61594420067d7654c42056be7419320004ff75d854200fea72c81200057f735944201cfe73587400067c64d81530067d658cb40006bf4258042056df3218930006bf54d913246f6e32189530077953c8120136f710d8532005df7358941004fd70d8d421b6ed2198b411cef710d8941056f571d93210057d759911000dfa701093001cfc7359321054fc764c72011e7f53d85430667d6354f20014fc7119110006f761d81321afac20d91200247e75991300075f6518d411857c755874229e7d20d9510136f672d8532006df63d0d1002e7f53d8d1000dbe70d09400067c32d952020f7a4054f400acfc7599320056df628c9320067f7059721006bf73d91200567e7518940006be6319120006f77158d100067f53586420257f73d81530073f7454c42014fc71d9120136f631d8532006de65d8d410467f5358d200067f75d8d100fff23050510024fe7558341004ff70591210aeee649084201cfc7458b43015f4714c9102067e65d0f21054fe72d8f200957c7550540014fe71d8d204876e32d89530067f65d09102167f6254d211aeed2098b402557f7354f400057f73597210067e75d8143014fc764c9210073f6454d20014fc7258321015f6711091034e7f3059740004ff7558632055ef74508420067f65589410067f74d95422c4ff764cb20005fb70509210aeed72991200acfc7599132006f465d85320e57c7550b210067d6558321006dc6018d411afb8409094000cfc70993210067c20d95410067c61d89530067c73d954243f7930d81530067f65d8d410067c40d9542004ff75580420247c75591210057d71991530067e6159442004fd73d8540024fc75d8d420073e6419153004bf7458d10024fe75d91212ce7e40d95200067f6550d200047f7654f210057f7559232217747154f21056ec6290941015f47150d410077765485100067c65991204975f63d8953014fe7159232014fd725872000cfc7650d400fef860581411757c75508420063f65191200cd7e7510921024fe75189300047d75189430067d531894001cfc73583421ffd431d0f210073d53909420acfc76d0520004bd74d8f210077b65181420bcfd76989100067d6550b210aef97099120004fd72d814115fae2019120014fe764c921006fb32d8142056bf7459232
  | 25 => 0x95410057d759912017e7e6590b40007e5324851001cfc7359320004fd7558742024fe759913001cfd74d854305ef431989100067d7654f20194fd7690b4138e7c415972103ef431d85200067e43d9542007777154d1001f9f64d0d43014fc74583410acff75991300567f6159442054fc7258f41006f841d8142006ee21189400def443d8532004fc7648540017b774505100067d7654d4001ebe6350f4108e7f5358343006bf651912020e7d6054f40015ee718cb2101fdb604c9300067e605972115dbc70508420afb840d05400067f72d95410067c65d8d200065d6354e420067c71d95200073d5350b40004fd7198b43024fc7558632004fd74d89100aef741587430afb441d0941056dc6358e42145f87050a32004fd73d9120075f471589300067e7654d20004fd71d813200cfe70d932114edd31d8d21006f464d8532134ff7158d21006de3158e4200cfc70586420077471591530057f70591530063f5319120004ff7258743005be74989310047f7558b430057e749895301cff7658f401aebe40d93200acfc751911001ef8634c1100067e6598b40004fd76909302b77865c812020f3c4054f400067d6458953007bb70508422c4ff7258d2000fba74d0140004ff75583410ae7c40594420067f6454d21005f77158f20054fc7259110004ff7158f4004d7c7550920024fc75d8d4000cfc7018931024fe7559132004ff7058e4220f7820d815316e7e6254e420aebc40193200247c75591100047c7654d412167e6154e42276f431d8d101fedd71d8d41014fe71d8132056be42992320067d70594422157c71d89531ccff725912138e7d2159721005bc7458910055bd72d08421073f5350d410076f625895300cfe7059131054fe72d8f2120e7e6054e42024fc7559121004fd7650f200067c75d8d10004fd75189430acfc7458d2000cfc7299320004fd76d0f200067d53d854201ede6350e42006df70d8d410073d53d0a42004ff735864215ebf201912001cff764c9200079f6350d413ce7d10d95412157c7158953004fd73989100067d6550b400467f6354d200067c63d9542004fd71d91201ff9e31d0f411defa30d8143006bc6450932005df73507401867c65d09420067c60d9542004fd73991200067c6558d42004fd72d81311afba405824200dfa70d0920006f731d8542136ef614c92104d7c7559120024fe7559232056ee72d9232217762154f21024fc75d8931056ee72193200aedf4358f41054ff7598b430079f7350d410573e6550842006df634c9410067f53d85200057d74d85530073c65d912047f5f631895311e7f5358f41136f651d8532006be41d912000df87050f200067f3259721004ff7158242006be40d91210057c74581530067f5398910006bd64191210057c7654d100075c65d8d410afb84058042024f
  | 26 => 0x56bc64593210567f20597210057d74d81534475f63d8153014fd74587400067d62d815320d7d70d8153004fd7558b43014fe76d854312df87059132004fd7558b40024fe7558743015f671909411aebe70d9120006f742d8532056fb20580420067f10d9542006bf74589100075c75d8d41007b543d054100dfa70109103ce7d71d95410adbe748cb400aef860583431fede61d0d43006f564d8532004fd7418930014fc71992320057d7518943056bc6450b20004ff75d912100cdc764c930004fd75d9320005ec7250d420567d75d8f21004fd75d85431d4fd7399132007cf634c92101ebc7650d41024fe7558b43006ef62989430067f6454f200057f745895329e7e10d951031ebf43d91300957e75189400073d6419153006f751d854301e7e6354f413a6bd41d9131004fd75d8941007b77150d41004ff75587400067c21d9542056ee321894301cff7119131006f570d8532014fe7158f400aebc64d09310057f71581530067b53d81420acfe7499120004ef725911041f3f53d0a420de7d6354f2100cfe70d913200cfc70591210067d6548740006dc63d81412167c6154d200aef441584421d6df3258f420567e3259442004ff75d81411dfb84050d401fedf41d8d41006de70d8d410073c74589531defa60d81431ed7c75589430076d6218953004fe76d0d20106dc32d8d410076d654cb21014ff7018910024fe7558b410aedc4358f40056f86058042006f452d85320067d7654f21014fc71582322157e71991531e6f631d85430acff76d0f210acfe74d8d20007f3714c110006ef624c94000cfe76d8143004ff75d8532024fe75d8132194fd7299121004ff7559110085f4714c940006fb7059110054fe72d8143004ff7359321024fc75d85420367e76d9510016f76050510024fe7559131386ef764cb21046dc31d8d20024fe7519320054fc761093100cfe7018931006bd5499232024fc75589100047d75193204c75f63d915318dfa76d81420067f3259740024fe7558f42014fe7158f422057c7558b43015f774505100067f7559121024fe75d89410067f30594420067d65580420def73158f210067f31d9520015bc7150d4120f7a60d8153004fd7650d2000cfc7058b41005f976d0320006bc6450520014fe71591320047e7654d100acff76509320acfc76d05300577575c8521116fa105834101cfc73d89100047f75591310067e60d9542006f552d85320075f6354d41005fb7058d42006de40d8d4100cfe7058b430ddf7714cb21004fc765093100efa76c8120006dc50d8d4101cfd74d81431b4fe7610921006f731587420df7553d85320067e31d95420aef571991100047f75587420ae7e759913001cff7658e42006df6350d4113d7c75591320067d6558c42004ff72583410aedc6358f40196f461585423ce7e21d
  | 27 => 0xc2119120005ef7250d420c5dc7358121106dc6358d41004ff715804201cfc73d894032f3c75509400aef4615874218efa60d81420aeed72991213a4ff7650f410067c6498953004fd74d8930004fd7519320196f641d85420acfe74189300057f7550842014bc7650d4110d7e7510941005dd739093001cfe735932001e7c6354d400057d75189300077553d054101cfe73d8910014fe7199130006dc70d8d4100cfc70991310047f7558d1023eed2118910004fe764c91001cfd701893016e7f5319232004fe76d0931014ed768cb210075f65d8d4101d7e73d8153006dc73589101beed3298b431aebe4098b401d6bd43992323ce7c10d95410067c7558232056de73d9321004ff7559131006bc415923201cfc7399120004ff71591300bdf87050921006be40d9132006ef321891020f761054d10014fe7158343004fd7598b4100cfe7650920014fc7199130057cc3290932396de31191310576d6590842006dc60d8d410aef464505100067e74d9520056ee72d9320004ff75d8d1001f9e74d0d43004ff75587421ddf8705894314fe7108c9210067c43d9542006ed621891013e7e654cb400aef461587430067d75d81430fef710587400047f755912000cfc70d912101cfd72d81320067f6559120014fe76d85302ce7c70d95200acff7519130005777158953006df634c92029e7f70d95100ae7d75191321adbe70d0a420067e71597403979e4118d412173c4154f411aebf30d9120004fd7558f420057f75505400ad7f76597402167e6154f40006df7358d20015f47150f21006be75d91200acfe7419110006be311912024eef21d89100aebc64109300adef7650842024fe7599321004fd739911000778705895301cfc73589104675f63d855320f784054d40057ae6490842006f574d8532006be4319120006de54d8d410057f74585530acfc7458f20004fd7558743005bf7458131005f7714c92017e7c6590941006dd5358e420047c7654d2003ef661d85203a4fe7619131387e43218532005f57199132004ff7558b4341fad52d0a42007b942d014029e7d30d95102157e7118953004fd751911000dfa74d0320006f7651853220f7860581530ae7c415974010d7c7558d41014fe71d91200ae7e7599110006be73d9120006ef62109100247c75d8d1016cff7650f42005fb705094100cfe7498b40217746158553005bf7458121006bf53191200067f53d891000dfb734c11001cff7650e421fcdf73591312cf7820d95200067f53582420067c6598941024fc7559110005bd74989313b77465d054120d7870589530067d6550842004fc764c54018cfd76993200067e64581532a67e71d9510006fb7059320105dc7358141015f671d0d100067c7654f4001cfd70d91300077765505100076f6298953004ff73580420067c7558b43
  | 28 => 0x8142006fa651814228cfe76191100067e7654d42004fd7599132054fe7299232004fd70993210067f65d09420aebc43191200067d71d95200067e6558f21085f970991100067e7558f21006bf649911000dbe70d0b4000cfc71d8121004ff72591310aef4415874201e7c6354d4201cfc73d81421c6fa205834212cff7058d20004fd75d8131056dc6358f20004ff7650520005fb7059121006f550d85320053f74585530b57c7550740014fc71189100067e7558c420067f72d954218ef84059320004fd7559110007b87050842014fc7159320004ff7458d21056dc3258f200aeed76d0a4220e7c6054e420247c7559132004ff7158343015f671d091000cf87059132005f571d09214555f7358553014fc7199132246ed20d8910006f652d85320257f73d915308df97099130004ff7058742004ff7158f422cf6c20d9520006f764185320057f755813208e7f6354d401be7f5358e420067f5319121024fc75d8d100ae7e7519132004ff75591300aedd7399132024fe75d89311d67d539923200efa62d0320006f752d8532086f661d85401bebd43d91320067f7558d2029e7c20d9510006be5119120056ee32189300057d7510921006ee20d89310067f6454f210067f71597400067c7654f210de7553d8532014fc71d8d10054fc7258f40005fb70585421ef5f6359153296bd41d911000cfd74d8540004fd75d85200077575d8532004fd76d0d100aebc75191200af3c4059442006bf6450920004fd75587400057d70d8553056bd7418940004ff7650f210fcfd7699110004fe764853000cfc70d8f210afac4050842077f2214c1101a67d74d9542396df6418d410067f7559132006dd6518d410076e6218953006fa31d81422167e6154d401ee7e6550f40006dc73591100375f7354d101aebf6490940006bf7458d10006ef62d09100a67f5399130054fc75193201d6ee32d89431a67e72d9542004fd764cb402176c2154f21004fc764853001e7c6354d10004fd73d8141007e7624851013d5d7398953054fe72d8d40024fc75d89410067d5398b4034e7f2059740004fd70d8d4120e7f6254d20016f461c8530004fd70d89411fedf31d8d410fcfd719911014def734c92138e7d415972101cfe7319110004fd7398b40006f750d85320257f73191530067f3259442004ff764c9410067f53d854017e7c659091007d7c755093000cff73191301be7d53d91320acff76d0d200067e63597400067f65d0d100047f75582320073e411915301cfe731913049e7f631915315ebf10191200067f72d9510006fb53d81423473f53d0b40024fc7558f200067c70d95420057f7550b210073c41191530aedc4358c420077675d8532006bf648c92020e7e6054c420257d73d89530957e75c8540014fc71d8d2001cfe73593210067f654c520006b
  | 29 => 0x6403300580f811602d00f806c002000000800431803b003028800a8b2001014400e015000000000042832f80b000a07b010803402000b00000a800000f0118004002000005000c00000501b001c334006001000000c007000000c01a07600186f4162006000001c06600c056800800e00300100f40b00710067c65d8d10054ff751894102ef731d8d100ae7f615974001e7c6354d21006bf6448520004fd755832102df67350510015ee714c921024fe75d8910004ff75583420067e20d9541004ff7259110006be43d9110217743154f2101cfc73191100073d53d09400567e75d8f21024fe751913101cfc73191300bcff70589100057f7458153006bc64c852020d7e705895313e7c654c9100557f7659442004fc764c9400057f7558743006bc52191200067d6550740024fc75d91300aebe741913201cfd7019130006bf64585200067e7654d21006bf745911001e7c6354e42004ff7158f20004ff7358b410def553d8532057e82010920014fe71d932019e7f6354d420067e6418953057ae52d0a420067e7654c4218df87058542004fe768c9402feee32d893010d7e7598941006f454d8532024fe75d8540006bd5219120004fd7099132014fe7498b4129e7d10d9510014ff7658642057ac4250a324b73f43d9153014fc71d89434ad7d739915300db87050940006de50d8d41004fd7610910286bd4119110056f62118910004ff7558232006bf32d9120006df72d8d4127cfe76d05401067d5358743055bd76d0a420247f76597401e6bf6150d41004fd70d854338e7e31597210247e7519321056bc42593200067f53d81410057d74d89530067d72597400067e4359721056ef2018910015ec714cb211defa40d81430067c73d95100067c30d95410067c65585424be7f63591530aebe5499232054ff759891000cff765824238e7f715972101cff701913017e7c659092001fcf724c930006f610d85320acfc751912000ddc704c93000df87050b200067e41d95204ad7e74191530067d5358341004ff7558d100067e61589533bf3c6550d410057f7550920005bc7458d20006ac62509401b6f46190932014fc7158342057e632c85210247e75d91300aebc6410920004fd75d812113e7c654c94101cfe73589100057f7559131006bd64191300067e30d9541135f471591322157e7159153054fe72d8d4100cfe76d092000cfc70d9232006fb10d8142387d73018532006fa43d814201d7e73d8553007777158953056ee3218931004ff75591200aebc54191312067c65d0d42056fb20583210067f53591200057e74d8153024fc7559132054fc73193210ae7c41594423e76c755084208edc31d8d400067f6558d42004f5719913201e7e6354f21054fc76909100057d72991534bd7f7359153004fd75d8132024fc75d8940006f821d
  | 30 => 0x407e8000005000000801000700a006c68200b02f802001000100d80f801c08203c84380ce51100000080360410218030004e920010dd80b45d7013819401400001400a0000004197004c00000003000080464fa00d0000006002000807811401400000ec00000e190000475a00500f000c004001006001401202215900d42d202c27405d02088a3000001c16802e00000240000bd014801800400000386e4010000000000c10e0bc01b0074320000032871800800000480080360220020068004003003003402405a00b801c3d22fb003865c0160000048048000265000800010001414b80ac080001003007400c000082800000e1d600c003c03400d447004c01e00200a0354002041000005c3e203b01580e800000401d004400a3ab01d801c04c75f04f8000060000009801406c020000006804a020007000000200f0030014000002000007402e008007803c00202100d80cc000010024814003a00006900241b8002001375000c00c00b00180120e80008a880c200b00000e807808504800080040060038de000c005004830001c0081f8002c008003001000ca783e0000863c1300e0007009400e0d90b791bc01005100200c4014000002000c00001000580c8bb40000d98114010001000031c0160090070038afc00005f802c02a0e7020003c0200280010004008108012039403c05800000000004e00000008138020000008c24000700600100000010008050082010000807c000003016801402801d02c0048002033037802813200f000003800001300282ac0500052df000804622102d80706320220b1029800a00001403b409402900400000002430003bfc02a008005000002a00113a800c6aa00c05c803c0000040019fd02fa03100380fc00e01a006004c0001fd05c805400601701500cc07200300300000800f3077807e12e00400e800002600501301000d2017005800c36600100f001c070006000001000401100300e820206300200e800000300d001000004f000800c028000025800800000212100000040000138170004000007802c0c205b001000800000200080140040ce000000000201301295a000005e1a8801806200d02000440e600000f00043000070028004cc0dda2c280901ba02c013817c0081070020c34006001002000002000008f008001400200680000580000c8800803803f00e00780ca0520ae800000e0000020009e780aa00200d0030164002804003400201d0008020000067803800c04d00490c4028039000007407e01100d8008002000042000800e000033000400c01808c80fc04e08a007034400600001f80080000140138004030001017800c09a10f00180c0188000018000400c0270200060004006064801c00218d0158548410000000800001c0000fd00b135a02100400f103002000100e0
  | 31 => 0x80f000255f000024003e002000802e06f004000001601d034005001200201c003800c0d8045800400000200900001aa00400280300000030000000008000003802c0080190098144c6e001002800001a00e141807c0120072c80f8858a0370028000002019019000008603501d82d83ca00800e0109a240700bc062c02600000400d400a00902a801001a0191a8002000e008000809800c00900000153ce035001801037400a0078484000000005004013a0330000014162007007000400073c093000000e07c4fd82d000e000025000409c0000fc07f800000d04b80081a843005700080180040828000450014005800000008700180d80000060058230008110009803800e21001e802c07a00400000100000ce01380ac03200d01b8034be003c000000016a0010008014042040002800002e00900680600000330110034004011060008000644e00004200e4000000800000007526480701320da00680000ee00500701341280b200700340e2015181803000a046000076c06c04c000000401e09005300b000201c007800401e001006800434c03602a8158102023002824001c00401c003401e005000806001c00e0000020000000037001402c0400010030004003012001000600b000800001c003006800000600200701b09f8004000800003a0ba00a835803200006c80000faf140150000008000001000000000000c001401607300004f000207166a000800000900580000a600203603241680d80000054188016113012059a000000000022001b00080c432601b005817402202314f0a0c01805a0098008004113043806800c01b01f800400e01a010800800402e0003b9002a00e00301e000037803480140b6033001838407e00101d8000028b870060000056004025000404800e000000c27602a004012c000004012810401e114041806000004200000083a4000000802000000d000003805000000f016830403200c0b1400e008019004802601b00d800002203700200500a42da00a0a9000000f03680000000070a980040663d200100180cc27500200201ee00001b149800c00000000180c600301000204f4006031034c0040070280ec400e0270068048000000000031c0000000010a040040010000034108295003033000a001011007802200e006000800e0000060160236038001800037e023003077005600064a000001001b74180000520c402c801800401714195d002200300184c4000000000000008e000002004400401215700140a2002000004c00401f003001800000b005802410a000000000000a0040cf800c00202e004000003800c02da7a40000220040000032032006001006a0020028024000008000807800c0000050040148001000002422800201384680020d60000274006001019803c048032003000c0920cb
  | 32 => 0xd82c000a00401bc00000200002a000601302c8024000000001801c006001001000001e000651801000466200180140c6000000012807202006d8000030005123800012400c00500200ee48300180c807400900600bc00c0bc00023bc0d205400000ac016cc1001004c0020250a418140340b300000e800004b00002c0002005002006c0a20261230074112013042803430000b01b814c00600201480bc01600001f006dc5c007795313003804b0da001001c04a000000806200e35e81ac0000324a2003001605b001804c2e800000202a4074002001001803a00000180401ae000007823c07400c038803004000c00009cc00a002570475c00028a016800003e000023800400a06805600000142933628338006018000001c000003003008400001807400a8000000017808004c03b002800c034004004000008c00009a04580440660298434ff400601c016805802c04d014c5f200000600340f8001005002c07000100006f000e00800200009ee00400d000001c12501680400020010008b0c00200307f000401802d009803003805000000d800001501f800000200000680b000c03601280ac000005009004805200000f8074024136001000c02a0ba00b8004050001010805007c00303a000408c00607400e0040001017a9e000404c002804000238b003805800cb9305080240120040010014094000005004077202d00180500000c909100d4014016000000001003400f000400404700000100040070308118000001004800000209d008804803000500100f005001194800041a20200218004038412003802000601300e000400c00204e01880025d200a02b
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87e87d95634800147d0a21ec8900570fdd675191200063abb6e2a9e820487e85dc562d002b17d0e188c890002ab20964191100066a31ee2a12829aba880508424c8011ef02baac7900031d1d771591325ae2f3b0ca31a8200a77815d953108018e8e2302c8a98021fe1d6454f203a4dbc3a87a0a8202ae4864cb21484011f700baac890002b560772d8d410243f42eec98a40018f8805d562d04011ef02bb286900021f21d6454f2020e3d3b2a7b02840083f875906454c031e90cb8c64880021f61e43d95105c52f42cca31a82008ef825d93244015958c4ba464a00721f21975c85200061e3a4c2b12a653c7476d952144001970e9b82c4880029d60630d95411347a436e2b026415c3c845d4644c8090f90bbb284210023761c20d8d410ae9c202ea2128000c9f74dcd62440010fb0e182cb9080f179cd5398b400062e3a8c6b128200ae58108362504018eaeba8ec2990021fa1f53591100243e42ae1b1a820087e8710f65504051ed03b9ac1a10021f616765091062eadb9ec0b02a600c5c85dcd6244001878ebb2284990021f61f31d95201a43ec3841b2a8400c3f7654d42108014bf06bb2a7908029760c75d8d200043f43862b288479d3471d9543504010fd0e3aac8900028f61673191200063bc0aeca9e4200cb47119132480011bf06bb264880028f61021597400145f43ec8a0a4000a3c8458b6054c0187aa73a6c7908121f2157098b430243e43ea6b12202795d839c86454c010fd0e18eca900030fd4f7458d100069bba0e2b12a62187d86dd541d000147b0b990c8900021f61c31d954200575c12ca302840087f855da32504010ff0ab8ec4980ae2f21d42580420063db2ee0a1240018f686dc532440018b90bb9ac8880022fe1176509100243e42ae03128200c5f751cd644409587ae9a98c4a00030f1d353589100070fb22e7322a600af08158c60508014ef02bb2a6a08028fa1473d912000637b28e4b1a2000a7685083614c8018bf0bb9ac8908032d1d061581320047bc0aec99220018fa87dc162440852ed0fb8ac8a9803171d473591100053ac0841b2a840087d87d4e64480014eb033b2a7210021fa1f6558d100051fc3ac8322a60087f855db43c800147d0b996c8900030f1d86454d200053ac1cebb0a6415c3c645d442480018e8cbb8a64900028f21953909420043fc2ae831262008bd870c464480018b8edb1aa6a0802ae2016419121006663b26490a6000e1f5394c64480a74eb023a6ca880030f1d764505200069c3a0e0b12a603c5c7354d61108018eae230ec4a98031ddd771591320063a3a8c2b026400cb474d85604c8011bb0f328c6a08031d1d761581320052fc1aeca9e820087c8759153480018bae639ecaa08030f19774585200047bc0aeab1a420487e86dd561480018b90bb9ac8908030f9db6454d20
  | 1 => 0x8e9b8ac4a98021fa1c20d95410064e39ec8b0a4000e5731d97634400187eea3a2c6880028fa1432191200043f438eca988400a3e85cc464480010ff0fb2884900021fa1f655894100637b28e4b222000e386454f20480a98e8e3b2a64880023de057558f400047dc02eca1a402187d8718f65504090f90ab8ec6900d21f61c32d954201c7d436e0a126000a79851cf60508011bf06baac4880562f2117558f2000673b90e2b1a4000e1c63d9543504012f700b90c8a98031d5c471d95420043f438eab226204a5e87d8d53484010fd0f322a690002ae60031191200043ec3ceca9e4200a5d839d953d04010ff0ab86c6a10021f61f32d95100062eb98e7b2a20008f5819d932500010fd0e186caa100317dce7654d410063dba8e0b224200a798598760508014f10ca9ec0a10021f61c6454f2002eaa39aa6a0a20cad4d73d8a6254c018decbb92c6880021fa1a7654d200043ec2ee0b1e8200a758510b614c8018eae23aec68800e97a0e6454d213cd3b40c61b2a82008f9870c7605080556d03b2282902eb179db6518d410062fb2ee6b1220048fb875436050801ae6e3b82c4a98572719173109300051f42cc3b22400087f855c6648c8014ed0a300c2990021fa1f655091000679b88e0b226400cb8601d160484090f90fa9ac990002cb6087454c420052ec1eebb1a8200a5d83dd7635080147f00b20c8a980a3da1f7158f202153a40aeca9884158bc845d56348001970e1b2284988570f19175991300545e43aa8b246435cb870dd942d00018f0cbb82c2a1003175cc63d95410043fc2ae3b128000c3d741906254c074bf0cb1aa72100317dd473591210061ebaea83226400ab980cc864480018f4ec328c0a10c6ae61b42d03200053b428c1b0a640087e870c3655054dc7041b28c8900121f60f7654f400051e42ac832262038dc835d84244057970e032284900572e19170d09200043f43ea6b224000a3f845d953c80014f30bb96c0a10ff651c77350d412543fc1aebb22600487c855c364484830fb06ba8c498002a7a1020d8d410061fb2ee8b12207ca3e84dcb655086b3770ea1680a00021f61e43d95410045fc22eab1a405387c86dd562440014f10da9ec0a10028f61020d95410043ec3863b2a4000d5b731c16254c5757501990c890106cea037454d402ae3ab88cbb1a2000a778550b614c8010ff0ab86c8988024f21d5350b401743f43cc6b28840087f855c3648c88347d0dba2a6a00023ee1d65181420051f436a7b22402beaa7219320480d3a70e0b2a85a000237e0d75591101a43e436eab028400a7b805d953484094bd0eb1aa7210121fe0f7654f400061fba4c8b02a60087d8790f65480090f90abb286908121f21574d813138eb238aca99642028f4811d9324400159b06106c49882a3b20976109100051f424eca9e8200
  | 2 => 0x672d8d410043ec3c80b28840087e871d564c80014bf06bb2a7a11069e20162581530043e43ecaa0a400087e87cc365508071bd073b282900031760e7654d410043f43aa6b0e8400a6e820c565d01a187ae7b24c8a98af2e1c0644c9200053cc04c7b2a8400a7a8619460508015e100a16c2990021f6177058f2100c5e432e91928000d3474d856154c014f50b308c0a10021f61e435972101d2e41ac8a9a420487e87dd564484014bb073b2a7a00034d10775509410043ec3886b2e423487d86dd542108010f90fb2a84880021f61c32597400252e43ec6a9a420487c855d943c819169b07310c4a98021fa1c32d954101d2e41ac8a9a2000cd87018d625040517908baac5a08023de057558c420051fc22eca9a4200c5d839d95344057970e032242900ff351c76350d410243f43eeab04840087f855cb63504014bf06bb2a6a1292abe0965191200045fc22eab1e400087f855d062440014f50a18ec0a10029be096454d100ad1f424e2b288400c7875dc164c80018f0c1baac0a1003331cf72589100043f43acaa168000ae581083624c54f87cedb28c8900021f61c32d95100243f43eeab0e8600c5c751cd62440010ff0ab8ec6a00031719773585420051e422c4312a600c3c65dd163440018790bbb2842100339cc47258d100053a432a7a0a8200c74615d4424c8019b6e7b82c89080317597735074000738b88ca302840487c87d4d644402b17908ba8c8988030fddb75508420043f43ecab0282018f8801d942440015e700b20c299002ae60352191200063c386c8b12a60487c87d4d64480014f50a31ec0a10029760f6454f2000656aa6eca108400c7875dc1644800147d09306c8a980347d8f74585530056dc1ac3b02840987d87d9442480010fb0ea9cc488003171d773591312a53b408e5b2a200087d879936054c01878ca3a2c4880030f1d1645895354637b90cab22400487c855da424c00117f0eb20c8880021f61e43597400545e422e73264200c5c7359541d00014db0418acba00031bdd953508420063bb8aeab1e4200a3d8498f65480014f700bb2a6900d6aea0031d91200043fc1eeab226400d70711c16254c011ef02baac8988029b2097654d4000579c02c9b0a6400c7b65dc163508010fd0e182cb908f65760e74d815300667b9ee4b222000c75711c765480019c8c2392c2980572d19171109100243f42ceca0a6000c5d73d4f64c84018b90fb1aa6a080317dcf53591100061fbaec8b0a4000a3e8598f64480010ff0abb084880021f21d53587420047ac0ee6b06840487c855db414816d4bd0c328c6a08029760e6454d2100579c0ac7b02840087f855c262d0c014ef02bb2a6a00031dd97714c9100043f43862b2e8000cd870d8d62504010fb0f996caa08030fd8f74585530071c32c843028400c7a65dc14210801a6
  | 3 => 0xca0a40048df8754f63484011ef0eb20c2991e69da0420d954115d5c402a4322400087f8759153480019b0c7b8284a08021f61f32597400ad1f42062b2884008f7815d5644c06b3770ea16819000333d8f72581410043ec2ee2b188400a7a86d4f60508019a8ec39a828810a9d2057654f200051ec30e8a988400a3e849d953c857f9cee430ac099003871d16354e422153a40aeca9a8400a75811c3655040147d0b200c8988121f21571d89400061fba8c8a0a4000a5f835d563d00015d30418ec0a10121f215765072020cbc402e4322a62baba8499320480074bd0db1aa6908021fe1571d89430063c382caa10840087f855db424c4010fb07baac9900121fa1776505201c55dc3285a06400087d83dd564484014790ab20c8990030fdd474589100145e422eda0a400487c851d94148001ccea5296c2990021fe15711913005476412eab22600487c87d4d609088387aeca9e85a00029de0573594420043ec3cc8312a600a7980dd953508e53ad0fb9a82880023da1c20d85325a70eba0ca31a820487c855c3644c80147d0818ecaa112b1d5c753189100052ec1841b2a8271a768110165c840187eebba2c690002ae60221191202a63c3b6ca9822041a788059153484018bd0e3aec6a08028f61031d9542006ca398c8a0a20008f587103614c8053c90e99242880030fe1d64191530062ec2ae7b264200c3d75d92644800117f0eb20c8900568f21173597400043fc3ac8322a60487c855c763508035710ca1680a00029e60031594420061e3aec8a12400087e87d9542504010ff06bacc8880021fe1574d81215cf0eba6ca31a8204c3c75951648c8019a862b98c4880032e19370485200062fb9aa6b088400c3e75d90424800187ea63a2c69014f1e1c365509100243e42aeda1a4000c5c655ce6250401c3ee6322a69000297e0d7654d100243e42aed21220028f4815d56310801970c03a2c0990121fa177650d100064e3a0e6b12200087d870c565d00690fb0dbaa85a000317d97735052000739388ca3028400c5d731cf654800147b0b308c8900033a1c362509410054ec1ee3b224000a5d8598363504014bb0b206c6a08028f61663191200053cc2ee3b028415c3e7499662d00018dea6392c6880030f5db7454c420062fc2ee6b2220028f4815d943480854e902bb2a6a000355d8f71589530062e32ee6b0282018bd84dd7635000157700a90c89000297a1640d8d410071c328c99024000c5c73d9541480018bf06bb2a79080237a1f63581410052ec1ceca9e4200a5d8598063504014db0418eca9000297e0d7654d400061e3a8e8b1a2000a3c845d953484011f700baac6908030fd4d74d8f21006abb9ee2b12a68a95f835c46254c018e8cbb8ac6a10038e9d065181424ee1fb98c8a9a4000c76819d953440014f30018ecaa100297a1
  | 4 => 0x34840517b09baec4a08121fe1f53991100053cc2863b028400c3d75d53644c4090f90abb464a01e61f21b75581410043ec3887b2a40158f7865c743c84014f50b986c0a12b28f61271597400070faa4a9b1a8200c7465dc543504010ff0ab96c6881e61f21f65509410053ac0880b2e429aaad8298c644800bb28e6a1a828800317d9773581410043fc2aeca1a4200a3e8598464480010fd0f98acba00032718c7458d100063a3aee2b2262018f686dc543440018dea6392c8880028fa1431d91200063a30eeaa126415a3e849c965d00094b90eb1aa7210021fe1d53189400063cb2ee0a16420087e871d953c84018e8ea38ac8990031d1047654d410043f43ecab22400acae8718942500090fd0bb92c7a00029760c75d8d100067238ec4992802795d839cb6054c010fd0fb22a79080336d8f70509410043fc2ae9b1e40038de87dcd64440010fd0c3b2a688002ae201641913200579c02cbb0a6400c3c75dd164480033750fb8284a000317d95739894101c5e422eda1a4000a7a8654c6050801878ebba2c898802a720d64191100063ba9ee2b1e4041a7a80dd953508010fb0bb8ac5a00023e60276509310063c380c2b12a604c3e75953644c0071b906bb283900021f61f539891000637a9ee4b1a200087e869d95350401aa8e7b2a82880034e10375505402543fc1aea3126000a798590f6050973cae21b28c6a08029d60420d95410049e43aa6a10840087d8719153c84090f90ab8cc899003179d763109410052ec1ceca9a42028f4815d943c800159906b10c4880029ee017654d420053741063b2a40008bf845d563484010ff0aba6c0990033618f70589410051ec18cbb224000c3c751914148063970edb8284a00031edd870589530062eb98c7b2a84bbc3f7419563505814df04b82ca2100e3720d75591210061fba6a6b12200093f875906454c018eeea38ac89900297a1660d8d410061fb28e8b0a4000a74815cd651080147b0a31ec8900028fa16401913200c5e432e990a8000e2d5318942500016ab073aec299003171d7635094100477c12eca122000c79301d95344001976ec382842100336d8f70589410063abaea3b0a860487c855d842440011f700baac69005a1f21d6550b404061f3b2a7a128000c5f73d4d62440010fd0e32ac6880021f61676d09300061eb2ae9196800395e839cb6054c014bd0b300c6a08023e61e61181420047dc3ac230284008ef87588625016f53f08b28c6a085a1fa1e43597400051f42e643224000c7576dc553c840187cec322a69000297e0d7654f200063ba9ee2b1a4000cd476dcd41440011df0eb10c4a18031719773591100047b438c2b026441d387054d42500018eaea3aec299003391c4624c9400051ec2062b288400c74719816454c010fb0bb92c7a00030f1d464509310043ec2ce
  | 5 => 0x121f21570d8d210045fc22eab224000c3d531d163440a74f501b96ca8800317dcd53587200055a422ca30a6400c5d839d953480010fd0f996ca880d6aea03425824200675b90e0b224200ab98499460508010fd0e3aac119002ab60831d91200063642eeca108400c3d431d953504014f10ca9e40900021fe0d75193200054ec1ea9b22640487c855c262d04010fb0f992cb908021f60f755913104c3ec3ecb90a40358be87d0960908010f90ea9ac4881e68f61070d95410043ec1eeab0e8441a78805d9535080156908b2ec2990121fe1f53189400243fc1eeca9e4200c75535c6644c8019aee638ac6902af0fdd96550b400147a40aeab226400ad583994614c8014f30a318c0a10029d61470d85320243f43eeab226200c5e75d8e62504090f90ab90c88800237a1c63589410063a40aeca9e8000c5d731cf655081555d0521ac990803390c47258d103ce3a38eca992820087e87d9563504019e0e2382c89900a3e21970109100547c432e02126000a3d8590f64480015c90c9924288003179d463989410062e39ecab222000c3d76dd153d00090fd0bb82c7908031ed4f70591320043fc3ac4312a6008be8719163480018f4cbb8285909571d5c465189100064e3a6e6b1a2000d3b741c16254c0117f0eb20c890b3f47dd373591530063c386cab0a844297687dc56254c015e700b28c2990022fa1f6458d205ed1f426e5b2a82008df835d5644c42b17908ba8c8990028f61f64991530062f398cb31282008f687d85604c87f5ad02206c6a08023da1c40d853200666398e4b22200087d87d9153c8401878ea32284990028f61a41d91530043fc2aed212200087d87cc965108078bce7a9ec9908121f21574d8d210069bba0e2b22a600a5f8719463504010fb0ea98c4a00021fe1570d8d2115d5d404423224000c6f76dd542108011f70eb18c0a10021fa187654d200147a40aeab1e400087f8759153440015d50418ec0a10027c21d214c1100071daa4a9b028403c5c7354d61d0001cb0c7b2a6088003179cf659894101e2e39aa6b1220008ef825d564440011ef02bb265a02d395c406518d410ad1f42620b2884008fb805d5644c8018b8e7b2ac2a10121fa1b75581410071a30882322a60487c855db43440014db05324c4a98029760e7654c4201c6f43ee6b224200c7b75dc164484010fd0e3aac3a10021fa1c75582420051f436a63224000a3d841c365508018decbb92c8880121f21576d093100636328e4b1a200087e871d953d000187aa7ba2c69000a3d20575591300053dc2ac3b0284018fa87dc164484014bb07baec6900034e1c375509400043fc2ae03126200a788558460508018eee338acba00031d1977150d1004c3ec3865b2a4003c5c7354d61c80014bf06bb2a6a08121f21572d8d100ae1e322ea21260158bc845d56
  | 6 => 0x43fc2ae0312827987e87903655040147902b20c8a98028d2056419153006563a0e4b1a2000a5d839d953c8137b56e83828421003171d763581410061fb28e8b1a400487c855da32440015e102b1ec0a10129721f6354d410056c41ac2302840487e87dd5644c8014ef0ab26c29902b8ba14625094015d5d40684b00840a8f4865c4424c4010ff06ba8c4a000237a1c635814104c3ec38c7b2a4000c3f631d16154c014bb073b2a6a10021fe1572191102153a40aeca9e80b1a9f83590644c401c3ce8328c6a082a3b20975189400062e398cab0a4000c5f7518d605040147f0d208c8a98031b19472591100045fc3ac83226200c7471d95634800155d0418ec8900031ddc461589530062fbaec6b028200c3d76dd153908010ff0abb4849814e9ea0074d951060d1fc22e0b288400e397419460508014f50b318c0a10121fe1d75d814351d1f430ca3224000a9c835c464480090ff063b2a6880021fa1f30594420043ec3acb90e8000aae871894250193a9ee7b12c4a9ac2b9e0562189310062e3a8c6b028200a6c825d953440014bb073b2a6a08029ee016454d210052ec1ceca9e8400d1f631d16154c375ad06106c2990029ee016454d200243fc18eca9a8200e2f7518942500838e8eca9a82880021fa1c75592320053bc0aeca9a840087c8754d60908018d8cbb92c6880038718f65d0d410062fb9ce6b288400c3c65dd163480834ed0db8aa6880ae2fa1f42580420063a388cab1a8400c5f87d8d53504014bb073aac62100355d8f71591530043fc2aeca1e4000cb870d9142484010fd0e3aac89901a1f61c63d95100043fc1aeb322400487c855c3644c4010ff0abb286900033a1c062509410043f43887b2a4000ce472dc563440854e902bb2a6900028fa1463d91200051f42c81b226200a7685dc3614c8019d6ec38284210030fd4e74d8f210061fa9eeca10842baba800c4644805757500288c8900021fe1d6454d210053cc2865b028400c3f7519161480031b90cb9884980562f21170189310062fbaee6b224200c3c75d936348001938e6322c2900568f21173594420063bb8ceab1e4200c5c65dcd624402b968e2b88c8900028fa16631912000637196eca9e4200cb7741c563480090fd0bb82c99080327d9373505200243f436eab122000d38751c14210801878cbba2c488002ada1020d85320243e42ae5b1a80b2c9f7418d6050401878ebba2c69006f3518f714c9210062e31ceca9a8200c7763dc56454c0117d0e322c29002aaba1b62509400062ebaea7b1a8200c7765dc532504018d8ca392c0a08121f21571992320061fbaee8b1a2000c6f651c9605059b63b07320c8a98031e9d576d03200061e3aec8b0a4000c9c73d9141480010fd0e322a7908121f21f53591210043f438cab02840087d83dd5644c8010fd0e196ca9
  | 7 => 0x75811c3655080147d0bb8ec8900121f21574189100065bba0c2b02640487c855d943480090ff0fa9cc8900021f21d6454d100062e39ecab1220048bf87553644c0010fb07baac8900030f1d4745891000636996eca9e4200a7685903614c8010fb0fa9ec9908562fa1f7458d101743f43c86b288400c3d741d3654800147b0b98ec8900031e1c261589530043f43864b2e800487f831d953508010fb0f21aca212138ed9153181420063c32ee0a124000c3f65dd161480014bf06bb2a69080317dd463589410047dc02eab168200a7a800c765508a94ed023a6ca880feb5a0420d8d410053cc2e61b0284018fa87dc1644c82d0fd0f31acba01671e9db65c81200052fc1ac8a9a4200c5f65dcd61480a74f50039eca880121fa1676509310043fc2ae3b1a400087d859d9414c001c76a6326409000e3720d71191200052f41cc1b2a82cec3e769906454c018eecbb8ac6900030f1d764509310063c3a8e0b22420087e87d9541480154d904b82ca211069e20162d81530047bc3aca30a6400c3c75dd942d00014b90ab96c6a08021fa1f65591100061f3aec990a400087e870cb654400187ae83a6ca880031ddc671594420053a42ac830a640087e87d896054c018e8e2b2a65a00028fa1260989530052ec18ebb1a840087e871956348001878ea32284900021f614764c9400062eb98c7b2a400087e879915344139c7040322a6900861f61c43d95410043f438eab122000c7553dc5644c8051f50db8284880034e1d3705895301c6e41aeca122000cbb76dc142d00014f700b92cba000e37a1f73589100043ec2eeca1a4000d3774dc56254c0153b08106c6a08d21f61b7550b210061fbaec8b1a4000a7485593614c82b878c8bacc89000297a0c20d95420062fbaee6b122000a6f825d9534400156b02206c8988030fdd774589100043fc2aec9922000a3d850c764480072b906b8ec0a9803171d473591210065c326e0a12400087d8799153440019a8e3b1a64900021f6177650d100051ec28e7b224000cac74dc96244001c5ecbb1484a11069ea027654f420046fc1aeca122000a7a8590f60508090f90ab88c8980021fa1c43d95100063c386caa128200af0815cf60508018bee7baac3a18572d10571191200061ebaec990a4000a7985cc760508015d305318c0a10031d597714cb400043fc2aeda1a2000a75818c165c84090f90ab8ec4a18029de1564185320045fc22ec992200487d831d9534400193ee839ac4880030f1d77458d100043f43e65b2a8200a3d8690165108151b90ea9ac721002b5e056518d410055dc22ca3028400c7676dc553440018e8cbb8a64880063d21974485100065bba6e2b1a40008bf845d943480010ff0aba6c0988ff651c76350d4105537414e6b2e4200a798598c60508051ed033b264a00029de0573597400
  | 8 => 0xca3a2c6880021fa1c31d95420051e422c4b02a600c5e65dcd41d0137d5040108c8900861f61f65109410043f43c87b2a4000c3d75d53644c8830fb06baec8980021fa1a7654d420243e42ae0312624095f835d36254c0147d0a188c8900121f21576d09100043fc2aeda122015e344159541d00014f50b30ec0a10029760e7558f2100579c0285b0a64a1e382019464480d38f0e0b2a85a00031e9db65181420062fbaee6b222000e573159563c84012df0eb10c4a980f271db7350d410053ac0881b2a8435cba76dd360508019a8e7b8ac8908035c1c3755051000637ba8e4b1a20008f7815d943c80014ed02306caa10121fa177058c4200c7c402eca1a42388fb865cb40c80014790ab20c8900029da1474d85320047bc0aeab226400cd7731c5644c8010ff0abb686908121f21570d8d420043ec3c81b2a84158be84dd931480e34ed03182cb90a128fa186454d20006aa3a8e6a0a200087f855da3250001998e7b92c8880031d1c7654c92020e9c382a6a16800487f83dd953108090fd0abb643a00031edd770591200147a40aeab1e80018dc865cf214c0014f70ab18c0a10021fa1f53589100243f436eab028400af080590614c8051e902baac69000f171cf53591210052fc1aeca9e800087d870c365504151d904baac6880023ee0176509100043f43ea6b048400c3e76dd153500078b8e7a9ac888002b920562189300ae1e3a4cab008400cb774d85604c8154dd0531acb90803175d475d8d410043ec3861b2a840a8ec825d943440018bae631eca880063d21971909100051ec18ca322400087d83dd5644400153f06b88c89000297e0d7558f210063c386cab1a84318f98799320480011bf06bb283900029da1464185320053d40062b288400c3e74d936254c01ad0ea38284210032b1d37258d100063c3aee0b2264008bf87590644c0010ff06bacc8980028f614631912000c7ac0eebb1a200087f855c664c80010ff0cbae43a000356d8f705895320d3d400c9b02a6008dd839d941480018e8cbb8a64a08021fe1f651094154f54380c4a128000a7585903614c801aaeea39a828806f9518d53c8521006adb9ee0b12a600a3d850cb64480f3878edb2a86a0802bc20164d85320052ec2ce5b1a820087d87d4e64440090f90a3b284880029ea1771d814205716c28c4a128000a3e8408365508010fd0fb2ac48800317dd763589410053b428c9b0a64008bf87590644c8018e90ab8cc8990063e20175591321743e43acaa108400a5f855c363504018bf06bb2a7a00030f5d7649913005727194c6b2e42038ee87d893250001a3ee9b9ac2a98031ed8f70589530071bb28c8a0a2000c7b75dc1644c86b1f70eb2681900031dd97714c92000637a9ee4b22203fad6811c363504010fb0bba2c19080237e0d761091000637a9eeca108400a
  | 9 => 0x64585200053ac0ceca9e8400aad820c46448001878e8a9ac4880021fa1e43597210063c386cab128215a3e8408565d00051e902bb265a000317a1573d93210243f42ee2b188400c3d761d1531080187908bb2a7a00029d21542d853200717a98c4a128000a7886d4c60508010fd0e32ac8880568fa1031597400061e308e8b0aa6a2c3e761946448001c3ee8b1aa7210031b1d47258d100061ebaea9b224000cb471d91634800717d0fb2286901661f21f65509200053a40ac8322a60487e87dd5608c8018b8e632ac0a08021fa1d65508420243f43eeab26400ace8625c042440090f90aba6c0908031dd977158d420252f43ec6a9a8200a5d8508363504010fd0e3aac6880121f21676109102ce3c386caa124041c3c7654d42500015690ca1a82880022fe1175589100053c402c4312a605d9473d0d41440018b8e632ac4a086eb5a0c70d85323cd1ec26e5b2a8200a3d8590c64480012f70ea9e81900021f61676509300243f43eeab224000a7585dc3614c8010fb0bbb264a082b1b20975189400046fc1aeca1a4200a3e849806254c01cceca31242880038dd5254d85320043ec3860b288400c3c75d9163480011bd0e106c6a08021fe1576507200051f426eca9a4000cd8731c164484018b8e7b2ac0a094f1d1db65505100243ec18eca9a40018fa809d9424c40147d0b398c8900038ed9642181420051f424c0b22a600c75719866454c6bb54e939681900031da177158f200063c382c8b12a600a6f825d953500018decbb92c0a08af2e9c864c812000636b90e5b2a82afa6d829cd65c84018f2cbb82842130e8fe1173594420062e39ecab12820087f835d764c840147d0b21ec8900023d61e64185320047bc0aeca1a42008df835c4644809587ce9a9cc5a000347d8c74589530043f43c87b2a2000e5b5394f60508014f50b39ec0a10035c1c770589530053cc2e65b02849fea82088464480018f6cbb8284880021fe157650910454afc1ae3b02a600c6c65dc96050401ce6a328ec0a1002ab21162189100043f43acaa0e800087d83dd562440074bd0db1aa6a08028f61261d95200043ec2ee8b1e4200a79800c565d00018bae6a9cc5a08031761f53d8d410063d180eca9a200087d85dd932440010fd0f996caa10023be097558d1029d3ac0ee7b2a2000d73711c16254c830fb0fb16c0a99f29ba0b74d95420243ec1eeca98840087d87d4c62500018bee731acb908033c18770509320056ac18e1b0a6400a5d83dd7634402b17908ba8c890003171d773591100053c42ac63028400cbb741c1644840147b07b2ec8900021f6177650520006b4baae5a064000a768510b614c8071b906baac8880022fa1f64585200061fb18e8b12a6018f8805d5644846b974ed216c0a10031dd4d71991320243fc3ea73122000c7b65dc1615080187e
  | 10 => 0xb226203c5e7354e62d04010fd0fb2a84900022f613764c5200073432e843028400c7585dc563c80014f10ab0ec0a10021fa1c7559110454afc1ae2322a600c3f75d9142480832f50fb82c4a980297a0c20d95410246fc3aa7b1a8215cb8405c0644c543c5c40328c8900022f61e65191200051ec2ce7b2240018f4865c4424400187ea7ba2c69000317dce735974001e2e39ea6b12200487e87dd56344001b3081b9a82a00066e20174c85400051f424c3b2a4000a6e821876254c010ff0ab86c6a08039c9c7651814200679b8ee0b226405bd08350530440014bd0b386c6a08023be097650d100043ec2ee2b1e8000c5c65dcd41480014ef02b9acb90a6faa080648c9200052f42841b1a8200cb764dc5634800166902b20c8a98122fe1d54d91200043ec3e65b2a4000c3f75dd164480014f50b328c0a12d3879046518d410045fc22eab226400c5f731d953504010fb0f986caa08021fa1f325974001c6e41aeab122000a74815936254c01878e9b22c4a980327d9373585200043f43887b2a840087e87d9561508090f90fa9ac3a10031dc407654d410053a40ac8b12a600c5c7319564440011f700baac8908022f61c31d91200243f42ee2b1e4000c7b709c165c84010fd0e32ac2a1003175cd53189100052ec18ebb1a820087f855c76350801b6083b8284a08121f21576509100061fa18eca9a8235cba76d9320480014f50ca9ec0a11068f6187454f400069c386eaa168000a3d840c765480010ff0aba6c6900029d61474d85320043e432ea212200087d85dd942440b50fd0dbaa849000317d9773585420051f428c6322400087e87cc36550401a68e838ac4a989a3d61c20d85320043ec3e62b28840087d835d4644c801a9865baa84990021f61f53193200061e3aeeca10840087e87cc5651085d0f90cba884900021fa1c43597210053cc0063b2a4000a7585183614c8958f0e1a9ac8908021f61676509310043fc2ae1b2264028f980dd7624400147d0818eca900021f6177058c420043fc2ae3322640087d870c565108018bee731aca210031760e7654d420064e326e6a0a4000cbb76dc142108014bf06bb2a6900028fa1020d9541006abb98e2b22a600a768110365508a94f30039eca880121fa177650d200064e398c8a0a401c87e87cc965c84031bd0db9a82980721fa1e63597210ad1e422e0b288400a3d840c565d00015d100b10c4a08121f21571d8d4000637baee4b1a2071a74815cd65c84010fd0fa9ac8908039c5c7651814233d1f420e1b2a8400c3c7519161480010fb0fa98c9908030f54f7458d10007e09924298220bea3e841cf655040147908bb2a6880031b19772591100065c386c8a126400a7585dd3614c801878ea326c6900572b95376508420063c380cab12820087f8754e62440033750fb8285a02672bdc8
  | 11 => 0x108018baebb1cc4a08030f61f649915300674396e0b22200087f855d943440011bf0eb28c6a0b2e8fe0d64191530ac5e422ec212200487e85dc563908010ff06ba8c99080297e0d7558c42136723b6e2992420087e8719153c80010fd0eb2a85908029da1475d85320053d428c6302840087e87cc165c84010fb0bb8ac7900021fa1f31d95200053d428e7b028400a3d85cc464480014f50b98ec0a10d21f61c43d9542006363a8e4b22200087d87cc565d000187ee93a2cb908029760f6454f210056dc1ac2302840087f855c8644c0090fd0b3b6849800317dd763509410052ec1ceca9a2000a3f845d953504a78eae3b2ec6880121f21572d8d413cd3b40881b2a820087e86dd54244001ba0e038a6498003351cf71589100053cc28c7b028400e1c43d95435080187ea63a2c6880030f9d464c85200053ac0c60b288400a7685dd3614c8018deea392c8880063d21971d09100052e42ae1b1a8200c7665dc543c840147d0931eca900033318c7258d100de6a31ee2992820087e8754d60908010fb0e21eca880030f1d774589100061e3b6c8a9a400087f835d662440018d8ea31284a000297e0d6454d100243f42ceca12601687c8759541d000baa8e6a9a42880031e5c070d95410043ec3eca2122069a78805c965d00690fb0e31ecaa10030f5d764109200056bc1ac830a6400a798510f60508018bf0bb9ac4880029b60831d95420043f438eab0e8600caf741c964440010fb0f206caa0802bce05631814200477c3ac4312820087d839d9534402bc5e84b2cc5a000387d4e53d91200061fba8e8b1a4000a3d85ccb64480018d8ebb1284a00033a18b70509402a53cc00e9b2a20a1e2c20194644800147b09bb2a6900030f5d764109300043f43aa6b1220008ef825d5644c0010fb0f202cb908031e0807654d200063bba8e2b1a4000ab784594614c901a70e0a9a84210029ea1432d81420071db28c99024041a78805d953484011f50e18ec0a1003171d773589100065a38ec8992400487e87dd561d08010fd0f98ecaa10029d60630d9542014da43a86a0a2000a7a8098765508f50fd0dbaa84a08031b1d77258d100243fc3aebb0a640087f87d9442440010fd0fb2ac6a100a6da1f7150d410055bc22cbb0a6400c5f7354d61d00090fd0bbb264a08038dd4651d91202a53cc06e5b2a20038dc831d9414c0014eb0a300c2990029e21953181420053cc04eca9e840093c8754d42500015750818ec0a10028fa1673d912000477c12eab224000caf741c963440010fd0e182ca210032dd93714c9200243ec18eca9a84158bc845d932440018f0ebb82c8909eeaba1b72509400061fba8c8b1a4000ab98498c605080187aea32642900121fe0c7654d2000477c3ac43126200aae820c4644800147b0a188c890002b560420d8d410043fc1eea
  | 12 => 0x803350c773583210243f42ee2b1e80008bf845c0624c4090f90ab8cc9901e78dd9365d05410043ec1aeb322600487e87dd5648c8014bd0c3aec6a08030fdd075582420053d42ee5b028400c3f65dd163440010fd0f202cb90803175cd5398b4001d4f436c6a1a8200af080597614c8018dce5b16c0a99c71d1c5654cb216271db26a63028400c3c651d16148001970e032284908121f21574d8d204261fbb2a6a168000c7775185604c85757501a90c89000e57a0e74d81530061fb28e8b122000c5c7319562440018beebb9ac8988031b54c7258d100062eba8c73128200c7553dc563c80154dd0418aca210031ddd761581320047cc3cca302840087d879d76050c090fd0fbaac8880030f1d262589530062fb98eab0e860a8ec825d564440018b8c7baac6a08031de057654c420061e3a0c2b12a600c3d535d363c8401a76e9b82c4a98121fa16765052000667b98e4b1a2000c75819d953440014d90ab10c4a00031b1d772591201ae5c386c8a12400087e87d4d61d08011f700bb286908021f617764c5204051f424c8a9a4000a768108365508014f50131ecaa10021fa1f53593200043ec2ee0b264200c777159532c84014f50b31ec0a1002ae61261181420063d32ee099680059d4835d121440854ed033b2a7a10d66ee1d64d03200072dc1aa7b028400c6c75dd942108090ff0fa9ec99080333d8c72581410243f42ee8b0642018f4815cf60484014eb0a320c299002ad60440d912100657ba6e4b1a200087e869d9534418daaee7b0ac2a98033a18072581410243f43eeab12200087e8719561480090fd0b3b28488332c7e0d64191530052fc1aeca9c84018bc845d563d000156b08106c2990031ddd871591530052ec1ceca9c8400aad8408362504834f501b16c0a9a6baa080644c9200068e3a6e6b0aa60087d879d7644c0012e90ea9a82880033addb705084200636baea43128000c3d761d153d00014bb073aac7a00121f21576d0f200062e31eeaa12820087e871d5644840147f08bb2a6880030f9d87454e420062ebaec62128200a6e820c7655099747b0d320c8a98021fa1c6558d420051ec2864322404ac7571d4c64440018b8c6ba884a08121f21574d8f205a70e208ca31a820087e871d563480018f6a7b82c8900031d9da75d85320062e3aee6b224200ab9840c760508010ff0ab84c5a08029e61663d81420062fc1aeca988400c7775dc563480074bd07b22a7900032b54b7650842006abb98e2b12a600e1f835906454c7f9a8e3b1a64a08578e10165580420ac5e422eab1a2000c3c76dd5425000187aec3a2a6a00029de057654d200051ec24c3322a60087d87cc765508090fd0fbaac5a18022fe117650d100064e3a6e6b12200487e85dc163d04018ef02baec2990031edd770593200ae1f3a2cb316800087d87cc165
  | 13 => 0x63c32ee0b1a8400a75879d7614c8018e8e3b2ac6a10023de057558d200243f428ec99280008f587994614c8090f90aba6c6880031edd470591320243e42aeca1a200487c855c464480010fb0f982cb908562f21175589100063a3a8e2b1a4000c74815d7614c8018b8ebb1ac4a08031e1d77058d200061eba4c9312a6a5a3e8599464480018eec7b8ac4a98031ddc6615895363da7c1ac4312a600c5f7354d6244001970c9b8264900033318c725814101caf41ce5b0aa600a3f855c4644800187ee8a9ac4880021fe1d62d81530051ec20c2322a600a798598460508010fb0bb8ac7210031d54f7158d2000637c2eeca108403c7a7654f204806b970c0b8484a10028fa1643191200069a308e8b0aa600c7665dc532d00151bf0eb1e879080297e1572d8d410069dba8e0a108400cb471191634800187cc23a2c2a98030fdd375582420053cc04c3b2a8400c3c651d163440151d904bb464a00029d60460d95420066c386c6a128200c3c7519163480010fb0f986caa10031e1c06558d420051fc22eca9a8400a6d820c5651080147b0a21ec8900022fe1175591310065bb8ce3b22400487c855da32504010f90eb22a6908031de1571991320046fc1aeca1a200087d870cb65504018bf063b2a6a090b1dddb61585530147b43ee2b226400a798319760508958f4eda9ec0a12aaabe11621894000579c0ae7b028400a7983d9460508019b0e7b82c89080a3721973109311743f43e64b2884008ef87588624c00147d0a196c8900031e19770589410043f438cab028200ab9800c76448037d88c6996429080317dcf53591210063a40aeca988400a76811c365508018bee731acba00029da1470d85320063c32ee0a128200ea86250b405000147b093b2a7908021f61c20d95410053d42e65b028400c787019561508018ef02bb2a7a00021f61e75d85320043ec3cc8a9a4000a3d84c41651080187f0bbb284210570f9d1658cb400243e42ae1b24642b9ba87dc142108015ab02386c6a09e68f61073d95410053d436a6302840487f87d4c64c84018f6cbb82c4a08028fa1731d912020e3a3b2a690a2000cb870191424c4031f100baac6908029e60c65181420243f42ee8b1e4200a5d87d9463504014ed03182ca210031ddc66558f210043f438cab128200ad88358760508018b8e632ac2a10021f61e43d95421fc6e436e6b028200a5d859c363504830fb0e326c0a9a838e08353191200243e42ae83126200a9e83dc764480010ff0abb682900021fe1576d0d2056d1ec24e4b2e800087f855c3644840157300288c8900031dd4f71591320063da9ee0b224200a7585193614c80147b07b28c8900031ed9770509410063a3b6eaa0a2000a3c855c464480010ff0aba6c6908030f54c7458d200053bc0aeca9a4200a76818c36550801a38e9b9ac4a9
  | 14 => 0xd83dd953c842b87eebaa0c8900030fdd464509202cc3f43e65b2a402bab8805096010801aaee7b8ac8a9aba8fe11735974001e2f3b6a7b1a820487e85dd932440018deebb92c88830a8f61271594420051e422eca9a4000c3d751d764480eb53d0db9a86a08021fe1571191200062e39ecab0a400087f87d972148001c3ee7b22a6900023e61e63181420051f42c81b226400c3c411d9535040147f0ab20c8900066e201748c940056b4102ea2124000a5d8398365504090f90abb6869080a3da1f7158d202cd3d40063b2a400487d831d953504a74eb02396ca880021fe1d65c87400043fc2ae5b1a800087e8719564480015b10c9926088003741cf70505100063a3aee2b1a400087e8708365508151d904b98c4880029ee1563d81420063bc3aebb0a6400d1f74dcd6254c2b47d0938acba01e69da0470d95415a72a208ca31a820087f835d953c846b1790cb8484a10028fe117654d200064e326e6b0a402e87c865d442504d34f50018acba00032e1c064509320066a3b0e2992601c87c8759542c85a3a3ae7b24c8a98021fa1c65589100051ec2cc3b224000a5d839d953480018f0e0b2a85908029ea1443d814200c6e432e7212600487c855d932440018b8cbb9ac4a08032d1937158d200ae5d3b0c9902400087f855d363440010fd0dbaa82900030f1d774591320063b3b2ebb0a6400c3f63dd16254c090f90ab8ec49810a9da067654e4200c7a432e3a1a2000ccf731c9644400187c823b2a6a09529da0773d9510007163a8c4a128000a6c8259153440051e902b9ec0a10029ee1561181420066db98e0b224200c5f65dcd644400187ae8326c0a98021f60e7654d200247bc3aa3b0a6400e37815906454c0187cebb24c8900029d61420d85320053bc0aeca9e4000cd476dc5324c00147b0bb8ec8900030fd977458d200063c3a8e0b226400a5d839d95350001878ca3a2c6900121fe1d75d91300052ec1841b2a8400ea862dc142500018becbb9ac4a0a7b0fdcf6454d200051e412c8322a6bca3e841c365504014f307b2ec0a10031d1c46558d200051f420c1b22a6008df835d5644845d0fd0f202ca21002bc20165185321fe4e3b6c6a1a8200a3d861046454c010fb0bb82c7a10039519463d05410045fc3aca3224000ad583dd3614c8018f0cbb8284880022fe117558d100071cba6ca3028404c3c7595364480018f0cbb8264900031b54f7258d1005674312e12128055c757119464440010fd0e322c0a98022fa1c31d91200065c3a6e0b1a400087f855da3244001968e838ac69000317dd473589100043f43ecab02840487f87d4c64c80f30fd0f21ecaa08021fa1f64589530061e3a8e8b1a4000e34815906454c090fd0bb82c7a100f179cd53189100053bc0aeca9e8003a5e83d9153c8401b28e7b2282880023be1d621891000
  | 15 => 0x301e00000001800c00300002201300e0053f604003c0040416d20012ed00505700100801811f01000001801800000608b06900b17404e01500900c00101300000300b01501d0cd0000050030020080910130310001777070070001da00000001900000102d05702308300e01000000000000900200000000000b01004100000001a00e2aa00000000600d00e00501800000500a00003908c03801e0cc05900001403804300200006100000401a0092700000b006603200001002c01d00000600302500e0a01ba01500000000700700302601e00100100800602102c00b00002900a00009402100501509b02d01d0130280b600200000200200300503b00706014401a00501900101b03700700100000600000300100801200402c00002105207a00413f0cc00500b00000e00600500900c00c00700500300001000100000c00000302200d00204200004900100400003d0041240d400101701700c00101408f12c00b00000300100006500a01c10801100d00001301312d00339500f00000236800200000702501600600f06501109e02200508800900200000000800101201309905305c01300801803300000303000100f04c04300000800300100a0000090e400101402c00700200c00700200c00000900304d05300b02100d01101600005a00004f00f00400b0020070000270000020000f502800d03b0ca00900000b0e222a00000a0010ad00100000000d01500c00600503c00800702006900e0020fc00201804400202300100902800200100c0030c700b0810000000010040060320060100000010000210011d501100301702200601d00001300000003400d01401b03001400601400b00800000401403200405f02410a03d00100000201c0002010110c400200706000000000201300c00900f0000470051ec2cc7b22400487e85dd942440018b9063b2a6a08031719773585200061e422eca988400ad58198063504018eae3baec6880031d1977158d2005657296eca108400a3c845d953c80018bee739acb9089e5760e72d85530047bc0ae7b028400a77835d7614c8e59a8e231ec0a082a2fa1e43593210065dba0e0b22640087d87ccb65508018f2a7b82c8990021fa1c6558d410053cc2ce7b028400e375194464480011bd0fb1ac4a08031e5d975d03200043f43865b2a840487c855d3604c8018d8ebb92c8880030fdd764505200064fba0e6b22200087d83dd560908018f041bb2a7a00033318f725814105672312e221220008f587cc6624400187eedbaa85a00021fe0d75191320052fc1aeca98840487e87dd563480019e0e3b82c8990032d1d37158d200ac5f43ee8b1a4000c74815d953c8401a3ec7ba2c4a9acf275d063989410053a40ae6b2e800087e87d956148001968c9b8a64900121f21572191300053c42ac7b02840487
  | 16 => 0x6200000622715b00500001504808700903f00001304600007c02100102210e00006a00202600b3fb00000000704d03300000300c05800300300703a0000010220000060250580000470ee01d02b00003200200000004100705300804c03106d00000901332104100700b00026000901200408900301100d00500f00002300200502f05500106600700135c02100d00208401d00101507e02012c0fe00001400005e00500c00507b03a00002e00303901100600b00101600100303303401400000000407b00400016b00003607816d00800416a0120000cd03400000b00200000200000105100202a01a00400000001a00500400009500700e00100e07100d00200a00800000700001300001f00500002f00401a0020020290300e600c00100502700100500203d0050140e105c00b01400101500000623a13800500311a00b01654000100601435701105e00008900a00100b05100201006f0e200600602f0110ed00a00100001c02f04301b0070031c401a00700804d00500400d00000700002e00100500f00002118006200700503b0500000760290110630ba0000130000380af03201400200660800100a0421c301500200800000300900000000000009500200206f04600004700f01400001400000200203e00a00a5bd00000104c00000600b00600001600201a0440170040000040110170020c800001000f07
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x40a00040080200000008000002003800003840000011000103d989d87454e420049564e85190614c801ca0201c4644c9200067021d324853044001436919d87454e420050d245761d1531080183787e0564191530050d245431d953504016c0964c9214c1104de2ae1c6250b4050001c45530c47258d100060d210815d95310801434915d87454d400060da10719816454c018347420564589530040f65f869046454c01434915d87454f4000685e0c815906454c0142c925d87454d400060de1c815906454c01870811c16458953006159d9839d7614c80103f985d87454d400050b25d5318942500012359818441191530060d210815d953d0001c28701d46250940
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x4
  | 4 => 0x6
  | 5 => 0x94c
  | 6 => 0x94e
  | 7 => 0x98a
  | 8 => 0x98c
  | 9 => 0x98e
  | 10 => 0x3
  | 11 => 0x150a
  | 12 => 0x150c
  | 13 => 0x150e
  | 14 => 0x9ca
  | 15 => 0x9ce
  | 16 => 0xa0a
  | 17 => 0xa0c
  | 18 => 0xa0e
  | 19 => 0x180a
  | 20 => 0x180c
  | 21 => 0x5
  | 22 => 0x180e
  | 23 => 0xb09
  | 24 => 0xb0c
  | 25 => 0xb0e
  | 26 => 0x1549
  | 27 => 0x154c
  | 28 => 0x154e
  | 29 => 0xb49
  | 30 => 0xb4e
  | 31 => 0xb89
  | 32 => 0xb8c
  | 33 => 0xb8e
  | 34 => 0x1849
  | 35 => 0x184c
  | 36 => 0x184e
  | 37 => 0xcc9
  | 38 => 0xcca
  | 39 => 0xcce
  | 40 => 0x15c9
  | 41 => 0x15ca
  | 42 => 0x15ce
  | 43 => 0x409
  | 44 => 0x40a
  | 45 => 0x40c
  | 46 => 0x40e
  | 47 => 0x160e
  | 48 => 0x188e
  | 49 => 0xd09
  | 50 => 0xd0a
  | 51 => 0xd0c
  | 52 => 0xd0e
  | 53 => 0x1609
  | 54 => 0x160a
  | 55 => 0x160c
  | 56 => 0x1889
  | 57 => 0x188a
  | 58 => 0x188c
  | 59 => 0xe89
  | 60 => 0xe8a
  | 61 => 0xe8e
  | 62 => 0x18c9
  | 63 => 0x18ca
  | 64 => 0x18ce
  | 65 => 0xec9
  | 66 => 0xeca
  | 67 => 0x9c956
  | 68 => 0xb0956
  | 69 => 0xb8956
  | 70 => 0x209
  | 71 => 0x8a
  | 72 => 0x1409
  | 73 => 0x128a
  | 74 => 0x1a49
  | 75 => 0x16c9
  | 76 => 0x1449
  | 77 => 0x168a
  | 78 => 0x12ca
  | 79 => 0x289
  | 80 => 0x10a
  | 81 => 0x1489
  | 82 => 0x130a
  | 83 => 0x14c9
  | 84 => 0x134a
  | 85 => 0x2c9
  | 86 => 0x150996
  | 87 => 0x3c9
  | 88 => 0x1709
  | 89 => 0x1649
  | 90 => 0x449
  | 91 => 0x181516
  | 92 => 0x138c
  | 93 => 0x124c
  | 94 => 0x8c
  | 95 => 0x128c
  | 96 => 0x589
  | 97 => 0x10c
  | 98 => 0x1789
  | 99 => 0x130c
  | 100 => 0x180a16
  | 101 => 0xd0a16
  | 102 => 0x188a16
  | 103 => 0xd1816
  | 104 => 0x189816
  | 105 => 0x1049
  | 106 => 0x154b16
  | 107 => 0x140c
  | 108 => 0x3ca
  | 109 => 0x1a4a
  | 110 => 0x170a
  | 111 => 0xcd556
  | 112 => 0x20c
  | 113 => 0xd4a
  | 114 => 0x58a
  | 115 => 0x28c
  | 116 => 0x178a
  | 117 => 0x148c
  | 118 => 0x184b96
  | 119 => 0xe8b96
  | 120 => 0x18cb96
  | 121 => 0x194a
  | 122 => 0x74a
  | 123 => 0xd0411
  | 124 => 0xd0416
  | 125 => 0x160411
  | 126 => 0x160416
  | 127 => 0x188416
  | 128 => 0xec411
  | 129 => 0x160d16
  | 130 => 0x188d16
  | 131 => 0x189616
  | 132 => 0xed611
  | 133 => 0xa4c
  | 134 => 0x12ce
  | 135 => 0x198c
  | 136 => 0x168e
  | 137 => 0xbcc
  | 138 => 0x144e
  | 139 => 0x19cc
  | 140 => 0x16ce
  | 141 => 0x44c
  | 142 => 0x164c
  | 143 => 0x3ce
  | 144 => 0x1a0c
  | 145 => 0xd4c
  | 146 => 0x170e
  | 147 => 0x74c
  | 148 => 0x58e
  | 149 => 0x194c
  | 150 => 0x1a8c
  | 151 => 0x104c
  | 152 => 0x178e
  | 153 => 0x41411
  | 154 => 0x40cd1
  | 155 => 0x10b
  | 156 => 0x40ed1
  | 157 => 0x41a51
  | 158 => 0x161a51
  | 159 => 0x140411
  | 160 => 0x1a4411
  | 161 => 0x44411
  | 162 => 0x45611
  | 163 => 0x41651
  | 164 => 0x41a11
  | 165 => 0x40451
  | 166 => 0x164411
  | 167 => 0x165611
  | 168 => 0x45891
  | 169 => 0x40d11
  | 170 => 0x41611
  | 171 => 0x105611
  | 172 => 0x180b96
  | 173 => 0x180d16
  | 174 => 0x181796
  | 175 => 0x154cd6
  | 176 => 0x21554
  | 177 => 0x598d2
  | 178 => 0x59312
  | 179 => 0x58d12
  | 180 => 0x74592
  | 181 => 0x758d2
  | 182 => 0x59952
  | 183 => 0x59a92
  | 184 => 0x58752
  | 185 => 0x194592
  | 186 => 0x1958d2
  | 187 => 0x75792
  | 188 => 0xb9816
  | 189 => 0xb8416
  | 190 => 0xb98d6
  | 191 => 0x21294
  | 192 => 0x41296
  | 193 => 0x41316
  | 194 => 0x40b96
  | 195 => 0x41796
  | 196 => 0x1a5611
  | 197 => 0x1692d6
  | 198 => 0x16d456
  | 199 => 0x3d5d6
  | 200 => 0x3ccd6
  | 201 => 0x1715d6
  | 202 => 0x170cd6
  | 203 => 0x75054
  | 204 => 0x598d6
  | 205 => 0x58e96
  | 206 => 0x195a94
  | 207 => 0x18d796
  | 208 => 0x1a9954
  | 209 => 0x178e96
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1763
  | 6 => 5100
  | 5 => 2132
  | 4 => 27
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
  | 8 => 2*((h/62+packedAt gbK8 (1612+(h % 62)*6) 6) % 62)
  | 7 => 2*((h/664+packedAt gbK7 (65231+(h % 664)*11) 11) % 1763)
  | 6 => 2*((h/1707+packedAt gbK6 (244800+(h % 1707)*13) 13) % 5100)
  | 5 => 2*((h/780+packedAt gbK5 (125788+(h % 780)*12) 12) % 2132)
  | 4 => 2*((h/37+packedAt gbK4 (1890+(h % 37)*5) 5) % 27)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xf83e07c0ffe07fc3ff803fff067f79189e33cf
  | 1 => 0xfc007ff03ff83fc1ffffe0019b89fe0e3ccfc
  | 2 => 0xfffff80003ffffffe0003fffe1c0e1ff03ff0f
  | 3 => 0xffffffffc0003ffffffc000fe00fe07fc0ff0
  | 4 => 0xffffffffffffc0000000000ffff0007fff000
  | 5 => 0xf00000000000000000000000fffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x980a01c864a425413c82b2aa021b39088e11c5
  | 1 => 0x89400259216ca0c40d29b40608b80b60a2c45c
  | 2 => 0x22d4c80002514aaa400509546140c0b3016e0a
  | 3 => 0x4a754a2c800033392560018b600f405540ba0
  | 4 => 0xf39a73cb39e700004181060dded0006fbb000
  | 5 => 0xc001c030c018402318602180fff6ffd8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaece0fee0eca0feeaece0fee0eca0feeaece0fee0eca0feeaece0fee0eca0feeaece0fee0eca0feeaece0fee0eca0feeaece0fee0eca0feeaece0fee0eca0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_38845
namespace PEqualNP.Outside.L_meta_38845
open PEqualNP.Outside.L_meta_38845.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_2_0 : Interval s1Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 10 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 60 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 165 := (concat bs1_4_0 bs1_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 50 := bs1_5_0
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
theorem bs3_3_0 : Interval s3Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 8 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 92 := block_range (n:=92) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 92 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := bs3_5_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 5 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 414 := (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 (concat bs5_4_288 bs5_4_384)))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 616 := (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 40 := bs5_6_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 27 := bgb_4_0
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
theorem bgb_5_1056 : Interval gbAtlas 5 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1152 : Interval gbAtlas 5 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1248 : Interval gbAtlas 5 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1344 : Interval gbAtlas 5 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1440 : Interval gbAtlas 5 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1536 : Interval gbAtlas 5 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1632 : Interval gbAtlas 5 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1728 : Interval gbAtlas 5 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1824 : Interval gbAtlas 5 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1920 : Interval gbAtlas 5 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2016 : Interval gbAtlas 5 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2112 : Interval gbAtlas 5 2112 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2132 := (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 (concat bgb_5_576 bgb_5_672)) (concat bgb_5_768 (concat bgb_5_864 bgb_5_960)))) (concat (concat (concat bgb_5_1056 (concat bgb_5_1152 bgb_5_1248)) (concat bgb_5_1344 (concat bgb_5_1440 bgb_5_1536))) (concat (concat bgb_5_1632 (concat bgb_5_1728 bgb_5_1824)) (concat bgb_5_1920 (concat bgb_5_2016 bgb_5_2112)))))
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
theorem bgb_6_2016 : Interval gbAtlas 6 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2112 : Interval gbAtlas 6 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2208 : Interval gbAtlas 6 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2304 : Interval gbAtlas 6 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2400 : Interval gbAtlas 6 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2688 : Interval gbAtlas 6 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2784 : Interval gbAtlas 6 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2880 : Interval gbAtlas 6 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2976 : Interval gbAtlas 6 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3072 : Interval gbAtlas 6 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3168 : Interval gbAtlas 6 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3264 : Interval gbAtlas 6 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3360 : Interval gbAtlas 6 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3456 : Interval gbAtlas 6 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3552 : Interval gbAtlas 6 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3648 : Interval gbAtlas 6 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3744 : Interval gbAtlas 6 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3840 : Interval gbAtlas 6 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3936 : Interval gbAtlas 6 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4032 : Interval gbAtlas 6 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4128 : Interval gbAtlas 6 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4224 : Interval gbAtlas 6 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4320 : Interval gbAtlas 6 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4416 : Interval gbAtlas 6 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4512 : Interval gbAtlas 6 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4608 : Interval gbAtlas 6 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4704 : Interval gbAtlas 6 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4800 : Interval gbAtlas 6 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4896 : Interval gbAtlas 6 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4992 : Interval gbAtlas 6 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5088 : Interval gbAtlas 6 5088 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5100 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 bgb_6_1152)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1344 bgb_6_1440)) (concat (concat bgb_6_1536 bgb_6_1632) (concat bgb_6_1728 bgb_6_1824))) (concat (concat bgb_6_1920 (concat bgb_6_2016 bgb_6_2112)) (concat (concat bgb_6_2208 bgb_6_2304) (concat bgb_6_2400 bgb_6_2496))))) (concat (concat (concat (concat bgb_6_2592 (concat bgb_6_2688 bgb_6_2784)) (concat bgb_6_2880 (concat bgb_6_2976 bgb_6_3072))) (concat (concat bgb_6_3168 (concat bgb_6_3264 bgb_6_3360)) (concat (concat bgb_6_3456 bgb_6_3552) (concat bgb_6_3648 bgb_6_3744)))) (concat (concat (concat bgb_6_3840 (concat bgb_6_3936 bgb_6_4032)) (concat (concat bgb_6_4128 bgb_6_4224) (concat bgb_6_4320 bgb_6_4416))) (concat (concat bgb_6_4512 (concat bgb_6_4608 bgb_6_4704)) (concat (concat bgb_6_4800 bgb_6_4896) (concat bgb_6_4992 bgb_6_5088))))))
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
theorem bgb_7_864 : Interval gbAtlas 7 864 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_960 : Interval gbAtlas 7 960 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1056 : Interval gbAtlas 7 1056 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1152 : Interval gbAtlas 7 1152 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1248 : Interval gbAtlas 7 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1344 : Interval gbAtlas 7 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1440 : Interval gbAtlas 7 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1536 : Interval gbAtlas 7 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1632 : Interval gbAtlas 7 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 35 := block_range (n:=35) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1763 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 bgb_7_288)) (concat (concat bgb_7_384 bgb_7_480) (concat bgb_7_576 (concat bgb_7_672 bgb_7_768)))) (concat (concat (concat bgb_7_864 bgb_7_960) (concat bgb_7_1056 (concat bgb_7_1152 bgb_7_1248))) (concat (concat bgb_7_1344 bgb_7_1440) (concat bgb_7_1536 (concat bgb_7_1632 bgb_7_1728)))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 24, 25),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaece0fee0eca0feeaece0fee0eca0feeaece0fee0eca0feeaece0fee0eca0feeaece0fee0eca0feeaece0fee0eca0feeaece0fee0eca0feeaece0fee0eca0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808928 * 2 ^ 32 + 4276153504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_38845.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,3]⟩,⟨.or,[2,3]⟩,⟨.or,[3,5]⟩,⟨.and,[0,4]⟩,⟨.and,[4,6]⟩,⟨.or,[0,10]⟩,⟨.and,[2,11]⟩,⟨.and,[1,7]⟩,⟨.or,[9,13]⟩,⟨.and,[8,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4276153504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808928 * 2 ^ 32 + 4276153504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_38845

open PEqualNP.Outside.L_meta_38845 in
theorem PEqualNP.Outside.L_meta_38845 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4276153504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808928 * 2 ^ 32 + 4276153504) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
