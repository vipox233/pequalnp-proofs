import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37339.Model
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


end PEqualNP.Outside.L_meta_37339.Model

namespace PEqualNP.Outside.L_meta_37339
open PEqualNP.Outside.L_meta_37339.Model
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

def SBf (j : Nat) : Nat := [8, 6, 6, 5, 5, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37339

namespace PEqualNP.Outside.L_meta_37339
open PEqualNP.Outside.L_meta_37339.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0xa2e00026262100b080110746181210060a8e340009b000000000012802078f941e14e8324000000000c9100000244e34000002400018000160000e00020200002023400d0000101ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xe817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c3dca5185b94a30bea9461ed528c2daa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f721241ed42483de64907b0c920bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd98621f830c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dc8410fa108217e50043f660087e0c010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca61977d0c32ee218657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf29683ee52d06dca5a0df54b41f6a96836d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef19663dc32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131ef21a63dd434c6fea498fbd4931b7a92637c524c7d8a498db14931ef19263dc324c7ee6298f78c531bfa8263fb504c6f6a098df14131fc2826378504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510fb90a21f6a1443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29043ee42087da8410fbcc821f6190437e51087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28
  | 2 => 0x17e2b4001ee0000002a0240006d41d8001c01b530a2200062ccc9145124d8098be1c60009b9953fc4b4e90000561d82780013a57c000004c0000002100005ec000001b8740b91c9192000000000000009f0000067612b9a10000000015b480000000db000001330000001b0001ce000890478180ac7d88f24812a07cd30003ca320df06512c0308999c1242306285b4ba000000e436258d3c08b1ba1f52c90f0000001d188000630f6000414000240000880000299f26655ceb8000001049c9af29c7cd2290e0004087f0e93ba835409550620002a8000004e8000004e000000000484504001a04880a82482313831c0011925c8143419814e878fda79000905450000000b8000fd1d417c0017d0008b90d0000008b4002000e00240024344e000000740000008e00043a770002323905e14900047e534980000001e4ca1454508f0ae8000000000000000015d3e1823724a9369bb00084c392821026f06700000093d0925146a48c000001066a8000892e2000000f4000000000001be9d4708001041bd158ef000098979e817a350522830009280026b0c80000016216c8700003e0009586a800186000001690007a4000001b02e8a427b0869c40000001000000000000378679db1c40000000000000000000000440000e50004f000000294000ba0000003300011d15c5dc001294740000002200030800073000170ac18d0000000010b4ec344001eb0020080000300100600c02808006000000000000040080300400400007002000008010000040380200203001004006004068000060000000100c00c008030000140200400001c000000020040080500200800001006040058030020040080c016010000000000000480200201409802000004018000000040080300a008008040060000100000a00400000002008010000000000080b00000c0100400e000048040140140180000e00000003016008000020000040080200200001800006000000030120000080200600401002002010010000060040100101202c028040120000000000e0000200000000806010008000000000020080080900e0080100001600403004008004070020060000000001000001002000000008000000200180301800400000002010010050000040300dbf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0x87c000000005448b206166678851f902ca209a8ca000548000bc3480000000013c0012f000000498000001ee950230b70008bc07000036734129ac5265114b05912e0004326a2300001ea092d800000094000484421d50004300020b000300001e0000000000991cc448d108749c9a0818000001c5021d918c5a00019b50851c9111a000000000b238a000fe93d0009401396e0000014611b4a64547c0340702381600009a000bf80000000000000000000510004fe8a5328003460000013f00000000000000000738002b8729458000fe8587692700099c0027d0ba4940000051c2b0108001ea11d4ba490002bc9625c47232d0a80000062543093000a14508f606402cf112b4360011f01e1ae000000000003e85c86333a564000001007b4001903865ac000004a45e5348002ec000000001100000a00700000000000060000000532b491c000cd2ce000000002a0804e01f70b0508531cf0962a87ca4b3f4864b31060f80001415e4e86f477156268358250004689f800000000310608000003f0cb9c63688b0db8b11a00000000041e000788000d24c91e80636c0000023b14688cd58000009880005230219c2027a52800110810000000f398f000000000000004c5469200788c40016400097c0ea33248000dd000000850310bb1d880d261e44228dc001e63be0000010505e000000002d47c800000000000b01ff0000013226f2020008f80022e1dc741c40722142886b46c1e0002203824e0001b848c05486800000114f78000006b8cb000000240000003a80002f037000000d2800000000ba80006c000a5800004049439cc0000a4780003b4000001614dc0013b800000294000002ca000211530001a92a8d911a000821493ac5180005a4303fc5a183000185181f052a0347d987384000fa8002e00000d0d20006cd2d8193265b4300000004440020730a000c30003600001026c000830d3800364000000000008982700035a6fc000352a86a40013b0660005c20813e7793988a3f800016a020ea7846d0000982808414c152000001401300012d1d12f4000a79e30007d008943136a400005031c5f83d173250000e58f20009c80017c4702c07587b334895488910dc0004d00000000000000314000000170000000003f0146494787e0003cc00000000000001f800000002000000401151f14c68380781c000000c00000000000000030885cc8a4d0007a8d4107000000b7800000000000000002a0849c70cca000000000000000000000000000001a6000e98000000052c0000002d45580000
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x53c82cc6350b20ab59032c823e64947208f59251c825e63947209758e51c82ad64c87209798f548825d63d52208f993538823d64d4e208f992538823d6494e208fd91518823c64546208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e6515120cb588544831f54d4d20c7153534834d62d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f19153482776154d209d185534825e6514d20c7d50534831c5414d20cb152424826c6550920b318d424826e65cc920cb15332482ad640c920cb150324834f530c920cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d990851483654214520d9cc8514836432145209b99721482ad64c8520d914721483645148520d9146204823d65950208f990540826e62150208f993530823d64d4c209b98b530823e6414c208f59053082766114c209d584530826d6588420cb552210832d5408420cb553200826f6548020cb55120082e461480209ed95200826e62953109b58a54c425e63153109758c54c423f6454f108f19153c426f6254f109b18953c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c425e63952109758e548426e62152109b588548423e64d4e108f593538426e62d4e109b58b538423e6494e108f592538423f6454a108f191528425f6354a109718d528423e6414a108f590528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109ed81534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524435853c4110d914a104425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c10d6181530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520436552c84109d594210435953cc0109e594300427965840109dd9510042e462440109ed9510042d86344010
  | 1 => 0xc63e64951319b98a544c66d62951319e982544c67960951319bd89544c66c62551319ed81544c67860551318f994544c71d6315131c7152434c65c6550d31b3189434c72f54d4931cb153524c72f5414931cb150524c71c548c931a7590324c71c540c931d3d48324c73b54d4131ce153504c76b52d4131da14b504c73b5414131ce150504c76b5214131da148504c75a4314131d650c504c75a3214131d60c8504c75a31141318f596540c63e64150319798c540c71d54cc43197d95310c71d544c431b6181310c677654c4318f99353c863d64d4f219e98353c867960d4f218f99053c863d6414f219798f548865d63d5221cb58a548865e63152219758c548863e64d4e218f593538871e5494e21c7552538871e5454e21c7551538874f6254e218f990538863d6414e21cb95242886cc6350a21cb95332886ad640ca21cb950328874d530ca21ab593218866d629512197d8d544865c63551219ed81544867860551218fd91534863c6454d219bd89534867b6054d219e181534863e6414d218f590534863e64141218f590504865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f590530867a6014c219e580530863e64948218f592520866d6590821b318d420866d650c821ab59032086e5610c8218f992510863d64944219798e510865d6394421ab593210866f65484219dd95210863f64540218f191500865f63540219718d500866f6254f409b18953d034f6254f40d318953d031d5390f40c754c43d031d53d0b40a718d42d031d5350b40c754f41d02ad62d0740c754d41d02ac6250e409bd89519026c6254640a758c419029d63d02408f994435023e65d0940a718d425025e63145409758c515023e65d0540ab58b415023f6550c40ab189431025f63548409718d521034f6354840d318d521032f4354840cb50d521023d6590840cb54a421032d52108408f596411032d5290440a758c411032d5210440a758f401032d52d00408fd95401032d52500409ed95401031d54cc730c755131cc2d8604c7309b98b548c26d62d5230c758e548c26e62152309b588548c31e5490e30b3189438c32e5494a30cb552528c32e5454a30cb551528c31e548ca30a7590328c31e540ca30d3548328c29d640c630a7593308c25d63951309bd89544c26c62551309dd85544c27461551308f990524c23d64149308f990514c23d641453097997314c2d8604c5309b988540c26d62150309d984540c27561150308f992530c23d6494c3097596430c2cc6250c308fd91520c23c6454830a7590320c2d9600c8308fd91510c23c64544309bd89510c26c625443097596310c29d640c4308f992500c23d6494030a7593300c25f654c0309ed95300c25e63153209758c54c823f6454f208f19153c823e6414f208f59
  | 2 => 0x3a6234251592e2490702080001b09f0de2320742e9b500044c6e0e5000554769bf21c064be000252000f79f20005fc020002a2848000d50a06cc002003aa4ec791c7344000611303b66c4048f309a650229f40003bc8400016882cf9979040794211420304d4441df0ae3d46b0432283508e8001762547d000000000c390a28200048800000000000000006a4c09d423e2fc291bd2e85a8ed1310000008e14a10849c4f00d3400eccf10516a5742f95c19a5e8d801c1f2780f70510ac29c3c1dc130764500a22882380002231a4e81e8000002cc4c8213ea000819a5000248671e93b0004c018a050290550440002c0001b900016c74000192000000000b26605e93c0542bc8b9850c60000012c2d82b449a141f85ccd199929c834770750220000405407080030002009001070180180400003010050000b0143601803004090000707c0500006018070101800c050500200802010050180102c22004000340a01c0501000034070140701c4d07c060200302800000010a0001040b0c01d000000080200807028020000a06c01004100040001c060240101809044020081b0040000c00050000601a0380b0040200c0002000008090300e0000a0000600401064440280f0041001c0a0000001c0802805024020100100000064180100e0980001c02000020301601c33020050140100002000170300505400034030280601e6f62546439b1895190e6e62942439b58a5090f4f4314943cb90c5250e3f6550c43ab1894310e5f6550c43b31894310eac6250f429798e5190a5d639464297d8d5090a5c63542428f9974350b1c53d0d42c714d4350aac6250d42d314f4250b1c53909428f5964310a3f6550842a718d4210a6f6550842b318d4210a7661153329d58454cca3f64547328f19151cca3e64943328f59250cca7a60152329e580548ca3e64946328f592518ca3f64542328f191508ca3e649513297d8d544ca6f62551328f994544cb2c54cc932c7152324ca3d6595032c718d540cb2c62550328f990540cb1d54d0c3297594430cb2d54d0832e3d0f420ca6d6510832e310c420ca5f654c832a7191320ca6f654c832ab191320caac6250f4197d8d52d065c6354b41d3d8d52d074c6354b41cbd0d52d072d4354b41cb54a42d072d5210b41a718d42906ad62d064197d8d509065c63542418f99743506ac6250d418f994425066e62141419b588505066f6254c419b189531074f6254c41d3189531063d6590c41c754e431071d5310c41c754f421063f6550841a718d421071d5350841c754f41106ad62d04418fd95411071d53504419dd95411066e62153319b58854cc6cc6250f318fd9152cc63c6454b31a759032cc63e64943318f59250cc66e62943319b58a50cc66e62d52319b58b548c63e6494a318f592528c63f64542318f191508
  | 3 => 0x7f02f39e20843a0c4321bca396e1b64e07f82418c000fc80042a0f80018f00001cf0800000000d30000000980b1ed000384e8a0e2c8630a49fd3906d00191233685c3d03c17c04d011252bc7006e8083c614c2088b36c39c6c1221f654c758860000ac2a0a93ee6bc000b100069c879e62c40004a0002124bc002101186b05d0ac00005c3e9231c63f42487c0b45f8aa0002907a80f1d72086c85c0800c81701b0b20005e01687b188814a298b38a0d0d6814000844de0a63e2400000890ca258a813f000130e69931a42a0398292d07e8ac0003205987311e0c027c8880000000000032202000188ab0000b8e50000006dcc40002367c05197d0c4228e58f608c5dcce80025a0cc751dd3d8594838403ce67c2589011e028d585e38860c1195707e810c202c3d68604e13903e1604d10b0ce4dc5e1890003290080035c4cc1d19c2ce3650b0c82805ac74952342000df1063481f84b9f63bc65cff0c11ee469051ba0d2030238c025c000af8350001b80000615c0004e9f8230000000d030c02cdd812286008679703a47fce0a13000000869761425bc4280e04a4f4b90df0000007c00000003c000a50000010790209e204eb19103430c000480c2000418000000dc38066434368001102646083b8273847f0c901b1ae518ad9ce35034c3b0f016c70c9b1150f23c5030b73c45d4a7855198458f214b1367189412b2c66a8950302425ec62815370000c70d12b43b06387f29a01400010000824e60000005b50180032a000001c90007ec1c0cb2d22e4720002983883a0f40e47a0359600d0430930000000e49a0000d45582706d00081ce81610e2658cd12
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1c44c64953c00010162c0302011600280417143348389500411460b058318c6255032a18e6a9085a0d0c7254c4310706a9ac5a0883431c9631513183aec2a06498d487250c504c68cba0642826386550604c431a18e6b14a910c2d769503288686392a621e818354d62d0740a18e6a90842060d635484110306b1aa5a008186550604c730a18e4b1ca91841d76950328c28639ac42a2410b5d8540c920a88e6a10a290525740c85148312b20a390a41895506148020
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x980400080c8754d62d044180c8754d62d074080c8758d521044080c8758d52d0040
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 7 => packedAt s0K7 (6+((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s0K6 (731+((h/13+packedAt s0K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s0K5 (20359+((h/221+packedAt s0K5 (17928+(h % 221)*11) 11) % 1059)*11) 11
  | 4 => packedAt s0K4 (22272+((h/179+packedAt s0K4 (20482+(h % 179)*10) 10) % 647)*11) 11
  | 3 => packedAt s0K3 (1265+((h/8+packedAt s0K3 (1225+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s0K2 (244+((h/1+packedAt s0K2 (240+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xe07ffe07ffffff81fffff81ff83ffffcfe31ff
  | 2 => 0xfffffff81ffffffe07c0ffffffc1ffff23fe3f
  | 3 => 0xff80ffffe03f83fff800ffe0fffe1e03c3cfcc
  | 4 => 0xffffffc003ffffff0000ffffe003fc0ff0
  | 5 => 0xffff0000000003ffffffffff00000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x290a22310489208059492909281232a84e10d5
  | 2 => 0x42144440c9124116029052325241455120e62a
  | 3 => 0x8526a89243a426aaa8289d489cb4181ac34b4c
  | 4 => 0x1658d12492074b4d34f20610e7298063b40db0
  | 5 => 0x1860e1c71c3873f1c73ce79c06311183fbb000
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcccf0c0fcc0c0c0fcccf0c0fcc0c0c0fcccf0c0fcc0c0c0fcccf0c0fcc0c0c0fcccf0c0fcc0c0c0fcccf0c0fcc0c0c0fcccf0c0fcc0c0c0fcccf0c0fcc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37339
namespace PEqualNP.Outside.L_meta_37339
open PEqualNP.Outside.L_meta_37339.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x1000e92880002c8351900005bf43bd43be42bc42be41bc41f721f421bf40bd40f710f510
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x400003209a28a871d5310a3aa7a05914910
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
  | 3 => packedAt s1K3 (112+((h/1+packedAt s1K3 (108+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x7ffc1ffffffff03ffffc0ff83fffffe7e31ff
  | 2 => 0xf81ffe03f03f07fc3e07ff07fc3e0781b3cecc
  | 3 => 0xfffffffc003fffffc007ffffffc007ffc3ff0f
  | 4 => 0x1fffffffc007fffff80007fffff801fc0ff0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x90444448820841008a494848805294a4161055
  | 2 => 0x32cc8c3926524b2c16c2d943a434350cb2c6cc
  | 3 => 0x4191109068a484554104a2954a804259416b0a
  | 4 => 0x651a21224c06969a6590308673296011e80da0
  | 5 => 0x861c39c38f38e7e3b9e73ce062318461ffb000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafa00faaaaa00faaafa00faaaaa00faaafa00faaaaa00faaafa00faaaaa00faaafa00faaaaa00faaafa00faaaaa00faaafa00faaaaa00faaafa00faaaaa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37339
namespace PEqualNP.Outside.L_meta_37339
open PEqualNP.Outside.L_meta_37339.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x500880052502c0239860303be43bc43bf42bd42be41bc41f731f431bf40bd40f710f510
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x298096a9087345150a5aa5a05514d10
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (208+((h/4+packedAt s2K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s2K3 (111+((h/1+packedAt s2K3 (108+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffc1ffffffff03fe07ffff83fffffe63f1ff
  | 1 => 0xf81ffe03f07e07fc3ff83e07fc3c0f81bccecc
  | 3 => 0xfffffffc007fffffc0003fffffc00fffc0ff0f
  | 4 => 0x1fffffff8007ffffffc007fffff001ff0ff0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8444448841041008a424a48806524a4215055
  | 1 => 0x12cc8c3924a4cb2c16ca16c3a4286d0cacc6cc
  | 3 => 0xa199109069498655418425956a808a59c0ab0a
  | 4 => 0x85122122480d149a651481065312c011560da0
  | 5 => 0xc61c39c38e71e7e3b9e739e062230c61fbf000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeaa00eeaaaa00eeeeaa00eeaaaa00eeeeaa00eeaaaa00eeeeaa00eeaaaa00eeeeaa00eeaaaa00eeeeaa00eeaaaa00eeeeaa00eeaaaa00eeeeaa00eeaaaa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37339
namespace PEqualNP.Outside.L_meta_37339
open PEqualNP.Outside.L_meta_37339.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x80fe07fffff81c1ff83ff81e1fffff00e3c3fc
  | 1 => 0xfffff81f81ffffe0ffc0ffffe0f01fff3cfccf
  | 2 => 0xffffffe001ffffff0000ffffff001fffc0ff0f
  | 4 => 0xfffffffe001fffffff001fffffe001ff0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xa662314530432c052a193b060994d90c61c15c
  | 1 => 0xa2450c8129104a05a48492a20a14a542c54c5
  | 2 => 0x14c8a2036526194b043096555a0294a9c0ab0a
  | 4 => 0x589104924034527294a20419944b0031960ea0
  | 5 => 0x60e1c71c79c79f9ce73ce781188c18c1fbf000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeeeec0c0eaeac0c0eeeec0c0eaeac0c0eeeec0c0eaeac0c0eeeec0c0eaeac0c0eeeec0c0eaeac0c0eeeec0c0eaeac0c0eeeec0c0eaeac0c0eeeec0c0eaeac0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37339
namespace PEqualNP.Outside.L_meta_37339
open PEqualNP.Outside.L_meta_37339.Model
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
  | 4 => packedAt s4K4 (6+((h/1+packedAt s4K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x80fe07fffff81c1f07fff81e1fffff008fc3fc
  | 1 => 0xfffff81f81ffffe007c0ffffe1f01fff0cfccf
  | 2 => 0xffffffe001fffffff800fffffe001ffff0ff0f
  | 3 => 0xfffffffe001fffffff001fffffe001ff0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa662314530432c0541593b061294d90c85c15c
  | 1 => 0xaa450c8529514a082e84d2b21a14a550c54c5
  | 2 => 0x1448a2032522094b48109254540294a8b0ab0a
  | 3 => 0x589104924034527294a20419894b00315a0ea0
  | 5 => 0x60e1c71c79c79f9ce73ce781118c18c1eff000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xfac0fac0eac0eac0fac0fac0eac0eac0fac0fac0eac0eac0fac0fac0eac0eac0fac0fac0eac0eac0fac0fac0eac0eac0fac0fac0eac0eac0fac0fac0eac0eac0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37339
namespace PEqualNP.Outside.L_meta_37339
open PEqualNP.Outside.L_meta_37339.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x8435d53086f8a610df94821f7a1043ec42087de6410fb0c821bf28843f741087e88210fdcc421fa18843ef21087ec4210fb48421fa90843e521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d02fca3a05f54740beaa4817e53902faa7206f90e40de21c817e52902faa5205f94640bea8c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c52502fea2a05f14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a90817e51103eca2205d94440bea8881f551102eaa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30bf28e617d51cc3f681987e10330bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea94617e518c2faa3185f94230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa92617c524c2fea2985f14530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa88617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83dc65907b4cb20bf28e417d51c83dc43907b08720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51883eca3105d94620bea8c41f551882eaa3105f94220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483dc84907b50920f719241ed32482fea2905f14520f710a41ec21483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ec63887d4c710fb90e21f421c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10f7294216e52842faa5087b54a10b6a94217c52842faa3085f94210fd10421f920843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb20a21f541443ec62887d4c510fb90a21f421443f440887e48110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xc0800001008060080000c0000002044000c80600c050543700411060020000106803004030040305c0200000008030180e04800000040000300c0c0040601000038040282b002fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa8287fb5050ef6a0a1df14143fc28287785050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e857e51d0afaa3a15f94342bea86857d5490afca7215f54e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42be29a85ef4250b7c84a15fd4542fba8a85775150af8a2a17d14542ba28a857f5050af8a0a15f95042bf298857d5310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9995f94732bea8e657e50ccafaa1995fd5232bf2a4657d548caf8a9195f54e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132bf2a2657d544caf8a8997bcc932ef192657f514cbeea2995dd4532be28a65f4514cae8a2995fd4132be282657f540cafca8195f55032be2a0657e530cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e837e52d06faa5a0efd0b41dea16837e50d06faa1a0df55241bf29c837d53906fca520df54a41bf28c83bf41907ee8320df94241bea84837f53506f8a6a0dfd4941f7a92836f52506f8a4a0fb14941b629283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf298837d53106fca420df54841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998df94b31bea9663df32cc7ba6598df94331bea86637f548c6fca918df55231be2a4637d538c6fca518df54a31bf28c63df318c7ee6318df94231bea84637f544c6fca898df55131be2a2637f524c7dea498dbd4931be29263ec524c6d8a498f7cc931ee99263f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c6fca418df54831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fdd0721fa20e43f731c87e86390df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52887de8510fb10a21f799443ec32886fca310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea9
  | 2 => 0x199838272800000312000988aa39679c2d8002882e0ef0dd18e578f89b9000154118002f6000ac91b3480009418c0ea110a91652788ecbe0bb3c6174efa013f88ac2003836e000e41ea0a02a4cd0242005e880800274028890f533e3348a1aa00c6740d9220ae8c84596c000314cd86900464c3d9052101a87c13e2a83900004c1e41080001421e02c711a62ae6e06d2020003ec4ea141b63c5032251ec3f0001581448900023c0003a4ee00043e0000021b0b0718d59a506868c00000000918d982e09e000c7a450005044b23411c000000ac0000003b14330a5885e2330004285e8af15a000000d12a04d80004744e000480002a20007b9820006c400000160000998000004a46503509c4603e2220a4000000a539e7352097e44c784dd01e000730760613b058c089133e8528738460b812c191ad3ee600bba101067901d89b2763210d1b6306854091033407fcdd8812464250b8c028c59cfc13224c3b5168c91a4268b985406c810d79da00a234781ae2382291792e02a2082d0683e03d09a0d70440410197822025c460730265b4eb1870006180000f2e483c3003c008000002422ba000e18001d46886b0003c06d0f492146e0004907e3240000009302c000000003ae8a44f8a322c72506160462710a71971820e4131fb3420000010e1c68c11094c128794858c60fa07c000002d61586110d222260a48192aa29890000296534218000dc74c3906b02e004040860660250c08723e0006f0003c40c4bb0002c22c800065000000a3a0a3cc0000012c26e7a0002161081e86c8b13146c855800142188a0018412834b79eb1ca0a90c82c19c3ccb41991c26fcf98fa1744b4fe97f0004643617433c76c660450003b9070001966b03688015c4c01e95638e5c00019c000454a79641aa4780024405e4189e9bd00075508a403dc000001ef22e6f054000122291098000007c8ec8002b6068c823d32c6383215a1fa651150893da8e447a3a01a4e4a100731a1e0e892f4165c52380003a3e45020745c708ee80e3ea6550922c1fe5f4fd2361880a4f604938a8e0ae10c17c62c8e86719e748d38e8000700000000cc29cb30d01663812180047e350fb0201103f80e12a0001bca414516a5b86c02104a874002280940e8001252704acfca3e440000000b40560001f208000000839793100001b8b70fe00c0005400000020000600c06004130080c0100c00000010190ec050101309c23028010000200000014000680300005040050080f0080000c020100006800004110080200c010000200002004060281d0040506c0301403000240100202008004010f8010182700401000000040301401004050080101009024010a807018110300101c020180a004070000001c090041d0081e040030ac0701000008090140f0180001c16024000042f0180400
  | 3 => 0x30778d30502fcdf0001b80000009e0ee5a8d42052d2000000003fc7500004813849cc08790001d01822324857c7593f490000e70000821c09a9750000004c8592a6800e818412a4082f05f05a37c389040a62d813a354382e4018514923982683f000000428003226d40021e352000d800023418c6
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xd43502b86050d40d614f405031c5390140d6181531023d6590c40c754e431031d5310c40d394e521034d5394840d394d521034d5354840d594e51103555394440d994a51103655294440d594d51103555354440d994951103655254440c754f401023f6550040a718d401031d53500409ed9540102d86350040c715143cc2d86050f309dd8552cc2746154b309bd8951cc26c6254730e650f40cc2d96310330e690c40cc26e62152309b588548c27661152309d584548c31f5410e308f992544c25f63551309ed81544c23e6515130c758c544c25e6590d30c7152434c25c6550d30c7151434c2d86050d30ce153304c31c548c1309b98b540c26d62d50309d987540c27561d50308f596540c31c6355030ce181540c23e64150309798c540c26e62150309b588540c27661150309d584540c25d65d0c30c7553430c25d6510c30c7550430c32e5494830cb552520c32e5454830cb551520c3365494430cd552510c3665294430d954a510c3365454430cd551510c3665254430d9549510c33954d0030e6d0f400c2796510030e610c400c31d54cc03097d95300c29c644c030c7551300c27b654c030ae191300c25e63d53209758f54c823e64d4f208f59353c82e46150b20b918532c82ad6408720b358c21c836551087209d987548827561d52209798c548825d63152209d984548827561152209d987538827561d4e208f990538823d6414e209d98453882756114e20dc982518836651c822097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d209b19542482e461509209b19532482e4614c920ab59021482cd6308520ba98021482e661881209798c540825d63150209b988540827661150209d584540823e6414c208f590530826e6214c209d98453082756114c209bd95200827b65480209798f54c425d63d53108f99353c423d64d4f108f99052c423d6414b109798c52c425d6314b10b918941c42e4624c710ad59021c42d56308710d954821c426e62d52109b58b548425e63152109758c548426e62152109b588548426e62d4e109b58b538423e6414e108f590538426e6214e109b588538436a6094a10da949208436652c421097d8d544425c63551109bd89544426c62551108fd91534423c6454d109bd89534426c6254d108fd91524423c645491097d8d524425c63549109d19541442e462505109d19531442e4624c5109d99721442b56408510b558c21443655208510bc98021442f261881109e19520443e02148110b998a104425e63150109758c540426e62150109b588540427661150108f990530423d6414c109b988530426d6214c109d984530427661d48108f990520423d64148109798c520425d63148109e980520426e62940109b58a500427965840109dd95100427b6544010
  | 1 => 0xa4c0017687800908000000000000772be4180c002200004c0f12614880bb886000060014c10892000005d148a00008c000ad854000b0002aa2992e630003f0dc7f9344f2d49c9422386a4299c9ea4e7c8be7986e002ec8217c2d8040000000000028020040f01c0401c09014060000500c000100101001018090180001000010040240001402000010001200401000010040000000000100000100c0100c000080300c030080103000018000000000004028160a80f00400000000101302c000140001401004030040301c070040c00c000080200c04014010240003c05000000300b004090040e0000000c010140c004010000000c010066e62141439b5885050e7661141439d5845050f5b4314143ce90c5050f6a6214143da5885050f726114143dc5845050e9d6490c438fd954310eb86050c4397d954310ed86050c43a7d954310f1f6550c43e6d814310e9c6050c43e61814310e986050c439dd855210e7461548439bd895110e6c6254443c750d5010e7661942429d5865090b6742145428fd954210a6f6550842b91854210a7661d53329d58754cca7a60d52329e583548ca7661942329d586508ca7661951329d586544ca7761551329d185544ca7b60551329e181544cb6732145329d984540ca7561150329e980540ca79601503297d95320ca6f654c832b9185320cab46150b419b98a509066d6294241cb14b425076452d05418fd9541106776550441b9189411066e62d53319b58b54cc6d4614cb319e983548c67960d52319b98a508c66d62942319b98a544c66d62951319bd89544c66c62551319ed81544c6786055131d314b324c76452cc5319b988540c66d62150319e980540c679601503197d95310c677654c431b9189310c65e63951219758e544866f62551219dd85544863e6494d218f592534866f6254d219dd85534865e63d50219758f540867a60d50219e583540863d6595021cb189540873461550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c21d318953087546154c218f990530863d6414c219798c530867a6014c219e580530872d54d08219b59442086e56110821d354f320866d650c821b9584320873554d0421e9d0b41086756510421b9588410875553cc421f1ccb3108675650c421b958831086e562884219bd9521086776548421b9d9521087676548421b999121086e46448421e995121087a55448421b998d21086e46348421f194d21087c55348421b9d81210873a5494021ce552500875a5394021d654e50087e12194021ce95150087395454021d694d50087595354021f848550086b86050f409dd8552d02746154b409bd8951d026c62547408f997435031c53d0d40c714
  | 2 => 0x940140011259800590000000072000b10003b8002b2a0b90447b8ec0a80000000172145600000000862c04622a2aa003600000000000949f9bc8280000000001b8000006f800000007d1fc001d0002f000000002ba668006da0c260000000078000002d60028ab18001880000016000009b29619000500507a0d407100a38f27291471a28790006198e5a93200008000008089c0000094828119de000001591e578fe00020a504e9923a6d01e56a60160f41d258421c033a844c0009b8348899455960b20006e9a6761f80019e0023c001f6001d400000060b8002744a8380000000084340a21f8009700062000a40fa010000000e5e246b08900000083a560415023244001b2000000000000000002e686800000c053a6846ab00010e4800000000000dea6800b4000000008d000001b0a18001c0325c22e000ea9e04020800000000023e180724e922001f0000e852adc5a23832954bc82c0022c5c8b400000000002c800628000000061000870889c0245b8022a0cc3d88a12aa40010c000000000000000951ac002d89200000000471465b0006a13e388481b096368009f1e2658000eaca2f0d60000a7a92c81a8831ab484a16929fa1a26a002e8278ae6000099a98308005f800731249d8006811026990a49361d800571046aacc69204b3800988000b8007685ea3000a792816a8200000b48e0bd0787b00039aeaa8800001c20d87c0003e0c152000ba001ce8d8224e2a83e198a71d6a98c4b787aae01a28026512e2acae0af06645a5e901627121040aac3225a74a326ba2439000002da000f05e8126480034aae89800608a468
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x5800110103cc00800048018000d00a14004011300008000054324738b500020001004e61625845050f0cba8c0a1887a29c86050c43d12e43028621e92711814310f48b88c0a1887461c1435404398ce73224210ca67498d2108782aa2a690843c85512154021e82a690aa010e185418143cc24cbb48620661861506050d30c30c6302a81851975d0f400c30cb288620061071d9544c030a48e8a9042885447354821442d0ba04290221705cc2148110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x4400c09755c86050c43c11755c46050c43c81725c46050c43
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 586
  | 4 => 379
  | 3 => 23
  | 2 => 3
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
  | 5 => packedAt s5K5 (17772+((h/195+packedAt s5K5 (15822+(h % 195)*10) 10) % 704)*11) 11
  | 4 => packedAt s5K4 (15662+((h/126+packedAt s5K4 (14402+(h % 126)*10) 10) % 550)*10) 10
  | 3 => packedAt s5K3 (1169+((h/7+packedAt s5K3 (1127+(h % 7)*6) 6) % 39)*6) 6
  | 2 => packedAt s5K2 (183+((h/1+packedAt s5K2 (180+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf81ffff03ffff00f1e3f8ffff1fffc0013f3fc
  | 1 => 0x7fe0f8ffc1f1fff01fc7f1c0fe381ff8eccccf
  | 2 => 0x7fff00fffe01ffffe007fe00ffc01fff0f0f0f
  | 3 => 0x800000fffffe01fffff80000ffffe007f00ff0
  | 4 => 0xffffff00000001ffffffffff00000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8c2101184200201020982463048c43001515c
  | 1 => 0x114a21228c82a0500e42908a5211495064c4c5
  | 2 => 0x22845245106540a720052414a48292a30b0b0a
  | 3 => 0x714a4882940653a54900020c92700c5b00ea0
  | 4 => 0x4418c00e318989cc9926493800040306dea000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0feeaeac0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37339
namespace PEqualNP.Outside.L_meta_37339
open PEqualNP.Outside.L_meta_37339.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10054f028d243179f00b1c3100d4e200000022128c00a1e057390000da80e192306e21a363a515804c845bb0601d322e0022d2c9c99866408804a68f192a39e805218341020604000280c4800c08800264c180017fd5005fe54017f55005fc54017fd4c05fe53017f54c05fc53007fd0c01fe43007f50c01fc43017fd4805fe52017f54805fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc32017fd4405fe51017f54405fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc2100ffd40037f5000ff94003fd5000df54003fc5000ffd0003fe4000ff50003fc4000ffcc003fe3000ff4c003fc3000ffc8003fe2000ff48003fc2000ffc4003fe1000ff44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a4208bfd9521006feca908027f6548411ff32a4202bf99521047faca90822fd6548411fe32a4202bf19521046f8ca9080a7c6548401ffb224200bfd9121007fcc890802fe6448401feb224200bf59121007f8c890802fc6448411ffaa24208ff95121047faa890823fc5448401ffb1a4200bfd8d21007fcc690802fe6348401feb1a4200bf58d21007f8c690802fc6348411ffa9a4208ff94d21047faa690823fc5348401ffa1a4200ff90d21007fa8690803fc4348411ffa924205ff94921047faa490817fc5248401ffa124205ff90921007fa8490817fc4248401ff9924205ff8c921007fa6490817fc3248411ffa8a4203ff94521047faa29080ffc5148401ffa0a4203ff90521007fa829080ffc4148401ff98a4203ff8c521007fa629080ffc314840bff90a4205fdc852101ffc429080fee214840fffb024207bfd812103ffcc090806fe604840ffeb024207bf5812103ff8c090806fc604840fffa824207dfd412103ffca09081ffd504840fbea824207ff1412103ffe809081ffe404840ffea024207ff1012103ffe609081ffe304840ffe9824207ff0c12102ffe409081ffe204840ffe9024205ff0812101ffe209081ffe104840ffe8824203ff0412101ffeca1080eff6508407ff3284202bf9942101efcca1080a7e6508407feb284206bf5942101efaca108027d6508407fe3284203bf1942101ffec81080eff6408407ff3204200bf9902101f7cc810802be6408407feb204200bf5902101f7ac810802bd6408407fe3204203bf19021037fea81081bfe540840dfeaa04206ff1502101ffec61080eff6308407ff3184200bf98c2101fbcc610802de6308407feb184200bf58c2101fbac610802dd6308407fe3184203bf18c21037fea61081bfe530840dfea984206ff14c21007fe8610803fe4308401fea184200ff10c2102dfcc410817ff520840bff2904205ff5482102ff8a410817ff420840bff2104205ff5082102ff88410817ff3208401f79904205ff8c82102ffa6410817fc320840bf61904203bf9842101ffea21080ffe5108407fea884203ff1442101ffe8210803f74108407ff2084203ff5042101ff8821080ff44108407ff9884203ff8c42101ffa621080ffc3108407ff9084203fbc842101ffc421080ff62108407fe9084203fb4842102fea4210803e52108407ffb004203bfd802101ffcc010806fe6008407fd3004201be9802101ffac010812fd6008407fcb004200be5802101ff8c010806fc6008409ffa804204dfd4021027fca010813fd5008409bea804204ff14021027fe8010813fe4008409fea004204ff10021027fe6010813fe3008409fe9804204ff0c02102ffe4010817ef200840bff1004205ff48021027da4010817fc2008407ff8804203fdc402101ffc201080ffd1008409fa8804203ff04021
  | 1 => 0xffe600c4037f3006203ff5803106dfac01880ffc600c4037e300620dffd403106efea018837fe500c41bfea80620ddf5403106ff8a018837ff400c41bff200620dff5003106ff8801883bff300c41bff180620dff4c031077f86018837ff200c41bff100620dff4803106ff8401880fff100c407ff0806203ff4403101ff82018817ff65c840b7fb2e4205ff99721015fccb90817fd65c84197eb2e4205ff1972102df8cb90817ff64c840b7fb264205ff99321005fcc990817fd64c84017eb264205ff1932102df8c990833ff54c8419ff2a6420cff55321067f8a990817ff63c840b7fb1e4205ff98f21005fcc790817fd63c84017eb1e4205ff18f2102df8c790833ff53c8419ff29e420cff54f21067f8a790803ff43c8401ff21e4200ff50f21007f88790817ff52c840bff2964205ff54b2102ff8a590817ff42c840bff2164205ff50b2102ff88590817ff32c840bff1964205ff4cb2102ff86590833ff51c8407ff28e420cff5472101ff8a390803ff41c8401fba0e4203ff90721007fa839080ffc41c8401fa20e4200ffcc72101ffc6390803fd31c8407fe18e4205ffd832102dfec190817fe60c84037f3064205ff5832105dfac190817fc60c84037e306420bffd432105efea19082ffe50c8417fea86420bdf5432105ff8a19082fff40c8417ff206420bff5032105ff8819082fff30c8417ff186420bff4c32105ff86190817ff20c840bff1064205ff4832102ff8419080fff10c8417fb886420bff8432105ffa219082ff510c8407fe0864203ffd962101dfecb1080ffe65884057f32c4203ff59621055facb1080ffc65884077e32c4203ffd922101dfec91080ffe64884017f3244203ff59221005fac91080ffc64884077e324420affd5221057fca91082bfd5488415fe2a44203ffd8e2101dfec71080ffe63884017f31c4203ff58e21005fac71080ffc63884077e31c420affd4e21057fca71082bfd5388415fe29c4200ffd0e21007fc8710803fd4388401fe21c4207bf58a21057fea510817fe5288415fea944205ff14a21007fe8510817fe4288401fea144205ff10a21007fe6510803ef328840bff1944200ff4ca2102ff86510803ec32884077f30c4203ffd462101ffca31080ffd5188407fe28c4203ffd062101ffc831080ffd4188407fe20c4203ffcc62101ffc631080ffd3188407fe18c4203ffc862101fde4310817f72188407ffb044203bfd822101ffcc110806fe6088407feb044209bf5822101ff8c110806fc6088413ffa844209dfd422104ffca110827fd5088413bea844209ff1422104ffe8110827fe4088413fea044209ff1022104ffe6110827fe3088413fe9844209ff0c22102ffe4110827ef2088413ff1044209ff4822104fda4110817fc2088407ff8844203ff8422101ffa211080ffc1088411ffb
  | 2 => 0x31007fe8518803fe428c401fea146200ff10a31007fe6518803fe328c401fe9946200ff0ca3101dfcc31880fff518c407ff28c6203ff5463101ff8a31880fff418c407ff20c6203ff5063101ff8831880fff318c407ef98c6200fdcc63101ffec11880eff608c407ff3046201bf9823101ffac11884efd608c407fe3046201bf1823109ffea11884f7f508c427ff2846213ff5423109efaa11884ffc508c427ffa046213ff9023109ffa811884ffc408c427ff9846213ff8c23109ffa611884ffc308c427ff9046213ff8823109ffa411884ffc208c407ff8846203fdc423101ffc211880ffd108c427fa8846203ff04231097feca9884aff654c401bfb2a62009fd9531097fcca9880afe654c425feb2a6212bf59531097f8ca9880afc654c425be32a62029f19531007fec898802ff644c401ff3226200bf99131007fac898802fd644c401fe3226200bf19131097fea89884bfe544c425feaa26212ff15131097fea69884bfe534c425fea9a6212ff14d31007fe8698803fe434c401fea1a6200ff10d31007fec498802ff624c401f7b126200bbd8931007fcc498803fd624c401fe3126205bf18931007d8c498802ec624c425ffa926212ff94931097faa49884bfc524c401ffa126200ff90931007fa8498803fc424c401ff9926200f7cc931007fc6498803fd324c401ee9926200ff0c931097fea29880ffe514c425fea8a6203ff14531007fe829880ffe414c401fea0a6203ff10531007fe6298803f7314c407ff18a6203f78c53108ffec098846ff604c423ff3026201bf9813108ffac098846fd604c423fe3026201bf1813108ffea0988477f504c423ff2826211ff5413108efaa098847fc504c423ffa026211ff9013108ffa8098847fc404c423ff9826211ff8c13108ffa6098847fc304c423ff9026211ff8813108ffa4098847fc204c407ff8826211fdc413108ffc2098847fd104c423fa8826203ff0413101ffeca1880eff650c407ff3286202bf9943101efcca1880a7e650c407feb28620fbf5943101efaca188027d650c407fe3286203bf1943101ffec81880eff640c407ff3206200bf9903101ffac818802fd640c407fe3206203bf1903107ffea81883ffe540c41ffeaa0620fff15031085fcc61883fff530c41dff298620fff54c31077f8a618803ff430c41dff2186200ff50c31077f8861880fff620c407ff3106205bf9883101ffac418802fd620c407fe310620fffd483107ffca41883ffd520c41ffe2906200ffd0831007fc8418803fd420c401fe210620effcc831007fc6418803fd320c41dfe1906203bf9843101ffea21880ffe510c407fea886203ff1443101ffe821880ffe410c407fea086203ff1043101ffe621880fdf310c407ff1886203fd8c43101ffa621880fdd310c401fa9886203ffd803101dfec01880
  | 3 => 0xf902821aff881410d7fa40a086bfc2050407ff882821afdc41410d7fc20a086bfd1050435fa8828203ff0414101ffeca2080eff6510407ff3288202bf9944101ffaca20862fd6510407fe3288203bf194410cdfcc820863ff541042fff2a08218ff550410bff8a82080fff6310407ff3188200bf98c4101ffac620802fd6310407fe3188218ffd4c410c7fca620863fd5310431fe2988217ffd0c41007fc8620803fd431042ffe2188203ffd884101ffcc420816fe6210407feb108200bf5884101ff8c420863ff5210431ff2908218ff548410c7f8a42085fff4210401ff2108200ff508410bff88420803ff3210401ff1908200ff4c841007f8642080efe6110407ffa888203ff9444101ffaa22080ffc5110407ffa088203efd044101ffc822080ff64110407fea088203ef50441007ea822080fff60104077fb008203ff9804100dfcc02080ffd601042d7eb008203ff1804100df8c02085bff501042dbfa808216ff940410b7faa02085b7d501042dfe2808217ffd00410b7fc802085bfd401042ffe2008216ffcc0410b7fc602085bfd301042dfe1808216ffc80410b7fc402085bfd201042dfe1008203ffc404101ffc202080ffd1010407fe080820effd97310adfecb98857fe65cc4057f32e6215ff597310adfacb9883bfc65cc4057e32e620effd9331005fec998803fe64cc4017f3266200ff59331005fac99883bfc64cc4017e3266215ffd53310affca998857fd54cc42bfe2a66215ffd4f31077fca798857fd53cc41dfe29e6200ffd0f31077fc8798803fd43cc41dfe21e620effd8b31007fcc598816fe62cc401feb166200bf58b31077f8c598857ff52cc42bff2966215ff54b310aff8a598803ff42cc401ff2166200ff50b31007f8859883bff32cc401ef9966200ff8cb31007fa6598803dd32cc41dfe1966215ffd473101ffca398857fd51cc407fe28e6200ffd073101ffc8398803fd41cc407fe20e620effd8331085fec198843fe60cc4037f3066210ff58331085fac19883bfc60cc4037e3066210ffd4331086fea198843fe50cc421fea866210df54331087f8a198843ff40cc421ff2066210ff50331087f8819883bff30cc421ff1866210ff4c331077f86198843ff20cc421ff1066210ff48331087f8419880fff10cc421ff0866210ff4433101ff8219880fff658c4077fb2c6203ff99631015fccb1880ffd658c4297eb2c6203ff1963101df8cb1880fff648c4077fb246203ff99231005fcc91880ffd648c4017eb246203ff1923101df8c918853ff548c429ff2a46214ff552310a7f8a918846fd638c429ffa9c6214ff94e310a7faa718853fc538c401ffa1c6200ff90e31007fa8718803fc438c407ffb146203ff98a3102dfcc51880ffd628c4017eb146203ff18a310a7fea518853fe528c429fea946214ff14a
  | 4 => 0x803fd43d042ffe21e8217ffd8b41007fcc5a0816fe62d0401feb168200bf58b410bff8c5a087bff52d043dff296821eff54b410f7f8a5a085fff42d0401dfa168200ff90b41007fa85a0803bd42d042ffe2168200ffccb41007fc65a0803fd32d0401fe196821effd474101ffca3a087bfd51d0407fe28e8217ffd83410cdfec1a0867fe60d04037f3068219ff583410cdfac1a085ffc60d04037e3068219ffd43410cefea1a0867fe50d0433fea868219df543410cff8a1a085fff40d0433ff2068219ff503410bff881a0867ff30d0433ff1868219ff4c3410cff861a0867ff20d0433ff1068219ff483410cff841a080fff10d0433ff0868219ff4434101ff821a080fff65904077fb2c8203ff99641015fccb2080f7e65904053f32c8203ff596410edfacb2080f7d65904013eb2c8203ff1964101df8cb2086afd649043bffaa4821dff952410effaa920877fc5490407ffb1c8203ff98e41005fcc72080ffd63904017eb1c8203ff18e410effea720877fe539043bfea9c821dff14e41007fe8720803fe4390401fea1c8200ff10e4101ffec52080ffe629040b7f3148203ff58a41005fac52080ffc629043bffa94821dff94a410effaa520877fc5290401ffa148200ff90a41007fa8520803fc4290401ff9948200ff8ca41007fa6520803fc32904077f30c8203ffd464101ffca32080ffd5190407fe28c8203ffd064101f7e8320803f74190407ffb048203bfd824101ffcc120806fe6090407feb04821cbf5824101ff8c120806fc6090439ffa84821cdfd42410e7fca120873fd5090439bea84821cff142410e7fe8120873fe4090439fea04821cff102410e7fe6120873fe3090439fe984821cff0c2410e7fe4120873fe2090439fe904821cff0824101ffe212080ff71090407ff0848203ff442410e7ea212080ffc1090437ffb2a821bbfd95410dffccaa080afe6550437feb2a821bbf595410dff8caa080afc6550437ffaa2821bff951410dffaa8a086ffc5450401ffb1a8200bfd8d41007fcc6a0803fd6350401fe31a8200bf18d410dffea6a086ffe5350437fea9a821bff14d41007fe86a0803fe4350401fea1a8200ff10d41007fec4a0802ff6250401ff3128200ff58941007f8c4a0816fc6250437ffa92821bff949410dffaa4a086ffc5250401ffa128200efd0941007fc84a0803fd4250401dea128200ff10941007fe64a0803fe3250401fe9928200ff0c9410dffea2a080ffe5150437fea8a8203ff14541007fe82a0803f74150407ff20a8203ef905410d7fec0a086aff6050435ff3028201bf981410d7fac0a086afd6050435fe3028201bf181410d7fea0a086b7f5050435ff282821aff541410d6faa0a086bfc5050435ffa02821aff901410d7fa80a086bfc4050435ff982821aff8c1410d7fa60a086bfc3050435f
  | 5 => 0x823202ff8c119006fc608c849ffa846424dfd4232127fca119093fd508c849bea846424ff14232127fe8119093fe408c849fea046424ff10232127fe6119093fe308c849fe9846424ff0c23202ffe4119017ef208c80bff1046405ff48232127da4119017fc208c849ff8846424ff84232127fa2119093fc108c847ffb2a6423bfd953211ffcca9900afe654c847feb2a6423bf5953211ff8ca9900afc654c801ffb226400bfd9132007fcc899002fe644c801feb226400bf59132007f8c899002fc644c847ffaa26423ff9513211ffaa89908ffc544c847ffa9a6423ff94d3211ffaa69908ffc534c801ffa1a6400ff90d32007fa8699003fc434c847ffa926405ff9493211ffaa499017fc524c801ffa126405ff90932007fa8499017fc424c801ff9926400fbcc93202ffc6499017de324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6403bf1853211ffea29908ffe514c847fea8a6423ff14532117fec09908aff604c845ff3026401bf98132117fac09908afd604c845fe3026401bf18132117fea09908b7f504c845ff2826422ff54132116faa09908bfc504c845ffa026422ff90132117fa809908bfc404c845ff9826422ff8c132117fa609908bfc304c80bff9026422fbc8132117fc409908bfd204c845f69026405ff08132117fe209908bfe104c845fe8826422ff0413202ffeca19016ff650c80bff3286402bf9943202ffaca19082fd650c80bfe3286405bf1943202ffec819016ff640c80bff3206400bf9903202ffac819002fd640c80bfe3206405bf19032107fea819083fe540c841feaa06420ff1503210dfcc619083ff530c81dff2986420ff54c32077f8a619003ff430c81dff2186400ff50c32077f88619016fe620c80bffa906405ff9483202ffaa419017fc520c80bffa106405ff9083202ffa8419017fc420c80bff9906405f7cc83202ffc6419017ee320c80bfe9906405f74c832007da6419017ff610c80bff3086403bf9843202ffac219002fd610c80bfe3086420ffd4432107fca219083fd510c841fe2886405ffd803202dfec019017fe600c8037f3006405ff580320fdfac019017fc600c8037e300641fffd40320fefea01907ffe500c83ffea80641fdf540320fff8a01907fff400c83fff200641fff500320fff8801903bff300c83fff180641fff4c032077f86019017ff200c80bff1006405ff4803202ff8401907fff100c83fff080641fff440320fff8201905fff65d043d7fb2e821eff99741015fccba087b7e65d04053f32e821eff597410f5facba08037d65d04013eb2e8217ff19741015f8cba087bff54d042fff2a6821eff553410bff8a9a085fff63d0401ff31e8200bf98f41007fac7a0802fd63d042ffe31e821effd4f410f7fca7a087bfd53d043dfe29e8217ffd0f41007fc87a0
  | 6 => 0xbff3288402bf9944202efcca2100a7e651080bfeb288428bf5944202efaca210027d651080bfe3288405bf1944214dfcc8210a3ff541082fff2a08428ff550420bff8a821017ff631080bff3188400bf98c4202ffac621002fd631080bfe3188428ffd4c42147fca6210a3fd5310851fe2988417ffd0c42007fc8621003fd431082ffe2188405bf9884202ffea421017fe521080bfea908405ff1484202ffe8421017bf421080bff2108405fb9084202ffa8421017bd4210801f6a108405ffd844202ffcc22100efe611080bfeb088400bf5844202ff8c2210a3ff5110851ff2888428ff54442147f8a221017ff601080b7fb008405ff9804200dfcc021017fd601084f7eb008405ff1804200df8c02109fff501084fbfa808427ff9404213ffaa02109f7d501084ffe2808417ffd004213ffc802109ffd401082ffe2008427ffcc04213ffc602109ffd301084ffe1808405ffc804202ffc4021017fd201080bfe1008427ffc404213ffc202109ffd101084ffe080840effd9732135fecb9909bfe65cc8057f32e6426df99732014fccb9909bfd65cc84d7eb2e6400df59732004facb9903bfc65cc8057e32e640effd9332005fec999003fe64cc8017f3266400ff59332005fac99903bfc64cc8017e3266426ffd5332137fca99909bfd54cc84dfe2a66426ffd4f32077fca79909bfd53cc81dfe29e6400ffd0f32077fc8799003fd43cc81dfe21e6426ffd4b3202ffca59909bfd52cc80bfe2966400ffd0b3202ffc8599003fd42cc80bfe216640effd8732007fcc39900efe61cc801feb0e6400bf58732077f8c39909bff51cc84dff28e6426ff54732137f8a39903bff60cc8437fb066421ff9833200dfcc199087fd60cc8437eb06640eff1833200df8c199087ff50cc843bfa866421ff9433210ffaa1990877d50cc843fe2866421ffd033210ffc8199087fd40cc843fe206640effcc33210ffc6199087fd30cc81dfe1866405ffc833210ffc4199087fd20cc80bfe1066421ffc433210ffc2199087fd10cc843fe0866405ffd963202dfecb19017fe658c8057f32c6405df99632014fccb19017fd658c84b7eb2c6405df59632004facb19017fc658c80b7e32c6405ffd923202dfec919017fe648c8017f3246405ff59232005fac919017fc648c80b7e3246425ffd523212ffca919097fd548c84bfe2a46422bf58e3212ffea719097fe538c84bfea9c6425ff14e32007fe8719003fe438c801fea1c6400ff10e3202dfcc519017ff528c80bff2946405ff54a3202ff8a519017ff428c80bff2146405ff50a3202ff88519017ff328c80bef9946400fbcca3202ffec319017fe618c8077f30c6405ff58632005fac319017fc618c84bffa8c6425ff9463212ffaa319097fc518c80bffb046405bfd823202ffcc119006fe608c80bfeb046424bf5
  | 7 => 0xa105fff63d0801ff31e8400bf98f42007fac7a1002fd63d082ffe31e842effd4f42177fca7a10bbfd53d085dfe29e8417ffd0f42007fc87a1003fd43d082ffe21e842effd4b4202ffca5a10bbfd52d080bfe2968417ffd8742007fcc3a100efe61d0801feb0e8400bf587420bff8c3a10bbff51d085dff28e842eff54742177f8a3a105fff60d08537fb068429ff9834200dfcc1a10a7fd60d08537eb068417ff1834200df8c1a10a7ff50d0853bfa868429ff9434214ffaa1a10a77d50d0853fe2868417ffd034214ffc81a10a7fd40d082ffe2068429ffcc34214ffc61a10a7fd30d0853fe1868405ffc834214ffc41a10a7fd20d080bfe1068429ffc434214ffc21a10a7fd10d0853fe0868405ffd964202dfecb21017fe65908057f32c8405ff5964216dfacb21017fc659080b7e32c842abf5924216ffea9210b7fe549085bfeaa4842dff1524202ffec721017fe63908017f31c8405ff58e42005fac721017fc639085bffa9c842dff94e4216ffaa7210b7fc5390801ffa1c8400ff90e42007fa8721003fc439080b7f3148405ffd4a4202ffca521017fd529080bfe2948405ffd0a4202f7e8521003ef429080bffb0c8405ff9864201dfcc321017fd61908017eb0c8405ff1864216ffea3210b7fe519085bfea8c842dff1464202ffec121016ff609080bff3048401bf9824202ffac1210b2fd609080bfe3048401bf18242167fea1210b37f5090859ff284842cff54242166faa1210b3fc5090859ffa04842cff90242167fa81210b3fc4090859ff984842cff8c242167fa61210b3fc309080bff9048405fbc824202ffc4121017fd2090859f69048405ff08242167fe21210b3fe1090859fe884842cff0424215ffecaa10aeff6550801bfb2a84009fd954215ffccaa100afe6550857feb2a842bbf5954215ff8caa100afc6550857be32a84029f1954215ffea8a10affe5450857feaa2842bff15142007fec6a1002ff6350801ff31a8400ff58d42007f8c6a1002fc6350857ffa9a842bff94d4215ffaa6a10affc5350801ffa1a8400ff90d42007fa86a1003fc4350857ffa928405ff9494215ffaa4a1017fc5250801ffa128400fbd094202ffc84a1017be4250801ffb0a8400bfd8542007eec2a1002f76150801ff30a8400ff58542007f8c2a100efc6150801fa30a8400bd1854215ffea2a10affe5150857fea8a842bff14542157fec0a10aaff6050855ff3028401bf98142157fac0a10aafd6050855fe3028401bf18142157fea0a10ab7f5050855ff282842aff54142156faa0a10abfc5050855ffa02842aff90142157fa80a10abfc4050855ff982842aff8c142157fa60a10abfc305080bff902842afbc8142157fc40a10abfd2050855f69028405ff08142157fe20a10abfe1050855fe882842aff0414202ffeca21016ff651080
  | 8 => 0xf58a43077f8c5218d7ff5290c6bff2948635ff54a431aff8a52183bff6190c01ff30c8603bf98643007fac321802fd6190c1dfe30c8635ffd46431affca3218d7fd5190c6bfe28c860effd824318dfec1218c7fe6090c037f3048631ff5824318dfac12183bfc6090c037e3048631ffd424318efea1218c7fe5090c63fea848631df5424318ff8a1218c7ff4090c63ff2048631ff5024318ff8812183bff3090c63ef9848631ff8c24318ffa61218c7dd3090c1dfe1848631ffc824318ffc41218c7fd2090c63fe1048631ffc424318ffc21218c7fd1090c63fe0848634ffd95431a5fecaa18037f6550c013fb2a8634ff99543015fccaa18d3fd6550c697eb2a8634ff19543015f8caa18d37c6550c053e32a8634ffd51431a7fca8a18d3fd5450c69fe2a28634ffd4d431a7fca6a18d3fd5350c69fe29a8600ffd0d43007be86a1803fe4350c01df21a8600ffd8943005fec4a1803fe6250c01feb128600ff1894302df8c4a18d3ff5250c69ff2928634ff549431a7f8a4a1803ff6150c017fb0a8600ff98543007fac2a1803fc6150c077e30a8634ffd45431a7fca2a18d3fd5150c69fe28a8633ffd814319dfec0a1803fb6050c017db028633ff9814300dfcc0a18cffd6050c677eb028633ff1814300df8c0a18cff86050c037c3028633ffd414319efea0a18cffe5050c67fea828633df5414319ff8a0a18cfff4050c67dfa028633ff9014319ffa80a18cfbd4050c67fe2028633ffcc14319fbe60a18cffe3050c67fe9828633f74c14319ff860a18cfff2050c67ff1028633ff4814319ff840a18cfff1050c67ff0828633ff4414319ff820a183bff6510c617fb288630ff99443015fcca218c37e6510c053f3288630ff59443185faca218037d6510c013eb28860eff19443015f8ca218cafe6410c61ffaa08617ff95043187faa82185ffc5410c637f3188630ffd4c43077fca6218c3fd5310c1dfe2988617ffd0c430077e862183bfe4310c01ef2188600ff50c430077a8621803dd4310c01cea18860effd8843007fcc421816fe6210c01feb108600bf58843077f8c4218c3ff5210c61ff2908630ff54843187f8a42183bff6110c01ff3088603bf98443007fac221802fd6110c1dfe3088630ffd4443187fca2218c3fd5110c61fe288860effd804317dfec0218bffe6010c037f300862fff5804317dfac02183bfc6010c037e300862fffd404317efea0218bffe5010c5ffea80862fdf5404317ff8a02185fff4010c5fff200862fff500430bff8802183bff3010c5fff180862fff4c043077f860218bfff2010c5fff100862fff4804317ff840218bfff1010c5fff080862fff4404317ff8202185fff65d085d7fb2e842eff99742015fccba10bbfd65d085d7eb2e8417ff19742015f8cba10bbff54d082fff2a6842eff553420bff8a9
  | 9 => 0x5c00c01002c00000001401000c00400c01800000400800400000000800000000c01c00000400002400800400000c01400800000401400000000000002000c06000c00001800406c02801400402405c01001000000400000400404000001804c00001401400c00403c00000000000800000001402402800c00c05801000c04801001001c00001801c03400800003400c02c00800400c00000000801c00004800c00000405c00400000400401401400000401401000c0100140240c401800801c00000001000000800800c00001000000400003800000000000800000800000002400402000400800c02c00800400c01001c00800801002401001000801401800000401000000000800c01001c03c00400c00001003005804c00000400000400000003800004400006806401800400000001400401402400002803400000002c00400c02000003c00000400c00000001401400c00003000000800c00000000800001001804c01002c01c05001800000400000000800000804c00402800000004802803000000400400c01000c00808800000000400000400400c00802000800400c00000400800800002001800000804802800002400401001801401001801800000401000402c00400000c00402000009c00802000000004000000001002400400000000000000400400001402400000800001400000000000000800002401800800000000800c00401c00000c00001001401c00c02400000000400000007000001400000001800000c0080000000000080040000000140100380000180080080040000100540000280040000002fffb2e8636bfd97431b7fccba180afe65d0c6dfeb2e8636bf597430bff8cba180afc65d0c6dffaa68617ff953431b7faa9a185ffc54d0c6dffa9e8636ff94f431b7faa7a18dbfc53d0c2fffb168600ff98b4302dfcc5a1803fd62d0c017eb168617ff18b431b7fea5a18dbfe52d0c6dfea968636ff14b430bffec3a1803fe61d0c077f30e8600ff58743005fac3a185ffc61d0c6dffa8e8636ff947431b7faa3a18dbfc51d0c2fffb068632bfd8343197fcc1a1806fe60d0c65feb068632bf583430bff8c1a1806fc60d0c65ffa868632dfd4343197fca1a18cbfd50d0c65bea868632ff143430bffe81a18cbbf40d0c65ff2068632ff503431977a81a185ffc40d0c65ff9868632ff8c343197fa61a18cbfc30d0c65ff9068632ff88343197fa41a18cbfc20d0c65ff8868632ff84343197fa21a18cbfc10d0c1dffb2c8635bfd96431affccb2180afe6590c6bfeb2c8635bf59643077f8cb2180afc6590c677eb248635ffd52431affca9218d7fd5490c6bfe2a4862fbf98e431affea72183bfe5390c6bfea9c860eff14e43007fe8721803bf4390c01efa1c860effd8a43007fcc521816fe6290c01feb148600b
  | 10 => 0x2d10000208421230807c00000000000006243e805a83700007072e3956c5a22ba3a096b4c983f100000000003451090980b3c62f3a21384f3249419f000000000000019c856e0dd321163495200000019e84c679514980008f800036080002ea0000198000000000349941424a2f92250040e1c3cc3b10290f16586260871056a2dc3a6888c4d82b03a18f483565cc00c131405a0000001e8c4c415f1720c2437a0000249e5c55a08c17706ccc2816126f1f78bb450f33d8000ef63152b1075c0006530000000f668000f39488e1a49300000007c800009b1f040000001bf8cfc6b60190cc05045e677a00003c479e6890000000c240003f611ec0000000da009c0000000508000856000163800000048314d85bc9480002058b34d1a00030b041863c40100006e80000001879f80cda5270001f4c0000001c000000e20000000000000000079000006c000000000000000027485300004e31fe9c2000000b1701fcc4d05003241e589083e710980005120000000da459413a0d31a780b47c41d40ae086e0542da13d80d261f361121400075b000000000011d38d800044a13518108f42042e32c39dd000000017f1048e122760000000f300001c9800056c0000000d60ffa10c10a0000b6c39d000045cc507ef3e71df092e4c80001b0c5f43c323b103800023c0001c6811a31101e1c50ace1821430d6400000036700006880000000000d066dd20a1d640005951a41c603806cd22d000087061e122201ca6677105180001d051b1bb000013600038999c06f80002160000976626000000400000401800800000000001001800001404000400c02000000c02000c01800400000001002402000400401000c00801400400c00c01000000400000c00400000c00409802400400000400804c02c00800000c00003800000401800804c00000800001c00400403801000005000002005400001400401805401c00000000400c00000400800800005401c01000000405804800001400000c0080000040080280300d000000403400000002000c01401c00000c00c00000000801c02400001802c00001400009800400000c00c00400801400002002001002000004402401403800001801000001400000400801000004000801000000000000000404400401801406800c00002000003c00000000802000000000005803402800000403402c00000802407c00000000400c0d804001c01400400801000000c01c00c01401c00400002c00c00000800000000800000405801005c01000400000401400000001400c02800400401402c00000000000401c00400001801400801400400000004000800000403800c00002001401000000400c02805c00c02403000c00800805806001000000000003000001c00001802401802c00800000402800001c008014024004
  | 11 => 0x4d7014e21900002ba81d00000000005df0001a040000000000bd093e0000ca8000fc61800c616700360002fb80004326380fe8d48000430000000000000000001a094675519e119c76860e000020ccb02871bc03a8bd80003af8000000000000000098e17c00000004e400025d0000ef227a10c1e0c2da00009a000096c61b000058c0000002331bd0b5c7600000000000000000108853459200003f40000003799a680000001f6800000065a0df1da80006841860f8000037d0000000d4865f2e083bc258038000163ce0257d15f13d0bcc552106000081805013d800069e0000e40000f7e73e2340508000000000175461c5070f181807940002a39a2000081834100fcb7e6bb0000da901800000000003d00000001584000000000009439c64d00017080000000379d385b20000000ba8e0c0000001cf4f1a74022e0d704220002fe9268266000353864000000000012ac00026d20780000000863039310a3448d3328fd41f80003218000c0a6c00ee9d9469a4b0000126458a3030de018c00053a39280000000002e51f9800012b00000000005f33c79cfc3d60000010000a30000000000078c00000000000005d90f8109453e334071868099e0003d900004ae08b30480008ba00028e00000007ae2f2800000000028a9c900007e41730ecc000000000000000000000000005e425600000007a800000000000007b72599f9c36c7fc31a000000071200000000000002c400008e057e204800000042a1a180000000000000000b92000000000000000007b8000a9c7523b39494d38000000000000078e00017445be0000b98e5c0ca02000000006501131380000a020003c997b8d227113f80000f9e0f90290000afe0000000000000000325202848600000016402ac5d202b0794ecc2cf29912f400030b36a98a808e63013a8dd0eb43b832a1b503dc71d0728c2825e7503c805709e61d500009089ee00000001740000001508d0400059d0000000a4866800000f446263e0001ee83fc00007f800061a00015c8000000000000000095a3542960a80b1c17100000000f62512a483d800c71c25796600007563f70e84f026660c312886706fd08d8f54e701a33fc17100be1db00005f8cae00007c1434000208127000000080e0000000cd40000001e706202af1280000a5a76830798440066ed00015ecd6e0ad1b815d46761f500000003140000001d840001a10000e340105ab00000000001070000000ff222d2de11cce447943e61ff80001a40b6000000000000000007ac000000000047200000019ccd30126330039819037e0780208630165000110090e066000036800081136e0b4000051f275000000047100000009fc0000001d08af0011102013844c7e933113903103fc23a0b78a040db0000984bac1460d61f203c25a620206e000002a
  | 12 => 0xf159005cad818d3fd9608b144d40ee03080000001011bb88aa2c11e886ec3640000000000b7a00000000000006f227690e433a54500000008be2c43590000694000000000000049e1d7030ce5446326190f80006f13d580000004350000cb4000000000048ccfe4f034c85e80000401cf03249a27b40000000ae80000000cdc00050e24100004401180e7971800007d3ef8e1400050327f80003ee04f3c2800089c2cc17d86d40007893da9dcceda5163428f406e42d60f1051464a4e63c01578bf600037b00009f624a1531188d1c7331ec12e421c16804b209400028b2321bd455600020e0fd09361f92c192f086c00007100005226d93f11c7cc6e3072c981900007e101c9b8c0004e211b054c12e39900000009d00001411014bf04aa0000724d5c02300000c81280001ec94845ba0000b00dbc89e000000199cf182cb07018b80d600000000000002220141bec6e60000b20000fd60bc0000b4c0000e43a9825470e74815700140002f10000170708000000102040c0000c8979d04248e2f695dc34467d00002c80007ac00009980000001f1000000000000000000003cb35a8b5000000024e000000007a0001be400062500000000001da22b954c0003aa1bd83b44062070001948df800008f959000000000001140bc0000000000f5a6b3000000088e0002be000000008000011c83a681900000000005130000000000000000000000000035b0000000000000000103e32632813703e80002a400b80005440000000acc0000000bd501a2c633200000fc3860000000e084a03970f84f0e5fc1078550de00001540cd4f7a24620f99245061051bd000064e08109402f8dde0ec3de1ddc00060430300000006df0001aa8c106be2210e0800016700004001e819f1d0000007c29808d0001012735000107417e5f533785540000770990000bfe1cd4118000bb66401e70e0cf942d52601f6844800032e98c484032f0db93c803c351142000001a08900002e00007463a59e840000f50001c0c0004103d486700001a800000008de33d26c85ec41c70b24509a80006bd0e100000000001a3058842c72103c96449243650b70f4c7d229c000000000045335008e0e9219938610a0c2612736d9d14c721763628e384ce2c916d1808d3a3312a81d306ea6d33d314d8aaa47825f98b41ce3a50258340d904ef05109aca125be18e942c26232310b814d02c18440d02200007d6068994476a63f3279f4400000040110c43cc09d0481b1cb626c6000052c00000034900000004fd05a0b38c747692888544b122bd00000000007570001e080000000000ce4d4400000007b4f76573394816408804837f06e484e00013990bc5480001900000ab0091104969c3f61d20eb000000016a2d60d8000000020392b8bd044900018400e00000001194a2e356000139
  | 13 => 0xdce4e3f30001ad02024912c594c4fda6ad2d2800082c53d00b00000000001dd80009e281b18a1888a687fa40b8c0090013730c06c4efa15806f1a5800056b2a688d060c77534802706d862c3e38f7030e29229c0b608742bc3930a74f0810f13e19380fe68728200002763941d2013083000026596bcb285f000019f005e31c40200005d800017800003be79201d800054a5e400007cc9021bf00003a4b5015e07d800008c0000b4872c00000017b052800056e1bb941832c41e09f1ab0dee1d42ff000000010d33a00001605e20000000cdc0000001db8bc02000000ee8d464f91478fe40000002539d8c0000000a000000000000000a30f480d8014a0900006b100008b001800000000000004890950acc0000d20090278920400000065caba1a712e91107ca7762509c00d980d920506b4000000000152c19820b1f58000e9435a2c219c4d964be3119a301a612406681d892c3af01b81f04d247725a9aa4d4a0fa3d509707ec55a35d0350f444cc1b5871c15469b000053427a4d60208c7c01e00013e9a5c8fa35d14f2040d0c3c42d18b842326ca4100f7cbf41aa03094507340d517e98a40a241b1cf937c0f07c0364845427e59904287a400040d2db97406021e40000a582522e73121978e680002f51ee00da36802690f4000000000202c00024b00000000003241d39c7807400000007800005d829e1d9000003023d1ba4d3e00038c9b900001ca000000084831325897505f01520e09ba000064639012b0ae25b9000158ca8600011980000000003a3832846e81e3198b5c568000000182c0004a83978c146083c100000000000001601b68c8209813217d03d80bd00094ac000000000123cade000000159400060d02c1aa01962900fd000000000000000000000003e115c81324150000000c7a7f700000000007510001a84000000203000000000000000001664d713782bc8047280000484c344581d90eb074c0000398000c405dc0000e400000000fe0ed84fc3f2000208850a459084800000000020b8ac40346e50968e54a1800000015e8000110000153cb3e000000087cb5281400000009b04480001a008860000000d98000075184056400000000000001ac0000000f000000000001cc4b800003581f70c3a01d17f8878f103c800014fc4908151dc88f8f3e7d706b9c5400025332a800068400039b0aa4c962ef27d00002602280000930a6e000000000000000000014f89ce6e100008b86dc32b246191cd9e581129030078a5793759de01be0000000000bd2000000200c0004f531915046c200000000000000001af000079229514c85c8f8c0001618000aa80c10c99464b3604329a978cefe0ba00019e4e720c43e48c6c0480a63479784b640ab0e88000000000063000000006e00013807bc6f8062893c99c0001ff0524fca27
  | 14 => 0x1f71964f4a27840e1cc86c67e800000006be00012691f80003400001af04927ff0bf8000dac58c0000000e2079a36b80009a416b05293b8b9a6ec3961130f6c3d70c58db4dc454a0001c5c9b4170334908c0002450ca2048dbc42927c0084544770298000000022a32d91b8000000000000010e68b110800000080f36895c00000c71df815c74400714701b0ab841a3878bacfb200026d8d8817600014b80000000000000cb800000000000000000001f6000062c0000e600000000003a7800000019e04902dc31c2d228f07bc84c000050080489a5971ff82a0b600003bf0000c38758230050c000528000000000000020896148ac26e00000000000930000f8c3fe0003e909d000000000000000000003fa1b9c436000000000099a3bd0001dac00000000001088a438b3e18000dcc00000000008760001a70ba000000039e00003a066b3109a987cc4131450000ea800010d00000000001d8800000033600000005f8000000000000034b3c509c477c0000000000f0c5ce00481c80c40002b680000008010c78d5cf3a2ac0001fc800000000006940001ea15380007300000001cec93a0002199a500583f81400fec78e347000122c30251208a1564ede06731a800000000000000007122a312a9ef8b9e00017101d06980001ee85dc51a0003cd80000005760250e047145b300000000000f30001e789640000000e708ea63617487600380001de000000019200000000000001f80000a5202612a0c648964692681abcb7000000017c40003b01611854ed80040000000000434000177806a2322440994b6a0003360000fea14729d98accec0001cb17ac9301c608880000003fa3851294f5031734a9f2c8d600010a95a07b40002fc8028a5412000013540003ab2758050b4831a2dd1f6c0001de00000000000000a2130871021d0001b1035e0001768f08fec00000000000007b10a411a88bc808057172cb8a2f724a88ec000000345000000025f2b50fa800054c00000000620000001658b3422f10e1cc0722000140854000015b2eb8c88f4e1c329c823c6a647f000042897000011d00004bc00020c80008d83cd2a300006666d812380000004410000dc46605083d79720ba64a60bea0143ec81338b1828cac2bf30b9b80f8a18500000000000ce07f0000f9a09a297800057651000010b8dd423f1729ce8c0044533f0c841c20ac2901428bec138330958000079100016a8000000293000019e0000c49ec09922292f907e0cee00000002e400064516401540003323f5016cc1800009e0000e565dd194900cfe26d01cd8a503b24540b3197029e43f118045869219a3318054000000000000000035022800004f20003af1be800000029180d03601570111500cf00000bc88140000002d080ac00032a2a8955838a3ef3d0000090c0a70350f
  | 15 => 0x77000096e4c604708ac2e81780001cb43364dd09c8000b0064400008d40005693691f74fa8000265000001c2db00000005541f20000000c025c312c8000e4638f00000000001a9000042000063b000000000000000010b400000005b189ccea3793019bfc13e3643e80eb48b61123dc83ac6ce70512c000041418300000001522100910edcfaa4b42a11d709f812e26998f002625b0589ae44820000000e3000052e00017bc2386ab00011e44ee1ae0ad1afc0005a01d19144e040002af8ea40000000000e4800000008f090000022721e11b43e225a30ca01810855728e842ceba32c14416ec41a00008193b06aa3db3ec111800008a3b91cdc6740
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x960cc8211ff6f50cc8211ff6d50cc821207e710cc8211ffe510cc82101df576d0421006f576d04211f77675d04210077575d042101f7665d042101f7565d042101df674d042101fb674d042101ef764d042101fb664d0421006f564d042101fb564d0421006b564d042101fd663d042101fd563d04211e5f772d04211e5f572d04211e6f662d042101fe662d04211e7b742d04211e7b542d0421007e732d04211e7e432d04211edf770d04211edf570d042101ff260d042101ff160d04211df7750d04211df7550d04211e7e720d04211dfe520d042101fe7764842101de77648421006e776484211d7e775484210076775484211cfe675484211d7e575484211cfe475484211cf64754842101fe7654842101fe6654842101f66654842101fe5654842101f65654842101fe46548421007e77448421007e67448421007e57448421007e4744842101fe7644842101fe6644842101fa6644842101fe5644842101fa5644842101fe464484211cfe754484211cfe654484211cfe554484211cfe45448421007e77348421007e67348421007e57348421007e4734842101fe7634842101fe6634842101fc6634842101fe5634842101fc5634842101fe463484211cfe753484211cfe653484211cfe553484211cfe45348421007e74348421007e64348421007e54348421007e443484211c7e770484211c5e770484211bfe670484211c7e570484211c5e570484211bfe4704842101fe7604842101fe6604842101fe2604842101fe5604842101fe1604842101fe460484211bfe750484211bf6750484211bfe650484211bfe550484211bf6550484211bfe450484211bfe740484211bfe640484211bfe540484211bfe440484211bfe730484211bfe630484211bfe530484211bfe43048421006fb7558021006fa75580210067a7558021006f97558021006797558021006f87558021006fb7458021006fa7458021006f97458021006f87458021006fb5458021006fa5458021006f95458021006f85458021006fb7358021006fa7358021006f97358021006f87358021006fb5358021006fa5358021006f95358021006f85358021006fb4358021006fa4358021006f94358021006f8435802102efb725802102efa725802102ef9725802102ef8725802102efb525802102efa525802102ef9525802102ef8525802102efb425802102efa425802102ef9425802102ef8425802102efb325802102efa325802102ef9325802102ef8325802101efb715802101efa715802101ef9715802101ef8715802101efb515802101efa515802101ef9515802101ef8515802101efb415802101efa415802101ef9415802101ef8415802101efb315802101efa315802101ef9315802101ef8315802101efb215802101efa215802101ef9215802101ef82158021
  | 1 => 0x8c2101cfe7158c2101cfd7158c2101cfc7158c2101ede3158c2101edc3158c21004ff7058c2100cfe7058c21004fd7058c2100cfc7058c210067f5058c210067d5058c21006df3058c21006de3058c21006dd3058c21006dc3058c2102eef2058c21006ed2058c2101ef71058c21006f51058c21006df7558c21006de7558c21006dd7558c21006dc7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c21006de5458c21006dd5458c21006dc5458c2102edf7258c2102ede7258c2102edd7258c2102edc7258c2102ecc7258c2102edf5258c2102ede5258c2102edd5258c2102edc5258c2102edf4258c2102ede4258c2102edd4258c2102edc4258c2101edf7158c2101ede7158c2101edd7158c2101edc7158c2101edf5158c2101ede5158c2101edd5158c2101edc5158c2101edf4158c2101ede4158c2101edd4158c2101edc4158c2101edf2158c2101ede2158c2101edd2158c2101edc2158c21006df7058c21006de7058c21006dd7058c21006dc7058c21006df5058c210065f5058c21006de5058c21006dd5058c210065d5058c21006dc5058c21006df4058c21006de4058c21006dd4058c21006dc4058c2102edf2058c2102ecf2058c2102ede2058c2102edd2058c21006cd2058c2102edc2058c2101edf1058c2101ed71058c2101ede1058c2101edd1058c21006d51058c2101edc1058c210bcff76d0c2101cfe76d0c21004fd76d0c2101cfc76d0c211b67e65d0c210067d65d0c210bebe64d0c21006bd64d0c21006de63d0c21006dd63d0c2102dee72d0c21005ed72d0c21196fa60d0c21074ff7690c2101cfe7690c21004fd7690c2101cfc7690c211ae7e6590c210067d6590c21006be6490c21006bd6490c21076de6390c21006dd6390c2101df67190c21005f57190c2118efa6090c21004ff7650c2101cfe7650c21004fd7650c2101cfc7650c210057f7550c210357c7550c211a67e6550c210067d6550c21006be6450c21006bd6450c21006de6350c21006dd6350c21005ef7250c2102dec7250c21005f77150c2101df47150c21005fb7050c21025f87050c2119efa6050c21074ff7610c2101cfe7610c21004fd7610c2101cfc7610c210357e7510c210057d7510c211867e6510c210067d6510c210bebe6410c21006bd6410c21076de6310c21006dd6310c210079d4310c2117efa6010c2102ded76cc821006ed76cc8212176e75cc8210076d75cc82102f6e65cc82102f6d65cc82102fae64cc82102fad64cc82102dee73cc82102fce73cc82102eef63cc82102fce63cc821006ed63cc82102fcd63cc821006cd63cc821205ef71cc821205ed71cc821206ee61cc82102fe661cc821207e441cc821207cf31cc821207cd31cc82120def70cc82120ded70cc82102fea60cc82102fe
  | 2 => 0x6bd5359021006bc535902102ebf725902102ebe725902102ebd725902102ebc725902102ebf525902102ebe525902102ebd525902102ebc525902102ebf325902102ebe325902102ebd325902102ebc325902101ebf715902101ebe715902101ebd715902101ebc715902101eb4715902101ebf515902101ebe515902101ebd515902101ebc515902101ebf315902101ebe315902101ebd315902101ebc315902101ebf215902101ebe215902101ebd215902101ebc2159021006bf7059021006be7059021006bd7059021006bc7059021006bf50590210063f5059021006be5059021006bd50590210063d5059021006bc5059021006bf3059021006be3059021006bd3059021006bc305902102ebf205902102eaf205902102ebe205902102ebd2059021006ad205902102ebc205902101ebf105902101eb7105902101ebe105902101ebd1059021006b5105902101ebc1059021074ff7598c21014fe7598c21004fd7598c21074fc7598c210bcfe7498c21004fd7498c2101cfe7398c2101ede7398c21006df5398c21076de5398c21006dd5398c21076dc5398c2102cfe7298c2102cfc7298c2102ede3298c2102edc3298c2101cfe7198c2101cfc7198c2101ede3198c2101edc3198c21074ff7098c2100cfe7098c21004fd7098c2100cfc7098c210067f5098c210067d5098c21076df3098c21006de3098c21006dd3098c21076dc3098c21076df7598c21006de7598c21006dd7598c21076dc7598c21076df7498c21006de7498c21006dd7498c21076dc7498c21006df5498c21006de5498c21006dd5498c21006dc5498c2102edf7298c2102ede7298c2102edd7298c2102edc7298c2102edf5298c2102ede5298c2102edd5298c2102edc5298c2102edf4298c2102ede4298c2102edd4298c2102edc4298c2101edf7198c2101ede7198c2101edd7198c2101edc7198c2101edf5198c2101ede5198c2101edd5198c2101edc5198c2101edf4198c2101ede4198c2101edd4198c2101edc4198c2101edf2198c2101ede2198c2101edd2198c2101edc2198c21076df7098c21006de7098c21006dd7098c21076dc7098c21006df5098c210065f5098c21006de5098c21006dd5098c210065d5098c21006dc5098c21006df4098c21006de4098c21006dd4098c21006dc4098c2102edf2098c2102ede2098c2102edd2098c2102edc2098c2101edf1098c2101ede1098c2101edd1098c2101edc1098c21004ff7558c21014fe7558c21004fd7558c21014fc7558c21004ff7458c210bcfc7458c2101cff7358c2101edf7358c21006df5358c21006de5358c21006dd5358c21006dc5358c2102cff7258c2102cfe7258c2102cfd7258c2102cfc7258c2102eec7258c2102cec7258c2102ede3258c2102edc3258c2102eec3258c2101cff715
  | 3 => 0xd315942101e7c315942101e7f215942101e7e215942101e7d215942101e7c21594210067f70594210047f70594210067e70594210067d70594210047d70594210067c70594210067f40594210067e40594210067d40594210067c40594210067f30594210067e30594210067d30594210067c305942102e7f205942102e7e205942102e7d205942102e7c205942101e7f105942101e7e105942101e7d105942101e7c10594210bcff7599021014fe7599021004fd75990210bcfc759902101cfe749902101ebe7499021006bf54990210bebe5499021006bd54990210bebc5499021074fe7399021004fd739902102cfe729902102cfc729902102ebe429902102ebc429902101cfe719902101cfc719902101ebe419902101ebc41990210bcff709902100cfe7099021004fd709902100cfc70990210067f50990210067d50990210bebf4099021006be4099021006bd40990210bebc40990210bebf7599021006be7599021006bd75990210bebc75990210bebf7399021006be7399021006bd73990210bebc7399021006bf5399021006be5399021006bd5399021006bc539902102ebf729902102ebe729902102ebd729902102ebc729902102ebf529902102ebe529902102ebd529902102ebc529902102ebf329902102ebe329902102ebd329902102ebc329902101ebf719902101ebe719902101ebd719902101ebc719902101ebf519902101ebe519902101ebd519902101ebc519902101ebf319902101ebe319902101ebd319902101ebc319902101ebf219902101ebe219902101ebd219902101ebc21990210bebf7099021006be7099021006bd70990210bebc7099021006bf50990210063f5099021006be5099021006bd50990210063d5099021006bc5099021006bf3099021006be3099021006bd3099021006bc309902102ebf209902102ebe209902102ebd209902102ebc209902101ebf109902101ebe109902101ebd109902101ebc1099021004ff7559021014fe7559021004fd7559021014fc755902101cff745902101ebf7459021006bf5459021006be5459021006bd5459021006bc5459021004ff7359021074fc735902102cff725902102cfe725902102cfd725902102cfc725902102ebe425902102ebc425902101cff715902101cfe715902101cfd715902101cfc715902101ef4715902101cf4715902101ebe415902101ebc415902101ef44159021004ff705902100cfe7059021004fd705902100cfc70590210067f50590210067d5059021006bf4059021006be4059021006bd4059021006bc405902102eef2059021006ed205902101ef71059021006f51059021006bf7559021006be7559021006bd7559021006bc7559021006bf7359021006be7359021006bd7359021006bc7359021006bf5359021006be5359021
  | 4 => 0x8d21074ff7518d21014fe7518d21004fd7518d21074fc7518d210bcfe7418d21004fd7418d21076de7318d2102cfe7218d2102cfc7218d2101cfe7118d2101cfc7118d2121eee2118d2121eec2118d21074ff7018d2100cfe7018d21004fd7018d2100cfc7018d210067f5018d210067d5018d21006de3018d21076dc3018d210bcff76d0d21004fe76d0d21004fd76d0d210bcfc76d0d210067f65d0d211b67c65d0d21006bf64d0d210bebc64d0d21074ff7690d21004fe7690d21004fd7690d21074fc7690d210067f6590d211ae7c6590d21006df6390d21076dc6390d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d210457c7550d210067f6550d211a67c6550d21006bf6450d21006bc6450d21006df6350d21006dc6350d21005fb7050d2103df87050d21074ff7610d21004fe7610d21004fd7610d21074fc7610d210457e7510d210057d7510d210067f6510d211867c6510d210079d4310d2102dee7210d21005ed7210d2101df67110d21005f57110d2101cfe76d09210067f65d09211767c65d0921006bf64d09210bebc64d092101df671d0921005f571d092102fe421d092101cfc76509210057f75509210457c75509210067f655092115e7c6550921006bf6450921006bc6450921005f7715092101df4715092102fe4215092101cfe76cc9210457e75cc9210057d75cc9210067f65cc9211367c65cc921006df63cc921076dc63cc92101df671cc921005f571cc92102fe421cc92101cfc764c9210067f654c92111e7c654c921006df634c921006dc634c921005f7714c92101df4714c92102fe4214c92102cfe76d05210457e75d05210057d75d05210067f65d05210f67c65d0521006bf64d05210bebc64d052102dee72d0521005ed72d052101fe421d05210bcff7650521004fd765052102cfc76505210067f65505210de7c6550521006bf6450521006bc6450521005ef725052102dec725052101fe4215052102cfe76cc5210067f65cc5210ae7c65cc521006df63cc521076dc63cc52102dee72cc521005ed72cc52101fe421cc521074ff764c521004fd764c52102cfc764c5210057f754c5210457c754c5210067f654c5210967c654c521006df634c521006dc634c521005ef724c52102dec724c52101fe4214c5210067f74594210067e74594210067d74594210067c74594210067f73594210067e73594210067d73594210067c735942102e7f725942102e7e725942102e7d725942102e7c725942102e7f425942102e7e425942102e7d425942102e7c425942102e7f325942102e7e325942102e7d325942102e7c325942101e7f715942101e7e715942101e7d715942101e7c715942101e7f415942101e7e415942101e7d415942101e7c415942101e7f315942101e7e315942101e7
  | 5 => 0x4ff70d912100cfe70d9121004fd70d912100cfc70d91210067f50d91210067d50d9121006be40d9121006bc40d91210457e75991210057d75991210067f65991210067c6599121006bf6499121005de7399121005dd73991210bcff7599121014fe75991210be7e75991210147e7599121004fd75991210be7d75991210047d75991210bcfc75991210bcfe7499121074fe73991210bede7399121004de7399121004fd73991210bedd7399121004dd7399121004fd72991210beed7299121004fd71991210bef571991211e6f721991210bcff709912100cfe7099121004fd709912100cfc70991210067f50991210067d50991210057f75591210457c75591210067f65591210067c6559121004ff75591210067f75591210047f7559121014fe7559121004fd7559121014fc75591210067c75591210147c7559121006bf7459121004ff7359121074fc7359121004ff7259121006ef7259121004ff7159121006f77159121004f77159121004ff705912100cfe7059121004fd705912100cfc70591210067f50591210067d5059121004fe76191210067f65191210067c6519121006bd64191210bcff7519121014fe7519121004fd75191210bcfc75191210bebe7419121074fe7319121004fd731912102cfe721912102cfc721912101cfe711912101cfc7119121226f72119121226f421191210bcff701912100cfe7019121004fd701912100cfc70191210067f50191210067d5019121006be40191210bebc40191210067f65d8d210067c65d8d21004ff75d8d21014fe75d8d21004fd75d8d21014fc75d8d210bcfe74d8d21004fd74d8d21004ff70d8d2100cfe70d8d21004fd70d8d2100cfc70d8d210067f50d8d210067d50d8d21006de30d8d21006dc30d8d210457e7598d210057d7598d210067f6598d210067c6598d21005be7498d21005bd7498d21006df6398d21074ff7598d21014fe7598d210767e7598d210147e7598d21004fd7598d210767d7598d210047d7598d21074fc7598d210bcfe7498d21076be7498d21004be7498d21004fd7498d21076bd7498d21004bd7498d21074fe7398d21004fd7298d21076ed7298d21004fd7198d21076f57198d21206ee2198d21074ff7098d2100cfe7098d21004fd7098d2100cfc7098d210067f5098d210067d5098d210057f7558d210457c7558d210067f6558d210067c6558d21004ff7558d210067f7558d210047f7558d21014fe7558d21004fd7558d21014fc7558d210067c7558d210147c7558d21004ff7458d210bcfc7458d21006df7358d21004ff7258d21006ef7258d21004ef7258d21004ff7158d21006f77158d21004ff7058d2100cfe7058d21004fd7058d2100cfc7058d210067f5058d210067d5058d21004fe7618d210067f6518d210067c6518d21006dd631
  | 6 => 0xe7558e21004fd7558e21014fc7558e210067c7558e210147c7558e21004ff7458e210bcfc7458e2101edf7358e21006ef7258e2101cfc7158e2101ede3158e2101edc3158e21004ff7058e2100cfe7058e21004fd7058e2100cfc7058e210067f5058e210067d5058e21006ef2058e21006ed2058e210bcff76d0e2101cfe76d0e21004fd76d0e2101cfc76d0e2102dee72d0e21005ed72d0e21074ff7690e2101cfe7690e21004fd7690e2101cfc7690e21004ff7650e2101cfe7650e21004fd7650e2101cfc7650e210057f7550e210557c7550e21005ef7250e2102dec7250e21005fb7050e2104df87050e21074ff7610e2101cfe7610e21004fd7610e2101cfc7610e210557e7510e210057d7510e210079d4310e2101df67110e21005f57110e210bebe64d0a21006bd64d0a2101df671d0a21005f571d0a210057f7550a210557c7550a21006be6450a21006bd6450a21005f77150a2101df47150a210557e75cca210057d75cca21076de63cca21006dd63cca2101df671cca21005f571cca21205ed76cca21006ed76cca2125f6e75cca210076d75cca2102dee73cca21206ef63cca21207ce63cca21006ed63cca21207cd63cca21207e671cca21205ed71cca21007e571cca2102eee61cca21207cf31cca21207cd31cca21255ef70cca21255ed70cca2124f6f50cca2124f6d50cca21006de634ca21006dd634ca21005f7714ca2101df4714ca2121ded760ca2102eed760ca2102fce730ca2121eef630ca21006ed630ca2102def710ca2121ded710ca2102fe6610ca2102def700ca21245ed700ca2123f6f500ca2123f6d500ca210457e76d95210467e76d95210147e76d95212377721d952122f6e21d952122f6c21d95212377421d95210057f70d95210057d70d95210067f60d95210067e60d95210067d60d95210067c60d95210067f74d95210067e74d95210067d74d95210067c74d95210067f73d95210067e73d95210067d73d95210067c73d952122e7f72d95212367e72d95210467d72d95212367c72d95212367e42d95212367c42d95212367e32d95212367c32d95212367f71d952122e7e71d95210467d71d952122e7c71d952122e7e41d952122e7c41d952122e7e31d952122e7c31d95212367f21d952122e7e21d95210467d21d952122e7c21d95210067f70d95210047f70d95210067e70d95210067d70d95210047d70d95210067c70d95210067f40d95210067e40d95210067d40d95210067c40d95210067f30d95210067e30d95210067d30d95210067c30d95212367f20d95210067e20d95210067d20d95212367c20d952122e7f10d95210067e10d95210067d10d952122e7c10d95210067f65d91210067c65d9121004ff75d9121014fe75d9121004fd75d9121014fc75d9121074fe73d9121004fd73d9121
  | 7 => 0x8f21004fd7498f2102ede7398f2101cfe7298f2102ede3298f2102edc3298f21206ee2198f2102eec2198f21074ff7098f2100cfe7098f21004fd7098f2100cfc7098f210067f5098f210067d5098f21004ff7558f21014fe7558f21004fd7558f21014fc7558f21004ff7458f210bcfc7458f2102edf7358f2101cfc7258f2102ede3258f2102edc3258f21004ff7058f2100cfe7058f21004fd7058f2100cfc7058f210067f5058f210067d5058f21006f71058f21006f51058f210bcff76d0f2102cfe76d0f21004fd76d0f2102cfc76d0f21074ff7690f2102cfe7690f21004fd7690f2102cfc7690f2101df67190f21005f57190f21004ff7650f2102cfe7650f21004fd7650f2102cfc7650f210057f7550f210657c7550f21005f77150f2101df47150f21005fb7050f2105df87050f21074ff7610f2102cfe7610f21004fd7610f2102cfc7610f210657e7510f210057d7510f210079d4310f2102dee7210f21005ed7210f210657e75d07210057d75d07210bebe64d0721006bd64d072102dee72d0721005ed72d07211e5f576d0721006f576d07212877675d07210077575d072101df674d07211e6f764d07211e7b664d0721006f564d07211e7b564d07211e7e672d07211e5f572d0721007e572d072101ef662d07211e7b742d07211e7b542d072127df770d072127df570d07212777750d07212777550d0721006be6450721006bd6450721005ef725072102dec7250721225f5761072101ef5761072101fb67410721226f76410721006f5641072101df77210721225f5721072101fe6621072101df7701072126df57010721267775010721267755010721076de63cc721006dd63cc72102dee72cc721005ed72cc7210057f754c7210657c754c721006de634c721006dd634c721005ef724c72102dec724c7210bcff7599221014fe75992210be7e75992210147e7599221004fd75992210be7d75992210047d75992210bcfc759922101ebe7499221074fe7399221004fd739922101cfe719922101ebe419922101ebc41992211e6f7219922101ef421992210bcff709922100cfe7099221004fd709922100cfc70992210067f50992210067d5099221004ff7559221014fe7559221004fd7559221014fc755922101ebf7459221004ff7359221074fc735922101cfc715922101ebe415922101ebc4159221004ff705922100cfe7059221004fd705922100cfc70592210067f50592210067d5059221006ef2059221006ed2059221074ff7598e21014fe7598e21004fd7598e21074fc7598e210bcfe7498e21004fd7498e2101ede7398e2101cfe7198e2101ede3198e2101edc3198e21074ff7098e2100cfe7098e21004fd7098e2100cfc7098e210067f5098e210067d5098e21004ff7558e210067f7558e210047f7558e21014f
  | 8 => 0x14fc755903101cff745903101ebf74590310bcff7359031074fe735903119cfd7359031074fc7359031076be4359031076bc4359031004ff725903102cfc725903101cfe715903101cfc715903101ebe415903101ebc4159031004ff705903100cfe7059031004fd705903100cfc70590310067f50590310067d5059031006bf4059031006bd4059031004fd76d0c311b67e65d0c310067d65d0c31004ff7650c310057f7550c3107d7c7550c311a67e6550c310067d6550c310779c4350c31005fb7050c3106df87050c31004ff7558831014fe7558831004fd7558831014fc7558831004ff74588310bcfc745883101eef7258831076ef3258831076ec325883101cff715883101cfd715883101edf315883101edd315883101eee215883101eec2158831004ff705883100cfe7058831004fd705883100cfc70588310067f50588310067d5058831006ef2058831006ed20588310bcff76d083101cfe76d0831004fd76d08311767e65d08310067d65d08310bebe64d0831006bd64d0831075de73d0831005dd73d083102cff769083101cfe7690831004fd769083116e7e65908310067d659083102eee6290831006ed6290831004ff7650831004fd765083101cfc76508310057f755083107d7c755083115e7e65508310067d6550831006be6450831006bd645083102eee6250831006ed6250831005f7715083101df4715083102cff761083101cfe7610831004fd761083107d7e75108310057d75108311467e65108310067d6510831004fd768c83107d7e758c8310057d758c83112e7e658c8310067d658c831004ff764c83111e7e654c8310067d654c83129ede634c83101df7764c431006f7764c431004f7764c43100777754c43129774754c43101f76654c43101f75654c43101df7734c43101fd7734c431076f6634c43101fd6634c431077d6534c431297d5534c431077d6434c431007d5434c431007e7724c431007e4724c43101ef7604c43128ef5604c43128f77504c43128f75504c4310bcff7599321014fe7599321004fd75993210bcfc759932102ebe7499321074fe7399321004fd739932101cfe729932102ebe429932102ebc42993210bcff709932100cfe7099321004fd709932100cfc70993210067f50993210067d5099321004ff75593210067f75593210047f7559321014fe7559321004fd7559321014fc75593210067c75593210147c755932102ebf7459321004ff7359321074fc735932101cfc725932102ebe425932102ebc4259321006f77159321004ff705932100cfe7059321004fd705932100cfc70593210067f50593210067d5059321006f71059321006f51059321074ff7598f21014fe7598f210767e7598f210147e7598f21004fd7598f210767d7598f210047d7598f21074fc7598f210bcfe749
  | 9 => 0xf61cc9312df5f50cc9312df5d50cc9312dfd710cc9312dfd510cc93101cfe768c9310957e758c9310057d758c9310067f658c93112e7c658c9312d5dd738c931006ef628c93102eec628c93101df6718c931005f5718c93101cfc764c9310067f654c93111e7c654c931006ef624c93102eec624c931005f7714c93101df4714c93101cdc764c9310075f654c9312cf5c654c931007cf724c931007cf624c93102ede624c93102edc624c931007cc624c931007d7714c93101dde714c93101ddc714c931007d4714c9312c75f504c9312c75d504c9312c7cf204c9312c7cd204c9312c7d7104c9312c7d5104c931004fe760c9310067f650c9311067c650c9312bdde730c931006ef620c93102eec620c931004fe76d05310957e75d05310057d75d05310067f65d05310f67c65d0531006bf64d05310bebc64d0531005de73d0531005dd73d0531006ef62d0531006ec62d05310bcff7650531004fd7650531004fc76505310067f65505310de7c6550531006bf6450531006bc6450531005df7350531005dc7350531006ef6250531006ec625053101fb4415053101fd431505310067f65cc5310ae7c65cc53101dde73cc53101edf63cc531006ef62cc531006ec62cc53100cf676cc5310077765cc5312b77465cc53101df673cc53101ef763cc53101fd763cc531007e762cc531007e462cc531077d732cc531007d532cc531075f770cc5312adf570cc5312a77750cc5312a77550cc5310067f74594310067e74594310067d74594310067c745943107e7f73594310767e735943107e7d73594310767c73594310767e43594310767c43594310067f72594310067e72594310067d72594310067c72594310767f32594310767c325943101e7f715943101e7e715943101e7d715943101e7c715943101e7f415943101e7e415943101e7d415943101e7c415943101e7f315943101e7e315943101e7d315943101e7c315943101e7f215943101e7e215943101e7d215943101e7c21594310067f70594310047f70594310067e70594310067d70594310047d70594310067c70594310067f40594310067e40594310067d40594310067c40594310767f30594310067e30594310067d30594310767c30594310067f20594310067e20594310067d20594310067c205943101e7f105943101e7e105943101e7d105943101e7c10594310bcff7599031014fe7599031004fd75990310bcfc759903101cfe749903101ebe7499031074fe7399031074fc7399031076be4399031076bc439903102cfe7299031004fd729903101cfe719903101cfc719903101ebe419903101ebc41990310bcff709903100cfe7099031004fd709903100cfc70990310067f50990310067d50990310bebf4099031006bd4099031004ff7559031014fe7559031004fd7559031
  | 10 => 0x8931006ed50d89310066d50d8931006ec50d8931006ef40d8931006ee40d8931006ed40d8931006ec40d8931006ef30d8931006ee30d8931006ed30d8931006ec30d8931206ef10d8931006ee10d8931006ed10d8931206ec10d89310957e75989310057d75989310067f65989310067c6598931006ef62989310057f75589310957c75589310067f65589310067c65589310067f65189310067c651893102eee6218931006ed6218931005ee7618931006ee7618931006ef65189310076f65189310066f6518931006ee6518931006ed6518931006ec65189310076c65189310066c6518931006ef6418931006ee6418931006ed6418931006ec6418931007cd731893121fce311893121fcc3118931006ef6018931006ee6018931006ed6018931006ec60189310076f50189310076d5018931007e71018931007e5101893102eef751893102eee751893102eed751893102eec751893102eef741893102eee741893102eed741893102eec7418931006ef5418931006ee5418931006ed5418931006ec541893102eef7318931006ef5318931006ee5318931006ed5318931006ec5318931006ef4318931006ee4318931006ed4318931006ec431893102eef711893102eee711893102eed711893102eec7118931006ef511893121eee5118931006ed511893121eec511893121eee411893121eec411893121eee3118931006ed311893121eec311893102eef701893102eee701893102eed701893102eec7018931006ef50189310066f5018931006ee5018931006ed50189310066d5018931006ec5018931006ef4018931006ee4018931006ed4018931006ec4018931006ef3018931006ee3018931006ed3018931006ec301893121eef1018931006e71018931006ee1018931006ed1018931006e5101893121eec1018931004fe76d0931004fd76d09310bcfc76d09310067f65d09311767c65d0931006ef62d093102eec62d0931004fe7690931004fd769093102cfc76909310067f659093116e7c6590931005de7390931005dd7390931006ef629093102eec6290931004ff7650931004fe7650931004fc76509310057f75509310957c75509310067f655093115e7c6550931006ef625093102eec6250931005f7715093101df47150931004fe7610931004fd761093102cfc76109310957e75109310057d75109310067f65109311467c6510931005de7310931005dd7310931006ef621093102eec621093101df67110931005f57110931004fe76cc9310957e75cc9310057d75cc9310067f65cc9311367c65cc93102eec62cc931005de76cc931006de76cc9312e75e75cc9310075d75cc9310075f65cc9312e75c65cc931007cf62cc93102ede62cc93102edc62cc931007cc62cc93102ecc62cc93101dde71cc93101ddc71cc931076d
  | 11 => 0x67f65591310067c6559131005ef7259131005ec7259131005fb705913108df87059131004ff75591310067f75591310047f7559131014fe7559131004fd7559131014fc75591310067c75591310147c7559131006bf7459131004ff7359131006df7359131004ff7259131006ef7259131004ef725913102cfc7259131006ec725913102cec7259131004ff7159131006f77159131004ff7059131006fb7059131004fb705913100cfe7059131004fd705913100cfc7059131006f8705913100cf870591310067f50591310067d5059131006f71059131006f51059131004fe76191310067f65191310067c6519131006bd64191310bcff7519131014fe7519131004fd75191310bcfc75191310bebe7419131074fe7319131074fc731913102cfe7219131004fd72191310bcff701913100cfe7019131004fd701913100cfc70191310067f50191310067d5019131006be40191310bebc401913101cfe76d0d310067f65d0d311b67c65d0d31006bf64d0d310bebc64d0d3101df671d0d31005f571d0d31004fe7690d310067f6590d311ae7c6590d3101cfc7650d310057f7550d310957c7550d310067f6550d311a67c6550d31006bf6450d31006bc6450d31005f77150d3101df47150d31005fb7050d3108df87050d31004fe7610d310957e7510d310057d7510d310067f6510d311867c6510d310079d4310d310067f65d89310067c65d8931004ff75d8931014fe75d8931004fd75d8931014fc75d89310bcfe74d8931004fd74d8931006ef52d8931006ee52d8931006ed52d8931006ec52d893101cfe71d893101cfc71d8931004ff70d893100cfe70d8931004fd70d893100cfc70d89310067f50d89310067d50d8931006ef20d8931006ee20d8931006ed20d8931006ec20d8931006ef65d89310076f65d89310066f65d8931006ee65d8931006ed65d8931006ec65d89310076c65d89310066c65d8931006ef64d8931006ee64d8931006ed64d8931006ec64d8931207cf73d8931207ce31d8931207cc31d8931006ef60d8931006ee60d8931006ed60d8931006ec60d89310076f50d89310076d50d8931007e710d8931007e510d8931006ef75d8931006ee75d8931006ed75d8931006ec75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d8931006ee54d8931006ed54d8931006ec54d8931206ef73d8931006ef53d8931006ee53d8931006ed53d8931006ec53d8931006ef43d8931006ee43d8931006ed43d8931006ec43d8931006ef71d8931206ee71d8931006ed71d8931006ef51d8931206ee51d8931006ed51d8931206ec51d8931206ee41d8931206ec41d8931206ee31d8931206ec31d8931006ef70d8931006ee70d8931006ed70d8931006ec70d8931006ef50d89310066f50d8931006ee50d
  | 12 => 0xc7458a3101eef7258a3101edf3158a3101edd3158a3101eee2158a3101eec2158a31004ff7058a3100cfe7058a31004fd7058a3100cfc7058a310067f5058a310067d5058a310bcff76d0a3101cfe76d0a31004fd76d0a310bebe64d0a31006bd64d0a31005de73d0a31005dd73d0a3102cff7690a3101cfe7690a31004fd7690a31004ff7650a31004fd7650a3101cfc7650a310057f7550a310a57c7550a31006be6450a31006bd6450a31005f77150a3101df47150a3102cff7610a3101cfe7610a31004fd7610a310a57e7510a310057d7510a3101df67110a31005f57110a310a57e75cca310057d75cca310a57e758ca310057d758ca3102eee628ca31006ed628ca3101df6718ca31005f5718ca3102cff764ca3102eee624ca31006ed624ca31005f7714ca3101df4714ca3102eec620ca3101df576cc631076f576cc63101fd673cc631077d653cc631307d553cc631075f770cc6312fdf570cc6312f77750cc6312f77550cc6310957e76d95310967e76d95310147e76d95312ef5e31d95312ef5c31d95310057f70d95310057d70d95310067f60d95310067e60d95310067d60d95310067c60d95310077710d95310077510d95310067f74d95310067e74d95310067d74d95310067c74d95312ee7f73d95310967e73d95310967d73d95310967c73d95310067f72d95310067e72d95310067d72d95310067c72d95310067f71d95312ee7e71d95310967d71d95312ee7c71d95312ee7e41d95312ee7c41d95312ee7e31d95310967d31d95312ee7c31d95312ee7e21d95312ee7c21d95310067f70d95310047f70d95310067e70d95310067d70d95310047d70d95310067c70d95310067f40d95310067e40d95310067d40d95310067c40d95310067f30d95310067e30d95310067d30d95310067c30d95310067f20d95310067e20d95310067d20d95310067c20d95312ee7f10d95310067e10d95310067d10d95312ee7c10d95310067f65d91310067c65d9131004ff75d9131014fe75d9131004fd75d9131014fc75d913102cfe72d9131004fd72d9131004ff70d913100cfe70d9131004fd70d913100cfc70d91310067f50d91310067d50d9131006be40d9131006bc40d9131006f710d9131006f510d91310957e75991310057d75991310067f65991310067c6599131006bf6499131005ee7299131005ed72991310bcff7599131014fe75991310be7e75991310147e7599131004fd75991310be7d75991310047d75991310bcfc75991310bcfe7499131004fd73991310bedd739913102cfe72991310beee729913102cee7299131004fd72991310beed7299131004ed7299131004fd71991310bef571991310bcff709913100cfe7099131004fd709913100cfc70991310067f50991310067d50991310057f75591310957c7559131
  | 13 => 0x9331014fe75193310767e75193310147e7519331004fd75193310767d75193310047d7519331074fc75193310bcfe7419331076be7419331076de731933102cfe7219331004fd7219331076f57119331074ff701933100cfe7019331004fd701933100cfc70193310067f50193310067d50193310057f7550f310ad7c7550f310779c4350f31005fb7050f31085f87050f310ad7e7598b310057d7598b31076ef6298b3102eec6298b31076ec6258b31004ff7558b31014fe7558b31004fd7558b31014fc7558b31004ff7458b310bcfc7458b3101cfc7358b31076ef3258b31076ec3258b31004ff7058b3100cfe7058b31004fd7058b3100cfc7058b310067f5058b310067d5058b31006ef2058b31006ed2058b310bcff76d0b31074fe76d0b31004fd76d0b3102cff7690b31074fe7690b31004fd7690b31006be6490b31006bd6490b31075de7390b31005dd7390b31004ff7650b31004fd7650b31074fc7650b310057f7550b310ad7c7550b31005f77150b3101df47150b3102cff7610b31074fe7610b31004fd7610b310ad7e7510b310057d7510b310bebe6410b31006bd6410b31075de7310b31005dd7310b3101cdd76ccb310775e75ccb310775d75ccb3102ede62ccb31077ce62ccb31077cd62ccb3102edc62ccb3101dde71ccb31077d671ccb31077d571ccb3101ddc71ccb3130f5f50ccb3130f5d50ccb310ad7e758cb310057d758cb31005df764cb31006df764cb31077cf724cb3102ede624cb3102edc624cb3101dde714cb3101ddc714cb3129f5f504cb3129f5d504cb3129fcf204cb3129fcd204cb310ad7e75d07310057d75d07310bebe64d0731006bd64d0731075de73d0731005dd73d0731006be6450731006bd6450731005df7350731075dc73507310bcff7599231014fe75992310be7e75992310147e7599231004fd75992310be7d75992310047d75992310bcfc759923101ebe749923102cfe7299231004fd729923101cfe719923101ebe419923101ebc41992310bcff709923100cfe7099231004fd709923100cfc70992310067f50992310067d5099231004ff7559231014fe7559231004fd7559231014fc755923101ebf7459231004ff725923102cfc725923101cfc715923101ebe415923101ebc4159231004ff705923100cfe7059231004fd705923100cfc70592310067f50592310067d505923101ef71059231006f510592310bebe64d0e31006bd64d0e3101df671d0e31005f571d0e310057f7550e310a57c7550e31006be6450e31006bd6450e31005f77150e3101df47150e31005fb7050e3109df87050e310a57e7510e310057d7510e310079d4310e31004ff7558a310067f7558a310047f7558a31014fe7558a31004fd7558a31014fc7558a310067c7558a310147c7558a31004ff7458a310bcf
  | 14 => 0x147c7558c4101edf7358c41006de5358c41006dd5358c410bedf4358c410bedc4358c41004ff7258c4102cfc7258c4101ede3158c4101edc3158c41004ff7058c4100cfe7058c41004fd7058c4100cfc7058c410067f5058c410067d5058c41006df3058c41006dd3058c41004fd7690c41004ff7650c410057f7550c410c57c7550c410bf9c4350c41005fb7050c410b5f87050c41004ff75588410067f75588410047f7558841014fe7558841004fd7558841014fc75588410067c75588410147c7558841004ff7358841074fc735884101eef7258841006ee5258841006ed52588410beef42588410beec425884101ef4715884101ebf415884101ebd415884101eee215884101eec215884101ef4215884101ee42158841004ff705884100cfe7058841004fd705884100cfc70588410067f50588410067d5058841006ef2058841006ed2058841004fd769084101df47190841004ff76508410057f75508410c57c755084131ebe6450841005f7715084101df47150841074ff76cc84101cfe76cc841004fd76cc8410c57e75cc8410057d75cc8410bdbe74cc841005bd74cc841076de63cc841006dd63cc84101df671cc841005f571cc84102cff768c84101cfe768c841004fd768c8410c57e758c8410057d758c84102eee628c841006ed628c841004ff764c841004fd764c84101cfc764c841006de634c841006dd634c84102eee624c841006ed624c841005f7714c84101df4714c84102cff760c84101cfe760c841004fd760c84121fe4210c84101df77650441006f77650441004f7765044101df7745044101fb774504410bef6645044101fb664504410bfb74350441007b54350441225f4725044101ef76050441316f56050441317775050441317755050441074ff75d9331014fe75d9331004fd75d9331074fc75d9331076de73d933102cfe72d9331004fd72d9331076f571d9331074ff70d933100cfe70d9331004fd70d933100cfc70d93310067f50d93310067d50d9331004fd7699331076bf64993310bcff7599331014fe7599331004fd75993310bcfc75993310bebe5499331006bd549933101cfe7399331076be4399331076bc439933102cfe7299331004fd72993310bcff709933100cfe7099331004fd709933100cfc70993310067f50993310067d50993310bebf4099331006bd40993310057f75593310ad7c7559331076bc6459331004ff75593310067f75593310047f7559331014fe7559331004fd7559331014fc75593310067c75593310147c7559331076bf7459331006be5459331006bd545933101cfc7359331076be4359331076bc4359331004ff725933102cfc7259331004ff705933100cfe7059331004fd705933100cfc70593310067f50593310067d5059331006bf4059331006bd4059331074ff751
  | 15 => 0xd7518d410767d7518d410047d7518d41074fc7518d4102cfe7218d41004fd7218d41074ff7018d4100cfe7018d41004fd7018d4100cfc7018d410067f5018d410067d5018d41004fe76d0d4101cfe7690d41006df6390d41076dc6390d4101df67190d41005f57190d4101cfc7650d410057f7550d410dd7c7550d41006df6350d41006dc6350d41005f77150d4101df47150d41005fb7050d410d5f87050d41004fe7610d410dd7e7510d410057d7510d410079d4310d41004ff75d8941014fe75d8941004fd75d8941014fc75d8941074fe73d8941004fd73d8941006ef52d8941006ec52d8941004ff70d894100cfe70d8941004fd70d894100cfc70d89410067f50d89410067d50d8941006ef20d8941006ed20d8941006ef62989410057f75589410dd7c75589410dd7e75189410057d751894102eee6218941006ed6218941004fe76d0941005be76d0941006be76d094102ebe62d094102ebc62d094101dbe71d094101dbc71d09410bebf61d09413573f50d09413573d50d0941357b710d0941357b510d094101cfe769094134dbd7490941006ef629094102eec629094101df67190941005f5719094101cfc76509410057f75509410dd7c7550941006ef625094102eec6250941005f7715094101df4715094101cbc76509410073f75509413473c7550941007af7250941007af625094102ebe625094102ebc6250941007ac6250941007b7715094101dbe715094101dbc7150941007b4715094133f3f505094133f3d505094133faf205094133fad205094133fb7105094133fb51050941004fe76109410dd7e75109410057d7510941335be7410941004fe76cc941004fd76cc941074fc76cc9410dd7e75cc9410057d75cc941006ef62cc94102eec62cc941004fe768c941004fd768c94102cfc768c9410dd7e758c9410057d758c941005be748c941005bd748c941004ff764c941004fe764c941004fc764c941004fe760c941004fd760c94102cfc760c941005be740c941005bd740c941006ef620c94102eec620c94101df6710c941005f5710c9410dd7e75d05410057d75d054101dbe74d054101ebf64d05410bf7675d05410bf7575d054101df674d054101ef764d054101fb764d05411e6f462d05410bfb742d0541007b542d05410bdf770d054132df570d05413277750d05413277550d0541074ff7598c41014fe7598c41004fd7598c41074fc7598c4101ede7398c41076de5398c41006dd5398c410bedf4398c41076dc4398c4102cfe7298c41004fd7298c4101ede3198c4101edc3198c41074ff7098c4100cfe7098c41004fd7098c4100cfc7098c410067f5098c410067d5098c41076df3098c41006dd3098c41004ff7558c410067f7558c410047f7558c41014fe7558c41004fd7558c41014fc7558c410067c7558c41
  | 16 => 0x8e41014fe7598e41004fd7598e41074fc7598e4101ede7398e4102cfe7298e41004fd7298e4101ede3198e4101edc3198e41074ff7098e4100cfe7098e41004fd7098e4100cfc7098e410067f5098e410067d5098e41006de3098e41076dc3098e41004ff7558e41014fe7558e41004fd7558e41014fc7558e4101edf7358e41004ff7258e4102cfc7258e4101ede3158e4101edc3158e41004ff7058e4100cfe7058e41004fd7058e4100cfc7058e410067f5058e410067d5058e41006de3058e41006dc3058e4101ef71058e41006f51058e411b67e65d0e410067d65d0e411ae7e6590e410067d6590e41076de6390e41006dd6390e4101df67190e41005f57190e410057f7550e410ed7c7550e411a67e6550e410067d6550e41006de6350e41006dd6350e41005f77150e4101df47150e41005fb7050e410e5f87050e410ed7e7510e410057d7510e411867e6510e410067d6510e410079d4310e41004ff7558a41014fe7558a41004fd7558a41014fc7558a41004ff7358a41074fc7358a4101eef7258a4101ebf4158a4101ebd4158a4101eee2158a4101eec2158a41004ff7058a4100cfe7058a41004fd7058a4100cfc7058a410067f5058a410067d5058a411767e65d0a410067d65d0a4116e7e6590a410067d6590a4102eee6290a41006ed6290a4101df67190a41005f57190a4102cff7650a410057f7550a410ed7c7550a4115e7e6550a410067d6550a4102eee6250a41006ed6250a41005f77150a4101df47150a410ed7e7510a410057d7510a411467e6510a410067d6510a41074ff76cca4101cfe76cca41004fd76cca410ed7e75cca410057d75cca411367e65cca410067d65cca41005be74cca41005bd74cca41076de63cca41006dd63cca4102cff768ca4101cfe768ca41004fd768ca410ed7e758ca410057d758ca4112e7e658ca410067d658ca41004ff764ca41004fd764ca4101cfc764ca4111e7e654ca410067d654ca41006de634ca41006dd634ca4102cff760ca4101cfe760ca41004fd760ca411067e650ca410067d650ca4101df6710ca41005f5710ca4101df576d06410bef576d06410bf7675d06410bf7575d064101f7665d064101f7565d064101fb674d06410bfb654d064136fb554d06411e6f662d06410bdf770d0641365f570d064135f7750d064135f7550d0641004ff75d8d41014fe75d8d41004fd75d8d41014fc75d8d4102cfe72d8d41004fd72d8d41004ff70d8d4100cfe70d8d41004fd70d8d4100cfc70d8d410067f50d8d410067d50d8d41006f710d8d41006f510d8d41006df6398d410057f7558d410dd7c7558d41005ef7258d41005ec7258d41005fb7058d410d5f87058d410dd7e7518d410057d7518d41006dd6318d41074ff7518d41014fe7518d410767e7518d410147e7518d41004f
  | 17 => 0x4ff7058f4100cfe7058f41004fd7058f4100cfc7058f410067f5058f410067d5058f41006df3058f41006dd3058f411ae7e6590f410067d6590f410057f7550f410f57c7550f411a67e6550f410067d6550f410bf9c4350f41005fb7050f410cdf87050f410067e6598b410067d6598b410beef6298b4102eec6298b410067e6558b410067d6558b410beec6258b41004ff7558b41014fe7558b41004fd7558b41014fc7558b4101cfc7458b41004ff7358b41074fc7358b410beef4258b410beec4258b41006f77158b41004ff7058b4100cfe7058b41004fd7058b4100cfc7058b410067f5058b410067d5058b41006ef2058b41006ed2058b4101cbd76d0b410bf3e65d0b410bf3d65d0b4102ebe62d0b410bfae62d0b410bfad62d0b4102ebc62d0b4101dbe71d0b410bfb671d0b410bfb571d0b4101dbc71d0b4137f3f50d0b4137f3d50d0b4116e7e6590b410067d6590b410057f7550b410f57c7550b4115e7e6550b410067d6550b4101df47150b41005bf7650b41006bf7650b410073f7550b413773c7550b413773e6550b410073d6550b410bfaf7250b4102ebe6250b4102ebc6250b41007b77150b4101dbe7150b4101dbc7150b41007b47150b4101db47150b4131f3f5050b4131f3d5050b4131faf2050b4131fad2050b41074ff76ccb410bcfe76ccb41004fd76ccb410f57e75ccb410057d75ccb411367e65ccb410067d65ccb4102eee62ccb41006ed62ccb4101df671ccb41005f571ccb4102cff768cb410bcfe768cb41004fd768cb410f57e758cb410057d758cb4112e7e658cb410067d658cb410bdbe748cb41005bd748cb41006de638cb41006dd638cb41004ff764cb41004fd764cb410bcfc764cb4111e7e654cb410067d654cb41005f7714cb4101df4714cb4102cff760cb410bcfe760cb41004fd760cb411067e650cb410067d650cb410bdbe740cb41005bd740cb41076de630cb41006dd630cb4102eee620cb41006ed620cb410ee7f74596410ee7e74596410067d74596410ee7c74596410067f73596410067e73596410067d73596410067c73596410067f72596410067e72596410067d72596410067c725964101e7f715964101e7e715964101e7d715964101e7c715964101e7f415964101e7e415964101e7d415964101e7c415964101e7f315964101e7e315964101e7d315964101e7c315964101e7f215964101e7e215964101e7d215964101e7c21596410067f70596410047f70596410067e70596410067d70596410047d70596410067c70596410067f40596410067e40596410067d40596410067c40596410067f30596410067e30596410067d30596410067c30596410067f20596410067e20596410067d20596410067c205964101e7f105964101e7e105964101e7d105964101e7c1059641074ff759
  | 18 => 0xc75590320067c75590320147c755903202cff745903202ebf7459032006be5459032006bd5459032074fe7359032074fc7359032076be4359032076bc435903202cfe725903202cfc725903202ebe425903202ebc4259032004ff715903201cfc7159032004ff705903200cfe7059032004fd705903200cfc70590320067f50590320067d5059032006bf4059032006bd4059032004fd76d0c32004ff7650c320057f7550c321057c7550c320779c4350c32005fb7050c320fdf87050c3202def764c832006ef764c832004ef764c83202def734c83202fcf734c832076ee634c83202fce634c832077ce434c832007cd434c83221dec714c83202eef604c83238eed604c83238f6f504c83238f6d504c832004ff75584320067f75584320047f7558432014fe7558432004fd7558432014fc75584320067c75584320147c7558432004ff74584320bcfc745843202edf325843202edd325843202ef77158432006f65158432006f55158432076f73158432076f4315843202ef7215843202eec215843202ef4215843202ee42158432004ff705843200cfe7058432004fd705843200cfc70584320067f50584320067d5058432006f71058432006f510584320bd7f76597410f67f76597410147f76597410be7f63597410be7c63597410be7f62597410be7c62597413873e41597410bf3c41597410057f70597410057d70597410be7f60597410067e60597410067d60597410be7c60597410f67f74597410be7e74597410f67d74597410be7c74597410067f73597410067e73597410067d73597410067c73597410be7f43597410be7c43597410067f72597410067e72597410067d72597410067c72597410be7f42597410be7c42597410f67f71597413867e71597410067d71597413867c71597410be7f41597413867e41597410be7c41597413867e31597413867c31597413867e21597413867c21597410067f70597410047f70597410067e70597410067d70597410047d70597410067c70597410be7f40597410067e40597410067d40597410be7c40597410067f30597410067e30597410067d30597410067c30597410067f20597410067e20597410067d20597410067c20597413867f10597410067e10597410067d10597413867c10597410067e6598f410067d6598f410bedf6398f41074ff7598f41014fe7598f41004fd7598f41074fc7598f4101cfe7498f410bedf4398f41076dc4398f4102cfe7298f41004fd7298f41074ff7098f4100cfe7098f41004fd7098f4100cfc7098f410067f5098f410067d5098f41076df3098f41006dd3098f410067e6558f410067d6558f410bedc6358f41004ff7558f41014fe7558f41004fd7558f41014fc7558f4101cfc7458f410bedf4358f410bedc4358f41004ff7258f4102cfc7258f41
  | 19 => 0x9132004fd71991320bcff709913200cfe7099132004fd709913200cfc70991320067f50991320067d50991320057f755913211d7c7559132005f77159132005f47159132005fb7059132115f87059132004ff75591320067f75591320047f7559132014fe7559132004fd7559132014fc75591320067c75591320147c7559132006bf7459132004ff7359132006df7359132004ff7259132006ef7259132004ff7159132006f77159132004f7715913201cfc7159132006f4715913201cf47159132004ff7059132006fb7059132004fb705913200cfe7059132004fd705913200cfc7059132006f8705913200cf870591320067f50591320067d5059132006ef2059132006ed2059132004fe761913211d7e75191320057d7519132006bd64191320bcff7519132014fe75191320be7e75191320147e7519132004fd75191320be7d75191320047d75191320bcfc75191320bebe741913201cfe7119132004fd71191320bcff701913200cfe7019132004fd701913200cfc70191320067f50191320067d501913202cfe76d0d32006bf64d0d320bebc64d0d3202dee72d0d32005ed72d0d32004fe7690d3202cfc7650d320057f7550d3211d7c7550d32006bf6450d32006bc6450d32005ef7250d3202dec7250d32005fb7050d32115f87050d32004fe7610d3211d7e7510d320057d7510d320079d4310d32004fe76d0932006bf64d09320bebc64d0932005de73d0932005dd73d09320bcff7650932004fd7650932004fc76509320057f755093211d7c7550932006bf6450932006bc6450932005df7350932005dc735093202fac425093202fcc3250932005f77150932005f4715093211d7e75cc9320057d75cc93202dde73cc93202edf63cc9320776e75cc9320776d75cc93202dee73cc93202eef63cc93202fcf63cc932075ef70cc93239ded70cc9323976f50cc9323976d50cc932004ff75d8532014fe75d8532004fd75d8532014fc75d85320bcfe74d8532004fd74d8532006f751d8532006f451d8532004ff70d853200cfe70d8532004fd70d853200cfc70d85320067f50d85320067d50d8532006f710d8532006f510d8532006f761985320057f755853211d7c755853211d7e75185320057d7518532206ef621853201ef66118532006f561185320bcff7599032014fe7599032004fd75990320bcfc759903202cfe749903202ebe74990320bebe5499032006bd5499032074fe7399032074fc7399032076be4399032076bc439903202cfe729903202cfc729903202ebe429903202ebc429903201cfe7199032004fd71990320bcff709903200cfe7099032004fd709903200cfc70990320067f50990320067d50990320bebf4099032006bd4099032004ff75590320067f75590320047f7559032014fe7559032004fd7559032014f
  | 20 => 0x67f50587320067d5058732006f71058732006f510587320067f74596320067e74596320067d74596320067c745963212e7f735963212e7e73596320067d735963212e7c735963202e7f725963202e7e725963202e7d725963202e7c725963202e7f425963202e7e425963202e7d425963202e7c425963202e7f325963202e7e325963202e7d325963202e7c32596320067f71596320067e71596320067d71596320067c715963202e7f215963202e7e215963202e7d215963202e7c21596320067f70596320047f70596320067e70596320067d70596320047d70596320067c70596320067f40596320067e40596320067d40596320067c40596320067f30596320067e30596320067d30596320067c305963202e7f205963202e7e205963202e7d205963202e7c20596320067f10596320067e10596320067d10596320067c10596320bcff7599232014fe7599232004fd75992320bcfc759923202ebe749923202cfe729923202ebe429923202ebc429923201cfe7199232004fd71992320bcff709923200cfe7099232004fd709923200cfc70992320067f50992320067d5099232006be40992320bebc4099232004ff7559232014fe7559232004fd7559232014fc755923202ebf745923202cfc725923202ebe425923202ebc4259232004ff715923201cfc7159232004ff705923200cfe7059232004fd705923200cfc70592320067f50592320067d5059232006be4059232006bc405923202eef2059232006ed20592321b67e65d0e320067d65d0e320bebe64d0e32006bd64d0e3202dee72d0e32005ed72d0e321ae7e6590e320067d6590e320057f7550e3212d7c7550e321a67e6550e320067d6550e32006be6450e32006bd6450e32005ef7250e3202dec7250e32005fb7050e32125f87050e3212d7e7510e320057d7510e321867e6510e320067d6510e320079d4310e3202ded76cca32076ed76cca320776e75cca320776d75cca3202f6e65cca3202f6d65cca3202fce73cca32077ce53cca323b7cd53cca32206ee61cca32075ef70cca323aded70cca323a76f50cca323a76d50cca32004ff7558632014fe7558632004fd7558632014fc7558632004ff74586320bcfc745863202edf325863202edd325863202ef7715863202ef7215863202ef42158632004ff705863200cfe7058632004fd705863200cfc70586320067f50586320067d5058632004ff75d9132014fe75d9132004fd75d9132014fc75d913201cfe71d9132004fd71d9132004ff70d913200cfe70d9132004fd70d913200cfc70d91320067f50d91320067d50d9132006ef20d9132006ed20d9132006bf64991320bcff7599132014fe7599132004fd75991320bcfc75991320bcfe7499132004fd73991320bedd7399132004fd72991320beed729913201cfe719
  | 21 => 0xc73597320767e43597320767c43597321367f72597323be7e72597320067d72597323be7c72597323be7e42597323be7c42597320767f32597323be7e32597320767c32597320067f71597320067e71597320067d71597320067c71597320767f31597320767c31597323be7f21597323be7c21597320067f70597320047f70597320067e70597320067d70597320047d70597320067c70597320067f40597320067e40597320067d40597320067c40597320767f30597320067e30597320067d30597320767c30597323be7f20597320067e20597320067d20597323be7c20597320067f10597320067e10597320067d10597320067c1059732074ff75d9332014fe75d93320767e75d93320147e75d9332004fd75d93320767d75d93320047d75d9332074fc75d9332076de73d9332076ed72d933201cfe71d9332076f671d933201cf671d9332004fd71d9332076f571d9332004f571d9332074ff70d933200cfe70d9332004fd70d933200cfc70d93320067f50d93320067d50d9332004fd76993320067e65993320067d6599332076bf64993320bcff7599332014fe7599332004fd75993320bcfc759933202cfe7399332076be4399332076bc439933201cfe7199332004fd71993320bcff709933200cfe7099332004fd709933200cfc70993320067f50993320067d50993320bebf4099332006bd40993320067e65593320067d6559332076bc6459332004ff7559332014fe7559332004fd7559332014fc7559332076bf745933202cfc7359332076be4359332076bc4359332004ff715933201cfc7159332004ff705933200cfe7059332004fd705933200cfc70593320067f50593320067d5059332006bf4059332006bd4059332074ff7519332014fe75193320767e75193320147e7519332004fd75193320767d75193320047d7519332074fc75193320bcfe7419332076be7419332076de7319332076ed721933201cfe7119332004fd7119332074ff701933200cfe7019332004fd701933200cfc70193320067f50193320067d50193321b67e65d0f320067d65d0f320057f7550f321357c7550f321a67e6550f320067d6550f320779c4350f32005fb7050f3210df87050f321767e65d0b320067d65d0b320bebe64d0b32006bd64d0b32075de73d0b32005dd73d0b320057f7550b321357c7550b3215e7e6550b320067d6550b32006be6450b32006bd6450b32005df7350b32075dc7350b32005f77150b32005f47150b320067e65987320067d6598732076f7619873201ef461987320067e65587320067d6558732076f46158732004ff7558732014fe7558732004fd7558732014fc7558732004ff74587320bcfc745873202cfc7358732076f73158732076f43158732004ff705873200cfe7058732004fd705873200cfc7058732
  | 22 => 0x8542006f52018542006e52018542226f420185421467f74594420be7e74594421467d74594420be7c74594420067f73594420067e73594420067d73594420067c73594420be7f43594420be7c435944202e7f725944202e7e725944202e7d725944202e7c725944202e7f425944202e7e425944202e7d425944202e7c425944202e7f325944202e7e325944202e7d325944202e7c32594420067f71594420067e71594420067d71594420067c71594420be7f41594420be7c415944202e7f215944202e7e215944202e7d215944202e7c21594420067f70594420047f70594420067e70594420067d70594420047d70594420067c70594420be7f40594420067e40594420067d40594420be7c40594420067f30594420067e30594420067d30594420067c305944202e7f205944202e7e205944202e7d205944202e7c20594420067f10594420067e10594420067d10594420067c1059442074ff7598c42014fe7598c42004fd7598c42074fc7598c4202ede7398c420bedf4398c42076dc4398c4202ede3298c4202edc3298c4201cfe7198c42004fd7198c42074ff7098c4200cfe7098c42004fd7098c4200cfc7098c420067f5098c420067d5098c42076df3098c42006dd3098c42004ff7558c42014fe7558c42004fd7558c42014fc7558c4202edf7358c420bedf4358c420bedc4358c4202ede3258c4202edc3258c42004ff7158c4201cfc7158c42004ff7058c4200cfe7058c42004fd7058c4200cfc7058c420067f5058c420067d5058c42006df3058c42006dd3058c42004fd7690c421ae7e6590c420067d6590c42004ff7650c420057f7550c421457c7550c421a67e6550c420067d6550c420bf9c4350c42005fb7050c4213df87050c4202def7650842006ef7650842004ef76508420076f75508423cf6c755084202f6e655084202f6d655084202def745084202faf74508420beee645084202fae64508420bfae54508423cfad54508420bfaf4350842007ad4350842007e77150842007e4715084202eef60508423c6ed60508423c76f50508423c76d5050842004ff7558442014fe7558442004fd7558442014fc7558442004ff7358442074fc735844202ebf425844202ebd425844202ef771584420bef741584420bef4415844202ef7215844202ef42158442004ff705844200cfe7058442004fd705844200cfc70584420067f50584420067d5058442006f71058442006f510584420757f76597321367f76597320147f76597320767f64597320767c64597323bf5e32597320775c32597320767f61597320767c61597320057f70597320057d70597320767f60597320067e60597320067d60597320767c60597320067f74597320067e74597320067d74597320067c74597321367f73597320767e73597321367d73597320767
  | 23 => 0x77765d85420067765d8542006f665d8542006f565d8542006f465d85420077465d85420067465d85421e7b774d8542006f763d8542006f663d8542006f563d8542006f463d8542007e742d85421e7b642d85421e7b442d8542006f760d8542006f660d8542006f560d8542006f460d85420077750d85420077550d8542007e720d8542007e520d8542006f775d8542006f675d8542006f575d8542006f475d85421e6f774d8542006f754d8542006f654d8542006f554d8542006f454d8542006f773d8542006f673d8542006f573d8542006f473d8542006f753d8542006f653d8542006f553d8542006f453d8542006f743d8542006f643d8542006f543d8542006f443d8542006f772d85421e6f672d8542006f752d85421e6f652d8542006f552d85421e6f452d8542006f742d85421e6f642d85421e6f442d85421e6f632d85421e6f432d8542006f770d8542006f670d8542006f570d8542006f470d8542006f750d85420067750d8542006f650d8542006f550d85420067550d8542006f450d8542006f740d8542006f640d8542006f540d8542006f440d8542006f730d8542006f630d8542006f530d8542006f430d85421e6f720d8542006f620d8542006f520d85421e6f420d854215d7e75985420057d75985420067f65985420067c6598542006f761985420057f755854215d7c75585420067f65585420067c65585420067f65185420067c651854201ef66118542006f56118542005f67618542006f67618542006f76518542007776518542006776518542006f66518542006f56518542006f46518542007746518542006746518542007b57418542006f76318542006f66318542006f56318542006f46318542007e74218542227b64218542227b44218542006f76018542006f66018542006f56018542006f46018542007775018542007755018542007e72018542007e5201854201ef7751854201ef6751854201ef5751854201ef4751854201ef77418542006f75418542006f65418542006f55418542006f4541854201ef7731854201ef6731854201ef5731854201ef47318542006f75318542006f65318542006f55318542006f45318542006f74318542006f64318542006f54318542006f4431854201ef7721854201ef6721854201ef47218542006f75218542226f65218542006f55218542226f45218542006f74218542226f64218542006f54218542226f44218542226f63218542226f4321854201ef7701854201ef6701854201ef5701854201ef47018542006f75018542006775018542006f65018542006f55018542006755018542006f45018542006f74018542006f64018542006f54018542006f44018542006f73018542006f63018542006f53018542006f43018542226f72018542006e72018542006f6201
  | 24 => 0xe76d954215e7e76d95420147e76d95423ef3e42d95423ef3c42d95420057f70d95420057d70d95420067f60d95420067e60d95420067d60d95420067c60d95420076f20d95420076d20d95423ee7f74d954215e7e74d954215e7d74d954215e7c74d95420067f73d95420067e73d95420067d73d95420067c73d95420067f72d95423ee7e72d954215e7d72d95423ee7c72d95423ee7e42d954215e7d42d95423ee7c42d95423ee7e32d95423ee7c32d95420067f71d95420067e71d95420067d71d95420067c71d95423ee7f21d95423ee7c21d95420067f70d95420047f70d95420067e70d95420067d70d95420047d70d95420067c70d95420067f40d95420067e40d95420067d40d95420067c40d95420067f30d95420067e30d95420067d30d95420067c30d95423ee7f20d95420067e20d95420067d20d95423ee7c20d95420067f10d95420067e10d95420067d10d95420067c10d95420067f65d8d420067c65d8d42004ff75d8d42014fe75d8d42004fd75d8d42014fc75d8d4201cfe71d8d42004fd71d8d42004ff70d8d4200cfe70d8d42004fd70d8d4200cfc70d8d420067f50d8d420067d50d8d42006de30d8d42006dc30d8d42006ef20d8d42006ed20d8d4215d7e7598d420057d7598d420067f6598d420067c6598d42006df6398d42005f67198d42005f57198d420057f7558d4215d7c7558d420067f6558d420067c6558d42005f77158d42005f47158d42005fb7058d42155f87058d420067f6518d420067c6518d42006dd6318d42074ff7518d42014fe7518d42004fd7518d42074fc7518d4201cfe7118d42004fd7118d42074ff7018d4200cfe7018d42004fd7018d4200cfc7018d420067f5018d420067d5018d42006de3018d42076dc3018d42004fe76d0d420067f65d0d421b67c65d0d4202cfe7690d420067f6590d421ae7c6590d42006df6390d42076dc6390d4202dee7290d42005ed7290d4202cfc7650d420057f7550d4215d7c7550d420067f6550d421a67c6550d42006df6350d42006dc6350d42005ef7250d4202dec7250d42005fb7050d42155f87050d42004fe7610d4215d7e7510d420057d7510d420067f6510d421867c6510d420079d4310d420067f65d09421767c65d094202dbe74d094202ebf64d09420076f65d09423e76c65d094202dee74d094202eef64d094202faf64d09420bdef70d09423dded70d09423d76f50d09423d76d50d09420067f65d85420067c65d8542004ff75d8542014fe75d8542004fd75d8542014fc75d8542074fe73d8542004fd73d8542006f751d8542006f651d8542006f551d8542006f451d8542004ff70d854200cfe70d8542004fd70d854200cfc70d85420067f50d85420067d50d8542006f710d8542006f610d8542006f510d8542006f410d8542006f765d8542
  | 25 => 0x8443004fd7558443014fc7558443004ff725844302cfc72584430bef741584430bef44158443076f73158443076f43158443004ff705844300cfe7058443004fd705844300cfc70584430067f50584430067d5058443006f71058443006f510584430bedf6398f42074ff7598f42014fe7598f42004fd7598f42074fc7598f4202cfe7498f42076de5398f42006dd5398f420bedf4398f42076dc4398f4201cfe7198f42004fd7198f42074ff7098f4200cfe7098f42004fd7098f4200cfc7098f420067f5098f420067d5098f42076df3098f42006dd3098f420057f7558f421757c7558f420bedc6358f42004ff7558f420067f7558f420047f7558f42014fe7558f42004fd7558f42014fc7558f420067c7558f420147c7558f4202cfc7458f42006de5358f42006dd5358f420bedf4358f420bedc4358f42004ff7158f4201cfc7158f42004ff7058f4200cfe7058f42004fd7058f4200cfc7058f420067f5058f420067d5058f42006df3058f42006dd3058f420057f7550f421757c7550f420bf9c4350f42005fb7050f4214df87050f421757e75987420057d75987420bef7619874201ef461987420bef46158742004ff7558742014fe7558742004fd7558742014fc755874202cfc7458742004ff7358742074fc73587420bef741587420bef44158742004ff705874200cfe7058742004fd705874200cfc70587420067f50587420067d5058742006f71058742006f51058742074ff7598e42014fe7598e420767e7598e420147e7598e42004fd7598e420767d7598e420047d7598e42074fc7598e4202ede7398e4202ede3298e4202edc3298e4201cfe7198e42004fd7198e42074ff7098e4200cfe7098e42004fd7098e4200cfc7098e420067f5098e420067d5098e42004ff7558e42014fe7558e42004fd7558e42014fc7558e4202edf7358e4202ede3258e4202edc3258e42004ff7158e4201cfc7158e42004ff7058e4200cfe7058e42004fd7058e4200cfc7058e420067f5058e420067d5058e4202eef2058e42006ed2058e42076de6390e42006dd6390e4202dee7290e42005ed7290e420057f7550e4216d7c7550e42006de6350e42006dd6350e42005ef7250e4202dec7250e42005fb7050e42165f87050e4216d7e7510e420057d7510e420079d4310e4202ded76d0a420beed76d0a4202fae74d0a420bfae54d0a42407ad54d0a420bdef70d0a423fded70d0a423f76f50d0a423f76d50d0a42004ff75586420067f75586420047f7558642014fe7558642004fd7558642014fc75586420067c75586420147c7558642004ff7358642074fc735864202ebf425864202ebd425864202ef7715864202ef7215864202ef42158642004ff705864200cfe7058642004fd705864200cfc70586420067f50586420067d505864215d7
  | 26 => 0x773d65d0c43075bd73d0c43076be63d0c43076bf60d0c43436bd60d0c434373f50d0c434373d50d0c430775e6590c430775d6590c430bddd7490c434159d7490c430bede6490c430779e6490c43076df6090c4342edd6090c4342f5f5090c4342f5d5090c43004ff7650c430057f7550c431857c7550c431a67e6550c430067d6550c43005fb7050c4317df87050c43075bf7650c43006bf7650c43004bf7650c430073f7550c4341f3c7550c430773e6550c430773d6550c43075bf7350c43076be6350c4341f9f5350c430779e5350c4341f9d5350c430779c5350c43007bb7050c4340fb87050c43076bf6050c4340ebd6050c4340f3f5050c4340f3d5050c430779f3050c4340f9e3050c4340f9d3050c430779c3050c430bddf7650c43006df7650c43004df7650c430075f7550c4341f5c7550c430bf5e6550c430bf5d6550c43075df7450c430779f7450c430bede6450c430bf9e6450c4341f9f5450c430bf9e5450c4341f9d5450c430bf9c5450c43007db7050c4340fd87050c430bedf6050c4340edd6050c4340f5f5050c4340f5d5050c430bf9f4050c4340f9e4050c4340f9d4050c430bf9c4050c430079f7650c430059f7650c430069f7650c434279f7550c430071f7550c4341f9e7550c434279d7550c4341f9c7550c4341f1c7550c430779f6550c4341f9e6550c4341f1e6550c4341f9d6550c430071d6550c430779c6550c430079f7250c430079e7250c430079d7250c430079c7250c430779f6250c430779c6250c4341f9f5250c4341f9e5250c4341f9d5250c4341f9c5250c430079f7150c430079e7150c430079d7150c430079c7150c430779f6150c430779c6150c4341f9f5150c4341f9e5150c4341f9d5150c4341f9c5150c434179f7050c430079b7050c4340f9e7050c434179d7050c4340f9c7050c4340f987050c430779f6050c4340e9f6050c4340f9e6050c4340f9d6050c4340e9d6050c430779c6050c4340f9f5050c4340f1f5050c4340f9e5050c4340f9d5050c4340f1d5050c4340f9c5050c4340f9f2050c4340f9e2050c4340f9d2050c4340f9c2050c4340f9f1050c4340f9e1050c4340f9d1050c4340f9c1050c430067e65988430067d65988430079d4398843076ef629884302eec62988430067e65588430067d65588430079d4358843076ec6258843004ff7558843014fe7558843004fd7558843014fc75588430beef42588430beec4258843076ef3258843076ec3258843004ff715884301cfc7158843004ff705884300cfe7058843004fd705884300cfc70588430067f50588430067d5058843006ef2058843006ed20588430067e65984430067d65984430079d4398443076f7619844301ef461984430067e65584430067d65584430079d4358443076f46158443004ff7558443014fe755
  | 27 => 0xe6218943006ed6218943006f860189430067f65d85430067c65d8543006f860d8543004ff75d8543014fe75d8543004fd75d8543014fc75d854302cfe72d8543004fd72d8543004ff70d854300cfe70d8543004fd70d854300cfc70d85430067f50d85430067d50d85431a57e75985430057d75985430067f65985430067c6598543006f7619854319dfa7098543005f97098543006f860985430057f75585431a57c75585430067f65585430067c6558543005ef7258543005ec7258543005fb705854319df87058543006f860585430067f65185430067c651854301ef66118543006f56118543006f8601854319dfa76d814319efa76d814300cfa76d81430077b75d81430077875d8143006fb65d81430077b65d81430067b65d8143006fa65d8143006f965d8143006f865d81430077865d81430067865d8143007bb74d814319fb874d8143007db73d814319fd873d8143007db43d8143007ba43d8143006fb62d8143006fa62d8143006f962d8143006f862d8143006fb61d8143006fa61d8143006f961d8143006f861d8143006fb75d81430067b75d8143006fa75d8143006f975d8143006f875d81430067875d8143006fb74d814319efa74d814319ef974d814319ef874d8143006fb54d8143006fa54d8143006f954d8143006f854d8143006fb73d814319efa73d814319ef973d814319ef873d8143006fb53d8143006fa53d8143006f953d8143006f853d8143006fb43d8143006fa43d814319ef943d8143006fb72d8143006fa72d8143006f972d8143006f872d8143006fb52d8143006fa52d8143006f952d8143006f852d8143006fb71d8143006fa71d8143006f971d8143006f871d8143006fb51d8143006fa51d8143006f951d8143006f851d81430757f76594431867f76594430147f76594430767f62594430767c62594430767f61594430767c61594430057f70594430057d70594430767f60594430067e60594430067d60594430767c60594431867f74594430be7e74594431867d74594430be7c74594431867f73594430767e73594431867d73594430767c73594430be7f43594430767e43594430767c43594430067f72594430067e72594430067d72594430067c72594430be7f42594430be7c42594430767f32594430767c32594430067f71594430067e71594430067d71594430067c71594430be7f41594430be7c41594430767f31594430767c31594430067f70594430047f70594430067e70594430067d70594430047d70594430067c70594430be7f40594430067e40594430067d40594430be7c40594430767f30594430067e30594430067d30594430767c30594430067f20594430067e20594430067d20594430067c20594430067f10594430067e10594430067d10594430067c10594430773e65d0c43
  | 28 => 0xe4346f3d50d0e43005dd76d0e430bedd76d0e430bf9e54d0e4347f9d54d0e430bddf70d0e43475dd70d0e4346f5f50d0e4346f5d50d0e431ad7e7598a430057d7598a43076ef6298a4302eec6298a43076ec6258a43004ff7558a43014fe7558a43004fd7558a43014fc7558a43076ef3258a43076ec3258a43004ff7158a4301cfc7158a43004ff7058a4300cfe7058a43004fd7058a4300cfc7058a430067f5058a430067d5058a43006ef2058a43006ed2058a43076f7619864301ef461986430057f75586431ad7c7558643076f46158643004ff75586430067f75586430047f7558643014fe7558643004fd7558643014fc75586430067c75586430147c7558643004ff725864302cfc7258643006f65158643006f55158643076f73158643076f43158643004ff705864300cfe7058643004fd705864300cfc70586430067f50586430067d5058643006f71058643006f510586431a57e76d95431a67e76d95430147e76d95430057f70d95430057d70d95430067f60d95430067e60d95430067d60d95430067c60d95430077860d95430067860d95430073f40d95430073d40d95430075f30d95430075d30d95430067f74d95431a67e74d95431a67d74d95431a67c74d95430067f73d95431a67e73d95431a67d73d95431a67c73d95431a67d43d95430067f72d95430067e72d95430067d72d95430067c72d95430067f71d95430067e71d95430067d71d95430067c71d95430067f70d95430047f70d95430067e70d95430067d70d95430047d70d95430067c70d95430067f40d95430067e40d95430067d40d95430067c40d95430067f30d95430067e30d95430067d30d95430067c30d95430067f20d95430067e20d95430067d20d95430067c20d95430067f10d95430067e10d95430067d10d95430067c10d95430067f65d0d431b67c65d0d43196f860d0d430075f65d0d434675c65d0d430bddf70d0d4345ddd70d0d43457d860d0d434575f50d0d434575d50d0d430bf9f40d0d434579d40d0d430067f6590d431ae7c6590d4318ef86090d430073f6590d4344f3c6590d430079f6390d43075bf7090d43445bd7090d4343fb86090d4343f3f5090d4343f3d5090d430779f3090d4343f9d3090d430067f65d89430067c65d8943006f860d8943004ff75d8943014fe75d8943004fd75d8943014fc75d894301cfe71d8943004fd71d8943004ff70d894300cfe70d8943004fd70d894300cfc70d89430067f50d89430067d50d89431a57e75989430057d75989430067f65989430067c6598943006ef629894319dfa7098943005f97098943006f860989430057f75589431a57c75589430067f65589430067c6558943005f77158943005f47158943005fb705894319df87058943006f860589430067f65189430067c651894302ee
  | 29 => 0x1001001000000b8050008000001001001000b000000800000a001000c042000000001400000a001801401e000000002001400300e80040040020008000000014000007c00a00200180000180060030018000002000001801000f004802000e002009800001a00100100180260000000000010001000002000a005002009c004001004800001e0080000020008009000002000800200600080040030010030018033000801c05a0070018008000000001000c00000000280040000050088000000002000003400e002004001000e001001800001e00b0000024000000002801c0500030020000022001000000c00400900280000000030108004000007000000401c0100050004002006008000c010001000002000600000a000000400000000000000010000000006000002000000800000080080020000010000002006004000800e01c009806400600000000700000000000000006007000800000000e00c000c00200000e801c0040000068004010001001001001c00500200040000020010050002000000000800a000001800c0000010000024010000002004804200a009000000001c002801c0080100000008000000001804000a0020008000000001002004000600000a0010008000000006401a032000800001600500080080140000000000010001001006c002000004800000200e006001800e01a00000300120070018000000013005805c012001001801c00e000001000400003201000280120000040018028013000800000601500000180080040008010002000002004401a001004802001400500200000040000010000000000000002c00a00a001800c00000a008800001200000280bc006001000000c00201200400140040030010000004000005001400000000000280020150000000010002000009401c002000000800600800600380040080000004004007001801001c0020beef6298b4302eec6298b430057f7558b431b57c7558b430beec6258b43004ff7558b430067f7558b430047f7558b43014fe7558b43004fd7558b43014fc7558b430067c7558b430147c7558b43006ee5258b43006ed5258b430beef4258b430beec4258b43004ff7158b4301cfc7158b43004ff7058b4300cfe7058b43004fd7058b4300cfc7058b430067f5058b430067d5058b43006ef2058b43006ed2058b431b57e75987430057d75987430bef7619874301ef461987430bef46158743004ff7558743014fe7558743004fd7558743014fc7558743004ff725874302cfc72587430bef741587430bef44158743004ff705874300cfe7058743004fd705874300cfc70587430067f50587430067d5058743006f71058743006f51058743075bd76d0e43006bd76d0e430779e53d0e4347f9d53d0e43076bf60d0e4346ebd60d0e4346f3f50d
  | 30 => 0x4000800c008000003002400e0210000000000000004000002a02c005801003a00000080080000010018000000000008800000c003000000800a00000180080160020000014000003003000801a01000300300000000008004002000000800401200d000001c004004000000000000b0000024002007000801c000000002800c000000004003000c00c00000000000130010010002001000000400400700b0018028004000800c00000e0040014018000000804802e00a000000c00c000001800002a0000018018000002001000000000b0008028006004000800c00200000280000140030028004008006004804802e00000f00000080000000018002002001801c0060000120000010002001800401a00200000000060000010048010010004001400201500100100000000008014002008000803000400200080000000090020000000012003000801400800000080040190028000016000001000000400000f80080020000000000000002000801c01a02e0000000006000000000000800000f800c0060000000000006008000000000400500000000020020000000010000006000400e017001003c00200300800000020070030004006002002802000600000200000380020000028030001003800c000023000000c0000170020014008018000000c034001002801000000200480100000020000050006000001804c00e004005801000c023015000c00000b0020000006001000000001a004018005800e0020000008000000000005c00000200000380240000058014000012007000000000c002800000000a01600040460060028008000000015801400200100100000100010000018002000000001c00e002002001000200000380180180010020004000005000001800200000a0000000000003001800400300300040020010000000006002004001000600000180040040020080054006000001008401a012000000c0000120058000010001002002800600000000400140000010000018000007801401e00201300100000190008068014000002803803c012001003400201b000000c0020010010028000006002009402200e00080140060030000004016000000802804e00000d801001a0010050008000002001005400600100400740120020098008008000000000801000400100000020000038000006004000000000000500100ac01400100380040100010040068002001004000001e00100500180040050000010000003008001c0000030000024000001001000c00000000000ac002009000000000201400800000340210000000010002002002400400e001001c0440000048000008005000800000000e000003400c0010000078000008000802400a0150010024000000000801c00200b00e800c00a005000000000001
  | 31 => 0xcb200000006dc000000000006cf94660001ec600016cc00027002af00005710000000000006a002000000c000006001800c00200c00080040280000038000000006002005c04a0000088024000001004002001e004004800400000a00d8004012010002800404c0020000008002000000000001a0020018004000004003002c00c010000802000600000380080020000008010000006000800000e0020008000002002002807800201f00180200040000018004018000005801800404900700000020010008010002000001001000200c0020030000000001000004c006001802c0340010138030000000007006800401400c0018066000001806800000400200080360090008000004016006000401000d000000c00800b00300180000000000000000003000000c01a001001000000200e0050000002007000000001200b003000002c007006004c01c0080050008000005002000402a002005800c00c0010000034050003000000c008000005000c00200000000040240090018014002004002000001a0000010014002001000000402600c0048004004004001800c00000c0030010008008002800c040000006009800400f000000000000500380040000040008008000003000800c00a001001800000e008000001800800600180080140000010120006002001800002a0000000040004009000001c00000000f000000c00000080000000040000028006002001000c004004003000000000c001800801a00000000380140010000000008005004000c00200400700000000030068000028000002000002200000080040060000000000000000000000002200d0088030014003006000800001100a80100060000020000004017000001c000009002000400401500c803801e002004003803200100700000000020008010028000001800c0140010000008012039004800400000c0000038052001000000002e00a0000000000012000002401a00000300000020000060000000002000000800a0000000090000000003005c00600000080040080040030004004000001000800000600700040160080008000000001000004400401200780180000000010018024001001000000000200080240000010000038016000002004400c0000028008008000001002c006005001008003c0010070004004003000801400400400000000020010008020016008000802c000003000000000c00d00000080000040048014002000001000c024001000001c010000003000800e00a00180040100080068000000000003002c01801c0018000006001007009400000000180180640040098010000000008800c00204000100000080370008000008004000800c0000070030034002000001001400e00500000040080010000008034002008001001a00b00080
  | 32 => 0x59994ac00000003e600000d6141e5d1800081f81320000d2a2dd80000000d3a0000b2c44e80005a5882683c049c09880000001c068e5000073422f462c077a1b71bd22a1083809980004aba20c417800000019820559fee00006980e31a9640a0a6c05c878c943258c416a24400000008c9800000000002441ec48b11b7a2fb0f48361000081e264e3db80000001b4c00014a015300001c79f961d31430654834e681092a5c41bba88d125a00013b800025a20001a08000110a3c2168e04906a0600921c0001b0e7ee9ac80ec171411ca68c9968c5c1aa8b0810d11783e30f203b41cb800000000000000000000000000001f9217a4fe01b05c084485d690462da92ba40b00006c582fc21b80000000000700197a3308d0c927000017e800083890c2155819443601a638e24ee06b1494823148c000000050380006740adc00000005f0a2e66099aee6f7817a81c987a096267e1bd0120398100a00008320000e2400003b26910a0207b000087780006988000000225e8141ce21180f247839ab609411fc02c9e5886d86764751e2801386ca50e8fa85dd20cc5bb94f014f09402ec217e4298e925411eae39220b461f26e2626a4443249cf63d58734140a608594265e444035c00005940000000000000053f0c22000000086b02a00001c48000000000000002d0243094c026864891a86371a2057b81f48a022143cd22640000f380541a5a99b17d06d8925833794a20001fd42a300cc2a60ada09c8000170933a00015445b0a34e07490624999e121c4927468ca42e51a0e160db1aba302226e559092c0000e0012f82c82b382b00ba8c144c0000014506666d40000871000040aa1543621bd400026628c0804c8ad00009189a2a20b110c1058a129c59b0813d1ed27db99be0c5a35e7cf8000555a5d298a9d6860e00000e9000000004d4239884c97d01de45d8d660db8ade867801c0d425263e402b43609b201c588544e5174a78d80004a68de68660e7c87301da8f899ba569a3b4000000073780285d51a8033e0a0c770a0d81248c7844f82028ff9d726e99b962bc828e6a20fe48688c9a00002d4506000087f9a5c585820649b089c00004e28d800001cc23e80001da69861ae641926d260a062096780000810ba83f99384158955a6e600000001bfc00022ca1af0000779190e0c9240469e02906ea0aec20ea4140270c4c00000006270612000000084f0ba41ff22d610f0000000000093a000000c913889e1d263c50a2629619121e5261c82a96606a12406000038e000000000018da6a085ea0001de27d9800000000007918fe812e153290580000000000078195a9bd17ac28e8000000196a000000000026ba89a088c8a5000079d000098300000000000000000085e000000000008d09790636092600000008e00d160000582000151c000
  | 33 => 0xb26026fd85d657800247c39b102b0a59200016782911fa2042800060307500000c8829280005db0ba20f39ca639b2390000083668e18840002594595857200008ac8228c4406402847572374000000072515204089fb44b410f6375800013094d604696846bb025e359152667500004951a4601007b846b11e28cb8e7a75b957263fa65c000205c477169e7338d5e3ea902600000002d8865411f8000294991a63e90a816380000461cb26a88000000170e5190dc40000d625be000067f18e01a0905210894be000040861c22a000006c400000003420000000000047f84e456800000001e660000000332174c05198c60000000327a238000000065c18a011688840000000662917a08c851200023ce44a89425391bc010315606ac8c36812021685823d84f01f9c46d24a62d08a300a922721240fbc6eb1e967a990987bf962013b8000000173c0000440000163a3a1800030c9c727a40ba05011736360110e7588058066145626095d8782800023899781e487ac033822a9a424a49069ef87d3954e2c5912e0cea28e194000058724fe59d80006960702166800059a8000000192404e000028ca5a400000000000d446f580000000000018000009a9d1025a1aa813f12fe786a0c40001dd2663185200000006248e3e0000ee219c9842795968004a19dc126209476310de60614ec00006cc8b00f4c65a13fc7bd9d6005d9a2684618448c1a6a27c0924073e9c02922a16c5fc84ac4c38ef06d986b64ce2036832a166910039c2009aaa1ab106a0e28e5c14b8a0e95a8f4411c22067f2a02e61512e63d8918c1c8a2ae000263c8b48000000000041e81125249c6693409d000022b03b696001ae83fe00003e00001dfc8dca2963da1f8a09c11007889b144291d0076593569a600d6000000000001e8000106c5e500004c9257200012f4000078422521d000000004fd1cee41f00005e2825c73f9bdc0d81faa09593ee7409be295f256c5ee8c2c1fc8000000000000013f06bc067e0001c9e35b10ea88d800034714601f6855a0ff1006349221651c8b325820b7a6ad00004cf8000000000088c09fa1d20000000000037e000071180002fe000002f000094d18d2685097286517da94614b40000bfc29d1b6c8b78000000000000002f639095403481dba000051622c800000006d4000000000005261ba000053e10d03cf8dd8982800000000005a816f0000000016406a253a22869458000802262e33d800028da66460887de666979e00000000000000870031023496426018c168d4062855285da0001a3e5c207be1a986d87319b8800021be369860e54d951800000007bb230000000009c2a50a32e97a242f00164b01b5e09202f800022107b095f23e8800024f1b480910000000000039317f60000000000000000000000000e02438a646000000
  | 34 => 0x580001bc61989f1a35e000025d175c6b311666e0a4b06a1800032506d643b80008ff1b4e6b395d42f200005e611260368fbe000023c51d048870b8978000000003f1de04b80a3473c020e00000003cc1b9e28e0a726450e8e03b800000000005468e967ac047c99f180a42500002a500001ff88040001e803e39e0863200003f01080957913412b811e38a96024c998f03a417ce85d8726538000000000003e580000002232000240c10e1b3600017185d48e9857b140096b98cc15188c848d8d948f1000077b93825818af021c93d0000216200001e40001808000122600000005ce9c9600000fe0000000000074048f00000b900a6196800001f96d250687b010516725df827a8ec154235d2284000081e1be8000017854e00004646e280006ae149e388947e71c018286192f28c3908a6538a7c6458f1c27c0f1e00025ce000000000001aa97796ec0e9800062b890a93606162800930068a34602024e6721192c86d000032f000005a05a4974000028f80000000df68a61e207a90d865578b9c50e0cb81b780001ed80007638a8e00017e29781d5600001ca1798000845929e97080000002016816969c000178e0d68ce06a50000952000017a000008008da0000000553095600011228c401f094b000032c0b2a813007a5fb800081500006f802d687900000000d1a000000000004da53424780000000917262600004328ea0000000000000005c02040000635a4fc64b9a3c67d000043c8000000000092a8db68ba210c00000005f60b14532a1440000000781971e4a880000002536000122a384824c51621ea2aa8000353a674351896e8401efc1b413e668a15e4335267632d02a888284e69ae01ba0e69fec7289e4856a095a000131e2690be40000c7677c876c5da8450191961e02826243c580000001632075800095e9c1e5f480008a8a7103d70000690236c2b815b82fd99e86b1894c75e24226d091a085f1318623215054e8b244f511ae8b5000076121ca1118bce182000000024be129a33255700004d6121e980124608404b25e20f3600023d25851ba01f705b097c21707779aca3080af800014da20211705ae80000000000000012c000000087f231696f972a00021ee79b00003c686782c705241d48c300001eee3d18000000197c3be000044620a82ba82d0000000090382f431684020001e0000017a0650800095580004ad895005b0d6e8e30ce2000195600025440001d2439400001dc800072000007088a8092f0e187601e400499b066660e6813c80003f4270e51c000085d1fbe51a80006dc84c434d03420f11f242fca3ac2829d6689992184b31fc2658800090f0ec07af80005a90000000000000004100000000690800016a1020000000033580000438000510a5b600013720000000517959c8bc0a5e41700000001f605a
  | 35 => 0x319e8e0fb208007f06b09278e361ce17aa71504d253980000000f6c8d48f4021d08a400016240e003c636b99a680b010000000001f996da0a592700000a48000000000023922f289c2914800021a00e49120000789800046a8000244800020313a87d90000000000054907e0744959855e1abe80a12528af9ef064d254a27f893832b93ae00000005c10000036066e7e693c88839cb017492b26b6a2f289d9d76877065844c84fa65326e40d901d034e20e074b1b385b9156658e1c8a03c0382984a17248b83780a69c261b190f80001bbc8fc00000868b1200009b6631075e6ec23e48971538000070a665a6fe1a4a5908478000000000067f8246000005232617a8914202486994ea5b280f2316119c9a119001fb928a0ab8fba6f409046b7890e2d58000048a41e7e3a61e4de11fa59513048c30cf43b18f7c67203bc0dd8cea397986a17d00003b093cc0001e6827b0000000000000007c834c800090f80002601fc671900003190000000163e01415526e000001730b065ce1444000270291800000001a5606d9d0a0000cec7e51cbe000000000013fa352000034c0000533800042680009119f4800023ea62280000000000000025403d000000010e019c00001f01bda613000076800002d380000000bee7e30c8e7f220a60000e6214290dc57d80000000b9431b8000390148445680005a524988ce2520000223e5e49e10723204e9ba930c1b90dc800002fa4b18d9021aa584776139e93907ba0000000801239a0e605ae2dc1f345f792e24629f706bd21a88d60000000077e8c6800026e848e6d515fe315198e1fe907465d1dd037080005e6800060585e2202a34c756a5862f510b4000271298d9f908f300003819ed83d9a00626c89141d18bb6505a13e0df9db697f00004dd1a180000c0c000158633180007dc8780000000059900008561ddc0000cc021f874a0878dc0000235a44d80006bc800000000005a280002a90000593967400000004cc800000018206eb9ccc4011a007fa0aae2e6227a83c8aee5eb800042b860086c1c420000218748800000002d20000300686a53265b0ff663514b20000e840d118de00002f00000a7654f800071712b828102c64d280003ae00003d400000171b0a69405f80c380000000d42698138a1b998be8ac9260454a2e40169b0278f9b40212a41c30d091625117b611092dc45891063a0a36400000141869d503571a746ba0fb247608b825c24e22b2a384432214a2ac8e723b993b0121800018316fa1cb94b050f0ad816a87180000b300000f8200000008a9222c000000000000000000d3e000000021f02827c0012e23c00000bc904416018ce00023e04d380005138a204a097f400024f269a17268cf00001fa9d20000088000009c6971a6ae886048a2309c6c267a0ea619186c12c129c08e18
  | 36 => 0x4820001ac017400005c7027e0000000783196600013e45c58a088ad889e5aa80de80d0f2e29c1202421144025788b64ba8fa08aea0ba15f80e82e799b219023fa96e85781a58f2a34b83d249a9fa487a000018e85929b09f32428830a00019541561e9c7ab22ac00008484e800000e200007dd9ca4000145c0000000340883060d00004c880000000010000114200000003dd000000000000000c1c894800000014109c2000071380005e180000000d360b7800000018040001aa469b9b8e887977c29e800021381e21548000000247c56c916c0000000000081848480001eb80002e09ecc3f80000000216a353000000015822990bac000257652710e43bd230811700008b08b4670aa3b253c930a1179e2e000122458b996e1098fb036811e058d800067a800052f00005c880004c186140000000976000000000000000000000056e3a2a70c0e8847492d800078c19e6000093e62c86ec6289ca87ee191052b800036f8b4c0001776000000000000003c380000001d827422494661161800000007c211306ca0000890931292a21282eb8f02000000032f9a5e448000071600003d08000276037c0000226000204a00000000001e148c285b87f126a434616bc56d08ea50ba21a35e983236c9cea3e502ce01580003df9f04148185a50a0eee1a2053094e824a5089e887b980006da8dfc98d0d0436f0b6e4939f9e21e8b6870100007e60e748b88240000174022a052226180980580caa0c122ec86e0ab6000000000012063eb9fe005609e27bea50038b800091d083e3b21082000046614ca6720009314625822800010c00000eca0671d4a92316e86baa24e4ca9df017b1f146b1255c90d14fa1c226a69af843e34f14140a4810c0da101e00014de3a704541e61baa95c1d447ffa4181ef173294405f0000018e000000028f03c000000000000000000000c05100000000fce47b000018d8846012000098c00002c0034c7f89d4e9b8137e92387c469d964a5ad226035ca5ac22196302e2097c01b83f200019028c120623118a2e37697bc3bf97689569e2c6d29a527b817660bb103424215503740fdc484215a27d09ca000159017825688071a9a7560000100145423403483748dc6375199e60c0196806184a7728a16947882e4a910900210000000124c238000000009d600000002db000061801c000009f82a218ba22d1e183f580007f38ddc47d000000006246781d7e8579c3600012ce38ca5e44db1daa34194760000f802f980008ea93421d095063371d3a2f89e9e6bd998041ca68a95085b454789be2590c722c7948847e26aa04f8598101835e9a195547d78ad012122462b0216436d19b848522f63cc80aa17505f230f92a87ef10b8399159e83a01ea3b912f83e924706d10e665dc91ba57980001c6a7148da96829198bde5
  | 37 => 0x2391c780000ea418ca02a8e708bc01298141da12c87989eb20a50eb214d8000395800074a04580000eb63ed120855a211400001ae86b800089f8000392992600000001dd222a7a198a6058923e5e709e855d873e3a7a4d475e859c13c01fe7f6000046883e806f1b944a02506584a6527ad03dc8df0b041ab91685f209768b41c62940896005a9cac4d78d684ac00009a089aa8378000000000076d03f82f68d54000000087882dc49880005b7057000000000e1922200024028e38900469008c20580001d580000000bc67cb8000000061c74a9354000192000000006b700002660000000259a1e200004af237661e0c5644714aa0e4a23c00000000e100862d2800000003a800009de24789d40000d6000024ea4e6039690a8b5a00008d838380008c704cc81a8de042390cc27f00dc7a880000328e7e0e50bd048125e6000077033680009bc011c5d220526cd00008f08000000000027383aa6a493da0001742000000033c9856000139a000000000000005709e7c6758000000181a00000009c18000000000036619ac8a791f63ca0000000265633404ca5311abc287a5401629ce415f068672200004db800015d88cc00015c80c888d439190389a000005900c66000164c738128c21600002a88a8a513022435c0dfa634164641f9a305f29c9c792800000c07663fe8000867000000000000000000000000000000000000b9271a875c0000000000000066f0f0c00000001f4800078e866058980000000000000200c0000d2800000000001f6a293a202008000028b0ff80000000000104216e800066d1a70000259800000009b3819e00025f6000158a0001e3c673000005380001a393ec4160000000123894a93ea5400e2c94b952e53b95e8793215681f149878d161a8931f588c78c0a64f25c08f7051a59b89e400025d668d000049b80000001cda3f78a1c471a0c8000000000004d860b85684c200001bba3b86d596b20000000052a070497932c70b20b86240564641000036b1dc8000000051287c64be80000000a1840480000001c5a6218000000011069c80003fa80000000000000034a0000000000165859c016e93d91c46d19b682cd0000093800000020a48eda25091f8bc22549d482de23f66078000150800015b13a40000b0e000000043680000000f88000062a29e06be688800002a034600004aa000000051b8b5023700004e1800048a000017d80000ad93886279a0e1cb1310306a1844f7048000004f80000cac5fb23de41380003eb0e0c5120000347985c00003528d21cbc75aa47a39c0b5255c232826c1fa04daa1c221b00ea00008aa472266e502a4fa57a88202e980001e719506fe975897e800030f05fc0000462190a3362208f7a000187e4678000000029e887098473100006cea10a09b000000008063820
  | 38 => 0x476000196427318f24799e947c99ff00000c262571d0448000000001f7a71a00001738f3a0001d14726a08e32a25b823f9e643bc91d000000001bfa01a69b073c5d80000281864e000013633392a04971dd447c94022ea97ea457000079400006bf00967e480007d11d06944a2486048000000247684c0b26000143e0000000000000082b80001159d16415000086300822598a685611cf4297000092116d08e09f284d3212c8bb864479d9c521ed00000000000000172400004f69200000978a2ce00003ee1db8d7c543027823f000073604448c8800079f8000564833c000105030780002ed0f8681193b43548b5800016d600014d426b0a8660a80006831e5c1ad00627d284240000544757800087d80c826522bc45b923211b95de6be20225c29cf88f4147c0000afe0000b3a10a85548fba36230b91741f883303b50a9a80384de677a428298101854a169a0001184537177a69e800000000007621da287b003e77e19ec0001390000134400026dc00000000de8b6600019ca0000cc4000099a00000009bd8bf45690000000000008b26920880000000061801502888e89e9a08fa4c823a1db83e9866c9b29c905729698177a1a400026c44f626423de0000000000000000000000000363800000025543738ffe97b0ae68a31e5e14a99c27a283d800021f08221f52000211c7df9e8406200b60f5108c0000f9a13410d486c9cfc58f0dba3039a4a246069c18b9a2e5838ed288009e08f589ea656015e1bf08b07a81370340258e372a2260a71f789729cd43a802223b113286ef914400005c473080004bb00001be032a5cba6d64f4941237f83e63328ad605f0000179127c6f380009af00007fe8cfc97c9ff40001ede21804941a280004d4159a6f200000000bd835f803883d0306839263a0001cb400021f4000078a99e91ea304800048b2270999a2fe1c00ae42100bbe000250800000045e98eec38500b48d5239800000007719f36367a5b25a319a4839a36e43f00009a5234a00009a800010f012795465d91fe60220fc85638e882d520f656da4ba064a06000000007ff00009bc800000018b88d708a045200003e28ad41878d9c00000003bf0aac8821182447915097a00000001b2670c9a7c000183a2000fca0000ae868580007c3057a0000000289000000000008279dce00007643569e04000227c0001e1634414ba0851c740fe8b8e72387608d5991e79e9ba29841b7c13a24104a19c120001ed62cb83d04ec86b84a3a0007da1d926c126de66b903e16fa01e63a00000000000868000000023bc56fa6a86041cd25ef99401e98c280b28d9204e95aa45580001b6a1d40000000147028001a8000181989400001b400000000001d7c64c800055aa44a0000000000180046983ca00000000000000000056646f0000819854a0000652
  | 39 => 0xe16180003c2800002b1eaa8fd268889b056a0b1000000020be4031060000000000001b89950000000000017610360001030099139c5119de865c9fe40000000000000044b00007759e2a6de0c240000b7e8cf80000f300004bda3345b80b4499e269c00000000001fd600000000000000000000000000000000000000245a0001da493c08f84ab000038d00001a302343b79bc20001876521a3e666800003228e3a0000b0284397fa000057400000007248000000000008c20fa000199c9470e1a76ca5fe02890025cc265818e00000001fdc00010a04b906304b593ca00015c60000f5468b00009b320584638de400000007e195cc0e80c9649402a28a99d9a11b11024e58b804f1814c2e115ce063256640f0e0a8419c0a00000006c7000089000004531ee46cb9fda62d058c3ad24c27d8a68e4038cfa49a24923dc8c70575947a2199dae82107a28b70b5e50d194670e869e2f101f6288a16823b1c083b805a650a916a3ba96ae8798cfe913960493807288988d8c96001786ec8c025af99da3c492da96f1f888a09b6e71d821c3270c6a1a1094a0000ccc0000000000000000025744399c867870000962983e5f316b022f870e7dd000081b91d69b0190c4120ac83910000274920c5b00d9a84d94a88b3216e8b60000603a27406a1b12172053859100008498000930120a908221225f8000329000000000000000ecc6950d5619d03ba87580000350000802800013f8b3c1d500004fa21347911ee80001eb800000000000336217a7049ab00000111c100000aa69858000230015a69209544cc0000348a46a991000000015120ef984e03e800000000002c300000000c0684882ac8769f12248866a0fc18a400007d459b04e080ca14636aa1326fe1d941061c44831a32410b9dbc31200c64ed9db084a8000712827c87381648bf20b69539a1c30e00d0199009a050096c04100008aa00005a9a6b026e254674d0de80c4938c0001bf241d800000009a200000002c60000000261a000000064e0c3a0001c28214051844900004f38f4a00005500000a9e2d200183ab18f46e10de298107d863d848c0000c4a5290a2a6071d320000796040820c0f0a14c00000f6981958833c00001570000000000000013a67eb800000015303898f060b0041c14a00000001d748c600006f300006101a90041962842c24b8516800000026500000000000000000000002e315e2000195c703a1fa0002550339a5aa00000005d780000001986924253c1e69a2456e98f89159d407c29a6a9bb1290413219a3d8116093289b451e02be77693fe5240a1441a1be855f0ca03ab8fc200019b603e08f423580940000690071197640400000001ee20fa8610456000000000003a69a986ed9edc67c143200000000001fac35006e000000000000000710000006f8000000
  | 40 => 0x6965e7951eba26393f65e902ba916000038a21d8000199491a13c24df064c6fa80006ac25b482c99c67ce82522b88888352935c2af9bd81421d3670f831801ca4cc57726483968090492840e79e11047d0031403b133c00000001de07320001b1e24ea538427192a86e95b00078928617869a3d68000896931609d0bba10e81f8000001a8a289bc49213e26fc24422190180000137a8f00acc2561d982a81ad246c9f2c80410ac5d4044a0cd1b905c005ee8d9a064342a32a735873a93783ae3189b763cb153c77d9a4e33624ce00a9be48110a467d08d504661a8a5cd11ee01d06b2313932030400000001e8200020144218ac45db890c00009c40001b225c3041e158096a64d9230548800000021aa23c9908000062c7e106ce7ba911257f24006308906000000051880000000b7c98e23f85831128000050c5ec800000000007d59172000115452e0ef600023122481d86000143600000002d91ea81e19e8c8da0a667d180008de8fec3ee0b1014d17fc000136632108900d8a5825fc000090900007d68000000094e6a384c00000000137222257489c80000be8526864a7530000000123a97699440000be06b580000000e8c40683286d91a8c6cb06d20001ae080e800037c24860000134000000070680001338fd84a9862600010884d69f502148da44b78fc6728003639383207f4800073b000000000004000000000194800005b62ad1ece0f2243a22b8f6a0001c1c6d7000e3f68df40a312aa339102e79486687fa9ba43f480000000d1234b218236e013c87196880f7a5ee74b85047c783664b0a2c86be90ec69f8c60180a22e6c0118837ca5a65bd839e9411a9e21100000001d1a5bca6d4904a1083f5053e77a972000201ce0d00b720000b2000021484e487d6000000083b800000000007a6000037793624c095bc442150a50919aa1c8080e4c714526e48bd697304ba0000c8c82880667fc956e95e037067e800099c1f4c40c99d8295823a8e18ab85bf80000000cb6229800007c946c215a42c000170600000001258000000160a5a1a3a0293002c00000000002640750a432000000064c00000000afc0570f6496592d454b10b600014200f680007730000717897a82701a40000c2a0829e6a8d117968f217c66b093800001b0c4358eaa7f01b9c29422888359e721c30d0e509800000024dc00002d822280000001450523835400023ba365893446c012a5ff97e6208a12e20492842621e428241ff600896ce23ba1023200ffc6df87902b486c2226a40a6d81d700b6800031f010807622588782620225901c8748000767a18862f0ac60e4081400010920d5962a0000000209053a59f009284900260dd1d385fe15080521ad01fd96101c40f100bf94f4674a4ec26b914e8aa9aa657416d40001d465ed04042e596e63870b3627ba46
  | 41 => 0x158c317800000023f2560047a5d1000077b00000f8a0b07081298545174e8e780005968000747000048d1c242f000007030b3e31f80000000a6a5f703b80000000000000081d00000000936863a1bc41987e870c20fe6a8259c00000004fc9e2405f8dcc00014f601e09da687836a4e38af68e299c03e10c040001fd059a2696029119000003ac29b8276000000000020c245f80000000fc46c6800000000003b61c144b61dbe0a29caa0000000000119a626190a928a11a931000082814fe279a0d219796e21fb025a0cb8000000000000007627711f8000000000000bfe00015f44b2885c6ab00000000f9e131891c4cb803c7bd20dc00001525fa018608d9bc4888070461405480001b58737000000020683b58000000208270f1dac5889fcc000224a91c800027c9e3284800005ae1d3079b8f762a5800002e9c3882b00008be1df419710fe3ba1bb84311b528e923a66b6262252587ca86588fa4cd9ae49319f825208a5a412a4a00c092421eaa2fa4da107854382e627026da0001d0c2189fa6810a0d4465083c9be2204622000000006c82659e4e720800054d00003e494a6000000065f882815009a600000000000000061136077f98746461ef21f080b8000000000025a80001ce6920a13a8ce875800012941e091408fb0ca695498e67af017466c009e8c80dee32881ee2328eb071b9bca31b10ca9838a4200013a200000001fe11f049e1e702ae9d6c0000000000000087e06229681364998184854088781aa03380001264427800084493aa00005ac18f1ed42c282b29930e1017f80000001b3046018aa56581b2679000080982b8000002e2840000000073643a1e602e6a6146ff982495894e255ea3960002092000152a3a00e583d4a056000071c8080000251a0fc23124b22e2907071e9b3c2e400007db0b282aa0c42246800058d00003560924943a3d498b09a03949276075237e0000a5400020386739c160c69408972229c4a21cc87b68000000033e00000e203499f6000042000000009ad1116681800008b8ea682600004450a4073293bc1611e9200003d6128a6e869300c03af93de4a491b83950064664032c00002086e680000f9000022880005aa133449c83265de1c7e485800000020ce000000000015da2168bb21b01662568988080f9220000000000e8000410229a07e800031e8034821a4f85031562495800011311d259e90fa35d86ea1bc00000000706258a40817700000000000000000077016d87fe11de00025b0000008e000211080082aa3aa14d20000e7867e00005f0000000016c416200009ad96524ef8a92264800000019ee6470f2200010c60fd94c242e9ec07c5a25677984ec74380001f3982c000000016f264a000156c168a0ec82680003000694000187277e8000623996080486a447
  | 42 => 0x5280005c49906000000066480004730f0434990149771d9c000206c3ed800071326c633481304338000671007c25212c400011463af1fa846d800052d80001f4000057e911a6c6000046fa22464ea43688e972c0458c9000011640a98bf00c211c291b1b8607210964dda0bc472800027700e00a1a2ea000229015798ca49e98ea9bf0842314992812a0af44020b74059a14e7ce0f26171800663b030c000000068e94cc0509574491099c6dd04a43fb93e07f782e093d00005920ce800024b464f881a000037273a21f28179c7c004903a8e20bbc3209f7c7cf00001d68f5e6b5004246480009bb9c565ee11ce94f8a828d01b2a0000ff00000a625ec15ac68d843003093d66c91f5486484b4935a25492226327c1a14298f892e2fa898a4ba19e250708ce090a0964158c18000118663b8a7e8f295f02630000544078e8de11e45f9089280c01e674f099072e8b5c5700ff239d811494698e499aa69a2c697d61028000223a5d48ae067c4700dea1f316c69490f182d806f276a000019e88ba0000edc1caa1404ad05a06e3215c0000bb823d9b328eb8d145520724070841a39ba5580fd10d29150ab0522a57e5e3218a3dc00006848e04000000000021903d38876368800000000009590000000000081da2da5a48f007b418662a7159400000000001d527479d8a5ca00001e80000165915e000244c57e07f00001c180001b5a1149196000000000018467ca84c810a0c86405a4643d6000000020f800000008cc0b38409142c1ea14c80849348000218002f80000001afe00004a0000000000000008cb00007c700006a7000037b1d3e000000014b042c59f86040000fcc5cfa04000000ae0000e3c5b7a6c80001d5436c0eba4bf0ece948906e8ef87a47d70e6a7ec80006808000000079e0000da88341862126800094a0cee95b9f107c88bd266a00007300c501dd831c486913c000000000000005ba9d64000000000000002bea1c816788de141863e7b2000a5ad93c400026a000006f619599888b805100000a2800017e03a89c341d1000084104d69be80007ec00004ee8000000000038c251400001a07c8000012d8bdc24091e80cc89f65c690be99a18823cf120e00000b00001cae00017841ec80002e18000000000069902e2000077c00024ae43d25887968000000000092b026e9530a1a1479eca000006872623da45f000097e207a0771d9021c16a260f22c6000081c0730d8a00026b207197626ab8000780800000000460a606805a400c44d492f000000005e000000001be67ad8932022800000000000981ae211a019a31a245e88a000000003b600000005018478000074e62b18e200007f45f125ea05c243803980000af000031024969b613409b4000049f8000000076a0b08c7400000766fb046a6999c50055000042a800000000
  | 43 => 0x668a6e63f88898684231478782ee4d182cc5bd0000657800080f06340000ff42c8800083016fc597000000000004bb9a0a20d00001439cb65d5a4d2909807000010b210d88c600016c800018a838802e858b0000000018a000031e7ed9cf21b88efa83680004c680006fd1e3820a84bc63f00001c50e94556229214017708dc12be9268bcc00014d889a948084e15ae60d80002fe80002a4000000012d26fba62813a94c074624da95817d471805ca16c8000000000062d8000192060a9a79f18387929697100008548000545957e0ed18c0000000061a1bb45e08f9c01b19f200000008f1841261b8d6a00013ac000044e6529f304
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87e855d8430840717b08bb0861080e3760d7610c210043fc32ea2184217c3e645d4430841d8bcc6ba886108031e9817510c210043fc3aca218420087d87594430840187ceab2086108030f5d56410c210062f3aac62184200c5d7558c430840153f0ca188610802a76194310c210764fbb2862184200c9d7650c4308507c3ccaa188610803875954310c2140f4d302862184205acd835db320840b1df0eb1e6410816b3e1d63cc82102e67c3ac79904200e4e7558f3208401c9aeab1e641080333dc163cc82100666b82c79904200e4f5058f3208401c9aa0b1e6410903b1c4163cc82100762882c79904203ab5845db41084071ef0eb26821080eade1d64d042101e5bc3ac9a084200e36755934108401c6aeab2682108032ddc164d04210065ab82c9a084200e37505934108401c6aa0b2682108f3a9c8164d042100752902c9a084203ae687dd921084079cd0fbb2421080399e1776484210073242eec9084200e6475dd92108401ccea1bb24210803995437648421495b343eea9084239d6687dd5210848b6cf0dbaa4210916d961b754842122eb3bb6ea9084200e6776dd5210848be4cc9baa4210917c9593754842122fa331eea9084245f4563dd521084016cf01baa4210802d96037548421006b3b86ea9084200d6570dd5210848bec4c1baa4210917d8583754842100572c34e89084239b66859d121084016cb0b3a24210803591d67448421005e341ce89084200bc5839d121084015cf0cba24210802d9e1574484211cdb242ae89084200d64751d121084015cb0d39a42108e6d9a167348421005b2c2ce69084200d64759cd210840174d0939a4210802e9612734842100573c32e69084200b67855cd21084736c90ab9a4210803591d47348421004f3c3a8690842009e48750d21084016cf0aa1a42108e6d92154348421005f1c02869084237be08050d21084075cd0c21a4210802b961843484211cdb3428869084200b658510d2108401f0a8621a42108031edd6755802148d3cc3ceab004200c7b875d560085214f50a3aac0108029ea1774580210053cc2ee8b00423daf3815d160084075e102ba2c0108029ea1474580210053cc28e8b004200ada831d160084015b3063a2c010816baa08745802102574c10e8b004203af2811d160084095e3023a2c0108038ed5254580210053d42ee6b004200a7985dcd60084835d704b9ac010816ba20973580210053d428e6b004200a79851cd60084015750839ac010802ae610735802102d75410e6b004204ae9821cd60084075e50239ac010812bc60473580210072da9ca6b004205aea82d0d60084015d305a1ac01080ebca06435802100578c0c86b0042008fb8750d60084011f10ea1ac0108029ee1543580210053c42a86b004200a7a8510d60084014f30a21ac010803a650c4358021
  | 1 => 0xb053aac610802b3e097558c2102d66412eab184200ad7815d563084075a902baac610816b3a0a7458c210052fc2ae8b184200a5c855d1630840b59904ba2c61080eb52057458c210056dc02e8b184200ad8805d163084014bd0a3a2c610802976147458c210064eba0e8b184203ad681d5163084015ab03aa2c61080387d525458c2102d66416e0b184200a5e859c163084014bb0b382c610816b3a0a7058c2100566c14e0b184203ad6819c163084015ab03382c610802b3e097058c2102d66412e0b184200a5e851c163084014bb0a382c610802a7a107058c210054ec20e0b184205ace821c1630840159b04382c61080eb5a047058c210056ac08e0b184296e4c72d41630852dc9e41a82c610a4395c435058c2148d2ec2ca0b184205ace82941630840159b05282c61080eb5a065058c210056ac0ca0b184200e5b50941630852bc98e4a82c61080396e015058c214af27902a0b184291e571054163085214bd0a282c610816b3a085058c2100566c10a0b184203ad68114163084015ab02282c61080297a164058c210052ec2c80b184205ace82901630840159b05202c61080eb5a064058c210056ac0c80b1842008de8710163084011bb0e202c61080297a144058c210052ec2880b184205ace82101630840159b04202c61080eb5a044058c210056ac0880b184200acc87481630840b59f00902c610817b2e012058c2100727a8240b184200e4d504816308529d8e20902c610a53b28412058c214a76488240b184293ec47244163084075af00882c61080fb4e011058c210072ba8220b184200e55504416308527d8e40882c610a4fb48811058c210076290220b184293ed1204416308401d8240882c6108171b9c965d0c2101c6fc3ac7a184205cce7258f43084018dacab96861085f2b99172d0c2100666b1ae5a184203c7671596430840717f0eb24861080f2d9c56490c210063ab2ae32184200cb5645c6430841d9acc6b8c861080a1f2177650c2101c5e426eca1842038dc83dd943084031f101bb286108021fe157650c210143e42aeca1842058ec825d943084071e902bb286108023ee017650c2100c7c402eca18420087d86dd543084018f4c1baa86108021fa1d6550c210043e43acaa184200c7870595430840187eeb32286108030f1d66450c210065c384c8a1842038bc87591430840187eeab2286108030f1d56450c210754e41ac8a184200cb87059143084018beeb31a8610803171d66350c210066c384c6a1842038dc8758d43084018beeab1a8610803171d56350c210bd4e422c6a184200cd87058d430840195ac9b9286108033358f7250c210065ab26e2a184200cd563dc543084011f30db8286108031e9977050c210063cb2ee0a184200cba64dc14308401972c9b8286108033698f7050c210066cb1ee0a184202
  | 2 => 0x573590210051e42ae6b204205aac825cd640840756902b9ac810802aee0173590210055c402e6b204200a3e851cd640840147b0a39ac810803275cc735902102d57416a6b204200aad82d4d6408401c3ea729ac81080ead20770590210051f42ce0b204200a3d859c1640840b55d05382c810802ab60a705902101d5b40ce0b204200ab5819c1640840156f02b82c81080ead20570590210051f428e0b204200a3d851c1640840153d06382c810802a760c705902102d57410e0b204200aad821c1640840756d02382c810802ad60470590214871a38ea0b204296e2f20d416408521c6e21a82c810a468f616505902102d57414a0b204200aad82941640840756d03282c810802ad60650590210071da84a0b204291e34715416408401c7700a82c810a578bc81505902148f1b882a0b204290a3e85141640840b55d04282c810802ab608505902101d5b408a0b204200ab581141640840147d0b182c8108028f616305902102d5741460b204200aad828c1640840756d03182c810802ad60630590210045f43860b2042008bd870c1640840147d0a182c8108028f614305902102d5741060b204200aad820c1640840756d02182c810802ad60430590214a75238a40b204205aaf80481640840bd5700902c8108038bd41205902100716a8240b204294ea7104816408529d5420902c810a53aa44120590210055a43a20b204203ab7804416408407d6700882c8108038dd4110590210071aa8220b204293ea7204416408527d6440882c810803a9481105902149f5890220b204200ea12044164084071b906bacc6108021fe157498c210143e42ae931842038dc835d2630841d93886ba4c6108023ee017498c2100c7c402e9318420ec5f75d4e63084071b906b84c61080297a163098c210052ec2c61318420ec5f759d663084014bf0aba4c610802972157498c210764e3a2e93184200adb805d263084015b100ba4c61080387d525498c210052f42ce13184200a5d859c263085234bb0b284c61080396d425098c210072dc02a13184290a5e8514263084014bd0b204c610802976164098c210746f4388131842008dd8710263084014bd0a204c610802976144098c2102d67410813184200acd8210263084075ad02204c610802b56044098c2102c76412eab1842038f4815d563084071bd0fa9ac61080317dd75358c210162f3aca6b1842038dc8754d630840b1d904b82c610a5b1b1cb5058c214ae36392a0b1842038de878c163084014bd0b182c610802976163058c2102d6741460b184203ad6818c163084031b90e982c61080297a143058c210052ec2860b184200a9e840c1630840153b08182c610816b3a083058c2101d6b40860b1842008ec8748163085279c8e4882c610803b84811058c210062fbaceab184205ace829d5630840159
  | 3 => 0x221a42059e4825c443485250fd0dbaa84909f75908775509210043f43ecaa12424587c87d95424848b8e8e3b2a84908031dd9771509210063a32ee2a124200cb464dc542485250f90cbae64909df5908575cc92122c3fc3ecb992420087d87d9732484018e8cbb8a6490a761f21975d0521386b210aeba0a424687f87d9741484010fb0fb2e82908021fe1576505210143e42aeca0a423c8f7815d941484018d8cbb9282908021fe15764c5210143e42aec98a42408ef825d9314853b0fd0dbaa629097759087754c5210043f43eca98a424687c87d95314848d8d8e5b2a62908063ba1b724c52100637b2ee498a4200c6c65dc93148401998c7b9262908030fdd274594214e537c12e8b284205a6c825d165085374ef02ba2ca1080e9d20574594210062fb9ce6b28429aa6f825cd650840b4d904b9aca10a669de05735942101d3a40ae6b28429187d879c1650840b4dd05382ca10a629b60a705942101d3b40ce0b284297a75819c165084018f6e1382ca108031ee0170594214843f438e0b28420087e8790165084010fb0f202ca108021fa1c40594210043ec3880b284200a5e8310165084014bb06202ca108169ba08405942100536c1080b284203a768110165084014eb02202ca108021fa1e30594210043ec3c60b28420087e870c165084010fb0e182ca108028fa1030594210051ec2060b284205a6e820c165084014db04182ca1080e9da0430594210053ac0860b2842038bc845d6640842f87eebaa4c8108021fe1573990210143e42ae732042038bc845ce640842f93886b9cc8108023ee01739902100c7c402e732042038bc845c2640840147d0b204c8108028f61640990210be1fbaceb3204200a3f855ce64084014790ab9cc81085f271cd73990210055dc02e73204200ab8805ce6408401c3ea729cc8108028fa1670990210051ec2ce13204291a3d859426408401c76a1284c8108038ee0150990214851f428a13204200a3e858c2640840147b0b184c81085e2fa1c30990210045ec38613204200a3e850c2640840147b0a184c810816aba08309902100556c10613204203ab6810c2640840156b02184c8108163b209755902101c7a40aeab2042038be87d51640840187eebaa2c81080b0f9d6545902101c5e43aa8b2042038f4815c164085218e8e3a82c810a471d1c5505902101c5f43c80b204200a3e85901640840147b0b202c810816aba0a405902101d5b40c80b2042018bc87501640840147d0a202c8108028f61440590210054f41880b204200a9d83101640840b55d04202c81080eada0440590214a67238a40b2042008f4874416408401dc240882c8108030fdd6755902101d5b40ceab204200ab5819d5640840155f04baac810816ab20975590210055bc0aeab204203ab4815d5640840756d0339ac8108028fe1
  | 4 => 0x5484014eb03106ca9091a1fa1e10d95210043ec3c21b2a4246a6e8284365484014db05086ca90802a760c40d912100556c1081b224200ab58110364484018becb39cc8908031719673991210062fb2ae73224200c5c655ce644840193ec8b9cc89085f2719173991210043fc02eb322420287f87d4264484010fb0fa84c890803179cf50991210062eb9ea1322420087f8754264484010fb0ea84c890803179cd50991210062eb9aa1322420087e87d9564484010fd0e32ac8908021f603755912100477c12eab2242008f7815d564484018d8ebb92c8908031ddd771591210063a3aee2b22420087f855c164484050f90ab82c8908022fe1170591210046fc1ae0b22420e8dc835c164484011ef02b82c8908021fa1f50591210143e43ea0b224200c7771d4164484010fd0ea82c8908021f21d50591210063bb8aa0b2242008bf8759064484010ff0ab98c89080a1f21573191210bc5e422e03224217cb8405c0644840153b08186c690802b360830d8d210056ac0861b1a4200c3f659d26348401878cb3a4c6908030fd957498d210061e32ae931a420ec9c635d2634840193ae9b1cc6908021fe017598d210143fc3ea131a420087d87d42634840187ce9a84c6908030f5d35098d210043fc3aa131a420087d87542634840187ce8a84c6908030f5d15098d210143f436eab1a424587c86dd563484010fd0fb2ac6908021fa1c6558d210043ec06eab1a42008ef825d563484011ef02baac6908031bdd77258d21006363aee4b1a4200c7475dc563484010ff0ab82c69080a1f2157058d210045fc22e0b1a42178bc845c163484011bf06b82c6908023be097058d210043f43ea0b1a420287c87d4163484018dee5a82c6908021fa1d5058d210043e43aa0b1a4200c6f7254163484011bf0eb18c6908021fe157418d210143e42ae831a420e8dc835c0634841d9b060b80c6908021fe1576d0d210143e42aeda1a420e8bc845db43484010ff0abb4869080a1f2157690d210746e41aed21a420287e85dd943484010fb0bbb2869080a1fa167650d210043ec2ceca1a42018fa809d943484011f3013b286908021fe157650d210143e42aeca1a42008ef825d943484011ef02bb286908023ee017650d2100c7c402eca1a420287c851d943484010fd0dbaa86908021fa1f6550d210043e43ecaa1a4200c7870d95434841d17d0fb22869083aa7a0f6450d210065c386c8a1a4200cb870191434842f1bd0fb1a869085ea7a136350d210066c386c6a1a4200cd87018d43484018f6cbb8286908031e1977050d210143e42cec21a420087f855d843484050f90abb086908021f2197510d210043fc3eca21a420087d87d94434840193ceca18869083b271d94310d210070fb2a8621a4283e1c6550c43484071d90cb90869080e792057210d2102c7a432e
  | 5 => 0x88021fe1576508310143e42aeca10620087d86dd5420c4010fd0eb2a84188021f21d655083101e3a38acaa106203cb471991420c407968e2b22841880f391c562508310063b32ee2a106200c7565dc5420c4050fd0abb084188021fe1975108310043fc3aca210620087d87594420c4050fd0abb464188961fe19758c83107c3fc3acb190620087d87596320c4018e8ebbb262188031de17764c4310063a42eec988620ecd653dd9310c4019aaa7bb262188031dd43764c4310063aa86ec9886200c7776dd5310c4016af0aa1a621880339ddb724c43100673bb0e49886200d64751c9310c4010ff0ab9cc99080a1f21573993210143f43eeab26420087d80dd564c84fb0fd0e3aac9908031ddd771593210063a3aee2b26420087f855c164c84050f90ab82c99080237e0d70593210746e41ae0b26420087e87d4164c84050f90fa82c9908021fa1d50593210043e43aa0b2642008f687c4164c84010ff00bacc79080a1fe1f5098f210043ec3ea131e420087f8754263c84010fb0ea84c7908021fe1576d0f210143e42aeda1e420e8f7865c643c84010ff0abb2879080a1f2157650f210047dc02eca1e42018f8805d943c84018eceabb683908031d5d975d07212247bc3ac9a0e4200d65755cb41c84811df0cb966390817331ca634c7210043fc02eb324420287f87d4264884010fb0fa84c9108021fe1d50992210043ec3aa1324420087f855d263884050f90aba4c71080a1fa1f7558e210043ec06eab1c425d87e871d563884018deebb92c7108031b1d77258e210043fc2ae0b1c420287c855c1638840117f08b82c71085e2f2117058e210043f43ea0b1c420287c87d4163884010fd0ea82c7108021f21d5058e210047743e40b1c42178ef865cb43884010ff0abb4871080a1f2157690e210043fc2aeca1c420287c855d943884011f700bb287108063e2017650e211e47bc32e3a144203cb47199142884018dceabb665108031b5d975cca2121c77c3ac79944200d65755c732884010fd0db86ca9080a1fe1f60d95210063cb86c1b2a420087d8798365484010ff0eb06ca908028fe1160d95210051e422c1b2a4200a5f8358365484014b906b06ca908221f61c60d95210063cb80c1b2a4200c3d741d365484018bae639eca908021f61e70d95210063dc02e1b2a420087e871c365484018f2e0386ca908021fa1e40d95210043ec3c81b2a420087e8710365484010fb0e206ca9080297a0c40d95210052ec1881b2a4246a6e8210365484014db04206ca909169da0440d95210053ac0881b2a420087e878c365484010fb0f186ca908021fa1c30d95210043ec3861b2a4200a3e840c3654840147b08186ca9091a9ba0830d952100536c1061b2a4245a76810c365484014eb02186ca909161fa1e20d95210043ec3c41b2a4245a76818836
  | 6 => 0x536c28603126200aae840c0624c40155b08180c49890eb9a04301893100572c086031262a0ec673c40624c487d8ae7880c49880399d43101893100732a862031262058ee87840624c4011db0f080c4988029ba16101893100536c2c203126200acf83440624c40159906880c498803b1e0d10189310076241a203126293ec673440624c4875cf00880c49890fb8e01101893149f71382203126293ee170440624c401ccea0880c4988039954110189310043fc2aeda12620287c855db424c4010ff0abb4849880a1f215769093102c76412ed2126205ccc629ce424c4050fd0bbb284988021f61776509310143f42ceca12620087d859d9424c4050f90a3b284988021fa1b75509313ee36316eaa12620087e87d95424c4010f90fb2a84989771d1c7655093100637baec4a126200c6c75d89424c4819c8e3b1284988031dd9771509310063a32ee2a12623cce462dc5424c4050f90b3b084988021fe1576109310143e42aec212620087c865d4424c40b8d8c4ba884988021fe1f65109310043ec3eca2126205ccc629cc424c40b998c4b9884988031b9d7621093100636baec42126205ce4625c4424c4050f90b3b6649889a1f21975cc9313be36312eb992620087f87d97324c4250fb0fb2e64989df9318975cc931006673b6c59926200e4f6518b324c401c98ca3166498a7e1f219758c93102e36312eb192620087d87d96324c4018dcebb1464988031b5d7628c93102e72312e31926240ce471d89324c4018e8cbb8a6498977171db654c931206663b6c49926200e4f65189324c481b8ee438a649880a1f21676d05310043e432eba0a620087f87d97414c4010fb0fb2e829885f2719173d0531006373aec5a0a6200c6d75d8b414c4018dcea31682988031b5d462d053100667398c5a0a6200ccd7318b414c4010ff0abb2829880a1f21576505310047dc02eca0a62018f8805d9414c4bb8ecedb2e629897795d8f65cc53100732328c598a6200c3f749d1650c53d4ef02b92ca1880e9d205725943148c3ec3ce0b286200c7b709c1650c4018f700b82ca18a421fa1c70594310043f43c80b28620087d87901650c4010fd0e202ca188021f61c40594310752f41880b286200a5d83101650c4014dd04202ca188029b608405943101d3b40880b286200a7581101650c41f0fd0f182ca188021f61e30594310043f43c40b28620087d87881650c4074ed03102ca188029d60620594310052fc1a40b28620ea5c83481650c4010fd0e102ca188021f61c20594310043fc2ae5320620287c855ca640c4031790ea02c81880a1f2177650c311a43ec36eaa18620087e87595430c41f0f90eb2a861883b8710d6550c310063c382caa186200c7a65dc1430c4018f2cbb8286188063b21d20588310762f39acba106200c5d655cf420c4050f90bbb2841
  | 7 => 0xe88050f624c4014dd0a21ec4988029b61443d893100746a1887b126200a6e85dc7624c4014db0bb8ec498802aba1371d893100556c26e3b126200a6e859c3624c4014db0b386c4988029ba1470d893100536c28e1b126240ae6811c3624c4015cb02386c4988039ad4250d893100735c02a1b126200a6e85903624c4014db0b206c4988023ba1c40d893100476c3881b126200a6e85103624c4014db0a206c498802b3a0c40d893100566c1881b126240ae681103624c4015cb02206c4988029ba1630d893100536c2c61b1262008ee870c3624c4014dd0a186c4988029b61430d89310055742061b126200aad840c3624c4815cd02186c498802b960430d89310076498061b1262008ee87843624c4011db0f086c4988029ba1610d893100536c2c21b126205c6c625d6624c4018dcebb14c4988031b5d762989310143f436eab12620087e87d95624c4010fd0e32ac498a7f175cc651893100477c3ac43126200a6f85588624c4014d90ab10c4988031b9db651893100536c06ca31262008ed87994624c4011df0eb28c4988031b9d8651893100536c00ca31262008ed87990624c4014dd0b320c4988029b616641893100477c3ac83126200a6f85590624c4014d90ab20c498802bae01641893100574402c83126200e4f655cc624c401c98cab98c4988023b61e60189310053742cc03126200a6d85980624c4011df0eb00c4988029be1560189310053642ac03126200aaf84580624c40155908b00c4988029ba14601893100536c28c03126200a6e86d40624c4014d90da80c4988029ba19501893100536432a03126200e6765c40624c401cc8cb880c49880399d9510189310073232a203126200ee360440624c4875cd03aa0c498802b9607541893100717aa4a83126200ace83150624c40159b062a0c49880393d4e531893100573c0aa63126243ae48154c624c4014df0aa18c4988029b215431893100573c0a863126243ae48150c624c4015d700a18c498802ba201431893100537428863126200a6d8510c624c401d1a86218c49890f99947511893100537c2a623126200a6c854c4624c40159d07a80c498802b360f50189310072741ea03126200e4d83d40624c52dc9ce7a80c49890eb9a06501893100572c0ca03126200e6b50940624c52bc9ce6a80c4988039ae0150189314af35382a03126295e6970540624c4875cd02280c498802b960450189310053742c803126200a6d85900624c4875cd03200c498802b9606401893100567c1a803126200acc83500624c40b1dd0e200c4988023b61c401893100537428803126200a6d85100624c40159d06200c498802b360c401893121d73408803126200ae581100624c4014dd0b180c4988029b616301893121d7340c603126200ae5818c0624c40b1dd0e180c4988029ba1430189310
  | 8 => 0x4186ca988029b60830d95312ed3b40861b2a6200a75810c3654c401cb260186ca988021fa1e20d95310043ec3c41b2a625da7681883654c4014eb03106ca988021fa1c20d95310043ec3841b2a620087e87843654c4010fb0f086ca988029ba0a10d953100536c1421b2a62038dd83dc3644c40153b06206c898802ad60440d913100637b2ce53226200c6c659ca644c4018decab94c8988031b19572991310043fc02eb322620287f87d42644c4010fb0fa84c898a5b1b9cb509913100636b96a1322620087f87542644c4010fb0ea84c898a571b9c9509913100636b92a1322620087e87d95644c4018f0e1b2ac8988021fa1c65591310063c380cab226200c6f65dc9644c4018d8cbb92c8988031bd94725913100636328e4b226200c7b65dc1644c4018f0cbb82c8988021f603755913100477c12eab2262058ec825d5644c4011f700baac8988063e201755913100637baee4b226200c6c75dc9644c4018deea392c8988031b1d4725913100672396e2b226200c7b75dc1644c4018f0ebb82c8988033adcb705913100674396e0b226200c7b85dc1644c4018f10bb82c8988021fe1570591310143e42ae0b2262008bf845c1644c4011df04b82c8988163b20970591310063dba8e0b226200c78751c1644c401976e8382c8988033adc8705913100674390e0b22620087e87d41644c4050f90fa82c8988031bdcb50591314b636396a0b226200c7b70d41644c4038f0e1a82c8988021fa1d50591310043e43aa0b226200c6f72541644c52b8d8e4a82c8988031edc1505913100e3c382a0b2262a0ce472c41644c4039e0e1882c8988063d21d105913149e7239220b2262008bf87590644c40157100b20c8988021fe1572191310143e42ae432262178bc845c0644c53f0fd0dbaa86988021fa1f6550d312ec3e43ecaa1a6200c7870d95434c401970e1b22869883aa720c6450d310065c380c8a1a6200c7b65dc1434c4018f0cbb82869880a1f2167610d311843e432ea21a620087f87d94434c4250fb0fb28869880387d954310d3141f0e32a8621a62028ef8754b624c4014dd0b106c4988029b61620d893100c77c3a41b126200a6e85083624c4014db0a106c4988029b60365d893100536c00cbb126200a6e85993624c4014db0b326c4988029be1564d89310053642ac9b126200aeb80593624c4015d100b26c4988029ba1660d893100536c2cc1b126200a6f85583624c4014d90ab06c498802abe1160d893100556422c1b126200a6e85183624c4014db0a306c4988029ba1b50d893100536436a1b126200a6e86543624c4014d90ca86c4988029ba1774d893100536c2ee9b126200ae581dd3624c4014dd0b3a6c4988029b61674d893100717aa4a9b126200e4f5394f624c4014df0aa1ec4988029b21543d893100575c0287b126200a
  | 9 => 0x5058c4100c6e43a60b188217a9c844c163104010ff0abb4862080a1f2157690c410143f43eeab108245c7471dd5621048bcc843baac4208021f60375588414963a388eab108292e64211d562104058d8eb292c42080e3b21d525884101d7240aa4b1082a2ce421dc162104010ff0ab82c42080a1f21570588410046fc1ae0b10820e8dc835c162105299c842b82c4208021fa1f50588410143e43ea0b108290e6421d4162104010fd0ea82c4208021f21d505884148f3210aa0b1082a2ce471c8162104031d90e902c42080eb920520588410043fc2aed210820287c855da421041d8bcc6bae6420803175d563cc84102e37312eb1908200c6d7558a32104010ff0abb2642080a1f215764c84101e6a38ac69908203ce47158932104010ff0abb0642080a1f215760c84121e7210aec1908200c7685dd941104018eb0bbb282208031dd4376504410063aa86eca08820087f855ca64cc4050f90ab94c99880a1fa1f75593310043ec06eab26620087e871d564cc405878eb2a2c99883a2f21d54593310043fc2ae0b26620287c855c164cc4071b906b82c9988021fa1f50593310143e43ea0b26620087e8754164cc4010f90ea82c9988062f21d40593310754e41a80b266201cb87050164cc4010ff00ba8c99880a1fe1f50193310043ec3ea0326620087f8754064cc4010fb0ea80c9988063b21d2058b310043fc2aeda16620287c855db42cc41d93ce6b2485988021fe157650b310143e42aeca166217c3e645d442cc40187aeab20859885f0f99175d07310061ebaac9a0e620ec9c7359141cc4010ff00bacc91880a1fe1f50992310043ec3ea1324620087f87542648c4010fb0ea84c91880a1fa1f7558a310043ec06eab14620087f855c1628c4050f90ab82c5188021fa1f5058a310143e43ea0b14620087e87541628c4010f90ea82c51885f2799173d0a310043fc2aed214620287c855da428c4010ff0abb2851880a1f2157650a3101c7a40aeca146203cb471991428c4079c8e2b1265188021fa1b70d95310143fc3ec1b2a6200c7970d83654c4010fb0f306ca988029ba0a60d953100536c14c1b2a620087f87583654c40147f08b06ca988028f21160d953100537c12c1b2a6200a6c82583654c4250fb0e306ca988031e5c060d95310061eba0e9b2a62a1a5e831cb654c4bb4bb06396ca9894a97a0f71d95310043ec3ce1b2a6200c7b805c3654c4010fd0e386ca989769da0470d95310053ac08e1b2a6200c79701c3654c4010fd0f206ca988021f61e40d95310043f43881b2a620087d87103654c4014bd06206ca988029760c40d95310053741081b2a6200a6d82103654c4bb4ed02206ca988029d60440d95312ec3f43c61b2a620087d878c3654c4010fd0e186ca9884a1f61c30d95310051f42061b2a6200a3d840c3654c4014dd
  | 10 => 0xb1682018ec8748162d04570fb0dbaa85a087a1f21d6550b413863a38acaa168270d347159542d040196eedb8a85a08034ddd47150b410069a3a8e2a16820287e855db32d04010ff0cbae65a08021fe1d65ccb410043ec3acb996820287e855da32d04010ff0cbac65a08021fe1d658cb410043ec3acb1968217c9e7458e32d04018eccbb8a65a085f0f9d1650cb410061eb2ae81968200a6f825d165904014d904ba2cb20a969de0574596410062fb9ce6b2c8200c6f729c965905230fb0f382cb208029ba0a705964100536c14e0b2c8203a76819c165905494eb03382cb208031edc270596410063dc02e0b2c829087e871c165904010fd0f202cb208021f61e40596410ec3f43880b2c820087d8710165904014bd06202cb208029760c40596410053741080b2c8200a6d8210165904074ed02202cb208029d60440596410043f43c60b2c820087d878c165904010fd0e182cb208021f61c30596410051f42060b2c8200a3d840c165904014dd04182cb208029b608305964101d3b40860b2c8200a75810c165904010fd0f102cb208021f61e205964101d3b40c40b2c8200a758188165904010fd0e102cb208021f61c20596410143f42ee4b1c820087d85dc9639040153b08182c720802b36083058e4101d6b40860b1c8203c767159643904018eacab8c87208021f61b7550e410043e43acaa1c8200c787059543904019b0e131a8720803361c16350e410063d32ee0a1c8200c7965dc143904610ff0cba887208761fe1d6510e4141f0f32a8621c8200e1d6550c43904050fd0bb9ac5208021f6177358a410043ec36eaa1482a387c8759542904078e8e2b2a852080f391c56250a410063b32ee2a148200c7565dc542904510ff0cba885208761fe1d6510a410143f42aed994820087f865d732904010ff0eb2e65208021f61d65cca410764f31ae9994820287e855da32904010ff0cbac65208021fe1d658ca410043ec3acb1948203c767159432904018eacab8865208021fe1572d8d410143e42ae5b1a82008df8758c63504010ff00ba8c6a080a1fe1f5018d410043ec3ea031a820087f8754063504010fb0ea80c6a080a1fa1676d0d410043ec2ceda1a820087f855cf62504050f90ab9ec4a08063be1d20d894100477c3ac43128200a6c8558862504050fd0b3b684a08021f61676d094102e72312e32128200c6c75d8942504799c8c5b8a84a09f70f1db75509411e65a3b6e2a128200d37751c542504018dcebb1664a080a1fa14764c9410043ec28ec992820087f855d832504050f90abb064a08172b189740c94102e72312e2192823cea46250b41504050fd0fbaac6208021f6037558c410162e3aca6b1882038dc8754d63104010ff0ab82c62080a1f2157058c410043f43ea0b18820287c87d4163104010fd0ea82c6208021f21d
  | 11 => 0x4c8019e0e2382c8990021fa1f50591320143e43ea0b226400c7771d41644c9218e8e3a82c8990031edc3505913200e3c386a0b22640087e87541644c8010f90ea82c8990031ddc5505913248e3a38aa0b226400c7b70541644c8038f0e0a82c89928b391c7205913200e7438640b2264018ec87481644c9299c8e2902c8990022fe1d64191320043fc02ea322640287f87d40644c8010fb0fa80c8990021fe1d50191320043ec3aa0322640287e859da434c8010fb0b3b4869905f2719173d09320043fc2aeca12640287c855d9424c8011f700bb284990063e20176509320043fc2ae9b0a640287c855d3614c8031ef0e886c2990023de1d61185320053a42ac230a640287e87dd5640c8010fb01baac8191f61fa1c75590320161e3aca8b2064058bc87551640c8010ff0ab82c81900a1f21570590320746e41ae0b20640087e87d41640c8050f90fa82c8190021fa1d50590320043e43aa0b2064018bc87501640c81d53906a02c8190021fe1576d0c320143e42aeda186400c6e85dd9320c8018db0bbb264190031bd43764c83200636a86ec990640287e87dd5610c88d8d8e5baac21911b9908775584320043ec06eab08649dc6c721d5610c93bcc8423aac21900b1d1d6515843202c7a43aa2b086405ae482545610c9419c843b82c2190021fe1570584320143e42ae0b0864008bf845c1610c82f17908b82c21924f3908570584320043f43ea0b08640287c87d41610c92dcc843a82c2190021fa1d50584320043e43aa0b086495e6421541610c8031e90e882c219016b920910584320043fc32e0b2e821e87e8798165d04018f6e1302cba080a1fa1d60597410063db82c0b2e8200c5f739cd65d042f47d09392cba0a9a8f61272597410053bc0ae4b2e8270a74815c965d04db47f08b8acba08029be09715974100536412e2b2e820087d879c165d04018f6e1382cba08031ee0170597410043f438e0b2e821e87e8790165d04010fb0f202cba085f8e10140597410043f43c60b2e820087d878c165d04010fd0e182cba08021f61c30597410bd1f42060b2e8200a3d840c165d04014dd04182cba08029b60830597413853b40860b2e8200a75810c165d042f47d09902cba08028f61320597410043f43c40b2e820087d8788165d04e14ed03102cba08029d60620597410043f43840b2e820087d8708165d04010fd0f082cba08021f61e10597410053741420b2e8200a6d8284165d040147f08882cba085e8f21110597410143f42ee4b1e820087d85dc963d04018f6e0a82c7a08071e1c15058f4100c6e43a60b1e8201cd8704c163d04690fb0dbaa87a087a1f21d6550f410bf0e21acaa1e8200c787059543d04018f4cbb8287a08031e5977050f410be1f3a4cb3168217c3e7459662d042fc5e84b2cc5a080a1fa177358b410043ec2ee6
  | 12 => 0x1de9ba0a105973200536c1420b2e640087e8704165cc8010fb0e082cb990021fe0175d93320143fc3ea1b26640087d87d4364cc9218ece3a86c9990031d5c750d93320043fc3aa1b26640087d8754364cc9238ece2a86c9990031d5c550d93320143f42ee2b26640087d85dc564cc8018f6e0a82c9990071e1c1505933200c5e43a80b266401cb87050164cc8010ff00ba8c99900a1fe1f50193320043ec3ea0326640087f8754064cc8010fb0ea80c9990d21f61b7550f321343e43acaa1e640ee1c4359543cc8018f0e0b2a87990031e9977050f320063cb2ee0a1e640ec5e7359742cc8018bacab9e85990021f61b7550b320043e43acaa16640ec9c7359142cc8018eccbb8a85990031d5977150b320063b328e2a166400c75651c542cc80196cc838a85990032d5907150b320762f39ccb30e640ec5e7359661cc81dcae62b2cc39900a1fa1774587320043ec2ee8b0e64018f48744161cc80187ee93a2cb192a29be0973596320053bc0ae6b2c6400a74815cd658c8018eee338acb192561f61e705963202d37414e0b2c64a7a6d829c1658c8014ed03382cb190029d60670596320063db84e0b2c6400c7b805c1658c92d0fd0e382cb190021fa1e40596320043ec3c80b2c640087e87101658c8010fb0e202cb1900297a0c40596320052ec1880b2c6405a6e82101658c8014db04202cb190029da0440596320053ac0880b2c640087e878c1658c8010fb0f182cb190961fa1c30596320043ec3860b2c6400a3e840c1658c80147b08182cb190169ba08305963200536c1060b2c6400a76810c1658c8014eb02182cb190021fa1e10596320043ec3c20b2c6405a6e82841658c8014db05082cb190021fa1c10596320043ec3820b2c64058bc845c2648c8050fd0bb8ac9190021f617715923202c5f43c80b246400a9d83101648c80b55d04202c919002ad604405923202e37392cba1c6400c6d655cb438c8010fb0dbaa87190021f21d6550e320063c382caa1c6400cb870991438c801970e0b2287190031e9977050e320063cb2ee0a1c643087f865d4438c84b0ff0eb28871920f879954310e320070eb2a8621c640287e85dd1618c8010fb0bba2c3190021fe1571d91320143e42ae3b22640087f855ce644c8050f90ab9cc8990021fe1572991320143e42ae5322640087d80dd5644c8011ef02baac89900e3d20575591320047dc02eab2264018f8805d5644c8018eeebb8ac8990031d1d771591320063bba8e2b226400c74751c5644c8019cee438ac8990031edd770591320063c3aee0b226400cf371dc1644c8019e0e3b82c8990031ee1770591320063c42ee0b22640087f855c1644c8050f90ab82c89900237e0d70591320047bc0ae0b2264038f4815c1644c8018f6ea382c8990031e1d470591320066db98e0b226400cf3711c164
  | 13 => 0x739c02a030a8491e72705406150923ce2e0a80c2a1112b9a08501854200572c10a030a8400a768590061508014eb0b200c2a1112b9a0a401854200572c148030a84038f68710061508014ed0a200c2a10029d61440185420056b4188030a8400ad58310061508895cd04200c2a1002b960840185420053b42c6030a8400a75858c061508895cd05180c2a1002b960a30185420055bc226030a8400ab4844c061508071ed0e180c2a10023d61c30185420053b4286030a8400a75850c0615080156d08180c2a1002ad6103018542225734106030a8400ae5820c06150945d4ce9900c2a128ba95d3201854200733a864030a8400e6550c8061508071ed0f100c2a10023d61e20185420053b42c4030a8400a7585880615080156f08900c2a1002ad211201854200753c224030a8400ea4844806150929d4ce8900c2a1113b8e0120185424a7713824030a8494ee1704806150801ccea0900c2a10039954120185420062fb9ce6b2884a9a6f825c5651080b4d904b8aca212561f61e70594420063db84e0b288400c7b805c1651092d0fd0e382ca210a21fa1e40594420043ec3c80b28840087e878c165108010fb0f182ca210021fa1c30594420043ec3860b288417a3e840c1651080147b08182ca210169ba08305944200536c1060b288400a76810c165108014eb02182ca210021fa1e10594420043ec3c20b288405a6e8284165108014db05082ca210028fe1110594420bd1e42220b28840087e8704165108010fb0e082ca210021fe157198c420143e42ae331884018dc874c163108050f90bbb286210d21f61b7550c420043f43acaa18842887c87595431082fc3886b2a86210031e1c16550c420063d32ee0a188400c7965dc143108018d8ebbb284210031be1776508420063642eeca108417cae54dd9421080195aa9bb284210031bd43765084200636a86eca108400c6f76dd5421080165f0aa1a842100339ddb715084200673bb0e2a108400d64751c542108031e90e882c2210021fe1970597321343f43cc0b2e6400c7b7098165cc8050fd0eb02cb990031edc160597320061fba4e8b2e6476a5f835c965cc8014ef02b92cb990029d20572597320752f41ce2b2e645ca5d839c565cc8014df04b8acb991de9b20971597320043ec3ce0b2e6400c7b709c165cc8018f700b82cb990021fa1c70597320043f43c80b2e640087d8790165cc8010fd0e202cb990021f61c40597320752f41880b2e6400a5d8310165cc8ef4dd04202cb990029b60840597320053b40880b2e6400a758110165cc84d0fd0f182cb990021f61e30597320772c18260b2e640087e8788165cc8010fb0f102cb990029da0620597320053ac0c40b2e6400a5f8348165cc81d4b906902cb9903a97a0f10597320052ec1e20b2e640087e8784165cc8010fb0f082cb99
  | 14 => 0x8058f61508014ed0b306c2a10029d61660d85420053bc2ac1b0a8400a748558361508015af06b06c2a1002b520d60d85420053b428c1b0a8400a758518361508014ed0da86c2a10029d21b50d85420053b432a1b0a8400a74865436150801c6ea92a6c2a10029da1773d85420053ac2ee7b0a8400ae582dcf61508014ed0b39ec2a10029d61673d85420072ba9ca7b0a8400a778550f61508014e90aa1ec2a1002bce0143d85420057840287b0a8400a768510f61508014eb0a21ec2a1003a550c43d85420053b42ee5b0a8400a7585dcb61508015ad07b96c2a1002b560f72d85420053b42ce1b0a8400a75859c361508014ed0a386c2a10029d61470d85421e573410e1b0a8400ae5821c36150801ce6a1286c2a10039ce0150d85420053b42c81b0a8400a758590361508011ed0e206c2a10029da1440d85420053ac2881b0a8400ad68310361508015ab06206c2a10f2b9a0840d854200572c1081b0a8400eb14010361508014ed0b186c2a10029d61630d85420047b43861b0a84008f5870c361508014ed0a186c2a10029d61430d85420055b42061b0a8400ab5840c361508795cd04186c2a1002b960830d85420047b43c41b0a84008f58788361508014ed0b106c2a10029d61620d854201e3a30aeb30a8400c7675d8661508018eaebb0cc2a100a1fa1b75585423ec3e436eab0a840087e87d9561508010fd0e32ac2a128f0f5d065185420047bc3ac230a8400a778558461508014e90ab08c2a10031d9db65185420053ac06ca30a84008f58799461508011ef0eb28c2a10031d9d865185420053ac00ca30a8400e37655d06150801c68caba0c2a10023d61e63185420053b42cc630a8400a758598c61508011ef0eb18c2a10029de1563185420053a42ac630a8400af38058c61508015e100b18c2a10039919742185420047ac3cc030a8400a768598061508014eb0b300c2a10023de1d60185420053bc2ac030a8400a748558061508015af06b00c2a1002b520d60185420053b428c030a8400a758518061508014ed0da80c2a10029d21b50185420053b432a030a8400a74865406150801ccecb900c2a100399197201854200733b2a4030a8400e64654806150801dc6c0900c2a10038dd52541854200573c12a830a8444ae48255061508895cd05a98c2a1002b960b53185420072ba9ca630a8400ab68414c615080156b08298c2a10029de1543185420053a42a8630a8400ae78250c61508895c904a18c2a1002bce014318542005784028630a8400a768510c61508014eb0a218c2a1003a550c431854222733296a430a8400a778550861508014e90aa10c2a1002ada1350185420055ac26a030a8400e3684d406150801c6b09a80c2a12438d9d3501854222573414a030a8400ae5829406150801ce6a1280c2a12478d9d1501854200
  | 15 => 0x4a1ac4218023de05755884301c7a40aeab1086018ec874816210c1d59906902c42183ba5185435844300477c12eab0886058ec825d56110c031e90e882c22185ead21110584430043fc2ae331e840287c855c663d08010fb01baac7a100b171d65358f420bc6e43aa6b1e840087f855c163d08050f90ab82c7a10021fa1f5058f420143e43ea0b1e840087e8754163d08010f90ea82c7a10063721d3058f420bd4e42260b1e8401cd8704c163d08031e90e882c3a10021fe017598e420143fc3ea131c840087d87d4263908010ff0ea84c7210021f61d5098e420143f43eeab0c840087d80dd561908010ff0ab82c32100a1f21570586420043f43ea0b0c840287c87d4161908010fd0ea82c3210021f21d50586420043f436e1b2a840287f87d8365508018f2e1b06caa10021f61e60d95420053b40cc1b2a8400a758198365508010ff0eb06caa100297e0d60d95420052e41ac1b2a8400a778158365508014e902b06caa10ae1f61c60d95420063cb80c1b2a8400c5d731cf65508f347d09b96caa11ba8fa1071d95423ed1ec20e3b2a840087d879c365508018f700b86caa10021fa1c70d95423ed37410e1b2a8400a6d821c365508018f2e0386caa11f61fa1e40d95420043ec3c81b2a840087e8710365508570fb0e206caa100297a0c40d95420052ec1881b2a847da6e8210365508014db04206caa10029da0440d95420053ac0881b2a8400e394010365508010fd0f186caa10021f61e30d95420043f43861b2a840087d870c3655080147d08186caa10028f61030d95423ed3741061b2a8400a6d820c365508014ed02186caa10029d60430d95420043f43c41b2a840087d8788365508014ed03106caa10029d60620d95420043f43c21b2a840087d8784365508fb4dd05086caa10029b60a10d95420043f43821b2a840087d87043655080153b08186c6a1002b360830d8d420063bb2ce331a8400c74659c663508018eecab8cc6a10031d1957198d420043f43ecab1a8400c7870d9563508010fd0e32ac6a10031e1c06558d420063bb2ee2b1a8400c7465dc563508018eeca38ac6a10031d1947158d420063db2ee0b1a8400c7865dc163508011bf0eb18c6a1002b62016318d420043fc2ae231a840287c855c463509470fd0dbaa86a10021fa1f6550d420063c386caa1a8400cd870d8d43508019b0e031a86a10031ed977050d420063c32ee0a1a840287c859d843508610f90cba886a10021fe1f6510d4215c3ec3eca21a8400e1f6550c4350907c38caa1886a11f78bd9365d09420147bc3aa3b0a8400a768584361508014eb0b086c2a10063de1d10d85420053b42821b0a8400a758504361508014eb01b2ec2a10029d60065d85420053b42cc7b0a8400a758598f61508014ef0ab1ec2a10029d21563d854200579c02c7b0a8400af
  | 16 => 0x594431843f43c80b28860087d879016510c2fc7080a02ca218c21fa1e30594430043ec3c60b28860ee58304c16510c2f47d09902ca218028f61320594430043f43c40b28860087d878816510c014ed03102ca218029d60620594430052fc1a40b28860ea5c834816510c010fd0e102ca218021f61c20594430752f41e20b288600a5d83c416510c010fd0f082ca218021f61e10594430053741420b288600a6d828416510c0147f08882ca2185e8f21110594430043f43820b28860087d870416510c050f90bbb286218d21f61b7550c434268ea1eeaa18860087e875954310c610f90eb2a862183b8710d6550c430063c382caa188600c7a65dc14310c018f2cbb828621a0b6650f7050c430061e3aeeca188600cb870dd94310c0187f0bbb286218030f2177650c430764f29eeca188600c9d53dd94310c0187ea1bb286218030f5437650c430061fbb6eaa188600cbb76dc14310c018b8ebbb28621803361c37650c430062fc2eeca188600c5c85dd94310c2f93ca9bb28621803275537650c430062fa86eca188600c5d50dd94310c018beedbaa862180336ddb7050c4341d8e42eeca188600d1c75dd94310c01c3ccbbb28621803661c37650c430064ec36eca188600d1f85dd94310c01a390bbb2862183b27d977650c430768f32eeca188600c9d65dd94310c01a3ea1bb28621803475437650c430764f43eeca188600e1f85dd94310c01c390bbb2862180327dd77650c430064ebaeeca188600e1c75dd94310c0153f01bb28621802a76037650c430074c386eca188600e1f50dd94310c01c3aa1bb28621a0ec7a1f7550c4341e8f43eeaa188684b1d86dd54310c01a3eedbaa862180387ddb7550c430060fbb6eaa188600b1f80dd54310c0163b01baa8621803c61c37550c430070fb06eaa188600e1d60dd54310c0163d0eb2a8621a0ec721d6550c430758fc32caa188684e1f865954310c1da3eecb2a862180387dd96550c430060fbb2caa188600b1f805954310c0163b00b2a8621803c61c16550c430770fb02caa188600e1d605954310c0153b0d3928621a0ec7a167250c430058ec2ce4a188681b9a809c94310c01733013928621802a7e197250c430058fc2ae4a188683b1c855c94310c0172f02b928621802e52057250c43005cdc02e4a188681b98805c94310c0153b0d38a8621a0ec7a167150c430058ec2ce2a188681b9a809c54310c017330138a8621802a7e197150c430058fc2ae2a188683b1c855c54310c0171f04b8a8621802e32097150c43005cdc02e2a188681b98805c54310d037350fb828621a0766a1f7050c430074dc36e0a188681e9886dc14310c01b36edb828621803a6ddb7050c430078dc2ee0a188600f1885dc14310c01e36ebb828621803c61d77050c430078d32ee0a188600f1965dc14310c1dd18c
  | 17 => 0x2a863487d870c36550c0147d08186caa18028f61030d95430053741061b2a8600a6d820c36550c014ed02186caa18029d60430d95430043f43c41b2a860087d878836550c014ed03106caa18029d60620d95430043f43841b2a860087d870836550c010fd0f086caa18021f61e10d95430053741421b2a8600a6d828436550c010fd0e086caa18021f61c10d95430070fb2ec721a8600c7a70d966250c018f4e032cc4a18031ed9570989430063c32ae13128600c7a751826250c018f2ea304c4a18021fa1f65589430063c386cab12860087e871956250c018f0e032ac4a18031dd9771589430063a32ee2b128600c77651c56250c018e8ca38ac4a18031ed9770589430063c32ee0b128600c7b751816250c018f0ea302c4a18033cdc4605894300678388c0b1286008ef875886250c015c902b10c4a18031e9c365985430063d380cb30a8600c7b655c26150c018f0cab84c2a18031e9d460985430063cba8c130a860287e86dd56150c690f90dbaac2a18021fa1f65585430063c386cab0a860087e871956150c018f0e032ac2a18031bd9772585430063632ee4b0a8600c6f651c96150c018d8ca392c2a18063ea1b70585430063db2ee0b0a8600c7865dc16150c018f6ea302c2a18031e1d4605854300675b90c0b0a8600ce8721816150c011ef0eb08c2a1802b920961185430053d436ebb028600c7a76dd76050c014f50c3aec0a18031e9d875d81430063d3b6cbb0286008f9879976050c014f50b32ec0a18023ee1d65d81430053d430cbb028600c7a761976050c675750dba6c0a1a06e6a0f74d814319d6d436e7b028681b9a84dcf6050c675750d21ec0a18023e61e62d81430053d42cc5b028600a798598b6050c011f70eb16c0a18029ee1562d81430053c42ac5b028600af38158b6050c015e102b16c0a18023e61e61d81430053d42cc3b028600a79859876050c011f70eb0ec0a18029ee1561d81430053c42ac3b028600aeb825876050c015d104b0ec0a18029ea1675d81430063cba8ebb028600a7a871d76050c018f50e3aec0a1a06b6a0f74d81430071daa4a9b028681aba84dcf6050c01cb6a729ec0a18029ea1672d81430053cc2ce5b028600a7b855cb6050c014f10ab96c0a1802bce0572d81430057840ae5b028600a7a859c76050c014f30b38ec0a18029ee1571d81430053c42ae3b028600aeb825c76050c015d104b8ec0a18021fe1970594431843f43cc0b288600c7b709816510c050fd0eb02ca218031edc160594430053bc0ae4b288600a74815c96510c014df04b8aca218029b20971594430043ec3ce0b288600c7b709c16510d5747f08b82ca2185e8f21170594435552fc1ae0b28860ea5c835c16510c0187f08b82ca218030f21170594430062fc1ae0b288600c5c835c16510c018f700b82ca218021fa1c7
  | 18 => 0x200000001a04400602202e00000001402400800200000a00c00400000800200200600e00003601e00800000000000804802c01c00202800009a08000000601600e00201000201e03400400000002200a00600e02200604200800401200600800200000000801602600001001201400a03801000805400800000400804a00001c02000c00001000000001400200c01400000c02401600400000000c00400e01a03c00802800000001800403400800a00a01209c00000a00202c00000800203000200800200000001600600000000200400000a02200200000000c00001e00e01000400a00c00602a04e00202a00a02800603800800000002a0240120020080020020200000180000180060040060b00c802601602002000000000000a00a00000600000000000a00600400000000000600000001e00801000405802405800c00000000201000600400000000801000001e00000202202400000e01c00201e01a09400000000c07a0000180780c203000000a0020bc01a00600405402204004a00200c00003c01200000000c00203600000000c00000000401a00800605a00800600805200600600401004200e00e00000000001400003201c00402000401805c00401c00005c02600a00001601c00e0060000087d80dd562d0c058d8eb292c5a185e3b21d5258b430043fc2ae0b16860287c855c162d0c010fd0fa82c5a180a1f21f5058b430043f43aa0b16860087c8754162d0c031d90e902c5a18063d21d105874300c7643a40b14860087d80dd56190c058e8eb28ac32183a3d21d51586430043fc2ae0b0c860287c855c16190c010fd0fa82c32180a1f21f50586430043f43aa0b0c860087c875416190c031e90e882c3218021fa1b70d95430143fc3ec1b2a8600c7970d836550c010fb0f306caa18021fe1d60d95431a43ec38c1b2a8600a6e821836550c014db04306caa18029da0460d95430053ac08c1b2a8600c79701836550c018f30e306caa18038e61060d95430072cc18c1b2a8600e6a821836550c01cd304306caa18039ca0460d954300738c08c1b2a8600e3860d036550c0163906a06caa18038e18140d95430072c30661b2a8600f1b40cc36550c0163908986caa18039618130d954341d2f41ee9b2a8683a3e84dcf6550c018dae4396caa18031d5c471d95430043ec3ce1b2a8600c7b805c36550c010fd0e386caa1ab68fa1070d95430051ec20e1b2a86aca5e831c36550c014bb06386caa18029ba0870d954300536c10e1b2a8600a76811c36550c014eb02386caa18031e5c070d95430043f43c81b2a860087d879036550c010fd0e206caa18d21f61c40d95430052f41881b2a8600a5d831036550c014dd04206caa18029b60840d95430053b40881b2a8600a75811036550c010fd0f186caa18021f61e30d95430043f43861b
  | 19 => 0x44fb295e08d00000006792d20b440008bd14295c000053d0338a60d0838700001a82ce488060909506c8524e822840006ca00c855466e4fc2d804c0a108c42b71f3400003e0000ab45fe40c10b0c3cf7a6060438dad342200233892486c13a4f30d280000b700024d098825400003d400a9764ec851ce1a8fa1fc162d12a6ae1fd27f825a66b33719301986ab39d95606ce81500008fc49a47d0a517d0b7a2a624987340009a600021a4ac672f0000f1c97622543a15f08c69661f5a2ac4b02bc1e09bfce3633b3859be000604003000000400c03400602a00200200403600a00000e04002400a01a00000200200800402201a00a00000400600600200000200600000800002e00207600805a00a00600a01800600000c00400200004606600000204600800000000000a01800400400400001002e00c00e00003000400a00c00a00000e00a02a00c00003a00002c07a02810400003e01000000800202a00600a00600200602e00000000800200000800001a00a00a00a00200201800600000404000401001004200000000200001802600800a00000604400603a02a01003602402800e03203c00203400408600202200001400000401000e00202e07402a02600a04609e0a200000001002000200a00201e00e00e01201600000400401200000002200200003400a00c02005200800a03e00002000202201000e00a00403600601000003600000200000800a00a00200e0a600e00001800202e00800000204e00201400805000c00400200000200600000206e00c01a00c01600601009c04800c00001a00c00001400000801a00a01c00002204800200a00600002a00000804801800001400602a0f001400000000e00002001600600400000a00201200c00600200400c00006c00600400000003e00600202000a04001600000000000402201a00801000400000400400000600401e03404001400200001200603600400800a00401001c00a01000403406000601400000000e05600001800c00c00400600a00001000c00002a02c03400400e00000403000004c00005a00a01803a00000400200001a01c01803400e02000000000600000400a01803400c00401401a04a01c01c00200a00c05200001202200000000000000200400000002800000000001401600602800800001a02600000000600a04006400c00600001e00400000201a00000a02200001a00a02805400000a00200200200000200000000202400c00000a02202200000000000002001e03601e00000200e00203001a00400800200000000000202400004602c04a00400800a02e00400a05a00e00400a00a00401000400200200c01600400201c01c00400200000800204a02602000000e0000000d200400400000402800401e05c00000a00a00602400400001c00200a00802400001
  | 20 => 0xb24100000001b238500012ac00042200000004590001b84000000000184800087500026d0d2c5a035c16c82d6a0a000219c2f08b526c00001f200000021b00e073c1b30074dbc36512797b01e82b9327867c66836d2a92414ed43b72068654ff08e94cd9320b623c9126000045e00024a252800049904300008603593d4237400004509887cc00037614500000282600afa3000008763ce86acd682532fba42cbf24a325100cd3665c600016cd1e6348122807ce464093058eac95621523c936823e6033ed00000000001d998786c80000000000344180000000101206e4739964e32082022000000049800008389380000001a852fa0693878c001b29e42021ca0cca00017e95083ec00000008a00000003c10140a4c4b20001d5c30c6434daa56026c19e0832098bf64b311913fc4100fd2849ed13ce000000000093a0001bd2674aa65af0b6a41c5466af2bea1288320004be20ccbbe2f33cca51822a27a033075d1965690f30954b086920f0a2c465871143f9ecd3ea399242800127e9f33d500000003d219300007b00001c413cc94a00000005d00002803fc8c140003d549d1c802961ae00722d800012813d90480000004aa8b14000000446800000010b1e818586428d430617309926ad00010f8000000000000000009206580f4ba23a04de147cc4667d20d1300a5435c41485ccb1a85027c8710bfe7441b52014084000000097d2b491b28697ad046926210048472423104ca38530863d16b18512e86dd0d88850e303a346902f868c56546c21547e01343268b1d3e25e51f005bc8da65e10f07902667594951ae45f63b24141d8cc727393592614fd22d83a18900ae64a406106a492e07238498f04d07983471b206bc90e3d4a5c482c1b74552120b4e5dc04d864935281a441a6b04e051c4fe82005543bf42d256c0125e03120f7cc7c30a25401ad00652c28102c0fc88072e01b40f764ba4808f8c4d208f14788607b469c19727880002b706d800005c6a20108708f824721421f9c000113108921c41883a4d79d708e61b31b48cc539a48e0001b4c55042727b80000003de26800009e20000e00f44d022f013e068479828944d98ac7504af08417a08f414f00000000004c74a180009c638940da7200008341d700010ca98a13188ad3aa51706a1b609ec95f3b01c204ae56a1d121701bc77804713289e05a307d93c8a46a0c1e30a5513c85123d8818dd41192982634d9e0003d180010644d722098b40f406044c152c696428000033481c3b800009582fe0002550000fe48ba3be88a4d7e1814e50f652d42644820440ed634f30383183bc2072b20a30da47271bf0dccb706eb0f508f90180c92a396ec2c68d6439182004653205588ec5521c8489017c00098b0001e5c9520b30001158000000000250400000046802a00aa24744ba5
  | 21 => 0xcd467a6221810af4f1097900000013f018236ba4703b0000445804cada22340e227c8903b0068a3bcad8a070e809dc14407b48b14d137c8ea3ad24504da5ef01e2150fda8780f4a4cd3b00000459268fba00043f0c3464873d1db1fc40e82a71891f4104e1ff2348f0027e1604341c5cb923f700012b495c0081a01418a365d33730df4f268f03fd084ca2618443ca65caec78a087a64929e99e3498888064959000272472c04d0d78000c041761ba0fe518453938905c0c886bb0828c1d0c85662309210b3a0544259bd8e744ce0001ba4d1469e3ff8874b2c7851b0000097a9f925f8fb00000881759e351aa40239500014109b141f8000cbe23533928343c613b2b59428d7819300000002ea9004f7148806e16e216841008e1072ab01e058648d0c2a5ecbfc4914d10000000301000000110e0000378000d6093212707705906e400e05c8b343832c100011b23dc31d00fd1048da00003288a41421649c000000000d18d682a051912825853fe000310825015e8a50cb800043e8c91af86a08ea0a400026c0d5006c2501c4c6f21c1075248473a7a50000000c349c0085009d37622a05880000001b60001d1d0bc5790001f580000000068e40baa69b1ed9dbc37e76645980010789e04959e780003181e9861c5348924a4855822477100000013f669d30296988c46ef131153d01a63106905a53460001f70000c8e89a007973474e6804b99f3927c2414aa02b856617134b8a7086e00000011b800000000020200003bb34d11a843820400006d44ea55d0e8855088e417405074c7687414352314e9600000027e8bd431f47100003c47323ce0458c3a5385048ee400000000007bc6ac79b37f14b850c3a43a0019044c8f136118549ba4f836c81612845e62c61d78b2e5de05f83ac4ca6fa1be03682b27d72709adc1cc26a40b20ec5ce8454e592d12589c6407873852861c38a234d26a25c3ef196074c62a420230d3c27961870c9464e9d646880005ba98343e9580a985153e5120c2f43be0b08b2d384061185968483a48020f873c0a22c00f8a6a000018f0000424ba85bc309897400000048a80011020000001ded22286048c8000faa9aa17d0000416000159008000028b27ea0c00746783a98b40b882374771d38e664c52508010f5a21a330809930c6870f5883c000685000156871c43814b0bd03307031f117b401477204e8000c7e0004b29fccdda000176937d4008bb3e980011fa7be0fe93b8cc40002fe8000b306a527a0f589b22cf3a6031c00003108f063443685b0000d0c0c6000000000000064000000001407804f41c980000e93df82a483c1640c81330edc524000173cc944ef0740000000000496a65440631b4ca269cea23f43fa8000dd0251000144000000000015181ec8f804080586d000046080005ea9c50001dc0aae5
  | 22 => 0x2884c000b4b0292300014d8aea25a21500001fc1510e380002441ba0000000a403e600000000001d644312280000001e2800000095d188000000071505e9bc85320a63a5155517000000025800000000000000fd091e00018a00009020c725ac0004761fd8d441c612b3d8903cf243234021d5800000000000000006910000000a0e0000000ab00009280001f251584072fc05051b845139100013d69f72a50118b327d11379f014169cc06c0ddc9725b5497879ca069ef0120388892083218a1e88ca1ac4570cf90de274430828c3b439e24a82f03685d73fb87f11d800000000007346663fa1f510ae50139f000000084604810900000002ec1350f0e7250001f3ce8477f4dd00000003e700015dc4cc5a20918b8c7fa60e0af0ba84043c33c892d80fa4601c8a5c8c648940ab8c68b0013e000000101600016f22993380004b19c100003a5000000056249e2f917652309644cc80000004ac2199050f649300ad0e852da0000001bed2fc0361508b10ebe2cd03f1b9c00042900000000000003448000e3800000025b90300004cd000000076547c800020601004600003da9dc32a000000058600019b40004781ada7486e07ea0000370000152000000000016641000005dc40800000bc8d834d0001db0cd275b0fba77c00037104d20a80006730ae95bcdbe8e336694f008027e0f91a2c9705a83ba01713263164d68decb127c80c896d91505953799b54c6a71e4c80e286644181da9b007940b220da77912000046700009bc1bd4318000000410415a5704f21402871c080002d41f205110489d72728d308f80180781a5103c8fe02f0000e4800021a8e000009b72e388e0d8a0000770d400008eb2da0104000000000000114e8773ee1bdccc8812000280c0006a600006c00001ad0e5862c0b260100ba3dc4d87ab4cf87247da2bb3c794506505e43d217c40000003148000654205000060c1725f023f99580940621558000df2000390a6c87544574851af8cae8c737818342780003d31550e0260a32e80004e6039502189423800006219a8fec09e00f0674000000328913851c7e133f0b5cc666b6152a71c00000000011788ee42c1371fc058c77607b88340000004fa06310ac92045107e0b6e4b532911d000e4c61169ac416a65c0000000f7400035980005f888e4e70000e6ca011e580000007af000000131e5e21258e54a762a01ca0d5c6ba59410905f80000000c51298f2a2814a70f380007ef3631da11e81d912100000005283538000fdc4ea22500001e49ea25e0a7800034722d80000006a900014fc00000000006e000053316a90040006984e780000b467600008d843258528916ac1545924bf8728e6811b1c10000c9c58f30c1fecb524e7203247400012c2bf052504467f076263025c1c6245912cd04000416a0e40004ec2280
  | 23 => 0xfc85448193e397f12ee7c6417800000006807080a4b3617c437199cc767373d1217c1221774d280000561430e2a10c72e000000244120600000013553ec00039700005ca3dd03b82b0d746422461f98e608c622186246849812b88a0ca5e2921c218440163984f28c545b47ec160991922e2240701d3d1404e0124253527240b0950d3909c4d10a2a66075299119c09e0c4e3780dd9d885701ec1292044c5e22e1ba9c4106a9c406297d805833624d91980000000a68000000000000162078859e4ed80006388b725880946445250929ee0da877a1c302e111064b4dca1b49605432af04f42402dc22c0b6cab271f452244c7de3ba21a1c687585e31359aa90ba15812210841860c032d0d10a084eb06f9b68aa239c024013c0368622eb0cfc79a59c174114c264858000049862664532980002047ae2ee91f80001790000000f6c51e444915425e0002449b6c1f80001bf99d453a8664a3a2650e248629380e000000032480009cc00000025100002d906417e80008253c623f0df800034a89d89027894768a4413e7a141c01246e4548052a3c867219449b98010846e2100a54d1fe5db15f19bcab8a0e09b9af505c9573ae969524e0d0362051862845a2e2a1342529521b611704405ad2710194d4641345814010923630000000b1c0003ff2808f4e000346800125211102b249000096f13f800000062e0001e0c8564d240721c0b143044460eb53487df2afa2bcfca9313f11ab0f1c2bf09a98e02b68e60f72430c9004b1d7a5884bc5443de1ca40005c320194f83327c530f8db8e0a8021a918d0ef8234400923c0003c800023a0af485907c204c63c168029a7b45c481f00024e0f3e6b513e8ba529691f2c18fa01309062669e6846644f49e00006c270e2b1223c1e6471000037451a2901c294684942d200010991b60fa03b20b098484134c8004a5a04c00019a000050f3ed9cd410a83d1faa6ac5d88e02df01fd2e016c1700d249ac6044668c6487e9d11ac14452ce6ec0151f2d11422c38613a0bea6fd18310e834e3174f4a0180007c2347889d1221963bba08422e1182bc05a80000e72ad8cb506e98e2a690b85c823d2768c80f886c94c396b92d254127da5141084cb4f819d0a929094261f488225c81579bb8ba48f52bd878054819a1de23908002fe0671e04b582e630d87953823e546f153821c76919d096cd9619c1049cb04782f74db0e7c2b88142c38be40ea287000108cfb009333e11086528471819d413f889d39c0000a802933f01190ce278b37a9d6131038b00006e47fe0000001f8c00055000026240000ef2f0828400000001d9e1876273f3a49cb45608a32191a900001c31888000a0a000000000119897549701384208bc29d04342a69964f1835415a1f028e8e30b7e81015a010cf2859f22a1e10d3e41544007d4702
  | 24 => 0x9d331b99ed2d03f10001b38c1e0000001df873668800006207ec49f1f992480e600041894582ca5c200000000006c11a990141ae1fa3fe81b40000000000000b5494c06b1258d186d634324ed16800000005f51ae00008022a400066c000000112c000000000000000000000003a85b9123029c0008b900013d40008c80001a810d61392f7077c0009c300000000002ce1fe07eca18590000000012c0bb2948430c823c214f8588db852b2539dd400043d000000000000000020f89c890d3d80e4ccc608d4421cc44ce0003a9110057489c368a3ecd0630c00006806de8b21308ad40009ae23581c48767cc4ea13708ba0000a40d883ba0ba00011bd21e6901de989824e101491015c6660000000000cb60002ba047400000009c11c04866e50001584dc05ba00000006a81db00003b4a621a6383239442e0000a700d0bce97800007543d06e332a946102e08948427b08387480d200544725353660f3c0346c733ba1f0f5844433815c80505c10001d902985f340ea6fc55c609179232822825927d00000ba5ce4d01864ee6000000113000000000019400006f41a280000009362c992dc00056700000000f884f000254100087b07886f0c6c853211069471e1fe3e18000594309361a60924a09522316440003fe1ea1d18e3a32b4a006a885e9f200009c800000048d27743989481610a6c0000110000fa43a40b44dc05eceaa000000198019e52126980009d245f4bd01e4ba02f84569d14f402b61f0866c41432f33d0018ece7eb3bc8fa8de243927f136c1a68be2e50cc0bd233c21e1d8468262c2268d54e2c27104b9ee471a40a1eba6f5126754439839540c1f930825b0e560b630b888488a56818e808824870745f9240b962823fe151540a2ef16f933c0065da184130510a09c0091db4f6e00c045233c37c297118237d27a6201789e40afe8f607f88e8e9a1f41709ed40002cc23400009860e401800000b69da29b80d45ec052001000097c0000000b4c000000318
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x30000014260089718180002a003a03820d8d42245161e48f1900048040000580040001d0000c0e3e000000a680010030800c00440c100698609811836550c0181c8420d70594430064621470dd94310c0141d96d437650c430044726150dd94310c0141e971d77650c4300507a5f50dd94310c0181d86ddb7550c4300447a5f80dd54310c01c1b761c37550c4300507a5f60dd54310c0181c87dd96550c430044725d805954310c01918871c16550c4300706dd8705954310c01a1b805816550c4340d26a5f86dc14310c0151a97e177050c4300546a5c85dc14310c0191a872177050c4300706ddb75dc14310c0191a871d77050c4300706dd965dc14310c01e2350481105902100788541204416408401e43504811058c210079054120441630852546697e17764842122d19a5c85dd9210840196180dc37548421006511d6839d1210840192475a1273484210045925d8510d2108401a858650c4348421
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x6
  | 3 => 0x2
  | 4 => 0x209
  | 5 => 0x3
  | 6 => 0x20e
  | 7 => 0xb09
  | 8 => 0xb0e
  | 9 => 0x1409
  | 10 => 0x140e
  | 11 => 0x1549
  | 12 => 0x154e
  | 13 => 0x249
  | 14 => 0x4
  | 15 => 0x24e
  | 16 => 0x16c9
  | 17 => 0xb49
  | 18 => 0xb4e
  | 19 => 0x1449
  | 20 => 0x144e
  | 21 => 0x16ce
  | 22 => 0x289
  | 23 => 0x5
  | 24 => 0x28e
  | 25 => 0x1849
  | 26 => 0xb89
  | 27 => 0xb8e
  | 28 => 0x1489
  | 29 => 0x148e
  | 30 => 0x184e
  | 31 => 0x3c9
  | 32 => 0x3ce
  | 33 => 0x1709
  | 34 => 0xcc9
  | 35 => 0xcce
  | 36 => 0x15c9
  | 37 => 0x15ce
  | 38 => 0x170e
  | 39 => 0x409
  | 40 => 0x40e
  | 41 => 0x1889
  | 42 => 0xd09
  | 43 => 0xd0e
  | 44 => 0x1609
  | 45 => 0x160e
  | 46 => 0x188e
  | 47 => 0x589
  | 48 => 0x58e
  | 49 => 0x1789
  | 50 => 0x18c9
  | 51 => 0xe89
  | 52 => 0xe8e
  | 53 => 0x178e
  | 54 => 0x18ce
  | 55 => 0xb0211
  | 56 => 0x20b11
  | 57 => 0xb0216
  | 58 => 0x20b16
  | 59 => 0x184211
  | 60 => 0x184b
  | 61 => 0x21851
  | 62 => 0x184216
  | 63 => 0x170211
  | 64 => 0x170a
  | 65 => 0x21711
  | 66 => 0x170216
  | 67 => 0x3ca
  | 68 => 0x28b
  | 69 => 0x164a
  | 70 => 0x14cb
  | 71 => 0x3d411
  | 72 => 0x1403d1
  | 73 => 0x171411
  | 74 => 0x141711
  | 75 => 0x171416
  | 76 => 0x29551
  | 77 => 0x154291
  | 78 => 0x185551
  | 79 => 0x155851
  | 80 => 0x185556
  | 81 => 0xb4251
  | 82 => 0xb4256
  | 83 => 0xcd6d1
  | 84 => 0x16cb51
  | 85 => 0xb56d1
  | 86 => 0x16cb56
  | 87 => 0xb5711
  | 88 => 0xccb51
  | 89 => 0xccb56
  | 90 => 0xb4cd1
  | 91 => 0x170b51
  | 92 => 0x170b56
  | 93 => 0x17ca
  | 94 => 0x16d451
  | 95 => 0x1456d1
  | 96 => 0x16d456
  | 97 => 0x1716d1
  | 98 => 0xb8291
  | 99 => 0xd1851
  | 100 => 0x184b91
  | 101 => 0xb9851
  | 102 => 0xb9891
  | 103 => 0xd0b91
  | 104 => 0xd0b96
  | 105 => 0xb8d11
  | 106 => 0x188b91
  | 107 => 0x185491
  | 108 => 0x149851
  | 109 => 0x185496
  | 110 => 0xd1856
  | 111 => 0x189851
  | 112 => 0x104a
  | 113 => 0xcc3d1
  | 114 => 0x170cd1
  | 115 => 0xcd711
  | 116 => 0x1715d1
  | 117 => 0x15d711
  | 118 => 0x1715d6
  | 119 => 0xecb
  | 120 => 0xd0411
  | 121 => 0xd0416
  | 122 => 0x188d11
  | 123 => 0xd1891
  | 124 => 0x188d16
  | 125 => 0x194b
  | 126 => 0x189611
  | 127 => 0x161891
  | 128 => 0x189616
  | 129 => 0xe8591
  | 130 => 0x58e91
  | 131 => 0xe8596
  | 132 => 0x58e96
  | 133 => 0x178591
  | 134 => 0x18c591
  | 135 => 0x178e91
  | 136 => 0xe9791
  | 137 => 0x178e96
  | 138 => 0x18ce91
  | 139 => 0xe98d1
  | 140 => 0x18ce96
  | 141 => 0x18d791
  | 142 => 0x1798d1
  | 143 => 0x18d796
  | 144 => 0x198a
  | 145 => 0xa4a
  | 146 => 0x44a
  | 147 => 0x94b
  | 148 => 0x98a
  | 149 => 0xa4b
  | 150 => 0x198b
  | 151 => 0x20956
  | 152 => 0x20996
  | 153 => 0x216d6
  | 154 => 0x21716
  | 155 => 0x21856
  | 156 => 0x21896
  | 157 => 0x2cb
  | 158 => 0x25556
  | 159 => 0x5ca
  | 160 => 0x138b
  | 161 => 0xb5716
  | 162 => 0x150a
  | 163 => 0x74b
  | 164 => 0x148956
  | 165 => 0x149856
  | 166 => 0x184d16
  | 167 => 0x15c996
  | 168 => 0x15d716
  | 169 => 0x41416
  | 170 => 0x592d6
  | 171 => 0x59316
  | 172 => 0xe9696
  | 173 => 0xe9816
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2086
  | 6 => 5004
  | 5 => 2575
  | 4 => 34
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
  | 7 => packedAt gbK7 (85522+((h/695+packedAt gbK7 (77182+(h % 695)*12) 12) % 3029)*13) 13
  | 6 => packedAt gbK6 (261876+((h/1668+packedAt gbK6 (240192+(h % 1668)*13) 13) % 6605)*14) 14
  | 5 => packedAt gbK5 (162221+((h/858+packedAt gbK5 (151925+(h % 858)*12) 12) % 3091)*13) 13
  | 4 => packedAt gbK4 (2446+((h/11+packedAt gbK4 (2380+(h % 11)*6) 6) % 53)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xf0783fc3ffffe1fffff8002e347e013f3fc
  | 1 => 0xfff007fc3fc1e01fe1f00fffcd3c8678eccccf
  | 2 => 0xfffff8003ffe001ffe000ffff1c0f87f0f0f0f
  | 3 => 0x1ffffffc000001ffffff0003e00ff87f00ff0
  | 4 => 0x1ffffffffffffe0000000003fff0007fff000
  | 5 => 0xfe00000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x300100804c1328c612946c81806142e001515c
  | 1 => 0x525003a41441414b21a0a52a842c862864c4c5
  | 2 => 0xa4a748002ab4029454014a5511c058530b0b0a
  | 3 => 0x413a956a80000419894b80062e00ad05b00ea0
  | 4 => 0x81cce65333289700000200183b960006dea000
  | 5 => 0xf800c06202311801118c0c603ffbf7f8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefac0feeaeac0feeefac0feeaeac0feeefac0feeaeac0feeefac0feeaeac0feeefac0feeaeac0feeefac0feeaeac0feeefac0feeaeac0feeefac0feeaeac0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37339
namespace PEqualNP.Outside.L_meta_37339
open PEqualNP.Outside.L_meta_37339.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 25 := bs0_3_0
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
theorem bs0_4_128 : Interval s0Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_160 : Interval s0Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_192 : Interval s0Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_224 : Interval s0Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_256 : Interval s0Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_288 : Interval s0Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_320 : Interval s0Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_352 : Interval s0Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_384 : Interval s0Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_416 : Interval s0Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_448 : Interval s0Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_480 : Interval s0Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_512 : Interval s0Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 539 := (concat (concat (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 bs0_4_96)) (concat (concat bs0_4_128 bs0_4_160) (concat bs0_4_192 bs0_4_224))) (concat (concat (concat bs0_4_256 bs0_4_288) (concat bs0_4_320 bs0_4_352)) (concat (concat bs0_4_384 bs0_4_416) (concat bs0_4_448 (concat bs0_4_480 bs0_4_512)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_64 : Interval s0Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_96 : Interval s0Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_128 : Interval s0Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_160 : Interval s0Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_192 : Interval s0Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_224 : Interval s0Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_256 : Interval s0Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_288 : Interval s0Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_320 : Interval s0Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_352 : Interval s0Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_384 : Interval s0Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_416 : Interval s0Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_448 : Interval s0Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_480 : Interval s0Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_512 : Interval s0Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_544 : Interval s0Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_576 : Interval s0Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_608 : Interval s0Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_640 : Interval s0Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 664 := (concat (concat (concat (concat bs0_5_0 bs0_5_32) (concat bs0_5_64 (concat bs0_5_96 bs0_5_128))) (concat (concat bs0_5_160 bs0_5_192) (concat bs0_5_224 (concat bs0_5_256 bs0_5_288)))) (concat (concat (concat bs0_5_320 bs0_5_352) (concat bs0_5_384 (concat bs0_5_416 bs0_5_448))) (concat (concat bs0_5_480 (concat bs0_5_512 bs0_5_544)) (concat bs0_5_576 (concat bs0_5_608 bs0_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_32 : Interval s0Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 40 := (concat bs0_6_0 bs0_6_32)
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
theorem bs2_3_0 : Interval s2Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 4 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 12 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 23 := block_range (n:=23) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 23 := bs5_3_0
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
theorem bs5_4_352 : Interval s5Atlas 4 352 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 379 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat bs5_4_288 (concat bs5_4_320 bs5_4_352))))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 586 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 bs5_5_96)) (concat (concat bs5_5_128 bs5_5_160) (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)))) (concat (concat (concat bs5_5_288 bs5_5_320) (concat bs5_5_352 (concat bs5_5_384 bs5_5_416))) (concat (concat bs5_5_448 bs5_5_480) (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)))))
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
theorem bgb_4_32 : Interval gbAtlas 4 32 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 34 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_2560 : Interval gbAtlas 5 2560 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2575 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)))))) (concat (concat (concat (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408))) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)))) (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888))))) (concat (concat (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)))) (concat (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368))) (concat (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)) (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)))))))
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
theorem bgb_6_4992 : Interval gbAtlas 6 4992 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5004 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 (concat bgb_6_384 bgb_6_416))) (concat (concat bgb_6_448 bgb_6_480) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))))) (concat (concat (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)))) (concat (concat (concat bgb_6_928 bgb_6_960) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056))) (concat (concat bgb_6_1088 bgb_6_1120) (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)))))) (concat (concat (concat (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)) (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504)))) (concat (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664))) (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824))))) (concat (concat (concat (concat bgb_6_1856 bgb_6_1888) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984))) (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144)))) (concat (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304))) (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464))))))) (concat (concat (concat (concat (concat (concat bgb_6_2496 bgb_6_2528) (concat bgb_6_2560 bgb_6_2592)) (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)))) (concat (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912))) (concat (concat bgb_6_2944 bgb_6_2976) (concat bgb_6_3008 (concat bgb_6_3040 bgb_6_3072))))) (concat (concat (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232))) (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392)))) (concat (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552))) (concat (concat bgb_6_3584 bgb_6_3616) (concat bgb_6_3648 (concat bgb_6_3680 bgb_6_3712)))))) (concat (concat (concat (concat (concat bgb_6_3744 bgb_6_3776) (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872))) (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032)))) (concat (concat (concat bgb_6_4064 bgb_6_4096) (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192))) (concat (concat bgb_6_4224 bgb_6_4256) (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352))))) (concat (concat (concat (concat bgb_6_4384 bgb_6_4416) (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512))) (concat (concat bgb_6_4544 bgb_6_4576) (concat bgb_6_4608 (concat bgb_6_4640 bgb_6_4672)))) (concat (concat (concat bgb_6_4704 bgb_6_4736) (concat bgb_6_4768 (concat bgb_6_4800 bgb_6_4832))) (concat (concat bgb_6_4864 bgb_6_4896) (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992))))))))
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
theorem bgb_7_2080 : Interval gbAtlas 7 2080 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2086 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))))) (concat (concat (concat (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152)) (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280))) (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536)))) (concat (concat (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 bgb_7_1664)) (concat (concat bgb_7_1696 bgb_7_1728) (concat bgb_7_1760 bgb_7_1792))) (concat (concat (concat bgb_7_1824 bgb_7_1856) (concat bgb_7_1888 bgb_7_1920)) (concat (concat bgb_7_1952 bgb_7_1984) (concat bgb_7_2016 (concat bgb_7_2048 bgb_7_2080)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefac0feeaeac0feeefac0feeaeac0feeefac0feeaeac0feeefac0feeaeac0feeefac0feeaeac0feeefac0feeaeac0feeefac0feeaeac0feeefac0feeaeac0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074624 * 2 ^ 32 + 4276808384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37339.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.and,[2,3]⟩,⟨.or,[3,4]⟩,⟨.or,[3,5]⟩,⟨.and,[6,7]⟩,⟨.and,[4,9]⟩,⟨.or,[2,11]⟩,⟨.and,[1,12]⟩,⟨.or,[0,10]⟩,⟨.and,[8,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074624 * 2 ^ 32 + 4276808384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074624 * 2 ^ 32 + 4276808384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37339

open PEqualNP.Outside.L_meta_37339 in
theorem PEqualNP.Outside.L_meta_37339 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074624 * 2 ^ 32 + 4276808384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074624 * 2 ^ 32 + 4276808384) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
