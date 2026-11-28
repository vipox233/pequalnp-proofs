import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37233.Model
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


end PEqualNP.Outside.L_meta_37233.Model

namespace PEqualNP.Outside.L_meta_37233
open PEqualNP.Outside.L_meta_37233.Model
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

def SBf (j : Nat) : Nat := [7, 6, 7, 7, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_37233

namespace PEqualNP.Outside.L_meta_37233
open PEqualNP.Outside.L_meta_37233.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x1200f800c690174a00000101422a26053ab420131944606230008691140d49b2854e9238787875058010009058e001032001d200638a1520c1ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x12380000500c04005c9e14260060001800440a5a008a4e002200ae0090a0b4400016000200009c78009874009600003a00005210640082005600000062000000006a000608007a340000926c004800002c002a240000322800b6000000aa6e365e00000000b27094008e88540000000000000000a81a1c76000030002e20589a683c84ac72807e4aa68ca23e00000000000000a4b046007c00421e4c66860e00000102010002080206070000000200000800080103010101010000020c050eb7a92876c5250ebea6a15714d429faa2653c544cb9a64194f943419eaa4835f53506b8a6a0dbd4941b6292837b50506f0a0a0e7d4d41ce29a83af5250758a4a0edd4541dda82833c5050770a0a0ce141419f2a0836e52cc6daa598cf952319eaa4636e528c6daa518cf950319eaa0635e53c86baa790cf952219eaa4435e53886baa710cf950219eaa0435e53902baa7205b94a40b6a94819e539033aa7206b94a40d6a94813d519027ca1204f544409f28081ba501027ca9984f553309faa2613c544c2dea4985b14930bba8a6174514c2dca4185b548309f2a6413d54c827ea8904f15120afa9a415c53482eea2905d14520af298415d530827ca9884f55310dc206213f5484278a9084fd51109e2a2215f53442b8a6885bd4910b6292213e540427aa8085794c10aea98216e52042daa4086e10010
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xe04002086ca70a3191320cb0c5314941c6d4c50507185314141cad4850507285214141c394e52902396510010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | 3 => packedAt s0K3 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (788+((h/14+packedAt s0K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s0K4 (2724+((h/30+packedAt s0K4 (2484+(h % 30)*8) 8) % 161)*8) 8
  | 3 => packedAt s0K3 (312+((h/2+packedAt s0K3 (304+(h % 2)*4) 4) % 12)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffff81fffffe07ffffffffe03fffe3ffe3f
  | 2 => 0x3f81ffffffffffff81f03e07ffffffffc88fff
  | 3 => 0x3ffe03ffe03f81fffe003ff83ffc1f01f0f3cc
  | 4 => 0xc00003ffffc001ffffffc0003fffe001ff03f0
  | 5 => 0xfffffc00000001ffffffffffc0000001fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x84882808c489082016514a284a212954133615
  | 2 => 0x11245191091260c580a4148694c652a8c888ea
  | 3 => 0xa6149aa243a42b6aaa0927b227691c0d70d34c
  | 4 => 0x3459634492074db34d3d812439b38831bd03b0
  | 5 => 0x386183871c3871dc71ce39c701c210c1eeec00
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0fcccccc0f0c0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37233
namespace PEqualNP.Outside.L_meta_37233
open PEqualNP.Outside.L_meta_37233.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x1024a041c4022c0050cc0027bf43bd43bf42bd42f731f431f721f421be40bc40f710f510
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x100018000000003800000000000004140002406080020000080025aa5a1c754f42b32966395430c6aca790e9508218ea98812d52102a8a6885914910
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 10
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
  | 3 => packedAt s1K3 (288+((h/3+packedAt s1K3 (270+(h % 3)*6) 6) % 42)*5) 5
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff83ffffffe07ffffffff03fffff1ff1ff
  | 2 => 0x81f03ffc0f83e0ff8f0783e0ffc3c1e0eacecc
  | 3 => 0xfe003ffff003fffff007fc00fffc01fff30f0f
  | 4 => 0x3ffffffc00fffff80000fffffe00fc0ff0
  | 5 => 0xffffc000000000ffffffffff00000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x84000088200000000108842210044422005055
  | 2 => 0x2c665918e52549658743a34676428d466ac6cc
  | 3 => 0x18aaaa21434a98aab0856908aaa8119cb30b0a
  | 4 => 0x514d34428a60d2d35ad04210cd333808dc0da0
  | 5 => 0x618e38730c731cfc6ce6739c0e222110ffa000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafaaaaa00faaaaaaafaaaaa00faaaaaaafaaaaa00faaaaaaafaaaaa00faaaaaaafaaaaa00faaaaaaafaaaaa00faaaaaaafaaaaa00faaaaaaafaaaaa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37233
namespace PEqualNP.Outside.L_meta_37233
open PEqualNP.Outside.L_meta_37233.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1e4c40b32251a80000301001071f00003800474a18540001b205400500596004a01300005d10a06480000084d005244000009002b3830f271a80201800000389240c086000c081ff43fe43fd43fc43ff42fe42fd42fc42ff32df32fe32ee32fd32dd32ed32cd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xb0001c0a8285e120805e7602928aa713c1d44c7c0011cc62d0789c4269098001a671b1dc0200001807a3f1a0742262380c4d60000000de720c8309e00039fcb85428000007b000004400049a000230f8008a4e00144041800000000024198004300100346a1900000001b858960036800ca173a104c87907028e62e3f124722c3d1743c6e00048525a15800001b0e10876000216c0000220d420591f00000252b00c0c4c2f800006c2b8209a803e854a64600000500019800603a1e1841652048002018700808080018000030001828010000084018e810085008d8101808102858008010000010204005b94a43b6a9487765190eeaa321db94843b6a90875e5390abaa7215d94642baa8c855e5310abaa6215754e32b6a9c654d538cb9ea49973d0932e721265cd424cb98849973d4d32e7a1a65ce434cb9a86997310d32e7aa265ce544cb9aa8997315132e7a8a65ce514cb9aa2997314532e7a8265ce504cb9aa0997314132af298656e520cb9a64195794f41aea9e836e52d06daa5a0f34cb41af29c835d53906dca520db54a41e699483cd325079a6420ed504419f2a6633d54cc6dca598db54b31e699663cd328c79a6498db94831b6a9063cd320c67ca990cf55321af29e435d53c879a6590f34ca21e6992435e53086baa610f34c821e699681cd32902bea6a05714d40b7a92816c525039a64a05dd4540ba28a815e53102baa6205b94840b6a9081cd32102eca2205d54440b7296616d52cc39a6598734ca30e6992613e540c27aa8185b94830b6a9061cd320c2eca2185d54430af29e415d53c839a6590734ca20e6992413e540827aa8105794c20aea9841cd32082eca2105d54420e699621cd328427ea8884f15110afa9a215c53442dea4885b14910e6992213e540427aa8085794c10aea98216e52042daa408734c810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x5600003c000000006e08000022001c640a000000800044003a001a006c0000001e000000000000700c045c3400006a7a00000052500000546618003e005a862e2c3000844658622a0640020028267c00123810720e7800004a487e4c00003200004e00005e0000000068764216242036140000000000820000000000000000000074000060000000000401010100010c0100000301020500000000000200b1986424cac56190932b1986434cac56190d32b1987544cac561d5132b1986544cac56195132c3550544ca8e64d4532a3593514ca8e6494532a3592514cb455114532a3d91504ca8c6454132b1d85504cac46154132a3990504ca8d6414132b1984504cac561141329358a53d064d6394b4193d9532d064d654cb419358a539064d6394a4193d95329064d654ca41e14c9411070e544cb31c355132cc70e544cb21c355132c864d6214d409358c525024e654c94093195325034532d4540d14c8515024d6294c409358e521024f654c8409359532103453294440d14c9511030e544c830c3551320c3453294430d14c9510c24d6254c20c3951320830d544c820d14ca5108345325442093588534424d631491093995324424c654c910c3d51324430c544c9109358a530424d639481093d95320424d654c810c3951320430d544c810
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (825+((h/15+packedAt s2K5 (720+(h % 15)*7) 7) % 66)*7) 7
  | 4 => packedAt s2K4 (3827+((h/43+packedAt s2K4 (3483+(h % 43)*8) 8) % 170)*9) 9
  | 3 => packedAt s2K3 (2760+((h/22+packedAt s2K3 (2584+(h % 22)*8) 8) % 141)*8) 8
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfc3ffffffffffff03f07f07fffffffff223fff
  | 1 => 0xffc1f0f83e0f83ffc7f87f870e0f0f0fddd293
  | 3 => 0xfffe00ffc00ffc3ff8007ff80ff00ff0e1e31c
  | 4 => 0xfffff0003fffff80000ffff000fe03e0
  | 5 => 0xffffff000000003ffffffffff0000000fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x4000008000000000000800900110100000425
  | 1 => 0x2894611194551512c3283282268a2a2e4cd292
  | 3 => 0xb10caaa28d6a517558a45b504ba84ce2e16318
  | 4 => 0xa3a94cc5294359b9adb50a408dcce844f603c0
  | 5 => 0xc2318886318c622e36c66c64e1008088bbb800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaaaaaaa88eeeeeeaaaaaaaa88eeeeeeaaaaaaaa88eeeeeeaaaaaaaa88eeeeeeaaaaaaaa88eeeeeeaaaaaaaa88eeeeeeaaaaaaaa88eeeeeeaaaaaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37233
namespace PEqualNP.Outside.L_meta_37233
open PEqualNP.Outside.L_meta_37233.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x15a51a440001000ba8003021b0c800002498503122ce212600aa352507813400000007c3800058022309cc8000015003c74702480080500000040401007043100043ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x16071ba22d2783a59d05aca3a88e0b2d888f1682a52990129e180019910186002a80000000000a24ab032b80090014809713a720800415001f8d05000d95800e8aa900021f26a3118c1219011304909e9c800980001d80260024142297a18f88079b2c0021189a8ca01c1a2a280b868c8602005810a0818220280042a2c08110001813404785ae28003cea18876e5210edaa421d794c42aea98853e540ca7aa8195794f41aea9e836e52d06daa5a0d794e41aea9c836f52506d8a4a0cf953319eaa6636e52cc6daa598cf952319eaa4636f524c6d8a498db94621b6a84433e540867aa810d794c21aea98437a50086f2a010eb95021d6aa043ce530879aa610db94421f328843ea50086daa010fa54021b4a80436e52902daa52057d4d40ae29a815e53102baa6205b94840b6a90817651102eaa2205b94a30b6a94613f544c278a8984f950309eaa0616e520c2daa4185d94430baa88613e54c827aa9905794f20aea9e41ae54c835aa9907394f20e6a9e416e51c82daa5105b14520f5a82416e52082dea5885b14b10b7294216d52843d241084fd51109e2a2215f53442b8a6885bd4910b629221e9204427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2080004e0a6c004c350d5210f0d5454c21ca95150087295454021d294d50087495354021c355153c82686548110
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
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (788+((h/14+packedAt s3K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s3K4 (2694+((h/30+packedAt s3K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s3K3 (312+((h/2+packedAt s3K3 (304+(h % 2)*4) 4) % 13)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xc1ffff83ffff0f07f0fe1fffc3fff81e89f3f3
  | 1 => 0xfe1f0ffc3e1ffff87f0fe1c1fc383fff764c9f
  | 2 => 0xffe00fffc01ff1ff800ffe01ffc03fe1878f1c
  | 4 => 0xfffffe001fffff00001ffffc001f80fe0
  | 5 => 0xfffff000000001fffffffffe00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x44020088040010008012024440488844009131
  | 1 => 0x88841110902a00283104208884111298324486
  | 2 => 0x144aaa290d548353888b54156a82a545858b18
  | 4 => 0x3954cc42a906a59d5aa11021b3270189d80ec0
  | 5 => 0x219888733198c9e66ccd993822040611ef6000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeaeac8c8eeeeeaeaeaeac8c8eeeeeaeaeaeac8c8eeeeeaeaeaeac8c8eeeeeaeaeaeac8c8eeeeeaeaeaeac8c8eeeeeaeaeaeac8c8eeeeeaeaeaeac8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37233
namespace PEqualNP.Outside.L_meta_37233
open PEqualNP.Outside.L_meta_37233.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x9300000000e00c96007c00000340004eac01e0038002484140c3a9428000280112ea44183811506004819a4c24022408cd8b42540141e3400c0004040001000000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x229001f1804991e9a8026ac952a8192ad898001260017212b2c0ca3a31b2b90078fad1888140e179c1a0687002803a71b8b919616920885a513aa0f0b25a21100201e29a099801f82a88624131da4a28a0000000014890c0010800403009d001c800015a180000e8a800527800d8d01010e092814a0010200140080a1c61404d00000c080000c24b00cea18876e5210edaa421d794c42aea98853e540ca7aa8195794f41aea9e836e52d06daa5a0d794e41aea9c836f52506d8a4a0cf953319eaa6636e52cc6daa598cf952319eaa4636f524c6d8a498db94621b6a84433e540867aa810d794c21aea98437a50086f2a010eb95021d6aa043ce530879aa610db94421f328843ea50086daa010fa54021b4a80436e52902daa52057d4d40ae29a815e53102baa6205b94840b6a90817651102eaa2205b94a30b6a94613f544c278a8984f950309eaa0616e520c2daa4185d94430baa88613e54c827aa9905794f20aea9e41ae54c835aa9907394f20e6a9e416e51c82daa5105b14520f5a82416e52082dea5885b14b10b7294216d52843d241084fd51109e2a2215f53442b8a6885bd4910b629221e9204427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x8c0e0600a4000202c350d5210f0d5454c21ca95150087295454021d294d50087495354021c355153c82686548110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (788+((h/14+packedAt s4K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s4K4 (2694+((h/30+packedAt s4K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s4K3 (312+((h/2+packedAt s4K3 (304+(h % 2)*4) 4) % 15)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc1ffff83ffff0f07f0fe1fffc3fff81e89f3f3
  | 1 => 0xfe1f0ffc3e1ffff87f0fe1c1fc383fff764c9f
  | 2 => 0xffe00fffc01ff1ff800ffe01ffc03fe1878f1c
  | 3 => 0xfffffe001fffff00001ffffc001f80fe0
  | 5 => 0xfffff000000001fffffffffe00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x44020088040010008012024440488844009131
  | 1 => 0x88841110902a00283104208884111298324486
  | 2 => 0x144aaa290d548353888b54156a82a545858b18
  | 3 => 0x3954cc42a906a59d5aa11021b3270189d80ec0
  | 5 => 0x219888733198c9e66ccd993822040611ef6000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaeac8eac8eeeaeeeaeac8eac8eeeaeeeaeac8eac8eeeaeeeaeac8eac8eeeaeeeaeac8eac8eeeaeeeaeac8eac8eeeaeeeaeac8eac8eeeaeeeaeac8eac8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37233
namespace PEqualNP.Outside.L_meta_37233
open PEqualNP.Outside.L_meta_37233.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x40b0b8952082160000c800014018009912a1a1d2060094a832038fa700700945aacf1214007884244d0c2674da8008c5890882820122001c20c11ccff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x38157011145a00191b21561f0000496955000064672f003400004a04006f006e304c4f3e396c71455f545b121d104d5e230048003f00006a520000070a40240c0d5808005c4702662b0000000000510000010e32002d18311e3d3a00000028722a6300570f330000001c0900615d0543170050730b3b006d3c6813224e602e4400362520163700410026354603594262744b296500272c531a066b008500800003000002850581808080010480010780118385808304000101830681808004010403e750c43bb28887755110ebca7a15754f42bb28e857551d0a7ca9994f55332bb28e657551cca7aa920d794e41aea9c836f52506d8a4a0ebd4941d629283b7515067ca820d794c41aea98839f41cc73a8398cf952319eaa4635d538c76a8318dbd4931b629263b5414c79ea498f314931eba8a639f414c7ac8298e750531eaa0a6395414c67ca818cf55031af29863b541c87aa6390cf952219eaa4435e53886baa710cf950219eaa0435e53086baa610ed50421ea988437a50086f2a010db94a40b6a94815f53502b8a6a05794c40aea98816e52102daa4205d94440baa88816e528c2daa5184fd51309e2a2613e540c27aa8185b94830b6a906176510c2eaa2186bd0720d6a0e41cf31c839a63905b54a209faa2413c54482bea6905714d20bba8a4174514835ea8906b15120e7a9a41cc53483cea2907914520d7a0a41ad414839e6290734c520f5a82416e520827ca9884f55310af29e215d53c436a8388754c710b7294216d52843d241086d50510ea98a21e9204427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x60068e88252c710812b80a9ea2629602410020600000c00068198a1c550d5110f245250531a5592414c6c46250531e1d89414c7846250531e1d49414c7845250531c554d4108715544c421cc505500875131540219558453502356115130e150531c83245414520d114c514822c6550520931953148385414c520c554d41c4315544c710e850520443c13148110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xa0c00a0cebb128298c8676d49414c6823aa8298a4181195414c520
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 4 => packedAt s5K4 (3471+((h/39+packedAt s5K4 (3159+(h % 39)*8) 8) % 155)*8) 8
  | 3 => packedAt s5K3 (952+((h/8+packedAt s5K3 (912+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s5K2 (199+((h/1+packedAt s5K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x83ffff07fffe1f0787fe1fffc3fff81e19f3f3
  | 1 => 0xfc3e1ff87c3ffff8070fe3c1fc783fff164c9f
  | 2 => 0xffc01fff803fe1fff80ffc01ff803fe1e78f1c
  | 3 => 0x1fffffc001fffff00001ffffc001f80fe0
  | 4 => 0xffffe000000001fffffffffe00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x88040110080020008012044440888844009131
  | 1 => 0x110932212255112843852288a4511299124486
  | 2 => 0x2894445218a80253880a48154902a544658b18
  | 3 => 0x72a99885520d559d55a10221b2670189b80ec0
  | 4 => 0x433110e6633199e666cd933820440611df6000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfaeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8faeaeac8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37233
namespace PEqualNP.Outside.L_meta_37233
open PEqualNP.Outside.L_meta_37233.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x13d54f12b11e397913e01c2c00d401c0001139168c6006c0522b4034028361d0b06e29a2e3a502b34c2493b06000322e01d2d2c9cc1900203000068f042a400135210540811630000240cc000e081800c50a0002ffd5009fe54007f55009fc5402ffd4c07fe53007f54c07fc53027fd0c07fe43007f50c07fc4302ffd4805fe52007f54805fc52027fd0805fe42007f50805fc4201ffcc805fe32007f4c805fc3202ffd4401fe51007f5440bfc51027fd0401fe41007f50409fc4101ffcc401fe31007f4c407fc31017fc8401fe21007f48405fc2102ffd4003fe50007f54003fc50027fd0003fe40007f50003fc4001ffcc003fe30007f4c003fc30017fc8001ef2000ff88001fd20007b48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x824001fb8c12000fda6090007ec3048003f70824001fa8412000fd8209001bff65c400d7fb2e2006ff9971002dfccb8801bfd65c40017eb2e2006ff19710035f8cb8801bff64c400d7fb262006ff99310025fcc98801bfd64c40017eb262006ff19310035f8c98803bff54c401bff2a62000ff5531006ff8a98801bff63c400d7fb1e2006ff98f1001dfcc78801bfd63c40017eb1e2006ff18f10035f8c78803bff53c4019ff29e2000ff54f10067f8a788037ff43c4019ff21e2000ff50f10067f8878801bff62c400d7fb162006ff98b10015fcc58801bfd62c40017eb162006ff18b10035f8c58803bff52c4017ff2962000ff54b1005ff8a588037ff42c4017ff2162000ff50b1005ff88588033ff32c4017ff1962000ff4cb1005ff86588006fe61c400dffa8e2006ff94710037eca38801bfd51c4001faa8e2006ff14710037fe838801bfe41c400dfb20e2006ff50710007ea838801bfc41c400dff98e2006ff8c710037ec638801bfd31c4001fa98e2006ff0c710037fe438801bfe21c400dfe90e2006ff0871000dfac188007ff50c4003ff2862001ff5431000ff8a188007ff40c4003ff2062001ff5031000ff88188007ff30c4003ff1862001ff4c31000ff86188007ff20c4003f79062001ff8831000ffa4188007ed20c4003fe1062001ff8431000fec2188007fa10c4003fe0862001fd04310007feca88002ff6544001bfb2a20009fd9510057fcca88016fe6544001feb2a2000bf59510057f8ca88016fc6544001be32a20059f19510007fec888002ff6444013ff3222004bf99110007fac888002fd6444013fe3222004bf19110057fea888027fe5444001feaa22009ff15110007fec688002ff6344011ff31a2003bf98d10007fac688002fd6344011fe31a2003bf18d10057fea688023fe5344001fea9a2008ff14d1004ffe8688023fe4344001fea1a2008ff10d10007fec488002ff624400fff3122002bf98910007fac488002fd624400ffe3122002bf18910057fea48801ffe5244001fea922007ff1491004ffe848801ffe4244001fea122007ff10910047fe648801ffe3244001fe9922007ff0c91000dfec28802bff514400dff28a2000fd94510007faa288003f5514400dfe28a2009ffd0510037fc8288003f64144001fea0a2000fd50510037f88288023ff314400dff18a2000fd8c510007fa6288003f5314400dfe18a2007ffc8510037fc4288003fd214400dfe10a2001bfd811000ffea088007fe5044003fea822001ff1411000ffe8088007fe4044003fea022001ff1011000ffe6088007fe3044003fe9822001ff0c11000ffe4088007ef2044003ff1022001fe8811000ffa4088007ed2044001fc9022000fa4811000ff84088007ff104400dfd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x7fc204c003ff0826001ff04130017decb9000bee65c8005b732e4002fb59720016dacb9000bec65c8005f7b264002fb99320017dac99000bec64c8029f7aa64013fb95320007daa99004fec54c8005f7b1e4002fb98f20017dac79000bec63c8029f7a9e4012fb94f20007daa79004bec53c8027f7a1e4012fb90f20007da879004bec43c8005f7b0e4002fb98720017dac39000bec61c8029f7a8e4000fb94720007daa390053ec51c8027f7a0e4000fb90720007da839004fec41c8025f798e4000fb8c720007da639004bec31c800376b064001fbd432000fdca190007ed50c8003f62864001fbd032000fdc8190007ed40c8003f62064001fbcc32000fdc6190007ed30c8003f61864001fb8432000fd82190003ff65480017fb2a4011ff9952002dfcca90003fd65480017eb2a4011ff1952002df8ca90003ff64480017fb224010ff99120025fcc890003fd64480017eb224010ff19120025f8c890047ff5448021ff2a24000ff55120087f8a890003ff63480017fb1a400fff98d2001dfcc690003fd63480017eb1a400fff18d2001df8c690047ff534801fff29a4000ff54d2007ff8a690043ff434801fff21a4000ff50d2007ff88690006ff6248005ffa924011fbd4920017fca49000bee5248005fea924000fb54920017f8a49000bec5248005ffa124010fbd0920017fc849000bee4248005fea124000fb50920017f8849000bec4248005ff992400ffbcc920017fc649000bee3248005fe9924000fb4c920017f8649000bec3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4006bf1852008ffea290003fe5148001fea8a4011ff14520087fe8290003fe4148001fea0a4010ff1052007ffe6290003fe3148001fe98a400fff0c520017fe429000bef2148005ff10a4000fb88520017fa4290003ed2148005fe10a4002fb0852000dfec090007ff5048003ff2824001ff5412000ff8a090007ff4048003ff2024001ff5012000ff88090007ff3048003ff1824001ff4c12000ff86090007ff2048005fd9024001ff8812000fdc4090007fc2048003f61024001fe0812000ffc2090007fa1048003fe0824000fbd952008fdcca90003ed6548023f632a4000fbd9120087dcc890003ed6448021f63224011fbd5120087dca890003ed5448021f62a24000fbd8d2007fdcc690003ed634801ff631a4011fbd4d2007fdca690003ed534801ff629a4010fbd0d2007fdc8690003ed434801ff621a4000fbd8520007dcc290003ed6148001f630a4011fbd4520007dca290003ed5148023f628a4010fbd0520007dc8290003ed4148021f620a400ffbcc520007dc6290003ed314801ff618a4001fbd812000ddec09000beb6048003f7a824001fb9412000fdaa090007ec5048003f7a024001fb9012000fda8090007ec4048003f79
  | 2 => 0x5002ff8a2a8077ff4154001ff20aa000ff505500eff882a8073ff3154001ff18aa000ff4c5500e7f862a806fff2154001ff10aa000ff485500dff842a8006ff6054003ffa82a005fed415000ffca0a80077e5054003fe282a001df1415000ff0a0a8007ff4054003ff202a001ff1015000ffe60a8007fe3054003fe182a001ffc815000ffc40a8007fc2054003ff082a001ff04150007fecaa0002ff6550035ff32a8005bf99540007facaa0002fd6550035fe32a8005bf1954000dfec8a0013ff5450009ff2a28004ef95140027faa8a0003bd5450009fe2a28000ffd8d40005fec6a0067fe63500077f31a8000ff58d400cff8c6a000efc6350035ffa9a8019ff94d40007faa6a0067fc5350009ffa1a8004efd0d40027fc86a0013fd4350001dea1a8004ff10d40007fec4a0002ff6250031ff3128002bf98940007fac4a0063fc62500057e312801affd49400c7fca4a0003fd5250031fe2928004ffd0940027fc84a0013fd4250009fe2128019ffcc9400c7fc64a0003fd3250031fe1928000ffd8540005fec2a0003fe6150001feb0a8000ff18540035f8c2a006bff5150001ff28a8000ff545400d7f8a2a0013ff4150009dfa0a8004ff90540027fa82a0003bd4150009fe20a8019ffcc540007fc62a0003fd3150033fe18a8018ffc8540007fc42a0003fd2150031fe10a8001bfd814000ffea0a0007fe5050003fea828001ff1414000ffe80a0013fb4050003ff2028001ef9014000ff880a0007bc4050003fc2028001ffcc14000ffc60a0007fc3050003ff9028001ff8814000ff840a0007fe1050003fe0828000ffd9530005feca9805ffe654c00b7f32a6000ff59530005faca9805ffc654c00b7e32a6000ffd9130005fec89805bfe644c0097f3226000ff59130005fac89805bfc644c0097e3226017ffd51300b7fca898003fd544c02dfe2a26001bfd8d3001ffea69800ffe534c007ef29a6003ff54d30007baa69800ffc534c007ffa1a6003ff90d3001fbc869800ffd434c001eea1a6003ff10d30007fec498002ff624c02bff3126002bf98930007fac498057fc624c0057e3126017ffd49300affca498003fd524c02bfe2926016ffd09300affc8498003fd424c02bfe2126003ffcc93001ffc649800ffd324c007fe1926000ffd8530005fec298003fe614c001feb0a6000ff18530035f8c29805fff514c001ff28a6000ff545300bff8a29805bff414c001ff20a6000ff505300b7f8829800fff314c007ef98a6003ff8c53001ffa6298003dd314c007fe18a6015ffc8530007fc4298003fd214c02bfe10a6001bfd813000ffea098007fe504c003fea826001ff1413000ffe8098007fe404c003fea026001ff1013000ffe609800ffb304c003ff1826001f78c13000ff86098007dc304c003fc1826001ffc813000ffc409800
  | 3 => 0xf31c4206ff58e21005fac71081bfc638840d7e31c4225ffd4e2111ffca710803fd5388447fe29c4224ffd0e2111ffc8710803fd4388447fe21c4202bf58a21017fea51080bfe5288405fea944202ff14a21017fe8510893ef4288405ff2144202ff50a21017f8851080bec4288405ff9944223fbcca21017fc651080bfd3288405fe1944202fb0ca21035fcc31081bff518840dff28c4206ff54621037f8a31081bff418840dff20c4206ff50621037f8831081bff318840dff18c4206ff4c621037f8631081bff218840df790c4202fdc8621037f8431081bf4218840dffb044206ff9822100dfcc11081bfd60884017eb044206ff1822100df8c110897ff5088445ff2844222ff14221127fe811088bfe4088445fe2044223ffcc221117fc611088bfc3088405ff9044202fbc8221017fc411080bfc208840dff0844206ff04221007feca90802ff6548443ff32a4205bf99521007faca90802fd6548443fe32a4205bf19521007fec890802ff6448441ff3224204bf99121007fac890802fd6448441fe3224204bf1912110ffea890883fe5448401feaa24220ff15121007fec690802ff634843fff31a4203bf98d21007fac690802fd634843ffe31a4203bf18d2110ffea69087ffe5348401fea9a421fff14d21107fe869087ffe4348401fea1a421fff10d21035fec49080bff5248405ff2924202ff54921017f8a49080bff4248405ff2124202ff50921017f8849080bff3248405ff1924202ff4c921017f8649080aff6148443ffa8a4206ff94521007faa29081bfc5148441ffa0a4206ff90521007fa829081bfc414843fff98a4206ff8c521007fa629081bfc3148405ff90a4202fdc8521037fc429081bee214840dfe10a4206fb08521017e84290803ff60484017fb02421eff9812100dfcc090803fd604843dfe3024201bf1812110ffea09087bfe504843dfe2824220ffd01210f7fc809087bfc404843fff982421eff8c1210f7f8609080bff2048405f79024202ff88121017f8409087bfe104840dfe0824201bfd9550007fec8a8002ff645403bff322a004bf99150007fac8a8077fc64540097e322a005ffd515002efea8a8017fe545400bfeaa2a000df5515002ff8a8a8003ff63540017fb1aa01cff98d5001dfcc6a8003fd6354039fe31aa003bf18d5002ffea6a80177f535400bff29aa005ff54d50006faa6a8017fc535403bffa1aa01cff90d50007fa86a8073fc4354001ffb12a000bfd89500dffcc4a800afe6254001feb12a01bff18950015f8c4a8017ff525400bff292a005ff5495002ff8a4a8077ff4254037ff212a000ff509500dff884a8073ff3254037ff192a000ff4c9500dff864a8003ff61540017fb0aa000ff98550007fac2a8003fc615400d7e30aa005ffd455002efea2a8017fe515400bfea8aa000df545
  | 4 => 0x8c7ff505045dff282822eff14141027fe80a0813bf4050409ff2028204ff10141187fe60a08bbfe305045dfe182822fffc8141177fc40a08bbfc205045dff0828206ff04141037fecb1881aff658c40dff32c6205bf99631037facb18802fd658c40dfe32c6206bf19631037fec91881aff648c40dff3246204bf99231037fac918802fd648c40dfe3246206bf1923116ffea9188b3fe548c401feaa4622cff1523101dfac71880fff538c407ff29c6203ff54e3101ff8a71880fff438c407ff21c6203ff50e3101ff8871881bff628c40dff3146202bf98a31037fac518802fd628c40dfe3146206bf18a3116ffea5188affe528c401fea94622bff14a31167fe85188affe428c401fea14622bff10a3101ffe651880ffe328c407fe9946203ff0ca31035fcc31881bff518c40dff28c6206ff54631037f8a31881bff418c40dff20c6206ff50631037f8831881bff318c40def98c6203fdcc631037f8631881bf4318c40dff90c6206ff08631037fec11881bfe608c4037f3046206ff58231005fac11881bfc608c4037e304622dffd4231157fca1188abfc508c459ffa04622aff90231157f8811880fff308c407ff1846203ff0c23115ffe41188abfe208c455fe1046206ff84231037f82118803ff654c4017fb2a6229ff9953102dfcca98803fd654c4017eb2a6229ff1953102df8ca98803ff644c4017fb226228ff99131025fcc898803fd644c4017eb226228ff19131025f8c8988a7ff544c451ff2a26200ff55131147f8a89881aff634c407ffa9a6229f7d4d3101ffca69880ffd534c407fe29a6203f714d3101ffe869880ffe434c407ef21a6203ff50d31007ba869880ffc434c401ffb126200bfd8931007dec498802ef624c44fff3126202bf98931007fac49889ffc624c4057e3126200fb18931015d8c4988a7ff524c44fff2926200ff5493113ff8a4988a3ff424c44fff2126200ff5093113ff8849880fff324c407ef9926203ff8c93101ffa6498803dd324c407fe1926203bfd853114ffea29881bfe514c401fea8a6206ff14531147fe829881bfe414c401fea0a6206ff1053101ffe629880ff7314c40dff18a6206f78c531037f8629881bdc314c407fa18a6227ffc8531037f84298803ff604c4017fb026226ff9813100dfcc098803fd604c44dfe3026201bf1813114ffea09889bfe504c44dfe2826228ffd0131137fc809889bfc404c407ff9826203f7cc13101ffc609880ffc304c44fff9026226ff88131137f8409889bfe104c40dfe0826206ffd9621035fecb1081bfe658840b7f32c4206ff59621005facb1081bfc658840d7e32c4206ffd9221035fec91081bfe64884097f3244206ff59221005fac91081bfc648840d7e3244225ffd5221127fca910803fd5488449fe2a44206ffd8e21035fec71081bfe63884077
  | 5 => 0xd51007fa86a88e3fc4354401ffb12a200bfd89511bffcc4a880afe6254401feb12a237ff18951015f8c4a8817ff525440bbfa92a205ff9495102ffaa4a88037d525440bfe292a239ffd09511bffc84a8803fd425446ffe212a238ffcc9511bffc64a8803fd325446ffe192a205bfd855102ffea2a8817f7515440dff28aa206df94551037f8a2a881b7c515440bfa28aa239ffd0551037f882a88e3ff315440dfe18aa237ffc8551037f842a8803ff60544017fb02a236ff9815100dfcc0a8803fd605446dfe302a201bf1815102ffea0a88177f505440bff282a205ff141511cffe80a88dbfe405446dfe202a238ffcc1511b7fc60a88dbfc305446fff902a236ff881511b7f840a88dbfe105440dfe082a206ffd9641035fecb2081bfe659040b7f32c8206ff59641005facb2081bfc659040d7e32c8204bf59241027fea920813fe5490409feaa48204ff15241037fec72081bfe63904077f31c8206ff58e41005fac72081bfc639040d7e31c8235ffd4e411a7fca720803fd5390469fe29c8204ffd0e41027fc8720813fd4390409fe21c8206ffd8a41037fcc52080afe629040dfeb148200bf58a41037f8c52081afc629046bffa948233ff94a41007faa5208cffc5290409ffa148204ff90a41027fa8520813fc4290469ff9948233ff8ca41007fa65208cffc329040d7f30c8206ffd4641037fca32081bfd519040dfe28c8206ffd06410377e8320813f7419040dfe20c8206fd10641037fe632081bfc319040dff90c8206ff08641037fec12081bfe60904037f3048206ff58241005fac12081bfc60904037e3048235ffd4241197fca1208cbfc5090409ffa048204ff90241027f881208d3ff3090465ff1848232ff0c24119ffe41208cbfe2090465fe1048206ff84241037f82120803ff65504017fb2a8231ff9954102dfccaa0803fd65504017eb2a8231ff1954102df8caa081aff6450409ffaa28231efd5141027fca8a0813fd5450409fe2a28204ef15141007fec6a0802ff6350461ff31a8203bf98d41007fac6a08c3fc63504077e31a8231ffd4d41187fca6a0803fd5350461fe29a8204ffd0d410277e86a0813fe4350409fea1a8200ef50d41027f886a0803ff62504017fb128200fbd8941005dec4a08bffe62504057f3128200ff5894117ff8c4a080afc6250401f63128202bb1894118ffea4a08bffe5250401fea92822fff14941027fe84a0813bf4250409ff2128204ff509410077a84a0813fc4250461ff992822fff8c941007fa64a08bffc32504097fb0a8231ffd4541037fca2a0803fd515040dfe28a8204ffd0541027ee82a081bfe415040ddf20a8206ff105410377882a0813f44150461ff98a8206ff0c54117ffe42a081bfc2150401ffb028200bfd8141177fcc0a0806fe6050401feb02822eff1814100df8c0a0
  | 6 => 0x1ffb028400bfd814220ffcc0a1006fe6050801feb028441ff1814200df8c0a110fff5050883ff2828441ff14142027fe80a1013fe4050809fe2028442ffcc14220ffc60a1107fc3050805ff9028402fbc8142017fc40a100bfc2050883ff0828441ff04142007feca99002ff654c881ff32a6405bf99532007faca99002fd654c881fe32a6405bf19532007fec899002ff644c87fff3226404bf99132007fac899002fd644c87ffe3226404bf19132207fea8990fffe544c801feaa2643fff15132015fec69900fff534c807ff29a6403ff54d3201ff8a69900fff434c807ff21a6403ff50d3201ff8869900aff624c805ffa926402ff94932017faa49900bfc524c805ffa126402ff90932017fa849900bfc424c805ff9926403fbcc932017fc649900bde324c805fe1926402f70c932017d86499003ff614c8017fb0a6400ff98532007fac299003fc614c80d7e30a6440ffd4532207f8a2990ffff414c87ffe20a6403ffcc53201fbe629900ffc314c805ff90a6402ff08532007fec099002ff604c87dff3026401bf98132007fac0990fbfc604c8037e3026440ffd41321f7fca0990fbfc504c87fffa02643eff901321f7f8809900fff304c807ff1826403ff0c132017fe409900bef204c805ff1026402ff081321f7fc20990fbfc104c80b7eb2ca206ffd9251037fcc928812fe649440ddf324a204af99251037fac928802fd649440ddeb24a200af59251037f8c92881afc649440bffaa4a205dfd525102ffca928817fd5494401beaa4a205ff15251037fec72881bfe63944077f31ca206f798e5101dbcc72881bfd63944017eb1ca206f758e51005bac72881bfc639440d7e31ca205ffd4e5102efea728817fe539440bfea9ca200df54e5102ff8a7288f7ff4394479ff21ca200ff50e511e7f8872881bff629440dff314a202bf98a51037fac528802fd629440dfe314a206bf18a5102ffea528817fe529440bfea94a205ff14a511effe85288effe4294401fea14a23bff10a511e7fe65288effe3294401fe994a23bff0ca51035fcc32881bff519440dbfa8ca205fdd4651037f8a32881bf4519440dffa0ca206ff10651037fe632881bfc319440dff90ca206ff08651037fec12881bfe60944037f304a206ff58251005fac12881bfc60944037e304a205ffd425102ffca1288eb7e509440bfe284a205df142511effe81288ebfe4094475fe204a23cffcc2511d7fc61288ebfc3094477ff904a23aff882511d7f8412881bfe109440dfe084a206bfd9551007fec8a8802ff6454473ff322a204bf99151007fac8a88e7fc64544097e322a205ffd515102ffca8a8817fd545440bfe2a2a200ffd8d51005fec6a88e3fe63544077f31aa200ff58d511c7f8c6a880efc635440bffa9aa205ff94d5102ffaa6a8817fc5354473ffa1aa238ff9
  | 7 => 0xa1927fc6550c0b7e32a8603bfd9143027fea8a1813fe5450c09feaa28604ff1514301dfec6a180fff5350c07ff29a8603ff54d4301ff8a6a180fff4350c09efa1a8603ff90d4301f7c86a180ffc4350c07de21a8603f710d4301f3886a1803ff6250c017fb128648ff98943015fcc4a1803fd6250c91fe3128602bf1894324ffea4a1923fe5250c91fe2928604ffd0943027fc84a1923be4250c09fe2128604ef1094301ffe64a180ffe3250c91ef1928603ff0c94301fb864a1803ff6150c017fb0a8600ff98543007fac2a1803fc6150c0d7e30a8649ffd454324ff8a2a1813ff4150c09dfa0a8604ff1054301ffe62a180fdf3150c07fe18a8648ffc8543247f842a1803ff6050c017fb028647ff9814300dfcc0a1803fd6050c8ffe3028601bf1814324ffea0a191ffe5050c8ffe2828604ffd01430277e80a1813fe4050c09fe2028603ffcc14301fbe60a180ffe3050c07fe1828648ffc814323ffc40a191ffc2050c8fff0828647ff04143015fecaa9003ff64548017fb22a446ff99152025fcc8a9003fd645488dfe322a404bf1915202ffea8a90177f545480bff2a2a405ff55152006faa8a9017fc5454801ffb1aa400bfd8d5222ffcc6a900efe6354801feb1aa445ff18d5201df8c6a9017ff535480bbfa9aa405ff94d5202ffaa6a90037d535480bfe29aa446ffd0d5222ffc86a9003fd435488bfe21aa402bfd8952017fea4a9017ef5254805ff292a402df94952017f8a4a900b7c5254805f6292a402ffd0952017fc84a900bfc4254805ff992a402ff8c952017f864a9003ff61548017fb0aa400ff98552007fac2a9003fc615480d7e30aa405ffd455202efea2a9017fc515488dffa0aa446ff1055222ffe62a9117fc3154805ff90aa402ff08552007fec0a9002ff6054889ff302a401bf98152007fac0a9113fc60548037e302a405ffd415202ffca0a91137e505480bfe282a405df14152237fe80a9113fe4054889fe202a445ffcc152227fc60a9113fc3054805ff902a402fbc8152017fc40a900bfc2054889ff082a444ff04152007fecaa1002ff6550887ff32a8405bf99542007facaa1002fd6550887fe32a8405bf19542015fec8a1013ff5450809ff2a28404ff55142027f8a8a1003ff63508017fb1a8442ff98d4201dfcc6a1003fd6350885fe31a8403bf18d4221ffea6a110bfe5350801fea9a8442ff14d42027fe86a1013fe4350809fea1a8404ff10d42015fec4a100bff5250805ff2928402ff54942017f8a4a100bff4250809f7a128402ff909420177c84a100bfc4250805de2128402fb10942017fe64a100bfe3250805fe1928400ffd8542005fec2a1003fe6150801feb0a8400ff18542035f8c2a110fff5150887fe28a8404ffd05420277e82a1013fc4150885ff98a8442ff0c542017fe42a100bfc215080
  | 8 => 0x400200300000900000200200100100d00000100400000100100100000700200400300000400000100800100200600100102d00700901c00500e00000900300900000000000200000100900100001900600100201900a00000000700800000200000200100700400500500200700301f00400100d00400600400300000702000100700500000200f00c00101000500200a00b00900000300500100c00200000200000400000500000800000001d00000100000100300500b01d00000100000000200600700200100500100100c00000000700100700200100a00000200000600000300600001100100400100400100200000a00000401300900000002100000100100300300300400000001300900d00402a002000007025fecaaa012ff6455009ffaa2a805efd5154027fca8aa0137e5455009fe2a2a804df1515402778a8aa003ff63550017fb1aa84fff98d5401dfcc6aa003fd635509ffe31aa803bf18d5402ffea6aa017fe535500bfe29aa804ffd0d54027fc86aa013fc4355001ffb12a800bfd8954277fcc4aa00afe6255001feb12a84eff18954015f8c4aa017ff525500bbfa92a805ff9495402ff8a4aa013ff4255009ff212a804ff1095427ffe64aa13bfe325509dfe192a800ffd8554005fec2aa003fe6155001feb0aa800ff18554035f8c2aa017ff515500bfe28aa805df14554027fe82aa013fc415509fff98aa84fff0c554277fe42aa13bfc2155001ffb02a800bfd815426ffcc0aa006fe6055001feb02a84dff1815400df8c0aa017ff505500bbfa82a805ff9415402ff8a0aa013ff4055009dfa02a804ff90154027f880aa13fff305509bff182a84dff0c154277fe40aa137fe205509bfe102a84dff8415426ff820aa00eff6554c01ffb22a600bfd9153267fcc8a9812fe6454c01feb22a64cff19153025f8c8a9817ff5454c0bff2a2a605ff5515302ff8a8a980eff6354c07ffa9aa605f7d4d5301ffca6a980f7e5354c07fe29aa603df14d5301fb8a6a980fff4354c07ff21aa603ff10d53007fec4a9802ff6254c97ff312a602bf98953007fac4a992ffc6254c057e312a605ffd495302efea4a9817fe5254c0bfe292a64cffd095325ffc84a992ffc4254c07ff992a603ff8c95301ff864a9803ff6154c017fb0aa600ff98553007fac2a9803fc6154c0d7e30aa605ffd455302ff8a2a98177c5154c99ffa0aa64cff1055301ffe62a980ffc3154c97ff90aa64bff08553007fec0a9802ff6054c95ff302a601bf98153007fac0a992bfc6054c037e302a605ffd415302efea0a9817fe5054c0bfe282a64cffd0153257fc80a992bfc4054c07ff982a603f7cc15301ffc60a980ffc3054c97ff902a64aff88153257f840a992bfe1054c95fe082a600ffd9543005fecaa1927fe6550c0b7f32a8600ff59543005faca
  | 9 => 0x5c73aaea3bcb9e0ee000dfc000000a9aebc0001e40006608a605e73e80200093226aae60003469c06a67c63a0eae000e004c40000001aa000000b4aba85349960000000000000003fe47a8e492e9b0bb8a9e18af12000738b1c4a4be4b08000e1674e26eb60000b8e4e8410c74a6805c238a56ea87302d81100009a2df0ade5aa46c300c405604720000000000000005f48b40001c200000000042ab2483c00064eaa2bbc28295c000224c1a2761d200002eb9623c852000000000afe00074a00040e000000458042f0e1d4c600003e6b3e08e00025e4d439a206826eac000000000000de27e8962d9c98400008cd0c00004635e69a868cd65d267e0bae1e2ced18b7e87c7ae85e000000828d7a0b8db80eae746b6014000c502dc00000018200000088c0006eed8814631a000a7457e044bfa0000002e8c4ce02000842e06d428dc000ee410ede0e6e6d400093c000f00e2400200100300300900000400100100000600b00100100500000200d00600100100a00000000200200000100000d00b00000000300000100c00200501a00200000800000000200d00000d00c00200700000200200000301402500100d00001600000003000900200000200c00e00000100000600000200400101000000200300000800000f00400a00900000400500000100100000200000600000300900100300000000101f00302900f00101500200400100800b00100000000000400300001400202200100a00c00700100200900800600000000b00000000000300200600700c00200700200300f00001000500000201100101600b00e00200300600000001800300000300000200200400300000100200000100100500e00b00301100b00101600200100300200400500200901700b00000100100002702400300500000000f00000500000000200000000600200c00c00000000c00400400001400701600201600102700000000700600900101000b00600001100700c00200000600400500000200500000000001b00d01000101d00500000b00000b00000100300200d00000200d00500200200200000e00400100e00100200200500400400000000000100700100400000f00a00100201300700600d01900300600300f00000400100100100000000f00c01100200000100100000b00100200100200200801c01f00100000100200600800000800000300301200200000f00000000000600102f00801a00000200000000100100000000701900500000400600400a00200300000e00000300900000300200000301c01100100a01000300800d01200d00100c00000401700200300200500100000700300400100700000502c00700100001600000000700200501e02801100100300000000100100200800001d00a00000400000001b004001000000000001002000001
  | 10 => 0xe00000000000045abd20001e25b02b6162000a360000000042c8328798000000960ebe00013cb88000be817805aad64a800069e000b5c000000c80ce4190b48e9edba91a4e4de4444beea5e000152be000000016ac940009fca3e976002b7ab440000008ec00090c00064c0000000000000000000000004ce000de8e4a7f28f0b12000000b6c0f64269e000000000000087ebce11480e156a8ae228924f4000b1000028a0006a0d1ca6243654e34413e3de86a2ec000ae25ec3c04923f8ed88d45a275280ceee00036c000000caed90000bccd508de80636e946368770e18aee1d6e88a145eed6a00037eaf058e6a4982cb0d6284c39ec984d228c04a112a8e000b6e72e0006f450ec2691e92678e5123ca06cb787a07b4d7caaaeca670abe19a77ad58232c7030c85a480a2a454d2cbc696a53c314cc6c101f43066acc1414e048c3229c0927fa2aed821c0dfec8c8e80741a04566e402c5f27047dc6944883800002ba63a39c000000e2a1707a60004de3c8000c7e17c9141920001985240001f862cdc2e0a000000000d5e46869000030a2366f80006280000000008fcb50096e1a3da25a5fa000ed62865ba3eedc6a88990c667885e2c9081a33c7cc588c3408aedeba4ccc00000000000096e4000000e80006ec0000000007dae68000f0c96cd0a68689caa688a0000880000000004120000f068e6f6ac44204f0432a124765e063ebc8ec886ec547ca4aae1c25652ee207860e69b4a8cdf2dd699888e00000059ebda0008849580007644e6000000b66c08000e12b543727d00000000001e6e800000000000003e82a668c8ac0000004d085657cb6858435c000a6a63c93ea52e926fc0620008769b8376ab6000a90000e842c00005daa3c4a2000e6c65ca70000000000000afc0007ce000e4e682b80792ca8000e7a83a66400000000000055ece0b70da0060dbeb0c0007e6124a4c37ada66be8360000000005d6ba08c0d80000000000000000a00e6a0000000000000000002e4658000522000e10466000226a447eac06790000ce65086f2cfc48ec42000f082f448464454aca4230c6ec0ed400005cc8bc510bead98340128c20b4c0000003ae00082e5ae73c67aeb43e4b867b29e6d949860005026063f656e7501a65307eebe24b48c2552d44302abc778e9ad002000d667c44a00049612e12666884eb427d40a6d8e6c429837c0f816000009e0001880d48c80a46387846343b0000000654000e6473200007292c000000d4ade669ce3400057279e07e5c400097e00041c13a0e42b04bacf80ca000706a1a8b00fc8c6b06db47d29fe00040c1806b80c88d07003b45b2268896c64eb65c61167400009e81c40000009388b6000000daa7c8e660001a403000018c000cea000000000000000000000762e8c68a000e44cb882a3865eaeb8000d
  | 11 => 0x33a000ae0000000a7c4fa000000000b8a4ec590d1010475894843c00051a00066e0002b254611845e0008b84427a2000000eaa89e1dab28000a2e61042cd38c7a98a48a0000009f8536246d76a246ba00004e5b4710cee00011c60ce5a000352d24c1c000a1800092894c672000000184082aae00075a3e238e0000ec000000080a2cc2e518e940005b800000045c0003a27b8330000ab01dc00000c11a0006d2000eb05d0000a80272d0600000075e5960520380000004e0dea000c366043a6556f06000000e08e389d849a000d640001e0ac682c3c45bc17272ad14d34d2e916580bd41b6dee578bb036020c0580a2bba050000336b58ee6a7e8d20004bea08022766618bf497a0a00b215ec927fca16244bde41abd0744c44dae1e81b07489da850cb61ba000e320001f0834026d5a0006b4a5ac960007f0d8cef4df4260064ea6404000000b9a4f200025c398936b46a92978a30c7612c4a6d84652bec562280018040ace4347bc17e742262e502d00008c47028545fc000922000000d9600034ac0ad60542000bf84f6210d4ca506e21a200043860000000000012a000000b14000000acc0b6c4a016cf4000c0c21a9ee216000980366b0e3b20000007ba000f1420eb6adbca3a9dc9d2e4c8127c0000000cd22c2000bac7466ccc868862e6a86cc8c2297c36a4ee204e7816e6ea0006d6cac0de000a7a0000b4f16954250000988000bc09122ee000972000312d6c0dc7be000a6ecbc03a424af266c2ca000dd8000000a788442e06aea585266b20aaa02ab2150822adcaa850ca069ac0a846a8eacb264a90014ceeab760f432e63261261ca843fc000000000ef200a000bf0b4e89000026cd308e69d6000c82108000000000d16000c2a71e6fa0000fa0005de5b6776ae4a28efe100b00000ccaa4e220528a1cd208944e23dc22a1ec46eb52aa43785fe294e86364582b38144ed4908da22fa00e15c9d43d85a008620ae3c7146e8e52da80706c87b69708dab8c0840fe52ce56474310350000cd0592b04ca0000392dec89838a878382d72e8a73431c93a9ae8aa2becc25384d690e0b00001660000000006dc00031eece0000000009060009ea0008480001c83d0e2e0340007364fee42a264407d83a4a7647c85c2aaa6c7fef02388d2643083227ae8e60eb821cabd890251cb2647e5a800001c944544a2294a46075648623403601253a2a23f0c3c83e622a821ce662cd4eec598c16514dc4ef80007287d61d8c48000c8e14023a0009948f604c4dc248ab870ccc0000d22348000c5a240754000666000cbe000000c048d6418e3ad8a7687f4208402c84000000000b980000000009d000021e79a2925940000001eebd68046fe642d9e5aca4a71acb40009dedac00023e2d2b840000000000005864da7605163ccc5e2f695ed52820bca1a
  | 12 => 0xd800074c00024eeba1c6b30c52ae81b8c562660000000001beea2cdc032774b20816000ec035800000002400000040800002a428a349aa72c00058ab0a0002907962d4000000c5c000b1a65abe60000009ba000e5c0005ce06e0001bc2f800079c4c057a0006460280009ce120d286e0bfc27ebb470ed708185a46c015a19c000b2214270894e0be000a0c1f279499e000cf0c8a2228d80bc2020c6270506c3aa9400042e00009000000011e9e2b620003ce0000c4000000eda00099a6ce4ae000168b7c00081c65614ab3c6361942c60003a8a9810290a626b928620008e200052a678000000000d869c695289a608ecca48470a6041676e000228000da400000000000000000000016c0000000004caed28247ec000942000992d74d0228880a3548f49f4b903f40009ca614910dcac4e3d606a6a86500009565c200038c000000e62e90000218000000a320000000000000000009e4000000000000000c62000000316d780009b2bc2000d48000e408662ea3faef044c574e58264e2600000000000059a4bcee0318c9ad68ac8000000aac28ece81cc0000000005f69c8566cec000808dce782c6aa42414b348be0d23aa5687a4676696c120d05588cebf23228aedfa864c9e940efcd047a849c2ac2b84f81381f624229e692846af855417643a34e63098e9cc34cce272449800007c680d36d2abf609443e0006980000000001b49a464858c3ea3be4fc18ea66dd076aca24525761362bc0000c2258dcc000e465c0a106f0020d66af4dde54caca0c0bdc4b22844485e403e3bacfab2c7183620000005d42fe5a600032c49061606800050000078c000000c884460000007c45e60000000000000000000000000000007e29ec0000008f84826dead4aa000000025456c1a84b8000bbe000000df8840000772830d0e4b0dd203cac2924c24e1477e87a9f0db29a078a9a60007c2c302a43340008806d09b6b16000ad0000000000000d3c86007884ae043c67ac174274000baeb1e8006e64c84cce76950918712624b56ec4b321485ca5d8000d921fcbaa000000000c387f66a20000008e0e703ec0008fa0009308b200009a19e00098c000000000000000c6c5480000dab5a15400000000032048c3c27f8dc817a4068ee3d40d8b2e19671cef60006bcec6000c28000000000a1eab4e5e214106ac0a0eba2c78f101b2d3259c000d5441e8145f0000000b748a000072076c3e021cb5e0000000088a8a04000c0033e0002e256a00030ed560661accf26da22ebb6c2ccfe3f2edc13453e00081000099c0002f200000000064001a000c1ec9cd6ec688cc39081e006e60000b94d1ee962b4e4855a342e0e6ca0000000000009bc000b3adda70a132000000a0a5700002c4cded4649e7de00066a0004b6a20000000a9629a6c63b8620870db6c7c000cce
  | 13 => 0xcf62da6c21fe4c20000005e82f0ada550bfe67488218649495a09c716324000000000602caa2ccc46374b72ea492a974a64e7ce823d2252a549660006b05c8000cda96410aed000055cc3e7b0dd48380000006d80000f24a08a2e3ecbac02d7e75c4d861aec29045be688b3610c21260a40a4504aca4650a62e858326a40f0a1de3848a4000000d9a000000000d129f2338304f04c58e3000062a2de056afa000000000122540000e98394e0c0005dc0000000008ba93400096861e0005329f632a9202fce2c4c6aecdc022caba478e9cb02396b40356efa0549be27cdb0e36c727e02964ea000df6000000000bc4af6a38a720007aa000000ca6000b2a684a9c86c1649c23aceb20003329fa1fa6aa422cc43087e4ad8c189a8ee20000ce000ba60002d60e2000e54000888000000b9c000098ee8d1ad3a000130780000ad25040cca5c00044e0000008ca87291cbb272200024a77c462d3e1ea51ed4e2a80000008740ae0000000e00009c40005f856424c1d035a2a007ab1865e5200acddc01e8fe010e72370b64726278158464e28000000e7e000076d083b68f2ea0c
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x4708c510036f7608c510037f3608c510157e7208c510157f2208c510157e5208c51001cff764c51000cfe764c510134fd764c51000cfc764c5100067f654c51014e7c654c510006df634c51001edc634c510005ef724c51003dec724c510037d4314c510005fb704c51000df8704c51000df4764c51001ef4764c51000cf4764c510005f7754c510005f5754c51000777654c51000774654c510005f7744c510005f5744c510035f7734c510037d7734c510007d7634c51001ef6634c51001ef4634c510047d4634c5102a7d7534c510047d4534c510047d6434c510007d5434c510007e7724c510007e4724c510047d7324c510007d5324c510007f3704c51000df6704c51000df4704c510137f0704c510036f7604c510037f3604c510137d7304c510137d5304c510137e7204c510137f2204c510137e5204c510014ff764851000cfe76485100f4fd764851000cfc76485100067f654851010e7c6548510006ef6248510016ec6248510005fb704851000df87048510035f87648110016f87648110034f876481100077b654811000778654811000dfb724811000feb7248110007eb6248110016fa6248110016f8624811003fe8624811029feb524811003fea5248110007e9524811003fe85248110297eb424811003fea4248110007e9424811003fe8424811028feb324811003fea3248110007e9324811003fe83248110007f37148110035fa7148110035f87148110007f0714811000efb614811000ff36148110007f25148110007f15148110007f24148110007f14148110007f23148110007f1314811003feb2148110287ea2148110007e92148110287e8214811003feb7648110016eb7648110007e87648110016e87648110007eb754811029fea7548110007e9754811029fe87548110007eb65481100076b654811029fea6548110007e9654811029fe86548110007686548110007eb7448110297ea7448110007e97448110297e87448110007eb6448110297ea6448110007e96448110297e8644811029feb5448110297ea5448110007e95448110297e85448110007eb734811028fea7348110007e9734811028fe87348110007eb634811028fea6348110007e9634811028fe8634811029feb534811028fea5348110007e9534811028fe85348110297eb434811028fea4348110007e9434811028fe84348110007eb7148110007e37148110287ea7148110007e97148110287e87148110007e0714811000feb614811000eeb614811000fe3614811029feb5148110287ea5148110007e25148110007e95148110007e15148110287e85148110297eb4148110287ea4148110007e24148110007e94148110007e14148110287e8414811028feb3148110287ea3148110007e23148110007e93148110007e13148110287e83148110
  | 1 => 0x8910004df735891001cfe735891001cfc7358910006dc735891001cdc7358910114ff7258910006ef72589102ccff7158910006f77158910286ee2158910286ec21589100f4ff7058910006fb70589100f6ef20589100f6ed2058910004ff7654910004fe7654910004fd7654910004fc76549100067f655491002e7c6554910004ff7650910004fe7650910004fd7650910004fc76509100067f655091021e7c6550910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9102067c654c9102c5f67694510036f676945101b5f575945101d777659451002ef6659451002ef4659451005774659451002e746594510037b67494510005f57494510037b57494510005b57494510057775494510007755494510037d67394510005f57394510037d57394510005d5739451005777539451000775539451000df6709451000df47094510036f76094510037f360945101d77650945101d77450945101d7e720945101d7f220945101d7e5209451002cff765451000cfe76545101b4fd765451000cfc76545100067f655451002e7c6554510037745154510005fb705451000df8705451000df4765451002ef4765451000cf47654510035f7755451003777755451000777655451002ef6655451002ef46554510057746554510005f77454510005f77354510057775254510007755254510007f3705451000df6705451000df470545101b7f07054510036f76054510037f360545101b77750545101b77550545101b7e720545101b7f220545101b7e520545102bdf67690510036f67690510035f77590510005f57590510007776590510007746590510175f57490510026f66490510026f46490510005f5739051000df6709051000df47090510036f76090510037f36090510197e72090510197f22090510197e52090510024ff765051000cfe7650510174fd765051000cfc76505100067f655051018e7c6550510006bf6450510026bc6450510005ef725051003dec7250510037b44150510005fb705051000df8705051000df47650510026f4765051000cf47650510005f77550510005f57550510007776550510007746550510035f77450510037b77450510007b76450510026f66450510026f4645051004fb464505102b7b7545051004fb45450510005f7735051004fb74350510007b54350510007e77250510007e4725051004fb74250510007b54250510007f3705051000df6705051000df47050510177f07050510036f76050510037f36050510177b74050510177b54050510177e72050510177f22050510177e520505102adf6768c510036f6768c510035f7758c510005f5758c51000777658c51000774658c510035f7748c510005f5748c510135f5738c51001ef6638c51001ef4638c51000df6708c51000df
  | 2 => 0x2cfc75591100067c755911002c7c7559110194ff7459110006bf7459110004ff7359110006df7359110004df735911001cfe735911001cfc7359110006dc735911001cdc735911004ebf4359110004ff7259110006ef7259110004ef7259110014fe7259110014fc7259110006ec7259110014ec72591102dcff7159110006f77159110174ff7059110006fb7059110176ef2059110176ed2059110004ff7655110004fe7655110004fd7655110004fc76551100067f655511002e7c655511001cfe76d8d100067f65d8d100067c65d8d10046de63d8d1002cfe75d8d10004fd75d8d1002cfc75d8d10024fe74d8d10004fd74d8d10024fc74d8d10006df43d8d10046dc43d8d10014fe72d8d10004fd72d8d10014fc72d8d10006de32d8d10046dc32d8d10034fe71d8d1000cfd71d8d10034fc71d8d10046df31d8d10034ff70d8d1000cfe70d8d10034fd70d8d1000cfc70d8d10156df30d8d10156dd30d8d10156ef20d8d10156ed20d8d100057f7558d100557c7558d100067f6558d100067c6558d10005bf7458d1004dbc7458d10046dc6358d10005ef7258d1003dec7258d102d5f77158d10004ff7558d100067f7558d100047f7558d1002cfe7558d1002cfc7558d100067c7558d1002c7c7558d10004ff7458d10006bf7458d10004bf7458d10024fe7458d10024fc7458d10006bc7458d10024bc7458d10154ff7358d10006df7358d10046de4358d10004ff7258d10006ef7258d10004ef7258d10014fe7258d10014fc7258d10006ec7258d10014ec7258d102d4ff7158d10006f77158d10134ff7058d10006fb7058d10136ef2058d10136ed2058d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d1002e7c6554d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d1024e7c6550d10026be6450d10006bd6450d1001ede6350d10006dd6350d100479c4350d10014fe76d89100067f65d89100067c65d891003eee62d891002cfe75d8910004fd75d891002cfc75d8910024fe74d8910004fd74d8910024fc74d891001cfe73d8910004fd73d891001cfc73d8910006ef42d891003eec42d8910006ef32d891003eec32d8910034fe71d891000cfd71d8910034fc71d891003eef21d8910034ff70d891000cfe70d8910034fd70d891000cfc70d8910116ef20d8910116ed20d89100057f75589100557c75589100067f65589100067c6558910005bf745891004dbc7458910005df7358910045dc735891003eec62589102cdf77158910004ff75589100067f75589100047f755891002cfe755891002cfc75589100067c755891002c7c7558910004ff7458910006bf7458910004bf7458910024fe7458910024fc7458910006bc7458910024bc7458910004ff7358910006df735
  | 3 => 0xc53d9510014fe72d9510004fd72d9510014fc72d95100567f52d95100067e52d95100567c52d9510034fe71d951000cfd71d9510034fc71d95100567f51d9510034ff70d951000cfe70d9510034fd70d951000cfc70d95101d67f50d95101d67d50d95101d6ef20d95101d6ed20d95102c57e76d951002c7e76d95100067e64d95100067c64d95100067e63d95100067c63d95100067e62d95100067c62d95101d77771d95101d76f20d95101d77a20d95101d76d20d95102f77b10d95101d77610d95101d77410d95101d77810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067c42d95100067f32d95100067e32d95100067c32d95101d67f71d95102f67e71d95101d67d71d95101d67c71d95100067f41d95102f67e41d95102f67c41d95100067f31d95102f67e31d95102f67c31d95100067f21d95102f67e21d95102f67c21d95101d67f70d95101d67e70d95101d67d70d95101d67c70d95101d67f40d95101d67e40d95101d67d40d95101d67c40d95101d67f30d95101d67e30d95101d67d30d95101d67c30d95101d67f20d95101d66f20d95101d67e20d95101d67d20d95101d66d20d95101d67c20d95101d67f10d95101d67e10d95101d67c10d95100567c65595102edf771595101d4ff75595100067f7559510004ff7459510024fe7459510024fc7459510004ff735951001cfe735951001cfc7359510004ff7259510014fe7259510014fc72595102ecff7159510006f771595101b4ff7059510006fb70595101b6ef20595101b6ed20595101d57e76195100567e76195101d47e76195100067e64195100067c64195100067e63195100067c63195100067e62195100067c62195102c77571195102c67f61195102c67f60195102c76f20195102c77a20195102c76d20195102e77b10195102c77610195102c77410195102c7781019510024fe76d91100067f65d91100067c65d911004ebe64d911002cfe75d9110004fd75d911002cfc75d911001cfe73d9110004fd73d911001cfc73d9110006be43d911004ebc43d9110014fe72d9110004fd72d9110014fc72d9110006be42d911004ebc42d9110034fe71d911000cfd71d9110034fc71d911004ebf41d9110034ff70d911000cfe70d9110034fd70d911000cfc70d9110196bf40d9110196bd40d9110196ef20d9110196ed20d91100057f75591100557c75591100067f65591100067c655911004ebc6459110005df7359110045dc7359110005ef725911003dec72591102ddf77159110004ff75591100067f75591100047f755911002cfe7559110
  | 4 => 0x5310034fe7655310004fd7655310034fc765531032e7f655531002e7c6555310035f6715531032f765155310004ff7558f1002cfe7558f1002cfc7558f10004ff7458f10024fe7458f10024fc7458f10036df7358f10006df5358f10066dc5358f10066de4358f10004ff7258f10006ef7258f10004ef7258f10014fe7258f10014fc7258f10006ec7258f10014ec7258f10066df3258f10034ff7158f1000cfe7158f10034fd7158f1000cfc7158f10036de3158f10036dc3158f10136df3058f10136dd3058f10136ef2058f10136ed2058f10004ff7654f10034fe7654f10004fd7654f10034fc7654f103267f6554f1002e7c6554f10035f67154f10327765154f10004ff7650f10034fe7650f10004fd7650f10034fc7650f10026be6450f10006bd6450f1001ede6350f10006dd6350f100679c4350f10035f67150f10004ff7558b1002cfe7558b1002cfc7558b10004ff7458b10024fe7458b10024fc7458b10004ff7358b1001cfe7358b1001cfc7358b10036ef7258b10034ff7158b1000cfe7158b10034fd7158b1000cfc7158b10036ee2158b10036ec2158b100f6ef2058b100f6ed2058b10036fa1058b10036f91058b10004ff7654b10034fe7654b10004fd7654b10034fc7654b1002e7e6554b100067d6554b10004ff7650b10034fe7650b10004fd7650b10034fc7650b10026be6450b10006bd6450b10004ff764cb10034fe764cb10004fd764cb10034fc764cb1001ede634cb10006dd634cb10035f7765471031ef7765471003777755471003777655471002ef66554710036f46554710037746554710005f77454710005f7735471007777525471000775525471000df6705471000df470547101b77750547101b77550547101b7e720547101b7e52054710035f77650710316f77650710005f77550710005f57550710037b77450710037b76450710026f66450710036f46450710037b4645071030fb7545071006fb45450710005f7735071006fb74350710007b54350710007e77250710007e4725071006fb74250710007b5425071000df6705071000df47050710177b74050710177b54050710177e72050710177e52050710035f7764c710306f7764c710005f7754c710005f5754c710005f7744c710005f5744c710037d7734c710037d7634c71001ef6634c710036f4634c710037d4634c7102ffd7534c710067d4534c710067d6434c710007d5434c710007e7724c710007e4724c710067d7324c710007d5324c71000df6704c71000df4704c710137d7304c710137d5304c710137e7204c710137e5204c71002cfe76d95100567e65d9510024fe74d9510004fd74d9510024fc74d95100567f54d95100067e54d95100567c54d951001cfe73d9510004fd73d951001cfc73d95100567f53d95100067e53d95100567
  | 5 => 0x7dee7390520005ed7390520285ec73905202bdee7190520287af4190520087e74190520287e44190520195ef709052000dee7090520197ea709052000dea7090520195ed7090520287e97090520005e9709052000dec7090520196ef609052019feb6090520197e71090520197ea1090520005ef7650520006ef7650520004ef7650520005ee7650520005ed7650520005ec7650520006ec7650520004ec7650520005ef755052008dee7550520005ed755052008dec7550520195ef7450520087ae6450520007ad645052033faf5450520087ac5450520005ef735052007dee735052007dec7350520087af4350520007ad43505202ddef7150520087e74150520287ae4150520287ac4150520087e44150520175ef705052000dee705052000dec7050520176ef605052017feb6050520177af4050520177ad4050520177ea1050520285ef768c520005ee768c520005ed768c520285ec768c520285ef758c52008dee758c520005ed758c520285ec758c520285ef748c520085ee748c520005ed748c520285ec748c520135ed738c520007cf638c52007fcc638c5202adee718c520287cf318c52007fe7318c520287e4318c520155ef708c52000dee708c520157ea708c52000dea708c520155ed708c520287e9708c520005e9708c52000dec708c520156ef608c52015feb608c520157e7108c520157ea108c520005ef764c520006ef764c520004ef764c520005ee764c520005ed764c520005ec764c520006ec764c520004ec764c520005ef754c52008dee754c520005ed754c52008dec754c520005ef744c520085ee744c520005ed744c520085ec744c520155ef734c52007fce634c520007cd634c520337cf534c52007fcc534c52007fce434c520007cd434c5202d5ef714c52007fe7314c520287ce314c520287cc314c52007fe4314c520135ef704c52000dee704c52000dec704c520136ef604c52013feb604c520137cf304c520137cd304c520137ea104c5200367f7559710004ff7459710024fe7459710024fc7459710004ff735971001cfe735971001cfc7359710004ff7259710014fe7259710014fc72597100767f5259710034ff715971000cfe7159710034fd715971000cfc71597100367e51597100367c51597101b67f50597101b67d50597101b6ef20597101b6ed2059710004ff755931002cfe755931002cfc7559310036bf7459310006bf545931006ebc5459310004ff735931001cfe735931001cfc735931006ebf4359310004ff7259310006ef7259310004ef7259310014fe7259310014fc7259310006ec7259310014ec725931006ebf4259310034ff715931000cfe7159310034fd715931000cfc7159310036be4159310036bc4159310176bf4059310176bd4059310176ef2059310176ed2059310004ff765
  | 6 => 0xc7598520085ee7498520005ed7498520285ec7498520006ee6498520006ec649852007dee7398520005ed7398520285ec7398520006ee6398520006ec6398520345ee7198520286ef6198520007e76198520115ed7098520287e97098520005e97098520116ef609852005feb6098520117ea1098520005ef75585200076f75585200056f755852008dee755852008dec75585200076c755852008d6c7558520005ef7458520007af7458520005af7458520085ee7458520085ec7458520007ac7458520085ac7458520005ef7358520007cf7358520005cf735852007dee735852007dec7358520007cc735852007dcc7358520007e76158520286ee61585200f5ef7058520007eb7058520005eb705852003feb60585200f7ea10585202cdee761852008dee75185202876e751852008d6e7518520005ed75185202876d75185200056d7518520285ec7518520085ee7418520287ae7418520085ae7418520005ed7418520287ad7418520005ad7418520285ec7418520006ee6418520006ec641852007dee7318520287ce731852007dce7318520005ed7318520287cd7318520005cd7318520285ec7318520006ee6318520006ec6318520115ee7118520286ef6118520287e66118520286ed6118520007e56118520007e75118520287e45118520015ef701852000dee7018520015ed7018520287e9701852000dec7018520346ef601852034feb6018520347e71018520347ea1018520347e51018520285ef7694520005ee7694520005ed7694520285ec76945201b5ed75945200076f659452008f6c6594520085ee7494520287ae7494520085ae7494520005ed7494520287ad7494520005ad7494520285ec749452008f6f54945200076d549452007dee7394520287ce739452007dce7394520005ed7394520287cd7394520005cd7394520285ec739452008f6f53945200076d53945202c5ee71945202876f519452008fe75194520287e451945201d5ef709452000dee70945201d7ea709452000dea70945201d5ed7094520287e97094520005e9709452000dec70945201d6ef60945201dfeb60945201d76e50945201d76c50945201d7e710945201d7ea1094520005ef7654520005ee7654520005ed7654520005ec76545201d5ef755452008f6e65545200076d6554520005ef7454520085ee7454520085ec7454520005ef735452007dee735452007dec73545202edef715452008fe751545202876e51545202876c515452008fe451545201b5ef705452000dee705452000dec70545201b6ef60545201bfeb60545201b76f50545201b76d50545201b7ea1054520285ef7690520005ee7690520005ed7690520285ec7690520285ef759052008dee7590520005ed7590520285ec7590520175ed7490520007af6490520087ac6490520
  | 7 => 0x912007dec7359120005ef7159120285ec7159120087af415912020def7059120007eb7059120005eb705912020eef60591200c7eb605912020fea1059120005ef7655120005ee7655120005ed7655120005ec76551203a5ef755512008f6e65551200076d655512039def745512008faf54551200876e54551200876c5455120087ac5455120005ef735512007dee735512007dec7355120005ef7155120285ec715512008f6c515512026def705512000dee705512026ded705512000dec705512026eef6055120277eb605512026f6f505512026f6d505512026faf405512026fad405512026fea1055120395ee76d8d2008dee75d8d20005ed75d8d2008dec75d8d20085ee74d8d20005ed74d8d20085ec74d8d201f5ed73d8d2007eee63d8d2007fce63d8d2007eec63d8d20007cf53d8d2007fcc53d8d2007fce43d8d20285ee71d8d20005ed71d8d2007fcc31d8d20015ef70d8d2000dee70d8d20015ed70d8d2000dec70d8d2037eef60d8d2038feb60d8d2037fcf30d8d2037fcd30d8d2037fea10d8d20385ef7658d20005ef7558d2008dee7558d2008dec7558d20005ef7458d20085ee7458d20085ec7458d2037def7358d20007cf6358d2007eee6358d2007eec6358d2007fcc6358d20005ef7158d20285ec7158d2007fcf3158d201f5ef7058d20007eb7058d20005eb7058d201f6ef6058d200afeb6058d201f7ea1058d20005ef7654d20005ee7654d20005ed7654d20005ec7654d20375ef7554d2008f6e6554d200076d6554d20005ef7454d20085ee7454d20085ec7454d2036def7354d2008fcf5354d2007f6e5354d2007f6c5354d2007fcc5354d20005ef7154d20285ec7154d2008f6c5154d20255ef7054d2000dee7054d20255ed7054d2000dec7054d20256ef6054d2025feb6054d202576f5054d202576d5054d20257cf3054d20257cd3054d20257ea1054d20005ef7650d20005ee7650d20005ed7650d20005ec7650d20005ef7550d2008dee7550d20005ed7550d2008dec7550d20365ef7450d20007af6450d20087ac6450d2035def7350d20007cf6350d2007fcc6350d20087cf4350d2007fae4350d2007fac4350d2007fcc4350d2007f8c4350d20005ef7150d20285ec7150d20087af4150d2007fcf3150d2023def7050d2000dee7050d2023ded7050d2000dec7050d2023eef6050d20247eb6050d2023faf4050d2023fad4050d2023fcf3050d2023fcd3050d2023fea1050d2008dee75d8520005ed75d852008dec75d8520085ee74d8520005ed74d8520085ec74d852007dee73d8520005ed73d852007dec73d8520007e751d8520007e451d8520015ef70d8520357eb70d8520015ed70d85202ceef60d8520357eb60d85202cfe710d85202cfea10d85202cfe510d852008dee7598520005ed7598520285e
  | 8 => 0x5ed728c520015ec728c52000dfa708c520005f9708c520004ff764c520004fe764c520004fc764c52001ede634c520006dd634c520005ef724c520015ee724c520015ec724c52007fcf324c520007cd324c52000dee7688520116ee768852000cee7688520285ef758852008dee7588520005ed7588520285ec7588520285ef7488520085ee7488520005ed7488520285ec7488520126ee6488520126ec6488520285ef738852007dee7388520005ed7388520285ec738852011eee638852011eec6388520015ee7188520017e67188520286ef6188520007e76188520287e4618852000dee7088520117ea708852000dea7088520287e9708852000dec7088520016ef6088520017eb6088520117ea108852000dec7648520036ec764852000cec7648520005ef754852008dee7548520005ed754852008dec7548520005ef7448520085ee7448520005ed7448520085ec7448520005ef734852007dee7348520005ed734852007dec7348520015ef7148520017e77148520007e76148520036ee6148520036ec6148520007e46148520007eb704852000dee704852000dec70485200f7e87048520016ef6048520017eb60485200f7ea10485203e5ee76d9520225ed75d952008eee65d952008f6e65d952008eec65d9520085ee74d9520005ed74d9520085ec74d952007dee73d9520005ed73d952007dec73d9520285ee71d9520005ed71d952008f6c51d9520015ef70d952000dee70d9520015ed70d952000dec70d95203ceef60d95203dfeb60d95203cf6f50d95203cf6d50d95203cfea10d95203d5ef76595203cdef75595200076f655952008eee655952008eec655952008f6c6559520005ef7459520007af7459520005af7459520085ee7459520085ec7459520007ac7459520085ac745952008f6f5459520005ef7359520007cf7359520005cf735952007dee735952007dec7359520007cc735952007dcc735952008f6f5359520005ef7159520007e77159520005e77159520285ec7159520007e47159520005e4715952008f6f5159520225ef7059520007eb7059520005eb7059520226ef60595200dfeb60595202276e50595202276c5059520227ea10595203c5ee76d912008dee75d9120005ed75d912008dec75d912020ded74d9120086ee64d9120087ae64d9120086ec64d9120007af54d9120087ac54d912007dee73d9120005ed73d912007dec73d9120087af43d9120285ee71d9120005ed71d9120087ac41d9120015ef70d912000dee70d9120015ed70d912000dec70d91203aeef60d91203bfeb60d91203afaf40d91203afad40d91203afea10d91203b5ef7659120005ef755912008dee755912008dec75591203adef7459120007af6459120086ee6459120086ec6459120087ac6459120005ef735912007dee735
  | 9 => 0xc765492000cec7654920015ef75549200176f75549200076f655492002eee655492002eec655492008f6c6554920005ef7454920085ee7454920085ec745492008f6f54549200076d5454920005ef735492007dee735492007dec735492008f6f53549200076d5354920005ef7154920285ec715492008f6f5154920007eb705492000dee705492000dec7054920227e87054920016ef6054920017eb60549202276e50549202276c5054920227ea105492000dec7650920026ec765092000cec7650920005ef755092008dee7550920005ed755092008dec7550920015ef7450920017af7450920007af6450920026ee6450920026ec6450920087ac6450920005ef735092007dee735092007dec7350920005ef7150920285ec7150920087af4150920007eb705092000dee705092000dec705092020fe87050920016ef6050920017eb605092020fea105092000dec764c92001eec764c92000cec764c920005ef754c92008dee754c920005ed754c92008dec754c920005ef744c920085ee744c920005ed744c920085ec744c920015ef734c920017cf734c920007cf634c92001eee634c92001eec634c92007fcc634c920005ef714c920285ec714c92007fcf314c920007eb704c92000dee704c92000dec704c9201f7e8704c920016ef604c920017eb604c9201f7ea104c920034fe76d852002cfe75d8520004fd75d852002cfc75d8520024fe74d8520004fd74d8520024fc74d852001cfe73d8520004fd73d852001cfc73d852000cfd72d85202ceed72d8520006f751d8520006f451d8520356f621d8520356f521d8520286ec21d852000cfe70d8520014fd70d852000cfc70d85202cef710d8520006f7619852003df970985200057f755852008d7c7558520005bf7458520085bc7458520005df735852007ddc735852005dfb705852008d7e75185200057d7518520085be7418520005bd741852007dde7318520005dd7318520036f66118520006f56118520004fe7694520004fd7694520034fc76945200067f659452002e7c6594520085be7494520005bd749452007dde7394520005dd7394520015ee7294520005ed7294520015ec729452000dfa7094520005f97094520004ff7654520004fe7654520004fc765452002e7e65545200067d6554520005ef7254520015ee7254520015ec725452008f6f52545200076d5254520004fe7690520004fd7690520034fc7690520006bf6490520026bc6490520015ee7290520005ed7290520015ec729052000dfa7090520005f97090520004ff7650520004fe7650520004fc7650520026be6450520006bd6450520005ef7250520015ee7250520015ec7250520087af4250520007ad4250520004fe768c520004fd768c520034fc768c520006df638c52001edc638c520015ee728c520
  | 10 => 0x9520024fc7459520006bc7459520024bc745952008e7f5459520004ff7359520006df7359520004df735952001cfe735952001cfc7359520006dc735952001cdc735952008e7f53595203d4ff7259520006ef725952008eef52595200deec5259520004ff7159520006f77159520004f77159520034fc7159520006f47159520034f4715952008e7f5159520224ff7059520006fb70595202267e50595202267c5059520024fe76d9120086be64d9120015ee72d912000ded72d9120087af42d912002cfe75d9120004fd75d912002cfc75d912020cfd74d9120006bf54d9120086bc54d912001cfe73d9120004fd73d912001cfc73d9120086bf43d912000cff72d9120014fe72d912000cfd72d91203aeed72d912000ced72d9120014fc72d91203bebf42d9120086ef42d91203bebd42d91203beec42d9120034fe71d9120004fd71d9120086bc41d9120014ff70d9120014fd70d91203aebf40d91203aebd40d9120024ff7659120086bc64591203b5ef72591203f5fb7059120004ff755912002cfe755912002cfc75591203acff7459120006bf7459120004ff735912001cfe735912001cfc73591203b4ff7259120006ef7259120086ef42591200c6ec4259120004ff7159120034fc7159120086bf415912020cff7059120006fb7059120004ff7655120004fe7655120004fd7655120004fc765512002e7e65551200067d6555120005ef7255120015ee7255120015ec725512008f6f525512001cfe76d8d2007ede63d8d20015ee72d8d2000ded72d8d2007fcf32d8d2002cfe75d8d20004fd75d8d2002cfc75d8d20024fe74d8d20004fd74d8d20024fc74d8d201f4fd73d8d20006df53d8d2007edc53d8d2007ede43d8d2000cff72d8d20014fe72d8d2000cfd72d8d2037eed72d8d2000ced72d8d20014fc72d8d2038edf32d8d2007eef32d8d2038edd32d8d2038eec32d8d20034fe71d8d20004fd71d8d2007edc31d8d20014ff70d8d20014fd70d8d2037edf30d8d2037edd30d8d2001cff7658d2007edc6358d20385ef7258d203edfb7058d20004ff7558d2002cfe7558d2002cfc7558d20004ff7458d20024fe7458d20024fc7458d2037cff7358d20006df7358d20384ff7258d20006ef7258d2007eef3258d200aeec3258d20004ff7158d20034fc7158d2007edf3158d201f4ff7058d20006fb7058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d2002e7e6554d200067d6554d20005ef7254d20015ee7254d20015ec7254d2008f6f5254d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20006bf6450d20026bc6450d20006df6350d2001edc6350d2007f9c4350d20005ef7250d20015ee7250d20015ec7250d20247ae4250d20247ac4250d20247ce3250d20247cc3250d2000dec765492002ee
  | 11 => 0x9dec7454720005ef7354720095ee7354720095ec73547202edef71547200a7e751547204076e51547204076c51547200a7e451547201b5ef705472000dee705472000dec70547201b76f50547201b76d5054720405ef7690720015ee769072019ded7690720015ec7690720405ef75907200a5ee7590720005ed7590720405ec759072019f6e659072019f6d6590720095ee7390720005ed7390720405ec73907202bdee7190720407af419072009fe74190720407e44190720195ef709072000dee7090720195ed709072000dec7090720197e7109072017def7650720006ef7650720004ef7650720015ee765072017ded7650720015ec765072017eec7650720014ec7650720005ef75507200a5ee7550720005ed75507200a5ec755072017f6e655072017f6d655072017fae645072017fad6450720417af545072009fac5450720005ef7350720095ee7350720095ec735072009faf4350720007ad43507202ddef715072009fe74150720407ae4150720407ac415072009fe44150720175ef705072000dee705072000dec7050720177af4050720177ad4050720405ef768c720015ee768c72015ded768c720015ec768c720405ef758c7200a5ee758c720005ed758c720405ec758c72015f6e658c72015f6d658c720405ef748c72009dee748c720005ed748c720405ec748c7202adee718c720407cf318c720097e7318c720407e4318c720155ef708c72000dee708c720155ed708c72000dec708c720157e7108c72013def764c720006ef764c720004ef764c720015ee764c72013ded764c720015ec764c72013eec764c720014ec764c720005ef754c7200a5ee754c720005ed754c7200a5ec754c72013f6e654c72013f6d654c720005ef744c72009dee744c720005ed744c72009dec744c72013fce634c72013fcd634c72040fcf534c720097cc534c720097ce434c720007cd434c7202d5ef714c720097e7314c720407ce314c720407cc314c720097e4314c720135ef704c72000dee704c72000dec704c720137cf304c720137cd304c72002cfe76d952008e7e65d9520015ee72d952000ded72d952008f6f52d9520224fd75d9520024fe74d9520004fd74d9520024fc74d952001cfe73d9520004fd73d952001cfc73d952000cff72d9520014fe72d952000cfd72d95203ceed72d952000ced72d9520014fc72d95203de7f52d952008eef52d95203de7d52d95203deec52d9520034fe71d9520004fd71d952008e7c51d9520014ff70d9520014fd70d95203ce7f50d95203ce7d50d952002cff765952008e7c6559520005bf7459520085bc7459520005df735952007ddc73595203d5ef7259520005f77159520005f471595203fdfb70595203ccff75595200067f7559520004ff7459520006bf7459520004bf7459520024fe745
  | 12 => 0xe73505300079d4350530005ef72505300adec725053000ddc764c530036dc764c53000cdc764c530005df754c530005dd754c53014ede654c53014edc654c530005df744c530005dd744c530006df644c530006dd644c530007cf724c530007cc724c530006df624c53001ddf714c53001fd7714c530007d7614c530036de614c530036dc614c530007d4614c530007db704c53000dde704c53000ddc704c530137d8704c53001edf604c53001fdb604c530004fe7688530004fd7688530034fc768853001dde7388530005dd7388530006ef6288530016ec6288530004ff7648530004fe7648530004fc7648530275ef7655320015ee7655320275ed7655320015ec76553203a5ef75553202776e65553202776d655532039def74553200a7af545532009f6e545532009f6c545532009fac5455320005ef7355320095ee7355320095ec7355320005ef7155320405ec71553200a76c515532026def705532000dee705532026ded705532000dec705532026eed605532026f6f505532026f6d505532026faf405532026fad405532025def7654f20015ee7654f2025ded7654f20015ec7654f20375ef7554f2025f6e6554f2025f6d6554f20005ef7454f2009dee7454f2009dec7454f2036def7354f200a7cf5354f200976e5354f200976c5354f20097cc5354f20005ef7154f20405ec7154f200a76c5154f20255ef7054f2000dee7054f20255ed7054f2000dec7054f20256ed6054f202576f5054f202576d5054f20257cf3054f20257cd3054f20245ef7650f20015ee7650f20245ed7650f20015ec7650f20005ef7550f200a5ee7550f20005ed7550f200a5ec7550f202476e6550f202476d6550f20365ef7450f20247af6450f20247ac6450f2035def7350f20247cf6350f20247cc6350f2009fcf4350f20097ae4350f20097ac4350f20097cc4350f200978c4350f20005ef7150f20405ec7150f2009faf4150f20097cf3150f2023def7050f2000dee7050f2023ded7050f2000dec7050f2023eed6050f2023faf4050f2023fad4050f2023fcf3050f2023fcd3050f20405ef7694720015ee76947201dded7694720015ec76947201df6e65947201df6d659472009dee7494720407ae749472009dae7494720005ed7494720407ad7494720005ad7494720405ec74947200a76f54947200076d5494720095ee7394720407ce7394720095ce7394720005ed7394720407cd7394720005cd7394720405ec73947200a76f53947200076d53947202c5ee71947204076f51947200a7e75194720407e451947201d5ef709472000dee70947201d5ed709472000dec70947201d76e50947201d76c50947201d7e710947201bdef7654720015ee76547201bded7654720015ec76547201bf6e65547201bf6d6554720005ef745472009dee7454720
  | 13 => 0x9130366bd40d9130366ef20d9130366ed20d9130024ff76591300057f75591300bd7c75591300b6bc645913035ddf7359130435fb7059130004ff75591300067f75591300047f755913002cfe755913002cfc75591300067c755913002c7c7559130364ff7459130006bf745913035cff7359130006df7359130004ff7259130014fe7259130014fc7259130004ff7159130034fc71591300b6bf41591300cedf315913023cff7059130006fb7059130004ff7655130004fe7655130004fd7655130004fc765513001dde735513000ddc7654d3002edc7654d3000cdc7654d3001ddf7554d3001f5f7554d300075f6554d3002ede6554d3002edc6554d300bf5c6554d30005df7454d300bf5f5254d30005df7154d300bf5c5154d30007db7054d3000dde7054d3000ddc7054d30257d87054d3001edf6054d3001fdb6054d302575f5054d302575d5054d3000ddc7650d30026dc7650d3000cdc7650d30005df7550d30005dd7550d3001ddf7450d3001f9f7450d300079f6450d30026de6450d30026dc6450d300b79c6450d300269c6450d30246de6250d30246dc6250d3042f9e4250d300b79c4250d30005df7150d300b79f4150d30007db7050d3000dde7050d3000ddc7050d3023fd87050d3001edf6050d3001fdb6050d3023f9f4050d3023f9d4050d30014fe76d89300aeee62d893002cfe75d8930004fd75d893002cfc75d8930024fe74d8930004fd74d8930024fc74d893000cfd73d8930014fc73d89300aeee32d8930426ed32d8930034fe71d8930004fd71d8930426df31d89300aeec21d893001cfd70d8930386ef20d89300aeec6258930095fb7058930004ff7654930004fe7654930004fc76549300067f655493002e7c65549300075d5354930004ff7650930004fe7650930004fc7650930006bf6450930026bc6450930034fe76d853002cfe75d8530004fd75d853002cfc75d8530024fe74d8530004fd74d8530024fc74d853000cfd73d853041ede43d8530006dd43d8530014fe72d8530004fd72d8530014fc72d853041ef631d853041ef531d853001cfd70d85302d6ef20d85302d6ed20d85302d6f710d8530006f76198530045f970985300057f75585300bd7c7558530005bf74585300b5bc7458530005ef72585300adec7258530065fb70585300b5be7418530005bd7418530036f66118530006f56118530004fe7694530004fd7694530034fc76945300067f659453002e7c65945300b5be7494530005bd749453001dde7394530005dd73945300075d5394530004ff7654530004fe7654530004fc765453001dde7354530004fe7690530004fd7690530034fc7690530006bf6490530026bc649053001dde7390530005dd7390530004ff7650530004fe7650530004fc7650530026be6450530006bd645053001dd
  | 14 => 0x2cfe75d8540004fd75d854002cfc75d854000cfd74d854001cfe73d8540004fd73d854001cfc73d8540456bf43d8540006bd43d8540014fe72d8540004fd72d8540014fc72d8540456f641d8540456f541d8540024fd70d85402deef20d85402deed20d85402def710d8540006f7619854004df970985400057f75585400d57c7558540005df73585400cddc7358540005ef72585400c5ec725854006dfb70585400cdde7318540005dd7318540036f66118540006f56118540004fe7694540004fd7694540034fc76945400067f659454002e7c6594540025be7494540005bd74945400073d54945400cdde7394540005dd7394540004ff7654540004fe7654540004fc7654540025be745454000dbc7650540036bc765054000cbc7650540005bf7550540005bd755054018ebe655054018ebc6550540005bf7350540006bf6350540007af7250540007ac7250540006bf6250540025bf7150540027b77150540007b76150540036be6150540036bc6150540007b46150540007bb705054000dbe705054000dbc7050540177b87050540026bf6050540027bb6050540004fe768c540004fd768c540034fc768c540025be748c540005bd748c540006df638c54001edc638c540004ff764c540004fe764c540004fc764c540025be744c540005bd744c54001ede634c5400079d434c540005ef724c5400c5ec724c540004fe7688540004fd7688540034fc7688540025be7488540005bd7488540006ef6288540016ec6288540004ff7648540004fe7648540004fc764854002cfe76d95300be7e65d9530254fd75d9530024fe74d9530004fd74d9530024fc74d95300067e54d95300be7c54d953000cff73d953001cfe73d953000cfd73d953001cfc73d953044e7f53d953044e7d53d9530014fe72d9530004fd72d9530014fc72d95300be7f52d9530034fe71d9530004fd71d95300be7c51d953001cff70d953001cfd70d95303767f50d95303767d50d9530376ef20d9530376ed20d953002cff76595300be7c6559530005bf74595300b5bc745953036ddf7359530445fb7059530374ff75595300067f7559530004ff7459530006bf7459530004bf7459530024fe7459530024fc7459530006bc7459530024bc745953036cff7359530006df7359530004ff7259530014fe7259530014fc7259530004ff7159530034fc7159530254ff7059530006fb7059530024fe76d91300b6be64d913002cfe75d9130004fd75d913002cfc75d913023cfd74d9130006bf54d91300b6bc54d913000cff73d913001cfe73d913000cfd73d913001cfc73d913043ebf43d913043ebd43d9130014fe72d9130004fd72d9130014fc72d91300b6bf42d9130034fe71d9130004fd71d91300b6bc41d913043edf31d913001cff70d913001cfd70d9130366bf40d
  | 15 => 0xf534c550005ef724c5500ddec724c550004fe7688550004fd7688550034fc768855002d7e75885500057d7588550004ff7648550004fe7648550004fc764855002cfe76d95400d67e65d954026cfd75d954000cff74d9540024fe74d954000cfd74d9540024fc74d95404867f54d95404867d54d954001cfe73d9540004fd73d954001cfc73d95400067e53d95400d67c53d9540014fe72d9540004fd72d9540014fc72d95400d67f52d9540034fe71d9540004fd71d95400d67c51d9540024ff70d9540024fd70d95403a67f50d95403a67d50d95403a6ef20d95403a6ed20d954002cff76595400d67c655954039dbf7459540005df73595400cddc735954047dfb70595403a4ff75595400067f755954039cff7459540006bf7459540004ff7359540006df7359540004df735954001cfe735954001cfc7359540006dc735954001cdc7359540004ff7259540014fe7259540014fc7259540004ff7159540034fc715954026cff7059540006fb705954000dbc765514002ebc765514000cbc7655140025bf75551400273f75551400073f655514002ebe655514002ebc65551400d73c6555140005bf73551400d73f5255140005bf71551400d73c5155140007bb705514000dbe705514000dbc705514026fb87055140026bf6055140027bb605514026f3f505514026f3d505514001cfe76d8d400cede63d8d4002cfe75d8d40004fd75d8d4002cfc75d8d4000cfd74d8d4001cfc74d8d40006df53d8d400cedc53d8d400cede43d8d40476dd43d8d40014fe72d8d40004fd72d8d40014fc72d8d400cedf32d8d40034fe71d8d40004fd71d8d40476bf41d8d400cedc31d8d40024fd70d8d4035edf30d8d4035eef20d8d4035eed20d8d400057f7558d400d57c7558d400cedc6358d4046dfb7058d40004ff7654d40004fe7654d40004fc7654d40025be7454d4000dbc7650d4001ebc7650d4000cbc7650d40005bf7550d40005bd7550d40025bf7350d400279f7350d400079f6350d4001ebe6350d4001ebc6350d400cf9c6350d4001e9c6350d40246be6250d40246bc6250d404679e3250d400cf9c3250d40005bf7150d400cf9f3150d40007bb7050d4000dbe7050d4000dbc7050d4023fb87050d40026bf6050d40027bb6050d4023f9f3050d40014fe76d89400c6ee62d894002cfe75d8940004fd75d894002cfc75d894000cfd74d8940014fc74d894001cfe73d8940004fd73d894001cfc73d89400c6ee42d894045eed42d8940034fe71d8940004fd71d894045ebf41d89400c6ec21d8940024fd70d89403b6ef20d89400c6ec625894009dfb7058940004ff7654940004fe7654940004fc76549400067f655494002e7c65549400073d5454940004ff764c940004fe764c940004fc764c940006df634c94001edc634c940034fe76d8540
  | 16 => 0x515000d7e705515000d7c705515026f78705515002e7f605515002f7b605515026f3f405515001cfe76d8d500e6de63d8d5000cfd75d8d5001cfc75d8d50024fe74d8d50004fd74d8d50024fc74d8d500e6de53d8d504a6dd53d8d50006df43d8d500e6dc43d8d50014fe72d8d50004fd72d8d50014fc72d8d50006de32d8d500e6dc32d8d50034fe71d8d50004fd71d8d500e6df31d8d5002cfd70d8d5036edf30d8d5036eef20d8d5036eed20d8d50005bf7458d500edbc7458d500e6dc6358d5049dfb7058d5000d7c7654d5001e7c7654d5000c7c7654d500057f7454d5002d7f7354d5002f5f7354d500075f6354d5001e7e6354d5001e7c6354d500e75c6354d500057f7154d503267c6154d500077b7054d5000d7e7054d5000d7c7054d50257787054d5002e7f6054d5002f7b6054d502575f3054d50004ff7650d50004fe7650d50004fc7650d5002d7e7550d500057d7550d500e79c4350d50014fe76d89500deee62d895000cfd75d8950014fc75d8950024fe74d8950004fd74d8950024fc74d89504967f54d89500067d54d895001cfe73d8950004fd73d895001cfc73d89504967f53d89500067d53d89500deee52d8950496ed52d8950034fe71d8950004fd71d89504967f51d895002cfd70d89503d67e50d89503d67c50d89503d6ef20d8950005bf74589500edbc7458950005df73589500e5dc73589500deec6258950005f77158950005f471589500a5fb7058950004ff7650950004fe7650950004fc7650950004ff764c950004fe764c950004fc764c950034fe76d855000cfd75d8550024fe74d8550004fd74d8550024fc74d855001cfe73d8550004fd73d855001cfc73d8550014fe72d8550004fd72d8550014fc72d855048ef651d855048ef551d8550006f721d8550006f421d855002cfd70d85502eeef20d85502eeed20d85502eef710d85501d67f65985500edbe7498550005bd74985500e5de7398550005dd7398550006f76198550055f97098550075fb70585502c67f6518550036f66118550006f5611855000d7c76545500367c765455000c7c76545500057f74545500057f73545500067f625455002d7f715455002f7771545500077761545500367e61545500367c61545500077461545500077b705455000d7e705455000d7c70545501b778705455002e7f605455002f7b6054550004fe7690550004fd7690550034fc769055002d7e75905500057d7590550004ff7650550004fe7650550004fc765055002d7e75505500057d7550550006bf6450550026bc645055018f3f5450550005ef72505500ddec7250550004fe768c550004fd768c550034fc768c55002d7e758c5500057d758c550004ff764c550004fe764c550004fc764c55002d7e754c5500057d754c550006df634c55001edc634c55014f5
  | 17 => 0x1cfe735912101cfc735912117cff7259121006ef7259121124ef72591214c4ff7159121006f77159121004ff705912100cfe705912100cfc705912117eef2059121004ff7655121004fe7655121004fd7655121004fc76551210067f655512102e7c6555121006bf6455121026bc645512101cfe76d8d210fede63d8d2102cfe75d8d21004fd75d8d2102cfc75d8d21024fe74d8d21004fd74d8d21024fc74d8d210fede53d8d210fede43d8d21034ff72d8d21034fd72d8d2115edf32d8d2115edd32d8d21014fd71d8d210fedf31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d210fedc30d8d2115eef20d8d210fedc6358d214bdf77158d21004ff7558d2102cfe7558d2102cfc7558d21004ff7458d21024fe7458d21024fc7458d2115cff7358d21006df7358d2113cff7258d21006ef7258d2111cef7258d214bcff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d2113eef2058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d2102e7c6554d21006df6354d2101edc6354d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d21026bc6450d21006df6350d2101edc6350d210ff9c4350d2102cff7654521014fe76545211bcfd7654521014fc76545210067f655452102e7c6554521005ef7254521015ec7254521037e42154521024ff7650521014fe765052117cfd7650521014fc7650521006bf6450521026bc6450521005ef7250521015ec725052101cff764c521014fe764c52113cfd764c521014fc764c521006df634c52101edc634c521005ef724c521015ec724c52100cfe76d81210f6fa60d812102cfe75d8121004fd75d812102cfc75d8121024fe74d8121004fd74d8121024fc74d812101cfe73d8121004fd73d812101cfc73d8121406ef72d8121034fd72d812100cfc72d812100cec72d8121014fd71d812100cfc71d8121406ee21d8121406ec21d81210f6ef20d81210f6fa20d81210f6fa10d81210057f755812110d7c7558121005bf7458121105bc7458121005df73581210fddc73581210f6f86058121024fe76d91500eebe64d915000cfd75d9150024fc75d91500eebe54d91504b6bd54d915001cfe73d9150004fd73d915001cfc73d9150006be43d91500eebc43d9150014fe72d9150004fd72d9150014fc72d9150006be42d91500eebc42d9150034fe71d9150004fd71d91500eebf41d915002cfd70d915039ebf40d915039eef20d915039eed20d91500eebc6459150005df73591500e5dc73591504adfb705915000d7c76551500267c765515000c7c765515002d7f745515002f3f74551500073f64551500267e64551500267c64551500ef3c64551500057f73551500057f715515032e7c61551500077b705
  | 18 => 0xf5459221126bc5459221004ff735922101cfe735922101cfc7359221126bf4359221126ef725922117ebf4259221126ef425922117ebd425922117eec4259221034fe7159221034fc7159221036be4159221036bc4159221004ff705922100cfe705922100cfc7059221126bf405922117eef2059221004ff7655221034fe7655221004fd7655221034fc765522132e7f655522102e7c6555221005ef7255221015ec7255221004ff7558e2102cfe7558e2102cfc7558e21004ff7458e21024fe7458e21024fc7458e21036df7358e21006df5358e2111edc5358e2111ede4358e2111eef7258e2113edf3258e2111eef3258e2113edd3258e2113eec3258e21034fe7158e21034fc7158e21036de3158e21036dc3158e21004ff7058e2100cfe7058e2100cfc7058e2111edf3058e2113eef2058e21004ff7654e21034fe7654e21004fd7654e21034fc7654e213267f6554e2102e7c6554e21005ef7254e21015ec7254e21004ff7650e21034fe7650e21004fd7650e21034fc7650e21026be6450e21006bd6450e2101ede6350e21006dd6350e2111f9c4350e21005ef7250e21015ec7250e21247ac4250e21247cc3250e21004ff75582210067f75582210047f755822102cfe755822102cfc75582210067c755822102c7c7558221004ff7458221024fe7458221024fc7458221004ff735822101cfe735822101cfc7358221006ed7258221006ef425822103eec4258221006ef325822103eec3258221034fe715822100cfd7158221034fc7158221036ef2158221036ed2158221036fb7058221116ef2058221116fa2058221036fb1058221036f8105822102cfe76d952110e7e65d9521024fe74d9521004fd74d9521024fc74d952110e7f54d952101cfe73d9521004fd73d952101cfc73d952110e7f53d9521034ff72d9521034fd72d95211de7f52d95211de7d52d9521014fd71d952110e7f51d952100cfe70d9521004fd70d952100cfc70d95210067e50d952110e7c50d95211deef20d952110e7c65595214cdf771595211dcff75595210067f7559521004ff7459521024fe7459521024fc7459521004ff735952101cfe735952101cfc73595211bcff7259521006ef72595214ccff7159521006f77159521004ff705952100cfe705952100cfc70595211beef2059521024fe76d9121106be64d912102cfe75d9121004fd75d912102cfc75d9121106be54d912101cfe73d9121004fd73d912101cfc73d9121106bf43d9121034ff72d9121034fd72d912119ebf42d912119ebd42d9121014fd71d9121106bf41d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121106bc40d912119eef20d9121106bc64591214c5f77159121004ff755912102cfe755912102cfc755912119cff7459121006bf7459121004ff7359121
  | 19 => 0x893111eef31d89314eeee31d89314eeec31d8931006ef70d8931006ee70d8931006ed70d8931004ed70d8931006ec70d8931006ef50d8931006ee50d8931006ec50d8931006ef40d8931006ee40d8931006ec40d893111eef30d893111eee30d893111eed30d893111eec30d89314eeef10d8931006ee10d89314eeec10d893113eec62589314e5f7715893111dee761893113eee761893113f6e751893113f6d7518931006ef6518931006ee6518931006ed6518931006ec6518931006ef6418931006ee6418931006ed6418931006ec641893113fce731893113fcd73189314deef6318931007cf53189314d7cc53189314d7ce4318931007cd43189314beef61189314d7e731189314dfce31189314dfcc31189314d7e43118931005ed7018931006ee6018931006ec60189314d7cf3018931004ff7654931004fe7654931004fc765493102e7e65549310067d6554931005df735493101ddc735493114f5f5354931006ef6254931016ec6254931005f77154931035f47154931004ff7650931004fe7650931004fc765093101dde7350931006ef6250931016ec6250931035dc764c931016dc764c931034dc764c93114dde754c93114ddc754c931005df744c931005dd744c93101ddf724c93101fcf724c931007cf624c931016de624c931016dc624c93113fcc624c931007d7714c931035de714c931035dc714c931007d4714c931035d4714c93101edf614c93101fd7614c931005df704c93113fcf204c93102cff765453101cfe76545311c4fd765453101cfc76545310067f655453102e7c6554531005df735453101ddc7354531006ef62545311beec6254531037d43154531024ff765053101cfe7650531184fd765053101cfc7650531006bf6450531026bc6450531005df735053101ddc73505310079d4350531005ef725053113dec7250531006ef625053117eec6250531037b44150531037d4315053100cfe76d8131006ef62d8131006ec62d8131136fa60d813102cfe75d8131004fd75d813102cfc75d8131024fe74d8131004fd74d8131024fc74d8131034fd73d813100cfc73d8131066de43d8131006dd43d8131006ef72d8131014fe72d8131004fd72d8131014fc72d8131006ec72d813101cfd71d8131136fa30d8131136fa10d81310057f755813114d7c7558131005bf7458131145bc7458131005ef725813113dec7258131006ef6258131006ec6258131136f860581310367f7559621004ff7459621024fe7459621024fc7459621004ff735962101cfe735962101cfc73596211be7f52596211be7d5259621034fe7159621034fc71596210367e51596210367c5159621004ff705962100cfe705962100cfc705962112e7f50596211beef2059621004ff755922102cfe755922102cfc7559221036bf7459221006b
  | 20 => 0x4ff705953100cfe705953100cfc705953114e7f50595311c6df3059531024fe76d9131146be64d913102cfe75d9131004fd75d913102cfc75d9131146be54d9131034ff73d9131034fd73d91311a6bf43d91311a6bd43d9131014fe72d9131004fd72d9131014fc72d913101cfd71d9131146bf41d913100cfe70d9131004fd70d913100cfc70d9131006be40d9131146bc40d91311a6df30d9131146bc6459131005ef725913113dec72591314fdf77159131004ff755913102cfe755913102cfc75591311a4ff7459131006bf7459131184ff7359131006df7359131004ff7259131006ef7259131004ef7259131014fe7259131014fc7259131006ec7259131014ec72591314fcff7159131006f77159131004ff705913100cfe705913100cfc7059131146bf4059131186df3059131004ff7655131004fe7655131004fd7655131004fc76551310067f655513102e7c6555131006bf6455131026bc6455131005df735513101ddc7355131276ec6255131035dc7650d31026dc7650d31034dc7650d3114dde7550d3114ddc7550d3101ddf7450d3101f9f7450d310079f6450d31026de6450d31026dc6450d311479c6450d310269c6450d31005df7250d31246de6250d31246dc6250d31246cc6250d314f79e4250d311479c4250d31007d77150d31035de7150d31035dc7150d31007d47150d3101edf6150d3101fd76150d311479f4150d31005df7050d311479f4050d31014fe76d893113eee62d893102cfe75d8931004fd75d893102cfc75d8931024fe74d8931004fd74d8931024fc74d8931034fd73d8931006ef52d893113eee52d893113eec52d8931006ef42d893113eee42d893113eec42d893113eee32d893111eed32d893101cfd71d893113eef21d893100cfe70d8931004fd70d893100cfc70d893113eef20d8931006ee20d893113eec20d893113dee76d8931014ee76d8931006ef65d8931006ee65d8931006ed65d8931006ec65d8931006ef64d8931006ee64d8931006ed64d8931006ec64d89314efcf73d893111fcc73d8931007cf53d893111fcc53d893111fce43d8931007cd43d893111fe731d89314efce31d89314efcc31d893111fe431d8931005ed70d8931006ee60d8931006ec60d893111fcf30d8931006ef75d8931006ee75d8931006ed75d8931006ec75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d8931006ee54d8931006ed54d8931006ec54d89314eeef73d893113eee73d893111eec73d893111eef53d893111eee53d893111eed53d893111eec53d893111eef43d893111eee43d893111eed43d893111eec43d893111eef71d89314eeee71d893111eed71d89314eeec71d8931006ef51d89314eeee51d89314eeec51d8931006ef41d89314eeee41d89314eeec41d
  | 21 => 0xc73d814106ebf43d8141006bd43d8141006ef72d8141014fe72d8141004fd72d8141014fc72d8141006ec72d8141024fd71d8141176fa40d8141176fa10d81410057f755814118d7c7558141005df7358141185dc7358141005ef725814117dec7258141006ef6258141006ec6258141176f860581410367f7559631004ff7459631024fe7459631024fc74596310067e545963116e7c54596311c67f53596311c67d5359631004ff7259631014fe7259631014fc725963116e7f5259631034fe7159631034fc71596310367e51596310367c5159631004ff705963100cfe705963100cfc705963116e7f5059631036f71059631004ff755923102cfe755923102cfc7559231036bf7459231006bf5459231166bc5459231186bf4359231186bd4359231004ff7259231014fe7259231014fc7259231166bf4259231034fe7159231034fc7159231036be4159231036bc4159231036df3159231036dd3159231004ff705923100cfe705923100cfc7059231166bf4059231036f71059231004ff7655231034fe7655231004fd7655231034fc7655231004ff7558a3102cfe7558a3102cfc7558a31004ff7458a31024fe7458a31024fc7458a31036ef7258a3115eee3258a310feed3258a31034fe7158a31034fc7158a31036df3158a31036dd3158a31036ee2158a31036ec2158a31004ff7058a3100cfe7058a3100cfc7058a3115eef2058a31004ff7654a31004fd7654a31034fc7654a3102e7e6554a310067d6554a31005f77154a31035f47154a31004ff7650a31004fd7650a31034fc7650a31026be6450a31006bd6450a31004ff755823102cfe755823102cfc7558231004ff7458231024fe7458231024fc7458231004ff7258231014fe7258231014fc7258231034fe7158231034fc7158231036df3158231036dd3158231036fb7058231156fa3058231156fa2058231036fb1058231036f8105823102cfe76d953114e7e65d953101dde73d9531035dd73d953114f5f53d9531024fe74d9531004fd74d9531024fc74d953114e7f54d9531034ff73d9531034fd73d953114edd73d9531034dd73d95311e67f53d953114edf53d953114e5f53d95311e67d53d95311e6dc53d9531014fe72d9531004fd72d9531014fc72d953101cfd71d953114e7f51d953100cfe70d9531004fd70d953100cfc70d95310067e50d953114e7c50d95311e6df30d953114e7c6559531005ef725953113dec7259531505f771595311e4ff75595310067f7559531004ff7459531024fe7459531024fc74595311c4ff7359531006df735953114edf53595311c6dc5359531004ff7259531006ef7259531004ef7259531014fe7259531014fc7259531006ec7259531014ec725953114e7f5259531504ff7159531006f771595313267e51595313267c5159531
  | 22 => 0x894117dee76d8941014ee76d8941006ef65d8941006ee65d8941006ed65d8941006ec65d8941527af74d8941127ac74d8941007af54d8941127ac54d8941006ef63d8941006ee63d8941006ed63d8941006ec63d8941127af43d8941007ad43d8941127e741d8941527ae41d8941527ac41d8941127e441d8941005ed70d8941006ee60d8941006ec60d8941127af40d8941006ef75d8941006ee75d8941006ed75d8941006ec75d8941526ef74d894117eee74d8941126ec74d8941126ef54d8941126ee54d8941126ed54d8941126ec54d8941006ef73d8941006ee73d8941006ed73d8941006ec73d8941006ef53d8941006ee53d8941006ed53d8941006ec53d8941126ef43d8941126ee43d8941126ed43d8941126ec43d8941126ef71d8941526ee71d8941126ed71d8941526ec71d8941006ef51d8941526ee51d8941526ec51d8941126ef41d8941526ee41d8941526ec41d8941006ef31d8941526ee31d8941526ec31d8941006ef70d8941006ee70d8941006ed70d8941004ed70d8941006ec70d8941006ef50d8941006ee50d8941006ec50d8941126ef40d8941126ee40d8941126ed40d8941126ec40d8941006ef30d8941006ee30d8941006ec30d8941526ef10d8941006ee10d8941526ec10d894117eec625894151df77158941125ee761894117eee761894117f6e751894117f6d7518941006ef6518941006ee6518941006ed6518941006ec651894117fae741894117fad7418941516ef6418941007af541894150fac5418941006ef6318941006ee6318941006ed6318941006ec631894150faf4318941007ad43189414c6ef611894150fe74118941517ae4118941517ac411894150fe44118941005ed7018941006ee6018941006ec601894150faf4018941004ff7654941004fe7654941004fc765494102e7e65549410067d6554941005bf7454941025bc745494118f3f5454941006ef6254941016ec6254941005f77154941035f47154941035bc7650941016bc7650941034bc765094118dbe755094118dbc7550941005bf7350941025bf7250941027af7250941007af6250941016be6250941016bc625094117fac6250941007b77150941035be7150941035bc7150941007b47150941035b47150941026bf6150941027b76150941005bf705094117faf2050941004ff764c941004fe764c941004fc764c941025be744c941005bd744c941006ef624c941016ec624c94102cff7654541024fe76545411ccfd7654541024fc76545410067f655454102e7c6554541005bf7454541025bc7454541006ef62545411beec6254541037b4415454100cfe76d8141006ef62d8141006ec62d8141176fa60d814102cfe75d8141004fd75d814102cfc75d8141034fd74d814100cfc74d814101cfe73d8141004fd73d814101cf
  | 23 => 0x67d6554a41005f77154a41035f47154a41004ff764ca41004fd764ca41034fc764ca4101ede634ca41006dd634ca41004ff755824102cfe755824102cfc7558241004ff735824101cfe735824101cfc7358241004ff7258241014fe7258241014fc7258241034fe7158241034fc7158241036bf4158241036bd4158241036fb7058241196fa4058241196fa2058241036fb1058241036f8105824102cfe76d954118e7e65d9541025be74d9541035bd74d954118f3f54d9541034ff74d9541034fd74d954118ebd74d9541034bd74d95411ee7f54d954118ebf54d954118e3f54d95411ee7d54d95411eebc54d954101cfe73d9541004fd73d954101cfc73d954118e7f53d9541014fe72d9541004fd72d9541014fc72d9541024fd71d954118e7f51d954100cfe70d9541004fd70d954100cfc70d95410067e50d954118e7c50d95411eebf40d954118e7c6559541005ef725954117dec725954153df771595411ecff75595410067f75595411ccff7459541006bf745954118ebf54595411cebc5459541004ff735954101cfe735954101cfc7359541004ff7259541006ef7259541004ef7259541014fe7259541014fc7259541006ec7259541014ec725954118e7f525954153cff7159541006f7715954132e7e515954132e7c5159541004ff705954100cfe705954100cfc705954118e7f50595411cebf405954101cfe76d8d41186de63d8d4102cfe75d8d41004fd75d8d4102cfc75d8d41034fd74d8d41186de53d8d41186de43d8d41166dd43d8d41014fe72d8d41004fd72d8d41014fc72d8d41024fd71d8d41186df31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41166bf40d8d41006de30d8d41186dc30d8d41186dc6358d41005ef7258d4117dec7258d41535f77158d41004ff7654d41004fe7654d41004fc7654d410067f6554d4102e7c6554d41005bf7454d41025bc7454d41006df6354d4101edc6354d4125eec6254d41035bc7650d4101ebc7650d41034bc7650d4118dbe7550d4118dbc7550d41025bf7350d410279f7350d410079f6350d4101ebe6350d4101ebc6350d411879c6350d4101e9c6350d41005bf7250d41246be6250d41246bc6250d41246ac6250d4152f9e3250d411879c3250d41007b77150d41035be7150d41035bc7150d41007b47150d41026bf6150d41027b76150d411879f3150d41005bf7050d411879f3050d41014fe76d894117eee62d894102cfe75d8941004fd75d894102cfc75d8941034fd74d894101cfe73d8941004fd73d894101cfc73d8941006ef52d894117eee52d894117eec52d894117eee42d8941126ed42d8941006ef32d894117eee32d894117eec32d8941024fd71d894117eef21d894100cfe70d8941004fd70d894100cfc70d894117eef20d8941006ee20d894117eec20d
  | 24 => 0xf72591511bdec725915155df7715915101cfe76d8d511c6de63d8d51034fd75d8d51024fe74d8d51004fd74d8d51024fc74d8d511c6de53d8d5116edd53d8d51014fe72d8d51004fd72d8d51014fc72d8d5116e7f52d8d5102cfd71d8d515567e51d8d515567c51d8d511c6df31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d5116e7f50d8d511c6dc6358d51005ef7258d511bdec7258d5154df77158d51004ff7650d51004fe7650d51004fc7650d510057f7550d5102d7c7550d511c79c4350d51014fe76d89511beee62d8951034fd75d8951024fe74d8951004fd74d8951024fc74d895101cfe73d8951004fd73d895101cfc73d89511beee52d895112eed52d8951006ef42d89511beec42d8951006ef32d89511beec32d895102cfd71d89511beef21d895100cfe70d8951004fd70d895100cfc70d89511beef20d89511beec6258951545f771589510357c76549510167c76549510347c76549510067f64549510067f635495102d7f725495102f6f72549510076f62549510167e62549510167c62549511bf6c62549510077771549510357e71549510357c715495100774715495103574715495102e7f615495102f7761549510057f70549512267e60549512267c60549511bf6f2054951004ff7650951004fe7650951004fc7650951004ff764c951004fe764c951004fc764c95100cfe76d81511b6fa60d8151034fd75d815100cfc75d8151024fe74d8151004fd74d8151024fc74d815101cfe73d8151004fd73d815101cfc73d8151014fe72d8151004fd72d8151014fc72d815102cfd71d81511b6fa50d81511b6fa10d81511b6f860581510367f75596411ce7f54596411ce7d5459641004ff735964101cfe735964101cfc73596410067e53596411ae7c5359641004ff7259641014fe7259641014fc72596411ae7f5259641034fe7159641034fc71596410367e51596410367c5159641004ff705964100cfe705964100cfc70596411ae7f5059641036f71059641004ff7558e4102cfe7558e4102cfc7558e41036df7358e41006df5358e411a6dc5358e411a6de4358e41146dd4358e41004ff7258e41014fe7258e41014fc7258e411a6df3258e41034fe7158e41034fc7158e41036bf4158e41036bd4158e41036de3158e41036dc3158e41004ff7058e4100cfe7058e4100cfc7058e411a6df3058e41036f71058e41004ff7654e41004fd7654e41034fc7654e41004ff7558a4102cfe7558a4102cfc7558a41004ff7358a4101cfe7358a4101cfc7358a41036ef7258a4119eee4258a41106ed4258a41034fe7158a41034fc7158a41036bf4158a41036bd4158a41036ee2158a41036ec2158a41004ff7058a4100cfe7058a4100cfc7058a4119eef2058a41004ff7654a41004fd7654a41034fc7654a4102e7e6554a41
  | 25 => 0x8e5114edd7558e511e6dc7558e51006df7458e51006de7458e51006dd7458e51006dc7458e5114edf5458e5114ede5458e5114edd5458e5114edc5458e51006df7258e51006de7258e51006dd7258e51006dc7258e5114edf5258e5114ede5258e5114edd5258e5114edc5258e51006df4258e51006de4258e51006dc4258e51036df7158e51036de7158e51036dc7158e51036df5158e51036de5158e51036dd5158e51036dc5158e51036df4158e51036de4158e51036dd4158e51036dc4158e51036df2158e51036de2158e51036dd2158e51036dc2158e51006df7058e51006de7058e51006dd7058e51006dc7058e5114edf5058e5114ede5058e5114edd5058e5114edc5058e51006df4058e51006de4058e51006dc4058e51006df2058e51006de2058e51006dc2058e51036df1058e51036d71058e51036de1058e51036dd1058e51036dc1058e513257f7654e5101e7f7654e5101c7f7654e510057f7454e513273e6454e513273d6454e5102d7f7354e5102f5f7354e5101e7e6354e513275e6354e5101e5e6354e513275d6354e5101e7c6354e513257f7154e51007777154e51327747154e5102e7e6154e5102f766154e511d57e7054e511d57c7054e511e75f3054e51004ff7650e51004fd7650e51034fc7650e5102d7e7550e510057d7550e51026be6450e51006bd6450e5101ede6350e51006dd6350e511e79c4350e51004ff7458a51024fe7458a51024fc7458a5110e7f5458a510067d5458a51004ff7358a5101cfe7358a5101cfc7358a5110e7f5358a510067d5358a51036ef7258a511deee5258a5110eed5258a51034fe7158a51034fc7158a510367f5158a510367d5158a51036ee2158a51036ec2158a51004ff7058a5100cfe7058a5100cfc7058a510067e5058a5110e7c5058a511deef2058a51004ff7650a51004fd7650a51034fc7650a51026be6450a51006bd6450a51216de6350a51006dd6350a51004ff764ca51004fd764ca51034fc764ca511febe644ca51006bd644ca5101ede634ca51006dd634ca51004ff7458251024fe7458251024fc74582510567f54582510067d5458251004ff735825101cfe735825101cfc73582510567f53582510067d5358251004ff7258251014fe7258251014fc7258251034fe7158251034fc71582510367f51582510367d5158251036fb70582511d67e50582511d6fa50582511d67c50582511d6fa2058251036fb1058251036f81058251024fe76d91511cebe64d9151034fd75d91511cebe54d91511aebd54d915101cfe73d9151004fd73d915101cfc73d9151014fe72d9151004fd72d9151014fc72d91511ae7f52d915102cfd71d91515667e51d91515667c51d91511cebf41d915100cfe70d9151004fd70d915100cfc70d91511ae7f50d91511cebc6459151005e
  | 26 => 0x2cfe75d8532004fd75d853202cfc75d8532024fe74d8532004fd74d8532024fc74d8532014fd73d853201cfd72d85324e6f631d85324bef621d853200cfe70d8532004fd70d853200cfc70d85324beef20d85324eeef6298532006f761985321fdbe7418532005bd74185324eeef6218532036f66118532006f5611853200cfe76d81321f6fa60d813202cfe75d8132004fd75d813202cfc75d8132024fe74d8132004fd74d8132024fc74d8132014fd73d8132096ef72d813201cfd72d8132096ef32d81323eeec32d8132034fe71d8132004fd71d8132096df31d81321f6fa30d81321f6ef20d81321f6fa20d81321f6f86058132036bf74592511eebe545925118ebd5459251004ff735925101cfe735925101cfc73592511eebf4359251006be43592511eebc4359251004ff7259251014fe7259251014fc72592511eebf4259251006be42592511eebc4259251034fe7159251034fc7159251036be4159251036bc4159251004ff705925100cfe705925100cfc70592511eebf4059251006be40592511eebc4059251036f7105925118ebe755925118ebd75592511eebc7559251006bf7359251006be7359251006bd7359251006bc735925118ebf535925118ebe535925118ebd535925118ebc5359251006bf7259251006be7259251006bd7259251006bc725925118ebf525925118ebe525925118ebd525925118ebc5259251006bf3259251006be3259251006bc3259251036bf7159251036be7159251036bc7159251036bf5159251036be5159251036bd5159251036bc5159251036bf3159251036be3159251036bd3159251036bc3159251036bf2159251036be2159251036bd2159251036bc2159251006bf7059251006be7059251006bd7059251006bc705925118ebf505925118ebe505925118ebd505925118ebc5059251006bf3059251006be3059251006bc3059251006bf2059251006be2059251006bc2059251036bf1059251036b71059251036be1059251036bd1059251036bc105925132d7f76552510267f76552510247f765525102d7f745525102f3f74552510267e645525132f3e64552510263e645525132f3d64552510267c64552510057f735525132f5e635525132f5d635525132d7f715525100777715525132f74715525102e7e615525102f7661552511d57e70552511d57c70552511ef3f4055251004ff7458e51024fe7458e51024fc7458e51036df7358e511e6de5358e5114edd5358e51006df4358e511e6de4358e511e6dc4358e51004ff7258e51014fe7258e51014fc7258e511e6df3258e51006de3258e511e6dc3258e51034fe7158e51034fc7158e51036de3158e51036dc3158e51004ff7058e5100cfe7058e5100cfc7058e511e6df3058e51006de3058e511e6dc3058e51036f71058e5114ede755
  | 27 => 0xf7459542006bf7459542004ff735954201cfe735954201cfc7359542274ff7259542006ef7259542004ff7159542034fc7159542004ff705954200cfe705954200cfc7059542276ef205954201cfe76d8d42216de63d8d4202cfe75d8d42004fd75d8d4202cfc75d8d42014fd74d8d42216de43d8d425b6dd43d8d42024fd72d8d4256ebe42d8d4256ebc42d8d4256edf32d8d42034fe71d8d42004fd71d8d425b6bf41d8d4200cfe70d8d42004fd70d8d4200cfc70d8d4256eef20d8d42216dc6358d425adef7258d42004ff7654d42004fe7654d42004fc7654d42034fe76d854202cfe75d8542004fd75d854202cfc75d8542014fd74d854201cfe73d8542004fd73d854201cfc73d8542024fd72d854251ef641d85424c6f621d854200cfe70d8542004fd70d854200cfc70d85424c6ef20d8542526ef6298542006f76198542215de7318542005dd7318542526ef6218542036f66118542006f5611854200cfe76d814220efa60d814202cfe75d8142004fd75d814202cfc75d8142014fd74d814201cfe73d8142004fd73d814201cfc73d814209eef72d8142024fd72d814209eef42d81423f6ec42d8142034fe71d8142004fd71d814209ebf41d814220efa40d814220eef20d814220efa20d814220ef8605814202cfe76d95322067e65d953225cfd75d9532024fe74d9532004fd74d9532024fc74d9532014ff73d9532014fd73d95325a67f53d95325a67d53d953201cff72d953201cfd72d95325967f52d95325967d52d9532034fe71d9532004fd71d953200cfe70d9532004fd70d953200cfc70d9532596ef20d953202cff76595322067c655953258ddf735953259def7259532594ff75595320067f7559532004ff7459532024fe7459532024fc745953258cff7359532006df735953225cff7259532006ef7259532004ff7159532034fc7159532004ff705953200cfe705953200cfc705953225eef2059532024fe76d91321febe64d913202cfe75d9132004fd75d913202cfc75d9132244fd74d9132014ff73d9132014fd73d9132586bf43d9132586bd43d913201cff72d913201cfd72d9132576bf42d9132576bd42d9132576de32d9132576dc32d9132034fe71d9132004fd71d9132586df31d913200cfe70d9132004fd70d913200cfc70d9132576ef20d9132024ff76591321febc645913256ddf735913257def7259132004ff755913202cfe755913202cfc7559132574ff7459132006bf745913256cff7359132006df7359132244ff7259132006ef7259132246be4259132246bc4259132246de3259132246dc3259132004ff7159132034fc71591321febf4159132216df3159132004ff705913200cfe705913200cfc7059132246ef2059132004ff7655132004fe7655132004fd7655132004fc7655132034fe76d8532
  | 28 => 0x9152006be40d9152236bc40d91525beef20d9152236bc64591525edef72591520157c76551520267c76551520147c765515202d7f745515202f3f74551520073f64551520267e64551520267c64551522373c64551520263c64551520057f73551520076f72551520157e72551520157c72551522776c725515202e7f625515202f6f62551520057f715515232e7c61551522257e70551522257c70551522373f40551522776f205515201cfe76d8d5222ede63d8d52014fd75d8d52024fe74d8d52004fd74d8d52024fc74d8d5222ede53d8d525e6dd53d8d5222ede43d8d5202cfd72d8d5258edf32d8d52034fe71d8d52004fd71d8d5222edf31d8d5200cfe70d8d52004fd70d8d5200cfc70d8d52006de30d8d5222edc30d8d5258eef20d8d5222edc6358d525ddef7258d520157c7654d5201e7c7654d520147c7654d520057f7454d5202d7f7354d5202f5f7354d520075f6354d5201e7e6354d5201e7c6354d5222f5c6354d5201e5c6354d520076f7254d520157e7254d520157c7254d5225f6c7254d5202e7f6254d5202f6f6254d520057f7154d523267c6154d522257e7054d522257c7054d5222f5f3054d5225f6f2054d52004ff7650d52004fe7650d52004fc7650d5202d7e7550d520057d7550d52006bf6450d52026bc6450d52006df6350d5201edc6350d5222f9c4350d52034fe76d8552014fd75d8552024fe74d8552004fd74d8552024fc74d855201cfe73d8552004fd73d855201cfc73d855202cfd72d8552546f651d85524cef621d855200cfe70d8552004fd70d855200cfc70d85524ceef20d8552006f610d8552006f410d8552235be7498552005bd749855222dde7398552005dd7398552006f76198552036f66118552006f5611855200cfe76d815202d7e75d81520157d75d8152226fa60d81522277a50d8152014fd75d81522267d75d81520147d75d8152024fe74d8152004fd74d8152024fc74d81520a67f54d81520067d54d815201cfe73d8152004fd73d815201cfc73d81520a67f53d81520067d53d81520a6ef72d815202cfd72d81520a6ef52d81523feec52d8152034fe71d8152004fd71d81520a67f51d81522267e50d8152226fa50d81522267c50d8152226ef20d8152226fa20d8152005bf7458152235bc7458152005df735815222ddc7358152005f77158152005f47158152226f8605815202cfe76d954221e7e65d9542274fd75d9542014ff74d9542014fd74d95425d67f54d95425d67d54d954201cfe73d9542004fd73d954201cfc73d9542024ff72d9542024fd72d95425c67f52d95425c67d52d9542034fe71d9542004fd71d954200cfe70d9542004fd70d954200cfc70d95425c6ef20d954202cff765954221e7c65595425bdbf74595425cdef72595425c4ff75595420067f75595425bcf
  | 29 => 0x256fa60d815301cfd75d8153024fe74d8153004fd74d8153024fc74d815302cfd73d8153014fe72d8153004fd72d8153014fc72d8153034fe71d8153004fd71d8153256fa50d8153256fa30d8153005bf7458153265bc7458153256f8605815302cfe76d954324e7e65d954360f9c43d954327cfd75d954301cff74d954301cfd74d954361e7f54d954361e7d54d9543024ff73d9543024fd73d954360e7f53d954360e7d53d9543014fe72d9543004fd72d9543014fc72d9543034fe71d9543004fd71d954324e7f51d954300cfe70d9543004fd70d954300cfc70d95430067e50d954324e7c50d954361ebf40d954360edf30d954302cff765954324e7c6559543605bf7459543615df735954327f9c435954360cff75595430067f7559543604ff7459543006bf745954327cff7359543006df7359543004ff7259543014fe7259543014fc725954324e7f5259543004ff7159543034fc715954324e7c5159543004ff705954300cfe705954300cfc705954324e7f5059543266bf405954327edf3059543014fe76d8943025be74d894301dbd74d894301dde73d8943025dd73d894357f9c43d8943246ee62d8943247ae42d8943247ce32d894302cfe75d8943004fd75d894302cfc75d894301cfd74d8943246bd74d894301cbd74d8943024fd73d8943246dd73d8943024dd73d8943246be42d8943246ee42d8943246bc42d8943246de32d8943246ee32d8943246dc32d8943034fe71d8943004fd71d89435aebf41d894357edf31d8943246ec21d894300cfe70d8943004fd70d894300cfc70d8943246ef20d89432179c4358943246ec6258943034fe76d854324d7e75d85430057d75d85434ff9c43d854302cfe75d85430067e75d854302c7e75d8543004fd75d85430067d75d85430047d75d854302cfc75d854301cfd74d8543024fd73d8543014fe72d8543004fd72d8543014fc72d8543536f641d85434fef631d854300cfe70d8543004fd70d854300cfc70d8543536bf40d85434fedf30d854324d7e75985430057d75985431a79c4398543006f761985431879c4358543005ef7258543245ec72585435ff9c4318543036f66118543006f5611854300cfe76d81434379c43d814323efa60d814302cfe75d8143004fd75d814302cfc75d814301cfd74d8143024fd73d8143014fe72d8143004fd72d8143014fc72d8143034fe71d8143004fd71d814346ebf41d8143436df31d814323efa40d814323efa30d81430057f755814324d7c75581430cf9c435814323ef86058143024fe76d9152236be64d9152014fd75d9152236be54d91525f6bd54d915201cfe73d9152004fd73d915201cfc73d9152236bf43d915202cfd72d91525bebf42d9152034fe71d9152004fd71d9152236bf41d915200cfe70d9152004fd70d915200cfc70d
  | 30 => 0xa01c0000004000002004001c000001000801000e0130018024002000001003001a02e0058008000007004000000000200080100000120020000002005000002800e0040040004000032000003c0040190000008002012000002403a000000001800002601cfe76d8d5427ede63d8d54024fd75d8d5402cfd74d8d5427ede53d8d5427ede43d8d54014fe72d8d54004fd72d8d54014fc72d8d546267f52d8d54034fe71d8d54004fd71d8d546267c51d8d5427edf31d8d5400cfe70d8d54004fd70d8d5400cfc70d8d546267f50d8d54616bf40d8d54006de30d8d5427edc30d8d5427edc6358d54014fe76d8954276ee62d8954024fd75d895402cfd74d895401cfe73d8954004fd73d895401cfc73d8954276ee52d8954276ee42d8954034fe71d8954004fd71d8954276ec21d895400cfe70d8954004fd70d895400cfc70d8954276ef20d8954276ec6258954034fe76d8554024fd75d855453e7d75d855402cfd74d855455ebf54d855453ebc54d855401cfe73d8554004fd73d855401cfc73d8554014fe72d8554004fd72d8554014fc72d855455e7f52d855455ef651d855432e7c51d855453ef641d855400cfe70d8554004fd70d855400cfc70d855455e7f50d855453ebf40d855427dde7398554005dd7398554006f76198554005ef7258554275ec7258554036f66118554006f5611855400cfe76d815426efa60d8154024fd75d815402cfd74d815401cfe73d8154004fd73d815401cfc73d8154014fe72d8154004fd72d8154014fc72d8154034fe71d8154004fd71d815426efa50d815426efa40d8154005df735815427ddc735815426ef86058154024fe76d9153266be64d915301cfd75d9153266be54d915362ebd54d915302cfd73d9153606bf43d9153014fe72d9153004fd72d9153014fc72d915362e7f52d9153034fe71d9153004fd71d915362e7c51d9153266bf41d915300cfe70d9153004fd70d915300cfc70d915362e7f50d9153006be40d9153266bc40d9153606df30d9153266bc6459153625df7359153014fe76d895325eee62d895301cfd75d8953024fe74d8953004fd74d8953024fc74d895302cfd73d895325eee52d895325eee32d8953034fe71d8953004fd71d895325eec21d895300cfe70d8953004fd70d895300cfc70d895325eef20d895325eec6258953034fe76d855301cfd75d85535067d75d8553024fe74d8553004fd74d8553024fc74d855302cfd73d855354edf53d8553506dc53d8553014fe72d8553004fd72d8553014fc72d855354e7f52d855354ef651d85533267c51d8553506f631d855300cfe70d8553004fd70d855300cfc70d855354e7f50d8553506df30d8553265be7498553005bd7498553006f76198553005ef725855325dec7258553036f66118553006f5611855300cfe76d8153
  | 31 => 0x380000000000038018056000002800c00a007003002400e00000080a00560080040000008019005000400200a000002c0040000118000002002002800800000900280040000050030000000000006000005c005009803000a061008804001c009000004c016002036001800e00100e001c00c01f0020034004005007801c00600000e002801e0000210014026000006000000e00200900680020040000070002007005001400000700a000004a0020068000006002001002c004004000007c00600b002009001000000a8014054006000800400e0220048028042000018000c01200300a80000040020000348012000000000400200001b800000c000002800000002d009004c00c0010068008022000004002000a01a000000002201f0020010008007001800803a00000b006c006005002000401600100100000040010110000008003016001400400300c0014036001000004400400a0008008034003003000001200700a800000000a003800c00000f000002000c00000200000020040068008004004000003800600201e80000080020000000004064005000c01200700080040000040010000000002000012800000d000004001200200000a8028000002010001a001000801c06e0090010000004001000002c0000010028000000018000800000400a004001408c00000300000100080020014006013023800c036001002808c01200a00500200060090038008024033002801800800200080000180110020054012004006003800a012008800c046002000004c0020000218000000002014800000000001300d400200c003000401e00a0058068036005000000006a008002005800a001001005400200b001003800c00200e000800e002000008c0020160010010032001001800002801200000000020050000084006000000819000000e00000480020010078000000001000800c00002100b001000a01e001000c02600100080a004600000000040080000098000000001005000c08600b0010014016010000000000400000080140000040000008034000006801004402f00b801400000003f802002e0110000000016006000000c00000400b8000000007013801c0000040080074018008001005002200101e0000006000005807000200400a80480000060080018048001001000000000400c801002200500100080020220000004002001000000005e01000000200120010058004012001001800000604d007000c0060000130024000002000000c01e00d0030010022000005001000a00a000800000a0020078024002000001000400a00b003800000200701b005c00600000100040020000028000000006000000400e028000000804c0010068060000008003000c0040090018000032001006020400201e000010804a00000100500
  | 32 => 0x18014032001c02603d000013801a0070030028006000003800401a011000000001600c001000c03a00a0018000002000010803000400100b806c07400f006800400400000c005c03e00201e80280000080088000000005007001c0000000010050002016000800c0040080018038000022001800000000500e002002a019002001c020007004800c004000002006400403800080000100020008000008005012800000a020000000000e003003800800c002000000400e00b00c802000400500000a0040061000010400a00c00680880020040000030000002001004800000000a80080300010048024004007000800802c00000200400440090050000006002013809401e00b009000001c00c0020004014011000824000a0000008024012012001003800200b000800c00000b0030014000004000003403200002000040160010000008016002000000400e001004803800000d00c000000400100a800c00c013004002804201a0000020040001000800c000000008800000a035000803001a003008800000800c000800801a01f019802c016000002000c000007009802c0260020020000000006004001c000016001801c020007000006c004001000802002a0040040008006005006802c00000a012800000c000007000002200a0088008030006004802c0aa0180020024012005009801800000d003800000000000000340080050008000000000000003000c013003804000801a000001c00000500180100180010000044008005002001c004005003000c000013007800000601a00a000800000601d80080000020030044026009006001000800300e0058002004000000001c000000009001a000001000801e00000f0010002000001801c00a00000100b801000600000180320120070018014043002800001200300700180100000008000000008009803800e0030000020012000000002c01a00501d8020000000001800804c00d00100040740070010000000004004800800a005008800c0080000058000002001002001800000e00200000140000060040000002000009400600000300d000e0050050010018000002800000e00c00080c000600700280180000490020064002002001007803a01b000004800201d00400700580000020000000002000802007e000002008003e000000801401e0060000098010012002801401600a002001000c004004800000600f000004000000e005805c0160000008040060003000800001600a0000000016015000008c028000004804c04c03e010000002e000008800000e009002806c022005000000003601a000805800e00000000000260020000000024005001800801800400100040040000010074004007008003000c00c02100400000130088028002001001000001402900080000000110
  | 33 => 0x10b808b8f9e4601ec03d780746dd25063c78000000000000009f0126244000004e2049800048500008711c180b89ad052317aea0416000000000085044495200003ee288e2cca02e9d58a3e96e000000006b280222343c9069826b0f3404b00002cd000078880003b19ab00000000a46079a19b0000000001e370894000006da528a69465b0bda5a3800056800003601f162fe1ce47b8800034500004871c86a0005926598000016000027499d068800000f8a15c77400001dc24be0759a4005d01901b080000d4000080313689aa01a600a17bc9d71bc0056893a41080003c9913691c097a00006c86f2024c13b0000631800091e98823f90f8a32a00da10d93547760fe60000b409c8a61e6fd800000006dc7868c845f927dc3dd00007e7000086a9a3e9491b0623914fa7ce8000a428b42000000000001760000094002000800c00e011001801c0020080030080032000000800801600f01580f000602a0010028008034000005c00a005000000000a002000000800a011004804000001a009003001e000002001c008012000003400400300000240e800200080e805400000080740020080018010010009005004c02c0000080000004000000803c0000000000008000023000800000a010007801c01801a0050064032000000001800c000004805400001b001004400601400080340020000020068004001001003c00202c00180040020000108008008000002801008800300a002800a002000011005200000600ac012013023000000000b004802000c00b001801c05a000000000c00002e000000402a00a001000001e00600500080e6000000000001e00000580000000070028040004006004800000000e00000380140010010000032002000000400a004001005000400c000804c01a00000c0000002000001000003e004005005401200d001800000a0600000008016027001007c00000700480d000600100100000000000000054014017001005c008000021001000e001001000001600401d8000022019016800013e03b0068074000001017000c0000050020010092003000806400600200d801400200b001801000200e00e800800000001380d0006002000002401a00900a001401e001008805000e003001800c0080040038000010001000000401a0000000000000002000802000c006002000c01400b00100000000160208004000001000800c0140080000000016002000000400c000000011c002000005000c00c0030388000008001001002401200f000801800e00000200100500050150024000002000802409a00a010800c00000000b8018000000001805800e002000800c006018000002c02400a009001400200b00380080280190020024098000002804000c001002008401800400e800000c003006800c00000100000ac
  | 34 => 0x63521420246000014907f21e98000775a4105c5a53e3fe01e688e0b9c8c6155c1f5251854c98ba41690da344129290a93ca3399158a3521d60a682b47618ac8a3280f60000b1015823362160c6e3af97e20001080000056697d0b0a6169b668c5256090180001201132451a5022268fb43a212a064b14542e3a20e33600000000cb28e888a68a180006d60f846b5082c000183a2a0a196768178e92d8f9c906105c9d0a19a3a080003180000000000086996540001d8e1b59d30000136600000005a7000085b1ec600000000e913ee00015f67178fca7819bfe50c9f40a0680d87d922ec1bb1c2613a9e2ca4b15e8105819878211ea00000003309f0c505000088324b8000216400022cc50117e0207a2a400000006211a9a00000004e20adc0249b4a72b07486b39f1e539000000000007dc9e502ce978621d000043404a679ca18a4f400004330e5a0609ba8000281e99800000000000538179265c1cf43ad09700001c0400000000001bbe00000000191c5200003de0000000671186410e1a8450592789aa931e00025aa000051063300000001c0e3d411784911c3c2330c9e5c11050354000011fa172021225a000251043d0000113000000006ba43496bc2f0804600000000000c107df800007b89ae0c816fa20c85565321eda879242c864a1ba03588ce832831220126b23c327869da8cd672e84ac88099f07ac800035b0ee039aa1fe01580006b022e42f80000808853069e00006b2a69c56c95867b780000001c9c000000094700001bf8e48855126c26c8b7015e84964c98d589be20e00001848723136e2a4049c0eb99f437b11b489d0ce45f989fa00007567db8bec2bba6ec96c27764b100fc8f4856c00004087b489602e925ea57016923729c101d38e0497b8d881f9800074f8c5497728b200000b0740800000017980000f7e6371dae75391a66f28e6685a0f907bc806063e88bc2cf172807a0910308a54a2fd14a01ba0b1a9c211ba0000dfc79e2386738015e924141087ba8ae35e8340000000097c02680ab0ec828585da5020c667ab0ff00f092ea0000e9a2a686661ba884a447a85a4a2a2c86941c942d42448a0ca706043800012913b400003480001fe800028424d78a2000001a227722ea4a78ed290b863285080007e8a0e426a993a8cc284e00028286b59a8273880000000d9ea0e00009010f9479485741c88b5805285d036a28268dc1b6209580500000a8a5379a3692c28f27128d6a89904c4178942c7eb189a3668000380004204b92b46f4868644195ba938a24a8e0011c89a165e00e122a565a71058513a271b9b9c3a3206e3bb82703129d447f01a968de03d84948654a1707fe5ff11de2030006a44a0b80c50d9c6bc1dce70a8b441dc987c1ac21b4000179036c00007f684e603d1b889009c8e81e1096877a246000
  | 35 => 0xd0c6a84717b248a1024a2d03e88901cde6991df679c0fe81d08c2678725d68a6179ca1f82000748e220000226792094a6361dfe801203286814fe0000000600a6824ff215e031000000011b267c895a7e5000069980000000000a2d892a609256c5629c30846869a9449bf418f050c2ec9f464ed82c62cfa62242698324249fbe0b283da19e9e207ca95b679a888a9b417da3c1147a1ce0b6e1cd81b441b09f65b604d2710a8747fd9a76734a83474408183ff22564d591ae43a87ae4d090e224500329f21980818881a46299d8361128e2f01dbc8ee07947bd15602951f82161141c7610a30840852c52c933a7398b3691582b04dca8408b0a9043dc09a45638fc4555926a6a90bd44098e4c52c0150685a48a3799d560c304922e68e4e24d97e802b98389029eca77d122481698268d520262eb818a240a7f088e8bbc3f21d5c6f8261a2a617d211a21e85d912266af06ac62522728ada1b690711f29a2a7e007c03649c09b04200220a670919c53c82f00d284da49e81aa3850a8e0a61a3a5a79aac38612d433b875033e0388967190a5b723a400026e8177919630aa3e800013d600016ba902000000002384ea82445fd0a782a18000756a932221800038088725bca4de72c0b7600003dca0080008fd00005e687ec08883a084aa862000199e00011f65e7893e59ca75e00016de7ee86020251f903588000a161d1400026120000fe261390aa5cba8fc00007ca4120cae0001a5870900e856e117c5c3a45c000228005b807c81280007eb800028e94425ee1dc88ff000000000002b0a22412099641fc21f87f4800020916801ca9a7c0001d1691f800063200000778f6a68502d00f984a06bf000036f800000014ba47b1cbc2428000000042a000226a00000008000e340000d185960000438058202700007968d7e2049c3419016d2003a8b070e1b7834482a64352880753171a7311dc21b913a458680000000000000061c00000007cb10162b1234230c915e95616e491e10d600006c60001efc9921e6800000000000ae238d8000a36a4446f40000263918400013bc0380000419800000022103981f5a7478000000276e6d0a63800020a816b000000003725c280008148000243a6f40001e8400000000001d0c00500000001d886688cc40001756943000000000000000000000225452d02aa8ed1f86145000073f24666028000000203400013522bd89200001c7a41122586a7a58a0dc18ca1da9b689d60000452800019f257c92b251621a8000511800027a090000000000fc800000017a2a2a264042d000073e00008c100000af1290677915c00000000000e74597045281300006f600000001e6c5a5a08a7c7085c7f0859e1d98d464fd853a04699d674611828cc95542a30d327ba08f446b00000000000000267e4e3a4720001fd8000255
  | 36 => 0x8a389061246c194e52fa8ac40490a666d133483f0c0061b03a600016ea20c16303069d9619714965bd0f7c1858bc851a066a000106e7341f2265e006a68ca56a48f11e65de80006179f4200001101ea064849a214e0001eb85ce8988330213e000164000022b4000106200000007b5162a5dc840256980003528000678282a5f121280868a9490025d4708981a5f4000051100003f30000000000000026a00000000000129400027807ab8fb61fea3a8a2994ee7801b8a249a62a382230e8432540025800065f9c5061085520b09a0e24105fa73a9cc051e17469d917b422597ba0f3a65847f241682c90f09a210724b1969a7fb003097682a04639730297825498c9eb613025c0809153402988a23ce06f229205f62aa01f2047952c32c10000b5052a566219478c19cc09c818c25513fa6459b468c928e27aaa5324b99a9075a01f41db21ea8d79af638708483d104f27b819ba37c92488609c1a564284634123ea298047c5470d526dd83c464080525cd15e07a48aaa0e510c690e22962962100311a0829b493c2280892431f93a077102282a118f281e8bbe776923456fa34e1c720884720dea52e17b057b8e1e52d8b1202f1de21be81e27c6a08e7b702c05c6129663f000068190c82e1033c000098c8d0108c60a0cbe22813444800e92582921833f1b863568f202eaa2166ca86a01671b9a11085401370bfa61489768241af480fa3c82d79c5c63d97ee91522c62eda7602520d28179091c0828b4e52b0be455986287a5a07032487d841c24dc18982503bd06d46389bee548995c1869aae62c03ba54513a89fe82b81e495285490a381e88c1e6ad0eea0000000000000017f000088c0c488c18b167e28000329224420a062a32625f23379192a030ed000028d29f0a61c000141a1ed1bc260b83d271014d800a8ac64ff959e36f0e966081f0e0000a1e8e41ca800002e69d28000000066454f8aea06f081067e8f22529a8ee39899da9218fae30c274e3908d24182a38804325ae4f9006258f0d2e8b5946229a0da65c990065c325789bf27c47ba999a00000005ad84408f599aa8801f4c34716b253008b8a3f83445bf00000002926000000000022a21ee2602146941e64391e23341f0862a23ee4a695ce3cf23cc00000008fb27168ab00009a1000064da71c974232ca06000056316f8314a4682570c644a31fc62ce00000001f766eb081c000043000018e4000267c0000f0a255976c13a1402749a53c47187906970000498900c6c590983ac800053a80002d591ca00000000000000000000027980007a40ee481091565f506b42f302dc1f49c4400897a81e00c0a6d79e8a604801669c00008620000000267a15fa9288c89b2e4818b521cb903600011c28c99e5c000015649f8c1c1bf0b8c3bb0ed45a98ab400018e600007dc0b4a0845a
  | 37 => 0xf80546000176843b9d9c83981ea000098a5871c087e9137082b1cc88f380000c5a43a205a32a0d5a634000016a000000088c93ec000194c27180360dd17669d327ba466131c1e3051e2bf099a2ae90de1c4217894d935a77998108738a723e90450742903099b083459a15dc4fd144e9919fb829e8e287f314ec71505aa0fb9c1e301a56e74800003d626e07b30e1a2860ba067922c447e0e2e11b800039b886e1fd182c9f5a2e89cd93360fa830a2249b4e74900a2680949a43e860c68028d8067957000024ba7da03a86b782963681de87be8e5200000000000c5a00000007898cd200018865b106a49d103c6581185c6a71c9a0d81f521fe0cb644c033089712a27689c62a3e934e9ad15d66621c82917893c5fc00005ca96a007b144a4fc9994a2827685a21e0443f9ef810c80008ec0b7868a179658812bc00026ba2db18be34d0a66098838651000009591c68000145c94980007541d540000000000000093607e00001550a2794d4000000000023840d5263c156966e00699501380f9840d0cf2775139a163000060c000071c9f0062303808f296aa000000014885b2750122c0000414a4599b8000163859c1114000198600028988d29fb47371d049e092e42ca112a25e0000596a55c93388ac00009d800015b01081ae496f222600024340001b7e4bb046444a035c3aa23c48230fd632980008ae889e61c124c8dd0a9600008900730f1800000004b78000829800093f88c69dc24601e2000000000007b61c127b1000018525902b480001159384000196a58621ca000000015c800084c9a2453d1d7a0138000425000087680000000000509000029c0e3c0001d7410894502158dc47ea24f096620c2608800035e253060a86f4000226e4de937e298831e00023524be8000407816c29910685370fb204080009a790c05990000000000017726261c00000123a7d41471bb600015d2819930026511241b614ca25fa0ba5fd91b863d16505a8856802a067e2bc068a30e0b245f32116948270c8511272a48a2fe353162287c9c5a39b23124160cac9c0113e8f6906415ba3e28dca66e9a9819c9e3a4c813e0eda9f891505fca6ae4f6a1246c40ea40a70c120881f025a9204e3940e6822311903bf8a2e7a19e4600000004ab9e746ec99f80000624000000033f8bba00021125d4065601200886f72204574048451313a692d21b80961dfa3ba21f02789ae8000075490a036835380009ae000098512f69e2034e3d29b18959a368401117e4ce129823c06508fc0192444a17075c132006c08ea5d2841e9390bf60f013066f7a8840ca1dbe68b148e4ee9bf2119a19096c83c81730c564ca24a25df2796722159293d8d382c88f608b78a6a05e09860d4a45a2ad8bb41390cf48be99729ec8faa8418ea20a087ce8688fd448fa6cca3aa84a00010
  | 38 => 0x48c02096363aa9f7a82c151e41e1c963eb09905aa1116898252a4cf265055e96ce3ab11206e9953625f16486aa279447380c04e301c69c61d469f49c1642180d200014d6331994423096e81ff0000a1c800032aa4bc000268c1a0145a1c1287007f026e94685ec12e8fdc000249c46f9f244b4121e495195840e80c8796140e89f1be63db0bea529209e0000000793a81499c800000018b80000a8099915de982000085185980f30acc6a300000001b2283d00001c09b728d821408ec91f487989a05d004b403c800077e0fa60000c14081a5220000a4220e26c46798e380710ae0000124e0000a3c00025f696017540000f100c886928300b1c9bc8ec201ea2065fe9a866341b5a3689d7e2dc9bce5c48dda194804086b17808d41a4a286803e40f0dc03a702408a223a629300042c60d7c14a0c584e51f9a13b802e0001ccc00004045bb16f09bb800045a1a1200008ee85421302f287be6b710f83a600000000e5e00008ca92a89f49f6025c2fa26b63a2a220629800051c8000824800000000000001b3200000003060dde417800098e88e80129e6607395420001b4c7fd09b69fa132a0000000000158268d1776002975878424ae855978c04f01fa9fda0ea8268f0e8b603f471b20e29048a2c83ca7ee66b2064451000017fa71a14121268b70f80000143e04a800000028f60000f889d01cfe68f28cc72e0ff626780005a6146036e276c1c1912e5a3224e2b780009f29e2467a98184c39ef600003b89668000000273c0001b0e5562006589a2129779b845c790dc8bd08d60e58ee20de1c6009f822ca25000000000002e7840c8ce0bac00025fc0000000a090e5c59808b00001e0a40a0bfe52f000070099a00001b0c00004fa17ba8666ec00009d4800000000008038000a3b0000841212000004065f080007ae800023f967800014940a1038c2f7800000010d8284000000000000000000000036e00009b000000005419abe0001f36000000078f9cce6921f0a771a5fa35b80004928db226a02928a78c88196805e31d86cc5fb241e4bd083c5a425ec000215a000035a000000002d80008e280003d2023c23e800042fa3d0000000035a1d6489c167430f8d9633e9b507d8802684504b82d21202a081f043558d0e4b0999c00000004c28ac01c68f368ca22780bb92be400957680091bca47841816e25845481e5e34f92823720538943937400000006a2a1c83322292000000076488c41228146288935c00023f20001b6e0000000000000037c087e9a6172c4041e0236a96e679b908844400000002724375000094ea4809b6125c52496d6335278a9de1628000271e21b000000020d00f405f04730000660862c7fc97a42f399100002816806a920116800000008209260000000062e1ad8a0014092ac76a81dc16b913478e066e80f05e03
  | 39 => 0x4df1db805819061f184d478e8b685c1a762359a6fe60d05ba45b9fe0169813a0768dfa4338ba221e0efc876168a2e50f5a42a13089890ef806e8d42172a3e062a953848c18043b99c561a71020960925a8ac0ae828304ce83e97007600234a1a270e70da43095d1aa005f0be21dd18c44aa9a62060094e1a305a86a98000000143a0979bec61c800024310908318f8c6fc12cea1e9bb46648b8a44e106a27f828015a839c5048b809e300003649ab619194560aa21f613d08d816f93c00761d940000c9a2f98a880002452973205693d098063384de68421a423480005e21f183e380006bb00005d080000450a568670c90834914870319d40000dfe00001309089fd665d9b1277b98de4e421620c01ab21f026920ec12e84531920000000037a087c0000000764289a77f00006f10000729a73249d041069582f82be0c7400026dc8521afa02805c60001a604b6842e00015a40ed80009c2800000020281b8177e7db00000000efa81f800078a04346f50e7600000001b298b20001dd20ce238293a80009ca19267400e0e8d58aa2160078e30e873067a1cee4b883083b720f051d95303b7a5425398a0e1de185877c8808302265e80da6762598f7a88d95a24a9965611d178a61a8bee1ca290258185a46878fa850b9470297000085e8c042261418820057051f25e44c4176228280080198000669811836500000df000045894844c4a7b668117aaa4c000000000005c2151800026f0000102e3370c5e0001c1c000008e8bc9d1a00016ca03e00004d0000000000005190866218110e00001e04ef9a2627b923636409967f4250081a81b63500c2c200a0aa2f480002d89de0000197a75d800052a831814600009b2a27a1c2a21e1d8a1ec7ef17b615316086d58c345410f52000279e97120867e816322dd000080e802048392dc48e917200017a032e047a7ac248e26107465e08afa8df89926ce940650303103cc00002cc0000477173207d96fe79f99084b28b7e000277a72d12469be998e51d15c68f511a201d81383ac1fe21419890799060e32f15a83da00009fb16d06c90fd29e101407c486880000000000215873c0ab2340a77e6e617a676e8932342148a7289cd48b9875e4fa99c8580a73a0b3194a4e7884655a89c03d998c29a420509a5a6a4a01a64472d848849c25a81c20d5c0cb20162a4a67474a1db66f902fc7d3841c88526e43110d7449600244830e062caa34c50d867425d1a7a128855420188ae32891426a007827af95ec62b83f813599423e828ba1f79b800b61ac89af1cc670b1d324be27aa03f809a7ed9f9281b108e4ae25f84569ac64f8a65c87509b46fa1d7827c97c68d18460000246c1499052a3085b063b24a88e380000ef80000000a2834880008bb899c0000d8278489d49f7884e3660fea2cb21661e8191e1d30
  | 40 => 0x1d488e70000572923803b80002a818502d8186202026c64cc8516a339bc64bf100a9880ffe2b4000053e078a000218600023f666c00007ff0e0c5f728b8969888200013f083e0fc63cf800000000000cb8d3c3bd9a4e00028d004488e670ca3024d823c01f6a2d464c20a257e28968c700008531c5800001640658e3a00019546578a9c2821fd4030a23c7a095128a987201d28cf69721c640921eb42b280be78f1d0e51b06a60001f9800000001f2000000023ae290000036380000001e427471af8000000000415e60000bf294296e03478dd035820726e80dd81091f8803418e0227000073da4623d18000221091601e0a0457f14ce9df249207200000000000000062212b94da00ea1cc4849a4c00010ac251800029492609ea026089fa1083550c6257e854e173800000000000000000a3782b20000000000000004100000000de40001b1e00000009e720ae000260a00011e09caa4e807280000001264000000000000000000930635248c000000093f04fe9ba9c900fd871e30f257a027800000003d40c081a001f800081006ee7eca2b200000008b6800000007a49c11d1200020ce6b107ac64b80003ca91aa0000fbc09280006128000056082e45b17029b6a0bc4c3150c15e27144c90a6c00493dc8ab89287cd10bc1bda2f61af954044b1aea92089fc2c08d6403ea3fa95d8ec49858d2090924d066ca40c09d96e28270d00735a64a7e5967a0b11f5c86b92e04750f283628e7a4bf81e4102a5e821c0912035153a833037e2929ebc66d971400027307f9932c11b0000000010a00023dc000000054220dc8ef09520001c7c2ee251e00002ae88ba2ca2bfa88268884c882612568a0980c82d11407418000a23000016215da000000040380000c9864a00000009ff000000026ce000000000010409530b7a0000abc000189600000009349a72981800027b0e2a132a1c00d9829400018925591d36000221c17d07586a500000d3255a032800096e8000000146a0000f6e54a8b5c000254e9318b0c00000008e6191a626155e9f3883a2c19bea00026a2080815200007440331c98888800050027a67fe1a183bca57050f0b2661a292a427a01e7f90e844cf967600f28aa7a88ec05879fde1be1c2812f0c4c42806426bb8cce7e10ea69e61c7e75ca7b039f80002a7a0f60000000420a5a058e9cbe8460576118800037308ba2131e0c65ba848a4508c81669e329ef9a8e71c25501b8a83a5bd8f720000000690a4c4000252e6e4000038280006d50ff223c9d9a57c1d3c08e91860ea831a31c9d428b3a726a140400a1801546de99460e10124a300512a2895948d89fdc4c69bfa81708ec29f800031c089400025723f40000000000000000b46d805f24c600007d217be373a7387faa7a46d71f4475b1b0029b8108a470c5c7282096a0392a8
  | 41 => 0x66b8109c2cba04880725521d71546022a40e65f16ee309086804f82c8619a35a65013308ee963e9bd9f5607fa3009dc8a5a26e98a01a416628b821bc553a3080b580001ec0000000193e7e0230c3c1800022d0eae65800002ea15cc89300009af8cca37d24586d00998171206041d27a279f00003ad8470000000067d96347c1885443b1cc22e20fde01715aa05a285466405d416d12ee7b92054371930480a8ab066285ea8179bd622c85e818f8f3209387521560eba02b1f509f4002c5cf863a45520e819a27c61ec99847c9980e84290e447c085a6e7938a0531f546b31d221930eb89f305625c90f146279ece02918407770c0c13187d031426368ce827a7e9a2428d9991872904b00cd9da42e18c363a7a44e2b5935056214382c781a88af81348d9289c8c299963901cec8aa24968369d8a6291ce825a1f781e784941421ba2979959a4ee1ad83ef8f763e4a17c000262808794985408230151172067fa1c691d17d884414c43e8a33e05122bc00023b603a92a4a089038000000056b0c680000000000000000000003f605a2000266a00028c6000226600009bc7fb800074e918c75a9032000128800027b411c800093c8086520a3de19800005b68000000150e0000f7805e887696786180000d701a513e600015103e5800000013ce6d10000000000013c239a44314cc405081432e80000000972000128400013824a0032489d8dee21080009421a6c9b7a31e0b6800041f06f0a490ca029100005e1154a2af9b969410dd66cd076e63b80001a38dd247680003af0c42835865800000004c5954c0eb222c46d901a76c0ddc2941e9e38ca90024780440001b6a0000000000000000000005d685a000000003a411a48c6a0120ae873e000000000000003459f74378860809080de454896a3e1957e7dc10ca0001dc00001c6a61e8c7893990b600000000b8214a57922b81e18b6448ba64244f080e8bc110a28513c60169ea832500342489e804a70bfc995052096508c00baa62c28d27460858f422e0854a2ae13d40000b6630b82e80a207843c000008e499744fa249ea3d00006d202be0fb0a460000f4c00001c07e30dba63f8000000000085d981e56f22c05891b3809b00005eb08dc9fd00005db86960000000000000038985942741a3000024368ef84fc91d8a262bd000035119c62b987c200000009b582081c5800047419321639b8e508800004a183c26e000000013d8712260e78b891a99a070c00002fe6b086ce36d26e60a39fcaa3e160c3eea44a0000e70070833a02e00000001bba9eb0fee78782b6208a5549faa5be7a9228c000069e860275a00000004b5971c96d8000a24800087724a426994e2000223e00021980860000000143091b8f16000022aa0d96b8000000000019564d3000023520a459327545b318f80000000905
  | 42 => 0x23201fda17e38c226c58b063600010ae7e399a89a388de00028560e692ba53c0000241938000002f200000005ff8bd85ac000062200725f796423239b7000011d20001db28fe1ff00001cf20000a36048a91000002a285b80001160e8e4b005c23ce955a053a37a3c48000a19210e65205965b083b419380008b41a0a176157c52b85d67581f9e658a5c686a06006fe05b6494177000000000e49748000008c00018800000000000151a06381320f811260001b5250993d2000160e30380007b58000276a138313a22a93b00002d50fda60200003f39c745309998413a37c83788be3d58d0a0001dac211228e00000000001b3e61d2450000259243111e411505f808c9b02112a21a3b588e200000000a1910069a0090605a1847d615783929f141a119ce793212e3cb964e69a8aac0bd95f2628a4da45c16949dd28786c51644236a4322890e2072a8184a2f0714687262e779286e2ec272c4810bd055c907e6db01b25de1584a421a080d627e666b9dea549a73ea370204229167c847959c8c40dac64a000060000683d525289eba068644873c1138c7c273a6ac1fa09ea7b403fa5ce0000429136ca2288f82f5a1f4157800000009c2000150a5a10000558800028704264821bbc961873a78594fc09f0d3a62d0d76816000000019dc00025a2a02a67805fa604000113a2b9233c87880006c214a836900009a1a64e772984c6c2800033aa47c1f91cd8599a8e00001fb07329f7c000000000000008cd24e024b80002f1a7125f280002b6a1d051b800012f8938000224876d1cfa65a175e9b524d416182460000000222149e000043c13323c67bb80004b2152e1989c4639613584ac0a0687f10e6867842c2d6840e713260c00015ae95a285200027fe74d23489fe191c482a34408316be6aea2d2760992238b0d8ca1f06040d080008b8901c59aa8c446500000b904c2000000000028886f6800061e000059b0000462000028c800091a98e853193b08ff856400009ca000000080e0d1a47f8448a3c0000000202c24d0f08a0c1a9227312100001c3e0e38ef007401886b6826a05980004f8000000000005dd27348630dae7f20bdc000045e0000000000000000018bc59196864dd91fa8be00008dd9b2c94e1486338a7501841faa86fa90e61d9cae5161e8c999852e000063492101a4111a3d84e580000001008a131276811127c69f8f5c8d7030e20a800084f193c257916a3c715009cb9c8000000005faa7a0545a7927ce05e6835006e42c80f07ff936486c87329b0a49a89480e46eb9afe5cf037641591e850a8a124b611647980e3e4bc939c978038249b8ad44ec83b20c70bf0242055c97f9e8e3218b0442c11049fca13602611d606b96826df07684ac89d6320104684e877c24b192476a263e0ca843a0a91f324f21ee69328e7c31ea07
  | 43 => 0x26585860639c92d280811667a501420001a6e0e6272086c004c0be9af2308188e000000081182ec47116c6250a55e27200000001a523a80a7c127a7bc1c481ac0001e7a00023581520ce81b0074083225c279888d025b290ca3208408820aa680412420d785d29330000634a79a00000009b8800029d00000000f4e72c986044710ba0001be20001b364089c9e3849428154119a49004aa14380000001710a3919ee1509e981c90b928bf1c4e07e045c0d18c968e31ea67f115d8a1799d204590fc19c1dcc78a9aa292983069308b4a615282c67b00001f318465d4914e64110180e89d528e792f0986274834c09a27028c8251f97ce7da8ece0001e8883b84769190fc2a0207ee1e587b6258a6c8338016206197941ae1dde4469ec884b1f306e091080bd07c412d8f8274b1c3a000156c220077676780006ee19a45d30000a219c2e98416c08cb800006e13f80000000300954875f265a000000074a93cc21e9d8c8e59a88000080a6450678448964a00021e01e600001fa830427e01000000ff4000000000020be67025345148000a070d8693e06a801c10f26e487ba083819a033a7b84309ad275b800021404f66e3000045e89504de00000000000a0b800009695800990f2c90980004ad8000908000099480000000000a0fa2aa2561e560000000000013615f16c800000ba0000000721022485480006728f648f0886298c0120584986e848800079518142f11222973a7903e69e0e4c523e4000110200021605840cf075799e200015c28a6a662000102c9b013860b79c0097620ec2d194e8a469a385ab883e73686824d19c8a09d00001ea9ae658b98da3ec1d2ea011b3c38597c0395000019109e41978000a2f9174217800057a849a60d80006270b001d68000000029e000000000027da7528a2a310104c8a80c2878d80004999d9800000dc57d23ac00000009f90ba68c5828aa1120184d28e7836d90545d11b1a0cc876452423e692526560948df63fe806c1b103ca00012cc90f117618806de93e841a2510b962da9bcc5cd8b0e1e712209f0039066f05bc72480e287490a28a113222c223a021495e219c9e184daa0b69a007d61de9f6057fa57e22a8f023a005325ab1d66000229412ca1344a1907a4cb80004211ab81d8244c09e028c4eb1a541f884d03a1800000020fea1a8b9832302ce56d181c6301dec785082603986bc34b1f5e1aa8d266831b2067f24886ca00000e29b940cd00007421ba45f20266000176a622911893587269931eec59484a8468000083125b400011a85d811d800025d251995c805c058aa049e9a79d801c1b4990065681480000000870a5962ab9efe9800a4e19d800063580c66c719387c40836a3a000033b02123d0000077c130295184901b400007561ec27ca000000000008a400001218de0000228a00
  | 44 => 0x6cc000041d80003b30eca00000000001ef096b000052700001360d2a065121a54f207408da7662d318ac000036c6919f3c60f8000512000000002107051480000236a769853e9789a2e00009c46aa8ad86ff28a41400a76467853c5fe25a422da4ee1c39ae21ab8cda0ef00aa0ff24b243da51488a08f621915d437e1baa23f05c008f916055b9f6680c19be3d88e560dea0d87588d0c9ac241a7c807bc0f9216a40a9722963a174006184422a190c68a93de4e6290674e1f2e8ea82901c610e85f59b64a1da44640f8c9c0da8b140cf86386548ace25b8aec0e78b7c62d8964305843e4d88cb43418534502a89094b1e349108ccc0f59ffa104a86c087207c96304284858590000010614d80003990c8a696877e92823948db1e4423816d453da36e3a5258887e94d263a8fec0d88b90554a4c005c98562530e44412a83c71d9a9826f957403b1fce82514882780fc09729f4a828145e3b6198c50d0c6c1a8967e4eb91eea4ba2181cb1a1a00028d6000005400000b22778f1a142898211a9a740001f3e8989e402a91c66057125e63c06308979a5e5d3a43e60183f0958a00a71e0d72000193406f80000000000000000079280004180d5e86383fe64a8d362238e4600001d47019c20187a54400015c4003000200015681b98e102bc923211e22504e494d01cd28e699c1a445510b20000175c805229c470269a4d205c861f9e9c7a813c40001b
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xbe185dc52044001ec6cbb8a4088003d81977148110005f0c26e29022000be183dc520440055d70cb8a40881433a1d97148110005b5c2ae29022053b68855c5204400175708b8a408814aea2117148110005e5c1ae29022051bc8835c520440b37c50e38a408814378a1c7148110115f1430e29022050ee2861c520440a1ec50a38a4088002f86147148110287b0c28e29022000b61851c52044001ec6ca38a4088003d81947148110287d1420e29022000be1841c520440a1f430838a4088002e86107148110287e1418e29022000be1831c520440a1f830638a4088002f060c7148110005f143ca29022050be08794520440b17c50d28a4088143b8a1a51481101b5f0c2ca29022000f637594520440a7ec0eb28a40880ebd8d96514811029fb032ca29022050fa28494520440017c30928a4088143e86125148110005d0c24a29022053f63549452044001ec2a928a4088143f0a0e5148110005f0c1ca29022050fc18394520440017830728a408814fd8d4e5148110007b0a9ca29022050f605154520440017c50ea8a4088002f821d514811000df1432a29022001be08654520440757c70aa8a4088143d8e15514811029fb13aaa29022000f61755452044001ec6caa8a408814fd81955148110005f1c22a29022000be38354520440017c50f20a4088142f821e41481102bdf1434829022050ee28690520440a17c70b20a4088002f86164148110007b1b2c829022000f6065905204405d7c30920a4088003e8dd24148110297d03a4829022000be18390520440013d70ea0a40880027a21d4148110287d020a829022000de38750520440017c50ea0a4088002f821d4148110006f043a829022001be28650520440037c10ca0a4088002f8e154148110005f0c2a829022000f63655052044001ec0caa0a40880caf8e114148110287d1c22829022052fa2745052044001f42e8a0a4088003e8d914148110297d03228290220c7fa35450520440a5f40a8a0a4088002f8e0d4148110297d1a1a829022000fa14350520440017c50f18a4088142f821e31481102adf1434629022050ee2868c520440a17c70b18a4088002f86163148110007b1b2c629022000f60658c520440a17c70918a4088002f86123148110135f0c1c629022000fc3738c520440a3f80e718a40880027ae1d3148110004f443a629022050fc0314c52044001bc70e98a4088002f8a1d3148110005f043a629022000de0874c520440037c50c98a4088006f82193148110005f1c2a629022000be1854c52044001ec6ca98a4088003d81953148110005f1c22629022000be1844c520440557c70698a4088143f0e0d314811028fe139a629022000fc1734c52044001f86c698a4088147f018d3148110637e1a9a629022051fc0534c520440a3f848698a4088003f050d3148110
  | 1 => 0x906bb2a4880023de05765491002c3e428eca92200287e87d95524400b0fd0bbb284880021f61776509100043fc2aeca12200587c855d9424400117f08bb2848800237e0d765091001c6e41aeca1220008ef825d9424400b0fd0bbb264880021f617764c9100043fc2aec992200587c855d9324400117f08bb264880122f211764c9100046fc1aec99220008ef825d93244001a6ecaba4a28815b4d19574945100365bb02e928a2006db3605d25144001b4e40ba4a2880036c8817494510006d2902e928a2000a74865525144001aaecab9ca2881535519573945100366bb02e728a2006dd3605ce5144001b8e40b9ca288003748817394510006e2902e728a2000a748654e51440758f0e1b2aa2880eb1d1db65545100053a432a4a8a2005c747654951440018d8e5b2a828817b8d107655051000656396c8a0a2000c6f65dc941440018d8cbb92828801a6d61375505102b69baa6eaa0a20018f4865d541440758e8edb2a82880038d19365505102c63a3b0caa0a2024ce476dc941441439c8ec3928288002f860072505100055a43284a0a2000c6c72d9531440bdca863b2a6288003331cb634c51000637b2ee498a2000c6c65dc9314400d3ab07baa628815355d4f754c51000c7a432ea98a203ac7476d953144001ca8c7b2a62881631d1d8654c51000c7a432e898a2023ce476dc931441359c8ec3926288002f8600724c5100056a4326498a20018fa86dc121440bd8f0edb2a40881731e1d86548110005b8c28e29022000bb1841c520440017a30638a4088002ec6125148110005e8c1ca29022053f63525452044001ec2a4a8a408814be8d094148110007d0a12829022051fc3324c52044001f826498a40880067a21d2148110036743b2429022006de07148520440059d6ec3b24088002bae19754811028574432ea9022000bab845d520440a575108baa4088002f2e0d754811028de441aea9022000be3815d520440a17c102baa4088162daa1b654811000735bb6ca9022000e6876d952044075ec703b2a40880eb9ad8765481101d7b1b0eca902205dbe38159520440756d50c32a408814f9aa18654811000735bb0ca9022000e687619520440b1ec30232a40881639ad8465481102c7b1b08ca9022000aeb865d120440a15d10cba24088002f8e057448110285f040ae890220079e88759120440016d70ab22408814eda2156448110005e5c1ac89022051bc88359120440b77c702b224088002bae19734811028574432e69022000be3815cd20440a17c102b9a408801e7a21d6348110005b5c2ac69022053b688558d204400175708b1a408814aea21163481102d5f1c0ac69022051f884350d20440035d10db8a40881433a1db7148110345f143ee29022001be286dc520440037c10db8a4088143789db7148110006f03b6e29022000
  | 2 => 0xb65591100043f438cab222000c5c7319564440018d8e432ac88800317d9773591100062e32ee6b222000c6f65dc964440018d8cbb92c8880161fa1f755911000637906eab222000c6d20dd564440071bd0fb9ac88800317dd773591100062e3aee6b222000ccf20dcd644400199a41b9ac88800317dd473591100062e3a8e6b222000c9f741cd64440051dd0fb92c8880031bdd77259110006363aee4b222000ccf73dc96444001998e7b92c8880023be03725911000476c06e4b222000c6f751c964440018d8ea392c8880032bdd0725911000667b98e4b222000ccc731c964440010ff0abb2a88800237e0d765511001c6e41aecaa220008ef825d954440051d904bb2a8880121fa1f65551100251f426caaa220008bf845cb634400917908b96c6880021fa1f6558d100061e3a6cab1a2000c6c72d9563440010fd0e32ac6880030f1d06558d1000636390cab1a2000c3f65dd16344001878cbba2c6880031bd977258d100063632ee4b1a200587e87dd563440018de41baac6880031b4837558d100245f43ee8b1a2000c3f75dd16344001878ebba2c6880032bc837458d1000656906e8b1a2000c3f751d16344001878ea3a2c688003271d37358d100147743ee4b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a20008ef80dc963440011db01b92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d100043fc2aeca9a20008bf845d9534400917908bb2a6880023be097654d1001476412eca9a200387e87d9553440074bd07b2aa6880161fa177650d100043ec2eeca1a2000c9c439d943440010ff0abb286880161f2157650d100045fc22eca1a20008df835d943440011df04bb2868800a3b2097650d100064e218eca1a2000e1c43d9543440071790eb22868800ea720d6450d1024556412c8a1a20048dc8758d434400953908b1a8688122b32096350d100056741e85b122000aae84ccb62440750f90dbaac4880021fa1f65589100061e3a6cab122000c5c73d9562440010fd0e32ac4880030f1d065589100062e398cab1220c8c7771195624400187ecbba2c4880030f19774589100062fb2ee6b122000c5c65dcd624400b0fd0fbaac4880031bc83755891000636906eab1220048be87dd1624400187eebba2c4880030f1d7745891000657906e8b122000cad20dd1624400187eea3a2c4880030f1d4745891001c6f43ee6b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000ccf20dcd624400199a41b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880032b1d372589100066639ee4b122000c7475dc562440010ff0abb2a4880022fe1176549100245e422eca9220008df835d952440071b
  | 3 => 0xaa0a40008ef865d541480011d90cbaa82901426b21d6450520006563b2c8a0a4050ba481591414800175700b2282901426b21d4350520006563b286a0a400fd8c7350d41480033d1013b462900026be11768c520084d6422ed18a40009eb805da31480053d50cb84629000a7a219708c520006e5b1ae118a40c9dc8635c231480a1b9662b846290143724c5708c520004f4c06ec98a4000ce980dd931480019d421bb262900023ba1a764c520004b7c2aec98a401196c855d9314800135f08bb262900426b211764c520004f5c02ec98a401196e851d931480012db0a3b262900031ba14764c52000636c28ec98a4000cce831d9314800199b063b2629000333d4c764c52000666298ec98a4000cce431d9314800199c623b26290003330c4764c52001477c00ec98a40028ed801d9314800199e603b26290003334c0764c52000673880ec98a4000cea101d931480019ca203b262901427360f754c520336a7a9eea98a40008ef865d531480011d90cbaa62900023be19744c52000476432e898a40509cc8758d3148001998ecb1a6290142f1205634c520005e5c02c698a40509cc8750d3148001998eca1a6290043631d1434c5200345f43ea8b262000c3f75d5164c400d56d03aa2c98800a3ba1f72593100243ec2eecaa620018f681dd954c40011df04bb2a98800a3b20976553100346f43ea6b1e2000c5f75d4d63c400d5ad03a9ac78800a3ba1f7258f1001c3ec2eeca9e20018f681dd953c40011df04bb2a78800a3b2097654f1002c3f42eeca1e200087d85dd943c40031ed03bb287880023be097650f1001476412eca1e20068bc8759143c400753906b228788122ab2096450f100346e43ac6a1e2004a9c8458d43c409159904b1a878801a1f21d6554b1052477c12eca1620068bc8759142c413b1df04bb2658801a3721d634cb100353a432a4a8e2061d3754dd541c400d5690ca12838817f55d4f754c7100356a4326498e2000c3d7495365440014eb032a6ca88003175ce53d95100053ac0ca7b2a2000a5e8319365440014bb06326ca880028fa1063d95100051ec20c7b2a2000c3f749d3654400187ae83a6ca8800297a0c74d95100052ec18e9b2a205ea76811d365440754eb023a6ca8800317dce73d95100051f420e7b2a2000a3d841cf65440018bae639eca8817a9da0473d95101d53ac08e7b2a203aa7a801cb65440bd4f300396ca8800297a0f42d95100052ec1e85b2a200087e8710b65440010fb0e216ca880028fa1332d95100051ec2665b2a200087e870cb65440010fb0e196ca880ea1fa1f41d95100043ec3e83b2a203a87e87cc765440010fb0f98eca8800297a0c64195100052ec18c832a2000a3e8418c654400147b08318ca8800237e0d72d911001c6e41ae5b22200087e87d9564440018b8e7b2ac8880031b1c
  | 4 => 0x148001a5eebba2c2900034b1d77458520006d5b06e8b0a4000daa10dd1614800195eec3a2c2900034bdd47458520006963a8e8b0a400f9ce87dcd6148001a9eebb9ac290003531d77358520006c7ba6e6b0a4000d8c74dcd6148001b96c1b9ac29000372843735852000667bb0e6b0a4000d4f751cd6148001a98ea39ac29000363dd07358520006c63a0e6b0a4000d6475d856148001ad6ebb82c2900035a1d77058520006d5ba6e0b0a4000da874dc16148001b96e7b82c290003721cf705852000cf5436e0b0a40019e886dc161480053d303b82c29000378d877058520284f240aea30a4050d64815d461481018dec0ba8c2900035ad817518520286b3882ea30a4050d6a105d46148001aca20ba8c2901435a441751852040657b02e830a4000dab605d061480a1b4e20ba0c2901436a8417418520006d2882e830a4050da9105d0614800195ae9320c290002b3a0e64185203f674b84c830a40cdce970190614810199ec0b98c29000372d817318520286e3882e630a4050dca105cc6148001b8a20b98c29014372441731852000557424c630a4000ccd7398c61480fb9d2e1318c2903333a5c06318520004f3c3ac230a4000b648558461480017c700b08c290003595d7511852000cf4404ed28a40009eb805da514810195ec0ba4a2900036ad817494520286d3882e928a4050daa105d251480a1b5220ba4a2900425be1d5494520086973a2a928a4080ccf605ce5148001b96c0b9ca29014371c417394520286e5082e728a4050dc9105ce514801f2df0ea9ca29003f539cd5394520014f5432e128a40029e8865c25148075ad70ab84a2900eb5a2157094520006b5b2ae128a40cbd68655c25148197ad6a8b84a2900035a551709452065eb5a9ae128a4000d69535c251480a1ad6a2b84a2901435a5457094520004f4c06eca8a40009af845d9514802135908bb2a29000273e0d765452007ce641aeca8a40009e7815d951480013d700bb2a2901425b21d6554520285b240acaa8a4000b6b8059551480033d1013b4829000273e0d769052007ce641aed20a40009eb805da41480053d50cb84829000a7a2197090520006d5b22e120a40cada8645c241480a1b5682b8482901436a5057090520004f4c06eca0a4000ce980dd941480019d421bb282900023ba1a7650520004b7c2aeca0a401196c855d9414800139f06bb2829003e7320d7650520004f5c02eca0a401196e851d941480012db0a3b282900031ba14765052000636c28eca0a4000cae841d9414800195b083b282900032bd507650520006562a0eca0a4000caf431d9414800195c823b282900032b104765052001477c00eca0a40028ed801d9414800195e803b282900032b500765052000673880eca0a4000cea101d941480019ca203b282901426b613755052033e97aa6e
  | 5 => 0x63b60a768c5200045fc22ed18a40048bc845da31480031d90cb94629001a3e219708c52002c3f428ec98a400087d851d931480051d9043b2629000333cc8764c5200346e43ac698a4006ad48158d31480031dd0db92629000a7321d324c520006663b26498a4050bc4814c931480031d90cbaa42900063b219744852000c76432e690a40109ae87dd1654800195ec1ba2ca900036ad837459520006d5086e8b2a400f9ce87dcd6548001b1ee9b9aca90003631d3735952000667b06e6b2a4000dcb60dcd6548001b9421b9aca9000363dd07359520006c63a0e6b2a4000da774dc56548001b48e9b8aca9000371dcf7159520006e239ee2b2a4000de380dc56548001bc101b8aca9000339d837159520006f1b06e2b2a4000da7741c56548001b48e838aca9000371dcc7159520006e2398e2b2a4050d66851c56548001aceca38aca90003591947159520006b3aa0e2b2a4000d67531c565480a1bc50038aca9014378600715952040673b00e2b2a4000de3601c56548001acca038aca90003591407159520006d5ba6e0b2a4000da874dc16548001b96e7b82ca90003721cf7059520006f1b8ee0b2a4000de071dc16548089ad50bb82ca901135a6177059520006b5b2ee0b2a40d0d6865dc165481a1ad6a9b82ca903435ad4f7059520004f4c0ee0b2a40d0d6b51dc1654800155b0daa6c8900034b5d754d9120004b7c2ae3b22401196c855c76448001b56c9b82c89033f6a1937059120004f4c0ee0b2240cfdab41dc164480013d301bb2a8900026be117655120004e7c1aecaa2400f9cc835d954480013cf02bb2a890142792057655120004f5c02ecaa2401096c87595544802165908b2aa890002d92056555120005b5c02caaa24000acd86d4f6348001a9aeba9ec6900025be1571d8d2008cb642ae3b1a4000dcb63dc1634819db90c7b82c6900027a6077058d20676e598ee0b1a40009e980dd9534800135f08bb2a6900426b2117654d20004e7c1aeca9a40009e7815d953480a13c902bb2a6900027ae017654d2007cb643acaa9a400fb4c8359553480016c902b2aa690002dae016554d20004f4c06eca1a400096f855d943480232d90abb2869000279e057650d20284f240aeca1a40009eb805d943480232dd0a3b286900025b6147650d20004f5c02eaa1a40019e8805d5434801f35d0fb22869003ee3a0f6450d20084e743ec6a1a4010b8e84d8d43480232dd0bb8a86900025b6177150d20004d7c22ebb0a40109ac845d7614800139f06baec29003e7320d75d85203fcf5c02ebb0a407e9eb805d361480fb3d700b9ec290002f860051d85200056741cc930a4000aae8498e6148001ad70ab84c2900035a2157098520006f1b0ae130a4050de0615c261480232dd0fbaac2900035ad837558520006b5086eab0a40109ae87dd16
  | 6 => 0x4e2e32eea98a60018dc865d5314c0031b90cba2629801a3721d644c53014d2e42ac898a609dccc76dc9314c137998ec39262980021fe15768853002c3e42aed10a60008bf845da214c00917908bb442980063721973885300a4b742ee2a1e400096d85dc543c8105a5ccaba4a3900034b5957494720406d3882e928e401396f8755251c8027a5ce8aa4a390207539957394720006a6b2ae728e4080dc7105ce51c80252df0ea9ca39004b539cd539472000657a06eca0e4000cad40dd941c80019ce21bb2839000339443765072041697aa6eaa0e40008ef865d541c80051d90cbaa83902026b21d4350720246563b286a0e4012d8c7350d41c800199e61bb26390003334c3764c72000673886ec98e4000ce510dd931c8103a9ea7baa63900023be19754c72001476432ea98e40008ef865d131c80051d90cba263902027321d434c720246663b28698e4013d8c7450d31c80018e8ca38aca900122fa1f745952001c6f43ee6b2a4000c9f74dcd6548001938e9b9aca9000327dd073595200064e3a0e6b2a40068f687dc5654800196ee9b8aca900032d1d371595200066bb9ee2b2a4000cd473dc565480018eeea38aca900032ddd071595200065a3a0e2b2a4000cd7731c565480019a8e638aca900030f5d754d912000556c16a9b22400087f855c7644800b0f90ab8ec8900022fe1176551200046fc1aecaa240038dc835d954480011ef02bb2a89001a3d20576551200243e43acaaa24004a3c8459554480cb4e902b2aa8900063ba1b72551200062ebaea7b1a4000acd82d4f63480010ff0ab8ec6900161f21571d8d200045fc22eca9a40048bc845d953480011bf06bb2a6900023de057654d200347a40aeca9a400387c8759553480074b906b2aa6901929d2056554d2000c77436e4a9a400087f855d9434800b0f90abb286900023de057650d200347a40aeca1a400587e851d943480010fb0a3b2869000e2fa1f6450d2001d4f41ec8a1a40048de87d8d434800953d09b1a86900063ba1b7250d20244d6c26e4a1a40489cd83dc943480052d90eaa2a4900434b1d15454920014b643aa6a92400fd4c7354d5248001bc421b8aa4900063b219755092000c76432ea99240018ec865d1324800117f08baec2900122f21175d85200046fc1aebb0a40038dc835d761480011ef0eb08c2900029d215611852000c76c14ed28a40018ec865ca514800d1f10cb84a29001a1f21d65545200353a40acaa8a40018ee86dc951480052d90ea92a290142d9205525452000c76c14ed20a40008df835da41480071b906bb482900063b21972905200347c432e120a400587e851d941480010fb0a3b2829000a3b208765052000657a10eca0a40068bc87591414800d56902b2282900063ba1b7250520014d643a84a0a4000cac7650941480a174902a12829
  | 7 => 0x7d85dd943484011df04bb2869080e2fa1f6450d2101d4f41ec8a1a42048de87d8d434840953d09b1a86908932b193725052111e6631ee498a42018ec825d760484031d904ba6c0908063b20973d81210051ec2c87b22a0008df835cb64540071b906b96c8a80121f21571d91502c43f436e2aa2a000a5d85d0f635400117f08b96c6a80122f21172d8d5001c3e42ae3b1aa05887e86dc55354001938873b286a80032710c7650d5000c3e432eaa1aa05ec77651c562540014eb0a10ec2a8002bc60021d85500047bc3ac230aa05ea778558461540030f90cbac82a800a3ba0a765055000476c14eca0aa00187c865d54154001958e5b2282a801aada07645055000c3e432eb18aa0028ee829d931540011db053b262a80061f219754c55000666396c698aa006ad681d8d31540bd0ff0abb442a80061f21975885500051ec24a7b2a8000c5d7394f65501a587eebba2caa000e37a1f735954000667906e6b2a8000ccd20dcd65500018beea39acaa000327dd073595400062ebaea7b1a8000a9d84d4f635000717908b96c6a00021fe1571d8d4002c3e42ae3b1a80018bc865d5435000753d0db1a86a00024f6177150d400143f43ecaa928005a3c865515250001878ecaa2a4a000a37a1f634c9400046fc1aebb0a80038dc835d76150007938e6a1ec2a00023de1d61185400345e424ed28a8000c5e73d9651500031790cba4a2a00030fd95749454018e1e32ae928a800493f87552515000b4790caa4a2a00030f9d9549454018e1e32eeaa0a80018bc865d54150149958edb9282a028b2b1d8725054000c5e432e918a8000c9d74d8e31500051dd053b262a00023b60a764c54000c5e432e898a8000c9c7650d3150119b18e4a1a62a00021fe15768854002c3e42aed10a80008df835da21500071b906bb442a00062f21974885400061eba4a9b2a6000a5d83953654c00917d0fba2ca980032bc83745953000656906e8b2a6000c3f751d1654c1a38beebb9aca98003271d373595300061ebaea9b226000a9d83d53644c0071b906b96c8980021fe1571d913002c3e42ae3b22600587e87dd5644c0018de41baac8980031b48375591300061e3aee8b226000c5c75dcd644c0010ff0abb2a8980022fe1176551300046fc1aecaa260018dc865d5434c00953d0db228698002576177150d300143f43ecaa926005a5c8654d524c0018b8eca9aa49800a2fa1f64509300045fc22ebb0a60048bc845d7614c009938e8a1ec2980023de1d61185300346e41ced28a6000c3e74d96514c0031b90cb9ca29800317d95739453014e2e32ae728a600395f8754e514c00b4b90ca9ca298003179d9539453000c6e432e720a6000c9f645ce414c0051dd053b282980023b60a76505300345e43ac8a0a6031a3c85591414c001938eca1a8298217631c943505301
  | 8 => 0xba0ec4988029b61741d893100537c2ae1b126200a6c855c3624c4018df0ab86c4988031b21570d893100537428e1b126200a6d851c3624c40155d08386c498802ab61070d893111d67418e1b12629dacd831c3624c53b5cd02386c49888eb960470d89310047743ca1b1262008ed87943624c4011dd0e286c4988023b61c50d893100557420a1b126200aad84143624c44759d06286c498802b360c50d89314ed73408a1b126200ae581143624c4011dd0f206c4988023b61e40d89310047743881b1262008ed87103624c4014dd0a206c4988029b61440d893111d6741881b126200acd83103624c53b5cd02206c498802b960440d893111c7743c21b1262008ed87843624c4011db0f328c498802aba12651893100556c24ca3126200acd83994624c4011df0eb28c4988023b61e64189310053742cc83126200a6d85990624c40159b07320c4988023be1d641893157567418c8312629bace86d4c624c401c9ecba98c498a6ef1a0753189314dd66432863126200e8f6450c624c401d18c8a18c49880372cc1701893100537428c03126200a6d85180624c40155d08300c498802ab610601893100674b80c031262048be849d9524c40117b093b2a49880a1f21d65549313263a38acaa9262058ee87d89524c447998e7b12a498a77391c7625493101c7b436e2a9262048ee87d89424c40d1b90cba2649881a75205744c9314ee663b6c4992629ddc471d89324c40d3ad0fb8a6498a7771dc8714c9310062fb2ee6a8a620699c8750d414c40d5390ca1a829880f271d943505314f6c639286a0a62a5e8c6250d414c40d72902a1a8298a6a3ba1b725053150c7743ec4a0a62238ec87d89414c4011df04baec09880a3b20975d813100477c12e9b0262028ec825d3604c409938e8a1ec098802ba60372d813100574c00e5b02629d8ec86dc9604c4011dd0fb12c0988031bdd76258131006363aec4b026200caf74d89604c401958e9b12c0988023ba1c625813100637ba8c4b026200c6c75189604c40195ee8312c0988032b1d062581310345f43ea8b244200c3f75d51648840155b05aa2c9108121f61776552210346f43ea6b1c4200c5f75d4d638840159b05a9ac71080e1f6177654e2102c3f42eeca1c420087d85dd9438840d1790eb22871080ea720d6450e210346e43ac6a1c4204a9c8458d438840b0fd0fbaac1108031ba0b755822100636c16eab044200c6f20dd560884018da41baac1108531b9c8755822100556422e4b044200acc835c960885015d700b92c110802b3a0f42582210055742664b0442038de83dd954484011bb07bb2a8908023be0976551210243f43ecaaa242058be87d9154484031d905b82c6908122fa137654d210045ec26eca9a42008ef825d953484070fd0fb2aa69081637a1f6354d2102c3f42eeca1a42008
  | 9 => 0x70d894100567418e1b128200acd831c362505495cd02386c4a0892b960470d89410047743ca1b1282008ed8794362504011dd0e286c4a08023b61c50d894112557420a1b128200aad84143625040159d06286c4a0802b360c50d894152573408a1b128200ae58114362504011dd0f186c4a08023b61e30d89410047743861b1282008ed870c362504014dd0a186c4a08029b61430d89411255742061b128200aad840c362505495cd02186c4a0802b960430d89411247743c21b1282008ed8784362504011db0f328c4a0802ab61265189410056741cca3128200acd8399462504011df0eb28c4a0a8aaba1b541894100717b2ea831282a2ba681d5062504011db0f318c4a08029ba16631894100536c2cc63128200aad8498c62504011df0eb18c4a0ab6aba10631894151556432863128200e8f6350c6250401d18c6a18c4a08036ad01701894100537428c03128200a6d85180625040159d06300c4a0802b360c601894100674b80c031282038de839d952504011bb073b2a4a080a1f21d655494132e3a38acaa9282058ee87d895250449958e9b12a4a0a93391c762549410247b436e2a9282a4cac76d894250549b48e3b1284a081a6da1f7150941526d3b90e2a1282068bc865d1325040d36902ba264a080e3ba1f624c9410061fb2ee8a8a82008ef825d760504051d904baec0a08023be0973d814101476412e7b028203c9c7350f60504015d301b96c0a0802ba60072d814152476436e4b0282008ee87d8960504018deebb12c0a08031b1d7625814100667b9ec4b028200ccc73d8960504011dd0e312c0a08031bdd46258141006363a8c4b028200ccf731896050401998e6312c0a081a1fa1e54596310061fba4a8b2c62068be87d51648c40187eebaa2c918802a760f54592310347a40aeca94620687c87595528c40d8e8e2b2aa51881a2f21d6450a310052ec1ca1b2a62028ee87dc9654c4011db01b92ca9880a3ba1f725913100476c06e4b2262028ee82dd9544c4011db05bb2a8988023be09765513101476412ecaa262008fb805d9544c4031f100bb2a8988121fa1f655513102c5f43ec8aa262068de86dcd544c4018becbb9aa89881a75a0773551310254f436c8a1a620399d84dc9434c491998c5b9286988021fe1570d893102c3e42ae1b126200aae84997624c40155b0932ec4988029ba1664d893100536c2cc9b12629dace86d4f624c401c9ecba9ec498a76f1a0753d89314ed6643287b126248cce7650f624c401d18c8a1ec49889e3b61c60d893100537428c1b126200a6d85183624c40155d08306c498802ab61060d893100674b80c1b126200aae84dd7624c40155b09baec498a76b360f75d893111d72c0eebb126200a6e859d3624c4014db0b3a6c49888eb3a0c74d89314ed66c18e9b126200e2f54953624c4014dd
  | 10 => 0xb24a200aad820c1649440d56d02182c928802ad604305925118d1f42e40b24a200a3d85c81649440d56d03102c928802ad60620592510355b40840b24a200ab5810816494557a6ee9b8aa928802976174358e510245f426e4b1ca2008bd84dc9639440159d05182c728802b360a3058e510356b40c60b1ca229a5e859d163944014bb0b3a2c728802b3a0a7458e5100566c14e8b1ca200c9d741d1639440153d09b92c728802a76137258e511e52f428e4b1ca200a5d851c963944011bd0fa12c7288023761f4258e5114d2f42884b1ca200a5d85109639440159d05382c728802b360a7058e510356b40ce0b1ca200ad5819c163944014bf0ab82c7288f297a147058e510052ec28e0b1ca200a9e841c1639440153b08382c728802b3a087058e5100566c10e0b1ca206ad6811c163944795ab02382c728802b3a0a4058e5100566c1480b1ca206ad68190163944015ab03202c72880237a1c4058e510046ec3880b1ca229a5e8510163944014bb0a202c728802b3a084058e5100566c1080b1ca206ad68110163944015ab02202c7288a697a172058e510052ec2e40b1ca206ad68188163944015ab03102c72881ab5a042058e510056ac0840b1ca2a9d5773dc5539440193887bb287288032710d7650e510345e43ac8a1ca203a9c83591439440d1b90eb1a8728812a72116350e510345e43ac8a14a2068dc8758d329440987ce8aa2c12880f179cd53582510043ec2eeca1aa200ace83d0b625440155d09996c4a880a1f21570d89515663a38ec8a92a2aac7471d8d525440d2ed0fb8aa4a89721fa1b705495100477c12e9b02a2028ec825d360544011df04b9ec0a880a3b20973d81510062fb9ca6b2c8200c5f75d4d639040153b09a9ac72081a3d2057654a410343e43acaa948206c7471595529040d1b90eb1a65208028f61250d95410147743ee4b2a82008ed80dc965504051dd05bb2a6a08023b60b7654d4101c3f43ecaa9a8200c3f65dd1535040d36d03ba2a6a081637a1f6354d4101d4f436c6a1a820499d83dc94350491958c5b9286a08021fe1570d894102c3e42ae1b128200ace83997625040159b0732ec4a0a92aba1b54d894100717b2ea9b1282a4ba681d5362504014dd0b31ec4a08029b61663d89415255643287b128248cae7650f6250401d18c6a1ec4a08be3b61c60d894100537428c1b128200a6d85183625040159d06306c4a0802b360c60d894100674b80c1b1282a4aad84dd7625040159d07baec4a0802b360f75d894112572c0eebb128200a6e859cf62504014db0b39ec4a0892aba1073d894152556c20e7b128200e4f5394f62504014dd0b98ec4a08029b61731d894100537c2ae1b128200a6c855c362504018df0ab86c4a08031b21570d894100537428e1b128200a6d851c3625044955d08386c4a0a92ab610
  | 11 => 0x2800c00c0440000f400000001c00c01400800400000400002803c00c03804c00000400402801400800000c00c03402401000401002800001400001c03400401400408c00001000c00000402804403400000401400406802c00000000000400c00002401c0000080200e804002c00000c01400400c07800800000400800000803400400000c02803001000400800000000400004000000401c01003c02800c02001000c00002c03001c00c00402800c02000400c05001400005001000000004402003c04800015402800001400c00000c0ac00002c00000000401408401006c00805c01401001401800c00000c02802400000403001c01000002803801800800c01400800000002002400400400000001400800c01003401c008000008008000010000004000000018014bb0b186c6aa3632d5d361985540047bc3ac230aa8008ef825c760550051d904b8ec0aa0028f61640d91536be6ab9ec330aa6008f7875846154c011df04b8ec0a980a3b20971d81530051ec24a1b2a8600a5d839436550c018f2e1286caa1b5b0fdd774595436ae2fbaee6b2a860087f855c36250c0b0f90ab86c4a18034710d75d854302c3fc3aebb0a8600c3f845d76150c0187908baec2a180317e0d75d85430062e41aebb0a8600c3f405d76150c018be60baec2a18034710d7598543006c621ee4b0a86008f7875846150c011df04b8ec0a180a3b20971d81430068e21eeab028604a3e86d9154548074bd0db1aa6a901a3da077650d520047ac0eeca1aa40287c865d5435480717d0fb2286a900ea7a0f6450d520246f43ec6a1aa404a9e84d8d43548014eb0a086c2a9002ad61010d85520056ac1821b0aa400ae582043615480d968c2ba4c2a901b3518573985520065aba6c330aa400cd573d8661548011ef0eb08c2a90130f1d154d815201e2e39aa7b02a4d4c3f75dd165508011ef0eb08c2a1292b9e09611854269e2fbaee6b2a64008f787584614c93b5cf04b08c2990063b20971d81320051ec2c86b24a2038de83dc964944011bb07b92c928802aba0a405925100556c1480b24a206ab681901649446347d0b39ac9288028f616735925100557414e6b24a200aad829cd649440193ae639ac928802a7a0f72592510054ec1ee4b24a23da3e851c9649440147b0a392c9288022fa1f32592510045ec3e64b24a231a3e850c9649440147b0a192c928802aba0a705925100556c14e0b24a206ab6819c1649440156b03382c9288028fe1570592511ed1f428e0b24a200a3d851c1649440153d06382c928802a760c705925100557410e0b24a200aad821c1649440d56d02382c9288f6ad60470592510055741460b24a200aad828c1649440d56d03182c928802ad60630592510045f43860b24a2008bd870c1649446347d0a182c9288028f61430592510055741060
  | 12 => 0x80023490e9448000d992300022003c0d080e80027ea0707d952a14a4000013d00006c00030e16f0f300d14221212029831306420900023f046180b139288b90001b280007791e9ba2ae8d7a8e0e02830302c69512e49972bc315a6d0001cd80000000400014795806e97087c0000ab800068aeb8000000730179748660a8895a82a4e18b30bafd9680079a98001199798d30c40000ae8000003240001da08a0a11218000002278000cda669e8ac18939a42818000000b32b0ad480000025f2de0001998bca8798d87b8dd2ae0000000000000b40000001482bd0a71ac10987413200017388f8001bc1428df05a325a16a6b0000858c29d98108001f92b98a906d09d0e28000e48000768f380022f12227d9a480011200008d0001ab1ce00000000013b03487485d80000000000000000000025f8949080001d114321125420d00013eb199a62210809bf98b8332691bd9c38250b6a0996d21292a9b6b0981621b2b618a2ea8bc087a16060aa39391699302c5a9e0002ba0a398e12732a8001648002df0003080450000000000000000001b115b8e819e8708000000000dc8000f410a04c1be083a032b421a90b1469db0a0ae42a01e70b989e00027a8002e50000003278888c4950aee0ed1cf80000025300007eacd2352ad8002780001380001040e79ee8d41691268000000000000001a380000005e2ed082000000000801c03800000000000403c01400000004000000400000800000009c02000000000400c0240200a803400400400004c01402004000000400001800400000c06802000000005c00004400001402c00c00000401400000000c04802c03403802402805800400400403000000c01400003802000000000c01c00003800000000000801c00400800000000c04000000800001001000000000000800000000001c00002803402402000809401803c00807800000406c03000000000802401c0140000000140000000440040000200180dc04000000000800805403001001c00804000000400801c01c00400408805004400800000c00402000401400000001800401000800000000000000400000801400001800000400800000c01001400000800000c01000400400800400000c00c00400000000003c00000c02400400c00c00007802800400c00403805800c01000401000801800000000802001c00c00400000801802805000000403001000000000401c01002c03801801800400000c00002402800400402000004005c04006800000c00802001400402000000000c00001400001c00000000c01c00c0000bc00003801406c00c0d401400001c00001c00400401800001000005000401400005000c0000080280000040040040880000000040140080300100080a400000c00c00803401c08001802806001c00401400c0240000040
  | 13 => 0x9805cb270588000000679aca2f84489a2e6a290fa8d21c500014d8ae1b60001b4a56a6f32a28527a19f0000000002f223680024e81ea962b6afb91923b19fa069ee2a91560fc1a1968a8a2678cf0248e18ff1c12eb1bd12eab18c395ca0010e04390c88b9f492d96e1858381aead6ac107b2a724800000028c0c08b8a49252a6c04ca550ee8db8000002052ecb05257852adb90524cac4ad510680000000000000006280032301d8000003140000001c00e70001cd2e100018480000027d0002e200000000020a8002e1800046a7100000029f81e18aa7500007d0000000600670819980001958000000002ce0000000000360001441609e39b70000002520002a2139ac380014d00300e0e615a8fe01b15480023409885799294f0a00b5a941f5814a080158c59d90928000fd242a9709e92131f000000131099a8709b8d3800003901ad9b0b0cba2a01f19e00b91b2199ea10793f1dc9e10c18ec99d1f68000000000000000003170aa09b25730480000030c80016a8bb8000000000002a584802e82588007a2be8d600028b80000000000000023aacb8001e480016b0000000000000001829c88001978000001fb27027200003d198aa32a527f0000f200000000022e8000912cc0fca2632499a14b896a2400028405d2f7add0c200004000007f8000c023a0000000000af2890b499c0c790d8871369ed9d191c1b20d59a905c0002cb1faa741260002488002ef0000000003021d22ad00010c00000001800015332200032b000000072838abd81d1ea8f2b0aae8175a7b9b88000000000df8110618b02d126d8000002439aba68ae28000000002271b90002479003228000000770000000000000000000000002788000000000219a0051800325161b0d04913e1f50c600000000000000000000000000022e0fa0001cb0d8918107148af8861065aef80015e29ab0683691405fa8a8f700031d2e0937054831aa61729dda77187204af49b9ab281b8d18b11a595596e9d4095279a7388501311e0902a89a78060aa9fd00000000028da89a239b330602b04fab80002c89340000000000000de20f0000d68e500000012518900000000016015a0002250000001009b380000000021400f0b3a5131500000000028828f8001a8800264a2b2ec0000fb31e0cd0ddab30840050000ceaac9ed0001af8000000000c80001720db17a9f731ab0323c19b19d8a622c2bf2589a080026e8fbb0900002f2ba8000000001e6800187ac780022c9a300019506e00009c1821f822ab2b96c9b08868002938000920681d49bbac200000025a0b61fc9470ca9ef0f1159855102ac2929a4b20f873802b078003058001e98002519b19e59491f29362c732980009610b92b00031815711f8a581c9a82ff00009a83da9b80026828611d0540e40000000001e90dc21e99b
  | 14 => 0x9ac99459281cb8000001b803b84a2f19de8001d01eb9e2ae703a23d2022a2ae99c81bf07a983299104aac0bd0a7a77a40aa986516c177a598a226e04420e9b00001c706d8000000000000000ef12907521c00000081217429c3162622801de0000000c90000eda0b2aa8002670000000003101888a688b3039861d397917ca968ebb11017283a6380010a8d29c4aea00023e8001132c029f0b192a2ca26590d1611408862b12109d713501aa1f2af8002c4131a91064a0a17fa85ae596b8be11da28aa42d59782b8a17a132708ac91080000000023f8001a721b80027b0000d4acca6016d8002ee8339d502d92b8bb071229b120000c111582a8f4934a808d821d8bda1a0003269a12fb19225eaa10342d39762150e3162a441d58ef9d81be98f2d617f1640f521fa0c2fa0002c32a1a208001c30a42392ab889800222026af10b08f1ac80329a2933a3222326a1e00359f7a640000fd9e09911ec89faf39e81aa05385aa9510114615195f0002fe039b1ba7281180025b92425d8992948001592192cd9c20c500014a13307f14f9f399aa4a99031680c0f888e124837a339fbb1f81fa2580000014cada9fe0000000000ba04e820911a8b11f0000bf08a80000000026981c04300016200003c8a82e8b109cc000284a580001c09ad8002d7a502cf9bb24d8702078002309841412d700a29a175132965a3112d0000002de8002f58000001940390002380192b798100000020b9162e01ca8000000698002249588312d3000000108a79000000183a7680006b9aa88e8000002dc00000016614a8e38000be8000d500000025e1c994b2171e3009897a631ff0422df95688810200014500032c11687184e0000100002138561f404093c18e9dab1b0002663040001f331e80029d9630001e20620222dd87e2bf9a50b22b031a13b8d91ad04f2b90da8240058001d780000018500000015f8000210270429b513c9ff80014e0e980028f00002c80000023c92f84a8c70f79cc9df00cabca0429ca0cad08829b42f08b700017888c1401d28e6a388001c5a3780014c2922411dc0000782db0fea3285980029290f00b2c080032188488c9899b580000013a0cc0370000f58932d816700023700000000015c0b28000003210000000ab17e85b80000000908124c2fc1228a193d9db80000029891a80016684b96500017da8d1fc1038e90000001ae0002420002fa92f22800010fae300006b218a1d1102228f0b178cca058af85b26aa449d30eb1768b8047b0c22d12e14997003f0001238002b4ae90ad17c23593fa6112cb001638001c29f6029a5080000009f0cb2dc80025383e9ec30727c8d71f1a7e02a06aa15aff9378001990e0808a7c13aaa083a875aa8117016800125800000231994aa78ea2018000a2a9b0ec2d20909e4203a5b0002ce8010000000
  | 15 => 0x2d90001f08309818000261c68000001efac52c918ca8e8762a6a62823a268000229ba82910595200025d17119c80000000030d95b141afc9b797a1ce8ea80db239550000289e52460000000ee138a653290c996f8c3261aaf271800241aeda3604b288918a9d31c8e8a4f2060ac2be208812acf2ab15780183e23e2470531fe82325585ea2dabb9d880017186f00804d1e60418500f801384d872004ac60322028002da2e7800006a011091f0000112a810c68001fd8000000001278691f8b0a0000003189f980000000017b2aa2f42d8a900000002979c78000001d600000003b0188002758200000023261af1a229300f97b9fa000188000245891a3b8971c4308ae62caa101df8942fe9eb0f90d0027aa4a958da089079af5063a9980000001505215d1960001bc9f231c2592450790bab200ada821f102d286b1da4bb0f8000a98cf8c8a0d993246913ad189db0eabb17726080018f80015d80000015427f8488f6af302e08332888f26f8f624980015e8000000001a69308b5059045a11a8c80000002c09c8000000e59dd2760632d280000000000000000001a14e9148001150ca2f600000000032822b8000000582f805f11c9e791125625c80021817e0498000352f99d680000000000000000006c800000191a4f95000029e96a0000558509968000de88dad425c23321e300a3018d0a30000000002b5ab380020e26ba7482b800320af01179679c90a4993a5aaf92e38a51731c1990af291a000290a7318c1d0b2c90600a92c2b207cad024d2b5028302afd2009cf066af7047135b1190318006a00023d80023997d21c8140e20000000570f98000789e18000e10b7800056a4a03f943986800153b010ce2219c631482f920af6a5486fa4326c8d10000512b73018bf80711ba918ff9ca30f3128f031904101
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x38a5c8000c1712000c00b00b402b3c247930ec802a0010ba62c9001a0a2051f0294aaf22d0a3304751901a89b201cc53b570a0d806eb0621006000632000000534000812e188160c18403002400400507a58435d76150c018c9835c060189410062a61170180624c40148d93d08765052000523653321d9314800146696940715952000519a58501c565480015259414071595200055164c501c56548001164984417518520006325c28399061480018a970a1263185200052364e841d941480014a99090476505200052364c411d941480014a990104765052000728501101d9414800148d94a0c764c52000532642311d9314800148d940c4764c52000532640311d93148001cc130440764c5200040fe61741d3654400105f985cc73d951000427660431d943440014959110c7650d10006381d9801c941440018e076600724c510004e8e5185dc520440013c3936177148110007181d865dc5204400136398d947148110004d8660651c52044001b23656107148110006c8195841c52044001b436560c7148110006d0195831c52044001b2365612514811063ec8195849452044001b436560e5148110636d01958394520440a1360985d5514811028598259755452044075a6086d955148110004d86548750520440019a38421d4148110284e865385505204418fb2354e154148110284e82617450520440019a0875d14148110285a82597450520440013619521d314811000670e0c874c520440a13c193e153148110636d0d4f854c520440a13c0985cd31481100067021d734c520440a16c0965cd3148110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x2
  | 7 => 0x94b
  | 8 => 0x94c
  | 9 => 0x94d
  | 10 => 0x94e
  | 11 => 0x138b
  | 12 => 0x138c
  | 13 => 0x138d
  | 14 => 0x138e
  | 15 => 0x98c
  | 16 => 0x98d
  | 17 => 0x98e
  | 18 => 0x150c
  | 19 => 0x150d
  | 20 => 0x150e
  | 21 => 0x9cb
  | 22 => 0x9cd
  | 23 => 0x9ce
  | 24 => 0xa0b
  | 25 => 0xa0c
  | 26 => 0xa0e
  | 27 => 0xa4b
  | 28 => 0xa4c
  | 29 => 0xa4d
  | 30 => 0xb09
  | 31 => 0xb0c
  | 32 => 0xb0d
  | 33 => 0xb0e
  | 34 => 0x1409
  | 35 => 0x140c
  | 36 => 0x140d
  | 37 => 0x140e
  | 38 => 0xb49
  | 39 => 0xb4b
  | 40 => 0xb4d
  | 41 => 0xb4e
  | 42 => 0x1449
  | 43 => 0x144b
  | 44 => 0x144d
  | 45 => 0x144e
  | 46 => 0xb89
  | 47 => 0xb8b
  | 48 => 0xb8c
  | 49 => 0xb8e
  | 50 => 0x1489
  | 51 => 0x148b
  | 52 => 0x148c
  | 53 => 0x148e
  | 54 => 0xbc9
  | 55 => 0xbcb
  | 56 => 0xbcc
  | 57 => 0xbcd
  | 58 => 0x14c9
  | 59 => 0x14cb
  | 60 => 0x14cc
  | 61 => 0x14cd
  | 62 => 0xcc9
  | 63 => 0xccd
  | 64 => 0xcce
  | 65 => 0xd09
  | 66 => 0xd0c
  | 67 => 0xd0e
  | 68 => 0xd49
  | 69 => 0xd4c
  | 70 => 0xd4d
  | 71 => 0xe89
  | 72 => 0xe8b
  | 73 => 0xe8e
  | 74 => 0xec9
  | 75 => 0xecb
  | 76 => 0xecd
  | 77 => 0x1049
  | 78 => 0x104b
  | 79 => 0x104c
  | 80 => 0x98a
  | 81 => 0x98954
  | 82 => 0x98955
  | 83 => 0x98956
  | 84 => 0xb4956
  | 85 => 0x249
  | 86 => 0xb8956
  | 87 => 0x289
  | 88 => 0x2c9
  | 89 => 0x1549
  | 90 => 0x16c9
  | 91 => 0x1849
  | 92 => 0x14a
  | 93 => 0x19c9
  | 94 => 0x134a
  | 95 => 0xb5396
  | 96 => 0x4c
  | 97 => 0xb9396
  | 98 => 0x4d
  | 99 => 0x4e
  | 100 => 0xeca
  | 101 => 0x104a
  | 102 => 0xb4996
  | 103 => 0xb8996
  | 104 => 0x209
  | 105 => 0x4b
  | 106 => 0x124b
  | 107 => 0x18c9
  | 108 => 0x1789
  | 109 => 0x1a49
  | 110 => 0x17c9
  | 111 => 0x15c9
  | 112 => 0x1709
  | 113 => 0x12cb
  | 114 => 0x3c9
  | 115 => 0x1a89
  | 116 => 0x1949
  | 117 => 0x1609
  | 118 => 0x1889
  | 119 => 0x130b
  | 120 => 0x409
  | 121 => 0x1649
  | 122 => 0x1a09
  | 123 => 0x134b
  | 124 => 0x449
  | 125 => 0x168b
  | 126 => 0x180b
  | 127 => 0x198b
  | 128 => 0x150a
  | 129 => 0xb5516
  | 130 => 0xb9516
  | 131 => 0x124c
  | 132 => 0x128c
  | 133 => 0xe89d3
  | 134 => 0x180c
  | 135 => 0x130c
  | 136 => 0x198c
  | 137 => 0x134c
  | 138 => 0x124d
  | 139 => 0x128d
  | 140 => 0xe8a13
  | 141 => 0x168d
  | 142 => 0x12cd
  | 143 => 0x198d
  | 144 => 0x134d
  | 145 => 0x124e
  | 146 => 0x128e
  | 147 => 0x168e
  | 148 => 0x12ce
  | 149 => 0x180e
  | 150 => 0x130e
  | 151 => 0x16cb
  | 152 => 0x184b
  | 153 => 0x19cb
  | 154 => 0x20c
  | 155 => 0x3ca
  | 156 => 0x154c
  | 157 => 0x170a
  | 158 => 0xe8b53
  | 159 => 0x184c
  | 160 => 0x19cc
  | 161 => 0x20d
  | 162 => 0x40a
  | 163 => 0x154d
  | 164 => 0x188a
  | 165 => 0xe8b93
  | 166 => 0x16cd
  | 167 => 0x19cd
  | 168 => 0x154e
  | 169 => 0x16ce
  | 170 => 0x1a4a
  | 171 => 0x184e
  | 172 => 0x1a8a
  | 173 => 0x18cb
  | 174 => 0x178b
  | 175 => 0x188c
  | 176 => 0x160c
  | 177 => 0x1a4b
  | 178 => 0x17cb
  | 179 => 0x1a0c
  | 180 => 0x164c
  | 181 => 0x170d
  | 182 => 0x15cd
  | 183 => 0x1a8b
  | 184 => 0x194b
  | 185 => 0x1a0d
  | 186 => 0x164d
  | 187 => 0x170e
  | 188 => 0x15ce
  | 189 => 0x188e
  | 190 => 0x160e
  | 191 => 0x28c
  | 192 => 0x1a8c
  | 193 => 0x194c
  | 194 => 0x1a4d
  | 195 => 0x17cd
  | 196 => 0x18ce
  | 197 => 0x178e
  | 198 => 0xb49895e
  | 199 => 0xb89895e
  | 200 => 0x2d551
  | 201 => 0x94994
  | 202 => 0x94995
  | 203 => 0x94996
  | 204 => 0xcb
  | 205 => 0x10b
  | 206 => 0x150994
  | 207 => 0x150995
  | 208 => 0x150996
  | 209 => 0x1a57d1
  | 210 => 0x1a9951
  | 211 => 0x1a57d3
  | 212 => 0x1a9953
  | 213 => 0x1a57d5
  | 214 => 0x1a9954
  | 215 => 0x16cb56
  | 216 => 0x184b96
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1932
  | 6 => 5274
  | 5 => 1626
  | 4 => 58
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
  | 7 => packedAt gbK7 (79212+((h/644+packedAt gbK7 (71484+(h % 644)*12) 12) % 2550)*12) 12
  | 6 => packedAt gbK6 (276006+((h/1758+packedAt gbK6 (253152+(h % 1758)*13) 13) % 6329)*14) 14
  | 5 => packedAt gbK5 (102438+((h/542+packedAt gbK5 (95934+(h % 542)*12) 12) % 2147)*12) 12
  | 4 => packedAt gbK4 (4193+((h/19+packedAt gbK4 (4060+(h % 19)*7) 7) % 70)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1fffc1e03ff83fffe0ffff807c14513e19f3f3
  | 1 => 0xe0e07e00383fc3c0ff0f03fffc6baec9164c9f
  | 2 => 0xff007fffc03ffc00fff003ff838c30f1e78f1c
  | 3 => 0x7fffffc00000fffffc0003f03f01f80fe0
  | 4 => 0x7fffffffffff0000000003ffc001fff000
  | 5 => 0xffff8000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x1210020004804422011088108000012009131
  | 1 => 0x20424a021a124284490a112a70218649124486
  | 2 => 0x5a0514ec402ca80ab2a02a55098c30b0658b18
  | 3 => 0x8086756ae820210dcccf00612f03b01b80ec0
  | 4 => 0x1010799b3737333c08084018237ec001df6000
  | 5 => 0x9c9e001c040420201080806043df7dec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeeeeeafaeaeac8feeeeeeafaeaeac8feeeeeeafaeaeac8feeeeeeafaeaeac8feeeeeeafaeaeac8feeeeeeafaeaeac8feeeeeeafaeaeac8feeeeeeafaeaeac8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37233
namespace PEqualNP.Outside.L_meta_37233
open PEqualNP.Outside.L_meta_37233.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 8 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 92 := (concat bs0_4_0 (concat bs0_4_32 bs0_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 44 := (concat bs0_5_0 bs0_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 1 := bs0_6_0
theorem alls0 : ∀ k ≤ 6, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 10 := bs1_3_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_64 : Interval s2Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 68 := (concat bs2_3_0 (concat bs2_3_32 bs2_3_64))
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
theorem bs2_4_128 : Interval s2Atlas 4 128 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 129 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 45 := (concat bs2_5_0 bs2_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 8 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 92 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_3_0 : Interval s4Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 8 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 92 := (concat bs4_4_0 (concat bs4_4_32 bs4_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 44 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 24 := bs5_3_0
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
theorem bs5_4_96 : Interval s5Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 117 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 58 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_1600 : Interval gbAtlas 5 1600 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1626 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768))))) (concat (concat (concat (concat bgb_5_800 (concat bgb_5_832 bgb_5_864)) (concat bgb_5_896 (concat bgb_5_928 bgb_5_960))) (concat (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)) (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184)))) (concat (concat (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280)) (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376))) (concat (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 bgb_5_1600))))))
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
theorem bgb_6_5248 : Interval gbAtlas 6 5248 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5274 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 (concat bgb_6_576 bgb_6_608))))) (concat (concat (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 (concat bgb_6_736 bgb_6_768))) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)))) (concat (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280)))))) (concat (concat (concat (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)))) (concat (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760))) (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920))))) (concat (concat (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080))) (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240)))) (concat (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400))) (concat (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)) (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592))))))) (concat (concat (concat (concat (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752))) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912)))) (concat (concat (concat bgb_6_2944 bgb_6_2976) (concat bgb_6_3008 (concat bgb_6_3040 bgb_6_3072))) (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232))))) (concat (concat (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392))) (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552)))) (concat (concat (concat bgb_6_3584 bgb_6_3616) (concat bgb_6_3648 (concat bgb_6_3680 bgb_6_3712))) (concat (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808)) (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904)))))) (concat (concat (concat (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064))) (concat (concat bgb_6_4096 bgb_6_4128) (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224)))) (concat (concat (concat bgb_6_4256 bgb_6_4288) (concat bgb_6_4320 (concat bgb_6_4352 bgb_6_4384))) (concat (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480)) (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576))))) (concat (concat (concat (concat bgb_6_4608 bgb_6_4640) (concat bgb_6_4672 (concat bgb_6_4704 bgb_6_4736))) (concat (concat bgb_6_4768 bgb_6_4800) (concat bgb_6_4832 (concat bgb_6_4864 bgb_6_4896)))) (concat (concat (concat bgb_6_4928 bgb_6_4960) (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056))) (concat (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152)) (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248))))))))
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
theorem bgb_7_1920 : Interval gbAtlas 7 1920 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1932 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat (concat bgb_7_96 bgb_7_128) (concat bgb_7_160 bgb_7_192))) (concat (concat (concat bgb_7_224 bgb_7_256) (concat bgb_7_288 bgb_7_320)) (concat (concat bgb_7_352 bgb_7_384) (concat bgb_7_416 bgb_7_448)))) (concat (concat (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)) (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672))) (concat (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800)) (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928))))) (concat (concat (concat (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)) (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152))) (concat (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280)) (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)))) (concat (concat (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536)) (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 bgb_7_1664))) (concat (concat (concat bgb_7_1696 bgb_7_1728) (concat bgb_7_1760 bgb_7_1792)) (concat (concat bgb_7_1824 bgb_7_1856) (concat bgb_7_1888 bgb_7_1920))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeeeafaeaeac8feeeeeeafaeaeac8feeeeeeafaeaeac8feeeeeeafaeaeac8feeeeeeafaeaeac8feeeeeeafaeaeac8feeeeeeafaeaeac8feeeeeeafaeaeac8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071594 * 2 ^ 32 + 4209699528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37233.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.or,[3,4]⟩,⟨.and,[1,5]⟩,⟨.or,[0,8]⟩,⟨.and,[7,9]⟩,⟨.or,[1,6]⟩,⟨.or,[1,5]⟩,⟨.and,[0,12]⟩,⟨.and,[2,11]⟩,⟨.or,[10,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4209699528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4209699528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37233

open PEqualNP.Outside.L_meta_37233 in
theorem PEqualNP.Outside.L_meta_37233 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4209699528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4209699528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
