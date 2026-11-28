import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37099.Model
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


end PEqualNP.Outside.L_meta_37099.Model

namespace PEqualNP.Outside.L_meta_37099
open PEqualNP.Outside.L_meta_37099.Model
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

def SBf (j : Nat) : Nat := [7, 5, 5, 7, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37099

namespace PEqualNP.Outside.L_meta_37099
open PEqualNP.Outside.L_meta_37099.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x160c080119334046a62c0c0213018800622151e1e00a1514480242ebc880040000000883b0009c02d3a145a836b9000129401f327000052015801c002c4800c2010116000062600000ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x12590f00000000000092001c801400000000ee20090204c722a1ac8403000fc4a6d3d288c89e1f14c8c8d0c12814003f290c0653f8012a5f24275269f001343a5003a58f8000b0005c340003cb47b0d115040015111146a261a51c9044031363346200568314938ec13030002e002005142571e8d4e000190b4c43c4e198f227000452e023a870b85d059c4326f11a1c8e31279d0a2910692c5e5b448151e28218003e3620810d0844d20470860d9781c551d94874241b96130993c0000000318002aa3458000010371f4002c491580021308050a304a00000730019c446c000e010380060207801203800002800006020001840c80078102848d80050d04028c830088850280000a82840208850181070081018484cf54b439f28e873e50d0e7aa921ddd4543ba28a879f5350e7ea4a1edd45439e28a87b45150e68a2a1cf141439f2a0875e53d0abaa7a16794f429ea9e859d53d0a3aa7a14f947429f286853d5490a7ea6a16bd49429e28a853c5050a7ca8214f953329eaa6653e548ca7aa9196750e32bb28c6575518ca7ca8994f551329f2a0653d540cb3a86195794f41aea9e833d539067aa520cf946419f284835f53506b8a6a0cf54c419ea90833e511076ca220cf940419f2a6633d54cc7688398cfd52319e2a4639f438c73a8718e7d5231ce2a4639f428c73a8518d794631cf20c639c418c67ea898cf151319f2a0633d540c73e8618e750c31da208639e540c73aa818e7d0831cea10635e510c7aca218f5d0431cf208639c410c7a88218e5104319f2a6433d54c86bca790d754f219faa4433c54887a86310cfd51219e2a2435f53486b8a690f50c521bda824378504867ca810cf550219ea9c813d529027ca320678c640ce18c813e50902bca6205754c40cf298813d531033aa6204754c409ea90813e511033c6220670c4409f28081ba501027ca9984f55330cea1e613f548c278a9184fd51309e2a2619d434c2dea4985b14930bba8a6174514c27ca8184f550309f2a6413d54c827ea9104f152209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209f2a6213d54c427ca9084f55210af29c215d53843a863084fd51109e2a2215f53442b8a6885bd4910b6292213f5404278a808750c410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x75c9500840294a00f2d000170000000200000000701c59700e80940028037008db2700bc0001200000004960c4c4d58662ed9181a0120000002000a88c801ca801a0640d803e440006a599a80021a00043d800380c140000e00080140040000001820004004c5d4c5150f1763145439518553d0a346154f42a518553d0b176154f428718553d0b146154f428518553d0a1d6314142a5185438cb1543946328758e544ca3461551328e181544ca946150c3287d8d529061d63942418b588548c69661d5231a3588548c696611523187997428c635651043187597420c6946150831a5986410c6976510431a5594410c6956210431a5980410c61d6315221c51503188714540c521d40c4504861d639502187d8d5290316510c6409518553102346154c40a518553103176154c408718553103146154c4085185531021f658c4408759431102946150f308d987548c21c6550d30a5185434c30d4314930c550c514c21d63953208758c548821d6395310c5950318421d63150108b5885404314540c410
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x60800810c00000050000449c300283396c628a87051c5631414290ae5b288218c147158e540860b38ec6a9481411c54314930828e2b1ca9904147158c548820abb0a818821415c8540c410
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
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (912+((h/16+packedAt s0K5 (800+(h % 16)*7) 7) % 67)*7) 7
  | 4 => packedAt s0K4 (4895+((h/55+packedAt s0K4 (4455+(h % 55)*8) 8) % 199)*9) 9
  | 3 => packedAt s0K3 (2420+((h/20+packedAt s0K3 (2280+(h % 20)*7) 7) % 96)*7) 7
  | 2 => packedAt s0K2 (505+((h/3+packedAt s0K2 (490+(h % 3)*5) 5) % 22)*5) 5
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
end PEqualNP.Outside.L_meta_37099
namespace PEqualNP.Outside.L_meta_37099
open PEqualNP.Outside.L_meta_37099.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xcc32
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | 3 => packedAt s1K3 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (6+((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s1K3 (17+((h/1+packedAt s1K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffc0fffffc0ffffffffff80ffff1ffe3f
  | 2 => 0xe07f01ffffffffff0781e07c0fffffffe493ff
  | 3 => 0xff8001fff03f03fff801ff800fff07c0f8e3cc
  | 4 => 0x1ffffc003fffffe00000ffff800ff03f0
  | 5 => 0xfffffe00000003fffffffffff0000000fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x220a100460821040188a228462884a4a092615
  | 2 => 0x491462c88514c18b0320c868853194b46490ea
  | 3 => 0x8526b55123a856d568497b2129da4706b8e34c
  | 4 => 0x1658d9a24a0e9b66b5ec12424e6ce218df03b0
  | 5 => 0x1860e1c38c30e3b8c6719c7380708420f6d800
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0faaaaaaaf0a0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37099
namespace PEqualNP.Outside.L_meta_37099
open PEqualNP.Outside.L_meta_37099.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1fffffe03ff81c1ffffe0fffff81ff007cfe7c
  | 1 => 0xe07e07ffffffffe0f81ff0780fffffff9333ff
  | 3 => 0xff8007ffc1ffffff001fff800ffe0fffe3c38f
  | 4 => 0x7fffe001fffffe000000ffff001fc03f0
  | 5 => 0xfffff80000001ffffffffffff0000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xc30c40238410a40318a60288e390990c24563c
  | 1 => 0x49108a4490a208a06a0a905124a322549130d5
  | 3 => 0x842554890d44954d04952b0249548ca962c30a
  | 4 => 0x1659e7122876de76b6c18a448e79c831fc03e0
  | 5 => 0x1861861c31871b98c719cc67006100c1dba800
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00eeaaeeaacc88cc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37099
namespace PEqualNP.Outside.L_meta_37099
open PEqualNP.Outside.L_meta_37099.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x234c3c00000149842e013995678d080e0d2103a24a00006002150446815200000007c300404800000945953601500388860a04007002c00010008020c140542203ff43fe43de43fd43dd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x54b200820a0000004846a0009a1c0000780036283e889c2672009600007a8c0060700056244ea60c2c3200646886003c5076aeb052aa0802a20442a800000038907e0000941e001006408400744a00006c626a188a0030a4669e440000164c3a2a9298348e580eac2e005e80226e7c1a0000145c12205a0008280140018b026050202001003c84381005838102842820206baa921d794643bba8a87745150f3ea8a1f5d4543ae28a87d45150ea8a2a1d794c43af29e855d53d0b3a87a15d94742baa8e859d4350abca6215754c42bba8a6574514ca7ca8194f55032af29e835d53d073a87a0db94b41b6a96835f53506b8a6a0e750d41af298835d53106bea918d755231af28c633e540c67aa818d7d5031cf2a0635d540c73aa818c755031af28863d6510c7ae8218f5104319f2a6433d54c86bca790d754f21ea18e435f53486b8a690f50c421af29e815d53d033a87205794c40aea98819d43102dca4205b54840bb2888175511027ca9984f55330bb28c6175518c27ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca6105754c20bb288417551083a863885794e10aea9c213f5444278a88857d4d10ae29a216f52442d8a488750c510
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x98010058078668092a2944ac308080ba062201c390c00a0c309418582946150f42c550d51d0a946150d42951855310a946150f41c350d52d061d6595031c5185540c71554d0431b198b410c6556510431a559031c8716540c721875905348695640c4219518553d02946150e40a5185431030d4354840c550d5110295640c710875925384295640c510c51503144344520c510
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x290098020c28238a86a96838155262d043182aed2a06390d047150d521020abb0a818a2181590520c510
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 5 => packedAt s3K5 (788+((h/14+packedAt s3K5 (704+(h % 14)*6) 6) % 63)*7) 7
  | 4 => packedAt s3K4 (2640+((h/30+packedAt s3K4 (2430+(h % 30)*7) 7) % 119)*8) 8
  | 3 => packedAt s3K3 (990+((h/8+packedAt s3K3 (950+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s3K2 (302+((h/2+packedAt s3K2 (294+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1fffffe07fffff03ffff07ffff07fffcf1f1ff
  | 1 => 0xe03f07ff81ffc3fc3e0ff8781ff87f034ece7c
  | 2 => 0xffc007fffe0fffffc00fff801fff87ff8f0f8f
  | 4 => 0x7fffff003fffff000001ffff803f00ff0
  | 5 => 0xfffff800000003ffffffffffe0000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x428400230400800046110088c50089281050b5
  | 1 => 0xc98a4a451ca5052c1a8748514b48521946c65c
  | 2 => 0x5129488286a2255810a9502129504d28b0b0a
  | 4 => 0x962ce7125143ab9aeda0c4449ce66063f00de0
  | 5 => 0x1830c61c618c33e331cce66700c44083eda000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae8e8a0a0eaeaeaeae8e8a0a0eaeaeaeae8e8a0a0eaeaeaeae8e8a0a0eaeaeaeae8e8a0a0eaeaeaeae8e8a0a0eaeaeaeae8e8a0a0eaeaeaeae8e8a0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37099
namespace PEqualNP.Outside.L_meta_37099
open PEqualNP.Outside.L_meta_37099.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x20de31dc31
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (34+((h/1+packedAt s4K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x3ffffe07fe1ff83fc3fc3fffe1fc07fd31f3cf
  | 1 => 0xc07c3ff83fff0fc3fc3fc381fe1fff02ceccfc
  | 2 => 0xff803fffc01ffffc003ffc01ffe007ff0f0f0f
  | 3 => 0x3fffffe00fffffc00001fffff803f00ff0
  | 5 => 0xffffc00000000ffffffffffe00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8510023080220004c044048ca02451281051c5
  | 1 => 0x9308445194081141441c41146209321846c45c
  | 2 => 0xa2aa8830d548ad8222aa8215540a4d30b0e0a
  | 3 => 0x2c5331242906acaeaa8220499992c063b00ba0
  | 5 => 0x306221c63198cf333333327011030083eda000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaeca0eca0eeeaeeeaeca0eca0eeeaeeeaeca0eca0eeeaeeeaeca0eca0eeeaeeeaeca0eca0eeeaeeeaeca0eca0eeeaeeeaeca0eca0eeeaeeeaeca0eca0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37099
namespace PEqualNP.Outside.L_meta_37099
open PEqualNP.Outside.L_meta_37099.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x2437c50487f0a090de14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037c83a06f10740beaa4817e53902faa7205f94a40bea9481be429037885205f94640bea8c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa9281ef52502dea4a05f14940f6292816c525037e84a06f50940bfa8a817c515037c82a06f10540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea98817e52102faa4206f90840de210817e51102faa2205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef18e61dc31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa3185f94230fd20461f9408c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930ef99261dd324c2fea2985f14530ef18a61dc314c3f480987e50130fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca6185f94830bea90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83f681907e10320fd18641f930c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5107bd0a20f6214417e51882faa3105f94220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea6905f94d20bea9a417c53482fea2905f14520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4107bd0820f6210417e51083eca2105d94420bea8841f551082eaa2105f94020fda0041f840083f460107e4c020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c43f641887e08310bfaa4217e548437ca9084f95210beaa421bd548427aa9085f15210bfa9c217e53843bca7085794e10bea9c21dd53842baa7085f14e10bfa94217e52842faa5085f14a10bea8c217e50843f461087e4c210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ec42887d48510fd18221f930443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf288217e50043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xf4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a87f75150eeea2a1df14543fa28a87745150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021fe94043bd280877d5010ff2a021de54043bf29e857d53d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85bf4390b7a87215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42f7a1285be4250afea2a15f14542bfa8285fb5050af6a0a15f14142fc28285785050afca8215f94c42bea9885bf4310b7a86215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccb7ca9994f95332beaa665bd54cca7aa9995f15332bf28e657d51ccafca1997e94332bd286657d50ccbf2a1995e54332bfaa4657e548cafaa9195f15232bea9c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa2657e544cafaa8995f15132f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d06fca1a0df54341beaa4837e53906faa720ef90e41de21c837e52906faa520ef90a41de214837e519077e8320fdd0641bf284837d50906fea6a0f7d4d41afa9a837c53507b8a6a0d714d41dfa1a83bd43506fea4a0df14941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7ee8398fd10731bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498df14931fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf29863df430c7b88618df94831f7290636e520c6faa418fb54831b6a9063de320c7b86418df94431fba0863f4410c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f719643ed32c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea94437e51887de4310fdc8621bf284437d50886fea890efd51219faa2437e54486faa890df15121de2a2433c54486fea690f7d4d21afa9a437e53486faa690df14d21ee29a435c53487dc6490fb4c921fb90a43ee21486fea090fed4121bda8
  | 2 => 0x9e35a29902a662680e47c00002831d14909492108da04f000000470ee0008ec001aa2ee0200a9df3e23c521128000361272142480000013b0800a4060d406c738001443288347a0d00000000006d0001d0c20001aa0008e8002e282c5b9f00000000000005e8d4969f3000824938000d62b01d19a48e608fa0dc000840000ef45a19c4a9ab000000f182c2d8170ea1ca21a285041f806858cad0724be218710de02c4203f1f520a26cec99c4a038cef232424514000022868882a1a71965fc958d300090c0f91b000000241123ae8f8000c8390918f682539e95c87089246000b00004a21c08087b414000a916a1d2488b400018400c000001ca2e49616d490178860a34ac760909a20ea8f4371fd46220c6897e4b63392f03006e7bc0006a00e8180b8f30008d08b01a3625f0a32603f86f44e8f619e0d5259d2096001078511000003990004e154f622300042c001b90006fcdd9fe0b27883096917c3e4a70003a07250125316014cb20001306dc0004a0667306088a01e8bc4b9d62f22b89f9a9406718208ca12c00050216474854329e41387b85fa6119a2400e02d48a2b4751be00057cf40f51645410c08f13e2a8000a82c26bcda81146c6f06d06c0082e8000883208ac311e00b66804889e4c6495251c54080782b1da00004d0f84d3f68740492a296080559dd016001160004665007f1171ee36ccd9ae2f64e8820920320c4cc90f2a25f4c713e4b07fc899490c6288000a90ba480dd1e64888e46b16b0002f43c8001da0011e00037047caba1b046654c98a42284683e8e80c0428b91552bc754e201b386674988df0ec7087d83211a0006280020e000000004821a11b8a52cc000001870008688800044a601100fa3a64a41f0001c25712a87c4805d837a5a1e489c49a641988a87e9753f2470291590006151203c000204ad800168408759d10001e8c61f634c2ec0007f0542e0c41581189740002e4422c4f91e714e4190c9911664dce69c10006349c1c0000618a6a130003906c8463b6264d08000100000c0201c000180001032024000081502c300180102003004060b00c0200203401000001d801034140181d10c0007805000120440d0200e008000e8010040701c2d00016030000041801c02000010140509402034000000600415004000200003c01000000080001003000030180009002008080000f000170600f030150040000000048040040700404000030000102008034000380004803000010080104801000020080c00000000030101a000040200001c0d0180003037038030100600008008000102301c1306c02024070440900428000140001300004038030101a010000ec02000030340000400014000140102c0e010100f0060000616019bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87d
  | 3 => 0x66030028f29482dc168bd25400001445a621ae398bc0c30002d9088004ca250b780623240c0018b23c214ab2000005cc0000d188130b29323143b0a99300000001e857000098e5a2840e85c1089a00000021800000000f48004b2318ee0004ce000d2a4d0480880004532421d2794235063cdb0bc306038d21180000009b0002c40001f9260000000021c00053000167000348001c7366970972010707a8000003d61e1180b50001600004e2e83c0001a33f400008000000190348dd0884f09a8af0246c8009ac050300f08c929e5043b93d000000fb8000008e04212f0006248898107651d071152a85747e13303a17c239962e08fccc19f32e898000e00928b8000820e29490f1b01fe9307382b27200106000000140a51
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xd51d02b46150d40cbd0c525032d43149408f997425032c52d0940cb14942502b86050940cb14a41502ba6090540cb148415036852d0140cb14a405023d6590840c754e421031d5310840c754f401035953900408fd95401031d5350040ab189401027b6550040d654d40102e862500409b98b54cc26d62d5330b518543cc29d64ccb308fd9151cc23c6454730a759031cc2cd620c730d554431cc27661d52309d587548c23f6454a308f191528c2e862502309bd89544c26c62551309dd85544c274615513097195434c2d46150d30a7593324c2da60cc930a7590314c2cd620c530b6980314c2786550130e650d404c2e862501308f596540c23e64150309798c540c27a6015030c7553300c339548c03097d95300c31d544c0309ed95300c339544c0308f99253c823d6494f208fd9151c823c645472097d8d51c825c6354720b658c40c825e63152209758c548823e6414e208f590538823e64951209bd89544827b60551208f994544823e6494d208f59253482796094d208fd91534823c6454d209dd8553482746154d20ce153204832c54881209798f540825d63d50209d987540827561d50208f596540832c6255020ce181540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530835a6094c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d584530832d54d08209b59442083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d51083706054420ce55340083ab42d00209e59440082d96310020ea1084008279658c020ce55230082e9628c020dc5463008339544c020d694d3008371514c0209bd9520082ac64480209ed9520082b864480209b98b54c426d62d53108f99053c423d6414f109b98853c426d6214f108f99352c423d64d4b10bc18121c42f161083109798f548425d63d52109798c548425d63152108f993538423d64d4e10c7952538431d5494e10d6982538431e5454e10c7551538423e6414e108f590538423e64d4a108f593528425e63d4a109758f528423e6414a108f590528425e6314a109758c5284339548c210ce551308435a534c21097d8d544425c63551109bd89544426c62551108fd91534423c6454d109bd89534426c6254d108f990534423d6414d108fd91524423c645491097d8d524425c63549109ed81524427465485109e195304425e63150109758c540426e62150109b588540423e6414c108f590530426e6214c109b588530427a6014c108fd91520423c64548108f990520423d64148109798c520425d63148109d984520423e64940108f592500425e63940109758e50042796508010da548200427965840109dd95100427b6544010
  | 1 => 0x80009840020080800000480c10000480c0000038000a35000350200038141602008040a02018a40c040f0001c4b08810000c15014060a018d80a000880c020e00000060205800062f0600c08010209414049ed8152d0e786054b43d5d0c5150f3643145438fd954310eb46150c4397d954310ed46150c43ced0d5010f5a4354043ce50d5010f5943540439e9825390a796094e42c794d4390ab46150e429798c5050a5d6314142d698c5050b596314142dad085050b3a4214142ad1854310a3f6550842ae1814210a6f6550842ba1814210a5f63544429718d5110a7a60d53329e58354cca7a60153329e58054ccb3a5494332ce55250ccb3a5454332ce55150cca7661d52329d587548ca7761551329d185544ca7b60551329e181544ca3e64141328f590504ca7661150329d584540ca7a60150329e580540ca3e6494c328f592530ca5f654c8329bd95320ca3f64544328f191510cab46150f41ae580439065e63942419758e509067a6014d419e580535075a6014d41d6580535063e65d0d41c714f435071c5350d41ad185435075453d0541c714e415063d6590c41ae580431067b60548419e181521072d5210841ad584421063f6550441a718d41106776550441b518d411067a60153319e58054cc6d96010e318fd91528c63c6454a319ed81528c6786054a318f992508c63d64942318f992544c65f63551319dd85544c63e6515131cd153314c71c548c5319b98b540c66d62d50319e983540c67960d50318f596540c71c6355031cd185540c63e64150319b988540c66d62150319e980540c6796015031c7553430c65d6510c31b6580430c72e5494831cb552520c72e5454831cb551520c74d528c831b5584320c73554d0431e5d0f410c6756510431e510c410c65f654c431a7191310c677654c431ad191310c73a5494031ce552500c76a5294031da54a500c73a5454031ce551500c76a5254031da549500c65e63d53219758f54c863e64d4f218f59353c863e6494f218f59253c867a6094f219e58253c867a60d52219e583548863e6414e218f590538867a6014e219e580538863e64942218f592508865e63942219758e508863e64951219798e544865d63951219e9825448679609512197d8d544865c63551219ed81544867860551218f994544871f54d4d21c7153534863e6494d218f592534865e6394d219e98253486796094d218fd91534863c6454d219ed8153486786054d2197994534871f5414d21c7150534874d6214d21d314e324866c654c921ced53504873854d4121d6d4f504875853d4121ced5050487385414121d6d4c504875853141219798c540865d63150219e980540867960150218f990530863d6414c219b988530867a6014c219e580530866f65484219dd9521086b46150f40ae18142d025f63547409718
  | 2 => 0x371d42f33ac523c749582b2f01f90a518cea13109105c0f00020906501c41087a04adac819e000360022224274540a41f0105f0844693ec7880898a60a024918fc7e8d82200016098b3a2a2d27a4b0d4539a6ab002412d82383095ab2929cc000349d800000009029a7ba543229e039429981a8e00a00000000f8438cca529c020006d800b7000bd0004881e0027000000aa800758608c1d800000000505f972beabc5889a0ba3e3418460262ca8543027c8dad02326a1c9bcb78aa37a12b590c709b239000c592a000000004e0020294280000005205a3e800001de72000002963b2324a18c4baf2ac1be739ba7aa16cb15a7c0e6002a057a1c00178179e0001a89626c61800742ec1180062800229cab28fe5919a0a8a2000e2cd9e4bab2468208be1dc949e84080000118c2ab80800c8930c6532ea62a283a925ea0c499247f81400000b90488b960c0832528005c000a30b0702785b87032a280011e8816664800018008004ccd0da42338c72642d8402e21a000003d99c349b0000003b9320000045878001aebd8004e000ad000482c0a386a5506e001f4000000022c850a800206c10180024800000a08e0cc0c6249fc270004d8449306401196071763cb285a17400000002c4bf9b468a90001989b98e878d62b952c62cca2ac2c993aad930571820b332af96c442c6a90be30b12bf2348100097800aba884d00014ae0002183d1f812ae6b514c0589e452d2768229cae2002a61da7e7896a7c80025a603a000098001b1ac7980069094ba25a470662eb06c232221956001aa7d990620381d30e000008424e400a0c00f03a83e828b2908689a0564f03a8eac87b2ee18aa85131a6e286aea5c448c47180800000043400018041a030000006000080402100607c00030380c2602028000006000080e050a818340d000140214010004c050c0000a24000040619068000209000382c08018080a0
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2950000c04800004460000000000000000054c000124040e0805805c400730b34f5180000000002000000600c5034c1c54354043aa0e2a1aa021d197094d4390b0b298c2a1c85465c05350d41a50e0a908420c9473584421068cb80c6aa0638518c6155031928e8b086418d917010c410c69238a8629281265cc6050940932e730482a0628529824150306a98c4a00819254c6250040a28e8a8863985907150d404c344a18c4a0261465cc6055020c50c4302a8106896310840082543a2c5180414a1d15208010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x40231000a118094c6150e42a118018c6155031c097314a6090540a808150c6250130c09731886055020
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
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (18682+((h/205+packedAt s5K5 (16632+(h % 205)*10) 10) % 740)*11) 11
  | 4 => packedAt s5K4 (16974+((h/138+packedAt s5K4 (15732+(h % 138)*9) 9) % 497)*10) 10
  | 3 => packedAt s5K3 (1273+((h/8+packedAt s5K3 (1225+(h % 8)*6) 6) % 57)*6) 6
  | 2 => packedAt s5K2 (303+((h/1+packedAt s5K2 (300+(h % 1)*3) 3) % 7)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffff81ffe1ffc1f0f87c7ff8ff01ffc41f3cf
  | 1 => 0xf01fffe07fff87e00ffff87ff0fffc007e7cfc
  | 2 => 0xffe0ffff801ffffff007ff87ff001fff8f8f0f
  | 3 => 0xffffffe007fffff80007ffffe007f00ff0
  | 4 => 0xffff0000000007fffffffff800000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa14488c51125440583c144ca8991455440b1c5
  | 1 => 0x24c21143240808a0048ac8119024c83016545c
  | 2 => 0x428a220a0c52016a10049105220292a18b0e0a
  | 3 => 0x4b14c49049035653a95004464ccb00c6e00ba0
  | 4 => 0x8c18871c719c679cce672660088c03077de000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfce8eca0fce8eca0fce8eca0fce8eca0fce8eca0fce8eca0fce8eca0fce8eca0fce8eca0fce8eca0fce8eca0fce8eca0fce8eca0fce8eca0fce8eca0fce8eca0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37099
namespace PEqualNP.Outside.L_meta_37099
open PEqualNP.Outside.L_meta_37099.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c38182140400004085000238085000000101ffd5007fe5401ff55007fc5401ffd4c05fe5301ff54c05fc53007fd0c05fe43007f50c05fc4301ffd4807fe5201ff54807fc52007fd0801fe42007f50801fc42017fcc801fe32007f4c805fc3201ffd4407fe5101ff54407fc51007fd0401fe41007f50401fc41017fcc401fe31007f4c405fc31007fc8401fe21007f48401fc2101ffd4003fe5001ff54003fc50007fd0003fe40007f50003fc40017fcc003fe30007f4c003fc30007fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24001ff5012000ff88090007ff3048003ff1824001ff4c12000ff86090007ff2048001fd9024001ff8812000fdc4090007fc2048003f61024001fe0812000ffc2090007fc104800fffb2e2009bfd971004ffccb8800efe65c4013feb2e2009bf5971003ff8cb8800efc65c400fffb262000bfd9310007fcc98801afe64c4001feb262000bf5931003ff8c98801afc64c4013ffaa62009ff9531004ffaa988027fc54c400fffb1e2000bfd8f10047fcc78800afe63c4001feb1e2000bf58f1003ff8c78800afc63c4013ffa9e2008ff94f1004ffaa788023fc53c4001ffa1e2008ff90f10007fa8788023fc43c400fffb162000bfd8b10007fcc588002fe62c4001feb162000bf58b1003ff8c588002fc62c4013ffa962009ff94b1004ffaa588027fc52c4001ffa162000ff90b10007fa8588003fc42c4011ff9962000ff8cb10007fa6588023fc32c40037f30e2009ffd471003ffca388027f651c4013fea8e2009fd5471003ff8a388003ff41c400fff20e2000ff5071003ff88388023ff31c400fff18e2000ff4c71003ff86388003ff21c400fff10e2000fd88710007fa4388003f521c400ffe10e2001bf5831000ffea188007fe50c4003fea862001ff1431000ffe8188007fe40c4003fea062001ff1031000ffe6188007fe30c4003fe9862001ff0c31000ffe4188007fe20c4003fe9062001ff0831000ffc2188007f610c4003fd0862001ff0431000fe82188017ff654400b7fb2a2000dfd9510004feca88017fe65440077f32a2005ff5951002dfaca88017fc65440077e32a2005df1951001cf8ca88003ff64440017fb222000ff99110035fcc888003fd64440017eb222000ff19110035f8c888017ff544400bff2a22005ff5511002ff8a888003ff63440017fb1a2004ff98d10015fcc688003fd63440017eb1a2004ff18d10015f8c688017ff5344009ff29a2005ff54d10027f8a688003ff4344009ff21a2000ff50d10027f88688003ff62440017fb122000ff98910005fcc488003fd62440017eb122000ff18910005f8c488017ff524400bff2922005ff5491002ff8a488003ff4244001ff2122000ff50910007f88488013ff3244001ff1922000ff4c910027f86488006ff614400bffa8a2005ff9451002feca288017fd514400bfaa8a2005ff14510007fe8288003fe4144001fea0a2000ff10510027fe6288003fe3144001fe98a2004ff0c510007fe4288003fe2144001fb10a2000ff48510007ea4288003fc21440037fb022001ffd411000ffca088007fd5044003fe2822001ffd011000ffc8088007fd4044003fe2022001ffcc11000ffc6088007fa3044003fe9822000fe4c11000ff86088007ff2044003ff1022001ff4811000ff84088007ff1044001fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fc614c0017e30a600fffd453007ffca29803ffd514c01ffe28a6000ffd0530007fc8298003fd414c001fe20a6002ffcc530017fc6298003de314c005fe98a6002ff0c530017b86298003ff214c001ff10a6000ff48530007f84298006ff604c003ffa826001ff9413000ffaa098007fc504c003ffa026001ff9013000ffa8098007fc404c003ff9826002fecc13000ffc6098007de304c003fe1826001f70c13000ff06098007fe204c003fe1026001ff8413000ff42098007fc104c019ffb2e400ebfd9720077fccb9000efe65c801dfeb2e400ebf59720067f8cb9000efc65c8019ffb264000bfd9320007fcc99001afe64c8001feb264000bf59320067f8c99001afc64c801dffaa6400eff95320077faa99003bfc54c8019ffb1e4000bfd8f2006ffcc79000afe63c8001feb1e4000bf58f20067f8c79000afc63c801dffa9e400dff94f20077faa790037fc53c8001ffa1e400dff90f20007fa8790037fc43c80037f316400effd4b20067fca59003bee52c801dfea96400efb54b20067f8a590003ff42c8019ff2164000ff50b20067f88590037ff32c8019ff1964000ff4cb20067f86590033ff61c8001ff30e4000bf98720007fac390002fd61c8019fe30e400effd4720077fca39003bfd51c801dfe28e4000ffd0720007fc8390003fd41c8001fe20e400dffcc720007fc6390003fd31c801bfe18e400cffc8720007fc4390003fd21c8019fe10e4001bf5832000ffea190007fe50c8003fea864001ff1432000ffe8190007fe40c8003fea064001ff1032000ffe6190007fe30c8003fe9864001ff0c32000ffc4190007ee20c8003fd1064001ff0832000fd84190007fe10c8003fe086400bffd952005dfeca900037f65480013fb2a400bff9952001dfcca9002ffd65480177eb2a400bff1952001df8ca9002f7c65480073e32a4000ffd9120005fec890003bf64480015fb224000ff99120035fcc890003fd64480017eb224000ff19120035f8c890003bc64480015e322400bffd512005ffca89002ffd5448017fe2a24000ffd8d20005fec69002bfe63480057f31a4000ff58d20005fac69002bfc63480057e31a400bffd4d20057fca69002ffd5348015fe29a4000ffd0d20057fc8690003fd4348015fe21a4001bfd892005ffea49002ffe5248017f7292400bff5492005fdaa49002ffc5248001ffa124000ff90920007fa8490003fc4248015ff9924000ff8c920007fa649002bfc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4000bf1852005ffea29002ffe5148017fea8a400bff14520007fe8290003fe4148001fea0a4000ff10520057fe6290003fe3148001fe98a400aff0c520007fe4290003fe2148001fe90a4000ff0852000dfec090007ff5048003ff2824001ff5412000ff8a090007ff4048003ff2
  | 2 => 0x4009ffaa7a004bfc53d000dffa1e8006efd0f40037fc87a001bfd43d0001dea1e8006ff10f40037fec5a001bfe62d00017f3168006ff58b40005fac5a001bfc62d0027ffa968013ff94b4009ffaa5a004ffc52d000dffa168006efd0b40037fc85a001bfd42d0001dea168006ff10b40097fe65a0003fe32d0001fe9968012ff0cb40037fec3a001bfe61d00017f30e8006ff58740005fac3a001bfc61d0027ffa8e8013ff9474009ffaa3a004ffc51d000dffa0e8006ff907400077c83a001bfd41d000dfe20e8006ef10740097fe63a0003fe31d0001fe98e8012ff0c740007fe43a0003fe21d0001fe90e8000ff0874000dfac1a0007ff50d0003ff2868001ff5434000ff8a1a0007fe40d0003df2068001fe9034000ff881a0007bc40d0003ff9868001ff8c34000ff861a0007fe20d0003fe1068001ff8434000ff821a0047ff65500237fb2a8011ff9954001dfccaa0047fd65500237eb2a8011ff1954001df8caa0006ff6450023ffaa28006ff9514008f7ca8a0047fd5450023deaa28006ff15140007fec6a0002ff6350021ff31a8002bf98d40007fac6a0043fc63500057e31a8011ffd4d40087fca6a0047fd5350021fe29a8006ffd0d400077e86a0043fe4350001fea1a8000ef50d40037f886a0003ff62500017fb128000ff98940007fac4a0003fc62500017e3128011ffd494008ffca4a0047fd5250023fe2928006ffd09400077e84a0003fe4250001fea128000ef50940037f884a0043ff3250001ff1928000ff4c940087f864a0003ff61500017fb0a8000ff98540007fac2a0003fc61500017e30a8011ffd454008ffca2a0047fd5150023fe28a8006ffd0540007fc82a0003be4150001fea0a8006ff105400077882a0043ff3150001ff18a8000ff4c540087f862a0003ff2150001ff10a8000ff48540007f842a0006ff6050003ffa828001ff9414000ffaa0a0007fc5050003ffa028006fed014000ffc80a0007be4050003fe2028001ef1014000ff080a0007ff3050003ff1828001ff0c14000ffc40a0007fc2050003ff0828001ff0414007ffeca9803eff654c01fff32a6003bf9953007ffaca9803efd654c01ffe32a6003bf19530007fec898002ff644c001ff3226006bf99130007fac898002fd644c001fe3226006bf1913007ffea89803ffe544c01ffeaa2600fff1513000dfec69800bff534c005ff29a6002f794d30017faa69803fdd534c005fe29a6002ffd0d30017fc869800bde434c005fea1a6000f750d30017f88698003ff624c0017fb126000ff98930007fac498003fc624c0017e312600fffd493007ffca49803ffd524c01ffe2926000ffd0930007fc8498003fd424c001fe2126002ffcc930017be649800bfe324c005fe9926000f74c930017f86498003ff614c0017fb0a6000ff98530007fac29800
  | 3 => 0xea84421cff142210e7fc8110873fc408843bff984421cff8c2210e7f86110873fe2088439fe104421cff8422103ff8211086fff65484377fb2a421bff9952101dfcca9086ffd65484377eb2a421bff1952101df8ca90803ff64484017fb224200efd91210057ec890803fe644840d7f3224200ff59121005fac890803fc644840d7e3224200ef1912100578c89086fff5448437ff2a2421bff551210dff8a890803ff63484017fb1a4200f7d8d21005bec69086bfe63484057f31a4200ff58d21005fac69086bfc63484057e31a4200f718d21015b8c69086fff5348435ff29a421bff54d210d7f8a690803ff4348435ff21a4200ff50d210d7f8869086fff5248437ff292421bff549210dff8a490803ff4248401ff2124200ff50921007f8849086bff3248401ff1924200fb8c921007fa6490803ed3248435fe192421bffd45210dffca29086ffd5148437fe28a4200ffd0521007fc8290803fd4148401fe20a421affcc521007fc6290803fd3148435fe18a4200ffc8521007ee4290803fe2148401f710a4200ffd8121005fec090867fe60484037f3024200ff581210cff8c090806fc6048437ffa824219ff941210dffaa090867fc5048433ff2024219ff101210d7fe6090867fe3048433fe1824219ff881210cff84090867fe1048433fe0824207ffd94210b5feca1085bfe65084077f3284216ff594210b5faca1081ffc65084077e3284207ffd9021005fec810803fe640840d7f3204200ff59021005fac81081ffc640840d7e3204216ffd50210b7fca81085bfd540842dfe2a04207ffd8c21005fec610857fe63084057f3184200ff58c21005fac61081ffc63084057e3184216ffd4c210affca61085bfd530842bfe2984200ffd0c210affc8610803fd430842bfe2184218bf988210b7fea410833fe520842dfea90420cff14821007fe8410833fe4208401fea10420cff108210affe6410833fe3208401fe990420cff0c8210bdfcc21085bff510840fff2884216ff5442103ff8a210803ff410840fff2084200ff5042103ff88210857ff310840fff1884200ff4c42103ff86210833ff2108401f79084207ff88421007ec4210803fd2108401f69084200fd4842103ffec010853fe60084037f3004200ff58021005fac01081ffc60084037e3004216ffd40210a7fca01085bfd5008429fe2804214ff900210a7f88010857ff3008429ff1804214ff0c0210a7fc4010833fc2008429ff0804207ff04021037fecba001aff65d000dff32e8003bf99740036fccba000e7e65d000dfeb2e8013bf59740036facba00027d65d000dfe32e8006bf1974000dfcc9a001bff54d000dff2a68006ef95340037faa9a004fbd54d000dfe2a68006ffd8f40037fcc7a000afe63d000dfeb1e8000bf58f40037f8c7a000afc63d0027ffa9e8012ff94f
  | 4 => 0x80bfe534c405fea9a6202ff14d31017fe869880bfe434c405fea1a6202ff10d31007fec498802ff624c401ff3126200ff58931007f8c498802fc624c443ffa926221ff9493110ffaa498887fc524c401ffa126200ff90931007fa8498803fc424c405ff9926202ff8c931017fa649880bfc324c4057fb0a6221ffd453110ffca298887fd514c443fe28a6200ffd0531007fc8298803fd414c401fe20a6202ffcc531017ee629880bfe314c401ef18a6202ff0c531017b8629880bf4314c401ffb026200bfd8131107fcc098806fe604c401feb026220ff1813100df8c098887ff504c441ff2826221ff54131107f8a098883fe404c441fe2026202ffcc131017fc609880bfc304c441ff1026220ff08131107fc2098883fc104c419ffb2e4218bfd97210c7fccb9080efe65c8431bf32e42039f997210c7facb90862fd65c8401beb2e42009f59721067f8cb9080efc65c8419ffb264200bfd9321007fcc99081afe64c8401feb264200bf59321067f8c99081afc64c8431ffaa64218ff953210c7faa990863fc54c8419ffb1e4200bfd8f210fffcc79080afe63c8401feb1e4200bf58f21067f8c79080afc63c8431ffa9e421fff94f210c7faa79087ffc53c8401ffa1e421fff90f21007fa879087ffc43c8431ffa96420cff94b210c7faa590833fc52c8401ffa16420cff90b21007fa8590833fc42c843fff996420cff8cb21007dc6590803fd32c8401f6996420cff0cb210c7fea390863fe51c8431fea8e4218ff14721007fe8390803fe41c8401fea0e4200ff107210fffe6390803fe31c8401fe98e421fff0c721067fec19087bfe60c84037f3064200ff58321005fac190833fc60c84037e3064218ffd43210f7fca190863fd50c843dfe286421eff903210f7f8819087fff30c843dff186421eff0c3210f7fc4190833fc20c843dff086421eff0432103ffecb1085eff658842fff32c4203bf996210bffacb1085efd658840ffe32c4203bf1962103ffec910802ff6488401ff3244206bf99221007fac910802fd648840ffe3244206bf192210bffea91085ffe548842ffeaa44217ff1522103ffec710802ff638843bff31c4202bf98e21007fac710802fd638840ffe31c4202bf18e210bffea710877fe538842ffea9c421dff14e21007fe8710877fe4388401fea1c421dff10e210ddfac51085fff528842fff2944217ff54a210bff8a510803ff4288401ff2144200ff50a21007f88510877ff3288401ff1944200ff4ca210eff8651085afe618842fffa8c4207ff946210bffaa31081ffc5188401ffa0c4207ff90621007fa831081ffc418843bff98c4207ff8c621007fa631081ffc3188401ff90c4200fbc8621007ee431081fff6088439ff3044201bf98221007fac110802fd608840ffe3044201bf182210bffea110873fe508842ff
  | 5 => 0xc54114ff862a0803ff60504017fb028228ff9814100dfcc0a0803fd6050451fe3028201bf18141157fea0a08a3fe5050455fea828228ff14141147fc80a081bfc4050453ff9828228ff8c141147f860a08a3fe2050451fe1028228ff84141147f820a081fff651040d7fb288206ff9944101dfcca2081b7e65104073f3288206ff59441135faca2081b7d65104013eb288207ff19441035f8ca2081afe641040dffaa08206ff95041037faa82081bfc541040fffb188206ff98c41015fcc62081bfd63104017eb188207ff18c41015f8c62089bff531044bff2988226ff54c4112ff8a62081bff431040dff2188225ef90c41037fa862081bfc431040dde2188207ffd8841037fcc420802fe621040dfeb108200bf5884103ff8c42089bff521044dff2908226ff54841137f8a42081bff421040dff2108200ef90841037fa842081bfc421040dde2108225ffcc841007fc6420803fd321044bfe1908227bf98441137fea22081ffe511044dfea888207ff14441037fe822081bbf411040fff2088206fd90441037fa8220803bd411040dfaa088225ffcc44103ff8622081fff601040dff3008201bf98041037fac020802fd601040ffe3008201bf18041137fea020893fe501044dfea808224ff14041037fc802081bfc401044bff9808224ff8c041127f86020893fe2010449fe1008224ff8404103ff8202081fff658c4477fb2c6223ff9963101dfccb1888ffd658c4477eb2c6207ff1963101df8cb1881fff648c4017fb246200ff99231035fcc918803fd648c4017eb246207ff19231035f8c91888fff548c447ff2a46223ff5523111ff8a91880afd638c405ffa9c6202ff94e31017faa71880bfc538c405ffa1c6200f7d0e31017fc871880bfd438c405fe21c6202f710e3103ffec518803fe628c4017f3146200ff58a31005fac51881ffc628c447ffa946223ff94a3111ffaa51888ffc528c401ffa146200ff90a31007fa8518803fc428c405ff9946202ff8ca31007bc651880bfd328c405fe1946202f70ca31015fcc31888fff518c40fff28c6223ff5463103ff8a318803ff418c40fff20c6200ff5063103ff8831880bff318c405ef98c6202fdcc63103ff8631880bf4318c40fffb046222ff9823100dfcc118803fd608c4017eb046207ff1823100df8c11888fff508c445ff2846223ff54231117f8a11888bfe408c445fe2046202ffcc231017be611880bfe308c405fe1846222ff88231117f8411888bfe108c40ffe0846221ffd953110dfeca98887fe654c4077f32a6221ff5953110dfaca98887fc654c4077e32a6200ffd9131005fec898803bf644c4015fb226200ff99131035fcc898803fd644c4017eb226200ff19131035f8c898803bc644c4015e3226221ffd513110ffca898887fd544c443fe2a26202bfd8d31017fea698
  | 6 => 0x5fe1826430ff88132187f840990c3fe104c861fe0826406ffd9741035fecba081bfe65d04077f32e8206ff5974117dfacba081bfc65d040d7e32e8206ffd5341037fca9a081bbe54d040dfeaa6822fef55341037f8a9a081bff63d040dff31e8202bf98f41037fac7a0802fd63d040dfe31e8202bf18f4117ffea7a08bbfe53d045ffea9e822eff14f41037fe87a081bbf43d040dff21e8206ff50f410077a87a081bfc43d040dffb168206ff98b41005fcc5a081bfd62d04017eb168206ff18b4117ffea5a08bffe52d045ffea96822fff14b41037fe85a081bfe42d040dfea168206ff10b41177fe65a0803fe32d0401fe996822eff0cb4117ffea3a08bffe51d045ffea8e822fff14741177fe63a08bbfc31d040dffb068206ff9834100dfcc1a081bfd60d04017eb068206ff1834100df8c1a08bfff50d045bff286822fff5434116ff8a1a081bfe40d040dfe206822effcc34116ffc61a08b7fc30d045bff106822dff0834116ffc21a08b7fc10d040fffb2c8227bfd964113ffccb2080efe659044ffeb2c8227bf5964103ff8cb2080efc65904557eb248227ffd5241037fca92089ffd549040dfe2a48207ffd8e41167fcc72080afe6390401feb1c8200bf58e4103ff8c72080afc639044fffa9c822cff94e4113ffaa7208b3fc539040dffa1c822cff90e411677c8720803fd439040dfe21c822cef10e4103ffec520803fe62904017f3148200ff58a41005fac52081ffc629044fffa948227ff94a4113ffaa52089ffc529040dffa148200ff90a410077c8520803fd429040dfe2148200ef10a41167fe6520803fe3290401fe994822cff0ca41035fcc32089fff519040fff28c8227ff5464103ff8a32081bff4190401dfa0c8206fdd0641167fe632081ffc319040fffb04822bff9824100dfcc120803fd60904017eb048207ff1824100df8c12089fff5090457ff2848227ff5424115ff8a1208affe409040dfe204822cffcc24115ffc61208affc3090457ff104822bff0824115ffc212081ffc1090455ffb2a822abfd9541157fccaa080efe6550455feb2a822abf59541157f8caa080efc6550455ffaa28206ff951411577ca8a08abfd5450455deaa28206ff15141007fec6a0802ff6350401efb1a8200b7d8d4114ffcc6a080afe6350401feb1a8229ff18d41015f8c6a0803dc63504056e31a822affd4d4114ffca6a08abfd5350453fe29a8206ffd0d410077e86a08a7fe4350401fea1a8200ef50d41037f886a0803ff62504017fb128200ff98941007fac4a0803fc62504017e312822affd4941157fca4a08abfd5250455fe2928206ffd0941007fc84a0803fd425040dfe2128229ffcc941007fc64a0803fd3250453fe192822affd4541157fca2a08abfd5150455fe28a8206ffd0541037ee82a0803fe4150401df20a8229ffc
  | 7 => 0x2101afe641080dffaa08406ff950420377ca82101bfd541086ddeaa08406ff15042067fec62101bfe63108057f3188406ff58c42005fac621033fc63108057e3188436ffd4c421affca6210dbfd531086bfe2988406ffd0c420377e862101bfe431080dfea188400ef50c42037f886210defe621086dffa90840cff948421b7faa421033fc521080dffa108406efd0842067fc842101bee421080dfea108400ef50842037da84210d7ff3210819fe190840cffd8442037fcc221002fe611080dfeb088400bf58442067f8c2210dbff511086dff2888436ff544421b7f8a2210d7ff311086bfe188840cffd8042037fcc021006fe601080dfeb008400bf58042067f8c021006fc601086dffa808434ff940421b7faa0210d3fc501080dff2008434ef90042037f8802101bbc401086bff9808434ff8c0421a7f860210d3fe2010819fe1008434ff840421a7f82021033ff658c8677fb2c6433ff9963201dfccb190cffd658c8677eb2c640cff1963201df8cb19033ff648c8017fb246400ff99232035fcc919003fd648c8017eb24640cff19232035f8c9190cfff548c867ff2a46433ff5523219ff8a91900afd638c805ffa9c6402ff94e32017faa71900bfc538c805ffa1c6402ff90e32017fa871900bfc438c8057f3146433ffd4a32067fca5190cffd528c819fe2946400ffd0a32067fc8519003fd428c819fe2146402ffcca32017be651900bef328c819fe1946402fb0ca32067fec319003fe618c8017f30c6400ff58632005fac319033fc618c867ffa8c6433ff9463219ffaa3190cffc518c805ff98c6402ff0c632017b86319033ff608c865ff3046401bf98232007fac119002fd608c819fe3046401bf1823219ffea1190cbfe508c867fea846432ff14232197fc81190cbfc408c805ff9846402ff8c232017f861190cbfe208c819fe1046432ff84232197f821190c7ff654c8637fb2a6431ff9953201dfcca990c7fd654c8637eb2a6431ff1953201df8ca99003ff644c8017fb226400ff99132035fcc899003fd644c8017eb226400ff19132035f8c8990c7ff544c863ff2a26431ff5513218ff8a89900aff634c805ffa9a6402ff94d32017faa69900bfc534c805ffa1a6402ff90d32017fa869900bfc434c8057fb126431ffd493218ffca4990c7fd524c863fe2926400ffd0932007fc8499003fd424c801fe2126402ffcc932017de649900bfe324c801ef1926402ff0c932017b8649900bec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6400bf1853218ffea2990c7fe514c863fea8a6431ff14532017fe629900bfc314c801ffb026400bfd8132187fcc099006fe604c801feb026430ff1813200df8c0990c7ff504c861ff2826431ff54132187f8a0990c3fe404c861fe2026402ffcc132017be609900bfe304c80
  | 8 => 0xfd9742035fecba101bfe65d08077f32e8406ff597421fdfacba101bfc65d080d7e32e8406ffd5342037fca9a101bfd54d080dfe2a68406ffd8f42037fcc7a100afe63d080dfeb1e8400bf58f42037f8c7a100afc63d087fffa9e843eff94f421fffaa7a10fbfc53d080dffa1e8406ff90f42037fa87a101bfc43d087fffa96843fff94b421fffaa5a10fffc52d087dff996843eff0cb42037fec3a101bfe61d08017f30e8406ff58742005fac3a101bfc61d087fffa8e843fff947421fffaa3a10fffc51d087dff98e843eff0c742037fec1a101bfe60d08037f3068406ff58342005fac1a101bfc60d08037e306843fffd43421effca1a10fffd50d087bfe2868406ff90342037f881a10fbff30d087bff186843dff0c3421effc41a10f7fc20d087bff086843dff04342067fecb210deff659086fff32c8403bf996421bffacb210defd6590819fe32c8403bf196421d5fac9210dfff549080dff2a48437ef952421bffaa9210dfbd549080dfe2a4840cffd8e421e7fcc72100afe6390801feb1c8400bf58e42067f8c72100afc639086fffa9c843cff94e421bffaa7210f3fc539080dffa1c8400efd0e421e7fc8721003fd4390801dea1c8406ff10e42035fcc5210dfff5290819ff2948437ff54a42067f8a52101bff4290801dfa148406fbd0a421e7fe6521033fc3290819ffb0c8400ff98642005fcc321003fd61908017eb0c840cff186421bffea3210dffe519086ffea8c8437ff146421e7fe63210f3fc3190819ffb04843bff9824200dfcc121003fd60908017eb04840cff1824200df8c1210dfff5090877ff2848437ff542421dff8a1210effe4090877df2048406ff102421df7881210f3ff3090877ff184843bff0c2421dffc4121033fc2090877ff084843bff042421d7fecaa10eaff6550875ff32a8403bf995421d7facaa10eafd6550875fe32a8403bf195421d7fea8a101bfe5450875feaa28406ff15142007fec6a1002ff6350873ff31a8402bf98d42007fac6a10e7fc63508057e31a843affd4d421cffca6a10ebfd5350873fe29a8406ffd0d421cffc86a1003fd435080dfe21a843affd49421d7fca4a10ebfd5250875fe2928406ffd0942037de84a1003fe4250801df2128439ffcc9421cff864a1003ff61508017fb0a8400ff98542007fac2a1003fc61508017e30a843affd45421d7fca2a10ebfd5150875fe28a8439ffcc5421cff862a1003ff60508017fb028438ff9814200dfcc0a1003fd6050871fe3028401bf181421d7fea0a10e3fe5050875fea828438ff141421c7fc80a101bfc4050873ff9828438ff8c1421c7f860a10e3fe2050871fe1028438ff841421c7f820a1033ff651080d7fb288406ff9944201dfcca2101b7e65108073f3288406ff594421b5faca2101b7d65108013eb28840cff19442035f8ca
  | 9 => 0x880000300000000480080601580100280100000000080380480080203780800080080180380500000080000000080400100a00280100400e00080000180400000000000200600280182480081d80000900180400100000280580480280080080300400000d80081600180280400200000100180000180000780900180101180000000000480a80000280680000181680100100280c80280080400700480200580500c01080100b80000380080100600b80500380180080081300801d80480c80001080380000680780900080082680000000900280700080180801980180b01e00000180100a00580280080100380280780000100000080800280280000180080280700700480001380080001200200780c00100300000080200100580080380180500000100180d00381300a00780000000180080a00400280280300300d80180000501c80180000200000000000101000080100080300080080b80180180000200500000000300100000e80280280280d00800080280e01980380001781e81bff65d0c0d7fb2e8606ff9974301dfccba181bfd65d0c877eb2e8606ff19743035f8cba180afe64d0c0dffaa68606ff95343037faa9a181bfc54d0c057eb1e8602ffd4f43017fca7a180bfd53d0c05fe29e8602ff90f430177c87a180bde43d0c05fe21e8602ef10f43037fec5a181bfe62d0c017f3168606ff58b43005fac5a181bfc62d0c87ffa968643ff94b4321ffaa5a190ffc52d0c05ff9968602ff0cb43037fec3a181bfe61d0c017f30e8606ff58743005fac3a181bfc61d0c87ffa8e8643ff9474321ffaa3a190ffc51d0c05ff98e8602ff0c743017b863a181bff60d0c0dff3068601bf98343037fac1a1802fd60d0c0dfe3068601bf1834321ffea1a190bfe50d0c87fea868642ff14343037fc81a181bfc40d0c05ff9868602ff8c343017f861a190bfe20d0c85fe1068642ff84343217f821a1907ff6550c837fb2a8641ff9954301dfccaa1907fd6550c837eb2a8641ff1954301df8caa180aff6450c83ffaa28606ff9514320ffaa8a181bfc5450c057fb1a8602ffd4d43017fca6a180bfd5350c05fe29a8602ffd0d43037be86a180bfe4350c05df21a8602ff10d430177886a180bdc4350c01ffb128600bfd8943007fcc4a1803fd6250c01fe3128600bf1894320ffea4a1907fe5250c83fea928641ff14943017fe64a180bfc3250c01ffb0a8600bfd8543007fcc2a1803fd6150c01fe30a8600bf1854320ffea2a1907fe5150c83fea8a8641ff14543017fe62a180bfc3150c01ffb028600bfd8143207fcc0a1806fe6050c01feb028640ff1814300df8c0a1907ff5050c81ff2828641ff54143207f8a0a1903fe4050c0dfe2028602ffcc143017be60a180bfe3050c05fe1828640ff88143207f840a1903fe1050c81fe0828606f
  | 10 => 0x82b455029d2d08b805ac2f3009859000000009c116458c3000000c5c05a00011b0870f1c4da15b921ce5a15f217013ce520972e714a8c9426c2df0d4c0003a12e18678d466f62830c6489200035400002ee7d129e1d88b08000000201c0004b22e4800104a00006e82100008363ff09fc0006b01930000ad20f3381876c00061f0719c04cd45aa3301f6c35615e3980234bca000000000004e3e51949a309f248500012e800072c0c788e080a6e01b78bd00662f816b9754d78000000000010e00029497f47620000000fe80000002fc9674dcc4183b4a05c7403b30608880a1043f00493ac0004c52f6a0a447c0d01ab000033254936b0000e8e43a3e68a109327a62c1994c7326120778e1c9ca36c0ec83f8000000311800000022f0e18524ffa0000000000ee00002a69df00002661098000e6600000000007a213e35c00001a819409a872c132028334955055458b2571fb84165f400000200100100200400000900800300002001780300180100200300200000080700000182680700000000880180400000280280000900100280f80880500500100280000300280000480581780100000300380080000600a80100200280200080000000180301100300600300000003580200180c00680080900080280700000700000800980100081f80b00d00200980000800000180300080680200100480080680000000080281382880680500000300700100900080200080080700280080500480780000000000280700180080000000200100200080083880f00000100000300100e00080c00300481202601600000080002f80000080d80080680000180100100000080500200380100200000100200080080180280000100c80480500a80180001600200300200000a00100080082180c80480480080000180900480600380180180700300300100080500580401100280100000000100480400082800080200680180a80480500080000d00780000d80380000c80000000000a80000180080100000080100000180180200100000000881f00582000600600100980f00080000100f00a80080180180000000100080180000a81100000880000280200080000580000581400000100000200200501880000080000080a00780000000080000f00200600200380100100280100680800580a80000400080000280580380000780000000b00180006000000200580300280200380100200000000180000000380180400281400f00600080300180700080080080380c00002200100a80100000181081500100300700080900080080180000780a00000380500180080380780180380600000600900280980780a00c80300002800300480700000500800b815000006000802805000002001801006000804000806004800001000806000000024000004801
  | 11 => 0x200018e8ca8be4093266836084450a1738f580aa7112528428fb46db2679a50df600019e80000000383369b9c00000003200000000003208270e4a39f18708c019800000020dc0002c732f8000ca216600004c024a1fc41d8fd84427c10000994c98229422000086211808291f857671f1fe80000003903fe0c0c00629f0ec147420853e2a40c901f011b37c04485840001af19c4000000190000035c4580001dd83826553a98cfc5046190fd0bc4a722552ab1ef476063b1d90bb881203a0000f9ca3250d2ed1e48bc83883e3a0384f81e93ad822444c3c23ca2070d8817d10b83d416c83e0c5881870474641996a4a2e8481f001990160002b500b8d6814400000000007212da86cc20e00000000000003042d101acd8e00000000009dc1740001d5cc6c6450089aa888200033e82e04a05e00000ae01061ac367117c5da7de2091a746ba40e32d0ba000000024300000007980240f4c4325d000009e50942f22d998689aa42315a826c17c31f14680000e034e09217105cc6a923e9f00e5620d2cba0d48ec3920001a5c1b646c21300000ae66716a00007c209014d8258f0400000018180005d620a0ca0d7e6bd12e9b2cbbc10e00000000001c43bd1238c7066e0058990a3600033900000b67eb41c148079641f2038000ee673f0ad914889420826613004a6047167167024c3150fd89606fa70c00020590840192931acc000501302000094064937f8d347803c513096645d2167000064007251219803e4ddc1370001c59046225308835c4800cb0b090443ec3b50020d8043e0250000d70c7e0001d490342f0000121922821a5dd0369d50a6c56224b00503120a90001c400002ad40493d81922731ac1a4ce2a4393b600008e076015184fc03e54e1d1800020c0002ba9ee4c103ff1ce8e90ab48130679c4c74c1a91ee8a4c1020ed0cd098cf2281019b91204986613290cb0b4e0434001a3ccc684106f05943bc1570361ed00ec0b31f81834c0425102c0634fae24a1fc875503a6e10610a545140e732b1b1491631024f09340fc56641a029439e27d31f0ac4b2635f02e06f43da5c01d712fcd926a52a80e605a443c2cd14e86ae55d08493bcbb04423a4139c0002002b918dd05e35b24f917830a0913f687f800c46537d1cd4c146920eb081c3947793a50cb47e21e22d307901a680412e053d07a0bb375831899250e20e19d03e82ff00000000002a00000dfc9a42c52db02b03f22bc2cc1d9c70000000010dc7c484f0628b689e815d2b79c340e24250000810ee44401dd93cca6461b00013882104ed1cd0ef494802339a18e800000013808fc000839000052800071b297800000072a0001fec0007c533311e00007a40000000fb84af06e0048efc3da34007308f42683d508586f24613d01fbcde63d43cd0bdc3803723560474000246075
  | 12 => 0xf30c580412fe1c28ec24323e100089442fa3469d389b60f7400803c5d67061fc1570f002691e901cce6c5700e109b4d0e5923471fb03920001ca92546e25bc3e808f43220e400b8eac8c03d52260f6042a58c1839e542a082a19b0674e162372b285e426678c25d8bd8d364240f41ec884e0ce4068e305183011531b881b22af3761e8901e4013b882e80544fa3e413900a81214290c70fcc0052dc93580fa1ba3a80384d2268203480000007ac00001fc0001b70001f8838e1860dd9e24b762ec3b50000b8200025f000008a6a60001500e12141000000091e7870001ad9028000000102c00000008d00200007183600a145ba0f1060022c53864d044050870800000005600002123be912c6105130000f8d0345240000fa4c12827307172c6047a737a045888c10b14897505967640959b5ca9805135d92b4d082103fba11c94220302c8b5477e61505e9eb8bdc7b60d7891040a04631680f4ab04a629600003d627831c95b8c783222b4193c8084301fa15cc0842b316793dc0ba73932f13610801200aa0718c302311be083006062f1e49a8821834624d95e435025f3109fd4aa606a18d8f40c1e1632c8191043c5e64268a60ac64b13b30e503e63402d216bc03a6f139414a06da09d09d8000548000345907804c38f4169614e9a438000132c00081f27199ac97a68307d95180007382c416c8f3a24900000ec00046705300005be0000ca9f2c0000003910080b90000357800037e3b42b681840005ca2fd9b900007ea0910cf06aa6b13a212a00001340000b6cb0200000000001dc15523308b40000000000770cb64340000000c960003b799ecc7a000000127400074f422865c0b47322fa88a104468a38f0c689a630b07411f00f859f029000087c00026f800000000004900f89d41132018000a760003c30df82065f7058000006400020c9e403d84f527e01788ea73b2d285e8f426580979d606464c612d209067c3701661634e8027e2a084b022e6000c9800078c3a83bb9ba4b7a5e71e6800046819b14300008c46ef00003d8e7476e34f018c9561113c594841fa36b17811681683e439780008d27201f50514eb83760d390d4c3c55900000004b230c1750c504044e03b2800000017e34c166cfe262b343000007864e11d851ca5c19239e94dcf925df29f8c781e80623e71b344e87f312380000003441ef00005065eb0000000b0447139700010620000d2000003c0001dd0000faa0000000fa08506fe1d6853877838b0db01281044aa06a8becc602e50a880000001e70001b509087d90001c48e4c0a223d9f181304811cf00340ca0000222138f066502af9da0dba09e2371270f3c3110731b283c23783f0a00ce323431350b342284880c09a84f9e123361971cfca82e0880a9c76e37b160875cb1e6ae2ff1080ff445500001dcfd
  | 13 => 0xba5b428a0660bfe5cf18504c8bc26e80001b3c64e000000099c00054b0d31bc00005ad3cb18d075445d2d800003720df0da9e100007e008799203fa074164049c82628e2078a400002fd302911ca5a62413d1b484ec00000002b809a000000000000000021e8d9829635011d0b780003ee2ca94cc8de00027400000002e424ba02050218c00002dc0000a00ba9b4400012a000178d03065734d1e704f649132e093cc0606f09e800082a0000461d042de0000c21bb40006b20000e0c00084303d8ae8cc400032015dcabc3773098eb0f4a00025c0e1861e17b00d86946ea33805c941410c1f827d9a80e8a7d617f1fd8d204543ea181c5b21e001b8b883d47b72bd8cc4b8a03111c9aacdbc36839e05a8be206033785703001a30b494c0f5200c23402a877c6f93bc0d9400000033d200800071705f88accc800034400007f826b36d16a00007491a787d402000000000001a239b4259c204224b40000da8fe845310084083e40fc0000f5d056502300800035a0001d7800025c0002268a788101b1000148c09c02c000141c4146d013a9d5406a2d12c014e02da0001991dfc4bc0002ad890800000010d1a141b477b0b617080000003b591b40006a734491c82ec5551e41c1c4660001b39230c6a6260f18564be08050940f7cdb2547419159c96e00000011e42000f22dc1430000443165115cbc4482315124cfce4f011212c0d4800018911a872c000317092cb2c69540a8da411453418696fc0000001b10d202800221ed80fcf7867513894f4f6a0002b08c604ac1732bf11cc98432e15b1a705c20000c70a003905ba03c9ebc54476d4141364c204f235a9bdca3c58e1ad189cbf40ca04a0b700023e62539bf00001ce31297a415007a06192cccd8429222890419040642898880000ea00e1f0ce0429a28798cc3a45ea3c080000003741e19b4c00070542600000000001aa1454ae87bf29a9fc00006991c71b206827ab10704f00004ca00000a474441d1390aa40681df2a79c38b9a5941dc82540000072c48740dea1720000d8418e5d10a9039468e0000d112a45280003989f4c05e0b2382000026c0001ee19f01481dd20602382d60003919d488202523ff9144dbe3590ff8268a000000000860d3e4922d713408560ff0000798c2e00000000001a424e3d680000004bc039000000014304000010784170001cdc1f434200000009125dc26080000800001560ad03de5312fc13b0e2800040885308343212e98c94fc839115c9d7cdc626f199a0b100c2f50621718fd06ad35f1580d745250a40e5d03c4c71958afce4816e1bd04544c05273cd891490608f0f891407f62a110a13e0f1e57c21793fc4468303191ee82742ab2a50608c164631310ac0a343fe1db1110a305a0281924023e3ca0000b60f6601a2788000dca1f7262116cbae00000
  | 14 => 0x6681b20280874f9433a40605185325761c080006a400000000000000002f79628bec6280001b600001a10000b000000000000a480002be42800007ea79708f06f000039c00000000002f938e1e2907e4770780fbc3548122ec8000c6283a3ad00002fe67300519e06c80002d61a0497261c284883c01c4ac0ab086cf5028b0000c143a65643fc1508000000306144014e0000000888a2c00025b000055c2870b80a945a000028200005a65861e700003a85b72052098b2231632e930c0000d6042a080e8600020d90587d640037513204642c31a8867002c5a33238d14c405d22b880000a66b735c82c40000180c199c099c4dc21099fc9a81cd17e000000076336081d4e9870000000008540000b882ac0005440001d440000003f91b0879e1d13939dd4aae46b18313440962273a10e14314289070161c0420242e603882324de27491584ee3633c2800086c131000019c00052b0b013847da0001718e940000002858000f882b22ed82f090017c1049b18fbe44e3ab06c045c2c404f80009345222a920289287b827e88f00000560000ee000025b3c40a3c1d20001b99e3503200032a02d40003c707616ac71a19f000211846a00028892d50362971a5054c6986590c39e4c00000037919dcfc606e2320680fb04740948cd4ad86141d39f480004a30a69170c866652bf86e03dc61608e12600003f30000cec00000001b123489e0a10000000d982480b4000080475928f93f837c59e2bc1e7c57a5453df00004540001a590b45de43b09c80006263931c4828c0001f018495e8cd03f72d899f80007b038e895caa2000273212400029628e19e40006291a497cc0006fd0ad01302021da00000003ca6dc0b10db87881b41979ec4ad67993dd8ce4a8600003c17b038a4dd30e80000d057d1441b540004331f91908c8c3ec0000000000000057800000042c12a065802a7cc3d19a584dc7f91161cf8eba12d3879d2c0000000158b24e3467641097a00be0cd0c400000924d723f8000ebc3c11c51dd00000001ec8000f
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf638c910016dc638c910005f6718c910005f5718c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c91018e7c654c91000cfe76d051000cfc76d05100067f65d051017e7c65d0510006bf64d0510036bc64d051000dfa70d0510005f970d0510124fe76905100067f659051013e7c6590510036be6490510006bd6490510034ff765051000cfe7650510144fd765051000cfc76505100067f65505101567c6550510006bf6450510036bc6450510005df7350510025dc7350510005fb705051000df8705051015cfe761051002d7e75105100057d75105100067f65105101367c6510510036be6410510006bd6410510254fe768c5100067f658c51011e7c658c510016de638c510006dd638c51000df8708c510014ff764c51000cfe764c510104fd764c51000cfc764c5100067f654c51010e7c654c510005bf744c510005bc744c510006df634c510016dc634c510005fb704c51000df8704c51000cfe76c851000cfc76c851002d7e75c85100057d75c85100067f65c85100c67c65c8510006ef62c8510066ec62c851000dfa70c8510005f970c85100a4fe76885100067f65885100be7c65885100a5f67688510006f6768851024df7758851024df575885100077765885102477465885100cdf57288510066f66288510066f4628851000df6708851000df4708851003ef760885100e7f23088510064ff764851000cfe76485100ccfd764851000cfc76485100067f65485100de7c6548510005bf7448510005bc7448510005df7348510025dc7348510006ef6248510006ec6248510005fb704851000df8704851000df476485100cef4764851000cf4764851023df7754851023df57548510007776548510237746548510007b77448510007b47448510007d77348510007d47348510007e77248510007e76248510066f66248510066f46248510007e46248510007e63248510007e53248510007f3704851000df6704851000df470485100cff070485100cef760485100cff230485100e4fe76085100067f65085100b67c65085100e5f67108510025f8764c110016f8764c110014f8764c1100077b654c11022f78654c11000dfb734c11000fdb734c110007db634c110016fa634c110016f8634c110027d8634c110027da534c11022fd9534c110027da434c110007d9434c110027db324c110007d9324c110007f3714c11003df8714c110007f0714c11000efb614c11000ff3614c11022ff2514c11022ff1514c110007da314c110027d8314c110007f2214c110007f1214c11000dfa76c411000efa76c411000cfa76c41100077b65c41102277865c411003dfb73c4110005f973c411000dfa71c411000ff271c411000efb61c411000ff361c411003ff251c4110227f151c411003ff221c4110007f121c4110
  | 1 => 0x8d10026dc3158d10104ff7058d10006fb7058d10034ff76d0d10004fe76d0d10004fd76d0d10034fc76d0d100067f65d0d1021e7c65d0d10036be64d0d10006bd64d0d10006df63d0d10016dc63d0d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d1020e7c6550d10036be6450d10006bd6450d10005f77150d10005f47150d100067f65d89100067c65d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910034fe74d8910004fd74d8910014fe73d8910004fd73d8910014fc73d8910006ef32d8910006ec32d891003cff70d89100e4fd70d89100e6ef20d89100e6ed20d891002d7e75989100057d75989100067f65989100067c6598910006ef62989100cdf57198910064ff759891001cfe75989100667e759891001c7e7598910004fd75989100667d75989100047d7598910064fc7598910034fe7498910004fd7498910014fe7398910004fd7398910064fc7398910064fe72989100ccfd7198910066f571989100f4fd7098910066f970989100057f755891002d7c75589100067f65589100067c6558910005bf7458910005bc7458910005df7358910025dc73589100f5f77158910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910034fc7458910006bc7458910034bc7458910004ff7358910006df7358910004df7358910014fe7358910014fc7358910006dc7358910014dc7358910006ef72589100f4ff7158910006f771589100ccff7058910006fb70589100e4fe76189100067f65189100067c6518910006ed6218910064ff751891001cfe7518910004fd7518910064fc7518910034fe7418910004fd7418910014fe7318910004fd7318910064fc7318910066ee7218910006ef3218910066ec321891003cfe7118910066f5711891003cfc711891003cff701891000cfe70189100a4fd701891000cfc7018910066ef20189100a6ed2018910034ff76d0910004fe76d0910004fd76d0910034fc76d09100067f65d09101fe7c65d0910006ef62d0910006ec62d0910064ff7690910004fe7690910004fd7690910064fc76909100067f65909101be7c6590910006bf6490910036bc6490910005f67190910005f57190910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101d67c6550910064ff7610910004fe7610910004fd7610910064fc761091002d7e75109100057d75109100067f65109101b67c6510910006bf6410910036bc6410910006ef6210910066ec6210910005f67110910005f5711091000dfa7010910005f97010910064ff768c910004fe768c910004fd768c910064fc768c9100067f658c91019e7c658c910006d
  | 2 => 0x2677810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f32d95100067c32d95102667f71d951002e7e71d95102667d71d95102667c71d95100067f31d95100067c31d95102667f70d95102667e70d95102667d70d95102667c70d95102667f40d95102667e40d95102667d40d95102667c40d95102667f30d95102667e30d95102667d30d95102667c30d95102667f20d95102667e20d95102667d20d95102667c20d95102667f10d95102667e10d95102667d10d95102667c10d9510034fe76d91100067f65d91100067c65d9110004ff75d911001cfe75d9110004fd75d911001cfc75d9110014fe73d9110004fd73d9110014fc73d9110006be43d9110006bc43d9110064fe72d9110004fd72d911003cfe71d911003cfc71d911003cff70d911000cfe70d911015cfd70d911000cfc70d911015ebf40d911015ebd40d911002d7e75991100057d75991100067f65991100067c6599110006bf6499110145f571991100057f755911002d7c75591100067f65591100067c6559110005df7359110025dc7359110005ef7259110005ec725911016df77159110004ff75591100067f75591100047f755911001cfe7559110004fd755911001cfc75591100067c755911001c7c7559110006bf7459110006be5459110006bd5459110004ff7359110006df7359110004df7359110014fe7359110014fc7359110006dc7359110014dc7359110004ff7259110006ef7259110004ef7259110064fc7259110006ec7259110004ec725911016cff7159110006f77159110144ff7059110006fb705911015cfe76191100067f65191100067c6519110036be6419110006bd6419110014fe76d8d100067f65d8d100067c65d8d10026de63d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10034fe74d8d10004fd74d8d10026dc43d8d10064fe72d8d10004fd72d8d10026dc32d8d1003cfe71d8d1000cfd71d8d1003cfc71d8d10026df31d8d1003cff70d8d1000cfe70d8d10114fd70d8d1000cfc70d8d10116df30d8d10116dd30d8d100057f7558d1002d7c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10026dc6358d10005ef7258d10005ec7258d1025df77158d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10034fc7458d10006bc7458d10034bc7458d10114ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d10064fc7258d10006ec7258d10004ec7258d1025cff7158d10006f7715
  | 3 => 0x47150f1003cff75d8b1001cfe75d8b1003e7e75d8b1001c7e75d8b10004fd75d8b1003e7d75d8b100047d75d8b1003cfc75d8b10034fe74d8b1003ebe74d8b10034be74d8b10004fd74d8b1003ebd74d8b10004bd74d8b10014fe73d8b10004fd73d8b1003cfc73d8b1003cfe71d8b1003ef671d8b1003ef970d8b100ccfd7698b1004d7e7598b100057d7598b1003eef6298b10064ff7598b1001cfe7598b100667e7598b1001c7e7598b10004fd7598b100667d7598b100047d7598b10064fc7598b10034fe7498b10004fd7498b10014fe7398b10004fd7398b10064fc7398b1000cfe7198b10066f67198b1000cfc7198b1003eee2198b1003eec2198b10066ef2098b100f6ed2098b1003eec6258b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b10034fc7458b10004ff7358b10014fe7358b10014fc7358b1003eef7258b10064ff7158b1000cfe7158b100ccfd7158b1000cfc7158b1003eee2158b1003eec2158b100ceef2058b100ceed2058b1003cff7518b1001cfe7518b10004fd7518b1003cfc7518b10034fe7418b10004fd7418b10014fe7318b10004fd7318b1003cfc7318b10064fe7218b1003eee7218b1003cfe7118b1003ef67118b1003ef97018b10034ff76d0b1003cfe76d0b10004fd76d0b1003cfc76d0b10064ff7690b1003cfe7690b10004fd7690b1003cfc7690b10036be6490b10006bd6490b1003df67190b10005f57190b10004ff7650b1003cfe7650b10004fd7650b1003cfc7650b10064ff7610b1003cfe7610b10004fd7610b1003cfc7610b1004d7e7510b100057d7510b10036be6410b10006bd6410b1003df67110b10005f57110b10064ff768cb1003cfe768cb10004fd768cb1003cfc768cb10066ee628cb10006ed628cb1003df6718cb10005f5718cb10004ff764cb1003cfe764cb10004fd764cb1003cfc764cb10006ee624cb10006ed624cb10144fd76d071016cff7650710005df7350710045dc735071025cff764c710005bf744c710005bc744c7100ccfd76c871004d7e75c87100057d75c871000df5768871003ef5768871000cf5768871003df7758871027df57588710066f6628871003fe6628871003fe5628871003ef4628871000df6708871003ff2708871003ff1708871000df470887100f4ff7648710005bf7448710005bc7448710005df7348710045dc73487100f5f77648710006f77648710275f77548710275f57548710007b77448710007b47448710007d77348710007d4734871003fe77248710066f66248710066f46248710007e63248710007e5324871000df6704871000df4704871026d7e76d951002e7e76d951001c7e76d95100067e63d95100067c63d95102677771d95102677471d95102677a30d95102677610d95102677410d9510
  | 4 => 0x520004fe7650520004fc76505200067f65505201567c6550520006bf6450520036bc6450520005df7350520055dc7350520004fe7610520004fd761052003cfc761052005d7e75105200057d75105200067f65105201367c6510520006bf6410520036bc6410520005ee7210520005ed721052000dfa7010520005f97010520004fe768c520004fd768c52003cfc768c5200067f658c52011e7c658c520006bf648c520006bc648c520006df638c520016dc638c520004ff764c520004fe764c520004fc764c5200067f654c52010e7c654c520005bf744c520005bc744c520006bf644c520006bc644c5200a4fe76c852005d7e75c85200057d75c85200067f65c85200c67c65c8520006bf64c8520006bc64c8520067e820c852000cfe76885200067f65885200be7c6588520006bf6488520006bc6488520006f7618852003ef4618852000dfa7088520005f9708852000cfc76485200067f65485200de7c6548520005bf7448520005bc7448520006bf6448520006bc6448520005df7348520055dc7348520006f76148520006f46148520005fb704852000df870485200cfe820485200f4fe76085200067f65085200b67c6508520006bf6408520006bc640852000dfa76c812000efa76c81200077b65c81202877865c8120007bb64c8120007b864c812000dfa72c812000fea72c812000efb62c812000feb62c8120067ea52c8120287e952c812003cff75d931001cfe75d9310004fd75d931003cfc75d9310014fe73d9310004fd73d931003cfc73d9310064fe72d9310004fd72d931003cfe71d931003ef671d931003ef970d9310144fd769931003ebf649931003ebc6499310034ff765931003ebc6459310004ff755931001cfe7559310004fd755931001cfc755931003ebf7459310006be5459310006bd5459310004ff7359310014fe7359310014fc7359310004ff7259310064fc7259310034ff715931000cfe7159310034fd715931000cfc715931003ebe415931003ebc4159310146bf4059310146bd405931003cff75d8f1001cfe75d8f10004fd75d8f1003cfc75d8f10034fe74d8f10004fd74d8f10104fd73d8f10064fe72d8f10004fd72d8f1003cfe71d8f1003ef671d8f1003ef970d8f1003efa10d8f10014ff7658f1003edc6358f10004ff7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f10034fc7458f1003edf7358f10004ff7258f10064fc7258f10014ff7158f1000cfe7158f10014fd7158f1000cfc7158f1003ede3158f1003edc3158f10106df3058f10106dd3058f10106fa1058f10034ff76d0f1003cfe76d0f10004fd76d0f1003cfc76d0f10036be64d0f10006bd64d0f10004ff7650f1003cfe7650f10004fd7650f1003cfc7650f10036be6450f10006bd6450f10005f77150f1003df
  | 5 => 0x57f7558d2005d7c7558d200067f6558d200067c6558d20005bf7458d20005bc7458d20006bf6458d20006bc6458d20056dc6358d20295ef7258d20005f77158d20005f47158d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d20034fc7458d20006bc7458d20034bc7458d20194ff7358d20006df7358d20294ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d2003cfc7158d20006f47158d20004f47158d20184ff7058d20006fb7058d20034ff76d0d20004fe76d0d20004fd76d0d20034fc76d0d200067f65d0d2021e7c65d0d20006bf64d0d20036bc64d0d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200067f6550d2020e7c6550d20006bf6450d20036bc6450d2000cfe76d092000cfc76d09200067f65d09201fe7c65d0920006bf64d0920036bc64d092000dfa70d0920005f970d09201a4fe76909200067f65909201be7c65909201debf6490920036bc6490920034ff765092000cfe76509201c4fd765092000cfc76509200067f65509201d67c6550920006bf6450920036bc6450920005fb705092000df870509201dcfe761092005d7e75109200057d75109200067f65109201b67c6510920006bf6410920036bc641092028cfe768c9200067f658c92019e7c658c920006bf648c920006bc648c920014ff764c92000cfe764c920184fd764c92000cfc764c9200067f654c92018e7c654c920006bf644c920006bc644c920006df634c920016dc634c920005fb704c92000df8704c9200067f65d85200067c65d8520006bf64d8520006bc64d8520004ff75d852001cfe75d8520004fd75d852001cfc75d8520034fe74d8520004fd74d8520014fe73d8520004fd73d8520014fc73d8520006f731d8520006f431d85200f6f710d852005d7e75985200057d75985200067f65985200067c6598520005be7498520005bd7498520006bf6498520006bc6498520006f761985200057f755852005d7c75585200067f65585200067c6558520005bf7458520005bc7458520006bf6458520006bc6458520005df7358520055dc73585200067f65185200067c6518520006bf6418520006bc6418520006f5611852003cff751852001cfe7518520004fd751852003cfc7518520034fe7418520004fd7418520014fe7318520004fd731852003cfc7318520006f7311852003ef4311852000cfe701852000cfc701852003ef710185200a6f51018520004fe76d0520004fd76d0520034fc76d05200067f65d052017e7c65d0520006bf64d0520036bc64d0520004fe7690520004fd769052003cfc76905200067f659052013e7c6590520006bf6490520036bc6490520004ff765
  | 6 => 0xc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006be53d9120006bd53d9120006bc53d91201debf72d91201debd72d9120006bf52d9120006be52d9120006bd52d9120006bc52d9120006bf32d9120006bc32d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bd51d9120006bc51d9120006bf31d9120006bc31d91201debf70d91201debe70d91201debd70d91201debc70d91201debf50d91201debe50d91201debd50d91201debc50d91201debf30d91201debe30d91201debd30d91201debc30d91201debf20d91201debe20d91201debc20d91201debf10d91201debe10d91201debd10d91201debc10d912005d7e75991200057d75991200067f65991200067c6599120006bf64991201c5ed72991200057f755912005d7c75591200067f65591200067c65591201edef7259120004ff75591200067f75591200047f755912001cfe7559120004fd755912001cfc75591200067c755912001c7c7559120006bf7459120004ff7359120014fe7359120014fc73591201ecff7259120006ef7259120004ff715912003cfc71591201c4ff7059120006fb70591201dcfe76191200067f65191200067c6519120036be6419120006bd64191201ddbe7619120006be76191201dcbe7619120006bf65191200073f65191200063f6519120006be6519120006bd6519120006bc65191200073c65191200063c6519120006be6319120006bc6319120007ae5219120007ad52191201a7ae20191201a7ac20191201a7b82019120036bf7519120036be7519120036bd7519120036bc7519120036bf7319120036be7319120036bd7319120036bc7319120006bf5319120006be5319120006bd5319120006bc5319120036bf7219120036bd7219120006bf5219120006be5219120006bd5219120006bc5219120006bf3219120006bc3219120036bf7119120036be7119120036bd7119120036bc7119120006bf5119120006be5119120006bd5119120006bc5119120006bf3119120006bc3119120036bf7019120036be7019120036bd7019120036bc70191201a6bf50191201a6be50191201a6bd50191201a6bc50191201a6bf30191201a6be30191201a6bd30191201a6bc30191201a6bf20191201a6be20191201a6bd20191201a6bc20191201a6bf10191201a6be10191201a6bd10191201a6bc1019120014fe76d8d200067f65d8d200067c65d8d20006bf64d8d20006bc64d8d20056de63d8d20004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20034fe74d8d20004fd74d8d20064fe72d8d2000cfd72d8d20064fc72d8d20056df32d8d2003cfe71d8d20004fd71d8d20056dc31d8d20064ff70d8d20194fd70d8d20196df30d8d20196dd30d8d20
  | 7 => 0x872003cfc7598720034fe7498720004fd7498720014fe7398720004fd739872003cfc739872000cfe7298720066f7219872003ef4219872003ef710987200e6f51098720005bf7458720005bc7458720005df735872006ddc7358720066f46158720004ff755872001cfe7558720004fd755872001cfc7558720004ff7458720006bf7458720004bf7458720034fc7458720006bc7458720034bc7458720004ff7358720006df7358720004df7358720014fe7358720014fc7358720006dc7358720014dc735872000cfc7258720066f72158720066f421587200cef71058720034ff76d0720064fe76d0720004fd76d072003cff7690720064fe7690720004fd7690720006bf6490720036bc6490720004ff7650720004fd7650720064fc7650720005df735072006ddc735072003cff7610720064fe7610720004fd76107200757e75107200057d7510720006bf6410720036bc6410720065ee7210720005ed721072003cff768c720064fe768c720004fd768c720006df638c720016dc638c720004ff764c720004fd764c720064fc764c720005bf744c720005bc744c7200ccfd76887200e4ff7648720005bf7448720005bc7448720005df734872006ddc73487202a57e76d952005e7e76d952001c7e76d95200067e63d95200067c63d952029f6f72d952029f6c72d952029f6e20d952029f6c20d952029f7820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067e43d95200067c43d952029e7f72d952005e7e72d952029e7d72d952029e7c72d95200067f32d95200067c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f31d95200067c31d952029e7f70d952029e7e70d952029e7d70d952029e7c70d952029e7f40d952029e7e40d952029e7d40d952029e7c40d952029e7f30d952029e7e30d952029e7d30d952029e7c30d952029e7f20d952029e7e20d952029e7d20d952029e7c20d952029e7f10d952029e7e10d952029e7d10d952029e7c10d9520034fe76d91200067f65d91200067c65d9120004ff75d912001cfe75d9120004fd75d912001cfc75d9120006bf54d9120006be54d9120006bd54d9120006bc54d9120014fe73d9120004fd73d9120014fc73d9120006be43d9120006bc43d9120064fe72d9120064fc72d912003cfe71d9120004fd71d9120064ff70d91201dcfd70d91201debf40d91201debd40d9120034be76d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d9120006be63d9120006bc63d9120007ae52d9120007ad52d91201dfae20d91201dfac20d91201dfb820d9120006bf75d9120006be75d9120006bd75d9120006b
  | 8 => 0x79d4350530004fe7610530004fd761053003cfc761053007d7e75105300057d7510530006bf6410530036bc6410530015de7310530005dd731053012f9e431053000dfa7010530005f9701053000dde768c530116de768c53000cde768c5302b5df758c5302b5dd758c530005df748c530005dd748c5302aede648c5302aedc648c530005dd728c530006dc628c530015de718c530017d6718c530006df618c530007d7618c530007d4618c53000dde708c530117da708c530007d9708c53000ddc708c530016df608c530017db608c530117da108c530004fe76c8530004fd76c8530064fc76c853007d7e75c85300057d75c8530015de73c8530005dd73c8530007cd32c8530006f761c8530006f461c8530004fe7688530004fd768853003cfc7688530005df7388530015dc7388530006ef6288530006ec628853000dfa7088530005f97088530004ff7648530004fe7648530004fc7648530005bf7448530005bc7448530005df7348530015dc7348530007cd3248530004fe7608530004fd760853003cfc7608530015de7308530005dd7308530006ef6208530066ec6208530006f7610853003ef4610853000dfa7008530005f97008530064ff75d932001cfe75d9320004fd75d9320064fc75d9320006be54d9320006bd54d9320014fe73d9320004fd73d9320064fc73d9320064fe72d9320066ee72d932003cfe71d9320004fd71d9320066f970d93201debe40d93201debc40d93201c4fd7699320066bf6499320066bc6499320034ff7659320066bc6459320004ff755932001cfe7559320004fd755932001cfc7559320066bf7459320004ff7359320014fe7359320014fc7359320034ff725932000cfe7259320034fd725932000cfc7259320066be4259320066bc4259320004ff715932003cfc71593201c6bf40593201c6bd4059320064ff75d8f2001cfe75d8f20004fd75d8f20064fc75d8f20034fe74d8f20004fd74d8f20184fd73d8f20064fe72d8f20066ee72d8f20066df32d8f2003cfe71d8f20004fd71d8f2006edc31d8f20066f970d8f20014ff7658f20066dc6358f20004ff7558f2001cfe7558f20004fd7558f2001cfc7558f20004ff7458f20034fc7458f20066df7358f20014ff7258f2000cfe7258f20014fd7258f2000cfc7258f20066de3258f20066dc3258f20004ff7158f2003cfc7158f20186df3058f20186dd3058f20034ff76d0f20064fe76d0f20004fd76d0f20064fc76d0f20006bf64d0f20036bc64d0f20004ff7650f20064fe7650f20004fd7650f20064fc7650f20006bf6450f20036bc6450f201c4fd76d0b20066bf64d0b20066bc64d0b201ecff7650b20066bf6450b20066bc6450b20294ff764cb20066df634cb20066dc634cb20066f7619872003cff759872001cfe7598720004fd759
  | 9 => 0xc6450d300079c6450d30005df7250d30005dc7150d30007db7050d3000dde7050d3000ddc7050d30207d87050d30016df6050d30017db6050d302079f4050d302079d4050d30207da1050d30004ff75d893001cfe75d8930004fd75d893001cfc75d8930034fe74d8930004fd74d893000cfd73d89302deee32d89302deed32d893003cfe71d8930004fd71d8930014fd70d8930296ef20d8930006ef6298930055f970989300057f755893007d7c7558930005bf7458930005bc7458930005f77158930005f4715893006dfb705893007d7e75189300057d7518930006ed6218930064ff751893001cfe75189300667e751893001c7e7518930004fd75189300667d75189300047d7518930064fc7518930034fe7418930004fd741893000cfd7318930066dd7318930066df3218930066ee32189302d6ed321893003cfe7118930004fd71189302d6dc3118930064ff7018930014fd7018930066ef201893028eed2018930004fe76d0930004fd76d0930034fc76d0930015de73d0930005dd73d0930004fe7690930004fd7690930064fc7690930006bf6490930036bc6490930015de7390930005dd73909300079d4390930004ff7650930004fe7650930004fc7650930015de7350930004fe7610930004fd7610930064fc761093007d7e75109300057d7510930006bf6410930036bc6410930015de7310930005dd73109300079d431093000dfa7010930005f9701093000ddc764c930186dc764c93000cdc764c9302cddf754c9302cddd754c930005df744c930005dd744c930015df724c930017cf724c930007cf624c930066dc624c930007cc624c930005dc714c930007db704c93000dde704c93000ddc704c930187d8704c930016df604c930017db604c930187da104c930004ff75d853001cfe75d8530004fd75d853001cfc75d8530034fe74d8530004fd74d853000cfd73d853025edd73d8530064fe72d8530004fd72d85302c6f631d85302c6f531d85302c6dc31d8530014fd70d853025ef710d8530006f76198530025f970985300057f755853007d7c7558530005bf7458530005bc7458530005ef7258530005ec7258530045fb7058530006f5611853003cff751853001cfe7518530004fd751853003cfc7518530034fe7418530004fd741853000cfd7318530064fe7218530004fd721853003ef631185302bef5311853003cff7018530014fd701853003ef9701853003ef7101853003efa1018530256f51018530004fe76d0530004fd76d0530034fc76d0530015de73d0530005dd73d05300079d43d0530004fe7690530004fd769053003cfc7690530006bf6490530036bc6490530015dc73905301679e439053000dfa7090530005f97090530004ff7650530004fe7650530004fc7650530005df7350530015dc7350530
  | 10 => 0x8540006f761985400057f755854008d7c7558540005df7358540085dc7358540005ef7258540005ec7258540006f5611854003cff751854001cfe7518540004fd751854003cfc7518540014fe7318540004fd731854003cfc7318540064fe7218540004fd721854003cff7018540034fd701854003ef71018540126f5101854000cfe7690540006f7619054003ef4619054000dfa7090540005f9709054000dbe769054015ebe769054000cbe7690540305bf7590540305bd7590540005bd7390540166be6390540166bc6390540005bd7290540006bc6290540035be7190540006bf6190540007b76190540007b4619054000dbe709054015fba7090540007b9709054000dbc7090540036bf6090540037bb609054000cfc7650540005df7350540085dc7350540006f76150540006f46150540005fb705054000df8705054016dbe7610540036be7610540035bf75105400373e75105402fdbd75105400373d75105400053d7510540005bd731054012ebe631054012ebc6310540005bd7210540006bc621054015dbe7110540037b67110540006bf611054000dbe701054000dbc7010540036bf6010540037bb6010540004fe768c540004fd768c54003cfc768c540005bf748c540035bc748c540006df638c540016dc638c5400079f438c540004ff764c540004fe764c540004fc764c540005bf744c540035bc744c540004fe76c8540004fd76c8540064fc76c854008d7e75c85400057d75c8540035be74c8540005bd74c8540004fe7688540004fd768854003cfc7688540005bf7488540035bc7488540006ef6288540006ec6288540004ff7648540004fe7648540004fc7648540005bf7448540035bc7448540005df7348540085dc7348540004fe7608540004fd760854003cfc7608540035be7408540005bd7408540006ef6208540066ec620854000dfa7008540005f97008540034fe76d9130004ff75d913001cfe75d9130004fd75d913001cfc75d9130006be54d9130006bd54d913000cff73d9130014fe73d913000cfd73d9130014fc73d91302f6bf43d91302f6bd43d9130064fe72d9130004fd72d913003cfe71d9130004fd71d9130014ff70d9130014fd70d91302eebf40d91302eebd40d9130204fd769913007d7e75991300057d7599130006bf6499130205dd7399130085f97099130034ff7659130215df7359130095fb7059130004ff755913001cfe7559130004fd755913001cfc7559130006bf7459130214ff7359130006df7359130004ff7259130064fc7259130004ff715913003cfc7159130204ff7059130006fb70591302ecfe7619130036be6419130006bd641913000ddc7650d30036dc7650d3000cdc7650d302e5df7550d302e5dd7550d30015df7450d300179f7450d300079f6450d30036de6450d30036d
  | 11 => 0x1cfc75d8d4000cfd74d8d40014fc74d8d40086de43d8d40064fe72d8d40004fd72d8d4003cfe71d8d40004fd71d8d40086dc31d8d40034fd70d8d40216df30d8d40086dc6358d4032dbe76d0d40036be76d0d40035bf75d0d40325bd75d0d40205bd73d0d40016be63d0d40016bc63d0d40005bd72d0d40005be71d0d400879c31d0d4000dbe70d0d4000dbc70d0d40036bf60d0d40037bb60d0d4000cfc7650d40006df6350d40016dc6350d400379c4350d40005fb7050d4000df87050d40037b84050d4000dbc7650d40016bc7650d4000cbc7650d4031dbf7550d4031dbd7550d40035bf7350d400379f7350d400079f6350d40016be6350d40016bc6350d400879c6350d40005bf7250d40005bc7150d40007bb7050d4000dbe7050d4000dbc7050d40207b87050d40036bf6050d40037bb6050d402079f3050d40004ff75d894001cfe75d8940004fd75d894001cfc75d8940014fe73d8940004fd73d8940014fc73d8940006ef52d8940006ec52d894003cfe71d8940004fd71d8940034fd70d89401eeef20d8940006ef62989400057f755894008d7c755894008d7e75189400057d7518940006ed6218940064ff751894001cfe75189400667e751894001c7e7518940004fd75189400667d75189400047d7518940064fc7518940066bd7418940006be5418940006bd5418940014fe7318940004fd7318940064fc7318940006bf4318940006bd4318940006ef5218940066ec521894003cfe7118940004fd7118940064ff7018940034fd70189401a6be40189401a6bc4018940066ef20189401a6ed20189401a5be76d0940036be76d09401a4be76d0940035bf75d0940315bd75d0940005bd73d0940066bc62d0940005be71d094000dbe70d094000dbc70d0940036bf60d0940037bb60d094000cfe76909401c5bd74909401debf6490940006ef6290940066ec629094000dfa7090940005f9709094000cfc7650940006ef6250940006ec6250940005fb705094000df8705094000dbc76509401c6bc765094000cbc765094030dbf755094030dbd7550940005bf7350940035bf7250940037af7250940007af6250940066bc6250940007ac6250940006ac6250940005bc7150940007bb705094000dbe705094000dbc70509401c7b87050940036bf6050940037bb6050940004fe768c940004fd768c940064fc768c940035be748c940005bd748c940006ef628c940066ec628c940004ff764c940004fe764c940004fc764c940035be744c940005bd744c940006ef624c940006ec624c940004ff75d854001cfe75d8540004fd75d854001cfc75d854016ebd74d8540006be54d8540006bd54d8540014fe73d8540004fd73d8540014fc73d8540006bf43d8540006bd43d8540064fe72d8540004fd72d8540034fd70d854016ef710d
  | 12 => 0xe7498b4000cbe7498b4000cfc7498b40036be5498b40006bd5498b40014fe7398b40004fd7398b40064fc7398b40036bf4398b40006bd4398b40066ee7298b40066bf4298b40036ef4298b40066ec4298b4003cfe7198b40004fd7198b40036bc4198b401debe4098b40036bc4098b40066ef2098b401deed2098b40004ff7558b4001cfe7558b40004fd7558b4001cfc7558b4000cfc7458b40004ff7358b40014fe7358b40014fc7358b40036ef7258b40036ef4258b40036ec4258b40004ff7158b4003cfc7158b401c6ef2058b40035bf7650b40006bf7650b401dcbf7650b4033dbf7550b4033dbd7550b400373e6550b400373d6550b40005bf7350b40037af7250b40066be6250b40005bc7150b4000dbe7050b4000dbc7050b40064ff768cb40034fe768cb40004fd768cb4019e7e658cb400067d658cb40035be748cb40005bd748cb40004ff764cb40004fd764cb40034fc764cb4018e7e654cb400067d654cb40035be744cb40005bd744cb4003cff759874001cfe7598740004fd759874003cfc759874000cfe749874000cfc7498740014fe7398740004fd739874003cfc7398740064fe7298740004fd729874003ef67198740036f7419874003ef4419874003ef7109874015ef51098740004ff755874001cfe7558740004fd755874001cfc755874000cfc7458740036bc745874000cbc7458740036be5458740006bd5458740004ff7358740006df7358740004df7358740014fe7358740014fc7358740006dc7358740014dc7358740036bf4358740006bd4358740004ff7258740064fc7258740036f77158740036f74158740036bc4158740036f44158740146f71058740035bd7690740006bd7690740335bf7590740335bd75907400373e65907400373d6590740005bd7390740166be6390740036bc6390740005bd7290740006be6290740037b67190740006bd619074000dbe709074000dbc709074003cff768c740034fe768c740004fd768c74011e7e658c7400067d658c740005bf748c740035bc748c740016dc638c7402af9f438c740004ff764c740004fd764c740034fc764c74010e7e654c7400067d654c740005bf744c740035bc744c740064ff76c8740034fe76c8740004fd76c874009d7e75c87400057d75c87400c67e65c87400067d65c8740035be74c8740005bd74c874003cff7688740034fe7688740004fd76887400be7e65887400067d6588740005bf7488740035bc7488740004ff7648740004fd7648740034fc76487400de7e65487400067d6548740005bf7448740035bc7448740005df7348740095dc734874003cff7608740034fe7608740004fd76087400b67e65087400067d6508740035be7408740005bd7408740014fe76d8d40086de63d8d40004ff75d8d4001cfe75d8d40004fd75d8d40
  | 13 => 0xc21004fd76d0821004ff76508210fcff764c8210feee624c821004fd76d0421004ff7650421005df73504210addc73504210ecff764c421005bf744c421005bc744c4210676e75c84210676d75c842103eef63c8421006ed63c842103ded71c842103eee61c8421065f57288421066f6628842103fe66288421004ff7648421005bf7448421005bc7448421005df73484210addc734842103def7648421006ef7648421004ef7648421007af7448421007ac7448421007cf7348421007cc734842103eef6348421006ed634842103def714842103eee614842103fe6514842135fe5514842103fe64148421007e54148421065f77648421006f77648421004f77648421007b77448421007b47448421007d77348421007d4734842103df7724842103fe77248421066f66248421067e66248421067e6524842135fe55248421067e64248421007e5424842100cff76580210057f75580210b57c755802103ef86058021004ff75580210067f75580210047f755802101cfe7558021004fd755802101cfc75580210067c755802101c7c7558021004ff7458021034fc7458021004ff7358021014fe7358021014fc7358021006f62158021006f521580210a6fa5058021006f950580210a6fa40580210a6fa3058021066fb2058021066f8205802103efb105802103ef810580210367f74597400367e74597400367d74597400367c74597400067f73597400067e73597400067d73597400067c73597400367f43597400367e43597400367d43597400367c43597400067f72597400067e72597400067d72597400067c72597400367f42597400367e42597400367d42597400367c42597400067f32597400067c32597400067f71597400067e71597400067d71597400067c71597400367f41597400367e41597400367d41597400367c41597400067f31597400067c31597403567f70597403567e70597403567d70597403567c70597400367f40597400367e40597400367d40597400367c40597403567f30597403567e30597403567d30597403567c30597403567f20597403567e20597403567d20597403567c20597403567f10597403567e10597403567d10597403567c1059740004ff7558f4001cfe7558f40004fd7558f4001cfc7558f4000cfe7458f40014fd7458f4000cfc7458f40036df7358f40036df4358f40036dc4358f40004ff7258f40064fc7258f40004ff7158f4003cfc7158f40206df3058f40035bf7650f4034ebf7650f40345bf7550f40345bd7550f400373e6550f400373d6550f400379f7350f400379f6350f40016be6350f40016bc6350f400379c6350f40005bf7250f40005bc7150f4000dbe7050f4000dbc7050f402079f3050f40064ff7598b4001cfe7598b40004fd7598b40064fc7598b4000cfe7498b40066b
  | 14 => 0x7b541105210fcfe768c521006bf648c521006bc648c521006df638c521016dc638c521007ce328c521014ff764c5210d4fd764c521014fc764c521005bf744c521005bc744c521006bf644c521006bc644c521006df634c521016dc634c521005ef724c521005ec724c5210d7d4314c5210dd7e75c85210057d75c8521006bf64c8521006bc64c8521006df63c85210fedc63c85210677675c85210677575c8521007b764c8521007b464c8521007d763c8521007d463c8521067e632c8521007e532c8521005f570c8521006bf6488521006bc6488521006df63885210eedc6388521007af6488521007ac648852103def7388521005ed7388521007cf6388521007cc6388521007e7618852100cfe76d8121006bf64d8121006bc64d8121006df63d8121006dc63d81210cefa60d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121034fe74d8121004fd74d8121014fe73d8121004fd73d8121014fc73d8121006fb50d81210cef850d81210cefa20d81210cefa10d81210057f75581210dd7c7558121005bf7458121005bc7458121006bf6458121006bc6458121005df73581210d5dc7358121006df6358121006dc63581210cef8605812103cff75d902101cfe75d9021004fd75d902103cfc75d9021014fe73d9021004fd73d902103cfc73d9021064fe72d902103eee72d902103cfe71d902103ef671d902100cfe70d9021004fd70d902100cfc70d9021004fd769902103ebf649902103ebc6499021034ff765902103ebc6459021004ff755902101cfe7559021004fd755902101cfc755902103cff745902103ebf7459021006be5459021006bd5459021004ff7359021014fe7359021014fc7359021064fe7259021064fc7259021066be4259021066bc425902103cfe715902103cfc715902103ebe415902103ebc4159021004ff705902100cfe705902100cfc705902103cff75d8c2101cfe75d8c21004fd75d8c2103cfc75d8c21034fe74d8c21004fd74d8c210acfd73d8c21064fe72d8c2103eee72d8c2103cfe71d8c2103ef671d8c2100cfe70d8c21004fd70d8c2100cfc70d8c21014ff7658c2103edc6358c21004ff7558c2101cfe7558c21004fd7558c2101cfc7558c21004ff7458c21034fc7458c2103cff7358c2103edf7358c210aede5358c21006dd5358c210aede4358c21064fe7258c21064fc7258c21066de3258c21066dc3258c2103cfe7158c2103cfc7158c2103ede3158c2103edc3158c21004ff7058c2100cfe7058c2100cfc7058c210aedf3058c21034ff76d0c2103cfe76d0c21004fd76d0c2103cfc76d0c21036be64d0c21006bd64d0c21004ff7650c2103cfe7650c21004fd7650c2103cfc7650c21036be6450c21006bd6450c21016de6350c21006dd6350c21005f77150c2103df4715
  | 15 => 0xd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006de40d8d21006dc40d8d21006de20d8d21006dc20d8d21006de10d8d21006dc10d8d21005bf7458d21005bc7458d21006bf6458d21006bc6458d210d6dc6358d21004ff7558d2101cfe7558d21004fd7558d2101cfc7558d21004ff7458d21006bf7458d21004bf7458d21034fc7458d21006bc7458d21034bc7458d210d4ff7358d21006df7358d210ecff7258d21006ef7258d210fcff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21005de7618d210d6de7618d21004de7618d210d75e7518d210d75d7518d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d210079f6418d210069f6418d21006de6418d21006dd6418d21006dc6418d210079c6418d210069c6418d210d7cd7218d21006de6018d21006dc6018d21034ff76d0d21004fe76d0d21004fd76d0d21034fc76d0d21006bf64d0d21036bc64d0d21006df63d0d21016dc63d0d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006bf6450d21036bc6450d21006df6350d21016dc6350d21004fe76d092103cfc76d0921006bf64d0921036bc64d0921006df63d09211f6dc63d0921005f671d0921005f571d0921004fe7690921006bf6490921036bc6490921006df63909211e6dc6390921034fc7650921006bf6450921036bc6450921006df63509211cedc6350921005f77150921005f47150921004fe76109210dd7e75109210057d7510921006bf6410921036bc6410921006df63109211aedc6310921007ad42109210ecfe768c921006bf648c921006bc648c921006df638c921016dc638c921005ee768c9210eeee768c921007af648c921007ac648c9210d5ed738c921007cf638c921016ee638c921016ec638c9210d7cc638c921016cc638c92103dee718c921066ef618c9210d7cc318c921014fc764c921006bf644c921006bc644c921006df634c921016dc634c921005f7714c921005f4714c9210d5ec764c921016ec764c921014ec764c921007af644c921007ac644c9210d5ef734c921007cf734c921007cf634c921016ee634c921016ec634c9210d7cc634c921007e7714c92103dec714c921007e4714c9210d7cf304c921004fe76d0521064fc76d0521006bf64d0521036bc64d0521006df63d0521176dc63d0521005ee72d0521005ed72d0521004fe7690521006bf6490521036bc6490521006df6390521166dc6390521034ff7650521004fd7650521034fc7650521006bf6450521036bc6450521005df73505210d5dc7350521006df635052114edc6350521005ef7250521005ec7250521004fe76105210dd7e75105210057d7510521006bf6410521036bc6410521006df631052112edc6310521
  | 16 => 0x9121006bf50d9121006be50d9121006bd50d9121006bc50d9121006bf30d9121006be30d9121006bc30d9121006be20d9121006bc20d9121006be10d9121006bc10d9121006bf64991210d5de7399121005dd7399121005df73591210d5dc7359121004ff755912101cfe7559121004fd755912101cfc7559121006bf7459121004ff7359121006df7359121004df7359121014fe7359121014fc7359121006dc7359121014dc7359121004ff7259121006ef7259121004ff7159121006f77159121004ff705912100cfe705912100cfc7059121004fe76191210dd7e75191210057d7519121036be6419121006bd6419121005be7619121006be7619121004be76191210073e75191210073d7519121006bf6519121006be6519121006bd6519121006bc6519121006be6319121006bc6319121006be6019121006bc6019121036bf7519121036be75191210363e7519121036bd75191210363d7519121036bc7519121036bf7319121036be7319121036bd7319121036bc7319121006bf5319121006be5319121006bd5319121006bc5319121036bf7219121036bd7219121006bf5219121006be5219121006bd5219121006bc5219121006bf3219121006bc3219121036bf7119121036bd7119121006bf5119121006be5119121006bd5119121006bc5119121006bf3119121006bc3119121006bd2119121036bf7019121036be7019121036bd7019121036bc7019121006bf5019121006be5019121006bd5019121006bc5019121006bf3019121006be3019121006bc3019121006be2019121006bc2019121006be1019121006bc1019121014fe76d8d21006bf64d8d21006bc64d8d210d6de63d8d21004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21034fe74d8d21004fd74d8d21006df53d8d210d6de53d8d21006dd53d8d210d6dc53d8d210d6de43d8d210d6dc43d8d210d4fd72d8d210d6df32d8d210d4fd71d8d210d6df31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d210d6df30d8d21006de30d8d210d6dc30d8d210d5de76d8d21014de76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d210079f64d8d210069f64d8d21006de64d8d21006dd64d8d21006dc64d8d210079c64d8d210069c64d8d21007cf72d8d21006de60d8d21006dc60d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d21006df72d8d210d6de72d8d21006dd72d8d21006df52d8d21006de52d8d21006dd52d8d21006dc52d8d21006df71d8d210d6de71d8d21006dd71d8d21006df51d8d21006de51d8d21006dd51d8d21006dc51d8d21006df70d8d21006de70d8d21006d
  | 17 => 0x3ebe415922103ebc4159221004ff705922100cfe705922100cfc7059221006be4059221006bc405922103cff75d8e2101cfe75d8e21004fd75d8e2103cfc75d8e21034fe74d8e21004fd74d8e210ecfd73d8e2103eed72d8e210eedc32d8e2103ef671d8e2100cfe70d8e21004fd70d8e2100cfc70d8e210eedf30d8e21014ff7658e2103edc6358e21004ff7558e2101cfe7558e21004fd7558e2101cfc7558e21004ff7458e21034fc7458e2103edf7358e210eedf3258e2103ede3158e2103edc3158e21004ff7058e2100cfe7058e2100cfc7058e21034ff76d0e2103cfe76d0e21004fd76d0e2103cfc76d0e21036be64d0e21006bd64d0e21004ff7650e2103cfe7650e21004fd7650e2103cfc7650e21036be6450e21006bd6450e21036be64d0a21006bd64d0a2103df671d0a21005f571d0a21006bf6490a21036bc6490a21034ff7650a21036be6450a21006bd6450a21005f77150a2103df47150a210bd7e7510a210057d7510a21006bf6410a21036bc6410a210d4fd768ca21006df638ca21016dc638ca21014ff764ca2103cfc764ca21016de634ca21006dd634ca21005f7714ca2103df4714ca21005df73506210eddc735062103fb441506210acff764c621005bf744c621005bc744c62103fd4314c6210bd7e75c86210057d75c862103ded76c8621006ed76c86213676e75c86210076d75c862103eef63c8621006ed63c862103fe651c8621367e551c8621005f576c8621066f576c86210677675c86210677575c8621067e652c8621367e552c8621005f570c862100cff765822103ef86058221004ff755822101cfe7558221004fd755822101cfc7558221004ff7458221034fc7458221004ff7358221014fe7358221014fc73582210e6fa30582210e6fa205822103efb105822103ef81058221034fe76d9121004ff75d912101cfe75d9121004fd75d912101cfc75d9121006bf54d9121006be54d9121006bd54d9121006bc54d9121014fe73d9121004fd73d9121014fc73d9121006be43d9121006bc43d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121006bc40d9121034be76d9121006bf65d9121006be65d9121006bd65d9121006bc65d9121006be63d9121006bc63d9121006be60d9121006bc60d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d9121006be53d9121006bd53d9121006bc53d9121006bf72d9121006bd72d9121006bf52d9121006be52d9121006bd52d9121006bc52d9121006bf32d9121006bc32d9121006bf71d9121006bd71d9121006bf51d9121006be51d9121006bd51d9121006bc51d9121006bf31d9121006bc31d9121006bf70d9121006be70d9121006bd70d9121006bc70d
  | 18 => 0xe75d8f21004fd75d8f210667d75d8f210047d75d8f21064fc75d8f21034fe74d8f21066be74d8f21034be74d8f21004fd74d8f21066bd74d8f21004bd74d8f210fcfd73d8f21066ee72d8f21066f571d8f210fedc31d8f2100cfe70d8f21004fd70d8f2100cfc70d8f21014ff7658f210067e6558f210067d6558f21066dc6358f21004ff7558f2101cfe7558f21004fd7558f2101cfc7558f21004ff7458f21034fc7458f21066df7358f210fedc4358f21066de3258f21066dc3258f210fedf3158f21004ff7058f2100cfe7058f2100cfc7058f210fedf3058f21034ff76d0f21064fe76d0f21004fd76d0f21064fc76d0f2121e7e65d0f210067d65d0f21006bf64d0f21036bc64d0f21016de63d0f21006dd63d0f21004ff7650f21064fe7650f21004fd7650f21064fc7650f2120e7e6550f210067d6550f21006bf6450f21036bc6450f21005f77150f21005f47150f211fe7e65d0b210067d65d0b211d67e6550b210067d6550b21067ac4250b21065ed768cb21066ed768cb21014ed768cb210676e658cb210676d658cb21016ee638cb21067ce638cb21067cd638cb21066ec638cb2103dee718cb21067e6718cb21067e5718cb210ffcc318cb210acff764cb2118e7e654cb210067d654cb21005ef764cb210aeef764cb2136f6e654cb210076d654cb21067cf734cb21016ee634cb21016ec634cb2103dec714cb210ffcf304cb2117e7e65d07210067d65d0721036be64d0721006bd64d0721065ee72d0721005ed72d072113e7e65907210067d6590721006bf6490721036bc6490721034ff76507211567e65507210067d6550721036be6450721006bd6450721005df73507210fddc7350721005ef7250721065ec72507210c57e75107210057d75107211367e65107210067d6510721006bf6410721036bc64107210d4fd768c72111e7e658c7210067d658c721006df638c721016dc638c721007ce328c721014ff764c721064fc764c72110e7e654c7210067d654c721005bf744c721005bc744c721016de634c721006dd634c721005ef724c721065ec724c72100cff76583210067e65583210067d6558321066f86058321004ff755832101cfe7558321004fd755832101cfc7558321004ff7458321034fc7458321004ff7358321014fe7358321014fc7358321066fb2058321066f820583210f6fa105832103cff75d922101cfe75d9221004fd75d922103cfc75d9221014fe73d9221004fd73d922103cfc73d922103eed72d922103ef671d922100cfe70d9221004fd70d922100cfc70d9221004fd769922103ebf649922103ebc6499221034ff765922103ebc6459221004ff755922101cfe7559221004fd755922101cfc755922103ebf7459221006be5459221006bd5459221004ff7359221014fe7359221014fc7359221
  | 19 => 0x93110d7e75109310057d7510931006bf6410931036bc6410931015de7310931005dd7310931005f67110931005f57110931014fe76d0531014fc76d0531006bf64d0531036bc64d0531015de73d0531005dd73d0531177d431d053112cfe7690531166bf6490531036bc6490531034ff7650531014fe765053114cfd7650531014fc7650531006bf6450531036bc6450531005df7350531015dc7350531164fe761053110d7e75105310057d7510531006bf6410531036bc641053103fd431105310079f648c5312aede648c5312aedc648c5310079c648c5310069c648c531006dc628c53103dde718c53103fd6718c53103edf618c531017d7618c53100cfe76d8131006bf64d8131006bc64d8131106fa60d8131004ff75d813101cfe75d8131004fd75d813101cfc75d8131034fe74d8131004fd74d813100cfc73d8131064fe72d8131004fd72d8131014fd71d8131006de31d8131046dc31d8131106fa30d8131106fa10d81310057f755813110d7c7558131005bf7458131005bc7458131006bf6458131006bc6458131005ef7258131005ec7258131106f860581310657f76597210c67f765972101c7f76597210667f64597210667c64597210667f63597210067e63597210667c63597210667f60597210067e60597210667c60597210067f74597210067e74597210067d74597210067c74597210067f73597210067e73597210067d73597210067c73597210067e43597210067c43597210c67f72597210667e72597210c67d72597210667c72597210667e42597210667c42597210067f32597210667e32597210667c32597210c67f71597210c67e71597210067d71597210c67c71597210067f31597210067c31597210667f21597210667c21597210067f70597210067e70597210067d70597210067c70597210067e40597210067c40597210067f30597210067e30597210067c30597210667f20597210067e20597210667c20597210067e10597210067c1059721064ff75d932101cfe75d93210667e75d932101c7e75d9321004fd75d93210667d75d93210047d75d9321064fc75d9321006be54d9321006bd54d9321014fe73d9321066de73d9321014de73d9321004fd73d9321066dd73d9321004dd73d9321064fc73d9321066ee72d9321066f571d932100cfe70d9321004fd70d932100cfc70d9321004fd76993210067e65993210067d6599321066bf6499321066bc6499321034ff76593210067e65593210067d6559321066bc6459321004ff755932101cfe7559321004fd755932101cfc7559321066bf7459321004ff7359321014fe7359321014fc7359321006be4359321006bc4359321066be4259321066bc4259321004ff705932100cfe705932100cfc7059321064ff75d8f2101cfe75d8f210667e75d8f2101c7
  | 20 => 0x6bc51d9131166bf31d9131166be31d9131166bc31d9131006bf70d9131006be70d9131006bd70d9131006bc70d9131006bf50d9131006be50d9131006bd50d9131006bc50d9131166bf30d9131166be30d9131166bd30d9131166bc30d9131006be20d9131006bc20d9131006be10d9131006bc10d9131006bf649913114df57199131175f77159131004ff755913101cfe7559131004fd755913101cfc7559131006bf745913114cff7359131006df7359131004df7359131004ff7259131064fc7259131174ff7159131006f77159131004ff705913100cfe705913100cfc7059131164fe7619131036be6419131006bd6419131165be7619131006be7619131164be7619131006bf6519131006be6519131006bd6519131006bc651913112fb7311913112f9c311913112fb43119131006be6019131006bc6019131036bf7519131036be7519131036bd7519131036bc7519131036bf7319131036be7319131036bd7319131036bc731913112ebf531913112ebe531913112ebd531913112ebc5319131036bf7219131036be7219131036bd7219131036bc7219131006bf5219131006be5219131006bd5219131006bc521913112ebf321913112ebe321913112ebd321913112ebc3219131036bf7119131036bd7119131006bf5119131006be5119131006bd5119131006bc511913112ebf311913112ebe311913112ebd311913112ebc311913112e9c3119131036bf7019131036be7019131036bd7019131036bc7019131006bf5019131006be5019131006bd5019131006bc501913112ebf301913112ebe301913112ebd301913112ebc3019131006be2019131006bc2019131006be1019131006bc1019131006bf64d8931006bc64d8931004ff75d893101cfe75d8931004fd75d893101cfc75d8931034fe74d8931004fd74d8931006ee52d8931006ed52d89310eeee32d89310eeed32d893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931006ec20d893110d7e75989310057d7598931005be7498931005bd7498931006bf6498931006bc6498931006ef62989310d5f57198931005bf7458931005bc7458931006bf6458931006bc64589310fdf77158931006bf6418931006bc6418931006ed6218931064ff751893101cfe7518931004fd7518931064fc7518931034fe7418931004fd7418931066ee5218931006ed5218931066ee32189310aeed32189310aedc311893100cfe7018931004fd701893100cfc7018931006ee2018931066ec2018931004fe76d0931004fd76d0931034fc76d0931006bf64d0931036bc64d0931004fe7690931004fd7690931064fc7690931006bf6490931036bc6490931004ff7650931004fe7650931004fc7650931006bf6450931036bc6450931004fe7610931004fd7610931064fc761
  | 21 => 0xe7598a31004fd7598a310667d7598a310047d7598a31064fc7598a31034fe7498a31004fd7498a31066ee3298a310feed3298a3103cfe7198a3103cfc7198a3103eee2198a3103eec2198a3100cfe7098a31004fd7098a3100cfc7098a31005bf7458a31005bc7458a3103eec6258a31004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a31006bf7458a31004bf7458a31034fc7458a31006bc7458a31034bc7458a310d6ee3258a310d6ed3258a310d6dc3258a3103cfc7158a3103eee2158a3103eec2158a31004ff7058a3100cfe7058a3100cfc7058a310d6df3058a31034ff76d0a3103cfe76d0a31004fd76d0a31015de73d0a31005dd73d0a31064ff7690a3103cfe7690a31004fd7690a31006bf6490a31036bc6490a31015de7390a31005dd7390a310079f4390a31004ff7650a31004fd7650a3103cfc7650a31005df7350a31015dc7350a31064ff7610a3103cfe7610a31004fd7610a3111d7e7510a310057d7510a31006bf6410a31036bc6410a31015dc7310a312af9f4310a3103df67110a31005f57110a312adde748ca312addc748ca31015de728ca31017ce728ca31007ce628ca31006dd628ca31007cd628ca31007d6718ca31005dd718ca31007d5718ca31016de618ca31017d6618ca31005dd708ca3114cfd76d063103ebf64d063103ebc64d0631015dc73d06312af9f43d0631174ff765063103ebf645063103ebc6450631005df7350631015dc73506310079f435063100cff76582310057f755823111d7c755823103ef86058231004ff75582310067f75582310047f755823101cfe7558231004fd755823101cfc75582310067c755823101c7c7558231004ff7458231034fc7458231004ff7258231064fc725823103cfc7158231116fa305823103efb105823103ef81058231034fe76d9131004ff75d913101cfe75d9131004fd75d913101cfc75d9131006bf54d9131006be54d9131006bd54d9131006bc54d913103cff73d9131164fd73d9131166bf43d9131166bd43d9131064fe72d9131004fd72d913100cfe70d9131004fd70d913100cfc70d9131006be40d9131006bc40d9131034be76d9131006bf65d9131006be65d9131006bd65d9131006bc65d9131167b731d91311679c31d9131167b431d9131006be60d9131006bc60d9131006bf75d9131006be75d9131006bd75d9131006bc75d9131166bf73d9131166be73d9131166bd73d9131166bc73d9131166bf53d9131166be53d9131166bd53d9131166bc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d9131006be52d9131006bd52d9131006bc52d9131166bf32d9131166be32d9131166bd32d9131166bc32d9131166bf71d9131166bd71d9131006bf51d9131006be51d9131006bd51d9131
  | 22 => 0x884103eee7298841036ef4298841066ec429884103eee219884103eec219884100cfe7098841004fd709884100cfc7098841004ff755884101cfe7558841004fd755884101cfc7558841004ff7358841014fe7358841014fc735884103eef7258841036ef4258841036bc4258841036ec4258841036ac425884103eee215884103eec2158841004ff705884100cfe705884100cfc7058841036bf4058841035bd7690841006bd7690841036bf65908410373e659084138ebd65908410373d65908410063d659084112dbe739084112dbc7390841006bd6390841035be7290841037ae7290841006bd6290841005bd7190841386be6190841037b66190841005bd70908411debe6090841036bc6090841064ff768c84103cfe768c841004fd768c84119e7e658c8410067d658c841035be748c841005bd748c841066ee628c841006ed628c841004ff764c841004fd764c84103cfc764c84118e7e654c8410067d654c841005bf744c841035bc744c841016de634c841006dd634c841006ee624c841006ed624c841005f7714c84103df4714c84103dbf7650441006bf7650441004bf765044103ebf655044103f3e655044137ebd655044103f3d65504410063d65504410079f735044112dbe735044112dbc73504410079c735044112d9c7350441006bd6350441005bc725044103dbf7150441037b7715044103ebe615044103fb6615044103fb6515044137fb55150441377b7315044103fb43150441005bf7050441004ff755804101cfe7558041004fd755804101cfc755804100cfd7458041004ff7358041014fe7358041014fc7358041004ff7258041064fc725804103efb7058041036fb4058041036f84058041126fa3058041126fa205804103efb105804103ef8105804103cff75d923101cfe75d9231004fd75d923103cfc75d923103edd73d9231166be43d9231166bc43d9231166dc43d9231064fe72d9231004fd72d923103cfe71d923103ef671d923100cfe70d9231004fd70d923100cfc70d9231166df30d923114cfd769923103ebf649923103ebc6499231034ff765923103ebc6459231004ff755923101cfe7559231004fd755923101cfc755923103ebf7459231006be5459231006bd5459231006df735923114ebf435923114ebd435923114edc4359231004ff7259231064fc725923103cfe715923103cfc715923103ebe415923103ebc4159231004ff705923100cfe705923100cfc705923114edf30592312aedd76d0e31015de74d0e310179e74d0e312aedf64d0e312af9e64d0e312aedd64d0e310079d64d0e31005de72d0e312afd671d0e31005dd71d0e312afd571d0e31016de61d0e31017d661d0e31005dd70d0e3111d7e7598a310057d7598a3103eef6298a31064ff7598a3101cfe7598a310667e7598a3101c7
  | 23 => 0x6be5418941006bd5418941014fe7318941004fd7318941064fc7318941006bf4318941006bd4318941066ee5218941006ed521894100cfe7018941004fd701894100cfc7018941006ee2018941066ec2018941006df63909411e6dc6390941006ef6290941066ec6290941005f67190941005f57190941006df63509411cedc6350941006ef6250941006ec6250941037ac4250941005f77150941005f47150941037b44150941004fe768c941004fd768c941064fc768c941006df638c941016dc638c941004ff764c941004fe764c941004fc764c941006df634c941016dc634c941006df6390541166dc6390541035f67190541036f7619054103dbf7590541395bd7590541005bd73905410079f6390541166be6390541166bc63905410079c63905411669c6390541006bc629054103dbe719054103ebf6190541037b7619054100cfe76d8141006df63d8141006dc63d8141146fa60d8141004ff75d814101cfe75d8141004fd75d814101cfc75d814100cfc74d8141006be54d8141006bd54d8141014fe73d8141004fd73d8141014fc73d8141006bf43d8141006bd43d8141064fe72d8141004fd72d8141034fd71d8141006be41d8141146fa40d8141146fa10d81410057f75581411557c7558141005df735814114ddc7358141006df6358141006dc6358141005ef7258141005ec7258141146f860581410367f74594410367e74594410367d74594410367c74594410067f73594410067e73594410067d73594410067c73594410367f43594410367e43594410063e43594410367d43594410367c43594410363c43594410067f72594410067e72594410067d72594410067c72594410367f42594410367e42594410367d42594410367c42594410363c42594410067f32594410067c32594411367f715944103e7e71594411367d715944103e7c71594410367f41594410363f415944103e7e41594410367d415944103e7c41594410067f315944103e7e315944103e7c315944103e7e215944103e7c21594410067f70594410067e70594410067d70594410067c70594410367f40594410363f40594410367e40594410367d40594410367c40594410067f30594410067e30594410067c30594410067e20594410067c205944103e7f10594410067e105944103e7c1059441004ff7558c4101cfe7558c41004fd7558c4101cfc7558c4103cff7358c4103edf7358c41036df4358c4112ebe4358c41036bc4358c41036dc4358c41004ff7258c41064fc7258c41036bc4258c4112edf3258c41036bf4158c4103ede3158c4103edc3158c41004ff7058c4100cfe7058c4100cfc7058c41036bf4058c4112edf3058c41064ff759884101cfe7598841004fd7598841064fc7598841014fe7398841004fd7398841064fc739884103cfe729
  | 24 => 0xa305824103efb105824103ef81058241014fe76d8d4114ede63d8d41004ff75d8d4101cfe75d8d41004fd75d8d4101cfc75d8d41006df53d8d4114ede53d8d41006dd53d8d4114edc53d8d4114ede43d8d41064fe72d8d41004fd72d8d4114edf32d8d4114edc32d8d41034fd71d8d4114edf31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d4114edf30d8d41006de30d8d4114edc30d8d4114dde76d8d41014de76d8d41006df65d8d41006de65d8d41006dd65d8d41006dc65d8d410079f74d8d410079e54d8d410079d54d8d412afd741d8d412afd441d8d41006de60d8d41006dc60d8d41006df75d8d41006de75d8d41006dd75d8d41006dc75d8d41006df74d8d4114ede74d8d41006df54d8d412aede54d8d41006dd54d8d412aedc54d8d41006df72d8d41006de72d8d41006dd72d8d41006dc72d8d41006df52d8d41006de52d8d41006dd52d8d41006dc52d8d412aedf42d8d412aedc42d8d412aedf71d8d4114ede71d8d41006dd71d8d41006df51d8d41006de51d8d41006dd51d8d41006dc51d8d412aedf41d8d412aedc41d8d41006df70d8d41006de70d8d41006dd70d8d41006dc70d8d41006df50d8d41006de50d8d41006dd50d8d41006dc50d8d412aedf40d8d41006de40d8d412aedc40d8d41006de20d8d41006dc20d8d41006de10d8d41006dc10d8d4114edc6358d41005de7618d4114ede7618d41006df6518d41006de6518d41006dd6518d41006dc6518d4114f9d7418d410079e5418d410079d5418d41176df6118d413afd74118d413afd44118d41006de6018d41006dc6018d41005be76d0d41036be76d0d41164be76d0d41035bf75d0d413a5bd75d0d4114dbd73d0d410079f63d0d41016be63d0d41016bc63d0d4114f9c63d0d410169c63d0d4103dbe71d0d41036bf61d0d41037b761d0d4114f9c31d0d41014fc7650d41006df6350d41016dc6350d41005f77150d41005f47150d4114dbc7650d41016bc7650d41014bc7650d4139dbf7550d4139dbd7550d41035bf7350d410379f7350d410079f6350d41016be6350d41016bc6350d4114f9c6350d410169c6350d41007b77150d4103dbc7150d41007b47150d41005b47150d41036bf6150d41037b76150d4114f9f3050d41006df63d8941006dc63d8941004ff75d894101cfe75d8941004fd75d894101cfc75d8941014fe73d8941004fd73d8941014fc73d8941006ee52d8941006ed52d894100cfe70d8941004fd70d894100cfc70d8941006ee20d8941006ec20d89411557e75989410057d759894114dde7398941005dd7398941006df6398941006dc6398941006ef6298941005df735894114ddc7358941006df6358941006dc6358941006df6318941006dc6318941006ed6218941064ff751894101cfe7518941004fd7518941064fc7518941
  | 25 => 0xcb41016de638cb41006dd638cb41004ff764cb41004fd764cb41034fc764cb41005f7714cb41005f4714cb41004ff755834101cfe7558341004fd755834101cfc7558341036be5458341006bd5458341004ff7358341014fe7358341014fc7358341036bf4358341006bd4358341004ff7258341064fc7258341036bc4158341036fb7058341036fb4058341036f8405834116efa1058341014ff7658e41035bc7458e4103edc6358e411679e4358e41004ff7558e4101cfe7558e41004fd7558e4101cfc7558e41166be4358e41166de4358e41166bc4358e41004ff7258e41064fc7258e4103cfc7158e4103ede3158e4103edc3158e41004ff7058e4100cfe7058e4100cfc7058e41014ff7650e41165bf7450e41016de6350e41006dd6350e410379c4350e41005f77150e4103df47150e4113d7e7598a410057d7598a4103eef6298a41064ff7598a4101cfe7598a410667e7598a4101c7e7598a41004fd7598a410667d7598a410047d7598a41064fc7598a41014fe7398a41004fd7398a41064fc7398a4103cfe7198a4103eee2198a4103eec2198a4100cfe7098a41004fd7098a4100cfc7098a4103eec6258a41004ff7558a4101cfe7558a41004fd7558a4101cfc7558a41004ff7358a41014fe7358a41014fc7358a4103cfc7158a4103eee2158a4103eec2158a41004ff7058a4100cfe7058a4100cfc7058a41066ee6290a41006ed6290a4103df67190a41005f57190a41386bf6590a41386bd6590a41165be7390a41165bc7390a41006bd6390a41035be7290a41007ae6290a41006bd6290a41007ad6290a41007b67190a41005bd7190a41007b57190a41036be6190a41005bd7090a411debe6090a411debc6090a41006ee6250a41006ed6250a41005f77150a4103df47150a41005bd7610a41036bd7610a410373e7510a410373d7510a413bebf6510a413bebd6510a41165be7310a41035bc7310a41006bd6310a41037ae7210a41006bd6210a41005bd7110a41037b66110a41005bd7010a411a6be6010a411a6bc6010a41064ff768ca4103cfe768ca41004fd768ca41035be748ca41005bd748ca41066ee628ca41006ed628ca41004ff764ca41004fd764ca4103cfc764ca41005bf744ca41035bc744ca41006ee624ca41006ed624ca4103dbd76d0641036bd76d064103ebf65d06413b6bd65d0641165be73d0641035bc73d0641006bd63d0641005be72d064103fb661d064103fb651d06413b7b551d0641005bd70d064100cff76582410057f755824113d7c755824103ef86058241004ff75582410067f75582410047f755824101cfe7558241004fd755824101cfc75582410067c755824101c7c7558241004ff7358241014fe7358241014fc7358241004ff7258241064fc725824103cfc715824115efa405824115ef
  | 26 => 0x1e6df30d9132006bf64991321cded72991321f5ef7259132005f77159132005f47159132004ff755913201cfe7559132004fd755913201cfc7559132006bf74591321ccff7359132006df73591321f4ff7259132006ef7259132004ff7159132006f77159132004f7715913203cfc7159132006f47159132004f47159132004ff705913200cfe705913200cfc70591321cedf30591321e4fe7619132036be6419132006bd6419132014fe76d0932014fc76d0932006bf64d0932036bc64d0932015de73d0932005dd73d09321acfe7690932036be6490932006bd6490932034ff7650932014fe76509321ccfd7650932014fc7650932006bf6450932036bc6450932005df7350932015dc73509321e4fe761093218d7e75109320057d7510932036be6410932006bd6410932065de728c932067ce728c932066df628c932017cf628c932005dd708c932004ff75d853201cfe75d8532004fd75d853201cfc75d8532034fe74d8532004fd74d8532006f651d8532006f551d85320fef631d853200cfe70d8532004fd70d853200cfc70d8532006f610d8532006f410d8532006f76198532005bf7458532005bc7458532006f5611853203cff751853201cfe7518532004fd751853203cfc7518532034fe7418532004fd741853203eed7218532006de32185320aedc321853203ef65118532006f5511853203ef631185320aef5311853200cfe7018532004fd701853200cfc70185320aedf3018532006f6101853203ef4101853200cfe76d8132186fa60d8132004ff75d813201cfe75d8132004fd75d813201cfc75d8132034fe74d8132004fd74d8132014fd72d813203cfe71d8132004fd71d8132186fa30d8132186fa20d81320057f755813218d7c7558132005bf7458132005bc7458132005f77158132005f47158132186f86058132004ff7558f4101cfe7558f41004fd7558f4101cfc7558f41036df7358f41036df4358f41036dc4358f41004ff7258f41064fc7258f41176dc3258f41176df3158f41004ff7058f4100cfe7058f4100cfc7058f41176df3058f41035bf7650f4112ebf7650f4112cbf7650f413c5bf7550f413c5bd7550f410379f7350f41016be6350f41016bc6350f4103dbc7150f411779f3050f41064ff7598b4101cfe7598b41004fd7598b41064fc7598b41036be5498b41006bd5498b41014fe7398b41004fd7398b41064fc7398b41036bf4398b41006bd4398b41066ee7298b41036ef4298b41066ec4298b41036bc4198b4100cfe7098b41004fd7098b4100cfc7098b41004ff7558b4101cfe7558b41004fd7558b4101cfc7558b41004ff7358b41014fe7358b41014fc7358b41036ef7258b41036ef4258b41036ec4258b41004ff7058b4100cfe7058b4100cfc7058b41064ff768cb41034fe768cb41004fd768
  | 27 => 0xd759844203cfc7598442014fe7398442004fd739844203cfc739844203ef67198442036f7419844203ef44198442066f7219844203ef4219844200cfe7098442004fd709844200cfc7098442004ff755844201cfe7558442004fd755844201cfc7558442036be5458442006bd5458442004ff7358442006df7358442004df7358442014fe7358442014fc7358442006dc7358442014dc7358442036bf4358442006bd4358442066f77158442036f74158442036bc4158442036f44158442036b44158442066f72158442066f42158442004ff705844200cfe705844200cfc7058442004ff755804201cfe7558042004fd755804201cfc7558042036be5458042006bd5458042004ff7358042014fe7358042014fc7358042036bf4358042006bd4358042036bf4258042006bd4258042004ff715804203cfc7158042036bc4158042066fb7058042036fb40580421a6be4058042036bc4058042036f840580421a6fa3058042066fb2058042066f820580421a6fa1058042064ff75d923201cfe75d9232004fd75d9232064fc75d9232066dd73d9232064fe72d9232066ee72d923203cfe71d9232004fd71d923200cfe70d9232004fd70d923200cfc70d92321ccfd7699232066bf6499232066bc6499232034ff7659232066bc6459232004ff755923201cfe7559232004fd755923201cfc7559232066bf7459232006be5459232006bd54592321cebf43592321cebd4359232064fe7259232064fc7259232066be4259232066bc4259232004ff715923203cfc7159232004ff705923200cfe705923200cfc70592321ccfd76d0a321f4ff7650a32066f7619863203cff759863201cfe7598632004fd759863203cfc7598632034fe7498632004fd7498632064fe729863203eee729863203ef631986320eef53198632066f7219863203ef4219863200cfe7098632004fd709863200cfc7098632066f46158632004ff755863201cfe7558632004fd755863201cfc7558632004ff7458632034fc7458632064fc72586320d6f631586320d6dc3158632066f72158632066f42158632004ff705863200cfe705863200cfc705863200cff76582320057f755823219d7c7558232066f86058232004ff75582320067f75582320047f755823201cfe7558232004fd755823201cfc75582320067c755823201c7c7558232004ff7458232034fc7458232064fc7258232056df3258232004ff715823203cfc7158232056dc3158232196fa3058232066fb2058232066f82058232034fe76d9132004ff75d913201cfe75d9132004fd75d913201cfc75d9132006be54d9132006bd54d9132064ff73d91321e4fd73d91321e6bf43d91321e6bd43d913203cfe71d9132004fd71d913200cfe70d9132004fd70d913200cfc70d9132006be40d9132006bc40d9132
  | 28 => 0xd42006df6350d42016dc6350d420379c4350d42005ef7250d42005ec7250d42035ee7290942036ef62909423eebf65909423eebd6590942006bf6390942065be7290942066bf6290942037af6290942005bd70909421debe60909421debc6090942004ff75d854201cfe75d8542004fd75d854201cfc75d8542014fe73d8542004fd73d8542014fc73d8542006f731d8542006f431d854200cfe70d8542004fd70d854200cfc70d8542006f76198542005df73585421cddc7358542006f5611854203cff751854201cfe7518542004fd751854203cfc7518542014fe7318542004fd731854203cfc7318542006be4218542006f7311854203ef4311854200cfe7018542004fd701854200cfc701854200cfe76d81421c6fa60d8142004ff75d814201cfe75d8142004fd75d814201cfc75d8142014fe73d8142004fd73d8142014fc73d8142034fd72d814203cfe71d8142004fd71d8142006fb50d81421c6f850d81421c6fa40d81421c6fa20d81420057f75581421d57c75581421c6f860581420367f74594420367e74594420367d74594420367c74594420067f73594420067e73594420067d73594420067c73594420367f43594420367e43594420367d43594420367c43594421b67f72594420667e72594421b67d72594420667c72594420367f42594420667e42594420367d42594420667c42594420067f32594420667e32594420667c32594420067f71594420067e71594420067d71594420067c71594420367f41594420367e41594420367d41594420367c41594420067f31594420067c31594420667f21594420667c21594420067f70594420067e70594420067d70594420067c70594420367f40594420367e40594420367d40594420367c40594420067f30594420067e30594420067c30594420667f20594420067e20594420667c20594420067e10594420067c1059442004ff7558c4201cfe7558c42004fd7558c4201cfc7558c42064ff7358c42066df7358c42036df4358c42036dc4358c42066de3258c42066dc3258c42004ff7158c4203cfc7158c421aedf3158c42004ff7058c4200cfe7058c4200cfc7058c421aedf3058c42035bf7650c421f6bf7650c423e5bf7550c423e5bd7550c420373e6550c420373d6550c42035bf7350c420379f7350c42016be6350c42016bc6350c42005bf7250c421e6be6250c42037ae6250c42005bc7150c421a5be7050c421a5bc7050c421af9f3050c42065bf7650842006bf7650842004bf76508423ddbf75508423ddbd75508420673e65508420673d6550842005bf7350842065bf7250842037af7250842066be6250842067ae6250842067ae52508423d7ad5250842005bc71508421a5be70508421a5bc70508423cfae2050842067ac205084203cff759844201cfe7598442004f
  | 29 => 0x1cfc7558742004ff7358742014fe7358742014fc7358742036f77158742036f74158742036f44158742004ff705874200cfe705874200cfc7058742004ff755834201cfe7558342004fd755834201cfc7558342004ff7358342014fe7358342014fc7358342004ff715834203cfc7158342036fb7058342036fb4058342036f840583421eefa2058342014ff7658e42066dc6358e42004ff7558e4201cfe7558e42004fd7558e4201cfc7558e421e6de5358e42006dd5358e421e6de4358e42064fc7258e42066de3258e42066dc3258e42004ff7158e4203cfc7158e421e6dc3158e42004ff7058e4200cfe7058e4200cfc7058e421e6df3058e42005bd76d0e42036bd76d0e42035bf75d0e4240dbd75d0e42016be63d0e42016bc63d0e42005bd72d0e42037ae62d0e42005be71d0e421e79c31d0e421ddbe70d0e42035bc70d0e42014ff7650e42016de6350e42006dd6350e42005ef7250e42065ec7250e421e5bf7650e42016bf7650e42014bf7650e42405bf7550e42405bd7550e42035bf7350e420379f7350e42016be6350e421e79e6350e420169e6350e420079d6350e42016bc6350e42005bf7250e42007af7250e42007ac7250e42036be6250e42005bc7150e421ddbe7050e421ddbc7050e421e79f3050e42065bd76d0a42036bd76d0a42035bf75d0a423fdbd75d0a42005bd73d0a42067ae62d0a42067ae52d0a423f7ad52d0a42005be71d0a421ddbe70d0a42035bc70d0a42066f7619864203cff759864201cfe7598642004fd759864203cfc7598642014fe7398642004fd739864203cfc7398642064fe7298642066f7219864203ef4219864200cfe7098642004fd709864200cfc7098642066f46158642004ff755864201cfe7558642004fd755864201cfc7558642006be5458642006bd5458642004ff7358642014fe7358642014fc7358642006bf4358642006bd4358642064fc7258642066f72158642066f42158642004ff705864200cfe705864200cfc705864200cff76582420057f75582421bd7c7558242035bc7458242066f860582421dfba4058242004ff75582420067f75582420047f755824201cfe7558242004fd755824201cfc75582420067c755824201c7c7558242006be5458242006bd5458242004ff7358242014fe7358242014fc7358242006bf4358242006bd4358242064fc7258242006bf4258242004ff715824203cfc71582421debe40582421defa40582421debc4058242066fb2058242066f82058242014fe76d8d421cede63d8d42004ff75d8d4201cfe75d8d42004fd75d8d4201cfc75d8d421cede43d8d42034fd72d8d421cedf32d8d4203cfe71d8d42004fd71d8d421cedc31d8d4200cfe70d8d42004fd70d8d4200cfc70d8d421cedc6358d42005f77158d42005f47158d42014fc765
  | 30 => 0x4419874303ef63198743166f5319874300cfe7098743004fd709874300cfc7098743036bf4098743004ff755874301cfe7558743004fd755874301cfc7558743014fc7458743004ff7258743064fc7258743036f77158743036f74158743036f4415874314ef6315874314edc3158743004ff705874300cfe705874300cfc7058743004ff755834301cfe7558343004fd755834301cfc7558343014fe7458343014fc7458343036de4358343036dd4358343004ff7258343064fc7258343004ff715834303cfc7158343086dc3158343036fb7058343036fb4058343036f84058343216fa3058343004ff75d894301cfe75d8943004fd75d894301cfc75d89431f6bd74d8943034fd73d89431f6ee32d894303cfe71d8943004fd71d894300cfe70d8943004fd70d894300cfc70d89431f6df30d8943006ef6298943005f77158943005f4715894320d7e75189430057d7518943006ed6218943064ff751894301cfe75189430667e751894301c7e7518943004fd75189430667d75189430047d7518943064fc7518943034fd7318943066ee32189431aeed321894303cfe7118943004fd711894300cfe7018943004fd701894300cfc7018943004ff75d854301cfe75d8543004fd75d854301cfc75d8543034fd73d8543064fe72d8543004fd72d8543006f751d8543006f451d8543176f631d854300cfe70d8543004fd70d854300cfc70d8543006f7619854320d7e75185430057d7518543006f5611854303cff751854301cfe751854303e7e751854301c7e7518543004fd751854303e7d75185430047d751854303cfc751854303ebd7418543034fd73185433aedf431854312ebe431854312ebc431854312edc4318543064fe7218543004fd7218543006f7511854303ef4511854303ef6311854312ef5311854300cfe7018543004fd701854300cfc701854312edf301854300cfe76d814320d7e75d81430057d75d8143206fa60d8143004ff75d814301cfe75d81430067e75d814301c7e75d8143004fd75d81430067d75d81430047d75d814301cfc75d8143014fd74d8143034fd73d8143064fe72d8143004fd72d814303cfe71d8143004fd71d8143206fa40d8143206fa30d8143206f86058143004ff7558f4201cfe7558f42004fd7558f4201cfc7558f42036df7358f42036df4358f42036dc4358f42036bc4258f421f6df3258f42004ff7158f4203cfc7158f421f6dc3158f42004ff7058f4200cfe7058f4200cfc7058f42036bf4058f421f6df3058f4203cff759874201cfe7598742004fd759874203cfc7598742014fe7398742004fd739874203cfc7398742036bc429874203ef67198742036f7419874203ef4419874200cfe7098742004fd709874200cfc7098742036bf4098742004ff755874201cfe7558742004fd7558742
  | 31 => 0x4802000e000006803000400100000740080000030014000001000003c00c00100c8008002007000000401200600400000000000008004004000002004800200300c000800200d006000000200300000a800a000002001000400200200180040050000008006000003801403400300300080220040010004000001000809c010001001801402200100080000000070000004012001001800800600100180000020020030004012000001005c000000004001802a000001002402000800000080080030018014000001003001400000000780000040020000014004007002802801402f0008000006002000003000800f000000800000c002804401a00f00c00080040000008000004001003004c002010003000000a0060048028002001005001c018007002801001400300100000000090048000006000000800400600000080240140070000004008001001808001001000200380020000050000004002002000000c002002803000400c002000000000b0028014000002001000801000c001000801a00000400240100030000004014000001800400a000000000800402600480300180010018000002052000001c006001003000401e0010000008074000007802c01c005000003400a00c000000001000e00a003400e00100000180020300070000018009002800000e000000000401400000a803000003800000040080040050010000000000000800000a007800002400001c0014024012005005c01a00d0098070004000000001401600e0048010000003002000c0040000048000004002003000c00e0040000004004001009000801c00000c0000004000001001802600000000800040010000010002000002000c00000900080080360040050008006000000006c00c00600200000040050010000004002007800000000d006000c00800e0000000000002003801000e00100100a4004015001001800600e0030020000000000001c018018064ff7598b4301cfe7598b43004fd7598b43064fc7598b43014fe7498b43064fc7498b43066ee7298b43036ef4298b43066ec4298b43066ee3298b431e6ed3298b4303cfe7198b43004fd7198b431e6dc3198b4300cfe7098b43004fd7098b4300cfc7098b43004ff7558b4301cfe7558b43004fd7558b4301cfc7558b43014fc7458b43036bc7458b43014bc7458b43036ef7258b43036ef4258b43036bc4258b43036ec4258b431ceee3258b43004ff7158b4303cfc7158b43004ff7058b4300cfe7058b4300cfc7058b43036bf4058b4303cff759874301cfe7598743004fd759874303cfc7598743014fe749874303ebe7498743014be749874303cfc7498743166be4398743036bc4398743064fe7298743004fd7298743036bc429874303ef6719874303ebf4198743036f7419874303ef
  | 32 => 0x24002000001803c010000000004000a004001001c002002005000c00400700a002800800100080100020000000000002000000000000c004001000001400300b8000002002000800801400c0050008000001010001000601800400040080000008000012001003005002001a000002c00401c000000801a000003800000000400380040060000050000002008005003c004001000804000c0100000008004000002001c0380000000004004001002002c004023002800000e000006000c0020000000000004000001000801200000180040120010020010016001001802c000003000001400000c000800400000400400740080000030004008000003800c00000300000000060020018050002000000800000200a001000c00200600080ec00000600b0000004000000800c000009000000c00a00000680000000080010000002004000802c0000020048000006015002008800600200100240020010000008002007002002c00200d00e801800800800180280000060070020002000007000000c00b0080074020015018000c0140050008008010001001000000a006002001800400000180080000010018004000000004800c000015000800400200d00180c8000003002001401c000007000c00c0010008000004002002800000a0000028000016008003802800600a00000000020060028008000009001000400000000400500000000028014002002008000000a000002000400000c0010024000002000003000000000100140020000000000024000004800400201e003003403a00700b00000000000010000000000003000000a000001806801a001000000000000000000140180030008000016003002002c00c002000000800c00d000000801401c002800000a0080008000000007000000400a000000000000000100b0008020002004000c00e0050078000018000000001c0200040018040002002001802c008002000800400600800000180120020028000004005002002800200200000140200010010020008000001804000a00400000000060040050018002020000800001a00f004000c00000900600180080020048058000011002004401600600000040000000038014002007000801801000d0040000002001000000c00a0020000018004005000000000000000000040040090010008000000001800c0000050010004004000000805000e000000001000e00000000040000000000000002008001001000a0020000008022000000802000400000000040040010000030000001000800800400800c000400000100080040420090088010000006003800401200c0000018002002000800000e00f0020000010006002001400000500080000020180108014000008000001000600200180040020010060048000000002001400c0
  | 33 => 0x10048030000003008000004a00e006000001c00000000100020290058000006002002800401400100580040020050000000006006001001c000000000002c030003007001000801000380f0004003003800000000d00a000002a000001800000601800680500060060000014008023003000401003a0038008010002002800401600300b80000260110008004004004000002400a0010048000000011009806000401d01300000140050040000000006005000007800a000802c006002000004c0200310000050006003000800000800000100080160230058004002002005000001201c002000c002003000000001a003000001800600100400080040060000000004041003000800e00300300180020000010000016001000801c012000001000800800200100280260000000030020000000001801600e01a0000066005002800c0020050030000002002004000000004f0000008000000000807c00002e0028018000004010000000800000080140140000008050008003000001400a006004806804e00000080c0000001000000004800000000040040010008068018000007000400000000f00000180020008000002000001805000c0020000000000001000801001400d002000805c001000801400400e000003800e0010048000004001009000401400100100100100050030088012000000000800000c001012c000023002002000c003009000400000a000000000800d004801000c0020008010010003000000400801a000800000e000000800c00600200b00ac00400500080000000030010000062014000002800a00500080080100000000010008000001000c008002001800800a0010008044020002008003c03200f00a800000000100000040020000000010000000010004000e01200100100060000058034000004007800401400000180200220000010030016000000800404400700200000000450020004004000000000000000c00980200020020020004018001000801400200d00000500040040010040006003000002800a00700180380100070000014004002000000c0060010008000000001000001c002005001000c00000e003800400a014005002000e0000070034002001000000400200d000000400c00700180000260020030000002000000000c006007000002800c001000000000000f000001001800400400100020070030000004005001003800400c005000c002000000801c00000001d00040160150000000008008000002000200001a800806a00100f8020002011000002401a004005800400200000680040060020030020004001010800c038007000000002400e0088000004003009000c01402100b800000a000006800c00800000100040000210038008008000009000800000d00b000400400c0010
  | 34 => 0xd299aa52d13b253e879444322aa15c1a9299b17ca39a00006c7a7c20001af222ea7c066a01240c695287c1a9507d5139c6f6000095992e06c68c8c00000005bc21182f217449a11140394971029808bc59986084311f1651712b20349b7e1e1145250e173e92d0f9e05e8a2e4ea000059804c00000000a618cc47fd84d66ae80000001e6e3af88d8006000084211547c218f255008be60b1f7a9e49e3c00016d2681a0e006098fc9e2892847e9eba5d800006ec025c0389d22549828e1450558058143235b888a8310a8e095000052c952400017e2733a1c6000000097a8a849d215923b48e080000c22406a22c21480007ef0e7c68980000e421667cf2154000090e4b2000000000703ac000022406d48471298000000024714ac23594d0948853a000225200019b837280006b30000a5c184680c800000000005f9000011625dc5ca93060001daaa0c9610471157e536a84c00027748b800aa00020120000000000000095f8000395800045c8000000000000016f84ae255e76f2562321957288987d875aa5e400026d635900001d083386259f48380262834f8000000184e8eb800000000004c280ca14910de97c150200009562208e381d10000000225e1f8000069c000035f024806e966a19a93f691501d06569b2c72b18d07a38ddc2418068487a2a2000011c50b051c91829ae000178a439805c00007de77400003058f14867825017497b25751d947bf04c40909a2c6e385f45d98f763eb80004f4a85a47980000000000011a41217700ac1c880003468000a5b12c40001c3e432128e731126e93d22ee9a19fba09e0a068890a4600026122be0dd6428282252980007d60682000000000007ae65e96800000a5083880000001a5e59b21e052496da000000000000001bf0000768099a000083e0771d3a90f102247223863a1280a5829a484221f6a013236c9bd9c441418ace30506fe275845e98aa8d2554183600a80000001f840000c620db284a53c9b483a8a30a43527628ab8b40a6c00000001e8a913000032e24fc000000000000008d480000e68bba00016080000000000000008624e40001b84756000096480004638ae40ff800000010085d79bec4661aa600006ba000000078192341498f180000a26000275e868a14a33a80008a9162204d19a20001a2a48106b0a0f000021e80000428d0a98306b20001d02a3401aa88f11ce98c186a5b61d26223910607ca348a1624caa240000186152a3538fa8001004c01c0070000000006001002000000c006000003400000000000000120010018010002008001800401202a0058034000000001002000c005002802401000500180000000000010000000003001801401200301000140060000020004004001008001000000a000800800000200000080060010010008002001001800400c
  | 35 => 0x54400011ba00015060002388000000000009c839d00003b216ee2ad87fe0c18000000064a0000f1c0000c4e00023742a0800086f27424cf0df483983bc912978ea2389f88a00de29321138a23163255f18b04600000a64140e017877251ba2ce33d225c09d0000232062267d142649c800000002c697c84e63b9051e585010450f925c0000000821263865200000000d589c61202000215200023fa000026c0ed887249e8000a5e82462d9800000000007f68b50000074e00001f60001ef84c580000000000340000000000000000240000000000013f80000b54a2800006971b6c00021dc78a99460001a9a527800029c260659e8000799084200000003852776204a8106050e608f38cd43578b083f987d00008d8e198894c00015c45b100004faa00c8539e8401825b6000229e46194f6926880896b8000000162c77c80000000806000000063c1ae65d5a42a00b1512000028800008a053315a836ba94247a0b3a00008c4450937c00017c617607004f20212552a07417915229580ef63a482ec82292ce95501160b014949ae068801a81ea112181e5df9806273829406995a022a931e46b800000009bc3279ece45a0000000000000015f80000000000000053180008361ca64d9103460c000000000009c310d28161cc64f080004f88000860800000000009e1228e00025a429520728b608b03331ec02d5990e4f5952075b20943d3204897e06be19581d655a83d679e25d67db1d5243d0a4e14f01b649013980a2a65616da8b651d9baea3516fe2fb229433b11d0000000044c9f3a0d500004e406c000024267cd80008f1295a2c812583289e5631980000000000341000000004ec82c9bb46fe0000845a10c48ca58a8479ade059a5723d4000000024ba000067a0cb9880991877e71ba52e88c9e3400003c0000218a323800000022089a90624478890a44083c21e01a1673a88e600005f08930ed80000f601ce0000000192622200008b300005a4000000024769521dc800000008e388e80000000000000084b25505afa2860001dee7a21c6c8441ddca12163a00000009f7a316a31800000020bc9b202927a8220c0000ecc004158aa5d80000a09222241176a3168c000000d9a9cd27fe94d800000003662948e16483108287601e89d922366761cca9dc972c3c794be1c6a4c23d0a824818a58c3c187ba80789f2a4e885412b8d5ca4418d275da4c084c9d8623da9680ee1a1c02610c66de874a38900006ce0000a428000745000000000000000000000000068d0fde0a61f1065281c061004ba8a28c1c6e591b893aa9604b9156080f12f694998f69e4220a9d489900000bd64fb9dc622e000000012e25a713a294a9ca23a926729ac09c643d8ff813190fa1b41e222f723a07b404fe33e086c45d95162c99a4e2dd17684248e7283b00000
  | 36 => 0x1b82159856e0000000000000000009242a59c469af11b29e31c6851e826a7128f6c7cf800002d277c32909c019086e464118526b000007528ba067013488da1cd40ad196e00004460fb0e7a7c6252c8a828c256a968e86225b053995300000bac5930000000000071804764e30000000000085096d631a800000025a000000000000e0c57c9c301a3221e3da8ec20000000000000027e80000000000000000000028504729fc600022c20000ea01a38000a1823b00a8883477897841a80a241049a500000000482820e25893083f689987071fb6446831e80d8dd858e254e7521e68000000000008c24f90000000134ea530f085e71b6e7bea8c4000141e2ef0c504fb10683fe94ee330a59c12c00000eca5842ea85ea8f2084a3ec0f664d41740a4912f2799961a7870ee02dc819e411a120295836226500005b1a8f29518dfc0000afe35f800092d9c72980105a92c000054c959a0000a7a8d69150000055027f0e1a000214600018ea2fa05ee8139824766033a1c904aa6dc9c908e79ff83a5a61415e07bc4e68f6491e9e86175252438121ea997110e3ef082c41e1de6a270000a559a0ea6300003dd0000a449b6a8f800005ea14e400000000001de09a20000000000000007c400004ac5b28000415800088f800084ba2b0a3284e413227d4522800000023d46358892000169e3640000076a90651d1b3c9e928ce2768c6000000004ff8e3290200007968a9e4a2806200000009a60b8200f18102cb04d05f71a8c37919508f595ce5601ce285406aa1741b4e4d884162d706e82b128de3ce11c000e830202f0000000000061a25d81f323f631923224b003361571b98a5b948435aa36430600ae2e018500269e8293e20fa628a3aa98e8eb669b0daa31a00001449ef065391282a408485ca035c7ec8eea51a852e8c102b225192fc0c28000a11000000000009881406000098e000160e74aa4e03dc946232588f21362876762962ea3b032244d2004662929c80800000000000439205023d00000001cbc5d6202c00000000000c061cc01c63030b3c0000bdea0c11dc94c9f1c5309b24851272ca3f00003458d1e1e602e027898447a59f1a03f11f01309ada00322403f823608fe20fc50027381e69eb413ea866175a09e5eb18c8784087e11fa96a2daa88a1be0e8051c137872193c01831df606305fe8191c1825b890280b85bc1559e048e58f0299081fa5d4967e64322d01cd85382aa9d1a18382ae000000051e0a7490186589371ae2a220000000039614d1f2e57980004c509780e813d88c6173482f95bc41b80004a027b63600000000136e944277a00016c0000000060480009ca9ce400000000000172a38128c0000c7e00001e20001cc243e089e00021de000000097380003e60e280b6901c68c1ba469e27ca2db1a623358c9c21b8
  | 37 => 0x20a00a6800000000006850142000275c44b25880002954000000000013bc81f000000000006f880008ba94de000000067787ea00000dc3be8000000246e000048c59691c290794c878203a820509cc846820032f80c215518043ad1a9833b8508122000065d13c40000000215a4746c802fa6f7878a2f001ac58d157081e8000a0aa7700001f5228e800092aa0c68af977c4be800042b8510395290218802fc08414307f09a6a34a9d343e123a613502aa9bc26e200000005aba31013c978c8489a9e16324904329e460000d28035283a0000000000000040300001969b063de99687fe80000f88000000081a7f78000000000000000000000000280000000000000000fba0889b0c061000000000009369ef255222d605e0bae2ca17643cf214c00000007470e907d682f447da3c6138898a8a09f9236506ec3cd000022580006e6800078a00002da08020001a0800029b69061a720b606ee58aa9803508aae0000e2e83d0c983b693ba834112a2a28000000000000025be000000000000509b6186e00000009c51f32a5f182e00012b67c4a18e00019be9cf83a4000000091e1ba03e983da0000000117213c0000000061800000000003d2012c2bd00000000d1051905e8000030860680004ed08ec714933a01f9fe2000175a5cc80000001f74000052a879800001628dc6610000336a234034000000004384b4279e0000000375000087da36e000000015e9bb2837a4044179c027b60e060228cd80001b449eca5fe8cb9e90609800081a02d600024b25c900003e3007801480006a2882e55d1dc208ba51a5559ed60730b1e9a29ebe2e7a212047919a086993010c888c2b815b029b812097407a68bd12a45a9984a6fc82aca59147c523999c99b8d82899166e6f9a0982541c4e7d319b021917c021880e42dea8a49d818c237e8cd23a395a24dd0b7674b85c299213de29d939e0000c904da160664d192000023986251dce4b6827a3af0140a6715d24e9a7fa9968000000000061e25ec0001d1242c83f2000000085a93aa0431eaa34d096600000004b500002cc27ba1f50e4a6de0a0c2c099e00001a74142901279fa2a847f993e2b191d498d8e0e7b7804e3f6134a39b89e898f99065ef135479c815003a95dc991102c50d27e80aa0b8c19427ec7f604440f31158a39800055d8000883826e9be90660ae14d489e80006d090d0288a0100001428000117a301280ea48917c671a35e7370bfa8f0076c5621cf01b7824c000000000019c833405ae4590720000000000015c80000000736000078980009ef80008ff127c769000062194ae249a9781d4a7d28050a3843b19982791d200b423fe48f980072d96a43bb22f692e10162d3991c73f24240000fac0000cf01d51f260f422a6a1508c679d8bf291896ea4759fd44370ef200000000000000
  | 38 => 0x219a1f0a00000004fa24ce198056c35d96aa1e4058a04507280000bd80441c9c3e71318a0180002b318fa000000059615683f11c2a99d0000000000005d28c07f922f28dd9cfe2812500329800000027300000000000291e000063268fa3a20000000921000000000001c5800000000008d620f000026e800000001710000098800023a9d9e7b81fa687e800041900000000000000013a421808665724361b8a55218e862815f246c0000e3e59e00005fb08fe00003f67baa51680695aea2581ae3fc80004231cc055b273600000000001afc00028b44908de663e148600000004b302ba00007ca8288a4a1b09bdc825a880000000031027460658b422b8a17a0001120000000025f800099e000000182a020100003ca80002548000817800000018424a980006b819f8133291c79d000056c8000a298000000080a94c000000023e80001adc6afa43400024c65ffa8fa000119e88e203e000000080889ac00000006d48f5670d02e645b8eaa9778ba4000209c00017da503016c4c6887416580007979cec009089473e8dfe00017860001f8800001fc000132a00000008d029747b196b2595a72e09c918c0dd940224d0972a4f137a00006fa57b13a0000130400028144ec1cba000000000026341c99c32158a868459a82c067194c8ca15d86c5a2bc66f1600320231e50d80000001a4c0001a1a9878000000067453c000006e01a80001b22000167444217a4a21001c5e680002cd9688000000057f048e35580da2f124d09d117025dc903e000076678d9e54000000084d202859198166150000000041c77100002079b64000074800000003aa11ea000145a3e499240ca27548f6000075fa0702b9a0cc152a43e7e280004d69ca01f88b6e28c1c5600022660000000a658a2c1ad01f06d416dc04f8bb85780bb096a80005890000066a4be3a700006b2201c1d680007d280007e91112a6080006428cac0bf971c52c122a1b100ee82915fa6be00009a31e2e00000000000916000000000013302b2800033f958c0000000a1020800728800000182a622a08c0c3000000009d285780009a08000824950a599125277f000000000003fb1af06c100002cb9fae18b2060277883801c80009978000191800040b9b308c18d1c02f800000020ba415000050b8dc2069180c7861e40110a22a593835a1920000000042a77d06ce8f300000000cfa4ff09f400000003d39ba800000006f10000000124c5a5000096180006aa06b80000000000000042580006d8800006407da0000000000000001b800067e80003bb834e00013ae00025787e08b32000040282a21c889207a07ff806c000172200b820841f11a404a11369ab015290013826fd9fe68130000000000026c88a67688dda236800000015c000028ea000159e00029008d1122496d26ca0000516000
  | 39 => 0x800006209a460c480008b9151a217886664590b661d89aa62a0c3600000001c626949e517ce09d908457b9fd04a1249499c08ee0000000000197e2560ce630c00003e400008bf9518230047213488de2c1970a70e00004ed934c046124800000000001d748601c841f399cc8b01cb07c3000000000000220f5c26707607eb183262fa7a60000844526000000017b000027986c006ae8df084e76e0a0214b00000000000000000061817fa3131ebc00027968aca928574007a76b0000955940417886166241ee4a5200008980000000196283003e473d800064009307b4800010d1d6e6aca29237392c2418800000000005b4000000007ee0001b080520c6e000219c966978252e0000520283600000000001fb0000000000026dc000000000021d66dd929a73302dc0eb04827ab2414033000000000008591eb851784bc2630f0e3f4000070029aa7e4000000000009c800000000000553800000000000000000510a496000083c00000005f5800085000001128000950000000016ec3dfa6f811680440000aea0001c9a00000000a117180000d926ff800033a00000001f783f50000675800024400000000cc0000052278580008dc8000000163ea2880008968fe2000000000000002ce17968240c3897a0dd24d4a24200000003f4a6d234c94e899a00004d5a7b88ae98dc4c30634922018e384800094314e05d322fa59120300001fca197a5142098a1246a1802a219b103029c9276c000099f88842ac1f6602481b269f0bc69fe0ce2a6c9afa51009b69a9800000010205c3a55c18da0e4514093a0eb9ee60000f447b302582f800009d9800044b9c66405133608700000001a766dd295c9f38000095a7828ca80008cda076000000065605800001a44029002086b0b46297051867726620000d02309000065f00000f212f4624800016a98e87a8954c8b100009b1a3b87a700000001edc5eea1ae5b324200001e5c173800000024e2841000000000005e00f3a94800003a603468702464268800083a000056396e80321c7060390ce27fa57497d299e000066e68d8000a3d14c4a030be447b00005fa9fc0000207e9709616399a9ac55603261ec8492000022898987060000000073800001d8dea8f405a20000560623838a3439cde0c900005d8a12400000000f79dd800014ca0b2a6c20001d0072623003e814ec20800000000bc200000003cf93c65730000000000000001bea43000000025c40000986471a65474180005dd00001768fb627503ee03f959634b8000000292e23f00008661f04538a44200017500000000802800065e000000010ba7101f200001c8824a9d309a7800052800002cd191e0000b9636ca16e55497e8986a0ce709081c74b1c5a6c98ed038a864071f201613d111e41d8000000274e000092c00021a072e0c5676707f
  | 40 => 0x3c043800000000007e190cc92b843c0000f2c3e09a048ce8dbc3ff8f5842c10ea6791d364e59aa45c9a2b46a00b1c58f00046e423be30d0e822eda2f00001e70a1a8000a4c1a2434d8d7a5f0987059f1bee27c15f63fc1e487f800004ad281619b20b08c724a6758a99206d18e2107992e616a3460511dd226e923a42511ac5660db874f043e7cd118a5591de42f5226c000000000000000001792000168400005846fc280050f000000000009da1456000280800024c488e993a456a70091c000000000008fa8000133a36a000000041ea73c0001358594269a00000005ce0c947b500000000000000000090e20c8000125600010509f31c74a58a63211b097c6ae00009ea1b5e74c85c64b6010212597904d80f8a7e8000067a90da95ba1d45e800420e50f881e48b1890400008ef19a05ae8a660588a5a00017aa3b195ba84a26e02f49cc812a1ad8893a39496a00003f3832c397097a282060000796623d78c5e7550e3c8d28e4838ea9980f502240bd81e61c512ae6cf8c7066ba02a390112622c83160000fc87d192bc6080a9c2c5029c80087b026480001798cc8a1c81c849910240550686695245e76312620000ba82900fe80d58c2857d0b2496b1aea0000b5a5a805a00000fa400000007f2000000027d659016fc6a09ac64938d481e79dcc44c198c5f215549e3a00e0b78000000295e00018180000f0400013f05fd03a67ff00000b4a4d49c5800000005c007780009679dba118070e45580005dba94468498c02101ab604b8f86921800085623ac05580001c41dfa4f68000575a31a299023a04c09886c3846e86f848493616f232107be28810280168fa23ba245054f9f9c3611e2c1728e5e00d070c58a094a14c99026c28b5881696e43c2a49209a05ac8800ce40000ca0940a3f2939a55a97880000002724934877407e0a1a8c2083a00001ec8d58cde8df80008f9a39c88600006a114fc74282060faa5940001f8c4868d2c0001dd40001dbe9840000189a4a800000000000eac287192c1d00d6263810362a9121c1400fc69c104643d00a4276000f01f7010628504185a4a15c02e17c400023702e71ba287e023600000006e9800058c0c3c1a419f21b580000001408368881800001269198000000103800016180f38aec345198268780000000c0e70b0000000000035c80009c480000001fb49288b485c514f4085052040aa826172208e45e1276351114e31f0ab4830896418798de25b24a01e19002688a5961040000a0e28a878fa558143028077aa416359917403b0c108fb800025da85e7420000000000000000005871d8e75080007b683586ca16e000000000000922000000000000002f2973623907b62a803521bd800000000000000000a5c8000000048600027f471798c65220000000000000000000001e1e362036450
  | 41 => 0x2219521698000000000000010528728ef00000000000000000024f66658000000271e706949c0e10af24cf800031b0936a451a0062b8000000000062796988e407c81a78e2c0001862000059e0001218000000000000002260c7a9e180f256422c602413121f9055e0ee87967539ec22698a0e9238c2000000000e328e49db00568b2a3d27e514100d41ef653395de7bd249c11e1e8c8ba1334037a3b24b9860a0000e303f589a80b21fa800019f0000033e000000000023a437b80000001c8a00029ba9f80000000122e000000000013884d790260000b0a32280000001e3000019ac337058e04f206e91221b83c4000073a12500dc1504898a7e617300000dc8caea06a7c48730ce084e104234f220400000e86740b6200000008a68876128049808a8bcc93c221a000000000000007e780000001d7a710891800011b0000280294e0000701204200009be39e17d45790e9e769800000018e61a00a3c06610ac0e88470089869c48980003079ab45061bf44e5132c153a03400008f8a699380000000091f90323e026220001bb6000156e076000000009b80000000000067e03100002a980005768df09ca00009fb84da2a202c200010e018111aa00015941ca8c740001af61eb15e29330d9800000000ba000098b800004ca0ee1b700000000db000002b088a1a0c35e25d20001a0a0000000975000015a20ae427055a61c80000359b0254e190802000005e78dde00003782af0ff43df12dc000087c0000000000024a9f700000000f947669aaca461bda000203a000000019c23846161914a2c23da37102442e60348636816e94a0f460001cb400027f200000009b98000000054067f9c4c0000000401872e000111027716f4a6295340001c9e00024fe12799fc000104c9ef267c000000035b253c0f109406351ce65ff06c8963800032f1d445950000000000029a8d080000778000045200020dc9d2a3540fc18b89731ca42421e202bb9d8200011fc3a2172e65aa0a689d8faa1c108d48fc22502dc094e1fa29a29de206c94727505d3a278326821600000007a014fe00008a420d83e810e8000000000073e2966000119230215ac61980000001b3a66e87b4019000022b80008fd260e4918054702811a31723c20001c0657080008d31aca18aa50a8c98454000227c00020da7800000612150c47e000000013b800008d06599d2426580009261c8c2e2800066986b61af0000454800029f9bfa0000f2641000002d784f6000191a69590c0000058800026d08c093dc7fd1b3664c834446d0dec270916c54b11b6a3613868d40b9227129a42510b844a8985c9f40000404077c113000096c807c51a0ed489aa788233286e42913322b69fce36e873a00005be5a6838219f043675c90f282697f879300007849e9a08080009fa97ae00008d200023
  | 42 => 0x7fc5439a664d1000066d168a5f303141e89ce000022b8a1080000001e982c3a29c9c40ede9110638000096849c00003aea24a00014a88b99b5c9a800f8000277ea3681f415d80007b883fc9720c2a43f0f52557800024e000083e00004f3926070300000001cd205f800000000000000d248ce03100000000247a0005ae00009c884ea8658c1a49a9b5a0e21d046269cd62fa800000014a2000009e1138000000165e0790e5a00015b4000161e0001ad65518e9aa3a00003f2a288320800047600000000e6a00000000000980a26a0fe01226609bf853e5ad860672c80000001fcc5e612f844f20560ba814a24f0000000000000002960001828129052800000006ee21ba3b38000000075099600140000000002000005c00002c496869e800002ff95a439c041a888000014c1a7a77780009c200c00591bfc1fb08ca9b521ec7868000000166847c99920000f2200018ba95a89ee2430ef800000003eca5f6000000041b000000000001cc8000a3b800000022d40000000000141c000000071f9fbe00010aa628171200000002858734000216299980000001d5698f114c8b705a8082a45a44026c4895a3ec05f13a400000007fa22f892f000049280009a710fe70d80000001c7a78e84b60f8096a2e412fe8742066000068a00000000001c6a50497d2567000025d02c41a119641e9032a42f97886e202862e684ca00000007fb11a60000afc9d61a8861904f026d0a1035c1d5c0000a9a00000000001aa093c800097825082b792be8b88bf49e0196081499285e500000001048a19000000000003bd157a4a599da3ac889c58086302f8914a00000000001db61619b9279b03fa74a1aec7d8a27091600005ac22224e10f208ee800048428200000028000238a1241a3a1c48c4a00000008e69170159156249a28343fd9c1e00004ee56da8be0000000315024e56102b67bb8000000152e0001b9ca500f5a70b864e00002a69bba27200006d200003c61d31310441000000018c461d1f724b586e67d3989c58492360000000000151462600005a0a1b20000c760001ec8051876a7d79c941b810e800002be09910b46e01fee6fa0000000000033f0c3a2a889828a4063ca278d5a6e28b3e460a9580000df2087a60a9f9000072080005d50000994850e675042895c00000000000000085c3ed0f308060000a3580006ba0b645b50de8221a00600000008520a28520a8b80001c1400000000001604798970838d9bac32ca9b49928238811054203d0b4c95b02320000c46000279a660000021680d885f93f20000000a4c842267da2eca170000204000000021aa3149a58000046a343003683aa1a80000cce436047400023200001eca60e80000001b1439f8000678800076580000001b347e000000000da00000a36000000000e00000bca5ca00008f03
  | 43 => 0x8098000000246aa06000048800000000ad00000000000116a0d00040499951e97992123a309e60000fc06f4832009489d80000a3420c970c00026da745800036b030e592186c7c509848840c5888c1be064e12b00001a962f9a44e7d410049811184000144ea538b2a000131c300a046191287400000009c70000000079c00024ac95e800000000001f0248a7701c3a286006602384209c09f9865c00007f7000087080004641d505fc000080e15b8a45800008f999a8651c0800000005db11244a19d46993100a9479e6a0d7a366423949a371811200027d81a99dd61d89d6475812c66b107a89209c646a5130282da3622400592391a5645970b7c420151ca0791f48150df870818aaa668cf21ea90bc8f912de22a245c73c9bd62ae297e8c5174221a9c2264886cc16d204a127020c53027c8a1387b83a523dc08c0da65599a2093a113e6c719c28ab06949ae8a806af17be4bb8a0a11a240c6bba3820cf051a2450bce71e0e4c60e283e10006725cea58083c929091c82f8118922887f974865d95a62a3130e9e894ba00000007611a0284a800064f1d680001a7e54219a490a00e02d2a5ee8809f9a1948b0c1e0a53e09791467ac9fea40f26240338bbe09fa8123f3129e00000004b48b10000000068a0fee51b25b81951e4e6291f689d680000001cbe99017e03449bca1b68e3442400001dba8b200022b600000000000000000000010b091a60f2468000000047800000230000750000078387703e3a0081bc26f42ff07580da915e1fd85945f9895c51506d89ad81b04dc05ec7d0a7b4000084c67b0b8677e25449a480000000fb83cb98e40001fb89b00ea63da0000000000085e1a645c113269c6800083585b066d840c9c18c782a481e03808000000000076d05481ba9b1286980005118da80000332000210687100000560c26483a2060000db6a4a848a9c280003b980007648f4a64a940a57f869299aa21c27aa29668ca126551227e18090580001dda00028e200000002448000012872c205a0b833d933862f1b2e0ef936677f828c873800094100000000000000047c6b40da47bb00004bc208600f80003b017de41715869ce80005e98d5044e81c23cca7e200c16361cf28820000c120f994dc86191440c7287c1a88948a1b0000485800099392540000000000239259090744aa000086680007d911cc0000efe68ba4fa10206a4000000043c232c4c881084800df66f500ba00003803d885e08ea0000994250607f80b60000000617a1ee00000007db94d658805ba8a6014c9858e50820823c47485f2782801a29228c8756a82800022d20000000000054c0001c2800029089d00e227e382668c380006ab80003781dec2b71ab028aa0788b69f0281a8000000199063628ae298a3b642e262c00007885d199d25de13d4a2605f80002
  | 44 => 0x54da4562568b7e0000574341800e97008dc68e03aa00006ac000000084e80005949b9e1d5a1da7b101c46df1d3e476a13e6d827ae25c00227d81d5e41a91625ab0504953187a004a0aa4c827b06ef09e0185009c6b48546a4120243b2919c2ab05fc6578000505230c3ca125a63b8e769aaa69619d8a6c2039eae00021125d2957800000004f316bc592800019e00a241810a2000171e32c00007a4a42c00005b85bea4309a4241a000000000000002ac9bbe4d0892060280968850000250800000002ce000000071226be5b98ba20001a686d3276a4daa6b452300fa28794ea86d869621e0ad22ec861c29121140a4205c35291187910d869bb0d742c88a3e000287a9aa00003548d6021180008569e9e89a000091198b4000216c000039805a9b321d70ad66bf80007340c2e00000000001d704a20368062a936477800082d000068600000000c321d7a17200000005ed0e582e2260890b8b0400000000000a5800016963c0191290e82f000000003500000000071e166198e4128b0076a0c440000000258065c0001c9635180000001e140000a7200980000d30000000000024b827000000000b3000096e822000000005ee15ea704087087f00003f7000020908684358000000101e5c004049279c5c960a45200004307809db286c0efc6c60a685fda938000047a00016702ae80000001f440f70000000000000025bc4ae8abe000000076200c6000029e1849f7e832a1601381d9017e82346d9a26e1028000000251813e10182e504243f90000363000000015ca64d9df0445153c86d0000a51849a571a86237200001a6266448228fe62d8aa8000053600018ce6d580006f192e80001e0c00016c200000823db80000000cca2a5187e0002136000000023e800041100006b900007891f7000005029ac80000ec21920000a7c4e3800000027aa82219e8000143a000000071412148918bb44fe89a4000000000000006d2800005380006f000000001a42a46800000018ec9699a1072381d20000d543b700000001b941d1800071d878c06884de93792ac4f29d784a49f2c38607fc1e391e41101bc804d9f000f2864c31c94445d70ca82b088306a880004fd1fc412ca432000000055080005cc17d88b2100063f960c3b883f446599ce2d11ad42d8183e97e8ad82ba059a88ba10a6d188605c81f1e98600001250a5e74e0300000000000007769c9949664619ee66c98a600000000000d2295288ce12e01921fc173c12898b26b3800000000007d0250e0c6000000013ac3c4a8045aa000000002d46729bc278e000aa6a039201d0768000000052415f06b0857e6981160000000089d0f246230fbe3a28af07479eb60000000000276e000217606227da00014b600025986ea8000000000084c151000000004a087e600000000e7000043b8000
  | 45 => 0x21b2a95251800000000000a2e8000000000040e80004d0000063d188452f1ee800009a05ed971a34822dea61177a3658bf83910000000000075f0d9e46f99422740bf06fa800085d111c6d6042e04011482d4a70e5b786100001fd266787640000176000122c51f99560000822000134600022580001b8c05711220001efe2a18664964041465001ee9b7a1d28409e3234c1a5a413a1e219980004dd96b40000b1a0b880000001f38465082885580008cd1ea40000b8e508930037319541f4982274601bc0001a8e51c8000000000077280001779d6695d800000000000000e1c39b26f2000167620a98ac1c280007f59c264db0954633059c92300a064403b462213be0af1a863d5056a12fa4d666217ee3c59f7c16c800000000005b3944ca1e000032a800000000005dc0c3e72a84265c580002be9f246a7181c8e300004a51f5c28c8000a6e000058980006130f1a3ae0d2650a84dc42615be94d23de8641d0ea6500004279f0e35a10727189cee2f40d189719cae534800000584806f40f707d592a013f28f60001a52835000049f9e4a7fc80008bf1458632a8708d080007fc00b05fc9a4a02a04e85091b86000196c24f80b200c8bf694480847e59c588349fa23a1a37a68f08e2a438cb62201c121aa0b1661f139204e2480257932e8de25da4b2a79c0d0855273d10e20de8fea081218449e059015ca9885c1a81c5e8a3e295f12743b59c806d027f04d7026000026ce17d94d887a11a077a15e874316a226ba10000000005bd92307ca836e1bc83d28859372160825a39081941c700947940c480001e527aa110a1cf9bcc9eb1e580a901a02031672a118bee0df08e09291c160001b543f080001fe0000753168c398a7f60cd1b2a79f20f67a9a6e479820ac703a34ea1480f6000132400000009b325fc91000001f1822c1f0a1a41fe9500902a16800003f809f294aa4b1faa6dc0c920000e0a0000db40569d10000038e8a313e60000168426a6ae000000085f13d06f90000226840e7368d9c95a28f049114f865107023700ac0a1f837400000004df8eae12d08a200000001b196c800002ee52a9a6e0000000384012aa2f2892a3e233e49b282e52908ac00028aa8ed240e119a41c4f81808029885048f1aaa30b228470f12ec422a74c4458f78615915c32e91a22b5039e36f9070a2b10a618b8e6426c015e1bd085840c24ec0cc26a20df88b43878f9a7a507d68c9155c497953a6f399862f699e687c260200001d426783d89bf0000968a38000000000000e269a3a98e66509ca00011bc000000004880000000d3a9870a988f28af642a000072a1f7600000002b20000879155a671247c8100000000144a0000e2029312069009eb0000000041f80008d717d0a2526ea8cc00001a680e64e2941600000004ba8ec411426807cc1e7a000
  | 46 => 0x4308a7899d9f226da077a37409f68cc89322e984568632170715070818f900e2de0406506861a3cd81809089a403c30d387ca000000000000e19dae22da8560000000a499af4a330000a4f8d8a0b91328519a1f2000144800029a048e1776950a9340c124ee6ee800089100005b8983400000007908000a4822543e58d4c32d0360843a1f43ff1a9047b800000027c61fd04a600009ec45f8cc60000000310a75639395824aa800094e80009cca67a1692312462197
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8f686dc543440018e8cbb8a86880025d6147150d100063a328e2a1a2000cb5641c5434400155d09996c48800e1fa1b75589100043f43ecab122000c5c73d9562440010fd0e32ac488003171cc65589100061fb2ee8b122000c3c65dd1624400187eca3a2c4880030f19474589100062fb2ee6b122000c5c65dcd62440070fd0fbaac4880022fe1175589100345e422eab1220008df835d562440051b906baac4880023ee0175589100043f438eab122000c3f75dd16244001878ebba2c4880030fdd474589100061e3a8e8b1220028de87dcd62440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd6244001958e9b92c488003331cf72589100066a39ee2b122000c7875dc1624409b8eae2328c4880023be1d621891000556422c43122000acc8358862440191d904b98c488002aba1332189100043fc2aeda12200387c855db42440010ff0abb4848800e1f215769091000c7a432e3212200387e85dd942440010fb0bbb284880021fe15765091001c3e42aeca1220008bf845d942440011bf06bb2848800a3720d765091000477c12eca12200387c859d842440010ff0abb0848800e1f21576109100345e422ec21220008df835d842440051b906bb084880323b20976109100043e432ea212200087f87d9442440010fb0fb2884880063d21971109100365a322e2212200cce4625c4424400f1f10cb8084880021fe15768c91001c3e42aed19220018f4865c632440070fd0bbb264880021f617764c9100043fc2aec992200387c855d9324400117f08bb2648801a2f211764c9100046fc1aec99220008ef825d932440011ef02bb264880062fe1d64905101654e41ac920a2000aac8259241440018b8e7b2a8288003271cf64505100062fb2ee6a0a2000c5c65dcd414404d0f90cba8828801b0f99175105100043fc3eca20a200587d87d94414400117f0eb2082880030f5d5641051012d4e41ac820a2000aac8259041440031bf0eb1c6288156a7211638c51000566412c718a2000c3f65dd13144001878cbba262880030fd94744c5100061e328e898a2025c9c631d13144001938e9b1a62881361f21975c85102643fc3ecb90a200087d87d9721440018b8e7b2a42880030fd9774485100061e32ee890a2000c3f651d12144001878ca3a2428800317d9773485100062e32ee690a2000cac74d892144001998e7b1242880032b1d0624851000666398c490a20018fa86dc121440018f0cbb8242881331d1db65485100065a3b6e890a2000cb4761d121440019a8edb9a4288003351d87348510006ca3a0e690a2000e676518921440015c90c99242880031e1db654c110005e840a86982204aada868c53044001f826490a60881331e9db65c4110
  | 1 => 0x4edb26409001b2e9d864c81200071c328c990240078bc8755164c400d17d09b92c7880022f6137258f1000c7a40aeca1e20078bc8759143c400553906b22878801f2d1c56450f1006637902eb3162000c6d205d662c400f17f0eb24858801f2d9c56490b100361f322ea2162000c3d7559042c400f1d90eb12658800335dd87348710006ca3a0e690e2000a3e8418f654400147b0831eca880030f5d074d95100051fc22e7b2a2000a3c845cf654400147d0839eca880028f61073d95100062eb98e7b2a204ca7a801cf65440014f30039eca880028fe1172d95100051e422e5b2a2000c6d721cb65440934ed02396ca881329d60472d95100051f42665b2a2000a3d84ccb65440010fd0e196ca880021f61c32d95100043f43863b2a200587d870c7654400147d0818eca880028f61031d95100053741063b2a2000a6d820c765440994f50018eca880021fa1f65591100062e39ecab22200087e8719564440018b8e632ac88800317d9773591100062e32ee6b222000c6f65dc964440018d8cbb92c8880031bd94725911000636328e4b22200387e87dd564440011bf06baac88800a3720d755911000477c12eab22200c8ec825d564440010fd0e3aac88800f0f1d6545911041e4e39ca8b2220038bc875516444105938e6aa2c88800a37a1f73591100062fbaee6b222000c5c75dcd64440018beea39ac888003171d473591100064fba0e6b222000c6f75dc964440018d8ebb92c88800333dcf72591100066639ee4b222000c6f751c964440018d8ea392c8880032bdd0725911000667b98e4b222000ccc731c9644400195ca8392c8880032b55072591100045fc3ac83222000a9c83590644400155904b20c8880022fe1172d8d100345e422e5b1a200087e87d9563440010fd0e32ac6880030fd977458d100061e32ee8b1a2000c3f651d16344001878ca3a2c6880032718c7458d1000637b2ee4b1a2000c6c65dc963440018deca392c6880031b1947258d1000666318e4b1a200387e87dd5634400117f08baac68801a2f2117558d1000477c12eab1a200c8ec825d563440010fd0e3aac68801a2fa1f7458d100061fbaee8b1a2000c3c75dd1634400187eea3a2c6880030f1d47458d100064e3a6e6b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c9634400199862392c688003391cb7158d100145f424eda1a200087f855db43440070f90abb686880022fe1d64d0d100154e41ac9a1a2000aac8259343440070fd0bbb286880021f6177650d100043fc2aeca1a200387c855d9434400117f08bb2868800237e0d7650d1000477c12eca1a200c8ec825d943440051790eb22868800aa720d6450d1000556412c8a1a2001
  | 2 => 0x47158d200063a3a8e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a400087f855db43480070f90abb6869000a2f21176d0d2001c3f42eeca1a400087d85dd943480010ff0abb2869000e1f2157650d200045fc22eca1a40008f7815d9434800f1e902bb2869000a2fa1f6450d200154f41ec8a1a403bcb870d9142480018f0cbb8284900da1f21975109200361e322ea212400087f87d9442480170fb0fb2884900030f9d764109200061ebaec82124000ae5820c761480015e30018ec2900030fd9674985200061e32ce930a4000c3f655d26148001878caba4c2900030f9d764985200061ebaec930a4000c3e75192614800187aea324c29000e1fa1b75585200043f43ecab0a4000c5c73d9561480010fd0e32ac290003171cc65585200061fb2ee8b0a4000c3c65dd1614800187eca3a2c2900030f19474585200045f43ec8b0a4000c3f75d916148001878ebb22c290003271cf64585200045f438c8b0a4000c3f751916148001878ea322c290003271cc645852042657b90c8b0a4000c5f65dcd61480018b8cbb9ac29000327d9373585200064e326e6b0a40008f78758461480015a906b08c2900022fe1173185200345e422e630a40078f4815cc61480010ff0abb6829000e1f21576d052003c5e422eda0a400087f855da41480070f90abb4829000e1fa1776505200043ec2eeca0a40028de839d941480011bb073b28290003171cf65505200064e39ec8a0a4000c5f65dcd41480018b8cbb9a829000327d9373505202ae4e326e6a0a400387c859d841480010ff0abb0829000e1f21576105200043e432ea20a4006c3c645d441480010ff0fb2882900021f61f65105200061f3aec820a4000c3d75d90414800d958c939082900063b219721052003656322e420a400087f855da31480070f90abb462900022fe11768c5200345e422ed18a400387e85dd931480010fb0bbb2629001a2fa13764c5200045ec26ec98a40068be849d9314800117b093b262900022fa1b744c5200061fb2ee898a4000c3c65dd1314800117d0c3a262900030fd94744c5200061e328e898a40008be87d9131480011790fb2262900022fa1c644c5200345e438c898a401887c865d721480010ff0fb2e429002e1f61f65c85200061f3aec990a4000c3d75d93214800187cea32642900030f5d464c85200062e39eca90a40348be86dd1214800187ecbba242900030f19774485201dc5f430e890a4000c3f651d12148001878ca3a242900022fa1f64485201dc5e43ec890a4000c9c73d91214800117d0e322429001a2f21c64485200064e398c890a4000c5f65dcd21480018b8cbb9a429000327d9373485200064e326e690a4000cd473d8521480019a8e630a42900031e197704852029e3d3b6cb9024053e6b62d97204807797
  | 3 => 0x3b2a4000c3d75d53644800155b05aa6c89000f0f1d654d912001c5fc3aa9b224088e2d82197644800147d0b31ec8900028f61663d91200071632ca5b22403baac8654b644800187aea3aec890002a7a0c75d91200054ec18ebb224000aae821d7644807755b043aec89000327dce73d91200045f43ea7b2240008bd87d4f6448001c3ea729ec8900ee2fa1f52d91200045ec3ea5b224000e2f5294b644807717d0f996c8900022f61f32d91200051f42865b224000a3d850cb644800153d07b8ec890002a760f71d91200051f42ce3b224000a3d859c7644800117d0e28ec8900022f61c51d91200045f43863b2240008bd870c7644800147d0a18ec8900028f61431d91200055741063b224000aad820c764480775750018ec890002ae60031d91200361e322eb3224000c3e75d92644800187aebb24c8900021fa1f65591200043f438cab22408cc6f7219564480070fd0fbaac8900022fe11755912000477c12eab2240008fb805d564480010fd0e3aac8900030fdd774591200061e3aee8b224000c6c75dc964480018f0ebb82c8900022fe1d64191200051fc2ac83224000a3c85590644811787cedb28c8900022f61e651912042d1f42cca32240008bf87594644811555f04b28c8902268fa1865191204461f3b0ca3224087e2d82194644810fc5c40328c89021f8b080651912043f1c100ca3224000a3e8598c644800147b0b318c89021aab60a631912042d57434a43224000e2c6594864480695590ca90c8900038b19552191200345f43ea632240008bd87d4c6448001c3ea7298c890002aba08531912000556c10a632240068be87d48644800117b0fa90c8900038bd4a52191200055dc02a43224034ab8805486448001c5aa4290c89001a2fa1f32191200045ec3e643224000a3e850c8644800147b0a190c890002aba0b511912000556c16a232240068be87144644800117b0e288c89001a2fa1c31191200045ec38623224000a3e850c4644800147b0a188c890002aba08311912000556c10623224034aba800c4644800157300188c8900021fa1f6558d200043f438cab1a4000c3f65dd16348001878cbba2c6900030fd947458d200061e328e8b1a40008be87d91634800187eebb22c6900030f1d76458d200045f438c8b1a4000c3f751916348001878ea322c6900031dd977158d200063a32ee2b1a4000cb764dc56348001968c9b8ac6900031dd947158d200063a328e2b1a4000cb7641c56348001968c838ac6900033518c7158d2001c3f43eeab1a40008bf845d5634800d17908baac6900023de057558d2003c7a40aeab1a400087e871d5634800d17d0fba2c6900030fdd77458d200061e3aee8b1a4000c3f751d16348001878ea3a2c6900031ddd77158d200063a3aee2b1a4000cb774dc56348001968e9b8ac6900031ddd
  | 4 => 0x15000d179083b262a00062fa1b744c54000c5e432e990a80018be86dd2215000195ee831442a000a37a0e76485400046ec1cec90a80068bc841d9215000317d0dba242a00021fe15760854001c3e42aec10a80018bc865d02150019958c4ba042a00333a189700854001c5fc3aa9b226006c3c645d6644c00187aebb24c8980023be09755913006476412eab2260008f7815d5644c00f1e902baac8980022fe1d6419130004aec28e2a1a60019da801c5434c0051f301baec4980021fe1571d893001c3e42ae3b1260008ef87588624c0015c902b10c4980331bc81751893000636902ea31260008bf845c4624c00d17908b88c498003350c5711893000c6e432e7a12600087f855da424c0070f90abb48498006372197390930014cfc3a872126006a9c8650e424c00193ceca1c849801b0f19175109300061ebaec821260018dc865cc424c00d938c8b98849801aa721943109300647c432e02126000d99435c0424c0031b90cba2649800275205744c93000ced400e29926000dd2101c5324c0031bb07baec2980023de1d611853000572412c230a60008bf845c8614c00d17908b90c2980063721973d053012ccfc3a87a0a600087f855da414c0070f90abb4829801e3e21970905300146e418eca0a60018de86dcd414c0053390ea1a8298003271d94350530005ca40a86a0a6006c3c645d4414c001a3c86ba882980030f5d7641053000c6e432e620a60078f8865c0414c0031bd0dba4629800267e11728c5300246ec3ec318a60018dc865cf214c0031bd0db9c429801e3e21970885300345f424ec90a60008bd849d9214c0051b9063b2429800637a1b7348530014e643a6490a6000ccc764c9214c0010ff0abb0429800e1f21576085300045fc22ec10a60068bc845d8214c0031b90cb98429801f35185730853003c7c432e010a600cce8625c0214c00717f0eaa6c99000a2f21176d0f200047bc0aeca1e40078f4815d943c800517d0fb22879000aa7a0f6450f200045fc22eab0e40068bc845d561c80011bf06baac39000a3720d75587200146f43ee6b0e4000c9f74dcd61c8001938e9b9ac39000327dd073587200064e3a0e6b0e40008bf845d941c80011bf06bb2839000a3720d76507200345e422ec20e4006c3c645d441c800187aebb20839001b2b19172107200045fc22ed18e40068bc845da31c800117f08bb2639001a2f211764c7200046fc1aec98e4000a3e8498f654800147b0931eca900030f5d074d95200051fc22e7b2a4000a3c845cf65480018bae639eca900028fa1332d95200051ec2665b2a400087e870cb65480170fb0e196ca900028fa1271d95200051ec24e3b2a400087e870c765480010fb0e18eca900028fa1031d95200051ec2063b2a4000a6e820c765480014db0418eca9014e9ea0031d95200053cc006
  | 5 => 0x31bdca72597400053dc02e4b2e806aa78805c965d00018dae4392cba001a8fa1332597400051ec2664b2e800087e870c965d00010fb0e192cba019a8fe1171597400351e422e2b2e8000a5f835c565d00014b906b8acba001a8fa10715974009d1ec20e2b2e800087e870c565d00010fb0e18acba001a8fa1031597400051ec2062b2e8000a6e820c565d00014db0418acba01aa9ea0031597400053cc0062b2e80028bd84dc963d000127b0a38a87a00022fe1d5498b400045fc3a873168002c9e7350e62d00070fd0bb8ac5a00021f6177158b400361f3a2cb1968000c3d655d232d000317d09bb265a00022fe19744cb40004da40ae899680018bc845d561d00011bf06baac3a000a3720d75587400045e43aa8b0e8003c3e7555161d0105938e6aa2c3a000a37a1f73587402ae4e3a6e6b0e8075c9c741cd61d00011790ea1ac3a000b271cd43587400055a40a86b0e802ca9c835da41d005917f0cb9c83a00022f61e629074000c5fc3ac320e802ca9c8358641d000317908bb463a00b22fe11764c74000c5e422ec98e80558df835d931d000d878e8b2a63a00030f997744c7400061eb2ee898e800387e855db21d00010ff0cbae43a00021fe1d65c87400043ec3acb90e80018bc845da21d000117b0dba443a00022fe11764874000c5e422ec90e80008df835d921d00051b906bb243a001b0f1d165487400062e39aca90e8000c3e65dd121d000187acbba243a00031799773487400062eb2ee690e8006c3e7459421d000187acaba043a000a2f21172d8d401a45f436e4a1a800093d851c543500018daeba96c4a0002ab61352d89400043fc2ae3b12800387c855c762500011df0eb10c4a00029b215621894046d57c22c4312800c8ec825d462500198d904ba8c4a00331bc81751894000636902ea31280008bd87950625000787ceb2a0c4a0002ab60a541894001e1f3aaa83128000aaf82550625000117b0fa18c4a0002ab60b431894000636baea43128000aad84d486250001c5aa9a90c4a000237e0d71189400146e41ae2312800caae86d89425000155d0e31284a00332ba1c625094006717428c4a12800ce2d85189425000195ee631284a00032b18871509400043fc2aed192800387c855da32500191d904bb464a00062f219748c94006656312e919280018bc865d1325000136902ba264a000a3ba1f624c94000656ba0c499280018bd84dd7615000117b0f2a6c2a00022f61f43d854012c5fc3a87b0a80008f78758461500691790cb9482a00030f98d75105400061e31aea20a8006c3f605d4415000da76c0ba882a00962f21973105400045ec38c420a8000c3d75188415000195ae431082a0002ad60462105400061ebaec220a800087f855da31500070f90abb462a00023be09768c54006476412ed18a80018be86dd23
  | 6 => 0x52ec28c831a4200a9e86190634840193cec320c69080387a146418d210070ec28c831a4200e1e751906348401c3aea320c690803a35c86418d210054f424c031a4200a9d84980634840517908bb686908022fe117650d210047bc0aeca1a420387e851d943484010fb0a3b2869080a2fa1f6450d210346f43ec6a1a4206cb4649c742484019a8c7b8a84908032dd9071509210066a318e2a124206c3c645d442484018b8c6ba884908030f9d764109210061ebaec82124200c5e75d8c42484018baebb18849081aab21942109210074631ec91924200e8c63192324840559d0db1c6490803339db638c9210065a326e29924200cb4641c532484019aec638a64908032b1db644c921006563b0c89924202ccc76dcd3248435998edb1a649080371dcc714c92103656324e5a0a420387e859da41484010fb0b3b4829080237e0d76505210146e41aeca0a4200c9c73d9141484011bd0db9a829080327d9373505212ae4e326e6a0a42758de87d8d41484ab1b90fb1a82908032bd9072505210361e322ea20a4200c5c635d4414840187cebb2082908030f5d764105210062f3aec620a4200c5d75d8c414840d5690ca0882909bba518d41105210fe673b46518a42008be86dd13148459938c7ba262908022fa18744c52112e4e318e898a42258be87d9131484591790fb2262908b22fa1c644c5210345e438c898a4200e9431191314840193ee9b1a6290803271d3634c52100667b18e498a4200c5c635d72148419ac842bae42908030f9d764c85210061ebaec990a4200c3e75193214840187aea3264290803179d763c85210062ebaec790a4200e946418f214840117d0fb22c0908030fdd764581210061e3aec8b024200c9c73d91604840117d0e322c0908030fdd464581210061e3a8c8b024200c9c7319160484351b90db9ac09080327d9373581210064e326e6b0242008de87d8d60484018beebb1ac090803171d763581210064fba6c6b024200c9c74d8d60484011bd0e31ac09080317dd463581210062e3a8c6b024200c9f7418d6048401938e831ac0908021fe1570d902101c3e42ae1b2042078bc8755164084010ff0ab86c61080e1f21570d8c2103c6e43aa6b1842078f4815d9430840f1790eb22861081f2d1c56450c2103c6e43ac6a184207cd47158d430840f9cca3bb2421080339547764842100657bb6e89084200caf761d1210840199eedb9a421080333dd8734842106673296ec9084200ce552dd9210840196eedba242108032ddd874484210066bbb6e69084200cd7761cd2108401b28e839a421080e1fa1f75580210043f438eab0042078f887541600840d47d09b9acba004e8f61373597400351f424e6b2e8068a3d849cd65d00018bee739acba001a8fa13725974009d1ec26e4b2e8006a3e849c965d00cf47b09392cba
  | 7 => 0x1f5394c644840155d04298c890802ab60853191210345f43ea432242008bd87d486448401c5ea5290c89081a2fa1f32191210045ec3e643224200a3e850c8644840147b0a190c890802aba0b511912100556c16a232242068be87144644840117b0e288c89081a2fa1c31191210045ec38623224200a3e850c4644840147b0a188c890802aba0831191210055d400623224200ab9800c4644840d17d0e280c8908022f61c50191210054f418a03224200a9d83140644840155d04280c890802ab60850191210055b408a03224200ab581140644840147d0b980c8908028f617301912100557416603224200aad82cc0644840156d03180c890802ad60630191210345f4386032242008bd870c0644840d17d0e100c8908028fa1420191210051ec28403224200a9e83080644840153b06100c890802ada0420191210045ec3c203224200a9e83840644840153b07080c890803175d753d8d210054f426a7b1a4200a9d84d4f63484071bf0ea9ec6908021fe1570d8d2101c3e42ae1b1a4200a9e84997634840153b0932ec690802a7e1165d8d210054e422cbb1a4200adb8059763484015b100b2ec69080297a1464d8d210052ec28c9b1a4200e1e851936348401c3b0a326c690802a7a1260d8d210054ec24c1b1a4200c5d751d7634840153d083aec690802a761075d8d210052f428e9b1a4200a5d851d36348401c3ea92a6c690802a7e1172d8d210054e422e5b1a4200a9e84d4b634840153b09a96c69080393d4a52d8d210052f42ee3b1a4200a5d85dc7634840153d09b8ec690802a761371d8d210072ba8ca3b1a4200a9e84147634840153b0828ec690802a7a1270d8d210054ec24e1b1a4200a5f855c363484014b90ab86c690802b5a0470d8d210056ac08e1b1a42008de8714363484011bb0e286c690802a7a1050d8d210054ec20a1b1a4200ace82143634840159b04286c690802b5a0450d8d210056ac08a1b1a42008de8710363484011bb0e206c69080237a1c20d8d210d46ec3841b1a4200a5e8508363484014bb0a106c690802a7a1020d8d210054ec2041b1a4200ad68108363484011bb0f086c690802a7a1210d8d210054ec2421b1a4200c9c63dd16348401938c63a2c6908022fa1f6458d210045f438c8b1a42008bf845d5634840d17908baac69080237e0d7558d210047dc02eab1a42018f8805d5634840d17d0fba2c69080327dd37358d210064e3a6e6b1a4200cb474dc563484011bb0f328c690802a7a126518d210054ec24ca31a4200acd8299463484015ab03328c69080237e1d6518d210054fc22ca31a4200a9c8459463484015b700b28c690802b62016518d210064f3b6c831a4200e1e75d906348401c3aebb20c690803a35cb6418d210046ec3cc831a4200a9e8499063484011bf0eb20c69080297a146418d210
  | 8 => 0x84b2a85908031bdd9654cb211654f41ec920e4200c5c7359541c84198d8e4b2a8390803271cd64507210062f32ee6a0e4200c5d65dcd41c84018dacbb92839089a1fe1975107210361e322ea20e421887f8759441c840117b0fb2083908030f5d7641072112d4f41ec820e4255a9e84d8e31c843599aed19463908331b1c9654c7210061f32ee898e4200c3d65dd131c840187cca3a263908030f594744c72112e4f318e898e4200c9c7458d31c84018dacbb92639081e2f21d545922101c3f42ee0b24420087d85dc1648840153b06202c91080e1fa177058e210043ec2ee0b1c42078bc87591438840553906b2287108022f61f6410a21006373aaed90c4200c6d765d7218840187aebaa6c89080e2fe1d54d91210043fc2ae1b22420387c855c3644840153d06206c890802a760c40d91210054f41ccbb224200a9d83997644840153f06b2ec890802a720d65d91210055dc02cbb224200ab880597644840147d0a31ec8908028f61463d91210054f41cc1b224200a9d83983644840187aea3aec8908028fa1473d91210051ec28e7b224200aae821cf644840155b0439ec8908022fa1f53d91210045ec3ea7b224200e1f5394f644840117d0fa96c8908022f61f52d912100717a94a5b2242008be87ccb644840117b0f996c8908028fa1432d91210051ec2865b224200a3e85dc7644840147b0bb8ec890802a7a0f71d91210054ec1ee3b224200e3751947644840117d0e28ec8908022f61c51d91210045f43863b2242008bd870c7644840147d0a18ec8908028f61431d91210055741063b224200aba800c764484015730018ec890802a7a0e70d91210054ec1ce1b224200a3f855c364484014790ab86c890802ada0470d91210055ac08e1b2242008be87143644840117b0e286c890802a7a0c50d91210054ec18a1b224200aae82143644840155b04286c890802ada0450d91210055ac08a1b224200a3e85cc3644840147b0b986c8908022fa1c30d91210045ec3861b2242008be87083644840147d0a106c8908028f61420d91210054f41841b224200a9d83083644840156d02106c8908022f61e10d91210054f41c21b224200a9d83843644840193ce7b24c89080327d9173991210364e322e732242008bf845d564484011bf06baac89080a3720d75591210047dc02eab2242018f8805d5644840193ee9b9ac89080327dd073591210066a39ee2b224206c3c645d4644840117f0eb20c890802a7e0d64191210054e41ac83224200c3e769d4644840187cecba8c8908022f61e65191210054f41cca3224200a9d83994644840117f0eb28c890802a7e0d65191210054e41aca3224200abb80594644840157100b28c8908028fa1463191210051ec28c63224200a9e83980644840153b07300c89081a2fa1f53191210045ec3ea63224200e
  | 9 => 0x501913112d4f418a03226200a9d83140644c40155d04280c898802ab60850191310055b408a03226200ab581140644c40d17d0e100c8988022f61c20191310051f428403226200a3d85080644c44b53d06100c898802a760c20191310055b408403226200ab581080644c40d17d0f080c8988022f61e101913112d4f41c203226200a9d83840644c4071df0ea96c4988029b61420d893100566c1841b126200ae581083624c4198d8c4bacc4988030f9d764989310061ebaec93126200c3e75192624c40187aea324c4988031b5d762989310045f43ec8b1262008be87191624c52196ee2322c4988023be1d62189310043fc2ae0312620387c855c0624c40117f08b80c49881a2f21170189310645e422eda126206c3c645d4424c40187cebb2084988030f5d764109310364e322e62126206cb4649c4424c4191e90cb88849881b2d19171109310364e322e7a0a622cc9c73d91414c4ab938c9b9a829881b0f191751053103eaa18aea20a6200c3e75d90414c40187aebb208298a3ea7a1b648c53147e4f388c918a628fe9671192314c40117d0fb22c0988030fdd764581310061e3aec8b0262008be87191604c40187eea322c0988030f1d4645813100657b26e4b026200cac64dc9604c40195ec8392c0988032b19072581310051f424c6b2e4200a3d8498d65c8419c9c6531acb908030fdd274597210051f426e6b2e4200a3d84dcd65c840147d0939acb908028f61273597210062fb9ce6b2e420ca6e829cd65c851d4db0539acb908029ea0273597210053cc04e6b2e420ca6e8290d65c84014db0521acb908028fa1332597210051ec2664b2e4200a3f845c565c840147908b8acb9080297e0d71597210052e41ae2b2e426ca6f825c565c84014f700b8acb908029e20171597210c43f43862b2e420087d870c565c840147d0818acb908028f61031597210653741062b2e4200a6d820c565c84014f50018acb908029e60031597210051f420e0b2e4200a3d841c165c84014bd06382cb908029760c705972106537410e0b2e4218a6d821c165c84314ed02382cb908029d60470597210052f41880b2e4200a5d8310165c84194dd04202cb908029b60840597210043f43e60b2e420087d87cc165c840147d08182cb908028f61030597210653741060b2e4200a6d820c165c840147d09082cb908028f61210597210052f41c20b2e4200a5d8384165c84194dd05082cb908029b60a105972101e1f3aca9b264283c9e7395364c840717f0eaa6c990a0b279cd54d93210645f43c86b26420387e85dc164c84010fb0bb82c99080e1fa177058f210043ec2ee0b1e42028bc845db43c840117b0fb26879080aa7a0f64d0f210646fc3ac7a1e42028be87d9143c840553d07b2287908031d9977150f210063b328e2a1e4200cb7641c543c8419c58
  | 10 => 0xb28820087d87081651040d47d08102ca208028f61020594410052f41840b288200a5d83081651040f4ed02102ca208029d60420594410351f42420b288200a3d8484165104014bd07082ca208029760e10594410345e422eab1882078f4815d563104070fd0bb82c6208021f6177058c410043fc2ae1310820387c855c2621040d17908baac4208023ee01755884100c7c402eab108206cae725da421040187ce6b2c84208030f1cd65908410361f392cb2108206e2e72596421044b17f0eb1c8420897279cd63908410061eb2ae3210823b8bf865c2421040187acab84842081b0f9d1658c8410061eb2ae91908206c3c74595321040f8e8e2b2a64208030f597744c84103c7643ac49908206cac74589321040f9c8e2b1264208031d597714c84103e5b28eeca088200cb551dd9411040187ce6b2a82208030f1cd65504410060e39acaa088207c3f71595411040dc6ee2b2a8220a3e67a1f73504410064fbb6e6a088200e1d65dcd411040193eec39a822080387594735044112c5e43ac6a088225c9c7358d411040f56902b1a82208030f59472504410061eb2ee0a08820087f855c3648c4070f90ab86c91881e2f21d545923147ccfc3ac9a1c622e8df865c7438c40117f08baac51881a2f2117558a310047dc02eab1462018f8805d5628c40193e61ba2c5188b3279cf6490a310365a322e221462029d4835c4428c4abb2e86b88851887637e1d628ca310fc6fc32e3194628f99e87d0d418c45d93eeda1a831880e1fa1f75582310043f438eab046200c3d75d53644c40717f0eaa6c8988021fe1570d913101c3e42ae1b226200a9d83103644c40155d0532ec898802ab60a65d91310061eba8ebb226200a3e859cb644c40147b0b396c8988022fa1f52d91310045ec3ea5b226200e2f5294b644c401c6ea328ec8988022fa1c51d91310045ec38a3b22622ca9e839c3644c40153b07386c8988028fe1570d91310051e42ae1b2262008be87143644c40117b0e286c8988b2a7a0c50d91310054ec18a1b226200aae82143644c40155b04286c898802ada0450d91310055ac08a1b2262008be87083644c40117b0e106c8988028fa1420d91310051ec2841b22622ca9e83083644c40153b06106c898802ada0420d91310055ac0841b22622c8be87843644c40117b0f086c8988b2a7a0e10d91310054ec1c21b2262008bf845d5644c4011bf06baac8988023de0575591310045fc3ac832262008bd87994644c40155d05328c898802ab60a65191310045fc3aca3226292ab781594644c52356b03300c89881a2fa1f52191310045ec3ea43226200e2f52948644c44b53d06290c898802a760c521913112d4f41ea23226200a9d83d44644c40153f06a88c898896a720d51191310345f438a232262008bd87144644c40d17d0e280c8988022f61c
  | 11 => 0x50401caea328ec6a0956a7a1051d8d410054ec20a3b1a8229a9e849c3635040153b09386c6a080297e1570d8d410052e42ae1b1a82008de8714363504011bb0e286c6a0956a7a1050d8d410054ec20a1b1a8200ace82143635040159b04286c6a0802b5a0450d8d410056ac08a1b1a82008de8708363504011bb0e106c6a080297a1420d8d410052ec2841b1a8255a9e84083635040153b08106c6a0802b5a0420d8d410056ac0841b1a82008dd8784363504ab53d09086c6a0802a761210d8d410046ec3cca31a8200a9d84994635040159d05328c6a0802b360a6518d410046fc3aca31a8200a9f8459463504015af02b28c6a0a0ea7a106518d410054f434a831a828fa9e8655063504015390caa0c6a080387d955418d410054ec24c031a8200ad5819806350459938c73b686a080aa7a1b63d0d410064f3b6c7a1a8200cd7631c5435040553d0db1a86a08a7271db6350d413aecbb98e2a1a82009b6861c5435040f96d0c38a86a081f4da147150d4103e9ac28e2a1a8200d97631c5435052fb28c638a86a0a5f65cc07150d4101c77c3aa5b128200a6d85083625040155b08106c4a0802b960420d894106636312eb3128200c5e75d8e62504018baebb1cc4a0803179d463989410062eba8c73128200c6d75d8a62504011bd0fb1ac4a080237a1c635894100477c3ac43128203c3e75550625040156902a18c4a08038b55152189410043fc2ae0312820387c855c062504019a8c7b8a84a08033518c71509410345e432e720a822cc9c635ce415051f53d0db1c82a080f0f9d554d81410164e39a87b028200ab48150f60504531b90db9ac0a080237a1f63581410062fbaec6b028200c5c75d8d60504011bd0e31ac0a080317dd463581410062e3a8c6b028200ccf63dc96050401998c7b92c0a080333d8c725814100666318e4b028206a3e84dcd651044d47b09b9aca2080317dce73594414b51fc22e6b288206a3c845cd651052b4ef02b9aca2081e9d20573594410351f41c86b288206e1e8390d651040147d0521aca208028f60643594410051ec0486b288206a3e84dc9651044d47b09b92ca208031bdca72594414a51fc22e4b288206a3c845c965104014f700b92ca208029e20172594410351f42664b288200a3d84cc965104010fd0e192ca208021f61c32594410351e42064b288206a3c84cc5651040d47d09382ca20a4e8f61270594410351f420e0b288226a3d841c165104014bd06382ca208029760c705944100537410e0b288200a6d821c1651040f4ed02382ca2089a9d60470594410043f43e60b28820087d87cc1651040d47909982ca208038790f30594410351f42460b288200a3d848c1651040f4ed03182ca208029d60630594410351f42060b288200a3d840c1651040d47d09102ca208028f61220594410043f43840
  | 12 => 0x31e5d750d81420351f426e6b288436a3d84dcd651080d47d0939aca211f28f61273594420062fb9ce6b288406a3e84cc9651080147b09992ca211de8fe1171594420351e422e2b288400a5f835c565108014b906b8aca2101a8fa1071594421b51ec20e2b28840087e870c565108010fb0e18aca2101a8fa1031594420051ec2062b28840ca6e820c565108014db0418aca210029ea0031594420053cc0062b288499a3f845c1651080d47908b82ca212629be09705944206536412e0b288406a3e841c1651086d47b08382ca2100297a0c70594420052ec18e0b28840ca6e821c1651086d4db04382ca210029da0470594420053ac08e0b28840087e87cc165108010fb0f982ca2101a8fa1030594420051ec2060b288406a3e84841651080147b09082ca2100297a0e10594420052ec1c20b28840387e85dc163108010fb0bb82c6210024f6147150c42004d6c10e2a18840ccae52dd9421080195aa5bb284210021fe15709844201c3e42ae130884008df835d561108051b906baac22100f0f9d554584424164e39aa8b088400ab48155161108051bd0fb9ac221157271d373584422af4a20ee6b088475c9c741cd61108ebd288239ac22100b271cd43584420055a40a86b0884068bc845d560108691790eaa2c0210d22f21d43580421a45e43a84b008434ab88050960108010ff0ab86c91900e1f21570d92320645e43aa8b24640387e87dd5608c8010fd0e3aac11901a2fa1371582320045ec26e2b046400cd431dc5608c80717f0eaa6c8990021fe1570d913201c3e42ae1b226400a9d83103644c8011ef02baac89901e3d20575591320047dc02eab2264018f8805d5644c80196ee838ac89900335dcc71591320066b980e2b2264008bf87590644c80156902b20c899002ad20564909320045fc3ac82126400ab481590424c8071ef0ea8ec299002ada1210d85320047bc3ac230a6400ab484584614c8010ff0ab80c29900e1f21570185320055b4242030a6400ad583840614c80117f08b8ec09901a2f21171d813200c6e41ae3b02640387e85dc163d04010fb0bb82c7a080b279cd4398b410043fc2ae1316820387c855c262d040f9a8e2b1a872081b2d9857610a411645fc3ac6214822c99c835c4429046917f0cb8085208d32e9817010a4106657312e919482078ec87589329045917f0eb1e83208b3279cd63d064101c3f43eeab04820087e871d560904018baeba9ec6a0802a761353d8d4101c6fc3aa7b1a820087f855c363504070f90ab86c6a0802b3a0a65d8d4100566c14cbb1a828fc9e76dd3635050593cecaa6c6a0803175d475d8d412ad4f420ebb1a8200a9d841d763504abc3ca9aa6c6a080297a1672d8d410052ec2ce5b1a8200a9f845cb635045353908b96c6a0956a7a1352d8d410054ec26a5b1a8200e4f5294b63
  | 13 => 0x380100080100000900080080300300a00800280280500180100000000200100000700500a80380a00000080500000380000100680180480200080380700100180080500180000180000100200200280000780000080180100a00000100100280400a80100000880100300000080000300000100d80200e80000200000100200080600080000000000380200000300900200000000200480080000780100000400080000300080400200400180100000080080180300f00080000000000b00080200000700000000100900a00100080380280200000000480000000200380000000100080680080380080000000000380080000400000500080180880280180080880700280080080000200000180000200180200180300000000000000200100300000180081500100000380880080100000380380000400100980e00280000080080100080000180001800d80080100080180000100180100680400100100080080100000380000380a00180100000000180400000180080000500780100080000000000080a0060098010018000008030008008008020030090000000000008028008090008010030020008088028000000000000000010000030000010000000000018008008018050000028010000030090038018020008068058008020018010070068020020000000000000018010030010000008000098018020000008018018008040010020010000028010038000060008000000020060000008000000050000098010000000000000000010000000020028018000018000010008008018021fe157098b4301c3e42ae131686028bc845d562d0c011f700baac5a18063e2017558b430043fc2ae130e860387c855c261d0c0517b09baec4a18023be1d62189430063abaea3b0a8600ab5841476150c011ef0eb08c2a1a6aade1161185430061f21aea30a8600c3c435d46150c0f8e902ba8c2a181f0fd05751854303e1ea0aea30a8600c5f305d46150c0f8ee20ba8c2a18031d5d751185430043ec3cebb02860387f875d76050c070fd0bb82c7a10021f6177058f420043fc2ae130e840387c855c261d08051bd07b8ac1a10023760f71583420646e43aa6b1c8402a9f8658d439080127b0a38a87210972798c7150e4212c5e43a86b0c840387e87dd5609080187ee9baac1210021fa1c75582420061fba0eab04843b8be879516090807878eb2a2c12100f0f1d554582421dc5f43e86b048402c9e7350d609087717d0fa12c1210eeaea0342582420146f41ee2b0484008dd83dc560908010ff0ab86c6a100e1f21570d8d420066a318e2b1a84068bc865c24250877970c0b8484a1002ad61031d854200572c1063b0a84008f78758461508015a906b08c2a10021fe15701854201c3e42ae030a84008df835c760508051b906b8ec0a1
  | 14 => 0x327402236673c35b5512593f66ce1160aa0000680012be6a13ea00022216516153331e29706100050000000051b03a0003af50b40b3646af45a4252440cc0000005b20000006dd17100051e0000007320001d362900002906570239426200000000072352203069014c6060005a500020267e00000048655e24262e1cf3bb6943a420e58e0006374342f74aa5f00ef0762c613951c3254f24152881ed02c6bc3c84051593145774b11795905d500024c0b63a347153819200067713e5a044c0004352e70000006c713f0002de4422934995281da02a0d411159e1213056724083354821a232f1564281af1e937800059560352e07763c00000000071f00004604839d05b26e5a900034f58363a5e063400063e4453585a81902c20004043275e74f72697340004bc3000a60005d44cf64a00000000026f67500027b0b95655932eb0e11060853ff3cb6146f40000973a71a560e5cc5f91fa3454520000004314c05270000004775135dc5b16223b82da0000967370000000004d11d10946c40000001f00000001f533000050d72056d1e51ef42760829500032e23356101e6735ab09e6886660000000000000000006da17e00013c00035d0a900000016621000000000000000070b0005f30002140004923390000000003b66890001fd00000000001530b00000000005745f0000000002c46e200058900000003600000060c0001b303d0004cb4e251d0005c64c17126011d26601231bc12e5ad5c113b5e35bc18f0003ae17b6cf2905d95e25eb3764004c21de59f29c0000000004d76e653b3ed3fc00000054152400000000000017400056202800009327d54e0003970000002f068c5036990e72794206ae06351410e19a0fb4c762d5911812fb1370f456c2730000ac3163590001e21d57030e000043d59704f71b0004950007270fc06411b00080800780000180900000000300300100080000080000380100000000500100980200100300000280080300000000300680500200100280200000000000180000580100000080100000380000380000080b80600180100f00500100280200000000000200000000100180a80000a80000300180280100400080000000180000000180200000000080000080100080000400700000180000280080000080100080100101000300500000000080000000000000280080180000000300300000000000280200480000080100080480000000080200500080180000300300300000180a80480e8000040000028000020000010000068080028060030008028030000040020048020010040038030048000028018028000010000010000000040018000000000018000008000038000010000010000040000018008000078000048008020000000008008020000008000008000048160008000098008000080
  | 15 => 0x12502e00000061133729f2415cd0005b86e533d11523e37a0f31a722b1e449370f6e32aa56702327e6cc21d6b229400031941300000000014453e53d3f50000000000000005291f40000000000000000001580003700005764a20000000003fe0005c35420000000000000000000004b000044e0002b200000000055a2d80005183993d20000002874fb0000000000b20000001ec10422d5ee3de10b4cd42c0005ec21a43000023c53726c6762055c82f334400071e2a83616f354b00000000070a1ce0000000006e856a0005b63821ba00064b0000000000000000000004b500000000000068551600000000000039a5122f909f6c65cf1e10001764090003db2470e93c90000e60003461b401b0d13ca6f11700b34ff5440fd33246e16d0bb4641f800034d0006d00210003f13c46eb67d62531b38f6e135f73b1750ca1a043f33f0f64f40004983876310080f511a6e75fb6400001022210001ac02d0f95210005602a45d72c103408214049c3ec66d11d1000251820114a616f48f2090003b248e0000001382c30000005c40006fe05303b6ed5340335f25390ab00031060a3510000000001ff00000000012066e0000003a000000000041f00050245938c0320004dd0000002e623700000000006f0005fa00000000046a5922c90000000000002560000746630006c91340000005680c20004e569300000007839821e36b49618449d1320000000002ea0de69c2ed4b86830c123a3ee3e06bb3f22ab4440002a90000000001df00000000000000049b2ca23800000000026767a5660000000006593da69f0003830003914af36f00000067b5d34470000000000003883bc2432c764c18e45b2ad5430916040006c200015450c3e33c600030c1172e31b70000005de0004552165e95af00000000000052a00000040f5da1db14d41a0000000000006d24f30005844e95d60c74de0006f52611690ce2ef00068625451a0000996274d912f1961aa1184911c102f0006566ec0c35db3930bd0004600006a400030144f0001b92290a742309a00000039e2f11c00006be4ca12c0db5a70001e02926c800029e50e70c27c3ce2a24941851415aa6802fc2a507969d50128c71750465c6d827f29162322c4e300043253f1a600068f7265863a10004070005a400006b00064872f41b00000000060d0bf44a5f83a83060000006f200052600019f00000057a0005786b757b6c00000000000006550750002f64560000fe00000040e0001470006b467417374017a3506b86b30e55e81864bd3cf62104a0005b43894bf1492d32720d620351716b0000002fd6824d41600000020df0000f10001f10000000000000006680007080004b40000003b36710003d625d25c00059a0006d30af1f22830bc01713064d2e21d94cc6a600020f6610001bd0000004db5a
  | 16 => 0x70065a10d15100000000000009d54800000024a48155014e6d60000000002b17290007470000006840000810005d10001e74170000000001940003530000000003d13fb3851243d43dc67901907c00000048b2a72822c03cc00019c2272192e00000002ba11e69700000700000021f0710000000002a02a60001985560000001d64e600000047e5462d24620907485b51ab0000be2170000003b901f53a0000002771e67160cb16e0000000002dc5946d75644720002801f60000cf4010000003f972100015b7053542466490000000001140000002df0000a000022f04e0c84736a35803e852d47b53123546c00022636c26a6960004546380000000000000000000006ea67c6586536ef00053c00059d4a73f717f7010002f85756c365100000000016404d05f1102b800000370645300058d5400dc28d4c82b40000000005ac4d574256900022a67f0004116120000700006cd3ac37d0000002632301c410516238a34970d0000000242fe0490001b80000000006154f000022e00046350862f0000000001c600000000000025100000023f00000000004b0840000003be0000002bc2043c747c16a1a41c30a336019d6626d16134f91c25c74a90006e43d504200052066a00000000069b10900000015754a31849f1285f700a2b56b62ff3ad0003aa6f03dd00016c00001200030a1a84e45a21fb0000002086f61f353561d2ee00463334843805c55b63d0e432a4ee4d26453283b40510ad32255451900068e39000054f1fc6f800006c0620002c50312066200000005f43c50002346ca0003c25d86ab5ed1ca50931f20b55c38d12b5e433400068b20c0b83075580003620000000d76874a428f6393b06d94e16b94d64a01fe15f0000000006101036642c80c57302f435c5f50ea1b208023603847d0662e12570006ac0734794d070400000000000000000057c15e0002db56e00000019555500067854d18700000037b0000000000001e80000000002b618a25e00057e0005dd60b0b044b6197130da00000000040a00e4ab2bf5d052b00000000636700000042e42168d00000011931d2ce0005cb3d35ea1362530003f371d4670000006a765b3e733a00000000000000000007d3fd0000000870000003d00000005bd0000004d31e300000000000051014a65e3e50000091a95a64dc15373f5855993a90000001d857348d00000048874561700038600000005e3950204900004756fd42457f61e00000000049e00038e36e2f25813d909c0005300005ce0000000002b300006900012d6db71a0004e000028643361b0f269513d00024d55920042f29b17210f3471a34ae6653210d221b3126a551100009b49a3e144862b6a93d857d00044d4657392250005c250f00006e0000000002b70000001f95be2bb2686912e4000271525000
  | 17 => 0x20407090002200000003805152850000b42e91670006ba2dd3fa46d0004f11bf56b5e50000ba28e3ab48726b0007330d03040005e66aa25a0b11dc6bf0390000000e200010c0000520a80f73726ee4fd0c94b35ca00052c0000000003c01be2406cb0000006fc0002110006c100000032b00000036d4d800018c0000000000006bd6fa00063f34c7244c54400a26b029a6473d719e6e000037168a59830346b48a4ce4a82b065d35260200008669864e14217806a61c44650760f1bb07a55347f21214f2d162c0004fc57150a11f0d320a2242f500d47a45d0160ee44145072a03c2763ef6260504ea6d401c1eb32d0f800034200012923d1800003021881460005230000002967312580003f029800008e02773d62a1016b15060880565c54ba00000000049758702625f0001dd46f3ba00031c02b00073a00000000048528900000006700000000000064172e7410000007463246073564c621340205d00000000005431113563500030d1453b50002500006435570007152643650000000000000005520003770006c540d6ff27543b6056420005b00000000a40004ed00000000000052f6245a14833df2fa0000005bb39b2e52e800000000034b0000003c306d23245138b1ea4290002230c03e630907f72524b03512766f00014328b65015d0003630cd00000000011c13339617d6360007385b732023108900041400063241200000037e0e803766933b00046929915500072d4fa1934682d55fe71c0000000000f00005d200000000000046143e34041072845e4c40001a119131a45863b08341d28a72b14b58a31334a01442200f01d27a1ae41c6d533e0001ad0002a30920053a205527032600042b00000025570e33c0000000000005725323681d04ec0000000000001cc1c572200059b4360002810003e440600000000030e2650000004b600000035500000000005a53631500069266c0ec00003f57424e2af3e267000071900074419b00000042d0004030001c90000000000000005492a16520000004740b55e11ee0002b95b33361260000000ff5820003232d458b1b63f82070000a10003b70000000000c61c713171447000000004100004540c56f04c08f0d90000000000000002ec4ef0006f70000987351682184bb0002495790003eb3310003cd0000430e30000ed13a2392cb54c4ad00000000043c00000037f0005450eb4a51b15ff27837c32c0005fc5b90004800dd0000005ae2523432d64b76180003734576f965403e14800059c11265f64618b07b2bd0004e86ad35a0004fe10721c0d84a108a43a2d05fd0004193bd0000003e900041e0000000000005c02600000000003380006a008c72c00047800b0000001b017710a1d40ae5966004e76b526d0006812d900058c3f400008b1220005886300007364260004c948c0
  | 18 => 0x10845c0184b90002cc2d744931739f33320d6671cb0584b23a50100004eb32923b58f5ef0006444660000000007070473084f50002456dc00020100007e4c301a1633742ac0004396570000005df00000069e64f4be0003bf0592cd57071161a00000c0000000000001f715234154700034e35e6e900015a6a81830003b161615c73e29d5ba7184376df50500018d2ae55f0004893570000d500006000000000056315000000042a0000006a20c40134da36a00000069a0003a60000000000000006284842cf4f800055d5f108d5bf61f6090007430fa0004f62485c94ac25b2840b70001cd3c100000004430f00026624f39c37522838419917c3810950a519712a3790004a300051f0003690004180001d76fb0001b50000000005f61c80000004df0004760003924431890007106de11321541600000066b00007
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x52658488e00a00080008c68040801e0004a41807006080008410060798d851c5439080189473205545844247e07a1d65dcd411040181e835d764107210040f65e8518c644840103d97a1432191210040f65e85cc0644840121d989d46418d210040f66275193214840106f985c872597400041b261205d462500014a4915d0624c9400050ba4a635d4415000122f9854852191200041d660651c543440014a4925907150d100060720d75590414400182d7520964105100040f660651d1214400135195205434c110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x94c
  | 5 => 0x94e
  | 6 => 0x5
  | 7 => 0x2
  | 8 => 0x138c
  | 9 => 0x138e
  | 10 => 0x98c
  | 11 => 0x98e
  | 12 => 0x3
  | 13 => 0x150c
  | 14 => 0x150e
  | 15 => 0x9ce
  | 16 => 0xa0c
  | 17 => 0xa0e
  | 18 => 0x180c
  | 19 => 0x180e
  | 20 => 0x209
  | 21 => 0x20c
  | 22 => 0x20e
  | 23 => 0x140e
  | 24 => 0x154e
  | 25 => 0xb09
  | 26 => 0xb0c
  | 27 => 0xb0e
  | 28 => 0x1409
  | 29 => 0x140c
  | 30 => 0x1549
  | 31 => 0x154c
  | 32 => 0xb49
  | 33 => 0xb4e
  | 34 => 0x1449
  | 35 => 0x144e
  | 36 => 0x289
  | 37 => 0x28c
  | 38 => 0x28e
  | 39 => 0x148e
  | 40 => 0xb89
  | 41 => 0xb8c
  | 42 => 0xb8e
  | 43 => 0x1489
  | 44 => 0x148c
  | 45 => 0x1849
  | 46 => 0x184c
  | 47 => 0x184e
  | 48 => 0xcc9
  | 49 => 0xcce
  | 50 => 0x15c9
  | 51 => 0x15ce
  | 52 => 0x409
  | 53 => 0x40c
  | 54 => 0x40e
  | 55 => 0x160e
  | 56 => 0xd09
  | 57 => 0xd0c
  | 58 => 0xd0e
  | 59 => 0x1609
  | 60 => 0x160c
  | 61 => 0x1889
  | 62 => 0x188c
  | 63 => 0x188e
  | 64 => 0xe89
  | 65 => 0xe8e
  | 66 => 0x18c9
  | 67 => 0x18ce
  | 68 => 0x138956
  | 69 => 0x9c956
  | 70 => 0xb0956
  | 71 => 0x94b16
  | 72 => 0x140956
  | 73 => 0x95416
  | 74 => 0x249
  | 75 => 0x16c9
  | 76 => 0x14c9
  | 77 => 0x2c9
  | 78 => 0x138b16
  | 79 => 0x139416
  | 80 => 0x150996
  | 81 => 0x3c9
  | 82 => 0x1709
  | 83 => 0x1649
  | 84 => 0x449
  | 85 => 0x144d
  | 86 => 0x9d456
  | 87 => 0x4c
  | 88 => 0x124c
  | 89 => 0x9ccd6
  | 90 => 0x8c
  | 91 => 0x128c
  | 92 => 0x9ce96
  | 93 => 0x1789
  | 94 => 0x130c
  | 95 => 0xa0296
  | 96 => 0xa1496
  | 97 => 0xa0d16
  | 98 => 0xa1896
  | 99 => 0xa0e96
  | 100 => 0xa18d6
  | 101 => 0x589
  | 102 => 0x181496
  | 103 => 0x180d16
  | 104 => 0x180e96
  | 105 => 0x10c
  | 106 => 0x1049
  | 107 => 0xb0216
  | 108 => 0x155416
  | 109 => 0xcd556
  | 110 => 0xb8294
  | 111 => 0xb8296
  | 112 => 0x161496
  | 113 => 0x160296
  | 114 => 0xb9496
  | 115 => 0xb8e96
  | 116 => 0xb98d6
  | 117 => 0x24d
  | 118 => 0x185496
  | 119 => 0x41496
  | 120 => 0x184e96
  | 121 => 0xd0411
  | 122 => 0xd0416
  | 123 => 0x40d16
  | 124 => 0x40e96
  | 125 => 0x160d16
  | 126 => 0x189616
  | 127 => 0x161896
  | 128 => 0x160e96
  | 129 => 0x1618d6
  | 130 => 0x104c
  | 131 => 0x194c
  | 132 => 0x41411
  | 133 => 0x40451
  | 134 => 0x40cd1
  | 135 => 0x44411
  | 136 => 0x45611
  | 137 => 0x41651
  | 138 => 0x41a11
  | 139 => 0x165611
  | 140 => 0x45891
  | 141 => 0x41611
  | 142 => 0x154cd6
  | 143 => 0x58a
  | 144 => 0x29554
  | 145 => 0x28954
  | 146 => 0x299d4
  | 147 => 0x28a16
  | 148 => 0x29616
  | 149 => 0x296d6
  | 150 => 0x29796
  | 151 => 0x28b94
  | 152 => 0x41296
  | 153 => 0x41316
  | 154 => 0x29494
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2131
  | 6 => 5342
  | 5 => 1865
  | 4 => 20
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (87367+((h/710+packedAt gbK7 (78847+(h % 710)*12) 12) % 2558)*13) 13
  | 6 => packedAt gbK6 (279556+((h/1780+packedAt gbK6 (256416+(h % 1780)*13) 13) % 7052)*14) 14
  | 5 => packedAt gbK5 (117487+((h/621+packedAt gbK5 (110035+(h % 621)*12) 12) % 2708)*12) 12
  | 4 => packedAt gbK4 (1430+((h/6+packedAt gbK4 (1400+(h % 6)*5) 5) % 29)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfff83e03e07c1fff87fc01ffc19e98fc41f3cf
  | 1 => 0xf00fc003ffffe0fff83fffc0066967607e7cfc
  | 2 => 0xffffc007fff07ffc001fff87187878f8f0f
  | 3 => 0xfffffff800007fffffe003f81f807f00ff0
  | 4 => 0xffffffffffff8000000003ffe0007fff000
  | 5 => 0xfff0000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10e80a20e414094a8264144a8082082c40b1c5
  | 1 => 0xa121400128ad209188094c818228236016545c
  | 2 => 0x202d4c4004a520554802935185185818b0e0a
  | 3 => 0x44ca76a550008466732b0062d81d806e00ba0
  | 4 => 0x888f39b39e739ce00220c01837fe00077de000
  | 5 => 0xcf0001c018031080440300203f7df6d0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafce8eca0feeaeeeafce8eca0feeaeeeafce8eca0feeaeeeafce8eca0feeaeeeafce8eca0feeaeeeafce8eca0feeaeeeafce8eca0feeaeeeafce8eca0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37099
namespace PEqualNP.Outside.L_meta_37099
open PEqualNP.Outside.L_meta_37099.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 10 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_32 : Interval s0Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 60 := (concat bs0_3_0 bs0_3_32)
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
theorem bs0_4_160 : Interval s0Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 165 := (concat (concat bs0_4_0 (concat bs0_4_32 bs0_4_64)) (concat bs0_4_96 (concat bs0_4_128 bs0_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 50 := (concat bs0_5_0 bs0_5_32)
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
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 6 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 90 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
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
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 2 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
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
theorem bs5_4_384 : Interval s5Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 414 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat (concat bs5_4_288 bs5_4_320) (concat bs5_4_352 bs5_4_384))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 616 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 20 := bgb_4_0
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
theorem bgb_5_1856 : Interval gbAtlas 5 1856 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1865 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)) (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 bgb_5_416)))) (concat (concat (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)) (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640))) (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768)) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 bgb_5_896))))) (concat (concat (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 bgb_5_1120))) (concat (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)) (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 bgb_5_1376)))) (concat (concat (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 bgb_5_1600))) (concat (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 bgb_5_1728)) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 bgb_5_1856))))))
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
theorem bgb_6_5312 : Interval gbAtlas 6 5312 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5342 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 (concat bgb_6_576 bgb_6_608))))) (concat (concat (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 (concat bgb_6_736 bgb_6_768))) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)))) (concat (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280)))))) (concat (concat (concat (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)))) (concat (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760))) (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952))))) (concat (concat (concat (concat bgb_6_1984 bgb_6_2016) (concat bgb_6_2048 (concat bgb_6_2080 bgb_6_2112))) (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272)))) (concat (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432))) (concat (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)) (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624))))))) (concat (concat (concat (concat (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 (concat bgb_6_2752 bgb_6_2784))) (concat (concat bgb_6_2816 bgb_6_2848) (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944)))) (concat (concat (concat bgb_6_2976 bgb_6_3008) (concat bgb_6_3040 (concat bgb_6_3072 bgb_6_3104))) (concat (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200)) (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296))))) (concat (concat (concat (concat bgb_6_3328 bgb_6_3360) (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456))) (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616)))) (concat (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776))) (concat (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)) (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968)))))) (concat (concat (concat (concat (concat bgb_6_4000 bgb_6_4032) (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128))) (concat (concat bgb_6_4160 bgb_6_4192) (concat bgb_6_4224 (concat bgb_6_4256 bgb_6_4288)))) (concat (concat (concat bgb_6_4320 bgb_6_4352) (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448))) (concat (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544)) (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640))))) (concat (concat (concat (concat bgb_6_4672 bgb_6_4704) (concat bgb_6_4736 (concat bgb_6_4768 bgb_6_4800))) (concat (concat bgb_6_4832 bgb_6_4864) (concat bgb_6_4896 (concat bgb_6_4928 bgb_6_4960)))) (concat (concat (concat bgb_6_4992 bgb_6_5024) (concat bgb_6_5056 (concat bgb_6_5088 bgb_6_5120))) (concat (concat bgb_6_5152 (concat bgb_6_5184 bgb_6_5216)) (concat bgb_6_5248 (concat bgb_6_5280 bgb_6_5312))))))))
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
theorem bgb_7_2112 : Interval gbAtlas 7 2112 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2131 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))))) (concat (concat (concat (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152)) (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280))) (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 (concat bgb_7_1536 bgb_7_1568))))) (concat (concat (concat (concat bgb_7_1600 bgb_7_1632) (concat bgb_7_1664 bgb_7_1696)) (concat (concat bgb_7_1728 bgb_7_1760) (concat bgb_7_1792 bgb_7_1824))) (concat (concat (concat bgb_7_1856 bgb_7_1888) (concat bgb_7_1920 bgb_7_1952)) (concat (concat bgb_7_1984 bgb_7_2016) (concat bgb_7_2048 (concat bgb_7_2080 bgb_7_2112)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafce8eca0feeaeeeafce8eca0feeaeeeafce8eca0feeaeeeafce8eca0feeaeeeafce8eca0feeaeeeafce8eca0feeaeeeafce8eca0feeaeeeafce8eca0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4243123360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37099.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,5]⟩,⟨.and,[3,4]⟩,⟨.or,[2,6]⟩,⟨.or,[0,7]⟩,⟨.and,[8,9]⟩,⟨.or,[0,2]⟩,⟨.or,[4,5]⟩,⟨.and,[11,12]⟩,⟨.or,[3,13]⟩,⟨.and,[1,14]⟩,⟨.or,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243123360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4243123360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37099

open PEqualNP.Outside.L_meta_37099 in
theorem PEqualNP.Outside.L_meta_37099 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243123360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4243123360) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
