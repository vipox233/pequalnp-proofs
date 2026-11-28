import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40523.Model
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


end PEqualNP.Outside.L_meta_40523.Model

namespace PEqualNP.Outside.L_meta_40523
open PEqualNP.Outside.L_meta_40523.Model
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

def SBf (j : Nat) : Nat := [8, 6, 5, 6, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_40523

namespace PEqualNP.Outside.L_meta_40523
open PEqualNP.Outside.L_meta_40523.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x10cc0010c000104a0c97810c50800011800c8fc41fd40fe43fc31fd10fd32fc32fe32fd42fc10fe42fe10fd21fd41fc21ff42bc40bd43fe30fe40ff31fc30fc42fe20fe41ff10fd20ff43fe21ff32fe31be40ff20fd31bf43ff21ff40fc43ff30fd30fc20fd43ff41fc40
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x4417d53c43e8a2985f943319eaa621bd5250efea8885f14b10dfa0c817e50d07baa7a15f94643eea1887bf438c2fca3206fd0c31beaa2617e534437a86186f50d21fa988637c54cc6fca3996f50f41dfa10817f52443e86208770c830de282873d54086faa1a0dfd5320bf298837c51502faa3205f54a20dea9687bd51d0efca2105f14532dea1883fa20082faa5a05f54242bea9c83de320c7bc87987dc4210dfa8c81be41507eea2986f90310bfaa463bf43886faa8185f15220dea1a217e50842fca190dfd45439eaa661be5050f78a4205fd4930bf28685bd43842fca0216f95320dfa1e437e5390efca0207d50441ef19461fa10042f8a898df55031beaa4857c528437a42205fd4f10ef188617751482f8a0a0df95320bfa96217d51ccafca810fdc8410bfa9841bf411037e86106f8ca40fc88021bd43ccafea9986f50d41be29a837c524c6faa6886f50c32ef99065ec218837ea4a1ef90320be2a421be50d0fbc8618d754f41de20881bc42907de40105754c40bf29e85be4350f7842205f94620fa908433c544c3b862186f14e40efa9a21bc404437a8718cf95031bea94637e511037ea8887790c32cea1a61df4350f7881986fd0e41bea8841bc40843f641885f14c10bfaa4437e530837ea5207bcca20be29e417e539077a86216f50f31dfa9a87be400c2fea2905f14e10f7908437e50ccafca4217714d21bf28e417e5110afaa3986f94b43dea1683bc5150efaa5186fd0a42dea0881be531037e64205f14d42bfa8a81de53d077a87106fd4743ae29a415e53103be8721ef54543df218817d51c83d865107b88521bfa8263bc21903be61185f55120bfaa265bf434c37a43205f95040de2a241de438c77ca818df540429eaa4877d548ca7aa998dfd5131de190817d530437ea5a1ef10640ee19463f741507e843085fd5321deaa6637d5110b7ea8905f550329f28481bc42102faa890df14d40f629221be540cb7ea7205f95020dea1c617d5090f78a4a1df94742fb082217d528437ca810df95130df20421be404437c81987750e32bf2a0617f548437a8618df55321bea80637e544cafca7085fd5331bfaa0637d5110f7c8420df15321bf288617c548877e86205f94443bf28483be311037a84a0f70ca30bf29e817d518cafca208770c831de20441bd41902baa7a15fd4c10df994817e508cafaa7194fd5110be2a4637f5250f7aa7205f54831bf29663df318c67ca8195f54830df98881ec21082fca4197ec4110afa9a415f53442f8a710df54440df21c817f53c837ca2a1ef50e21be2a461bf434c77e86905f94820fd88421bf435037865206f0c440dfa8287de53d0afca7216f50d42dfa18217d53d06faa8887bcc820bfaa0217d5010f7a8790df15332ef98863bc42902fca8215f54b31df2a0617d508c6b8a690dfd4931
  | 1 => 0xd52902fea710ef55332dfa1e857d50d0b7a86a05f94432bea8665f6310c6f8a2a1efd0842dfa8a87bc50d0f7ea890df95230bea9841bf438cbba8618cf15230bfa8a65bd54c42fca8905bd4910be2a465bd43903f480205f54f42ae29a217c540cb7e87905f14142bea9e417e53487bc60985f94020bea9a43bc54486fca218de14121f7102417f54ccafaa3106750e31df202617f53442faa910dfd4d20dea0883bf52102faa7a06f50c43ef21887de324cafaa5886f90a41fc10621ed4210afaa9886f14a40bfa9a836f524c3bc6298df94030bea9c437d540877aa1a1df54810de98881bd401037880907ed4121af29e85fa300c37880085fd4121bf29483bc42106fca318df94730de2a461df53482fca6215f54910bea96877f548cae8a2985f54e20dea1081bf430c37ca32057d4d21cea1e617e518caf8a4a1df15030f719065bd43d02faa7085f15132bea98839d430c77e8610efd0f41dea1c857c53086f8a690df94243dfa1a437e53d067aa9995f54743de2a221bc43103d8a4986fd4440bf28843be50103dc84217ecc230de98c81de320c27ca998f74c431be29221bc439037e8620df94f20df292877e540c7e8a2904f14143eea1a619d53102faa9984fd5130dfa1c87bd43cc27aa6205f94032be28a61f421042f8a4a0efd0d10bfaa0657c53c86fca410cfd5121dfa1e6177514c2faa110efd0e109eaa6417c53c433a86197dc86219faa461f510043f680a05fd4810bf29843be405037c80906fd0d419e2a241ef324cafca12079484219faa241be40042fea7086f90840bf284413e54c42fca1a1df54041df2a6637d50cc73ca6206fd0f32bea8c617e53902fca418df94021bea94817f52502f8a4986f50f10dfa00817c544c33ea6a1efd0a40fda04817e5190afaa010df54b41dfa1865bd429027aa7204f15121be2a0637e52d037a86996fd5230df288817d5490378a3205fd4142bf296217e51106fca710f74c832dfa9881ba50102faa7187b4c832dfa1c637f534877ca3a1ef50f20de206217e5010fda40106fd0c429f2a661bd32902fea2987bcca32bea9c857b50486faa1195f94b43bfaa6217e53c87be65194f15110bf294817f504cafaa921dfd4a10eea9e837d54cc6fea810ef50e32de29687f9300c2fca898df54840bf28083de328c67ca9995f94a10f690843be4250afea790df94740ef980617d5290efca9086f55330ef21c65be429027ca821fec8120bea8483bf438837a87a15f54a41dfa0c837f54082faa0195f95231dea1085f7314c6fca8196f4c840fd900217e544437aa6205f14131dfa1e63be521037aa2204f94343bea9c63bf544c37aa8185f94843de20061bc40c82f8a7105f15010fb98821fb304c2fea6a16fd0240be29a21be32103dea4985f55230bea9087bd43086fca118df94810f790
  | 2 => 0x210149203c000000002c1c00010000010c000000022401a000110580000000010d5078000000200c050240b00c1c03c0100001000060007a0600b03004014890740b0140504a6103400040590200c020050080504c340046a04400008020f4000340d020030002b0241011803028930fc0504c01018400440303c1104c08024070040101c012b00e074020500000c0002c0009c020640000c00000180080100001010030e40e02c1c000003283d0546d08c0000c1702c000180000c0001c01000e610cc5010080000a0500000402180510000404c0002c0200c000040115c7e068149fc08000090680b054390a00106c000b00642400000000240906800248950000c104a4000150001f0180007402000950100005084020673a4970d81a000000002f0600500008000060381b008000302f00013000353fd42360000080403006000000001f28015000040240007c370000f3982d0001006c16004000105d0181000000000620004d11c010137881184f55030ee980617f540c378a6204f55031ef18c61bf4310efca998f750f30bf2a083bd434c6fca910df54643f790c43bf4350b7c42205b14910bf296837c544877e87205fd5220bf29c41ee218827ca9906f0c640af29e837c540837c81105d14520df18c817d5310afaa9105f55020bea9881bd43082fca3a1df54343be29281ec320827ca0205f94f10ef298817d544cafea2a15f55332beaa641bf31903ee63087bd0942bfa98433e54087b863185f94a43fc28243bf211037a8720df94230bea96617d52886fea0a0fe48020de2a261be54cc2f8a810df15120fa18c21f8200437aa818df14121beaa483be54c423aa6207714d10bea8c857c5050f7aa9906f94e40dfa1c85dd53102fca6905f95220df204617f544c3ba86195f95232fba8a41de434c2faa190efd0b41bf28c836c524c2faa420df95121bf298217e51886fea9187ec8220bf2a6217c54c437aa8197dc8521bf28485f621087dea4886f50d30bea8e81bc40082fca6185f14520bea8c217e520c37e87a05f94031bf298637e50042fca6195f94a31bf290817f53502fca110dfd5121df208817c53483bea690df54d20bf2a021be21902f8a2a15fd4941df294817f5050fde85215f14c20df2a6657e53102fca821df948419f2a0617d54042fea8905f94c43fb90c217c504cafaa7205f54742df90c81bf50d0ef8a4085f95321dea9081bc404c2faa610e750e32fca00813d540cb7a86205f55231dfa12837e52443ee8320f750e31bea9e437e52cc2fca9985f15330fb98c637d548437aa810df15320dfa0883bd5050f7e87885f94a32f7108417e54ccafaa2196f14743bea8861f641106f8a8885f94630bfa9c41bd51902fca5187dc4010ee29a41bc511037a86085f94a42df20041bf434cb7c83205f55131dea1a41b
  | 3 => 0x2b98a000010001c00821064494f81f00000150280301601000214000c8020140500c810000203800294000500b02c12024bb0100c1fc1905
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x7430863c6055032dc147204825d6315020c7989531031e6154c40b9d95210871f6554c408fd954310f1c5350c21cdd44404829d63103208fd94400c23e6414f10d9148514c31f5350d429718d520432d4314930c750d508c71e53940409b189544c6786054d21f818121086f061480209dd95310c63d65d0c328fd9743c429c6050c328f59253c823c6454a308f58f544426c62551108f59253083585314121cb14a404c23f6454032c758c544c3385414121abd895150e3d6414b10c7193534869f63546409798c520429f6354a408f594329023f6454321b9185200831e5350f218f191508c71f548c630c798e540865f6355120ae98353103676548421a798c53103986050d308f59543c833754d4530c758e54c431f64d4d10c718953102756115020d514c514831d53108408f98254cc72d43d4930cdd0c51483954314530e694e501023e65d0d218f180544423e64d4131c794d438831c54d4d20c7193534431d5350e42c7d85531031d548c8308f990538871e6395031cd150514825e63951108f58c54486766114c208f99352c42986050d309799453442bb604c440a758c40c425d63d4a109798f52c4367521453097d8d520423e650c840c754d438431f53d0d20e350c524c2ac6254143a758c400438f434c832b9181210863d64946208fd9150cc63d63550308fd95430c29e61d4d439dd85544831e6414d10cb153524423e6494820cbd4a404c25f6354910c754d52103732114121c794d439029d63100208f992538836551084209b98a524423c6055332cd50f514825d63951328f195211033a60940408f992538867b6544010cd153514c31f5414d219b988548c7c763484219718d5190ae462440108f982540867765484218f594400c23d65cc640c715353486ba60d4a40c7d935348795438c431c794d43d0a3d65900309758e524429f6550c32a7590328c737519012097d95300c31d6414d10bc181210874c53d49108f992528c31d6154c408fd91528c66e62150108f996404823f6550c218f590538832f54d4910bc580310431d53cc440ad98750d0e3e60950319bd8953442b46154143c714f43442b761541439758c540423d6414f108f590524c63d6395320e9d0d210871e6395320e6d0d300c31e6414d20a798f429029d6490c329ed95401026e62951109dd85544cb1d5394440c7152434c23c64549108f590530831543145309d58753c82ba6014e40add855250e3d650c6408f59421102756195120c794d431031d53948408fd91518c31d530c8408f593504ca3c6454420c750d500ca5d63951219d594310427b60549108f59053c865f654c832c754d511033754d4520a758f4210a6f6255130e350f524c25d6590c31ae983539023d65d0c31c754d430425f63551108f980544423d6494630c714f434872c5414910
  | 1 => 0xc27b654c030b358a430ca9d6310030c754d321031d5350440cb148404c23d6494c21e3d89438ca5d63d4b108f597311031f6550e318f99053482ac6254543c750e52cc23d64d41218f590538425f6550c43a7181438cb1f5350d409758c548829d6490c31ae181434c32f43d4930d3548320c71e5350e10cd5445150f1e5450f30ab988511031d530c440ab58b50d0e3d6590c409d58653482d5610c831c754f42103564314530c794d430423d64949108f191500c7a840480209d986544831f540ca308f597430c31e5450c31b5185300c35453841109d586544c25e6394910a758c511021d63950219e982534863d64d4f10d5d4c514833a60d52309e59420042ba6014440c7d93534831d5390c40e550f514c29d6395021cd54451d0fa55448421c750c514c31d5350e40c7d95430c73451101308f99253487c46348421cd1535148395430c4108f592520831d54cc030c7d4d435065c63549109bd954210abb6048440a798f511034e4314930c7d4d434423c60553318f992510429e63d0440cb50c524431c5414d109b98b53c431e6395032a758e54c42cc624c030c7d4e404423f6590030aed81321035453d4520ad984521036752d45308fd91500c69d6310110c754e411023e64d412197994534863f6355310c754f42d06ba60d0d309ed81534869e63d4840a798c511025d63153218f990534432c5290110c7193534825f654c4319b58b53c423e6510110cdd0f514831d63950218f997329023d65cca409d185534838d430ca209e181544cb1e6414d218f994544863d64d4131ae181438c29e62d4d438f992518823e64150328f590520429d64cc631a758f429031d4394832ad185435063e6095032e9191210871e5350c20ce980548c26f6255110a758f511031f6550d308f992544823e6415030ae1815150e5e63150209d984548ca3f6550040ab98851d0e3e64d4a10ae983438c31d5310440c754c511023c65486408f59743c823e65cc6408f990530829f6550c31c7d50534431e5350f41c754e321023f64546329798c54c871e6454c40a758f4250795430c610a758e400c2756115232c7589531031d540c4309b58a544423f6454332c794d438863e65d0d10b8181210873b54141218f590534423d6494e209798e5348397434c4319b588548c6ad6214440a7d92304c33943d4121a798f421023d6494c30a758f419073543145309b994524425d6395320cd146404c23c64540219dd85534431e6454f418f992530871f5350f108f596540ca3e609533297195434c29d6310120e9d91210863c64540328f597430863e65cc840cbd48404c31d43947309b98a544c23d6414e218fd91534823f6355030c754f511029d63953208fd9743c82bb60486408f58e54c431f5350c21a798f419023e6494c109e580530871d6414d208fd9
  | 2 => 0x63d0b41a75835350e3c6454331a7d8d211025c6354021c7d4d43c83976150e31c7d4f434425d63951318fd8d540863f64542329b98a534429d63902309718d544423f64542319e181544c65e6395120ae1815250e746154032c754e42102ac6250d42c754d401023f64542218f592534425f6354021ae983521023d6414c218fd95411063e65084408fd8d54c82b8604c840da14b104431d5348440ae18143c431d5350c20a798c521025d6395120ae181311023e64d4f20c7552310c3375110130e350c320829d640c8318f191520423d6494d21d3d4f524431c5310120ce50c50486ba6014a40a7593320cb1d53d0f418f99053c863d65d0f108f19153482ba6014c40ba18121086756114c208f994544c23d6414d218f992524423f655084297d8d529063d6494f108f58e54086d86050d30ae181219029d6594c409ed81544863e6414b108f990534871d43540318fd91520431f548ca308f592530ca3e64d4132c758e54c823d6414d208f992518c2e86244010d5d4f514825e6394d218f994219023e6414c218f99543482b86050c208fd9153486796094d21ce993504863d65950318f990538431e6454f428f592538863e6495130ae181430425c63551209758c520431c5414d219b988530426d62150108f992544869c6050c31ab98b50d0e3e6494c32ced53504863c65d0d21c7195438c66d6214c10a758c521023e64951108f594219034c5388120c7d95438ca9c6050f30c754d421029f63486409718d529033751901309798e54c831f5394e408f59253c872f43149108f59053c831d53d0c42c754f43d0a756508410c7181531033543d45309798e544866d6294d108f181540c69d63d04408f596540871e63953109d986544c31c5350d208f197434825e6394d10b958a210871f6550c32c714d43c823d6494a308f994329023d6494c31c750d508ca7860551218f99353087995394040ad584521023e6494a109799453482776544010d6d4f504871f5350d219e982544863e6510130c7550320c63d6494a10d550c514c23d63d5120a758f4290a5c63551218f996404423e60151218f995434866f654c8328f19153486746155132cb5485250e3e65151108f191534426c6254d108fd9543c423f64544208f990520431f5310110c7590534869d63d0640b518d100423e6414f20cb50f524431d4394831c714e40483374314530f8084200431e5350c30c7185531031d5350e418f59352c434d4314930c754d438831c6550d30cb54852d0e5d6395310ae983511031c5350d41abd895050f2f5290110c754d42d076452d45308f596421063c6454a31c754e501023c6454630d3d4c52442ba6014840c7d50534833b43d4121cb148404429d63103309798e540863f654864097d8d5190a3f6454a30c754f401029d63d0840cbd0c524
  | 3 => 0xd308f990538825e6315220d6d4c504866d650c8209b58a544c3946150e3197d8d529029d6310210ced90504863d6414c108f992530c71e63953309e582544865d6315210c714c404439b6050d30c7d4c404823e65d0d208f58f544871f6550f308f59253043645284110ced0c504863e64149319798e54c431d53cc8408f992530c23e6494d20e9484211023e6414c108f590514ca3e6494e10a7d9543cc27761540328f994544829c6348440ec101100423f6454910c714d43c426f6548421c7d53308c23e65101208f997435029d63d0441c7d53534425e63d4a10c754f43d02ba6014640d9146204827a6014c21c754c52103375414530c7550320c25f6354420c754f41102ad62d0c42e3189438ca3d6550c21ad58750d0e3e6415031ae983519025d6395110aed815250e3c6550d108fd91534432f54d4930a7592434c31d5350f21b5586430c65f6354640c7d53534863d6595030d314c5244354518c130a7181438c63e6494f208fd9543c823d650c4409758c54886cc6348020cbd50524c23c6550d21cbd50524429d63101308f181540863d64944108f1954348398404c0309ed81544c63e6494f109bd89534829d64cca328f594321033743d4530e950d210871c5350d21c7951430ca3e60d51218f992534431c5414d208f99353c423d63151108f191508863c64543329b189500c79943cc130c7195438ca3c65d0d10cd150514c31d5314c40a758f521023d64d4c218f597321023e650c6409dd85524433543145208f592534831d53d0c41c754d43886746155120ae181211023c64542329dd85534827b6055132a758c408833451901209798c548867765504419b189544c34c528c130c754e211031f5390120a758c408c26f6255131f8d81210869c6354a40c754f211031f540c6308f19150c865d6590c32e9484219031f5350d20c754d311023f6454021c750e510c71d4394a31ad98452d0f3964d4121d9d4821842746155130c714d434432c54149309bd95200825c6354a418f995434423d64d4f20c7d4f434871d548c831ce153504872f43d4910c754e311035853d4121e350e320ca5e6315030c754c431023d6494e108fd9521102ad6214743cbd48404431d544c030c714e404429c6348640cb153524c31d5308440ad58452d0eb46154943c714f434831e5450c43c758f548c36552084108f99731103a654484219e596100423e65901309dd85544c23d6550f10c754f43103386414121cdd50514831d63152308758e54c825c6354640c750c524c23d63151208f99253c871c5350d42c754f521036a21141219d98753c823e6494c208f191518ca1c6550d3097d8d544867b6548020ba58032082b86050f208f990514ca3f6550c32c750e518cb1d43944328f99431102b561d0c41c7d53534831f6254c409d986534829d
  | 4 => 0x2200b500040a990d100400044030000502400078380002508c030e52a0140f0241e01c0d0200318c130cc6608026010001840f00005894130080c03c150040801c6400407024010d000000120005100c22158070041098c010040030c1e0340d02c0019455004650e003000074e415084024ac080000d04a910200011c01042650c800004000d81f000027644500874008150050600074000271500007810004000080504430000125b81d01805000090305b1b01a0101709c283200c004720fc000000005c21008030800a0a43f13c002b80b0102902c49000200041b000410000007c00175cc0241200019004000b432014050a00b014cc000a601401000011141b01018064174fcbe0000000afc00c0e004140280000c0b0404f0040308c0019066000d201020000e902c09004000000701c001380a038000000000006130010080a0346200c00004070000211c170140109c5801000184630002a090530405e0345c088030d0081ac040400c0141b00c00004de048003dc005b8133b80103f1e6054c40a7593310c6bb60545439718d51082766115020a718d519031c54d4d108758e54c423e65d09418f195434c26f62540319798c548423d64d4a109758e540865e6315010c350c524c23e65d0d30cd144404823f6550c318f990540869c6050
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x7b020900050d00010c462985082402240206001e0c040b0500000104081c093800070000410920060d16000b00120200030f060502000300101c000b0827a2ae3322a6206195318121102c43828619041985942108010c2ac6288809869063101100420eb9cc928821075d85310110c32c7306a91860d53588511030aa18c2a8065895952108440a30e0a1aa018e0d43189500c687396a6a1e21a85506048421c2aa6b08a4205907050f514c20ebb0a620241451c14314530d46e83024210d85739512108698382a228a87435ca6454f4183eeda9880905087050c524c30ca98c0a1841075cc654844083ae7320a5884e07158032082983828628a61681c12108640a2ce232a871960d63d484044312a92c229687291d94348421c1ec8294609841d73180544430d3a8c0a1a61c41c14314530e0a86290a29841f7359421902c438286292614a1c14314930c32a630286085157199153d0b8438286292618654f604c440838eca9a4220591731011004351a18c090843075cc6055021d40c83024210e0d63d48404c20fbaac720061461c16254c40d40c2202401041d73994211020eb98c8a84438654f6048440a30e0a18a2986c063181210870bb20a31826183595430c820a32e6320a090d907050c514c312b12a228e87521c14314930a2ce3b2a8698524715485250f4431080980614a1c15214943a1ce5b2a869861563d444048287b92c2a9881459c66454c40c2ac230aa620518705855310292392a228a87681c12108440e26e0a18a29870b7050c524c28c3828629261451c56254c40870e0b2a8610e156550c310420eb98c8a8643075d46348440e0aa6908422061b5318143c82a83828628a61465d4404c030a1ce432a8718c1d7598f421028c38286a8065621c143d4930a20e0a18a29851975d0d300c292bae869084307ddb531011083ceca9a42206a062101100420eb9cc9a8243459c75350f20d2286b00620861563d44404c270392c018821c150f521453083aeb31e82205197399350487503a0c09084385550614c030c1aa8312601849a75181434c361b18c090843a8d906048421d20c2202601841d7399252843512a0c090843a850c6048421a18e4b0aa62041d73992520830aa9cc229081075ce6494620d08c831a4210e1953d813210287394c8a9881641c1430c410a1ae5322a62060d63148404c30ab18a2202418358c5210110c36a63028788688631012008306b10c4a988145dc56254c4083ae7306a890c1e76d4d43086863828629261465c05350c21d1286b0064107054314b514c2c4b9880900418354e6214440
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x8828127000c0100026b220000010000000000d01531c12108440a81831d06048421a04825846154c40b008050c52d4530c81431c9600c4109048754d2108440b008050f5214530b008050c5214530c81731844048020c21651c12108440c09651c1430c820c81431c5600c820c81731884044010a818395060484218918718c4044010a1281d4c6050f20a04815886254c40a0a82d4c6050f10a21851d06048421a08805886254c40a2185d0c6048421a108050c6154032c11651c1430c410a088050c6254031884865ce54484218898718c4048020a10805846154c40
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 802
  | 4 => 883
  | 3 => 144
  | 2 => 27
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
  | 5 => 2*((h/337+packedAt s0K5 (21654+(h % 337)*10) 10) % 802)
  | 4 => 2*((h/308+packedAt s0K4 (33554+(h % 308)*10) 10) % 883)
  | 3 => 2*((h/62+packedAt s0K3 (7056+(h % 62)*8) 8) % 144)
  | 2 => 2*((h/30+packedAt s0K2 (1620+(h % 30)*5) 5) % 27)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffff01ffffff03ffffffffc0fffc7ff1ff
  | 2 => 0xffc07ffffe03fffffc0fff03ffff07ff9c7e3f
  | 3 => 0x1fff80fffffc07fffff03ffc0ffff83fe78fc7
  | 4 => 0xe00000fffffff80fffffc0000fffffc3f80ff8
  | 5 => 0xffffff000000000ffffffffff0000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x24450a211c48912200b2cb4512c04a4429b0db
  | 2 => 0x48931452243922452c055522a55904a994562d
  | 3 => 0x110a269448907489555026a889aa9032c68b46
  | 4 => 0x9c2c58e8912240ee9a6980c30e34e703780db0
  | 5 => 0x1e3060f0e1c3870fe38e38f3c038c623ff6000
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc0c000fcc0ccc0fcc0c000fcc0ccc0fcc0c000fcc0ccc0fcc0c000fcc0ccc0fcc0c000fcc0ccc0fcc0c000fcc0ccc0fcc0c000fcc0ccc0fcc0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40523
namespace PEqualNP.Outside.L_meta_40523
open PEqualNP.Outside.L_meta_40523.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x3000027bc40bd41de32ef32be40ec32cc32bf41dc32
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x30c0000c6aa0658c32507186420630cb419aa88818e540ca9ca519630ca40
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x9c10c9511020d650cb418359432102856195032
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | 2 => packedAt s1K2 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/10+packedAt s1K4 (144+(h % 10)*4) 4) % 9)
  | 3 => 2*((h/9+packedAt s1K3 (216+(h % 9)*3) 3) % 8)
  | 2 => 2*((h/8+packedAt s1K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffe07fffffc0fffffffffe07fffe3ff1ff
  | 2 => 0x81fc0fff83ffffff0783c1f03ff87fffd24e3f
  | 3 => 0xfe000ffffc0fc1fff803fe003fff8781e38fcc
  | 4 => 0xffffff001fffffc00003ffff801fc0ff0
  | 5 => 0xfffff000000001ffffffffffc0000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8828002300208000188442118a0088940490d5
  | 2 => 0x24519644194530cb032191a214c85568d2462a
  | 3 => 0x149aaa8928ea13556842f484a755060d638b4c
  | 4 => 0x59634d125283a5a6b5e8210939a66031bc0db0
  | 5 => 0x61838e1c630c39f8c67339ce01c44441fb6000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0faaaaaaafaa0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40523
namespace PEqualNP.Outside.L_meta_40523
open PEqualNP.Outside.L_meta_40523.Model
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
  | 4 => 2*((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 1)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfe07ffffff01ff81fffff03fffffc07e7e3fc7
  | 1 => 0xfff80fe03ffe07fe0f81ffc1f80fff81b3ccf8
  | 3 => 0xfffff0003ffffffff001fffe000fffffc3f0ff
  | 4 => 0x3ffffffffffe0000000ffffffc00ff
  | 5 => 0xffffffffc00007fffffffffffff00001ffff00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x1230a145011c1180318a310a68e2ca2a1615c3
  | 1 => 0x5452628d5224739606a8d54971255aa8b2ccd8
  | 3 => 0x88a144d1a448a4aad04169ac2249a34d43706d
  | 4 => 0xd1c58b1e3891474d6b6c0c21448e3c71fc00b6
  | 5 => 0xe1060c1830e186718c718e3187003041e9aa00
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaaee000000eeaaeeaaee000000eeaaeeaaee000000eeaaeeaaee000000eeaaeeaaee000000eeaaeeaaee000000eeaaeeaaee000000eeaaeeaaee000000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40523
namespace PEqualNP.Outside.L_meta_40523
open PEqualNP.Outside.L_meta_40523.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x24090031000f421f710de32dd30de31dc31f510de43dc32f721df30dd43
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x208eaa0651d54cc2a8a2a1d914910
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
  | 5 => 2*((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/11+packedAt s3K4 (192+(h % 11)*4) 4) % 12)
  | 3 => 2*((h/8+packedAt s3K3 (108+(h % 8)*2) 2) % 4)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7fffffc0fffff03ffff83ffffc0fffe7c7e3f
  | 1 => 0xf80fc0fff03f07fc3e07fc3e07ff0781b3b3cc
  | 2 => 0xfff000ffffffffffc007ffc007ffffffc3c3ff
  | 4 => 0xffffc007fffff8000007fff801fc03f0
  | 5 => 0xffffff00000007fffffffffff8000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x10a10804608221004628804a31484c94141615
  | 1 => 0x32629948a3942b2c1aa3a42c52d9450cb1b2cc
  | 2 => 0x4144a2910528845581054a8084a2926942c16a
  | 4 => 0xe58b3ce24a0eb79aedb06229273ce431fc03b0
  | 5 => 0x860c30c38c30c6e331c67331c0308041eb6800
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0eaeaeaeae0e0a0a0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40523
namespace PEqualNP.Outside.L_meta_40523
open PEqualNP.Outside.L_meta_40523.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x80000df30f710dd30de31f510dc31
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x7a260885654031
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/9+packedAt s4K4 (96+(h % 9)*3) 3) % 6)
  | 3 => 2*((h/7+packedAt s4K3 (54+(h % 7)*1) 1) % 2)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x83fffff81ffffc0ff83fe1ffffc1fffd8c7e3f
  | 1 => 0xfc07e0ffe07e0ff0ffc1fe1e07fe0f02f3b3cc
  | 2 => 0xfff800ffffffffff0001ffe007ffffff03c3ff
  | 3 => 0xffff800ffffffe000007fff003fc03f0
  | 5 => 0xffffff0000000ffffffffffff8000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x88508808c1044401190a202a31509928841615
  | 1 => 0x19314911472854b06948e20c52d28a18b1b2cc
  | 2 => 0x20a252a20a5109560421554084a524d302c16a
  | 3 => 0x72c59cc4941d6e6bb5ac11092739c863dc03b0
  | 5 => 0x4306108718618b8cc6319991c02100836b6800
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeae0a0e0a0eeeaeeeae0a0e0a0eeeaeeeae0a0e0a0eeeaeeeae0a0e0a0eeeaeeeae0a0e0a0eeeaeeeae0a0e0a0eeeaeeeae0a0e0a0eeeaeeeae0a0e0a0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40523
namespace PEqualNP.Outside.L_meta_40523
open PEqualNP.Outside.L_meta_40523.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3830400400cf00a0000060000000000006c000000008c2820000590000020c0008001ff30fd20fe20ff10f710f510fe42fe10fd21fd31ff32fe43fd43ff40fc31ff31fd40ff20fd30fd32fc10fe40fe30fe21fc30ff42ff43fc42fc43fc40fc32fc41fd42fc20fe31fe32ff41fc21fd10fe41fd41ff21
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa21f520c42faa998df94221f710a437c53507eca9887d84110f810221775150fbc60985ed4132df21c85f653c43f640905f95220fb186217f5150b7e81207d14542be2a261fa40842faa710df94742fa18621f930842fca7207dd0110efa1e61f441cc7eea8887e8c210efa1c877f54ccafaa3085f54231bf2a041bd42d02faa6205f94031df21a87f640c42eca2187d50510fb192217d540c2f8a4a05fd5131bea90217e5110bec63887d88421bf29a437e518c2fca0207d54f10bf294657f54042fca720df94f21fb996217f53c42faa4885f94441beaa665bd40103f420085f55121fa18843f453c42fca6185d94640bfa9621f5510c3bc64995fd4532fa28a65f452c42f8a8885f94c43baa8c81f441c86faa198ef55020fa90a21f652c43ea85885f14121ee21c657d54482bea6a0dfd5330eea9c81ed320cafaa3995fd4e10bfa9a437c544c6bea6a17d50310bfaa6437c53842fca121dfd5230bea9c63dc5350a7ea8994f55230bf2a6617e54c42fca3906fd0441be2a6617e54487f660105f95041bea9c837e508437887a07b48421baa88817c53442faa8107e0c320bea8e61f420442faa5107e94221dfa1085f820443ee6390dfd5320fa98863fb5050bf681207e14142bfa92617f50507f281085f94c10fb21221bd411077c84a15f15031af298417e500c3da84215f14d40beaa263df430cafca0195f94341bea9c61fa40102f8a7887dc8710be28283ee20482fca6215fd4530fb292217f5250eeaa2187d50d10fa21e217f53482bca7205fd4543dfa1c87fa500c7eea4885f94430efa9a837e54043de64995f94431be292217e53443f680a07dd0721fc900417e530cbba64197e54041bf29043f753443e862887e94041fca00817950886fea098fd88510be29621745150be885887d10710f7190657d51902fea498fbcca32fda82657d54cc2fea818f7d0d30bf296217e540c6fca11877d0e31bfaa2437d53c42faa3907d8c431beaa4817f54886fca7885fd4f21de21c857d54882fea610df14a10beaa4657e52d06faa518df14532dfaa263f431c86f8a0a15f95132faaa2217f53502faa598fdc8621df21c833e548c2faa5205f54642bd28083df308c2faa3a1df14542ef988637d50086fca3206f50c43ee21863bf42d03ee63885d94440bf29081f421442fea8185fd4c20fa99621bf4290beea9887dd0310fba8a877c54042fca8887bd0942bf290637651042fca1a15f95021bf280437e52902faa1a17d54d10faa88817e50cc7f060106fd0040fba0e637f53507ea8220df94830fb106215d53902faa12177ccb30bf29e855c5350afca9195f94e43bf29485f721486f8a2905fd4f20be2a4217d50886faa2205f94b31fba1a217e52d03ee85887dc8310faa8c617c548c2faa790fc8c110f690041df4350efca8905fd5032
  | 1 => 0xf5350afca1a1df94041fa90e217e54102faa0195f54f41fc88021f552c42faa120df15121baa8841f630442faa190dfd5210bf28e617e50083eea2a15f54d20ae29a837d5210efea4085f54a43fd18221f930442fca1195f95331bfa8285fb304c2fca4107d4c110fb28c617e528c2faa0215f95042fc98061f950886fca0085f54243fa106217f5050fba8621fd90110bf28c417e52842fca9185f54d21fb18a21ef20882faa5087d10431fb21621f543c42fea8887d14910fd20221f732442faa2215f54c21bf29e837d54c86fca421df94f20bea80637f54087f041087710d309f2a0417e53d02fca520fbc8621df21883fa20083ba65986f90140fa182217d54906fca2195f94240df218857e520cbea84887d08710be28a817d5490bb88718fd94d10bea9c817551882faa7217d10421fb10e21df5350af8a990df54830faa0221dd324c37a84a07e50110bf29c857d544cbdc84215fd4540bf2a6653f544c6faa020df94c21bf28c657f54882fca0217714d41fa18e217c504caf8a710fd153109eaa041df320cafaa5a1df94241bf28c637d52886faa7905fd4941fba0a83f551882eaa3185f55032bfaa663fb40082faa58877d0e32bf294637e54c87e6a0887e10020bf28643f741907ee6210fd55310bfa92817651082f8a2a1df94c20be2a065f7410c6faa2107dc8510fb2a2217e51087e886885f14943bf296617c548caf8a9905f14f20bea9883f741086f8a6a15f94220dfa0c83de53903e640885f94743eea98417e5210afea090fe8c030bf28c85f551083de4210fe54031de21a817e54c837aa9187d90441be2a4417e51ccafca710dfd4a10ef98c63f551902fca8185f94c41fa20a217d5010efca9085e94221bf280877e51082fca4085f55320fa21221f6510c2fea6085f14941bf292217e51d037a84215f55243bba8a857d52106fea8105fd4910f7900417c54c43ee87885f94621de21885bf42502f8a690df55031bea94837d54886fea6886f90541bea8683fb30c82f4a018df15331bea96837d53d0b7c87a05f95130fb28c817d51882faa7105f95032be29263f752c42faa5985f94a43bf29c21f45150e78a898dfd4e21fa986217c5050fde85215f14e20fb98a637c544cbea64886fd5132bfaa4637f51483eca2107dcc510fba9e217e54886faa8885f55310bea8c61f641c42faa4207dcc310baa8c217d518cbeea0887d90f10bf29083fb10443f640886750c43bea98217e5090af8a910ef10c41bda82857d5310afaa1a1df95043df2a041f720442faa3a05d94630ee988637e53103ee82885f95231bea9841df328cbea63887d88110beaa261f7514cbe8658877d0c31be298217e53482faa418fdd0910bfa9c413c544cafaa918fd48421fb98c637c524c3e880885f54742bba8a65be548c3ee20085d14532bea9
  | 2 => 0xa01804170120102c000020036e018d20002201c04061160108c128014894c0303c040040300c050020a0001e80010812120500294c08804040240000e6d00e0084600000139a22703e00000003aa00000009e0100bc040100601c17802013860581131000020bc000b60b000308ba358a42186a0102a0000e008000682800026298220104a340c00205e6880e4980a0a00027826f90000580600006b4b520001c008121a0000000605070170000f00c16826008026800c059700600e190b40003a9f0169a0deb600c000883b8040186e4680204802020000a00038000000121c08a038141000002800030061401e08800008d42b936270f61a00001804460c21480000aae24800a70080d8241f0000786800004038000801c360000800205802000280180c420062480c0284400826060041747a1b0040600a1893bf741c42fea8987ec8210ef18a63f130443be649877cc030fa2a2217e51906faa1195e14142beaa421f710842f8a6105754c20fd884217d5190efea8906f10e41fd984617c54482fca5a1dd14543faa92217c53086f8a790fc90110fa880217f504cbbca6105f54432be2a043fb20883b886195d94620bca8063f730442f8a098df94332bf284637d5110fec86885f55230fda0641f64144378a898fd94440beaa021dd300c3ea83887d10310bca80837e53882fea8997710f30fb19621de4310ef0a0995f54430df21a81f432443e280885f54b40be28a61f651882faa7a06fd0c43beaa0437e530c6faa7197d4c510bfaa6217e51102fca221df94643bea9461f840c83e8a6885f14d20bf288217d5384378a8995f15231be2a6657f548caf8a8187e14132bea86657e544c6f8a8107d48110be290217
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x151082d76354910b51854310eb7644c9109d584540825e63148109e18152cc6f16010431f44c9304426c62551109dd8552d027761551328f99353842d46355310bc98820442796094632cd153314c69c644cb30dc984504ca9c6350842b558c20c43385414132d514d314437361d41329798f548427b6544010b558c20443b26408110a718d42d027960d52219d987540425f63553209bd954210af364081109d185540ca7661d4810d6d4f5050af360509109d587540827561d5230bc98041443364314543d554c31086b7644cb108f990540825d6510c328f994544c6766114c10bc591304427665d0510ad1854310e5f6550c439bd9520082776154b30bc986404427a6015031bc58e304427a6095132c7152314c675650c421d594e51902f3648c110f4d4d304427765440109758c520437061d41329dd95310c6776155032c7953308c2756510421bc983324427a6014e219d195414437051d4142f8d4b20443565354640b918954443586054c209e19530442766114143a798e40502f3644c110bc98030443345450510bc98331443355410710ad19153c42f160d0d109d18552d025c6355320b518d424431d5410d308f593530425d6315021a71854310e7960150319d9865090a776548421cd55041087355494420bc58041cc6f26590110bcd8142c42776154d20bc58041087d3634c1109d587548ca746154f20ad99020442ad6210c42bc58053c42cd6210c32d554d519034c524c9309b189544c2f16010721add9131442766194343d554e51902756115030bc593504433b54141329e9825190a776154f20cd55054c42f1600c4219758c540827b654c03097d95320cb3854d41329758f54c863f6550c438f191534825f654c431dc98550107976150c43dc547208827661d4c109dd8554cc26f62551309ed815210e766114142c7952530827665901108f19153c823f6454f209d5845050af1639011097d8d54c437061d4142c7550430c63f6454f109d984538825e63d5020ae18142d0276650c110bc98220442746550d10bc58243442f0654c110f414d304427661152209d98754882f2618c110dcd44504ca7a60d4810bcd8c204433954d00209758f548423e64d4c208f99250cca3f6550040b658e408427965840109d98754ccad46350b10bc98a40442b66408310d954852c427661d5030add9131c42946150c439d586508cb645248510bc582524426e6215031dc5845050a7661150329d19521443584354031bc19720443e052c8110c7550430ca7665cc5109d986508cb1d5454c209d195324433a43540419bd89544431e53d02409d58453882f164c8110a75924310e3f645491097d8d544425e63d5030c7d50438ca5d63d5221bc9803244355530c7109d5865090a7561152309d587540c27965100208f19153486766115030
  | 1 => 0x427461548439ed8152cc67a60946328f592500c25d6510c319798c54082b464549109758e50d0b355454420bc99630443b043501109798e50d0ab164081109dd9543c42f1610c32097d8d544833654946309dd855210f5b43540319d98650ccb1d5310c42ae59020443b05450110dc98251902786054d219d984540427b6054d20ac59230442776154f40a718d41106f2600c5109e58354ccaf16490110ce18154082796095132bc58440c82f360549109d9865010a776550d109e580540867461553309d583514ca5e63d5321dc545300c27661141329e5805150ed663083108f590530825c6355121bc99530442f163d41109e18154486b564081109d584530823e6495132dc9805150e5d63d50209e58053086756115032c7951530823e64d4e209798f54886f16308110dc5805150f5853d41429d1855310a5e63d5010bc5805150e5c63553109d58754ccb726094420a7191324c3365454630dc546300c2f160d4f109d5835150e7561943438fd954210af260101109d984520435753d4542bc18132c427560145329e997204423c6454c218fd9153442f1600c7219e9805150e3d64d4f218f99052042d963082109c5805150f7261542219d5805150e7661d4e209d584548827b6550040a7d954310ef26090d109d18553482d46350510bc984204423e6414a109bd95210863e6414c20bc58f20442f160d5310a71894310ed46355110dc105500c63f6550441e51854310e766115230bcd8132443d26390110d5d4c5150a6c6254d10ad99230442b4644c9109e18152d06766195132b518d41107355415110dc905501075453145429e580548c63d64d4c20ad59020c42b76454d109dd85544c6766114c209d594410c67b6055120bc582210867661d4c20a718d42502f1610c0209e58054886776154c42a7191310c77161141329798c54087e12008310dcd05500c677654cb109d99440442b5648c310bcd81544427960150329e98053087d0434c110f4cc930442f265c8110c7552530823e6515132b618132cc2b4644c4319e98353886b4644cb10bc58254442776550b108f99353887d163081109e980540caf26010d10d554c53442f16014b10b518d41c42f3604cb10ad99230c423c6454f108f593538866d62150319d587530825c6355021bc181214423e6414c21c7152324ca75619434297d8d52442e46254d109759653083d163901109dd95424427461551328f590530877231540319e980540437131540319d5845050e7a60d52219dd85534875653944209d586544cb5953cc0209758f548825d6314a10b458c20443b342501109d19543c43555354420dc9845050bb14250110bc99540442f0625011097d8d540871f5410e31b658c204427561940439e98054086f160d4b108fd9153086756194042bc5844008274654c510cd95
  | 2 => 0xd020ec2f8510d8040045203c00000002940643c0000031000d007c0e0000e0010a0041302c0d001f32a4031d80e0c43c000450040200c0001556000003b401654000201f058050387c02c008a886008bc000006b0000007e018000080400c04004069dd8554483b35450110b5d8d41c42f16015310d554c53c427661d5232bc982214427960d4e219e181544ca5f6355132bc58043442f260d0510bc590204433b54d41329ed95200827b60551219d185544837351d41329d18554c82756194010dcd475050b1d5410f309ed8152d067860548439d18552cc2f364c81109d987548c31f6550c43d6d4c5050b384354041a7191320cb705114132b5d8d5444372658c1109d986500ca776155130c714e4250b655208710bc592304427b60551328fd91534823d6494332cd150514caf160cc910c754c431073454d4532bc58342442e76255110e550c43442d663901109d9865010e5e65d0d309d19532c437265081108f992544c6b7645491097d8d544c6d763553109e5825190af060509108f191534425e6314c20d514f41506f36350110bc98343442f16188020dcc85508863e64d4c109e98354ccb555394420b458e404427561942438f59353842b46454d10b5d8d42442f16094d10dc99750442756194032b658e404425f654c0309718d544829e648c1308fd91534865f6355121b518d524425e6314a10add9153c42f260d0910d514f5150b735114142bc98b504435853141429d987540825e63d52209d9865090f705114142e550c43c427665881108f19152442b96408210dc94510043695208210f498c204431c5390541dc505501067a6015221a7d814310ef06050b10dc546401025d63d5010ad19131442776550441e510c410c6f363c81109bd8953442d663903109d18553d02d76350510b558e40442f260109109d99721442b9648c210dc982518c27865501108f59353883726154031dc147504cb715150040ec592304427b6054d218f590520427a60d50319d185544c35653544209e594300827661150209d99420442756194332bc580424425c6354910d5d0c5150e796014e21cdd50514cad76350b109d584504cb3754d45329dd9532442766194342ecd91404433654944209dd8554c82746550b10bc18132442f1600c910cd552518c2b9648c1109dd85544871d5310f409e980548c67561d5220b9d8953442f265081109e98053042f36054d109d5805150a3d6414a10f898820443b2648c1109718d54442b5648c1109d587538826f654c832f4d0d304427560d4542ec59020442f0624c1109b588540c32c5250940b598c2044276658c1109e583540c63e6494030b558e40c437361d41428f99353c86b4644c710bc19540442f2628c1108f59654082746550910dc99640443b24350110cd551518c26e6215030d9548524
  | 3 => 0x505d0180034c310000d0000100002108000f001000000700744c120080000c3b07006010390040a0242f03403004000000002413360230000d004230001d0002b0d00200400000000758b0443c024c9000b600800014000140c54c3100c0c05c1902c010003e0140d0000c0140901c86020001bc1605801020040000201422000034c8010002c00c1d0000002400064b9200002e4013a51300c0100000028200040d0607701ca901008004030140217c00000091200f11c02004080000000000340000102103c04028050a009004130cc2c0900c000fb0100643c690000100c02010000b403030010002800001004
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x81c1000000137001020500500860020008002000000000000400502020008a16000000400b041600283682da551711815308348b22c6102211c5c261d5232932e030a8621d30744c5500c718aa2c020843451c55310f40a18e4aa0869852472550544428a3aa8621a212c5c06150c43ca2a6b00a7886146414d314428a39aa82a621511c95314d1092ae030a8621d50754c93044258ba6c6102218318c5250940a28e8a986210e91701854310f48b24c610221645c06150c43a60eaa1280884b37458f5044329a1ac028a872c5d260cc910d22c821a60884e0725913044268b9cc1a1221541cd4154041962e9300608871043105500c76031264982211c1d5644c110922e030a8621cb37458f2044238b80c2aa06534dcd64c81108e2e030aa6215247454852442c939ec8a0221451c55410d309a2e7b2040886a0625094044258bb4c810221451d15314d10a28eaa1887886515358031086c839a84a0221459c75410e32b24e9b1a60886926458c2044268bb4c61022183190524c9309a2e030a8621d1471550430ca98b88c0aa041451c55310c42d2086b008218cd276d0d304428a39aa820843451d1530c710c28a831a8288514735505444349380c2a1887641d1324c110c2aca2188218d147155043cc2a239aa429221451d15314f10a28e6aa08388632435805150e69b9ac9a82218c5516015310
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x20000010050030001310c8074189324c110c80731894250110a108454d600c421a108454d6014f10a8082590434c110a10835516010421911801c55310c42911809c75410e32911801c55410c32c4075189324c110a1085590434c110c20751894250110a10835516015310
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 699
  | 4 => 626
  | 3 => 75
  | 2 => 13
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
  | 6 => 2*((h/49+packedAt s5K6 (672+(h % 49)*6) 6) % 42)
  | 5 => 2*((h/254+packedAt s5K5 (18873+(h % 254)*10) 10) % 699)
  | 4 => 2*((h/271+packedAt s5K4 (23788+(h % 271)*10) 10) % 626)
  | 3 => 2*((h/53+packedAt s5K3 (3675+(h % 53)*7) 7) % 75)
  | 2 => 2*((h/25+packedAt s5K2 (780+(h % 25)*4) 4) % 13)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7ff03ffc0fffff81f1f83ff0ff87fff8c78e3f
  | 1 => 0x81ffc07ff01fc1fe01ffc1ff0ff87c00f8f3cc
  | 2 => 0x1fffffffffffffffe0001ffffffffff00ffff
  | 3 => 0xfe00007fffe001fffffffe000fff8007ff03f0
  | 4 => 0xffffff80000001fffffffffff0000007fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x49485446244a980505d2a5892c4e550c38615
  | 1 => 0x2ca19348a1c92b9600ad68b985cc6830d8b2cc
  | 2 => 0x50420a110492002aa2000122291112a300596a
  | 3 => 0x188b2c2249038ccd35318c000e6620c56d03b0
  | 4 => 0x610c30438e1c3171c9c631ccc0004306b6ec00
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfee0e0a0fee0e0a0fee0e0a0fee0e0a0fee0e0a0fee0e0a0fee0e0a0fee0e0a0fee0e0a0fee0e0a0fee0e0a0fee0e0a0fee0e0a0fee0e0a0fee0e0a0fee0e0a0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40523
namespace PEqualNP.Outside.L_meta_40523
open PEqualNP.Outside.L_meta_40523.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x440083340144018b803c03ca01a0001340450830400005a66c5017f55003fd50017fd5001fd42007f0c803f51000ff08003f71000ffd0003fd10017f15001fd4300ff84003fc50007f10401fd3100ff50003fd3000ff8c005ff5200ff88005fe54007f50401ff43007f08403fc40017f54801fe21007f90801fe4300ffd4001fd3200ffc4003fe5000ff04003fc30017f14c01fc43017f14801ff21007f10801fe31017f94c05fc51017fd4401ff42017f94405ff53017f94801fc31007f48401fe4100ff90003fd20017f54401ff32007fcc403ff30017f54c03ff20007f8c801ff41
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x226403ff5884101ffc6290803fd3210467fa8848609ffd014104f7e84210bffc2010c13fea008209ff50c41007fac890806fc608c415fe1824208bfd9331057fec090803fe4350401fea104219bfd8141007fac321023ff6510c11fe1826406ffd4821047fc86a18a7fe6090825ffaa26208ff10c31015f8ca98863fc52104016fb1a8200f7d0c31157fc40a10027d65c8469fea94860aff84121007f86520817fe420c839fea9c8205ffd972102ffec721003fd62504117e3266429ff5424204fbe87218d7fd20d0c01ff9948208fb8c832007fec899002ff63c8421fea90621fff1003204f7ca9a085bfd54cc401fea1c6211ffc81311b7fca5a1802fd618c801ff2166403bfd8c21067fc8110897fc40cc8077f30e8616ff1533102ffec819002fc62504657fb2a8603ff18e41045fec819003fe618c811fe9906208ef90d43057fe8090826fc644c411fea186224ff146320a7f8a5188afff6550861ff288862aff0c1421b7fea3a1893ff518c8037e3044209ff1534104ffe80a18abbf4050801ee21c6222ff1813204ffea8208abfe1050801fea146222ff0813201ffec418817ff6010801fe3226208ff5803201ff86290803fe3288429ffa946228ff94442007fc869089fff5010807fe0866200fdc862102ff865908cffd4090c077f3088203ff98e2104ffe80a1027fc43d081ffea006203ff5802114dfcc421023fd6010c5fffa808600ef19131015fcca99003ff614c813ffa12822fff9404300dfcc010822fe63c8407ffa8c420aff98121147fca621023fe5350c4fff9808400ff9893101ff821a089ffe5010821fe2906224bf59632007fe65908d3fc5290c077fb2c4219ffd4141047fc619886ffd309043dfea8e8205ff18032047fca6990abfc2050801ffb1a8427ffc404204ffac7a10bbfd52d0853fe9848403ff98c4101ffca2a0817fe528c80bfe32c6408ff94c43037f8a610877fe30d0433ff282822def503420d7fca6a0823ff65cc8117e32c8601bf181410efee21a080ffe6510411ff980860dff94a21115fec09907efd600c86bef9868603ff98831007fcc299067ff3050445ff8826423ff195320bfea20208bfff1010c01ff2126204fd44021047b88618846ff604c411ffa9e6200bfd854202ff8c91900fff10504537eb048403ff90531007fe8490827fd54d0c117fb066200bf98b3101ff8c018827fd43d0865ff28a8621ff1423204ffca9a080a7e650c80f7f3104211ff10131047fac321823fe6590c11ff3008609bf993311b5facba18dbfc51d0c0bfe3064203ffc4121057fea090803ff438c811ff9826400ffd0e210a7fea91885efd60104137f3266431ffd414300df8c01909ffd2010811ef218862eff14b4201ffca290827fc61d0c11fe29c8607ff4c321047f8c021806fe60d04137f322640bff94d21
  | 1 => 0xaff60508637eb248600bf5883101df8c710827fe40d0801ff2166203ef5044119f7a8121897ff20cc807ff3244203ffd0641007fe839880fff608840bfe3206422ff4c132117fea0990c7fd3050c01ffa1c6212ff5493101ffea218833ff5088407fb8848210ff948310c7f8a62082bfd3048433fe1828200bf58f411a7fca5218bbfc51d0853ff1848429fdc4242007fcc2a1023bf4390c077e328421abfd954101ffecb188a6ff6090859ffa9c8421ffd4232007fe8519027ff65d08557eb248409ff10c4109ff8a118803ff31c84117f3184203ff98e4104ffa842083bfd54c8455fe9828408f7cc04304ffc81a1827ff40d0c07fea8c8200ffd0a21015fcca2080fff6590423fea026215fdc4331047fc8621802ff63504037e3028609ff95242127fca3190d7fc20d0c59fea8c842effd4742007fa629088bdd304c807fe0864208bf1903200dfcc02104bfc654c411fe298640fff1403101ffcc810823ff430c411ffb066208ffd0e4305ff8ca90823fe538c859feb2c8413ff5023101ffca310823ff308c8037e3006200ff18d2104ffaa9a0817fc4208411ff3266221ff9423206ffca710802fd6190c0fff1864212ff14931047fcc598803fc6150801ee9906400ffd072113ffc4021023fe600c85dff2968433ff1424301ffec710827bc4310443ff8846405ffc8032005fac621002fd644c4117f3188205ffd843210dfac11901ff710c8407ff8844200ff10c2101ffec918802bc644c407fea084210ffd483101ff8ca2083bfd51c8401df2188409ff98f4201ffac520803fd424c401fe2106208ff14f32007fcc9190bffe2010c2dff2a66209ff98341047f860a1803fc6350843fe9046419ff8814118ffec0a182bfc204843ffa8806400ffd093217fba602183bfe54c84057f32c620effd4f21067fa4110803df438c401feb1a8406ff5482102ff8cb9080ffd628c4037f3006403ff5044106dfacb10817fc6110863fe1028614ff54a31047fcc999003fd6250c13ffa00841effd4f4104ffe87a1003fd644c811feb2c8635ffd4343007f88518823ff30d0c117e31e4200bfd8943025fac010867fe1050413dfa008600ffd8931047f860218237e650c863ff0828603ff5923103ffaa19080ffd648840ffe8864222ff8413201ffa2120827fe65d082dfea8e6200ffd89410c7faa42086ffd5090413fe32e8405ff1804204ffec5a080ffd2108401fe9904200ff4ca31047f8a698827ff4210811fe21c6204ff500210c7fea4208dbfe51d0c01feb226200ff50c21045feca1902bfe2048407fea0c6222ff88132047fca7a1817fc2010843ff2046435ff94343007fc86a10b3fe6590807fea08620eff9972118ffc40a1823ff6290c59fea9c8405ff1482108fea20988d7ff10d0c017eb206203ff1052104ffe8021827fe4310801dfb
  | 2 => 0x41005fac710803fd420c40bfe3288408ff1944301ff8ca1880ffc600841dfea9e422abf5814201ff8a3108d7fd30d0c5ffe8808600ff18d4101ff8a21084ffd208c409ff2004208ff50f32005fac7a10a3fd53108053f3288611ff141310cffa60a089ffd1010801ff30c8408ff54c4316ffea1a1033fe5088413ff32e8600fd0c72116ffca1a1003fd6348419ff9844234ff1464313ffaa021026fc64484017fb1a422eff947420afea21988cbfc6550c5bff8868408ff10f3202ffc64108bbfe53d08017e3128619ff54141007fe869880ffd60904077e32c8203ff1883104ffc8020823fd640c807fe3284234bf5964304ffea9a085bff54cc447feb2a6409bf9913118ffa20a181bff540843dfe29e821aff54d4110ffc41190cffd2090c07ff108421ebf5974107ffa4018823fc430c84fff0808422ff44132105faca19076fd60d042ffe2808208ff14f31197faa6a1803fc3250419ff1044203bfd963101ff8a220823ff64cc801ff1908221ff84232047ee631880ffe630842b7eb066209bf19321107fea819023fc308c831ff2908203ff5943101ffea22080ffc6588407fe3048200bf58a3109ffc811886bfd6550411fe32e6203ff106211677ca921067fc20504117e32e621cffd4e41045fec99900fff650c411fb98a6203ffd92210cffa20a0826fe64084637eb028603bf19441137faa599027fe60d0c137f3148403ff8422111dfeca99077f510d044ffe9808405ff94821067f86110803fd42cc845fea826408ffd933101ff8a31880fff5108411fe9906409bfd9442005f8c498802fd639046bee9868600ff8ca31157fac0a1003fc644c843ffa04642cff552421677aa921003fe644c415fea824203ff8c621005fcc421823ff6090c1fff2006208bf98e4319ffc8121803fc3248417fea9a4215ff10331005fac918866fd6490463fea82862dff48342007fe6490857ff20cc43ffea006408ff50c32047fe649900afe6510811feb286402bf99741067f84110833ff4088411fe3166225ff5033201ff8a218823fd3010c13fe2a48208ff0c343047f8c3990abfd5050807dfa0c8205ff0823201ffacb18803ff430846bff106862bff54d4203ffcc190823fd65cc40bfe3046420ffd4832057fa2090803f731084017eb1c8408ff8c831137f8a59900ffc6010411ff21c6400bf98831005fac990823fe6510c09fe2804200ff98941007f88498803fc624c4017eb088603ff0c6210a7fca518803fd420c8137fb068200ff90e211a7fea921897f510cc8037f302840eff1532104ffe862080afe658c813fe32e8608ff58a431a7fea521827fd63d0413ffb068403ff0424101ffc83988d3ff5190c07ffa8c620abf58a2100dfcc11088afd638c8017eb108208ff10d3104ff881a089ffc3010801fea0a622aff4414204ffc85a08a
  | 3 => 0xfa048624ff54e32015fcca19017fe320c82fffa808222ff58132007eec299047fd204c411ff21c621aef9514106ffaa71085bfd52cc44dff2966428ff54442047fa6598827be5410813fe216822fff04043005fac39900ffc105045bff1068409ff98c4201ffac810806fe60904077fb284208ff10f31007fe651085fff30104013eb28860fffd0031007fa8398806fc6008409ffa804209ef9504301dfcc319027bf40d0807ffb20420eff14f21005fac5988b7fc30d0813fe21e8208ff58243085faca1880ffe608c4117e326622bff5954201ffca210822fe6348433ff1828207bf5832104ffac22102ffc544840dff2984228ffd4c42027fca01088ffc544c811ff2186203ff9444101dfcc3218bff71010c117fb048600ffd0a31027fe601080efe61cc813ff32e821eff54b4104ff8a8a182ffd5448431ff2988203ff04121005fac52188ffd544c8437f3106403ffc402102ffecb190cbfd5450c5bff0868403bf1943110ffa6119027fd6510817ffb2a4212bf59531045fcc71080fff1010455fe3028417ff9404101dfcc210827fe5410c13ffb068213ffd4231047fea621827fe54504037f302621affd4d4104ff8c1a1883fd520c8077fb286200ffcc521117f820990d7fd50d0c13ff21e8408bf1973204ff881208affe6550813fea1e8209ff1514201ff8a298827fe5450807ffb046208ff182430f7fea5a0877ff20d0411ff29c6203ffc403108ffc8098803ff414841fffa806205ffd8f2104efcca2100ffe518c415fb8824200ff4cb41057fc6090817ff20c846dfea9e860cff4c221007fe8418827fd60d0c01ff1926200bf5843201ffec518823ff43cc8017eb20640bff54521157f820a104ffe508c445fb8826412ff59531045fec01902fff5348411ff9846203ff18c2118fee20a187ffc500c80bffb00642dffcc34212ff8a199022fe63d08077e30a6403ffc423102ff8a419017fc420c8037e3068209ff9524105ffca890803fd42cc465fea8a8604ff48021157fc60a1027fd6010813fea168203ff4c621097fea29888fff534c8017fb0a8623ff545320e7faa9208d3fe5190c07ff2886209ff9514307ffca018823ff300c4037e3008232ffd4d4304df8c919027fd40d08337eb028209bf992320dffc612080ffe6590407ff20e4208ff94c3104dfcc821823fe5390c35ff32a821cbf59641015fccb218abf710508137e32e8417ff4804114ffac121017fe42c8407f790c4200f718d41007fe64a081ffc40c8411ff9848609ff1084101dfec91887bbd54d0401ff31e4200ff50d3101df8c2a18afff535086dfe2968602bf99742007fac2a10cfff1090c017fb126212ff94931097fea4988c7fc5050c01fe9926202bf195420cffcc0a08affd51508057f32a8603ffd9421005fac99880efe6110801fe2166403fd904
  | 4 => 0x803fd41c8411ff2986400bfd93210fffca019017fc6390807fb884421cff14a4108ff84098803be425081dfea964203fe58031047fe6019093fe548c8037f3066208ff94f32047f8c199097fe50cc8137fb068424ff5463204dfecba0823fe434c401feb264223ff9953206ffca910873ff5290407fe988621fffc4032015f8ca99013fe2008411fe3088625ffc433204dfcc821003fd4290413fe2a68603ff58c41047facb9908bff604c8057f32e6433ff942430fffc8019002fe6290411ff3066409fd5044104dfec02107bfe52d0407fe3246203ff1042101dfcc221827fc60d0401ff2128409fbd0a4217dfac021847fe604c4077fb204205ff18f21005b8c6a080eff608c40bff2906435ff8c343047fac42187bfc52d042fff1008200ff4cb2101ffa2110827ff41504077e3246223ff9513208ffac098803fd43c845bfe9868405ffd824210ffa2119027fd40d0411ffb008604ff0c02103ffa819085bff52cc4037e3066412ffd9531047fe879880eff6388411ffb108631ff8c14301ffc20108cafd6550c35fea8a8208ffcca321b7fea7a18c3fd5110c2ffe1808203ff5822104ffe8420817fc610c80bfe2964203ff1922101ffc621080ffc640844bfe9066409ff98b431afee21a1857fc50cc427ff104620effd4b21007fcc89902bfd6048407fe20c6208ff9824301ff86210847fc604c44d7eb2e641dff14341007fe849880ffe101040bfe3286400ff50b2101ff4c018813ff4008445ff1826416ff14b311877aa821827fe60d0827fe1046208ff5933104dfcc990803fe644840ffa8864205ff0802104ffacba080afc658c8037f3008611ffd413115ffaa8a1002bf644c407fe3108217ff0804101ffc6218803be431046dfea8e8601bf1804304ffe802080afe6548413ff2a6860effd5321007fec2a100ffe514c401ff2184208ff0c23101ffeca208a3bd5410811ff9826208ff99432047fca698827fe43104017eb24421aef5514105ffaca90873ff549041fff1006211ff9413101fbc629880ffe108c467ff1048609bf1974101df8c61080fff104c413feaa08401bf98143045fcc7210b3ff549084ffe0808409ff15042067faa110802ff644c407feb184200efd9131047f8cb9900ffc410c413ff2a0841bffc82410a5facb1880fff631041ffe1006215ff50331047fac39906bfc6550459fe29c8400ff5923209ffe8118897fe40cc813fe2a28209ffd8f410d7faa8a080ffe6010415fe3024220ff144320dfea2120827fd5410c07ff3246220ffd443204ffecba1823fc300c413fe3168208ffd873213fee2021027fc5410c43fea846408ff0c243047be619900ffe100c453fa8848403f74c431007fec890867f71050411feb066200ff0ca2119f7e8121817ff648c863fe0828600ffd0821007f88598823fd43cc413f
  | 5 => 0xc3200df8c098806fc6090801ffa106418ff54c410bffa6020823fd610c813f72108400ffcc841077fea3908bff51010c13ffa1e8208ffd9643045feca2180ffc6590413feb068201bf18331005fac5a0873fc5390401fea1c8203f7cc43101dfeca20823fd3090c13fe31e8203ff44021007fcc6a0802fd6310417ffaa24208ff0c03200df8c099027fc4290427fea846200ff9094101ffec018803fd639083fff0806409ff5974317ffe4021817ff2010843ff3046403bf9862104ff8c3a102ffc5348413fe32e8200ff90a4111ffea899097fe10cc8077fb048203ffd8e41047f86518853fd538c407fe8808208ff0c831047fe651887ffd200c8117fb2e620afd44121055fec090803df63504137e32e8616ffd473115dfecaa1002bf644c813feb0e8407ff14321047f8a6a1857fd20cc4077e32c4208bf18d410cffe40a0897ff40cc801de21c8205ff14a4201dfcc32087fff400c807df20a8208ff58b31027fa6010817fc42c84037f3068603ff4423101dfec91088bf5104c82dff2966209ffd8b43047fc879901eff60c84017fb226405ff0803219ffaa12180ffd6390401fe3128231fd4414312ff84199003ff644c411ff218640fff54031014fccb90857fe40cc411fe30c8600bfd8941047faa6188d7fc10d0c01de21c8421ff8c23200dfcc199023fd5390c1d7eb2e4208fbcca32006facb90823ff320c413fe2008405ff9084201dfcc218802fd63c8449fe2a46401be9803115ff8a6a1027f74190407fe9884209ff10e41067fc61108c7ff2050c07ffb206209ff1024204ff8802180fee2148423ff1026202bf9974304ff88721067fc6050401ffa166403ff44031007ea421080ffe4150439fea94822cbfd9642167faa521026fe648c4037e300842aff98142005fac3a180ffe4148415ff9024209ff1014119dfac121893fd548c845ff902640dff1522101ff88298823fc64cc44fff1808424ffd4e320dffa81208cbff6550c077e3204213ff4c231047fec59880fef2108413f6a108401bf9804119ffc2121823fc304c40bfe3264209ff90341005fac8108bbfd53d0801fea1c8403ff5462101dfcc3188027d6510843fe0846405ffc8242045fcc621847ff404c4057e32c8400bf5912101ff8a398823fe32cc459ffa94841effd474116ffaa1a1027ff4250823ff0826212bfd9531007ee6390802ff6350807ff18a6201bf1823201ffe631080ffc1088401ff2126400ff90921005fac610806fe6048407fe28e8200ffc8521137fca39900ffe65884137fb068600ff8cb41157fe40a1003fc43c843fffa806401bf98231007fa6520846fd604c415fe2024209bf99221047fa601880ffe62104077fb04420dffd4e2110fee211900fff418844bffa866420ff9443214ffa8121023fe65cc845fe2026409ff10143005fcc5a0
  | 6 => 0x1dea108408ff50c43047fa6199022fe630c80ffe9064205ffc823202ffec3190d6fd60d0c07ffa0c6200ff10d21087f8a818803fd3250401fea0a4203bfd903104ff8a921823ff60cc8017eb0c8415ffd0331007fa86a0833ff208840bfe30c6418ffd4c4104ffa802184ffe308c413ffaa68608bfd8332087faa81880ff7108c411fe9806434ff5524302ff8c621047fd504c43bfe1068209f7d0d4304ff886a100ffe6508453ff204841aff1494104ffe81a08a3ff521082bfe1066221bfd8232047f8a7a18c3fc5210c01fe992421affd9541047f864988c3ff5210c47fea926408ff9873201ff8c110803fe64c84057f32a6233ff0424301ff8a320803fe3290465fea928603ffcc431045f8ca21823fe43cc457fea928414ff9523101ffcc018873fe529041dbf32e4212ff54d3101ffacb20893fd658c813fe2a68400ff50941047fc601880fff51904137f320641affd494101ffc8310887fc408c801fea1a6426ffd533200df8c19080ffd6508401ff2144203ffd88411a77ca92189bff52cc867fb8848603fdc4031047fc6121827ff5410c13ffaa0840cff10221007fec6a089bff51cc811feb26641dff48341007fa869082bfd4048401ff31a8408ffd4c31117fa809904bfe654c463fea028607ff9032101ffecb108cbff5450c13fe3068426ff1473211ff8a499023ff30cc813feaa6841dffd434104ffac621023fc30cc801ef9946400ef191321577a80a1043fe540c417fe2924208f7cc83201ffaa2188d3fd5190c057f3288635ffc83430cffec0a0822fe63d0411ffa9c8607ff5832104ffac3a18cbfc5250c11ff3086403ffd8041007fa8490827ff65d0407fe28e4209ff9874305ffea490817fe5290811ff29e622dff0434208dfac718803ff42cc447fea9a6403ff5944102ffc659080ffe628c401fea126409ff98b41047fc8699002ff614c801fea1a8408ff98331045f8c6a10b7fd10d0801feb1a8200bf593320effe61a0803fd614c8117e31a4228ff14c4201dfcc2190b3ff519082bffa866200fd1853201ffe4310827ff4390409fea80420dff5522101fec42108b7fe30d0807ff28e8202bf9954101ffac118802f9600c413fe206862bff1494201ffca3988b7f710d085dfea8e8402bf1952108ffa6098867f5105043fff1006403f7cc63102ff86410857fe50cc44ffa8808401bf9834204ffe872100fff10cc407ff328621affd514115ff8caa10afff5250853fe2848406ff54c2118dfec0a1823ff65cc401fe1908231ff18143007fec4a1827fe54d08017f310821bff14241007fe6410877fe50d0411fe2988622ff981320d7f8a6a080fff10d0413eea188601bf9824302ffca590803fd6150c497fb2c6425ff88332007fe879088bff404c80bffb286408bf19432047f8a69905ffd501040bffb046408ffd
  | 7 => 0x9080ff71010401ff21e421dff4c341007fa85190cbfe5250c13fe21a820bff9492106ffea5108237d6510c017eb088409ff10342007fa8510817fc20c8407fe082622fff14043145faca2108ffe524c80bffb0c8419ff1414104ffca9218dbfd52d0c13ffa148232ffd454301ffcc5208b2fd6590813ff3008425ff54332047fe6298827fe43d0417ffa8a4203fd0c42111ffea2990c7fd6050c057e32e4209ffd0a420dffea120803de324c837ff2848200bf58a4101ffaa22080fbf41104057f32e6200bf591320a7faa918803ff6150c07fe3148229ff94242007fe8699023fc6210c13ffa1a8411ff8c131097fea6988affe5250807ff28c8202bf9942102ff8c321047f7104c407fe320621cff94e4101ffe8218823fe6290c137e3226405ff90a3201ff82018803ff4348415fe2824200e750c43065fac1108b3fe5190845fe282641bffcc24101df8c9108237d650c807fe0808205ffd8442015fccb908b3fe5390813ffa1a8603ff0402101ffe2120893ff548c853ff984841eff94f4104f788621003ff42c84017eb0e8412ff95131187faa421803fc6150c017f3146215ff8433114ffe2121002fe62d0c55ffb028402bf1954304fde84a100afe650c42fff1808209ff5084204ff88621027fe63d0465ff32a8605ffd9321007f8c29901bfc540840fffa864205ffd964201fec6218802fd6348407fea8c6206bf5942110ffac119017fc521080bffb288409ff15041077fca7908237e6510c0dfeaa04223bf5953201dfec020803ff6348407feb2c4209ff55041047fac199023fe3010c13ffb1e8400ff5863204dfecba1802f4614c813ffa168202bf9964203ffca190833f5108841bffaa4421fff5403201ffca390823fe6110c11fe29c6408ff54c3204ff884a083bfd65c84013eb286403bfd8031157f8a0a1023fd6110c13fba0a8208ff1833103ffe6190877fc30d0407ff9884208ff54f3204ffcca21062fd651041d7fb2e4215ff8833106ff8a71080ffd600c407f69084209ffd8742047fcc421823ff30cc451fea908419ff501410dffa412080fff10c8407fe20e6214ffd4e3101ffe8210803fe6390809ff180422fef5004301fee2010823fc30cc407fea884235fd443430a7f8a918803fd624c411ff9926200ff191210effc41a0806fe6050447ffb2a6429ff4824212dfac19900fff4110407ff3206203ff9824108ffa209882ffd524844bee9866403ffd8021045fcc519026fc6510807fe32c6201bf1834300578c89907ffd100c80dffa98421aff549410477a8621827fc63d0869deaa48600ff1092112ffa2199003fc424c80dff2a04200bfd9232015fccaa10cbff5250c07ff98c6223ffd493200dfcc099022ff6590c13fea008409ff58b41185faca21827fe541043bff086821abf5954101ff82118823fc434c80
  | 8 => 0xf19541087fea818806fc60d080bff290842aff9414215ffca6a105fff20104117fb2e6403ff1823104dfcc89082efd6548411fe298622affcc142157fe20a102ffe65484137fb2e8403ff9963101ffec120822ff6010c11ff32e622effd4f4204ffcc3a100efe61d080bff210420ffd4403113dfac02105afd65cc4377eb048203ff904211b7fea5a184fff208c411ffb088626ff1533204ffac1a1027fc62d0c5bfe2868409ffd034201ffac818806fe608c811ffb0c861bff88241057fa4090813fc400845bfe1068401bf1812104ff8a9210a7fe209080bfe2146419ff9014101ffc8220803be4390859fe28c8409ffd53420affa219883efd600c413ff2008620ff15032117fa4099027fc40104017eb246433ffc82430dff86120806fe6090811fe21c6403ff18a3118ffa40a18d7fc50d0c43fa8846420ff5503214ffc21210aefd6550807fe28a8203ff9802104ffc84208abfd205081bfea944226ff553320d7fea2a08c7fe6050c25fea8a6229ffd4242007f885108a7fd1090853fe0848409bf9903101ffec520817ff6310851ffa888403ff84241007fc64a08c3fc5110c017fb224229ff0c2420affaa19880efc658c407ff908421eff54f410fff8201903fff200c411fe1966200ff0cb41047faa79880ffe418c45dfe29e8425ff04332007fc8418806fc6050811ff9906422bf5813201ff88390803fc4388401fb90a4208ffccb310effaa1a0803fe428c407fe28a4203ff5062100dfcc018822fe6310801df21c8213ff10231007fc6490803fe6348413ffa04822dfd443420ffee2019093fd528c811ff1806407ff8832101ffac418823fe30cc801ff996820dff14a21047da641902bfe4048411fa9886209ff58b4301ffc82188cbfc5150c45ff2026422f7cc13204ffec3a186ffc2090401ff21c8225fdc4332047de64990c7fe4050c13ffa048408ffd4f3202ff84121023bf4310c49ff32c6400ff90e4207ff8801880ffd601040bfe32c8430ff9484311ff8a29901ffe10c8441ff2a06421ff50232107faa219017ff60c8461ffa888600ff50e32047fea619022fe630c455ff202841aff949410effa21a089bfe54cc801ff1926400ff58f21137faa39901ffc30c84057f32c4209ffd0c4204ff881218afff545085bff9068403bf1854205dfeca9080ffe2148407ff3044200ff4ca2101ff8c6208abfd4050807ff18e420cff5022104ff880a10abf510508137f3208203bfd9641007fa8710823fc6290c07fe31c4208ff196430cffac0a0827fd431080bfe2946412ff551310dffc8120827fd65d084ffe2808424ffd4a3204ffe86a084bfc544c4077fb0042029f99442047fa6198803ff414c401ff30a8609ff9844215ff8a2a1023fe640c857ffa8a8408ffd0c4303ffe8190803bf42908117f31c8213bf5823101ff863
  | 9 => 0x3404d5500300c5f00683d0020180b0d20065040002e0322540b81600201c0382b1bc000b700000801000818000028aa97a0b4290010040181b80006e01c144178180dc81118000000028028000000007403c02e3b4179560000980000900001c0200100e300000013f41bc030000141340700004a5e8039cf024014080000080002e0aa0020a0cd0240000280e05e02e3f5c18060080880182800a00001a9e01e0100800000a1c00b00008c1701c82d0a26802103a00000cab001080290020d10100541880917e3ac018130740d0078040003a86b00803e0007704800e014000003700480000301600c090090060308c8ca0020001900003a00800a4db2a018006ac0082b40d00005e014148041845bc000053300380b00216e9240b04905e000660020000004dd0e0011c8ce8070082600380500a070228060000001d3e1008010000af00e4d8005cc16c0000183e00000088808002005068660cc00858918004039ff0e702400c1d0080000040004a0120081912a942090010670081640085e4ee0901f805d8c3981401c1284540002b02e0c13506d0100140b07c916114058080020ec000050000060b5bb08005dd40210000001780020e0089a014012000000500320800f85d0160040381700802006813042014000d20ae0b03881b21a0909581100a94809000030014008002c2059080660000000203a02a0000900046c3c07181500225c0a01401c0240681d02e0b4080230160080f824002010038fe01000401821004084a101c000000021630b431afa01900a0843e0129480140f800035228618010003a4bd80195099002003094bb000000658060029760322ac0002800429016000004031f804300e0768f1080060040c88b002008b63480001b8418000001880186c06054c9d00a31c0109a81503014c049890000004d81505741c050020000000a00232e4a00000f0000080181300015c7401e01a06c000190fa01017808000054950140000044f00100404001a0d01c0459e13f0121181500000a0440200108400cb180000a0280005625e078000070320440400700003c0f80000468c01822266014010400de23ff9453215ffca2a102bfe50484017f3148603bf19031005fac5a1823fc64cc813ffb06860affcc121055fac090827fd40d0c45ff2826419ff48141067f8a1108bbff52d0811fe29c6202bf9964102ff8c1210c7fe5050c55ffa828435ff84343047fe60a18cbfd6550c07feb1c4211ffd81311affa21a1817ff2008411ff30c8601bf1824318ffe20a18cfff5090c07ffb184233ff0824319ffa21218bffd2010c017bb0a6409ff90042175facba100efe61908037f3064213fd44231007fcc4a18277d65108037e304822dbf58342007f8c4a1823fd6510c017eb10862fff54043007fa63908bffe1010c51fe2888402b
  | 10 => 0x24b80d0100043a96901c3700000b006170018824700a00000513e000120380121100080001e04cc383303801c8700901a0000a0000000000b82201c1287a1bf0382531e9020183580006d000072de11600c020288000d201412803000000000790a23f80004401a24c5a000006ba84a09f0020e7c089500500b7f80019c000000016fa0080080e2880042593f01484c000a40520182d041026064c9001038060010980020143180c23e0300001000e0002a04903ec0b51003010650ff86210a9ae0f0030d604abb00609c0013a8010100380780a0
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc75d913104ebe731913200cfe7058a41296be53d9131006ed5298a43006f750d8532006f710d894304ef4415874300cfc7058443006bd6419121004ff764c841006f5101893101eef62c8521046dd7518d4100cfe7058c4104ebe7519132007b764d853200675105972102cff75d9232005df735073100cfc7058a3101eee2198841006df5118d4104cff76d0e21004fd7558f42386bd6510e4201cf7701853204ebc6450931006dd6018d4104cbc7458d2102eee72d9321006be20191320073e7519132006bf6450921004fd7059221006dd30d8d4200cfe70d9321004fd73d932101ef71059221006bf64d09210479f6150c4301cfc7458b41014fc7559021014fc7558831004ff764c94102dec724c7210057d750c921046f4315873204dbe748c841006f51058e413bf9d5250c4301ef5760c721006dd5358c21046dd7218d41004ff705923204e9c4358c4104ebf7519132006dd5358e42004ff7558f4200cfe70d8542006bd51d91310057d7510a31014fe7558f41006bf521913101df6710c9410067e7259443004ff7458432006bd6450a2104eef4258b4302fcc204c832005bf744ca31205df71d0c31046ef7258b312667c7159721014fc7559131004fd7018941006ec20d893104e7f4259442006ed6250831006bf405902100cfc70d8532006dc60d8d4100cfe7098b433af971050c43006bf64d0932044ff764c521004df735913104ebe641913101cfe7198843006f71058a43006de1018d41006f4501853201ebf745922100cfc7058c41006bf6499132006bf64d8532004ff7358742006be7619132296bc53d9131004fe764c94102eec32988311f6bf10191311d5f770cc421004fd76d0b31004ff70d893101fb44150521006f71098b4102cfc72590310e57e750ca41005bc744ca21006df73592313af9e7050c4301df4714ca41014fe75d9132006bd5019131006dc6318941006f440d8532006bf648c9311f6bc2119131006bf649912104ebd7519132046de6350e410077565cc721004ff7458e2104ebc6410c2100cfc7098a4102cff7098b31004ff71592320079f30d9132006bc645853200cfc701894101ef7701853202df770c8521014fe7558a410f67e65d0721045dc7350b32014fe7558c41006f65418532006bd5319131006ed52d8931004fd7610c2104ebc64d05211f7d43110c2100cfe7059132006de5018d4101ef762c8521006f460d8532005bd74985322667c4159721004fd7650932005de7618d41044fc7650b31006bc70d913101fe6624842100cfe705864202ebc6459232006dc5018d41006bf60d9131006bf65d9132004ff7259231004fd709884102cff768cb41004fc7650931006f51058d21006f510d8d41004fd7558d21006bc75d9132327ad525084201cfe760c84104e7d42594420067d65d0832
  | 1 => 0x8d210057d750ca41004ff765093101cfe76d0921004ff7559231006be545922101ef66118542006bf51d9132005ec724c52102eee72d9232006dd30d8d41046de63cca2104cfe7498b31004fd7398b410467f7359443014fc75d8931046df7218d41006bf645053101cfe7690a3101ede3158c21005dd7390a3102ddf724c8321ff9d6390e41006de70d8d41004fc7650d21005bf744cb41006f8755803129edd76d0e3101cfc764c84102edc6398e4201ff2700c72100cfe705864301cfc7158a3100cfe7058f2104edf4358f42006f5105922100cfc70d9131004fd70d85430479d6050c4301df67190a41006de40d8d4115e7e6550b2102eee628ca3104ebe6419121046de63cc721006bf75d9131006be54d9121296bf31d913101eec2158a31006f574d85320357e7510c21005bf744c921004fd705843204ebc64d0931006dd51d8d4102fce52cca3204ebf701913204ebe721913104cfe74d8931006f56018532006f510d91210057d75109210067d105943202cfe72d8d41004ff70d8d41004fd765083102ebc64992320067e705944304ebc64509211efe432d85320067c7059443004fe76d052101ef71058a3101cfc7690e21006bc7458d211f79c3119131006be601913229edd64d0e31005df73591210067d655932102eec4298b43006dd3058e41005bf744cb21046dd76cca3201edf7358c211f6be3119131006be54d9132004fe7610931046fb3258031005bf7458d21046f8735803102dbd76d0a4229edc42d8d4102cfc7259131006bf405932102e7c2059721004ff7558743006bf72d9131006ed2058843207d710d0e312779c439083129fd441d8d41006dc75d8d41004fd75d8f21006f51058a43004ff7559021367b510d0a4202ebc4259032006bd20d9131014fc7558c2122fe552c8621006bd4059021005f57190d41004ff75d8d41004fd7058841006f77159131004be7619131006fa52580310079e7250c4300cfc7058e42006f5611854201cfe76cc84101ebe4159231006bd75d91321eef7630c72104ef741584430067e735972102dec7250e42005f5720c72101cfe7498b4101ebc4159021006f51058b43287d74118d41006bd6410f21006bf70d91321ffb71090c41006bc6019132296bf71d9131004ff75d893104f3d7510e4104eef7258b43006be5119132014fc7559032004fd70d912101cfd7158c21044ff7258c2101df671d0d31046dc7218d41005ed7290d4204cff7650e3100cfe7018931014fc75d8941014fc75d8d21006ec20d8941046ef3258b3102e7c21594420479e6050c4302ebc64593212667c1059721004ff7158c4200cfe7058442004ff7059032276bf6490b32004fd70d8931006dd20d8d4100cfe70d893102cfe7258c21006f5105884101ef71059031006bf73d9132006df6398941014f
  | 2 => 0x6df5418d413af9c2050c43004fd7059132006bf5019132046de63cc84102cff701894102cff7598b43005f571d0d31005f7714cb4102e7f635972104e7e415944204ebf6590c42006bd73d91310067d654c72101ef9415803102e7e75d932101cfe7198a410067d65ccb21046bc435933101cfe7690d410d57e75989410079d30d9132006f565d85320147e75d9321005bf744ca4104cff76d0c21006bd5418941004fd701894302edc3258f21004fd75588430467d3259443004ff7059331006bd64d083104cff7659321004ff705843204eef4298b411febf6418543006f51018943014fc7558f21006bd5458442206df60d0e31006f710591211f5dd7610e31286dd76d0c3101cfc7650e21006de75d8d41004fe768c941004fd7058e413af951050c43004fd7558841006f51098b3101ef951580312676e2159721006dd54d8d41005ef7250d420067e105943202e7c725943201cfd7159021006ee52d894101eec21988312079c41d8d4104e7f7459443006df50d8d41006be40d9131004ff7558442014fe75593210053d7510e4201cfe7690c2102ddd76cca32004fd7690f2101cfc7610e210067d1059442006f77159132006bd10d9132006bf20d913100cfe7058841006ef629893100cfc7058732044ff7610f21006bf7650842006df65d8d4101df67110d2100cfc7059121006f51058831006db4358031004fd760c841004ff7258743005bc744c521206de21d8d41276be43d923201ef7109883101cfc715923204cfc764cb412c6bd6590c41006df3058b4300cfe701894301cfc7650d3104ebe6410e2101df77648421007d71018d41014fc7558841006f75318532005ee72cc52126ebc32191321eef5630c721047d66110e3102e7f20597211eef663c862100cfc7058f4202cff7690a31006bd6450831046be4359032005bc744c7210857e7510831004fd7698f2102dee72cc721046fa535803104ebd7219131046de63d0f21006bf6410931046f8535803102cfc7259331014fe7558d210067f305972102cff74590321767e65d0b21006df634c921046fa325803102eee62908311eef73198a31006f543d8532047cf724c832006f71058443046f73158643014fe75584433bf9c5150c431f79f6410e31044fe7498b4302edd73d9232006ee52d8931004fd75d9121006bf64d0d31297b57190e410079d7150c43006bd405932102fce524c83204ebc64d0921004fd760ca4104cfc7458432006bf645893101ef93158031006dd3058b430067c705943200cfc7058e21004fd7058c41046de7518d41006be4398841006bd30d9131007b510d9132044fe73590313af9c1050c4302e7f2159442044ff764c721004ff7558432014fc7558643045df7110e3102f7575c8621006bd64d0a21045de74d0e310067c305972102cfc72d
  | 3 => 0xd7259443006bc52191320479c4350d3102cfe72d912104eec4258b41004fe7690d21044ff7359031004ff7558643014fc7558a31004ff7359131006f553d8532006be20d9131014fc7558e41004ff7558e41006be54590313af9f2050c43006dc70d8d41007b71019131004fd71d923201ef475185321d6f443185321febe6190c41006be5019131004fd7558a4101df4715092102ebe6250842004ff705874201ef47158c21014fe7558a31004fd764c5210067e7059442005f47158943004ff735884102fae52508420057d7519132006bd72d9132006f5105903101edf7358c41004fe7610d2102e7e3259721007d4714c832006bd101913137fb71010e42046dc7118d41006f761985421d6f563cc42101ef4731853232dbd755084202f5e654c832276be4398b4311d7e7519132006ee625083100cfc705864202e7c725972104f3d6590c42205dd71d0e31006f550d853204f3e7510e42005f571d0831004fd7058f42004fd7058f41006f65018532046f9735803104ebe711913123df5700c72101cfc7158e210067e715943202cff7098a43004ff75588431ff9e31d913104eef4298843014fe7598a43014fc75d8d4104cff765072104ebe701913229edc40d8d4124776650c72101ebf74592310147e7598a4100677105944304dbf7510e42006f452d853202cfc7610931014fe75587430063d6590c4201cfc7158c2104ebe5498b41006bc54d913201cff7158c210467c31594430467c435944302cff7098b4104ebc6450d32044fe73d9121047da60d0c3105d7e75c8521004fd709883102cfc7258c41046de6390e42206de51d8d41006df6390d410067f7059432006df6018d411edf770cc721006be10d913200cfc7058632006f51098b410067d735944202cff7018931004df764c83204cfe74d8f21004ff75d913102d7f7659721004fd7058a3101ebe41592211febe21d9131006ef628c931006f630d8532006ef6298943004ff735902101cfe76d0831006ee2018941006d71018d41004fd7558642005ee72d052101fd431d0531004fd7610b3102cfe7610f2104e7c7459442006f710d8542004fd76cc94104cfc7458632006fb7258031014fc75d8943004ff755922104ebd76d0a42044fc7358642006bf5119131006f674d8532006df6390d42004fe7650931005f77150d31006bf64189311efd4430c721006bd54d913100cfe70d8d41006f7715912102dee72d072102cfe725902102fce624c83226fac321913204ebc425884300cfe7059331006f642d85320479c6150c43006de20d8d410465f3059443006be50d9132006f7541853201eee2198a41005f57018532005f7714c821004fe76d0d2102cff7690831006f451d8543006f53218532046dc634c941006bc50d9132006df6310d2102cfc725874300cf676c8521
  | 4 => 0xc4204ebc6490b3201dee72c8521006f954580312bebd6090c4104ebe6410a31046dc6390d4204f9e7390c421f6dc4118d4102cfc7258c2101ef71098841006f765d8532006bf50d913101eec21988411f79c4110e3101cfe76d0d31046dc634c9210067c1059443044ff7658f2101cfc7650921006ef7258d2102e7f645972102ef42158432044ff7610d21004fd72d8543006f5109884302eee5298a43004ff7458632004f770d8532286dd64d0c31006b46418532006dd4018d4102fac4250a3201df47150a4101df4714c841006f51058a3102eee7298b3105d7e7510d2104ebe64d0e31236f7600c721236f5600c721004ff7158e42006ef62989410067d20597212b7d510d0e310757e7510f2101df47150c2132dbf7550842004fd7498b3100cfc7059132006df6398d4202cfc7598b43005ee7210d21006bd545864301ef7721853204fb66190c4104cff7650e32006df630c94101eee2198a3102e7e7598a3102e7d75d8f2100cfc7058f41004fe76d093126ebd6390c4204cff76d0d2100cfc7058432007b710191322779f3010e4200677105943204ef44158742005f570d8532004ff7650b3101efa71580310c57e750c841006bc65d913204ebe6410f2101efb3158031006bd60d91322a79d4010e31006bf70d9131006f71098843006bd64d0e32004fd7559131046f77158732005f57110d21006be7619131004fd7558e210767f71597210467c73594433bf9e5250c43004fd70d8f21366bd60d0a42006be30191320067d105944304edf7358f41004ff75586422bfb51090c4104ebc64909321f79f6310e41006bc40d91310067d6550721006dc63d894102ebf629094204e7d40594430467f7359432006bc50191310067f7159432007d730d853202ebc649932104eef6290942046de6390e41006f710d923204e7c4159443045de73109312debd6090e410067e1059442006dd6390e4104cbc7458c21046dc7418d41004ff70d8d21004ff7558e21046df7518d41006f752d8532044ff7650e410067d6558f211febe51d9131006be4398a41006f84258031006f74018532004fd7518943005bc744c8210057d7598931006f55218532044ff7610e21004fd7598b41006f675d853201df67190e41044fc7359221004fe7650d2104ebf721913101df672c852104ebd701913204dbd7690c42014fc7559121296bc73d913102cfe72d8543044fc7359332006f510d89430067f7259443004fd7058c21006be101913102cff7598a4304ebf6590c41286df4018d4104e7f4059443355bd709094204dbc744cb4129f9f4010e3104ebc4358c41004ff7058743046fb43580310057d7518d42004ff73591321f69c3119131006f710d8532006bd651913202f3e65508420067f7459721004fd76d0931006dd5218d41044fc73584420067
  | 5 => 0x44fe73d8941005bf74585321067d725943227edd60d0c3104ebe64d0e320467c435943202eee7298a4304cfe76d9131006bc60191310479c6550c43006f51059121005be7619132006bf54d91320079d7250c43006f660d853201edc3158e21004fd7418931004ff7158843006f46518532006b710d9132006d51018d410067d705972102e7c4259721005dc73589410469c4359031044fc73587421f79c3110e41014fe7598a31046de6350e42006bc651913102f5d654c83200cfe7058c21044fc73d913100cfe70d853200cfe7058b41004fd76d0821006f71058432044ff7690f21014fc7558f41004ff75d91320467c3159432005f7714ca31004ff715933202ddf708c93201ef67518532046dc6310d21006f71059032006df6350d423bf9d5150c4304dbe7390c42004bf7458c21007b464d853204ebd7610e42014fc7558e2104ebc6450932006df6350d41004ff765082101cfe76909410957e751093101cfe71d894302ebe425903204e3d751913201ef7741853201cfc76d0e2102eec42988431f6dc5118d4136fad52d0a42004fe7619132296bc32d9131014fc75d8543006ed624c8410079e5418d4104ef741584420079f301913201cfe71d8d42004f771591320067d65d0f2100cfc7059031005ed72d0d32007d51018d41046ec325884304e3e751913204ebe5458443005bd740cb4102cfe7650f21006bd4059231046df7418d41044fc7359032006f5109883101ef77518532297b731d9131005f77150921006f5105844300cfc7059032006bf52191321cfe552484210479c4350e3201eee7298831004fe76191213b59f7050c4301ebc4159231046df7118d4100cfc7058b3104ebc701913201ebe415903100cfe7059332006f7421853204edc4358c420067f7459432006bd53191320067d745943202e7f2159432006f742d8532006dd6318d41006bd5459232005f6719913200675105944302cfe7690f2104cff76d083101cfc7159221006f77648421004ff7058d211f6dc1018d41004fe769092101cfe71d9132044fe76d093202ef576c8621014fe75d8d410067d65cc721005f77150d41014fe755933100cfc7018943004fd7058d21006f710d8d21004fd75590323af9c7050c43004ff75d894101fe6620c72101df671d0921006f664d853202cfc75d8f21006f54018532006ec624c93104cff7650b32006dd634ca210067d3059721006f464d8532004ff7058732006be70d9131006bf405923101cfe711893102fe652c8621004fd70d8941006f542d853204ebe5498843006bd5019132006bf101913202cff768ca41004fd70d85320067d65993211d6f431189310467d32594322ffd7108c932046ef3298a4301eef7258841006f454d853202dee7210f21004ff7458d21044fc7690d21004fe769093104ebf609
  | 6 => 0xe70d854301eee7298a411d5f47348421006bd73d913200cfe701894102cff7610a3104eef4298841046f13158031006ee20d893102cfc725844304cfe74d8d211d6f7301853202cff701894300cfc7098b41006f5641853204ebe70191311f6be6110e4204ebf7219132006df63cc9211f5bd7110e41004fd768ca41004fd760cb4104dbd7690c41004fd759884337fb51010e421f6df6410e31004ff70d8d42006bd64d0c2101df47150e31007771059721006f872580311d6f4301853200cfe70d9132004fd7398841276be73d91322667e215972102f6c2159721006de30d8d412efce204c832004fd769083104cfe76d91210057d750c841005f77150a41006f71098b43004fd7650c21046de7018d4102eec62909410079f744c832006f710189410057d75108310467d315944301fd4314c52104ebe64d0b3200cfe7058f4101cfe7610c2126ebd7690c42276be6290c4202fac2050842006bf6519132276bc31d9132206dc21d8d41006b764d85320067d6598f21046dd7610e31004fd76d0c21004fd7559332005f576cc7210067f2059443207d431d0c21006f575d8532004fd70d8542006bd6450721014fe7559031006f7105844201df6711093104ebc7519131006f751d8532004fd7699232006ed5258a43006bd5459332004ff7458732004ff7059031006df63909413af9d2050c43006bf6450d310467f3059443014fe7558e4201ef66118532004ff7158a43014fe755923102ebc4259232006bd405923202cfc7598a31004fd7058632006bc40d9132006f510d913202cff75d932104ebf711913202e7d7598a41004fd749883102cfc725863204e7f7459442046de6318d4204ebe6419132006f510d854201efa5158031005ec7250d320067f4059432006dc30d8d21004fd755874329edf41d8d41006dd6350e4102ef4215844201efa2158031006bc64d853202cff7518941005bc744ca31006bf2019132006df634c5211357e7510b32006b71019131006dc52d8d41296bd6310e4102e7f6059721004ff70d913102e7d7598a31006df6398d2115d7e7518d420479c4350d3211d7e751093201fd673cc42102e7c6059721006dd75d8d41014fe7558b43006f42018532044dc735912104ebe6450b32004fd705884301cfc764c921014fe75d894102cff7098841004fd70591310067c20594430067c7359721014fe7558f21014fe75593320067d7159442005f7714c9210067d6059721004ff755923201ef87158031004ff7358a41007ad421093202cfc75189430079f648c932014fe7558841004fd76ccb41006dc2018d410067e40597211fdbf7190c410069e5418d4104ebe6450731007d632d8532005f47158d420057d751093202cfc72590321febf6390e41006ed5218931006fb7558031046fa4358031006f654d8532
  | 7 => 0x941004ff7259132006bd50d913102edf7358c4204e7d4059442005dd739083100677105944202ebc42593211f7b71010e41044fc73588410067e705972100cfc7098b4301edc3158c21004fd71d8d4200cfe70d9131006bf5319131006bd4058a43014fc75590310067c105943202cfe76d0f210067c4059721006bd5219131004ff7559132006f610d8532386bf6510e42006751059432006de53d8d21045de73d093200cfc70d8d42006bd40d9132014fe75d8d2102ef571d9321006f450d85320067e745943204e7c415944201cfc76d0d31004fd7558b31006bd5459021005bd7210e4201cfc7159231014fc7558b311eef432d853201df47150f2126ebc431894311e7e654cb21046dc63cc9411d6f732185322667e715972104ebc64d093204cfe74d853202fe42048421006bf511913204f3e7510e41006de5218d41046f8325803104ebf7119131006f652185321f79c6310e41006f66518532005ec7250d42005bf744c84100cfc70d8d41006bd60d91310067e20597211eef763cc721004ff7558b43006bd70d913204ebc7319131046dc6350d42006f751d854204e7c4359442006be30d913102e7c725944202ef66248421276bd6390e4201df7700c721004fd74d8f21006f510d9232006bf6490931045ee728c932207d710d0c3101cfc7358b31006bd6410e210067d6590f21006f71058843044fe76d0b31004ff7258643006bc64d8931006f71058c4201cfc7650d41006ed6218941014fe75590211f6bc3119131045de7310b31014fe7558e41007d530d8532206df10d8d4101df4714c931005bc744c921006dd53d8d41005f7714ca41006ed52588310079c648c932004fd70d8943004fd74d8532046bf745933101df6718c9311e5f570cc4210479d6550c430067d7059432005f57190941004ff7258e4104cfe768cb411febc21d9131004ff7458a31046dd7018d4104f9c4350d4100cfc70d9232006df6358941006f97558031005bc744cb211f69e4118d410467f3259443004ff7059231006f710d91311febf6090e41014fe75988310047d75d8f211467d7259442006bd52d913200cfc7058f2102edf604c832006ee20d8941044fe7359032006bf6410d2102cfe72d8d2102ef42158632006bf64d053129edf71d8d4102cfc7258642006f7201853202cff7690b31006bc52d9131006bc644c931006bd6519131006bf4058a430067c715943201ef71098a4100cfc7058c2101ede3158c41006dd50d8d4102eee6290a41337b71090c42004ff70d912100cfe70d8943006f510d853204e7f405944204fae6290c4202ebf745932101eec2198a41046ef628c932006df2018d41046ec3258b310067d405943202ebc4259021006bf40d91320479f7650c431c5f77048421046f731587321f79e4118d41007b5101913100cf
  | 8 => 0x467f30594321f6bc101913102f7575c852102e7c325972100cfc70d9132004ff7059221046de6318d21004fd76cc82102ef46158632014fe7558b31006be5019132006f51058432004fd73d894104edf7358f42004fd74d8d212979f3010e411efe672cc721004ff75d9121006f465d853202ef72158442006bd5498a43004ff7650e21006ed624ca31006dd65d8d4100cfe70d8f2102ebe74d8f21006dd5118d4102cff70d932102cfc7598b41005f571cca21006f71058b410067f7059442004ff735844201edf7358e21006be6019131004ff705864202eee729884301eec2198a3101cfc7158a4301eef7258831045de7390a3104ebc6490c21004ff75593210067f73594422d6bd6510e4101ef760cc4210067510594421867e6510f2100cfe705922100cfe7058d2101ef71098a3102e7c2059432014fe755903202cff70d8f2102ede73d932101df47150831006b510d91321d6f6531853204eec4258843006be6519131006f632185322eedd604c832046dc638c94100cfe7098a31006f97458031005dd73109311d6f453185320079d3019132006f71058643205dd76d0e31046de6318d41046fa7358031004ff7058443006bf52d913101cfe76cc9210b57e7510b31006bc71d913204dbc744ca4100cfe7059031005df7350a313af9f5050c43004fd7558f213bf9e7550c43206de61d0c3129edf42d8d4100cfe70d9232004fd705903104eef4298b43014fc7558f42004fd7558e4104ebc7119131046f943580310079d4310e2129edc54d8d41044de73d93211f5bd7610e4104ebc6410d21004fd7598a31004fd75d8d41006f51058f4201cfc7159021006bf53d9132004ff75d854302f3d6550842004ff755874202ef72158432006f5105903231fae2050842006bc51d9132046be435933200cfe7058743277ad7290e42045de74d0c3104ef7715874239ebf6590e42006f510d8d210467c735943204ebe6190e4102cff760c841006bd1019132005be7498931046df3058843007b5101913200cfe705883102eee7298b41277ae7290e42006bd53d9131004fd7518931044ff7650e4202fce62cca320067c10594421febf10d91310467e3259443004ff7058f4201ef71058e2101ebc4159221004fd755932102eec2018931044fd7359031005ef7250e422ffd5108c93235ebd659094238dbd7510e42006bc10d9132006bd6450731006f51098841006ec62509410475d7510e31005f572cc421014fe75d9121006df52d8d411d7e73218532006f650d853202cfc7259231005de7398941006f710586320467e73594430067f7359721006bf6499131045dc735053104ebe7119132014fe7598843005f57110a3137f9d3010e4200cfe709884337ebf6010e42004ff7059332014fe7518943004ff705884300cfc7059232006df635
  | 9 => 0xd6550f21006f5301853201ebc415903102eee5218931004fd7558742006df51d8d41006bf20d9132006f5101894100cfe7058742004ff7558d2101ef5741853204cff7650531006dc65d8d410067f30594421febe31d913101cfc7158a41004ff7558f4102eee72d8f21005bc7458d2104ebe645072130fd710cca3204cfc76d0d21005f571d0b310067c3059442006bc2019131006f753d853201cfe7650e21006f5105844202ebe42592320067d7459721004fd76505210047d75189433c79f7550c430467f325943201ef4741853204ebd7319132046ef7258843006f51098b43005ec7250521004fd705923104ebd7219132276bc30d913202dec7250721046df60d0c31205dd71d0c31006dc63989412079e64d0e31044fe7690b3101df671cca21004ff755873204eac4258843006bf7459132006bd6490f21046f77158443044fc7359121006be75d913202cff7598b3135ebf65909420467d3059443004fd755913204ebf6390c421ff9c31d9131046dc63cc921006de60d8d4101cf47158c21014fc7558432044dc7359031004fd7058742006f52018532005df7350521004ff70d85420467f315944300cfc70586430079c7250c43006dc6018d410079f7150c43006bd6450e32044fe7398b41006df7358d21006b51019131006df63d0d21046fb7358031014fe755864202ebf6050842005df735072102edf60cca32004fd7098a4129ede54d8d41004ff7650d21046f43158443004ff7258443004fd7650d21004fd71d9132006be1019132006bf6498532004fd761093104eef42588430467c3059432207d671d0e3102ef76198632006df3058c4202fae52d0a4204cfe76ccb41044fc765053102e7f20594320067c745943200cfc7098a43004fd755843204dbe740c941004fd7558c413bf9e5150c430067d2059443006dd4118d41006fa4258031004fd7018931006bf64d09310467d3159432006bc54d9131005f5718ca3101df4714c9410067f705944339ebd6590e42006bf6450931047cc3250d3201fd6730c72101ef8215803101df673cc421345bd7590c420079d54d8d41006bc5019132006f71059232046de7218d410067d715972104ebe64d0c2100cfe7098b41004ff725913100cfe70d8d21005f5710ca41004ff7558841047d661d0c3102fe6524842101cff715902104ebe6450e3100cfc7058843006f560d8532006df63cc52101efb4158031046bc4359031305dd708c9320067c7059442004fd7650f21006ee6250a411f6bc51191310d57e750c94102cfc72d912102ddf764c832006bd6419131046bf745933202e7c205944202edf6398e42006f852580310067f7159442006f71058b31004fd7559121004ff7258f413af9e2050c4301cff7459021046dc634c52104e7d4159443006bc20d91321eef563cc721
  | 10 => 0xc421006dc50d8d41277af32d9132004fd7558e4201df47150e41004ff7458b31004ff7158d2104ef7415874304dbe7390e42006f76018532004ff7058e41006bf651913104ebe6490e21004fd7690a3104cfe76d913204cff7650932006de4018d4124ef560cc72102eec3298a431f59c7150c4300cfc70d854302ef771584321f6bf6418d41006dd10d8d4102e7e425972100cfc7059021004fd7559331286dc4218d41047d4314c931006ed628c841006ed5298831006bf51d9131206de41d8d4104cbe74d8f21396bf6090e4202e7c215972104ebd701913104ebc7019131006bf20191311f6bf6410c2102e7e3259432014fc75d854204eef4258b410067d65d0721006f94258031006bd545864201cfc715903202eec628c931004fd7398a4101ef2715803104cfe7498a31004fd75d9321276bf32d9132005f77158943004ff715903228ebf3019131006f710d894127fd510d0c31006ef629094101cfe7198b4304e7e7459442006f51058c42004ff7058f41046f431586431f6df6319131004ff7558a43006f51058843006be65d9132006be52d9132046ef3258a43006fb525803106d7e7510a21004fd7559231005f6761853228ebc301913101eee7298a31004fd7058e21006de7618d41004fd7098a310067e7359442004fd76d083104cfc745873204cff7650521004ff75d894301cfc7158e42006ee5258a43287d44118d41006f754d8532006bc651913204ef4415844302cfc75d923204cfd725902104e7e40594431d6f576cc421005bf744c521005ed7210d21046f9535803101cfe7159021004ff715912101cfc7690c21006f71059332006f56118532006f74318532006f510d854300cfe7058a43005ed7210f2104ebe7519131206df6318543005bf744c7210065d3059443014fe75d853226dbf7590c42006be54d913102ebf649932129f9c4310a31004fd7690d21006f51098a41255f570cc721006bd601913204ebe6450e32006f71058e420067d735972102ede3258c4201ef71058c210479e7410e31337b51090c42276bf30d91320467c305944304eef7258b4102ef721586320079d6390e4201df471cc821045dc7350a31004fd75d893104e7c4259443004f5701853200cfe705863201df671d083101eee2158a41006f710d8931006be5418941004fd70d8d2102edc6358f2104f9e7310e4201cfc7650a310467f43594432efd7104c832007d7430c72102fce424c83201ef570185320057d75109310459f7650c4304ebe6490a3102e7f2059442006f510d913101ef5751853201cfc711893125f7665cc721005bf7458931005bf744c931006ed6218943004fd755922104ebf6090c4101df671d0c211f6bf6510e4120ef760c85211eef463c852101ef67318532006f77158b31007751059721004fd75592320067
  | 11 => 0x44fc7358b41004fd75584430067e7159443006f874580310467e4359443006be5458643005ed72cc52102dec7250e32014fc7559321004ff75d8d21014fc75d9132005ed72d072104ebf7019131006be50d91311d6f731189311f6de2118d41005ed72cc72101df671d0e31005ed72d0521046dc63cc521044fe73d932104edf4358c421febc71d9131007b710d9131014fe7558b41006bd3219132006df5018d41006bf601913102cfc7598831006bc50d91310063d4059443006fb4258031006dd60d8d4131fb7105084204ef771587430067e2059443004fd7558a4302fae6250842004ff7558e420067e715944204ebc4158443006f7501853204cfc7458e21006f51058643006f71059131044ff7690e21044fc7610d21014fc75d8d42044fc7458b4301fb44150731014fc755863202cff7098843006df6518d4102cff7598a41006bf648c93201df4714ca2101ef710590212667f1059721004ff7458f21006dd305884301ef661185432cfb51010e41006ee5258831004ff764ca410067d2059432006de50d8d41004ff705912102e7e325944201cfe769083100cfe7098a43014fe755923202cff760ca4101ede3158e4128ebf3219131006bf71d9132007cd424c832004ff7359321276bc53d913201fe662cc421006df60d8d41006dd2018d41006bc649893101cfe760ca41004ff7558b31004fd768c841005dd7310b312af9d5410e3106d7e750ca21004fd711894302ef76198642005f571d0a210067e655932102cfe7259032046ef3298b3137ebd6010e4202f7675c8621004f570d8532046be43593310079f7250c43004ff7059131006ef7259121006be5219131006f51058632006f552d8532006f55418532045dc7350731006bd10d913101efa31580310057d7510b321eef443d8532005f572cc721004ff70d913204ebd7519131006f51058e21006dd5418d4104e7d745944301df6710ca410057d750c941006f64018532006de10d8d410067e60597210479e6150c43006bd6410a310057d7510e211eef673d8532004fd76d0d21004fd7558b43006bd64d0e31006bd6450c21007d7714c832006f85458031046ef3258831004ff7158f42004ff7558632006b7101913202cff768c841275be73d0a420067c7359442005f77150831004ff70593210767f765972101cff7358c21004fd7610e21004ff7559331006df3058e4200cfc709883128fb43119131006df3058c2101cfe7650c2101cfc71d8d21006dd63cca2104cff725902104fac4250d42005f571d0c21046f77158643006fa7458031046dc7518d410147e7598a3100cfe705873229fd571d0e3102cff761083100cfc7058442014fc755874324ef760cc721004fe760c921005ed72d0e320067e3059721006f44218532006bf5319132006bd31191311def560c
  | 12 => 0xc70d894304cfc7458f213bf9c5250c430067d3059442286dc4018d41006dd6310f2104ebe6490f2128ebc53191311febe6190c42004fd7058b41006bd30d9132004ff7058c41014fe7598b410467f315943202edc6398f21006f451d853204cfc7458831004ff705864300cfc70d85422667e315972100cfe7058e41004fd71d8943006de5358c2104ebd73191312a6dd6010e31014fc7558b430079d4310c210147e751894302ede624c83202ede3258e4202ede3258c2104eec42588413b79f7050c430067d65d0b21004bf7458d21044fc764c521006f770d853202ebd74d8f2101ef471588310069f7650c430479e6250c4304e9c4358c4201efb515803102cff7518943006f440185321d5f67348421276be53d9132004df7359121006f410d8532004fd7650e21004fd7558c21006f71059321006f4601853201cfc715903101ff1700c721014fe7598b31005bf744c941006bd20d913202e7c425943201cfe71d9232006ee624c84102df770c862101cfe729883100cfe7098b3104e7e74594431f6de5118d4101df671d0f2101ef921580310471d6550c430067d2059442006bd5119131004be761913204ebd7610e41006be5459232006bd521913228ebd6390c41007b76418532006bc648c931006bf6450521046dc63d0d2104ebc7319132004fd768c941005f7714c841045de73d0b3201efb2158031225f570c862102e7d751894301cfc7159132014fe75d854301ebf7459031006dd634c84104f9c4350e42004fd75d8542004fd7558a31006dd6318d21004ff7558b41014fe7558831004fd75d85430467f4359432006f510592320079c744c83228ebe5319131004fd7559021006f475d85321d6f6431853226ebc3119132006bd6450b3201cfc7158c42004fd7058e42046dc6390d41006bd54d932101df673cc72101df676c8521006f451d8542046de7418d4104ebd7119132006fa5458031004fe76cc941006f540d8532004ff7058841004ff7558f21005bd749893101cfe76d0c2104e7d4159442006be10d913101cfe7610e21004fd768cb4104e7c4059443044fc7650d42004ff7258c410067d6550b21006f62018532004fd7690b3104ebe64d0731006de2018d41006f775d8532004fe7618d210069f3019132014fe7558f42006df6318941005f77150c21004ff75d854202ebe42590211f69c4118d41397b71090e42005df735894129fd741d8d41006bd5459231006f51098a31006dd3058c42006f51058b310967e654c721004fd75d8d42005f57190e411c5f5704842101ebf7459021014fe7558632005f47159132004fd75d8532006ef6250941014fc755913201ef676c852101cfe7610831006ef725913202ebf74592320467d305943204edc4358f41006f51058b41006f710587430767f7259721006f76418532
  | 13 => 0x8442004fd764c84101ef71058a41006df634c941006bd71d9131006f7619853200cfc7059221005f5719913226dbc7350842004fd764ca41014fe75d89430479e6550c4302e7f2159721006df54d8d4104ebc72191311f5dd7110e3104cfc76d093100cfc7058841006ed6290a41004fd7058b31006bc1019132005df73509320057d75c8521006be40d913204ebc6450521014fe7558843044fe7398a4302ef4215864202cff760cb4104e3f4059443006bf60d913201cfe7118943006be5459332006de5358e421d6f4321853204faf725084202cfc7259021004fd7610a311bfe6204842129edd6410e310067f7059721006bd30191310067c715944300cfc70d8f21004fd73d9121005ef7250d32005ef725052102ef46158642004fd7650b31005f77150e3101efa415803100cfc705932104ebf7519131046dc7018d41004ff7059021005dc735854202cff7098a3104ebe6450c210057d750ca21005bd7290c42006f51059332006f51058e4204cfc7650521005ef7250721276bc43d923202cfc7258e4202ebf649923202cfc7650f2104cfc7458d212cebd6010e4101df67190d41044fc7358643004fc764c94102e7c42594420047d7598a31006f420d853200cfe70d8941006f740d853201cfe7198a4302cfc75d93210479d6150c43006bf6410932004fd7058f21004fd7559031004fd7598b431fdbd7190e41004ff7259331006f71058732004fd75d9232006d710d8d413af9f1050c43006bf64d0d32014fe7558c4202edc6358e4200cfc7058b410479c6050c43014fe75d8f2104dbc744c84101cfc71d9121014fe75584320067e6558f2104ebc7519132006f51058c2104e7f435944204edc4358c41206df64d0e31206df74d8d41006df53d8d4104cbe76d9131006f710d8543006bd2019131006bf6458532006f510d893102dee7290e422efd5104c832005f77158d42044fe7398a41004fd75d913201ef97158031276bf31d9132004fd70d9232006bf7458d21014fe7559132006bd51d9132004fd769093130fd510cca32004fd7098b31014fe7558442006df53d8d42006b464d853201fe7724842101ef463c8621044fc76d0932004fd7598a41005ef724c52102ebe4259321005f571d0e31005ef724c721004fd75988310067e4059432046f4315843201df67190941004fd7650a3104ebc6450531005f77018532006f7105913201edc3158c411f79c4118d41006de65d8d41007d710d8d4102cfc7690f2101fe672c86213af9d5050c4300cfc7098b311367e65ccb2104ebe54584420067e74597210067d705944202cfc7258e4130edd60cca32006bf6418532006ed621893104cff76d0f21006bd64d0721044fc7359031014fe755913113efa6010831006dc735912104eec4258b43006f660185320057d7510b3100cf
  | 14 => 0x6de30d8d2100cfe7058e42044ff76ccb41006f51059131006f71058b43004ff7259031006bd54d9132014fc7558b411f7d71010e31004bd74d8f21004ff7058c21004ff7558c21044fc745874300cfe70d912101cfc7610c21004fd7059332044fe76d8d21006f54318532004ff735864200cfe7059131006bd4059032006bc2019132006bf644c931004fd7558c42006f51059021004fd7198a4329ede74d8d410479f6250c43047d960d0c31045de73908310067d105972100cfc705883104ebf7319132006be71d9132046dc6350d41046de61d0e31006bf54d9131006bd545922100cfc7098843004ff7158b430067c4059432004fd7098843296bd6390e410057d7510a2100cfc7058a430b67e65cc72101df47150941014fc755933202cfc7598a432cf9d3010e41004ff7559131046dc630c94100cfe7058c42206de71d8d41005f77150f210475e7510e3102cfc7598a410467c32594431febf73d9131005f7714c9311eef772d853202cff7598843006b5101913202eee5298831005df7350831006f774d8532006f720d8532006dc72d8d4104e7e4059442006bd54d91211f69f6410e31005ee7290d42006ee201893100cfc7058743006f5611854304cfc7650d3228ebd7690c4104e3c4359442005bf744ca210479c4350e31006bd64d073104dbf75d0a4201eee729884100cfc705913102cfc76cc52102cfc72586431d7e432185320467e43594320467d435944304cfc7458b31005dd73d0932006ed628ca31004ff7358b41006f470d853204fb44190d41014fc7558c411eef730d8532044fc7358a4102cfc7610f2101eef7258a31006f564d853200cfc70d89310147f7659721044fc7650932206df6399131004fd7690c21046ef32988313b59d7050c4304f9e7310e41046dc7359031006bf53d913101eee2158841004ff7650f2104e7d7459442014fe75d9232004fd73189411ffb67190e41014fe7558c211eef430d853204ebe6290e4201cfc725932101eec2158a4101ed43158c213a5bd7590e42006f710d8f21006dd3058c21005ef7250e32006bc60d9131004fd7058c42005bc745853202fae62d0a42006f7105933100cfe7058e21007d563cc7210067e6599321004fd7498a31005ee72d0d3202cff75d8f21006bc6458931046d84358031006dd3058e4204f9c4350d42044ff76cca4104ebc64d0d31006bf405903204cfe760cb411f79c6410e31005f571d0f21006f71058f41006be40d9121006fa755803100775650c72101efb715803100cfc70d912102cfc760c941014fc7558a41046ef329884301edf7358e41046bc4359032006dd72d8d41006bc51191323bf9f5250c43006f510d8941004fe761913104ebc43988410d67e6550721044ff7690c21006bd64d0b32005bd748ca41336bd6090c4202ef7715
  | 15 => 0x662cc721006be72d9131004ff70d8543006f6301853201cfe768ca41004fe760c941006be2019131004fd7058732006be51d9132006f51098a43004fd7690e2101ef71059231004fe7610932006bc40d912101cfe7159031014fc75593313bf9f5150c43006be60d9132006f4715913204cff7650a21046de6310f210047d75d932100cfc70593311febe6190e42005f5760c7212667e415972101cfc7258f210467e305944302eec4298b4104ebe6450a210067c7459721004fd74d89311febc31d9131006bd6490e21014fe7598b43014fe75d8d4200cfe705903204dbe748ca4101edc3158e41046de634c841004fd7610831006dd40d8d41004fd70586421f6be2119131044ff7610c21006f9725803104cfe7498831004ff764c821006f510593211eef663c8521004ff7559032005f571cc921004fe768c921004fd7198b4304e7c405944200cfc70d8941206dc41d8d4102cfc7518931296be73d9131006f64218532006dd53d8d21006bd6419132004fe7610921005be74985321b67e65d0f2101df4714c8210067e1059721005dc73591211f79e31191310057d75189431ff9e6390e41006bf6490d21006bd75d913102cfc7598843006bf64d8931006bd70d9131006bf75d91320079d4310d210057d7598941014fe755922104ef7415874202edc3258c42046df7018d4102dbf709094202cfc7258f4126ebc301913201df4714cb41004fd7058643286df4118d41004ff7058f211eef732d8532014fc755844201ef0215803101ef71058c41006bf5019131004ff7558c42375bd75d0a4204edc4358f42004fd705912104ebc4398b4301df67110e21006f56518532006f45218532004fd70588310079c4390a31006ed6250a41006dc5218d4104e7e4359442004ff70d8943397b51090e42275bf7590e42014fc7559232004fd75586320f57e750cb41276bc73d9132004fd760c941005dd73d0531044fc76cc9410047d7598a41006df63d894104ef441584420479f6050c43004ff7650c2104dbf7110e410057d7510c2104e7e42594430069d301913202cff751893101ef760c8621006bd65d913101cfe7198a3129edf40d8d41006f71058f211f6df6010e31004ff7058e420067e2059442006f665d8532004fd73d8542006bc6498532006be20d9132004fe76cc521004ff7458831006f652d8532006bc6418931004ff7558443006bc65d9131004bf7650842007b510d913120ef560c8521006f773d853200cfe705902100cfc7098a31006dd52d8d41004fd7598b3101eee215883100cfc7018931006f751d854304cfe7418931006be545902102cff7598831004ff755912104e7f4159443006f7105864201df47150b3102e7e72594420067e205943228ebf311913131fb51050842006b710d913104dbe7390e41006ed5218941
  | 16 => 0x9131006df764c832007d73018532006f710d8d41004fd70d93210467d435943204cfc7458c2100cfe7059231004fd705903215e7e6550832004fd7098b4304f3d7510e4204ebc6490d211efd663cc721004ff7058632006f710d8d42006f51058732004fd7558831006d510d8d41006bf50d913234fb71090942006f752185321efe732d853202cff70d923226ebf3019132006df5218d4104ebe64d0a212779e6390e420067d7059443005f77150b31004ff7058b4102e7c325944201df671cc921006f71058d2104f9c4350e41005f7714c941006bd6490a31276bf72d913202ef721586421f6be5119131276bc32d913226faf321913202cff7598b41046dd7118d4102edf7358f21004ff75d8d4202e7e75d8f21046f9325803101eef7258a4104ebe645083102e7c32594321febe71d9131006bd5459031004fd72d8d41014fc7558843006dd6390c21006f51058743004fd7058443006be65d9131006dd70d8d4104e7d425944326ebe4318943006f55318532006dd6390e42006bd40d9131004ff70588311ffb71090e41006f7105874201cfe768c931206dc51d8d41014fc755844302eef209884301cfe76d0a31004fd7558643006f474d8532004fd7610f2101df47150a2101df671d0b31006df7359131014fe75d89310079e54d8d4102e7e7518943006dd71d8d413af9d1050c43044fe7318941005bc744c931044fe73d854226ebf6410b32044fd7258c211f6df1018d41045dc7350831006bd72d913102ebf60d0a42006f5501853204fb66110e41046ef7258a43004fd70d8d42006dc63589410067e705943202e7c6359721004ff70d894102cfe729884326f9c431083101ebe415902104ebe64d07210067e6598f21004fd7558442044ff764ca2100cfe7058443004fd7098b41006be70d9132007d510d8d41006f51059132006be6519132006be521913204ebf4058843006bd5498b41006dd5018d41046de6390c21006be5498a4304ebc641093102e7d75d9321046df64d0c31004fd76cc841004ff7058a430a57e7510a31006f71098a4301cfc76d0921004f7764842104ebc4358c4202e7e7259721006dd634c721004ff7558a31045de73d0531006bc72d91310957e7598931045dd76d0c31004ff7058b310479e74d0c31006f77158f212079d64d0e3104ebe73191311eef653d8532005f7715094101fe762c8521006ee624ca31006f710d93210067f1059443014fc755923102dbf765084201cfc76508310079c7150c43046fb53580310467d7359443006f632d85321eef453d8532006bd52d9131006be75d913102cff759884104e7c7459443005f77150e410479f6550c4301df576cc421044fe76d0531004fe76909320079d4310f21006df3058f2101cfc7650c21006bc60d913201ef43198a31006bd6450e3101ef
  | 17 => 0x4ff75d85320467e7359432006be5458642006df30d8d4200cfe7098841317cd52cca3202eee628c8412079e41d8d4102cfc751894104dbc744c94102cfc7598841004fd764cb41006df72d8d41004fd755873201df6718ca31006f743d853201cfe7690e210467e3059432004ff7058e2100cfe7098a41006f77158d2100cfe70d8d42006bc20d91311f6dc2118d41006f45418532006f71018931006dd6518d41004fd7058a41006bd5498843004ff7058a41004ff7650831006771059721006f5105933106d7e7510e2101eee2158a3102cfe72d913104e7d435944201df4714ca31006f67618532006f51058642014fe75d9131046be4359031014fe7558742006dc30d8d41046de7118d41006bf6450d32004ff7259121006f510d8f21004fd76d0f21006f4641853201ef231580312e6bd6590e4102e7e425943201cfc7158e411eef576cc72102e7c215943201ef67418532004fd7059021014fe75d932128ebc3219131006f9525803101cfc7158b4301cfc7159332014fc75d8532006f51058a4104e3c425944301ef71058e41044fe7398841004fd72d913100cfc7058742046f8435803100cfe7098831006ef624c931006df735913233ebd6590c42004ff7058a31044fc735902102cff7098b43014fc7558642006b510d9131006f6641853202cfc76d0f210057d750cb4101ef43158c21006bd5119132006dc6350941006f530d85321767e65d083201ef76048421004ff7058b4301ef46198632006f71058f4201cfc764c931044fe73d913102edd73d932101ef83158031005f57110e21367b710d0a4228fb73119131004fd76d0832206dc10d8d41046ec3258831044fc76d053104dbe740cb41005f57110931004fd7598841004dd73d932101ef77318532004fd7610d2104cff76d0b31046f73158443006bc4398a4101cfc7158f4202cfc768c941005dd7398941006f51058f41004fd75d913101ef4619864202eee7298b433af9e1050c4301ef763cc42126ebc531913201cfc7458f4102cfc76d0521014fe7559121006bc648c93201ef67018532004fe76d0d32005bd7610e4205d7e7510921046de634ca2101cfe71d8d21004fd70d9131006f7651853204ebe64d083102dde728c932004ff7258d21006dd63cc84101cfe7398b3102eec2018941006dc639094104e7f425944301df67110a3101df77248421004ff7650a311febc51d9131004fd75d8943044ff76cc841277ac32d9132047cf628c932006bf7459131006fb5458031006f520d8532004f77158d21006bf40d9131045dc7350932006f542185321a67e6590f21004fd7198843006be60d91313af9e5050c4301df47150d3102e7e7598a4104ebc71191323af9c5050c43046ec3258a43004ff735912100cfc7059231014fc7558c42006dc20d8d411febc10d
  | 18 => 0xd7059232006be30d9132004ff7559332006bc641853202cff7610b3102e7c6459721276bc63909422667c3159721007b710d9132005f5718c931006ed52d8941046de634c72104faf629094202ebf7459032004fd7059321296bf30d91310479d6250c4304e7f4159442006df75d8d41286de5418d41005df7350b3200cfe7058f42296bc30d913102dbe72909420067e3059442004fd70587431f6bf6010e41006f554d853200cfc7058a41004fd76d0e21005bd748c841006df70d8d41005dc735052104fb44150941014fe755864300cfc70d932102eee521894101cfc7650941004ff7058c42006ef2058843004ff70d85320069d5418d41006bd2019132006bf65d9131005f571d09210467d735943201df4714c921006df63cc941014fe7558e21046de6350c21006bf64d052101cf4715913204fae6210e4200cfe7058432006f7619854300cfe7058b430147e75d8f2101df4714cb21005dc735072101cfe7298841006bd3019132007d6321853202e7e4259442004fd7518941006de52d8d411f6bf6310e4102f7675c8521006bf649093201cfc735933101cfe76cca4105d7e750c921005bf744c821006bc7458c2121ef560c8621005bc7458931006f710d91320067c705972104edf4358f41005ed7290e4204ebc6450d31006df3058e410067f105943201cfe76d0e21006ed209884304cfc7458a31014fe7558a43006bd5458443006fb745803101eee2198831006bc70d91323bf9c7550c43006bc52d913200cfe70592321efe572cc72101df47150d411febf6590e4100cfc7058d2101ef84158031006f710d9121004fd75d894104cff76d0a31006f760d8532005f77150a2104dee729094201ef71058841006f640d85320079d5418d41014fe75d8542014fc7558e42046dc4359031014fe7598a41006f551d853229f9e5410e31006bd65d9132006f51058f21005dd73d07310057d7510d2101ef42158831006f442d853201df671d0a210057d7510f21007b46418532005f770d8532047d431d0d3104cbe76d91320067d654cb2101eec215884100cfe7058a3101df576c86211f69e311913114efa609083100cfc70d8d2102cfc7598b3102cff7598a310067c7159442286df4218d411fdbd7190c4101cfe71d9121004ff7458c212a7d51010e310067d715944302edc3258e42006bf405923201ef47018532286dc5418d41005f57190a4104ebf731913101cfc76cc921004fd70d913200cfe705884302ede3258f210067f71594430467e315944302edc3258c21044fe7610b3126ebe5319132004fd7098a43005df7350531044fc7358a43004fd7558f4102eec3298b31004fd7058b4304ebf6390c41006df20d8d41004fd7059331006df30d8d4102cfc769093104cff76592320067d7159432004ff75588311957e7518943
  | 19 => 0x9443014fe7518941006bf52d9132014fc7558742004ff7359221046dc3158443004ff765083204dbe7390c4101cfe7158c21004fd75d8d2101cfc71588431f6de4118d41006de6518d4102eec42988411467f72594421eef643d853202cfc725923200cfc7058e41004ff755903100cfc705933200cfe7058b31014fc75d912102eec329884301ede3158e21014fe7558732006bd405884304eef425884131ebd605084204ebc6410b3207ef1715803104edf4358c41006bf7458c21006b764185320067c7259443006be3019131005dd73d0b322dfb51090e41044ff7690d210467e315943200cfc7058b4302edf628c9321febf6490c21006f620d853226ebf3119132004fd7058a43006f764d8532215f570c8521005bd7290e421f79e4110e31004fd7058442014fc7558d2101cfc76d0c2102e7e7259432006f51059231006bf6019132006dd1018d41004ff7558c41006bd60191311febf6498d41006f670d8532006bf6498931006bf74591210471e6550c4304e7e4159443014fc75592211bef56048421006dc53d8d41006df735912102dee72d0e3204ebd7119131004fd7699321006de53d8d41006be54d9321004ff71591310479c6250c4302cfc76d0d3204ebc64d0d32296bf32d91311967e6550f21006df638c941006f510587423b79d7050c430079e7150c43156fa6050831006bf10d9132044fc7359321006be52d913104ebc6490931006dd63d0f21006dc53d8d420067f1059442006df6398d41004ff7058442004fd7558b41046ef3258843006bd53d913200cfe705932102edf6398f21004ff7159132006bc75d9131006f71098b3102cff7098a4100cfe7059121276bd6310e42396bd6090e4202dbf7250842297b431d913101eec2158831006dd63cc721046f7315843201ef71058831004ff764cb41004ff7059132005bd740c94104f3e6590c422b6dd60d0e310067f405972101cfe7610a31006bd71d9132004fd70d8d41004fd76cca41006fa725803102ef571d8f21006f510d932104ebc6410932004ff7558a41006be5459231006f51058c4104cff7650731005f5710c941006de6018d4126ebf3219132006dd6318d42004fd765053104ebc64d053101cfe768c841014fe7518931006bd50d9132006f570d8532006ed62908313c79d7550c4304f9e7390c4101ef85158031045de73d07310767d7259721046bc43593322f7cd524c8320067d655083200cfc7098841005f77159132006bc5219131005f7714ca21004fd7598a43006de72d8d410067d6510f2101cfc764ca41006dd3058f2100cfc7058c42005be7619131006dd6350e421067f725943202cff7098831005f1700c721006dc6518d4101cff74590310073d75191321eef662cc421006f71018943004fd76d0a31014fc7558a43006dd6350c21004f
  | 20 => 0x1100618b00200100203873a00001001000708c60900600000b01a0020580000070ba0e30000000000bd03800700e02d0031020290610d30f502204a004001023aa80000000ce01800a75e0000030030080720382061e70a000d00d01200e00500800000000000004e00d00900700a02800000003000000002300e00000a01001400000704201600508c0200280090005f90d905a01e00521a00900128b02400000400010300800400502300100100100301000000200106a0ca00103100507801d00200901400103d00300004700800971300f01300007e02f25700a0070010050140183270110d600407400104601300000201506c00800201c01d00000000400803202201c0b300714401231d00200000003813000a0ad00f00200153b01402545c9df00400300507100002404318300204801804100100606700300501f04d01504800000000615109800100100a00800000001602600300800001300900100d00005100201d04200901000200900b06b02900007e00153805600f16306707500200200000004300907b00400000400900004700b0d71dd0080000ac00603109a00026d01a31200c00500000400e03f07c00106413a05b02804800000774301b51b01000402100d00000f00002c0000280de02700002905404600202f00c0ba0100d60050b702e00101200000700406a00300107600100304c00a0000000d70010380180080030080f800300200605402f01503d0a600800002100701b00244402a00000200800a05e25600303000202000800600429518e01f00400003300002a00700204b00700920821500103044700704b00050600000000002c00900000204500300006800203100400001c09e00000005e00101100000300a00001100001900000010d00704200100018300002100204800714900d02b00502500006b00003900102c00000800a00800a00a0011d800000600300500100500d00000904917400001c00001300600307b00200500300300002e00400600000100b0170250a30150010000143750000090010570011dc01100500001e00705304802171e04300d00100c1c902300b0c300000d03000500f0701016e60010000080b801702401e00000400372b02b00d00600000201000f0130981ec0130000020191b40250000f100500700f00300002100500a0028590010190300051040363dd02200401605100b00701400a4a60210030b700400000100100100300305c08002b00002801800101800100000000600300717000001b00f0020e903100114808100004d00000001c02400700600b02a00a00500303300504703d10603105d00600534fb51090942006bf6450932005df7358542006f651d8532006f510d8d420067d4059721014fe7598841007d53018532014fc755873216efa60d08310067e105
  | 21 => 0x900f5852d400000001600f00201a11302900f05322700f02100000700c10e00332600000000000006910502403701100300d06304804500106502a1970175e1b4d05100105d01702e0050570000650020052fa05500000200803518000107a01000209b03673a00145900f00a00202500303303d01100100400100702a01100112700801c00b01501600400200600302a00000005100e01700c00a0060020b301500003600801504100401014200100a00702a0007af0010000720026fd04501600000f0030030013d105400100989c5bb01000200000e00b00000f00600800a00c0000000050033870180950000000040090d400419f01904239a02802001247306d01602704800408400a00000000000101d01000018200702b02400e00502d03a00001d0411de01000300300400200006205a0a025200702a04905302900100400600a00000401c0090490c100100f0060290040020040000030000913a002911600301f04600003503a01504f00b00400000004100a09600100000403103900001e00201500200702303a01300d02904400900300600701606100604902b00600002b0490850000010090000040000000cc00200c00600a00303900400c00401005202f0d000800300a01603401000003007d05500d0000040000630540f400c00000300100007b00702902101300002d04506700204100201114c0200289e24dc0020360000e201402c00000801665700f13700600204d00001a04906000400104800000e02002800200100302b01b00306a01001901200b0000080007a303f00d03e05902b00a0170120570680050af00004c00201602100400000401c02a0880070140263b10030121ad03700001700909411f13500200403600c01100a15000002700100000e00800c19a0010000000dd0010040013b000a00b00644a00c0000000030140344d701e00600406d00f00700000300800510300300603700200701f00400600004b00600801100000001600603d02b0160c300200000101215800100f0000660020100a0
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xaf381549600c40117b0f180c898802ada1050d85320072bc2a2031a8245a6f825c565c84010ff0ab82c3a18038bd4a52d91320056ac0841b1a8200ab484594614c8015ab03106c6a0802ad61260d853204c5f43840322647ded270440635040187cebb208498803a64c110191320065a322e1b0a6400a5e850806350407968c2ba4c2990fab52055418d4101c5e43aa8b20427da7581841650c85147b08382ca210829b60870594320076898221b1a84018dc874c163908019aae7886c9908022fe1170584320055a40ac83226400e2d5454a6290c011ef02baac6908274b9897510e420047ac38a1b0a647ae1c434c165108014bb06102ca21802a760c521913102e67296ec9906400ab686c43644c8015b307212c0188032dd93714c9310064fbb0e89906408a5e838416510c01938e8b1a639080a1f21570587420046ec38a1b1a823ecd47118d42504015cb02106c4a08029d60640597213ee6a39a20b224200c6f729c96510c01968c9b8a64988023d6037158d210055ac26a430a64018f8805d562cc49bd3086212c018823271cd64508313e71b3ae2032264008bd878c0644c8755ad07200c2990172b94b76508420053b40c40b286400ab684994614c801d2a60880c89900e3d2057650c2104f1dc0280b288652e1e53d4f644c4015b307a92c01894f271d3634c9413de4e21ee0b188400a9d84080635040147b0a100c8988028f61420d91310462e31aea21a4250b948444063504819aee7882c89880a1f21570586421fe5a38ee8b184200ab581183644c80117d0fb2264988223b21d5258a430076898221b1a8200ab684d48614c8f5d1884982c4218021f61f40597210065bba620b1a42008ef825c164484018bacbb9a8390802bce0165185320070eb2a8621e424d8bf8759342cc8014eb0ba06c299003351cf71591210046ec3841b1a8250e1e54d50635040156908b2ec299002b560f74d853204c5e422e0b108200cb7649c6644c80117b0e106c89900eb52073058c210063bc3a20b28863f8bf845d9414c4010fb0eb288790802b3a0a65d8d414652ec1ce0b2886008df8758c6350813179083b284988223720d75590210047b43a20b2264058dc8754d639080317f0ea06c898802a760c1019132006e9a1ae018e42018bc8750164c840155b05aa6c899003b44c11058c420055ac0c41b2264008f78758461508111b906b82c818803b4dc110d8d410047dc02eab2242038f687080614c87fd6700886c8988028f61020594431ff4a18ee8b184200e9554440635040196ae9886c7908038da1464d853200733a94a430a6400a3d848416510c7f17d0f2a2c3218063721d3058c420055b408c1b226400cf37044161d0801ba6e0986c2990028fe1120594430046ec3c81b1a8205a6e821c165c847dd6700880c8989f38d10b1059443
  | 1 => 0xb07082ca21802a7e115118d411f56b40c8031a82008f580dd9210847b5a906886c7908034d4417510e420161f3aaa93148600f9130440644c8075e503b92c01880ebc20572580310064e3a6c698a42008f787584614c8075e102aa2c018802b360c20d89310446f4384031a8200a748544361508019e6e0882c690802ade0565191322754f418e1b226451a9e83148644c4010ff0ab82c610803179d463989410464fbb286218420087f855c1620c40157700b2ec899003954c310594430054ec26a7b1a8400e7380441650c8f3968e8882c6109ff1d9d510189431851ec20e0b288608a5e830416510c0147b09182ca21002a76105018d410063abaa21314824da9e83940644c8031790ea02c8191fb95cc3105944301d7840a84b006200cb4645c0614c80156b03106c8988262fa1c201913100579c02cbb0a6400ab9841d5600c4015af06a10c2990fb659c47150c430047bc06ec9084200a6d821c16510c0156b03100c89880393d4a52d8d410053bc0ae6b2e4200c5f739cd6510811d3509a1ac0188029da0470594430053ac08e0b286453a9e840836350401d6460880c89900237e0d75590210071b428c830a6405ce652dd921084fbce460882ca2193b8794f53d913245d2fc1ae8b28640087e870816510c7d56902a98c8988022fe117558c210053ac2ee7b0a6400ab681983644c8011f700baac8990022fe1d65191311f54f40ca831a824fed171d0d600c40193ae621cc5208f63de19718ca310055a4226430a6400e3485440644c8014ed0a320c2990031d5d710d8f2107d6cc18e4b0062018f4874416190c0156f08990c299002ada0420d91320055d420e4b0062008bf845c1644c8018bee739acb908029d61740185320053bc2ac1b0a64008bd87d48644c80156b093aec2990038ed5254580312955ac08e1b226281c9c73551640c401d2e60880c89900297a1672d8d410051fc2ac03226400aac825016210c0317f0ea06c8990270f1917510d2101c7a40aeab10864ca768110165c84a1938c839a8290903351c7634c9410053ac0ce0b2e4200a5c8544063504019ae21bb26419002b3a085018d410056ac08a1b1a8203af2811d5600c4a7a3886ba885188ff2d9db10191311f55bc022032262018bc87501648c801d6260886c898946a7a0c50191310045ec3cc032262008bd87080644c4015c904980c2990030f594744c7213fe3b3aa213148252a9e83143644c40153908b18c690803175d753d8d4200758982203226200c3d65dd131c840156b03280c8990022f61c51d91320143f42ee1b0a86008bd87140644c40117d0fb22c2990039c8c110597211d74a21a8630a6400a7581101650c8015e702aa2c018946ad21910191312955a43221b22620087f855c161908f7c3887982ca2120e1f21d10597210055bc22c230a6400
  | 2 => 0x77650c430051f42ce5b226200a3c85440644c91d4bf06b92ca219fa9da0410594320075918221b226400e9783440644c40156902b00c8990063d21d105864200679b8220b24623aad483440624c503d3086aa2c01880237e0d7058d210043fc2ae0b08867de7130441650c87f56d02106c8988021fe1570d91320045f43c61b226400a75818c165108011ef0eb28c2990229720d72594430446e41ae0b2242028bf87553644c4031ef0e886c2a1936a7a0e10191320054ec1ee3b22643eab681080644c48153b08386c6a08029ea1472580310054ec26a5b1a8200ad583083614c8014790ab00c898802b960620189410052f418e0b2e4200ed1304416390903c3ceaaa0c6a093aab60875d91320047b43881b0a6400af181d09600c401c6ea92a6c2991e7ac5c110191320055b42461b0a64038f4815c163084f5c3e80982ca2180637e1d30d8d423df0ebae603226409c3e645d4428c401d2aa9880c6a080237a1c63589410143e42ae1b22643dcd463dc5324840157108b92c018802ad60640d91320055ac24c030a6408ada83d49600c4014790ab06c898902a761372d8d410052ec1c80b2864008df87580635041153906aa2c8188029721560d8d410446f43c8031a82028bf8755364c84ff8ecea886c79094ea7a1352d8d410055bc22cbb0a6400a3e841c5650c801c6b0a320c29900e3d21f10591320062f3aec61928200a5f85440635040117d0e322c4988038bd4a52d91310043fc2ae0b148600a3d841c1650c8050f90ab82c521937650c4744c9310074a41a203226200ad983d51600c401c5ea5290c8988063721d3058c210071a882cb21884008bd87143644c8f3d2886882c6209372718c744c92102d37410e0b286430a5d831c16510cff8ecea886c9908171b1c965507210046ec3cca31a8200ad686cc0614c8011ed0f882c6908028fa1230597210055ac2041b0a6400e3540c416510c0193ee839ac89080237e1d6518d411fe5a38ec89926200a3d85d03644c8011ed0f286c299026ab21120588430055bc22c1b0a6409a9c8458e43084815ad03386c6a0802ad61353d85320043fc2ae1b22420287c855c1644c4114bd06382ca1915697e0d71594430061f3b4ea32264008bf87594644c80117b0e286c89880f3c989700c7210055b420a030a6400aae82994644c4b547f08b8aca218223720d76505210066bbb0e29906400ab9841c9600c4011eb0f100c299002abe0960d913100536c1420b2e4200ed230443634840117f08baac8990033c5c110d932100557c12c0322627aa9d838c0644c8a3c3ca7a98c8988031b59772507213d70ebaa60322640087f855c3644c4815ad02106c6a0803a52111018d410454f41ec8a1a623ecb471191324c4014db0a106c4a08262f2117058d212054e432a9b1a820087d85dc164cc4014b
  | 3 => 0x1b22644da9e83080644c8019a8c7b8a84a080a1fa1770593210054ec1c203226400a768188165108075a902982c610802a7a1a5418d4101e6a38ac6a18420287e85dc1640c801c690a886c8990028f61740d91310055ac0c81b226200a7985109600c47d5ad03280c6a08031d21d105943204e563a4c499082008bd87994644c801d28c8980c29902297a0e705944304e57312ec21c84098be878c0644c4019e6e0882c51880a3de1d51d853200c6e43a60b1c82008be87083644c8011bf0eb18c6a08022f61f531913200567c12c1b1a823dcf1635c031c84019e2e0886c79080f2d1c56450e31005c6412603226453a9e84143635047d5ad02280c6a08073c9c110d854300716aa2a43128200b94815c94310c010fd0fa02ca19002aba0850191320061fba4e8b286428a6d821c1651081387cc8ba887108021fe1d10594430066bbb6e29906400c5d7518e62504018eaea886c99094f2719373505310076918221b1a8200ab584d4c614c8ff8eeec882cb908030f5d64398a4126e4e21aec210624ca74815d165c8413958c93968699002ad60630191320053b408e0b288400ae482441620c4015cd04286c2990029e215725803101d7840ce4b0062018dc874c163c840196e21bb284210032dd9170d85321f74b20a2031a82098bc845c1620c413968c8b8cc8990022fe1d60191310054ec18e1b22643dad6831c3614c80117f0eb20c89080a2fe1d54d91210143e42ae0b0c643f8bf8759341cc4f34eb03082ca210fa2fe1d64d0c210056ac0861b1a8200ab781597644c8014e902ba2ca19002f120930d85320047bc0ae0b226428a3d841c5651087dd28623a2c610802ada0470d91320055b4246030a6400a77815c96510c01d28c9986c29900a1f21570d91210053b40ce0b288400c3d75590428c4011bf06b82c89080a1f2157058c2100666a96ec99064098bc845d8430840b4dd04382ca210032ddd0715913200477c12e0b226200cad52dd9421080147d0a100c899002ade1160185320055b426a7b0a6408e5b804c16510c015390ca1886908063de1d10d85420047bc3ac830a6400ad583d48614c81f5b3063aac018802a7a1230d8d210071bc2a20322640287c855c161d0c014ed0a106c299002b560640d8d410052fc2ac031a8208c5c635d432504fbd2886882c818827271d1634c8410047b43e20b166200e94644c3614c8014e90a886c299136a7e0130191323f66a39e20b224200e1d54d486350401d28c9190c2990031799473507210055b40881b226400cf170540614c80117d0e322c299002b360a65d8d410052ec18e0b2e4208ad883509600c4031e90e882c3990263de1971d0f213851fc22e4b288600ed360443635040153b06100c89900327ddb744c8320074a986203226452a9e831c3644c4031bf0e986c6a080327dd
  | 4 => 0x44c8015cd04280c2990033c619700c7213d70e21260b28867da75818416510c011bf06baac8990faa72055418d4100c7c402eab1a4200ab584997614c87d9a862bb0861094ea7a1070d8d410055bc0ac1b226400a7785443614c801c3ecaaa0c6a080ebca0474580310047bc0aeab2264008f687903614c8051bf0ea9ec690802ad61230d85324063b3ae21b26420087f855c163484031e90e882c22100a1f21570588312745fc3ac9a1c6400bc4824c0614c8994ed03202cb90802bc20165d85320071b882cb21884018f4874416110c0193ec839a8290802bce05425803101c7b438a030a643fab6819c3644c40156f02b20c8990030f5d475d91320452f41c80b2864008f68744163484079e700b80c2990022fe1170591212854e4222031a8200ab581980644c8019aee638ac8991e72d9d110d8f210061eba8c931262038bc8759143084011f700baac598802ada1353185320052f418e0b2884038bc8755164884111b906baac8190029da1420185320072a42a21b1a8200a9d84d40635040159904b00c6a0802ae20165191320055bc22ca30a6400e9464cc0614c801ce700882ca21027879cd6590c4200572c0841b126208ada831c9600c4014ed0bb9ec2990031d21d10594424564e21ee0b206200a6d85083624c4015ab06286c29900a2fe1d54d91321ed6b41841b0a648ae98439d1600c401d6460886c8989e72d1d11058d210047bc0aeca1a4200a9f83440644c47d17d0dba26498822b520d105843200566c10a031a82018f787443614c8014ed03182ca211331dc417598a413451fc22e6b288409a3c844c165108751e90e882c610803ac8c11019131006b932ae018e4200a75811c165108015ab03280c6a0802ada1260d85323cf5221220b108600a75819c1651080195ec839286990032dd9370185320053bc2ac030a643ea9c865506350401a6e20ba887210c28f61071594432856a4322031a8200ab584080614c80156b0828ec2a1002a76135118d4100679b8220b0c8480c7675c406250c111b906b82c2210029da0620594433ee6a39a20b206200a3c855c3644c80156d09300c2990023ee017558d210053ac0c60b2e4200ce552dd921084115b5063aac0189e78d10d105944204d1f426e4b288601cf27044163d040196ec8b80c299002b560c20185320061eba8873148200eb060443644c48d9e50cb806390803e44c110d91323fe3b3aa2131462008bf87580644c8019e2e0980c29900ebc20552580310051f426e6b2e4208c9c7359141cc40156b08286c2990038dd52541853200679b8220b0886018f48744161d0c7f17d0fa9ec89880e3da1e40185320056ac18e1b0a6451a9c83440644c4019e2e0884c5188262fa1c51191320055ac0cca32264008bd87d4c644c47d5ad03100c6a08028f61071594320051fc2ae
  | 5 => 0x1822b6a0e425803104e5a322e22126200ab584dcf614c87b9a8c7b8a64a08029d21560d85320061f21aea3128609aac84c816210cf3d2886882c621002aba0850d91320056ac18a030a6400a9d83140644c8011eb0f200c2990039ce0110594430076830221b1a8200cf17044163d040147f0ab86c898802a761353d8d412653b40c60b2e4200cf1704406250c031f100baac89094ee521110d8d412854f420a431a82008f587943614c8010f90e882ca2100f391c6624ca3104d1f42440b28868da3d849c16510c014bb07102ca218021f61f40594320073898220b28843eed38044063504018e90e882ca218163b2097058c2104e1f39acb2188409a3e848416510cf593886b82c6208029da1740d85320143f42aec21e4200cb7645c6644c8f94ed02082ca21002e320930d91320456d41ea8b006253e1e54d5363504018eaea880c4a18eab520d42185320055b40cca3226400ab681940644c8a153d09080c6a0802976142018d4104d4e422c6a184209a3c845c56510c9dd3087212c0188223720c764c9410053ac0c80b286400ab481583644c8018eccabb663908023da1f10591321f5ca40a862184200ab58110364484014f100b92ca218021f61771588430051ec2e80b204200e1d54940635040117b0e106c8988028fa1420d91320053ac0860b288408a5e838816510c079c8e331264208029d205735944204d5a42220b08860287c855c3644c4079a8e2b1a872093b47cc17510e423d70f3aa603226403af281dd1600c401c690a886c8988229720d71594430061f328e89964209a3e848c16510801968c9b86c2990029d60420594430051e42a21b226400e965444063504119a8c6b8c86a0803175d7630c9410043fc2ae0b0e6400ab6818c0644c8015d5043aac018803474c17510e420047bc3ac030a6400ab584140614c801c690a880c89880e3da1c401853207d78c08e8b00620faf181dd5600c4011bf06b82c2210eab5a0c20185320161f3aca9b264280c7675c4363c840147b09182cb908028fe15601913100636b2ee498e4252b9483443644c4011eb0e206c299002b560670d8d410054ec2041b1a823e8bc875516110c015ab02100c6a080a3be1d52d89310053b40ce0b28640287e85dc164cc4014eb0a216c299137a6e0130191320053bc0ae8b286400ad583d50614c8015ab02280c6a08fb2d1c47458c210456c41aa8b006200a9d83083644c81317908baac690a07279cd54d93210043f43e80b2e4200a7581881650c8018eaeba8ec2990028fe1560d913200678b8220b188451b9483440644c47d53f08a08c6a0802ba60875580310047bc0aeab108600cf170500614c8755ad07a90c2990031d5d51098a3104e1e322ea2126400c3d75d90434840187aebb24c4988073c9c11058c4200679b8220b224200a9d831d76
  | 6 => 0x47ac3cc830a6482c9c73951640c4014790a880c8988028f61740592320051f428403226250a9e84d40635041347908902ca219f32d1d31058d210063b42ee1b0a6400a9d8414363504fbda2e0880c6a08023761e6018d410143f42ee1b0a6400a76811c1650c8015cb04286c29900e3d2057558c210053a42a21b0a8600a3d840416510c994ed03102cb90802a761a7250c432076810e86b006279e37404416510c015ab03186c6a08023ee01755884304c5e422eab1882008f587940614c80153b06286c899136a7a0c101913242d3ac0c20b2e4200ace82994635040b5c904882c2210030fd817510e420052fc2ac1b1a827ea76810416510cf9d4885882c4218272d19171d0d3101c5e43aa8b246200ab5818c3644c8031ef0e886c9908028f20940594430054ec184032262008bf845d5644c4019e6e0882c21900a1f21570584433ef3898220b28867de7230441650c80153b06106c89880ebca0752580310055b426e7b0a644ca76811c165c84014eb0a210c299002b3a0850d8d4100678b8221b0a847ce3443c41651080156d03206c899146a7a0e101913104c5e422e0b086400e3785443644c8a353906a88c898a23a610d745803101d79408e4b006209aac86508424c80155b04280c8991dec7a147250c4302c76412e0b2042088de8714063504014790ab00c8990032d1d37158d210043fc2ae0b0c64008f587140614c80156b09328c29913b271cf64509320055ac0ccbb226400ab584147614c8a753d083aec6a08268fa1070594430072898220b288646af3815c9600c4010ff0eb288790802b960b53185320063abaea3b0a8684c778744165c847d5af00880c6a08039559563cc7212076808221b1a820087f855c1644c4014eb03102ca21146a7a0f51191310053b40880b28640287c855c161cc8014ed0a3a6c299002ad612301853228e4e318e898a4200e578544363504018baca39a839080e3da1e50185323df0f3ae603226400ab681880644c8011ed0f186c299002ada1275d85322653b40ce0b2e4200a9f8650c43c84014f700b92ca21826a72113058c4200578402ca30a64008bf845c1634840b55904a02c8108162f21176d09313cf1abaa20322640faf1811d5600c4019e2e1280c29900297a1420d8d413cd5ac0c20322643aad483441630847dd2c62880c8988268fa1071594430045f43ea7b226408a5f804c16510c015b706aa2c018802ad60470d91320452f41840b28864ea9e83083644c8014b90a886c6a08031d5d710d93210043fc2ae0b1c823ee9764c40635040193aeca18861083ebc60472580310047bc0aeab2262008f587100614c801d2a21bb286218eab520d20185320054ec1ea9b226405ae482441610c80156d02280c8990262f211764c5210063bc3a20b286486c7776c4165c841193d0fbb2862
  | 7 => 0xb681997644c80117d0fa96c8988022fe117058c2100679b8220b22620faf181dc9600c4014dd04382ca218028fe1510d913204d1f420e2b288488e1f305016510c0117b0f186c89880297e1510d8d410043fc2ae0b224200a9d83840644c5090ff0e882cb908029da0430594421ef2b29ea7b0a643d8f7865cb310840156908b08c2990021fe1570586430047ac3cca30a6400a3d85080644c80187ccbba2659080a1fa1770d85421eee821ae018e4200e1d54548635041347908b9aca210268fa1020594430076898220b18424de1e53d4c644c8050f90ab82c520802a760e20191320053b42e8030a6400c3c435d46250c01d2e61880c8990171b1c9654c7210066bb9a20b224200ab6818c3644c8075a902a9ac610946a7a0c20191310064e3a6e6b1a42008bd87140644c80172f02b9286218035c595700c72104c5f43ea63226200e4f52948635040156b03386c89914aa7a0c20d91310055ac0c61b226253ad5811c36350413878c8ba8c8990029e61674580310071bc2a203226200cf170080614c8051bf0ea9ec6a08021fe1570587421fc5f430e89926200ab5818c0644c481caca3a8ec6a0803175d475d8d411d47bc32e39944200a3d848816510c010ff0e882ca190029d606705944300759c02203226400cf1704436150c998ee20bacc5188272719173d093200679b8220b0c6400a3c85443644c49b53d07100c8990028fe1510191320045f438c89926200c3d75d90424c91193886b82c818803175d76310d210055ac08a03226400cb764dc3614c8031dd0db9262909472798c744c7210062f3aec73128208ada84d0d600c40117f0eb20c899002aba0850d91310053bc0ae6b2884098bc845d56308401da0e0886c6a08063de1d10d8f210051fc2ac1b226200ce462dc5324c4014e90ab00c2990163b20970584430055a40aca3226400ab581080644c90f5b706b92c018802aba0850191312056b40c81b1a82018f8805d56210c0196ee9b8ac8990028f61373597210053d42884b006203af281dd5600c413938c8b9e82988029d604705944300578c0ea4b00620287c855c1639040153b07280c8990022f61e30d913200678b846030a6400cf3704c3614c80156b03306c8990038de1510d91311f54fc1a623226200c77855c0614c8071d90cb9086909f32d9d310d8f210446e41aeab20620ea6d821c165c840117b0fa9ec8990023be1d62189430063ac2ee1b0a6400a75818816510c1f5b307ba2c0188233318d7210d2102c5e43aa8b246400ab880597644c80153b08290c6a08038750130594430053ac0ce0b28643feb010443644c411938c6ba064a0802b56062018d410053ac0880b2e4200a3e85083644c49b53906a90c89914eb560772d8d4100556c2041b1282008f687083614c8018e90ab80c299142a7a102018d410
  | 8 => 0x60882ca2100a1f215705843200636baec531262038f4815d5640c40156b02206c899002ad60650d913200679b8220b0e86098be87d48644c813878c8ba884989e78d10910594430065b3a6c330a643d8f687c4163c84011bf06b82c8988021fe157058a410076898220b1e427ce3575c40644c80117b0fa9ec898802b520d61185420045fc22e0b2262038f4815d5640c8755ad07aa0c29900e2f211764cb412056b40ca1b1a8200abb845c9600c4010fb0bb86c2a18031d5d710189430051fc2a21b226289adb835d1600c4071b90ea9ac6108268f21172594430053b40ce0b2886018f481dc1634847b9e6c6b806390a0ba610e54580310065b3b2203226400e726044165c847b5ad06286c2991f3a510f1058c420054f4328621a4200e6b52949600c4018eaecb2e6390803651d0714c8320047ac3c81b0a6400ad48158c63508f956d02080c8990268fa1010594430076898220b1c82038f4815d5640840147f0a880c898802972156018d410062ebaec73128200c5d75d4f6350401d6260880c899002ad21910191320043ec3840b288600c3e75192624c40196ee8882c610903351c76350d410452f418e0b288600ae581880624c40117f08baac690936a7a0c50191320055bc0ac03226430a3d84dc96510c0156d02286c8990030f594744cb2100c7a43a20b0e8400a768510b614c87fc6ca3a8ec8988028f21560d91320054fc32e4a188600e9710dd94310c0b4dd05082cb90802b560e40d85320043fc32ea21e420287c855c1644c89d938c7ba264a08268fe0140594430062f32ee6a0e4200e9130440644c80147f08982ca211df879954310f2100678b86c1b0a64058ec825c1644c40147b08382cb908032d9d864185320046f43ec6b128200c7787441651080153b06286c8988fa2fe1d64d0e3101c7643aa4b1062008f687143614c80187cebb24c4988023d61c60185320053b40840b288600ab5819c3644c40117b0f328c8988023de057058d210055d420eab006209cac645c84348401da6c0880c6a08073c9c110189430054ec18a0322627dcd67344364c847f56d02386c898803a52055418d410053ac28c9b0a6400cf37044363484071e902baac6210033cdc110587320045f438a1b226200a9d84d48635047d1bf0eb1c8720803745c130185322854f426a431a82058f4865c443484010f90e882ca191339ce01105972101c7b43c6030a6400a9f83544644c40156d03286c899002b9608501853201c5e43aa8b2062088dc835d5644847d5ad02100c6a08023d21d105883100679b8221b1a82008ef87588624c40187aeab2087108028fa1740d91320072c98420b288600e3585193614c8014eb0a106c2990031d5d751d854200679b8220b0c8600e9654c4063504019e6e0882c2210021f21d10594430051f420e0b2e4200a
  | 9 => 0x7058c4100566412c1b1a8250a9e84140635047f17f08bb286108fe2fa1e30d91310066bb9e20b224200a7681901650c87f56d02286c898802b9e0930185322964e39ec8a0a6200a9e8390364484015ab02186c690802ab20960d91310053b4288430a6400ad583900614c87d56d02280c8988038bd4a521913200556412c032262008f5878c3614c80187aebb2084988030fdd274597210055ac08a1b226400acf8258063504014e902b92ca21803acd8110d91310056ac0ca1b1a8200c9d641cd41c847d33d0fb8a86218023de1d61185430074db0260322640287c855c163484011ef02baac6210022fa1c50d913200566c10a1b1a8250c9e641cd41c840157309a92c0188262fa1f52191310052ec1820b2886008dd8714063504014790ab86c8988029760c705944200678b80c1b0a6400ab686c40644c8a153908a88c6a0822b620d72580310143e42ae0b1c84038dc8758d430847f56d03286c8988faa72065418d410047ac3c41b0a6400ab481597644c8a75a90c886c6a080ead205545902101d7940e84b006200e716044165c84071e902bb26520942a7a135118d410055ac0841b22644ea9e831d7644c8014eb0a3a6c2990021f617705932100678b8220b1e4200a3e85d03644c47d56d03280c8988031d5d475d85321f55b40c6032262038f4815c1644c8019aee6882c8988262fa1c50191312653a40ae6b2e42008f686dc0614c8815ad03106c6a0802b9a0b54185320047bc0aeab224202c3e75550625040147d08382ca19003a64c210191320045fc3ac83226200a7585080614c80117f08b82c4188262f2117058c210064e3a6c69924200ed1304416210c0156908b06c299002a760f511913100c7a43a20b1a4200ab581180644c87f56d03186c8989f38dd0310594432745f43ea5b226400c7665dc543c8401d66c0880c8989329de01105972101c7a40aed99042008dd8790063504031f100baac8990022f61e60191320074bc222031a823ee9763c40644c475caca7a98c2990023be097058d210061f32ee898e4200aad82994644c47f53b06386c8988022f61f521913100678b86c030a64018bc87501640840187cca3a26390802ad60620191320053ac28c830a6400a5d8390165c840117b0fa96c898802ab60850d91320065aba221b1e420287c855c1644841317908b82c621002ada04601913204e5a324e332264018f4874416448401c3aa8280c6a09eb271d13058c210045f43841b226200acd82994635040193aebbb28621802b56064018d4104c5f43c60322644ec3f645d4635080157509a92c0188021f61770d85420045ec3ea5b226408a9c8359143084031e90e882c319016b32093058c2100c7643a40b1086008df835d941484011bf06baac8988032ddd11058d210055b40c41b226440ad6811c36350401ce4
  | 10 => 0x322623e99f875c54310c050f90ab82c321a0b279ce54d93210143e42ae0b088400ab5841476150c0155d0532ec8988175908575c85210053cc28e4b00624e8bf845d932104018daebb14c4a08ff2dc437458c210143f42ee2b1086018f487441644c4010ff0ab82c22120f1d21d10597210054ec242031a8200c3d605d4439081347d09382ca2190237e0d76505313d64e21ae0b188400a9f83548644c80153b0d38a86218023d61e30185320456c41ae8b006200ab684080614c8011e90e882c8990021fe157058e420061f3aec8212640087f855c1610c8fbcae60882ca218272719173109310047bc0aeab20643d8f687883614c80717f0eb248710802b960b54185323cf59382203226400a9f844406350401ccea5296c299103b4e0110d8d4140f0ebaaa831a823dad683903614c80155d043aec8990022f61c511913200679b8461b0a64098be87140644c81347909902ca219434710d75108310047dc02eab168200ab684d4b614c80b8d8c4bacc4a08031e98175108310065b3b6c830a640087f8744165108031e90e882c2190223720d70588310055ac26a5b0a64408de87903635040155b04286c8988022fe11764c52102c5fc3ac921e4200a9d8650c43c845147b09b9aca210229720d74594320066ab9a21b264200cb464dc0614c80187aea3aec8988033c5c24018532006cab88e2a188609c3e625d4439081317908baac6210023761c2018d410055ac0881b22620faf181dd1600c40156b03286c8988023d60371591323f66b39e21b264200ab684997614c80187aebaa6c8990031d5d510d8f210055b40cc032264008f587980614c8a1c3f0aaa0c6a0803954c110594430055b408403226400ab581940644c40147b0a106c8990033c5c060185321fe5a38ec8a1a6200a3d85d01648c401cb260882ca21823271cd6450b320046fc1aeab224203de2625c031c840156f02a98c8988033c5c320185320043ec2ee1b0a6400a77815d165c84015b706a12c01880237a1c50d8d4101c7a40ee0b18423aad683140614c80157700b28c8990268fa1070594420053ac2ee1b0a644cc747159532c84119a8c6b8864a08feada0620d91310053d42ce8b006200c3e765d4644c87d56d03100c89880335443764c8320053ac0860b2e4203cb4619d2614c80156d03386c8990032d9d910191310065a886eca108400a758188165c84414bb06382ca19102a761075d8d413cd5ac0c20322623ea9e81550635047d72902a188790802c76147250c430055b42041b0a6409a3e84dcd65108f3c6cea880c899002a720d641912100678b82213148200e713044165c840155b0532ec8988029761672d8d410056bc1a4030a640087d85dc1640c80117d0e28ec8990262f210764c9413de4e3a660b184200eb380443644c8071ed0f100c2990262f211
  | 11 => 0x70020540b00001e014090003a60000300501403c0500a0080700780601a03d8100a01203c010130220001280a07c21c33807096000000ff0aa9640800a03e3580486d0080940f820000050000000381e41800303800000002006134450130020241c000000074c0032010204030050425dc450050001d0041aa0480940405300a370640120be0280180300c00c0210307a01802045006bbc050020d80280002604a058010500b404d2c801006020020050040011c8020621d80206f00602c008010066e40080601e0c0003960000741e80701c005e88ad0160ac92051000034031cf00421c1603d004020008000161c80182b0920040080800227c030170ee0280383e00c04c0001d00002404124000620008040b6014058650020080a01c0000781207b0040100713308800da400009008c1600106c6a80b8000221380000100e0bc06000012004128000000181300000209c1086c6220c08300300a4ad358040080b40800000400c2c80700a01800014026004078480020f802007002004010020180700900001c0007583606a054000000262810b0110004d8000c300007c0a00300405401007006001c301701a0b003808012010010621220200000200022c268040300240b00407a068058000120241080411400000000018018058050a87113785903e000018630bc0a80580f07203c168120266245d8000321bc0188201e1c8028020000a917801648050038300300280001200004c0000704005402002000168051440a6128008a700607405007000c080e8120080380680b00003806001162124000000040080400a0b8034e300100008c09802a7e197150c4302e36312eb3126200ed13044162d0c01c6a80882ca21802ad60450d91310061ebaea9b226200a7685dc3614c80156b02106c898903b49c743580310445e43aa8b266400cf3805c3614c807968e2b2286108262fa1f53191320055ac08a032262058df8758f43c84015af02aa0c6a0802ada1051d85320066bb1ee29928200a7b855c9600c4014eb02382cb90802ad21160185320043fc2ae0b226400a7685193614c8015cd05a98c299003a5e055418d412653b40860b2e4209ab484441611080117b0e100c89900e3d20575591322046fc32e7a0e62058dc835db32504815ad02286c6a080297a0e40597210045f43ec8b12627bc9c43dc163104011bf0eb18c6908028f61672d91310065aba6c330a6400ab486443644c80196ced880c8990023be0970584430065bba6e2b1a4200e548544063504031f100baac5a0803ac4c110d91320046f43841b1a8208ad4834416110c051df0ea96c4a08029761420d8d410456d41ee8b00623de944350f614c8011df0eb10c4a093aa7a0c50d913200678b8221b0a6400ab581080644c4031790ea02c9188030f597744cb2100556c10a0
  | 12 => 0xb0060240083b0001140080403c60c088001440088380003a004070492f8b0c3d4250020000000c000344051502aa0001601800648400028136000050135cc060770011b40101500308a0202b000000000090006f60183f818330040020010780bc008002120340303000014401013000074010010140440d02d00009c0100
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x10512550c000400904e1405c1000040103d97215101913247f2410d704416310801c50874c1105944347f8410d304416510801c90645c130185320078421530440644c801a846420930185320068610d85109600c4014d393619700c7210052c65e30440644c80181d875505018d413ee94605308416510c7d8947161a7150c430062c611708c0614c801a90864c110d913247f845d530440644c801a0d546085018d410062c61170080614c801d11304417510e420063460d70080614c91fc90744c11058c210068521484440635051fe12754c1101913200670209704c0614c921691938c1101913201cb4261304416308401294985511018d410040f662651d132c8401871855c0201853247fa0109304416210c7d894815d94310c210068521483440644c401e13854c1101913247f84d01304416510c01a184361674580310050d65c85440644c91fe10424c1105944300784501304416510c01c53874c1105944300724193704c3614c8018d1835c24018532
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1608d390a982203226400e20190825c13018532
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x6
  | 3 => 0x2
  | 4 => 0x209
  | 5 => 0x3
  | 6 => 0x20e
  | 7 => 0x1549
  | 8 => 0x4
  | 9 => 0x5
  | 10 => 0xb09
  | 11 => 0xb0e
  | 12 => 0x1409
  | 13 => 0x140e
  | 14 => 0x154e
  | 15 => 0x249
  | 16 => 0x24e
  | 17 => 0xb49
  | 18 => 0xb4e
  | 19 => 0x1449
  | 20 => 0x144e
  | 21 => 0x16c9
  | 22 => 0x16ce
  | 23 => 0x289
  | 24 => 0x28e
  | 25 => 0xb89
  | 26 => 0xb8e
  | 27 => 0x1489
  | 28 => 0x148e
  | 29 => 0x1849
  | 30 => 0x184e
  | 31 => 0x3c9
  | 32 => 0x3ce
  | 33 => 0x15c9
  | 34 => 0xcc9
  | 35 => 0xcce
  | 36 => 0x15ce
  | 37 => 0x1709
  | 38 => 0x170e
  | 39 => 0x409
  | 40 => 0x40e
  | 41 => 0x1609
  | 42 => 0xd09
  | 43 => 0xd0e
  | 44 => 0x160e
  | 45 => 0x1889
  | 46 => 0x188e
  | 47 => 0x589
  | 48 => 0x58e
  | 49 => 0xe89
  | 50 => 0xe8e
  | 51 => 0x1789
  | 52 => 0x178e
  | 53 => 0x18c9
  | 54 => 0x18ce
  | 55 => 0xb0211
  | 56 => 0x20b11
  | 57 => 0xb0216
  | 58 => 0x20c
  | 59 => 0x16c211
  | 60 => 0x216d1
  | 61 => 0x154c
  | 62 => 0x58a
  | 63 => 0x178a
  | 64 => 0x18ca
  | 65 => 0x154b11
  | 66 => 0xb1551
  | 67 => 0x155411
  | 68 => 0x141551
  | 69 => 0x155416
  | 70 => 0x25551
  | 71 => 0x154251
  | 72 => 0x25556
  | 73 => 0x16d551
  | 74 => 0x1556d1
  | 75 => 0x16d556
  | 76 => 0xd4a
  | 77 => 0x40c
  | 78 => 0x160c
  | 79 => 0x18c251
  | 80 => 0x24d
  | 81 => 0x28c
  | 82 => 0x148c
  | 83 => 0x144d
  | 84 => 0x59451
  | 85 => 0x59456
  | 86 => 0x18d451
  | 87 => 0x178291
  | 88 => 0x178296
  | 89 => 0x59491
  | 90 => 0x59496
  | 91 => 0x179491
  | 92 => 0x179496
  | 93 => 0xcc3d1
  | 94 => 0xcc3d6
  | 95 => 0x15ccd1
  | 96 => 0xcd5d1
  | 97 => 0x1715d1
  | 98 => 0x1715d6
  | 99 => 0xd0411
  | 100 => 0xd0416
  | 101 => 0x40d16
  | 102 => 0x178411
  | 103 => 0x178416
  | 104 => 0x41796
  | 105 => 0x160d11
  | 106 => 0xd1611
  | 107 => 0x160d16
  | 108 => 0x189611
  | 109 => 0x189616
  | 110 => 0x161896
  | 111 => 0x59611
  | 112 => 0x59616
  | 113 => 0x160596
  | 114 => 0x179611
  | 115 => 0x179616
  | 116 => 0x161796
  | 117 => 0xe8591
  | 118 => 0x58e91
  | 119 => 0xe8596
  | 120 => 0x58e96
  | 121 => 0x94d
  | 122 => 0x9cd
  | 123 => 0x168d
  | 124 => 0x138d
  | 125 => 0x94c
  | 126 => 0x138c
  | 127 => 0x94e
  | 128 => 0x138e
  | 129 => 0x104c
  | 130 => 0x194c
  | 131 => 0x2c9
  | 132 => 0x14c9
  | 133 => 0x154956
  | 134 => 0x1a0a
  | 135 => 0x255d1
  | 136 => 0xa0c
  | 137 => 0x258d1
  | 138 => 0x180c
  | 139 => 0x3d8d6
  | 140 => 0x589d6
  | 141 => 0x58a16
  | 142 => 0x595d6
  | 143 => 0x9c955
  | 144 => 0x949d5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2045
  | 6 => 3424
  | 5 => 1585
  | 4 => 41
  | 3 => 2
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
  | 8 => 2*((h/34+packedAt gbK8 (1612+(h % 34)*6) 6) % 62)
  | 7 => 2*((h/723+packedAt gbK7 (75665+(h % 723)*11) 11) % 2045)
  | 6 => 2*((h/1141+packedAt gbK6 (164352+(h % 1141)*12) 12) % 3424)
  | 5 => 2*((h/528+packedAt gbK5 (93515+(h % 528)*11) 11) % 1585)
  | 4 => 2*((h/20+packedAt gbK4 (2870+(h % 20)*6) 6) % 41)
  | 3 => 2*((h/1+packedAt gbK3 (162+(h % 1)*1) 1) % 2)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff03e07e03ff81ff83ffff04fb18f8c78e3f
  | 1 => 0xfc03fc007ffc0ffe0ffc1f001b65e760f8f3cc
  | 2 => 0x3ffff80000fffffffffffe386078700ffff
  | 3 => 0x3fffffffff0000fffe000fc07f807ff03f0
  | 4 => 0x3fffffffffffff0000000fff80007fffc00
  | 5 => 0xfffc00000000000000000000fffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x343b00a01651529092a1392a00290828c38615
  | 1 => 0xb84b2c002ad545b285a51a0609616360d8b2cc
  | 2 => 0x80554c80000945294a44d46286058300596a
  | 3 => 0x11119a754d1a60000e738818b407b8056d03b0
  | 4 => 0xa222e39a71e38e79c0001060dff80006b6ec00
  | 5 => 0xc3c0001c0182006100420080ffd6d6d0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafee0e0a0feeaeeeafee0e0a0feeaeeeafee0e0a0feeaeeeafee0e0a0feeaeeeafee0e0a0feeaeeeafee0e0a0feeaeeeafee0e0a0feeaeeeafee0e0a0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40523
namespace PEqualNP.Outside.L_meta_40523
open PEqualNP.Outside.L_meta_40523.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 27 := block_range (n:=27) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 27 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_96 : Interval s0Atlas 3 96 48 := block_range (n:=48) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 144 := (concat bs0_3_0 bs0_3_96)
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
theorem bs0_4_864 : Interval s0Atlas 4 864 19 := block_range (n:=19) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 883 := (concat (concat (concat bs0_4_0 bs0_4_96) (concat bs0_4_192 (concat bs0_4_288 bs0_4_384))) (concat (concat bs0_4_480 bs0_4_576) (concat bs0_4_672 (concat bs0_4_768 bs0_4_864))))
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
theorem bs0_5_768 : Interval s0Atlas 5 768 34 := block_range (n:=34) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 802 := (concat (concat (concat bs0_5_0 bs0_5_96) (concat bs0_5_192 bs0_5_288)) (concat (concat bs0_5_384 bs0_5_480) (concat bs0_5_576 (concat bs0_5_672 bs0_5_768))))
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
theorem bs1_3_0 : Interval s1Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 8 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 9 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
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
theorem bs4_3_0 : Interval s4Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 2 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 6 := bs4_4_0
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
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 13 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 75 := block_range (n:=75) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 75 := bs5_3_0
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
theorem bs5_4_576 : Interval s5Atlas 4 576 50 := block_range (n:=50) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 626 := (concat (concat bs5_4_0 (concat bs5_4_96 bs5_4_192)) (concat (concat bs5_4_288 bs5_4_384) (concat bs5_4_480 bs5_4_576)))
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
theorem bs5_5_672 : Interval s5Atlas 5 672 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 699 := (concat (concat (concat bs5_5_0 bs5_5_96) (concat bs5_5_192 bs5_5_288)) (concat (concat bs5_5_384 bs5_5_480) (concat bs5_5_576 bs5_5_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 42 := block_range (n:=42) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 42 := bs5_6_0
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
theorem bgb_3_0 : Interval gbAtlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 2 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 41 := block_range (n:=41) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 41 := bgb_4_0
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
theorem bgb_5_1536 : Interval gbAtlas 5 1536 49 := block_range (n:=49) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1585 := (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 bgb_5_288)) (concat (concat bgb_5_384 bgb_5_480) (concat bgb_5_576 bgb_5_672))) (concat (concat (concat bgb_5_768 bgb_5_864) (concat bgb_5_960 bgb_5_1056)) (concat (concat bgb_5_1152 bgb_5_1248) (concat bgb_5_1344 (concat bgb_5_1440 bgb_5_1536)))))
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
theorem bgb_6_3360 : Interval gbAtlas 6 3360 64 := block_range (n:=64) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3424 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)))) (concat (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 bgb_6_1152)) (concat (concat bgb_6_1248 bgb_6_1344) (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632))))) (concat (concat (concat (concat bgb_6_1728 bgb_6_1824) (concat bgb_6_1920 bgb_6_2016)) (concat (concat bgb_6_2112 bgb_6_2208) (concat bgb_6_2304 (concat bgb_6_2400 bgb_6_2496)))) (concat (concat (concat bgb_6_2592 bgb_6_2688) (concat bgb_6_2784 bgb_6_2880)) (concat (concat bgb_6_2976 bgb_6_3072) (concat bgb_6_3168 (concat bgb_6_3264 bgb_6_3360))))))
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
theorem bgb_7_1728 : Interval gbAtlas 7 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2045 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 (concat bgb_7_576 bgb_7_672)) (concat bgb_7_768 (concat bgb_7_864 bgb_7_960)))) (concat (concat (concat bgb_7_1056 bgb_7_1152) (concat bgb_7_1248 (concat bgb_7_1344 bgb_7_1440))) (concat (concat bgb_7_1536 (concat bgb_7_1632 bgb_7_1728)) (concat bgb_7_1824 (concat bgb_7_1920 bgb_7_2016)))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 24, 25),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafee0e0a0feeaeeeafee0e0a0feeaeeeafee0e0a0feeaeeeafee0e0a0feeaeeeafee0e0a0feeaeeeafee0e0a0feeaeeeafee0e0a0feeaeeeafee0e0a0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4276150432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40523.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.and,[1,6]⟩,⟨.or,[2,5]⟩,⟨.and,[3,4]⟩,⟨.or,[8,9]⟩,⟨.and,[1,3]⟩,⟨.or,[7,9]⟩,⟨.and,[2,12]⟩,⟨.or,[0,11]⟩,⟨.or,[13,14]⟩,⟨.and,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276150432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276150432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40523

open PEqualNP.Outside.L_meta_40523 in
theorem PEqualNP.Outside.L_meta_40523 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276150432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276150432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
