import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40203.Model
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


end PEqualNP.Outside.L_meta_40203.Model

namespace PEqualNP.Outside.L_meta_40203
open PEqualNP.Outside.L_meta_40203.Model
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

def SBf (j : Nat) : Nat := [7, 7, 6, 5, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_40203

namespace PEqualNP.Outside.L_meta_40203
open PEqualNP.Outside.L_meta_40203.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x4c0170020c04820000020cb000103542041540140047ff32fe42fc43fd31fe43fc10bf42fe21ff31ff43ff41fd40bc40fe20ff20fc32fd21be40fd42bc41ff42fe30fe10de32fd41fd43fe32fe41fe40be41dc32ff10fc40fc42fe31fd30fc41ff30ff21ff40fd20bd42fd10fd32fc21fc20fc30fc31
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x100010d05032b030002004b140200010600010107000a40041c1003022800000100010b002d0d03010900200004006904090900001a00000008000006000e7701041900710000092ccf29e853d54c867ca320cf940419f286853e54c427ca9905b14931e6a10653d529067ca90857d4d219f2a085ad42ccb5a8419678ca40b6292616f524c27aa5204fd5220bba8a415e520cb986410cf95232ae29a416f524c6f0a098cf95330e7210659e321076ca220d754f429eaa0413c544c3386420730c820ae29a439f428cb70a0a15b149109e2a2215f53443386520ee10320e619441b441086f0a090d7d4d42cf2a4659d420ca7aa9984f95032ba28a613f544867aa9214d145429e282853e54c86bca5194f942419e2a0219d53d0a7ca2206795032e6194438d420ca7aa420cf55331b6a96873c5150a78a898eed4142da20e439c329027ca3204f15120e729065785050a7aa9084fd5130bda82433c548873aa8194f553209faa0215d538867ca1204f55232ae29a213c548827aa810cfd5110ce19083b45150aeea2a15d145209ea90815e538835ea4a167d08329f28883b8400827aa9884f94742bba8a617b5050abca710cfd5221b7296879f5350abca6084f95331cf194835c5350b3c64204f950209f28081385050af6a098e714d42dba8a853e540873aa9196750a32dd280813c54486dea4885d14542aea9c415e53d0abaa6084fd51319eaa065f110042bea6904fd5120
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x218020051504b0c6004880004001443002006000044a3592420ca346154840aa181420caa4615083287d95420ca8e63d49428e594400830d520c841aa18142cca356510421a3592520ca386054841c6d4c5050b0f540ca21c5d4c5150ae06244010a6181420ca4c6254c10e10c8410868c615083287597420cb0f6550832a5185428cb883210020a918542ccb0d520c840a2181420ca8c6050832cc1475050b0f540ca20c614c5050b1453145428d987548822d6215010e2181420ca986050a32e1185420cb0d540c821b418d10042c46150832e2d81420cb305114142e1d85420ca8f6550832b2181420ca8461508328e98354887335114142c355032082946150832
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x200000205a01876050832a14e1aa06510e09650c8400828338ea819441421c1520c841d06c23028419504715483210302b286420843a01846050832
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 136
  | 3 => 50
  | 2 => 9
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
  | 5 => 2*((h/30+packedAt s0K5 (768+(h % 30)*6) 6) % 48)
  | 4 => 2*((h/73+packedAt s0K4 (3672+(h % 73)*8) 8) % 136)
  | 3 => 2*((h/30+packedAt s0K3 (1900+(h % 30)*6) 6) % 50)
  | 2 => 2*((h/10+packedAt s0K2 (441+(h % 10)*4) 4) % 9)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x7ffffffffe03ffffc0ffffffff01fff1ffe3f
  | 2 => 0xf80fffffffffc07ffff03fffffffe03fe3ffc7
  | 3 => 0xfff01fe03fffffffffffc0fc03fffffffc63ff
  | 4 => 0xffffe0003fffff80ffffff0003ffffc0ff83f8
  | 5 => 0xffffffffc0000000fffffffffc000000fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x409225228a2389122c02cb2d54b10e590dae1b
  | 2 => 0x4e8449451444872454b015569957222a62d6c5
  | 3 => 0x122e1089a689124899554098c26a54b4b4616e
  | 4 => 0x64c89d163912240ee669a603138d9b08db83b0
  | 5 => 0x870f1e183e1c3870fb8e38e3e00e1c30ff7800
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0c0c0fc00c000fcc0c0c0fc00c000fcc0c0c0fc00c000fcc0c0c0fc00c000fcc0c0c0fc00c000fcc0c0c0fc00c000fcc0c0c0fc00c000fcc0c0c0fc00c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40203
namespace PEqualNP.Outside.L_meta_40203
open PEqualNP.Outside.L_meta_40203.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x30170011c724208404484205c3031c6fe41f721fd31fe42fd42fc30fd41fd40fc41fd43fe21ff21fc43ff41ff40fe32fd21bc40f421fc40fd32fc42ff43dc32fd10fc20fe43fd20ff31fe10ff30ff32fc10fe31fe30fe40fc31fc21be40fd30ff42ff20de32fc32fe20ff10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xd000000002041021400002000800604000006e000020000980005400002001030000000000000d00080002e00000002e68000105000098000000000200040150000d010400000000800200200410004000001808100018010000000001800300000800000000000428002000020000002000408500000040000980000005d54440da108815e530427ca8195d54732cf1908176510c398641057d4d10af29c43ae521035aa4205bd4930af294656c524c3aa6218ddd4542e619043ba50102b8a6a15754e21b7296877551d0fc842105d94821af29e857551d0bcca410dd946219f2a6617651d0abca41979908219eaa6217b5050b3ca8194f55032b6a90816c52442bea690cf95021ae29a21c432086b8a6905e14142ceaa0656e521033aa6204f940409faa221ce520cb9865106e10020db288817551882dea488750cb21bb28e8774514c2b8a690dd94732ea190433d54086eca3105d145329f2a6219e53103c843105754c40aea9e833d54cc2eea2985754e209f28481cd420cae8a290758cb21db2a043e732087ac6410e70ca40bb288815e53883c86410f30ca21f2a10435f53482bca6204f151309faa241b7219027ca9905754c10cf19481b421902eea2904fd5130ba28a85b5511027aa9905b54b43aea9e856f524c73864205794f41baa8861b840c82daa5a0cf15110b629263b554086dca5a0ddd4532afa9a85ce420ca78a8906dc8440
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x928010205008101860b2181420cb255254440b198a3208786640c821e15903208785540c821d194c218821d650c840e10c82110384320864099189510c2c4624c431c354d5210386540c821a959032086c46150832c3550320874432946209318953043a021100208d59421102e06050821e20c840082c46350821
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x4000c0aca1904220485769503208682ba86410881415d6640c821
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
  | 4 => 2*((h/144+packedAt s1K4 (3159+(h % 144)*7) 7) % 117)
  | 3 => 2*((h/15+packedAt s1K3 (912+(h % 15)*5) 5) % 24)
  | 2 => 2*((h/15+packedAt s1K2 (196+(h % 15)*2) 2) % 4)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffffffff01fffe07ffffffffffc07fe3ffe3f
  | 2 => 0x7f01fc07ffe07fff83e07c1f80fff83fd933c7
  | 3 => 0x7ffe0007fffffffffc007fe000ffffffe1c3ff
  | 4 => 0x80000007ffff81ffffff800000ffffc1fe03f8
  | 5 => 0xfffffff8000001ffffffffffff000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x914284011c104200c628c228e2c42520a561b
  | 2 => 0x2a4c51cb224728e581aa351b1255ca34d932c5
  | 3 => 0x44289a95448a514ab4105b48249a94a961c16e
  | 4 => 0x68b1636689141db35adb021248e36711be03b0
  | 5 => 0x70c183870e1861dc631c639c70038421f5a800
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafa00a000faaaaaaafa00a000faaaaaaafa00a000faaaaaaafa00a000faaaaaaafa00a000faaaaaaafa00a000faaaaaaafa00a000faaaaaaafa00a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40203
namespace PEqualNP.Outside.L_meta_40203
open PEqualNP.Outside.L_meta_40203.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x80001504ec32de32bd41cc32dc32bc40bf41ef32be40
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xc000000028c6aa0658c329031864204d54440c6192838c32d069ca5196395032
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x8359432103043254440a1586540ca0d650cb41
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | 2 => packedAt s2K2 (i*38) 38
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/10+packedAt s2K4 (144+(h % 10)*4) 4) % 9)
  | 3 => 2*((h/23+packedAt s2K3 (216+(h % 23)*3) 3) % 8)
  | 2 => 2*((h/8+packedAt s2K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffe07fffffc0fffffffffe07fffe3ff1ff
  | 1 => 0x81fc0fff83ffffff0783c1f03ff87fffd24e3f
  | 3 => 0xfe000ffffc0fc1fff803fe003fff8781e38fcc
  | 4 => 0xffffff001fffffc00003ffff801fc0ff0
  | 5 => 0xfffff000000001ffffffffffc0000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8828002300208000188442118a0088940490d5
  | 1 => 0x24519644194530cb032191a214c85568d2462a
  | 3 => 0x149aaa8928ea13556842f484a755060d638b4c
  | 4 => 0x59634d125283a5a6b5e8210939a66031bc0db0
  | 5 => 0x61838e1c630c39f8c67339ce01c44441fb6000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaaee888888eeaaaaaaee888888eeaaaaaaee888888eeaaaaaaee888888eeaaaaaaee888888eeaaaaaaee888888eeaaaaaaee888888eeaaaaaaee888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40203
namespace PEqualNP.Outside.L_meta_40203
open PEqualNP.Outside.L_meta_40203.Model
def s3K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x22236196d20de65bc83610ee21
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x40208e438869105208c43482990732
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*4) 4
  | 3 => packedAt s3K3 (i*15) 15
  | 2 => packedAt s3K2 (i*26) 26
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => 2*((h/1+packedAt s3K4 (4+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/9+packedAt s3K3 (90+(h % 9)*3) 3) % 6)
  | 2 => 2*((h/8+packedAt s3K2 (104+(h % 8)*2) 2) % 4)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0xffffffffffffffffffffffebfc79ffe387fe4f
  | 2 => 0x72ff81cffc070f8c
  | 5 => 0x7cfffe0ffff80ff0
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa018100104912095
  | 1 => 0x142322862122c64a
  | 2 => 0xd49751b48546b8c
  | 5 => 0x38241ac92608d60
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 39 s3Pos s3Neg, 0xeaeaeaea88888888eaeaeaea88888888eaeaeaea88888888eaeaeaea88888888eaeaeaea88888888eaeaeaea88888888eaeaeaea88888888eaeaeaea88888888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40203
namespace PEqualNP.Outside.L_meta_40203
open PEqualNP.Outside.L_meta_40203.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x8140004a000020400c00432849000010010011005ca0032c0200fe32ff30fc40fe42de32fe31fe10fe20fe21fc30ff43fd40fd41fd21fc41fc10fd20fc20ff40dd43fe40fe30fd31fc31ff42fe43ff32ff31fc21fd10de43dc32fd43fe41fd32fc32fd42fc42ff20ff21fc43fd30ff41ff10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xb00092d00209b1c6c040012e000040004000000040434001060208ca60008080360c0012528000006800d5a00001100c2af00008000048004021000000073a87a15714d42af298855d5310b98a4a1e795032af298215e53d0adca5185b94b41af29c436c52442bea8195754c10aea9e85cf420cabca7a0db54b41aea9c433d540c73a86205754c41e6192416f52442bca62057d4d219f2a0635d540ca7aa8084f95221e6194433d54886daa4084f95010b6a90813d540cb986410d794832af298837651d0abaa620730cb20af298876e52042bea6905d544409faa2213d54cc27ea8905714d219e2a2215d53882e8a2906750e40b7290816d528c2bca521cf95032ae29a411d540cab8a68857d4d10cea1a837751482bca7105d54742af294656c524c6d8a4a1d754f40e6210655f548cabaa921dd94440ae292876f5250e78a8904f95330aea9e835e53d039ca4195755232afa9a856f524c73a87a0e7d5143ceaa065cf5250e98a4a1e750d42
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x100039000108221020002a0a08028c6250c40a3189439028d640ca21a359032c824d6510832c3950328870d4354840c3189540ca1d6494e20a3590320868d640c920c350d52d070c540c920b1987420ca1d6414d21a318943d064c6254f40a318943d0a4c6254c41d10c851483154354440c550d51d0a1d6595032c3553420ca8c6250d41
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0xc0000028239286a8e85035d8540c920c0aa930e8419505740c8514828239286a8881035da540ca21
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 6 => 2*((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/35+packedAt s4K5 (704+(h % 35)*6) 6) % 44)
  | 4 => 2*((h/72+packedAt s4K4 (2430+(h % 72)*7) 7) % 90)
  | 3 => 2*((h/22+packedAt s4K3 (950+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/16+packedAt s4K2 (294+(h % 16)*3) 3) % 6)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1fffffe07fffff03ffff07ffff07fffcf1f1ff
  | 1 => 0xe07f07ff83fffffc1e0ff8781ff87fff4e4e3f
  | 2 => 0xff8007fffc0fc3ffe00fff801fff87038f8fcc
  | 3 => 0x7fffff003fffff000001ffff803f00ff0
  | 5 => 0xfffff800000003ffffffffffe0000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x420a00230020800062110088c50089281090d5
  | 1 => 0x89144a441945212c0c8648510a4852d146462a
  | 2 => 0x4526948928ea0655a10b95025395041a8b8b4c
  | 3 => 0x9658e7125283ab9ad7a0c4449ce66063f00db0
  | 5 => 0x1860c61c630c33e319cce66700c44083ed6000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeaeaeaeae888e888eaeaeaeae888e888eaeaeaeae888e888eaeaeaeae888e888eaeaeaeae888e888eaeaeaeae888e888eaeaeaeae888e888eaeaeaeae888e888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40203
namespace PEqualNP.Outside.L_meta_40203
open PEqualNP.Outside.L_meta_40203.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300500000000000000808004a1451800480819c700500004a002fd10ff31ff32fc42ff43fe42fc43ef32fd41ff20fd32ff41fe41ff21ff10ff42fd30fd42ff30fe20fe32fd40ec32fd20fe10fe43bc43ff40fe21fe31be43fd43fd21fc40fc10fc20fc30fc41fe40fe30fd31fc31fc32fc21
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x283ec420cb7ca9197bd0c32bf28c81be430c67aa8107b948419faa261ef50ccafca020db54b43bf286437c534877ca810df94232f7296876f5250fde64905f15120de21c417d53486fea810dfd4540df21e837e50102faa5a05f54c42bfaa0637e5110feea2985f55130fda8263ec328877c86187b50b32fda0281ee528c2d8a4985f14d40cf298877d5110efaa8996fd0740bea8e417e544cbde6498ef90d40bfa9a43bc43d0afaa018ef10d30bf294657f5350afca5206f90c42bea8c21ec32503de6420efd0e43fa188217d51902fea5885fd4f20bf28c857e52c43dca3995f54e20bf298817d520c2faa8085f55242bfa9a41fa40103f641107ec4110bf2a0417d5010e7ea898cf95230de280877e53483788720fb95032dea1283ec524c6baa6087e44010dfa8c87ed4210afea790df54d20dea1683bc430835887995fd5332f621665ef524c7d8a3995f14530b729081f7314c7de65985f54430be29a833e54043daa3995f94030be2a661de53042faa8907d0c610f619621ef320c2fca3195f55320f619021ef320c77a8220f78c932be292637e54cc2fca8905fd5320b6292877e50cc7b887195f15230dea1887bd548c2faa5105dd4530efa1c873d548cbde65a0fb94432df2808774514c2faa7a0dfd5321bf288433e548cafaa7905f94b43beaa2439c430cbbe64195f55241bea9c637d5110b7c860877d0d43bfaa2637e51d03de411077cc530de21e43ec32842fca320fd14530dea8c87be43c43daa9997b0c840ee988637f514cafea09977cc631bf290837d548c2f8a2905fd4c20bfa8a85ef43ccafaa3985f15310be29c437c53482faa40877cc230f72a6657f54842fca120df94e20bea8443ec510caf8a5886f90e10be2a463ec5250ff661887bcca21bf288653e5390fec8220ef94243afa9a85be43102f8a8995f94c30bf29a217e51d0fbe86195f15320be2a4417c53c82daa5185f54632bf29865ed320cafaa610d714d42fd98021ec50ccaf8a8885f95043bea84857f52442faa3996fd0040d7218657d520c7de40106f50842fb88021dd31cc3788690df94631be29c41bf41106faa2207b0ca20deaa463ec32cc77ea898ef90e20bea8c85ef540cafaa5085fd4d41beaa4437f54cc6fca5215f94f42f7a8865be40502faa4886f95230f888021bc43c837aa8085f94230be282837f524c2fca820fe0c010eea18877c53c43de64087b54810be28287be43cc6faa6086f90d32fc18621ec540cb7ca221dfd4c21fb88421ef32c42fea498dfd4121df21e43bf42506fca9195fd4f10f6a80657d540c37887a05f14543beaa0417f544cafca7207bc8720f790843ed528c6fca9996f90f42bf2a0437f544837887215f95121f7992817e53842faa321df94242de2a261bc5290fdc64195f54b31f799081ef51ccbee8320df94810
  | 1 => 0xd50d0efca0216f95020f6190437e5090fde6520df14f21f7992617e54842f8a9085fd4543bf29c877e54c86fca8185f14a10be29283df31cc2daa420df94c31fd902417d548831886196f15132bf28c877d510837c86a0fbd4943de21e61ed430cafea9107b90832bf2a6217c5250e7aa810df14121beaa221f8504c6faa898f394c32bea8c41be430877ca621ef10c31de2a2637d548c6faa3a16f90f20bea80657f53043bea6a16f90541f7a92617c54ccafca1995f14142bf2a085bc438cb7886215f94220df21e817f52042f8a8197bccb21bf29e43dd53043d86490efd5132ce21c65ec32903de84195f54841faa0883bc430c37887a0fb90b329eaa463ed42c83de4310ef90e42d6a10857e50086fca9105f15131df2a0217e50d0af8a8185ed4131bfaa661df310c6fca4196f55021bf290617d5090efea0a17b90920beaa663de304c3d864a0fbcca31bea8c617d53902fca1a1dfd5230de21c433d540437c8690df55321dfa04816d52042fca720df94441e7a18657d538c2dca6195f94430de21c637f540c378a221ef90c32dfa1887bf42d067ca8105f15021f619221bf5110f7aa221df94b30bea96833c544c7ba62985f54740bfa82877d51d0fda42905f55031be2a643bf4210b78a321fb0c920bf29683ec328c2faa5187d4c431bf28087ed424877c8698df15221bf28c61ec430cadea4985bd4931bfaa465ef32c82d8a498fb0c931de21a857f53843ee6318df14542ef99465be5210fde6410df94910dfa0c83ee52102faa7a07bccb40f721e65be43442fea098df94c10fba0a837e52086fca1a0df54321bf2a4637e51886faa5205f94420f6a10657c54082faa520df54b30dfa9487bd40102fca6107b50f32be29c21bc43ccafea710df54a21be2a261be438c37886086f55020b7290217d5290efca621df54042bf2a0637c504cafea6a05f94431f6190837e51882faa7a15f94c42de21e217d54c42fca118fb0cb30bf298437e5290efca018fbd5332f799243be43483de65207e88020f729865de314c77c86a17b94332df21a87f5100437887085f55210f799461bc43102dca5186f90c41bea9c21ec524c2fca0197bd0a42bfa8a61bd42d03ba60186f10d409eaa461ee4210a7ea8997ecc230df21285bf544c2faa010fb50920efa1c656d5210278a8996f50740f6a9083be5190efaa118eb10c32dea90877d510cafaa810fb15332f7a80657e52082fca3985f14c20f6190637f525037886997b55032bea9841bd548cbec20887e8c0309f2a0437d50d06fca518fdc8521f799221bf42503d864185f95040bf2a6417f53442faa790df14810f7992837c504c778a421fb0cb41df21e617e5210afaa921df94a41e621865bc43086fea7106f90e21df21e657e544c7dc4290df95331bea94637f51483ea4210ef10f31bfa9
  | 2 => 0x860082e2c82c000020600025824000380e0000980a0504c0081a018004582c350000a000000ea0003014818030c0020c4228b02d8020180204804098aa0200a001ca0021e040cc04a1c0bb8e06800bd81047acef90500d000010080f086038000000c090001f01e01b2601042508020484c0002c22820053ee0280c0200481802080001003200000e8010120201e806008120080003800050001981a16838000e600a90838020100604018218000186206000048020081c4e836090084f02409830000d20a0082f01c000001280c02010069100703a238002f026468400005c00002010001ac94048000a0180080a0001e0182a000160089c078002e84c000980801e3d8213b1ba232380d0a822806018000a000008b0040020400600142c100e0000c00806140d20003c6aa920d818005680880c1104a180001180827800b401a1380209000100200000026426040001083c048000280001130008ea0f09c160000380228833ef324cbba64195f15031bc28263ec32906fca7885f94440bfaa021de4310f7e85a05fd5130f721643ec32082fca421fbcca10dfa14857e53886fea0a0f7cc030de21c81ee528c6f8a4885f54c40f710241ed210877c87195f94a30f6a86657d540cbee4310df54232fb988217e54443d864985b94a31ee21865fb10842faa9987e48020bf2a261ec32c86f8a9196fd4243bea90817e548c3de84a15fd5020fb188637f54486fca8085f94410f799441ee52042fca910ef10c32bf28421be439077ca918df95032dea1281bf5210f7887186b90f32beaa665be43082f8a6885b54a31df21a617c54cc6faa710df54342f621e65ef320837aa121df15121bea8083bc43443ee63084f95231bf28e413c544c37a82a07ed0240bf28e85ef32cc6faa421dfd5221de284877e5110bda40105f14c10f6a94617c51502fea8885f54d10beaa4657d53106fca690fb54b43bea9e21dc5350afca110df94a10beaa481ee42c82fca5a05f54b10bfa92877f54c437ea021ef10d31dea80877e5390bd86518df14d42bf29e817e50902fea5087b0cb40f6a90817e50043de85996f10d20fd080217f540cbd8a0197b48720af298217e52cc77c87207ecc130be29261bd5290edca5195f54b43bf29e417e51ccbde42906f90e31f6a1643ee430cbf260185f94831f6a88657c530877886a0df54e32bfaa4637c52502f8a2995b94b43f728065f940102fca7a0db94841f799465bc43106faa720df94840be2a0217d5390b7e82a07d88421f6196417d50ccafaa120ef94a439f29887ee42486fca0105f54331bf298837
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x4540ca6f6254c41d6181530423d64d4c219b588530431f5310d428fd9153842ce6390c329bd9732103345414530d394c320863f65500409e982544c78c43940328fd91524426c6255110d354c329072c43948419b597430ca6d65908329b588548c66c6254f40d394e520432c431493197d8d544ca3f6454e21c794c431063e64150109bd97320432e5494a319d594310438c6510c32cb549411069d6510e32cd153514c32e43948109b98b540438c6350842b318d424832d5454a319e582544c63d64940308f59250cc63e6414520da0cb504c66d6295131ce150504c76832141318f59252cc66e62150318f99353c872d54c80208f590504863f6454d10ab59250ccae860485209ed95200826e62150109b59732106b661148439b195424834c53cc9218f996434ca3f6454d21cb551528c23d6510c20cb10e528c2776154d10ae181415038f6510c328f590530425f63551219b588540c23d64d4c209bd8953d03d153440109758c540437365440109b988505063e63950219b98e521063e6515131cb550420cb1c5310d10bc98d100423e6590d309e980540caae6414432bc181310c72e5450b329e181534866d650c810cd10c514c34e6394c32dacc8504c65f654c832d9d4651cca6f6254c40cb951520423c6454d20cb15142c82d8604c7309798f548827b6054d21b318d42486ae62d0c438f19153086776548421cb90e521025d6510c329d986544c23f6590c208f596430423d6494732ab191320ca3e64150219bd8953d066f6550c32a798a5310f3443d45309b594321073854d41319b588544423c6454c209d984530836852d4131c794c43d029c6350842e3988430caea60144328fd9153082776154d209b988548c6ad62140439d98753c82756114c209d984540c33a43141318f994544c32c54149309798c540434e530ca4097596530432c54d4930cb10d52102ad62d0c438f59353c825d63d50109b994324c6b56110c41e394c430cb2c5414931e310f500cb8e6110c32c798e5310ecc6350b208f59443042ba60148438f99250ccab96010c40cb90f524c6ad6414032c7d91530434c530c940c794c438823e64d4d208f99252cc6ad6294243e310c328c26c6254f419bd89534823c6454d21b9584320866d650c8208f590530866f6255110c714e435023d6414b10f80c910043e332440109b994324c32c5450b219b58b538438c430ca10d354d520434c53cc920ad9845010f8c43d4432d394c32c826e62151108f994544ca3d6510c21bcd95100423f6510c10ba580320823e6510d30cb950320826d62d4f108fd94430823f6550842c7550438cb1d5310c10b3992530ca5c6355110ba983324834e530cb21a718d42d06ae62942439e98353c867561951308f990520435451cc530f494d100426c6254e109b58854c426e62d4c21
  | 1 => 0xc32e5454a31e310c320426f6548020cb14942503e15244010c7d8d548cb8c430c930cb952520426d62943319b588540438c4390832e310c320823f65504419b98a50cc63e64150209b988548c2796584010e3d80430ca3c6454e10cb90d521032e540c8218f593520438c430cb20b9984500ca3f6454c10ec10d100432e54cc8219b988548438e5390c32ab99251cca3f6454f20a718d42d038d6110c329b596520426e65cc920e310d320ca6f65484219dd95100438c43944329b98b534423f6454f108f590524423d6414520e310c32882af6250c43cb10d521074d530c810cb90c524c31c4394832d354f320438e6310c32dc147304c26d6214540bc18d100423f6454f21b3594430ca3e64d4e208f992520ca3e6494431cb5485210f8d6210c32c794c43886756115320e398c43cca3f6550c439b58a5190e6f650c841c714e4250a3c6454910e310c328c72f54cc930cb151420cb8c43508329e18154486af644c8329bd954210bb15444010cb549401023c6315130c7192530423e64d4e21ab59251cca5c6355121e310d500caad64908429b997324c72c54d4931d3d4c325063e6494730d3d0c5250ece63d53329b98b548c71c5390d428fd94430874c6254c10c7d4c434426e6295331e310c325023d64d4d108fd96430426e6215030c714c43482ae6494332cbd53324cb2c4354a308f98e540826e6215310d354e520432e43d49308f99052c423c6454f219b18953c425c63551209b98e521023d64d4f109b594420cb8c4314032e310c420ca6d62d4c108f994434c66d62d50108f590530838c430ca21d394f328826d62947309e181544c74f6254c10ab9885110e3e6414c208f993530833551144439e580530863d6595020cbd5254cca3d6595010cb94d4210b2d42540429ed81534423c6454d10d3597430cace63150329d98454c82ad648c832cb94e430cb8d6510c32cb552528c71d6510e32ab98b4390f5953cc0109b18d52043733114131e3d84430ca6d650c821b318d42c866f654c832d394c329063e64947329b58a544ca3d64d4c10cb90e528c72c54cc9329b58a54cc72d54150328f99353442ae62140439bd89539026e6214c10cb550328c78f6350842ab1894310f2d54cca31c7191530434e530c810c7994430cacd62d0c329b58b548c38d5410c329b588548436551144329bd89534434e53cc810cb953328c32d52d0441b9584540cb2e540ca309ed95300c2ae6310c32c794c43d0aad6414432cb551520432f54d4931c794e439068e6390c32ec95110042746155120d314f4250a7b6550040a798e430caae62946438f992544c67b60551319b58b548c74c6294c10e310c32cc23f6454c21ba580540cb1e5390c109b597321038c438c8329758f548866e62d4c20b3d94430ca6e62d4c109e98054c866e62150219d98
  | 2 => 0x6414c10e310c320c6ad62946439b98a51cc2b5611484397d95300c26d6215230c794c430426f6254e108f18d54083395014043cb10d528c71f5310d219798f548874d62d4d42cb5095110b2e4354810d3d885350a6d62141418f996434c71d5494c10e310c324863c6355010c7d92530423d6494b30cb550320436950140329dd85544833451505409d185544c25e6314810ab990500ca6e63948108f191530423c6454f10ced425090f375194643b398c54cca3d6494332ae5805210e3e6510d32cb10e520426e65cc930d354c329038c430ca41cb55332043546154c10b318d4210b2e43149438f59643086796015321c7951530438c430c941cd90c514c2cd65d0c32e3994430cb2d540ca308f99250cc78c43144329e59430042af65508428f59353486f1600c410d394c320823c6355021ba580510cae661cc921c7152324cb6b32d4131e3184430cb375414530e310c32c423e64951328f59353c863f6454d20cb550320836752145309b58b535072d54cc820cb54b401033843d41318f98e540423d64d4e209b988540836452145309e580540c7685214131cdd53514c23e64d4f10e310c320c33b541413197d954310f2c4394840cb150324c78d4310c32e3180430ca3d64d4d20ce90f504c63e64d4e10cbd50324c31c5310d218f19153882ae6290d42cb552520427960d4f21e310c324436732145309b98b53c42746154d20d9145214832c54cc931cb553210876452d4530d9d4b514c38d6010c32a718d425066e62951309758c520425e63d48109758f54882e66115032c754c438866d62953308f993520425e63d50108f990528433643d45309e980530866c6254c418fd91538826f6254d21ab5884310a3e64d4c10cb90c524c63c6454f20c754c43882cf63508328f191538871f6414d428f590528434c530c910cb952528c26d6295130ae5805110f8e6010c328f990504866c6254d10c754c43d0a6d6215031cb149425071e5310f41b9584500cb384314131cb90e528c31d5390c10cb90e5210677654c4319ed95100432e540c810dad4b504c72e54cc810e310c32cc76432145308f593538874f6294c10c795253042ad6214443b398f540cb2d54cca30e310c32d032c43548108f993530872f54cc9319b58a5090ecd63908329dd9541106f161840109bd89544ca7b6055121ab58b4390e3d6590c209dd85544c26c6550921e310c329032f54d4930d90cb514c26f62551319b18d52102f1610c010cb10f524c66e62942439e980540c66c6254c40cb551200826e62145408f59251cc36732d45309d58753c82ba6014443c794e4390a9c63509409b997324866d65cc810cbd50324c72f54149308f992544c26e62d5230d554f310426e62d4e109bd89544c32c54509208f99052442cc6250c43ab18d4210aea60150328f99252c
  | 3 => 0x9044010181700425001480341500004014000800000400018050383208c01004650001f00001014161c06e00a0a000160040e66c013ec0602c0004a670042e0000300c0300164180005bc1b89c0d000002381416c0a01c14000ef1a848024ba1b54c0146c3049706d6c0124d038000040002c022cc180c40103c050480206806000050000b0041d0c83e0e0160980b2d000074030300511c07002ac8b801000090000504469880f0004730b8150205b0003e004130c8067740400c461780001c14004003000100403234000a809098840340452800028002c0000280c0040502cc5048120300620481000003844d00c440cc4102c082f4260000007c0648944010260fc0034c02074110004f0540f014350011d0140000c62000b30880e1780002c03018470d80406001004010000c0080005813014389c84d0300255c280100046c0302401058060005e0500a000020105b8f593538432c540c9309b58b53443e25244010ced53504c72d5448421a318d4210a6f65cc841cb153324c3b24344010f4cc7300432c4394a31d314c32506ce6410c32e310c321026c6354841cb10f524c34e53cca21cb10c524c32e4354a3197d8d524426d62d4d4097d95310c63d6414810cb552528c31d6510c32cbd4a5290e756115030ae982435025f63551209bd89530832e43548419b188534836b50943329b98a54cc32e54cc8208f596540871d5454c10e310c320872e4354a30e310c32d072d54cca329b98b535038c43d0832cbd50524c66f650c8409b594321029c644c8329bd94320432d540c821e310c321066e62946438f592510c63e64940309798c530438e6410c3297d8d544431e5390e40cb90f5250e3e64d4f20e3950430cb2d54cc8218f98c544c26f6254e41d3d4c324431f5310d20c714e435078c430c9209d584540cb2f65508429bd8953c423d6494832ab992320ca6f6254c10cb151424865d63d4810cb950328c72e5454a30cb953328ca6e6295131ad986435072e54cca319b18953042796015032d3d4c32502f0614c0309718d524423e6414c21ab98e430ca6c6254e40cbd5042ccb8c430c9319b98b53506b56114043e310c32c876b5214131e310d510ca3e64d4d219b988520423f6590c21cb94c430ca6c6255131c794c431034e53548109b189539066c6255130c794c4310a3e
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xb8000184000a0060200181037e1c2840450e030a0000006144000000018043008014a8581000008a2600482005018007831906254c10c1aca328861960c5418d42c8730a8ac02886543dd4430c810d0887308a01950c73550320830631886a908183d94430c810d1087300a21950c7454c3204330b0aa028065c210c32d4131b0ae23288619704430c8514c287ba88619043071cd6414910898e6b10a8885297010d5210312aa2c219043831506350b20b14e03088619561750c9100430631886a9021435d44310832a4ae22a28419629525805210f14aa2c0190418a5895014043d0ac2308861970843540500cb062a0c6a1241895895114443a18e4a98860850d7510c3204286390a621a41495c44354841c1eea31a842162564544510cb44b00c0218658318c5250940b12e0308861950f7510c32082873a6a619221a110d6114032a62ea21a2008704430cb514c34831886880218a5915014032c4aa4b08a421e0c6314942507842186428263439cb5310d10a18e6a12a2217115454d100428639aa8190438a5516015032c18c729a842160c6418a53043603186488021619c46510c32c1eca31a84215257115142c8318a8ac028887439cf5495332c62c2a80a021e8843580510ca8639a84a8085831506350921a18e6aa06408741535491004307b288619081e010c3244010c4aa8b08a81952970151420cb0629cc521a85c110d5114432a52e02a28590d8571180430cac3388c0218658318c4354841c1aca218640858970194430cac5380ca2186583d94430c841
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x4052000db00b018510c3244010e00435855014032e00435456014432c08635c04354840c81715806010c32a0883551600c820c09655c06510c32a0483551610c821c05655c46510c32c81615c06110c32a05811506350b20d017510c3244010a09801506350b21c04635c44354841
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 779
  | 4 => 754
  | 3 => 85
  | 2 => 14
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
  | 6 => 2*((h/35+packedAt s5K6 (704+(h % 35)*6) 6) % 44)
  | 5 => 2*((h/287+packedAt s5K5 (21033+(h % 287)*10) 10) % 779)
  | 4 => 2*((h/272+packedAt s5K4 (28652+(h % 272)*10) 10) % 754)
  | 3 => 2*((h/56+packedAt s5K3 (4165+(h % 56)*7) 7) % 85)
  | 2 => 2*((h/11+packedAt s5K2 (840+(h % 11)*4) 4) % 14)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7fffff03ffffff81f83e1ffffc3ffffa07f1ff
  | 1 => 0x81fffffc0ffffffe003fe1ffffc3fffc38fe3f
  | 2 => 0x1e03ffff01fc1ffffc001f07ffc7c07c0cfcc
  | 3 => 0xfe003fffffe001fffffffe007fff8007ff0ff0
  | 4 => 0xffffc000000001ffffffffff80000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4229118824490805a0a12549424a5520350d5
  | 1 => 0x2845222064892116041520a92a414aa418a62a
  | 2 => 0x5489b44921d233aaae41113c4ea87036c0cb4c
  | 3 => 0x181608924903844d30a64400711200c16d0db0
  | 4 => 0x611830e38e1c39f1c73999ce02206307b6f000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfe88e888fe88e888fe88e888fe88e888fe88e888fe88e888fe88e888fe88e888fe88e888fe88e888fe88e888fe88e888fe88e888fe88e888fe88e888fe88e888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40203
namespace PEqualNP.Outside.L_meta_40203
open PEqualNP.Outside.L_meta_40203.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x140046401ba4861c724e0080d5641034bc028704400ff84007ff4100ff10001fd20027fd4001fe42007fc8009ff52007f8c809fd52027f14805fe21027fd4409fd5000ff90007ff40007f4c807fc43007fcc001fc32027fd5007fc42007f90c07ff42007f50405ff10027f55007ff43027f54401fd31007f50807fe5400ff0c001ff21017f8c401fd30006f10c01ff3200ff8c001fd43017f14405fe41017f10403fc2001ff15009ff5300ff94001be43027f94809fc5300ff04005fe51027f94c01fd40007f44001fd21007fcc403fc50017f08403fe20017f0c409fd53
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x966200ef10f2003ff8c01900bf44150401ffb0a642cff1513203ffec3210fbff5290c0ffe32e4219ff9952117ffca3190bbfe408c8497fb2a8203bf1913100ffa8198066fd65484057e30a8602ff905410aff842a0093fd655045ffe20c6422ffd4f3100ffc419805bff5350001ffb028405bfd9510197fcc19900f3e6510c0fff996423bef8c04301ffa86a001ffc2048401ff1928203bf9932100ffaa08804bfc64cc403fe2024001ff04120097f8879880fff4290c497eb2a8200ff58d1001fb886a1807ec20c80097f32e6202ff50721007fac898873fc53c846fffb2a8403ef10d4001ff886a000bff51cc40fff2124002ff0873118ffaa7190a7ff50cc825ff98e6012ff10e4300778c89801eff65c8025fe3066202bf1863202ef8ca88003fe624401dfe18a6007ff9823209ffe8398003ff324c80fff3264201ff841101fffc40a1887ff42cc43dffa126203ff55142007f8c49881ffe52cc825fe1806433ffc4332007fcc6a106bfc50c8401df21a402dff14d320b5fecaa0057fe215007ddfa948603af9923215ffc8299002ff6048407df3288612ff90f311df7c402180bfd5144001fea126000ff98d41015fcc3210c3fc548c85b7eb1c6403ffd0543007da849002bfe53480017fb266002ff54521087fea898003ff644800fffa106419ff54121007fe64a080efe648c805ff8828243ef9864303ffec31903ffc424c00fee990643fff0414307ff8c89803bfe514c003ff2026002bf9854001df8c8908cbfc50cc825ff21e6001ff04330077f8c298003fd6050c25fe29e6405ff1951003ffac790007ff40c801dfe20a6001ff10330087faa698003fe434803fff32a6207ff4cb2103ffec721017fd6544003ff2822000efd913003ff8649003ffe644c00fffa906412ef10f3103ffaa59001ffc52c8001ffb126009ff9512003ffec99001fdf320c801763126203fbd094203ffcc01908ffc5050449ffa828201ffd0140007fec290093fc535040fff3086400ffd8131024fccb9800bfe21cc407fda028009ffd0d2000ffe4088012fc654c001ffb226007ffd8f20007f8c4a190ffe6190c0ff62906408ff8c52015ffe20990fbbf5190c037e3064201bf1824303dfcc41901ffe52c84017fb02843bef0404303ff8421900fbf4290c057e30c8401ff8c11003ffc659090fbc2190c01fe98a4001f78c1300fffea498803ff324c001feb266005fd54510157f8a099072fd65c840fffa94843effd464307ff8a89801efe62cc087fe10c8600ff9894003f7e85210fbbf5390c51ffa886411ff8c7300b7f8a4a004bbe43cc03fffa9a6217ff94121007fa64a0803fc6350057ff30a6400bf58032017fc209084bfe53cc0097f32e6024ff9494120ffccaa185bfd525003dff3226207ff1832100ffa808802bff5448005fe28a8243ef88643
  | 1 => 0xfff42500097f32a2001bf9814200df8c09080bfc514c40ffe216420aff545200077c871900bfe51c8425ffb2e6000bf58730007fac898002fd60cc829fea8e6007ff98642005fec89800bfc41c8437fe2a64202bf98530057faca90006fe60cc40ffea164207ff99632005fec4980efbc2010c03ffa022012ff182430177c82a0803fe63480017eb222000bfd85320177882a0806fe608c801dea128201bf18142087fca698003fe6348453ffaa66441ff54143007fec298007fc104c001feb128605ff1491000ff8809800bfc3150465ff2066436ffc41421cff8a32101ffe52908097e32a4030ff9523219ffca399003ec624c425fe316621cff54f210fffaa89884bff6290c7dffa9c8605ff549100b7f8caa0007fe5048007fe2a28202fd08521005fac8190cffc41cc80f7fb1e4212ffd8b30007fec2a180fff5450407feaa4862dff5953200ffc209000afc610c805ff28a8200ff18940007fc649880ffc425040fffb1e4207fec812003ffea590003fc324c003ff902403eef5524303ff8c390073ff50c8407ff2028217ff9812101f7ac021806fc605046ffe29a8407ff5863203ffc85190a3ef520c853fea9e6418ffd0121017f882a0802fd610c8017fb0a8012efd94431aff8a0a1002ff6250005fe90a201fbf5953115ff8629905bfd655007bdea808600fb0c920025f8cb98807fe3048051feaa0643fff98143007fac199093fd535041fff2a26007ff149210077c86980dfff505087d7eb2c8607ffd8032007dc8490067fd52484057fb228234ff1533215ff88299007dc304c00ffe294642dff99532017b86298803fe434c047fe3028201bf9833217ffc8319007fc30440057fb0a4207ff1093216ffea89901ffd600c883fea8a862fffc423206fdaa590003fd6250001feb028201ff50120005fec99881fff42c8005ff8864216ffd494003ffa851900afe61cc80fffb08642aff9013200ffca198003ff6250c57ff28a6407ff08720007de649903fff434c00ffe214640dffd47200977ec5218efbe5010c01fea12643def54443017fc8390807fe30cc003ff0866000ffcc5200977ec4218bffc318c807feaa48408ff185201fffca0a18037d65cc019fe21e4000ff50f201fffc20a1803fd314c003ff1024000ff50f31077fc6298007fc2044067ff20e6401fe8c3302177cc12181efc65c8403ff9864000ff98d10007fec69081fec210c80ffe10c6407ff8872003ffca4a1043fd654c007dfa128007ff5972016ffea4990b7fd534c8037fb02203fff8c1431b7f8a2a1003fe424c02ffe1824241ff1954304ffe829000ebc644c42dffa8a8031ffd523201fde8521037ff53c8001f690e4007ff192320a7facb980faff6590c77df08086009fd951003ffecb1900efe640c80fff3286402ff1472103df8c819012fe65cc845ffa
  | 2 => 0x3201ff880a080eff6350c0fffb2e4007ef10942097f8a619057fc5150005fe082822eff8c23203ffc6419007fc3048001df21e421fff59531015fac398842fd654c0097e32c8607ff19642005fec290003ff6350459ffa0a6422ff94b310dffca990807fe504c0017eb0c641cff94f21017fc639081ffc4250821fea8a6002ff90531015fec69884bbf6590c01ff21e4212ef19443187b8871904bbc5390c0ffe31e4007ff0cb2101ffc8321007ff3044087df8848600ff4cb310a7faa59800ffc4150805ffa8a2000ff8c94003ffac390007ff40cc087ff8848602f78c731097fec32180bfc51cc40f7fb228407bfd9642097fecb9884bfe53cc825ffb2c8606ffd09100b7fecaa001ffe208c837ffa1e4216ef551400cffea49089bff100c829fe2966035ff98142217f8a12184bbc6010c59fe3226403ffd0143157f8209904bfe43cc803ff0826007ffcc83206ffaa99001ffe640c805fe10a2007ff19032157f880990d7fc6050831ff322422dbf595321a7fe879909bfc510c801feb224204bf9972102ffea688003bc644c807ff21a8242ef1424320ff8a4a1807fd30c8069ff2a66407ff90b21127fca6a089bee210c883fea9286009fd952000ff040900fbff5090c017e31a8207bf98b31017f8639081ffc42cc801ff9926200ff50d1001dfcc999023fe6148001fe1928207ff90b3200ffc6098007fc204804bfe2806412ff14e4301ffa84a08f7bc5210c07ff2128203ff55140017fe209880ffc5450831ffa124200ff8cb3100778c89880bff5148407ff2a28201ff5013018ffca719003fe438c87bdea908607ff99721017bc6298803bc4344073ff8848402bf98f31147fea019007fc30cc03bfe2826219ff195210fffea09880afe614c80fff32c8400ff90d32007fa439807bfc644c40ffe3086401fb8812013fbe861900bfe2144001fe9926202ff8c5410077c869902aff654800dfe21a2002ff08521177f8811900bfd414c487de28c8629bf5973201df8c89800bfe2148401fea1a4203f7d0e43017b86398803fd42cc83ffe29a6203af1913016ffca69904bbf6090c093e32a401cffd5321005fec890802fd6190c33ffa9a4238ff1424203ffa641901eff658c875fe29c8400bf589101fff860a181efc648c885ff3048601ff88130097fec398006ff6450007ff20a8404bf9953217ffc631904bff6090c03fea82403fff0814301dfac9210d3fe64cc8537f3186418ff10d21167fca899003fc63480057e30a6000bf5933100778869087ffe524c425de1808607ff18642007fe629808bfd54cc403fe1066000ff18d101f7fca521803dc635080fff290640fffd05300d7fc819084bbc6090c0fff2126400ff18d4121ff8a321807fd50cc0057f30a8600afd91300cdfeca908affe314c8077f3226003bf1912003df8cb2100
  | 3 => 0xfb124001ffcc120197fca19904bfc3190c457eb2e6201fe0c1300a7fea598003ff325000ffe1046426ff9443203ff842900cbfe10cc815ff32a4007ffccb2014dfecb99107ff5250c077f3222043ef94643007fac321803fd434800ffea106442ef9024301ff88321847fe61cc051ffaa06402bf18520137f8821900fff5490c01feb224023ff9414100ffe21900dffe5350833feaa2422bff18532007da429008ffe6050473ff28c842eff0423206ff8a79001ffc420c807ff2048600bf18d2121ffca32180bfe1050405fe0864200ffc85400a7fea398097fe400c80fff1064203ffd524201ffe86a100ffe435080f7fb206400bfd9120007788690002fd64c80057fb0a8200ff485301ef7ea42184bbc6110c01fea0e4000ffd8d101b7f8c2a10b7fd514c87ddea9c8623ff8c14100ff8609800bfe41cc407ff2048401ff143200fffea89880ffe54508017eb226031ff54232167fcc89900aff614c411ff10a4001bf9813109ffe8598027fc4348003ff8828000bf18d421f7faa721907ff5150c15fea924007ff10a420f7f88498807ec2048003ffa864007ef90942147faa6190ebfd539086ffea9a842aff941320077a82a00abfe104c86dff18a8427ff15032017f88298802ff6250c05ffa0e4202bf9854208ff84398003fd424c401fea1e6004bf1954201f78a9218dfff5150865ff1066440ff0854318ffaa319002ff614c06dfe18a8400ff58d2000ff8409801ffe4250807fea0a803defd44430977ec22180ff74150455ff1826414ffd4f30017fe6390807fc50500075e3226400bfd8d41017d8429080ffc5490c25fe21e6003ff90142007da641902ffc51c8069ffa0e6429ff99732015f8c2a101ffd32c8007ff20c861fff54d311f57cc62181ffd640c835fe2064201ffd414014ffacb9900efc644c825ffb266200ffd891011ffc40a084bbc43cc0077e3222000ff5853208ffc43980f3bc2110c07fe21a8600ff4c94003ffca59000bfd41cc47bdfa988607ff584320077ec89904bfc31cc825ff996621eff15131097fecb9900fbc4350c01fe3122000bf5933021f7c83218fbbd6590c0ffe2924000ff98d40025fccaa000efc64cc003ffa024002ffd0541207fc42a180fff5450805fe98e4200ffd91320affcc2a0003ff6444001feb166030ffd0632177fca119003be435045dff084642aff8813203df8c4a180ffc5490801feb0a6001ff54130007fcc49880bf4314c47dfeb2c8633ff8c732017dc429084bfc53cc403fe9022032ff04332107f8a1988cbfc40cc867ff10e6404bf99543137fc8219012fe658c801ce21c6441ffd9543007fec0a1803ff61500077fb228600ff4852003ffc6590017ff5244007ffa1a8207bf98a321b7fca2a10b3ff434c879df1088616ff94940117fccb9888bff50cc407deb108607fb8c8
  | 4 => 0x2ff624c403ff206403eef94a4311ff860a081ffc20c8417ff28e4003ff551431fff8c0a1802fd6390801fea1a600eff0853000ffe6098077fc404c46f7eb2a8407ff50b20017f820988dffe655082bfe18a8010ffd4d30007f8c49800fff4390c297fb2e6003ef5844301dfcc99000bfd4148455fe1826403ff90e42007fa648804bbf6190c71fe0848417ff141210a7baa798007be4050007ffaa2803aff94e4200778869804bfe5390c25ff2986435ff881420977c8619067fc5348433feb2a4203ff109400077a84a001ffd658c807dfa0a8400bf58d1006ffaa79001ffc20cc80f7e328641fff94d310cffea09080bf631cc4093e32a20009f5943202ffca48800ffd4390803ff2028003ef9524300dfcc0a190fbe3190c01df21a8412ff90c320b7faa6a000ffd4250025de32c8603ff1054001f7e872180afc614c801feb0a8002ff145101ef3aa62181fec4290807ffa128612ff1873013ffca81900ffe5490c1ffe21a602dff54132007ee6298873fd50c8447fe102820eff88530007fa649084bbe43cc8157eb2a4012ff196430077c8698883fe60cc44fffa18640cff1532001ff880a181ff721484097f32c8400bf98d2003ffec11900bfc31cc425fe32e6403ff10e42005fcc79001efe6290873fe18c8400ef90e4221ffc6321803fe32440077e3266400ff9093114ffaa199003ff60484097e32a8626ff8c43203ffac121003fe434c40ffe1026428bf59432017f86298812fe6590c75ffa848400bf18d2020ffea6a188bff54cc407ffa0a843eefd4243007fec6a100bfe51cc4097e32a2007ff9492103ffac1190dffc655080fff2106416ff14d4000dfcc0a081fee52c8001ffb128020ff9033102dfaca8800afe61c803dffa1a6207bf98910017f8a29080efe644c805fea8e420affd4920017f88398803fd42cc401feb26621aff94321005fac598803fc63508037fb0a2003ffd0e42097f8cb98893fd505040f7e3264000bf58331017fe219882bff5348061ffa1c6402ff8c531004facb9802ffe41c8001f79946418ff19121007fac498003fd644c86dff30a8435ff0414214ffaa399017fd5444021fea926039ff8c64200dfec09001fff6590815ffa8a4001ffd0130117faa79881ffe3248415f6a92401dff90131177f8611900bfe514c4097f32a8407ffd832100dfec698003fd6150c01ff3128600afd913203df8cb90003df63508017eb1a423eefd5243097fec19900fac4250805ff0864200b718d4201ff88521843fc524c025fe32e6012ef0c643097f8c99904bfc310c835ff1864200ef58643015f8c2a000ffc41908297eb2e6001ff4c11004ffe849000ffe4150007de2148600ff9893016ff8ca99002fd6090c017fb226402ff5454103ffe4390003ff6348043fe2a66232ff8c33220ffacaa180fec42508037
  | 5 => 0x4143217fc61218b7ff534c81bff29e4000bfd814103ffea51900bf621c84017eb1a4010ffd95301ef3ca62181ffc214c80fef994640cffd0f20097f8879901ffe60c8475fea8c8407ff0814203ff8c990803bd6090c01ee98e6000ff90f20005fac190907ff5050c017e31a8003ff10d41007fac121806ff605000ffe1964003ef10d41017eca28806fff40c840f7fb264019ffd9521087fcca9800ffe4350077de2808612ff0c33203ffc649000bfe215040f7fb286407ff5832112ffc601901eff65c84017fb128200ff4cb30067fca99004bff64cc001df21a8016ff995401c7fc212101ffe200c801fe1928018ff151211ef7ea02180bfe4144007efa1a8638ff94242107f88198802fd63c80017fb1a4216ff94d40127f8caa082ffe31c800f7fb1e4000b7d8d420077886990cffe61cc807df2a28000ff58d42097fec39901ffc52c840f7e3128200ff4c720005fac32100ffc405084fee2186400bf582421affc60a1077fe304c429ff2966007ff54a32025f8ca9900ffc4090885df1048600bf5823203ffc8590103fc6150c5bfea9264049f9943201ffca8a0047fc51cc0037f31e6003efd014101dfcc998907fe5250c07dfa0c8607ffd0a32007fcc598903fc5150c63ffa8c6402ff9052101ffe86a00c3fc438c871ff1848407ff54b2118ffea71910bfe2090c0ffe31c8402ffc85100a6fccb980d3ff40cc807ff2a48407ffd972115ffc4299087fe54cc459fe21a640aff55120097fca798803fe32cc02bff18a8001ff4c120007fa8719003fd315000fef1926400ffd9121005fac52180ffe4250007ffa0c8627ffd04321ef7ca42180bfb1044001ffb028207ff14b320affca2a004bbc6290c057eb0e4212ff0cb3100dfcc1210037f6544079de2888637ff54542007fe64880abfc604c853fea966403ffd014100ffe2088043ff524c0097f32e4013ff99330007fcc598003fc324c4017fb0a8604bf99432007fec4a0812fc654c405ffa0a6207ff8824202ff8a688077fe204c485de084861aff0c321127fecaa081efe6290c07de2048614ff99730127f8a4a08c3ff408c885fe0848600bf98e42097f8c521803ff32484037f3164000afd913103ffec81900ffc5450007de20c8624ff5494100778871900bff214844bfe2006402ff5051010ffe8798897fc100c8017fb226207ff8863205ff8639000afe6148007ffa0c8401ff14110005fcc688002ff635000ff790e4010ffd45300977ca721803fc625041fffa126001ffd411004ffcc890003fd604c80fdeb246402ff8c73102ffeca8804bfc62cc005ff98a6235ff941420effcc09881ffd648c80ffe2926414ff55330167fe8099037ff54c800ffe2164000ff90b3105ff883900d7fe1050805ff8824200fbccb20007f66098012fc65cc887ff10c861eff95131005fac899
  | 6 => 0xffe32e401fbfd953100ffc6190007fa20c8027fe2a66002bf9873003ffe4290063fe54484037f3006442ef0824301dfac92180ffc5450c55ff3026431ff552320c7fe8690807fe105000fff3048404bf9952100ffc4190003ff31c8071fe1848402bf98b21007fa8488067fd5348403fea064040ff98543007fac39800afe6190c01feb1a820aff14d20147faa2190fbfd5190c0ffe1006400bf59321217f84121803fd64cc83bfe1826200bf5912103ffea59080bfd3148401ff1926003ff1024309778a621843fc654c005fea8e6205ff54d1003ff8cb19097fe100c80ffe2928401bf1833203ffc849080bfe21c8403ff1828000ff50520017f82198802ef624c46ffea928404bf1952109778c421806fc604c82bfe30a8003bfd894203fdc859000fbf42504077e3266203ffd014203ff8439900ffe4150c017fb1a4003efd01420077ec898803fd604c401feb166201ffc412008ffc8398006fe604c849ffa928200ffcc920007fec89880fbf4150053ffa966407bf18930017f8628801ffd64c8403fc2028001bfd8130005fec09881ffe63c84017eb224007ff59320017fc2198877fc204c47ddea848601ff9011003ffcc319033ff41c8005fe20a2012ff14f30017f8629080bff51c847dfea848607ffd0b21167fe8499017ff544400ffe1048403cf5944314fd8a599003fd624400dfe2122003f710e43025f8caa080bfe5144001ffb126201ff88140015f8c321803fd6250483fe29a8601ff14120087faa8980a3fd500c803ffa824000e710c3200df8c121036fd65c80037e3026229ffd4732007fac498883fe20cc42ffe3024204bf99520007fe43980fbfe6590c41ff1866203af98e4301f3cc62180fff4150007df3088642ef8c243007fa84908dffd5050825de21e641cffd4f211a7fe8599003fd43c84057fb124207ff1943203ffac72100bfc4148403fe2064040ffc414300ff8219007ffd504c47ddea8c8600ff4c920007fa869900fbd6510c07ffa128201ffc43302177c2121843dd534c053ffa9e643eef99643097f8c199003fd6350001ff98a8007ff1092116ffeca99067ff5448425ff9966041bfd954302ffcca8800bff51504757eb2c8400ff58121007fac888003ff604c82fff202423aff54242007788790802bd648c807fea1a8200fb50b2000f7880a0003fd43cc845feb2e6207ff98e42017faa2988b7ff514c805ff28a4200bf58b30005fac919006fe60c8485df2848607ff594320effca098802ff6050c01fea0e6007ffd92320077c879006ffc43c8403fe0828002ff0854100ff880a001bfc5444029ef29e6007ff9492000dfcc090802fe6348403fe2866042ff84243047f8a29001efc64c8485ff284863cefc404312ffca01900bff41cc4017e31a2001ffd433018dfacb190dffd6550849ffa9a823fff1
  | 7 => 0xa1807fc3050025fe2186407ff0864200ff8419001ffc4248001f79924007bf19632017fe6288023fc3148001fea1a6200f7cc53003ffc42190bbfc508c801ffb0a841cff55321015fcc3190c7fc538c82fff1024212efd8043015f8c39900ffc4250c07feaa28230f7d0e3203ff8c31900efe6448005ffa0a4207ff9493200ffaa190007f81044043ff326623cef8c44318ffea119007fc4044001de21a6201ff90120047f88290003fd6148007de21c842bff14532005fec999007ee20c8001ff90a6007bf18f2100ff820880f3be5110c01fea124000ff18d2100ff840a0023fe514806f7fb2a8407ef9923214fdea599003ff6350043fe2166207ffd82421aff860a107bfc434c40ffeb1e4202ff8853103ffacb2101bfc64440097e32a801fff19531005fec6880cfec21cc8837eb2a861dff18131056f8ca9001fff64c840fff10c8400ff5873203ffcc990003be43440057f3086401bf9824303ffc6499007ff104c005ff98a4212ff0c331085feca98002ff6150841fe1066207ff992320977c879880afc61cc025de1848609ff19120077fcc298002fd61cc82ffe2024200ff50530057faa6900bffc518c825fe18e6011ff9473001ffe812180bfe104c40fff294643eef14a4301dfcc890812fe654c001feb0a8412ff187321f7faa52180bec21c840bff29a2007bf1893113ffe8019027fc54480017fb026400ff9894103ffeca190fbbd5290c05fe0824200ff50b3000ff8a09801ffc520c807ffa128400fbd89311f7f8a52181f7d650c881fe18a8600ef58a43087f8a698053ff54cc027fe2166012ffd933200ffea098007fd5050025ffb06620aff19520007f8648801ffd520c80fffb0e4010f794d3006ffaa39001ffe63c800fbf3286400ff90d1000ffc81980dfff5350805ff18a4207ff0854203df8c4a0002ff62440017eb226220ff9433101ffea8a180ffc4150c23fe20e6012ef0c44316ffaa89907ffd524c401feb028407bfd92320f7fe809880bfd3144005f710e4200f7cc730037fca88800ffe4050c81ff28a8616bf595400077cc52180fff409080dffa1a2007ff18242015f8c390053fd53cc003fa0822003ff50d4203ff8a521002fd64cc8097e32e6001ff94320025fcca9887ffc524c40f7e3122000ff4c930005fec88800bfe3144003ff0864000ff98a4300ffca0a0067fe534842dfea8a800afb949200077c8690806fd60c80097f32a8207ff5864203ffaa521002fe63c8401ee98a6007ff1823203ffcc3900f7bd5310c07de21a8412ff0c243007fac52181ffc64c8011ff20a4000ff9091020ffaa6a1807de30cc05b7fb2a6403bf99131117faa198803fe4348401feb066202ff0872119fdc4399043fe524c00ffe1924203bf98e4301f7cc021806fc60cc407fe21a8436ff8854203fd8659003bfc514c00
  | 8 => 0x19c1180019a0700203703c1ac1e80101a000088020300280001a00c0b80400b006000010041ee004020070521301d02411c0000180411c3e0098140001dc001000080481b00314a4a8240030480040282103a018000d216a0000100300807007a06060038030400000b4080f9088068000020020004000101200cd60020000a00000a5980100e82328e3580281000614c100030da080050000005500700600c118000012e208c0903807a3dc050790580900b01601c074f600b0082b86b00101c2f06d8260002443880106e2451a0000000141d05e0020980081a00c04c00000040010008003b20681400005c0000007d0be1c0010030820245d82a0100001888a1160100280400e3264e8080120301a034012000073c400a0002f80202e03c0104e01203c008000100003b0810001980000200803800800010000020a00fe0f85f0629740000888700c0040d0020220300282603a030559bf0080a402806032018968000120100002c01a03c0102305c014118000140540085c03a06c0806b04836c00904142084008000141a83400008a000018003300dc0f0000140100502401c0083300309821c018651000180687211a199bd000000068008020020540000403e02814000002288010000c20040e8001100201303301803c000006300bc250011d801c000040000201381a0142843b80700a00815a7102400c020070060080e0380122f40001400200c11090002000000400080000001c00e000020100040540201b0114f00180300006403000034000000040120300600e0780240d3b30460002fa710660101000009000000008002000000013200d01f0000044fc0380e0840600400205a0001781c0640ac38d000340bc02004030078038050081f80000000e050078070b80000e80500202d8f00d03e0023c0ce05600c0507c00201c0800000004815003000018111620000a00000103400401000040b880005d05400c1d8000000481a37b0100700580201e0000680819ff8a39904bfc32cc003ee1866000ef90d43005fac39004bff62cc45bffa826406ff9911009778c321807fe2044025df3188607ff4872014ffaa99908aff65cc4037e3046413ffd0f3020ffca6a1893fe6550427ff2a66001ff0c32001dfcc99805ffe3048451ffa986400dfd952001ffc86a188bfd52cc405ffa8a6212ef10c320fffeca98803fd430c875ffa8c8400ff90b3001ffe86a1803fd63484037e3028612ff186430977ca62180ffe5450c43ffa066207ffcca32097f8c99801efc63c800fffa148400fbc852001f7e8121803fd31cc00ffeb2e420eff90530117f8a59880bfc214c4037eb066002ffd051003ffccb90006fc600c875ffa9c8403ef988431bffea4a1002ff6350803fb0822007bfd932103ff8c790802fd63c8415ffb2a4000ff48540207fc62
  | 9 => 0x8000000282d800c740020141580004c00c400e209c05400000020030030740300a8008170040982380e04807d068144120000901b17a078000070000040600d00201410801002078000514ce0000e8280000000a00307a008000111ec0f40300000801001854024c684a000018010000680280280280d0500237c85d008
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe70591321cef64158642006dd7518d420067f655092012edd3018d2003eef73189311debc4018d400067c64d9520006bf645092101cfc7458632004fd75d8d410d6f710d85200557c7558d2007ebc54d9130006be70d9131006bc5359232014fe73593311dfb830191302977410d9510006de53d8d420c7b57110d21097b46158643004fd7650b3103ef77158720006bc7559232014ff7658643004ff74583322967e30d9510096bc4359331024fc7558a4326edd31d8d10096be7610d310eef71058730004fd75d8520097b443cc531094fc7498d1021dbe7610d31006dc43d8d100067e21597301e5be7390d2103cfc760c941004fd75d8d20006ef6298931006dc30d8d2100cfc7648520014fe7198e4200cfc70d8941096bc43d933001cfc7458f210aef661d854001cfc74d8931006ee53d89311f6be6590d3000dee7050b20007ac43c8520006be51d913221ebc21d9131005dc735092119fcc31d893103ebc3259232006ef6290931136ee610c92003e7c4259432094fc76cc9102af6c6548520006be535923201cfe7418d21006bf51d9130006df6518d42004fc764c5401b6f651d8542006bc651913001dbe740c94021ebf21d9131005fb7050d301fcfd7650d30096f731586430067f6598d10096f73158432096de5398e42096bc61586431f5be7558243004fd7559110005ef7250d2003cfc7690931006be611913221ebe6190d2001ebc6490d3221ebe615864303ebe42592320057d750c91001cfe7458232014fc7118d4200cfe705932101cff7659331014fc7258f2107ebc41d9130024fc755913103cfd74d8d42004bf7458d21006be65d9131006ef52d89431febf405933023fae7210f2003ebc425923200cfc7098f2149fcd534c832256dd3018d1023fae7210f210057f755852021fae2190f2101dbc74cc9401afb8705094000cfc70d8d21426bf4218d4000dec70cc920046f661d8520005fb704c930007b771509410979c3110e32004fd75d8930215be7310d1001ebe6490e3213edd4118d421e6be6210f21006bc64d8132007b764cc53119eef71d8931166ee4258a43007ae43909201869e74d8d42264ff764c73000efb63cc130004fd7558a4309ebc43d814323edc2118d420373e7510d102967c40d9510096bc4318d41095bc7358a43004ff7458730096be6390d210067d6550c32095bf7658243164fd7650932005bf71582431879d7010e3201cfe7418d1021ebe6190f200d5f7715891000dec709092003eec62cc94103eef2098f210b57c7558940004ff7558332024fe75d89404ef9d5110e3213edd7218d4203ebf4258642005bf744c72024fbb2090d2023edf2118d42004ff75d9120097ac6298a43097da70cc730004fd75d8530006dc53d8d4200cfe70d8520006ec42d893101cfc74d8131186bc5459232
  | 1 => 0xd32094fc7358243004fd71d8d40006bd5418d40214be7619130006dc50d8d4203eed7318931216bc6090f213e67d4059730096f43158732004fd755912024ebe7690f21004ff7259110004ff7458d21217ba4058243005ec72591104a79c5010c3200cfe7059121014fc71593300067f6558d20006be7059232006ef7258d2000cfe70d912100dbe7690d40216bc4058243006dc73591210067c6518d102967d30d9510006be43d8910005bf7458520006bf50d9132006bd52d9130004fd7558242216bf10d91300065d7518d420076f65c8520006be43586323dddd75cc730005bf755864303dee7250720005ed7190920005df73509200f6bf42586432967e10d95100ce7c65485201257e750c9410979c430c93124ebf73d913200cfc7058b31096bc4358032006af64d893100ddc704c730007e462cc531016e4614852013ede4118d42006bf53d91310067f43597300963c43594322967c20d95104e79c5110e32004fd7518d2113ebf4018d420debf40d8542024fc75d8d20006ee651893100cfc7058d2103f6d750c920096bf6010d3003ef82058032024fc75d891015eef2158b31016f461cc5200067c75589100973e4359730095bf7450c321dfae2010f200067c6558d1001cff7650920196ee76cc920024fe7558720186de74d8d42006f77159131006bf75d9131006bd70d9132006ed64d8931024fc75d8940006bf651913123f9c3210d20005bd74d8d21006f610d8532006be65d9130184df7359132095dc7350b30096be4358b30024fe75583311f6bc6590d4100cfc70d8d420975e7359730096be4358243005bf74cc94104ebc41d9120024fe7559121096bc4358730096bc7690d21097db31cc13000cfc7059321006bf73592323d5df754c7300bcfd7698910006df52d8d42096f8605824303feb60909201eebe6510e3200cfc764c930096bc6390d21006bc30d9131007ac62509410979e6510c32006df5318d423c4ff7359130216bd50d91301bd7e7518d42004fd75d853200dee76cc920096ec3258b3023e9f6510e32024fe75d8d4003eee760c920005bf744c730007cc724c530006be75d9131006bd42d8141014fc71d894300cfe76d813201faf7250941015be7690d41005bf7458d201bd7c75581420067f7558d2004dbc7458520094bc73d9130094fc7598f20004fd75d8941006ec53d893103e7e42594320067d654cb300067c6598d20094ff7018d4007ebf4258243014fc7158e42024fe755832121ebd21d9131096be435833103ded76cca32006ac43d8931024fc75d9120096f43158432096bc6390d40216bf6090d1003efb7058232004ff705913100dfa700c9100079f64cc530004ff7058a43006be50d913100cfc70d91100079c744c7302977810d9510216bd10d91300dfac42d8542007b864cc13000cf
  | 2 => 0x4fd7559132004fd75d81430967c4359432145ee754c83207ebc42d9130096fb3058331004fd7598d21006dc6518d42024fc75d8d42014fd70d911003cfd73d913200df87050920004fd72d91311cebd41d912103e7d205943200cfd72d91201eebc6510d301a4ff7259132006bf6418930094fe73d8142024fe75d852000cfc764c530006ee60d8931005ec7348520015be715094112cfe76cc930005ef72585301b6f661d854200cfc70d8d41006de51d8d4200cfe70d911007dbe748c930004fd7690b3000dec7650920006ec43d8931006ee5018931094fc73d913003eec7118931006ef6298943094fc7690d101acfd7650920006bc5059232445ef7259121006ec50d89310079f6310d21004ff7059232005bf74cc540004ff7058642006ec42d8910006de31d8d42094fe7690b3103cfe72d8d401b4fd7650921004fd7558b31014fe71d933023d9d7610e32096be4358332005ec724c7304af9e5110c3201eee6450b20006be43d8142005bd7098a430067f65d8520096dc7118d42006ec301893107dbc744c9300079f735094101cfc7458331004fd7018d42006dc1018d4223f9f5210c32006bf648c93119eef62cc9312dfae43cc92001cfc74d893003e7e7259432004ff75d9130005dc7358540006bf6450d3003ebf3259232166bf41d91321f6bc6590d20096bd7690e3203cfc7259330217b61090d10014fd72d8121006bf6390d100967d7598d1003cfc7258d10024fc75d8941004fc7648530005bd7598a43024fe75d8143436bf6510d21004fd755833203cfe76d894101dbe74c8540005ef724c52003fac4250932005f77150d31096be435864346ebd74d8d41166bc644c93119dee761893100cfc7359330186bc73592320076f654852001ebe6290e42006bc645893101fb76190d41146ec650c92001cfd7118d411f6be6590e42005ec7258d4103cff7259320005f77158d2000dec7048520004fd70d8d4103ebd205923200dec700c92024fae7290e4200cfd7418d4013cff7650f320057d7598d200067f65d9110096dc630c91003ebf525923223ede7218d4201ebc6490d3001cfc74587320979c438cb31166bc4359132006ef52d8931216bd70d9130006dd6318d42004fd70d8542024fc7558332006bf72d913215ded7298d2103eec2198f211afaf405092023e9e6398a430067f7558d100debc435932103ee42158432446ef21d8941005f7714c931005df735093113ebf4059032024fc7558730005df7359120004fd7558643094ff7598f210557e7598d2019eec2158732006ec7258d10004fe7650d10176dd30d8d20096bc7690d4211cfd74d9110006bf71592320979c7210e32004ff75d8543096bf6310d3233cff725912021ebc71d9131006bf640c930006bc601913124ebc6290d30007ae4350b201f6be659
  | 3 => 0xd71d89300979c3190d310067d715943201dbc744c540024fe7559131096bc64593314bedf74d8d42216be6090f21096be6390f20096f7315873203eec628c93121ebc6190d404bddf7350e32136ec101893101cfe74d852032fae5210d201dfac2010d20006bf65d9132206bf415933103eec7418931006bf6450b3101fbb6090d402967f10d951003eee751893101cfe7458632006be74d8d2024ebf6590e32096f8305824321fae2190d21024fc75d893001eac645092000cdd76cc73007ebe7619130024fe7558a4319eee61cc92000cfd71d891001cfc7458332004fe769091003cfe72d8540094fc7518d4101cfc74d8d210067f6598d2003ebf4298e4200cfe76cc920174ff764cb30214ff745913010dbe7498b313467f20d952020e7e6550f30006be20d9132156df3058f20006be40d913100df8704c930006df50d8d42006ed65d893103cfd71d9121015bc715094109ebf41d9330035bc744c910096f97098d20096bc6258a43004fd768c941187cf42d8d42006be31592320067c7559110096fb305824303ebe6250941014fe71d913001dbc74cc941006ec21d8930004df735912119eee51d89310047d7518d21006bc65d9131014fe7118d42006be53d913001ebc6490e32206f631d854319eee31d8931024fe7518d100cd7e7518d21006be515923203feb60cc920004ff75d8941004ff764c520094fc75d9330004fd74d893001cfc7458730005f9700c91023ede6398a430befa60d8121004fd72d9330004fd74d8121006bc4358910006bf649093003fe4214c921006bd62582430065f4359432136ee411893100cfe7018d100067e6558b3019eee61ccb2003ede7398e420075e7518d42024fc755933042ebc43d8d40006bd70592320079c6310d10006be43582320067d73d9510004fc7650930005bf72505400057f755814124ebf6418943216be6090e42035be748c91000dbe705054003e7f72594320067f71d9520004fd73d8520097b843cc1301e7b67110d10004ff705913229e7c41d9510097d661cc730005ee734852015ef651d85320969c6390d420067c6518910006bd5458243097b83010d3032f9e5310d20097d970cc7301debc6010d3203ef421586320247f7659730094fe7318d101febd40593301debf63191301eebc6510d31006df7358d100971e6510c320979e7210c32004fd755872003ebc725923201cfe74584320067f655052013ede4018d42216be6058243006ef531893101dbe7448540097af3298a43004fd76cc720004ff75593200eef860581312967d10d951001ebe64509100979e5310d31024fe75d8d21006ed621891003eec3258232024fe75d9132005dc7359120094fc7518d201e6bf6110d21016b46150540094fe7690b3003ef72158632096f83058331004fd74d8532196ef20d8930
  | 4 => 0x8e42014fc7159130004fd7418d2101cfe74d81211f6bc6590d21004fd7558331007ac6250940096fb3058332004ff72593310967c6159730004fd75d89313467c30d952023f9e2110e323467f30d952001cfe745873200cfc7018d42007d7614c530024fc755803213edc4018d4203eed7418931024fc755864300dee704872001ebe6450e32024fc755891000dec70c852001eec6450920094ff7690d20206f661d854324dbd7290e42094fc735872027cff745911035ded754872001cff7650e32095be7310d310979e7010c320067f65485200067f65d8910096f83058332096ef3258b30004ff7558242014fc71d9132105df714c53000cfc7298f2021fbb1090d10006dd5318d4203def740c920006dd53d8d2101cfc745832101ebc645093100cfe76d8121096bf6290d3201cfc7458032005bc735094019cff7258d21006f551d85423467c70d9520094fc7598d1003edf7358f21006bd72d91301e6be6110d320067f6550d101c4ff7459120096bc7690f21014fd74d814103ebd4258242004fd71d894003ebf7459232096de4318d42155ed7298d2000cfe70d8910094fe73d8540006ef50d89310979c3290d3219fe6215873200cfc73587301d67e6590b301a6bf425933223f9e6010e322dfaf7290d20006bf5059232005ec7350b2001cfe7498f210079c64cc53023edf2018d420f5f57198d41215be7310d20005bf7150940096dc3118d40004fd7558032006ef64d8931186df41d8d42007ac43d8931096be4359332004ff70593210067e74597300973e7510d31004fd7558e42014fc7298f21036bc42d9110006bd74d8d20006bf54d9131024fe75d8931004ff7650931094ff7518d4034e7c21d9520004ff7158232217ba2090f2000cfc70d85200979c7510c320079c6390d40236bf6510d1000cfc70d9332024fe7558f201f63c6590d2003dee73cc9200067d73d9520094fc73593200969c6310d1013edf4218d420067f72d951004f3e7510d204b79f5010c3224ebc6290d40004fd7598d1003efb2058232006be43d853034e7f21d9520005bf725824300cff765824304ebc4359120006bd6490f2003edc3258f211b6bf4159321006bf7458f201ddbe76d9130006ef620c910156fa30d813224ebc4258a43006dc63585420067f650c910007cc63cc9200067e31594321879d7510e32006bc53d91301466c650c92001dbe740c941006ed70d8931094fc7358a43006bc72d9131096ef3258a43024fe7518d40036bc43591100c6bc435912121ebc10d9131004ff7650d10004ff7359110005bf745893100cfe725932003cfc768c940006dc635814203cff76c8730096f970d933023ebc6510f21005ef7258d10006bd6258643096be6390e4200cfc70d912113f9f4118d42005ef7258d4103e7f325943200cfc7058f21004f
  | 5 => 0x13edf5418d42006ef5418931006be30d913121dbe7198a431e7b43119131216be6090d31096dc7518d42004fd70d91210057f75589400067f7259730004fd75592324ee9d6510e320047d7598d10006be6519130024fc7559232006bd6490d31096bf7610d10024fe7598f2107dbe749893001cfe76d9132005fb704c920004fe764c9103e67f2059730165bc745813201cfd71d8d4103ede3258f200967f6259730255de76cc530466bd6590d31006de20d8d4225edd3118d1021ebf51d9131024fc75d8532006bf71d9130004ff72583311879c438c94014eec65cc920036bd7610d1000cfc765092002d7c755891009dbe7498b30094fc7498d20094fc7518d42024fe75582431dfb81010d10024fe75d8d41004fd75586321f6be6590d1001f9f6390d43005dc73581410c6bc4358642216bc50d91301f67c6590d20024fc7559110004fd75d91210f6bf42d91310067d7459730006de30d8d21006f761c85300067e41d952023f9e2010c32094ff764c921164fd72d9132007cf63cc920004fd71d8132006de3018d4200cfc7258f20024fe7558432186bf4159232096dc4318d10006be72d9130024fc75590321dfb41010d10096bf6310d30006bc52d9131004fd7558f21004ff7158243024fc75d8520096bf7690d10336bf6590d200067c42d9510004fe76485300067f65d8d10006ef62cc910006bf64cc9300067f659091024faf2190f20006df6398d42097af6298a4300cfc70d8943095bf7658a43096ec3258a43006be31d91321257e7518d410f6bc40d91310067d6558730006ef628c930016ec614872021ebc4158643006ef6298910006bd53d913100dee709092001cfc74d8121006bc75d9130007af64d8931006be6519132094fe7398d210067d74d9510004fd7498d10005be7690d32094ff7518d2100cfe70d89412977610d95101a6bc43d894319eef41d893123f9e3210d32006df5118d42094fe73d911003eed70189310967c6259730006bf6490910136ec610c920216bd20d9130004ff755923223f9d7610e3203eef2059032004fd70d93310057d750c9310057d7598d1001ebc6450d32096be6310d1021ef6415864314eee65cc932047e46148520096df3118d2101cbe76d91320057d7598d40005bd740c94001ebf60509400979f7110c321afad4050920016f461c8540006bf52d9130006ef62581310073f6510d100067c655912040ebc43d8940004fd75d8542004ff7558732014fc715824223edc5218d420adf47158940004ff75d8d210969c6310d20226ed20d8910215bc7058a43024fc75d854321ebf6490d31024fe75d9332006bd51d9132006bc31d9132006bf64d8530006dd7018d42006ec6518931006ee40189310067d6550730014fe71d911024ebe6290d10004ef7258d1003ef77158432166bc435
  | 6 => 0xc6310d210967f645973021ebe10d9131006dc61d8d420967c305973015ef4615853204ebf415912001ebf605054001cfe7458b31006dd51d8d42096be43d9332014fe764c92100dbc76505400067c7159432006bc7458d200067d65487300067e7059432006ec401893100dee70c852000cfc71d8121004ff75d891003ebe2059232006bf70d913201cfe7458f21004fd75586424b79d5110c320247c755891003cfe76cc72003dec724c720006de65d8d423e67e70597300079c744c5301debc6010d21006be52d91310c6bc6459121006bc43d8931036bc43d911021ebc6190d20004fd76487301debf6010d20006be75d9130005bd7558243095be7390d3024ebf6490e3203ebc2059232094ff7598d10016dc614c530096f46158643165bc7458532004fc765053003cfc7218d20004fd7650f21217b82090d200967e7518d41006bc20d913104fac6450920024fc7558b3103def74509202dfac430c92023ede5218d42006be53d913234e7e32d952021fac2190d21004be7610d3200cfa76cc130154fd768cb30016de61cc73019ef62158732004ff705933203eee6218941004dc73591210067f74d9520096dc63cc92000cfe7018d41005dc735093023f9f6010e32006bd75d913013ebc640c930006ef325823221f9e31d913102d7c75591100057f7558142004fd72d8d40006ee20d89310fe7e654c730194fe760c930004ff75d8532006be31d9130006ee431893103dec7250d20006be51d9130005f5710c9410067c2159730006bd6158243096be4358432096dc4318d200979f7210c32006bc51d9132006bd54d9131006de1018d423467c10d95201debf6110d100bef86058121004fe765052019eee61cca3201cbe76d9130004ff7159120096bf7459330004ff7650910005cc7350920014ff76587300978c434c83200cfc76cc9200069f6310d20097ce534c8320067e6598b30217ae2090d20024fc75d81410067d65c873003cfe7650f210067d6550b30006ec70d89310079f6390d41175ee760c92023edc2018d4207ebe73d9130006de61d8d4232fad5210d20014fc735933103cfc7259331014fc715923201cbc7458f20004ff75d8121006bc61d9132104fd7098d100079d74d8d42006f771591201debe6210f20006de5018d42016be61505401e79e3110d3121fac2190f21004fd70d8d21006de60d8d42004fd7559032216fa40582430067c6558520006bd72d9131176ed72d8d2013edd5418d421e6be6110e32096ed72d93320063f6510d100979c7110e32094fe73d933003cfc760c940006ae43189314af8e2110c32024fc75d8943006bc7458d21014ff70d891000cfc7059331007ae434872003cec72591101b5f4715814200cfc70d853221fb64158643004ff75d9121096bf6390d310067f41594323f5fb7058540
  | 7 => 0xc9321acff705912001ebc6490930006bf64585302fded75cc920006ec52d8930264fe7618d10006bd7690d20137ce3118931014bc765094123f9c32191320969f7418d4203ef7215843224ebc6590e321e7ae2110f2104fac4390920006de70d8d4200dbc70509400f5be748c9310067f659891003ef4215843203def764c832004ff7458b30024fe7558732005df7358540006bc3159232095be7358643014fe7158232096be7690d3103fae64cca3203fce634c83219edd3198f213373c6590d2001cfe76d91302967e70d9510097cc434c832006bd51592320067e4159730195ee730c920005dc7350910096bf7610d20006df6398d21216bc6090d41006ef62d8131006be43583211ddbe7390d1003cfe72d913104ebc43d912001ebf6190d4113edc5418d4223fbb2010d2019eed51d8931037b57110d1003faf7450b2021ebe71d913103cfe72d912003eef605092000dec7050b20006bc7458f210067e64d952003cfc76c853014e6c65cc920006dc43d8d2003cfc764c720216bf50d9130004fd72d8141006dd70d8d423bebd6590d30006de3118d20006f551d85320067f6558520016f4614852029f7b10d951000dfa76cc130005dc73581210067f65cc910006be43d8121005df7358121024fe75d8d420067c65d912001cfc7458f2000efa76cc13003cfe72d8d410247c7559110004fd74d813121cfd71d91312e76c650c920004fd7198d2003fe77148720005ed74cc92001cfe7418d20096f97098d10006bc6019132004ff75d8d4029e7d31d95102cdee76c8520004ff7259130097d7714c730096bc6390d10006ee30189310067c43d951001ebc6450d3000dfa73cc1303a5df754c53003cfd74d81420063f6590d20006be43d85403addd75cc53015df47158132005ef7150b20004fe768c9412967d20d951000cfe7098e42004fe764c9400973d7510d32004ff755864324ebf6390f2100cfe7058f2101cfd735933000cfe7258720006be40d9121006f741d8520006bf64d8931224fe7618910136ef5118931007b464cc531246bd6590d103467e40d9520004fc764c941006dc30d8d4103ded76ccb203febf42d85400979c43cc530006be60d91321aefa40d81420975d65cc730007eb7048520006be651913140ebf41d8940004fd764c910004fd755832103cff71d8d21005bf744cb3103e7e205943221ebe7690d41006df75d8d42096dc3018d4103cff745903203eec6298a4301ebc6490d21024fe7558d1013edc4118d42005ee739092003eef7418931065bc744c720005bf744c530004ff7058d2103ebc425932003cfe76d8930094fc7690d21094fc76cc540004fd75d8940006bd6390d10214fd70d9130154fd7298d20216bc6090e3221ebe6190d43006dc31d8d42004fd7690910096dc7018d42005ed71ccb20096b
  | 8 => 0x96f86058332096bc4358b3001cfe74d891009fac4250b30004fd7418d10096be6358243024fe7558730096bc6459330007ad7290d42006bf6490d2100cfc70d913103ebe4259320016dc61cc73034e7e72d9520216be70d9130094ff75d933001cfc74d8d20004fe764c94103eee621894303eef75189313e67c10597303176c65909200aef421d8540005ec724c53000ddc704c530006de31d8d200067c72d9510006ed5318931006bc6418930184ff7359132096bc7610f21004fe76cc941014fe71d89430067f42d95200067f6590d2003efb2058321096dc7218d42024fe7558f21007ad4250520004fd75593200067c755912019eec61cc92013cdc735903203cfe72d853021ebe41d9331006df4318d21004ff725933003cfd70d8d20006ee761893129e7e31d9510216bf6290d20006bd50d9131094be73d9130006df63cc9203467d72d9520096bf7690f2019eed71d893123e9c4218d42076f421d853000cfc7650d300979d7510c320067e7459432004fe760c9410f5be7498931166be54d9132106fa1058331004fd7498f2124ebc6290d10004ff7058632006ac64d8931006df1018d4203cfc72591100c6bf42d9121006dd71d8d421debf6010d10014fe76cc921024fc75d8d402967c71d95100079f6390d420967c7359432006ec20d894121ebc6190d30006bd65d9130005ef7258131006bf644c530006dd6318d100067f75591100967c31594320067d74d952001cfe7458f20014fe71d8143004ff75d8943166be64d91320a67f7359730006ee70d8931006dc51d8d421e7ae2110d210079c6310d20006ef74d893101faf6290d4207ebf41d9130486bf4018d41006dc638c94103fac425092103eec620c910006ee52d894101ebc6490f201f5bc7558243004fd76cc910014fe768c9310f5bc744c931006df638c941006de71d8d42006dd6318d21136ee101893101f9e7390d401e6be6110f200067d658cb30004fd75d8543096be6310d21096bc4358331006bd71d9130024fe7558d211878c42d8d42006bc72d9130024fe75582420067c715973003f6d654c8320979c3090d30096bc6390d20006bf7059232006dc634c9211eebe6510d3021ebd10d91312d7cf430c920094fc735864203dec72cc7200067f655912003cff768c91019eec31d8931006be7159232096bc4318d40005bc7350941006bf745912126edf31d8d100f6bc54d9131004ff75d8142014fc7159032004ef764c83203cfc72d912003ebf745932104dbc744c920096bf74593311f6be6590d2104ebe7610d203fef541d8540194fd7098d20006dd5018d42024fe75591200967f3059730006ed54189313476c72d9520006fb70591204c79d5310d3224ebe6258a4303eec6298b31004fd7198e42094fc7498d211e6be6110d203476c20d9520007af64c
  | 9 => 0xf72d91300979d6110c320067d71d9520004fd71d9332006f47158d20215be7058a430057f7558930006ed50189310067f6558d1000dee70cc920006be43d81311a6bc64cc930006dc735891024dbc7598a434af9c5110c3203cff7658b30186bc648c931265df764c7303f6bf42d8141094fe73d8542046f431d85200967e7518d21004fd7018d21006ee21d89401a4fd74d9332006ef630c9201f6be6590d42014fc71d89301b6f621d854201cfd71d8941104ff7158d100f6bc644c53003cfe76d8940004fe7690d210247e76d9520024fc75d9131004fd7598e42006bf6450d31004ff7559130167ac4258d4203cfe72d9130006bf649893123edc4218d42006be21d9132005bd740c9410969c6390d41006be70d9132004fd76cc540004fd73d91200979c6510c32014fd7018d10094fc7598d200a67f765973050ebf6590d43014fc764c921035be74d8d10007cc7350b2003cfc76507200079c7350940004ff7358720006bf6390d20136ed10189313467e30d95200079f6310d2023f9c6110e32004ff7159232095be7358a43004ff7158b30004bd74d8d2116e7c654c910006ed6218940096be6358643215be7610d30006be74d8d2123f9e3219132024fe7518d21006bc4358632006bc64d8530186df40d8d421879e7510e320977975cc13021ebc6190d420963e4359730216be20d91300857e750c930014fe76d854003cfc7359332096be6390f2121cbe7619131097ae434c832166bf4158a43156dd3058f20006df70d8d424f6bd6590e32005bf7058643004ff75580320967c6459730006df73591301879c438c94100dbc7090d40004fd7498d2104df9709894000cbc7650940014fd73d9131006dd5218d42094ff7598e423e67e405973003f6e750c920066bc4359320006bd6390f21006bc43d89100debf4059321004fd72d9130004ff73591201debc6010f21024fe75d9121024fe75d853013edd4318d420973c4359730004fd72d9331096ed7298d21094fc7518d2121fb65190d10006bc5159232095be7390d43006bf640c931004ff75590320aef46158540136f64158432004ff7158242006bc61d913001ebe6450720006be43d8141006ed74d893109dbc744c73023ebf6310f2103cfe72d9331096df7418d4200df8704c920204fd7650d3121dbc7198a4303cfe72d933003cfc7358332004fd72d9110004fd75d913223ebc6210d30004fd72d8540006bd52d9131216be6090d4212efa10580320979c7210c32187cc42d8d4215edd3158f21094fc75d9332006bf75d9132077d4614c530007ae4318931014fc725932121dbe71582430c6bc40d91214cebf6590d3201ebc6450920136ec4118931006f761c85400977a30597303467c40d95200067f745973000cfc7358b3003cfc7650e32004fe7650d2000cfe7058d21
  | 10 => 0x8d21136ef1018931096de4318d41186de54d8d42094ff7690d100067f4259730004fd74d8d2103cfe7690f2123f9e3210f212f76c65cc9200967e4359730006ef7258d10014fe76d852003eef60c852024ebc6290d3103cfc7259232006de7618d420967d75d9330014fc76cc92103ef8205823248ede43d8d4103eac6250941004f7715912001cfc74d8d10094fe73d9121166bf43d91320969d7610c3221f9c31d91310069f6310d21006ef725912103cfd71d8d21006bc31d9130005ef7258540006bd6558243096ef6298a430073f6590d20186df72d8d4223f9c2110e3203eec620c9310967d7518d213467d30d9520016bc7650540007db704c530004fd7559131186bf405923202d7e750c91023e9e4218d42004ff7258d10006ee21d8943006bf6490931024fc75d813124dbc7258243006ed52d8941006df63d8542006bf6458532004fd7650d21006bd51d9130004fd764c720096dc5318d42094fe73d9130006bd65d9132004fd755933103fcf734c83200cfe7098f21005bf744c940096de5318d4203cee76d893121fb62190f21006bc65191310067f65d912000fda73cc130004fd7098d21004ff74587203467e10d952001cbe74d8d103c6df30d8d40006de53d8d210967f31594324bddf7350c32005bd74989310076f650c92000cfc7058a4323f9d7210e3221cff7459131096be4358b310979c3110d310971d7510c3203dde73cc93203cff7658910004fe768c940006be72d9131004fe7650530094fc7359120014fc7118d403467c72d9520006bd54d9121094fe73d894000cff71d8d10067ac4350b20006df6398d40014fe71d9332006ef40d8931024fe755911001cfc74d8910006df7358910096f431587303edbd7550540005bd749893020e7c6550d20005bd748cb3103cfc7259032004fd7198f20014fc71582323467c20d952029e7f41d9510024fe75d814200cfd7258321096ec3258b31004fd7558d21004fe769093117cff764cb310067f74d9510024fc75d9130004ff7558d203c6bd74d8d4001dbe7390e42096be7610d32046f4615852003cfe7650f20096bc43583320067f6518d10096be43593300f6bc42d913100cfe7298f2021ebe6190d42014fe7158b30075f97098d100aef641d854003cff7258f20176fa30582321eebe6510d3209ebe54d933015cfd768cb311dfb61010d100557c7558520006dc63d8142006be7559232004ff7258243016f461c85302179c30d913041dbf7590d40005ef74cc92001cfd70d8940096bf7610d21024fc755933103cfc7690f2121ebd71d9131006bd71d91322dfac43cc9201879e7110e32006ec64d893101cfe7498f2023f9e3210f20014fd7358730006bf6310d1028ebf41d911019eef31d8931004ff75584321eebc6510d20156fa20d8132005ed710c920006b
  | 11 => 0x7ac64d8931004fd76c85300067f1059432014fc71d8d40096dc3118d2001cfe74d8d10024fe7598f2021ebd73d9131096bc43593320673d7510f20096bf62586433e67f70597301869d7610e323467d10d95200076f6590920094fc7418d100979d7610c3203eec62cc910015f6718c931005ef74485201ee3c6510d20006de3018d4107ebf4158243095bc7398a4323f9e6510e3201f9e7390d4103cfd7118d2123ebe7610f21005bf7458132006f761cc520004fd7018d411dfba2010f20096be43d9331006df43d8d10094fc76cc941006bf6450932006bf74591311debe6010f21024fe75d9110024fc7558321006df638c9402967e20d951024fae5290f200979d7010c32007af744c83211efa60d81414ef9f5310e32214be7610d300967f615973016d7c755813246cff7650f31006be71d913223f8c2110c3204fac425814203edc3258f2010ebf42d933101ebe6490f21005df7350b3100cff7658331066bc43d814223f9e2110c3200cff7118d10217ac2090f200247e7518d210979e6110c3203eef7018931405bf7550940024fe7518d42096bc4398e423476f72d952000dbc7650940007cf724c730006bc75d91311f6be6590d4119eec51d8931024fc7559120004fd71d81430978d7210c32186be5459232004fd75d913137def7550b2000cfe7059131006be53d91310067c41d952003eef604852000cfc705913145f9d5310d31096bf62582430067f73d9510005df73581410c6be7610d21024fc75d893100cfe7059232006bf64d8532006ee54d8931024fe75d9130006ec5418931004fd7498d200067f6518910014fc7158b3004fae7210d20186bc43d8d42006be43d8941096ed76cca321871e7510e32007cf7350920094fc7518d1001eee6450920015f4715092123ebf6510e32014fc715803221ebf10d913103fcf63cc932216be6090d4301cfe74d8532024fe7558d20005f9708c930004ff764c720004fd70d8532024fc75d8143004fd768c940004fd75d913003ebe62509401be7c65509104df9e5010e323e67d73597300067f4059432006f751d8530096be6310f20006ed4318931024fe755932021ebc6190d32094fe73d89100f6bc43591310979c438cb3003eec65cca32096be4358732136ed4118931004fd755843224ebf6490f21014fe7118d103e67c4059730014be7690d410979c3010e32005ef7250d32005bd748c931135ec714c83203def7648720426bf4118d400057f755813103eee6218931006bc53d9131006dc7359110014fc71d8132216be7690d40004ff745832123f9e3210d2101ebe6490d1023f8c3210f20006ef620c941004ff7559110005bc7350540096bc7690f20024fc755932103edc3298f21006bd7690d10216be6090d32004fd7098f21006dd53d8d414d7cd53cca3201cfe749
  | 12 => 0xf2110f20006be60d9131004ff75d911034e7c32d952003cff7690910006bf6458132014fc74d85400bcff7058910004fd71d9130097ae43cc932005ec7258543006ef624c93103cfc7258642004ff7558730094fe7398d100047f755911013edc43590320979f7510e32004fc764c9400857c7558530416bd6590d4040eed42d894003cfc7258e42186dd40d8d42004fd7650f200b57e7598d40005bf7458530006ef7258d21274ff7159110006bf64cc5301a5ef7258d42006f7715911000cfc7098d21004ff75d813203ebc7650940024fe7598e423e67d3059730006bc43d8530094fe735903201cfc74d852000df87048520004ff7158032024fc7559121006bf52d9131405bd7550940186dc74d8d4201ebc6490d31004fd70d893138f9d5310f2013f9c430c94001ebf6090d40006ec60d89313467f10d952003cfc7690930006ac4318931136ee2118d2101cfe7498d1001cfd70d85404df9c1010e32016de614c530007d7714c530006be43582421afe870509200679e7310f20005be761913201cfe76d912100cfe7258f20024fc75d812121dbe7619131006bc70d9131094fc7650b3124ebe42d933203fce73ccb201debe6010d314bedf631894303e6f205943223ebe6210d10005ee73c85200ecfd7698d103bf9d5390d30005bf744c52003ebe2159232006ec5318931024fc7559320014fe7650d31014fd74d8d4137ded7550b20006dc5018d42134fe76cc931006df63cc9210c5bc7458d210967d7518d423e67c2059730094fc7498f2100cfe70d854200dde70cc73003cfe7298e421eebc6510d210979c7110c32067af4150b200df3d7510f21006fb7058910004ff764c9103e67e3059730095bc7358643004bf7458f21005bd74c8540014fe7198d20006be43d893003ebf4258242006ee5318931004fd75582321e7bb1010d10004ff7558321004ff7458b31006bf65191320979c3210d32137cc3118931006bc645853001cfd73d81430057f755911015ef621d853203cec725913101ebe6490d21066bf415932020e7e6550c32095dc7350b32006bc6350941096bf6210d32476ee42d8941095be7390d310067e61d952003eee6218910006bc51d913003cfc7690910004fd755824303eef205932103cfe725903200cfe705903234f7b20d95201e4be7690d310067e65593300057d7518d41004fd70d9132366ef764872001cfe7458d10005dc73509310047f7558d202977471d9510006dc43d8d21006be74d8d1021ebe6190d40004fc7650d200979e7310d3203ef77158632005df73509321a6bc64cc93203eec629093119eee61cc932006bc70d91321ddbe7390d20216bf73d913000dee7050920156fa60d8132005dc7350920006ef65d893115ef631d85320c6bf4059121094fc7650730096f73158730006f77158d21
  | 13 => 0xf200076f65cc920096bc7610d10004fd76cc940216be6090e320067f7559120006bd65d9131014fe76d85301e7ac2110f21006de7518d420057d7598910007e970cc92002d7c7558d1003dec724c520005ed71cc9200067e64d9510096bc4358432036bc6459110006be43d85421dfae2010d2034e7c42d9520007ac4348720004fc7650d21215bc7058643007bb7050940004ff7359121004fd75d8141006bc65d9132004ff7458f21014fc7650921024fe7559132024fc7558243185de7618d4221ebe51d9131096bf6158a43004ef72591310979e434c730004fd74d81320ddf77158941006bf7458d2111efa40d81414379d5310d21024fe755823221ebc6190f20005ef724c540096be7690d3021ebe31d913124ebc6590f202179e30d913013e9f4118d420067f6550d20066bf41d814200cfc70d8931004ff75d8d41004fd7690b31006bc611913000cfe768c93000cfc764c92003efb20582420967e7598d100979e5310d3201ebe6490d3224ebc42d933203e7d32594320978e6210c32006bc71d91300c79e7310d21006de21d8d42024fe7518d410967d7518d41004fd73d8542006bf64cc931186bf435923200cfc7098e42014fd72d91211e79e31191310979f7010e32024fc75d85404bf9c42d8d420067c4159730216be6090d41014fc71591200247c75591200dfad7210f2100cfd7118d10004fe76cc5400247e7518d42006ef43d893121ebc6190e42006bd75d9131247b55190d1045ebd6510d31004fd71d93300079d53d9130094ff7118d41004fd7690d20006ef75d893123ebe7610f20006f471591200fe7c654c520005bd748c940375ef75ccb20096bf6310d3121ebc6190d4303ede3258e420f6be73d9131006dd5318d4124dbf7598a43094fc7598e4203fac6450b2014e7c65cc920015f4714c9211df9c3019130006ed6418931216bf40d913003e7e2159432105f77158d10004fd769093044f9d5310f21096be6398a43456bd6590f21036be64d911011ef860581411e4fe7690d31006bc50d9131006de3118d423557e76d95203e67e1059730006bd651913000cfc7058642006bf64d8930396bd6590f20006de5118d42096bf7690d21006af64189311fefa60d81431eebe6510d10096bf6190d3103cfd70d8520005f571cc921096dc7418d42005df7358940007ac744c8322179e3090d3019eec71d893100cfe76d8141005f77158132024fe7518d2017edd31d8d21004fd7558d10014fc7198f20006dc31d8d20006ef63cc9200067e72d9510094ff7690f20004ff7648530024fc7558d1000cfd73d853029e7c31d951032ebf6510d20004fd7098e421f6be6590d400df9e7310f2135def75487200c73d7510d21096df3118d101e6bc6110d20164fd7690e32004fd7598f20067ad7210f20006bf6450b3023fa
  | 14 => 0x4fd75d933203fce73cca320247c7558d1003cfe7218d40005ed744872033eef20d8940096bc7690d20006be305923203dee73cc93203cfc735873223dbd7610e323febc43d8540014fe71d8d42096be6210e32096bc6310d1029e7f31d95100973e7510d32146ee650c9201871d7510e32174fe7618d20014fe76d854201cfd7018d40094fc7650b32006bc4358232236bd6510d1001cfd71d81410079c7350941005df7358142004ff705864324fac7290f2024ebf20d91320979f6110c323e67f105973021ebf6290d21006ec7259131006be435872027ebf40d9110096df7118d42006dc71d8d42006fb7059110166bf40d9132216bc6090d311b6f46158542014fe76509212967d70d951024f9c32d9132006ef6250931024fe7558632094fc76cc940005dc7359110004fe765093000cfe70d8543004fd73d8940004ff7159320006bf7458d2011cff7059110014fc7358331096ef3258b31024fc7558f20005df735891034e7e42d9520004fd7218d1000dea70cc92003ebd7259232016ec7648520006bc61191321879d7110e32024fe7558b31166be73d913203cfe7258242006bd6310d10096bf7610f21004ff75d8d20006bd6390d211c6bf40d9120006ec5018931166bf4058a43096bf7459332216bc6090d43046f621d852019eec61cc932006bf6390d21006be7690d10016dd76cc730014fe715824339fd953cc130006ef6418931096de73d9332024fe7559332005dc7358910216be6090d2101ebe6450b3221ebe6190d30004ff765073000cfe76509200973d7510e32007ae435092007ebe54d9130006ee6018931165ed7298d420067c7558d20006ef6298940004fd768c910094fe7398d20006ef62cc941006dd53d8d40005bf7458532004ff745803201ebc6490d10014fc7650d31024fc755823221ebc41d933103cfe72d8141106f710d8530006ec4318931005ef7258543006dd6318d401f5be755864329e7e71d9510006de30d8d41015f6710c941006bc64d8931096be43590321ccff745912100cfc70d8910006df5018d42466bf6590d3103def74c8520004fd75d8d2142ede43d8d40004fd7518d100567e76d952024fac3290f200979f6510c3213fcf4218d421dfb82010d20004fe765091007fac4250930006bf71d9132024fe75d813143ebd6590d211e7ac2110d21005f771591201a4ff7650c3203eec62cc931005dc73589400057d750c940006dc60d8d42004ff7650f210969f6510c320067f4359432024fc755833103cfe76d8910004fc764c520016dc61cc530006ee64d893124ebe7690f20005bf744c941004ff75d8d100979c7010e320c7ad7210d2107dbc744c530005bf7458d10006be6019132005ef7258141096bf7498e42136ed31189313467f72d9520096dc3018d213e67d1059730397ad529
  | 15 => 0xe764c920006de6118d4213f9f4018d424df9e3010e3215cfd7298d2113f9c430c941006bc75d9132006df5218d42006bc30d913223ede4218d4200dec70ccb2001ebe6490d3003eec7258f2000cff7658332006be21d91300fd7e750c93124ebf6590f20004ff7650d212c5ed75c8520005ef7250f200247e7518d41005bf744c92103cbe7690d42386ef7650b20096bc6310d201879e74d8d4201f9e7390d4200cfc72593200067e71d9520005f77150921004ff745833103eed7118931215be7058643006f77158d2003cfe72d81430067c74d9520006bf6390d42014fe71580324ef9f5110e32096bc6390d421b6bd4159321004fd70d89410c7ac42585421ddbe7690d30004ff7058b31006bf50d9131486dd4318d4110dbe748cb311fcfd74d93303cf5e654c7301fef86058143024fc75d911048edd43d8d41014fe7159232004dc7359110024fc75d81320979c3010d30096bf6390d43004fd71d8d200067e73d952010dbc744cb310067c73d95101eebe6510d21004df7358910336bd6590d2007dbc745893024ebf21d9132004fd70d9332004ff735932024fae4290f200efd8704c53001cff76593320067c71d9520004ff7058e42004fd7650b30006ec21d894001cfe7458331096bf6298a430067d6550f30097b431586431f6be6590f200065e7518d42006be7690d2021ebf41d9131006bf6450730014fc7118d104cebd6590d32004fd73d912123ebc6510e3250ebd6590d4303feb6050920136ee3118931005dc73581420057f7558d202967f40d951000cfe70d9331195ef7258d20006be61d913003ef8205832101ebc6450b304ef9d5310e32005f5710c91003efb70582420ecff7058d100befa10d812100cfc705933200cfe7058a43004ff76505300063f6510d20006ef52d89301e5be7690d31096be7610d30004fd7118d20014fe71d814223f9c5210e32024fe7598d10004fd7558732006ed6518931037ac425091001dbf7250940206bd415933103e7d425943203eec624c93000cfc7058732096de73d93300067e6159730006bc43583210067d6558b303b6bd6510d30095be7310d32096df3018d40096df3198f2100cbe7690d4000cfc7058632014fe71d912000cfc705913215edf3158f21007ae7290d4232f3c6510d20024fe75d8d200979f3290e32004dc7358910094fe73d8121096dc630c94103cfd73d8532007af6250941136ee511893100fdb63cc13001eec7650920006bf64d81320967c3259730005df7350b32006bd545923213edf4118d42006df630c941004fd7558730006bf64581311f6be6590d20006bc43d812123e9f6319132004fd73d8910005bd74485400979e7310e32186df4359232004fd73d854021ebf73d9131096be7690d32004bf7458d10006bf7559232005f5718c931024fe75d8132
  | 16 => 0x8f20006bf6310d20006dc634c9200afb46150540005ec73509200067c6518d20006dc6118d424eebd6510e324b69d6510c3201cfe7458d2023f9c2010e3221fb42190d21045f97098910096bc6459332096df7218d42004fe76c854010df77158d410eefa30d8131004fc7648540004ff75591201e7b65110d1003eef20586424df9e1010e324bedf20d8d42004fd74d8931006be43d854323f9c3210f20006bd6390f200557c7559120005bd748c9412967d71d9510005ef7150920006df7359110004ff7558f200979e7110c3203cfc725864301ebc6450d3100cfe7650d30004fd7598f21024fc7558f2123f9e5210e3205dfb705891018e7c658c910004ff75d8131004fd75d8943006be41d91323f6bc43d81410067e74d9510006de6018d4204ebc6459120006df4318d10006dd75d8d42007af6418931014fe76d8532096bc43d9332166de4358e4213ebc640c93100dfa700c9403467e70d95200979e6010c32097ac3290e32014fc7159132005bf7258643006ec21d8943006de53d8d4103cff71d91210067c745943203ebc62509410c5be74d8d2103ede7398f20444ff725912103eee621893003cfc7690f2003ef42158720096bf6158243004ff7059331005bf7158a4301cff765911003cfc7258331006dc638c9400067d6590b3000cfd74d8d40006be43d853224ebc21d91320067f65cc920006ec6258131004fd7690d100067c43d952001ebc6490f2121dbe7158a4300cfe705873207ebe64d913007ebf43d91304c6bf6510d32014fc7158d20004bf7458f2024ebf6390f20275f77159110004ff7558232014fe71d8940004fd75d9330006ef5018931024fe75d8d10216bd73d913023f9e6110e323c5df735913003edc3258e42006bd6450910004ff7458d10005ec7259131216bd40d9130004fd73d814100cfe70d8d42136f710584320057f755812103cfe76d893101ebe6490d31186dd41d8d420975c305973019cfd7198d21014fc7158f20096f86058331014fe7158e42004ff75d8d420057d7518d4213fac4218d420067f654c52001cbe76d91310c6bc43d9121007af6450920006ef72591313467d20d95200979f6010c321debf6210d20096dc3018d42006be50d9132006bf644c93002d7e7598d10004fd73d8941005bf744cb3001ebe6490f20004fd70d8d4203eee620c93003ef7215872003cfc72582430079c6310d210067f715973017ef6315863200cfe70d89311f6bc6590d1023ebc6210d100247c755823203cfc768c941007ac4318931005f970cc920004ff7559330014fe7159032006ed76ccb20004fd7558f2024f9d6390e4223f8c5210c32006dd5358e424bedf6398943004fd72d8543094fc7358321006dd6518d42094fc7418d21004fe76509310067c42597301e6bc6110d30005fb705092000cf
  | 17 => 0x3476e20d95201b6f641d85420067f654c910006bd6390d20006bf64d813100cfe705933101ebe64505200967d7598d20005fb704c530094ff7598f20004ff7650930035be7418910006f7614c530006dc30d8d42007ae43c8520004ff764873003eec751893103e6c725943219fe431d89311e79c3119131004fd7558b3021fb67190d4127ebd40d9110004fd70d854300ddc764c530217ba7090d4003cfe7218d41004fd76c87301dcbe7690d30194ff7258d20006df65d8d42006ed630c920024fe7559232006de6518d42024fe7558b304bedc21d8d42094fc76cc520014fc73d8530006de50d8d4200cfc7018d4100cff71d91104a79e5010c320979e5390d30004fd7558d2001cff7650921186dd72d8d4224ebc6590e42096bc4359330096ec6258a43006dd5118d42145ec754c832095be7398a4303ebf20592321aebf4059320014fe715833201cbc7458d2000dec704872036fae43ccb2000dee7048520096dc3118d42005ef724c720067ac42d8142096af6298a43004ff7559321004fd75d81310c5bc7458121006bf6450930004ff7358642006bc64d8930004ff755864201cfe76d9131215be7098a43096be6358a43024fe7559032094ff71d91310247e7598d10006dd6318d4129e7e21d9510006bc43d8131006df4318d201afaf4050b2019eee2198d210979d7210c32024fc755824223f9c2110c320057d750c941006df73591311c6bd40d91200075d7518d42004fd71d8142006bf745913203dec7250d3223f9c3210f210979d6510c32015bc7190d41006bd7690f201e6be4118d41006bc10d9132014ff70d9110005ed740c92001ebc645073003eec61ccb200067e31d9520004fd71d8d421b6f410d8542007cf724c530015be7190d411a6bf41d933203cfc76c854010ebc64cc5300079d5319130004fd71d912021ebe6190e42426be5418d4007dbc745853001cfe74d8930005ec7258540276f710d8540024fe75d891003cfc7298e4200dbe7090d402b5ed75485204bedf21d8d4224ebf6590e4224ebe32d9132004fd760c941004fe764c540097b76158643094fc7359121005ef7259131094fc75d9331004fd7218d41004ff764c9400067c61d952009dfb7058d401c6fa40582420067c64d95100967e7598d2024dbc7258643014fc7158332096be6310f21266df30d8d10005bf7558a4324fb72190d2101cfc74d813200cfc705912103eec65ccb2000cfe7098d21006bf64989302473c6590d10006bc649893119eed41d8931004fd76cc9410d6fa10583210979e7510c3201cfe74d8530005bd7498b3016e7e654cb30006de2018d4201ebc6490d20004fd70d8943016dc614c730096de5318d41216bc6090d42005bd7498b310963c43597300079c438c930006be20d9131097ac434c832006bd6310f2103eec325
  | 18 => 0xc7458d2001dbc744c940005df735852003cfe7218d10014fe71582420971d6510c323edbf755054042edd43d8d4003ebf7459032004fd765073003feb60c8520006dd65d8d4201cff76509320079c6390d42004fe769093026ede76cc53013e9f4018d42006de3018d21006bf64189310067e73d9510094ff75d9332006bd65191320973d7510d300047f755912003e7c21594320067c6559110006bf6458930076f631d8530014fe76d85430969c6390d4003cfe72d813114eee65ccb20005df735854203def7650b20006bc30592320061d6510c3200cfe7018d21497cf434c83223ebc6210d311879f41d8d42096bf7418d42006be43d8520006df43d8d20006be7690d211be7e6550b30094ff76cc91003e7f215943201dbf7250941004fd76c85400979d6010c3203ebd2159232024fe75d85404bf9e42d8d4219def7258d21006ef72591320eefa10d8131006bf6450920096bf7418d41094ff7690d21096bc7690d40024fe7559331096f46158730006be5059232014fe7298f212967d40d9510005df7350921006ee50d8931014fe7158d200967c43597300fd7c75581310067c65d8d20006bd6450520005ee7348720006bf72d9131035bc7458d1021dbc7158a43006df630c9400079e53d9130024fe75d85320067f43d9510005f7714c921005f9700c940165be76d91321f63c6590d100967f3259730005dc7358520094fc7650b30007ae43485201e6dd3118d41005bd74d8d1046ddf735913119eef21d8931006bc60d9132187ac42d8d42014fd70d8d10006df638c91003cfc7259130006df53d8d420067d6598b3003e7f2059432096ee634c832024fe7558032006ee65d8931096ef6298b31024fc7559332096bc43587320067d654c7300f6bf4058643006be40d91320967e75d93303477820d952013f8c4218d420067e725973003eac625094038f9e5310f20004fd75d85403e67d2059730006ee20d8941007e7614852001eec64909201f6bc6590d3214eee65cc920014fc71d913003ebc21592320047f755823221ebd51d913100cfc74d8141094ff7518d10006bd7690f2119eee71d89310073f6510d200067c7558232005df7350b30004ff76485400067c655891003ef77158642197ea70cc92019eef62cc9210079c438c9101e7b62110f21006df634c920006ee74d8931006ed62189301df9e3019130004fd75d912003ebf215923200cfd72d852001cfe7458d21005bf7458121004ff7158f20014fc71d8d2001ebc6490931024fc755863203cfd70d9120097b73158643096bc7610d2121ebc31d9131006dd5318d211debe6010d3200cfc705903201cfd73d8543096bc6390f21014f4715912003ebd425864207ebe5458243097b43190d31005ec734872003fad64cca32006bc6458532014fc7118d200067c74d9510
  | 19 => 0xd100067f6518d20097da53cc130014ff70d8d10005ef704c8320067c6598d1001ebc6490910014fe715913003ede3298e42016ee6148520006bd53d9132096be6390d2015cfd764c92103cfc768c910006bc43d8930096f57198d21094ff7518d20006ef53d8931156ef2058b3003ebe425903236faf7290f20096ed7298d20006bc64d85321aded74909200067f6550910004ff755833103fe77148520006df7359132216bf6090d20006dd6318d20096de4318d4003dae7290d42006be61d913201cfe76d9110006bf6490d321e6bc6110d3215ef410d85321a6bc64cc93113fcc4218d4217edf31d8d210967c305943224ebf6490f203b79d5310d30014fe71d813217cfe7618d2103cfd7418d4200cfe70d91320673e7510f20216be40d933044f9e5310f210f7ac4250931186df7359232006bc705923200cff71d891003eef600c920095dc7350b3123f9f6110e32004ff7559332006ed621894104dbc744c52003ede3298f2001cfd70d8d40004ff7358321136ee215843203eef63ccb2047ebd6590d4123f9d6110e3200dde704c730016ee614872003fac4250920096bf6110d310979f7510c320067e3159730166bf42d9132006ef725912003cfe7690f2011efa10d81410079e434c530005bd748cb30004ff75d913221ebc51d91310979e7310d3001cbc7458d101869c735923203feb6048520094fe73d814100cfc7018d21004ff7259131014fe7258321004fd7518d40094ff7518d42014fe7118d20006ef725911003ebc4259032024fe7558643014fd70d8910094fc73590324379e5310d2102e7e76d9510096ec6258b30136ed5118931017d763cc531136ec2118d2100cfc705864323e9e6210c32006ec62d813103cff7690b30007ac64cc932016ee61c8520014fe715932000cfc70d8543004fd7498f20006fb7058d20096bf7690f21254fe76cc53003e7d2159432004bd74d8d1021ebc6190e321f67c6590d10004fe76cc52023fae5210f20006dd5318d40096bc6390f204bedc72d8d42006bf53592320067f41d9520005bf7458131006bf62505401b4ff71591211dfac2010f20014fc71d8143015f671cc921014fe72593214a79c1010c32006ec30d8931006dc10d8d42006dc5118d42004fd72d81311f6be6590f211cebf41d9121006bf54d913219eec2198d210067f7558910014fe7198f20215bc7098a4308dfb7058d1001cfc7458232285fb705911024ebf6590f213e67c70597300f6bc6459131136ef4118931004fe760c94023f9d5210e321dfba7010d1023ebc4218d42004fd75d8d4003cfc7259131005ef724c730186de41d8d42004fd755891001cfe7458321006f77159121004ff7559132476bc43d894100cfd74d854001cff7659330004fd7650d104e79f1010e32004fc765091003cfc725873001cf
  | 20 => 0x6bf7459130096be43d9330186dc4359232004ff7558e4201dbe748c940004fe7690d20007b97090d401afad4050b2001ebc6450932004ff7058432096f43158643416bf6590d400379e7310d10006ec52d8943006bd6519131004ff755933102d7e759891022eef21d8910136ec51189312379d5310d10024fe7558e42024fe75d8542004ff7258643024fc7558b304febf6590d42006bf7458910094fc7418d2038ebd6510f20004fd74d8d1003cfc725824201cfc7458d10024fe75d9120004fd76cc520095df75cc730006dc70d8d420979c7010c3200ddc70cc7300067f73d9520006ef6298941094fc7498f20004fc76509310979e6210c32007b76150540006bf65d9130006be30d913201fb771505401debc6010e32166dd4358e42004fd70d9131005ec725814103ede7398f210067c105943209ebf42d93301dcfe7690d301467f7359432006bd74d8d10037b97010d101167c65cc52003dec73c8520004fd71d9132005bf755824301cfd72d8142024fc75d8142096be43587300f6bf40d91310067f7558232005bd7190d40216bf20d9130096df7018d42005be7610d32006bc63509400067e7159432094ff7518d4103cfd7258f2024f9e32d9132006bd73d9132006bf7458f2121ebe6290f2100cbc765054001cbc7458d21186de40d8d42006be43d8143006ed63ccb2023dde7390e32166bc644c9301aefa60d8142184fe7690d323d5dd754c7300047d75d9330094fc7690d201df9e3010d3000cfe70d8d2100dde70cc530004ff75d89300f6be76191313467e20d9520004fd75591300065c4359432006bc7458910226ef20d891019eee41d8931006be41592320079f644c530004ff75d8931024fc755913003fe8204c920006de53d8d4044ebd6510f21097ce53cca3203def750c920006de7118d4221ebf6190d2100dfa70cc9201e5be76d9131004fd7518d4100cfe7059332075f471589301aefa20d8142096df3098f20004fd7650910096bc6390d4103cfd71d8121006bd735923203eee769092003ef8205824203def7590920005df73591100eedf604c530014fe71d8d203e75d7359730006be6019131006ac641893100cdc764c530014fc71d8910006f77158d10006bf6390d4100cfe70d8532097ae43cca320067e415943200cfc70d854203faf745092004ebc4358242004ff7650b31004fd72d8d103bebf6590d300979f7010c32006bc1059232005bf7458d21006be43d81320967e735973003ebe325923213edf4018d42016de61cc530004ff7458f2000dec70509200373d7510d1019eec10d893103f6e654c83203dec7290f201f6be6590d310df3e7510f21014fd7418d411f5be7598a43097b643cc531006bf6450530004fe7690d1000cfe76d8143486bf4218d41024fc75d8530006bd6490d30036be761
  | 21 => 0xc73509200f6be54d913103def75c852000dba7090d40016f4614c5301e6be6110d3000dfa708c930004fd7518d20024fe7558332006dd53d8d4201cfc7458d21015b67190d410963e435943215cff7158d21216bf30d913023fac3210f20096bc4359032096de7318d2029e7d41d951001fb7615094100cfc72587204febd6590d4201cfe7458b30014ff7658732006df6398d100059c7350940217ae2090f20004fc764c910006bd72d9132006bc7458f2003cff70d8d20005bd7190d420067c31d9520005bf744c930186de43d8d420067e40594320079f744c7304bedc52d8d4203cfc7650f201debe6010d21166bc40d913223f9c5210c32325ee769092001cfc7458b3145ebf6510d31005bd741891003efb7058321006ef764c8320debc43d8542014fc71d8142006be10d9132006bf6310d21006bf6448530196fa2058332005cc7350b2024ebe52d913201cff7650d31006bc6498930006dc75d8d42436bd6510d21096bc43d9331097ac6258a4338fad5210f201aebd4059320096bc4358b311879c4350e32006bd54d91321f6be6590e3203dec7250f20006dc65d8d42096bc4318d42014fe7159330005ec7258530216be50d9130004fd74d89100067c7059432004ff7558720006ec64189311debe6010e32006fb70591300067c65d9110004ff7650d2000cfd71d8d1024ebc20d91321e6bc6110f20186df42d8d4201cfc7458b301f6be6590d4303e7e3259432005fb7048520096df7518d42136ef311893123f9c3210d213e67d7059730006bc645813201cfe745873003dbc7290d42006f610d8542004ff7650b30006bf64c853001cfe745803224ebc52d9132004be7690d3219cfe760c931094ff7598d210979d7110c32024fc7558720045f47159120216bc40d933025edf764c730006df63585420979c434c730005bd7090d42004fe76cc910097ac43cc93223ebc6510f20014fe7158a43006bc6519132006ae43d8931004ff764c941006bc21d9130006df635814222eed21d891003fac4250b32006dc63d8542506bd6590e42004df7359110006ed63cc92028ebd41d911023f9d6010e32006bd7690d21004fe76485400067f65d8d20006ee40d8931006f761485200067c7558d10004fd75d9331006be4059232097ac3258a43186df54d8d420969e6390e4213ede5418d4214eec65cc93203eef6090920004fd73d8121004ff75591211dedd3018d40096be435933101cff7650d30004ff7458232006be611913003cff760c9100067e6558730006bf7458d100979c5310e32096bc7610f20014f47158d203e75e305973000cfe7058643005bd7290d40005bd7290d41004fd760c910006ec74d8931006df7358d2011fb8705054004dbc7458d20096de7318d21097d561cc730005df7358941237b55110d10096bf6090d30
  | 22 => 0x9132005df73591210067d72d9510005bf744c9104df9c5010e320979c6110c32006ec40d8931006bc645813103e7f4259432266dd30d8d10006de5358e42006de31d8d400957f76597300f5bc74581310967e7359432096bf6390d32096bc7610d200967f30594321eebe6510d20004fd7690f20006dc7359120006bd6490d32024fe755932103cfc760c9100971e7510c32004fd72d85301e6bc4118d41005ed74ccb200979e6358243006bd53592320ce7e6548730096ef6298b30006bf51d913219eef73d8931004fd7218d40006ed53d893103efb205803200df8704c530156f8605813219eee2198f21006bc60d913100cfe70d8d41005ec7258d10014fc7198d2000cfe70d8943024fc75d854200dee700c920006de30d8d420047d7518d410979e5310e320979f3210e3243ebf6590d21024fe75586422967f20d951003eec61cca32006df634c921005dc7350932004fe768c910094ff75d9331006bd6490e32095be7390d32006dd5398e42024fe75d9331216bf70d913021ebf71d9131006ec52d89310067f7059432004ff705912121ebf31d9131006bc71d91322a57e76d9510006bc6350540007ad7290e420979e6358643007bb7050540005bd7558a431aef8605814200df87050d30004ff7558910006bf645893101cfe76d9120006be41d91304b79f5110c3203eec628c93023f9e3210d2000cfe76d81421a6bf40d9332096de4398e423e67e2059730004ff7159032136ec3118931006ec75d8931007e762cc531006bd6490f2103eef2098e4203eac6450b2001dbc744c94100cfe76d813101cfc7458720024fc75d912100cfc70d91320979e7390d43006ef628c93123f9f5210e3215ef661d8532006bd74d8d210c6bd7610d21206f641d8543006bd54d9330024fe75d8943166bc41d9132006bc4358720006ef42d89310067c7259730006be75d9132004fd7418d20004ff7558f2103edf63cc9321e6bf63191311e6bf6210d21004ff7158d2003cfd7259320004ff7558d101debc6010d31006de2118d420e67e65c873000cfc70d933103eec6298b30006ec65d8931006bf53d9130096bf7418d40004fd7650720204ff7159131006bf65d91310c73e7510d2100cfd73d9130005dc735854221dbe7310d2103cfe72d8d1003efb7058032096be4358032186dc40d8d42014fe71d913201dbe748c94123f9f6510e320057f7559120014fc71d8d4203eee6218940004fe760c910096df3018d100067f415973003def734c832004fd760c940014fc71d933001ebc64509300057f7558530006df7359120216bc30d9130006df7358d21007d931cc1301a7ac4298d42094fe73d91201267e65507300973e7510e32006bd6310d21006bf5459232004ff7159330004ff7158a43006ef54d893104fac4350920006ef4018931007c
  | 23 => 0x6ed54d89310067d6559330014fc7158a43096fb30580320979c6010c320c6be64d9121004ff75d8530006bc65d913030def75509200047f7558d100bded71c8520006ed621893121dbc7158243006be41d912023ebf6310f2001cff7359330096f83058032006bd52d9132006be43589100eefa60d81314e79e3110e32096bf65582432967f30d951023f9f7418d420eef850d81311879f40d8d4203eec7018931014fd73d81310bdf57198910096bd7610e32004bd74d8d2003ebd4298e42216bc6090d32006bd6450720006ef65189312967c30d9510024fe75d8941005df735093001ebe6490d2003eec6450b2016e7c654c92029e7d21d9510024fc7558d20006bf53d91320979c430c930024fc755864203cec7258d10006de10d8d4203dec7258732004ff764c5400067f65cc5204e79e5110e32007ac6418931004fd7690f214a79e1010c3201fbb6050940006bf515923200cfc70584321dfba7010d201eebc6510d10004fd73d81422967c70d9510004ff7158e4203cfc7650d32006bf6390d40005bf744c540005bf7458930097b8605824319eef51d8931014fe7118d4023ebf6510f200067c405943203cfd73d81324bede52d8d420078c430c92024f9e6390e4203e7c7259432006bd7159232097ba43cc130097b83090d30014fc71d9332006f7715891001dbe7390d40014fc71d89401467c650c91013ede7418d42004ff7358242004ff7558a431f5bc7558a430247e76d9510015f673cc531154fd764c9200069f73592321f6bc6590d31006df6398d204b78f5210c32005bd7090d410057f75589104bedc20d8d42006ef32d81321467d7359432005bf7058a4323f9c2010c3200ddd76cc73003def7148520005ef7250e3201cbe74d8d20096bf7610f2013edc73590320079e53191300b57c7558540006df43d8d21094fc735864301f9e7390e42096dc630c9400857c7558930006bd70d9131004ff75d8141095be7358243006dc638c910096bc7690d41015f6710c910006bd50d9132375ed75ccb2029e7c21d9510006ef70d8931006ee43d89310967e4359432066bd7610f2003eee76c8520006df71d8d42096f571d9331004fd72d8d41007cc724c730166be7619132006bc6458930006bf644c931004fc765052032ebd6510d2029e7f21d9510186dd54d8d4221ebe21d91311f6bc6590d30004fd769093113edd4018d4203ebf72592322eded750c9200975e65cc730004ff7458632186bc405923203eef60cc9204ef9d5010e3203cff7118d2100cec7648520006ee54189310057d7518d212967f71d9510096bf6058a43096bc6058243094fe76c8730006bf648c9301eebe6510f203076c65509200057f7558d10005ef7259110004ff71591324c6bd6510d3200cfe7058b31096df3018d20216bc10d9130166bc54d
  | 24 => 0xd750c920014fe7159332076f451d85300979e6358a4330ded755092041dbd7590d40005df735091013ebf4159032014fe7159120016ec61485200079c430c910186dc54d8d421fefa40d8143006bd6450b32095bf76586431d67c6590910004fd7598d20004fd74d852003e7c2059432016ec61c85200067d715973004faf4150920006ed75d8931035bc7458910006ee75d89310079c438c9311f6bc6590d422d7cc430c920014fc71d912000cfe70d933221ebe6190d3203eef2058432096de5318d40005ef724c530006dc6018d42014fe7258f21004fe7650d210079c644c530024fc7558d21004fe76c85300067c65d8d10004ff7558d21005bf70509414ef9f5010e3201cfe74d8d2003cff70d9120004ff75d8520216bc6090e4203cff7018d20007ad4250720094ff7690f21024fe755891004f3d7510d200bef71058720004ff70590320967c3159730006bd6490d10005f77158930005ed74c8520015f4714c931097af3258a43024fe7598d21005dc7358941094ff7598d2029e7e41d9510135ee714c832005bd748c9301f6bc6590d4003eee74189310067e305943201cbe74d8d21024fc755873201cfe74d813113edd4218d42004ff765072003eec624c931017d673cc53109dbc744cb3000cfd71d911001ebf6290d422373c6510d10004fd75d8132004fd7118d42246bf6590d10006be105923223f9e4218d42007b57190d41004ff7558b30076f461585301e7b42110d21005bd7558643024fe7598d200973d7510d31004fc7650d10024fc755843203eec620c94131ded7590920007bb64cc13003dec7250e3200cfe7359330006df51d8d42186dc41d8d420047f7558910005bd7198a43004ef7259110006ee52d893103ebe525923213ebf4118d42006be43d8940006ed6218943217b830d913001dbe7390d42006bd6310f2001cfe745872003ebc6250940014fe71d8d4023fb72110d21006bd6490d20095bc735824310ebc43d8543045f47158d2013edf43590323467f40d9520006ec20d8931014ff7018d10006bd6490d210f6be64d913103cfe72d8543004fd75d8d10006ef725891018e7e658cb3001ebc6450530337ae5290d2023f9e7210e3203faf6450b20004ff71593320d4ff715891024ebc6590f210ecfd7198d10004fd7559330097ac3210e3224ebc32d913223f9e5210c321e7b67110d21006bd7559232094fc7518d40216bc70d9130196dd3098f20014fe7158f20036bf425911009dbe748cb30176df30d8d2023f9c4218d4219fce31d8931014fe71d8930426dd4318d400067c65d8910096de5318d2103ebf74593200969c6310d21006bf10d91320f6bf43d9131217ac2090d2023ebe4218d4201cfe74589100f5bc74589311b7b47150941004fd75d812103ebc765094120e7c6550d10004be7619132
  | 25 => 0x9131217b81090d1007df97098d40007eb705092000cfe7058632097bb3058243006bf6450931006be43586420067d7459432015bc76509410debd7610f21096df3118d41016bc615054023f9c6510e32006bc641893124f9e3290d3201cfe74d8d21006df10d8d42014fe71d89100978e7210c32094ff76cc720014fc715824301fbb60505401879e7010e3246edf31d8d41006bc53d9132217b41090d10004fd75d9110094fc7358910004fd75593210967f3159730006dd52d8d421fcff70591304af9f1010c3219eed10d893101cfe74d893123f9d5210c32096bf6390d300979f7110e32096de73d933101cfc7650932014fc72d8520094fe73d9331014fc764c93100cfe7058432004ff76505203c4ff7650f30024fe755933003cfe72d9110154ff7058d20024fe75d854301cbc7458910004bf7458d200c6be54d9121016dc764c53046cff7359131006fb50d813100cee76cc920006ee6418931004fd7518d42006df6398d4103ede3258f211257c755814103edf7358e42004ff7558632004ff7158332004ff75d8940006bd6390e42007af625094000cfc72d8121216bf6490d30005ef74ccb2003cff7690b3103eef63cc932024fc7559132164ff7459132006bf75d9130097b43110d31094ff764c920096dc63cc921004fd72d81431466f72594320debc64c85302b5ef7548520004fe76cc940096be6390d101ee3c6510d1000cfe7018d42005bf74cc94003cfe7298d1004fad7210d200977a75cc1301eebc6510d32004fd7298d1019eee2158732136dd3118d211be7c6550920094fc7358242096f461587320247c7558d2003ede3298f2124ebc72d913200dde704c530096dc4318d210073f6590d10007ae43d8931006bc7458d1001dbc745824303eec21584320befa20d8121006dd50d8d42094fc7598d21006ef42d891014eee65cca32004ff75d854003ebd325923224ebc6290d410eddd71cc530004ff7058f2107ebf42d9130096f57198d100979e5310d3000dee70ccb200059c7350941014fd74d8941005f771589404b79d5010c3207ebc6459130096bc7690d10006be43d89430057d750c93003cfc7650f21006bf6519130004ff7458432006bc43d853201cfe7498d20006ef431893136fac43ccb2004ebd7610d2019eec41d8931186bc415923232f9d5310d20004fd74d8d20006df630c91021cbe7610d310067d70594320067f658c91004fb97010d20096bc6310f21005bf74589100979e7310d310067e1059432004fd75d8d42006bf6450d32004fd71d89432967c10d9510006bf54d913003dbe7290d4203cff7658b31004fd74d853001cfc74d853204f9e7310d20006be65d9132005ec724c540006bc64d813123f9c6010e3219eee10d8931024fe75d933003fce730c920024fc75d8d4101eee64909200056
  | 26 => 0x47d7598d20096bf7690d2001cfc745891014e7c65cc910004ff7458d20006ee30d8931096de7318d10097af6258a4303ebd52592321debe4018d40095be7310d30337ad5290d2001cfe74583320067c74597300067f654c920004fd73d9110024fe75d81411e6bc6110e320079f735094001ebc6450921006ef620c931004fd75d891000ddc70cc530094fe73d8520004ff755913101fae6290e42024fc75d8d21006bf7459110095bd7698a430bfe870485200063f6590d10004ff7058732006bd53d913003edf7358f20007cf7350b20004f77158d2019cef7258d21014fe715913221ebe415864303ebc42593212977771d9510004fe764c520004ff7359321004fd7690d210247e7598d203467d70d9520216bf6190d10014fc7358b3103edc3298e42006be71d913004dbe74d8d20096ec6258b313e67f405973023f9e2010e32004fd7650d20006ed52d89312bf6c65c8520096df60cc5302dfae430c920006bf6490d2003cfe72586420067e74d952003eee7118931006bf105923219eef10d89310cd7c75581210979c4350c320067c6558d20006dd7118d42004fd75d8142016f763cc5312379e5310d103addf75cc530476bf40d8941024fc75d8d100067f6558910216be30d9130005f7715814201dbe7390d41204fd74d93311a6ee42d89432967e40d9510024fc75d9132166bc645913201faf72509400967c7359730094fc7598f21004ff75d854203eee701893113f9c7418d421eebe6510f21024fe75d9131216be6290f200979e7610c32006bd5059232004df7359120094ff70d913001cfe74d813200cfc7058e42014fc715933224ebe72d913200cfc7018d1003eec6250931006bd75d913203edc3298f2004ebf42d91200067e21d9520006bf70d9131014fc7159320006bc7159232024fc7558e422fdef75cc92012efa4058032014fd725872001cfc7458432094fc7359110006bc52d91300969e7610c3221ebe6190e32004ff73589100979e6398a43006df7359121005dc7359121006bc43d852021f9e3190d3100dbc705054001dbc74cc5403a5dd754c530006de75d8d42014fc7258321004ff75d91311debf6019130097b830582430247e75d93300079f6310d10004bf74589102967f70d95100967e7518d42005bd748c910024fe7559130096bf60586430067f74594320067c73d952023ebf63191320c5bc744c921006ec54d8931006bf7459120006ed50d8931004ff7258730007ac43485200067c4159432004ff75582430067d72597300057f75581320c6bc64485300076f655092004ebe64d9120006ec72591101f5be7558a4301dbf7150540006ef624c9300969e6210e32206f461585430c5f5719894121fb431d9131006fb7058d10004ff7558b3100dec7648520006bd6310d20006ee21d893000cfe70d
  | 27 => 0x8800000a0000000000026005016826c00401700102d00dc00002101b404a05200b816c02003a0060004296034003800000e00000180000160070048074000017003819c01000300b000805a136000025800202b007800c02000000f000819e09000c015800c00000003f43060010d300c4000016006001802610200a800001c61a00b00000000c1002001801e03900d0014034000014803801a03e00002ec0f400100080440b0011002003c0a000201f001809a0490008004022003002804002000100300f87d0003000024000000000080000000010edf57198d100c7ae7210d21216be40582431f6bc6590d4300cfe7058e4224dbd7690e3203cfe7218d20006ed43d8931006de3118d4048ebc43d8d41006de7018d42006bc43d8132216bc20d91303467d40d9520006bc50d9132004fd7118d4001ebc6450b310067f6590d1047ebf6590d4101cfc74d853000cec7258f2003feb600c920094fc76487301267c6550520097ac43cca320979c7510e322dfac7290d20004ff715913000dbe70509401fefa30d81430079f6390d4003eed75189310075d654c730005bf744c9313467f70d9520094fe73d89410067e71597300079f744c530215be7619130076f661d853010ebf40d933107ebc4359130004dc73591203b6bf6510d30006df63d8142006bf64cc932097ac3298a431eebe6510d31186bc648c9300047d7518d4219eed73d893103ef421586420079c6390d41004ff75d814300cec76509200067f7159432137e4311893103e7c32594320057f7558540216be10d9130004ff745891003ef7215864223ebf6510f21004fd755933233def7259120096be6310d204bede42d8d420979f7210e32006ef62989300067f42d951001dbc74586430067c65d8520005ed7448520006bd6450e3200cfc70592320067f43d95200067f6559110014fc7198e42006be52d91300979e43cc530006be43d89310067e64597300067c6598910094fc7359321216bc6090d21004ff7650f20004fd75591214bedc42d8d4203e7d725943203ebe7259232005bf744c92001ebf6150941006dc31d8d401f5bc75586431a6dd4398e420069f6310d1000cfe7058642005bd74d8d20006bf52d9132014fc71d911003cfd7018d2001cbc7458f2123f9d6510e320973e7510d3003ebe4259321024fe75d8121046f441d8520006bd54d9130006bd42d8540005ef744872001cfd72d8542005ec7258131024fe75d893000cfd74d894010fac4250b310079c434c530006ec6018931065fb705894003ebc525923240eee42d8940004ff7458732476ed42d89411e6bf6119131097bb605824301cff7650b3203cfd74d8542015f47150d31006bf6490d104bede72d8d4221ebd41d913103eef7118931186dd43d8d420b57e750c940016de614c730096bc6310f20
  | 28 => 0x4a003002008804807100100148e80820c50994e8613c00000a8004037000001800800119680380680050128000008006000800003800c00487c803e000032002400a00000100200f0009005000800400100c003c050030003800004a012012000400002500c00001b60000189a38000cc80358028000001023834805800600000c80640040168011448002003800c0a600001301442c006700103601a400000700b010804500a89c025604106c000800000600081340080030000000000039034001803441b04000280000210f729602be0050d5000c00002e003086864e000008027400401101a006001032906a00f802a023031804029a001004000406806f01d90640001ff0cb803c0440002d40dc8000022195000800c00200601b0104000017002001400114682f81280290010000072000001807405400a0000004008005035804004c00602a800000a0ea144800006400442e80441120060170c1403602600b81202b200200000ec09a00000180c8006006000001c0265eb000003c2062b9083008c4a603600980188e4002011802800413e0008000066003000000800800100006101aa03801b00100780000800010026000000004800c0063e2806c00000400300900060190be001c0cc0440419dd00120010000e78050030000806c08e00001b806033800800f009400e002028800016400418c805c0860010030120006001032804811e0cc00a05340080b00008004006004000176c04e015007000000e0e30028000000002001017001a00200201e008e05a000003455e031002828802600a006800401806d01a002002800d00a012800a00f02301dc00663d02181c4170011000800000605200000182ee4e01a480240b800e000002105400e028800018a0050000000006015008807400401d0108000000093024801c01a07b017800402608a0bb007003e00b0060004002000012011c000001000800828801001e80180000c200080000341dd043812404400003f013c21e0750030000080004008800000201f23503ec02000300184f000201000000000020010018020000006002000800206f00e001133600e007000005400500982480000fc00681105ca00000200d4e620111308034138011001b13c01a00846c819000826b076803c00000035f004808200d2ca003802e050001800c0b000104e000c000a0903b801801c00901f88d4000055016800001200000080851e800b5e3000000200301100040120b4005000c00c000003005827e000002800c002000015018c31200700d006c0be02101f80a8040023002809800810f0000010008002012800c000001000005400c00905e004400200b00716f40060260048010036004014829c00001200108e400000100100002920000238000088006003001000001300000183ac0240
  | 29 => 0x1400604800000b002401400580c8080005000234800a0d700c8000002094005000800400000f03841a4092008802800002c00400ec00000100a804800000700000040020030000010004009009807800203808701e40088b0022809c2c000d0018e44016003001801401e004012803000abe00c1001c00402e0008008092031002000c02c001003804400404100000240000230000000020005006000c0d60310028178048023006800002804c00100980020010010024152004002002802a006000000404c00521700181ea00200e8068066027000003400e005000008001a00300a8f640120280008280014007000000000000b002001048a000148000c0040543ac8124002c9a00080340260000008054000a5a001800000200702e800007800000100040022fb00205b4008020007003010418202d00240040da0000110052003013807800a063000000804409600007700b2002000016c00003426880200341b502501840b800500184b402a3c4013000830000002d006c0bc00600900ec4a200104680000180000020000000027018000cda800901c057822202801903b440e006001801400004900a80703d40b31d88000c200000040000db01a100d003406400f004030400800100680d800c00c005004c05447700e8014000005002000c40828f000000000201300d801409201d02f012c2fa0960fa800800000200104a400e02400b86052b60072f406bc022016000001813c0b90020048056000011008c5aa1030000130060008103048c042054002005000a03e002001440c0000300040016007001001c0da0330010024440001000000000c01300101a8014005003028403400e025002c00001401700004184da00780000a0000000000400010e0020b2402000001000000040000008030000026002802c00200d00300000000aa020000000203c076933000006400e06fc04c0330000040030054005800800057500100e40920000a7002c00e00001a008c06800d010802109a089010000000004300300000788c800280051e40023ed002804e0000029ed400c005003800800006f4780000008001039801c00001f004000000a009000013400018a002023842a008005822000800300782ac010006000000c138005000045001006d028000800e04b00a80141646cc000007002200200180ec0be00c05e002802822a0018c4801e01e00e000819200d000003002a02a00080940f2003001001401c023014000012e0580018100000117000809c00203f008008400c000009001001000001c804c000030011800000600100d06100e0000002801d41200a000000002400215c80640265b500581540000a00070078004000006800c01800000000582e00030080130000000190800802a0021ca860809a00100180a000003900a8008
  | 30 => 0x6001800802a02021a003600e17f010009000a19901c010c00200401f013800a003000007400800b00006dc000022004003400012001f000c0040080008004212341001014c01e00e094000c124008001805c00000000180c000a2a6004805c0580002ea803c00600000480e409e10703d800002601a07d8f9000c008000800c07e02b048000000a00001f0000030008006800000c0bc00e00001be005005801c6c47062ff81782ae0725a1800c0000e2000001802600200a00d0008001000007800078d00080240dc0010000008064141009029c00e04712280100860170098014006124049000439000000d80000700050040008004089000829805682b002002009c002003000837000d09f802802c01f00080000000000000d8c0020000000030002003000003803202b0708014162843
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xaad82997644c40153b08080c6a130eaba1843d893123ec6210e6a126400c3f7510d624408fd1864b1887900021fa1f655852021c5f43ea7b22620087e8710f6548025938e721ac48800393d4e53d89310970e392ca21864008ef825d943440010fb0bb92c39800aad20564505200964e3b0c721a8400a6e8510c624c4019aec7b8ac0a104b279cc43d89102e536c14e0b286443a9d831c3644c4090fd0bbb26290002a7a0c10d913214e363ae64b04643ec3c7590d608c80717908b88c69000e2fa13735891003d5741020b246400a9d83143644c8090f90abb464a00121f215760c9100043f438eab122000aad84980624c52f53b09baec6a100e3ba1f62509310972b98cc2b2e6047e4f2010d650c8014bb0a18ec6a10031719473591205bf174288631262008bd87083644c40153b0738ac9190022f6127650d200061f3a6cbb1a20038bc845d562440011db0e286c4988030f1d1654c7300946e41aeab1220cba6f825c5650c88f59d04080c6a101e3d219710c941006c63a0e498a6000a5c835d365440018becbb9ac8880028fe1f6510d2023ec7b98e89906412e8e635ca439080147d08382ca190029b6081059432095c6418e89906400c6c65dc96344001c3ce821aca190032bdd8744c83200637baee4b1a205bf898010c32480011df0eb20c4988023be097558d1000566c18a03126200a9d84d48635080f4d904b82ca1900317e1d7518d425e64fb98c8b026200ce472d85314c02543d09a1aca19002b320d621891003c76412e7b0282008df835d56244025958653b4869900387d067518d4260567c1ac8312623bc9c76191314c0051790eb228390002a720d64505200970f38aca2186400a6e8510f624c461938c9b9a8499003875515318d4066536c14e2b2864008ed878c3624c40f958c4ba4c4989a31b1db65509200043ec2ee0b1e4247e8c621cd425040153b07328c89901e9b2097159432006ca39ee2a1282019eb875c3324800157100b28c8988023b61c40189310046fc1aeab224212c9c7610c3244001b90e1b9a84900032bdd3625813100656b94e9b1a4000a9e831d7644c80f1d904b88c6a00032bd9372585300954f41aa831a80008bf845d5644c00156f02b28c8980022fa1c645893123e67b00e6a124000c5c75dcd644404f938c839a84900022fe117018d210064e3a0e6b122030a9e84d8e32440090fd0bbb2648810aa760c75d913001c5f426ebb1a4097a9d841c3635088f17f0eb1c87210030f5d7640c93123ec6420e6a164012c5d8710d650c84f53908a90c6a10030fd9574d8d20006cc386e6a1280018be86dd3325000159b07a96c49800eaba1b64509200945e43c86b122000c3d75d90324c14593ee6322c2980067aa02739092003c7743ee4b226200cd4611cd61480251790e31a84a08029761443d8d21
  | 1 => 0xec839a849896f639ce43909200054ec2ec621a40bdaae8610c624c4090f90abb4648804a37a0e76509104dec73b08619240078ee87100624c4018d8ea392c6880030f995748cb300970e21acb1966000c3c74d95314800147f0ab1c86880023be1d62189430962fbacea31a84008bf8758c434847d4790abb4869000237a1c63581424bd4ec20ebb1a8400c3f749d165cc00f1d904baac721002b360f54d893121d4ec1ee5b226214a5d83dd165cc12f53f06b9ac91900237e0d755912000557c22a7b126200d1d851cd42504015d100b2ec49880e2f21173d891000574402ca3126200aaf8254f644c0bb2d90cba864900035361473509205f557424c83126200a76811c1650c82587c86bacc6900062f219740c9400952f41ee8b2e600096d851cd42c813953d0c31886908031ddd47159120006563a6e4b1a20079af875ca43508018beebb9ac4880121f21570d8d420064f426e6b122000c3c7419562440015ad0332ec6a1002b560665d8d420946e41ae831a4000c3c751d1624412f53b0838ec6a100e3b60b75d8d420155b40ec8a0e6000ab681994644c80117f08b90c68800237a1c50d8d420062e3a8e6b222000a9e83041648c80153b0fb1886880030fd977458d1000567c12a631a840087e87195624400117b0e086c8990031d1c7655912000c5f436e898a8000c9c74dcd63484014db05b9eca8835ba310a6518d4224d56412c921a6249aae829c3644c80187eeb21ac1190021fe1570d8d210046fc3aca31a8404c5e7554c634840717f0eba6c69091e2fa1f644c9310074a308c898a6000d1d851cd4250001878ebb22c29811f279d86390d420243e42aed98a4000c3f75d91624c0014db0a21ec49884b87dd27518d420046fc1aeca1a2000aae82994644c40159b05180c69090aa760f72d913000636b90e5b2a2000ce4611c9614c12f59d04086c6a10029ba0a71597302145e43aa7b226000c5f751cd64480018d8ca392c88800317dd773591100054ec24e231a8400a5e85884635080117b0e286c8988032bdd062581311f45fc3aa6b246400cae74d8a624c40193ae831c64a08031b597724c7300062fb28e6b224000ace828c3635047d4790ab2486900029b60a30594320063a388cab224000a9d848806350801c3b093a8c6a10023b60b75d8d400070f214ea31a8428a6d821c1650c973c5b0a21ec498803275cc43d891001e5d3b0c99826000e1f845d4635080187ce8328c48811fa3d80430c9200051ec2821b2264128bc8718d415000717f0eba6c68804aa720d6490d215fe573b0c83126200c9e84dcd644402595e653b0869901eb32095398e4200656210eca1262008bd87d4d648c80195ee5396c8980f22f219748c9310961f21aea31a8400e1d75d8c434400193b09b9ac48811f2798d7598a434bf46316e6a128200
  | 2 => 0xd65582430054ec20a231a8412cd8635c032500254bb0f3a8c6a116f2bd897098a430043f43ecab224000c9d7410f634808555b05b1c869004b871d17518d4219e663b6e498a6047e8c621cd42500011df04baac6900021fa1f65591100061fb2ae83122000c5e65dcd42cc0671df04bb263900022f61f6310d200061e3a8c8b0a6047f0e7510c324802547d09a1acb98003331cf725891034d37410e9b2a40008be8710d6244001958e9b92c6908c2a7a1075d8d420243f43eeab1a4000ae581d4c624c425c38e2b28861932383e096510c3213d4f4262031a84008bf845d5624400117b0fb246498802b3a0e40189310062fba8e6b2220a2a9e8618c43440018baebb1864a08032b19372585301452ec18e0b286400a3e85041648c80147b0918acb9804b875c56510c3200536c1080b286400c3d751d7644c8015ab02280c6a100353a147350b200054fc1ae0b246400e1f6518c434800193cec21864880030f9957498b303d52ec1ce2b2e6000a9f845c4635088fb1f0839a85900032bdd3624c93123ec7ba0e6a164000c3d65dd132cc0018baea3aec6a10022f61376485300964e39ec8a166000e1f5394f644c879b2ce221c64988028f61272597300054e422a7b1a4212c9c841cd644400147b0a18ec898003351cf715912000672308e4b0a803cc9c761d1314c007179083b262a011f2b1c87458f202154ec18e3b226000d4f435d4324804fb2ec239a84a084a3720d7418d10004e641ae890e4012e1e70594430c80187aebaa6c89809ea7a122118d420065a3a0e2b1a4000a9c8350b60504014bb0b108c6a10028fa1431592320043ec3c43b2a4000ab581141648c87d878eb21ac48800e2fa1f7458f200070e3a086b286447e8c42884635080159904a9ec6a08b22f61f6390d4224d4ec18ebb2264008be87041648c8018decbb92629000387d976310d101f51f436cb21a2000a6d8510c624c4014bd0b10ec6a12ef33dcc62581310051f428e3b226000a3e841cb65440010f90cba864882df8b61443189310045fc22eca1a20008ed82dd763440018daca392639801e3e219700c94000557414c03226200a9d849d4635080147d0918aca19003a310f620c9102df47430861924012e1c4359531cc0018bae639eca880029721570d8d42586c7a08e6a164000a6d851d3624c4010fd0e32ac8900033354f764c8320061e3a8e8b1a2007cac72591438c80117d0fb22c498ae7a394c43d89310064e3a6e6b1a4000e1c6518c43480259390839ac8900031b197724c5200247bc3aa3b0a840099c835d062440014bb0720acb9800317d9473591100061e322ea19260028f687dc56448085958ed21a42900121f2157650d1000727a9ca63126200a3e85184644c18f53f08b18c6a08032dd9371589305bf47298863126200d1c745d4635080193
  | 3 => 0xca1a20008bf845db214c001968c9b8ac49811eaba0e43189310064e39eeab246427a9e84140635080195ee9b92c688002976166118d420061fb2ee89922026ccc761c9314c00147b09b9eca880032bdd274d89310147a40aeca1a400487e86dd56148001b188439ac2a104b875c96510c321ed1f436ca21a4000c9f641cd424c00155908b10c4988030fdd4645893000566412c631a2000e1c845d4635080117b0f18ec8980022fe117558d210054f418a1b226200c3f65dd132480018b8ebb9ac8900121fa1f755911000556422a7b126200d2c425d4635080155b04082c9190022fa1e30592324be2fb9acaa1864008bf845d5634400147d0b10ec89800327d0473591200970f42086b286468a6d82dcf654800117f08baac6900030f9d7640c9310243e42ae1b1a4200aad82980644c40f1d904baac8190030f1d7645813236ec639c86a164000a5e8504363508254bd0720acb980032ddd07158d2023f06412ca218640487c855d942440018bcecba8c6a100387195531913000667b98e4b22200087f855da43440011bb0e280c6a100327590735091023f27296a431a8400c3e65dd131cc0018b8ea31ac0a101e2fe1d6490f202df46c3086192405ad8f401cd4248001878cbba264900ceb920563cc9200046fc3ac631a40029b681dd332504018e8ebb8ac6880030fdd4745891003d37414e8b286400e1c43105650c801968e2322c09900339dc87158d2034e36396ca98a4000a9f85d8c434840f55d05b228598003271d3634c92000557c12cbb226227a9e8494063508018daea3aec4988ee2fa1b744c9300061e32ae9b1a2000a6d821d36544001c38ca318868804b27218735094103e56312e81928200e1c43d01650c80155b09386c4988038710c40594320045f438c8b126000ad581143635080f1790eb22848801f3a189700c9100054ec1ea9b22640087e8710f654400195ee8392c88804b2b0ca7610d3203d3741080b286400e1f6510e32440014bd0a18ec6a10a63be1d53189310047bc0aeab1a2012c9e7394f644c00f1dd05baec6a025ba3994430c92021d5a40ac721a4000a9c835d5648c80155b08286c4988022fe1173d81210051f42ce2b2464028dc835d942cc40147f0fb2886880021f617765052000727b2ec799240018ec825d563c800153d06282c9190123be1d52d89410045ec3843b226012a9e86d8c434800117d0fb22c09904b0710d7518d210047743881b126243a9d831d7644c44f53d09a90c6a1126ab2096390d100063bba8e2b1a40008be87d91624c0014bb0b10ec6a1002ab60a60191320046fc1aeca12200093d851cd415012f59f06b10c4a18028f61f6510d200043ec3887b2a406dd8c43dc1320c80187ce932cc59811f87d0843594320052f4282031a8400c9e739da434408fd18c421c649890a2f21
  | 4 => 0x50c8018becbb9ac29000363d9073509200954e41ac921e4212c3c435d764cc0010fd0e3aac88825f931cb43594320052ec1c82b286400aad84d4f624c40187887baac8880028f612715973000566c146031a84d5e8c42194635080717908b9ec090803879097518d4234536c10e9b2a4000c5c65dcd424407917d0fb2262980022fa1c50d913200566c14a031a8400c9f741cd624400117f0eb18868809f27d8073509400053dc02e2b2e6000ab581143644c4031d90cba242900031719773585200051f420e3b2a4000c7765dc56448001958c9b92c898803279ce7690d2003d37414e0b286400aac8454c624c48f17f0eb1c87900030f9d365d8d200051f420c3b2a4000c7775dc56448001878ea322c0988029761661d8d425d567c12c631a42028bd84dd7635040153f08a98c6a00063ea1f705891023f07902ca2186497a9d84dc7635080147b0810acb980022fe1d65191310945f41ee8b1a2000acd820436350801c3c20b288619002b36081018d420962f428e6b224230a9e841436350877938ec21a6298003721cf705092000536c1480b286400a9c8350b6150001e18853a8c6a10031d197715912000575c02cbb126200a9c835914244001968e9b8ac4880021fe157690d2024d5741461b226427a9e849d463508014bf0ab86c6a10030f9d065d8d205670f196ca21a4007acc8254d639080155b04282c9190063b209764c7200043fc2aed9922000c3f75d91604c4254bd07202ca190031b5d7620c93123f0e902ca2186400c3d75d53644c401c3d093a8c6a109b39185710c9200054ec1821b2264008bd84dd7634400f958eca128390002a760e75592320061e3aee8b1a20008ef87588624c4018b8ca39a84880022fa1c645813200637c12ea31a425aacd829c063508931790dba2c0990cf391c7624c93100c76c16ebb1a4000aac82597644c40f1b90ea9ac7210021fa1c755912001e563b486a124000a3e8408565cc00117f08baac8990021fa1c65591100061e21eeab22405287c86dd5624400f1d90ea98c49884aa720b6310d2023d4f416c621a20008bf845c4634814987ce7b2c86880031b5d7620c94123e46310e6a128200e4c825d4635080147b0830eca90002ab61050189310054e422c631a20078ec821d9314800117f08bb2648825f9394b52d8d420061fbac86b12206887c86dd5614800117b0f328c898802aba1270d893100c7a432e21922000abb80594644c4259390c39a84a00121f21570d8d415761f39ecb21a4000a5d8308565cc001c5ea5296c8988032b10876509100047bc0aeab1a4000c5d75d8e635007b4790ab1886900031b5d752d893100657ba0e4b2262d2acf825c46350801878c8ba864989272b18b744c9310046ec3821b1a8400c3c655d2324400155b09186c49890e2f21d62586430043fc2ae
  | 5 => 0x80c2a7a1071d8d4214636432ea1924000aad84d4c624c4014790ab82c9190021f617765091000c7c402eab224207a6e82841650c80159b05288c6a10038bd4a52d91300946e41aeab2064008be87191604c40187f08ba8c6a084a8761d6510c3213e4e320e6a1260018ec825d943c800f8d8c4ba8649884b2718d7090d4265636392e2b286442cb870d91434c0018baebb1864a00021fa1c31d95200054f42461b1a42018ef8758f32c800117f08b9ec2900062fe1d6490d3023f0e90aca21864008de87d8d605080147b0918eca900032719073591202de9621aea1924026ce4611c9314c0031d904bb4879000a2f21d64505200045f43821b2264038be87dd163484015d700b28c49884b1718d7598d4024d57410a1b226447ace8294063508018b8ea39ac488003331cc72591100064e320e6b222000a3d841cb65440018b8ca39ac4880062f61375d8d4000657b20e4b026200acc8254f6350151b1aea21864900121f216760c9100064fc1ae9b1a2000c3e75d90324c0258be60ba8c6a100297e0d74d951000657ba6e4b1a4212a9e83d924344001a3aea2186488126ab20953d91320970e43aca218640087d87d9432440d14db0438eca900039319463cc9200046fc1aec9922012e1e87594430c8031f100baac8988022fa1e43589100968e21aea1926247c9c761cd425000193ee621ac48810ead2056490d2000556c1461b2262008ef825c46350025c3ee8ba8c6a10062f219748c94001c5e422ea31a80428bc875896090c4fd18c839a849001e3ba1c50189310055742461b1262008be87d91614c0018d8cbb92c888003279d8438c91001d57426c4a1262029b7875c6435040153b09188c6a025b87194430c91000566c10a1b1a8469a6e82dcf654804f53d09388c6a10032b193725813107c5ec3ec721a8096e0c6510c324803d17b0fb1c86a08023b61e65189310051ec2c43b226000c7875dc163440090fd0bb92c39800e2fe1d74d8d201dd56412c621e4000c6c75d89604c40155b04286c898802a72116318d2001c5e422eab1a4200c3c751d163480b7b18e621a42900028fa1431d91306bf46214ec31a8412d1c435d4324c0851790fb226498003271d3634c9210054ec3ec621a4000e1f6554c644c12bd1c62320c498b371b1cb71594320043fc2aed19280008ed829d9315000717908bb26390002ada0450592320045fc22ec192206887e87887654800196887b8ac890002abe1165d893103c77416e6b0642008df8758c63508018becbb9ac4880022fa1c21d91300047bc0aeca122000c5c75d8d605080117d0e322c29904aa720d6490d200051ec3eca21a2000a3d85187644c001c3e82ba8c6a100e2f211764c9100051f424c2b2e600087d8710f654400337501ba662a004b17dc17518d42006c6218e498a6007a6c82dc16
  | 6 => 0x61e3a6cab122000a5d850406350801878e9b2ac2900c3331db735092063746214c231a8427c9c641cd424840195887b92c8988029b60a74597300243e42ae5b0a803da3c8558c434402593f0839ac488002b9205621894000566412c631a825ae8c4218d605080155b05328c8988030f2117518d410054ec18a0b246430acd82dc7635080155908b2ec4988ef279d8438c9300054e422c631a4212c3c435d4635052bd1c62218c4988022fa1c50d913100477438a1b126200d8c73d89425040193ce8baec6a111f278ca7690d3214d3642ac79924000c9e739da434847d4790ab1c869004a2f21c435891000556412cbb226000c9d87d8c434840155f08b10c4988030f1d0655852003e72312e21928200a3e84dcf654408fc3904b2886190c2b360870d8d4200537428e9b126200acc8254c635000159b07aa0c498813179d55318d410054f418ebb226200ccf73dc9644402553d0db1886908031b1977250d2003d5743486a164000a3d85041648c92bd1cc22186490003175d753d8d422dfc540086192405bf0e8510c3248001878ebba2c6900030f9d3651891000557c22a63126200e1c10594430c82533906ba4c5980c327193735093000557424603126212c5e8710d650c8251b906baac8908a29760f74594320061e3a6cab1a4012e1f71594430c82595eed39486a1003271cd75592320145fc3ac921a6200c9f401cd6448401938e831a6490003175d74318d2100c5f436e998a8007a6e828c1650c8011df04bb264880031b1d77258d2064d37c12e0b286400c3f75d91614c00153d073aac919002abe096310d10006563a6c49926200e1f81594430c80f4dd04382ca190023be1974487200061e32ee8b122000c3f75d51648c80187e80ba8c6a100e2fa1376487300047dc02eab1a20b9aaf8258e434842587ee8b2a87980021fe1576909104be4e3b6e6a1280008bd878c3644c48f17f0eb1c87908031d1d77158d2013e663b0e6a124000aac84594624c4010fd0e32ac29000327d9073509200951f42686b286400c6c75189604c44fb36c039a84a00030f1d06558d2018556c10e0b246400aaf84594624c40f1d904ba8c69000e2fa1f7458f2123f0f412ca2186400ad6811406350879d28c221a62980023b61c5018931006363a8e4b222000c3c75dd1624417355f04b18869080a3d205755912000557414e1b226212e1f87594430c861d18c9b9a849000e2fa1375d8d2100556c24603126200e1f10594430c825b18653b0869901e9b20974594320043f43820b286400a3d848c5650c8018decbb92c688002ab60a30592324bf46316e6a1280428bc875856090c015ad02286c6a110f2d1c76450d3121d5b408a1b22620487c855da43440018daeba96c498003661cf70509402145f43ea7b2260018ee86dc9314802553906b24868
  | 7 => 0x9d84884635080155d0d21a849000237e0d75591320051f42cc3b2264008ef825d5644c82599ca7bb26419002a7e0d65191320051fc2aed21a4000c6c651c9634412fc9e41a1aca190029761431d8d400070fa9ca6b246400a9f845c063508011db0f320c498802a76121018d420065bb26e2b0264008bf8758c434804f938c839a84988030fdd47458d101e7523088690a40008df835d9434854787ce7b2886880030f1d3654c91013e4f320e6a1220008bd84dd763484011bb0e286c6a10025b61473485204bec7396c721a8400a5e8598463508b7d1886b18649004aa720d6490f2000567418e1b126200c9e84dcd644840f1d904bb484988030f1d3654c9201e45f436e89926200c7765dc563480011df04baac8980028fe156310d2019d66c1ee9b126212e94635c6435040155f04a9ec89900317dd4735891000657b20e4b0a6000a9d83143644c4014bb0a086c6a1002e320d425052000637ba8e4b222000c75711c565cc00153908a98c6908030f1977458d200061fb2ee8b1a40bfe8d7310f624c40195ec9b9286990031bdd47258d1057e37b90cab1a4002ae686d852148025d30c6b8486a02b70f9cf6510d2000c5e422e7b028200d1c435d432504031bd0db9a849801e3b20975591105a64f3a2a7b1a4227a9e84d8c3244025938e7b2285988029b61770d89310056ac0cca31a8429a6e86d97324800717d0fba2c48800e2f21176c85300061f3a2cb1966000cd47118d605088fc3840b2886190032b9d3628c9310952f418e0b2864d3acf82594635080117f08bb28690802aba1020d89310051ec2460b2864008bd84dcd61c809355d06218c49884a2fa0f74589100147a40aeab1a4012a9e83d92434840f9c8c4b8864882d3279d953d9130006a621aea1924012c5c635d4325000193ce9b1c648804a3720d765091000657b94e5b226200c3f75d91604c80117b0f18ec8990021fe1572d8530006c6a00e6a124000c7465dc563481a759f04ba8c6a111f87e096510c320061e3a8c8b026430acd82dd76350801878e8b2a65981a71b1ca70594320064e21ae7b128207aae82d91424c47d47d0db2c869011f2798873509400070fa04ea31a8400a6e821d3654407d4790ab24868800e2fa1375d8d1000672396e2b2220cfa6f825d1650c99dc9ee5a1aca190028f61010594322145f43c63b226000e1e81594430c801c3b02b28861901e3ba0b75d8d4103c76412eca1a2000c3d741d36548001a9b0a39a85900028f61461191301357240ac61924047d8e7218e435080f1d904baac89801e3ba1f725911001c5f43ee8b1a4047e1d82594430c80117f08baac8988039918765485200068e21aea1928000c6f651c964440011df04bb2869080327e0d74d8d200243f43eeab1a2000a6d829c565cc00147f0abb486882c3a310863d81420
  | 8 => 0x9a9ec49890aab2097690f200062eb2ee6a166007d6b605d43248161b1e8039a85900023be1d62189300054fc22a631a8242a9c8654f644c025c3887182ca1909e6720d740c9410961e21aea31a4200c3f655d3634400117d0e322c2981262fe117650f2154ce641ae819240008ef8758862440011bf0eb18c68816f4b90d750c9200054f418e1b226200c3e74d96324400f17d0faa2c919002b36085018d420066a38ec6b02845bd8d8710c324800199ee6392c89884aa7a1b6310d100054ec1ea8b2464008bf87594644c0011dd0fb12c098ae7a3a0c43d89310145e432e8192823e93c855c26290c0187acaba4c5980031b1d77258d1001c5e422e431a2012a5c835d1650c801c3ea729ec8988021f61c10594320054f42463b1a4000aaf82594644c4090fd0bb82c7908023761e6518d4201476412eab1e4200c3f759d5648c89317f0eb18879010e2fe1f648c93155f46c16c621a4000a3e84041650c801938c839ac890802b360e40189310964e398c6a128000cac429d94244001c3b00b28861904a97a1343594320061eba8ebb2260128dc835d564480019a8e7b8ac4880021fa1c6558d100061f3a2cb3166000d4f651cd4248061938c9b9a849881f1b189750c94113cce41ae819280008de8718d615080117d0f18ac9190029720d74d95200055bc0ac921a4012a5e83905650c9a9d1884308c6a1002ae20165d91310051fc2ac921a2012c9c7318d41500b7e1b0a2186490002a76131018d420961f21aebb266000a9e831d7644c00163b0a318869084ba318e7290d422d566c14c031a8400a3d850c7644c9a599ee431ac2a111f63a1c430c92049746212c631a8400c3f75191614c001c3eca3188688003271d373589100066639ec4a126233acd831c3624c401968e3b22c4980028f61661d91320243f42eeca1a2000c3f75dd162440011ef02baac89810b271da434c53023f0f90aca2186412c5c7359542cc00147f08b9eca900023b60b75d8d410051fc2ac921a4000d8c421cd60508014bb06082ca190023be1d651893100cddc3ae121a8000cd7731c564480011ef02bb2648801e9ba0a405943200557424cbb1262038be849db324408555904b1c8790257a30c464189310043fc2aec192200087f855d943480018dee5392cb980028fa1661191322df4621ec619240008bf845d943480011bf06baac888002ade056310d200070f402ca2186400a9e839c1648c8010fb0e18eca9004a2f20f7458d1023ec739ce521a8400a5e859876350801878e832ac6880032710d73d89400043f438eab1a4000c3d655d232cc02587c86ba8c6a08036310b7358142006a6328e6a124000ccc73dc9644400195ae9b14649880e2f2117018d2124c5fc3ac621e42028ed82dd763484531df04baac7900038720f6510d1019c7643aa7b126200a
  | 9 => 0x30592320070f39eca21a4000c5c65dcd64480031f100baac690802ab209651913123e4e3b0871922000a9d848c46350801958c8392c8988021fa1f6558d100054f4246031a420087d85dd9434408fc98e421aca190031719773509200051f424e4b2e60078bc87551648c96fd1862218c4988023b61c40d893123dc6410c621a40038bc845d5634416fd1d06218c4988031bd9772591100945e43aa831a803d8bf8754f644c00117f08bb26390002a760f54d913100557424c1b126247d8c421cd424800153b06082c919002aba126518931006c63a0e498e60018be86dd1325007717d0dba262980023ee017558d210062fba8c6b028412e1e72594430c8018beca39a848800e2f210764c9400247bc3aa3b0a6400cb471191624c02587ee8b2a861904a97a0f74594320966a31ae219282aac6c721c1650c801998e7b92c89084b2720e7690d320062fb28e6a1240b6c9f761d131cc08fc388421aca190028fa1621d91320961e21aeb31a2000aae82997644c52f53b09b86c6a10032b19072585300056ac1ea3b0a6047e1f20594430c825c388718aca1911f631907350b201357340ea631262c1cae76d90624c4015cb02286c49880387dd0435943200656b92e9b1a40048ef8754b624c401c3f00b28861900a37a1b73509316852fc1ae8b286400c3f655d2324400195eedba264190028f21173d951000cf5406e99924000f0f6510c324802593886ba8c6908023760e76509100043f43ecab1a4000a3d8498565cc07d4790abb48688003651c7735094100746a9887b12623b8bc865d2324c0018d8ebb92c8880f3279d8438c9310062ebaae031a8447ccc621cd424c54d8eee232ac688003871097518d4203c77416ebb1a20338ef825cf6048401c5ea92a6c4988031b997724c7300043ec2eec98a4047ace82944635080156b0332ec8990031d1d471591200064f3a6ebb1a84008df8758c635040187ce832ec6880022f61f53d91315cf4621ec419262008bd849db324414fe18ca2186490002ab61021d894300556412ca32260078bc849da32500018b8ca39a84900031719773591100051f42460b2864008bd849d943440014db05082ca19003179d17518d4203d56412c8a12200087f855c363504018df04ba8c6a1003c31097518d420243e42aed2122047c9c621cd425040117b093b2869081f2b189748c93113d4f4244031a84038bc845d563c80011df0eb10c4a00038b1096550b30006563a0e4b1a20008df8758c63484011bb0e080c6a10066ea0374cc9400147a40aeab226012e1f70594430c8019cee438ac890002b920562189300954f436c721a8007aae86d89425058dd1887b1064a091e2fa1f644c9300952f41cc2b2e6000c9f7390d624400153f08a98c6a100335dcc7158d200045ec26ec90e6000a6e82dcf654400155d
  | 10 => 0xb2660bdaae86190624c40147b0b10ec89901e9ba0810594320062fbaec6b0284b5ccf761c931cc0010fd0f10acb980023be097558d210045f438a0b246400e1f6510c324400f55d05b2284900029760e405943200557420a1b1262008bd878c3644c84f53908ba8c6a10032b5d3629893162d4ec1cca3226230c9e87dcd648c825c3ee4b2886190033518f715814209657994ed21a64b3a9d83994644c0018deebb12c098802aba1260189310062e328e6b0a4047e1d4210d650c8011bf06bb28690002abe0965d91301f51e42ac721a2047d8f741cd424800155d05186c898a5e37e0d7650b3000657b26e498a6000c5c651cd64440dbb18e621a4390003275d0638c94003d57410e0b246400e1c80594430c80193d09b9ac89011fa31907350b206255743487b126200a5e859c763508871790dba2c098926ab2096490d100064fa10e6b222000c3c75d91624c00156902b2ec89810f271db744c53000572c08a03126247ace829c06350801c3887a0aca19002a7a0e71592320070fa9ca7b226000e1e75d8c43480014eb02382ca190121f215764c91000477c12e7b0282028be86dd1325042553d07b2486990028f21173d95205670e196ca21a40078be87d9142cc00155908b10c4880032d1d37158d2023f46398863126200e2c42d95424412dc9ee421aca19002abe096490d31004aec28e6a126012c9f841cd644800f8dec0ba8649000317d9773591200964fc20e6b222000c3c65dd1634400133906ba242a00030fdd77458d1023f47b98863126269e2c42d95424800153b07300c8990122fe1d54d912101c5f426e6b0642008bd87d4f644c8090f90abb6648800317d97735091023f473b0861924000e8d5310c624c40187eea322c09889ea7a105118d4201c5e422eab1a4000aad84997624c4514d90ab1864900038bd5254189310054ec20a031a840087e87d95624408fc3c42b28861910a2fe1f648c9300962ec28e6b224200ace83143624c4018becbb9a84900021fe15768c91000656320e4b2220008ef825d9424400187ecbba262900023de057650d200054ec2ec621a2000cac43dc964440251b9063b284980122fe1d54d913013672308e690a409bc9f73191624c00127f0ab84c5218063720d7650b3000537414e8b2e6000aad829c3644c801878cbba262900031b2097518d210045fc22e7b122000c6e651c931cc00159d05180c6a081e9ba0a71594320045fc22eab1e4000acf8254c6348401938e831a6490802a76127018d420049ec28e6a128097ccc62dcd424c4254bd0738acb980029761671d8d420043fc2ae5b0a8012a9e849d8635080147d0938acb98003879cf6510d100965621eec9906400aaf8258e434400147f0ab82c9190023ba1c625813123e56310e6a128200c6e75d88324c40187eea3a2c69001eaba0a
  | 11 => 0x5080193ec839a84990022f61f648c9300070eba086b28640487e85dd9434800147b0a38ec8980067aa0273c852000557420a031262048bf87553644c80717d09bb2429800387d017518d4203d57410a0b246400ab681997644c8090fd0bbb2848811eb3a0a1018d4219e7230ce690a40028bc865d232504011db0f180c498802ab60a60d91310051f42462b2e6012e1c70594430c8031dd0dba6649000327dd073591200961e21aeb31a4000ccf731c96344093c5ca5a96c8992df6310c724c73003c5fc3ac921a64128dc835d063484259390839ac8908034b10b755814201c5e422ec1922000c5c751cd644808f938c439a84a011f8790843594320065a326e2b026400c3f65dd1624400155f04b28c8990030f19574189100054ec246031a8249aae82043644c8012db0a39a849000a2fa1b74cc9410070e21c80b286400da442dc5605080139906ba242900032ddd37158d2000656320e4b0262128dc835d832440258b8c6ba864a084b0f10d7518d4203d57436c4a128000ab78158e434800193f06ba6c69089ea7a121018d420054f418a1b226496e8c6510c324806153d09baec6a1002a7e176310d100954f41ec921a40008bd87d8c43484018deebb92c8880032761f6310d100061fb2ee8b0a4000c9d7410f634400147d0a18ec89901e3ba0a764c5404bf46326e6a164000c3c65dd1614800117b0f328c89800317dd773591200243f43eeab046400c3f75191604c80f55d05b2285988022fa1f645813123d67410a031a8447f0d7510c324800153b07aa6c8982e7a3d886310d210964fc30e6a128000cac429d9424c40193ae821ec69091f63d907350b204bd67410e1b1a84a5c7b70195634400517d0fb2283980028fa1410d913223ec7c20e6a12403dc3c7510d608c88f59904ba8c6a1003871976310d101ec5fc3aa7b22623ec3c755956090c8f93cc439a84a084ba318d7290d420962e21aea31a4200c5f651cd61480019c8e5b8ac688002aba0a60d913100566412a631a82aaa6e86d943248001a3d0a39a84a080387e0f6510d100066bb9ee2b224000ace83140624c401a9d0a39a84900030fdd77458d2013476432e21924000d1e851cd42500031dd0db92869004b279cd53d913024e56396c8a1a6400a3f8558e43480018eeebb8ac69001eab2095359232006c6398c4a128200aad84994624c4018beca39ac48804b875c16510c320055bc0acbb226000e1c81594430c80f55d05b2284980ef669c0438c93000557426a63126200c3d65dd131cc0b5b1e8239a849004aa7a0b6310d2000657ba0e4b1a2012a5e8308565cc00153f08ba8c6a10030f5d475d91310047bc0aeab22403d8bc8754d648c80f1d904baac68810fa918643485200054ec20a1b1a8400ab581143644c80147b08382ca190eea721953191300245fc3aa9
  | 12 => 0x1e3b20975580320045ec24ed98a403da3e86d9443440011df0eb10c4a0803871976310d2023f46310871926000a9d83984644c80556d0db0a82a00023ee0175591310053742c43b128600a5f835d3654800193ee9b9ac4880121fa1b75589100962e41aea31a8400aad82043644c8251790e31a84a00ce3be1971ccb200946e41aeab222000cad64dc9438c8012df0fb2864900022f61f53d91300064fba0e6b222000a9f8454e639080f17f0eb24879091f72d80735092000656326e498a6047e1c21594430c8033d50139a429004b8710d6550c32006563a6e4b122000c3c65dd1324400153b09a9ec6a11272b1cb7458f2024c5f43ea7b22646ac6d72197634818559b07328c498802a760e70592320061e3a8c8b126012a5e83041650c8010ff0abb662900a31be19750c92013d4f424e031a8412c9c635c6435096553d06328c8980a23be1d53d89310061e422ea31a840487c855cb614c077958ec21a429004ba310f764c8320056a40ac631a40008df8758c635000187f08ba8c6a10063ba0b76507200043f438eab1a203d8bf8754f644c801c3cebb1886908030f5d754d91322165d3b6c99826000a3f8558c434409317f08bb287900030f5d074d95100046f43ec6b0a8412a5f875d4635092f938edb9a84a0802a7e0d71592320061fba886b046442c9c76d91314c00117d0e106c898802a761010d8d420043ec2eec99220048bf87553644c44f53d08080c6a1002ab60a70d91310970e3a4ea31a8400aad84083624c40195ec9b92c0988021fe1576509100243e42aeca1a40048df8754f63504011f700baac8908032ddd071591202de57b94ed21a40018bc865d121500010fb0bbb2869004b271cd6450b320055dc02cbb226212c3e435d4634840f17d0fb22859884a87e1d6510c320070e21c82b28647ca78805c565cc0018baeba98c6a10023be09755911019d73408a1b12625bd8c7390d424800153d09188c690257a3184430c9200043ec3c42b2e6000c5d731cf654817d55d0d218c49891f271d873509410054ec3ec621a4268c6c76d952148001958e9b12c0989a69ba0871d95200147c432e01922000c7475dc5644800117b093b2629004b271cc435891023e4f39ac921c6412c9c745d4635080517d0fb228298003875d76310d2034c3f438eab0464078ec825d5610c8510d90cba8649025eb3a0850d8d420054ec26a631a84008bd87994644c80155b08106c4a089f27d84735094100477c3ac619240008bf845d563c8401c3f07b2886900022fe11765091000557410a1b226200c6f75189604c40193b0fb188690002a7e176310d200051ec2cc23226400c74751c5634800f1d904baac8988028fe1173d95100064e3a6e6b1a2000aac8254f644c48717d0f186c898a7787194438c9100064fb20e6a124297ace82dd763
  | 13 => 0x716326caa1240b9e2e8510f624c40159d07aa0c4988028f616715923201c5f424ec98a4000e1c83d944348093958c5ba664a090aab60a7690d200147b43ee2b1a4000a3e848c7654800117d0fa9ac91911fe2d80430c92000656320e498a6047e1e20594430c80f1d904bb0648800393e097518d4200636baea5b128600c3c655d363480d1ad4e1b2e64900021fe1f650c91001c5f424ec9922012c9f861cd42504091bf0ea9ec690802ab20953d91300970ec3aca218640487c855da434808f55904b18868804b2710d7518d200054fc22a431a84008ef825d5644c42533906ba4c59880a2f21173d854000556c24c1b126212c9c329da434c8018b8cbb9ac488003171d773589101dd56c16c621a4000a9d84944635080156902b28c89801237e1d53d8d400053742c43b1260008bd84dcd60c840155f04b2486880028fa1373d95200054ec246031a840087f855d932440031db0fb18649011f2719073509320045ec24ec9922000c9f741cd64484010ff0ab86c6a101237e1d53d8d420964fc20e6b224230a9e840436350801b1885b9ac2a10032d1c764581320061e3a6cab1a2004c5e7554c6350801c3cebb18868827327dcc64589310061f32ee899660008be87d91614c8015ad03328c6a10062f21974c85400954f436c721a84498bc8754f644c8014d90ab10c49804aa7a1b6390d410061fba4e8b286400aad84087625004d5cd02280c498ae2a7e116318d4058e4f3b0c998a6000caf641c9314c00153d0638ec8980021fa1c6558d2001c5f426e6b0e4000c3c75d91604c40117b0e282c919003635007350b2000637b28e4b1a2000d0d7510c3248001c38853a8c6a10031d1c76558d2000c76412ed98e40038bc845cf614800159b06286c4988030fd017518d410064f3a0c719220008bd87d8c434400117b0e082c9190c2a7a1070d8d420946f4382031a84438bc8754f644c401c3ecbb1886900028f61071d9520006563a0c4b026204c3e75550635000155b05186c8990028f61373d95200243f42eeca0a4012cae43dd9320c8014dd0bb86c49890e2f21f644c9310243f43eeab12200487e87dd564481a34db053a2ca190025b614734872000557c12a6b246400ab581994644c88fb1eea21864902cb279d253d8d2100636412ea31a8412c9c435d4634400155f04b28c898002a76125018d42005c641a84a0e4000acd8284063508018bced3a8c6a11a31b9db65cc920006563b284a0a4012c9c841cd624400153f06baac9190063ba1a73485200964e398c6a128200cd4731c5644804f53d09288c6a111fa310b5218d421ee1e3a886b122000aad82143644c88fd186421ac1190031d1c46558d202d6c6320e6a124000ace83d53624c42587c86bacc6880022f61c50d913201c5e422eab1e4200caf74dc9644c40717d093b66290
  | 14 => 0x52f90100201901e07a07cc78030780b0078000240001680c1460bc150050ca790000020000003f006012034008f723e1400780b16a0183200b00001c59005000018000060000000000908c0040001d00a13c00000002002da0f9004004000100820503200107803c0212226a00ca803200a0046d84500003d6900c0a00ec0004b00a0000c803006000018071c807c028c55f2004058000820440e00200a0003c0070480040300700008c1800b0b407c5700009a4cc4681613a0880000800a0080980804a128090112a6000000310be0700082c0020080580c028011a80120000445d8d511a04cbe0340040001f15b0a600c078153b6020002a221c01c088000300900388b0160010900d1661a0028140000047f0c300c0c0258000340f8010010041e48500f000000398fe0140140201400000c0083601801c0780004a184260ed004018082030340000100901c00c00001004014148130000300b80104e0580883b0200006f0010000001880000e00c1d02d02824c168050248581f812084268000000160141900000204026ac501600007014062010078004720086f9a60022385582100c0202c035028094018000342346e8390c0044021110780708a83005800001004086000009790e8034000120240dc000be3fc0500486000602c0100007e0140000cce80000005b00c2b0020040082740d0050080140a80003c000db02f0104d0020070000341980504e000000000000180001b0000dd0700400a1d2e9800020088068011f40040c002010024090000060000180300000408000002080008003e68541300000007029008004344080040000700081200204000800074008000002a60000a00700a1b80002d000128398010260080400900a0f4018000220000180009e2680900000001c04816004010040810000260f00010c0fc2b00e0340780000a0004481f0080140481a80f0c2000150050200001500002a0ec0000002a51801803002000148170060b406805000034028020b24dc0122600c0043a80100200000805008020040000200240580e0140040b00c0000540080001a10c030001a402c0f84000433006813000000098000121341600000800406800022014020000260d40780f0040000180000000c040020360040a0000b43092001d0c600800800000028050002b1188008020180000b814af40e02101800000434000010000000050000100080002c04cfd00000001c0702500402049828016000e7803875d76310d210045ec26ebb1a40428bc87d91314c00117f0eb28c8990022f61373589100054ec2ec621a429ba9e8618c434808fd18c42186488002ada0450d91320056641ac43128200a3d850c5648c80155f04a9ec8988028fa1461d91300946f438a031a84008de87043635080717d0fba2c6880f2ad2056310d2000
  | 15 => 0x8008150020340162819e238550000580380001e0040080c80101e010010010ba0180881d00600428807004030008030cc0ac530ba008004000000000142801a00218c
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x9c560f925d0435943209507a5c10594430c8b750d985d4430c92009507a4f845d4635088fa0e8210e405943200607191851cd424c0db90c846147350b205668320a80594430c9bda0c826056510c322de4310d851cd2148001c0c435d7620c9410058564480594430c80106c9661473485206e583e4980594430c88f60c92e016510c320048725183041650c82581c86614735094036e4310d851cd21c81b3a0c822016510c324b5032597510c3248001c84421c4635814223d83a4a10594430c88f50e94d0d750c92023d8324980594430c80150f97d94430c9200041b259851cd424802541c97d017518d426df0310f825d4634840121d980416510c3256583a4b83d94434808fc0f605d4430c9200068310a85984635080121e980416510c3200507e5f6510c324400141d970416510c326df031d3825d4635088f60e920416510c32545432597510c32480b788c73a1a435092000607d94835d0624412bc846110c724c53009507a4f845d4635048f48c9754c431893123f03188435d4325040144c9661473509200960718d851cd425002509c9361276cc91070e8310a85884635082581c63614735054023d83a4a81594430c92d48f9754c43d893171d8364a7410d650c99d84c86d0d750c9202df42a017510c324808fd0b605d4430c9200960720d655d262cc001a0c4360840594326458364880594430c8b750f985d4430c92023ca324984144635088f88e861cf625094100703189851cd425048f60c926056510c327058364a81594430c92dc0c965d4430c9200050ba58425d4635088f28c926127518d4209607219851cd42505bb60d92a016510c320070318a851cd4250591c0f965d4430c9206d70310c825d4634842541e972016510c326cf03108651cd424800160d928416510c32006a110a81994635088f60c925d0435943200585a4480594430c80121c9361072d9510007031087518d6050801a0c4360a405943223ca3a4b85d8c43481b5c0c742097518d42006191c9811c1650c82521c9361272597305bf0310d651c931cc02541e979097518d420948724d841c1650c9c3a0c82e056510c3223d23a4b641cd424c08f60e92a016510c3209607a1175d0c6348401c0c6419473509202df426017510c32480b7a0c4360a305943200583249849d4635080181c6520d741891023d83a4a7410d650c85106c9760a105943200583a58429d4635080141c965d4430c91023e83a0843101650c80188c7620d425052023d23249641cd424402581e835d7640c9305cf0310d75d88324c5bf60f926056510c3200583a58425d4635088f28e92e176310d104b613218435d4324808f28c926127118d420050765c80594430c88f28c926131018d4200583a4b83d9443441b160e96d94430c92023d83a4880594430c80141e94e1d7518d42
  | 1 => 0x2013800a03691a05038e8900022a33c4c10a500d400140001b0a0c1dd0b9cb620c00400201c00908548f88c7620d42507205541ba5b87d94324800160d920416510c320948724d84041650c
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xc00900000000336240ea6e5f6510c3248001430d00e4c08e0b286400c03209972016510c32006019084b30a39a84900032048264480594430c92d10654325082ca2186400c0310c966147348520
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x5009b0210966147350920005201b0209912016510c32005009b0209972016510c32
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x94e
  | 6 => 0x94d
  | 7 => 0x3
  | 8 => 0x98a
  | 9 => 0x98d
  | 10 => 0x98e
  | 11 => 0x150a
  | 12 => 0x150d
  | 13 => 0x150e
  | 14 => 0x9ca
  | 15 => 0x9cd
  | 16 => 0x9ce
  | 17 => 0x168a
  | 18 => 0x4
  | 19 => 0x168d
  | 20 => 0x168e
  | 21 => 0xa0a
  | 22 => 0xa0e
  | 23 => 0xb09
  | 24 => 0xb0d
  | 25 => 0xb0e
  | 26 => 0x1549
  | 27 => 0x154d
  | 28 => 0x154e
  | 29 => 0xb49
  | 30 => 0xb4d
  | 31 => 0xb4e
  | 32 => 0x16c9
  | 33 => 0x16cd
  | 34 => 0x16ce
  | 35 => 0xb89
  | 36 => 0xb8e
  | 37 => 0x3c9
  | 38 => 0x3ca
  | 39 => 0x3cd
  | 40 => 0x3ce
  | 41 => 0x170e
  | 42 => 0xcc9
  | 43 => 0xcca
  | 44 => 0xccd
  | 45 => 0xcce
  | 46 => 0x15c9
  | 47 => 0x15ca
  | 48 => 0x15cd
  | 49 => 0x15ce
  | 50 => 0x1709
  | 51 => 0x170a
  | 52 => 0x170d
  | 53 => 0xd09
  | 54 => 0xd0a
  | 55 => 0xd0e
  | 56 => 0x1609
  | 57 => 0x160a
  | 58 => 0x160e
  | 59 => 0x589
  | 60 => 0x58a
  | 61 => 0x58e
  | 62 => 0x178e
  | 63 => 0xe89
  | 64 => 0xe8a
  | 65 => 0xe8e
  | 66 => 0x1789
  | 67 => 0x178a
  | 68 => 0x1409
  | 69 => 0x128a
  | 70 => 0x58956
  | 71 => 0x58b
  | 72 => 0x178956
  | 73 => 0x178b
  | 74 => 0x249
  | 75 => 0xca
  | 76 => 0x1449
  | 77 => 0x12ca
  | 78 => 0x1849
  | 79 => 0x1489
  | 80 => 0x180a
  | 81 => 0x130a
  | 82 => 0x14c9
  | 83 => 0x134a
  | 84 => 0x2c9
  | 85 => 0xb0996
  | 86 => 0x98b16
  | 87 => 0x154996
  | 88 => 0x99556
  | 89 => 0x209
  | 90 => 0x3c995
  | 91 => 0x98c
  | 92 => 0x3c996
  | 93 => 0x983d6
  | 94 => 0x170996
  | 95 => 0x99716
  | 96 => 0xd0996
  | 97 => 0x98d16
  | 98 => 0x160996
  | 99 => 0x99616
  | 100 => 0x409
  | 101 => 0x58996
  | 102 => 0x178996
  | 103 => 0x1889
  | 104 => 0x1649
  | 105 => 0x134b
  | 106 => 0x449
  | 107 => 0x150b16
  | 108 => 0x8a
  | 109 => 0x150c
  | 110 => 0x151716
  | 111 => 0x150d16
  | 112 => 0x8d
  | 113 => 0x59516
  | 114 => 0x179516
  | 115 => 0x1689d6
  | 116 => 0x9cb56
  | 117 => 0x9d6d6
  | 118 => 0x589d6
  | 119 => 0x1789d6
  | 120 => 0x18c9
  | 121 => 0xb5696
  | 122 => 0x168b56
  | 123 => 0x1696d6
  | 124 => 0xec9
  | 125 => 0xa0b96
  | 126 => 0x138d
  | 127 => 0x124d
  | 128 => 0xa0d16
  | 129 => 0x128d
  | 130 => 0x178a16
  | 131 => 0xa1796
  | 132 => 0xcd
  | 133 => 0x12cd
  | 134 => 0x58b16
  | 135 => 0x178b16
  | 136 => 0x188a
  | 137 => 0x59556
  | 138 => 0x179556
  | 139 => 0x58b56
  | 140 => 0x178b56
  | 141 => 0x18ca
  | 142 => 0x140d
  | 143 => 0x178b96
  | 144 => 0x24d
  | 145 => 0x144d
  | 146 => 0xcc3d5
  | 147 => 0xcc3d6
  | 148 => 0x583d1
  | 149 => 0x583d2
  | 150 => 0x583d6
  | 151 => 0x18cb
  | 152 => 0x58cd6
  | 153 => 0x178cd6
  | 154 => 0x1715d6
  | 155 => 0x595d1
  | 156 => 0x595d2
  | 157 => 0x595d6
  | 158 => 0x1795d6
  | 159 => 0x178d16
  | 160 => 0x179616
  | 161 => 0x178e96
  | 162 => 0x59451
  | 163 => 0x14d791
  | 164 => 0x14c591
  | 165 => 0x15692
  | 166 => 0x2d6d1
  | 167 => 0x583c99e
  | 168 => 0x58983de
  | 169 => 0x983d5
  | 170 => 0x14b
  | 171 => 0x15c591
  | 172 => 0x134593
  | 173 => 0x165791
  | 174 => 0x164591
  | 175 => 0x45711
  | 176 => 0x3d515
  | 177 => 0x58251
  | 178 => 0x17cd
  | 179 => 0x58ed1
  | 180 => 0xecd
  | 181 => 0x3c0d2
  | 182 => 0x580d2
  | 183 => 0x20c
  | 184 => 0x59791
  | 185 => 0x140c
  | 186 => 0x3d712
  | 187 => 0x3d2d2
  | 188 => 0x592d2
  | 189 => 0x3d792
  | 190 => 0x3c592
  | 191 => 0x59712
  | 192 => 0x3d8d2
  | 193 => 0x179712
  | 194 => 0x3ced2
  | 195 => 0x171792
  | 196 => 0x170592
  | 197 => 0x58ed2
  | 198 => 0x1403d5
  | 199 => 0x59792
  | 200 => 0x3c596
  | 201 => 0x3d296
  | 202 => 0xbcb
  | 203 => 0x3d416
  | 204 => 0x3cb16
  | 205 => 0x19cb
  | 206 => 0x18c3d6
  | 207 => 0x3d896
  | 208 => 0x3d8d6
  | 209 => 0x3cd16
  | 210 => 0x3d415
  | 211 => 0x3da15
  | 212 => 0x203d5
  | 213 => 0x443d5
  | 214 => 0x1a03d5
  | 215 => 0x15c3d5
  | 216 => 0x58153
  | 217 => 0x14593
  | 218 => 0x44c
  | 219 => 0x1a0c
  | 220 => 0x3c5929e
  | 221 => 0x3c5899e
  | 222 => 0xbc593
  | 223 => 0x3c5941e
  | 224 => 0x3c58b1e
  | 225 => 0x19c593
  | 226 => 0x583d89e
  | 227 => 0x583cd1e
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1836
  | 6 => 4743
  | 5 => 1961
  | 4 => 121
  | 3 => 7
  | 2 => 3
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
  | 2 => packedAt gbK2 (i*92) 83
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
  | 2 => gbHint (packedAt gbK2 (i*92+83) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/27+packedAt gbK8 (1612+(h % 27)*6) 6) % 62)
  | 7 => 2*((h/619+packedAt gbK7 (67932+(h % 619)*11) 11) % 1836)
  | 6 => 2*((h/1581+packedAt gbK6 (227664+(h % 1581)*13) 13) % 4743)
  | 5 => 2*((h/702+packedAt gbK5 (115699+(h % 702)*11) 11) % 1961)
  | 4 => 2*((h/47+packedAt gbK4 (8470+(h % 47)*7) 7) % 121)
  | 3 => 2*((h/23+packedAt gbK3 (567+(h % 23)*3) 3) % 7)
  | 2 => 2*((h/1+packedAt gbK2 (276+(h % 1)*2) 2) % 3)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffe07e01f01fffff03fffff023e78fa07f1ff
  | 1 => 0xf807f8001ffe0fffffc1ffff1dc9a72438fe3f
  | 2 => 0x7ffffe0000f81fffe1f00e1f1c7c7c0cfcc
  | 3 => 0x7fffffffff001ffffe000fe01f807ff0ff0
  | 4 => 0x7fffffffffffe00000000fffe0007fff000
  | 5 => 0xfff800000000000000000000fffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8720161050092925012292a0012084a0350d5
  | 1 => 0xd08458020a720564a64152d40cc8a32418a62a
  | 2 => 0x116aaaf201089b13ab41c06617145c6c0cb4c
  | 3 => 0x422134d453a52001cd298018b601f8016d0db0
  | 4 => 0x8447c71b9cd9ce7802101860dbfe0007b6f000
  | 5 => 0xe780001c00e100400c210080ffadf6b0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeaeafe88e888feeaeaeafe88e888feeaeaeafe88e888feeaeaeafe88e888feeaeaeafe88e888feeaeaeafe88e888feeaeaeafe88e888feeaeaeafe88e888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40203
namespace PEqualNP.Outside.L_meta_40203
open PEqualNP.Outside.L_meta_40203.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 9 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 50 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 40 := block_range (n:=40) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 136 := (concat bs0_4_0 bs0_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 48 := bs0_5_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 8 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 9 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 6 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 6 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 90 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 44 := bs4_5_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 14 := bs5_2_0
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
theorem bgb_2_0 : Interval gbAtlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 3 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 7 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 121 := (concat bgb_4_0 bgb_4_96)
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
theorem bgb_5_1920 : Interval gbAtlas 5 1920 41 := block_range (n:=41) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1961 := (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 bgb_5_576) (concat bgb_5_672 (concat bgb_5_768 bgb_5_864)))) (concat (concat (concat bgb_5_960 bgb_5_1056) (concat bgb_5_1152 (concat bgb_5_1248 bgb_5_1344))) (concat (concat bgb_5_1440 (concat bgb_5_1536 bgb_5_1632)) (concat bgb_5_1728 (concat bgb_5_1824 bgb_5_1920)))))
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
theorem bgb_6_4704 : Interval gbAtlas 6 4704 39 := block_range (n:=39) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4743 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat bgb_6_864 (concat bgb_6_960 bgb_6_1056)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344)) (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632))) (concat (concat bgb_6_1728 (concat bgb_6_1824 bgb_6_1920)) (concat (concat bgb_6_2016 bgb_6_2112) (concat bgb_6_2208 bgb_6_2304))))) (concat (concat (concat (concat bgb_6_2400 (concat bgb_6_2496 bgb_6_2592)) (concat bgb_6_2688 (concat bgb_6_2784 bgb_6_2880))) (concat (concat bgb_6_2976 (concat bgb_6_3072 bgb_6_3168)) (concat bgb_6_3264 (concat bgb_6_3360 bgb_6_3456)))) (concat (concat (concat bgb_6_3552 (concat bgb_6_3648 bgb_6_3744)) (concat bgb_6_3840 (concat bgb_6_3936 bgb_6_4032))) (concat (concat bgb_6_4128 (concat bgb_6_4224 bgb_6_4320)) (concat (concat bgb_6_4416 bgb_6_4512) (concat bgb_6_4608 bgb_6_4704))))))
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
theorem bgb_7_1824 : Interval gbAtlas 7 1824 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1836 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 bgb_7_576) (concat bgb_7_672 (concat bgb_7_768 bgb_7_864)))) (concat (concat (concat bgb_7_960 bgb_7_1056) (concat bgb_7_1152 (concat bgb_7_1248 bgb_7_1344))) (concat (concat bgb_7_1440 bgb_7_1536) (concat bgb_7_1632 (concat bgb_7_1728 bgb_7_1824)))))
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
  · exact allgb_2 i (by omega) hi
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 34, 38),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 9, 25)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeaeafe88e888feeaeaeafe88e888feeaeaeafe88e888feeaeaeafe88e888feeaeaeafe88e888feeaeaeafe88e888feeaeaeafe88e888feeaeaeafe88e888
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 24 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808426 * 2 ^ 32 + 4270385288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40203.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.or,[2,6]⟩,⟨.or,[3,5]⟩,⟨.and,[7,8]⟩,⟨.or,[0,9]⟩,⟨.and,[2,6]⟩,⟨.or,[5,9]⟩,⟨.and,[0,12]⟩,⟨.or,[11,13]⟩,⟨.or,[1,14]⟩,⟨.and,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4270385288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4270385288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40203

open PEqualNP.Outside.L_meta_40203 in
theorem PEqualNP.Outside.L_meta_40203 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4270385288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4270385288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
