import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40425.Model
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


end PEqualNP.Outside.L_meta_40425.Model

namespace PEqualNP.Outside.L_meta_40425
open PEqualNP.Outside.L_meta_40425.Model
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

def SBf (j : Nat) : Nat := [6, 7, 8, 6, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_40425

namespace PEqualNP.Outside.L_meta_40425
open PEqualNP.Outside.L_meta_40425.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x2000000000210b20020230df30be42de32be40dc32dd30bc42bd41de31dc31bc40bf41
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xa00006000040000138505071884194b14941a6292614e528c6a8a2984b94a40
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
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/25+packedAt s0K4 (192+(h % 25)*4) 4) % 12)
  | 3 => 2*((h/23+packedAt s0K3 (189+(h % 23)*3) 3) % 7)
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
end PEqualNP.Outside.L_meta_40425
namespace PEqualNP.Outside.L_meta_40425
open PEqualNP.Outside.L_meta_40425.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x20000071a0000001c310000810000300200028600200fff32fe40fc20bd41bd43fc10bc40bf43ff31ff20ff42fe43ff41fc32fd40bc42fd21fc30fd42fc40be40fd30fe20fd43fd41fe42be42fd20ff30fc42ff43fe21fe30fe10fe41fe31ff10fd10ff21bf41fc41ff40fc31fe32fd32fc21fc43fd31
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x48006898002c341030008cd8dc600c4c01f804142c74add42000280010004c08000400040404802c0c3404d05000343801b444000000303c7806dea4a0cf552419eaa6613d54cc6eaa2184f54f41afa9a21af525067ca821cf55131dd280813e544c6dea4884f55031d6a94815c534827ea9194f950219f2a4413c548427aa7204f550329f286876e529027aa8184f552219faa0413f548427aa6205bd49309ea88855d5304278a4a1f54c431af298216d52042dca4084fd51329f294853e501027ca5204f950319f296833e52d0ed8a4a1db149109ea8c812c52506daa5204fd5321bba8a415e538867ca8194f950109fa8a8776510c27aa918cfd51109f2a6613f544867ca820db548309eaa4413e5010adea4a1cf553109f28485ac5250e7ca1a0cf150209eaa4873e54c8278a0a0d7d4d209eaa6659f5350f5885904f952219e2a2212e529035ea4a1cf141439ea88815d538867ca4204f151209f284815c53442eea2985b14930d621443ac52506eca3995b54b319e2a2613d540867aa9906b10920d6216653e548c6e8a2905b149419e292833f544c3588410cfd52309ea8c856d528c678a990cf95331dba8a837551cca78a8994fd5120d7290853d5390a7aa3a1cf55010d6210653f5350678a9194f54c429f290853e54c4258a4a1cf950309f2a6656e52cc678a9185d145309e2a2436e520c35ca5205b94a31
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xe40002508c051002000012009608d584548ca2c62551318b189511022c6255031c910a51cca2c6254c408758c54c872442145208b98a50d062c6255330a358c420ca2d65108328b98b548423860551318b98b540822c62553108758c540830e5310a21a9584420870c53109208b98b548c22e62943438b18951d0e2d65108218d584540822c6254f41
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s1K5 (768+(h % 30)*6) 6) % 48)
  | 4 => 2*((h/58+packedAt s1K4 (3618+(h % 58)*8) 8) % 134)
  | 3 => 2*((h/22+packedAt s1K3 (988+(h % 22)*5) 5) % 26)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 2 => 0xe0ffffc0fe0fffff0783e0fffe1e07ffd23e4f
  | 3 => 0xff03ffff000fc1fff803ff07ffe00781e3cf8c
  | 4 => 0x3fffffff001fffffc0007fffff801fc0ff0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x20080888240200002904a108802290a404d095
  | 2 => 0x4a3191064894b0cb02a148d332142558d2264a
  | 3 => 0x865aa2921d29135558427a45d540560d634b8c
  | 4 => 0x14a344249181a5a694e8108669996011b80d60
  | 5 => 0x18c38738e1ce39f8e7739ce071118461ffb000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0faaaaaa0faaaa0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40425
namespace PEqualNP.Outside.L_meta_40425
open PEqualNP.Outside.L_meta_40425.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x120080118002646844091402800c00c0fd31fd40ff41fe31fc32fd32fe21fd21dc30fe41ff43fe32de30ff40fe40ff42fc31fc40fe10fc10fe43fc42ff32ff20fe20ff21fd42fd20fc20fc43ff30fd43ff10fc21fe42fd41fe30fd30fd10fc30ff31fc41
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0xa85f631c42faa8887d10410bea8e877f54887dca598df54632fd98461bf4310bdc64905dd4520bfa9221de30083f260187d4c421fd904417d5110bba6498fbd0a32bf29c81dd4310efca70877c8630be2a4417d52cc2fca8907bd0a20be28a617e5090afaa2185f14121beaa4417d548427ca998df14910bf2a041de30c42faa4885f94220bf28c635e53106fca7a07dd0410bea8887ec424cbec6390f554430dea18857e510437c82a0d714d40bfa9a437e52102fca410f790c30bf280857f52503e842085bd4940be292617f52842f8a498f394830bf2a061745150afaa9985f54f20bfa8a41be41102fca010df54242b7a9283bf43502fca6086f50e42bea8e65dd520c2fca8207b90842fa98e43ed20083ba43185fd49439faa243dd420c3f4401077d0230bf29c43fb40903ea63885f14542be2a0635e500c2faa5a07b88620f699043f541107bca0187754f20bea8685dd438c2dea4885f14c10dfa0481df310c2fca2197b8c832bf284617e53c83bc64185f15021beaa4877d52886f8a4085f55021aea98837f52042fca021f7cc030fa28a419e540c3baa5186f55030ee208617d53886faa8197bd4941bfaa621f721043ee20085f94841eea9e21bd4210bda65907754c42b629221ef20883be65197dd0541deaa663de53c82faa61077d4a30bf28443bc42106dca521efd0c43af298857f53c43dea488770c320ba28a41be4350fb842187354830bf2a6637f53c86fea6a05fd5121bf294217d5010fbe82187b54b31bf29865df4350feaa321df94f41bf28643df53482f8a9885f14e10efa18617e5190bd8a4885d94430ef996637d528c2faa1a0db14940ef99461dc53502faa990efd0040bfa9621dc30842f8a2905fd4d41bfa9c41de30482fca7a15f94740beaa241de410c3bca610fed0140ae29a415d53087ba6598f78c630bea98857d540c7eea2a157d4d20bea9441dc53482fea0995d94643ef29e817d538c35a84215f14540bfa82837c540437a86a05dd4540f6214437e50d0bbe64185f94231bea94217d528c7b863185f15030bea8043f551ccafaa1996f95332fb208837f54042fca218770c020fb28c877e54c87de84a15f94b30dea1887f621086faa521fe44010dfa18837d54042faa418efd0441bf290877f540867ca99977544309eaa0617e50102b8a6885f54d10ef908617d548c7b861885f94a43be29e217e51d0efca598df14c20ef2a0617f548cafea2a05f94a41be2a641de30442f8a998f790d31fb28e657c544cafca2105f54730bfaa2657551ccafea8187d8c510fb90c43dc328c3be6318dfd5332efa00617f540c6faa3087b08620bf28c877e54486fca218f714d10bfaa263de434cbbe6218df94910be29a437d54c82faa899774c630ee994617e5210bbc60987bd0821aea9e817c5050efaa1195f94d10
  | 1 => 0xd52cc7b864185794f20be29a833d54cc6bca1185f54c40ee290617d5490bbe85186fd5110ceaa0617d52d06faa5885f54640fba8a817e53883bca5185f54b43bf28c417e50083b881186f50e41af298437d54903ba81185f14543bea84837d54906fca12077d5030be2a263fb20482f8a9985f55232fd20081f741c87ee4290d7d4d40deaa665bf54482fca5185f15110ee182217f5350afca8217d14542de2a241de310c2fca620ef90840f710a43ee32c837e85215f54c21ee980617e50d06fca6107b94830bf284837d50cc7be83186f50f40be282837d53487dc6410fdc4210bf2a621ee20482f8a990df94d21b6a9663dc438c3b862187dc8610ef2a4617c504ca7ea89077d4d40fca0081de218c2f8a7105b94830aea98857d51083bca7885f943319eaa665dd310c3ba64185f55130beaa2637e540cbeca218778c531bea9883be540c2f8a4a07bc8020be2a6657e54042fca3905f95220bfa8a653c54483baa620df54243bf290617f548c6fea918770c010ef21c617f54442fea998df94030fa90843dc430c2f8a710df95230bf2a4217d53c86fea2a1f7cc832bf29621ed520c3bc80185f94e43bf29885be41903baa8185f54620efa1061dc518c2f8a910dd54643f7a1443dd43cc6f8a610f78ca30bfaa2617f53087f660987b08420ef992637f54083b885185fd5032bf29c85ef424cbbc8798f7d4830fc900417c548c6fca5215dd4542de21481de420c2fca9196f50040be282857e511037c8420db54830bf298877f53042f8a890fbc8421beaa243f4418c6fca3205f94742beaa4437d5190afca9905f55331eea8c617f5150afaa321df94a40bea8c617d53842fca310dfd4d20faa88617d520c3dca521df94d20be2a421df438c2faa420efd5121f2908437d54cca7ca8185fd4930ef984617e53c86fca89877d5230eea1461df318c2fca3197b14941bf298617d53d0abea6885f54840bea98217f54cc37e8721df94831bea8e41df4390efca618f710630bfaa421f7318c7b861105f95041bfa82877f54482faa2207794830ef18641ec42883da4210ef10640eea0861be4250af8a6885f54a41bea9c817e53102fca1a1fb54a43bf280217f5050afaa1a1fec4110bf28c617d53d03ba80185f54231ef108617d5010bb4a0187754c21bf2a265dc400c2faa020df14131de208817e500caf8a6905f15032bf290417c514caf8a8906fd0842de210817451503b884185f54d20be29e41b541107bea6887dd0631ee2a461dc218c3f420085f94c21f7a14857d50887e88298f74c832bf2a0877d53c42bca7885fd4121ef20c617c548c2fea990f74c431dfa1c857d51d0bbc61087d8c421f699443dd53d02faa0196f50441bf28883de518c37c8520dfd5320bf2808375510c2f8a8107bcca32bfa9283f610443eea2907dd0531be29
  | 2 => 0x4c42800360000103c0097a35002018120c85e00000990040084e0582408870002e6598322200002a222700408b5402102590004380c000020008c0480604810148040c95405802001600b00405012251a4128b0558041a002078000780202a100dc96038a600000600e6390000d8047823006006000080680a0014a0100c0d8d61182a008000303c9a00e0380c0000c038cc0c012008340e8000a8a04b1aa0082c018200002401814228282e0801300e1bb860080c010220000a0a028114500186a000000283e5d0240601e0005203812020000302a0280c000360e0204a8761301044812990029c0420014263022048060a88c0080e0f0000c8080580a0400a000001901a340840b800058e42783e0004e000021001000010018002c89e77238058080001e010001f17c0000601008008200003e0012a0100a000c25cdf54a40ee28861de4310fbaa9187d8c431bf29465de428c3ba42186fd0641bb28e65de53106daa521f750c30ef29885bf43906baa7887d4c510be292837e53907ea6218fb50842bea9087de43ccafaa718df55310b7296637e5444378a890dfd4d10bea86437e54086faa2197714a30ef180217f53c82bca7a07b8ca21bf2a661f441086faa018dfd5220efa8c617e52042fca7885f14943bf288437f53082fca518df54e32bfa9c217e548c7de84105f94210bfa92637e51ccbea20087e8c030f699065bc42906faa9185fd4e21bf296837e51907bc81185f94b43f699241d6510c3ba83184f15110bea9c41ef52503ba8698df94443bf2a263bf43d03ee8210fd10610be2a465ef324cbee6298df54e42f621043be42903ba87995f15130bf28e617e500c6baa7905f55030fd884217d51d02fca1197b10a32bfa8a61de324cafaa4085f94243bf29065bd43107e843085f14b10bea9e837f504c6faa720f70c120de2a2217c52843dc42107dd0641eea1a65f441c87d8a4a05f95332bf2a4436c525067ea8887dd0610bf29681de510c37c80a07715030efa8861de30882fca2215f95031beaa041ef21886fca1997d14540be29a813c544877ca998fb10820be29e437
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xa53c82d66114430b6181410c32c5488521f294a500c25e63d5320d5551510c26c6255010c715030443c5525443097994428c29d64cc630c798e54cca5e6394640a7593324c65e63951209718d509066d6294f409dd8554083665254430b6980528c26f6254d10cbd0e5290f2f5410a208f990530826d6214e10f254a500c32d4314940cb54842106ad6490842add9541106d56190f32d598653d025e65084308f191528c364524c5109798f54086b564904418f992534867661d5220a7593310c23d6595030a7d91518c23e6495121ab1814210a3f6454910e5504410c25d63d414297d8d544832d5494b31b398a438c25f63543218f592524427761551309d185544c31d54cc430d354f420871e5450f318f99352c43c65254430b9185200829d6595030a7191210c2b46150842a7990520c2d661cca30d398a53c423d6494f108f191520429d64d44309d984540c2d461500309d98653482756510410d5546500c23e6494d208f191524434e534cb209dd95310c63d6414e109798e529029d64ccb319d185544ca3d64d4a10d358a531066d62d50319bd954210ad6611503097d8d544c3355494732d1549510c25d63d41219b588540429f64486309d98653d032f54d4910ab18940103556194f20b6d81420c2746154840d514630482cf62502309d58453882ce62cc6309b18951103374394643cb14a415065e6315032d3d4a304425e6094c418f191518c3a76250441a7590510c25e6510830b6983548c2e661cc932c7d52304826c6255110d94c8514825d6314941d3d4f52502d561d48309758c54486ac6250441f4546500c25c63542219bd89544c3a461508429d984530426e62949109d185534826d6294c41d5d49510c25d63d4b109b988530823d6414f21d55865310a5d63145428fd91528c6e56348421b9991210865d63d41418f99053883645284110b5d85428c29e64cc630c798c54486f0604c510d3148304423d6414c10b358b510c26f6255231b5986438c31e5450f32cb550424cace62148309d984540827b6055132ad993314c6da60150309b195324825c6354341c7d50304429e64d4830d5d46304834d52cc430c7d53534826f62552309758e52083a46448421b3596520c2d661cc931ba181324825c6054c218f994544426c6255131b5986434c7645214540c759253c426f6254041ab191210863c6454632b398b510c25e6014d10cd152314423d6494c3197594410c2756194d219798c548875a6094030cb15220482766195120d914b41506746155020d5d4c51483a462504419e580540865d6394a10d558c5150b1c5414d10b5d85528c2776154b439b98854042da60144309b189548c66e6214e108fd95411072f5410a21b5d85408c27561d5032d5d4f515026d62d5030a7590520c2da60d50308f59053083665294643
  | 1 => 0x434d53108219798c54c431c540c120cb550420865e6394d10d394932cc65e63949109799430482cd6290e30a7990540c2cd6310a2197d8d5010b676548421c755332cc67661d5030d314f525032d54548309b189518c38e5350842b3988510c26e62d5331b9d95210866f6255110b5987520c33554944309dd85521031d63151219798e518823d6414810c7551510c23e6494f208fd91534826c6254041d354a320c2776544010ad993318c71c548c110e3552520c32d5494830e594d41106cc6255230d9d4b515027761552309d185548c31e5450c309b98a53d031e5350f409dd855010a9c6454a30c7551310c29d64cc830c715053483655254430b5587328c25f63549108fd9153486e462504419d58754ccb4d6294f40d5d51510c33743145408f19153486b46250441d550d51ccb8d4210a308f592534866f62551318fd954310f9541106308fd954210a5e650c1109758f54c825c6354041b558c410874d524c43097594430c356514c4309d586544831d5494030d390d520c3665294430b358a434c676611533297594428c2d46150230d5cc9510c25d6314810d9d4851503554354430a7191218c32c54d4910c799253086776155132b6983510c35453d45409b58b54c425c63542429b98b54c425c6355110b3588540c25d6394910c7553430c2776154d20c3551520c25e6395210c799253c423f6454a309798f505063e64148109bd95320cad661d5030ad5844210757531454097195434cab66190d43d3d4f524435765544309ed95200825d65d00309bd9521086e460484219e98054086af6550842b6983518c36451881209b58a53487c65294430e6552500c27561150209758f54c427661d5330d590d51ccb1e5350c419b98a54442cd62cc4309798e548831d54d4830add8d411063d6414e219d58754cc3355454430e9108410874d525443097d954310f655294430f194d21087565194030b6181420c26d62d53319d185528c23f6550040cbd954210a5e6508630b5584540c32c52901409b98854cc72f5414910f154a510c36552946439798e528425c6550d31a7191518c25e63d414297d95310c7566194c42d314a30442e5618c821d9548210434d52940309dd85544827860551319758f54087c55348421e5551510c25f6354341c5551510c3564354430a7593328c25e6510430ad191210866e6294f109d58754c834e52940309b98b540cb8d42108309d584530832e5454b31cd55151ccad56190d329799453443566194f20d314c525026d6215030b358a430c27561153329d185548ca5d6395130f40c1100433454841108f99254442d461552309b98b54843d25194030b5584520c2746154042b3d89548c26e65d09329b189548c23f6454021cd151314431f548c1109b98b54cc3a76150842d514e31442756115030d398
  | 2 => 0x5310841d354b510c25e658c1209d587540c2776154a30979825310a5d6315321b9191210876742145428f992524425c6014d10c798e54cc74e6294c42ab58b4310a5e6094c219758c54c834e534c821e354d4210a3e6414e21d554c410863c6454a31d358a53c433554104219ed81544c78e5454830d558653d02776155110a7993310c31c548c12097594420c34f6554830d9d48218425d6394410e554d411071e5494030cb550428cb1e6494f209e181544cad761500309dd95411072c544c920c7153534435453d4520b9588410871c53d0d40d390d52cc7566194c219b98a534431f5414d109798c54c823e6494c319798c52507954310531cd50c51502756194c42b3d89518c23d6494f209d594410873554104109bd89544865e6394d209799630442b46444010b3189518c2e561108219bd8951102ce62d50309b98b540c26d6214c1097994418c34c538c920b6980518c39a54940308fd91518cab46050441c759253086cf62504308f592530cb4d6314941b358a43cc7a76448421cb55152cc65d650863097594210c23c64540219798c52042cd6214430b6980548c25e63d4121c7553320c2756194d20d3949320c2a46150842ad185401033654947329798e510433754106109798c544863e6494c32c715353482cd6310821b5185420c26d62951109d997414c73654544309758c540866c6254743d594d31c42ae64cca32b91854210b5553d0421b3189400c31d544cb31b5586430c25f63551109dd95210866d65108208f99253086756194f40b5d85548c31e5350c42d398a531065f6354342e5951510c23e6494d10c798e540c3556114d10b998b318c66d62153318f59352c429d64d4830cd150514823e6414f219d98754c834d43548308f590538833754107219b98a531074d5454830b9d8d21086e5628c421d5549510c2766114e20e5552510c36452d4540cb548421026d651082197596530872d5410820a7d91528c2b86050d409ed95100438d5454830d3d4c524434c53d4910d594d310865d6394620b3189410c25d63150209758c54c423c6454d10b358b318c26f6254743b398c424cae56288421a7993320c2d86048430f14c931086746154b438f990538434f5454830d398a530866c62551308f993528425c63540219798c540865d6394a408fd91510831d53908419b988540c2af6350842b5587320c2ce62150309d587548823e6495120cd153514825d6395120d398a53d02ce6290d32f1484210c25e63951108f99253c423e6415030cd550414c72c5414910b5185528c2b561d0c419758e519033554106318f19153482e462440109bd89518c2ae6290d439798c530872c548c920d54c9510c25d6315221b6d81410c25c6354910d398c525065c6355120c7d53534429e64d44309798c52c425f63542429b988530
  | 3 => 0x60140000d05003018032905201002030200640e109ad0005a2340500000154600180a0446b6040515400448020801801c00340040340400c0002c870105007c18010250001209458020000680200d5d101a90005c01c1600011014050c0030103100801414130840005c1a06861870dc004140c82b0000a07ca3000040081f070002981401801008000000a050030281b1c81d02004018000580000c060000600c000000009c03468021640011003038001280b008000024f00c1401838004000282b0082e0b8030c85523c1a00095071720743d034060384c004050040300c050641718c000200a1940103c20000001dd48070073d83404c9a07c001e9fd0145b0480b1440000c00014081ac015f8090040103c190740d084000000000801248050100d3244e00c5410000020369700700074024000680907c0006407060177784211c00c7553510c25c6054c41c7551520c25e6394820d598c5150a7b6550040c7d50304825e6315020cdd50514826f65480209dd85544874d6214d20a919121086766194f20b558c41c867661d50328f59253086cd62d50309d58653c825f63540418f592534825c63543219b99452443566194f109dd85548cb3642145429d594210433551104408f994544835753d4520d9544210823d6494d10c759253c82e661cca328f191510833754d45209d19531442cf62506309b58b54cc23f6454630ab1854210a3f64548109718d5010ad56190e30b6983528c23e6515121cd95151ccb4d4354b31cbd0c525025e6514d20b398a430c25d63951109798c5150a6d6294f10b5185428c25d6510630f20c1200832e5494b31e350c424cad5659443097596430c29f64484309ed81534874f520c110b6980520c25e63d53109758c540425e63d4b10d3d4c52502cc6250630a918941107663214520cdd954110754510c12097d95300c26d6294d10b398b310c2db60484309758e548431f5414d2097d95320ca6d658c8218f990530425c6054c4297d95400c2e662cc531d914a314431f65550309bd89544827461551209d59631086ac64480209b58b54842cc6250230d598653106da60d4830e6500400c25f63540219ed95300c2d661cc83097d8d5088755518c430a758c42907545314520cd146405025c63543429d98453082d66190c30b3d89400c26f62550109d987540c7365494430b5d85420c25f63542419d9865310a786054d21cd15321487c521086309d98754cca9d6310841a7993328c29e6414430c718d540c2776154910b5984520c38e54948309758e54882d66310531d514c515025e6315031d99495190f2e54548309798c54c871d544c830cb952520c25d6314b10e5952510c3655254643d5d44304834c53149108fd9153442796584010ab993324ca6e62d50319798c54042d561d50309b189534431d
  | 4 => 0x442713c000a4057d00604000008009c8360001c109810a40031c192c004bd8030200100000024040
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x10100000010c0008e2a1c5800000100000550000002340048500100000018385811800105000420000000001634000000000500080000000100000000c2400058474484218c342a98c4a0883621c14210830a8ae521aa21858472504418c30aaa2c399061b01843048020d10c8182401060d6458a53c4306b22a5988618355162d4430b20e0a08821858472504410c3142a0c099241491d15108420cc0a43026288686731894110782aa4a4a8861291c562d0c42948e8b146210d2674d4821842a2b96a8a8861915896194f40a2ae9a92a218560704c851482a2b8c86a9061515d65254430c1ac8a96a21851574cc9510c342b98c4a0883a41903044010c1acaa1084186846494d2108743398c890843155d4615083092ae63128220e1565504410c292392a820a63455d65454430a48e2aa084106846454d21086923a2a410821621c94010030c4aca2108210e86731854210a46b98c2a10854c1c14314540948e4b0e8620d2472550418c60eba8c890861299d264484219c0e0b1a4210c4d75189410c382a988420843315cc6448421c2ac8b0ca790685731854210b43298c4a0883a194c6150842a48e2aa085194a4745863208692ba88420843491c55210840a48e4a888220685531854210b06aa2c598861c19515254430d0ae63224210f0554549510c3182a0c098a21615cc4210421e0aa8a94a2186c0620c110042c238a84210614a1c15410932c8aca908421850d75951520c2523a2c690843499c75410a20b80e0908421854571d51520c2c23a24210861611c54210a30a48e2aa0849952472550410430aaa2c3a9061499cb5410610a60e0aa08298d9071500400c342b1884208434a1c14314940
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x2206000000020000108858794c6150842a05859cc62504418858794c6250441905851c54210830a05859cc6448421905851c94110430c05651c54210830c05651d12108430c05651c94110430885871925348421a05859cc6150842905851d12108430
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 42
  | 5 => 741
  | 4 => 794
  | 3 => 91
  | 2 => 12
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
  | 7 => 2*((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/21+packedAt s2K6 (672+(h % 21)*6) 6) % 42)
  | 5 => 2*((h/254+packedAt s2K5 (20007+(h % 254)*10) 10) % 741)
  | 4 => 2*((h/292+packedAt s2K4 (30172+(h % 292)*10) 10) % 794)
  | 3 => 2*((h/79+packedAt s2K3 (4459+(h % 79)*7) 7) % 91)
  | 2 => 2*((h/25+packedAt s2K2 (720+(h % 25)*4) 4) % 12)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf80fffffffffffe07ffffc0ffffffffc78ffff
  | 1 => 0xfff03ffc07f03fff83e0fff0ff83e03fa71e67
  | 3 => 0xffffc0fff8003ffffc00ffff0ffc003fc7e387
  | 4 => 0xffffffc0ffffff00000fffffc3f803f8
  | 5 => 0xffffff00000000fffffffffff0000003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xa6082049120080014a12c0111842984086cab
  | 1 => 0x50a58c487245526581685550a6a342a9a31665
  | 3 => 0x6143169120e9a4aaac109a6a0b690532c5a386
  | 4 => 0x458a28e2448d06f34a5a03488c739623f00350
  | 5 => 0x860c30c3870e38dc739ce38cc04218037ed800
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaaee88aaaa8800eeaaee88aaaa8800eeaaee88aaaa8800eeaaee88aaaa8800eeaaee88aaaa8800eeaaee88aaaa8800eeaaee88aaaa8800eeaaee88aaaa8800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40425
namespace PEqualNP.Outside.L_meta_40425
open PEqualNP.Outside.L_meta_40425.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x110500001bbd42bc40bf42bd43dd32bc41be40de30dc30be41bf43df32
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x34008ea98834d520c268a2a14d94640
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
  | 0 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 1 => 0xc1fffc0f83ff87f0f83fe1ffe1e07fc1a67d9c
  | 2 => 0xfe1ffff003ffffff003ffe1ffe007fffc78e1f
  | 4 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x840088a200808002284c02240229109408b0b1
  | 1 => 0x9449186425240a505a15214d21432584a25594
  | 2 => 0x89221014a4844a50422541254044a29450a0a
  | 4 => 0x295c4249606d57399683111b99960309f00f40
  | 5 => 0x3198738e738e67cee73b998311180c31ffe000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0eaeae8e8eaeae0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40425
namespace PEqualNP.Outside.L_meta_40425
open PEqualNP.Outside.L_meta_40425.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x3580002a800000c0000006344a000000c0008218081040180340ff41df32fe31fe40fc40fe20fd30fe10bf42dd32fc20fe21fd40fd41fc30ff40fd21fd20fc10fc41ff31ff42fd31bd42fe42fc31fe30fc21fd10ff32fd43ff43fd42fc42fe43fe41fc32fd32ff20fe32ff21fc43ff30ff10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x421be4350afaa898dfd48109f2a641f521442fca2105f94f10bfa82835f53503f621086f95032be28a817d53d07bea8995fd5030dea9a857f53c837a8410f78c430dfa1a85fb304c2baa7195f14530f7900417f504cbbea4995f94f209eaa0437f53887baa3997ecc230ee98061f910043bca610fd50441eea16657e548cb7a8621df54f10ee992437e53d07ba87995f94a10bd28043bd420c2fea6a05f55242bf2a643ed20082fca69077d4332dea8e85bf544437e8520df14d41ee99683de324cafca9185f942419f2a0415e530cbdc4310774cb30e721265f5310c6faa921df94831ee21c617d528c2fea8885f55032fb10a21df438c37a851077d4d41ef18a637f548877e84105f54440bfa9a217d540c2fea8195fd5210bfaa663bd420cafaa7a15f54331dfa16216e5210ef8a8906f94142ee21861bd42442bca7215f54430bf280637e548c7ba65a07dc8521fb08221f551082f8a4a1df54d10fc904217d51cc2fca890f794f21efa1861df535037aa8197dc8621ee994435e5308378a2a15f54830be2a441ec21083be6490f7ccb41ee992817d52cc6faa7a077d0932beaa6437f52843b8a0995f94f40ef994657d52886faa521f7ccb30be2a0617e530cafca820df94242ae29a21fa40102fca5a0df15232dfa8685bf428c77e85905f94c30bfa8a877e5390afaa4887bd4910afa9a83bc41103ba65085f55121bea84837d548cafaa121df94643be282837e54087be65a05f94832bf29841f741506b8a6a05f14810de2a261df310c7bc8621dfd5131ef2a6657d508867ca990ef50441bfaa6217f50486f8a818fbc8621ef992813f544c2fca8205f54e40dfa12417e51882f8a890fb50932dfa0481bc41903be6510dfd4e10df2a643bd42c86f8a898df95210bea8683bf424c2f8a6886fd4542bf2a6617651082fca210df55240bf29083ee428cafaa8985f14b10bf28885bd42103e220087e48020ee990635e5310b7c86a1df55332df21c817d500cbbaa9995f54831be298217e544427aa8105f94720ef994217d5190afea6a0f74ca41bf286837e544caf8a7905fd5232bea9483bf544c6fca0085e54021dea1085bf420c2baa79073d4932ef2a265bf428c37a84a0df94631bf29687bc5350bbaa1995f14d40bea8885fa20843baa2995f95310ee99041bd42106fca6215f94443bfa9283de53c83ba6518df15130beaa021dd32c437e87a15f94a40dea12657d50ccbb8a1996f90942deaa643bd4290378a898efd0821dea10217d510cbde64995fd4910f790441bf5350bbe6418df14121bea80857c54c87788720f7d0b32fca0081bd4350afaa7905fd4c21bfaa241be54082faa6207ec8120ef99621df329067ca8195f95042f710241bf420cafea0a16f14742ee29a817c52506f8a7106fd0910df28e857d548c6fca220efd0a20
  | 1 => 0xd518c37a8510df54b41bea9463df308c2faa9907710f32bf284657e500c3ba65105f94e21dfa1887bf42506fca3215f54231be292217e50086fca8105f14131bf28c437d518cb7e85215f94f42bea8087dd32443be6410f7d0f32bfaa021be41902fca910df95043fba0c833f544c6baa6215f55132dfa14817e51d0efca398774c931bf28861df534437a85086f94f42fa90e21bc53d0afaa9986f10d42f6a1085df320c2f8a7887794132bf280857f544cb7c8720cf15131dfa10217c54886fea29077cc030be28a417f548c35a84995f94230dfa10837e540c2faa3206fd08319eaa465ee5210fdc84995f54841be2a065dd53c82faa910df94742cfa1265df32882baa7217754c20ef99663de50ccbbe64885f94343bea90877e50083be64195f54c42bfa9e43bf5250afca5987dcc531de286857f540c6fca1996f50a41bf294657f514cb7a8418df54b439e2a2617e530437e8598df55220ee996437e53902fea9105f54610aea9e43cd424cbf44088774c840dfa12657f53482faa9085f54e31f7108417e528c3baa0997d88710be2a661bf42d07b8a6a0df54e10dea1e857f538837aa9195f94c31bfaa661fb40502fca4886b50a32ee21c637e50d0bb863185f54643bfa8287bd42c437ca2a15f15010dea10417d5390bb8a6885f55310bfa82637d50d0ef8a2a1df14542dea9e857e5010e7ca8215f15331bea9c65bd424c2fca121efd0b329f2a0437f544c37887a15fd4542ee996637e52103ba6420efd4742bf28e657c54087ee21085f54f21ee21265dc430c6fea7886fd0921bf294637d53482faa1197794732be2a4217d51d0fea200877d0c31bea94817d54083ba64a0fe54021ee188613c54442faa020df14d20ef996437f54c86fca4185f94041bf29883bd50d0afca410ef10c40dfa0c83de424caeaa2106fd0b30df218837e50902faa3a06f94d42bf29487df32103bc86995fd4940bea9883dd32902fea690df54e21fa90843bf428cb7a8498df54021bf294837e510cad8a4885f54321bfa9261bd428c6fea2a06f50b20bf2a663dd32042faa9187710b32df218817e52d037ea7a16fd0b40be29421bf428877a84905f95031bea94217c524c3788620f794532bea9c83f621086fca898efd0940ef994817e50103da851977cc941bf29485ed210877e85085f94740f6990657c54c83ba6218fb8c832bf296217e5210afca31977d4132beaa483de42ccbba84995f94221de282857d544837e8721fb90842b6a9087bc43903bc63187794e42bf2a4417f5350b5ea4a157d4d10bf28c837c5350a7aa9907790f32bea90817e540cb7a85185fd4b10bea80635e53c83ba86995f94843fb188637e50cc6faa39977cc810bf298877e53906fca31877d0e31eea9843df32106fca71077d4532cea1887de304c2b8a6a0dfd5320bf28
  | 2 => 0x62014068100708681106008040181a0400000030000b434800048020a80e000600080802044020121283c000020ac08028042ea3ab18020081e2581a308000080a6f826038b4121be0b02e39018068181a0080000001812000a62e8020203637862181b82381e05800030280580003800008000004e008364082a0006a29000029280505402008448068398a0413e3480a02004ba02805004368461a8240800008088068100080208800120262033c5f828038000a81e018000a82000800000b00301a040600d00e2000cac8061d00002000419360abc8102221682e000160008c01800001520823405838170130480e2c00000004002b0120022e8941901203004098a000812018260c8008a146140041280005800010820005c000300801e022a800026020302328e01848000000083e090003380206082060020400a0680800000138000100802802000057e508c77ca9905794f21ef98c637d51c82faa3a177cc820cea12657c544cbbe86a1df55031f710a43dd328c2faa59877d4732bfa8a617c54442f8a498f714532bfaa0417e50882faa690d794c21ee996417c5050fbca6105f94d21be29e43bd5050bb8a3996f50b31be2a041bf40102fca2085f14e21ee992413d5490bf440107bd0a42bf29e43f641106fea6086fd0931aea9841bd54c83daa421df94b31bf28c817e544c3be8721dfd5021beaa663be548cb7a802067d0b32eea9885dd53c87de84a16f50b40be29a43dd324c3f620884fd5110dfa1081bc54442faa6086750b32fd90441ef328cb7ca1a15f54620be292817e511037a85a0ef95021f610c417e520437e8220df14c21be2a4637e53842fea99977d5332bf288637e544837c87a17ed0240bea96217f54486faa61077cca319eaa643df32c837aa8107b149109f2a4657d50d0afca6885f14132fb880217c514cb7a85996f90541be2a6217e52083f460187715332f7908435d53087f4a010ef509409eaa0657d52883be64905f55110dea12437f5250f7aa2a15f94321bea8887df324c2fca8087d94420bf29881be40503b8a8996f50b30dfa1643f9300c3ba6410df15230efa1a65dc434cafca9906f55021eea9c857d52042f8a6107750c43bfaa4637d538c37c82207755132bf29843bd428cafea498df94032bea84857c5050afca9996fd4142b7a9221df324c7ba64187794c42fb98c637c54ccbf42008774c832fc902217d510837ea8985f55021bea9c417f530831a84995f14e10dfa1085df328c2faa610df54b40bf29c877
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x5324c74d524c8408f197424c63e6415021d9584524432f52509419d584540c25d6394a109b588540431c53d0910d654e500866d6215030cb949420c25f654c030e350932c823d6494a31c7153324438e6150932c754d42c825e6394821a7592324ca3e64d4f109b58854cc66f65508429e181544863f6454e219dd85544826e6215330c7d5053442f3654401097197325031d5494f20cb990524438f5250932d5cca510825e654c9108f191530431e53d0a428f59052042ce6210d328f993530834c53d4910d354e4210a5d6314940d554451ccb8d424ca10c7151324c34f63d4910a718d401025e6394d108f590524431d54cc820a718d411071d53508218f994544c26e6294d10cb19352442db60551329758e529027960d4c219798e52d07374254420c714d4350a6f654c8328fd91524431e54cca328fd95420823c65d09109718d524427a60d50219798f540ca5d6394a419798c52443593294021ec191100423c6550910d654d500863f6454031c7550544cb2e5250832d358c524431d54cc832d64c9500876852881109b988540c34f524c930d6540504cb565354420c794f4210a7465485108f990524429c64547328f59252cc63e65509308f992520831e54cc8209ed95100433542944209718d544867a60d4c219758c524431d5454f209d98753082d46154132cb9514210b8d424c831e3151424ca3f6454d218f59742086cd6210e319798c54042796015021f44c910042cd62d5332a7d954310f1d5310c41a7d91504ca9f6250c43a7592424cb1e53d083297997325023e6494a319ed95401038e60509328f990528425c6354620d314b324427661d5230e3509324c66f65484218f590530831f6550c43ce5405050a5e6394a41c7550434ca5e63150328fd91534425e6590932c7d53324431d544cb208f59052c438c65509328f191538831c548c130c755132c86cd6295132c7550430c31d5454c218f993538431e54ccb218f592520cb712154021c7153534426d62153308fd95420872e62952328f997424423d6494d10cb149424432d4354843a71814310e9d63909428f992544c38d424c82197d8d544427b60551329d984530823e6494830ced0a500863e6414f20d394932043696014910c7951320cb1d5310c40d3549320423d6494810e310d424ca5f63551219758c54c866e6214c10e3509325025e6394a10c714f425072d544c832e350d424cb1c5390541e390d424ca5c654c9409719732507e062440109758e52d077152440108f597420825e63949108f990530834d524c841c794f420865f6354910d3d4b324425e6315321d554e510827a60148109798c540866f6255110ab98a4350a3c6454620add855350a3f6454d20a3592424ca3f655084297597320825f6254c209758c540863c6454031c7551530831d544c821
  | 1 => 0x83555114532c795253c827a60d52318f994544c63c64542218f596540823f6550c4397589530825e65109329d984520429c635434297d8d540423d6414930c7953320cb4e534c832c794d420865e6314940c755332c878d424c81097d8d51102d86054532c7d50438c2d8604c930c754c53d0b4e6294e42ae1815350a9c63541429b588530431f544c9109798e520425c654c9418fd91510c3b14244010cb549429029f6354142ab588431063d6494b30c754f4290a3e64948329798f540873954940219798e521034f524c9109718d50d0b1e5494c208f990524c25d63150108f596540cb1c548c531cbd0d5210ed46155132e350e5210f1d54cc8219b189534431e5454f20c714e40502bb6054542add855050a5e65d0d32c755253086ae6210d42e3508514ca3e64150209758c525063c645473297d8d50d0ab86050940e3509321071c5414d10cb14b424438d424cb30d354b320c2cc6550932cb549420438f43509329dd85534838d424ca30ab592424ca5d63d52108f59353c832f5414910d398d5210f2e52508109798f540831e53d08208f990530863e64148109b98a524427761551329d587530823d62151319b988540438d65509329758e524425d63d53109798c52c423d64d4f10e3508504cb1e5454c219dd95411071c53509409798e52c434e524cb419d98754083395454021ae580411032f54d4910c7d4d425063e64149319758b535023e6494810ad1855050a3e64948218f992528438f6150932e3d89424cb1f53509109b189544431f544c9309e583540871e5454f218fd91518823d6494b10cb549420c25f6354041b358854cca786055132e3d8d424cb1e5494f218f592520c23c6454910f4d8d10042796584010d3996424cb1d5350820a7191300c2cd6490932e3181424cb2d52d0b41ad185425072f52d091097d8d508866c6550932c7d50438c71d5410f328f99252cc71d53d0b21e3d91424ca3f62550209e181534875532544208f590530425c6354221cd55151082796015031c794d42c838d6150932c7d4f425023e6515110c795132086746155132cb590524434d524cb40a7d8d50d0b8d428c9329e583548c78d424c930ab588439065f6550c43ab58853d0b1d54153329b994524425e6314c208f58b544c31c54cc931a7191310c63c65d0930a7d91514ca766115030a719150cca5e63948419758e520874c53149108f992520c71e544cb20dc885500863f6454332b6181544ca3d6494a309758c52c425c63540419718d548825d6394b108f99353c878d424ca41cd951510825f6355130e3509328c6af6550a32cb549429065e6315320b3588438c31e53d0b21e3185424caaf6254d42b3988424ca9c6454532a7191504cb4e6314910dcd95100431f54cc931b3593524ca5f6354620cb951428cb2d52d0b40b518
  | 2 => 0x65d09319e980540c72d5250b309798e52d023d659502197d95320835732544208fd95420cb1f53d09108f191534423d62d51318f195424c25d6510c3097d95320cb1c544c9318f58b544438d42d4532c795332c825d62d4d10c754f420823d6494820c7d53534425e6394a40ae1815150bd06344010d914a214423f64547328f99252cc23d6494831c714d424432d5250b31e3509328826f6254d108f597420ca5e654c941d3d4f52442b561d08419d185544825d6214d109b58a534431d544c82097d8d548871c5450d3297994534425d65cc8219d584530825d63951108f191534865d6594c20c794f42c833554944208f990530431e53508429798c520433a54540218f992524427765440109758e521063f6454221d3549328c3354254420c7d4f425065e63150209ed815348755510c430cb94942cc6ad63d4942b6580310c2f06048510a718d5150a776548421cbd95424cb1c544c910c7553328cb355110440b398e424cb8f60509329798e520825c6355110cd952510826d6215031c7d51324c6bb6054d4297588535025f6355131e3509320c2d561cc831d54ca510825c6355221cb94942cc29c6354742c750d5210ece62d0d32a7d8d5150b4d52cc8319758f54c872d548c8329e98054087595014332c7153324c25c6355010d3949321063f65504418f19150cca3d6414c21d6cca500878e6550932ab588431029e648c9328f191510c34d5350842a7990424ca7b654c0308f99052c425f654c8219798f54c823d6215110cb150524431d53d0b209798c525074c63d49109758c540833950143428fd91530429c6150c43ce50a500872f5250940e3509514ca3c6454e219dd95310c65d63948408f995424c63d64d4c21c7951320826e6295110c7551320ca9d6490c43cbd95428ca5d63d532097d95310c63d64d4f21a7d9151ccb2d5250831d394932d023e6495131c754f420877151480209798c528429f6354742d694e50086f061481108f99252c42d76154132e3509321025c65cc9109758e520838d60509329758c520425d6594c219758f540863e6495110e350d5210f2e5250831d554d510838d424cb10c715143ccace6590932c754c5350a5c6354742cb153524425d63948109b58a54442d960cc830d354932d065d6394b40cdd0a510823d6215130ba580218838f54509328f995424427661150208f593538432f64d4910c350d5210e5e654c940d3149324425e63d5310c794d420cb4f524c931d6cc9500863e6494a3097d8d51d0bd332440109e58053086756115020c714d425078d424c921c754d4210a5c654c910d394932103394254021e3509324425e65cc910e350b504cb8d424c920e3d4b424cb8c6350932c795132c86cd6210c30d594e510825e63d5321b5d85544cb1d5494c20d694d500871d54ccb209758c54c
  | 3 => 0x71a0000901601c1304858011900014408c4c070040040a21016034000200133c00038020380103400008e47e00000251000300141a030140500302c0b000350a4ab004000ec390002f0b8000280007418004000705d00c170280000010168040001f95047004110084f0d0040000c03c030140000c000082e0102100010008120200300407000002100200c0200c0e000000e0000500500000004000001d04400040bd070190e40106c0d0641224c4803c0b050010040e0541e03404020130000000c020040101c340340700804000070e80003c0e080090081203c0f0f0030003b014000000001801000010080004807024020bc03024041ac4b00c12008000ac0012400000550180003c1800cdb04c010001302c160640302406000001040212c030200201d7e0007e0b0580141316002000020047c008000000100411050170700805c01008030b01d0005f314000d0000b4fa08c300ac1501c0102c110000008c14000010040e0080300c00c754c43d0a5d6510c31dcd4910042ad6294d42e350932d02ce6550932d354b32cc31e5454c20c755253c863c6454d208f590528431d53d0842ced09500863e64d4c21ecd0910042cd6210c31ecd9110042746154d209718d544838d4294532ab588439023d6414f21cb195424cadb6054532c7550430c72e6454843cbd49424423e65d09308f592528425c6550d32e3d95424cbe36244010e350932cc78d424c820d3549328c78d424ca409798c530878d4254132e350932c87355114742c794d420831c53d09409d587548c38d424c94197588535063e64d4f208f58954082786548110e3508424cb2d52d0840c754d42c863e6414f21bc58610042ad62d4f429798f54842b46154d429b98854cc78d4294132e3509320ca3f6550040d3d4c524426e62150318fd91538831f53509408f195424c67a6014c21e3509328863d641493197d8d548834d52ccb319798e544427b65480209758c528423e6494d10f8886204427b6055121cb54b421063d6494821d954621082cf6255132ae583421026e62150328f59053c834d4354843c7d53324c26f654802097997325067561d5020d390d5210e9f64543328f990540cb1e5494c21ce952500865d63d50209718d511023d64949109758b535063d64d4c20c794d42c865f6355120dc546200829e6390942cd5445150b8f6250b32e350932d071e54cc821c755153c863e
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x230000c0a325d71a0001384003c001020801104000028a0c294120c5d10414001361408203621c16550932c1aa8b10861860e65509325028a38aa821a65461cd5014142e0a84992a21055070544514ca86b90a6a1283835916314910a1ee4a1aa421d0e75509324c6c5b82c2a1265a25806050932a18e0a1aa421d8471581424ca87bb286a908762dc16550932c1ec9b1ea4884d0764c9100428a38aa629a85469c35410e31e1284992a010d0d739494204342a10c2a8265d05493244010a28e6a88a2a160c6550d424ca86ba4a499021439d5424c91089ae431aa80850d72151324c2c3b8ac0a12654c1c15114542c28a630a84a0c2d721915304306a9ac421883435c8544c910d1285b02a29970542544514cb0a2a0c299263435cc5250910960eca12200851870550434cac238acaa1265461d15014132f02849922008530715405050b84a12652804383d516210e31a30e0aa0a89950d741493244382a126528841451d15114532a18eaa12648868942181514cb06a9ac421881435c85350910c18caa126488721525091004286b90a6a1281459c75410e30c1ccaa1264a0e0f54588438c286b90a899263835516210c31c1aca32a849958771595424cb06aa2c42a6658614c6050940b10e0b0a849968561185424ca8a38aa82a265439d5424c930d80c6312200850c7150d5210ea838aa028265a81906244010a1ae4aa2641060d5358853d0b0732a849922143dd54354843c30a8302649870942540504ca8c382a629a85a150b6154132
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x90000001200000000010003700700000a0681d516210e30a08805946550932a0a80d516210e31d01421c55014132a098214c6050940a0982150604c930d01421c15114532a80865093244010a80805846150932a04815946550932a80815806050932c80765093244010a058214c6150941a0582150614c931
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 779
  | 4 => 754
  | 3 => 85
  | 2 => 14
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
  | 6 => 2*((h/35+packedAt s4K6 (704+(h % 35)*6) 6) % 44)
  | 5 => 2*((h/266+packedAt s4K5 (21033+(h % 266)*10) 10) % 779)
  | 4 => 2*((h/293+packedAt s4K4 (28652+(h % 293)*10) 10) % 754)
  | 3 => 2*((h/42+packedAt s4K3 (4165+(h % 42)*7) 7) % 85)
  | 2 => 2*((h/32+packedAt s4K2 (840+(h % 32)*4) 4) % 14)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x81fffe07fffe1f07ff0ff0ffe1ff81fa39f3f3
  | 1 => 0xfe07fff81fffe1f83ff0ff0ffe1ffe05c67cfc
  | 2 => 0xfff83fffe0ffffffc000fff1ffe3fffe078f1f
  | 3 => 0x3fffff0001ffffff0001fffc0007f80fe0
  | 5 => 0xffffc000000001fffffffffe00000007fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa4308231442420014b013012602484b018b171
  | 1 => 0xc910450c848022815105104a2092c10c254b4
  | 2 => 0x104228820291115280888aa115425146050a0a
  | 3 => 0x5965b124921d559ce6aa0881d9901867680fc0
  | 5 => 0x618621c71ce199e738ccecc811006187b7e000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeee8eee8e8e0e8e0eee8eee8e8e0e8e0eee8eee8e8e0e8e0eee8eee8e8e0e8e0eee8eee8e8e0e8e0eee8eee8e8e0e8e0eee8eee8e8e0e8e0eee8eee8e8e0e8e0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40425
namespace PEqualNP.Outside.L_meta_40425
open PEqualNP.Outside.L_meta_40425.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x465bf4290bf621085f54e31aea98817e5010afea9995f14d41be2a063f940103da8421778c530bf28e873e54c42faa420df95032fa88021bc421037e84a06f90a40be29c43ed42c83baa7215f54032bf2a6217d51c82fca3187d0c710dfa0481df32cc2fca7a0ef10c409faa2417c54c4378a8905f54b41bf296617d5490afea690df94331bf298637e510c3ee6390df14131bfa9c43f641c42f8a998dfd5020bf28463ee20482f8a6905fd5030bfaa221df4350f7ca9885f54231bf294857c5150efca1215fd5120bea9421de434c3baa610dfd5232bea9221df328cafea710774c930bea9063bf41102fca421efd0b40f710a43dc43ccae8a2995f94410ef18a637f514cbea4210f754c40bba8a41ee42483be64196f55020f6a90817d50106bca7a17ec8220fa10821be40502eaa2105f55130bf2a2617c544c6dca4205f14143bfa9e41f6518c2fea8085f94820bea96877f514c2fca9985f94d10bf28665f731442faa6907b8c832bfaa2637d50d0fbe8618ef55021df21e85f431c86bca7217d88710ef29841ed210877a82207e48110bf29881df53483ea83885f54341baa8c615e53842fca318ef10d42bea9c817c52502fca7a05f94b10bf296817f540c6fea40877cc631be2a443755110efca6185f94421dea1e837d53083da40105f94640bf29843dd324c7ec8390df94a30fc980617d538837a84215fd4132bf288837e53042faa2185f54743bf290437d510cafca4207754f42ef21a637c53042eaa3a15f94832bf29a417c53486fea810df95030fa18a21ef4250afca721fdd0641fb90c435e53107be8718774c030be29a817e53882daa4205fd5230faa88817e5410afca8905f54c10dea16837f52842faa8107dcc421be2a0617e54106fca5197794f42bfa9e217f53482fca399774c4309f2a063bd4310fbc63985f54732fb20a21dd32cc6faa710f754e10ba28a417e544c6fca818df15121bf280617d53842f8a8997dd0541bea8e81de328c6fea9907d94440be29021df53486fea498dfd4c20ef21e637d51842fca3905f14532faa0e43fa20442f8a790df94f10bea9e213d54082fca7206f50941beaa4875d5390afca321df14930beaa4837c54c86faa2105f94040afa9a837e5090fbca6205fd4520be29c217d53086fca5085fd4143ee21c637c514c3baa620df15210fa188437e51886faa4205f54043eea1a617d52cc7de4310f790f30be2a0655e53082faa720f70ca31dea1a83bf4390fbaa6105f54c41bf2a221f950086b8a6a0df55032bea8c617551102fca598dfd5331fb10a217e50d07f660985f54742faa0a217d5110fba65987d94420faa88877d54843be62187d90421df2a063de324cbda84905f54640fb884217d51883f241085f54a43ee29a815f53486f8a9995f14e20df2a0417e52906baa7a15f54a31
  | 1 => 0xd50c877887a17d50421fb98c637e51cc2f8a7885f14a10beaa2417f53442fea4886fd0b41bf28043bc439037c84205fd5032ef98061f541107de4210d794c40beaa263ef328cafaa5204f15120bf288877c54086f8a8886fd0640fc88021bf42506faa998f710c30bea8663de304c2fea910fdc8610fb208837c54482fca821ef55031fd104215e53087bc64185f94010bfaa6617e51906faa018d714d40bf28c85bd40103eea2905754c20bf2a021fa300c2eca3a1770c830bf288657d52cc2f8a9185714d21bfaa4213e54086faa2215f94221fc900417f544c2faa2204fd5130be29221f610442faa5886fd0040bea8043bd41902f8a9985fd4131bf2a0437c5350afaa1215f54642beaa621dd43cc3ba63185f54f20de2a2617e54882f8a2a05f15020fb188637d51cc3b863985fd5132f7904413e54082fca0105f54843bf29885be4250afca890f7d4d41f7216417d50886faa9985f14c21bf29e417651082f8a7905f14542bf2a0417e508cafaa690f750c32fba8a65be43102faa520df15010bfa98217c54c82fca8997750c43bf28881df438c6fca7a15754e10af29e21df318c3ec8318d7d4d20bf29085dc430c6fea610d754f10bea84877e500cafea9105f15130bfa9a81dc53506fea890df55221beaa2653d54086faa6887d94443fd882217e510c6fca521df94831fa90e217f5050afaa810f794e10bf29c857f52503be64985f946329eaa6215d53086fea4986f553109e2a2617f548c77a85a07dc4010aea98837e50d0be8a290778c831dfa18877e54843be86995f95230bf29221dd53c43ea8318fd08610bea8085de53c437a8220df94e10bf29e43f6414c7f440105f95321bf28e817e54c83f661185f94810bf284417e518837e8220f70c831fb98a63de53106fca8207bc8020be282837e54886fca918fe84010f721085bd42502faa80877cc931beaa4817f53842faa7195e94021bf29463f5414c7be8721df94031bea9681f4514caf8a0995f55320beaa64376518c3be61185f94c41fb98e217f54c86faa5185f14c20bea9e43be4350afea2a05f94c439eaa4657e50902fea4a0df94d21df21a87de53086fea090df55231bfa8a857d5190efca3a15f54c40bf29c4377514cafaa510fdc8521dfa1a83f721042fca2105f55232ef194617f53c87eaa2105f54e30ee21c61ef4290afaa4185f55220ee19461df32cc6faa890fd4c431bfa96217e50842f8a4a0dfd4943df2a043dc53482fca420fe94021f7290817e52d0ef8a498df15220bfa82837e50c86fca1185f94830be282437e50906fca720df54e42df21c817d50d0bbea6a05fd4d41beaa4617e5010efaa6215e54021fd90241f651d0bbe86184f95232fda0281f521442faa1995fd4543bf288855f53502faa3195f54f40f6990657e548cafca6105f54241df2a
  | 2 => 0xc3018000280001ca9010000ec513a40c0940a0040a050940040101004038011b02e048050145c0044701802014901e000018320041c0040007c0600062014080380205c2566c000001a0140d8ac5b00017005180100a00001001000000000007000000080607c000040000c01010b63f0190080e0e0090280d00c7c048000502b068080a40000000039df0040101405024240002d0002201c001cc0a06c20004004d4140000d0440d0000400c1706c0c01400048050000e0143100011084060102b0940300403000002782d08c0c0180700008130160280300c000000000000034040ec0e01c000242f02c03041f726c0104c00008660151100c100102c01c2c050010080005c2c0000002c2f034100442c0040002c1c0302500c050180c09405024080581d1382606d030004900016040010000f01c001dc170cc250241d510080080e010003c40ebf29481bf41907ba8698f70c530be296217c53442fca99977d0f32bf298655c53483bca7215f55110ef218877d54ccafaa4087710d32dfa1e837f54c437aa9195f15231bea8465de438cbba64197750e32fda04817651103de64995f94b41bf2a6637c5050beaa3185f14943beaa0617d540c7ba8798efd0842be2a465dc534877ea8905f14520ef218657e50d0eeca221fd884219eaa063bf544c2fea6a16f90541ef988637d52882faa7a0df94041fd20081f551d0afaa7a16f10a40ee988637
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xc54087556114d41d654d500873a5454021c714f435063d6414b10c714f425065e631414297996434c25c63551209758c5150a6c6550920d5d4c51482746154a409d586544ca756114c20cd592518c2776154d219d98454cc25e65d0d329d195414c63e6414f109758f54842d46348710d554e41086b5640c7109d594310871e5494c21c7951530871c548c530d5947308c25e63152109e98053086756194243b5584430c67761548309b189544435553cc4218f19150cc67661141429758e518823f6454910a7590314c35653947429718d5110a3d64d4c219d185534825e6315310c7d50534835a535402197d8d544c65d63152209b988530435453d45208f191534823d64944109798e544833a54940219798e544871c5414d209d984544c335544c431d654e500865d6314b10bc580210435651cc630c754d411063e6414e218f992518c2756195232b558443cca5d63d5310a7992324cb716014520ad584439023f6454032c7952530827561953209d984540825e6394b41d554d51d0a5d6315310c7151434c25e63150109758c544425d63946409d596410869e63908408f99252cc29c644c0309758e50042776154a409798c530835432946308f59252cc31d6315130cd986548ca5e63d53209758c54042766115032a759031cc26d62152108f590520426e6215020d594e511025c6354a4097d8d51c826f6548421c795153c431d63952328f99052042796015032a798e4250a7565c84108f1915388355535444097596320c65d63951219798f540825f6354a409d584540835a5394021a7992328c26f654c8328f59352c433564145329e580540867a6015021b518532cc65f654c030c7550430c65d6314910d594f108425e63940109758f54c825e6394d2097994434ca766588510cd951510825e63152208f992520cb7331540219b98a544c71e5454c20a7992320c66d62152309d98654c83366414532ad590310867561153309e583530867661d4c109d584544c26f65480209b588530435543544439798c540c72c54909209d984540425f6354810d514f21486d4614c8329e983548c6b5640c7219b18953442d46348421cd95141c425d6594c209d19521442d463485109ed95200823d6494630cd153514833754d4520d554d41c42766115230d58ca518c31e54cca328f19153442b5640c5109798c540865f6354042d594d511023e64149109e181544877151480208f99352c425e639464097594430c2b56110c409758f540825c635501097997324c7565394420c754d41102d56110c309dd8553482746154f20b5986304c25f654c4309d98454cca5d63944108fd95411065f6354740c7553430c6756194d20cd986540874d53548409b98854042b56110d428fd954210a3d6414c20bc181414425d65d0c318f590538863d64d4f21
  | 1 => 0x82d56110e31bc5802184279658401097d8d544429e648c8308f59642102d4614cb309d986544cab661d09419d586544823d64d4c209758e54c831e5490e328f590524425e6590d319d587548c25f6550c328f590528435443145329758e50887574394630c754e431025e63d532197994534823c64543219d99731442d46350631c7551530865d63d53219e181544cb5743145329d986544827661943329758c528431c5350940ad58443d0a3d64948329718d50d063d6414f108f99252cc71d5390f42c7553310c63d6494b319798c520425f654c8329758c54082756115030d554d411065c6550d31e550d414c67960d5021ce552500871c63550318f99742502756115220c754f411026d6295131d5945318c2776154a43bc185208425d6395321d590d5110f3754145209d185544823f6454d109758c520433561952328f990540c65d63d502197d8d50c8771518802097596320c2776154f209758f52c432d52d004097d95310c67561150329e983540865f6354341cd952510827661d4c20a758f42d073651504409e583548c65f63551209ed95300c27b6544010c7552530875553cc710cd150514825e6314a109798e51883565354742d954a511025f6355221b518d41c871c544c930cd951410869e648ca31dc485500865e63d4a109b988548435553504219d984520432d52500408f994544c37141540219e195204423e64d4f10d554e411071d548c831b5185324c6d463504219759653087366494630a718d411025e6394d219798e52d025c63547409758c548871c5350941cb90d5210274615513297d8d5110a756195121cd552310c66f6550842c795253c425c6354042d994a511032d52108409798c548865c6550d309798f548425c63547208f59654082d463505108f990540866d62150309e983530871c548c1309d986534827561d4c209718d524425d63942419d987548c25d63141429798e509065e6314c21d594d510825e6314910b5584438c25d6394b419dd95310c65e63150208f99052843546154f10c755153c431d540c8319798f540cb1c54cc9309e980520423e64d4f208fd9150c867765440108f992534833554944209758f528432d52d04408f992544c23e64946209798e510431c540c5309798c540c26e62150309ed81544ca7561d4e209d984540c33661953109bd8954442d56110d329e580530871c53d09409dd85544827a60150329758e544ca5c63552218f990530427661d4e20cb588544823e64d4c219ed95401027465505109dd95411069e6390a409d58650cca3e64d4c208fd9150cc67565084109798c52c423e64d4f2197d8d540423f6454e208f191524426e6215230cb551200835553544209d9865090e3d6494d20dc905500865e65cc9309758e52d023d659503197597430c27561152309758
  | 2 => 0x1024880000527c0204851004000000532832000081081100c27020000181906c1800114050880200309803004d908c6900802000060340201030014030044600802000001380006406074020ac5b0700b0181f000200001200c093382118046010000240100088100240000105811078011840011c4c4cc06134122f47101400018020281100402034780003e07800018000580d004110e40a4d807000030d40034d960185b0300000430014180002c0000102c1a0101a0000003807040f30040e00406068020b833000010000001c0101c07174050040001403004020080803c0f0b44d0000c16800600000101b060040bc1d0000001c0a0042209c0b0b406020310500b0040000004007366115130cb10d521029d63d0941cd50d5110e5d631521097994534865e63d53108f99053082756115332c7552530823d65950218f590530866d6215010c714e405023d64d4f10dc0c5500865f6354a4197d8d544866f6254d109798e50886746154a438fd954310e7661d5020d510e518c2766114c20d554e51d0b4e5354840d58c8514ca766115220d9549511023e64944108f994544832d54c80209718d544863e6495120c7153534834d53948409718d548831d544c4319718d50c874e53948408f990514cad4614c930d554e510825e63151109758e544825f6550c439dd85524432c5250941c794f4290a5e6395321c7551530831d53d044197d8d544c23d6414c10c7d53534825e6395320c7951438ca7561141429718d544423d64d4f20dc885500863c645403297594430c6766115031d594c2184337435444397d8d524435753d45209798f52c435653c86108fd91534823e6414c21c755253c427561d5020d554e41c432d52504408f590514cb3554544209798c5150a766195232a718d40103665254440c7152434c23d649462097596430ca5c63548109798f54086d663841108fd95401035553944409dd952108674615483097994314c23e6415020b518d41c43546154c21cd584544c25f63552208f99052c429c6350640e5d0d418c67761551329ed81544872d5290840ce551500865c6354a41d514c514
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x5618800408402000005800070018558d619523283eecaa46418e1454185324c30731aa521081151d95350421c18c6a9282204547654d41c42a839a42a8043455d2514c630c18c6a92802051571151434c28b3a46528c6185152618c130c2ac6b08a8985257110d521020ebb0a818a61455c65450e32a2ce9190a2995157418553086a839a82a80439494d6008610a62e818aa010c9574185324c70aaa2c221863455d06154f10
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1010081587152618c130815869d2329463081587150614c930815869d23214532
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 5 => 2*((h/263+packedAt s5K5 (17928+(h % 263)*10) 10) % 664)
  | 4 => 2*((h/214+packedAt s5K4 (20482+(h % 214)*10) 10) % 539)
  | 3 => 2*((h/22+packedAt s5K3 (1225+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/15+packedAt s5K2 (240+(h % 15)*2) 2) % 4)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x83ffffc0fffe1e0f0fff0ffff87fe07c39f3f3
  | 1 => 0xfc0f87ff07ffe3f00f87f1e07f8fff8226ccfc
  | 2 => 0xfff007fff87ffffff007fe007ff0ffffc70f1f
  | 3 => 0x7ffff8003fffff800007fff0003f80fe0
  | 4 => 0xfffff800000003ffffffffff80000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x88610046100420010189022318112118085171
  | 1 => 0x19224c8a3229065086c391452c8a4b0a22c4b4
  | 2 => 0x20841110415000a61004240841209460c50a0a
  | 3 => 0x72cb6624a51d4b3bab508112764c0633780fc0
  | 4 => 0x430c4438c66193cccc66c99c04081843b7a000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfaeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0faeae8e0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40425
namespace PEqualNP.Outside.L_meta_40425
open PEqualNP.Outside.L_meta_40425.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x403403850310010c00800000064417410000000803820c00200000000c200000254700901ff10007fc4301ff50c09fe53007fcc005fc3201ff950057d5201ffd0003fe21017fd4805fd3201ff55005fe20007f4c003ff10017f94807fc5400ff14405fc52017f10809ff51017f8c807fe43027f54009ff53027f14c09fe50017f50803fe5101ffd0407ff43007f84005ff3201ffd5005fd21017f08001ff31015fd4809fd5100ff08401fd31017f54809fc50007f8c003fc10007f0c001fd10027f54c05fe4201ff50405ff2100ff10403fe31017fd0803fc3101ff50005ff2000ff90409ff5001ff90005fd20
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x286004bf9951003ff88688027ff530c035ff9066012bfd8930107fe4198827ff43cc40bef9806020bf58b31004feca8806fff41cc013ef9966009bfd973104ff8869883bfd420c003ff98a2009f7ccb3106ff8421805bfd328c013ffa1e6006ff58910097fa649804bfd624c00bfe2822001ff8c61004ff8c598827fc320c013ff21a6209fdcc53102ffac518007fd414c41fffaa06009ff58b3004ff8a798027fc53cc40bff1022001ffd0531025f8ca9887aff644c435ff2166005ffd42100fffaa09886bfd52cc0077e322201dff0813102dfec288017fc2084003fe90a6209ff8cb3100ffa6308087fd40cc40bfe2026005ff4821002ffc6098017fc4044025ee9926007ffd511000dfcc298007fc214403ffeb2a6211ff1453002ff8cb18027fc65cc40bfe328601bff5033002df8c50800afe62cc43bffa92621dff5493104ffec598802ff614c00f7eb222005ff042300fdfaca98837fe410c0057e3166205ff0413001d78c89801bfd4244037ff2a66005ff08230047faa688027fd430c037ffa066004bf9963004ffacb98807fc3184045ffa866212ffd493010ffe819884fff644c021ffa886020ff08331047fea68804bfd204c0257eb126016ffd4a3000ffc43080037f654c02d7eb146005ffd961004ffc6598047fe314c043ff2a6620edf5483002ffecb18027fc64cc42bff18c6009ff94c30037f86488077fd324c411ff29a2005fe8821002ffe2018026fe634400bfeb142005bf1963004ffec398007ff21440057f3106001ff50731077fe421807afd644c435fe90e6005bf18e100f7fac898816fc620c00bfb8842009ff58b3104ffecb98817ff620c01dffa10601df74c93100ffc8288017f61044013ff21e6205ffd90300b6faa51803bfc420c00bff3086009ff90f3000ffe6308017de304c003fe28a6201bf987300dffa839803bfe520c00bff2006005ffd423000ffe8398816fe6084003fe082620bff10e100affca318017fc648c023ff28a600dff1043000ffea288007fd21cc417ffaa42005bf9803002ffe6108053ff504c003ef18a6212bf58e30007fa6298077fe624c401fe98c6013ef1913002ffcc318027fe62cc4097f32c2005bf1813102ff84098026ff65cc00ffaa0a2005ff4823002ff8a108026ff64cc40bff1042006fd48510107faa598827fd32cc0057f3142000ff1813102ffac908017fc408400dff2922006df5491010dfac998817fe500c013fe18c6005ff98a30077f8a418027de43cc00fffb222001fec4110015fcc498817fc618c013fe18a601cff54330037f8848808bfd50cc40dff3122001bf1873004ffe6318027fb308c00b7f306620aff0ca10025fcca18027ff60cc43ffe2826215ff8863004ff6609801aff624400bffb1c2011ff8853000ff88288027fd32cc413ff9906005ff94110
  | 1 => 0x7ff53cc401ff31a201dff58931057fc6508017fe30440077f3266001ff4861004ff86598016fc648402ffe2a46003bf990300edfac498812fe65cc427fe2a2601eff9013100dfcc21801bf9204402dbfa946021ff90331007fec098852ff654c0397eb2e6012dfd4930097fe4098007fd514c403fe28a2001fd9051002ffac708027fe310c00b7fb206000ff4c11002ffcca1804fdd434c00bfe0822001ffd47310cffc8398007fe41cc413ff29e6005ffd403002fba6018017fd408c00bfe3146012f7cc9300effec498887ff54cc413ff29e6202bf9893001dfcc998827fc534c003ffa0c200bff90e1006ffca21805fff438c027ffa1a601eff50d310bffca918007fd418400dffa922016ff8ca3002ffec518007ff104c40b7f3046001bfd811004ff8a718016ff628402dff2146005ff4803001df8c89886fff54cc013ff992621eff1913102ff84018077ff424c401feb0a6017ff506300d7fe4398007ff21cc427fea02601eff55131097fc8498007fe3144015fea942001ffc433100ffca28806bfc42cc041fe2166209bf18d10025fccb98027fe65cc413fe29a6219ff107300efbe6498853fc654c03dfe2a26205ff18a1004df8c998002fd61cc03dffa1a6205fe04210037fec488077ff204c43bff1926209ff0c43002ffccb18017ff648c013ff32e601aff94b3000ff88398817ff300c03bbfa92621adf54b3000ffa628804fff404c01bff1086005ff542100d7fe8598083fe52cc40bff2066005ffd023002ff8c818023ff5044013ff3266005bf18a3000dfac30804bff624c027ff2a2600fbf590300a7faa098017fc2044013fe2186017ffd0630097fc6498087fc54cc415fe9942003bf19130037fa4088027fd65cc0357eb16601fdf1953102ffacb1806ffd54cc001ffb0a6005ff58430047f8ca8804ffc644c035fe2966000ff5813102ffca198007fc3144045ff2866200bf58d1002dfec518017fc6384013ff9966001ff1461000ffaa398827fd43cc041fe2966213ff5053004ffc8698017fd508c0093e32a2016ff54a300effc8498823ff65440137fb166209ff50f3104ffc8718026fc65cc40bfe9842005bf18430005fac708067ff10cc03dfea026213ffd053000ffc428802bf92084001ff9822005ff0421004ffe6218027ff32cc413fea986016ff4863000ffca298812fc654c041ffa166205ff9961002dfec91801bfa204400dfe3122012ff4853002ffc6108017fc500c00bffb28601bf750f3002ffc4018047fe614c027ef21a601effd013100fe862988127c654c437fe2a6601cff5473004df8c99882bff52840017fb1a2012ff5493003ffcc88807bfe544c40bfeb106009ff9933102ffcc508057fc518c041bfa966209ff1933000ffca308017fc400c013feb0e601adfd4b30047faca88062fd658c00bfeb
  | 2 => 0x30007fac688006fe63cc441ff2166209ff4c73000fb86298817ff400c003ff18e6219ff947300aff84318027fc324c0137f3186016ff50a30097fa8498053ff534c011fe29a201aff48330057fca508007de31cc4057f316601cffd43300affc8318007ff314c441fea166209ff0ca3002ffcc70801afd6244003fe20c2001fec42100c7fea718027fe320c01fff2a06020ff4833102ffcc918002fd618c003fb18e6206ff9091002ff8c908007fc31cc40bff2042010bf594300effc409887ffc654c427feb22601dff14931057f8a508007fe21cc427ff3226003bf9913105dfac908027ff62cc00ffea022009ff0c93104ffac998047fe414c03fffa9a6201ff9053104ff86398053fe654c00bff2842001bf185300f7f88098803fe604c433ff10e6009ff90c3003ffe808807ffd534c417fea1c2002bf1893005ffaa908027fd60cc40dff1922016ffc8630046f8ca8800afc62cc029be32a6005bfd8e1007ffe8218063ff518c013ff29c6001ff546100a7fea298007f6214401ffea08600affcca100fffcca9883bfd210c00bfe1842005bf196100f7fcc89881ffe5444003fe10a621dff5093102ffec508017ff1084013fe32e6013ffd5130065facb08027fe534c0277eb226005ff99210057fe8508002ff604c43fff2826204bf9953104ff8879805fff548c03bbea926203bf99230077faa418003ff6344025ff90a6004bf995300eff8c498827ff31cc025fe2126008ff9951000fb8639882ffc54840297eb2a6016ff14a3003ff8c888016ff6484013ff29a620adfd4a1004ff8879880efe644c00fff21a2020ff88331006feca88047fc414c003fea0a2005ff540300b7f88518027fe62cc0057e3126201ffd051004ff26018017fa300c00bff9042000efd9130096faa498007fd2144025ff2926016ff94a3002ffc4198057fc418c017ffa1c2009ff4c83000ffea298817fe10440093e32a6005ffd02100edfec498877fe524c40bfe2866022ff1433102ffc8118053ff654c00bff2026009ffd933002ffca118017ff610c00bff310601effd513103ffac888017fc100c019fe29c2006ff5491004ffe6518087fc40cc40bfe3106005bf1943004ffe649807fff654c439ffa8e6005ff1033009ffa8698016ff620c035fea166005ff94130047faa08804bfe624c02ffea1c600aff90a1004ff8c598007f81044025fe292600dff1443008ffe2098007ff214c40bfea04201fbfd953104ffaa798867fc21cc029fea8a6005ffc823009ffaa89804bff424c013fe1966201ff105310b7fe851801eff6444013fea9e6001ff0873102ffa601800afe624400dfe9922005ff8c03004dfec998063fd518c0137f31c2017ff5523002ffe211803bff520c013fe988601dff109310057ec89800efe6484017ff2a42020df54b3104ffea79802
  | 3 => 0x2012dc3c0480707825138230000501408000000002a0000c34000004150309c2c42f008071b03f0080303400004060bc4b02c050500d0b80e01417009110003e00400004010081f00004108030340c048010c4070000ab48080281800008084020880a00015018065406f1600203c250740808c42058000400e0100c1241d000050007e030000100100402000030dc770000218c2c0440008019038000000019c020d4000042b0c82302c05000170184c0040110400194180f4000000d000007bc020000006c6801054058e90440a01002000180440416c2f0241d0681102ca60001a014000100a014a506ca509c0105d0b0141a044280e01711c003c00507870030050001a1e802000036b00f028000000009c320140c028170940802c060280000aa31c00b01449714110a43500c9200c0d000341283300800008171601d0ac8a1b4040140200c01008dd0002200414058180000bff2022005ff1961000ffc629887fff504c4013fb2a6205ff9903002ffacb08007fc2184015fea142001bfd8d3102df8c918027ff430c00b7fb2c2005bfd943002dfecb18067fc51cc019fea9c2000dfd953104ff8c198843fd510c0037eb0e620fff5503004ffc6398006fe618c019ffa9c200fff150300effa409886efd64cc003ff90c2001ffd4610037f8a48806bff52cc031fea9c6001ff9061004ffe6098017fd648c00bff9006009ff14c30107ba6598807fc51cc40ffea1a200edfd483004ff88718012fc654400bfe0866009ff10d30015fcc518007fc10cc435ee9966009bfd8b3008ff8c2980027f654c003fea8a2005ff0c11002df8c318017f41044003fe18a6209ffcc53002ffe611801ffc544403dffb226206ffcc91000ffe2088033fe5384013ffb266206ffd0910005fac198817fd640c00bfeb0c6011ff08530107fea598817ff6484003ff10a6205ff88230045feca88017fc504c00bfe2846005ff8813004ffecb9801ffd5444013fe30e600ebf5883002df8c81802afd6284001fe31a2006ffc8110115facb9882bfc4284025fe3126007ffd0d1004ffcc39800afc6244003ff28e6209ff5933102ff8811803bfe420c0137e32e6013bfd91300a7faca9800efe644400bfe1066006dfd49100a7faa698027fe60cc4017eb086005ff5003002ff8c218006ff614c443feaa66205f7cc230045faca88017ff618c015bea942017bf592
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf6558131024fe7558430006dd4358e10004fd725843002ef41058430004bf7458d10006bf65d91300067d62d9531014fc725843015e7f30d95310067f62d95100067f5258d10006df5358e101567c10d953111e7f71d9510006bc62d91300067f6598d100067d32d95100067f32d95100067f70d9531004ff72d8131006f7515863004ef7315843013ebe73d9130004fd72d85301267f41d9510014fc72d81310067d40d95310067d20d9510006bc52d91300067f5258730006bc21d913002cff71d8d1001cbe76d91300067f10d9530006de32d8d1002cfe70d853008ef631d85300067f655853000cfc76cc1100067c74d953109ebd30d91300067f654c5301567c21d9531006dd3258e100077521d951000ef6614c630006f551584300cefa10d813101cfc745873001cfe74d8131006bc71d91300067e64d95100067f74d9530004ff74d81310e67c65cc1100067c6558d1014e7f30d953002ef77158630004ff7458d10006df3258e101277621d9510024fe75d8d1008ef661d853002cfc70d8d1001cfc74d85301267e71d9510004fd7258e101267d21d95100067f52d81310067c6518d100047f72d953000cfc73d85301267f21d9510024fe7558e10005ef7258131005f7714c110006f54158630024fe75d85300067e62d9530024fc7558730024fc75586300067c65981310067d40d9530004fd75d8131004fd7258d101577431d95311267e21d951002ef410586300067d5258e100aef64158630004ff75d85300067f64d951000cfc71d8d10014fc7258630006bc72d9130005ef7258d10004fd75586300067c62d95300067d71d95300067f74d953108cff7158d10006dc5358e10006bf53d913002ef61058630014fc72d853011e7c30d95100067d74d951002df8704c53013fb830d91300067d62d953000cfe764c110004ff72584300c57c754c63014e7c73d95300067d43d95300067c74d95300067e72d95300057f754c53002cfd70584300067f40d951014e7c43d9530006bc65d913008df97098d10006bd32d91300067c32d95100067d72d95300aef63158630006bc51d91300067c21d9530136bf73d9130004fd725873004edf325833102ef61058430014fe72583310a67d30d95300067c7558430004fd72586300067d32d95310077541d9510024fc755843000cfe76cc11000df671cc11006ef641584300067e62d95101467f73d953013ebf32d9130024fc75d85300067d43d95310067c65585300067f74d9510006bc7458d100f5bc745813111f7410d95100edec725813102edc3058e100067e43d95100fe7c654c530014fe7258e10006bf72d913000cfc73583311567d73d953113ebe53d9130006dd325833111e7c10d9510014fc72d8d101267d41d9510006bd20d91300067f5258e100a67c654c11001cfe7458e10
  | 1 => 0x8d100067e32d95311567c71d95310067d70d9531136be10d91300067d64d951000cff764c6301467e40d953004edc634c110006fb609813115e7c30d95310067c70d95310067f20d95310067e20d95311567e10d95310063f65d91300067d40d95100067d64d953013ebc31d9130006bf20d91300467e76d9510004fd72d81310075e43d9530004fd7558331004ff7558430006bc75d913002cfd73d853001cfe74d8530024fe75586300067c74d951008edd3158e100067c72d95100067f755843004ef431587301467c70d9530136be20d91300a57c754c5300067c42d95301567e41d95310067d52d8131005fb704c630014fc72587300067c41d9530004ff7458630006dd32587301475e30d9530004ef7258d100067f42d95310067e62d9531024fe7558730006be51d91300067f6518131006f521584300067f64d95300067c43d95100057f72d9530006bd52d91300067e74d95300067c72d95300067f42d95301567f71d95311267c21d9510006bf50d9130005bf74585301567c31d953106ef6215843004cff764c11004efb70583310077a20d9510004fd7458630024fc7558d100057f72d95101575c31d9531006df3258d10006f721d85300067c65d85300067e74d951001cfe74587300067f52d8d100067d62d9510006dc32d8d10006dd3258d1001cfe74d8d10004ff7558d100067f72d9530004ff745873004ede6318d10004ff74584300067c62d95100cdfb7058d100067e41d95300067e42d9531004fd755843014f7b30d953003dbc7458d10004ff72583310067f65d81310067d5258d10004fd75d8d100457c754c11002cfc764c53015f7731d953104fd4314c5301467e10d95300067f654c11004cfd70d8530006bf10d91300067e72d953100cfe76d85301277b10d95100067f20d95301467e20d9530035ec7258d10004bf7458331006bf644c53009dbe76d913004edf3258730004fd7458e10006bf645853014e7c31d95300067d43d951001cfe74583310067c65d8d100cef7105873009ebd73d9130006bf75d91300063c65d91300067d74d95310247c7558430006df43d8d1013ebf30d91300067e64d9531006bf52d91300057f7558d100457c7558d10006be62d9130006df32d8131006f96018131006f52158630006bd53d9130004fd74d8131006bf7458331006dd32d8131014fc7258e100aef4515863004ef830583311267d71d9510004ff7258d100067f72d951001cfe74586300047f72d95310aedf31d8d10024fc75d8d1002cfe70d8d10004ff72d8d101567f10d953100df4714c110006be75d91300067d5258730004fd7558730004ff74583310fd7e7598131014fc72583310aef62158630006f541584300067e42d9530006bd71d913015e7c43d95310067d20d9531006bf71d91301567d31d95310067
  | 2 => 0x67c61d9530136be70d9130136bc50d91300067f42d95100057f75585300a57c755853009ebe76d9130136bc20d9130006dc43d8d100067f659813111f7610d95100057d72d9530006ef7258d10006bd65d91301267e41d95100067f73d951015e7e43d953108cfd764c11002cff7058430004ff725863013ebf70d91301267c31d95101567d71d953104ef731587300067d42d953114e7f70d95301277810d95100047f75584301567d41d9531006be31d913002df8704c630004fd74d8530006bd51d913000cfd735843014e7c32d953001cbc7458d10006be32d91300075d32d95300047f72d95100075f32d9530006be61d91301379c30d91300057f754c6300067c20d95310247e76d953008ef421d85300067d73d95100067e64d95300073f52d913004cfe76d8d101567f31d95310067f65d8d100067f20d9510004ff7558331005bf744c110006f5614c6300057d7598d10014ec7258d10006df634c11001cfc74d8d100067c40d9531006dd6318d10004ff7258e101267c71d95100067e72d95100063d52d913004edc63cc11014e7e43d953011e7e20d95100073f65d9130005f571cc110006be71d9130004ff75d81311567e31d95310067d42d9530006bd50d91300057d72d95100a67d70d95300067f52584300ccff7058d100067d525863009f9c73d9130004ff74d85301657e76d95310047d72d95301575e31d953101cfc7458d100067c6558131004fd7458d101467c10d95300047f7558d10136bc70d91301467e30d953004cfd71d81310247c7558d10024fc7558331004fd74587300067e42d95100057d7598131014fe72d85300067f62d9531024fe75d81311467e70d95300067c64d95301567d10d9531136be50d913014e7f31d95300067f72d95310057f72d95311467c40d95301567f73d95310067f43d95301467c20d9530004ff7558630004fd745833101cbc745833104efb30583310067f71d95300fe7e76d9531004fd74584300247e76d95311379e30d913001cfc7458e10006be72d91300057d72d95310067e31d9530014fe72584300067d72d951000cfc764c110004ff7558e100067f65d8530005ef7258530005bf745813102cfc7058e101567c41d9531006be52d91301267f10d95100067c73d95100067e40d95310067e61d95300067c62d95310075d32d9531006df6398d101475c30d95300067c65d81310063f52d9130014fe725873015e7e73d95310067f43d95310067d72d95310057f754c110024fc7558e101267d31d9510006bf7458d1012d7e76d951002cfd7058e100067f65cc1100067f6558d100073c65d913001cfc74d81310067c42d95310067e32d95300067f52586300f6bc644c530006bc645853013fbb30d91300067e74d9531004fd7558e100067d52d8d10014fc7258d100067f651
  | 3 => 0x43a0080600e8214c001980406400450020000002400000110000067802034010140e124190880000c0200000000010000809409004010040007c06000020101401000054050047a02812006fb7058d1001cfc745843004ef77158730004fd7558d10006bd72d913011e7e70d951002cfd71d8d10006bf62d913013ebc53d913002cfc73587300067d52583310047d72d9510006ec7258d1011e7e30d9510006de4358e1014f7830d95300067f43d95100067d42d951008ef461585300067f64d95310067c72d953111e7c20d9510006bd75d91301267f31d95100067c64d9510004ff74d8d1011e7c40d951002edf7358e10006bd21d91301567f41d95310067f7558d100077920d95100067e71d953015e7f32d953104ef43158430006bf21d91300fd7c75581310057f75581310075f32d9531024fc75d81311567c73d95310067e73d951002ef771584300067d74d95300067c7558d10024fe7558d10004ff725873000ef4614c5300047d72d95311267e31d95100a67e76d95301267f70d95100067c71d95300067d41d95300067e21d9530006be21d9130095ec7258530004ff75d8d1014e7f32d95300067d32d9530006bd62d913002ede3058e10006bc64d853001cfe745843006ef6515843000cfe71d8d101379f73d913015e7c32d953102cfc7058430005bf7458d1002cfc70d85301267d10d951008efa105833108edf3158e100067f40d9530136bc30d9130004ff7458e1009ebd70d91301567d21d95310067e32d951002cff7158430006bf51d9130004fd72d8d100067c6598d100067f52583311567e71d953103dbc744c1100247e76d951011e7c70d95100067f41d95301567f21d95310acfe7618d100079f32d91300aedd31d8d1013ebc32d91300067d20d9530006bc61d91300067d64d953102efa601813109dbc7458530006df7358d100067c64d9531136bc10d9130006df63cc110006be65d91301567e21d95310067f62d953011e7e40d95100067f52d85300067d52584300073c64d9530014fe72586300a57e76d9530004fd75d85300079d32d9130004ff72d8530014fe7258d10005fb704c53001cfe7458d10004fd74d8d1013ebc73d91300067e70d9531014fe72d8d100067c651813114e7e73d9530024fe755833101cfc74586300a67d73d953008ef710d85300073d52d91300067d21d9530006f7614c5300067c42d9510004ff75587300067f21d95300067f40d95310067d52d853002cfc70586301267c41d95101467c30d953001cfc745833102cff7058e10006bc7458331006df32d85301267d70d95100063c64d9530006dd32d85300457e7598d10136be30d913013ebf31d9130004fd7258331006f77158d100075d43d9530006bf64d8530014fe72d813102cfe7058e101277641d951011e7e10d9510
  | 4 => 0x178120082509c0401800000150041e000040040000c01068020e81e000020e41c04c0101c00014000000200c010001c1c400208000100205400000010e82600001590080140000c010dc180000a03c000000009804048001fc00004010140b05007000e50080000000018010000403402018000001b0a00712c2300400004000009400c02000020000201c0400c02008001c0000081500000000190941804c020005a13dc9018080f000018000000000410004102500a000300000000010004032b02e038000200000040000002a8040180b180000048a0000008004018151d80606402054000042405c016e002000020142794cdc00000418030040c0000301404020030081f0780905800000000001a018e800000004000040e0000708c04928010000d0000b060002d80005000000020980405c66020007b00008c000042100c0234c000000800048000b3074000041618800034000200001c0202c050080224c05002640000600019054110088b00c002a4070004c064
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8bf87483644c0031b906baac1988021f61f21d95300061e3aec898a600087d87c8365440010fd0f216ca880121fe1f62d95311354ec18e5b22600087e8710b654c00147d0ca96c89800297a0c72d95101be4f3b665b22600087d82dd56344001c38c8a1eca980021fa1c32d95100051ec20e5b2a2000e1c644cb654c06187ceca96c8980bb271d13258d101253cc00e5b2a2000a9e848cb63440010fb0f316ca988028f21120d953000536412c9b2a2000e1c6490f654c00147d0b30ec8980aa9760f70d95310051ec2cc3b22600087e878cb65440018eeeba8ac3180021fa1f6558d1000637b2ee4b0a600087e86dcb654c4590fd0fb2a62980028fe1162d95101553b40841b2a6200c3c65dd13044001878c9baa62980ae97a0c20d95310a43ec38c5b2a6024a76811cb654400147f08b16ca980a7950c7654c5300061e3aec8b0a600087d8790b654c4018dee4a92c6880021f21d525843000636b90c5b2a2000a3d85c87644c001878e9b2a608800b331c93258d100051e422c5b2a2000c6c65dc9614c0018df0bb92c6880163d21d415843011d3ac08e9b2a2000c3d751d7644c0018bee739eca88002b32096318d100045fc3acbb22602ec9c744c960cc40717d0fba2c6880032b19372585300061fba8c8b0a600087f87593654c00117f08baac6880028f60b65d913004c6e41ae8b086029a5e83087654c00117d0e3a2c6880028fa1720d913013f0f29ea7b226000a3d85087644c00b1e90ea8ac2180031be0972d953000637b2ee4b1a2000a5d8318b654400147f08906ca988021fe1d62d95100061eba0e9b2a6000a3d848cb654c40b1ed0db8a60880038760c64d95300043ec3cc5b2a200087d87d0f654c4090f90fa92c6880039318932d95310043ec3e83b2a6000c6f75dc9634400147b09196ca880021f61f20d95300051ec20c5b2a2000a5d8390b654400717d0fba2c1988921fa1f20d951015d2f41ee1b2a6236a3d8594b644c0010fd0fa0eca980e3175cc65981310061f3b6cbb22600087d8798b654c0010fb0f396ca880030f5d074d95101764f3b265b226000c3f75d91314c0014db04206ca988028fa1262d95310045fc22eab0662008be87191614c00147b0432ec8980028f61262d95300061fba6a4b1a202ab54814cb654c4010ff0eb26ca988032b1d07258d100064e3a6e6b1a2000a3e85997644c0014eb023a6ca980028f61472d91300061fbaec8b0a600087e87103654c4051dd0fb92c6880030fdd15258d1013c5f43e21b226000a3e859cb644c0135a90690ac2180029be0964d95100051f42c65b226000cac72d91614c00187ecbba260880ae97a0c74d953111d3ac0ee7b2a2000c3c741956344063878e9a92c6880032bdd07258d100073231243b2a200087f855c9610c0014790ab16c898003175cc73d9510
  | 1 => 0x90ca1eca980021fe1d62d95311861e3a2a4b06622be1c4350f654c4018d8e5b2ac0988021f61c42d953000656390c8b0a6003c9c7450d63840554b90c996ca988121f21572584300070e32665b2a6000e4c624cb654c0018d8e432ac2980023ba1c7258d100243e42ae4b1a20008be87087644c0010fd0e32ac6880038be0952d91300064e3a6c698220028dc874c9634400195ee9b92c6880021f61c40d95310043f436e5b2a600087f855d163440135a906a0ac2180029e60021d953001c5e422e4b06622487c87d95304400147b0a316c8980021f60b7558430006563a6e4b1a2000c6c72d95634400147d0da96c8980ae97a0e42d95311443e436eab0a60018dd83dd7604c40117f08b92c6880030fd9774585300166639664b1a2000a5e8390b65440010fb0f396ca988ce2f21d20d91301543f43c65b2a62058f487485610c0010fd0e106ca988028fe1120d95300061e3a6cab0a6000c6f751c963440018df04b96ca988163721d3258e1002c7a43a42b0c6029a5e8390b654c06387ceda96c8980021f61f43d953015d2f418e5b2a6200ab980087644c001c68c8a0eca880029760c21d95300043f43ecab0a6000c6f825cb65440090ff0fb16ca980021fa1c72d95310051ec2e41b226000a3e851cb644c0010fd0fa92c6880030f9d865d91300051ec2621b2a600087d8799365440530fd0f906ca980021fa1c65581310063642ee4b1a2000a5c8358b654400117b0f886c8980021f61e32d95301345e436e8b0a600087e8710b654c40147d08106ca9881637a1f5358e100043f43ea4b086000c6c72d95614c0554bb06396ca988031bdcb5258d101452ec18e5b2a60008f7815c963440010fb0f326ca98003391cb7158d1000636b96c5b2a6200c6c65dc9604c4010fd0f216ca9880297e0d64d95100043ec3e87b2a2000a5f8358b654400147d09196ca988021fa1f65581310063632ee4b1a2000a3d849c7654c00b1eb03baec6880030f19372d95300051f420c5b2a2000c6f65dc9604c4014bd06316ca880121fe1f62d95100243e42ae8b086000a9d83087644c001878ea322c2980023be097558d100051f424c3b2a60008be87d91614c0474e90c90eca880028f61021d953001c5e422eab1a2029a5e831cb654c0010fd0f90eca980021fa1e42d95301371d286a1b2260008bd87147644c0014bb06396ca880029760c74d95100243f43eeab0860028ec825d563440010fb0f196ca880021f61c21d953012c3f436ea9822000a9c8458c63440014dd05326ca988028f21162d95300045ec3c65b226000c6c75dc963440550fd0fa1eca9889ea7a0c72d91301452ec18e9b2a6000a7581083654c401878c8b96ca980d68fa1452d91300243e43ea4b086000e6862483654400117b09b96c098802ad20562d913001476412e8b1a2034
  | 2 => 0xc7258d100062fbaea6b1c202aa7681103654c401878e832ac0988021f61c32d95100043fc2ae4b1a2000c6d72d8b654c00117b0e10ec8980121fa1b7558d1001636396a4b1a2000caf64dc9614c04f53d0610ec8980028fa1021d953001c5e422eab0662058f487505618c0131b906b92c2180031d1d5614c6301453d40043b2a6000a3c8654b644c0018dae4316ca988a697a0c74d953015d2f41881b2a620087e87087654c0010fd0e396ca980028fa1865d913014d2f41ee3b2a6000a3d8598b644c0090fd0fbaac68800237e0d7258d100061e32ee8b1a2023b708050765440018d8e432ac0988028fa1232d95101443f43e87b2a602387e871d5610c0010fb0f216ca880028f21120d95310061e3aee8b1a200087e8710b65440554ed023a6ca988028fa1421d913001c5f426e5b026200a3c8448365440510f90fb2a62980029de0562d95300043fc2ae8b086031c3c74d4960cc4514bb07b8eca980ca1fa1b754c5300052ec1c85b2a60008bf8758b644c0494ed023a6ca880a21fa1e32d95300052ec1841b2a62008df835d1634400187ee9a92c1988029ba0840d95310443ec38c5b2a200087f8758b654c001878ea3a2c6880021fa1b72d95100243f436eab0a6000a76811d3654c00187ee8a92c1988023be097458d100045fc22e4b066226aba80087644c0014db05326ca9880e2f2117258d1000636390cab1a20058dc835d561cc0010fb0f396ca980030f5d074d95310051f420e5b2a2027e9431d91314c051cd040906ca980021f61e64d953111d3d400e5b2a202aa5d831d3654c4014e902b16ca980021fe1d64d951015d3ac08e9b2a6200a3e85c87644c00147d0938eca980028f61020d95310043f43aa4b1a2000a3e848cb654c00147d0a316c8980029760e42d95310046f43e64b1a20008bd87997644c0010f90ea92c6880030fd9774581310043ec3c65b2a62268be878cb644c03f0fb0e316ca9888e9d60472d95100051e436a5b226000c6c751c9634400156f02b16c8980030f197745853000636b90c5b2a6000a7581103654c4014bb06206ca988c30f1d15258d100051f424c5b2a6000a3d859cb644c0474e90ca0eca880021f61c42d95310046fc3ac631a2000a3f8558b644c0010fb0e216ca880aa1f21b755813102c6e43a86b1c2000a5c8359365440010fd0fa1eca880028f61261d953011c3e436eab1a200087d87083654c401878e832ac2980a29721932d95301253c43241b2a2026a9c864cb644c00117d0e28ec8980031b5cb62d95100061fb2ee8b1a2000a3d8498b654c4010fb0f216ca980bf271d33258d100045ec3cc5b226000c3c74d95604c40717d0dba2c2980030fdd47458d100043f438eab1a200087e87549610c00147f08906ca880030f1d36558d1001636392a4b1a2000c3f75dd163440514b
  | 3 => 0x60100016060380000000b840460a000182c2a088480407020780c2301800d80046bac321f8507c6a20710100c2c0388c060108018060b1f840020003c906406001040603038340203050643e00000040a000b8446026008f4945a410000c000003c06d2168180c240786c13170c01408210c0040e0402008205801054001512828005e0f801be000b820021404048c8003080432002fdb0100103070040001528042c00000040037000090f90aba2c6880028fa1662d91300051ec2465b2a600087e87195614c0010fd0f906ca988021fa1c72d95100051e42ae3b226000a5e831d36544001878cbba2c0988028f61632d91300043ec3e41b2a6200a3e84c43654c05b0fd0fb2a60880121fa1b75581311253b40ee7b2a20008fb87580604c40147f0ab8ec89800333dc
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x105f985cc73d9510
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x3
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x1
  | 6 => 0x94b
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x4
  | 10 => 0x124b
  | 11 => 0x124d
  | 12 => 0x124e
  | 13 => 0xca
  | 14 => 0xcb
  | 15 => 0xcd
  | 16 => 0xce
  | 17 => 0x9ca
  | 18 => 0x9cb
  | 19 => 0x9cd
  | 20 => 0x9ce
  | 21 => 0x12ca
  | 22 => 0x12cb
  | 23 => 0x12cd
  | 24 => 0x12ce
  | 25 => 0x168a
  | 26 => 0x168b
  | 27 => 0x168d
  | 28 => 0x168e
  | 29 => 0xb4b
  | 30 => 0xb4d
  | 31 => 0xb4e
  | 32 => 0x16cb
  | 33 => 0x16cd
  | 34 => 0x16ce
  | 35 => 0x14c9
  | 36 => 0x134a
  | 37 => 0x14a
  | 38 => 0x1789
  | 39 => 0x130c
  | 40 => 0x17c9
  | 41 => 0x134c
  | 42 => 0x17ca
  | 43 => 0x14cc
  | 44 => 0x5ca
  | 45 => 0x14c
  | 46 => 0xccd
  | 47 => 0x170d
  | 48 => 0xd4d
  | 49 => 0x1a0d
  | 50 => 0x5c9
  | 51 => 0x130b
  | 52 => 0x10b
  | 53 => 0x9da15
  | 54 => 0x9cd55
  | 55 => 0x10c
  | 56 => 0x5c9d2
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 778
  | 6 => 670
  | 5 => 434
  | 4 => 1
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
  | 8 => 2*((h/48+packedAt gbK8 (1612+(h % 48)*6) 6) % 62)
  | 7 => 2*((h/273+packedAt gbK7 (28786+(h % 273)*10) 10) % 778)
  | 6 => 2*((h/363+packedAt gbK6 (32160+(h % 363)*10) 10) % 670)
  | 5 => 2*((h/151+packedAt gbK5 (25606+(h % 151)*9) 9) % 434)
  | 4 => 2*((h/1+packedAt gbK4 (70+(h % 1)*1) 1) % 1)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7fe0f01fff03ffffe0ffe01fc09e8e7c39f3f3
  | 1 => 0x83ff001f07fc3e01ff0fffe00769719e26ccfc
  | 2 => 0xfc3fffe007ffc001fff0fffff87181e3c70f1f
  | 3 => 0x3ffffff8000001ffff00003f81fe03f80fe0
  | 4 => 0x3ffffffffffffe000000003ffe0003fff000
  | 5 => 0xffc0000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x44010030900428c601120498002062c085171
  | 1 => 0x82a5010d43643414a90a4ac08328309622c4b4
  | 2 => 0x680a6620048a802112a0951618518140c50a0a
  | 3 => 0x2033bb56d0201049dccc01832d81da03780fc0
  | 4 => 0x423ccd98e6f339700808060437fc0003b7a000
  | 5 => 0x73000e0080c22180108018183effedf8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeee8faeae8e0feeaeee8faeae8e0feeaeee8faeae8e0feeaeee8faeae8e0feeaeee8faeae8e0feeaeee8faeae8e0feeaeee8faeae8e0feeaeee8faeae8e0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40425
namespace PEqualNP.Outside.L_meta_40425
open PEqualNP.Outside.L_meta_40425.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 26 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 38 := block_range (n:=38) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 134 := (concat bs1_4_0 bs1_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 48 := block_range (n:=48) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 48 := bs1_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 12 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 91 := block_range (n:=91) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 91 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_576 : Interval s2Atlas 4 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_672 : Interval s2Atlas 4 672 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_768 : Interval s2Atlas 4 768 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 794 := (concat (concat (concat bs2_4_0 bs2_4_96) (concat bs2_4_192 bs2_4_288)) (concat (concat bs2_4_384 bs2_4_480) (concat bs2_4_576 (concat bs2_4_672 bs2_4_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_672 : Interval s2Atlas 5 672 69 := block_range (n:=69) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 741 := (concat (concat (concat bs2_5_0 bs2_5_96) (concat bs2_5_192 bs2_5_288)) (concat (concat bs2_5_384 bs2_5_480) (concat bs2_5_576 bs2_5_672)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 42 := block_range (n:=42) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 42 := bs2_6_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 14 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 85 := block_range (n:=85) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 85 := bs4_3_0
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
theorem bs4_4_672 : Interval s4Atlas 4 672 82 := block_range (n:=82) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 754 := (concat (concat (concat bs4_4_0 bs4_4_96) (concat bs4_4_192 bs4_4_288)) (concat (concat bs4_4_384 bs4_4_480) (concat bs4_4_576 bs4_4_672)))
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
theorem bs4_5_768 : Interval s4Atlas 5 768 11 := block_range (n:=11) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 779 := (concat (concat (concat bs4_5_0 bs4_5_96) (concat bs4_5_192 bs4_5_288)) (concat (concat bs4_5_384 bs4_5_480) (concat bs4_5_576 (concat bs4_5_672 bs4_5_768))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 44 := bs4_6_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 59 := block_range (n:=59) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 539 := (concat (concat bs5_4_0 (concat bs5_4_96 bs5_4_192)) (concat bs5_4_288 (concat bs5_4_384 bs5_4_480)))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 88 := block_range (n:=88) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 664 := (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576)))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 1 := bgb_4_0
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
theorem bgb_5_384 : Interval gbAtlas 5 384 50 := block_range (n:=50) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 434 := (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384)))
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
theorem bgb_6_576 : Interval gbAtlas 6 576 94 := block_range (n:=94) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 670 := (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat (concat bgb_6_288 bgb_6_384) (concat bgb_6_480 bgb_6_576)))
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
theorem bgb_7_768 : Interval gbAtlas 7 768 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 778 := (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 bgb_7_288)) (concat (concat bgb_7_384 bgb_7_480) (concat bgb_7_576 (concat bgb_7_672 bgb_7_768))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeee8faeae8e0feeaeee8faeae8e0feeaeee8faeae8e0feeaeee8faeae8e0feeaeee8faeae8e0feeaeee8faeae8e0feeaeee8faeae8e0feeaeee8faeae8e0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809448 * 2 ^ 32 + 4209699040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40425.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,5]⟩,⟨.or,[0,1]⟩,⟨.and,[2,3]⟩,⟨.or,[2,6]⟩,⟨.or,[3,5]⟩,⟨.and,[1,10]⟩,⟨.and,[7,9]⟩,⟨.or,[0,8]⟩,⟨.or,[4,11]⟩,⟨.and,[13,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4209699040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4209699040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40425

open PEqualNP.Outside.L_meta_40425 in
theorem PEqualNP.Outside.L_meta_40425 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809448 * 2 ^ 32 + 4209699040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809448 * 2 ^ 32 + 4209699040) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
