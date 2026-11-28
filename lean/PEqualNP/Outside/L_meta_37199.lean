import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37199.Model
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


end PEqualNP.Outside.L_meta_37199.Model

namespace PEqualNP.Outside.L_meta_37199
open PEqualNP.Outside.L_meta_37199.Model
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

def SBf (j : Nat) : Nat := [7, 7, 6, 6, 5, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37199

namespace PEqualNP.Outside.L_meta_37199
open PEqualNP.Outside.L_meta_37199.Model
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
end PEqualNP.Outside.L_meta_37199
namespace PEqualNP.Outside.L_meta_37199
open PEqualNP.Outside.L_meta_37199.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x1a2441000006539b5e0000e28005a52c2088c120150a464cf000e61683081802c1e990a2500400038ac0173e354955c74282480000440c0000381007003242ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x1a800ce4f0011c84481f940740007024387a05040967900138760d001b0f6590914c4c6d19060c2221495834392489c5e5f0583c66771b800b841300104a2326044a4623a8c00c40420003e0039814001e01874001b2c1b8007d00000d20000000486a38000002100000004d098b802432f110f86300050002d330d832001f0d0fe5a0b8588a08002142a552e8a8007e1c1280e723b0ace86f1620d02020000104681e9e1005b189945054231907857288801871358083c8040008800640800b0081c00000c0c88080818000000000c180864280424180024f8480c283c2c3c3c467ca721cf54a439ea8c873e5090e7ca621e794c439ea90873d5110e7ca021cf94f429ea8e853e50d0a7aa92157d4d42ae29a859f5350a78a6a16714d428e29a85af5250a7ea2a14f141429f2a0853f54cca78a9994f952329eaa4659c438caeca3195d546329faa2653c544ca7ca8194f55032ce218653e53d067aa5a0cf943419eaa4835f53506b8a6a0e7d4d419e29a839c5350638a6a0cfd4941dba8a833c505067ca820cfd53319e2a6633e548c67aa918e710e31b7294636d528c67ea898cf151319f2a0633d540c7388618cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710cf951219eaa2433e540867aa810f948421af29c815d539027ca7206794e408f29c819d539027aa5204f546409f284813e531027aa4204f544409f28081ba501027ca9984f55330ce21e613e548c27aa9184fd51309e2a2619c434c2dea4985b14930bba8a6174514c27ea8184f150309f2a6413d54c827ea9104f152209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209f2a6213d54c427ea9084f152109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x2e020b2818040039c6a601602a024032794c0048008c02260a2040003890071428718d51d0a1e63943428d58454ccb14439463287594430ca8d6210c328718d52d061e63943418b58854cc70c4394a3187594430c6956110c318718d544863860551218718d540861c63548408718d511030c4314930c510c514c21e63d50308b588540c23561150308718d54c821e63d52208718d54c421e63d5210
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
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s1K5 (864+((h/16+packedAt s1K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s1K4 (3970+((h/44+packedAt s1K4 (3618+(h % 44)*8) 8) % 161)*9) 9
  | 3 => packedAt s1K3 (1036+((h/8+packedAt s1K3 (988+(h % 8)*6) 6) % 35)*6) 6
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 2 => 0xc0ffffc0fff83fff07c1e0fffe1fe07fd13e73
  | 3 => 0xff03ffff03ffc1fff801ff07ffe1ff81e1cf9c
  | 4 => 0x3fffffc0001fffffe0007fffe0001fe0fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x44100888209000002942410900222a280650a5
  | 2 => 0x92299106492270cb0290a8d2b2154154d12652
  | 3 => 0xa4aa2121a46135550213a44d5419505618b18
  | 4 => 0x2cb344a49074a5a69cf4108769980619ba0de0
  | 5 => 0x30c38738e38739f8e739dce071111861fdf000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaaaa0faa0aaa0faaaaaa0faa0aaa0faaaaaa0faa0aaa0faaaaaa0faa0aaa0faaaaaa0faa0aaa0faaaaaa0faa0aaa0faaaaaa0faa0aaa0faaaaaa0faa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37199
namespace PEqualNP.Outside.L_meta_37199
open PEqualNP.Outside.L_meta_37199.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x20df32dd32
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (34+((h/1+packedAt s2K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfe07fffffffffe07ff03ff03fffffffcc78fff
  | 1 => 0x7ff80fc07ffc0ff83ffc1ffc1f07fe0378f27c
  | 3 => 0x7fffffff81ffffffc0001ffffff83fff80ff8f
  | 4 => 0x80000ffffe000fffffffe0001fffc003ff03f0
  | 5 => 0xfffff00000000fffffffffffe0000003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x290a449104904014b412541250c62a84384b5
  | 1 => 0x143264872491565815550b550b46b41958b25c
  | 3 => 0x584149120d224aaa8092129a52d21953805b0a
  | 4 => 0x51658a24483a6b34e69a40921ce31063ad03e0
  | 5 => 0x61860c3871c38dc738e39ce380842182f6ec00
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeee00aa88aa00eeeeee00aa88aa00eeeeee00aa88aa00eeeeee00aa88aa00eeeeee00aa88aa00eeeeee00aa88aa00eeeeee00aa88aa00eeeeee00aa88aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37199
namespace PEqualNP.Outside.L_meta_37199
open PEqualNP.Outside.L_meta_37199.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x60040028a00be43bc43bf42bd42df32dd32
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2025aa421e350932
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
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
  | 4 => packedAt s3K4 (104+((h/2+packedAt s3K4 (96+(h % 2)*4) 4) % 9)*4) 4
  | 3 => packedAt s3K3 (56+((h/1+packedAt s3K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3ffc0ffffc1fc1ffc1ff07fc3ffc0fd8f33f3
  | 1 => 0xfc0fff03fffe0fe0ffe0ff83fc3fff02f1ccfc
  | 2 => 0xfffffffc1fffffff0000ffffffc3ffff01ff1f
  | 4 => 0xfffffe0000fffffff0003fffc0003fe0fe0
  | 5 => 0xfff0000000000ffffffffffc00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x48644628849284052d093424c0664258871171
  | 1 => 0x19248a19091094a0552854a1442a9608b144b4
  | 2 => 0x208910405221094a0210894a2a8128a300aa0a
  | 4 => 0xb2ca249243a52a739a520843b3100c335a0fc0
  | 5 => 0xc30c38e39c39cf9ce39cee70222230c3edf000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeeeee0e0e8e8e0e0eeeee0e0e8e8e0e0eeeee0e0e8e8e0e0eeeee0e0e8e8e0e0eeeee0e0e8e8e0e0eeeee0e0e8e8e0e0eeeee0e0e8e8e0e0eeeee0e0e8e8e0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37199
namespace PEqualNP.Outside.L_meta_37199
open PEqualNP.Outside.L_meta_37199.Model
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
  | 0 => 0x1ffc1fffff83f83fe0ff83fc3ffff03ec733f3
  | 1 => 0xe0ffe07c1ffc1fc3ff07fc1fc3c0ffc179cd9c
  | 2 => 0xffffff801ffffffc0007fffffc00ffff81fe1f
  | 3 => 0xffffffe0001ffffff8001fffff0001fe0fe0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x4244451104250808a849a124065290944310b1
  | 1 => 0xca48c321292129416942a50c4286a584594594
  | 2 => 0x491080a5242129410844a52a8084a2980aa0a
  | 3 => 0x94a2124a034a54e65290421b312c0309ac0f40
  | 5 => 0x18c39c739c739f3b9ce7738222308c31f7f000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xeee0eee0eae0eae0eee0eee0eae0eae0eee0eee0eae0eae0eee0eee0eae0eae0eee0eee0eae0eae0eee0eee0eae0eae0eee0eee0eae0eae0eee0eee0eae0eae0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37199
namespace PEqualNP.Outside.L_meta_37199
open PEqualNP.Outside.L_meta_37199.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x4817e53902faa7206f90e40de21c817e52902faa5206f90a40de214817e51903eca3205d94640bea8c81f551902eaa3206fd0640dea0c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037e84a06f50940bfa8a817c515037c82a06f10540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea9081be421037884205f94440bea8881bf411037a82205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc3be6598774cb30bf28e617d51cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa518778ca30ee194617e518c2faa31877cc630ee98c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa92617c524c3be6498774c930bfa8a617c514c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830f7290616e520c2faa4187b54830b6a9061de320c3b864185f94430fb2886176510c2faa2187d54430baa8861df310c3ba62185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f719641ed32c82fca3905f54720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3105f94220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53483dc64907b4c920bfa8a41f751482eea2905f14520fa28a417451483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2105f94020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c42faa5885f14b10fba0e21f441c43ec63887d4c710fb10e21f521c42fea9085f95210df2a4213e54842faa9086f552109eaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843f441087e48210fb88421fb10842fea8885f95110beaa2217c54442fea6885f94d10bea9a217c53442fea4885f94910bea92217c52443ee82887d10510fb18a21f531443ec42887d48510fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xe5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7c86a16f10d42f7a1285be4250afea2a17dd4542bba8a857c5150be8a2a15d14542bfa82857c5050afca8215f94c42bea9885bf4310b7a86215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccb7ca9994f95332beaa665bd54cca7aa9995f15332efa1e65dc43ccafca3997d94732bb28e657d51ccbeaa3995d54732bf286657d50ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbe86997710d32f799265de324cafea2995f14532bfa82657c504cafea8195f95032beaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483be42907788520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620ef90c41de218837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef99663dd32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631fb20c63f5418c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c7bc8698f750d31bfa92637c524c7be6498f74c931fb20a63f5414c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21fba0e43f441c87ec6390fd4c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e51087ee8210fd10421fb18843f531087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037c83a06f10740beaa
  | 2 => 0x280000023800000000a080008d1080a86d23c0007b45f98144c0007ca5937c000000003e000000000000000000004080006e09a24c5000000047e0000010d2a4000000000007e4001282c20006c800000710d680034a030000001600011b948212980c88000001c00008900000000229154824000000007a000000000000001ae1f41992fa4e2d46cc000b7000000000c227a8a9122104922d4a60e100014000000000000ef8003340010c0541301a4491a62ec8510000014224c0011800026ca3000100000929451ae2f91c01800057c0000004240c000000001b48ea85000000e48001947d40000004800069a3d00096c06891204449480f826c3809c962000a0c3c8001fe000000002d0001158000ae000df8002b653cf70002700000000000000000000000000dc00000000000000000114000d600000000000000804710b632c130001fa0004cc000003cc69c0022f31421800000424000001541200001c11f41a90c2d242000000002230003ac958a90203493b8080fe93d4003e000618001e50000007d8ce0004443980000068c739b64fa001490003608200a000060790000002840000023200018c128132629ec000000008b46f1d42820008e00012c000000003fc06400000000000b700000000000000000000000003e80003a0000000000000000031ce4036208000000001a0000fd8000fc000000000f41340010821c0000013e03a1a8d20cd005000008000030080080000000400c00000002000010060020000080400200801001002000010000020180000000200001800000008010000060000000000001400002002004010000020000000000c00000000002004000000000040080100000c028000020000000700200400802000000008010020040000400200c02800002000000000120040080700a000000020000000080200e000010060000000200000000002004002024030000000040080200000800800006008008010000080080100000400002000000018010060000200200000402000000004008010000080100000200800001002000000000140100000000600001800000000000000040000000100400400000004008028000060040080a0020080080400400000002000034030040020080580000000000800bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf28887f65110eeca221df54443faa8887755110efca021df54043bf29e857d53d0b7c87a16f10f42bf28e857d51d0afca1a15f54342beaa4857e5390bbca7215794e42bea9c85dd5390abaa7216fd0e42dea1c857
  | 3 => 0x2fa2ec5d0004d80000000010a0000b000000000000ab000000a8800218000000df000000000000008b000000368120de0940000012b9a10005340000037499cd40005280fc0000000000000000000564000ec000000000000000011d0004d200000000000555018000005c40000000000000000000000000000009c4000000007fc00000000000001cc000000b280000000067800000000000000949e40000015a00000000146000000ed2ea57800000000000000f0000828000001ec000000b8352000000000000cc7a0003306340000000651c5a2312da0000028c0000014580013c000000000dc29c0019f0007400014e0000013b0c34a2a54002250000f0000004689f894800000101208001d4324daa664dc00000000000994002192ac0000000030a00000000000490001ab0bca28881c70000100018008c83c00000000000ca00046a00000000508870000530000000015d0000010f000000000000003182b8058c42943c80000042e000002160741d83e0644982c50d85d0b8000000000004b06c000000000000b340a4c00004401e375438e60005ccd528802a23147800000000e19db1e2888000003ba0000000006a00080000000718000000000014300007a77000000190000000003b00010700044003800000000000001ac1aa0000888f480624c10290006e4c8000000148000000001540007b06867400000082a58000000000000026f4a422c0006b18c754e59d90000009da561a8000000002cc928301ca3a614490000000000001060000000000000000016a7c000000000bd00000079800000808fe8000b0000a992e42a254001f23ac000000004e600000000000000000000007f13a8e30fa25c00071000000210000009200000033c79c7e1c540e0b00000003c000000004c246800000000000000000c29fc118a80005ec9a12d000000fb000000000000000005680028106e00000083522000000000508f92f0000ca92c2f8000008e462800000000c400049a000000fe0000000000000000000000000000000000004bc57a1d0007a400000000000f9a681ca000f58f7000080b480000000000000000000001ea09600000000000220ca8000005d000000000004f018e0000008f006000299468000008b874000000950000000002b0000000000ac0000044e49c002330007383404f00000000230000708e08000920012311b4b00000020c2421e00027821410c000000000000000000062cbd2212ae4fc002454d40000004e22a270f101c3c6000cd97e0d8a4c002894da0004e913000000000000000008a1321dc0000025a4a6000000000003d4238670e400132000000000000003622e52200000000000000000000002720000009e06f0000000000000041c0017c00045c0d0000c40013d000000404fb80000027c0382700
  | 4 => 0x1fa4640008a2fe844000a20000e4001992d66c8002700004140000000042c00000000648000e43a4610ef03b1d2000000000000000000040c000000003e287cc38000000c40002e296000bc0b22ee000000000004dc0025d000008e6800000000001430000000002f0006700012300029000000000000001630007009500a32e000000000000000021a2c8744b7800000000001440009ac87800000000ed0000000000016000060c2d9ec2e4570410000004e8000000000011d80000084d4ba36198954d01a24a00005e000000000000000000013a081000000a48001a2000609d72ce540000a000091d0580003e4d4000000000000000000000000056244000000c00000000000036e21c0000000000000158024000001af000000b80000000000007500000000032000000f7a284b8000000000000000000000029400000000000000172f2000658001de000c785937a02400000000098001161b61dc1128e00098c0000000000131000000264fc0002d8784001cf0000000001b3266ec00000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1310c34d524c430d5945310c34d52cc03097d95300c29c644c030d3549300c27b654c0309798f54c825d63d53209dd8554c827461553208f99353c823d64d4f208f99253c823d6494f209d98653c82756194f208fd9151c823c64547209d987548827561d522097d8d548825c63552208fd91538823c6454e208f990538823d6414e209d98453882756114e208f992518823d64946209798e518825d63946208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e6515120c7d53534831c54d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f19153482776154d209d185534825e6514d20c7d50534831c5414d20d3588534834c538c9209b195324833754d4520cd153514835753d4520d514f51483375414520cd15051483575314520d514c514837160145209798f540825d63d50209d987540827561d50208f596540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209b98853082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510834d53c8020dc546200826f6548020d354d200827b6548020dc545200825e63d53109758f54c433461553109798c54c425d63153108f99353c423d64d4f10c795253c431d5494f10d598653c431e5454f10c755153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6414b108f59052c425e6314b109758c52c433554d0710b558c41c4335548c710ad19131c4335544c710d594d31c42b464487108f993538423d64d4e108f990538423d6414e109b988538426d6214e108f993528423d64d4a108f990528423d6414a109798c528425d6314a10cd95321843365408610bc58021842f06148210cd953108425f63551109718d544426f62551109b189544423f6454d108f191534426f6254d109b189534423e6414d108f590534423f64549108f191524425f63549109718d524427761549108f990524423d64149109798c524425d63149109d99741442d563105109d19531442b4644c510bc181314427665885109d19521442b464485109e19520442b664841109d987540425e63150109758c540426e62150109b588540423f6454c108f191530423e6414c108f590530426e6214c109b58853042766114c108fd91520423c64548108f990520423d64148109798c520425d63148109d984520427a60148108f992510423d64944109798e510425d63944109d59721042756508410bc580210423e64940108f592500427965840109dd95100427b6544010
  | 1 => 0xc67960d52318fd91528c63c6454a318f992508c63d64942318f992544c63e6515131c758c544c7356115131c7152434c65c6550d31a7593324c71c54cc931b5987324c71c544c931d3149324c7345490531e590e414c6746550531e550d414c63d65950318f990540c65e63150319d984540c71d54cc431cd552310c65f654c431c7551310c677654c431cd551310c65e63d53219758f54c863e64d4f218f59353c863e6494f218f59253c86d56310721ad19131c863f64543218f19150c865f63543219718d50c865e63152219758c548863f6454e218f191538863e6414e218f590538863e64942218f592508863e64951219dd85544863e65151218f992534863d6494d219d586534863f6454d218f191534867b6054d219e181534873454c85219798f540865d63d50219e983540867960d50218f596540873461550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d5986530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c21cd55341086756510421b558c4108675658c421cd55231086b4644c421cd5513108756534c4219bd9521086776548421ad191210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d50087734154021dc10550087723154021dc4c550087722154021dc485500865e6394b409758e52d02b46150b40a758c41d02b56110e40a798e429025e63946409758e51903566394640d558e51903364394640cd10e51903364294640cd10a519033651d0640cd945419033651d02409d98453502756114d40d598453503556114d408f997435031c53d0d40c714d435023e65d0940c714f425031c5350940ad185425031c53905408f994415029d6310540c714c415031c5390140ad986405023d6590c40ad584431027761548409d185521023d6590840a798e421023f65504408fd95401029c63500409ed95401027661153309d58454cc23e6494b308f59252cc23f64547308f19151cc27661d52309d587548c2d56110e308fd91528c23c6454a309dd85528c2746154a30a7992328c23e64946308f592518c29c644c6308f992544c25f63551308f994544c25e65cc930c7153324c31c544c930c7152304c26e62d50309b58b540c27661d50309d587540c23d6595030c718d540c23e64150309b988540c26d62150309d984540c2756115030c7553430c25d6510c30b5584430c32e5494830cb552520c32e5454830cb551520c34f4354830d310d520c25d658c830a7992320c34d528c830d3548320c3365494430cd552510c3665294430d954a510c3365454430cd551510c3665254430d9549510c31d54cc430d354b310c29c644c430c755
  | 2 => 0x16a1bc000d31590000000007200000000154218331090000000009c14e2980005e0890006c4000000007e00007f00051c0000001c001051290ea000000000002608800029400000000000000000c40000008882f000000f10d6000000d38080000010d00000000000000000000000971026f8000c70003c0001550600005b8760001ecf500000026400000000000018800a665c000001ee00000144000158b49983e0000ef9c139a000f29fb22a000a28000006ac960b90000000000008a0000000037a140000000000000000000000000000000000000000002081700006c000000000000010300000000082000184000000000000003194f1c22d09d00024c4f8900ba1e86b4000330020000040000400000000000000010000010000040000000200000001000000000000020080000000000000000000000000010200000080000a00000000002008010010060000000000e00002807004004000010000000080000000001001008008000000000080000000a010010030000000080200000c000000000000000000000c0080100c00c000000020000000100000002002004004010030000040080000001c0000500200c00003000004000040000200200500000000800002000000000000040000100001400004000004008010040000300101c0080000000400400000000000000000080080000000002800003000002776154b439d18552d0e7661943439d58650d0e3f6550c4397d954310f374354443d590d5110f354354443d550d5110eb56110f429d98650d0a7561943429d9865390a756194e42d59865390b556194e42c794f4390b1e5350e42c794f4290a3e6510d42ad5844350a9e63909429798c5150a5d6314542d598c5150b556314542cd90c5150b344314542cd9085150a3f6550c428fd954210ab461508429bd954210a5f63540429718d5010a7661d53329d58754ccb1c63553329d98454cca756115332c755343ccad56110f32cd95251ccb355494732cd95151ccb355454732c7953328ca7761551329d185544ca7b60551329e181544ca5e65d0d32b5584434ca9e648c9328f990514ca3d64145328f990504ca3d64141329d984504ca7561141329798f540ca7661150329d584540ca7a60150329e580540ca3e6494c328f592530ca3e64948328f592520ca5f654c8329bd95320ca3f64544328f191510ca3f64540328f191500ca5e6394b419758e52d06b46150b4197d8d50d065c6354341ad584439069e6390a418f997435063e65d0941ad185425063d6590c41c754e431071d5310c41ad584431063d6590841a798e421071d5390841c754c421071d53d0441d554e411063f6550441c754d41106776550441d554d411066e62d53319b58b54cc63e6494b318f59252cc69d64ccb318fd9150cc63c64543319e983548
  | 3 => 0x248000000000017d35c1e464000000228000a5000000000000005480002a12c168002142c6000000000a220c000463e45841280036e12ce59790007700000000042c00000000000568001ec000308ee0000b0000002e65f0ee800282000908000fc000ba8001de000bd9130000b40000000068c9a9e30000009f9140000000000013a1f0001170000000000002e00000000344000e2000000000000c608400000000000000001a03da744ff133000000980640001bc000003b0000a10000cc730001b500000100211000750ae01d3ec000000eb3de00000203000520000da192218d501142c6241595d1366b0e51570164f400000000000c4176000098000921fa0005190f254000a300a1f83fc740000003e468800000000dd9160003b40004007e0005912200000000000000334e40000000000003d29600000000000000000003420000003903408c00000000000b70000c0000000000007590b9a830478442000156000000000001ac9e05f000408000001b24b80007d0008209380000041c0000000083c4a00031c0004f80029a23c00000286000001f30000000020c36c3400000009c110ac000000234e71d912676c548000005240000000000006800000000001c212a00004800000000000000000002b9b3000000000001f66f00000000000000000000000d2800000104e995b0003a800000158000b58000dc000101fc0000140000023e19cdf8900b07144885925e0000008c2ac018c600000007c000000005680000000000000043194420000f30000000000000057c001ff000000001360000009a04726e500000000003c43816725639c470000005c80011e272000e317403800000000000000000000441b40a000000000000a6000000c99ba4167e42f0000000590c00000033c9d800000000458d3032271010000008640000000000043800224000000240002e00000000000000000110000000000002881c0001fc5a00000021a544c88f50000006089a0420006180000015000000000000ce19e00021400000000000000000f43c813800000000928e0000000000001c681c830001540008d98f0003000016433e000bc1eb0002fcf00bd2fc65409800000000f61e4000000a99843720000000013c0f0ca00000069000124000000eb9801b0810fe83b000400000310004c800000000000f718d000004f88a015070cc2800036000000ce0000000016c1d2000b0000000000570dc3d2000710690200005999200029c8e03a0000000000018a0007d0180007e85a800000000001310000005f01e0004602a800000348bd0d73ce000000b0250724388000005c10480016c0000000042a00000000000578000003640000011d0002ec918002cc5dc00000000000000001a800000105000740d780200000000
  | 4 => 0x1c8000d80000c4464d49c000000000183000000290000000000018600000000000000000000003687dcc5201000000001e60e6000509d52da000bf8000006680a8f8000748f4000316000000000000f800000050174e780033a0000000006e1a00000001e00000000064048b88001624286e9010000008180000013ccd80030e1a8760000000000000000000014a10000000000741be71c0000000000000000000640000000001dc00000000768000000006e00000033213000000000000b100000039400000090000039f41aa16d028000685400000032c1340000021c0001a8af000604658002ca00109865234000000e6000424001de1480009680000000000000000000021f5094030360780b8001070002de36c00000000834
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2cc20d3c01400150000042821804870005c044040000e0000000540000d360958000002004301455c65350e42a2ce7210a2a15157118d54cca4ab98c2a12838558d611513183aec2a66498d1573185540861a3b2a898843545cc4154021a60e898aa010d3074485500868b39c8528c81455ce5150640a2ae229a86a061453185425030a29cc320281455c46355030a8ae221aa41860e6454a320c20e3b2a89886183191524c430c18c8a9260185157318554c421a3b2a898e218c9516008610
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x68020815869ce4214542815869ce42946408158714c61509408158714e6190140
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
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (20359+((h/221+packedAt s5K5 (17928+(h % 221)*11) 11) % 1408)*11) 11
  | 4 => packedAt s5K4 (22451+((h/179+packedAt s5K4 (20482+(h % 179)*11) 11) % 1144)*11) 11
  | 3 => packedAt s5K3 (1273+((h/8+packedAt s5K3 (1225+(h % 8)*6) 6) % 44)*6) 6
  | 2 => packedAt s5K2 (244+((h/1+packedAt s5K2 (240+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x81fff83ffffe1e0f0fff87fe1fffe07c39f3f3
  | 1 => 0xfe0fffc0f87fe3f00f87f8ffe3c0ff82267d9c
  | 2 => 0xfff0ffff007ffffff007ff0ffc00ffffc78e1f
  | 3 => 0xffffff8003fffff8000fffff0003f80fe0
  | 4 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa420088a20102002028981120452212808b0b1
  | 1 => 0xca2918644a5065085c2c8a722864b0a225594
  | 2 => 0x10442210114800a51004120848089450c50a0a
  | 3 => 0x594ac424940d4b39a950408d932c0613700f40
  | 4 => 0x618c8738e67193cece6764c102301863bfe000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfae8eae0fae8eae0fae8eae0fae8eae0fae8eae0fae8eae0fae8eae0fae8eae0fae8eae0fae8eae0fae8eae0fae8eae0fae8eae0fae8eae0fae8eae0fae8eae0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37199
namespace PEqualNP.Outside.L_meta_37199
open PEqualNP.Outside.L_meta_37199.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12d50f0b1a6a317110001c00007803660014b11284020000400f10a9ca63e19d2f6e41a2c3629115481d5bb062ccb20815e80289400000491b30060e0d2638b9d4e38146800038000000d080042c1802a0400001ffd5007fe5401ff55007fc5401ffd4c07fe5301ff54c07fc53007fd0c01fe43007f50c01fc4301ffd48077f5201ff94807fd52005f54807fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc3201ffd4405fe5101ff54405fc51007fd0405fe41007f50405fc41007fcc405fe31007f4c405fc31007fc8405fe21007f48405fc2101ffd4003fe5001ff54003fc50007fd0003fe40007f50003fc40007fcc003fe30007f4c003fc30007fc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x64001fe8832000ff84190007ec20c8003ff8864001ff8432000ff82190023ff65480117fb2a4008ff9952001dfcca90023fd65480117eb2a4008ff1952001df8ca90003ff64480017fb224000ff99120005fcc890003fd64480017eb224000ff19120005f8c890023ff5448011ff2a24008ff55120047f8a890003ff63480017fb1a4000ff98d20035fcc690003fd63480017eb1a4000ff18d20035f8c690023ff5348011ff29a4008ff54d20047f8a690003ff4348001ff21a4000ff50d20007f88690006ff6248011ffa924008dfd492002ffca490023fd5248001bea924005ff14920007fe8490017fe4248001fea124005ff10920007fe6490017fe3248001f71924000ff4c920007da6490017fc3248001ffb0a4000bfd852003ffcc29000afe6148001feb0a4007ff18520015f8c290023ff514800fff28a4008ff5452003ff8a290003ff414800fff20a4000ff5052003ff88290003ff314800fff18a4000ff4c52003ff86290017ff214800fff10a4000ff4852002ff84290006ff6048003ffa824001ff9412000ffaa090007fc5048003ffa024001ff9012000ffa8090007fc4048003ff9824001ff8c12000ffa6090007fc3048003ff9024005fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007ff1048003ff0824001fe8412000ff82090013ff65440097fb2a2000dfd9510004feca88013fe65440077f32a2004ff59510025faca88013fc65440077e32a2004df1951001cf8ca88003ff64440017fb222000ff99110005fcc888003fd64440017eb222000ff19110005f8c888013ff5444009ff2a22004ff55110027f8a888003ff63440017fb1a2000ff98d10035fcc688003fd63440017eb1a2000ff18d10035f8c688013ff5344009ff29a2004ff54d10027f8a688003ff4344001ff21a2000ff50d10007f88688003ff62440017fb122000ff9891002dfcc488003fd62440017eb122000ff1891002df8c488013ff5244009bfa922004ff94910027faa4880037d5244009fe2922000ffd0910007fc8488003fd4244001fe2122000ffcc910007fc6488003fd3244001fe1922001bfd8510017fea28800bfe5144005fb28a2002ff54510027eaa28800bfc5144005ffa0a2000fdd0510017fc828800bfd4144005fe20a2002fd10510017fe628800bfe3144005fb18a2002ff4c510007ea628800bfc3144005ff90a2002ff88510017ec428800bfd2144001fa90a2002ff0851000dfec088007ff5044003ff2822001fe9411000ffaa088013f95044003fe2822001ffd011000ffc8088007fd4044003fe2022001ffcc11000ffc6088007fd3044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044005fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x7fc51cc001ffa0e600dff90730007fa8398037fc41cc00dff98e6006ff8c730037fa639801bfc31cc001ff90e600dff88730007fa4398037fc21cc0037eb066001ffd433000ffca198007fd50cc003fe2866001ffd033000ffc8198007fd40cc003fe2066001ff8c33000fbc6198007fa30cc003fe1866001f70c33000ffc4198007fc20cc003ff8866001ff8433000ff82198033ff654c0197fb2a600cff9953001dfcca98033fd654c0197eb2a600cff1953001df8ca98003ff644c0017fb226000ff99130005fcc898003fd644c0017eb226000ff19130005f8c898033ff544c019ff2a2600cff55130067f8a898006ff634c019ffa9a6006ff94d30067faa69801bfc534c001ffa1a6006ff90d30007fa869801bfc434c001ffb126000bfd8930007fcc498003fd624c001fe3126005bf18930067fea4980337f524c019ff292600cff54930006faa498033fc524c001ffa126000ff90930007fa8498003fc424c00dff9926000f7cc930007fc6498003fd324c001ee9926006ff0c930007fec298002ff614c017ff30a6002bf98530007fac29802ffc614c0057e30a600cffd453005ffca298033fd514c017fe28a6000ffd053005ffc8298003fd414c017fe20a6006ffcc53005ffc6298003fd314c00dfe18a6000ffc853005ffc4298003fd214c017fe10a6001bfd813000ffea098007fe504c003fea826001ff1413000ffe8098007fe404c003fea026001ff1013000ffe609801bfb304c003ff1826001f78c13000ff86098007dc304c003fc1826001ff8813000ff84098007ff104c003ff0826001ff0413002ffecb90016ff65c800bff32e4003bf9972002efccb9000e7e65c800bfeb2e400abf5972002efacb900027d65c800bfe32e4005bf1972002ffec990016ff64c800bff3264000bf9932002ffac990002fd64c800bfe3264005bf19320057fea99002bfe54c8015feaa6400aff1532002ffec790016ff63c800bff31e4006bf98f2002ffac790002fd63c800bfe31e4005bf18f20057fea79002bfe53c8015fea9e400aff14f20007fe8790003fe43c8001fea1e4000ff10f2000dfcc590017ff52c800bbfa964005ff94b2002ffaa5900177d52c800bfe2964005ffd0b2002ffc8590017fd42c800bfe2164005ffccb2002ffc6590017ee32c800bfe9964000fb4cb2002ff86590017ff61c800bff30e4002bf9872002ffac390002fd61c800bfe30e4002bf18720057fea390027fe51c8015fea8e4009ff14720007fe8390027fe41c8001fea0e4009ff10720007fe6390027fe31c8001fe98e4009ff0c72002ffe4390017fe21c800bfe90e4005ff0872000dfac190007ff50c8003ff2864001ff5432000ff8a190007ff40c8003ff2064001ff5032000ff88190007ff30c8003ff1864001ff4c32000ff86190007fe20c8003f71
  | 2 => 0x400077e87a0003fe43d0001fea1e8000ef50f40097f887a004bff62d0001ff3168005bf98b40007fac5a0002fd62d0025fe3168013ffd4b4009efea5a004ffe52d0027fea968000df54b4009ff8a5a004bff42d0001dfa168000ff90b40007fa85a0003bd42d0025fe2168000ffccb40007fc65a0003fd32d0001fe1968012ffd874008ffcc3a000afe61d0001feb0e8000bf58740097f8c3a000afc61d0027ffa8e8011ff9474009ffaa3a0047fc51d0025ffa0e8011ff90740007fa83a004bfc41d0001ff98e8011ff8c740007fa63a0047fc31d0001ff90e8011ff88740007fa43a0047fc21d00037eb068001ffd434000ffca1a0007fd50d0003fe2868001ff9034000f7c81a0007fa40d0003fe2068001ef1034000ffc61a0007fc30d0003ff1068001ff0834000ffe21a0007fe10d0003fe0868010ffd9540085fecaa0043fe65500077f32a8010ff59540085facaa0043fc65500077e32a8001bfd9140087fea8a0043fe5450021feaa28010ff15140007fec6a0002ff6350001ff31a8000ff58d40007f8c6a001afc6350021ffa9a8010ff94d40087faa6a0043fc5350001ffa1a8000efd0d40007fc86a0003fd4350001dea1a8000ff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a0016fc6250021ffa928010dfd4940087fca4a0043fd5250001bea928010ff14940007fe84a0003bf4250001ff2128000ff509400077a84a0003fc4250001ff9928000ff8c940007fa64a0003fc3250001ffb0a8000bfd854007ffcc2a000afe6150001feb0a800fff18540015f8c2a0043ff515001fff28a8010ff5454007ff8a2a0003ff415001fff20a8000ff5054007ff882a0003ff315001fff18a8000ff4c54007ff862a0003ff215001fff10a8000ff4854007ff842a0006ff6050003ffa828001ff9414000ffaa0a0007fc5050003ffa028000fed014000ffc80a0007be4050003fe2028001ef1014000ff080a0007fe3050003fe1828001ff8814000ff840a0007ff1050003ff0828001ff04140037fecb9801aff65cc00dff32e6003bf99730037facb9803afd65cc00dfe32e6006bf19730037fec99801aff64cc00dff3266000bf99330037fac998002fd64cc00dfe3266006bf19330077fea99803bfe54cc01dfeaa6600eff1533000dfcc79801bff53cc00dff29e6006ff54f30037f8a79801bff43cc00dff21e6006ff50f30037f8879801bff62cc00dff3166005bf98b30037fac598002fd62cc00dfe316600effd4b30076fea59803bfe52cc01dfea966000df54b30077f8a598003ff42cc001ff2166000ff50b30007f8859801bff32cc00def9966006ff8cb30037fa6598003dd32cc00dfe1966006ffd8730037fcc39800afe61cc00dfeb0e6000bf58730037f8c39800afc61cc01dffa8e600dff94730077faa39803
  | 3 => 0xf2826219ff541310c7f8a098863fe404c431fe2026218ff8c131037f86098863fe204c431fe1026202ffc4131017ee209880bfe104c405fe0826205ffd972102dfecb90817fe65c84077f32e4205df9972101cfccb90817fd65c842f7eb2e4205df59721004facb90817fc65c840b7e32e4205ffd932102dfec990817fe64c84017f3264205ff59321005fac990817fc64c840b7e3264217ffd53210bffca99085ffd54c842ffe2a64205ffd8f2102dfec790817fe63c840d7f31e4205ff58f21005fac790817fc63c840b7e31e4217ffd4f210bffca79085ffd53c842ffe29e4200ffd0f21007fc8790803fd43c8401fe21e4202bf98b2102ffea5908177f52c840bff2964205ff54b2102efaa590817fc52c840bffa164205ff90b2102ffa8590817fc42c840bff9964205ff8cb2102ffa6590817fc32c84057eb0e4202ffd4721017fca39080bfd51c8405fe28e4202ffd0721017fc839080bfd41c8405fe20e4202ffcc721017fc639080bfd31c8405fe18e4202ff88721017dc439080bf621c8405fe10e4202fb0872102ffec190817fe60c84037f3064205ff58321005fac190817fc60c84037e3064217ffd43210b7fca19085ffd50c842dfe2864216ff903210b7f8819085bfe30c842dfe1864205ff8832102ff8419080bff10c8405ff0864202ff043210affeca90856ff654842bff32a4203bf995210affaca90856fd654842bfe32a4203bf19521007fec890802ff6448401ff3224200bf99121007fac890802fd6448401fe3224200bf191210affea890857fe544842bfeaa24215ff15121007fec690802ff6348401ff31a4206bf98d21007fac690802fd6348401fe31a4206bf18d210affea690857fe534842bfea9a4215ff14d21007fe8690803fe4348401fea1a4200ff10d21015fec490857ff524842bbfa924205ff949210affaa4908037d524840bfe2924200ffd092102ffc8490803fd424840bfe2124200ffcc92102ffc6490803fd324840bfe1924202bfd8521017fea29080bfe5148405fea8a4202ff14521017fe829080bfe4148405fea0a4202ff10521017fe629080bfe3148405fe98a4202ff0c521017fe4290817f72148405ff10a4202fb88521017f8429080bec2148405fa10a4200ffd8121005fec090853fe60484037f3024200ff581210a7f8c090806fc604842bffa824214ff941210affaa090853fc5048429ff2024214ff101210a7fc6090853fc3048429ff1024205ff08121017fe209080bf71048405ff0824202ff04121097fecba004eff65d0027ff32e8003bf9974009ffacba004efd65d0025fe32e8003bf1974000dfcc9a004fff54d0025ff2a68013ff55340097f8a9a004bff63d0001ff31e8006bf98f40007fac7a0002fd63d0025fe31e8013ffd4f4009ffca7a004ffd53d0027fe29e8012ffd0f
  | 4 => 0x877fd5250401bea92821dff14941007fe84a0803bf4250401ff2128200ff509410077a84a0803fc4250401ff9928200ff8c941007fa64a0803fc32504057fb0a8202ffd4541017fca2a080bfd5150405fe28a8202ffd0541007ee82a080bfe4150405df20a8202ff105410177882a080bf44150405ff18a8202ff0c541017fc42a080bfc2150401ffb028200bfd81410e7fcc0a0806fe6050401feb02821cff1814100df8c0a0877ff5050439ff282821dff541410e7f8a0a0873fe4050439fe202821cff8c1410e7f860a0873fe2050439fe1028202ffc4141017fc20a080bfc105040dffb2e6206bfd9731037fccb9880efe65cc40dbf32e62039f99731037facb9886efd65cc40dbeb2e62009f59731037f8cb9881afc65cc40dffb266206bfd9331037fcc998802fe64cc40dfeb266200bf59331037f8c99881afc64cc437ffaa6621bff953310dffaa99886ffc54cc4057f31e6206ffd4f31037fca79881bfd53cc40dfe29e6206ffd0f31037fc879881bde43cc40dfea1e6200f750f31037f8879881bff62cc40dff3166205bf98b31037fac598802fd62cc40dfe316621bffd4b310defea59886ffe52cc437fea966200df54b310dff8a598803ff42cc401ff2166200ff50b31007f8859881bff32cc40def9966206ff8cb31037fa6598803dd32cc40dfe1966202bf58731017fea39880bfe51cc405fea8e6202ff14731017fe839880bfe41cc405fea0e6202ff10731017fc639880bde31cc405fb18e6202ff0c731017b8639880bfe21cc405fe10e6206ffd8331037fcc198806fe60cc40dfeb066200bf58331037f8c198806fc60cc437ffa86621aff943310dffaa19886bfc50cc435ff206621aff10331037fc619881bfc30cc435ff106621aff08331017fe219880bfe10cc405fe0866219ffd95310cdfeca98867fe654c4077f32a6219ff595310cdfaca98867fc654c4077e32a6200ffd9131005fec898803fe644c4017f3226200ff59131005fac898803fc644c4017e3226219ffd51310cffca898867fd544c433fe2a26202bfd8d310cffea69881bfe534c433fea9a6206ff14d31007fe869881bfe434c401ef21a6200ff50d31007ba869881bfc434c401ffb126200bfd8931007fcc498803fd624c401fe3126205bf189310cffea4988677f524c433ff2926219ff54931006faa498867fc524c401ffa126200ff90931007fa8498803fc424c40dff9926200f7cc931007fc6498803fd324c401ee9926206ff0c931015fec29880bff514c405ff28a6202ff54531017f8a29880bff414c405ff20a6202ff50531017f8829880bff314c40dfb98a6202ff8c531017bc629880bfc314c405ee18a6202fd0c531017fc429880bfc214c401ffb026200bfd81310c7fcc098806fe604c401feb026218ff1813100df8c098867ff504c431f
  | 5 => 0xc13211ffc4099017fc204c849ff8826423ff8413211ff82099017ff650c80b7fb286405ff9943201dfcca190177e650c8073f3286405ff59432115faca190177d650c8013eb286405ff1943202df8ca19017ff640c80b7fb206405ff99032005fcc819017fd640c8017eb206405ff1903202df8c81908bff540c845ff2a06422ff55032117f8a81901afe630c80dffa986406ff94c32037faa61901bfc530c80dffa186406ff90c32037fa861901bfc430c80b7f3106405ffd483202efea419017fe520c80bfea906405df5483202ff8a419017ff420c80bff2106405ff5083202ff88419017ff320c80bef9906405ff8c83202fdc6419017fd320c80bee9906406fb4c83202ffec219017fe610c8057f3086405ff58432005fac219017fc610c8057e3086422ffd443210ffca21908bfd510c843fe2886421ff9043210ff8821901bfe310c80dfe1886405ff8843202ff84219017ff600c80bff3006401bf9803202ffac019002fd600c80bfe3006401bf18032117fea019083fe500c845fea806420ff14032107fc8019083fc400c80dff1806406ff0c03202ffc4019017fc200c843ff8806420ff84032107f8201904bff65d043f7fb2e821fff9974101dfccba087ffd65d043f7eb2e8212ff1974101df8cba080afe64d043fffaa68212ff953410fffaa9a084bfc54d0425ffb1e8200ff98f41035fcc7a0803fd63d04017eb1e8212ff18f410fffea7a087ffe53d043ffea9e821fff14f41097fe87a0803bf43d0401ff21e8200ff50f410077a87a084bfc43d0425ffb168200ff98b4102dfcc5a0803fd62d04017eb168212ff18b410fffea5a087f7f52d043fff296821fff54b41006faa5a087ffc52d0425ffa168200efd0b41007fc85a0803fd42d0401dea168212ff10b41007fe65a0803fe32d0401fe9968200ff0cb41015fac3a080bff51d0405ff28e8202ff54741017f8a3a080bfe41d0405df20e8202fd90741017f883a080bbc41d0405ff18e8202ff0c741017fc43a080bfc21d0425ffb06821eff9834100dfcc1a0803fd60d04017eb068212ff1834100df8c1a087fff50d043dff286821fff543410f7f8a1a087bfe40d0425fe206821eff8c3410f7f861a087bfe20d043dfe1068202ffc4341017ee21a080bfe10d0405fe086821dffd95410edfecaa08037f65504013fb2a821dff9954101dfccaa0877fd655043b7eb2a821dff1954101df8caa08777c65504073e32a8202bfd91410effea8a0877fe545043bfeaa2821dff15141007fec6a0802ff6350401ff31a8200ff58d41007f8c6a081afc635043bffa9a821dff94d410effaa6a0877fc5350401ffa1a8200efd0d41007fc86a0803fd4350401dea1a8200ff10d41007fec4a0802ff6250401ff3128200ff58941007f8c4a0816fc625043bffa92821ddfd49410effca4a0
  | 6 => 0x7fe2a66406ffd4f32037fca79901bfd53cc80dfe29e6406ffd0f32007be879901bfe43cc80dfea1e6406ff10f32037b887990afff52cc857bfa966405ff94b3215ffaa5990037d52cc80bfe2966400ffd0b3202ffc8599003fd42cc80bfe2166406ffd8732037fcc39900afe61cc80dfeb0e6400bf58732037f8c39900afc61cc857ffa8e642aff9473215ffaa3990abfc51cc855ff20e642aff10732037fc639901bfc31cc855ff10e6405ff08732037fec19901bfe60cc8037f3066406ff58332005fac19901bfc60cc8037e306642bffd433214ffca1990affd50cc853fe2866429ff9033214ff8819901bfe30cc80dfe1866429ff8833202ff841990abff10cc853ff0866429ff0433202ffecb19016ff658c80bff32c6403bf9963202efccb1900e7e658c80bfeb2c6428bf5963202efacb190027d658c80bfe32c6405bf1963202ffec919016ff648c80bff3246400bf9923202f7cc919002be648c80bfeb246400bf5923202f7ac919002bd648c80bfe3246405bf19232147fea9190a3fe548c851feaa46428ff1523212dfac7190a3ff538c80dff29c6428ff54e32037f8a719003ff438c80dff21c6400ff50e32037f88719016fe628c80bffa946405dfd4a3202ffca519017fd528c80bbea946405ff14a3202ffe8519017fe428c80bfea146405ff10a3202ffe6519017df328c80df79946405ffd863202ffcc31900afe618c80bfeb0c6400bf5863202ff8c31900afc618c851ffa8c6427ff94632147faa31909ffc518c84fff20c6427ff1063213ffc631901bfc318c80bff10c6405ff0863202ffec119017fe608c8037f3046405ff58232005fac119017fc608c8037e3046428ffd4232137fca1190a3fd508c84dfe2846426ff90232137f8811909bfe308c80dfe1846405ff8823202ff8411909fff108c84dff0846426ff0423212ffeca99096ff654c84bff32a6403bf9953212ffaca99096fd654c84bfe32a6403bf19532007fec899002ff644c801ff3226400bf99132007fac899002fd644c801fe3226400bf1913212ffea899097fe544c84bfeaa26425ff1513212ffea69901bfe534c84bfea9a6406ff14d32007fe8699003df434c80dff21a6400ff50d32037f88699003dc434c84bffa926425dfd493202ffca499097fd524c801bea926405ff14932007fe8499017fe424c801fea126405ff10932037fe649901bef324c80bff1926405f78c932007fec299002ff614c849ff30a6402bf98532007fac299093fc614c8057e30a6425ffd4532127fca299097fd514c849fe28a6424ff90532127f88299093fe314c80dfe18a6424ff8853202ff84299003ff604c8017fb026423ff9813200dfcc099003fd604c847fe3026401bf1813212ffea09908ffe504c84bfea826423ff1413211ffc809908ffc404c847ff1826406ff0
  | 7 => 0x21017bf4290801f7a148405ffd864202ffcc32100afe619080bfeb0c8400bf5864202ff8c32100afc619086bffa8c8434ff946421affaa3210d3fc5190869ff20c8434ff106421a7fc63210d3fc319080bff10c8405ff0864202ffec121017fe60908037f3048405ff58242005fac121017fc60908037e3048435ffd424219ffca1210d7fd5090867fe2848433ff9024219ff881210cffe3090867fe1848405ff8824202ff841210d3ff1090867ff0848433ff04242197fecaa10caff6550865ff32a8403bf99542197facaa10cafd6550865fe32a8403bf19542197fea8a10cbfe5450865feaa28432ff15142007fec6a1002ff6350801ff31a8400ff58d42007f8c6a101afc6350865ffa9a8432ff94d42197faa6a10cbfc5350801ffa1a8400ff90d420077c86a1003fd4350801fe21a8400ef10d42197fea4a10cb7f525080bff2928432ff54942006faa4a1017fc5250801ffa128400fbd094202ffc84a1017be4250801ffb0a8400bfd854218ffcc2a100afe6150801feb0a8431ff18542015f8c2a10cbff5150863ff28a8432ff5454218ff8a2a10c7fe4150863fe20a8431ff8c54218ff862a10c7fe215080bfe10a8400ffd8142005fec0a10c3fe60508037f3028400ff58142187f8c0a1006fc6050865ffa828430ff94142197faa0a10c3fc5050861ff2028430ff10142187fc60a10c3fc3050861ff1028405ff0814218ffe20a10c3fe1050861fe0828405ffd944202dfeca21017fe65108077f3288405df9944201cfcca21017fd651085d7eb288405df59442004faca21017fc651080b7e328842fbf99042177fea82104bfe541085dfeaa08412ff1504202ffec621017fe631080d7f3188405ff58c42005fac621017fc631085dffa98842eff94c42177faa6210bbfc5310825ffa188400efd0c42007fc8621003fd4310801dea188412ff10c4202dfcc421017ff521080bbfa908405ff9484202ffaa4210177d521080bfe2908405ffd084202f7e8421017fe421080bf72108405ff5084202f7a8421003ed421080bffb088405ff98442015fcc221017fd61108017eb088405ff18442015f8c2210bbff511085bff288842eff5444216ff8a2210b7fe4110825fe208842dff8c44216ff86221017fe211080bfe1088405ffd804202ffcc021006fe601080bfeb008400bf5804202ff8c021006fc601085dffa80842cff94042177faa0210b3fc5010859ff2008412ff10042167fc60210b3fc301080bff1008405ff0804216ffe20210b3fe1010859fe0808406ffd9732035fecb9901bfe65cc8077f32e6406ff5973215dfacb9901bfc65cc80d7e32e6406ffd9332035fec99901bfe64cc8017f3266406ef993320057cc99901bfd64cc8017eb266406ef593320057ac99901bfc64cc80d7e326642bffd533215ffca9990affd54cc85
  | 8 => 0xf59443037f8ca2181afc6510c7b7f320863cffd5043097fca8218f3fd5410c25fe2a08606bf98c43037fea62181bfe5310c0dfea988606ff14c43037fe862181bbf4310c0dff2188606f790c43037fa862181bbd4310c01eea188606ffd8843037fcc421816fe6210c0dfeb108600bf58843037f8c4218f3ff5210c79bfa90863cff948431e7faa4218f3fc5210c0dffb088606ff98443015fcc22181bfd6110c017eb088606ff18443015f8c2218f3ff5110c77ff288863cff544431dff8a2218effe4110c25fe2088606ff8c443037f862218effe2110c77fe1088606ffd8043037fcc021806fe6010c0dfeb008600bf58043037f8c021806fc6010c79ffa80863aff940431e7faa0218ebfc5010c75ff2008612ff10043037fc602181bfc3010c75ff100863aff080431dffe20218ebfe1010c75fe0808600dfd9152006fcc8a90037d6454801be322a400dfd8d52006fcc6a90037d6354801be31aa400dfd0d52006fc86a90037d4354801be21aa403dfd895201cfec4a900f6f6254801bfb0aa439df98552006fac2a90e77c6154873bf20aa439df105521cefc62a90e77c3154873bf10aa405df08552006fec0a90e37e6054801beb02a438df181521c6fc80a90e37c4054871bf182a438df0c1521c6fc40a90177c2054873bf882a438df841521c6f820a904bff65d085f7fb2e842fff9974201dfccba10bffd65d085f7eb2e8412ff1974201df8cba10bfff54d0825ff2a6842fff55342097f8a9a104bff63d0801ff31e8406bf98f42007fac7a1002fd63d0825fe31e842fffd4f4217ffca7a10bffd53d085ffe29e8412ffd0f42007fc87a1003be43d0801fea1e8412ff10f420077887a10bfff52d085fbfa968405ff94b4217ffaa5a10037d52d080bfe2968412ffd87421bffcc3a100afe61d0801feb0e8400bf58742097f8c3a100afc61d085fffa8e8437ff9474217ffaa3a10dffc51d086fff20e8412ff107421bffc63a10dffc31d086fff10e8405ff08742097fec1a10dbfe60d08037f3068400ff58342005fac1a104bfc60d08037e306842fffd43421b7fca1a10bffd50d086dfe2868436ff90342097f881a10dbfe30d086dfe1868436ff8834202ff841a10dfff10d086dff0868436ff0434202ffecb21016ff659080bff32c8403bf9964202efccb2100e7e659080bfeb2c8435bf5964202efacb210027d659080bfe32c8405bf19642195fac9210d7ff549086bff2a48435ff552421aff8a921017ff639080bff31c8406bf98e4202fbcc721002de639080bfeb1c8400bf58e4202fbac721002dd639080bfe31c8435ffd4e421affca7210d7fd539086bfe29c8400ffd0e420077e8721003fe4390801fea1c8400ef50e42007f88721016fe629080bffa948405dfd4a4202ffca521017fd529080bbea948405ff14a4202ffe85
  | 9 => 0x40000000038014000006000801000000100000040000000000000000001000004800a0000010004004000000003000400000004bff65d0c7b7fb2e863dff9974301dfccba18f7fd65d0c7b7eb2e8612ff1974301df8cba18f7ff54d0c25ff2a6863dff55343097f8a9a18f7ff53d0c0dff29e863dff54f43037f8a7a184bff62d0c01ff3168605bf98b43007fac5a1802fd62d0c25fe316863dffd4b431eefea5a18f7fe52d0c7bfea96863dff14b43097fec3a1917fe61d0c057f30e8600ff58743005fac3a184bfc61d0c057e30e863dffd474322ffca3a18f7fd51d0c8bfe28e8645ff90743097f883a1917fe31d0c0dfe18e8645ff8874322ff843a184bff60d0c89ff3068601bf98343007fac1a1802fd60d0c25fe3068601bf183431effea1a1913fe50d0c7bfea868644ff14343227fc81a184bfc40d0c89ff1868606ff0c343227fc41a1913fc20d0c8bff8868644ff84343227f821a181bff6590c0d7fb2c8606ff9964301dfccb2181bfd6590c877eb2c8606ff19643035f8cb21902fd6490c87ffaa48643ff9524321ffaa92190ffc5490c0d7f31c8606ffd4e43037fca72181bfd5390c0dfe29c8606ffd0e430377e8721803df4390c0dffb148606ff98a4302dfcc52181bfd6290c017eb148606ff18a4321ffea52190f7f5290c87ff2948643ff54a4321ff8a52181bff6190c0dff30c8602bf98643037fac321802fd6190c0dfe30c8602bf1864321ffea32190bfe5190c87fea8c8642ff14643217fc832190bfc4190c0dff18c8606ff0c643217fc432190bfc2190c0dffb048606ff9824300dfcc12181bfd6090c017eb048606ff1824300df8c12190fff5090c83ff2848643ff5424320ff8a121907fe4090c83fe2048606ff8c243037f86121907fe2090c83fe1048642ffc424320ffc2121907fc1090c81ffb2a8640bfd9543006fecaa18027f6550c81ff32a8603bf99543207facaa1902fd6550c81fe32a8603bf19543206f8caa180e7c6550c81ffaa28640ff95143207faa8a1903fc5450c81ffa9a8606ff94d43207faa6a181bfc5350c01ffa1a8600f7d0d43037fc86a181bbe4350c01ffb128600bfd8943007fcc4a1803fd6250c01fe3128605bf18943207fea4a19037f5250c81ff2928640ff54943207f8a4a1803ff6150c017fb0a863fff98543015fcc2a1803fd6150c7ffe30a8602bf18543207fea2a18fffe5150c81fea8a863fff145431fffc82a18fffc4150c7fff18a8606ff0c5431fffc42a18fffc2150c01ffb028600bfd81431f7fcc0a1806fe6050c01feb02863eff1814300df8c0a1903ff5050c7dff2828640ff541431f7f8a0a18fbfe4050c7dfe202863eff8c143037f860a18fbfe2050c7dfe102863fffc41431f7fc20a18fbfc1050c0dffb288606bfd9443037fcca2180efe6510c0dfeb28863cb
  | 10 => 0x4000000000000800000d000000800200200000080000040010008002004001800000200100300080040040000000006000001000000000000a000000800000080040020000040010000000001801000000300080000100010000004002000004000000a001000002c00400300300000000000000000004000000000c01400200000000060030000000002000003000c0000000000008000007009800000000000a00000000010028004004004000000c000000000800c0080020050014000003004000400200700180140020000048024006004008001000000000000000020000000014002003000000400c00000100000000010000004000000000001000000000200180060040000000010001000000000000000180000000000010004000000000000000200100080000040030000000004000007000000000300200000000020000018006000000800000000000180000020000018000000004003000000000100080340040000008000000001000000c00000100180040000020010024000008000800400800200100080000000000000004001004800000200100000040040070000000006002004800000400d0008000008005000800c00200100000200020010000018002002000000000000000400000080010008014000002000002800000000200000020010018010000002003801800a0000008010002005000000c0000000018010006000000801c00400600180000040020000004000000002800000000500100000100010000004000002000800000a00000100000000090000008000001000000800800500100040000000010000002003000000000600000200040040020018010002000000800000800b000000000000200000040000090000010000000000800000400000280000020010000000006009000000000000200380080020040010000002000001001c00a0060000008000002001000800000000000080000010000000000006004000000400100000000000010020000000001000000c01c002000801c002000000000000000f0000004000000007000000000100180040040000000000000000000800800c001001000c0080020000004002004000004c010012000000800000a000800000000100080100000000010008000003005800000000200200040040000000010002006000000800200500080080020000008000006001000800401000a0000000002003000001800000400400000020010018000000001002800000000100380000080020018004000002000000800400200000000040000020004000002001000000a001000001c002001001000800000700180040020000000000004003000000800200500d0004000001000800400000000000000000000000004006000000001c00000100000
  | 11 => 0xa49bf000000033580006fc00041480000000000ea000000000014c8000d1673000000000005a71ba000000000000000000000001ab94f8000000000000080a14a13f89b858a13600019d00001461169730aec807000188c00009026d94ac0007e91f01eac0803ec00000008c263f000000000085d00000000000000000000cca000000185001a0003c41f1103c805000150400000000000000000003a305ec0004ce33f80004f20000000000000000000000082800000000ac00015721580000000000000dac0003622c8000000000000003844f400000000000003220001bbc07600000013a8000586189800000079f1cf00000006c900d0efc0e80002bd02dc0004f200000008fa00000008848ec0002b700010ac2b74168c3460c75300008dc76a00030b800014c09300000000006dd24a00000000000000a8c00000000000000008640000300b9e00035c800000020119d0408b8251b0000e348145190001a5000052600011b90247f502612400005593680afc00000000002ecba841d09290e8d627c63e980003f27f0000000000000000003e400000000018700000000000000000000000064800023c2f51ec4da65ac000046cd3802c1160080fce2f919300008c800000000000001ce00000002b400000004f85aa0000000000b964460d4000000000037a80011225e423919b00007da26a9e480000001778b2800000025a0828a3a1b5219145c93005f0001d8c60206c25598940000002cc11a08be0c31080001030000019800000038f00000000000000001b6400000000000000000000000000c7688d0000000e1e0003ae000025c1810000d1400000042c0000d4a03a0001e58ce05c700000000001f300014c8a1a1ae19480000000000000cd03fe67e00000000006d22ff00000001aa0f904400180001a01e1400000000007105ea6e1424053000000020b0000a580df22a8000d2435903522640ae23e0001370abc7e30000000f3669f000000010200000000005c8000000007800055800003d8e2e2131121c80dfc000000000025417c075800103e2b63428000000000000000000000000009800a0000000042c00000014296f40000001269214b9c00000017005a400032900000000ea1e69fac00040000000004a0000000000000046900000000000000000b7c72488400000000c818900011f83a654b000000000000020d00000006aa373800057a03f0000000a2a0003bb92e80000001a89cbc00000000012a80006fa1e20000002000001c006000001000c000001003000000400300100100000000018000006000001000400600000100000020000008000002001000000801600700080000020000020000004003002000800a0010000000014007000000c00400100400200020000000014002000000000400000300000040000
  | 12 => 0xbf009c00000000000440000b2c00001904e80000005b2439926827a000000000099e1b400015801c812240e80000000000000d189a80002331330c004a73e100e074a6c800000002e400000000010aa3b32e492281a80001d81e80a745d900012c0a06585000205c00020c09880009e200009d00000008472a01c60f7e0000001ee0a760002f080008d86cf0000000bda00000020ec5882551571a78c6a7dd2070cf047e5fb291055875c07739704800b2773037a1fc5223c541300003b200000000004d43540000c3c1a219a3e912e0bc06541c822240000390000000a4a7cb2a40760ae60000000fa87b800012f8aac0000c900018a801400000000002700001dc16f8754101117000111e7d92dd00000000000000000000676000124caaa3a3000000000000000018f865a00023c092c0000000db864433a1fb00c1b580000000001814000750000193800049f0c1000020a0000000000f5804b000000101e01b00018c4b6a3790000000a1c0003249e280ca1590b5800028800014401cce7c7de000000000049e0000b68c4270527e17a423a217275800102237a42b9df473e8492ba0c700000001c09e7800008f000000000000000000003bc4a60000000c9067d4171594b623f4345000000000000000000006f32d0000000000032d01b8f8a00000000000000000001e440002c8000000037e0f706f00000005f100000000000001f69914ba21a90001a10000000000000000000000006f800000040a1720000000000000063255a29418e87f80003b6107c56a0000000b4c0005fa0748000000000000000000042a00000000000002b58000000000000000000052e3db800078044e00012f4b5a000084061c00000000021f000000000000000004750000af0000000000144c00000038f82b40004961db00000006422e68000000000007891cdd047400009740000002a29e685b84910000f303cc7c900000004a484e000000000071925600000000001d21e8c8ce64c4318c30000000000000100043930509580000002d080000000000000000d3200039e8000992297000042490200000000009163253888f183c270c0000a1c0000000000000d941473d1216400067200001200000dc00000c400000000000000000000000fcc3f01c500000000001ad3a78000bfe00016e800000005c000000000047124d9aa428400017f9348b5c39900000c0000000439077441e6100000000d7e000000197cbae26b00000000007e1029000022800000000000000da0411f004043b700000000000003ea000070c000000000032e0001a7800000075d1ea0000000000000000000000000000000002f138400000942e803a8000bdc0002e800000000003299ad800000036f834000028d0000cec46600000010905ec00002a8000c5000005600000007bd3
  | 13 => 0xf0400000000021440005211e89c4800043802c0000abe6d70d9a064000000270857400074500018a4b7074e27280004860af0c6129013e7000ff1e947d00092769ed800000039d80000002f22cd000000031f0001c98db061a03f066452a61235a000000076900000010b600000000010600000000000d9c00000000006a4630000100400000000000004b85622e9025400072d3250cb800087100000000000000001e240000aa0ef9ca84d06ff2fc992c0000000940d20f2a00025b000000000000000000007f8020800000000000002247b44c3183868c0001c80db000000000000000004923800001f88000000000114499450910c07687f276139a8000b180003c81f6000000034e8000000000000000000000000000004ea000000090417e000000000000000000b138c000000000181000000035400c8d423721f38e9c0000b43780000000000000000049e0000000000ae22830000000000524298800060400000009e00e210c0b380000100000000000f680000001df07e000005f00000000e6000000000000044b149c00033d00002340420000000000772000000000000000000000000002e007980006226073700000000000000000000000000022200003840f899604ce13c0f204bcfec0003fe1b900000001958000d1a74a0000000bcc4d304d1b880001f014d0b3c2d25840aa952885270634188bc02448400015a4d2e54e3c0800000033827c800000041c40b03b03fa4e91b40000a8c00020300000000000000c600000e82118d5800000031002a44f81962fa9fa908a82c07e159ce7e000000000042a00000011800000000000b1c0000002c791405122a9000000025600003e9d5891c7280000aed0c47ec1149768e366152c980000000003fd8fd454c00000000000000001af88244b000026111dc0006360000d08000000000000098e1500461034f6666e000000000000000021707906b200006800000000b992700003883530c74b160c81b61cc80000000311e60000000000220097e0b80000c9014a7f240500004e4000000000000000000014102220002fb000096a23a00000000000003158dec56416c0000f9000034a36080000000002ad87bc06c60e27e8878eb677b2b600010840000001a544005bf1eb8b94bde35d29800000001ee057000000078339c8000756000106800025833000000000007a730621ec00000000003e88c42770000318000544000000000000003c800000000000000008780000000000000000224000000078b2bf0bf066e00000015580f81a71b9800000000000000005ac000000000000021a29b80000000001260000cd202d077802c95a6400000000de80000001de000000004b80000000000001df80001480000000906000000000000088b0000000efe4da0000000cc22282398000
  | 14 => 0xd098000000000000000000000000003940000b380002c6053800000000000009d86360d33959ce00ba1211d0835895c74400020048220003c98000d1000000000a000029200000000007af0000a4c0000000000ccc0006390000000000000309800000000000011100005c41ff8000c5e81510e84e40000000001ec00007d70ba81450e00c20000000000000000000001c0003009e5c0004e23b81274b5247c0540870e1244c01a941828667b000000064600000000000002461118000000000000000000025138a1360472308291968853e70d07a9e6507a37c14e8dc41b204d0ada25c00000000021e0000000000000065878f2669bec2cc31040d80009d800018200000000000b800000000000000000be00000000da85a20000001a685666ad0a7a150000501066202033653d1a720bc0000b3000118ccaa00012201e09be05618b800000039a185000000000000000000001c637b18cc00061b0fe045c42c4790d900000008221608000a9a75219a8f088762903410000e3c0000000000000000000010881280400000000000000001dd82fe25b175800055a208000160c0000000000000000641337839c554452000142c0000000339eb4796000000000091e5e3446065474400000000000000000bd050400022523795f40002274369ffc84a7ee0a980000004b2000225057400000000000006780001af09326f100016289d000000016a0000336099000046400000000000000fe0000000d840000000000ea80001511ae800044127b9e8400082b29ca2040000003e69ccc3a02a4449000000000000009cd10e0000b0014c7580002598000000126000000000074c000102c000000420a17872678000013c044c0801c3800039273c14e0f9512a6b02cd94bc9420000000000fee16f1a0800000000000000003da00017d1020c8883328000008040003ad00000000002e98d902344b700000000000001d0199c1c08750f600000000000000000a6c000000000083c00000000000000000819ab000000000000000000000000000000000177209047000000000000005533ed8000000152000000000000000004587745b30000410c9a00000000000000000000b6400000000012084a80c4110000000074000000003066b72ca000046c09801e198c0003fe000069400036138e80005d450f30f0a280c04fb000005000000000000001747fa3b3800091268c1ae0a9c7620000000968e040000000fd804e84a0ce0000da86a72f900000000000000000e625540ba00940000000000f280004a32ec00d000080c00000004e04a50e78bdc00050537584481ba8130c5000019e00009b8c48cb2000000000027e7240000f8800000014200000000002111bf4a2c589000177d07801c26b20940002640000b988f476f00022600003f10000000000017
  | 15 => 0x7340000bcc94059926b8684000000000000013c0000000000ffa0003dd80000006ae13a00000003ad00004a40007ef00005383c655d40d00009720000001a4437067500020180005a527b1d607cc00026f15dc23060b42980000000000e6904c2da4700001e380000000000ce50fa00000000008b20f427f041d0420000000000358269290132c00065700000007380011760000cd4367000000000000000002c00000000000d540000001940000c0c0002a900000003b41680b6cd560000000000fda36d0000000000000000000000022b41a8000000000000000000042815092bc00000000019800002052da1d7c00000000007700000000b700000000003b7191cb3c0002bd8c843ae4ff3e182644240131e98c0d0a456f1c5800000073a0001e90000000000000000072518b08d400035a0000000000000000202c0001d635c00000001b0000196c0006980000000b5488a05e8000c0400000000000000004308000dd200000002385ce0002180490f7c7c80001890b7620b00000002fc0003949c38afe20736611b46ee00000000006920000001ba8a1400000000990884420000000000000000000000000000006f40002f80001b4400000007e80010d2000035919400000000000000007b90000000106000000000000000000016580006b32b90000000557000073000065600001c10dc33e295016849c000000000000000000000000000004481dd48f627e38b0810e160003eb1b6c0000000710284000000411a1d8000000000000000000008f00007d66660000000d0c00014a186000008a000000111c0001be800108c0000000000000000000000000000011819c435e7ae0000cbc84200000000000d20000000000000000000000000000000000000000000000cc40000002e280000001e00000000e3800029f92a40006e622985880547e5000001818e271000000000000029a89640004270330000268000000000028a369436000025a00010c8000000000000224c7c60ce1e4800ce46000000136400000000000000000001c88e084c66a021f02903a200000000000000633b300008320000000000d020002fe000000081c000000000044d36308385501e71e8000110404e0cf0000500000000221800000021700005040003b000000000e5430124800000017e8fb8e4e000000044ce9a000147864069848800000007bc0000000d9800000000000000000000c421d000000000a808c0000000dd21f857255c2be1380e6e15e000000000051400001ecaf200000019cc12c6903281be02461f727213b8cc445e3e80614aa05e80001f1c9a28672c900007f618b000213c00051114080000001f60790000fbe5de002826c7363d64188000000000000000000008800001147de00041404eca8e6cd000000087e43700011f
  | 16 => 0xa3e00006a9dc42a280e000000000000000000000000001ea800000000014700000005f7000000029a834376939c00000000000000007c1000184400000030c88500001fa00013748b60004081dd00005420001d0800034431b82e40000c1415000039617d1d901fce6c3fa000000000048629e1a6c5188202540000b040000001b54b860000511bc861238c000000000000000000006343f81ed80000000000000000cf2435000007cb1a31517f0ebcef43a900002d4022704000028c47a30500000000006b500000000003bc2080000d1e00006b80000004d021e800000000042180003b600000000000000002ee00000081763b5000000000000000006162f024a83c01960003b69054a0e84d13da2140002062188ac0000000000000000003d00000000006be0000b080003632dc9b2c0000000001c0c00000000020f800000035e894c598000000165c9800003619f700f4000000000016235300020e400015f2238000f6452d2949b14b6c0000000ef40000000f4a1e80005eb00013bc73a45d316859453c6f70999bb004800007f993c0da00000000003d000000000000000003d4000000036f35195d4bc48320000d1c00046b00000000007d512500002a8000000000003a0002f280000000000000000e260000000e2400000019900000000000870000ac60001ad80000007cf41b8000e0200040680000000003b419b48800002130e60c7878d3da92010d63433a1987c6a05f40000900000376000000009e7f3171052450c7e00d200000000000b08000a6800000000000000000001c40b842222d580004840372b800a485a1860000fc800000000000005580000000000000000000160400019400009b40000000000000476000000000089200000012ecbac000000112c00017942f80007500000000000f3800000016541780000001be400000000000007ba00000021a067e6801ac0af80e4000396123400000039100000005a60001b700000003111d889e8866133130408e5880f2921c6fe7a907195a800018f33d0000a9200013107d437600000000000003d921780000000001bc182000000005580000004173139a883c43cf0fa11280007f911880000000d800000000002b81ec0001004000042800000082700015988b00002cf800000000002d85a80001c30000e3821a5dd2d80c00fcc09200000000003bb0d10ac400000000000009f40000e1000000000000000000000000000000092000000000000000000000009907591cb80005c245c00015840006e53a09f28cba0000001e1c00059100000009cc00000000000006e3246000000070714583c4c8c00004580008361c10001ff800018e000000000000000000000000000438bd000000031a0fdc97c00000018b82b81c00a007480000100000000000000307800059a00
  | 17 => 0x5db00015e000026c02f18c90701152f980010a00070000000ef21840000000b9400000000000000001ef8000d1c000000000000078228811583785d50000000d8059d00005a0000000000180c4902e9157a1680006ee2b2000000036e1c503b81081eb33200b8f980002fea12c000000209103c6c00002a18600aa2000000000100670a0b200000006c70f500003300000000000a186960d898b09f02c93aba0d86ea5c600000004bc04600000000000000000000cee00000000005b00000000c7800000000000001f6000000000000000031300000003950b18000ea20000000000fe86de00012f0000383000024400044f2621970e340000000000d0e1a6000194400000013784285ae7f100020244ae00025116000002a03e8925cf181771328f4886611f000000000035e3c211687c2000000000078e0000001420000000000000000000016f0000000000000000000034b3c300000000003218d94ed61301619d941a45bc2c3864d07e6091cb1fa0ad00a00769d20f74000357800043e54f0651ea800043400005e000000014c00000000002d190d8bd800012280000000000000000000000000046420c5e725890b09e640409a800000031426280000000000001c8405e000000000000000000000000000002a621e40000000001a904c20000000000c7083a00000000002ed3d3025074c10003b00000003ce38a818400000032f0e14d763fd000043cb380000000000cf800226300000001c743783344060000000000b48000000000045400031e8000436865093a2680000000000000b6e32706d808864000000000005c60000000000b1c0000000000a380000000754a3400000011510d40001df1a4c5f60003aa80000000b60340f0c0004200000000ee400015a04700000003de0a94c1a6c400014e00000f800011a800061d2b68000000000000000000000000008440005af2061e740000000000000db4000043115c31a1b90cf800000074b000000000000000005c400000000000000002d422280005360000001e50d124430590000a0414b00000000000000000000000883000000000000020380000a86160d589f4a300000ac14788307ce1600000cd034d00000f80000003a3800000004327a80000003e900000000001ca1b814cc6542960001d9000075e11a2100fc8000187000000000000000000000000000000000000289000000040343b800000000006280
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc65cc910005be74cc910005bd74cc910036de63cc910006dd63cc910006ef62cc91002eec62cc910015f671cc910005f571cc91002cff768c910004fe768c910004fd768c91002cfc768c9100257e758c9100057d758c9100067f658c9101467c658c910005be748c910005bd748c910006df638c910036dc638c910015f6718c910005f5718c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c91012e7c654c910036de634c910006dd634c910015f6714c91002cff760c910004fe760c910004fd760c91002cfc760c9100257e750c9100057d750c9100067f650c9101167c650c910006df630c910036dc630c910006ef620c91002eec620c910015f6710c910005f5710c91000dfa700c910005f9700c91000df676d05100f6f676d051000cf676d051026df775d051026df575d05100077765d05102677465d0510015f674d0510017b674d0510006f764d0510007b764d0510006f564d0510007b464d0510005f573d0510007b743d0510007b543d0510005f572d05102677752d05100077552d0510007b742d0510007b542d051000df670d05100f7f270d0510007f170d051000df470d0510016f760d0510017f360d05100f7f250d0510267f150d05100f7f220d051000df4764c510036f4764c51000cf4764c51025df7754c51025df5754c51000777654c51025774654c510005f6744c510005f4744c510015f7734c510017d7734c510007d7634c510036f6634c510036f4634c510007d4634c510007d6434c510007d5434c510005f7724c51025777524c51000775524c510007d7324c510007d5324c510007f3704c51000df6704c51000df4704c5100c7f0704c51000df0704c510016f7604c510017f3604c5100c7f2504c510257f1504c5100c7f2204c51000df4764851002ef4764851000cf4764851024df7754851024df57548510007776548510247746548510005f67448510005f47448510005f77348510005f57348510015f77248510017e77248510007e7624851002ef6624851002ef46248510007e46248510247775248510007755248510007f3704851000df6704851000df470485100a7f07048510016f76048510017f360485100a7f25048510247f150485100a7f22048510015f8764811002ef87648110014f8764811023dfb754811023df975481100077b654811023778654811000dfb724811000feb7248110007eb624811002efa624811002ef86248110007e862481102377b5248110007795248110007ea3248110007e93248110007f37148110015fa7148110015f8714811003ff0714811000efb614811000ff3614811003ff25148110237f15148110007f3414811003ff0414811003ff23148110007f1314811003ff22148110007f12148110
  | 1 => 0x891001cfc75d89100067c75d891001c7c75d8910094fe74d8910004fd74d8910034fe73d8910004fd73d89100067f52d891000cff71d8910014fe71d891000cfd71d8910014fc71d891028eef21d891028eed21d8910014ff70d891000cfe70d8910014fd70d891000cfc70d8910286ef20d8910286ed20d89100a4fd76989100257e75989100057d75989100067f65989100067c6598910006ef62989100a5f5719891003df9709891002cff76589100057f75589100257c75589100067f65589100067c6558910005bf7458910005bc7458910005df7358910005dc73589100b5f7715891004dfb7058910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910094fc7458910006bc7458910004bc7458910004ff7358910006df7358910004df7358910034fc7358910006dc7358910034dc7358910006ef72589100067f52589100b4ff7158910006f771589100a4ff7058910006fb7058910284fe76189100257e75189100057d75189100067f65189100067c6518910005be7418910005bd7418910005de7318910005dd731891002eee6218910006ed62189100067f76549100057e76549100067e76549100047e76549100067d76549100057c76549100067c76549100047c76549100067f64549100067e64549100067d64549100067c64549100067f635491027e7e63549100067d635491027e7c63549102757f72549100276f72549100067f625491002e7e62549100067d625491002e7c62549101cf7671549100077571549101c67f61549101cf7441549101cf7631549101cf7621549101c77a70549100077970549101c67f60549101c77a20549101cf7b10549101c77610549101c77410549101c7781054910094ff76d0910004fe76d0910004fd76d0910094fc76d09100067f65d091017e7c65d0910096be64d0910006bd64d0910006ef62d091002eec62d0910015f471d091002cff7690910004fe7690910004fd769091002cfc76909100257e75909100057d75909100067f65909101ae7c6590910006bf6490910006bc6490910005de7390910005dd7390910015f67190910005f5719091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101967c6550910006be6450910006bd6450910005f77150910015f4715091002cff7610910004fe7610910004fd761091002cfc76109100257e75109100057d75109100067f65109101767c6510910006bf6410910096bc6410910006ef621091002eec6210910015f67110910005f5711091000dfa7010910005f97010910034ff76cc910004fe76cc910004fd76cc910034fc76cc9100067f65cc91015e7
  | 2 => 0x34dc7359110004ff7259110006ef7259110004ef725911002cfc7259110006ec725911002cec72591100067f52591100f4ff7159110006f7715911007ef441591100e4ff7059110006fb70591102b4fe76191100067f65191100067c6519110006bd6419110094ff751911001cfe7519110004fd7519110094fc7519110094fe7419110096be7419110034fe7319110004fd731911002cfe7219110004fd72191100067f521911000cff7119110014fe711911000cfd7119110014fc7119110096bf41191102aebd4119110014ff701911000cfe7019110014fd701911000cfc7019110096bf40191102a6bd4019110034fe76d8d100067f65d8d100067c65d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10094fe74d8d10004fd74d8d1002cfe72d8d10004fd72d8d100067f52d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d1029edf31d8d1029edd31d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d10296df30d8d10296dd30d8d100c4fd7698d100257e7598d100057d7598d100067f6598d100067c6598d10006df6398d100c5f57198d1005df97098d10034ff7658d100057f7558d100257c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10005ef7258d10005ec7258d100d5f77158d1006dfb7058d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10094fc7458d10006bc7458d10004bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1002cfc7258d10006ec7258d1002cec7258d100067f5258d100d4ff7158d10006f77158d100c4ff7058d10006fb7058d10294fe7618d100067f6518d100067c6518d10005be7418d10005bd7418d10036de6318d10006dd6318d10094ff76d0d10004fe76d0d10004fd76d0d10094fc76d0d100067f65d0d101ee7c65d0d10096be64d0d10006bd64d0d10006df63d0d10036dc63d0d10015f471d0d10034ff7690d10004fe7690d10004fd7690d10034fc7690d100067f6590d1021e7c6590d10006bf6490d10006bc6490d10015f67190d10005f57190d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d100257c7550d100067f6550d102067c6550d10006be6450d10006bd6450d10005f77150d10015f47150d10005fb7050d1000df87050d10034ff7610d10004fe7610d10004fd7610d10034fc7610d100067f6510d101e67c6510d10006bf6410d10096bc6410d10006df6310d10036dc6310d10015f67110d10005f57110d1002cfe76d89100257c75d89100067f65d89100067c65d8910004ff75d89100067f75d891001cfe75d8910004fd75d
  | 3 => 0xd70d852000cfc70d85200b6f710d85200057f75585200457c7558520005bf7458520005bc7458520005df7358520005dc735852003ef46158520004fe76d0520004fd76d0520094fc76d0520004ff7650520004fe7650520004fc76505200057f75505200457c7550520004fe76cc520004fd76cc520034fc76cc5200457e75cc5200057d75cc52002dee72cc520005ed72cc520007cd32cc520004ff764c520004fe764c520004fc764c520007cd324c52000cfc7648520006f76148520016f46148520005fb704852000df870485202d57e76d95100267e76d951001c7e76d95100057d72d95102c77771d95102c77471d95102cf7441d95102cf7631d95102cf7621d95102cf7b70d95102c77870d95102c77a20d95102cf7b10d95102c77610d95102c77410d95102c77810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f72d95100067e72d95100067d72d95100047d72d95100067c72d95102c67f71d95102ce7e71d95102c67d71d95102c67c71d95102ce7f41d95102ce7e41d95102ce7d41d95102ce7c41d95102ce7f31d95102ce7e31d95102ce7d31d95102ce7c31d95102ce7f21d95102ce7e21d95102ce7d21d95102ce7c21d95102c67f70d95102c67e70d95102c67d70d95102c67c70d95102c67f40d95102c67e40d95102c67d40d95102c67c40d95102c67f30d95102c67e30d95102c67d30d95102c67c30d95102c67f20d95102c67e20d95102c67d20d95102c67c20d95102c67f10d95102c67e10d95102c67d10d95102c67c10d95100067f65d91100067c65d9110004ff75d911001cfe75d9110004fd75d911001cfc75d9110034fe73d9110004fd73d911002cfe72d9110004fd72d91100067f52d911000cff71d911000cfd71d91102b6f571d91102bebf41d91102bebd41d91102bef441d9110014ff70d9110014fd70d91102b6bf40d91102b6bd40d91100e4fd76991100257e75991100057d75991100067f65991100067c6599110006bf64991100e5f5719911007df97099110094ff759911001cfe75991100967e759911001c7e7599110004fd75991100967d75991100047d7599110094fc7599110094fe7499110034fe7399110004fd739911002cfe7299110004fd72991100067f52991100e4fd7199110096f571991100f4fd7099110096f970991100057f75591100257c75591100067f65591100067c6559110005df7359110005dc7359110005ef7259110005ec72591100f5f7715911008dfb7059110004ff75591100067f75591100047f755911001cfe7559110004fd755911001cfc75591100067c755911001c7c7559110006bf7459110004ff7359110006df7359110004df7359110034fc7359110006dc7359110
  | 4 => 0x8d20006df6398d2011ded7298d2014def7258d20004ff7558d2001cfe7558d20004fd7558d2001cfc7558d20004ff7458d20094fc7458d20006df7358d2014cff7258d20006ef7258d200067f5258d20004ff7158d20014fe7158d20014fc7158d2011cff7058d20006fb7058d20134fe7618d200457e7518d200057d7518d20036de6318d20006dd6318d20094ff76d0d20004fe76d0d20004fd76d0d20094fc76d0d20006bf64d0d20096bc64d0d20034ff7690d20004fe7690d20004fd7690d20034fc7690d20006df6390d20036dc6390d2002dee7290d20005ed7290d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200057f7550d200457c7550d20006bf6450d20006bc6450d20006df6350d20036dc6350d20034ff7610d20004fe7610d20004fd7610d20034fc7610d2002dee7210d20005ed7210d2000dfa7010d20005f97010d2001e7f76549201c67e76549201c67d765492001e7c76549200067f64549200067e64549200067d64549200067c64549200067f635492027e7e63549200067d635492027e7c635492002d7f72549200476f725492002e7f625492002f6e425492002f6e32549201ce7e61549201ce7c61549200077b70549201c778705492002e7f605492002f7b20549201c76e205492002f6c205492002f78205492002f6820549201c77a105492000cfe76d092000cfc76d0920006bf64d0920096bc64d092000dfa70d0920005f970d0920094ff765092000cfe7650920184fd765092000cfc7650920006bf6450920006bc64509200076d5250920005fb705092000df8705092002fe8205092000cfe76cc92000cfc76cc920005be74cc920005bd74cc920006df63cc920036dc63cc92000dfa70cc920005f970cc920105ee768c92002eee768c92002f6e758c92002f6d758c92002fae748c92002fad748c92011ded738c920036ee638c920036ec638c92000dee708c92000dec708c92002eef608c92002feb608c920137ea108c920034ff764c92000cfe764c92011cfd764c92000cfc764c920006df634c920036dc634c9202df6f524c9200076d524c92002fcc324c920005fb704c92000df8704c92000dec764c920036ec764c92000cec764c92002def734c92002fcf734c920007cf634c920036ee634c920036ec634c920007cc634c920007cf434c920007cc434c920007eb704c92000dee704c92000dec704c92011fe8704c92002eef604c92002feb604c92011fcf304c92011fcd304c92011fea104c920014fe76d852003ef661d8520004ff75d852001cfe75d8520004fd75d852001cfc75d8520094fe74d8520004fd74d8520034fe73d8520004fd73d852000cfd72d8520014fc72d85200067f52d85200067d52d8520006f751d852003ef451d852003ef621d852000cfe70d852002cf
  | 5 => 0x2fcc634cb20007cf434cb20007cc434cb2000dee704cb2000dec704cb2011fcf304cb2011fcd304cb20004ff755872001cfe7558720004fd755872001cfc7558720004ff7458720094fc7458720004ff7358720034fc735872000cfe7258720014fd725872000cfc725872002e7f525872002e7d525872002ef7715872002ef7215872002ef4215872002efa205872002ef920587200a6f71058720094ff76d072002cfe76d0720004fd76d07200fe7e65d07200067d65d0720096be64d0720006bd64d0720004ff7650720004fd765072002cfc76507200057f75507200557c75507200ee7e65507200067d6550720006be6450720006bd6450720034ff76cc72002cfe76cc720004fd76cc7200557e75cc7200057d75cc7200de7e65cc7200067d65cc720036de63cc720006dd63cc72002dee72cc720005ed72cc720007cd32cc720004ff764c720004fd764c72002cfc764c7200ce7e654c7200067d654c720036de634c720006dd634c720007cd324c7200457e75d91200057d75d9120004ff75d912001cfe75d91200067e75d912001c7e75d9120004fd75d91200067d75d91200047d75d912001cfc75d9120006bf54d9120006bc54d9120034fe73d9120004fd73d91200067f52d9120014fe71d9120004fd71d9120014fc71d9120006be41d9120006bc41d912002cff70d912002cfd70d912019ebf40d912019ebd40d9120006bf6499120005de7399120005dd7399120185ed7299120094ff759912001cfe7599120004fd7599120094fc7599120094fe7499120034fe7399120096de7399120034de7399120004fd7399120096dd7399120004dd7399120184fd7299120096ed72991200067f5299120014fe7199120004fd7199120014fc71991201b4fd7099120096f970991201b5ef7259120004ff755912001cfe7559120004fd755912001cfc7559120006bf7459120004ff7359120034fc73591201b4ff7259120006ef72591200067f5259120004ff7159120014fe7159120014fc7159120184ff7059120006fb705912019cfe7619120006bd6419120094ff751912001cfe7519120004fd7519120094fc7519120096be7419120006bf5419120096bc5419120034fe7319120004fd731912002cfe721912002cfc72191200067f5219120014fe7119120004fd7119120014fc7119120006be4119120096bc411912002cff701912002cfd7019120096bf4019120166bd4019120034fe76d8d20004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20094fe74d8d20004fd74d8d20006df53d8d20006dc53d8d2002cfe72d8d2002cfc72d8d200067f52d8d20014fe71d8d20004fd71d8d20014fc71d8d20006de31d8d20006dc31d8d2002cff70d8d2002cfd70d8d20136df30d8d20136dd30d8d20005be7498d20005bd749
  | 6 => 0xe75c85300057d75c8530035de73c8530005dd73c8530004ff7648530004fe7648530004fc76485300067f74597200067e74597200067d74597200067c74597200067f73597200067e73597200067d73597200067c735972002e7f725972002c7f725972002e7e725972002e7d725972002c7d725972002e7c725972002e7f425972002e7e425972002e7d425972002e7c425972002e7f325972002e7e325972002e7d325972002e7c32597200067f71597200067e71597200067d71597200067c71597200067e41597200067c41597200067e31597200067c315972002e7f215972002e7e215972002e7d215972002e7c21597201c67f70597201c67e70597201c67d70597201c67c70597201c67f40597201c67e40597201c67d40597201c67c40597201c67f30597201c67e30597201c67d30597201c67c305972002e7f205972002e7e205972002e7d205972002e7c20597201c67f10597201c67e10597201c67d10597201c67c1059720094ff759932001cfe7599320004fd7599320094fc759932002ebe7499320034fe7399320004fd739932000cfe729932000cfc729932002e7f529932002e7d529932002ebe429932002ebc4299320014fe7199320004fd7199320014fc7199320096bf40993201b6bd4099320004ff755932001cfe7559320004fd755932001cfc755932002ebf7459320004ff7359320034fc735932002cff725932000cfe725932002cfd725932000cfc725932002e7f525932002e7d525932002ebe425932002ebc4259320004ff7159320014fe7159320014fc7159320186bf4059320186bd4059320004ff7558f2001cfe7558f20004fd7558f2001cfc7558f20004ff7458f20094fc7458f2002edf7358f2002cff7258f2000cfe7258f2002cfd7258f2000cfc7258f2002e7f5258f2002e7d5258f2002ede3258f2002edc3258f20004ff7158f20014fe7158f20014fc7158f2011edf3058f2011edd3058f20094ff76d0f2002cfe76d0f20004fd76d0f2002cfc76d0f201ee7e65d0f200067d65d0f202eebf64d0f20096bc64d0f20036de63d0f20006dd63d0f20034ff7690f2002cfe7690f20004fd7690f2002cfc7690f2021e7e6590f200067d6590f20006be6490f20006bd6490f2002dee7290f20005ed7290f20004ff7650f2002cfe7650f20004fd7650f2002cfc7650f200057f7550f200557c7550f202067e6550f200067d6550f202e6bf6450f202e6bc6450f20005fb7050f2000df87050f20034ff7610f2002cfe7610f20004fd7610f2002cfc7610f201e67e6510f200067d6510f20096be6410f20006bd6410f20036de6310f20006dd6310f2002dee7210f20005ed7210f2002def764cb20006ef764cb2002f6e654cb2002f6d654cb2002fcf734cb2002fcf634cb20036ee634cb2002eec634cb20
  | 7 => 0xd301f4fd7650d3000cfc7650d300057f7550d300657c7550d30006bf6450d30006bc6450d30005fb7050d3000df87050d3002cfe76d8930004ff75d893001cfe75d8930004fd75d893001cfc75d8930094fe74d8930004fd74d89300067f52d8930014fe71d8930004fd71d8930014fc71d8930006ee21d8930006ec21d8930034fd70d893014eef20d89300657e75989300057d7598930005be7498930005bd7498930006ef62989300657e75189300057d751893002eee6218930006ed62189300067f76549300067e76549300067d76549300067c76549300067f64549300067e64549300067d64549300067c64549301c67f63549302757f72549300676f72549300067f625493002e7e625493002e7c62549301ce7e61549301ce7c61549301c67f605493027f7b30549301c75e30549301c75c30549301c7783054930004fe76d0930004fd76d0930094fc76d0930006bf64d0930096bc64d0930004fe7690930004fd769093002cfc76909300657e75909300057d7590930035de7390930005dd7390930004ff7650930004fe7650930004fc7650930006bf6450930006bc6450930004fe7610930004fd761093002cfc76109300657e75109300057d7510930035de7310930005dd731093000dfa7010930005f97010930105de76cc930036de76cc9300379e74cc9300379d74cc930006de64cc930006dc64cc93002ede62cc93002edc62cc9302ff5f52cc9300075d52cc93000dde70cc93000ddc70cc930036df60cc930037db60cc93000cfe768c9300657e758c9300057d758c930005be748c930005bd748c93011ddd738c930006ef628c93002eec628c93000dfa708c930005f9708c93000cfc764c930006ef624c93002eec624c930037cc324c930005fb704c93000df8704c93000ddc764c93002edc764c93000cdc764c930006de644c930006dc644c930035df724c930037cf724c930007cf624c93002ede624c93002edc624c930007cc624c9302f75f524c9300075d524c930007db704c93000dde704c93000ddc704c93011fd8704c930036df604c930037db604c930014fe76d853005ef661d8530004ff75d853001cfe75d8530004fd75d853001cfc75d8530094fe74d8530004fd74d853000cfd73d8530014fc73d853002cfe72d8530004fd72d85300067f52d85300067d52d8530006df32d8530006dd32d853005ef631d8530034fd70d85300d6f710d85300057f75585300657c7558530005bf7458530005bc7458530005ef7258530005ec725853005ef46158530004fe76d0530004fd76d0530094fc76d0530004ff7650530004fe7650530004fc76505300057f75505300657c755053000cfc764c530006f7614c530016f4614c530005fb704c53000df8704c530004fe76c8530004fd76c853002cfc76c85300657
  | 8 => 0x34fe76d0b30004fd76d0b30316bf64d0b30096bc64d0b3002cff7690b30034fe7690b30004fd7690b300757e7590b300057d7590b30006be6490b30006bd6490b30035de7390b30005dd7390b30004ff7650b30004fd7650b30034fc7650b3030ebf6450b3030ebc6450b30005fb7050b3000df87050b3002cff7610b30034fe7610b30004fd7610b300757e7510b300057d7510b30096be6410b30006bd6410b30035de7310b30005dd7310b30035df764cb30006df764cb30006de644cb30036dc644cb30037cf724cb30037cf624cb3002ede624cb3002edc624cb30037cc624cb303075f524cb300075d524cb3000dde704cb3000ddc704cb30004ff755873001cfe7558730004fd755873001cfc7558730004ff7458730094fc745873000cfe7358730014fd735873000cfc7358730004ff725873002cfc72587300067f52587300067d5258730036df3258730006dd3258730036f77158730036f73158730036f431587300c6f71058730094ff76d0730034fe76d0730004fd76d0730096be64d0730006bd64d0730004ff7650730004fd7650730034fc76507300057f75507300757c7550730006be6450730006bd645073002cff76c8730034fe76c8730004fd76c87300757e75c87300057d75c8730035de73c8730005dd73c8730004ff7648730004fd7648730034fc7648730004ff75d913001cfe75d9130004fd75d913001cfc75d9130006bf54d9130006bc54d913002cfe72d9130004fd72d91300067f52d9130014fe71d9130004fd71d9130014fc71d9130006be41d9130006bc41d9130034ff70d9130034fd70d913020ebf40d913020ebd40d9130006bf64991301f5dd7399130094ff759913001cfe7599130004fd7599130094fc7599130094fe74991301f4fd7399130096dd739913002cfe7299130004fd72991300067f5299130014fe7199130004fd7199130014fc7199130224fd7099130096f970991300057f75591300657c7559130225df7359130004ff75591300067f75591300047f755913001cfe7559130004fd755913001cfc75591300067c755913001c7c7559130006bf7459130224ff7359130006df7359130004ff725913002cfc72591300067f5259130004ff7159130014fe7159130014fc71591301f4ff7059130006fb705913020cfe7619130006bd6419130094ff751913001cfe7519130004fd7519130094fc7519130096be7419130006bf5419130096bc5419130034fe7319130034fc731913002cfe7219130004fd72191300067f5219130014fe7119130004fd7119130014fc7119130006be4119130096bc4119130034ff7019130034fd7019130096bf40191301d6bd401913000cfe76d0d3000cfc76d0d30006bf64d0d30096bc64d0d3000dfa70d0d30005f970d0d30094ff7650d3000cfe765
  | 9 => 0xe758c9400057d758c940005be748c940005bd748c940004ff764c940004fe764c940004fc764c940005be744c940005bd744c940006df634c940036dc634c9400079f434c940004fe760c940004fd760c94002cfc760c9400857e750c9400057d750c940005be740c940005bd740c94000dfa700c940005f9700c940014fe76d854007ef661d8540004ff75d854001cfe75d8540004fd75d854001cfc75d854000cfd74d8540014fc74d8540034fe73d8540004fd73d8540006bf43d8540006bd43d854002cfe72d8540004fd72d85400067f52d85400067d52d8540006bf42d8540006bd42d854007ef641d85400f6f710d85400057f75585400857c7558540005df7358540005dc7358540005ef7258540005ec725854007ef461585402a4fe76d0540016f661d054000cfc76505400057f75505400857c7550540006f76150540016f4615054007fb44150540005fb705054000df87050540004fe76cc540004fd76cc540034fc76cc5400857e75cc5400057d75cc540005be74cc540005bd74cc5400079d43cc540004ff764c540004fe764c540004fc764c5400079d434c540004fe76c8540004fd76c854002cfc76c85400857e75c85400057d75c8540005be74c8540005bd74c8540004ff7648540004fe7648540004fc764854000dfa76d014000efa76d014000cfa76d014000dfa74d014000fba74d014000efb64d014000fbb64d0140097bb43d0140007b943d014031f7b52d01400077952d0140097bb42d0140007b942d0140094ff759933001cfe7599330004fd7599330094fc7599330036be749933000cfe739933000cfc7399330036be4399330036bc439933002cfe7299330004fd72993300067f5299330036df3299330014fe7199330004fd7199330014fc7199330096bf4099330226bd4099330004ff75593300067f75593300047f755933001cfe7559330004fd755933001cfc75593300067c755933001c7c7559330036bf7459330034ff735933000cfe7359330034fd735933000cfc7359330036be4359330036bc4359330004ff725933002cfc72593300067f5259330004ff7159330014fe7159330014fc71593301f6bf40593301f6bd4059330004ff7558b3001cfe7558b30004fd7558b3001cfc7558b30004ff7458b30094fc7458b3000cfc7358b30036ef7258b300067f5258b30036ef3258b30036ec3258b30004ff7158b30014fe7158b30014fc7158b3011eef2058b300067f7654b3027e7e7654b300067d7654b3027e7c7654b3027e7f6454b300067e6454b300067d6454b3027e7c6454b301c67e6354b302757f7254b300776f7254b3002e7e6254b300067d6254b3002e7c6254b3027f5f3254b301ce7e6154b301ce7c6154b301c67d6054b301c75e3054b301c77a3054b301c75c3054b30094ff76d0b30
  | 10 => 0x8740004fd7648740094fc7648740034fe76d8d40004ff75d8d4001cfe75d8d40004fd75d8d4001cfc75d8d40006df53d8d40006dc53d8d4002cfe72d8d40004fd72d8d400067f52d8d40014fe71d8d40004fd71d8d40014fc71d8d40006de31d8d40006dc31d8d40226df30d8d40006df6398d400057f7558d400857c7558d40036de6318d40006dd6318d401d4fe76d0d401d5be76d0d40006be76d0d40036be63d0d40036bc63d0d40005bd72d0d402eebc62d0d4033f3f52d0d4000dbe70d0d4000dbc70d0d40096bf60d0d4000cfe7690d401f5bd7490d40006df6390d40036dc6390d4000dfa7090d40005f97090d4000cfc7650d400057f7550d400857c7550d40006df6350d40036dc6350d40005fb7050d4000df87050d4000dbc7650d40036bc7650d4000cbc7650d400073f7550d403373c7550d400079f7350d400079f6350d40036be6350d40036bc6350d400079c6350d400369c6350d40005bf7250d402e6bc6250d403373f5250d40007bb7050d4000dbe7050d4000dbc7050d401f7b87050d401f6bf6050d40224fe7610d40225be7410d4002cfe76d8940004ff75d894001cfe75d8940004fd75d894001cfc75d8940034fe73d8940004fd73d89400067f52d8940014fe71d8940004fd71d8940014fc71d8940006ee21d8940006ec21d89401b6ef20d89400857e75989400057d7598940005de7398940005dd7398940006ef62989400857e75189400057d751894002eee6218940006ed62189400067f76549400067e76549400067d76549400067c76549401c67f64549400067f635494027e7c63549400073f43549400073d43549402757f72549400876f72549400067f625494002e7e625494002e7c62549401ce7e61549401ce7c61549401c67f60549401c73e40549401c73c40549401c7784054940164fe76d0940165be76d0940006be76d0940005bd73d0940316bc63d094002ebe62d094002ebc62d094032f3f52d09400073d52d094000dbe70d094000dbc70d0940096bf60d094000cfe76909400857e75909400057d7590940185bd7490940005de7390940005dd7390940006ef629094002eec629094000dfa7090940005f9709094000cfc7650940006ef625094002eec6250940005fb705094000df8705094000dbc765094002ebc765094000cbc7650940005bf735094030ebc6350940007af7250940007af625094002ebe625094002ebc6250940007ac62509403273f52509400073d5250940007bb705094000dbe705094000dbc7050940187b87050940186bf60509401b4fe76109400857e75109400057d75109401b5be7410940004fe76cc940004fd76cc940034fc76cc940005be74cc940005bd74cc940006df63cc940036dc63cc9400079f43cc940004fe768c940004fd768c94002cfc768c9400857
  | 11 => 0x20cff7650f400057f7550f4009d7c7550f4020dbf7650f40006bf7650f400073f7550f403573c7550f400979f7350f40036be6350f40036bc6350f40005bf7250f402e6be6250f403573f5250f4000dbe7050f4000dbc7050f4009d7e7598b400057d7598b40005de7398b40005dd7398b40096ef6298b4002eec6298b4002cff7658b40096ec6258b40004ff7558b4001cfe7558b40004fd7558b4001cfc7558b4000cfc7458b40004ff7358b40034fc7358b400067f5258b40096ef4258b40096ec4258b40004ff7158b40014fe7158b40014fc7158b40186ef2058b400067f7654b400067e7654b400067d7654b400067c7654b401c67e6454b4027e7e6354b400067d6354b400073f4354b400073d4354b402757f7254b4009f6f7254b4002e7e6254b400067d6254b4002e7c6254b401ce7e6154b401ce7c6154b401c67d6054b401c73e4054b401c77a4054b401c73c4054b4000dbd76d0b4002ebd76d0b4000cbd76d0b40005bd73d0b40316be63d0b4002ebe62d0b40097ae62d0b40097ad62d0b4002ebc62d0b4034f3f52d0b400073d52d0b4000dbe70d0b40097ba70d0b40097b970d0b4000dbc70d0b40184fd7690b4009d7e7590b400057d7590b40005de7390b40005dd7390b4019cff7650b4019dbf7650b40006bf7650b40005bf7350b4030ebe6350b40097af7250b4002ebe6250b4002ebc6250b403473f5250b400073d5250b4000dbe7050b4000dbc7050b40034ff76ccb40094fe76ccb40004fd76ccb40095be74ccb40005bd74ccb40036dc63ccb400079f43ccb4002cff768cb40094fe768cb40004fd768cb4009d7e758cb400057d758cb40095be748cb40005bd748cb40036de638cb40006dd638cb40004ff764cb40004fd764cb40094fc764cb40095be744cb40005bd744cb400079f434cb40005fb704cb4000df8704cb4002cff760cb40094fe760cb40004fd760cb4009d7e750cb400057d750cb40095be740cb40005bd740cb40036de630cb40006dd630cb40014ff7658740096f46158740004ff755874001cfe7558740004fd755874001cfc7558740014fd745874000cfc7458740004ff7358740034fc7358740006bf4358740006bd4358740004ff725874002cfc72587400067f52587400067d5258740006bf4258740006bd4258740096f74158740096f441587400e6f710587402b4ff76507400057f755074009d7c7550740097b44150740034ff76cc740094fe76cc740004fd76cc74009d7e75cc7400057d75cc740095be74cc740005bd74cc740036de63cc740006dd63cc7400079d43cc740004ff764c740004fd764c740094fc764c740036de634c740006dd634c7400079d434c74002cff76c8740094fe76c8740004fd76c874009d7e75c87400057d75c8740095be74c8740005bd74c8740004ff764
  | 12 => 0xc70d8d21006de30d8d21006dc30d8d2113ef710d8d210ad7e7598d210057d7598d21005be7498d21005bd7498d21006df6398d21125ed7298d21155ef7258d21004ff7558d2101cfe7558d21004fd7558d2101cfc7558d21004ff7458d21094fc7458d21006df7358d21154ff7258d21006ef7258d210067f5258d21124ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21126f71058d2113cfe7618d21036de6318d21006dd6318d21094ff76d0d21004fe76d0d21004fd76d0d21094fc76d0d21006bf64d0d21096bc64d0d21034ff7690d21004fe7690d21004fd7690d21034fc7690d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210057f7550d210ad7c7550d21006bf6450d21006bc6450d21034ff7610d21004fe7610d21004fd7610d21034fc7610d21015f67110d21005f57110d2101e7f76549211ce7e76549211ce7d765492101e7c76549210067f64549210067e64549210067d64549210067c64549210067f635492127e7e63549210067d635492127e7c635492102d7f72549210af6f725492102e7f625492102f6e425492102f6e32549210077771549211cf74715492102e7f615492102f7721549211cf6e215492102f6c215492102f7421549211c67e60549211c67c60549211cf771054921014fe76d0921014fc76d0921006bf64d0921096bc64d0921015f671d0921005f571d0921094ff7650921014fe765092118cfd7650921014fc7650921006bf6450921006bc64509210076d5250921005f77150921015f47150921014fe76cc921014fc76cc921005be74cc921005bd74cc921006df63cc921036dc63cc921015f671cc921005f571cc921034ff764c921014fe764c921124fd764c921014fc764c921006df634c921036dc634c9210076d524c921005f7714c921015f4714c92100cfe76d81210a6fa60d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121094fe74d8121004fd74d8121034fe73d8121004fd73d8121014fd72d812100cfc72d81210067f52d81210067d52d812102cfd71d812100cfc71d81210a6fa20d81210a6fa10d81210057f75581210ad7c7558121005bf7458121005bc7458121005df7358121005dc73581210a6f86058121096df6398f40036dc6398f40034ff7658f40096dc6358f40004ff7558f4001cfe7558f40004fd7558f4001cfc7558f4000cfc7458f40096df4358f40096dc4358f40004ff7258f4002cfc7258f400067f5258f40004ff7158f40014fe7158f40014fc7158f401f6df3058f4000dbd76d0f40036bd76d0f4000cbd76d0f40036be63d0f400979e63d0f400979d63d0f40036bc63d0f40005bd72d0f402eebe62d0f4035f3f52d0f4000dbe70d0f40097ba70d0f40097b970d0f4000dbc70d0f401f4fd7690f40
  | 13 => 0x8f2101cfe7558f21004fd7558f2101cfc7558f21004ff7458f21094fc7458f2102edf7358f21014fe7258f21014fc7258f2102e7f5258f2102e7d5258f2102ede3258f2102edc3258f21126df3158f21126dd3158f21004ff7058f2100cfe7058f2100cfc7058f21094ff76d0f2102cfe76d0f21004fd76d0f2102cfc76d0f211ee7e65d0f210067d65d0f212eebf64d0f21096bc64d0f21036de63d0f21006dd63d0f21034ff7690f2102cfe7690f21004fd7690f2102cfc7690f2121e7e6590f210067d6590f21006be6490f21006bd6490f21004ff7650f2102cfe7650f21004fd7650f2102cfc7650f210057f7550f210bd7c7550f212067e6550f210067d6550f212e6bf6450f212e6bc6450f21005f77150f21015f47150f21034ff7610f2102cfe7610f21004fd7610f2102cfc7610f211e67e6510f210067d6510f21096be6410f21006bd6410f21036de6310f21006dd6310f21004ff755832101cfe7558321004fd755832101cfc7558321004ff7458321094fc7458321004ff7358321034fc7358321014fe725832100cfd7258321014fc725832102e7f525832102e7d525832102ef6215832102ef5215832102efb705832102efb205832102ef820583210b6fa1058321004ff75d912101cfe75d9121004fd75d912101cfc75d9121006bf54d9121006bc54d9121034fe73d9121004fd73d91210067f52d912102cff71d912102cfd71d91211a6bf41d91211a6bd41d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121006bc40d9121006bf649912118ded7299121094ff759912101cfe7599121004fd7599121094fc7599121094fe7499121034fe7399121004fd739912118cfd7299121096ed72991210067f52991211bcfd7199121096f5719912100cfe7099121004fd709912100cfc70991211bef710991210057f75591210ad7c75591211bdef7259121004ff75591210067f75591210047f755912101cfe7559121004fd755912101cfc75591210067c755912101c7c7559121006bf7459121004ff7359121034fc73591211bcff7259121006ef72591210067f525912118cff7159121006f77159121004ff705912100cfe705912100cfc70591211a4fe7619121006bd6419121094ff751912101cfe7519121004fd7519121094fc7519121096be7419121006bf5419121096bc5419121034fe7319121004fd73191210067f521912102cff711912102cfd7119121096bf411912116ebd411912100cfe7019121004fd701912100cfc7019121006be4019121096bc401912116ef71019121034fe76d8d21004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21094fe74d8d21004fd74d8d210067f52d8d2102cff71d8d2102cfd71d8d2113edf31d8d2113edd31d8d2100cfe70d8d21004fd70d8d2100cf
  | 14 => 0x10dde76cc931036de76cc931035df74cc9310379e74cc931005dd74cc9310379d74cc9310059d74cc931006de64cc931006dc64cc93102ede62cc93102edc62cc93136f5f52cc9310075d52cc931015de71cc931015dc71cc931036df61cc931037d761cc931157d710cc931014fe768c9310cd7e758c9310057d758c931005be748c931005bd748c931125dd738c931006ef628c93102eec628c931015f6718c931005f5718c931014fc764c931006ef624c93102eec624c931005f7714c931015f4714c931015dc764c93102edc764c931014dc764c931005df744c931005dd744c931006de644c931006dc644c931035df724c931037cf724c931007cf624c93102ede624c93102edc624c931007cc624c93102ecc624c9313675f524c9310075d524c931007d7714c931015de714c931015dc714c931127d4714c931036df614c931037d7614c931127d7104c93100cfe76d81310c6fa60d8131004ff75d813101cfe75d8131004fd75d813101cfc75d8131094fe74d8131004fd74d8131014fd73d813100cfc73d813102cfe72d8131004fd72d81310067f52d81310067d52d8131006df32d8131006dd32d8131034fd71d81310c6fa30d81310c6fa10d81310057f75581310cd7c7558131005bf7458131005bc7458131005ef7258131005ec72581310c6f860581310067f74597210067e74597210067d74597210067c74597210067f73597210067e73597210067d73597210067c735972102e7f725972102e7e725972102e7d725972102e7c725972102e7f425972102e7e425972102e7d425972102e7c425972102e7f325972102e7e325972102e7d325972102e7c32597211ce7f71597211ce7e71597211ce7d71597211ce7c71597211ce7f41597211ce7e41597211ce7d41597211ce7c41597211ce7f31597211ce7e31597211ce7d31597211ce7c315972102e7f215972102e7e215972102e7d215972102e7c21597210067f70597210067e70597210067d70597210067c70597210067e40597210067c40597210067e30597210067c305972102e7f205972102e7e205972102e7d205972102e7c20597211ce7f10597211ce7e10597211ce7d10597211ce7c1059721094ff759932101cfe7599321004fd7599321094fc759932102ebe7499321034fe7399321004fd7399321014fe7299321014fc729932102e7f529932102e7d529932102ebe429932102ebc4299321096bf41993211bebd419932100cfe7099321004fd709932100cfc7099321004ff755932101cfe7559321004fd755932101cfc755932102ebf7459321004ff7359321034fc7359321014fe7259321014fc725932102e7f525932102e7d525932102ebe425932102ebc425932118ebf415932118ebd4159321004ff705932100cfe705932100cfc7059321004ff755
  | 15 => 0xc755913101c7c7559131006bf745913122cff7359131006df7359131004ff725913102cfc72591310067f52591311fcff7159131006f77159131004ff705913100cfe705913100cfc7059131214fe7619131006bd6419131094ff751913101cfe7519131004fd7519131094fc7519131096be7419131006bf5419131096bc5419131096dd731913102cfe7219131004fd72191310067f5219131034ff7119131034fd7119131096bf41191311debd411913100cfe7019131004fd701913100cfc7019131006be4019131096bc40191311def71019131014fe76d0d31014fc76d0d31006bf64d0d31096bc64d0d31015f671d0d31005f571d0d311ddde7690d31036de7690d311fddd7490d31096de6490d31096dc6490d31005dd7290d313875f5290d31015de7190d31015dc7190d31036df6190d31037d76190d31217d71090d31094ff7650d31014fe7650d311fcfd7650d31014fc7650d310057f7550d310cd7c7550d31006bf6450d31006bc6450d310379c4350d31005f77150d31015f47150d31037d43150d31015dc7650d311fedc7650d31014dc7650d310075f7550d3137f5c7550d31035df7450d310379f7450d310079f6450d31096de6450d31096dc6450d310079c6450d31005df7250d3137f5f5250d31007d77150d31015de7150d31015dc7150d311ffd47150d31036df6150d31037d76150d311ff9f4150d311ff9d4150d311ffd71050d3102cfe76d8931004ff75d893101cfe75d8931004fd75d893101cfc75d8931094fe74d8931004fd74d89310067f52d8931034fd71d8931156ef21d893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931006ec20d8931156f710d89310cd7e75989310057d7598931005be7498931005bd7498931006ef62989310cd7e75189310057d751893102eee6218931006ed62189310067f76549310067e76549310067d76549310067c76549310067f64549310067e64549310067d64549310067c64549311ce7f63549310075e43549310075d43549313757f72549310cf6f72549310067f625493102e7e625493102e7c62549310077771549311cf7471549311ce7f615493127f7731549311cf5e31549311cf5c31549311cf7431549311c67e60549311c67c60549311cf771054931004fe76d0931004fd76d0931094fc76d0931006bf64d0931096bc64d0931035de73d0931005dd73d09310079e43d0931004fe7690931004fd769093102cfc76909310cd7e75909310057d7590931035de7390931005dd73909310079d4390931004ff7650931004fe7650931004fc7650931006bf6450931006bc64509310079e4350931004fe7610931004fd761093102cfc76109310cd7e75109310057d7510931035de7310931005dd73109310079d4310931015f67110931005f57110931
  | 16 => 0x8b310067d7558b3101cfc7558b31004ff7458b31094fc7458b31014fc7358b31036ef7258b310067f5258b31036ef3258b31036ec3258b31126ef2158b31004ff7058b3100cfe7058b3100cfc7058b3127d7f7654b310067f7654b310047f7654b3127e7e7654b3127d7d7654b310067d7654b310047d7654b3127e7c7654b3127e7f6454b310067e6454b310067d6454b3127e7c6454b311ce7e6354b3127f5e4354b310075d4354b313757f7254b310df6f7254b3102e7e6254b310067d6254b3102e7c6254b3127f5f3254b311ce7d6154b311cf5e3154b311cf763154b311cf5c3154b311c67e6054b311c67c6054b31094ff76d0b31034fe76d0b31004fd76d0b3117e7e65d0b310067d65d0b31316bf64d0b31096bc64d0b31035de73d0b31005dd73d0b313179e43d0b3102eee62d0b31006ed62d0b3102cff7690b31034fe7690b31004fd7690b310dd7e7590b310057d7590b311ae7e6590b310067d6590b31006be6490b31006bd6490b31035de7390b31005dd7390b310079d4390b31004ff7650b31004fd7650b31034fc7650b311967e6550b310067d6550b3130ebf6450b3130ebc6450b31035de7350b3130f9e4350b31005f77150b31015f47150b3102cff7610b31034fe7610b31004fd7610b310dd7e7510b310057d7510b311767e6510b310067d6510b31096be6410b31006bd6410b31035de7310b31005dd7310b310079d4310b3102eee6210b31006ed6210b31035df764cb31006df764cb310375e654cb310375d654cb31005df744cb31005dd744cb31006de644cb31036dc644cb31037cf724cb3102ede624cb3102edc624cb3138f5f524cb310075d524cb31015de714cb31015dc714cb31004ff755833101cfe7558331004fd755833101cfc7558331004ff7458331094fc7458331014fe735833100cfd7358331014fc7358331004ff725833102cfc72583310067f52583310067d5258331036df3258331006dd3258331036f63158331036f53158331036fb7058331036fb3058331036f830583310d6fa1058331004ff75d913101cfe75d9131004fd75d913101cfc75d9131006bf54d9131006bc54d913102cfe72d9131004fd72d91310067f52d9131034ff71d9131034fd71d9131216bf41d9131216bd41d913100cfe70d9131004fd70d913100cfc70d9131006be40d9131006bc40d9131006bf64991311fddd7399131094ff759913101cfe7599131004fd7599131094fc7599131094fe74991311fcfd7399131096dd739913102cfe7299131004fd72991310067f529913122cfd7199131096f5719913100cfe7099131004fd709913100cfc709913122ef710991310057f75591310cd7c755913122ddf7359131004ff75591310067f75591310047f755913101cfe7559131004fd755913101cfc75591310067
  | 17 => 0x79f434c941006ef624c94102eec624c941004fe760c941004fd760c94102cfc760c9410ed7e750c9410057d750c9410067f650c9411167c650c941005be740c941005bd740c941015f6710c941005f5710c9410077765d05413a77465d0541015f674d0541017b674d0541016f764d0541017b764d0541097b743d0541007b543d05413a77752d05410077552d0541097b742d0541007b542d054100cfe76d81410067f65d81410067c65d81410e6fa60d8141004ff75d814101cfe75d8141004fd75d814101cfc75d8141014fd74d8141034fe73d8141004fd73d8141006bf43d8141006bd43d814102cfe72d8141004fd72d81410067f52d81410067d52d8141006bf42d8141006bd42d8141006f741d814108ef441d81410e6fa40d81410e6fa10d81410057f75581410ed7c75581410067f65581410067c6558141005df7358141005dc7358141005ef7258141005ec72581410e6f860581410067f74597310067e74597310067d74597310067c74597310367f73597310367e73597310367d73597310367c73597310367f43597310367e43597310367d43597310367c43597310067f72597310047f72597310067e72597310067d72597310067c72597310367f32597310367e32597310367d32597310367c325973139e7f715973139e7e715973139e7d715973139e7c715973139e7f415973139e7e415973139e7d415973139e7c41597310367f31597310367e31597310367d31597310367c315973139e7f215973139e7e215973139e7d215973139e7c21597310067f70597310067e70597310067d70597310067c70597310067e40597310067c40597310367f30597310367e30597310367d30597310367c30597310067e20597310067c205973139e7f105973139e7e105973139e7d105973139e7c1059731094ff759933101cfe7599331004fd7599331094fc7599331036be7499331014fe7399331036de7399331014de7399331014fc7399331036be4399331036de4399331036bc439933102cfe7299331004fd72993310067f5299331036df3299331096bf419933122ebd419933100cfe7099331004fd709933100cfc7099331004ff755933101cfe7559331004fd755933101cfc7559331036bf7459331014fe7359331014fc7359331036be4359331036bc4359331004ff725933102cfc72593310067f52593311febf41593311febd4159331004ff705933100cfe705933100cfc7059331035df7650f31006df7650f310075f7550f313975c7550f310375e6550f310375d6550f310379f7450f310379f6450f31096de6450f31036dc6450f310379c6450f31005df7250f313975f5250f31015de7150f31015dc7150f311ff9f4150f311ff9d4150f31004ff7558b3101cfe7558b310067e7558b3101c7e7558b31004fd755
  | 18 => 0xf6350d41036be6350d41036bc6350d410079c6350d41005bf7250d412e6bc6250d413bf3f5250d41007b77150d41015be7150d41015bc7150d411ffb47150d411febf6150d4122cfe7610d410067f6510d411e67c6510d4122dbe7410d410079d4310d4102cfe76d89410ed7c75d89410067f65d89410067c65d8941004ff75d89410067f75d894101cfe75d8941004fd75d894101cfc75d89410067c75d894101c7c75d8941034fe73d8941004fd73d89410067f52d89411beef21d894100cfe70d8941004fd70d894100cfc70d8941006ee20d8941006ec20d89410ed7e75989410057d75989410067f65989410067c6598941005de7398941005dd7398941006ef62989410057f75589410ed7c75589410067f65589410067c65589410ed7e75189410057d75189410067f65189410067c651894102eee6218941006ed62189410067f76549410057e76549410067e76549410047e76549410067d76549410057c76549410067c76549410047c76549411ce7f64549410067f635494127e7c63549410073f43549410073d43549413757f72549410ef6f72549410067f625494102e7e625494102e7c62549411ce7f61549411cf3e41549411cf3c41549411cf7441549411c67e60549411c67c605494116cfe76d09410067f65d094117e7c65d094116dbe76d0941006be76d09410073f65d09413b73c65d0941005bd73d0941316bc63d094102ebe62d094102ebc62d09413b73f52d09410073d52d0941015be71d0941015bc71d0941096bf61d0941014fe76909410ed7e75909410057d75909410067f65909411ae7c659094118dbd7490941005de7390941005dd7390941006ef629094102eec6290941015f67190941005f571909411a7b44190941014fc76509410067f65509411967c6550941006ef625094102eec6250941005f77150941015f47150941015bc765094102ebc7650941014bc76509410073f65509413af3c6550941005bf735094130ebc6350941007af7250941007af625094102ebe625094102ebc6250941007ac62509413af3f52509410073d5250941007b77150941015be7150941015bc715094118fb47150941015b4715094118ebf61509411bcfe76109410ed7e75109410057d75109410067f65109411767c65109411bdbe7410941097b44110941004fe76cc941004fd76cc941034fc76cc9410067f65cc94115e7c65cc941005be74cc941005bd74cc941006df63cc941036dc63cc9410079f43cc941004fe768c941004fd768c94102cfc768c9410ed7e758c9410057d758c9410067f658c9411467c658c941005be748c941005bd748c941006ef628c94102eec628c941004ff764c941004fe764c941004fc764c9410067f654c94112e7c654c941005be744c941005bd744c941006df634c941036dc634c941
  | 19 => 0xcb41005bd74ccb41036dc63ccb410079f43ccb4102cff768cb41094fe768cb41004fd768cb410fd7e758cb410057d758cb41095be748cb41005bd748cb41004ff764cb41004fd764cb41094fc764cb41095be744cb41005bd744cb410079f434cb41005f7714cb41015f4714cb4102cff760cb41094fe760cb41004fd760cb410fd7e750cb410057d750cb41095be740cb41005bd740cb4100cff7658341096f86058341004ff755834101cfe7558341004fd755834101cfc7558341014fc7458341004ff7358341034fc7358341006bf4358341006bd4358341004ff725834102cfc72583410067f52583410067d5258341006bf4258341006bd4258341096fb4058341096f840583410f6fa10583413d57e76d95410ee7e76d954101c7e76d95410057d72d95413cf3e41d95413cf3c41d95413cf7441d95410067e60d95410067c60d95413ce7f74d95410ee7e74d95413ce7d74d95413ce7c74d95410067f73d95410067e73d95410067d73d95410067c73d95410067f72d95410067e72d95410067d72d95410047d72d95410067c72d95413ce7f71d95413ce7e71d95413ce7d71d95413ce7c71d95413ce7f41d95413ce7e41d95413ce7d41d95413ce7c41d95413ce7f31d95413ce7e31d95413ce7d31d95413ce7c31d95413ce7f21d95413ce7e21d95413ce7d21d95413ce7c21d95410067f70d95410067e70d95410067d70d95410067c70d95410067e40d95410067c40d95410067e30d95410067c30d95410067e20d95410067c20d95413ce7f10d95413ce7e10d95413ce7d10d95413ce7c10d9541034fe76d8d410067f65d8d410067c65d8d41004ff75d8d4101cfe75d8d41004fd75d8d4101cfc75d8d4102cfe72d8d41004fd72d8d410067f52d8d4122edf31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006de30d8d41006dc30d8d410ed7e7598d410057d7598d410067f6598d410067c6598d41006df6398d41005ee7298d41005ed7298d410057f7558d410ed7c7558d410067f6558d410067c6558d410067f6518d410067c6518d41036de6318d41006dd6318d411dcfe76d0d410067f65d0d411ee7c65d0d41097b441d0d411ddbe76d0d41006be76d0d410073f65d0d413c73c65d0d41036be63d0d41036bc63d0d41005bd72d0d412eebc62d0d413c73f52d0d41015be71d0d41015bc71d0d41096bf61d0d41014fe7690d410067f6590d4121e7c6590d411fdbd7490d41006df6390d41036dc6390d41015f67190d41005f57190d41014fc7650d410057f7550d410ed7c7550d410067f6550d412067c6550d41006df6350d41036dc6350d41005f77150d41015f47150d411ffb44150d41015bc7650d41036bc7650d41014bc7650d410073f7550d413bf3c7550d410073f6550d413bf3c6550d410079f7350d410079
  | 20 => 0x10ef64158432036f73158432036f4315843202ef7215843202ef42158432004ff705843200cfe705843200cfc705843210ef71058432004ff755803201cfe7558032004fd755803201cfc7558032004ff7458032094fc745803202e7f525803202e7d525803202edf325803202eee325803202edd3258032036ed3258032004ff7158032014fe7158032014fc715803202cff705803202efb7058032106fa4058032036fb3058032036f8305803202efb205803202ef82058032106fa1058032096df6398f41036dc6398f41034ff7658f41096dc6358f41004ff7558f4101cfe7558f41004fd7558f4101cfc7558f41014fc7458f41096df4358f41096dc4358f41004ff7258f4102cfc7258f410067f5258f411fedf3158f41004ff7058f4100cfe7058f4100cfc7058f411fef71058f41015bd76d0f41036bd76d0f41014bd76d0f41036be63d0f410979e63d0f410979d63d0f41036bc63d0f41005bd72d0f412eebe62d0f413f73f52d0f41015be71d0f41097b671d0f41097b571d0f41015bc71d0f4122fb710d0f411fcfd7690f41036dc6390f41214ff7650f410057f7550f410fd7c7550f410979c4350f41215bf7650f41006bf7650f410073f7550f413ef3c7550f410979f7350f410979f6350f41036be6350f41036bc6350f410979c6350f41005bf7250f412e6be6250f413ef3f5250f41015be7150f41015bc7150f411ffb71050f410fd7e7598b410057d7598b41005de7398b41005dd7398b41096ef6298b4102eec6298b4102cff7658b41096ec6258b41004ff7558b4101cfe7558b41004fd7558b4101cfc7558b41014fc7458b41004ff7358b41034fc7358b410067f5258b41096ef4258b41096ec4258b4118eef2158b41004ff7058b4100cfe7058b4100cfc7058b4118ef71058b410067f7654b410067e7654b410067d7654b410067c7654b411ce7e6454b4127e7e6354b410067d6354b410073f4354b410073d4354b413757f7254b410ff6f7254b4102e7e6254b410067d6254b4102e7c6254b41007777154b411cf747154b411ce7d6154b411cf3e4154b411cf764154b411cf3c4154b411c67e6054b411c67c6054b411cf771054b41015bd76d0b4102ebd76d0b41014bd76d0b41005bd73d0b41316be63d0b4102ebe62d0b41097ae62d0b41097ad62d0b4102ebc62d0b413e73f52d0b410073d52d0b41015be71d0b41097b671d0b41097b571d0b41015bc71d0b411bfb710d0b4118cfd7690b410fd7e7590b410057d7590b41005de7390b41005dd7390b411a4ff7650b411a5bf7650b41006bf7650b41005bf7350b4130ebe6350b41097af7250b4102ebe6250b4102ebc6250b413df3f5250b410073d5250b41015be7150b41015bc7150b4118fb71050b41034ff76ccb41094fe76ccb41004fd76ccb41095be74c
  | 21 => 0xf64d0932096bc64d0932035de73d0932005dd73d09320079c43d09320076d52d0932094ff7650932004fd7650932034fc7650932006bf6450932006bc6450932005df7350932035dc73509320079c4350932014fe76d853212d7e75d85320057d75d8532126f661d8532004ff75d853201cfe75d85320067e75d853201c7e75d8532004fd75d85320067d75d85320047d75d853201cfc75d8532094fe74d8532004fd74d853202cfd73d8532034fd72d85320067f52d85320067d52d8532126f441d8532126f631d8532126f621d853200cfe70d8532004fd70d853200cfc70d8532126f4615853200cfe76d813211efa60d8132004ff75d813201cfe75d8132004fd75d813201cfc75d8132094fe74d8132004fd74d813202cfd73d8132034fd72d81320067f52d81320067d52d8132014fe71d8132004fd71d8132014fc71d813211ef840d813211efa30d813211efa20d813211ef860581320067f74594320067e74594320067d74594320067c74594320367f73594320367e73594320367d73594320367c73594320367f43594320367e43594320367d43594320367c435943202e7f725943202e7e725943202e7d725943202e7c725943202e7f425943202e7e425943202e7d425943202e7c425943202e7f325943202e7e325943202e7d325943202e7c32594320067f71594320067e71594320067d71594320067c71594320067e41594320067c41594320367f31594320367e31594320367d31594320367c315943202e7f215943202e7e215943202e7d215943202e7c21594320067f70594320067e70594320067d70594320067c70594320067e40594320067c40594320367f30594320367e30594320367d30594320367c305943202e7f205943202e7e205943202e7d205943202e7c20594320067f10594320067e10594320067c1059432094ff759903201cfe7599032004fd7599032094fc759903202cfe749903202ebe7499032034fe7399032034fc7399032036be4399032036bc439903202cfe729903202cfc729903202e7f529903202e7d529903202ebe429903202ebc429903202edf329903202edd3299032014fe7199032004fd7199032014fc719903200cfe7099032004fd709903200cfc7099032004ff755903201cfe7559032004fd755903201cfc755903202cff745903202ebf7459032034fe7359032034fc7359032036be4359032036bc435903202cfe725903202cfc725903202e7f525903202e7d525903202ebe425903202ebc4259032004ff7159032014fe7159032014fc7159032004ff705903200cfe705903200cfc7059032004ff755843201cfe7558432004fd755843201cfc7558432004ff7458432094fc745843202e7f525843202e7d525843202edf325843202edd325843202cff715843202ef77158432
  | 22 => 0x823202edd3258232004ff7158232014fe7158232014fc715823202efb7058232136fa305823202efb205823202ef82058232136fa1058232004ff75d913201cfe75d9132004fd75d913201cfc75d9132006dd73d91320067f52d9132014fe71d9132004fd71d9132014fc71d913200cfe70d9132004fd70d913200cfc70d9132006bf6499132094ff759913201cfe7599132004fd7599132094fc7599132094fe7499132004fd7399132096dd7399132316be4399132096bc4399132004fd7299132096ed72991320067f52991322eebe4299132096bc4299132014fe7199132004fd7199132014fc719913200cfe7099132004fd709913200cfc70991320057f755913212d7c7559132005f77159132125f47159132005fb705913211df87059132004ff75591320067f75591320047f755913201cfe7559132004fd755913201cfc75591320067c755913201c7c7559132006bf7459132004ff7359132006df735913230ebe435913230ebc4359132004ff7259132006ef72591320067f52591322e6be42591322e6bc4259132004ff7159132006f77159132004f77159132014fe7159132014fc7159132006f47159132014f47159132004ff7059132006fb7059132004fb705913200cfe705913200cfc7059132006f8705913200cf87059132004fe7619132006bd6419132094ff751913201cfe7519132004fd7519132094fc7519132096be74191320067f5219132014fe7119132004fd7119132014fc711913200cfe7019132004fd701913200cfc701913202cfe76d0d32006bf64d0d32096bc64d0d3202dee72d0d32005ed72d0d3202dde76d0d32006de76d0d3202cde76d0d32035de74d0d32006df64d0d320079f64d0d32006dd64d0d320079c64d0d3202dde72d0d32007ce72d0d32007cd72d0d3202ddc72d0d32036df62d0d32037cf62d0d3240f5f52d0d322ef9e42d0d322ef9c42d0d32005dd71d0d32005dd70d0d3202cfc7650d320057f7550d3212d7c7550d32006bf6450d32006bc6450d320379c4350d32005ef7250d3202dec7250d32005de7610d32036de7610d32405de7410d320379e7410d32006df6410d320079e6410d32006dd6410d320079d6410d3202dde7210d3202ddc7210d32036df6210d32037cf6210d323ff5f5210d32005dd7110d32005dd7010d3201e7f765493227e7e765493212e7d765493201e7c76549320067f64549320067e64549320067d64549320067c64549320075f73549320075c735493202e7f63549320075f43549320075c435493202d7f725493212f6f725493202e7f625493202f6c425493227f6f325493202f5e325493202f5c325493202f6c325493202f4c32549321ce7e61549321ce7c615493202f6f21549321c67e60549321c67c605493202f6f2054932034fe76d0932006b
  | 23 => 0x2ebf529923202e3f529923202ebe529923202ebd529923202e3d529923202ebc529923202ebf329923202e9f329923202ebe329923202ebd329923202e9d329923202ebc3299232096bf7199232006be7199232006bd7199232096bc7199232006bf5199232006be5199232006bd5199232006bc5199232316bf3199232006be3199232316bc319923202ebf219923202ebe219923202ebd219923202ebc2199232096bf7099232006be7099232006bd7099232096bc7099232006bf5099232006be5099232006bd5099232006bc5099232316bf3099232006be3099232316bc309923202ebf209923202ebe209923202ebd209923202ebc2099232006bf1099232006be1099232006bc1099232004ff755923201cfe7559232004fd755923201cfc755923202ebf7459232006bf5459232006be5459232006bd5459232006bc545923202cfc725923202e7f525923202e7d525923202ebe425923202ebc4259232004ff7159232014fe7159232014fc7159232006be4159232006bc4159232004ff705923200cfe705923200cfc7059232006be4059232006bc4059232006bf7559232006be7559232006bd7559232006bc7559232006bf735923230ebe7359232006bd735923230ebc7359232006bf535923230ebe5359232006bd535923230ebc535923202ebf725923202ebe725923202ebd725923202ebc725923202ebf525923202e3f525923202ebe525923202ebd525923202e3d525923202ebc525923202ebf325923202ebe325923202ebd325923202ebc3259232006bf7159232006be7159232006bd7159232006bc7159232006bf5159232006be5159232006bd5159232006bc515923230ebf3159232006be315923230ebc315923202ebf215923202ebe215923202ebd215923202ebc2159232006bf7059232006be7059232006bd7059232006bc7059232006bf5059232006be5059232006bd5059232006bc505923230ebf3059232006be305923230ebc305923202ebf205923202ebe205923202ebd205923202ebc2059232006bf1059232006be1059232006bc10592321ee7e65d0e320067d65d0e32096be64d0e32006bd64d0e3202dee72d0e32005ed72d0e320057f7550e321457c7550e322067e6550e320067d6550e32006be6450e32006bd6450e32005ef7250e3202dec7250e32004ff755863201cfe7558632004fd755863201cfc7558632004ff7458632094fc745863202cfc725863202e7f525863202e7d525863202edf325863202edd325863202ef7715863213ef6315863202ef7215863202ef42158632004ff705863200cfe705863200cfc705863213ef71058632004ff755823201cfe7558232004fd755823201cfc7558232004ff7458232094fc745823202cfc725823202e7f525823202e7d525823202edf325
  | 24 => 0xc42d0f32005dd71d0f32005dd70d0f3201e7f7654b3201e7c7654b3227e7f6454b320067e6454b3227f3e6454b320063e6454b320067d6454b3227f3d6454b320063d6454b3227e7c6454b320075f7354b3227f5c7354b3202e7e6354b320075f4354b3227f5c4354b3202d7f7254b3215f6f7254b3202e7d6254b3202f6e4254b3202f5e3254b3202f6e3254b3202f4e3254b3202f5c3254b321ce7e6154b321ce7c6154b321c67e6054b321c67c6054b32096be64d0b32006bd64d0b32035de73d0b32005dd73d0b323179c43d0b32006be6450b32006bd6450b32005df7350b32035dc7350b3230f9c4350b320076d5250b32004ff755873201cfe7558732004fd755873201cfc7558732004ff7458732094fc745873202cfc73587320067f52587320067d5258732036f77158732006f75158732156f45158732036f73158732036f43158732156f62158732004ff705873200cfe705873200cfc7058732156f71058732004ff755833201cfe7558332004fd755833201cfc7558332004ff7458332094fc745833202cfc73583320067f52583320067d5258332036ee3258332036ed3258332004ff7158332014fe7158332014fc7158332036fb7058332036fb3058332036f8305833214efa20583320067f74596320067e74596320067d74596320067c74596321467f735963227e7e73596320067d735963227e7c735963227e7e435963227e7c435963202e7f725963202e7e725963202e7d725963202e7c725963202e7f425963202e7e425963202e7d425963202e7c425963202e7f325963202e7e325963202e7d325963202e7c32596320067f71596320067e71596320067d71596320067c71596320067e41596320067c415963227e7f31596320067e315963227e7c315963202e7f215963202e7e215963202e7d215963202e7c21596320067f70596320067e70596320067d70596320067c70596320067e40596320067c405963227e7f30596320067e305963227e7c305963202e7f205963202e7e205963202e7d205963202e7c20596320067f10596320067e10596320067c1059632094ff759923201cfe7599232004fd7599232094fc759923202ebe7499232006bf5499232096be5499232006bd5499232096bc549923202cfe729923202e7f529923202e7d529923202ebe429923202ebc429923202edf329923202edd3299232014fe7199232004fd7199232014fc7199232006be4199232096bc419923200cfe7099232004fd709923200cfc7099232006be4099232096bc4099232096bf7599232006be7599232006bd7599232096bc7599232096bf7399232316be7399232006bd7399232096bc7399232006bf5399232316be5399232006bd5399232316bc539923202ebf729923202ebe729923202ebd729923202ebc7299232
  | 25 => 0x9332006be4199332096bc419933200cfe7099332004fd709933200cfc7099332006be4099332096bc4099332096bf7599332006be7599332006bd7599332096bc7599332036bf7399332036be7399332036bd7399332036bc7399332036bf5399332036be5399332036bd5399332036bc5399332096bf72993322eebe7299332006bd7299332096bc7299332006bf52993320063f52993322eebe5299332006bd52993322eebc5299332036bf3299332036be3299332036bd3299332036bc3299332096bf7199332006be7199332006bd7199332096bc7199332006bf5199332006be5199332006bd5199332006bc5199332036bf3199332036be3199332036bd3199332036bc31993322eebf2199332006be21993322eebc2199332096bf7099332006be7099332006bd7099332096bc7099332006bf5099332006be5099332006bd5099332006bc5099332036bf3099332036be3099332036bd3099332036bc30993322eebf2099332006be20993322eebc2099332006bf1099332006be1099332006bc1099332004ff75593320067f75593320047f755933201cfe7559332004fd755933201cfc75593320067c755933201c7c7559332036bf7459332006bf5459332006be5459332006bd5459332006bc545933202cfc7359332036dc735933202cdc7359332036be4359332036bc4359332036dc43593320067f5259332004ff7159332014fe7159332014fc7159332006be4159332006bc4159332036df3159332004ff705933200cfe705933200cfc7059332006be4059332006bc4059332006bf75593320063f7559332006be7559332006bd7559332006bc75593320063c7559332036bf7359332036be7359332036bd7359332036bc73593320369c7359332036bf5359332036be5359332036bd5359332036bc5359332006bf72593322e6be7259332006bd72593322e6bc7259332006bf52593320063f52593322e6be5259332006bd52593322e6bc5259332036bf3259332036be3259332036bd3259332036bc3259332006bf7159332006be7159332006bd7159332006bc7159332006bf5159332006be5159332006bd5159332006bc5159332036bf31593320369f3159332036be3159332036bd3159332036bc31593322e6bf2159332006be21593322e6bc2159332006bf7059332006be7059332006bd7059332006bc7059332006bf5059332006be5059332006bd5059332006bc5059332036bf3059332036be3059332036bd3059332036bc30593322e6bf2059332006be20593322e6bc2059332006bf1059332006be1059332006bc1059332035dd76d0f32006dd76d0f320379e74d0f32036df64d0f320379e64d0f32006dd64d0f320379d64d0f320069d64d0f3202dde72d0f3202ddc72d0f324175f52d0f322ef9e42d0f322ef9
  | 26 => 0x967f43594420967c435944202e7f725944202e7e725944202e7d725944202e7c725944202e7f425944202e7e425944202e7d425944202e7c425944202e7f325944202e7e325944202e7d325944202e7c32594420067f71594420067e71594420067d71594420067c71594420967f41594420067e41594420967c41594420067e31594420067c315944202e7f215944202e7e215944202e7d215944202e7c21594420067f70594420067e70594420067d70594420067c70594420967f40594420067e40594420967c40594420067e30594420067c305944202e7f205944202e7e205944202e7d205944202e7c20594420067f10594420067e10594420067c1059442004ff7558c4201cfe7558c42004fd7558c4201cfc7558c4202edf7358c42096df4358c42096dc4358c4202e7f5258c4202e7d5258c4202ede3258c4202edc3258c42004ff7158c42014fe7158c42014fc7158c42004ff7058c4200cfe7058c4200cfc7058c42034bd76d0c420973e65d0c420973d65d0c42036be63d0c420979e63d0c420979d63d0c42036bc63d0c42097ae72d0c422edbd72d0c42097ad72d0c422eebe62d0c42097ae62d0c422ef3f52d0c422ef3d52d0c42004fd7690c4221e7e6590c420067d6590c422e5bd7490c42316be6490c42004ff7650c420057f7550c421757c7550c422067e6550c420067d6550c422e5bf7650c42006bf7650c42004bf7650c420073f7550c424273c7550c422e73e6550c422e73d6550c42095bf7350c420979f7350c42036be6350c42036bc6350c422e5bf7250c422e6be6250c422e7ae6250c422e73f5250c422e73d5250c4202def7650842006ef7650842004ef765084202f6e655084202f6d655084202def745084202faf7450842096ee645084202fae6450842097ae545084241fad5450842004ff755844201cfe7558442004fd755844201cfc7558442004ff7358442034fc7358442006bf4358442006bd435844202e7f525844202e7d525844202ebf425844202ebd425844202ef77158442096f74158442096f4415844216ef6315844202ef7215844202ef42158442004ff705844200cfe705844200cfc705844216ef71058442004ff755804201cfe7558042004fd755804201cfc7558042004ff7358042034fc7358042006bf4358042006bd435804202e7f525804202e7d525804202ebf425804202ebd4258042004ff7158042014fe7158042014fc715804202efb7058042096fb4058042096f84058042166fa305804202efb205804202ef82058042166fa1058042094ff759933201cfe7599332004fd7599332094fc7599332036be7499332006bf5499332096be5499332006bd5499332096bc549933202cfe7399332036be4399332036bc43993320067f5299332014fe7199332004fd7199332014fc719
  | 27 => 0xf705864200cfe705864200cfc70586421a6f71058642004ff755824201cfe7558242004fd755824201cfc7558242004ff7358242034fc7358242006bf4358242006bd435824202e7f525824202e7d525824202ebf425824202ebd4258242004ff7158242014fe7158242014fc715824202efb705824219efa405824202efb205824202ef8205824219efa1058242004ff75d8d4201cfe75d8d42004fd75d8d4201cfc75d8d420067f52d8d422eebe42d8d422eebc42d8d42014fe71d8d42004fd71d8d42014fc71d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42006df6398d420057f7558d421957c7558d42005f77158d4218df47158d42005fb7058d42185f87058d42036de6318d42006dd6318d42004fe76d0d4202cfe7690d42006df6390d42036dc6390d4202dee7290d42005ed7290d4202cbe7690d4230dbe7390d4230ebf6390d420079f6390d4230f9c6390d4202dbe7290d4230fae7290d4230fad7290d4202dbc7290d4243f3f5290d42005bd7190d42005bd7090d4202cfc7650d420057f7550d421957c7550d42006df6350d42036dc6350d42005ef7250d4202dec7250d42004fe7610d42036de6310d420079d4310d42005be7610d4230ebe7610d42004be7610d4230dbe7310d4230f9e7310d4230ebf6310d4230f9e6310d420079d6310d4202dbe7210d4202dbc7210d42096bf6210d424373f5210d42005bd7110d42005bd7010d4201e7f765494217e7e76549421967d765494201e7c76549420073f74549420073c745494202e7f64549420067f635494227e7c63549420073e43549420073c435494202d7f72549421976f725494202e7f625494202f3e425494202f3c425494202f6c425494202f2c425494202f6c32549421ce7e61549421ce7c615494202f6f21549421c67e60549421c67c605494202f6f205494202dbe74d094202ebf64d094242f6f52d09420076d52d094202dee74d094202eef64d094202faf64d0942007ae43d0942097ac43d0942014fe76d854218ef661d8542004ff75d854201cfe75d8542004fd75d854201cfc75d854202cfd74d8542034fe73d8542004fd73d85420067f52d85420067d52d8542006f751d854218ef451d854218ef641d854218ef431d854218ef621d854200cfe70d8542004fd70d854200cfc70d854218ef710d85420057f75585421957c755854218ef4615854200cfe76d8142186fa60d8142004ff75d814201cfe75d8142004fd75d814201cfc75d814202cfd74d8142034fe73d8142004fd73d81420067f52d81420067d52d8142014fe71d8142004fd71d8142014fc71d8142186fa40d8142186f830d8142186fa20d8142186f860581421767f74594420967e74594421767d74594420967c74594420067f73594420067e73594420067d73594420067c7359442
  | 28 => 0x8e4202edd2198e4202edc2198e42036df7098e42036de7098e42036dd7098e42036dc7098e42006df5098e42006de5098e42006dd5098e42006dc5098e42006de4098e42006dc4098e4202edf2098e4202ede2098e4202edd2098e4202edc2098e42006df1098e42006de1098e42006dc1098e42004ff7558e4201cfe7558e42004fd7558e4201cfc7558e4202edf7358e42006df5358e42006de5358e42006dd5358e42006dc5358e4202e7f5258e4202e7d5258e4202ede3258e4202edc3258e42004ff7158e42014fe7158e42014fc7158e42006de3158e42006dc3158e42004ff7058e4200cfe7058e4200cfc7058e42006de3058e42006dc3058e42006df7558e42006de7558e42006dd7558e42006dc7558e42006dd7458e42006df5458e42006de5458e42006dd5458e42006dc5458e4202edf7258e4202ede7258e4202edc7258e4202edf5258e4202e5f5258e4202ede5258e4202edd5258e4202e5d5258e4202edc5258e4202edf4258e4202ede4258e4202edd4258e4202edc4258e42006df7158e42006de7158e42006dd7158e42006dc7158e42006df5158e42006de5158e42006dd5158e42006dc5158e42006de4158e42006dc4158e4202edf2158e4202ede2158e4202edd2158e4202edc2158e42006df7058e42006de7058e42006dd7058e42006dc7058e42006df5058e42006de5058e42006dd5058e42006dc5058e42006de4058e42006dc4058e4202edf2058e4202ede2058e4202edd2058e4202edc2058e42006df1058e42006de1058e42006dc1058e421ee7e65d0e420067d65d0e42036de63d0e422edbd76d0e42006bd76d0e422ef3e65d0e422ef3d65d0e42036be63d0e422ef9e63d0e420369e63d0e422ef9d63d0e42036bc63d0e422edbd72d0e422ef3f52d0e422ef3d52d0e4221e7e6590e420067d6590e42036de6390e42006dd6390e4202dee7290e42005ed7290e42034ff7650e420057f7550e421ad7c7550e422067e6550e420067d6550e42036de6350e42006dd6350e42005ef7250e4202dec7250e42034bf7650e420073f7550e4244f3c7550e422e73e6550e422e73d6550e420079f7350e42036be6350e422e79e6350e420369e6350e422e79d6350e42036bc6350e422e5bf7250e42007af7250e422e7ac7250e422e73f5250e422e73d5250e421e67e6510e420067d6510e42036de6310e42006dd6310e4202ded76d0a42096ed76d0a4202f6e65d0a4202f6d65d0a4202fae74d0a42097ae54d0a42447ad54d0a4202fce63d0a4202fcd63d0a42004ff755864201cfe7558642004fd755864201cfc7558642004ff7358642034fc7358642006bf4358642006bd435864202e7f525864202e7d525864202ebf425864202ebd425864202ef771586421a6f6415864202ef7215864202ef42158642004f
  | 29 => 0xcfc7058f42006de3058f42006dc3058f42005bd7690f42316bd7690f42316bd6390f4202dbe7290f4202dbc7290f4245f3f5290f42005bd7190f42005bd7090f420057f7550f4217d7c7550f420979c4350f4202cbd7610f420979e7310f420979e6310f42316bd6310f420979d6310f4202dbe7210f42097ae7210f42097ad7210f4202dbc7210f424573f5210f42005bd7110f42005bd7010f4201e7f7654b4201e7c7654b420073f7454b420073c7454b4202e7e6454b4227e7e6354b420067d6354b420073e4354b420073c4354b4202d7f7254b4217f6f7254b4202e7d6254b4202f3e4254b4202f6e4254b4202f2e4254b4202f3c4254b4202f6e3254b421ce7e6154b421ce7c6154b421c67e6054b421c67c6054b42014ff76587420057f755874217d7c7558742096f46158742004ff75587420067f75587420047f755874201cfe7558742004fd755874201cfc75587420067c755874201c7c755874202cfc7458742004ff7358742034fc73587420067f52587420067d5258742096f74158742096f441587421bef62158742004ff705874200cfe705874200cfc705874200cff7658342096f86058342004ff755834201cfe7558342004fd755834201cfc755834202cfc7458342004ff7358342034fc73583420067f52583420067d5258342004ff7158342014fe7158342014fc7158342096fb4058342096f840583421b6fa20583421ae7f74596421ae7e74596420067d74596421ae7c74596420067f73596420067e73596420067d73596420067c735964202e7f725964202e7e725964202e7d725964202e7c725964202e7f425964202e7e425964202e7d425964202e7c425964202e7f325964202e7e325964202e7d325964202e7c32596420067f71596420067e71596420067d71596420067c71596420067e41596420067c41596420067e31596420067c315964202e7f215964202e7e215964202e7d215964202e7c21596420067f70596420067e70596420067d70596420067c70596420067e40596420067c40596420067e30596420067c305964202e7f205964202e7e205964202e7d205964202e7c20596420067f10596420067e10596420067c1059642036df7598e42036de7598e42036dd7598e42036dc7598e42036df7498e42006df5498e42006de5498e42006dd5498e42006dc5498e4202edf7298e4202ede7298e4202edd7298e4202edc7298e4202edf5298e4202e5f5298e4202ede5298e4202edd5298e4202e5d5298e4202edc5298e4202edf4298e4202e9f4298e4202ede4298e4202edd4298e4202e9d4298e4202edc4298e42036df7198e42036de7198e42036dd7198e42036dc7198e42006df5198e42006de5198e42006dd5198e42006dc5198e42006de4198e42006dc4198e4202edf2198e4202ede219
  | 30 => 0xf7650d520057e7650d520057d7650d520057c7650d520067c7650d520047c7650d520073f6450d520073c6450d520075f4350d5227f3e4350d520057f7250d5202d7e7250d5202d7c7250d522067f6250d522076f6250d520057f7150d521cd7e7150d521cd7c7150d520057f7050d521c57e7050d521c57c7050d5227d7f7610d520057e7610d520057d7610d5227d7c7610d521ed7e7410d5227d7e7310d5227f3f4310d5227f5e4310d5227f3d4310d520075d4310d5202d7e7210d520057d7210d5202d7c7210d524767f6210d521e76f6210d521cd7e7110d520057d7110d521cd7c7110d521c57e7010d520057d7010d521c57c7010d521cd7e76d85520057e74d85520057d74d855227d7e73d85520057d73d855202d7e72d855201d7d72d85520be7f62d85520bf6f62d85521ce7e61d85521cf7661d85521ce7661d85521ce7c61d85521cf7441d85521cf7631d85521cf7621d85521c57e70d85520057d70d85521c57c70d85520077610d85521cf7410d85520057f74585520073f74585520053f74585520057c74585520073c74585520053c74585520057f735855227d7c735855246d7f72585520076f725855246d6f72585520ae7f62585520af6f62585521cd7f71585520077761585521ce7e61585521ce7c61585521cf7461585521ce7461585520057f70585521c57e70585521c57c70585521cf7710585521c57e76d81520057e74d81520057d74d81520067e64d81520067c64d815227d7e73d81520057d73d81520067f63d81520067d63d815202d7e72d815201d7d72d81520567f62d81520576f62d81521cd7e71d81520057d71d81521cd7c71d81520067f61d81520067d61d81521c67e60d81521c77a60d81521c67a60d81521c67c60d81521c77a20d81520057f74581520073f74581520053f74581520057c74581520073c74581520053c74581520067e64581520067c64581520057f73581520075f73581520055f735815227d7c73581520075c73581520055c73581520067f63581520067d63581524657f72581520076f72581524656f72581520467f62581520476f62581520057f71581520077771581520057771581521cd7e71581521cd7c71581520077471581521cd7471581520067f61581520067d61581521c57f70581520077b60581521c67e60581521c67c60581521c77860581521c77a1058152096df6398f42036dc6398f420057f7558f4217d7c7558f42096dc6358f42004ff7558f420067f7558f420047f7558f4201cfe7558f42004fd7558f4201cfc7558f420067c7558f4201c7c7558f4202cfc7458f42006de5358f42006dd5358f42096df4358f42096dc4358f420067f5258f422e6be4258f422e6bc4258f42004ff7158f42014fe7158f42014fc7158f42004ff7058f4200cfe7058f42
  | 31 => 0x91520057d71991521cd7c71991520067e61991520067c61991521c57e70991520057d70991521c57c70991520073f64591520067e64591520057f735915227d7c735915217d7f72591520076f725915217d6f72591521967f62591521976f62591520057f71591520077771591520057771591521cd7e71591521cd7c71591520077471591521cd7471591520057f70591521c57e70591521c57c70591521ad7e76191520067f64191520073e64191520067d64191520073d641915227d7e73191520057d73191521767f62191521776f62191521cd7e71191520057d71191521cd7c71191520067e61191520067c61191520073e41191520073c41191521c57e70191520057d70191521c57c70191520073e40191520073c40191520057e74d8d520057d74d8d521467f62d8d521476f62d8d521cd7e71d8d520057d71d8d521cd7c71d8d520067e61d8d520067c61d8d521c57e70d8d520057d70d8d521c57c70d8d520075e30d8d520075c30d8d520057e7498d5227f3e7498d520053e7498d520057d7498d5227f3d7498d520053d7498d520067e6498d520067c6498d5227d7e7398d5227e7f6398d520075f6398d520065f6398d5212d7d7298d5227f6d7298d5212d6d7298d524767f6298d5215f6f6298d521cd7e7198d5227f767198d521cd767198d520057d7198d5227f757198d52005757198d521cd7c7198d521c57e7098d520057d7098d521c57c7098d520057f7458d520057c7458d520075f6358d5227e7e6358d5215d7f7258d520076f7258d5215d6f7258d5212e7f6258d5212f6f6258d520057f7158d521cd7e7158d521cd7c7158d520067e6158d520067c6158d520057f7058d521c57e7058d521c57c7058d521457e7618d520057e7418d520057d7418d520067e6418d520067c6418d5227e7f6318d5227f5e6318d5227e7d6318d520075d6318d524767f6218d521176f6218d521cd7e7118d520057d7118d521cd7c7118d521c57e7018d520057d7018d521c57c7018d520075e3018d5227f5c3018d520057f76d0d520057e76d0d520057d76d0d520057c76d0d520073f64d0d520073c64d0d5202d7e72d0d520076e72d0d5202d6e72d0d520057d72d0d520076d72d0d520056d72d0d5202d7c72d0d521ee7f62d0d521ef6f62d0d521cd7e71d0d520057d71d0d521cd7c71d0d521c57e70d0d520057d70d0d521c57c70d0d5227d7f7690d520057e7690d520057d7690d5227d7c7690d522057d7490d5227d7e7390d5227f3f4390d520075f4390d5202d7e7290d5227f6e7290d5202d6e7290d520057d7290d5227f6d7290d520056d7290d5202d7c7290d524767f6290d5221f6f6290d521cd7e7190d520057d7190d521cd7c7190d521c57e7090d520057d7090d521c57c7090d520057f7650d520067f7650d520047
  | 32 => 0x14fc71d894300cfe70d8943004fd70d894300cfc70d89432057e75989430057d75989430067f65989430067c6598943006ef62989430057f75589432057c75589430067f65589430067c6558943005f771589431fdf47158943005fb70589431f5f870589432057e75189430057d75189430067f65189430067c651894302eee6218943006ed6218943014fe76d85430067f65d85430067c65d85431fef661d8543004ff75d854301cfe75d8543004fd75d854301cfc75d8543034fd74d854302cfe72d8543004fd72d85430067f52d85431fef641d85431fef631d85431fef421d854300cfe70d8543004fd70d854300cfc70d85431fef710d85430057f75585432057c75585430067f65585430067c65585431fef4615854300cfe76d81430067f65d81430067c65d81431f6fa60d8143004ff75d814301cfe75d8143004fd75d814301cfc75d8143034fd74d814302cfe72d8143004fd72d81430067f52d8143014fe71d8143004fd71d8143014fc71d81431f6fa40d81431f6fa30d81431f6f820d81431f6fa10d81430057f75581432057c75581430067f65581430067c65581431f6f86058143035df7650c43006df7650c43004df7650c430075f7550c434875c7550c43035df7450c430379f7450c43096de6450c430379e6450c430979e5450c434879d5450c43005df7250c434875f5250c4347f9e4050c430979c4050c43004ff755884301cfe7558843004fd755884301cfc7558843036ef72588430067f5258843096ef4258843096ec4258843036ef3258843036ec3258843004ff7158843014fe7158843014fc7158843004ff705884300cfe705884300cfc7058843004ff755844301cfe7558443004fd755844301cfc7558443036bf4358443036de4358443036bd4358443006dd4358443004ff725844302cfc72584430067f5258443036df3258443036f77158443006f751584431def45158443096f74158443096f44158443036f73158443036f431584431def62158443004ff705844300cfe705844300cfc70584431def71058443004ff755804301cfe7558043004fd755804301cfc7558043036bf4358043036bd4358043004ff725804302cfc72580430067f5258043036df3258043004ff7158043014fe7158043014fc7158043036fb7058043096fb4058043096f84058043036fb3058043036f830580431d6fa205804327d7e73d91520057d73d91521ae7f62d91521af6f62d91521cd7e71d91520057d71d91521cd7c71d91520073e41d91520073c41d91521c57e70d91520057d70d91521c57c70d91520073e40d91520073c40d91521757e74991520067f64991520073f64991520063f649915227d7e73991520057d73991521957d72991520076d72991521956d729915217e7f629915217f6f62991521cd7e719
  | 33 => 0xd755874301cfc75587430067c755874301c7c7558743034fc7458743004ff725874302cfc72587430067f5258743096f74158743096f4415874322ef63158743004ff705874300cfe705874300cfc705874300cff7658343096f86058343004ff755834301cfe7558343004fd755834301cfc7558343034fc7458343004ff725834302cfc72583430067f5258343004ff7158343014fe7158343014fc7158343096fb4058343096f84058343226fa3058343035dd76d0e43096dd76d0e430379e74d0e430979e54d0e4349f9d54d0e4349f5f52d0e43005dd71d0e43004ff7558a4301cfe7558a43004fd7558a4301cfc7558a43006df4358a43036dc4358a43036ef7258a430067f5258a43006ee5258a43006ed5258a43036ef3258a43036ec3258a43004ff7158a43014fe7158a43014fc7158a43036df3158a43006ee2158a43006ec2158a43004ff7058a4300cfe7058a4300cfc7058a43004ff755864301cfe7558643004fd755864301cfc7558643036bf4358643036bd4358643004ff725864302cfc72586430067f5258643036f77158643216f64158643036f73158643036f43158643004ff705864300cfe705864300cfc7058643216f71058643004ff755824301cfe7558243004fd755824301cfc7558243036bf4358243036bd4358243004ff725824302cfc72582430067f5258243004ff7158243014fe7158243014fc7158243036fb705824320efa4058243036fb3058243036f830582432057e76d95432067e76d954301c7e76d95434973e43d95434973c43d95430057d72d95430067e61d95430067c61d95430067e60d95430067c60d95434967f74d95432067e74d95432067d74d95432067c74d95430067f73d95434967e73d95432067d73d95434967c73d95434967e43d95432067d43d95434967c43d95430067f72d95430067e72d95430067d72d95430047d72d95430067c72d95434967f32d95434967c32d95430067f71d95430067e71d95430067d71d95430067c71d95430067e41d95430067c41d95434967f31d95430067e31d95434967c31d95430067e21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d95430067e40d95430067c40d95434967f30d95430067e30d95434967c30d95430067e20d95430067c20d95430067f10d95430067e10d95430067c10d95430067f65d0d431ee7c65d0d43035be74d0d43036bf64d0d430075f65d0d4348f5c65d0d43035de74d0d43036df64d0d430379f64d0d4348f5f52d0d43005dd71d0d432057c75d89430067f65d89430067c65d8943004ff75d89430067f75d894301cfe75d8943004fd75d894301cfc75d89430067c75d894301c7c75d8943006df43d8943316be43d8943316bc43d89430067f52d8943014fe71d8943004fd71d8943
  | 34 => 0x1402a00000080100080030030000030000000803001e0000020000002000006003c01000300400080480020010000002003000800001400b000800002400901500040020020000000000000004802800a019000000401600f00a800400200000880380120000028008000002000000400c00d000000000003c004008400600d00b804800a006002000c0000020008000000005000001c00a000005000c00000000b001c00001500000040040000040014004023000002402400500000000120020000004000000005000400e004003800002a01300080000020010040020010000008800801e001000000000000400000000000000010014000001000001400000000000000000080020010004000005800c012007006801c00800400080100020140028004002022001000c000018016001000e000002001c0180030030038002004000802c01c0090058044000014000800800400000180140000010148044000013000000001e0030038004026000000001401c002000000000200c000800000000200000080080020098004004008000000c004000001808c008014004002402000000080200040060028008006000000001800e0000008034006007003801c010000002800800000200480240020010010000002002001000004c00d003800400e0030030048006020003005c004020003800000000c0068000006001001800400a0000000000000001000805400200a000000c0020100018000000004000801c0020000010000000009002000400000000500100300000028000004000002000801e001006802c00000300000080020000000004000000000000000c0100038024000004000801c006001000001000400100000000000000070014004001003800801c0030010000018000005800000000200000040100040018014004000005801400400a00380280000020010000000017002000400200300c00000180010000008002005002002c0060040040000008000001000000800300100040080090060004008001003000c00802300000080220060028008028001005003800400600500180000000000024000020002800400000b0008040000003001000c000002002800400000c0020000004000000000400a007000001401a00700200000000001ed7e7598b430057d7598b43096ef6298b4302eec6298b43096ec6258b43004ff7558b4301cfe7558b43004fd7558b4301cfc7558b43034fc7458b4330ebe4358b4330ebc4358b430067f5258b43006ee5258b43006ed5258b43096ef4258b43096ec4258b43004ff7158b43014fe7158b43014fc7158b43004ff7058b4300cfe7058b4300cfc7058b43014ff76587430057f75587431ed7c7558743096f46158743004ff75587430067f75587430047f755874301cfe7558743004f
  | 35 => 0xd0000008046002000804c028000000804c00c0010098020000001004000c0000000000008000000000003800600a001800c00e0010008000006000000000c0020050048004016000007000000e00000a8054004019002804802402400100040060040000044008008004000800a00e0010010000007000801402e019000004400a0050030028006001000003c00200d008000001600200000000100000010018016003000002c002001000806400e0020000000010034000002800000c000002400401d000801406600c00f003000c036009001000000e0010000002000001000c00a004000801000000e0000000002000005800400a00a0000004004023005800400400000000d0000013009801c00e00b0058004004006000800c00400200f00800140070010000014000000000000e002001000400200c000800007e00a00100040040060000028000017000002c00800a000000000a00a00480080000020028000092000000005400e00300100680560010000000000001000000801200a000800c0000130040000002000006804000000000780000000040008004004004000002001a003008000001c00100600240000130008004002001003800002400101300080100010048000000003001001402400d000001c006000001000400000300000100000140010004000001001000001600f008800003200f00a800404a0160000000000006005000001e000003808c002004000000000402a001800000000c0020014002002000001001801800280040020060000008000011022800000a0070020004006001000001c00600000080080000090050004086006009800403e007000002000200a004800000000c003800000a000003802c0080000088000000001002800000000000780000060050008018002000000800c008002001001800000100980140000000040060000000005800400200000100000060040078000038005002001400e00c00a001800a003001000800800100180140000000038004000005002000800000500b003001600b008804400a00000c8004002003003800001e0010040030024007000000001000000b8018000000002000400c000000000c00400000200080060010000000000009001800c004000005800001a000001000c00203100a8000012001000001402a0070028000006000003803001e0120040010004004000801406a0020010010004001000000c00000d000000c006003000000c00000b000803800e01000400000020120020000000000007805400c00d0008044014008019001800e00a000000400401300000d8000001000000400400100a801c002004000800000e00100d000000801400000340000000018004006002005802c00c0080028000000001008000400000e000000000200000000
  | 36 => 0x3000000100100480020010000008010001002000000400c0008000010000000001800000300000080260000008000016000000802800200200180dc036000000006000000000380000000030048020012002002800803c00b003000000c004000800001002a0000000028002005800803a0000008030002001005803400804f0058004004003000005400c0000018000012001005000c00a0010000000002007003001c00201a000000800000d000004c00001a0040040002003006800800c009001000c018000001803400400e0000000008001000801800a00400080200040010018028004000003800801c0120070000002000006800803200000480080080040068000042014003802c032005005800800600d0000000002000001800800000900100080000000000050002006006801c00200b002004001e012000000400c003007800800600200f8000002003000800000200400700040460030000010006001000001c02a000000000801400500000b000e000008801c0000030018038012005005000000000600100100020020008040002002000800400c0060018020008006002000401a00a00000000140180018010000004000004c000000001804400e024000800000c0010018008008009009000402c00200200080060010048008008001001001400000000500040000030038000002000010802002804100000140000010020010006000002000000e005001000c004007000001400000b0000000008004000000000200f0008050000002000000400800000480000040040078000000002006800000000d000002400200400180280000140070000028002006000000c00600a004c01a006003801000000600100b400400101080000000000020000006004000801c01800c000805004000200100000140060030054000006000800c03200100200000120030000004006009002800001a0020000034004002000000400a00e0028008004003001000c00a000001000400000c00180000060060000024002007002800400001000180000120090110004000003000000c000008003800001401a001800c030000004000c002000000800800e0010088008014001000800800200b000006002e003000000400201a0008008006018004003400e002000000400400400100100060000000000002001000004c0000000030000000000001000c0080000018044006013000800c01c00c000800400001b00280980000040000040002001000001000a0030000014022001006800c002006000002401e00300200040020000018000000005003000800a00800180000000060040018000000004005800001000000480000020000078000001002000c00e00000d0000006008003000800200b0048000000003005800800400b002000800a0
  | 37 => 0x96a00864200000000000000000000000000000000000000025ca174374800045f80000d39a10ade800064d9b64000257ca9909880000000ab28000b2d000034480004aa000021eab64a75192024c80002ca0000ac89efa19080002dd00003e707ea3f0043c74a02f00000000000147c00017226d98000a9180006b42ad855980008b825e23c891f400006140001e442040e520001d561052850000000000012da00009e600027d242f134caf915b0087a606253810a86300006b12764261848a00003104c2819e2bf9bb44471ed676110483780860853228c8169a6630b10d03798ed48d8a2da3cfa5a66681dc61a928e018aab4c8ed1fc20000380000212873417fc1a693721d0877648c138c4ba000073faa2292d0d460300cf23caa2160000d240000000547282600005603c297100001bb00001f0e00000003732c3254000002809094b26000000000001ed87c07620c6267b000000013c2b11800070a00006490c30000060a92900008ad000000000008db9b2a95a1f14685931400000000000000000000043c80000002ae80ee11a24f7a856000094200000007458000634000040c000031612b0000225a7948d30632a2063f70f500001cc28bf8bba13502644d3893846e250aa388f8e65e90d6a24076e831a35055301f09358b048a19b506b79e0a000000000026f84a824b891a0000000135c31b800045a9454a0f000000024982f580000000000746836400021a200007fa00002961a4941a0000968abe95b2000121400023feb17286289f0b700002a3c0001b6200018b0791a8a8165297c04b1dc415c1a2e873973877c2504430904ca5c80006e900001d58000494aa60250000047511549ef9e0200028a420b000000012a6416027856981fe0002c4a7648000000171800024f47698aa64a21d220001fe00000000871238a0001656000180801719f437106169a382066fa068c7aeab820d0876619b8ac21448f765218c4c8882b9415b00001c8273c893ab5e000087645897dc1a59a5e82a00525a095d296094f83dc29ea00d00000020020030000018007002005800000500100340000120068000004001001000000200d004800000202000680100040000028008002000008002000e001000000001c0070018008018001000000c000003000005c0020100118014000000001000000400c00380140000000010000010006005800000600100080300240060000030000000001000c000006004002000000e000000400600a001800000200000180000000010118050006029002001c006007000005000000d000005400400300780000000060018028014028000000c0040010080008000001000000000000900000000020000038000000005000805800000000380000060130040000002008000000c046001003805c0380210000
  | 38 => 0x38800000000000001d0c000128642b146e3aca9da5ff9dd0743a35e00011a620692003b025065a29bd4a861ec44af05301fca6248060d50271a2842a60f0cb1b1b040000000000259e0001bba000149c00000000001fcc00001dc0000000000000030227fc2a8000000000000000e3200014462e2000037586fc3008c9e93e11fe1b78e8e32d80008a4ab7250aa120a4c07686028006ad1a914305052890c862e3cc23780fd834c9da95bc49525f0a7c1458873000056a024200015e40ab25581d82c5418d1dd6aa1a05e30682307e09070357ac0a6d600007d08ec225816907ae1e4e1768c126d80000089239e0790dc034d0bd01dd0d922a221dc17d9fe661e9d2e1f085b26df83547cd88aa4981c98958847a87fa9061ab000050f1292395060c14e802a00000000001df600018a80000132000109870e000097090fa1970000b4d80000001946000131e00017da69700006fe063e31800004248000b1598b67bd8000452a89291598800402c42617157611502263deabae3001f54a8c909a83581ce737264c70220b88f1800098d80007fb98e600000004ae2a5c00000009da00000000a5ca011322a4100003b12b2a5000aec82a800004614ec0000010ad024106ea23cc7a98a40000123c0002538000189c000168ca0e84cc90b2a1a9b10d6eb211fa430d0b1c056ab1455a9b3c08501066b99efc2e7222218f1fe2289901e0fb8ce460913ea0270000502135a0001e7c61197762ad800036102e2060924e666842a0000a204909eac0938a426c51d760001a347e59cb65ee00002892b506300de8b481d98676000015b80005f8133e000018e2dbad8496e9a189172936000099695f9ef00001600000211206f800000015247d32b2e6ae97ba54c23825a7aba234980de2c988e22d3961c56597083720e0e5fba06c0001cfc7c4a8468fe264e47622ea7cb9a1c00000000000000b33136c58512a491f949a1c5170e534a78e13b80000000b605d30f74285a9e20000000000000000000006b500001c68dfe0001a1e0002cd4000130e00012f4acf95ea000224459f800050a07a40fd285a0001276000000005d0000000086247788a45eb00000000000107000020583c678415165d408da3cb213a7ec26ee5a58382a7b11e253d03f21aeac6a13c1d1c00008440a78494028163a00000000000000ac11a2a66f2bc48fa03a4000000070b986c2e81b90000021624c0ac0000000000000000000000581000000028a60001bce8e00000000222e026a31070d00009f4010294800004f9000000000000002ab2b04273ab00a51248c91641558894180a97656d032400000ae0001ce677f8daa6a305c8000282a4a78b327c080e66bd96207c31c7e5838e76a70abaa9aa0fde499aa06000128c22989ee6d719aa226a978000031a55c0000605841e
  | 39 => 0x83028000834000020700800000000a32004c010073226418fc8ca843a51b000000009bc1de2bc28500ff69b4800083389b62428e44a8d00007de0188139a84c875800000002a0a3316ea2550c9218613d86f4999c9b79a600000e8845d8796b341dacb47000038609c4359020271927620002522b4f8a660001090a6d130806982a2704a1423e42d5a00000005f89df80000dee52c973e000135e00000005f10000a30893c273a8d200022e663600000001d0a00018fe0002c8e00000003fa80000b2059e397872600000000000ca83c92342358a1366bba5ce0000000000024c0339f243f803aa00011d000000000000000000108e5ae29ca9f284bc000045c000000006480006d098f60001494902267e628a070199a91e2d300006da11063a8000000000000588b3e02a084ea4282ceb0103b40001e2a5e8a85c25c0f063da80000000cc6aa9ad603fc1d124c92d6ca8d8000ace0000000037a54b277e92a8b80b2889d469b00000000000000015201124f08e680b20001c7282c08321cf000056b0000000088c703011e08608b08df0000a6d80001ef2c3c02197ca93100003d7800000019fa701800000000000beac228c114b474e19b689b8a82a6b800001caaf0000261c00000000002832000236435480000000150076000014c80000002cda17f800000001b6000000000000000001736079a07653893d00e802002a2a43c82ea51c00013880f0000043f8000000000045c1be241388ba1e3020442196ba00021b600011ea7aa80000001aa400000003f22d3c00980001192c6e3310000358130c754800040310128e5a2de00014620501c2264c1394548ad18a000b3a6812138ad995921fd24aea5480005e0107e0001f221b988c800010b250e2cc61e82814afa8000a3e09f60001d54641258430aa406ab51e280000a48000000096613f800028885a5000001d1a7e000006c000000048380000a408b6000289e9458000000167a000000092e91485d480b620a298a8f2075e41d1e96ae8013816094cab01800078c205200015f01fe00009089e8a594836a4bf887096910e68868cd409ba00e05110a2b54876455180fa00e87e69e42d784fd000e00006b60431acc428125e824a736000096e000000055c8000419ac7a482223045f16d0ad826006c3a0505211640ab90bbe7ce1f4448a13f66e2a434a83187813b18505bd943a291a5249630c6c00c8da685d997095108ae946996474f0bb6af5945687b861a0000a84078000091ca9c41f180009d1800017000001fb2b249e60ed82a6a71800000001840bd800000000000eda00024b6a23264039e01eaaef1b02927aca01c880123ab21f4aa0259c73600c4652897409c9dde5e11bda82193b8489070aa999f5c504808a3840ef2a06922030a11c682b203c23100284f100002ae28b08c7
  | 40 => 0xb018c41584f42d51e9a75001cc3c110523d9acf420380008f692e27d2aa6e561100e000000000011e42559d5e719a57243d9bae00025cc60124cc5d680000000ec80000000000083a2e8941814b1d4272480f0aee128e9ec194c590a3349ad21da0c0042600022d84b983605df9c8e000006059a8000a7d1c7862e035a4f4931c0308022b5e83e6b21ad1a6961a724c190467dd137665028720a48ca4a3dab0290e9ff816315a40e7a6645da855a049a316ae3a6f67cf00940002102000160675a000030319069c0000024021561a3a004b1800005888b1e0000000000000065580006252780345800000000000f296d40001ec218480000000000000000000000006e598329d51a683818000000038c0000b9e7cc0000a940fda85a18662f69ab678112909c31ba65750000112928220f24e0000000000000002c40394000000040e899c66fac3e0002b1c9bc2abe402082e0e10000b4580000f69cc4000000000027766541746000124c0000000367838e59f03bab0683ec7a41770a20abe652816983f984ae5468a2c8eb8e0209880000001e0ea5b19720000000000000042e9cf2a048000a4c8a923aa0cd61eb8e385b600009009f627d62be262798824578b4a7b9027450792ea09f253e33388541529ec0974a8dc23e909c99a1ace3e7994e6d0071298b855864c94f61a0173c60d889e68e218e0ce02585ea2c2a1f88c7eaed974a9a6107a9c0a8c69c41cc65cca90e1c222f817825887e512f071a096246302984042728b5f1c947e703264b10f1eb200890a9a1a0e07480000000000198800000025a050c2cec0000c9c0bb22084912d247c00eee000282e2ec26144cea83639805408fd9c10a2f036253f9c62a070a7a9c3ab80000007eb0d16542c00b660000d04380233c68492deaecaab638811145fe04500b7805e20809f248d80002b99c504e9000012b17e48c3000056016467af00008498000299000017082b26b90c90a7e000034a958e61900002101d9e6c42934854285e4530cbe34ba7feb32ace669a8d86a60874c90aa1fc9af8166b618fa6a238000a4600001e62aec000080a027ab5254805be770000084b1a8e000260c75926ec8c80a3a00022d427d08800000ab271500007570f625f5a3921c190009d7a68822f2950712187c38512ae8a28f540c7208867725020fc12b21c020b23cf11f850f996a27c021083e89da1b491aa0002a020001e76104aba409011ae90502a800010c6ab69a2496489344fb00002c8000000000008ea000094d8a3c0001ce40001a3a0001eee00002fc0001e9217e1cd20e58fd239b21d292280000d11c1e00005361b416c4851800031a927000009280001a78399000004a148cac019e819c00007a7976803d000083700006552cbc000132e1ca8d7280d80000d0064a35b00001510000162a14
  | 41 => 0x1445d0000032875857c80c66f1800000001b094aabf800000001179c5e2439662b4d00d03d307840001f848c8800000000009cb0000a741d50aed000000000002e30a540001e6601927da28a01546eda95601c12c05689b1e23ca17211c0cac4870ef8b032d2c920a9882522a2422396188c28220599136e34329b01230bfc000023c00026c83c400001b000009f6138654628766c898485b90ee429c8aaa4f289e200007948cb1f80962abd8000025684c8bb41029abc4bf20c420e27240000e6889d1a86057a2a080ba9ac0d28000000144e9ce1fda00000000000066000147e00014a20002964130a6f200026560000fa80000000000071879280009ab2c7e70a8000000000000000000000bac000000003f00000001d241290e98000191800016de97f8ddc33f0e2e87286bc65221c65261d1892cabfab452cb657421bc2001984000000000008e09e18000000288a928205867e13aa1b9050423aa3281ec1f864bb154eaca116800020a250d867eaa803ea000198c5c0828a9ed000009289826be095a74c15c859720de00000007c6a808a95052a1d4ad221180f860001d0600024e40002d5e00000000000772a901ece6ce1410ae680001b3906a36b29f200012969c807fe7990d3c57d287ca4417c046686748390c1c110951468f8112a4f82be78d1e5c2462d824e00ff20868c1000001c69ca80009251840977a8e8000280e00006520000a341248d4a0000baab03800010e105a79b000007e03d6109025c7d4049c23b800035a09d0685000090720a009e84c88d6972a0000822a28ad443ffa4586a6274083600000059db486b00dca1b0e56000265200000003a50474000000002388783f30372709939077c90fc0ad9fbc7c20000af291b470d800049a18864201c6c00000008e8948e00018d255829a20000000296800000016c000106a2b632b7e5371db69f890382a19fc670c2a08a5c14fc23b16ae4cb204a8b2870cb2917d00488c3271a800026c06dc1401bea4f8a2ce57a27f894c18585031ee2128255a0001144b621baa3e126022c31b4e0b2ac8a3d008fc235184c2ae800092f00000ab8000000178e5701a7c672000066e800042f8adc6dc98f885614ae591160c4de013c6e4800042b804eb5a9926190166c0000da44cf0ad4ae20e3e61c088221d11ce00009cca9a82e400026660000bf266b00001659df42160cfe3c58000a9f27bc9068000000062c49e800012c28800000000a0327f000006a65a9849ea19a94c6ff8000992aa909c70000b5ca9082830f981ba00000000b2a449000096a8000488a1e01b605ee7bc80000000000a569faa23384b26b1a7dc2fb985a00000000002d6401227acb26a32e00014f2337204e5ce87360a10ebc7ba06c65b298ee76917784c61b3a00016d21d106ec09d85343e810f037a80001d
  | 42 => 0x1a0ffa3c218ba3231b540002ce20cf96e630903dc48e85d689f99d6af714d6000070400001aa00018425fa13fe25f8e9a6b28bfa7582b48000071048300005c8111e5ec23381ef922e6ba94969e5176600019a42f0000045b901a0bd90d22e3ab8a68a139e0b50e364c01b1a9039146b141e747e628de9dc93ae2cb91942a5025e5fd95861f31e24ae4000000000000000c38000261800000008da80005c6991a6648000ae98000959074013e15de54e86009759a620df96fa93ba66a00b0f5c00000007e8abfc4f8261ea570000782291c2479a086e7abd22f3014241a0c529a786ca73e0000000000000023c0000072c3a080004b600005500000000203a8970fd65e225e48920e48440857e0002c12221109e05c022807880009c21fd07160286919150c924a63c0000000702a01000000000001b5662a8af291698020000000a4b1e3e9761a3293705d2abc800092f800000000001e21dee6dc1d5823419f624a8e6e34ca0129c49a0c4819b0686910dc96027d69a68ab438a8eeab5719ae6570fd815e993c5711c1836c811a28682f2171970c1041bc81601a6e49f04d074aa9900000e927aca64651e04307d210421621cbe7ab80d61e72cb076516ec049140eb321b86544a43838206783d0a95eaea190c6dbab184b31b8c00025bc8c99cca000000037d00005cb07709219da2a4a2bba275a1080001a3692881b4abf0000000000028c8b5c53a18f000000006269a5646e937a000000069d9ea022280627d49b9c07011509ba00b893d9c9c6da9e804780792181000091491da2f926341111e4226ba66233d9ae8183816c49603927afa38c5ec89463190f1c000000000001baaae09a053101de02300002449564905958c305ab4260e80000000fbc54d8be66aa97ae000247a70500000001bc09131bc460a091c14bac1400000088d3223e1d702aa293a2245338f68000000065a0a000001cec8fc0c36a1d00006c6000076680000000000000057c8328000797a312a6a96c87fa86c86e3800077b10a6a7d8000000231a9559aa824d8f9a80900004d114805fc896a0001e880002b0a41918c800023fc00013c690a28fe49423866150fbe91da18466a13985de969226ea38800015be6d204ca00000003108000ab7884a50114740002a1c00023d02030000678810453416a8179a5ea60d23c48f82ce041015da4f004ce0000d7818c00008bea88654d0626000075a00000bc4d500002c625ee9e28000679ad0e9fb25a296ba0726fda5f8000196247c29c68e8188a57f00006bf8000ac8283444480000000000633122c4d41e5466504fc000004218d800003a00000000fa2000144aad280000000000acc20b4a5f80000001ee6000222c0000e627dda1902302ce86a69d96b5a0fc206e211e420ac2002997a63c985a034625261c7000007b14
  | 43 => 0xb6c0001f7a3171f3e40a161aa8b8fae8da03cc4811c8478481ae76323187c18d947ee82a48800d2000000d241f0aa20610cec0f0800000019da94509a84f300007b4a5766de9b7400009942ef18c600000008eb283800000008b726c026600008ed80005e7800061125d00fa252c937abec000277090780003878f60846a6e403fa57479e1fe47bfa60e42292480001c2c42e00001e994c6123800005a2a1400003ac10b0000460ab9c0000000ade00000df1c82045000091c00000000f365bbad6651002d017a000000000000002b1e00000008c214889b400005b691b25b30b8602aa0c02f288d200015d896b275237601dab4424ac53b8ace96e00002d78a44303800061b8a602fa017c0000000000000000001bc6e01c5248d175c5ef118428504668a005c4b3e9d8e000074a00023f423320fc000000030ba336b2593164421adc000836e37524d87969e560e28b3665e131093f285805710ec95705e28ac9b4659e00ee752800044886609c9acac73aa460abf8cc06438ceaadd0cd011e18527681e1e325a1525099d70aa8981a87211e867906d6000220c894116600014da2cb22e867c0d5aa6f978250d160823e11c01372b5a20083d0149abde000138e441237a00000008ee1e14101899a03200000001dce0002204b0e8ecc44b8b44432000059280007da997c00000004eca4f222b16386ec80ec8e71fbe00027c6759a508270a6860002196b310404b0b99cc5110336a7480006230000000000000000007cca69032d0000306000034a00007d8204c99721aa241000000000000002bcc37b000076a28f06ef0000000010e36e80ac1f7800092c16e032e80008122d2600000000002374217800012a90ee00f1d0000000000af00004bd9a94917888813c841a08b895ca12009600000006a120f04a69bd80000000826a73400010964b19f8a9d309fc00000009952c1c0002be86fd1fc40000dfa0002348aef85240001338a8809f80741c3e0ebaa7684f237e36715ba7499aa08298cd89a90d10059000028aa164ab3864875ca74a18701a27788eaa68005f04eeabf4448000043900007bd03e0000141600000004a1000081e84b65d123543fbac2c96529d854f8f34007800036c14a600026208bd00000000000659a6ba08ea6f47ca2c740000cc86cd82c4169939c66190f825b1b2c633ab440001d14000045869524fe0001d1e393800020921606000000000019a8bb800020f889666205f400020f200000001b0851606027b6a0b0b8480f86b4a50980698c20d4ae48facb63a11c40d0000966952ab589a2085895f658c000032e097615c800049580842bb926e9a596c25c01bfc0521686000122a805957c0002d4e0000000000000000000003c500000000000000011c58499fe0001b267cb203042c0b7a95517247c40a5677487a83
  | 44 => 0xae18000239969c756902e0000000a0c16e29f30a103628000173000078821de0001ca8000205600022346ab0ee065b000039f9ffe4929b9a81808d600005a207eaa7a7b41e00412a4500000000000181e3c6145a38f086eae6142200000004ef223c14380000000b6264a9b5a0c7948a8fca7a0355047e15994e446483b0911a78272c80000000000a8e162c340aaf685ea9dc8a58fb00000c5e0000eceb3d917a000158222c800011b80004539c704ab04767d7813e04d166e000274414600001262706038000000000004fca182000000000020447321c4200000006899d4c435270a852850283d89ea4f72a9c000000043d24806f3032a56aaab03719ef8000170488703d822d0f1a0000f025a392748b8a596443ad407ee011635da9a0155089298b145e000103c8d811360999212a44a19e89925b02b7800000013fc51409804e6800000000004aa921667c80007fd8312738830699d9fd492312182dda820332a7c4aa290aa8f615106a9806890108fe00017deb2fa6dc467013a8f924544da0cfa5b7167222805ac8188ca64090b0610b88309c78000000000000015dc00000000ac2920593a65a029000046400ba3bd00000d7a6440000a3e70e8eaeb4300009ae119e0000000334a67a0ed9e2200028600000000000044697b0000744000056b800000000008348bde66780000d9800030f8c768a60000a3c800000023fa798196e0001abe43a00005c48fca0002992728ad021e2a2d62eca24019a82802540e1a4b81cfa4bba6cc000212a64f885a7a507d45a6a1e27222a2c6658c80acd000000001ac63e8a6a7df02e0000121a9f0a7f24089a4c0002ac4172aa5841100000000d06ad600000ad24245f187d8000000031f16321e795680a099a66b580007ea000040282da1089fb200002cc7ce9d742b1956214229fe8619dc26c9000002d07ce37427c05c291c4a2d884c6f90c046060000902a78469400000000000000017845cab4e10ca2be0001e2c00005380000fba36d00002e900000000000950286a7960000aa20000130155e6d30000000089c9d8073a2b680002829bca0000df26e610cc0000000882800000008261cbad4811019d200000003fd0e5800006d49ac00008f52c4c0000f468488818301892688511ee71da7b815a844c1f288869768ee8596a1f02e584c472021e825102600cc89e84728bce700ab10a2126fc9ad80000001d2c00017f0000022c00023700ce821c326000026f800020d030c000000000004004b70dc261d00004559b9400019742c697fa34019b00002cd647300001c91ede59d800000022b00000a589b60f4400028ee00000f80001e82612a4740000000148091a00013fa23718983e5a5fc48f83fe000181400004d61fd801826e00000000000000000006280007b2228234e1fb4530a
  | 45 => 0x284e45b2b1a8978156a5d03a605d800000028b400025dc000000000021f891aacfe000024800e24180001fa082700005bf800011200009c5800093883744d921a66ac80005df1d349f5299c0000d1c7259468230a9609859c1c89ea6e26f5aabc86c91880000e0a59c2d8a6509ae062b0000000000000028e463820bea2687486be87fc020a394555902625f04e211891341a61b309a11f8e0f39bde00017c80000e1235d1b0a00007ac4368000000238e0000bd40000000083a70480a23be2b4292273697a0b3ba26656da71a000260471721c252d9020000233e35395b832c18da0001bf20150f642da27f6a7201201cf8ba854f1f26a3d10e2aa312fa337a48e53a9c903889ecca3b2bfe0001014a7991dc5d61e70b4280000002c308ae8000562017e5ac1d32a0a0ca082380006489062b4b800050b0ffc122000000021f26b4a08413d92642e68000ae30d8c437a74e7fc000000002dc4b58f2e120915a2b61f888bd88f48f28000000129899ba14461fad286c002520cb09a689580000c080006e8800096a00008840a7e49a89921211b7878719443a100006e080000001054a36a35688ea2946ef800085b1140a93800098e039856699341aa1d0238a0000640014a3769de6115a0a40000e0caab03a2113800000015fa16f01304d1800060f18d40000abc000213e86709a20001910a01915c3df80008e912b602406f661d9fec000218047c8000000000007200001af80989d704a64ed800000000002d099906470f2818825f4b251f460002d760001fde4a50910a110000a522cea31d2b702f18000000229033a0236aaa8acc4b50e90267ad92758800033b97d2b5529a46a4aab40001bf0527837657b800060fa53a5ca26940000de20001a063f12a4266c80001b69af40e6a81078b9d468bc812eb3f000049700003dc8fb46fe800088aa0069cc00000dc0000530195e95e211436698dc96f9dbc570a23272d0b9200024ea0000000000004630820409a8183060322d2ada000000020bc2050000298829cb2a051a3c393ce76e2b12a2606ea19c84c64a881865fd0c7800027ee81f85500000000a4b8000ad89af02da8000000000026915f8912a6a62020000000217018e0000b0600000000000000206653c0000000076285e0000000000056294702bd85221c5800038b2c765789b2860b800077a155c78d9cc01a50a0e0d7000000019ea5351f720000000589224600000000000000acc800088d8000a6e9a7a4969bec00028520000f209f98000000000099f28aa54200000000b08a94800077aa24a80b1caa0bb800000000005be183811b181c0cf157e96d2560a4e22683239f0a98c800091b1fe82a418d600011288f9911a0000000a259fdcaa6a7667b7249c0000916000137e0000d7e000292a01d80008a6a17c0c800007a18000
  | 46 => 0x90d86246c8047240583fa00000007ad15d600000000000196510800099209249978bf6728000096382f88649748000188e543800000020e000003f86e129d6000111095bacd2a9d19a202c15e03c487c456814de134a0021360fe239f2d563970000b2b9f5a00028429b51ea2ac5a00c6f993f09e32af8a2e0000000297a0e70000000000072900006139d7881a886c3e080d897524c000023580000f942260c940002c3866d127e1ee1dcc5859a2c3ae1c5a0001a743d208361450000000268ca9e1dca879000000024da0002cf200019762422042000000069002d274d800005c8000000000047b1bdc000055e5e2aa7e8bf2bc60000d3e00011a8705a6fa28c0234044144863c9db221a06aa7e9a400b1c00000000000000000000000007c8000067f1cbc000242e07c800050280009feacf0ae5ad468db20741020ea20000c4400000000000000000000000000002cd0000174257a93400005978000000068a23c0000000098a2c52642000212e000090c19a0aa495780000000000aab960aac30000000000069929465aa8d8841b04ba00000008988bc4000000000000009eb80006908000215a7e42e60000365812a00019520002bf000006220000000152136a00000002019c7420100003f3800091e1eda98eab9e78e97940001e6a60a87460562b080000000672867c000244e00018ea0ca1d7a00000002942caa00000000000000443004aab080000000000000106e1039c56b1024a64eb0aac3a78c5083fad58a8c0d7a03aa26cac384be00000008fb9b16ab704a278c8000b020000000176c3d39c600002324193040c0000dce96d800000000009b3a8b20000000000023e00000009dba26000027a657992ce00000007038b3c0000000857251e00029cc6d1097a0000632aa10000000078200000000001b5286d277c05a9e8443617960001d9c35f2aba74e94247628050147ac647c70000add895e86a21182e40d903208e268ea89deb0906f2972875446f146a9e91a4a3e22acc35613e68a912e48089d80a9c901800022d000011c252f0c1ea7907300a225b21a209581a40d708d02b3a0001e26a2f800000000000002d38573800095aa7a2000000093a249a761827e0068ae01c085fa845a79c36e01f41531666312aa6c7750000aa907d60001d3ea1517b4af38922000250c00d0000000162ea3a800009a0db6000065a0000ae40002d6e000293a00000003dbaa94000161e00017401202732a2717a48d182ea13fa38499425fa4ca9dd8677829a187819063b084600000007f28000000000082413b0000000078f1c8c00010025429f64095103638e9138000000000009d28c5000010d80000000000480a2a860b0ab0071251816a0cda1d40000000253400012788c19ed82f89ce09f3ab5c7b2a6c6343a0ee2d6a54a89a945c000
  | 47 => 0xdab6a9b821e6176219a1e015583ee0b12000020c5019ca69082ae093394b075f9dba859ab26a32a34ea5a8000b3928d82ce209ea2b8cbca1c2aea000119857b00005afac1e3b880007f016f4b47a878868201e8ef2528b189f0400000001f48eb02c3868290c27227bb26d629e14beb3618e819d800053e9a1a15d00f66c49a8057f8cc21f7007c1e40bf82b29f9207a192c65600001509860a60210e6922288a618b480000c861b322024e292be889a01c00026fe000273e000000000027e880980007fe800000000bea538000000000000000005e6000095b0334000000045480002d18000b0980008432bda0000000000286484c189085aa792a0f9f9e00022b812d1a5a4f591a0874234a8e416a41ae00d447200003de081264e060632c9f682d480008f59fae2df91a471129b245e08529de87ee4d61e188551ea488a171621429267d380004d98000a9302d89e59e6829a00002c28a3634786b01cd00005a200000002080432800093ea20e353024445093a2000274821c97ce0001c1a21f8000aaa00000002b3c00025c60002966000000000020ea0002cc2b5fa16e23903fc000000059a0a7cb1780000001d480000000986aa9eb4c0af80d20ea4554262692a0000b2091004bc8e4a00000000000ed0000000010a0000b1a2412000068475a937067ba5e8261129c4ef9c7c0c58dbca73a34482bab5699d09fe00000000000bc2826197e445850a05e9f6c3db000000000001951bb86ae0c469a4aa5617f09c87b1a2ec00013400002d3a000074e6b0092c98aacc061a0cae54ba84aa3400001f81dae000093ea7780000888be0000000055e1bd08dd800000024d427e8496713800017a8ac40001006a610000490076a3af97d82db1392000150671ba8c000012d27410000a491ab01618e1c292912a6a7198295198ae00007e4b5280000ef91ac4c68000a358000815108c3388c560ea0000498848640c800042103e2556a40c7ba8212000243e000000000000000001ff4b1c82469ab97aa0000df09dd16608a794603b29e1a988a6120f780000000da21bba93c465840200014a48b3290c8ec841800001c283d006e8c0000000000009ec8f3a000000000006e26cd000037f0ad200023de1ab80005240000000230e0530000792041675b2ae6000000021a800000000001ce00009980000348856216483d4000150200016749ee9e726d28e5a21210504f500e40cc18265208b02355800008aa8ce1eaac58a1a14aa44280007332c9e0000b226c221ec87e976000000006919076640aa700002c4499619c483689b47f5a2f015e01f63ec800000000005e4963400000000001cf600028c4ac18000293224c78580005ada69c5bc0e4c44628d48ceaa48000000000028a091f103e16da56600026280001980a8380004e817749e79072000000
  | 48 => 0x2c90000000000000013da0000c8a8ad800007286645d3a96212401a40750000b5c25c8000000000000000ae85d4000000081a000000000000001db00000a0816e03561bd23ba00017340000eba99ca50e33c0bf039e986a0b19a2298226b2166843eab1a3d2458000004d8f0000022420000000aa5912c16e9ff21549b5e00013525bf11b02aba7de0000a225bc905c2548ccc4d8a99411684da52e2d909322d04778027003300007000efe3b181b23fa26c202218de55b17be41798e20002af47f227568b90a6c6281ad89198160621059c000281886209e08cc1ffc0029554000248810825486b22940000028e13a1d8244e952861c8af030f15909d0a490931a0821a82462b1209d80002276000130400016bca5a094caf5006a6bb215e50091e60681526abb90b4a45847cab49afc8e622a272e0e345c98d446cfa2185e188e82450e745d50b7c28480a23d295ca97107a22fd1b88a5118c23609e6e5c7218a11a85de7c7ac16aa39f349d40e806719aae939ab2c86f980e19782c23a99eb0a56159875126aa0000f922ba8c700da000044c2b7c8411a9e629989617c8f7c8230d40b14aae28b20b822bf00583900dae00013840f4882ab2c9eb6294800016b8e04aa62496000000000005dc00000009c50000000139600000000001d201611cf400020b667000004f2000000000000e217b600000000001132a7b851c47f000012687da000000000000003639c325cc00000000000519000094c8000000142000000000002cbaa40800079880000001b6c91000003ad8a2e8cc88c694b893a00023ea000000000003143d609c051e80002170b300828000b379060000000029d0564000263e53600002a700008b116b23a180003a2860872b162a80c88b85148aa86a080000000000000281e0002c9c29c2020000000042223dc3bd800000000000000e9c2af800031c80009b9866c5cb80007dc2c90000000006a000000000006948000a250000709069c6392a3e000205c3b9a7a80001bc245613a65199ba0000228e016a1b00000b562861f166a592d08ab18bc15386b289c80307a60d0aa52a9c03e3101c73b95c62e98b789cb8edc4601e9c66e0d989fd198a0001ddc5f0ad123268000000000000029fc2be80783728e960001e4c0c39c8a86e9544622081e8441610ab41c3ca87800075380000002d4200000000000f800000000876000083e268080a80000c224ec00024c200002e6000000000000000000000895221e13eac667818faa7379c4c97caa8202481464e080002288644ab022c60002a040d6014e000121e2d41c2003690a4a840000000000000000000000ae8000191662fa80a37e00000001e38a00aa3a0001ed49db09dc5fa94ba4ed2c924382d324ae959c75ba2580000e167d0206e58f0ce606607d046
  | 49 => 0x93121055d0350af817906041ae2b13800067080000001e40000000081f1f9000005b40002a4400000000001b325808238b5d2cf80a98c5a000003e1ca09aaab5a1d4179001400816b4a67800081927aa461a000961947200029963be937400000004ea1b76000059883a2cce68f19d00c10e460000dde0001cae0000e720000646000003636a000039c000000026106f802d6a402a269e680000000000297a57080508a8433a3b0000000003ca2703fb00003288c2254e16362d0000050c97641ec8cf480d2c7808ca3c23bc00000001fd847d91d69828000000000000000004ca0d084cd198e40b144c86b94c86c308d8196120a04226700000b8a000133000000008401772a92878689e14768028e2436815cc55e8000b60000086e1648000028c0001aa2a10178c0002510841a8baa85a9b82b897e600009e40000000000201a11a000055480003b7902a67804ea0000b720ba16ce0002038733878ea8a9bac26c96507119cf04d28fa42a58a9ea08879a32a990a1c7a98c2ee0568870055c5f501ee9702d505380546067000018e926c00000009402cb82199f8c6a22c5a0f12b541690fc63a30e6a00018b2431142e00000008dca816075a542912000000000000001cd41b104e0000000000016ac000210a13906f8000266c31e9f66322191ea1f92c23bf00000000000712923800019120000a060001fce10d0000a09000000022c094f1f2aa638000000254c5e68a8c0651cba38c0d48ae113eeb4a830a8250fe453300006738eec0de0000000275a00000004d202c00000bdc8d7151e000050c0001756194268a0001628000000000000000000a046ad05b03ad07e823d8c845899dda0002bb08d980004d82a2800020e2a7a0b9415da87ab1f09060000024550a4d2921176244f9c04a399d902191ada00007b4000175e4c8000000000008ab992e2a029bc7f480007ed98c4693800000003520001c9a0db25e05248b6465680008a7163e1a18000000000000000006bcaa9200000005c7954a00003e4000299a8fb2c88910877cab202b87b80000b37000000000008118f5a8c0abf2000214e1be8df63d49960b401ea800001fc6a2ac3612a1e7a964058e7a396c68f8989212e0d42a9690eaa6a0ac814f8a1e52b21ea5f3299855b86f0a829e508321d7c0000000000092e310296e3790000259839072799d4000193a9ba8a1c5520f3891b88de00322c2721991435983b29f8137c97da0c29110c660e191d25b5a7ea3f4291a5c50d6a0000bc830ea2a60940a8e2b580006828000000165800000000c8870e263800024800000000cf8000118aaf00bec7100ed6000295436012f873588ca2c5928aa848ff89b695941f223ce25283c872c1302000113c0000000082000000000002bd132617b150400021f6a98a0cca1b9312000005600000
  | 50 => 0x12465d09b1cb00062847e92b4489ac8c00000003908000394000022f8000313ad4c7422b3669c000042d90784fa1dc84d58590a69a54e315186277eaa5eaf418128d48f8a932800029d800083b026c61584de1939f184cc877e62d199886502f49d616a27eb15320000c48144208a0001e8c0cb800077f159e1738bfe00009643f5007a0001928894a23876a80001dea552849141c3b4831800023a600010c01b82426608000042a00007830000346884282583460ef09026291ce8449a17e608979c79f80000000d3a6fb850609a800033812c80002550afb8000000100484d2198000002e4cd80009f200006cb9f7e0001ac2000215a29b9f9a00025e605b9a90000065600029fa0000d140001f560bf80008aaa6788af1a02691118ea2b12804b28d5c5ba0000af216a03d586fe6df12725fb09ac7db98f46178000000278816aa6ca2728bae71e801cafd8b5877911be34b2a0027b231e0000dbe81e28fab29800000000001a78c2676f80003ed800028e28fc5dba6a29a0a7785a00f32539a6bc8849342aeb0bea00020e62f4ad065c1ab6e0a514a81148d362632d0825e0000399853cb0a1a30000067a00007ba5a129e01fc087c5
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xaac8259342440070f90b3b484880021fe15769091001c3e42aed212200087c865d642440010ff0fb2c84880021f61f65909100062fb2ce72122000c5c659ce424400193ec939c84880032719273909100062fb2ae72122000c5c655ce42440031e90cb8c848800a3e219709091001c3f42eeca12200087d85dd942440010ff0abb2848800e1f21576509100045fc22eca1220008df835d9424400d1b906bb284880023be0976509100045f43cc8a1220058bc8759142440c353906b228488016ab209645091000c7b436e2a122000c7465dc542440070f90b3b084880021fe15761091001c3e42aec21220128bc845d842440011bf06bb0848801a3720d761091002c76412ec212200087c865d442440010ff0fb2884880021f61f65109100045ec3ec821220018f4865c442440051f10cb8084880173a189701091002c6f41ced992200087f855db32440070f90abb664880030fd9674cc9100061e32ce9992205dcac629d3324400187ecaba664880030f19574cc9100054e422c79922005acc8258f324400195ce9b1664880063d21971cc9100063a32ae399220019f0805c732440070f90b3b464880021fe15768c91001c3e42aed192200087c865d632440010ff0fb2c64880021f61f658c9100061fb2ce91922000c3c659d232440c5938c73a464880030fd95748c9100061e32ae91922000c9e74d8e32440031e90cb8c648800a3e219708c91001c3f42eec992200087d85dd932440010ff0abb2648800e1f215764c9100045fc22ec99220128bc845d932440011bf06bb264880023be09764c9100945f420ec99220008bd841d9324400b1b90eb1a6488002a7211634c91002d66412c6992200387c859d832440010ff0abb0648800e1f215760c9100045fc22ec19220128bc845d8324400d1b906bb064880163b209760c9100043e432ea192200087f87d9432440010fb0fb2864880023761f630c91000c7a432e219220028f8865c032440b18ecedb2e828803e3d61f64d05100071bb2ec9a0a20018f78759341440014e90ca9682880e31d9d952d05100055b43685a0a2058c7476d9531440b1ae0e1b2a62880063da1a744c51000cf9404e898a2000e576518d314400172b0831a628800a7521d434c51000cf8406e498a2000de220dc931440014e90ca9262880e31d1d9524c5101c6b8382a498a2000b9584cc931440015a90c99262880067ca1f704c5102c63a3b6ca90a20018f6869d121440031e90cb9a42880067c201734851000733b28c490a2000a7486549214400b8e8eca9242880179918952485102ce3c3b6ca9022000e6b6518920440017930631240880029e219524811002e3c3b2a49022005e686254920440015d10c99240880027c21d3148110007e0992629022001af08648520440059e0ec90a4088017b81892148110
  | 1 => 0xd0fb2a86880021f21f6550d100045f43cc8a1a20068bc87591434400d53906b228688172ab2096450d1000c7b436e2a1a20028fa86dc143440010ff0abb0868800e1f2157610d100945e422ec21a20068dc835d843440011df04bb086880163b2097610d100045ec3ec821a20018f4865c443440018e8cab88868804b2d1917110d100366a31ae221a2000a6d82dd762440014db043aec4880021fe1574d891001c3e42ae9b1220008df835d3624400d1b906ba6c4880021fe1573d891001c3e42ae7b1220008bf845cf624402517908b9ec48800e1fa1b75589102c43e436eab12200087e87d9562440010fd0e32ac48825f1ddc465589100061fb2ee8b122000c3c65dd1624400187eca3a2c4880030f19474589100062fb2ee6b122000c5c65dcd62440018beca39ac48800317194735891001c3f43eeab1220008bf845d5624402517908baac48800237e0d75589100346e41aeab1220008f7815d562440010fd0e3aac4880030fdd774589100061e3aee8b122000c3f751d16244001878ea3a2c48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880032b1d372589100066639ee4b122000c3f74d496244001878e9a92c48800317dcf52589104762e39ea4b122000c7475dc562440031f50fb82c4880121f61f651891000536c16ca3122000a6d8219462440b58eae2328c48825b1e5c065189100061fb2ce83122000c3c659d0624400187ecaba0c4880030f19574189100062fb2ce63122000c5c659cc62440018becab98c48800317195731891000477c3ac43122000aac84588624400159906b10c4880021fa1a765491000536c14eca92200087d829d952440018db053b2a4880028fe1176549100051e422eca922000a5f835d9524409f4b906bb2a4880029be0976549100053bc0aeca922000c76811d952440018eb023b2a4880031d10476549100063b188eca922000c76211d952440018f5003b2a4880031e60076549100063d100eca922000c76101d952440018e8203b2a4880021fa1e64549100043ec3cc8a92200087f8759152440010f90eb22a48800297e0d645491027d2e41ac8a922000a6f82591524400b4d904b22a4880169ba08645491000536c10c8a92200087f8758d52440010f90eb1aa4880028fe1163549100051e422c6a922000a6f8258d524400b4d904b1aa48800e1f21f62549100043fc3ac4a92200387c87589524400147f08b12a4880028f21162549100052fc1ac4a92204fa5c8358952440714e90cb8aa4880031d1d971549100059a422e2a922095b67825c552440734f10cb82a488252dae097054910006b8b8ae0a9220058be849db42440010ff0abb6848800e1f21576d09103154e41ac9a122005
  | 2 => 0x972cc52001c3f428ec98a400087d851d93148001998ec99262901669da0774d95102c53ac0ee9b2a2000c3d741d3654400147d0839eca880028f61073d95100062eb98e7b2a2059a76811cf65440b14eb0239eca880028fa1072d95100051ec20e5b2a2000a5e831cb65440014bb06396ca881669da0472d95102c53ac08e5b2a2058a7a801cb65440b34f300396ca8816b1d5c465d911000c7ac0eebb22204ec7571d4b64440010ff04bacc88800e1fe1f52991100043ec3ea5322200087e87d9564440010fd0e32ac88800317d9773591100062e32ee6b222000c5f651cd64440018b8ca39ac8880031bd9772591100063632ee4b222000c6f651c964440018d8ca392c88800e1fa1f75591100043ec16eab2220008df835d5644400d1b906baac8880023be09755911002c76412eab22200087e871d564440018beebb9ac888003171d773591100062fba8e6b222000c5c751cd644400193ee839ac8880031bdd77259110006363aee4b222000ccf73dc96444001998e7b92c8880031be1772591100063642ee4b222000c6f751c964440018d8ea392c8880032bdd0725911000667b98e4b222000ccc731c964440010fd0fa92c88800e1f21f52591100062fb9ea4b22208ec5c73d4964440018dee5a92c8880171b1cb52591100045fc3ac83222000a9c83590644400155904b20c8880021fe15731911001c3e42ae632220008bf845cb634402517908b96c6880021fa1f6558d100043f438cab1a2000c3f65dd16344001878cbba2c6880030fd947458d100061e328e8b1a2000c6f65dc963440018d8cbb92c6880031bd947258d1000636328e4b1a200387e87dd563440010fb05baac6880022fe117558d100945e422eab1a20008ef825d5634400b1d904baac6880021fa1c7558d100061fbaee8b1a2000c3c75dd1634400187eea3a2c6880030f1d47458d100064e3a6e6b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000c6f85dc963440018d90bb92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d100043f43ea4b1a200387c87d49634400187ee9a92c6880030f1d35258d1000637b96a4b1a2005c6c72d4963440b58eae2328c6880030fd967418d100061e32ce831a2000c3f655d06344001878caba0c68800237e1d6318d100054e422c631a2000acc8258c634400d17d093b686880021fe1576d0d1001c3e42aeda1a2006a9c8359343440bb55904b2686880021fe157690d1001c3e42aed21a20018f4865c643440070fd0bbb286880021f6177650d1001c3f42ceca1a200087d859d943440010ff0abb2868800e1f2157650d100045fc22eca1a20008df835d943440011df04bb286880163b2097650d1001c3e428eca1a200087e86dd543440010f
  | 3 => 0x790a6000c3f749d165c80014ef02ba2cb900029d20574597200051f424e6b2e4000a3d849cd65c80018bee739acb900169ba0a73597204c536c14e6b2e4000a76819cd65c80014eb0339acb900031ddc671597200051fc22e2b2e4000a3c845c565c80018eae238acb900e29ea0071597200053cc00e2b2e4000a5e8310565c80014bb0620acb900169ba08415972000536c1082b2e4000a3e840c565c800147b0818acb900169ba08315972000536c1062b2e400087f855ce64c80070f90ab9cc9900162f21173993200043fc2ae3326400387c855c664c80011ef02baac99000a3d205755932001c3f42ee2b1e400087d85dc563c800d17908bb6879001637e1d63d0f2002e37392cb21e405c8bd8799243c800b17f0eb2487900031b5957290f2001c3e42eeca1e40068bd84dd943c80010ff0abb2879000e1f2157650f200047bc0aeca1e40028f4815d943c80010fb0dbaa87900021fa1d6550f200043e43acaa1e405d8bf8759043c800117f08baac39004a2f211755872001c3e42eeca0e400087f855d941c80070f90abb283900021f61b75507200043f43acaa0e400087c8759541c80051790eb22839000aad205645072001c3f42aed98e400087f865d731c80010ff0eb2e63900021f61d65cc7200146e43ac698e4005ccc764c931c80010fb0f3aec89000e1fe1d75d91200061fc22ebb22404e87f825d7644800187aebaa6c8900030f5d454d912001c3fc3ea5b22400087d87d4b644800153b0620ec89000327d9173991200964e322e7322408ec5e73d4a64480018bae7a94c8900022fe1175591200046fc1aeab2240068dc835d564480011ef02baac89000a3d20575591200045fc3ac832240128bc845d464480010ff0ab88c89000e1f21571191200062ebaea7b1a400087f855c763480070f90ab8ec690002a761031d8d200364e31ae931a4000c9d74d8e634800117f08baac69004a2f2117558d200046fc1aeab1a40008f7815d563480051e902baac69000237e1d6318d2001c3f42ceda1a400087d859db434800d17908bb6869001a3720d7690d2000c76432e521a400387e859d943480010fb0b3b286900021fe157650d2001c3e42aeca1a40008f7815d943480051e902bb286900023ee017650d200345f43ec8a1a4000c3c75d914348001878ea322869004a37a1f6350d200062e3aec6a1a40018ec865c8434800b1f10cb8086900ba1fa1f64549201c43ec3ec8a92404fa5e8399152480014bb07322a4900169ea1b70549201c63d3b6e0a924005b6a82dc152480718d8eca9284900038b19152509201c6b4382a4a124006c9c635d3324800193ae9b1e64900e31b1d9524c92027f2631aa49924038d687054932480017930021a649000e1fa1676d05200043ec2ceda0a400387e859d941480010fb0b3b282900063b21
  | 4 => 0x2d000193eeda1a65a00062f21175587400146e43ac698e8000c5d75d4f63500010ff0ab8ec6a000e1f21571d8d400054ec2063b1a80008df8758c63500014b90ab18c6a01762f21972d0d400062e3aec6a1a8092c3c76dd54350125c38c7baa86a023ea7a1b7350d400354f436c6a1a8062c9c63dc943500010ff0ab9ec4a000e1f21573d89400043fc2ae3b12800387c855c7625000155b0810ec4a0002ba60021d894000477c3ac43128000a6d829d9525000147f08bb2a4a000297e0d765494027d2e41aeca928000a6f825d952500014ef02bb2a4a00e69d205765494000596c1686a928038a3c8650d525009fc38c6a1aa4a018a2f21973d09403164e31ae7a128005c3c76549425000bc58c4a9284a001a2f21276cc9400043fc2aed992800387c855db325000b1b906bb664a00062f21974cc9400364e31ae99928000c9d74d8f325000b179093b464a00062f219748c94000c5e432e89928061c9c635d1325000337100ba264a00062f219740c94000c5ec26ebb0a80018bc865d3315000d938eca1e62a0003271d9434c54000c5e432e990a800087f855c664cc0070f90ab8cc99800e1fa1f75593300043ec16eab26609287e871d564cc0010fd0fa92c99800e1f21f525933001c3f42ee2b16600087d85dc562cc0014df04bb2a5980169ba0a6454b3000536c14c8a96600087f8759152cc0010f90eb22a5980021fe1576d0b3001c3e42aeda1660058bc845db42cc00b1bb06bb485981862f61e6490b300364f39cc92166006c9e7359242cc00b17b09bb285980021fe157650b3001c3e42aeca1660008f7815d942cc0051e902bb2859818a2fe1d6410b300054f426ec9966005e4c6254932cc00117f08baac39804a2f211755873002e6639264b0e600087f855d941cc0070f90abb2839800a2f21d64507300061ebaea9b226000a9d83107644c0070fd0fbaac8980021f60b75591300045fc22eab2260008df835d5644c0010fd0e3aac8980030f1d774591300062e3aee6b22600087e87d49644c0070f90fa92c8980022fe1d64191300051e42ac832260128bc845d4644c0010ff0ab88c89800e1f21571191300965a20ae23226000c3c75d91434c001878ea32286980021fe1574d893001c3e42ae9b12600087f855c7624c0070f90ab8ec498002b360c21d893000574c0043b1260008ef87588624c0014db053b2a4980028fe1176549300051e422eca926000a5f835d9524c0014df04bb2a4980029de0576549301cd3a40aeca926005a6e82991524c0014db05322a4980021fe1d64549300043e43ac8a92600087f855db424c0070f90abb684980163720e769093000c6e432e721260018dc865cc424c0011bb0f326649801637a1e644c93002e2e3b2a49926005e4c62549324c0070fd0b3b282980021f616765053000c6e432e
  | 5 => 0x880a37219744c93102c6f43cc89926205ace82991324c40b59d0db126498817171d9524c93102f26312a499262028dd83dd7604c4010ff0aba6c09880e1f21574d81310061fba4e8b2e4200a77815d165c84734e902ba2cb908028fa1273597210051ec24e6b2e4200c5f739cd65c84734ed0339acb908029d60673597210063db84e0b2e4200a3f845c165c840147908b82cb9080297e0d70597210052e41ae0b2e4200a77815c165c84734e902b82cb908e69da0470597210053ac08e0b2e420087e8790165c84010fb0f202cb908e69da0640597210053ac0c80b2e4205a6e8210165c84014db04202cb908021fa1c30597210043ec3860b2e4200a3e840c165c840147b08182cb908169ba08305972100536c1060b2e4239a76810c165c84014eb02182cb908021fe15739932101c3e42ae732642058bc845ce64c840d17908bb6879081637e1d63d0f212e45ec3cc921e42058bf8759243c84070f90bbb2879081a2f6137650f210043fc2aeca1e420387c855d943c84011f700bb287908063e2017650f210043ec36eaa1e420087e8759543c84010f90eb2a87909762fe1d6410f210045fc22eab0642128bc845d560c84011bf06baac19081a3720d755832101c3f42ee8b06420087d85dd160c840187aebaa6c8908028fa1640d912101c3f43eeab2242008bf845d564484011ef02baac8908021fa1c75591210061e3aee8b22420087e87d4964484070f90fa92c8908031d1d771591210045fc3ac83224200a3c85590644842517908ba8c8908028fa1640191210055ac0c803224200acd820c363484015ab02186c6908022fe117558d210945e422eab1a42008fb805d563484031f100baac69080237e1d6318d210043fc2aeda1a420387c855db434840d17908bb6869080e1fa167650d210043ec2ceca1a420087f855d943484070f90abb286908023de057650d210047dc02eca1a42018f8805d9434840d17d0fb2286908030f1d76450d210354f41ec8a1a4200c3c75191434840b1e90cb8886908021fe1d645492101c3e43ac8a924239c7676dc55248425968c8b8e84908e71b1d9525092100716322a4a124239c6c76549324849fc98c6a9264908021fe1574d812101c3e42ae9b0242018f4815d360484070fd0bb8ac7a00021f6177158f400061e3aeeca1e805c8bd86dc943d00070fd0bb8ac5a00021f6177158b400051f424eca96804fa5e839d952d00014bb073b2a5a00029b60a7654b401cd3b40ceca968000a75819d952d00014df04bb2a5a00e28f61b4354b4000596c1686a968062c9e635cf42d000b87aeca9685a00178b98952d0b4030c5ec36e6a168061c9e63dcd42d000bc58c4a9285a001a2f61176ccb4002c6e41aed9968000c9d76d0f32d000b17b08bb465a004b279d1638cb4000c5f426ec99680019b8805d13
  | 6 => 0x51ec24e4b2e6206a5e839c965cc5354bb07392cb988028fe1170597310051e422e0b2e6299a5f835c165cc40d4b906b82cb989ce9da0470597310053ac08e0b2e620087e8790165cc4010fb0f202cb989ce9da0640597310053ac0c80b2e6206a5e8310165cc4014bb06202cb988021fa1c20597310043ec3840b2e6200a3e8408165cc40147b08102cb9881a97a0c20597310052ec1840b2e6273a768108165cc4014eb02102cb989bb179cf529933127d36c14eab16628ea6f825d562cc4070fd0bba2c5988021f6177458b3101c3f42ee0b16620087d85dc162cc4070fb05bb2a59893f17ccb7654b3127e3b18eeca96624fc7531dd952cc4014df04bb2a598a3a1fe097654b3100637c12eca966239a5e8399152cc40b4dd05322a5988029b60a6454b3101c3f43ac4a96624f87d8758952cc40b17908bb6859881b179cd65d0b310062eb2ae7a1662068ef8758b42cc40d99ce6b16859880e1fa157690b310043fc32eb216620087f8759642cc4010fb0eb2c859881b179cd6590b3130c5ec3cc92166206c9e7399242cc40d93ce6b248598803179957390b310062eb2ae72166206c9e7650e42cc40b17b09bb2859880a37a0f7650b310063b32ee2a16620387e855d842cc4010ff0cba885988021fe1d6510b310043ec3aca21662628bf8759042cc4c533f0ea188598802a7a13764cb31014ea40ae899662008de8799132cc4014bf0ca92659881793189524cb310045fc22eab0662128bc845d560cc4051b906baac19880e1fa1774583310043ec2ee8b066200c3d75d53644c40147d0b206c89880e1fa1f75591310043ec16eab2262008bf845d5644c4010fd0e3aac8988030f1d774591310043f43ea4b22620387c87d49644c40117f0eb20c8988028f21564191310945e422ea322626ec5d73d48644c40147d0b200c898802ad6064019131496aa18eeaa1a6200c3c75d91434c401878ea3228698803171db7550d31006aa38eeaa1a62068f581dd7624c4010ff0aba6c49880e1f21574d89310043fc2ae1b12620387c855c3624c40159b06106c498802b960420d893100477c3ac43126200a6d829d9524c40147f08bb2a4988028f211765493100537c12eca926200c74715d9524c4014f700bb2a4988e29e201765493102d37414c8a926200a6d82991524c4010ff0eb22a4988021f21d6454931005a6c1486a926239a5c8650d524c49f4ed0db8aa4988031d9db71549310043fc2aeda12620387c855db424c4051b90cb9e849880a372197390931034cfc3a872126200c9e7650e424c4051b90cb98849880267e1d4310931006caa1ae22126200c9c865d3324c401a3f0aba664988034721574cc9310068fa92e99926206c9f615d3324c40db2ec2ba6649880365c4174cc9310064eba4c999262008dd87193324c401a3ae8a96649
  | 7 => 0xd5810c363504018decb394c6a08031b1967298d4100637b2ae531a8200c6c655ca635040199ec6b94c6a081b3318d7298d410043f43ecab1a820087e87195635053d87ee832ac6a09eb0f5d06518d410046fc3ac631a825d8bc865cb43504f50fd0dbaa86a08034d1077550d414ec3f43ecaa1a827987c87d954350525878edbaa86a08034d1c77550d413ce1e3b6caa1a8200e1f6518d4350401c3ecaa1886a08029b60b75d894100536c10ebb12820087f855cf62504070f90ab9ec4a08021fe1570d894101c3e42ae1b128200aad84083625040159b06106c4a0802b960420d89410062fb2ce73128200c5c659ce62504018becab9cc4a080317195739894102e66312e73128200ccd73d8a62504010fd0fb2ac4a08021fa1c65589414e61fba0cab12821d87d87d9462504014db05b28c4a09eb0f5d0651894100536c10ca31282008ef8758862504010fd0d3b2a4a08029b60a765494100636c14eca928200a3f845d952504014df04bb2a4a08029de0576549410061f208eca928200c3c411d952504018e8823b2a4a08030f1db435494100596c1686a928239a3c8650d5250401878eca1aa4a098a2f21973d09410051e432a5a12827a87c865d64250401a6882bac84a09e61fe1f65909410043ec3ecb2128200c5f659ce42504018b8cb39c84a080317d9573909410062e32ae72128205ccc625ce4250401b2882b9c84a0803335cf62909410063a32ee2a128279c3c76d9542504f3a68e3b2a84a08038bd9462509410051e432a4a128205c3c76549425040bc58c4a9284a08e74d1c55250941014db43ee2a12822e87c865d44250425a6882ba884a08021fe1f65109410ec3ec3eca212820087f855db32504070f90abb664a08163720d76cc9410061fb2ce99928200c3c659d332504051790cba664a08030fd9574cc9410061e32ae99928200c9d74d8f32504070f90b3b464a08021fe15768c94101c3e42aed19282058ec825da32504010f90cbac64a08021fe1f658c9410043ec3ecb1928200c3f659d23250401878cb3a464a080a2f219748c9410061fb2ae91928200c3c655d2325040536902ba464a08032b5d3628c94101c3f42eec992820087d85dd932504051790cba264a080a6d205744c9412ef4631686992820387c859d832504010ff0abb064a080e1f215760c9410043e432ea192820087f87d9432504010fb0fb2864a080a2f219740c9413cf1bb26cba0a8200a748654b415046936f0ea1682a080a2f61375d814101c3f436eab02827987c86dd560504010fd0fb2ac0a08021fa1c65581410062fb2ee6b028200c5c65dcd60504018beca39ac0a080317194735814100637b2ee4b028200c6c65dc960504018deca392c0a08031b19472581410061fba4e8b2e6206a5e839d165cc5374bb073a2cb988028fa1272597310
  | 8 => 0xea38ac8990031d1d471591320063dbaee0b226400c7875dc1644c8019e6e3b82c8990033c1c770591320063da96e0b226400c7b751c1644c8018f0ea382c8990033cdc4705913200678388e0b2264008bf87590644c8c317b0fb26869918a2fa1c6450d3230dc6c14c821a64008df87590434c80133f0eb20869918ae3e096410d3202ce6412e221a6400a6d82991524c8010ff0eb22a49900e1f21d64549322e716212c8a926400a7781591524c8734e902b22a4990029ee0164549321c53c402c8a92644fc5e76dcd524c80b6990439aa49901697a1b435493202da741686a92645df0c42d0d524c80b6990421aa4991722f61f64d093202ccec3887a12644fc6e7654b424c801c5ec8a96849913f539cd52d09320078621aa5a12640087f855d9424c8070f90abb2849900a3d205765093200c7c402eca12645d8be87191424c8bb33d0e21a84990021f61e75d853201c3fc3aebb0a640087d87d4b614c9470ff0ea96c2990021fe1574d813201c3e42ae9b0264008f7815d3604c8051e902ba6c0990030fdd274594320051fc22e2b286400a3c845c5650c8014f50038aca190029e60071594320352f41882b286400a5d83105650c80147f08b82ca190028f21170594325152fc1ae0b286406a5c835c1650c8014ed02382ca190029d60470594320043f43c80b28640087d87901650c8014ed03202ca190029d60640594320043f43820b28640087d87041650c8010ff0ab8cc81900e1f21571990320045fc22eab0864128bc845d5610c80117f08baac01904a2f21175580320346e41aeab00640387e85dd1600c8010fb0bba2c0190030f1d77650f412e45ec36e4a1e820387e85dc162d04010fb0bb82c5a08028fa127654b4100536c14eca968200c74719d952d04014df04bb2a5a08e68f61b4354b4100596c1686a968200c7576dc552d040b87aeca9685a08178b98952d0b4130d4f41eeca1682618bd86dcd42d040bc58c4a9285a08163720d76ccb410064ebb68799682028be84dd932d040536902ba265a080a2f21175583410046fc1aeab0682068dc835d560d040d938e6a1ac1a0a868fa1073d95413cd1ec20e7b2a8200c5d731cf65504f34ed0239ecaa08029d60473d95415051f420e5b2a8279a3d841cb655053f47d09b86caa09e68f61370d95413cd3b40ce1b2a8200a75819c365504018f2e0386caa09e61fa1e40d95410043ec3c81b2a8279a768190365504014eb03206caa08021fa1c30d95410043ec3861b2a8200a3e840c3655040147b08186caa08029ba0830d954100536c1061b2a8279a76810c365504014eb02186caa08021fa1c20d95410043ec3841b2a8200a3e84083655040147b08106caa080297a0c20d95410052ec1841b2a8279a768108365504014eb02106caa0802a761030d8d4100566c1061b1a8200a
  | 9 => 0x6454b3227f0f98ac8a966405b4c82dcd52cc801c3ac9a1aa599016d3a0b4354b322ef8721686a966405a9c8359342cc80b33908b9e859904b2799173d0b3202d4e41ac8a166400c9d64dcd42cc801c5cc8a92859900353dcd5250b325378621aa4a166400c3f749d1658c94b4df04b9acb190031ddc671596320053d400e2b2c6400a79801c5658c89f4bd0620acb190029760c415963202d37414e0b2c64a4a6d829c1658c8018f6e1382cb1900297e0d705963227d2e41ae0b2c6400a76811c1658c8014eb02382cb190021fa1e40596320043ec3c80b2c6400a7681901658c8014eb03202cb190169ba08405963200536c1080b2c640087e87041658c8010fb0e082cb190162f21175992320961fbaea9324640087f855c6648c8070f90ab8cc91904b2d10571992320051f42c813246400a3d85902648c80156d03204c919002ad60640992320961fbaceb3246400a3f855ce648c8014790ab9cc91918b8794f53992320051fc2ae33246400a3c855c6648c825968e2b8cc919002aea0051992320055cc00a33246400a3e859c2648c80147b0b384c919002ada0670992320055ac0ce13246400a9f83542648c8c553906a84c919002ada0450992320055ac08a13246400a3e85042648c80147b0a084c9190162fa1f54592320061fbaea8b246405aae82d51648c80787ceb2a2c9190162f21d54592320054ec1882b246400a3e85901648c80147b0b202c919002ada0640592320055ac0c80b246400c3f759d5648c80b55d053aac919002ab60a75592320051fc2ae6b246400a3c855cd648c80156f02b9ac919002ad20573592320055dc02e6b246400ab8805cd648c8c3c3ca7a9ac919016aba0b535923200556c16a6b246400a3f855c5648c8014790ab8ac919016ab209715923230d4f418e2b246400a9d831c5648c80196ae238ac919016aba08515923200556c10a2b246400aba80145648c8015730028ac9190028fa1670592320051ec2ce0b246405aae829c1648c80155b05382c919002ada0670592320055ac0ce0b246405aae82141648c80155b04282c919002ada0450592320055ac08a0b246400a3e85041648c80147b0a082c919016aba08105923200556c1020b246405c6e72597438c8018dacab96871904b2b99172d0e320043ec36eaa1c640087c87595438c80187eeb32287190030f1d66450e320061fbaac8a1c6400c3c75591438c80195ac9b92871900e1fa1774582320043ec2ee8b0464058dd83dd7644c80b8bae7a96c8990021fe15739913201c3e42ae7322640087f855c6644c8070f90ab8cc8990023de0575591320147a40aeab2264008fb805d5644c8031f100baac8990021fa1f525913201c3e43ea4b22646ec7471d49644c89d8f0e1a92c8990031ddd771591320063a3aee2b226400c7752dc5644c8018ee
  | 10 => 0xa18845cc3f52dd943108b987aa5bb286210030fddb7550c42096572a6eca108400cad54dd942108011bf06baac02101a3720d75580420364e39a86b0084068bc845d664cc8010ff0ab8cc99900e1f21571993320051f42c813266400a3d8590264cc80156d03204c999002ad60640993320961fbaceb326645da3d82d4a64cc80147f0ab8cc9990028f21571993320055d400a33266400ab98014664cc80147d0b384c9990028f61670993320055b40ce13266400ab5819c264cc80156d02284c999002ad60450993320051f428213266400a3d8504264cc8070fd0fbaac99924b171cf75593324961ec26eab2664058dc835d564cc9250fd0e3aac999277171cc75593320345f43ea8b266400c3f75d5164cc80d53d07aa2c99900f0f1d654593320345e43aa8b266400c3f7515164cc8010fd0fa92c999017171cf52593320354f41c82b266406a9e8310564cc80147d0b202c9990028f61640593320055b40c80b266400ab58190164cc925c38e7baac9990028f60b75593324970f98eeab26649da3e859d564cc80187eeb3aac99901aa7a0e75593320054ec1ceab266400a9f835d564cc80d53906baac99924a8fa1c75593320061f438eab26649de1c731d564cc80147b043aac99927787cc475593322e64e39ee4b266400a3f855c964cc8014790ab92c999173271cd72593320055bc0ae4b266400ab4815c964cc80157700b92c999002ae20172593320354f41ea4b266400a9d83d4964cc80147d0fa92c9990028f21f52593324770f41ea4b266400e1d83d4964cc8b9c38e7a92c9991728f60b52593324770f98ea4b266406a9c83dc564cc80147d0b38ac9990028f61671593320354f41ce2b266400a9d839c564cc8015750138ac999002ae60271593320051fc2ae2b266400a3c855c564cc80d53906b8ac99901aa7a0c71593320054ec18e2b266406a9e8394564cc80153b0728ac99901aa7a0c51593320054ec18a2b266400aba8014564cc8015730028ac99901aa7a0e21593320054ec1c42b266400a3e859c164cc80147b0b382c99901aa7a0e70593320054ec1ce0b266400ab6819c164cc80156b03382c9990028fe1570593320051e42ae0b266406a9c835c164cc80d53d06282c999002a760c50593320055b408a0b266400ab58114164cc80d53d07882c999002a760f10593320051f42820b266400a3d8504164cc80d53d06082c999002a760c10593320354ec22eda1e6406a9f8759343cc80d93f0eb26879900387e1564d0f320070e42ac9a1e6400e1f5259343cc80193ac8b8e87991778ba0a6454b3200716c14c8a96645dc3f7299152cc801c5ee5322a5991778b8ca6454b3227f16994c8a96642e87c8759152cc80b4b906b22a5990030fe1d6454b320061e43ac8a96645ce1c8359152cc8b987ee4b22a5990038bdc9
  | 11 => 0x908015b30028cc72101a37a1c4198e420054fc22a131c8400a9c8454263908015ad02284c721002b56045098e420052f42c8131c8400a5d8590263908015ad03204c721002b56064098e420052f4282131c8400a5d8504263908018beeba9ac721016b3a0b5358e4201e2f3aca6b1c84058dc8754d63908070fd0bb8ac7210021f6177158e420054ec2062b1c8400a5e850c163908014bb0a182c721002a76103058e4202d6741060b1c8400ad6810c163908015ab02182c72100317dd67558e4202d67414eab1c8400acd829d563908014bf0aba2c721002972157458e420056bc0ae8b1c8400ad4815d163908015b700ba2c721002b62017458e4202d67416a8b1c8400acd82d516390801c3ea92a2c72100297a177158e420052ec2ee2b1c8400a9e841c5639080153b0838ac721016b3a085158e4200566c10a2b1c8400ada8014563908015b30028ac7210023761c4158e420052f428e0b1c8400a5d851c1639080153d08382c721002a76107058e4202d67410e0b1c8400acd821c163908015ad02382c721002b56047058e4202d67410a0b1c8400acd8214163908015ad02282c721002b56045058e420052f42c80b1c8400a5d85901639080b59d05202c721002b360a4058e420056b40c80b1c8400ad58190163908014bd0a082c721002976141058e4202d6741020b1c8400acd82041639080b8dce4b2c87210031b5957290e420366731ae521c840087d86dd543909258bcc7baa87212761f21d6550e420062fbaac6a1c8400c5c7558d439080199ac7b92872124b0fddb7550e424970f31eeaa1c8400d2f75dc94390801b1ee7b9287210170f5d352d8d420043fc2ae3b1a840387c855c763508011bf0eb18c6a11876310d7290d420064f3b28621a845dc9e839d843508bb87ea53b086a117727cca7610d42004cfc3ac621a8400c9e7658c435080171f04b1886a12ab0f9db74549422ef16216c6a928405a3e8690d525080b65d0521aa4a11768fa18435494202d9641086a928405d2e7454b425080bc5ec8a9684a104a8fa12735944254d1ec24e6b288400c5f739cd651095147f08b8aca2104a8f21171594420053d400e2b288400a79801c5651082547d0818aca210028f610315944253d1fc22e0b288412a3c845c165108014bf06b82ca210029720d70594420053b408e0b288400a75811c1651085d0fd0f202ca210021f61e40594420053b40c80b288400a758190165108010fd0e182ca210021f61c30594420951f42060b288400a3d840c1651080b4dd04182ca210029b60830594420053b40860b288400a75810c165108010fd0e082ca210021f61c105944201c3f42ee2b18840087d85dc563108070f90bbb286211021f61b7550c420043f43acaa18842e87c875954310801878ebbb286210030fe177650c420061e42eec
  | 12 => 0x31d18474585520071a308e8b0aa400c3f621d16154801a5ec43a2c2a90030f98474585520061e308e8b0aa400d34611d16154801868c23a2c2a90034dc4074585520063a30ee6b0aa400d2f74dc96154801a58e9b92c2a92c39918772585521cd3b436c2b0aa400d3474d85615495facee5b0ac2a90165ba0a74d8152194b6c14e9b02a400977815d360548732e902ba6c0a90e21f61c64d81520061eba0c9b02a438a7a8019360548710fb0fb1ec0a913f179cf63d81521c53d406c7b02a43887d87d8760548738ece3b0ec0a90e29ea0361d81520043fc3ac3b02a400a3c8458760548738e8e2b0ec0a90030f61b74581520061fb16e8b02a400d2f62dd1605480187ec43a2c0a90034bd8874581520061fba4c8b02a400c7471991605480187ee8322c0a90031d1c4645815227caf43ee6b02a400d1f74dcd6054801a38e9b9ac0a900317d8b7358152006a7b16e6b02a400d1f741cd6054801a38e839ac0a913f1761873581520062f320e6b02a400c5c641cd605491d8bec439ac0a900353d88735815227e2e39ec6b02a400c7471d8d60548710f90eb1ac0a913f171cd63581520063a38ac6b02a438a788058d6054801a5ee9b92c0a90034b1d37258152006a7b9ee4b02a400d4c73dc960548732ed0fb8ac0a90034ddd371581520069a3a6e2b02a400d5773dc56054801aa8e7b8ac0a900359dcb71581520063bb16e2b02a400d6762dc560548018eeec38ac0a90034ddd071581520069a3a0e2b02a400d57731c56054801aa8e638ac0a900359dc871581520043f43ec2b02a439c7471d856054801ce421b0ac0a90e21f21d61581520051e422c2b02a439c7471585605495dad6e5b02c0a900f171d65358f420946e43aa6b1e840087e87d4963d080b878e9a92c7a1002976143058f420954f42060b1e8400acd820c163d08015ab02182c7a108a1f21d6354b4202d9741486a968405a3d8610d52d080b65d0421aa5a100e1fa1f75587420043f438eab0e840087e87d4961d09470f90ea92c3a12aa9be0974596420053bc0ae8b2c8400a74815d1659095b47d0939acb210028f61273596420062fb9ce6b2c8400a76819cd65908014eb0339acb210031ddc671596420051fc22e2b2c84aca3c845c565908014f50038acb210029e60071596420052f41882b2c8400a5d83105659080147d0818acb210028f61031596420063db84e0b2c8400a3f845c1659095747908b82cb210029da0470596420053ac08e0b2c840087e8790165908014ed03202cb210029d60640596420043f43860b2c840087d870c1659080147d08182cb210028f610305964202d3741060b2c8400a6d820c165908014ed02182cb210029d60430596420043f43820b2c840087d870416590801c3ea92a4c721002a7e115198e420054e422a331c8400ada8014663
  | 13 => 0x63c32ee0b12864087d87d946250c014db05b28c4a18029b608651894300477c3ac4312860087e87d956150c010fd0e32ac2a180e1fa1b75581434943e436eab02860087e87d956050c010fd0e32ac0a1803171d77650c430964f2a6eca188600c9d54dd94310c018bea5bb2862180317ddb7550c4301c3f42ee2b10860087d85dc56210c25d2e82a1ac22181a3da1f51584430346e41aeab00862b96f825cf645480147b0d20ec8a9002c760c41d915200596c1083b22a400a3d86903645480166d03206c8a9002cb60840d91525be96b96c9322a400a3d87d92645480187b0fb24c8a92df0f5cb649915200717b22e5322a400a3d8498664548018eae330cc8a90029e600619915244697ba6e4b22a43997687dc56454801acee5b8ac8a90031dd8b7159152006b3b16e2b22a400c77761c56454801a6ee838ac8a900359dc871591525b596c14c8322a40087f8759064548014e902b20c8a90024fe1d64191525ad97c12c8322a400b348159064548018eae2308c8a90029e60061191520058ec1882322a400b2d821046454801c68c2208c8a90028f61a40191520059b40c80322a400b2d82100645485f2df04ba6c6a913e1f61c61d8d5227d2f418c3b1aa400c757118763548014f30030ec6a90029761a30d8d520052ec3061b1aa400b4d820c3635491d87ec53a4c6a90034bd8a7498d524761fb12e931aa400d2f625d2635480187ae9324c6a90029760e6498d520063b38cc931aa400c3d7419263548018ece2324c6a92d3535cb6398d5227d2ec3ec731aa400c5d87d8e635489fc3ce9b1cc6a913f875d36398d525a62eb96c731aa44fe4d72d8e635489fcace3b1cc6a913f955c76398d524763bb12e331aa400d67625c66354967a9ee7b92c6a90031ddc66158d520053cc00c2b1aa43296d829d0635480187ae8320c6a90029760c6418d52004afc3ac631aa4b2b4f8258c63548012db05bb686a90025be0976d0d52004bbc0aeda1aa439974815db435489f27b0e32686a91774b10972d0d5202cb7c3ae5a1aa40396e865cb43548072d90cb9686a91774be1172d0d5200697b22e5a1aa400d2c645cb4354963a5c86b9686a92c74b10d72d0d520043fc32e3a1aa40087c865c7435480b2d9053b486a90025be097690d5201cb7432e521aa40396c865ca4354801a9e86b9486a913f5310d7290d5227ea798ae521aa40096d82dd9435480187b09bb286a90031b60b7650d520043f434eca1aa40096f825d943548012ef02bb286a90e65d2057650d52004bdc02eca1aa438978805d9435489f27d0fb2286a90030fddb6450d5227d8f41ec8a1aa400c3f7619143548b9a5c85b9286a90025be097610d52004afc3a8621aa40596e829d361548652db053a6c2a90029d61a10d85520071a30ee8b0aa400c3f62dd16154801a5ec5ba2c2a9
  | 14 => 0x1200000000400000800400e00201a00000000600600000800000000200200000200000400000000200000400001400600200600600000000200200400601400000000800001000000000200000000e00400200000202a00000400000a03400000200200000000200400000200001000e00600000200400400200000000200200000401a00a00c00a00201a00000000000000000400000400400c00000400400000400000a00200200000000200200a00400400000400001200000400000c00200a00400a00000001201000200000a00002600000000200600402800800000000a00001000200400400600001e00000800000000000000000200200000000201601600000200000c00200600200000000003400600000201401800600201600000400200400400600000001200200000800200000000000200600000800200600400800600000000000600601c00e00000000800600200800000200000200400400000000800c00000400000600400a00200000e00000200400000000400000000400800800000000000000200c00200600200400000000600600000000400800800600001a00400200000401800000000800000200000800600000600600a000004000000004000000000000002000002000000000008f7815d562d0c051e902baac5a184a3b21d5258b4301c3f43eeab0e860087d82dd561d0c010fd0e3aac3a18021fa1f525874301c3e43ea4b0e86068ec875496290c070fd0bb8ac5218021f6177158a4300536c2842b148600aad840856290c0d59d0610ac521802ba6002158a430053d404c3b2a8600a79809876550c014ed03306caa18029d60660d95434851f426e7b2a8684a3e84dcb6550d2547b09b96caa18031b5c872d95430053d404e3b2a8600a79809c76550cfb47d0838ecaa1a4a8f61071d95434952f418e3b2a8600a5d831c76550c018eae238ecaa1a4a97a0c41d95430043f43843b2a860087d870876550c0147d0810ecaa18028f61021d95434952f41843b2a8600a5d830876550c014f50010ecaa18029e60021d95430053b40ce1b2a8600a75819c36550cd547d08386caa1a4a8f61070d95430063cb80e1b2a860087d879036550c014ed03206caa18029d60640d95430043f43841b2a860087d870836550c0147d08106caa18028f61020d95434952f41841b2a8600a5d830836550c014ed02106caa18029d60420d95430043f43821b2a860087d870436550d25c3ec9b2e86a184b65d0571d0d434ee1eba0cbb128600a6d82dd76250c014db043aec4a18021fe1571d894301c3e42ae3b12860087f855c36250c070f90ab86c4a18021fa1f65589430063a38ecab128600c7870d956250c010fd0e32ac4a18031d1c465589430063c380cab128600c7765dc56250c018e8cbb8ac4a18031ed97705894300
  | 15 => 0x391418000248001ba935187c000001159ac0000001aadce5128be40000000ac001a5400000000118d304755d293ac000059d488ec0d43080005d8000000228b51804140001834d04000000001ae4001d64000000078000574000001ac4000000000000000c180b000177c000000000000264000000000c68000000000bd4d8c000b0501c1080018c5c9c001ca4c8c0000000000004fde9d7356c9a64a5c695e040000000001600011400000002d80000000016982e0000000000dd04d491c000d0c2a80f54ac000000000001d7c0004f80000000000000000000000000002403cdbbce14ff17c10d5c55630000001088f28000000000000d018905f000037c0000011bc000000594000000000001c85e5c001a5c000000001371c308c00000000000018781f569d560434af80014f81a09e8000000001b80001220cb8000b4c0010b40000002818700000000000000018f971d3400011b08b4a80000284bdc00129c570784b38b89e4035d195ead2e18b16383e0000944000001954000b7c0007c8e604298b8000d44be9414001ec50bc000000000000001b680000000000000000015acf08b64838c7c000000000000000f680000008f0a3c5580c9724001bb1e641848f97444e40000004dc0000011b4000000000e4800000000001200200a00a00000000000000000400000400e00a00200000000200000400a01400600400200800000000003200800200000a00000000200400e00200400000200e00000400200200800201400000200200000200000600000000000000001a00000000200200600200000200c00600200000000a00200600000000000000c00200201000000a00200000001600200000800200600000400200600000000000000400401e00600001000200002400000200400c01400000403800402801800600800001600c00000000200000600200e00000000200002c00600400200600200000204800600400001600000600602c00200200000c00400000000000800200000000000000000003800000200200000800200800400200000c01c00002800000600800200002800000400a00a00200a00000000600a01000200000e00000000000200200c00000000000002400800400001400600600000800200001000000200800001000001200000200200801e00400000400200a00a00000000a00200200000000000001a00600a00200600200000800800200e00800200400a00001e00200600a01400000000200400000600800a00000200c00200200401400000800000000200800000000002200400000001200e00c00000601400400000000800000000000600000000400603800000000000001200c00a00000200800000800a01400400000200000600e00000000000600600401600400600200c00
  | 16 => 0xad4080000000000000000013f1f6465c000000000000000000001a780000000000000000000005500000000009ec001474000000000bc9298000001360000001a7c2c0000000000000001c39ef4000000028001b10c640017e1a240018edcd5c5c15c000000168d48d7d6d40000010f8000000329a400006d400000098000000093c00115400090c0000006280000000000001b0000000000000000000001d30001788f74f10000000000c38000aa00000000000010b925c0009f07517c80012a90381d8000000d800015980002500012d1d6068c70d5f1df0001099711605e30dac505378000000000001e35ddc001144001d40000addd08200e1db640000000000000000000004b8000000000a54001590091ea19640a85b8000000e34000000710000000000001291859dec00107cf51ad4000000fd12e4b9400188cc2db6c000000e04c54700000221928000000000b0c001c1c000f78001e955cc000000cd917dc94000f80c20000000000724e39f5cc5c000000000000000000d3c001d257a02d4ec00a5b8c00186c06d2d840000173d38c104a50ba5a040000000000000000000000001dc07c5cc0006dc00082066ceb93a1bedab8000000001db0000d70000001808000000000000d115a00001ec0002edab49acccc0000008e00001ccedc38c0b5864000000000ec40007880000000004edbd4000001e10000000000001e0db18c48c88001e489d004459c3b9035cc5e91095641a0c3f45e5ed00387ad8c00000019a5660aa5394000001b9400179412d4fd8e800107000000000005c8a0a648a4000000000001609d396d1d789a47052bdf6dde4520001e750112a05c8cad30801cae800159430400000155c0007e4001bfc0000000019e17c446c000000000000d206d8000958a7c00000000000048c0000005102c449d209f4d714000d75dad888498000000de0bcd18131c0010f5e713e40855191683f9b39461b7594889594cab42e414c0000000018853f4000000000604d1800064c02d22c0004387384895814e1508001d58a4ce88728971f7897c00072d2a4fed898000fd8cd10d1f70000e64000000000aed5680000014f0000000000000000000fb0f54000120001700000000000000000238001440000000000000000000000000000dec0008540015d0021b70000000000000000000f9c00000149c001df4300000001740000001f300000009907781557612c4afdef119c000000868000c14a0d4d0001a700256680000000015a8810001ee80000019940000000006a4001850c9482800106c0016002b4000a1c7180010300000000000013dda8c000000000000001e78000d1c0016b4f6c000661dbdb051a84d83d01c4001494000dc14380001440014cc000001a2c6c84500016e0358001a740018f54a59bc000000001b31464
  | 17 => 0x80000003b4000c100000000000016940000000016240017d9e50000000000d340000000002ddd106bc0113e09b0a6dbe4000b195c1944128e71c75d9da21ac8fdc6e4c4584c00061c0000340000014019a0000b24000d4d9d4e6c0000000000c00005840008e4000000001104001914001281848fc88500000004a40015500000000013a4000000000000000000e28001654000000000000a10fe00017d5b9130c0000000000000014480010e0000fe858c51c001e140000008c80009614884a806130004c000c58cd5c18b1dbc000000035526dc4000000000029800042c0010a833095000132c000388a9800000033c2d1358000000000001244000000000001505ca055cfb428844c000001541cb00013353d8b40eac790860a2cff547011de6c79dc985a041135c7bc800ac965150c000000abc2a11612fc4adb20e451f94b161552c001a8508da9c424088001dc0484001eb0580a48260600cdd284688000fbcf60000001935218001b2cd2da584cc001718188528001a488dda81ba0001a3c000000000000000000000001bad7b8000000000000000001bd80000000000017815212ecea5a900000017d0b34001d34001d4c611748000000af520d99c8fc0000004480001a50e903dc05e2c000a443c5b9c0013c4ef47754e4cbc66909029400000093852c0003d9491515d44bd86cde88bbd681b5daec27905c000000000000000000bf8001a60000000000000000000000a74000000f24000001528000000000000000000000ab8001498098405679311a11ec9a6cf994c1784a9d4a9c65ccc3788e9bf83f18f112c004cc45f82f533ced94bd9300d06c55708647216f062ced1ec07c0e0010000069c9a00000000545480007dc0019d0000001381acc0011f0cc00000000000000000000008842bc001150149afd7dd015bf0c3c000000000ad40004c9078000000b700000300001e524c000000000000000001ee40013d0001c2c0007997f00d96fd4300810410b1f209881fc000000000040a24c4cdd5dd88700019609fce991d92f8bb57b4c1c3c9044e740000000000000013bc000f203a4000ac0000001004001ecd6c074c00000000085cea89554b80000004d14d827400110941003cdf06e8000e940000000000000017551900000000008cd17940df8000142df340001253cc210001b44000000898e51c6800000165de45975234615d218dcf00c411c4dfcddc051de80016209e07640000015d4c801b9a0146c0000011d00007b4b1591800021800000123db4d3ec6ac0017fd958678000540f0400000027cca853000196c00000000117180009dda111400000000109de18ce15380004645544c0908001e38000bb992c6d1d54ae4018364000c348404b12dc159aa0000001424000000000000000000409ae1f1000039c000000000f
  | 18 => 0xd41674001f7c00000000c000000000000001174234174740000000494000000000000000d28001cc0000674c6c150da9548001df96f4000b017f4000e58964000001b98000000000000001c3c3246809851380000000000000005f40000000000000009f8000a14000001bf4c040a0545b342c8000000598421c2000031cd251dcc09c48000000000000001c24994001118000534564000638f440000000018ad62d02d34c001751f2c000000000000000138a69988940df9385d6c0c59fc0018d9b4183c13d00092c000a7000000139dc5964d3d57781f8ca00007cd478915b89b48920924231364b9dc0155800000036cd087495d80015e4fa5f853e88b8888418115051e800f9759abcd5c315610001064000001d685e84608d96a40002f07d0000000538000000001a69a50000000000dc8f0c001cd07f0a9000000000090000182c000000001bb81c0000000e80000000000399d3c0000000000000000008f4008768b9910d3b0bfc0006f4a393481800014ecc74000000001798001cb59717057e8000000e211ec000000000000000000000000001bcc00000094c00181190da4d5b9f54071f4053ccc9d800000004755bc0006213c02046fdce8670d582fdb00000000001b0c001cf04bc0001780000009cca052293b80010f02cc0010fcd61adc000e094b591d70d730e112057903d40000000000001700016ad83993800000074418c00000000000022c4a0000000001d1d97d484ae01d00017ec000f700008786b057854c0000000000000013c83ec99c001cfccecf2c00000000000000000167d3b4000000931c80000290001f69124001d8400000045c000000001874000000f150a55c4000560468a61ce0000c78001d0dc8c0011b8d78b60fc521d1c9ae90ecfa15c81a80140000011ac00000000000178c0756d8dbc0014a08315dc0000014517a92b5de0000000001d2c0dc001cdd12000026dd14000f3c385075dccf34000f7d275e99404000000db0000001a88ee8731480ca5924c288352698192c000020c000e68ef80000000000000000019200000000000005ec000000d5434c808000000bf419c0006184b40e896dd00000000fa927c37137cc0c0015780cc338000b0884c0f00006f800000179c0e0f940019846452490099b0bec0012947710480006587a8ee0000001728f8400000000000000000156c0012100000000016355b0a3044174d684d14000000000fb80012e8000001cf9a140000018e46e0631e4c001da42589b4000000890b44000b3c969910001aa4001b1c5ad9e80000002b0000648479a08998000000da11a4000000001188000dd9904000000000001391cd80003e98cc000000000000000001110001a9515dea5c7998cd9181c064eec00000000000071c000000000000d8878da38001a1800000000019
  | 19 => 0xce9e00001af8000001ab1a28001101355be14dc6b9c6c608641f04a78000000000db8480001e0902440c3fc0000007a0270ffc000000a84904000001eb400185d68800000000000157400127800145800000000000000000000000000025400114d0d800081c000000000000bc00017655e0000c30000000000000000000000000000001e7c0000000007b00009d5990001b78001e280018d5dd4000f380000014e9814000000e4c6a07595f80000000000000000000000000003a0000b8ddfc0017a430cb29efc0000000006540000013fc0000000000000001359ac0015b4000000a880000000005902089ddb593f86847b95000016708180014c5ca80001c95fd434000ad8000cb0cf00017ad6ec87c858000000b797cc001cf40018a40003409a880d0580bcef017dd75f28001a311fd6652ac5e0001ed41bc92824cc84e54d65f18781c902a4e258559b953000141c41ceb01187a450936c000f8dbe8df40000000016a0000501ad0000001d8cf318447ece900011d40008440940007e8874001e54000001c14000a080018bc0000000ed564000000e9c000001ea8000000000f480000000000000019e5880001af40014f41e80000000000002b9895968a94ab00000e4394000d6c43c001260001eec00000000158c00000148c1653200010c8000ec8000000ba0a59868dcc000da43b076d7759ed7f955500ccb4f58000f18191821388a20b540012f09bd5ec000001ef9770f640000005c166c0000000000000008252380000000000000000006c0000001c45d88000000db4000c240000010acbd10c5e8c3a8000000000001691a350dc0000009d8000000000d940000000000018d113c7358a000163c000000001af00005d4000000000000708000000b59900000001978f913284f0b6d4445b16dc001720918000000001f740012240004e9658f400017b0a415100003dc00000101976cad0048000e5d2b0000000e7c3351a04f48c41b48bda1c6248ad5f5544e78e18000000001429a980009485bc000001b29e60b1143d2cc0019f583088c001ba4001941b7c000aa80000011640019f05149c57e4ce4e84000001d045a86640000001ac0018a8000ea000037504df591e0001d90000b30001db80010680000005d0000000d840000000000000004c5e3d0e40005dd0a1c080015e80b9339c60fe5bd00000005fc000dc5318efc000000cf400057c000000001f3d259081dc9130001f08001860b2c5b51e40014680019c067c0011842e89f4000000001ad8000000760f4cb74001e699cc8d0000000000c611c120189d7bc0016bc60c0000fd68c86c23c71400153545c814001f252b80019504556e957d9dcc903c12f554deb85a55a4c9df8800000125000000184082c000000001b54000000000000f5c001e1d8fc6356b0
  | 20 => 0x1e2400000041400000000180c974445d94e0d8c8de40000007d4e3d6b8849829029ebc10d2d53a9c50000000458001e84001cac000000000bb0000490000000cf80001959f928d9c43e400000000063c47c000000269d5c00000000000116c000000b48000001f600000019a800000000172dd5000075c000000000001908001b15cbdc4c6900000000011988a976800065032c00000008d420000001edc000001db4001d7159d649c7c6b593c0000000000016295840000000000000000000000000000018b495c6ed53c13161c000000000000ba92554d5bb511c21c349618000000aac000fcc001c28ac4000000001c349340000007f5f480000001f01e00011e8000000000d9d7380005240000000000000003680000000012647fc001f0073d6c4de9b3d589c70350ff8badb84320e300018e10cc000000000000978000805ee077cf88000cfc381240b80000000ecd75d345060001148000000318000360000000000000000568001aa8000001230000000000000001020af19d8ed5134c50a3400195c0000008d5b240016e55240007e1b60acde207d93140000000000006980000012700010c1dd160c4e0d9825c0000000000016440000000000001d4000000000001c100005c40000002146a9ceca8d6cc0000013987c4000001bc8001bc4001cb89b9f38d68000f1d215ed8000b5c4700006f0310b6858843147c244000001da80000013680000019812c8000000e40e8dd98911288c70ebd0542f9cc99b4bf0001c0df1551c001b089c03bd82450c0000000000007f8fd5dc4000000fc0000000001998344001f1c89d3759c8519c88224000a00be0000000001d19325f45331e58000001f516a80000002ac000000c00bc4d500014c80000016f829ceb4d397083ad1cc56cee4000000000000000000000880001a4400083cc98e2c068000b9098d44c000000000000b851f40008b0111b50000000a187949c8000b20000001f0c001bdc0009e4d3000000000145400000016d08428ca280000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xd54a108d998b5800005240000026d040a001d22a5a791003001c001c94032000001434003001a00f950274000040003100300006e010304ebd183124000000000000001311505cb2b320001c000001b00007800001700000a0830008041010e0c01100000050200018717160061191520068560c611046454801a258218441191520058c6406110464548018717160061d8d520041de5d8684361548014369718774585520058c64061dd161548014719018474585520050da5c611d161548016319018474585520050e640611d161548015319018474585520070ca40611d161548014359018474585520070c640611d161548014319018474585520051c64061dcd6154801434915d064d81520060d1c4845876054801870801c563581520061ca1e10d856054801834712116158152006239db8258c435080142d922177650c422e50b65f6454b424c801836841c67654b410051c640719d952d0401077985db7154b410050764c411d9525040142d9210476549410060d1c486549425040144d929957390b310060d210715d9524c401471901c576549310061c200715d9524c401075989db715493100607218855d3324c40142d921d46450d210041de61711c565c8001434945c471597200061c5c5801c565c800142d921d46450d200050b648655d0624400144d9219573189100051564c411d952440018718160076549100041d660101d952440018347621171549101ce1c219715c15244001530945c5705491000513648655ce424400142d92195748c9100061c1c08654931440011719521d31481100067021d324c520440016c0964c93148110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x84006a200001908c1b2030882322a400c8860990184411915200606108c80e2bb2a498802830a45c5801c565c800181843128b8ae0a92200081c6a470219524c510
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x6
  | 4 => 0x94e
  | 5 => 0x3
  | 6 => 0x4
  | 7 => 0x98a
  | 8 => 0x98e
  | 9 => 0x150a
  | 10 => 0x150e
  | 11 => 0x9ca
  | 12 => 0x9ce
  | 13 => 0x168a
  | 14 => 0x168e
  | 15 => 0xa0a
  | 16 => 0xa0e
  | 17 => 0x180a
  | 18 => 0x5
  | 19 => 0x180e
  | 20 => 0xb09
  | 21 => 0xb0e
  | 22 => 0x1549
  | 23 => 0x154e
  | 24 => 0xb49
  | 25 => 0xb4e
  | 26 => 0x16c9
  | 27 => 0x16ce
  | 28 => 0xb89
  | 29 => 0xb8e
  | 30 => 0x1849
  | 31 => 0x184e
  | 32 => 0x3c9
  | 33 => 0x3ca
  | 34 => 0x3ce
  | 35 => 0xcc9
  | 36 => 0xcca
  | 37 => 0xcce
  | 38 => 0x15c9
  | 39 => 0x15ca
  | 40 => 0x15ce
  | 41 => 0x1709
  | 42 => 0x170a
  | 43 => 0x170e
  | 44 => 0x409
  | 45 => 0x40a
  | 46 => 0x40e
  | 47 => 0x188e
  | 48 => 0xd09
  | 49 => 0xd0a
  | 50 => 0xd0e
  | 51 => 0x1609
  | 52 => 0x160a
  | 53 => 0x160e
  | 54 => 0x1889
  | 55 => 0x188a
  | 56 => 0xd49
  | 57 => 0xd4a
  | 58 => 0x589
  | 59 => 0x58a
  | 60 => 0x58e
  | 61 => 0x18ce
  | 62 => 0xe89
  | 63 => 0xe8a
  | 64 => 0xe8e
  | 65 => 0x1789
  | 66 => 0x178a
  | 67 => 0x178e
  | 68 => 0x18c9
  | 69 => 0x18ca
  | 70 => 0x98956
  | 71 => 0x94996
  | 72 => 0xb0956
  | 73 => 0x94b16
  | 74 => 0xb4956
  | 75 => 0x94b56
  | 76 => 0x184956
  | 77 => 0x95856
  | 78 => 0x1a09
  | 79 => 0xd4c
  | 80 => 0x1409
  | 81 => 0x128a
  | 82 => 0x1449
  | 83 => 0x12ca
  | 84 => 0x289
  | 85 => 0x10a
  | 86 => 0x1489
  | 87 => 0x130a
  | 88 => 0x14c9
  | 89 => 0x134a
  | 90 => 0x2c9
  | 91 => 0xcc996
  | 92 => 0xe8b
  | 93 => 0x18cb
  | 94 => 0xcc9d6
  | 95 => 0x1709d6
  | 96 => 0xcd696
  | 97 => 0xd0c
  | 98 => 0x188c
  | 99 => 0x180a16
  | 100 => 0xd0a16
  | 101 => 0x188a16
  | 102 => 0xe8a16
  | 103 => 0x18ca16
  | 104 => 0xd1816
  | 105 => 0x189816
  | 106 => 0xe9816
  | 107 => 0x18d816
  | 108 => 0xccb56
  | 109 => 0x170b56
  | 110 => 0x1a0a
  | 111 => 0xe8b56
  | 112 => 0x178b56
  | 113 => 0xcd6d6
  | 114 => 0xe96d6
  | 115 => 0xeca
  | 116 => 0x184b96
  | 117 => 0xd0b96
  | 118 => 0x188b96
  | 119 => 0xe8b96
  | 120 => 0x18cb96
  | 121 => 0x194a
  | 122 => 0x74a
  | 123 => 0xd1856
  | 124 => 0x189856
  | 125 => 0xe9856
  | 126 => 0x18d856
  | 127 => 0x58cd6
  | 128 => 0xcd8d6
  | 129 => 0x18ccd6
  | 130 => 0x18d716
  | 131 => 0xd0416
  | 132 => 0xe8416
  | 133 => 0x188d16
  | 134 => 0x58d16
  | 135 => 0x178d16
  | 136 => 0x189616
  | 137 => 0xe9616
  | 138 => 0x59896
  | 139 => 0x179896
  | 140 => 0x128e
  | 141 => 0x140e
  | 142 => 0x1a0c
  | 143 => 0xe8591
  | 144 => 0xe8596
  | 145 => 0x18ce96
  | 146 => 0x194c
  | 147 => 0x18d796
  | 148 => 0x95296
  | 149 => 0x95416
  | 150 => 0x14a
  | 151 => 0x2d551
  | 152 => 0x150cd6
  | 153 => 0x16d2d6
  | 154 => 0x16ccd6
  | 155 => 0x16ce96
  | 156 => 0x75612
  | 157 => 0x74c
  | 158 => 0x75792
  | 159 => 0xb8116
  | 160 => 0xb9896
  | 161 => 0xb98d6
  | 162 => 0x3d2d6
  | 163 => 0x20e
  | 164 => 0x15c996
  | 165 => 0x15d716
  | 166 => 0xd4d14
  | 167 => 0x41316
  | 168 => 0x41496
  | 169 => 0x40e96
  | 170 => 0x161896
  | 171 => 0x160116
  | 172 => 0x160296
  | 173 => 0x1618d6
  | 174 => 0x151296
  | 175 => 0x155416
  | 176 => 0x1a0d52
  | 177 => 0xd0d54
  | 178 => 0x3d716
  | 179 => 0x1715d6
  | 180 => 0x15ccd6
  | 181 => 0x41896
  | 182 => 0x40d16
  | 183 => 0x160d16
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2203
  | 6 => 5834
  | 5 => 2019
  | 4 => 57
  | 3 => 6
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
  | 7 => packedAt gbK7 (91053+((h/734+packedAt gbK7 (81511+(h % 734)*13) 13) % 4254)*13) 13
  | 6 => packedAt gbK6 (305304+((h/1944+packedAt gbK6 (280032+(h % 1944)*13) 13) % 7701)*14) 14
  | 5 => packedAt gbK5 (127197+((h/673+packedAt gbK5 (119121+(h % 673)*12) 12) % 3546)*12) 12
  | 4 => packedAt gbK4 (4123+((h/19+packedAt gbK4 (3990+(h % 19)*7) 7) % 99)*7) 7
  | 3 => packedAt gbK3 (492+((h/2+packedAt gbK3 (486+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1fc1e03fff07ff83ffffe01fc163b1cc39f3f3
  | 1 => 0xe07e003e0ff87ffc3e01ffe006bc5e72267d9c
  | 2 => 0xffffffc00fff83ffc001fffff8c0607fc78e1f
  | 3 => 0x7ffffff00003fffffe00003f007f83f80fe0
  | 4 => 0x7ffffffffffc00000000003fff8003fff000
  | 5 => 0xff80000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x480400a1300c48062a5204a802190c408b0b1
  | 1 => 0x244a0216854869a4340d4ac0822c1652225594
  | 2 => 0x5914ac400895024a8010951518c06028c50a0a
  | 3 => 0x86736a5a0402373195801812f006b03700f40
  | 4 => 0x1079db39cee630201060060637d68003bfe000
  | 5 => 0x9e001c0100844042218118183dfb7dfc000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeeeee0fae8eae0feeeeee0fae8eae0feeeeee0fae8eae0feeeeee0fae8eae0feeeeee0fae8eae0feeeeee0fae8eae0feeeeee0fae8eae0feeeeee0fae8eae0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37199
namespace PEqualNP.Outside.L_meta_37199
open PEqualNP.Outside.L_meta_37199.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 26 := bs1_3_0
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
theorem bs1_4_128 : Interval s1Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 134 := (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 (concat bs1_4_96 bs1_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 48 := (concat bs1_5_0 bs1_5_32)
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
theorem bs2_4_0 : Interval s2Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 2 := bs2_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 2 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 6 := bs3_4_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_416 : Interval s5Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_448 : Interval s5Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_512 : Interval s5Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 539 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96)) (concat (concat bs5_4_128 bs5_4_160) (concat bs5_4_192 bs5_4_224))) (concat (concat (concat bs5_4_256 bs5_4_288) (concat bs5_4_320 bs5_4_352)) (concat (concat bs5_4_384 bs5_4_416) (concat bs5_4_448 (concat bs5_4_480 bs5_4_512)))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_640 : Interval s5Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 664 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 (concat bs5_5_512 bs5_5_544)) (concat bs5_5_576 (concat bs5_5_608 bs5_5_640)))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 6 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 57 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_2016 : Interval gbAtlas 5 2016 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2019 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 bgb_5_480)))) (concat (concat (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608)) (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 bgb_5_736))) (concat (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864)) (concat (concat bgb_5_896 bgb_5_928) (concat bgb_5_960 bgb_5_992))))) (concat (concat (concat (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 bgb_5_1120)) (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248))) (concat (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 bgb_5_1376)) (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 bgb_5_1504)))) (concat (concat (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 bgb_5_1632)) (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760))) (concat (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 bgb_5_1888)) (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 bgb_5_2016))))))
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
theorem bgb_6_5824 : Interval gbAtlas 6 5824 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5834 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 (concat bgb_6_448 bgb_6_480))) (concat (concat bgb_6_512 (concat bgb_6_544 bgb_6_576)) (concat bgb_6_608 (concat bgb_6_640 bgb_6_672))))) (concat (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832))) (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)))) (concat (concat (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)) (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216))) (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)))))) (concat (concat (concat (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568))) (concat (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664)) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760)))) (concat (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952))) (concat (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))))) (concat (concat (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304))) (concat (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)) (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)))) (concat (concat (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592)) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688))) (concat (concat bgb_6_2720 (concat bgb_6_2752 bgb_6_2784)) (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880))))))) (concat (concat (concat (concat (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040))) (concat (concat bgb_6_3072 (concat bgb_6_3104 bgb_6_3136)) (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232)))) (concat (concat (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)) (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424))) (concat (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520)) (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616))))) (concat (concat (concat (concat bgb_6_3648 bgb_6_3680) (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776))) (concat (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)) (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968)))) (concat (concat (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064)) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160))) (concat (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256)) (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352)))))) (concat (concat (concat (concat (concat bgb_6_4384 bgb_6_4416) (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512))) (concat (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608)) (concat bgb_6_4640 (concat bgb_6_4672 bgb_6_4704)))) (concat (concat (concat bgb_6_4736 (concat bgb_6_4768 bgb_6_4800)) (concat bgb_6_4832 (concat bgb_6_4864 bgb_6_4896))) (concat (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992)) (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088))))) (concat (concat (concat (concat bgb_6_5120 bgb_6_5152) (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248))) (concat (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344)) (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440)))) (concat (concat (concat bgb_6_5472 (concat bgb_6_5504 bgb_6_5536)) (concat bgb_6_5568 (concat bgb_6_5600 bgb_6_5632))) (concat (concat bgb_6_5664 (concat bgb_6_5696 bgb_6_5728)) (concat bgb_6_5760 (concat bgb_6_5792 bgb_6_5824))))))))
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
theorem bgb_7_2176 : Interval gbAtlas 7 2176 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2203 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768))) (concat (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 bgb_7_896)) (concat (concat bgb_7_928 bgb_7_960) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)))))) (concat (concat (concat (concat (concat bgb_7_1088 bgb_7_1120) (concat bgb_7_1152 bgb_7_1184)) (concat (concat bgb_7_1216 bgb_7_1248) (concat bgb_7_1280 bgb_7_1312))) (concat (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 bgb_7_1440)) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600))))) (concat (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 bgb_7_1728)) (concat (concat bgb_7_1760 bgb_7_1792) (concat bgb_7_1824 (concat bgb_7_1856 bgb_7_1888)))) (concat (concat (concat bgb_7_1920 bgb_7_1952) (concat bgb_7_1984 bgb_7_2016)) (concat (concat bgb_7_2048 bgb_7_2080) (concat bgb_7_2112 (concat bgb_7_2144 bgb_7_2176)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeee0fae8eae0feeeeee0fae8eae0feeeeee0fae8eae0feeeeee0fae8eae0feeeeee0fae8eae0feeeeee0fae8eae0feeeeee0fae8eae0feeeeee0fae8eae0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071584 * 2 ^ 32 + 4209568480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37199.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,5]⟩,⟨.and,[4,6]⟩,⟨.or,[2,3]⟩,⟨.and,[1,5]⟩,⟨.or,[7,8]⟩,⟨.and,[3,4]⟩,⟨.or,[0,9]⟩,⟨.or,[1,11]⟩,⟨.and,[2,13]⟩,⟨.or,[12,14]⟩,⟨.and,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4209568480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4209568480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37199

open PEqualNP.Outside.L_meta_37199 in
theorem PEqualNP.Outside.L_meta_37199 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071584 * 2 ^ 32 + 4209568480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071584 * 2 ^ 32 + 4209568480) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
