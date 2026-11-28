import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36667.Model
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


end PEqualNP.Outside.L_meta_36667.Model

namespace PEqualNP.Outside.L_meta_36667
open PEqualNP.Outside.L_meta_36667.Model
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

def SBf (j : Nat) : Nat := [6, 4, 7, 8, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36667

namespace PEqualNP.Outside.L_meta_36667
open PEqualNP.Outside.L_meta_36667.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x284c1a40128080018076a1601806bf43bd43bf42bd42be41bc41be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x180028810020025aa5a1c754f428ea98832d52107a060087808010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 6
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
  | 4 => packedAt s0K4 (244+((h/4+packedAt s0K4 (224+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s0K3 (170+((h/2+packedAt s0K3 (162+(h % 2)*4) 4) % 11)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfe03fffffffe01fffff80fffffff01fff1fe3f
  | 3 => 0xfffc03fc03fffe01fffff01fc07ffe07fe63c7
  | 4 => 0xfffffc0003fffffe01ffffe0007ffff81f83f8
  | 5 => 0xfffffffffc00000001ffffffff8000001ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x9604848428a224242450b162d48b628a26acdb
  | 2 => 0x2ba1292a51451d4948ac0ab56955115551562d
  | 3 => 0x4caba2329a69491d913d58198c66b4479a6346
  | 4 => 0x713233a3639191911dce6cd03078d9e11d83b0
  | 5 => 0x81c3c3c383e1e1e1e1f78f1e3e40e1861ff800
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000ccc0c0c0ccc0c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36667
namespace PEqualNP.Outside.L_meta_36667
open PEqualNP.Outside.L_meta_36667.Model
def s1K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (6+((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xf80fe01fe01fffc07c0fe07e07e0fff016327c
  | 3 => 0xfffffffe03ffffff0007fffff03fff83f8f
  | 4 => 0xfff0001fffffc0007fffff8007fffc001fc3f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8202142224204880851648a48a1451542d4b5
  | 2 => 0x556554ce51d4a91abe0aac56c568eba0d6325c
  | 3 => 0x468992949491b23256a81065965a22ca982b0a
  | 4 => 0x64cd1b19191923a3673cd941079cb0831d43e0
  | 5 => 0x870e1c1e1e1e3c3c7bcf1e79e410c30c1fbc00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00aaaaaa00aaa0aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36667
namespace PEqualNP.Outside.L_meta_36667
open PEqualNP.Outside.L_meta_36667.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x5c2cd202c1002d2800024001c0002600119442000000700123c6c000589831f00012980000009144468000a539d18bc19000a0bab1e84a8e02a8005460208001020008302000021e0c880ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x23310541400001a400763b8000027000d40c1600000001f1c8000000078003a000013cac1a289302e7b3c000007f00000007028100fc6f35000e4590a11c1600160000000000fcf8002f8008c09409e8486e000f0408300000000000174cc0000104c64500084000e2409400000919cae5c00128ea37320000000368107033029840008080443213130f860311694876000e0d01a6b3c8005c000d8bc02650000004842a0006c2930000645811108883d15800004d151c45007362140074402080000060e892732a800005b29800004e2596806432f1a0fa180f0780458043060000c00180404000c0000200800045004040800000424000000341c10181000140024000424027ca721cf54a439ea8c873e5090e7ca621e794c439ea90873d5110e7ca021cf94f429ea8e853e50d0a7aa92157d4d42ae29a859f5350a78a6a16714d428e29a85af5250a7ea2a14f141429f2a0853f54cca78a9994f952329eaa4659c438caeca3195d546329faa2653c544ca7ca8194f55032ce218653e53d067aa5a0cf943419eaa4835f53506b8a6a0e7d4d419e29a839c5350638a6a0cfd4941dba8a833c505067ca820cfd53319e2a6633e548c67aa918e710e31b7294636d528c67ea898cf151319f2a0633d540c7388618cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710cf951219eaa2433e540867aa810f948421af29c815d539027ca7206794e408f29c819d539027aa5204f546409f284813e531027aa4204f544409f28081ba501027ca9984f55330ce21e613e548c27aa9184fd51309e2a2619c434c2dea4985b14930bba8a6174514c27ea8184f150309f2a6413d54c827ea9104f152209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209f2a6213d54c427ea9084f152109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xac400c80000000ba6004000a805a868000029c398022188c0c81e0240144800000800410878718d51d0a1e63943428d58454ccb14439463287594430ca8d6210c328718d52d061e63943418b58854cc70c4394a3187594430c6956110c318718d544863860551218718d540861c63548408718d511030c4314930c510c514c21e63d50308b588540c23561150308718d54c821e63d52208718d54c421e63d5210
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 5 => packedAt s2K5 (880+((h/16+packedAt s2K5 (768+(h % 16)*7) 7) % 69)*7) 7
  | 4 => packedAt s2K4 (3970+((h/44+packedAt s2K4 (3618+(h % 44)*8) 8) % 194)*9) 9
  | 3 => packedAt s2K3 (1036+((h/8+packedAt s2K3 (988+(h % 8)*6) 6) % 45)*6) 6
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 1 => 0xc0ffffc0fff83fff07c1e0fffe1fe07fd13e73
  | 3 => 0xff03ffff03ffc1fff801ff07ffe1ff81e1cf9c
  | 4 => 0x3fffffc0001fffffe0007fffe0001fe0fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x44100888209000002942410900222a280650a5
  | 1 => 0x92299106492270cb0290a8d2b2154154d12652
  | 3 => 0xa4aa2121a46135550213a44d5419505618b18
  | 4 => 0x2cb344a49074a5a69cf4108769980619ba0de0
  | 5 => 0x30c38738e38739f8e739dce071111861fdf000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88ee88aa88eeaaaa88ee88aa88eeaaaa88ee88aa88eeaaaa88ee88aa88eeaaaa88ee88aa88eeaaaa88ee88aa88eeaaaa88ee88aa88eeaaaa88ee88aa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36667
namespace PEqualNP.Outside.L_meta_36667
open PEqualNP.Outside.L_meta_36667.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xe817d51d037e83a06f50740beaa4817e53902faa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c3dca5185b94a30bea9461ed528c2daa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c83de65907b0cb20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20f721241ed42483de64907b0c920bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd98621f830c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087dc8410fa108217e50043f660087e0c010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332f7a1665ec42ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca61977d0c32ee218657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf29683ee52d06dca5a0df54b41f6a96836d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef19663dc32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131ef21a63dd434c6fea498fbd4931b7a92637c524c7d8a498db14931ef19263dc324c7ee6298f78c531bfa8263fb504c6f6a098df14131fc2826378504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510fb90a21f6a1443ef32887d86510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29043ee42087da8410fbcc821f6190437e51087de4210fd88421f690843f521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28
  | 2 => 0x20542ba562442d12480027e7a000000000000001010d41f00000031a000eb21b00005cbc0000000000015b00000000001000000002010000014596335a0452d000000000002190001e000000000001278ca206000000a9474000969a800095c0024334a0d0001290001204c1d928200000000000648000000000000000000000000000000920bd20f20c3c00014a00036800000000001350004aa6894092a43c570f600001660d0299d3c6000001bc4560000027849c0ac000000000009817d00077cb61254149880000000a000000b80005952580037600113856148454001933bc00128a651148dc000002f2000000370000003d8940000013900013c000000000305b4000002a6188fe21c21e35c378710009e4000ef000a30001be4081ac711540fc0008500000000000000000380a38004d80000013421c0d4620963d431d4a2421f600047904386510000002e09400f9f62a21400028843000119882024038000000000013f000000000000002f68ed1a8b247026c839ac3e83b43487000c7c8228000008880013224e4f866800000000130002ba000db8fa00034800000000000099ff4bc210000402744f00008500000000000000590001601bc97cca9b507c0009e93715e000000000000000010b4f69ccd78ec0005ac0024d2de0a03920c000000000003700000000014c6e4868080ba254c78000000000d80000018cd50860887ac4f80a06c0ccf995200300000000800008020000000000000000400e01405005000000010070020180000b0000100000400a0080380400802003014002000008000040000000300e00400000000000000010000000080000000401024000000000080000000080300a004018000000040000300200000801002014000000000040100300000001000000000030030020140300500c0000300100e014000000040040000000000000002008004040010000180100200800000000012000000030040040a0080040040080200800000000000008000000000380400000800c000070040000080102a01c000090000240600701601c0080a00400c040020000140000200e0040e000010000000080260080080500c0040480000c0000500000001000002000004000020080000000900601c0100000e00804800bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1fbd4943b7a92877c5250fd8a4a1db14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0x3500000000065000276422000698383ae000d98003460013091024c0008600045e6248928a07e000001d00003f00000052400000185000330000d10000000009c00013ce398b1d60000000052a598d006c0007902197f48e7b5121902be0000016a0004e00000027601cf78293b40008992432c638000000000000002300078800000000000000000000006f91f0008740019e3321fcf80b91226200000002c7986c000000000e123d246728ad05f22e38c239bf3ce50c0017518c69ce08000da2f8fd000162000001fb50a465080c50845cc00000060001221f1000154788fe00028c001dd000000e4874300a34000003ee8346580051c200a7800150000b4800000009058c31b60013f80005c324ee00000000000000000a18000003ea87c000000085f8001c60006b80d000000000001cc000000d8a14180000000090000a8b10240ea000611111026a425800000000000a7000558000003fa784000dc000338ff1ab2e49b51c97c1ac0002d121000000b8a411aa9ad3484c1e472c3b05b000000988001e86d8b7270072a08c881d400128ce22947c2d8e722e0002d5189873c00c40000014000000000364450941420000001e8ac000755118001c23980000c4f40000025b11814c0f2961d41dc00000000001098b3000000001450005780000023a5408e0ab29a00000234000000e00000009bc000034a86c00012f4b094c002932aa4e4cc2324b84d9321d8032000508540005a0000731c88f0a49d404a20c8c1ba0fa4145e9a60001e47a99b33e2f1010002b22e87c85c3b60007c00009a898000000000000011b4943941082700000000228234001439082b00e855246000500a4099000000e224c0a40000000046003c99a770000c8848f34d00002480d0cc000bb9f90f40f051000000a0c0018200014449897412628271cd0001854b8002ec744b3a67000001169b41a07950b94b000530160004100511500025c00080207000538001f8000000000d90004b1161613082740018c17e55c32225442374440ff4dc2690192b4ea948480a537a000000000bc9740000000000000000000000e7800000000ba00046c000458000826913e01c19e0007b9c84cc848609e91761614827405e39d2291615a4787b1ee0762c1488ae000618000101123b83420e0002340000000000064000000685401c532e858000591d0a3d3e9464800003006516e74833a6300000081000000080490e90009649a86e40ca110aa604340b5101d300060400000000088000fd0004800019a08c00144a3f000238000874e
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x53c82cc6350b20ab59032c823e64947208f59251c825e63947209758e51c82ad64c87209798f548825d63d52208f993538823d64d4e208f992538823d6494e208fd91518823c64546208f992544825e63951209758e544827661951209d586544825f63551209718d544827761551209d185544823e6515120cb588544831f54d4d20c7153534834d62d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f19153482776154d209d185534825e6514d20c7d50534831c5414d20cb152424826c6550920b318d424826e65cc920cb15332482ad640c920cb150324834f530c920cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d990851483654214520d9cc8514836432145209b99721482ad64c8520d914721483645148520d9146204823d65950208f990540826e62150208f993530823d64d4c209b98b530823e6414c208f59053082766114c209d584530826d6588420cb552210832d5408420cb553200826f6548020cb55120082e461480209ed95200826e62953109b58a54c425e63153109758c54c423f6454f108f19153c426f6254f109b18953c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c425e63952109758e548426e62152109b588548423e64d4e108f593538426e62d4e109b58b538423e6494e108f592538423f6454a108f191528425f6354a109718d528423e6414a108f590528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109ed81534425e6514d10c7d50534431c5414d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109b994524432f5414910cb150524434f5314910d314c524435853c4110d914a104425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c10d6181530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520436552c84109d594210435953cc0109e594300427965840109dd9510042e462440109ed9510042d86344010
  | 1 => 0xc63e64951319b98a544c66d62951319e982544c67960951319bd89544c66c62551319ed81544c67860551318f994544c71d6315131c7152434c65c6550d31b3189434c72f54d4931cb153524c72f5414931cb150524c71c548c931a7590324c71c540c931d3d48324c73b54d4131ce153504c76b52d4131da14b504c73b5414131ce150504c76b5214131da148504c75a4314131d650c504c75a3214131d60c8504c75a31141318f596540c63e64150319798c540c71d54cc43197d95310c71d544c431b6181310c677654c4318f99353c863d64d4f219e98353c867960d4f218f99053c863d6414f219798f548865d63d5221cb58a548865e63152219758c548863e64d4e218f593538871e5494e21c7552538871e5454e21c7551538874f6254e218f990538863d6414e21cb95242886cc6350a21cb95332886ad640ca21cb950328874d530ca21ab593218866d629512197d8d544865c63551219ed81544867860551218fd91534863c6454d219bd89534867b6054d219e181534863e6414d218f590534863e64141218f590504865e63150219758c540867a60150219e580540863f6454c218f191530863e6414c218f590530867a6014c219e580530863e64948218f592520866d6590821b318d420866d650c821ab59032086e5610c8218f992510863d64944219798e510865d6394421ab593210866f65484219dd95210863f64540218f191500865f63540219718d500866f6254f409b18953d034f6254f40d318953d031d5390f40c754c43d031d53d0b40a718d42d031d5350b40c754f41d02ad62d0740c754d41d02ac6250e409bd89519026c6254640a758c419029d63d02408f994435023e65d0940a718d425025e63145409758c515023e65d0540ab58b415023f6550c40ab189431025f63548409718d521034f6354840d318d521032f4354840cb50d521023d6590840cb54a421032d52108408f596411032d5290440a758c411032d5210440a758f401032d52d00408fd95401032d52500409ed95401031d54cc730c755131cc2d8604c7309b98b548c26d62d5230c758e548c26e62152309b588548c31e5490e30b3189438c32e5494a30cb552528c32e5454a30cb551528c31e548ca30a7590328c31e540ca30d3548328c29d640c630a7593308c25d63951309bd89544c26c62551309dd85544c27461551308f990524c23d64149308f990514c23d641453097997314c2d8604c5309b988540c26d62150309d984540c27561150308f992530c23d6494c3097596430c2cc6250c308fd91520c23c6454830a7590320c2d9600c8308fd91510c23c64544309bd89510c26c625443097596310c29d640c4308f992500c23d6494030a7593300c25f654c0309ed95300c25e63153209758c54c823f6454f208f19153c823e6414f208f59
  | 2 => 0xd000000000003e439c0013d000000000003762607d15d2943848d0001987a03181f2ec00012165000650000002160d8000000000b8000001cc5f8b700000016c000001ba000fd8ff00052c00000000018000002c20005a8070fa7240004628270cea8c128c000000263940000008a000619070aa0001ac3413e0001042a1b93a8714fa88930086400215188550fa1ed0ac6c0f70eb2383c8238a6318780b21273f81f84c8bd18485ce820d01048c8988b31e61c5387733c26caf80011c0888291f27e5a4f200002c3783088c292130cb8000004bcef800414454000000000002a8000005001f09e00a420ad9b634220cf8000000180771ec2b81b08902a3ee200f28004181709d89c0006b0bf86a1ac7f879a182a43f0e3800000000869ce00000001000000440000c0001400020000000401c0902400010020000100800014010080000400014000080c0100100c0100000000010400b0000102c1301c0d02c0000c0106c000200101400044000300e0280401009000000000101c0a024010000000400008060040000002008010280d018000040d00c04000000080201003004010380100000000010000100c050040405c01000030000201800008010600104c0700401000040080400800004030000000400008020100101408008040400007802000010040000801014040000700015004000040900401000230000002a6f62546439b1895190e6e62942439b58a5090f4f4314943cb90c5250e3f6550c43ab1894310e5f6550c43b31894310eac6250f429798e5190a5d639464297d8d5090a5c63542428f9974350b1c53d0d42c714d4350aac6250d42d314f4250b1c53909428f5964310a3f6550842a718d4210a6f6550842b318d4210a7661153329d58454cca3f64547328f19151cca3e64943328f59250cca7a60152329e580548ca3e64946328f592518ca3f64542328f191508ca3e649513297d8d544ca6f62551328f994544cb2c54cc932c7152324ca3d6595032c718d540cb2c62550328f990540cb1d54d0c3297594430cb2d54d0832e3d0f420ca6d6510832e310c420ca5f654c832a7191320ca6f654c832ab191320caac6250f4197d8d52d065c6354b41d3d8d52d074c6354b41cbd0d52d072d4354b41cb54a42d072d5210b41a718d42906ad62d064197d8d509065c63542418f99743506ac6250d418f994425066e62141419b588505066f6254c419b189531074f6254c41d3189531063d6590c41c754e431071d5310c41c754f421063f6550841a718d421071d5350841c754f41106ad62d04418fd95411071d53504419dd95411066e62153319b58854cc6cc6250f318fd9152cc63c6454b31a759032cc63e64943318f59250cc66e62943319b58a50cc66e62d52319b58b548c63e6494a318f592528c63f64542318f191508
  | 3 => 0xd833e668990121c4000b68000003680011d2744d46b8312366b43f8ce3500009b9a33fa440bd0003982f03321017621c560fd21c000320002987e00e8820dc6f8000000000007a8023140000000012a000000000006d40013c29c340ad0002602c8000003ae1a400000000000e88340000e400204000394fd049000858000000001284e8ec150000000510320000010c0000000000001264cba80034c658001de3380002785925c0800005200019cf11622f20bc698000001d4ab1c0000000811893f26bc000b00e4401018572707080000000054c7b114000610050b134a4186690a416054421571f074c1e9470867480b8be18e6641696f000824bd80000058cee8323625f0d91723d676c409b80f06f48c9603ce03000000000674741c4000000000002020acfb0f730481c001480e25b0001503c600000044030044200332440004810924a82000001000000000a91c8534000f1122000000370004d0aa8003664100008609c0000003b0006e8cd9c12cc5c05c000428001031880002b8578002e80000018b3e200099800324220c695e400000000003d2000000043fe0e0e41261a86a4108921e0758001c60000d4a280019014c701cd12628c0001b000000878ed32a6400000040a688679310e025cf98a414a8484a0c33de808e59110284d80012c00086800117000000f31dc06000068a13000068129bc2ce35400000000000000000de0000006d1340000000000053c069422d40fcc08000007a8000000ec318749b7000000468b7000000c705a000000628000000405c8733b03d056918000784001da11e1e40000019684414121000179008d9194000cc00008a4ac75151000000000dc180000d70290004802f8001de000098d22d60000001c07800000000000000000482503f83d80000008ce78741be4e41d07c348000000000006803289f1c6000259912482ac5f87a00041c001ab3b2188000a02fa0385b0a11926a8001440002e8000000000000580f41e3e40015830a140000db000000000272b240c2e91603c000428420b05a0da11e25260cb994334e3ec5a00000000059977058288bc12a000000b89bf0062582692
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x20000101400a00600f1103975490006000d644030748d2c21400004c00208248418b8318c6255032a18e6a9085a0d0c7254c4310706a9ac5a0883431c9631513183aec2a06498d487250c504c68cba0642826386550604c431a18e6b14a910c2d769503288686392a621e818354d62d0740a18e6a90842060d635484110306b1aa5a008186550604c730a18e4b1ca91841d76950328c28639ac42a2410b5d8540c920a88e6a10a290525740c85148312b20a390a41895506148020
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x3202080c8754d62d044180c8754d62d074080c8758d521044080c8758d52d0040
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (i*5) 5
  | 6 => packedAt s3K6 (i*16) 16
  | 5 => packedAt s3K5 (i*27) 27
  | 4 => packedAt s3K4 (i*38) 38
  | 3 => packedAt s3K3 (i*49) 49
  | 2 => packedAt s3K2 (i*60) 60
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (6+((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s3K6 (718+((h/13+packedAt s3K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s3K5 (20359+((h/221+packedAt s3K5 (17928+(h % 221)*11) 11) % 1059)*11) 11
  | 4 => packedAt s3K4 (22272+((h/179+packedAt s3K4 (20482+(h % 179)*10) 10) % 782)*11) 11
  | 3 => packedAt s3K3 (1273+((h/8+packedAt s3K3 (1225+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s3K2 (243+((h/1+packedAt s3K2 (240+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xe07ffe07ffffff81fffff81ff83ffffcfe31ff
  | 1 => 0xfffffff81ffffffe07c0ffffffc1ffff23fe3f
  | 2 => 0xff80ffffe03f83fff800ffe0fffe1e03c3cfcc
  | 4 => 0xffffffc003ffffff0000ffffe003fc0ff0
  | 5 => 0xffff0000000003ffffffffff00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x290a22310489208059492909281232a84e10d5
  | 1 => 0x42144440c9124116029052325241455120e62a
  | 2 => 0x8526a89243a426aaa8289d489cb4181ac34b4c
  | 4 => 0x1658d12492074b4d34f20610e7298063b40db0
  | 5 => 0x1860e1c71c3873f1c73ce79c06311183fbb000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeaeac8c8e8e88888eaeac8c8e8e88888eaeac8c8e8e88888eaeac8c8e8e88888eaeac8c8e8e88888eaeac8c8e8e88888eaeac8c8e8e88888eaeac8c8e8e88888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36667
namespace PEqualNP.Outside.L_meta_36667
open PEqualNP.Outside.L_meta_36667.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x51000100c70940342562500bf43bd43be42bc42be41bc41ee21ec21bf40bd40ef20ed20
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x21a096292871d531063aa7a05914520
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (208+((h/4+packedAt s4K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s4K3 (111+((h/1+packedAt s4K3 (108+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7ffc1ffffffff03ffffc0ff83fffffe7e31ff
  | 1 => 0xfffffe07f03ffffc1e07fffffc1e07ff93fe4f
  | 2 => 0xf81ffff8003f07ffe007ff07ffe00781e3cf8c
  | 3 => 0x1fffffffc007fffff80007fffff801fc0ff0
  | 5 => 0xffe00000000007fffffffff800000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x9044444122084100a4494848812294a4261095
  | 1 => 0x218888324452822c0a8291932414215890e64a
  | 2 => 0x52d51490eaa44d556144ea45cb40560d634b8c
  | 3 => 0x651a21248c06969a5390308672996011d80d60
  | 5 => 0x861c39c70f38e7e39de73ce063118461ffb000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeac8eac8ea88ea88eac8eac8ea88ea88eac8eac8ea88ea88eac8eac8ea88ea88eac8eac8ea88ea88eac8eac8ea88ea88eac8eac8ea88ea88eac8eac8ea88ea88, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36667
namespace PEqualNP.Outside.L_meta_36667
open PEqualNP.Outside.L_meta_36667.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf29043ef42087d88410fb8c821f6990437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d037c85a06f10b40bf28e817d51d037e83a06f50740beaa4817e53902faa7205f94a40f7294816e52902faa5207b54a40b6a94817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c525037c84a06f10940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea98817e52102faa4205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f7a1641ec42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f7a1241ec42483dc64907b4c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb18e21f531c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea68877d4d10afa9a217e53442faa6885f14d10ee29a215c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443ec62887d4c510fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0x400006000000b82603026000160004c010000b5f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250fdea4a1dbd4943be29287ec5250ed8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210fdca421db94843bea9087ed5210edaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42be29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42df21885bc4310afca4216fd0842f721085bd4210bda84216b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccbde85997b10b32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c657e528cbdc85197b50a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbbc86997750d32f721265ed424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d06fca5a0df54b41bf286837d50d06faa920df94e41bea9c83bf439077a8720df94a41bea9483be42907788520df94641dfa0c83f741906fca120df54241bfa9a837c53506fea4a0fbd4941b7a92837c52507d8a4a0db14941fba0a83be41506fea0a0df14141bf2a0837e53106faa620efd0c41dea18837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331bf29663ee52cc6dca598df54b31f6a96636d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa92637c524c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f621443ee32887da6510df94621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a437e53486faa690df14d21fb90
  | 2 => 0xb3374084002020624691b1cf4ac72c840d24225aca787444e1acaca1a32e3b0d81860920ec978d303e000be0d51c6000000eb3a26d40009d000914000b04aa0011c2390000b0001f808c0300014c0009012716010600049000000260048000003fc0000018c0000011042a000620dd000000ac0d90000000021e292688340af0643cc000a941e0007386e0003d86f1800ca7d00e8a83e41ed2200307e0000000009848ce19404068a89f8912ee3f88a0702c4960d700014852c2f1c84ae094b081436887c589ac0ce0145323212c7e83f0340b65b42aa51366549119b22867b8179f307c000f68001ea000420000004dc001a518e3f4de8000005690e1e4000000000f9278270c2a264488b8dca210904cc171040404c8000040541ccc3a42000948388002ac5146d8004a00cc34a53000000970a323e7104810309a390ef800000698000000008dca720d3c63dcc69e7496728af9823323b4000f149a4a0000d816a1489306f0003a5061480f8904c622f398654eea3145a4805903c24e340eb01e44a04c111ab0246a89112406e9243e9fc060769180e04304e85517a0001380012b1906505b93e184280e096f16c9184400045009c8e17d0000006a22b330000f08800b8880a9839056684002350c88e81aa143ee7700020b3d05508c88f33e000628ca2527f9098ac06c4e4000821865e4b18df000000cf1ce002000b880000056c278000000010b11302e2182095d1566f00c0cb4367942c1350000008c1743a808c00111420000000f20da1400d93b49e424c09be0343c01683838e6e07783d000000d222c3380000000001a00000059000518001150000644c872050408b92331340540017b3224149a00010a000750000000440017f19e8f40e12c3ec5d8ba9900964749e8e617c810001ec168000211550004044f8d11782fc2a1d920e43cce9f90d81983a9360c290d1a0762d8418a885d0488143c8e13a647840800080180d386247e7c0d69211f40e90017847862cc48001263a0001a81b88289c0000008a4001684020a4ea8cd0f05a92509b3fe6bc711fd0163d0f500a41c6ec8692d31e230a098e40e8240400608e17c038563c05948721200203802000440000401004030060101600800000260002410800070220800009804028000583e020600000004834058060b802010040182c0300602002000cc0002a0182c000000203c00806000761300800816080020000e020000580200802010040a8260a058150000c01a0180c048020301c0102600002000040203a090180100001000008000200a000360c800080042181204840020a60000001014010320382a088041885400012038020201a010040084c0981c0101e010020400e060080000803804018001e85016800010720200001808060480000806824020040001c02816008
  | 3 => 0xcd1d73624944a0873d62948d8da3405406000f3f6448569b7182734cb2223ea1a8f30104902e0b996628e3e0801e929a76c221c62625f8d498411c2343fa1d3a02e80b0893e23ec6714a2dc3312399b306578b20453de3b84b9693c42787290a3806fc8b9441f815cab9b60b4254b814201c1e8010bd2ce430e9000086458250bb0007245712a14435cd1a4c1146210b9d80a22e4130534100010c80000064c459302b8950c90000ee3580006300042d1f00000000000000192000e12060008ecc51c514229cef
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x941502ae62901409bd89511026c62544408f596411023f65500409ed95401026f62553309b18954cc26e62153309b58854cc23f6454b308f19152cc26e62d52309b58b548c23f64546308f191518c26f62546309b189518c26f62551309b189544c27761551309d185544c25e65cc5309b98b540c26d62d50309d987540c27561d50308f596540c23e64150309b988540c26d62150309d984540c2756115030cb952520c32d5494830cb951520c32d5454830cd952510c3355494430d994a510c3655294430cd951510c3355454430d9949510c365525443097596310c355518c430d5544310c35551cc03097d95300c355514c0309ed95300c25e63153209758c54c823e6414f208f59053c832d5410b20b358c42c82ac644cb20ab19121c823e64d4e208f593538823e6414e208f59053882766114e209d584538832e5488620cb950218832e54c822097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d208f990534823d6414d209b997424832d5410920b358c424826c654c920ab191324834c534c9209b99721482ac6448520ab992204826e62d50209798c540825d63150209d984540827561150208f990530823d6414c209b98853082766114c209d584530823f64544208f191510826d65884208f992500823d64940209bd95200827b65480209bd8954c426c62553108f99253c423d6494f109b98a53c426d6294f108fd9152c423c6454b109b98b548426d62d52108f990538423d6414e109b988538426d6214e108f993528423d64d4a108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e6515110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10d5584534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c5244354538c5109d19531442f0604c5109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c109d984530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d53548108f990520423d64148109798c520425d63148109b988520435553c40109e59610042776544010d554d100427b6544010
  | 1 => 0x2887126a5ba4aae82a00188400b25f8a401814020401000100f00810120a0681c000201818160a018000c0200800120104804000e06010020f0184c040003800000e0180402010000c000a0019002050d02c000b0102806000000034071181002020080400102f8000205000042a00000b002030a00010040000c060e010080423008104800030081e010000808000b01816040080c0c0003800000000014060c010140a1e9bd8951d0e6c62547439b98a50d0e6d6294343cb90c5250e3f6550c43ab1894310e5f6550c43cbd0d5210f4e4354843cb50d5210f4d4354843ab18943d0aad6210e428f9974350aac6250d42d31895310a3d6590c42c754e4310b1d5310c42ab5884310b1d53d0842ab5924210b4d53908428fd954210b1d53508429bd954210b4d5350842abd954210b2f6550842ab18d4210b8e5350842cb54d4210b8d5350842c354d4210aac6150842abd814210a7661d53329d58754ccacc6250f32e350f42ccb2f5410b32b358c42ccb8e4310b32cb151428ca3f64546328f191518ca3e64942328f592508ca3e64951329bd89544ca3e6515132c758c544cb2d6215132c7152434ca5c6550d329b996424cb2c5490932e390e424ca6c6550932cb151424cb8d4350932cb153324ca3d6595032cb189540ca3e64150329798c540ca6e62150329b597420cb2d54d08329b594420cb2d5410832b358c420cb1d54cc832cb552320ca5f654c832c7551320ca6f654c832ab191320cb2d544c8329b98a50d066d62943419b98a539066d6294e41c794d43906ac6250e41a758c429072c5290541ab189431069d6310841cb548421063f6550441ab189411067765504419b98b54cc66d62d53319b98854cc66d6215331cb95252cc72d5494b31cb95152cc72d5454b319b98b548c66d62d52319bd89544c66c62551319ed81544c67860551318f990504c63d64141319b988504c66d62141319bd89540c66c62550319b988540c66d62150319e980540c67960150318f992530c63d6494c318fd91520c63c645483197d95310c677654c4319798c54c865d63153218f99053c863d6414f218f99250c863d64943219798f548865d63d52218f993538863d64d4e218f992538863d6494e21cbd5042886cd6310a21ab191328874e534ca218f992544866f62551218f994544863e6494d218f592534866d6294d218fd91534863c6454d219ed8153486786054d21cb152214865e63150219758c540867a60150219e580540863e6414c218f590530867a6014c219e580530866d6510821cb55042086cd63108219b59632086ac644c8219bd9521086ac64484219dd9521086ac6250f40a758c42d032d5210b40ab18941d032e5290640cb948419032e52d02409b988535026d6214d40c714d43502ac6250d40a758c425023e65d0540ab18
  | 2 => 0xc2c0b523a0027ebf9f80029800276a780000164002dc002900030000000002cc0027a180ec0018a13ae430086630e62c17c420c8389980697004a54c09b05a0e42888a990cec42fc9c966369a219a243aa943e0f415314918cc1b10c442c45ca1a262d2a287aafade7c26c039523b9e49330ea9a2a090445d818358b63489a40822981d8aa8d0ac96a9a2bc239f25b0fc71af88f058b39b201856672b4380c61f1741aa5a99ae6c1204ba8f09013e73934819c0129d4852620000a88828082c63c85a768aa602a00013a87000001a678a5e7faac0020e1d8001214e25090001e02300000218002fa7e8006aa36571d62828e95800000008785c5027400010ba1be1b800c1b16691c86d12800248552267721200000499ec27200c2000002c2911a849252509b69f1c2971ae2f8000015e00160000b400270b41d258b0c2f15051000c49586198455ada64a8c909bc211e879a38000001d1ac0e02e8087000000bba588c26e00178742921f8620000088000030000003600228428004e2d81e2ca51892ac190730d4001b85691e7a800008000f032000fa3d8e8a89ba148a8002320002c44a34119a04d9040513248ae0452a42799e9e2821018e37a10a700032800a1800ada4e8206830a2cbc05ea0000a680037000b58004b04205a2e3f9f40010e0003a00050669f6bb28400000130c44b8044f0ac2e23e0d2f40003e46800530ba7281c000801cab829826778964aaf6529ee45800000085211c94082001820011807930658d84820c5e906c2ae27f2f2192ae002c882a96220aeaa216650
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x8802a609a00e00000002460048080000000041e53458610002c000a2e72a332d88c061021c00000c1c18eca9a842160d531854210b06a9ec0a1085499c75410b32c1ea8b18859948d7690c42ccb06b1ac42a265839964390932a18eaa1a849960d5458c420ca163b2a899065435ca5350e41c1ca63128720e0d63548421068739ea82144383d516310a21a1ae929a6510e0c6494d3288706aa2c6210438358d5210b40a1ae429a86a060c531894350306aa2c621641431cd5410920a48e2aa0849060d5458c4248286ba0a69924183190534c920
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x32100a0681d516310b3280d87192534ca21a0481551631092080d87190534c920
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 601
  | 4 => 396
  | 3 => 28
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
  | 5 => packedAt s5K5 (18227+((h/200+packedAt s5K5 (16227+(h % 200)*10) 10) % 722)*11) 11
  | 4 => packedAt s5K4 (16236+((h/132+packedAt s5K4 (15048+(h % 132)*9) 9) % 476)*10) 10
  | 3 => packedAt s5K3 (1426+((h/9+packedAt s5K3 (1372+(h % 9)*6) 6) % 48)*6) 6
  | 2 => packedAt s5K2 (243+((h/1+packedAt s5K2 (240+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc0ffff07ffffff03fe1ff0ffe1fffffa31f1ff
  | 1 => 0xff07fff81fc3fffc1fe1ff0ffe1c0ffdce3e4f
  | 2 => 0xfff81fffe003f1ffe001fff1ffe00e060fcf8c
  | 3 => 0x1ffffffc01fffffe0001fffff007f00ff0
  | 4 => 0xffffe000000001fffffffffe00000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x5200411104808000a40250122025229010d095
  | 1 => 0x84518220c905202c0a20a104c2084560c6264a
  | 2 => 0xa32d45243aa435561113aa17540a8360b4b8c
  | 3 => 0x2ca518849220659a535408819992c047600d60
  | 4 => 0x30c610e71c3389e39d99ccc811030187bdb000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeee8ea88eee8ea88eee8ea88eee8ea88eee8ea88eee8ea88eee8ea88eee8ea88eee8ea88eee8ea88eee8ea88eee8ea88eee8ea88eee8ea88eee8ea88eee8ea88, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36667
namespace PEqualNP.Outside.L_meta_36667
open PEqualNP.Outside.L_meta_36667.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10050f029a7a316910001b8000cc01e00e17a012855001e0400a58d5ca600183ae6c219343689499487c5bb06000302a0022b289493a62400164660e0d2638b9d4e061868100040000e0c4800c08700263c18001ffd5007fe5401ff55007fc54017fd4c057f53017f94c05fd53015f54c05fc53017fd0c05fe43017f50c05fc4301ffd4803fe5201ff54803fc52007fd0803fe42007f50803fc42017fcc803fe32017f4c803fc3201ffd4407fe5101ff54407fc51007fd0401fe41007f50401fc41017fcc405fe31017f4c405fc3100ffc8401fe21007f48403fc2101ffd4007fe5001ff54007fc50007fd0001fe40007f50001fc40017fcc005fe30017f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a200cff59510065faca88033fc65440077e32a200cdf1951001cf8ca88003ff64440017fb222000efd91100057ec888003fe64440137f3222000ff59110005fac888003fc64440137e3222000ef1911000578c888033ff5444019ff2a2200cff55110067f8a88802fff63440177fb1a2000f7d8d10005bec68802ffe63440057f31a200bff58d1005dfac68802ffc63440057e31a200bf718d10015b8c68802fff5344017bfa9a200bff94d1005ffaa68802f7d5344017fe29a200bffd0d1005ffc868802ffd4344017fe21a2000ffd8910005fec488003ef624400177b12200aff9891000dfcc488003fd62440017eb12200aff1891000df8c488003ec624400376312200cffd4910057fca488033fd5244015fe2922000ffd0910057fc8488003fd4244015fe212200bffcc910057fc648802ffd3244015fe192200cffd4510067fca288033fd5144019fe28a2000ffd0510007fc8288003fd4144001fe20a200bffcc51005ffc628802ff63144017fe98a200bfd4c51005ff8628802bff2144001ff10a2000ff48510057f84288033ff5044009ff282200cff54110027f8a088003ff4044009ff2022000ff50110027f8808802fff3044009ff182200bff4c110027f8608802bff2044009ff1022000ff48110027f84088003ff1044001fd8822004ff84110027ec2088013ff65040097fb282004ff9941001dfcca080137e65040073f3282004ff5941003dfaca080137d65040013eb282004ff19410025f8ca08013ff64040097fb202004ff9901004dfcc808013be64040015f3202004ff59010005fac808013bd64040015eb202004ff19010025f8c80801fff540400fff2a02007ff5501003ff8a808013ff63040097fb182004ff98c10015fcc608013de63040056f3182004ff58c10035fac608013dd63040016eb182004ff18c10025f8c60801bff530400dbfa982006ff94c10037faa60801b7d530400dfe2982006ffd0c10037fc860801bfd430400dfe2182004ffd8810025fec408013fe62040037f3102004fb9881000ddcc408013fd62040017eb102004fb58810005dac408013fc62040097e3102007ffd481002ffca40801ffd520400bfe2902000ffd081002ffc8408003fd420400bfe2102006ffcc81002ffc640801bfd320400bfe1902008bf9841003ffea20801ffe510400ffea882007ff14410007fe8208003fe4104001fea082000ff10410037fe620801bfe310400dfe9882006ff0c41002ffe4208003fe2104001fe9082005ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff4004009ff2002004ff50010027f88008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802000fe44010
  | 1 => 0xbfe3148025fe98a4012ff0c52000ffe4290007ef2148003ff10a4001ff48520007da4290007fc21480037fb024013ffd4120027fca09004ffd5048009fe2824000ffd0120027fc8090003fd4048009fe2024012ffcc120027fc609004bfd3048009fe1824001ffc812000ff64090013fe2048009f71024004ff08120027d84090007f82048023ffb2e2011bfd971008ffccb8800efe65c4023feb2e2011bf5971008ff8cb8800efc65c4001ffb262000bfd9310007fcc988026fe64c4001feb262000bf59310007f8c988026fc64c4023ffaa62011ff9531008ffaa988047fc54c4011ffb1e2008bfd8f10047fcc78800afe63c4011feb1e2008bf58f10047f8c78800afc63c4011ffa9e2008dfd4f10047fca788023fd53c4011bea9e2008ff14f10047fe8788023fe43c4011fea1e2008ff10f10007fec588002ff62c4021ff3162001bf98b10007fac588002fd62c4021fe3162001bf18b1008ffea588043fe52c4023fea962010ff14b10007fe8588043fe42c4001fea162010ff10b10047fe6588043fe32c4011fe9962010ff0cb1008ffea388047fe51c4023fea8e2011ff14710007fe8388003fe41c4001fea0e2000ff10710047fe6388023fe31c4011fb18e2008ff4c710047ea6388023fc31c4021ff90e2000ff88710007fa4388043fc21c4023ffa862004ff9431008ffaa188013fc50c4001ffa062004ff90310007fa8188013fc40c4011ff9862004ff8c310047fa6188013fc30c4021ff9062004ff88310007fa4188013fc20c4009ffb2c2004bfd9610027fccb0800efe6584009feb2c200fbf59610027f8cb08012fc6584009ffb242004bfd9210027fcc908026fe6484009feb242000bf59210027f8c908012fc648401fffaa4200fff9521007ffaa90803ffc5484009ffb1c2004bfd8e10027fcc70800afe6384009feb1c200ebf58e10027f8c708012fc638401dffa9c200edfd4e10077fca70803bfd538401dbea9c200eff14e10077fe870803bfe438401dfea1c200eff10e10027fec508012ff6284009ff3142001bf98a10027fac508002fd6284009fe3142004bf18a1007ffea508037fe528401ffea94200dff14a10007fe8508037fe4284001fea14200dff10a10077fe6508037fe328401dfe994200dff0ca1005dfac30803fff518401fff28c200fff5461007ff8a308003ff4184001ff20c2000ff50610007f8830803bff318401dff18c200eff4c610077f86308037ff2184001ff10c2000ff4861006ff84308012fe6084009ffa842004ff94210027faa108013fc5084009ffa042004ff90210027fa8108013fc4084009ff9842004ff8c210027fa6108013fc3084009ff9042004ff88210027fa4108013fc2084009ff8842004fdc4210007f62108033ff65440197fb2a2000dfd9510004feca88033fe65440077f3
  | 2 => 0x400c7faa42005bfc5210013ffa108009ff9084004ffa8420027fc421002fff9908016ff8c8400bffa642005bfc3210009ffb088004ff98440005fcc220013fd61100017eb088004ff184400c7fea220063fe5110031fea888018ff1444004ffe8220027fe4110001df2088009ff5044004ff88220027bc411002fff9888017ff8c4400bffa622005ffc311002dff9088000ff88440007fa422005bfc21100097f3008004ffd4040027fca020013fd5010009fe2808004ffd00400277e8020013fe4010009fd2008004ff500400277a8020027f94010009ff9808004ff8c040027fa6020013fc3010009ff9008004ff08040027fecb10012ff6588009ff32c4003bf99620027facb10056fd6588009fe32c4004bf19620027fec910012ff6488009ff3244009bf99220027fac910002fd6488009fe3244004bf192200affea910057fe548802bfeaa44015ff15220027fec710012ff6388009ff31c4002bf98e20027fac710052fd6388009fe31c4004bf18e200a7fea7100537f5388029ff29c4014ff54e200a6faa710053fc5388029ffa1c4014ff90e200a7fa8710053fc43880037eb144001ffd4a2000ffca510007fd5288003fe2944001ffd0a2000ffc8510007fd4288003fe2144001ffcca2000ffc6510007fd3288003fe1944004ffd8620027fcc310002fe6188009feb0c4000bf58620027f8c310057ff518802bff28c4015ff546200aff8a310003ff4188001ff20c4000ff50620007f88310053ff3188029ff18c4014ff4c6200a7f86310007ff2188003ff10c4000fb8862000ffa4310007fc2188003f610c4004bf98220027fea110013fe5088009fea844004ff14220027fe8110013fe4088009fea044004ff10220027fe6110013fe3088009fe9844004ff0c220027fe4110013ef2088003fd9044004ff08220027f0411004fff65480277fb2a4000dfd9520004feca9004ffe65480077f32a4013ff5952009dfaca9004ffc65480077e32a4013df1952001cf8ca90003ff64480017fb224000ff9912004dfcc890003fd64480017eb224000ff1912004df8c89004fff5448027ff2a24013ff5512009ff8a89004bff63480257fb1a4012ff98d20015fcc69004bfd63480257eb1a4012ff18d20015f8c69004bff5348025bfa9a4012ff94d20097faa69004b7d5348025fe29a4012ffd0d20097fc869004bfd4348025fe21a4004bfd892000ffea490007fe5248003f72924001ff5492009fdaa490007fc5248003ffa124000fbd092000ffc8490007fd4248003fe2124001fb1092000ffe6490007fe3248003f71924001ff4c920097da6490007fc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4000bf1852009ffea29004ffe5148027fea8a4013ff14520007fe8290003fe4148001fea0a4000ff10520097fe629004
  | 3 => 0xf32c8004df9964001cfccb20013fd659003d7eb2c8004df59640004facb20013fc65900097e32c801abf592400f7fea920027fe549003dfeaa48009ff15240027fec720012ff6390009ff31c8002bf98e40027fac720076fd6390009fe31c8004bf18e400effea7200777f539003bff29c801dff54e400eefaa720077fc5390013ffa1c801dff90e400effa8720027fc4390009ffb148004ff98a4000dfcc520013ee6290003773148004ff58a40005fac520013ed629000176b148004ff18a40025f8c52007bff5290039ff294801eff54a400e7f8a520027ff4290039ff2148000ff50a4004ff88520077ff3290039ff194801dff4ca400e7f86520013ff6190009ff30c8000bf98640027fac320002fd6190009fe30c801effd46400f7fca32007bfd519003dfe28c8009ffd0640007fc8320003be4190001fea0c8009ff10640007788320077ff319003bff18c801dff4c6400eff86320073ff2190001ff10c8000ff486400e7f84320012fe6090009ffa848004ff94240027faa120013fc5090009ffa048004efd024004ff68120013ff3090009ff1848004ff4c240027f86120013ff2090009fe104801bffd95400ddfecaa006ffe65500077f32a801bff595400ddfacaa006ffc65500077e32a801bffd514004ffca8a006ffd5450013fe2a2801affd8d400d5fec6a006bfe63500057f31a801aff58d400d5fac6a006bfc63500057e31a801affd4d400d6fea6a006bfe5350035fea9a801adf54d400d7f8a6a0027ff4350035dfa1a801aff90d400d7fa86a006bbd4350013fe21a8000ffd8940005fec4a0067fe62500037f3128000ff589400cff8c4a0006fc6250037ffa928019ff949400dffaa4a0067fc5250013ffa128019ff90940007fa84a0027fc4250035ff9928019ff8c9400d7fa64a0067fc3250001ffb0a8000bfd8540007fcc2a0003fd6150001fe30a8000bf185400dffea2a006ffe5150037fea8a801bff1454004ffe82a0003bf4150001ff20a8000ff505400077a82a0027fc4150035ff98a801aff8c5400d7fa62a006bfc3150033ff90a8000ff88540007fa42a0067fc2150037ffa828004ff941400dffaa0a0013fc5050013ffa028009fed0140027fc80a0013be4050035ff9828004ff8c1400d7fa60a0013fc3050033ff9028004ff08140027feca20012ff6510009ff3288003bf99440027faca20062fd6510009fe3288004bf1944004dfcc820027ff5410013ff2a08009ff5504004ff8a820013ff63100097fb188004ff98c40015fcc620013fd631002f7eb188004ff18c40025f8c62005fff531002fbfa988017ff94c400bffaa62005f7d531002ffe2988009ffd0c4004ffc8620027fd4310013fe2188004ffd8840027fcc420006fe6210009feb108000bf58840027f8c420012fc6210031ffa908016ff948
  | 4 => 0x807ff3288403ff1944201fb8ca2100ffa6510893ed3288403fe1944201bf9862112ffea310897fe518844bfea8c4225ff14621007fe8310803fe4188401fea0c4200ff10621127fe6310893fe3188449fe98c4224ff0c62100ffe4310807ef2188403fb90c4201ff0862100fe84310803ff6088401ff3044204bf98221007fac110802fd6088401fe3044225ffd422112ffca110897fd508844bfe2844224ffcc221127fc6110893fd3088449fe1844201ffc822100ff84110807ec2088447ffb2a4223bfd952111ffcca9080efe6548447feb2a4223bf5952111ff8ca9080efc6548401ffb224200bfd9121007fcc890826fe6448401feb224200bf59121007f8c890826fc6448447ffaa24223ff9512111ffaa89088ffc5448445ffb1a4222bfd8d21117fcc69080afe6348445feb1a4222bf58d21117f8c69080afc6348445ffa9a4222dfd4d21117fca69088bfd5348445bea9a4222ff14d21117fe869088bfe4348445fea1a4222ff10d2100dfec490807ff5248403ff2924201ff5492100ff8a490807ff4248403ff2124201ff5092100ff88490807ff3248403ff1924201ff4c92100ff86490806ff6148447ffa8a4223ff9452111ffaa29088ffc5148401ffa0a4200ff90521007fa8290803fc4148445ff98a4222ff8c521117fa629088bfc3148403ff90a4201fdc852100ffc4290803ee2148403fe10a4201fb0852100fe84290803ff60484017fb024200ff98121007fac090803fc60484097e3024223ffd412111ffca09088ffd5048447fe2824222ffcc121117fc609088bfd3048445fe1824201ffc812100fde4090807fc2048413ffb2e8009bfd974004ffccba000efe65d0013bf32e80039f9974004ffacba0086fd65d0013beb2e80009f5974004ff8cba0026fc65d0013ffaa68009ff9534004ffaa9a0027fc54d0013ffb1e8009bfd8f4004ffcc7a000afe63d0013feb1e8020bf58f4004ff8c7a000afc63d0041ffa9e8020dfd4f40107fca7a0083fd53d0041bea9e8020ff14f4004ffe87a0027bf43d0013ff21e8009ff50f401077a87a0027fc43d0013ffb168009ff98b4000dfcc5a0027fd62d00017eb168009ff18b4000df8c5a0087ff52d003fff2968021ff54b400fff8a5a0027ff42d0013ff2168009ff50b4004ff885a0083ff32d003fff1968020ff4cb400fff865a0027ff61d0013ff30e8000bf9874004ffac3a0002fd61d0013fe30e8021ffd474010ffca3a0087fd51d0043fe28e8009ffd074004f7e83a0027fe41d0013fea0e8000ef5074004ff883a0083ff31d0041ff18e8020ff4c740107f863a007fff21d0001ff10e8000ff487400fff843a0087ff50d0009ff2868021ff54340027f8a1a0083ff30d0009ff1868020ff4c340027f861a007fff20d0009fe1068004ffd9640025fecb20013fe65900077
  | 5 => 0x954101cf8caa08b3ff5450413ff2a2822cff5514104ff8a8a08afff63504577fb1a822bff98d41015fcc6a08affd63504577eb1a822bff18d41015f8c6a08afff5350457bfa9a822bff94d4115ffaa6a08af7d5350457fe29a8209ffd0d4115ffc86a08affd4350413fe21a8200ffd8941005fec4a0803ef625040177b12822aff9894100dfcc4a0803fd6250455fe3128201bf18941007d8c4a0806ec6250459ffa92822aff94941167faa4a08abfc5250413ffa12822aff90941007fa84a0827fc4250457ff992822aff8c94115ffa64a08abfc3250459ffa8a822cff94541167faa2a08b3fc5150413ffa0a8209fdd0541007fc82a0803be4150457ff98a822bff8c54115ffa62a08affc3150455ff90a822aff08541007fec0a0802ff6050401ff3028200ff58141007f8c0a0812fc6050459ffa82822cff94141167faa0a08b3fc5050457ff982822bff8c14115ffa60a08affc3050455ff902822aff0814104ffeca20826ff6510413ff3288203bf9944104efcca2080e7e6510413feb288228bf5944104efaca208027d6510413fe3288209bf1944104dfcc820827ff5410413ff2a08209ff5504104ff8a820827ff63104137fb188209ff98c41015fcc620827fd631044f7eb188209ff18c41015f8c62089fff531044fbfa988227ff94c4113ffaa62089f7d531044ffe2988209ffd0c4104f7e8620827fe4310413fea188227ef50c4104ff88620827ff6210413ff3108201bf9884104ffac420802fd6210413fe3108201bf18841147fea42089bfe5210451fea908226ff1484104ffe8420827fe4210413fea108209ff1084113ffe642089bfe321044ffe9908226ff0c84114dfcc2208a3ff5110451ff2888228ff54441147f8a220827ff4110413dfa088209ff9044104fec8220827fd4110401dea088209fd5044113ffe622089ffe311044ffe9888227ff0c441137fe422089bfc2110413ffb008209ff98041025fcc020827fd60104017eb008209ff18041147fea0208a3fe5010451fea808228ff1404113ffe602089ffe301044ffe9808227ff0c041137fe402089bfc201044bffb2c4225bfd962112ffccb1080efe658844bbf32c42039f9962112ffacb10896fd6588401beb2c42009f5962112ff8cb1080efc6588401ffb244200bfd9221007fcc910826fe6488401feb244200bf59221007f8c910826fc648844bffaa44225ff9522112ffaa910897fc5488449ffb1c4224bfd8e21127fcc71080afe6388449feb1c4224bf58e21127f8c71080afc6388449ffa9c4224dfd4e21127fca710893fd5388449bea9c4224ff14e21127fe8710893fe4388449fea1c4224ff10e2100dfac510807ff5288403ff2944201fb94a2100ffaa510897ed5288403fe2944201ffd0a21007de8510807fe4288403fea144201ff10a2100fd88510
  | 6 => 0x5fea1a8432ef50d4204ff886a1006ff6250803ffa928401ff9494200ffaa4a1007fc5250803ffa128409fbd094200ffc84a1007be4250803fe2128401ef1094200fd884a1007ac4250803ff9928401ff8c94200fdc64a1007fd3250865f69928401ff0c942007fec2a1002ff6150801ff30a8400ff58542007f8c2a1002fc6150867ffa8a8433ff9454219ffaa2a10cffc5150865ff98a8432ff8c542197fa62a10cbfc3150803ff90a8401ff08542007fec0a1002ff6050801ff3028400ff58142007f8c0a1012fc6050867ffa828433ff9414219ffaa0a10cffc5050865ff9828432ff8c142197fa60a10cbfc3050803ff9028401ff0814204ffecba0826ff65d0413ff32e8203bf9974104ffacba08c6fd65d0413fe32e8209bf1974104ffea9a0827fe54d0413feaa68209ff1534104ffec7a0826ff63d0413ff31e8202bf98f4104ffac7a08c2fd63d0413fe31e8202bf18f41187fea7a08c37f53d0461ff29e8230ff54f41186faa7a08c3fc53d0413ffa1e8209ff90f4104ffa87a0827fc43d0413ffb168209ff98b4100dfcc5a0827fd62d04017eb168209ff18b4100df8c5a08c7ff52d045fff2968231ff54b4117ff8a5a0827ff42d0413ff2168209ff50b4104ff885a08c3ff32d045fff1968230ff4cb4117ff865a08c7ff51d0463ff28e8231ff5474118ff8a3a08c3ff31d0461ff18e8230ff4c741187f863a08bfff21d045ffe10e8209ffd834104ffcc1a0812fe60d0413feb068200bf5834104ff8c1a08c7ff50d0463ff2868231ff5434118ff8a1a08c3ff30d0461ff1868230ff4c341187f861a08bfff20d045ffe106822effd9641175fecb208bbfe65904077f32c822eff59641175facb208bbfc65904077e32c822bbf59241177fea920827fe549045dfeaa48209ff1524114ffec7208a6ff6390453ff31c8202bf98e4114ffac7208a6fd6390453fe31c8202bf18e4114ffea7208a77f5390453ff29c8229ff54e4114efaa7208a7fc5390413ffa1c8229efd0e4114ffc87208a7fd4390453dea1c8209ff10e41007fec5208b7fe62904037f3148200ff58a41005fac5208b7fc62904037e314822effd4a4116ffca5208bbfd529045bfe2948209ffd0a4116ffc8520803fd4290413fe2148229ffcca4116ffc65208a7fd329045bfe1948209bf98641177fea3208bbfe519045dfea8c822eff1464104ffe8320803bf4190413fba0c8229ffcc64114ffc63208a7fd3190453fe18c822dffc864116ff84320803ff6090401ff3048204bf98241007fac120802fd6090401fe304822effd4241177fca1208bbfd509045dfe2848229ffcc24114ffc61208a7fd3090453fe184822dffc824116ff841208b3ff65504597fb2a8200dfd9541004fecaa08b3fe65504077f32a822cff59541165facaa08b3fc65504077e32a822cdf1
  | 7 => 0x10020181a0110560100784a0000580180a00c0380f80006e00c000000000000201d04e06c1200601c018030000400000400100605c078070020000000407200000800000004038000060000f00000400019005002014058030180240000b00e06005802000000010090240200100000e0040980902c00c0001d00a0200800703c03c090010200000380001207c05800004088048000000080000402e0040180701002400003004000268000221000180905c00c06000000040020030000240180000404c0b802000024010000020201280a006000038020ac0080000700a1bc00004000004018050800080080a01c00c018010000000201c002020088150ca01000002004000238010000080500000000c158030480000480007a044030000160000000b020000000010040100700a02a00c138060840040481500a00c0100700a06c1383a00e008038080020100580200000c000080200340200300200802805000000000000020100100200201801000006000050060040000902d000038080000080000180e01e000108010080080380101a0480d00102c00800004068000018080040000380000e0040281c00400c0501f00000802015000000020000020383d8020000100582201c0040000e0000080680001404c04831038054008030020040700f0100000000b00009ffd974204dfecba1027fe65d08077f32e8409ff597421adfacba1027fc65d08137e32e8401bf9934204ffea9a1027fe54d0813feaa68409ff1534204ffec7a1026ff63d0813ff31e8402bf98f4204ffac7a10d2fd63d0813fe31e8402bf18f421a7fea7a10d37f53d0869ff29e8434ff54f421a6faa7a10d3fc53d0813ffa1e8409efd0f4204ffc87a1027fd43d0869dea1e8409ff10f4200dfac5a1007ff52d0803ff2968401ff54b4200ff8a5a1007fe42d0803df2168401fb90b4200ff885a1007bc42d0803ff9968401ff8cb4200ffa65a1007fc32d0813ffb0e8409ff98742005fcc3a1027fd61d08017eb0e8409ff187421affea3a10d7fe51d086bfea8e8435ff147421a7fe63a10d3fe31d0869fe98e8434ff0c74200ffe43a1007fc21d0803f610e8409ffd834204ffcc1a1012fe60d0813feb068400bf5834204ff8c1a10d7ff50d086bff2868435ff543421aff8a1a10d3ff30d0869ff1868434ff4c3421a7f861a1007ff20d0803f79068401ff0834219ffecaa10ceff6550801bfb2a84009fd954219ffccaa100efe6550867feb2a8433bf5954219ff8caa100efc6550867be32a84039f1954200dfec8a10cfff5450813ff2a28433ff5514204ff8a8a10cbff63508657fb1a8432ff98d42015fcc6a10cbfd63508657eb1a8432ff18d42015f8c6a10cbff5350865bfa9a8432ff94d42197faa6a10cb7d5350865fe29a8409ffd0d421977e86a10cbfe435086
  | 8 => 0x589295320b1c80b10000410000000000001cb8002841a725d263036000195800306208aafb1980012a33430f9bcb1a324a0322c0240822430752eb99312e8282d2aea8910cb27808928a8edaac0d5303b2eaa59b71aea42a000002709ec87c83416da790e10a20e18522988bc250840075b351caac31659e1ad300014800000002000004bb3ea0384c0922570000c600015c062a279e9a2400000000000030717c1858350a2aef00000033721780000000000f80027b2bd8003339570570000908003080d1000053113000000140a199c18ee98700008d8000ae2dd16006626f83c9971558002420000003050cba1310a8f8a4c0a5085058a97a9002b80b98a0a48d2230ae70002a680023219f29ab0e85e1fe000064ac70cfb2a00021eb3d17189e9b403d12b00029a32b00000000031700009f0000000d482e0fb8001cd00000008a0001b2800128800141a349d0ab28191040002248d40de1851ba8001ffaba93186d80003f25320f8219a40098c227c8002c903fa5e1d38489ac13920a1671df022238a488001e0a168b58002a3b0323300299100027893780018b8000000728001acb0229580015f0001b3000176212a2e8000b0000000135afcb16063000336a1712d0000001728b2b0b95a00000009523424caa800000c9710001b9a6a1320000001c3a450309ee0ea8738002710a403800010d0000000002380001942d70000000a80cc0c2817000ab6a858810c90500e600011bb1c2329bb8799dbac003a2f09f1a752d18e028d9a39a21b88003151d4ad40bc96900033e00000000028e0d7945a01acd0fc04aa2d00004d0000288370000d38188000be0002c880010081d17a00000006e18891601b288ab1211842b1833a83eaca8000000002288978000c093b18103200024d2898730f0ab78bf2a09e10ef1f78001c50001f49fd0000001b197094a14685aadd8c98002b8a931de00005910fa592140000a30002839d7afea7e08d2d99a98002df0002a48000cc8b0af4a700001fd8f18000259f30f30000001b08b70ac80b0aa0002e180380400001c0380a0060481c80201202c0a00101c000070000000100280200000c0101302c0880400202a0100000701009c000020040002400006201c0600400a0040081c00a00c0600600213002005014000000010060200900a0180040d80201c0000002c01e0001384101c0380000004a04800804006044028040380080000b0100a8140020660041200300203c000030000000500102601c0283104001c00008002000000090280000300903807c0d8020120701d02d0140140b08600c0680480200c024000060020040300000400000004002030020000160101903100e0240480500c01c3503b00003006000010008030a00100000080301602404019006054118040260004300503e0000200
  | 9 => 0x1ad0b6a2f9bf03128183784832ba6e93d9bd22b908a4e800214982b262928860000000f78809afb2fae32bf0a72741ba11e2b82b017c9fc8bd005ae6063a0f2760061ae0239152d832791481289d2271c58fc8c81e31bc1a48bd98789881998dade13828d0d6afe3232aa00d2ad07e96085126d82919b0248ec0d0a54af1a9081ca1a00015e8369948000003002b329fa918efa9498e01aa8e8000001248a9831aa1ac9a35a9107e32cb229af3290418f014cacc9b105996b11f02321d8841361b900021225b8938002772de9438b4936962ab705a1291431251b8000105a551aa15d0699ad86121c80031f1f88da06c85f0fa1b008b12a87b2730b60000001d928f9d127fab92739c8856026000078800186015b250001ed2862228000c893a8001792bb84423fb3925c8a0a9eaba22921f9ce0898e91081509590002d61119a0a5f84f15810798aae3a3526ab2f1642458fd1768019d687780015a97ea9f2efa4aa5d9bea2e22a09b930210a8a1c0a1c32593286ba2323baaaab18002d78828eb26c08328f1e92b48c316e20b9d431490ca110ea19905f9738000031501d805080000000000000023aabb0001349dfa3f0e5adcb100a88c41fb2c233b11c23e9620002ec0a622100000013fac39da00000016600000026880000000024780007433028201f0002dbb3c0001138002b988e0d80001dc86a119000004000011b401f117d95ca3b18c098220a2692b8ff86d000319255a8781c0000d5acb22800100007484331da7d00a1f29bda3e0298c3aad84097f9071db19a0001561d50aa90b1c90000ae8000000001918001821be0ba0000c49d294a8b39902368549fe9c28772f90f4a61af425980031b1e51dc11f8001a7ae407f9a882aa539809ef32407690482c161247117225003a6e06c0b40e2026a56b0197833f142147a75a09aff9b48cd16e9212a10602be0932c4acf12d98c968337b2c0deb0a1daa2f0db8e79618af163123a519341de8b927ea5eb209512d52259399819890490c6a4904e04532995bae81801350a02363201230ec8878e8a629060ad2ea1271f53320bab0ca60adc1c60818ce1222eb2a990ead590008a83295295fb1311426d0df04ea719e41ceaf515e25011da960000f500c0b233fa30106a0589b2650f90848ac02e849a722e799d8cda9c97aac61b600000031ab121551938dd09fa3a01796baf3865197ae8ad0b1c8b98e3000047b0e21521620787628c1742bc01da461339a2afb87a1839331538ee1460550e519eaf2294121a540a6ab4263a5b0dc9cc1429240ce8e2a0e116b312d014c2c09e829d852ad395486588e8469f6a9b91804ca2213c03925c0e68001dd919a46a182e4a438000001a63331579d580000003015889020d000264a7a00000e0d8b358a58d62a50b7af685d8568002d90b18001c009
  | 10 => 0xd01988eb96507092c99501eadfb389e6afd80000030123980005b2e501680017f071aff2da21591e80014fac580032732200000000026b8000002e21a187d8538110001cb01b82a08398300030d00000013e999aa20bb00002d0e700000000024f91d31e800000314000000334a012d48001b5967b1380f10a02b12004d80000017ba601598919fa8c71fa0e48579e39d1a1000012f800120b0486f905196a82a6980027a9758000000d9b238002f82f88000968272a910c00e80001493106e9a80000000a787f126a1e0a1a0e9a914406b28bab52da9898afab3a4a2830000bb99619f94b97721f00010d80908c83b22b10294da5a8f70002020002fa138b12a7d8ca0000002ae151861aa620c2612482c42c180011b2970002299521909c1310b05a661ea330a0d8df8002621f089c8c7b3a27c18480000009707133d82f000293aaeaec8949450c59c783c0d72e284a2ca0688e38000a11ec2260000332e901a26819c91c99d0540000fe8080f3ac2b2e01322013b842101a7ba810139f70003119a516680000009a81e09919e258963aa7979800000000088ae58f8149b3199b8d00ca99c31b87918b1e000019805806780008f3329722eeabd1258002e68703269c6ab588f8003189eeac68640002339cf2ac8722bea9d03b8209c31b5004aa700016d1e58fd8fa9f2000038ac514b2db10310b80000025a0a933800000000506217490902f86f0001cf8001ff02ca669ab0001eda4480021a8002a30b832814e07c1751a59688b516c286a139a695d9c7317a3cae9835af730798d241a801fc302a808d911a2a29121e29eb9f9221886b1e21baf32bc9308279b683994f2ab89d96c9c4b0f0ff23c30dafb007acead6a890070100e99020f42090438db2fd0339700668c113a2b224988832da999372ce20723923da0a81f9c40962cb86918f0f590f04faee2ab2441880ab28c9cd8e82f029c24116a0b8a02b2880024080000000031691a8001f408c034a9680000000022d80000006800000024b10e27280000000012c000252a0421b30691283aa510fe31f80026ca31173000206969a9921888b89c2318bf87a8182f29108dc0c1a9e2b600031d0153088022579a3129894045a7994030c23d28b1e4b0b2051488782c12cf93c9eaa74aa0012240208339a4d9b22690000000000000000000001a0315918964aed1411f98001d32008f202d9f39c9a581eb19a94918f89a2e09e70068001ca309a5f11780a9100fb00014d00005c2f78000ad8000002060002521ab8003042cc19218e855a6794700022a8002ed9bb30a86715b00017b0c50210f616f12f26b0000002981789cc80024f060800109a2caa413e28485ea049e896fb2a8802658003219f02882560dd88582287d0cf1d7144b3b9b39e21d61260f9a9b2d130927f1e61278251aa984
  | 11 => 0xa396a80000880000013f0001229f823789e1b780005d3008000002e10c000033c992a8531100032120caf60d2af98e09f62952f12c7a921159e7aa897d14eaaf07b8abae02bfa23a871568d183d8ed0e432d2d21d21ef93d05b8daa6f1868bea6724e04b0d32d89d88872c8044acd89992e1bf86a851a778000f280010104700003e00021d0001f5a191fbab08140001d9911000000000103a3705ca642fa9540109779c20000000160000f10b300da4b80017e0002f5b36276afc0000000f69281dd0461a11
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe4358810006ed4358810006ec435881002eef7158810006ee7158810006ec7158810006ef5158810006ee5158810006ed5158810006ec5158810006ef3158810006ee3158810006ed3158810006ec3158810026ef7058810026ee7058810026ed7058810026ec7058810026ef5058810026ee5058810026ed5058810026ec5058810026ef4058810026ee4058810026ed4058810026ec4058810026ef3058810026ee3058810026ed3058810026ec3058810026ef1058810026ee1058810026ed1058810026ec105881004cff76d0810024fe76d0810004fd76d0810024fc76d08101ae7e65d08100067d65d081004ebe64d0810006bd64d08101a6de63d0810006dd63d081000eee62d0810006ed62d0810004ff7650810024fe7650810004fd7650810024fc76508100057f755081003d7c755081019e7e65508100067d655081004ebe6450810006bd6450810196de6350810006dd635081000eee6250810006ed625081002fac4250810005f77150810005f47150810004fd76d041018e7e65d04100067d65d041004ebe64d0410006bd64d0410186de63d0410006dd63d041017eee62d0410006ed62d0410004ff769041004cfd76904101767e65904100067d659041004ebe6490410006bd649041014ede6390410006dd639041016eee6290410006ed6290410025fa7090410005f97090410004ff76504100057f755041003d7c75504101667e65504100067d655041004ebe6450410006bd645041015ede6350410006dd6350410005ef725041002dec7250410156ee6250410006ed625041004cff7610410024fe7610410004fd7610410024fc761041003d7e75104100057d75104101467e65104100067d651041004ebe6410410006bd641041013ede6310410006dd6310410136ee6210410006ed6210410025fa7010410005f97010410084ff7688410024fe768841000cfd7688410024fc768841003d7e75884100057d758841012e7e65884100067d6588410006be6488410006bd6488410126de6388410006dd638841000eee6288410006ed6288410025fa7088410005f97088410084ff764841011e7e65484100067d6548410006be6448410006bd6448410116de6348410006dd634841000eee6248410006ed6248410025fb7644010006fb7644010004fb76440100077b75440101bf7875440100277a6544010027796544010007bb7444010007b87444010027ba6444010027b96444010007db73440101b7d87344010027da6344010027d963440101b77b53440101b7795344010007eb7244010007e87244010027ea6244010027e96244010025fb7144010027f371440101c6fa6144010027f261440101bff251440101bff15144010007f24144010007f141440101b7f331440101b7f03144010007f22144010007f12144010
  | 1 => 0x9010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf53590100063f5359010006be5359010006bd53590100063d5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006be3259010006bd3259010006bc3259010006be7159010006bc7159010006bf5159010006be5159010006bd5159010006bc5159010006bf3159010006be3159010006bd3159010006bc3159010006bf2159010006bc2159010026bf7059010026be7059010026bd7059010026bc7059010026bf5059010026be5059010026bd5059010026bc5059010026bf3059010026be3059010026bd3059010026bc3059010026bf2059010026be2059010026bd2059010026bc2059010026bf1059010026be1059010026bd1059010026bc1059010006df7558c10006de7558c100065e7558c10006dd7558c100065d7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006de4258c10006dc4258c10036df7158c10006de7158c10036dd7158c10036dc7158c10006df5158c10006de5158c10006dd5158c10006dc5158c10006df2158c10006dc2158c10026df7058c10026de7058c10026dd7058c10026dc7058c10026df5058c10026de5058c10026dd5058c10026dc5058c10026df4058c10026de4058c10026dd4058c10026dc4058c10026df2058c10026de2058c10026dd2058c10026dc2058c10026df1058c10026d71058c10026de1058c10026dd1058c10026d51058c10026dc1058c10004ff755881001cfe7558810004fd755881001cfc7558810004ff745881004cfc7458810004ff7358810014fe7358810004fd7358810014fc73588100067f53588100067d5358810026ef7258810006ef525881002eee5258810006ed525881002eec525881002eee425881002eec4258810006ef325881002eee3258810006ed325881002eec325881000cff715881000cfd715881002cfc715881002eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef53588100066f5358810006ee5358810006ed53588100066d5358810006ec5358810006ef4358810006e
  | 2 => 0x8e7c65c4110006bf64c4110006bc64c4110006df63c4110046dc63c4110006ef62c4110086ec62c4110025f671c4110026f761c4110025fa76c4110026fa76c4110024fa76c41100077b65c41101d77865c4110007bb64c4110007b864c4110007db63c41101cfd863c41101cf7b53c41101cf7953c4110007eb62c4110007e862c4110025fa71c4110026fb61c4110027f361c41101cff231c41101cff131c41100067f74594100067e74594100067d74594100067c74594100067f73594100047f73594100067e73594100067d73594100047d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067e42594100067c42594100067f32594100067e32594100067d32594100067c325941003e7f71594100067e715941003e7d715941003e7c71594100067f31594100067e31594100067d31594100067c31594100067f21594100067c21594100267f70594100267e70594100267d70594100267c70594100267f40594100267e40594100267d40594100267c40594100267f30594100267e30594100267d30594100267c30594100267f20594100267e20594100267d20594100267c20594100267f10594100267e10594100267d10594100267c105941004ebf759901004ebe759901004ebd759901004ebc759901004ebf739901004ebe739901004ebd739901004ebc7399010006bf53990100063f5399010006be5399010006bd53990100063d5399010006bc539901004ebf729901004ebe729901004ebd729901004ebc7299010006bf5299010006be5299010006bd5299010006bc5299010006bf3299010006be3299010006bd3299010006bc329901004ebe719901004ebc7199010006bf5199010006be5199010006bd5199010006bc5199010006bf3199010006be3199010006bd3199010006bc3199010006bf2199010006bc2199010026bf7099010026be7099010026bd7099010026bc7099010026bf5099010026be5099010026bd5099010026bc5099010026bf3099010026be3099010026bd3099010026bc3099010026bf2099010026be2099010026bd2099010026bc2099010026bf1099010026be1099010026bd1099010026bc1099010004ff755901001cfe7559010004fd755901001cfc7559010026bf7459010006bf5459010006be5459010006bd5459010006bc5459010004ff7359010014fe7359010004fd7359010014fc73590100067f53590100067d5359010006bf4359010006be4359010006bd4359010006bc4359010004ff725901000cfe725901000cfc7259010006be4259010006bc425901004cff715901004cfd7159010024ff7059010024fe7059010024fd7059010024fc7059010026be4059010026bc405
  | 3 => 0xf65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6418910007af6418910006af6418910006ee6418910006ed6418910006ec6418910007ac6418910006ac6418910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc63189100076f53189100076d53189101deef6118910007e63118910007e531189101dfe610189101dfe4101891004cff76d0910004fe76d0910004fd76d091004cfc76d09100067f65d09101ae7c65d0910006bf64d091004ebc64d0910006df63d09101a6dc63d0910006ef62d091000eec62d0910004ff7650910004fe7650910004fd7650910004fc76509100057f75509100657c75509100067f655091019e7c6550910006bf645091004ebc6450910006df6350910196dc6350910006ef625091000eec6250910057ac4250910024fe76d0510024fc76d05100067f65d051018e7c65d0510006bf64d051004ebc64d0510006df63d0510186dc63d0510006ef62d051017eec62d0510025fa70d0510005f970d0510004fe76905100067f65905101767c6590510006bf649051004ebc6490510006df639051014edc6390510006ef629051016eec6290510024fc76505100057f75505100657c75505100067f65505101667c6550510006bf645051004ebc6450510006df635051015edc6350510005ef7250510055ec7250510006ef6250510156ec6250510005fb7050510025f87050510004fe76105100657e75105100057d75105100067f65105101467c6510510006bf641051004ebc6410510006df631051013edc6310510006ef6210510136ec621051006cfe76885100657e75885100057d75885100067f658851012e7c6588510006bf6488510006bc6488510006df6388510126dc6388510006ef628851000eec6288510024fc76485100067f654851011e7c6548510006bf6448510006bc6448510006df6348510116dc6348510006ef624851000eec6248510005fb7048510025f87048510004fe76d01100657e75d01100057d75d01100067f65d011010e7c65d0110006bf64d011004ebc64d0110006df63d0110106dc63d0110006ef62d01100feec62d0110005f671d0110005f571d011004cff7650110004fd765011004cfc76501100067f65501100de7c6550110006bf645011004ebc6450110006df63501100d6dc6350110006ef62501100ceec6250110005f77150110005f47150110027f0105011000cff7648110054fd764811000cfc76481100057f75481100657c75481100067f654811009e7c6548110006bf6448110006bc6448110006df6348110096dc6348110006ef624811000eec6248110005f77148110005f47148110027f010481100067f65c4110
  | 4 => 0x8d101eedc10d8d1000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d8910006df63d8910006dc63d8910056ee62d8910004ff75d891001cfe75d8910004fd75d891001cfc75d891004cfe74d8910004fd74d8910004ff73d8910014fe73d8910004fd73d8910014fc73d89100067f53d89100067d53d8910006ef52d8910056ee52d8910006ed52d8910056ec52d8910056ee42d8910056ec42d8910006ef32d8910056ee32d8910006ed32d8910056ec32d891000cfe71d8910024fd71d891000cfc71d8910056ef21d8910024fe70d8910054fd70d8910024fc70d8910056ef20d8910055ee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89100076f53d89100076d53d8910007e631d8910007e531d89101e7e610d89101e7e410d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d89100066f53d8910006ee53d8910006ed53d89100066d53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d89101e6ef71d8910056ee71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef31d8910006ee31d8910006ed31d8910006ec31d8910006ef70d89101e6ee70d8910006ed70d89101e6ec70d8910006ef50d89101e6ee50d8910006ed50d89101e6ec50d89101e6ee40d89101e6ec40d8910006ef30d89101e6ee30d8910006ed30d89101e6ec30d89101e6ee10d89101e6ec10d89100057f75589100657c75589100067f65589100067c6558910005bf7458910005bc7458910006bf6458910006bc6458910005df735891005ddc7358910006df6358910006dc6358910056ec6258910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf745891004cfc7458910006bc745891004cbc7458910004ff7358910006df7358910004df7358910014fe7358910004fd7358910014fc7358910006dc7358910014dc73589100067f53589100067d5358910054ff7258910006ef725891006cff7158910006f77158910084ff7058910006fb7058910005ee7618910056ee7618910004ee7618910006e
  | 5 => 0xcfe725911000cfc7259110006ec725911000cec7259110004ff7159110006f77159110004ff7059110006fb7059110004fe76191100067f65191100067c651911004ebe6419110006bd6419110006dc6319110005be7619110006be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006bf6319110006be6319110006bd6319110006bc63191100079c63191100069c63191100073f53191100073d5319110006be6219110006bc6219110007b63119110007b531191101f7b610191101f7b4101911004ebf751911004ebe751911004ebd751911004ebc751911004ebf731911004ebe731911004ebd731911004ebc7319110006bf53191100063f5319110006be5319110006bd53191100063d5319110006bc531911004ebf721911004ebe721911004ebd721911004ebc7219110006bf5219110006be5219110006bd5219110006bc5219110006bf3219110006be3219110006bd3219110006bc321911004ebf711911004ebd7119110006bf5119110006be5119110006bd5119110006bc5119110006bf3119110006be3119110006bd3119110006bc3119110006bf2119110006bc211911004ebf701911004ebe701911004ebd701911004ebc7019110006bf50191101f6be5019110006bd50191101f6bc5019110006bf30191101f6be3019110006bd30191101f6bc3019110006bf20191101f6be20191101f6bc20191101f6be1019110006bd10191101f6bc101911005dde76d8d1005ede76d8d10014de76d8d100075f75d8d100075c75d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006de62d8d10006dc62d8d101efd771d8d1005fd471d8d101efd610d8d101efd410d8d10006df75d8d100065f75d8d10006de75d8d10006dd75d8d10006dc75d8d100065c75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006de42d8d10006dc42d8d101eedf71d8d1005ede71d8d1005edd71d8d1005edc71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df21d8d10006dc21d8d10006df70d8d101eede70d8d1005edd70d8d101eedc70d8d10006df50d8d101eede50d8d10006dd50d8d101eedc50d8d101eede40d8d101eedc40d8d10006df20d8d101eede20d8d101eedc20d8d101eede10d8d1005edd10d
  | 6 => 0xe31d95100067d31d95100067c31d95100067f21d95100067c21d95100067f70d95102067e70d95100667d70d95102067c70d95102067e40d95102067c40d95100067f30d95102067e30d95100067d30d95102067c30d95100067f20d95102067e20d95102067c20d95102067e10d95100667d10d95102067c10d951004cfe76d91100067f65d91100067c65d9110006dc63d9110004ff75d911001cfe75d9110004fd75d911001cfc75d9110006bf54d9110006be54d9110006bd54d9110006bc54d9110004ff73d9110014fe73d9110004fd73d9110014fc73d91100067f53d91100067d53d9110006bf43d9110006be43d9110006bd43d9110006bc43d911000cfe72d9110004fd72d911000cfc72d9110006be42d9110006bc42d911004cfe71d911004cfc71d9110024fe70d9110024fc70d911004cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100079c63d91100069c63d91100073f53d91100073d53d9110006be62d9110006bc62d9110007b631d9110007b531d91101ffb610d91101ffb410d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d91100063f53d9110006be53d9110006bd53d91100063d53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d91101febf71d9110006bd71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf31d9110006be31d9110006bd31d9110006bc31d9110006bf21d9110006bc21d9110006bf70d91101febe70d9110006bd70d91101febc70d9110006bf50d91101febe50d9110006bd50d91101febc50d9110006bf30d91101febe30d9110006bd30d91101febc30d9110006bf20d91101febe20d91101febc20d91101febe10d91101febc10d91100657e75991100057d75991100067f65991100067c6599110006bf649911005dde7399110005dd7399110006dc6399110055ee7299110005ed72991100057f75591100657c75591100067f65591100067c6559110005df735911005ddc7359110006dc6359110005ef7259110055ec7259110004ff75591100067f75591100047f755911001cfe7559110004fd755911001cfc75591100067c755911001c7c7559110006bf7459110004ff7359110006df7359110004df7359110014fe7359110004fd7359110014fc7359110006dc7359110014dc73591100067f53591100067d5359110004ff7259110006ef7259110004ef7259110
  | 7 => 0x710024fd768871008d7e75887100057d758871000eee6288710006ed6288710025fa7088710005f9708871002cff7648710006ef624871000eec624871008d7e75d03100057d75d031004ebe64d0310006bd64d0310005f671d0310005f571d031004cff765031004ebe6450310006bd6450310005f77150310005f4715031000cff764831000cfc76483100057f754831008d7c754831000eee6248310006ed6248310005f77148310005f47148310004ff755921001cfe7559210004fd755921001cfc7559210026bf7459210004ff7359210014fe7359210004fd7359210014fc73592100067f53592100067d5359210006bf4359210006bd4359210004ff725921000cfe725921000cfc7259210024fc7059210026be4059210026bc4059210004ff7558a100067f7558a100047f7558a1001cfe7558a10004fd7558a1001cfc7558a100067c7558a1001c7c7558a10004ff7458a1004cfc7458a10004ff7358a10014fe7358a10004fd7358a10014fc7358a100067f5358a100067d5358a10026ef7258a1006eee5258a10006ed5258a1006eec4258a1006eee3258a10006ed3258a1006eef2158a10024fc7058a10026ee2058a10026ec2058a1004cff76d0a10024fe76d0a10004fd76d0a10024fc76d0a1000eee62d0a10006ed62d0a10004ff7650a10024fe7650a10004fd7650a10024fc7650a100057f7550a1007d7c7550a1006fac4250a10005f77150a10005f47150a1004ebe64d0610006bd64d0610025fa70d0610005f970d06101febf649061004ebc649061004cff76506100057f755061007d7c755061004ebe6450610006bd6450610005ef725061006dec7250610005fb7050610025f8705061007d7e75106100057d75106101f6bf641061004ebc6410610054fd768861007d7e75886100057d75886101e6ef628861000eec628861000cff7648610024fc764861000eee6248610006ed6248610005fb7048610025f87048610025f976c4210006f976c421020f7b53c421020f7953c4210027f271c42100657e76d95100667e76d951001c7e76d95100057f73d95100057d73d95100067f63d95100067e63d95100067d63d95100067c63d95100075c63d95100065c63d95100067e62d95100067c62d95100077631d95100077531d95102077610d95102077410d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100047f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067e42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95102067f71d95100667e71d95100667d71d95100667c71d95100067f31d95100067
  | 8 => 0x22f6c6548520225ee7448520225ec744852021def734852021ded73485202176f53485202176d534852000def714852000fe77148520007e76148520006ec6148520007e46148520007eb7048520025ee7048520025ec7048520007e8704852000eef604852000feb604852000cfe76d012000cfc76d012009d7e75d01200057d75d01200067f65d012010e7c65d0120006bf64d012004ebc64d012000dee72d0120005ed72d012004cff765012000cfe76501200ccfd765012000cfc76501200067f65501200de7c6550120006bf645012004ebc6450120005ef725012000dec7250120004ff75d931001cfe75d9310004fd75d931001cfc75d9310004ff73d9310014fe73d9310004fd73d9310014fc73d93100067f53d93100067d53d9310006bf43d9310006bd43d931000cfe72d9310004fd72d931000cfc72d9310006f671d9310006f970d93101febe40d93101febc40d9310004fd7699310006bf649931004cff76593100057f755931008d7c7559310005ef7259310085ec7259310004ff75593100067f75593100047f755931001cfe7559310004fd755931001cfc75593100067c755931001c7c7559310006bf7459310004ff7359310014fe7359310004fd7359310014fc73593100067f53593100067d5359310004ff7259310006ef7259310004ef725931000cfe725931000cfc7259310006ec725931000cec725931008d7e75193100057d751931004ebe6419310006bd641931008d7e75d8b100057d75d8b10086ee62d8b10004ff75d8b1001cfe75d8b100067e75d8b1001c7e75d8b10004fd75d8b100067d75d8b100047d75d8b1001cfc75d8b1004cfe74d8b10004fd74d8b10004ff73d8b10014fe73d8b10004fd73d8b10014fc73d8b100067f53d8b100067d53d8b10084fd72d8b10086ee52d8b10006ed52d8b10086ec42d8b10086ee32d8b10006ed32d8b10006f671d8b10086ef21d8b10006f970d8b101e6ee20d8b101e6ec20d8b1000cff7658b10086ec6258b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b1004cfc7458b10004ff7358b10014fe7358b10004fd7358b10014fc7358b100067f5358b100067d5358b10006ef7258b10024fc7158b10086ec2158b10086ef2058b1004cff76d0b10004fe76d0b10004fd76d0b1004cfc76d0b10006ef62d0b1000eec62d0b10004ff7650b10004fe7650b10004fd7650b10004fc7650b100057f7550b1008d7c7550b10087ac4250b10006bf64d071004ebc64d0710024fd769071004ebe6490710006bd6490710025fa7090710005f970907100057f755071008d7c7550710006bf645071004ebc6450710005ef7250710085ec7250710024fd761071008d7e75107100057d751071004ebe6410710006bd6410710025fa7010710005f9701
  | 9 => 0xd755912001cfc75591200067c755912001c7c7559120006bf7459120004ff7359120006df7359120004df7359120014fe7359120004fd7359120014fc7359120006dc7359120014dc73591200067f53591200067d5359120006bf4359120006bd43591200ccff7259120006ef72591200ceec42591200ceee3259120006ed3259120004ff7159120006f77159120004f77159120004fc7159120006f47159120004f471591200fcff7059120006fb70591200e4fe76191200067f65191200067c651912004ebe6419120006bd6419120025ee76d0920226ee76d0920024ee76d0920225ef75d0920255ed75d09200076f65d092024f6c65d092000dee74d092000fae74d0920226ef64d0920007af64d0920226ed64d0920227ac64d0920225ef73d0920245ed73d092023f6f53d092023f6d53d0920227af43d092023fad43d0920005ed71d0920025ee70d0920227ea70d0920227e970d0920025ec70d092000eef60d092000feb60d09200067f65d85200067c65d8520004ff75d852001cfe75d8520004fd75d852001cfc75d852004cfe74d8520004fd74d8520004ff73d8520014fe73d8520004fd73d8520014fc73d85200067f53d85200067d53d8520024fd72d8520006f731d8520006f431d852006ef621d852006ef521d852009d7e75985200057d75985200067f65985200067c6598520006f76198520055f970985200057f755852009d7c75585200067f65585200067c6558520005bf7458520005bc7458520005df7358520095dc7358520085fb70585200067f65185200067c6518520006f56118520004ff751852001cfe7518520004fd751852001cfc751852004cfe7418520004fd7418520004ff7318520014fe7318520004fd7318520014fc73185200067f53185200067d5318520024fd721852002eee5218520006ed5218520006ef421852002eec421852002eee3218520006ed3218520006f73118520006f4311852002eef211852002ef6211852002ef52118520024fe7018520024fc70185201deee20185201deec2018520004fe76d0520004fd76d052004cfc76d05200067f65d052018e7c65d052000dec72d0520006f761d0520006f461d0520004fe7690520004fd7690520004fc76905200067f65905201767c6590520006bf649052004ebc649052000dee7290520005ed7290520004ff7650520004fe7650520004fc76505200057f755052009d7c75505200067f65505201667c6550520005ef725052000dec7250520004fe7610520004fd761052004cfc761052009d7e75105200057d75105200067f65105201467c6510520006bf641052004ebc641052000dee7210520005ed7210520006f76110520006f46110520025fa7010520005f97010520024ec7648520235ef7548520235ed75485200076f6548520
  | 10 => 0x8620024fc7058620026ef2058620026ed2058620026f61058620026f4105862004cff76d0620024fe76d0620004fd76d062004ebe64d0620006bd64d062000dee72d0620005ed72d0620004ff7690620024fe7690620004fd7690620004ff7650620004fd7650620024fc76506200057f75506200ad7c755062004ebe6450620006bd6450620005ef725062000dec725062004cff7610620024fe7610620004fd76106200ad7e75106200057d7510620025fa7010620005f970106202876e75886200076d75886201e6ef6588620286ed658862027eee64886201e6ec64886201e6ef6388620276ed63886202776f53886202776d538862000dee718862000fe671886201e7e66188620006ed61886201e7e561886201e7ea70886201e5ed7088620007e9708862000eee608862000fea608862026d7e76d952009e7e76d952001c7e76d95200057f73d95200057d73d95200067f63d95200067e63d95200067d63d95200067c63d952025f6f72d95202676c72d95202676c42d95202676e32d95200076d32d95202676f21d95202677b20d952025f6e20d952025f6c20d95202677820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200047f73d95200067e73d95200067d73d95200047d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d952025e7f72d95202667e72d95202667d72d95202667c72d95202667f42d95202667e42d95202667d42d95202667c42d95202667f32d95202667e32d95202667d32d95202667c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f31d95200067e31d95200067d31d95200067c31d95202667f21d95202667e21d95202667d21d95202667c21d95202667f70d952025e7e70d95202667d70d952025e7c70d952025e7e40d952025e7c40d95200067f30d952025e7e30d95200067d30d952025e7c30d95202667f20d952025e7e20d95202667d20d952025e7c20d952025e7e10d952025e7c10d952004cfe76d91200067f65d91200067c65d9120004ff75d912001cfe75d9120004fd75d912001cfc75d9120004ff73d9120014fe73d9120004fd73d9120014fc73d91200067f53d91200067d53d9120006be43d9120006bc43d9120024ff72d912000cfe72d9120024fd72d9120006ed72d912000cfc72d91200e6bf42d91200e6bd42d91200e6ec42d91200e6ee32d9120006ed32d9120004fe71d9120004fd71d912009d7e75991200057d75991200067f65991200067c6599120006bf64991200cdf970991200057f755912009d7c75591200067f65591200067c6559120005df7359120095dc7359120005f77159120005f471591200fdfb7059120004ff75591200067f75591200047f755912001cfe7559120004f
  | 11 => 0xcfd7458840004ff7358840014fe7358840004fd7358840014fc73588400067f53588400067d5358840024ff7258840026ef72588400b6ee5258840006ed525884004eef425884004eec42588400b6ee3258840006ed3258840004ff7158840004fc71588400b6ef2158840024fc7058840026ee2058840026ec2058840004ff759844001cfe7598440004fd759844001cfc7598440004ff7398440014fe7398440004fd7398440014fc73984400067f53984400067d539844000cfe7298440004fd729844000cfc7298440026f67198440006f65198440006f5519844004ef7419844004ef44198440006f63198440006f53198440026f61098440026f41098440004ff75584400067f75584400047f755844001cfe7558440004fd755844001cfc75584400067c755844001c7c7558440004ff7358440014fe7358440004fd7358440014fc73584400067f53584400067d5358440004ff7258440006ef7258440004ef725844000cfe725844000cfc7258440006ec725844000cec7258440026f77158440006f65158440006f5515844004ef7415844004ebc415844004ef44158440006f63158440006f53158440026bf4058440026bd4058440026f61058440026f4105844004dbd7690440006bd7690440004bd769044004ebf639044028ebd639044028f3f539044028f3d539044004dbe719044004fb67190440006bd61904401fdbd70904401febe609044004fba6090440004ff7688440024fe7688440004fd76884400c57e75884400057d758844000eec6288440006f66188440006f56188440004ff7648440004fd7648440024fc7648440005bf744844004dbc744844000eee6248440006ed6248440006f66148440006f56148440004ff755922001cfe7559220004fd755922001cfc7559220026bf7459220006bf5459220006bc5459220004ff7359220014fe7359220004fd7359220014fc73592200067f53592200067d5359220006bf4359220006bd43592200cebf42592200cebd4259220004ff7159220004fc7159220024fe7059220024fc7059220026be4059220026bc4059220004ff759862001cfe7598620004fd759862001cfc759862004cfe7498620004fd7498620004ff7398620014fe7398620004fd7398620014fc73986200067f53986200067d5398620026f67198620006f63198620006f53198620086f62198620086f52198620024fe7098620026f61098620026f41098620004ff75586200067f75586200047f755862001cfe7558620004fd755862001cfc75586200067c755862001c7c7558620004ff745862004cfc7458620004ff7358620014fe7358620004fd7358620014fc73586200067f53586200067d5358620026f77158620006f63158620006f53158620056f62158620056f52158620056ec215
  | 12 => 0xa6010640004ff7688640024fe7688640004fd76886400f57e75886400057d758864012e7e65886400067d658864000eee6288640006ed6288640004ff7648640004fd7648640024fc764864011e7e65486400067d6548640005bf744864004dbc744864000eee6248640006ed624864000cfe76d89400ceee62d8940004ff75d894001cfe75d8940004fd75d894001cfc75d8940024fd74d894000cfc74d8940004ff73d8940014fe73d8940004fd73d8940014fc73d89400067f53d89400067d53d8940006bf43d8940006bd43d89400ceee42d8940004fe71d8940004fd71d89400ceec21d894004cfd70d89400ceef20d89400057f75589400dd7c7558940005df73589400d5dc73589400ceec6258940005f77158940005f47158940024fc76509400057f75509400dd7c7550940006ef625094000eec625094004fac4250940005fb7050940025f87050940004ff75d854001cfe75d8540004fd75d854001cfc75d8540004ff73d8540014fe73d8540004fd73d8540014fc73d85400067f53d85400067d53d854000cfe72d8540004fd72d854000cfc72d8540006f721d8540006f421d8540006f761985400057f75585400dd7c7558540005df73585400d5dc7358540005ef72585400cdec72585400dd7e75185400057d7518540006f56118540004ff751854001cfe75185400067e751854001c7e7518540004fd75185400067d75185400047d751854001cfc7518540004ff7318540014fe7318540004fd7318540014fc73185400067f53185400067d5318540006bf4318540006bd431854000cfe7218540004fd721854000cfc7218540006f72118540006f421185401f6be40185401f6bc4018540005be76d054004ebe76d0540004be76d054004dbf73d05402b5bd73d05402af3f53d05402af3d53d0540006bc61d0540025be70d0540025bc70d054004ebf60d054004fbb60d0540024fe769054029dbd7490540006f76190540006f46190540025fa7090540005f97090540024fc76505400057f75505400dd7c7550540005ef72505400cdec7250540006f76150540006f46150540005fb7050540025f87050540024bc76505400073f75505402a73c755054029dbf735054029dbd73505402973f53505402973d5350540007af7250540007ac725054004dbf715054004fb77150540007b76150540006bc6150540007b46150540007bb7050540025be7050540025bc7050540007b8705054004ebf605054004fbb6050540004fe7688540004fd7688540004fc76885400dd7e75885400057d758854004dbe7488540005bd7488540006ef628854000eec6288540004ff7648540004fe7648540004fc7648540004ff75588400067f75588400047f755884001cfe7558840004fd755884001cfc75588400067c755884001c7c7558840
  | 13 => 0x8a40006ef3258a400e6ee3258a40006ed3258a400e6ec3258a40004ff7158a40004fc7158a400e6ef2158a400e6ec2158a40024fc7058a40026ee2058a40026ec2058a40006ef7558a40006ee7558a40006ed7558a40006ec7558a40006ed7458a400e6ec7458a40006ef5458a40226ee5458a40006ed5458a40226ec5458a40006ef7358a40006ee7358a40006ed7358a40006ec7358a40006ef5358a400066f5358a40006ee5358a40006ed5358a400066d5358a40006ec5358a40226ef4358a40006ee4358a40006ed4358a40226ec4358a40006ef7158a40006ee7158a40006ed7158a40006ec7158a40006ef5158a40006ee5158a40006ed5158a40006ec5158a40226ef4158a40226ec4158a40006ef3158a40006ee3158a40006ed3158a40006ec3158a40026ef7058a40026ee7058a40026ec7058a40026ef5058a40026ee5058a40026ed5058a40026ec5058a40026ef4058a40026ee4058a40026ed4058a40026ec4058a40026ef3058a40026ee3058a40026ed3058a40026ec3058a40026ef1058a40026ee1058a40026ed1058a40026ec1058a4000cff7650a400057f7550a400f57c7550a4019e7e6550a400067d6550a4000eee6250a40006ed6250a4004fac4250a40005fb7050a40025f87050a40004ff759864001cfe7598640004fd759864001cfc7598640004ff7398640014fe7398640004fd7398640014fc73986400067f53986400067d539864000cfe7298640004fd729864000cfc7298640026f67198640006f63198640006f53198640024fe7098640026f61098640026f41098640004ff755864001cfe7558640004fd755864001cfc7558640004ff7358640014fe7358640004fd7358640014fc73586400067f53586400067d5358640004ff725864000cfe725864000cfc7258640026f77158640006f63158640006f53158640024fc7058640026bf4058640026bd4058640026f61058640026f410586401767e65906400067d659064016eee6290640006ed6290640006f66190640006f56190640025fa7090640005f970906401ff3e65906401ff3d65906401febf63906402c6bd63906402c73f53906402c73d53906401ffae62906401ffad629064004dbe71906401ffb66190640006bd61906401ffb561906401ffba70906401fdbd7090640007b9709064004ebe60906400057f75506400f57c75506401667e65506400067d6550640005ef72506400e5ec7250640156ee6250640006ed6250640006f66150640006f56150640005fb7050640025f870506401f5bd761064004ebd761064004f3e751064004f3d75106401f73e65106401f73d65106401f6bf63106402bebd63106402bf3f53106402bf3d53106401f7ae62106401f7ad621064004fb67110640006bd611064004dbf70106401f5bd701064004fb
  | 14 => 0x2ee7e20597402ee7c20597402ee7e10597402ee7c1059740004ff7558b4001cfe7558b40004fd7558b4001cfc7558b40024fc7458b40004ff7358b40014fe7358b40004fd7358b40014fc7358b400067f5358b400067d5358b4004ebf4358b40006bd4358b4004eef7258b4004eef4258b4004eec4258b400feee3258b40006ed3258b40004ff7158b40004fc7158b400feec2158b400feef2058b40004ff759874001cfe7598740004fd759874001cfc7598740024fe7498740024be7498740004ff7398740014fe7398740004fd7398740014fc73987400067f53987400067d539874004ebf4398740006bd439874000cfe7298740004fd729874000cfc729874004ef6719874004ebf419874004ef7419874004ef441987401febe409874004ebc4098740004ff755874001cfe7558740004fd755874001cfc7558740024fc7458740004ff7358740014fe7358740004fd7358740014fc73587400067f53587400067d5358740004ff725874000cfe725874000cfc725874004ef7715874004ef7415874004ef4415874004dbf7650740006bf76507400073f75507402e73c755074004f3e655074004f3d65507402ddbf73507402ddbd73507402d73f53507402d73d5350740007af7250740007ac725074004fb77150740006be6150740025be7050740025bc7050740004ff768874004cfe7688740004fd768874010d7e75887400057d758874012e7e65887400067d658874004dbe7488740005bd748874000eee6288740006ed6288740004ff7648740004fd764874004cfc764874011e7e65487400067d65487400f67f74596402ce7e74596400067d74596402ce7c74596400067f73596400047f73596400067e73596400067d73596400047d73596400067c73596402ce7f43596400067e43596400067d43596402ce7c43596400067f72596400067e72596400067d72596400067c72596402ce7f42596400067e42596402ce7c42596400067f32596400067e32596400067d32596400067c32596400067f71596400067e71596400067d71596400067c71596402ce7f41596402ce7c41596400067f31596400067e31596400067d31596400067c31596400067f21596400067c21596400267f70596400267e70596400267d70596400267c70596400267f40596400267e40596400267d40596400267c40596400267f30596400267e30596400267d30596400267c30596400267f20596400267e20596400267d20596400267c20596400267f10596400267e10596400267d10596400267c1059640004ff7558a4001cfe7558a40004fd7558a4001cfc7558a40004ff7358a40014fe7358a40004fd7358a40014fc7358a400067f5358a400067d5358a40026ef7258a40006ef5258a400e6ee5258a40006ed5258a400e6ec5258a400e6ee425
  | 15 => 0xd7418221125de7318221005dd7318221026fa6018221006f9601822104cfe76d9121004ff75d912101cfe75d9121004fd75d912101cfc75d9121006bf54d9121006bc54d9121004ff73d9121014fe73d9121004fd73d9121014fc73d91210067f53d91210067d53d9121006bf43d9121006bd43d912116cff72d912116cfd72d912116ebf42d912116ebd42d9121024fe70d9121004fd70d9121006bf6499121155f571991210057f755912111d7c755912117df77159121004ff75591210067f75591210047f755912101cfe7559121004fd755912101cfc75591210067c755912101c7c7559121006bf7459121004ff7359121014fe7359121004fd7359121014fc73591210067f53591210067d5359121154ff7259121006ef7259121004ef725912117cff7159121006f77159121004ff7059121024fc705912116cfe761912111d7e75191210057d751912104ebe6419121006bd641912100cfe76d052100cfc76d0521006bf64d052104ebc64d052100dee72d0521005ed72d0521134fe769052104cff765052100cfe7650521154fd765052100cfc76505210057f755052111d7c7550521006bf645052104ebc6450521005ef725052100dec725052116cfe761052111d7e75105210057d75105212ff6e75885210076d75885212feef65885212feed658852127eee648852127eec64885212f6ef63885212f6ed63885212f76f53885212f76d538852100dee718852100fe6718852100eef618852100fe76188521005ed7088521004ff75d812101cfe75d8121004fd75d812101cfc75d812104cfe74d8121004fd74d8121004ff73d8121014fe73d8121004fd73d8121014fc73d81210067f53d81210067d53d8121086fa20d8121006fb60981210057f755812111d7c7558121005bf7458121005bc7458121005df7358121115dc735812111d7e75181210057d75181211e6ef6218121026fa6018121006f9601812104e7f745974004e7e745974004e7d745974004e7c74597400067f73597400047f73597400067e73597400067d73597400047d73597400067c735974004e7f435974004e7e435974004e7d435974004e7c43597400067f72597400067e72597400067d72597400067c725974004e7f425974004e7e425974004e7d425974004e7c42597400067f32597400067e32597400067d32597400067c32597400067f71597400067e71597400067d71597400067c715974004e7f415974004e7e415974004e7d415974004e7c41597400067f31597400067e31597400067d31597400067c31597400067f21597400067c215974010e7f70597402ee7e70597400067d70597402ee7c705974004e7f405974004e7e405974004e7d405974004e7c40597400067f30597402ee7e30597400067d30597402ee7c30597400067f2059740
  | 16 => 0x96210067f70596210067e70596210067d70596210067c70596210067f30596210067e30596210067d30596210067c30596213267f20596213267e20596213267d20596213267c205962112d7e75d92210057d75d92210067e65d92210067d65d9221125de73d9221005dd73d9221135f671d9221004ff75d922101cfe75d92210067e75d922101c7e75d9221004fd75d92210067d75d92210047d75d922101cfc75d9221004ff73d9221014fe73d9221006de73d9221014de73d9221004fd73d9221006dd73d9221004dd73d9221014fc73d92210067f53d92210067d53d9221006bf43d9221006bd43d9221006ed72d922116eec42d922116eee32d9221006ed32d9221134fe71d9221006f671d9221024fe70d9221004fd70d9221154fd76992210067e65992210067d6599221006bf649922104cff76592210067e65592210067d6559221004ff755922101cfe7559221004fd755922101cfc7559221006bf7459221004ff7359221014fe7359221004fd7359221014fc73592210067f53592210067d5359221006be4359221006bc4359221006ef7259221156bf4259221156bd4259221156ec4259221156ee3259221006ed3259221004ff7059221024fc705922112d7e75192210057d75192210067e65192210067d651922104ebe6419221006bd641922116df6711922127eed76d0a2127def75d0a2131ded75d0a213176e65d0a210076d65d0a2100dee74d0a2100fae74d0a2127eef64d0a2127fae64d0a2127eed64d0a21007ad64d0a2127def73d0a2130ded73d0a213076f53d0a213076d53d0a2127faf43d0a21307ad43d0a2127fe671d0a21005ed71d0a2127fe571d0a2100eee61d0a2100fe661d0a211e5ee70d0a21154fd76d062118e7e65d06210067d65d062100dec72d062100cff769062100cfd76906211767e65906210067d659062104ebe6490621006bd649062100dee7290621005ed729062117cff76506210057f755062112d7c75506211667e65506210067d6550621005ef725062100dec725062100cff761062100cfd761062104cfc761062112d7e75106210057d75106211467e65106210067d651062104ebe6410621006bd641062100dee7210621005ed721062112d7e75d82210057d75d82210067e65d82210067d65d82210067e65982210067d6598221006fb60982210067e65582210067d6558221004ff755822101cfe7558221004fd755822101cfc7558221004ff745822104cfc7458221004ff7358221014fe7358221004fd7358221014fc73582210067f53582210067d5358221056ee5258221006ed5258221006ef4258221056ec4258221056ee3258221006ed3258221056ef2158221056fa20582211e6ec205822112d7e75182210057d75182210067e65182210067d6518221005be7418221005b
  | 17 => 0x4e7c74594410067f73594410047f73594410067e73594410067d73594410047d73594410067c735944104e7f435944104e7e435944104e7d435944104e7c43594410067f72594410067e72594410067d72594410067c725944104e7f425944104e7e425944104e7d425944104e7c42594410067f32594410067e32594410067d32594410067c32594411467f71594410067e71594411467d71594411467c715944104e7f415944104e7e415944104e7d415944104e7c41594410067f31594410067e31594410067d31594410067c31594410067f21594410067c21594410067f70594410067e70594410067d70594410067c705944104e7f405944104e7e405944104e7d405944104e7c40594410067f30594410067e30594410067d30594410067c30594410067f20594410067c2059441004ff755884101cfe7558841004fd755884101cfc7558841004ff7358841014fe7358841004fd7358841014fc73588410067f53588410067d535884104ebf4358841006bd435884104eef725884104eef425884104eec4258841136ee3258841006ed3258841136ec2158841004ff7058841024fc7058841136ef205884104dbf7650441006bf7650441004bf76504410073f75504413373c755044104f3e655044104f3d655044134dbf735044134dbd73504413473f53504413473d5350441007af7250441007ac725044104dbf715044104fb7715044133ebe615044104fb66150441337b65150441337b551504411f5bc7050441004ff755804101cfe7558041004fd755804101cfc7558041004ff7358041014fe7358041004fd7358041014fc73580410067f53580410067d535804104ebf4358041006bd4358041004ff725804100cfe725804100cfc725804104ebf4158041006bd415804104efb705804104efb405804104ebc405804104ef84058041006fa3058041006f9305804132d7f765962112e7f765962101c7f76596210057f73596210057d73596210067f63596210067e63596210067d63596210067c63596213276e72596210076d72596213276c42596213276e32596210076d32596213276f21596213277721596213277421596213276c20596210067f74596210067e74596210067d74596210067c74596210067f73596210047f73596210067e73596210067d73596210047d73596210067c73596210067f43596210067e43596210067d43596210067c43596213267f72596213267e72596213267d72596213267c72596213267f42596213267e42596213267d42596213267c42596213267f32596213267e32596213267d32596213267c325962112e7f71596213267e71596213267d71596213267c71596210067f31596210067e31596210067d31596210067c31596213267f21596213267e21596213267d21596213267c215
  | 18 => 0xf20d8941156ec20d8941155ee76d894100cee76d8941006ef65d89410076f65d89410066f65d8941006ee65d8941006ed65d8941006ec65d89410076c65d89410066c65d8941006ef63d8941006ee63d8941006ed63d8941006ec63d89410076f53d89410076d53d894127fe741d894127fe441d8941006ef75d8941006ee75d8941006ed75d8941006ec75d8941006ef74d8941156ee74d8941006ef54d894127eee54d8941006ed54d894127eec54d8941006ef73d8941006ee73d8941006ed73d8941006ec73d8941006ef53d89410066f53d8941006ee53d8941006ed53d89410066d53d8941006ec53d894127eef43d8941006ee43d8941006ed43d894127eec43d894127eef71d8941156ee71d8941006ed71d8941006ef51d8941006ee51d8941006ed51d8941006ec51d894127eef41d894127eec41d8941006ef31d8941006ee31d8941006ed31d8941006ec31d8941006ef70d8941006ee70d8941006ed70d8941006ec70d8941006ef50d8941006ee50d8941006ed50d8941006ec50d894127eef40d894127eec40d8941006ef30d8941006ee30d8941006ed30d8941006ec30d89410057f75589411657c75589410067f65589410067c6558941156ec6258941005ee7618941156ee7618941006ef65189410076f65189410066f6518941006ee6518941006ed6518941006ec65189410076c65189410066c6518941006ef6318941006ee6318941006ed6318941006ec63189410076f53189410076d531894117eef6118941367e74118941367e4411894100cfc76509410057f75509411657c75509410067f655094119e7c6550941006ef625094100eec625094104fac4250941005f77150941005f471509410067f65905411767c6590541006ef629054116eec629054104df6719054104ef761905410073f659054135f3c6590541356bf6390541356bd63905413573f53905413573d5390541007af6290541007ac629054104dbe719054104ebf619054104fb76190541005bd70905410067f65d81410067c65d8141006ef62d8141006ec62d8141004ff75d814101cfe75d8141004fd75d814101cfc75d8141004ff73d8141014fe73d8141004fd73d8141014fc73d81410067f53d81410067d53d814100cfe72d8141004fd72d814100cfc72d8141006fb30d8141006f830d81411657e75981410057d75981410067f65981410067c6598141155ee7298141005ed7298141006ef6298141006ec6298141006fb60981410057f75581411657c75581410067f65581410067c6558141005df735814115ddc7358141005ef7258141155ec7258141006ef6258141006ec62581410067f65181410067c65181411febf6418141006ef6218141006ec6218141026fa6018141006f9601814104e7f745944104e7e745944104e7d7459441
  | 19 => 0x8341004ff725834100cfe725834100cfc725834104efb705834104efb405834104ef840583411757e75d8a410057d75d8a4114dde73d8a41005dd73d8a4116eee62d8a4100cff7658a4116eec6258a41004ff7558a4101cfe7558a41004fd7558a4101cfc7558a41004ff7358a41014fe7358a41004fd7358a41014fc7358a410067f5358a410067d5358a41006bf4358a41006bd4358a4116eee4258a4104cfc7158a4116eec2158a41004ff7058a41024fc7058a4116eef2058a4100cff7650a410057f7550a411757c7550a4100eee6250a41006ed6250a4104fac4250a41005f77150a41005f47150a41005bd76d064104ebd76d064104dbf73d0641385bd73d064137f3f53d064137f3d53d064104fb661d0641377b651d0641377b551d06411fdbe70d0641006fb60982410057f75582411757c7558241004ff75582410067f75582410047f755824101cfe7558241004fd755824101cfc75582410067c755824101c7c7558241004ff7358241014fe7358241004fd7358241014fc73582410067f53582410067d5358241006bf4358241006bd4358241004ff725824100cfe725824100cfc7258241006bf41582411757e75182410057d751824114dde7318241005dd731824116dee7218241005ed7218241026fa6018241006f960182411657e76d95411667e76d954101c7e76d95410057f73d95410057d73d95410067f63d95410067e63d95410067d63d95410067c63d95410067e62d95410067c62d954136f7741d954136f7441d95410067f74d954136e7e74d95411667d74d954136e7c74d95410067f73d95410047f73d95410067e73d95410067d73d95410047d73d95410067c73d954136e7f43d95410067e43d95410067d43d954136e7c43d95410067f72d95410067e72d95410067d72d95410067c72d954136e7f42d95410067e42d954136e7c42d95410067f32d95410067e32d95410067d32d95410067c32d954136e7f71d95411667e71d95411667d71d95411667c71d954136e7f41d95411667d41d954136e7c41d95410067f31d95410067e31d95410067d31d95410067c31d95410067f21d95410067c21d95410067f70d95410067e70d95410067d70d95410067c70d954136e7f40d954136e7c40d95410067f30d95410067e30d95410067d30d95410067c30d95410067f20d95410067c20d954100cfe76d89410067f65d89410067c65d8941156ee62d8941004ff75d894101cfe75d8941004fd75d894101cfc75d8941004ff73d8941014fe73d8941004fd73d8941014fc73d89410067f53d89410067d53d8941006ef52d8941156ee52d8941006ed52d8941156ec52d8941156ee42d8941006ef32d8941156ee32d8941006ed32d8941156ec32d894104cfd71d8941156ef21d8941024fe70d8941004fd70d8941156e
  | 20 => 0x3967e42d95423967d42d95423967c42d95423967f32d95423967e32d95423967d32d95423967c32d95420067f71d95420067e71d95420067d71d95420067c71d954239e7f41d954239e7c41d95420067f31d95420067e31d95420067d31d95420067c31d95423967f21d95423967e21d95423967d21d95423967c21d95420067f70d95420067e70d95420067d70d95420067c70d954239e7f40d954239e7c40d95420067f30d95420067e30d95420067d30d95420067c30d95423967f20d95423967e20d95423967d20d95423967c20d95420067f65d85420067c65d854217fac42d8542004ff75d854201cfe75d8542004fd75d854201cfc75d8542004ff73d8542014fe73d8542004fd73d8542014fc73d85420067f53d85420067d53d854204cfd72d8542006f631d8542006f531d854217ef621d8542024fe70d8542004fd70d854219d7e75985420057d75985420067f65985420067c6598542195de7398542005dd739854216fac4298542006f761985420057f755854219d7c75585420067f65585420067c6558542157ac42585420067f65185420067c6518542137ac4218542006f56118542004ff751854201cfe7518542004fd751854201cfc7518542004ff7318542014fe7318542004fd7318542014fc73185420067f53185420067d5318542006bf4318542006bd431854204cfd7218542366ef4218542136ec4218542136ee3218542006ed3218542006f63118542006f53118542136f52118542024fe7018542004fd70185420067f65d81420067c65d81420ffac42d8142004ff75d814201cfe75d8142004fd75d814201cfc75d8142004ff73d8142014fe73d8142004fd73d8142014fc73d81420067f53d81420067d53d8142006bf43d8142006bd43d814204cfd72d814238eef42d81420feec42d81420feee32d8142006ed32d8142004fe71d8142004fd71d81420fefa20d814219d7e75981420057d75981420067f65981420067c65981420e7ac4298142006fb60981420057f755814219d7c75581420067f65581420067c6558142005df7358142195dc73581420cfac4258142005f77158142005f471581420067f65181420067c65181420b7ac4218142026fa6018142006f96018142004ff7558b410067f7558b410047f7558b4101cfe7558b41004fd7558b4101cfc7558b410067c7558b4101c7c7558b41004ff7358b41014fe7358b41004fd7358b41014fc7358b410067f5358b410067d5358b4104eef7258b4117eee5258b41006ed5258b4104eef4258b4104eec4258b4117eee3258b41006ed3258b4117eef2158b41004ff7058b41024fc7058b4117eec2058b41004ff755834101cfe7558341004fd755834101cfc7558341004ff7358341014fe7358341004fd7358341014fc73583410067f53583410067d535
  | 21 => 0x3006000000600a00000000020000000004006001001003000e00300000200080000030010016002001000800c006000000000000f0040038004009001800000000b000001c002000000800800200d00c000000000900000040060090038024004005000000000200a000000c01200000180c8002000000000408e000000002402a0060018010000004003802000600b0028004036004002005000e0010000004044034001801c02a000003001000600a0008000006023001800000a0000018018030000000000000200c00b80040000020000004004000003800000a0260028004000001001800002c0000040014002000003000000000300080040000070000024004042003801000a002000800401000001400000000030040004012024003001c0080200000024004000000004401600a004001002400800300000140000000004014000000007400c00a000001c000010020801400a001009000000e00000380040000000038004014024003800400e002001803400a002000000c006000002000c008005001001c0080010018020014002000000c026003001000c00400d0088040006000001002c0140000028008020002004ff759874201cfe7598742004fd759874201cfc759874200cfe7498742004ff7398742014fe7398742004fd7398742014fc73987420067f53987420067d539874204ebf4398742006bd439874204ef6719874204ef7419874204ef4419874216ef52198742024fe7098742004fd7098742004ff75587420067f75587420047f755874201cfe7558742004fd755874201cfc75587420067c755874201c7c755874200cfc7458742004ff7358742014fe7358742004fd7358742014fc73587420067f53587420067d535874204ef7715874204ef7415874204ef44158742156f62158742156ec2158742004ff7058742024fc7058742156ef2058742004ff755834201cfe7558342004fd755834201cfc755834200cfc7458342004ff7358342014fe7358342004fd7358342014fc73583420067f53583420067d535834204ebf4358342006bd4358342004ff7158342004fc715834204efb705834204efb405834204ef840583420cefa20583423a57e76d954219e7e76d954201c7e76d95420057f73d95420057d73d95420067f63d95420067e63d95420067d63d95420067c63d95420073f43d95420073d43d954239f6f42d95423973e42d95423973c42d95423976c42d95423972c42d95423976e32d95420076d32d95423967f74d954239e7e74d95423967d74d95423967c74d95420067f73d95420047f73d95420067e73d95420067d73d95420047d73d95420067c73d954239e7f43d95420067e43d95420067d43d954239e7c43d95423967f72d95423967e72d95423967d72d95423967c72d95423967f42d9542
  | 22 => 0xc0008001007001800400a002000c0080020008008004000000000c012001000800c000000001800000a002002000001c00b0048034004001001005c01c000000000000400800500040000020048004004000000000000001b003800c056001000000c002000003801c0020050000004008000000000c00a0020060000000000000000c02e019000805c00200b0008004002000000000801e00000000480060000000028000006001804000200a0088000004000000801c00c001004000000a0100000004004008006000000200900000740000160080000000012003003800400c0040014018004001000400800600080580000080000000018019000000800c007005000400e000008800002000900000080000000000000014000003000000a001000000400400100600000000060000000008008000800400200100580140060050000004004000003004c0020000030074000030000800000a003001800400800a0010008000001001000c00000500000180160170030008002009000803c01a0020070040000017002002401400b000001002e0050028014000001000000801e000002000400200600000000020010070008002001000000000000c00000b000c00400100680020220060000002001002000001000900180040260010020028004004000801401a00100000480200020038074026001000800400c000001000000a00a000800001c0000000000000006002802800000200300000000000078010000009001000400a00000900140400080000000018008003000c00a00301c000c010006002000401000100d801402c0020000008004000000002001e00a00d000c0040070058050000002000808400200100980000000030000000016000007802000001e001800800c0000000008018000000801c00a000005000000000000000000020050000004006004005000000c00200f800800002a003001c004005000007000800100080000000020028020012005000000c004001002000000a009009004801401a003801c004002014800401000c00100cc0020010098004002010001802000000900200140000080018078000002001000001c00400900040060090040014002008000000401200000480000060020018000002003000000c000013007800400200100d00000080030008018000002008801401e0020020004002000000800c01000b002000c00200700100040120000000010002001006800000e0010018018018013002000800800600b001000000000480100000080000000004006000800000c005003000800200f000000001801a005002c02600000280000400000040000000001005000002000f00b800c00800000300040060040020000004006003000001a00100b804c00200e002000c06e007000004804000
  | 23 => 0xe626f00000016623853e30000c2e1bb0003294a4ee6100037c917ea853f087f40000005c526f00005904c88f880003cb2f098942180002ca00c568682603608c0a9c4e55642d9c0006022c4a870f1800028cb4cd9461cd7210000000c880e30a880000002c538a850000000018ad6985233a6a61c0001303a0b0100000000000001b5e97300000012e8bb645936e14ba5ce3d593fcd5857057302c97b4df84c184490ceac213691f8c54d5a64b9fb8c066d63e29e44422a530002e11496a0f70fadd108a01e585b32d8f803f4ab29f96c40000000b4416e2b53559274b9000024b2b700000000001a4046e0000000da83a6761000193000024642f1ba02d60000c72cd800000003880009c2dba00025101da00000022f8c740c0000202517400006e000004ad073539c24ac60622be18f85a62d724317a80004bb00000000007a72698b7886279800000007a8b5937d000000062e59d0001a1cdcd2c131191cc00020ba791a765b402512c99c8000371a904be61b20002f2cf50d366340400942000663800045000038720f000088e378a23c000d4100000000000005be271c000a2f5a515b0dea8144ffa1f5af23de0000000000d500001a457400000000000fe000065794a5c260003772ad1ba64790000000e0c0000000000866ccf00034699c033b17100018e6904000400200a001800400a00500080000220010038018004000000003c01c00f004000800000400000a80000060000000016000004800c002005000005000400400480000020000080004014005000803000000100000300080000010000006004002800c012000000801c00a00300400a8024000000800c000000018800001200000200080340060048014008008005002001600300c8008018005002000c000000000001801e0080078010000022000000c00e000002801001600000d8080004014008800801001e000000400001e001000403600d0038000002003005001800c00400000240000000000010004000003000400000400080000040020000004018000000000c030000000002400200600000000020000018018000000004800001400f0088008006027002000c01e00a00000040000000038088000003009001403c00c004000c0060000000000004002003002000800a000000000600a0018034000000005801000000c0030058024004005001c07400c0000014000012000000401e0010038024070002002800c00a003000803c000000000001000001200280080000010018010002002000807c004002002003800000301a003800200a001803000400202d803400200000180080180000068008004006005000c010001003000000a00000180080000000118090000000000000800000a00600000040040038074008000002001c000000008000400002400080
  | 24 => 0xe4b4f8a40c7a292167430c7f325d12a85ce66038907741eec090dd16140008890001bf4f7ac7765b12bd892cfe2158000000000430000000000000018900007d600033e59dedd91a1a59c00084940f000076a3100fc2e6c76000000000000003812310000000bba0000f49c70000179800000059167a23e82ec5f158c1d4c70cd2e2598d00af46c4000202c0000000000001324ced05134a8b4a9e3000182193ea476e8800000000027e1068a5a00043aaa70b4091f00035ad4bec1a00008203a4a5e08980017040004b793e8e5468a10a07001b28ec0db07d00000000000001ace7ef4bba08091874932a8ab1c7cd9a6d10c1178843217bb5b5a00ac04072a44b969c817d02600c826422a1a184c631c17e16e4c323c422b045c906abd4a780006f20f8138ac28c348741709ce92b246400004510fc3a50e717e865a8151679114a348f04340384930627290800000008d2e1a24dc1a58614780019400004bd329d206a6e25b0a65532dd827c2ac50aa0000000000c768bb0000001b960005fa8000dc482525e319d7be00861200002b64d02dd80000000000002b613646a51e8000035a000145a28524266a46fb0e4ce8792000000038aa2c00037057fe2544a19d4884c0f26f0ab0c93ca160c8025c2081ec5bbaf5c8384c55fe0000000d511f3b6b9b80000076293d1d49bf347acf4550bb400029b59500006d480edb2cbec0c99e5dc8278919130d8e1674b0000000eb800044e0000dcc00070c00002665310da2dacb9203737d8000000cb372432a8f485420000b155d6a822b386118d66de0078588e440190a82ba457e3eb3ca8978d1007d2f42234828a875622dd91904a75c60ffc0e4da516183559742a50f51428cfe370493b58497c00058f36800006c80ca1350f3e28d40504e800030957a800036a17d340811427cbe337b39344ec00033432c0a8036e22880001ce9da00000000003af0003954a9a00000000000004eb00022296549d36ad8001b0432552e202156400000000000000002378001c00b236a3a69400077051200017ee9cc45400b08429c51f696353ce3bf20c000172c7542d40000000b794ee08d417200014980006606ed00e0000000ca400000001d43b600031c8000000203017584acdd5a200013d0b25502336ce2618366d1afd70cbd10421ea93c44d1692939023abf31cdb7dd9587b12981ff90ae7ac5441a4cb586851f50521a7400066e38e800060136e04180000005271415bda0000000000f4a0000000001c5c94100006b8c281642f59a680000eb6de02085dabc05dab08d7b853f38624b96a00001778670000b6c42c91001409f42211211b6e67e677000196a00013418012dccb94d613194426943ea89b024a41519f2594066000000166c2324de39f1131334a8a5c71b74e46a0000001d4b4c63635d18791
  | 25 => 0x75c0004ba83a54106bb43d80018f66316e39ee80006a452b281cfe80006462685b2856b1391e1d4ea0004eb800188400064333d400055f1270e640000005b7266ce1089a4f30000000000000000147600057d1d940000000001c28d6800045a000000054136d80000003e847105bdc5aca95349e0129a6635ec00c05529a92eb96f80002345b1a4f00780005608001158b7f000000114a9ea6c019640121ef5528000000c22393b728b1068e428af812626d71cb27a57e281213802943cca4a64b0001668aac4c49309122000087a3953b0cb8209a069b7e1185d430182be04912c1af870e17851f8d9ceda8880d081556602cb4268a98000c9d0001774708cc90001c1c0000001803260b54df34500000000066078b3d902e00000027416be000401964c26800000d0000000c8764990a49da74e6b41f79c367461dcb70c7768ee647b21503a19e6759969ae2e3738222c58403c557b8e79bd0d3d3e20d7c4d6c8261a3020000c16469810cdce7ca2ba241c5b20616350b71234870202b85017eb8b31010bd7f6b122f2304d2443022b4b384d32db5465800000093d46312280000000003334eb43620fc8000000c0025a000103029459129f40000000642c1456862d1a400000820006019cd0004000000000000048117a97b4636b034f914a1224dbb14e91b4f06536688196c3cebaa46c8455832d1f47380014807ae00034aca58c0e000000000077c00027f84a643619c08891c0c9a100b88089052f5490b80c7a19f64a14ccee82260092ad4a2e0004139794f52b603ca0001b7a000000204112cb0e3a6193cca68226f58af57c416d1af30740000000003580598d5660c251c2d42b700000000000002cd1ff15c498c2e0b6c800000000000016ba502000219000000053b0fdd692dd400009091200000000000000a30000000172024038b000000040f6d680000000002e68e4c000ad100001a40002835d600019fa8811a50001530000000000075437333c959812400071a0f20000e440002940000000000000000000000000016260500000001794000000000044e0000c48001392cab3ec1f8d2faa2a570968c00094c27620e8000000000000109000050493e4000333261800157e0000359de94d0bb34c83888a64d6f6939e741140004402ee09ec1ac5f696c803e36308508e8de8b294958000ed087968636540006974e59e2060c4881bd800000000000000000000006d3800000000000000000000001d62dc1310bfe1d319180000000000035b200002b780001fa0fb000000027e1e20003424000000557ab6598c0006aba481ac6a3d5de09ec6ec88c3a51e65742000032841c0002f06d2235441c9c10003978000000638910d79215d68a2454f8641117db534426684674988cb483c03671154aae3083148c3485041063c27651ba6923
  | 26 => 0x36254c24954cf93240000004f9aa9800000000000000008de00000000000002aa31744948aa57228a59ac00000016c55aa99402c0e380000002ae1d8800000035b85f030400009638101320003af86e013454c2439b0d9d48ce00000009cc1af000280c0003d50002f14f6cdef63700000000004e000014c87f770925254ce000368943c000c171078001c2063369a93391e2a3313eb7701a6d29227800000047a0000bad6dece20cb0b381b06a325290f8c2071e1608470eac1d81e5030d9f8d13360184531649c3948000efa2f435b2a3d5e668b5a7b39d1b0dde1229201a1acc000027e081c90a06490492329f73d9808837a1cf38fb575a8452262fa83972872d717b5388b086e3b3000037c8ff0f71770000d43000000000000062b912467237c21cac243ee18b0589c912a2b474682735738000000310530806d0002e68000000613b77c7160001162494000b972fa8001a423bc1080e00ef64a23d0038c1ec5082d9af9879cd8745193d0e3a8925d7a9cc2e20006af84340000005ac201c00061500000017868ae6e821e11b8aff12617542f44fb2d7965933c54807035b0f465f2480a2f570ec123700e900f225d2892d099d8b1c2861ced7f449436ca831a1e516026b195c58173130b3fdad4d8d1edb61828628766538683ac2f96468668000e1d16d00004f4c1119aae0c3b65c42150e0d2ba8ed38d03bd2006f72299b342f619d0781c0826c36444e8459bb49e52fc9b413bcd3c6c2a5416a297e005b2000de3165ab21f08d4ab604300005ec4c44e31ee179eb2f3fd9208122afd00032ed1ee7183878151aa6a555c92be526c9142120810cc800052932c463e64d11f0c80dc83c70d31a605badaa2f4b41918443000031a4198000206acac000dc54298f34c8800000004a99a63cf131138d45a50400036107ba0006ff000149060b00035d854009e0e61abc00e58e3410000e8e3ab6781d400000000001ac8b78de55d2000152a00000014ac00004658b848c562aa300022bd74c282000109c0000000000000000b3b000000118a00072037e40001580d9aea40000002492d18eb67f80002d0160e33229300012bc0001a490edb18000000154cf1c0760000001a6e00010b80017f2425255b7c0000bf00002995596000000106c0000001a2a4a0000a9f28c00000002b32c90a8d9f484342700000004b76d08ddda3600000000000001f64d00d38cf84ea50100000e88364fe0000000dc418e8000bb0aaa0949371058bb757a3270000a971aaa2658b84d218982315a8239119804c99022f07f0e2197870d2339141046d7429d82b0c6ebf259b800029e0000002ff572a0a65140001080195414a160a0c0110000001c8678f44d806054e56e183a30c3189c40002d381020004b1094462e74455700d03b446b569850943ac026510001
  | 27 => 0x1b66000515b4b027621c0002cf83a0000000000000000000029605368ca0000c393e06350001da403613253faa6cce454f17f8880bf04910fda5e48c01e118c0db1394b8041c8000000ba200034648d8a5732029e4f7c9eb5232b1d5d400030ea87dac4a8e0000000d6acf261326c091cdce3de092d5163f23ae82cc0000c56e783117607485220c495be00052195640004662e2899951a0001da005c00085b6d62da40be00026d881d1f84cd5430000ac40004dd8000000e3263f8000020000050a158556c5a051a944e8a1b11818fbd43064105f000000037100000016ca00000005d1c480631c88c6430ebad7198cbcdde0d4000122cd5461300031d0edc2cd2112c919b202431fa9ad2307dd00007655e20003ea1c04b6a8b71ac1ae1a02000244a0dc94c11e0d0382c7c0555119091054214728f1595a5e7d33bb9d8d2e41464a43894372be1567a03108ede95379970d420000000dfd18057500729d0576c2b0b380000007af2819f21be86f8659214958a2504efb8047c873d72d0ef5afca26358316dbd42c012b13a163e47d043935800000000023f800048f0001ff40004fd61ea478000af2436016d2cc0003312554000cae00020f87280002bfa7500009230000cd00d4c9b00021300000e60000001c2cc59000362ce66e4e0e21eed0840006719764eb2e492480a90bb496416485a40007ea3108001076000000063c00077628986447fa9ee0200000000c3f00035b800098d32f0001a2400000013c12a406800000018986da1cc0cf000019b4ad00000000000000001a6400022529302c021b55432100000006e3095c000ac90482dec00000000028d4ffe0000000000ad4e5419d1e988f09f61bf000000070328491edb56648000320400000000031002166d513a800173253700038ad03835a1a9000004e27f000000193c00049200009eaa1143500009e649737080018ccbdb58e80000000000000001816c45513a09100c0004f88545bc87e83b5932c0000001cd38855d860a1328000a54000000146d4347ad1ff10244ce3a143100001f4b523ed80007500d10000b98174c9934382580b46fe7132d6c138dbe195acb80000bd00000000000003b991d543c0003a880010e415300006a92b8bc25881f4510682101500000000000000e5cb74a706081bb16da12f6aa80000000000000000000d6420f32b40009570002f300004d56beb42cbee905066aef47cc3f954635e157c21672925e0000d266ffa52d50239d6f0000000037d00000011e4b640c000015ced4a00029f0000772011a17c7820001128000f040002c5a9dc9be3b16cdaf5142a1f554b2c200008d656b077da2c0004b68d35ab887600000000004d700007cd5446d24fe800185893b6c88e800000004188585bf409d01c800000000033c22180006ea0fe00008328cc
  | 28 => 0x752d282c00000032b800000047300034709b06f00002f18c7208863a800166a88400000017567201b58dd4b70e3c0002a50cd60006c51268aacc3b1ca944081879c459a110d8c7574ad80b55561970000000000b040000c99444b1a5f501490e20000000ff0000aa0161372000000000000003d669555b999c2bc06e00006205b06c147cadc8250bc81f72ae88e01f16a000002442b92a300019cc90c1878368e4aba70239944000b152308bb8e6297122227bcf0c005220a509990e355cf20e126a29a4cc947ce5e93808702913c260e5ee9830570e580052da127455a53505a0ba859833b971d63651c309000126091d09e02bcc362063512614000a2e6cf037d34e00051a1928fae6691b4000164e36653d0570e2290957725f0d402e460616780004353f8800000000018a00007040c20001728442d9f00032384d4b325bf11a1c6cc430000dc90260000e8a2900001f200037d8000ad0000000134c00000001385b63be4cba2e0bdc8c709890b80000003c826e5b4c5fc04da6cda44000101ad5c0009d10003409a500d74843515b260001b680000000006270001642c2100009e400000000000006144012501ce18bc69d6b9377400000000018580000005092cf000000000022550665a1000000000000000000002400002bc000173ad4f672b511c32a5b30215c8e58000000000000000000000009609ba00020d40000b80571dc418200062a86fc8682e30b915113449682548500324be708282acf4258027482c000000000000000000000d220a1b100001db840c00050b04ab4113f27f511b30f0bacb5c090ad2000000000000000000002df8000000e0839b21696507fa6eb0f4d5bc15408d0c8cb32e45278a7082f277937f8a0489a9ce3f621fdc1e28565a207d31c4025700cfd2c6a3c3c999084e800028a33ed6e2547126b85d16ab3937c8c319125d10000530a2a80533d0f0947cc91025ae140002ba2b69cc00000004c100010320000000000f845f062b0b196580000000000d98a320000001a22ddb000228800000011e1f6400000046919b000005c267a5fca1a0002e30001cbedb63828d090c258f11c15417468463112fb8400db92ef12b460acd74dc1b157a645a3b630a492648d464b12c00071b42583754c60c70002ee46de00052683794c40001431f045a883f1ae898183c14e2d10fd834600c0000d6544a0005cc0a38c641a50002a857d2b1100024b142820c1d1860525441d00009f04569584558f3125275e7183480f9e085000051438e0562102f798e080d00022e47c66c96009ac50f45ef0e09dd54620730aa80003ae0000003830f9ca6c4d59cf0000a3858000000008502119cfc5d80b416b2311a46a0a5c7b66400023d000000087e0001ce0fcd7825c005e1578000adb6c918e13863f40000000492b7d1d4901
  | 29 => 0xc08000147010a11cba000000389d5ae00000000011608041e30965c2a0a700001edc728bc6a580000009b60001f0000058c399072c95c00025619cc2ee671725868946e0002d3ad547f41b722ca0056f0000017b0c8f2c6b30001f884dc63c3b7994159c3d800000000002d268500005640045d8b07c0001ff0003579a3c0000000f5c0000000000000f9a877000000000000007e000000023b5c09c840002430000a21bdcd1812380000009ec63f30349c400000000000000001fa85fd3f6d304b81af1b60649010800110a6ae4328001570db17148970000a061450059b3a00000000000004fe65e98140005ff000100c00040b63ca57cc0c0f4571b1485202bc52a10200905e3000000035000000008b586a000000000000089f00023840f8a4557439703521e300000017e83470000da469650e114a4445aa29538b907d22c24854493652c27371a6179dbd8d3910f9aa5a70465041a03d28053500006299a43311dc165d8da98a00000006aec5868ba5d834eaf032f9fa43c096c14f9ca1484c3a4d720a9c7e7191348000c1e4da14f0001266a9e00000005940004d896dc000cc154238a0dbe67d2e9831800000072800a16a80006323748d1891b436800047e49f41e80007b20007251bcd2a65775f2055c7ca6432701e05c1c2f26aca61800011100010e800000000000c92380003b00000000139079a6f406a0000131ce4a720000001f480000000000000000a900000f7d8c69814d79ed0cec656602a1cc0000002b20001af88f468ead4c0000e26c0b34029acbe57e075400047609b84d4000b1600031b0dca16638000000003d11bd314d05e00000025ed9d007f6311f1c6a606742780013ac15954012d5152141084000071800000000014e400000023f49360003698e2811cc4d59302246e835c0000a7000053e00000013ba0003fb02d80402b03bc229800062c4d50a4859022e0e40000df89b5000000147400000023a1604b7a0f2a5a971025a723813db98c15556a7559e64b165ba3901527cc57d981c42a85c10cb93061602e08080015f08f6000000000054b0001ae561e00014b0001aee11029a09540f00006f132fcae2cf1000000000000059c2d7800000006738440003010001f90b605ab0000d418de000049a5ad7a400000002500000004013309828ada01c2accdd62ad00000000000000000fc4950a014d4000199c3110a902ec1ac0002318001c0cb0c4cc324000031a0f48e48b020000001e1098e00000035e927c6bd0000000000c5000024b54b20004349d9cd000002c3b594b6c92f0bf080927278d6fdaef802a07e5ec8869866e0938a2aa521e1021059bc87865fb6f3252928c0000ba8001ca6d520e4b55024cadd47189f969a6476ebafbcc8a000000036c5a059529e0000e8035139a80000003295e720450947e
  | 30 => 0xe96feb03cabaaa76ba941d90654a0001560236beb32c38c57aa000617315171abd633800010de16c01d29e000045f34b00011ae2af70e2881814634400032cfa08fb69f9a78cdcde771d87a19866613a1306cf3c38929d3981888755684058daf600000000015983656a488153384b910c2654f342090ea313c21292622e00000001994c9958007c98f3df8fe14369321279c98f0a5115c49dfc3bc5ae3d12435b3813d2b985595fc4992bd8d3d4f6b663bf194942033d19084b88961c34f68d05578bb200033459ee1e46508e890d6b911729edc3567f23610904c1a4ca23f916c00000063b10b028852e52480016325cf4aa363c1946280000f70c3eb6100023a400064e1c6992d98a8cf5a0a0599f08301a32ac159a4bf6038f24462c953568000d06000000096d8c05f40003919b68b5a22b8bf4f720001050000000583618a1980005e24439cb800055b4e7b4540ee9a344100000000000001d0c000000000000112e71c00000011f04a30001b2c0000005302ae4b08324227393c0000002f31c41c7a46e46db7247d854954e9ec88ba4bd6ea97f9628654419147513c4c13f6a29db06e572e613315345fd35435a45e24a448993ddc3cd314cb2a901f209f49b9f2d998be80de3829890e594faadcca8a67b0001b6000000060e267465047201e82a13a46e900000007d2000696917921c9a4000b41520400000024d18547b000022519beabb5f287b416ab060f82dd5b46b456fa92e119abcd54196712163442a91d911d6d9763e8aa978e1b05b5245c7b43ba15724fc000cd53c5033c30adf100009cd59465d5728ec90a8c3713b80005be00009c150c0003fb21c00002e00000000000cdecde70280009ce000000000029485d00000011b400064500014e27b5511b0c0000a1300011d0000af60000ca9b303360001a7116c4466b800011a88f52edb5cd35a0006fe0eb8c12d5800026f800011f0000000c5e2ea00000740000ee0000f8487a59f3a7800cccc00002c8de129c00000022b585e9db1aa0000000b3f00000015a47eb445a18c31a4162808e9c64ea665c9822c4f07e633a99b5a90c286622fe1afe00036382b49ba0000000000512b2d2fb00008e25df6921b5000012b6a600000006890000000fb882d2b080001ca000279000000000002602a80000003fc800000000000034d0fb400000000000000004c00d84000ca623b80000001dc00013002b42c72d69f8000016e00020d146c500112066011e8980a596f441ada80e50d6cd1aa3901b01e80001492e800004549061292bb41ea3ad07f85951de000000114960269f00020b80c05680fd049c5f00000ff15e458831504000008d2e070968af91a2d665dfa8345d0000000000000000000000018c2c8b66c0001182000367a865082e236f1800063cd033c5870890a05e29c0f
  | 31 => 0x4f0311c8f8c4a2f000013f457659990b5cacb0d12f8cb8c600002e100000560000001f7c000bbb1ab00005fc9b76a30a5c51862606914948140005a5974800082b07200018a2ac610900012200000000000d4caef6e12f4086e3b3616814c7ac04261f1c54aa272b19bae7c1a00440003350ed40002d48000000070223800000057e02b8001b1c0e82038e7c5220064b493bd36881b72d8879640bf64b039440000000001b2843a0000000000c30c380000001c060003328e406580295d29e6c0000510000d8044600000017b00002b61c7a5140000003f2800053061c549b248d3643c29e9d6140a57d277049142e2
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa6e8514d62040014dd0b21ac4080029b61643588100047743886b1020008ed8710d62040014dd0a21ac4080029b61443588100053742ce2b102000a6d859c5620400b1dd0fa8ac4080023b61f515881000733a8ca2b102004aea8014562040015d30028ac4080163ba1f315881000476c3e62b102000a6e85cc562040014db0b98ac408002aba13315881000556c2662b102000a6e850c562040014db0a18ac408012baa00315881000574c0062b1020048ef8758b42040070f90bbb284080123b20b765081000656216eca10200087f855d942040070f90abb284080032b10976508100043ec36eaa102073c3e64dd542040018bcc7baa84081cb1b98b75508100043f43acaa10200087c875954204001c5884b2a84080122f21d64508100061fbaac8a102000c3c75591420400355904b22840800317dd563508100062e3aac6a102000e8c4258d42040091d90eb1284080031bdd56250810006363aac4a102009aac84589420400196ac9b8a84080033558f715081000672b16e2a1020008f5861c542040019aac638a84080027c60071508100065cb22e1208200387c85dd9410400917909bb282080063b20b76504101643ec36eaa08206dc3e64dd541040018bcc7baa82080031b98b75504100043f43acaa08200787c8759541040018d8e4b2a82080030fdd564504100061e3aac8a082000cac7259141040018beeab1a8208003171d5635041000666392c6a08202a8ed86dc941040018dccbb9282080031b597725041027e57326e4a082000cad64dc9410400199cc7b9282080033358f72504100047743ac4a0820058ec8758941040018deeab1282080031b1d5625041001c3f42aec20820048bd845d841040010ff0cba882080270f99175104100062f31aea2082000c6e625d441040010ff0eb2882080021f61d65104100061f3aac82082000c3d7559041040018bceab188208003175d563104100266d382c62082000c6e7558841040018daeab1082080133a9c1621041004e5d322e02082000cd9635c041040019d2c4b8082080021fe1975884100062f31aeb1082064c6e625d621040cb0ff0eb2c42081921f61d65884100061f3acc91082000c3d75992210400187ceab2442080030f5d564884100062f3aac71082000c5d7558e21040091df0eb1442080031b9d5628841000636baac51082000ce9625c221040018f0ebbb22008003361cf76440100063dc2eec8802000c7885dd9100400197709bb220080032e21376440100066dc1eec8802000cd883dd910040018f6a7bb220080031e54f764401000675c16ec8802000ce882dd910040018f6edbaa20080032eddb74440100065dbb0e88802000d98731d110040019b6edb9a20080033addb724401000675bb0e48802000b738550510040017c704a0a2008002dc6162144010
  | 1 => 0xb05a8cc8080262fa1f31990100045ec3e633202000a3e85cc6640400147b0b98cc808002aba0b319901000556c16633202000a3e850c6640400147b0a18cc8080028fa1721990100051ec2e4332020048be87d51640400187eebaa2c80800f0f9d654590100245e43aa8b2020048f8805cd640400917d0f21ac8080028fa1643590100051ec2c86b2020048bc8750d640400147d0a21ac8080028f61443590100055741086b202000aad8210d640400917d0f212c8080028fa1442590100051ec2884b202000a9e83109640400153b06212c8080030fdd675590100051f42ce6b202000a3d859cd640400157700b9ac808012ae20173590100051f428e6b202000a3d851cd640400155d0439ac808002ab60873590103b51ec2ca6b202000e1f5394d6404001c3f06a9ac8081d68fa1453590100051fc2ae4b202000a3c855c9640400156902b92c8080028fa1472590100051ec28e4b202000a9e831c9640400153b06392c8080032b5c872590100051f42e64b202000a3d85cc9640400117d0e192c8080022f61c32590100051f42864b202000a3d850c9640400147d0a38ac8080028f614715901000557416a2b202000aad82d456404001c6ea328ac8080022fa1f31590100045ec3e62b202000a3e85cc5640400147b0b98ac808002aba0b315901000556c1662b202000a3e850c5640400147b0a18ac808012aea0031590100055cc0062b202000a3e85c85640400147b0b90ac808012aea0021590100055cc0042b202000c5f759d563040ed4bb0f3aac6081d795c427558c103af2a884eab182000c5f875d563040edcae20baac6081db954417558c103ad2f428eab182000a5e85dd163040014bb0bba2c6081e6b6e017458c100256c402e8b182000a5e851d163040014bb0a3a2c608002b3a087458c1000566c10e8b182000e1f5495163040014bd0bb92c608002976177258c103c56bc0ae4b182000ad4815c963040014bd0a392c608002976147258c100054f420e4b182000a9d841c963040011bd0e212c6080023761c4258c100052f42884b182000a5d8510963040ef5b30138ac608002b3a0b5158c1000566c16a2b182000e575194563040014bd0b90ac608002976172158c100256d40042b182000ad98008563040011e902b9ac4080123ba1f52588100247643aa4b1020048ee87cc962040014dd0b992c4080029b61732588100247643a64b102000a6f855d162040014d90aba2c408002b9205745881000537428e8b102000a6d851d1620400195ae83a2c408002b3a0c745881000566c18e8b102000e2f5495162040014dd0b39ac4080029b616735881000573c0ae6b102000ae4815cd62040014dd0a39ac4080029b614735881000557420e6b102000aad841cd62040ed4db0b29ac40800393d4e535881000727c1aa6b102075
  | 2 => 0x7645051000656396c8a0a203fcb870d9141440018beebb1a8288003171d7635051000666396c6a0a203b8ee86dc941440018decbb9282880031b197725051000657b26e4a0a204fcac64dc9414400199ec7b9282880033318f72505103647743ec4a0a203c8ec87d8941440018deebb1282880031b1d762505100066c31ee0a0a200387c859d841440510f90cba882880270f19175105100062e31aea20a2000c6c625d441440010ff0fb2882880321f61f65105100061f3aec820a2000c3d75d9041440018bcebb188288003175d76310510006373aec420a2000c6d75d88414404b0f90cbac42880031718d758851032636312eb10a200087f87d9621440190fb0fb2c42880030f9d764885100061ebaec910a2000c3e75192214400187aea3244288003179d763885100062ebaec710a2000c6e75d8a21440018daebb1442880f33a1c3624851001c3e42ceda02200087c865d74044013878c8bae80880031718d75d011000636312eba02200087f87d9740440010fb0fb2e80880030f9d764d01100061ebaec9a022000c5e75d8f40440018baebb1e80880031b9d762d011000636baec5a022009cb4649c740440010ff0abb2808800e1f21576501100046fc1aeca0220028dc835d940440011df04bb280880063b209765011000672316e2a022000cb7641c540440019c8c438a80880021fa1b75481100062e31eea902204cc6c62dd52044097ae021baa40881361fa1f65481102643e43eca9022000c3f75d912044001878ebb2240880030fdd464481100061e3a8c89022000c5f75d8d20440018b8ebb1a40880031bdd76248110006363aec49022000cb464dc520440019a8c7b8a40880032d19071481100066a318e29022000ce7621c520440818f4edb2e20880ff2e9db64c411004e5d3b0c98822000e9863193104407b9b4edb1e20880f33a9db62c411000e753b0c58822000c3f749d165040ed0fb0f39aca0800317dce73594100062fc1ae6b28207587e871cd65040010fd0f21aca080021f61e43594100043f43886b28200087d8710d65040014dd0421aca080029b60843594100043f43884b28200087d8710965040014bd06212ca080029760c42594100043f43e64b28200087d87cc965040010fd0e192ca080021f61c32594100051f42064b282000a3d840c965040f54f30138aca0801e1fa1f31594100043ec3e62b282000a3e84cc5650400147b0998aca080029ba0b315941000536c1662b28200087e870c565040010fb0e18aca0801e1fa1f21594100043ec3e42b282004a7a8008565040014f30010aca081da8f61653990100070fa9ca73202000e1f8354e64040eb47d0a29cc8080028fa1732990100051ec2e6532020098be870ca640400117b0e194c8080028fa1432990100051ec28653202000aae82d46640400155
  | 3 => 0x4b122000ccc73dc96244001968e9b8ac488003351cf7158910006373b6ca3122000a6d83d9462440011db0f328c4880029ba16651891000557424ca3122000aad84994624400159d07328c488002b360e651891000477c3aca3122000aaf84594624400155908b28c488002b3e0d65189100056641aca3122000a6e8619462440018dcec328c4880029b60c6518910006573b6c83122000e2f65d906244001c58cbb20c4880023b61e64189100053742cc83122000a6d85990624400155d09320c488002b3a0e641891000566c1cc831220008ef8759062440014df0ab20c4880029b215641891000567c1ac83122000acc83590624400155d0c320c4880032b9d8641891000717b28c83122000e2c6519062440fdd4c20320c4881fba90406418910006673b6c63122000e4f65d8c6244001c98cbb18c488003a3d93631891000746326c63122000e4f85d8c6244001c990bb18c4880023b61e63189100053742cc63122000a6d8598c624400155d09318c488002ab61263189100056741cc631220008ef8758c62440014df0ab18c4880029b215631891000557c22c63122000aac8458c62440015cf02b18c4880029ba14631891000536c28c63122000ace8618c624400199cec318c48800393d94631891000726328c63122000e8f6418c6244001d18c8318c48800393a14631891000726c28c63122000ec58118c62440fbd8c20318c4881f7b1040631891000537436a63122000a6c86d4c62440018dceda98c4880038bd93531891000716326a63122000e4f63d4c6244001c98c7a98c4880029ba19531891000536432a63122000c6e7654c6244001c5ec8a98c4880038b191531891000727b1aa63122000e4c6354c62440015cd0d188c488003a919231189100076231c62312203bae4864c46244001d48c8988c488003b118d31189101ddf040262312200087f855db42440070f90abb684880062f21176d09100046fc1aeda1220028dc835db42440070fd0bbb284880021f61776509100146f41eeca1220008dd83dd942440070fd0b3b284880021f616765091000656214eca12200087f855d942440070f90abb284880022fe1176509100046fc1aeca1220028dc835d942440011ef02bb2848800e1f214765091000656210eca12200087e86dd542440e7878c9baa84880031718f755091039636316eaa12200087e87d9542440010f90fb2a84880038b10b655091000c5f43ec8a122000c3f75d914244001878ebb228488006aba0b64509100062fbaec6a122000c5c75d8d4244001d1885b1a84880263ba1f625091000637baec4a122000c6c75d89424401355d09b1284881f21fa1b755051036e1e326eaa0a2000c5c63dd541440018d8c5baa82881ee1fa1f65505102043e43ecaa0a2000c6c72d95414400187eebb2282880030f1d
  | 4 => 0x2441058dceda9ec4880038bd9353d891000716326a7b122000e4f63d4f6244001c98c7a9ec4880029ba1953d891000536432a7b122081c6e7654f6244001c5ec8a9ec4880038b19153d891000727b1aa7b122000e4c6354f6244001d88c718ec4880f2b921931d89101e5f040263b122000a6e85dd362440014db0bba6c4880029ba1674d891000536c2ce9b122000caf749d3624400159d073a6c488002b360e74d891000717aa4a9b122000a6e859cf62440014db0b39ec488002aba1273d891000556c24e7b122000a6e851cf62440014db0a39ec488002b9a0473d89101e572c08e7b122000e4f5394f6244001c9f06a9ec4880029ba1643d891000536c2c87b1220008ee8710f62440011db0e21ec4880029ba1443d891000536c2887b122000a6f855c762440014d90ab8ec4880f23ba1f51d891000476c3ea3b12203c8ee87cc762440011db0f98ec4880029ba1731d891000536c2e63b122000aae84cc7624400155b0998ec4880029ba1431d891000536c2863b122000a6e85dc362440014db0bb86c4880029ba1730d891000536c2e61b12200387e86dd562440018d8c5baac4880021fa1f65589100062e39ecab12200087e8719562440018b8e632ac4880030fd9774589100061e32ee8b122000cac62dd1624400187eca3a2c4880030f194745891000656310e8b1220008be87d91624400187eebb22c4880030f1d764589100064e39ec8b1220008be87191624400187eea322c4880030f1d464589100064e398c8b1220028de86dcd62440018becbb9ac4880031719773589100064fb26e6b122000c9c64dcd6244001998c5b9ac48800237a1f63589100062fbaec6b122000c5c75d8d624400193ee9b1ac488003271d363589100046f438c6b122000c5f7518d62440018b8ea31ac48800327dd063589100064e3a0c6b12200387e87dd562440010fb07baac4880022fe11755891004c5e422eab1220008df835d562440051b906baac4880023be0975589100043f438eab1220098be87dd1624400187eebba2c4880030f1d774589100061fba8e8b122000c3c751d162440051bd0fb9ac48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac48800317e1773589100062e42ee6b12200087f855cd62440070f90ab9ac4880022fe11735891004c5e422e6b1220008ef825cd62440011ef02b9ac48800237a1c73589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100043f43ea6b12200387c87d4d624400187ee9a9ac4882030f1d353589100062fb9ea6b122002c5c73d4d62440010fd0ea9ac4880021f21d53589100061fba2a6b12207fc3c7454d62440018bee6a9ac48800b171cd535891000637baee4b122000c6c75dc9624400195ee9b92c4880032b1d3725891000667b9ee
  | 5 => 0x8002ab60b511911004c5f43e6232220008bd87cc4644400147d0b988c8880028f617311911000557416623222000aad82cc4644400157700988c8880faae20131191100051f428623222000a3d850c46444001d2a62188c8880028fa1721191100051ec2e423222000a3e85cc0644400147b0b980c8880028fe1510191100051e42a203222000a5e86dd763440018bcedbaec68800297a1875d8d100062f3b0ebb1a2000c5e76d9763440011bb0f32ec68800297a1665d8d100054f424cbb1a2000a9d84997634400159d0532ec688002b360a65d8d100046fc3acbb1a2000a9f84597634400153908b2ec688002b3e0965d8d1000566412cbb1a2000a5e8619763440018bcec32ec688003279db64d8d100070fb2ec9b1a2000e1c65d936344001c3eebb26c688003871d764d8d100046ec3cc9b1a2000a5e8599363440014bb0b326c688002a7a1264d8d1000567414c9b1a2000acd8299363440011bf0eb26c68800297e1564d8d100052e42ac9b1a2000acf82593634400159904b26c688002a7a1864d8d100064f3b0c9b1a2000e1f651936344001c38ca326c68800387dd464d8d100070e3a8c9b1a2000a5e8598b63440014bb0b316c688002a7a1262d8d100054ec24c5b1a2000a5e859d763440018baea3aec68800297a1c75d8d100062f438ebb1a2000a5e859d363440014bb0b3a6c688002b3a0a74d8d1000566c14e9b1a2000a5f855d363440014b90aba6c68800387d5254d8d100052f42ce5b1a2000a5d859cb634400153d09396c688002a761272d8d100052fc2ae5b1a2000a5c855cb63440011bd0e216c6880023761c42d8d100052f42885b1a2000a5d8510b634400159d05a8ec688002b360b51d8d100052f42e43b1a2000a5d85c87634406d5ad03b86c68800e3be1d52d89100053742e65b122000a6d85ccb62440051df0e996c4880029b60f65d891000557424cbb122000aad84997624400159d0732ec488002b360e65d891000557c22cbb122000aac84597624400159f06b2ec488002b320d65d891000536c18cbb122000e2f65d936244001c58cbb26c4880029ba1664d891000536c2cc9b122000ace83993624400159b07326c4880029be1564d89100053642ac9b122000acf83593624400159906b26c4880038bd9464d891000716328c9b122000e4f65d8f6244001c98cbb1ec488003a3d9363d891000746326c7b122000e4f85d8f6244001c990bb1ec4880029ba1663d891000536c2cc7b122000aae8498f624400155b0931ec4880029be1563d89100053642ac7b122000aaf8458f624400155908b1ec4880029ba1463d891000536c28c7b122000e4f6518f6244001c98ca31ec488003a3d9063d891000746320c7b122000e4e8518f6244001c9b0a31ec488003b160463d891000537436a7b122000a6c86d4f6
  | 6 => 0x64fb22e73222009c9c645ce64440018bcea31cc888003175d4639911000667390c73222000c6f655ca64440018d8cab94c8880032bd91729911004e56322e53222000ccc635ca64440010fd0fb2ac888003171cf655911000636396cab22200087e8719564440018b8e632ac8880031b1c865591100062fb2ee6b222000c5c65dcd64440018beea31ac888003171d4635911000666390c6b222000c6f65dc964440018d8cbb92c8880033318f72591100043ec1eeab2220008bf845d564440011bf06baac88800a3720d755911000477c12eab2220018ec825d5644400187eebba2c8880030f1d774591100062fbaee6b222000c5c75dcd644400193ee9b9ac88800317e1773591100062e42ee6b22200087f855cd64440070f90ab9ac8880022fe11735911000477c12e6b2220018ec825cd64440011f700b9ac88800317dd473591100062e3a8e6b222000c9f741cd64440010fd0fa9ac88800e1f21f53591100062fb9ea6b222002c5c73d4d64441058d8e5a9ac8880021fa1d53591100043e43aa6b222000c5f7354d64440058b8e6a9ac8882071b1c9535911000637baee4b222000c6c75dc9644400195ee9b92c88800333dcf72591100066639ee4b222000c6f53dc964440018daa7b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc725911000672396e2b222000cd873dc1644400117f0eb20c8880028fe1564191100051e42ac83222000a9f83590644400153906b20c888002abe09641911000556412c83222000c3e76d94644400147b07b28c8880022f61e65191100054f41cca3222000a9d83994644400155d05328c888002ab60a65191100045fc3aca3222000a9f83594644400153906b28c888002abe09651911000556412ca3222000c3e76194644400147b06328c8880022f61e63191100051f42cc63222000a3d8598c644400155d05318c888002ab60a63191100045fc3ac63222000a3f8558c64440014790ab18c888002abe09631911000556412c63222000a3e8518c644400147b0a318c88800387d9463191100070e328c63222000e1e8518c6444001c3b0a318c888003a560463191100051f436a63222000a3c86d4c644400187ceda98c88800387d8f53191100070e31ea63222000a3e8654c64440014790ca98c8880030f9d953191100070fb1aa63222000e1c6354c644400147d0b310c8880028f61662191100054f41cc43222000a9d839886444001d28c7188c8880faad21931191100074a31a62322203ebb0804c464440ff47b0b298c88800387d4e53191100070fc1aa63222080a3e8514c644400147d0b990c8880028f61732191100055b40e643222000ab581cc8644401317d0e190c8880022f61c32191100051f428643222000a3d850c8644400155d05a88c88
  | 7 => 0x7e871cf65440018bae639eca8820e9da0473d95102053ac08e7b2a200087e8790f65440010fb0f21eca880021fa1c43d95100043ec3887b2a2000a6e8210f65440014db0421eca880021fa1c42d95100043ec3885b2a2000a5e8310b65440014bb06216ca880021fa1f32d95100043ec3e65b2a200087e870cb65440010fb0e196ca880028fa1032d95100051ec2065b2a204087e87cc765440010fb0f98eca880028fa1331d95100051ec2663b2a2000a6e82cc765440014db0598eca880021fa1c31d95100643ec3863b2a2000e55310c765440810fd0f90eca880021f61f21d95101bd3b40ee1b2a200087e87cc365440010fb0f986ca880030f5d754d911001e1e3aca9b2220038bf87553644400147d0b21ec8880028f61643d91100145fc3a87b222000a3e8510f644400147b0a21ec888002aba0843d911000556c1087b222000a3e8510b644400147b0a216c888002a7a0c42d91100054ec1885b222000a3d83d97644400153d0732ec888002a760e65d911000557414cbb222000aad82997644400153f06b2ec888002a720d65d911000557c12cbb222000aac82597644400147b0632ec8880028fa1663d91100051ec2cc7b222000aae8298f644400155b0531ec8880028fe1563d91100051e42ac7b222000aaf8258f644400155904b1ec8880028fa1463d91100051ec28c7b222000e1f6518f6444001c38ca31ec88800387a1463d91100070ec28c7b222000e958118f644400147d0da9ec8880028f21b53d91100070fb1ea7b222000e1c63d4f644400147d0ca9ec8880028f21953d91100070fb1aa7b222000e1c6354f644400147d0b316c8880028f61662d91100054f41cc5b222000a9d8398b6444001d28c718ec8880fead21931d91101fdd840263b222000c3d751d7644400147d0b39ec8880028f61673d911000557414e7b222000aad829cf644400147d0a39ec8880028f61473d91100055b408e7b22203fab5811cf6444001c3ea729ec88800387e0d53d91100051f42ee5b222000a3d85dcb644400147d0b396c8880028f61672d91100054f41ce5b222000a9d839cb644400195ee5396c8880028fa1732d91100051ec2e65b2220008be870cb644400117b0e196c8880028fa1432d91100051ec2865b222000aae82d47644400155b05a8ec8880fe2fa1f31d91100045ec3e63b222000a3e85cc7644400147b0b98ec888002aba0b31d911000556c1663b222000a3e850c7644400147b0a18ec8880028fa1721d91100051ec2e43b222000a3f855c364440014790ab86c8880028fa1730d91100051ec2e61b222009c3c645d664440018bce7b2cc8880031b9cb65991100062f398cb3222000c6e72196644400187cebb24c8880030f5d764991100064f39ec93222000cae72d9264440018becab9cc8880031719573991100
  | 8 => 0xabb4829000e1f215769052001c3f42eeca0a400087d85dd941480070fd0b3b282900021f616765052001c3e428eca0a40018ec821d941480010fd0dbaa82900021fa1f65505200043e43ecaa0a404cc6c72d9541480018decbb9282900031b197725052001c3e42cec20a400087f855d841480070f90abb0829000237e0d76105200146e41aec20a400087c865d441480010ff0fb2882900021f61f651052004e56322e420a40018f8865c041480019e0c2b80829012f1b1db654852008477438c290a4000e6765185214809b0f90cbae80901321fe1f65d01200043ec3ecba024009cac645cb40480058bce6a9ec988003175cd53d93100145fc3a87b262002c9e7350f64c40070fd0fbaac9880021f60f755931000477c12eab2620018ec825d564c40010fd0e3aac9880021fe15735931001c3e42ae6b2620008ef825cd64c40031d904b9ac9880021fa1f535931001c3e43ea6b262082c6c72d4d64c40010fd0ea9ac9880021f21d535931040e36392a6b2620018ee87dc964c40018deebb92c9880031b1d7725931000637a9ee4b262000c6d53dc964c40018deea392c9880031b1d472593100045fc3ac8326200087d879d762c40070ff0ebaec5880021fe0d75d8b1001c3f42ee7b16200087d85dcf62c401317d09b9ec5880022f61373d8b1001c3fc3ea7b16200087d87d4f62c40010ff0ea9ec5880021f61d53d8b1001c77c3aa5b1620028ef874cb62c400599ce6996c5880022fe117558b1004c5e422eab16200087f855db42c40070f90abb6858800e1fa167650b100043ec2ceca1620028de839d942c40011bb073b285880021fe157650b1001c3e42aeca1620008ef825d942c400117f0eb2083880123ba1f62487101fc5fc3ac9a062000c5f7354d64840058b8e6a9ac9080122f21d43592100164e39a86b24200387e87dd562840010fb07baac50812e1fa1c7558a100043fc2ae6b14200387c855cd628400117f08b9ac5080262f2117358a100043f43ea6b14200387c87d4d62840010fd0ea9ac5080021f21d5358a100247643aa4b1420048ec874c96284005998e6992c5080123be1d62d0a100043fc2aeca14200387c855d942840011bf06bb2850800a3720d7650a101f45fc3ac9a0c200087e86dcf65440070ff0fb1eca88003175cf63d95100043ec3cc7b2a2000a3e8498f654400147b0931eca880029ba0a63d951000536c14c7b2a200087f8758f654400147f08b1eca880028f21163d951000537c12c7b2a2000a6c8258f65440190fb0e31eca88003175cc63d95100062ec38c7b2a2000e558118f654400147d09316ca880028f61262d95100052f41cc5b2a2000a5d8398b6544001ca8c718eca881029d21931d95100072a31a63b2a2040b70804c7654400187ae83a6ca880021f61e73d95100062fc1ae7b2a20008
  | 9 => 0x73d95200043f438e7b2a4000a3e841cf654800147b0839eca90003175cc73d952026537410e7b2a404ba6d821cf65480010fd0f21eca900021f61e43d95200043f43887b2a400087d8710f65480994dd0421eca900029b60843d952000537c12e3b2a404ca6c825c765480994dd0438eca9012e9b60871d95200043f43e63b2a400087d87cc7654800147d0998eca900028f61331d95202653741663b2a4000a6d82cc765480010fd0e18eca900021f61c31d95202643f43e61b2a400087d87cc365481098dae432ec8900123b60b75d912002476c16e7b224075c6d72d4f64480ed8dae4a9ec890002ab60843d91202255642265b224002ccc734cb6448001d1c86996c89000e1fa1671d91200043ec2ce3b22400087e87d9564480018b8e7b2ac8900021fa1c65591200062e398cab224000c5f65dcd64480018b8cbb9ac8900031dd9771591200063a32ee2b224000c77651c564480018e8ca38ac89000e1fa1f75591200043ec1eeab2240008df835d564480051b906baac8900023de0575591200047a40aeab22400087e871d564480051bd0fb9ac89000317dd773591200062e3aee6b224000c5f85dcd64480018b90bb9ac8900021fe15735912001c3e42ae6b2240008bf845cd64480011ef02b9ac8900023d20573591200046f438e6b224000c5f751cd64480018b8ea39ac89000327dd073591200043f43ea6b22400387c87d4d64480018bee7a9ac89000b171cf53591200043f43aa6b22400087c8754d64480018bee6a9ac89000b171cd53591200045f43e86b224002c9c73d0d64480051790ea1ac89000b271cd43591200147643a64b224002ccc734c96448001d1a86992c8900031ddd771591200063a3aee2b224000cd773dc564480019a8e7b8ac8900031dd4f71591200063aa9ee2b224000c77751c564480018e8ea38ac8900032ddd071591200066bb98e2b224000cd4731c564480019cee438ac8900031dd4c71591200063aa98e2b224000cb7431c5644800196a8638ac89000339d08715912000672210e2b224000ce6321c564480019ca6438ac8900022fe1d64191200054e41ac83224000ab48159064480978dcedb2e84900038bd9764d09201dc76432e3a12400096f855c7424800156d0998ec29000e1fa1b755852025c3e436eab0a400087e87d9561480018b8e7b2ac2900021fa1c65585200062e398cab0a4000c3f65dd16148001878cbba2c2900030fd9474585200061e328e8b0a4000c5f65dcd61480018b8cbb9ac2902131b5c865185200047bc3ac230a4000ab48458461480015a906b08c2900021fe15741852001c3e42ae830a4000cac425d061480058bce6a98c290003175cd531852000573c0a6430a4000ab684cc461480015cb05988c2900123b60a76d05200043fc2aeda0a400387c855db41480010ff
  | 10 => 0xb12800387c855c762500019c8c438ac4a0006aba1362509400043fc2ae5b0a800387c855cb61500011ef0eb08c2a0002b920961185400043fc1aea30a800387e85dcc61500010fb0bb98c2a000e1fe1f53185400043ec3ea630a800087f8754c61500010fb0ea98c2a0002ad607431854000578c004230a8000c3e859db415000187b0b3b682a00030fd4e76d05400061ea9ceda0a8000ce472d8541500019c8e430a82a00034b1d472505400069dba8e0a0a800387e851da21500010fb0a3b442a000e1fa1476485400043ec28ec90a800387e87dd562100010fb07baac42012e1fa1c75588400043fc2ae6b10800387c855cd621001317908b9ac4200021fa1f535884001c3e43ea6b10800087e8754d62100010f90ea9ac4200123b21d52588400247643a64b108009aac844c962100091eb0f28cc2200123d61e319844001c3f43eeab08806dc3c74dd561100010fb07baac2200262f211755844000477c12eab0880018ec825d561100f7878e83aac2200021fe15735844001c3e42ae6b0880098bc845cd61100011df04b9ac2200063b20973584400043f43ea6b08800387c87d4d61101058d8e5a9ac2200021fa1d53584400043e43aa6b088081c6c7254d61100031dd0fb92c2200031bdd77258440006363aee4b08804fcac74dc961100018dea7b92c2200031b54f725844000637ba8e4b088000c6c751c961100d9958e8392c22000f1d1d651584400247a43aa2b0880048f4874c561100095e10098ac2200030fe1576904400061e42aed2088000c3f535da411000187aa6bb4822000e1fa1776884400043ec2eed10880048f58798621100018eaeb30c42200031d5d5618844000d72412c3108800087f855d921100070f90abb242200272b1d162484400247a43ac290880048be87d51648800187eebaa2c9100122f21d43592200164e39a86b24400387e851c564880010fb0a38ac9100021fe15749862001c3e42ae930c40048f5878c661880070fd0fbaac3100021f60f75586200063610eeab0c4040c6f20dd561880818da41baac3100021fe15735862001c3e42ae6b0c400087e87d4d61880070f90fa9ac3100021fa1d53586200043e43aa6b0c40048f4874c5618801395cc8b9683100021fe15769062001c3e42aed20c400087f855d941880070f90abb283100030f1d5645062027e57326e4a0c403b8ef8758621880014df0ab0c43100035a5d570886200043f436e7b2a400387f87d8f65480018bae7b1eca900021f61e63d95200043fc3ac7b2a4000a3f8458f654800147908b1eca900029de0563d95200053a40ac7b2a401387d8718f654800147d0831eca900028f61063d95200062eb98c7b2a404ba6c864cb6548001c98c6996ca901329ba0b74d952025d36c16e9b2a4000c3d741d365480010fb0f39eca9000317e0d
  | 11 => 0xd0001d1a86992c5a000e1fa177158b400043ec2ee2b1680048be84dd661d000917d09b9cc3a000b179cd53987400062eb9aa730e8002c9e7350e61d00070fd0bb92c3a00021f61772587400061e3aeeca0e8000c3f76dd541d000195eedb9283a00032bdd87250740006963a8e4a0e800387e85dda21d00010fb0bbb443a00122fa1376887400146f41eed10e80008dd83dda21d00070fd0abb443a00021fe1975887400043fc3acb10e800087d8759621d001395ce8b1443a02169ee0174596403b43ec3ce6b2c8000c5f739cd65900018bf06b9acb201d61fa1c73596400043f43c86b2c800087d8790d65900b3c3886a1acb200021fa1f32596400043ec3e64b2c800087e870c965900010fb0e192cb201668fa1032596400051ec2064b2c8000a6e82dc565900014db05b8acb200031ddc671596400051fc22e2b2c8059a3c845c565900010fd0f98acb200021f61f31596402cd1f42662b2c8000a3d84cc565900014dd0598acb200029b60b31596400043f43862b2c800087d870c565900010fd0f90acb200021f61f21596400253d40042b2c8000a798008565900091d90ea92c5200029ba173258a4000536c2e64b1480048ec874c96290005998e6992c52000e1fa177158a400043ec2ee2b148000a6f855d162900014d90aba2c520002b3e0d7458a400056641ae8b148000ae7815d162900015c902ba2c5201138b9535458a400053742ce6b148000a6d859cd629000155f08b9ac520112ab2117358a4000537428e6b148000a6d851cd629003955d0839ac520002ab6107358a4000666b98e6b148000e4f5394d6290001c9f06a9ac5200029ba164358a4000536c2c86b148044e8c4350d62900014dd0bb8ac5200029b6177158a400053742ce2b148000a6d859c5629000155f08b8ac5200023ba1f5158a4000476c3ea2b1480008ee87cc562900011db0f98ac5200029ba173158a4000536c2e62b148044aae84cc5629000155b0998ac5200029ba143158a4000536c2862b148004aea800c562900015d30018ac5200021f61b7550a4039637316eaa14807287e8759542900e90f90eb2a85201678b1096550a4000637baac4a148000c6c7558942900019d2c5b8285200123d61e31986400062fb9aa6b0c8002c5c7354d61900070fd0bb92c3200021f61772586400247a43a62b0c800087d86dd541900018dcc5baa83200021f21d655064000636392caa0c80008ed86dc941900018dccbb9283200031b59772506400047643ac4a0c8000c6f7558941900018d8eab12832000e1fa1776886400043ec2eed10c800387e855da21900010ff0cbac43201931b98975886400043fc3acb10c800087d8759621900018dceab1443200031b5d5628864002476416ec90c8000c3e65dd12190089958e8b12432000b271cd43d89400043fc2ae3
  | 12 => 0x803175d573d92210062f42ae7b244200c5d855cf64884070ff0fa9ec9108021f61f53d92210162f39ea7b244200c5d73d4f64884010ff0ea9ec9108021f61d53d92210162f39aa7b244200c5d7354f648840593ce7a1ec91080a2fe1d43d92210164f39a87b2442028ef874cb648840599ce6996c910803a350d32d92210066ab9ce3b244200a9e83d92648840153d07ba2c9108022fa1e43592210045f43886b244200aad8210d648849f55908992c91080b339cd32592210074721a64b24420387e85dc164884010fb0bb82c9108021f61e65192210043fc3aca32442008bf875906488401c5acab2685108be3be1971d0a21004b7c2ae3a14422c87d86dd541884010fd0eb2a83108961f21d655062132636392caa0c4200c6e65dc941884018dacbb9283109961fe1975106210043fc3aca20c426487d87594418841395cc8b90831080e1fa1774582210043ec2ee8b044200cac42dd160884018bee6a9ac11080b171cd535822101c3fc32ea304420087d8799460884018bce7328c1108021fe1d65182210062f39aca3044200c3e659d0608840187acb3a0c1108030f99574182210061eb2ae83044200c5e655cc60884018bacab98c1108023ee1d60182210061ebaea9b2242028bf8750f644840593ce6a1ec8908021fe1570d912101c3e42ae1b22420387e87dd564484010fb07baac8908022fe11755912100477c12eab22420087e871d56448401878ebba2c8908021fe15735912101c3e42ae6b2242008ef825cd64484011f700b9ac8908123e20173591210043f43ea6b22420387c87d4d64484010fd0ea9ac8908021f21d535912100637baee4b224200c6c75dc964484018dea7b92c8908031b54f725912127e37b12ea32242008bf8759064484014790ab20c8908272b19172d05210061e3aec8a0a424fcac64dc941484c98dcecbac42908063b21970885211e674302e110a420087f855d360484070f90aba6c0908f31bd8975181210047dc3ac0302427f87d879cd65d001347d0939acba02268f61273597400062fb9ce6b2e8000c5f835cd65d01010fd0e39acba02228fe11725974004d1e422e4b2e800087e87cc965d00010fb0f992cba00021fa1c32597400043ec3864b2e8009a3e840c965d000147b08192cba00029ba0b715974000536c16e2b2e8009a3e849c565d010f47b0938acba00021fa1f31597400043ec3e62b2e8009a3e84cc565d000147b0998acba00029ba0b315974000536c1662b2e8009a3e848c565d000147b0918acba00021fa1c31597400043ec3862b2e800087e87c8565d00010fb0f90acba00268fa1021597400051ec2042b2e8086a3f845c165d00010fd0f982cba00021f61f30597400051fc2260b2e8009a3c844c165d001347d09902cba00028f61320597400245e422eab1680028ec874c962
  | 13 => 0xd1ec24e6b288200c5f739cd65104018bf06b9aca20a021fa1c73594414651fc22e4b288209a3c845c965104010fd0f992ca208021f61f32594410043f43864b28820087d870c9651041347d08192ca208028f610325944145d1ec24e2b28822887e87cc565104010fb0f98aca208268fa1331594410051ec2662b288200a6e82cc565104014db0598aca208268fa1231594410051ec2462b28820087e870c565104010fb0e18aca20803954c431594411443f43e42b28820087d87c85651041347d0810aca208028f61021594414551fc22e0b288209a3c845c165104014dd04382ca208029b60870594410043f43e60b28820087d87cc1651040147f08982ca208268f21130594410043f43860b28820087d870c1651041347d08182ca208028f61030594410053741060b288200a6d820c165104014ed02182ca208029d604305944104d1f42640b288200a3d84c8165104010fd0e102ca208021f61c205944104c5e422eab1082028ec874c96210401d1a86992c4208030f1d776504410061fc2eeca088200c3c85dd9411040187ea7bb282208030f54f76504410065b28eeca088200cb551dd9411040187eedbaa82208032bddb725044100657bb0e4a088200d2c751c941104018bee6a9ac02080b171cd53580411f45e43a86b008202c9c7350d601047d1790ea0ac0208faae20141580410147c43a60b00820087f865cd65884010fd0fb1acb108028fa1363596210051ec26c6b2c422587e8798d658840147d0931acb108028f61263596210062fb9cc6b2c420387e8758d65884018bee6b1acb108021fa1c635962112d37c32e4b2c4200b2c845c96588401c9cc6992cb108030fdd2745962100537c12e8b2c4264a6c825d165884010fb0f39acb108028fa1273596210051ec24e6b2c4200c5f739cd65884c94dd0539acb108029b60a73596210062fc1ae6b2c420087e871cd65884010fd0f21acb108021f61e43596210043f43886b2c420087d8710d65884c94dd0421acb108029b608435962112c3f43e62b2c420087d87cc5658840147d0998acb108028f61331596213253741662b2c4200a6d82cc565884010fd0e18acb109921f61c31596210063db84e0b2c4200a6f825c165884c94d904b82cb109929ba08705962100536c10e0b2c420087e87cc165884010fb0f982cb108021fa1c30596210043ec3860b2c4200a3e840c1658840147b08182cb109929ba08305962100536c1060b2c4200a76810c165884014eb02182cb10803179ce65d92210062f39acbb244200c5e655cf64884018bacab9ec91080a37a0f75d92210046ec1eebb24420087d879d764884070ff0ebaec9108021fe0d75d922101c3f42ee7b24420087d85dcf64884011bb0f39ec910803179d673d92210062ebace7b2442028df875cf64884018bceab9ec910
  | 14 => 0xd8598f62504014df0ab1ec4a08029b21563d894100575c02c7b128200ae88058f62504014dd0a31ec4a08029b61463d894100537436a7b128200a6c86d4f62505058dceda9ec4a08029ba1953d894100536432a7b128281c6e7654f62504014dd0bba6c4a08029b61774d89410056741ee9b128200acd83dd3625049fc5ca9aa6c4a093eaba1373d894100556c26e7b128200a6e859cf62504014db0b39ec4a08aaaba1273d894100556c24e7b128200ccf739cf62504014dd0a39ec4a08029b61473d894100727a9ca7b128200e4f8354f62504014dd0b21ec4a08029b61643d894127f4621a87b128200a6f855c762504014d90ab8ec4a093e3ba1f51d894100476c3ea3b128200e6751947625049f1dd0f98ec4a08023b61f31d89410053742e63b128200a6d85cc7625049f55d0998ec4a0802ab61331d89410053742863b128200a6d850c762504014dd0bb86c4a08029b61770d89410053742ce1b128200a6d859c3625040155b08386c4a08023ba1c50d894100476c38a1b128200a6e85cc362504014db0b986c4a08023ba1c30d894100476c3861b128200a6e850c362504014db0a186c4a093eaba1030d894100556c2061b128200ae6810c362504015cb02186c4a08031b18b75589410043f43ecab12820087e8719562504018dcedb28c4a08029b60f651894100476c3cca3128200a6e8599462504011df0eb28c4a0802abe11651894100537430ca3128200c6e7619462504014db06328c4a08023b61e63189410053742cc63128200a6d8598c625040155b09318c4a0802b9606631894100477c3ac63128200a6f8558c62504014d90ab18c4a0802bae01631894100574402c63128200a6e8518c62504014db0a318c4a08029ba1b531894100536436a63128200a6e8654c62504014d90ca98c4a08021fa1b755094139636316eaa12827487e87d9542504e50f90fb2a84a09b78b10b655094100637baec4a128200c6c75d8942504019cec438a84a09b78dd87659054100716328c520a82098bc865c2415047f970c0b8482a0802ae61030d814100578c0861b028200c6e72d9660504018dce432cc0a08031bd9572981410063632ae53028200c6e75d8a60504018daebb14c0a08031b9d4629814100636ba8c5302820387e86dd560504db0f90dbaac0a08021fa1f65581410062e39ecab028200c6c72d9560504010fd0e32ac0a0803171cc655814100636390cab028200c5f65dcd60504018b8cbb9ac0a08aa3b21b725814100637b2ee4b028200c6c65dc960504011dd0fb12c0a08031bdd76258141006363aec4b028200ccf73d896050401998e7b12c0a08023ba1c625814100637ba8c4b028200c6c75189605040199ee6312c0a0803331cc62581410047dc3ac03028200ad88358060504ff0fb0f39aca208268fa12735944146
  | 15 => 0x8186caa10028f61030d95423953741061b2a8400a6d820c365508014ed02186caa10029d60430d95420147bc3a63b0a8400d2c425d661508018bce7b2cc2a1003179cc659854248f16210cb30a8400c5f655ce61508018b8cab9cc2a10036310973985420066ab9ec330a8400d2c42dd561508010fd0fb2ac2a10021fa1c655854248e1fba0cab0a8490e2c4219461508011ef0eb08c2a1003a350d32185420147ac3c6230a840087f855c061508070f90ab80c2a100237e0d70185420146e41ae030a848fe2c421976050801d1a86996c0a100e1fa1671d81420043ec2ce3b0284028de839c760508011bb0738ec0a10034b10975981424761eba0cb302840387e86dd560508e50f90dbaac0a10034b10b75581420043f43ecab028400c5c73d9560508010fd0e32ac0a1003171cc655814247716210cab028400c5f65dcd60508018b8cbb9ac0a10036310b73581420063bb2ee2b028400c7465dc56050801b4885b8ac0a10031dd9471581420063a328e2b028400da4421c560508011f70eb00c0a100e1fa1f7558b410043ec1eeab16827387e871d562d04010ff0ab9ac5a080e1f2157358b4104c5e422e6b16820087e87d4d62d04070f90fa9ac5a08021fa1d5358b410043e43aa6b1682098ec8754962d04051d90e992c5a0826ab2113258b410164f39a86b14820087d83dd560904010ff0ab9ac12080e1f21573582410043f43ea6b04820387c87d4d60904010fd0ea9ac1208021f21d53582411fc5f43e86b04823f8be87d05609047f57501a0ac1208023ee1d60182410043f436e7b2a820387f87d8f65504018bae7b1ecaa08021f61e63d954100537414c7b2a8200a6d8298f65504010ff0eb1ecaa08029be0963d954100536412c7b2a8200a7b8058f65504014f100b1ecaa08b21f61c63d95410062eb98c7b2a8266a7681dd365504010fb0f39ecaa080317e0d73d95410043f438e7b2a8200c5d731cf65504010fd0f21ecaa08021f61e43d954136f0e21a87b2a820087e87ccb65504010fb0f996caa08021fa1c32d95410043ec3865b2a826da3e840cb655040147b08196caa09b61fa1f31d95410043ec3e63b2a826da3e84cc7655040147b0998ecaa08029ba0b31d954100536c1663b2a820087e870c765504590fb0e18ecaa09b61fa1f21d95410043ec3e43b2a8200a6e829c365504014db05386caa09b68fa1070d95410051ec20e1b2a820087e87cc365504010fb0f986caa08021fa1c30d95410043ec3861b2a826da3e840c3655040147b08186caa08029ba0830d954100536c1061b2a8200a76810c365504014eb02186caa08021fa1c20d95410043ec3841b2a82038ef8754b62504014dd0b996c4a08029b61732d894101477c3a65b128202cce734cb62504014db07b2ec4a08029b60c65d89410053742cc7b128200a6
  | 16 => 0xc07c00407000403000400c05009001002803800400011401000403c03400801400000402802c00802002001001000c00400005400800801c00004400005000803c00002801c0000f80a800000005000c00408400400403c00000003001000000002c00001810802001001403400c00c00c0040e400c02000c04c0000600200740140100080380b006003800000406800c00c00001005801800000009400001c05406006c00000001000000000002c02001000005800800400004803401800c02409400002800000801400000804000000401000c00000000400400404c0081080000a40700cc01c01803c01800005006400c08c00c00403000002c00800800002c01001400402000002801c07400800000400807001801000803800002000000c03001400010c00001c02400000000009800000000007801800003c00c0f80240b400003400005800802c05800800001400c00405409001c01003802400800801c0140080700280100dc00000400002401401400004c01800404c0000d002400c00000000001402409c00000000400404000002002401c01800800000401801000400011000801400002c0dc00801801c00401407408800001802801800c00c00401000804001004801001804002800800402800802000000000001000000800000002000404000400000401c02c04400800400c02c06400805401c01802408007c018000058bce6a9cc3a1003175cd53987420164f39a8730e840087f855c261d08070f90ab84c3a100e1fa1f75587420043ec1eeab0e8400c6c21dd561d08018de41baac3a10021fe15735874201c3e42ae6b0e840087e87d4d61d08070f90fa9ac3a10021fa1d53587420043e43aa6b0e8400c5f7354d60d08058b8e6a9ac1a100b271cd435834201c3f428e2b06840087d851c560d08010fd0db9ecaa10034b10b73d954200696212e7b2a840387f87d8f65508018bae7b1ecaa10021f61e63d95420053b40cc7b2a8400a758198f65508010ff0eb1ecaa10ce1f61c63d95420062eb98c7b2a8472b2c82d0f65508e54790ca1ecaa10038718d43d95423959641287b2a8473a6c864cb65508e765908996caa10039318d32d954200786a1a65b2a840087d879cf65508018bf06b9ecaa10021fa1c73d954239d1f420e7b2a8472a3d841cf65508018bae639ecaa11ca9ba0873d954239d36c10e7b2a847287e8790f65508010fb0f21ecaa11cf8710d43d954200537c12e3b2a8472a6c825c765508018eae238ecaa10021fa1f31d95420043ec3e63b2a8473a3e84cc7655080147b0998ecaa11ca9ba0b31d954200536c1663b2a840087e870c765508010fb0e18ecaa11ca9ba0a70d954200536c14e1b2a8400c79701c365508010fd0f986caa10021f61f30d95420043f43861b2a840087d870c365508e747d0
  | 17 => 0x1000088c63615d3ea000028853133b9af01765250359ae509013230c08940005b2450985cf262294360b5889e644223a25d0e843133a82c06a88b221500007de0560d79bf45d475c00005fcc8c4f81569400c2a608000000051e61e0931cacf8a85000000000000000f013ccec81940001ae8dd20004141d94496762019047800008e3f39298e6a00b2d59b9883632307b000035200000001d80000000379758a461f834786889fc82000000005fa71705c800000000024781c00001ea1150b9087400000003700000000000decca23e745700009a665f04f93d50ea0000ff800000042241f80006de595000181040c39401c1150126203383962c0767370000c4879004f177000000074f3169210fe00000c493e843247832a21781287811c095f846a0191fe9454c7a6323000f151d445c0000e00c944d0358100c1c240805f8d9c0dc89413a9ca0d2e1090000cdc0001221071b4000067b1f12034c567cc0542130b8a4a730d1c706b052a0302164bcc51723e93ac0006fe08b926d0185092bf88849ce0001c1830899e2780a1000400801c0000000a800000c04000000008410400400c00402c0c800401008c0340200380280041c800800006401400405801800400804801005800401400001007800c02c00003000401800801000c00000400c02822800800001c00001408c00800001406c01000400006c00c00807001001800804025001800401002802800c0180040d80080b000000403000c0180a800002c01002800c03400800c0000080840740dc00400802403005800005800402c00c0100b800800000000001c00000000002805c04000800403000409c0040140a800c02c03000400000400402c0300e400400800c0380000000c802000c01002c00401c00000000400401c02003002c01001c00800002004800c01800001400000000001410401406400402400000c01400c00400000801003400000003410001c01802000001000000000407800401001c01404c00801000000400c03000400800402404000012c02000802003000400000400c0a800400007806400000c0000440f800800401000800c00401808c00001c01c00000407000400000403c01c00c00800001002c02c02800c07402000402809c00801801c01000400401002400000c00409c03400800007400002402c03801800005805c06c08c00007001c1c80000b400403c02400400400c00004c01805401800000000c07c00000403800c0000b00000200c00f800408000402405c00002c14400c00c0340000bc0e007000002c00004c0d801800400801400000000006800c01002802400400c0840100200100a401400000803000004802801c04402803800001400800000002400c0300c804400000005003c00800c00000000400802406800004c07c05001c01800
  | 18 => 0x58e3a00010a08aceaa1bf38a905479a8ef1b8226c2944a502f02dd11e0d03418eb01148b127b11c48ae7dc2f222c0a403892960a5498c5292830e80f560cc38a011097285d33c922072659a0d288a05363a320a0f7917e00001e12c8dfe3510940d406d055800000002cc6ce14e800000078535792e11a40003e70aec000477079a2d843c51e167163858255114a1c281404c51ec14c08721f43f2167453e1cc45783ed10c7f100c073834007d2a785241dc2f327b9a0085649d1398f548fc6a943ea198be28702bd0ca50123a92e518040000003900000d5035f32f065c01a151000179475685a0001e28b2429116399708464a1074a16cda460300a1e6cb181690870748f4809144404844ec1d32af188c48030224ba2a868060e3f01ee8e6024820c00000cc0f1000072cdba0000001920b6c34a20d1e10c704d82070d040006f326f8324e0c1e31f018347ec36b0999c48d5a0003639fd0c5436533202982b627b00001f03f202e00004b80003d012a1e70a2c64522100fd02e65325222d4d6630b42389b485c4213a3a37ca687af3a70c100003480e31b54e0031e1aa9e9c0005c23a9965855e6631441a6c01e1d80bd143806c00038d0098aca0001a291cc5166cb3cf04403b46e30c29a210a886743ba0f118c77b0759a1cd087ef1ff80000002b51519c850462980f7800000018017f2320a168cd00016c453486427693200005801b9840000021301898c48140cf03a9ec00007c400021705b435c4001994a223133d981c91d240f2b594280f071333109f41202681be0634f3a6ec0001f783561f721019307a484f0071fa4c7800005f02490e24812a816145d032009397385c06fa23919a89688d70741ea8a6a44b3180554a1a7e64268be00da04d05115c039087c3f0800000008826e805c96e00015301fcac81590000efc00076e2060000a7e2ef1b1800000000025999f0fc60000000aaca101d429b9d091c08b300019cc0001de30481ecfa03e10000ae90800000be800097a2fb38c1cf0a8c16e0fe08e8a7816b40181a0c220074679bd09000000139898ab20001ff1e483788210168000eac6d10aa00006e21b00e4816c06a53a00004f00003361cd0d106864ca42b1b902ae8012bb800000038e1bf18fc20c3ec3a400011927f83f291ac9963df39893fc64883425d8a5806e8893b394647507663c70000bd40002b180003d618712f800031c2812c896dc5d279636f80000004c1000147c2261110000ed05aa000000000000000028e05e493e0003ec0000d44318312000c00000011813bc0201c51339534ea03ae000190465c7190000568e4c3be4699c8879c6ef43020ec72e18205d02bcd823f424589fc00089c0001df918612b1dc15f051a5610878ec107a4ab20f964c43011c1088cd11e05793428e6c73a0002e0a11435831
  | 19 => 0xea29c0b08d7065d1cb1b890a642f4769308826005375987ca2800021392b07a2000000050c02a2f50ec9e2d1341520001bc4ed07bd13598884865da2240c5c4205c62a389c47d68f13080b446fa55336f0c708c25754451d011943d421e9014e1684b39d13b104e65618a20782f87523179e0c25e8ce29094ccae272421a17543c800019380010a46c63e901a40005e90000fe0f8612c19797f022a62534904749302d331d1ed877205a00000000002694158b0022c41e4490a100005490bb800105a858008935c0007a5000000053c86d0001b680000d50f70000db240b28214bcf045552eb8000da83012689be09ca47530b22091d67030000bac44c5ed08d9a811708cb0000a006b48303ea84a888c0984289be47b201f0c811a0bf682212e80000003644208b490480001d200000007770601a04186000182950cdee22424f1ff0ea81ae0000000f340e33550e950f4000000000000000038080011aa000000034c76616200000000006ac0000000000161208800114a4bf362a0645400001f68000d142c418480bc00037f0000000ce80b600020dc0007c14038ae0000000000124000000000000200ba7410001ce4b966760ee0000a200000b21140c162d7000055800000000000003d82e21ee875470a54029690740341812f800001da76314802a85ba00007217007d01a809e86980003083f684dca1e75b2cd84e51a200011c177c1880000001af50660c12fa0090a3a8310c980000001c13d680cccae7b23d41d74f6e0002ee081040244c1b6058ccc245f054800119848e36783f054e1883e88e10a6445208208e449e15e2cf90c0f3205f00005ecd900001871364abe00000017504b64c712c80005620002cc936d0341351de8fa8000620000087421a71600000a0d1a0810000be8ee83b52751e1857211813d000007200018787f85b860f12889610d22093050970d887a00000000e523dc29597107420572a90a0908c14f2dc0be4ca403a00009b035a4822d29b5cda600021d837836263411895b800087912390b0000000202000000066e4251e54c0a0001510834d6481c12210c90fc01e15b22dc8bc73b00000000000ea051800000055c43180000000000ce05f800077600019f808289323196d450e14142194f504c002387081c9ac12d000000032a88c2d5059c0007bf0000000218325271040912c3564708ee818c8363a2035885000044f80003305b0000095c0000ef1739b591885781c40f24cda65a147231c78c64038f16cd1c420021296900ca5893520cd444e01239390708ec78c42117410647580d39bf00c6369222a264ec27f309c0e9c0ee08026203d042a61417b8954fd64fc391860c56638b27a19800143150af9380b7a5e106683744bc47c3738f90b040401cf1b0072256d1931b8443e8dd364800059243c35b87
  | 20 => 0xbb51b005035a0e28b5e4352a20a280008ac1328ec87e21fd0001cf4ebc07a2cf0ab0e54000000026903e0002b4926400008d18d09b83be2522ad00011d81402d61e443c238c15f98dce9864b2f188ecc9e6c235f83985245683b6036512036e225040c0381e90f906680b88133bf8420d4c7cd2d717ac5b056f25788bcfba7720e18000eae0861fb9104bec1ed2a2a21d0f04a8286174838016c1210d08e1e3f217318184046693b796fc67c04a0cd800063237800011a4000000082800078400000003380a80000bb1610f0e19d2ff0e6000000c000000040a63b0001df4000000382023cae406203a000083200007f80006707d31e014986446ab2dd8ed86b223c14c87e834662e1a98eb4cfe09b4469194e580001d89198000000000000000000030613510e42600000cf4000000000000118a34d0000428bfe73235f000012a2b20000000c525181a39c081ce81511e9d28fc427446a17d40920003fd14b895a0002e78000ce00fa271800031601300000000000000c9000067e00000017340008621308000f7c5412661c7c4e06980000000a048d607b86d090c8101998e1c00009c00022103725a845d1df0ee000043082304ee73e3650000c42253451000089a26a0eda20c0863bb15e99e0b7c3520410de8ce48ad15711a8dd00000000fb800019936da1d90520000228cb07440003360570f5c64d41c946c18e1b31b11fc826c694000035c0b000425e00ac0000002d3901800046c0000000d0c63947316e42a01f61ab8f0cfea23639b0858a9c6430149c4000028334e1ad4e4a46222d9d6800019f00006dc00029721f05188f60000d08a185d800017f88205b600000000011a0000069000100c69a22a90589182ed11fa0b000031634f8b8c00053e2ad80000004a0000021c13c1733c69ce0c8e79f11004a4000000000202d07c0e50001190d1241700017f44c64ae13e0e18a4e29337d85d48f27c61a60c1800c04705e02105ec000000000063a0fe2c681cc3ae17800011685688dc25a9f24e6603e30998b03d054a1ca80000008054088c0cde459030c800000004e3a88000db87df3a6a06c0000b22c0800058a3ca4011a74b46000200900000000031404d00004870001b0ca902bc1c6800018a0003700cc463e1aa3c413ed1b40002c50000e5a48a16580003182f21fe157400061b3091f5c0000d44539a8d16883a19680000a64430000088f207713b980000000ab3cc0000bc4000000051c000000167a06073200037a800000074538882b000000000004050f640d052996012e0000000938f280001f498d490675f2c4000000000005e8000bf00b40000000ae620f2789404b1e5280001ac40003e537813e4c928e81708edccd61c23fd9a4d1b28082fd20d4fb6873128199c5900cb2f6132403635d0c512a81f013f1f320b8dec7
  | 21 => 0x1b307cc3f63f92898ac00fc1192ba1174cde3da06c16508ce3cc34a8af8ac42490008534f2e5d3000000070429c000000014e061000011810a34f346196c7b65600da91fc9dc7ff45009344144d53f4061066404823786c800059722c226065624524a1c248dc19608d0514fec05920110fc7f6112090195449443823a0b34848131274a1fccf47f93a309180002f422985c815c10740909f80843791060fcd0ae80a2428a840420b104c8b291c678934722443e08683841040c3a5a226e1da91785422ab9c3080e2de09d0f4d0707ca29c9cd0c4e77531b16b473836a03505a00aa7fe372808d0084f01b00db454a70500017e421648d0b813a00002170000cec04a1b6214838078868b224812c1666330000b50bd0690000000000000040e91580000001eb000000020b0418a24b8e8db21b960c5f84e1038800000000025f000046e32a36c0dd8bbc6500001cbc2b000013c8fd505e02c2380000000000272049478e8160df23943ea89e3e115b08c00000000f040008ee01000000f251a3e0000054800000021b80ce6bb2cc0000af6377251093069c38f19416f03cc45916813490540001eba1543e21603e78f2ce362d90e811e8c9c19e4379550b9077a1660284a244fd0568d6c1b414e3e388482964a911708c8f761243dca20430c39f076088837423405a836c6c23391c922a51bc7b410e1de4b923753f603e4bce80f4471a9513a11f0e201b0d3c00000003c060084900018082901bd0000000ffa00045180a800082500b0f8c0000640a996800001cf3aca30046600000000001c45761e795980007c8172a2908887a63d61ab8f1e0ca15517c8e7e34600e8000bde35e29b174485a8952ab05940002f10ee9e8ca4870d19e00000003903ec9e841160003eb045000025642712580688ab26f0c3486c0000f380241fa69624885c4f0049a01818703ca6cc0c8886c000000219a2a0e9285f25b07345183214220c300a23bc2498ea88a24c34459d2c3c46a704b05a81124401378b7d0d45dd3331964bb05cc19822ec58654b2130968fee1bb1a49a850d66b60e5130019012331f239cbee49245c83c8ed233a4328bc04584b10ba13c899c18f0e396d0a768c20001a08a0e3a600012e89604953de16a4fb47b52be80009380001b92298f527ee2f719c4bb26422d30c403a276b1f805bc60e2a926d013045a2662c317805505673d11db502872e01e97cc14813b1ba1670ef04890a61398a986ea09f22f8b4250306884c0d328c11390d2d17a5c31fd11b510016d2ed981c94621a37703d417040913216e8cfa76011f0690f623af000203813a0001631ee110a0002910a140004123e58000b0e0523668904a0a4cd18500004c469147211380000df15b95a8cd01b83a19
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x150018200000a00d804a0ce81400118e58b458414a4a000000a9c0009300424479f4400b102468009569c0132ea06a40e003180078c800810041800040810820530060ba1842dcf655080150d9310b73d95420054364c425cf65508e530c9850d32d954239583259434cb65508e7a0c8650d32d95420054364c425d66150801c0c429cc659854200463660425ce615080150d9310b75585420054364c425d6605080150d9310b75581420070310873195605080118e9810b73581420056164c42dc56050801c246510871581420056164c421c5605080188d84dce73d89410050764c85dd9411040160d9498d325962101523e5d434cb648840588f8750d32d92210052364c42dd1608840188d845cc7358a400050764e859db415000141d93215769044000583650634cb654800548c9750d32591200162321d434c964480014c59310871591200072150d321c5644800148d9310974185200062360f729cb644400188f7460e74d89103f6a8200644c4624400148d9310a76509100052364c421d9424400160d9310b6550910004a3a6042d8d424400188d835c87259010006235d1831d1620400148d9310b76508100052364c425d9420400160d931096550810004a36604258d42040018d1636007150810
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x10026000000601d0cc9885b9ecaa100240da910a731966150801206d4884398cab028400d01195931087158142
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x1
  | 5 => 0x4b
  | 6 => 0x4c
  | 7 => 0x4e
  | 8 => 0x138c
  | 9 => 0x5
  | 10 => 0x94b
  | 11 => 0x94c
  | 12 => 0x94e
  | 13 => 0x124b
  | 14 => 0x124c
  | 15 => 0x124e
  | 16 => 0x138b
  | 17 => 0x138e
  | 18 => 0x98c
  | 19 => 0x98e
  | 20 => 0x128c
  | 21 => 0x128e
  | 22 => 0x10b
  | 23 => 0x10c
  | 24 => 0x10e
  | 25 => 0xa0b
  | 26 => 0xa0c
  | 27 => 0xa0e
  | 28 => 0x130b
  | 29 => 0x130c
  | 30 => 0x130e
  | 31 => 0x180b
  | 32 => 0x180c
  | 33 => 0x180e
  | 34 => 0xb0c
  | 35 => 0xb0e
  | 36 => 0x140c
  | 37 => 0x140e
  | 38 => 0x28b
  | 39 => 0x28c
  | 40 => 0x28e
  | 41 => 0x148c
  | 42 => 0xb8b
  | 43 => 0xb8c
  | 44 => 0xb8e
  | 45 => 0x148b
  | 46 => 0x148e
  | 47 => 0x184b
  | 48 => 0x184c
  | 49 => 0x184e
  | 50 => 0xd0c
  | 51 => 0xd0e
  | 52 => 0x188c
  | 53 => 0x188e
  | 54 => 0x94054
  | 55 => 0x94056
  | 56 => 0x95394
  | 57 => 0x138954
  | 58 => 0x138956
  | 59 => 0x209
  | 60 => 0x1409
  | 61 => 0x1449
  | 62 => 0x289
  | 63 => 0x1489
  | 64 => 0x14c9
  | 65 => 0x139254
  | 66 => 0xb0994
  | 67 => 0x98b14
  | 68 => 0x98d
  | 69 => 0xb0996
  | 70 => 0x98b16
  | 71 => 0x188994
  | 72 => 0x99894
  | 73 => 0x188996
  | 74 => 0x99896
  | 75 => 0x1649
  | 76 => 0x134b
  | 77 => 0x14b
  | 78 => 0x141294
  | 79 => 0x140d
  | 80 => 0x141296
  | 81 => 0x148114
  | 82 => 0xb8a14
  | 83 => 0xa0b94
  | 84 => 0xb8a16
  | 85 => 0x184a14
  | 86 => 0xa1854
  | 87 => 0x29314
  | 88 => 0x149314
  | 89 => 0xa4d
  | 90 => 0xb9814
  | 91 => 0x180b94
  | 92 => 0xb9816
  | 93 => 0x1049
  | 94 => 0x140b14
  | 95 => 0x140b16
  | 96 => 0x189414
  | 97 => 0x141894
  | 98 => 0x189416
  | 99 => 0x141896
  | 100 => 0xbcb
  | 101 => 0x19cb
  | 102 => 0xb8296
  | 103 => 0xb9494
  | 104 => 0xb8294
  | 105 => 0x28b94
  | 106 => 0x148b94
  | 107 => 0x148b96
  | 108 => 0x20d
  | 109 => 0x14cd
  | 110 => 0x185496
  | 111 => 0x185494
  | 112 => 0x149854
  | 113 => 0x150d
  | 114 => 0x194b
  | 115 => 0x164d
  | 116 => 0x74b
  | 117 => 0x1a49
  | 118 => 0xec9
  | 119 => 0x4954
  | 120 => 0x5554
  | 121 => 0x5814
  | 122 => 0x4956
  | 123 => 0x2cd
  | 124 => 0x2c9
  | 125 => 0x24211
  | 126 => 0x28211
  | 127 => 0xecd
  | 128 => 0x1a4d
  | 129 => 0xecb
  | 130 => 0x1a4b
  | 131 => 0x95456
  | 132 => 0x449
  | 133 => 0x131816
  | 134 => 0x181316
  | 135 => 0x180b96
  | 136 => 0x181616
  | 137 => 0x180e96
  | 138 => 0x29316
  | 139 => 0x28b96
  | 140 => 0x29616
  | 141 => 0x28e96
  | 142 => 0x74a13
  | 143 => 0x75813
  | 144 => 0x74293
  | 145 => 0x75493
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 1665
  | 6 => 3682
  | 5 => 2290
  | 4 => 46
  | 3 => 4
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
  | 7 => packedAt gbK7 (67710+((h/555+packedAt gbK7 (61605+(h % 555)*11) 11) % 1999)*12) 12
  | 6 => packedAt gbK6 (192687+((h/1227+packedAt gbK6 (176736+(h % 1227)*13) 13) % 4860)*13) 13
  | 5 => packedAt gbK5 (144266+((h/763+packedAt gbK5 (135110+(h % 763)*12) 12) % 2749)*13) 13
  | 4 => packedAt gbK4 (3310+((h/15+packedAt gbK4 (3220+(h % 15)*6) 6) % 61)*7) 7
  | 3 => packedAt gbK3 (328+((h/1+packedAt gbK3 (324+(h % 1)*4) 4) % 10)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7f01ff80ffc0fffc0fffffffd13f3f1a31f1ff
  | 1 => 0xfffe07ff07ff03fff03c03ffeec8c9fdce3e4f
  | 2 => 0x81fff80007fffc3fffc003c030f0f1e60fcf8c
  | 3 => 0x1fffffff800003ffffffc003f00fe07f00ff0
  | 4 => 0x1ffffffffffffc0000000003fff0007fff000
  | 5 => 0xfe00000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x120029000940444404454a548013130810d095
  | 1 => 0xe41602b102910299102810ab06484870c6264a
  | 2 => 0x11ab580844eae82eae802b01b0b0b1a60b4b8c
  | 3 => 0x21cd94dad0082033cb32b0023b00ec07600d60
  | 4 => 0x41f1e76ce73cb3008200c00c3ded0007bdb000
  | 5 => 0x788100708030c2030c2302303ffeffd8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeac8eee8ea88eeeaeac8eee8ea88eeeaeac8eee8ea88eeeaeac8eee8ea88eeeaeac8eee8ea88eeeaeac8eee8ea88eeeaeac8eee8ea88eeeaeac8eee8ea88, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36667
namespace PEqualNP.Outside.L_meta_36667
open PEqualNP.Outside.L_meta_36667.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 6 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 14 := bs0_4_0
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
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
theorem alls1 : ∀ k ≤ 3, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 26 := bs2_3_0
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
theorem bs2_4_128 : Interval s2Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 134 := (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 (concat bs2_4_96 bs2_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 48 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
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
theorem bs3_4_64 : Interval s3Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_128 : Interval s3Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_160 : Interval s3Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_224 : Interval s3Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_256 : Interval s3Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_320 : Interval s3Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_352 : Interval s3Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_416 : Interval s3Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_448 : Interval s3Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_512 : Interval s3Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 539 := (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96)) (concat (concat bs3_4_128 bs3_4_160) (concat bs3_4_192 bs3_4_224))) (concat (concat (concat bs3_4_256 bs3_4_288) (concat bs3_4_320 bs3_4_352)) (concat (concat bs3_4_384 bs3_4_416) (concat bs3_4_448 (concat bs3_4_480 bs3_4_512)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_64 : Interval s3Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_128 : Interval s3Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_160 : Interval s3Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_224 : Interval s3Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_256 : Interval s3Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_320 : Interval s3Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_352 : Interval s3Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_416 : Interval s3Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_448 : Interval s3Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_512 : Interval s3Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_544 : Interval s3Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_608 : Interval s3Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_640 : Interval s3Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 664 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 (concat bs3_5_512 bs3_5_544)) (concat bs3_5_576 (concat bs3_5_608 bs3_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 40 := (concat bs3_6_0 bs3_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_7_0 : Interval s3Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_7 : Interval s3Atlas 7 0 1 := bs3_7_0
theorem alls3 : ∀ k ≤ 7, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
  · exact alls3_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 4 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 12 := bs4_4_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 28 := bs5_3_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 396 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat (concat bs5_4_288 bs5_4_320) (concat bs5_4_352 bs5_4_384))))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 601 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 bs5_5_96)) (concat (concat bs5_5_128 bs5_5_160) (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)))) (concat (concat (concat bs5_5_288 bs5_5_320) (concat bs5_5_352 (concat bs5_5_384 bs5_5_416))) (concat (concat bs5_5_448 bs5_5_480) (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 4 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 46 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_2272 : Interval gbAtlas 5 2272 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2290 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))))) (concat (concat (concat (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)) (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)) (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696))))) (concat (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)))) (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 bgb_5_2112)) (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272)))))))
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
theorem bgb_6_3680 : Interval gbAtlas 6 3680 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3682 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768)) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896))))) (concat (concat (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)))) (concat (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696)) (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824)))))) (concat (concat (concat (concat (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)) (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144)) (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 bgb_6_2272)))) (concat (concat (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368)) (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 bgb_6_2496))) (concat (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624)) (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 bgb_6_2752))))) (concat (concat (concat (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848)) (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 bgb_6_2976))) (concat (concat bgb_6_3008 (concat bgb_6_3040 bgb_6_3072)) (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 bgb_6_3200)))) (concat (concat (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296)) (concat (concat bgb_6_3328 bgb_6_3360) (concat bgb_6_3392 bgb_6_3424))) (concat (concat (concat bgb_6_3456 bgb_6_3488) (concat bgb_6_3520 bgb_6_3552)) (concat (concat bgb_6_3584 bgb_6_3616) (concat bgb_6_3648 bgb_6_3680)))))))
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
theorem bgb_7_1664 : Interval gbAtlas 7 1664 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1665 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)))) (concat (concat (concat bgb_7_416 (concat bgb_7_448 bgb_7_480)) (concat bgb_7_512 (concat bgb_7_544 bgb_7_576))) (concat (concat bgb_7_608 (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 bgb_7_800))))) (concat (concat (concat (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)) (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)))) (concat (concat (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312)) (concat (concat bgb_7_1344 bgb_7_1376) (concat bgb_7_1408 bgb_7_1440))) (concat (concat bgb_7_1472 (concat bgb_7_1504 bgb_7_1536)) (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 bgb_7_1664))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeac8eee8ea88eeeaeac8eee8ea88eeeaeac8eee8ea88eeeaeac8eee8ea88eeeaeac8eee8ea88eeeaeac8eee8ea88eeeaeac8eee8ea88eeeaeac8eee8ea88
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372936 * 2 ^ 32 + 4008241800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36667.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,4]⟩,⟨.or,[2,5]⟩,⟨.and,[4,7]⟩,⟨.or,[3,8]⟩,⟨.or,[5,9]⟩,⟨.or,[0,6]⟩,⟨.and,[2,10]⟩,⟨.or,[11,12]⟩,⟨.and,[1,13]⟩,⟨.and,[0,9]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 4008241800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 4008241800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36667

open PEqualNP.Outside.L_meta_36667 in
theorem PEqualNP.Outside.L_meta_36667 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 4008241800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 4008241800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
