import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36805.Model
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


end PEqualNP.Outside.L_meta_36805.Model

namespace PEqualNP.Outside.L_meta_36805
open PEqualNP.Outside.L_meta_36805.Model
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

def SBf (j : Nat) : Nat := [6, 4, 8, 8, 8, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36805

namespace PEqualNP.Outside.L_meta_36805
open PEqualNP.Outside.L_meta_36805.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1872a1a1580404800a00066000801800bf41bd41df31dd31ef21ed21be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x22195414c74a8290f14c521
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 3
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
  | 4 => packedAt s0K4 (244+((h/4+packedAt s0K4 (224+(h % 4)*5) 5) % 22)*5) 5
  | 3 => packedAt s0K3 (84+((h/1+packedAt s0K3 (81+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x3f80fffe03ffffff01f83f07ff07fffe88e3f
  | 3 => 0x3fff00fffc03fc0ffe003ff83ff83e030f3cc
  | 4 => 0xfc00000fffffc000fffffc0003fffc003f03f0
  | 5 => 0xfffffff000000000fffffffffc0000003ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x80840a022048480016284508450842a8334d5
  | 2 => 0x5155294651a92934781522a46aa46b55288a2a
  | 3 => 0xaa64aa6a94a3b215bab0433d233d2381b0d34c
  | 4 => 0x3346cd8d193223a6dcd9ea0843ce71063d03b0
  | 5 => 0xc3870e0e1e3c3c38ef1e73ce720842183eec00
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xccccccc0ccc0c0c0ccccccc0ccc0c0c0ccccccc0ccc0c0c0ccccccc0ccc0c0c0ccccccc0ccc0c0c0ccccccc0ccc0c0c0ccccccc0ccc0c0c0ccccccc0ccc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36805
namespace PEqualNP.Outside.L_meta_36805
open PEqualNP.Outside.L_meta_36805.Model
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
  | 2 => 0x3f80fff807f03f81e0fc1f83ff07c0f8149ecc
  | 3 => 0x3fff03fff8003fffff001ffc1ff800fff8e30f
  | 4 => 0xc00003ffffffc001ffffe0001fffff001f03f0
  | 5 => 0xfffffc0000000001ffffffffe00000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8082000890800400021422842108520a412c55
  | 2 => 0x955699947525692af0ad15a3574686d0d496cc
  | 3 => 0x264caaa52469b269758219691ad208e598c30a
  | 4 => 0x3468d346464d234db9cb50421ce72c411e03a0
  | 5 => 0x3870e387878e3c71def39e73908430861ff800
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aaaaaa00aaaaaaa0aaaaaa00aaaaaaa0aaaaaa00aaaaaaa0aaaaaa00aaaaaaa0aaaaaa00aaaaaaa0aaaaaa00aaaaaaa0aaaaaa00aaaaaaa0aaaaaa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36805
namespace PEqualNP.Outside.L_meta_36805
open PEqualNP.Outside.L_meta_36805.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x15000000052380803000000004cea23e000212c1c01e009d51000300020c3d21c465c20022005923465426369400a563501400201890a0c10010c010010000c003ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x81fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc3be6598774cb30bf28e617d51cc37c83986f10730ef98e61dd31cc37e81986f50330bfaa4617e548c37ca9184f95230beaa461bd548c27aa9185f15230bea9c617e528c2faa5185f94630bea8c61be418c3788318778c630ee18c617e508c37e81186f50230ef98461fb308c2fea8985f95130beaa2617c544c2fea4985f14930ef99261dd324c2fea2985f14530df20a61bc414c3be6298774c530dfa0261bd404c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa8861be410c3788218778c430ee188617e500c37e80186f50030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f719641ed32c82fca3905f54720df20e41bc41c83de43907b48720dfa0641bd40c82fea9105f95220df2a4413e54882faa9106f552209eaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620bea8c41be418837883107b88620f610c417e508837e81106f50220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483dc64907b4c920bfa8a417c514837c82906f10520f790a41ed214837e80906f50120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841be410837882107b88420f6108417e500837e80106f50020f790041fa20083da40107e48020bfaa621bf54c427ea9885f95310beaa6217c54c4378a9884f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10df20e21bc41c43ec63887d4c710fb10e21f521c437e81886f50310bfaa4217e548437ca9084f95210beaa421bd548427aa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52842faa5085f14a10bea8c21be418437883085f94210dfa0421bd40843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910df20a21bc41443ec62887d4c510fb10a21f5214437e80886f50110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2086f90410de208217e500437e80086f50010fb88021fa10043ea20087e44010
  | 1 => 0xc52507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077c8620ef50c41de218837e52106faa420efd0841df21083bd42107788420df94441dfa0883f6411077a8220fd50441bf280837d501077ea620ef94c41dea9883bc531077ea420ef94841dea9083bc521077e6420ef8c841de99083bc321077ca220cf94441db28883bf501077ca020ef540419ea8083bc50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc6fca598fb94b31b7296637d52cc7daa598db54b31df20e63bc41cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518f7cca31ee994637e518c77c8318ef10631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131bfa92637c524c77c8298ef10531fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf298637e520c6faa418f7cc831ee990637e510c77c8218ef10431ef98863f6310c7ba6218fd4c431bf280637d500c6fea990df95321df2a6433e54c86faa990ef553219eaa6437c54c86fea790df94f21ef29e435e53c86faa790f754f21aea9e437c53c877c8390ef10721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fb8ca21f6994437e518877c8310ef10621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a437e53486faa690df14d21df20a43bc41487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410fb8c821f6990437e510877c8210ef10421f790843f621087da4210fd48421bf280437d50086fca7a05f54f40dfa1e81be43d037a87a06f10f40bf296817d52d037e85a06f90b40dea1681bc42d02fca3a05f54740dfa0e81be41d037a83a06f10740dfa9e81be53d037aa7a06f14f40dfa9681be52d037aa5a06f14b40df99681be32d037a65a06f0cb40dfa8e81be51d027ca3a06f54740de28e81bf31d037c63a06f4c740de18e81bf21d037c43a06f48740de10e817d549027aa9205f94e40bea9c817e52902faa5205f94640bea8c81be419037883205f94240dfa0481fb40902fea6a05f14d40dfa1a81be435037a86a06f10d40bfa92817c525037e84a06f90940dea1281bc42502fea2a05f14540dfa0a81be415037a82a06f10540fda0281be405037ea6a06f94d40dea9a81bc535037ea4a06f94940dea9281bc525037e64a06f8c940de99281bc325037ea2a06f94540dea8a81bc5150278a2a06fcc540df18a81bd315037862a06fc8540df10a81bd215037842a06fd4140dda82817e541027ca8205f94c40bea98817e52102faa4205f94440bea8881be411037882205f94040dfa0
  | 2 => 0xc12c5013a60c0941f9871125ed312e3638ad9150573268987a8c557c9653dab061e5980781a0181e01004000020086e0000e00806168100081e00002038020000209800000000280000022130120280003000018080087601006050040c00205004020000001a0f00006810020020981408008008100280001820010100f000008020080000002008180001c0c0040b04602024028041f0340080a01000000060d8100080013004018000005e0d002028040280a000040085a03024008140c8000008000002000220500c00814468020300e000000601004014000000280003000288000386000848270100480200830030000084c09800008040200000002040200000e030060281a07808010240081e16016030260380e000000000229000020100300001000018001386000044058160000e1301c0b0000006005018000000f01e0586a0900000000018280f0060601013008010020100c010040a0940680e00000000040785e060141580000800005f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18877e5210fdca421db94843bea9087ed5210edaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42be29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997790f32eea1e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cafca5197b90a32f6a1465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997790d32eea1a65ee424cbda84997bcc932ef192657f514caf8a2995fd4132be282657f540cafca8196f950329f2a0657d540cb7aa8194f55032be2a0657e530cafca41977cc832f719065dd320cbda6419734c832bf288657d510cafca0195f54032bf29e837d53d06fca5a0df54b41bf286837d50d06faa920df94e41bea9c83bf439077c8720ef50e41de21c837e52906faa520efd0a41df21483bd42907788520df94641dfa0c83f741906fca120df54241dfa9c83be539077aa720ef14e41dfa9483be529077aa520ef14a41df99483be329077a6520ef0ca419f28c83bf509077ca120ef542419ea8483bc50906fea6a0df14d41bfa92837
  | 3 => 0x3a0054fe9951680000d23026a9782f17833e4989a0f63c40c0e914a0f6c20609030ac464491c90d819cb680062211c281b73c87440010937e1c8030f24e83680002247c17c000000e0000ae10713e7814495f21e000130665500014dae10ec000001e60005b84326e12e3cc65a6000045c00159000af0002a04000019001e15a299062c50e61e8701795c82858a9aa11607ca8b0e0006cc000d904ea1c2e00000000085000000c680017630a9b1670001aeae80019953ea8d6d0b62227e0922f1258acd190d355e928e085a2e25740019d5d08551c8bc5bc0914821422851cbd1ad278c297e9ea46830cad8110e82148102d636064538000c82044cae60ca504a6a5821c87c1c8f40466ed48b0355a8b5530b55046bc67a56004ba5058000de8358f9703584dd4e2d820c990e30d55106582504919a6e88683b5d6000760000242f85c800000a95070e544e0017000026600018a92000bb53492f16495c8021c2708615100b2ac1e4b626615c80c548ed3a876d549cd4de001868955fc730588d21fcbfc0608a11a1b4bb93b0000010f0dd4028456aacf5620dcb48de51a738641df476488820e90d263c208e412249d3aa974a07853e08c2feb348b12b254338788345f67fd149363b8318a19125ba910e206e314a01661582020d8cd9dd0d4b292a15a2d47a128a2806631d7b0e700000000000000a90b910b4e6035103001280015a10516e000e409c53a274002f82a60000030733c278000005d84a0001670b2000001b90009358b000410000019da1be9e4000000c0460102d708cbc800108000539608a236097c1e0d42727e83f13e48a5185605555c91c6da094861389913100a1f4222d930c7dceba954fa755640482f84750d8a310600475948318b71813053caaec8f000564000142316023f0001a827e6a4c1910368b0cf79ca08070d381f01b02ecf62652d0000000000000000014b2a016d6f9d85ea0015e961000000002b8036c797384f380c654991b530524c499c46c0e8cd10c41e8fcb297e5a80bc0e0cc07000061140000b24fd80000030000255000000a791f0000596b000064000000b024000140ab7348b40440000420004c1bc0a4c6089a6737085c0c0170d68f0001b11f0000000ef01c370000005723dc002ab38a000af184000000cc1fc4b603c002d13162cc002381503a11a9e734c000472335069a8c0a8a18855c03b120109b58984225a4f4410434081e0d703545c484e7ac732e14d028001c6bc000000000891422520000000000010064400000000a152e8a41345557280000000000000000514b1a632a83c07e8f9156c410eab54b472c0005d020000001d6532000048000009fc000b8194001308003c62588a9a558874d50a53000828ba3141c288d8ea2261668d0921645e8408d28b40e1c47508707a000df03e3f
  | 4 => 0x8e9128fa1207c4002964d01f1431ee4840007dac624a26c2c0000008692797300000000237000000002720005d428aa709a0016d8000009c40016f008bb83f8bd15e4b81614223863852ad33429396000036a531798d6456bd13d2fc0007e5201b203a24cc41c24924c0b5a9a3560012e0000c49f94728f0002fd2407757e7ccb20543d6000001c70000000018d596904a21b60eaaa830a9e5c418cde8ba000650681a7000600000c93d28847304c000210050001dc4a5862f95187b46888f608bdca92060569e0148ff0000b87122c3b2ab18b99052848d0ca6b3bc050c92fa2fa0a96124c5de7d8099f2154c25751f44ee92cb024647a588d11a04ec808fa845426b48c1068
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x6410833551904208fd94410823d6510420c794c410831d5310420cd944410833551104209b596210834d5388420d9546210834d5308420d9544210823e64940208f592500823d65d0020c794f400831d53d0020cd947400833551d00208fd95400831e5350020c754d40083365150020cd545400834d53c8020d9547200826f6548020d354d200836551480209ed95200833661d5310ce58354c43366115310ce58054c423e6494f108f59253c426e6294f109b58a53c423f6454f108f19153c423e6494b108f59252c425e6394b109758e52c423f6454b108f19152c42b96090710ae58041c42b661d0310ad18540c423e64d4e108f593538423e6414e108f590538426e6214e109b588538423e64d4a108f593528423e6414a108f590528425e6314a109758c528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544423e61151108f184544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c715053443556114d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910d9584524423e6590510c7d4e414431c5390510cbd4a414432c52905108f994414431f5310510c714c414432f5210510cb1484144354538c5109d195314436452885109d195214423e65d0110c7d4f404431c53d0110cbd4b404432c52d0110ad987404423c6550110c7d4d404431c5350110cbd49404432c5250110ad185404425e63d50109758f540426e62d50109b58b540423d65950108fd81540423d60550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109d984520423f65904108f596410431e5390410c754e410432e5290410cb54a41042b960904108fd94410423d6510410c794c410431d5310410cb948410432d5210410ae580410423e64940108f592500423d65d0010c794f400431d53d0010cb94b400432d52d00108fd95400431e5350010c754d400432e5250010cb549400435553c4010d954b100427965840109dd9510043555344010d954910043b140440109ed9510043b24144010
  | 1 => 0x2ac6254540aed81515023e65cc5408f59731502ae62cc540ab58b315033451cc5408fd95315023c654c540cd14431502ba600c540ae580315023e65c85408f597215029e63c8540a758f215033451c85408fd95215023c6548540cd14421502ba6008540ae580215023d6590440cd944411023f65500409ed95401033a54500409b98854cc26d62153308fd9152cc23c6454b308fd9151cc23c6454730b358b31cc23e61952308f185548c23f64546308f191518c26f62546309b189518c23f65906308f596418c23f65106308f594418c2b960106309bd89544c26c62551309dd85544c27461551308f990524c23d6414930d3149324c23e64d45308f593514c3375110530cd144414c2b9601053097997314c2cd62cc5309b98b540c26d62d50309d987540c27561d50308f596540c23e61950308f185540c23e64150309b988540c26d62150309d984540c2756115030cb952520c32d5494830cb951520c32d5454830cd952510c3355494430d994a510c3655294430cdd92510c33464944308fd91510c23c6454430cd951510c3355454430d9949510c3655254430cdd91510c33464544308fd96410c23d6590430cb94a410c32d5290430cd946410c33551904308fd94410c23d6510430cb948410c32d5210430cd944410c335511043097596310c34d528c430d5546310c34d520c430d5544310c23e64940308f592500c23d65d0030cb94b400c32d52d0030cd947400c33551d00308fd95400c32e5250030cb549400c3365150030cd545400c34d52cc030d5547300c25f654c030d3549300c355514c0309ed95300c25e63153209758c54c823f6454f208f19153c823e6414f208f59053c834c534cb208fd9151c823c6454720b358f21c823e61952208f185548823e64d4e208f593538823e6414e208f59053882766114e209d584538823f64546208f191518825f63546209718d518823f65906208f596418823f65106208f59441882b9601062097d8d544825c63551209dd85544827461551208fd91534823c6454d209dd8553482746154d208f990534823d6414d209b195324834c534c9208f993514823d64d4520cdd4441483345110520ae580414826e65c8520b358f214825e63d50209758f540827661d50209d587540823d65950208f986540823c61550208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c530826e6214c209d98453082756114c20cd95251083355494420d594e51083555394420cdd92510833464944208fd91510823c6454420cd95151083355454420d594d51083555354420cdd91510833464544208fd96410823d6590420c794e410831d5390420cd94
  | 2 => 0x6114841ae98052106b96014841ad98732106b561cc841ad98632106b5618c8418fd95321063c654c8418f994321063d650c841e34c832107366194441a798c501069d6314041ab98850106ad62140419b98b54cc66d62d53318f58254cc63f60553319b98854cc66d6215331cb95252cc72d5494b31cb95152cc72d5454b31cb94a41cc72d5290731cb94841cc72d52107318f99250cc63d64943319b98b548c66d62d52318f992528c63d6494a31d3949328c6cd62cc6318f992508c63d64942318f583544c63e64951318f994544c63d60151318f996414c63e65105318f990504c63d64141319b988504c66d62141319b988540c66d62150319e980540c67960150318f992530c63d6494c318fd91520c63c6454831b5587320c6cd62cc43197d95310c794414c4319dd95310c63e64940318f592500c65e63d53219758f54c863d60953218fd8154c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c863e6414f218f59053c871e5390721c754e41c871e5310721c754c41c863e64943218f59250c865e63d52219758f548863e64d4e218f593538863e6494e218f592538874e534ca21b358f218863e64942218f592508863d60d51218f992544863e65151218f580544863e6494d218f592534866d6294d218fd91534863c6454d219ed8153486786054d218f996414863e65105218f990504863d64141219798c504865d63141219798c540865d63150219e980540867960150218fd91530863c6454c218f990530863d6414c219e98053086796014c218f992520863d64948219798e520865d63948219b59632086e5618c821d314d32086cd63c84219bd9521087a441484219dd95210863e64940218f592500871d5310f40ab98843d02ad6210f40a798c42d029d6310b40cb54842d03365110740ae58353d031d5314f40ab98853d02ad6214f40ae58053d02b960d4b40a798c52d029d6314b40cb54852d02b96014b408fd9532d023c654cb408f99432d023d650cb40e34c832d029e63d4740a758f51d02ae62d4740ab58b51d02b960d4740ae58051d023e65cc7408f59731d02ae62cc740ab58b31d023f654c7408f19531d023e65c87408f59721d029e63c8740a758f21d023f65487408f19521d033651906409b988535026d6214d40c714d43502ae6210d40ab588435025e63149409758c525032c5250940a798c425029d63109408f99741503345190540ae58253502af6254d40ab18953502b76154d40ad18553502bb6054d40c754c53502ae6214d40ab58853502b96094940a7d8d525029c6354940add8552502b46154940aed81525029e6314940a758c525032d52149408fd95325023c654c9408f994325023d650c940e34c832502b96094540a7d8d515029c6354540abd89515
  | 3 => 0x3d32e9f80030421aa69379463d26980018f60a000000001a67fc0fa4e000b996223c19c6f15b9340bc57cef0904d6198000e833e00006a2b39c0700000c0040200c64028060180008c0209c000dc0005000000010141d024010081300003008080940501c0c0200200002000000080b0000c010000000004c0005848018040700302011004130101d024000202c0140101000000030080101c0000c10094040040101c0e0a4000000500c15010010300000000000090540703803004060140304c020d8070080d02407004010041e0000209810008090180000003008040100702c120300204c0200000018010140d07400044080481900412000200100800821004070203901800004040500301c020000b07408054000000c0440001c00050020180100004000010081003000000010700d02801008010640c1ec0000804010070040000000000040280101c010000d098080000300814084010180101c050200100002004000000702005010020100700c010b80401800008141281c034000363f6550c4397d954310f2f4354843d390d5210f2d4354843d350d5210ead6210e428f9974350a3d6590c42c754e4310b1d5310c42ab5884310b1d53d0842d354e4210a3f6550842c754d4210a6f6550842d354d4210a7661d53329d58754cca3f64547328f19151cca3e64943328f59250cca7661d52329d587548ca3f64546328f191518ca3e64942328f592508ca3e61d51328f583544ca3e64951328f994544cb1d6315132cb588544ca3e61151328f580544cb1c5490d3297195434cacc6250d32cb152424cb8e43909329b195424cacc6350932e350d424ca3e64d45328f593514ca3e64141328f590504ca7661141329d584504ca3d65950328f986540ca3d60950328f185540ca3f60550328f990540ca5e63150329b988540cb1d54cc832cb552320cacd638c83297d95320cb1d544c8329bd95320cb2d544c832b3d95320cb4f654c832e3d91320cb8c644c832d3d51320cb8e544c832d3551320cb8d544c832c3551320cb4d32944328fd91510ca3c64544328f992500ca3d6494032d34c9500ca6e6294e419b58a539071e5350e41ab98843906ad6210e419798e529065d6394a41cb949429069e6310a41a758c42906ae62d4e41ab58b53906b661d4e41c7d4e53906ae6294e41ab58a53906b66114e41a798f529069d63d4a41ad987529069e6394a41a758e529072f5294a41ad984529063f654ca418f195329063e650ca418f594329078d320ca41a798c509069d6314241ab98850906ad6214241c754c43106ae6210c41ab588431069e6310841a758c421072d52108418fd9541106776550441ad987531071d5314c41ab98853106ad6214c41ad98453106ba6014c41ae58053106b661d4841a798c521069d6314841cb54852106b6
  | 4 => 0x4b380c38a524f9800000910598f73009a0b2afe56447d1494110a34014a370006c0441af3e09d8fcae81f2b2c450131ec5000008c156000d480036800000212474a015684c0000014b000000001582d02fc02075a48072a040000000019d3baab1e00005fb01124a70e6acf3d600048800000a8c3db081987dc938fc508881183032ac0011d800130a91018725c809c589b54f85843124005674d8398b4e04289100008a764a816015423caeacc05431cc80460baa2829842494b48002da2228401ba8f16ebc10f1db0442f93300020487ce19c26121a4561212947f549223000048d1810618b040022d2101595627d0003849c8003c098083af34ca8a82bab90b01c00a17d30e13c00064000684001d513cc2d43000000290000b854c288108000006557f8ff0a2000002d90001a92785506a94c4d8ad000000e495c0920012b80000017c2d2a2212068f31725f60000019a0003200008e0ca000ee91c33a0000000058a000c18001f47d8cc81121e208198005b6464668000000b43c0814b235ca292b27078d5094f176474aa0f25122343026748206c0002c150810191df14c000bc2a51a85f12c09640a658002ba57e8e5171be470074251c82183455a947000670001ba000648fc000506001641b216c728600c43c26e4fda5e14a8983a26e4044a4e099b26a8a1398f5134418e31bd42a61454af202c000f91c40000009e8064925dd0b000000458c080005ea2c048de0000b9428000000013d00000075c002ec000000962c9046750ad059006000e79d00000000022404c864001150869c4df8fd53c0ec9f000568000a20e9000b9d1faeb24cbd0ada793287bc001ad062280819200002bd1e8ca000b58bf800376c28b58155dc9413d800000700bc8761605554cad44260014a11734ab7067a6c4840e12e8f80002852fab1400678d986c5f825d6705b20ac08880002648d82e25b132468d21a71c0000dc0d853687024000504b7cc688424a6a0d88b4416918978c31966893c1e72f4a44b7a720e68d02210451ab81669e21b80010d80706036cfa0d2340819711234c291d0c0022eca9ca98df58c3755b15110c0f0499305404052a81e182be4999132d872caf2ca17812c8c0bd31200020aa8000af4129590003956980036c11d1614b32289d63aaf2a4490f72563ac5d57aac30023b9260c52b0619188172505d043a090dca547793a1e892cb680057ca5c4a000000acc0000a0ee7317884e444534a19d1000868001730d63980000060c64c0718e5f08cc4ead50009d03798c07c42cd58f143a5315e0000006b09e1fe5fa0001b13b1066600020d1fc7700025c0481fc1a1e80004c4002ed314b94002bb6004d80022f5c2a391aa1726eae1439ae2d2368f88ba3d82006c91b4c8ba8f20792d03b121a111d4ba4f68000f4988002ae5b07608
  | 5 => 0x950b8a010008288709f1848c9600e247c000e92521c63ed4e86d41c0608a1da4106112689c5308840028c0005ec0026900000030a9f3d4538002de5c61483f16200002c340ae2903243e0c63546dd318002dc000000ed520be97b83f3ca000000005ae224c100440e0e86a92a09a39d2d1c74dab44fa87d510001498000009fc102450c658c001125deb749fa0f1c85a8200f32cc0a1288a70006210600000047838aa90eaaa8b80002c89a82a22501e28d7b0b23f40656112e16a0142812d1169d4ab9fc000850a10d612a2e
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x13890000b002a340183201b00001811736cc51c420001a6a3801f585170000413121e7861144014b108a802d6e4d2813ad02a860ac000101c00016bc1a048c918202000840000000800610080161c080c1ac6b10a89950d75951320ca873b2a899065431d9544c832a18e2aa2641950f70551320ca86b94a6a1c83435ce5250a41a1ce5a9ca720e0f5358a539068739ea5294838358f5294a41a1eea9906520e0e654c83290706a9ac4218838358d5210841c1aa6b10a620e19535805310706b1aa4290838a5496014841872e032a6420e0d654c83210686ba4a499463435d2534ca21a1ae829a6410d497014d3208706a9ac421e818358d5210b40c1aa6b10a7a060d6354852d0306b2a6419681435c85350d40a1ae629284a050c7254c535028a38aa629a818354d6214d40a18e6a90a4a060d63548525029238aa4292810d1c5650c940a18ea99064a060d654c83250313310a398a818598c51c8540a1ae8292649863051580414c286ba0a699641435d0534c920c60a2b0082906326158054c430a298c2a0221891486150110c32a6b008208629525804104388a9a8088021c85494044010
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x92298005906819d9544c83280e87995320ca41a048154d6214d40c05631c5521494080c87595320c940a0481595320c940
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 7 => packedAt s2K7 (6+((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s2K6 (788+((h/14+packedAt s2K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s2K5 (24297+((h/267+packedAt s2K5 (21627+(h % 267)*10) 10) % 962)*11) 11
  | 4 => packedAt s2K4 (32278+((h/260+packedAt s2K4 (29678+(h % 260)*10) 10) % 938)*11) 11
  | 3 => packedAt s2K3 (2870+((h/18+packedAt s2K3 (2744+(h % 18)*7) 7) % 74)*7) 7
  | 2 => packedAt s2K2 (366+((h/2+packedAt s2K2 (360+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xe0fffe1fffffff81fe1fe1ff87fffffd18f1ff
  | 1 => 0xff07ffe07e1f87fe1fe1fe1ff870707ee73e93
  | 3 => 0xfff83fff801ff8ffe001ffe3ff807f8307cf1c
  | 4 => 0x3fffffe000fffffe0003ffff8003f80fe0
  | 5 => 0xffffc000000000fffffffffc00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x28000204100400004402402400941420085025
  | 1 => 0x42518443242908160a20a20988212158632692
  | 3 => 0x8432a8890d5241aaa1113542d5024b0b058b18
  | 4 => 0x16a53112490352cd33541103664b0213b00dc0
  | 5 => 0x18c621dc719c64f1dd99d990440c0c63def000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeeeee88eeaaaa88eeeeee88eeaaaa88eeeeee88eeaaaa88eeeeee88eeaaaa88eeeeee88eeaaaa88eeeeee88eeaaaa88eeeeee88eeaaaa88eeeeee88eeaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36805
namespace PEqualNP.Outside.L_meta_36805
open PEqualNP.Outside.L_meta_36805.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x4817e53902faa7206f90e40de21c817e52903dca5205b94a40bea9481ed52902daa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037c84a06f10940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea9081bf421037a84205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa51877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830f7290616e520c2faa4187b54830b6a9061df320c3ba64185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20f7a1641ec42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f7a1241ec42483dc64907b4c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb18e21f531c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb18a21f531443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f721465ed428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbdc84997b50932f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41ef29c835e53906faa720f754e41aea9c83bf439077a8720df94a41bea9483be42907788520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa9283ef52506dea4a0df14941f6292836c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620efd0c41dea18837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331efa1e63dc43cc6fca598fb94b31b7296637d52cc7daa598db54b31ef99663dd32cc6fca198df54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f621443ee32887da6510df94621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043ef42087d88410fb8c821f6990437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037c85a06f10b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0xb00e1e2884ce1732123b02fa5c0ae704be1283e01ac0024b4ac42c04a2803e00100a7c4e672c4484432e5c4000004a00013b153144478000d00180004300026a6f83e07a1227003e9c34840d51b8ae0743e0000561907ed3697d1385487e0002fca052f80012c904189bb3a2000d8a0d17874c001793ee96c86842390440000000000005d0000708b93d1a5028020c900051c4fc65177398000000000229b8a38e214c2fc001842926fc001e80000000594e3d4994138000000000019e00009414a6a0a41203111b09216400000226000000001ce214001c90f20000029700000104000000770000004fa4c0ab00000000000000000000000004ae5d5439ad00064000247458144308000006a4950000006300024e49028c1b99f0001349b0a043e1545d9fd1b2000d38002304852c20319a4192e9b627c540d024335e1cd090721d068cb4a3f1262511c00017c000000004ee4b0870001861a4fa0001b67089c000300924400120e86d50f13215e2ac3b1f24682d0dea1401e57ce222031a8686596b4b43e40013b09e1812997f000000da08a13e230b505452859c171580b8660fc119000160eca003781b4c404b2149f8e30f70fc0bcca0dc444140cd0e045e000fd0ed370000001e70003a41580000000071800148508c8926302568998003f2000408003329d5450000f60001fa330ca3480028200062cd80d33a899000000000494af000000000001fe0001746f8002827b40004025a084000000007ac000000000005980400c00010030242a008030040400c000002001000004000280d0000000802020090000c0940b0100d008000040b00018014020900203802018110100000c000200200c0200c050140802802000000380305c0200c0000000000030000002c0100c00004070040500c01000020040100000024010040100c0101c02010010000403808000010240502c020000502c01000010200002c100240c02803008050040200000000010000005c08034000140e008000040c000060080403802008020340402c050100d00c0003007000000a00700c2e014030002b010000000001800000050140301402000000000006c02000000040000401004010840100007020010000300000004000300d034000040500c0300400bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0x4dc9780015aa451b00017a980810000000009e8000006c80023e0b60000021022c0680000029e830001ab000000602233c2490000000009e40009d116000319110080040e80047685c1900211a2c0001430b4284fa8000587d90e1b7000070000da4888f00000029800000000000104e79680003504c9461086e89592221e0880021939a41c5408f16e0a80010503c9451d1ff1ec96504a40000000c2a3935852d449e638a8b4f2a55000a2033a723049acc7964408358002020000000000015400009a162ec4e4000003120000000030e7a47086a0203111322408e984bd0951e0054cd88337226d1480043649d430432cc000a00005180007217030c00086232000000b70fe2da0000021823400000064000001070003b0000b2800520000900700003443c14d00000014172000119228b600000000000000000c19f33c67f142a301cc000000000000e5380c111c3bc9701700098c1a000268450d11b318c4c4aa9442740008e2354e200000000000978ca8002240000015c2b61bcf10003949fcd21dd0003f48400052c064000ea0768740d97406c410b79ce2a2918ab84a34c3e8d509e3bc520001171e4930000683262d40011f3de308000000009a4d086e52a000000004a421c000000003b80000004876cb19782c0a00549ee4f00000000000082c0016c1aa84c6e800414000000004d833c000000000000000047a000ac8000003d0c70c50000000000000040c03800000000a294a000a48001ec4cc584002934620f93100051a000001e41ca9d06c00008a75c590b9014000d424d3a4179128ff12031cb106c0001fccb0202025505282d00008d45888000000000ce3a01990380d0008144b92335c83c0018a13000ce387551e9ec4d0000000007d892000000000004d033053a2700000058a6f0000000000049e000000300660012a0053b43cc8e800000001418c93ac2e0f00f51041391583d4220000013c0000000000600000026000000000000264540605617b42a000001001d6001030714ce0008a8d72521dc1e0533e2a10ae8001bc77c000003aa675250000000000000
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x2310c355518c430d5544310c35551cc03097d95300c29c644c030d5545300c27b654c0309798f54c825d63d5320cb18954c825e63153209758c54c823e64d4f208f59353c831e5494f20c755253c834e6294f20c795153c831d5454f208f99053c823d6414f20cb55342c82cd6310b20cb55232c82ac644cb20cb55132c834e534cb20ab19121c823e64d4e208f593538823e6414e208f59053882766114e209d584538832e5488620cb95021882e96008620cb953208825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d185534823e6414d208f590534826e65d0920b358c424826c654c920ab19132482e8604c9208f990514823d64145209798c514825d63145209b99721482ac6448520ab992204826e62d50209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209b98853082766114c209d584530823e64948208f592520825e63948209758e520823f64544208f191510826d6588420ba580210823e64940208f592500826f65480209ed95200825e63d53109758f54c426f62553109b18954c423e64d4f108f59353c423e6494f108f59253c426e6294f109b58a53c423f6454b108f19152c423e6414b108f59052c425e6314b109758c52c426e62d52109b58b548425f63552109718d548423f6454e108f191538423e6414e108f590538426e6214e109b588538423e64d4a108f593528423e6494a108f592528425e6394a109758e528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c715053443556114d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910da5805244354538c5109d195314436852881109e195204425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109e980520435553c40109e596100436952840109dd95100435553440109ed9510043695244010
  | 1 => 0xc66f62551319b189544c67b60551319e181544c65e65d0d31b3588434c63e64149318f590524c69c644c931b5185324c69e648c5318f990504c63d64141319b988504c66d62141319798f540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63f64548318f191520c63e64944318f592510c65f654c4319dd95310c63f64540318f191500c65e63153219758c54c863f6454f218f19153c863e6414f218f59053c863e64943218f59250c865e63d52219758f548863e64d4e218f593538863e6494e218f59253886cd6310a21ab191328863f64542218f191508865f63542219718d508863e64951219bd89544863e65151218f992534863d6494d219b58a534863f6454d218f191534867b6054d219e181534872c54885219798f540865d63d50219e983540867960d50218f596540872c62550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c21cb553420866d6510821b358c420866d658c821cb55232086ac644c821cb551320874e534c8219bd9521086ac64484219dd95210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500876b4254021da109500876a3254021da4c9500876b2154021da485500869d6310b409798e51d025d6394740ab18941d02ad6210e409798e529025d6394a40d398e529034d6394a40cb90e529032c4394a40cb94b429032e5250a40a798e419032e5290640cb948419032e52d02409b988535026d6214d40d3988535034d6214d408f997435031c53d0d40c714d435031c53909408f994425029d6310940c714c425023e65d0540c714f415031c5350540ab189415031c5390140ab98a405023d6590c40ab588431023f65508409bd89511026c62544408f596411029e63904408fd95401029c63500409ed95401026e62153309b58854cc23f6454b308f19152cc23e64947308f59251cc26e62d52309b58b548c2cd6210e308f992528c23d6494a30a7191328c23f64546308f191518c26f62546309b189518c29e648c6308f992544c25f63551308f994544c25e65cc530c7153314c31c544c530c7152304c26e62d50309b58b540c27661d50309d587540c23d6595030c718d540c23e64150309b988540c26d62150309d984540c2756115030c7553430c25d6510c30b3588430c32e5494830cb552520c32e5454830cb551520c31d54cc830a7191320c31d544c830d3949320c3365494430cd552510c3665294430d954a510c3365454430cd551510c3665254430d9549510c3574354430d510d510c3573254430d54c9510c25d658c430a799
  | 2 => 0x1106349a80007c4c0001a7000000000002520000006d198604040000002e4001eb4025380011f0000006000000000101977246420da00029e2b4c71630001dc598a240a6c4459570fe1401c84c0d44602c8460785f4f789505c0d03d0093b86b4810151b8518fb9060361700009228a000901611da0a4bd000300000af0003581f4000f70d83d4391b308a4ed0908337e25c571b7032608681af024278e9a04388208b605235029c940f60fc1747a1f30be0784003a0226490c1df12064c010d812c37501066354238fc10923a8385f9600445084691901c0cc6696b0ce08065825114700ec08c0000000000d2ba28c0c074000000e08ce1f43c4d01ae31e000708003e4000eb8000006f10c9121f02c800000394410dc8001e600030a093ec01001014030080000402020060040200806000020340703459008010c00200c13014000800000001000010640b0000e0240203000018020100002800010010000e014070040301c020500001c010180e004010000f000010441402813028060040200800040010680706c000480400002014000001f00004020000080c04c12018020180b07c000200b0000100401000060400f0840105802000020000005c010000002c00018020400403c0c00c020200000003014000080400c000480100c3a000040080001800000020d015058030000c01402000040100000c01014000066f62547439b18951d0e6e62943439b58a50d0e3f6550c4397d954310f2f4354843d390d5210f2d4354843d350d5210e5e63947429758e51d0a5f63543429718d50d0aad6210e428f9974350a3d6590c42c754e4310b1d5310c42ab5884310b1d53d0842d354e4210a3f6550842c754d4210a6f6550842d354d4210a7661d53329d58754cca3e64947328f59251cca3f64543328f19150cca7a60d52329e583548ca3f64546328f191518ca3e64942328f592508ca3e64951328f994544cb1d6315132cb588544cb1c5490d3297195434cb2c5490932e390e424ca6c6550932e350d424ca3d65950328f990540ca5e63150329b988540cb1d54cc832cb552320ca5f654c832c7551320ca6f654c832cb551320caad6210f419b98a50d066d62943419b98a539066d6294e41d398a539074d6294e41c794f439071e5350e41c794e429069d6310a41c794c429071e53d06418f99443506ad6210d419798c525065d6314941d398c525074d6314941cb90c525072c43149418f997425072c52d0941cb149425069e6390541cb14a415063f6550c418f596421069d63108418fd9541106ac62504419dd95411065f63540419718d501066e62d53319b58b54cc71c63553319b98854cc66d6215331c755343cc6cd6210f31cb95252cc72d5494b31cb95152cc72d5454b31c755332cc69c644cb31c755132cc74e524cb31c7953318
  | 3 => 0x9b84f0a26d88b10e35279cd191b00857ccc1394180e0c192e082000c81f01f6070000003987d4b81d63c03f4179f93d41ecf496523c750b694c39616ca991a3fc630758000264f45d0f91d836c5c0e50b40000006e14a7b4000000927b05d8794141c4cf8571ae56021000000000aa0003f66c90896425403cbe1a5018000d10c607e000828000005d50d0b125841c001e53bc000c58c213a70c4790d25652c1a85e0944cced82c10c5985ea173fa3c8ffa161260c0a09341a2618b913f2f20b4bf1781782ace7816108290628000006685a12d0001bc530c42480000d00000027c0004d112000858ac38a324000002002d80000000000000000000001059430f82dcf88000000000000000000000000280000e49a42a4000ad8a81a41e0001271cc34c00000328000ae0002a255800081002000000001e008cb786027c12c0003b41e000108d4310854000002b4320f08a932a440310ff00031c0199d000000650e82261a0711d12b2658cc876228378b11ab0005200019e0000005500024c628dd95533639c909c640e0000011c000754190001385fcc493c000000001850560009b000270768001c2028284c880032e5d8de894400000bd9682181cc000ee2640a01b89b1f87486aa063c4194270fe390028028000a82680003d00051c000000005a4a50002e2699098ef0ac834a4800342840a68004107f00000000011c000104287e82c1cd06210cd81e30c87641b1ce3d0404b98002227744c12200000000000000000e380000000029800214000000b0000380000990d643c0f9b8000364000df2d4494dd0ea3cc1a46792f22a0742a9b51d2280c20073c859c12044080540818270007b85787517c45c000481ac21c720060001c0609441c60006d0001862d4150000007d00001704c5d0000850002440000000002cdf00000018c0000030e6700013a0000000016e0007409880
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x4034a0c90100000805083800000001801400000045c73d300001655130000b000000480018000000841800078358d6215132a1ae529a8720d0d731494250707318a520a83435c86355331838ecaa26598d0d7318954086163b2a899043525cc4254021a50e8992a010d28744855008686b9ca4a14818398e5290640a1ae429a86a060c53189415030629cc520281435c86355030838ecaa264185457210d510c28a3a264a886185991518c430c28c8a8a601850d7318954c82163b2a8996418a9516008620
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x688080d8798c529054180d8798e529064080d8714c625054080d8714e6290140
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
  | 5 => packedAt s3K5 (20138+((h/221+packedAt s3K5 (17928+(h % 221)*10) 10) % 963)*11) 11
  | 4 => packedAt s3K4 (22272+((h/179+packedAt s3K4 (20482+(h % 179)*10) 10) % 711)*11) 11
  | 3 => packedAt s3K3 (1273+((h/8+packedAt s3K3 (1225+(h % 8)*6) 6) % 52)*6) 6
  | 2 => packedAt s3K2 (243+((h/1+packedAt s3K2 (240+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x81fff83ffffe1e0ff87f87fe1fffe07d19f3f3
  | 1 => 0xfe1fffc1f87ffff07f87f87fe1c0fffee63c9f
  | 2 => 0xffe0fffe007fe3ff8007ff8ffe00ff8307cf1c
  | 4 => 0xffffff8003fffff8000fffff0003f80fe0
  | 5 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xa402088850102002900980920252212808d131
  | 1 => 0x884110480a400502882082420844a50622486
  | 2 => 0x144aa290354906a58444d50b540a950b054b18
  | 4 => 0x5954c425240d4b394d50440d992c0613b00ec0
  | 5 => 0x61988739c67193ce7667664110301863dfb000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeeeee8e8eaeac8c8eeeee8e8eaeac8c8eeeee8e8eaeac8c8eeeee8e8eaeac8c8eeeee8e8eaeac8c8eeeee8e8eaeac8c8eeeee8e8eaeac8c8eeeee8e8eaeac8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36805
namespace PEqualNP.Outside.L_meta_36805
open PEqualNP.Outside.L_meta_36805.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x4817e53902faa7206f90e40de21c817e52903dca5205b94a40bea9481ed52902daa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037c84a06f10940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea9081bf421037a84205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa51877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830f7290616e520c2faa4187b54830b6a9061df320c3ba64185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20f7a1641ec42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f7a1241ec42483dc64907b4c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb18e21f531c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb18a21f531443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f721465ed428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbdc84997b50932f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41ef29c835e53906faa720f754e41aea9c83bf439077a8720df94a41bea9483be42907788520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa9283ef52506dea4a0df14941f6292836c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620efd0c41dea18837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331efa1e63dc43cc6fca598fb94b31b7296637d52cc7daa598db54b31ef99663dd32cc6fca198df54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f621443ee32887da6510df94621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043ef42087d88410fb8c821f6990437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037c85a06f10b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x2587511f35a1890584f20e0008a83437c000f516d468000000cc2620007a82837a6d546a302960293d1234822b8001c0000738001043969ec3922f0884b8d80c23ee5106b8320d876c5f0640000c0268c61fa77000000000a4d388941c424cc61881f43440c01248044034169440504328002026d0e20fc41c4fc0000048c54887a010340880007416a8d8079b634c3bc6680010484cdc0563585913c16822455c3b98b43c7e4000001ec000002611e4000a1276156815089c922c94d3997f298478fb2681f06792a1c300045c0008e0002fc000aa114500ff8000007600012f37e0011f0b200025c0026c50e058000751da4754b27d0009bc05800000000c082906e00028a2a31e2140006a0b4a10a184a12209000000498254980ba264908000000005c03b1d2438001350003347ac6f0130965350906e1d63ec0002c0460005088f00074077249000000dd8331b80000d88900a0414513a4342b49625703a969392561b2311019e049c001460e10cc2cc0028538a5711a96700099400038506970e985f1ca248bf1a73ca54c8193633e5886984008a5390d9864da2812c24d0006e42a95d20ca2d170d81e64ec1c9b300018cd424821c0bcdb8bd0000011d0000000000017121a0d42b800000644002903ea514000092b4001129ef30a2d0000040007c12208c522998ba2470f21311c99d1709b8000001381bc6b000240000000000008b00007c04e000000004420013a05819e840998481e8000e400621097cb605c194001190000000403003004040300000004004090100000008000000280200007000130000a00c03030010180200402004010340000400048050000502c080080d02c0301011020010501f000020080203804004000081500002068060200000006004030000001002004000000300006034030100104c04064140040001c1403c04000070001500405000010140201002008030080000401040020b80000013010000080402004018000100702001004030040b0000200c1a00c0001408040010380201c1900801008020080904002018160001200002024040000500400000000081e01c05028020440201404000000080003000000010140a08406004000040100000008020540402802004020040900003010060a400bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0x1da0000000000026a5c8001d4000000d2019000184aa1980f427c00243000000001504d296518a0618679c7f0421aa49c38000000000001874e081d288870780000a8003260009c00000066d3e173000000de1af42c210908000002a40012d35c104639cf504200001ab3be7a40000045a4293211b1bea540027f32c1fd2280201a8303e9d93bc8a4738b61fe555000360bc0a8a886b41e3dc860a4362338c00000006080028604a2a0002235124a8238a700019cbe1c1470000000f9312000ff00032e000d90002ec000000000000b5312084566a53c81f38e180eb1ec0002ec0000343e9d400000000a043f17d2ac1b4348710007189c9614ce38c0016b344400000a33c6071111a1000234189d5028730fa007000260441ee52496cb30001ba2dcc7000000000931e8000000fea26022001471844bc26c0020a07a3980013733800000000000148d285d0002f00000c2688340003e3e20012ea092560e9479922263a08e1f81205e08c17b000000af24b00093c0000024a00000000000264248d0000790001463e6000072192f256cd021500032c00000180278001ca32a0002196a32858c82911252560b70e900042c000000b6928d500039a0000000042826845909478164b29c2102808000f127851c0004e0406e80000029e000588d41b6020fe23f0000b88a0532940fc9f08613a000001751820003d800250488920001902b0780543e4000000735008ed1995900294000000000380002774080000b9dd000000b79833ae8903c0003148dcf0a7e0a0001140a23c40ac9e9992903490ea882c0368af8462043901d8ec3f62e41325242e7e92a80044e4688c80003c298581ed528640bd1774d600062a184c65254b8003a2324000003cc2bd3018d47a00052821106000d180
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x2310c355518c430d5544310c35551cc03097d95300c29c644c030d5545300c27b654c0309798f54c825d63d5320cb18954c825e63153209758c54c823e64d4f208f59353c831e5494f20c755253c834e6294f20c795153c831d5454f208f99053c823d6414f20cb55342c82cd6310b20cb55232c82ac644cb20cb55132c834e534cb20ab19121c823e64d4e208f593538823e6414e208f59053882766114e209d584538832e5488620cb95021882e96008620cb953208825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d185534823e6414d208f590534826e65d0920b358c424826c654c920ab19132482e8604c9208f990514823d64145209798c514825d63145209b99721482ac6448520ab992204826e62d50209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209b98853082766114c209d584530823e64948208f592520825e63948209758e520823f64544208f191510826d6588420ba580210823e64940208f592500826f65480209ed95200825e63d53109758f54c426f62553109b18954c423e64d4f108f59353c423e6494f108f59253c426e6294f109b58a53c423f6454b108f19152c423e6414b108f59052c425e6314b109758c52c426e62d52109b58b548425f63552109718d548423f6454e108f191538423e6414e108f590538426e6214e109b588538423e64d4a108f593528423e6494a108f592528425e6394a109758e528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c715053443556114d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910da5805244354538c5109d195314436852881109e195204425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109e980520435553c40109e596100436952840109dd95100435553440109ed9510043695244010
  | 1 => 0xc66f62551319b189544c67b60551319e181544c65e65d0d31b3588434c63e64149318f590524c69c644c931b5185324c69e648c5318f990504c63d64141319b988504c66d62141319798f540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63f64548318f191520c63e64944318f592510c65f654c4319dd95310c63f64540318f191500c65e63153219758c54c863f6454f218f19153c863e6414f218f59053c863e64943218f59250c865e63d52219758f548863e64d4e218f593538863e6494e218f59253886cd6310a21ab191328863f64542218f191508865f63542219718d508863e64951219bd89544863e65151218f992534863d6494d219b58a534863f6454d218f191534867b6054d219e181534872c54885219798f540865d63d50219e983540867960d50218f596540872c62550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c21cb553420866d6510821b358c420866d658c821cb55232086ac644c821cb551320874e534c8219bd9521086ac64484219dd95210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500876b4254021da109500876a3254021da4c9500876b2154021da485500869d6310b409798e51d025d6394740ab18941d02ad6210e409798e529025d6394a40d398e529034d6394a40cb90e529032c4394a40cb94b429032e5250a40a798e419032e5290640cb948419032e52d02409b988535026d6214d40d3988535034d6214d408f997435031c53d0d40c714d435031c53909408f994425029d6310940c714c425023e65d0540c714f415031c5350540ab189415031c5390140ab98a405023d6590c40ab588431023f65508409bd89511026c62544408f596411029e63904408fd95401029c63500409ed95401026e62153309b58854cc23f6454b308f19152cc23e64947308f59251cc26e62d52309b58b548c2cd6210e308f992528c23d6494a30a7191328c23f64546308f191518c26f62546309b189518c29e648c6308f992544c25f63551308f994544c25e65cc530c7153314c31c544c530c7152304c26e62d50309b58b540c27661d50309d587540c23d6595030c718d540c23e64150309b988540c26d62150309d984540c2756115030c7553430c25d6510c30b3588430c32e5494830cb552520c32e5454830cb551520c31d54cc830a7191320c31d544c830d3949320c3365494430cd552510c3665294430d954a510c3365454430cd551510c3665254430d9549510c3574354430d510d510c3573254430d54c9510c25d658c430a799
  | 2 => 0x410c354362011b2664f081900054400000000490001de0461f10819b40424482a0011a000ea18d3d8578ae0511de000000a22b46a81b96305c38c399c50000289b9a40002a425018228000001d11023a41c0792ba470071231f81d49d9590002940003f1000000605a0fe5a48581e23a460ce1390007c8d68f2000001069960000007f80000000000000000820508000000000000000c814809740004442f1be00071c7b12712e5e00000015c40c228002e28507c94c0ae448989b721e0002f976012000e68da00000000000000688a90bd2a83ac24122296698a010831c53885000076000931500005e8b100000070000000268228569a32e06d80e86621253c5b0621dc6088c9253ec2dc000000005f0e30003fc7d04d99723457cb400012800802010070000000401010050380004c0200c000940a0000000403028000440000003000030000d0000404406004060000004000008010000000001018010040b01001024030040300c0400002004010080000c0000400018050200001c01014010440101c0000801004270040100006000010100100400000000040200007028050040000c0100c000040b0040102808014040000a0100000400000060000402400000020200100c0000000000090400000c0a01c03024000000700c0001c030040f00c0204408014100301000000010000280601c010080300405058050226f62547439b18951d0e6e62943439b58a50d0e3f6550c4397d954310f2f4354843d390d5210f2d4354843d350d5210e5e63947429758e51d0a5f63543429718d50d0aad6210e428f9974350a3d6590c42c754e4310b1d5310c42ab5884310b1d53d0842d354e4210a3f6550842c754d4210a6f6550842d354d4210a7661d53329d58754cca3e64947328f59251cca3f64543328f19150cca7a60d52329e583548ca3f64546328f191518ca3e64942328f592508ca3e64951328f994544cb1d6315132cb588544cb1c5490d3297195434cb2c5490932e390e424ca6c6550932e350d424ca3d65950328f990540ca5e63150329b988540cb1d54cc832cb552320ca5f654c832c7551320ca6f654c832cb551320caad6210f419b98a50d066d62943419b98a539066d6294e41d398a539074d6294e41c794f439071e5350e41c794e429069d6310a41c794c429071e53d06418f99443506ad6210d419798c525065d6314941d398c525074d6314941cb90c525072c43149418f997425072c52d0941cb149425069e6390541cb14a415063f6550c418f596421069d63108418fd9541106ac62504419dd95411065f63540419718d501066e62d53319b58b54cc71c63553319b98854cc66d6215331c755343cc6cd6210f31cb95252cc72d5494b31cb95152cc72d5454b31c755332cc69c644cb31c755132cc74e524cb31c7953318
  | 3 => 0xe7000392000001bf0006ac000560005ec00000190000dc00037a5b0961980c0214001020443f8b294d0004a43b0963e20a8280dc068704ed8fb00671000195000000d7000000000000000001d03d8070002e46e80026c00050000000000299790001c8000003f6000701842506bcd41900000e4c894231216cff910098560130a80007210319d1fa2d0000820003284c138000648671480004bcf18001ea528000421324b4a388806a5587890e3c00000007d0000006004127a0000018b000000001070000f8000000001bc1b000000000998003f4768001f522c10ce98de2261a89f064000510001d50002746d80012a0000000027e0005a8aa3fa7f0dd8a7146430d907822a050001860001c000000000000e789c0000010b8c23e60010986d2540010a8003ac0441280000020c0000041e5fcec13a3407b9048af000000c9a1808c4b9070653c43c0a482113c5b81987a2b6230001212de1b8340103be27cb501b1da37cc51e83624c0628b10b80bd0d0280a847ca99e63ae45ce58e53da7e0001e5000000001e70000000000001a3186b00018e67c00071000000de000058774f59044065183180026a0005d00004e7dcc0800000000001a10005c8470d70b06e80017d000000958490000001d204422330690b011e00053000000000000000000000000021a30c0001f000000560002ae000040b83988580000009e350168001cc164a08000000008f0172aa50cf813217834c000000005f8000f70c2070ec80000032ce90000000589e000366770b5800360400000243d2008830bf00059cc01d0026148da8f30007a80a8e10005dc001450000c0f79752da0ac73a191566143b8b20d2390688ea33c000d380b4143e8d28f8000324000002362f800000096240149662e66d023a070405845d80031000000000088000000000002480780037206852001080000000002c02247a1ac06433c0004d4160006c08b134210001c31827e4e103c4242cc000e8328000000000ce000000001c41f80203d30e668000c4000630c7800000000029a92c8340270551d83340005d3060004380000048000031418000000930d6728091e
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x24030550f1804530cd00e0000006070010121000085d540a0160022c0001000861818358d6215132a1ae529a8720d0d731494250707318a520a83435c86355331838ecaa26598d0d7318954086163b2a899043525cc4254021a50e8992a010d28744855008686b9ca4a14818398e5290640a1ae429a86a060c53189415030629cc520281435c86355030838ecaa264185457210d510c28a3a264a886185991518c430c28c8a8a601850d7318954c82163b2a8996418a9516008620
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x688080d8798c529054180d8798e529064080d8714c625054080d8714e6290140
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 7 => packedAt s4K7 (6+((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s4K6 (731+((h/13+packedAt s4K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s4K5 (20138+((h/221+packedAt s4K5 (17928+(h % 221)*10) 10) % 876)*11) 11
  | 4 => packedAt s4K4 (22272+((h/179+packedAt s4K4 (20482+(h % 179)*10) 10) % 782)*11) 11
  | 3 => packedAt s4K3 (1273+((h/8+packedAt s4K3 (1225+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s4K2 (243+((h/1+packedAt s4K2 (240+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x81fff83ffffe1e0ff87f87fe1fffe07d19f3f3
  | 1 => 0xfe1fffc1f87ffff07f87f87fe1c0fffee63c9f
  | 2 => 0xffe0fffe007fe3ff8007ff8ffe00ff8307cf1c
  | 3 => 0xffffff8003fffff8000fffff0003f80fe0
  | 5 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa402088850102002900980920252212808d131
  | 1 => 0x884110480a400502882082420844a50622486
  | 2 => 0x144aa290354906a58444d50b540a950b054b18
  | 3 => 0x5954c425240d4b394d50440d992c0613b00ec0
  | 5 => 0x61988739c67193ce7667664110301863dfb000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8eee8eee8eac8eac8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36805
namespace PEqualNP.Outside.L_meta_36805
open PEqualNP.Outside.L_meta_36805.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x440100c12a0d10060008f00600212820699381d382004c9292c10eaa4c00f174694a910c2802b482c280007cd8e000c001d04304704a000040ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x2aa48c239096ab80009d2c042098801c800600048a978e9f0da680002712240d158002180189859d801eaa0519012d8013002600219b232d0814878e1c29a1118f94069a1b871a8cab1e038b800022001729251113888b1280280f1520102580199f96028003002ca8a2800a09278000800400281d620080082870018481820a4410400002800200600cea18876e5210edaa421d794c42aea98853e540ca7aa8195794f41aea9e836e52d06daa5a0d794e41aea9c836f52506d8a4a0cf953319eaa6636e52cc6daa598cf952319eaa4636f524c6d8a498db94621b6a84433e540867aa810d794c21aea98437a50086f2a010eb95021d6aa043ce530879aa610db94421f328843ea50086daa010fa54021b4a80436e52902daa52057d4d40ae29a815e53102baa6205b94840b6a90817651102eaa2205b94a30b6a94613f544c278a8984f950309eaa0616e520c2daa4185d94430baa88613e54c827aa9905794f20aea9e41ae54c835aa9907394f20e6a9e416e51c82daa5105b14520f5a82416e52082dea5885b14b10b7294216d52843d241084fd51109e2a2215f53442b8a6885bd4910b629221e9204427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xe0062a048c02c350d5210f0d5454c21ca95150087295454021d294d50087495354021c355153c82686548110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (788+((h/14+packedAt s5K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s5K4 (2694+((h/30+packedAt s5K4 (2484+(h % 30)*7) 7) % 111)*8) 8
  | 3 => packedAt s5K3 (312+((h/2+packedAt s5K3 (304+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc1ffff83ffff0f07f0fe1fffc3fff81e89f3f3
  | 1 => 0xfe1f0ffc3e1ffff87f0fe1c1fc383fff764c9f
  | 2 => 0xffe00fffc01ff1ff800ffe01ffc03fe1878f1c
  | 3 => 0xfffffe001fffff00001ffffc001f80fe0
  | 4 => 0xfffff000000001fffffffffe00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x44020088040010008012024440488844009131
  | 1 => 0x88841110902a00283104208884111298324486
  | 2 => 0x144aaa290d548353888b54156a82a545858b18
  | 3 => 0x3954cc42a906a59d5aa11021b3270189d80ec0
  | 4 => 0x219888733198c9e66ccd993822040611ef6000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeeeaeac8eeeaeac8eeeaeac8eeeaeac8eeeaeac8eeeaeac8eeeaeac8eeeaeac8eeeaeac8eeeaeac8eeeaeac8eeeaeac8eeeaeac8eeeaeac8eeeaeac8eeeaeac8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36805
namespace PEqualNP.Outside.L_meta_36805
open PEqualNP.Outside.L_meta_36805.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c38182140400004085000238085000000101ffd5007fe5401ff55007fc54017fd4c05fe53017f54c05fc53017fd0c05fe43017f50c05fc4300ffd4803fe5200ff54803fc5200ffd0803fe4200ff50803fc4200ffcc803fe3200ff4c803fc32027fd4401fe51007f54409fc5101ffd0407fe4101ff50407fc41017fcc405fe31017f4c405fc3100ffc8403fe2100ff48403fc21027fd4001fe50007f54009fc5001ffd0007fe4001ff50007fc40017fcc005fe30017f4c005fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a2000ff59510005faca8803bfc65440097e32a2000df19510024f8ca88037ff644401b7fb222000efd91100057ec888037fe64440077f322200dff5911006dfac888037fc64440077e322200def1911001d78c888037ff544401bff2a2200dff5511006ff8a888033ff63440197fb1a2000f7d8d10005bec688033fe63440057f31a200cff58d10065fac688033fc63440057e31a200cf718d10015b8c688033ff5344019ff29a200cff54d10067f8a688033ff4344019ff21a200cff50d10067f8868802fff62440177fb122000fbd8910005dec48802ffe62440037f312200bff5891005dfac48802ffc62440037e312200bfb1891000dd8c48802fff5244017ff292200bff5491005ff8a48802fff4244017ff212200bff5091005ff8848802fff3244017ff192200bff4c91005ff8648803bff5144001ff28a2000ff54510077f8a288037ff414401bff20a200dfd9051006ffa8288037f5414401bfe20a200cffcc510067fc6288033f63144019fe98a200cfd4c510067f8628802fff2144017ff10a200bff4851005ff8428803bff504400bff2822000ff5411002ff8a088037ff404400bff202200dff5011002ff88088033ff304400bff182200cff4c11002ff8608802fff204400bff102200bfe8811005ffa408802ff9204400bfe1022000ffc4110007f62088017fe104400bfb0822005ffd941002dfeca08017fe65040097f3282005df99410024fcca08017fd65040017eb282005df59410004faca08017fc650400b7e3282005ffd901002dfec808017fe64040077f3202005ef9901001d7cc808017fd64040117eb202005ef590100057ac808017fc640400b7e3202008ffd5010047fca808023fd5404011fe2a02005ffd8c1002dfec608017fe63040057f3182005f798c10015bcc608017fd630400f7eb182005f758c10005bac608017fc630400b7e3182007ffd4c1003ffca60801ffd530400ffe2982007ffd0c1003ffc860801ffd430400ffe2182005ffd881002dfec408017fe62040037f3102005fb9881000ddcc408017fd620400d7eb102005fb58810005dac408017fc620400b7e3102006ffd4810037fca40801bfd520400dfe2902006ffd0810037fc840801bfd420400dfe2102006ffcc810037fc640801bfd320400dfe190200abf9841004ffea208003fe5104001fea882009ff14410047fe8208023fe4104011fea082008ff1041003ffe620801ffe310400ffe9882007ff0c410037fe420801bfe210400dfe9082006ff0841002dfcc008017ff500400bff2802005ff5401002ff8a008017ff400400bff2002005ff5001002ff88008017ff300400bff1802005ff4c01002ff86008017ff200400bff1002005ff4801002ff84008017ff100400bfb8802005ff8401002ff42008017fd100400bfa8802000fe44010
  | 1 => 0x3fc415402fff98aa017ff8c5500bffa62a805ffc315402dff90aa016ff885500b7fa42a805bfc21540097fb02a004ffd4150027f6a0a8017fe505400bbf282a005ff1415002ef8a0a8013f85054031ffa02a005ff901500c7fa80a8017fc405402fff982a005ff8c1500bffa60a8017fc305402dff902a005ff881500b7fa40a8017fc2054001ffb2e2000bfd97100affccb88012fe65c4001feb2e2000bf597100aff8cb88012fc65c4029ffb262014bfd93100a7fcc98800efe64c4029feb262014bf593100a7f8c98800efc64c4029ffaa62014ff953100a7faa988053fc54c4027ffb1e2013bfd8f1009ffcc78800afe63c4027feb1e2013bf58f1009ff8c78800afc63c4027ffa9e2013ff94f1009ffaa78804ffc53c4027ffa1e2013ff90f1009ffa878804ffc43c4015ffb16200abfd8b10057fcc588006fe62c4015feb16200abf58b10057f8c588006fc62c4015ffa96200aff94b10057faa58802bfc52c4015ffa16200aff90b10057fa858802bfc42c4015ff996200aff8cb10057fa658802bfc32c402bffa8e2000ff94710007faa388057fc51c4029ffa0e2014ff907100a7ec8388053fd41c4029faa0e2014ff1071009ffe638804ffe31c4027fb18e2013ff4c71009fea638804ffc31c4015ff90e200aff88710057fa438802bfc21c402bffa862005ff94310007faa188017fc50c4029ffa062005ff903100a7fa8188017fc40c4027ff9862005ff8c31009ffa6188017fc30c4015ff9062005ff88310057fa4188017fc20c400bffb2c2005bfd961002ffccb08012fe658400bfeb2c2000bf5961002ff8cb08016fc658400bffb242005bfd921002ffcc90800efe648400bfeb242011bf5921002ff8c908016fc6484023ffaa42011ff9521008ffaa908047fc548400bffb1c2005bfd8e1002ffcc70800afe638400bfeb1c2010bf58e1002ff8c708016fc6384021ffa9c2010ff94e10087faa708043fc5384021ffa1c2010ff90e10087fa8708043fc438400bffb142005bfd8a1002ffcc508006fe628400bfeb14200fbf58a1002ff8c508016fc628401fffa94200fff94a1007ffaa50803ffc528401fffa14200fff90a1007ffa850803ffc428401fff994200fff8ca1007ffa650803ffc32840177eb0c2012ffd4610007fca308003fd5184025fe28c2011ffd061008ffc8308047fd4184023fe20c2010ffcc610087fc6308043fd3184021fe18c200fffc861007ffc430803ffd218401ffe10c2005bf9821002ffea108017fe508400bfea842005ff1421002ffe8108017fe408400bfea042005ff1021002ffe6108017fe308400bfe9842005ff0c21002ffe4108017fe208400bfd1042005ff4821007ff24108017fc208400bff8842005fdc4210007f62108003ff65440017fb2a2000dfd9510004feca8803bfe65440097f3
  | 2 => 0x51026fea4a8813fe5254409fea92a21cdf54951027f8a4a8873ff4254439ff212a21cff509510e7f884a8873ff3254439ff192a21cff4c9510e7f864a8812ff6154409ffa8aa204fdd4551027fca2a88037e5154409fe28aa204df14551027e8a2a887bff415443dff20aa21eff505510f7f882a8877ff315443bff18aa21dff4c5510eff862a8873ff2154439ff10aa21cff485510e7f842a8803ff60544017fb02a200ff98151007fac0a8803fc605440b7e302a204ffd4151026fea0a8813fc505443dffa02a21eff901510f7fa80a887bfc405443bff982a21dff8c1510effa60a8877fc3054439ff902a21cff881510e7fa40a8873fc20544097eb2ca005ffd925002dfec928017fe64940077f324a005ff592500ddfac928017fc649400b7e324a004ffd5250027fca928013fd5494009fe2a4a005ffd8e5002dfec728017fe63940057f31ca005ff58e500d5fac728017fc639400b7e31ca004ffd4e50027fca728013fd5394009fe29ca01affd0e500d7fc872806bfd4394035fe21ca005ffd8a5002dfec528017fe62940037f314a005fb98a5000ddcc528017fd62940337eb14a005fb58a50005dac528017fc629400b7e314a004ffd4a50026fea528013fe5294009fea94a019df54a50027f8a528067ff4294033ff214a019ff50a500cff88528067ff3294033ff194a019ff4ca500cff86528017ff619400bff30ca000bf9865002ffac328002fd619400bfe30ca004ffd4650027fca3280037e5194009fea8ca004ff14650026f8a32806fff4194037ff20ca01bff506500dff8832806bff3194035ff18ca01aff4c6500d7f86328067ff2194033ff10ca019ff486500cff84328016fe609400bffa84a005dfd4250027f6a128017fc509400bfc284a005ffd025002ffc8128017fd409400bfe204a005ffcc25002ffc6128017fd309400bfe184a005ffc825002ffc4128017fd209400bfe104a005bfd95500c7fec8a8062ff6454031ff322a003bf991500c7fac8a8062fd6454031fe322a003bf19150027fea8a80137f5454009ff2a2a004ff551500c6faa8a8013fc545402fffb1aa017bfd8d500bffcc6a800afe635402ffeb1aa017bf58d500bff8c6a800afc6354009ffa9aa004dfd4d50027fca6a8013fd535402fbea9aa004ff14d500bffe86a805ffe435402ffea1aa017ff10d500b7fec4a805aff625402dff312a001bf989500b7fac4a805afd625402dfe312a001bf18950027fea4a8013fe525402dbf292a004ff54950027f8a4a80137c525402dffa12a016ff909500b7fa84a805bfc425402dff992a016ff8c9500b7fa64a805bfc3254001ffb0aa000bfd8550007fcc2a8003fd6154001fe30aa000bf18550027fea2a80137f5154009ff28aa004ff54550006faa2a8013fc5154031ffa0aa018ff905500c7fa82a806
  | 3 => 0x770ad816216a60d08bc03c0000000000018ce680000000073800000000000018000000040480300400400000000000048010140180380300000006004004014010010200000000200000000000000004080030000000180a002004008060000000180000000400004000000008040060100000000401800800000008008000060000080000e0080300200600000000008004008010000000000000000c00000002004030000000000000001000c010050000000000101400401801000000010000000040080000000402000016020008010020500000000000800800004000048050000000080100a0040000100a00000002000000030010080200000001000c008010060200180600601c020320000200000000c01c0100200c0040500000200001001000084030040000080000000400000001012004068020080140280b004000068000100080000600402801805002010040030040140080400a00800001004008040030020100400100a00000800000000010000020380000000a0000000a0000040200200000002804025facb28887ff64944437fb24a221ff9925101dfcc928887fd64944437eb24a221ff1925101df8c928813ff5494409bfaa4a204ff95251027faa9288877d5494409fe2a4a220ffd8e51105fec728883fe63944057f31ca220ff58e51105fac728883fc63944057e31ca204ffd4e51026fea728813fe5394409fea9ca220df54e51027f8a728883ff4394441ff21ca220ff50e51107f8872887fff629443f7fb14a21fff98a5100dfcc52887ffd629443f7eb14a21fff18a5100df8c528813ff5294409ff294a21fdf94a51027faa528813fc5294409be294a21fffd0a510fffc852887ffd429443ffe214a21fffcca510fffc652887ffd329443ffe194a204bf98651027fea3288137f5194409fba8ca204ff14651027e8a328887ff4194443ff20ca221ff5065110ff88328883ff3194441ff18ca220ff4c651107f8632887fff219443fff10ca21fff486510fff84328803ff6094401ff304a205bf98251007fac128802fd6094401fe304a204ffd4251027f8a1288137c5094443ffa04a221ff9025110ffa8128887fc4094441ff984a220ff8c251107fa6128883fc309443fff904a21fff882510fffa412887ffc20944097fb2aa21effd91510f5fec8a887bfe64544077f322a21eff591510f5fac8a887bfc64544077e322a204ffd5151027fca8a8813fd5454409fe2a2a21dffd8d510edfec6a8877fe63544057f31aa21dff58d510edfac6a8877fc63544057e31aa204ffd4d51027fca6a8813fd5354409fe29aa21dffd0d510effc86a8877fd435443bfe21aa21cffd89510e5fec4a8803ef625440177b12a21cff9895100dfcc4a8873fd62544397eb12a21cff1895100df8c4a8873ec625440376312a204ffd49
  | 4 => 0xa6b38001bb3a40000000408a000791bd036000c2800526000338000006787c9990fc7e49eaab2580bd568803e47ec0029700051c5d2b400000000000000000898b5546594001ef00000150a650561440000000000000000112a390da8401a1dc001933ec0018380000029c000c339c4787629c5342a4f09df5be21881ab80de60c478001bc000031b6298699248001ec700001f32a40010b0bf0f04cd6000020ec0d5b00c000b689f0db46278d081a904e000e50e3000238b7805000319778c21926dd2e000000000000000dc000000000008b4000000007580000020400093a07000baceb800120410a304f0000009b8002f4b20000e62c000008af70000000000025c0009c99b000060a800037c0000000039e0000000019e000001642320000000000000d0300038e000000000640012715f0ba0000022458e000000004fe000d010e07eb9c001d1000000001965660008f95e1542201e8c41e03f405994076aa4209610b6270830220002a00027a000508000152eaa44c530b0eca6d05a99358b946006a4de4847982600000109acc4520002d15d1fc984000dc0000016b90a00019000000000afc00000000a340011446a000002680000008a8003e20005c16a000bcd132410005ec00000042000000000465598723f000528b191b00e760d2a051b27f92297d43a414f590f34e154e12c6000000f4aff000000002fa5c299c002b2000c10f10d04465608b94d2f2a24da0000004d4000ea146598001c822267c5c800000000000000005c0000000000b4001b000000000171000000210000f4000dc0000000014406601e070941574380953609e3f83d10f000630000b12f1000b80002014eeb882216b02e328c3000000b092a8bd2e40000019d00000009177108075889f54b4a540002900000000000288000000003885b4199aa1c296d8a8001906255e0000000001a000372000001ad47ca0517a3c54a998778ab0008e9230001e2001769da00049504a1729c13812300256001108da00048017000624b296d800074001439840500001c13b1f60000011c330920000001d0000003024180010c0094a400000000060a2958a2b1763dd26acd3660016e0001fe000002365d2000c7800000af9401cb0008e1412f51d2244c90002921b400250000988a5af61aa04c00181304950002b537e5f0001af38c001502304401c87c08a16e4c1698000005045f2e400000096800450550a1aee5aa4f069800098284000365ac00000000000401018e24647980006251e5443880054c5692f191588c2800000000bc17189d01c7b05627b4d40000007d576c3408000000000000000900000000041c5640000000018021af95fc000002a85f879cea87415a6316799a4da74c0d2004f81b188008516000000690003e8002c152c0009907c0b226800000000
  | 5 => 0x9d80020862e0014829f1ac00142abd414498fbac93f0129261364889c97313f2e8b2c0105710200123b080004e0fd0002468540025910ec05320001a8809419535247d0000543dc4600f800000b64001ab000001618012ce00052000422000000000000010c8000007640023d0d00016826e4761ec002dd0008e400000000000ef0003feae91a0b3000194001120000000031f0004904a800000000290000000005725700021400000000000e4a0d4545e18d21a1d6064bf89962835d580006389440000021a0a98f0000e07a0dd0731289814f0d10000000000000000134ade000000000004d6000001314447f4002ac00024c7a8000007915380049e0004b0000006d48d2d24a69d4b71804f21d40000018eba0268003a04bc58a714c6b50001c50000e4000af08c0dc0019c2ec000a289232a000e62700a08509a0004fa0000016922c975161db3488956c00000062184800000000000000000017500013eb44000cd31aa500000016865d0780000022c6fafd29ebec0007f0620000009842417823ab75720013a1a300000000000000000c58b608032d8780000070c0527e000404258000000012503e1042349483c1b00b0000001360002e035000c14f80d20000000028600029400000000abc91061000160d40a655c0007e29d0006397c000000000000140000000008c220a900000054400000000000000d92330be90c9524b12e0002b2371400017a000164bc93c1ea0002c0ae306218750000001dc4e835a8c4080000000000000000079000000002c53da2890fa2e0006c4000000005f800187344339761553c0374729bc3200008e8000009ccb9a580000000030c0006b8f28001c03b58b16c000000000830000000031900000155108382000000c50009587204919842460800000c74a01dd636000b402000089c003130005212100000000120000000000000000000000025f0
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c10006df4258c10006de4258c10006dd4258c10006dc4258c1003edf7158c10006de7158c1003edd7158c1003edc7158c10006df5158c10006dc5158c10006df4158c10006de4158c10006dd4158c10006dc4158c10006df2158c10006de2158c10006dd2158c10006dc2158c1002edf7058c1002ede7058c1002edd7058c1002edc7058c1002edf5058c1002ede5058c1002edd5058c1002edc5058c1002edf4058c1002ede4058c1002edd4058c1002edc4058c1002edf2058c1002ede2058c1002edd2058c1002edc2058c1002edf1058c1002ed71058c1002ede1058c1002edd1058c1002ed51058c1002edc1058c10006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810036ef7158810006ee7158810036ed7158810036ec7158810006ef5158810006ec5158810006ef4158810006ee4158810006ed4158810006ec4158810006ef3158810006ee3158810006ed3158810006ec315881002eef705881002eee705881002eed705881002eec705881002eef505881002eee505881002eed505881002eec505881002eef405881002eee405881002eed405881002eec405881002eef305881002eee305881002eed305881002eec305881002eef105881002eee105881002eea105881002eed105881002eec10588100acff769441002cfe7694410024fd769441002cfc76944100267e65944100067d659441010ebe6494410006bd6494410106de6394410006dd63944100feee6294410006ed629441002dfa7094410005f970944100acff76544100267e65544100067d65544100f6be6454410006bd64544100eede6354410006dd6354410005ef7254410035ec72544100e6ee6254410006ed625441002dfb7644010006fb7644010004fb76440100077b754401000778754401002f7a654401002f796544010007bb744401012fb8744401002fba644401002fb96444010007db7344010127d8734401002fda634401002fd96344010007eb724401011fe8724401002efb624401002fea624401011ef9624401002fe96244010006e9624401002dfb714401002ff37144010116fa614401002ff26144010007f25144010007f15144010
  | 1 => 0x4110007bb64c411013fb864c4110007db63c4110137d863c4110115fb72c4110115f972c4110007eb62c4110147e862c411002dfa71c411002efb61c411002ff361c411013ff241c411013ff141c4110137f231c4110137f131c411002e7f7559410004ff745941001cfe7459410004fd745941001cfc745941004e7f54594100067e54594100067d545941004e7c5459410004ff7359410014fe7359410004fd7359410014fc735941004e7f53594100067e53594100067d535941004e7c5359410004ff725941000cfe7259410004fd725941000cfc725941004e7f52594100067e52594100067d525941004e7c5259410024ff7159410024fd715941004cfc715941004e7c515941002cff705941002cfe705941002cfd705941002cfc705941002e7e505941002e7c50594100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067d42594100067c42594100067f32594100067e32594100067d32594100067c325941004e7f71594100067e71594100067c71594100067f41594100067e41594100067d41594100067c41594100067f31594100067e31594100067d31594100067c31594100067f21594100067e21594100067d21594100067c215941002e7f705941002e7e705941002e7d705941002e7c705941002e7f405941002e7e405941002e7d405941002e7c405941002e7f305941002e7e305941002e7d305941002e7c305941002e7f205941002e7e205941002e7d205941002e7c205941002e7f105941002e7e105941002e7d105941002e7c1059410006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006be5259010006bd5259010006bc5259010006bf3259010006be3259010006bd3259010006bc3259010046bf7159010006be7159010046bd7159010046bc7159010006bf5159010006bc5159010006bf3159010006be3159010006bd3159010006bc3159010006bf2159010006be2159010006bd2159010006bc215901002ebf705901002ebe705901002ebd705901002ebc705901002ebf505901002ebe505901002ebd505901002ebc505901002ebf305901002ebe305901002ebd305901002ebc305901002ebf205901002ebe205901002ebd205901002ebc205901002ebf105901002eb7105901002ebe105901002ebd105901002eb5105901002ebc1059010006df7558c10006d
  | 2 => 0x66dc71d8d10006df51d8d10006dc51d8d10006df41d8d10006de41d8d10006dd41d8d10006dc41d8d10006df21d8d10006de21d8d10006dd21d8d10006dc21d8d10006df70d8d10156de70d8d10066dd70d8d10156dc70d8d10006df50d8d10156de50d8d10156dc50d8d10006df40d8d10156de40d8d10006dd40d8d10156dc40d8d10006df20d8d10156de20d8d10006dd20d8d10156dc20d8d10156de10d8d10066dd10d8d10156dc10d8d1005dee76d891005eee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910007e641d8910007e541d8910007e631d8910007e531d8910007eb70d891005fe870d891014fe610d891014fe410d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef74d8910006ee74d8910006ed74d8910006ec74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d891014eef71d891005eee71d891005eed71d891005eec71d8910006ef51d8910006ec51d8910006ef41d8910006ee41d8910006ed41d8910006ec41d8910006ef31d8910006ee31d8910006ed31d8910006ec31d8910006ef70d891014eee70d891005eed70d891014eec70d8910006ef50d891014eee50d891014eec50d8910006ef40d891014eee40d8910006ed40d891014eec40d8910006ef30d891014eee30d8910006ed30d891014eec30d891014eee10d891005eed10d891014eec10d8910094fe76945100067f65945100267c6594510006bf649451010ebc6494510006df6394510106dc6394510006ef62945100feec629451002cfc76545100067f65545100267c6554510006bf64545100f6bc6454510006df63545100eedc6354510005ef725451005dec7254510006ef62545100e6ec6254510005fb705451002df87054510024ff7654110074fd7654110024fc76541100067f65541100267c6554110006bf64541100c6bc6454110006df63541100bedc6354110006ef62541100b6ec6254110005f77154110005f4715411002ff010541100067f65c41100ae7c65c4110006bf64c41100a6bc64c4110006df63c411009edc63c4110006ef62c4110056ec62c411002df671c411002ef761c411002dfa76c411002efa76c411002cfa76c41100077b65c41100077865c
  | 3 => 0xc64195100073c64195100063c64195100067f63195100067e63195100067d63195100067c63195100075c63195100065c63195100067f62195100067e62195100067d62195100067c62195100076c62195100066c62195101667f61195100077641195100077541195100077631195100077531195100077a201951000779201951016776101951016774101951006dbe76d911006ebe76d911001cbe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100079c63d91100069c63d9110006bf62d9110006be62d9110006bd62d9110006bc62d9110007ac62d9110006ac62d911015fb771d911006fb471d9110007b631d9110007b531d9110007ba20d9110007b920d911015fb610d911015fb410d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006be52d9110006bd52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d911015ebf71d911006ebe71d911006ebd71d911006ebc71d9110006bf51d9110006bc51d9110006bf31d9110006be31d9110006bd31d9110006bc31d9110006bf21d9110006be21d9110006bd21d9110006bc21d9110006bf70d911015ebe70d911006ebd70d911015ebc70d9110006bf50d911015ebe50d911015ebc50d9110006bf30d911015ebe30d9110006bd30d911015ebc30d9110006bf20d911015ebe20d9110006bd20d911015ebc20d911015ebe10d911006ebd10d911015ebc10d9110065de76d8d10066de76d8d10014de76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10006df62d8d10006de62d8d10006dd62d8d10006dc62d8d10007cc62d8d10006cc62d8d10157d771d8d10067d471d8d10007d641d8d10007d541d8d10007da20d8d10007d920d8d10157d610d8d10157d410d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dd42d8d10006dc42d8d10156df71d8d10066de71d8d10066dd71d8d10
  | 4 => 0x4210175f972c421002ff271c4210024fe76d95100767e65d9510006bc64d9510006dc63d9510006ec62d9510004ff74d951001cfe74d9510004fd74d951001cfc74d95100767f54d95100067e54d95100067d54d95100767c54d9510004ff73d9510014fe73d9510004fd73d9510014fc73d95100767f53d95100067e53d95100067d53d95100767c53d9510004ff72d951000cfe72d9510004fd72d951000cfc72d95100767f52d95100067e52d95100067d52d95100767c52d9510024fe71d951002cfd71d9510024fc71d95100767f51d951002cfe70d9510074fd70d951002cfc70d95100767f50d95100757e76d95100247e76d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100067f63d95100067e63d95100067d63d95100067c63d95100075c63d95100065c63d95100067f62d95100067e62d95100067d62d95100067c62d95100076c62d95100066c62d95100077641d95100077541d95100077631d95100077531d95100077a20d95100077920d951016f7610d951016f7410d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d951016e7f71d95100767e71d95100067d71d95100067f41d95100067e41d95100067d41d95100067c41d95100067f31d95100067e31d95100067d31d95100067c31d95100067f21d95100067e21d95100067d21d95100067c21d95100067f70d951016e7e70d95100067d70d951016e7c70d95100067f40d951016e7e40d95100067d40d951016e7c40d95100067f30d951016e7e30d95100067d30d951016e7c30d95100067f20d951016e7e20d95100067d20d951016e7c20d951016e7e10d951016e7c10d95100767c6559510005bf745951006dbc7459510006bc6459510005df7359510065dc7359510006dc6359510005ef725951005dec7259510006ec6259510074ff75595100067f7559510004ff7459510006bf7459510004bf745951001cfe7459510004fd745951001cfc7459510006bc745951001cbc7459510004ff7359510006df7359510004df7359510014fe7359510004fd7359510014fc7359510006dc7359510014dc7359510004ff7259510006ef7259510004ef725951000cfe7259510004fd725951000cfc7259510006ec725951000cec7259510094ff7159510006f771595100acff7059510006fb70595100057e76195100767e76195100047e76195100067f64195100067e64195100067d64195100067
  | 5 => 0x4fd73d8550014fc73d8550004ff72d855000cfe72d8550004fd72d855000cfc72d8550096f651d8550096f551d8550006f76198550075f97098550005bf74585500c5bc7458550005df73585500bddc7358550005ef72585500b5ec72585500adfb7058550006f5611855002cfd7518550004ff741855001cfe7418550004fd741855001cfc741855004e7f54185500067d5418550004ff7318550014fe7318550004fd7318550014fc731855004e7f53185500067d5318550004ff721855000cfe7218550004fd721855000cfc72185500067e521855004e7c521855004e7f511855004ef6511855004ef5511855002cfe701855002cfc70185501667e50185501667c501855002c7c765455018d7f745455018d7d74545501857f73545501857d73545500076f72545500b57e72545500b57c725455017f6c72545500b56c725455017e7f625455017e7d62545500257f71545500277771545500077761545500067c61545500077461545500077b705455002d7e705455002d7c70545500077870545500267f60545500277b60545500ae7e65d97100acfd75d9710004ff74d971001cfe74d9710004fd74d971001cfc74d97100ae7f54d97100067d54d9710004ff73d9710014fe73d9710004fd73d9710014fc73d97100ae7f53d97100067d53d9710004ff72d971000cfe72d9710004fd72d971000cfc72d97100067e52d97100ae7c52d9710006f671d97100ae7f51d9710006f970d971016e7e50d971016e7c50d9710024ff76597100ae7c6559710005ef7259710055ec72597100067f7559710004ff745971001cfe7459710004fd745971001cfc7459710004ff7359710014fe7359710004fd7359710014fc7359710004ff7259710006ef7259710004ef725971000cfe7259710004fd725971000cfc7259710006ec725971000cec72597100ae7f52597100067d525971002cfc71597100ae7c51597100ae7f505971002cfd76947100267e65947100067d659471002dfa7094710005f9709471004cff76547100067f65547100267c6554710005ef7254710055ec7254710024ff7654310024fc76543100267e65543100067d6554310005f77154310005f4715431002e7f7559610004ff745961001cfe7459610004fd745961001cfc74596100967f54596100067d5459610004ff7359610014fe7359610004fd7359610014fc73596100967f53596100067d5359610004ff725961000cfe7259610004fd725961000cfc72596100067e52596100967c52596100967f515961002cfc705961002e7e505961002e7c5059610074fd769461016e7f65946100267c6594610024ff765461002cfc76546100267e65546100067d6554610005ef725461007dec7254610005fb705461002df8705461002df976c4210006f976c4210175fb72c
  | 6 => 0xd7094551006ef62d8151006ec62d8151004ff74d815101cfe74d8151004fd74d815101cfc74d8151004ff73d8151014fe73d8151004fd73d8151014fc73d8151004ff72d815100cfe72d8151004fd72d815100cfc72d81510aefa50d81510e5ee7298151005ed7298151006ef6298151006ec6298151006fb6098151005bf74581510f5bc7458151005df73581510eddc7358151005ef72581510e5ec7258151006ef6258151006ec625815116e7f6518151006ef6218151006ec621815102efa6018151006f960181510ceef7558a500ceee7558a501aeed7558a500ceec7558a50006ef7458a50006ee7458a50006ed7458a50006ec7458a501aeef5458a501aeee5458a501aeed5458a501aeec5458a50006ef7358a50006ee7358a50006ed7358a50006ec7358a501aeef5358a501aeee5358a501aeed5358a501aeec5358a50006ef4358a50006ee4358a50006ed4358a50006ec4358a50006ef7158a50006ee7158a50006ed7158a50006ec7158a501aeef5158a501aeee5158a501aeed5158a501aeec5158a50006ef4158a50006ee4158a50006ed4158a50006ec4158a50006ef3158a50006ee3158a50006ed3158a50006ec3158a5002eef7058a5002eee7058a5002eed7058a5002eec7058a5002eef5058a5002eee5058a5002eed5058a5002eec5058a5002eef4058a5002eee4058a5002eed4058a5002eec4058a5002eef3058a5002eee3058a5002eed3058a5002eec3058a5002eef1058a5002eee1058a5002eed1058a5002eec1058a50004ff749865001cfe7498650004fd749865001cfc7498650004ff7398650014fe7398650004fd7398650014fc7398650004ff729865000cfe7298650004fd729865000cfc729865002ef671986500aef651986500aef55198650006f64198650006f54198650006f63198650006f5319865002cfe709865002ef6109865002ef41098650004ff745865001cfe7458650004fd745865001cfc7458650004ff7358650014fe7358650004fd7358650014fc7358650004ff725865000cfe7258650004fd725865000cfc72586500767f52586500067d525865002ef77158650076f65158650076f551586500767c5158650006f64158650006f54158650006f63158650006f5315865002cfc705865002e7f505865002e7d505865002ef6105865002ef4105865016e7f64946501a67d649465016e7f639465019e7d63946501957f72946501957d72946500fe7e629465016f6e62946500fe6e629465016f6d629465016e7c62946500257e719465002776719465016f7661946500067d619465016f75619465016f7a709465016d7d70946500077970946500267e60946500277a609465002cfd75d8550004ff74d855001cfe74d8550004fd74d855001cfc74d8550004ff73d8550014fe73d8550
  | 7 => 0x20000000180000200000802002010008000020100000000800c0100200c000000000080000000001400c0280100002c0100d00e000010000180040080000000400000018000048010000040700600600000015000000010000020000180000001000815000010018070100340380200a0200000301200c000010000000000100000400801042008018000000100200900000c0300800401c048000000000000100e0200100000e02001006002028008000080280380301a00000002036000018030000000200300a02c0180d002010000000260340100800e00c008000060000580001e004020020020000100400001403002018034008000000000980100000c0180202001401800002004000000020240a807002010010000000080300400801c0000301800405801006fb6098251004ff745825101cfe7458251004fd745825101cfc74582510767f54582510067d5458251004ff7358251014fe7358251004fd7358251014fc73582510767f53582510067d5358251004ff725825100cfe7258251004fd725825100cfc72582510067e52582510767c52582510767f5158251076fa505825116e7c5058251006fa2058251006f9205825110dbe7418251005bd7418251105de7318251005dd73182510fdee7218251005ed721825102efa6018251006f960182510e5ee76d89510e6ee76d895100cee76d89510076f75d89510e76c75d8951006ef64d8951006ee64d8951006ed64d8951006ec64d8951006ef63d8951006ee63d8951006ed63d8951006ec63d89511d7e751d89511d76c51d89511d7e451d89511d76f50d89511d6ef75d89510e6ee75d89510e6ed75d89510e6ec75d8951006ef74d8951006ee74d8951006ed74d8951006ec74d89511d6ef54d89511d6ee54d89511d6ed54d89511d6ec54d8951006ef73d8951006ee73d8951006ed73d8951006ec73d89511d6ef53d89511d6ee53d89511d6ed53d89511d6ec53d8951006ef43d8951006ee43d8951006ed43d8951006ec43d89511d6ef71d89510e6ee71d89510e6ed71d89510e6ec71d89511d6ef51d89511d6ee51d89510e6ed51d89511d6ec51d8951006ef41d8951006ee41d8951006ed41d8951006ec41d8951006ef31d8951006ee31d8951006ed31d8951006ec31d8951006ef70d8951006ee70d8951006ed70d8951006ec70d89511d6ef50d89511d6ee50d89511d6ed50d89511d6ec50d8951006ef40d8951006ee40d8951006ed40d8951006ec40d8951006ef30d8951006ee30d8951006ed30d8951006ec30d89511ce7f64945511ce7d64945511c67f63945511c67d63945511bd7f72945511bd7d72945510076f62945510fe7e62945510fe7c62945511b76c62945510fe6c62945510257e71945510277671945510267f61945510277761945510057
  | 8 => 0x99e2827a3903b05d00023e80003a889a18a840359391b488b9de0000318000001298001fb93a9ea00021d8dd00000015b1aa9cb9249d68e182698888d99e0001a18178d212600015000003c8000001948000000001780001970001898002228dc9978b29852830000e500003c28ea739b880280000000619e9718282098000001d900000028b8000baa35249163084a428000000cd06e80017f271917935a7586582b1c519a8ea8000a400000014a2502789a49089b201500000006f0528001e11a22309341c29ed02b9f09559a08e31f18000000002688ee80011b9d000027990400016401a8000001120f60000e40d5a10165195198a6711800009f8001c785400019f1cda240000000000000a480000023a0260c18001d88000000000000002860000000000000a58000970ec2169f99191ec0e38efa820168c90000a70000bf0fd0001b184896a0c515615aa5a80025d22c07b00000029000013884080013800000012000024500000000000028e22303d247053216227a220010001e302a80025f80000000000000000000004a21389604100008296e0000ed0e10e00a380027725e1628fd9e810101ca760518d821780000000f0001a380010a109a618819598e580027aa058051d580008725c19a0e2a5e8bb8001a583791a0001b300926b871a589b58000249b60000119b6a7c8001fe1648d320212d1149bf15921d00d0830fc098a5393f8000908000d50ca00000000021b2418002498dd8f1993a7304f26d9bb8df22d83617b00021a89c9998000000df86a9a5000000288979a399488001cc0b798e8000ff8001c20000000000d107f9310000001cb0001218000000000ad234a6b0000000490000001940740000000000c60001c01b500000019c05481a154958a4e00028280028016f9b080003b8002291e00668c988114f800000000091269a782530000001e48000000fb050a0f981a2c93180000000011a8000000001721228b61bd869a4626506480026380181000a014048000000040580d0320080b80c002028088030040080180d0180540500200200000004012000000010040000100500c00000004002000000000080080080700000c0000f0000000000000200802808000000000000080000100000002c00000006008020020000040000c00a008008080060200781200400804801000004008020000080480003a00c008000080080100001001c000080000080000100400005004000008060060200080000000000400808000000010010060100380100000c0200001200c0100200e0080100c0080180000200c010068010040000280e0040040102a00602000006004004068090020000300100400800803002004080010020040100300e0081500000200801802000020000030000040180500a0040b805000004018060
  | 9 => 0x1cd00010787c8020000001b70208000000a08748000000678c30000d9143879a910000992678030001872811d101c1140000c08002159618000000000000000bf80000000015e21c89d8fb94b8729929c380000014f2459bd09e9f79c988c14aa0626683080010d00011d09d1750000000188b99fc1b784787300000006b0c2800008000284a5b26800000010385b2710bc80000000000009a1bb0000000001ee07f117000019800000100a77a8395384a9cf80000000000000024200016205f8000002478000000000a51dc82a02210014723114180a86b90f9b1096930a1291b0ca9a413e81205c02d0cda4c8550b59250e09b98000002728e9a1800f911a2e1ad08005d86d1490000c780000000000022a99b85708f07c06001593285c80000022099584f98d9d282900d800172990a661101b28f68000001449110a11c6a3d91c0001188001610a90048db80027b03480008d00022580e8000001f881d8f280012a8d7a400000000e723c00000000006720880012f97a0c38211da00016894ea518000ea1569fda041e88001fe99d8621518000d607b80000000000010f1ee97e8001198001e61790000cb80010da3a92c27a0000000751430001c09b415c0000000001030001d221f8000099df80000001b9458dc27d8088bd1109d705117a86a0110001eda850000001920000fa8d8a809ab09300c80001411e0ac9e215c8002260001289c6063166a5a04c9b800010b8000000298890000f782e8001aca560001d303e00000019302f00016780016900028a17700000022f00000021300000000012a16c80007e0521530daa8c1f31e0a4880008580020d0000000fe9bf80000000023f04580000000016c20689201800010b1d38000001788001d79a82768d28a808c80000000080002c1540a993d8000711f5014a2524c0608000000860948499602008000000001a28000f71028001ef9279460e88000d08a6057a090701c300000000000000000000004624d8b08cf04209580023400000000011f80005f004176000078a328000002590000000350002630888001a88000000000000000918e909e26589296da410000ae0000000b180020e8160001572629212442579b39ae25f21e0000000af0c58448d390c26c80000000012080011c9980f006c259838264a28a5c9ce0de8ff00016f16e8130610310682748000c80538002542148000000000b41afa2f83324e83405e12f240a0b0b122b0c69f6270a72136a4d2449021671961d09ea801a4380021e8852298001dc00017e00010a9ae8000480689ca09b1f900026f1401eb8c70c49e59699df06502019d09b800000112a2d1dd8002271c41b000000020c90e9880001fc8001658881bc22a05686c84380000000018f17c85b8001a90000000c11f29f00ad8d48138da21b9dba1995a13
  | 10 => 0xd1a0a8b38759af0b4845281a372201258f111d8d1a362378002859e9a4b9268338001be0d72000000628001f5a12260a3b0001a31cf00002f800000183a3b8000778560b69e78000001ce80012804d0001059969ad8000a32791d980003007700000027d02e18f80000000024306415da8808a9421c89db0e22551f69ab97680000000a113a048f08d41300001868bda0703da0e27b8001d808680000019100025100023880020c0368000000c000000012900c00004d8000000be80015099b000000258235a1126c00000000007d1f20000000058a1a3c80786180015b83f8e79468bc0ba17780003900000010e0000b82239608000428f818c0588b013e0000238000592621411520000001160000001480000f500000b80000026e0000000be03280000000017400000005018d1eb13618499014400024b00005a80026910194780013d0808000aa00000000000023e00000011690900007d80000023d1730001ec8eb05a11f2028a207a14c8000b918c94e0440db0ab0e69daa5d9d60002898a89e18879a714515d21928da61151028a3f9a78950691fb0a696d1810ef0a025693b82700023693a0000000068001fa9d400000004c0e48eb96b80000001000009c0c880000000014280000000000000014d22b87095798a93c8b88aaa571890000000000000000001069f81e3800180a7f9270ac09a8ab9918ec94d81d1dea0500012e0000242150cf98b9660fa0001f480003716808a13712401700008f975a332141338000002529821331859ca81fa0f0f3a6a97d00006394b26fa038ce800149973a508b200010812e9528a7a701d503e98405ea321fa08ea8f00012b01e0000999fd0d024a94c28fa0d98296b137a1f00000002197d88e0e601b0a280000004e0ed876a33839a2ea86a5581e97c12200000000009f0001860002109a60cc80022188b00012380015f254a6d25b8001e68001060e800020316386f97004e9151c58000fe0939f41c903206d8c41cc82c80000026a0000fc974a7f0001e51ff9802171130001f10002480f904b80000000006600006e226a078000000738ce0000001e70001e40001e91b900000b1ac1159bc80028b10c8001048838128002318000001a680004300008200000015f8002878000f980012b8000941c128aa4a27e9a121c04009000393492c9f70000000000bb00000e00000000000000019913500000024f8f5a0800000000000000013220109782500022480000000010529099f8599c80720780471be8000ee00024f1c48001a00f88aea7421a0b50b3246a0a0cc18795e97f93c2520070389d4a8c8000d98f222807a9c181084193f02d80017b80000000000013b0580001f380000000000003f27c09828904b1ef00026018a00002318b0c223807918e1ba0000001832640cb221230055a871aa
  | 11 => 0x20b95500000003a0000000840f30afa8d00000019c91e800000107025a11822a7e00017092d9230000000002750000000de0191dd00007607ea018b700001f0000001ba80000026e8000f495804696a8001408d68f41a99711ff1c71
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xace821d5630400159b043aac60800297a147458c100052ec28e8b182000c9d741d1630400159d043a2c608002b36087458c100070faa4a8b1820008de8715163040011bb0e2a2c608002b3a085458c1000566c10a8b182000a5e851c963040014bb0a392c608002a7a107258c100054ec20e4b1820008de8714963040011bb0e292c608002a7a105258c100054ec20a4b1820008de8710963040011bb0e212c60800297a144258c100052ec2884b18203cad9809c5630400b5b50028ac608002b66005158c1003c6f43e82b1820008dd87d0563040014bd0ba0ac608002976174158c100056741682b182000acd82d05630400b5b50020ac608002b66004158c100052fc2a42b182000a5c8548563040011bd0e10ac6080023761c2158c100052f42842b182000a5d85085630400153d0810ac608002a76102158c1002d6d40042b182000ad980085630400155d083aac408002ab610755881000567418eab102000acd831d562040014dd0a3a2c4080029b614745881000567418e8b102000acd831d16204001c5ea92a2c4080023ba1c545881000476c38a8b102000ace83151620400159b062a2c4080029ba14735881000536c28e6b102000aae841cd620400155b0839ac40800393d4e535881000477438a6b1020008ed8714d620400155d0829ac408002ab61053588100047743886b1020008ed8710d62040014dd0a21ac4080029b614435881000746a1886b10203bae9809c5620400b5d50028ac408002ba60051588100347743e82b1020008ed87d0562040014dd0ba0ac4080029b61741588100056741e82b102000acd83d05620400b5d50120ac408002ba602415881002d7540082b102000ae980105620400d1dd0f98ac4080023b61f31588100053742e62b102000a6d85cc5620400155d0998ac408002ab613315881002d7540462b102000ae9808c5620400b5d50018ac408002ba600315881002c3fc3acb2882005cea7058a51040018f2cab84a2080033a589709441000636392caa882000cac725915104001998e4b1aa2080723b61b72544101d63732ee4a882000c6d65dc9510400195cc9b92a2080032b59372544100066731ee4a882000ccd63dc951040011dd0eb12a20801a3b21d62544100065c3a6ec8802000cd873dd910040019d0e5bb220080031ee1776440100063c42eec8802000cbb84dd9100400197109bb2200800336e0f76440100066c41eec8802000ceb82dd910040019d105bb220080031eddb75440100063dbb0ea8802000cbb76dd110040019b6edb9a20080033addb72440100057543ac48802023ae8875891004001cd6eab1220080039a1d5624401000755ba2c48802000ea8745891004001d96e6b122008003b21cd624401002e75b8ac48802005ee3715891004001dc2c528a2008003b85895144010
  | 1 => 0xb07a0ec4880a63ba1f31d891000476c3e63b122000a6e85cc762440014db0b98ec488002aba1331d891000556c2663b122023ae681dc362440018d8e5b2aa2880b71e1c3655451000656396c8a8a2000ccc72d8d514407f1dd0db92a2880031bd9772545101d63632ee4a8a2000caf64dc95144001958c9b92a28800333d8f72545100066631ee4a8a203e8ee87d8951440531d90fb12a2880031dd94715411016e3d3b6cb8822004c7a761971044057974edb2620880ab369db63c411014e753b6c5882200587e87951650400187ee92a2ca080161f21d545941002c3f43ca6b282000c5f7394d650400b0f90ea9aca080161fa1e525941002c3e43aa4b282000c3f749d165040014bd063a2ca080029760c745941000537410e8b282000a6d821d165040018bee739aca080028fa1073594100051ec20e6b282000a6e821cd65040014db0439aca080021fa1c43594100043ec3886b282000e1d4310d65040014dd0421aca080029b60843594100051f420e4b282000a3d841c965040014bd06392ca080029760c72594100043f43884b28200087d8710965040014bd06212ca080029760c42594100043f43864b28200087d870c9650400147d08192ca080028f610325941004c3f43e82b28200087d87d0565040014bd07a0aca080029760f41594100053741682b282000a6d82d05650400b4f50020aca080029e600415941004c3f43e62b28200087d87cc5650400147d0998aca080028f61331594100053741662b282000a6d82cc5650400b4f50018aca080029e60031594100043fc3a42b28200987c8748565040010fd0e10aca080021f61c21594100051f42042b282000a3d8408565040014bd0610aca080029760c215941002d3d40042b282000a7980085650400187eeb3aac808002a7a0c75590100054ec18eab202000aae821d5640400155b043aac8080028fa1473590100051ec28e6b202000c9d731cd640400155d0439ac808002ab60873590100070fa9ca6b2020008be8714d640400117b0e29ac808002aba08535901000556c10a6b202000a3e851c9640400147b0a392c808002a7a0c72590100054ec18e4b2020008be87149640400117b0e292c808002a7a0c52590100054ec18a4b2020008be870c9640400117b0e192c8080028fa1432590100051ec2864b20203dab9809c5640400b5750028ac808002ae60051590100445f43e62b2020008bd87cc5640400147d0b98ac8080028f61731590100055741662b202000aad82cc5640400b5750018ac808002ae60031590100051fc2a42b202000a3c85485640400117d0e10ac8080022f61c21590100051f42842b202000a3d85085640400153d0610ac808002a760c215901002d5d40042b202000ab98008564040018beeb3aac608002a7a107558c100054ec20eab182000
  | 2 => 0x254d8d100046f438a9b1a20008dd87153634400159d042a6c688002b360854d8d100052f42ce5b1a2000a5d859cb634400153d09396c688002a761272d8d101556d400e5b1a2000ad9801cb63440011bd0e296c6880023761c52d8d100054f420a5b1a2000a9d8414b63440011bd0e216c6880023761c42d8d100052f42885b1a2000a5d8510b63440551bd0fa0ec6880023761f41d8d100052f42e83b1a2000a5d85d07634400159d05a0ec688002b360b41d8d100052fc2a43b1a2000a5c8548763440011bd0e10ec6880323761c21d8d100052f42843b1a2000a5d85087634400153d0810ec688002a761021d8d101556d40043b1a2000ad98008763440495ad03b86c68800237a1f20d8d100046ec3e41b1a2000a5e85c8363440014bb0b906c688002a7a1320d8d100054ec2641b1a2000c6e76d9762440011db0f32ec4880029ba1665d891000557424cbb122000aad84997624400159d0732ec488002b360e65d891000477c3acbb122000aaf84597624400155908b2ec488002b3e0d65d89100056641acbb122000a6e8619762440018dcec32ec4880032b9db64d891000717b2ec9b122000e2c65d9362440011db0f326c4880029ba1664d891000536c2cc9b122000aae84993624400159d07326c488002b360e64d891000477c3ac9b122000a6f8559362440014d90ab26c488002b3e0d64d89100056641ac9b122000aae86193624400195cec326c4880038bd9464d891000716328c9b122000ea581193624400199cedb1ec48800393d9763d89100072632ec7b122000e8f64d8f6244001d18c9b1ec4880023b61e63d89100053742cc7b122000a6d8598f624400155d0931ec488002ab61263d89100056741cc7b1220008ef8758f62440014df0ab1ec4880029b21563d891000557c22c7b122000aac8458f624400159d0c31ec488003339d863d891000727b28c7b122000e4c6518f6244001d1ec831ec488003a319063d891000762c08c7b122000ea46490762440535c90ca0ec488003b118e31d891014d7243263b12200baea86dc3624400155d093aec488002ab61275d89100056741cebb122000acd839d762440014dd0b3a6c4880029b61674d89100056741ce9b122000acd839d362440835cd023a6c4880a6b960474d891000717aa4a9b1220008ee8715362440011db0e2a6c488002b3a0c54d891000566c18a9b122000a6e859cf62440014db0b39ec488002aba1273d891000556c24e7b122040ae6811cf62440535cb0239ec48800393d4e53d891000477438a7b1220008ed8714f624400155d0829ec488002ab61053d89100047743887b1220008ed8710f62440014dd0a21ec4880029b61443d891000746a1887b1220298ee87d0762440011db0fa0ec4880029ba1741d891000536c2e83b122000ace83d07624400159
  | 3 => 0x7b222000aac8258f6444001c3eca31ec8880038719463d91100074ac08c7b2220008bd8798b644400147d0b316c8880028f61662d91100054f41cc5b222000a9d8398b644400117f0eb16c8880028fe1562d91100051e42ac5b222000a9f8358b644400153906b16c8880038bd9462d911000716328c5b222000e8c6318b6444001d5300316c888003a518e31d911015d5a43263b222000ea862883644400153d073aec888002a760e75d911000557414ebb222000aad829d7644400187aea3aec8880028fa1673d91100051ec2ce7b222000c9f739cf644400155d0539ec888002ab60a73d911021d5b408e7b22202bab5811cf6444001c3ea729ec8880022fa1c53d91100045ec38a7b222000aae8214f644400155b0429ec8880028fa1672d91100051ec2ce5b222000a9e839cb644400153b07396c8880aeaea0072d91100055cc00e5b2220008be8714b644400117b0e296c888002a7a0c52d91100054ec18a5b2220008be870cb644400117b0e196c8880028fa1432d91100051ec2865b22202b8be87cc7644400117b0f98ec8880028fa1731d91100051ec2e63b222000aae82cc7644400155b0598ec8880028fe1521d91100051e42a43b2220008be87087644401b17b0e10ec8880028fa1421d91100051ec2843b222000a9e83087644400153b0610ec8880aeaea0021d91100055cc0043b222025ab681dc3644400117d0f906c8880022f61f20d91100051f42e41b222000a3d85c83644400153d07906c888002a760f20d91100062f3b6cbb1a20008dd8799763440014bd0b32ec688002a7a1265d8d100054ec24cbb1a2000ace82997634400159b0532ec68800237e1d65d8d100054fc22cbb1a2000a9c84597634400159f04b2ec688002b320965d8d100052f430cbb1a2000c5e76197634400193cedb26c68800387d9764d8d100070e32ec9b1a20008dd8799363440014bd0b326c6880029761664d8d100054f424c9b1a2000ace82993634400159b05326c68800237e1d64d8d100052fc2ac9b1a2000a5c85593634400159f04b26c688002b320964d8d100054f430c9b1a2000c9e761936344001c3eca326c6880038719464d8d100074ac08c9b1a20008dd8798b63440014bd0b316c6880029761662d8d100054f424c5b1a2000a9d8498b63440011bf0eb16c68800297e1562d8d100052e42ac5b1a2000a9f8458b634400153908b16c68800393d9462d8d1000726328c5b1a2000e8f6418b6344001d18c8316c688003b260062d8d100074a32483b1a202aad4865076344001d90c5106c688002a7a1275d8d100054ec24ebb1a2000ace829d7634400159b053aec688003175d475d8d100052f42ce9b1a2000a5d859d3634400193ee93a6c688002b3a0a74d8d1000566c14e9b1a2042ad6811d363440555ab023a6c68800387d5
  | 4 => 0x5440890ff0e90eca880b61f21d21d95100043f43843b2a200e87d87087654400147d0810eca880028f61021d95100052f41843b2a2000a5d83087654405b4f50010eca880029e60021d95100043f43e41b2a200087d87c83654400147d09906ca880028f61320d95100052f41e41b2a2000a5d83c83654405bcd040906ca8800e2fa1b74595100061e32ee8b2a2000c9c731916544001958e4322ca8800a37a1b73595100062e32ee6b2a2000c9c64dcd654400193ee831aca88003271d0635951000666390c6b2a20018ee86dc965440018d8cbb92ca880032b19372595100066631ee4b2a2000caf741896544001958e8312ca8800333dcc625951000666398c4b2a20038be87dd1654400187eebba2ca880021fe1574595100046fc1ae8b2a20028dc835d165440011df04ba2ca880063b20974595100045f438e8b2a2000c3f751d165440051bd0fb9aca8800317dd773595100064fba6e6b2a2000c9c74dcd65440010ff0ab9aca880022fe11735951001c5e422e6b2a20008ef825cd65440031d904b9aca8800237a1c73595100062fba8e6b2a2000c9f741cd6544001938e839aca880063ba1f725951000637baee4b2a2000caf74dc96544001958e9b92ca8800333dcf72595100066639ee4b2a200087f855c9654400117f08b92ca8800e2f21172595100046fc1ae4b2a20028dc835c965440011dd0e392ca880031bdd4725951000657ba0e4b2a2000cac741c9654400199ee6392ca88003331cc72595100043ec3cc832a2000a5e8399065440014bb07320ca880029ba0a641951000536c14c832a200087f8759065440014bf06b20ca880029720d641951000537c12c832a2000a6c825906544001c6b02320ca880021f61e63195100051f424c632a2000a3d8498c65440014dd05318ca880029b60a63195100043fc3ac632a2000a3f8458c654400147908b18ca880029be09631951000536412c632a2000e1c6418c6544001cab02318ca880021f61e62195100051f424c432a2000a3d8498865440014bd07310ca880029760e62195100043fc3ac432a2000a3f84588654400147908b10ca8800297e0d62195100052e41ac432a2000e2c641886544001c98c6310ca880039a60062195100071a3248232a202ca74865046544001ca8c7188ca880b29d2193119510007343144032a2000a7886480654400187cedb2ec8880022f61e65d91100051f42ccbb222000a9e83997644400153b0732ec888002aba0a65d911000556c14cbb2220008bf87597644400153f06b2ec888002a720d65d911000557c12cbb222000aac82597644400147d0c32ec8880030f9d865d91100045ec3cc7b222000a3e8598f644400147b0b31ec888002aba0a63d911000556c14c7b2220008bf8758f644400147f0ab1ec8880028f21563d911000557c12c
  | 5 => 0x80d69ba173158a5000536c2e62b14a000aae84cc5629400155b0998ac528016baa003158a5000574c0062b14a0058f587906619400b1eb0f18cc3281121f21d525865002c7a43a82b0ca0058f4874c561940590ff0eb0ca3280023de1d61185500243e42ae430aa00087d87948615402d2dd0fb92a2a80561fa1c615455000636390c2a8aa000d6872dc151540051bd07ba6cb880023760f74d971001c3fc3aa9b2e2003c3e7455365c400717d09b9ecb880022f61373d97100143fc3aa7b2e2002c5e7354f65c40011df04ba2cb880063b209745971000477c12e6b2e20018ec825cd65c40031dd0fb92cb880021fe15725971000477438e4b2e2000c6f751c965c40030f90ea92cb880071b1c952597100fd36412cb28e200587e87d9551c40018d8e5b2aa38805a9b20965543100046fc1ae8b2c20028dc835d1658400b0f90eaa2cb0800f0f1d154596100045fc22e6b2c20038bc845cd658400b0f90ea9acb0800b171cd535961002c3f43ca4b2c2000c6c72595518400187ae92a6ca880029d60654d951001c3fc3aa9b2a2000c5d7394f65440014eb0329eca8800a1fe1d53d951000c3fc3aa5b2a2000a5e8399365440014bb07326ca880029ba0a64d951000536c14c9b2a2000a5f8359365440014b906b26ca880029be0964d951000536412c9b2a2000e3581193654400147d0931eca880028f61263d951000537414c7b2a2000a6d8298f654400147f08b1eca880028f21163d951000537c12c7b2a2000a6c8258f6544001c38c831eca880039560463d95100051f424c5b2a2000a3d8498b65440014bd07316ca880029760e62d95100051fc22c5b2a2000a3c8458b65440014bf06b16ca880029720d62d951000716320c5b2a2000e4c6318b6544001cd300316ca880038d19241d951016d3a43283b2a2000e54638c7654405b4e90c98eca880039a18a20d95100073431241b2a2000a5e839d365440014bb073a6ca880029ba0a74d951000536c14e9b2a2000c3d741d365440014ed023a6ca880b69d60474d95100051f424e7b2a2000a3d849cf65440014dd0539eca880029b60a73d95100062eb98e7b2a2000a76811cf654405b4eb0239eca880021fa1c43d95100043ec3887b2a2000e1d4310f65440014dd0421eca880029b60843d95100051f424e5b2a2000a3d849cb65440014bd07396ca880029760e72d951016d3d400e5b2a2000a79801cb65440010fd0e216ca880021f61c42d95100052f41885b2a2000a5d8310b65440010fd0e196ca880021f61c32d95100051f42065b2a2000a3d840cb654405b0fd0fa0eca880021f61f41d95100052f41e83b2a2000a5d83d0765440014dd05a0eca880029b60b41d951016c3f43e63b2a200087d87cc7654400147d0998eca880028f61331d95100053741663b2a2000a6d82cc76
  | 6 => 0x40600400000c028000000b40200001a0100d000006000018180240002f80000e00c028250040300600100200c00005000000140000020140600d01c004018000200000000c0040240380000201c0d00000a0740000607e028038050020000280704e0c01800000804c000000180080f00500002c020080100100c80b01a02c090000020000000203000c078021fa1e525825116d3d404a4b04a200a798588160944031f10e902c12891b9a149205825102e75302e4304a2008fb8758060944019d2e4b00c1288729ba1b75d89510fe373b6ebb12a2008ed87993625440159d07326c4a8802b360e64d895100477c3ac9b12a2008ed8798f625440155d0931ec4a8802ab61263d895100477c3ac7b12a21ca6e859d362544014db0b3a6c4a8802b3a0e74d895100566c1ce9b12a21ca6e859cf62544014db0b39ec4a8802aba1273d895100556c24e7b12a2008ee8710f62544011db0e21ec4a88ea9ba1443d895100536c2887b12a200e8d4310f62544751dd0fa0ec4a88023b61f41d89511d53742e83b12a200a6d85d07625440159d07a0ec4a8802b360f41d89511d47743e63b12a2008ed87cc762544754dd0b98ec4a88029b61731d89510055742663b12a200aad84cc762544019d6e1386c4a88029be1570d89510e53642ae1b12a200aaf845c3625440155908b86c4a8802b3e0d70d89510056641ae1b12a23aa6e851c362544014db0a386c4a88023ba1c40d895100476c3881b12a23aa6e8510362544014db0a206c4a8802b3a0c40d895100566c1881b12a200ae68110362544015cb02206c4a88023ba1c30d895100476c3861b12a23aa6e850c362544014db0a186c4a8802aba1030d895100556c2061b12a200ae6810c362544015cb02186c4a887e9ba1b62945510243e432e128aa200c6c625c2515445b8f0c0b84a2a88161f21572d815100c77436e4b02a21c8ec86dc960544011dd0fb12c0a88032bdd36258151006563a6c4b02a200ccf73d896054401998e7b12c0a88023ba1c625815100657ba0c4b02a200cac74189605440199ee6312c0a8803331cc625815122e373a8c4302a2008fb8758060544334dd0a3a2c5280029b6147458a5000567418e8b14a000acd831d162940334dd0a39ac5280029b6147358a5000557420e6b14a000aad841cd62940011dd0e21ac5280023b61c4358a501ad3742886b14a000a6d8510d6294001d1a8621ac5280029be157158a501ad3642ae2b14a019a6e851c562940014db0a38ac528002aba107158a5000556c20e2b14a000ace831c5629400159b0638ac528016baa007158a500cd74c00e2b14a0008ee87d0562940011db0fa0ac5280d69ba174158a5000536c2e82b14a000ace83d05629400159b07a0ac528016baa004158a5000574c0082b14a0008ee87cc562940011db0f98ac52
  | 7 => 0x9039165086a0002415cc5f4000005ae4b070993396a28c515c12204c0016934e3eca40736de0816a000000000ee2a701a001ae0d70008f58b80076e000000007445c926a1c32a0406c20d0e850d7a1f87481e8838005f233559800364cd44422b74ae3118800516e69cea0432c9e0e3000046879b1a7f000c2c00216000c9d1f8001b874cf60004c28ed2396019c5245e0c8092d1c0029243e82c0014c0002f9100000001ad8a98b000000212a40004d0a58000a6c2459800000710d2915426b7124ab61dc9497ab0a6ae5941392d5fe000000bf062cb8003590008558e800000000b40000005e8798f80e21c82c1ee4203780002f5a2000610005120215fb9256e0007e1915a01980000031cc580002c21cb2da42a637c21540a9d1fe201909db00039c832283d402c0018f000001cf000538c096d0000288f000039000d199b82a33c4c80025f70c5b0c215745c9c8e112f70ade14c8610343a1b28da6ec470c49114cc20c5c0007261a5000bb41043d012ba00025d7624669ad01c11615f8c15192c357adc4781ab2e211c4fa01000ed91308c762869b6b5e2c87601587c31813d6fa875aa1a1a819469254d87abb6c2b052bb5b0008242025046c208ef8006440005ba866fc0f16c2be000c44a300000000189aa8130a78bb9aa00eca0c32514c6329a5000000000000002b6239123206d00002a1b033a00093000484bbcb80e200072974b0408a6d94280000054098826302028958005f4ac87288f1aadf40006e00046c2d2fb3408dcba14e380d155736066c39065aa03c4b343505b75e0004331a0005e0002b1228c303d863552a2122329218c40808d607ad4c0011a5703b02c80037acc599800000000493ac71e73408b06152000540002a47c0000a01d4a8cfca2a714889d49202ce42400000000eb99fb2407600040800330000001b1000915ba052048195a78c7000d104592a446b8c198d3664badab18d376ca83eb3d1b24c0000004680019e280000be00020e3340000000580001a00401000048028020020840040300102e008008000b2020018010040000b8040580080000401200006803004038018220000000000503600400800006008018050000200002d00000400804004078000160000180180003600000001002028088000120000000c0020040201d018070018000180580080000c00009007014000000140180380000406605c0000c00400c0000801a01800000004000018090000180203401601809806008010000050000000400b0300000200c000008000000040041a80000e00c0a0290000100d8170000500000100c008020000040740a00000c00000001004004050000040080000103400c0281200e0000000800e03800000008020038120020481400400200c028230280080080000801c0381100008c020000080
  | 8 => 0x2f332ecc14a8002acc05c400f000000a101e6f2001cf9e71a8b4d2ab7564a0e12d000474001968795c4a58f29e83bad0c85a1b71a568f20846f6ad1769b45ee4e59a01827c7b478a1702adac2b9883067658d89a6d800110ae009cec0e4abc36eb498e159370c0d62b1f35a0006d94f1861402507630a3005893807c064829335c80e935b893462bd8c09b6ba80d6f1134ac9894700072cb64e804164cd51841eb3f8490689ce4302c84e8000000b9499e1198c640026f358324001de2aada4910f714400152b5a2ec071a901717249ca09a2738851641da764039aaa274ec495559040523f8da88d1f2ddc71aee6f4000680aa09acb13280067068400000000a345394d210abc223ab37e848a52384e60082a99f26c9b9cb84b742d88e1b2b35e0ddc08354c00c8180161daea15082d46a7e94d03427a6a525ae85fc000002ea000000000060247d890b3a4d228c3f800246d7c531f1646e2c000003740a00025e03a9e88cb954229b1a603614266c33b98000a3c970ba5fa751793914e00013c9e31a4db84b1d21ea17056910332e992e8e6160228be2983aae1d9c80040a400ba8b523e014001e03e87c91634226ec78001900003f4002334b600004a4e378b1d8909061ce8d14bb308c145241a42bc3d13ba7b274dc14f8996e4179650ac4d07f52e3ad708875d02ce2a2b004e0257544ed70944168a312a158418e503badd4ea2f4fd8fa770b6c00000000000d705f0860015a8e90c88b53e0002f2a089419c74ee01352e7206088000b641e000608216b0180438005060016200000000129800090d9cb69875ac4f1789662dc699b99633a2294003b460e7ddda8002a80017b0003fc1882eb6600025597af0000e0c8f351528ae52c87013cb086324a69c1b08b9f52c47bc55a716f89d0f30f60f0b18620e040c514c93640ea9900621949e5cce281f28eda89493f0fcaa9cda2f2fc000379c81480011811d4140000038e000a6dcc9e9000e40e0b002d671c49ac9558250792403665ec6290a0ac0112c0dd0005751c97f67c5bcf9a4c07e33cff8002d400486800000b3156800000b940000000099c8c0890003bcc00000008940006d1d637c0027e47c0000033b2be2b95801b000501a09b93aec514bb0d22473ce604c696dfc002433049f4812914da000002900067589a80059ea8
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1818068088010e09601048800c00000000091c81e50a9800000010c004100623a1d4310f6254401a0d8550c43d89510062361d4310d6294001a0d8550c4358a5000607a1d4310f6544001a0d4360843d951000607617739cf644400188f7360a73d911000607617749d3634400188f7460a74d8d1000623a1d4310f6244001a0d8550c43d89100060761d4310d6504001a0d43608435941000607615731cd640400188d73608735901000607615741d1630400188d746087458c100062361d4310d6204001a0d8550c4358810
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x1
  | 6 => 0x4b
  | 7 => 0x4c
  | 8 => 0x4d
  | 9 => 0x4e
  | 10 => 0x138b
  | 11 => 0x94b
  | 12 => 0x94c
  | 13 => 0x94d
  | 14 => 0x94e
  | 15 => 0x124b
  | 16 => 0x124c
  | 17 => 0x124d
  | 18 => 0x124e
  | 19 => 0x138c
  | 20 => 0x138d
  | 21 => 0x138e
  | 22 => 0xa4b
  | 23 => 0xa4c
  | 24 => 0xa4d
  | 25 => 0x134b
  | 26 => 0x134c
  | 27 => 0x134d
  | 28 => 0xbcb
  | 29 => 0xbcc
  | 30 => 0xbcd
  | 31 => 0x14cb
  | 32 => 0x14cc
  | 33 => 0x14cd
  | 34 => 0x95393
  | 35 => 0x94053
  | 36 => 0x94054
  | 37 => 0x94055
  | 38 => 0x138954
  | 39 => 0x138955
  | 40 => 0x138953
  | 41 => 0x1409
  | 42 => 0x1449
  | 43 => 0x1489
  | 44 => 0x2c9
  | 45 => 0x14c9
  | 46 => 0x125393
  | 47 => 0xbca53
  | 48 => 0xa4bd4
  | 49 => 0xa4bd5
  | 50 => 0x1354d3
  | 51 => 0x14d354
  | 52 => 0x14d355
  | 53 => 0x98e
  | 54 => 0x14cbd3
  | 55 => 0xbd4d3
  | 56 => 0x14cbd4
  | 57 => 0x14cbd5
  | 58 => 0x140e
  | 59 => 0x4953
  | 60 => 0x4954
  | 61 => 0x4955
  | 62 => 0x20e
  | 63 => 0x209
  | 64 => 0x95453
  | 65 => 0x95493
  | 66 => 0x95494
  | 67 => 0x95455
  | 68 => 0x2cb
  | 69 => 0x198b
  | 70 => 0x98956
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 800
  | 6 => 1315
  | 5 => 953
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
  | 7 => packedAt gbK7 (32526+((h/266+packedAt gbK7 (29600+(h % 266)*11) 11) % 1278)*11) 11
  | 6 => packedAt gbK6 (67938+((h/438+packedAt gbK6 (63120+(h % 438)*11) 11) % 1909)*12) 12
  | 5 => packedAt gbK5 (59714+((h/317+packedAt gbK5 (56227+(h % 317)*11) 11) % 1144)*11) 11
  | 4 => packedAt gbK4 (1436+((h/6+packedAt gbK4 (1400+(h % 6)*6) 6) % 34)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x83fe07f83fc1ffff83ffff00fd51a33e89f3f3
  | 1 => 0xfc1ff83fc1fe0e03fc1c07fffeae5cc7764c9f
  | 2 => 0xffe3ffc001fff003ffe007ff033060f9878f1c
  | 3 => 0x3fffffe000003fffff80003c07f01f80fe0
  | 4 => 0x3fffffffffffc0000000003ff8001fff000
  | 5 => 0xfffc0000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8024004002401288802511024800811a009131
  | 1 => 0x40828184082041104082254b0060c44324486
  | 2 => 0xeb4355c21175a02aeb4054aa0b3060a9858b18
  | 3 => 0x21039eaeb41080437392e00c13c07601d80ec0
  | 4 => 0x4203e73739b9c9702100803023fb0001ef6000
  | 5 => 0x7391040420210180420300c0c3fdfbf6000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeeeee8eeeaeac8eeeeeee8eeeaeac8eeeeeee8eeeaeac8eeeeeee8eeeaeac8eeeeeee8eeeaeac8eeeeeee8eeeaeac8eeeeeee8eeeaeac8eeeeeee8eeeaeac8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36805
namespace PEqualNP.Outside.L_meta_36805
open PEqualNP.Outside.L_meta_36805.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 3 := bs0_3_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 6 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 56 := (concat bs2_3_0 bs2_3_32)
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
theorem bs2_4_128 : Interval s2Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_160 : Interval s2Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_224 : Interval s2Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_256 : Interval s2Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_320 : Interval s2Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_352 : Interval s2Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_416 : Interval s2Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_448 : Interval s2Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_512 : Interval s2Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_544 : Interval s2Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_576 : Interval s2Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_608 : Interval s2Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_640 : Interval s2Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_672 : Interval s2Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_704 : Interval s2Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_736 : Interval s2Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_768 : Interval s2Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 781 := (concat (concat (concat (concat bs2_4_0 (concat bs2_4_32 bs2_4_64)) (concat bs2_4_96 (concat bs2_4_128 bs2_4_160))) (concat (concat bs2_4_192 (concat bs2_4_224 bs2_4_256)) (concat bs2_4_288 (concat bs2_4_320 bs2_4_352)))) (concat (concat (concat bs2_4_384 (concat bs2_4_416 bs2_4_448)) (concat bs2_4_480 (concat bs2_4_512 bs2_4_544))) (concat (concat bs2_4_576 (concat bs2_4_608 bs2_4_640)) (concat (concat bs2_4_672 bs2_4_704) (concat bs2_4_736 bs2_4_768)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_64 : Interval s2Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_128 : Interval s2Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_160 : Interval s2Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_224 : Interval s2Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_256 : Interval s2Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_320 : Interval s2Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_352 : Interval s2Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_416 : Interval s2Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_448 : Interval s2Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_512 : Interval s2Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_544 : Interval s2Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_608 : Interval s2Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_640 : Interval s2Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_672 : Interval s2Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_704 : Interval s2Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_736 : Interval s2Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_768 : Interval s2Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_800 : Interval s2Atlas 5 800 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 801 := (concat (concat (concat (concat bs2_5_0 (concat bs2_5_32 bs2_5_64)) (concat bs2_5_96 (concat bs2_5_128 bs2_5_160))) (concat (concat bs2_5_192 (concat bs2_5_224 bs2_5_256)) (concat (concat bs2_5_288 bs2_5_320) (concat bs2_5_352 bs2_5_384)))) (concat (concat (concat bs2_5_416 (concat bs2_5_448 bs2_5_480)) (concat bs2_5_512 (concat bs2_5_544 bs2_5_576))) (concat (concat bs2_5_608 (concat bs2_5_640 bs2_5_672)) (concat (concat bs2_5_704 bs2_5_736) (concat bs2_5_768 bs2_5_800)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 44 := (concat bs2_6_0 bs2_6_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
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
theorem bs4_4_512 : Interval s4Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 539 := (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96)) (concat (concat bs4_4_128 bs4_4_160) (concat bs4_4_192 bs4_4_224))) (concat (concat (concat bs4_4_256 bs4_4_288) (concat bs4_4_320 bs4_4_352)) (concat (concat bs4_4_384 bs4_4_416) (concat bs4_4_448 (concat bs4_4_480 bs4_4_512)))))
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
theorem bs4_5_640 : Interval s4Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 664 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 bs4_5_192) (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)))) (concat (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 (concat bs4_5_416 bs4_5_448))) (concat (concat bs4_5_480 (concat bs4_5_512 bs4_5_544)) (concat bs4_5_576 (concat bs4_5_608 bs4_5_640)))))
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
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
  · exact alls4_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 8 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 92 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 44 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
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
theorem bgb_5_928 : Interval gbAtlas 5 928 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 953 := (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672))) (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800)) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928)))))
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
theorem bgb_6_1312 : Interval gbAtlas 6 1312 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1315 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat bgb_6_576 (concat bgb_6_608 bgb_6_640))))) (concat (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800))) (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)))) (concat (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312))))))
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
theorem allgb_7 : Interval gbAtlas 7 0 800 := (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat bgb_7_288 (concat bgb_7_320 bgb_7_352)))) (concat (concat (concat bgb_7_384 (concat bgb_7_416 bgb_7_448)) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))) (concat (concat bgb_7_576 (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 bgb_7_768)))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 33, 37),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeeeee8eeeaeac8eeeeeee8eeeaeac8eeeeeee8eeeaeac8eeeeeee8eeeaeac8eeeeeee8eeeaeac8eeeeeee8eeeaeac8eeeeeee8eeeaeac8eeeeeee8eeeaeac8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008636136 * 2 ^ 32 + 4008372936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36805.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,2]⟩,⟨.or,[1,3]⟩,⟨.or,[2,3]⟩,⟨.and,[6,7]⟩,⟨.and,[5,8]⟩,⟨.or,[9,10]⟩,⟨.or,[5,8]⟩,⟨.and,[1,12]⟩,⟨.or,[0,13]⟩,⟨.or,[4,11]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008636136 * 2 ^ 32 + 4008372936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008636136 * 2 ^ 32 + 4008372936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36805

open PEqualNP.Outside.L_meta_36805 in
theorem PEqualNP.Outside.L_meta_36805 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008636136 * 2 ^ 32 + 4008372936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008636136 * 2 ^ 32 + 4008372936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
