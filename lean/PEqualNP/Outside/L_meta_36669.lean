import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36669.Model
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


end PEqualNP.Outside.L_meta_36669.Model

namespace PEqualNP.Outside.L_meta_36669
open PEqualNP.Outside.L_meta_36669.Model
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

def SBf (j : Nat) : Nat := [6, 2, 7, 7, 7, 8].getD j 0

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

def mirrorSteps : List Move := [swapRows 67]

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

end PEqualNP.Outside.L_meta_36669

namespace PEqualNP.Outside.L_meta_36669
open PEqualNP.Outside.L_meta_36669.Model
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
end PEqualNP.Outside.L_meta_36669
namespace PEqualNP.Outside.L_meta_36669
open PEqualNP.Outside.L_meta_36669.Model
def s1K1 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 1 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 1 => packedAt s1K1 (i*3) 3
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 1 => packedAt s1K1 (4+((h/1+packedAt s1K1 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffffffffffde73
  | 4 => 0x6f9c
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff8205
  | 3 => 0x2552
  | 4 => 0x1958
  | _ => 0
def s1Atlas : Atlas := ⟨1,rawDecor 25 s1Pos s1Neg, 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36669
namespace PEqualNP.Outside.L_meta_36669
open PEqualNP.Outside.L_meta_36669.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1610da02c000002800d24001d1802600c824420000007001200015a5589831f00a401800bc49114340004e0000e18a01902ab8baa423c01d02b4f000a0408008020000f0a040020024980ff43bf43fe43fd43bd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1c0380000623d800c60000000b8280008c0616008e0861d41850003f30118000d051f46a1b40860964215800100b2b0d8d60020054246a2c800fe70340006e001d954a6790f8009e003b8007800000988a06160e400751500000002c000a000001b4006124040d86606000a2270491c887642000920027000000000000446e2a15cde3439190223e0b8686205070b4bc33079c4f03a001d0822f0c808422e2e880600000000000000000be52410c8003d000003c4c148000873339e8006512000000000000005a400000000001a4000025134f81300214fc252d82008180004341c040400741c20000010580008200804002400000c10000404140c001400040040281c0014027aa5a1cf947439f286873d5490eeea2a1dd14543cfa9a873f5250f6ea2a1cf14543da28a87345150e78a0a1cf950439ea9e853e51d0a7ca1a14f55242bba8a85745150a7ea6a16bd4942dba8a853c5150b68a2a14d145429e282853e5410a7ca9994f55332bb28e657551cca7ca9194f55232bb28c6575518ca7ca8994f551329f2a0653d540cb9a64194f54e419ea94833e519067ca120cf54c419ea90833e511076ca220cf940419f2a6633d54cc6dca598db54b31da20e633f548c678a918cfd51319e2a2633e540c67aa818ed104319f2a6433d54c86bca790d754f21da20e433f5488678a910cfd51219e2a2433e540867aa810ed10421bb28c8175519027aa7204f54a409f28c81b6519026ca3206d546409f284813d531027aa4204f944409f28081ba501027ca9984f553309faa4613c548c27ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f553209faa4413c548827ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ca9884f55310da20e213e548427aa9084fd51109e2a2215f53442b8a6885bd4910b629221b4414427ea8084f15010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xb0002800e00068091880641408000010003000000832a000c8002200001600000000000048000098ab9c01e0040020000408d18552d0e3661943438d18553d0a3661943428d185544ca3860551328d185540cb2652107318b588548c6356510431a558c410c71653107218758c54886356510421a958841086346154c408d185521023461553308d987548c23461553208d98754883145310510c9148414423661d50108758c540422d6215010
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
  | 3 => packedAt s2K3 (1036+((h/8+packedAt s2K3 (988+(h % 8)*6) 6) % 58)*6) 6
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 1 => 0xe07fffc07e0fc1ff0f83e0fffe1e0781d27ecc
  | 3 => 0xff83ffff800ffffff003ff07ffe007ffe38f0f
  | 4 => 0x3fffffff001fffffc0007fffff801fc0ff0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x21000889100200002284a108802290a404b055
  | 1 => 0x4b199187249492cb05a168d3b214350cd256cc
  | 3 => 0x862aa2120d29315550425a4555404659630b0a
  | 4 => 0x145344244981a5a69968108669996011b80da0
  | 5 => 0x1863873871ce39f8ee739ce071118461ffe000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00eeaaaa88eeaaaa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36669
namespace PEqualNP.Outside.L_meta_36669
open PEqualNP.Outside.L_meta_36669.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x587284029e5228995229cb8100a801f00854091e892004c0002300206a50000000243161b00b40200618d0004ac019085801c1c60e800814401870000433000c2ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xb000ae8872002e468cc282585e1e3c124264020a00004e7856004c9894000c8a38c0360e3ea89e000000009052001880145a28002c0000b676440000100034306a00b2a0a4546c1c8400008e4a7a923a0048a22a707c742496a6ac069ab49cbc085c6816222662ba046e50321a60c4667eb8beaa864020060440f000019c0604292060c8000000b90028d98c36480045048280053e51d0e7aa921e7d4d439e28a873e5410eeea2a15d145429f2a6653d54ccaeca3995d547329f2a0653d540cadca5a0db54b419ea9c833e51906dea4a0db14941af298835d531073ca620cf54c41cea98831d531067ca220ed944419f2a6633d54cc73a8798db94b31b6a96633f548c678a918cfd51319e2a2639d434c6dea498db14931bda826378504c67ca818cf550319f2a6433d54c87688390ebd0e21d6a1c436e518875c8310eb106219faa2433c54487688210ebd0c21d6a18436e51087cca210f9d0421d720843ac41087c88210e910421f318843e531086bca7a05754f40b7290816d521027ca9984f55330cea1c613e540c27aa8186750c30b7290616d520c2eca2185d544309faa2413c54482bea6905714d20bba8a4174514827ca8104f550209f2a4213d54842dca5085b54a10f210c213f5444278a88857d4d10ae29a216f52442d8a4887908410
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xa00000c69802400000078002880058001200002639411c4221880000000800000401011e1c6550d31c650c504c6956310721a358c41886956310421a918543086a66190421a358c41086c56310421e198c41086a56310421e158c41086856310421a919231086a4644c421e150d31086e0604c42199185521031543544308758e54843265408610
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x810004847650d3108740a18c098843415ce5408610
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 5 => packedAt s3K5 (826+((h/15+packedAt s3K5 (736+(h % 15)*6) 6) % 61)*7) 7
  | 4 => packedAt s3K4 (2904+((h/33+packedAt s3K4 (2673+(h % 33)*7) 7) % 119)*8) 8
  | 3 => packedAt s3K3 (840+((h/7+packedAt s3K3 (798+(h % 7)*6) 6) % 42)*6) 6
  | 2 => packedAt s3K2 (150+((h/1+packedAt s3K2 (147+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xc07ffc0fffffff81fffff81ff83ffffcfc71ff
  | 1 => 0xfffffff01fc0fffe0f81ffffffc1e03f27fe67
  | 2 => 0xff81ffffe000fffff001ffe0fffe003fc78f87
  | 4 => 0x1ffffffff03fffffe0000ffffffc3f80ff8
  | 5 => 0xfffe0000000003ffffffffff00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x530444624488208052925909181229a44c30ab
  | 1 => 0x851888a1c911491605a0aa326a41428921d665
  | 2 => 0xa2d514483aa92aab0513548b4b40532c68b86
  | 4 => 0x2c51a20912301b4d29640610c7299603b00d50
  | 5 => 0x3061c38e1c3ce3f1ce79c79c06311823ff6000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeac8c8eaea8080eaeac8c8eaea8080eaeac8c8eaea8080eaeac8c8eaea8080eaeac8c8eaea8080eaeac8c8eaea8080eaeac8c8eaea8080eaeac8c8eaea8080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36669
namespace PEqualNP.Outside.L_meta_36669
open PEqualNP.Outside.L_meta_36669.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x15804a006801030916400cd8a00003001208d23381000e3a0142d321d62128788184e5c8852a05493447c580540078048013040800c43c32800000c0640ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x20aa2c5e12003c7c009864884e0a764c84bc0e689432408e3e720caea836c4acc214789052665a18703a220000b0009a10b2c09eb48200000000928a861c005800004a00a22e560008346c003806b62854a01a5c46168074ba6a6e9c0496be627a6050a40000422430b8004400261e0248a67e008c2a08144042219390000c284162c00202001031e4400200148000230183113e51d0e7aa921e7d4d439e28a873e5410eeea2a15d145429f2a6653d54ccaeca3995d547329f2a0653d540cadca5a0db54b419ea9c833e51906dea4a0db14941af298835d531073ca620cf54c41cea98831d531067ca220ed944419f2a6633d54cc73a8798db94b31b6a96633f548c678a918cfd51319e2a2639d434c6dea498db14931bda826378504c67ca818cf550319f2a6433d54c87688390ebd0e21d6a1c436e518875c8310eb106219faa2433c54487688210ebd0c21d6a18436e51087cca210f9d0421d720843ac41087c88210e910421f318843e531086bca7a05754f40b7290816d521027ca9984f55330cea1c613e540c27aa8186750c30b7290616d520c2eca2185d544309faa2413c54482bea6905714d20bba8a4174514827ca8104f550209f2a4213d54842dca5085b54a10f210c213f5444278a88857d4d10ae29a216f52442d8a4887908410
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x40123875053cd3014000001802ca09300020325100008c054821c6550d31c650c504c6956310721a358c41886956310421a918543086a66190421a358c41086c56310421e198c41086a56310421e158c41086856310421a919231086a4644c421e150d31086e0604c42199185521031543544308758e54843265408610
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x4404847650d3108740a18c098843415ce5408610
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
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
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (826+((h/15+packedAt s4K5 (736+(h % 15)*6) 6) % 61)*7) 7
  | 4 => packedAt s4K4 (2904+((h/33+packedAt s4K4 (2673+(h % 33)*7) 7) % 119)*8) 8
  | 3 => packedAt s4K3 (833+((h/7+packedAt s4K3 (798+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s4K2 (150+((h/1+packedAt s4K2 (147+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc07ffc0fffffff81fffff81ff83ffffcfc71ff
  | 1 => 0xfffffff01fc0fffe0f81ffffffc1e03f27fe67
  | 2 => 0xff81ffffe000fffff001ffe0fffe003fc78f87
  | 3 => 0x1ffffffff03fffffe0000ffffffc3f80ff8
  | 5 => 0xfffe0000000003ffffffffff00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x530444624488208052925909181229a44c30ab
  | 1 => 0x851888a1c911491605a0aa326a41428921d665
  | 2 => 0xa2d514483aa92aab0513548b4b40532c68b86
  | 3 => 0x2c51a20912301b4d29640610c7299603b00d50
  | 5 => 0x3061c38e1c3ce3f1ce79c79c06311823ff6000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeac8eac8ea80ea80eac8eac8ea80ea80eac8eac8ea80ea80eac8eac8ea80ea80eac8eac8ea80ea80eac8eac8ea80ea80eac8eac8ea80ea80eac8eac8ea80ea80, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36669
namespace PEqualNP.Outside.L_meta_36669
open PEqualNP.Outside.L_meta_36669.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x8c89c0a59400029938034503a0149001e1800009420800000014833210f801620815005ce80006c900444cc0f0c386a5000401601020810430c3082ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xe81bd43d02fca5a05f54b40bf28e817d51d03dc43a07b08740beaa4817e53902faa7205f94a40bea94817e51902faa3206f90640de20c81ee21903d843205f94240dfa0481fb40902fea6a05f14d40dfa1a81bd43502fea4a05f14940bfa8a817c51503dc42a07b08540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea98817e52103dca4205b94840bea9081ed52102daa4205f94440fb288817651102faa2207d54440baa8881be411037882207b88440f6108817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc3bc87987750f30bf296617d52cc2fca3985f54730f710e61ec21cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa318778c630ee18c61ee218c3d843185f94230ef98461fb308c2fea8985f95130beaa2617c544c3bc86987750d30bfa92617c524c2fea2985f14530f710a61ec214c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa8861de310c3b862187b88430f6108617e500c3be60187e8c030ee98061f9300c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c83dc85907b50b20f719641ed32c82fca3905f54720f710e41ec21c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620fb28c417651882faa3107d54620baa8c41ee21883d843105f94220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483dc84907b50920f719241ed32482fea2905f14520f710a41ec21483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2107b88420f6108417e50083de40107e88020f690041f920082fea9885f95310beaa6217c54c42fea7885f94f10bea9e217c53c42fea5885f94b10bea96217c52c43ec83887d50710fb18e21f531c43ee43887b88710f610e21f421c43c843885fd5210bf2a4217d54842f8a9085fd4e10bf29c217d53842f8a7085fd4a10bf29421ee52842dca5085f54a10f6a94216d52842f8a5085f54610f710c21ec21842fca1087dc4210fd884217f544437ea8884fd5110bf2a2217d54442f8a8886f151109e2a2217f53443bea68857d4d10bf29a217d53442f8a6887714d10ae29a217f52443dea4885bd4910bf292217d52442f8a4887b14910b629221f641443ea82887d8c510fa98a21f721443dc42887b08510fa10a21e421443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821ee21043d842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xc54ccbbc87997750f32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c657e528cbdc85197b50a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbc86997750d32f721265ed424cbde6499778c932bfa8a65f7514caeea2995f14532fa28a6574514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbbe64197b8c832ee99065ed320cafca2195f54432bf280657d500cafca7a0f794f41af29e837d53d07baa7a0d754f41bf29683ee52d06dca5a0df54b41f6a96836d52d06fca1a0df54341beaa4837e53906faa720efd0e41dea1c837e52906faa520df94641dfa0c83f741906fca120df54241bfa9a837c53506fea4a0fbd4941b7a92837c52507d8a4a0db14941fba0a83be41506fea0a0df14141bf2a0837e53106faa620efd0c41dea18837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc6fca598fb94b31b7296637d52cc7daa598db54b31bf286637d50cc6fea918df95231beaa4637c548c6faa718f790e31eea1c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131bfa9263ef524c6dea498df14931f6292636c524c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618f790c31eea18637e520c6faa418df94431ef98863f6310c7ba6218fd4c431bf280637d500c6fea990df95321beaa6437c54c86fea790df94f21bea9e437c53c87ee8390fd10721fb98e43f431c86fca190df54321bfaa4437e54886faa910df15221bfa9c437e53886faa710df14e21bea9443ef42887dc8510fb50a21f621443ef32887dc6510fb4ca21f6194437e51887de4310fdc8621bf284437d50887dea910fb95221f6aa443ec54887dea710fb94e21f6a9c43ec53887de8710fb90e21f6a1c43ec43886dca310fbd0621f720c43ed41887d88310fbcc621f718c43ed31887d86310fbd4221f728443ed50887d8a110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821f7a1043ee42087da8410fb10821f799043ee32087da6410fb0c821bf28843f741087e88210fdcc421fa18843ef21087ec4210fb48421fa908437e50086faa010fbd5021f72a043ed54087d8a810fbd4c21f729843ed53087d8a610fbd0c21f721843ed43087d88610fb94421b728843e651087de8210f9d0421f720843ed41087d88210f910421f798843e731087dc6210fb4c421f618843e431087dea010fb94021f6a8043ec50086fca7a05f54f40dfa1
  | 2 => 0xa44c28b00094cda80000024c9f9b0536000299140005fc5080054c57c0000010e0010980000079d4509619e00053800346244002ac08c0f51d0e100015c6e8000fe364a50ad1901380001229080ca216039a240281412a878c0007847c564502b3206605289ea000ae4d20730306f93b00006a07430a640920001f9f80009b40025a000448850000000012411f32e028fc9cb0008bc002383cc53c0026e4ae4e477a6c472a44572b84a04cd1d94e1da0c4468f5340000a800036813c5f1664ac7e9510241caa34c119f3fe1b8ad80050c2945aa041c84f42a02f000a10e808f0002e4552464560f11420a08aa9cbd26138c764fa1fb2f00080fa1123288943a7f0000010f16b00008cb695c000000b70a62f20b0e99bc000a3c002210000008326900037000000000324a89e104e5d8b62b500090c0000020e9ec000003da001090000b8000f88101d06584a0095740013a8071e05a8619362646a83e88c36252c670743768c8002963d68409f000000710000000001e5168002522b0000000009e800000106305518004a490926000372000198e31622d0c60000caa0c000001d86448605b00802000000000380a0000c0a81404804010060600205000038040480601004000200101c0000e000000100001800038060280200008020220a0140580602802000000080c010000000203000000000700c008480380e01840000000180a020060000000814000060300c00056000020100c0900c010040000a0180a00000018020c00404000050040100a0080000000040000100c00804010060180000802050020001000800038040001200000000000080e0000a00000048060180a010000102000000020020100a02002048000381601810000040001204800030100000a0100400004030000781c0080a0000600000048000180a0000003002018000002800800040040c806010000000400814000000000c0880e0000002004010000000e0003d7e52d0efaa5a1df94743bea8e877e50d0efaa1a1df55243bf29c87bf4390fbe8721df94a43bea94877e5190efaa321df94243bea8487df4350f7c86a1dfd4943be292877f5150ef8a2a1dfd4143be282877e5410efca621efd0c43ef21887bd4310fba8621e750c43bf29087ee5210edca421df54843f6a90876d5210efca221df54443bf280877d5010efca7a15f54f42dfa1e85bd43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a17dd4542bba8a857c5150be8a2a15d14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657
  | 3 => 0xd9d6236000001020002d8002700001f83e0003e4359400950bc0004f800000498000fe01e788f2800000021501c0028000000992449bc6016732485c909585286d8c020f4283f400000510000710c54d00000019d1d610d2c80000096c450005607bc5e92843e000000f80a45f80000b160000408f3000001578250000000012e088960000000001d40002e0000f925a791240c0002970001c53f0a80560e0068290760dc0019c4be39c00109000001330000008dc310d310418000000000080001e90004ec0000005a00096000000000bd8003944c4829880002241410d556834b128c3649246f9cf40e278000001986894914938e3dc4e13834e2bc55a36000000c780009800000000000934002b6000461540000008fc000841f8000fe14d0006410b0000000e8f01f74685f122a1a38a398b0aa54e6000b28000000c83180012e0015b9c10009f0889bf23c000a0000478508d688e4d4650b81471a21ec332022e899400026238360241dd2e43800b10e0348193a00000028c002a952a44c0000040a2ec000000009e000000000000000002d20014f80053200000000512010eb82117e6a00008b01c8a542a5e3be0004d9ba460000000004ba17c6b800094354ea98749c4f0061930847206a0ee5421a026910166474000de000654590000a2000f421840089c0009d202000ab9162fa000c59ac530001588002ee6bd059c9332694000c60000009280029800156800254000ed0000000000000055c00148000000001220000f4164001a6000268000001880009680039c2f0b99e400077054a4a28c4bcf81f50000010d80024e88c7b0001a031d061430ce900000013dc3480000014400085800000558000003faa6887a60256000001370006788d000000000000002d00000029d2bc000ef000000000000fa4820000000000000000047000000e10000000000000000000035800000a70920364b80010722c208000088000001bc002b403c01801840174590cc1bd000000381b7000000440003fc000c28340000005c1c349e401551d22c66a4c68853b0a39198cb0ee36cd0813000989170fb268160840f20009502d2a435c9547a04b3989f49aa813a898d33a190e47b0150002e2000368004d68d4c31234620013ba0926076c000a41d40000018e5268055908000060c2aa08000000f995d00000000000000015410003ec190cd00010c308348002740010a98a44a174001ab03848036175438001392711f2744000000ec3680000008291d12155194001150562b4624a99842de66d0e800000000350b7000334002264406cca90171fe064111b802a0000000022e8f4000000005140011553c0001c8001e23
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x310c2d9600c4309bd96210c26d6588430cb952210c32d5488430d9946210c36551884309bd94210c26d6508430cb950210c32d5408430d9944210c3655108430f10c4210c31d54cc03097d95300c31d544c0309ed95300c25e63153209758c54c823e6414f208f59053c82e46150b20b918532c836651087209d987548827561d52209798c548825d63152209d984548827561152209d987538827561d4e208f990538823d6414e209d98453882756114e20d9d8a51883665188620d9544218836651c822097d8d544825c63551209dd85544827461551209798c544825d63151208fd91534823c6454d209dd8553482746154d208f990534823d6414d209b195424832c5450920b9185424826c654c920d314d32482e4614c920d914621482ea6088520b9986204825e63150209758c540826e62150209d984540827561150208f990530823d6414c209b98853082766114c209d58453083665108420d954421082e960084209bd95200827b65480209798e54c425d63953109b98a54c426d62953108f99253c423d6494f109b98a53c426d6294f10b918941c42e4624c710d999421c43656508710d995021c43645408710d994c21c43645308710f898021c43e160087109b98b548426d62d52109798c548425d63152109b988548426d62152109b98b538426d62d4e108f990538423d6414e109b988538426d6214e10d994b108423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f99454443356115110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10d5584534432f54d4910cb153524434f53d4910d314f524436561d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c53149109b984524426c6114910cd15241442746550510b91894144354538c5109d19531442e4624c5109d997214433454c8510d514f21442f260c85109b996214432f5488510cb152214434f5388510d314e21442e661885109b994214432f5408510cb150214434f5308510d314c21443345408510d514c21443675208510b999421443666508510e9d5021443665408510d915021443a45408510c915021443c75308510d994c21443645308510f114c21443445308510f808710442e662841109798c540425d63150109b988540426d62150109d984540423e6414c108f590530426e6214c109b58853042766114c109d987520423e64148108f590520425e63148109758c520436651084109b98a500426d62940109e596100427765440109ed9510043e22144010
  | 1 => 0x86e7614c8219b59432086ae640c821ab590320874d530c821b598f41086e562d04219d59441086b664cc421b958b3108675650c4219bd9521086776548421b9987540872d5415021b398c54086cd6315021b998454086ea6015021ba58054086e661d4c21ab99053086ad6414c21d354c53086e66114c21ba98053086e96014c21b998743086e561d0c21b998643086e56190c21b9d8543086e46150c219b994430866d6510c21e350c43087666194421b999251086e66394421b9582510866d65d0421b398f41086cd63d0421b9597410876565d0421b998f41087c663d0421b198f41087c563d0421b958341086e661904219bd9541086e76510421b959441086e66410421e999041087a65410421e955041086e66310421e9d0c41087a54310421b9580410866d65cc421ab99331086ad64cc421b9597310876565cc421b999331087a664cc421a999331087a564cc421b919331086e560cc421b9986310866f654c421b9d9431086e5650c421b999031086e4640c421b998c31087c6630c421f194c31087c5530c421f190c31087c5430c421b958031086ae6414021ab59050086ce6314021b358c500876950140219dd8552d02746154b409bd8951d026c625474097d8d519025c63546409bd89519026c6254640d994421903655108640e9104219026e6214d409b588535031c5350d40ae181435026e62d45409b58b51503675108540d9144215034e5394840d354e521026e6194840d394d521034d53548409b18552103565394440d554e51103665294440d954a51103676294440d918a511026f62544409b18951103565354440d554d51103665254440d954951103676254440d9189511031d5390440cd546411031d5310440ae580411026f65884409b596211034e5388440d354e21103665188440d9546211026f65084409b594211034e5308440d354c21103665108440d954421103a44108440c754f401023f6550040c754d401027b65500409b98854cc26d6215330c715143cc2776154b309d18552cc26f62547309b18951cc26e62152309b588548c27661152309d584548c23f64546308f191518c26f62546309b189518c3665108630d9544218c3c431086309bd89544c26c62551309dd85544c27461551309b988544c26d621513097195434c31c5450d30b6181434c26e62d45309b58b514c3675108530d9144214c26e62d50309b58b540c27661d50309d587540c23d65950308f990540c25e63150309b988540c26d62150309d984540c2756115030cb952520c32d54948309b986520c32e5454830cb551520c26c6154830cd952510c3355494430d994a510c3655294430d9d8a510c36462944309bd89510c26c6254430cd951510c3355454430d9949510c3655254430d9d89510c3646254430c7552310c355518c430c755
  | 2 => 0x8070080e0200100800004000000b00c0100c1001c010700202c0600c000040200c0403006010000000100800004010000001006000000340000003018000040100002000010080000000018060000000c050040000008000090140100c010100e9bd8951d0e6c62547439bd895190e6c62546439b98b5150e6d62d45439b9885050e6d62141439d9845050e756114143a75924310e3f6550c4397d954310e9f6550c43c7d954310f8d43948439b9865210f1d43548439dd855210e746154843e350d5210ee46154843cbd0d5210f4e4354843cb50d5210f4d4354843c350d5210f6761548439b1855210f646154843991855210f1d43944439bd895110e6c6254443c750d5010e7661942429d5865090b1c5350d42cdd0c5150b354314542d9d885150b674214542c754f4210b4d53908428fd954210b1d53508429bd954210b4d5350842b91854210a7661d53329d58754ccb1c5450f32b9185428ca7661942329d586508ca7661951329d586544ca7761551329d185544ca7b60551329e181544ca5c6550d32c7151434ca6c6550932e350d424cae46150932d590c514cb554314532d9d88514cb664214532d9508514cb6732145328f596540ca3e64150329798c540ca6e6215032c7553320cb2d548c83297d95320cb1d544c8329bd95320cb2d544c832b9185320cb4e5394b41d354e52d074e5354b41d354d52d07676154b419b98a539066d6294e41c794d439069d63d06419b98a509066d6294241d914b415069d63d04418fd9541106776550441b9189411066e62d53319b58b54cc66e62153319b58854cc72e5494b31cb55252cc72e5454b31cb55152cc7676154b319b98a548c66d6295231c7951438c69d64cc6319b98a508c66d62942319758e544c66e62951319b58a544c66f62551319b189544c67b60551319e181544c76452cc5319b988540c66d62150319e980540c67960150318f992530c63d6494c3197596430c71c5450c31a7593310c65f654c4319dd95310c6e4624c4319798c54c865d63153218f99053c863d6414f21b598f41c86b664cc7219798e548865d63952218f992538863d6494e21cb95142886ce6310a21b358c428874e534ca21ab99032886ad640ca21b9987548872f5495221b398e54886cd6395221b998454886e661d4e21ab99253886ad6494e21d3d4e53886e66114e219b994438866d6510e21e350c43886ce63d0621b358f41886ae64cc621ab593318876b50942219798e544865d63951219b58a544866f62551219dd85544863e6494d218f592534866d6294d219bd8953486776154d219798c540865d63150219e980540867960150218f990530863d6414c219e98053086796014c219b59642086e56190821b9d85420866d6510821cb55042086ce6310821b358c420866d658c821b9586320
  | 3 => 0xc00122000204001ea2c00001c9191fa001258353661751a1d90000011d069166000fca421e6000c400021a000001141a40005880013c000499bf4583d8001eb2e8578531d828217c451321a28f0fba3f0006b42918f312001248c000000016a2940a5e0e416300070c1b80024a0000022843e99cc91ff000384000000005f0000c8248000002701dc0012ca08000000001cb0003102a02307e6a0f182615c000c3a6437a5841500748e4b07e18a000294b3912000000001be09a00076000112070b11053e828c711fb4a8000000850e27d85c8001ca9b0000000002840014e2e63d4002093a0000538b7472000e0800182360001c50009ac000000000001e0001100000697b00084c000240000009fa571483a8000000000c8000600008380000027083c298703d848c001e524c65522950000000000004381dc000002e2001241420005a0e72501be3d00000000025c6317d3c03700024e0ca010f22460004205d256018850001793cc000000000004a42d8e325a0f85c1580000e0070ff026000958004709a45906b0001d80016d02c54ceb8112fc36c0f8001301f00c8004d06d0379b716a024f916f0001703f11a0b221c0000031c02000241000048e20731d0594e022115e1b8551b1260364b49e14c06e0002551e0334a00002383e89707400085c0000000000000000000000de00022667c1796c0fe5190a80000094cf814810c0004ea31000008001ba0003c5069ac40e6acfd1bb3164d8f6a01486328ea0780560000026f000808c205646c818ef2110003a51b8e72aa0e83607946413cc694444a6949a95a1e40801423e1c8001059f10000003419e206254ce0ef0005900004b2f43791e80002060c000b434c000000bb000000a6000000000bb227000000a49100000000000017c0006a22d00035c002660c4000288000020012f0833a2528d50001ac000ad95111c5640d25b3dc80000000000000000004800c12515249a9b4000004b06d4240000000010e8573920008000049e000eb000000428000002040cc510c900068c001430008ec461ef4601e88b1fd02a3dc661c70d488c1e8ce11e100820001968cc00263278890bb9d33226840000522e000000000e48491a8500004dd1302703c05cfc00000047d2fa52432788000e0000000000583f8060a589c0949688f11518e9c50616e000000a78002ae1b4000002ac0040000000008050080100400008000000300c000000106c12010130001800803014050240000c0000c02008050040100406038000000002c1d0140000c08004040000105405000020000603c00004030100400005020030580401400000010040200403004010500802c04008000200201408008030000301010004040600100c000000700c0002000004040040700005000000000d02802000010380700000004
  | 4 => 0x3603984d8c50844cc001800005ac000000004382200000019c839ae0000000025d00064ced800328000000000000005480019e24000145186200c088d4400004890c4dc66c5e1723ea0d84d15c236534540003300004226a27c258cc8f925e688cd000272680218ac1607302d1013ce22c61000268104c815f1561849e800000000c6000128118ef9663480943d8004068408e8d34c2460b809f45641800120042000000ad43000000000000910ed03b16c614f49fe32c000f413b0001d5050001d649cd90000005d4239af254444018d52fe574ee21b38c340260990623f8ee800372734e798200c0000000017a97000000058114002620002490205e32e0006d0000360000022e0000b8001210c803cea8142620d0aa19d1da0000000000072800216092000e916a2746d87d80021e2fc0022a00069c00000000001288000001f41100000000031800000000410000004a0000000004250f00a0000a5261c2000374001470001387c10b000000000004449940021a3527ccc300b0cc1540e8a00008b
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x131b8d8c00110b800f001207828f8004000d1e038688001b0023800000181506000300001f80251f0e0022a315a00b249c9c19801785a4219a01900e89848a8717168a1e800c889d001498a100139a9916109d851420928901021180800000220000188d041019004004800a04083162c1801624a8028043e15431855210f42a18c2a9087c150f6154843c1a8630aa421f05431855210f13a18c2a90879190c6154843c4a8630aa421e45431855210f02a18c2a90879154c6150842c18caa1a849968543185424cb82a1a8428a6589550614c832a1ae529a8720d0d72951438c686b90a8a1863465c05450c31a1ae72a28510d0d7494d328869338ea92a44383d516395221c1ac9a9ca710d4671d4e538870732a8621c43835516310821c1ac8a986410e0d5458c5408714aa2c02a043835915314c21c92a6b00a610e0d6550c430866339cc928843299d26394421b0ae73208210c65751903108670b80c818843299d2630c421b0ae93186210cc57690c310874232286188438a5915014021c92c6a80a010d4473544219023238ac429a81435c85350d40c32a6b008220625651042110382a988210881685c041084408c8e2b10a99850d7215143cc2923a2a210c61191c56215130a1ae42a2869861954580310c322b286210861c15503108430b82e0188421850d7315142483122a0c2a1241435d0534c920c88a630a64905467395021c42933a4a610e21491c96115110a88e4b08a6885267495021442a339ca810a21c11535308510a4ce929842885467394c2144383aa0a610a21c11505308510
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xa410465840748000015800006004c3a0681d516395221c05649c75394e21a0585191430c421a8180191430c421904815c85350d40c21655c04108440d01535c04108440904815c85450f30904815c85450d30c41655c03108430d01545c03108430a05831506150920a058414c614c920
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
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (756+((h/14+packedAt s5K6 (672+(h % 14)*6) 6) % 56)*7) 7
  | 5 => packedAt s5K5 (21203+((h/233+packedAt s5K5 (18873+(h % 233)*10) 10) % 1014)*11) 11
  | 4 => packedAt s5K4 (25868+((h/208+packedAt s5K4 (23788+(h % 208)*10) 10) % 909)*11) 11
  | 3 => packedAt s5K3 (3850+((h/25+packedAt s5K3 (3675+(h % 25)*7) 7) % 100)*8) 8
  | 2 => packedAt s5K2 (800+((h/4+packedAt s5K2 (780+(h % 4)*5) 5) % 20)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x81fffff03fffff03fc3fe1ffff87fffa23f1ff
  | 1 => 0xfe07e1ffc0fc3ffc3fc3fe1c0ff8703ddcce67
  | 2 => 0xfff801ffff003fffc003ffe00fff803e1f0f87
  | 3 => 0x1ffffffc1fffffc00000fffffc7e00ff8
  | 4 => 0xfffffe00000001fffffffffff0000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8c1040118208000044046024618091880150ab
  | 1 => 0x14b182228e50542c1c41a208a6882290ccc665
  | 2 => 0x2862d545143aa955c222d5414b550526170b86
  | 3 => 0x7145198828a20d9aaaa811020c664e07600d50
  | 4 => 0x4186110e30c331e33333199380440807baa000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80eeeaea80, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36669
namespace PEqualNP.Outside.L_meta_36669
open PEqualNP.Outside.L_meta_36669.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12106d5df000000050700000c2c5cd3c016e1dc017413365005000002f08012a14e26023065cb582f2969412a800e00089a215bf80f5598d08acb185d4131147229166947aca90311a1808418008001a0c183121400c0e14029020007ff5301dfd4c05fe5301ff54c017d53017f14c05fe43007f50c05fc4301ffd4803fe5201ff54803fc52017fcc803fe32007f4c803fc3201ffd4407fe51005f94407fd5101ff144077c51017fcc401fe31007f4c405fc3100ffc8401fe21007b88401fd2100ff08401ec2101ffd4007fe5001ff54007fc50017fcc001fe30007f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x9c200dff90e10007fa8708037fc4384009ffb142004bfd8a10027fcc508006fe6284009f73142001bb98a10027fac508002fd6284009f6b142000bb58a10027f8c508012fc628401dffa94200cff94a10077faa508033fc528401bff994200cff8ca10007fa6508033fc32840177eb0c200effd4610077fca3080037e518401dfea8c200eff14610076f8a308037ff3184001ff18c2000ff4c61006ff86308033ff2184001ff10c2000fb88610007fa4308033fc2184001f610c2004bf98210027fea108013fe5084009fea842004ff14210027fe6108013fe3084009fe9842004ff0c210027fe4108013fe2084009fe9042004ff08210027fe2108013f71084001fd884200bffd951005dfeca880037f65440013fb2a200bff9951001dfcca8802ffd65440177eb2a200bff1951001df8ca8802f7c65440073e32a2000ffd8d10005fec688003df63440016fb1a200aff98d10015fcc688003fd63440017eb1a200aff18d10015f8c688003dc63440056e31a200bffd4d1005efea68802bfe5344017fea9a2000df54d10057f8a68802bfe4344001fea1a200aff10d10007fec488002ff6244001f7b122000bbd891004ffcc488006fe6244001feb122000bf5891004ff8c488006fc6244001f63122001bb1891005ffea488027fe5244017fea922009ff14910057fe6488027fe3244001fe9922009ff0c91005ffea28802ffe5144001bf28a200bff5451005ff8a28802f7c5144015ff98a2000ff8c510007ec6288003fd3144001fa98a200aff0c51004ffe4288003fe2144001f710a2000ff4851004ff84288003ec2144017ffa822004ff9411005ffaa088013fc5044015ff9822004ff8c110007fa6088013fc3044013ff9022004ff88110007fa4088013fc2044001ff8822000fec4110027fc2088013f61044009ffb282004bfd9410027fcca0800efe6504009feb282007bf59410027f8ca08012fc6504009ffb182004bfd8c10027fcc60800afe6304009feb182000bf58c10027f8c608012fc630400fffa982007dfd4c10037fca60801ffd5304001bea982006ff14c10037fc8608003fd430400dfe2182004ffd8810025fec408013fe62040037f3102004ff58810005fac408013fc62040097e3102007ffd481002ffca40801ffd520400bfe2902006ffcc81002ffc6408003fd320400bfe1902008bf9841003ffea20801ffe5104001bf2882007ff5441003ff8a20801f7c510400dff9882000ff8c410007fa620801bfc310400bff9082000ff88410007dc4208003fd210400bfe1082000fb08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802000fe44010
  | 1 => 0x6fd6288003ffa944001ff94a2000ffaa510007fc5288003ff9944001ff8ca2000ffa6510007fc3288009ffb0c4004ff98620005fcc310013fd61880017eb0c4004ff186200a7fea310053fe5188001bf28c4014ff546200a7f8a3100537c5188027ff98c4000ff8c620007fa631004ffc3188003ff90c4001ff88620007dc4310007fd2188003fe10c4001fb08620025fcc110013ff5088009ff2844004ff54220027f8a110013ff3088009ff1844004ff4c220027f86110013ff2088009f79044001fec8220027f84110013f82088025ffb2a4012bfd9520006feca900027f6548025ff32a4003bf99520097faca9004afd6548025fe32a4003bf19520096f8ca9000e7c6548001ffb1a4000bfd8d2008ffcc69000afe6348001feb1a4000bf58d2008ff8c69000afc6348025ffa9a4012dfd4d2008ffca69004bfd5348001bea9a4011ff14d2008ffc8690003fd4348023fe21a4004bfd892000ffea490007fe5248003f72924001ff54920097daa490007fc5248003ff9924001ff8c92000fdc6490007fd3248001f69924001ff0c920007fec290002ff6148001ff30a4000ff58520007f8c290002fc6148025ffa8a4012ff94520006fca29004bfd5148025fe28a4012df1452008ffe6290003fe3148001fe98a4011ff0c52000ffe4290007fe2148001f710a4001ff4852000ff84290007ec21480037fb024012ffd4120027fca09004bfd5048009fe2824011ffcc120027fc6090003fd3048009fe1824001ffc812000ff64090013fe2048009f71024004ff08120027d84090007f82048011ffb2e2008bfd9710047fccb8800efe65c4011feb2e2008bf59710047f8cb8800efc65c4001ffb1e2000bfd8f10087fcc78800afe63c4001feb1e2000bf58f10087f8c78800afc63c4011ffa9e2008dfd4f10087fca788023fd53c4001bea9e2010ff14f10087fc8788003fd43c4021fe21e2000ffd8b10005fec58803ffe62c40037f3162000ff58b10005fac58803ffc62c40037e3162008ffd4b1007ffca588023fd52c401ffe2962010ffccb1007ffc6588003fd32c401ffe1962008ffd4710047fca3880037e51c4011fea8e2008ff14710046f8a388043ff31c4001ff18e2000fd8c710007fa6388003f531c4021fe18e200fffc8710007fc4388003ee21c4001fe90e200fff08710007d84388023ff50c4009ff2862008ff54310027f8a188043ff30c4009ff1862000ff4c310027f8618803fff20c4009ff1062000ff48310027f84188013ff65840097fb2c2004ff9961001dfccb080137e65840073f32c2004ff59610075facb080137d65840013eb2c2004ff19610025f8cb08013ff63840097fb1c2004ff98e10015fcc708013fd63840017eb1c2004ff18e10025f8c70803bff538401dbfa9c200dff94e10077faa7080037d538401bfe2
  | 2 => 0x210efd8a010873ef3008439f61804204ffd9630025fecb18013fe658c0077f32c6004ff596300ddfacb18013fc658c0097e32c6004ffd9230025fec918013fe648c0317f3246004ff59230005fac918013fc648c0097e324601bffd52300defea91806bfe548c037feaa46000df552300d7f8a91800afd638c005ffa9c6002dfd4e30017fca71800bfd538c005bea9c6002ff14e30017fe871800bfe438c005fea1c6002ff10e30027fec518013fe628c0037f3146004ff58a30005fac518013fc628c0097e314601bffd4a300cffca51806ffd528c033fe294601affd0a300cffc8518003fd428c033fe2146002ffcca30017fc651800bfd328c005fe1946004ffd8630027fcc318002fe618c009feb0c6000bf58630027f8c31806fff518c037ff28c6000df946300dffaa31806ffc518c037be28c601affd0630007fc8318003fd418c035fe20c6002ffcc630017fc6318003de318c005fe98c6002ff0c630017b86318067ff218c001ff10c6000fb88630007fa4318067fc218c001f610c6004bf98230027fea118013fe508c009fea846004ff14230027fe8118013fe408c009fe2046004ffcc230027be611800bfb308c009fe1846004fe0c230027fe4118013fc208c02fffb2a6017bfd95300bffcca9800efe654c02ffeb2a6017bf595300bff8ca9800efc654c001ffb226000bfd91300b7fcc898062fe644c001feb226000bf591300b7f8c898062fc644c02fffaa26017dfd51300b7fca89805ffd544c001beaa26016ff15130025fec69800bff534c005bfa9a6002ff94d30017faa69800b7d534c005fe29a6002ffd0d30017fc869800bde434c005fea1a6000f750d30017f88698003ff624c0017fb126015ff9893000dfcc498003fd624c02bfe3126001bf189300bffea498057fe524c02ffea926015ff149300b7fe8498057fe424c001fea126015ff10930017fe649800bfe324c005fe9926002ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298002fc614c02fffa8a6017ff94530006fca29805ffd514c02ffe28a6017df145300b7fe8298003fe414c001fea0a6016ff10530017fe629800bfe314c005fe98a6002ff0c5300affe4298003fe214c001f710a6000ff485300aff84298003ec214c0057fb026017ffd4130027fca09805ffd504c009fe2826016ffd0130027fc8098003fd404c009fe2026002ffcc130017f66098013fe304c009ef1826004ff0c130027b8609800bf8304c02bff9026004ff08130027fecb10012ff6588009ff32c4003bf99620027facb10052fd6588009fe32c4004bf19620027fec710012ff6388009ff31c4002bf98e20027fac710002fd6388009fe31c4004bf18e200a7fea7100537f5388027ff29c4014ff54e20006faa71004ffc5388027ff21c4000ff50e2009ff8871000
  | 3 => 0xe1826222ffc8131117f8409887bff658843d7fb2c421eff9962101dfccb1087bfd658843d7eb2c421eff1962101df8cb10803ff63884017fb1c4221ff98e21015fcc710803fd63884017eb1c4221ff18e21015f8c71087bff538843dbfa9c4221ff94e210f7faa7108037d5388443fe29c4221ff90e21007fa8710887fc43884037eb144201ffd4a210f7dea510807fe5288403f72944201ff54a210f7daa510807fc5288403f62944201ffcca2110fde6510807fe3288403f71944201ff4ca21007da6510807fc3288403f61944201bf986210f7fea31087bfe5188401bf28c421eff546210f7f8a31087b7c5188443ff98c4200ff8c621007fa6310887fc3188403ff90c4201fbc862100fee4310807fc2188403fa10c4200ffd8221007fcc110812fe6088401feb044200bf58221007f8c11087bff508843dff284421eff542210f7f8a110887ff3088443fe1844201ffc822100fde4110807fc2088403f6104421efbd96210f7dccb1087bed658843df632c4200fbd8e2110fdcc710803ed6388443f631c421efbd4e210f6dea710887ee538843df6a9c4200db54e2110fd8a710887ee4388401f6a1c4221fb10e2100ddcc31087bef518843df728c4200db946210f7daa31087bec518843db628c4221fbcc621007dc6310803ed3188443f618c4200fbd8221007dcc110803ed6088401f6304421efbd42210f7dca11087bed508843df62844221fbcc22110fd86110883ff65484417fb2a4200dfd9521004feca90883fe65484077f32a4220ff59521105faca90883fc65484077e32a4220df1952101cf8ca90803ff63484017fb1a421fff98d21015fcc690803fd63484017eb1a421fff18d21015f8c690883ff5348441bfa9a421fff94d21107faa6908037d534843ffe29a421fff90d21007fa869087ffc43484037fb124201ffd492100ffca490807fd5248403fe2924201ffcc92100ffc6490807fd3248403fe1924201bfd8521107fea290883fe5148401bf28a4220ff54521107f8a2908837c514843fff98a4200ff8c521007fa629087ffc3148403ff90a4201fdc852100ffc4290803ee2148403fe10a4201fb0852100fe84290803ff60484017fb024200ff98121007fac090803fc60484097e3024220ffd4121107fca090883fd5048441fe282421fffcc1210fff86090807ff2048403fe1024201fbd942100fdcca10807ed6508403f63284201fbd8c2100fdcc610807ed6308403f6318421dfbd4c210eedea610873ee530843bf6a984200db54c210e7d8a610873ee4308401f6a18421cfb10c2100fdcc21087aee6108403f3308421dfbd44210efdca2108036e510843bf6a88421dfb144210eed8a210873ef3108401f71884200fb4c4210e7d86210807ef6008403f73004201fb5802100fd8c010877ef500843bf7280421dfb540
  | 4 => 0xbff304c805fe1826401ffc813200fde4099007fc204c801bfb1ca229df98e51006fac7288027d6394453be31ca229df90e51006fa87288a77c4394401bfb14a228df98a51006fac5288a37c6294453bf994a228df8ca51006fa65288a37c3294407bf30ca2039f9865101eecc3288a77f3194453be18ca228dfc8651146f843288037f6094401bf304a200df58251006f8c1288a77f3094453be184a228dfc8251146f8412889fff658c44f7fb2c6200dfd9631004fecb1889ffe658c4077f32c6227ff5963113dfacb1889ffc658c4077e32c6227df1963101cf8cb18803ff648c4017fb246226ff992310c5fcc918803fd648c4017eb246226ff192310c5f8c91889fff548c44fbfaa46226ff9523113ffaa9188037d548c44dfe2a46202bf58e31017fea71880b7f538c405ff29c6202ff54e31016faa71880bfc538c405ffa1c6202ff90e31017bc871880bfd438c401eea1c6202ff10e31007fec518897fe628c4037f3146200ff58a31005fac518897fc628c4037e3146227ffd4a3112ffca51889ffd528c44bfe2946226ffd0a3112ffc8518803fd428c44bfe2146202ffcca31017fc651880bfd328c405fe1946202bf9863113ffea31889ffe518c401bf28c6227ff5463113ff8a31889f7c518c44dffa0c6200ff90631137f8831880bff318c405ef98c6202fdcc631017f8631880bf4318c44bff90c6225ff08631007fec118803fe608c4097f3046200ff58231005fac118803fc608c44fffa846227ff9423113ffaa11889ffc508c44dffa046226ff10231017fe611880bfc308c405ee1846225ffc823112ff84118893ff654c4497fb2a6200dfd9531004feca98893fe654c4077f32a6224ff59531125faca98893fc654c4077e32a6224df1953101cf8ca98803ff644c4017fb226223ff991310c5fcc898803fd644c4017eb226223ff191310c5f8c898893ff544c449bfaa26223ff95131127faa8988037d544c447fe2a26202bfd8d31017fea69880b7f534c405ff29a6202ff54d31016faa69880bfc534c405ffa1a6202ff90d31017fa869880bfc434c401ffb126200bfd8931007dec498802ef624c445ff3126201bf98931007fac49888bfc624c4037e3126200fb1893100dd8c498893ff524c445ff2926224ff54931117f8a49888fff424c445ff2126200ff50931117f8849880bff324c405ff1926202ff4c931017f8649880aff614c449ffa8a6224ff94531006fca298893fd514c449fe28a6224df1453111ffe8298803fe414c401fea0a6223ff10531017fe629880bf7314c405ff18a6200f78c531017f8629880bdc314c405fa18a6222ffc8531117f84298803ff604c4017fb026200ff98131007fac098803fc604c4097e3026224ffd4131127fca098893fd504c449fe2826223ffd013111ff8809880bff304c405f
  | 5 => 0x38108060680000000000203c030050000100900a000004020020000300400000e000088050000240000f000008000020120000c02f0060040081001601c0a0000100140001000603c0080805002401833026004020050140400180900a0001500000000007001004014010090060100108c0060200180104605001bfb22a6009fd915317efcc8a98037d6454c5fbe322a602dfd8d53014fec6a980f5f6354c05bfa1aa602df90d53016f886a98037f6254c5dbf312a600df58953176f8c4a98bf7f4254c5dbf212a62edf10953016fe64a980b7e3254c05be192a600dfd8553006fcc2a98037d6154c01be30aa6009f1855317efe82a98bf7c4154c05bf98aa602df0c553176fe42a98bb7c2154c01bfb02a600df98153006fac0a98037c6054c5fbfa02a62fdf10153016fe60a980b7c3054c5dbf902a62edf0815316ffecaa18b6ff6550c5bff32a8603bf9954316efccaa180e7e6550c5bfeb2a862dbf59543006facaa18027d6550c5bfe32a8603bf19543015fec6a180bff5350c05bfa9a8602ff94d43017faa6a180b7d5350c05fe29a8602ff90d430177c86a180bfc4350c05ee21a8602e710d43007fec4a1802ff6250c59ff3128601bf98943007fac4a18b3fc6250c037e312862dffd4943167fca4a18b7fd5250c59fe2928602ffcc943017be64a180bfe3250c05fe1928600ffd8543005fec2a1803fe6150c01feb0a8600ff18543005f8c2a18b7ff5150c5bff28a862dff5454316ff8a2a18b77c5150c05ff98a8602ff0c543017b862a18b3ff2150c59fe10a8600ffd8143005fec0a1803fe6050c01feb028600ff18143025f8c0a18b7ff5050c5bff282862dff5414316ff8a0a180bff3050c05ef9828602ff0c143167fe40a18b3fc2050c57ffb2a642bbfd953215ffcca9900efe654c857feb2a642bbf5953215ff8ca9900efc654c801ffb226400bfd9132157fcc899062fe644c801feb226400bf59132157f8c899062fc644c857ffaa2642bdfd5132157fca8990affd544c801beaa2642aff1513200dfec69900bff534c805bfa9a6402ff94d32017faa69900b7d534c805fe29a6402ffd0d32017fc869900bde434c805fea1a6400f750d32017f88699006ff624c803ffa926401ff9493200ffaa499007fc524c803ffa126401ff9093200fdc8499007fd424c801f6a126401ff1093200ffe649900bef324c803ff1926401f78c93200ff86499007dc324c803f61926400ffd8532005fec299003fe614c801feb0a6400ff18532005f8c2990afff514c857ff28a642bff5453215ff8a2990af7c514c855ffa0a642aff10532017fe629900bfc314c803ff90a6401ff0853200fd84299003ff604c8017fb026400ff98132007fac099003fc604c8097e302642bffd413215ffca0990affd504c857fe282642affd0132157f88099
  | 6 => 0x5550cda8000000b80fd0001f90b626e9a488c1798448f3012047e851a00c782c92d8644001900b00956280638b402ce858199768069a88848e05818410909e307b86013691511426e6511b1dc61840d11a4dd49a9a088b18f5620cb45f5124e6cdaf17640f01904881613a87dd039c1974cb30e48000000328000000ac8c9cc423080006c8e5e342191a68000002680000000000012195ed13b87c9d90ff10d97e923a4d27c896df68520ee0000158000001a6cd612f1220911a586d00000000019899304c8000e1c002350bd99614da6617b98905ca5d0f00000670c615080000016b010808061832d6809d17227394480015c27d87d8968b083e1dd1178b88c1908a1188a9bf15804353b05f247872c17a5a0f34e46658700428a900e4b12899fe171a500e188c83010a23b826122da20db25900619e8000d90ae0001861b68c988ae4900008d22718c05f4afa2985806aa311a38aba56161020cd94db8bb80009da081eb8001ce23708100008bcd78bd25818018a88b8282742832244cd04315e0bf94ca2380000016c9d3a054080000040000a01301203c01800002008030150000000300300007c0000901a01000000012010068110120100681901401014803000024130050020000400601a00c0080000601802800000004008020100080980705209005805022008060010220040780000003c0001a028010000050360040000000000c000060260040b80000000807000000024018400020640080400a0e40200a0360040000100a00c0100000c004000040040600180000000001019002000010000020600f009000020028180040000600100a00c030040260080401101800c0500f0040180c01100006c0401a04a0180f00000402c0101800000800800000000110000200840f002000008018200000100000200a008050040040200480103a0000980303c0040080c00001c05004050020000010000a00481e0040000000a00400c060030100180080302a01c020010060140700b0080200080000e008030160320001480400c02003004002130008090040080080700001407000000058000000160000001703e00010804000000008030140000000200c0000001d022014028020020240000c012014028030040000380300206c0d00000202400000000010010010000000080000c0040601500800c000010060000180202400401011000044008010000100103707c0040a80104a0000000000800002000002020070000120380000d0100000380500007c05003034020060010100000280600400002003008008000000020100a802000004040040000641080105807c0c80000a0580f800002000018000160000081400000c0200b0300240002000c004000030020180100400e0540081100c018028000140240100900e0080080c08c
  | 7 => 0x1aa8568000000074eaa1d9cca6024259f547a7e13203780010f895d1b1409572644e117061e0a321c0ad91826d8ab47a12619d094418a489ce8c049f8f5929dcc0478f95b20e0d832529c8a550000df6010002078fb0000229758001439b41601b4ce90c891e9ae844c0018a00012e8bd673072000255587e6209c05315ae3d07e8000f48398002598000000628001e6160400074510c000001131371b90caa729ea0a08fc9406758322369ce41bd420000292268000001ee0d308788e26bc0011601b1d2145a4a05e95b40002b4e99d70dc80014fd5860f13e846c9c8000000a367a9ef9af5ca19fa264c380000b17f88da208bfc00048428901a4820f9d51c5856c4fa578e3511046421c5753f21c8ab06f02a0002768dc218d308001daa1794513491c9a65f28ee957a469f815b92f8000f61879738ea17448002066c4a3d329858b581b8798e51b813517a5784ba8cc0d2475041a4999fe4f0890724b39318491b0c86d218001bc9f98d4800000227a7b8590000000000001c784600009711a0558fd84d07e0401b6071a4c24b03802b1378b3e170eba2d0218ca0f4c3a14298e124533931000211114912873d500b287703866c0a583a9158c30bf40017403ea6912b19b0548000a20000169b09f40e3c60a3302e9e09fc0249dc27f80024080000005d20ba1f2008390e58fe00d4000001f3a039958978d69001ec1b06188001e98ff9838001e89aedcf05c10f15040a93a0620395df838a4000090421f6818ad225ca98000000ec159c000358001bb1da00015a80000000010200001c00000027c00014f1048a8a04e76086a2b19e1e4a889a1124a2010927825c4d22710000f220d1010ae9bc074989949071d6947e61992c9eaa3b07ecd70cae2065a80000017d90312a1ac21f809a0e9599fd4649668ca49492813d86fc001b54000a698b21e81f28726c90099d8000df84203100005d8000564000000508540fa87697481cdab0001e700d9eb000159400209800157e2e1200b48000e21c0a221fa8dd0000000370bb4000aa24f9fe80016e1d8a4b80000022317d0450808000a005387d1869fc9980001a28348135ff1910cc80007c0000552881a792284b6809fba668c924ca771ee98ed550a2c7155191da6d40dcf50001d79099a040000021208416997543c80019482d03f81e68208a000034c001921f78000d088880000021696f5e80984a110a5fd991c000e29fb0fc0bcc00210a1d181d34242e8113d2388000d400011e0f788302595b02f07110e2451b2978e7e863221990dd81e4102e8a1d7cc486524114c0561d31848cfa70a828f993341e179169d9068406366ee1d4d58734679fa0658a291f97b5f4976c1dccd82241c4f08bc898dd61b492e19b8b2059a7f17b0000000e4039c000b50640a60001b3d5323da040c6a2b8b24e
  | 8 => 0xc708c44f07a852a5e1b70be968a72110845c6e16c1a18000739d58dae752462348cb18c9c281f4c80951f10e003382215a18d5e687f26709ba6393fa1fc0014a01411723180014a80016705a27d000051a070788c08b981d4cb54810280016da5b80007787f5c41c9c0000000d14d27b261000003800022c000458002328454f880022a8000002160000850000000e30001ad000000005c0006b80000011200000022e84718d179d7966f91d0001ac85dc43cbe12a8002641e113618525c0030e3977d7026dc1a22f9079a3175d4420b15205b21301ec04a63e0e1c480009a1a09979e78002532149690270000000001b0280093d0695e82c2790214001358000854b68aa50ea839e90eca544001fd15fde012086e8c00002031d283526fc480f8e3e9d99100a7a1a03b89300012946991194621417a0dee021914001a0c82a54ccf1e3a6f49a8de01ea459c74ba19a186c129562292589e50c700020c8000148ed00592c17740003b000248d299c0012e2a1559ba22595918d81504a821097400000105a26cbaddd5909bd95399189386f40911889e06b05e0995d41a5ced9709a866899c82d800018262c63cde8138fa03d1512540476379e295d26f1b2e3ca6297f049e6482416e95fa09177026927034539836a420501c1013d3899414b8aa81304bc2b85e59710520c17c04ba65097c0f96edaf9a41515c21f09c920a9710761b1a5711393800026309e943000070c001870000000000b3562000099d638001b398e5974498f1000224c0022f16f80004d9ca9c307567a2430d164416fd27800084df8d5d8aac00263546a4e24280011680016f2159190f90690fb8ce8bc5b8a2da5d88226a8e817c81a80026ba2480018fc0000016b9f711f0408002002128001be8708001938efc0c274800048d9280013c9874001dd8000940002799c50df1cd00020a0110000c2a0d800000070400000034158800243a5206ec000e61ff96400014b1c380000e8000bc01d8000001b98001d680000000026b13000011b9ed88657314b4000000000e89bb9ae5650e24001210ba51a8bbc001ad82bc440209b78572138000c596782c66e00798fa029df178875894e5e80ec85a5be702019f00becdfdf884e98116d1f60a39e1a1005f8d18f717ac6697a98de5c8001f30e697816a98f56300000a0001761b5874e3812500000000000002e0990ac08b6321ae08e82386612b8fbcc0c000250c20278000d9e0b52c4e2c85e5582aa5ccb78ef2302879bf80010d1060001609db9241ba8bddcb8ef89645116ad9a8000000d1c0000012d0001cd8000002448145575498018588b70e15259569cf82994ea548861889660468001aba21099a4e88f01d0360318c52254001924001d000706121803096580005ec000000000000f18000be41fc001b35be0a522c95c896
  | 9 => 0xda1881e596a50b1c685a90c06c11c1ec8a480000010a8001de8e4d8f0fe8abcf400280008b1071e2000128a778da4001081390000000000d989188823904b0001649b30d3a35a4a8b4e518a712308f9528001829a81729ef2788c11884171d1a241afe04800064cd810b80000e000068a4719f00019528914880013c03d9809de0d880023a1db0000731b500006f80004a4001778325629cb26784ac92857806c002609b449224d954196e0594700641c8a1a39857e1b02f9dca698d004c23f04c62889007b0838bf0dd95be05154843a3c0742068af0bb14003c06a199a6d123c3f23f8a422618e88980016a04a26a14e1b15a7c001f1a3aa2502022c1b24d500021512680000008721ccd28e08958088a444e0f44eb2869c810ac7918209a40218b93add10f8158c1f80521b8001751a91a514f8e723e023078033c000002508cba06215c000000f395c5332338b2c7f80000c8000000001b100018248740009812900000000014ac000000041968d2e5f8444331a544950ca56a719d0a6ac0000028a8682861418000101aa06e57e0818ce09ac6d96180000022280025380019900019c05b8000001bd00000015f09b0f295a40b9199a700000021a838c001f58118e78334728f68001a740024193e0988000b9e36284a61a5f0001410b925b0001f21c99a60a800009f1
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe7550c100057d7550c10016de6350c10006dd6350c100379c4350c10005fb7050c10025f87050c10004ff75588100067f75588100047f755881001cfe7558810004fd755881001cfc75588100067c755881001c7c7558810004ff7358810014fe7358810014fc73588100067f53588100067d5358810026ef725881002eee5258810006ed525881002eee325881000cff715881000cfd715881002cfc71588100067c515881002eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810004ff764c810024fe764c810004fd764c810024fc764c810016de634c810006dd634c81000eee624c810006ed624c810005f7714c810005f4714c8100467f769441001e7e769441001e7d76944101c67c76944100057d73944101c67f639441014e7e63944100067d63944101c67c63944101c67f62944101467e62944100067d62944101c67c62944101cd7e719441003f7671944100467e61944101c77a70944100077970944101c67e60944101c77710944101c77a10944101c7751094410084ff768c410024fe768c410014fd768c410024fc768c4100057f758c41003d7c758c410016de638c410006dd638c410086f6618c410025fa708c410005f9708c410084ff764c4100057f754c41003d7c754c410005ef724c41002dec724c410086f6614c41007cff7688410024fe768841000cfd7688410024fc768841000eee6288410006ed6288410025fa7088410005f97088410006ef768841000eee768841000eed76884101aeec76884101aeef65884100f6ee65884101b6ed65884101aeec65884101aeef638841010eee6388410006ed63884101aeec63884101b76f53884100076d5388410195ee71884101beee61884100076e51884101b76c51884101afea7088410007e970884101aeee60884101afe710884101afea10884101afe5108841007cff76484100057f754841003d7c754841000eef7608410196ee760841002eed760841000eec7608410196ef65084100eeee65084101a6ed6508410196ec6508410196ef63084100e6ee6308410006ed6308410196ec63084101a76f53084100076d53084101adee710841002fe6710841007eee61084100076e51084101a76c510841019fe7310841019fe43108410197ea700841002fe97008410196ee6008410197e71008410197ea1008410197e51008410025fb7644010006fb7644010004fb76440100077b7544010187787544010007db7344010007d873440101877b5344010007795344010007eb7244010007e87244010025fb7144010027f3714401018efa6144010027f261440100077a5144010187f25144010007725144010187f15144010187785144010007ea2144010007f22144010007e22144010007f12144010007e82144010
  | 1 => 0x8510007cc638851010ecc63885101ff6f53885100076d538851004dee71885100076e51885101ff6c5188510007e63188510007e531885101afe61088510024fc76485100057f754851005d7c75485100067f65485101067c6548510006df63485100fedc6348510006ef624851000eec6248510005fb7048510025f87048510005ee760851004eee7608510004ee76085101eeef65085100076f65085100066f65085100eeee65085101eeed65085100eeec65085101ef6c65085100ee6c6508510006ef6308510007cf6308510006cf63085100e6ee6308510006ed63085100e6ec6308510007cc63085100e6cc63085101ef6f53085100076d53085101f5ee710851004fe671085101efe751085100076e51085101ef6c51085101efe451085101ef645108510007e63108510007e53108510197e61008510014ff764c110054fd764c110014fc764c1100067f654c1100be7c654c110006bf644c1100b6bc644c110006df634c110016dc634c110006ef624c1100aeec624c110005f7714c110005f4714c11000cff764811004cfd764811000cfc76481100057f754811005d7c75481100067f65481100967c6548110006df634811008edc6348110006ef624811000eec6248110005f77148110005f47148110027e82048110027f010481100067f65c41100467c65c4110006df63c4110086dc63c4110006ef62c411007eec62c4110025f671c4110026f761c4110025fa76c4110026fa76c4110024fa76c41100077b65c41101e77865c4110007db63c4110007d863c41101e77b53c41100077953c4110007eb62c4110007e862c4110025fa71c4110026fb61c4110027f361c41100077a51c41101e77851c4110007f231c4110007f131c4110007ea21c4110007e821c4110004ff7558c1001cfe7558c10004fd7558c1001cfc7558c10004ff7458c100c4fe7458c100c4fc7458c100067f5458c10026df7358c100367f5358c10036de5358c10006dd5358c10036de4358c10004ff7258c1000cfe7258c1000cfc7258c10036df3258c10014ff7158c10014fd7158c10034fc7158c100067c5158c10036dc3158c10024ff7058c10024fe7058c10024fd7058c10024fc7058c10026de3058c10026dc3058c10026f71058c10026f51058c100067f7654c101d67e7654c100067d7654c101d67c7654c100057f7454c101d67f6454c1017e7e6454c100067d6454c101d67c6454c101dd7f7354c1003f5f7354c101d67f6354c100167e6354c101d75e6354c100165e6354c100367d6354c101d75d6354c100065d6354c100167c6354c101d67f6254c101767e6254c101d67c6254c100057c7154c100867e6154c101d67e6054c101d7771054c101d77a1054c101d7751054c10004ff7650c10024fe7650c10004fd7650c10024fc7650c1003d7
  | 2 => 0x4ee7618910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc63189100076f53189100076d5318910196ef61189100076c5118910197e61018910197e41018910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c91015e7c654c910006bf644c910156bc644c910006df634c910016dc634c910006ef624c91000eec624c9100057e76945100767e76945100747e76945100057d73945100067f63945100075f63945100065f639451014e7e63945100067d639451014e7c63945100075c639451014e5c63945100067f62945100076f62945100066f62945101467e62945100067d62945101467c62945100076c62945101466c629451005d7e719451005f7671945101c776109451006cfe768c5100057f758c51005d7c758c5100067f658c51013e7c658c510006bf648c510136bc648c510006df638c510016dc638c510006ef628c51012eec628c51000776518c51021774518c510005f6768c51006ef6768c51000777758c51021774758c51000777658c51021774658c510005f7748c510005f5748c510007b7648c510007b4648c51021777548c51000775548c510055f5738c510007d7638c510016f6638c510016f4638c510057d4638c510016d4638c51005777538c51005775538c510057d6438c510007d5438c510007e7628c510007e4628c510025f6708c510025f4708c51020fd6308c51020fd4308c510024fc764c5100057f754c51005d7c754c5100067f654c5101267c654c510006bf644c51011ebc644c510006df634c510016dc634c510005ef724c51004dec724c510006ef624c510116ec624c51000776514c51020774514c510005fb704c510025f8704c510025f4764c510016f4764c510024f4764c51000777754c51020774754c51000777654c51020774654c510005f7744c510005f5744c510007b7644c510007b4644c51020777544c51000775544c510055f7734c510007d7734c510007d7634c510016f6634c510016f4634c510057d4634c51005777534c51005775534c510007e7724c510007e4724c510007e7624c510007e4624c510007f3704c510025f6704c510025f4704c510007f0704c510064fe76885100067f65885100f67c6588510006df638851010edc6388510006ef628851000eee6288510006ed628851000eec6288510005ee7688510006ee7688510004ee76885101feef65885100076f65885100066f65885100f6ee65885101feed65885100f6ec65885101ff6c65885100f66c6588510006ef6388510007cf6388510006cf638851010eee6388510006ed638851010eec638
  | 3 => 0xc7654d100067c7654d100047c7654d100057f7454d100067f6454d100073f6454d100063f6454d1017e7e6454d100067d6454d1017e7c6454d100073c6454d1017e3c6454d100557f7354d1005f5f7354d100567f6354d100075f6354d100065f6354d100167e6354d100567d6354d100167c6354d100575c6354d100165c6354d101767e6254d101767c6254d101766c6254d100057c7154d101d7761054d10004ff7650d10004fe7650d10004fd7650d10004fc7650d1005d7e7550d100057d7550d100067f6550d1016e7c6550d10006df6350d10016dc6350d100579c4350d10166ec6250d1000cfe76d89100067f65d89100067c65d8910006df63d8910006dc63d891004eee62d8910004ff75d891001cfe75d8910004fd75d891001cfc75d8910014fe73d8910004fd73d8910014fc73d89100067f53d89100067d53d8910006ef52d891004eee52d8910006ed52d891004eec52d8910006ef32d891004eee32d891004eec32d891000cfe71d8910024fd71d891000cfc71d89100067c51d891004eef21d8910024fe70d891004cfd70d8910024fc70d891004eef20d891004dee76d891000cee76d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d89100076f53d89100076d53d89100076c51d89101afe610d89101afe410d8910006ef75d8910006ee75d8910006ed75d8910006ec75d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d89100066f53d8910006ee53d8910006ed53d89100066d53d8910006ec53d8910006ee43d8910006ed43d8910006ec43d89101aeef71d891004eee71d891000cee71d8910006ed71d891000cec71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d89100066c51d8910006ef31d8910006ec31d8910006ef70d89101aeee70d8910006ed70d89101aeec70d8910006ef50d89101aeee50d8910006ed50d89101aeec50d8910006ef30d89101aeee30d89101aeec30d89101aeee10d89101aeec10d89100057f755891005d7c75589100067f65589100067c6558910005df7358910055dc7358910006df6358910006dc635891004eec6258910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7358910006df7358910004df7358910014fe7358910014fc7358910006dc7358910014dc73589100067f53589100067d535891004cff7258910006ef7258910064ff7158910006f771589100067c515891004eec215891007cff7058910006fb7058910005ee761891004eee7618910
  | 4 => 0x8d10056de43d8d10056dc43d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10056df32d8d10006de32d8d10056dc32d8d10014fe71d8d10024fd71d8d10014fc71d8d100067c51d8d10056df31d8d10024fe70d8d10054fd70d8d10024fc70d8d10056df30d8d10055de76d8d10014de76d8d100075f75d8d100075c75d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dc64d8d100075f54d8d10006de62d8d10006dc62d8d1020fd771d8d100075c51d8d1020fd610d8d1020fd410d8d10006df75d8d100065f75d8d10006de75d8d10006dd75d8d10006dc75d8d100065c75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d100065f54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d10006df42d8d10006de42d8d10006dc42d8d1020edf71d8d10056de71d8d10006dd71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d100065c51d8d10006df41d8d10006dc41d8d10006df21d8d10006dc21d8d10006df70d8d1020ede70d8d10006dd70d8d1020edc70d8d10006df50d8d1020ede50d8d10006dd50d8d1020edc50d8d10006df40d8d1020ede40d8d1020edc40d8d10006df20d8d1020ede20d8d1020edc20d8d1020ede10d8d1020edc10d8d100057f7558d1005d7c7558d100067f6558d100067c6558d10005bf7458d10225bc7458d10006bf6458d10056dc6358d10005ef7258d1004dec7258d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d100c4fe7458d100c4fc7458d10006bc7458d100c4bc7458d100067f5458d10054ff7358d10006df7358d100567f5358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d1006cff7158d10006f77158d100067c5158d10084ff7058d10006fb7058d10005de7618d10056de7618d10004de7618d100575e7518d100575d7518d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d100075f5418d10006de6218d10006dc6218d10057d57118d1021edf6118d100075c5118d1021fd61018d1021fd41018d100067f7654d100057e7654d100067e7654d100047e7654d100067d7654d100057
  | 5 => 0x1c67c62946101cd7e71946100777671946101c67e60946101c7771094610054fd768c6100057f758c6100757c758c61013e7e658c6100067d658c61020edf638c610016dc638c61012eee628c610006ed628c610014ff764c610024fc764c6100057f754c6100757c754c6101267e654c6100067d654c610016de634c610006dd634c610005ef724c610065ec724c610116ee624c610006ed624c610005fb704c610025f8704c61004cfd76886100f67e65886100067d65886101aeef628861000eee6288610006ed628861000eec62886101aded7688610006ed76886101aeef65886100f6ee65886101af6e65886100f66e6588610246ed65886101af6d65886100066d65886101aeec65886101aeef638861010eee6388610006ed63886101aeec63886102476f53886100076d53886100076e51886102476c51886101afe7108861000cff7648610024fc76486100057f75486100757c75486101067e65486100067d654861000eee6248610006ed6248610005fb7048610025f87048610195ed7608610066ed7608610196ef65086100eeee65086101976e65086100ee6e650861023eed65086101976d65086100066d6508610196ec6508610196ef63086100e6ee6308610006ed6308610196ec630861023f6f53086100076d5308610067e671086100076e510861023f6c5108610237e73108610237e43108610197e71008610025f976c4210006f976c42100277a65c42100277965c421022f7b53c42100077953c4210027ea62c4210027e962c4210027f271c42100077a51c421022f7851c4210007ea21c4210007e821c421005d7e76d951005e7e76d951001c7e76d95100057d73d95100067e63d95100067c63d95100067e62d95100067c62d951005d7c71d95101c77610d95101c77410d95100067f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f32d95100067e32d95100067c32d95101c67f71d951005e7e71d951001c7e71d951005e7d71d951005e7c71d951001c7c71d95100067f31d95100067c31d95100067f21d95100067c21d95100067f70d95101c67e70d951005e7d70d95101c67c70d95100067f30d95101c67e30d95101c67c30d95100067f20d95101c67e20d95101c67c20d95101c67e10d951005e7d10d95101c67c10d9510014fe76d8d1005d7c75d8d100067f65d8d100067c65d8d10056de63d8d100075f53d8d10004ff75d8d100067f75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d100067c75d8d1001c7c75d8d100c4fe74d8d10004fd74d8d100c4fc74d8d100067f54d8d100567f53d8d10006df53d8d100065f53d8d10056de53d8d10006dd53d8d10056dc53d8d10006df43d
  | 6 => 0xf70596100267e70596100267d70596100267c70596100267f30596100267e30596100267d30596100267c30596100267f20596100267e20596100267d20596100267c20596100267f10596100267e10596100267d10596100267c1059610004ff7558e1001cfe7558e100067e7558e1001c7e7558e10004fd7558e100067d7558e1001cfc7558e10004ff7458e100c4fe7458e100c4fc7458e100067f5458e10026df7358e1006e7f5358e1006ede4358e10004ff7258e1000cfe7258e1000cfc7258e100067c5158e1006edf3158e10024fc7058e10026de3058e10026dc3058e10026f71058e10026f51058e101d57f7654e100067f7654e100047f7654e101d67e7654e101d57d7654e100067d7654e100047d7654e101d67c7654e100057f7454e101d67f6454e1017e7e6454e100067d6454e101d67c6454e101dd7f7354e100775f7354e101d67f6354e100167e6354e1006e7d6354e100167c6354e101d67f6254e101767e6254e101d76e6254e101766e6254e101d76d6254e101d67c6254e100057c7154e100567d6154e101d67e6054e101d7771054e10004ff7650e10024fe7650e10004fd7650e10024fc7650e100757e7550e100057d7550e1016e7e6550e100067d6550e10016de6350e10006dd6350e1006f9c4350e10166ee6250e10004ff7558a1001cfe7558a10004fd7558a1001cfc7558a10004ff7358a10014fe7358a10014fc7358a100067f5358a100067d5358a10026ef7258a10006ef5258a10066ee5258a10006ed5258a10066ec5258a10006ef3258a10066ee3258a10066ec3258a100067c5158a10066ef2158a10024fc7058a10026ee2058a10026ec2058a10006ef7558a10006ee7558a10006ed7558a10006ec7558a10006ef7358a10006ee7358a10006ed7358a10006ec7358a10006ef5358a100066f5358a10006ee5358a10006ed5358a100066d5358a10006ec5358a10006ee4358a10006ed4358a10006ec4358a10006ef7158a10006ed7158a10066ec7158a10006ef5158a10006ee5158a10006ed5158a10006ec5158a100066c5158a10006ef3158a10006ec3158a10026ef7058a10026ee7058a10026ed7058a10026ec7058a10026ef5058a10026ee5058a10026ed5058a10026ec5058a10026ef3058a10026ee3058a10026ed3058a10026ec3058a10026ef1058a10026ee1058a10026ed1058a10026ec1058a10004ff764ca10024fe764ca10004fd764ca10024fc764ca1015e7e654ca100067d654ca1000eee624ca10006ed624ca10005f7714ca10005f4714ca101c57d769461005e7d769461005c7d76946100057d73946101c67f639461014e7e63946100067d63946101c67c63946101c67f62946101467e62946101c76e62946101466e62946100067d62946101c76d62946100066d6294610
  | 7 => 0x8b10014fe7358b10014fc7358b100067f5358b100067d5358b10006ef7258b10024fc7158b100067c5158b1007eec2158b1007eef2058b10004ff764cb10004fe764cb10004fd764cb10004fc764cb10006ef624cb1000eec624cb1001e7e769471001e7d76947100057d73947100067f639471014e7e63947100067d639471014e7c63947100067f62947101467e62947100067d62947101467c62947100457e71947100477671947100077a7094710007797094710024fd768c7100057f758c7100457c758c710016de638c710006dd638c71000776518c71025f74518c710025fa708c710005f9708c710025f5768c710016f5768c710024f5768c71000777758c71025f74758c710005f7748c710005f5748c71025f77548c71000775548c710016f6638c710087d6638c710007d5638c710016f4638c71008777538c71008775538c710087d6438c710007d5438c710025f6708c710007f2708c710007f1708c710025f4708c71020fd6308c71020fd4308c710034ff764c7100057f754c7100457c754c710005ef724c71007dec724c71000776514c71025774514c710005f7764c710036f7764c71000777754c71025774754c710005f7744c710005f5744c71025777544c71000775544c710007d7734c710016f6634c710016f4634c71008777534c71008775534c710007e7724c710007e4724c710025f6704c710025f4704c710024fd768871000eee6288710006ed6288710025fa7088710005f9708871000eee768871000eed76887101beef65887100f6ee65887101beed65887100f6ec6588710006ef638871010eee6388710006ed638871010eec63887101bf6f53887100076d53887100076e51887101bf6c5188710007e63188710007e53188710007ea7088710007e9708871002cff76487100057f75487100457c754871007eee760871007eed760871024eef65087100eeee650871024eed65087100eeec6508710006ef63087100e6ee6308710006ed63087100e6ec630871024f6f53087100076d530871007fe6710871024fe751087100076e510871024f6c510871024fe4510871024f645108710007e63108710007e5310871007fea700871007fe97008710014ff764c310014fc764c310016de634c310006dd634c310005f7714c310005f4714c31000cff764831000cfc76483100057f75483100457c754831000eee6248310006ed6248310005f77148310005f471483100067f73596100047f73596100067e73596100067d73596100067c73596100067e43596100067c43596100067f72596100067e72596100067d72596100067c72596100067f32596100067e32596100067c32596100767f71596100767e71596100067d71596100767c71596100067f31596100067c31596100067f21596100067c21596100267
  | 8 => 0x67c61945201476c21945201467f60945201477b20945201c76e20945201c76c2094520147782094520004fe768c520004fd768c520004fc768c5200057f758c5200957c758c5200067f658c52013e7c658c520006df638c520016dc638c52000dec728c520004ff764c520004fe764c520004fc764c5200057f754c5200957c754c5200067f654c5201267c654c520005ef724c52000dec724c520024ee768852026def758852026ded7588520266ef65885200076f65885200066f65885200f6ee6588520266ed65885200f6ec65885202676c65885200f66c6588520005ef7388520005ed7388520006ef638852010eee6388520006ed638852010eec63885202676f53885200076d538852000dee718852000fe67188520006ef6188520007e76188520006ec6188520007e46188520006e461885200076e51885202676c5188520025ee7088520007ea7088520025ea7088520007e97088520025ec708852000eef608852000feb6088520014ff764c12000cfe764c1200acfd764c12000cfc764c1200067f654c1200be7c654c120006df634c120016dc634c120005ef724c12000dec724c120086de63d8f10004ff75d8f1001cfe75d8f10004fd75d8f1001cfc75d8f100c4fe74d8f10004fd74d8f100c4fc74d8f100067f54d8f10084fd73d8f100867f53d8f10086de43d8f1000cfe72d8f10004fd72d8f1000cfc72d8f10006f671d8f100067c51d8f10006f970d8f1020ede30d8f1020edc30d8f10014ff7658f10086dc6358f10004ff7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f100c4fe7458f100c4fc7458f100067f5458f10006df7358f100867f5358f10004ff7258f1000cfe7258f1000cfc7258f10024fc7158f100067c5158f10086dc3158f10086df3058f100067f7654f100067e7654f100067d7654f100067c7654f100057f7454f100067f6454f1017e7e6454f100067d6454f1017e7c6454f100857f7354f100475f7354f100867f6354f100167e6354f100867d6354f100167c6354f101767e6254f101767c6254f100057c7154f10004ff7650f10004fe7650f10004fd7650f10004fc7650f100457e7550f100057d7550f10006df6350f10016dc6350f100879c4350f10005fb7050f10025f87050f100457e75d8b100057d75d8b1007eee62d8b10004ff75d8b1001cfe75d8b100067e75d8b1001c7e75d8b10004fd75d8b100067d75d8b100047d75d8b1001cfc75d8b10014fe73d8b10004fd73d8b10014fc73d8b100067f53d8b100067d53d8b1007cfd72d8b1007eee52d8b10006ed52d8b1007eee32d8b10006f671d8b100067c51d8b10006f970d8b101aeee20d8b101aeec20d8b1000cff7658b1007eec6258b10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff735
  | 9 => 0xc7158d20006f47158d20004f47158d200067c5158d200aeec2158d20294ff7058d20006fb7058d200067f7654d200057e7654d200067e7654d200047e7654d200067d7654d200057c7654d200067c7654d200047c7654d200057f7454d200067f6454d2017e7e6454d200067d6454d2017e7c6454d2028d7f7354d200975f7354d2008e7f6354d200167e6354d2008e7d6354d200167c6354d201776e7254d200076d7254d201d67f6254d201776e4254d201776e3254d200057c7154d201776c2154d201767f6054d201777b2054d201d76e2054d201d76c2054d20177782054d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200957e7550d200057d7550d200067f6550d2016e7c6550d20016de6350d20006dd6350d2008f9c4350d2000dee7250d20025ec764c920016ec764c920024ec764c920285ef754c920285ed754c9200076f654c92027f6c654c920005ef744c920005ed744c920006ef644c920006ed644c92027f6f544c9200076d544c92000def734c92000fcf734c920007cf634c920016ee634c920016ec634c92008fcc634c920016cc634c92008f6f534c92008f6d534c92008fce434c920007cd434c920005ec714c92027f6c514c920007eb704c920025ee704c920025ec704c920007e8704c92000eef604c92000feb604c9200957e75d85200057d75d85200067f65d85200067c65d8520004ff75d852001cfe75d85200067e75d852001c7e75d8520004fd75d85200067d75d85200047d75d852001cfc75d8520014fe73d8520004fd73d8520014fc73d85200067f53d85200067d53d8520024fd72d85200067c51d8520006f731d8520006f431d8520066f621d8520066f521d8520066ec21d85200957e75985200057d75985200067f65985200067c6598520006f7619852004df970985200057f75585200957c75585200067f65585200067c6558520005df735852008ddc735852007dfb70585200957c75185200067f65185200067c6518520006f56118520004ff75185200067f751852001cfe7518520004fd751852001cfc75185200067c751852001c7c7518520014fe7318520004fd7318520014fc73185200067f53185200067d5318520196ef7218520024fd721852002eee5218520006ed521852002eee3218520006ed32185200067c5118520006f73118520006f4311852002ef6211852002ef52118520024fe7018520024fc7018520196ee2018520196ec20185200067f76945200057e76945200067e76945200047e76945200067d76945200057c76945200067c76945200047c76945200057d73945200067f639452014e7e63945200067d639452014e7c63945200076f72945201476c72945201c67f62945201476e32945200076d32945202757e71945200977671945200067f6194520
  | 10 => 0x46200067d61946201476c21946201c67e60946201c76f20946201477b20946201c7782094620004ff768c620024fe768c620004fd768c6200057f758c6200a57c758c620006f6618c620006f5618c620004ff764c620004fd764c620024fc764c6200057f754c6200a57c754c620005ef724c62000dec724c620006f6614c620006f5614c6201aeef65886200f6ee65886202beed65886201aeec65886201aeef638862010eee6388620006ed63886201aeec63886202bf6f53886200076d538862000dee718862000fe67188620006ee61886201afe66188620006e66188620006ed61886201afe561886200076e51886202bf6c51886201afea70886201aded7088620007e9708862000eee608862000fea60886202b57e76d95200967e76d952001c7e76d95200057d73d95200067e63d95200067c63d95202a76f72d95202af6c72d95202af6e32d95200057e71d95202af6c21d95202af7b20d95202a76e20d95202a76c20d95202af7820d95200067f73d95200067e73d95200067d73d95200047d73d95200067c73d95200067e43d95200067c43d95202a67f72d95202ae7e72d95202ae7d72d95202ae7c72d95202ae7f32d95202ae7e32d95202ae7d32d95202ae7c32d95200067f71d95200067e71d95200047e71d95200067d71d95200067c71d95200067f31d95200067c31d95202ae7f21d95202ae7e21d95202ae7d21d95202ae7c21d95202ae6c21d95202ae7f70d95202a67e70d95202ae7d70d95202a67c70d95200067f30d95202a67e30d95202a67c30d95202ae7f20d95202a67e20d95202ae7d20d95202a67c20d95202a67e10d95202a67c10d9520014fe76d8d200957c75d8d200067f65d8d200067c65d8d2008ede63d8d20004ff75d8d200067f75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d200067c75d8d2001c7c75d8d200c4fe74d8d20004fd74d8d200c4fc74d8d200067f54d8d2008e7f53d8d20006df43d8d2008edc43d8d20024ff72d8d2000cfe72d8d20024fd72d8d2000cfc72d8d200ceee42d8d200cedf32d8d200cedd32d8d20004fe71d8d20004fd71d8d200067c51d8d2008edc31d8d200ceec21d8d2000cfd70d8d2008edf30d8d200057f7558d200957c7558d200067f6558d200067c6558d20005bf7458d2029dbc7458d2008edc6358d20005f77158d20005f47158d20295fb7058d20004ff7558d200067f7558d200047f7558d2001cfe7558d20004fd7558d2001cfc7558d200067c7558d2001c7c7558d20004ff7458d20006bf7458d20004bf7458d200c4fe7458d200c4fc7458d20006bc7458d200c4bc7458d200067f5458d200ccff7358d20006df7358d2008e7f5358d2008ede4358d200acff7258d20006ef7258d200aeee4258d20004ff7158d20006f77158d20004f77158d20004f
  | 11 => 0x6ef6188530006ec61885300076e51885302df6c518853010eef608853010feb30885301afce30885301afcc308853010fe83088530004ff7648530004fe7648530004fc76485300057f75485300bd7c754853000eef76085300aeee76085300aeed760853000eec76085302ceef65085300eeee65085302ceed65085300eeec6508530006ef64085302d6ee6408530006ed64085302d6ec64085302cf6f54085300076d54085300afce73085300afcd7308530196ef63085300e76f53085300e76d53085300e7ce4308530007cd430853010dee71085300afe67108530006ef6108530007e76108530006e76108530006ec6108530007e46108530006e461085300076e51085302cf6c51085300afea70085300afe97008530296ef60085300e7eb3008530197ce3008530197cc30085300e7e83008530014fe76501302c4fd7650130014fc7650130005df7350130015dc73501300079d4350130004ff7558e2001cfe7558e20004fd7558e2001cfc7558e20004ff7458e200c4fe7458e200c4fc7458e200067f5458e20026df7358e2009e7f5358e2009ede4358e200aedf3258e200aedd3258e20004ff7158e20004fc7158e200067c5158e200aeec2158e20024fe7058e20024fc7058e20026de3058e20026dc3058e20026ef2058e20026ed2058e200067f7654e201d67e7654e200067d7654e201d67c7654e200057f7454e201d67f6454e2017e7e6454e200067d6454e201d67c6454e201dd7f7354e200a75f7354e201d67f6354e200167e6354e2009e7d6354e200167c6354e201767d6254e200057c7154e201776c2154e201d67e6054e201d76f2054e201777b2054e201d7782054e20004ff7650e20024fe7650e20004fd7650e20024fc7650e200a57e7550e200057d7550e20016de6350e20006dd6350e2009f9c4350e20004ff759862001cfe7598620004fd759862001cfc7598620014fe7398620004fd7398620014fc73986200067f53986200067d5398620006ef7298620026f67198620006f751986200067c5198620006f4519862000674519862007ef6219862007ef52198620024fe7098620026ef2098620026ed2098620026f61098620026f41098620004ff75586200067f75586200047f755862001cfe7558620004fd755862001cfc75586200067c755862001c7c7558620004ff7358620014fe7358620014fc73586200067f53586200067d5358620026f77158620006f751586200067c5158620006f4515862000674515862004ef6215862004ef5215862004eec2158620024fc7058620026f61058620026f410586200067f76946201c67e76946200067d76946201c67c76946200057d73946201c67f639462014e7e63946200067d63946201c67c63946201467d62946201cd7e71946200a77671946200067e619
  | 12 => 0xe76d89300aeee62d8930004ff75d893001cfe75d8930004fd75d893001cfc75d89300c4fe74d8930004fd74d89300c4fc74d89300067f54d89300067d54d8930024fd73d893000cfc73d893009e7f53d893009e7d53d893009ede43d8930006dd43d89300aeee32d893009eed32d8930004fe71d8930004fd71d89300067c51d89300aeec21d8930014fd70d89300aeef20d89300057f75589300bd7c7558930005bf74589300b5bc74589300aeec6258930005f77158930005f471589302fdfb7058930004ff7650930004fe7650930004fc76509300079d435093000eee62509300bd7e75d85300057d75d85300adee72d8530005ed72d8530004ff75d853001cfe75d85300067e75d853001c7e75d8530004fd75d85300067d75d85300047d75d853001cfc75d85300c4fe74d8530004fd74d85300c4fc74d85300067f54d85300067d54d8530024fd73d853006e7f53d853006e7d53d853000cfe72d8530006ee72d853000cee72d8530004fd72d8530006ed72d8530004ed72d853000cfc72d85300067c51d853006ef631d853006ef531d8530006f721d8530006f421d8530006f76198530055f970985300057f75585300bd7c7558530005bf74585300b5bc7458530005ef72585300adec7258530085fb7058530006f56118530004ff751853001cfe7518530004fd751853001cfc75185300c4fe7418530004fd74185300c4fc74185300067f54185300067d5418530024fd73185300367f53185300367d5318530036de4318530006dd431853000cfe7218530004fd721853000cfc72185300067c5118530036f63118530036f53118530006f72118530006f4211853021ede301853021edc30185300067f76945300067e76945300067d76945300067c76945300057d74945300067f64945302f67e64945300067d64945302f67c649453014d7f739453014d7d73945301c67f639453014f5e43945300075d43945300067f62945301467e62945301467c62945302ed7e71945300bf7671945300067f61945300067c619453014e7f609453014f7b30945301c75e30945301c75c309453014f783094530004fe7690530004fd7690530004fc76905300057f75905300bd7c7590530006bf64905300c6bc64905300079d4390530004ff7650530004fe7650530004fc76505300057f75505300bd7c7550530005ef72505300adec7250530004fe7688530004fd7688530004fc7688530006ef628853000eee628853000eec6288530006ef7688530006ee7688530006ed7688530006ec76885302deef65885300f6ee65885302deed65885300f6ec6588530006ef64885302e6ee6488530006ed64885302e6ec64885302df6f54885300076d54885301aeef638853010f6f538853010f6d538853010fce4388530007cd43885300adee7188530
  | 13 => 0xc6300075e518c63034f5c518c63020fda708c63020ddd708c630007d9708c630016de608c630017da608c630004ff7688630024fe7688630004fd768863000eee6288630006ed628863000eec6288630006ef76886301aeee7688630006ed76886301aeec76886301aeef65886300f6ee6588630346ed65886301aeec65886301aeef64886302e6ee6488630006ed64886301aeec64886303476f54886300076d548863010f6f538863010f6d5388630006ee6188630006ed61886300076e51886303476c5188630007ce318863010fcc31886301aeee60886301afcf308863010feb30886301afe83088630004ff7648630004fd7648630024fc76486300057f75486300dd7c7548630005df7348630015dc734863000eef7608630196ee76086300ceed760863000eec7608630196ef65086300eeee650863033eed6508630196ec6508630196ef64086302d6ee6408630006ed6408630196ec640863033f6f54086300076d54086300e76f53086300e76d53086300cfe67108630006ee6108630006ed61086300076e510863033f6c5108630007ce31086300e7cc3108630197ea70086300cfe97008630196ee6008630197cf30086300e7eb3008630197e830086300c4fe76d91300b6be64d9130004ff75d913001cfe75d9130004fd75d913001cfc75d91300b67f54d91300b6be54d9130006bd54d9130024ff73d9130014fe73d9130024fd73d9130014fc73d91303367f53d91303367d53d9130336bf43d9130336bd43d913000cfe72d9130004fd72d913000cfc72d9130006be42d91300b6bc42d9130004fe71d9130004fd71d91300067c51d91300b6bc41d9130014fd70d91300b6bf40d91300b6bc645913032dfb7059130004ff755913001cfe7559130004fd755913001cfc75591302c4ff7359130006df73591302c67f5359130004ff725913000cfe725913000cfc7259130004ff7159130004fc71591300067c515913032cff7059130006fb70591300067f76551300067e76551300067d76551300067c76551303257f74551300bf3f74551300b67f64551300073f64551300063f64551300c67e64551300b67d64551300c67c64551300b73c64551300c63c645513030d7f735513030d7d73551303167f635513030f5e435513031e7e625513031e7c62551300057c715513030e7f605513030f7b30551303175e30551303175c305513030f783055130025dc7650d300c6dc7650d30024dc7650d303075e7550d300075d7550d30015df7450d300179f7450d300079f6450d300c6de6450d300c6dc6450d300b79c6450d300c69c6450d300b75f5450d300b75d5450d300b79f4250d303075c5150d300b79c4150d30007db7050d30025de7050d30025dc7050d30007d87050d30016df6050d30017db6050d300b79f4050d3000cf
  | 14 => 0x24fc7059230026be4059230026bc4059230026df3059230026dd30592300067f76552303167e76552300067d76552303167c76552303557f74552300df3f74552303167f64552300c67e64552300d67d64552300c67c645523030d7f735523030d7d735523030e7d635523031e7e62552303167c62552300057c715523030f5c31552303167e60552303175f305523030f7b3055230317783055230004ff7558a300067f7558a300047f7558a3001cfe7558a30004fd7558a3001cfc7558a300067c7558a3001c7c7558a30004ff7458a300c4fe7458a300c4fc7458a300067f5458a300067d5458a3008e7f5358a3008e7d5358a30026ef7258a300ceee5258a30006ed5258a300ceee4258a300ceee3258a3008eed3258a30004ff7158a30004fc7158a300067c5158a300ceec2158a30024fe7058a30024fc7058a30026ee2058a30026ec2058a30004ff7650a30004fd7650a30024fc7650a30005df7350a30015dc7350a3000eee6250a30006ed6250a30004ff759863001cfe7598630004fd759863001cfc75986300c4fe7498630004fd74986300c4fc74986300067f54986300067d54986300867f53986300867d539863000cfe7298630004fd729863000cfc7298630026f671986300067c5198630086f63198630086f53198630024fe7098630026f61098630026f41098630004ff75586300067f75586300047f755863001cfe7558630004fd755863001cfc75586300067c755863001c7c7558630004ff7458630006bf7458630004bf74586300c4fe74586300c4fc7458630006bc74586300c4bc74586300067f54586300067d54586300567f53586300567d5358630004ff7258630006ef7258630004ef725863000cfe725863000cfc7258630006ec725863000cec7258630026f771586300067c5158630056f63158630056f53158630056dc3158630024fc7058630026f61058630026f410586300067f76946301c67e76946300067d76946301c67c76946300057d74946301c67f64946302f67e64946300067d64946301c67c649463014d7f739463014d7d739463014e7d63946301467e62946300067d62946301c67c62946301cd7e71946300df7671946300067e61946300067d619463014f5c31946301c67e60946301c75f309463014f7b30946301c7783094630004ff7690630024fe7690630004fd76906300057f75906300dd7c75906300c6bc6490630006f66190630006f56190630004ff7650630004fd7650630024fc76506300057f75506300dd7c7550630005df7350630015dc7350630005ef72506300cdec7250630006f66150630006f561506300075f758c63034f5c758c63020edf648c630006dd648c63034f5f548c6300075d548c630015de718c630017d6718c63020fd6618c630006dd618c63020fd5618
  | 15 => 0xe6154c2110e6e6154c21177666154c213bf6f4154c213bf6c4154c210e76f3154c210e76c3154c210076f7054c210076e7054c210076d7054c210076c7054c211776f6054c211776e6054c211776d6054c211776c6054c213bf6f4054c213bf6c4054c210e76f3054c210e76c3054c21165ef7650c2100dee7650c21165ed7650c2100dec7650c213b5ef7550c210edee7550c213a76e7550c210ed6e7550c213b5ed7550c210076d7550c210056d7550c210edec7550c213adef7350c21167ce6350c21167cd6350c210e76f5350c210e76d5350c210e7ae4350c210e7cc4350c210e78c4350c21005ef7150c21005ec7150c2110eee6150c21167e66150c213a76c5150c210e7cc3150c21005ef7050c21195ec7050c210e7cf3050c211476f76944211476e76944211476d76944211476c76944210076f739442139f6e73944210076d73944210056d739442139f6c73944211476f63944211476e63944211476d63944211476c639442139f6e43944210076d439442139f6c43944210ef6e71944212756e71944210ef6671944211476e61944210f66e619442114766619442139f6f319442139f6c31944210076f70944210076e70944210076d70944210076c70944211476f60944211476e60944211476d60944211476c609442139f6f309442139f6c309442112def768c42100dee768c42112ded768c42100dec768c421395ef758c4210076f758c4210056f758c4210edee758c421395ed758c4210edec758c4213876c758c4210ed6c758c421005ef748c4212d5ee748c421005ed748c4212d5ec748c4213876f548c4210076d548c421115ed738c42112fce638c42112fcd638c4210e76f538c4210e76d538c4210e7ce438c421007cd438c42138dee718c42110eee618c42112fe6618c4210076e518c4213876c518c42137fe7418c42137fe4418c4210e7cf318c4210e7e7318c4210e7e4318c421195ee708c421005ed708c4210e7cc308c421115ef764c42110eef764c42110cef764c421375ef754c4210076f754c4210056f754c4210edee754c421375ed754c4210edec754c4213676c754c4210ed6c754c421005ef744c4212d5ee744c421005ed744c4212d5ec744c4213676f544c4210076d544c42112def734c4210e76f534c4210e76d534c42136def714c42110eee614c421117e6614c4210076e514c4213676c514c42135fe7414c42135fe4414c4210e7e7314c421007ce314c4210e7cc314c4210e7e4314c421005ef704c421195ec704c421004ff755923001cfe7559230004fd755923001cfc7559230026bf74592300d67f54592302c67f53592302c67d53592302c6bf43592302c6bd4359230004ff725923000cfe725923000cfc7259230004ff7159230004fc71592300067c51592302c6dc3159230024fe7059230
  | 16 => 0x8d210c4fe7458d210c4fc7458d210067f5458d2112cff7358d21006df7358d210fe7f5358d21114ff7258d21006ef7258d2110cef7258d2136cff7158d21006f77158d210067c5158d21116ec2158d21004ff7058d21024fc7058d210067f7654d210057e7654d210067e7654d210047e7654d210067d7654d210057c7654d210067c7654d210047c7654d210057f7454d210067f6454d2117e7e6454d210067d6454d2117e7c6454d2128d7f7354d211075f7354d210fe7f6354d210167e6354d210fe7d6354d210167c6354d211767f6254d210057c7154d211767f6154d21177772154d211776c2154d21177742154d211d67c6054d21004ff7650d21004fe7650d21004fd7650d21004fc7650d211057e7550d210057d7550d210067f6550d2116e7c6550d21006df6350d21016dc6350d210ff9c4350d212757e76945213ce7e76945212747e76945210057d73945210067f639452114e7e63945210067d639452114e7c63945211467f62945212757e71945211077671945211467f61945211477721945211476c21945211477421945211c67c609452138cfe768c5210057f758c5211057c758c5210067f658c52113e7c658c521014ff764c52100cfe764c521114fd764c52100cfc764c5210057f754c5211057c754c5210067f654c5211267c654c521006df634c521016dc634c521005ef724c52100dec724c5213c6ef65885210076f65885210066f65885210f6ee65885213c6ed65885210f6ec65885213c76c65885210f66c6588521006ef638852110eee6388521006ed638852110eec63885213c76f53885210076d538852100dee718852100fe6718852100eef618852100fe761885210076e51885213c76c51885210067f65d81210067c65d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121014fe73d8121004fd73d8121014fc73d81210067f53d81210067d53d81210067e51d81210067c51d8121006ee21d812107eec21d812107efa20d81211057e75981210057d75981210067f65981210067c6598121006fb60981210057f75581211057c75581210067f65581210067c6558121005df73581210fddc73581210067f65181210067c65181211aeef6218121026fa6018121006f960181211776f7654c211776e7654c211776d7654c211776c7654c210076f7454c210056f7454c213bf6e7454c210076d7454c213bf6c7454c211776f6454c211776e6454c211776d6454c211776c6454c210e76f7354c2128d6f7354c210ef4f7354c211776f6354c211776e6354c211774e6354c211776d6354c211774d6354c211776c6354c210e76f4354c210e76e4354c210e76c4354c210076f7154c21007677154c210076e7154c210076d7154c210076c7154c210056c7154c21007647154c21005647154c211776
  | 17 => 0x5ef704c6211adec704c621005ef75d82210f5ee75d82210076e75d82210f56e75d8221005ed75d82210076d75d82210056d75d82210f5ec75d8221006ef65d8221006ed65d822110dee73d8221005ed73d822110dec73d8221006ef63d8221006ed63d82210076f53d82210076d53d8221007e671d822107fe661d82210076e51d82210076c51d8221005ed76982211adef75982210f5ee75982211af6e75982210f56e7598221005ed75982211af6d75982210056d75982211adec759822110dee7398221005ed73982211adec73982210076f53982210076d5398221196ee6198221067e661982210076e51982210076c51982211aeef6098221007eb6098221006eb6098221005ef75582210f5ee7558221005ed75582210f5ec7558221006ef6558221006ed6558221005ef735822110dee735822110dec7358221006ef6358221006ed63582210076f53582210076d535822104eee615822104fe661582210076e51582210076c5158221007eb60582211aeee60582211adef75182210f5ee7518221005ed75182211adec751822110dee7318221005ed73182211adec73182210076f53182210076d53182211afe6711822102fe661182210076e51182210076c51182211adee70182211aeef60182211afea60182211aeed6018221007e960182212757e76d95211067e76d952101c7e76d95210057d73d95210067e63d95210067c63d95211457c71d95211477721d95211476c21d95211477421d95210067f73d95210067e73d95210067d73d95210047d73d95210067c73d95210067e43d95210067c43d95211467f72d95211467e72d95211467d72d95211467c72d95211467f32d95211467e32d95211467d32d95211467c32d95211467f71d95211067e71d95211467d71d95211467c71d95210067f31d95210067c31d95211467f21d95211467e21d95211467d21d95211467c21d95211466c21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f30d95210067c30d95211467f20d95211467e20d95211467d20d95211467c20d9521014fe76d8d211057c75d8d210067f65d8d210067c65d8d210fede63d8d21004ff75d8d210067f75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d210067c75d8d2101c7c75d8d210c4fe74d8d21004fd74d8d210c4fc74d8d210067f54d8d210fe7f53d8d210fede43d8d2112cff72d8d2112cfd72d8d2112edf32d8d2112edd32d8d2100cfd71d8d210067c51d8d210fedf31d8d2112eec21d8d21024fe70d8d21004fd70d8d210fedc30d8d210057f7558d211057c7558d210067f6558d210067c6558d210fedc6358d2136df77158d21004ff7558d210067f7558d210047f7558d2101cfe7558d21004fd7558d2101cfc7558d210067c7558d2101c7c7558d21004ff745
  | 18 => 0xf6458e21006ed6458e210076f5458e21007cf6358e2110eee6358e2110eec6358e2110fcc6358e2110f6f5358e2100dec7158e21116ee6158e21117e66158e210076c5158e2110fcc3158e21005ef7058e211adec7058e210076f7654e210076e7654e210076d7654e210076c7654e210076f7454e210056f7454e2140f6e7454e210076d7454e2140f6c7454e210076f6454e2140f6e6454e210076d6454e2140f6c6454e2110f6f7354e2110d6f7354e210f74f7354e2110f6f6354e2110f6e6354e2110f6d6354e2110f6c6354e2110f6f4354e2110f6e4354e2110f6c4354e210076f7154e210076e7154e210076d7154e210076c7154e210056c7154e211766e6154e2140f6f4154e2140f6c4154e2110f6f3154e2110f6c3154e210076f7054e210076e7054e210076d7054e210076c7054e2140f6f4054e2140f6c4054e2110f6f3054e2110f6c3054e21005ef7650e21005ee7650e21005ed7650e21005ec7650e21405ef7550e210f5ee7550e213ff6e7550e210f56e7550e21405ed7550e210076d7550e210056d7550e210f5ec7550e2110def7350e21007cf6350e2110fcc6350e2110f6f5350e2110f6d5350e2110fae4350e2110fcc4350e2110f8c4350e21005ef7150e21005ec7150e21166ee6150e213ff6c5150e2110fcc3150e21005ef7050e211adec7050e2110fcf3050e211476f76946210f76e76946210f76d76946210f76c76946210076f73946213f76e73946210076d73946210056d73946213f76c73946210076f63946213f76e63946210076d63946213f76c63946213f76e43946210076d43946213f76c43946210f76e71946210f56e71946210f76671946211466e61946213f76f31946213f76c31946210076f70946210076e70946210076d70946210076c70946213f76f30946213f76c309462100def768c62110dee768c62100ded768c62110dec768c6213edef758c6210076f758c6210056f758c6210f5ee758c6213eded758c6210f5ec758c6213e76c758c6210f56c758c621005ef748c6212e5ee748c621005ed748c6212e5ec748c6213e76f548c6210076d548c62110fce638c621007cd638c62110f6f538c62110f6d538c62110fce438c621007cd438c62110dee718c6210076e518c6213e76c518c62110fcf318c62110fe7318c62110fe4318c6211adee708c621005ed708c62110fcc308c621005ef764c6210e6ef764c6210e4ef764c6213ddef754c6210076f754c6210056f754c6210f5ee754c6213dded754c6210f5ec754c6213d76c754c6210f56c754c621005ef744c6212e5ee744c621005ed744c6212e5ec744c6213d76f544c6210076d544c62110f6f534c62110f6d534c62110def714c6210076e514c6213d76c514c62110fe7314c621007ce314c62110fcc314c62110fe4314c621
  | 19 => 0x4e2117e7e6454e210067d6454e2117e7c6454e2128d7f7354e210f75f7354e2110e7f6354e210167e6354e2110e7d6354e210167c6354e210076f7254e211776e7254e210076d7254e211776c7254e211767d6254e2140f6f4254e211776e4254e211776c4254e2110f6f3254e211776e3254e211776c3254e210057c7154e211767e6154e211776f2154e21177772154e21177742154e211d67e6054e211776f2054e211776c2054e21004ff7650e21004fe7650e21004fd7650e21004fc7650e210f57e7550e210057d7550e21006df6350e21016dc6350e2110f9c4350e21005ef7250e2100dee7250e2100dec7250e2110fcf3250e2110def764ca21016ef764ca21014ef764ca2141def754ca210f5ee754ca2141ded754ca210f5ec754ca21005ef744ca212e5ee744ca21005ed744ca212e5ec744ca21006ef644ca21006ed644ca214176f544ca210076d544ca2100def734ca2100fcf734ca21016ee634ca2110fce634ca21016ce634ca21007cd634ca21016ec634ca2110f6f534ca2110f6d534ca2110fce434ca21007cd434ca21005ef714ca21007e7714ca21007e4714ca2100eee614ca2100fe6614ca214176c514ca21005ef704ca211adec704ca211467f769462101e7e769462101e7d76946211467c76946210057d73946210067f639462114e7e63946210067d639462114e7c63946211476e72946210076d72946213f76f32946211476e32946210076d32946211476c32946212757e71946210f77671946211467e61946211476f21946211477721946211476721946211477421946211c67e60946211476f20946211476c209462100cff768c621014fe768c62100cfd768c6210057f758c6210f57c758c621016de638c621006dd638c62100dee728c621005ed728c62136cff764c6210057f754c6210f57c754c62110def724c62100dee724c62100dec724c6210f57e75d82210057d75d82210f57e75982210057d7598221006fb6098221004ff755822101cfe7558221004fd755822101cfc7558221004ff7358221014fe7358221014fc73582210067f53582210067d535822104eee5258221006ed525822104eee3258221006ed32582210067e51582210067c515822104efa20582211aeec2058221026fa6018221006f96018221005ef75d8e210f5ee75d8e21005ed75d8e210f5ec75d8e212e5ee74d8e21005ed74d8e212e5ec74d8e21006ef64d8e210076f54d8e2110ded73d8e2110eee63d8e2110fce63d8e2110ece63d8e2110eec63d8e2110f6f53d8e2110fce43d8e21005ee71d8e21007e671d8e21005e671d8e2112fe661d8e210076c51d8e211adee70d8e21005ed70d8e2110def7658e21005ef7558e210f5ee7558e21005ed7558e210f5ec7558e21005ef7458e212e5ee7458e212e5ec7458e21006e
  | 20 => 0x4fe7650931004fc76509310067f65509314667c6550931006ef625093100eec6250931005f77150931005f471509312ed7e769453145e7e76945312ec7e76945310057d74945310067f64945312f67e64945310067d64945312f67c649453114d7f739453114d7d739453114e7f63945310067f62945310076f62945310066f62945311467e62945311467c62945310076c62945311466c62945312ed7e719453112776719453114e7f619453114f77319453114f5c319453114f74319453114f5431945311c67c6094531454fe76905310057f75905311257c75905310067f659053144e7c65905310c6be6490531006ef6290531446ec6290531014fe765053143cfd7650531014fc76505310067f65505314367c6550531005df7350531015dc7350531006ef625053142eec62505310075f758c5314275c758c5310075f658c5314275c658c531006df648c531006dd648c5314275f548c5310075d548c531007cf628c531007cc628c531015de718c531017d6718c531016df618c531017d7618c5310075e518c5314275c518c5310067f65d81310067c65d8131006ef62d8131006ec62d8131004ff75d813101cfe75d8131004fd75d813101cfc75d81310c4fe74d8131004fd74d81310c4fc74d81310067f54d81310067d54d81310867f53d81310867d53d813100cfe72d8131004fd72d813100cfc72d81310067e51d81310067c51d8131006fb40d8131006f840d8131086fa30d81311257e75981310057d75981310067f65981310067c6598131115ee7298131005ed7298131006ef6298131006ec6298131006fb60981310057f75581311257c75581310067f65581310067c6558131005bf745813111dbc7458131005ef7258131115ec7258131006ef6258131006ec62581310067f65181310067c651813120edf6318131006ef6218131006ec6218131026fa6018131006f9601813110ede63d8e2138df671d8e21004ff75d8e2101cfe75d8e21004fd75d8e2101cfc75d8e210c4fe74d8e21004fd74d8e210c4fc74d8e210067f54d8e21114fd73d8e2110e7f53d8e2110ede43d8e21006ed72d8e2112eee42d8e2110eef32d8e2112eec32d8e2138cfe71d8e21006f671d8e210067c51d8e21024fe70d8e21004fd70d8e2112eef20d8e21014ff7658e2110edc6358e2100dec7258e2110fcf3258e21004ff7558e2101cfe7558e21004fd7558e2101cfc7558e21004ff7458e210c4fe7458e210c4fc7458e210067f5458e21006df7358e2110e7f5358e2110eef7258e21116ee4258e21116df3258e2110eef3258e21116dd3258e21116ec3258e2100cfc7158e210067c5158e2110edc3158e21004ff7058e21024fc7058e21116ef2058e210067f7654e210067e7654e210067d7654e210067c7654e210057f7454e210067f645
  | 21 => 0xc3159131004ff7059131006fb7059131004fb7059131024fc7059131006f87059131024f870591310067f76551310057e76551310067e76551310047e76551310067d76551310057c76551310067c76551310047c76551313257f74551311273f745513111e7f64551310c67e645513111e7d64551310c67c645513130d7f735513130d7d735513130e7f635513131e7e625513131e7c625513131e6c62551310057c715513130e7f615513130f77315513130f5c315513130f7431551313167c605513100cfe76d89310067f65d89310067c65d8931116ee62d8931004ff75d893101cfe75d8931004fd75d893101cfc75d89310c4fe74d8931004fd74d89310c4fc74d89310067f54d89310067d54d893110e7f53d893110e7d53d8931006ef52d8931116ee52d8931006ed52d8931116ec52d8931006ef42d8931116ee42d8931116ec42d8931116ee32d893110eed32d8931014fd71d89310067c51d8931116ef21d8931024fe70d8931004fd70d8931116ef20d8931116ec20d8931115ee76d893100cee76d8931006ef65d89310076f65d89310066f65d8931006ee65d8931006ed65d8931006ec65d89310076c65d89310066c65d8931006ef64d8931006ee64d8931006ed64d8931006ec64d89310076f54d89310076d54d893110f6f53d893110f6d53d89310076c51d893110fe731d893110fcc31d893110fe431d8931006ef75d8931006ee75d8931006ed75d8931006ec75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d89310066f54d8931006ee54d8931006ed54d89310066d54d8931006ec54d893110eef73d8931116ee73d893110eec73d893110eef53d893110e6f53d893110eee53d893110eed53d893110e6d53d893110eec53d893110eef43d893110eee43d893110eed43d893110eec43d893110eef71d8931116ee71d893110eed71d8931006ef51d8931006ee51d8931006ed51d8931006ec51d89310066c51d8931006ef41d8931006ec41d893110eef31d893110eee31d893110eec31d8931006ef70d8931006ee70d8931006ed70d8931006ec70d8931006ef50d8931006ee50d8931006ed50d8931006ec50d8931006ef40d8931006ec40d893110eef30d893110eee30d893110eed30d893110eec30d89310057f75589311257c75589310067f65589310067c6558931116ec625893146df7715893110dee7618931116ee7618931006ef65189310076f65189310066f6518931006ee6518931006ed6518931006ec65189310076c65189310066c6518931006ef6418931006ee6418931006ed6418931006ec64189310076f54189310076d541893112eef63189310e76f53189310e76d531893136eef61189310076c51189310e7e731189310e7cc31189310e7e43118931004ff7650931
  | 22 => 0x46310c4fe7690631014fd76906310067f659063144e7c6590631015de7390631005dd73906310079d43906310067f65d82310067c65d823113d7e75982310057d75982310067f65982310067c659823112dee7298231005ed7298231006fb60982310057f755823113d7c75582310067f65582310067c6558231004ff75582310067f75582310047f755823101cfe7558231004fd755823101cfc75582310067c755823101c7c7558231004ff74582310c4fe74582310c4fc74582310067f54582310067d54582310567f53582310567d5358231056de4358231006dd4358231004ff725823100cfe725823100cfc72582310067e51582310067c5158231056fa305823120edc30582310067f65182310067c6518231026fa6018231006f960182312ed7e76d95311267e76d953101c7e76d95310057d74d95310067e64d95310067c64d95310067e62d95310067c62d953114d7c71d953114f7731d953114f5c31d953114f7431d95310067f74d95310067e74d95310067d74d95310047d74d95310067c74d953114e7f73d953114c7f73d953114e7e73d953114e7d73d953114c7d73d953114e7c73d953114e7f43d953114e7e43d953114e7d43d953114e7c43d95310067f72d95310067e72d95310067d72d95310067c72d95310067f42d95310067e42d95310067c42d953114e7f32d953114e7e32d953114e7d32d953114e7c32d953114e7f71d95311267e71d953114e7d71d953114e7c71d95310067f41d95310067c41d953114e7f31d953114e7e31d953114e7d31d953114e7c31d95310067f21d95310067c21d95310067f70d95310067e70d95310067d70d95310067c70d95310067f40d95310067c40d953114e7f30d953114e7e30d953114e7d30d953114e7c30d95310067f20d95310067c20d95310c4fe76d91311257c75d91310067f65d91310067c65d913111ebe64d9131004ff75d91310067f75d913101cfe75d9131004fd75d913101cfc75d91310067c75d913101c7c75d913111e7f54d913147cff73d913147cfd73d913147e7f53d913147e7d53d913147ebf43d913147ebd43d913100cfe72d9131004fd72d913100cfc72d9131014fd71d91310067c51d913111ebf41d913147edc31d9131024fe70d9131004fd70d913111ebc40d91310057f75591311257c75591310067f65591310067c655913111ebc6459131005ef7259131115ec7259131475f77159131005fb7059131005f87059131004ff75591310067f75591310047f755913101cfe7559131004fd755913101cfc75591310067c755913101c7c755913143cff7359131006df735913143e7f5359131004ff7259131006ef7259131004ef725913100cfe725913100cfc7259131006ec725913100cec7259131474ff7159131006f771591310067c515913143ed
  | 23 => 0x67c75d923101c7c75d923147e7f53d923100cfe72d9231004fd72d923100cfc72d9231454fe71d9231006f671d92310067c51d9231024fe70d9231004fd70d92310c4ff76592310057f755923113d7c75592310067f65592310067c6559231136bc6459231004ff75592310067f75592310047f755923101cfe7559231004fd755923101cfc75592310067c755923101c7c7559231006bf74592311367f5459231136be5459231006bd545923143e7f535923143e7d535923143ebf435923143ebd4359231004ff725923100cfe725923100cfc7259231014fc71592310067c5159231136bc4159231004ff7059231024fc70592310067f76552310057e76552310067e76552310047e76552310067d76552310057c76552310067c76552310047c76552313257f745523113f3f74552311367f64552310c67e64552311373e64552310c63e64552311367d64552310073d64552310063d64552310c67c645523130d7f735523130d7d735523130e7d635523130f5e435523131e7e625523131e7c62552310057c715523130e7e615523130f5f315523130f77315523130f7431552313167e605523130f5c3055231135df7650e310c6df7650e310c4df7650e314875e7550e310075d7550e310075f6550e314875c6550e31015df7450e310179f7450e310c6de6450e311379e6450e310c69e6450e310079d6450e310c6dc6450e311375f5450e311375d5450e311379f4250e31005df7150e31007d77150e31007d47150e31016de6150e31017d66150e314875c5150e311379c4150e3120ddc7050e311379f4050e310067f65d8a310067c65d8a3112eee62d8a310e5f671d8a3100cff7658a310057f7558a3113d7c7558a310067f6558a310067c6558a3112eec6258a31004ff7558a310067f7558a310047f7558a3101cfe7558a31004fd7558a3101cfc7558a310067c7558a3101c7c7558a31004ff7458a310c4fe7458a310c4fc7458a310067f5458a310067d5458a310fe7f5358a310fe7d5358a310fede4358a31006dd4358a3112eee3258a310feed3258a31014fc7158a310067c5158a3112eec2158a31004ff7058a31024fc7058a31004ff7650a31004fd7650a31004fc7650a310067f6550a314667c6550a310079d4350a3100eec6250a31005f77150a31005f47150a3114e7f76946312ed7e769463101e7e769463101c7e769463101e7d769463114e7c76946310057d74946310067f64946312f67e64946310067d64946312f67c649463114d7f739463114f5e739463114d7d73946310075d73946310055d739463114f5e43946310075d43946311467e62946310067d62946311467c62946312ed7e719463113f76719463114e7e619463114f5f319463114f77319463114f57319463114f7431946311c67e609463114f5c309
  | 24 => 0xe6258a511467c6258a511476c6258a5101d7c7158a511067e6158a51107766158a511476c2158a510057f7058a511c57c7058a510057f764ca510057e764ca510057d764ca510057c764ca510057f744ca512f57e744ca510057d744ca512f57c744ca510067d644ca511457f734ca5114e7d634ca5114f5e434ca510075d434ca511457f724ca511476e424ca510076d424ca5114f6f324ca511475e324ca511475c324ca511476c324ca510057f714ca510057c714ca512767e614ca5115f76614ca511476c214ca510057f704ca511c57c704ca511476f204ca5114d7e73d82510057d73d825114d7c73d82510067f63d82510067d63d82511457e72d82510057d72d82511457c72d82510067f62d82510067d62d825103d7e71d82510077671d825103d7671d82510467e61d82510477661d825105d7d769825114d7e73982510057d73982511c57c73982510067f63982510067d63982511457e72982511c76e72982511456e72982510057d72982511c76d72982510056d72982511c57c72982510067e62982510067c62982511ce7e61982510777661982511c67f60982510077b60982510057f735825114d7e735825114d7c73582510067f63582510067d63582510057f72582511457e72582511457c72582510067f62582510067d625825105e7e615825105f7661582510077b60582511c67e605825114d7e73182510057d73182511c57c73182510067f63182510067d63182511457e72182510057d72182511c57c72182510067e62182510067c62182510457e71182511c77671182510457671182511ce7e611825103f7661182511c57e70182511c67f60182511c77a60182511c67d601825100779601825113e7e76d96310057d74d96310067e64d96310067c64d96310075d73d963114f5e43d96310067e62d96310067c62d96312ed7e71d96310077671d96312ed7671d963114f5f31d963114f7731d963114f7431d963114f5c30d96310067f74d96310067e74d96310067d74d96310047d74d96310067c74d963114e7d73d96310065d73d963114e7f43d963114e7e43d963114e7d43d963114e7c43d96310067f72d96310067e72d96310067d72d96310067c72d96310067f42d96310067e42d96310067c42d963114e7f32d963114e7e32d963114e7d32d963114e7c32d96310067e71d96312ec7e71d96310067671d96310067f41d96310067c41d963114e7f31d963114e7c31d96310067f21d96310067c21d96310067f70d96310067e70d96310067d70d96310067c70d96310067f40d96310067c40d963114e7f30d963114e7c30d96310067f20d96310067c20d963113d7c75d92310067f65d92310067c65d9231136be64d9231455f671d9231004ff75d92310067f75d923101cfe75d9231004fd75d923101cfc75d9231
  | 25 => 0x8532024fe7018532004fd701853238eef2018532024fe76d8132004ff75d813201cfe75d8132004fd75d813201cfc75d81320c4fe74d8132004fd74d81320c4fc74d81320067f54d81320067d54d813200cfd73d81322fe7f53d81322fe7d53d81322fede43d8132006dd43d8132014fd72d8132296ee42d8132006ed42d8132004fe71d8132004fd71d81320067c51d8132296ec21d81322fefa30d8132296fa20d8132006fb60981320057f755813215d7c7558132005bf7458132155bc7458132005f77158132005f4715813215d7e75181320057d7518132026fa6018132006f960181322f57e74d8e510057d74d8e512f57c74d8e510067f64d8e510067e64d8e510067c64d8e5114d7d73d8e5114e7e63d8e5114f5e63d8e5114e7c63d8e511457e72d8e510057d72d8e511457c72d8e510067e62d8e510067c62d8e5148d7e71d8e510077671d8e5148d7671d8e5113e7e61d8e5113f7661d8e511c57e70d8e510057d70d8e5114d7f7658e510057f7458e512f57e7458e512f57c7458e510067f6458e510067e6458e510067d6458e510067c6458e510075f6358e5114e7e6358e5114e7c6358e5114f5c6358e5114e5c6358e510057f7258e511457e7258e511457c7258e510067e6258e510067c6258e5101d7c7158e511267e6158e51127766158e5114f5c3158e510057f7058e511c57c7058e510067f7458e510047f7458e510067e7458e510067d7458e510067c7458e5114e7f4358e5114e7e4358e5114e7c4358e510067f7258e510067e7258e510067d7258e510067c7258e510067f4258e510067e4258e510067c4258e5114e7f3258e5114e7e3258e5114e7c3258e511267e7158e5114e7c7158e5101c7c7158e510067f4158e510067c4158e5114e7f3158e5114e7c3158e5114e5c3158e510067f2158e510067c2158e510067f7058e510067e7058e510067d7058e510067c7058e510067f4058e510067c4058e5114e7f3058e5114e7c3058e510067f2058e510067c2058e510057f7650e510057e7650e510067e7650e510057d7650e510067d7650e510047d7650e510057c7650e5114d7f7350e5114e7d6350e5114f3e4350e5114f5c4350e5114f1c4350e510057f7250e511457e7250e511457c7250e5114f5f3250e510057f7150e510057c7150e512ee7e6150e5116f766150e5114f5c3150e510057f7050e511c57c7050e5114f5f3050e5114d7e73d8a510057d73d8a5114d7c73d8a510067f63d8a510067d63d8a511457d72d8a511467e62d8a511476e62d8a511467c62d8a510ed7e71d8a510077671d8a510ed7671d8a510f67e61d8a510f77661d8a511c57e70d8a510057d70d8a511476f20d8a511457f7658a510057f7358a5114d7e7358a5114d7c7358a510067f6358a510067d6358a510076f6258a511467
  | 26 => 0x156be64d9132004ff75d913201cfe75d9132004fd75d913201cfc75d9132164fd74d91321567f54d913200cff73d913200cfd73d91324c67f53d91324c67d53d91324c6bf43d91324c6bd43d9132014fd72d91324bebf42d9132004fe71d9132004fd71d91320067c51d91324beec21d9132024fe70d9132004fd70d9132156bc40d91324beef20d91320c4ff7659132156bc64591323addf73591324b5ef7259132004ff755913201cfe7559132004fd755913201cfc75591323acff7359132006df735913249e7f5359132164ff7259132006ef7259132004ff7159132004fc71591320067c5159132166ec2159132004ff7059132024fc7059132166ef20591320067f76551320067e76551320067d76551320067c76551324ad7f745513215f3f74551321567f64551320c67e64551321567d64551320c67c645513230d7f735513230d7d735513231e7f635513230f5e435513231e7f625513231f6e425513230f6f325513231f5e325513231f5c325513231f6c32551320057c715513231f6c21551323167c605513231f6f205513200ddc7650d320c6dc7650d3200cdc7650d324a75e7550d320075d7550d32015df7450d320179f7450d320079f6450d320c6de6450d320c6dc6450d321579c6450d320c69c6450d321575f5450d321575d5450d32007cf7250d3200dde7250d3200ddc7250d32167cc7250d32016df6250d32017cf6250d321679f4250d32167ce4250d321679d4250d324a75c5150d321579c4150d32167cc2150d321579f4050d32167cf2050d320c6ec7650932014ec7650932007cf7350932015ee7350932015ec735093249fcc735093200eef635093200fcf635093249f6f535093249f6d535093249fce4350932157cd43509320078d43509324976c515093215d7e75d85320057d75d85320077451d8532004ff75d853201cfe75d85320067e75d853201c7e75d8532004fd75d85320067d75d85320047d75d853201cfc75d85320c4fe74d8532004fd74d85320c4fc74d85320067f54d85320067d54d853200cfd73d853246e7f53d853246e7d53d8532014fd72d853246eed72d8532006f751d85320067c51d8532006f451d85320067451d853246ef631d853236ef621d853236eec21d8532024fe70d8532004fd70d8532006f761985320057f755853215d7c7558532006f56118532007745118532004ff751853201cfe7518532004fd751853201cfc75185320c4fe7418532004fd74185320c4fc74185320067f54185320067d541853200cfd73185320e67f53185320e67d53185320e6de4318532006dd43185320e6ef7218532014fd721853238eee4218532006ed42185320e6ef321853238eec3218532006f751185320067c5118532006f451185320067451185320e6f5311853238ef5211853238eec211
  | 27 => 0xf735954330c7f73595430065f735954330e7e435954330e7d435954330e7c43595430067f72595430067e72595430067d72595430067c725954330e7f325954330e7e325954330e7c32595430067f71595430067e71595430067d71595430067c71595430047c715954330e7f315954330e7c31595430067f21595430067c21595430067f70595430067e70595430067d70595430067c705954330e7f305954330e7c30595430067f20595430067c205954300cfe76d894316d7e75d89430057d75d89430067e65d89430067d65d89434b79c43d8943166ee62d8943004ff75d894301cfe75d89430067e75d894301c7e75d8943004fd75d89430067d75d89430047d75d894301cfc75d89430c4fd73d89434b67f53d89434b67d53d8943166ee32d8943004fe71d8943004fd71d89430067c51d8943166ec21d8943024fe70d8943004fd70d89430067e65589430067d655894349f9c4358943166ec625894316d7e75d85430057d75d85430067e65d85430067d65d85434779c43d8543165ee72d8543005ed72d8543004ff75d854301cfe75d85430067e75d854301c7e75d8543004fd75d85430067d75d85430047d75d854301cfc75d85430c4fd73d85434d6dd73d85434767f53d85434767d53d854300cfe72d8543006ee72d854300cee72d8543004fd72d8543006ed72d8543004ed72d854300cfc72d85430067c51d8543476f631d8543476dc31d8543024fe70d8543004fd70d854316d7c75985430067e65985430067d659854347f9c4398543006f761985430057f755854316d7c75585430067e65585430067d655854343f9c4358543005ef7258543165ec7258543005fb7058543005f8705854316d7e75185430057d75185430067e65185430067d65185434579c4318543006f56118543004ff751854301cfe75185430067e751854301c7e7518543004fd75185430067d75185430047d751854301cfc75185430c4fd73185434567f53185434567d531854300cfe7218543004fd721854300cfc72185430067c5118543456f53118543024fe7018543004fd7018543024fe76d814316d7e75d81430057d75d81430067e65d81430067d65d814332f9c43d8143004ff75d814301cfe75d81430067e75d814301c7e75d8143004fd75d81430067d75d81430047d75d814301cfc75d81430c4fd73d814332e7f53d814332e7d53d814300cfe72d8143004fd72d814300cfc72d8143004fe71d8143004fd71d81430067c51d814332efa30d81430067e65981430067d65981433379c4398143006fb60981430067e65581430067d65581432c79c435814316d7e75181430057d75181430067e65181430067d65181434cf9c4318143165ee7218143005ed7218143005f67118143005f57118143026fa6018143006f960181430c4fe76d9132
  | 28 => 0x85530067e62185530067d62185530067c621855314d7e71185530067f61185530077661185530067d61185530077561185532ef7631185532ef7531185530077721185530077421185531d57e70185530057d70185530067f74185530067e74185530067d74185530047d74185530067c74185532ee7f73185532ee7d731855301c7d73185532ee7f43185532ee7e43185532ee7d43185532ee7c43185530067f72185530067e72185530067d72185530067c72185530067f42185530067e42185530067c42185532ee7f32185532ee7e32185532ee7d32185532ee7c32185530067f41185530067c41185532ee7f31185532ee7d31185532ee7531185532ee7c31185530067f21185530067721185530067c21185530067421185530067f70185530067e70185530067d70185530067c70185530067f40185530067c40185532ee7f30185532ee7e30185532ee7d30185532ee7c30185530067f20185530067c201855317d7e74d81530057d74d815317d7c74d81530067f64d81530067d64d815301d7f73d815301d7d73d81534f67f63d815350f5f63d81531757e72d81530057d72d81531757c72d81530067f62d81530067d62d81530057e71d81530057d71d81530067e61d81530067c61d81534f77a30d81534f77930d81534fd7d769815317d7e74981530057d74981531d57c74981530067f64981530067d64981535057d73981531d75d73981530bd5d73981531de7f63981530df5f63981531757e72981530057d72981531d57c72981530067e62981530067c62981530057e71981530057d71981530067e61981530067c61981531d57e70981531d67f60981530077b60981530057f745815317d7e745815317d7c74581530067f64581530067d64581534fd7f73581530075f73581530dd5f73581534fe7f63581530bf5f63581530057f72581531757e72581531757c72581530067f62581530067d62581530057f71581530057c71581530067e61581530067c61581530077b60581531d67e60581534f57e761815317d7e74181530057d74181531d57c74181530067f64181530067d641815301d7f73181530157e731815301d7d73181530157c73181531de7f63181534ef5f63181531757e72181531d76e72181531756e72181530057d72181531d76d72181530056d72181531d57c72181530067e62181530067c62181530057e71181530057d71181530067e61181530067c61181531d57e70181531d67f60181531d77a60181531d67d60181530077960181531d77a30181534e77930181533257f765954316e7f765954301c7f765954330d7f73595430075f73595434dd5f735954330f3e435954330f5c435954330f1c43595430067e62595430067c625954330f5f32595430057c715954330f5c315954330f5f305954330e7
  | 29 => 0x3267d31d91533267c31d91530067f21d91530067c21d91530067f70d91530067e70d91530067d70d91530067c70d915317e7f40d915317e7c40d91533267f30d91533267e30d91533267d30d91533267c30d91530067f20d91530067c20d915354d7f76591533257f74591530073f645915317e7e645915317e7c645915317f3c645915330d7f73591530075f73591535455f735915330e7f635915316f5f63591530057f72591531757e72591531757c72591530067e62591530067c62591530057f71591530057c71591530057f70591531d57c70591531757e76d895317d7e74d89530057d74d895317d7c74d89530067f64d89530067d64d895301d7f73d89530157e73d895301d7d73d89530157c73d89535367f63d895353f5f63d89531757d72d89531767e62d89531776e62d89531767c62d89531776e32d89535376d32d89530057e71d89530057d71d89531776c21d89531d57e70d89530057d70d89531757f76589530057f745895317d7e745895317d7c74589530067f64589530067d64589535257f73589530075f735895352d5f73589535267f635895315f5f63589531757f72589530076f62589531767e62589531767c62589531776c62589530057f71589530077771589530057771589530057c71589530077471589530057471589531776c21589530057f70589531d57c70589531776f205895317d7e74d85530057d74d855317d7c74d85530067f64d85530067d64d855301d7f73d855301d7d73d85535167f63d855345f5f63d85531757e72d85530076e72d85531756e72d85530057d72d85530076d72d85530056d72d85531757c72d85535177631d85535177531d85530077721d85530077421d85531d57e70d85530057d70d855351d7d769855317d7e74985530057d749855317d7c74985530067f64985530067e64985530067d64985530067c649855314d7d73985530075d73985531255d739855314e7f639855313f5f63985531757e72985530057d72985531757c72985530067f62985530067e62985530067d62985530067c62985532ed7e71985530067f61985530077761985531d57e70985530057d70985530057f745855317d7e745855317d7c74585530067f64585530067d645855351d7f73585530075f735855313d5f735855351e7f63585531275f63585530057f72585530076f72585530056f72585531757e72585531757c72585530076c72585531756c72585530077761585530067e61585530057f70585531d57c70585535157e761855317d7e74185530057d741855317d7c74185530067f64185530067e64185530067d64185530067c641855301d7f73185530157e731855301d7d73185530157c73185532ee7f631855348f5f63185531757e72185530057d72185531757c72185530067f621
  | 30 => 0x3000000000e004000800401000e0030010004015008000801000100a001000604900000d8000001004800000c005000000002c001002000400e00d000801c020000000001003a007002001801e008003801c012000022002000c0000098020030008005002800000e014000800e002000001401e0500058010038004011800400000700000240020060080064004001009000000a003000000006600d000006c00c0010148040000004001001412200100c805c000000000002400a00000300c400000000380740000070008010038028000000400a00b00c000c02600100000480000000008038030002011802002c02100280100000090030004000003006800006a00e010009c0020090058008014000000800001c000002800400000b006004400802a000002800000f003000401a03c00f00200260190158000006004003005c00000000080d801c022000800c00200300000500020160000040002047001000c00a0700078018008013001000c000000002809001400000f800000200000a0074000000002000000400100000100020000028000000000000000004001c0038004002000004801001a002000000001e018000002c00e004000001000c0050048048002005002800c01a0040140020014004000000800002600000000080010038154000032000801c00a02500180080020070030138018000002000000e003002005000a003016000005e00500500280440060048000000004001013001200a001000c00e00d00200f0000000005807c00800000080000000010198018002008004800001205b001001000000f001803800c0000008000002002003001000000d000807c00200c002002c00002a0008000010007000000000000400000180180000030068038002001800c002008000002400000e0070070000004001001800e009014009c080002001000800c000010801c03a011005001800800b0000018000003000814c01a00055d7e76d915330d7d74d915317e7e64d915317f3e64d915317e3e64d915317e7c64d915301d7f73d91530157e73d915301d7d73d91530157c73d91533267f63d91535575f63d91533273f43d91533273d43d91531757e72d91530057d72d91531757c72d91530067e62d91530067c62d91530057e71d91530057d71d91531d57e70d91530057d70d915330c7d74d91533267f73d91533267d73d915301c7d73d91533267f43d91533263f43d91533267e43d91533267c43d91530067f72d91530067e72d91530067d72d91530067c72d915317e7f42d915317e7e42d915317e7c42d91533267f32d91533267e32d91533267d32d91533267c32d91530067f71d91530067e71d91530047e71d91530067d71d91530067c71d915317e7f41d915317e7c41d91533267f31d91533267e31d9153
  | 31 => 0x68070000018005804c002005000800009e0000048000000033000002800e001011806c0000300010070010004004002804602d0090060066008008001401c027001000c01400400f800c000000002802800c0050028010000008023000c002044000000000a00100f0000008005000802802400a00000000000000000048004003005001800400400e8040008007000003c04c000001002c02c001009800000a000009801c0020030018048012006000012c04c0010000020002000002804000000a00180200480020038000010003009800000000e0018000022009000001000e0030050020010002000802801600500b80200100000070000030000001800800200800000000020020038094000000000000000800c00a80040460130010050000003000808800c01a0048000010004007802801600a0018000006000000001c00e001000002c000000000000000000000180300060180008010002002004801000800600580340000010008010004001000800001800000000780060040038024000014006000000a00b00180080540000018004012003000800000e039000800001e04501e007002c0010008008002000001807000401d0048028000000005801400000a00080380060010018000002001000000c01200200b800000402f000800000e000000000401e024002010c01e000010000000201200080000020060010208002006001005001e00000f000000200a002801c04400100680d4028011001807c002006017801000600100600280420170000070058000000001800601900200540020040020004004001001000001e002003008000400000080500120030050008000000003002000e0030088008002010001002800c014000000800000a0010014000000022800000000000e000c00800000080bc000002000000c028000000001800600100f802c014007007803000200100480000000070150010010001000002000c01c01f001000000200f00c800000a002800001a01d000000c018008004000400000400100fc000000002000001e00304201b001203000980a000c007004800800e01501d800c000000003000000a0400008054012002000003800c008002000000c005002800c00200000a000800000102d801004c00100000ec036001000001401400b007002800a000002800c002022007802000000000180180060020070048002001000001800000500080040040070000014004001004000802a002005001c006021002801400e0010040078000003004806c00002800b000c0ae004013801c002008004000001401400600000020090080008000022001000002a0120040008002001023000000002e001003809e01400e00040020040158044008000001001000c00800300ac00000000000000000050050000
  | 32 => 0x200b002000001c00e01000b401c00100081fc01200300300040000010060090002003000007c000017000000000000c0000000012023002801005000c004001801a000000000003a002002801c02c00c00d000c00c0040070004018000000000400200500501300040050020008000005001804000e00000a800000802e007003000400000100500040080038000002001003000000c004000802400201200100040000020040044002006009801000401c003007800200a00a809003800100480100000040000064004000000000400400500180080040010008000018000009006000001c009001c0000640008038016001006000400a01a00280040180000000060006001000000c00c038001000c000008002000000000a0010064002005010000405c00f002000400e03e000000004c00c001000c00001a0000008002018000000000a0110030098010006000804800600500601e80900020040018004001002010000c0060000000002009000000403a05a014000400c008000001800800a00d001402a019003800401000000101c400a008000801800200400000080600180048008008000000803c00e000002801c0000150058000000003000000800000d00a000000e00000880140080010040040016002008002400000a0038004002001000005c00c00000180080240000018008004001006000800e006000001001a00d001000001a0040000000000000024004000c003001800000400a000004c0020000008030000008000001000a0000000068008003002000c0160770008004030000007001801a01a000804c00e00a00f8054034001003000c030000033000c020018001803800400200000000120020030030028002000003001e009005000c010006003000001e00701d00ac02c026002000c0b80000000028000042000001001c0030008014010022002000804400800080040340020008038004006002800c00400000100a002000000e0014088003000801801800702400080180170008028000007000000000202a000000800e0010000000000008000001400600001a8000018002000000400000000a000403a028000800800200f00480000000010000040000008000000800e0000020000172005000005400004a0028050036014000802800600b006800c0000080020014000004000000401c00a0020000032011001001c0000180000008036006008000000e000000003000001a004007400000000400080520010048000016000000002000200101e00b80060010010004006041001001801600d0038038024008003800001a00b003803008401f007001402c000000002800000800180000220000148064002000002007c004003001800000001000500c4006007005001400000500000100000040000004034002
  | 33 => 0xe404088388d7820095045e1895412c000081612304e61b3a40a800057a40006fa0e405d4c454014d3f8100161c43a91eaa0e87266d9094258618bc62844ef19d9f1a0a184985e2109a05695428a519f752b04345d0186e6e6c87489622fc0e90af245c94509a22704629a7a087d09794ae904c59185968680e209678efc87198e85ff0b225550000000178a8da113c920856402a883d5380eb488b8aa348700fe1fb19ce0000ab05295c589b90ca81fc1bbe2ef06487ba57d411297fa979825872d0fd4788012a89692cf93058c43db0a7f4da006e3ea87426555ea372121a643ea5533c5d31036c23cb0000458312829b0001ee60001aab0da0efa2ea4ce729c80002de19e844ba4665ec1ee2105800071ba4f245d275428c00006b897d287302b0114855d857126446a922863e9b5c05b8e946980e153cb17aea079b84182a0445a6a43a381e22c5f5922a11687661b9086474510370001576000158a03a82cc00011947281dfe000171a52282085eca7fe70d91460001ac2959c89875be4bb16e00000329e4c33184ce23e037820284049f10cbc8cc1a507611fc62048db7049e69a664000000785a48ba0bc89ada7340f90dd85ab80006ea114823511c826d678c7ab0eb05e919188e88c606ca8000191000013b8c3d0000aaa376800095653d42658f4c616800000000001e394c0271262230108765150ec038b80001baccb68efc07445e800000000003b7a0b472e83b60000000000000a00a0048008000000001800400400000200100060040078004010001000000002c00000000000000170138004002005003011c004000000000800c00d00200580a6001000800802a004001000c002006001800803e0050008000004000000002c004001001001c00000200f000800201b001002000001f00000b40000330000030004000000009401401c001005c12400100380340020000000004000012001800003c0090028000002004001000001c00c00000d8010000000003002e006003800000a013000000c004010000000c00c00000a800401002100100a4018003001005001c00700480380000040000000012001001001800800a001000400800100d002408c007001800001e006009000c00a00200b002000e001001000c0000040008000000001000807801a002000000000000a0000078008000001001c00600200080000040010000000000000000008000e001015800400e0020010024008000000003403e00c001000c0000bf00000000160040050068008000000000c002000002002401000400000180000150020014034001000004c0d40030000010004014005009401201800180180100000218080008001002800c01400500080000020000000028002002004005c0060000000000026000010003400400b00080c0000002000001
  | 34 => 0x5d458f079d6d08acd7321b562ee267c0c34bc246b8d802e1202e0eb0e2636d047453e9b2058b814f380104a26502d46d9948c7d3100c0e5a804440938882b081e44d804f185137e070a76c00000005d4174736300005639428a18800091e243c5cd897480980002021e808cacaf00000dd00001d3a09b8ff00001ef60000000420197c00000008df8000000221229005dc1290bdc39b40004f980008bb8bab97b0d0039503239b2062083917a6988185401a243e947a4f78ed27969cda05468a8ab219ca2306b417261461f081ac1ed43af80d61ce84e482a64ac5c0841e86f19242c289280f007fc3f48a246391232228a1ca25a0e503c4633d3458b9c022da7a45116f200015a88691f3400002ce9da98ba4828158471026209957007eb12722fd9e0490d800021bc93632814dd28c9ac698980007ee21d41fb56120000764462041c0f31e266ff9fba76c03da0684c0a11e93c0181213663c00000001fa84cf22be154a02a0001bda1c9000090c9c9e8c9008960794f6095dce28921d648e564b66fb230225f4eae49118201869fe60da4aba5d18ee008d128e838e8587620c49a01a6080a9123356e8cdc7ab962c41fa3b2582e45a091164700485f64fcd8690001e3476a60a673d9ab47ae9298406195000000001d291f8992a638933800a185a40000024657a8841519e84de129ddcc03113fa2da85ce9c00b52724072a64809646bd90de77204480000598000040e369000000000000000000000028e5e480000de4d4c0ba4c888281cb600000003348000884126c1fe9e065f948b900016860000000068800000000002a0ced0910189836b0000763a2e600007a00e3192a9dd96a88c7800075e1f88956926e00021267d9a3e75cf0000a009e24000232f000082e1360a5470300000000baa14ea0e600000009b29a0413d8000000000010c06de106e58a7b215c4254000004ce3d6000123a482187c2f189df0000eac97e02f06af9bf33a761332e1a3b61d8d9b28b016fd8b611385f788be8119cbe38e161b57bc87156621d639d636e5d710567790c6693b1eb83ea4b265c3931e4ed89ee7ce1515608911a42a8dfc93e1338108c6f00dd17302f30cc47c29a38614164537c06e235903720f798a401a88ef6f78fc82320d4a32e066c752866672493720a9e82a744804a2fe965467f206233e93601e207a57b596f890e1ae80e1054c15190083e69a98242864a67502991e325e804dc055661130a0001d47367049c74f86c61430000508867e06c0cfc00a87a108425510371fa00001fee000023294980008f625a60d1e2a295c20e02d1834500021aa637a4a766b00005241f683adc2e29b68a74284800027e0e0500015c89fe893a0000ed287480005b29a523374000400d4529e2a82092c1b6e9b000621c1a1448f45f8c13b5fd01204bb18
  | 35 => 0x78b08727989bd40c8887c657119019927222ad89a5923000c9b791755f6957c9cc88226f590230000000a129b7471900ed9e4277097583ea8fb12d0000000082ea1818400f288f8800012e80000000f4200006d872c157483d80004559f306dda5862489ab000000009430057516a12466924e6681e4ae8c504e81fd229280a272447357c4716a5c88a6083e2c4a3265ed8f3c3fd12f03b7436248586b6275977169e1b1c1af960a27c84b16ab0cca0d38c3737bc4f208d916c47c97bb1da597e44d218540d8fed51711e01f5a14a5fb1ce480686827208da281c885c5cccddc9151db69aca21c758083b78a04ae2371b88963274271a9aee7728fa83c78bec2fb661829288104bc817092716a22160934033a46976099602bd01aa9400ac438385a69e09d4e3cf98b29471b9238ad43a11c08348dd008525a532250f1ca213998008048d8a888a2ea8b91a3a3041c423e988c446310b897824222ab09128f408e466291b6a18136427d1f067409a6209d992e128e39e1dd9b067bc66364e380fc484a15d66882ba0ba0ac20db800029686e08d08bf85461af80b196008c59ee72200a2e1aea0526889c664fa800000000007c09c463d5a358000011c302044258e553c4ee845670e000044c000049d1e2a03e832680c000095ad03b4b792ac94856ea790873c25b23fc5581f94682864c384a13026e0f974059538714998283c01c8545c81590d4d3c36f99660e8df844cb07f889304df0000be05590c3968b00000ab87d02329a203db800031709b90cd2564841c17c06490d00c7c0e0745800000021ac4d780005178eb927d93821e7978419b88112fb8b1c5cd06680ac642476e8134000249e15a0000260230600018ae00020a7569838955b11b46930df885983332bd800029e1b0e3089e3e953daf20a8e67086955d6000106b70c8000000000008a07549fda2424aa8e822d0013079917940a6127556f12be1d2441996f25a079f0aa02c00a9c24f883c46b10964a18000305c26a6d180000942606000000083680000000ea20f08000089a0484ab9c102cc800007a00000000cdf97f8d3a000000000002f613f9fec6c48c38538400000000006c61bbc6eadffe001a738000000068200001c58bac06d80005cc4000000000010860ee000000046e000000000007cd920c0000d946a080007bc24c66bc0eea1090ee258ce032000257e3b21cae5f8264271500de042906600027ea2918cfea0b000086521d8000000031d9db43e7a034570d5e7269104371017aa9fe0c9c66ac0660f38e4a1938c0c33080d01bc82fe7d1a4aa000010140b96ee0dd53bc1f1045e8ab00000e14151000070a00007d949f24ea38aa178923800004c9d6b0001daa313c00030a1a121041e3a000058b95b46da00000005dc8d31000256869792ee8f824e83fed94c9328
  | 36 => 0xdfd81195eee7751a8e4e900a698c0a00448203a0002002000059c00020a590a000023684fa12525cc1c0815052a9268500118e0000ba88971bc017a0000067095c6f2a5de0d20000351522c66d1a483f108241bd800000000000001877662000097d222422b807017880008951aa2846917d00011a4963952e08618aa879188c000000018d90280000698059081a000000089d000099d90401e40000000000025380002d3a5741ce22f885f23cd0a787400ad0000000073e9548e7c49191e2a0285b222a08bb3708ae841ea214669a68c74a9266798029c0280d0e000071d55f8000743800092f8c548f38dbc0000b9a26d0000342097652983aa0948d2a9e9972f7b7007200000006e08000275c154000193c347000057004642039f54999232011ba4d88e71d0430d0d8244b03ad1a29ba59c3991c3a803ca0002399130a35a75b224a266800044022ec7430ee605a11928619c1e98a00007d580005f9d7236f200001111a2e4e780007df40008aa86ae8e0054d56780206e3e4c8000031e00027ba00b998c0000ac642b81364ad00002d51fd42561fdc81293e1267870d1a3c000430952c8cc9c200000ae63dd9828668ce1856fa85e8d10608826047e00000002498606000031c3eca4fb00000000000d567baa4bf60a8efe00013d60000e1007e179b3a28332860d25e30247e800001ee00000000000c128d8225256b964c0001b9a2b3d74992d07a364500000f110c02ec17f65420520000000000025ba0001da40144d4e4ed073608e00007cba7842c5800000014c693f94460f8408d0000ffa5c88fa0a04a3c418d0ef600000000001a9a000000000019da0000000603000032e8ac340988ac444cc1a1ec0ff800002fa74724da134800023022ca00002c2000000084491ba3ed80009db80003f389a34c227301cc17581cc9ad4794245036e264600004b662e16d8633a30c3f24000000160875b8000000000000000007e6496b0f940a2885a4de8808e1316a97ca867122631e9b4a31f16be8c3a5ee0d2a76834095566ed936634d43f619ed30d3200bbe4f38f265cf8b3c278a4ee6d3168a4151ede6a1a6dc64217f076c47d89ab924a99d23826334166285922493918e26669cda708a4f0695990681d164e9c78e454b196a43a49f8620019988f689e3294a3c009f982c34499ea52ce78600d051c2139a0b5e6633e7db9bac86c8c112621b4e85e826802c1ae031781a08af08560c310fc53525284e511ca2fd25d809392da56416625e3a14c8c49bf02850a58230a1c85ad012f77f15de5c79348889824c14b06ec8778f507a50d58698c9701e523555a222d28be91c63a912220c68b152ff83fe235874c57280ef10284e12149e4006625da31fa45c5750ab80e625020ada2da8649a889f28c93568159c1c2c8821c79ad82348c3a6fc4036
  | 37 => 0x64e08e800005fc0fe000061305f200012361bd000013ac0000001458519879f6e7d8a8801128d00e800013211e47e48000000234e406a32e6aa0ac06bf8478a140000080d3a69a980007c98dc61f50000000037c53dd71c1e98e1c000000014496c600024d40000f4888e8bce16e802682fda4e2a3cf5c000000000022de21c1b78944000043a077435480006cb80005b98c8466ba427000000001622b600000002f50f105a706f943390940000aea0001e545446838000000082d80f176613349451a363f6855c05d008c97902ac787240420e9ca488a4813a15a68085f8fbe305a35c5aa88e28109d3f0b203462f610842b38956a098c964db8fea69625382facecc62500f648105da2e9db9e0fad9461969fca5038d2215c8da65921dea5bd8a9637e955e4ba14be314a78e6f19d4080011c0096a66a9f59fe4854094c391165696a1cd2751211c6969fa161d0b562f696141b51cd400010da3460d100f8dc8000015b24b4626e50320767f0251a700800078019346e51dd61f00000000018b00016780000ec68231c3e1514b7400011b0000247e0391eb08e188bc000000026cc3fc837087b0001e740000000000000032c011e3580588361053e2f8822c2aa60ce25ee5129a626d60000bf223383c92a000000bfc000918a2f023c83566c686c00001392869c0000000000256c00000013123e90e8e122586aa151b803d48b28268845000009de7588000194a81823b8a8121f95141bec7623a0617d7df89f00001e0c000072265c97804921df677686ac11d85f44b4a720508274e5b687785e5c0006778cb40810aa299c80009cb8e905d50000000000015d9dfa74a50423c8821795d8000107cf8000023f62df47f6420502400000000fd0d3460b800011f033658a968e901941a8d895ec364000000003e20000e4e00010bc0000a640000fb43cd8000000000000000007d81830118c0005519f479af80000000b0e766800000000005da99480000c565609dc29200140000162200011b28331a9e00005fa9038000000254a9609c0000002ea8311486431a3885da06fa98d000075500002821a1e4ea14ca8f9a4d2021c76582f9a9059c9e6e819976c5b5229e32a8cac54aa68e3f58000a0680005c3253642981a613b18be25764ba000076c209dd583fd8b60566988200013327a2971836218146b59390057a2ce2988e1e416208087884b45a808ba506039e0d6c0009ed10e400012df67e16e24af10f28a0a2ae1b10a762754000a12205a8d004a01aa95cb298048b20183c66aba3765408152404805600027f0592a53e02a1ba18228ef414d000053c81bc098071885394123619a034035a1878e0b8a83f8e9300021ce9310cc3041098428ee4a278d97217e1c77c747d26a97101ed6869fde027852679b06fc86283bd92220244e021fa5d5
  | 38 => 0x9aa9ce9c4a000057c7ec1ac025990c47a19de034e18ea5f7debc8ce63c61dc21987841ff846591b587703521030e8694b2300000080c51d14e77d25c5c0650574409ccce11a9f8079e14117c4187600001ba01347580000187113c90e04595cc9968acb5db82a21a9074800000000fb5f1852d40002df058e0f9c230000104b47d80007268cb256d808407c228c6d41adc67c8e9744727620668b7a5d7800015ed5c70000000221869c2a4c0000000e6b14ca7141c85d063991a64000000000000003af0dcc000000017b0d1e4f29f9a7a940002380a4e01804dc0000f3460d03051520381835938b0000000697028952a109075c18529e7a16884891769f18000764013e85b8000129800000000000000c5a536d15e99e800400002da49e1d1051b8f3000026e800018260000000382000097080004111acc570a118000000000000000bb800006026b88a000006a5258016193fe7659038000086c39fc0000f3c6c252b93242140e9e58d85e620e210862bc00035d27d436e90f4950542a493000049549106fd22b408657629130f0f000068e56300008cb0e0a65d8d4827080003378d1a7da92904fd974ca0d978c3a007ae1a31e3c527008e34926525138000631dd286b908414a29c2800010068b80bfc2cf8016000000000015484fb8340a0f87c64079c2a7aa172c06d225e7dc19210000a564f8831210f80009c4a74603ac3141c4a19e000144a0001da0000105a7c700003cb916e000284024681d000019f06d8a68671f1fbc35c86a294924a40001f6b0e4987a73600002899a9633b8bb60a98fbc0df800000006587d540002f0000040c1c0a4b889c84f607c220b4f14937002541d80000001a6500003618a040000000a282e38052288c4f04e300006411f5c52c8d50000000093d91be75d00005ed00000001f2200000005e68b38000086b000000048b80003a4455076b8cda467616186400008220000000194a00015e68e819aa18ea54656c26b00000ec426b8a6b79680006e31c4822a83f006c866017f91cc6d209dd54d15c926494e621ba56e7fd9bb0913a77e441167e275028a07be55647cdd6a000000000010f843303ba7ea666c1d8479234ba03684e80000000000000124e83799d850700d200013eca190000343000002913f09961a6c0b4879c1ec800095b23dc777a60041900000959e3044900002ee9756000000059b9184062168497893aa83003b00001d6670b01be7938f380139f442b31c7a12b05ee04225ea3120d760001f4b39b27d08588414171a0e791909814aa084c3ff9cb2000000018089c67ff069248780004ee17747bb62b82d219a189118f48100000523835e5df12a671f800094fc0d4323a3379bfa42e42b218e39c928891e8a1041f61da0619fcc753206a298c43c2f10c0715b11e814286ea000000
  | 39 => 0xf88fd1002786a1878e595ce5a0245e16f1d2c43b14ee5ad9300000193e46a00005e8241a000054b156a474324490283d1c3c95305a0854869444312182739f6c9a595f200010b409740009848a448d1921001681e20be0f2376f2842820939a589848d89427740d988f300021be61a06004be1cfe7398b2e5c49b264420a3c3eb004173188f03dd00f894be20a10e56106711a160ec84e061396829020d9a55b80008c70d4234a15880000edb4b280004e340000171a2667900006441bae1ee00b20000000808896706280003d81f7c97d89da39f916a18980008f30c4c29082062f5a20488d1f6d9ae99649bf000053a800002d00008d742720000bb213cda147cf0b2000027e66eca3358414646000179627603a21d700007f4800074887ca6d600009d4000000010f00001b022b709b08319da829c075a1eaa38e59491328a40000000263e000140a9eb8261031e64e04b87204ec138a627c82842e88b27d4a57255e8e6e0e023509072569020c000826800051026f083ad87900000005a40000009c0003a983182c2150b0040d0a5b3229c000045c01028528cd91d939c61fe0bf0c468f29c8c381226a5aea2085cc875040f05826da08a5490a05e1374ce496d8b14000086d99e237c5ee8ce6316232a76c86c85d38a2200025310002393156547876e0c9e480809a1d5e65c60c8e141231df86c89faa0ef9b1e51d8cf961b11a028825ac45e0ad20399795942884448003a05980fe81ba411a2b58e7a1180d66755514c557134607d9dd21e1189360f1ee40f755dc928000013500009d61448000204e5de1f04000138409990703208e2c37b897a23314817bd172d96685f0a110f1547b169e2461a09891a0d85dc00009030d994cc0f1357f000064957771da800017aa5ae4178eb659618025541602965043a5f427563d9a284000192c41049ec30f14026c508367a7c172283a38c4329cfc4348ae0618147294c01a53b8dc8e5f84ded3c207086d004873b2981c212262c0000000000000071323ae9670fba000116222e058a9cf96d6203c360087975528fa7b063d8ad01a183b43d79f76454800013c5afc60615ed358821a00012cc08804a22e58000825908805200003721a2844f973a2d3160c36a8b02222800021088d84f199dc7571d50767221a7618b941b380003249f142e896300cbdfea3f810042ebdd188e054a45b1020518b0b4249407d265e07595e4dc14a088000252c00067d11d06a9265e1f90000674800000000000000088587c61e89e009c0d921209538f9100000f00ea1d3271400005795270000000000007dc66a4000000079b5d0d0a890d10b22b68000973a702801914216797664df09ac3b70c723dc17140001e2e865a3e420a80001411a0545a22ba74b8e849c986a600000001c6800045740cc62787f36ae9fa200
  | 40 => 0x37800019f1d76000249a57f800000000000001ffb000000012a400080f149a9de15360001b9879d90e046980002bb800099800005378eb2297800047082ec0b42420000003091c80007bcc00051595622525fc400022bd82a93028d20cd6675800066481fe18c8b30544e0ec8e980000000db20000eb562681000c38e8825e18dc322d81a0000270000156a9fd00004de0c6c84a06a800020b20001c4e30b825e2680000000236a65aa5d400000005ac0000918000000000e273a8000000032c65b00001a55c9c1119dee12f8000000000075e8c20522087a000201c7b6966a2e317913c011587649a5478380007aca23850dc9861dc800046e400000020b8699a132000102058a000062d27a20000000341056e8b200003cc800000014f800000003bb800028e80000e20ac84d111fc62b00000f80488183a0c700000000001a6a3df00005c584ad326400086b9c26241a6e65d05a2400002a9498130c6f0822f024132e3eb86700001d30000255e3228bb44a4800076780000000bae26f2141957000000020b00000c515358ca63579f5a4b1028c5e780006f997dd5b38a5c22215da48e019e8eaa6ce5de599e0000b706670f7e345018402496dc3f3149e33c234c64a27d8218820c000248a2e4134c57617b90000c0e00016375d2a22057825a49dea4761c39be23b5800000005241bb97ce8a984e20001a7e51e67fc51102be7359d5a53b5a0c6288b829a101903135d5653113d09c184b21e603b34ec906c35c17828d7994e305475e469481c01120f88250a111740c6a07f281426f616c96e22367f89a683f423560c087964ac8ae25fa9ec029f15aa75f90a003b0a8c33d1ca81c317526a01bea57aa3ac5b09b9057a191a1f34b5c0108abe1e19ac89890fe760423ea35040006fb81a8084a10b18a000067982ad78898c1000215b11c84960000e5a50597c09a516e084fd1f01650ef228a9dd06e3a7e814197ac000089a0ca90726ad8000000048a00000004a10cea396000000000000e080000000000048915025c968c0581cc2000285c61084f819d00000000afc39980005c40752459153073123c800a270800000006c400007772318000000064d8000000279261027ec00017422e6086628080c051e99b614e1816690863000026c20000000000128c00fd90200000009b4800015e0ba059d42b247780002491b9c15fa1d0000236c00000000001fe830c00005ce054e85a98470b81ec616c24943d60000341a70a5131ef25499cf02d60eaa6e896e48cec7a4292dfce000231a058870900000002aa1ee800000000000cd91b4051a41f212e79aa5623c18d44866896a000194033d8f0c1f980001f945d8225210a9ca828b19a95d08da4ce0397a5204c101eb079062e5a5000e71d1e9a625903494a84cc20c93be53f0a2c7aa91ce372a1
  | 41 => 0x6558ece53c167c96483584baa6a096c000080e068092f400010180ba93583a52f6e59826416fa6219c7815fe12a30500000000abc00020d40000e6259726d44be820a0888c24509a0ca7e9a00c50d897e01925089b804bc8d2985822394d28bd9e141ea20c30acd4a08e9139c0f484aa00021ba0000000537c2ab4d299c20000e52490000050d000000003439b4136a9bb09dc2e00e254215a746e765508e100009be980686a1d0000027a85688db367f962419008c600015b4124275a14a9cd03f987600b1246a8b8947e955443d077a0e5000150f3ee18c91cb24922450688000060c0001d6d0fa026c0000ed85909f90631a4c000023ba5d69d1a99a00001c6c6bc0001e4600021a12be1b5e7d2850e9d919e20a011da0a11bb466f9a5966e9a1c780800050b1e9802da5f26179cde76880006d6844088f18ec81b220c50c19625bc195a58c8f3a10fe33801b27bc37389fa58d1c56393030450403a960925dc22da5603a721ec3648e566702522314021637980005a48e460000fc2195250690982bc7cb09b6000104f184082c57d17760000a0682100005210f1a00000000f6000000014d007613dc8f082aa3f79ecc000000000000000000897000000005b00008ffa414000000013a963e626508c000000000000000000bca84d000052e190e3f8a456955c248802058d33207cc83a842881e1cec3c8270c479980b0b9150c1eb048366e13df9d48af36c5a83409d00006f800009388000495a3bd300000000027667fc8a3890e536c2a9c3ae62c1e9e0a819684d39ec32279e447e710e22411aaa74296503678ffc9bca0a29b11a7019084d077881201970c8c008e0d07a815fa3e49b24205269241383768b180009e600000001f9e00002243d1000083c8c3679c801c27980007e7e53c2a60000000074400003d000002f457b9c305bf0dec8b308ec5a6188e50c8ea87010ba65e718c80a5127a7701a46982a6c6000000027400006618ed4974186241a8da859910107c011838519c1c00000000000c8907b1caa0f14fec1848000000129a79200001c019329eaa06e279d16698c84fc0f51f1e68c101400000003c71fb600000007a716ac00000002c900001959cf41fa988070e889c0001bb814f000070616892ab823b00005e76b49bd0a0c19fa9921d34429149406b40001dba5342c65aea05f8530099d6ec435807c5fa181289f96a658380b84b2c25f000000042381568e680008441ef800016c384b13e4610c00042198a5292202c26c91a2092942e59e4b4a01e9aa604b19bc4f5c696000227a012043b8590485852198e2748492832000009e02826818ad14001cf239d91d8439835c84396c80000000211a7de0000000a04061c2ca98e67f3469057ac0003779970000020e26610f654411fe22556c0328834203687de00024fc2
  | 42 => 0x26e839c55c0dfe210000000008267d61c720001f780000000752086000000003070259645a7ee29ea3be3d38fee31113a08081e8c000091629b8f9015dc4667c3849a6df800020c06a04a24c4b0001d804670000252899c8d045662b624672b925908bf9f2805a8b5e21a27a41094417532659645f071f10691fa0e9a47c3788c190000f2469ba6cc000119122ae7cc00026a20000000000237a000144511892dc70699587259f820a419af1fb9f4e12e0436251c85365b81d75979c7035f83101400fb05491cb87111b964c3c96286e048638d0f724e1800048520181721efa96f81fa8ee11867a11930000010240e83bc750a82e1cbe7da8c8895e6cd8df68620a8619f632d4180d7c37a0098625540871d85c23f7233122901246192262757893895f023a3d919fd5ffa79c81f0ec26cc14cc0de80767371ba638bc44e164905c44607342f90be67820f825599ada6b29dac42495e42a111d600919a80258330045180a762800068943dc33dd4c86901c607d2135621e0877206188a59da1c04a08b504c18b4484e16389c5a232422980825f1d2f4b901c67b817a2000107499b94e38b080004ce911040c56d2631446c501044d50e000000000000000c2c814d72045f89205308df42878fca00008f66111f3e1e69cf82aacd369e6846834c82d6130137483f07ba0e1800088002b84aee5ca4fbc00051800be44a08235188402109972e2154e6f2b28562536804c48381769ad00002638a8500000142b510786fc800000b00784b5148f6011a7600001d9000237897c07ce51c1b608f51c9887d80003f9072e821a10916d0000098c00000012b800000003c4a540000000039a8000000000000000004c505a844f52542eb5aa000020a41731a3e09a51609c71c015ef1ade7bf09e09d3250446f1f6407d1340402a67e3de800070d16358d481ac94f5f7a6129c0e3e5a7ce87f0106850014c622094800000bc8bd0cd87849bf638ea4842479d7248fa61471890480d410d49f707465c91dce5c2c3df5434000000030a7ef8f186c29ccc3c3800000008fa44e925853f5482569085e6e2932a0e69fe05ca08540b9d6966fe0f98747a170474800098722c4a0f27e4630803c0b0098a14342922580c1812ccc981c7108200025d212ac0002a94202078280c095000089f000037a80009ee1cce263159600000002e78000473e4966f9249070597e32829fb24661d380001aec900824067ecfc613100000001d3c0000df1391c0003218da07c300000000000830800008b80000000edf0000dc410aa61a828db3c64487e033a000000000004a8903e9d282ca4569fa4000000021fd4bc9a4086a6c1000000000009c600002941c5e6e9032e863000071b0000000000000000003d4c000999800009e800000015f0000000039d0000000000082f0
  | 43 => 0x8791669f8a00006d55e40a4c8a69f1662d98837fd0a367948c2a9d80ebb05390be7fc260e260a5fc540212b6b98f8832b80e84c687315600b766d5005068f000051900006359354000000000000007e380000001df01060f78538800094e9ed86d4a0c5000167a0000bd332527b65d923a8000000081e800059680000000f2a18924371da12e063ba4466400a0466822886381926581244a91b92763018ba451a98d405180000001e7e0001eb69cb261061187fe0001d3622d0a1804f13da000269e13181a4025000070197dc08f06d269c8dae3e526821368b6623d00000c81da60000eb30001a0000009c00000e424449b7c000261e0db000032f9e1859981cc000000000022b238d88fc5ee1d465bd09e447716687bb0e22000230800001ca26f83f21a645440002116310177e1ef0000449a20ea131b7a67e40009028a8e88aa010000275c945800000002a5304e6f43d500547eb91221d2ca7e0000b6c805a4f4240120641b800015600005f60a6a28d000079c2558709242c995992238f0ce27d420e900012f616b0000000063e242197493e9b2c6214f8c00015440001de834b0f8a54e963a881a370000280057163c18e50b7238580000fa581315585707d351f4325db0886003e600690d84550de06368d4051a0be75e61afa54683034868c9092a1a1014da1c449710c84d40a0c5dd5358868909867226d8228d3428078000000000084180000001d681ca000023981d287a85b600019ca85080007ca87149ab0f8e22814924f808a609f205c0e40c6888780000000816376c000000030044397486ca0e8d143c3db12bca87356a30aa1381c430f84b54dd82e64ac1dc468ca60c3b6a114642925a3e194b49f017e25ca9ca61be1abc6cc988400000004fca7488aa19db000000000020e886119c600004ff82707e2847a0600000c7800000000000d6a00012ce4f100000000000815842286c042c00022644f31bfc2b4ceba6b10eb85361f5e73e92f4000902c00000000f222687f581af403800013d1685000073361f80000001e8e00014fe782861842d80006c31dec799800000007c81b323726a11eca0000000531c0002a98000466c5f895941ea7a8408235e80006ee9fda0001892857a28a31d1ed2000185300015201ba00000000000000066f0ebe56a0e9c38e90593fc60fa50e15821567ed16b200000180001e32000000074811d46a70e5c93e478a0d7dd2461c948006e1bc40001c1255680009260d6800006fe56192340ad4ade7a482af5478dd400006e735199d02fa800066c417a256a74000027e24bfa3a955017bf1a68b1a27f856a0000000000005e865dd521c1000006b833c0000000971928041894060000a9425b99ee2db92529e500009a918c321d40001b71140042c2d50a20f407d9c00085518b561200001075ea6
  | 44 => 0xc7a919ec5c345840c5a1b4951225666c197a62763ee4b602378fa21030ce9558886135a1ae17bd177d6702241f986e8d528049a43039a052e5efa15f442a6620fb17e44ad93960aa1cc00e512a4000084a000000061c13e82fa00ae7a424c28ec242a72f000022c18c06a30dd6414038a0850f8f77188a773a03d6000151c00000003f60e9a00005ca39c02d8299946c000000000012e69f225a2765263c5cfe7c210485c442c0144489cb6415508ea53a16065f3057a04ea46c21cdd8c3268bb574acd5c6f6244863305d66478e3e2784000856094683e8c3203ce6e24c70b0c3c59ea918a9f1299013ac1b285e488f9ce08238541000077a9811d857ce8516619978f4278e1a000000055480005fca4b26038622625e5b2824a3bc4b8c1c065105a2552910664e810c8a1a1b685fd11e87c0f4a466824298587825050f4f6f4966c0bc95c614889bb333008656125c08a926ea77626bc3b9017877997c238f66f8000048400007be76f9ab86839f20a0a092a6f319425ae129c8708f623701c94124c97f9eb28081e89bce37c9b7293d67f200006b400000225c1209e957583853ae5b431080004a80d6e243044c8900d965f6dc087a09e1656b15220000d980000b1800015b82d88f9c000000000000000000e1745c284614066ee00020ab55a195e00010685edc4d600001e60000cd4000000000024d000009ea4ca03700919df20001f89000018c9aa00005448000000112aa059be97ad00007dca0d20fe885a164161e437042e0000000000087d63280c8858023e5391116269813127a083f2ece00a8cf14986a491ee59d065014792c879e810e0b71b8691c03aba0c808a0ec5d087afa3542a49a0290780462cd9efe2f7a07e6b3918071a24a92bb0c3f8938e2748f25fa82ba10c178174524c0b68254914a7328b1e000000068d048e00024444c607f208a865e4d718f200019e09041ab22ad264475f000089c21f2868c420374a1740360528000248698ea75e94622962248e8c5c29ec400000009ef811882a0e608634e78952244200012624148e430b5db6c3ba18d08ce910d60d81428f781384b1c34c00015f830980008fe963b4f0a6aa0750f849bd977353940006a2a62a0000e9638b400057d8000453800000018565f1800084080001eda28e31ae69c4f20e328f49ffa097000081320681a7800054280006fe9df47d8a4a63da85de878032468fd3203189fc803c8c6e7b398782c40de40448a88000153e0fb800031908170001c8a27f0c6d533a364000177a7b6400000004381294b3a66b657a23e4c700000000545888488a13628ac2328408833e7d00cc091a176026dc00000000004f48000904800026a18cb79a273c9c41a4a9941032a090510150189063f81d66bd1616349943e5288b7e4a50d3e79793ae1b58cec07a67449df
  | 45 => 0x5499a294ba00013f438180007cc858c4cd8b2c096dbaa4c9a2d696210a202009ca6d100ac2e4814a52d8fc073b876b091627628696fe24710fe12794ec6cf91824dc003e3830a8a1245f240ee0b060000000467933e22317061df876734c2064000071003b930e00016208569a3b8a800000001e9687a0719916c5ae63f0e300f344320001b706910944000271a00000009e0093c38a5e1e1c8cfbb24b8c95000161a2a69bdc3d698d200015d2914a1727e594dc961231051f16bc721800000020144070e2460e85be458db6a04d5e4a000000000200009809e580c20f02000000049ad2ec3bb19543e88f0a628036a19880000001d265ba15a3234174400024580d10a950000000000092c00000002534c020000a9050916d03be018200007b48dc41100308306077200e8b41ed052c10ee7959994a071ba053a48208564cf8329000070b8aa400004802a7a4e00000cf28e94580076953263e0a68000000094b80004de8e021328d8e3b8639856942969f4820087b8a1c2d699f6000021c8fc14f42fc150698b97f400009e5a038b3442718a300012c089c80000084f46933063818f1f746730a6c00c833889b019634819806ee550e94c8780860a2dc00008964a7824795093133c9400000005c04bf00005b7800000009779e223330002392073857d92e213e4b09b3495e0000898000000022d4157a3340000000802d220456d54c05718d83fc84517f080008bc8000000054a64304a8472cc1e0001996000026400008a924ca4185910f686c0068b1508e9800013de4e8964065497c80a6a30441181280000d54123c00044517a88141e884a5800057885d28e287da7efccd000000006ce00000002772000000000023f2000094000024bc00000006171e5c0639aa7273050214200007220354993170800000002e215785fba1044d49ec2947e72811fc6e669f089301f918a3c1067855c989c879a3f82bc626636d927e830656685d8e1935b00f4a16800052586843138e487d088fe3bc003850780009ec97e696a84825650bd0564a36638a05140ca203e2f4a07082401f2553a13c1d387560b7989b2bfa7e02be8e732a08000995035a2c113160319a4100017f800008041aca55451092d672b115
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc6e769442144001c9ec728842881cf9318e510851057db340ca210a2046ae6868c4214407b6c90b18842881bfa919231085100e76231c6210a2032ae4864c4214407b6c90a98842881afa919131085100e76231a6210a2000ce462dc530440019aec638a608800339188714c1100043f436ea9022000c5c63dd520440ab8d8c5baa40881535c04375481102b43f43eca902205587c87d952044071cd041b2a408800317dd763481100062e3aec69022000c6f75d8920440018d8ebb1240880033518f71481100066a318e29022000ce7621c520440718f4edb2e2088107369db63c41100166d3b0c78822000e986418f10440058f4eca9e20880d73a9db62c411000e753b0c58822045a7a8694710440078f4ed28e2088002baa1a21c411000e753b4438822000aea8608710440039d4ec10e20882bbd814421c41100052ec1ea8b1820048dc8754d63040014bb0628ac60800a9720f7654c100052fc1aeca982064c5e63dd153040074bd0eb1aa60800e9721d6354c100062fba2c6a98203ae571058d5304075caa20b1aa6081771798c7154c100062eb18e2a98200387e85dd943040010fb0bbb286080123e2017650c1030e2f31aeaa182000974815d543040091b90eb1a8608003175d56350c100c54e422c6a18200387e87dd562040010fb07baac4080021fa0775588100063610eeab10205487e871d562040010fd0fa9ac40800e1f21f53588100043f43aa6b10200087c8754d62040091d90ea92c4080021fa1c515881001c3e438a2b10200087f855d932040070f90abb264080123721d634c8100247643ac499020008f5861c532040f30ff0eb14a2080021f21d629441014e2f31eeb1882000c5f7558e31040091df0eb1442080029be1562884100f53642ac51082004cea7058a210403d4dd0bbb442080029b617768841002d7340eed1082035cea70dda2104043c9cc6a9c42080039358d538841019d7240ac6108201ce4e6354c2104001c9ac6a984208002d920553084100063c3aeec8802000c7b53dd910040018f0a3bb220080031eddb75440101c5b840eea8802000cdb76dcd10040019b6ec39a2008003661d073440100063dbb2a68802000ceb76dc910040019d6ec39220080e65ea1e51440100063dbb4a28802039b7287945100415bae50f28a20080e35cdda514401000739bb4a28802000f53739451004001ea0e728a2008003d8dca5144010007b0394a288020329ea8788510040019d6ed10a2008003d89462144010567b028c428802032be2878851004001bc50f10a20080d778dda214401000771bb4428802000f63758851004159ec0eb10a2008003f0dce2144010007e039c4288020acf63538851004001ec2a710a2008002dce1521440101acf5438428802000ceb76085100406b7c50210a2008003d89442144010
  | 1 => 0xd0fb1262880d63b21f624c51000637baec498a2000c6c75d8931440718e8ed28a62880a79518e514c5101c6b8384a298a2000cb864dc131440538e8edbaa62880e31d1db654c5100072a31eca98a20048f4865d131440093e100ba262882cf2d1db644c5105965a3b0c898a2000e946319131440c58e8ecaa2628800b351db734c51020e6a3b6c698a2021ce476dc931440399c8ec3926288003591d4724c5101ae723b6c498a2032ce4761893144001d48c83126288003b118c624c510006b9ba8e098a2041dd3731c13144001bc6e438262880123be1d628851000537c2ac510a201ea6c8558a214400159f06b144288086b320d62885100063632ced10a2001ae4819da21440018dea73b442880031b14676885100f537436cb10a2000c6e76d9621440014db07b2c428813a9ba0765885101453640ecb10a20b1c6e71d96214403d4d90bb1c428800393d4f638851010d67436c710a2000cce76d8e2144001c9ecbb1c428800393197638851000747b26c710a2000e4f85d8e2144001c990bb1c428800393d5363885100072628ec710a20008ef8758e21440014df0ab1c428807a9b215638851000557c22c710a205caac8458e214400199cec31c428800393d94638851000726328c710a2000e8f6418e2144001d18c831c42880029ba19538851000536432a710a2000c6e7654e2144001c5ec8a9c42882078b191538851000727b1aa710a2021e4c6354e21440914dd0d28c42880031b9da518851000727b1ca310a207ee4c639462144043d88c718c42880d6b921931885101adf04026310a203987e86dd521440018b8c7baa42880a31b18b75485102743f43eca90a203887c87d9521440018beebb1a4288003171d7634851000637baec490a2000c6c75d89214406b9d0e1b1242880031b1967608510006b228cec10a2000c6f539d821440018d8a33b042880769ba1b6508510006373b6ca10a2000a6d83d94214409d4dd03b2842882c799a0765085101ef32c0eca10a2028a6c81d94214407d8dce3b284288003999c765085100ed3642ec610a2000e4f53d8c214403959d0db184288003339db630851000727b2ec610a2000e4c65d8c2144001d1ec9b184288003d1147630851000727c2ec610a2000e4c85d8c2144001c9ea9b184288003339c763085100076338ec610a2000e4c51d8c21440011df0eb1842880029be1563085100ed3642ac610a2000aaf8458c21440b555908b18428811ab9e05630851000567430c610a2000cce7618c2144001c9eca318428800393194630851000747b20c610a2000e8c6418c2144161d8ec23184288003d1144630851000537432a610a2000a6c8654c21440018dceca9842880038bd9153085103bf16322a610a2000e4f6354c2144039c98c6a984288002d9205530851023d37434a210a2000
  | 2 => 0xe63189100053742cc63122000a6d8598c624400155d09318c488002ab61263189100056741cc631220008ef8758c62440014df0ab18c4880029b215631891000557c22c63122000aac8458c62440014dd0a318c4880029b614631891000567430c63122000cce7618c6244001c9eca318c48800393194631891000747b20c63122000e8c6418c6244001c9d0a318c48800393614631891000762c08c631220b0ec61018c6244161d8820318c4880029ba1b531891000536436a63122000c6e76d4c6244001c5ec9a98c4880038b193531891000727b1ea63122000e4c63d4c62440014dd0ca98c4880029b2195318910006373b2a63122000e2f6454c6244001c58c8a98c48800393d8d53189100072631aa63122000a6e861446244001c9ec6288c4880039318c511891001c3f42eec992200087d85dd9324403117d09bb264880022f613764c9100043fc2aec992200387c855d9324400117f08bb264880622f211764c9100046fc1aec99220008ef825d932440011ef02bb2648800637a1f634c9100147743ec4992202987c865ce5144001878c8b9ca2880a71718d739451000636312e728a200087f87d8e51440018bae7b1ca2880a697a1b63945100062f3b6c728a2000e1f64d8e51440018bf0fb1ca288003175d363945100062f38ec728a2000e5671d8e51440010ff0eb1ca2880028fe1163945102f51e422c728a2000a6f8258e51440514d904b1ca28800297a1863945100062f3b0c728a2000e1f6418e5144001c38c831ca2880a29ba1b6294510006373b6c528a2000e4f63d8a5144001c98c7b14a2880031b5cf62945100063738ec528a2000e6671d8a51440010ff0eb14a28800297e0d629451014d2e41ac528a2000a6e8618a51440018dcec314a28800393d8c629451000726318c528a200087e86dd63144001878c9bac62880a71718f758c51000636316eb18a200387e87d9631440530f90fb2c62880030fdd7648c5100061e3aec918a2000c5f75d8e31440018b8ebb1c62880031bdd7628c510006363aec518a2029e546394631440014ed0dbac6288002d560f758c51014f2a31eeb18a2000e5463d963144001d28c7b246288003a518c648c5100069aba2a918a2061e546355231440055ad0db1c6288003359db638c5100056a4328718a2000ec463d8a31440019ccec3146288003a9190628c51000762318c518a203987e86dd53144001878c9baa62880a71718f754c51000636316ea98a205d87e87d9531440710f90fb2a62880031b1cb654c5100061fbaec898a2000c3c75d913144001958e5b22628800317dd7634c5100062e3aec698a2000ccc72d8d31440839b0e1b1a62880ca3ba1b724c51000637b2ee498a2000c6c65dc9314400195ec9b9262880032b193724c51000667b1ee498a2021ccc63dc931440391d
  | 3 => 0x7b122000e4c63d4f62440014dd0ca9ec4880029b21953d8910176373b2a7b122000e2f6454f6244001c58c8a9ec48800393d8d53d89100072631aa7b122000a6e861476244001c9ec628ec4880039318c51d89100057340eebb122035ae581dd762440014dd0b39ec4880029b61673d891000557424e7b122000aad849cf62440014dd0a39ec4880029b61473d891000573408e7b122035ae5811cf62440014db09a9ec4880029ba0753d891028e3738ea7b122051c6c71d4f6244001c9ea729ec4880029be1153d891000727c1aa7b122000a6c8154f624405d8dce2a9ec4880bb1b1c553d89100053742c87b122000a6d8590f62440014dd0aa1ec4880029b61543d89100047743887b1220008ed8710f62440014dd0a21ec4880029b61443d891000746a1887b122000a6f855c762440014d90ab8ec4880d63ba1f51d891000476c3ea3b12201d8ef87547624406b1d90ea8ec4880029b60c51d89105a733388a3b122000e6571147624406b1dd0f98ec4880023b61f31d89100053742e63b122000a6d85cc7624400155d0998ec488002ab61331d89100053742863b122000a6d850c762440014dd0bb86c4880029b61770d89100053742e61b122000a6d85cc362440070fd0dbaac4880031b18b75589100043f43ecab122000c5c73d9562440010fd0e32ac488003171cc65589100062fb2ee6b122000c5c65dcd6244001998c5b9ac48800237a1f63589100062fbaec6b122000c5c75d8d624400193ee9b1ac488003271d363589100046f438c6b122000c5f7518d62440018b8ea31ac48800327dd063589100064e3a0c6b12200387e87dd562440010fb07baac48800e1fa0775589100063610eeab1220008df835d562440051b906baac4880023be0975589100043f438eab1220028de87dcd62440018beebb9ac488003171d773589100064fba6e6b122000c5f85dcd62440018b90bb9ac4880033308773589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100043f43ea6b12200387c87d4d624400187ee9a9ac48826f0f1d353589100062fb9ea6b122002c5c73d4d62440010fd0ea9ac4880021f21d53589100061fba2a6b12202fc3c7454d62440018bee6a9ac48800b171cd535891000637baee4b122000c6c75dc9624400199ee7b92c488003331cf72589100066a39ee2b12200087e8714562440018bee628ac488177171cc5158910006373b6ca3122000a6d83d9462440011db0f328c4880029ba1665189100056741cca3122000acd8399462440011df0eb28c488002b3e0d65189100056641aca3122000a6e8619462440018dcec328c4880029b60c651891027536408ca3122000cce76d8c6244001c9ecbb18c48800393197631891000747b26c63122000e4f85d8c6244001c990bb18c4880023b61
  | 4 => 0x3440014b90daa0c68800387d935418d100070e326a831a2000a5e8598863440014bb0b310c688002a7a126218d100054ec24c431a2000a5e861446344001c3ec8288c688003871905118d1017d1f426eca9a2000a3d84dd9534405d4dd05bb2a6880029b60b7654d100043f434eca9a2000c5c639d953440014bb073b2a68800317dce7654d100043ec24eca9a200087d839d953440018bb073b2a6880028fe117654d1017d1e422eca9a2000a5f835d953440014df04bb2a6880ba9b2097654d100043f430eca9a2000c5f731d953440010fb083b2a68800e1fe0c7654d100062fc18eca9a200387d831d953440018b9063b2a6881761f2047654d100063b188eca9a2000c75311d953440010fd0dba2a6880bf0f1937454d103262e31ee8a9a2000c6c62dd153440010f90fb22a6880030fdd36454d1017d1f436c8a9a2000c3e76d915344001878edb22a6880038718f6454d100061fc3ec8a9a2000c3c87d91534400187ee7b22a68800387dcf6454d100043fc3ac8a9a200087c8759153440014bf06b22a68800a9720d6454d1000537c12c8a9a202ea6c82591534400147d0c322a6880030f9d86454d100061e3b0c8a9a2000e1c6319153440054bd0db1aa688003171db6354d100070fb26c6a9a2000e1c64d8d53440018bf0fb1aa68800e97a1f6354d1001d2e43ec6a9a2000c5c87d8d53440018bee9b1aa6880021fa187154d100061fb20e2a9a2000c3c641c553440018bec638aa6881771718c7154d1000636310e2a9a200387e85dd943440010fb0bbb286880063ba0b7650d1000476c16eca1a200387c859d94344001938873b286880021fe157650d1001c3e42aeca1a20008df835d943440011df04bb286880063b2097650d100047dc02eca1a200387e851d943440010fb0a3b286880032710c7650d100043e432eaa1a2061c5c635d543440018d8c4baa86880021fe1f6550d100043ec3ecaa1a2000e1c43d9543440311bd0fb1a8688003179d76350d100062ebaec6a1a2018a9e84d8d43440091eb03baec48800e3be1d52d89100053742e65b122000a6d85ccb62440738eae228ec4880029b60f65d89100056741ccbb122000acd83997624400159f06b2ec488002b320d65d891000536c18cbb122000e4f65d8f6244001c98cbb1ec488003a3d9363d891000727c2ec7b122000e4c85d8f62440014dd0b31ec4880029b61663d891000557424c7b122000aad8498f62440014df0ab1ec4880029b21563d891000557c22c7b122000aac8458f62440014dd0a31ec4880029b61463d891000727b28c7b122000e4c6518f6244001d1ec831ec488003a319063d891000727428c7b122000e4d8518f6244001d8b0231ec4880029ba1b53d891000536436a7b122051c6e76d4f6244001c5ec9a9ec4880038b19353d891000727b1ea
  | 5 => 0x80029721571d8d100054fc22e3b1a2000a9c845c7634400159f04b8ec688002b320971d8d1000567416a3b1a2000acd82d47634400159f04a8ec688002b320951d8d100052f438a3b1a2000a5d8414763440831bd0fa0ec6880023761f41d8d100052f42e83b1a2000a5d85d07634400159d05a0ec688002b360b41d8d100052f42883b1a2000a5d8510763440014bd0b90ec6880029761721d8d100052fc2ae1b1a2000a5c855c363440014bd0ba06c6880029761740d8d100062e31eeab1a200087e87d956344001878e9b2ac6880031b1cb6558d100043f438cab1a2000c3c7419563440018d8e432ac6880030fd977458d100061e32ee8b1a2000c9c63dd1634400187eebb22c6880030f1d76458d1000656396c8b1a2000c6f65dc963440018d8cbb92c6880032bd937258d100066631ee4b1a200387e87dd563440010fb09baac6880022fe117558d100c45e422eab1a20008df835d563440011df04baac6880063b2097558d100043f438eab1a20188be87dd1634400187eebba2c6880030f1d77458d100061fc2ee8b1a2000c3c85dd1634400187ea7ba2c6880030f54f7458d100061fba8e8b1a2000c3c751d163440010fd0faa2c68800e1f21f5458d100061fba6a8b1a2018c3c74d51634412b8d8e5aa2c68800317dd77358d100062e3aee6b1a2000c9f74dcd6344001938e9b9ac6880063ba1f7258d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000667b9ee4b1a2000c6f54dc963440018dea7b92c6880031b54f7258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a2000ce472dc563440010fd0e28ac6880030fdd05158d105ae1e3a0a2b1a2000c6f72145634409d8d8e428ac6880032e1d37058d100062f3b6ca31a2000a5d87d9463440014bb09b28c688003955c76518d100046ec3cca31a2000a5e85994634400153d09328c688002a76126518d1000567414ca31a2000acd8299463440011bf0eb28c688002a7e116518d100054e422ca31a2000acf82594634400159904b28c68800297a186518d100062f3b0ca31a2000a5f8719463440014bb08328c688176972046518d100072b388ca31a2000e5571194634400193cedb20c68800387d976418d100070e32ec831a2000e1f85d906344001c390bb20c688003879d76418d100070ebaec831a2000e9571d9063440011bb0f320c68800297a166418d100052ec2cc831a2000a9e84990634400159d05320c688002b360a6418d100046fc3ac831a2000a5f8559063440014b90ab20c688002b3e096418d1000566412c831a2000a5e8519063440014bb0a320c688003279d86418d100070fb28c831a2000e1c651906344001c3cea320c688003875d46418d100074ab88c831a2000a5e86d506
  | 6 => 0x43ec36ea90c2028c6e62dd521840510fd0eb2a430813a1f21d654861000637baac490c2000c6c7558921840019d2c5b8243080029be0d65086101ae3738aca10c2000e6671594218403b4dd0ab1843080029be19530861000536c32a610c2000b648154c218407b4db0d28843080f29e61a51c4210007b128c438842000a3e8498f654400147b0931eca880029ba0a63d951000536c14c7b2a200b87d8718f65440018bae631eca8800297a0e62d95100052ec1cc5b2a200087f845cf65440070f902b9eca88003175cc73d95105b53b408e7b2a2038a75811cf65440010fd0f21eca880021f61e43d95100043f43887b2a200087d8710f65440014dd0421eca880029b60843d951058d3b40ee5b2a2038a7581dcb65440010fd0f996ca880021f61f32d95100043f43865b2a200087d870cb654400147d08196ca880028f61032d95101c43f43e63b2a200087d87cc7654400147d0998eca880028f61331d95100053741663b2a2000a6d82cc765440010fd0e18eca8802e1f61c31d95101c43f43e43b2a200087d87c8765440614ed03b86ca880021fa1f30d95100043ec3e61b2a2002c5e76d4f63440014bb07baec6880029760c75d8d100043fc2ae9b1a200387c855d363440010fd0faa6c6880029760f54d8d100062ebaea7b1a2000c5d87d4f63440014bb09a9ec68800e37e1d53d8d100052f42e87b1a2000a5d85d0f63440010ff0ab96c68800e1f21572d8d100043f438a3b1a2000a5d8314763440014bd0c3aec6880029761365d8d100054f424cbb1a2000a9d84997634400159d0532ec688002b360a65d8d100054fc22cbb1a2000a9c84597634400159f04b2ec688002b320965d8d100052ec20cbb1a2000e1f65d936344001c38cbb26c68800387dd764d8d100070e3aec9b1a2000a5e8599363440014bb0b326c688002b3a0a64d8d1000566c14c9b1a2000a5e8519363440014bb0a326c68800297a1b54d8d100052e436a9b1a2064c5e76d536344001c3ec9aa6c6880038719354d8d100052f42cc5b1a2000a5d8598b634400153d09316c688002a761262d8d100052f430a3b1a2000e1f6414763440014bb09baec688003175d475d8d100062f438ebb1a2000a5d841d763440014bd023aec68800297a1674d8d100052ec2ce9b1a2000c9f749d3634400159d053a6c688002b360a74d8d100052fc2ae9b1a2000a5c855d363440014bd0a3a6c6880029761474d8d100056b408e9b1a2041ad5811d363440014bd0faa6c6880029721f54d8d100052f40ea9b1a2000e1f5495363440014bd0b396c6880029761672d8d100054f424e5b1a2000a9d849cb63440014bf0ab96c6880029721572d8d100052f42e85b1a2000a5d85d0b63440011bd0e216c6880023761c42d8d100052f42885b1a2000a5d8510b63440014bf0ab8ec68
  | 7 => 0x3d840c965840014bf06b8acb080029720d715961000537c12e2b2c2000a6c825c5658416f4f700b8acb080021fa1f31596100043ec3e62b2c2000a3e84cc5658400147b0998acb080029ba0b315961000536c1662b2c200e87e870c565840010fb0e18acb0800317dcc31596100043f43e42b2c200087d87c8565840750fb0f3aac7080028f6127558e101d52ec1ceab1c203ba5f835d563840070fd0bba2c7080021f6177458e100043ec3ea8b1c200387e85dc963840010fb0bb92c7080021f61c5158e100052ec18a2b1c200087d84dd953840070ff07bb2a70800e1f60f7654e100052fc1aeca9c200087f845d953840770ff06bb2a70800317e0d7654e100043ec36e8a9c2000c6e62dd153840010fd0eb22a70800297e0d6454e100152e41ac8a9c2000c6e621c553840070fd0bbb287080021f6177650e1001c3f42aeca1c200087f865d543840018dcc4baa87080025d2057550e100043fc3acaa1c200087d875954384001c3886b2a87080123721d6350e100c54e422c6a1c20048ee87d4962840091d90ea92c5080123ba1f3258a100053742e64b142000a6d85cc962840014dd0b39ac5080029b6167358a1000573c0ae6b142000a6e851cd62840014db0a39ac508002aba107358a1000556c20e6b142000ccd731cd62840014db09a9ac5080029ba075358a101d536c2ca6b142000e4f5394d62840014df08a9ac50800393e0d5358a100053640aa6b14203ba6e8514d62840014dd0b21ac5080029b6164358a100053742a86b142000a6d8550d62840011dd0e21ac5080023b61c4358a100053742886b142000a6d8510d6284001d1a8621ac5080029ba177158a1000536c2ee2b142000a6f855c562840014d90ab8ac508002b3e0d7158a100056641ae2b1420008ee87d4562840011db0fa8ac50800399d465158a100f477c3aa2b14201d8ec8754562840014db0628ac5080e29ba045158a100047743e62b1420008ed87cc562840014dd0b98ac5080029b6173158a100055742662b142000aad84cc562840014dd0a18ac5080029b6143158a1002476416ec99420048ec87589328400559906b1265080031d997714ca100063b328e29942000ce5621c532840530ff0cb9ca3080a71798d739461000637312e728c200087d8758e51840018bae6b1ca3080031b5cd62946101ce3738ac528c2000e667158a51840018dcc5bac630800297e0d658c61000637baac518c2000c6c7558a31840010fb0dbaa63080031b98b754c61014c3f43aca98c205d87c8759531840018d8e4b2a63080023b61b724c6100063732ee498c2000c6d65dc931840431dd0eb1263080723b21d624c61000637baac498c2000c6c7558931840014df06b2c43080cb1b9c565886100f53742ac710c2000a6f8654e21840014db0ca9c43080fe9b61a51886100
  | 8 => 0x2b1ca2900029d20563945201c537436e528a40bab6681dca51480716d501b94a2900e29b219329452014f2631a6528a400387e859da31480010fb0b3b462900021fe15768c52001c3e42aed18a400387c851da31480010fd0dbac62900021fa1f658c5200043e43ecb18a400387e85dd931480010fb0bbb2629000e1fa16764c5200043ec2cec98a400387c851d931480031d9043b262900021fa1b754c5200043f43eca98a400087c87d9531480ab8d8e5b2a62900031bd97724c5200063632ee498a4056a6e86d9621480a98dcedb2c42901535a9c3658852000536c1ecb10a4000a6e81d9621480ab8dce3b2c4290157999c7658852002477436e710a4021ccc63dce21480093d501b9c429007a9b217638852000537c2ac710a401ea6c8558e214800155f08b1c4290172ab21163885200057240ac710a4000a6e8654e21480014d90ca9c42900eb5a9c1538852004c76c3ec310a401ea6e85d8621480014db0bb0c429000399d9761885200f536428c310a4000e645118621480659d4e030c429000399d94618852000732328c310a4000e67851862148001cc90a30c429000399d4c618852000732a98c310a4000a6e8694621480014d90d28c429000399d8651885200073230ca310a4038d6a709462148001dc0c338442900127ae1d70885200077030ae110a4000a5d8314763c40014bb07aa2c78800e1fa177258f100043ec2ee4b1e202ea6e82dd953c40014db05bb2a7880029760e7654f100052fc1aeca9e2002a5e83d9153c40014bb07b22a78800e1fa177650f100043ec2eeca1e20018ee82dd943c40011db05bb2878800e1fa147650f100043ec28eca1e20188de87d8d43c403153d09b1a87880021f61e75d8b1001c3fc3aebb16200087f835d762c40018d842baec58800e1fe1f53d8b100043ec3ea7b16200087f8754f62c40010fb0ea9ec58800e3be1d52d8b100057240aa5b1620b9e642114762c40091e902baac5880e71d1c45158b1001c3f42eec996200087d85dd932c40070fd0b3b265880021f616764cb100c45f424ec99620008bd849d932c40051dd0fb12658800ab3a0f624cb1001c3ec3ec528e2038c757694631c4053cacc728c63880a71d5db758c710005aac1eeb18e20048f586dd231c40c58eaecaa463880034d5d1548c71020de84028718e20049f0805d131c40679ceec3926388003591d4724c7101ad7240ac510e2035ae5868c621c40016c902a9843882e2d9a06510871019572c346210e2049b64858c421c40675cf0c9884388126d921531087100043ec26e6b2c2000c5f739cd65840010fd0f21acb080021f61e43596100043f43886b2c200087d8710d65840014dd0421acb080029b60843596100043f43e64b2c200087d87cc965840010fd0e192cb080021f61c32596100051f42064b2c2000a
  | 9 => 0x5158d200061fba0a2b1a40b5c3c7414563480014bb0628ac6900031ddc45158d200063a388a2b1a400087e869d953480014bb073b2a6900021f6127654d200043ec1ceca9a4000c5d839d953480010fd033b2a6900031b0867654d200051fc22eca9a402fa3c845d953480014bf06bb2a6900029de057654d200053a40aeca9a400087e861d953480010fb083b2a69000e1fe0c7654d2001c3ec18eca9a4000c6e821d953480018db043b2a6900031b8c87654d2000636990eca9a400087e811d953480018d8423b2a6900021fa1b7454d2017e1e326e8a9a400087c87d91534800187ee9b22a6900021fe1d6454d200043e43ac8a9a4000a5f8359153480054b906b22a6900029de056454d200053a40ac8a9a403aa6c865c9534817969f06b92a690002d92057254d200043f430e2a9a4000d64211c553480070fd0bbb286900021f6177650d2001c3e42ceca1a4000c9c439d943480010ff0abb2869000e1f2157650d200046fc1aeca1a40008f7815d943480011e902bb2869000e1fa147650d200043ec28eca1a4000c9c431d943480010f90cbaa86900021fe1f6550d200043ec3ecaa1a4000a5d83d954348001c3887b2a86900623721d6350d200c54e422c6a1a4000ad48158d43480a98d8edb2a64900039318f654c92002476432e899240049e8805d1324800559907b226490003a390f644c9200147643ac89924002acc8359132480015c902b22649018b1b1d9544c92030f2631aa89924002ace86d8d32480015990ca1a6490003a3591434c9200e666318e29924000d64511c532480250fb0fb2ec2900029da0765d85205de36b90cbb0a4000a7681197614803b8dce53aec29000e1fe1d75d85200043fc1aebb0a4000c6c215d761480070ff0fa9ec2900021f61f53d85200053b40ea7b0a400087f8754f61480010fb0ea9ec2900029d20553d85200055b42663b0a400387e86dd561480a90f90dbaac2900021fa1f65585200062e39ecab0a400087e8719561480018b8e632ac29000317d9773585200062e32ee6b0a4056c6c7219461480011ef0eb08c290002b520d61185200053b40eea30a40018ec825d461480014bb063a8c2900771b1c875185200053b408ea30a400087f855cc61480070f90ab98c2900021fa1f53185200053b40ea630a400087c8754c61480058bce6a98c290003175cd53185200053a40aa630a40328ec8754861480651d90e990c290002b920532185200055b4266230a4000ae582cc461480014ed03bb4a2900021f60e769452000637414ed28a4000c6d829da51480018d8433b4a2900021fa1876945200053b408ed28a400087d831da51480018ed023b4a2900031b08476945200043e432e728a400087f87d8e51480010ff0eb1ca2900021f21d63945200051fc22c728a405ea3c8458e51480014ef
  | 10 => 0x18c40048f58798631880018e8eb30c63100031d1d5618c6200043fc2aec98c400387c855d931880018e8eb30a631000339dca614c6200247a43ac298c4000c74755853188001cc8a330c431000399d4e618862000732a9cc310c4035ee27098621880651df0eb0c43100029be1561886200f53642ac310c4000e66619462188001ccac328c4310003b898570886200943ec38c7b2a4000a3e8418f654800147b0831eca90003175cc63d9520006b210ce3b2a400087f845cf65480010f902b9eca900031b08573d95200051f420e7b2a4000a3d841cf65480018bae639eca901569ba0873d95202a536c10e7b2a400087e8790f65480010fb0f21eca90003175ce43d95200043f43887b2a400087d8710f65480ab4dd0421eca900029b60843d95202ad37416e3b2a4054a6d82dc76548001cc84338eca900021f60e71d95200063b90ce3b2a4000c6c219c765480018e84338eca900031908671d952000537c12e3b2a4055a6c825c76548001cc842b8eca900021fa1f31d95200043ec3e63b2a4000a3e84cc7654800147b0998eca901569ba0b31d952000536c1663b2a400087e870c765480010fb0e18eca901561fa1f30d95200043ec3e61b2a4000a5d83dd763480014bb063aec6900021fe1574d8d2001c3e42ae9b1a400087e87d5363480014bb07aa6c69000e1fa1671d8d200043ec2ce3b1a400087f855c763480070f90ab8ec6900022fe1171d8d200c45e422e3b1a40018ec825c763480010fd0e28ec6900021fa1f6558d200061e3a6cab1a400087e871956348001878e832ac6900030fd977458d200061e32ee8b1a4000c7765dc563480018e8cbb8ac6900031dd947158d200063a328e2b1a4000cd4631c563480070fd0fbaac6900021f6137558d200043f40eeab1a4000c6c21dd5634800117f08baac6900622f2117558d200047bc0aeab1a40008f4815d563480010fd0e3aac6900622fa1f7458d200061fbaee8b1a4000c3c75dd1634800187f0bba2c6900030f2177458d200061fa9ee8b1a4000c3d53dd1634800195843ba2c6900030fdd47458d200061e3a8e8b1a400087e87d5163480070f90faa2c6900030fdd35458d200c61e3a6a8b1a4000c9c74dcd63480070fd0bb8ac6900021f6177158d200063bbaee2b1a4000c7475dc5634800196ee9b8ac6900032d1d37158d200063b42ee2b1a4000c7585dc563480018eea9b8ac6900031dd4f7158d200063aa9ee2b1a4000ce682dc563480019cb05b8ac6900031ddd47158d200063a3a8e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a4000c77851c563480018e90a38ac6900031dd507158d200063ba98e2b1a4000c75531c563480019ac8638ac69000339e087158d2000672410e2b1a4000ce6421c563480010fd0e28ac69000e1f21c
  | 11 => 0x4c0018dceab96c2980031b5d572d853000637aa2e5b0a6000c6d545cb614c0018dea6b96c2980031b54d72d853027637390a3b0a6000c6d72147614c0019cae410ec2980023de1d611853000572412c230a6000a7481550614c031938e8a18c2980021fe15721853001c3e42ae430a6000a5d83144614c0015e300108c2980029da0776945300051fc22ed28a605ea3c845da514c0014ed023b4a2980e29721943945302f70e3228728a6028a6e82d86514c0014db05b0ca29800e1fa1676905300043ec2ced20a60018ee829da414c0011db053b482980021fe15769053001c3e42aed20a605ec3c64dd6414c00187eebb248298062a721943905300064f3b28720a600387e859d9414c0010fb0b3b282980063ba0a765053000476c14eca0a600387e859da214c0010fb0b3b4429807a9ba17768853000536c2eed10a605caae84dda214c00155b09bb4429807a9ba16768853000536c2ced10a6000ce6719da214c0015cd023b442980038bd9154885302e716322a910a6035acc8650e214c0b9d18c8a1c429807a9ba17618853000536c2ec310a600387e859d9214c0010fb0b3b24298002b9e0564085300057240ac810a6000e2f64550214c0b5c58c8aa04298002d92055408530195664328610a605ae8c6450c214c03b4dd0bb0842980029b61761085300073228ec210a6000ae587d84214c0019cb0fb08429800399a17610853000732c2ec210a6000e6754d84214c001ccaa9b0842982fb99d4f61085305f732a9ec210a6000e6451184214c0015cf0e308429800399d50610853000732aa0c210a60bdec673184214c001d8ae630842982f799d4c61085305ef32a98c210a60bdec643184214c001d8a863084298003b89c0610853000770b80c210a60b0ec630184214c161d8860308429800399d8651085300073230ca210a6004a9c8650d404c005938eca1a8098012e6201435013001c3f42ee2b1c400087d85dc563880019c84238ac7100029760c5158e200052fc1aeca9c4000d64211c553880070fd0bbb287100021f6177650e200246e43ac6a1c4018a9c8458d43880014e902a9cc3100cab9a07729862000572c16a330c4039c758714661880014eb0628cc31000399dc851986205cf32390a330c4039e72801466188001ce30028cc3100e799c8051986201cf32900a330c400387e87dd561880010fb07baac3100e31d60775586200063610eeab0c401dc6c721d561880010fd0fa9ac31000e1f21f53586200043f43aa6b0c400087c8754d61880014e902a9ac3100031ddd7515862000572c16a2b0c403887e8714561880018eeea28ac3100e29da1c51586200063b438a2b0c4000a75831456188169cc8e428ac3100029da0776946200063b38eed28c4000c76715da51880730ff0eb0ca3100021fe15768c62001c3e42aed
  | 12 => 0x30f1d474586300043f43ea8b0c600387c87d51618c00187ee9aa2c3180630f1d354586300052ec1ea8b0c6095c6c72d51618c0010fd0eaa2c3180021f21d54586300061fba2a8b0c6018c3c74551618c0c78d8e4aa2c3180063ba1f725863000637baee4b0c6000c6c75dc9618c00195ee9b92c3180032b1d3725863000637aa6e4b0c6000c6d54dc9618c0018dea7b92c3180031b54f725863000637ba8e4b0c6000c6c751c9618c00195ee8392c3180032b1d072586301c43f438a2b0c6000c3f74145618c16b878e828ac3180031bdc8515863027636390a2b0c6000a7681dda518c0012bf06ba4a3180021fe1d62946300043e43ac528c603987f87586518c00147f08b0ca31817a8f211619463000537c12c328c6028a6c82586518c0010ff0abb4831800e1f21576906300247ac3cc320c6018ab484586418c0010ff0abb2831800e1f215765063000477c12eca0c60018ec825d9418c0091e90eb0a8318176d5a07758c63021c6fc3ac318c6000a9f84586318c001caac328c631800356dd5708c63001c3f42eed10c600087d85dda218c0014df0ab14431807a9b21562886300f53742eed10c6000a6d85dda218c0015cd03bb443180ca3be1d618863000537c2ac310c601ea6c85586218c00155f08b0c4318172ab21161886300043fc2aec90c600387c855d9218c00117f08bb243180622f211764863000573c0ac810c6000ae481590218c0016c902aa043180039914661086301ac77c3ac210c6000a6f85584218c03b4d90ab084318002abe1161086302d556422c210c6000e6451584218c00717f0eaa6c8980021fe1572d913001c3e42ae5b22600087f855c7644c0070f90ab8ec89800a3720d71d913000477c12e3b2260018ec825c7644c00147b0828ec8980023be09755913000c76412eab2260008f7815d5644c0011e902baac89800e1fa1771591300043ec2ee2b2260018ee82dc5644c0011db05b8ac8980031ddc451591300063a388a2b226000a3d849d9544c00147f08bb2a8980029be09765513031d36412ecaa26000a77815d9544c0014e902bb2a8980628fa1b645513001d1f43ec8aa26003a3c87d91544c17f87ee7b22a8982ff0f5cf64551300061fb20e2aa260b5c3c641c5544c0012bb0638aa8980bf171d97550d303258fc22eaa1a602fe1c645d5434c03153d0db228698003569d47050d300c64e3a287b12600087f855c7624c0070f90ab8ec4980029760c51d893000672310e2b12600387e851d9424c0010fb0a3b28498003271d9435093000c77416ebb0a60008ed82dd7614c0070ff0ebaec2980021fe1175d853001c3fc3ea9b0a600087d87d53614c12b8dce5aa6c2980021fe1d54d85300043ec3aa9b0a6063c6e72553614c0014e902aa6c2980031b9d672d853000636bace5b0a60018ef875cb61
  | 13 => 0xda6c1ce0a984200b66819c153084016cb03382a610803591c67054c2133da7c1ae0a984200b67815c153084016c902b82a610803591c57054c2117537430e0a984200a6d861c15308401ac8e2382a6108765be1d7550c2163da7c1aeaa1842c5f0c435d543084016c902baa8610b1a5be0d7550c21006a7c1aeaa1842c5d4e635d54308401a9ac6baa861080359e057550c21004b640aeaa184200d64815d543084012c902baa8610b071b9857550c21006b330aeaa1842008ed86dc5430843b2dd0bb8a86108025b6177150c21006b228ee2a18421d96e851c543084012db0a38a8610803591447150c210ecb742ee0a18420096d85dc143085896cd03b9ca2109cf531cd7394421004b7c22e7288421d96c815ce51084fd8dcc2b9ca21080359985739442139ea618ae7288420096d8750e51084e7e1886a1ca2108d2d9a07709442161eb338ee12884228a6e869c251084014db0d384a210ac7599c5709442124db3408e128842c0b6681dd631084012db09bac62108035360f758c42139ea731eeb1884200d4d63dd631085812dd03bac621080359a07758c421604b340eeb188427ec6e61dd63108401accc3bac62108765b217748c421004b7c2ae9188421d96c855d231084393c902ba462108025ba1d548c421004b643aa9188425ad2e745523108401a5ae8aa46210802d9205548c4212d4e7c3a87188425ad8e7450e31084dff0882a1c62108765ba1e518c421005a6c1ca31884273f473194631084012df0ab8462108765b215708c4210ecb743eea988427ec6f76dd531084012db09baa6210b0a5be0f754c421614b6c1eea988427ec6e61dd53108401accc3baa62108765b217744c4210e4f2c0ee898842008ef865d131084012df0aba262108765b215744c421004f5c02e898842329e8805d131084012dd0eaa262108025b21d544c42160e37bb2a89884200b648155131085812dd0f28a62109fb1bdda514c42139fa218ca29884221ccf768c531084070fd0bb8ac9180021f617715923000c77416e2b2460008ed82dc5648c00147b0828ac9180028fe11765523001c3f43eeab14600087d84dd5628c0010fd03baac5180031b0877558a302a43f438eab14600087e87d51628c0070f90faa2c5180021fa1d5458a300043e43aa8b1460048ec87549628c0070fd0bb8ac5180021f6177158a300043f438a2b14600387c87145628c0010ff0abb2851800e1f2157650a300047bc0aeca1460008f4815d9428c0091d90eb128518062ab2116250a3001c3f43eeab0c600087d84dd5618c00117f08baac3180622f211755863000477c12eab0c60018ec825d5618c03117d0fba2c3180030fdd774586300061e3aee8b0c6000c3f85dd1618c0018790bba2c3180030fd4f74586300061ea9ee8b0c6000c9c31dd1618c00187eea3a2c318
  | 14 => 0xf825d943484011f700bb286908123e2017650d2101c3f428eca1a420087d851d943484010f90cbaa86908021fe1f6550d210043ec3ecaa1a4200e1c43d9543484311bd0fb1a8690862a7a136350d2114c3e432e728a4229c5c635ce51484010ff0fb1ca290803175cf63945210043fc3ac728a427ea6f8258e51484010fd0dbac629093a1fa1b754c5212ec3f43eca98a422887c87d9531484518d8e5b2a62908031bd97724c5210063632ee498a4221ccc63dc9314849d4dd0db2c42908a399d87658852100536c1ecb10a4228c6e71d962148451ccce3b2c429087a9b217638852101477c3ac710a4200a6f8558e214843d4d90ab1c42908029ba19538852100536432a710a424ea6e869462148451ccec328c42908d71bd8975981215a63ab88cb302420387e86dd560484510f90dbaac0908021fa1f65581210062e39ecab02420087e8719560484018b8e632ac09080317d9773581210062e32ee6b0242008fb8758060484efa5ce9ba2a610b1a5b6137454c210ecb6c1ee8a9842d0d4e63dd15308401a9ac7ba2a610b434bd0f7454c21004b740ee8a9842cfc6e61dd15308401accc3ba2a610b3ad3e0d7454c21005b3c0ae8a984200b64815d153084014db0db8aa610802d961b7154c2100732c36e2a984200d6774dc55308401acae9b8aa610b3359dcf7154c2166fa3b9ee2a9842ccf4663dc55308401e8ac7b8aa6109bad360e7154c21605b340ce2a984200a6f865c553084e569f06b8aa610803595c47154c21004b6c20e2a98421d96d831c55308591a9cc638aa6108035358c7154c2165e37308e2a984200d66611c55308401ace8238aa610803591047154c21646b2988e2a9842cab66871c55308401acd0e38aa610802d9e187154c21005b2c30e2a984200d67761c55308401acaec38aa61080359dd07154c21006b33a0e2a984200d65741c55308401ac8e838aa610b2359dcc7154c2164fa3b98e2a9842c8f46631c55308401e8ac638aa61080359e187154c21006b3430e2a984200d65861c55308401ac90c38aa61080359e107154c21006b3420e2a984200d65841c55308401ac90838aa61080359d907154c21006b3320e2a984200d65641c55308401ac8c838aa610b0359e0c7154c21646b3418e2a9842c0d65831c55308591ac90638aa610b2359d8c7154c21646b3318e2a9842c8d46631c55308591acac638aa6108035158c7154c21646b2318e2a9842c8d67431c55308591acc8638aa610b235950c7154c21646b2218e2a984200d67801c55308401acd0038aa610803596007154c21006b2400e2a984200d67601c55308401accc038aa610803595807154c21006b2300e2a984200d67401c55308401ac88038aa610b2359cc07154c21646b3180e2a9842c8d65301c55308591ac86038aa610803591c77054c212c
  | 15 => 0x2baec1108d63b61f65d82211ad75406cbb04421ec6e75597608846b1db0fb1ec110887339cf63d82211ad75406c7b04421e96f87d4f60884012db0fa9ec1108025be1d53d8221004b6c3aa7b044200d66759c76088401acaeb38ec11087a5b61e51d8221004b7c1aeb304424e96c815d660884658dcc2bacc1108035998575982211ae37b02eb3044235c6d605d6608843d2df0fa9cc1108025b61f5398221004b7c3aa7304420096d8754e60884512df0f28cc1108fe5b61e5198221274b7c38a3304420096d87146608846b5d30fb04c1108033a61f60982210073542ec13044200e6985d82608846bcd4ebb04c1108d79a5d7609822100735a9ec13044200e6953d826088401dc503b04c1108039a94760982210073428ec13044200ae681d95608846b1d90eb2ac1108d63b21d6358221006a7b9aa6b044221d4c7354d6088569cccc228ac110887539cd5318221006a6b9aa630442009eb87580608840147d0931eca908028f61263d95211043ec38c7b2a4200c5d7318f65484010ff08b9eca908031b08573d95210062eb98e7b2a420087e8790f65484010fb0f21eca908021fa1c43d95210043ec3887b2a4228a6e8210f65484014db0421eca908a21fa1f31d95210043ec3e63b2a4200a3e84cc7654840147b0998eca908a29ba0b31d952100536c1663b2a420087e870c765484410fb0e18eca908a29ba0a70d952100536c14e1b2a420087e87cc365484010fb0f986ca908021fa1c30d95210043ec3861b2a4200a3e840c3654840147b08186ca908a29ba0830d952100536c1061b2a4200a76810c365484014eb02186ca908029760f75d8d210052ec18ebb1a420087f855d363484070f90aba6c6908021fa1f54d8d210043f438a3b1a4200a5d8314763484010ff0ab86c69080e1f21570d8d210043f43ecab1a420087e8719563485a58eee232ac69080e1fa1f7558d210043ec26eab1a4200c6c21dd563484011df04baac6908023de057558d210043f438eab1a420087e87d5163484070f90faa2c690b3f1bdcb5458d2100637baee4b1a4200c6c75dc963484018e8ebb8ac6908021fa1c5158d2165e37b90a2b1a42d2c777114563484014db05bb2a6908021fa1a7654d210052ec1ceca9a420087d849d953484010fb073b2a6908031760e7654d210063610ceca9a4200a5f835d953484014df04bb2a6908029de057654d210043f430eca9a420087d841d953484070ff063b2a69080e1f60c7654d210063b908eca9a4200c6c211d953484018e8423b2a6908021fa1b7454d210043e43ec8a9a420087f8759153484010f90eb22a690a069be096454d210043f430e2a9a42d1c77611c55348401ac84238aa69080e1fa177650d210043ec2eeca1a42008ed82dd943484070f90b3b286908021fe157650d2101c3e42aeca1a42008e
  | 16 => 0x44ca2130f2731aa89944202acf8658d32884033990ea1a6510802b3e19434ca212e6c63a2869944200e8f6450d32884451db0db8a651087a5ba17714ca21004b6c2ee299442719e687dc532884516c902b94a3108a69be19329462114f2731a6528c4200b67814ca51884012df0ab94631087a5b215728c62112cf240ae518c4200c5f7354d60884058b8e6a9ac1108023ee1d6018221004f340eebb1c42218ed87d93638844359d07b26c710b3f9398f54d8e210e66731ce3b1c42d9ec6639c763884019cec938ec71080359d5271d8e216cee331ce3b1c42d9d67539c763885b3acaa738ec710b677190e71d8e21005a6c18a3b1c42cbe4e631476388401acce228ec7109732b9d36458e210057340ec8b1c42218ec87591638840169b07aa2c71088733ddb6358e21005e340ec6b1c421e96e85dc163884012db0bb82c710803999877654e21005a6c1ceca9c4200b66819d9538840169f06bb2a710802d9a047654e2140e973a6e8a9c421e96d83dd1538859fa5e87ba2a7108025ba077454e216c5a7c1ae8a9c42d7e2e64d91538844369d07b22a710802d360f6454e21005b340ec8a9c427bb4d839c55388401acee338aa7109f6d3e0d7154e21004b6c20e2a9c421e96d831c55388597aca6238aa71096ed360e7054e21345a7c1ae0a9c4200a6e861c153884014db0c382a71087a5ba177650e21004b6c2eeca1c42009e6819d9438843d2dd0a3b287108025b6147650e21004f3408eca1c421e96f875d543885ad69f06baa8710b07c310d7550e21006a7c1aeaa1c420096c815d543884b939d0fb1a871080333ddb6350e212e5c7426c6a1c4200e8f64d8d438840178d03b1a871087a5ba177150e21004b6c2ee2a1c421e96e851c543884012db0a38a871087a5ba177050e21004b6c2ee0a1c42d5b6681dce51884fda98e6b9ca3108025be1173946210f4b640ae728c427ed4c315ce51885a9c9cc7b1ca310802d9a076394621004b6c3a8728c427ef0c4350e518846d6cd03b84a31087a9ba1a709462100536c34e128c4237b66811c251885a76cd03bac63108025b613758c621006a6c1eeb18c4200d6681dd6318843d2d90bba463108025be15748c6210f4b642ae918c420096e8755231884012d90eaa463109734b9d1548c62100696ba2a918c425c9cf8750e31884b9b1ce8a1c631087a5ba1e518c621005a6c1ca318c427ef473194631884012df0ab84631087a5b215708c6210f4b743eea98c4273c6f76dd531884012db09baa63109cf1b987754c6210f4b642ee898c420096f855d1318843d2d90aba263108027ae01744c6211acf4402e898c420096e8755131884012d90eaa26310b171bdd9544c62169cb743ca298c4273c6f7694531884fde886328a631087333dda314c621004f340eebb04420096f835d76088401accc
  | 17 => 0x1262caae781594624c5854dd0c328c498b2f1b9d8651893100536c20ca31262c0a6f83194624c5814db06328c49893a9b204651893164733988ca31262c8e6431194624c4011db0f320c4988029ba16641893100536c2cc83126200acd83990624c5b95cb03320c4988023be1d641893100537c2ac83126200a6c85590624c4015d700b20c498802ba201641893100537428c83126200a6d85190624c4014dd0daa0c4988029b21b5418931005a6c1ea83126200a6e86550624c4014d90caa0c498b0a9ba18511893169733b08a2312620387e85dd9424c4010fb0bbb284988623ba1f62509310c557426c4a1262028f686dc5424c4018e8cbb8a84988031d194715093100673b10e2a12625e87c865d2514c4bd878c8ba4a29880257e0d749453100636312e928a620087f87d92514c40187ae9b24a2988021fe1d649453100537c12c928a6228a6c82592514c4014f700b24a2988e29e201649453114537436c528a62d3c6e76d8a514c5a9e8863b14a2988031b5d362945316a637b9ec528a62d4c6d73d8a514c401ccce3b14a298b031b9d86294531617a2188c528a620087e86dd6414c4018d8c5bac82988028f613659053100637baec520a6200c6c75d8a414c56b0fd0fb2a82988a61f21f655053100636396caa0a625a8ee87d89414c4431d90fb1282988031bdd76250531006363aec4a0a625da5e86dd6314c4bb6ad03bac62988a7559c7758c53114f2bb0ecb18a62188df87592314c4835b100b24629897697a1a518c53114eab38ca318a6229e5761946314c4015b306206c098802bc60440d813100637396cb3026200c6e72196604c4018decab94c0988031b1957298131006373aec53026200c6d75d8a604c4018dcea314c0988031b5d4629813101c3f436eab02622987c86dd5604c4010fd0fb2ac0988030f1d3655813100636396cab02620087e87195604c401878e832ac0988031b1c865581310061fb2ee8b026200c3c65dd1604c4451d90db92c0988031bd9772581310063632ee4b0262008ee87d89604c4018deebb12c0988031b1d7625813100657ba6c4b026200cac74d89604c4011dd0e312c0988031bdd46258131006363a8c4b026200caf74189604c401958e8312c09891b39dc462581312ee3ab88ca30262008fb87580604c40157108b00c0988023da0775d8e210052ec18a3b1c42dbc767114763884014bb07aa2c71080e1fa177058e210043ec2ee0b1c4200a5d839d953884014ed033b2a71080297e0d7654e210152f41ec8a9c4200a5d83d9153885b569f06b92a710b231d9847154e2101c3f42eeca1c420087d85dd943884070fd0a3b287108021f6147650e210c46f43ec6a1c4218a9e84d8d438843d2dd0bb9287108025b6177250e210147743ec89944202ace83d91328840559d06b2265109871bdd95
  | 18 => 0xc4010fd0e32ac8988031b1c8655913100637b2ee4b226200c6c65dc9644c4018f6cbb82c8988031e19770591310063db28e0b226200c78651c1644c401970c8382c89880e1fa1f755913100477c12eab2262018ec825d5644c4011f700baac8988123e20175591310043f438eab2262018ee87dc9644c4018deebb92c8988031b1d7725913100637a9ee4b226200c6d53dc9644c4018deea392c8988031b1d472591310043f438a2b226200c6f72145644c49d8d8e428ac8988e71e1c051591310063dbaee0b226200c7875dc1644c4019d6e5b82c8988033a1cb70591310063da9ee0b226200c7953dc1644c4018f0a3b82c8988031edd470591310063c3a8e0b226200cdb731c1644c4019d6e4382c8988033a1c8705913131d37416ecaa26200a6d82dd9544c4010fd0d3b2a8988028f61276551310043ec24ecaa26200c3d849d9544c4010ff073b2a8988021f60e76551310051fc22ecaa26200a6f825d9544c4c74d904bb2a8988029ee0176551313153c402ecaa2620087e861d9544c4070ff083b2a89880e1f61076551310043fc18ecaa2620087d831d9544c4010fd0c38aa8988031b188715513101c77c3aa5b126200a6e85d0b624c4014db0ba16c4988029b61365d893100536c20cbb126200a6e85993624c4014db0b326c4988029be1564d89310053642ac9b126200aeb80593624c4015d100b26c4988029ba1464d893100536c28c9b126200a6e86d53624c4014d90daa6c498a571b9db54d8931005a6c1ea9b126200a6e86553624c4014d90caa6c49898f1b9d954d89316a537430a3b126221ae581dd3624c4014dd0b3a6c4988029b61674d893100657ba4e9b126222ace839d3624c40159b073a6c4988029ba1474d893100536c28e9b1262dea6f83d53624c5bd4db07aa6c4988029ba0754d893100717aa4a9b126200e2f84553624c5bb4df06aa6c498b769b60d54d89310053640aa9b1262218ee87d47624c4011db0fa8ec49880399d4651d89310ec77c3aa3b1262218ec87547624c4014db0828ec498b4e9be0c51d893169d36c18a3b1262218ee87d07624c4011db0fa0ec4988029ba1741d893100536c2e83b126221ace83d07624c40159b07a0ec4988029ba1441d893100536c2883b126200a6e85dc3624c4014db0bb86c4988029ba1670d893100536c2ce1b126221ae5811c3624c4011dd0e286c4988023b61c50d89310053742e81b126200a6d85d03624c4011dd0e206c4988023b61c40d89310053742881b126200a6d85103624c44359d06206c498802b360c40d89310057340881b126200ae581103624c4018d8c5baac4988021fa1f65589310043f438cab1262d1c7771195624c4fd8dcedb28c4988029b613651893161537c1eca31262c2a6d83d94624c4011db0f328c498b029ba16651893100477c3aca3
  | 19 => 0xbf17dd97550e313258fc22eaa1c622fe1e645d5438c4016a902baa871880317ddb6550e310058ec26caa1c6200e1e64d95438c4bb6ad03b2a8718862a7e196450e3143c6ec36e2a1c6200d5575dc5438c40147b0832ec518b231d9c465d8a310043f43ecab14620087e87195628c40147b0832ac51880e1fa1f7558a310043ec26eab14625d87e81dd5628c4018d843baac5188021fa1c7558a310043f43ea8b14620387c87d51628c4010fd0eaa2c5188021f21d5458a310c64f3a286b14620087e87145628c4070f90e28ac5188029760c5158a3101c3f42eeca14620087d85dd9428c4010ff0abb2851880e1f2157650a310064fbb286a146200c7465dc5428c4051eb0c38a85188031d1947150a31006caa18e2a14622787c865d2518c4070ff0fb24a318b7e1fe1d649463114c3e43ac928c6229c5f765ce518c4538bf0cb9ca3188a7172197394631004afc22e728c6229d57815ce518c453aa902b9ca3188a717985739463114eab30ae728c620095d8750e518c4bd4bf0ca1ca31897b879914394631005abc0a8728c627987f8758a518c4530f90eb14a3188028f613659063114e2f39ecb20c6200c5f655ce418c43153f0ca1c831880b275d94390631005cbc0a8720c6200a3d84197608c4018dce5b2cc1188028f610659823100637390cb304625dc7671196608c4018decab94c1188031b19572982312ecbb40eeab04620087e87d95608c4010fd0e32ac1188028f610655823101c3f43eeab04620087d84dd5608c4bb0fd03baac1188021fa1f545823101c3e43ea8b04620087e87551608c4010f90eaa2c118863279d143582310743f43ca2b04622987c87945608c4010fd0e28ac11880e1f21c51582310052ec18a2b046200a3d84194608c4011f70eb00c1188029ba0a64d953100536c14c9b2a622487d87193654c40187ae8326ca988021fe0d74d95310043ec1ae9b2a6200c3d741d3654c4010fd0fa16ca988021f61f42d95310043f43885b2a620087d8710b654c4534bd06216ca988029760c42d953114c3f43e83b2a620087d87d07654c4534bd07a0eca988029760f41d95310053741683b2a6200a6d82d07654c4010fd0e20eca988921f61c41d95310061eba083b2a622987e87c87654c4010fb0f90eca988029ba0a70d953100536c14e1b2a624aa76811c3654c4534eb02386ca988021fa1f40d95310043ec3e81b2a620087e87103654c4010fb0e206ca988a697a0c40d95310052ec1881b2a6200a6e82103654c4014db04206ca988029da0440d95310053ac0881b2a620087e87083654c4010fb0e106ca988028f61375d91310051ec20ebb226200a5d831d7644c4010ff0ab96c89880e1f21572d91310043f438a3b226200a3d84147644c4010ff0ab86c89880e1f21570d91310043f43ecab226200c6c72d95644
  | 20 => 0xb643a84994a200f0d4350932944710fb0fb1ec1288e21f61f62d825161d3b40ec5b04a200c6e72d8e60944530ff0eb1cc1288a7179cd63982510062eb9ac7304a200c6e7258e60944018dec6b94c1288031b58d72982510ecb640ae5304a239c6e615ca6094401accc2b94c1288e31bd8172982511c636b02e5304a200c6d7298a60944014f301314c1288031b5c8629825172db940ec1304a23887c8758d60944018bee6b1ac1288a7171cd63582510043f43ec4b04a2b1a7681d8960944710f90eb12c1288c2dca07605825114e2f39ec6304a24bc7671d8c60944958ece2b18c1288021f61e62182517263b38cc4304a200c6d7218860944938ece2310c1288029e6006218251004bdc3ac0304a231d727158060944014dd05326cb188029b60a64d96310061eba0c9b2c62e3c767198b658c5818ece2316cb18803555ce71d96310052ec1ee9b2c6200a7681dd3658c40187ee93a6cb188030fd0d74d96310061ea1ae9b2c6200c3d741d3658c4014bb063a6cb188029da0474d96310052ec1ee5b2c6200a7681dcb658c4014bb06396cb188029da0472d96310043f43e85b2c620087d87d0b658c4010fd0e216cb188021f61c42d963114d2f41885b2c6200a5d8310b658c5c58bae738ecb18b871d5ce71d96310072ab9ce3b2c6200c76729c7658c4018e8e538ecb188a697a0f41d96310053741683b2c6200a6d82d07658c40187ae820ecb188a697a0c21d96310052ec1843b2c6200a5d83dc3658c4014ed03b86cb188029ba0a70d963100536c14e1b2c6200a5d831c3658c4014ed02386cb188021fa1f40d96310043ec3e81b2c620087e87103658c4010fb0e206cb188a697a0c40d96310052ec1881b2c6200a6e82103658c4014db04206cb188029da0440d96310053ac0881b2c6229a5e83c83658c4014bb07906cb188021fa1c20d96310043ec3841b2c6200a5d83dd7648c4014ed03baec9188029760c75d92310053b408ebb24620087f855cb648c4070f90ab96c9188021fe1570d923101c3e42ae1b24620087e87d95648c4010fd0e32ac91880e1fa1f75592312ec3f40eeab24620087e871d5648c4071790eaa2c9188021fa1c515923101c3e438a2b246200a3d84145648c40187cc93b2a9188025da0676552310051ec24ecaa46200c5d839d9548c4010fd033b2a9188031da0676552310051fc22ecaa46200976811d9548c40187d083b2a91880e1f61076552310061ec20ecaa46200c5d831d9548c4018bc863b2a9188021fa0476552310063b408ecaa4622793c87591548c43147f0cb22a9188030f1d964552310061fc3ac8aa46203a3e87591548c4074790eb22a9188030f21d645523101c1e43ac8aa462e0c3f73591548c5c187ae6b22a918ad70f99071552310061eb20e2aa4620095d831c5548c4014b90cbaa87188
  | 21 => 0x72d53614c8010ff0eaa6c2990021f61d54d85320053a40aa9b0a6400c7575d47614c8015cb05a8ec2991771b5c851d85320063aba8a3b0a6400a7587147614c8018eb0e28ec2990029d61051d853271d3bc18a3b0a64e3a7583147614c9a5ccce428ec299347995c851d85320047bc3ac230a6400a7485584614c9b35cf04b08c299002d560c51185320053a40aa830a6418c9c7450c614c8391d90ea10c299003a350d421853200572c16a230a6400a5d83144614c8015ab06288c2990031d61c51185320053ac20a230a64c8e5683144614c9814eb06288c2990039560c51185320052ac18a230a64c8e5643144614c801caa86288c29932399dc851185326df32390a230a64dbe6642144614c801cca84288c29932399cc851185326df32190a230a64dbe6720144614c8010ff0ab80c29900e1f21570185320045fc22e030a64188bc845c0614c831938e8a1ec099003a350d42d81320043fc2ae3b02640387c855c7604c8014bb0628ec0990023ee1d601813214c3ec3ec9b1ca229a5e83d93639440187ae8326c728ba71d9c662d8e5114d2f418c5b1ca2c4c767118b63944530fd0f322c7288030fdd26458e5114d2f41cc8b1ca22987c8759163944534b906b22c7288021fa1c6458e51745ab40ec6b1ca22987e8798963944534bd07312c7288030fd0f7458e5173c3f40ee8b1ca200c5c31dd1639440187ee93a2c7288029760e7458e510052fc1ae8b1ca200c3d741d163944014bb07392c7288021fa1f4258e510043ec3e84b1ca20087e8710963944010fb0e212c7288a697a0c4258e510052ec1884b1ca22987e87d0563944010fb0fa0ac7288030fdd34158e5114d2f41e82b1ca200a5d83d0563944014dd05a0ac7288029b60b4158e510043f43882b1ca22487d8710563944530fd0f90ac7288021f61f2158e5114d2f41e42b1ca200a5d83c8563944014dd05382c7288029b60a7058e510051fc22e0b1ca200a3c845c163944954ed02382c7288a69d6047058e510043f43e80b1ca20087d87d0163944010fd0e202c7288021f61c4058e510061fba080b1ca229a5e8310163944014bb06202c7288029ba084058e5100536c1080b1ca200a768110163944014eb02202c7288021fa1c2058e510043ec3840b1ca229a5e8308163944014bb06102c7288025da067650e510070e21ceca1ca200a5f835d94394401c3886bb2872880317e0d7650e510062e18aeca1ca200976811d943944010fd0db9287288021f61b7250e51144b7416e2a1ca20096d82dc543944070fb0c38a87288021fa1b7050e510043ec36e0a1ca22887d87d8f62944510f90eb1ac52880317dcd6358a5114e2e39ac6b14a2e6b6681d8962944018ecc3bb265288025da06764ca51004bb408ec994a200c76611d932944512b90ea1a652897b471d1434ca5114c
  | 22 => 0x32ec2a18031b9ca65d854378f0e21acbb0a8600c6e725976150c018dccab96c2a18031b59572d8543006c621ae5b0a86188dd83dd76150c031dd05baec2a18023b60b75d85430043ec3cebb0a8600c5d739d76150c070ff0ebaec2a1803175cd75d85434dc3fc1aebb0a862f87d835d76150c018dceb396c2a18031b5d672d854300666b9ce5b0a86018ef875cb6150c018dceab96c2a18031b5d572d854300666b9ae5b0a8600c6f535cb6150c018daa6b96c2a1ad7175cc51d854327637390a3b0a8600c6d721476150c01a3887baac2a1bc29760e655854300636394cab0a8600a76819956150c5b0f90eb2ac2a1bbf8710d655854300636392cab0a8600a74815956150c018dccbb92c2a18031b5977258543006c621ee4b0a8600c7a65dc16150c018f2cbb82c2a18036610f70585430063d328e0b0a8600c79651c16150c01b3086382c2a1a6e57e0d75185430068e21aea30a860087d879946150c010ff0eb28c2a18023de1d61185430043ec3cea30a860387f875d46150d370ff06ba8c2a18be1f60d75185434dcafc1aebb028600d1c435d76050c010fb0f3aec0a180e1fe1d75d81434dc3fc1aebb02862f87d835d76050c010f902baec0a18021fe1571d814301c3e42ae3b0286008ef825c76050c031d904b8ec0a180e1fe1c51d81430043ec38a3b0286eea5d839966050ddbc3886b2cc0a180e1fe19751814330c3ec32ea3028600d1c435d46050c010fb0f328c0a1bb29760e65181434de2eb9cca3028600c6e729946050c010ff0eb28c0a1baf8710d651814300637392ca3028600c6e655c86050c018dacab90c0a18036310d72181430063b32ce23028600c75659c46050c01b2887388c0a18031d99571181430063ab2ae23028600d94435c46050c011f70eb00c0a18033908671d91320043fc2ae3b22640387c855c7644c80147b0828ec8990021fe1570d913201c3e42ae1b2264008f7815d5644c8011e902baac8990023ee0175591320247c402eab22640387e85dc5644c8010fb0bb8ac8990031ddc451591320063a388a2b226400a3d849d9544c80147f08bb2a8990029de0576551320053a40aecaa26400a7b805d9544c8c54f100bb2a8990025760c7155132006b2108e2aa2642fc5c765d5434c8c963f08baa86990bf871917550d32006a6392eaa1a6418a9e86d91434c80371d0ca1a8499006e321943509320c74643286a126402d8e7650d424c831d18eca1a849900b231d943509327578742a86a126400f0d8550d424c9d5e18a2a1a8499002d560c51d853201476c16ebb0a640087d879d7614c83b8dce53aec2990031b5ca75d853201c3fc3aebb0a6400c6d725d7614c8010ff08baec2991461fe0d75d85321743ec1aebb0a6400c77815d7614c8018d842baec29900e1fe1f54d85320043ec3ea9b0a6464c6d
  | 23 => 0x18553607329904230aa6c0e64320846154ded4bf06b80c2a98028fa1070185530051ec20e030aa691a5d831c06154c014dd04380c2a98029b60870185530043f43e8030aa60087d87d006154c0187ae9a00c2a98021fa1c40185530043ec388030aa65da5e831006154c014bb06200c2a98029ba08401855300536c108030aa600a76811006154c014eb02200c2a997697a0f20185530052ec1e4030aa600e6421c806154c010fd0e100c2a98021f61c2018553007321084030aa63a87d87d936054c5f87ce9b26c0a98030f5d364d81531d43ec3ec5b02a600a748158b6054c492bb0738ec0a98025be0971d8153174b6412e3b02a63a87d871876054c018ece230ec0a9be3175cf64981533062eb9ac9302a600c6d7298a6054c014f301314c0a98025be097198153174b6412e3302a6f7d5973d826054c750f90eb22c0a98bf0f1d164581531d53c402c8b02a60087e87d896054c750f90eb12c0a98029d2056258153174b7416e2b02a60096d82dc56054cd38bee730ac0a98031ddc661581537b62fb98c2b02a6f5d5b73d816054d512bf06ba0c0a98be1f61f641815317e1f3a6c8302a600c3d74d906054c018dce5b20c0a98029e603641815300637392c8302a600c6f645c86054c018dac8b90c0a98ef1bd8d7218153006a7b1ae4302a60096c815c86054c758dec0b90c0a98eb1b58172181530043ec3cc4302a600c6d729886054c018dae4310c0a989e57e0d7118153004b7c12e2302a62e96c825c46054c018dce5308c0a98031b5ca611815300637390c2302a600c6d721846054c018ece2308c0a98025ee1d60181537a5adc1ac0302a661b1e84dcd6550c01a3ee9b9acaa18034710c715954330e2f43ee6b2a86f3c5f74dcd6550c01c3ee9b9acaa18029760e72595430052fc1ae4b2a8600a77815c96550c014e902b92caa18029ee0172595430053c402e4b2a8600c6d721c96550c014dd05b8acaa18029b60b71595430052ec1ce2b2a8600a5f835c56550c014df04b8acaa18029b20971595430053dc02e2b2a8600a78805c56550c018ea6238acaa18021fa1f21595430043ec3e42b2a8600c7471c856550cc34bd0610acaa18029760c21595430063a38842b2a8600a5d839c16550c014bf06b82caa18029be09705954300536412e0b2a8600a77815c16550c014e902b82caa18029ba08705954300536c10e0b2a8600c79701c16550cc34bd07902caa18029760f20595430043f43840b2a860087d870816550d372bf06baec4a18034710d75d89430043ec3ccbb12860087f875976250c010fb0f3aec4a180e1fe1d75d89434dc3fc1aebb12862f87d835d76250c010f902baec4a18031b08575d89430043fc2ae3b12860387c855c76250c070ff0e28ec4a18021f61c51d89430068e21aebb0a86f2a5d839976150d378bae7
  | 24 => 0x2a60295e839c76254c492bb0738ec4a986e57e0d70d8953014ae41ae1b12a62e87c875916254c5d4d904b22c4a9bff53dcf6258953006abb9ee2b12a600c7586dc56254c018eec9b8ac4a98031d59371589530063bb1ee2b12a600d5763dc56254c01acd05b8ac4a980355dcc71589530063bc30e2b12a600c77641c56254c018eac838ac4a98031dd8c7158953006abb18e2b12a600d67821c56254c01acec438ac4a98031d98871589530063a310e2b12a600d64621c56254c01ace4038ac4a9aa257e0d74d855317c3ec3ec9b0aa62fc3e74d936154c0187ae9b26c2a98031b9cb64d855300637392c9b0aa62e96f875cb6154c018dec8b96c2a98031b59172d855300637b1ae5b0aa600d4f635cb6154c01acf02b96c2a98029d61b21d8553005aac1843b0aa600d65720876154c0187ae9324c2a9bfa9760e64985530053ac0cc930aa62fc3e745926154c014eb03314c2a98029ba0b619855300536c16c330aa6fdd5573d866154c010fd0fb22c2a9bf317dcf645855300636396c8b0aa690c5f735916154c018d8e4b22c2a98ba5ba1f7258553006a7b9ee4b0aa600c6f64dc96154c018dac9b92c2a98031bd8f7258553006a7b1ee4b0aa600d4f731c96154df7aaee7b0ac2a9803591cb615855300637b94c2b0aa600c6c729856154c5f0fb0fb20c2a98bf0f9d364185530061eba6c830aa60087d879906154df34bb07320c2a98030f5d064185531743ec3ec430aa600a7581d886154c014ef02b10c2a98029ba0b611855300536c16c230aa6e2b55839846154c010ff0eb08c2a98029be09611855300536412c230aa600977875846154dc34ef0cb08c2a9bead5e0d6118553005b2412c230aa600a7586c846154c016ab06108c2a980399d882118553007333104230aa600e65620846154c01cc8c4108c2a986e57e0d701855348d2ec1ee830aa600a7681dd06154c0187ee93a0c2a9be69760e74185535443fc1ae830aa600c3e435d06154c0187886ba0c2a98030f5d074185530053b408e830aa600a7681dc86154c0147d08390c2a98028f610721855348d2ec18e430aa600a76811c86154c014f500390c2a98029e60072185530043f43e8430aa60087d87d086154c0187ae9a10c2a98029da0742185530053ac0e8430aa60087e871086154c010fb0e210c2a997697a0c42185530052ec188430aa65da5e83d046154c014bb07a08c2a98029ba0b411855300536c168230aa600c3d741046154c014eb0f908c2a98031d61f211855368d3bc1e4230aa6d1a7583c846154cbb4bd06108c2a98029760c21185530053ac384230aa6c0e56830846154d914eb06108c2a98039560c2118553007334104230aa600e66720846154c01ccae4108c2a980399d082118553007332104230aa600e64420846154d81cce64108c2a9b03998c821
  | 25 => 0xe02f0018054002001003800c000001006807400a0230000000006000000001c01e006001803c004002000801000401c000004c00803e000804000000f000007409c00b0028038012003001802401200f0030024002001013802801600300080100220050030080000002001000000c007000001c000015002013407a000000001800000d000001801400401f00140160020088020002001008802400200001200000020050010018022001004002800a007006800400001200b0078034000000001c0000000010010026000000800003003100b000400c0000000028028008002803c0040020000034000002000002c008009043804800601e013800c01c0040000000000004000001001e00d005011001e00001c000400802100c0000000000000801c00000f00180f8004004000001401200f000002007000e0008044034006001000006000e0000000008002000000001600d002003407400000800c80000030098000014003014803c0000080010008000006000000001600c000000800c00e000014800400000e8004022009006802c00400300b000400e0000000000000002016002c0060000010018014000000000000200800680340020040010004038012001805c00c01b002001401e0020088000010007001800403400800a003400c00a0058010018007002800801400f0060054036000000000000a003000000401400000300fc006026000803402e00900b802000000e00c800000a001000804000000400300000020000028020000000011802000206a000800c00c002001001801c01000300180000000010020000002001803c00202e0000000004003007000403200e0028008000000000001001e00100c000000000300000bc016034007805c028004004000400000200080080000010010020004024018001801e00c000001401600c00080000120030054069760e62d915317c3ec38c5b22a62fa3e8418b6454c018dae4316c8a989e57e0d71d9153014ae41ae3b22a60096f825c76454c5d2d904b8ec8a999297a0e72d915380d2ec1ce5b22a600a3d841cb6454c018dae4396c8a98029ba0b71d915300536c16e3b22a600c3f439c76454c0187a8738ec8a98031d50671d91537e52fc1ae3b22a664a5c835c76454c014df04b8ec8a98029b20971d91533252f418e3b22a6aaa5d831c76454c010fd0f90ec8a98021f61f21d91533252f41843b22a600a5d830876454cc94bd07b86c8a9aaa9760f70d91533252f41ce1b22a6f8a5d839c36454c014dd04386c8a98029b60870d91530063cb80e1b22a664a5e83c836454c014bb07906c8a98021fa1c20d91530043ec3841b22a62fc3f76d916454e01a3ee9b9ac8a9a529760e6259153174b7416e2b22a60096d82dc56454c5d0fb0fb26c4a98bf0f9d364d89530061eba6c9b1
  | 26 => 0x3800c02000c001805803e0080020004036001006807c004001000009c00001f002001400200000100140000000008000008005000000401e000001802400c01100000140000030030004000001003002800801f004803400000a000005401c00d0038000000000000000000400500200340040000008038024007001001c00400300180000180000018020000009002000000800200a000c00c000001009400a000001002c00200800200a4042001003001c012001000000c0000140018128020002000000c03e00e003805c008004000801800000b0060028000007000004800e013001804000c00d001800400e003000004c00c03a0018008002022000000000800200b802c00200000080640120050008010004001004000805c0040000004002006002802c00e018000806c010001002000400400000000200000040008000004000005804c00a000001800c0180060038000014004016000c00600001080d40120020000014016004000000002e000003800c00a0020050090000008001800008e0000010010000002000801000a008000800402400800a000402a014000801400800500d00180460050010004000000004001c024009000001000000c003804002a01000f002c01e0000010000002016000006c0160060000008002002002007c09602a00e800800003a00100000220030000000022001000002c00e008005801005800a00b80040120010000008006004000002001e00e00000b001e01e005006c02e00100a0040000000000800802a00b000000001201d0060064000002003005c02a000000801c00201e01f001805c00000c800400800000580a000200a000003006a00000180000000150008028014000001000000000c00000340220280068000006015000000000000b002800000000000000000000050038058004026002001000200c0088000014003003000400200e007004000000302080700040030000018000008001803800a000012000405201102e003800c01300080080200010000024016003000806c000011001001c00000900100200060060020010040003000000403201c002801400401602f80500000000028004006027003000c00000a001808800800000e004802e0160020000000001017001003c0000010074002003001000001000d000000005c00b000000c0060050050000014001003802801400100b8020016000001801c01400100000e001a000001800400000a00000080000070020058000015007800c00402e0060008026002000005000a0030000000002000002001c00001e003800000000a0000020006004001801800001200a000c0020000038260004000012000000600200480040020060000000008012001804400a000008000c006000000001000402c004801c000007000802000
  | 27 => 0xb969e7083c0015024e401faf2d0160b000000000001b90001ff19c60000000a240000005a5a4640008ce3c1a0f40000000000e940001da0000000000000000000000049016f1b4000095134100017c293a08b3021262a2a84d9dc00000001d684f940600026c9fa40000000000fe64f203719d350837320311280004d6d6a0002b000000000bfd85d50442662212885e4cd85b100014b407080023c000069146b00000005560001958000b8907b8000d941472c5000161452893286409cda0c26318444c89660438dd052624a27ca69c5a4c2010280001906e5058909d81812ca7787e1204a4248200742fd10a24213b81343bc32980000481849ef492600025861d207c000000093a2290a6a51000117831e000000219dab829f46a86b0d6c74835c0b020005d6000325981c0f4886a9d83827ea1681a926dc2ca22a1f1800000047310d40007640000000f780003b880000000005b8000034c0e42d924b41b69e30000410bba18780caf18000b5880031317ac01c4b9b0d0c703f112adf101967ec51d14992c66570d9209143630f00003b004a4ec2f3169800042800000000006cc5a4ab980006ce5e1a6843b9bad207b6e879a00001b000126ed0a1bc206d9420e04a9b4989c6562000038caa67293fc8964000d7309b00002560e9161b3451c07e62f65954a2c0002c101fc00013c00027f055a50d26f122b2ce32321a00016123ae58716316680004eeacf045c35246b94a155b0004b900310245831a89aa14d07ee08d000000096200025dcbc6754b0196dd8d2bd839c12485520003b79b980000001e9a6e40003775ca821553600000032b54aa00036f26d06e44b43442204a6e848000400a000003004000200800e0000002053000001400600e00d0040014003002000005600501580040020040100038002000001002c000004008803c000003002801002c0130008000012018005000000000100480080020210000060006000019000401c0000058000000000001801000c001003000801200c000000000a00c0088004000000000005803800300f800002c008002801401e0020000020002001006001802000d0008000008007000802400c019005001c0060020000008000001031000000a000000800c006004000007800e002001002800000900080040000000000014006003000801800e00401580000060060080008004010000800000e001002000c00801b000000802800400280780000090000024016025000000802e00100181300000190188004010010003800c026011008001000a01700980300020170000040000004000801400000400000a0008000000005c04a00500000d00000000000000002011009000000a0000060024000007015801c00001100480f400000000e00000080050030004022003004000c00200200
  | 28 => 0x235e20c74080ace00002595b1a95000000145800063d31ac000a5f00016a9970750000077ae501570000000000b13000203994c7b62a39428ad25e46cd80001831a1547892a18cd722e3b15893a4c437681801748654631a4c00005b000023800002a59d0cd449162338a1b16546d0d0838000c3c84b4872240f744a83e6800196a05e1cc00416100004d412a48c0b176332190000000000198c6440748c2a9c00007ab0ad80240006642aeab0c00086a0e90a40ac041a2c780019f22b9d14a3f400078927c0000764000208067869e48b455b6b038054500005a4000c320036b113f63023e8897c0002344f118ad33ed0134e00002ad0000000352000d7d6d78000b50785859b56ca410006af143001127f89d968c59f00053980f0000db70002b6c1b325c0000000000d7c0000d4c75061f00027e06d08eddeb8d046586db00000000005f45dc8891538135c0c8000000000000000139e0004fb320e93ead8000350462c95d00024340000004ca25110080001672fa40000000001df439e000000191973204b00014809040003b41b9c99829b1a480002851bfbea339d96ecf34063400d40c99c07ab5d97e5670ce992c55ec79c740988fc21011dd11b1290029092329c47243e23f8ab8df6088879086d986a7733d2f9c9902c9bc9a2552bccec3d38bdd4349834c80a548400000001b080003fa4eb80000008163df800117cba78c42851322ccd572c859a8a0000000000fc00006cf800000000000023d542e00000017550da5c510e0309160b8661fa164cbcb984e325591b0a5d381a84891879f1efcea584a163a5a948cc89c7b3872fdd47ac6a1afa568e16b262a0b2c14a88256cb2714dc229430da6f000ad4a4ea1ab9301b480c8ea2ce6653c4950921a485c15f8934e00026a25614a933aa2048e000164a9af39a0d715d6baf1424590a2362238c872dabe3cf1710fc185e75a2cb95782a31af83188db99400000012f020db04800253d3f200028c878571ab6f28487a9ae8d2f0001e380002762bc89f60007851d80da80009a638f251499648a03b821067e76b5bd5cbd83800043800013d696e29dab3d2d431243faec650400015e405d98e4a44cc8f3879600000000000000002b1a8258f21cc0e40114d2c4549dd85e30fa675435b068bf26f80b0b004000d844dd2998000000335b055266b8b3e080000cc0006720dec000d3e533a22000000050bc0018be0002d996fcc4cb1d0cc10f40000000002fa942c683000000000058015100011bad830003520368bda2108a45265d16047b2cce78ab10002f3841b1815d8a22f0fc45b4b59818000997419843aa5a0000002c7186677c000291183a00052284c4d802ab33134100006b1559e17d62435653f084545a84a3ca2aa4f1e575000182137c658535af1d190a3b82640007fe30c2f900
  | 29 => 0x4015c4a070e8c0015bc3c05ec80016be9ac3380ba980e25a4ef9a74f8e0d32a5800051400068380015988970f3c057592586283f17143cab726eb2898922562e4195058ea580e4e11d0017e50bea630aa40002b8000072400000011d949600063f000020a42c1160000db00003ba0000000be30001118000c9582c000000000048f23943ba00000000000000004baa0800003af0d73006a228a7448b58c36a41720206f082496f234b2e9560000034000044b0006279b580005a1217b20b27782f66f06b341469a07124047d044b44fd5941de0000eb234872a0eb00db06c503cc155414c3b461566d33194b3472122c89bceaca2e10968602061e3013ae510ac9e900006d78cf661415100054a0d2cfbae894941936cf2ce5116c546c431185ce70204a22a80e626151e1a9c04d0d86c10c54ec07354ae00ec59e60c00000011449b637900008eac0ae44c0008a6a3b3d700012b2c180001140e3ad400ba9014e26b7a01154fcdba40093bf0b581e00000007808322b40230a48f04a9849096804e238d2785e983bea7a312862530c8a061481682ca684000280824693e5bc924ce4e0005c80bf9870ba13b68668502ca2b62901da38d4425e95b42861d76bfafd16bc4185bb857d07ed1e00000015a000000016b8274d9a6de03a864ea1a99f00002bc9360732ce08c84802830b4d634a400000208fd6cf1000000090c00000023b17fc0000000e5cc1cb971a0000087e000608a948701a7500023ae70e2ef139337cd003ca3d89db097233400005c418a2df63399bc7129e565599e55bb122035eeb8f116b40000000f5e4d7689894e73207a605c7fc26a7a140cdd1c2ba00000027b4ce6c7a8c109545ca00004f298c0000001ca0154000c6193d40015068a15acf554e9466531982257822852be99a8c640ff07e02a91984a5243a72477ea5b08586ec16a433492883113ed5455f9afd9b6b5028252546fcd292a507ecd746890d9807c0506c15320de815ea208038295b320710d282551fc1cd6b88d080ae3f661b9a913e63464a6a85a4b6c0414400e886ec5514f1ad4eeec731ef82a5b0c4b063e16ba9ecd6f53535d8c887c3021a1b950ccfa2a7282c000000000000192d7a900035884201b8c5d83a118d9a20a0cb2c00000039b2e1000015041f0000edc4946413484000da85119270b8423b00017b19b400043988698c8c2a51b8397a1e000000067cf7072e0a904f45840005f98000b2641f45985396b62454e0000000014f00014099a682735d97d53e068b266a0d03512871d3ad059eabf84bb11bc2280005f7b11cc5c0000002a7740c2c45ff88b60000000001cad14624d000100d9feaf82abab66a2a7cf24710319a08014a108bd2362446d9aeaca0a17918a0001147d190000ac042a64e4bc0ed8087a215940e6d8b47dd3f57370dd89
  | 30 => 0x28380026ac94cc6c5402a9133c501b861f298da0f029d03751dc6903d11220822681378aa9d70025e5978bc435d46e000303415c6a327e1d4e7c83572cb06aec2404d29230591866cb59d8b98763be00208b3b5b99348002971b6a0de00000007c02e92a00f892f600067ba6ccf9800015d80001570001b116a46e6517e118f8c09f8aeea99ce55fed064080e7c00018e590acc5340ac8290e0f04d04a1076c5fd24e7f56a6113954093f8000ccd91c000321ae58966bf22fd8bb4cb642354caad856e8b126d00011de41569388e068a3be56d6a3961ec44a6b283cd7855b1b3800023a1e43900e150cc00000b2eeda4622b00010e965cd3642e00388ac00042205f01fb0da3c400345c28f843c9381b26270303977d310a7251f0000a90bfa000000118e1f433481d4000b6300022d08446a259915a96ae0d10d880002dccc600024880001002ba00015a87781454de55ea246cb41ee4000afc1419b4c00075428c150cb98cbe00019fcea65329560000d3c815400237190871c222035a00036c6abb575206c9823c23a40006e021c244c32aa2380022a49f400000015b8000a8a22d3308c6c00023f295d0b00004c9a47ccce00057b80009e400049e000012716f0002278a914bb0002ec8000941519aef911e54448b00000008b75428d695c05d30000000500a61000325c54c305000000193eb92555b4e40008365021e600009654d23534000c8c9fe0f792240006cb80018bc4e7523adf997ab6e110c4600930000002c5580028b1e6d732466c9c5bb04857a4335d1281a6e757595e2800141aced0d593517b69260001a3000c0003c5f0906e0d58066ae9567c52529eb1dd2f2c132913524af4b77df5a259462032571edc47100000a3ea4557a00069500003210000000000000c6f239363c000000000005000036d0b30ad38b900000000013ea0005a52dccec4d9004d6b840000006270454bf042e47d000061694e13626d56f8000578a0243d0bb054a052c0003da580aeeb666a466bd95c942064033932249228db00021091d1a2b036110ccf80004c3ac35572ba414694c0ddb29a114f6256540004ff1836000000000000132a0e748580012fc0005ac9be47d48f44804000000cb901095456580001c72da8000a79000000101484917186b40003d600030f4b6c000000107036f4971ee15f800000000025d00009d118d28be000a6209400000000003f2000111cd6d54d000034070d0000000b1a000649201f9f01f64f3002d9fa8ba31c86d80000005cfa230000b350f79c5ce44b9c5c504b08623b50000504c0f7df15a9ffca4b0000402a25778c7d1ec0744c9a87b0000185a4adae1d60ae4f243c1278284c54021e4b480015da0bd53e80005f2aca0f291356801e7326000060eb46212141d76890a18e130955891a51a90a51be3cc0002
  | 31 => 0x2c8d4f014cc3e2fd4b4a9ee6b42ee98501442aa0f8515aa1f5c711846c607a86a27d06c8c760f355dda8e18453605a83c3c03e22ee0d5be5f748ef32538427e674a4252800203f39824cb2a4323d9b111da1530e9b5195d10005ac00001fabe5347143866e00045b31ba0ba2784c2b598b580675c99f786643f4102216cac216b03687095654fb5241d04000d2d003ed549b687462890d913800051900016acda037baea000017dcce5c240ded690fe274c9ea463517a1c4ad046a12b872817c7451ac34252e264214a57413380002d20000060c635630000428cafc981dd8bfcaad000175d9c283246f0af92b09ea3fd8000db87d33772f7920e0003209f2d1925ca34ec0004c50000c921140003bd1ac875b5e900000000000000000001bac000158000091d01a2f406500001242d720d80001aeb4523e21043b000048b9c54a520000000000ebe00000033580000003598000000bca222b2690ee285b00173c0220d1b8d93256b89704dd820511247a4cd9c48bd7206355130c5f832f3bf9d1850c29836a19a13fa0d62819ba85b2cd960c93cd304c40168800154100000000001f0b3d0000b7597898b2a656ec85a7a5637152a8be1bd392000115c4996731fe00008723d52a840009f2000000014e000000161017000053d88740003a30faac8985c9550abc2c857117340c28058f02d50000888ece00017420b2af8c3083e83b4c4daf40df974445053e3eaa47485600054f000059070f00021d90a8cacebc9e584278bf19434dcf7a3eb0a00f94e76d5a6ba97e859a32604c915caaa8cd28f99251935986c722e4f00350380ac1a5920c9629305049c7c83fba8887d800000000000001ec285872ef3a1d506189d17614bf0000b180006f54d83631a9eada5fb042224c2122fb07b8220c436b383f8ba41aa0000edd5b2d7a013153c1234af239b16000096c0000431a780003d1b1c560e0000a11f2494f90812183d900e5c631f800005637c0a50001022b33d0718859541a91c50000000117000000151a59400027318d9a65639482c51c0000000001314509a992d692201eacd1b58019c5f00f4b480e6216702e0cf1134b270c34ff43480000d3465d31ec485c61e2846e3205d99c996604ff0001e1e000b66118800104ccb469a8521130dab2c88000e08d8b0000ac4ab4ac20d396e1922b0b686149ebc05126c083b900a78627897601979d968d09ecad87422f536a41584703fe8000d600005e4900830bc98eb0acac880ceb0d1b4e8ce263e6432ed860c95401f0dd830e97c2ec85345829384deb0c0314875679321c3b31c61923085947430906b40c00000000006d2bde81d0ec8e2c9d00003ad946cf680bb00013000000000000000e882ec1ffc0007a27c2000088000085e538b280cdaaeae4d9f7009444914233a1a200006cc0001256
  | 32 => 0x97a5e60aa811a53112600019904b6c28b67160094c36c9ecc92b48f62cb23063699a6b8046d1ceb4d35c945177a112081145c0468a44688d2d36216c5b4a8a025c2082962d50fb45b9024ae816a496d5d62bc0882c4c86f89517a08c52de97b8c8ec8f113b05c30c4981801778c7a1946c89389438089dfd800021eb810001b0c93c6bd34789b8000855002d9dc0001302f4144c000c3faf6b033086c62cf78afc7001552f39361b5a1d42b5a2946faca50609c44374b20070962c0c85b115d173531c6d155c06f9916d3f65420d4c4eb8724d255db2a39c6dc256c2c0152b3304a40e8db60c18acc16e3c51119a725114ab010cc207888c15491c60c68134cc691995c80705d51f8c784b0c5f323ad2968635042f00f18d180d2c2811f832929a08c91b2595246ab569da8820692d0d7b839e0003220860a150001bd9a2e08637a133799c3470000e89a28c4d3a79bbd6e43c909fa3413540083278bf4ed4ad633a0917240abc35f000000082ec88810900cbfc25baca4df4b1b227a41800012a64f23ec4ee6185b009440000004cc0000000317172d04c00000063902dac3ac1200000001724c14861bf4690c60d4f8000000b788003374000000257272d17a25ae9728e40a2c944432a4ca3ac030001cdc0000006891fcd9ec98109a29bc0001798c68e68de616d0000000e2cdb20001a98accac70000f0d03cc0511f30b0a1e6c842617f15a2a1128e0000412da436a88f4e863f22a10274e74797479b5f9ab28c23f9c1a970a04444da95812f0f94709d555742b7d7db5e1b0e090009acb51ff36f66a915560cd3019e90e5a56a602cd9eec9a4add05fa694766c090390d7960603512e92b46ca60d3b9af5119498ad2691b57461dc55aa705980cfc3102760b7800010b89322a1a6e41d89e85420005cd34ed7d07e84f417840005584e1a15d308573460058c0000003179a7d1509ec0c0d51985fcfe2d8000057000000000019c48990002e999003d1abb19f4000af9582aea4c2c59e23cb180024bdf5a1149d6300002e21cf99146a93f103638ba0004010e08c76cac000202180c416152000000086111d35dc5b80000000d75b620004c02710180c6130a9f41aa25a25b2acdeed200045603d0b7c2264d92658000c455db800077f08b000111d5d000048c2ab8f8a12500026b4a5cbf05cea22a0621464920568a723191615fc969e235ced1b243eec4257521e96884d480000012fe000391a1b08120000002248142000572b6147208b85baa4a4b868ff629800000024b25f11f4aa0c6397b2df54755ff29c000074c5c01d5359000051a18c16e97ba0000002a88000abe00000006220006519f48fac39654bb079518af2e9e80014920003f69ba4000862615b4146e9abb04e05303cc9dc3b9037192a0ad062e0e80001c584636490d2ab3316
  | 33 => 0x6c00000000003c00009c200049e800000014900000012c056411f8c100000003ca80000005ab0fd00007eeb3663f9856cba0000000d3109e0005280bfca560005bc176c000000166c000b024711fa8f740006f026883d58620000001f38f388f1272a0c027f00051a114800000313a98c43da2304a3ab1537ea15832b028df807e01caf087ae29737f29314fed1d63a98f1a645041aa00000007b74c468e0e7e00062b92801eb000688877980f0000002d444196244ea81b2beb200694257c4fe82d34283400f68b5000028c33659d20e8d345b0d340001b3510600068120707b6b046b6120c03fd5211bdfd73b6b241f705d8000d33621d94899e09f5e400003500000000bd48a244c0003008000ccb000156451e000471a74800000013b75ad6c800000006e0e3ed8d1a5076c3e2093000092e8647b54269e911d400023b8fe51a826d000075722aa8400005a07ce4623ae9865820cb202a1c1499c31e3cd881cc285853c59a82b2035b5eaa210f0d4061dc1b687684e91e42bb0e7a7a00000000e4ac6ab50b0db5d2cf0052134ca772ee0110364d6e1c316a30fb9022660fe5e0473a896de048830583c611e11ac70cb190270ece2f4da10000d3800000056991d0fec2d60e8006967ea9e80017faafe00020a04c830049b2339d8424010e4db800092c5492449a957f20004290715070b1457f1d5c000c99588a168eea00000018a0000c261d00000fe222935698a8ca2cfb573efb0000000579ab715fa13812800003a10005b380013bc06927a1c406d675e0002584be913b93485c011000031d02616fe68700034e18e045c55924c8ba82fb61e2fb472688704873b807039102995715f4c5b3c6b236e0050108f8b80d0c00244e91945b63a4307a33c0001a200013dd80500056586c15c6d6500001642a844a09c894d44820e26824151780974c4a8d9228219088adb409e9522f8a89da101f352c80016981ce18527215dc37130d32747b279a667a8658441f067a17719ca3fe1882d4c05e3441f9800179e1e3e778b90322d153e03234d2eb1657750203160000a5d8d426600050e80003d10006ca2f620ec000258a7fc2b886f0000789b601085e6981416c273000000172231f0a8973846c0004d714d44a422cac730d8cb843c6a8000097474b6701b4890a75c3741d0083c3d45fe83941983d509b91740f808300f1fc0ec60f3181889aeaf7f414600004f88da0001fd395e5b52bc19208d085022419d850f38f0b0587184e5003ec044c4920a80bc0be14bcaa38e0c84c46aacd3c803c72a029d4711b88a1037538419282c41090aca05d54d878190b6017a200026392175eccae31b8fe1034803097de781cdd5637fae212727db457800045f9cd3a897880004c3a4090340002996da0060602be22844001894a261b4969c06804c5791ca800
  | 34 => 0x52080556d87b0000b42d52c2670978710b10d1f3bd0dceabe24f4f00c382381190d245ec5648d3527b20c15658905a08a897027d037031c6127305c79c1927eaa6552ea8c395bd3649af912c818c0451c28946dbb22123e417860127e951edae58716d0e11a9627ce5b2ee03d6bb506aa44e1e2b9e0239670cfc000654a9f217540a356052359d2bc1e9000056c83710532760002c00000159a620fb32f8da707200005653aa9513e91b0000110a7664eb0cad1884253838ce41f4cea648166436e42a000224cd14ab48001980000c850001a632fa0505b59cc9028ad220727e819e6950000000b240a233d8000ea48292f2ab059a469b5aeb0d556d40101694d83f26136b70000f22c4b2f5a80135254c123294c96c60a6dc99b0c16d9d00009056d0000000273814c19c411800077238c446b2ae6cc48e8cc85152436ab54eb6a90d092c198a8c09cc5715a39156be60005bdb02d77eb9b000000000000009680000000005369f6400000016285031e40000002fb800074d107b53960421f55280018d70c442e8000ef60003590001809a25dba000048f00000000000008600000000f0eb824878000000da54109fbc000cc53632aa8a4206236381e40df1b2da70ce0eca2bd56a8be800092e65d8c344422cc019b688ff47994a366e0994a872d7991423c5e926e0cc0fef56f4a18908c6020158fb3110627d73d40808a171771d8a391454192a5384180148a62da072540a650302369d4d200003594bc7de091000000032c2604a531d16c201694e24d000071a1c097258720003a48c9512817425500b1b1460261f335c7cc22d47b93545e661014b032a2fc99200031a0d2882b2ed0d5555ec50631102cb5a3d00000000f585101a1a8ba7566cf1951de5a3662d0fea0a065c93b4e3ac78550b1051fb4891d300002fb3314f82d08c7d478000240000167ce9c6292751ef905c8460e38f1c00000033c0c4c7425fd39600019a81af00000000008f634cb50ceb09d01b0a524ffc9350ff22c93e2ba7346a10125002e54413ac00057b262a7280002182590dfc4c600f1f244f325e2eb44031040906e404cce0d5ce6925481b8c67694633732915680524099cb4a6632d0b90fecd5e3b4a1d800054eb374f08000a9a8223bf29d0008cb10001d303e49e436f916183e7ad687232cf642f026f99698764fe5779e11a580001e24fb549c3360001a6007a84e15
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x401c25641907154c2164551a4c641c55308401545931907154c2100558a40641c55308401561901907154c2164551e59631c55308581c479658c7154c2182d51e4d801c55308401465962007154c2100549a50801c55308401525942007154c2164d5164c801c5530859154693d807154c210055164f601c55308401c4563d807154c210071158d601c55308401166981807154c2100459660601c55308401526941807154c2100549650601c55308591546931807154c210055164c601c55308401c61601807154c2100459a60401c55308401165981007154c2100519a58401c55308401465961007154c2164551a4c401c55308401545931007154c2182e51e0c715c15308401866861c47054c21006c110c815d54308401c0d6458d7550c210065198c815d54308401945632057550c210045924585dc1430860916691e11739442160651a0563dd6310840116691a1d548c4210ec4b26174552310860592674205548c42160459a47855c23108401866810877558a300050764c85dd1618c00181f7460f54586308168921051584218c00181c6460c715513081d46652751c1434c0018667220554d85300052364a7650e414c001a276420554085308168919081550214c0012679855361085300059164c51184214c001cc1735c061085300050d650759863188001435941d5618c620006076117318f654800181d845cc73d952000525650631c56348001455932147158d20006071d1831456348001855831c45158d2000619a04219d9534800144d93a087654d200051364c211d9534800148d9210e7650d2000427660431d9434800148d9210c7650d200048766043d95434800160d9210f6550d200058365063d95324800528c98591434c9200152325d6450d324800168491591434c9200055164c511c53248191c4463144714c9200ee131c9831d4614800103d9421d531852001c172617354c614800103d94a1f658c5200059164c85186214800705e97e0d6454e1000619988815d5438400160d9210d6550e1000623611731cd628400188d8750c4358a100051564e651c5328400103f9461d63946100050b6507558a318400188f7460a74d8d1000523648439d9434400148d9210c7650d1000525a44431d943440014999010c7650d100058364843d95434400188e8750c43d89100040fa6075d92314400141d941d7638c5100050b65075d8a31440532549660f758c510605912446518c214400164696144630851000781d905118c2144001e04641446308510604992448654c2144001a27642055308510006891908154c2144001a476320553085106469118c8154c21440018668108775588106469198c8154c2104001c5376dce514401000718ddb729451004001c6376946214401000718ddb7588510041619c2871ce2144010
  | 1 => 0x301c1764e87d006154c0126491608401855300499249811006154d81a468308720185530069160c21c806154cc311d98dd3735954300447a60431c56550e0f81d8610c715954300543648431c56550c015169110c715954300519245721c96550c01468905c8725954300519249311c56550c01855831c421595430051a249701c16550c01470915c070595430041d245870816550c0111e9810d75d894300543648435d76250c018648108575d894300543648435d76150c0118d9810d72d85430054364843dd56150c0186472205655854300463a6043dc96150c015899210f70585430051664e651c16150c0147091594705854300706594431c16150c015899210c705854300447a60435d46150c0150d9210d751854300447a60435d76050c0150d9210d75d814300543648435d46050c0118d9810d721814300561648439c46050c0145593995711814300705594435c46050c015859210d711814300564640435c46050c5fa0c86615435093230f031d98550d424c991a476260c51185320049564c81550614c83988c8750d42185320068590d84144614c8012579460c511853200691e4983144614c801a449260c511853264691dc983144614c991a447260c51185320069190983144614c801a472060c51185320049566143144614c9914649750851185320068961142144614c801a458350851185320078150d42144614c80103f985d07458e5100607dd183d05639440181f7460c4058e510060ddd181101639440121d9810e7650e5100583648439d9439440121e9810d7650e5100583648435d9439440105e980c57650e5114e4321d43509329440103f985d074d963100417662431d9548c40103e981d9645523100607991831c5548c40160d929936550e310060d9c584197628c581866810877558a310050d65065dc5428c401435941947150a310060d9c584196608c40182d849c865982310050b650655ca608c40188f7460e74d89310049325983d50624c40143594194715093101c1764f87d92514c40144d931d76290531646159c583147638840528e98d91434ca2101523a5f6450d3288401945839c451d8e216071198e71147638844328d98d936350e212e623a1f64d8d4388401a8764a076350e210f44b2617455231884018698761760982210051a65c51d82608840160d9210f6550d210055164f411c55308401925841047154c2100459662741c5530860d545939d07154c2100711dd9631c5530840154593a187154c2100549a50861c55308401525942187154c2164d5164c861c55308401562902187154c2100558640861c5530859354593e107154c2164551a4e841c5530860d54593a107154c2100649610841c5530859154693d907154c210055164f641c55308401166981907154c2100459660641c55308
  | 2 => 0x1c87d8c610a2e000004436db0001eb80000009000ee00468353a000037c6a070000160eb05c016e003996cbe0000000442167c01aa03672f4d69a466d00000001d13e945daf00000161c9c42d1c259040066311824146c00007873a600000182119680539332b004999000a20030db9d910131ca312680076000000000d2000e800004ba25d8b6000008cda0014a000036800000a3d800fa000009000002e971320000000000050b20000000324000400068e000001c4c0007501400aa00000a7000003600d300241d0f03e00000000700116000823db8b324b5c4751190000083624002e4a000003a0000244260000078a47a15b08002900000000000000b0951b000c64f1e1a174197095d9454002c5baa540ba4a60022988000015c013600562a40016732d40050378002a000000000000000000550000000000008c0000000001ec0002910c3400198000c00194f2d6439111400349fda21176a808e3f5f2fd4c0057b90b49e041b86e6c4299c00a3d6b02382a81100fc2f0033cd40077801dcd415315564b2428cec010000000cd000cd4d262b0004a00001788600490013800000b800a8719380000001d47cb90000000001409c0004ac80016c74600000d048c19bc092123800b257000301b000000000010060600018060c030000003008000403000000e0000810020e028000401050000402000100401000280800040000a03000001204080001201020000000000042006008000402010000200000300207010000208038080400020040c0000000014649259071589530069160c620846154c0142d9210d74185530040fe61741d06154c0705d93a1f421855360591a4c420846154c0164593108211855
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1200028c5200007046004c000000000800600058001e68e8824010c00c9000121250b2421ae830aa600c036199210c7159543004a0942c908638acaa180340965648431c16150c012c050b24218e0b0a8600d015959210d7118143006822cac8086b88c0a1802a05a424983144614c9918224bb06a10a230a6400a816a14350851185326468092ea1a84288c29900342164640641c55308401830cc2c0300e2a984200d08651601807154c2100688326b00c038aa610802a05a610c815d54308401c02b22c640aeaa18420091129993144714c920
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x810000006401652859210c7058543006004976a1435085118532004405b429993144714c920
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
  | 8 => 0x138e
  | 9 => 0x94b
  | 10 => 0x94c
  | 11 => 0x94e
  | 12 => 0x124b
  | 13 => 0x124c
  | 14 => 0x124e
  | 15 => 0x138b
  | 16 => 0x138c
  | 17 => 0x98c
  | 18 => 0x98e
  | 19 => 0x128c
  | 20 => 0x128e
  | 21 => 0x9cb
  | 22 => 0x9cd
  | 23 => 0x9ce
  | 24 => 0x5
  | 25 => 0x12cb
  | 26 => 0x12cd
  | 27 => 0x12ce
  | 28 => 0x20c
  | 29 => 0x20e
  | 30 => 0x140e
  | 31 => 0xb0c
  | 32 => 0xb0e
  | 33 => 0x140c
  | 34 => 0xb4b
  | 35 => 0xb4d
  | 36 => 0xb4e
  | 37 => 0x144b
  | 38 => 0x144d
  | 39 => 0x144e
  | 40 => 0x14cb
  | 41 => 0x14cc
  | 42 => 0xccd
  | 43 => 0xcce
  | 44 => 0xe8b
  | 45 => 0xe8e
  | 46 => 0xecb
  | 47 => 0xecd
  | 48 => 0x94056
  | 49 => 0x95396
  | 50 => 0x209
  | 51 => 0x20054
  | 52 => 0x20056
  | 53 => 0x1409
  | 54 => 0x140056
  | 55 => 0x141396
  | 56 => 0x14c9
  | 57 => 0x2c9
  | 58 => 0xec9
  | 59 => 0x1a49
  | 60 => 0x138956
  | 61 => 0x20956
  | 62 => 0x95416
  | 63 => 0x140956
  | 64 => 0xb4956
  | 65 => 0x1449
  | 66 => 0x144956
  | 67 => 0x249
  | 68 => 0x94d
  | 69 => 0x139256
  | 70 => 0x21254
  | 71 => 0x21256
  | 72 => 0x141256
  | 73 => 0x21396
  | 74 => 0xb5396
  | 75 => 0x145396
  | 76 => 0x140996
  | 77 => 0x99416
  | 78 => 0x2cb
  | 79 => 0xcc996
  | 80 => 0x98cd6
  | 81 => 0x1a4b
  | 82 => 0x168b
  | 83 => 0x98d
  | 84 => 0x1649
  | 85 => 0x134b
  | 86 => 0x14b
  | 87 => 0x141296
  | 88 => 0xa0c
  | 89 => 0x209d6
  | 90 => 0x20d
  | 91 => 0x1409d6
  | 92 => 0x140d
  | 93 => 0x2cc
  | 94 => 0x14cd
  | 95 => 0x150c
  | 96 => 0xe89d6
  | 97 => 0x104c
  | 98 => 0x1049
  | 99 => 0x104b
  | 100 => 0x1a8c
  | 101 => 0x180c
  | 102 => 0x130c
  | 103 => 0x212d6
  | 104 => 0x1412d6
  | 105 => 0x1452d6
  | 106 => 0x1a89
  | 107 => 0xb4215
  | 108 => 0xb4216
  | 109 => 0x16cb
  | 110 => 0x20b56
  | 111 => 0x144215
  | 112 => 0x144216
  | 113 => 0x24b
  | 114 => 0x21456
  | 115 => 0x14c214
  | 116 => 0xe8216
  | 117 => 0x18cb
  | 118 => 0x20e96
  | 119 => 0xec215
  | 120 => 0x140b16
  | 121 => 0x154e
  | 122 => 0xb5416
  | 123 => 0x140b56
  | 124 => 0x145416
  | 125 => 0x141456
  | 126 => 0x14d414
  | 127 => 0xe9416
  | 128 => 0x140e96
  | 129 => 0xed415
  | 130 => 0xcd416
  | 131 => 0x140cd6
  | 132 => 0x144b56
  | 133 => 0xb8b
  | 134 => 0xb8e
  | 135 => 0xb8c
  | 136 => 0x148b
  | 137 => 0x148e
  | 138 => 0x28c
  | 139 => 0x16ce
  | 140 => 0xd0e
  | 141 => 0x154c
  | 142 => 0x184c
  | 143 => 0x148c
  | 144 => 0xe9456
  | 145 => 0x24e
  | 146 => 0xd0cd6
  | 147 => 0xd0c
  | 148 => 0xe8cd6
  | 149 => 0x1a8b
  | 150 => 0x188c
  | 151 => 0x178b
  | 152 => 0x160c
  | 153 => 0x10c
  | 154 => 0x16cd
  | 155 => 0x1a4d
  | 156 => 0x14c
  | 157 => 0xce
  | 158 => 0x198c
  | 159 => 0xa4c
  | 160 => 0x134c
  | 161 => 0x168e
  | 162 => 0x19cc
  | 163 => 0xbcc
  | 164 => 0xd4c
  | 165 => 0x15ce
  | 166 => 0x1a0c
  | 167 => 0x170e
  | 168 => 0x18ce
  | 169 => 0x194c
  | 170 => 0x178e
  | 171 => 0x74c
  | 172 => 0x1409405e
  | 173 => 0x5256
  | 174 => 0x213895e
  | 175 => 0x942d3
  | 176 => 0x24211
  | 177 => 0x94216
  | 178 => 0x289
  | 179 => 0x1489
  | 180 => 0x2c953
  | 181 => 0x2cd
  | 182 => 0x95456
  | 183 => 0x125396
  | 184 => 0x1382d3
  | 185 => 0x2d393
  | 186 => 0x98216
  | 187 => 0x449
  | 188 => 0x995d6
  | 189 => 0x4214
  | 190 => 0x124214
  | 191 => 0x131054
  | 192 => 0x202d4
  | 193 => 0x105414
  | 194 => 0x214d4
  | 195 => 0x138216
  | 196 => 0x20256
  | 197 => 0x104214
  | 198 => 0x21054
  | 199 => 0x21a55
  | 200 => 0x2c214
  | 201 => 0x24216
  | 202 => 0x219d4
  | 203 => 0x2d414
  | 204 => 0x19c214
  | 205 => 0x16c216
  | 206 => 0x218d6
  | 207 => 0x1a9414
  | 208 => 0x1a8214
  | 209 => 0x2d554
  | 210 => 0x2d6d3
  | 211 => 0x1402d4
  | 212 => 0x1414d4
  | 213 => 0x140256
  | 214 => 0x141a55
  | 215 => 0x140ed5
  | 216 => 0x1418d6
  | 217 => 0x21414
  | 218 => 0x1415d6
  | 219 => 0x2c253
  | 220 => 0x20b94
  | 221 => 0x141054
  | 222 => 0x141a94
  | 223 => 0x184e
  | 224 => 0xb9054
  | 225 => 0x2d4d4
  | 226 => 0x24b56
  | 227 => 0x1542d4
  | 228 => 0x155396
  | 229 => 0x124056
  | 230 => 0xb0216
  | 231 => 0x28e
  | 232 => 0xb4256
  | 233 => 0x154256
  | 234 => 0xe8d0cde
  | 235 => 0x104114
  | 236 => 0xced5
  | 237 => 0x105314
  | 238 => 0x12ced5
  | 239 => 0x104b94
  | 240 => 0xb4ed5
  | 241 => 0x105854
  | 242 => 0x16ced5
  | 243 => 0x1a4ed5
  | 244 => 0xd2d6
  | 245 => 0x1692d6
  | 246 => 0x252d6
  | 247 => 0x1689d6
  | 248 => 0x1789d6
  | 249 => 0x24e96
  | 250 => 0x25456
  | 251 => 0x16d456
  | 252 => 0x179456
  | 253 => 0x16cb56
  | 254 => 0x144e96
  | 255 => 0x1715d6
  | 256 => 0x18d796
  | 257 => 0x178cd6
  | 258 => 0x2c215
  | 259 => 0x11054
  | 260 => 0x20296
  | 261 => 0x24212de
  | 262 => 0x2420e9e
  | 263 => 0x58e96
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 49
  | 7 => 1302
  | 6 => 5171
  | 5 => 3517
  | 4 => 241
  | 3 => 18
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
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1428+((h/22+packedAt gbK8 (1274+(h % 22)*7) 7) % 82)*7) 7
  | 7 => packedAt gbK7 (54158+((h/544+packedAt gbK7 (48174+(h % 544)*11) 11) % 1959)*12) 12
  | 6 => packedAt gbK6 (274234+((h/2002+packedAt gbK6 (248208+(h % 2002)*13) 13) % 7208)*14) 14
  | 5 => packedAt gbK5 (224455+((h/1304+packedAt gbK5 (207503+(h % 1304)*13) 13) % 4696)*13) 13
  | 4 => packedAt gbK4 (17644+((h/86+packedAt gbK4 (16870+(h % 86)*9) 9) % 415)*9) 9
  | 3 => packedAt gbK3 (1494+((h/6+packedAt gbK3 (1458+(h % 6)*6) 6) % 34)*6) 6
  | 2 => packedAt gbK2 (279+((h/1+packedAt gbK2 (276+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7f01ff01ff81fffffc0fffffd13e7e3a23f1ff
  | 1 => 0xfffe0ffe0ffe07807ff03c03eec993fddcce67
  | 2 => 0x81fff0000ffff8007fffc003f0f1e3c61f0f87
  | 3 => 0x1fffffff00000007ffffffc3f01fc07e00ff8
  | 4 => 0x1ffffffffffffff800000003ffe0007fff000
  | 5 => 0xfe00000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x12001100118088a30c04451a401226180150ab
  | 1 => 0xe416076206a2050535102828864890e8ccc665
  | 2 => 0x11ab70108b55d00a5aae805330b16346170b86
  | 3 => 0x21cdaab5a010401063cb32e03b01d807600d50
  | 4 => 0x41f1ccd9cc79665c008200803dec0007baa000
  | 5 => 0x788100e100618460030c23023fffffb0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeac8eeeaea80eeeaeac8eeeaea80eeeaeac8eeeaea80eeeaeac8eeeaea80eeeaeac8eeeaea80eeeaeac8eeeaea80eeeaeac8eeeaea80eeeaeac8eeeaea80, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36669
namespace PEqualNP.Outside.L_meta_36669
open PEqualNP.Outside.L_meta_36669.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_1_0 : Interval s1Atlas 1 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_1 : Interval s1Atlas 1 0 1 := bs1_1_0
theorem alls1 : ∀ k ≤ 1, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_1 i (by omega) hi
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
theorem bs3_2_0 : Interval s3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 3 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 21 := bs3_3_0
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
theorem bs3_4_96 : Interval s3Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 99 := (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 46 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_2_0 : Interval s4Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 3 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 21 := bs4_3_0
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
theorem bs4_4_96 : Interval s4Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 99 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 46 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 13 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 11 := block_range (n:=11) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 75 := (concat bs5_3_0 (concat bs5_3_32 bs5_3_64))
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
theorem bs5_4_512 : Interval s5Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_544 : Interval s5Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_608 : Interval s5Atlas 4 608 18 := block_range (n:=18) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 626 := (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128))) (concat (concat bs5_4_160 bs5_4_192) (concat bs5_4_224 (concat bs5_4_256 bs5_4_288)))) (concat (concat (concat bs5_4_320 bs5_4_352) (concat bs5_4_384 (concat bs5_4_416 bs5_4_448))) (concat (concat bs5_4_480 bs5_4_512) (concat bs5_4_544 (concat bs5_4_576 bs5_4_608)))))
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
theorem bs5_5_640 : Interval s5Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 699 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 (concat bs5_5_192 bs5_5_224)) (concat bs5_5_256 (concat bs5_5_288 bs5_5_320)))) (concat (concat (concat bs5_5_352 bs5_5_384) (concat bs5_5_416 (concat bs5_5_448 bs5_5_480))) (concat (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)) (concat bs5_5_608 (concat bs5_5_640 bs5_5_672)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 42 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 18 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_128 : Interval gbAtlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_160 : Interval gbAtlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_224 : Interval gbAtlas 4 224 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 241 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224)))
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
theorem bgb_5_2560 : Interval gbAtlas 5 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2592 : Interval gbAtlas 5 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2624 : Interval gbAtlas 5 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2656 : Interval gbAtlas 5 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2688 : Interval gbAtlas 5 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2720 : Interval gbAtlas 5 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2752 : Interval gbAtlas 5 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2816 : Interval gbAtlas 5 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2848 : Interval gbAtlas 5 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2880 : Interval gbAtlas 5 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2912 : Interval gbAtlas 5 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2944 : Interval gbAtlas 5 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2976 : Interval gbAtlas 5 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3008 : Interval gbAtlas 5 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3040 : Interval gbAtlas 5 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3072 : Interval gbAtlas 5 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3104 : Interval gbAtlas 5 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3136 : Interval gbAtlas 5 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3168 : Interval gbAtlas 5 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3200 : Interval gbAtlas 5 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3232 : Interval gbAtlas 5 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3264 : Interval gbAtlas 5 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3296 : Interval gbAtlas 5 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3328 : Interval gbAtlas 5 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3360 : Interval gbAtlas 5 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3392 : Interval gbAtlas 5 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3424 : Interval gbAtlas 5 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3456 : Interval gbAtlas 5 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3488 : Interval gbAtlas 5 3488 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3517 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608))) (concat (concat bgb_5_640 (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832))))) (concat (concat (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 bgb_5_1056))) (concat (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)) (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)))) (concat (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 bgb_5_1504))) (concat (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600)) (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 bgb_5_1728)))))) (concat (concat (concat (concat (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824)) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920))) (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat (concat bgb_5_2048 bgb_5_2080) (concat bgb_5_2112 bgb_5_2144)))) (concat (concat (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240)) (concat (concat bgb_5_2272 bgb_5_2304) (concat bgb_5_2336 bgb_5_2368))) (concat (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)) (concat (concat bgb_5_2496 bgb_5_2528) (concat bgb_5_2560 bgb_5_2592))))) (concat (concat (concat (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688)) (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 bgb_5_2816))) (concat (concat bgb_5_2848 (concat bgb_5_2880 bgb_5_2912)) (concat (concat bgb_5_2944 bgb_5_2976) (concat bgb_5_3008 bgb_5_3040)))) (concat (concat (concat bgb_5_3072 (concat bgb_5_3104 bgb_5_3136)) (concat (concat bgb_5_3168 bgb_5_3200) (concat bgb_5_3232 bgb_5_3264))) (concat (concat bgb_5_3296 (concat bgb_5_3328 bgb_5_3360)) (concat (concat bgb_5_3392 bgb_5_3424) (concat bgb_5_3456 bgb_5_3488)))))))
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
theorem bgb_6_5152 : Interval gbAtlas 6 5152 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5171 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 (concat bgb_6_576 bgb_6_608))))) (concat (concat (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 (concat bgb_6_736 bgb_6_768))) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)))) (concat (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)))))) (concat (concat (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408))) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568)))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728))) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))))) (concat (concat (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)))) (concat (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368))) (concat (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464)) (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560))))))) (concat (concat (concat (concat (concat (concat bgb_6_2592 bgb_6_2624) (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720))) (concat (concat bgb_6_2752 bgb_6_2784) (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880)))) (concat (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040))) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200))))) (concat (concat (concat (concat bgb_6_3232 bgb_6_3264) (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360))) (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520)))) (concat (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680))) (concat (concat bgb_6_3712 bgb_6_3744) (concat bgb_6_3776 (concat bgb_6_3808 bgb_6_3840)))))) (concat (concat (concat (concat (concat bgb_6_3872 bgb_6_3904) (concat bgb_6_3936 (concat bgb_6_3968 bgb_6_4000))) (concat (concat bgb_6_4032 bgb_6_4064) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160)))) (concat (concat (concat bgb_6_4192 bgb_6_4224) (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320))) (concat (concat bgb_6_4352 bgb_6_4384) (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480))))) (concat (concat (concat (concat bgb_6_4512 bgb_6_4544) (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640))) (concat (concat bgb_6_4672 bgb_6_4704) (concat bgb_6_4736 (concat bgb_6_4768 bgb_6_4800)))) (concat (concat (concat bgb_6_4832 bgb_6_4864) (concat bgb_6_4896 (concat bgb_6_4928 bgb_6_4960))) (concat (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056)) (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152))))))))
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
theorem bgb_7_1280 : Interval gbAtlas 7 1280 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1302 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 (concat bgb_7_576 bgb_7_608))))) (concat (concat (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 (concat bgb_7_736 bgb_7_768))) (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)))) (concat (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat bgb_7_1216 (concat bgb_7_1248 bgb_7_1280))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 49 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 2 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeac8eeeaea80eeeaeac8eeeaea80eeeaeac8eeeaea80eeeaeac8eeeaea80eeeaeac8eeeaea80eeeaeac8eeeaea80eeeaeac8eeeaea80eeeaeac8eeeaea80
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 38 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372936 * 2 ^ 32 + 4008372864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36669.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,2]⟩,⟨.or,[5,6]⟩,⟨.and,[1,7]⟩,⟨.or,[4,8]⟩,⟨.or,[2,4]⟩,⟨.or,[3,9]⟩,⟨.or,[2,3]⟩,⟨.and,[1,12]⟩,⟨.and,[10,13]⟩,⟨.or,[0,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 4008372864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 4008372864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36669

open PEqualNP.Outside.L_meta_36669 in
theorem PEqualNP.Outside.L_meta_36669 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372936 * 2 ^ 32 + 4008372864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372936 * 2 ^ 32 + 4008372864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
