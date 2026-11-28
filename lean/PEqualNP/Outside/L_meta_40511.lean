import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40511.Model
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


end PEqualNP.Outside.L_meta_40511.Model

namespace PEqualNP.Outside.L_meta_40511
open PEqualNP.Outside.L_meta_40511.Model
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

def SBf (j : Nat) : Nat := [7, 5, 7, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_40511

namespace PEqualNP.Outside.L_meta_40511
open PEqualNP.Outside.L_meta_40511.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x10cc0010c000104a0c97810c50800011800c8fc41fd40fe43fc31fd10fd32fc32fe32fd42fc10fe42fe10fd21fd41fc21ff42bc40bd43fe30fe40ff31fc30fc42fe20fe41ff10fd20ff43fe21ff32fe31be40ff20fd31bf43ff21ff40fc43ff30fd30fc20fd43ff41fc40
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1003800716300081200d002000180005c1912428a85000850000000044000000000400444d50c80200089004c000020020e013d53102bea6884f553329f2a0615e53d067ea890dd946329eaa0637b504877080186750c31da28a873e50d0eb8a6906750e31cf29881e521086bea6904fd5130af2988178504867aa9986e14143ba28a413d54c827ca818cfd51109e2a2211d531027aa8185b54a31b7a92613f54482dca518cf550329f2a6413f548c27ca9995b94810ba28a876c52442bca7a14f55243bc2828775518cb5ea4a1db54810b6292613c54482baa7a14f95330cea1a619d438ca7aa998edd45439e2a24377514833ea6a1dd94420afa9a437551082eea2a1eb14943ba28a615d53d0678a9185bd4943bda82879d43cc376a0a1e754c409f2a0873e54cc6b8a690e750c32aea98813d539027ca0205714d109f28481ba501027ca9884f141439f2a0653d54c437081985dd4530b7a9221385050e78a8985b14943
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xa15880014430100032f2b5214143a6181430c6986050c32a6181438ca986050e31c3189531021c6550d30c550c514c2996310330cc1445050f0f6254c40b818121087146154c40ccd445050f0d4314930c91485150f0d4394a31c550e518cb176154c40ca1485050e1d63953108758e54c83186054c40a618143cc2396510030
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x400005811886154c40a10e0a1ca518d107050e518cb04310c0a9881841846054c40
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => 2*((h/28+packedAt s0K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/58+packedAt s0K4 (2457+(h % 58)*7) 7) % 91)
  | 3 => 2*((h/15+packedAt s0K3 (950+(h % 15)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s0K2 (245+(h % 8)*3) 3) % 5)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffffffc07ffff03fffffffff01ffe3ffe3f
  | 2 => 0x3fff01fffff80ffffc0fff01ffffe07fcf1fc7
  | 3 => 0xc07ffe03fffff01ffff03ffe03ffff81f3e3f8
  | 4 => 0xff800003ffffffffffffc00003fffffffc03ff
  | 5 => 0xfffffffc0000001ffffffffffc000001fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x429114288471224500b2cb4a94b08aaa156e1b
  | 2 => 0x13224c514890e48b2c0555295956a24ccb16c5
  | 3 => 0xb244289a512241d3555026ac526ad30963a368
  | 4 => 0x2470b163a244891c9a6980c1838d1c71bc01b6
  | 5 => 0x3878c183c3870e1ee38e38f1e00e1861fed800
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000fcc0ccc0fcc00000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40511
namespace PEqualNP.Outside.L_meta_40511
open PEqualNP.Outside.L_meta_40511.Model
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
  | 4 => 2*((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/1+packedAt s1K3 (16+(h % 1)*1) 1) % 1)
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
end PEqualNP.Outside.L_meta_40511
namespace PEqualNP.Outside.L_meta_40511
open PEqualNP.Outside.L_meta_40511.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x1800800070011424c30010007d6984300ff21ff30dc31ff41ff42ff31de43fd42ff10ff20fe40de31fe30fc32fd30fe21fd40fe20fe42fc30fc41ee21fc43ff43fc21fe43fd21fd43dd43fc40fd41fd31fc10ff40fd32fc31fe32fc20fe31fe10fe41fd10fc42ff32ec21fd20
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x51808202a80820532000007c7000c0001b840000900000210106780050054002000070300000042c000840c0470201cc31886d8a4885794431b6a94215f53486baa6105714d20f3208435f53506baa918dbd4941b6a90819e540c67ea89057d5031af298833c544823aa818d7d5231f2a0843d6510c6eea2905794f40e7188439d43102dca598f10c421af28c876e528433ea8a1e750e40bb288815d540c6e8a29957946319f2a6615d53842b8a2a1f908610e618843d4310867ca818d794f41b7288436c52506dca4205794c439e2a2216d52d07cca210d754c41aea9e857551d0abca790d794c42e7218436f52442dea498d794c40aea98859d540c6bca6105794f42b729061cd43886dca5a0cfd5110b728c433d54cc3ce6210de14141b6292635c53487a86390dd14520e721c437551103c84208790c421cea1a836d52cc6b8a6885755243aea9e815d53c86baa6206750f41bb28e85cd43086bca7084f55031bda82835f53442baa7a0ddd4532afa9a41ce31886daa4185714d41
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x14050140119020102c46150c21a359031086c5640c42187592538421d6595031b1d90310868d640c621a959031086646154830b19863108685640c421c650c50506c46350421e159031087854350421a559031c8695640c421e199031087154354440b818141087465308610
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x681431814108682ba4a610c21215da640c421
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | 2 => packedAt s2K2 (i*49) 49
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/22+packedAt s2K5 (736+(h % 22)*6) 6) % 46)
  | 4 => 2*((h/54+packedAt s2K4 (2673+(h % 54)*7) 7) % 99)
  | 3 => 2*((h/14+packedAt s2K3 (798+(h % 14)*5) 5) % 21)
  | 2 => 2*((h/15+packedAt s2K2 (147+(h % 15)*2) 2) % 3)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xe07fffffe03fff81fffff07ffffe07fcf8fe3f
  | 1 => 0xff80fe07fffffffe0f81ff83c07fffff2733ff
  | 3 => 0xffff0007ffc0fffff001fffc007ff83fc7c3c7
  | 4 => 0x7ffff03fffffe0000007fffc3f803f8
  | 5 => 0xfffffff8000003ffffffffffff800003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x230a144023820880318a30144716426448561b
  | 1 => 0x4526288a4494511606a0d482892a8c892330ed
  | 3 => 0x8a144d54890ea2aad0496958124d5232c5c346
  | 4 => 0x1c58b1e712283bcd6b6c0c522471e723f803b0
  | 5 => 0x1060c1861c30c3718c718e6338018403b6a800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaacc888800eeaaeeaacc888800eeaaeeaacc888800eeaaeeaacc888800eeaaeeaacc888800eeaaeeaacc888800eeaaeeaacc888800eeaaeeaacc888800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40511
namespace PEqualNP.Outside.L_meta_40511
open PEqualNP.Outside.L_meta_40511.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x8300030000f0000c4a41003181282500381480147fc30ff42fe21fc32fe32fe43fc40ff10fd42ff40fd30ff32ff43fe41dd43fc31fe31ff21ff41fc41fd32fe42de43ff20fc10fd41fd31fd10fd20de31fe10dc31ff31fc21ff30fc43fd43fd40fc42fe30fc20fe20fd21fe40
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x130614011060419214140010200e1a120440d1e0028b101c0022400400000038052000054e000000430088000278a8905754f41ba28a87d4310873ca818d794c43ea18e435d548c6bca6105754c20bb28c615e510c6bca321e750d42af29c2175510833ea8a1cf550319faa2413e54cc2bea6885714d209f2a0653d54c87a8a2a1e750f42ae29a83d6510c6e8a2905dd4532afa9a433e54082bca6205754f42af29e856d52102baa70857550319faa221d4410c6bea818d714543aa28a875e53d033a86205d544409e2a2216d52d06eaa3a15754f219eaa6617651d0a7ca990d754c42afaa4637651082eaa3185794c418eaa0637751482b8a6885794c42bb2888174514cb3a86a0d754c40ea18e21d4314433a87205b94840bba8a875e53c86d8a48875d0431aea9e815e53d06b8a690cf55020ceaa0635d531073a87a0db94b41afa9a416f52442bea6a0cf55032eba8a873e540c6baa921d794631
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x7143318200014000008938006102c662d043187590534870d43548409518553d0295640c71087596540c716540c72195594410c6946150c40875925384344520c510c51503144295640c721951855310a95640c421a559031442946150e40c350d52d06946150f41c550d51d0a946150d42c5185540c71554d0431c550d51102946150f42
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x28238a86a9081411c54354b41c0ac8290628841576150314420abb4a818e438155262d0431
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
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s3K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/51+packedAt s3K4 (2430+(h % 51)*7) 7) % 90)
  | 3 => 2*((h/22+packedAt s3K3 (950+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/16+packedAt s3K2 (294+(h % 16)*3) 3) % 6)
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
end PEqualNP.Outside.L_meta_40511
namespace PEqualNP.Outside.L_meta_40511
open PEqualNP.Outside.L_meta_40511.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x5c0003a8000110000100659f0400000400082536420c2040500ff30fe42fe40fc40fe20fd30df32fe10ff43fe21fc20de31fd40fd41dd32ff40fd21fd20fc10fc30ff31ff42fc41dc31fc31fc21fd10ff32fc42fe30fd43fd42fe32fe43fe41fd32fc32fe31ff20fd31ff21fc43ff10ff41
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xacd0268f0256ec3040e0c9000a14c0c006408604022831e5f9aa418d794431ea18e215c53886baa7195b548409eaa041755190abca7905b14910afa9a815e53102baa610d754831af298655d53c82daa418dbd4940ae29a215c53506b8a2994fd5110aea98856d5210eeea2a05794c20bb288415e53087aca218d754e42af29c21cf524cabaa7085794e42e699441d431c86bca3994f95020bba8a875e518c7a88218d7d4d10ba28a815d53d079a6590dd54630b7290636d52d06eca318750c510ea188435f53887aea2995794f41b62928175511039ca418dbd4910e699041cd32486daa5985514532aea9e4374514cadca421f3909329f2a6435e53c8678a8885b94840b72966177514cba8a2995d544209eaa6435d53082b8a6a07350932eba08636e52d06eca3215d14543ae29a435e5310a9aa418dd94440aea94635f53486bea6a0d754c40
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x4210000050cc0008000800000001000000024d6294e10935885350714540c510d154b410c6c4614c8209559431086c56190932c355132c87455210431d114831442c4614ca20d14c951082c5620c721951855310b464214532b118532c86c5620c7109319532486c5620c510d1508514cb446154831b198b410c716540c721c355132082546154f20
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x410080302aa0c299041115d8520c510c0aa830a6590e045458831443032a2c418e4311dd952d0431
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
  | 4 => 2*((h/30+packedAt s4K4 (2430+(h % 30)*7) 7) % 90)
  | 3 => 2*((h/29+packedAt s4K3 (950+(h % 29)*5) 5) % 25)
  | 2 => 2*((h/9+packedAt s4K2 (294+(h % 9)*3) 3) % 6)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf83fffffffffff03fe0ff07ffffffffc8c7fff
  | 1 => 0xffc07e1f03ff83fc3ff0ff8703e0ff0373b27c
  | 2 => 0xffff801ffc1fffffc000fff803ff0fff83c38f
  | 3 => 0x1fffe003ffffff000003fff003fc03f0
  | 5 => 0xffffffe0000003fffffffffffc000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8850801080100004601100918a111280414b5
  | 1 => 0x51931422394a152c1a5072822968aa1931b25c
  | 2 => 0x620a255450d453558148ab50425a8cd382c30a
  | 3 => 0x472c5998a2875b9aed6a0a40939cc863dc03e0
  | 5 => 0x84306110c31862e3318ccc64e0100082eb6800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaa8a0a8a0eeeaeeeaa8a0a8a0eeeaeeeaa8a0a8a0eeeaeeeaa8a0a8a0eeeaeeeaa8a0a8a0eeeaeeeaa8a0a8a0eeeaeeeaa8a0a8a0eeeaeeeaa8a0a8a0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40511
namespace PEqualNP.Outside.L_meta_40511
open PEqualNP.Outside.L_meta_40511.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x857c5150efca2186f50b40fd202617c53886fca4187ed0140df2a0417e53d06faa5206f50d40bca80877d53903ee6298df94020be28283f9404c37aa8185f54e32bf286837d5190b7e81207d4c621bea80877c544c2fea610fed0240bf294657e51d0b7ca9085f95330bf284217f53486e8a2a077d0c30df20e817d53043ea20087794e42ee996617f51503b86418ef90140bf280637c53042fca71077cca32bf29881f910042f8a4885f94243bf296817f54c43bc6518fb4c921bf29841bd4210bf640905f950419e2a2637f52502fca320df54742be28a41de53082fca1215f94a41eea9c217f51483b886995f54032be29a217e510cadca418df95232df20a817c544c6f8a2a07e50230f719643df430c6f8a690df95120be298437d54907f660985f54243efa9a43f9300c2f8a0a15f94d20bf29a437d51902f8a4987bd0942eea9c857f504c6fca518ef10a41beaa621765190afea998df14943fd204617e5310efaa5187b4c832bf28e87de434c2faa3907ec8220bfaa4657e52107e88398df54221fd90021f7418437ea890df55321bfaa4637d5110efca5985f54343f7102417e54c87be86997714d21ee99065f95010efca6217bd0820bea9681f441842fca2207e84010fa28a877d53086fea4085fd4e219e2a2437c5350b7a8621df94732ef996637e5190afaa4205f54232bfaa0217d518c2faa3987b50842bea88857d51102f4a021f794c21fd180617651082fca8215f14e10bf2a443f741cc7ea6218df54a41fa20c43f741886f8a9905f54b10fa98a43df318c7be64985794e10be2a2437c54442fca7206f95030bea84857c544caf8a0995f94c32faa8841bf43d02f8a7907dd0641bfaa0437d54483eea2a05fd5110dfa1a81fb308c2faa118df55221ef218875f53506fca021dfd4a10bf28e81bc41d02fca3105f94332bf28c437e51083be64195f55110de21c837d53d03bc87985fd5221bea86635c53502fca120d754c40ef18a61bc42106fca1a1dfd4d10ef992637d54486faa5085794c21bea9c43f451502fea0a0fb48421bea9c217e534437c84a15f952309eaa0417e54087f0a090df94021af29c857e540cbeaa2195fd4f21b6292817c52043f240105f14530bf2a641dd53103f620885f94a43bf28083df53502faa8105f94331beaa661bf41106fea0995f54a43fb208837c5150afaa4186f10540be2a4437e51042faa7887bc8621bfa92837d5010afaa9215f94b43dea08837f53c82faa5a1dfd5320bda8243ef4290afea8195f54b30fd10041be42906fca2215f95031ef29c217e52903f040086fd0641bfa8a65ef42882faa8085f54732bea9a43de314c7b88718df54d20bf28e61f541106f8a91877ccb30be292637e510c6fea090df94643bf29e217f53502fea4885f15330bea8c417c52c43be8721df94221
  | 1 => 0xf42d02f8a6a0fdd0521ee21e657d5190fee21085fd5132be2a643f7318c6baa7217ec8310bfa92617c540c7dc6490fd54642bf290657e540437e8621fbc8020ef18e617e54cc6fca118efd0940ee996637e50c87e88218df54031df21a877d53c87e88290df14f21bf28481ef324cabaa6107ec4210bf2a2616d520c6faa818df55331bf29041ee520c6fca4205f95131bea98857e500cafea0a15f95220fb08221bf4210a7ea898f7d0f32be2a4657e52087ec43885f54b31bea9e41de320c67aa8185f94042bf28887dd434c2f8a8905f94b41bea9c837e51c82f8a9885f94f40bf280213e54082f8a8087d8c621de218837f5250efca610f714d40beaa0617f54cc2faa1a0fd94432bf29c217e51086faa9107d94420bf2a041f741042faa7a0fdd0541bea86437f544c6fca918df94c41ee19463ee320cbbe8718d794c40af298417d5210ef8a5085f94342b7a92817d5490f7c8720df54c41bfa96217d528c6fea2a17754c21beaa665ed32c86bea690fbc8421be2a463de304c3ec4288778c932fa208217f54082fca618d714d21f7994657e538867aa9085f15332bea9c617f524c7d8a4a05f55021bea80837c514caf8a8105f94910ee980617f5350af8a7107e94043bfa9a837d518cafca8205f54b41be282877d531037c8420dfd5120bf2a2437d54842bea6a06f15121fa908437e5290b7aa8105754c21bfaa441ef20882eea2a07794c40f6210417e508cafaa9205f15030be29a81ee21487b8a6a0df54430bea8665df310c6fca9997750c43fb90c437c54882fea7887d94642baa88657e50102faa1a15f95310bfa98217e54443f041887750f30dfa00817f53842f8a810df54810ee18a617e53d0afaa3a07e50040be298417c540cafca4215f14941bf29e437e528c2fea7105f94630be292817e50882eea2a1df94f20bfa9841f521c42faa120ef50040be2a6637850486faa898df94e42beaa0657e51106f8a9085f55232bea9c637d51082fca0185f14f10bea8865f75150ef8a098df94b10bf284617d5390a7ca8186fd0a429faa2437f54843f480205f55130bea9c413e548437e8721dfd5230ee21863bd54842faa010df95030fb188637e5210fec6290df94b31bea9221dd324c2fca8995d54420be28243f521442fea9996fd5131bfa9a41df308c2fca9085fd4143bf29021755190afaa6887ed4121efa1a8776510cafaa9905fd5130bf29861dd310c7be60185f14d20ee21c617d544cae8a2a1d754e10eea98417e5410f7a84a05f94640bea94437e52842fca318df54f42bfaa0637f5150fb88618774c931ae29a83f710042fca721ef90c41bea9841df53506fca6085f94632f690041ef52503ee4290df55230bea9083bd43d02fea81877d0e30f6a90637d548c6fea890fb10a20bf29c837d52883b863985f54831f721
  | 2 => 0xa60000100403014d705c4d0280000c1200008010470001003c0035000000060181001003000011400000c870000911c000040f04c00004220c40c0040500412138001a00001416000270000502401048c100806010020040f0104b318500140302555014de0280102029018003fc0002c1e0040002c0007c0a0140800c040181302804094010001902400054030000121800004020001506c4a44c03354ca0180009422090000100a00401020580f00100001000020740001c00000161184c004000500310800000ac3f0050201e0801a5900a0101d0041a03c040000f284060400500403034110380030c000941d03403028000000b0080819c220000200034080240bcdc048fe258000041200001020a900402000000580500c0101003288000906d0842d000000001b0303d0000104c580700700c0400c2e2440e000430042b0000310401004e00200002800fb108437f54c8778a898fdd0431df20a837e520c6faa3a1df54610bfa8a61b
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1314865d6314b109d195214427a6015331d554d210871d544c0309718d540431c54cc9318f992534873b54d4121d6d4f504867661d52329e58054ccb5453d05419798f540827b654c0309d984540823d6414e2097997324c6766194b409d984524c23d6414e10b6580430c63f64547308f99352842776544010d614c50487375410521d3549310c6d5610ca318fd954210acd620c5308f992508c73561d5121c7152314c7574314543d558453487706054420d354d21086ba60905409798e508871d5410f32d9548410c63f64547208f191524425e63d4a10b6580434ca3e649512197195434c34c53d4940a798e421067761553329dd85548827a6094d219d594410c66c62551109b58b54c427b65500409d59441043575314540c714e415063c6454432c7553430c25e6394b419798e544873464544328fd91534425c635474097d8d544866d62d53309718d524423c6454d109758c5244354538c52197594430c67561d5330b658043cca5e6314c209b98b54c42746154d20d554e510832c52105408f596540c2746155220d9148515025f6550c43cb14b42502d96010e31d3d0d520c63f65504419798f54c8279601503297994534879943501309d58652d033943540438f990540c23e65151218f990528425e6314b1097d8d544c63d64d4c20c714e41502786054d2197996434c339548c0309d98453c82756114f2097d8d51c825d63942219b19532486b86050940ce150504863e64d4f219798f54c863e6415020d314c525025d631502097594430c26e6214c109798c540c23d6494231d554d510825f63550109b988540427661d52309ed81544873751105409d185544823f65500409e582534875b5314121ce551300c2766194b43ced0d5010e5f63551209758f540823d64d4e10ced50504879b43502309798c524425e63150109d98754cc34d528c8319bd95320ca7960150219798c530867b6054d219d58652d0e3c6454730b51854310f5653946429dd95210867561d532097d8d524427860551329798c54082d86350230cd185540c35453d4540d98c9510ca5e6315220d954a310c67960150319798f540873454cc5319d587548cb2c5290540c7550430c3c6328c5219e980540c66f65480209d584540ca5d63942419798f548427b60549109d587530832d54d0820d554e5190a5f654c8329758c548827661d53209bd954210a5f654c431d594d5190b5953900409d984530826f6548421ae580431075653d06108f593528425c63552209e58054cc65e63141429b58853c435653944209d18554cca6f62551209b189534431e5454e108f99052043944310431d3d4f52502776154d209758c540434d53c84219d997414866f62551309dd95411073761550309798c548427561d5032a798e429065e6314810d3149324c27661d5032
  | 1 => 0x70081202088100400470000005008000201018000a064b800001b280201800010000200028500a0005006880100008060600000040001844001f01028240f1e9c4041400028140009038120200004380b9758c548426e62d50319718d548877341141218f994544c7596014d40c7951530834c4354831dc104504866f6254d10cd952510825d6394010d594c418425f63552218f990530831c5414d219798f540ca5d6594c2197d8d5110a5d6314810d594d510825d63141428f59654083594354043d3588534863e64940109e98254486e662d05219798e5090677654c431c7952538425d6394b41cd90c5150e5d658c831d9d4b515026d62150319b189544c27761551319b98853c434d520c831cd55041842d46150f3097d8d544c23d64d4f21b6580430c25f63552209d584524c23e64141329b588530427965840109d584530832c62550209ed95100425c6354720c7d50534863c6454d219d984540cb1d5454c20b6580438c33654544209798c52843595350040b518d411065c63544428f590528423f6550c438fd91510cb4f53149409758f54c835553546428f590530826d651082097d95300c31d5454e108f993538431d54cc0308fd9152442796508010ad18543d027960951219d195314867561150209758c540871d53d00409798e500429c63504419e980540c27661d4c209b98b54cc23e64d4c209d984530867661d50208f992544c71c53d0d409b58b540c6d8604c9309758e544866e62150319dd8554443555388421d614f504865d63d53109e980540875753d4540b358831cc2b4644c431ad185435035453145409b588540427761551208f992508863d64148108f592500423d6414c10d94c9510cb1c54d4d219dd85544c31c63550308f590504caf161083108f592534867461550309d587540831e5494c209798c540865c6355110c714c415027a60150329d185544ca3e6414c109798e52d036452d4540d514c414867865501308f19151c825d65d0c30c754d40103355494420ae580439063e6414e10d514f414875a43540439d987540865d63d50219ed95200831d5494e109ed81544ca77615513297d8d51d025c6355121c7d53534865e63d53109758f54c865d6394b4097d8d5444365524c431b5185434c3376155210ad1854310e5d63d52108f191534825d6594c20d554431cc35532544329718d544826f6255110d954b410c65d6314a108fd9153482f060487108fd91534867661148109e18154486776155030cdd91510cb355454420d354b310c67a6015332d314e324863d6494221c7151324c6d5610c831ce153504863e6414e209d587548c3675214540d914921442b561908419758f528425e6394d219b988530865e65d0d32ad19131886746155130a7191310c7573254432f14c9314871d5494c20ad19
  | 2 => 0xa1302000000f18808041106050124a0308d6eda030054c130001c0807000240c01008000628090040415018000000000340000018141a0200024322700000001b3c0000a02000183c000008238052a00002290380404090010400020081c062603940361606000061301804000719014000100000360002808000300014060002024001201008300
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x10002407406023100d00240000191589510c730932e8302649870443548410c68a3a2a218e61265ce6090540c32a8b0087995147458453486a838a86a8087525c04354831932e630284a0684644c931486a2b88a499261515cc5248510928e8b086418d307150d5010f12322a498863915896114d21c32a8b0086185147155043ccb06322a498863645c04310431a28e2aa086184c57398b41486c838a86a02618518c6155030
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x420000a10815516010f32b018010d5210431c04745896114d21c0474589510c730a10815516010c30
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
  | 7 => 2*((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt s5K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/268+packedAt s5K5 (16632+(h % 268)*10) 10) % 616)
  | 4 => 2*((h/194+packedAt s5K4 (15732+(h % 194)*9) 9) % 414)
  | 3 => 2*((h/22+packedAt s5K3 (1225+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/8+packedAt s5K2 (300+(h % 8)*3) 3) % 5)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf03ffffffffffe07c1f83e1ffffffffa207fff
  | 1 => 0xffc07ff01fff07f801ffffe1ff07fc043f9e7c
  | 2 => 0xffff81ffe07ffffffe003ffe1ff83fffc3e38f
  | 3 => 0x1ffff8007ffffffc0001fffc007fc03f0
  | 4 => 0xfffffe00000007ffffffffffe0000007fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x1485091244128401605c0a13258c4552202cb5
  | 1 => 0xa1931421c9242a5808a956a04b42a8340d965c
  | 2 => 0xc20a2444834822aa8a0124c4125232a4c2c30a
  | 3 => 0x8b2c5989120eb734ed3580911ce720c77403e0
  | 4 => 0xc30610e1c70c5c731c6391980840303bb7800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfce8a8a0fce8a8a0fce8a8a0fce8a8a0fce8a8a0fce8a8a0fce8a8a0fce8a8a0fce8a8a0fce8a8a0fce8a8a0fce8a8a0fce8a8a0fce8a8a0fce8a8a0fce8a8a0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40511
namespace PEqualNP.Outside.L_meta_40511
open PEqualNP.Outside.L_meta_40511.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa28214004000008904002ffd5001fd3100ff14005fe5200ff04001fd21007f88405ff21007f4c00bff53017fc8003fc40017f90801fe41017f8c805fc4200ff94007fe53017f08407fe4302ff54805fc52027f1040bfd5100ff08009ff4101ff14c03fe2000ff90003fc3001ffcc40bff51007f50801fd4101ffcc807fc43007f4400bfd50007fc4009fc5400ff8400bfe51007f8c401fd40027fd0c01fd2002ffd480bfc5102ffd4001fd43027fd000bfd54027fd0807fc31027f95005fc32007f4c807ff3002ff54c03fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1c8203f7cc1320fffaa310803fe3148427fe20a600aff19221007fa8710803fe414800dff90a2000ff5814100ff88088016fe6550c05fe1924003bf18f1002dfccaa0812fe644c001fea0a6026ffd0a31005fec09900afe6244033ff9824200ff50d10005fec690802fd6444015fe3044205bf19521005fec6a0003fd32c4003fea024001bfd81200a7faca98027fd51440037fb026022ffd0131007fac898816fe65c4013fe28a202def90a4100ffc808802bff628c407ffa9c6200ffd9131057f821208abfe5350405fe1044200ff5912017ffea320803fd214c001feb0a4014ff55130117fe8298807fe504c015fe3046200ff9853200dfcc0a1807ff4048001ff30a4007ff0c51010ffc84988aefd6550427ffa126002ef90942057f8c58807fff5088403fe0828028ff1414101ffe629883bf651c40057e3146238bfd9543007fec2a10cffc1050845ff2a26204ff10943025fcc899007fc304403fffa8c4203ffd4d3001dfcc720803ff644c0057e3122003ff8ca31077fccb880cffe6050803fe2028003bf98d10107fcc098877fe638841fff21a4003f70c5310bff8a2a00b7ff2190447ff28a6204ff10d4001ffc6498007fe40500057f312600aff1464104ffea288013fd4350029eea9a6006ff94910005fec2a0013fc409040b7e32a6004ff50e41017fca5108d7fc5150803ff9062004ff90241005f8c2a180efc635002bff90a802fff54641107fc409883bfd53c400b7f32a6000bfd9310025f8c890003de314c005ff90a8424ff9823108ffcca9002bfc63c402bfe3128003ff14d31057fc638800afe628c46bfea8a8404ff1014200ffc4090013fd435083bfe21c4217ff5454000ff84088002fd644c809ff2028428ff84141097f8c49803bfd65c4005ff2928402fdc852100ffe618801ffc43440037e3028619ff94d21057fecb10803fd4188429ffb2a6004ffd5143087fca8900d6ff6550811ffa1a201fffd5221117f8a898812ff6450405ff2124038ff195431c7fca2a1863fe6048405fe2944201fd8411001ffa651885efd6550007ff21a8603ff54d320e7f86110803ff604c801feb0a8600bf1853201ffe6099007fd30c400b7f32a6402ffc813204ffea8880bfff5390405ff10a4201bf18132195faca99047fe5148031ff082420fffcc520007fec0a185fff515000dfe2922029ff0854119ffc60a1003fd6350001feb1a200affd9221057fc8318803fd6090401dfb22621fff5422116ffca5208abfc5350439ff1844201bfd8510027f680a0007ff5044023ffb2a400fff14d20005fac118816fe6588405ff9924001ff54110027fe80a18167c6544059fe1048200ff4c520027f88720813ff43500017fb224204ffd05430c7f8a09082bff64c4007fe9926015ff9494000fe82188007fc2050063ff3226401ffd4140
  | 1 => 0x7fe30c404fffa8c6203fd0c531077faa5880a7fe32504057f3162005bf19531027fa84a007bfe54884097e3224201bf18231197faa09900bfc4250835fe3224202f78c932017fc84a100ffe5350c0b7e32a8402ff8c92101ffc6099003ff635040ffe29a2008ff95110037fc848804bfc524c01dffa962000b7d8d2112ffca518807fe1048001fe98c4224ff08231017fc4110803dc6348409ffa028400f7d8d21007fac2a102bfc41c4015ff28c4200ff58930187fcc09900ffc314c037ffb2a4200ff5071001ff88718803f621c40017fb1a820affd9231027fc86a0026fd654400fff9922000bfd9120007fac4a1803fd644c0017fb0a6407ffcc51004ffca288047ed5248003fe282401bbfd952108ff8ca9007ffd658840b7f32c8205bf19641027fc86a1037fe64c40037f3046200ff58f1015f7aa8a0803ff6250009ff2a28001ff8811013ffea918813ff4150001ffb222000ff58e21007fa628803bfd54c4003ff2862012ff94930007fa43880c7fc414c80b7e32c6202ff54932007fac0a100afc624c003ffa028015ff9894000ff8409807bfc54884095e3226203ff0c231025fcc888003fd315001bffa162000ff4c941027fca920813f741504037fb022000ff1854200ffea09800efc6350807fe21a6027ffd4231027fe82a100efe6350807ffa1a6001ff0c1301affacaa107bff438842dfe29a8008ff1511001ffc869889ffd508c401ffb0a400effd4f10177fe6320813fe4390409ff2a28400ff18530027fc84a0002fd64884013fb2a2021ff08531007fec4a08cbfd544c829ffaa26004ff15140017fa649082bfe51904017fb1c4216ffcc54002778852082bff6590417ff3162000ef90540007fac298013fe5450c05ff1926417ff9454000ffaa0980bbfc5390469fe29a8405bf99510057f8cb1880ffc324c407ff1846204efd0641017fc4290067fc634846bffa8a840bff8cb10177fe6520803ff614c86bff28a842bff54d411a7fe62a1003fe414c407ffa9a6403f7cc93113ffea518803bd4250015fe28c4201ff48110017de429900bbc4250801de322421cff10221005fec68800bfe205084ffea946200ff509310b7fe64a0013be5450015fe0844200bfd894101ff8869900afc62c4043fe212622bff59541025fcc898813fc5490415ffb1c8202ffcc94202578c89082bfc3188401fea0c620aff18e2101fde6499016fc658845ddf21c8202ff1092000ffc6098053fd524c001fe30a4023ff5953100ff82088083fc104c4037e3028410ffd0520017f64090013fc4350805fe10a4003ff0c943027f8a8a109ffd548c409dfa028405bf195100e7fc8110803dd324c055ff9828200bf58a41075facb8800bff2048429ffa926003bf18d21017fa849006ffd5348409dfa048238bf59543007fec69080bff21884017eb
  | 2 => 0x32027fc8520802fd644c043ff9026233ff8414205ffe4388013ff4250457ffa828201ff9031001ffe86990b3fc5090403fe206201aff991210cff886908d7fe65508237eb2a4001ff88130137f8a918877fc5388401eea1a600aff18a4116ffcc520807fc5050001ff10a2003ff14d30007fa829083bfd51c4007fe98a6000bfd9130005fac69006fff50484097f322421bffd51210f7fe811082bfc318c4057e3128203f710e3101ffe64980cffc5050801ffb028407ff18d1001ffa869907eff6588427fe2a26002ff14921005fac588093fc408c405fe2926423bfd95310c7f8609082bfc648c405ff90a641bff541211bff842a1803fd6088403ff1028000f7d8d41057f843108c3fc404c823fea9a400effd471001db8c690802fd6344001ff18a4030ff90132197f8a299063fe504846dfe2828628ff8c1411c7facaa1803fd628c465fea8a6400ff5813212fbc6518806fc6048407ef9846202fb94920007fac4a001bfc2144049ff2046201ffc8120017f88510807de304c04ffea8c6214ff1453000ffa8088007f610c4003ff9824018ff8c121027de84a1026ff6544015fe084622bffd4941017f865108befd65904017fb126200ff58532057fc8310802ff614c04defa1c6204bf19131005bec6a0863fc6048409fe20a822bff549410effe63108dbfc6050c17ff2962000ff88540015f8c498802ff6488401ff20a2000ffd8121037f8648805ffe6550003fe9824003bf18d2000dfec69806ffd6548403fe106200aff0c710067f8878805ffc65500037f3026400ffd8910007fec89900fdc314c005ffa924203ff0c13200fd8409001bfc42440017fb02420affd8221005f8c2a000bfd5248409fe2128003ff94d3101dfcc69000afe624c42fffb2a8000ff5091006ffe8788007dc304c005fa10a4201ff04130007ea428800ffd5350c51ff2828204bf98641027fe8320897ff218c415fe10c8238ff99543057f8c120803fd6244005ff292640effd531001df8c720857fc21500017fb128601ff54310017f84099012fd649043bff21c420aff1463101ffa869802ffc52c4021fe322402cff9824101ff86299013fd4290441ff0826214ffd453000ff86188057fc325006fff9028603ffcc143017f842a1003fd62c4057ffa9a821bff55121005fec2a1807ff50c4041fe2826207ff90d100a5faca980b7fc32904017fb1a4004ff10a41025fcc988097fc528c401ffb0a6032ffd4132127fca118813f44190425ff90a601bbf59521017fe651087bff4188403fe2026000bf58f100277882a08cbff544c8097f324421bff19521027fc82a000bfc3250801ffb126002ffd493200ffe808802bfc418c471ffb2a8601ff90130017d8649900aff6250829fea8a600fff94d20005fec6a100bfe4288437ffa9a4236ff84143047fe828800
  | 3 => 0xf98a642cff8824118ffe809901bfc624401fff31a4030ff94132015fcc4a0807fe5048009df2a2822fff54e41057f8632082ffe42c40057e3128604bf192310bffaa6a0003fd428c407ff1828603ff0ca31007fec0a080bfd2148023feaa2400aff9471001ffc6498803fd6290451fe0828203fecc1300057ec898803de314c401ffb1a8012ff085301affaa6a100bfe424c863ffa0a640affd963116ffe4120803fe414c001ff18a802aff18d4112ff88518813ff4090403fa0822002ffd0920067fe6388007fe20c4009feaa2860cffccb100057ec8908e3ff5250c63ff2a26400bfd8141007fa6388007ff2050003ff9828003ff0c930147fcc0a0807ee2048057fe28a8218ff041211a7fe60a100bff2050801feb0a8011ffd4d20027f880a0877fe53884077e31c420cff14f1014ffe42a08e3fd5250c05fb90c4204ff50d41027f882a180fdf324c0097f3224000ff5923100dfcc388002fd628c4017fb0a8400ffd8943177fcc72086ffd5148403fea026032ff9453215ffccaa084bfc424c0077e31a820dff15310017fc4099013ff5450407ff21c6209df1951015ffaa2a081ffe5344001fea126019ff98d2101ffea6a1803ff6150c077f31a422aff98d41007fec8900d3fe6350839ff0844231ff1513200dfec8a000bff21484037f3028202ff8c9201b7fcc0a1827f5514400fff31a2003ff4c9310c7fc8090863fc4048415ffb048202ffcc93215ffea2a0803fd434846dff2828600ef19131117fcc898807fe1044037fe28a4202bfd8521007fec2a009bff408c4017fb22641cff14221027faa8a08a3fc6050453ff902822fbfd964114ff8a4a0802ff648c407ff21a6026ffd0631007fcc2a0003fb1044001ffb1a4001bf18221057fec11884ffc644c007ffa1c6203ff50e31027fe86a0802ff624c0017fb026201ff48310015f8c4a0012fc64884077fb1a6200bf58d21157f862a0803fd63484077f31a8202fb0852100dfcc0a109bfe548c43fff32c4203ff50d3100df8c09885bfc6350003fe2822002bf58a2112ffc851880bfd4288401feb1a841aff10521177fca72080efe6350007fb98a6201ffd013009ffe829800bff4248407ff98c620aff94631007fcc298003ee2148403fc1024029ff949410b7fca6a0007fc10c404fff32c6213ff951300dffea290852ff654c02ffeb2a8003f710d3201ffc64a1802fc614c011fe3222035ffd9542027f886a08d3fe5350839ff3044202ff4c92015ffaa0a0816fe654c415fe28e2012ff90930127fc41188b3fe1090407fea9a6229ff1894101dfec6a18c3fc104c805ff2924203ffcca3101ff8a718853fe514c007ff9926203ffcc13101ffc629880fdf3050c077f31c421affd0d21007fa8788007fe1050005fe1024203bf9863101ffe6298067fc31484017eb048231f7d0d
  | 4 => 0x3ed3248403fe102400aff88710005fec488013fe4350401fe9922003ffd0d31097fcc49802bfc65c4009ffa128015ff8c94000ffe2088002fd6448401feb024224ff84231057fec7108dfff2150c47ffb2a6204ff10143007fec6a1013fe4050c43fe2926200ff58d20007fac91088fff544c4017eb122011ffd4520007fac9880aeff6550413ff32a2008ff9911000ff080a00caff654c8477eb2a6200dfd951001ff8609883aff65c4001ffb126201ff84130007fac0988d7ff5350833ff21a4203ff94d30027fe80a080bfd3288405ff9044200bf5923107ff86290087fc624c449fe2846238ff14543017fca4900b7fe3290407ee1946204ffd05411aff8caa1007fc3048001feb046223ff54131057f84388002ff62c4015fe32c8204ff1514108ffaca90012fc644c009ff2128203bfd914317ffccb20806fc6090401feb02861bff9952101dfcc788003dc6350405ff1928404ff9514107ff8869000ffe304c4017fb12800bff0cb10147fc40a0802ff6050c017eb224005bf195431c7fea2a18dffe5250c21ffa1a4035bf595420d7fe8290802ff644c417fe2162002fbc8621007fec688003be415040b7f32c620aff9071002dfcca9002bfc65884097fb0a8204ff9014119ff8c0a1003fe6150c63fe3226400bf1854208ffea8900abff3150405fe10a6404bf193101a7f8c6a1002ff63c4001feb1a8202ff149200d7fca890807ff5048003fe2826002ff9092100ffa818800fdf314c8057fb228403b718d41007fec890807fd5048045fe3226200ff4c521007fa8588027f65144047fea926204ff151430fffaa710827fc6544015ffb2e2002ff0c932015fcc5208abff325044ffeb2c6219ff14d2100ff42188083fe504c401fea0a6217ef551400dffca290867ff3148409fba0c8202ff10932007fa6520803f521c40037f3026200f74c931015fcc4a18dbfc2050c07fe18a8603ef10d43057fec58802bfe3188407ef21a6002ff88121017fe649080ffc4350c077fb0a6204efd0940137fcc918803fd3250019ff21e2009ff54d10005fac898807fe3048001ff18a2001bfd892011ffaa89880bfd424c819ff31e200aff19310037fcc48800fff4350c09ffa12860fff18d20007f8c2a1802ff64440237fb2a4038ff54543197feca99007ff3044003ff9022004ffd0d42017fea490037ff41c4045ffa12620aff18e41197f8ca9900efd638c471ffa828610ff105201c7faa0a180aff634c801ff10a6001ffd03100d7f8a89082bfc218c4017eb1c4203f7cc63101ff8a699003bf644846ffe2928602ffd093201ff860a180bfd5248051fe1828203ffd4d3101ffc8699003fd6444015ffb1e201fbf5962114ffcc4a0807fd3044065ffa8a6400ff50520007fac72089eff658c447fe32a622effcc24106ffca9880a3fc2050407f
  | 5 => 0x60500000000a028090000260680200600e0140e84103e0100200500601004a350680883d0120000840081d00a00c3b8f701c04c030ff0003c001000202004008030040040000c0060499283b00c03024816040008388ff0242e8001470000140183900a114000050441f80000607a031bc0d30f8014048040021d80900000809ffd9510025f8c89905bfc3150007fb98c621eff9922101ff8a6a1813ff4390405fe1028404ff109411b7fc40a18bfff529040b7e32a4003ff94e31087f8a890007fe3044035ffa024234ff0c54202dfcca9080bff528846dfe0828601ff54140015f8c52085ffd5250007df21a8604ff90943027fea92080aff624c859fe1848202ff54a2100f7880a000ffd538c415fe20c4204ffd514000ff060980b7fc529043bff9844202bf989401affea0a1003bd4350003df202800cff94f1001fbca698027ff5244067fe1828404bf1911011ffaa298887ff214c407ff98a8608ff1051000ff020880bfff5090409ffaa28415ff14940017fe8510827fd5244041fe2026225ffc823100ff860a0006fe6088405fe292842fff54241007fa828800fff308c41dfaa8e2000fd88510007fa8690003fd644c85ffeb2c8203ffcc9430e7fca110803ff604c407ff29a6400bfd85201affaa0a1083fe404c40b7e32a8023ff145310fffaa910816fc6550401feb126227bf59631197faca99007fe10c4059ff184820affd8a4109ffcc89800bec4250805fe2124203ff54d3001ffc6298043fe6448003fe0824032ff9953204ffaa888003fd2144015fe3146205bf1971000ffca08800aff6248405fa10c4205bf99540027faa920807ff304c06ffe3128617ffd4940025fcc918813bf4350003ff1828001ff1431001ff88698807ff204c001ff30a8408ffd0910017dc6490806fe60904037eb062003bf18d100fffea710802fd64c4005ffa928400ff18532027f882a00c3fe104c861fe302640aff1064117ffaa52085eff6550047ffa926200bf18520017f84290813fe415040b7f32a8400ff18540005fec0a1027ff5344053fe1928204efd014319ffca0a108fff514c409feaa28411ff54520017fe429000afe6188409fa20a8204ff50540027788720802fd6088403fe2024002f70c932027fa84a0813fc415084bff3146202ff5494215ffca2a080bff4250805fe1924211ff1452015ff8caa080bfe3288461fe2826420ff0813100ffc809001bfe3244005fea124204ef1054010ffca4988b3fe509040b7e32a6401bf9812104ffaca88003fe4148457ffb2a8204ff5514000dfec0a000fdc4350c41fe3026204f7d0d430b7fcc6a008ffe654c447ffa826201bf181410a7f8ca98003fd625042fffa9a8003ff0c531027fe8520887fe624c401fe90a8022ff1053100ffca0a000ff4318c401feb224237ff989430a7fcca98
  | 6 => 0x60000000500e0340080100e0783f8694b80fc1e858006008020580000580100000000c0300005401c04800012280000000000940e0250520040004700002c1000301c00800c9f0062980482800a3540e80f0aa000000080240006e0a90001000080104c414038000e40101b80e006058000180888d827a491660282081300207c0000220c004023630040200080407800000028006304030060000700000010a02c0d8080000100ca1007a72c0080516401004c3b00c3c8018000c20381d80f00000004802046240008202a0034000000181b8000010080d4000033a80fc018482c8820068152de0082980d00400c0281698c5102d00100600816a1b0aa0001c800000000000410860080983c00005c0c00002a014028140060880400b00000c0102708a04841004000010028c0212050018000160180b86816a01c2600410404c1500e0162d40000c040278000a60160641200200a4c80100101000c018000b604c0007701a0002b8020000200b00b06c05c0080400010c0e008060018450070080880087a0c814c0180403c0041383f12e0001580001a038118010001e9df8250064344981041675c4b0031d40049100000000c170000561d4028010000000200c00007c018010ea0240581706600086005032004000040005840300001001c7e84402c0000a8010001080a81c0140003b07000a0001780201
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc6290540004fd75d9121056f62118520006bf50d91310067c7558d2001cfc73d8910024bc7458d100079f6450d3006dbc7448710136df7359231056f71018530005f77158d42006bc6458131136dc648c531006bf51d91210057f75582412edbf7590540006dc6018d21004ff7359120014fd73d8532006bd75d9121035f9709852002cfe75d854202cfc7559231054fe7158a411bcfd74d913202cfc75d814202cfe75d912110cfd73d8e210c6ef2058b10006df53d8d402cedf30d8d4000ddc708c530006bd65d9121004ff7259310336de3218532014fd7018520056be4159310006df7358d20057f221c411029ef531185300069f6418d21004fd74d8e21116be71d9131004ff725913033fae321912100cfe76505100c4fd72d8b10224ff7159110004ff7559131054fc715923116ebf21d9121014fd73d8132004ff7558f10006bf6190540006bf7458910004fd7558a311379f4359231014ff7158b1002cfe75d8132056f671d9310004ff76505300cedc6358d21006bd5459110006dd75d8d21006de50d8d41006bd54d91210067f65d8d1000cfe7158b10006bf6450510024bc7458d2001cfe76d8d2100cfd74d8540005df73581412fef541d8540024ff7659231265fb7058d200cedf31d8d210079f644c93100cf57688710054ff72d9121055ef7388521144ff7059110024fd70d8940005bf7458532006dd50d8d21156dc6350521054fc7650f10024fe7418532006f77159131056f4311852018ebe64d91320279f7350d40006bf52d913100cfa76c4110014fe72d85430c4ff70589100067f6558d10006be75d9121106f8605813116ebf42d912101fdb6050d30014fc74d8940006bc63d9121054fc7218540054fc768c52000cfe70d91310f6be5459221006bf64d812100cfc70d894100cfe70d891019cfd74d9120057e77248710156de7618d410c6ed2058b1016cbe7619121006dd6518d2102cfc7558910004ff7359110014fe725911016ebc20d9121006be6319121005f47158d200a57c755893000cfc70d9221004ff725824110cff7258d21006bf6458131136de54d8d41024fd71d8941375bd7590541004df735922103ddc7350510014fe72d8131204fe768c510006bf7458d10004ff7458d20014fd71d8d21006ef725912116ebd71d912101cfe7359221006f651d8532004fd75d813101cfd71d8131005f47158943086be54d9120006f751d8540006ef7258d10004ff7458910006dd52d8d41166fa4058241007e76248510054fc75d8e21336df6118d21054fc73d931000df6704851002cfc75d85320067f7559110054fc75d9231006df65d8d41006bc6019121006bc7458d20054fe71d8930004fc7650d2100dfa71c4110004fd75d8d42004ff7650520014fc764c5210067c21d9510396dc4318532006be41d8141
  | 1 => 0x9510176bf31d9131004ff7558d20005fb7048510004fc7650d20006be40d9121056f63118530004fd73d8520325fb7058d40337ce7218d2100dde7050d30186f86058132137d441d8d41014fe76d8940006bd72d9131014fc725913101cfc7358221006dd70d8d4100cfc70d911001cfd7418543014fe72d923101edf608c530176bf71d9131014fe72d913100cfe76d8121054fc7650a31006df6358141006de70d8d412addf754c93001cfd72d91322ddfb7059130255ef7258d20007db704c930005f771591320067e72d9510014fe721854325cff7358d20176bf73d9131014fe72d8540007e53248510004fe764c540014fe72d931000cfc70d8931006fb50d812111d7c7558131104fd73d8f10004ff7559221054fc751854200cfc7058d21066dc31d8131006dc21d8d4102c7c7558d2001cfc73d9130036ef21d8910004ff7650931056ed721853200ff361c411000cfe76d8142004fd75d893002cfc755931010cfd764c521007e7714c921056df7358f1002c7c7558241007b4619054001cfe7358241006f721d8530006df6350d2122e7d10d9510006be43d9121014fe764c521144fd74d9310116bc644c521014fc72d9130004fd72d8d4100df8704c51001cfc73d9120014fd741854200df4708871000df6708851012eee3258a31086bc6459120014fc7258241054fc7158a3100ff271c4110136df40d8d41006f72118543054ff70d8910097cf214c9300057f7558910005bf744c510006de6518d41006ef42d89100079d5418d41005ef724c52135cfe7690531006df43d8d2101edf614c931004fd70d8941024fe7458d210067f41d9510056f970d8f10057d6718c5310067e62d951000dde704c930005bf7458132056f64118542006f441d853202cfe75d8540006bd51d9121025be7190540116bf41d9131024fd715931002cfc75d8943014fc72d8d20024fc7458a3106ebe54d8141054fc7688540006dc63d894131dbf7550d4000cfe7059132056fb1058241004fd75d8530024fc7458e21014fc7259231026bc6490530014fc72d814127ebf40d912002c7e76d9510006bc60d9121005bf7458d10005ef7258d10004ff764c9410adec725854016ebe32d9121006bf6458d21026de6450d30004fd7650d20086bc41d91200067f74d951016ebc52d912102cfe75d8142054fc72d9231056df634c6210079c644c9310057f7558d10054fe71d8142037e46248510176bd53d9131004fd7218530004ff7458a31006be43d9110056ed72d9221006bf6450521386f54118543136dc41d8d411edf77588510054ff75d9221054ff70d8d10004fd72d8131056bc4159221004fe764c940054fc7650b1012edc3258a31006de51d8d41006df7358d10006df75d8d412cddf7359130006f751185430067c755911014eee62d894116eb
  | 2 => 0x24fe74d8d20056f6511853200efa76c4110055f47150f102e6bd43d91300eeed32d8931006de62d8d4119efa20d81420067e63d9510054fc74d8e21176bf43d9131006bf644c521055be7190541006f741d8532006df50d8d41004fd755931000cff73d913001fd7614c93100df8704851003edc6358d1002cfe75d8520024fd7018540137d741d8d412ccff7359130006df735913218edf43d9132005bf7448710006bd54d913218ebf4059132006be6519121004fd7650a3100cfd73d91300cfcf314c921004ff75d853214dec7258141006ed52d893133fb7211912100df470487101edf5758851003edf31d8d1001cfe7359310004fd7558f10005dd728c530004fd75d891000cfc70d913101cfe7358a4100cfc70d923102cfe75d8d10005df7359121014fe725913112ede21d8d21015ef734c9212e6bf43d9130006f451d8540056bc6459231046bc42d9110006be73d9121276ef20d894000dde768c53003ddc7358910004fd75d8132004fd71d913200cfc701853235ebf611913136cff7650631004ff7358b1000cfe7158f1000dde708c53002cfc75d8143014ff7658b1001cfc73d89410b5dc7358540004fd74d8910016f4628851021cff7158d10007d9708c530256ef20d893016fae32d9121004fd7650910054fc715824102cfe755922102cfc75591212febe54d8540136df435923101ddf724c93002cfe7558231024fd72d85420067f7558241024fc74d8d21024fe74d893123df57548710004ff72582310cedf3058a3110dec725813102cfc75d893112fd421d8d2110eee32d8931004fd768c540045bc7458910004fd71d894016ebc629054116ebc42d922116eee3258a41224ff7650710006bf6519121004fd75d89400cedc53d8d2106ebe545931001edc634c52102cfe75d8e21004ff75d912100cfc70d85432febc41d854002cfc755913001cfe735911012ede72d8d2101cff764c52106ebc41d8141004fd71d8d40056dd73d9231024fc74d852001cff7658e21054fc75d8f1000cfc7158f10065dc7348710004fd75d8543004ff7258e4112ede20d8d21005ed7388521006bf75d912100cfe7018532004ff75d8943005bd7390540274ff7259120136bc648c5210067f31d951000cff72d912001cfe73d9221014fe7258e41254ff7258d2002cfc7559120055bf7590541006df634c941006be63d9121006df6358941045bc744c510006bd5459231007d7714c93115e7c6550510004fd70d8d4201cfe7318540006bd50d9131005fb7050510054fc74185323a6bf42d9132024fe76d9130226f710d8540016bc765094001ede634c910006f761985300f6bf40d9221004ff75d8d10016bc6250940336f52118532004fe7650d20014ec725911010eec6258931275ef72591200eedc43d8e21004fd74d8d200067c63d
  | 3 => 0xc6358e4101cfc735911035edc431854316ebd20d9121006bf65d912100cfe70d8532006bf648c521014fd74d854202cfe7559120116bc54d913111e7c654c510006de10d8d21004fd764c910004fd7418532004ff7358910024fe76d9121004fd7559221056f63118543004fe765093002cfc7558b10004fc764c910024fc74d8d1020cfe7690510004ff75d913202c7c755891001cff7658d20005bf748c5401b6fa40d8143106fa60d8131006f7619854201cfc735824122e7e20d9510014fe76d8930056de3158e2102cfe75d8943006f751185400067c32d9510014fc7258d100067c31d9510054fc769053002cfc7558e41006df52d8d41176bc31d9131004ff75d8142136de41d8d4101cfe73d9130024fd731854300cff765824102cfe7558e2102cfc75d89410067c74d9510006dc6358941116dd4358e41006df43d8d10004ff7458231176bc32d9131347cf434c921177b731d9131004ff7650910115bc7458131006f731d852002cfe75d8d2038df77158d41006ee20d8941006be20d9131006be40d9132106fa30d8131024fe74d8520006df53d8d2102cfe75d9221056f4411853216ebe72d9121136df74d8d410067c73d951000cfe70d8d42024fd70d8d40006dc10d8d2103ede63d8d10354ff7159121007bb7050940004ff764c5400069c64d8d21006f751d8543014ff73d9132004ff7558910056fb1058231054fe7650b1001edc638c521005df7358542146bf4059310004fd70d9121024fe7458910056f45118543054ff7518530006dc54d8d2130dfb7058940006bc51d9121016ef614c9211a6dc4359132025bc7458a410b6de43d8d40004fd70d92211b79d4050d3001cfc7359120005f47158d42056f86058231005df735051001cfc73d85400cede71d8d21005ef7259110006df6518d21054fc7518532054fc751854002cfe755822101eec634c921386bf401854301cdc7359110004fd7650d10005bf7250d40014fe72d9120056bc4159310176bd32d9131054fe71d9231014fe76d894101cfd74d85430cedc30d8d21005f47158132016dc764c930004fd75d91200cfd4314c521007d7618c530186fa30d813201cfd7158f10025bc7458e410067f6550d1039cff7359132026bc6490521006bd70d9121006dc6418d21136df41d8d41004ff7558d10004df7358910176bc53d9131006ed624cb10176bd43d9131054ff7018520006dd53d8d4100cff72d8d201b79f3050d40004ff7059231014fe72d8f100067f43d9510215f77158910024fc74d8131046bc43d9110004fd755824101cfe73d912135ef531185430079c6418d210eddc735062102cfc7558e21004fc764854001cfc73d8520007cf624c93000df57688710004fd70d9231004ff7058a41054fc7158a41004fd71d8132004fd7518543006f721d8543
  | 4 => 0x9130136dd43d8d41006df735911016ebf6490521006bd6490510024fd73d8143007d4714c931004fe764c910027b6719054019ef8605814226edf32d8d2037df77158941004fe764c5200067f7558d2002cfc7558a31004fd741853022e7c30d9510006f77159110006dd75d8d410eddc735922100cf4764851000cfc72d8121066df3258f10006be42d9110024fe74d8f102beed32d8930054fc7688530024fc74d813213e7c658c510056f671d8b10004ff764cb10006be65d9121056de3158f10004fc764c940024ff7650510054fc7690520007cf624c9310d6bc40d9121025bc748c54016fb721d912112ede3258a31176bc30d9131116be761913101cec764c921006bd75d913104d7c7559110005df734854002cfe75d8d41027bb6050d40176dc6390521097cc624c930024fc74d8d20024ff765922116ebf20d9121004fd75d854203edc3158d10054fc751853001ddc73505300079d54d8d41004ff75d9120006df638c52002cfc75d814100cfe70d9110006de65d8d41006bf745913102cfe75d9110004ff7058d21054fc7158221006dc60d8d41015ec7250521155dc7358941004fd75d931009ebc645913001cfc735912112cfd72d8d2102cfe75d8d21006bc64d8d2133cfe7690521006dd74d8d21007e4714c921054fc72d9310016ec624c94000cfd73d8530014fc7258e41004ff75d814304e7e76d9510004fd72d8540004fd731854019fb8705094002cfe75d9130015dd73d9132156de74d8d413cedd43d8d4212ede628c53101cfd72d85320067f658851002cfe7559310005f471591320cedf30d8d2112fce3258a3103edc32d8d101cff151c411000cff7658231004ff7650d1012edf72d8d21005df7348530006bc645812102cfc75d8540014fc73d8930036ec42d8910004fd7418520004fd7650b10005bf744c62102cfe75d931000dbc7050d40014fd74d8142056ec2158b102f6f54118540024fe7458221006de6518d21005f77158930024fc74d8530046be64d9110054fc71d8d100057f7558930024fc74d853200dbc7090540085bc7458d20056dc3158e4100cfe7058a41054fe71d931016ebf32d9121004fd72d9130004ff75d8d4236cff7159131006dd50d8d41006de64d8d212fef641d8540007cf6388521176be4358e41024fe745823110edf3258e2135fb731191310c6fa20d812102cfc75d912102cfe75d923105fe6324871001cdc7359121024fd71d8141004fd72d8530005bf7458910007d77348510004fd764ca4121ef710d853000cde768c530337d72118d21006be53d9121006be75d9131155dc735814101cfd70d91302a6f531d8530006bc75d9121006bc72d91310057f7559110316ed42d89400d6bc43d9121004ff75d854318f9f43d913218edc644c931026be6490510006fb7059120056d
  | 5 => 0x56f71018540184ff7058d2009f9c6450d30004fd72d814322e7f30d95100e6ef20d8910004fd74d8d100e5f77248510024fd73d854312edc20d8d21144fd7650510004fd751854017e7c6590510004ff75d8121176bd30d9131176be43d9231006bc651912100cfc7018542006de6018d41004ff75d813121edd73d8530054fc7158e21176bc6390540004fd72d8d40024ff765913016cff7459121104ff7058d101f6f621d8520004fd75d8520004ff7650d20054fc715913001cde76d8d41005df744c930054fc721854335fb43119131016cc624c93016dbe76191210c6fa10d812101cfe73d8940004fd74d8930024fe74d8d10024fc74d8930014fe72d8d41005bf7458530014dc764c9310079c63905412c5df7550d302a6df32d8530014fd7158b10006dd6518d41006bf75d913101cfc73d911012edf21d8d21004ff764c520006f74118532054fe71d8d40004ff7358241005dd748c530016f66288510024ff765053136df77159131004fe7648540024fc745823116fae4258a41176bf30d91313b6df30d913201cfe73d8520057e671885210e4ff725891019efa40d81420cede7618d21006de20d8d41007cf72d8d210057f755853012fce328c521004fd75d8931156de71d8d410069f64d8d21156dc32d8d41176be6390540156de63d8d41006bc10d9131176bf53d913123df775487101779c31d9131006df63d8121086be64d912012edf42d8d2101cfd74d894312edd71d8d21156dc6358d4134cff764c621004ff755912101f9f7450d303a6dd73d9132004ff7558231006ef32d8910006f77158d20014fc72d912002cfc755913222e7e10d9510054ff75d8b1016cfd72d9121004fd7690520006df618c530005f77150f1016ebe52d9121006be10d913116ebc72d9121136df43d9231004fe7648530006f431d8520146f860581411cf7865c4110164ff74591100079f6418d21014fe76d8931004fd75d89430047f7558d203c6df43d8943006be6019121004fd7688530004f77158d2010fcf214c931156df305923116ebd72d9121004ff7458221116bc6459131054fe71d894322e7c10d9510025bf7350d4001fcf724c93019efa60d8142006bf72d913100cfe70d8543006ef624c9400e6ed20d89100aeee42d8940054fc71d911000cfe7059221006bf7459110004ff7358221007b474487100e4fd70d891021cff764c710054fc7318520177b431d9131006dc75d8d41004ff7059121006df54d8d21335de76d8d21006df6418d2107ede63d8d2001edf604c930136dc74d8d4101eee634c92101cfc7359310136dd71d8d4100cfd71d911016ebe4258a413cebf40d8d422a6f631d853008d7c7558d20156dc53d8d41054fe71d8b1000cfe70d922100cfc70d8d21136dc648c53000cfd72d8520054fc7159221054fe71d
  | 6 => 0xf42d913116ebd32d912101cfc73d8542004ff75d8520004fe768c540054fc715912002cfe7558a31004fd75d89411ae7c6550910004fc764853000cfe70d9231006be70d9131006be51d912101cfe73d9310006dc6518d4112edc628c530004ff7648530046be5459110056df31185320067c64d9510025bc744c54001cfe7358b10004ef7258d1022e7c20d951001cfe76d8d40024fe7458e2100cfe764851000cfe7058a31004fc7650930004bf7458d1000cfe70d8941014fd7318532006ef624851000cfd73185300cede43d8d21016f6624871002cfe75d8d400067e73d9510005df7358520004ff75d9130016e462485101e77465885100d6bc6459121004fd721854301cfc7358a41006bf64d8931004ff7258f10006be60d9121006f410d8532006bc20d91310047f7558d1000cfe7018543024fc74d893100cfc7059121156dc30d8d4102cfe7558d10006dc72d8d41005dd728c531126dd30d8d1001cfe73d8141014ff7658a411beee32d8943006bc60d9131004fd72d9110006f7311854218ebc645913200cfd72d8d20004fe765052002cfc75d9110004ff735931001ddc735923100cfe70d91210067c6559110004fd7018542014fe721853016eee4258a41164fd70d9110155de76d8d41057b67190541007d47348710005bc7150940004fd7559130014fe76d8910056be415923101cfe76d8d41006df51d8d21004ff7159120126fa3058231007ac644c92112edc72d8d21004ff764ca41006be70d9121024fc7458d10004ff765093000cfe764c510024fe7458d20054ff751854239edf32d8d42006df7358d21004ff7158d20006dc60d8d21056f71018520006bf54d9131126df30d8d1012edc52d8d21015ec724c52116ebd52d91210c4fd764851002cfc75d8d42054ff751852018ebc40d9132004ff75d891001cff70d9130005bf744c540004fd75d8d10024fc7458d20004fd7650d21006bf64d8d210cfcf304c92100cfc7158b1001ddf724c931005f7715894317d7c7558241096ec21d8930006bf6458121004ff75d81320067c65d8910056f45118540026bc649052001cfd701853012cff7358d21006fb7058d1000cfc70d8d1002cfc75d8940006f451d854301ddc7388530004fd70d9131006dd65d8d2102cfc75d9132176bc4358e41006dc6358121007f37048510004ff7559110005df7350621006f56118542136dc54d8d41056f64118543004fd7518542006ef72591320067c65d9110004fd73d931002cfe75d893116ebd42d9121096ee62d8930014fc72591100aeec21d894022e7d30d951000cfc764851002cfe7559231014fc72593101769c6390541004fd75d8532006de6018d21056f42118530006be30d91210aeee62d894001dde7350930007776548510005df7350a312d6bd40d9130006dc63d8141
  | 7 => 0x8d21014fc725913001fdb608c530056bf745922101cfd72d813212fcc72d8d2102cfc75d8d10006ee20d8931014fe72d8d40187d8704c930176be32d91311967c654c910006bf64589310f5bc744c6210067c7558241045bc7448510006bf65d9131004fd768c520004fd70d8d21006bf73d912122e7d40d951002cfc75d913100cfd73d8930004ff7558d21007cd3248530354ff7650621005df7350530156df30d8d41056f64118540005df7250d30006dd634cb10004ff75d854201cff7658e41146fa60d814101cff7658f10006bf6450531285fb7059120024fe7458f1001cdc7359221016ec62485100d6be54d9121004fd75d8d20004ff75582410cfcc634c9211fdf67688510355f77159121007bb7050d40054fe71d8940004fc7650520004fd751852000cfc70d8d4202cfc755911026edd32d8d20006df53d8d4100cfd71d8d10024be76d913101cfe76d8d42006df72d8d41054fe71d91100067c6558910004fd72d92313a4ff74591320079f6350d40206f51018530006df63d8941004ff7559310004fd75d911014eec6258941006dd54d8d213aedf30d8943004fd75d8b10016de624c931006bc65d9131006df7359131004fd74d85200de7c6548510017e7614c921006dc74d8d210d6be71d91210d6ed4258a41006de40d8d21024fe74d8121026bf609054000cfc7058e21046bc415911008d7c755852038ef641d854312edf71d8d21004ff75d8d410d6bf4058a411b7b87050d40006ef725891022f7810d951022f7771d95102addd754c930054fc75d8b10004fd71d8143126de768c530004fd75d8d40004ff7558e2116ebe629054007edc6358d20005fb704c510004fd70d8931004fc76505303879e5418d410067f21d9510006ec7259110154fd74d9231006bc64d893137ef641d8542006f56118530004fd755891002cfc75d8520004fd70d8e21005ef72585400ceed3258a31054fc72d8f10006bd54d91310067f42d9510004fe769052001cfe73d8121016f46248710007e77248510006bc6019131004fd73d8940014fc72d8543004fd7018543054fe71d8132025be744c9400067c7558d10056bc6459310007b77448710166bf40d9110005ef725853018dbc74581321a6dc6358d42006dc6518d2114eef21d894106dfb705854000cfd7418540004ff7458f1022f7471d9510006f610d85320c6f76048510004fc764c5400b6df32d8d4002cfe75591300c7f0704851000cfc70d8532004ff75d8d210cedc4358a31005bf744ca4136ef631d8543006be50d9121004fd7559121006bd54d9130024fe76d912002cfc75d8d20174be761913101cff72d913200cfd74d8d40016ee624cb10014fd70d8d2010edd3258e21006de70d8d21006dc10d8d410047f755891000cfc70d913202cfe75d891000dbc7050940116b
  | 8 => 0x24fe74d8910014ff7658a310079c64d8d21006be72d9131006dd65d8d41054ff75d8e21005ef72581410057f7558d20004ff75d8141136de648c530056dc6358e21124fd70d8d10006bf745912001cfc7358910056bc6459221005bf7488540004ff75d893128ebf42d912012cde7618d210e6fa2058221006df635052133fac21191210057f7558540056ec2158a31054fc7518520006dc20d8d4100cfe70d89310067f73d951001cfe76d8d20054ff7518540006df634c9400cedc43d8d2100cfe7058d2100cfe70d8e21007f121c4110006dc6218d410d73d75191211beee62d8943004fd7650e21056f62118532006de32d8d10014fc72d813116ebe6290541104fd764c510056f86058241006df4318532014fe7258231006bf745912100ddc7050d3014cfd7650521004fd75d8143006bd5459221056ee2158b10005bf7458930006bd651913122e7e40d951012ede52d8d2101cfe73d9120054fc7518543056f6211854202cfe7518520006dc7359110004fd70d8943006ef52d8940017cf734c92114eec20d894100cfe705923101cfd7218532124ff7358d10027b76190541056bf7459310174fd73d913101cfe7358221186fa20d8132006bc6519131056dc6358f10007af644c921004fd75d854001cfc73592211957c7558132024fd7218542004fe7688540136de648c531054fc74d8f10006df638c54000df4708851000efb61c4110006dd32d85300067e43d9510014fe7259130004ff75d893012edc42d8d21014fc72582310d6be7619121004ff75d8d40016be625094001ddc7350531026bc645053118ebe54d9132036ec625891004d7c7558d1000cfc705923100ddc764c930336dc3218532014ff70d8d20005df7358121065dc735071000cfc7058a41024bc7458d2135f9c311913114ebf4259221136df54d8d41006bc65d91211b4fd74d9130004fd71d91203879c4118d41014fc72d8530176bc43d9231005df748c530176bc73d913133ef5211854200ddc704c930004ff7458e21026bf6050940054fe71d89100cede63d8d2100df6704871000cfe70d8d41006be62d913101cdc7358910295df758c53000cfc7058e41004ef7259110006df7359121006df634c521014ff70d9120136dd40d8d41136be5459231004fd72d8f100b6de63d8d40054fe7158a3116ebc21d9121056f43118542006ec7258d1027ebd40d91201b6fa30d81431779e4358e4118edc644c93000cfe76d8141014fe725931000cfe70591310067e32d951012edc628c53101cfd71d9131006f7619853216ebf52d912102cfe75d81411379f438c540006bd65d913101cfc73d8121004ff7559130005df7348710004fd75d91300067f6550510006bd51d913101cfe73d8540176df30d9231004fe7650d21054ff7018530024bc7458910006dd641
  | 9 => 0xc75d853001edc638c54001ddc7390530116bc42d9131006de32d8d4133ebc421854201cfc7650531004fd731854200dfa76c4110004ff75d9110004fd70d9132006f5611852012edf20d8d21007e53248710004bf745891001cfe7650531006bd73d9121004ff7558221006dc65d8d41156dc4359231006de65d8d210067c6558d100047f7559110005bf74485100067f654c51002cfe75d9120005f47150d100067d72d9510135de7618d41154ff7359131054fe71d9120004ff7058a31056f410185320067c7558910004bf7458d20024ff7159310156df31d8d4122e7f10d9510006df51d8d41214ff7158910006f77158d10025bc7488540006f61018532006bf7458d2101dde73d9132054fe7650e2100df4704851001cfe73d891034cff7158d21016dc624c930004fd768854009ebc42d913010fcc624c93112edd72d8d21004fd75d8f10004fd72d8d10006dc40d8d21005bd744c940004fd73d9120175be761913102cfe75d8131004fd72d8141016ee624ca4101edf6050d30004bf7458d21005bf744c710056ec2158a41006f77158d2103ddc7348510006f551d8532006de31d813100df870505100bd7c7558540004ff72591311a5dc7358542054fc7318542006bc70d913102cfc75d8542014ff7648510006df43d8e21004fd73d814116fac21d9121026bc6450d21006bd53d9121014fd71d8121054fc7318540005bf7458131004fd755913131dbd7550d4007ddc7350520014fe7650521006bf7458d20006f7619852002cfc75d8910005ef725813112edf32d8d2102cfe75d8530056ef211853200cdc764c930066df32d813101cfc7358b1001cfe73d8542004fd71d894300dbe769054001cfe7358910056ef61885211a6de43d8d4233dbe76d9121006bf50d912118ebc41d913201ddc7350631006bd54d91200067c65d8d101ddf5754851016ebf71d9121024fe74d8b1000cfe70d894312edd20d8d21046bf41d9110035ec7258d10004fd75d923102cfe7518543004fd74d8121006bc7458d2100cfc71593100cfcd7218d21006be40d9131004ff7559231176be6390541054ff7518543214ff764871001cfc73d8141055f77588710006bc7458d10005df7359221005f77158d2000cfe70d91321a6de63d8d42025bf725094039ddf735913212edf638c521006df21d8d4101cfe7359121024fc745822102cfc75d8d21246f52118520004fd7518532005df7359110024fe74d8d2102cfe7558241004fd7518530136df42d8d410cddc73591210dd7c755812102cfe75d8f10225f77159110004fd73d8910056bc4159231006df7358910006df65d8d21337cc2118d21167ba7090540006dc64d8d21056bf619054102cfe751853001fcf724c931006df70d8d41004ff75d8540176de4358e41134df7359131054fc7418530
  | 10 => 0x9221115bc7458931014fe7258d10056df31d8e2114cff7259121176bf32d91310d6bf40d9121004ff7258d10136dd54d8d412b5fb705893010eec20d893101cfc73d894021df77158d10006bc50d912122e7d20d951024df5758871000cfc70d8e2102cfe7558910057f170887101b6f86058143006df64d8d210cdec764c9211b6fa60d8143005bf744c52002cfe7559121006de75d8d21006dd51d8d21025bc744ca41006be621913112dde7618d210057f7558131006dd51d8d41006bf51d9131215f776487100067f658c510056ec6258a31024fe74d893000dbe7050940004fd75582310d6bf41d9121004fe7688530004ff7559132024fc7458f10006dd72d8d41004fd7558d102357e76d9510006f77159121006f421d8543176be31d9131004fd7558b10136de40d8d41005dc714c930006bd54d854000cfc70591320079f64d8d21004ff7650b100057f7558520006f7715913202cfc7558d10036ee62d8910014fe72d91301beee42d8943005f47158930004fd75d8d2133ebf6219121016f46248510054fe7158e21006ef6288540056ef21d8e210d73e75191211b4ff7059130006dc70d8d41006dc51d8d2100cfe71593101369c648c53100cfe76d81431f6f6768851014fe42150521176df6418d4102cfe75185421379e54d8d4112ede42d8d210067c43d9510054fc768c54004e7e71d9510004fd75d8e210057f7558141006f56118540004fd7558221006df639052101cff7158f10024fe7458a3133fb4211912101cfd70d8930156de43d8d41054fc764cb10006bf31d9121396df3018532006bd54d8141006ef6288530006df634c510045bc7458d1001cfe7318542226bd74d8540146bd4059310006be52d913100cfe7018542006bd50d9121006dc52d8d41056f8105822135dbe76d9131116bf4058e4102c7c755911001ddc7350a31007cd324c521006fb7059130004fd74d8131054ff73d9131004fd7558e2100dbc7650940176be73d9131004ff764c940056dc634c62100cfc7059221305bd7550940004ff715913001cfe76d8d10006df7359221004f771591323b6dc43d913201dde718c530056f671d8e21006be43d912006dbc744c7103a6bd42d9132005bc7150d40006bf70d91311bcff725913200cbe7690540026bc6450510056f671d9231006de60d8d4114eee52d8941026dc7650d30006bc51d9131006dc70d8d21004fd74d893100cfd71d891000cfc70d8542057f251c411012edc32d8e21057e56288710016f4764851000cfc74d814100cfe76d813201ebc7650d400079f6390541004fe765053000cff7658221004fd73d9121016ec62885400067c42d9510006df7359130057d4314c621004fd73d8b1012fd721d8d21006f421d8530055ee71885211779c434ca41004fd72d913100df6708871002cf
  | 11 => 0x1cfc73d81420d6bf43d912116ebe20d9121054fc764ca410057f7558132005bf735094016ebc32d9121024fe76d913201ebe6350d4002cfe755913203edf3258d10006bf745913202cfc75d8121054fc7159132004f47159132056f86058221006bc62d9131065fb705853002cfe75d8121004ff7059132005df73505310067f6590510024ff7659120006be42d9130007db7050d30006dd32d8131004fd7558d2134ef621d8532056dd7318532136dc42d8d41054fe7159231085bc745852018ede644c930014fc7650521006dc62d8d41006de54d8d21004fc7650910056dc3158e21305bf75509401b79f4050d30006fb7058d20056f8105824100dbe7050d4000cfd74d894002cfc75d8d4100cfc7650510176bf6490531337d42118d21014fd70d8520004f47158d20006f55118532004fe7650d10054fc7158e4102cfc7559131024fe74d813202cfe75d8532004fe768c520386df4318543006be65d9131176df3258e410067e64d9510024fd71d8d41054ff7018540004fd74d8132004ff7558a41024ff7659310006dd638c51018ede644c93122e7f20d951002cfe755911012edd52d8d21005bf745893101cfc73d9121006bf20d913116ebc4258a41004ff7650f10006dc50d8d21006bd5459310085bc744c520035ec7259110056bf7459231006bc53d91211379c41d8d41005df7350710004fd70d8d4101edc638c520146fa40d8141004fd73d8142004fe7650910006df6358121006bf6490530006bc73d9121006df70d8d21146fa10d814110eef21d893115d7c75581413c5ef7258d42006bf6450d2102cfe7558a410077b65c411001cfc74d8d40365f77158931216f710d8520054ff75d9231006f47158d20004ff7650a3101edc6350d21176be53d913122e7c40d9510054fc74185200cddc735052101eec764c92112ede628c530014fe725824135ebf63191310067c72d9510054fc75d9221004ff7159132006ed624ca41006bc52d9131004fe769053002cfc75d8543006bf21d913112edd42d8d2101fdb604c930056de3158e41024fc7458b10006de30d8d210047f755824101cff764c51005dfb7058520027af7250940106fa10d8131004fd7559132004fd755911018f9f434c940054ff7518532056f671d9221116bc40d9131004fc764c94100cbc765094010fe4214c521004ff75d8d20056f970d9310006de10d8d41037e6324851000cfc764c51018edf4359132014fe72d8d10006dc63581410067f32d9510054fe7158e410067e74d951002cfc75d9130024fc74d81210cfcc434c921006df63d81410cede53d8d2100cfc70d8943006bf651913103edc43d8d10004fc7650931016dc624c931004fd75d814202cfe75d8143006bc645893110ddc764c931176bc63905410b79c6350d40004fd75d9221006dc735
  | 12 => 0xf7059221006f56118543054ff70d9110156bd4359231014fe72d8141004fd73d8941014dd73d9132006df40d8d210d5bc744c521004ff7558a31004fd72d85430067f655091001cfe7318520004ff7458b100077765885100aeec625894000cfd721852022e7e30d95103adef7259132004fd74d8532004fd74d8b10006be60d9131004fd7690530024fd73d8943007af625094000cfc7018543025bc7448540156bf435923101cfe73d8142056ee2158a3102cfe75d8543004fd70d8542004fd71d8d42006dc41d8d21176be30d9131006bf70d9121056dc3158f10136bf40d9231054fc7158d2003ddc7359110006ef7258d2002cfc7559221054fc73d922101fd6718c530026dc6450d30054fc7218530054fc71d891002cfe7558e41006bf64d8131387d44118d41056f57688710005df7350520004ff705913101ebc6350d4020ef5101854000cfe705912109dbc74485300079f648c531057e66288710156de53d8d41295dd758c530054fe71d8d10004df73591210067f6559110086bc43d9120005df7358910054fe71d9221006f76198543004ff7359221006de52d8d41006de51d8d210067d73d951016ebe21d9121054fe71d8e21004fd75d9132006bd70d9131135df7350631014fc72d9131024fd72d8142006de60d8d21174ff7459131006f731d8542005ef7250521007d773487100067f65485101ddf7754851016fb421d912110eee62d893102cfe75d913102cfc75d8930054fe7159221054fe764cb10004fd701853201edc634c941006de50d8d2105eee3258b1022e7f70d9510054fe71d9132005df73885303bef54118542004ff755912002cfe75d8930005bf744c52135ebe4318543004ff75d894102cfe7558b1000dbe7090540026bc649053102cfe7558d21016dc764c931056ef7258b10004ff7458d10024fd70d85401c67c6550d10005f77150d1002cfe75185320d6bc54d9121054fe7650f10024fe74d853009ebe64d9130006bc62191310057f7558121007ac6488521004ff76485402d4ff74591300067f65d8910024fe74d8e2101cfd70d8530116be64d9131366f631d853201cfd74d814312edd32d8d213aedc43d89430067e42d95100eedf30d8e211b7d87050d30006be651913110eef2158e21004fd73d922107ddc7358520014fe72d8d20006ef7258d21004ff7558e41014fe721854001edc634c510006dc7359121006dc51d8d4133ebe4218542007b97090540006f761985400067f65d911002cfc7558d21014fe76d894300cfc70d8910007b47448510006df75d8d2102cfc75d8d40004ff7259110016ec62885303c6bf40d894314eee42d8941006df6518d41336df6218d2122e7d70d9510006be42d9131006bc31d912119cff7059120054fe71d8d42004fd75d8d4100cfe70d8542055ec728c521
  | 13 => 0xc92100cfc701852032edd43d8d40055de718c5310b6dc53d8d401f6f521d8520156df32d8d4122e7c70d9510057f270887100067f654c910006bc64d81211a6df30591320c6fa60d8121006bc7458910056f8105823100cfc70591312c5dd7550d30005df735854034df77158d210b6dc6358d40006bf6450931006bc75d9131014fe7258f10055ec714c921004fd75d8141006dd64d8d2122f7610d951002cfc7558f10056f671d8f10004ff7650e21095ec725853022e7c71d951001ede634ca41056f421185430b6dc31d8d40016f66248510334fe768c521006f72118530014fc72d8d41006be50d9131054fc7158231004ff7058e2100cfe7058e4101ede634cb10004fd721854033ebf611912100cfe7018520016f66288710006be51d913122f7410d9510014fe72d814335f9f321913102cfe75d8940054fe71d8d200c6f850d8121006bf53d9121004fd73d8542004ff7558b10027bb609054001cfe7359120006bf6490520004fe7650931056ee2158a41004fd71d91300d5bc7458d21006bc64d8131054fc73d8b102a6dc31d8530014fd73d9132006be10d9121006fb7058910006be601913102cfc7558221004fd764cb10006ef725911000dbc7650d401779f32d9131024be76d9121004fc764c520006bc631912102cfc7558d2002cfe75d89410fe7c6588510006bc10d9121004ff7058e4102cfe7558d20006de6418d21056ec6258a4100cfd72d912002cfe75d8d42004ff7650d210afac62509400cddc7358121024ff7659132054fc7650e2102cfe7559131006dc6018d41024fc7458910116be54d9131007d4734851012edc21d8d2102cfc75582312edbd7590540026bc6450931005df7358941004fd70d8543004fd71d8142017e761885211fef51018520056df618c531006df20d8d410069c6418d210067c62d95100067f72d951004d7c7558910014fc72d9110136dc40d8d41004fd73d8540024fe7458b10007cc638852112edf52d8d21004fd74d8530024fe74d8532014fd71d9121006ef7259120176dc43d9231006ed52d89413b6bd43d9132004ff7359121056be41592210d5bc7458121004fd74d8f100f6ed42d894100cfe70d8d100079c648c53122e7e70d9510014fc72d8d40154fd7650531006de75d8d4102cfc7558241024fe76d9131057e42190521036ec32d8910024fd72d8d420067f65589100a57c75585303b6bf43d9132014fe7259231006bd52d9131045f97098540004fd71d8d20004fd75d9131004fd73d91100067d74d951001edc634c94007edc31d8d20056f970d8b10006dc65d8d2109ebe54d9130006fb7059110006dd70d8d21007b76190540004ff75d853000ddc7650d30004fd75d8121006bc50d913101cfe73d8941004ff7358a410067f7558910014fc72d8143054ff75d9310004f
  | 14 => 0x6dc50d8d41005bf7458121006bf54d9121004df735911001ddc7358a3125edd30d8d20007d4618c53001ddf7450d30006bc30d912101cde76d8d21014ec7258d10006df74d8d2101fd7618c531006dc63d8121024fe76d91101d7746548510014fc7258f1028ebd42d9120004ff75d8940014fd70d9120004fd7559231166be7690540006df4358a3109dbc7458530007af6488521024fc74d8910006bc21d9131026bf6050d40056fb1058221006de6218d4101cfd71d8931006bc6458d21006df41d8d21046bc645911000cfc70d8d4112fcc21d8d21006f7715891025edf30d8d20186fa60d8132004fd7559120136dd42d8d4103df97098530387d74118d41006bf745913002cfe7518540004fd7558d20176bd71d9131004ff764c910004fd70d8532004ff725923102cfc75d9120006dd634c91016ebe42d9221006dd53d8d2100cfc70d9121356f621d8542004fd73d8121006bf30d912122e7f40d951027cff7459120005dc7150d300067c41d9510106df3058f10005bf7458d20005bf7448540054fc75d9310014fe72d9110024fe7418520006dc75d8d21006f5611853200cfe7058e21005bd7290540024fc7458d21006bc70d9121004fd71d8930004fd7558e41006dd634ca41004fd7558a41006df50d8d21004fd74d8d21056ed72d8e21057e4218c5213bebf4018542096ec6258930054fe71d8f1009dbc745893022e7d71d951000cfc7058a3112ede32d8e21004fc7650d10055dc714c931026bc6450521024ff7650521027bb605094014ebd4259221024fe74d81310c6f86058121005bf7458520116bf40d913110eee52d8931006f47159132014fc72d8d101fcfe768851001cfe73d9110014fc72d854018e9c644c931056df7358e2100cfe70d8d21004fd72d9310056f7608851035edf3018543004ff7458d21016de624c93009ebc41d91301a6dc31d8d42005df735052101ddc73485300aeec52d8940006de72d8d41005bf744853002cfe75d8b10006de74d8d21396f531185320cedf3158a310aeee32d894035ebc431854300cdc7650d30005f77158132056f46288710054ff75d8f10054ff72d8d21136df71d8d4102cfc7558a41006dc735891000df47648510056ec6258b10136de42d8d41024fe7458d102d6bf40d9130014fd74d8d42004ff75d913101cfe73d8b10166bd40d9110004fe764c941005bf7458d21096ee32d8930024fe74185301779e4390530005dd744c930006f431d8542004fd731852002cfe7558f100c5f5728851000cfc73d81310d6be64d912102cfe75d9132007b7744851002cfc75d813202cfc75d81311beec625894301ede638c51014cfd74d9221054fe71d8143004fd7650f1002c7c7558d10006bd651912122e7f71d9510246f776487100b5dc7348540006f73118520007cf634
  | 15 => 0x501000301a00300609a00604100d00400100000f07000900c00b02202100400300c0174e00005bd00700500000a00004600002d2b800100106402035f0f803502103502008415002100004500e00501f00000600028b00300200401300600f06f00000104d01008a00002200d03a39000d00708101100502012301f00d24b05d10300900306702608103f2570001bb03500004e0030040000000000290071b900331d00003a05d00200621e00000000100005d0601bb0070000000c000300d00c0121a300201811101500102100e01e02109307900d0150002e105204e03a06c00a0190040160010006142a700001203301f00b3c900200100801f00308a66a25504d02400700400400d18b00100e01000f02501a00323d00001000500100002500204500306a0020113b60dd04b00300500200d00206c05200001b00100022d0240020001e700402900d00700300000700007201d00400d01901b01405c00100c03900901300e00b00602400000000400301703131300f01b00200005c00800100007806301300700000100700063d00015700d07303a02900c01000e00d04912600200000504214301b0010050a500e01904a0050020b903c00700000300634f06200702200004004500000701500601500000200002e00500c00000301100000202500e01f2ce00018f0b900200f14900000f01100100705800000001032c0000030040030040020000280000021ac00000002700000800000d02501101e0000221d001f00b0b700400000001500200300001c00107406e00412209707e00800000516502309100000600000007003500200a00000e0000a402f23b0000b70330041662473e600201e00101d1f201d00600004e00000923400000000a0ad13900000002100002100200e00a00000e00000a00b00b00509800300041001c00201100a00202f01000b00b0ca00902a00700f00a00000004400001201802700405500001a00001000300600002903101402d02300203000800004798c01402701700a00b13b0055e20010000100b200200006300401006600200400c0000030c900000103200000102700d05903b00000100703600002000101b00000100100d00a0b60070010300000070010030000020001342ea04201e0020481ad00200001b0e100d04600a00000a00113f0531670fa00e0040150010038fc00100000b00a00800a0210c500007800000700000001600303e0000050040a000e01102100404e01701e0220010020160001860090020000040131a502700002e35b00e00c00700b127da708c530014fe72d853036edf6118d41106dd3058f1016ebf72d9121056f63118532184fd73d8d20054fc74d8b1000cfe76d813118dbc745853200cbc7650d40006de30d8d41005df7348510176bd73d91310067f7558d10
  | 16 => 0x1800617315200400500003300900101001a0280104630140c90000160150020030a301700400002600f00103737509c0c40010190000090020060180010db00b00e02000400d00d00100600e00200400600005400100600101702c03a01611202701614b01d00d00d02500000003000100f02601800000000b1db00d00902d01d01300100100206401400701107102f41b02a00604200704700402c02328e02a00d02500b00000906c00b00f02800609917c01b0070100100260000000f200205d00607f0071be01301600b00001800700001900b00b03800002d00804903900700900900b00100d02003a00300003001b00b03900006800601f08259600600301b01f00d00600500000300900300d38902500106700200000f02101300000102d0380150320742ef2190778d903700e00000101a0060320120080030163cb0120014051b200a0000030120000030170050ad00000701004300400800000118f08300106a03700000000404203c01200004000d00101d00000f99400200403304000d0030000000ac34b22202001500152c0040070
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc9c63dd163484015a906b08c29000237e1d6518d211754f418e5b226200ccf63dc960504051d904baac88800333dcc7258d100047bc0aeab222000cac76191324840136902ba264a00022fe1172185300051e422e7b2a2000acd8214363484011bf06bb442a000237e0d7558d210054f420ebb1a42048bc845cc614811396ee2322c498802ab60873d91210063c32ee090a2000a5e831cb65440151e902bb286900261f61c41d95100052ec1843b2a2026a9e84843635040117f0eb28c890802b560450d8d2112c6e436e6b024200adb805976348405998e4996c2980022fe117650d2100667b9ee4b222000ccc731c9644400159d05328c6a08022f61276485300054ec1cca322420587c855c3644c80156902aa6c2a00029760e42d95100045f438a1b22428aab581980644c40157700b28c8908ba2fa1e10d91310056b408a1b1a82048bc845c7604c85d53d07086c8988031b1d77258d101145ec38a3b226200a7685c876150ccd1bf0e996c2980062fa1b748c5400043ec2eeca1a200087f855da414c0151d90eb126588002b520532d853022e3a3b6ca90a200abc4814c931484011bb073b2829000327dd063581210045ec3cca32242008be87143644c4015cb0418ec2a102a3d2057558d200045fc22ec9922000cac741c9634400b17f0eaa6c899002a7a1210d8d210056b408e1b1a4200a9d83994644c4cfd48c43a242880022fa1f64589310054e41aca32242018dc835c7604c8011bf06b8ec0a1002a761353d8d2112d66412c718a2025ec462dcd21440010ff0ab8ec4980031e1d770589100046fc1aeab222000a9d83843644c4cdd88c439a42880161f215764c91001573436c490a20268de87843635045d938e7b2282988bb2718f744c5210054ec2041b1a8200ae482584614c00159b04286c6a0a13a39cb6418d210064e3b0c89926225ccc62dce214c0031b90cba264980021fa1c7558d1012c6e43ec6a0a42008be87d4b644c40147d0a106c8988029761721d8d410045ec3841b226291ab784584615080193ee9b1ac09082a3d20575592210547a40ae630a401a8bd87147644845b55d04286c890802a7a1353d8d210046f438c6b0282008f787584614c85b17d0f086c890803a35c86418d210047bc0aeca1a420087f855d9324407d5cd0db924288002a76126018d210055ac26a3b0a80008f787584614c001cc8c5b2a4288002a7a0c50d91214156bc0ac831a4200c9f74d8d314840117f08baac68819f2d1d874485100045ec3861b2242008dd871036348401878cbba2c4880032ddd07158d200055ac20a3b0a8000a9d8498363484071b90cb946298803b14cb21d85300043f43885b2a2025cd476dcd214400153b09386c6a099b351d8734851000746326c49926200ab681dd764484051d904bb286880022fe117650910
  | 1 => 0xb07300c8908031d5d751d85430045f43ec8b0262008ef825d564480010ff0ab86c89080297a0c62d9510336e3b98e29924200cac72191604c4010fb0e216ca8801e3761f618c5300047bc0aeab226000cd4631c563480031f100baac890803175d753d8d400054ec18a1b2262048be87dd1634800b0f90abb48298002a7e116518d410065a3a6e2b1a4000cd7731c5634800117b0e286c8908023be0975591100045fc22eab122000c9c76d91324c401878ea3a2c68802a3d205741853202c7bc3aa3b0a640a8bc87551648845d53d07386c89880637a1b73485300045fc3aca32262008be87191604840147f0ab86c8988029761662d8d41006563a6e4b1a2000c6f75dc964440011bb0e286c6a080e3720d76885400062eba8ebb1a4200a3c845cb65440014bb06316ca881ffa50846418d2100656326e4b026200e3751947644840153d07328c8908063d2057650f100054fc1aca32242708de87d8d414840b1df0ea96c498802b5a0450d8d2101c6f43ee6b24428ea9e84194635044d53d08286c6a08030f5d475d91210061fbaec8b026200cb4641c5644c8011bf0eb28c6a0802ab60850d913100567410a1b1a820087f855c0614c8018baea3aec6a08062f219744c94000557414ca32262008de8718d60484cd998c438a649800237e0d75591300066631ee4b028200a9e8398364484071bd073b242a0002a761352d8d410051ec2e43b22620a8f4815d5644c0015ab0610ec2a1803271cf64505214956bc1ac230a860587c855c7624c00147b0b310c8988023761c20d8d410054e422cbb1a4200a3d8598b644c4014bb0a106c6a082a3721d634cb100046ec3c21b1a4200c6f65dc964440018d8e5b2ac688002a761075d8d210146e43ac69922000c6c72195634400196ee838ac899003331cf72589103de4f3b2a9b1a82018de86dd2314c00159d0532ec6a0802a72116518d2102c3e42ae1b2242008f7815d943480018d8ebb92c8880022f61e10d91213e63bb88cab2220028ee87dc963440019ae6038ac89900e37a1f7359121006563a6e4b122000cd473dc562440014bd0b310c6a08aa3761c21d8d410063a3aee2b2220008be87d91604840187eea3a2c6900021fa1c41d95100054ec24e1b1a42048bc845d562440014bd0a3a6c6908122fa12764c52002c3f42eeca1a20008be87191624c401878ea3a2c69000f335cb43185320064e3a0e6b1220008bf845cc6148001878ebba2c6880021fa1f6558d100064fba6e6b1a42008df8759063484071b906baac8908162fe1d54d91204454f436c720a82008f7815d564480051eb03baec89080387d5254d8d2102c6fc3aa7b1a4200aad82994644c40147d0b90ec8988032bdd37258d1000477c12eab226000c9c73d91604844b1bd0f086c69081637e1d53d8d410045f438a3b224200
  | 2 => 0x5764c9100063bbaee2b1a40038dc831d9414c001938e831ac090802ab61352d89400047bc3ac230a808dad58198063504018b8e632ac4880baa7a0c50d91310064e3a6c6b024226c9c64dcd414c4010fd0e32ac88800387d955418d4149d5bc22c230a86008bf845d9434405b1790fb226290802ab60a65d91310245f43ee8b1220038de87dcd624411756f02b28c898802ada1210d85321754e41ac920a2000a9d84d4f63500018bae639eca88002a760e70d91210054f41c21b2242008bd87843644c44d53908b1c6288002a761051d8d410051ec2841b22620087e87d95644400156b02106c898803171d463581410051e42ae1b22620a8ec8758932904031f100baac6908030f19774485100052ec28e9b1a4200ab58114364484f5958e4aa2c888002a761075d8d4116d5741063b2242019da80dce214c0011bb0f320c69080327dd373591210062e39ecab122000c3f751d162440011bf06baac890002a760c20d913102c77c3aa5b128200cb774dc563480011bd0fb1ac4a0803a5193714c9310061fb2ee890a20048bc845d932440010ff0abb2869000297a1740d8d210061fbaec8b024200c6c65dc9634405b55904b2482880030f1d3655891035c5f43ec898a4200a5d85107634840b0fd0fbaac6880222f61f61905400054f41ce1b2242008bf845d563480011bd0fb1ac0a08b62f21b745812116d57410e7b22420a8dc8758d329047b4ed02396ca880022fa1c30d912101c6e41aeab224000c3c75d91604840117d0e28ec8988021fe157650d1000c7b436e2a1a20008df835d562440011df04bb264880161f21576509100062e3a8e6b1220038ee87d89325000147d0b310c8988031bd977258d1002e1f3aaa9b0282008de87143635040b1790eaa2c8880122fa1276485300045ec24ec98a407dcd7761cd21c400156d02286c8908023761c50d8d210061e3a8e8b122000a9d839c3644c4011df04baac688002ae20165d91210065a3a6e2b1a42038de839d9414800159b0532ec6a080a3b20975591300064fb26e6b024200a9e8414363484010fb0bbb264881ffa39c86418d210052f42cc5b1a82038dc835d56244001998e7b92c8880030f5d754d91210061eba8ebb226200c9c74dcd62440011df04bb28488002a7a1260d8d2143e5bb88c8b1a4200a9e84980634844b5ab02386c6908032b1cb64581310046fc1aeab226202acc8258d32440018e8ebb8ac6900022fa1f6458d210070fa9ca7b224200c74651c5434400156d02286c8989a3631d1324c52100566c14ca31a8225ace8214363484031bd0db9a82980021fe1576509100064fb26e6a0a42008f7875846150c0b0f90ab86c8988031b197725911002c3f43eeab0482048bc845d563484015390caa0c6a0803175d753d8d410052f42883b1a42009d4815d1324c00153
  | 3 => 0x3b2a2000ab5841476150c0b17f0eaa6c8909161fa1f21d951002c3f43eeab1220008fb805d5644c8011bd0e206c690803171d7635814100666396c6b02820a8f4815d46150c018b8cbb9ac888002976166218d410146f43ec69928000c5c65dcd414400147f08b9eca8809aa7a1352d8d410046fc1aeca1c422dea462dd1214400b0fd0bbb2648800e3720d765091000672310e2b126000c5f75dcd624400117f08baac69080395d4651d8d410054ec1cc432262008de87143634840147d0b316c89880317dd773591100070ec28c9b1a42008ef825da315004b998e5b1a62908023de0575591310061e3aec8b026200c3c7419563440551b90db9ac0a080237e0d75591210062fb2ee6b1220018f8805d5644c8010ff0abb4829000297a0e42d9510006ca3a0e690a200587e87dd563480018becbb9a828800333dcc72591100064e3a6c698a4200a9c8359764484071b906b8ec0a102a3d20575591320043fc2ae1b22646bc9c73193624c401d1ae5b20c690802aba0850d91310054f41cc03224200ae4864c9214400917d0fba2c6880122f210764c5400051ec2ce5b226200a7585107614c84d53d0828ec6a080237e0d7650d101554f424e1b1a8200ae5820c761480011bf06ba6c48819e2fa1b744c5210061e3a6cab1a2086ad58199463484018becbb9ac8880029761464d8d210045ec3ea7b224200c5c75dcd62440014bb0a320c6908038d55351d85400072ba8ca3b1a422dcb476dd121440011ef02baac899002a7e1165d8d210061e3aee8b1a40008f787584614800187eebba2c69002a3d20575591200051f42ce5b2262008f7875846150801958edb226490802a760e65d91210052ec18e5b2a2000c3c74d95314400157700b2ec890803171d7735911000657b26e4b026200c9c74dcd634400117b0e286c8988161f2157650d200054ec18e5b226200aae82997644c45d53d06106c8988033518c7158d420545e43aa8b246200ad681083635040117b0fa96c8988022fe1175591210064e39ec8a0a2000cac74d89214400193887ba2c5188028fe1570d91210065a3a0e2b1a4000c5f7518d60504014e90ab08c2a00021fe1570d913101567436c4992607ecd77118d60484019a8e7b8ac8909ef271cd54591100064e398c8b02420a8bc8755164c40011bb0f328c69080237a1c20d8d410054ec24c031a8200c3f65dd163440019ae8638ac8990030f1977458d100054ec24ca31a8200c9c74d8d314410b93cedb20c690803175d753d8d210066639ec490a2000ccc7218d6050463938c9ba264980031bdd47258d100047dc02eab224200c5c73d954144001998ec99242980021f61776509100062fba8e6b12200587c855da414800153b07086c890a06a7a186418d210043f43ecab122000c3c7419562440019cee438ac6900023de0
  | 4 => 0x1500091bd0fb1a86908031b1d47258d100043f438cab122026a9e841d763504018b8e632ac8880161f2157650d100063a32ee2a1a20668de86dcd4148401b8843b9a82908030fdd4645813100c6fc3ac718a2026c9c64dcd41484011bb073b242a00122fa1f7458d210054fc1aca322620587c855c762500011bb0f328c6a08031b1c865591100146f43ec69928200e1e85193634850753d09320c690802a761210d8d410062e39ecab2220048bc845d563440071bd0fb9ac888002b560c21d853016d5ac08e1b224200c9c64dcd644840153b06286c890802a7a1270d8d210145f43ec8a126200ad581083635040187ae83a6ca8802b3908572185430061fbaee8b1a2000ab681083644c4014bd0a326c6908021fa1c6558d100056ac1c2030a640087e871d5644400153b09086c690802ad211611853201c5f43ec8a1a4200c5c65dcd2144001878ea322c0988b6ad60775d91210061fba8c8b024200c6f751c964440014ed0b908c2a180e3720c76485300245e422e430a60048bc841d9215004d53d08106c6a0803171d473591100062e3aec6b0242008ef825d9434400155b04286c890802a7a1265d8d2102c5fc3aa9b226000a9e8499463484018d8ea392c88800317dd7635812102c3e42ae030a6431a9c8458d32440015b100b2ec6908030f1d365485100046fc1aeca122000c5f7518d604840157100b28c89080237a1f63581210045f438c8b026200ad48358461508011bf06bb286909169d60472d951002c3f436eab122000c5f65dcd214400155b05328c8908062fe1d649051016e56396c8a0a4200c5c73d9521440051dd0fb92c88800335dcc71591320043f438eab122000a5e850836350401c3d0a320c690a42b5e0d611853235d4f436c89926200acd82994634840117d0e106c898802ada0470d912147d6bc0aca31a8288c9e76191324c4015b100b28c690802b560450d8d410066a218e2b22640087e871d563480031f50db824288003a5190714c93100636396cab222045c7a76d97104400b0fd0fbaac8880029ba0831d9510055664326498a4200c3c75191604840153b09328c69080317dd763581410054ec24cbb1a42038dc835d5644400153b08286c69080a3b209768c5400062e32ee6b1220018de86dce214c00196e8038ac89923335dc463589410055ac08a1b226200a9f835976448401c6ea328ec89880e3720d74d89100054f41c85b222000c9f741cd6244001938c9b9ac0908022fe117650d2000c5f436e898a8000a5e8519063484014bb0ba06c69082a7321d324c5210046f43843b1a82008df835d932440011f700baac69080a3720d74d89300052f41843b2a2000a9e84147634851153d0db2462988023de057558d200070ec28c831a420a8f4815d461500018deebb92c688002a760e60191310043ec3e4
  | 5 => 0x1c00a01058008020f8000003408807070220001e3081a0002402876068103d0964c87a020e805940058060381000c9405800448080001a0129400006098b0078040f84280a20190de038ba1681c020071b002638125f012150040491e008000186600056130086e800010f0040000587e1c01a239e41480000b500001605822060004585c360be1100a0b00a000480004e25020118020000455336058300000429006080001a9780185a030460390a139a80000608006058160c81015060010241a13f388000100200004198040f830098145f8041db22118008e85408800000c6060202580600006080000f0000d83000000040040703a0204c00054000041d802000320100e0f8460000003010010300180a1e02c000080204c01012090203b0ce0003a229560e014001840300602940009740380e020000880a67816010d20224200928018dd83dd7614c0011bf06baac9108028fe1172d95100045fc22e3b026400c3c65dd1314400187eebba2c4880022fe1175591313de4e39aa8b2442018bc845c76050801878ebba2c488067331db634c9210056dc02ca31a4225ccc625ca314c4011f700baac4880161fa17765091000657ba0e4b1a2000a9d83983644840187ecbba2c48800237a1c635894100c5f436e890a8000a9f84594634840153b0828ec6908030f5d754d91310045f43ea7b224200a3c855c3644840153b08286c6a080e3720d75592214064f3b0c831a4200ab684840614c80193ee839ac89080327191728c53100c5f436e910a80058bf87553644c4051d904baac688222a7a195418d411754f41843b22622e8bc86dd1604c4018beea39ac8881ffa5c846418d210061fb2ee898a2000c3f751d16344001b28e839a43880122f2117558d200054ec26a7b1a82008dd87843635040193ee9b9ac4880021fa1c75582410054ec24c431a8200ce472dc563440073990e992429800327dd0735911000657ba0e4b2220008be871916348401938e9b9ac6908029b60831d95100043fc2ae3b128000da421dd131484018e8ea38ac69000297a1721d8d410063bba8e2b1a40008bd87994644c40153d0732ec890803171d463581210146ec1eebb2264018bd84dd76
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xffc84621d07348510
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x94b
  | 7 => 0x94c
  | 8 => 0x94d
  | 9 => 0x94e
  | 10 => 0x2
  | 11 => 0x138b
  | 12 => 0x138c
  | 13 => 0x138d
  | 14 => 0x138e
  | 15 => 0x98c
  | 16 => 0x98d
  | 17 => 0x98e
  | 18 => 0x9cb
  | 19 => 0x9cd
  | 20 => 0x9ce
  | 21 => 0xa0b
  | 22 => 0xa0c
  | 23 => 0xa0e
  | 24 => 0xb09
  | 25 => 0xb0c
  | 26 => 0xb0d
  | 27 => 0xb0e
  | 28 => 0x1409
  | 29 => 0x140c
  | 30 => 0x140d
  | 31 => 0x140e
  | 32 => 0xb49
  | 33 => 0xb4b
  | 34 => 0xb4d
  | 35 => 0xb4e
  | 36 => 0x1449
  | 37 => 0x144b
  | 38 => 0x144d
  | 39 => 0x144e
  | 40 => 0xb89
  | 41 => 0xb8b
  | 42 => 0xb8c
  | 43 => 0xb8e
  | 44 => 0x1489
  | 45 => 0x148b
  | 46 => 0x148c
  | 47 => 0x148e
  | 48 => 0xcc9
  | 49 => 0xccd
  | 50 => 0xcce
  | 51 => 0xd09
  | 52 => 0xd0c
  | 53 => 0xd0e
  | 54 => 0xe89
  | 55 => 0xe8b
  | 56 => 0xe8e
  | 57 => 0x138956
  | 58 => 0xb0956
  | 59 => 0x94b16
  | 60 => 0x140956
  | 61 => 0x95416
  | 62 => 0x124b
  | 63 => 0x209
  | 64 => 0x249
  | 65 => 0x289
  | 66 => 0x1549
  | 67 => 0x16c9
  | 68 => 0x1849
  | 69 => 0x14c9
  | 70 => 0x2c9
  | 71 => 0x138b16
  | 72 => 0x4b
  | 73 => 0x139416
  | 74 => 0x1709
  | 75 => 0x15c9
  | 76 => 0x168b
  | 77 => 0x12cb
  | 78 => 0x1889
  | 79 => 0x1609
  | 80 => 0x180b
  | 81 => 0x130b
  | 82 => 0x9d456
  | 83 => 0x4c
  | 84 => 0x124c
  | 85 => 0x9ccd6
  | 86 => 0x150c
  | 87 => 0x128c
  | 88 => 0x9ce96
  | 89 => 0x18c9
  | 90 => 0x1789
  | 91 => 0x180c
  | 92 => 0x130c
  | 93 => 0xa1496
  | 94 => 0x4d
  | 95 => 0x124d
  | 96 => 0xa0d16
  | 97 => 0x150d
  | 98 => 0x128d
  | 99 => 0xa0e96
  | 100 => 0x168d
  | 101 => 0x12cd
  | 102 => 0x24b
  | 103 => 0x28b
  | 104 => 0xccb15
  | 105 => 0x16cb
  | 106 => 0x184b
  | 107 => 0x28c
  | 108 => 0x154c
  | 109 => 0x184c
  | 110 => 0xb9496
  | 111 => 0x154d
  | 112 => 0x24d
  | 113 => 0x16cd
  | 114 => 0x20c
  | 115 => 0x18cb
  | 116 => 0x178b
  | 117 => 0x188c
  | 118 => 0x160c
  | 119 => 0x20d
  | 120 => 0x170d
  | 121 => 0x15cd
  | 122 => 0x104b
  | 123 => 0x104c
  | 124 => 0x2d851
  | 125 => 0x24053
  | 126 => 0x25253
  | 127 => 0x28253
  | 128 => 0x29453
  | 129 => 0x25493
  | 130 => 0x25853
  | 131 => 0x24293
  | 132 => 0x148253
  | 133 => 0x149453
  | 134 => 0x24bd3
  | 135 => 0x296d3
  | 136 => 0x58a
  | 137 => 0x29554
  | 138 => 0x28954
  | 139 => 0x299d4
  | 140 => 0x25555
  | 141 => 0x24955
  | 142 => 0x194c
  | 143 => 0x259d5
  | 144 => 0x25453
  | 145 => 0x29493
  | 146 => 0x25455
  | 147 => 0x29494
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1301
  | 6 => 2575
  | 5 => 759
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
  | 8 => 2*((h/34+packedAt gbK8 (1560+(h % 34)*6) 6) % 60)
  | 7 => 2*((h/461+packedAt gbK7 (48137+(h % 461)*11) 11) % 1301)
  | 6 => 2*((h/893+packedAt gbK6 (123600+(h % 893)*12) 12) % 2575)
  | 5 => 2*((h/260+packedAt gbK5 (44781+(h % 260)*10) 10) % 759)
  | 4 => 2*((h/1+packedAt gbK4 (70+(h % 1)*1) 1) % 1)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffe07c03f01f03fffffffff067918fa207fff
  | 1 => 0x7807f8003fffffc1ff81ff0019a6e7643f9e7c
  | 2 => 0x8007ffffc001fffe0ffe0fffe1c70787c3e38f
  | 3 => 0x7fffffffe00000ffff000fe07f807fc03f0
  | 4 => 0x7fffffffffffff0000000fff80007fffc00
  | 5 => 0xfff800000000000000000000fffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x887401440b20501292a3112a0208082a202cb5
  | 1 => 0x50925801154ab5412590aa0608a263640d965c
  | 2 => 0x102aa99400929a409548cd461470584c2c30a
  | 3 => 0x22734eda6ac01108e79c818b607b8077403e0
  | 4 => 0x4445c73638f1ce39c0210060dff80003bb7800
  | 5 => 0x6780003800c00c2100400080fdf5d6d0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafce8a8a0feeaeeeafce8a8a0feeaeeeafce8a8a0feeaeeeafce8a8a0feeaeeeafce8a8a0feeaeeeafce8a8a0feeaeeeafce8a8a0feeaeeeafce8a8a0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40511
namespace PEqualNP.Outside.L_meta_40511
open PEqualNP.Outside.L_meta_40511.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 5 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 25 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 91 := block_range (n:=91) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 91 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 44 := bs0_5_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 3 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 21 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 99 := (concat bs2_4_0 bs2_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 46 := bs2_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
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
theorem bs3_4_0 : Interval s3Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 90 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := bs3_5_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 5 := bs5_2_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 30 := block_range (n:=30) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 414 := (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 (concat bs5_4_288 bs5_4_384)))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 40 := block_range (n:=40) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 616 := (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576)))
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
theorem bgb_5_384 : Interval gbAtlas 5 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_480 : Interval gbAtlas 5 480 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_576 : Interval gbAtlas 5 576 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_672 : Interval gbAtlas 5 672 87 := block_range (n:=87) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 759 := (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 bgb_5_288)) (concat (concat bgb_5_384 bgb_5_480) (concat bgb_5_576 bgb_5_672)))
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
theorem bgb_6_2496 : Interval gbAtlas 6 2496 79 := block_range (n:=79) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2575 := (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 bgb_6_1152)))) (concat (concat (concat bgb_6_1248 (concat bgb_6_1344 bgb_6_1440)) (concat (concat bgb_6_1536 bgb_6_1632) (concat bgb_6_1728 bgb_6_1824))) (concat (concat bgb_6_1920 (concat bgb_6_2016 bgb_6_2112)) (concat (concat bgb_6_2208 bgb_6_2304) (concat bgb_6_2400 bgb_6_2496)))))
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
theorem bgb_7_1248 : Interval gbAtlas 7 1248 53 := block_range (n:=53) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1301 := (concat (concat (concat bgb_7_0 (concat bgb_7_96 bgb_7_192)) (concat (concat bgb_7_288 bgb_7_384) (concat bgb_7_480 bgb_7_576))) (concat (concat bgb_7_672 (concat bgb_7_768 bgb_7_864)) (concat (concat bgb_7_960 bgb_7_1056) (concat bgb_7_1152 bgb_7_1248))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 60 := block_range (n:=60) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := bgb_8_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 20, 22),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafce8a8a0feeaeeeafce8a8a0feeaeeeafce8a8a0feeaeeeafce8a8a0feeaeeeafce8a8a0feeaeeeafce8a8a0feeaeeeafce8a8a0feeaeeeafce8a8a0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4243105952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40511.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.and,[1,6]⟩,⟨.or,[0,7]⟩,⟨.and,[0,6]⟩,⟨.or,[4,9]⟩,⟨.and,[5,8]⟩,⟨.or,[1,2]⟩,⟨.or,[3,8]⟩,⟨.and,[10,13]⟩,⟨.and,[12,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243105952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4243105952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40511

open PEqualNP.Outside.L_meta_40511 in
theorem PEqualNP.Outside.L_meta_40511 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4243105952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4243105952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
