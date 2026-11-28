import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37223.Model
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


end PEqualNP.Outside.L_meta_37223.Model

namespace PEqualNP.Outside.L_meta_37223
open PEqualNP.Outside.L_meta_37223.Model
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

def SBf (j : Nat) : Nat := [7, 5, 7, 6, 6, 7].getD j 0

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

end PEqualNP.Outside.L_meta_37223

namespace PEqualNP.Outside.L_meta_37223
open PEqualNP.Outside.L_meta_37223.Model
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
end PEqualNP.Outside.L_meta_37223
namespace PEqualNP.Outside.L_meta_37223
open PEqualNP.Outside.L_meta_37223.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xd431
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
  | 2 => 0xe03f01fff03f03ff0f81e0fc0fff07c0ecb3cc
  | 3 => 0xffc001fffffffffff001ff000ffffffff0c3ff
  | 4 => 0x1ffffc003fffffe00000ffff800ff03f0
  | 5 => 0xfffffe00000003fffffffffff0000000fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2284100460821040118a211462884a4a051615
  | 2 => 0x498a72c8a39455cb06a8e8d8a5b946866cb2cc
  | 3 => 0x8512a5510528c29560415a4109529534b0c16a
  | 4 => 0x162cd9a24a0e9b66bb6c10924e6ce218df03b0
  | 5 => 0x1830e1c38c30e3b8cc719ce380708420fae800
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafa00aa00faaaaaaafa00aa00faaaaaaafa00aa00faaaaaaafa00aa00faaaaaaafa00aa00faaaaaaafa00aa00faaaaaaafa00aa00faaaaaaafa00aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37223
namespace PEqualNP.Outside.L_meta_37223
open PEqualNP.Outside.L_meta_37223.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x52995800c5910042a009a166010000000003230025120028d46487800000007000000a000c013000001f0074014000120000440044e0001b385502a1040b9e003800283080400100005040200380ff43fe43fd43fc43ff42fe42fd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xa2b84a899988800001f9e982c80001725108a80098029888f1400228005aa9f00131a95a197800c27990000230423801e2800292420868002800ca10e9496802b2207a59c00000e0006071b112a00000b900d001a092600001ca026801d1d921280000000000f850000010200150b00002c2480001b80831391800183960d800027058241410000008680420041c1c04200000000000000800041004080c0016eea2a1dd14543b7290876d5210ebca7215754e42bb28c85755190abca6215754c42af28e655d538caeea2995d14532e7a9265ce424cb9a849975d4532ae28a65d4514caa8a2995794c32af29e835d53d06dca5a0db54b41afa9a835c53506baa518d794631b7290636d520c79ca418d754831e6a90634d520c6bca218f594431eba0863d4410c67ca990cf55321af29e435d53c879a6590f50c721afa9c435c53886bea690d714d21e6992435e53086baa610f50c421afa9a815c53502dea4a05b14940bba8a817451502bca6205754c40b7290816d52102eca2205d54440b7296616d52cc2eca3185d54630af29e415d53c839a65104f950209eaa0415e53082baa610734c820bb288417551083a863885794e10aea9c213f5444278a88857d4d10ae29a216f52442d8a488750c510
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x1800000000000068072422c98000a400a0008600000000e012000020000a8cbb001601400000000002200001e00010000200000102546154c42b1586424cb464214532d1508514ca4d6214d41d1185520c6c662d0431d154b410c7455210431c355132c86c4614cb21c595031c86c5620c721931953248655650c4219518553c82c4614ca20c355132082c4614c820d14c951082c5620c7109358a5384314540c510b15883144344520c510
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x1900a028000223bb2a5a086381550614cb21c0ca8b106390e055418532083022a2c418a21115d8520c510
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 90
  | 3 => 25
  | 2 => 6
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
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (802+((h/14+packedAt s2K5 (704+(h % 14)*7) 7) % 75)*7) 7
  | 4 => packedAt s2K4 (2670+((h/30+packedAt s2K4 (2430+(h % 30)*8) 8) % 130)*8) 8
  | 3 => packedAt s2K3 (998+((h/8+packedAt s2K3 (950+(h % 8)*6) 6) % 62)*6) 6
  | 2 => packedAt s2K2 (302+((h/2+packedAt s2K2 (294+(h % 2)*4) 4) % 9)*4) 4
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf83fffffffffff03fe0ff07ffffffffc8c7fff
  | 1 => 0xffc07e1f03ff83fc3ff0ff8703e0ff0373b27c
  | 3 => 0xffff801ffc1fffffc000fff803ff0fff83c38f
  | 4 => 0x1fffe003ffffff000003fff003fc03f0
  | 5 => 0xffffffe0000003fffffffffffc000003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8850801080100004601100918a111280414b5
  | 1 => 0x51931422394a152c1a5072822968aa1931b25c
  | 3 => 0x620a255450d453558148ab50425a8cd382c30a
  | 4 => 0x472c5998a2875b9aed6a0a40939cc863dc03e0
  | 5 => 0x84306110c31862e3318ccc64e0100082eb6800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaaa88aa00eeeeeeaaaa88aa00eeeeeeaaaa88aa00eeeeeeaaaa88aa00eeeeeeaaaa88aa00eeeeeeaaaa88aa00eeeeeeaaaa88aa00eeeeeeaaaa88aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37223
namespace PEqualNP.Outside.L_meta_37223
open PEqualNP.Outside.L_meta_37223.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x2000092981df32dd32de31dc31ee21ec21
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x22a8a299710c421
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
  | 4 => packedAt s3K4 (102+((h/2+packedAt s3K4 (96+(h % 2)*3) 3) % 8)*4) 4
  | 3 => packedAt s3K3 (56+((h/1+packedAt s3K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x81fffff80ffe0c1ff87fc3ffffc1fe018cfe7c
  | 1 => 0xfe07e0ffffffffe0ff83fc1c07fffffe7333ff
  | 2 => 0xfff800fff07fffff0003ffe007fe1fff83c38f
  | 4 => 0xffff800ffffffc000007ffe003fc03f0
  | 5 => 0xffffff0000000ffffffffffff8000003fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8c30c808e10454031814c0a471d1321884563c
  | 1 => 0x14910111242800a068814408924244a83130d5
  | 2 => 0x28425aa243514d4d0452aac124b5195382c30a
  | 4 => 0x71659cc48a1d6e76b558228247399063dc03e0
  | 5 => 0x418610870c618b98c6633313802001836ba800
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeac8c8c0c0eeeeeaeac8c8c0c0eeeeeaeac8c8c0c0eeeeeaeac8c8c0c0eeeeeaeac8c8c0c0eeeeeaeac8c8c0c0eeeeeaeac8c8c0c0eeeeeaeac8c8c0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37223
namespace PEqualNP.Outside.L_meta_37223
open PEqualNP.Outside.L_meta_37223.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x8ee21ec21
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
  | 0 => 0xffffe07ffff083fc3fc3fffe1fffe0113f3fc
  | 1 => 0xf07c3ff83e1fffc3fc3fc381fe1c0ffeeccccf
  | 2 => 0xff803fffc01ffffc003ffc01ffe00fff0f0f0f
  | 3 => 0x3fffffe00fffffc00001fffff003f00ff0
  | 5 => 0xffffc00000000ffffffffffe00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x6108023084001004404c048c6024621801515c
  | 1 => 0xa5104451902a0141c4144114a208a4a864c4c5
  | 2 => 0x422aa8a20d548a9c222aa829554149530b0b0a
  | 3 => 0x8a5331052906aceaaa82204199938063b00ea0
  | 5 => 0xc6221c63198cf333333327011020183dea000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaeac0eac0eeeaeeeaeac0eac0eeeaeeeaeac0eac0eeeaeeeaeac0eac0eeeaeeeaeac0eac0eeeaeeeaeac0eac0eeeaeeeaeac0eac0eeeaeeeaeac0eac0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37223
namespace PEqualNP.Outside.L_meta_37223
open PEqualNP.Outside.L_meta_37223.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1c813be00140825a4dfa622e5b190034aba0600000700003560b0c3434480007801dab0050b176eb928a467d4a13a40209626c00b00cc01e001800c00000225e0151c50c83a41e2003d05040818f003808100042802c000040c08400bda8287785050eeca221dd54443bba8a85745150af4a0215e540429f2a6653d54ccaeca3995d547329f2a4653d548caf4a1195e54232b7a92836c52506bca620d754c419faa2633c544c6dea498db14931bda826378504c67ca818cf550319faa2433c544867ca810cf55021af298435d53086f4a010de54021afa9a815c53502dca4205b548409faa2613c544c27ca8184f55030b7290616d520c2eca2185d544309faa2413c54482bea6905714d20bba8a4174514827ca8104f550209f2a6213d54c42bca7885754f109f2a4213d54842dca5085b54a10
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (718+((h/13+packedAt s5K5 (640+(h % 13)*6) 6) % 49)*7) 7
  | 4 => packedAt s5K4 (1875+((h/21+packedAt s5K4 (1728+(h % 21)*7) 7) % 84)*7) 7
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x7ff03fffff8307c1fffc1ff0ffffe011e73fc
  | 1 => 0xfffffc0fc1ffff801f07fffff0f01ffe13fccf
  | 2 => 0xf83ffff001ffffffe007fe0fff001fffe38f0f
  | 3 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 4 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x309118a2904250150549d0930914d21906315c
  | 1 => 0x51222864229422820b82632590a144aa10d4c5
  | 2 => 0xa29451019522152d2044948a2a029951630b0a
  | 3 => 0xc52882492034a9ca5290210cc4cb0062b80ea0
  | 4 => 0x630e38e39c73e739ce739c0888c1183dfe000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0fac8eac0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37223
namespace PEqualNP.Outside.L_meta_37223
open PEqualNP.Outside.L_meta_37223.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c38182140400004085000238085000000101ffd5001fe54007f55007fc5401ffd4c01fe53007f54c07fc53007fd0c01fe43007f50c01fc4301ffd4805fe52007f54805fc52007fd0805fe42007f50805fc42007fcc805fe32007f4c805fc3201ffd4401fe51007f54407fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc31017fc8401fe21007f48405fc2101ffd4003fe50007f54003fc50007fd0003fe40007f50003fc40007fcc003fe30007f4c003fc30017fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x24001ff1012000ffe6090007fe3048003fe9824001ff0c12000ffe409000bfb2048003ff1024001fb8812000ff84090007ec2048003fc1024001ff8412000ff42090007fc1048011ffb2e2000bfd9710057fccb8800efe65c4001feb2e2000bf59710047f8cb8800efc65c4011ffb262000bfd9310007fcc98801efe64c4001feb262000bf59310047f8c98801efc64c4015ffaa62000ff95310007faa98802bfc54c4011ffb1e2000bfd8f10007fcc78801afe63c4001feb1e2000bf58f10047f8c78801afc63c4015ffa9e2000ff94f10007faa78802bfc53c4001ffa1e2000ff90f10007fa8788003fc43c4011ffb162000bfd8b1004ffcc58800afe62c4001feb162000bf58b10047f8c58800afc62c4015ffa962009ff94b10007faa588027fc52c4001ffa162009ff90b10007fa8588027fc42c4001ff9962009ff8cb10007fa6588027fc32c40037f30e200affd4710047fca388003f651c4001fea8e2000fd54710047f8a388003ff41c4011ff20e2000ff50710047f88388003ff31c4011ff18e2000fd8c710007fa6388003f531c4011fe18e2009ffc8710047fc4388003fd21c4011fe10e2001bf5831000ffea188007fe50c4003fea862001ff1431000ffe8188007fe40c4003fea062001ff1031000ffe6188007fe30c4003fe9862001ff0c31000ffe4188007fe20c4003fe9062001ff0831000ffc2188007f610c4003fd0862001ff0431000fe82188003ff65440017fb2a2000dfd9510004feca88017fe65440077f32a2000ff59510005faca88017fc65440077e32a2000df1951001cf8ca88003ff64440017fb222000ff9911003dfcc888003fd64440017eb222000ff1911003df8c888017ff5444001ff2a22000ff5511002ff8a888003ff63440017fb1a2000ff98d10035fcc688003fd63440017eb1a2000ff18d10035f8c688017ff5344001ff29a2000ff54d1002ff8a688003ff4344001ff21a2000ff50d10007f88688003ff62440017fb122004ff98910015fcc488003fd62440017eb122004ff18910015f8c488017ff5244009ff2922000ff54910027f8a488003ff4244009ff2122000ff50910027f88488003ff3244009ff1922000ff4c910027f86488006ff614400bffa8a2000ff94510007eca288003fd5144001faa8a2005ff14510007fe8288003fe4144001fea0a2000ff10510007fe6288003fe3144001fb18a2000ff4c510007ea6288003fc3144009ff90a2000ff88510007fa4288013fc21440037fb022001ffd411000ffca088007fd5044003fe2822001ffd011000ffc8088007fd4044003fe2022001ffcc11000ffc6088007fd3044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044001fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0xbfc32cc00dffb0e6006ff98730005fcc39801bfd61cc0017eb0e6006ff1873007ffea398003fe51cc001fea8e600fff14730007fe8398003fe41cc001fea0e6000ff10730037fe639801bfe31cc00dfe98e6006ff0c730077fe4398003fe21cc001fe90e600eff0873000dfac198007ff50cc003ff2866001ff5433000ff8a198007ff40cc003ff2066001ff5033000ff88198007fe30cc003ef1866001fe8c33000ff86198007dc30cc003ff9066001ff8833000ff84198007fe10cc003fe0866000ffd9530005feca98037fe654c0077f32a6000ff59530005faca98037fc654c0077e32a6000ffd9130005fec898003fe644c00f7f3226000ff59130005fac898003fc644c00f7e322600dffd5130007fca898003fd544c01bfe2a26001bfd8d3006ffea69801bfe534c001ef29a6000ff54d30007baa69801bfc534c001ffa1a6006ff90d30007fa869801bfc434c001ffb126000bfd8930067fcc49800afe624c001feb12600cff18930015f8c498037ff524c019ff2926000ff54930067f8a498003ff424c019ff2126000ff50930067f8849801bff324c019ff1926000ff4c930037f86498003ff614c0017fb0a6000ff98530007fac298003fc614c0017e30a600dffd4530007fca298003fd514c01bfe28a6000ffd0530007fc8298003fd414c001fe20a6006ffcc530007fc6298003fd314c00dfe18a600cffc8530007fc4298003fd214c019fe10a6001bfd813000ffea098007fe504c003fea826001ff1413000ffe8098007fe404c003fea026001ff1013000ffe609801bfb304c003ff1826001f78c13000ff86098007dc304c003fc1826001ffc813000ffc4098007fc204c003ff0826001ff04130007feca90002ff6548017ff32a4003bf99520007faca90002fd6548017fe32a4003bf19520007fec890002ff6448001ff3224007bf99120007fac890002fd6448001fe3224007bf1912005ffea890003fe5448001feaa2400bff15120007fec690002ff6348001ff31a4006bf98d20007fac690002fd6348001fe31a4006bf18d2005ffea690003fe5348001fea9a400bff14d20007fe8690003fe4348001fea1a4000ff10d2000dfec49000bff5248005ff2924002fb94920017faa490003ed5248005fe2924002ffd0920017fc849000bee4248005fea124000fb50920017f8849000bff3248005ff1924002fb8c920017fa6490003ed3248005fe1924000ffd8520005fec290003fe6148001feb0a4000ff18520005f8c29002fff5148001ff28a4000ff5452005ff8a290003ff4148001ff20a4000ff50520007f88290003ff3148001ff18a4000ff4c520007f8629000bff2148005ff10a4000fb88520017fa429000bfc2148005f610a4001bfd812000ffea090007fe5048003fea824001ff1412000ffe8090007fe4048003fea
  | 2 => 0x4003ffcc7a001afe63d000ffeb1e8000bf58f4003ff8c7a004fff53d0001ff29e8000ff54f4009ff8a7a001fff43d000fdfa1e8007ff90f4003ffa87a0003bd43d000ffe21e8007ffd8b4003ffcc5a000afe62d000ffeb168000bf58b4003ff8c5a000afc62d0027ffa968012ff94b40007faa5a004bfc52d000fffa168007efd0b4003ffc85a001ffd42d0001dea168007ff10b40007fe65a004bfe32d0001fe9968012ff0cb4003ffec3a001ffe61d00017f30e8007ff58740005fac3a001ffc61d0027ffa8e8000ff94740007faa3a004ffc51d000fffa0e8007ff907400077c83a001ffd41d000ffe20e8007ef10740007fe63a0003fe31d0001fe98e8000ff0c740097fe43a0003fe21d0001fe90e8012ff0874000dfac1a0007ff50d0003ff2868001ff5434000ff8a1a0007fe40d0003df2068001fe9034000ff881a0007bc40d0003ff1868001ff0c34000ffe41a0007fe20d0003fe1068001ff8434000ff821a0003ff65500017fb2a8011ff9954001dfccaa0003fd65500017eb2a8011ff1954001df8caa0006ff6450023ffaa28007ff951400077ca8a0003fd5450001deaa28007ff15140007fec6a0002ff6350001ff31a8000ff58d40007f8c6a001afc6350023ffa9a8000ff94d40007faa6a0047fc535000fffa1a8000efd0d40007fc86a0003fd4350001dea1a8007ff10d40007fec4a0002ff6250021ff3128002bf98940007fac4a0043fc62500057e3128011ffd4940087fca4a0003fd5250021fe2928007ffd09400077e84a0043fe4250001fea128000ef5094003ff884a0003ff3250021ff1928000ff4c940087f864a0003ff61500017fb0a8000ff98540007fac2a0003fc61500017e30a8011ffd4540007fca2a0003fd5150023fe28a8007ffd0540007fc82a0003be4150001fea0a8007ff105400077882a0003ff3150001ff18a8000ff4c540007f862a0043ff2150001ff10a8000ff48540087f842a0006ff6050003ffa828001ff9414000ffaa0a0007fc5050003ffa028007fed014000ffc80a0007be4050003fe2028001ef1014000ff080a0007fe3050003fe1828001ffc814000ffc40a0007fc2050003ff0828001ff04140037fecb9801aff65cc00dff32e6003bf99730037facb98002fd65cc00dfe32e6006bf19730037fec99801aff64cc00dff3266007bf99330037fac998002fd64cc00dfe3266006bf1933007ffea998003fe54cc001feaa6600fff1533000dfcc79801bff53cc00dff29e6006f794f30037faa798003dd53cc00dfe29e6006ffd0f30037fc879801bfd43cc00dfe21e6006ffd8b30037fcc59800afe62cc00dfeb166000bf58b30037f8c59800afc62cc01fffa96600eff94b30007faa59803bfc52cc001ffa16600eff90b30007fa859803bfc42cc00dff9966006ff8cb30037fa659801
  | 3 => 0xf98c4208ff8c621007fa6310823fc3188405ff90c4202fbc8621017ee4310823fc2188405fa10c4208ffd82210bffcc110806fe6088401feb044200bf58221047f8c110806fc6088431ffa844217ff942210bff8a11085ffe408842ffe2044217ff8c2210bff8611080bff2088405f79044202ff88221017f8411085ffe1088411fe0844200ffd9521005feca9085bfe65484077f32a4200ff59521005faca9085bfc65484077e32a4200ffd9121005fec890803bf64484015fb224200ff9912103dfcc890803fd64484017eb224200ff1912103df8c890803bc64484015e3224216ffd5121007fca890803fd544842dfe2a24200ffd8d21005fec690803fe634840d7f31a4200ff58d21005fac690803fc634840d7e31a4216ffd4d21007fca690803fd534842dfe29a4200ffd0d21007fc8690803fd4348401fe21a4202bfd8921017fea49080bfe5248405fea924202ff14921017fe849080bfe4248405fea124202ff10921017fe649080bfe3248405fe9924202ff0c921015fec29085bff5148401ff28a4200ff545210b7f8a290803ff4148401ff20a4200ff50521007f88290803ff3148401ff18a4200ff4c521007f8629080bff2148405fb90a4202ff88521007dc429080bfc2148405f610a4202fd08521007fec090802ff604842bff3024201bf98121007fac090857fc60484037e3024216ffd41210affca090857fc504842bff2024215ff101210affc6090857fc3048405ff9024202ff88121017f84090857fe104842bfe0824201bfd9550007fec8a8002ff6454001ff322a000ff59150007f8c8a801efc6454007ffaa2a003ff9515001ffaa8a800ffc5454001ffb1aa000bfd8d50007fcc6a8003fd6354001fe31aa006bf18d5001ffea6a800f7f5354007ff29aa003ff54d50006faa6a800ffc5354001ffa1aa000ff90d50007fa86a8003fc4354001ffb12a000bfd89500a7fcc4a800afe6254001feb12a014ff18950015f8c4a800fff5254007ff292a003ff5495001ff8a4a8003ff4254029ff212a000ff509500a7f884a8003ff3254029ff192a000ff4c9500a7f864a8003ff61540017fb0aa000ff98550007fac2a8003fc61540017e30aa003ffd455001ffca2a800ffd5154007fe28aa000ffd0550007fc82a8003fd4154001fe20aa000ffcc550007fc62a8003fd3154001fe18aa014ffc8550007fc42a8003fd2154029fe10aa001bfd815000ffea0a800ffb5054003ff282a001df9415000ff8a0a80077c5054003fc282a001ff9015000ff880a8007fe3054003fe182a001ffc815000ffc40a8007fc2054003ff082a001ff0415003ffecba001eff65d000fff32e8003bf9974003ffacba0002fd65d000ffe32e8007bf1974000dfcc9a001fff54d000fff2a68007ef9534003ffaa9a0003bd54d000ffe2a68007ffd8f
  | 4 => 0x803fd544c43dfe2a2621effd4d31037fca698803fd534c40dfe29a6200ffd0d31037fc8698803de434c401fea1a6200f750d31037f88698803ff624c4017fb126200fbd8931005dec498877fe624c4057f3126200ff589310eff8c49880afc624c401f63126202bb189310f7fea498877fe524c401fea92621dff14931007fe8498877fe424c401fea12621dff10931037fe6498803df324c43bff1926200ff4c931007ba649881bfc324c43dffa8a6200ff94531007faa29887bfc514c401ffa0a6200ff90531007fa8298803fc414c40dff98a6206fdcc531007fc6298803de314c43bff90a621dff08531007fec098802ff604c439ff3026201bf98131007fac098873fc604c4037e302621effd41310e7fca098873fc504c439ff202621cff101310e7fc609881bfc304c43bff902621cff881310e7f84098873fe104c439fe0826208ffd9431035feca1881bfe650c4077f3286206ff59431005faca18823fc650c40d7e3286208ffd9031035fec81881bfe640c40f7f3206206ef990310057cc81881bfd640c4017eb206206ef590310057ac818823fc640c40d7e320621bffd5031007fca818803fd540c437fe2a06206bf98c31037fea61881bfe530c40dfea986206ff14c31037fe861881bfe430c40dfea186206ff10c31047fec41881bfe620c4057f3106206ff58831005fac418823fc620c4057e310621bffd48310d7fca418803fd520c435fe2906200ffd08310d7fc8418803fd420c435fe2106206ffcc831037fc641881bfd320c40dfe1906200bf984310dffea218823fe510c401fea886208ff14431007fe8218823fe410c401fea086208ff10431037fe621881bdf310c411ff1886206fd8c431037fa6218803dd310c40dfa988621affc8431047f84218823ff600c40dff3006201bf98031037fac018802fd600c411fe3006201bf180310dffea018867fe500c433fe2806219ff900310cff8801881bfe300c40dfe180621affc80310cffc4018867fc200c433ff0806208ff04031047fecb10802ff6588431ff32c4203bf99621007facb10802fd6588411fe32c4203bf19621047fec910802ff6488401ff3244207bf99221007fac910802fd6488411fe3244207bf192210c7fea910803fe5488401feaa44218ff15221047fec710802ff6388401ff31c4206bf98e21007fac710802fd6388411fe31c4206bf18e210c7fea710803fe5388401fea9c4218ff14e21007fe8710803fe4388401fea1c4200ff10e21015fac51080bff5288405ff2944202ff54a21017f8a51080bff4288401f7a144202ff90a21017fa851080bfc4288405f62144202ffcca21007de651080bfe3288405fe9944202ff0ca21017d8651080afe6188431ffa8c4208ff94621007faa310823fc5188401ffa0c4208ff90621007fa8310823fc4188401f
  | 5 => 0xc841137f86420802fe611044fffa888208ff94441007faa220823fc511040fffa088207efd0441047fc822081ff6411040ffea088200ef5044103fea822089bff2110411fe1088208ffd804103ffcc020806fe601040ffeb008200bf58041047f8c020806fc601044fffa808225ff9404112ff8a02081ffe401040ffe2008225ff8c04112ff8602089bff201044bff1008225ff0804112ffc2020823fc101040dffb2e6206bfd9731037fccb9880efe65cc40dbf32e62039f99731037facb98802fd65cc40dbeb2e62009f59731037f8cb9881afc65cc40dffb266206bfd9331037fcc99881efe64cc40dfeb266200bf59331037f8c99881afc64cc449ffaa66200ff95331007faa998893fc54cc40dffa9e6206ff94f31037faa79881bfc53cc40dffa1e6206ff90f31037bc879881bfd43cc401eea1e6206ff10f31037fec59881bfe62cc4057f3166206ff58b31005fac59881bfc62cc4057e3166224ffd4b3111ffca598803fd52cc447fe2966200ffd0b3111ffc8598803fd42cc447fe2166206ffccb31037be659881bfe32cc40dfe9966200f74cb31037f86598893ff51cc401ff28e6200ff54731127f8a398803ff41cc401ff20e6200ff50731007f8839888fff21cc447fe10e6206ffd8331037fcc198806fe60cc40dfeb066200bf58331037f8c198806fc60cc449ffa866222ff94331117f8a19888bfe40cc445fe2066206ff8c331037f8619888fff20cc445ff1066222ff08331117fc219888bfc10cc411ffb2c6200bfd963110ffccb1880efe658c401feb2c6200bf59631047f8cb1880efc658c411ffb246200bfd9231007fcc91881efe648c401feb246200bf59231047f8c91881efc648c443ffaa46200ff95231007faa918887fc548c4017eb1c6221ffd4e31037fca718803fd538c40dfe29c6200ffd0e31037fc8718803fd438c40dfe21c6208ffd8a31107fcc51880afe628c401feb146200bf58a31047f8c51880afc628c443ffa946220ff94a31007faa518883fc528c401ffa146220ff90a31007fa8518883fc428c40dff9946220ff8ca31007fa651881bfc328c40d7f30c6221ffd4631047fca318803fd518c411fe28c6200ffd0631047fc8318803fd418c411fe20c6206ffcc631007be631881bf7318c441ff90c6208ff08631047fec11887ffe608c4037f3046200ff58231005fac118823fc608c4037e3046221ffd42310fffca11887ffc508c43fff204621fff102310fffc611881bfc308c441ff904621fff882310fff8411887ffe108c411fe0846200ffd9531005feca9887bfe654c4077f32a6200ff59531005faca9887bfc654c4077e32a6200ffd9131005fec898803bf644c4015fb226200ff9913103dfcc898803fd644c4017eb226200ff1913103df8c898803bc644c4015e322621effd5131007fca898
  | 6 => 0xffe206822eff8c341177f861a08bfff20d045dff106822eff08341177fc21a08bbfc10d0411ffb2c8200bfd964116ffccb2080efe6590401feb2c8200bf59641047f8cb2080efc65904017eb24822dffd524103ffca920803fd549040ffe2a48208ffd8e41007fcc72081afe6390401feb1c8200bf58e41047f8c7208b7ff5390401ff29c8200ff54e4116ff8a72081fff4390401ff21c8200ef90e41007fa872081ffc4390401de21c8208ffd8a41167fcc52080afe6290401feb148200bf58a41047f8c52080afc629045bffa94822cff94a41007faa5208b3fc529040fffa14822cff90a411677c8520803fd429040ffe214822cef10a41007fe65208b3fe3290401fe994822cff0ca4103dfcc3208b7ff5190411ff28c8200ff54641047f8a32081fff4190401dfa0c8207fdd0641167fe4320823fc2190411ffb04822bff9824100dfcc120803fd60904017eb048208ff1824100df8c1208b7ff5090457ff284822bff1424115ffc812081ffc4090457ff184822bff0c241167fe41208affe2090457fe104822bff84241047f82120803ff65504017fb2a822aff9954101dfccaa0803fd65504017eb2a822aff1954101df8caa08abff545040fff2a28200ff5514103ff8a8a0803ff63504017fb1a8200ff98d41007fac6a0803fc635040d7e31a822affd4d41007fca6a0803fd5350455fe29a8207ffd0d410077e86a0803fe4350401fea1a8200ef50d4103ff886a0803ff62504017fb128200fbd8941005dec4a08a7fe62504057f3128200ff5894114ff8c4a080afc6250401f63128202bb18941157fea4a08a7fe5250401fea928229ff1494103ffe84a0803bf4250453ff2128200ff509410077a84a081ffc4250401ff9928229ff8c941007fa64a08a7fc3250455ffa8a8200ff94541007faa2a08abfc515040fffa0a8207fdd0541007fc82a0803be4150453ff90a8229ff08541007fec0a0802ff6050451ff3028201bf98141007fac0a08a3fc60504037e302822affd4141147fca0a08a3fc5050451ff2028207ff10141147fc60a08a3fc3050453ff9028228ff88141147f840a08a3fe1050451fe0828208ffd944103dfeca2081ffe65104077f3288207ff59441005faca20823fc651040f7e3288207bf9904103ffea82081ffe541040ffeaa08207ff15041047fec62081ffe631040d7f3188207f798c41005bcc62081ffd63104017eb188207f758c41005bac620823fc631044fffa988200ff94c41007faa62089ffc531040fffa188207ff90c410077c862081ffd431040ffe2188207ef10c41047fec42081ffe62104057f3108207ff58841005fac420823fc62104057e3108227ffd4841137fca420803fd521044dfe2908207ffd084103ffc842089bbe421040ffea108207ff1084103f788420803ff321044dff1908200ff4
  | 7 => 0x9900bef204c805ff1026402ff081321affc20990d7fc104c8077eb2ca208ffd9251007fcc92881efe6494401feb24a200bf59251047f8c92880fff5494407ff2a4a203ff5525101ff8a928823ff6394401ff31ca206bf98e51007fac728802fd6394411fe31ca203ffd4e5101efea72880ffe5394407fea9ca200df54e5101ff8a728803ff4394401ff21ca200ff50e51007f88728823ff6294469ff314a202bf98a51007fac528802fd6294411fe314a202bf18a5101ffea52880ffe5294407fea94a203ff14a51007fe85288d3fe4294401fea14a234ff10a51007fe65288d3fe3294401fe994a234ff0ca5101dfcc32880fff5194407bfa8ca203fdd4651047f8a32880ff45194469ff90ca208ff08651047fec1288cffe60944037f304a200ff58251005fac128823fc60944037e304a203ffd425101ffca1288cf7e5094407fe284a203df1425119ffc81288cffc4094467ff184a233ff0c2511a7fe41288cffe2094467fe104a233ff84251047f8212880eff6554401ffb22a200bfd9151007fcc8a8803fd6454401fe322a207bf1915101ffea8a880ffe5454407feaa2a203ff15151007fec6a8802ff6354401ff31aa200ff58d51007f8c6a881afc6354407ffa9aa203ff94d5101ffaa6a880ffc5354401ffa1aa200ff90d51007fa86a8803fc4354401ffb12a200bfd8951197fcc4a880afe6254401feb12a232ff18951015f8c4a880fff5254407bfa92a203ff9495101ffaa4a88037d5254407fe292a200ffd0951197fc84a8803fd4254465fe212a200ffcc951197fc64a8803fd3254465fe192a203bfd855101ffea2a880ff75154407ff28aa200df9455101ff8a2a880f7c5154407fa28aa232ffc8551197f842a8803ff60544017fb02a231ff9815100dfcc0a8803fd6054463fe302a201bf1815101ffea0a880ffe5054407fe282a231ff9015118ff880a88c7fe3054463fe182a232ffc815118ffc40a88c7fc2054463ff082a231ff0415103ffecba081eff65d040fff32e8203bf9974103ffacba0802fd65d040ffe32e8207bf1974103ffea9a081ffe54d040ffeaa68207ff1534103ffec7a081ffe63d040d7f31e8207ff58f41005fac7a081ffc63d0461ffa9e8200ff94f41007faa7a08c3fc53d040fffa1e8207efd0f4103ffc87a081ffd43d0401dea1e8207ff10f4103ffec5a081ffe62d04057f3168207ff58b41005fac5a081ffc62d04057e3168230ffd4b4117ffca5a0803fd52d045ffe2968207ffd0b4103f7e85a081ffe42d040ffea168200ef50b4103ff885a0803ff32d045fff1968200ff4cb4117ff865a08c3ff51d0401ff28e8200ff54741187f8a3a08bfff21d045ffe10e8207ffd834103ffcc1a0806fe60d040ffeb068200bf5834103ff8c1a0806fc60d0461ffa86822eff94341177f8a1a081ffe40d040
  | 8 => 0xf843421dff821a1003ff65508017fb2a843aff9954201dfccaa1003fd65508017eb2a843aff1954201df8caa100aff6450875ffaa28407ff95142007faa8a101ffc5450801ffb1a8400bfd8d42007fcc6a1003fd6350801fe31a8406bf18d421d7fea6a1003fe5350801fea9a843aff14d4203ffe86a1003fe4350801df21a8400ff50d4203ff886a1003bc43508057fb128402ffd4942017fca4a100bfd5250805fe2928402ffd094203fde84a100bfe4250805df2128402ff109420177884a100bec4250805ff1928402ff0c942007fec2a1002ff6150801ff30a8400ff58542007f8c2a1002fc6150875ffa8a843aff14542017fe42a100bfc2150801ffb028400bfd81421cffcc0a1006fe6050801feb028439ff1814200df8c0a10ebff5050873ff2828439ff141421cffc80a101ffc4050873ff1828439ff0c142017fe40a100bef2050805ff1028402ff081421cffc20a10e7fc105080dffb2e6406bfd9732037fccb9900efe65cc80dfeb2e6400bf59732037f8cb9901afc65cc80dffb266406bfd9332037fcc99901efe64cc80ddf3266400af99332037fac999002fd64cc80ddeb266400af59332037f8c99901afc64cc871ffaa66400ff95332007faa9990e3fc54cc8057f31e6406ffd4f32037fca79901bfd53cc80dfe29e6406ffd0f32037fc879901bfd43cc80dfe21e6402bf58b32017fea59900bfe52cc805fea966402ff14b32017fe859900bfe42cc805fea166402ff10b32017fc659900bde32cc805f71966402ff0cb32017b8659901bff61cc80dff30e6400bf98732037fac399002fd61cc80dfe30e6438ffd47321c7f8a39900bff21cc805fe10e6402fb08732037fec19901bfe60cc8037f3066406ff58332005fac19901bfc60cc8037e3066438ffd43321bffca1990dffc50cc86fff2066437ff10332037fc619901bfc30cc805ff9066402ff88332017f841990dffe10cc86ffe0866400ffd9532005feca990dbfe654c8077f32a6400ff59532005faca990dbfc654c8077e32a6400ffd9132005fec899003fe644c80f7f3226400ff59132005fac899003fc644c80f7e3226436ffd5132007fca899003fd544c86dfe2a26402bfd8d321b7fea69901bfe534c801fea9a6406ff14d32007fe869901bfe434c801fea1a6406ff10d32015fec49900bff524c805ff2926402ff54932017f8a49900bff424c805ff2126402ff50932017f8849900bff324c80df79926402ff8c932017bc649900bfc324c805ee1926402fb0c932007fec299002ff614c801ff30a6400ff58532007f8c299002fc614c86dffa8a6436ff14532017fe429900bfc214c801ffb026400bfd81321affcc099006fe604c801feb026435ff1813200df8c0990dbff504c86bff2826435ff141321affc80990d7fc404c86bff1826406ff0c132017fe40
  | 9 => 0xc87ffa828641ff9414320ff8a0a1907fe4050c0ffe2028641ff8c143037f860a190bff2050c83ff1028641ff0814320ffc20a1907fc1050c0dffb288606bfd9443037fcca2180efe6510c0dfeb288600bf59443037f8ca2181afc6510c0f7f3208607ffd504303ffca82181ffd5410c0ffe2a08606bf98c43037fea62181bfe5310c0dfea988606ff14c43037fe862181bbf4310c0dff2188606f790c43037fa862181bbd4310c0feea188606ffd8843037fcc42180afe6210c0dfeb108600bf58843037f8c42180afc6210c81ffa90863fff948431fff8a42181ffe4210c0ffe2108606ff8c843037f8642181bff6110c0dff3088600bf98443037fac221802fd6110c0dfe3088640ffd4443207f8a2218ffff2110c7ffe1088606ffd8043037fcc021806fe6010c0dfeb008600bf58043037f8c021806fc6010c81ffa80863eff940431f7f8a02181ffe4010c0ffe2008606ff8c043037f860218ffff2010c7dff100863eff080431f7fc20218fbfc1010c057fb2aa400ffd9152005fec8a9003fe6454801feb22a400ff1915203df8c8a900fff5454807ff2a2a403ff5515201ff8a8a9003ff63548017fb1aa400ff98d52007fac6a9003fc635480d7e31aa403ffd4d5201efea6a900ffe5354807fea9aa400df54d5201ff8a6a9003ff4354801ff21aa400ff50d52007f886a900aff6254805ffa92a403fbd4952017fca4a900b7e5254805fe292a402df14952017d8a4a900bfe4254805fe212a402ff8c952017f864a9003ff61548017fb0aa400ff98552007fac2a9003fc61548017e30aa403ffd455201efea2a900ffc5154805ff90aa402ff08552007fec0a9002ff605487bff302a401bf98152007fac0a90f7fc60548037e302a403ffd415201ffca0a90f77e5054807fe282a403df141521effc80a90f7fc405487bff182a43dff0c152017fe40a900bef2054805ff102a402ff081521effc20a90f7fc105480fffb2e8407bfd974203ffccba100efe65d080ffeb2e8400bf5974203ff8cba101efc65d08057f3268407ffd534203ffca9a101ffd54d080ffe2a68407ffd8f4203ffcc7a101afe63d080ffeb1e8400bf58f4203ff8c7a10f3ff53d0801ff29e8400ff54f421e7f8a7a101fff43d080fff21e8400ef90f4203ffa87a101ffc43d080fde21e8402bf58b42017fea5a100bfe52d0805fea968402ff14b42017fc85a100bbe42d0805f72168402ff10b420177885a100bfe32d0805fe1968407ffd874203ffcc3a1002fe61d080ffeb0e8400bf5874203ff8c3a10f3ff51d0879fe28e8402ffc8742017f843a100bec21d080fffb068407ff9834200dfcc1a101ffd60d08017eb068407ff1834200df8c1a10f3ff50d0877ff286843bff1434203ffc81a101ffc40d0877ff186843bff0c342017fe41a100bfe20d0805fe106843bf
  | 10 => 0xc4a980afe6254c01feb12a64bff18953015f8c4a980fff5254c07bfa92a603ff9495301ff8a4a992ffe4254c97fe212a64bff8c953037f864a9803ff6154c017fb0aa600ff98553007fac2a9803fc6154c017e30aa603ffd455301ff8a2a980f7c5154c97ff90aa64bff08553007fec0a9802ff6054c95ff302a601bf98153007fac0a992bfc6054c037e302a603ffd415301efea0a980ffe5054c07fe282a64aff90153257f880a992bfe3054c0dfe182a64bffc8153257fc40a992bfc2054c95ff082a64aff0415303ffecba181eff65d0c0fff32e8603bf9974303ffacba1802fd65d0c0ffe32e8607bf1974303ffea9a181ffe54d0c0ffeaa68607ff1534324ffea7a181bfe53d0c01fea9e8606ff14f4303ffec5a181ffe62d0c057f3168607ff58b43005fac5a181ffc62d0c057e3168649ffd4b43247fca5a1923fc52d0c0fff2168648ef90b4303ff885a181fbc42d0c91ff1968606ff0cb4303ffec3a181ffe61d0c017f30e8607ff58743005fac3a181ffc61d0c93ffa8e8649ff14743247fe43a1923fc21d0c0fffb068607ff9834300dfcc1a181ffd60d0c017eb068607ff1834300df8c1a1927ff50d0c8fff2868647ff1434303ffc81a181ffc40d0c8fff1868606ff0c343247fe41a191ffe20d0c8ffe1068647ff8434323ff821a181bff6590c0d7fb2c8606ff9964301dfccb2181bfd6590c017eb2c8606ff19643035f8cb21802fd6490c8dffaa48607ff95243007faa92181ffc5490c0d7f31c8606ffd4e43037fca72181bfd5390c0dfe29c8606ffd0e430377e872181fdf4390c0dffb148606ff98a43015fcc52181bfd6290c017eb148606ff18a43015f8c52191bff5290c8bff2948645ff14a4322ffc852181ffc4290c0dff1948606ff0ca43037fec32181bfe6190c017f30c8606ff58643005fac32181bfc6190c8dffa8c8646ff1464322ffe4321917fc2190c0dffb048606ff9824300dfcc12181bfd6090c017eb048606ff1824300df8c12191bff5090c89ff2848644ff14243227fc812181ffc4090c0dff1848606ff0c24322ffe4121913fe2090c89fe1048644ff84243227f82121803ff6550c017fb2a8643ff9954301dfccaa1803fd6550c017eb2a8643ff1954301df8caa190fff5450c0fff2a28600ff5514303ff8a8a190fff5350c0dff29a8600ff54d43037f8a6a181fff4350c0fefa1a8606ff90d430377c86a1803ff6250c017fb128642ff98943015fcc4a1803fd6250c85fe3128602bf1894321ffea4a190bfe5250c85fe2928642ff909432177c84a181ffc4250c85de2128642ff8c943037f864a1803ff6150c017fb0a8600ff98543007fac2a1803fc6150c017e30a8643ffd454321ff8a2a190bff2150c85fe10a8600ffd8143005fec0a1907fe6050c037f3028600ff5814320ff8c0a1806fc6050
  | 11 => 0xa00001800000200200803c00001601400801a00000000000804e00000000000a00000a00403602800000001000200200e00400600000600600400000600800800000200200200000000602403001c00001400200001200800000600003bf5965403dfcc92a01fff549500fbfaa4a803efd525401e7ea92a01ffc549500fde2a4a807ffd8e5403ffcc72a01afe639500ffeb1ca800bf58e5403ff8c72a00fff5395007fe29ca807ffd8a5403ffcc52a00afe629500ffeb14a800bf58a5403ff8c52a00afc6295007ffa94a803ff94a5401ff8a52a01ffe429500ffe214a851ff8ca5428ff8652a01fff619500fff30ca800bf9865403ffac32a002fd619500ffe30ca803ffd465401ff8a32a147ff21950a3fe10ca807ffd825403ffcc12a006fe609500ffeb04a800bf5825403ff8c12a006fc6095007ffa84a803ff9425401ff8a12a01ffe409500ffe204a850ff8c254287f8612a147ff20950a1ff104a850ff08254287fc212a143fc109500f7fb2aa803bfd915401ffea8aa00fbf545500fff2a2a807df9515403ff8a8aa01f7c5455007de2a2a800ffd8d54005fec6aa003fe6355001feb1aa800ff18d54035f8c6aa00fff5355007fe29aa800ffd8954005fec4aa13ffe62550057f312a800ff5895427ff8c4aa00afc6255007ffa92a803ff9495401ff8a4aa13ffe425500ffe212a84fff8c95427ff864aa003ff61550017fb0aa800ff98554007fac2aa003fc61550017e30aa803ffd455401ff8a2aa13fff215509ffe10aa800ffd8154005fec0aa13bfe60550037f302a800ff58154277f8c0aa006fc6055007ffa82a803ff9415401ff8a0aa13bfe405500ffe202a84eff8c154277f860aa13fff205509dff102a84eff08154277fc20aa13bfc10550077eb2ca606ffd9253037fcc92981efe6494c0dfeb24a600bf59253037f8c92980fff5494c07ff2a4a603ff5525301ff8a92981afe6394c0dffa9ca606dfd4e5301fbea72980f5f5394c0dfe29ca606f714e53037fec52981bfe6294c057f314a606ff58a53005fac52981bfc6294c057e314a603ffd4a5301ffca52980ffc5294c9bff214a64dff10a53037fc652981bfc3294c0dffb0ca606ff98653005fcc32981bfd6194c017eb0ca606ff1865301ffea32980ffc5194c9bff90ca64dff08653037fec12981bfe6094c037f304a606ff58253005fac12981bfc6094c037e304a603ffd425301ffca12980ffc5094c99ff204a64cff10253037fc612981bfc3094c9bff904a64cff88253267f84129933fe1094c99fe084a606bfd9553007fec8a9802ff6454c01ff322a600ff59153007f8c8a981efc6454c07ffaa2a603ff9515301ffaa8a980ffc5454c077fb1aa603ffd4d5301fbea6a981bfe5354c0dbf29aa606ff14d53036f8a6a980fdc5354c01ffb12a600bfd895325ffc
  | 12 => 0x3800600401400601201c00000000401801200e00000000400000601800c00400600000a00200201000000000e00200c00200000800a01400600a00200000000a00400800000200401800003a00400201000201000600400600400600000000000000000400e00201400200204200001a00400001601400000000600600800000c00404001e00000c00400000400400802e00200200c00200600000000400400c00c01c00800800200600200600a00000401c00000200e00000401c08600000002e00000002c00000802200000000200400c00400c00400201000000000002c00c00200200a00401600601600c00200000203400000e00200001000403a00600001000a00400000000200000000002000e03600800400801200401e00200000002204200200000600200400a00000600401200200800a00000600000400800202200201200803600400e00601600000001201c00c00000a00000801600600800203001402e00e01200200000404c02200000000000400401200c00202000a02200200403c01401001000001200001c00a01200a02401c02200001803000000001a00600001e0000000040b600001c05e01200001202400000000400000600000000000401c00200e06c00201800200c00401000200000600000600000e01201401000400c03200202800200000602400600e00400001400202205e00204000000800601200801200a00400000601400203200000400400000200200000802000a00400e00800a00600000002400000c00001400000002600c00401400400000400a03c00600200a00601600200402401000000200a00001201601a01000200200a00000c00000000000000003e00000400606200201000000800a00003e00600600a00201a00600404000c00a00400c00400400200000004603200800600400a00000003000000000601200200805400000000000003603800000202803a00000000000001a01001001c00000000a00403000800200c00200600401e00c00005803a00800000004400400400a00c00001200000000200a02e01200c00800600400000c00200601200000000201800001400000000400001800000000208a00000600000603000002e00805400400000000e01600200000203e00001a02400800000800002800401400000001a00000802600800601601a00a00202001400000201a00a00601000000002400200400000201000200401a00802e00000200400600800c00200c00200000400600e01400400401203001401400400008401000200001400401404200e00000000200000a03800000000600400402401602202000602000200000200400000000600802201800a00801801400202a00600a00803600000402e00000000400a03202600200e00003e00000a00a01000004201e00200
  | 13 => 0x697746c46ed27c9e1935e4104369d0400095700000003068a723480010be000000000000029a4c28e9800092b2de17691b849939b915c0004232bea90c0008294f0170c43e3133fd99292bea3b4d528c078050f1b0085915c50030182a89924da0049458ad27231f2897c000193034879cf8469911126cc43828e4718a0101001617f8f8136237e00000000005d445c8c94376693029208c2d07fa2b2889800024e3f517c07720b513117d052c60a15100013366b100000000003de16f06f4c0c83f000109d2046c22921aa4d9c32704f23ac34c83238d232800000041580000008be34f145000052800023848526c818a283ccde00041c1ea4c9a7a144e9ecc0b633d3b18f640003961e196d12a84684930e940008ff00000000000000000b347e2487009259c00068b39299fc93c21320880383ae877000226400000009e0760000000000000000040d4fa000039e2664c609a43c80000239e394486f123a06b00003413011fc066606f43d800109a00000000d510c31b25c00000004e22050000b000000000eb8e7681a2cc2248eca0002a1a42c9d00004e581e8abe8393ee877ca9839b0668d90000000000092d3aa0002ce800069e0dc2ae917546e0001e1000049e36730e9024d3e2883b68f180ec0004960bb10ae6363a899ec7941900ae800055e6ac16195c12eaa2a0000c182f21703ca119000089600024b8ee889e0cf89911ca000130947c0aa7202fba710cee0f1308a178000a0401d8000a365184e18b28046000000231d34a72b2cd1a6c2620003b48000ee489a4b78000fce0002ba80000740001370e8c0009a2334116400055423e032cd2c42c00003ac1480b238405b089284c000251400000000000006d28c4000000000000000001dd06285c3ee07d51d02e7302a7453de0004a39e7cea60823fb25545960000a01f2922600020c1fb85dc92015e8e0822e02a4140000dc28452d4000000000005800004721c92fc27fcf261180002444d6a64b10580000002eb13613180000002ad8000af00000001ebcae2000000054c39a4910001e9c00000014580010a0000000015000033123717d80006194451e04bde5903350cb115693800018b4000000474a5b40668f92ee0968f861c22450000000000000252402800000000c00000a03600200001600000000a00000000a02600000001000000000200000200000200602000201a00802e00000200401200001a00c00200000600200c02e00600000200c01a00400000000000200800c01800e00002401e02a00400000002200000002c00000600a03801c00800402e00600c00000000c03800a00402000000800000001c00e01a02600000200800001c00000000400803000c00000602400600c05403c01800001a01001200001600400000200401600200800a00200a004008000000
  | 14 => 0x2ac80011f40000f5000000000000006d0a683831582699058483053a298dd03c805e00000280001660228000a2200025892343ea478a07093800000020100000000f400007de00029691854786590001ccc0000a11f1985c0000002828000ad88540000368cbe7e300024f00003b71ada52c9c270a30680000001ed01f00000c22ae0000f3424a02c2e40000f3088f50f84d47027bd39728cc08887e3f315040004ec00000006d69df2bd800132c0000000fa40000a30fb8000708a3f43c800064609125200000008dd06da2442840004b9173803003f000039d2fe82a000264442400038b21543400003ce843c00000000000000006b428800000002ba45b03dca4671d1ec00002b200031f07e022c41425a94c01765bb3af8f4492e2b600016dd26c1f227e08a41f89514120ba41346824b4a5e06ec0003b300000000004f4000027a5321248f4cb48392362a4c00002932f60e800000002140000fa800023ca84c95a00004a000000067500000000000001dc00013dc63d00012ecbfa000000000121c66100010f44a688e00006711ec0000710ed000008800021d498413f50d08009345e5000000090a7403f68d20df22b50a515600d455c39d147083e98237827dc7383a92e49df43a201a11a06d8ac83354360f2ca9081419d07000000000bd000000079b11b8000d4481813427e819010019522848ce0002281698f4c00032880000000001b190fd2740001aa01c138a73050c281cf3200000026e4d56000072171c98034c04ba3514420002bf19009b092f417974406c12804a9960f7050909180000b800043387f0bd655642080005ea00024c06282b693f40395013ae099122986c94a2600a3000000000048f216001a8c332608b49b61da041a390a9c000000145cb842920d580008fa34305f0c692ac6d03da1c50cac06b22004053bc2d100016cc0000340000714bc84a04e69a50dc03d62b0800065e70f24a1bd505a1871f699989e875d0620218b8c000000000000046c017800052a963231a2ed36a3ad36a211c32c3904de17a519c42a0ff00001580ba3cb01202142411df80000000004ff022d0680002779d6000000000015e53b80000c006c4a9e0001c58000ffe29c19004a89cc0003fe18e49fe3562d01638b8803d00011e8ad00004c9186943869a1b6965d2240002620000762545099a1c4fc04624231db8d1021901e223510a1d20ec8000c568d5000000076416124d97282720000001cc80006e730489a80000000df120857034200000000008fc4e60c550c63280dc8000d0018648f81f00005f53e3246ce440920000000a728532421f38dde10b00006cc0000002e284705f235a12380000009b8359a41c8429e31910f980002d822622bccb45745250c30e722a40000f04b32776000275078e43a000000000000023
  | 15 => 0xaf00780c894f4df8bf40006a3000139c47c0002d79a18e5253d4ce8894cfa00048283a03e667312896d48c04650000ea86308a24cc85dcade6af000012800000010d8000b627880bf058d0d20d351a984013a00051b12a4000000000000127244f272000130c000286800069a0000001671402000000000000000010827d855428740683fc000000496a0982b00740000000c266354b0a36000044a350820033c0002cb00011402d0000201800048c20d84080000000000000d5ca49349097400009b0c100009a816f3c883a5228000169016400000004b00000000002ca1fc882e2912d710090b668d33299e93ca2bb300000138e770000000036484937f96f839c30b45a9bdcc8e283190a4c815e00019900005f60003f628c541a1f40f71de800000036900000004f7014044895c7ab466800000036c26ea24c26c9f93d2961031e12000023a83442184550580c422e4077a1cc24ea280259ff8d8830841291509560671791c081849a426b24a47762c126620dc4342590e6222425e83e0001004e300000000588414351000240c40270d0a58000f8a2dd3ec0718000526408800062200005991f814a30d3b09d583b800044b8a28f9097b30b00008346911e90188d4e0003bf9bd072816b00000013086714520000000000249976c0000001c40bc40000003638000a0c5f2218a318f9e00000008208ac2b32c50380b6c29f11e1de434822f00019ac45600000e92f142878c113a04921282000005d008017d023066087827214f27d51e615101c936401618e38f961c00005d2970788f0e8642818b2540c73e4f624540063124aca580a946274698ff00008fb29b96340007683e68fccc2a39e38900002604dc13b01c53680002d81b780000224d60e880009b246918a89f437500001f4f8200000000000002983ad80000000000000d1483c62400016c800000003180000000001c71da8ca478500000000000000c580003f48b835d19b867c4890e0a04cce0385195844137a1442e799749d242440702a54520000cb8fec0004f005ba4a860498d4880b88e0a55a52319d82360000129fe52bc7df27b12bcdaa1e54b723f93b04394b595451024cf0138ca42121bf1bd9d3d33c43e0dd000096871e00015cca7800014a01e45ae0003a512588cca2d0000000e161b700000000ea0003a480000000c61ea1bf41723364139ec8ece324000074c00000006b0e64ea80ae0060910d2027c04e00006de2a71d08ceca5622c1a8000905c00049112b070c5a54db1760c7e7d14f89a113141ca0001d20bdc00013f8340000935000000000095050d80000404c300005c8e4e0000028000b9637d34791c04f216d2850ba8e12000000000000078947900000000001548884d6e5e0000222000083c000243c000167360837941600043b2460b7400011800000
  | 16 => 0x6442199e2cfae7a22d480001080001199ec02be31d23925087745290000dcc8847e4000000015a6430189c852a624200005e000000000000000000cc000028000024d00000000000002f881049d698840e81c91be06e0f0236c83821119f85790fe00012914484ea8031a325e80ca4bf08ca35d2024e028727f435031733185c510e08946d27490d47ef13ba85d13856e34e91448966b92a3a62400030911424cc2f847f21314200001d6133a1e04bc0001f900012d4000356a4f86709c93079ef0e2a00042c800144012400015dc9ae5c126f26f8000000070a7a450c49d2901aecde40ca000282800075e5178e4437045c3d41dbc518000000158800037c08f800000067400000001189900a400000003b30000e3c80c45f27980000002990831cf0f3c4b619e1248caa0fa0470994542000000000100497e0001058000a2b1d20ef80700c91b2a6603968a92a800000007c00000000fd067236f951800074348e03ec0002824f100000be0dd36684b4db67440002304a5859b11b17f0000073464233ccda777000276c00000000003643f61b000001b000063428d0c7cd0e2f742500a4fbc92343e163080a51e2cf93945cc0573dd87ac28a5190002398228087000062473447700001340007a033e175820e46a27f0bf135c2570000000c526fa0000e9ce4898f4f98b54aa685a05f8fe00009ab46287a40000004bca1586cc6c63ca91c4000000000002000005a0001d0800059531c1db0c243890001d1400093400003012420c5352911c00000000015100007264518a146dc000437000098e00000000000009701ed800000070403da39c78a56634c1f242820ee000290800060752407110168f721c04892e210e1bf8bd08182320d396a8692a100ae11bce1c31613887406ae1762ef865135a56d10f0b001261653761d3809836820ca05866832e15a01a0f0075700002ac0008ee2640000c1c9bb41080009da28916d14844767361c50c000000000001f892944cb4b41c3147400000000000001aa38e0f1000007f1af800000095a441a6700004550000c6400070613f23b08164b73aaa41881c1852b58e1c58c00036583d14000003a801b4d1400051c9c64cfc000000000048060c2518b700008612f400010a24151030a350023af3fa80000008e04800e00ec46c00bf8045080a415170b8524a53845ea5982a000000000000001ad1ca800044841d51e8f882425132d193c94644aa08185a93827ae000000063805e0001dd4f1a90a1260bccf744df3a606bc26402623c00005a68440001f4c000a0e3960c78a6aa030001dcc00000000011cc0000d207b104c00013a47c152c41c25621900000000003cd0b2085e2a64c718f0a5e6d307f158032a6140409a5d1289f030086a4d38156180800042a0000c8a26c9f00000001f400000002
  | 17 => 0x1bc164d06a000000000000000000000001d80001db000129c1db51a145544c5ff1048be0c9016e3ed8af901239f471060499c9eb1ed0ffc2a434a45993c4ed684f4d4a19800020c27185506885a138391200000001ac28540007a338da3d0c9e9442fc8f7128004325e80011da0004e71e48f6c58900024580001f00000dc8bda0003a918989508d931d11110865e33b2149c37840727e8e5c1be80f01b92004b0138000079864c0000f6081101400000003d4cc09b70000f24cb849533204d018675c40b800025696c40f20000006851231f3096474b000081ccf000007c8da8000713000259400062f0a7194c7dc63300000000005020888fd400000038022b00005fe1e811346605ad39694d8f489b021b0b1c0009ea00000005c64d03c224313f04413941218b806462a6963d29a0e30000be888c7e5253a4ec428631000000000000431613480009d940a92f80006fc3c78adcaa48f53fc01e031000000000003f20cf3ce1b9023a95d0a19b8d0d09312b1a1c07f4747072800000001350b292d1186d923a9988afe0000000a80ba61262f3a8484f637a4e1123811a5e20211ec400028f46012e831aa451dea2d0386000033083c00045300004b845c15700021886e0000196922084a85d30e08a8cf21de0b9a8b12ee00052225d00001470001cfc8b60004e3000087600f00021080006cf3db87f4aaa3a8347232d1e06be4e02194b582f000009c0000a0c32100011786540001df0a7e5ea295161869c91d0428fe4df66f84bb19147d00e6000000000000032827ed24e3ce14e800049058138b988c57200000000000000b12ef1a544c6711008250400074644000010e442b0820664dd29da00d8dc4aec00011c1d80e5e9d014098788d62df3ad206d06c981353000141048b1f60e4c0007344eb00003080492598a107ce38d0001798dba35c34628240000c74a919251a20190001354dae88b4f201807c210822913b859ca1d3591b0c3fe790000123486853316b279c00000045fa0301b05421ba14111de0584a60000dd4608121a4203907d613596e085a53b0000ab4ace4c53f48138a441d44f6852420a000000000056435d1d623f40000002a4a87893e00000ba434b067c40000000d0684e46f15f0b7e2d405a000000000004794441fa11a1a91614cd20000000a6c27c620000269c38e00008aa2600000000000b3c94c00049b89e0af44760ee8ed46ee00000000009021f60000000c440003180ba000022041800000000000001b70cb65cd2dea1e84da37937585980003b0000000061c1f13408ef0dcc86b0000e751a013b1821fdcd7840f45d140525019b39aa4900006321768000860a0539880000000560000000fd621d51280000000001af0000b3c6b62d585913c24cd00000011606370d700006b28b2292878c42e02e4d01474
  | 18 => 0xa629ba366123d30011e22c25f00fc9971018140faa74d00001450208844d427992b602d46b21f462014d0c61b28c5072a4c3932914a2354e7941cdfc58b50c9c409824b92b50ff861e4433c10fc0d500a81528084c304a20bd82d818260400010800006f612a0f7c1e66d8000000115000000017ec00075900000010c00000000000dc460b2c90b140000002c40000324a3809612c071800000000000004d117f27204b694617b0bbd0445571a39f2cc9ca403129f651041a30ce9fd0b045e105e84300007c73df001d3340b806a0eac60a23f00027280005a219c86d4cae3fd0000344c3e00027d80c10de43712e0784000000000000000098331d9e0d0960982110fdd07a4122228f906803cf00026852fa7ad1a98a5cefc2a3019257103e53a37993a861423a44800003345d0106a8f800000021a94f80387784eea3082aa6b027a800069600013783a915a7b91818000000000000000000000100000000001134ac197800077113997cc21a2bc21709540009d316c807d4227b543a169d33e27d17297e8bb20d5000000089c73d0531aa80000003bd80007aa0451fa23244a000007c0aacd928483fe9afcdac81902991781da9fc0d29c0c04899500020e80000000001430ba400011e800000000034487544f40000001fccf2e2bf4a19f848080000000fac0006a000025cc00000000000000000001eea27c66e0001fb09d0d485720001644a1600000005300000003d60808462a023e9088d44e00014805d53166bd0000b6c1446e522d00009a60000000d5413e00035c20cc1e000000018b80001693689efc3de3d71700000ddc7da45b9904f146da25884dd27a15a1612149290015079264c0561a1183a88c7304034661fc46c25b91e6000122e2050001ce148e0001620001328000200293029e47b000000049489504800012080002eaa0140009a300020ec5625cc00000001ae0004b20ab0cce0000001c040004a10050000f54129067175d232000027800092066c00000000002a800310211629f2
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x3705451000df6705451000df4705451018ff0705451018ef7605451018ff2205451000cfe76d051000cfc76d05100067f65d05101867c65d0510006bf64d051003ebc64d051000dfa70d0510005f970d051012cfe76905100067f659051016e7c659051003ebe6490510006bd649051003cff765051000cfe7650510144fd765051000cfc76505100067f65505101567c6550510006bf645051003ebc6450510005ef7250510025ec7250510005fb705051000df8705051015cfe76105100067f651051013e7c651051003ebe6410510006bd6410510005de7310510005dd731051000cfe76cc51000cfc76cc51002d7e75cc5100057d75cc5100067f65cc5101267c65cc510006df63cc510036dc63cc51000dfa70cc510005f970cc5100ccfe768c5100067f658c51010e7c658c5100cdf6768c510006f6768c510005f7758c510005f5758c51000777658c51000774658c5100e5f5738c510036f6638c510036f4638c51000df6708c51000df4708c510046f7608c5100fff2208c510034ff764c51000cfe764c5100e4fd764c51000cfc764c5100067f654c5100f67c654c510005bf744c510005bc744c510006df634c510036dc634c510005ef724c510025ec724c510005fb704c51000df8704c51000df4764c510036f4764c51000cf4764c510005f7754c510005f5754c51000777654c51000774654c510007b7744c510007b4744c510007d7734c510007d7634c510036f6634c510036f4634c510007d4634c510007d6434c510007d5434c510007e7724c510007e4724c510007d7324c510007d5324c510007f3704c51000df6704c51000df4704c5100e7f0704c5100e6f7604c5100e7f2204c5100fcfe760c5100067f650c5100de7c650c510005be740c510005bd740c5100fdf6710c510294fe76885100067f65885100c67c6588510016ee6288510006ed628851000df87088510014ff764851000cfe76485100acfd764851000cfc76485100067f65485100b67c6548510005bf7448510005bc7448510006ef6248510016ec6248510005fb704851000df87048510025f87648110016f87648110014f876481100077b654811000778654811000dfb724811000feb7248110007eb6248110016fa6248110016f86248110027e86248110027ea5248110007e95248110027ea4248110007e94248110027ea3248110007e93248110007f37148110045f87148110007f0714811000efb614811000ff36148110007f25148110007f15148110007f23148110007f13148110007ea2148110027e8214811000dfa76c411000efa76c411000cfa76c41100077b65c41100077865c4110045fb72c4110005f972c411000dfa71c411000ff271c411000efb61c411000ff361c4110047f251c4110007f151c4110047f231c4110007f131c4110
  | 1 => 0xd10034fc7690d100067f6590d102367c6590d10006bf6490d1003ebc6490d10005f67190d10005f57190d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d1021e7c6550d1003ebe6450d10006bd6450d10034ff7610d10004fe7610d10004fd7610d10034fc7610d100067f6510d102067c6510d10006bf6410d1003ebc6410d10006df6310d10036dc6310d10005f67110d10005f57110d10014fe76d89100067f65d89100067c65d8910026ee62d891001cfe75d8910004fd75d891001cfc75d891003cfe74d8910004fd74d8910034fe73d8910004fd73d8910026ec42d8910026ec32d8910044fe71d891000cfd71d8910044fc71d8910026ef21d8910044ff70d891000cfe70d89100bcfd70d891000cfc70d89100beef20d89100beed20d89100057f755891002d7c75589100067f65589100067c6558910005bf7458910005bc7458910005df7358910005dc7358910026ec62589102adf77158910004ff75589100067f75589100047f755891001cfe755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf745891003cfc7458910006bc745891003cbc7458910004ff7358910006df7358910004df7358910034fc7358910006dc7358910034dc73589100bcff7258910006ef72589102acff7158910006f77158910026ec21589100acff7058910006fb7058910004ff7654910004fe7654910004fd7654910004fc76549100067f655491001e7c655491003cff76d0910004fe76d0910004fd76d091003cfc76d09100067f65d09101e67c65d091003ebe64d0910006bd64d0910006ef62d0910016ec62d0910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101d67c655091003ebe6450910006bd6450910005f77150910005f47150910034ff76cc910004fe76cc910004fd76cc910034fc76cc9100067f65cc9101c67c65cc910005be74cc910005bd74cc910006ef62cc910016ec62cc910005f671cc910005f571cc910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9101b67c654c9102a4fe769451019e7f659451001e7c65945102a5f6769451029ef6769451018df5759451019f77659451001ef6659451001ef4659451002f74659451001e746594510005f5739451002f77539451000775539451000df6709451000df47094510046f7609451019f76509451019f74509451019ff2209451001cff765451000cfe765451018cfd765451000cfc76545100067f655451001e7c6554510005fb705451000df8705451000df4765451001ef4765451000cf4765451019df7755451000777755451000777655451001ef6655451001ef4655451002f746554510005f7735451002f775254510007755254510007f
  | 2 => 0x4fd75d911001cfc75d9110034fe73d9110004fd73d9110014fe72d9110004fd72d9110014fc72d9110006be42d9110006bc42d9110044fe71d9110044fc71d9110044ff70d911000cfe70d911015cfd70d911000cfc70d911015ebf40d911015ebd40d911002d7e75991100057d75991100067f65991100067c6599110006bf6499110145f571991100057f755911002d7c75591100067f65591100067c6559110005df7359110005dc7359110005ef7259110025ec7259110175f77159110004ff75591100067f75591100047f755911001cfe755911001cfc75591100067c755911001c7c7559110006bf7459110004ff7359110006df7359110004df7359110034fc7359110006dc7359110034dc7359110004ff7259110006ef7259110004ef7259110014fe7259110014fc7259110006ec7259110014ec7259110174ff7159110006f77159110144ff7059110006fb705911015cfe76191100067f65191100067c651911003ebe6419110006bd641911003cff7695110004fe7695110004fd769511003cfc76951100067f659511001e7c659511002f3f5495110004ff7655110004fe7655110004fd7655110004fc76551100067f655511001e7c6555110034fe76d8d100067f65d8d100067c65d8d1001cfe75d8d10004fd75d8d1001cfc75d8d1003cfe74d8d10004fd74d8d10014fe72d8d10004fd72d8d10014fc72d8d10006de32d8d10006dc32d8d10044fe71d8d10044fc71d8d10044ff70d8d1000cfe70d8d100fcfd70d8d1000cfc70d8d100fedf30d8d100fedd30d8d1002d7e7598d100057d7598d100067f6598d100067c6598d10006df6398d100e5f57198d100057f7558d1002d7c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10005ef7258d10025ec7258d10115f77158d10004ff7558d100067f7558d100047f7558d1001cfe7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d1003cfc7458d10006bc7458d1003cbc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d10014fe7258d10014fc7258d10006ec7258d10014ec7258d10114ff7158d10006f77158d100e4ff7058d10006fb7058d100fcfe7618d100067f6518d100067c6518d10005be7418d10005bd7418d10036de6318d10006dd6318d10034ff7694d10004fe7694d10004fd7694d10034fc7694d100067f6594d1001e7c6594d1002f5f5394d10005f67194d10005f57194d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d1001e7c6554d1003cff76d0d10004fe76d0d10004fd76d0d1003cfc76d0d100067f65d0d1024e7c65d0d1003ebe64d0d10006bd64d0d10006df63d0d10036dc63d0d10034ff7690d10004fe7690d10004fd769
  | 3 => 0x5739471005777539471000775539471000df67094710047f27094710047f1709471000df4709471019f76509471019f7450947102b4ff76547102b5f776547102bef7765471004777755471001ef6655471001ef46554710005f7735471005777525471000775525471000df6705471000df47054710144fd76d0710174ff7650710005ef725071004dec72507100e4fd76cc7100557e75cc7100057d75cc71000df5768c710046f5768c71000cf5768c710045f7758c710005f5758c710036f6638c710047d6638c710047d5638c710046f4638c71000df6708c710047f2708c710047f1708c71000df4708c710114ff764c710005bf744c710005bc744c710005ef724c71004dec724c710115f7764c710006f7764c710005f7754c710005f5754c710007b7744c710007b4744c710047d7734c710036f6634c710036f4634c710007d6434c710007d5434c710007e7724c710007e4724c710007d7324c710007d5324c71000df6704c71000df4704c7102acff7648710005bf7448710005bc744871001cfe76d951002e7e65d951003cfe74d9510004fd74d951002e7f54d951002e7c54d9510034fe73d9510004fd73d951002e7f53d951002e7c53d9510014fe72d9510004fd72d9510014fc72d951002e7f52d95100067e52d951002e7c52d9510044fe71d951000cfd71d9510044fc71d951002e7f51d9510044ff70d951000cfe70d951019cfd70d951000cfc70d951019e7f50d951019e7d50d95102a57e76d951001c7e76d95100067e62d95100067c62d951019f7771d951019f7a20d951019f7610d951019f7410d951019f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f72d95100067e72d95100067d72d95100067c72d95100067e42d95100067c42d95100067e32d95100067c32d951019e7f71d951002e7e71d951019e7d71d95100067f21d95100067c21d951019e7f70d951019e7e70d951019e7d70d951019e7c70d951019e7f40d951019e7e40d951019e7d40d951019e7c40d951019e7f30d951019e7e30d951019e7d30d951019e7c30d951019e7f20d951019e7e20d951019e7d20d951019e7c20d951019e7f10d951019e7e10d951019e7c10d951002e7c65595102b5f7715951019cff75595100067f7559510004ff745951003cfc7459510004ff7359510034fc7359510004ff7259510014fe7259510014fc72595102b4ff7159510006f7715951018cff7059510006fb705951019d7e761951002e7e761951019c7e76195100067e62195100067c62195102a77571195102a67f61195102a67f60195102a77a20195102a77610195102a77410195102a778101951003cfe76d91100067f65d91100067c65d911001cfe75d9110
  | 4 => 0x931003cfd715931000cfc7159310046be4159310046bc4159310146bf4059310146bd405931003cff7695310044fe7695310004fd7695310044fc76953100573f5495310004ff7655310044fe7655310004fd7655310044fc765531001cfe75d8f10004fd75d8f10044fc75d8f1003cfe74d8f10004fd74d8f10014fe72d8f10004fd72d8f10044fc72d8f10044fe71d8f10046f671d8f10046f970d8f100e4fd7698f100557e7598f100057d7598f10046df6398f10046dc6398f10034ff7658f10046dc6358f10004ff7558f1001cfe7558f1001cfc7558f10004ff7458f1003cfc7458f10046df7358f10006df5358f10006dc5358f10004ff7258f10014fe7258f10014fc7258f10034ff7158f1000cfe7158f10034fd7158f1000cfc7158f10046de3158f10046dc3158f100e6df3058f100e6dd3058f10034ff7694f10044fe7694f10004fd7694f10044fc7694f100575f5394f10045f67194f10005f57194f10004ff7654f10044fe7654f10004fd7654f10044fc7654f100067f6554f1001e7c6554f10005fb7054f1000df87054f1003cff76d0f10044fe76d0f10004fd76d0f10044fc76d0f1003ebe64d0f10006bd64d0f10034ff7690f10044fe7690f10004fd7690f10044fc7690f10036de6390f10006dd6390f10045f67190f10005f57190f10004ff7650f10044fe7650f10004fd7650f10044fc7650f1003ebe6450f10006bd6450f10036de6350f10006dd6350f10034ff7610f10044fe7610f10004fd7610f10044fc7610f10045f67110f10005f57110f1001cfe75d8b10004fd75d8b10044fc75d8b1003cfe74d8b10004fd74d8b10034fe73d8b10004fd73d8b100acfd72d8b10044fe71d8b10046f671d8b10046f970d8b10046fa10d8b10014ff7658b10046ec6258b10004ff7558b1001cfe7558b1001cfc7558b10004ff7458b1003cfc7458b10004ff7358b10034fc7358b10046ef7258b10014ff7158b1000cfe7158b10014fd7158b1000cfc7158b10046ee2158b10046ec2158b100aeef2058b100aeed2058b100aefa1058b10004ff7654b10044fe7654b10004fd7654b10044fc7654b1001e7e6554b100067d6554b1003cff76d0b10044fe76d0b10004fd76d0b10044fc76d0b1003ebe64d0b10006bd64d0b10004ff7650b10044fe7650b10004fd7650b10044fc7650b1003ebe6450b10006bd6450b10005f77150b10045f47150b10034ff76ccb10044fe76ccb10004fd76ccb10044fc76ccb10005be74ccb10005bd74ccb10036de63ccb10006dd63ccb10045f671ccb10005f571ccb10004ff764cb10044fe764cb10004fd764cb10044fc764cb10036de634cb10006dd634cb1000df57694710046f5769471000cf5769471001ef6659471004776659471001e766594710047756594710046f46594710005f
  | 5 => 0xdfa7094520005f97094520004ff7654520004fe7654520004fc7654520005ef7254520015ec72545200076d5254520004fe76d0520004fd76d052003cfc76d0520015ee72d0520005ed72d0520007ad42d0520004fe7690520004fd7690520044fc7690520006bf649052003ebc6490520015ec7290520167ae429052000dfa7090520005f97090520004ff7650520004fe7650520004fc7650520005ef7250520015ec7250520007ad4250520004fe7610520004fd7610520044fc7610520006bf641052003ebc6410520005de7310520005dd7310520015ee7210520005ed7210520137ae421052000dfa7010520005f97010520004fe76cc520004fd76cc520034fc76cc52005d7e75cc5200057d75cc520015ee72cc520005ed72cc520007cd32cc520004fe768c520004fd768c520044fc768c520006df638c520036dc638c520015ec728c52000dfa708c520005f9708c520004ff764c520004fe764c520004fc764c520005bf744c520005bc744c520005ef724c520015ec724c520007cd324c520004fe760c520004fd760c520044fc760c520005be740c520005bd740c520006df630c520036dc630c520015ee720c520005ed720c52000dfa700c520005f9700c52000dee76885200beee768852000cee7688520005ef7588520005ed7588520005ef7488520005ed74885202ceee64885202ceec6488520005ef7388520005ed73885202c6ee63885202c6ec6388520015ee7188520017e67188520006ef6188520007e76188520007e4618852000dee70885200bfea7088520007e9708852000dec7088520016ef6088520017eb60885200bfea108852018cfd75d971003cfe74d9710046be74d971003cbe74d9710004fd74d9710046bd74d9710004bd74d9710034fe73d9710046de73d9710034de73d9710004fd73d9710046dd73d9710004dd73d97100567f53d9710014fe72d9710004fd72d9710044fc72d9710044fe71d9710046f671d9710046f970d971019e7e50d971019e7c50d971001cff76597100467c65597100467f7559710004ff745971003cfc7459710004ff7359710034fc7359710004ff7259710014fe7259710014fc72597100567f525971001cff715971000cfe715971001cfd715971000cfc71597100467e51597100467c515971018e7f505971018e7d505971001cfe75d9310004fd75d9310044fc75d9310034fe73d9310004fd73d9310014fe72d9310004fd72d9310044fc72d9310044fe71d9310046f671d9310046f970d9310144fd7699310046bf6499310046bc649931003cff7659310046bc6459310004ff755931001cfe755931001cfc7559310046bf7459310006bf5459310006bc5459310004ff7359310034fc7359310004ff7259310014fe7259310014fc725931003cff715931000cfe715
  | 6 => 0xe7694d20004fd7694d20034fc7694d2005f5f5394d20015ee7294d20005ed7294d20004ff7654d20004fe7654d20004fd7654d20004fc7654d2001e7e6554d200067d6554d20015ee7254d20005fb7054d2000df87054d2003cff76d0d20004fe76d0d20004fd76d0d2003cfc76d0d20006bf64d0d2003ebc64d0d20015ee72d0d20005ed72d0d20247ae42d0d20034ff7690d20004fe7690d20004fd7690d20034fc7690d20006df6390d20036dc6390d20015ee7290d20005ed7290d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20006bf6450d2003ebc6450d20006df6350d20036dc6350d20015ee7250d20217ae4250d20034ff7610d20004fe7610d20004fd7610d20034fc7610d20015ee7210d20005ed7210d2000dfa7010d20005f97010d2000dec765492001eec765492000cec7654920015ef75549200176f75549200076f655492001eee655492001eec655492005f6c6554920005ef7454920005ef735492005f6f53549200076d5354920005ec715492005f6f5154920007eb705492000dee705492000dec70549201efe87054920016ef6054920017eb60549201ef6e50549201ef6c50549201efea105492000dec765092003eec765092000cec7650920005ef7550920005ed7550920015ef7450920017af7450920007af645092003eee645092003eec6450920007ac6450920005ef7350920007ae4350920007ac4350920005ec7150920007eb705092000dee705092000dec70509201cfe87050920016ef6050920017eb60509201cfaf40509201cfad40509201cfea105092000dec764c920036ec764c92000cec764c920005ef754c920005ed754c920005ef744c920005ed744c920015ef734c920017cf734c920007cf634c920036ee634c920036ec634c920007cc634c920005ec714c920007eb704c92000dee704c92000dec704c9201afe8704c920016ef604c920017eb604c9201afea104c92001cfe75d8520004fd75d852001cfc75d852003cfe74d8520004fd74d8520034fe73d8520004fd73d852000cfd72d85202aeed72d8520006f751d8520006f451d85202def621d85202def521d85202deec21d8520014fd70d85202aef710d8520006f76198520025f970985200057f755852005d7c7558520005bf7458520005bc7458520005df7358520005dc735852004dfb7058520006f5611852001cfe7518520004fd7518520044fc751852003cfe7418520004fd7418520034fe7318520004fd731852000cfd7218520006f75118520046f45118520046f621185202d6f52118520044ff701852000cfe7018520014fd7018520046f9701852000cfc7018520046f71018520046fa1018520296f51018520004fe7694520004fd7694520044fc76945200067f659452001e7c6594520015ec7294520
  | 7 => 0x8530044fc7688530006ef6288530016ec6288530004ff7648530004fe7648530004fc7648530005bf7448530005bc744853001cfe76d952005e7e65d95201ecfd75d952003cfe74d9520004fd74d9520034fe73d9520004fd73d952000cff72d9520014fe72d952000cfd72d9520014fc72d952031e7f52d952031e7d52d9520044fe71d9520004fd71d952005e7c51d9520014ff70d9520014fd70d952030e7f50d952030e7d50d952001cff765952005e7c6559520005bf7459520005bc7459520005df7359520005dc7359520305ef7259520005f77159520005f47159520315fb705952030cff75595200067f7559520004ff7459520006bf7459520004bf745952003cfc7459520006bc745952003cbc7459520004ff7359520006df7359520004df7359520034fc7359520006dc7359520034dc735952005e7f5359520304ff7259520006ef7259520004ff7159520006f77159520004f77159520044fc7159520006f47159520004f471595201ecff7059520006fb70595201ee7e50595201ee7c505952003cfe76d912001cfe75d9120004fd75d912001cfc75d9120006bf54d9120006bc54d9120034fe73d9120004fd73d912000cff72d9120014fe72d912000cfd72d9120014fc72d91202febf42d91202febd42d9120044fe71d9120004fd71d9120014ff70d9120014fd70d91202f6bf40d91202f6bd40d91201ccfd7699120006bf6499120005de7399120005dd73991201cded7299120085f9709912003cff76591201ddef7259120095fb7059120004ff755912001cfe755912001cfc7559120006bf7459120004ff7359120034fc73591201dcff7259120006ef7259120004ff7159120044fc71591201ccff7059120006fb70591202f4fe761912003ebe6419120006bd641912003cff7695120004fe7695120004fd769512003cfc769512005f3f5495120015ee7295120005ed729512000dfa7095120005f97095120004ff7655120004fe7655120004fd7655120004fc7655120015ee7255120034fe76d8d2001cfe75d8d20004fd75d8d2001cfc75d8d2003cfe74d8d20004fd74d8d20006df53d8d20006dc53d8d2000cff72d8d20014fe72d8d2000cfd72d8d20014fc72d8d202eedf32d8d202eedd32d8d20044fe71d8d20004fd71d8d20014ff70d8d20014fd70d8d202e6df30d8d202e6dd30d8d201acfd7698d20005be7498d20005bd7498d20006df6398d201aded7298d20065f97098d20034ff7658d201bdef7258d20075fb7058d20004ff7558d2001cfe7558d2001cfc7558d20004ff7458d2003cfc7458d20006df7358d201bcff7258d20006ef7258d20004ff7158d20044fc7158d201acff7058d20006fb7058d202e4fe7618d2005d7e7518d200057d7518d20036de6318d20006dd6318d20034ff7694d20004f
  | 8 => 0x3cfc76951300067f659513001e7c659513006f3f5495130004ff7655130004fe7655130004fd7655130004fc7655130325de7694d30036de7694d30255dd7594d3001ede6594d3001edc6594d3000dde7094d3000ddc7094d30036df6094d30037db6094d3001cff7654d3000cfe7654d30254fd7654d3000cfc7654d300067f6554d3001e7c6554d300375c5354d30005fb7054d3000df87054d3000ddc7654d3001edc7654d3000cdc7654d30035df7554d300375f7554d300075f6554d3001ede6554d3001edc6554d3006f5c6554d3006f5f5254d3006f5c5154d30007db7054d3000dde7054d3000ddc7054d30257d87054d30036df6054d30037db6054d302575f5054d302575d5054d3000cfe76d0d3000cfc76d0d30006bf64d0d3003ebc64d0d3000dfa70d0d30005f970d0d3003cff7650d3000cfe7650d3020cfd7650d3000cfc7650d30006bf6450d3003ebc6450d30005fb7050d3000df87050d30014fe76d8930066ee62d893001cfe75d8930004fd75d893001cfc75d893003cfe74d8930004fd74d893000cfd73d8930014fc73d8930066ee32d8930044fe71d8930004fd71d8930066ec21d8930034fd70d89301beef20d8930066ec6258930004ff7654930004fe7654930004fc76549300067f655493001e7c65549300075d5354930004fe76d0930004fd76d093003cfc76d0930006bf64d093003ebc64d0930004ff7650930004fe7650930004fc7650930006bf645093003ebc645093000cfc764c930006ef624c930016ec624c930005fb704c93000df8704c93001cfe75d8530004fd75d853001cfc75d853003cfe74d8530004fd74d8530014fe72d8530004fd72d8530014fc72d8530034fd70d8530116f710d8530006f761985300057f755853006d7c7558530005bf7458530005bc7458530005ef7258530065ec7258530006f5611853001cfe7518530004fd7518530044fc751853003cfe7418530004fd7418530014fe7218530004fd7218530044fc7218530044ff7018530034fd7018530046f710185300cef51018530004fe7694530004fd7694530044fc76945300067f659453001e7c65945300075d5394530004ff7654530004fe7654530004fc7654530004fe76d0530004fd76d053003cfc76d0530004fe7690530004fd7690530044fc7690530006bf649053003ebc6490530004ff7650530004fe7650530004fc7650530005ef7250530065ec7250530004fe7610530004fd7610530044fc7610530006bf641053003ebc6410530035de7310530005dd731053000cfe768c530006f7618c530046f4618c53000dfa708c530005f9708c53000cfc764c530005bf744c530005bc744c530005ef724c530065ec724c530006f7614c530006f4614c530005fb704c53000df8704c530004fe7688530004fd768
  | 9 => 0xf7650b30004fd7650b30034fc7650b30346bf6450b3003ebc6450b3001cfe7598730004fd7598730044fc759873003cfe7498730004fd749873000cfe739873000cfc7398730014fe7298730004fd7298730044fc7298730046f67198730036f73198730046f43198730046f710987300fef51098730004ff755873001cfe755873001cfc7558730004ff7458730006bf7458730004bf745873003cfc7458730006bc745873003cbc745873000cfc7358730004ff7258730006ef7258730004ef7258730014fe7258730014fc7258730006ec7258730014ec7258730036f77158730036f73158730036f431587300e6f71058730044ff7694730034fe7694730004fd769473001e7e65947300067d65947300075d5394730004ff7654730004fd7654730034fc7654730005fb705473000df8705473003cff76d0730034fe76d0730004fd76d073003ebe64d0730006bd64d0730044ff7690730034fe7690730004fd769073033ebf649073003ebc6490730004ff7650730004fd7650730034fc765073003ebe6450730006bd6450730005ef7250730075ec7250730044ff7610730034fe7610730004fd7610730336bf641073003ebc6410730035de7310730005dd7310730044ff7688730034fe7688730004fd7688730016ec6288730004ff7648730004fd7648730034fc7648730005bf7448730005bc744873001cfe76d953006e7e65d953003cfe74d9530004fd74d953006e7c54d9530034fe73d953000cfd73d9530034fc73d953006e7f53d9530014fe72d9530004fd72d9530014fc72d953006e7f52d9530044fe71d9530004fd71d953006e7c51d9530034ff70d9530034fd70d95302667f50d95302667d50d953006e7c6559530005bf7459530005bc745953032ddf7359530264ff75595300067f7559530004ff7459530006bf7459530004bf745953003cfc7459530006bc745953003cbc745953032cff7359530006df7359530004ff7259530014fe7259530014fc7259530004ff7159530044fc7159530254ff7059530006fb705953003cfe76d913001cfe75d9130004fd75d913001cfc75d9130006bf54d9130006bc54d9130034fe73d9130034fc73d9130014fe72d9130004fd72d9130014fc72d9130044fe71d9130004fd71d9130034ff70d9130034fd70d9130226bf40d9130226bd40d9130006bf649913020ddd73991300057f755913006d7c755913023ddf7359130004ff75591300067f75591300047f755913001cfe755913001cfc75591300067c755913001c7c7559130006bf745913023cff7359130006df7359130004ff7259130014fe7259130014fc7259130004ff7159130044fc715913020cff7059130006fb7059130224fe761913003ebe6419130006bd641913003cff7695130004fe7695130004fd7695130
  | 10 => 0x540005bd739054033ebc6390540005bd7290540166be6290540166bc629054003dbe7190540006bf6190540007b76190540007b4619054000dbe709054015fba7090540007b9709054000dbc709054003ebf609054003fbb609054000cfc7650540005ef7250540085ec7250540006f76150540006f46150540005fb705054000df87050540175be761054003ebe761054003dbf7510540005bd751054003f9e7310540005bd731054003f9d73105400059d7310540336bc6310540005bd7210540136be6210540136bc621054015dbe711054003fb67110540006bf611054000dbe701054000dbc701054003ebf601054003fbb6010540004fe76cc540004fd76cc540034fc76cc54008d7e75cc5400057d75cc54003dbe74cc540005bd74cc5400079d43cc540004fe768c540004fd768c540044fc768c540005bf748c54003dbc748c540006df638c540036dc638c540004ff764c540004fe764c540004fc764c540005bf744c54003dbc744c5400079d434c540005ef724c540085ec724c540004fe760c540004fd760c540044fc760c54003dbe740c540005bd740c540006df630c540036dc630c540004fe7688540004fd7688540044fc7688540005bf748854003dbc7488540006ef6288540016ec6288540007af4288540004ff7648540004fe7648540004fc7648540005bf744854003dbc74485400367f7559730004ff745973003cfc7459730034ff735973000cfe7359730034fd735973000cfc73597300367e53597300367c5359730004ff7259730014fe7259730014fc725973007e7f5259730004ff7159730044fc715973007e7c51597302567f50597302567d5059730004ff755933001cfe755933001cfc7559330036bf7459330034ff735933000cfe7359330034fd735933000cfc7359330036be4359330036bc4359330004ff7259330014fe7259330014fc7259330006be4259330006bc4259330004ff7159330044fc715933020ebf405933020ebd405933003cff7695330034fe7695330004fd7695330034fc769533007f3f5495330004ff7655330034fe7655330004fd7655330034fc7655330005fb705533000df87055330035df7654f30356df7654f300375f7554f300375f6554f3001ede6554f30036dc6554f300375c6554f3007f5f5254f3007f5c5154f3000dde7054f3000ddc7054f302575f5054f302575d5054f30004ff7558b3001cfe7558b3001cfc7558b30004ff7458b3003cfc7458b3000cfe7358b30014fd7358b3000cfc7358b30036ef7258b30036ef3258b30036ec3258b30004ff7158b30044fc7158b301aeef2058b30004ff7654b30004fd7654b30034fc7654b3001e7e6554b300067d6554b300075d5354b3003cff76d0b30034fe76d0b30004fd76d0b3034ebf64d0b3003ebc64d0b30004f
  | 11 => 0x5be71d0d4000dbe70d0d4000dbc70d0d4003ebf60d0d4003fbb60d0d4000cfe7690d4020dbd7490d40006df6390d40036dc6390d4000dfa7090d40005f97090d4000cfc7650d40006df6350d40036dc6350d40005fb7050d4000df87050d4000dbc7650d40036bc7650d4000cbc7650d40005bf7550d40005bd7550d4003dbf7350d4003f9f7350d400079f6350d40036be6350d40036bc6350d400079c6350d400369c6350d40005bf7250d40216be6250d40216bc6250d40005bc7150d40007bb7050d4000dbe7050d4000dbc7050d4020fb87050d4003ebf6050d4003fbb6050d40014fe76d8940086ee62d894001cfe75d8940004fd75d894001cfc75d894000cfd74d8940014fc74d8940034fe73d8940004fd73d8940086ee42d8940044fe71d8940004fd71d8940086ec21d894003cfd70d89401deef20d8940086ec6258940004ff7654940004fe7654940004fc76549400067f655494001e7c655494035dbe76d094003ebe76d094003dbf75d0940005bd75d0940005bd73d094034ebc63d09401cdbd72d0940016be62d0940016bc62d0940005be71d0940087ac21d094000dbe70d094000dbc70d094003ebf60d094003fbb60d094000cfc7650940006ef6250940016ec625094003fac4250940005fb705094000df8705094003fb8405094000dbc7650940016bc765094000cbc7650940005bf7550940005bd7550940005bf7350940346bc635094003dbf725094003faf7250940007af6250940016be6250940016bc6250940087ac6250940005bc7150940007bb705094000dbe705094000dbc70509401cfb8705094003ebf605094003fbb60509401cfaf2050940004fe76cc940004fd76cc940034fc76cc94003dbe74cc940005bd74cc940006df63cc940036dc63cc940004ff764c940004fe764c940004fc764c94003dbe744c940005bd744c940006df634c940036dc634c94001cfe75d8540004fd75d854001cfc75d8540176bd74d8540034fe73d8540004fd73d8540006bf43d8540006bd43d8540014fe72d8540004fd72d8540014fc72d8540006bf42d8540006bd42d854003cfd70d8540176f710d8540006f761985400057f755854008d7c7558540005df7358540005dc7358540005ef7258540085ec7258540006f5611854001cfe7518540004fd7518540044fc7518540034fe7318540004fd7318540014fe7218540004fd7218540044fc7218540044ff701854003cfd7018540046f7101854012ef51018540004fe7694540004fd7694540044fc76945400067f659454001e7c6594540004ff7654540004fe7654540004fc7654540005bf745454003dbc745454000cfe7690540006f76190540046f4619054000dfa7090540005f9709054000dbe769054015ebe769054000cbe7690540005bf7590540005bd759
  | 12 => 0xd7690740005bf7590740005bd7590740005bd739074033ebe6390740005bd7290740166be629074003ebc629074003fb67190740006bd619074000dbe709074000dbc7090740034ff76cc74003cfe76cc740004fd76cc74009d7e75cc7400057d75cc74003dbe74cc740005bd74cc740036de63cc740006dd63cc7400079d43cc740044ff768c74003cfe768c740004fd768c740005bf748c74003dbc748c740004ff764c740004fd764c74003cfc764c740005bf744c74003dbc744c740036de634c740006dd634c7400079d434c740005ef724c740095ec724c740044ff760c74003cfe760c740004fd760c74003dbe740c740005bd740c740044ff768874003cfe7688740004fd7688740005bf748874003dbc7488740016ec62887402cfaf4288740004ff7648740004fd764874003cfc7648740005bf744874003dbc744874001cfe76d954008e7e65d954003cfe74d954000cfd74d954003cfc74d954008e7f54d9540034fe73d9540004fd73d954008e7c53d9540014fe72d9540004fd72d9540014fc72d954008e7f52d9540044fe71d9540004fd71d954008e7c51d954003cff70d954003cfd70d95402867f50d95402867d50d954008e7c655954036dbf7459540005df7359540005dc7359540284ff75595400067f755954036cff7459540006bf7459540004ff7359540006df7359540004df7359540034fc7359540006dc7359540034dc7359540004ff7259540014fe7259540014fc7259540004ff7159540044fc7159540274ff7059540006fb7059540365be769514003ebe7695140275bd759514001ebe659514001ebc6595140005bd7395140005bd7295140005be719514000dbe709514000dbc709514003ebf609514003fbb609514001cff765514000cfe7655140274fd765514000cfc76551400067f655514001e7c6555140005fb705514000df8705514000dbc765514001ebc765514000cbc765514003dbf755514003f3f75551400073f655514001ebe655514001ebc655514008f3c6555140005bf7355140005bf7255140005bc7155140007bb705514000dbe705514000dbc7055140277b8705514003ebf605514003fbb6055140034fe76d8d4001cfe75d8d40004fd75d8d4001cfc75d8d40006df53d8d40006dc53d8d40014fe72d8d40004fd72d8d40014fc72d8d40044fe71d8d40004fd71d8d4003cfd70d8d4023edf30d8d40006df6398d400057f7558d4008d7c7558d40036de6318d40006dd6318d40004fe7694d40004fd7694d40034fc7694d400067f6594d4001e7c6594d4003dbe7494d40005bd7494d4008f5f5394d40004ff7654d40004fe7654d40004fc7654d401f5be76d0d4003ebe76d0d4003dbf75d0d40005bd75d0d40036be63d0d40036bc63d0d40005bd72d0d40246be62d0d40246bc62d0d40
  | 13 => 0x8550044fc7688550004ff7648550004fe7648550004fc7648550005bf7448550005bc744855003e7f755974003cff745974000cfe745974003cfd745974000cfc745974003e7e545974003e7c5459740004ff7359740034fc7359740004ff7259740014fe7259740014fc725974009e7f5259740004ff7159740044fc715974009e7c51597402767f50597402767d505974003dbf765534037ebf765534003f3f755534001ebe655534003ebc6555340005bf7355340005bf7255340005bc715534000dbe705534000dbc7055340004ff7558f4001cfe7558f4001cfc7558f4000cfc7458f4003edf7358f4003edf4358f4003edc4358f40004ff7258f40014fe7258f40014fc7258f40006de3258f40006dc3258f40004ff7158f40044fc7158f4020edf3058f40034ff7694f4003cfe7694f40004fd7694f4003dbe7494f40005bd7494f4009f5f5394f40004ff7654f40004fd7654f4003cfc7654f4003dbe7454f40005fb7054f4000df87054f4003dbf7650f40006bf7650f40005bf7550f40005bd7550f4003f9f7350f40036be6350f40036bc6350f40005bf7250f40216be6250f4003ebc6250f40005bc7150f4000dbe7050f4000dbc7050f40004ff7558b4001cfe7558b4001cfc7558b4000cfe7458b40014fd7458b4000cfc7458b40004ff7358b40034fc7358b4003eef7258b4003eef4258b4003eec4258b40004ff7158b40044fc7158b401ceef2058b40004ff7654b40004fd7654b4003cfc7654b4001e7e6554b400067d6554b4003dbe7454b4003dbf7650b40376bf7650b40005bf7550b40005bd7550b40005bf7350b40346be6350b4003faf7250b4003faf6250b40016be6250b40016bc6250b4003fac6250b40005bc7150b4000dbe7050b4000dbc7050b401cfaf2050b40034ff76ccb4003cfe76ccb40004fd76ccb4003dbe74ccb40005bd74ccb40004ff764cb40004fd764cb4003cfc764cb4003dbe744cb40005bd744cb4001cfe7598740004fd7598740044fc759874000cfe749874000cfc7498740034fe7398740004fd7398740014fe7298740004fd7298740044fc7298740046f6719874003ef74198740046f44198740046f7109874015ef51098740004ff755874001cfe755874001cfc755874000cfc745874003ebc745874000cbc7458740004ff7358740034fc735874003ebf4358740006bd4358740004ff7258740006ef7258740004ef7258740014fe7258740014fc7258740006ec7258740014ec725874003ebf4258740006bd425874003ef7715874003ef7415874003ebc415874003ef44158740146f71058740044ff769474003cfe7694740004fd769474001e7e65947400067d659474003dbc7494740004ff7654740004fd765474003cfc7654740005bf745474003dbc745474003dbd7690740006b
  | 14 => 0x367c6354d500075c6354d500077b7054d5000d7e7054d5000d7c7054d50257787054d5000d787054d5001e7f6054d5001f7b6054d50004fe76d0d50004fd76d0d5003cfc76d0d50006df63d0d50036dc63d0d50004fe7690d50004fd7690d50034fc7690d5001d7e7590d500057d7590d50006bf6490d5003ebc6490d50004ff7650d50004fe7650d50004fc7650d50004fe7610d50004fd7610d50034fc7610d5001d7e7510d500057d7510d50006bf6410d5003ebc6410d50006df6310d50036dc6310d50014fe76d89500a6ee62d895000cfd75d8950014fc75d895003cfe74d8950004fd74d8950034fe73d8950004fd73d895038e7f53d89500067d53d89500a6ee52d895038eed52d8950044fe71d8950004fd71d895001cfd70d89503067e50d89503067c50d8950306ef20d8950005bf7458950005bc7458950005df7358950005dc73589500a6ec6258950005f77158950005f47158950385fb7058950004fe76d0950004fd76d095003cfc76d0950004ff7650950004fe7650950004fc7650950004fe76cc950004fd76cc950034fc76cc95001d7e75cc9500057d75cc950005be74cc950005bd74cc950004ff764c950004fe764c950004fc764c95000cfd75d855003cfe74d8550004fd74d8550034fe73d8550004fd73d8550014fe72d8550004fd72d8550014fc72d855029ef651d855029ef551d8550006f721d8550006f421d855001cfd70d85502b6f710d8550005be7498550005bd7498550005de7398550005dd7398550006f7619855002df97098550055fb7058550006f5611855000cfd751855003cfe7418550004fd7418550034fe7318550004fd73185502be7f53185500067d5318550014fe7218550004fd7218550044fc7218550046f651185502bef55118550006f72118550046f42118550044ff701855001cfd70185502a67e50185502a67c5018550046f710185502a6f51018550004fe76d0550004fd76d055003cfc76d0550006bf64d055003ebc64d0550004fe7690550004fd7690550044fc7690550004ff7650550004fe7650550004fc7650550006bf645055003ebc6450550005ef72505500a5ec7250550004fe7610550004fd7610550044fc761055001d7e75105500057d7510550005de7310550005dd731055000dfa7010550005f97010550004fe76cc550004fd76cc550034fc76cc55001d7e75cc5500057d75cc550006df63cc550036dc63cc550004fe768c550004fd768c550044fc768c550004ff764c550004fe764c550004fc764c550005bf744c550005bc744c550006df634c550036dc634c550005ef724c5500a5ec724c550004fe760c550004fd760c550044fc760c55001d7e750c5500057d750c550005be740c550005bd740c55000dfa700c550005f9700c550004fe7688550004fd768
  | 15 => 0xe7650d21004fd7650d21004fc7650d21006bf6450d2103ebc6450d21034ff7610d21004fe7610d21004fd7610d21034fc7610d21006bf6410d2103ebc6410d21005f67110d21005f57110d213a4fe7694521006bf6494521006bc64945210b7775194521047e4219452101cff7654521014fe7654521194fd7654521014fc76545210067f655452101e7c6554521006bf6454521006bc6454521005ef7254521015ec7254521197e42154521014fe76d0521014fc76d0521006bf64d052103ebc64d0521015ee72d0521005ed72d052117fe421d0521134fe7690521166bf649052103ebc649052103cff7650521014fe765052114cfd7650521014fc7650521006bf645052103ebc6450521005ef7250521015ec7250521164fe7610521006bf641052103ebc6410521005de7310521005dd7310521047e42110521014fe76cc521014fc76cc5210b57e75cc5210057d75cc521006bf64cc521006bc64cc521006df63cc521036dc63cc521015ee72cc521005ed72cc5210d4fe768c521006bf648c521006bc648c521034ff764c521014fe764c5210ecfd764c521014fc764c521005bf744c521005bc744c521006bf644c521006bc644c521006df634c521036dc634c521005ef724c521015ec724c521104fe760c521005be740c521005bd740c521006bf640c521006bc640c521007af64885212ceee64885212ceec6488521007ac6488521006ac64885212c6ee63885212c6ec6388521045ee7188521047e67188521046ef6188521017e7618852100cfe76d8121006bf64d8121006bc64d81210aefa60d812101cfe75d8121004fd75d812101cfc75d812103cfe74d8121004fd74d8121034fe73d8121004fd73d812100cfc72d8121014fd71d8121006ee21d812104eec21d81210aefa20d81210aefa10d81210057f75581210b57c7558121005bf7458121005bc7458121006bf6458121006bc6458121005df7358121005dc73581210aef8605812103cfe76d915000cfd75d915039ebe54d915039ebd54d9150034fe73d9150004fd73d9150014fe72d9150004fd72d9150014fc72d9150006be42d9150006bc42d9150044fe71d9150004fd71d915001cfd70d915036ebf40d9150006bf649915008df97099150005df7359150005dc735915009dfb705915003ebe6419150006bd6419150034fe76d8d5000cfd75d8d5003cfe74d8d50004fd74d8d50396de53d8d50396dd53d8d50014fe72d8d50004fd72d8d50014fc72d8d50006de32d8d50006dc32d8d50044fe71d8d50004fd71d8d5001cfd70d8d5032edf30d8d50006df6398d5006df97098d50005bf7458d50005bc7458d5007dfb7058d50036de6318d50006dd6318d5000d7c7654d500367c7654d5000c7c7654d5001d7f7354d5001f5f7354d500075f6354d500367e6354d50
  | 16 => 0x9121006bf7459121004ff7359121034fc735912114cff7259121006ef7259121004ef725912117cff7159121006f77159121004ff705912100cfe705912100cfc7059121164fe761912103ebe6419121006bd6419121165be7619121006be7619121164be7619121006bf6519121006be6519121006bd6519121006bc6519121137b72119121137ac2119121137b42119121006be6019121006bc601912103ebf751912103ebe751912103ebd751912103ebc751912103ebf731912103ebe731912103ebd731912103ebc7319121006bf5319121006bc531912103ebf721912103ebe721912103ebd721912103ebc7219121136bf5219121136be5219121136bd5219121136bc5219121136bf3219121136be3219121136bd3219121136bc321912103ebf711912103ebd7119121006bf5119121006bc5119121136bf2119121136be2119121136bd2119121136bc2119121136ac211912103ebf701912103ebe701912103ebd701912103ebc7019121006bf5019121006be5019121006bc5019121006be3019121006bc3019121136bf2019121136be2019121136bd2019121136bc2019121006be1019121006bc101912103cff7695121004fe7695121004fd769512103cfc7695121006bf649512103ebc64951210b73f5495121004ff7655121004fe7655121004fd7655121004fc7655121006bf645512103ebc6455121034fe76d8d21006bf64d8d21006bc64d8d2101cfe75d8d21004fd75d8d2101cfc75d8d2103cfe74d8d21004fd74d8d21044ff72d8d21104fd72d8d21106df32d8d21106dd32d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21006dc30d8d210b57e7598d210057d7598d21005be7498d21005bd7498d21006bf6498d21006bc6498d21006df6398d210edf57198d21005bf7458d21005bc7458d21006bf6458d21006bc6458d2111df77158d21004ff7558d2101cfe7558d2101cfc7558d21004ff7458d21006bf7458d21004bf7458d2103cfc7458d21006bc7458d2103cbc7458d21006df7358d210ecff7258d21006ef7258d21004ef7258d2111cff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21104fe7618d21006bf6418d21006bc6418d21036de6318d21006dd6318d21034ff7694d21004fe7694d21004fd7694d21034fc7694d21006bf6494d21006bc6494d21006df6394d21036dc6394d210b75f5394d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d2101e7c6554d21006bf6454d21006bc6454d21006df6354d21036dc6354d2103cff76d0d21004fe76d0d21004fd76d0d2103cfc76d0d21006bf64d0d2103ebc64d0d21034ff7690d21004fe7690d21004fd7690d21034fc7690d21006bf6490d2103ebc6490d21004ff7650d21004f
  | 17 => 0x2c7e671cca21005ed71cca212c7e571cca21016ee61cca21017e661cca21005ed70cca213acff76546210467f65546210467c6554621197e7215462114cfd76d0621046bf64d0621046bc64d0621015ec72d06212cfaf42d062117cff7650621046bf6450621046bc6450621005ef7250621015ec7250621007af42506210ecfd76cc6210c57e75cc6210057d75cc621046df63cc621046dc63cc621015ec72cc6212c7cf32cc62111cff764c621005bf744c621005bc744c621046df634c621046dc634c621005ef724c621015ec724c621007cf324c62100cff76582210057f75582210c57c7558221046f86058221004ff75582210067f75582210047f755822101cfe755822101cfc75582210067c755822101c7c7558221004ff745822103cfc7458221004ff7358221034fc7358221044fc71582210befa2058221046fb1058221046f8105822101cfe76d95210b67e65d952103cfe74d9521004fd74d9521034fe73d9521004fd73d95210b67f53d9521044ff72d95211a4fd72d95211a67f52d95211a67d52d9521014fd71d95210b67f51d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210b67c50d95210b67c6559521005bf7459521005bc74595213adf771595211a4ff75595210067f7559521004ff7459521006bf7459521004bf745952103cfc7459521006bc745952103cbc7459521004ff7359521034fc7359521194ff7259521006ef72595213acff7159521006f77159521004ff705952100cfe705952100cfc705952103cfe76d912101cfe75d9121004fd75d912101cfc75d9121006bf54d9121006bc54d9121034fe73d9121004fd73d9121044ff72d9121164fd72d9121166bf42d9121166bd42d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121006bc40d912103cbe76d9121006bf65d9121006be65d9121006bd65d9121006bc65d9121167b721d9121167ac21d9121167b421d9121006be60d9121006bc60d9121006bf75d9121006be75d9121006bd75d9121006bc75d9121006bf73d9121006be73d9121006bd73d9121006bc73d9121006bf53d9121006bc53d9121166bf72d9121166be72d9121166bd72d9121166bc72d9121166bf52d9121166be52d9121166bd52d9121166bc52d9121166bf32d9121166be32d9121166bd32d9121166bc32d9121166bf71d9121166bd71d9121006bf51d9121006bc51d9121166bf21d9121166be21d9121166bc21d9121006bf70d9121006be70d9121006bd70d9121006bc70d9121006bf50d9121006be50d9121006bc50d9121006be30d9121006bc30d9121166bf20d9121166be20d9121166bd20d9121166bc20d9121006be10d9121006bc10d9121006bf649912114df5719912117df77159121004ff755912101cfe755912101cfc755
  | 18 => 0xc75d9221034fe73d9221004fd73d9221046ed72d9221166be42d9221166bc42d9221166ec42d9221044fe71d9221046f671d922100cfe70d9221004fd70d922100cfc70d9221166ef20d922114cfd7699221046bf6499221046bc649922103cff7659221046bc6459221004ff755922101cfe755922101cfc7559221046bf7459221004ff7359221034fc7359221006ef725922114ebf425922114ebd425922114eec4259221044fe7159221044fc7159221046be4159221046bc4159221004ff705922100cfe705922100cfc705922114eef205922103cff7695221044fe7695221004fd7695221044fc76952210c73f5495221004ff7655221044fe7655221004fd7655221044fc7655221005ef7255221015ec725522101cfe75d8e21004fd75d8e21044fc75d8e2103cfe74d8e21004fd74d8e21046ed72d8e21106ec32d8e21044fe71d8e21046f671d8e2100cfe70d8e21004fd70d8e2100cfc70d8e21106ef20d8e210ecfd7698e210c57e7598e210057d7598e21046df6398e21046dc6398e21034ff7658e21005bf7458e21005bc7458e21046dc6358e21004ff7558e2101cfe7558e2101cfc7558e21004ff7458e21006bf7458e21004bf7458e2103cfc7458e21006bc7458e2103cbc7458e21046df7358e21006ef7258e210eedf3258e210eedd3258e210eeec3258e21044fe7158e21044fc7158e21046de3158e21046dc3158e21004ff7058e2100cfe7058e2100cfc7058e210eeef2058e21034ff7694e21044fe7694e21004fd7694e21044fc7694e210c75f5394e21004ff7654e21044fe7654e21004fd7654e21044fc7654e210067f6554e2101e7c6554e21005ef7254e21015ec7254e2103cff76d0e21044fe76d0e21004fd76d0e21044fc76d0e2103ebe64d0e21006bd64d0e21015ee72d0e21005ed72d0e21247ac42d0e21034ff7690e21044fe7690e21004fd7690e21044fc7690e21006bf6490e2103ebc6490e21036de6390e21006dd6390e21015ee7290e21005ed7290e21004ff7650e21044fe7650e21004fd7650e21044fc7650e2103ebe6450e21006bd6450e21036de6350e21006dd6350e21005ef7250e21015ec7250e21217ac4250e21034ff7610e21044fe7610e21004fd7610e21044fc7610e21006bf6410e2103ebc6410e21015ec7210e21045f67110e21005f57110e212ceed76d0a21015ee74d0a21017ae74d0a212ceef64d0a212cfae64d0a212ceed64d0a21007ad64d0a212c5ee73d0a21007ae43d0a212cfac43d0a212cfe671d0a21005ed71d0a212cfe571d0a21016ee61d0a21017e661d0a21005ed70d0a212c6ed76cca212cdee74cca212c7ae74cca21005ae74cca212c7ad74cca212c5ec74cca21015ee73cca21017ce73cca212c6ef63cca212c7ce63cca212c6ed63cca21007cd63cca21
  | 19 => 0x9031046bc3159031006bf2159031046be2159031046bc2159031006bf7059031006be7059031006bd7059031006bc7059031006bf5059031006be5059031006bc5059031036bf3059031036be3059031036bd3059031036bc3059031006bf2059031006be2059031006bc2059031046bf1059031006be1059031046bc105903103cff7695031044fe7695031004fd7695031044fc769503103ebe6495031006bd64950310df3f5495031004ff7655031044fe7655031004fd7655031044fc765503103ebe6455031006bd6455031004ff755883101cfe755883101cfc7558831004ff745883103cfc7458831044ff7258831046ef72588310d6ee5258831036ef3258831036ec3258831036df3158831046ee2158831046ec2158831004ff705883100cfe705883100cfc70588310d6ef2058831004ff7654831004fd7654831044fc765483101e7e65548310067d6554831006be6454831006bd6454831016ee6254831006ed625483103cff76d0831044fe76d0831004fd76d083103ebe64d0831006bd64d0831004ff7650831004fd7650831044fc765083103ebe6450831006bd6450831005f77150831045f47150831044ff759843101cfe759843110cfd7598431044fc7598431044ff749843103cfe7498431004fd7498431044fc7498431014fe7298431046df3198431036f73198431046f4319843100cfe709843110cff7654431006be6454431006bd6454431004fd76d043103ebe64d0431006bd64d0431004ff765043103ebe6450431006bd6450431005ef72504310d5ec7250431045df764c431006df764c431004df764c4310079f744c4310079c744c431046df644c4310479e644c431006dd644c4310479d644c4310069d644c431007cf724c431007cc724c431006dd624c431045df714c431037d7714c431046de614c431047d6614c431047d6514c431007d5514c431047d6414c431007d5414c431004ff755803101cfe755803101cfc7558031004ff745803103cfc745803100cfd7358031004ff7258031014fe7258031014fc7258031036f63158031036f53158031046fb70580310cefa5058031036fb3058031036f830580310cefa2058031046fb1058031046f81058031194fd75d962103cfe74d9621004fd74d9621034fe73d9621004fd73d96210c67f53d9621046ed72d9621044fe71d9621046f671d96210467f51d962100cfe70d9621004fd70d962100cfc70d96210067e50d96210c67c50d96211a6ef20d962101cff76596210467c65596210467f7559621004ff745962103cfc7459621004ff7359621034fc73596211967f52596211967d5259621044fe7159621044fc71596210467e51596210467c5159621004ff705962100cfe705962100cfc7059621196ef205962101cfe75d9221004fd75d9221044f
  | 20 => 0x6ef628c531106ec628c531035f6718c531045df748c531005dd748c5310079f648c5310079c648c531005dd728c531007cf628c531007cc628c531045de718c531037d7618c53100cfe76d8131006bf64d8131006bc64d8131006ef62d8131006ec62d81310e6fa60d813101cfe75d8131004fd75d813101cfc75d813103cfe74d8131004fd74d813100cfc73d8131014fe72d8131004fd72d8131014fc72d8131034fd71d8131006fb50d81310e6f850d81310e6fa30d81310e6fa10d81310057f75581310f57c7558131005bf7458131005bc7458131006bf6458131006bc6458131005ef72581310edec7258131006ef6258131006ec62581310e6f86058131044ff75594310467f7559431004ff745943103cfc7459431034fe7359431034fc73594310367e53594310367c5359431004ff7259431014fe7259431014fc72594310de7f5259431044fc71594310467e51594310467c5159431004ff705943100cfe705943100cfc70594310de7f505943103ebf759903103ebe759903103ebd759903103ebc7599031036bf7399031036be7399031036bd7399031036bc7399031036bf5399031036be5399031036bd5399031036bc539903103ebf729903103ebe729903103ebd729903103ebc7299031006bf5299031006be5299031006bc5299031036bf3299031036be3299031036bd3299031036bc3299031046be7199031046bc7199031006bf5199031046be5199031046bc5199031036bf3199031046be3199031036bd3199031046bc3199031006bf2199031046be2199031046bc219903103ebf709903103ebe709903103ebd709903103ebc7099031006bf5099031006be5099031006bc5099031036bf3099031036be3099031036bd3099031036bc3099031006bf2099031006be2099031006bc2099031046bf1099031006be1099031046bc1099031004ff755903101cfe755903101cfc7559031044ff7459031046bf7459031006bf5459031006bc5459031034fe7359031034fc7359031036be4359031036bc4359031004ff7259031014fe7259031014fc7259031006be4259031006bc4259031044fc7159031046be4159031046bc4159031036df3159031004ff705903100cfe705903100cfc7059031006be4059031006bc4059031006bf7559031006be7559031006bd7559031006bc7559031036bf7359031036be7359031036bd7359031036bc7359031036bf5359031036be5359031036bd5359031036bc5359031006bf7259031006be7259031006bd7259031006bc7259031006bf5259031006be5259031006bc5259031036bf3259031036be3259031036bd3259031036bc3259031046be7159031046bc7159031006bf5159031046be5159031046bc5159031036bf31590310369f3159031046be3159031036bd315
  | 21 => 0xc70d8931006ef50d8931006ee50d8931006ec50d8931006ee40d8931006ec40d89312c6ef30d8931006ee30d89312c6ec30d8931006ee10d8931006ec10d8931005bf7458931005bc7458931006bf6458931006bc64589310eeec6258931005ee76189310eeee76189310ef6e75189310ef6d7518931006ef6518931006ee6518931006ed6518931006ec6518931006ef6418931007af6418931006af6418931006ee6418931006ed6418931006ec6418931007ac6418931006ac64189310efcd7318931007ce4318931007cd431893111eef61189313b7e731189313b7e43118931006ee6018931006ec6018931004ff7654931004fe7654931004fc765493101e7e65549310067d6554931006bf6454931006bc6454931006ef6254931016ec6254931005f77154931005f47154931004fe76d0931004fd76d093103cfc76d0931006bf64d093103ebc64d0931035de73d0931005dd73d09310079e43d0931006ef62d0931016ec62d0931004ff7650931004fe7650931004fc7650931006bf645093103ebc64509310079e4350931006ef6250931016ec6250931005de76cc931036de76cc931035df74cc9310379e74cc931005dd74cc9310379d74cc9310059d74cc9310079f64cc9310079c64cc9310eddd72cc931007cf62cc931016de62cc931016dc62cc9310efcc62cc931016cc62cc931045de71cc931036df61cc931037d761cc9310efcc21cc931014fc764c931006bf644c931006bc644c931006ef624c931016ec624c931005f7714c931005f4714c9310eddc764c931016dc764c931014dc764c931005df744c931005dd744c9310079f644c9310079c644c931035df724c931037cf724c931007cf624c931016de624c931016dc624c9310efcc624c931007d7714c931045dc714c931007d4714c931036df614c931037d7614c9310efcf204c931124fe769453101e7e65945310067d6594531006bf6494531006bc6494531006ef62945311a6ec62945310f777519453101cff76545310f4fd7654531034fc76545310067f655453101e7c6554531006bf6454531006bc6454531005df7354531035dc7354531006ef6254531196ec6254531034fe76d0531034fc76d0531006bf64d053103ebc64d0531035de73d0531005dd73d05310079d43d0531006ef62d053117eec62d0531004fe7690531006bf649053103ebc64905310079e4390531006ef6290531166ec629053103cff7650531004fd7650531034fc7650531006bf645053103ebc6450531005df7350531035dc73505310079d4350531005ef72505310edec7250531006ef625053114eec6250531004fe7610531006bf641053103ebc6410531035de7310531005dd73105310079e4310531006ef6210531136ec6210531007b54110531006bf648c531006bc648c531
  | 22 => 0x913103ebd7119131006bf5119131006bc5119131336bf3119131006bd3119131336bc3119131006bf2119131006bc211913103ebf701913103ebe701913103ebd701913103ebc7019131006bf5019131006be5019131006bc5019131336bf3019131006be3019131336bc3019131006bf2019131006be2019131006bc2019131006be1019131006bc101913103cff7695131004fe7695131004fd769513103cfc7695131006bf649513103ebc64951310f73f5495131035de7395131005dd739513128eec6295131005f67195131005f57195131004ff7655131004fe7655131004fd7655131004fc7655131006bf645513103ebc645513127eec625513101cfc7654d310067f6554d3101e7c6554d31006bf6454d31006bc6454d310375c5354d3125eec6254d31005f77154d31005f47154d31037d43154d31004fe76d0d31006bf64d0d3103ebc64d0d31246ec62d0d31005f671d0d31005f571d0d31005de7690d31036de7690d31005dd7490d310079f6490d3103ede6490d3103edc6490d310079c6490d3103e9c6490d31005dd7290d31045de7190d31036df6190d31037d76190d3103cfc7650d31006bf6450d3103ebc6450d310379c4350d31216ec6250d31005f77150d31005f47150d31037d43150d3103edc7650d3103cdc7650d31035df7450d310379f7450d310079f6450d3103ede6450d3103edc6450d310079c6450d31005df7250d313bf9e4250d313bf9c4250d31007d77150d31045dc7150d31007d47150d31036df6150d31037d76150d31014fe76d8931006bf64d8931006bc64d89310eeee62d893101cfe75d8931004fd75d893101cfc75d893103cfe74d8931004fd74d8931006ef52d89310eeee52d89310eeec52d89310eeee42d89310eeec42d89310eeee32d8931034fd71d89310eeef21d893100cfe70d8931004fd70d893100cfc70d89310eeef20d8931006ee20d89310eeec20d89310edee76d8931014ee76d8931006ef65d8931006ee65d8931006ed65d8931006ec65d8931006ef64d8931007af64d8931006af64d8931006ee64d8931006ed64d8931006ec64d8931007ac64d8931006ac64d8931007cf73d8931007ce43d8931007cd43d89312c7e731d89312c7e431d8931006ee60d8931006ec60d8931006ef75d8931006ee75d8931006ed75d8931006ec75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d8931006ee54d8931006ed54d8931006ec54d8931006ef73d89310eeee73d8931006ef53d89312c6ee53d8931006ed53d89312c6ec53d8931006ef43d89312c6ee43d8931006ed43d89312c6ec43d89312c6ef71d89310eeee71d8931006ed71d8931006ef51d8931006ec51d89312c6ef31d89312c6ec31d8931006ef70d8931006ee70d8931006ed70d8931006e
  | 23 => 0xf67c50d95310f67c6559531005bf7459531005bc7459531005ef72595310edec7259531005fb70595310e5f870595310f4ff75595310067f7559531004ff7459531006bf7459531004bf745953103cfc7459531006bc745953103cbc745953110cff7359531006df7359531004ff7259531006ef7259531004ef7259531014fe7259531014fc7259531006ec7259531014ec72595310f67f5259531124ff7159531006f771595310f67c5159531004ff7059531006fb7059531004fb705953100cfe705953100cfc7059531006f8705953100cf8705953103cfe76d913101cfe75d9131004fd75d913101cfc75d9131006bf54d9131006bc54d9131014fe72d9131004fd72d9131014fc72d9131006be42d9131006bc42d913100cfe70d9131004fd70d913100cfc70d9131006be40d9131006bc40d913103cbe76d9131006bf65d9131006be65d9131006bd65d9131006bc65d91310079f73d9131006be62d9131006bc62d913133fb731d913133fb431d9131006be60d9131006bc60d9131006bf75d9131006be75d9131006bd75d9131006bc75d9131006bf73d913133ebe73d9131006bd73d913133ebc73d9131006bf53d913133ebe53d913133ebc53d9131006bf72d9131006be72d9131006bd72d9131006bc72d9131006bf52d9131006be52d9131006bc52d913133ebf32d9131006be32d913133ebc32d913133ebf71d9131006bd71d9131006bf51d9131006bc51d913133ebf31d913133ebc31d9131006bf21d9131006bc21d9131006bf70d9131006be70d9131006bd70d9131006bc70d9131006bf50d9131006be50d9131006bc50d913133ebf30d9131006be30d913133ebc30d9131006bf20d9131006be20d9131006bc20d9131006be10d9131006bc10d9131006bf64991310edee7299131005ed7299131005ef72591310edec7259131004ff755913101cfe755913101cfc7559131006bf7459131004ff7359131006df7359131004ff7259131006ef7259131004ef7259131014fe7259131014fc7259131006ec7259131014ec7259131004ff7159131006f77159131004ff705913100cfe705913100cfc7059131004fe761913103ebe6419131006bd6419131005be7619131006be7619131004be7619131006bf6519131006be6519131006bd6519131006bc65191310079d7319131006be6219131006bc6219131337b73119131337b43119131006be6019131006bc601913103ebf751913103ebe751913103ebd751913103ebc751913103ebf731913103ebe731913103ebd731913103e9d731913103ebc7319131006bf5319131336be5319131336bc531913103ebf721913103ebe721913103ebd721913103ebc7219131006bf5219131006be5219131006bc5219131336bf3219131006be3219131336bc321913103ebf711
  | 24 => 0xe74d9631004fd74d9631046dd73d9631014fe72d9631004fd72d9631044fc72d9631046f671d963100cfe70d9631004fd70d963100cfc70d96310467c65596310467f7559631004ff745963103cfc745963110e7f5359631004ff7259631014fe7259631014fc725963110e7f5259631044fc71596310467e51596310467c5159631004ff705963100cfe705963100cfc705963101cfe75d9231004fd75d9231044fc75d9231046dd73d923133ebe43d923133ebc43d9231014fe72d9231004fd72d9231044fc72d9231006be42d9231006bc42d9231046f671d923100cfe70d9231004fd70d923100cfc70d9231046bf6499231046bc6499231046bc6459231004ff755923101cfe755923101cfc7559231046bf7459231004ff7259231014fe7259231014fc7259231044fc7159231046be4159231046bc4159231004ff705923100cfe705923100cfc705923103cff7695231044fe7695231004fd7695231044fc769523110f3f5495231045f67195231005f57195231004ff7655231044fe7655231004fd7655231044fc7655231036f73158e3101cff7654e3101e7e6554e310067d6554e31005f77154e31045f47154e31037d73154e3103ebe64d0e31006bd64d0e31045f671d0e31005f571d0e3103cff7650e3103ebe6450e31006bd6450e31005f77150e31045f47150e31005bf7458a31005bc7458a31046ec6258a31004ff7558a3101cfe7558a3101cfc7558a31004ff7458a31006bf7458a31004bf7458a3103cfc7458a31006bc7458a3103cbc7458a31106ee3258a31044fc7158a31046ee2158a31046ec2158a31004ff7058a3100cfe7058a3100cfc7058a31004ff7654a31004fd7654a31044fc7654a3101e7e6554a310067d6554a31005f77154a31045f47154a3103cff76d0a31044fe76d0a31004fd76d0a3103ebe64d0a31006bd64d0a31004ff7650a31004fd7650a31044fc7650a3103ebe6450a31006bd6450a31014ff764ca31016ee624ca31006ed624ca31005f7714ca31045f4714ca310dcff7654631046bf64d0631046bc64d0631046bf6450631046bc6450631005ef7250631105ec7250631047b44150631045dd76cc631036dd76cc6310375e75cc6310375d75cc631046df64cc631006dd64cc631006dd62cc631047d661cc631047d651cc631007d551cc631046f86058231004ff755823101cfe755823101cfc7558231004ff745823103cfc7458231004ff7258231014fe7258231014fc7258231044fc71582310fefa30582310fefa2058231046fb1058231046f8105823101cfe76d95310f67e65d953103cfe74d9531004fd74d95310f4fd73d95310f67f53d9531014fe72d9531004fd72d9531014fc72d9531034fd71d95310f67f51d953100cfe70d9531004fd70d953100cfc70d95310067e50d9531
  | 25 => 0x97310367f31597310367e31597310367d31597310367c31597310067f21597310067c21597310067f70597310067e70597310067d70597310067c70597310067e40597310067c40597310367f30597310367e30597310367d30597310367c30597310067f20597310067e20597310067c20597310067e10597310067c1059731004ff755933101cfe755933101cfc7559331036bf7459331034fc7359331036be4359331036bc4359331004ff7259331014fe7259331014fc7259331006be4259331006bc4259331004ff705933100cfe705933100cfc705933103cff7695331034fe7695331004fd7695331034fc769533101e7e65953310067d65953311273f5495331035de7395331005dd7395331004ff7655331034fe7655331004fd7655331034fc765533101e7e65553310067d6555331035df7650f31006df7650f310375e6550f310375d6550f310379f7450f310379f6450f3103ede6450f31036dc6450f310379c6450f31005df7250f313c79e4250f313c79c4250f31045dc7150f31004ff7558b3101cfe7558b3101cfc7558b31004ff7458b3103cfc7458b31036ef7258b3111eec4258b31036ef3258b31036ec3258b3111eef2158b31004ff7058b3100cfe7058b3100cfc7058b3111eef2058b31004ff7654b31004fd7654b31034fc7654b3101e7e6554b310067d6554b3103cff76d0b31034fe76d0b31004fd76d0b311e67e65d0b310067d65d0b3134ebf64d0b3103ebc64d0b31035de73d0b31005dd73d0b3134f9e43d0b31016ee62d0b31006ed62d0b31004ff7650b31004fd7650b31034fc7650b311d67e6550b310067d6550b31346bf6450b3103ebc6450b31035de7350b313479e4350b31005f77150b31005f47150b31035df764cb310d6df764cb310375e654cb310375d654cb31005df744cb31005dd744cb31037cf724cb31016de624cb31016dc624cb31045dc714cb3111fcf204cb310f4fd769473101e7e65947310067d659473101cff7654731034fc765473101e7e65547310067d6554731005df7354731035dc73547311867e65d07310067d65d073103ebe64d0731006bd64d0731035de73d0731005dd73d07310079d43d073116e7e65907310067d659073133ebf649073103ebc6490731045dc739073133f9e439073103cff76507311567e65507310067d655073103ebe6450731006bd6450731005df7350731035dc73507310079d4350731005ef725073111dec725073113e7e65107310067d6510731336bf641073103ebc6410731035de7310731005dd73107313379e4310731004ff755833101cfe755833101cfc7558331004ff745833103cfc7458331004ff7258331014fe7258331014fc7258331036f63158331036f53158331036fb7058331036fb3058331036f83058331116fa105833103cf
  | 26 => 0x5bf7454c4103dbc7454c41036de6354c41006dd6354c4103dbd7690c41336bd7690c41004bd7690c4103dbe7390c4103f9e7390c4103ebf6390c4103f9e6390c41336bd6390c4103f9d6390c410069d6390c41135be7290c41135bc7290c41005bd7190c4103fb66190c41005bd7090c41004ff755884101cfe755884101cfc7558841004ff7358841034fc7358841006be435884103ebc4358841044ff7258841046ef7258841136ee525884103eef4258841136be425884103ebc425884103eec425884103ebf4158841046ee2158841046ec2158841004ff705884100cfe705884100cfc705884103ebf4058841136ef2058841004ff7654841004fd7654841044fc765484101e7e65548410067d6554841005bf745484103dbc7454841006de6354841006dd6354841016ee6254841006ed6254841005f77154841045f47154841034ff76cc841044fe76cc841004fd76cc84103dbe74cc841005bd74cc841036de63cc841006dd63cc841004ff764c841004fd764c841044fc764c841005bf744c84103dbc744c841036de634c841006dd634c841005f7714c841045f4714c841044ff759844101cfe759844116cfd7598441044fc759844133ebe439844103ebc4398441014fe7298441166be429844103ebc4298441046bf419844103ef74198441046f4419844100cfe709844116cff7654441006de6354441006dd6354441045bf7650441006bf7650441004bf7650441335bc73504410479e6350441006bd63504410479d63504410069d6350441007af7250441135be7250441135bc7250441007ac7250441135ac7250441006bd6250441045bf715044103fb77150441046be6150441047b66150441047b65150441007b551504413cfb72150441047b42150441005bf7050441004ff755804101cfe755804101cfc755804100cfd7458041004ff7358041034fc7358041004ff7258041014fe7258041014fc7258041046fb705804112efa505804103efb405804103ef8405804112efa2058041046fb1058041046f810580410367f7559731004ff745973103cfc74597311267f54597311267c5459731034fc73597310367e53597310367c5359731004ff7259731014fe7259731014fc72597311267f52597310067e52597311267c52597311267f5159731004ff705973100cfe705973100cfc70597311267f50597310067e50597311267c50597310067f74597310067e74597310067d74597310067c74597310367f73597310367e73597310367d73597310367c73597310367f43597310367e43597310367d43597310367c43597310067f72597310067e72597310067d72597310067c72597310067e42597310067c42597310367f32597310367e32597310367d32597310367c32597310067f71597310067d71597311267c715
  | 27 => 0xf75581411557c7558141005df7358141005dc7358141005ef725814114dec7258141006ef6258141006ec6258141146f86058141044ff75594410467f755944103cfe745944103cfc745944103e7e545944103e7c5459441004ff7359441034fc7359441004ff7259441014fe7259441014fc725944113e7f5259441044fc71594410467e51594410467c5159441004ff705944100cfe705944100cfc705944113e7f505944103ebf4059441036df7598c41036de7598c41036dd7598c41036dc7598c41036df7498c41036de7498c41036dd7498c41036dc7498c4103edf5498c4103ede5498c4103edd5498c4103edc5498c41036df7298c41036de7298c41036dd7298c41036dc7298c41006df5298c41006de5298c41006dc5298c4103edf4298c4103ede4298c4103edd4298c4103edc4298c41046de7198c41046dc7198c41006df5198c41046de5198c41046dc5198c4103edf4198c41046de4198c4103edd4198c41046dc4198c41006df2198c41046de2198c41046dc2198c41036df7098c41036de7098c41036dd7098c41036dc7098c41006df5098c41006de5098c41006dc5098c4103edf4098c4103ede4098c4103edd4098c4103edc4098c41006df2098c41006de2098c41006dc2098c41046df1098c41006de1098c41046dc1098c41004ff7558c4101cfe7558c4101cfc7558c41046df7358c41006df5358c41006dc5358c4103edf4358c4103ebc4358c4103edc4358c4103e9c4358c41004ff7258c41014fe7258c41014fc7258c41006be4258c4103ebc4258c41006de3258c41006dc3258c4103ebf4158c41046de3158c41046dc3158c41004ff7058c4100cfe7058c4100cfc7058c4103ebf4058c41006de3058c41006dc3058c41006df7558c41006de7558c41006dd7558c41006dc7558c4103edf7458c4103ede7458c4103edc7458c4103edf5458c4103ede5458c4103edd5458c4103edc5458c41006df7258c41006de7258c41006dd7258c41006dc7258c41006df5258c41006de5258c41006dc5258c4103edf4258c4103ede4258c410069e4258c4103edd4258c4103edc4258c4103e9c4258c41046de7158c41046dc7158c41006df5158c41046de5158c41046dc5158c4103edf4158c4103e9f4158c41046de4158c4103edd4158c41046dc4158c41006df2158c41046de2158c41046dc2158c41006df7058c41006de7058c41006dd7058c41006dc7058c41006df5058c41006de5058c41006dc5058c4103edf4058c4103e9f4058c4103ede4058c4103edd4058c4103edc4058c41006df2058c41006de2058c41006dc2058c41046df1058c41006de1058c41046dc1058c41034ff7694c41044fe7694c41004fd7694c41036de6394c41006dd6394c4113f5f5394c41004ff7654c41004fd7654c41044fc7654c41
  | 28 => 0x89412cfe441d8941006ee60d8941006ec60d8941006ef75d8941006ee75d8941006ed75d8941006ec75d8941006ef74d894114eee74d8941006ef54d89412ceee54d8941006ed54d89412ceec54d8941006ef73d8941006ee73d8941006ed73d8941006ec73d8941006ef53d8941006ee53d8941006ed53d8941006ec53d89412ceef43d8941006ee43d8941006ed43d89412ceec43d89412ceef71d894114eee71d8941006ed71d8941006ef51d8941006ec51d89412ceef41d89412ceec41d8941006ef70d8941006ee70d8941006ed70d8941006ec70d8941006ef50d8941006ee50d8941006ec50d89412ceef40d8941006ee40d89412ceec40d8941006ee30d8941006ec30d8941006ee10d8941006ec10d894114eec6258941005ee761894114eee7618941006ef6518941006ee6518941006ed6518941006ec651894114fad7418941006ef6318941006ee6318941006ed6318941006ec6318941007af4318941007ad431894117eef61189413d7e741189413d7e44118941006ee6018941006ec6018941004ff7654941004fe7654941004fc7654941006ef6254941016ec6254941005be76d094103ebe76d0941164be76d0941005bd73d094134ebc63d094114dbd72d0941007af62d0941016be62d0941016bc62d094114fac62d0941016ac62d0941045be71d094103ebf61d094103fb761d094114fac21d0941014fc7650941006ef6250941016ec6250941005f77150941005f4715094114dbc7650941016bc7650941014bc7650941005bf7350941346bc635094103dbf725094103faf7250941007af6250941016be6250941016bc625094114fac6250941016ac6250941007b77150941045bc7150941007b47150941005b4715094103ebf615094103fb7615094114faf2050941004fe76cc941004fd76cc941034fc76cc94103dbe74cc941005bd74cc941006ef62cc941016ec62cc941004ff764c941004fe764c941004fc764c94103dbe744c941005bd744c941006ef624c941016ec624c941184fe7694541006ef62945411a6ec629454115777519454101cff7654541154fd765454103cfc76545410067f655454101e7c6554541005bf745454103dbc7454541006ef6254541196ec6254541006ef6290541166ec629054103df67190541005bd739054133ebc6390541005bd7290541007af6290541166be6290541166bc6290541007ac6290541166ac6290541045be719054103fb7619054100cfe76d8141006ef62d8141006ec62d8141146fa60d814101cfe75d8141004fd75d814101cfc75d814100cfc74d8141034fe73d8141004fd73d8141006bf43d8141006bd43d8141014fe72d8141004fd72d8141014fc72d8141006bf42d8141006bd42d814103cfd71d8141006be41d8141146fa40d8141146fa10d81410057
  | 29 => 0x34fc7358241004ff7258241014fe7258241014fc7258241044fc715824115efa405824115efa2058241046fb1058241046f8105824101cfe76d95411567e65d9541154fd74d95411567f54d9541034fe73d9541004fd73d95411567f53d9541014fe72d9541004fd72d9541014fc72d954103cfd71d95411567f51d954100cfe70d9541004fd70d954100cfc70d95410067e50d95411567c50d95411567c6559541005ef725954114dec7259541154ff75595410067f755954116cff7459541006bf7459541004ff7359541034fc7359541004ff7259541006ef7259541004ef7259541014fe7259541014fc7259541006ec7259541014ec7259541184ff7159541006f77159541004ff705954100cfe705954100cfc705954101cfc76551410067f655514101e7c655514103f3c545514127eec6255141005f77155141005f4715514103fb4415514101cfe75d8d41004fd75d8d4101cfc75d8d41014fe72d8d41004fd72d8d41014fc72d8d4100cfe70d8d41004fd70d8d4100cfc70d8d41006de30d8d41006dc30d8d411557e7598d410057d7598d41006df6398d4114dee7298d41005ed7298d41005ef7258d4114dec7258d41036de6318d41006dd6318d41004fe7694d41004fd7694d41034fc7694d4103dbe7494d41005bd7494d41006df6394d41036dc6394d411575f5394d4126eec6294d41005f67194d41005f57194d41004ff7654d41004fe7654d41004fc7654d410067f6554d4101e7c6554d41006df6354d41036dc6354d4125eec6254d41005be76d0d4103ebe76d0d41004be76d0d41036be63d0d41036bc63d0d41005bd72d0d41246be62d0d41246bc62d0d41246ac62d0d41045be71d0d4103ebf61d0d4103fb761d0d41005bd7490d41006df6390d41036dc6390d4122eec6290d41005f67190d41005f57190d41034fc7650d41006df6350d41036dc6350d4103f9c4350d41216ec6250d41005f77150d41005f47150d4103fb44150d41034bc7650d4103dbf7350d4103f9f7350d410079f6350d41036be6350d41036bc6350d410079c6350d41005bf7250d41216be6250d41216bc6250d41216ac6250d41007b77150d41045bc7150d41007b47150d4103ebf6150d4103fb76150d41014fe76d894114eee62d894101cfe75d8941004fd75d894101cfc75d8941034fe73d8941004fd73d8941006ef52d894114eee52d894114eec52d894114eee42d894114eee32d894114eec32d894103cfd71d894114eef21d894100cfe70d8941004fd70d894100cfc70d894114eef20d8941006ee20d894114eec20d894114dee76d8941014ee76d8941006ef65d8941006ee65d8941006ed65d8941006ec65d8941007af74d8941006ef63d8941006ee63d8941006ed63d8941006ec63d8941007af43d8941007ad43d89412cfe741d
  | 30 => 0xe65547410067d6554741005bf745474103dbc7454741004ff755834101cfe755834101cfc7558341004ff7358341034fc735834103ebf4358341006bd4358341004ff7258341014fe7258341014fc725834103ebf4258341006bd425834103ebc415834103efb705834103efb405834103ef84058341176fa1058341046bd74d9641034fe73d9641004fd73d9641014fe72d9641004fd72d9641044fc72d9641046f671d964100cfe70d9641004fd70d964100cfc70d96410467c65596410467f755964116e7f5459641004ff7359641034fc7359641004ff7259641014fe7259641014fc725964116e7f5259641044fc71596410467e51596410467c5159641004ff705964100cfe705964100cfc705964103ef7415924101cff765524101e7e65552410067d6555241005f77155241045f4715524103fb74155241046df6398e41046dc6398e41046dc6358e41004ff7558e4101cfe7558e4101cfc7558e41004ff7258e41014fe7258e41014fc7258e41006be4258e41006bc4258e41044fc7158e41046de3158e41046dc3158e41004ff7058e4100cfe7058e4100cfc7058e41034ff7694e41044fe7694e41004fd7694e4116f5f5394e41045f67194e41005f57194e41004ff7654e41004fd7654e41044fc7654e41005bf7454e4103dbc7454e41036de6390e41006dd6390e41045f67190e41005f57190e4133f9e6390e4133ebd6390e410079d6390e41165be7290e41165bc7290e4133fb67190e41005bd7190e4133fb57190e4103ebe6190e41005bd7090e41034ff7650e41036de6350e41006dd6350e41005f77150e41045f47150e41005bd7610e4103ebd7610e4103f9e7310e4133ebd6310e41165be7210e4103dbc7210e41005bd7110e4103fb66110e41005bd7010e41046ec6258a41167ae4258a41004ff7558a4101cfe7558a4101cfc7558a41004ff7358a41034fc7358a41006be4358a41006bc4358a41166be4258a41166ee4258a41166bc4258a41044fc7158a41046ee2158a41046ec2158a41004ff7058a4100cfe7058a4100cfc7058a41004ff7654a41004fd7654a41044fc7654a4101e7e6554a410067d6554a41005bf7454a4103dbc7454a41014ff7650a41016ee6250a41006ed6250a4103fac4250a41005f77150a41045f47150a41034ff76cca41044fe76cca41004fd76cca4103dbe74cca41005bd74cca41036de63cca41006dd63cca41004ff764ca41004fd764ca41044fc764ca41005bf744ca4103dbc744ca41036de634ca41006dd634ca4113cff7654641045bd76d064103ebd76d064133dbe73d0641006bd63d0641165be72d064103dbc72d0641006bd62d0641047b661d0641047b651d0641007b551d0641005bd70d0641046f86058241004ff755824101cfe755824101cfc7558241004ff7358241
  | 31 => 0x8951004fd73d8951196ee52d89510c6ed52d8951196ec42d8951196ec32d895101cfd71d8951196ef21d895100cfe70d8951004fd70d895100cfc70d8951196ef20d8951005bf7458951005bc7458951196ec62589513ddf771589511957c76549510167c76549510147c76549510067f635495101d7f725495101f6f72549510076f62549510167e62549510167c62549511976c62549510077771549510457c715495100774715495101e7f615495101f7761549511ee7e60549511ee7c60549511976f2054951004fe76d0951004fd76d095103cfc76d0951006ef62d0951016ec62d0951004ff7650951004fe7650951004fc7650951004fe76cc951004fd76cc951034fc76cc951005be74cc951005bd74cc951006ef62cc951016ec62cc951004ff764c951004fe764c951004fc764c9510067f63945510057d72945510457e71945510477671945510467f619455101f77619455119e7e609455119e7c609455100cfe76d815118efa60d815100cfc75d815103cfe74d8151004fd74d8151034fe73d8151004fd73d8151014fe72d8151004fd72d8151014fc72d815101cfd71d815118efa50d815118ef830d815118efa10d815118ef8605815103e7f755974103cfc745974103e7e545974103e7c5459741004ff7359741034fc73597411867f5359741004ff7259741014fe7259741014fc72597411867f5159741004ff705974100cfe705974100cfc70597410067e50597411867c5059741004ff7558f4101cfe7558f4101cfc7558f4103edf7358f4103edf4358f4103edc4358f41004ff7258f41014fe7258f41014fc7258f41004ff7058f4100cfe7058f4100cfc7058f41034ff7694f4103cfe7694f41004fd7694f4103dbe7494f41005bd7494f411875f5394f41004ff7654f41004fd7654f4103cfc7654f4101e7e6554f410067d6554f4103dbf7650f41006bf7650f4103f9f7350f4103f9f6350f41036be6350f41036bc6350f4103f9c6350f41005bf7250f41216be6250f4103ebc6250f41045bc7150f41004ff7558b4101cfe7558b4101cfc7558b41004ff7358b41034fc7358b4103eef7258b4103eef4258b4103eec4258b4117eec3258b4117eef2158b41004ff7058b4100cfe7058b4100cfc7058b4117eef2058b41004ff7654b41004fd7654b4103cfc7654b41005f77154b41005f47154b4103dbf7650b41136bf7650b41134bf7650b41005bf7350b41346be6350b4103faf7250b41016be6250b41016bc6250b41045bc7150b4117faf2050b41034ff76ccb4103cfe76ccb41004fd76ccb4103dbe74ccb41005bd74ccb41016ee62ccb41006ed62ccb41004ff764cb41004fd764cb4103cfc764cb4103dbe744cb41005bd744cb41005f7714cb41005f4714cb41154fd769474101cff765474103cfc765474101e7
  | 32 => 0x4ff7058e5100cfe7058e5100cfc7058e51006de3058e51006dc3058e510347f7654e5101d7f7354e5101f5f7354e510367e6354e510075e6354e510365e6354e510075d6354e510367c6354e510057f7154e51007777154e51007747154e5101e7e6154e5101f766154e5119d7e7054e5119d7c7054e5103cff76d0e51044fe76d0e51004fd76d0e5103ebe64d0e51006bd64d0e51034ff7690e51044fe7690e51004fd7690e5101d7e7590e510057d7590e51036de6390e51006dd6390e51004ff7650e51004fd7650e51044fc7650e5103ebe6450e51006bd6450e51036de6350e51006dd6350e51034ff7610e51044fe7610e51004fd7610e5101d7e7510e510057d7510e51014ff7658a51046ec6258a51004ff7458a5103cfc7458a51004ff7358a51034fc7358a510b67f5358a510067d5358a511a6ee5258a510b6ed5258a51044fe7158a51044fc7158a510b67f5158a51046ee2158a51046ec2158a51004ff7058a5100cfe7058a5100cfc7058a510067e5058a510b67c5058a5103cff76d0a51044fe76d0a51004fd76d0a5103ebe64d0a51006bd64d0a51004ff7650a51004fd7650a51044fc7650a5103ebe6450a51006bd6450a51034ff76cca51044fe76cca51004fd76cca5101d7e75cca510057d75cca51005be74cca51005bd74cca51036de63cca51006dd63cca51004ff764ca51004fd764ca51044fc764ca51036de634ca51006dd634ca5100cff765825101d7c7558251046f8605825119f7a5058251004ff745825103cfc7458251004ff7358251034fc735825102e7f53582510067d5358251004ff7258251014fe7258251014fc7258251044fc715825119e7e505825119efa505825119e7c505825119efa2058251046fb1058251046f8105825116ebe54d915116ebd54d9151034fe73d9151004fd73d9151014fe72d9151004fd72d9151014fc72d9151006be42d9151006bc42d915100cfe70d9151004fd70d915100cfc70d9151006bf6499151155f57199151005ef7259151195ec7259151185f7715915103ebe6419151006bd641915103cfe74d8d51004fd74d8d5110ede53d8d5110edd53d8d51014fe72d8d51004fd72d8d51014fc72d8d5110e7f52d8d5110e7c51d8d5100cfe70d8d51004fd70d8d5100cfc70d8d51006df6398d510f5f57198d51005bf7458d51005bc7458d51005ef7258d51195ec7258d51125f77158d51005fb7058d5118df87058d51036de6318d51006dd6318d51004fe76d0d51004fd76d0d5103cfc76d0d51004fe7690d51004fd7690d51034fc7690d51006bf6490d5103ebc6490d51004ff7650d51004fe7650d51004fc7650d51004fe7610d51004fd7610d51034fc7610d51006bf6410d5103ebc6410d51014fe76d8951196ee62d895103cfe74d8951004fd74d8951034fe73d
  | 33 => 0xf735953226cff75595320067f7559532004ff745953203cfc74595323e4ff7359532006df735953225cff7259532006ef7259532004ff7159532044fc7159532004ff705953200cfe705953200cfc705953225eef205953203cfe76d913201cfe75d9132004fd75d913201cfc75d9132034ff72d9132034fd72d913222ebf42d913222ebd42d9132044fe71d9132004fd71d913200cfe70d9132004fd70d913200cfc70d913222eef20d9132006bf6499132215dd7399132245df7359132005f77159132005f47159132004ff755913201cfe755913201cfc7559132006bf7459132244ff7359132006df7359132346be4359132346bc4359132214ff7259132006ef7259132216be4259132216bc4259132004ff7159132006f77159132004f77159132044fc7159132006f47159132004f47159132004ff705913200cfe705913200cfc7059132216ef205913222cfe761913203ebe6419132006bd641913203cff7695132004fe7695132004fd769513203cfc76951321b73f5495132004ff7655132004fe7655132004fd7655132004fc765513201cff7654d32014fe7654d3225cfd7654d32014fc7654d320067f6554d3201e7c6554d32005ef7254d32015ec7254d32037cc3254d32014fe76d0d32014fc76d0d32006bf64d0d3203ebc64d0d32015ee72d0d32005ed72d0d3203cff7650d32014fe7650d32214fd7650d32014fc7650d32006bf6450d3203ebc6450d32005ef7250d32015ec7250d3201cfe75d8532004fd75d853201cfc75d853203cfe74d8532004fd74d8532034fd72d853211ef621d853200cfe70d8532004fd70d853200cfc70d8532006f76198532005bf7458532005bc7458532005be7418532005bd7418532006f5611853201cfe7518532004fd7518532044fc751853203cfe7418532046be741853203cbe7418532004fd7418532046bd7418532004bd7418532046dd7318532034fd72185323b6ef32185320d6ec3218532046f621185320d6f5211853200cfe7018532004fd701853200cfc70185320d6ef201853200cfe76d81321aefa60d813201cfe75d8132004fd75d813201cfc75d813203cfe74d8132004fd74d8132014fd73d8132034fd72d8132044fe71d8132004fd71d81321aefa30d81321aefa20d81321aef86058132046bf6499251046bc6499251046bc6459251156be5459251156bd5459251004ff7359251034fc7359251004ff7259251014fe7259251014fc7259251044fc7159251046be4159251046bc4159251004ff705925100cfe705925100cfc7059251006be4059251006bc4059251046df6398e51046dc6398e51046dc6358e51004ff7458e5103cfc7458e510f6de5358e510f6dd5358e51004ff7258e51014fe7258e51014fc7258e51044fc7158e51046de3158e51046dc3158e51
  | 34 => 0x9332006be5099332006bc5099332036bf3099332036be3099332036bd3099332036bc3099332246bf2099332246be2099332246bd2099332246bc2099332006be1099332006bc1099332004ff755933201cfe755933201cfc7559332036bf7459332006bf5459332006bc5459332014fe7359332014fc7359332036be4359332036bc4359332216bf4259332216bd4259332004ff7159332044fc7159332036df3159332004ff705933200cfe705933200cfc7059332006be4059332006bc4059332006bf7559332006be7559332006bd7559332006bc7559332036bf7359332036be7359332036bd7359332036bc7359332036bf5359332036be5359332036bd5359332036bc5359332216bf7259332216be7259332216bd7259332216bc7259332216bf5259332216be5259332216bd5259332216bc5259332036bf3259332036be3259332036bd3259332036bc3259332006bf7159332006be7159332006bd7159332006bc7159332006bf5159332006bc5159332036bf31593320369f3159332036be3159332036bd3159332036bc3159332216bf2159332216be2159332216bd2159332216bc2159332006bf7059332006be7059332006bd7059332006bc7059332006bf5059332006be5059332006bc5059332036bf3059332036be3059332036bd3059332036bc3059332216bf2059332216be2059332216bd2059332216bc2059332006be1059332006bc105933203cff7695332034fe7695332004fd7695332034fc769533203ebe6495332006bd64953321c73f5495332004ff7655332034fe7655332004fd7655332034fc765533203ebe6455332006bd645533201cfe7598732004fd7598732044fc759873203cfe7498732004fd7498732014fe7398732046de7398732014de7398732044fc7398732046f67198732006f75198732046f45198732046df3198732036f73198732046f43198732046f62198732106f5219873200cfe7098732004fd709873200cfc7098732004ff755873201cfe755873201cfc7558732004ff745873203cfc7458732014fc7358732036f77158732006f75158732006f45158732036f73158732036f431587320eef621587320eeec2158732004ff705873200cfe705873200cfc7058732004ff755833201cfe755833201cfc7558332004ff745833203cfc7458332014fe7358332014fc7358332036ee3258332036ed3258332004ff7158332044fc7158332066ec2158332036fb7058332036fb3058332036f830583321befa205833201cfe76d95321b67e65d953203cfe74d9532004fd74d9532014fd73d95321b67f53d9532034ff72d9532034fd72d953226e7f52d953226e7d52d9532044fe71d9532004fd71d953200cfe70d9532004fd70d953200cfc70d953226eef20d95321b67c65595323e5d
  | 35 => 0xcfc70d8d42246ef20d8d42006df6398d42005f77158d42005f47158d42036de6318d42006dd6318d42004fe7694d42004fd7694d42034fc7694d421d75f5394d42004ff7654d42004fe7654d42004fc7654d42005bf7454d4203dbc7454d42014fe7690d42006df6390d42036dc6390d42015ee7290d42005ed7290d42015be7690d4222ebe7690d42014be7690d4203dbe7390d42346bf6390d420079f6390d423479c6390d42015be7290d4222fae7290d42347ad7290d42015bc7290d4203ebf6290d4203faf6290d42005bd7190d42005bd7090d4222faf2090d42014fc7650d42216bf6450d42006df6350d42036dc6350d42005ef7250d42015ec7250d42245be7610d4203ebe7610d42244be7610d4222dbe7310d4203f9e7310d42346bf6310d42015be7210d42015bc7210d4203ebf6210d4203faf6210d42005bd7110d42005bd7010d421ffaf2010d4201cfe75d8542004fd75d854201cfc75d8542034fe73d8542004fd73d854203cfd72d8542006f751d8542006f451d854217ef621d854200cfe70d8542004fd70d854200cfc70d8542006f76198542005de7318542005dd7318542006f5611854201cfe7518542004fd7518542044fc7518542046bd7418542034fe7318542046de7318542034de7318542004fd7318542046dd7318542004dd7318542006be4318542006bc431854203cfd72185423d6ef4218542136be4218542136bc4218542136ec4218542006f75118542046f45118542046f62118542136f5211854200cfe7018542004fd701854200cfc7018542136ef201854200cfe76d81421cefa60d814201cfe75d8142004fd75d814201cfc75d8142014fd74d8142034fe73d8142004fd73d814203cfd72d8142044fe71d8142004fd71d81421cefa40d81421cefa20d81421cef860581420367f7559732004ff745973203cfc7459732014fe7359732014fc73597320367e53597320367c535973225e7f525973225e7d5259732004ff7159732044fc71597321c67c5159732004ff705973200cfe705973200cfc70597321c67f505973203ebf759933203ebe759933203ebd759933203ebc7599332036bf7399332036be7399332036bd7399332036bc7399332036bf5399332036be5399332036bd5399332036bc539933203ebf729933203ebe729933203ebd729933203ebc7299332246bf5299332246be5299332246bd5299332246bc5299332036bf3299332036be3299332036bd3299332036bc329933203ebf719933203ebe719933203ebd719933203ebc7199332006bf5199332006bc5199332036bf3199332036be3199332036bd3199332036bc3199332246bf2199332246be2199332246bd2199332246bc2199332246ac219933203ebf709933203ebe709933203ebd709933203ebc7099332006bf509
  | 36 => 0xe545974203e7c5459742004ff7359742034fc735974227e7f525974227e7d5259742004ff7159742044fc7159742004ff705974200cfe705974200cfc705974203ebf4059742004ff7558f4201cfe7558f4201cfc7558f42014fc7458f4203ebc7458f42014bc7458f4203edf7358f4203edf4358f4203ebc4358f4203edc4358f42216be4258f4203ebc4258f42216df3258f42004ff7158f42044fc7158f4203ebf4158f42004ff7058f4200cfe7058f4200cfc7058f4203ebf4058f42006de3058f42006dc3058f42034ff7694f4203cfe7694f42004fd7694f42036de6394f42006dd6394f421e75f5394f42004ff7654f42004fd7654f4203cfc7654f42005bf7454f4203dbc7454f42036de6354f42006dd6354f4203dbd7690f4234ebd7690f42214bd7690f4203f9e7390f4203ebf6390f4234ebd6390f42015be7290f42015bc7290f42005bd7190f4222fac2190f42005bd7090f4201cfe7598742004fd7598742044fc7598742014fe7498742046be7498742014be7498742044fc7498742034fe7398742004fd7398742006be439874203ebc4398742166be429874203ebc4298742046f67198742046bf419874203ef74198742046f44198742046f62198742166f5219874200cfe7098742004fd709874200cfc709874203ebf4098742004ff755874201cfe755874201cfc7558742014fc7458742004ff7358742034fc735874203ef7715874203ef7415874203ef4415874214ef6215874214eec2158742004ff705874200cfe705874200cfc7058742004ff755834201cfe755834201cfc7558342014fe7458342014fc7458342004ff7358342034fc735834203eee425834203eed4258342004ff7158342044fc7158342086ec215834203efb705834203efb405834203ef840583421defa205834201cfe76d95421d67e65d9542014fd74d95421d67f54d9542034fe73d9542004fd73d954203cff72d954203cfd72d954228e7f52d954228e7d52d9542044fe71d9542004fd71d954200cfe70d9542004fd70d954200cfc70d954228eef20d95421d67c65595423edbf7459542005f77159542005f4715954228cff75595420067f75595423ecff7459542006bf7459542004ff7359542034fc735954227cff7259542006ef7259542004ff7159542006f77159542004f77159542044fc7159542006f47159542004f47159542004ff705954200cfe705954200cfc705954227eef205954201cff7655142014fe765514227cfd7655142014fc76551420067f655514201e7c6555142005ef7255142015ec725514203fac4255142034fe76d8d4201cfe75d8d42004fd75d8d4201cfc75d8d42246bd74d8d4203cfd72d8d42246be42d8d42246bc42d8d42246df32d8d42044fe71d8d42004fd71d8d4200cfe70d8d42004fd70d8d42
  | 37 => 0x804303ebc4158043034ff7058043036fb705804303efb405804303ef84058043036fb3058043036f830580431f6fa205804303cfe76d9152014fd75d9152406be54d9152406bd54d9152034fe73d9152004fd73d915201cfd72d91523eebf42d9152044fe71d9152004fd71d915200cfe70d9152004fd70d915200cfc70d9152006be40d9152006bc40d91523eeef20d9152006bf64991521d5ed72991521e5ef7259152005f77159152005f4715915203ebe6419152006bd6419152034fe76d8d52014fd75d8d5203cfe74d8d52004fd74d8d523fede53d8d523fedd53d8d5201cfd72d8d523e6df32d8d52044fe71d8d52004fd71d8d5200cfe70d8d52004fd70d8d5200cfc70d8d52006de30d8d52006dc30d8d523e6ef20d8d52005be7498d52005bd7498d52006df6398d521b5ed7298d52005f67198d52005f57198d521c5ef7258d52036de6318d52006dd6318d520157c7654d520367c7654d520147c7654d5201d7f7354d5201f5f7354d520075f6354d520367e6354d520367c6354d520075c6354d520365c6354d520076f7254d520157e7254d520157c7254d5225f6c7254d5201e7f6254d5201f6f6254d520057f7154d521ed7e7054d521ed7c7054d5225f6f2054d52004fe76d0d52004fd76d0d5203cfc76d0d52006bf64d0d5203ebc64d0d52015ee72d0d52005ed72d0d52004fe7690d52004fd7690d52034fc7690d5201d7e7590d520057d7590d52015ee7290d52005ed7290d52004ff7650d52004fe7650d52004fc7650d52006bf6450d5203ebc6450d52004fe7610d52004fd7610d52034fc7610d5201d7e7510d520057d7510d52014fd75d855203cfe74d8552004fd74d8552034fe73d8552004fd73d855201cfd72d85523def651d85523aef621d855200cfe70d8552004fd70d855200cfc70d8552006f610d8552006f410d8552006f76198552005bf7458552005bc7458552006f56118552014fd75185520467d751855203cfe7418552004fd7418552034fe7318552004fd73185523f67f53185520067d531855201cfd72185520467f5118552046f651185523f6f55118552046f621185523a6f5211855200cfe7018552004fd701855200cfc70185520067e50185523f67c50185523a6ef2018552006f61018552046f4101855200cfe76d815201d7e75d81520157d75d81521eefa60d81521ef7a50d8152014fd75d81521ee7d75d81520147d75d815203cfe74d8152004fd74d8152034fe73d8152004fd73d81523867f53d81520067d53d815201cfd72d8152044fe71d8152004fd71d81521ee7e50d81521eefa50d81521ee7c50d81521eefa20d8152005bf7458152005bc7458152005df7358152005dc7358152005f77158152005f471581521eef8605815203e7f7559742014fe7459742014fc745974203e7
  | 38 => 0x3cfc7654d430067f6554d4301e7c6554d43005bf7454d4303dbc7454d430379c4354d43014fe76d894303dbe74d8943216ee62d8943217ae42d894301cfe75d8943004fd75d894301cfc75d8943034fd74d8943034bd74d894303cfd73d894334ebe43d894334ebc43d8943216be42d8943216ee42d8943216bc42d8943216ee32d8943044fe71d8943004fd71d8943216ec21d894300cfe70d8943004fd70d894300cfc70d8943216ec6258943005f77158943005f4715894301cfe75d8543004fd75d854301cfc75d8543014fe72d8543004fd72d8543014fc72d8543006f721d8543006f421d854300cfe70d8543004fd70d854300cfc70d8543006f76198543005ef7258543215ec7258543006f5611854301cfe7518543004fd7518543044fc7518543336be4318543336bc4318543014fe7218543004fd7218543044fc7218543006be4218543006bc4218543006f72118543046f4211854300cfe7018543004fd701854300cfc701854300cfe76d814320efa60d814301cfe75d8143004fd75d814301cfc75d8143034fd74d814303cfd73d8143014fe72d8143004fd72d8143014fc72d8143044fe71d8143004fd71d8143006fb50d814320ef850d814320efa40d814320efa30d81430057f755814321d7c755814320ef86058143034ff75594430367f755944303cfe745944303cfc745944303e7e545944303e7c5459443034fe7359443034fc73594430367e53594430367c5359443004ff7259443014fe7259443014fc72594432067f5259443004ff7159443044fc71594432067c5159443004ff705944300cfe705944300cfc70594432067f5059443004ff755884301cfe755884301cfc7558843034ff7258843036ef725884303eef425884303eec4258843036ef3258843036ec3258843004ff7158843044fc7158843004ff705884300cfe705884300cfc70588431feef205884301cfe7598443004fd7598443044fc7598443014fe7298443004fd7298443044fc7298443044fe7198443046f67198443006f75198443046f4519844303ef74198443046f44198443036f73198443046f4319844300cfe7098443004fd709844300cfc7098443004ff755844301cfe755844301cfc7558443036bf4358443036de4358443036bd435844303edd4358443004ff7258443006ef7258443004ef7258443014fe7258443014fc7258443006ec7258443014ec725844303ebf4258443036f77158443006f75158443006f4515844303ef7415844303ebc415844303ef4415844303eb44158443036f73158443036f43158443004ff705844300cfe705844300cfc7058443004ff755804301cfe755804301cfc7558043036bf4358043036bd4358043004ff7258043014fe7258043014fc725804303ebf4258043004ff7158043044fc715
  | 39 => 0xc4298743046f67198743046bf419874303ef74198743046f4419874300cfe7098743004fd709874300cfc709874303ebf4098743004ff755874301cfe755874301cfc7558743034fc745874303ede435874303edd4358743004ff7258743014fe7258743014fc725874303ef7715874303ef7415874303ef44158743004ff705874300cfe705874300cfc7058743004ff755834301cfe755834301cfc7558343034fc7458343004ff7258343014fe7258343014fc7258343004ff7158343044fc715834303efb705834303efb405834303ef8405834323efa30583430367f75596432367f5459643034fc73596430367e53596430367c5359643004ff7259643014fe7259643014fc72596432367f5259643004ff7159643044fc71596432367c5159643004ff705964300cfe705964300cfc70596432367f505964303edf4359243036be4359243036bc4359243036dc435924301cff7655243034fc765524301e7e65552430067d6555243005df7355243035dc735524303f9f4355243004ff7558a4301cfe7558a4301cfc7558a43034fc7358a43036ef7258a4322eee5258a4322eee4258a43036ef3258a43036ec3258a43004ff7158a43044fc7158a43036df3158a4322eec2158a43004ff7058a4300cfe7058a4300cfc7058a4322eef2058a4301cfe7598643004fd7598643044fc7598643034fe7398643034de7398643014fe7298643004fd7298643044fc7298643046f67198643046df3198643036f73198643046f4319864300cfe7098643004fd709864300cfc7098643004ff755864301cfe755864301cfc7558643034fc7358643036bf4358643036bd4358643004ff7258643014fe7258643014fc7258643036f77158643036f73158643036f43158643004ff705864300cfe705864300cfc7058643004ff755824301cfe755824301cfc7558243034fc7358243036bf4358243036bd4358243004ff7258243014fe7258243014fc7258243004ff7158243044fc7158243036fb7058243226fa4058243036fb3058243036f8305824301cfe76d954321e7e65d9543034fd74d954321e7f54d954303cfd73d954321e7f53d9543014fe72d9543004fd72d9543014fc72d9543044fe71d9543004fd71d954300cfe70d9543004fd70d954300cfc70d95430067e50d954321e7c50d954321e7c6559543005fb705954320df8705954321cff75595430067f7559543234ff7459543006bf745954324cff7359543006df7359543004ff7259543014fe7259543014fc7259543004ff7159543044fc7159543004ff7059543006fb7059543004fb705954300cfe705954300cfc7059543006f8705954300cf87059543034fc76551430067f655514301e7c6555143005df7355143035dc735514303f9c435514301cff7654d4321cfd7654d43
  | 40 => 0x865303cfc7458653034fc7358653004ff7258653014fe7258653014fc7258653036f771586530f6f65158653036f73158653036f43158653006f72158653006f42158653004ff705865300cfe705865300cfc7058653004ff745825303cfc7458253034fe7358253034fc73582530367f53582530367d5358253004ff7258253014fe7258253014fc7258253004ff7158253044fc7158253036fb7058253266fa5058253036fb3058253036f83058253034fd75d9153236be54d9153236bd54d9153014fe72d9153004fd72d9153014fc72d9153044fe71d9153004fd71d915300cfe70d9153004fd70d915300cfc70d9153006be40d9153006bc40d9153006bf649915321ddd739915324ddf7359153005fb7059153255f8705915303ebe6419153006bd6419153014fe76d895325eee62d8953034fd75d895303cfe74d8953004fd74d895301cfd73d895325eee52d895325eee32d8953044fe71d8953004fd71d895325eec21d895300cfe70d8953004fd70d895300cfc70d895325eec6258953034fd75d855303cfe74d8553004fd74d8553014fe72d8553004fd72d8553014fc72d85531267f52d8553126f651d85531267c51d855300cfe70d8553004fd70d855300cfc70d8553006f76198553005bf7458553005bc7458553005ef725855325dec7258553005fb7058553255f87058553006f56118553034fd751855303cfe7418553004fd7418553014fe7218553004fd7218553044fc7218553046f651185530def5511855300cfe7018553004fd701855300cfc701855300cfe76d8153256fa60d8153034fd75d815303cfe74d8153004fd74d815301cfd73d8153014fe72d8153004fd72d8153014fc72d8153044fe71d8153004fd71d8153256fa50d8153256f840d8153256fa30d8153256fa20d8153256f810d8153005bf7458153005bc7458153256f8605815303e7f7559743034fc745974303e7e545974303e7c545974324e7f5359743004ff7259743014fe7259743014fc7259743004ff7159743044fc7159743004ff705974300cfe705974300cfc705974303ebf405974301cff7654f4303cfc7654f4301e7e6554f430067d6554f43005bf7454f4303dbc7454f430375c5354f430379e4354f43004ff7558b4301cfe7558b4301cfc7558b43034fc7458b43034bc7458b43346be4358b4303ebc4358b4303eef7258b43246ee5258b4303eef4258b43246be4258b4303ebc4258b4303eec4258b43246ee3258b43004ff7158b43044fc7158b4303ebf4158b43246ec2158b43004ff7058b4300cfe7058b4300cfc7058b4303ebf4058b43246ef2058b4301cfe7598743004fd7598743044fc7598743034fe7498743034be749874333ebe439874303ebc4398743014fe7298743004fd7298743044fc7298743006be429874303eb
  | 41 => 0x14fe7298654004fd7298654044fc7298654046f67198654046f6519865416ef5519865403ef74198654046f4419865400cfe7098654004fd709865400cfc709865403ebf409865403cfc7458654004ff7358654034fc7358654004ff7258654014fe7258654014fc725865403ef77158654156f6515865403ef7415865403ef44158654004ff705865400cfe705865400cfc705865403cfe745825403cfc7458254004ff7358254034fc7358254004ff7258254014fe7258254014fc7258254004ff7158254044fc715825403efb7058254286fa505825403efb405825403ef84058254286fa205825403cfd75d8d5424ede53d8d54014fe72d8d54004fd72d8d54014fc72d8d54044fe71d8d54004fd71d8d5400cfe70d8d54004fd70d8d5400cfc70d8d54006de30d8d54006dc30d8d54006df6398d54005fb7058d54275f87058d54036de6318d54006dd6318d54014fe76d895427eee62d895403cfd75d895401cfd74d8954034fe73d8954004fd73d895427eee52d895427eee42d8954044fe71d8954004fd71d895427eec21d895400cfe70d8954004fd70d895400cfc70d895427eec6258954005f77158954005f4715895403cfd75d8554034fe73d8554004fd73d8554014fe72d8554004fd72d8554014fc72d8554186f651d8554006f721d8554006f421d855400cfe70d8554004fd70d855400cfc70d8554006f76198554005ef725855427dec7258554006f5611855403cfd7518554034fe7318554004fd7318554014fe7218554004fd7218554044fc7218554046f6511855413ef55118554006f72118554046f4211855400cfe7018554004fd701855400cfc701855400cfe76d8154276fa60d815403cfd75d815401cfd74d8154034fe73d8154004fd73d8154014fe72d8154004fd72d8154014fc72d8154044fe71d8154004fd71d8154276fa50d8154276fa40d8154276f830d8154005df7358154005dc7358154276f86058154036bf745925321ebe545925321ebd5459253034fc7359253036be4359253036bc4359253004ff7259253014fe7259253014fc7259253006be4259253006bc4259253004ff7159253044fc7159253004ff705925300cfe705925300cfc7059253004ff7458a5303cfc7458a53034fe7358a53034fc7358a530367f5358a530367d5358a53036ef7258a5326eee5258a53036ef3258a53036ec3258a53004ff7158a53044fc7158a53004ff7058a5300cfe7058a5300cfc7058a5326eef2058a5303cfe7498653004fd7498653034fe7398653044fc73986530367f53986530367d5398653014fe7298653004fd7298653044fc7298653046f67198653046f6519865310ef55198653036f73198653046f43198653006f72198653046f4219865300cfe7098653004fd709865300cfc7098653004ff745
  | 42 => 0x100140020010004000000300000000010000001000100040040010000000000000000000064003000000500080000008006001400a0014000000c00000ac0010020002000400e000000100040040000006001000800080060008010000402b00000030004002000800000000000000000000000500680050010013000000500080060000001001c00000040020014000000400a0008001000000c000000000000000034002002000b0008000000800400000010004006002c0110008006001c00200040000000000003800100000030004007000c00b001001100100010000002000000300080000004005001c01c0008004002c0010054004000400200280010000003000c0080024000002c0010000000002c0000004006000c00100040000000000002400200000040000004000c0020008001000000c0004001000000500080050008001000400e002400600680040000008001400100100000024000001c003003800300300030004003000800e00000060004001000400300080010024000000400300100020010008000000000000060014002000400d003800000000010008001000001c0004012004c00e000c003000400200000000008001001000700080070000003008400a0008009000400a000400000d80010000003001400000000000014005001c0020000004001c01300400000004000000400100300000004000001c001000400200000010028000000800000000030004014000000e000000100ac003000800200700020008002000000000240000000002000c000001000c001400100100070020000001c0150018000000400600040010004002001000200140060014005000001f001400d005800200280010024008000000200000080008001000000000000080010001001800000000010000000000800000040020018004001802a0004008000000e00040010008000000000000000010000001000000500000050004006000000000040140000006000c007000c00000000000050002000c0000004000000c000000400100000000004002003800100040000008009002000c000000000000030000004000800000040020034004000000000040050004000000c00800000160000001000800703cfc7458e5403edf7358e5421ede5358e5403edf4358e5403edc4358e54004ff7258e54014fe7258e54014fc7258e54004ff7158e54044fc7158e54004ff7058e5400cfe7058e5400cfc7058e5403ebf4058e5403cfe7458a5403cfc7458a54004ff7358a54034fc7358a5403eef7258a5428eee5258a5403eef4258a5403eec4258a54004ff7158a54044fc7158a54004ff7058a5400cfe7058a5400cfc7058a5403ebf4058a5428eef2058a5403cfe7498654044fc7498654034fe7398654004fd7398654
  | 43 => 0xc012000000100100010004003004801f000c004004400100000000008000000000700180060000000000000c001400000080000000001000000b0018000000800300440000000009003c005000800300000040008034000800000040000010000003800200000000008000000000e00040000008004000000000540070000002001000000000010024004003c00d00000020030010000c000000800300140180010008000800500000000010003000000000740010004006000c002001800500140000000001000000b00100070068000000c007001000c00180000000003000c005005c00500140050034003004c0080004003000c000001400200180010010000000800000000030000007000000000000000000000000000e000000c0010000001c0050024000001000000000030018005000800000040090010003000001f0014003000800300040000010005000c0000000007001800100280030000013004c001000c00300000080000000000000b000c000001802c005800500000000004002001c003000c00300000010004001002c00100140030068003001c017000400a00040000024000003400000300040048002004c000000400100340000000002001000800180010098002000c0000010001001400100000000008000002000400480090000001002800b000400000000000020002002800100140000048000000c000002000000180010020000000800300000040000000000000e000c000000c008001400200040010004000001400a00040050018006000400f0000000000000300440040004008000c0020000001009c00100040000004000000c0020004000000000000000140020001000000400540000004000000c000000400000000030040008002000000000000008005003c0000000004008c001000000b00e000000fc00000000000000015000c00b001c000000c00500000000040009000000000040020004004000c0010000000004c00000040000014003003401f0008001002c007000800b000400100040020008007000000200000010004002000000900040000000005001800300000000020010000000d000400c0074000001400200180070000000000000100140060008001000801e0004003002c00400040000000008000000300000000008006000c00000040030008000001000d0018000001800200000000004000001c003000400100040060004000002c0020018000000c00b000800e00280040020027001000e00040060014001000400100040020000001000000d0004001001400100080030008001000c006000802b001800300040010000000000802d0004005000c00200040020000000000400000240010000005001c0020004000000c00100200010010000001000000240010008002000c003
  | 44 => 0xe000800100300030008001003c00f00000010024001000800000040000000002000000600140000008006002c0000018001000400400100020030000000000000000000014004000000f000000b000c007000000100000000008003000000e00b400000280000008000001400a0000008000800f0008000000000100a4005000400b000c0000020000000001300000060000000003c0010014002000000000000000000002000400000080060030002002c002000800b003400100280000000001000000200000000014001000000400100000000002000000200580000024004000800200240020004036000c000001000000080000000007000400200040020000002000000100380010000000000401800000010008001002c0010018001000000c0014000000001400000010000007003c00e0000009001800600080010000000001c002000400d001c0020058006000000200280020014004000400800080000020003000800b004c00000100000004000000400a000000200000190034000006c005000800600000040004000000400000000010004001000000200100030000004002400000040000000002001c003005000d001400000340010014000000c004001400b000800600b4000001c00f00000010000004000c003000000300700060038000000c000001c00100000000000029003c002000000000140000000001000c00000000030000000000c002000400c0040000000400000040020000010000c00300000010008001007000400000050000000000400c00000000014000002400d0000006000c00000000110000007001c00c00000000010001000c00400340010024000001c00f0008008000401a001000000000050000011000000000100030000000001c000002400100040000010001000c00100140190000002000c006000c002000800800080000014000002c011000000200080050000005000000e001400100080220004018000c001000000c00000060000000000c0000060012000c0000034000003400000140040030000000800e001c0060004000000c000000c0000018006000400300200000000000000c00000440000004001001c0070000004003000300140000010002000800100000000010010000c0030008000001400c0000000001800400000000008000002c030000800e000c000002800000140070008000000c0000000007000800200040070000000003c0000028000002c007000400000000080038000002000400140000000001003c00300500000000000001801d0038002000c0000008000000800000040000058006003c003000000a000c0030000001000400500040000000005000000700000020000020000000100000080000000000c0000004003002400200040020000000001c00a000
  | 45 => 0x4400000200070008013000c001003c0060008003002c00a000c003001800c0004000000c00800000020000000002800000000010038000000000200000090000001000c0060008000000000000000000014003000000a0008002000000300040000008009000800c001800300440000008004002c0090004003000000b00040010028002000000400480030030000000000f00100010004004000800100000070000004001400a0028000000000a0000001000000800080040000000000000e001800000000000000001000c00000440010008001000c00000140000008007000000a00040000034004000000a0000000001c0010034000000000000000000048002000000300300080004004000c00f001c00100000010030002002000a003800000040010000000000c008002800100000030018000000400100240030004002000000b000802d000800c0008005001000100040000000001001000200040060004002000c00000000000010002000c0110000002000c00100100070004001000c0020000000000000d000802400080030004014000400200080050000002000c002002000400100000000007000000800080030004001000c004000c00700000010010008000000000080060004004003c0000000005000400000040050004000002c00a000400000000000004001000c0000000004003400000080030008008003800c00480040010019000c00200000040010004001800000180040000000001800400000010014001001c000001c000000800c0000006000c00d002001800000040000004000800200080060000004000c000000c00000200000044000002000b000c0020008001000c00100000000014001005000a000000b0018001004800500100000024000000001700040000018000000400100000060004003000400800200010008003000400400040000004005000000a0000006000000f0004000001c00100740000008002000400000000010008001000000700100000000001001c0040004003000400700040070018006000000b0004000004c00000100010008020000000100000000000008000000000780010000001000000900000000004007000c00d000000000180000008000002800d0008001000000400180000000009000800e0038001000c0060008000000000900100040028001000800e001000c0034008003800b000000100180000008000003400600080000018008002c007000800600000050000000000001b000801300200050008006000000000040010004000000c00400100080000009005000700080060000024000800000200120020001000000100240040000005000c004000800100200000000007000000b0024003000400500000090060001000c0010004000000c0010004000000000
  | 46 => 0xe62b684a394849fb12a2175279883820907192dae5d027b2b5f94aeb3613303f416b27fe1c5c70f25941e8b666ab50000d118000000006c000000088fae6a33300000a82032000239ace480006450000322383eb269cb600000f2b8203820f887a4000013a8ee8000000199600025a20000b7868c83de2c19aea92021760000000be7ab900002616091ad0a000251098e800000007088bf1a8e7710000623852a00011cce03acde0c837eed5410d6cc70058dc99f984d69850000281a049000020e89badc01ea6c6f0cba9d6800000000009c912060000abc00017040002782e0d88e2064800064700006d08000c4c800000f00003cb00007d1000000023226fbadbe009034c6809b7a00000000000eda2e12cea0002eac29a8000486b32ae028906000294061b8000d20a9367398facb248000000364ed3828b20002ca6bbd82bc00e0446178ad32000056c000098497388dc9fb8000b4a000071487780000000d4a1b74000101a07612268030000d700000d3e1960000317232cb7c67f5180c0e991ce2899548082000048c9a9e3d31fda7971a6c2c30000b403274737255a7280958a53ad504abae2cc7900000002ed80000bc46ed80000001f8a085139c5948e1e13200009f49d4400019be000058e920800000000000000d7237d0628c0780006ac26a67189a3cbaca83e0002bca0b98000b3c8000376af1ea1200000000604000368c91815ae53c80b872713b400009620002baa08d92cc9971f4c7f48000d8b34c6000000032f358426a324e6308e42000000000001c438880000000000000034a36321ecbb082400000000000222292700002e50000d4b931244b80008b51100a35000072500005b18bb628b10e40000000000000000000008740ea80000bea000000000000006b6b3b800000003f2000090c8e0e000201c0000000358800028700001851e92a169ed2a5d32965c3b5a8ce02aca8d0aba200035a248100006571e7c9f600000000000000116a000c0010010001002400000000000008009000800500540000000003000800300000040008003000000400000030010000000c003000401000700000004002000800300000010000000001800000040000028007001000e001800200040090014002000c001001000000000070034002001800100000090004000000000800140050010002001c00e00000060014007003c0010004005000802700000000000002000000000040000004002000000a00140020060007000c000001c00a003400c0004004000400100100000004000002c000000800a000000000000060004000001c000000400000080000000003000000200280010014009000800100040000000001003c0000000000000c0090000002000000000000040000002000c0040010020000400c0000000000000000
  | 47 => 0xa236c298780000002f3438d9f5aa5b1b681721436be2314a43720880cf8ece01c3530a64a5faaf32bceaef187e1f8a71651f2e28d6c37c4000070673a801e2843376b66000000000004a9861a00035aa000009c539845ad108000000305a6ab2646705a50400000ca9bd241696ba66c94c800018b35883dd00009bf164c83100001e2b6ca46583d470a2894978b7b2a0298cecb195161451c0292a0412975835866a0e2857d0e82d0290de00034aeca70ceea0a32461bb279e0002610ddca2a04fd05d60002e509cbb1b6b7a9e82d4d377a03980009b2800080bb52069ea05abbc1fd8afba07e75680008b28000094a22a6b91fee0fc30bccc9093665797a683c2d4600000007ab211462ea5700000000c050000ce9ad8ab802642d2729ae85b000000000000000000b3d0e083d516c000014dea6a0000051b046e09800000000000000000000000040300007168d5e000000059f0a021dd2ce0aac34d0d951f240002140a041db20001db69e11fd08962fd072e0000000000001eaee694022381e4af9839c95180002a6e00007e83760786a2e2fc82663500ba1a0a80e800000001702000233a119961a0002b10000000000002a813f9dea000000088eb75822217844d99b0e00000000ae918a0f8000000000000000000000117800021dac8b2c5a75ca410000085600034c80002a381b336fe94e18d8cbc12fe0000000cd10000bbf8dbccf326524e480007eb37f00002ca45800000b070000000000000000007e3ab1a00022180000000694ad9239388480000e4a9831b721ca0ca85e9222ca84ad7c8802b2ab4d0cac472000000005beab9973e00016a25b0875869cad488e006d650580000000b660000bf65a4a5b4bd0935e37500006c0af78084000000015108cd210a1f100000001a1000007c6000000000000005da00004a918b80120000cf219e00000acecd23174457ab9c45f2d20b05037024b99826549310097ad7048fa82400033d009b0abedc900008a538247122aa855623a081b80000001f7c9112a8400000004780000000047c0000000402801000022b6b1034f211580003e828d88d708ee4f781b893000000000264bfeaaee0001b882a1b036000000080008b867a143e4e611f273e1338a47a0d4a4f00000000accb6397a0000065a000153240fa02490705b8a90a14a0051d9c5a6088c674aebccb4965a2639e18ad9265463a06f4000000073d1954c958134734b0ee27d9caedd7917a45988f479e214276e167e2ba0c36126b78ed2d918807ea2a6ca51ddcb21a6e087c051c71a2c6e441000066100000c3a8c200016c41161f220002ef88c7a2624c19a5edea0d8434280000701e088320c8445731d60001e14000000045393c20000c440001ccc4bd908c00027ae00035f65a916f0d0b8b74a6e209c5ac091c209344a0000a
  | 48 => 0x3d20001dbe757800000011761348b1400000ea000168823f01f600000000002be8000000000000000002ede0001394742a8ac0002f3647180004700000000196804810549368000000125832182ac000176c000000000000002ab800000018fc4409c963f2864a000054c4e880000000324cfba442818037205c8000d3280000002602bd82a549fa80002bd17907e5334c00011b885aad181ed00000000f76000247444600000000b54000142c00020664d8000000018f8a83a4ce00026c400033d268f80000ec80004540904948250c0000000ca3b6d20000000b5137fc0000e96000000080f00ac1d780000000000a0a80000000000cfd3712236a25010b952646100002e7140c09d0000723040c000000000033e88c900000003676ddf8000000200423580002a88000865294c0001e545f0131a4a218ca00011427e730860001a346260000581946800000009c830201fd23d814d3660000007200006548418000000368ed18029ea3b000002c93625e280001779baab888000a09988a6d82a1e0001c3e000000068980000000000000000042c276ed358000ccf2e606f80340d72a0980998000b2f800000000009308bfc0001aa6d1380000002c7e65ca0200000000b9c00000000610000000000000000001dac6b8000000000006b3b29000000007d21308000000000000920002958000000000027c26aea43814a2628b010e1c358000055b10da92616de595023a78f800055280000002f908b480007ddb7ca0000cf0c688000782a68099cb122a9c0000000154c15c9e600002c7c00012600ccb5321daad68135af4a3608688b79800000018629310000541990a7a6800c8e20000723b79a2c705b4dc2800033e11e65be8ba600015360c1959812080000000c1c000000000027d6dbb000053580000000000dd180ec407aa3a0001234dd487ea8aea02ce0686401d5984e1c5a5160dd9c348562b9489ab35c9a319885a11fbc86b8000dad0000d2f800036c80000002c609dd91566048f2a5fb0000c6c000080080fcd65a4842c926acbc41fd68f5200ab40a5e600004c2000224c2f5000000000000ba90a200000000002728da600000000e200f6000000000000001e30a32236c0000000de604c6000042a0000000000000000000003728000000243470b97bc38c998e2088908e0d111c7838000a0eb0349fc800078b8000615ab6269f00002b80000000015ec69035c64695aa0000976b9b00003aa9130686047453400007f38eb800019c60000000000148e44d0000b900000000290e00000006931442a319644000264437e8000000379cd39b7226bb00009f1a5502140000bf38504da9012e0c4000025b800000000006b0800000000004ea0dc6709326600000000000000ab88000a1a800071c80001ee80000001f9a000091e0000a469
  | 49 => 0x617131851387fc02a2e7447a839cc6692c4db30000000060e76d0000713000000011f60000000a2a0a3499935866bd137ac200000000218223a0a885028e7c977291ad7f277208a0000000000000000009d930ac264000036800000000000a3a05741911c1a00036e4538abd88920a800000000000327a35181d6000134e122a27c00000000000096b69331a0fb00000000000000254e00035cc3ec0934000000082ea8d6529190eb2c00005cc8000000105800000001ef9c80000180ed95887800000000002996cac80000000fa23011f3e2ea880449ba7e271f382a2f0b2ba50806909a78dea000000000036f60572e182d8020400026b0736860c0130000ce280000000fea2d22c70835800000000005850b4600030ca36d0012000000068b2c9800008740000cb800004ce00000008038a44db2364cdee2808000008000034ce7c7963a00000003aea9680000f1429fa73a907b0d02b1339cd710000000000000000000003506000000000022ecb990aca2be800000003cc0001e8eade80000002eda00020b883d80004970714d14a83000000000381268522800076380004c02f08e05a1845421d3c41d8000d178000b002a9c8e306f06fd80007f30000c06a97a28100001891e5000030b00001f7ea03a6fa3b83474b71800000000000002f3e46b2906ce425deae2b0b439330a4a770000d078000c1280000c104e00000000000000056581380001282000193a404a2fe293175a0000000cd030da000362e00000000000000000119204aa8d20001140000122493c92126220000d8484b60000000be111e20002306000258c000182e9c0b300dc08a56dd6800000009d278a8000000271cd568000cb10e8400008ce0002130000355c0002e36dfd8000000000000006789bb1d4a31ab5e600004ee00018243c30de25770000b43000030a000039a80009bc00003b9b830000085e2ae000000017e4670a5d2d2a21746d7adb853f00004cf9e04000000018029acb9600005b80b8e00015a4a7aacc60ec00000002a529cd8b4a13294cc2a100003178000143a4ec00033788da2d5ae00848485c31ec931a1486b6065e76b80005798872c1c00000000d680000000ce88d8e4d7191200007b000000000000c8a00180004a5000000000002242b6addf1f6e00011d86f315ea0000000b93b738d6380002f1842400032aa000000010700000000000651800096e80002161de63b115ba0b427405f69fc400035804708000417149c4000000000136ace09a1a7a811f03e7129a0001afebcc9baeb5e25960000000c741622026a60800035ae0b3000049c1edc361ab1400000009461fa479f8000123169ea9316d6b68000053da7b6000358267000009468a1e4f0099e592800088412becee81de962000000021fe0000000000000095e000045928780002
  | 50 => 0x1ca8d70a6900a511581ae1e263f71e5226e16bc33cb022b0a2ffc114a3f4070abc6c3c9744c0b87cc2049ba05a1b78a06bb258857aafabb5153c40e8ce201594260000952a8f05f8000000082c0000de7a98a0001778c9d962c89a0000000230a00022b838d000000000008a60d1a7a7a59a354825c00000006c0239600000000002fa60000000000173800004a669809aa90880004a595c28e183621d900000000000000354200013ba00008649e920ac21db2a40a991a495300006f40c964942f68000000000011f40a59b50d0e14041d8946445c0920b5b0e262ad1be893e2a588b9a04e00000000002f7e00000000001a0a21a80000000000000383a76206fa1b48fc600000000000000a9230a0000146e0000000a8110784581a2a00037a00001b0c48584723e2248eda98000c710e2c66c00004d41660000258400000007a580000000000000063e4f280000001470a6300007680000ba48000000351a3b88c4a65b00000000000a4e8000000000000013a614b8000d89000000000000000000ca800000000000000000094280006d6049e9a2ad0800000000000c92000114cc92000000002d40000000a9e34623e3310a15a0ffe6689e005549be67bd055a2d418a8000000095e8a146068000aadade28490a066210000a8202867531ed60000000000300430c92e200000000001816b7000005eb960c00017a895885bc3c4126a030aea498f80000000000b91944a58600001c68eca96002a20001d1c1ee0000000000086b0922d8700001dc3204000000000001867c410082b88ca41f60d043efac24aa61ac6e06370c5740a96000000000033b073600000000000ae699365f8000008f103c8eaaefc1a9b25c731a84a530b0fa2dc8000159b0a80002e8e0001f5e919891874e9bfe98880000000000a388bca000161c00000000fbaf6e9ff246a0001ebc17180000000000000367260f800025f8ebeba21b1c8bab0c2000104a00000000002b320000000abc02b2000311c59c8000d2c8000002aafe99585f28cd861c2b01fde67780006c42c50a89378450c28fe015193c13d0ba858217e82b6a0260000000d2e863ad1f254a85f1668c2e37084052ee2b1880008449fae34c85308f0abfc69a08f89d297acbef1ea400017220001246000323400000008f800004e8000025a800016202aa54a91320000a9c8fd951c6cba7c800016788289b52dbf3048302b16037e13860001a580000782ac20a8abbcb31655f0b40c0f275288a14aca97b3346330000000000012d000048b12800003682000000000014060001d220001c54000000020c800000033e6000211c0000000000051600000003eea6f80000c3c91934deb2101ca50b83bad360114306305e000113a896868e0002e8c000278e0000bde75fa56c17c09428ec0000c851b16c7a855c
  | 51 => 0x4b2a999400000000d7b4c40a486180002592d29057ec7212022eba8dc9b481d4dfe353a0d180006a4aa1cdf92b5c0001e5a6a7328c96a9bead308000000267e00000000000000add81a20002926cde8bb800032fa0000000000000016625661dc902e94f9f365c23338c69abd0df596d83fda458dccab2600000000000000ba01ade4f134220000000000000000012d4000156634200000f2000007c345800000000000000b4400000000000000000076780006c20230d9e8dd07d521ee8ba1b240000000031ac58cbd920c34f000000000000000000277800073b029800006de98100285cc37ea000090c9f1000012bad1e6d58cf680ea9567dc00008d02e4a229ad7275a00000000000827800000021fa0000a0cc0180001d1b57c5e0b15607837de0000ec20000a5e84d9d785f480be00033d8262800067a9c866bf31f40000be054c24260000000000284200025a468e80001a7a6f6de1800050f000000000000003576000000086e06dc7e000007e8800035f8e8800030e821b26ea12b17f03b4b6e68acb3da8f187fa00000000000b1a22d8c400002edcce388200000e664f221d89c2ae66000000096a0000b8aa8f471290700001dd40001d86d6834789d41bd8bcf15b090126ba381347e6678242d7680002dc1b8e6e5210c07a0fd49aa30be6ab94405a080004ae000000027dc7da00001502ef43640000000000039016422bd97bed39240c859ab9e2eb2f6600000000000a22c7d8000bdc2c9e93d8000ad82658c2ab0e4627970a0002a808ca8000a8625c41bc8000c7791a02130ac2aa992202f93556d4201a8dd836b00231534b0d15a600005ea23c80000000000b178db0a759ce260a00000000e62799ad423bd1724bf59dba805243a027b5ce5489a2293700002320fa65ba33544438f2e98e317c746800066600006ee036058e177cd031c223778a7c9298000b7122808c100003b70c7600000002260000000000088999dc000077e6f00a0e1f80d5c814a44e2f3000000017289340d3800030747b801acb1a0000b34310421fb60c7210000bc280000000d7a9ea0000d90ad4c3d80dcec362b8630ab12c000138cbcbad4089127ceb98b4065dd94d4d51055268e000000000003771f0600012647f2318236d930c6012738b3323e8d7736d68a420580e202806dd8eb07b68f9050d1a200c00a4ad44978e6b880086600f68000229cb90aafc1fe302a480015a17e80002960000bb23718b22000010f8d2e0000000000068000016ac6d3800098f1ac45e519c4c80b498000078e201a278000085c00000000ba092c0000000000238a5d58522c94b03a92580001f29630861b1fcb6c9d08c358000000000000035c67d71c426bd9dccb632420c4ea27411780005d486768b200000db1bf0285b418a611d704a60000704b306d9614a0000
  | 52 => 0x912f800000000000a4200037300000000d7ab3580001adc0000000b372b5e81180d8d759cfa8bc1a1e0faa67600000000000d4293a28bc0000000ca18000000352c74588ea00033c600023ce33118e42cc1e1a15b80006ad1cd40df8a7a31c8000b38800000000001f735f4776000000015ac8ef80000000a5c94a000093d000041816b4330800000028a000000000001c6a1b52096000375658d812600029b6000002c0000000c6780000000000229297e8a18e9272d000006600007c4b5b8c61b74aab3a3c064c076608732162cbb1d43542a769218062e089caa2d1158441034888ac2fcaafa8d360eba95c616868ab57825a27e8cb68de800059e98a0beaaeb66cda31039e8caaa77b1c637c9da6853a2f2dd71d844db0a5400000000000000b9e261800008bc4eb346a00000006378000aa880d6af6800027200000001ffe68c1e801aa00001981f52064000000000006f5880ac683076b6d0dbeb8c32a2692014e1122836c8a34bcac02686adf8156059b6bcdf480000000000a3c0000bd000000000000b6a82f6c378ef66818000a5e0e6e200011c6ad800000015d48348000000000051c8000b9f0000a140a2e0ce046e000203e0000000000000000000005bf33be0000000000000020080007d40000a3f0000000280c00001640000000000000068a00000ad9ca40de2efad6f80000000000bdf0416000253600010a400026da0000000048ab84c53800000009fe00022300000000568800092d10985541ce8b8f0000db8024a000029c0000000000000000009e6000281c00000000000000b6796f2c3391b2b619b3e00009a00000ba4a580000d0994006af859a00031b80001df20b5b0b2c878ba297200b47b18a70aedab6c941820cb3985fe63737f4a96a1103e680000e50ce400000007288e2e000257e000058c9e586a000000005edb68000ba8f6cbbabae2c82316768800000005daaab106ac9f15ee0000cc014b000046c30c8000265ab2580000000000290051200000a0000000000000000000000511000026c8e980002c0e4950000308018e1e4137600030b60002760000183466d8000232a6f20002f4688100000242a960f6949400000000002b0a97525e84300c6043b000000029e21050ff8526800417292c88b182c41e70000aae2ca0000000052c089ab7e9122000320087899bcd0fa51260f00000000000ba6b51400005c29e6acd28d32812000056200012781362a68000143a798a1ba7c319d04fc89ce6a008d424e0302616127ebb4b18eb46b6a0a71372e557997c93f12c0a619774c92a0e43b9361ed09094a29e0c66060ade042405104511578b031f28000000039f80009ef14020002fc06b2ab54c599b6a93b800067c1c9092a81f41d40000c5c0000d53a26c0002e0c42a9a668dd8000000049000000002a8306
  | 53 => 0xce6de1c0ad5299e455a86aa1d384f6385278cbaa060a000000082bb20a000282292f000000011d6cc2a3fe000341c0000000c76000000036b2956082807ba1d403307300002e38000187ac508000a9f80000ad088e00020c6a818000000000046d2f5cab1350cb5d0a08ab5a5c69171b14d4627fa1100000a8014ba000000000008cc0000000137800028e80000002b7014921e87fe8000000000031d28c0000000046dac8267b800025c000017021be37b0e9a9b78000ac8000090f000000031da0003778af536740000036d00000000014285dc3394bf482782342b381930000709906400000002a331ce0000022ae3868c0ed000019f000057236f0b7e000025829f45bb8f6251d00005d7b0100003030ced1bfa0001e700d0a3c4000338800a93e00cf0818cdc26fe53625e400000001ae80000000000000085a000000000013b2000000000006d055000000000694b80884400022d0ceaa696000112600000009850b328f880006ccaa8e1e983c630780000001d3ed0080000002e3a31380006a2262400034a00000be68d387bc79a0f8e50790ac3d9affe7b09438432b64aaa48594aa22c12bfb10b85ce9c0851734cc490af264b4934c7ea1abc9d5800077588e67cb800000000003f095e84fb800001aa80065e2fe4caf80000000f46bc12a60b09b6868eb000000028ccc9fb1cc00011547d58c78cc23472168101636203221d7016edb017e27298000000129ecb40bfe980296ad3f2456d172cda3c925f293f80004c90a320002ec00000000d490a1230c2076bc02860c352312d248d100910000000229e000000053a99920001bdc0000bbc26da3840002276683ae940000000000000000000007930000255000040e0000853000000023600001ffca2c313827a239e85900000000000c00000042b800048c00008e9800000000000001384867135400000008af17180000e169438000a1c000000000000001696b3b9bbc93c13be98d027c0001a703d08dd2c240d3e0550bd06ea32de4399e48abe047a13a0262010242483424e620205d22881fa04dd0adc638260e00000006198000000000037800000000b6aa4105cc0000464b931dfa0001210427000091780008d20f12811146000028a2005880ca73000003e0000cdb2a6400037900000000000104868307400f034dcb0612e023789eed750000000097837980000000000000000066a8d181d682fca14aeaee05340e5e18ad200001368711a000000e466d18000000000000036a8000353882297fa879805e1f9838067622c012f87f60000f78000000000000000000f6a0000cd80000000b91218a6c78258863a470a462b4a82c9ba6c568000bc3019c7b9000000019e2b970000d9700000001b6600000004fb000018f26e64441a3600021c2b9e9e7600000001a0a4d2b7700008e
  | 54 => 0x99ae262c20dd64fd8f860ef1b44d67274ca69b04ebfe33e0843a78a30e80000000000c9a8000231b66a0001716000213e0000fce7c50854b7f3366cb680000002fd400021380001124623000059c1aaa05d0b8227e0e3e63595c0335ac38904800065304ec37a1e4454b04b23670a729e498c4962958a3b40d4e7279a825cd07ac41ba028d9f18c64cc9136812b4487bc9390c8392aadb8aae40003130de89030ac08d4cb75343c0001f840002c480001cf240b1222c8880ae00000004119f2a2b9b2ce00011147e78d0eafd94f891b1fec0be00000000d14d6500000000000d990000000098840192ce7f70000000000032f8492a8f8f52c86ad54000002600006ee000225c0002948a150000dffa3661008836c728a6c00018ee00008c05c330d2a2320780889ff092b0000a54000078789ac6119838d3c0000d7eb832d4708a03a800003969574ad2000000000007d935e83d62f168b7800038610fa22c179a19180001ab80000002e72d23b12a2e580e257b000000028ce1679b8c9ee9422359b600447800000010440000ba000003c40002b4291d80000000000ad01d400000ffc000000032c094800004760000000c298000b592e760002aa09358000000000030b882a5ffaec61cd86125a38000000040009303a8000289200037624d0000077dabbed1b8000000376e3ee0000000000098b800018d12569d0b4c0e0824e0c5536206e626dccb08d1641f97e691495ca07fadde76016eaafe00009818a48b229a62aca06a25f2045c8c7266a000378c0002d14328aa50139a544df38bc0cedb39826c23b63562eb4752148612e8390ac1ab1e0d91e426148e580001a045fcb304000031800000009d62f185d882189a68000000083800006e2b01b26e7d0ac08355a7d400000000000e94a85000000007020000000000000097d00004df254253d1a42d05831ccf78518409b6d4cc49764d7f8000000000000025c000016f800034300000a8e30e2e1c13e8f5e0000f94851800000004a49f029080001d6e00000000bb1904d77800000008aa000000000000000001eae5020000c7eb36a806abdc00000000000e5e566a0366a8a1780002d806d331e08e6000054a06ce000274400033d63cc35bc3dc8000acd00000000e505812df600000009379d96a0d00003328408000372a0001f46774a070bd4b6be30880001cf32bc000363a0000000000000000000000000000d58000000000008a90000083800005c0000682173c0001af8000180ac2780001da127a0da0e809c119fc000374817b3456c500000320000051325ec7a422820000000af10000000000081f2b3c8f280bc59d1c362762402a5280dc99321088908cd20ca1d8cd3bad2e829299e0d683b8531b4946492976587a92ed552aa42450e9e61c14be9522c640f0a81627734107f910
  | 55 => 0x67000007545570b1ed5d38060002f4855ba526699127c927b74c000262a7340ff2336859659b1f4ea938f7cda68b688588410011ada86dfb07a7819d7cacb1dec96786382f4b07e0002fe260da2a200019fa00016dc00033f8726974a000224ac3700000000000000000046700007d00ea4d7ca94400000001f90000ade00003db00009590000b869c5684f00000000000c4227105cb9dee0000000db611d4d6689bc062ac94c5600009d7800069a80d218bb58a01f9df8ad11dcaabc8bdac5e29fc504a39c96d81627a232108cb9240932ab2e365054800005a611fae32b3f8000624b6c40000000c4f80008cf1e0c0be9024013aa8c00024543ca000082aa74e7e980007ada27ab1a80aa640a1f600000005b9082caf0b626c7e00825b3a7e400028c400000003cf24480002010ca780000000000000000000012f2000000000000002710efc103800062f2fd8ab60b5c4138c9000031e8221287a0000000c3e0cd400027480002ce4b2eabfac25800000012920002c52dae94762a6300c06690b484585702a4000000002da0000e3c9da00000000200000000025980002502fc63818000426800000010c2000112022ba3707f80000000000000019d46320000d630000807afac0d3a1f4abd00000000c7c7fc8ca6593b2703d3b2c81b22ac2000000039d0000848090a2ca0000b3b264e000225273d80003722e90b842c8e9898000351091016a978c7380000000000017400005c521a20002540c14087075b000000005cec3f974861100000000c3467f9a960002ac0c84a9e65adb0423322e1600020bcb5b9ccebe707f0479000022c800091299f8b640bf8893b6ac9a49f3a8ee0000d2780001cf8000bde881c1d8311eb6c1c66000025693a8586000373c0000d8a00036d00000000000162e4130ccec1600000000b64000318cc7c800089fb43205080002cda57413c17a2dd99602b57245a5ec8000a74b0984b9831e0d4000036880000001c7432b8c680000c024c120d81ff933c0000000000006641c963cd841c0ee07a6b43068000b10800049d8f4a00027aa425179e00037c010f05d89642ebe4b68ef88059efccfaa2aa1388106227b24292dae8ada8b62870a8000000267c44b00000000f3e0000c0809b80008de0d6c00029160002c1079d273c1790c4609a0000b3daad00b90000000000042100000003828c3a80007bfac2e5231182a989e8cac12208279031ac38155a4e3901c0002f02c46000000025d8c1b800086c8000187b71a8631a5a9a632fc0000f82b0b2254c6200000000d0c8308d400001fe2000211a00009c000000000000000758ab1c4c2800000012aca66b220cc533fa0000c64737a1c6849882e73209ea00000000002c546c48dee11aa3dccf104383b616f6c5123d058390f665eaca2400909265c29ee8ce01102
  | 56 => 0x52a11d0a8800002e6a17e000071800005ac000255200000004080ed40000000000155600026d66f69042c1a828e000000042c81d03708000193800000016be0000000cffaee87e0800093523140002d9c00024b2cc40000c4380007d8a6a49101966000000000002fe434800000001a4bd68d7caed34145b8800000000000001f1a2c60000000000000027125e72c4c000000009faf4e9bb948000000000001e364b42fb2c3000000408000000000042a0000a198000c78a13446f0000bd433cebb3b06c87580004ffaf120003754a7e0d6a0002f94c640000000102ac8fa5221368cea7b7a95490b8a7408e0f0ab89376acbab35043f8a30a1a00006ce3634a292c66cae15f8b9a0dbaad189f40fe121ea2a9b9061e074c6c890107ef91dc6e59aa8023aba87141874ab3352a9f32f8ea271266ad3000019ab5400000ab20001d669b31e247ba80001f69f4a1c30ede00000c40002b567b29414bc8b3640000000a17197e1ac00007430000000000090f80001078fb656d80004ad82be9e19f08000150e3ce370616480a21f0adecae0920a00006d8000174cbe599b2a3993ea3ba2fda0ffa88470c0e5c34a2c90c6f80000000000000305c74a80000000000000160a01d00000000000625914a4dc9c440790de4a7c1f18c5301b052433ac00020eaab68ffa14d932a171255c78811fc9afad9a218a9b44ef049cbd89b3c0e398d0c62abe6a5f0a68511af2a8a69cba19d2a8a0808d30837297284b85a2a9e801c0000880289216e00000008e88000b4d8c54a01000063000000000000cc6000000036b6000262070ea90c7a100008f2180217f241a000276cad4991658a800016c8afe0438000162800020f000000000002f891d2438a9fe939192ad25800099e94181ba9cb0553a70097f29329c9980659da4928249726a21816a96c9bba31426c06f1805a5bb2bb83cd2b6e6fc91f8cb60fb4c5f88e07c5800096c1c183cd8b7c5cb1ed01a11882000021e00000004ff15fa000000000032f2ce584ea000000000022d60002c2000000000000000000000000000002fea356b5db8008ea18ac37c00000000000000000000010ee54e000081300002719d0000000004911becadf12b40000000cac215a00016f42d62fa4a8a29bc000000000009d01b823e49a8205e3db91a88b900000002c3e877a08242f171c9cc0050df89df4ad3ad0e06f0f1cc6cb0403268000883821ab302b729af0000d489e86691000000021b07edb4da000000000000000002be0c4035e4000069a000301200027b000000002aa9dc200029123e480001610428249800036e2e2e00024502ce0b86000000092693dcce6b01c53000000002f760002930c289e2c414b48c1d486f675eb08e0002d1c3ea130e1771ab233702760cc00000000000e070000188a7d01d098b60002
  | 57 => 0x1d1e00000008d9368460b01844bb8532891b008c1836de043307c0001e9800012cad8c9c1ea51aeeea69370eda5b28a3f585268e4b4903099e100002dd80001cac6ceaff22ef80000002d58a201454dc110f4540b7280001d50648996e0000000bc701e2000310cd0b1368a328d34aaeb65a0000000185853ca7a00004520000740800000020c0000000000021ca00035c800036300000daa0000000a0b8000000125ea3c949e4cb80008b08000841000028f1514000000000000da0000d64c3da83802293f818217884ca36dcb329c040000000000000047100000000000acc00003a380004d2000000017c2000019e0000f4455888ec9eb09ca0000000beb82840eaaeec56a05b60b79a7665619100000000b490b985a996246351380978228498c8f26dcb017e0001c0c7e58bec000000000000000000cfc4d60000bce8216000000006ea17a77c34b0000292a88d8000a0f0696bd52414c5aaf82a58a8145ec0e1a4a100005ee8000000000000020be000037400023202530000000007ca008000a70267407b1b70000000083e055479795fe0000000a268f980001dbc00000000000000000099200024a4d21986a0000672000000000001800320000000000000006a495bb63e1422d529a7323800000a46d906320000e3a5b5157a000143243ca7f07fd9948d5f84447249798966271a870316c1cc86c2617828aa7b0000010976a00000007be8e68aab800000021ce0000000a3680000cb324400000003a300008bd0000652813e0001b6e08905804311a4e542b59eaceb2924f3b7705d0866c4ec32d64cb20f2b5e854600022725898000c5722c4118951e5fa800000003f40f4adcad7c0b76cef2c44000000000000005849d3400010887fd000003f85906f100001558000000329ade58ec600000004689d9a000069c09382d20001d4228e27a2000263000000008662c4e0000d0000000000000000000000051f916c00000001808020d020000d8d80000003016000380c00029e4000376c000000000000008fb800000025a6000260a66ea152c4d00000000000000000039b00002f713e6ce300000002cae00004aa9928f5c4b70e0c000309a0e29ef019a0f227ba18fa34982821fb1e02000000040a376400000f425ca394aaf36160000176a549c820000000d3d1780a89800000000006478000d9b82ce14000003679ddea2394fecc39af279aa70cdf21a24a641b80496800095db0f444229a23c0b80464d1d2871d9ec03992f86c209d245fe20564a2a7788dcb2e0cdca328296b4a6bac0ad058a377471e30ae70c80000002bac0000000d5a2a406c6b7baa3eaa22000350eba5974e8d628b60620ce82bb100e313000013f04068089f8836493960001658c9004a07a515d6b3f00000002c4a429a6c838900008cc000090da3da5a51974
  | 58 => 0x49c537b4a6807ee0000f7abb900000000ebc95f00008d4b60400007d00000000d5180002cf000051a80000000000077346c0002c36bee00004fe9890d868000106000000000008790000be3000000013d226700004e780004a725da0002de497e01be73f04a2a2eab8cc520aba00034ac92ea56a47fa1bc43e00000000da64de00008c680008048aea0000d7400009e2961ac3aa9b03a2a13910ac9b265e2cb1daa00000000000af20002446dfc89ec1c8042c9b4006464330cc17d907400000005c780008cb0fbc92c288a000113e0000000348acf82730d7071b00002adac46108226649330f0ad692b05b207aa000325a298000085500003df9214895aa363031bd403c0a9ea40aa2e00019060000000236087c6f2a09a0000000000194e142a0800000f3200000008c600004ae8000cf000007482c808d500000001ee2000103424a871e74c1bb42df8f9e00000000001a1200021920000b92000080e22e906c16e8000000000000000005d1800000000000000000000000000022f82d395be48a2ed688900000ceac020002a0a000212c00000000000b5600000005199706bc822960002a9e00015cc00000009e20d247a8a35e5f61bac1990000c8b8000b7f920e000199c0de8810d5307b2c600000cff20841260e78b271066000240e6a18efa8f79138ab805a89b093d628ab4680fa067a0941586bd7b0e2821a3ec6e11d6048e21fc253b330000098276c11060000430000000000000004e200002fd0000000000074395f60002a1a0001f2c00000003b02eaa2a0ac3013500d41a480008b382d8c9c8000df500000000000c7080000003120c7bb470c44800000000000000670000000062899a4598b0542541cc209c90e033830524bb0dac214aade9df1c4e0c3028cb05800061500000001cfe60c01ce2d0800000012f06482eb80000c42bf3000069000000000000676800000034360000000000000070737ac0001acc00032dc20f93460658000c650000a3e15700001aa000000007c10000000072680c35a4a341b5a00026500002e7e026023e0000c9c0000c580e680000001c6e0001eb8000000090a94c40b195f2c0280000001aeeb159ae80000000384a5540003298000234400000000001b0654f80008b8800056c800000016b80000000c27000000017ce9ee1be2000000049c8052bc500009a8913c000322a00000000002ad2d838d200b70be87dd332c0002a161c917923a437bc78c89a4692800000000000000000000000000000002c280000001ef63ea813200021a00002df035237e66cd2ff00002f6aad997b400000ee37dabde00013706f7816cc45308488f378896f82206f080000000000d388000000277e0000000d918000dfa17aa2e30000d761b9c33d0000b3a247a4ac94b65c4000000000000000e704f40cfe000
  | 59 => 0x295ab6eb1288540000dcd0088c40800003e846048d996a1881cbed21000008c98d2817000070e13023fa2fe8c891a5cdc58308700027ab84800051680000002a442630000bfd0aa800035362d8a4680001456bedb288675839600000008ff0000522000000000006a6382e9421fb080d000000000000000000000177e0002e1e0000d2a65921dcc45800012214e04e6812c2bf0000947a21a0000d5a1a1add0365a87629b99769ed1f3ca651bfc6cb333e3e294b487491e823e936e0002fe60003606a7ea1908880354000134a00027dad13000067c84a89ac9a546beb23c26f88f025590be544a9dac86240a735b0686d8acb8532000062d00000001da86218000355302800000000002d043471942865a0489e40c0e23d94983b2374048f0b16021b5781e10000000000000000001331b0435b800016c34ea2b6000030b000040cb598db1965c5609de8d5b0260a4417660002be4567b61437300003e90000000000060aa51481e9bce22723020fc95d85e5add600000bad561760960a7060002cfa0390000225078004f0b8000018aa32d06c488d2dee87819cc00017de0d5905ab1e23fad1db4e889b90ba5aba61acd8806e0000b6c0001ed474c80004ba2fa2a6c2dce2869ee6503a84c0e92e82dd38dc069d30ba1bf891264600000002f3894eb6e8ac48fd83fc248c199aa305ca86c0db3b1ac32510509ad8794000000004c0a3e79caf1ae10331ec5baf8a477aab2a59073425706e8b95aea6b309218a1b2e6e94092d8766084070800000000d1e1ed8000d549d583f11d2600033f000000001e825cc3d233a87721ad6d010e0aabaa66eb650480b33876c3f8b7c2a80b3a4dda1950a6207880000b04b7cb7a66a6aba60ae0000a6a8000cec971a860090000000004b58000d7400001431f6cb699700a19022c55a05f4aff886e45f96da0000000c8e80002ab237400006fc0001818be693d4528ab18221a3cc2b50974000186cc0390a08f5a59c8ad03dc0001eba0002a6ace1b7ecb9534280458000a24000089913cc26bb25e0001de2000181e0000000b49976ed521ad4c0e32a81df04c43982c0acda022653a0a50dea82e01f002c2be83056d20152495c86b63f3000025b0fae000000098da06c49d31b40000000a100000a6700003d40000757000022b2a3400013da6270000da2097a4588bb087e34f62079a169c21e4ebc9000000009d64cd03b60b018726cc10d0a1b800007198485580f5600014aa3e00000bf0800000021568b800004c8915a8fa94da0002fbed8a8032c6a966a0002a72081800044a346411c214400000002a50000000032a000072e63d141a314b65e000198a00010181b280002e40b4c58f8000000081600035108108000a49000000032c053900000000da400000000171352cbb2dd2df332e60001720881a53
  | 60 => 0x207de28e4cdfa4a2672b7b01130d3a7bb2d3e4631dc0839814c67217ccb35800029483e498b01b21e59168000103634b00000002cb46a517ca00011160181b7c00037207919ab852e02f08ec8a76000030a000276aa3b8000000000000000002a9aa5600000008830000157a5c298729700001fea0b21f38000000000000001960000b5280009e7000020d18a46b4247e00000000001d2c77f0c62b3c1c8a880a11e42d80008a3a1f2aa69cc4000110c0000000d98adc85480000a843280609a8e0862251c4ba8748dd115c45b300000d231467629326a0ca82c0000000ba700001e78000d5c0ecc8bba9d4b96918610103ce0002556866acc40000f0051b0000a602050d142762cc080000001c7e00032ae000000046408d2cf700001c380000000000275000060ca36a00014a60000000052887a00028441898000000003a00000003f98000000000051e9356394ae1475ab4b4cb895bc000141c0000a36431ae3411e32542198eb4181945200000003fd279426504500000000c7f800000019327a71e7a1b68000d4fa3902bc33c2cd48ea2d10171220993b878f2ff60e333ec6918000da48c701e620fc0003504cab236200004b8cc899f6c23000000000003ab8000562124800000000000000000326400012fc00000000003780d57a054c1987c80002ac836b800000021a47aa8000000039e00028182438902810000089029c8ba7a7f400008b44b090d84bd1e3aa20b59212f348ab4c36ee3e596fe00008c40d100000002fba00033aedf689866c9959237f03662cd062a8330000000339e00000005120000591b67e0000000c4693b6042b838900306200033a0a8b108ed781bb2000000000000000000000000000000000000ef9dc6a9f2b980001572c589342a2202f4de5000097bb454aeead62885b15214e0ea65de80000000cde1af9de40001198000000000000000001666df600003bc8000610afee6e7895ed9c2ecad06800000000000002a82aad00000002d2cd0ea7de38c248822580009dc357a0bb800000000008c200005188000acd9632000000049b00000002f0e78a000000000000000000933000000000000000000000000000000003c100000000000000048e000000000000005d50000000000073b800000029b22b9155480ab2e824c80000000a9adc4072a0001b9296f0e2ab1b337c53c081aba8b572000122a8b71b28a50b5643ceb8089d9800092b9d127c72e3e00000000a20e76bb80cec83b0f1aa7099ec6500000b2d90860300000cc99e407ac1e12a26094686787d26368000a7282ae5259dceb6231680002472c251ac00b883d6408800000000000000000b68ab22d8f2becb7699a0608ad12003a9ba00010fc259022a278000052c89300000000c39a4624669f58cb308be000328284a00008b6b7920000a1800
  | 61 => 0x180000cf903d0974000000000000000442a9980007fa00000df0bb2340918eacf8f5a6e9183a2d480006a30000000000037100009c7a85e13018b04fc000051e000062000000002adc00011521ce03148281f32732b17693e9f02ac599a659026c607f11ca86d00000001fc675d8000717b3f65a29ef82dba20a54698ea55901124aa00a6000378226587046c600f681d08c2000240607229005a7017abf8236eb2a0652d6d800000018ae392360a000001ac5916ba0d499264f180000000000db68000000000061a21605ff0892c0b109696e1b4000002348d40000bed000032800000001a1c89811ee0fdb8129b534b8b320000c98800052498e60002fdc0000e100000c060000aee0000000924000000005a40000000d58800000000000000000000212aaba04940002e0a68511fa9abb268000000000000000db800033400001f3b2f475d31f0dbd0000d82000000000000000000000000043200007b20000000000000000001f580b6000383ccfc80002b180006a40712837800081c87d4b0f2678b92289e9b90000cb2a72a0000b106941bf864ba1a684cb51600005e89f2b2d461f0000352b444000181c000000086a8000000131e7cd0000380a6126b200003800000c981758825304c8f990d43f6804a6e6a52c7c0129060000000000000000000049295427d82dc280e04260769d948731808a59857cb2f2f6c000258e000369e000313cc6b80001b929c60000000bbaa1189ff93e41528d98465133a24f00000f280008a20feed1ea9f200000000000000af20118661824848209243c3800086d8ad664b0000d9492fac098000c3f19ce8339dfe00c335a71e88e400026480001a6e3c78000000285800000000000000801928c0001650a1f85ee792800087a81443958000210a3260001f20000190800000009fa00000cd800071800000000b2a00012a076906c600000000003434bcb1e1c0002734d19aa90000000074400000000000a4a25ca9060000a4f80000581ec4932000000037760000436000000000005e00001fb2000324c3601944cd7844a3ab36f2840a718a3a8b5e21a00000001e346252aaa09c11aa63f94d2a48a66257928de83a06ac0002214320888a000175c1db81586c812e40000f080001320b2300001541f723bfb342bd10feccad800000001f8bdca28aa25b6f87afaf92b1d153a05e25ea43321c8304184a0000af8000234a2ac2d4e0001c883a28b22c7736228849b6c00027a0bd900000b2800000000000000b0e000099a3e1000073c022e000000000000007aa148213c97d40000128be0000083f80004cd8e86b73131c000020a4fa00000002c32000000000034ec0000000c658000000221e568000000030c6ba1000000000009900000000011e84006b40000000dce8140ded80002601876b8380005cd96
  | 62 => 0xb2b0000658ad9600000006a11f90ca11c062b20c9e25a000024a30c49cc8000000199a41795b4c8c9ad2abb2fb09ef83340000000323000000000000002694ae809da1089b2a5430502bb10700151350a000198c0001690000000031e9d9000000000000000000175012580000c5908000000009f800000001f0e0001f6ad9e097c0002f4c00000009582494afc97b8584036a00000009aab12e0000c14d0a80001eb82f25f58000b4eac220fe8000e040744000000066426848b310e8a9d356a000000000013141ce9fba000190000000005f40000cd832fe000000018c332e0003618000000000000b015800002c01fca70b15e09cb010800000008cc800045b800000004345632bf4cc3051a2f2247c0002dbc0000152cdd0b9ed3ea722000373ec3b24e23448f700eb000088b80007e3000018db088c1e3742d9113aa073125290b31e6c820000cf515040000212000000000000008fc8a620a900001908000da2907c0000000d6c958000000000000cc600000000000000599293419fa68e6d295d23f90f4015631849a0b6fa000000030914eed698000c49a4be8df800001d80002208000823a4a003a0d78d7b0000000000016080003398000000286255d8000498800000000000001dd0293b71c41a2c7a000041a0002bc08190000000111a0000000000000000000004c58000cdb9f863ec80000002774564112a000235aa76366c000000059b80002828eea7ad0eecd7491a63c8371e74e16a000000007f9b42000025fe000077a3c180000001e380001f928be800000018f00000bce59781b637f8000000000006d000009500000000000a5b90623239772dab8000a7800000000000b61000010e96a8000054e00013640001f7a730189a0001d52c670018832a806c492d1616ba52467d1d36cd2b4d200000000000000a1f0e9c000000000029ce0000000785a46e00000008060000799158eda700001340d7682d8000000053e2699c46b811f0a0000000a8c800081a8000dfe800000015b852f334600000005090000000000024fb82c0001a8a00036400001cbc8afa2ac0002e5e0000b8800000000000000000000000031c083690eab48a9f6d7e2b24802298e316800000000000002408000320c1592c5c7cc00001482d6a74606986050eb60000386000051e21386b24870c6c000070a4939a5600011dac0f8b7a00000000000000d47aeba94ba2f68b60000af88486b4e000005f20f445d08a2000000041e80002ee8000d350000d7bb1a89228ef06fd2b805920000000281e82d17c600000004dfb566cccb07256700005aaa0e281a0b8a6f2079a46f8078d6411ba58584dc8c30f184e2800288c81484a180002118bd6341846c0002e06000003e74b95940000f16ab1800002502b01e331baa4b1d148fe1d827889faaa4700006
  | 63 => 0x4b7a38228a2f2800009165b4059c000333a205225e00024d87649ece05a275c6d22780c9418408a4800046780002a900440001e56000000073917f66f900009e980003f0228c1799e6c0000000422afde198800000000009f9a6e2000000000034a200000005b4800014ea30000000000002ed0000000048b9634cad0000d2a9ecc71035ac7c9800051601f200004323f4800015d8000000000030fb648102800000017dc000215c00000000001de0a1d32f80a40000af5ac7600000001c700004e9363830001d2000000011a37d0bfab2a68cf9c146040e54000150000011ecbdd000023f800057c000059592bc000338400001a05718454c8db328d9a274600000007b60000063000000000004e080001dd800090a37ae113af301cb244c00000001920d9a4f89d64defb3360000ed685a18e2aec954427c317a000000000000000000000b6b00000001b8a9de80000001a7e000000000000000000c1600000000000f640ff2b960003230000284686a2e207418c127f0866ebb31b54629b69400004b0c64b21c4b184e42fc287294c000000022a8741000006a9bbe0f9800004117f400000000001aa4cf88384000302427ca346517b7360000000bc1b5e2000074a6e199b4a91ab880003278a6f800094aa982afc118000017c4000000000018649c3b65036a0e380002a4a033b6aa0001112bea28be0cb89fcc11011a99a0e4400000000001c701f7a1728871e6e8ef26d8608308a69e1eee9518b5a5371172d168fe02a4ad60d6d238e2129004a66000000010f065580000000000c00b1d226889c28ebacb224680002fc8000000000000028a6b07afc40000000753810026d065c000237c0000000abd96e6a830000c44266665680001ea01e60c4ac72b35152edc52abe576a4b800031063260c7e4f6184c1b99680a15a95ecd5b6ea00000d0000349a64a000072c8000df83198a082568cc811466bc0000c0625ac5338bd8957942a0001410d0488309982b0c0002b0e0001fb8ae49a2e000071000000000002ba40002f580000722000000090c26ce24e856a31201a600019e64ebaa94532aea007aabb05b2b690194208c51422709d50000d49b53c66ba0ee218334e0000000000105653ea13a5fb88a8000000042080000001c9800020a6000000000000000000000000000000029d00000000c24b0324d1050653b0eb2b55b2260000150573a2ae1be05420002df42991eb29fe00005a30000ad400de00007f266e00002ed20fa31baa2a7d998f20c986bcaf48b26b5998f6577a7f62c4ad0646b895a2b78b3e9ba0eee00037a40002b742c080007041b0abd58000000000000000000002062a482a5cb6d9b82000000000028ae75580002ce8000ad61ae6000057a0650000c4d8656000360200000003158000000026a2fb8000b94a8b45788
  | 64 => 0xc542914b0680009ae0000000000057f2de87161b5c7f00fde01a273e5a68c5ca4e33ca6f498b213e2d82d5bb6b8a42a5f6c57b75063b2c2a33ea122000029aaa1ad2a5519d46000000091e35020001ba2b4f057864f800000000000001bb0ba623b4df700000000000796230ed6e800000025a07ed0084c81b4fe64e039200025f094f123a776b2e400000007a28000251000062f957e0001d5400023f066b00004278034
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87e87dd5624400f17d0fba2c4880030fdd774589100061e3aee8b122000c3f751d16244001878ea3a2c48801a37a1f73589100062fbaee6b122000c5c75dcd624400193ee9b9ac488003271d373589100062fba8e6b122000c5c751cd624400193ee839ac488003271d07358910006563a6e4b122000ccc73dc962440018e8ebb8ac4880021fe1576549100045fc22eca9220078bc845d952440011bf06bb2a48801a3720d76549100047bc0aeca92200287e87d95524400517d093b684880021fe1576d091001c3e42aeda1220008bf8759342440d353906b26848800aab20964d091001c3f42eeca12200087d85dd942440010ff0abb2848800e1f21576509100045fc22eca1220008df835d9424400d1b906bb284880023be0976509100145e43ac8a122068a9c83591424400555904b2284880063da1b71509100063a32ee2a122000c74651c5424400196ac838a84880027560c71509100043fc2aed992200387c855db324400187ecb3a664880030f19674cc91024656314e99922000c3f655d33244001878caba664880032b9d362cc9100063a32ce399220018f4865c732440018e8cab8e648800e1fa17764c9100043ec2eec992200087f855d932440070f90abb264880022fe11764c91003c5e422ec99220008df835d932440011df04bb2648801e2fa10764c9100045ec20ec9922000a748654e51440678f0e1b2aa28800f1d1db755451019eb8386eaa8a2033c7476d9551440014e90ca92a28800f1d1d9525451000c5fc3ac920a2067a9c83592414405955904b2482880031b1cb655051000656396c8a0a2000c6f65dc941440018d8cbb9282880022fe1d64105103354e41ac820a2026aac8259041440018becb39882880031719673105100062fb2ae620a2000c5c655cc414400f93cc8b9882880032759173105102a43e432eb98a203387f87d9731440010fb0fb2e62880031b1cb654c5100061fb2ee898a2000c3c65dd1314400187eca3a262880030f194744c5103364e318e898a2000c9c74d8d3144001998e5b1a62880031bd97724c5100063632ee498a2000c7865dc131440031e90cbaa62880cf1d1db654c5102a63a3b0ca98a2067cb476dd131440cd968ec3a2628800395d94634c510005cac20c698a2058ce476dc931440ed9c8ec3926288003691d0724c510005cac266498a2000ad4864c9314400187ecb3a062880030f196740c5100061fb2ae818a2000c3c655d031440031df0eb144288166ab21162885102c56641ac510a2000c3f65dd12144001878cbba242880030fd9474485100061e328e890a2026cac621d12144001958e9b1242880063ea1b70485100063c3b6ca9022000c787619520440017c102a124088003d85495148110007e0992629022052aea8688520440678f4edb2e208800f1e9d865c4110
  | 1 => 0xd0810eca880028f61021d95100052f41843b2a2000a5d8308765440674f50010eca8820b1ddd771595100051f420c432a2000a3d8418865440010fd0fb2ac8880031b1cb65591100043f438cab222000c6c7219564440018becbb9ac8880031719773591100062fb28e6b222000c5c651cd64440018decbb92c8880031b197725911001c3f43eeab222000c5f75dcd64440018b8ebb9ac88800317dd473591100062e3a8e6b222000c9f741cd64440051dd0fb92c8880031bdd77259110006363aee4b222000ccf73dc96444001998e7b92c8880031bdd47259110006363a8e4b222000caf741c9644400199ee6392c888003331cc72591100045fc3ac83222000a9c83590644400155904b20c8880028f61365951100043fc2aecaa220008df835d9544400d1b906bb2a8880023be09765511001476412ecaa2200787e87d95544400117f08b96c68801e2f21172d8d100054f42465b1a200087e87d9563440018d8e5b2ac6880021fa1c6558d1000636390cab1a2000c3f65dd16344001878cbba2c6880030fd947458d100061e328e8b1a2000c6f65dc963440018d8cbb92c68800e1fa1f7558d100061fbaee8b1a2000c3c75dd1634400187eea3a2c6880030f1d47458d100064e3a6e6b1a20028ee87dc963440018deebb92c6880031b1d77258d1000657ba6e4b1a2000cac74dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c6880031e1d77058d100061fb2ce831a2000c3c659d0634400187ecaba0c6880030f1957418d100046fc3ac631a2000a9c8458c634400159904b18c6880029760f6594d100063bb2ce329a20018f4865c653440018eecab8ca6880021fe157654d100045fc22eca9a20078bc845d953440011df04bb2a68800a3b2097654d100047dc02eca9a200687e87d95534400d4bd07b2aa68801a2fa1276d0d100043fc2aeda1a200387c855db434400d53906b268688122ab20964d0d100043fc2aed21a200387c855da43440031e90cb8c868800e1fa177650d100043ec2eeca1a200087f855d943440070f90abb286880022fe117650d100046fc1aeca1a20008ef825d943440051d904bb2868801a2f21d6450d100354e41ac8a1a2042aac8259143440010ff0abb0868800e1f2157610d1003c5e422ec21a20068dc835d843440011df04bb0868800a3b2097610d100045ec3ec821a2000c74659c443440031e90cb8886880031d1957110d1003e5a322e221a2006cd4635c4434400117f08b9ec48801e2f21173d89100043f43ecab12200087e8719562441038eee232ac4880030fd9774589100061e32ee8b122000c3f651d16244001878ca3a2c4880032b18874589100062fb2ee6b122000c5c65dcd62440018beca39ac48800317194735891000666310e6b122003
  | 2 => 0x173991200045fc3ac832240018ec865ca54480051f10cb84a8900022fe1176551200046fc1aecaa240068dc835d954480011ef02bb2a8900223d20576551200062ebaea7b1a4000acd82d4f63480010ff0ab8ec69000e1f21571d8d200364e31ae931a4000c9d74d8e63480011bf0eb18c6900063b2197294d200045fc22eca9a40078bc845d953480011bf06bb2a6900023de057654d200447a40aeca9a400687c87595534800d4b906b2aa6900029d2056554d201ee3c382caa9a40028fa86dc1534800d17908bb686900063b21972d0d200346e41aed21a40018ec865ca43480010ff0abb2869000e1f2157650d200047bc0aeca1a40088f4815d9434800d17d0fb22869001e37a1f6350d2000c76432e421a40028f8865c0434807b6d100a9aa4900067aa007154920006f1080e2a9240018ec865d542480013c902baa849000a6ba1e4350920244d743886a124000ba98010d424800139b0638a84900067aa00715092000c76432ea99240018ec865d132480013c902ba264900026b610714c92000cf5400e29924000ae582d4761480011ef0eb08c2900029d21561185200447a40aea30a40088f8865c251480031dd0db92a29000a5b21d525452000c76432e5a0a40269af8750b41480011bf06bb4829001a3720d76905200447c432e120a40028ec821d941480031dd0db92829000a6b21d4250520006563b284a0a4000ba481509414800193ec8b98829001f271917310520006c7212e620a40018ec865c841480111f10cb8082900063b21972cc5200045fc22ed18a40078bc845da31480111f10cb84629001e2fa12764c5200045ec24ec98a40028ec821d931480031dd0db92629000a7321d324c520006663b26498a4006c9c635d0314800193ae9b1862900063b219720c5200447c432e018a40018ee86dd621480031dd0dba442900063ba1b7388520004d7c22e710a40048ed87d86214801117d0faa2c9880030fdd754593100455b40ea8b2620088de87d4d63c40018beeba9ac788022b5a075358f1000c7b40eeca9e200687e87d9553c400d4bd07b2aa7880cf1e1c36554f100445e43ac8a1e20088dc8758d43c40110f90eb2aa5880063d2057650b100445e43ac8a162002aac8259142c4011968e2b22858801b2798d74ccb100064eba2c799620088dc8758d32c40014ef0ca9ca3880cedc201539471000cf8402ea98e2000da4741c931c400172b0999263880029e60252d95100051f420c5b2a2000a3d8418b654400187ae83a6ca8800317dce73d95100051f420e7b2a2000a3d841cf65440018bae639eca880ce9d60473d95100051f420e5b2a2000a3d841cb65440674f500396ca880029e60072d95100051f42465b2a2000a3d848cb65440010fd0e196ca880021f61c32d95100043f43843b2a200587d87087654400147
  | 3 => 0x7b0a80008bd87d0b615000156d03a16c2a009a2fe1d42d85400047bc3ac230a80018be86dd1515000317d0dbac82a019a2f21973105403364e31ae620a8000c9c865cc415000193cc4b9882a000327189731054003e4fb02e620a8007d9b605cc415004d1790cb9082a0003275cf611054000c5e432e998a8006c9c7650f315000317d0dba462a019f2718f748c54000cdd406e918a80028ee829d931500011db053b262a001e2f210764c54000c5f436e898a800799c8750d3150001938eca1a62a00222f212760c5400043fc2aec18a800387c855d831500031790cba062a001b2718d740c5400064eba6c618a800087f855da21500070f90abb442a000237e0d76885400346e41aed10a80018be86dd2215000f179083b242a00062fa1b744854034c5f43884b26600287c8759552cc00d8b8eca9aa59800a2f21176d0b300145ec26eca1660008f7815d942cc0111e902bb285980022fe11729873003c5e422e530e60028ee87dc961cc00195ee9b92c3980032b1d3725873000657ba0e4b0e6000cac741c961cc00d8bceca9ca3980022fe11765473003c5e422eca8e60008ef825d951cc0051d904bb2a39819a2fe1d64d073033c5fc22eca0e60008ef825d941cc0051d904bb283980032b1c9645073003c5e422ec20e60088dd835d841cc0cd93ec8b98839801f2719173107300045fc22ed10e60078bc845da21cc00117f08bb2439801e2f21176487302c477c12ec90e6000c3c651d1654c00f17d0fba2ca980030fdd474595304262fbaee6b2a6000c9c74dcd654c001970e9b82ca980030f5d754d91300054ec1ea9b22600387e87dd5644c001878ebba2c898003171d773591300063c3aee0b2260008bf87590644c0014790ab20c8980028f61365951300043fc2aecaa260008bf845d9544c0011bf06bb2a8980023ee0176551300143f43ecaa926003a5c8654d524c0018b8eca9aa4980021fe1576d093001c3e42aeda1260028bc845db424c00517d0fb2284980023de1d611853001d2e432a728a6000c5e7654e514c0051dd053b282980023b60a76505300446e41cec20a600087f855d8414c0070f90abb082980063721973105300064fb22e620a6007c9c645cc414c0010ff0abb4429800e1f21576885300045fc22ed10a60078bc845da214c00f17d093b242980022f61276485300063a328e2b2a40078be87dd1654800d1bd0fb9aca9000327dd373595200064e3a6e6b2a4000c9f741cd6548001938e839aca9020f1bdd772595200065bba6e2b2a4000cb474dc565480019aee7b8aca90003351cf71595200063bba8e2b2a4000cb7741c56548001968e838aca9000335dcc71595200066a398e2b2a4000c77531c565480018eca038aca900031d14071595200061ebaea9b224000aad82d53644800193ec8b9cc89001f2719
  | 4 => 0x35400f17908b96c6a8002a7a1232d8d500052ec2865b1aa0008df8758c635400153908b18c6a80065ea1f7054d5000c3e432eb21aa000c3d75d9243540030f90cba886a80022fe1173d895003c5e422e7b12a060a788054f62540030f90cbae64a80029d61421d855000578c0043b0aa0008f787584615410d4ef0ab08c2a80022fe11731855003c5e422e630aa054a788054c615400117f08b90c2a801e2f21172185500445e422eda0aa0008df835db415400d1b906bb682a800a3ba0a765055000476c14eca0aa000cac72d9141540030f90cba882a80223e21970105500343e42ced98aa0008bf845db315400f17908bb662a80223720d76cc55000c3e432eb98aa001978805d731540018baebb1e62a801e2fa12764c5500045ec24ec98aa0028ee829d931540011db053b262a819b2718c744c5500064e3a6c698aa000ccc72d8d31540030f90cba862a80223e219700c5500043fc2aed10aa0078be849d9215400117b093b242a801ea7a123258f4001c3f42ee2b1e800087d85dc563d000317d09bb2a7a00022fe197550f4000cdc402eaa1e80428bd86dc943d000517b09b9ac5a00062fa137654b400143e43acaa9680008bf865d542d000136902baa85a01a22f61b7350b403464f31ee6a16800099d831c542d000d17b08bb665a00062fa13764cb40004da40ae899680008bc8750d61d0085958e4a1ac3a000a3ba1f72587402ce563a6e4b0e807acac741c961d00011790ea12c3a000b2b1c942587400055a40a84b0e80018bc845da51d000317908bb2a3a00023be09765474001476412eca8e802caac825da41d000117b0dbac83a019e2fe19739074033e4f31ae720e802c8bf865ca41d000317f0eb0c83a00b2ab209619074000c5e422ed18e80678bf845d931d000317908bb263a00023be09764c74001476412ec98e8007c9c7458d31d0001998e4b1a63a00222f611760c74000c5e422ed10e802c8bf845d921d000317908bb243a01663be0976487400062e328e6b2a8085c3f75dd1655000d1bd0fb9acaa000317dd473595400064fba0e6b2a8000cd873dc165500018baeba9ec6a0002a761353d8d400043fc2ae3b1a800387c855c763500011bf0eb18c6a0002972156318d400052ec1ecb29a80018bc865d2535000187ecaba4a6a01222f21972d0d4000c5e432eaa1a80019b8805d5435000d53d0db1a86a01a72718f7250d403364e318e2a1a80028bc845cf62500050fd0fb2aa4a01a62f21973d094034e4e31ae7a1280018bc865d5425000136902baa84a00026760c71509400345e424ed992800087f855db32500070f90abb664a000a3720d76cc94000c5e432e99928006c9c635d3325000193ae9b1e64a00062f219744c9403464e31ae899280009b4815d132500051bd0fb1a64a00022f61f43d85403345fc3a8
  | 5 => 0x802ad60450d91210045f43861b2242008bd870c3644840147d0a186c8908028f61430d91211655741061b224200aad820c3644840156d02186c890802ad60430d91211645f43c21b2242008bd87843644845955d05086c890802ab60a10d91210045fc3ac832242008bd87994644840153d07328c890802a760e65191210045fc3aca322428aab781594644851356b03300c89089aaba08531912100556c10a63224226aae82d44644840155b05a88c89081e2fa1c50191210045ec38a03224200a9e83140644840153b06280c89089aaba08501912100556c10a03224200ab681140644840156b02280c89081e2fa1c30191210045ec38603224200a3e850c0644840147b0a180c89089aaba08301912100556c10603224200ab6810c0644840156b02180c89081e2fa1e10191210045ec3c203224226aae82840644840155b05080c89081e2f21176951210045fc22ecaa242008ef825d954484011ef02bb2a89080e2fa1f64551210052ec2861b1a4200acd820c363484015ab02186c69081b1718d7598d212c657b14e931a4200c3e75d92634840187aebb24c6908030f9d46498d210061eba8c931a4200c5d75d8e634840117d0fb22c6908022fa1c6458d214465bb88c8b1a4200caf74dc96348401958e9b92c6908032d1d37158d210046fc3ac631a42008bf845da534840f17908bb4a69081a3720d7694d210070fa9ec929a4200e1f53192534840f17d09bb2a6908022f6137654d210045fc22eca9a42078bc845d953484011df04bb2a6908023ee017654d2100c7c402eca9a420687e87d9553484071bd0fb1aa69081a2f21176d0d210045fc22eca1a42008ef825d943484011ef02bb2869081a2fa1f6450d2103c5e422ec21a42588ef825d8434840f968c9388869080a3d2197110d2103e5a322e221a4200e3751d92514844d958e4322a2908032b193725452103e56322e5a0a422ccac72d9141484b3958c9b92829080327d92731052103e4e324e620a4200c9f645cc414840f938c8b98829081b1718d75cc5210061f3aec998a4200c3d75d93314840187cea32662908030f5d464cc52113657390c998a4200c5d75d8f3148401958c8b96629089a2fa1b744c5211645f430e898a42668be87d9131484591790fb2262908b32b1cb644c52133c5f438c898a42078bc87191314844d958e432262908032bd93724c52100656326e498a4258ccc63dc9314840117f0fb2062908022f61f640c52103c5fc38c818a42008bd87190314850f55d0db244290a1f2b9c4648852143f53388c910a42008be87d91604840187eebb22c0908030f1d764581210045f438c8b024200c3f751916048401878ea322c09080327d9373581210064e326e6b024200c9f641cd6048401938c839ac0908022fe1d64191500054e41ac8322a0008bf845cb6
  | 6 => 0x45f43ec8b026200c3f75d91604c401878ebb22c0988032b1cb64581310045f438c8b026200c3f75191604c401878ea322c0988032b1c864581310ec76436e4b026200caf64dc9604c401958c9b92c0988023ba1f625813100637baec4b026200c6c75d89604c40195ee9b12c0988032b1d3625813100477438c4b026200c6f75189604c4018d8ea312c0988032bdd06258131006563a0c4b0262078be87142640c40117b0e284c81881aa7a0c50990310054ec18a13206200aae82142640c40155b04284c818822ada0450990310055ac08a13206200a3e85c82640c40147b0b904c81881e2fa1c20990310045ec384132062078be87842640c40155d05084c818802ab60a10990310445f43ea8b206200c3f75d51640c40d53d07aa2c818802aba08405903100556c1080b206200c3f759d5640c40d53d073aac818802a760e75590310455a40ae4b206206a9e83d49640c40153b07a92c8188028fe1570590310051e42ae0b206206a9c835c1640c40155d04382c818802ab60870590310045f438a0b2062008bd87141640c40d53d06282c818802a760c505903100557410a0b206200aad82141640c41156d02282c818802ad60450590310051f42e40b206200a3d85c81640c40117d0e102c8188022f61c20590310045ec3c20b206200aae82841640c40155b05082c8188222f21d64550310443e43acaa9062088ec87589520c4111e902bb284188222f21d64508310465a38ac8a106200cb564dc5420c401958e4b2282189672b993725043100656b26e4a086200c9f84dd9310c40193909bb2621882335947764c4310064fbb6e89886200c9f761d1310c40153d0eb226218802a721d644c4310464fb8ac89886206e9771591310c40199eedb926218803a3593724c43100667bb0e49886200e8d641c9310c4019aeeca8a62188032bc837458e2100657ba6e4b1c4200cac74dc9638840117f08bb2a71081e2f2117654e210047dc02eca9c42018f8805d9538840d0fd0fb2aa71081a97a0f6554e2103c77c32e5a1c42489ac845cb438840f53908b1c871081a3be197290e210045fc22eca1c42088bc8759143884111b90eb1a871081e2f2117610e210045ec3ec821c4207cb4645c443884053c904b88871096769d097110e2143cd7c3ac9a1442429ad8790f428845f1df0cb8e85109232b98674cca21246d330ce999442238ef865c7328850f35d0fa1283108bf2bddb425062111e67bb66498c420387e87dd5608840f17d0fba2ca908032b1d372595210065a3a6e2b2a4200c3d75d53644840155b04206c890802a7a0e65d91210054ec1ccbb224200c3d751d7644845955d05386c890802ab60a70d91210045f438a1b2242008bd87143644840153d06286c890802a760c50d912116557410a1b224200aad82143644840156d02286c89
  | 7 => 0xbe87d91544c4cdc38a6322a69881f2d19271d0d3103d4f436c921a6200c9e76d92434c40196ec838a8698803391887150d31034cec26e4a1a6266d97741c5434c4018daeba96c4988021fe1570d893101c3e42ae1b126200aae84997624c40155b0932ec498802abe1165d893100556422cbb126200aeb80597624c4015d100b2ec498803a360c64d89310074632487b126200aae84983624c40155b09306c498962b960775d893100636ba8ebb126200acd831d3624c401c5ea92a6c4989639394f53d893100557424e1b126200aad849c3624c4014df0ab86c4988029b21570d893100573408e1b126258ae5811c3624c4011dd0e286c4988023b61c50d893100557420a1b126200aad84143624c4b159d06286c498802b360c50d893100573408a1b126200ae581143624c4011dd0e206c4988023b61c40d893100476c3c21b126200aae84843624c40155b09086c4988032b18b745893100656310e8b1262008be87d91624c40117d0e322c4988023b61e651893100557424ca3126200aad84994624c40159b07328c4988023be1d651893100557c22ca3126200aac84594624c4015d700b28c498802ba2016518931006573b6c83126200e2e75d90624c401c5aebb20c498803a35cf641893100476c3cc83126200aae84990624c4011df0eb20c498802b9e05641893100557430c83126200cae76190624c401c5cea320c4988038b5d4641893100746c18c83126200e8d73190624c519d4e62320c498a33a90c4641893100746324863126200aae84980624c40155b09300c49881e2fa1376549310045ec26eca92620287c87595524c47b4f100b2aa49880e3ba1f62549310347b436e2a926200cb464dc5524c401968c838aa49880339d8871549310145e422eda12628b99d8790f424c4b199ce7b16849880a2fa1f64509310064e3b486a126277d8c625d3324c40d93ec2ba6649881b65d8574cc931004cfc3ec99926200e8c62d93324c40133b0e3266498803a318864cc93101567436c59926200cce76d8b324c401b1ae9b1664988032d193714c9310065a320e29926200ce7621c5324c4111b90cba26498803271db644c9310064e3b0c8992621dccc76d89324c4edb8ee438a649881a1fe1d659453119d3c402cb28a6200e3751d92514c401ccea3b14a29880317d9773545310454e43287a0a6266c9e7690e414c4051d904bb2829899f271cf645053100656396c8a0a620899c8750d414c4115390ca1a82989df631c94350531045ca40a86a0a62768ee86dc9414c40195ec9b9282989672b19372505313d47743ec4a0a6267c9e73d90414c40193ec8b98829881f27191731053100666312e620a620099d8790c414c4cf93ced2188298963339cf621053100666b9ec420a6207ab486504414c4f3d48c4a08829880267e11728c5310
  | 8 => 0xc8b98839899e2fe1d64d0e3103c5f43ee8b1462008bf845d9528c40f17908bb2a5188223d2057654a310443e43acaa9462008bf87593428c40117f08bb285188222f21d6450a310054fc22c598c62078be87dd1654c4051dd0fb92ca988032bdd37259531006563a6e4b2a6200caf741c9654c401958e8392ca988063ea1f70595310065dba6e0b2a6200cb874dc1654c4019d6e5b82ca988033a1cb70595310063dba8e0b2a6200cbb741c1654c401970e8382ca988033adc8705953100674390e0b2a6200c3d75d53644c40155d04206c898802ab60840d913100557414cbb226200aad82997644c40155f04b2ec898802ab20965d91310055dc02cbb226200ab880597644c40147d0a316c8988028f61462d913100557414c1b226200aad82983644c40187aea3aec89899f8794f53d91310051f428e5b226200a3d851cb644c4cf53d06396c898802a760c72d91310045ec3c65b2262008be87087644c40117b0e10ec8988028fa1421d91310051ec2843b226267a9e83087644c4015750010ec898802ae60021d913100557414e1b226200aad829c3644c40156d02386c89899ead60470d91310045f438a1b2262008bd87143644c4cf53d06286c898802a760c50d913100557410a1b226200aad82143644c40156d02286c898802ad60450d91310051f42e41b226200a3d85c83644c40117d0e106c8988022f61c20d91310045ec3c21b226200aae82843644c40155b05086c8988032b9cb649913100657b22e53226207cac645ca644c40195ee9b92c8988032bdd0725913100672396e2b2262008bf87590644c40155f04b20c898802ab20964191310045ec3cca3226200aae82994644c40155b05328c8988022fe1d651913100557c12ca3226200aac82594644c40157700b28c898802ae20165191310051f428c43226200a3d85188644c40155d05300c898802ab60a60191313370f29ea63226266a9e83148644c40153b06290c8988022f61e32191313354f41ea23226200a9d83d44644c40f17d0e108c8988022f61c21191310051f428423226200a3d85084644c4cd53d06108c898802aea0021191310055cc004232262078be87140644c40117b0e280c89899aa7a0c50191310054ec18a03226200aae82140644c40155b04280c898802ada0450191310055ac08a03226200a3e85c80644c40147b0b900c89899aa7a0f20191310054ec1e403226200ab681880644c40156b03100c89881e2fa1c20191310045ec384032262008bd87840644c40155d05080c898802ab60a101913103c5e422ed2a262008ef825da544c4051d904bb4a89882237219739513103e5a324e32a262068f4865c6544c4051dd05bb2a8988023b60b76551310045fc22ecaa262008ef825d9544c4051d904bb2a8988023ee01765513100c7c402ecaa262038
  | 9 => 0x2058c4103d4f42420b188200a9d84841631040159d05082c620802b360a1058c410047dc02eca9882018f8805d953104111b90eb1aa62080327dd16354c4103e4e3a2c6a988207c9e835da431040f93b06bb48620803279c96390c413364e392c72188200c9d635c6431040193ac6b84862089a2fa1e43588410447a40aeca90820887c87595521040f878e8b2aa4208231d1c565548410064fba2c6a908207c9c7458d52104119a8e2b1aa4208223b21d62548410066ab1ee2a908206c9e635d3321040f93ce8b1e6420803275d163cc8410045ec36e899082088dc8758d321040193ee8b1a642081f271d1634c8410466a38ac69908200cd563dc5321041196ca3bb2822099a2f21d63504413364e39ac6a088200cac7258d41104019390eb1a8220803279c963504410064e392c6a088200c8c7258d411040fd2ee2b1a8220a1e6ba1f725044100657bb6e4a088200e8d63dc9411040195eec3928220803a358c72504411345e43ac4a088226cac72589411041156902b1282208032ddd951504410064eb1ee0a088200c3f749d165cc40d4bd073a2cb988028fa1272597310051ec24e4b2e6206a5e839c965cc4014bb07392cb988029ea0272597310053cc04e4b2e6206a5e8390965cc4014bb07212cb988028fe1171597310051e422e2b2e6200a6f825c565cc4014d904b8acb988029ee0171597310053c402e2b2e622487e8708565cc4010fb0e10acb988028fa1021597310051ec2042b2e6206a5e8308565cc4014bb0610acb988029ea0021597310053cc0042b2e6200a3f845c165cc40147908b82cb9881a9720d70597310051f420e0b2e6200a3d841c165cc40d4bd06382cb988929760c705973100537410e0b2e6200a6d821c165cc4494ed02382cb988029d60470597310063cb80e0b2e6206a5e8310165cc4014bb06202cb988029ba08405973100536c1080b2e620087e87c8165cc4010fb0f902cb988028fa1020597310051ec2040b2e6206a5e8308165cc4014bb06102cb988028fa1210597310051ec2420b2e6206a5e8384165cc4014bb07082cb988029ba0a105973100536c1420b2e62698be8710964cc40d0ff0eb2ca9988028fe1165953310062eb2ae72a6620687c8759554cc4070fd0bb82c5988021f6177058b310143e43acaa9662028bc845db42cc40d8bce6b2e85988031759573d0b310145ec26eca1662088de83dd942cc4018eccbb8a85988031d9947150b310065bb20e2a1662009d5831c542cc401b2c8638a859882275205744cb310062eb2ee6a8e62668bf8759341cc4cd33f0ea1e839881b171cd655073100636392caa0e6200cac7259141cc4018bacbb9a83989e3631c943507310063732ee4a0e6200c6d65dc941cc40d8bce6b2883988031799573107310062eb2ae620e6266c9f645cc41cc40f938
  | 10 => 0x3128200e8f6350c625040155b09300c4a0802b9606601894101c7743ec4a92822ccac629db42504d31790cb9e84a090b2b18973d094101557436c5a128200cae76d8b42504019cec438a84a08022fa1b735094124656316e6a128202aae86d894250453958edb1284a09eb69dc87150941004db430e2a128208cb6861c54250411b2d0638a84a08236560c71509410065a318e2a128200da7621c5425051bb48c438a84a0a3769c80715094121656312e99928259cae74d8b32504111790cba264a090b2b189744c941044da40ae89928200e6751d8a515040187ecbba2a2a08032b18b745454103c5e432e720a8267c9c635ce4150401958c4b9c82a081e2f219729054116656312e520a8287aae86d8a4150405958e4a16c0a0802ad20542d814114c76436e4b0282008ee87d8960504018deebb12c0a08031b1d7625814100667b9ec4b028200ccc73d8960504011dd0e312c0a08031bdd46258141006363a8c4b028200ccf731896050401998e6312c0a081a37a1c5098c410046ec38a13188207a9e84142631040153b08284c620802b3a085098c4100566c10a13188208ad68114263104015ab02284c62080297a172098c410052ec2e413188207a9e84082631040153b08104c62081ea7a121098c410054ec24213188200ace82842631040159b05084c62080317dd75358c4103d4f426a6b1882668be8790963104cd53d07212c62081ea7a123258c410052f42864b188200a5d850c9631040f53908192c62081ea7a123058c410052f42860b188200a5d850c1631040f53d08182c620802b3a083058c4100566c1060b188208ad6810c163104018beeb3aac62081ea7a127558c410054ec24eab188207a9c845d563104015b700baac620802b62017558c4103d4f426e4b188207a9e849c9631040153b09392c62081ea72117258c410456a40ae4b188200a5e851c963104014bb0a392c62081ea72107258c4103d4f426a4b188200a9d84d49631040153d0f212c62081ea7a0a4258c4103f4741484b188200e8f729096310401d18e5212c620802a76064258c410054ec0484b188207a9c84c85631040f53909b82c62081ea7a127058c410054ec24e0b188200a5f855c163104014b90ab82c62081ea72117058c410052f428e0b188200a5d851c1631040f53d08382c620802a76107058c4100567410e0b188200acd821c163104115ad02382c620802b56047058c4103d4f424a0b188200a9d8494163104011bd0e282c6208023761c5058c4103d4f420a0b188200a9d84141631040159d04282c620802b36085058c410456b408a0b188200ad58114163104014bd0b902c620802976172058c4103d4e42640b188200e8e42c81631040f53d09102c620802a76122058c410456b40c40b188200ad581881631040f53d08102c620802a7610
  | 11 => 0x4c8031d904b8ec099002ab60840592510052ec2860b1ca200a9d840c1639440159b04182c728822b5a043058e510352fc32c6a9ca21e87d86dc5539440d8bcc6bac87288222f21d6450a5101556412c8a14a206c5e635d7329440d93cc6ba66528803275d163cca510446e43ac6994a200a3d8590b645440117f0eb20c8a8802ab20964191510045fc22e5b1aa2078bc845cb63544011bf0eb18c6a88023be097610d5101476412ec21aa2008bf845cf625440f17908b9ec4a880a1f21570d895100656310e8b12a248cac629d3325440195ce9b1664a881a9720d6554f412145ec36e4a1e8242cae62dc943d04070fd0bb82c5a08021f6177058b413445ec36e6a168207cae7458b32d041117d09bb265a08226d205744cb41004dac20e29968206c9c7350d60d040117d0f212c72099ea7a0e4258e4133c5f43884b1c8267a9e83109639040f96cc2bb087208b26b2097110e410045f43c86b14822c8be8710d62904110f90eb2aa5208030f5977454a410467238ac4a148206c9e635d3329040193ae8b1e65208223721d634ca4133c5fc3ac7a0c8267c9e7358f419045917f0eb1683208b32b9c962d06410147743ee4b2a8200caf741c965504019c8e5b8acaa08033918871551410052ec2861b1a8200a9d840c363504015ab02186c6a081b1718d7598d410062ebaec731a82008df8758c635040d1b906bb4a6a08023be097694d4101476412ed29a8200cac625d253504019c8c538ca6a0803391897194d4101477416eca9a82008ed82dd953504071bd0fb1aa6a09222f21972d0d4124656312e5a1a8200ce4621c5435040117d0db9286a090b2b18b7250d4100752316e2a1a8200ea4621c543504018daeba96c4a08021fe1570d894101c3e42ae1b128200ace83997625040159b0732ec4a0a1f2b9db74d89410053742cc7b128200a6d8598f625040155d0da1ec4a090b2b9d943d894100636ba8ebb128259e2e54d5362504014dd0b39ec4a08029b61673d894100557c22e7b128229aac845cf625040155b0839ec4a080393d4e53d894114d57424e1b128200aad849c362504014df0ab86c4a08029b21570d894100477438a1b1282008ed8714362504b355d08286c4a0802ab61050d894100567418a1b128200acd8314362504015cd02286c4a0802b960450d89410047743861b1282008ed870c362504014dd0a186c4a08029b61430d89412cd5742061b128200aad840c362504015cd02186c4a0802b960430d894100476c3c21b128259aae84843625040155b09086c4a08023b61e651894100556c24ca3128200ace83994625040159b07328c4a08023be1d651894100573c0aca31282008ed8798c62504014dd0b318c4a08029b616631894100477c3ac63128200ae78158c625049155d08318c4a0802aba1b431894143d5743286
  | 12 => 0x80a3ba1f72584432ce563a6e4b088659ea441dc96110cf5958e8392c2219eba9104725844303d5b426a2b088606ad683d456110c0155b04206c8a90022fe1d64191520055a40ac8322a400a5d850c3635480159b04186c6a900237e1d6318d520352f436c6a9aa4068bc845db43548011ef02bb686a90223d20576d0d5203c76432e5a1aa40287c865d6435480d1d90cb9486a900a1f2197510d520055b42421b0aa4008f787584615480156908b08c2a90031e14170185520055b4242030aa400ae582840615480117f08b8ec0a901e2f21171d81520052ec2860b1e8407a9e840c163d080159b04182c7a1002b56043058f420145e422eca9e84008fb805d953d08031f100bb2a7a101e3721d6354f420055ac0c8730e8491c3f75dd1655080196ee838acaa100339dc8715954200673900e2b2a8490c9d74d8e63508011bf0eb18c6a100a2fa1b7454d421345e432e321a84029ac825c443508018eaeba8ec2a10023de1d611854247d5bc22c230a8400c9f845cc615080193908b98c2a100333e09731854200666412e630a8400c9e425cc615080193884b98c2a102327d0573185420464ea0ae630a8400ccf205cc61508119ae20b98c2a10022f61e43185420064eb9c8630a8400c9d7310c615080156b02218c2a1122aba0b519933200556c16a332664078be8714264cc80117b0e284c99901aa7a0c50993320054ec18a13266448aae8214264cc80155b04284c999002ada0450993320055ac08a132664078be8784264cc80117b0f084c999122aba0a109933200556c142132664068be87d5164cc80187eebaa2c99901aa7a0f545933200556c1080b266400c3f759d564cc80d53d073aac999002a760e75593320354f41ce2b266400aaf825c564cc80d53d0638ac99901aa7a0c51593320054ec18a2b266400a3f855c164cc8014790ab82c99901aa720d705933221557410e0b266400aad821c164cc80117d0e282c9990022f61c50593320354f418a0b266400a9d8314164cc88555d04282c999002ab60850593320055b408a0b266400ab58114164cc80117d0f082c9990022f61e10593322155741420b266400aad8284164cc80d53d06082c999002a760c10593320345e43ac8aa66400ae582d4561cc80f17d09b8ac1990022f61371583324762fbaee6b2a6400cb7741c5644c8019cee438ac8990233560c71591320065b218e2b226400cb4431c5644c80196c8438ac8990032d108715913200673900e2b2264008bf87590644c80156902b20c8990023de0576551320447a40aecaa264008fb805d9544c8031f100bb2a8991a22f61f64d0d320047bc3ac230a6400ab484584614c80195f04ba0c2990032b20974185320465a40ae830a6408c9f315d0614c81193a62ba0c2990032bc8174185320045fc22e3b0264078bc845c760
  | 13 => 0x801c0280180ac17800000c01c0000600ac04808400000002c00000001801401001c00800407404c01801406004002400801400005000400400400001c0040180180000000400840100100040540180480c00240d800c01801400000005003c02001000c00005002001400800800808404801400000400006003000402400800800001001000000400401c01800000800400c11c00006813801401407404800002c04001400400001c00000805800006c09402804c0440c401405002400c1b400000c00004001c00000000000001407c0100000e80040ec00001401800400004400c00800005c0000000a80a001400003400405802404c03003000000001401805800000001400000000c00801004800c00c05401c03400000000400400403800000000401c02000400000000000c0000780200d407800c0000040140080400080081c40600b401002402404c00004c00003401800800000000c02c0200100b404800002401000803005400000400405003001001400801000001c00400407c00405c09000c02800800c00400800c00c00005400c03800c00403801000401401400006400801c04002000c0340b805000000000004010801000406800408c00400001400c02400002400405402810001c00404801406401401405c00000001402000c0a000002404c00c02800003800800002401800005400001c04008800c0140240340140040240400ec00800000000800403c00000000400011403c00002000800400002801404c02402801007c02401c02800001000c01800c07c0c400000800000402007400809006c0000000a400c00004c000000018000004014bb0a186c6aa002a761030d8d540046fc3ac631aa800ad88058c63550019c8c438ac4aa0029d61421d85540055ac2043b0aa8008f78758461550015c904b08c2aa0023be0971d815401476412e3b02a800cd8601cd605500117f08b94c32981e2f21172986530053ac2842b0ca600ab5840856194c0d5ad0610ac329802bc60021586530051ec2c81b22a600aad821036454c0117f0eb20c8a9802ae20164191530047bc3ac230aa6008bf845c76054c0f17908b8ec0a98023be0971d815301476412e3b02a600cb8601d16054c051dd05b8ac1a18023b60b71583430362e39acaaa486028ee82dc56090c011db05b8ac1218028f61250d95430063cb84a1b2a86018fa87dc16550c018f6ea382caa18032edd070595430066db98e0b2a8600c5f65dcd5450c0187ecbba2a6a18021fe1570d894301c3e42ae1b128600ce4621c56250c0156b0810ec2a1802b560c21d85430047bc3ac230a8600ae4825846150c0117b0f210c2a181f275ce421854343f521088430a860087f855c06150c070f90ab80c2a18023be0971d814301476412e3b028600c7975d436050c111e902bacc221
  | 14 => 0x32ea7e24cb0824b0001a280024f80a17291800010bb810001f685939f2943059caa989a18a1aca11d8df30489aaf09272bf959a1939216633e16f09e94c868abd00e95bad6a0a37822238b1bf077aa399382c83c3338001f21fa38d9149c9a2d33480039e341ae3098ae3a652f6ac705f31291212e8000198000000002778122791c20f21df1ff1628fab2a264a65b7589094aa24227215b598548e19370018a88481478470bda2623c9cd29380014494f93b8d182439aaa496b8a0301a23a1391c9c688fa352d138617d2c00f12ac88617f8003488002fb00d2aa2deaafa46a718eb18121ead3b72083a1d0a72a78690eba5390b2c38d314a02d35d8c989d138b5e1d482a17b0420001d9ac6b29a88a86160262260051a1aa8f1a099630a84989f9172b185085d3468da9c8a10b19945ad88002360220d88dd8d699713f28aa86a5c29921b8c38ad3179ac9d6a3d22cacdaa2214822ad09630723841980edb9ba9284d9302b7a7738ba7f29e1ae8c82b517a2c331f9ec005b65a100553800c292fb461a7b5804022fa3397a87b0201820beb7087f33b0aab4d3979cf0f38abb6cb25a31062aec00000033f14eb71b230000f6a79a4081302a9f8ae10888002ccaf922a989a43aef0dd2d1ab1289072b311381299f112283caed06839c1ad30d01523a8a085a2a180712bae230993280380021a095b050aea9a8098000000002f28000002d41f58598002e194211c1c12d51cb00037280031231f0ba0d40a3064084112a9000020eb9fb282fd00000805a8f1b49b4205c23190380030d9fe0002c180035a00000038480000000016d00000015037719c074a8f88680000000020b19d00025bb1d17c0f0ba218b1840001068001f50e5ae50d22d90e0992ab221c9a5085a2103117496c9a6137b2f9112c60de07c254b9080e03094db4584bb1e159010330b551740808289e80ed280ae91aa253351a41323931805000000c01000014c02000402800004c04800000000002800400000002400000000c00008c1000040280000a400401801005c06811400407001402802c00800000c0040000c801000000000c00400801800400c01400c01c04c0180080080100500000240140300140080e401400400002000007805408817c0000140240840000640380440300b400014003000806c06400800c0000080380200000040180000080c400000401000002000005800001400008006006802803000001402c06400800001801406401c00c0040200100000080300a401000000801802800002c01401400c00c0c407002402004c02c0680040a400007801800401000808409c0000f80000100080040d003805400000801014007c00805c02c07000400008802801000000802800000002808001c00000800000401800c06400402c00c0040200240100000100
  | 15 => 0x4180000033515c04aaf8b7faed84eb509b60b119490a1491852572de00000f8000000e9897b390530000002e99d6235a009c43681838ce0873712379089c3853ad587512195a0c185bb4488d23f0b20f799b10309121d8c518e27ca9b9a21000fd18099a83b11b8878c09c508b11a849000396b942681279ca21b00031697080000032c8442cf2ce18e80016d8000003481be00030f0003700af86aa611bc9048b8b0e067a482042431c722e9e1a28a400f50cf832a57aaf33a24da002d49c32b801e8cc2aab359ac0000601d88d1361aa2b7e80015f01f38e8f998815887382eb5b93cb991230001fdad31b09ecb270bf0c90f5a172bb04d0513698a607107e8d814b0b09d027ab14858a05a8203480006d28c00000027d80000027433c80016f80000009680001c80000000008291500000010c1f000023fae709e1ee18900003eaf10000001a303d939b4f2448a40003370cc9f62a92d70000000000002f2101a5e807a160000000001ab966ae5b868000000002e60000b822932080000039816428438f37300017ba74b0e8000001eb15c8000000a52dca9c0ecb15b9704504cb7f1761fa80020b8002828010000000000001051f82a129d00007699eb073478ada3d86b03a00025a8a208100010d00000031b9e30002bdb5d219b9581a209aff8002d9b7d32e00017c8bc18c0002fe08a2a512c2443228ec00011d0000000002231998000fb8bca3a0c2000176a8d8d0879b24150b7b216a3400012b332aae997a7ea0ab2f13b06f1d4273b090762b9a091ea23e36c13c23921886a1a011b3880a3aa60c42968d0203afda91b269060000b704619c9d71a42bea7d0009a399186fb542e4b6e38e06e00033aa2c3823641c80000000430000000c59db00037e0180e7a6b34e31c9b3a2db6da1130b1091f2a22b02000260aa8b891c1b630622c222e17792c8212a72f1acc3160d6000027940b030000000941f98a59ceaad9a4b5ab6a1f417e2510fb31a0002cd1e78002f7321a0c9d20002c98001b40002db1df80280500029f195380abc8e23900000780730000318000002b68000000e91438f42f7a1f16a2eea3803785e9f480029b0002a6a331ddadd93e1ae1fc9968000000001078000002bb87e0000001c28000a82f49b281b03e2b387426b8e381103839303887701f8000aa00034c84c0ff80001b8002dc00000011e800000000179185a769239e63668e00dea8808e12823c0001161e206513a2278918000002ff39db8d3620e72178d39e907a26da598409dc18aa04b1e8000002c8306b8faef9e5b3803ba3b9b49b926fa020569332a08c700001380010a91884f9e2b9a0000002671efa5c90400000025a00035126194700036d000000347014b25000000151b8c15da67a703182c59348000299fc0f8ae797309db008609b9aabb64800
  | 16 => 0x437db57a872b410228e9a12a01102d2878855881b1180c839a4a33623e8bfb68986a62ab327ba200e296b1cc21f8b18da0238d707929722b1c6270a800f80272db9fbb3c2fb93e9562132bab2225882f18b9e89c91b130600000033fb332492e29b239e80000000000026637518737a14111f80000003d0001a7113a4ea5e26a21c0170e62f58dc00c297a8b24c153b36a4500000000000028ca69b872e68c6398935835000367ad62e89b6acf9679720000ca9d82419719818ee2849b52950449b780000014194e2d790e8390881a906610da218efa30b40a5f9fd1b31a8125945182865b039d5800099abf00008c03014332c3910000000a68b380b2c08a7a282639932558d494ba6d19238c957ab28c4965a5806980027c1bb8ea8a12011d5358b81b79b5590125f29e81696e81889c83aaa80e31f92c8b5ca1e1ef1f79c0b76056014146a06105a8516e36f0a498313098a32d36bad81710410363768330129f31b8ab099a0322ea27a109aac1531773a28368000960e100000aa528000000d29ee9da89b80033210e2479c48001b735492aa0d83f98788a81c1b82b60bb01e0373a11ea86b8000000000002c2a0537c8001bb25180005b1c78d7aa98001e515e1cdb3da92000140387ac102c12d0000000000ab1f700022f043900aa5b613520000d5b07934120800057a2b96a8190000fda75800061811a5400026ea268000000000000000478001af8000000000000000218000000e828199100025b12900015eb9480000000002da9d8001752783170341759540b59e685c826ad01fe8852b8b290cf0e51991ffb431ed000232ba00001862249dbb539362da23988f0f70833429223828bb81db6fa6c024a9834a8002508000003832df87aa4987b8fa139289a08b44377a422ec8ef04a12e2fa8ca2a40040d51cb87f829236ace94d1b598f9a69178db3300ea0f29d1a429168f30e4b63a569d38f4b5290f97d8b79d2aeab9cb4f88db600a2911ae80a9095195817b5915721830134b0c32f024e37880635038aa551e41322fcacb8000001c00002488583192b4b92a9a0003132b909800011e3a1800000385360800000357269318a562eb8002fe8e8a721f0aba02b12112630b80000005f8003490260002e4020a689bd00034029490f2878cb82596c2f63200282071529de9a58ba871815a3b3211a9af818c9e480000018d806acb1f1b6b0000030000e6af52152b5a1186db650092831ba0002031511c5a4bac513d800220b998cd9988000001e739b19fb6726f28a000004a8d0f90990dc95494980012d924864af3b858002789e00f02858b68db80000000000000016880000000000f0b60429639ba9fb2ad0003918000900b304588480000005700016700033b80031098014f02f8000001e085db0f9690001eb87c8e40000528002da8
  | 17 => 0x1ce08e9080cb34129609320e2750800d93260001cfb953101bc2e012400ba4d1f3a95a069aa8acadd34a0af299ba0969914252142973a669581780ac0898ff33793130c308893936aa31e9808abe1649dd3791d7aee0488001d325d26336924580013d0000002029d08000c000009a246201a4f00000000029f9131de2c9119ac425db0019027f80035b107126b5c33429106cb6e9849cc90c80000000000d82523882e19da711af00020800014615b0000b4afc00000000037b800000110aae00024ab1da2595584b0c1283b0a1bea6400019e0001bf80032bb93b1b33d0002590b0070a0d2df1798001bd89f01d30c8b53898668ceb2484e34eb2b19f35e8c692a1159b18d98ae035b62b6a85e12518f20c0a9a8b8822811608b9229833b73b4dabc0001488c88003438000000fc95a80017f04f1ab0b98000000b280000007d00015f80000000029307d9888000000fea34800000133b7c31100000026ab8395217003f0000920000003142e08002fa2730f62ab135331902875b3895526c97e8fe30436600000019b91f08905233e80000013f8230972d22250b434520796526e09c05001ab7a8638002470cd27602b93a962374af416821219098d1b01e11a880001094c23231c1613278002128001190673562cab5315d0fc30292888c92f23709b2b71480928ee9e3ab023034c0469942c79da356816156863290a7b0dfb1ab2a9dc9d10bd25039606eb742f327292000000200000000000008bac4b289789ed80011a00020fb5f34b85407039d0c780006c32d80033980029c800388b150be20f38a1d9161b5f8001ad80000028e00014431386122a2eb2f9894a1
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1800700000000a14b1a40004042c00700ca08000040145993141701855200525644425cc615090f8a481209741853243e23a1d63dc941104011959890c7150b310062361c62193324c40189463205744c94033427a62625cc41500014559314071595200061c1c081595534800105f985cc73d95100052524d641c542440cd09c98591731051000523249645cc41440013c1932054248110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x6
  | 4 => 0x94b
  | 5 => 0x94e
  | 6 => 0x4
  | 7 => 0x5
  | 8 => 0x2
  | 9 => 0x138b
  | 10 => 0x138e
  | 11 => 0x98e
  | 12 => 0x9cb
  | 13 => 0x9ce
  | 14 => 0x168b
  | 15 => 0x168e
  | 16 => 0xa0b
  | 17 => 0xa0e
  | 18 => 0x180b
  | 19 => 0x180e
  | 20 => 0xa4b
  | 21 => 0xb09
  | 22 => 0xb0e
  | 23 => 0x1409
  | 24 => 0x140e
  | 25 => 0x249
  | 26 => 0x24b
  | 27 => 0x24e
  | 28 => 0xb49
  | 29 => 0xb4b
  | 30 => 0xb4e
  | 31 => 0x1449
  | 32 => 0x144b
  | 33 => 0x144e
  | 34 => 0x16c9
  | 35 => 0x16cb
  | 36 => 0x16ce
  | 37 => 0x289
  | 38 => 0x28b
  | 39 => 0x28e
  | 40 => 0xb89
  | 41 => 0xb8b
  | 42 => 0xb8e
  | 43 => 0x1489
  | 44 => 0x148b
  | 45 => 0x148e
  | 46 => 0x1849
  | 47 => 0x184b
  | 48 => 0x184e
  | 49 => 0xbc9
  | 50 => 0xbcb
  | 51 => 0x14c9
  | 52 => 0x14cb
  | 53 => 0xcc9
  | 54 => 0xcce
  | 55 => 0x1709
  | 56 => 0x170e
  | 57 => 0xd09
  | 58 => 0xd0e
  | 59 => 0x1889
  | 60 => 0x188e
  | 61 => 0xd49
  | 62 => 0x589
  | 63 => 0x58b
  | 64 => 0x58e
  | 65 => 0xe89
  | 66 => 0xe8b
  | 67 => 0xe8e
  | 68 => 0x1789
  | 69 => 0x178b
  | 70 => 0x178e
  | 71 => 0x18c9
  | 72 => 0x18cb
  | 73 => 0x18ce
  | 74 => 0xec9
  | 75 => 0xecb
  | 76 => 0x17c9
  | 77 => 0x17cb
  | 78 => 0x1049
  | 79 => 0x104b
  | 80 => 0x1949
  | 81 => 0x194b
  | 82 => 0x209
  | 83 => 0x124e
  | 84 => 0x2c9
  | 85 => 0x1549
  | 86 => 0x19c9
  | 87 => 0x4e
  | 88 => 0x140c
  | 89 => 0x140d
  | 90 => 0x4b
  | 91 => 0x124b
  | 92 => 0x15c9
  | 93 => 0x12cb
  | 94 => 0x1609
  | 95 => 0x130b
  | 96 => 0x1a09
  | 97 => 0x1649
  | 98 => 0x198b
  | 99 => 0x134b
  | 100 => 0x5c9
  | 101 => 0x1a49
  | 102 => 0x28c
  | 103 => 0x148c
  | 104 => 0xd0c
  | 105 => 0x188c
  | 106 => 0xce
  | 107 => 0x409
  | 108 => 0x749
  | 109 => 0x1a89
  | 110 => 0x10b
  | 111 => 0x10e
  | 112 => 0x150e
  | 113 => 0x128e
  | 114 => 0x12ce
  | 115 => 0x130e
  | 116 => 0x2cb
  | 117 => 0x19cb
  | 118 => 0x20c
  | 119 => 0xe8b53
  | 120 => 0xe96d3
  | 121 => 0xb8293
  | 122 => 0x20d
  | 123 => 0x154e
  | 124 => 0x1a4b
  | 125 => 0x1a8b
  | 126 => 0x20e
  | 127 => 0x15ce
  | 128 => 0x160e
  | 129 => 0x2d551
  | 130 => 0x19d4d1
  | 131 => 0x1a1651
  | 132 => 0x1a57d1
  | 133 => 0x1a9951
  | 134 => 0x2d4d1
  | 135 => 0x40a
  | 136 => 0x296d3
  | 137 => 0x28953
  | 138 => 0x299d3
  | 139 => 0xb4e93
  | 140 => 0x28214
  | 141 => 0x28b93
  | 142 => 0x1a57d3
  | 143 => 0x29493
  | 144 => 0x18ce93
  | 145 => 0x1a9953
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2637
  | 6 => 7201
  | 5 => 1862
  | 4 => 15
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
  | 7 => packedAt gbK7 (108117+((h/879+packedAt gbK7 (97569+(h % 879)*12) 12) % 3481)*13) 13
  | 6 => packedAt gbK6 (379248+((h/2400+packedAt gbK6 (345648+(h % 2400)*14) 14) % 10456)*14) 14
  | 5 => packedAt gbK5 (117298+((h/620+packedAt gbK5 (109858+(h % 620)*12) 12) % 2235)*12) 12
  | 4 => packedAt gbK4 (1075+((h/5+packedAt gbK4 (1050+(h % 5)*5) 5) % 30)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffc1f00ffff03fe0fffff80016344fd1e73fc
  | 1 => 0x700fe000f81ffffff07807ffc69cbb3213fccf
  | 2 => 0x800fffff001ffc1fff8007fff8e0c3c3e38f0f
  | 3 => 0xfffffffe0001ffffff8003f00fc03fc0ff0
  | 4 => 0xfffffffffffe0000000003fff0003fff000
  | 5 => 0xfff0000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x90e4050829272126048934818021005506315c
  | 1 => 0x2128a0105a09464a9050512a820c193210d4c5
  | 2 => 0x2454b690112a9152d00a65518e0c2c1630b0a
  | 3 => 0x40a72b296404219ca66c0062f00ec02b80ea0
  | 4 => 0x88f9cdce79cf3808443041837f70003dfe000
  | 5 => 0x4f0000e004008001080400603ddaf7a8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeeeeeafac8eac0feeeeeeafac8eac0feeeeeeafac8eac0feeeeeeafac8eac0feeeeeeafac8eac0feeeeeeafac8eac0feeeeeeafac8eac0feeeeeeafac8eac0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37223
namespace PEqualNP.Outside.L_meta_37223
open PEqualNP.Outside.L_meta_37223.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 6 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 25 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 90 := (concat bs2_4_0 (concat bs2_4_32 bs2_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 44 := (concat bs2_5_0 bs2_5_32)
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
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 64 := (concat bs5_4_0 bs5_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 40 := (concat bs5_5_0 bs5_5_32)
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 15 := bgb_4_0
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
theorem bgb_5_1856 : Interval gbAtlas 5 1856 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1862 := (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)) (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 bgb_5_416)))) (concat (concat (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)) (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640))) (concat (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768)) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 bgb_5_896))))) (concat (concat (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 bgb_5_1120))) (concat (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)) (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 bgb_5_1376)))) (concat (concat (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)) (concat (concat bgb_5_1504 bgb_5_1536) (concat bgb_5_1568 bgb_5_1600))) (concat (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 bgb_5_1728)) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 bgb_5_1856))))))
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
theorem bgb_6_5824 : Interval gbAtlas 6 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5856 : Interval gbAtlas 6 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5888 : Interval gbAtlas 6 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5920 : Interval gbAtlas 6 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5952 : Interval gbAtlas 6 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5984 : Interval gbAtlas 6 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6016 : Interval gbAtlas 6 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6048 : Interval gbAtlas 6 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6080 : Interval gbAtlas 6 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6112 : Interval gbAtlas 6 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6144 : Interval gbAtlas 6 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6176 : Interval gbAtlas 6 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6208 : Interval gbAtlas 6 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6240 : Interval gbAtlas 6 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6272 : Interval gbAtlas 6 6272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6304 : Interval gbAtlas 6 6304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6336 : Interval gbAtlas 6 6336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6368 : Interval gbAtlas 6 6368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6400 : Interval gbAtlas 6 6400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6432 : Interval gbAtlas 6 6432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6464 : Interval gbAtlas 6 6464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6496 : Interval gbAtlas 6 6496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6528 : Interval gbAtlas 6 6528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6560 : Interval gbAtlas 6 6560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6592 : Interval gbAtlas 6 6592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6624 : Interval gbAtlas 6 6624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6656 : Interval gbAtlas 6 6656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6688 : Interval gbAtlas 6 6688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6720 : Interval gbAtlas 6 6720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6752 : Interval gbAtlas 6 6752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6784 : Interval gbAtlas 6 6784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6816 : Interval gbAtlas 6 6816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6848 : Interval gbAtlas 6 6848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6880 : Interval gbAtlas 6 6880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6912 : Interval gbAtlas 6 6912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6944 : Interval gbAtlas 6 6944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6976 : Interval gbAtlas 6 6976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7008 : Interval gbAtlas 6 7008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7040 : Interval gbAtlas 6 7040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7072 : Interval gbAtlas 6 7072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7104 : Interval gbAtlas 6 7104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7136 : Interval gbAtlas 6 7136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7168 : Interval gbAtlas 6 7168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7200 : Interval gbAtlas 6 7200 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7201 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760)))))) (concat (concat (concat (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 bgb_6_1984))) (concat (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)) (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 bgb_6_2208)))) (concat (concat (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304)) (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 bgb_6_2432))) (concat (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)) (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 bgb_6_2656))))) (concat (concat (concat (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880))) (concat (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)))) (concat (concat (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200)) (concat (concat bgb_6_3232 bgb_6_3264) (concat bgb_6_3296 bgb_6_3328))) (concat (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 bgb_6_3456)) (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 bgb_6_3584))))))) (concat (concat (concat (concat (concat (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680)) (concat (concat bgb_6_3712 bgb_6_3744) (concat bgb_6_3776 bgb_6_3808))) (concat (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904)) (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 bgb_6_4032)))) (concat (concat (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128)) (concat (concat bgb_6_4160 bgb_6_4192) (concat bgb_6_4224 bgb_6_4256))) (concat (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352)) (concat (concat bgb_6_4384 bgb_6_4416) (concat bgb_6_4448 bgb_6_4480))))) (concat (concat (concat (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576)) (concat (concat bgb_6_4608 bgb_6_4640) (concat bgb_6_4672 bgb_6_4704))) (concat (concat bgb_6_4736 (concat bgb_6_4768 bgb_6_4800)) (concat (concat bgb_6_4832 bgb_6_4864) (concat bgb_6_4896 bgb_6_4928)))) (concat (concat (concat bgb_6_4960 (concat bgb_6_4992 bgb_6_5024)) (concat (concat bgb_6_5056 bgb_6_5088) (concat bgb_6_5120 bgb_6_5152))) (concat (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248)) (concat (concat bgb_6_5280 bgb_6_5312) (concat bgb_6_5344 bgb_6_5376)))))) (concat (concat (concat (concat (concat bgb_6_5408 (concat bgb_6_5440 bgb_6_5472)) (concat (concat bgb_6_5504 bgb_6_5536) (concat bgb_6_5568 bgb_6_5600))) (concat (concat bgb_6_5632 (concat bgb_6_5664 bgb_6_5696)) (concat (concat bgb_6_5728 bgb_6_5760) (concat bgb_6_5792 bgb_6_5824)))) (concat (concat (concat bgb_6_5856 (concat bgb_6_5888 bgb_6_5920)) (concat (concat bgb_6_5952 bgb_6_5984) (concat bgb_6_6016 bgb_6_6048))) (concat (concat bgb_6_6080 (concat bgb_6_6112 bgb_6_6144)) (concat (concat bgb_6_6176 bgb_6_6208) (concat bgb_6_6240 bgb_6_6272))))) (concat (concat (concat (concat bgb_6_6304 (concat bgb_6_6336 bgb_6_6368)) (concat (concat bgb_6_6400 bgb_6_6432) (concat bgb_6_6464 bgb_6_6496))) (concat (concat bgb_6_6528 (concat bgb_6_6560 bgb_6_6592)) (concat (concat bgb_6_6624 bgb_6_6656) (concat bgb_6_6688 bgb_6_6720)))) (concat (concat (concat bgb_6_6752 (concat bgb_6_6784 bgb_6_6816)) (concat (concat bgb_6_6848 bgb_6_6880) (concat bgb_6_6912 bgb_6_6944))) (concat (concat (concat bgb_6_6976 bgb_6_7008) (concat bgb_6_7040 bgb_6_7072)) (concat (concat bgb_6_7104 bgb_6_7136) (concat bgb_6_7168 bgb_6_7200))))))))
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
theorem bgb_7_2176 : Interval gbAtlas 7 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2208 : Interval gbAtlas 7 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2240 : Interval gbAtlas 7 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2272 : Interval gbAtlas 7 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2304 : Interval gbAtlas 7 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2336 : Interval gbAtlas 7 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2368 : Interval gbAtlas 7 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2400 : Interval gbAtlas 7 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2432 : Interval gbAtlas 7 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2464 : Interval gbAtlas 7 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2496 : Interval gbAtlas 7 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2528 : Interval gbAtlas 7 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2560 : Interval gbAtlas 7 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2592 : Interval gbAtlas 7 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2624 : Interval gbAtlas 7 2624 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2637 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 (concat bgb_7_576 bgb_7_608))))) (concat (concat (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 (concat bgb_7_736 bgb_7_768))) (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)))) (concat (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat bgb_7_1216 (concat bgb_7_1248 bgb_7_1280)))))) (concat (concat (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 (concat bgb_7_1408 bgb_7_1440))) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600)))) (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 (concat bgb_7_1728 bgb_7_1760))) (concat (concat bgb_7_1792 (concat bgb_7_1824 bgb_7_1856)) (concat bgb_7_1888 (concat bgb_7_1920 bgb_7_1952))))) (concat (concat (concat (concat bgb_7_1984 bgb_7_2016) (concat bgb_7_2048 (concat bgb_7_2080 bgb_7_2112))) (concat (concat bgb_7_2144 bgb_7_2176) (concat bgb_7_2208 (concat bgb_7_2240 bgb_7_2272)))) (concat (concat (concat bgb_7_2304 bgb_7_2336) (concat bgb_7_2368 (concat bgb_7_2400 bgb_7_2432))) (concat (concat bgb_7_2464 (concat bgb_7_2496 bgb_7_2528)) (concat bgb_7_2560 (concat bgb_7_2592 bgb_7_2624)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeeeafac8eac0feeeeeeafac8eac0feeeeeeafac8eac0feeeeeeafac8eac0feeeeeeafac8eac0feeeeeeafac8eac0feeeeeeafac8eac0feeeeeeafac8eac0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071594 * 2 ^ 32 + 4207471296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37223.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,4]⟩,⟨.or,[0,6]⟩,⟨.and,[0,5]⟩,⟨.or,[3,8]⟩,⟨.or,[4,9]⟩,⟨.or,[0,5]⟩,⟨.and,[7,9]⟩,⟨.and,[10,11]⟩,⟨.or,[1,12]⟩,⟨.or,[2,13]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4207471296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4207471296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37223

open PEqualNP.Outside.L_meta_37223 in
theorem PEqualNP.Outside.L_meta_37223 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4207471296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4207471296) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
