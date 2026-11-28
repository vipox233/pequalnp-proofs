import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37139.Model
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


end PEqualNP.Outside.L_meta_37139.Model

namespace PEqualNP.Outside.L_meta_37139
open PEqualNP.Outside.L_meta_37139.Model
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

def SBf (j : Nat) : Nat := [6, 5, 5, 8, 6, 7].getD j 0

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

end PEqualNP.Outside.L_meta_37139

namespace PEqualNP.Outside.L_meta_37139
open PEqualNP.Outside.L_meta_37139.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xc03000072c038d1060000853c004024a01020000009002bf43de43bd43dd439d43bf42bd42df32dd32be41bc41de31dc31be40bc40de30dc30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x5800a6102002403300e0408a000031c7552438fa92871c5150e38a0a1c754f428eaa6651d544ca3aa620c7d52318eaa0631d531023ea9184755030
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x99000085185544ca18605513286983548c61661d5230
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 13
  | 2 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | 2 => packedAt s0K2 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (297+((h/5+packedAt s0K4 (272+(h % 5)*5) 5) % 27)*6) 6
  | 3 => packedAt s0K3 (371+((h/4+packedAt s0K3 (351+(h % 4)*5) 5) % 20)*5) 5
  | 2 => packedAt s0K2 (155+((h/1+packedAt s0K2 (152+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x1ffff81ffff83fc1fffc1fff83ffe07e79f3f3
  | 2 => 0xe07fffe07fffc1fe0fffe0fffc1fff819e7cfc
  | 3 => 0xff83ffff83fffffff03fff07ffe0ffffe78f1f
  | 4 => 0x3fffffc0001ffffc00007ffff0001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x430888c51090504052cc09498129212c28b171
  | 2 => 0xc91111432122028a05552092a4124b049254b4
  | 3 => 0x42222080a442114a02252044a409451450a0a
  | 4 => 0x965bc4924876b5e7398318c7739c0619f80fc0
  | 5 => 0x1863871c738739f9ce3b9ce063181861ffe000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0fcc0fcc0fc00fcc0fcc0fcc0fc00fcc0fcc0fcc0fc00fcc0fcc0fcc0fc00fcc0fcc0fcc0fc00fcc0fcc0fcc0fc00fcc0fcc0fcc0fc00fcc0fcc0fcc0fc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37139
namespace PEqualNP.Outside.L_meta_37139
open PEqualNP.Outside.L_meta_37139.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xd830
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
  | 0 => 0xfff80ff01fff00f83fffffe03e07ff803ff27c
  | 2 => 0x3ffffffffffffffc0fc03ffffffffffc63fff
  | 3 => 0x3ffffffe07fffffff0003fffff81ffff83f8f
  | 4 => 0xfc000fffff8000fffffffc003fffe000ffc3f0
  | 5 => 0xfffff000000000ffffffffffc0000000fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x184a6311c51235380b2cd4e60e433c861af23c
  | 2 => 0xa910a522482450514055412a528e492a4614d5
  | 3 => 0x52614a448348a4aa95029254a5511654b82b0a
  | 4 => 0x63458c89120ec6cce69b181839e58418ed43e0
  | 5 => 0x83860f0e1c70f8f738e3e39f01861860f7bc00
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaaf000f0a0f000faaaf000f0a0f000faaaf000f0a0f000faaaf000f0a0f000faaaf000f0a0f000faaaf000f0a0f000faaaf000f0a0f000faaaf000f0a0f000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37139
namespace PEqualNP.Outside.L_meta_37139
open PEqualNP.Outside.L_meta_37139.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x9c43
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | 3 => packedAt s2K3 (i*16) 16
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s2K3 (17+((h/1+packedAt s2K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xe07ffc0fff80ffc1fffff81ff03ff03f3fce73
  | 1 => 0xfffffffffffffffe07c07fffffffffffc47fff
  | 3 => 0xff81fff03fff03fff8007fe0ffc1ffc0f8739c
  | 4 => 0x1ffffc00003ffffff8000fffe0000ff83e0
  | 5 => 0xfffe0000000003ffffffffff00000000fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x290c4462891550c0594a99093213909619c631
  | 1 => 0x421088841220810a02902232446425284418c6
  | 3 => 0x85255121a45456d4a82a4d489a91ca82b86318
  | 4 => 0x1659a24907669b6734f30610ef38830cee83e0
  | 5 => 0x1861c38e3878e3b9c73c779c0c210c30f77c00
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaacc88cc88cc88eeaacc88cc88cc88eeaacc88cc88cc88eeaacc88cc88cc88eeaacc88cc88cc88eeaacc88cc88cc88eeaacc88cc88cc88eeaacc88cc88cc88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37139
namespace PEqualNP.Outside.L_meta_37139
open PEqualNP.Outside.L_meta_37139.Model
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
end PEqualNP.Outside.L_meta_37139
namespace PEqualNP.Outside.L_meta_37139
open PEqualNP.Outside.L_meta_37139.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x142b320044814201c600c0bf43bd43be42bc42be41bc41bf40bd40fa30f930fb10f810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x264009629287395010a5ca520d654c10
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
  | 4 => packedAt s4K4 (208+((h/4+packedAt s4K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s4K3 (111+((h/1+packedAt s4K3 (108+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x87ff81f07e1ffe1f0787c3fc7c0f07ff92364f
  | 1 => 0xfffffe007fffffe007ffffff800ffffe1ff87f
  | 2 => 0xf81fffff801f07fff807fc1ffff00781e3cf8c
  | 3 => 0x1fffffffe007fffff8001ffffff801fc0ff0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xb1588c4c9526c607c1c1633464a924b5921645
  | 1 => 0x81102128080060020a84488042514804e81a
  | 2 => 0x12ca24a40c504aa94804e90d2960160ca34a8c
  | 3 => 0x451449084102951294d00212528ca011580560
  | 5 => 0x661871ce719ce7dce76733806308c461ffb000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xfcc8fcc8fc88fc88fcc8fcc8fc88fc88fcc8fcc8fc88fc88fcc8fcc8fc88fc88fcc8fcc8fc88fc88fcc8fcc8fc88fc88fcc8fcc8fc88fc88fcc8fcc8fc88fc88, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37139
namespace PEqualNP.Outside.L_meta_37139
open PEqualNP.Outside.L_meta_37139.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x26643842c9400000095984ea00174679005280c69b004109c0c552001824d2224a8700000401d5a447a910005a65828f810c9051018303180002008ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fa30fd30f930fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x22544a0000be78745c5230b41a3e660e12348c32706ab80c88022496649c1e2e0010424c9a500848180a58002a6c5ec200a8c08e0076626e1c28bc000072002c68a484b0ac82004ea646a2948606c4409e00925a167a8a00ba0020043660a09098004456147c00803c00003aaab600ae000000387e26b23000b810059687043c39204041001288622061c0060050382265c2880d3e52d0e7aa921de94243bca84876f5250ed8a4a1e7d4d43d7a92873c5250f58a4a1cb149439f2a0877a5010ef2a021cf54e429f294853d5310a7ca4216b948429f2a6653d54ccb5885995e94332bca86653f548ca78a9194fd51329e2a2653e540ca7aa8196b10832bb2886575510caf4a0195e54032b7294836d52906f6a0a0de141419f2a6633d54cc6f4a198de543319f2a0633d540c6dca418db54831bd2806379500c7588590cf952219eaa4433f5448678a890d7d4d21ae29a43ac42486f6a090de14121af298815d531027ca9984f55330cea1e6179538c37687186e50e30dd21461b8428c33a869876d4d30dda1a61da434c37286987650d30cca1a61ba424c3708498768c930ec19261db314c3b262984f950309eaa0617a500c27ca9104f55220af29c415d538827ea8904f151209faa2213c544427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1121200250000b0100073c600d2854c010e3010c0241110a00062d6510832c9109510ca5963141418b18954cc70c5310921a318943cc2a86250e30a3189434c2996490d30aa189434c2c86250d30e2d89434c2986250d30e2189434c2886250d30a658c424c29b648c930a6590324c388420c930b4584324c29964cc530
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x21048976108324c340212c219261221c964cc530
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 99
  | 3 => 21
  | 2 => 3
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | 2 => packedAt s5K2 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (826+((h/15+packedAt s5K5 (736+(h % 15)*6) 6) % 56)*7) 7
  | 4 => packedAt s5K4 (2904+((h/33+packedAt s5K4 (2673+(h % 33)*7) 7) % 119)*8) 8
  | 3 => packedAt s5K3 (833+((h/7+packedAt s5K3 (798+(h % 7)*5) 5) % 28)*6) 6
  | 2 => packedAt s5K2 (150+((h/1+packedAt s5K2 (147+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffff03e1f87fe1f0f0f8ffe3c0f07fe41f64f
  | 1 => 0xf07fffc01fffffe00ffff0ffc00ffffc7e387f
  | 2 => 0xff81ffffe007c3fff00fff0ffff007038fcf8c
  | 3 => 0x1fffffff803fffff0000ffffff803f00ff0
  | 4 => 0xfffe0000000003fffffffff000000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x621511892549a2078382899a24a9216a40d645
  | 1 => 0x50822044a020060041510244042529016281a
  | 2 => 0x212c4494031404a91009a206896014188b4a8c
  | 3 => 0x8a5189211040ab12a9a00889328ca023600560
  | 4 => 0xcc610e399c6733dccece4cc02308c0c3fdb000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfce8fc88fce8fc88fce8fc88fce8fc88fce8fc88fce8fc88fce8fc88fce8fc88fce8fc88fce8fc88fce8fc88fce8fc88fce8fc88fce8fc88fce8fc88fce8fc88, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37139
namespace PEqualNP.Outside.L_meta_37139
open PEqualNP.Outside.L_meta_37139.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001017fd5001fe54007f55005fc5400ffd4c03fe5300ff54c03fc5300ffd0c03fe4300ff50c03fc43017fd4801fe52007f54805fc52007fd0801fe42007f50801fc4200ffcc803fe3200ff4c803fc32017fd4401fe51007f54405fc51007fd0401fe41007f50401fc4100ffcc403fe3100ff4c403fc31007fc8401fe21007f48401fc21017fd4001fe50007f54005fc50007fd0001fe40007f50001fc4000ffcc003fe3000ff4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42003ff0821001ffe210800ff71084001fd8842000ffd9510005feca880037f65440013fb2a200aff99510015fcca88003fd65440017eb2a200aff19510015f8ca880037c65440053e32a2000ffd9110005fec888003bf64440015fb222000ff99110045fcc888003fd64440017eb222000ff19110045f8c888003bc64440015e322200affd5110007fca888003fd5444015fe2a22009ffd8d1004dfec688027fe63440037f31a2009ff58d1004dfac688027fc63440037e31a2009ffd4d1004ffca688027fd5344013fe29a2009ffd0d1004ffc8688027fd4344013fe21a2000ffd8910005fec488003fe62440017f3122000ff58910005fac488003fc62440017e312200affd4910007fca488003fd5244015fe2922000ffd0910007fc8488003fd4244001fe2122009ffcc91004ffc6488027fd3244013fe192200affd4510007fca288003fd5144015fe28a2000ffd0510007fc8288003fd4144001fe20a2009ffcc51004ffc6288027fd3144013fe18a2000ffc8510007fc4288003fd2144001fe10a200affd411001ffca088003fd5044007fe2822000ffd011001ffc8088003fd4044007fe2022009ffcc11001ffc6088027fa3044013fe9822009fe4c11001ff86088003ff2044007ff1022000ff4811001ff84088003ff1044001fd8822003ff8411001fec208800fff65040077fb282003ff99410015fcca0800f7e65040053f3282003ff59410005faca0800f7d65040013eb282003ff1941001df8ca0800fff64040077fb202003ff99010045fcc80800fbe64040015f3202003ff59010005fac80800fbd64040015eb202003ff1901001df8c80801bff5404001ff2a02000ff55010037f8a80800fff63040077fb182003ff98c1000dfcc60800fde63040036f3182003ff58c1002dfac60800fdd63040016eb182003ff18c1001df8c608017ff530400bff2982005ff54c1002ff8a608017ff430400bff2182005ff50c1002ff8860800fff62040077fb102003ff98810005fcc40800fee6204001773102003ff58810005fac40800fed620400176b102003ff1881001df8c40801bff5204001ff2902000ff54810037f8a408003ff4204001ff2102000ff50810007f88408017ff320400bff1902005ff4c81002ff8640801efe610400dffa882004ff94410007faa208013fc5104001ffa082004ff90410007fa8208013fc410400bff9882004ff8c41002ffa6208013fc3104001ff9082004ff88410007fa4208013fc21040077f3002003ffd401001ffca00800ffd5004007fe2802003ffd0010007f6800800ffe4004007fea002003ff1001001ff0800800fff3004007ff1802003ff4c01001ff8600800fff2004007ff1002003ff4801001ff8400800fff1004007fb8802003ff8401001ff4200800ffd1004007fa8802000fe44010
  | 1 => 0xffe61080017f3084003ff58420005fac21000ffc6108021ffa884000ff94420007faa210043fc5108001ffa084000ff90420007fa8210003fc410801fff988400fff8c42007ffa621003ffc310801dff9084000ff88420007fa421003bfc21080077f3004003ffd402001ffca01000ffd5008007fe2804003ffd002001ffc801000ffd4008007fe2004003ffcc02001ffc601000ffd3008007fe1804003ffc802001fde401000ffe2008007fd1004003ff4802001fda4010003f92008009ffb2e2000bfd971006ffccb8800afe65c4001feb2e2000bf59710027f8cb8800afc65c4009ffb262000bfd9310007fcc988022fe64c4001feb262000bf59310027f8c988022fc64c401bffaa62000ff95310007faa988037fc54c4009ffb1e2007bfd8f1003ffcc788006fe63c400ffeb1e2007bf58f10027f8c788006fc63c400fffa9e2007ff94f1003ffaa78801ffc53c400fffa1e2007ff90f1003ffa878801ffc43c4009ffb162000bfd8b10007fcc588002fe62c4001feb162000bf58b10027f8c588002fc62c401bffa962000ff94b10007faa588037fc52c4001ffa162000ff90b10007fa8588003fc42c400fff9962007ff8cb1003ffa658801ffc32c401bffa8e2004ff94710007faa388013fc51c4001ffa0e2004ff90710007fa8388013fc41c400fff98e2004ff8c71003ffa6388013fc31c4001ff90e2004ff88710007fa4388013fc21c401bffa862003ff94310007faa18800ffc50c4001ffa062000fed031001ffc8188003fd40c4007fe2062000fe1031003ffe618800ffe30c400ffe9862003ff0c310007fe418800ffe20c4001fe9062003ff0831001ffecb0800eff6584007ff32c2002bf9961001ffacb08002fd6584007fe32c2003bf1961001ffec90800eff6484007ff3242008bf9921001ffac908002fd6484007fe3242003bf19210067fea908003fe5484001feaa4200cff1521001ffec70800eff6384007ff31c2001bf98e1001ffac70802efd6384007fe31c2003bf18e1005ffea70802ffe5384017fea9c200bff14e1005ffe870802ffe4384017fea1c200bff10e1001ffec50800eff6284007ff3142000bf98a1001ffac508002fd6284007fe3142003bf18a10067fea508003fe5284001fea94200cff14a10007fe8508003fe4284001fea142000ff10a1005ffe650802ffe3284017fe994200bff0ca1004dfac308033ff5184001ff28c2000ff54610067f8a308003ff4184001ff20c2000ff50610007f8830802fff3184017ff18c200bff4c61005ff86308003ff2184001ff10c2000ff48610007f8430800efe6084007ffa842003ff9421001ffaa10800ffc5084007ffa042003ff9021001ffa810800ffc4084007ff9842003ff8c21001ff4610800ffd3084017fc9842003ff0c21001ffe410800ffe2084007fe9
  | 2 => 0x2001fbcc710006de6388007feb1c4014bf58e2001fbac710002dd6388007fe31c4003bf18e200a7fea710053fe5388029fea9c4014ff14e200a7fe8710053fe4388029fea1c4014ff10e20095fac510057ff5288001ff2944000ff54a200aff8a510003ff4288001ff2144000ff50a20007f88510053ff3288029ff1944014ff4ca200a7f8651000fff6188007ff30c4000bf9862001ffac310002fd6188007fe30c4015ffd4620007fca310003fd518802bfe28c4000ffd0620007fc8310003fd4188001fe20c4014ffcc6200a7fc6310053fd3188029fe18c4000ffc8620007fc4310003fd2188001fe10c4003bf9822001ffea11000ffe5088007fea844003ff1422001ffe811000ffe4088007fea044003ff1022001ffe611000ffe3088007fd1844003ff4c2200a7f2611000ffc3088007ff9044003fbc8220007f64110003ff65480017fb2a4000dfd9520004feca9004ffe65480057f32a4000ff59520005faca9004ffc65480057e32a4000df19520014f8ca90003ff64480017fb224000efd91200057ec890003fe64480117f3224000ff59120005fac890003fc64480117e3224000ef1912000578c89004fff5448001ff2a24000ff5512009ff8a89004bff63480257fb1a4012ff98d2000dfcc69004bfd63480257eb1a4012ff18d2000df8c69004bff5348025ff29a4012ff54d20097f8a69004bff4348025ff21a4012ff50d20097f8869004fff5248001ff2924000ff5492009ff8a490003ff4248001ff2124000ff50920007f8849004bff3248025ff1924012ff4c920097f86490003ff61480017fb0a4000ff98520007fac290003fc61480017e30a4013ffd4520007fca290003fd5148027fe28a4000ffd0520007fc8290003fd4148001fe20a4012ffcc520097fc629004bfd3148025fe18a4000ffc8520007de4290003fe2148001fe90a4000fb48520007f8429004fff5048007ff2824000ff5412001ff8a090003ff4048007ff2024000ff5012001ff8809004bff3048007ff1824012fe8c120097fa609004bf93048007fe1824000ffc8120007f6409000ffe2048007f71024003ffd942001dfeca1000ffe65080057f3284003df99420014fcca1000ffd65080017eb284003df59420004faca1000ffc65080077e3284003ffd902001dfec81000ffe64080117f3204003ff59020005fac81000ffc64080077e3204010ffd5020007fca810003fd5408021fe2a04003ffd8c2001dfec61000ffe63080037f3184003ff58c2007dfac61000ffc63080077e318400fffd4c2007ffca61003ffd530801ffe298400fffd0c2007ffc861003ffd430801ffe2184011bf98820087fea41003bfe5208001fea90400eff14820007fe841003bfe4208001fea10400eff1082007ffe641003bfe320801ffe990400eff0c82001ffec21000
  | 3 => 0xf10a8000ff48540007f842a006bff5050007ff2828000ff5414001ff8a0a0023ff4050011fda028003ff9014001f7c80a0067ff3050007ff1828019ff4c14001ff860a000fff65100077fb288003ff99440015fcca2000ffd65100017eb288003ff1944001df8ca20022fe6410011ffaa08008ff950400477ca820023fd5410001deaa08008ff1504001ffec62000eff6310007ff3188001bf98c4001fbcc620006de6310007feb188017bf58c4001fbac620002dd6310007fe3188003bf18c400bffea62005ffe531002ffea988017ff14c40047fe8620023bf4310011ff2188008ff50c400bf7a8620023fc4310007ffb108003ff98840005fcc42000ffd62100017eb108003ff188400c7fea420003fe5210001fea908018ff14840047fe8420023fe4210001df2108008ff50840047f88420023bc421002fff9908017ff8c8400bffa642005ffc3210007ffb088003ff98440005fcc22000ffd61100017eb088003ff184400c7fea220003fe5110001fea888018ff14440047fe8220023fe4110001df2088008ff50440047f88220023bc411002fff9888017ff8c4400bffa622005ffc3110001ff9088000ff88440007fa4220003fc21100077f3008003ffd404001ffca02000ffd5010007fe2808003ffd004001f7e802000ffe4010007fd2008003ff5004001f7a8020023f94010007ff9808003ff8c04001ff4602000ffd301002ffc9808003ff0c040077fecb90002ff65c802dff32e4002bf99720007facb90002fd65c801dfe32e4002bf19720077fec990002ff64c8001ff3264008bf99320007fac990002fd64c801dfe3264008bf193200b7fea990003fe54c8001feaa64016ff15320077fec790046ff63c8023ff31e4001bf98f2008ffac790046fd63c801dfe31e4001bf18f2008ffea790047fe53c8023fea9e4011ff14f2008ffe8790047fe43c8023fea1e4011ff10f200b7fea59003bfe52c8001fea96400eff14b20007fe859003bfe42c8001fea16400eff10b2008ffe659003bfe32c8023fe996400eff0cb20077fec390003fe61c80017f30e4000ff58720005fac39003bfc61c802dffa8e4000ff94720007faa39005bfc51c8001ffa0e4000ff90720007fa8390003fc41c8023ff98e4011ff8c72008ffa6390047fc31c801dff90e4000fbc8720007fc4390003fd21c8001f690e400eff087200b7fea19000ffe50c8001fea864003ff14320007fe819000ffe40c8001fea064003ff1032008ffe619000ffe30c8023fe9864003ff0c32001ffecb1000eff6588007ff32c4002bf9962001ffacb10002fd6588007fe32c4003bf1962001ffec91000eff6488007ff3244008bf9922001ffac910002fd6488007fe3244003bf192200affea910003fe5488001feaa44015ff1522001ffec71000eff6388007ff31c4001bf98e
  | 4 => 0x6fc63d003bffa9e801dff94f400effaa7a0077fc53d0011ffa1e8008ff90f40047fa87a0023fc43d0011ffb168008ff98b40005fcc5a0023fd62d00017eb168008ff18b400f7fea5a0003fe52d0001fea96801eff14b40047fe85a0023fe42d0011fea168008ff10b400effe65a0077fe32d003bfe996801dff0cb40047fec3a0023fe61d00017f30e8008ff58740005fac3a0023fc61d003dffa8e8000ff94740007faa3a007bfc51d0011ffa0e8008efd0740047fc83a0023fd41d0001dea0e8008ff107400effe63a0077fe31d003bfe98e801dff0c740007fe43a0003fe21d0001fe90e8000ff087400f7fea1a000ffe50d0001fea868003ff143400effe61a000ffe30d003bfd186801dff4c3400eff261a000ffc30d0007ffb2c8003bfd964001ffccb2000afe6590007bf32c80029f9964001ffacb20002fd6590007beb2c80009f5964001ff8cb2000efc65900337eb24801cffd5240047fca920003be5490001feaa48000ef55240047f8a92000fff63900077fb1c8003ff98e4000dfcc72000ffd63900377eb1c8003ff18e4001df8c72006fff5390037ff29c801bff54e400dff8a720023ff4390037dfa1c801bff90e400dffa872006fbd4390011fe21c8003ffd8a4001ffcc520002fe6290007feb148000bf58a4001ff8c520073ff5290001ff2948000ff54a400e7f8a520023ff4290001ff2148000ef90a40007fa8520023fc4290001de214801bffcca400dffc652006ffd3290037fe1948003ffd864001ffcc320002fe6190007feb0c8000bf5864001ff8c320073ff5190001ff28c8000ff546400e7f8a320023ff4190001ff20c8000ef90640007fa8320023fc4190001de20c801bffcc6400dffc632006ffd3190037fe18c8000ffc8640007fc4320003fd2190001fe10c8003bf9824001ffea12000ffe5090007fea848003ff1424001ffe812000fbf4090011fda048003ffcc24001ffc612000ffd3090007fe1848000ffd9540005fecaa006bfe65500057f32a8000ff59540005facaa006bfc65500057e32a801affd5140047fca8a0003fd5450011fe2a28019ffd8d400cdfec6a0067fe63500037f31a8019ff58d400cdfac6a0067fc63500037e31a8019ffd4d400cffca6a0067fd5350033fe29a8008ffd0d400cffc86a0067fd4350011fe21a8000ffd8940005fec4a0003fe6250001feb128000ff18940005f8c4a006bff5250001ff2928000ff549400d7f8a4a0023ff4250001ff2128000ff50940047f884a0067ff3250033ff1928019ff4c9400cff864a0003ff61500017fb0a8000ff98540007fac2a0003fc61500017e30a801affd4540007fca2a0003fd5150035fe28a8008ffd05400077e82a0003fe4150001fea0a8000ef50540047f882a0067ff3150033ff18a8019ff4c5400cff862a0003ff2150001f
  | 5 => 0x4421027f8a210803ff4108409ff2084200ff50421027f88210887ff3108409ff1884221ff4c421027f8621083bff2108401f79084204ff88421007ec4210803fd2108401f69084200fd48421027fec010803fe60084077f3004200ff58021005fac010813fc6008445ffa804222ff1402110ffe6010887fe3008443fe9804221ff0c021015facb2800fff6494007ff324a008bf9925001ffac928002fd6494007fe324a002ffd5250016fea92800bfe5494005feaa4a000df55250017f8a92800fff63940077fb1ca003ff98e5000dfcc72800ffd63940417eb1ca003ff18e5001df8c72800bff5394005bfa9ca002ff94e50017faa7280837d5394005fe29ca020ffd0e50107fc8728083fd4394041fe21ca003ffd8a5001ffcc528002fe6294007feb14a000bf58a5001ff8c52800bff5294005ff294a000df94a50017faa52800bfc5294005be294a000ffd0a50007fc8528003fd4294001fe214a020ffcca50107fc6528083fd3294041fe194a003ffd865001ffcc328002fe6194007feb0ca000bf5865001ff8c32800bff5194005ff28ca000df94650017faa32800bfc5194005be28ca000ffd0650007fc8328003fd4194001fe20ca020ffcc650107fc6328083fd3194041fe18ca000ffc8650007fc4328003fd2194001fe10ca003bf9825001ffea12800f7f5094005fda84a003ff1425001ff0a12800fff3094007ff184a003ff4c25001ff8612800eff6554001ffb22a000bfd9150007fcc8a8003fd6454001fe322a008bf19150017fea8a800bfe5454001bf2a2a002ff55150017f8a8a800b7c545403fffb1aa01fbfd8d500fffcc6a8006fe635403ffeb1aa01fbf58d500fff8c6a8006fc6354005ffa9aa002ff94d50017faa6a800bfc535403fffa1aa01fff90d500fffa86a807ffc4354001ffb12a000bfd8950007fcc4a8003fd6254001fe312a000bf18950017fea4a800b7f5254005ff292a002ff54950006faa4a800bfc5254001ffa12a000ff90950007fa84a8003fc425403fff992a01fff8c9500fffa64a807ffc3254001ffb0aa000bfd8550007fcc2a8003fd6154001fe30aa000bf18550017fea2a800b7f5154005ff28aa002ff54550006faa2a800bfc5154001ffa0aa000ff90550007fa82a8003fc415403fff98aa01fff8c5500fffa62a807ffc3154001ff90aa000ff88550007fa42a8003fc21540057fb02a002ffd4150017f6a0a800ffe5054007bf282a003ff1415001ef8a0a800bf8505403fff982a003ff8c1500fffa60a800ffc3054011ffb2e8008bfd9740047fccba000afe65d0011bf32e80029f99740047facba0002fd65d0011beb2e80009f59740047f8cba0022fc65d0011ffaa68008ff95340047faa9a0023fc54d0011ffb1e8008bfd8f40047fcc7a0006fe63d0011feb1e801dbf58f40047f8c7a0
  | 6 => 0xfff32c4202bf99621006fccb1080a7e6588401feb2c4200bf59621006facb108027d6588409fe32c4202bf19621027fec910802ff6488401ff3244208bf992210077cc910802be6488401feb244200bf592210077ac910802bd6488409fe3244208bf1922113ffea910803fe5488401feaa44227ff15221027fec71088eff6388447ff31c4201bf98e2111ffac71088efd6388409fe31c4201bf18e2111ffea71088ffe5388447fea9c4223ff14e2111ffe871088ffe4388447fea1c4223ff10e2112dfac51089fff5288401ff2944200ff54a2113ff8a510803ff4288401ff2144200ff50a21007f8851088fff3288447ff1944223ff4ca2111ff86510886fe618844fffa8c4204ff94621007faa310813fc5188401ffa0c4204ff90621007fa8310813fc4188447ff98c4204ff8c62111fec631088ffd3188447fa98c4204ff0c621007fe4310803ef2188401fb90c4204ffd8221007fcc11080efe6088401feb044200bf58221027f8c11089fff508844ffe2844223ffcc22111ffc611088ffd3088447fe1844200ffd9521005feca9089bfe65484057f32a4200ff59521005faca9089bfc65484057e32a4200ffd9121005fec890803fe64484117f3224200ff59121005fac890803fc64484117e3224226ffd5121007fca890803fd544844dfe2a24225ffd8d2112dfec690803df63484016fb1a4225ff98d2100dfcc690897fd634844b7eb1a4225ff18d2100df8c690897dc63484036e31a4225ffd4d2112ffca690897fd534844bfe29a4225ffd0d2112ffc8690897fd434844bfe21a4226ffd4921007fca490803fd524844dfe2924200ffd0921007fc8490803fd4248401fe2124225ffcc92112ffc6490897ee324844bfe9924225fb4c92112ff8649089bff5148401ff28a4200ff54521137f8a290803ff4148401ff20a4200ff50521007f88290897ff314844bff18a4225fd8c52112ffa6290897f5314844bfe18a4200ffc8521007ee4290803fe2148401f710a4200ffd8121005fec090803fe6048401feb024200ff1812101df8c09089bff504844dfe2824225ffcc12112ffc6090897fd304844bfe1824204ffd9421005feca1088bfe65084057f3284200ff59421005faca10813fc65084057e3284204ffd9021005fec810803fe64084117f3204200ff59021005fac810813fc64084117e3204222ffd5021007fca810803fd5408445fe2a04204ffd8c2110dfec610887fe63084037f3184221ff58c2110dfac610813fc63084037e3184221ffd4c2110ffca610887fd5308443fe2984221ffd0c2110ffc8610887fd4308443fe2184224bf98821117fea41083bfe5208401fea90420eff14821007fe841083bfe4208401fea10420eff1082110ffe641083bfe3208443fe990420eff0c82111dfcc21088bff5108409ff2884200ff5
  | 7 => 0xa08b3fd63504597eb1a822cff18d4100df8c6a08b3ff5350459ff29a822cff54d41167f8a6a0823ff4350459dfa1a822cff90d41167fa86a08b3bd4350411fe21a8200ffd8941005fec4a0803fe6250401feb128200ff18941005f8c4a08b7ff5250401ff2928200ff5494116ff8a4a0823ff4250401ff2128200ef90941007fa84a0823fc4250401de212822cffcc941167fc64a08b3fd3250459fe192822dffd4541007fca2a0803fd515045bfe28a8208ffd0541047ee82a0803fe4150401df20a822cffcc541167fc62a08b3fd3150459fe18a8200ffd8141005fec0a0803fb60504017db028200ff98141007fac0a0803fc60504077e3028200fe18141005f0c0a08b7ff505045bfe282822cffcc141167fc60a08b3fd3050459fe1828204ffd9441045feca20823fe65104057f3288208df99441014fcca20823fd65104017eb288208df59441004faca20813fc65104117e3288208bf99041047fea820823fe5410411feaa08208ff15041027fec620822ff6310411ff3188201bf98c41047fac6208a6fd6310409fe3188201bf18c4114ffea6208a7fe5310453fea988229ff14c41047fe8620823fe4310411fea188208ff10c41027fec420823fe62104017f3108208ff58841005fac420813fc6210455ffa908200ff94841007faa4208abfc5210411ffa108208ff90841047fa8420823fc4210453ff9908229ff8c84114ffa64208a7fc32104577f308822affd4441027fca220803fd5110409fe2888208ffd04410477e8220813fe4110411fb2088208ff504410077a8220823f54110453ff9888204ff8c44114ffa6220813fc3110409ffb008208ff9804101dfcc020823fd60104017eb008204ff18041157fea0208abfc5010453ff9808229ff8c04114ffa60208a7fc301041dffb2e4200bfd9721147fccb9080afe65c8401bf32e42029f99721007facb90802fd65c8401beb2e42009f59721077f8cb9080afc65c841dffb264200bfd9321007fcc990822fe64c8401feb264200bf59321077f8c990822fc64c8451ffaa64200ff95321007faa9908a3fc54c841dffb1e4224bfd8f21127fcc790806fe63c8449feb1e4224bf58f21077f8c790806fc63c8449ffa9e4224ff94f21127faa790893fc53c8449ffa1e4224ff90f21127fa8790893fc43c8451ffa96420eff94b21007faa59083bfc52c8401ffa16420eff90b21007fa859083bfc42c8449ff996420eff8cb21127dc6590893fd32c8449f6996420eff0cb21147fea390803fe51c8401fea8e4228ff14721007fe8390803fe41c8401fea0e4200ff10721127fe6390893fe31c8449fe98e4224ff0c721077fec190803fe60c84077f3064200ff58321005fac19083bfc60c8451ffa864228ff14321127fe6190893fe30c8449fe9864224ff0c321027fecb10802ff658844
  | 8 => 0xf18d5100df8c6a880bff5354405bfa9aa202ff94d51017faa6a88c77d5354405fe29aa231ffd0d5118ffc86a88c7fd4354463fe21aa200ffd8951005fec4a8803fe6254401feb12a200ff18951005f8c4a880bff5254405ff292a200df94951017faa4a880bfc5254405be292a200ffd0951007fc84a8803fd4254401fe212a231ffcc95118ffc64a88c7fd3254463fe192a202bfd8551017fea2a880bf75154405ff28aa200df94551017f8a2a880b7c5154405fa28aa231ffcc55118ffc62a88c7fd3154463fe18aa200ffd8151005fec0a8803fe6054401feb02a200ff1815101df8c0a880bff5054405bfa82a202ff1415118ffe60a88c7fe3054463fe982a231ff0c151047fecba0822ff65d0411ff32e8202bf99741047facba0802fd65d0411fe32e8208bf19741047fea9a0823fe54d0411df2a68208ff553410077aa9a0823fc54d0411ffb1e8208bfd8f41047fcc7a0806fe63d0411feb1e822fbf58f41047f8c7a0806fc63d045fffa9e822fff94f4117ffaa7a08bffc53d0411ffa1e8208efd0f41047fc87a0823fd43d045fdea1e8208ff10f41047fec5a0823fe62d04017f3168208ff58b41005fac5a0823fc62d0461ffa968200ff94b41007faa5a08c3fc52d0411ffa168208ff90b410077c85a0823fd42d0411fe2168208ef10b4117ffe65a08bffe32d045ffe996822fff0cb41187fea3a0803fe51d0401fea8e8230ff1474117ffe63a08bffe31d045ffe98e822fff0c741047fec1a0823fe60d04077f3068208ff58341005fac1a0823fc60d0461ffa868230ff1434117ffe61a08bffe30d045ffe986822fff0c341027fecb20802ff659045dff32c8202bf99641007facb20802fd6590409fe32c8202bf19641165fac9208bbff5490411ff2a48200ff55241047f8a920813ff63904577fb1c822bff98e4100dfcc7208affd63904577eb1c8204ff18e4100df8c7208afff5390457ff29c822bff54e4115ff8a720823ff4390457ff21c822bff50e41047f88720813ff6290401ff3148200bf98a41007fac520802fd6290409fe314822effd4a41007fca520803fd529045dfe2948208ffd0a41007fc8520803fd4290411fe214822bffcca4115ffc65208affd3290457fe1948208bf98641177fea320813fe5190401fea8c8204ff14641047fe8320803bf4190411fba0c822bffcc641027fc63208affd3190409fe18c8204ffd8241007fcc12080efe6090401feb048200bf58241027f8c1208bbff509045dfe284822bffcc24115ffc61208affd3090457fe1848200ffd9541005fecaa08037f65504013fb2a822dff99541015fccaa0803fd65504017eb2a822dff19541015f8caa08037c65504053e32a822dffd5141047fca8a0803be5450401feaa28200ef55141047f8a8a08b3ff63504597fb1a822cff98d4100dfcc6
  | 9 => 0x811fe2a28436ffd8d421b5fec6a10dbfe63508037f31a8436ff58d421b5fac6a10dbfc63508037e31a8436ffd4d421b7fca6a10dbfd535086dfe29a8408ffd0d421b77e86a10dbfe435086dfea1a8436ef50d42047f886a10dfff5250801ff2928400ff549421bff8a4a1023ff4250811f7a128400ff909420077c84a10dbff325086dff1928436ff4c9421b7f864a1003ff61508017fb0a8400ff98542007fac2a1003fc61508017e30a8437ffd45421bff8a2a10dbff315086dff18a8436ff4c5421b7f862a1003ff60508017fb028400ff98142007fac0a1003fc60508077e3028437ffd41421bff8a0a10dbff305086dff1828436ff4c1421b7f860a103bff65108117fb288408ff99442015fcca210237e65108053f3288408ff59442005faca210237d65108013eb28840eff19442045f8ca21022fe6410811ffaa08434efd5042047fca821023fd5410811fe2a08408ef15042077fec621022ff6310811ff3188401bf98c42047fac6210cefd631081dfe3188401bf18c4219ffea6210cffe5310867fea988433ff14c42047fe8621023fe4310811fea188408ff10c421adfcc4210d3ff521081dff2908400ff54842077f8a421023ff4210811dfa10840eff90842047dc8421023fd4210801dea108408fb5084219ffe642103bfe3210867fe990840eff0c842077fec221023fe61108017f3088408ff58442005fac22103bfc6110869ffa888434ff1444219ffe62210cffe3110867fe9888433ff0c442077fec021023fe60108077f3008408ff58042005fac02103bfc6010869ffa808434ff1404219ffe60210cffe3010867fe9808433ff0c042015facb28813ff6494401ff324a208bf99251007fac928802fd6494409fe324a202ffd5251017fca9288037e5494405feaa4a202ff15251016f8a928813ff63944657fb1ca232ff98e5100dfcc7288cbfd63944657eb1ca204ff18e5100df8c72880bff5394405ff29ca202ff54e51017f8a7288cbff4394465ff21ca232ff50e51197f88728813ff6294401ff314a200bf98a51007fac528802fd6294409fe314a202ffd4a51016fea52880bfe5294405fea94a200df54a51017f8a528803ff4294401ff214a200ff50a51007f885288cbff3294465ff194a232ff4ca51197f8652880afe6194405ffa8ca202dfd4651017eea328813fc5194405fa28ca232ffcc651027fc63288cbfd3194409fe18ca204ffd8251007fcc12880efe6094401feb04a200bf58251027f8c12880bff5094405fe284a202df14251197fe61288cbfe3094465fe984a232ff0c251015fecaa8803ff64544017fb22a200ff99151007fac8a8803fc64544117e322a202ffd5151016fea8a880bfe5454405feaa2a200df55151017f8a8a88c7ff63544637fb1aa231ff98d5100dfcc6a88c7fd63544637eb1aa231f
  | 10 => 0xa1290f3ff3094879ff184a43cff4c2521e7f8612900aff6554801ffb22a400bfd91520077ec8a9002bf6454801ff322a400ff59152007f8c8a9022fc6454801de322a400af19152017fea8a900b7f5454805ff2a2a402ff55152006faa8a900bfc5454877ffb1aa43bbfd8d521dffcc6a9006fe6354877feb1aa43bbf58d521dff8c6a9006fc6354805ffa9aa402dfd4d52017fca6a900bfd5354877bea9aa402ff14d521dffe86a90effe4354877fea1aa43bff10d52015fec4a900bff5254805f7a92a402ff94952006fca4a900bfc5254805be292a402fb149521dffe64a90effe3254877fe992a43bff0c952007fec2a9002ff6154801ff30aa400ff58552007f8c2a9002fc6154805ffa8aa402ff14552016f8a2a90efff3154877ff18aa43bff4c5521dff862a9003ff60548017fb02a400ff98152007fac0a9003fc60548077e302a402ffd4152016fea0a900bfc5054877ff982a43bff8c1521dffa60a90effc3054811ffb2e8408bfd9742047fccba100afe65d0811feb2e8400bf59742047f8cba1022fc65d0811ffaa68408ff95342047faa9a1023fc54d0811ffb1e8408bfd8f42047fcc7a1006fe63d0811feb1e8439bf58f42047f8c7a1006fc63d0873ffa9e8439ff94f421cffaa7a10e7fc53d0811ffa1e8408efd0f42047fc87a1023fd43d0873dea1e8408ff10f421d7fea5a1003fe52d0801fea96843aff14b421cffe65a10e7fe32d0873fe9968439ff0cb42047fec3a1023fe61d08017f30e8408ff58742005fac3a1023fc61d0875ffa8e843aff147421cffe63a10e7fe31d0873fe98e8439ff0c742047fec1a1023fe60d08077f3068408ff58342005fac1a1023fc60d0875ffa86843aff143421cffe61a10e7fe30d0873fe9868439ff0c342077fecb21002ff6590871ff32c8402bf99642007facb21002fd659081dfe32c8402bf196421b5fac9210e3ff5490871dfaa48408ff95242007faa921023fc5490871de2a4840effd8e421adfec7210d7fe63908037f31c8435ff58e421adfac72103bfc63908037e31c8435ffd4e421affca7210d7fd539086bfe29c8408ffd0e421affc87210d7fd4390811fe21c8408bf98a421c7fea52103bfe5290801fea94840eff14a42047fe8521003bf4290811f7a148435ffcca42077fc65210d7fd329081dfe194840effd8642007fcc321002fe6190801feb0c8400bf58642077f8c3210e3ff5190871fe28c8435ffcc6421affc63210d7fd319086bfe18c840effd8242007fcc12100efe6090801feb048400bf58242077f8c1210e3ff5090871fe2848435ffcc2421affc61210d7fd309086bfe1848400ffd9542005fecaa10037f65508013fb2a8437ff99542015fccaa1003fd65508017eb2a8437ff19542015f8caa10037c65508053e32a8437ffd5142047fca8a1003fd5450
  | 11 => 0x200000e00e00400002000000200001201000400000000201400000000200200200601400000000c00000400200000000a00001000600205400400000600200200000000600000e00400400401201c00400400000000000200200000000400200400200600000200001200204200000c00000000a00000000201a00800600600200000000a01400400000400600200000200202bf59654045fcc92a023ff5495011bfaa4a802efd52540167ea92a023fc5495011de2a4a808ffd8e54045fec72a023fe63950037f31ca808ff58e541f5fac72a023fc63950037e31ca802ffd4e54016fea72a00bfe5395005fea9ca83edf54e54017f8a72a023ff4395011ff21ca808ff50e54047f8872a023ff6295011ff314a800bf98a54047fac52a002fd6295011fe314a802ffd4a54017f8a52a00b7c529507dff994a83eff8ca541f7fa652a0fbfc3295011ffb0ca808ff98654005fcc32a023fd61950017eb0ca808ff18654017fea32a00bfc5195005be28ca83effcc6541f7fc632a0fbfd319507dfe18ca808ffd8254047fcc12a00efe6095011feb04a800bf58254047f8c12a00bff5095005bfa84a802ff142541f7fe612a0fbfe309507dfe984a83eff0c254045fecaaa00aff6455005ffaa2a802efd5154047fca8aa0237e5455011fe2a2a808df1515401778a8aa0f7ff635507b7fb1aa83dff98d5400dfcc6aa0f7fd635507b7eb1aa83dff18d5400df8c6aa00bff5355005ff29aa802ff54d54017f8a6aa023ff435507bff21aa83dff50d54047f886aa003ff62550017fb12a800ff98954007fac4aa003fc62550017e312a802ffd4954016fea4aa00bfc525507bff992a83dff8c9541effa64aa0f7fc3255001ffb0aa800bfd8554007fcc2aa003fd6155001fe30aa800bf18554017fea2aa00b7f5155005fe28aa83dffcc5541effc62aa0f7fd315507bfe18aa800ffd8154005fec0aa003fe6055001feb02a800ff1815401df8c0aa00bff5055005fe282a802df141541effe60aa0f7fe305507bfe982a83dff0c154015facb2903bff6494801ff324a408bf99252007fac929002fd649481dfe324a402ffd5252017fca9290037e5494805feaa4a402ff15252016f8a92903bff63948797fb1ca43cff98e5200dfcc7290f3fd63948797eb1ca40eff18e5200df8c72900bff5394805ff29ca402ff54e52017f8a7290f3ff4394879ff21ca43cff50e521e7f8872900afe6294805ffa94a402dfd4a52017dea52903bfc5294805f6294a43cffcca52077fc65290f3fd329481dfe194a40effd8652007fcc329002fe6194801feb0ca400bf58652077f8c32900bff5194805bfa8ca402ff146521e7fe63290f3fe3194879fe98ca43cff0c652077fec129003fe60948077f304a400ff58252005fac12903bfc6094805ffa84a402ff14252016f8
  | 12 => 0xc01e01800000a00000200a00c00000400600e00400e00000400200200000a00000200401a00800200001000001a03e00601e00402600200001200200200400800400000001c00201600000000000000000e00000c00400600600200200200000c00004c00201c00c00000400c02400200200e01405003000200600200a01200200400002200603000401800200600000000200000601200000000c01600801200800400800800000000200400203a00400200401400201200400000000201400400001a01000c00000001600800200800600001c00000200000000000000001000800400200c00600400200600800000000000000e00000800001600000801e00402600003600000200000000200200c00802c00000200200601e01400a00200201202e00202c00000800201a00000000200a00e00000201801801e00a00000c00800400000e00201c00201801c02800e00400c00400402e0040000a400402200000200a00000200200800000200000200401200000200000404600201000000c00600200000000c00000000000400400401200000800000201405209e00600000800800200a00405a00400202200400400200401400001001002001a00600600000000001800800200000400000400001c00000000000400800200801e00000800400000001800403803801800e00001e00200400400800400001a00202e00200000000001401400001800000601800000003a01200200000a00601000a00200600a00401200400001400200800201200800001200a00000a01000c00600601000005600000000200000401c00000000002800000000800201c00400a00000600a00000000401800000e01400e00800200400000200a01400000201000201001e00601200600a00200000a00400002200000600200000000001600000a00400400801000000001600200201000000800400200200200200600002200201601802801a00000001c00800000000601200400c00000401406200600000400a00a00000202600a00001400001c00200c02601000802800403000c00600000600000600000000200400400200600c00000200c00a00000600202600e00400200000200001000200000a00400000000001203200a03200000601203c01c00200000200200000000000a00400000200200002200000a00201400400000000600600000000600000a00201000001000401200801200400000000000000a00000400001a00000000c00400200e00a00000200200200a01400600601401c03e00800a00200002202000800000200801602000000a00a00000000800600000000600401400600800200600000600402005c00000000200400000000800000001800000a03000400200400400a01600c00002200200001000401000000200000c00001800
  | 13 => 0x40002c7a1b111a003133800075e59744e800140a4b900000007425e60b61a84e1013c19c260400077b00024c00000000002454aec00000006f88740000000000a788510c4808d26a0002eea73c0007784dd10f0ed09c328487000ce00017d19d40003413da8be4de499514884dc0000003e2224062c4c02c303502f07cb000250092c79741c169c8689c04d500013382b52929004000000089004c0000002ca81bd2b81620000000000722340a2f49100001890000dfe97d4c900002d078a49922fd1ee000000255cc86476147280850a84f0000000f0c0003e924682829ef4a30f54f827e13bb00010388d60000fb509400012903f534a67f0a5026c0003653130000d4c32900000000000ba4b500011be8e94b3278c13aa3050e931d3bc925465288857c68c44a800028e61a00019c8c12000000146800066500021800002fd4a88d694260000000f8400000000000000000000001cb00006b315907d921629e4ba0000cda0000000000aa42c914603483fa0000ff800000000011d0b2c9fa80c51490c060c0000000820ac464006e86d09bc0114c40b5c6fa5150001ba0b881dd2e40b9c07c1e042192d0a1e8ec40f80000009230000000000000458237400092700019ec5523dd44305fcf9400041a00008d60a52d2000059a000000000000000000000000002ac00018a04aa000000094400000000004000000000000db400000040504f46a83140620b88458000489048c3fc0000958000f6200028c8650db401b0000001000000423000089010e16d03340000004c4800000060200004701c65b2444a4e4000296102205c12e57c006a514a924c827591d000061d18aa1553fc00001e25a404a97b42100013186af2cd1c6c0329c12daa290f0a54001396b4d8891921c24d80001bc0a48000e4c2d2000120c00084c11500000009bb38e812805c5b800000000006c6401a528e7200000000000000001130f28faa7d949e99b0ade02944a1b98cc286b2689aa083283336603401e80001b201e000094f0000000000045000197001250050694706b21320b512180000004e325583ca54d2018d7808212c3641fb84c865e4f313d80009780000d58bf000000009b82486464d680011e82460f890c903c0003bea0dd07a0000189b8086e000000032c0006043e81b44ce233904c8000000000474015800037c0caa0b146a00043314f40000b80f19fe800042520a80000000000d5800000000800800000401000a00000800000401804200200000000600401400000400e00200000000000401400000000001200400002000c00400400200600400201a00200600200000a00003402e00201400000c00001a00200201e00000400600000a01200400000000000001800200200400e00800000000e000020002048002000002016008002004024004000
  | 14 => 0x41358cb20003cd1510c220e20000cec0008ff0201664000000422000000000000005f05fc01f29f80000000002c080000000810db0000000000000241800045b0fe00000004a52dba3ec57e08930aa5b00000002740000d7c9ec0001ee0000000000106093605700007692d63500b88f0c4609673ef00010faa3900026dc0004b22730bd11f075a04303b43c28720b2a8b8ef80000cd0f6cdde9a73d2891c9e88f130000000000001c5890400000022c000000097500001d800080e3fb0758fa67042e100010de00027a9c3c0002052698000000760000000000000000000013d400000000000000000000000ff83240001fc49d89e00001c0518e30f2098be102c1f933313404e652f0001b9c0001a448a0840b062de1090fb883e2e600028ac00040900020253f00be43b000000070c486800003800032200000000003fca2b807a7c22410b3843c83019b88b8d1278837d101111e8fe03e80000009fc00008bca7600000000009c455a03600004280002e7855800000006d0cd000039c3ae0000ca000000000003e4721000000068c37800004800007a924aa2ad25e32d0b094e40002f200000007d00000dc0b9127439706b8d0845297309a978c0004101910000212436232a6f4cb40d64e8950493a6331d6800000052d249822000000017e088400000022f00000cc4611da00ecc3631d0000000000000000000000027b350194cddc15f2bb95b40921d2295128929693e01a9201328000000208c79c11e1d51b708820000000000ea66013858000daa69f50f05b8cc432f2ff1b952565c30aa11f4b8059b40909641ee8cd4b100000007a83aa98808ae55f0000000b4a1c500000000000002610fcd0ac8f929a98a499e0000a898dc00079e45300008cc1150d2a054efe240000000000000000000004689e73c100011c21d30000000fd2059231000097e510247a1c00000000238dd4e7800000012c00000000000000f9e4b5000000129834c0001b8c00084b0ad9bccd223d8000257c85024e3811e891fa1ae13500014120554e81a2c0000004ad0001054000000000000000000000000008aa25e1fbc0003a52d78000000000000112c0000000e5000014400000000005a218f43a0a70b562aa000002841200046108600000aa00023249d40002b9000130e000347800031a9db2ce80000003090bb00013f45bb0000c712522c719098fcc9651e475145ce0c10d30b0c4c76c52925580000004c93eb9a1472a23f3b708cc7460002e89bac67a0000000f7c5fe0000000f880005d300004b90503040000244c1073443091b4bb462c2d104093964f106314508e400000017ac00005b23e25d82080003170934bfe811057252079a0721a9170400000000002f027e5d500000000006951dc05400004bb0a400003e03f22350bd400055000006ed14
  | 15 => 0xd261851f9ca8e9a98b12c0414c5e00016c28c400000038280007660004758fc40000640948f446506572902034c447fe39f000000000000000006a600008a05dcc6c00007ca60c000000393975c00091f1d480007982e800028952762f621fa2d83867524850000000a3330f80008280001ca1d4000050d00000007500f639d00000000000000c6800043d0000000f8a00044d00000002630e095b00001b9037149c0000000000000000000000115503600000000000000002251be47bc80b48e889445a73004a9a8c66a6542158724c9a5ed03984043608e623d1db4c54a3d29980003d88ba37f0000000000000245d13e0000a71e0c05a05e05b240800002f00026c86f616d035909c0000002c706b513094126f800070e00026c2730d140a00001b2c606999065000000039e000172895800000024e11783fd4491b380007e60000a4000000045f0b3047276747b1684e5c72400006f40004891158d9813c6d811b10e42f27b319519bc00000000000014580000000000dda0004e688c800000036d9de8be80654d0259415a95300015ec76a0000498000b080004f09b780000001de1cd43da1690000d7ce520004bf0d84796a1a468800000000003125243b06602c924207843d030f0240a1882f0fa1d141ca2840b319d000066e262000000029b00000000006130980000fc667607a83b12bc00026600003d0000000000116277200018287720000002634cfa6930a00cf000000043f800076e9ff00000011aa0e03751ef8c200000000268000000416800000000000027c00004c516a219c4da6781a700a00007141d90d5446a0004da000137264e00011140000000000e349f600048e0000d8e0001189e3c00041b0ce0e3d11c8782131a3883ca3b0d61f60000000000068c30c0002068a240000001f3800141c305000000000000015424604980ac1fd9a00e40632084072033241635e225c8d21e900000000000000000c380000000000c440005542a50d74d9a76a0042884e3c89346d0c654743c54838398a304f80000000b0e0000000000000a11519000096e52600003bc0000001070000b1200000000000002530001f240009770000000e5600027711c078287e3d680001000001619aa4ebc479047978400082604397a81d64400e200000569113b0a8d02860000c085183247ab4f880000005c90001c400003490000000d926733c6836c0002f00a6968c0e20004a18c400f60000cea6f0a9c3572a322210a683f000000000042030580008e61a60000000000000332092c0009fd4df000000077100009fc4fa6f63cc892083a71a1c1929d06a9c520289090ae2e939b97d88a60ee4ea21e424a2f729097a03445b100000000000000000000c8e16b00000002e666a0000d1c0008e71dd213881c8b43510514e7e8cf09c00013520a150
  | 16 => 0x99220000071c44280000000000698000c1e0000000abcbe62802c29e80dfa83c17892b906c8d3369955cd0e01000024880005e023722580da71749307bc51001a1ad99280002b1000281821826f44618f800000000012780009911901d7411a0002b1a508000000177800000072d00014b146e7aa0000ec40007e006c80004d800000b00000000000000dc4c820000000da91b247f000094000071f2fe9a906f200000023600ba7e435b27c8172006517a28c98c0522e71e3000000000017e910600000000000006d70002310866863303854c0002bb1b380000006981a8979400000013e000000000000000e13ea85911d884c0000004ac000000000000003440000004b18e210620000bea1dc000000000016000000000015a00000000a22754af210f3d0800023a0000ef23387804ca1c323c081000000000001c20002b283a00c23c8000217504086e1c984d8de200c0751fccc2812732480000000000001c480000000002850be074b0791304d249044111d5935e93126a0000f266844b89e7cd5c0005122580dd2000149893c00055b13b935c6180c3384800144c7b7000000113c0003889d200000002500dcd3484e427f21ec00030232100000007e831d9ffcf208d220b80007f01a126d00008380181c50efc1d207508c84cc33e7db22e84b4cba25b10d8770e1a58d1b80fb00001a9135908c00000006e09880001df16ea22c0003ac35913dc00069e2ec829926600000005080006bb0001a40ecc51130c8c5c5a600012b07e0bb600000000007d68b800000011865220000000bf6a283f500011e64e7000000116a7b200000007ec8692d513c86102d0000000000079c143868019e00019180010300ce297113ca2c3ea08b98e48ee1e60e714040f83254c324300003ae0600cac88e14b26e00002166354ec255458c53004189e4696085198a6c4e84a1900004f86d046c4c9800000028304615200e8537000152c902005193902c00021700010009082e110502dc9181e4088958000099b00000002aa4a902a15550b893f12e0a84a646f00911d182ae5f142492450a46aa0e611344ca8d409500000003450ae800031423700016980680000000000886000000150c38e17536a000090e9f337a8d340000001858dc892e33606082c80001902bc15984c25ec0420000ba806003ba708a7400000005649483d351c1e100000003a0216000000009d140c1f6a1c0000000fa20004cea0b89623be3122204f2200000003310be0003a4800018e1700c121a092885000027b93ba4cd0111ef000096d47200000000001f801100003e647e00fc52a39b442000125a0000b0000136096f4e998c41600a746419c000056a08392f40000003f38a7400000035ba43c000000000029036477e00021b440c2d64398cf87ea3e30001e591506df21700013
  | 17 => 0xe7a3891b78000d6a3b036b0000e5e99a16d9124a26459497000136c0000738dd88a431b4ed13c032264500000001240005080eace147a400000000008e300014a000000000000a90080512de00013ae0000000000b980000000b649962c80000f1919600033e0d6000000010100000005b94aa15a4cfc0000c18868ca247b2a8848406e2e03f827d000000000016d8822a1b4ef96a000029400000007446990000000000000078053c6dc5740cf000109a00000016b80004b35200000cb6026000000077600016280005d600000000004923d23091d309740000001e1cf766231568390f280002b095c02fc3d40001b141f40003ea00000000004031894ede2ee454977c7c006a1fd03f08521d540e847c0000324c1273941663d08198b483498e1d0046c5aa4ed21096589f80003fe91440009c90000f5852e25e0d38e58cb02574b917bcda48e50180c603667da10c8a7ccce2604bf9f593f262707f0fd0b8c52443d035520047522f837810477713400003360001b580007ca0002169ee80007c30d8810ce7083b3678090dc25a00000458c7042f1ed11e11dc9ab0dfa80cb2843b0000f651725b4399a83c4480000001428dba6770831b083a04f90a60000c609e501080008ce0000002728ea200041f1640e9e0003ba86d400085a5062678f02a00404258482428d21892b436e92812fa758d8019604509d52060003dc9ed8a1c34a43211901b06964cb883405876929f1f0067495000087506c40002260e040001cb00000008c62b321a8250a8e07f28d8d80ad605016223791425f515d1180000363000000000043e0e100000000000001b2800000004b147c00000011f16e83a281447a972d43e3dc24c8ac00004a8000000016822804e014c51612f4870e4800000035580002c860e00000014309e44e38000be42864df85d000013445d8d712683a714d19e869e09822b000069000000015fc0001672a99a181520792b98e400008dc000151400000032900000008d72748000000000000157415e80126d813000094400000000003c91678e74b7c9e216e0df896c9f73ac000098605f0f99870b184a64da9d953da09f0798000fea0003d1800000042c3030c04df85fc4768600fee2b41bd000004000e38c03142e48ac3f280013000170000f90b144ff16023e857800011e800000096e00000000006b04cf8000a462a30bd1b048e266905d9008d7e86a4a3802c9a47b014c861cafa9eb48980012485911389d387182b9089a1c4ed800010e9f212429fb00019acd5a7622120000ee80000d5000000000000004ed1380000002614f5c78e462818c00021f2bd1c0cf9c91b0001dc1212000153a80454a713410800111400034e000032e28219f9ef400018438aa04c0006ba00000000007570001ed0478033457941535830d0000000a100003
  | 18 => 0x4138000d700004b800000000000000e100003fe000159c0008320a906e80004e5000097494600000000012202162bf089c000422151083d26e7f42ac82f40000001a00e7cb000003f90a602f601e41217a42de98a40d25647ae5bf00000000003910d41660bf274a2c4000110e3f91061d0cb3800000000013707190001e487d26c34c202d42346bd31a1d6400006834e9814214a151220000ae258215201a4c780000000000fda3a63bc95604cc75f3dfa1893d02a60649d1c0007ac32fa11d2780003e3164c30a4e000008711984af19981c0bce6d00989f1cac89640001270eb68541cc9dac4e025a147873cf9a58b477901d3300001981788f4e2ae352995910412851f281120a12629b185c8a82723159920c747731fba6a0e002150459d04cd06790f714e088437f228046038c27e3b200000008b70000c780000000f5a6b8c9e5b0331a5f0f5e7df3f592410f800026ca4a80005ac0078ba800000000009d000049200000000000000000d0c00000000000000008e00ae142cfb88d03870000b3c4460000ff048615e0000a2800000015c229456c00000000000002f300028b534c0000000000000000000231891445c06f99305829dc0eda0406ee9a139d800089c1cd140800009e000000028c0000000fd20acd688db471174841694d279a194d2e2012e280013660b3000000000050200000000000000000e68000a3642f000000055c00000009f40000eba5e4ff618e00007d4000000000000055600000020e400018c459a0949ba00000000014542e52ef02ac3d460c00000009c22b70000c98330a0a4fb0000aea00000028803ce000000000000000000014c40000000000000d5800000000004ec0002508a48bb800000002fc93e00000012a80962bd34180001620003aa00000b401500922800006fb0001740adc4851118000bc8332203000132079d41480112baa3c2378074a3a8f20000000000000171903c2b03cf1851ac500a6a737a03e03f6000000000077a4be00000000002df2e68000ec60000001884a0897a10180000002070000cb000000000000000007cc00024592d007a4901c1c40026934691a00007980001e98000000000000065c00000012e000085b35c80000002ed44da68c0908910c4284899c54c407a0640840143c5976000e0000000000a9e00012a000000094e000271027253439b000070a8754609b900000002ab2858e4642a3ee80000000000d789e0326731283800000092c246a68800000026a903060e27a45922b4000000000000091c91e00000011800000001e6c000000000263c47000000000002b48a750b8b286009960230000c1a00042000e8788000000000000000015000000000002f707dd13203612517592a49d94240fbcd346880271268a246e21b61f88df0a270f1122c31644400116a4
  | 19 => 0x2d98000d0400000000007306f70001e0058437401c9c9400095b2af00000fc9d22cf941800021100012610740003fc000000090106100008b400030180003b20000001b6400000018f8da40002fb000000108a0000b180001fea07000201c70004d0000000e2c7281e39e544444ef29596f47fe11051197dc7046552050bb0f1200000003c41900001a200000005c7000210471c7441d20914fd854234d9a500000000000000000000376272000047e4010170000220271800011c0a8
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xb705481001df87054810044ff76d081001cfe76d0810004fd76d081001cfc76d08101d67e65d08100067d65d0810046be64d0810006bd64d08101cede63d0810006dd63d0810006ee62d0810006ed62d0810074ff769081001cfe7690810004fd769081001cfc76908101c67e65908100067d6590810046be6490810006bd64908101aede6390810006dd6390810076ee6290810006ed629081001dfa7090810005f97090810227b84090810004ff765081001cfe7650810004fd765081001cfc76508100057f75508100357c75508101be7e65508100067d6550810046be6450810006bd64508101b6de6350810006dd6350810006ee6250810006ed6250810005fb705081001df87050810074ff761081001cfe7610810004fd761081001cfc76108100357e75108100057d75108101a67e65108100067d6510810046be6410810006bd641081019ede6310810006dd6310810076ee6210810006ed621081021fb8401081006cff76544100167e65544100067d6554410006be6454410006bd645441018ede6354410006dd6354410006ee6254410006ed6254410004fd76d04101867e65d04100067d65d0410046be64d0410006bd64d041017ede63d0410006dd63d0410006ee62d0410006ed62d041001df870d0410004ff76504100057f75504100357c755041016e7e65504100067d6550410046be6450410006bd6450410166de6350410006dd6350410006ee6250410006ed6250410005fb705041001df87050410004fd76c84100357e75c84100057d75c84101467e65c84100067d65c8410006be64c8410006bd64c8410126de63c8410006dd63c8410076ee62c8410006ed62c8410004ff76484101367e65484100067d6548410006be6448410006bd6448410005df734841002ddc734841012ede6348410006dd6348410006ee6248410006ed6248410027e4214841001df976d0010206f976d00102077a75d00102077975d001001f7a65d001001f7965d001001dfa74d001001fba74d001001efb64d001001fba64d0010206f964d001001fb964d0010006b964d001001efb63d001001fda63d0010216f963d001001fd963d0010006d963d001001fea62d001001fe962d0010005f971d001020efa61d001001ff261d0010207bb41d0010007b941d001001dfb7644010006fb7644010004fb76440100077b754401000778754401001f7a654401001f796544010007bb7444010205fa7444010205f87444010007b87444010005b8744401001fba644401001fb9644401001efb634401001fda63440101fef9634401001fd96344010006d9634401001fea624401001fe9624401001dfb714401001ff37144010026fa614401001ff26144010027f25144010007f151440101fff33144010027f03144010027f22144010007f12144010
  | 1 => 0x8810026ec219881001cfe709881001cfc709881001eee209881001eec2098810076ef7598810006ee7598810006ed7598810076ec7598810076ef7498810006ee7498810006ed7498810076ec7498810006ef5498810006ee5498810006ed5498810006ec5498810076ef7398810006ee7398810006ed7398810076ec7398810006ef5398810006ee5398810006ed5398810006ec5398810006ef4398810006ee4398810006ed4398810006ec4398810026ee7198810026ec7198810006ef5198810026ee5198810026ec5198810026ee4198810026ec4198810006ef3198810026ee3198810006ed3198810026ec319881001eef709881001eee709881001eed709881001eec709881001eef509881001eee509881001eed509881001eec509881001eef409881001eee409881001eed409881001eec409881001eef309881001eee309881001eed309881001eec309881001eef109881001eee109881001eed109881001eec1098810004ff7558810014fe7558810014fc7558810004ff7458810044fc7458810004ff735881000cfe7358810004fd735881000cfc735881001cff725881001eef7258810006ef5258810006ec5258810006ef3258810006ee3258810006ed3258810006ec3258810074ff7158810024fe715881012cfd7158810024fc7158810026ee2158810026ec215881001cff705881001cfe705881001cfd705881001cfc705881001eee205881001eec2058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810026ee7158810026ec7158810006ef5158810026ee5158810026ec5158810026ee4158810026ec4158810006ef3158810026ee3158810006ed3158810026ec315881001eef705881001eee705881001eed705881001eec705881001eef505881001eee505881001eed505881001eec505881001eef405881001eee405881001eed405881001eec405881001eef305881001eee305881001eed305881001eec305881001eef105881001eee105881001eed105881001eec1058810074ff769481001cfe7694810004fd769481001cfc76948100167e65948100067d6594810006be6494810006bd64948101e6de6394810006dd6394810076ee6294810006ed6294810004ff765481001cfe7654810004fd765481001cfc76548100167e65548100067d6554810005bf7454810005bc7454810006be6454810006bd64548101dede6354810006dd6354810006ee6254810006ed6254810005f
  | 2 => 0x4fd735901000cfc7359010006bf4359010006be4359010006bd4359010006bc4359010004ff7259010074fc7259010044ff7159010024fe7159010044fd7159010024fc7159010026be4159010026bc415901001cff705901001cfe705901001cfd705901001cfc705901001ef8705901001cf8705901001ebe405901001ebc405901001ef84059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006bc5259010006bf3259010006be3259010006bd3259010006bc3259010026be7159010026bc7159010006bf5159010026be5159010026bc5159010006bf3159010026be3159010006bd3159010026bc3159010026be2159010026bc215901001ebf705901001ebe705901001ebd705901001ebc705901001eb8705901001ebf505901001ebe505901001ebd505901001ebc505901001ebf305901001ebe305901001ebd305901001ebc305901001ebf205901001ebe205901001ebd205901001ebc205901001ebf105901001ebe105901001ebd105901001ebc1059010044ff769501001cfe7695010004fd769501001cfc76950100167e65950100067d6595010046be6495010006bd64950100373f54950101f6de6395010237b84095010004ff765501001cfe7655010004fd765501001cfc76550100167e65550100067d6555010046be6455010006bd64550101eede6355010005fb705501001df8705501022fb84055010006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006dc5258c1002edf7158c10026de7158c1002edd7158c10026dc7158c10006df5158c10026de5158c10026dc5158c10026de4158c10026dc4158c10026de2158c10026dc2158c1001edf7058c1001ede7058c1001edd7058c1001edc7058c1001edf5058c1001ede5058c1001edd5058c1001edc5058c1001edf4058c1001ede4058c1001edd4058c1001edc4058c1001ed84058c1001edf2058c1001ede2058c1001edd2058c1001edc2058c1001edf1058c1001ede1058c1001eda1058c1001edd1058c1001edc1058c10014fe7598810004fd7598810074fc7598810044fe7498810004fd7498810074ff739881000cfe7398810004fd7398810074fc739881001cfe729881001eee7298810006ef5298810076ec5298810006ef3298810076ee3298810006ed3298810076ec3298810024fe7198810024fc7198810026ee219
  | 3 => 0xf6448110006bc6448110006ef6248110006ec6248110005f77148110005f4714811001ff010481100067f65c411006e7c65c4110006bf64c4110006bc64c411001df671c411001ef761c411001dfa76c411001efa76c411001cfa76c41100077b65c41100077865c4110007bb64c411020efa64c411020ef864c4110007b864c4110006b864c4110025fb73c411023df973c411001dfa71c411001efb61c411001ff361c411001cff755941001e7f7559410004ff7459410044fc74594100367f54594100367c5459410004ff735941000cfe7359410004fd735941000cfc73594100367f53594100067e53594100067d53594100367c5359410004ff7259410074fc72594100367f52594100367c5259410014ff7159410024fe7159410014fd7159410024fc71594100267e51594100267c515941001cff705941001cfe705941001cfd705941001cfc705941001e7e505941001e7c50594100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f32594100067e32594100067d32594100067c32594100367f71594100267e71594100267c71594100267e41594100267c41594100067f31594100267e31594100067d31594100267c31594100267e21594100267c215941001e7f705941001e7e705941001e7d705941001e7c705941001e7f405941001e7e405941001e7d405941001e7c405941001e7f305941001e7e305941001e7d305941001e7c305941001e7f205941001e7e205941001e7d205941001e7c205941001e7f105941001e7e105941001e7d105941001e7c1059410046bf7599010046be7599010046bd7599010046bc7599010046bf7399010046be7399010046bd7399010046bc7399010006bf5399010006be5399010006bd5399010006bc5399010046bf7299010046be7299010046bd7299010046bc7299010006bf5299010006bc5299010006bf3299010006be3299010006bd3299010006bc3299010026be7199010026bc7199010006bf5199010026be5199010026bc5199010006bf3199010026be3199010006bd3199010026bc3199010026be2199010026bc219901001ebf709901001ebe709901001ebd709901001ebc709901001ebf509901001ebe509901001ebd509901001ebc509901001ebf309901001ebe309901001ebd309901001ebc309901001ebf209901001ebe209901001ebd209901001ebc209901001ebf109901001ebe109901001ebd109901001ebc1099010004ff7559010014fe7559010014fc755901001cff745901001ebf7459010006bf5459010006bc5459010004ff735901000cfe7359010
  | 4 => 0x49100067f65549100167c6554910005bf7454910005bc7454910006bf6454910006bc6454910044ff76d0910004fe76d0910004fd76d0910044fc76d09100067f65d09101d67c65d0910006bf64d0910046bc64d0910074ff7690910004fe7690910004fd7690910074fc76909100067f65909101c67c6590910006bf6490910046bc6490910004ff7650910004fe7650910004fd7650910004fc76509100057f75509100557c75509100067f65509101be7c6550910006bf6450910046bc6450910074ff7610910004fe7610910004fd7610910074fc76109100557e75109100057d75109100067f65109101a67c6510910006bf6410910046bc6410910005f67110910005f5711091001dfa7010910005f97010910064fe76945100067f65945100167c6594510006bf6494510006bc649451001cfc76545100067f65545100167c6554510006bf6454510006bc6454510005fb705451001df8705451001cfe76d051001cfc76d05100067f65d05101867c65d0510006bf64d0510046bc64d051001dfa70d0510005f970d0510004fe76905100067f65905101767c6590510006bf6490510046bc649051001cfc76505100057f75505100557c75505100067f655051016e7c6550510006bf6450510046bc6450510005fb705051001df87050510004fe76105100557e75105100057d75105100067f65105101567c6510510006bf6410510046bc641051001cfe76c85100557e75c85100057d75c85100067f65c85101467c65c8510006bf64c8510006bc64c8510006ef62c8510076ec62c851001dfa70c8510005f970c8510004fe76885100557e75885100057d75885100067f658851013e7c6588510005be7488510005bd7488510006bf6488510006bc648851001cfc76485100067f65485101367c6548510006bf6448510006bc6448510005df734851004ddc7348510006ef6248510006ec6248510005fb704851001df87048510004fe76085100067f65085101167c6508510006bf6408510006bc6408510014ff7654110054fd7654110014fc76541100067f65541100167c6554110006bf6454110006bc6454110005f77154110005f4715411001ff01054110004fe76d0110024fc76d01100557e75d01100057d75d01100067f65d01100f67c65d0110006bf64d0110046bc64d0110005f671d0110005f571d0110044ff7650110004fd7650110044fc76501100067f65501100d67c6550110006bf6450110046bc6450110005f77150110005f47150110004fe76c81100067f65c81100b67c65c8110006bf64c8110006bc64c8110006ef62c8110076ec62c8110005f671c8110005f571c8110074ff7648110004fd7648110004fc76481100057f75481100557c75481100067f654811009e7c6548110005bf7448110005bc7448110006b
  | 5 => 0x46bd7219110046bc7219110006bf5219110006bc5219110006bf3219110006be3219110006bd3219110006bc3219110046bf7119110046bd7119110006bf5119110006bc5119110006bf3119110006be3119110006bd3119110006bc3119110046bf7019110046be7019110046bd7019110046bc7019110006bf5019110246be5019110246bc5019110006bf3019110246be3019110006ba3019110006bd3019110006b93019110246bc3019110246be2019110246bc2019110246be1019110006bd1019110246bc1019110044ff7695110004fe7695110004fd7695110044fc76951100067f65951100167c6595110006bf6495110046bc64951100573f5495110004ff7655110004fe7655110004fd7655110004fc76551100067f65551100167c6555110006bf6455110046bc64551100067f65d89100067c65d8910006bf64d8910006bc64d8910014fe75d8910004fd75d8910014fc75d8910044fe74d8910004fd74d8910004ff73d891000cfe73d8910004fd73d891000cfc73d8910006ef32d8910006ec32d8910006fa30d8910006f930d89100557e75989100057d75989100067f65989100067c6598910005be7498910005bd7498910006bf6498910006bc6498910006ef6298910014fe75989100767e75989100147e7598910004fd75989100767d75989100047d7598910074fc7598910044fe7498910076be7498910044be7498910004fd7498910076bd7498910004bd7498910074ff739891000cfe7398910004fd7398910074fc7398910074fe7298910004fd7198910076f57198910004fd7098910076f970989100057f75589100557c75589100067f65589100067c6558910005bf7458910005bc7458910006bf6458910006bc6458910005df735891004ddc7358910004ff75589100067f75589100047f7558910014fe7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf7458910044fc7458910006bc7458910044bc7458910004ff7358910006df7358910004df735891000cfe7358910004fd735891000cfc7358910006dc735891000cdc7358910006ef7258910004ff7158910006f77158910004ff7058910006fb7058910006fa3058910006f93058910004fe76189100067f65189100067c6518910006bf6418910006bc6418910006ed6218910014fe7518910004fd7518910074fc7518910044fe7418910004fd7418910074ff731891000cfe7318910004fd7318910074fc7318910076ee7218910006ef3218910076ec3218910024fe7118910024fc711891001cfe701891001cfc7018910074ff7694910004fe7694910004fd7694910074fc76949100067f65949100167c6594910006bf6494910006bc6494910004ff7654910004fe7654910004fd7654910004fc765
  | 6 => 0xe7359510004fd735951000cfc7359510004ff7259510074fc7259510064ff7159510006f7715951006cff7059510006fb70595100057e76195100567e76195100047e76195100067f63195100067e63195100067d63195100067c63195102567f61195100077a3019510007793019510257761019510257741019510044fe76d91100067f65d91100067c65d9110014fe75d9110004fd75d9110014fc75d9110006bf54d9110006bc54d9110004ff73d911000cfe73d9110004fd73d911000cfc73d9110006bf43d9110006be43d9110006bd43d9110006bc43d9110074fe72d9110004fd72d9110024fe71d9110024fc71d911001cfe70d911001cfc70d9110044be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d9110007ba30d9110007b930d911024fb610d911024fb410d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d911024ebf71d9110006bd71d9110006bf51d9110006bc51d9110006bf31d9110006be31d9110006bd31d9110006bc31d9110006bf70d911024ebe70d9110006bd70d911024ebc70d9110006bf50d911024ebe50d911024ebc50d9110006bf30d911024ebe30d9110006bd30d911024ebc30d911024ebe20d911024ebc20d911024ebe10d911024ebc10d91100557e75991100057d75991100067f65991100067c6599110006bf64991100057f75591100557c75591100067f65591100067c6559110004ff75591100067f75591100047f7559110014fe7559110014fc75591100067c75591100147c7559110006bf7459110004ff735911000cfe7359110004fd735911000cfc7359110004ff7259110074fc7259110004ff7159110006f77159110004ff7059110006fb7059110004fb7059110004fe76191100067f65191100067c6519110046be6419110006bd6419110005be7619110006be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006bf6319110006be6319110006bd6319110006bc6319110007ba3019110007b93019110247b61019110247b41019110046bf7519110046be7519110046bd7519110046bc7519110046bf7319110046be7319110046bd7319110046bc7319110006bf5319110006be5319110006bd5319110006bc5319110046bf7219110046be7219110
  | 7 => 0x4a100167e6554a100067d6554a10005bf7454a10005bc7454a10044ff76d0a1001cfe76d0a10004fd76d0a1001cfc76d0a10074ff7690a1001cfe7690a10004fd7690a1001cfc7690a10226bf6490a10046bc6490a10004ff7650a1001cfe7650a10004fd7650a1001cfc7650a100057f7550a100657c7550a10074ff7610a1001cfe7610a10004fd7610a1001cfc7610a100657e7510a100057d7510a1021ebf6410a10046bc6410a1001dfa7010a10005f97010a10054fd769461025e7f65946100167c6594610067775194610014ff765461001cfc76546100167e65546100067d6554610005fb705461001df87054610046be64d0610006bd64d061001dfa70d0610005f970d061024ebf6490610046bc6490610044ff76506100057f75506100657c7550610046be6450610006bd6450610005fb705061001df870506100657e75106100057d7510610246bf6410610046bc64106100657e75c86100057d75c8610076ee62c8610006ed62c861001dfa70c8610005f970c86100657e75886100057d7588610005be7488610005bd7488610005df734861005ddc7348610006ee6248610006ed6248610005fb704861001df87048610007e5210861001df976c4210026f976c421020efa64c421001ef864c4210025fb73c4210265f973c421001ff271c4210014fe76d95100567e65d9510044fe74d9510004fd74d95100567f54d95100567c54d9510004ff73d951000cfe73d9510004fd73d951000cfc73d95100567f53d95100067e53d95100067d53d95100567c53d9510074fe72d9510004fd72d95100567f52d95100567c52d9510024fe71d951001cfd71d9510024fc71d95100567f51d951001cfe70d9510054fd70d951001cfc70d95100567f50d95100557e76d95100147e76d95100067f63d95100067e63d95100067d63d95100067c63d95100077a30d95100077930d951025f7610d951025f7410d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f32d95100067e32d95100067d32d95100067c32d951025e7f71d95100567e71d95100067d71d95100067f31d95100067e31d95100067d31d95100067c31d95100067f70d951025e7e70d95100067d70d951025e7c70d951025e7e40d951025e7c40d95100067f30d951025e7e30d95100067d30d951025e7c30d951025e7e20d951025e7c20d951025e7e10d951025e7c10d95100567c6559510005bf7459510005bc7459510054ff75595100067f7559510004ff7459510006bf7459510004bf7459510044fc7459510006bc7459510044bc7459510004ff735951000cf
  | 8 => 0x6d7c7550710026bf6450710026bc645071001df8705071006d7e75c87100057d75c8710026ef62c8710026ec62c8710005df734871003ddc7348710026ef6248710026ec6248710014ff7654310024fc76543100167e65543100067d6554310005f77154310025f4715431006d7e75d03100057d75d0310046be64d0310006bd64d0310025f671d0310005f571d0310005f976d031020ef976d031020f7a75d031020f7975d031001dfa74d031020efb64d031020fba64d031020ef964d0310007b964d0310286fb63d0310286f963d031020ff271d0310005f971d031020ff171d031001efa61d031020fbb41d0310007b941d0310044ff7650310046be6450310006bd6450310005f77150310025f4715031001fb84050310005f9761031001ef9761031001fba741031020efb6410310277bb641031020ef96410310277b8641031020fba5410310007b9541031001fda731031001fd9731031027efb631031027ef9631031020fbb431031027fb94310310007ba421031020fb84210310005f9711031001ff26110310277ba4110310277b84110310076ee62c8310006ed62c8310025f671c8310005f571c83100057f754831006d7c7548310005bf7448310005bc7448310006ee6248310006ed6248310005f77148310025f4714831001e7f7559610004ff7459610044fc74596100667c5459610004ff735961000cfe7359610004fd735961000cfc7359610004ff7259610074fc72596100667f52596100667f515961001cfc705961001e7e505961001e7c5059610004ff7559210014fe7559210014fc755921001ebf7459210004ff735921000cfe7359210004fd735921000cfc7359210004ff7259210074fc725921001cfc705921001ebe405921001ebc4059210044ff769521001cfe7695210004fd769521001cfc76952100167e65952100067d6595210236bf6495210046bc64952100673f5495210004ff765521001cfe7655210004fd765521001cfc765521022e7f65552100167c655521022ebf6455210046bc6455210014fe7598a10004fd7598a10074fc7598a10044fe7498a10004fd7498a10074ff7398a1000cfe7398a10004fd7398a10074fc7398a1001eee7298a1001cfe7098a1001eee2098a1001eec2098a10004ff7558a100067f7558a100047f7558a10014fe7558a10014fc7558a100067c7558a100147c7558a10004ff7458a10006bf7458a10004bf7458a10044fc7458a10006bc7458a10044bc7458a10004ff7358a1000cfe7358a10004fd7358a1000cfc7358a1001eef7258a1001cfc7058a1001efa3058a10006f93058a1001eee2058a1001eec2058a10074ff7694a1001cfe7694a10004fd7694a1001cfc7694a1026e7f6594a100167c6594a10004ff7654a1001cfe7654a10004fd7654a1001cfc765
  | 9 => 0xf76593100057f755931006d7c7559310026bc6459310004ff75593100067f75593100047f7559310014fe7559310014fc75593100067c75593100147c7559310026bf7459310004ff735931000cfe7359310004fd735931000cfc7359310006bf4359310006bd4359310004ff7259310074fc725931001cfc7159310026be4159310026bc4159310006fb7059310044ff7695310024fe7695310004fd7695310024fc76953100067f65953100167c6595310046be6495310006bd649531006f3f5495310004ff7655310024fe7655310004fd7655310024fc76553100167e65553100067d6555310046be6455310006bd6455310005fb705531001df87055310014fe75d8b100267e75d8b100147e75d8b10004fd75d8b100267d75d8b100047d75d8b10024fc75d8b10044fe74d8b10026be74d8b10044be74d8b10004fd74d8b10026bd74d8b10004bd74d8b10024ff73d8b1000cfe73d8b10004fd73d8b10024fc73d8b10026f671d8b10026f970d8b10004fd7698b1006d7e7598b100057d7598b10026ef6298b10014fe7598b100767e7598b100147e7598b10004fd7598b100767d7598b100047d7598b10074fc7598b10044fe7498b10004fd7498b10074ff7398b1000cfe7398b10004fd7398b10074fc7398b10076ee3298b10006ed3298b1001cfe7198b10026ee2198b10026ec2198b10005df7358b1003ddc7358b10026ec6258b10004ff7558b10014fe7558b10014fc7558b10004ff7458b10044fc7458b10004ff7358b10006df7358b10004df7358b1000cfe7358b10004fd7358b1000cfc7358b10006dc7358b1000cdc7358b10026ef7258b10006ee3258b10006ed3258b1001cfc7158b10026ee2158b10026ec2158b10014fe7518b10004fd7518b10024fc7518b10044fe7418b10004fd7418b10024ff7318b1000cfe7318b10004fd7318b10024fc7318b10074fe7218b10026ee7218b10026f67118b10026f97018b10074ff7694b10024fe7694b10004fd7694b10024fc7694b100167e6594b100067d6594b10004ff7654b10024fe7654b10004fd7654b10024fc7654b100067f6554b100167c6554b10005bf7454b10005bc7454b10005fb7054b1001df87054b10044ff76d0b10024fe76d0b10004fd76d0b10024fc76d0b10074ff7690b10024fe7690b10004fd7690b10024fc7690b10046be6490b10006bd6490b1001dfa7090b10005f97090b10004ff7650b10024fe7650b10004fd7650b10024fc7650b100057f7550b1006d7c7550b10005fb7050b1001df87050b10074ff7610b10024fe7610b10004fd7610b10024fc7610b1006d7e7510b100057d7510b10046be6410b10006bd6410b10025f67110b10005f57110b10034ff76547100267f65547100267c6554710026bf64d0710026bc64d07100057f7550710
  | 10 => 0x4820004fd76d08201d67e65d08200067d65d0820004ff76508200057f75508200857c75508201be7e65508200067d6550820014fe7598420004fd7598420024fc7598420044fe7498420004fd7498420024ff739842000cfe7398420004fd7398420024fc739842001ef67198420026f63198420006f53198420076f72198420026f4219842001ef6109842001ef41098420004ff7558420014fe7558420014fc7558420004ff7458420044fc7458420004ff735842000cfe7358420004fd735842000cfc735842001ef77158420006f63158420006f53158420076f72158420076f4215842001eef205842001eed205842001ef6105842001ef41058420024ff769442001cfe7694420004fd76944200167e65944200067d6594420004ff7654420004fd765442001cfc76544200167e65544200067d6554420005fb705442001df87054420044ff76d042001cfe76d0420004fd76d04201867e65d04200067d65d0420046be64d0420006bd64d0420024ff769042001cfe7690420004fd76904201767e65904200067d6590420026f66190420006f56190420004ff7650420004fd765042001cfc76504200057f75504200857c755042016e7e65504200067d6550420046be6450420006bd6450420006f66150420006f56150420005fb705042001df87050420024ff761042001cfe7610420004fd76104200857e75104200057d75104201567e65104200067d6510420004fd76884200857e75884200057d758842013e7e65884200067d6588420005be7488420005bd7488420004ff76484201367e65484200067d6548420005df734842007ddc7348420296ee6248420077e4214842001dfb7648020006fb7648020004fb76480200077b754802000778754802001f7a654802001f796548020007bb7448020007b8744802001efb634802028ef9634802001dfb724802001feb7248020076fa624802001fea6248020077ea5248020007e9524802006cfd75d9710044fe74d9710004fd74d971006e7c54d9710024ff73d971000cfe73d9710004fd73d9710024fc73d9710074fe72d9710004fd72d971006e7f52d9710026f671d97100267f51d9710026f970d971025e7e50d971025e7c50d9710014ff76597100267c65597100267f7559710004ff7459710044fc745971006e7f5459710004ff735971000cfe7359710004fd735971000cfc735971006e7f53597100067d5359710004ff7259710074fc725971006e7c525971001cfc71597100267e51597100267c515971006e7f5059710014fe75d9310004fd75d9310024fc75d9310024ff73d931000cfe73d9310004fd73d9310024fc73d9310074fe72d9310004fd72d9310026f671d9310026f970d931024ebe40d931024ebc40d9310004fd7699310026bf6499310026bc6499310044f
  | 11 => 0x1167c6508520006bf6408520006bc64085202a5ee7208520014ff765412009cfd7654120014fc76541200067f65541200167c6554120006bf6454120006bc6454120005ef7254120005ec725412001fe82054120004fe76d0120074fc76d012009d7e75d01200057d75d01200067f65d01200f67c65d0120006bf64d0120046bc64d0120005ee72d0120005ed72d0120044ff7650120004fd7650120044fc76501200067f65501200d67c6550120006bf6450120046bc6450120005ef7250120005ec725012001fb840501200067f65c81200b67c65c8120006bf64c8120006bc64c812001dee72c812001eef62c81200077b65c81200077865c8120007bb64c8120007b864c8120075fb73c812029df973c812001dfa72c812001efb62c812001feb62c8120077eb21c8120007e921c812001cff755942001e7f7559420004ff7459420044fc74594200867f54594200867c5459420004ff735942000cfe7359420004fd735942000cfc73594200867f53594200067e53594200067d53594200867c5359420014ff7259420074fe7259420014fd7259420074fc72594200767e52594200767c5259420004ff7159420024fc71594200867f51594200867c515942001cfe705942001cfc705942001e7e505942001e7c50594200067f74594200067e74594200067d74594200067c74594200067f73594200067e73594200067d73594200067c73594200067f43594200067e43594200067d43594200067c43594200867f72594200767e72594200767c72594200767e42594200767c42594200067f32594200767e32594200067d32594200767c32594200067f71594200067e71594200067d71594200067c71594200067f31594200067e31594200067d31594200067c31594200767f21594200767c215942001e7f705942001e7e705942001e7d705942001e7c705942001e7f405942001e7e405942001e7d405942001e7c405942001e7f305942001e7e305942001e7d305942001e7c305942001e7f205942001e7e205942001e7d205942001e7c205942001e7f105942001e7e105942001e7d105942001e7c1059420004ff7559020014fe7559020014fc755902001cff745902001ebf7459020004ff735902000cfe7359020004fd735902000cfc7359020006bf4359020006bd4359020044ff7259020074fe7259020044fd7259020074fc7259020076be4259020076bc4259020004ff7159020024fc715902001cfe705902001cfc705902001ebe405902001ebc4059020044ff769502001cfe7695020004fd769502001cfc76950200167e65950200067d65950200873f5495020004ff765502001cfe7655020004fd765502001cfc76550200167e65550200067d65550200b4ff76548200167e65548200067d6554820005bf7454820005bc745
  | 12 => 0xd73d852000cfc73d8520006f731d8520006f431d8520006fa30d8520006f930d852009d7e75985200057d75985200067f65985200067c6598520005be7498520005bd7498520006bf6498520006bc6498520006f761985200057f755852009d7c75585200067f65585200067c6558520005bf7458520005bc7458520006bf6458520006bc6458520005df7358520095dc73585200067f65185200067c6518520006bf6418520006bc6418520006f56118520014fe7518520004fd7518520024fc7518520044fe7418520004fd7418520024ff731852000cfe7318520004fd7318520024fc7318520006f73118520026f4311852001cfe701852001cfc7018520004fe7694520004fd7694520024fc76945200067f65945200167c6594520006bf6494520006bc6494520005ee7294520005ed7294520004ff7654520004fe7654520004fc76545200067f65545200167c6554520006bf6454520006bc6454520004fe76d0520004fd76d0520044fc76d05200067f65d05201867c65d0520006bf64d0520046bc64d0520004fe7690520004fd7690520024fc76905200067f65905201767c6590520006bf6490520046bc6490520005ee7290520005ed7290520004ff7650520004fe7650520004fc76505200057f755052009d7c75505200067f655052016e7c6550520006bf6450520046bc6450520005fb705052001df87050520004fe7610520004fd7610520024fc761052009d7e75105200057d75105200067f65105201567c6510520006bf6410520046bc6410520005ee7210520005ed721052001dfa7010520005f97010520004fe76c852009d7e75c85200057d75c85200067f65c85201467c65c8520006bf64c8520006bc64c8520005ee76c8520006ee76c85200076e75c85200076d75c85200076f65c85200076c65c8520007af64c8520007ac64c85202beef63c85202beed63c8520026ec61c852001dee70c852001dec70c8520076ef60c85202bfea30c85202bfe930c852001cfe768852009d7e75885200057d75885200067f658852013e7c6588520005be7488520005bd7488520006bf6488520006bc64885202b5ed7288520006f76188520026f4618852001dfa7088520005f9708852001cfc76485200067f65485201367c6548520006bf6448520006bc6448520005df7348520095dc7348520006f76148520006f46148520005fb704852001df8704852001cec76485200076f65485200076c6548520007af6448520007ac6448520007cf73485202afcc73485202aeef63485202aeed6348520007e77148520007e76148520026ec6148520007e46148520006e461485202afe631485202afe53148520007eb704852001dee704852001dec7048520007e870485202afea30485202afe93048520004fe76085200067f6508520
  | 13 => 0x91200057d75991200067f65991200067c6599120006bf64991200057f755912009d7c75591200067f65591200067c6559120004ff75591200067f75591200047f7559120014fe7559120014fc75591200067c75591200147c7559120006bf7459120004ff735912000cfe7359120004fd735912000cfc7359120004ff7259120006ef7259120004ff7159120024fc7159120004ff7059120006fb7059120004fe76191200067f65191200067c6519120046be6419120006bd6419120005be7619120006be7619120004be7619120006bf65191200073f65191200063f6519120006be6519120006bd6519120006bc65191200073c65191200063c6519120006bf6319120006be6319120006bd6319120006bc6319120007ba3019120007b9301912021fae201912021fac2019120046bf7519120046be7519120046bd7519120046bc7519120046bf7319120046be7319120046bd7319120046bc7319120006bf5319120006be5319120006bd5319120006bc5319120046bf7219120046bd7219120006bf5219120006bc5219120006bf3219120006be3219120006bd3219120006bc3219120046bf7119120046be7119120046bd7119120046bc7119120006bf5119120006bc5119120006bf3119120006be3119120006bd3119120006bc3119120046bf7019120046be7019120046bd7019120046bc7019120006bf501912021ebe501912021ebc5019120006bf301912021ebe3019120006ba3019120006bd3019120006b9301912021ebc301912021ebe2019120006bd201912021ebc201912021ebe101912021ebc1019120044ff7695120004fe7695120004fd7695120044fc76951200067f65951200167c6595120006bf6495120046bc649512009f3f5495120004ff7655120004fe7655120004fd7655120004fc76551200067f65551200167c6555120006bf6455120046bc64551200acfe76949200067f65949200167c6594920006bf6494920006bc649492009f6f529492001cfc76549200067f65549200167c6554920005bf7454920005bc7454920006bf6454920006bc6454920005fb705492001df8705492001cfe76d092001cfc76d09200067f65d09201d67c65d0920006bf64d0920046bc64d092001dfa70d0920005f970d0920004fe76909200067f65909201c67c6590920006bf6490920046bc649092001cfc76509200057f755092009d7c75509200067f65509201be7c6550920006bf6450920046bc6450920005fb705092001df87050920004fe761092009d7e75109200057d75109200067f65109201a67c6510920006bf6410920046bc64109200067f65d85200067c65d8520006bf64d8520006bc64d8520014fe75d8520004fd75d8520014fc75d8520044fe74d8520004fd74d8520004ff73d852000cfe73d8520004f
  | 14 => 0x9e7f51d952009e7c51d952009cfd70d952009e7f50d952009d7e76d95200147e76d95200067f63d95200067e63d95200067d63d95200067c63d95200077a30d95200077930d952026f6e20d952026f6c20d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d952026e7f72d952009e7e72d95200067d72d95200067f32d95200067e32d95200067d32d95200067c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f31d95200067e31d95200067d31d95200067c31d95200067f70d952026e7e70d95200067d70d952026e7c70d952026e7e40d952026e7c40d95200067f30d952026e7e30d95200067d30d952026e7c30d952026e7e20d952026e7c20d952026e7e10d952026e7c10d952009e7c6559520005bf7459520005bc745952009cff75595200067f7559520004ff7459520006bf7459520004bf7459520044fc7459520006bc7459520044bc7459520004ff735952000cfe7359520004fd735952000cfc73595200acff7259520006ef7259520004ff7159520024fc71595200b4ff7059520006fb70595200057e761952009e7e76195200047e76195200067f63195200067e63195200067d63195200067c63195202c67f62195200077a30195200077930195202c76e20195202c76c2019520044fe76d91200067f65d91200067c65d9120014fe75d9120004fd75d9120014fc75d9120006bf54d9120006bc54d9120004ff73d912000cfe73d9120004fd73d912000cfc73d9120006bf43d9120006be43d9120006bd43d9120006bc43d9120074fe72d9120074fc72d9120024fe71d9120004fd71d9120044be76d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d9120006bf63d9120006be63d9120006bd63d9120006bc63d9120007ba30d9120007b930d9120227ae20d9120227ac20d9120006bf75d9120006be75d9120006bd75d9120006bc75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006be53d9120006bd53d9120006bc53d9120226bf72d9120006bd72d9120006bf52d9120006bc52d9120006bf32d9120006be32d9120006bd32d9120006bc32d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006bc51d9120006bf31d9120006be31d9120006bd31d9120006bc31d9120006bf70d9120226be70d9120006bd70d9120226bc70d9120006bf50d9120226be50d9120226bc50d9120006bf30d9120226be30d9120006bd30d9120226bc30d9120226be20d9120226bc20d9120226be10d9120226bc10d912009d7e759
  | 15 => 0xf6594a200167c6594a201e6de6394a20006dd6394a20014ff7654a2001cfc7654a200167e6554a200067d6554a20005bf7454a20005bc7454a201dede6354a20006dd6354a20005fb7054a2001df87054a20046be64d0a20006bd64d0a201cede63d0a20006dd63d0a2001dfa70d0a20005f970d0a20226bf6490a20046bc6490a201aede6390a20006dd6390a20044ff7650a200057f7550a200ad7c7550a20046be6450a20006bd6450a201b6de6350a20006dd6350a20005fb7050a2001df87050a200ad7e7510a200057d7510a2021ebf6410a20046bc6410a2019ede6310a20006dd6310a20014fe7598620004fd7598620024fc7598620044fe7498620004fd7498620024ff739862000cfe7398620004fd7398620024fc739862001ef6719862001ef6109862001ef41098620004ff75586200067f75586200047f7558620014fe7558620014fc75586200067c75586200147c7558620004ff7458620044fc7458620004ff735862000cfe7358620004fd735862000cfc735862001ef7715862001efa3058620006f9305862001eef205862001eed205862001ef6105862001ef41058620024ff769462001cfe7694620004fd769462025e7f65946200167c6594620196de6394620006dd6394620004ff7654620004fd765462001cfc76546200167e65546200067d655462018ede6354620006dd6354620044ff76d062001cfe76d0620004fd76d0620046be64d0620006bd64d062017ede63d0620006dd63d0620024ff769062001cfe7690620004fd769062015ede6390620006dd6390620004ff7650620004fd765062001cfc76506200057f75506200ad7c7550620046be6450620006bd6450620166de6350620006dd6350620005fb705062001df87050620024ff761062001cfe7610620004fd76106200ad7e75106200057d751062014ede6310620006dd631062001dfa7010620005f970106200ad7e75c86200057d75c8620126de63c8620006dd63c86200ad7e75886200057d7588620005be7488620005bd748862011ede6388620006dd6388620026f66188620006f5618862001dfa7088620005f97088620005df73486200a5dc734862012ede6348620006dd6348620006f66148620006f56148620005fb704862001df8704862010ede6308620006dd6308620007e5210862001df976c8220076f976c8220075fb73c82202cdf973c822001fda63c822001fd963c822001fea72c8220077ea52c8220007e952c8220014fe76d952009e7e65d9520044fe74d9520004fd74d952009e7f54d952009e7c54d9520004ff73d952000cfe73d9520004fd73d952000cfc73d952009e7f53d95200067e53d95200067d53d952009e7c53d9520074fe72d952001cfd72d9520074fc72d952009e7f52d9520024fe71d9520004fd71d9520
  | 16 => 0x4720005fb705472001df87054720044ff76d0720074fe76d0720004fd76d0720006bf64d0720046bc64d0720024ff7690720074fe7690720004fd7690720046be6490720006bd6490720075ee7290720005ed7290720004ff7650720004fd7650720074fc76507200057f75507200b57c7550720006bf6450720046bc6450720005fb705072001df87050720024ff7610720074fe7610720004fd76107200b57e75107200057d7510720046be6410720006bd6410720075ee7210720005ed721072001ced76c87200776e75c87200776d75c8720076ef63c87202d6ed63c8720026ee61c8720077e661c8720077e561c872001dee70c8720077ea70c8720077e970c872001dec70c87200b57e75887200057d7588720005be7488720005bd7488720005df734872008ddc7348720005ef7648720006ef7648720007cf7348720297cc7348720296ef6348720296ed6348720077e77148720026ee6148720297e63148720297e5314872001dee704872001dec7048720014ff7654320074fc76543200167e65543200067d6554320005ef7254320075ec725432001fea20543200b57e75d03200057d75d0320046be64d0320006bd64d0320075ee72d0320005ed72d0320044ff7650320046be6450320006bd6450320005ef7250320075ec725032001e7f7559620004ff7459620044fc74596200ae7c5459620004ff735962000cfe7359620004fd735962000cfc73596200ae7f5259620004ff7159620024fc71596200ae7f515962001cfc705962001e7e505962001e7c5059620004ff7559220014fe7559220014fc755922001ebf7459220006bf5459220006bc5459220004ff735922000cfe7359220004fd735922000cfc7359220004ff7159220024fc715922001cfc705922001ebe405922001ebc4059220044ff769522001cfe7695220004fd769522001cfc76952200167e65952200067d65952200af3f54952201f6de6395220004ff765522001cfe7655220004fd765522001cfc765522022e7f65552200167c65552201eede6355220006df7558e20006de7558e20006dd7558e20006dc7558e20006df7458e20006de7458e20006dd7458e20006dc7458e20006df5458e20006de5458e20006dd5458e20006dc5458e200a6df7258e200a6de7258e20006dd7258e200a6dc7258e20006df5258e20006dc5258e20006df7158e20006de7158e20006dd7158e20006dc7158e20006df5158e20006dc5158e2001edf7058e2001ede7058e2001edd7058e2001edc7058e2001edf5058e2001ede5058e2001edd5058e2001edc5058e2001edf4058e2001ede4058e2001edd4058e2001edc4058e2001edf2058e2001ede2058e2001edd2058e2001edc2058e2001edf1058e2001ede1058e2001edd1058e2001edc1058e2009cfd7694a2026e7
  | 17 => 0x5bf7448440045bc7448440005df73484400bddc734844012ede6348440006dd6348440006ee6248440006ed6248440006f66148440006f56148440005fb704844001df87048440024ff760844001cfe7608440004fd7608440005bf7408440045bc740844010ede6308440006dd63084400b4fd75d9720044fe74d9720004fd74d97200b67c54d9720074ff73d972000cfe73d9720004fd73d9720074fc73d9720076ee72d97200767f52d9720024fe71d9720004fd71d97200b67f51d9720076f970d972026e7e50d972026e7c50d9720014ff76597200767c65597200767f7559720004ff7459720044fc74597200b67f5459720004ff735972000cfe7359720004fd735972000cfc73597200b67f53597200067d535972001cfc72597200767e52597200767c5259720004ff7159720024fc71597200b67c51597200b67f5059720014fe75d9320004fd75d9320074fc75d9320074ff73d932000cfe73d9320004fd73d9320074fc73d9320076ee72d9320024fe71d9320004fd71d9320076f970d9320226be40d9320226bc40d9320004fd7699320076bf6499320076bc6499320044ff76593200057f75593200b57c7559320076bc6459320004ff75593200067f75593200047f7559320014fe7559320014fc75593200067c75593200147c7559320076bf7459320004ff735932000cfe7359320004fd735932000cfc7359320006bf4359320006bd435932001cfc7259320076be4259320076bc4259320004ff7159320024fc7159320044ff7695320074fe7695320004fd7695320074fc76953200067f65953200167c6595320046be6495320006bd64953200b73f5495320004ff7655320074fe7655320004fd7655320074fc76553200167e65553200067d6555320046be6455320006bd6455320084ff7654b200767f6554b200767c6554b20005bf7454b20005bc7454b200057f7550b200b57c7550b200b57e75987200057d7598720005be7498720005bd7498720076f76198720014fe75987200267e75987200147e7598720004fd75987200267d75987200047d7598720024fc7598720044fe7498720026be7498720044be7498720004fd7498720026bd7498720004bd7498720024ff739872000cfe7398720004fd7398720024fc739872001cfe7298720026f63198720006f53198720076f72198720026f42198720076f46158720004ff7558720014fe7558720014fc7558720004ff7458720044fc7458720004ff735872000cfe7358720004fd735872000cfc735872001cfc7258720006f63158720006f53158720076f72158720076f42158720024ff7694720074fe7694720004fd76947200167e65947200067d6594720075ee7294720005ed7294720004ff7654720004fd7654720074fc76547200067f65547200167c655
  | 18 => 0xf7258840046ef4258840046bc4258840046ec4258840004ff7158840024fc715884001efa3058840006f9305884001eee205884001eec2058840074ff769484001cfe7694840004fd769484026e7f65948400167c6594840045bc74948403073e54948401e6de6394840006dd6394840076ee6294840006ed6294840004ff7654840004fd765484001cfc76548400167e65548400067d6554840005bf7454840045bc74548400073d54548401dede6354840006dd6354840006ee6254840006ed6254840045bd7690840006bd7690840005bf7590840005bd75908401c6be6590840046bc65908402fdbf73908402fdbd73908400479e63908400479d6390840045be7290840047ae7290840006bd6290840005be7190840225bd7090840226be6090840047ba6090840227ba30908402f7b93090840014fe7598440004fd7598440024fc7598440024ff739844000cfe7398440004fd7398440024fc7398440074fe7298440004fd729844001cfe719844001ef67198440046f74198440026f4419844001ef6109844001ef41098440004ff75584400067f75584400047f7558440014fe7558440014fc75584400067c75584400147c7558440046be5458440006bd5458440004ff735844000cfe7358440004fd735844000cfc7358440046bf4358440006bd4358440004ff7258440074fc7258440006be4258440046bc425844001ef77158440046f74158440046bc4158440046f4415844001ef8705844001ebf405844001ebd405844001efa3058440006f9305844001ef6105844001ef4105844001ef81058440024ff769444001cfe7694440004fd769444025e7f65944400167c6594440045bc74944402ef3e5494440196de6394440006dd6394440026f66194440006f56194440004ff7654440004fd765444001cfc76544400167e65544400067d6554440005bf7454440045bc74544400073d545444018ede6354440006dd6354440006f66154440006f56154440005fb705444001df87054440045bd7690440006bd7690440004bd7690440005bf7590440005bd75904402e5bf73904402e5bd73904400479e63904400479d6390440005be7290440045be7190440047b67190440006bd6190440277bb709044024dbd709044024fb8709044024ebe6090440047ba609044024fba30904402dfb9309044024fb81090440074ff76c844001cfe76c8440004fd76c84400c57e75c84400057d75c8440045be74c8440005bd74c8440126de63c8440006dd63c8440076ee62c8440006ed62c844001dfa70c8440005f970c8440024ff768844001cfe7688440004fd76884400c57e75884400057d7588440045be7488440005bd748844011ede6388440006dd6388440026f66188440006f56188440004ff7648440004fd764844001cfc7648440
  | 19 => 0x540006bc6250540045bf7150540047b77150540007b76150540026bc6150540007b46150540007bb705054001dbe705054001dbc7050540007b8705054001db87050540046bf6050540047bb6050540004fe76c8540004fd76c8540074fc76c85400d57e75c85400057d75c8540004fe7688540004fd7688540024fc76885400d57e75885400057d7588540045be7488540005bd7488540004ff7648540004fe7648540004fc7648540005df73485400cddc7348540004fe7608540004fd7608540024fc7608540045be7408540005bd740854001dfa7008540005f97008540014ff76541400d4fd7654140044fc76541400067f65541400167c6554140005bf7454140045bc745414001cff755944001e7f7559440044ff7459440044fe7459440044fd7459440044fc74594400467e54594400467c5459440004ff735944000cfe7359440004fd735944000cfc7359440004ff7259440074fc72594400c67f5259440004ff7159440024fc71594400c67f515944001cfe705944001cfc705944001e7e505944001e7c5059440045bf76550400f6bf7655040045bf75550400473f75550400473f6555040016be6555040046bc65550400473c6555040315bf7355040315bd73550400479e63550400479d6355040005bc72550400c73f5255040005bc71550400c73f515504022dbf705504022dbd705504022ebe6055040047ba605504022f3e505504022f3c505504022fba305504030fb93055040006df7558c40006de7558c40006dd7558c40006dc7558c40046df7458c40046de7458c40046dd7458c40046dc7458c40046df5458c40046de5458c40046dd5458c40046dc5458c40006df7258c40006de7258c40006dd7258c40006dc7258c40006df5258c40006dc5258c40046df4258c40046de4258c40046dd4258c40046dc4258c40006df7158c40006de7158c40006dd7158c40006dc7158c40006df5158c40006dc5158c40046df4158c40046de4158c40046dd4158c40046dc4158c4001edf7058c4001ede7058c4001edd7058c4001edc7058c4001edf5058c4001ede5058c4001edd5058c4001edc5058c4001edf4058c4001ede4058c4001edd4058c4001edc4058c4001edf2058c4001ede2058c4001edd2058c4001edc2058c4001edf1058c4001ede1058c4001edd1058c4001edc1058c40014fe7598840004fd7598840074fc7598840074ff739884000cfe7398840004fd7398840074fc739884001cfe729884001eee7298840046ef4298840076ec4298840024fe7198840004fd719884001eee209884001eec2098840004ff75588400067f75588400047f7558840014fe7558840014fc75588400067c75588400147c7558840004ff735884000cfe7358840004fd735884000cfc7358840046bf4358840006bd435884001ee
  | 20 => 0x67d53d9540074fe72d9540004fd72d95400d67c52d9540024fe71d9540004fd71d95400d67c51d9540044fd70d95400d67f50d9540236be40d9540236bc40d95400d67c65595400d4ff75595400067f75595400e4ff7459540006bf74595403367e54595403367c5459540004ff735954000cfe7359540004fd735954000cfc7359540004ff7259540074fc72595400d67f5259540004ff7159540024fc71595400d67f51595400f4ff7059540006fb705954022e7e505954022e7c505954022ebe405954001cfc76551400067f65551400167c6555140005fb705514001df87055140014fe75d8940004fd75d8940014fc75d8940004ff73d894000cfe73d8940004fd73d894000cfc73d8940024fe71d8940004fd71d8940006ef62989400057f75589400d57c75589400d57e75189400057d7518940006ed6218940014fe75189400767e75189400147e7518940004fd75189400767d75189400047d7518940074fc7518940074ff731894000cfe7318940004fd7318940074fc7318940024fe7118940004fd711894021ebe401894021ebc4018940004fe7694940004fd7694940074fc76949400067f65949400167c6594940004ff7654940004fe7654940004fc76549400167e65549400067d6554940005bf7454940045bc745494001cfe7690940006ef6290940076ec629094001dfa7090940005f9709094001cfc76509400057f75509400d57c7550940006ef6250940006ec6250940005fb705094001df87050940047b84050940014fe75d8540004fd75d8540014fc75d8540004ff73d854000cfe73d8540004fd73d854000cfc73d8540074fe72d8540004fd72d8540006f761985400057f75585400d57c75585400d57e75185400057d7518540006f56118540014fe75185400267e75185400147e7518540004fd75185400267d75185400047d7518540024fc7518540024ff731854000cfe7318540004fd7318540024fc7318540074fe7218540004fd7218540206fb4018540246be4018540246bc4018540206f84018540004fe7694540004fd7694540024fc76945400067f65945400167c6594540045be7494540005bd7494540004ff7654540004fe7654540004fc76545400167e65545400067d6554540005be76d0540046be76d0540004be76d0540006bf65d0540006bd65d054032ebf63d054032ebd63d0540006bc62d0540026bc61d054001dbe70d054001dbc70d0540046bf60d0540047bb60d054001cfe7690540325bd7490540006f76190540026f4619054001dfa7090540005f97090540047b8409054001cfc76505400057f75505400d57c7550540006f76150540006f46150540005fb705054001df8705054001cbc76505400073f75505400073c7550540006bf6550540006bd655054031ebf635054031ebd635
  | 21 => 0xe6250a40006ed6250a40005fb7050a4001df87050a4021dbd7610a40046bd7610a40045bf7510a400473e7510a40005bd7510a400473d7510a400053d7510a401a6be6510a4021f3e6510a401a63e6510a4021f3d6510a4021ebc6510a40045bf7310a4034dbd7310a40047ae7210a40006bd6210a40005be7110a40045bf7010a4021dbd7010a40047ba6010a40014fe7598640004fd7598640024fc7598640024ff739864000cfe7398640004fd7398640024fc7398640074fe7298640004fd729864001ef6719864001cfe709864020efb409864001ef8409864001ef6109864001ef41098640004ff7558640014fe7558640014fc7558640006be5458640006bd5458640004ff735864000cfe7358640004fd735864000cfc7358640006bf4358640006bd4358640004ff7258640074fc7258640006be4258640006bc425864001ef7715864001cfc705864001ebf405864001ebd405864001ef6105864001ef41058640024ff769464001cfe7694640004fd76946400167e65946400067d65946400073e5494640004ff7654640004fd765464001cfc76546400167e65546400067d6554640005bf7454640045bc74546400073d54546401767e65906400067d6590640026f66190640006f5619064001dfa7090640005f97090640005bf7590640005bd759064024f3e659064024f3d6590640345bf7390640345bd7390640005be7290640045be719064024fb66190640006bd619064024fb5619064024fba709064024dbd7090640007b97090640046be60906400057f75506400e57c755064016e7e65506400067d6550640006f66150640006f56150640005fb705064001df87050640245bd7610640046bd7610640045bf75106400473e7510640005bd75106400473d75106400053d75106402473e65106402473d6510640045bf731064033dbd7310640005be7210640047b67110640006bd6110640045bf7010640245bd7010640047ba6010640074ff76c864001cfe76c8640004fd76c86400e57e75c86400057d75c86401467e65c86400067d65c8640045be74c8640005bd74c8640076ee62c8640006ed62c8640024ff768864001cfe7688640004fd76886400e57e75886400057d758864013e7e65886400067d6588640045be7488640005bd7488640004ff7648640004fd764864001cfc76486401367e65486400067d6548640005bf7448640045bc7448640005df73486400dddc7348640006ee6248640006ed6248640024ff760864001cfe7608640004fd76086401167e65086400067d6508640005bf7408640045bc740864001dfa7008640005f97008640014fe76d95400d67e65d9540044fe74d954001cfd74d9540044fc74d95400d67f54d9540004ff73d954000cfe73d9540004fd73d954000cfc73d95400d67f53d9540
  | 22 => 0x96400067e73596400067d73596400067c73596403367f43596400067e43596400067d43596403367c43596400067f72596400067e72596400067d72596400067c72596403367f42596403367c42596400067f32596400067e32596400067d32596400067c32596400067f71596400067e71596400067d71596400067c71596403367f41596403367c41596400067f31596400067e31596400067d31596400067c315964001e7f705964001e7e705964001e7d705964001e7c705964001e7f405964001e7e405964001e7d405964001e7c405964001e7f305964001e7e305964001e7d305964001e7c305964001e7f205964001e7e205964001e7d205964001e7c205964001e7f105964001e7e105964001e7d105964001e7c1059640235bd7695240046bd7695240016be65952402373e65952400163e65952402373d6595240016bc6595240045bf739524036dbd73952400e73f53952403673d5395240005be72952400e73c5295240005be71952400e73c5195240045bf7095240235bd7095240047ba60952402373f50952402373d5095240014ff765524001cfc76552400167e65552400067d65552400473c5455240005fb705524001df87055240047bb405524022dbf7655240016bf7655240014bf7655240045bf75552400473f7555240016be655524022f3e655524022f3d6555240016bc655524035dbf735524035dbd7355240005bc72552400e73f5255240005bc71552400e73f515524022dbf7055240007bb705524022fb87055240046be605524022f3e505524022f3c5055240014fe7598a40004fd7598a40074fc7598a40074ff7398a4000cfe7398a40004fd7398a40074fc7398a4001eee7298a40006ef3298a40076ec3298a40024fe7198a40004fd7198a4001cfe7098a4001eee2098a4001eec2098a40004ff7558a40014fe7558a40014fc7558a40004ff7358a4000cfe7358a40004fd7358a4000cfc7358a40006bf4358a40006bd4358a4001eef7258a40006ef3258a40006ec3258a40004ff7158a40024fc7158a4001cfc7058a4001eee2058a4001eec2058a40074ff7694a4001cfe7694a40004fd7694a400167e6594a400067d6594a400073e5494a40004ff7654a40004fd7654a4001cfc7654a400167e6554a400067d6554a40005bf7454a40045bc7454a400073d5454a401c67e6590a400067d6590a40076ee6290a40006ed6290a4001dfa7090a40005f97090a40005bf7590a40005bd7590a401c6be6590a402273e6590a401c63e6590a402273d6590a40226bc6590a40355bf7390a40355bd7390a40045be7290a40227ae6290a40006bd6290a40227ad6290a40005be7190a40227ba7090a40225bd7090a40007b97090a40046be6090a400057f7550a400e57c7550a401be7e6550a400067d6550a40006e
  | 23 => 0x74fc7398b40076ee7298b40046ef4298b40076ec4298b40024fe7198b40004fd7198b40046bf4198b40226be4098b40046bc4098b40004ff7558b40014fe7558b40014fc7558b4001cfc7458b40004ff7358b4000cfe7358b40004fd7358b4000cfc7358b40046ef7258b40046ef4258b40046ec4258b40004ff7158b40024fc7158b40006fa3058b40006f93058b40074ff7694b40044fe7694b40004fd7694b400167e6594b400067d6594b40004ff7654b40004fd7654b40044fc7654b400167e6554b400067d6554b40005bf7454b40045bc7454b40014fe7598740004fd7598740024fc759874001cfe749874001cbe7498740024ff739874000cfe7398740004fd7398740024fc7398740074fe7298740004fd7298740026f67198740026bf4198740046f74198740026f4419874024ebe4098740046bc4098740004ff7558740014fe7558740014fc755874001cfc7458740004ff735874000cfe7358740004fd735874000cfc7358740004ff7258740074fc7258740046f77158740046f74158740046f44158740006fb7058740006fa3058740006f93058740024ff7694740044fe7694740004fd76947400167e65947400067d6594740045be7494740005bd7494740004ff7654740004fd7654740044fc76547400167e65547400067d6554740005fb705474001df87054740045bf7650740006bf76507400073f75507400073c7550740046bf65507400473e6550740006bd65507400473d65507400063d6550740046bf6350740376bd6350740006be6250740047b77150740026be6150740007bb705074001dbe705074001dbc7050740007b8705074001db87050740377ba3050740377b93050740074ff76c8740044fe76c8740004fd76c87400f57e75c87400057d75c87401467e65c87400067d65c874001dfa70c8740005f970c8740024ff7688740044fe7688740004fd76887400f57e75887400057d758874013e7e65887400067d6588740045be7488740005bd7488740004ff7648740004fd7648740044fc76487401367e65487400067d6548740005df73487400eddc7348740005fb704874001df87048740024ff7608740044fe7608740004fd76087401167e65087400067d6508740045be7408740005bd7408740014ff7654340044fc76543400167e65543400067d6554340005bf7454340045bc745434001fba405434001e7f75596400e67f5459640004ff735964000cfe7359640004fd735964000cfc73596400e67f53596400067e53596400067d53596400e67c5359640004ff7259640074fc72596400e67f52596400e67c5259640004ff7159640024fc71596400e67f51596400e67c515964001cfc705964001e7e505964001e7c50596400067f74596403367e74596400067d74596403367c74596400067f735
  | 24 => 0xe7318550004fd7318550024fc7318550074fe7218550004fd72185500367f52185500067d52185500267f5118550026f65118550036f551185502567e50185502567c501855001c7c76545503357c74545500067f645455037e7f635455037e7d63545500057f72545500067c62545500157f71545500177771545500077761545500267c61545500077461545500077b705455001d7e705455001d7c70545500077870545500167f60545500177b6054550004fe76d0550004fd76d0550044fc76d05503357f75d05500157c75d0550046be64d05503373e54d0550004fe7690550004fd7690550024fc76905500157e75905500057d7590550006bf6490550046bc6490550004ff7650550004fe7650550004fc76505500057f75505500157c75505500073e5450550005fb705055001df87050550004fe7610550004fd7610550024fc76105500157e75105500057d7510550006bf6410550046bc6410550004fe76c8550004fd76c8550074fc76c85500157e75c85500057d75c8550004fe7688550004fd7688550024fc76885500157e75885500057d7588550005be7488550005bd7488550004ff7648550004fe7648550004fc76485500157e75485500057d7548550005df73485500fddc7348550004fe7608550004fd7608550024fc76085500157e75085500057d750855001dfa7008550005f970085500467f755974001cfc74597400467e54597400467c5459740004ff735974000cfe7359740004fd735974000cfc73597400f67f53597400067e53597400067d53597400f67c5359740004ff7259740074fc72597400f67f52597400f67c5259740004ff7159740024fc71597400f67f51597400f67c5159740046bf41597400f67f505974022ebe4059740046bc40597400467f74597400467e74597400467d74597400467c74597400067f73597400067e73597400067d73597400067c73597400467f43597400467e43597400467d43597400467c43597400067f72597400067e72597400067d72597400067c72597400467f42597400467e42597400467d42597400467c42597400067f32597400067e32597400067d32597400067c32597400067f71597400067e71597400067d71597400067c71597400467f41597400463f41597400467e41597400467d41597400467c41597400067f31597400067e31597400067d31597400067c31597400067f705974022e7e70597400067d705974022e7c70597400467f40597400467e405974022e3e40597400467d40597400467c40597400463c40597400067f305974022e7e30597400067d305974022e7c305974022e7e205974022e7c205974022e7e105974022e7c1059740014fe7598b40004fd7598b40074fc7598b4001cfe7498b40074ff7398b4000cfe7398b40004fd7398b40
  | 25 => 0x8650005be7488650005bd7488650004ff7648650004fd764865001cfc76486500057f75486500157c7548650005df7348650105dc7348650006ee6248650006ed6248650024ff760865001cfe7608650004fd76086500057f75086500157c750865001dfa7008650005f9700865001cfd75d91500e6be54d91500e6bd54d91503367c54d9150004ff73d915000cfe73d9150004fd73d915000cfc73d9150006bf43d9150006bd43d9150074fe72d9150004fd72d91500e67f52d9150024fe71d9150004fd71d91500e67f51d91503967e50d91503967c50d9150006bf64991500d5f970991500f5fb7059150046be6419150006bd641915001c7e76951500157e74951500173e74951503367f64951500073f64951500063f64951503373c649515038e7f639515038e7d63951500057d72951500057d719515001d7e70951503377a709515033779709515001d7c70951500167f60951500177b60951502373c409515001cfd75d8950044fe74d8950004fd74d8950004ff73d895000cfe73d8950004fd73d895000cfc73d89500aeee52d89500aeed52d8950024fe71d8950004fd71d8950006ef629895009df97098950005bf7458950005bc74589500b5fb7058950006ed621895001cfd7518950044fe7418950004fd74189500067e54189500867c5418950074ff731895000cfe7318950004fd7318950074fc73189500767f5218950076ee5218950086ed5218950024fe7118950004fd71189500867f51189502c67e50189502c67c501895001c7c76549500073f74549503357c74549500073c74549500053c74549500067f64549503867f63549503867d63549500157f72549500176f72549500076f62549500767c62549500076c62549500057f71549500077b705495001d7e705495001d7c70549500077870549500167f60549500177b6054950004fe76d0950004fd76d0950044fc76d09503357f75d09500157c75d0950004fe7690950004fd7690950074fc76909500157e75909500057d7590950006bf6490950046bc64909501c73c549095001dfa7090950005f97090950004ff7650950004fe7650950004fc76509500057f75509500157c7550950004fe7610950004fd7610950074fc76109500157e75109500057d7510950006bf6410950046bc64109503373c541095001cfd75d8550044fe74d8550004fd74d8550004ff73d855000cfe73d8550004fd73d855000cfc73d8550074fe72d8550004fd72d8550066f651d8550066f551d8550006f76198550055f97098550005bf7458550005bc745855006dfb7058550005be7418550005bd7418550006f5611855001cfd7518550044fe7418550026be7418550044be7418550004fd7418550026bd7418550004bd74185500067e54185500367c5418550024ff731855000cf
  | 26 => 0x74fc7398a5001eee7298a50076ee5298a500b6ed5298a50024fe7198a50004fd7198a5001cfe7098a5001cfc7098a5001eee2098a5001eec2098a50004ff7458a50044fc7458a5009e7f5458a500067d5458a50004ff7358a5000cfe7358a50004fd7358a5000cfc7358a5009e7f5358a500067d5358a5001eef7258a5009eee5258a5009eed5258a5009e7c5258a50004ff7158a50024fc7158a5009e7c5158a5001cfc7058a5001e7f5058a5001e7d5058a5001eee2058a5001eec2058a500057d7494a503067e6494a503a57f7394a503a57d7394a500157e7294a500176e7294a5026f6e6294a500067d6294a5026f6d6294a500066d6294a500057e7194a5026f7a7094a5026d7d7094a50007797094a50005797094a500167e6094a500177a6094a50044ff76d0a5001cfe76d0a50004fd76d0a500157e75d0a500057d75d0a50074ff7690a5001cfe7690a50004fd7690a500057f7590a500157c7590a50046be6490a50006bd6490a501c73f5490a5001dfa7090a50005f97090a50004ff7650a50004fd7650a5001cfc7650a500057f7550a500157c7550a50074ff7610a5001cfe7610a50004fd7610a500157e7510a500057d7510a50046be6410a50006bd6410a501a73f5410a50044fe7498650004fd7498650024ff739865000cfe7398650004fd7398650024fc7398650074fe7298650004fd729865001ef67198650026f6519865006ef5519865001cfe709865001cfc709865001ef6109865001ef41098650004ff7458650044fc74586500567f54586500067d5458650004ff735865000cfe7358650004fd735865000cfc73586500567f53586500067d5358650004ff7258650074fc72586500067e52586500567c525865001ef77158650056f65158650056f551586500567c515865001cfc705865001e7f505865001e7d505865001ef6105865001ef410586500057d74946502ee7e649465039d7f739465039d7d73946500057e72946500067d62946500157e719465001776719465025f7661946500067d619465025f75619465025f7a709465025d7d70946500077970946500167e60946500177a6094650044ff76d065001cfe76d0650004fd76d06500157e75d06500057d75d0650046be64d0650006bd64d06500073d54d0650024ff769065001cfe7690650004fd76906500057f75906500157c7590650004ff7650650004fd765065001cfc76506500057f75506500157c7550650046be6450650006bd64506500073d5450650005fb705065001df87050650024ff761065001cfe7610650004fd76106500157e75106500057d7510650074ff76c865001cfe76c8650004fd76c86500157e75c86500057d75c8650076ee62c8650006ed62c8650024ff768865001cfe7688650004fd76886500157e75886500057d758
  | 27 => 0xf7459021004ff735902100cfe7359021004fd735902100cfc7359021006bf4359021006bd4359021074fe7259021074fc7259021076be4259021076bc4259021024fe7159021024fc7159021026be4159021026bc4159021004ff705902101cfc7059021044ff7695021024fe7695021004fd7695021024fc76950210067f65950210167c6595021046be6495021006bd64950211173f5495021004ff7655021024fe7655021004fd7655021024fc76550210167e65550210067d6555021046be6455021006bd6455021144ff76548210767f65548210767c6554821005bf7454821005bc7454821004fd76d0821004ff76508210057f75508211157c755082113cff76544210267f65544210267c6554421004fd76d0421026bf64d0421026bc64d0421004ff76504210057f75504211157c7550421026bf6450421026bc6450421005fb7050421005f870504210776e75c84210776d75c8421026ef63c84213c6ed63c8421025ed71c8421026ee61c8421027767588421027757588421027b67488421027b57488421026f763884213bef56388421075f57288421076f66288421027e66288421004ff7648421005df734842110ddc7348421025ef7648421006ef7648421004ef7648421007cf73484213b7cc7348421026ef63484213b6ed6348421025ef7148421026ee6148421027e64148421007e54148421027e631484213b7e53148421075f77648421006f77648421004f77648421007d773484213b7d47348421076f763484213b6f56348421025f77248421027e77248421076f66248421077e66248421077e64248421007e54248421077e632484213b7e53248421026fb609802101ef860980210057f75580211157c7558021005bf7458021005bc7458021026f86058021004ff75580210067f75580210047f7558021014fe7558021014fc75580210067c75580210147c7558021004ff7458021006bf7458021004bf7458021044fc7458021006bc7458021044bc7458021004ff735802100cfe7358021004fd735802100cfc7358021006ef2158021006ed2158021006fa3058021006f93058021076fb2058021076f82058021026fb1058021026f8105802101ebf74592500d6be54592500d6bd5459250004ff735925000cfe7359250004fd735925000cfc7359250006bf4359250006bd4359250004ff7259250074fc7259250004ff7159250024fc715925001cfc705925001ebe405925001ebc40592500447f76552500157f74552500173f74552500467e645525022f3e645525022f3d64552500467c64552503ad7f73552503ad7d73552500057c72552500057c715525022d7f70552500077b705525022f7870552500167e60552500177a6055250044fe7498a50004fd7498a50074ff7398a5000cfe7398a50004fd7398a50
  | 28 => 0x4521014ff7654521134fd7654521014fc76545210067f65545210167c6554521006df635452118edc6354521005ef7254521005ec7254521004fe76d0521074fc76d0521006bf64d0521046bc64d0521006df63d052117edc63d0521005ee72d0521005ed72d0521004fe7690521006df639052115edc6390521044ff7650521004fd7650521044fc76505210057f75505211357c7550521006bf6450521046bc6450521006df6350521166dc6350521005ef7250521005ec7250521005fb7050521005f87050521004fe76105211357e75105210057d7510521006df631052114edc6310521007b541105211357e75c85210057d75c8521006df63c8521126dc63c85210777675c85210777575c8521075f773c85213e5f573c8521007d763c85213dfd463c8521077e632c85213dfe532c85211357e75885210057d7588521005be7488521005bd7488521006df638852111edc63885210276e75885210276d7588521027ae7488521027ad7488521025ef73885213d5ed7388521007cf63885213cfcc6388521007e76188521027e631885213cfe53188521005ed7088521006df63d8121006dc63d8121014fe75d8121004fd75d8121014fc75d8121044fe74d8121004fd74d8121004ff73d812100cfe73d8121004fd73d812100cfc73d8121006fb50d8121006f850d812112dde7398121005dd7398121006df6398121006dc6398121006fb60981210057f75581211357c7558121005bf7458121005bc7458121005df735812112ddc7358121006df6358121006dc63581211357e75181210057d7518121006df6318121006dc631812101efa6018121006f96018121114fd75d9421044fe74d9421004fd74d94211167c54d9421024ff73d942100cfe73d9421004fd73d9421024fc73d9421074fe72d9421026ee72d94210767f52d9421024fe71d9421026f671d94210267f51d942101cfe70d9421004fd70d94211167c50d9421014ff76594210267c6559421024ff75594210267f7559421004ff7459421044fc74594211167f5459421004ff735942100cfe7359421004fd735942100cfc73594211167f53594210067d5359421074fe7259421074fc72594210767e52594210767c5259421024fe7159421024fc71594210267e51594210267c5159421004ff705942101cfc70594211167f5059421014fe75d9021004fd75d9021024fc75d9021024ff73d902100cfe73d9021004fd73d9021024fc73d9021074fe72d9021026ee72d9021024fe71d9021026f671d902101cfe70d9021004fd70d9021004fd7699021026bf6499021026bc6499021044ff76590210057f75590211157c7559021026bc6459021004ff75590210067f75590210047f7559021014fe7559021014fc75590210067c75590210147c7559021024ff7459021026b
  | 29 => 0x44fe76d9121006dc63d9121014fe75d9121004fd75d9121014fc75d9121006bf54d9121006bc54d9121004ff73d912100cfe73d9121004fd73d912100cfc73d912101cfe70d9121004fd70d9121006bf649912112dde7399121005dd7399121006dc63991210057f75591211357c7559121005df735912112ddc7359121006dc6359121005fb7059121005f87059121004ff75591210067f75591210047f7559121014fe7559121014fc75591210067c75591210147c7559121006bf7459121004ff7359121006df7359121004df735912100cfe7359121004fd735912100cfc7359121006dc735912100cdc7359121006bf4359121006bd4359121004ff7259121006ef7259121004ff7159121006f77159121004ff7059121006fb7059121004fb705912101cfc7059121006f8705912101cf87059121004fe76191211357e75191210057d7519121046be6419121006bd6419121006dc6319121044ff7695121004fe7695121004fd7695121044fc76951210067f65951210167c65951211373f54951211f6dc6395121004ff7655121004fe7655121004fd7655121004fc76551210167e65551210067d65551211eedc6355121005ef7255121005ec725512112dde76d8d2112ede76d8d2100cde76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d21007cf72d8d2112fcc72d8d21007d771d8d2112fd471d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d21006df72d8d2112ede72d8d2112edd72d8d2112edc72d8d21006df52d8d21006dc52d8d21006df71d8d2112ede71d8d2112edd71d8d2112edc71d8d21006df51d8d21006dc51d8d2112edd21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006dc50d8d2113cfe76949210167e65949210067d6594921006df63949211e6dc6394921014fc76549210067f65549210167c6554921005bf7454921005bc7454921006df63549211dedc6354921005f77154921005f47154921004fe76d0921024fc76d0921006bf64d0921046bc64d0921006df63d09211cedc63d0921005f671d0921005f571d0921004fe7690921046be6490921006bd6490921006df63909211aedc6390921044fc76509210057f75509211357c7550921006bf6450921046bc6450921006df63509211b6dc6350921005f77150921005f47150921004fe76109211357e75109210057d7510921046be6410921006bd6410921006df631092119edc6310921007ad4210921144fe76945210167e65945210067d6594521006df6394521196dc639452113777519
  | 30 => 0xd7694a210167e6594a210067d6594a21006be6494a21006bd6494a2113f6f5294a21014ff7654a21024fc7654a210167e6554a210067d6554a21005bf7454a21005bc7454a21006be6454a21006bd6454a21005f77154a21025f47154a211d67e65d0a210067d65d0a21046be64d0a21006bd64d0a21025f671d0a21005f571d0a211c67e6590a210067d6590a21046be6490a21006bd6490a21044ff7650a210057f7550a2113d7c7550a211be7e6550a210067d6550a21046be6450a21006bd6450a21005f77150a21025f47150a2113d7e7510a210057d7510a211a67e6510a210067d6510a21046be6410a21006bd6410a21114ff76546210167e65546210067d6554621006be6454621006bd64546211867e65d06210067d65d0621046be64d0621006bd64d06210057f755062113d7c755062116e7e65506210067d6550621046be6450621006bd6450621027b44150621005fb7050621005f8705062113d7e75c86210057d75c86211467e65c86210067d65c8621006be64c8621006bd64c8621025ed76c8621006ed76c86210076e75c86210076d75c86210276e65c86210276d65c8621027ae64c8621027ad64c8621026ef63c86213f6ed63c8621027e651c8621007e551c8621005f576c8621076f576c86210777675c86210777575c86210077665c86210077565c8621007b664c8621007b564c8621075f773c86213edf573c8621077e652c8621007e552c86210067e65982210067d6598221006be6498221006bd6498221026fb609822101ef860982210067e65582210067d6558221006be6458221006bd6458221026f86058221004ff7558221014fe7558221014fc7558221004ff7458221044fc7458221004ff735822100cfe7358221004fd735822100cfc7358221006ef2158221006fa3058221006f93058221026fb1058221026f81058221014fe76d95211367e65d9521006dc63d9521044fe74d9521004fd74d95211367c54d9521004ff73d952100cfe73d9521004fd73d952100cfc73d9521134fd72d95211367f52d9521134fd71d95211367f51d952101cfe70d9521004fd70d95211367c50d95211367c6559521005bf7459521005bc7459521005df735952112ddc7359521006dc6359521005fb7059521005f87059521134ff75595210067f7559521004ff7459521006bf7459521004bf7459521044fc7459521006bc7459521044bc74595211367f5459521004ff7359521006df7359521004df735952100cfe7359521004fd735952100cfc7359521006dc735952100cdc73595211367f53595210067d535952113cff7259521006ef72595211367c5259521144ff7159521006f771595211367c5159521004ff7059521006fb7059521004fb705952101cfc7059521006f8705952101cf870595211367f5059521
  | 31 => 0x9221024fc73d9221026ed72d9221026f671d922101cfe70d9221004fd70d9221004fd76992210067e65992210067d6599221026bf6499221026bc6499221004bd7699221026bf6599221006be65992210273e65992210063e6599221006bd65992210273d65992210063d6599221026bc6599221026bf6399221006be6399221006bd6399221026bc6399221027b63199221007b53199221026bf6099221026bc6099221046bf7599221046be7599221046bd7599221046bc7599221046bf7399221046be7399221046bd7399221046bc7399221006bf5399221006be5399221006bd5399221006bc5399221046bf7299221046bd7299221006bf5299221006bc5299221006bf3299221006be3299221006bd3299221006bc3299221026be7199221026bc7199221006bf5199221026be5199221026bc5199221006bf3199221026be3199221006bd3199221026bc3199221026bc2199221046bf7099221046be7099221046bd7099221046bc7099221006bf5099221006bc5099221006bf3099221006be3099221006bd3099221006bc3099221026bf1099221026bc1099221044ff76592210067e65592210067d6559221026bc6459221004ff7559221014fe7559221014fc7559221026bf7459221006bf5459221006bc5459221004ff735922100cfe7359221004fd735922100cfc7359221006bf4359221006be4359221006bd4359221006bc4359221026be4159221026bc4159221004ff705922101cfc7059221025bf7659221006bf7659221044bf7659221026bf6559221006be65592210273e65592210063e6559221006bd65592210273d65592210063d6559221026bc6559221026bf6359221006be6359221006bd6359221026bc6359221027b63159221007b53159221026bf6059221026bc6059221006bf7559221006be7559221006bd7559221006bc7559221006bf7359221006be7359221006bd7359221006bc7359221006bf5359221006be5359221006bd5359221006bc5359221006bf7259221006bd7259221006bf5259221006bc5259221006bf3259221006be3259221006bd3259221006bc3259221026be7159221026bc7159221006bf5159221026be5159221026bc5159221006bf3159221026be3159221006bd3159221026bc3159221026be2159221026bc2159221006bf7059221006be7059221006bd7059221006bc7059221006bf5059221006bc5059221006bf3059221006be3059221006bd3059221006bc3059221026bf1059221026bc1059221044ff7695221024fe7695221004fd7695221024fc76952210167e65952210067d6595221046be6495221006bd649522113f3f5495221004ff7655221024fe7655221004fd7655221024fc76552210167e65552210067d6555221046be6455221006bd6455221134f
  | 32 => 0x57f7550b211457c7550b211be7e6550b210067d6550b21077ac4250b21134fd76947210167e65947210067d6594721014ff7654721074fc76547210167e65547210067d6554721005ef7254721075ec72547211867e65d07210067d65d0721046be64d0721006bd64d0721075ee72d0721005ed72d07211767e65907210067d6590721044ff76507210057f75507211457c755072116e7e65507210067d6550721046be6450721006bd6450721005ef7250721075ec7250721005fb7050721005f870507211457e75107210057d75107211567e65107210067d65107210067e65983210067d6598321125de7398321005dd7398321076fb609832101ef860983210067e65583210067d6558321076f86058321004ff7558321014fe7558321014fc7558321004ff7458321044fc7458321004ff735832100cfe7358321004fd735832100cfc7358321006fa3058321006f93058321076fb2058321076f8205832113cfd75d9621044fe74d9621026be74d9621044be74d9621004fd74d9621026bd74d9621004bd74d9621024ff73d962100cfe73d9621004fd73d9621024fc73d9621026ed72d9621026f671d962101cfe70d9621004fd70d96210047d76996210267f64996210267c64996210267f63996210067e63996210067d63996210267c63996210267e61996210277631996210077531996210267f60996210267c6099621014ff76596210267c65596210267f7559621004ff7459621044fc745962113e7f545962113e7c5459621004ff735962100cfe7359621004fd735962100cfc735962113e7f53596210067e53596210067d535962113e7c535962113e7f52596210267e51596210267c5159621004ff705962101cfc705962113e7f505962113e7c50596210257f765962113e7f76596210147f76596210267f64596210267c64596210267f63596210067e63596210067d63596210267c63596210277631596210077531596210267f60596210267c60596210067f74596210067e74596210067d74596210067c74596210067f73596210067e73596210067d73596210067c73596210067f43596210067e43596210067d43596210067c43596210067f72596210067d725962113e7c72596210067f32596210067e32596210067d32596210067c325962113e7f71596210267e71596210267c71596210267e41596210267c41596210067f31596210267e31596210067d31596210267c31596210267e21596210267c21596210067f70596210067e70596210067d70596210067c70596210067f30596210067e30596210067d30596210067c30596210267f10596210267c1059621014fe75d92210267e75d92210147e75d9221004fd75d92210267d75d92210047d75d9221024fc75d9221024ff73d922100cfe73d9221004fd73d
  | 33 => 0xd4158041026fb7058041046fb4058041046bc4058041046f84058041006fa3058041006f93058041026fb1058041026f81058041144fd75d9721044fe74d9721004fd74d9721074ff73d972100cfe73d9721004fd73d9721074fc73d9721076ee72d9721076f571d972101cfe70d9721004fd70d97210047d76997210767f64997210767c64997210767f63997210067e63997210067d63997210767c63997210767e62997210776e32997210076d32997210767f60997210767c6099721014ff76597210767c65597210767f7559721004ff7459721044fc74597211467f54597211467c5459721004ff735972100cfe7359721004fd735972100cfc73597211467f53597210067e53597210067d53597211467c53597210767e52597210767c52597211467f5159721004ff705972101cfc70597211467f50597211467c50597210757f76597211467f76597210147f76597210767f64597210767c64597210767f63597210067e63597210067d63597210767c63597210776e32597210076d32597210767f60597210767c60597210067f74597210067e74597210067d74597210067c74597210067f73597210067e73597210067d73597210067c73597210067f43597210067e43597210067d43597210067c43597211467f72597210767e72597210767c72597210767e42597210767c42597210067f32597210767e32597210067d32597210767c32597210067f71597210067d71597211467c71597210067f31597210067e31597210067d31597210067c31597210767f21597210767c21597210067f70597210067e70597210067d70597210067c70597210067f30597210067e30597210067d30597210067c30597210767f20597210767c2059721014fe75d93210767e75d93210147e75d9321004fd75d93210767d75d93210047d75d9321074fc75d9321074ff73d932100cfe73d9321004fd73d9321074fc73d9321076ee72d9321076f571d932101cfe70d9321076fa70d932101cfa70d9321004fd70d9321076f970d9321004f970d9321004fd76993210067e65993210067d6599321076bf6499321076bc6499321044ff76593210067e65593210067d6559321076bc6459321004ff7559321014fe7559321014fc7559321076bf7459321004ff735932100cfe7359321004fd735932100cfc7359321006bf4359321006bd4359321076be4259321076bc4259321004ff705932101cfc7059321044ff7695321074fe7695321004fd7695321074fc76953210167e65953210067d65953211473f5495321004ff7655321074fe7655321004fd7655321074fc76553210167e65553210067d6555321005ef7255321075ec7255321114ff7654b210167e6554b210067d6554b21005bf7454b21005bc7454b211d67e65d0b210067d65d0b21
  | 34 => 0x8141006f94118141206f84118141006fb3118141006fa3118141006f93118141006f83118141024ff75594410267f7559441044fe7459441044fc74594410467e54594410467c5459441004ff735944100cfe7359441004fd735944100cfc73594411567f53594410067e53594410067d53594411567c5359441004ff7259441074fc72594411567f52594411567c5259441024fe7159441024fc71594410267e51594410267c5159441046bf4159441004ff705944101cfc70594411567f50594411567c5059441046bc40594410467f74594410467e74594410467d74594410467c74594410067f73594410067e73594410067d73594410067c73594410467f43594410467e43594410467d43594410467c43594410067f72594410067e72594410067d72594410067c72594410467f42594410467e42594410467d42594410467c42594410067f32594410067e32594410067d32594410067c32594411567f71594410267e71594410267c71594410467f41594410463f41594410267e41594410467d41594410267c41594410067f31594410267e31594410067d31594410267c31594410267e21594410267c21594410067f70594410067e70594410067d70594410067c70594410467f40594410467e40594410467d40594410467c40594410463c40594410067f30594410067e30594410067d30594410067c30594410267f10594410267c1059441014fe7598841004fd7598841074fc7598841074ff739884100cfe7398841004fd7398841074fc7398841024fe7298841026ee7298841046ef4298841076ec4298841076ee3298841006ed3298841046bf4198841026ee2198841026ec219884101cfe7098841004fd7098841046bc4098841004ff7558841014fe7558841014fc7558841004ff735884100cfe7358841004fd735884100cfc7358841026ef7258841046ef4258841046ec4258841006ee3258841006ed3258841026ee2158841026ec2158841004ff705884101cfc7058841074ff7694841024fe7694841004fd76948410167e65948410067d6594841004ff7654841004fd7654841024fc76548410167e65548410067d6554841005bf7454841045bc7454841174ff76544410167e65544410067d6554441025bf7650441006bf7650441004bf76504410073f75504410073c7550441026bf65504410273e6550441006bd65504410273d65504410063d6550441026bf63504413febd6350441006be6250441025bf7150441047b77150441026be6150441027b66150441027b65150441007b55150441007bb7050441245bc7050441007b87050441005b87050441004ff7558041014fe7558041014fc7558041004ff735804100cfe7358041004fd735804100cfc7358041004ff7258041074fc7258041046bf4158041006b
  | 35 => 0x77865d81410067865d8141007bb74d8141007ba54d8141007b954d8141006fb63d8141006fa63d8141006f963d8141006f863d8141007bb43d8141007b943d8141006fb62d8141006fa62d8141006f962d8141006f862d8141007ba42d8141007b842d814120ff341d8141007ba41d814120ff041d8141006fb75d8141006fa75d8141006f975d8141006f875d8141006fb74d814120efa74d8141006fb54d814120efa54d8141006f954d814120ef854d8141006fb73d8141006fa73d8141006f973d8141006f873d8141006fb53d8141006fa53d8141006f953d8141006f853d814120efb43d8141006fa43d8141006f943d814120ef843d8141006fb72d8141006fa72d8141006f972d8141006f872d8141006fb52d8141006fa52d8141006f952d8141006f852d814120efb42d8141006fa42d8141006f942d814120ef842d8141006fb32d8141006fa32d8141006f932d8141006f832d814120efb71d8141006fb51d8141006fa51d8141006f951d8141006f851d814120efb41d8141006fa41d814120ef841d8141006fb31d8141006fa31d8141006f931d8141006f831d814116d7e75981410057d75981410067f65981410067c6598141006fb60981410057f755814116d7c75581410067f65581410067c65581410067f65181410067c651814124ebf6418141165de7318141005dd731814101efa6018141006f96018141005fa7618141006fa7618141006fb65181410077b65181410067b6518141006fa6518141006f96518141006f86518141007786518141006786518141007b97418141007ba5418141007b95418141007da7318141007d97318141006fb6318141006fa6318141006f96318141006f86318141007bb4318141007b94318141006fb6218141006fa6218141006f96218141006f86218141007ba4218141007b84218141207f34118141007ba4118141207f0411814101efb751814101efa751814101ef9751814101ef8751814101efb741814101efa741814101ef87418141006fb5418141206fa5418141006ba5418141006f95418141006b95418141206f8541814101efb731814101efa731814101eda731814101ef9731814101ed9731814101ef87318141006fb5318141006fa5318141006f95318141006f85318141206fb4318141006bb4318141006fa4318141006f94318141006b94318141206f8431814101efb721814101efa721814101ef9721814101ef87218141006fb5218141006fa5218141006f95218141006f85218141206fb4218141006fa4218141006ba4218141006f94218141206f84218141006b84218141006fb3218141006fa3218141006f93218141006f8321814101efb7118141006fb5118141006fa5118141006f95118141006f85118141206fb4118141006fa4118141006ba411
  | 36 => 0xf705514122ebc605514116f3c50551410067f65d89410067c65d8941014fe75d8941004fd75d8941014fc75d8941004ff73d894100cfe73d8941004fd73d894100cfc73d8941006bf43d8941006bd43d8941006ef32d8941006ec32d894101cfe70d8941004fd70d894116d7e75989410057d75989410067f65989410067c6598941006ef6298941005fa7098941005f970989410057f755894116d7c75589410067f65589410067c6558941005df7358941165dc7358941005fb7058941005f870589410067f65189410067c6518941006ed6218941014fe7518941004fd7518941074fc7518941074ff731894100cfe7318941004fd7318941074fc7318941006ef3218941076ec321894101cfe7018941004fd7018941004fe7694941004fd7694941074fc76949410067f65949410167c65949410073e5494941004ff7654941004fe7654941004fc76549410067f65549410167c6554941005bf7454941045bc74549410073d54549410067f65909411c67c6590941006ef6290941076ec6290941005f67190941005f57190941005bf7590941005bd75909410073f65909411c6be65909411c6bc65909410073c65909411c63c659094140dbf739094140dbd7390941045be7290941006bf6290941007af6290941007ac6290941025be7190941007b67190941005b67190941007b57190941046bf6190941047b76190941005bd7090941226bc60909410057f755094116d7c75509410067f65509411be7c6550941006ef6250941006ec6250941047ac4250941005f77150941005f47150941047b44150941005be7610941046be7610941045bf75109410473e7510941005bd75109410473d75109410053d75109410073f65109411a6be65109411a6bc65109410073c65109411a63c6510941045bf7310941415bd731094140dbe7210941047ae7210941006bf6210941025be7110941046bf6110941047b76110941005bd701094121ebc6010941184fe76945410067f65945410167c65945410073e549454116f775194541014ff765454116cfd7654541044fc76545410067f65545410167c6554541005bf7454541045bc74545410073d54545410067f65905411767c6590541045f67190541046f76190541025bf7590541005bd75905410073f65905410073c6590541025bf7390541405bd7390541005be7290541025be7190541026bf6190541047b76190541005bd70905410067f65d81410067c65d8141014fe75d8141004fd75d8141014fc75d8141004ff73d814100cfe73d8141004fd73d814100cfc73d8141074fe72d8141004fd72d8141006fb50d8141006f850d8141006fb30d8141006fa30d8141006f930d8141006f830d8141006fb65d81410077b65d81410067b65d8141006fa65d8141006f965d8141006f865d8141
  | 37 => 0x8241014fc75582410067c75582410147c7558241004ff735824100cfe7358241004fd735824100cfc7358241004ff7258241074fc7258241024fc7158241006bf4158241006fa3058241006f93058241026fb1058241026f81058241014fe76d954116e7e65d954116cfd74d954116e7f54d9541004ff73d954100cfe73d9541004fd73d954100cfc73d954116e7f53d95410067e53d95410067d53d954116e7c53d9541074fe72d9541004fd72d954116e7f52d954116e7c52d9541044fd71d954116e7f51d954101cfe70d9541004fd70d954116e7f50d954116e7c50d954116d7e76d95410147e76d95410073f74d95410067f63d95410067e63d95410067d63d95410067c63d95410073f43d95410073d43d95412ef7741d95412ef7441d95410067f74d95412ee7e74d95410067d74d95412ee7c74d95410067f73d95410067e73d95410067d73d95410067c73d95412ee7f43d95410067e43d95410067d43d95412ee7c43d95410067f72d95410067e72d95410067d72d95410067c72d95412ee7f42d95412ee7c42d95410067f32d95410067e32d95410067d32d95410067c32d95412ee7f71d954116e7e71d95410067d71d95412ee7f41d95412ee7c41d95410067f31d95410067e31d95410067d31d95410067c31d95410067f70d95410067e70d95410067d70d95410067c70d95412ee7f40d95412ee7c40d95410067f30d95410067e30d95410067d30d95410067c30d954116e7c6559541005fb7059541005f8705954116cff75595410067f7559541174ff7459541006bf7459541004ff735954100cfe7359541004fd735954100cfc7359541004ff7259541074fc7259541184ff7159541006f77159541004ff7059541006fb7059541004fb705954101cfc7059541006f8705954101cf870595410057e761954116e7e76195410047e761954116f3d74195410067f63195410067e63195410067d63195410067c63195410073f43195410073d43195414367f6119541437774119541437744119541005be7695141046be769514116dbd75951410073f6595141016be6595141016bc659514116f3c65951410163c6595141045bf739514142dbd739514116f3f53951414273d5395141005be729514116f3c5295141025be7195141046bf6195141047b7619514116f3c5195141005bd7095141236bc609514116f3f5095141014fc76551410067f65551410167c65551410473c5455141005f77155141005f47155141047b4415514116dbc7655141016bc7655141014bc7655141045bf75551410473f75551410073f6555141016be6555141016bc655514116f3c655514141dbf735514141dbd7355141005bc725514116f3f5255141007b77155141025bc7155141007b47155141046bf6155141047b7615514116f3f5155141005b
  | 38 => 0x5bf7454b41045bc7454b410073d5454b41045bd7690b41006bd7690b41005bf7590b41005bd7590b411c6be6590b41046bc6590b41445bf7390b41445bd7390b41047ae7290b41006bd6290b41025be7190b41005bd7090b41226be6090b4116cfd76947412ee7f65947410167c6594741025bc74947412ef3e5494741014ff7654741044fc76547410167e65547410067d6554741005bf7454741045bc74547410073d5454741004ff7558341014fe7558341014fc7558341004ff735834100cfe7358341004fd735834100cfc7358341004ff7258341074fc7258341046fb7058341046fb4058341046f84058341174fd75d9641026bd74d96412ee7e54d96412ee7c54d9641024ff73d964100cfe73d9641004fd73d9641024fc73d9641074fe72d9641026ee72d9641004ee72d9641004fd72d9641026ed72d9641004ed72d96411767f52d9641026f671d96410267f51d964101cfe70d9641004fd70d96411767c50d9641014ff76596410267c65596410267f75596411767f5459641004ff735964100cfe7359641004fd735964100cfc73596411767f53596410067d5359641004ff7259641074fc72596411767c5259641024fc71596410267e51596410267c5159641004ff705964101cfc70596411767f5059641014ff7655241024fc76552410167e65552410067d6555241005f77155241025f47155241047b741552411757e7598a410057d7598a41026ef6298a41014fe7598a410767e7598a410147e7598a41004fd7598a410767d7598a410047d7598a41074fc7598a41074ff7398a4100cfe7398a41004fd7398a41074fc7398a41006ef5298a41076ec5298a41076ee3298a41006ed3298a41024fe7198a41026ee2198a41026ec2198a4101cfe7098a41004fd7098a41026ec6258a41004ff7558a41014fe7558a41014fc7558a41004ff7358a4100cfe7358a41004fd7358a4100cfc7358a41006ef5258a41006ec5258a41006ee3258a41006ed3258a41024fc7158a41026ee2158a41026ec2158a41004ff7058a4101cfc7058a41074ff7694a41024fe7694a41004fd7694a410167e6594a410067d6594a41004ff7654a41004fd7654a41024fc7654a410067f6554a410167c6554a41005bf7454a41045bc7454a41076ee6290a41006ed6290a41025f67190a41005f57190a410057f7550a411757c7550a41006ee6250a41006ed6250a41005f77150a41025f47150a41154ff76546410267f65546410267c6554641025bd76d0641046bd76d0641026bf65d0641006bd65d0641026bf63d064143ebd63d0641006be62d0641027b661d0641027b651d0641007b551d064124dbe70d0641026fb609824101ef860982410057f75582411757c7558241026f86058241004ff75582410067f75582410047f7558241014fe755
  | 39 => 0xd52d895113e7c52d895113e7c51d895101cfe70d8951004fd70d895113e7f50d8951006ef6298951135f57198951005bf7458951005bc7458951005df735895118ddc7358951145f77158951005fb7058951005f87058951006ed6218951044fe7418951004fd7418951074ff731895100cfe7318951004fd7318951074fc7318951076ee5218951116ed521895101cfe7018951004fd70189510057d74949513067c649495145d7f739495145d7d73949510157e72949510176e72949510067f62949510076f62949510066f62949510076c62949510257e71949510077671949510077571949510167f61949510177761949510057d709495126e7c6094951004fe76d0951004fd76d0951044fc76d09510157e75d09510057d75d0951004fe7690951004fd7690951074fc76909510057f75909510157c7590951006bf6490951046bc64909511c73f5490951004ff7650951004fe7650951004fc76509510057f75509510157c7550951004fe7610951004fd7610951074fc76109510157e75109510057d7510951006bf6410951046bc64109511a73f54109510057d74945512ee7c64945510257f73945514557d73945510057e72945510067f62945510257e71945510277671945510267f61945510177761945510057d7094551044fe74d8151004fd74d8151004ff73d815100cfe73d8151004fd73d815100cfc73d8151074fe72d8151004fd72d815106efa50d8151006fa30d8151006f930d8151006fb6098151005bf7458151005bc745815125e7f651815101efa6018151006f960181510467f7559741044fc74597410467e54597410467c5459741004ff735974100cfe7359741004fd735974100cfc7359741004ff7259741074fc72597411867f52597411867f5159741004ff705974101cfc70597411867c5059741045bf7655341156bf76553410473f75553410473f6555341016be6555341046bc65553410473c655534144dbf735534144dbd7355341005bc72553411873f5255341025bc71553411873f5155341005bf705534122ebe60553411873c5055341014fe7598b41004fd7598b41074fc7598b41074ff7398b4100cfe7398b41004fd7398b41074fc7398b41076ee7298b41046ef4298b41076ec4298b4101cfe7098b41004fd7098b41004ff7558b410067f7558b410047f7558b41014fe7558b41014fc7558b410067c7558b410147c7558b41004ff7358b4100cfe7358b41004fd7358b4100cfc7358b41046bf4358b41006bd4358b41046ef7258b41046ef4258b41046bc4258b41046ec4258b41004ff7058b4101cfc7058b41074ff7694b41044fe7694b41004fd7694b413067f6594b410167c6594b41045bc7494b413073e5494b41004ff7654b41004fd7654b41044fc7654b410167e6554b410067d6554b41
  | 40 => 0x52510057d72952512ef7671952510057d71952512ef7571952510057571952510167e619525101776619525125d7e7095251026ef6298a51044fe7498a51004fd7498a510067e5498a511467c5498a51074ff7398a5100cfe7398a51004fd7398a51074fc7398a510767f5298a51076ee5298a51146ed5298a51076ee3298a51006ed3298a51024fe7198a51024fc7198a511467f5198a51026ee2198a51026ec2198a5101cfe7098a51004fd7098a511467c5098a51026ec6258a51004ff7458a51044fc7458a51004ff7358a5100cfe7358a51004fd7358a5100cfc7358a51136ee5258a51136ed5258a51006ee3258a51006ed3258a51024fc7158a51026ee2158a51026ec2158a51004ff7058a5101cfc7058a510073f7454a512ed7c7454a510073c7454a510053c7454a510067d6454a5146e7f6354a5146e7d6354a510157f7254a510176f7254a510767e6254a510076e6254a510076d6254a510057f7154a51007777154a51007747154a510167e6154a51017766154a5125d7c7054a51044ff76d0a51024fe76d0a51004fd76d0a512ed7f75d0a510157c75d0a51006ee62d0a51006ed62d0a51074ff7690a51024fe7690a51004fd7690a510157e7590a510057d7590a51046be6490a51006bd6490a511c73c5490a51004ff7650a51004fd7650a51024fc7650a510057f7550a510157c7550a51074ff7610a51024fe7610a51004fd7610a510157e7510a510057d7510a51046be6410a51006bd6410a512ef3c5410a51076ee6210a51006ed6210a51026fb609825101ef86098251005bf7458251005bc7458251026f86058251004ff7458251006bf7458251004bf7458251044fc7458251006bc7458251044bc74582510067e54582510567c5458251004ff735825100cfe7358251004fd735825100cfc7358251004ff7258251074fc72582510567f52582510067d5258251024fc71582510567f5158251056fa505825125e7c5058251006fa3058251006f93058251026fb1058251026f81058251176be54d9151176bd54d9151004ff73d915100cfe73d9151004fd73d915100cfc73d9151006bf43d9151006bd43d9151074fe72d9151004fd72d915101cfe70d9151004fd70d9151006bf649915116df57199151185f77159151005fb7059151005f87059151046be6419151006bd64191510447c76551510157f74551510173f74551510073f64551510467e64551510467c64551510073c64551514657f73551514657d73551510057c72551510077771551510257c71551510077471551510167f61551510177761551510057f705515122e7c6055151044fe74d8951004fd74d895113e7f54d89510067d54d8951004ff73d895100cfe73d8951004fd73d895100cfc73d895113e7f53d89510067d53d895113eee52d895113ee
  | 41 => 0x4ff705944201cfc70594421a67f50594421a67c5059442046bc40594420467f74594421a63f74594420467e74594420467d74594420467c74594420463c74594420067f73594420067e73594420067d73594420067c73594420467f43594420467e43594420467d43594420467c43594421a67f72594420767e72594420767c72594420467f42594420767e42594420467d42594420767c42594420067f32594420767e32594420067d32594420767c32594420067f71594420067e71594420067d71594420067c71594420467f41594420463f41594420467e41594420467d41594420467c41594420067f31594420067e31594420067d31594420067c31594420767f21594420767c21594420067f70594420067e70594420067d70594420067c70594420467f40594420467e40594420467d40594420467c40594420463c40594420067f30594420067e30594420067d30594420067c30594420767f20594420767c20594421c4ff76548420167e65548420067d6554842005bf7454842045bc74548421a73f5454842075bf7650842006bf7650842004bf76508420073f75508421a5be75508421a5bc75508420073c75508421a53c75508420773e65508420773d6550842076bf635084247ebd6350842075bf7250842047af7250842076be6250842077ae6250842077ae5250842007ad525084247faf3250842077ac3250842005bf715084221dbc7050842014fe7598442004fd7598442024fc7598442024ff739844200cfe7398442004fd7398442024fc7398442026f67198442026bf4198442046f74198442026f44198442026f63198442006f53198442076f72198442026f4219844201cfe7098442004fd7098442046bc4098442004ff7558442014fe7558442014fc7558442004ff735844200cfe7358442004fd735844200cfc7358442076f77158442046f74158442046f44158442006f63158442006f53158442076f72158442076f42158442004ff705844201cfc7058442004ff7558042014fe7558042014fc7558042004ff735804200cfe7358042004fd735804200cfc7358042004ff7158042024fc7158042046bf4158042076fb7058042046fb4058042046bc4058042046f84058042046b84058042006fa3058042006f93058042076fb2058042076f82058042026bf6499251026bc6499251026bc645925116ebe545925116ebd54592512ee7c5459251004ff735925100cfe7359251004fd735925100cfc7359251006bf4359251006bd4359251004ff7259251074fc725925116e7f5259251024fc715925116e7f5159251026be4159251026bc4159251004ff705925101cfc705925116e7c50592510157e74952510173e74952512ef3e64952512ee7d64952510073d64952510063d64952514767f63952514767d639
  | 42 => 0xc71d95423067f41d95423067c41d95420067f31d95420067e31d95420067d31d95420067c31d95420067f70d95420067e70d95420067d70d95420067c70d95423067f40d95423067c40d95420067f30d95420067e30d95420067d30d95420067c30d95421be7c65595421bcff75595420067f75595421c4ff7459542006bf74595421c4bf7459542004ff735954200cfe7359542004fd735954200cfc73595421d4ff7259542006ef7259542004ff7159542024fc7159542004ff705954201cfc70595420057e76195421be7e76195420047e76195420067f63195420067e63195420067d63195420067c63195420073f43195420073d431954248e7f621954248f6f421954248f6c4219542014fc76551420067f65551420167c6555142005ef7255142005ec7255142047ac42551421d4fe76949420067f65949420167c65949421bf6f5294942014ff76549421bcfd7654942044fc76549420067f65549420167c6554942005bf7454942045bc74549420067f65909421c67c6590942045ee7290942046ef62909420073f65909421c6be65909421c6bc65909420073c65909421c63c6590942075bf7390942485bd7390942075be7290942076bf6290942047af62909420067f65d85420067c65d8542014fe75d8542004fd75d8542014fc75d8542004ff73d854200cfe73d8542004fd73d854200cfc73d8542006bf43d8542006bd43d8542006be42d854201cfe70d8542004fd70d85421bd7e75985420057d75985420067f65985420067c6598542006f761985420057f75585421bd7c75585420067f65585420067c6558542005df73585421b5dc7358542005fb7058542005f870585420067f65185420067c6518542006f56118542014fe7518542004fd7518542024fc7518542024ff731854200cfe7318542004fd7318542024fc731854201cfe7018542004fd70185420067f65d81420067c65d8142014fe75d8142004fd75d8142014fc75d8142004ff73d814200cfe73d8142004fd73d814200cfc73d8142024fe71d8142004fd71d8142006fa30d8142006f930d81421bd7e75981420057d75981420067f65981420067c65981421b5de7398142005dd7398142006fb60981420057f75581421bd7c75581420067f65581420067c65581420067f65181420067c6518142226bf641814201efa6018142006f96018142074ff75594420767f7559442044fe7459442044fc7459442046bc7459442044bc74594421a6bf54594420467e54594420467c5459442046bc5459442004ff735944200cfe7359442004fd735944200cfc73594421a67f53594420067e53594420067d53594421a67c5359442074fe7259442074fc72594420767e52594420767c5259442004ff7159442024fc71594421a67f51594421a67c5159442046bf4159442
  | 43 => 0x9642004fd70d96421c67c50d9642014ff76596420767c6559642045bc74596421c73f54596420767f75596421c6bf74596421c67f54596421c6bf54596421c63f54596421c6bc5459642004ff735964200cfe7359642004fd735964200cfc73596421c67f53596420067d5359642074fc72596420767e52596420767c5259642004ff7159642024fc71596421c67c5159642004ff705964201cfc70596421c67f5059642014ff7655242074fc76552420167e65552420067d65552421c5bf74552420473c5455242005ef7255242075ec7255242047af42552421a4ff7654a420767f6554a420767c6554a421c5bf7454a42045bc7454a421c73f5454a42075bd76d0a42046bd76d0a421c5be75d0a42045bc75d0a42076bf63d0a42496bd63d0a42077ae62d0a42077ae52d0a42007ad52d0a42005bd71d0a42225be70d0a421c57e75986420057d7598642076f76198642014fe75986420267e75986420147e7598642004fd75986420267d75986420047d7598642024fc7598642024ff739864200cfe7398642004fd7398642024fc7398642074fe7298642026f63198642006f53198642076f72198642026f4219864201cfe7098642004fd7098642076f46158642004ff7558642014fe7558642014fc7558642004ff735864200cfe7358642004fd735864200cfc7358642074fc7258642006f63158642006f53158642076f72158642076f42158642004ff705864201cfc70586421adde7398242005dd7398242076fb609824201ef860982420057f75582421c57c7558242076f86058242004ff75582420067f75582420047f7558242014fe7558242014fc75582420067c75582420147c7558242004ff735824200cfe7358242004fd735824200cfc7358242074fc7258242004ff7158242024fc7158242006fa3058242006f93058242076fb2058242076f82058242014fe76d95421be7e65d95421bcfd74d95421be7f54d9542004ff73d954200cfe73d9542004fd73d954200cfc73d95421be7f53d95420067e53d95420067d53d95421be7c53d9542044fd72d95421be7f52d9542024fe71d9542004fd71d95421be7f51d95421be7c51d954201cfe70d9542004fd70d95421be7f50d95421be7c50d95421bd7e76d95420147e76d95420067f63d95420067e63d95420067d63d95420067c63d95420073f43d95420073d43d95423076f42d95423076c42d95420067f74d95423067e74d95420067d74d95423067c74d95420067f73d95420067e73d95420067d73d95420067c73d95423067f43d95420067e43d95420067d43d95423067c43d95423067f72d95421be7e72d95420067d72d95423067f42d95423067c42d95420067f32d95420067e32d95420067d32d95420067c32d95420067f71d95420067e71d95420067d71d95420067
  | 44 => 0x22e7c60551520057d74949520073f64949523067c64949520073c64949520063c64949520757f739495249d7d73949520757e72949520776e72949520767f62949520176f62949520057e71949520057d7094952006bf64d8552006bc64d8552044fe74d8552004fd74d85521467f54d85520067d54d8552004ff73d855200cfe73d8552004fd73d855200cfc73d85521467f53d85520067d53d85520067e52d85521467c52d8552146f651d85521467c51d855201cfe70d8552004fd70d85521467f50d8552005be7498552005bd7498552006bf6498552006bc6498552006f76198552005bf7458552005bc7458552006bf6458552006bc6458552005df73585521dddc7358552005fb7058552005f87058552006bf6418552006bc6418552006f56118552044fe7418552004fd7418552024ff731855200cfe7318552004fd7318552024fc7318552026f65118552116f5511855201cfe7018552004fd7018552006bf64d8152006bc64d8152044fe74d8152004fd74d8152004ff73d815200cfe73d8152004fd73d815200cfc73d8152024fe71d8152004fd71d81520b6fa50d8152006fa30d8152006f930d8152005be7498152005bd7498152006bf6498152006bc64981521ddde7398152005dd7398152006fb6098152005bf7458152005bc7458152006bf6458152006bc645815226e7f6518152006bf6418152006bc641815201efa6018152006f960181520467f7559742044fc74597420467e54597420467c5459742004ff735974200cfe7359742004fd735974200cfc73597421d67f5259742004ff7159742024fc71597421d67f5159742004ff705974201cfc70597421d67c50597421bcfd7694b423067f6594b420167c6594b42014ff7654b42044fc7654b420167e6554b420067d6554b42005bf7454b42045bc7454b42014fe7598742004fd7598742024fc7598742024ff739874200cfe7398742004fd7398742024fc7398742026f67198742046f74198742026f4419874201cfe7098742004fd7098742004ff75587420067f75587420047f7558742014fe7558742014fc75587420067c75587420147c7558742004ff735874200cfe7358742004fd735874200cfc7358742046bf4358742006bd4358742046bc4258742046f77158742046f74158742046f44158742004ff705874201cfc7058742004ff7558342014fe7558342014fc7558342004ff735834200cfe7358342004fd735834200cfc7358342004ff7158342024fc7158342046fb7058342046fb4058342046f840583421c4fd75d9642076bd74d96421c6bf54d96423067e54d96423067c54d96421c6bc54d9642074ff73d964200cfe73d9642004fd73d9642074fc73d9642076ee72d96420767f52d9642024fe71d9642004fd71d96421c67f51d964201cfe70d
  | 45 => 0xc7358252074fc725825209e7f5258252004ff7158252024fc715825209e7f515825209efa505825226e7c5058252006fa3058252006f93058252076fb2058252076f820582521c6be54d91521c6bd54d9152004ff73d915200cfe73d9152004fd73d915200cfc73d9152006bf43d9152006be43d9152006bd43d9152006bc43d9152024fe71d9152004fd71d915201cfe70d9152004fd70d91520073f75d91521c73c75d9152006bf63d9152006be63d9152006bd63d9152006bc63d91521c73f53d91520073d53d91521c7af52d91521c73c52d91521c7ac52d91521c73c51d91521c73f50d91521c6bf75d91521c6be75d91521c6bc75d9152006bf73d9152006be73d9152006bd73d9152006bc73d91521c6bf53d91521c6be53d91521c6bd53d91521c6bc53d91521c6bf72d91521c6bd72d91521c6bf52d91521c6be52d91521c6bc52d9152006bf32d9152006be32d9152006bd32d9152006bc32d9152006bf71d9152006be71d9152006bd71d9152006bc71d91521c6bf51d91521c6be51d91521c6bd51d91521c6bc51d9152006bf31d9152006be31d9152006bd31d9152006bc31d9152006bf70d9152006be70d9152006bd70d9152006bc70d91521c6bf50d91521c6be50d91521c6bd50d91521c6bc50d9152006bf30d9152006be30d9152006bd30d9152006bc30d9152006bf64991521bded72991521d5ef7259152046be6419152006bd64191521c5be7619152006be76191521a73e75191520073d7519152006bf6319152006be6319152006bd6319152006bc63191521a73f53191520073d53191521a7af52191521a73c52191521a7ac52191521a73c51191521a73f5019152046bf7519152046be75191520463e7519152046bc7519152046bf7319152046be7319152046bd7319152046bc73191521a6bf53191521a63f53191521a6be53191521a6bd53191520063d53191521a6bc5319152046bf7219152046bd72191521a6bf52191521a6be52191521a6bd52191521a6bc52191521a63c5219152006bf3219152006be3219152006bd3219152006bc3219152046bf7119152046be7119152046bd7119152046bc71191521a6bf51191521a6be51191521a6bd51191521a6bc51191521a63c5119152006bf3119152006be3119152006bd3119152006bc3119152046bf7019152046be7019152046bd7019152046bc70191521a6bf50191521a63f50191521a6be50191521a6bd50191521a6bc5019152006bf3019152006be3019152006bd3019152006bc30191520447c76551520157f74551520173f74551520073f64551520467e64551520467c64551520073c64551520463c64551524a57f73551524a57d73551520076f72551520757c72551520076c72551520167f62551520176f62551520057c71551520057f7055152
  | 46 => 0x8954044fd75189541a6bf541895448e7e541895448e7c54189541a6bc5418954074ff731895400cfe7318954004fd7318954074fc73189540767f5218954076ee52189541a6ed5218954006ef3218954076ec3218954024fe7118954004fd71189541a67f511895401cfe7018954004fd70189541a67c5018954044fd75d8554004ff73d855400cfe73d8554004fd73d855400cfc73d8554074fe72d8554004fd72d8554186f651d855401cfe70d8554004fd70d8554005ee7298554005ed7298554006f76198554005fb7058554005f87058554006f56118554044fd7518554026bd74185544367e54185544367c5418554024ff731855400cfe7318554004fd7318554024fc7318554074fe7218554004fd72185541567f52185540267f5118554026f65118554156f5511855401cfe7018554004fd70185541567c5018554044fd75d81540f6bd74d81544b67e54d81544b67c54d8154004ff73d815400cfe73d8154004fd73d815400cfc73d8154074fe72d8154004fd72d81540f67f52d8154024fe71d8154004fd71d81540f67f51d81540f6fa50d815422e7c50d8154006fa30d8154006f930d8154006fb609815401efa6018154006f96018154076bf6499252076bc6499252076bc64592521bebe54592521bebd54592523067c5459252004ff735925200cfe7359252004fd735925200cfc7359252006bf4359252006bd4359252074fc72592521be7f5259252076be4259252076bc4259252004ff7159252024fc71592521be7f5159252004ff705925201cfc70592521be7c50592520157e74952520173e74952523073e64952523067d64952520073d64952520063d64952524ae7f63952524ae7d63952523076e72952520057d72952523076d72952520056d72952520167e62952520176e62952520057d719525226d7e7095252005be7498652005bd7498652076f76198652044fe7498652026be7498652044be7498652004fd7498652026bd7498652004bd74986520067e549865213e7c5498652024ff739865200cfe7398652004fd7398652024fc7398652074fe729865213e7f52986520267f5198652026f6519865213ef55198652026f63198652006f53198652076f72198652026f4219865201cfe7098652004fd709865213e7c5098652076f46158652004ff7458652044fc7458652004ff735865200cfe7358652004fd735865200cfc7358652074fc7258652136f65158652006f63158652006f53158652076f72158652076f42158652004ff705865201cfc7058652076fb609825201ef86098252005bf7458252005bc7458252076f86058252004ff7458252006bf7458252004bf7458252044fc7458252006bc7458252044bc74582520067e545825209e7c5458252004ff735825200cfe7358252004fd735825200cf
  | 47 => 0x800000180000010007000c004001c000000400000100010044002000c0120000000000c005001400000080020008001000c00600100020000004000000100000090000000000000000000080004000000000d000000100480000000000002000400000000000010000800800000000034000000c01f00180000050010001c003001c0010004004002001f000000200040000000002002c000002c005001000c000000300240010008002000800800000000008002000000000000000040000000400100000030004001000000a001000000040030004004000000b0000000000800000080010030004000c008000800b0028000002000100100000014004000000b0000002000400200140000030024000801a002800100000030008002001000000080050000006000000000000000000002000000500040010004001001c000000800d00000010000000000000600000020000008000400000000030000009001c005000c006044fe7498a54074fc7498a541c6bf5498a54046bc5498a54074ff7398a5400cfe7398a54004fd7398a54074fc7398a54076ee7298a54076ee5298a541c6ed5298a54046ef4298a54076ec4298a54024fe7198a54004fd7198a54046bf4198a5401cfe7098a54004fd7098a54046bc4098a54044fc7458a540467f5458a540467d5458a54004ff7358a5400cfe7358a54004fd7358a5400cfc7358a541be7f5358a540067d5358a54046ef7258a541beee5258a541be7c5258a54046ef4258a54046ec4258a54004ff7158a54024fc7158a541be7c5158a54004ff7058a5401cfc7058a541be7f5058a54044fe7498654026be7498654044be7498654024fc7498654024ff739865400cfe7398654004fd7398654024fc7398654074fe7298654004fd7298654026f67198654026f65198654176f55198654026bf4198654046f74198654026f4419865401cfe7098654004fd7098654046bc4098654044fc74586540467f54586540467d5458654004ff735865400cfe7358654004fd735865400cfc735865416e7f53586540067d5358654004ff7258654074fc725865416e7c5258654046f7715865416ef6515865416e7c5158654046f74158654046f44158654004ff705865401cfc705865416e7f5058654044fc7458254046bc7458254044bc7458254004ff735825400cfe7358254004fd735825400cfc7358254004ff7258254074fc7258254004ff7158254024fc7158254046bf4158254046fb70582540d6fa5058254046fb4058254046bc4058254046f84058254006fa3058254006f93058254044fd75d8954004ff73d895400cfe73d8954004fd73d895400cfc73d89541d6ee52d8954006ef32d8954006ec32d8954024fe71d8954004fd71d895401cfe70d8954004fd70d8954006ef6298954006ed621
  | 48 => 0xb0048009000c004000000300240000008004003c0030024000000c0050000001000000f000400600100010020000000c0020020005008400a00080120030005000c0220038000001401d0000004000c00200000050004000000000100080060004007000400700180030000005004800e00000030000006000c00100140020008003000c001000c0000000000000c0000018007002c001001000200040000004002002400400080000004004000800300100060008002004000f000c007000801000080050000000000400e002800000000020000007001800a002c00c0000002005c000001400100000060030003000001c000c0000000001000000000300000014004000401d0000001004c000000000c0004001000000a00180010004004000400300100050004003000000000040000000003002c01200000000028002000400200240050000002005802b0008009001800100000030038003000401100200000008013002c000000400b00000000000005000401b00080000018002000001500040020004007000c00c0010000000000100000000000003000400b000c0000054002000000e00180070000003000800a00200030004002002c0070000001000c0010000000000400100040000000007005400300000010000001000400800040020000006008c002000c002000001600080020000001000400b0050010001400c0024006000800d0008000000c00300000000028002000000f000000c00040080068001000000300000190030009000000f000000000180000014000000000500080160004000000800700000020000001005c00b000000000000030008009000400000580000000002001800100100090018034000400600000000010001002c000000000000180020000017004000f0008014001400600380140008010001c000000000200180020000000001401f003000000000020000000000400c000000000080030004004000000a004c004004000000080030034000000000000080000000000000c00500380030008001000c00200fc0030034010000800200240030000000002000000280000004002000000500000050018007000400f00000010000000001000900080010008000004400e000c0000014000006c0020010000000c000000400f0000000001c007003c002000000a0004005000c006000800d0000030000c0020000000000000000040000000002000000000000040000001000000100140000008000000400300080070048005000c00200100000004000002c00100280040014005004800000240050004006002001d006000300000030034000000000f001c0020000003007000000000020000003000000000100030020000001000200000000000000000c00c00000090008001000000000100020
  | 49 => 0xc0010084009000800000000000040000000000300140010000005008c00b00040010004003000c000000c00d000c00c000000b000800f002800a0004005000400100040000014000001800300040010010000000800400040000090000004400100000000004000000000800000060014022000000000140000000001001800000500010008000000000000000030004000000c000001400a000400200000000000017000000100040060000001000000700140000068000000400c00040000004001000400100000010008002000c0060010000000801400380010004010000c0000008007001000f0028001000000400100020004002000c00c000000000000000018001000400000000000000000000800200240010004023000000100000000020001000000200100000014002000000000240010004001000000200000010050002000400000000060008002000800600180000010001000c011006c000000000000080060004009001001000040040094001000800000080000008000000000b000800a0000005000400a00340030000003002000100000000020003000000800000100000007000000700000050010000001400000040010008000000400000180000024000000000200580030000007000000200000000004000000400000080030004006003c0030000002001000100040030000009000800f0048000000000000000000020003007c000000400000080010014006003002d00180210024000000400700040000000000000000a00000010004000001800900000010008001000000000040010014000003400200100010000000002400300200040000002000800c000000100000000034000001401400280020000005001c000000c0030018001000001000000010004001000800000200000000000000c0000014003000400000040080000002001c0000000006000000a0034004000c00e00000020000000000c0040010000000c00b00040000004005001c001000c00d002400000140000004010000401200040000044002000000c0010019000002300040010018001004c001000000000000000010000000800600140020008001000800400000000000001000c00200000000000001000c000001c003000800a0004000000c000001000800240010004046000000000280010010011004002200080040030004000c0000000000000c0000058000000c0060004000000000700040000008000000000d00440010008000000001b00400000000003000000500000030004000000c00a0004000000001a00080020010009000c002001c001000000900080010004000000c00100000040030001000c001002000100100000018006000000000440110038001000c00b0000000003c00900280000024001000c0000000
  | 50 => 0x400a0004007001400000280110038014000c000000400a0004000002000000600010004000006c00700080040030017002400100000000004002002400200280000020001000000c0004004001000100000110008002000000e0008001000000000080150014012000000000140000008004000800200140020024007000c0210000006001c00400000030014014001c00100340000010000000400200040000000000000800000080070070021005c00900040020010000001000e000000100000080014001002400600280040000000000001c00000000014004000000000400010000001000000100100000008001000000e0000003000802c0014000001802f00040020008001000c000004c0020010008000c00600180000008000001000b00000000048001000000300000000014000000000600200030098000000000000080010000002001000300040010014005000400200000000000000002400a00080090000000000000700280080000000005c00a0000005005800d0028001000000f0050009001000300200000020001000000a000c0010000000002400100100020000000000000b0024001001800c0010001005000100080020014003002000200100000024015009000701200040000000001c00000240020020000000400e00280030004000000c0170000000000c000009000200040030000000006c003001c01a00000000000002004401300140000000009002c00300140000000004000001700980010000000002c019000000000000030000009000c00000080110014000001000100480030004002000000100040010000001000400400000010000003000800b000400100100010018000001001b00000030000002000000000180010018006003000f0038004000c00500000020000000000c0030000003002800a000001e00000070000002000800000100050004000000000700000010000001000000f00040010000000000800300040030004007000c00a0000000008000b00000020000004000400100000010014000001000600180010044017005800000000050000000000000700380000000000001800100040010000002002000100040010000001002c003000000200000030014000000001000080000008003002000000140010008002000000200000000060024000000200140050000000001400000000070004000002001a001000100480020000000000000000140000010000002c00b00040020008007000000800040090000001000000100480040000004000000200040010020003000401b0008002000800400000070024000001400000040000018000000000e000000400080090000007001c0000004005000400100040020008002001400800040130010000000c000000000600100110018001
  | 51 => 0x30000008000c008000000b002400600000000004002000c00100040030000002000000100000000008001000c0010010001000c0040010000003c0000000001000c000000c028000800000080090048002000000100000040000000000000a000000700000000000007000000d000000200000030024003001c001001400600180030008001000001b00280040000000001c00300000010008000000c00a0000004000000a0028000000c007001400e000c00f000800200000000000005000c00200000070034003002001500180090000003000000b0010005001400c0004000000400b0000000003800f00080000000003000000a003801b000000b000000000000000004013008c0010004001000000100200000040001000c0010000004000001a0004002000000300000030000002004400b0000007000400200040010000000002000a00000090038000001400000080000000006002000100000000000000000000d000800000000020008001005c01200040000040003001000000180100010000001002300040050008007001c001000000000040000000000000c00000180010000004005400200100000004000003800900000000004000002000000640000000000000c0000000001000000400080050000000000c0000004006003c002000c000001000a001c00400040000044016000c0000034004000c0070020001000000b0000000000001e0004001000400b001000b000400000200060014001000c0000014001003c00200000130004000001000100080040000001000c0000008001003400100000000030013003c0000010004001000b0000000002400100300010000002000000000000090000000000000100000010008001000000300100000034003003c0010000003000c00000240000000002000000200440000004006001000e00240000000027000000e000800b0000003000400000500320004000000000300180010018000001c002000800000000140004005000400e003c000000400400040030008014000000000140080000001000800100040020048001000000700000050068002000400000540000000000001800000180010000000001800a000000700000010000000002c0020010004002c00500000030000016001c000000800400000010000015000800900000020004007005c008000c00e000800d0008001001800c000001000000000004001000800f0000007000400300040040000000000000200000090000001003000200040050000006000400100040000000000000000000300000004000000000900000020024000000c003002400300300010000000000c0000014000000000a000c012004400a0004000000801500080000014001000800600000010018003000000100000010004003005
  | 52 => 0x390dea741f780cf8000f6ba9d65b4262a192ba7c0003d948383e7c772800000037309eba924eea00001d9800000035b800039bc000000000012c6c94000094c800037200000000000e77a2801af97a8a39ad12254237cc71a9a860f349400000000c32158658a254ae22128d20a786000179874219ee1da00000000000000142230c126a00020183b48000d2e0fd620600000003952c041768c651f463d500cc4238eb4aa2b5327f2afa80003b4263901e0d29274cbda800000024aeb8b1bce12300006d500005d698c200035d0000000090f00009da8000cda0000912a142fa81448e282146933000082f8000000212e0001c5a000267a2080e520000000531ac5400000000000000fdf95d8eb500000003c86070a22800030b8be2800012dbaca936240803d1bba0001cdcd09a59abf687109c3a5e8a6080003a30000b8680005108e68b3c0000c92008a0000000c071d787cd215400000e600000000001a5668b05bc5cb3aa8f660000aa4bb3262d8e84c080e6e465b066eb31e08000358894f87dad3d1652a240cae5828000cca83fcbb60000000000000000000000b92dc48000a0304c072b365a00018a00f2000090e347427b133e86500002c11496aa600001f9000002400009a700002a30f941e7bb44ce612b000000002910000000000093d350e9080000000114000000003d0000000000000000000d1a240a0003eee1ee8000000320ce9b0000000391c621a4780a3b73ac8d31229830000e45800000000000001ad6ae00000000000000000006131c460000000c2585e09f99840a1133749c180006f31290fd5924cac500009cb81220002b1ee4c36a8295000000028ac0002d8096c102ca40afdccaa1fb497e299aaaba6a43338b3226189a4c2d84b28332a6004f23f49c28c34101bcf8ceaacbc5c5aece6ccac4873e834811a871aaadade00003dda6a7b5208b91e78f828f58f14210c09417f47e688ee7660000db211c64fe8c6237a1c54000081470c1d3e9518000f3723ea0000000000000000000020074001000800000000030008000000800800080000008000001c0010000003001c001004c00100540010050001000400c00140070030003000000100180030018003000000400080000014001000c0080018004000c003004800100080160000002000000b000c000000c002000000000000020000001001000000340020004010006800100000080000000001000a0008004000000a00000020000001000400000000040000001000c007001c00a000000300000070000013001801900000050008000000c003003400100100000004000000c00300000020010000000000000000010050001001c0000018001003400b0000003003c007003c015000000800000110004021001000d00040040008000001c0080014001005800
  | 53 => 0xb23520758a4305648f1362c7cc8000e959a789f524240002b260003c7098f9b223b305b886dba7800000000000000b9e21c004aa0d00000000aa380007a42b8400012460d4a2980188000bcc9594720a52e00033b4f9808845173222a73b84cc630a760002bf00001ca84e3ac38000000033600004be3cc2ea2800028ab22c0621bae46ea0960001c24fa2bf5e21b10600888ef004530ec000101635109768a08bb20003366000361800000006ab800038229e251980000003a1400000002498000b1da3508fb800021a1ba80002c7e3b0bedc00000ca343ba4c00000000000fac95a9f4a2621cec000000066c96dc00000000000e8800025740002d48a390000c4282d2e42bee27700e1cc6db7ac00000008fc8ddae3c8d0220aa23023d184a9a10678a8e8fb0b7e3f3a8ef8ffc7180000000000054627f4000142aa6000004aa000050b9a68e572cc0c28000078e0000000000000000007a50000e65ad64000127eb23800073600001f7b39a000099e00036ea000113e000000000000000003c8a0002828c6c0000bc0ac568d9800028f80000000000ca406d0044af20edb8094543b822000293e9bb000077c80000000000dc38000bf6311e7918000cb6000031903c2000000049f21fc6610000e2bacd854d0aaa39ca7ea000000055d07600002f482649f38fab106ce880780d591600f0322d82a8b846d963dfcfb787b0b3e1f105ef8712f691d50cb22b1a00000000003bd009f0f141fb1afa5c10000c73a852397b80623a00000002f44862258474c9ee201c80009aa80000002f78e9717b60003c12f530000c2180003d586047340f0613d1262c978d08de3a0927040b4e0000000747193e3c690024dc8000804131e1450000188a8fc00015a074c0ddc9f1ae0ea3da21c0002f46746b8366a003be000170e7f108de000000000000000001774dc13a46000087600000000001728988bcee9ab8db000000009fe3c3eee4a24e83926a6d66064c811174613e2ec430189c845300001de8b3a000000007681464762388219bc92640a3d415200009acacea5c18048f619b46e3c0516bf399cccbcbe041fe1dbea91ac24407000000004a21c78d823a700000003bf00000000000203474a84c200004d800000000000000af70000db19c14000269006c800026e220a000000000000003f1862c9da1416caa81ca000315000014e26ae80002b980005bd2b94e0c80001209faa00025ec0000000f7b80008f8000000000000000000a799288b6880000001e44b2c8d3200014c81c9800016500004d6055ada7000034e00007e3090886119aa00028d2ef2000052000002c814403c10000d498e960001a08000298abc11326f701f0800039ea0002d92b3900005970000000192e4ca166657c00000003d568d7acf6c549ec2866bc2402fbf46c1c132cb9
  | 54 => 0x379e000000000033180001bc0000012e01fa6560fca81c00007160000000d26b66a000233400029ae00015bc3158ee0d9f9ba400000000000c2068280003e82362d340000d28b6d60a7bb0620422d29593a523c600003bf95020128000c1e80000001e640000000c6d3c16a45800000026000002f4ef1f00000000000e5a29a20001ed8e1439906da80000003b7a000227e096a1380001d1e3c78d4a000267ef19948279a8000000001405713deb7c247090431ccc880272cf6000079595920002f58f4280008af8b0a8f780009ceb2c4ddd0058ecd3390275ae30cd0b5563dd81ee9c9a940000000043c80000000000afc8000000043c5f2000000026e8045b8022d8a08e899ac843848000c179674d1e00008aa00006169a581680394c8205d200007c2dcd905a6003a6ae8a03f6df914f4000323c5bc900a0003ab60000ae4e1c8000b7c95c2a0995b42a920fa000000010580003ab800000000000000000000000000039f69708000000000017d000055f800076131fe000000000039440002710a87171a27480000000000fcf8000f72a54ad1500000000214e30139462600006148b12732b322a4835fa3442b3c000000000021ac0000000b2b34800000a2c60d800000000002ec0f4a16a887200000000002f068e49cf257f8bee4d3aa580002c620003686aec9ac05023cca5873ed00002dc0ab79b189d18440ea92a081e69df800021b4e3a96c6033800079512a20a236bae8982be5493830000000094180009bc0bd000000000000000f448000000000002589fe1e10000000000000000000000000fa58cc06b60000efa8ef2215948a4ec1af8b4824842331f8e7380f96f969760fa6126cd70b576156050682712c266e3814caf8000000010038586a609a80d40001280b6084048c728a658c80000003afc14c122e000000000000001a5194685fbc46bca8d9217fbbd800000000001b3cc100000c74b2123fb000000000000000d0000018180002bd4e502140e7e289c77337fe27537c2356116a6a42998cfa1a1a7873e50b8b8a865e18f24e7bbe4600012525793acebc280000e83e4a2980000000000000006087bd00008210000f5d000000000004da80000002aa2f2c8e94a8c0000e619160069ba70ba69ec81519b1ea5d19b4bc32dce95c12f6871ba6848e22b22eaaae8f0e83027630656fbfb65007a90746630a6e77c0aecbdb10aa0000424000107e00000009df8000052169c46b11fc00000000000000be731da000000000000007ba8000000390c000000083e00005f80000c66a6cae6d18ccaaf835e00000000000124876249200000004e70000000000000000005770000db4bc3600000000000cc4ae380000000000c0f0050da00000000020ae5400005900cd44cc2270f3f800000038d20000b228dd00000001a6c00008
  | 55 => 0x2a43b798da00000000000b688df8b722fda7d27a737e00000782c9f980c030000039fbdaa00000000000cf43f613f6eec16be4061404342937436e90ac29683b845614ca2f3382a00010e855a80007be903000000000002864000393661c1ac20423f08000070aaf600006232fd20003f3c00005b40002904f6f9baa0000000fd6000000008580001f4e79c06ae5590a8009384c652317d87a9aaa496aa74010cbf265f08130a8a80643431f6200024285eab66636622b4b9b0e3415e331c5c73b82203800000009388d500004c73e181080b7830580000001f4c39580000001752cb8205e63804cc0773ada4ba88fc245b2d220f9af295f289200004a8e21a4d6ee90000d0480000e0a41456c90bc0002cc800000000b59d0a0000000f62b39e3ee8d946db00006e7800000000007398000bfc83b424b27f2d0f00000001c88f36a4740002b8ca230000000060a000000000000000002288e80000070781c600000002bea46000017c60000000000000000014ae00000000002c445faa35c00020eec7f2f54000000000011f0429800000000009329546000317a0001db40000e0a11b8000000000000006d20000000d082b0632f800073c18f2b25af6e0ab18220073022f0102bc00000004780000d3928ae355b4fa7bf1c1c40c800091e8000000062ea90305c7c484460000212f340ab4ef780a2fcd2132ba2369a0000000000000000000000000000e4880000778000000000000000006680000da9a490b9196787f689f08122046a1fb7661c0b03eadfa7ecb862ed0c592e26d77a06a1eb13f26ba13fc6608be048924bc499248608a851c903ba4eb77b602b6f91c8a2a999a03630b2879b45e4f994b8dbf85120d8afc6fcb1de0aed0c4688400009d680006f40000000052264d8000ad82fe0b378000b428000886130ed7d80000000eb800006cc0003aae0001d460000000ec6b196d0a80005898000000363ef738198bb7a3242cd08fa0003004435000036a000000036e8ee28eea00016706f98cc267d04b80001b96a3280007bd80000b00000d6c000000037d8000197a00000000002c000001492a2f968a0001eb099c04da00000000003582f86b0006e095284a132fa901800000000000000a30ed81f66bc3acec537adb47af9c36e3bb18ed75a4424312bc881c15840003cac1790000f670000f3d3a2ec9c0dcc8dc050aaf5b2d05b60000c9300fe1199ca60000000000352c15439ecc0087d873f00006d0aa500000000000000082780000000bf400000000000000000000001d2452b8d80000000000000053c2818000000202cdd6117050380002b200000001dd46ff00002a22f9484685901548ec8d5a0d22000276600000000000742de2a4e6ad433c27a93d8200000000000000eb23840c7aadfc00016500000000c6801b800000000
  | 56 => 0x3f38000000000000009ed831c0000000595070e5391cae0003da200003ce0003e06c5f800009036480002a88b0bacb0f698000e3200002f5b924386094e043202a000353a0003ae20001c00cb18d520003ad8e22958c28a0000e6c000000036fc74d8000d78800087a800006d992c0003c9ecd40000c9b2f5aa049feab6b80007698084c06800060e14a62fc000000000000003d703b9985c60380000df03e00001d1600013841758c60a8a000063a0000e86898a30280000001d480001e2ea0280008cab8e29e80ffe9a7a28400000000002ad827609aa0001db8d93a73493a00000002aa600004e40001f0c000000000010542803c64000058a0000000d3d8886b412dd06603b48000318491400000003900b5e39ba0003d30920baa000000000003a9600000000003a3e14c80000000066ea216ccc31356c5d0b66ee2da7748740600000275e00005a49a800009c7bdc80c00c1a52dbd7c2c180007f182600003aea0000f38000026cdb713d27cb300ab24800034f9a4a0000000ece0000e950000f23000020b3ec8a2134424be800084580003093136d0c819c1a63e82ef490288e82c1ac1e3cf01efb7701462eae0b608a43bf07dc7843eda824016ef74161e5bbaae20000000000284e000039a00033be0001b2485400002b88ba8000021cfcc81fadf7a552a4792f462d0000e2a80003168000d9b057c8e005a60000e48d1b0000210a9c00000b2800035ee95cb1f6fdbb47eb8500002841d180000000674ba1878d86402a10794426814c37b24f659b09fc5b8beaa8c0b670b4da488005908246509f8a2000000000000214ace80000a6ab4b86bc000314870e030e4fab84830eaf340001ec0ab10d060000000118a576000000000000000001dfa9b680000000000089003a8b52cfc0003df2fb4800017a91da0a01e680003c20aaa32bc79380001a789dc8752836ee623ec0089a6e29c8000c92ab22065afc8d7d0000748000071e36a03b891ceda58c4a00020a26a0800088cb5ac000308804800da656260aaa3227679b8000512a4a630a2550b4f00000ad00006e52ce250cb94ab5a944cae81f6a0000000000115a9188000000088e0003f36f911874b49a2648f6a95641280000000ca40003396c840000c3f35b2efb020cf93af7000021ae238000000031a4dc01aacf840000f3616f6000000000024a0000000000029dca78383a49e99d889f00003b7000000000000eaaa760000000a99050e00000000000000a9f33de4669d58b00b36a00012de0001d94bfa83ea3698000000000044db4c60003b9ab961a5a00000000899434304896cd71120000033a05fa3af00be00000000000e4508f6a062d7c03e80009efbbf61a12a4ea3a318af2abcec02092acf598c2e5151caa040845abf3040eb6d800081a00004b5b26600000000000
  | 57 => 0x1bd2000003c7388670e2c0000793000099631ca00000008e60000000374a000374e709994a0000be2249023e7aa00005e6ae1c80f8afc7dcafbed7c1d645cebcea8fe142605f282c0c5abd22caa9fc000199697300004f90d4ea1a8000657236800017e65060000a1d2610c7b8000b8580000000000000000012480007758000cf9a47232c000015cb410470332c000073c217037a0002134e44000028f00002cf1c08000118c0000acaece832a2608000bbc15081c12d74a0e97ba15986e0000281a680838cf433b4e36232261e39934370810ebcbb9aa71c800000000000000000f7786d8ba5800000019104ef3b54000000000008266a580000002b30fd8074c0002a9c68d2cba0002ea68cb80006cf94a800000000002c6cc8c2466b260000d5697226dd8000690340c000000098d99e00b8800000038e4ad600003adae20cc080000000000000000039000008ff00000000000f12873820708020003d50000248c91a8000bc88000e04aedca86b41ac8197786338000000154cbe9000040d8000f1d00003618000c4b80000000000f90a990b9580000000a1ce0b00009b90b1822aa074c11b6de2bd06f6b62800008604ae00012a40000000ce00000000000011c80000001f6c0001718000000000000005d121dca108000161800000000005e900000000000000000000000009e13d6a00000000001ee800024c600035aa2fc968caea988e2b194aa00022fcead3b6c637855e9f6062a2943c086bc3ddcefb910e183252a722a31488131ba4188fca00038c616f9b8a00038560000000afbaa3e9c6b524dfe289e0c1a48edc0b688e0b800000019aecd8859e280aeba3fbbadc146ab38892124267e20f0dca25f2afa2782213bb58977114ee18973043b800041b99cac1ba5ee0000026f88ad087318000b808708000000000c00008593dc20002be685b8a62000009e34600000003338000000000000000000000000220c000000000013167d0b59e4bb3d2e0002fd60000000c4f83ec2c73e9c0000000d1839a2000000042db04cb56baaac608000724a66600023bcb2890769b19e7eb3c80009b40000000094ac77a13a48c9e02f1b3bfa00011b232c88c87cf80004f4000004700003da33b000000005702f9e000000000000007da380c0000000df50000c2a03de6a800a49c08d6a546941412f82b2e981d68db29f8a50c32e8a5a176ad7a272469ebac2c55a95282500009f00dc42ac22e07eb84d2b4ab3b2e4a000000033a4087a87a94e800067eac4259686c4b5b8290000000000000000003db4d432f12c0c2fac5a996ec1700cf21743e32dd5111c36c88540948f845ba9b5c517aab0cbda5a21cd00aa0ea045e8961344a9d2bfc00020e20000000ddcb1c24d88000391800097d000000031dc7c73f22f8abc2aac10dfa0002ad493f8000
  | 58 => 0xa86700000001da4cf800000000abcf801bc84d18000c3a2efca0fb992000000059caafcfd68746ed58000414bc3216ba598bf51cba6498000000358000000b0000378c0000fa6c59897c816a61435b8f8c59138b2afe218ec5e23221588b76f9fbe2e6d58000b7b969039b00009eb139090a97e2c99128c86909a6000324e5ca849092700003c3b90e313361a6fa35b6d3712ae8202b0040f002a000265aca93cd4000000014ba7c8b0da8d011201e22959b440000000000000044a171e00010f000035407b1b9a62ba1568aac86167509c94244800023a800000000001e58000cf7000000000004d2b2008ec85c28ae0bd83788d04b24000043e33f832291d074e88d40000000000000083d18a6b5786e2e0417620000000df280000002f62ea4a120a2f0000000156e1e8880a558a1087f22b9a43e9b5a6213202a0a800035d2e7242e00000000b884b30000000000014abf2800026c20000000fdca3068b437e2d648000d1d8626d970334784b59000019e20000000f0405fc0000000d0900003b10990880b7e60000e5800017120000000e733de00001fb0e4b30c00000bbad32920adb8800000000006a8b6dadde248a92b2868a0904e00cc28a8000059c57217d49cb1dea000025e9dbb0e200000003be9166e413bce7b400000002cda0000b300002328569892e53a8000000000031d8000000000011b00000000ccc0000000f088b2603835464a8000000036c49070d9a0003974635a3c80002a66ded800000000000000000000000000023aadc588c400032564d68000cf400000000e62e3583980000c103680000000000079f17020003cf2ac2342e1868464d1e800000da676805bca0e23800000027a6ac610d64a70e1ad25877ce5e2dc2ebf800000000005580000cbf14845b50000eddaf80d0129c40000000000250e0002a68000199eefcbc5c4adb12650337c09b31bf670f80009f3ae8400034a8a862688e709134a323d8452915c6e0f0e7a1fc132a39aaaaca75154a17627bcd8a98560e932aea72b4becf30ef83672e5c5a4ab349c019983ef21e28a53ae843819a40912beadd7bc884fc0b9e91100008320000d819eb29d580000000d469ae07bc2672dc8b5d800000020520000000d948032f2e000088bb1e81b02854ed4b44010aa1a800000000a880008c58000bfd1e3e3198aa60000000a03a29afbf0000566940a0000000c32800000010ec46280000003d589b731860e2a2c6d9310fc5eb00008e504d6252332048509404eaa4ee000286c21191de0001e88a95031e22f0000e8a86ea54eb288d76186212f00ae8a8872495eba5e88fada8d7e3116e20b4d469883726f6b2eca4ebf62e26b7f20000000000229cc553d38593bf0a00000005df89140000000ed98832fb000000000eba0003eb60001f5c4ee17f2468af28f52
  | 59 => 0x87e00000003e9260400000000f8a3ed953e0000000000399ac392318ba80b6e0f881fea9215b883f8cfc95e200292aa3202f02cd0061b42c0003a3c80324c29f7a97825e8000d24bb745c00bea000000000000000000000000000068980007c39056c762f4000000000002e5400000000001cea0003a7a00018a2ee1000040100003e000002e2800053480009c4a15ac8c8000000302600000000002c8af51817600480001cdab4ce88a11445fa78c9f0ac260000000359bc6a00022f2000314a6e1297626100004078000000000026e887e44e35e60002abc2ef1990bfa38fafb299a29a6abfa95081e40000c8c0002bf40001bfe00006d471d00006ed9b5eecd8000c2a800000000000ca2a723458000dea000081f00003b023ac1139308a369cb200001d8000000077719a84c531b84b4b8ec38b80000c43ece7fe00000003cb00000000a81902a10887c80001a10322367400000000002f1e8c3096a4020c8600018d40002ffa03e000000020c60003ebc91780000001d7600006c2c412dd40002d4634e8000000000047f800020e22ba00000004e6ab020001f6e861892285d0000beebd1e000143ac3a80000000dee00034d8db82feed772afac4696d2f8da4809881c04a2d14b2dd1223c50f0000dfd18ee4272c9e6a7196c0001918000063893c162a74431c431eba86000298ebdf00003ac328ec1d1d220003ce600026d2ab2b34a37c0000115a77c066800099c9e34f8789b462508dc00019400cb1ddee6784ace6a0b2485c00000000000608345663a8000a1200000003d082358000aef2fe2d4d1d6ceb98f888db80008a38000df49a484f13f0e93e2f503d6ad2200000000001a0c00000003c029340003b2c000000006b01a000000008f2800000037fa6c3b39c2440002d2c000000029580002b6ac1680008dab31000029da00000002f512f0ce48000dc93f149899a460000000c2539945cc8000d0a2c0400000008600000000000097d80001e92a860000be8000274aaa0a5b430500000002bac70480000003d96e2f8010403bde200010941c5328a80c11526b3000057500006340750f851fcc011b2eed311578139800076782b8f4d0000e7d1bbe23480000001f223ca80003a4b6640003e20a3cae7c38409561d52c285fe2446177083c45400f6be30000125800000039060003058000259c0000000000000000010ca76b8000cd307b864c8dd6654982afb32caa266ab761850ca800000006bbb336cb7195e837ab2ef21387c40483ae0000fa43e71efe642103856700a05f6893412213acdc7800096e1bdcc90a7b84cbb8e80000000e92b4460000000e198000c96a5a8000000035b39726719a36000078800001f8c750000a05800000000002f080009de18468f6290600002ce000207a6d380000000000000184eec810d
  | 60 => 0x32492b2e29132eb03728ebc2d31dbc00032b47b51a5000000002048944e741b4800000004ce80000000f9833b239a000174caf30e826df000000011a600000000000000c960000b69af3cc6f838e6f91220d5410aeb6506460dc018c4cda0867108f52948819e49438680000688545000000000000b21628cc78aba6aca9de1f8b5a8a4e0000e7000009ec11f60000000000110c000272000005a23cd8d64cdf9dfcb2218ba0693af850da4deb7a369000007727942ca42853f160000000b45800000000002f686c6d3080000000d780000000000000028e00009a03c440002a9a291b6c0000357a4960000c440000639af5eacd8308a692148b718000d1bb160ac48000ec60f48a8e1ce4cd814f01e4a634a9c2ee60002a5aa6227fe0003a5827111fa78c1796ada18bcdd88000dcd34860a80000b163ea26feacc4860b218f7a19bc7263678fb0b3004c33e58b50084ac7c00002b00000000000038d800000000006d301560000000a30800000006dc000040c0001e762c3aeec6b50000fd2ac5070b05c60000000a6d0000cb2a31200000008163dc46ca978e0000000d811c560003e888d180009c2333e0db8f3078a8fd200035067878000000000000020ba1d71a700002dcc000000000000000002f3000000007cd800000001c8d56000000038161f2a54800000002638000e180f0a0000000000000066236fa000000059eac063fd88c64a600925b1028a573144efc82e526f0881e07d0b7eca8814a6db9a74d5303f000022a000000001b6b3280000000b3589bc88e80b20000d84a6f0000aca17a6aec36cceedb998f1b9088eae8b8ceb128b6b7d9210a7e23f69458000f0710ba00032e400000000001e3a000000031abf680000000cd500000003ae000026f60002156000034020d287c58e1ba070333b6000000095680005e88000c108000e9f8000000000063b1bb4000000000000000000000000000090b0000000000000000001c7162c3503d028930220797a96a000358c0000000d880000e243cc4225000000020da72f00000000000303a458cc3bf00b1e8b8690fad8821903327fd156cdfda8e041a955ae108f6a8dd803eeaf128e34690d01610574000020472592e8186141e6ce0000000000000000000000000ca781440001cfe0000000ec8a2920002950d3e1ed2cc5b9ae83d9de6f2f95726b90974eff000013eb2ba290123c038843000021febd9281e000256c4a18a90000340a1e415067348000ce0afd0f1c800014911a02f48c780003d440002dba6fc82ee9e5006c0003d680a6b6828d0b5a0ddf0b7023908167749aca0d2883a8bdb20a47525b62e91f800158902af293f80000c4eb2a12aab1c98822e5841800000000000000000000003a3e62f1fadecb6720987908b56a69b56a0002f3a00006b4000235a48886fc00
  | 61 => 0x1a88ef700008c9a236000000067f9a0436da4764f59d34a59178cfa380000000408ebbb9665641c200b6a10a0a4849ac4f048647baac2c9a8000fa19e5a3811612c87800028616ac8b70a4203b946aee1a92a5f48000997399c0000000c07b7aa5f599740001e14478bf5c0aa3a5adf7000095387e804b19f05560000a8d3e765fc000000012600002d6200000b4000266458bac6ab96914a22fa3640000000e82119266d80001de0000ab32d8687bb090e878be402e8dfc5a81f88f632ba68b786f08578c265f0216c27a00008ec2ff6dc40d2000000005f900000003a360002250a222f7600000000001512b3480000001b060003668c51839049dbb2e22339d8000000000035309beb462abb80000001f900002f680003bc400000000001b0c000000000011f86010000752915ee1d182600018ac2cf93e027d94cc8730000e29a1180b109ce5d40ac4bff1322ebcbf123261d44e7f94d4f9abe9a5a215f87ae816c749866445a27980002cdc56c1ab07c080000f480006400000000000000000003f83f1e983848400017720002c180000000000000000024d200007aa0f2bbb800036b8def2588ba0b5443f380000000000000000000008b800018b00003dd40000000000005a8e5aa0ae0900007dd80009a5181ed348a1ac2889d09ca0f9a0000806000268c0001816000000000029008028e7800028babb5227400000002d8352eab8338814e8900fb527489ac085ece29334af7bc3cd2e800000039345bfa6eea85391a76cb0cc5789f2001a11143f908ae890b5aebf78f507411c4063e9e2613a05dab2723d6335828c13c998e00003b2e0128380002a7a16217b8c038000aa580002ef83440002032000000034d800000038feec08000b9a0000000256000000000001afcabfa066ef32b7a83287fcb35000083f0000000000000039c60000000dcb0000c7c9536187ad1c8f09f7a57a0000bae0356bd294020000000bbd08c25428526499be5cd891eccb5cbcf69c6046854a93380003d6000000003fe000059f00000000a9849e0dbc0000000000000000000007c925c00001feee588000b6686d600035100b30f78ab3a4be000000000008e6329800061b00005043a428bb049c000000000000000000000f3000000000000279000000000005c4000000000000000b1ea4f00004031f966a18000000000081fad6600000000003ad66c2225e000149e24e9f2ec5005d4350830463dbd32f1225866f81d0039f314cdf40242f200c50b6b22e6c8593a80000000000096000000006818000a4a0000000000000013da31d3da00000000acc81f2000000051a00ec65cb4e2cf58000000000008b8000d4a34e80000e901f00254102bf1800000007f39f5e09235fc44880000003bac82903cc44ea062f9c2d10ac90ad802e16faa21bc4c0f50e
  | 62 => 0x157000000000004898ade00018c4000302800000000003a0617a0000720000048a9fe806eb40885c80000000000000112c00031980000000336a5dea0ba93600005b049100006cb1c64b9da6fca589e280200f6200000008db28020003c5a0000ff40000000847076e34a000099200008ab000000000006849ea287200000000000000122c46900002cd9f0631f0000736a9920000000b8000000000000f4f8134b5a10427f819680000000000309200018dc4088000000196400032b06cc11d2000000005e000012911328141360d52000049d27363bb0ca2a000ca0fb81d0c0000000000307cbb9125a74b3d64be08a242de9352cf3b0f404dbb460a12772d23000027d28d80000d729cc80000000000c211d0ee31005cec5206e2a68b4604c80000000000a7d8000dde9ff06e40000bfe00008c380000002e3c25ca2ee730968299780007868000c32069a632298c7e9b614aea21e444238daf32128a3dd043ed88bd2c0d907feb98800000000009158086d1f00003ea17cc1ea02107e60000a65970c6d416c0883a2c40002d189719740fdd9f5600021b04bb800067f03d8dfc3d5275893ae3a3beaef6c8cba00015be7cc0a7a4f39b0ae0005f0641a0561a5853eda3024608d30c6000018a00033d25483d80c50b14e77d86cead2302a6eb1b700000000f0baa800000000000371cb07279c4c4ad24eb496f84202d0e96b0adc9003e9e00000000001eae09335be917000077180005a606527138000000327a6b8a4faec4ba409aeb706eef0000ed900001e80d7ceaf8cf0e2a03d60da000062cac3a24c80000002932bed808c00015d265f83ee1fea0b06aa2d06f97800080bae2a7658000de929125cf8000302180600000004af3e52cc1ab2ab198db4f411e6c0e015a877a06b624796e60001c189d880009861896ed8b57053b2e9c82b9f3c4e097fe0d6a75073ba8f4483a5a0c949470035b31287c3a824051b74f348df80a6257e056216a8e78da2bfc0c6e5dc1ab47f4aac0a1b800000000008628880fbd32149ba920401e80008a4000015b969400000001a403465f2b976be9abfe864153ca5f99dc00000001d12e4c7d210e6dd4141cb409ffc5e4800023e07eeb46ba0e00000002262ee8000195600003268c43baef009ec409c015e5a93cd6c448eda4c1844af2a032e6120570bd800000000000000000056e8000000000037626c0a578000887b4386020000a130000d7180000002cf42f1a642000065c46f0000150983e0002d3200013fe00024b2f5b800000000003778000000013e90580000468000820800000003f40000000339938cd0d800041600000000aa80000000854be081370000e6f94dc634804400000000bd00001250000d0617840000000edc8000000000000028e200021100000f4ee498676b9d0fc2000206c0
  | 63 => 0x60b000032380000003bbab0c96fc0001116118000075c8000bec800000000000000000987343400035e01a00000699341ed408e261ae8000e69302c3742556000000085a0cf60003d5c0002436a7d2d540001f26ea6a896000108afad2004d90916c7b7bb5081c9aa468b80000002eea4b10f465928000cae000011d22440003e7aadbb0be4ad0af600035a600000000001450ad3810a5dbb8dc92885bac40a88e8f000000003068000121cc6897b2e2e9386000237a0003f640003d4a9ea95ecc37800089abc580000000000302e87680000000126cb58000000000000000008a29c326c4b3a6000117a0000000a01935646130fe0000d9e000249438a800000000005402b20000000083080000001f7064f38d469a99b00002738000398c24a133c00000000000000dec204ee98a03c4b928b24521fe4dcf8668000104e7c10000ed28bfce32bcbc42a000010b8f1c7d4abba92e00000003820e3600004c900000000620e2d0000515800000004c4c7000000001754a1e2f16fc1033871bb2f0f0a2be40000000f9b9a16b168000c8aa780a6713a61941a3c5d980007fc9f4400025201ed800065c0e4ce5f2c80d688000f4a000024dae6e6b4000e33aaa62cf214f20000000000264e000000024180000e18000b9fbb1c2d90000acea3308858000807000000024ce894a348486186a2d7000000000007e7b83e00008fe0000000000370c000000001a80000000000f9d33e2d281fb69512c78000049811f80006b700bc62a2e648d11540d9515e00f70000fbca7e0000345c8001ea052380006bf800000297d037380000001df45fe90c60002ed298584b400000001278000000359c7be00000001be200000000003caed3807b20000000d7488ca0000000b04b4164448000dc6a8eebbe3b5ee92341cef01272b911f008c20c2265b8a9c030aa6e7fb2372757903a00037864f1b5143a2800000011260000000000000000037c872c2e6a0000000b1000005ef0000d5b80def10a714f8e0000fd1000029200000002fa2354003801ba2566e980000000648d73b89c36b2d3092d34da7f62dfe000000000029b80000b7c80e00000002faa00003540003660baa8c5c05980000000000ae60000d84bbf4e7a3dac0001d8200022fa00000000d70000aad00002af9ada000000057d2716f890e22ea51b140001db60000e0639280000003f4c6711588a9300003b3979e0000f7e0000000000000086ab16a4400b500108000e4c8a520000000dd680000003006132b5e4ee21ff67b5800000010cce890f3420a0fb80001938000000025faa2000023fe9f937ce98b80000001f6000000000000000a0c0762e6ca91ad628fe859fbc98847aa6cf8a1978075a67cb2b943e25a27e2dab376c00010f4c0c80007d4000000000000002cb400000001658de40000
  | 64 => 0xaec0114b0e01730000b56000054700ac259bb804fa1cd49fc000024a80000000000000000000033082fe8dae0b400001cb19440001aaaef1a2ea0000000eda3c9696b94768b0000067a845c0000000000000000011cc3a905f24f00d96d9dbbe642d3dfe8d82ad63c880006d83d72d830000d3f8000abe33ec0001c0a4fb8000c3c800048098b8000355c70b982e1722dda06515ea000011e6c038f600000001ca09a20000000f268000550bafa5d586f4f9b000001d991256b98020000000a8091ec332945800020bc201108cdad2022926042829900003f5058c891bcb60003c067ca28f063d27ca0000000ae90f020002bc283000000000000b2500000000000000308eee9ac344a4800093500000001bee228a014efe09b20000000243aeac72331061d780004e80000b79155c000054e09f80000000000ce8800086325ea292af109a490844c080009b538ac0001c22f80a568db5241283ab34eea6195a0c68000fafac4af9904dee7c1e160033b2a098b756886804ef3181aa8a194a0ad28d302aca5a62d691c29be1176ecf0cac38b289a1a48a0a0003c263e782c204e3748f620ed010d800000035ba00007d200003c00000000ef83b240d402f6a0d1eca0000000bec000000019c200028fe00000008068000ad1800000000001c824dc54137182508980c5c00000000000e9d0000c83bc68cb0a08ad82a6fe5b680000f900004d0955400016b430c8874ec7a39c0003cce2568444ec2072e00005440002e865b7800000030b48e885ac47aac5e00028220000be6e408fe65a100003982af200000000000000972aae60002426e4600000003948e6b0ed400039707e91aecc7414fc3c3038800013b472e13f40003864208b5ec18f398e9e20c82031919c396903424717b42130000d1692c00000000cd7bd9a602a5e4fdb0000cdb911a7ad285a975070091b9c6c77f8df20cda222b1f38c2858a58a6a68000bad3ade1acb5bc84b247cb08185800035cc0002b96ad580000000000fd0b7b400002b00002b5e1aa0000000142c000000000008aca72000000914b42208774f463594664b50a2d2a0aa47129d806080002da8000df18000b05175cd8cb1723cfb4c0c7ea4c40340aac9af0afe08cb082458ae8c0c80deae28a2e8d5f28ec51139a0db6000055ea7580180000000205c26a2e6671428c4f5b03a62b43df88f9800000018320000000c13b0248bc0000ef28fd00000000e4826c45fd9d4ca498d7ab5b3628a6c10c0054bd9225531380001104d91800000000000003ab2446000000018caa51830ae781da00d9800005a2f5c9b7a75400011b8f390000115192400034de7863f6a2300000dfab982c6980000000000d2b1dec0001960faeb6aeaa116b889700001a70fc09749872000000000037924f09a428403db68f180006220a5c
  | 65 => 0xa7c9544000137010780000003ef04f50c9c000323e0000000aef97802590000000000069791023e499480000000000077ed32000000000000003b0e67d96b6a119d7a9b38000441a3fa6388000362a2aa000066c00013988d3000014000000000a267131a30b50ad709500000000222ae170c58bb2258070ea7fa960a7762c3378450a3c600000ad21fd989cf5e86ac074800000000006ceb108000324465521d255980007f9ae1e00017b0e580b38cfb9e5c000278e00000008222e50000255c5a1b1ae00025f0859b128d3b0000f240a0cc1a8860000000026c2b9c0003cb44900000a8f04261bfaf0851ca08c67680009a38c5edac35080003be27f7000022580000410000000129a5b5b1ec76c01f0000000072d316800000002d480000003e1200021fac97000074e09caba28000000033c4e780000001f7e00000000000e24000000087820d4c2b0000bed3a38d59ab900a58282bb30c7e41a0fbee448cfe1bb19e6d129156cc306f823c12fc0d81e8eee525c89f68d60b4796e0b788ffaafd8070bbdbb9c71fb64a14232d427019d41872970cd2135efae3844deba3e8eae33a86fabf8690628a2d4682f2364335a0000000dfb000051b0528761bc8200000000001e0e94b0ce0b329552dac9580a2604b0cee03b629a0e746b38bf86b2389e209321a9c8b54a514ac4ce91000032f1a1800012f200000000002d98c6b354e000389238c3746b383c9c5eb82060000000ce3800011e0000cd600000002e9200030bcc051ce85ac8000b1a00008f49dd88de0000000000017d80007170b82000000068a0000000000018c15fa0000d7631a3c307c69cbed1600002068000a800000fd21186957bca6530000090d000000000002998000a8995d6063999c31c808eb8d20d62930000d80190ca8dad4aefa2dbc6c80000f588bb40000b5e779000000000000000000d4f9794000000000000000000000000125edd8000085f23a6d4d8000f4db798000111e0000000000000094f0000fb100001d21a7e8e9391e4d400000000000753800016c800000036ecc901e989aa00006d9aa94d3c80005ac21d641eb6d0ca4b464718912eca81510be800c83c99b8cda7b834191085007f11bee7e9462645a820ad52638349a62412e81b49ed3d544759110a1c2c080003c4031000000000000b08bd220001890fb1975ec9da6405d3bc8e000000000000000000cc836aa5900000000000000000000000000000000000000000005aa396cf9c847caf1160e00030ce0000000000000000011a800015b6288000000019be00030dc5e40c2a000203600000003109f541532cb8d088e9eeb40000f8c2e42c95260618901408f70000000351e000363400000000001586f76000000003da00000000003ce2e8c3b10a7316ca4df8000de40f9072791446af1236cba
  | 66 => 0xf00000000000000000090300000001e405c2bd26a679fe20002240d5513c88b89dba000000094c05ecf44129400009a08ee15cacb78e80a2536eec7d1d5a8ab93dc32a89fac030672939274e03f1b64998194e91900000dabd00cde3586c4300a63db3d2000233c4ea30000000356200000002a2bee40ab80002baa1a0000348a00019ec5398d5417b80008b0a9ea097000000032da22480007df37d68cb00004b28000000000090e8000000000000013329cf00000000000d8d8000fc30000000000027880000003ef60001d7e984a566ddf8000cdf214a694a1de00007180000000e070000e1e9364bbb80000002d140000000be481281cc371400031741ddb95ec8e068ac292a420e5863e7bb30a69930000a2c021a2340a96000000000024540002adc00013d800000000002a9eccf0000411b86c0bf315cb6a80008153d1c6a280008a937947d0073e9f5b8dec513baa89a2d8486caf26fa309f22a50000ee800002b6bc34fdd365e7f0177a95329f0bb81c586599e82870b2cc89e00000000000000343e3d08000d66a5bed13273014d222cdce0fae00035da000398870a06020000000a74a630add2c10d21214ee4a873a565b4ae000095e0000000e25068e00022140000000d9f185e22a0b080000000c3bb93aca090c8cb98cdca292f7e2f798c620d804008f0000a6db50000007d6a1430d601f2e7006c1d603750000ef690e2000000030f000057100000000a9e4d00000000000000000009f100000001f582c08000000000061f1edab33a75252fb49e48215de2d0b4a6b0abf02d449c52000213064abc1493a8540000220803700002eb1928000364400000006e6126e5b21d7c0000ba60c4aa5e0de0000ba4000059a9e96ea40000fdf197c00000000b1b4bc4b50000f332df4b3184428021b78b4a1a928d2bca228cbbbeaf834e6881bd0e17e2aec6b4816ace31e9200b822ce859f0ae0214d815a92061a0a1f46cd8556a610000e029c5e4ec8000d8c23ae00000000001d060001e720ce8000c06225a00006620002432d0080000003aa65e209980000000f7ebb40b3bb63c90100002ad8fea9402ab8e53800083616346ec964661faf720000a74000000000001be8ccad7e000189a83c8000c350a12000142089e80000000d62794a512e1fb4d60002b6c000201e75ab6aa3bd8b84e56896e00015a40000000d240f60006a966c343f527768000b3088b643da51800000000000000c561486a46066000010a4f459c665e28000d8b94fa9322f86eda864200000000000000998a178f63907c7e080004b6078a41c80006d8800000004342c5918ef1508f21b22c0a46a958e93887c65881ba26d02198ad11e040000000a53326e9a616429169c8e0000000000029c6f7800000013caf4680008ea35783e0a2c8b8c800000006e63f2000
  | 67 => 0x84ec9a5920003c52a01000003a80000ba0000fa50000553ba66a5c9a240003780246800098086ca09bb304829ae06479b22eea7b0f0026848000000000000000000000000014b000039b86b9960287d84c800016180000000ec28000000000092eb17694782e0ad00000bbc8000ea127e8c4e9172848a85cb8480000000b40b53800000002660000000a2292be216b8e600000000000000224169a0000000000190400030480001b520000000ee89d886e70c940000000000000040b800000025940001b7a39408b057c908687c99a6a5f3a1c00010a201e36f20002eb200000007018000bd0aefe000000003c98aadd484aa293a0a00e7191e7a11842548b6c2de20000af03692000078600016160002384effb35221e8df64972efa35322f40b29b264518000788230a99433f20003b78c483852eed000086e0150581152cb171edc5260000ae88000000000046b9fb82022eb619ea14c00000000000dc6978a0200003ea4def8000b89000000000008af0de6000000000000000003f3090891e43571a5c00022000003d060000000699926880900000148000000388c3f73c1a00029ac000000021c2102b4e80003d7acfef0e000000020280001a3a9d90c6c00000004f88000dfb946e0002fca3bba792000000099b8b100000000e4e0000e808af8000000060c29487549fa064c1950000027aa572bb64ed9eb8dd30b1af6e8000a580000963000000027b20000000cf51ece000044c4679942661851e0000f8600000002000000ad93e840003d4e3800a2e9f432f40000bb60a1a5a4be68000c1822721238c547f781ce2c0000000000000003132000270c4040000000349800039c454e3452ea8800000003bc3dc3016884aa7e936aeca3ca0000c0eb97a5963f2a831150ca18154834d00003d30ad60000000b1c0000000000000005ce5c91a22a31ab103aa8d3c82d0bce1d380002db2b16a7e8c9a00000003df2db00000000c8d80000000732ebb0000cc98000000317c25180000000000000101a00018344938000000385e000328053125fc0000000000000042f8004a9580000001c4a0000000b63ae3a0002e4a0000000804b58eabaa8b8a3aa66c1ac10dc000076400010d20001c440ffb2ceaf89c7c0000000df30000000000000000005cd000054c238a5e82af4a4280d20000cb67ffb332b2980000000000e72bdb032000000000f6e000000000006320000000370246800025240aab4ce8cf264a9b831c8ca1a73ede80878a16000044a80000000000000103e536b0baec3376407b1f3a0260000af184100808c1c199a430000000099d1f2abc531922961024000052c81d88b43880610d903ce80001e22000000008d8458b54bbd621badb8dd70e4273e37fc5930000ab21bec6980f8ed2cae400e48c96ee400000002608000174a51
  | 68 => 0x25c000000008ce0001bf00000000f8f00000fe969e0002c4e000000000012ba84f8000f18b16c0002a6adda80000000314b81000000030f86480000000233e8699dc400000003830ceede9bf502369fbc98a0000e340000000000000000006cd0000068ab5cae48000745184400000000003a320000000000361cfdc00004e89c2a04614bac18a84a000173ce55242e46c00007ee800010e041c000000000000000001178cd10000e51a47e0000e6600014ce6071bb02630000bef215c4b719bae721fd40001e74e5a9a1c0000e287a7800013b8f3c6b19cf40a50dd2bf0217a000000000000003f693663060000eac076a0000000000000000028c0cd9311889b00000000000000335c7c78a1e00000000002064000000000028405270000000010670380000002d8cc201c8694680b60001a320003f66000219236e079818eb72a1e980006b7bd5ac0d8034000000000020602b800004b425bc2ffad902483d42ad0adb2000189e9d80172d3f0000d4ab63a238a6460002eda91b0000c1fa8a0f13800000000000000000b7980000002ada68e0000000000000000000000000979af2c00028d40003f4e81e3c78000265200027f60440e9a000275cd459b8000007ea0000000d65afb8b760000000183a0000000acb000000000008f300000002496f02b53c00000003ab2040942041a4099676b53343a8018000000136ef9533465a59af6c273a3af3780008ad80008679a3e25e1748da8b826d75370a0001ef02859cc80001eac00014d0061139648d296e2460ff2bf98ce463e0bae2298f646202d502709090c9d050487a36f000034b613ab19e78b1b8899a0000ae2a5b214dbdea3939b040000000aee10663d1112000002baa839dc230e1048426089ce2227a8b6586e85cb80009c1000000000009d09fc2000000000036f4000392ea7b9e320001b72000000000000007af30760000b142813b960001a7c0003d3a0000c9200035c0f930342000137658c12965cd9bd400010fea0422ca05539d6edfadfaa4b945ad8e12e22e6a79a0ec066e19f8000000193a00024a8d50a12a00008a05180000b5800004de2b0ed610e3a0001570a61800047280000000000a859b025689776000261ec9800009381d4000000000000cd20000000000165ee0e00002f10d1e29f14e80003072b8e3726de5ae28000320468780000962c2c0f12382bb898141602e9ebb5bde4cebb9e2a5ea832daf8c2cccc20b2e533a0a7492f66c4c1f94f3f00008d00628c26907086eb5388e400000f4186ecc90cb462f8962675b79cceea1c429c117494db6845df3e260000000222bbc200000001299f164da105eca980009ad8520a7180007dd1f646839d8a6428374000121edc83e1c9009180ab180000000000d8580007923a04986b6e621224c05a0310e0733f
  | 69 => 0xaa404d0810a7eedbd800075582e4a48a3e200009b69ad000000000004ae023030100000002aa089b952eba92e8e00013cc58fb8f406f095800000000001eaa0d30000c0d2c746193e7800023b40002fae8ce8000bdd373228d10440002d000003d90013000000031a800029e459580000390000a1cb06420b8ed6e13aa1eeb1a0dc6790d2a0000000000064e6a9800000000a800000000001d6600000000001eb6e4235182650000d03b31a00022380002e5e9451cb63a18000ec580000000000000000000033761d4996a00000000002b7038fb1348c01d54000312a9b5a4b0d1cb5a4000000036006f2ddb8000a553372674000000000003f339d477b9f183a99720000000000000006bd367269dac9a00036260be99ac98cb9648fc2a783ce8e14873b48e0000b985980000000000094280006f2b1f85b08000a0514f810ea9ec6198cf80000000685123a76b00000002a5c39526823b18bc8e793dd28898c909290274ebd904cc40398a66500000000000253256214316ba3211e0ae7c800000000003f7b79aae080004001aea197a92c2a48ba200021ec178baf4a84000000008ec59880004391c4800000000003f8200000000002ebe7b82b5a865976cbe12e22bf12644f8fab66bffb1b2b7a800007033f6fa41cc400003f80000ba0000000000000000000000000311400009ea833800000032240001096f5e0f12000000000000000000000851321c276915427b95dae5580000000000000000059a3a721000000fb580009138000fc7000000030aed840000000000082da2da0002f886a380000003ee698e8000a8b224a000000000018fe5d90612fde11f20000000000000000029ba7f592c8b218ea2c6201f600000001710000eec8000fc900000001400e611b4ada3b2b200000006adb782000194c0001878a51210e00025281be8a2234716ae35c25cef6780000001a845092ec60538000ae78606af6aaf071a000000000009ab368aa4404fc57b800000005ca00015160000fb2c578000000017075c3f408880dbe44f2baecab1494975872a8d580000003272000304af4f0d5ae03ae0cdf6a0e60d61fa878f00005019e9a0003dcc74a130aedf00000002f24a538a0e49580001a89b2e000136c00000003cb8ea87271d90000386abd3000057db69400012e034490b0bcd9474000000046438fc792a2cc00011dc6228ce245729be4c40a080002f98e2632feafb00009de800043a8000000336cdd03c2c00781d084188badaf15aa85d800000000000000000809abce5841c3436385983af80001778006f9a000009d8000645385841904767ec848ab4d0d5eb69190e9e2b5ea000000000000001f837b8d72800000038bc647316e6301318d3a80000000000000157c7b900009bd0000000276c00000000003444e84000000030c20
  | 70 => 0x7e11b7e079b97e000357ed582fe4c020b9424c1bd632e1606ac318ae0003da83f8be4861e9bbc0003b0000035f2a7a1a44fb61d12d5c92169dc074015522ce7670592d9ea4f2c3d8000ac29e6213da654f15beea0001a98a8923d0898a296327b0525f70000000000000024d06628000000013a7efb1e46b1031800000004143c1e834bd5e00028de3ea8000e848000e7f370875b9a54d6d07e6c1102e6f5fb37a00001a805880007f40000000204c6ee25fe0000f20378000000030b0000002c31130380272a320000000bc72c6e0002104c7830563c58a360000df447a01904339c846143e16b710278e9d9ca00d3ae984e2a526b2802de0bb33e400022f8e21299421a82a60000000803a4400000a3aa7f80000001b16a948f08e06a1ca97633da6882ce6955000093f381ed470af22f712700000eb2e4f272a0000000000290e8bfab783b60000000000000038cc00026e6d2214f66f606342dd000000000000ee8e76ecfbefafc19636aaeb2f8ce51188b183c94278393ead8a4b600a2e089a8a13629e1e7a00028664833f1aed680005b9129e0000000000000000000000003b70222065497114649f73400b0386de535bf7a00017ce00004ce486a95af8308d800017ec4b3824ab03234e30fa86200000549b219764080000e7700000000a5e0002bd06d60904242a3522d637ba000137c3e8a83c00034707600f10a1580009442a0cc360582baf28f8cef1b920001d8e4592b1cea3bb8e3490bec0002ea80000000b728f7a5920000ce11c9ac789ef200007f400025d02a3b3ca95bbe400df858e2ab80000003b4c7689da8d8382dc0f18192acfb43076495fca3e8b48d4884a0424b6e415a057ab332cfad7f92a684f1c0256789e6cf006a47bbb7221e734ee1053ac00000c70ee7afec5f780001bb8e029e7ae80b770000000000097e883071aa85e0000000000361e93b384a94e0ab81ed17eef6e32844e900006ca06e4f503cba399072210b226005d056029b000000033f00000da40002b72b5ea9a000022b034b8ea0858387617991f4844800000000000000fc4f8e9532eab1a8cb55a50c51e8000ab400000000f662b0bdf6f99a59e3fc0000000330a7a02e7a19aa66a7a32c8cc98a9084ac83224100c526180216c8a294a71d80006f12ae455d800005ea6becce96249c71fa2ca694e0cfaadd682a113088d0c36ef515acd2a9d0200000000000000ccd00000002e484eea882f2909de9780af0dbe0576da91f5a058323a0003098c22b370e50b662e561320000231e3cc92feaaab3fc000329400038a40001078000155e573bea8b0c26e2ad4a3ce6092a4421f16f03001a94d578d68e3e1cf61f500000000ce846d91b4fcb8658f4a9198000000000000000003cfa000000000000000000000fbe3ee800031aa00031d6a3700000000
  | 71 => 0x93800753a508a78000000000034b00005c200000003a9c00039da7738000000067cb2fb86ebc6163c0002d0cbb080004308b6600013922d1152696e893c0000b2eab4ba64a451e60a021de20e8b8800dd923eb4f8000203074a524078c3ed35740178000c36b7420000000e38186800000000002c1eba8800000019de000000058680000003d76391000000000000000000000000000015560ad800067c80009ee800064880006f180001528b9000000004c1056ca6c80002d523580958aee07114460001b1c0002604f451c1aed70000e5b8000100bdbc5f137e84d20706e6d820e0001cceef90f72c1b0cde8a9b49c9e405b66703828e16a1be0000000ca60000737a38ce061124c6f268a0eb0000da616ce947231abdea8d600000003b289be58200000001388000000000000000000000bf082002f28000000149a140bdd66da0dfe0000000730249a00000000000000dec80000000c1e000000000024486e68000000000000020e8000000000000003d706366fe09ac49501e800000006fd12120000000135000000000000000000c230000fc41c704d32d444921e240bfb1900000264b0f00006931a72f7d3f806938000f95981a0003d2400016220000000b149ab8000000000000005ba000000000000002304000047a00038780000000766a678e150b80401bb305740000442b9800000ad40003896f8b0e5cf83b1243bd328cb190000dcf291ca5b1876a70966eb05893eb9803e651f8ee4cc504e2000000067380005541f86de880000002502265868c2a821bc00000000000e0e0000d14000095c0061e8613b0000fbb00000000000bcfa930ea0000013f8000cfd00000000510c9f0a8200027cc000070ccad9ccc0000000cfe80000000000000000082e1dd01838000a8bb3ac1fcb356dcb80009e91f9c00000000000000000191ab7480006150538df13de6f1daf906afa7fc70580005c980004b6800000028cc1eb87cc6c6b278000000000013ec7288756fa025da331b44eb6780f0735b3fe562aa220313decb571230fac8000ce1acb682b34f0300a41e5851ae0b11968eee32a120000000c67000082680004b9b180f1e8000b0faf38000000000000000000000000128205faf569e8800051e16aa00010d8022312c09a00000001812680000000023b6db3a7440001b86ccbb16211c1b8e98b075a7e4a03ab4e0000adf07d063c160ce8b00000000324e3380000002e3e7a2859a7240000f71800046080007802596bc68ee80000e3c8493c00a9281ae1dc2b860002504e748000be59f1441700009bcb2c00000f2cec1151e0e799c8d7209ae00000002b300007b980001aa80001a180000003870d05000000009ccd9580001db1828b209438c3e800000000005ff1c3c00000004c69d740002534fa9a63cca5889e00003e80000bb8
  | 72 => 0x15f98925068000226ada02103768c278000d5480000003a0c504a12600034cc050a58e528800000000000000000ba514fe08e000000016bc68a820800000000001e06000065af7c0b9c000000000005a80e12d2c7eb34481f10862a508d8c7721142906909e35f96640003eb0a81000052f00005663e3452b09c60003054c47000088926d831216a2f17b246c34a6865d6135430323365798000000000000000002b3836cfd52f0000038b88b597820003b2800002d40ba80001ae000042c8000000255829f979c00018d838e00005ce2f8eabdaf524de94eec3998a4d1a935c3a619e874bb9e62e3b6b6a33b60817ea3387999582334000008a14c20bc00000000000000000000006a0c9a00000001daa52200009e5a87600000000000000000000000000000001e58a6a8e1e8f90000c1400001f3963a45bbce083b122813c3a6e45f1d5cca71e0c25486745c5000033e8b2c00026968a318fc812b406f0633c6d413a34b82b9ce00034b4d143ae411400009279b10c569ffa00023ba8e3890c0003340868800000000000001300060000000000000001c7a7290000008000000000000000000000301239c023a056884474f3466b84377605910a04ef800010480000003c0e000000000031e600000008e1
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8ec8758942040018deeab1284080031b1d562508100065cb26e0a102000cd963dc142040019d2c5b82840800a1fa15761081021e5c202ec210200087f865d4420401187cc8ba884080031798d751081007637312ea2102040d38405d442040010ff0eb2884080021f61d65108100061f3aac82102000c3d75590420408757100b208408003179d563108100062ebaac62102043e984058c42040018dceab1084080031b5d5621081001c5ec22eda0820038f8805db410408197680bb6820800f361c163d04100143e42eeca0820038bc84dd9410405b0fb0dbaa82081770f99375504100062f31eeaa08200087e87595410400d0f90eb2a820800f1e1c165504100061fbaac8a082000c3c7559141040018beeab1a8208003171d5635041001e6c382c6a082000c6f7598941040018d8eb312820800f3a1c2625041000637baac4a082000c6c7558941040079d0e0b1282080031e99770504100063cb2ee0a082041cba64dc14104001972c9b8282080033698f70504100066cb1ee0a082000cea62dc141040019d2c5b82820800a1fa1576c841001c76c12ed908202887f865d721040018bcc6bae420803b1b98975c84100343fc3acb908200087d87597210400187ceb32642080030f5d664c84100061f3aac99082000c3d7559321040018bceab1e4208003175d563c8410006373aac59082000c6d7558b21040031b907bb2420800e3b20b76484100062e39aca9082000c9c739912104001938e6b224208013a9085644841012c6ec36e69082000c5e65dcd21040018bacbb9a42080032799373484100064eb26e690820008de8758d210400b1b90eb1a4208013b1085634841000667b9cc49082000ccc73989210400199ee6b124208003331cd62484100257240ac49082003abb8759340040079770eb2680081038e9d564d00102071cbaac9a002000e5a7558f4004001cb2eab1e800800f369d163d001001f4d3a2c7a002000e9b4158f40040831f70cb8e80080033658d71d001024cddc3a83a002041abb865074004001d32c6a0e80080031ee1776440100063c42eec8802000cbb84dd9100400197109bb220080031eddb75440100063dbb0ea88020489ba87dd11004001976edba220080032edd874440100069dba8e88802000d38751d110040913770c3a220081226e61874440102469d328e88802048d39651d11004091976c63a220081236698c74440100065cb18e88802048d99631d11004091b54c43a220081236a58874440102765d308e88802048db2611d11004001cb6eab1a2008003961d563440100074dba2c68802000cda7458d10040019b0e8b1a2008003a61d163440100064c3a2c68802097ed38158d1004009da102b1a200800f36dc5634401001f69b8ac68802004ed22158d100407f7a10690a2008003b458d2144010
  | 1 => 0x100ba2c608267a61017458c1001d6d406a8b182000ad980d516304001c3ea92a2c60811ba61025458c100056dc02a8b182003ad880551630408bd3080aa2c608262b5e057258c100256a40ae4b182000a5e851c963040014bb0a392c608002a7a107258c100054ec20e4b182004ad6811c9630400b5ab02392c60800eb6a007258c1002d6cc00e4b182004e5651d45630400117f08bacc4080222f211759881001c76412eb310200087f855d262040050f90aba4c40800e3b209749881001c76412e73102000aaf845d6620400155908bacc4080029be1574988100053642ae93102000e2f54952620400155d0929cc408002ab612539881000727a9ca73102003aea8094e62040015d30129cc4080029ba16439881000536c2c873102003aea8090e62040015d30121cc4080123d205735881001c7743ea4b1020038ee87cc962040071d90e992c4080029ba14325881000536c2864b102000aae840c9620400155b08192c408012b9a04325881001d7540064b102000aaf845d5620400155908baac40800eba201755881000537c2ae8b102000a6c855d162040075d100ba2c4080029ba14745881000536c28e8b102003aea80d5162040015d301aa2c4080038bd52545881000573c0ae6b102004ae4815cd62040014dd0a39ac4080029b614735881000557420e6b102000aad841cd62040095cd0239ac408002b9604735881001d75400e6b102000ae9801cd620400155d0929ac408002ab612535881000727a9ca6b102003aea8094d62040015d30129ac4080029ba16435881000536c2c86b102003aea8090d62040015d30121ac40801399947515881001c3fc3acb290200387c85dd9520400117f08bb2a4080222f211765481001c7c402eca90200387c87595520400117b0dba2a4080e30f99774548100061eb2ee8a902000c9e63dd1520400117b0c3a2a4080d30f99474548100061eb28e8a902000c9e631d1520400117d0f322a4080222f21e64548100045f43ac8a9020008bc87591520400193ee8b1aa408003271d1635481001e6c382c6a902000caf749895204001958e9312a40800e3b21d625481000657ba2c4a902000cac7458952040018f2cbb82a4080033658f705481000674b16e0a9020038ef8758b42040078f4e0b2c840800e2fe1d64908102255c402c92102003cba7059242040079b4e0b1c8408113a610163908100063cb2ae12102000cb9645c242040019b2c6b84840803b3a98970908100143e42eeca10200087f855d942040050f90abb2840800e3e20176508100043ec36eaa102060c3e64dd542040018bcc7baa84080021fa1d65508100043e43acaa1020038bc87591420400187eeab2284080030f1d564508100062fbaac6a102000c5c7558d42040079b0e0b1a84080031bdd66250810006363acc4a102003
  | 2 => 0xd764811000c6e41aec902200287c851d920440010fd0dbaa40881375c04375481100043f43eca902200087c87d95204400117d0dba240880030fd9774481100061e32ee890220008be861d1204400187eca3a240880030f19474481100045f43ec890220008bc87d91204400187eebb2240880030f1d764481100045f438c890220088bc87191204400187eea32240880030f1d4644811001c7b436e2902204bc7a76d9710440058f4ec32e20881272e9db64c41100465d3b0c98822000e3b651931044001c70ca326208813b2edcc64c41100065cb98c9882200387e8794d650400147d0929aca080028f61253594100062fb9ca6b282003a7a8094d65040070f90ea9aca080030fdd2745941001d3c402e8b282000a3e849cd650400147b0939aca0800317dce735941001d3d404e6b282000a79809cd65040010fd0f21aca080021f61e435941001d3d40486b282000a798090d650400147f08b92ca080028f211725941001d3c402e4b28200087e870c965040010fb0e192ca080028fa1032594100051ec2064b282004a76810c965040014eb02192ca0800e9ea0032594100053cc0064b2820088be8794e640400117b0f29cc80800387d4e539901001d5d404a73202000ab98094e640401117d0e194c8080022f61c32990100051f428653202000a3d850ca640400956d02194c808002ad604329901001d5d400653202000ab9800ca640400717d0faa2c8080030fdd7545901001c7c402e6b20209bcb870d0d640400717d0f21ac8080028fa1643590100051ec2c86b202003aba8090d64040071790ea1ac8082672e1c143590102365c386eab202000c3f759d56404007575013aac808002ae602755901001d5c402eab202045cb8705d56404137970e1b9ac8080028fa1673590100051ec2ce6b202003aba809cd64040015730139ac808002aee01735901001d5c402e6b202099cb8705cd640400117d0f29ac8080022f61e53590100070fa9ca6b202003aba8094d64040015730129ac80800eaea0272590102265c384e4b202000a3f855c964040014790ab92c80800eae20172590100051f428e4b202000a3d851c96404087970e0392c8080022fa1c32590100045ec3864b202000a3e850c9640400147b0a192c808012ada0432590100055ac0864b202003aba800c9640400157300192c8080138d94751590100061faa2ed2a0200387f87596540400147f08b2ca80800a8fa1564950102355c402c92a020038f8805d954040070f90eb2aa80800e2f21d645501022d5c402c8aa02000c7965dc15404001972c9b82a808002a7a137558c100054ec26eab182003ada80dd5630400b5b301baac60800317dd67558c100052f42ee8b182000a5d85dd163040075b501ba2c608016b66037458c104df4c204e8b18209aadb805d163040075b
  | 3 => 0x8312200e8ec825cc624400117f08bb4a4880222f21176949100445f426eca9220008bd84dd9524401117d093b2a4880022f61276549100045fc22eca9220088bc845d952440011bf06bb2a4880063720d76549100047dc02eca92200e87e87d95524400117d0dba2a4880030fd9774549101c61e32ee8a9220008be861d1524400187eca3a2a4880d30f19474549100045f43ec8a9220008bc87d91524400117d0e322a4880222f21c64549100043fc2aeda12200287c855db424401d17908bb684880021fe1576909100143e42aed212200287e85dd942440010fb0bbb2848800a1fa1676509100043ec2ceca12200087f855d942440050f90abb2848800237e0d765091000c6e41aeca1220008fb805d942440050f90a3b284880021fa1b75509103061e326eaa12200087e87d9542440010f90fb2a848803a2fa1f64509100061fbaec8a122000c3c75d9142440050f90b3b084880021fe1576109100143e42aec212200087c865d44244011878c8ba884880021fe1f65109100043ec3eca2122000c3e75d90424400187aebb2084880232d192711091001c7a432e22122008cb4645c442440091f10cb8084880232e191701091025e3c386caa8a2048cb87019151440018f6cbb82a2880032e19370545100465c322e1a0a204a87e86dd541440bb878c9baa828821a1fa1f655051025c3e43ecaa0a204bc7870d95414400187eebb2282880030f1d7645051024e5c386c8a0a2000c7b65dc141440018f0cbb8282881072e19370505100143e42cec20a202a87c865d44144011878c8ba882880021fe1f65105100543ec3eca20a2000c3e75d90414400187aebb20828812a1f21975c851025c3fc3ecb90a200087d87d97214400187cebb2642880030f5d764c85100061f3a8c990a2000c3d751932144091974e032642880032e19170c85100143e42ced10a202787c865d62144009ae020bac42880021fe1f65885100543ec3ecb10a2000c3f659d22144001878cb3a442880030fd9574885100061e32ae910a20008bf87d92214400117b0fb2442880030f9d764885100061ebaec910a20088bf87192214400117b0e32442880030f9d464885100061eba8c910a2000c5c73d952144001938e7b224288003271cc64485102465c380c890a2000c5f65dcd21440018b8cbb9a428800327d9373485100064e326e690a2000ccc73d892144001998e631242880031e19770485100065c326e090a2000c7765dc550440018eeca38aa08800a1f21676d01100043e432eba022008c3c645d740440010ff0fb2e80880021f61f65d01100061f3aec9a022000c3d75d934044011968c938e80880021fe1576501100143e42aeca022000cb7641c5404401d9c8c4b8e40880021fe1576481100143e42aec90220008bf845d9204401117908bb2408800237e0
  | 4 => 0x4440014790ab18c888002abe09631911000556412c63222000aba868c06444001c76cb180c8880038e19630191100071db2a603222000e38654c06444001d36c6980c888002ec20530191100445f43ca632220008bd8794c6444001c3ea7298c888122aea0253191100055cc04a63222048aba8014c644400157300298c888122aea0052191100055cc00a43222048aba80cc8644400157301990c8880222fa1c32191100045ec38643222000a3e850c8644400147b0a190c888002ada0432191100055ac08643222048aba800c8644400157300190c888122aea0351191100055cc06a232220088be87144644400117b0e288c888122aea0331191100055cc06623222000abb804c4644409157100988c8880222fa1c31191100045ec38623222000a3e850c4644400147b0a188c888002aba08311911000556c10623222048aba800c4644400157300188c8880222fa1f50191100045ec3ea032220088be87cc0644400117b0f980c8880028fa1730191100051ec2e60322209cab9838c0644409d57503180c888122aee0d30191102474dc1a60322209ce9a734c06444139d32e6980c888003a68c930191100074c19260322204eab8814c06444001d3662980c888003a64c530191100051fc2a203222000a3c85440644400187ea93b4a8880222f21176951100051ec26cb2a22002a3c85d92544400117f08bb2a8880023ee0176551100443f43ecaaa220028be87d9154440015cb02196c488002ba60032d891000e6d39a61b122000ec8324c3624400187ecb3a4c4880030f19674989100061fb2ae93122000c3c655d2624400187cebb24c4880030f5d764989100061f3a8c93122000c3d7519262440010fd0fb2ac488003171cf65589100043f438cab122000c5c73195624400187ecbba2c4880030f19774589100061fb28e8b122000c3c651d1624400117d0fb22c4880030fdd764589100061e3aec8b122000c9c73d91624400117d0e322c4880030fdd464589100061e3a8c8b122000c9c7319162440018becbb9ac4880031719773589100064fb26e6b122000c9c64dcd624400187eebba2c4880030f1d774589100061fba8e8b122000c3c751d162440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440010ff0ab9ac48800a1f21573589100045fc22e6b1220088bc845cd62440011df04b9ac4880023de0573589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100066639ee4b122000cd473dc562440018f0ebb82c4880032e1d370589104fe3c3ac60b12209ecb8748c162440039b0e7182c4880063e21d30589104ee3c3aa60b12209ccb8744c162440039b0e6982c4880023be1d62189100056641ac431220008bf845d4624401117908ba8c4880021fe1574189100143e42ae
  | 5 => 0x8003175cc73d951025d3d400e7b2a2000a79801cf65440010fd0f21eca880021f61e43d951025d3d40487b2a2000a798090f654400147d09b96ca880028f61372d95100043f43865b2a200087d870cb654400147d08196ca880028f61032d95100053b40865b2a2000a75810cb65440974f500196ca880029e60032d95100043f43863b2a200a87d870c7654400147d0818eca880028f61031d95100053741063b2a2000a6d820c765440974f50018eca880029e60031d95100051fc22e1b2a2000a3c845c365440010fd0f986ca880021f61f30d95100051f42661b2a2000a3d84cc36544097cb060986ca880030f19774595100061e328e8b2a20088be87dd1654400187eebba2ca880030fdd474595100043fc2ae6b2a20008bf845cd654401117908b9aca880023be09735951007476412e6b2a2000cb874dc165440010fb0f318ca880028fa1263195100051ec24c632a2000a798098c65440010ff0eb18ca880028fe1163195100051e422c632a2000a6f8258c65440014d904b18ca8812a9ea0063195100053c4326032a2000e5b634c065440016e102980ca880030f5d754d91100051f42c87b222000a3d8590f64440015730121ec8880062fe1d43d91100051f42cc7b222000a3d8598f644400147f0ab1ec8880028f21563d911000557c12c7b222000aac8258f6444001c70cb186c8880038e19530d91100074c31a61b222000bb0814c3644400187aea3aec8880028fa1473d91100051ec28e7b222049aba801cf64440015730039ec8880022fa1e53d91100045ec3ca7b222000e1f5394f64440935750129ec888002ae60253d91100051f42ee5b222000a3d85dcb644400147d0b396c8880028f61672d91100045f43865b2220008bd870cb644400147d0a196c8880028f61432d91100055b40865b222000ab5810cb644409357500196c888002ae60032d91100045f438a3b2220008bd87147644400117d0e18ec8880022f61c31d91100051f42863b222000a3d850c7644400155d0418ec888002ab60831d911024d5d40063b222000ab9800c7644400147f0ab86c8880028f21570d91100045f43ea1b2220008bd87d43644400117d0f986c8880022f61f30d91100051f42e61b222000a3d85cc36444093d3060986c8880230f19175991100061f3aec93222000c3d75d9264440010fd0fb2ac8880021fa1c65591100061fbaee8b222000c3c75dd164440010ff0ab9ac88800a1f21573591100045fc22e6b2220008ef825cd644401d1d904b9ac8880023ee0173591100063dbaee0b222000c7875dc1644400117f0eb20c8880028fe1564191100051e42ac83222000c3e76d94644400117b0f328c8880022fe1d65191100061f3b0ca32220008bd8798c644400147d0b318c8880028f61663191100045fc3ac63222000a3f8558c6
  | 6 => 0x43e43acaa084003c78705954108007970e0b22821000f3c1c2615042001e78382c2a084000c7a65dc141080018f2cbb82821000a1fa1576104200043fc32ea208400087f8759441080010fb0eb28821000a1fa15768842013c3fc32eb108401087f8759621080010fb0eb2c42100030f99674884200061eb2ce91084000c3e655d2210800187acaba44210003171cd65484200062f32ee69084000c5d65dcd21080018f70bbb240100031e217764802007675296ec9004000c7b76dd520080018f6ec3aa40100032eddb74480200065dbb0e89004000ceb7654920080090f90ea9acb8800a1fa1f75593100043fc2ae6b26200287c855cd64c40011df04b9ac98803a3b209735931050e1e3ae86b2620048bc8750d64c4141878eaa1ac9880031edd770593100063c3aee0b262000a3d84d9654c40054790ab24a9880021fe1576553100243e43acaaa620048bc8759154c40031bd0fb9ac58800237a1c7358b1000e6639c64b1620048ec874c962c40010ff0aba0c58800a1f2157418b100243fc3acb2962000a6f8259652c400117f08bb2a5880222f2117654b100046fc1aeca9620018dc835d952c401d0fd0fb2aa5880030fd947454b101a61e328e8a96200087f855db42c40050f90abb685880122fe1d6490b101c51e42ac9216200e8fb865c242c40010ff0abb2858800a1f2157650b100046fc1aeca1620018dc835d942c401187cc8ba885881074e1017510b101a51e42ac82162000c3d7559042c401187cc8bae81881174e10175d031024c5fc3ac9a062000c3d7559340c409d3770eb26818813a6ee1d41d03100267238ac490620088bc845da54840070ff0eb2ca9080028fe1165952100443ec2eecaa420028bd84dd954840010ff0aba4c50800a1f2157498a100143f43eeab142000c3f75dd16284001878ebba2c5080030fdd47458a100061e3a8e8b14200087f855cd62840050f90ab9ac5080022fe117358a100445e422e6b14209dc78754c16284139970e8982c508007361cd3058a100045fc22ed29420088bc845da528409b0ff0abb2a5080022fe117654a100445e422eca94200387c87595528406987cca3a2a5080030f5947454a100043fc2aed214200287c855da42840010ff0abb2850800a1f2157650a102245fc22eca1420088bc845d8428400187ec8ba885080230f1917510a100465c322e021420488bf8759341840811f70cb86830800f2e1c164506100061fb22ea20c2008c3c645d4418400147d0929eca880028f61253d95100062eb9ca7b2a2000a798094f65440030ff0ea9eca880028fa1263d95100051ec24c7b2a2000a3f8458f654400147908b1eca880029be0963d951000536412c7b2a209dc7a764c36544001cb0c6986ca88002dc20530d95100061eba0e9b2a2000a3e841cf654400147b0839eca8
  | 7 => 0xbb64dc14148083970c9b82829000a1f21676105200043fc2aec20a400287c855d841480010f90cba882900230f19175105200043fc3eca20a400087d87d94414800187cebb2082900030f5d7641052004656324e420a4008cac645c841480050f90b3b642900a21f21975c85200043fc3ecb90a401387d87d97214800187cebb2642900030f5d764c85200061f3a8c990a4000c3d751932148001c58ca32642901621f21975885200043ec3ecb10a40448be869d2214800187ecb3a442900030f196748852021c5e432e910a4000c3f655d22148001878caba442900022f61f64885200061f3aec910a4000c3d75d92214800117b0e32442900030f9d464885200061eba8c910a4000c5c73d952148001938e7b224290003271cc644852021e5c380c890a4000c5f65dcd21480018b8cbb9a429000327d9373485200064e326e690a4000cd473d8521480019a8e630a42900031e19770485200065c326e090a404dc6c76d9521480b18d8ec32a42901132b1db644852021e563b0c890a4000e2c6519121480015cd0db8a429000399d94614852000732328c290a4000ea7641852148001d48c830a4290002b9a1c614852002673438c290a4004ae78318521480015cb0630a4290003b1dcc614852000762398c290a4000dc8731c121480018deca392a09000a1f21676d01200043e432eba024008c3c645d740480010ff0fb2e80900021f61f65d01200061f3aec9a024000c3d75d934048011958c939680900021fe1576501200143e42aeca024000caf641c9404809b8f4edb2e40901379ad8b65c81200163d3b0cb9024044cba76d932048011974ec326409000e1fa1e53594200051f424a6b284000a3d8494d65080018bee729aca1000e9ea02535942001c3e43aa6b284000c3f749d1650800187ae83a2ca100028fa1273594200051ec24e6b284000c5f739cd65080074f50139aca100029e60273594200043f43c86b28400087d8790d65080074f50121aca100029e60243594200051fc22e2b284000a3c845c565080074f100b8aca100028fa1071594200051ec20e2b284000a6f824c5650801d4d90498aca100021fa1c31594200043ec3862b284000a3e840c5650800147b0818aca1003a9ba08315942000536c1062b284003a7a800c565080014f30018aca1000e2f21d435902001c3fc3acb2a04000a3f8459654080070f90eb2aa8100228f21165550201c61f32ee8a904000c3d65dd1520806987cca3a2a4100030f59474548200143e42eeca10403787d86dd542080010fd0eb2a84100421f21d65508200043fc2ae9308400287c855d261080071e90e98ac21000e1f21776544200045fc22eca8840088bc845d951080018f2cbb82a21000a1f21776504200043fc2aeca08400287c855d941080010fb0dbaa82100021fa1d65504200
  | 8 => 0x1990c890002ae60332191200445f4386432240008bd870c8644800147d0a190c8900028f61432191200055b408643224000ab5810c8644808757500190c890002ae60032191200445f438a232240008bd87144644808757501988c890002ae60331191200445f4386232240008bd870c4644800147d0a188c8900028f614311912000557410623224000aad820c4644808757500188c890002ae60031191200445f43ea032240008bd87d40644801117d0f980c8900022f61f30191200051f42e603224000a3d85cc0644813957307180c89010eaee0d301912021f4dc1a60322409ce9a734c06448139d32e6980c890003a68c930191200074c192603224000e9b314c06448001d3262980c8900028fe1520191200051e42a403224000c3f549da544801117908bb4a8900028f61365951200151e42ec92a240008bf845d954480110fd0fb2aa89000a2fa1f645512026d36c16cb2924000e2f52d92524809b8f0e1b2aa49010e2fa1b74549200061fb2ee8a924038c3c65dd1524808917d0c3a2a4900030fd9474549201a61e328e8a9240348be87d9152480891790fb22a4900e22fa1c64549200445e438c8a92405887e86dd542480c1878c9baa84902461fa1f655092026c3e43ecaa124000c3f75d914248001878ebb2284901132e1c364509200143e42cec212403487c865d44248011878c8ba884900021fe1f651092009c3ec3eca2124000c3e75d90424800187aebb208490002b960831d852000578c0063b0a4001cd8734c36148001da662986c2900030fd9674985200061e32ce930a4000c3f655d26148001878caba4c2900030f9d764985200061ebaec930a4000c3e75192614800187aea324c2900021fa1f65585200062e39ecab0a400087e8719561480018b8e632ac2900030fd9774585200061e32ee8b0a4000c3f651d16148001878ca3a2c2900022fa1f64585200061fbaec8b0a4000c3c75d916148001938e7b22c2900022fa1c64585200061fba8c8b0a4000c3c751916148001938e6322c29000317d9773585200062e32ee6b0a4000c9f64dcd6148001938c9b9ac2900023de1d61185200056a41ac230a400087f855d061480050f90aba0c2900022fe1176945200445e422ed28a4000c6f659ca5148001958c9394a2900032b19172945200445f426eca8a40008bd84dd951480010ff0abb6829000a1f21576d05200245e422eda0a400087f855da41480050f90abb482900031b196729052000657b24e520a4000c6c655ca41480050fd0bbb282900021f61776505200143f42ceca0a400087d859d941480050f90a3b282900021fa1b75505202ee1e326eaa0a400087e87d9541480010f90fb2a82901371e1c365505200061fbaec8a0a4000c3c75d914148089970e1b2282900031ed9770505200063c32ee0a0a4000c
  | 9 => 0x31d95200051ec2063b2a4000a6e820c765480014db0418eca901369ea0031d95200053cc0063b2a4000a3f845c3654800147908b86ca901371e1c170d95200043f43e61b2a400087d87cc3654800147d09986ca900028f61330d95200061e32ee8b2a4000c3c651d1654801117d0fba2ca900030fdd774595200061fba8e8b2a400087f855cd654800117f08b9aca900222f21173595200047bc0ae6b2a40048f4815cd65480010fb0f318ca900028fa1263195200051ec24c632a4000a798098c65480010ff0eb18ca900028fe1163195200051e422c632a4000a778158c65480014e902b18ca901629ea0063195200053c4326032a4000e5b634c06548001cb0c6980ca900030f5d754d91200055cc06a9b2240038ed82dcf644800147d0b21ec8900028f61643d91200055cc0487b2240018bf8750f644800147d0b31ec8900028f61663d91200051fc2ac7b224000a3c8558f644800156f02b1ec890002ad20563d91200071c32c61b224000e38654c36448001d30c6986c8900030f5d475d91202255d400ebb224000ab9801d7644800155d05b9ec890112ab60b73d91200051f428e7b224000a3d851cf64480895750039ec890002ae60073d91200045f43ca7b2240008bd8794f6448001c3ea729ec890112aea0253d91200055cc04a7b2240008be870cb644800117b0e196c8900028fa1432d91200051ec2865b224000ab6810cb644800156b02196c890112aea0032d91200055cc0065b224000a3e85dc7644800147b0bb8ec890002ae60371d91200051f42ce3b224000a3d859c7644808955b0438ec8900022fa1c51d91200045ec38a3b2240008be870c7644800117b0e18ec8900028fa1431d91200051ec2863b224000aae820c7644800155b0418ec890112aea0031d91200055cc0063b224000a3f855c364480014790ab86c8900022fa1f50d91200045ec3ea1b224044e3a50d43644800117d0f986c8900022f61f30d91200051f42e61b224000a3d85cc36448011878c8bacc8900030f9d764991200061ebaec9322400087e87d9564480010fd0e32ac8900030fdd774591200061e3aee8b22400087f855cd64480050f90ab9ac8900022fe1173591200047bc0ae6b2240048f4815cd644800117f0eb20c8900028fe1564191200051e42ac83224000c3e76d94644800117b0f328c8900022fe1d65191200061f3b0ca32240008bd8798c644800147d0b318c8900028f61663191200045fc3ac63224000a3f8558c64480014790ab18c890002ade0563191200055a40ac63224000e3b658c06448001c70cb180c8900038ed9530191200071c32a603224000e9b634c06448001d30c6980c8900222fa1e53191200045ec3ca63224000e1f5394c644808757501298c890002ae602531912021d5d400a63224000ab98014c6448087575
  | 10 => 0xa0640448bf8759340c800187aeab26819000e2fa1f54592200061fbaea8b24400387f87596548800147f08b2ca9100221f61776552200054f426eab1c4000a9d84dd563880075b501baac710052b66037558e200062fbaceab1c4000a5e85dd163880014bb0bba2c71000eb6a037458e200a56cc06e8b1c4000a5e859d163880014bb0b3a2c71000eb6a035458e200056cc06a8b1c4000e1f5495163880014bf0ab92c710002972157258e200054fc22e4b1c4000a9c845c963880015af02b92c710002b52057258e202cd6dc02e4b1c4000a5f855c563880014b90ab8ac710002b3e097158e2051566412e2b1c4000a5e851c563880014bb0a38ac710002a7a107158e200054ec20e2b1c4014ace821c5638800159b0438ac71000eb6a007158e200a56cc00e2b1c4000a9e84145638800153b0828ac71000eb6a005158e200056cc00a2b1c4000c9e63dd1528806987cca3a2a5100030f5947454a200064f318e8a944000c9f7458d5288001938e8b1aa51000f361c16354a200066cb1ee0a9440438bf8759342880018bcc7baa85100030f1d56450a200062fbaac6a144000c5c7558d42880079b0e0b1a85100033658f7050a200062f31aea2144000c5e7558c42880018baeab1885100021fe1574986200143e42ae930c400287e87dd561880010ff0ab9ac31000a1f21573586204ee3c3aa60b0c4001cda734c161880010ff0abb4831000a1f21576906200043fc2aeca0c400287c855d941880071f100bb283100031798f75506200061e3aac8a0c4003cb87059141880018beeab1a8310003171d5635062001e6c382c6a0c4000cda63dc141880019b2c7b8283100031798d75106200062f3aac620c4000c5d7558c41880079b4e0b1883100033658d70106200062f31aeb90c4000c5e7558f21880018baeab1e43100031798d75886200064f31ce910c4000c9e635d221880018bceab1c4310003175d563886200064f3a2c710c4000c9d7458e21880079b4e0b1c43100033658d70886200046ec36e690c40008dc8758d2188001d8ac690843100028fa1253d95200051ec24a7b2a4000c5d7394f65480014f30129eca900061fe1d53d95200051f424c7b2a4000a3d8498f654800147f08b1eca900028f21163d95200053bc0ac7b2a4000a748158f654813b8f4ec986ca900039618d30d95200061eba0e9b2a4000a3e841cf654800147b0839eca90003175cc73d952026d3d400e7b2a4000a79801cf65480010fd0f21eca900021f61e43d952026d3d40487b2a4000a798090f65480010fd0e196ca9004e1f61c32d95200051f42065b2a4000a3d840cb65480014ed02196ca900029d60432d952026d3d40065b2a4000a79800cb654800147d0938eca900028f61271d952026d36c10e3b2a400087e870c765480010fb0e18eca900028fa10
  | 11 => 0x100075b50038ac62005eb66007158c400454f420a2b188000a9d8414563100011bf06b8cc4200063720d71988400143f43eeab108060c3c74dd56210123878e83aac4200021fe1573588400143e42ae6b1080088bc845cd6210141878eaa1ac420002ab20943588404ee3c3aa60b108001cd8734c16210001d3286982c4201830f95176948400153642ac529080388bf845d95210011878e8b2aa4200032798f74548400449e43aa8a908008c3c76551521000193ee8b1aa420023271d16354840046563a4c4a9080038ec8758952100714790abb484200e22fe1975908401c61f32aeb2108038a3c8558a421000127b0b38c842000237e0d729844000c6e41ae5308800287e87dd561100bb878e9baac22012f1e1c375584404361e3a0eab08804ac78701d561100010ff0ab9ac22000a1f21573584400445e422e6b0880008ef825cd611001d1d904b9ac2202830f1d543584401c61e3ac84b088000ab68190961100011f10e982c2202771e1d5305844000e6d39a60b088000e99434c161100015e102982c2201770f95176944400153a42ac3288805de365458651100112790eaa2a2201174e1c154544400064fba2c6a888008c9c7458d51100079b0e0b1aa22000e3d21d61544400071aaa2c2a888000cd963dc1511000187f0abb482200030f21576904402765dc02ed2088049cb8805da411009397460bb482200032e4c176904400045ec36eb20880009ae82dd6411000127b0b39482200026e602729044024d5c402c32088000c5e635d7211001d8dcc4bae4220003179d563c84400062ebaac79088008c9e7458f211000193ae8b1e422000f369c163c844000636baac59088000cd9635c3211000917b08bb442200031798d75884400263b30aeb1088000c9e635d221100018bceab1c4220003175d563884400464f3a2c71088000c9d7458e21100018eaeab0c42200232d9d1618844000c6e41eec908800087f855d921100050f90abb2422000237e0d764844000c6e41aec90880008dd86dcd21100011bd0eb1a42200023721d63484400043fc2aec108800287c855d8211000117b0dba0422003a1f21d53597200143f43eeab26400087f855cd64c80050f90ab9ac99000e3b209735932050e1e3ae86b26400e8bc8750d64c8141878eaa1ac99003aab20943593200051ec26cb2a64002a3c8559254c80010ff0abb2a99003a1f21d65553200745e43ac8aa640a3c3f651d152c8147878ca3a2a5900032ee0174987200065c402e930e400e8f4874c561c80090fd0fb2aa3900021fe1576d07200143e42aeda0e40048bc845db41c801d95ce4b2483900021fe1576507200143e42aeca0e40048be87d9141c800956d03b2283901132e1c364507200461f322ea20e40008bf8759041c800187aeab208390003331cf76487200461f322eb
  | 12 => 0xd30f2197510a400469d302ea21480008df835ca61900031b906b94c32000b0f1d654586400143f42ee4b0c800087d85dc9619000147b0a212c3200029de0565946400061ebb4a928c800387c85dd951900cd878e8b2aa3200030f59774546400449e43aa8a8c8002a3f8655151900831f70cb8483200026ba0b75906400049ec2ce520c804eabb865c241900010fb0dbaa83200021f21d655064001e3c382caa0c8003cf07098541900018f4cbb8283200031e59770506400049fc32ea20c800093d865d44190011a74c0ba883200030f5d561106400143f42aed90c800087f865d721900010ff0eb2e43200021f61d65c86400143f42aed10c800087f865d621900010ff0eb2c43200021f61d65886403361f3a2cb10c8000c3e655d2219000187acaba4432000237e0d764864000c6e41aec90c8000c5c73595219000187ccbba243200031799773486400062eb2ee690c8000ccc739892190001998e6b124320012b9205624864001e3d382ca10c8000c79655c0219001137108b8043200061fe1d53d954000477c12e6b2a800e8ec825cd65500011ef02b9acaa00123d20573595400043fc2ae3b12800287c855c762500011df0eb10c4a00030fe1175189400061e422ea3128000c3e405d4625000187880ba8c4a00029b60b65949400445e420eca92800e87c8759552500cd878e8b2aa4a00021fe1572d85400143e42ae5b0a80008f787584615000987e82ba8c2a00130f50575185400061f202ea30a8000c3c405d4615000187ecaba4a2a00121f21d65545400061f42ceda0a8000c3d859db415000117f0eb2e82a00028f61462d05400067830ee0a0a8046cb870d9541500091790eb2a82a01172e1c165505400051ec28c4a0a8043cb8701894150081d66c030a82a000e6ea1f705054024e5dbb0e0a0a8000d3b751c14150001a70ea38282a00122f212768854001cdc402e910a80018de839d921500011bb073b242a000a1fa1476485400043ec28ec90a800087f855d821500050f90abb042a00030fd977454140004dcc00e4aa08008a9e84dd5631002f53b09baac62000eb6a037558c400bd6cc06eab188000c5f759d5631001153d093aac62018aa76127558c400052fc2ae4b188000a5c855c963100bf53f08b92c620022a72117258c400052f428e4b188000a5d851c9631001153d08392c62005ea76107258c400056b408e4b188000ad5811c963100075b500392c62005eb66007258c400454f420a4b188000a9d8414963100075b500292c620002b66005258c400052fc2ae2b188000a5c855c563100b953f08b8ac620022a72117158c4000567c12e2b188000acc825c5631009f5b700b8ac62000eb62017158c400052f428e2b188000a5d851c5631001153d0838ac62005ea76107158c4000567410e2b188000acd821c563
  | 13 => 0x51ec2462b2e800087e870c565d00010fb0e18acba00228fa1031597400051ec2062b2e8000a6e820c565d00014db0418acba01169ea0031597400053cc0062b2e8008a3e84dc165d008b47b09b82cba00021fa1f30597400043ec3e60b2e8008a3e84cc165d000147b09982cba00028fe1130597400451e42260b2e8045e38404c165d00050fd0bb8ac5a00021f6177158b4000e6c39a60b1680038bc845d952d0011878e8b2aa5a00e30f9977454b400061eb2ee8a96800287e85dc961d00010fb0bb92c3a00023ea1e305874000e6d39a60b0e8008c3e7459651d000187acaba4a3a00221f217765474022e3c382caa8e8000c7965dc151d000187eedbaa83a00030fdd8755074022e5c382caa0e8000a3e8759541d00014790eb2a83a00230fdc565507400471bb8acaa0e8045c3e7059541d008b878e0b2a83a01170e1c165507400255b40cc4a0e8044cb87098941d0001976edb8283a00038e59770507400069dba8e0a0e8000d38751c141d0001c72ca38283a0002e660c70507400143f42aed90e800087f865d721d00010ff0eb2e43a00021f61d65c87400143f42aed10e800087f865d621d00010ff0eb2c43a00021f61d65887400461f3a2cb10e8000c3e655d221d000187acaba443a000237e0d764874000c6e41aec90e8000c5c7359521d00018bccbb9a43a00031759773487400063d32ee090e8008c3e7459421d000187acaba043a00230f1d1655434022c5ec36e8a868000c3d65dd150d00070fd0f29acb200028f61253596400062fb9ca6b2c8003a7a8094d65900070f90ea9acb2019b0f9d374596403351f424e6b2c8000a3d849cd65900018bee739acb2000e9ea0273596400053cc04e6b2c800087e8790d65900010fb0f21acb2000e9ea0243596400053cc0486b2c8000a3f845c965900010fd0e192cb200021f61c32596403351f42064b2c8000a3d840c965900014ed02192cb200029d604325964001d3d40064b2c8000a79800c965900018eee338acb200028fe1171596403351f420e2b2c8000a3d841c565900010fd0e18acb200021f61c31596403351f42062b2c8000a3d840c565900014dd0418acb200029b608315964001d3d40062b2c8000a79800c5659007187ccb394a9200031e59770552400045ec30e2aa48096d3b75dc1549000155904a1ac520002ab6103258a4000572c0864b148003aea800c962900050fd0bb8ac5200021f6177158a400061ebb4a92948066c3c74595529007187ccbba2a5200030f5977454a400449e43aa8a948002a3f86551529000187eecaa2a52000f1e9c16590a400063cb2ae12148038c3e655d6429000117b0d38c85200024f6167190a400043ec36eaa14800087c87595429006917f0cba885200024fe197510a401a61fc32ea214803483f865d4429000127b0cba88520
  | 14 => 0xf8758a52940010fb0d38ca5280024f6127194a5026cbdc32e1294a000c7b865c25294001a7708b84a5280034e2117094a50004bcc06eb214a003cba7059242940052f10ab8485280025e6037550a500061ebaac8214a0008df835ca61940031b906b94c32821a1f21d545865000477c12e6b0ca00e8ec825cd619401117d09b92c3280022f61372586500043f43ca4b0ca00087f865d251940bb87cc8ba4a3280021f61a72946500043fc3ac528ca000c6e7258a51940950ff0eb0ca3280025ba0b759065001c7c402eca0ca05dc3e64dd5419400187eeab22832800f2e1c164506500149e43aa8a0ca008a3f86551419408ba70e0aa283280031b5d562c8650004bdc02eb10ca0008df835d921940031b906bb243280031bdd56248650004bcc06ea10ca002978855c0219400317f0ea1ec8a80028fe1543d915000e4f39a87b22a0008bf8759064540cd47b0fb24a8a80030f61f64951502c43e432e52a2a04a87c865c654540011df0eb10c4a80021f61e54189503361f430e8a92a066c3d861d1525400187ec63a2a4a80030f58c745495051e1e310e8a92a096c3f601d15254069a76c03a2a4a80021fa1f64549503361e3a6c8a92a04a87e86dc55254001a70e9b82a4a800e1f61676d09500061ebaec9212a00e8f8865c242540050f90a3b284a803a1f21676109503349e422ea212a008c3c645d4425400187aebb2084a80022fe1172d85500445e422e5b0aa0008f7875846154001878a8ba0c2a80030fe1574185500061e42ae830aa000c3f525d0615400987ea2ba0c2a80130f54574185500065dc02e830aa000cb8805d0615400187ca0ba0c2a80030f14174185500043ec3ca830aa000c3d7495061540010ff0ea90c2a80028f21152185500061eba2a430aa00087e87d9151540cd878e9b22a2a81621fa1b72545500043f438c4a8aa00387d859db415400917d093b682a819b0f95276d05500061ebaec920aa00287c851d94154001878ed2a282a811b4e1c254505500147d436e0a0aa00487c859d84154011878c8ba882a80030f5d764105500743e42ced90aa00487c859da21540031bd073b242a80023760e764855001c3e432ea90aa06693c845d521540072f100baa42a80022fe1176085500445e422ec10aa0048f8865c021540110fd0f29acba00228fa1253597400062fb9ca6b2e8000a798094d65d00030f90ea9acba00228fa1273597400051ec24e6b2e8000c5f739cd65d008b4f50139acba00029e60273597400451e422e4b2e800087e870c965d00010fb0e192cba00228fa1032597400051ec2064b2e8000a76810c965d00014eb02192cba01169ea0032597400053cc0064b2e8008a3e849c565d00014dd0538acba00029b60a71597400053dc02e2b2e8008a3e841c565d003d47b0838acba00228fa12315974000
  | 15 => 0xa3a2a4908d30f19474549210064e318e8a924200c9f74d8d5248401938e9b1aa49080a1fa1676909210043ec2ced2124238a3c85592424848957100b2484908031718f75509210061e3aec8a124200c5f75d8d42484018b8ebb1a84908031718d75109210045fc3ac82124234a3c85590424848757100b208490803179d763109210062ebaec621242a4b2c85508424851fd18c6a10849083a1fe1d65945212ed1e422cb28a424ba78805965148401caea3b1ca2908031bd9772545210143f42ced20a420087d859da41484010ff0abb2829080a1f21576505210046fc1aeca0a42018dc835d941484018b8c7baa82908030f1d764505210062fbaec6a0a4200c5c75d8d4148401998c7b9282908033318c72505210066db1ee0a0a4200cd863dc14148401976c838282909032e19070505210066db18e0a0a4200cd8631c141484018b8c6ba88290803179d763105210062ebaec620a4200c5c635d721484018bcebb1e4290803175d763c85210062e31aeb10a4200c9c639d22148401938c6ba442908136908574885210062f3aec710a4200c5d75d8e214840193ce9b1c4290803275d363885210043fc2ae9b02420287c855d3604840157509a86c09080637a1b735812112c6e436e6b0242008de87d8d60484018beebb1ac090803171d763581210064fba6c6b024200c9c74d8d60484011bd0e31ac09080317dd463581210062e3a8c6b024200c9f7418d6048401938e831ac090803179d763181210062ebaec63024200c5e7518c60484018baea318c0908023ee1d60181210053c42ac03024200ab884580604840117f08b86ca108222f21170d94210243e43aa6b28420087f855c364084050f90ab86c81080a1fa1f75590210043fc2ae6b20420287c855cd640841d1d904b9ac810a870f1d743590210245e43a86b2042a0c3c7550d640841d55904a1ac8108028f61365950210151e42ac92a0420087f855d954084090f90eb2aa8108122f21d645502151e1fb28e8a9042a3c3c651d152084010ff0abb6841080a1f21576d08210043fc2aeda08420287c855db410849d976c8382821093b2e19070504210143f42eec908420087d85dd92108401998e7bb242108031ba17764842100636c2eec9084200ccf76dcd21084017c100a0a4210803351cf76484210063b42eec9084200c7585dd921084019aeedb9a42108030fdd774580210061e3aee8b004200c3f751d16008401878ea3a2c0108021fe1573580210143e42ae6b0042008bf845cd600841117908b9ac010813b804121580214fe3c3ac60b00429ecb8748c160084091f10e982c010a771e1d530580214e65c3a260b004204af0814c160084071790ea1ac9280021f61872552500043ec30e2aa4a09187c8755162940010ff0cba4a5281621fe1d6294a500ad37c3ac5294a058c6
  | 16 => 0x4595210064fba0c6b2a4200c9c7418d65484019b0c7b82ca908031e19470595210066c318e0b2a42088be87dd1654840187eea3a2ca9080637a1f73595210064fba6e6b2a4200c9c74dcd654840117f08b9aca908222f21173595210047dc02e6b2a42038f8805cd65484011bd0e39aca9080327dd073595210064e3a0e6b2a420187c8754d654854d878e8a9aca90807171cd535952152e3c382a6b2a4200cbb74dc16548401970e9b82ca9080336dcf70595210066c39ee0b2a4200c7b751c16548401976e8382ca908032e1d070595210066db98e0b2a4200cd8731c1654840187aebaa6c8908021fe1570d91210143e42ae1b224200c5f7518d64484018b8ea31ac8908033618f70591210066c318e0b224200c3c75dd164484018beebb9ac890803171d773591210043fc2ae6b22420287c855cd64484011df04b9ac8908023ee01735912101c7c402e6b224200c5f751cd64484018b8ea39ac890a870f1d7435912100e4e39e86b22429bcb870d0d64484031790ea1ac890a830f1d5435912100e4e39a86b224299cb87050d6448401998e7b92c8908031edd770591210063c3aee0b224200cdb73dc164484019b0e7b82c8908031edd470591210063c3a8e0b224200cbb741c164484019b6e6382c890803361cc70591210045fc3ac83224200a3c85590644840157100b20c890803179d463191210062eba8c632242008df835da54484031b906bb4a8908028f613659512100c6f41eecaa242008dd83dd9544840117f08bb2a89080237e0d765512100c6e41aecaa242008fb805d954484071f100bb2a8908221f21d65551210451e422caaa24245a788059554484091dd0db92a8908033318f725512100666318e4aa242008dd8799763484011bf0eb2ec690802a7e1165d8d210054e422cbb1a4200adb8059763484015b100b2ec6908023761e64d8d210046fc3ac9b1a4200a5f8559363484014b90ab26c690802b6e0164d8d210056c402c9b1a4200a5e8519363484014bb0a326c690896b3a1b72d8d2112d6b436e3b1a4200a9f845d7634840153908baec690802b6e0175d8d210056c402ebb1a4200c5d751d763484014bf0aba6c6908029721574d8d210056dc02e9b1a4200ad8805d363484014bd0a3a6c6908029761474d8d210070faa4a9b1a4200a5e85dcb63484014bb0bb96c690802a7a1372d8d210054ec26e5b1a4276ad681dcb63484014bd0bb8ec6908029761771d8d213b567416e3b1a4200a9e84147634840153b0828ec69080297e1570d8d210052e42ae1b1a4200a9f845c3634840153908b86c69080297a1470d8d210052ec28e1b1a4252ace821c3634840159b04386c690802a7a1350d8d210054ec26a1b1a420487f8759652484c147908b2ca49089e9be09659492126d3c402cb2924200c9c63dd1524840187ec
  | 17 => 0x2c4204e2f219966488409c5a4332cc9108222fa1e53992210045ec3ca73244200e1f5394e64884015750129cc910802ae60253992210445f4386532442008bd870ca648840147d0a194c9108028f61432992210255b408653244200ab5810ca648840157500194c910802ae60032992210445f43ea132442008bd87d42648841117d0f984c9108022f61f30992210051f42e613244200a3d85cc2648840917d0faa2c9108030fdd754592210245f43c86b244200a3e8590d648840147b0b21ac910802aea0243592210055cc0486b2442048bc8750d64884050fd0bb82c9108021f61770592210061fbaceab244200aba809d56488401573013aac9108028fa1673592210051ec2ce6b244204ab6819cd648840156b0339ac910802aea0273592210055cc04e6b244200aaf825cd648840155904b9ac9108022fa1e53592210045ec3ca6b244200e1f5394d64884015750129ac910802ae60253592210051fc2ae4b244200a3c855c9648840153f06b92c910802a720d72592210055dc02e4b244200ab8805c9648840117d0e192c9108022f61c32592210051f42864b244200a3d850c9648840956d02192c910802ad60432592210055d40064b244200ab9800c96488409c6ca3a8ac9108028fa1770592210051ec2ee0b244200a3e859c1648840147b0b382c910802a7a0c70592210054ec18e0b244200cb9701c1648840117d0fa82c9108022f61f50592210045f43e60b2442008bd87cc1648840147d0b982c9108028f61730592210061faa2ed2a4420487f87596548840147f08b2ca91080a8fa1564952210243e43acaaa442048bc875915488401c5ea4b24a5108022f61b7454a211c61f32ee8a944200c3d65dd1528840117b0c3a2a5108d30f9947454a210061eb28e8a9442388be8799152884111790f322a5108e22fa1d6454a211a45e43ac8a944200c7565dc5528841196cc8b8e85108021f61b7550a213061f326eaa14426087e8759542885230f90eb2a85108030fdd56450a210061e3aac8a144200cb564dc542884690ff0cba885108230f9917510a2113c3fc3aca2144200c3e75590428840187aeab2085108b61f61b75506212ee1f326eaa0c422787c875954188409c6882b2a83108030fdd564506210061e3aac8a0c4204ab48159141884018f4cbb8283108031e597705062120e5d326e0a0c4200cb964dc141884018f4ca38283108031e59470506212065d320e0a0c4200cb9641c141884510ff0cbae431089e1fe1d65c86210061f3acc990c4200c3d75993218840187ceab2643108030f5d564c862100636bb4eb90c4200c6d765d721884018eaed32e43108031d5d965c86210065abb4c990c4200cb57659321884050fd0bba2c1108021f61774582210247c43a60b0442008bf845c3654841117908b86ca908030f1947
  | 18 => 0x49157100a0ac0208123e21d305804107537414c732e420e87e8794d65c840147d0929acb908028f61253597210062fb9ca6b2e4200a7a8094d65c84014f30129acb9083a1f21d53597210445f426e0b2e42008bd84dc165c841dc9c6531acb908029be1932597210061fba4e8b2e420ea6c825d165c840187ae83a2cb908028fa1273597210051ec24e6b2e4200c5f739cd65c841d4dd0539acb908029b60a73597210053d404e6b2e4200a79809cd65c84010fd0f21acb908021f61e43597210053d40486b2e4200a798090d65c840147f08b8acb908028f21171597210052fc1ae2b2e4200a5c835c565c84014f700b8acb908029e201715972100537c1262b2e420ea6c824c565c84510fd0e18acb908021f61c31597210051f42062b2e4200a3d840c565c841d4dd0418acb908029b60831597210053d40062b2e4200a79800c565c840147d09b82cb908028f61370597210051f424e0b2e4200a3d849c165c84014bd07382cb908029760e705972107537414e0b2e420087e87cc165c84010fb0f982cb908028fa1330597210051ec2660b2e420ea6e828c165c84014db05182cb9083a2f21d43593210143f42ee0b26420087d85dc164c841d0ff0eb2ca9908028fe11659532102476412ecaa6420e87c8759554c841147908b2aa9908031b59772553211c61f32ee8a964200c3d65dd152c846987cca3a2a5908030f5947454b211bc3ec36eaa16422887c8759542c841dc5884b2a85908031b59772547210043ec36eaa0e425d87e8759541c850d0f90eb2a83908031e99770507210063cb2ee0a0e4200c7a651c141c84018f2ca38283909032e99070507210065cb20e0a0e422a87f865d441c84510ff0eb288390803179ce659832107637394cb3064200c5e7359660c841dcd640b2cc1908031799573983210062eb2ae7306420287e85dd160c84010fb0bba2c19083a3e21d305832100e6c39a60b064204a768198e65884090fd0f29acb108028fa1253596210051ec24a6b2c4200c5f7394d65884014f50129acb108029e60253596210243e43aa6b2c42088be84dc1658840117b09b82cb10813958c663596210061fba4e8b2c4200a3e849cd658840147b0939acb1080317dce73596210253b40ce6b2c4200a75819cd65884014f50139acb108029e60273596210043f43c86b2c420087d8790d65884014f50121acb108029e60243596210051fc22e4b2c4200a3c845c965884014bf06b92cb108029720d72596210053dc02e4b2c4200a78805c9658844f0fd0e192cb108021f61c32596210051f42064b2c4200a3d840c965884094ed02192cb108029d60432596210053d40064b2c4200a79800c9658840147d09b82cb108028f61370596210063db84e0b2c420087e87cc165884010fb0f982cb108028fa1330596210051ec2660b
  | 19 => 0x38e95052181412255cc3c843028200abb8590860504015730b210c0a0802ae60e42181412274d39c843028244e9973908605049d57503210c0a08029ee1542181410053c42a843028243abb8710860504875730e210c0a0902aee1442181412071d428843028200ab9851086050481c730a210c0a08028e61442181410055cc18843028243e9a731086050487d32e6210c0a0903aaa08421814121f55390843028243ea972108605049d57502210c0a0902aea1332181410055cc26643028200abb848c8605048157109190c0a0802aee1132181412055c4226430282038fa870c860504011f30e190c0a08029ea1432181410053cc28643028240aba840c8605040157308190c0a0802bca04321814100578c08643028240aba84d44605040157309a88c0a08038e55351181410071d2a4a23028200e7351944605040157708a88c0a0902ae21151181410071caa2a23028240aba84144605040157308288c0a08038e95051181412755dc2c823028200ab985904605040157307208c0a0927a69ce411814124f4cb9c823028200aba8290460504014f70aa08c0a08029e21541181412055d426623028200ab984cc4605049d57709188c0a0802aee1131181412055c4226230282038fa870c460504014f50a188c0a08029e61431181412055d420623028200ab9840c460504015d504188c0a0802ba60831181410243f43ca6b288208a3e8494d65104018bee729aca208029ea0253594410053cc04a6b28820487c8754d651040517b09b82ca208228fa1273594410051ec24e6b288200c5f739cd65104014f50139aca208029e60273594410451e422e4b28820087e870c965104010fb0e192ca208228fa1032594410051ec2064b288204a76810c965104014eb02192ca208029ea0032594410053cc0064b288208a3e84dc1651045547b09b82ca208228f21170594410043f43e60b28820087d87cc1651041147d09982ca208028f61330594414f71c20460b288200a3f844c1651041147908982ca20a738e10130594410043fc2ae1310820287c855c262104091d90e992c4208230f1d165548411c61f32ee8a908200c3d65dd1521040187f0bbb282208030f21776504410265b28eeca088200c3f76dd5411040187eec3aa82208028fa1d65504410051e43acaa088204c3f715954110411c6ee2b2a82208030f1c165504410065bbb2a2a0882489ba87dc14110401976edb8282208038e59770504410065dbb0e0a088200d3b751c14110401a70ea38282208038e59470504412465d430e0a088248cb9861c1411049d976ca382822093b4e99470504410065cb28e0a08824ed39651c14110401872ca382822092366a0c7050441246ccc18e0a08824ecbb631c14110401972c638282208032e9887050441276d9308e0a0882488bc87505601
  | 20 => 0x3cc2865b028241aba840cb605040157308196c0a0802bca0432d814100578c0865b028241aba8414760504015730828ec0a08023ea1c31d81410053d42863b028200a79850c760504835750818ec0a0802ae61031d81410057541063b028200ae9820c760504078f0c0bacc0a08031e9d760981410063cbaec1302825d87c86dd560504010fd0fb2ac0a08021fa1c65581410062f39eca3028200c5e7319460504018becab98c0a080317195731814101e6c302e630282008fb8758060504014f70ab00c0a08029e21560181410063d3b6ca3028200e3b84d9460504011f30f328c0a08023ee1d65181410063d3b0ca3028200e39841946050401c76caba0c0a08038e19574181410055d434a83028200e3b659506050401c70cb2a0c0a08038ed9554181410071c32aa83028200cda769cc6050401cb6cb398c0a08039619673181410066d3b2e63028200e5b655cc6050401cb0cab98c0a08023e61e63181410053d42cc63028200a798598c60504011f70eb18c0a08029ee1563181410053c42ac63028200aeb8258c60504015d104b18c0a0802aea1b43181410071db2e863028200e3865d0c6050401c76caa18c0a08038e19543181410074db1a8630282008f98798860504014f50b310c0a08029e61662181410047dc3ac43028200a7b8558860504014f10ab10c0a0802b6e0d62181410056c41ac43028200e3b659086050401c70cb210c0a0803aa18a4218141005d940c843028200aba8610860504016730a210c0a08038ed9442181410071c328843028200e3b659046050401c70cb208c0a09038e95354181412355dc3ca83028246ab987950605048dc74eb2a0c0a091b8e5d654181410055cc1ca83028246e9a73950605048dd32e72a0c0a0802aea0a54181412755d40ca83028240e3854550605048b5770eaa0c0a09038ee15541814122f1dbaaa83028245e3875550605040157706aa0c0a0917a69cd541814122f4cb9aa83028200ab882550605049d57102aa0c0a0902aea1353181410055cc26a63028200e3a54d4c60504071f50f298c0a08023e61e53181412055d424a63028200ab98494c6050401cb6a7298c0a08038e95153181412055d420a63028200ab98414c60505375770fa18c0a0a6eae61f43181412055dc2e863028200ab985d0c6050537d34e7a18c0a0a6fa65cf43181410055d41686302824eaba81d0c60504071f50f218c0a08023e61e43181410053d42c863028200a798590c60505335770ea18c0a0802aee1543181410055cc2a863028240e9b8350c6050533d34e6a18c0a0a67a65cd43181410055c41286302824eab88150c605048157509a90c0a0802ae61352181410071caa6a43028200e3a54948605040157708a90c0a0902ae21152181410071caa2a43028240aba84148605040157308290c0a08
  | 21 => 0x751c5545040117d0db82a8a09172e18370551410055641287b128200aad840cb62504015cb02196c4a08031ed9670989410063c32ce13128200c7b655c262504018f0cab84c4a08021fa1f65589410062e39ecab12820087e8719562504018b8e632ac4a080317d9773589410062e32ee6b128200c7b65dc162504018f0cbb82c4a08031ed9470589410063c328e0b1282008ef87588625040159906b10c4a08021fe1570189410143e42ae031282008fb805da52504071f100bb4a4a08030f9da549494101c7d406eca9282008f980dd952504bb878e9b2aa4a08030fd9774549411c61e32ee8a9282049b681dd152504112790eaa2a4a080a8f21954549410061e3b2a8a9282048be86dd6425040936d03bac84a08e30f19575909411c51f436cb2128200e2f65d8a4250401c58ca31484a08026da1a71909410265b434e32128204d36859c64250409a6b0b38c84a08034dd9671909410069a32ce321282008bc865c2425040127f0ab8484a09132e18170909410043f436eaa128260d3441dd542504010fd0fb2a84a09778b10b65509411a45e432ea2128234c3f865d442504698790cba884a08d20f21975109410461fb0aea2128208d37615d44250401878c0ba884a08024fe1f65109414351f436ca212820093d8719442504871790cb8084a090f2e18170109412ed3ac0ecb28a8286c3e7695251504bb878e9b2aa2a08030fd9774545410249e43aa8a8a8204a3c86551515040966902aa2a2a09778dd8765905410049ec2ce520a82088bc865c2415040127f0ab8482a09272e18170905410046fc1ae5b0282018dc835cb605040157309a86c0a08029ea1730d81410053cc2e61b028200ab984cc360504031f70e986c0a0807369cd30d81410071cc20cbb028200e386595360504014f50b31ec0a08029e61663d81410053dc2ac7b028200a788558f60504015d704b1ec0a0802ba20963d81410071c32e87b028200e386550f6050401d30c6a1ec0a08029ea1662d81410053cc2cc5b028200a7b8558b60504014f10ab16c0a0802b6e0d62d81410056c41ac5b028200e386590b605040176503216c0a0802ce61442d81410071c32885b028241aba841d76050401573083aec0a09078e95354d81410066db9ce7b028200a7a851cf60504014f30a39ec0a0906aea1073d81410055cc20e7b0282008fa8794f60504011f30f29ec0a0906aea1253d81410055cc24a7b028200e5b5394f60504011f50f21ec0a08023e61e43d81410053d42c87b028200a798590f60504014f50bb96c0a08029e61772d81410055cc26e5b028200a7a859cb60504014f30b396c0a0802b6e0d72d81410056c41ae5b028200abb8454b605048357108a96c0a08029ee1542d81410053c42a85b0282008fa870cb60504011f30e196c0a08029ea1432d8141005
  | 22 => 0xb00c0a89162f61b70553410043fc2ae1316820287c855c262d04050fd0fbaac5a09830f1d37558b4148e1e3a0eab16820087f855cd62d04050f90ab9ac5a08122f2117358b415061e3aa86b168200aac8250d62d040917908bb4a5a09830f9517694b410245e422eca968208c3c7459552d0411878ecaa2a5a08e28f2157690b411c45fc32eb2168238c3e655d642d04714790ab1485a09122fe197090b410049fc2ae121682018de83dc960d04011bb07b92c1a083b1ba1672d9641006372a4e5b2c8200c6c549cb65904098dea3396cb208131b54672d964102657a0ce5b2c8204cad419cb65904018d8a1396cb208121f21d53596410061fc22eb3148200c3c845d6629041d8d904bacc5208031b5d75298a4100637baea4b1482048ec874c962904014df04b2ca52083a1fa1f6554a412ee1e3a6caa94820ea6e82d9552904018d8eb31285208031b1d56250a410051ec2cc5a0c8200c3e40dd5609040187881baac1208021fe1573582410143e42ae6b0482498be87d05609040187eeba0ac120926aea0341582414fe3c3ac60b0482048f8874c1609053b8f0ea982c1208028f61253d95410062eb9ca7b2a8200a7a8094f65504014f30129ecaa08061fe1d53d95410445e422e1b2a8200b2e82dd365504014f50131ecaa08029e60263d954100537c12c7b2a8200a6c8258f65504014f700b1ecaa08029e20163d95415061f3b287b2a8200e1c6350f65504014dd05ba6caa08029b60b74d95412ee1e3a2e9b2a825da3e841cf655040147b0839ecaa0803175cc73d95410053d400e7b2a8200a79801cf65504010fd0f21ecaa08021f61e43d95410053d40487b2a8200a798090f655040147b09b96caa08021fa1c32d95410043ec3865b2a825da3e840cb655040147b08196caa08029da0432d95410053ac0865b2a8200a7a800cb65504014f300196caa08021fa1c31d954116c3ec3863b2a825da3e840c7655040147b0818ecaa08029ba0831d954100536c1063b2a8200a7a800c765504014f30018ecaa08028fe1170d95412ed1e422e1b2a8200a3d841c365504014bd06386caa08029760c70d95410043f43e61b2a820087d87cc365504bb47d09986caa08028f61330d95410063c32ee0b2a8200c78651c165504010ff0ab9acaa08023be09735954107476412e6b2a82008fb805cd65504071f100b9acaa08031edd770595410063dba8e0b2a8200cbb741c165504010fb0f318caa08028f61263195410053d404c632a8200a798098c65504010ff0eb18caa08029be09631954100536412c632a8200a7b8058c65504014f100b18caa0a1a8fa1063195410051e4328632a8200e1f6350c655040547d0db2ca8a08030f9db65951411c61e32ce52a282468bc865c2545048d970c0b84a8a08031dd94715514116e1e3b6caaa28286d37
  | 23 => 0x594425361e3a2e6b288400a6f825cd651081d4d904b9aca210228f21371594420451f424e2b28840ea6e829c5651081147908b8aca210029ee0171594420053c402e2b288408a3e841c5651086947b0838aca2121b0f1d071594420451f42462b288400a3d848c565108014df0498aca2103a9b20931594420043f43862b28840087d870c5651081147d0818aca210028f61031594420753741062b288400a6d820c565108014f50018aca210029e60031594420451f426e0b288434a3d84dc1651092d878e9b82ca210228fa1270594420451e422e0b288408a3c841c165108010fd0f982ca210021f61f30594420451f42660b288400a3d84cc1651081d4dd05182ca210029b60a30594424f71c20460b288400a3f844c1651081147908982ca212738e10130594420461e3a2caa908438c3e65dd1521080187acbba2a4210030fe1776508420061e42eeca10840ecae52dd9421094727d0fbaa84210030fddb75508420061fbb0eaa1084089ac87549421080195eeca9284210021fe1570984420143e42ae1308840e8f4874c5611081d5c90498ac22127b2e10373580424e65c202e6b00840e8f8874c1601081157108982c0210122f21d43592510051fc2a86b24a25da3f87592549440187f0eb24a9288021fe1972952514343fc32e32a4a230977865c6549450d8ef0cb8ca9288021f61e5498a510247643a64b14a25dc3e861d152944bb87b0c3a2a5288030fd8c7454a510061eb18e8a94a2a3c3e621d1529450d87cc23a2a5288d34d9847454a510043e43ac8a94a25dc3c745915294401a58e9312a5288034b1d16254a511343ec36e2a94a200d3774dc55294401a68e838aa5288030f5d56490a51004bac0eeaa14a25d93c845d4429441187cc8ba885288030f5d56410a5100636baac4214a200c3c54dd1609440187d0bba2c1288030f61774582510061fa96e8b04a200c3f51dd1609440187ca1ba2c1288030f14374582510043f43ca8b04a200c3f74951609440117f08b9ac1288222f21173582510043e43aa4b04a200a3c84549609440187ee8a92c128a7b2e1d230582510247c43a60b04a29ccb8744c1609440317f0ea1ec8a88022fe1d64191510055c402c8322a20087e861c954544010fd0db82a8a89171e183705515148c3fc3aa9b12a2008ef87588625440117f08b80c4a88222f21170189510043e432e9292a22687d87d8a525444d4db0fb14a4a88031b61f62949510043e432e1292a20093f845c252544090fd0dbac84a88023ee01761095101c7c402ec212a200c3d75d9042544050f90cba4a2a89770f19174945510143ec3ec528aa200c6e72d8a51544050f90cb84a2a88024fe11709455125e3c302e128aa2008df835cb60544031b906b96c0a88063ee1d30d815100e6d39a61b02a2008fb87580605440157108
  | 24 => 0x2a400c9c645ce60548079b0c0b9cc0a9003365cf60981520045f43ec8b02a4008be8719160548011f70eb00c0a90230f1d16554b420043fc2ae130e840287c855c261d08050fd0fbaac3a10021fe1573587420143e42ae6b0e84a0c3c7550d61d081d0f90ea9acb210028fe1153596421c61fba2caaa484389af8754b42908712790ab8e85210130fd0575986420261ea0aeb30c840e8f4874c5619080187c81baac1210030f10375582420043fc2ae6b04840287c855cd609093f8f0eb182c12103a3e21d30582424ee3c3aa60b048401cd8734c1609080147b0929ecaa1003175ce53d95420053d404a7b2a8400a798094f65508030ff0ea9ecaa10029ea0263d95420053cc04c7b2a84a0c3e7650f6550801c38c6a1ecaa1002cb20943d95423061e3a2e9b2a8460a3e841cf655080147b0839ecaa1003175cc73d95420053d400e7b2a8400a79801cf65508010fd0f21ecaa10021f61e43d95420053d40487b2a8400a798090f65508010fd0e196caa10de1f61c32d95423051f42065b2a8400a3d840cb65508014ed02196caa10029d60432d95420053d40065b2a8400a79800cb65508c147d0938ecaa10028f61271d95420063ab88e3b2a840087e870c765508010fb0e18ecaa11828fa1031d95420051ec2063b2a8400a6e820c765508014db0418ecaa10029ea0031d95420053cc0063b2a8400a3f845c365508c147908b86caa10031e5c070d95420043f43e61b2a840087d87cc365508c147d09986caa10028f61330d95420043fc2ae6b2a84008bf845cd65508011df04b9acaa10021f61e63195420051ec24c632a8400a7a8098c65508014f301318caa10021fe1d63195420051fc22c632a8400a6f8258c655092347d08318caa10028fa1b431954251d1f4328632a8400a3c8650c6550801c3ec6a18caa1002cb209431954200637b28e4aa28460a6d82d9652508c1878e9b2aa4a10030fd9774549421c61e32ee8a9284a3a3e86d9642508c1c5ec5b2c84a10021fa1f65585420062e39ecab0a840087e8719561508018b8e632ac2a100317d9773585420062e32ee6b0a8400c7b65dc161508018f0cbb82c2a10031ed9470585420063c328e0b0a84008f78758461508010ff0ab80c2a100a1f215701854200c7dc3a61b028400c5e73d9660508018bce632cc0a100317d9573981420062e32ae73028403cd8605ce60508019b2e7b04c0a11821f21b75581420043f43ecab02840087e8719560508011f70eb00c0a10222f211735944207476412e6b28840e87e8794d651081147d0929aca2100317dce53594420053d404a6b288400a798094d651081d0f90ea9aca2129b0f1d1535944253e1e3a6e6b288408a3e849cd651080147b0939aca2100317dce73594420053d404e6b288400a79809cd651080147f08b9aca210228f21173
  | 25 => 0x8015730121ec8a90062fe1d43d91520055d404c7b22a400ab98098f645487147d0a39ec8a90028f61473d91520055d400e7b22a400ab9801cf645480117d0e196c8a90022f61c32d91521c51f42865b22a400a3d850cb645480156d02196c8a9002ad60432d91520055d40065b22a400ab9800cb645480147b0bb8ec8a9002aea0371d91520055cc06e3b22a400a3d859c7645480196ee338ec8a90022fa1c31d91520045ec3863b22a438a3e850c7645480147b0a18ec8a9002aba0831d915200556c1063b22a400aba800c764548015730018ec8a9002a7a0e70d91520054ec1ce1b22a400a3f855c3645480147b0a386c8a90022fa1f30d91520045ec3e61b22a438a3e85cc3645480147b0b986c8a90022fe1d64191520451e42cec322a4008bd8798c645480157501318c8a9002ae60263191520045fc3ac6322a4aaaaf8258c6454801c3ec6a98c8a929a8fe1d531915253d1fc1aa6322a434e1f8354c6454801c5f04a98c8a928e8f209531915200716412a6322a400a3c8154c645480147f00a98c8a90d28fa1732191520051ec2e64322a4a3a3c858c8645480147f0a990c8a90d28f21532191520445f43864322a4008bd870c8645486947d0a190c8a90028f61432191520055b40864322a400ab5810c8645480157500190c8a9002ae60032191521a51f42e62322a400a3d85cc464548694790b188c8a90028fe1531191521a51e42a62322a400aaf824c4645480155904988c8a90222fa1c31191520045ec3862322a434a3e850c4645480147b0a188c8a9002aba08311915200556c1062322a400aba800c4645480157300188c8a90222fa1f30191520045ec3e60322a434a3e85cc0645480147b0b980c8a90d28fa1630191520051ec2c60322a400aae828c0645480155b05180c8a92a78ed4230191521a51f42a60322a4a8e3b504c0645486947d0a180c8a90028f61430191520451f436c8aa2a434d2f741c954548010fd0c38aa8a921b0f19071551520043f436e0aa2a496c3c64dc154548050f90cba4a4a91830f191749495251d1f436c9292a438e2f62d92525494787d0e324a4a91830f61c649495251e1fb98c9292a400c3d73192525494787ce4324a4a928f8b9c864949520049ec24e3292a400c3c649c652548050f90cb84a4a90024fe1170949520061e322e1292a44dc78605c2525490d0ff0eaa6c2a900a3b60b73d85520143ec3ca5b0aa400a768194b615494995ae4324c2a90022fa1f64585520064e39ec8b0aa4008be871916154801938e6322c2a900327d9373585520064e326e6b0aa400cbb64dc16154801970c9b82c2a90032ed9070585520065c320e0b0aa4008f787584615480117f08b80c2a90222f211701855200c7dc3a61b02a44dc3f659d2605480193ce7b24c0a9003279cc64981520064fb22e730
  | 26 => 0xc00000100140080040040000002003000800c05c000008801801400100180240020010000010004003000000400202000180040dc014000000400000400b0010002000000016802a000000001400200700000b400e01c000005802a000001800801e0060068064008000001001800202200a007c00000100100140040090070564000012003000c00600102a000001600b0000004002000006800c01801d002004000a00000000100000200000000000002004003800c00000b00340060010060014008001009801c00800000200200040070010048006003003000001a00600280440040080030000092015002000400002300480140080020008004002004002002000802b00100281560040028000018001000001400000000c00200020040088004000015007000000a01a000000002600100100300060050000010018000000000800800500a014c0000020070000002000005800403c000000003c00000b003000401c004011000000001e000001c006002002800000400100000cc004009000000006601300000000000130090010006009001801000400f0040018002001000800001a006009003003c0000010008002004000000402000a002801c048002007812801000c00200080220000020004002000036000c00000f007805400200800200100680030008054012000014803c02a017000007401a000000000000200300280ac02800600080301ca011003010003800000b000000a00000600880000050068018012000002001000601b00580580000000000008066004024004801a009000803001800400000100620b4000019001a00000000000060050028014002000000000800202500400000ba00000477c12e6b0ca80e8ec825cd619501117908b9ac12a11b2e1d2305825400c7c43a60b04a89ccb8744c160950014db0a196c4aa002ab61032d895400572c0865b12a8008ef87588625515755f08b10c4aa0023de1d61185540145ec26e7b02a8018fb874c360550039b4e6986c0aa0023ee1d60181540745e43a86b24a400a3f8550d649494727f0eb24a9291828fe1d64952520061fc3ac92a4a49187f865ca54948752df0cb94a9292471be1972952520043fc32e32a4a400c3c545d2619480187f0aba4c3290030f21574986520061fa92e930ca404c3f515d2619480987aa2ba4c3290030f14174986520043ec3ca930ca400c3d74952619481d1d904b9ac32903a3d21d31586520061e2a6e8b04a400c3e85dd1609480187b0bba2c1290030fd4b74582520061fa8ee8b04a400c3e50dd16094801878a1ba2c1290021fa1e54582520061fba4a8b04a4008bf845cd609481117908b9ac12927b2e1d230582520747c43a60b04a400a7b854c16094939970e8982c129007361cd30582520051ec2c87b22a400aba8090f6454
  | 27 => 0x1802407200100080280aa00000d80540000010000000002000000000c000006001015c01c00c0030004000006005000800600800080300060090000018016003005810c008003000000003000b004801800e000001000000a003004008401801400000280020300018004000005004003c01600a002007000201d00080100040230000020004010013801403000b001001c01600000a800800000000a000001c004001001000000b006001000000107580040040020028000016007002000800200000000280060020000028014007004000000a00e00a800000000a00100000020000050004002002012800001200300c001c02600c004000c01c0300008004018000001001800c01700a00180060000000010002000001804c002000002800c0480020038000000007002000409400000180100020030000010000013000801c00000000100100040040000004004000000000c00a00100a8000000001000004c006007000800c00200100000340100060038008020000002000001401900f800400800100400240140180000000032000000000400200c000000401a0450068008004009000000401c034000002c00400a0000000002002022007c0000040028040006007001001007a0000038000004001002800001605901b806400e01400c80280120480028000000011000000002000000700080000000010038006002002800400000000900040040040000000006003001000807c015000000401c00000d8000000005007000c01000901a0104000000001803001a00b002801c00600100001780000100010004002002011000801005500400180080000010008016007007000c000004002006400000a00300480100100018038016017001000c00000a000000000a031002800802600000480000500020060000014014000000400000a002004400a000008001c0140030018000022003021000c000026000003000c029000000400a000000000012e02b005002800200000000140000050020064004011005001c000014009000800600200280100000030110000002000001000000000100280040060000028000018030012002c000000004801002a00300d8000028001001801c00200d000003001802d03c800000000700880000000000010004008002002003000002c002007c03a0070000000002005000001c0120030020048000007008000000c003003006801200200100700220000050008000000001021808001e0018000040000006801000200f000800401e01c004002800e00005f800000a00c0028000000005000800000000200000640440080000024020002008012001607e001801c00e000000000407e0590010004026003000801400e01300e000c0000060078008004001008800400002f0050000006008008001401
  | 28 => 0x808f2c106e101493cead418e9d080004586cc8d250e64650a08f79882ad559d91f8ad6a38659381d3a6caa27c075c19a6bb5bcaa8584485e05731350e87144d99c2c54e0d840628c9aa47cd05603fc92e3ee2bd9ab4b2c68811a0bac46cc382a21d4d0b6d5d298aa7c718e3d3ce947104a64110887e00004b94c7800001000064e00000000007022f6c00093f61da215ae21a50001d90a3c000000324ca169b738c13589e89623e834c44ac4030001e9d6b2e1f0bf80000ecd4543b2fa912e67a16db3b4ea8000000250d62c90e0cf8781ada0000003851058000000075905c0f5264000000000062f0e28b3013907b1bb47104e400022a40005aa1c10001b3800061332f0ce0c552e280000006d43b68001c500e1000066000000000000000e8c3400000000000000000000566b1a2df14ec0003d4486814c508953131924cada52f00017e413a0000000c0400000024380001200006c4a2858dc4550002f280007580af8000ab64ff5290c6d1e49f96c99dd5bc22f200009404aa308397b5b18d20000001e54834a1e13e127845ebfb53e253464e4ec4448e1c65a7922e62bb86d2d2504aa4f930a7803540d4d31200038621e9bf64665c72a959b227726388e11f800003fa45c000b850e635918f41c63372f48fd4dcc0000110000d6000002bcafe2cd2698001660cf50001c6800023c1ca0001ba00003d180012b4000059b67800000005d94b0000b9639338e80005c962891014be748389a44c71e00000015c14b400040d18a54987c500011258c88906388b2cd66a3a2602b84f441af0c0b6b52804f9496065565e1a800023443d40005342ed00007fa3cc8001c5e4ba1352d0539a6750003444000325000034132600072080003de66b3589824018ccf2769ca000096117c15f5bb6d49000360400000000027380003ed1542cdc0008f91b933984da000494a901038d4c1cb804c021002800002a01100900000040150028004010002000000000c0050028038002005000002400800f03f804c03002a007803800c03c0080030002002000805c00000600b004c00a0180040008002004008000800000501d8010006010000000c04c0080000030006003000002c022000000001c000000004000806400000e005000e01b002000c00000a002000000e0030000018000007014000403c0050090000000004000800000400400000380420020088008010000000008003a0000018000016000004000400002300b00240020000000000014000000800000000a0048118002007007800800a002001001800000d000800000000000d0098002016000007000000000100740040010010000004000001800000807c00f8008038000011802c0660000000004050004000800000a000003801c00000e010806c0080030040084000001003802400a00300
  | 29 => 0x6e52315b0cb112418dc44061145728470ece6e918c32dc5767f14cb129d1f637e3f821c9ba47bf0c493297b45d9586af31792de63771fb17020e01e90b4593016755ea010c8e007174281d00cd844750f8c7720cc05906dcd7c6d845bb9312787c92dd800161c51f1560000c3c3a06f429180000de2b502a88c02b90ed00007ba3fa0001ef087c51611a8a5478431c1891ef8000294000386194cdf51cd1294000a900002b6495000000000007a2c0015937c0000c2c0001b34000d375d615048b4c7812ea57080895130e09513769921f7a691b309810a780014943f10441570d60c2a3bf90ad2dc3be6792fc468695e2011b6cc70b9305207542467ad0003124294e391c80d312ca0631b82984f765f61ee03d07304d56e02a157506b715694e457a09861f1e699d83bf09082b48522da111b6d10bad805fea404aeaa3b14600640006715c919b5054bb312d0c644cec5d29311fd34cbf33490a5c000c036d61bc148ea982c70e9caec8480002c797f0aec6978ac5c240000002fb10c204c2a1013c00008b467a90c5220002c22c5d846d883d82340f1c9ad5fd1268c1a7e200000018106ca00027b18900ec0001144fa291b267a3e1742a802e4161d1e6a7d386a26574087116cb93c0000014eaa0140006c83ad0460a7a00024f9f216dc04872013d4c9e9a224206b4bf4d9b50fa564538d5621925ccfb00003bf08cd100be92b02b20c5a6fe000238c17461b012036cf86b66592b92422aaac4db1e0d0f0acb52bb6e577e4c9036284d9be51835a8b486ac8f15f41f484f42ea0002bc025aaf154523a400036a35525b52747e342a86e53c0d6130a072dac679e218b078b8299736d18ada060000002641b5c00000000009b60000d537aca6ecc40f39ed1bacb6414b04c4004ab6317070c17e8025553424a70cdb3f4019516420200000003269c5449a7e9c6611f08cb4796ac28e6952b88c8cce304c800081a6cb11d91f02de00068da58d6e64e9368a7d0000bf2164b5fdb867172d191e8300226000000000000000000003e800037d885400058937302dc00000024100009e01bc4bab7d1a686c132699fd85e1fe4933491a9687540923007cc5d65a61f8597a7e93bd98c12d20d31d70511bfc5971210c29a5820a184a7d80008ec3ff1434c9c9f55a721f40968eb4c4032c00000000000009a2000000112ca640000001678d706b400026651ae78522b0a840000006e88939a522095800248b9e72c4feb26d54c2ef2182298a803df68684e15600ab19515457522534b40830c6c7b666521146faa413ea0200000d3b0002c3d4b858d0002a1059c26f6c700000009a50000000f4208d0003859ad20006ed044800052b46e80000000006d89868000a7e2ee3149398d380799fe40000002db32b52700002c9a5811967af39a18ccc7c3cb52593
  | 30 => 0x101e5bd4d036440003076f785308fa2b62668000c3aa8372680015e849b0a3b870fb49d002b978c72c78f533a0dd4522a908d12e0c22e05592000094cba61f51c6d0ee5a141db5dc00001b4e8a3598ec88c138ac80ffa339504ae0caf89251ec240cb32cde0000001a2a9ea211afbd84093d2c81ee5a3a7703b89c9568084a62b99792482c650b8cb8c1cb5a0a300019d6dc945c3084dfa00059b0a18f6e82429f37f0cae13559fa911b8e3382d5a9e13e41040000000ef800000025e0662b39000000199a00043f00009cc68f33ea94491e5fc50c8a90a086045bd1cddb0ac026c6a3a09186cf0801abcd4e6773ec927058047b0002204aa42043100000000d23484000000000000001f800068e1a500000000003ac8000000374473ac087d80006d43520000000000326902681434fb21000000002e303024a46d58e17c0aa0d5c42e06d1664b7b6fd2e30d5684b00000008126fa052800032276c134000000000001c8000000776000000034c0000000978cec40f44680b09323bd1edaa7546adc54bd800000000004f04a14ca40654b0001a0c000414058c000000210257da085015af29e87546a944202697fed4d3258afda287c027e27484647ab6629801282b626f283394d241e31d13c588e9eb6ca1a08f02cf16cb800091a2d7351a5ac9843174f688380009ee1361e29778da410419997c0d702da2ba8000db24e21ef58e800000035c83f2d426bc2aa0264a303e79c050cc15439928395be0e701131a1684c0759607149968160c3a914acce375a8afd0aae5c46351305c1498c46a07ad38c2921b0ab246b045741586113087f337c05d00f20121de00800faa873611cc0690a8f27f31d44242c43420e2438273b5170429c46733429a29448e21410d984d95e9dd6fcac047527091f927fc5269525fb0cd490c2b837badc093ae0e51333f91620001a2879946224c48395d08cea912028000a74a0f62d2abda7e000537811c4865215302b80b945250002e91466c3d485856d49e9c1431987d8167e526a10759529ef29ab30412e3d70001b7137ccdd1e6344c822d331d2aef47ac00005b25e88ea3fc36232781ba7293b4906cef4dbc61992b51768f41d9a3542fad0113d88b95a2000091126010616e0000eed4ac0a26d51cfcbca16036000019605f369f1b5533858b32aad1d92e46f5fa96515f87fb60cb090dbcbb017a8e856d8a0b14d8ce90600d600039180008c14fb8840f20af52511ea8d4c55e621000158067c1b5800184e0000003245262533132046d4d80001f280000000006fe80002b000055690b897e21e0000000000b6d0000000000a5e00000000002ec2ef10b077499a0001f1d1ca000000005c000cff398b7dc000c6b0000d2c0000000000001b524eb60d897c00000000039089b4ae46a80b9087613a000139da5c0
  | 31 => 0x137000000000000066c26603b25ee000142800069d0b9000066c15771f889c8c89062f52e9c4560006a098c839a6ac6411240c625f146200004fa0003909910d5c00037c8c10fbe9ba501910cff0000000249dc58ab3312000145421a5f3994d41a0d45ca2c0d2deba21c29c1010c928128b344e0e7b528114b976c4cc5e1b3017548506f519809581e5002b0c9bc02987041519086b2942310058b6d5e5f1a2d481c58f08330180c84a95a92370ec2b9755a31990a24363a286588d668b56f0c01230715701aaed8f893423407f0816de301f1214ac2b584ad857573edc427798898c639541c0c79aa235d1acb69dab6da01532cf9158d55141adc8f88ad045f1badc70d901ff16cd9ae1ec690b3a5bbecb96eb9e508384e363f30499f4cf62ec1d346ccc4f645180d04c42f250997568c1023629ec46c81820d13284d0ee220d72858b9cb9c4418d3891c0313721064b4e1bf3a180ada005e1444346801aacc540b79da3e8224d9225830c9b04da3150900c1f3682384faa4c64dc09d1c2628f3a59c59bd207846d943c1d04775820da03c41c9279a8b47383ce655a1f141809c2aa0c2c79e39e3ffaed4658c7251005099906815dba520de8e0f4f990b5c9472e5368800376a34209190c5748ef3a032b966689a3bb98059c859b06410cd2760421402a21c40d392f42b1c46270f00005c4042e1e3390000676b740e220348f01341a39b855d0e2536b1f5d1724950001840988d653128ec8094a950a2b5f56aa7873dd179c05ccb86360ead7a69771f98304e403b057680012e24222ce9c450063786089e300000250002a8004635b4b500007ce3776ffb0250fe14324907600002d000000006de0006d5800000082d4a396888bae154f30e1000000054980013e2d920000000d8e0f0014043130c47242c2d407829c7167a93800098216413a00000005eb22f1124d67000122cafca3605036d531a1c7000000125a90406907787c8415557019d4c89de1438abc0005680001051116d834863790a36706240a1813141096df0ed00daace28a2aa5b747a868b16a4000b2b5ff2c557900002902894bf059a69a8000000d6b089aad4abe69500000018fe79f57bb29d3945fd000000175c26e295109873e0005ef181d1c46bd5dc80000001b358580000005784260e350ac42466e30a0d0acd40b10ebca901516ec2fe4b02bad3a5000004c82907c8d012fc7632aa8834e4e4696d789e10d6cb138c88615749835911ad84a467e06f8a2813e35c5448520d309457228cfcd78ddc38026b95327741b696712ba0002a494b573a8401748875284c18369af5c4e079653587c5c5c5c763291c40b411d1409d6c000ae928c92bc0002fd000109c0003d3000318188a000670354c00064c126a63861888216e2a091e054e0000000000cee05412f40000000000
  | 32 => 0x32180008df09e9f5981a0001769db82762a331e8001be439d4100370d86841028ada1a9ea9c0000634acae0137b314c3240f80150490000c9f65119000000004ee1e5c2fc3763be800024c5c312d8cc8e703b1503357c1460000000000000000000000110e91e3510e480b2a145dd0000222cd60003440c7e0fb6491ac91c08ee2d2826c54a17b1ad1c1450a4bc0001c8927233745685494724912ea205d43600063b80002a60003b00001a245d10aaa4597dc8005bf228d57c1f000f2f508506641ab825064c592112b6281cc2223d2800000081d34c8174dc6b2e037000172a5d50003005b424b534681ad2c83c80388058000af662f800188c6f105e1224a24bc55592f641024e2669b4f45f8af9252384598eb076750024b5a04e1121a18c18a8d36f92cc7267cc05c8c800005c00be288c68c55608426e597eb57172a0416a60000a015c52220b500000b5074c4c21281dd8c21ba18781c07460000002b2879483f5a1800084200037625b17eeadd0000fc000000025528f4a349c216380000c074f1f1000082026b3fb05a0be45da3361a683dcb3101c298c4e6d403dc0b78000380062a7256d6a04000215c08c90200020d4000cc91141b259744612099f9896417942d2d805c60fe2caa974b5e00040c219c000c8e6098000000be60002b6db60b2116b27c16920001fdb7b5358d6f3fe2bec4020842b91fad8e03832572ebccf6e3b60b0738000a8e1e017dc40a0000002d74cd20000000000000344335148d160b143968000eccb6100000003be0001958000b843f450504f9c3200017a065c490a2b1038000104c7b00005718c40ed4c58140fea262000118ce140006ba817ca4ec3768b83a8d220eb05338c487089f57c1cf9562b345372024000cbb000052c0007ed36708f57d60004d180008bc2cc000312926c9675c50000000000226a2180000c239c8e99354b486dfa96c5fe8470a72f6003a78614c9d7420a82716a8904f36b9a0002b1400060856317ad33a43d1e4ad6ccce2f900009d996a3e156b26c5c426b96bf0ccc3d03ad1e208a549250e039156882ca925e8078d6322fb04b1ce926e4541cca4a9128a3f14eb90c0c4c296e08cd1932e260b09e4545e4456abb774000b7d00020f400080a0001a90000b0845999242d81b226c00003fa56700014200000685ae000121e03c6e5800171613c28980000004dc0000001c60194047982d3420006b50001af433d00000000009e32c500006ceaef4fe3258000b8858eb0283200004fd9e2025cc2e3b92c7c0000d9000161825600055e2165906000000101c000000130abf40005362edb1cc6448233af18dca781d300000000002e01afb5d000097c3e0ae654f63051bd1eb122419b0351b883a80e223b00010d227220f94308900001b29a24c308980df13d887428962c2f89902
  | 33 => 0xcf70001a28000ce227d8c68000d080000000000dc823528685be4744650fe13000003b5884d4a0d3c3c6831818e0006cf90dc0000002a580007860000788adc1a21bd408b2b02927b246c2dd8750bc04502a8c2eedcd56093b929226926b89fd0e034f538aa910da90a5b5252c4c0a013959e80c1e9f81a0830c652bc420b8f14334923375010d396a726a731647d27102b1a7f870c3f53011a5d99c3f632c8159bb21a0110aec8fce0b01898db0ba0a113d329fc10ee1a288a0c53b63554671dccab07db127b86dbec88a5399960b788f60770bcc38088f23811041de1205f6b234ba492e6728a409862572cf99e00cc1b52dc0051b7ab8961816a17ba0b449780103462c36f9b564ca843c7242ca8cde7ef0a6b2f820208e648006164646e3138f40b48b10607b07169adb728020654044345bc0000000b8060e97d169e2165aa2111ab40004b907dc00000000018e50a8d0c6cb18d0b62d824a3342c1f87de1b9811400000000a9c70000b2d56e277d07221c5ba84b02549e5668163107c8653282109baaa1d65997359f81303403788c2ad0e67eaae591040a251ab9da406ef495a2f513c5ac4a537e033231f2a9833dc0c529464002c62a2f061e15a53b493251103280d262a03d9bc9a5a2c22a6a270d985a039e9415438b4a628000096e0b85c22f2c96205466196e9556d4400014a02ea25c47337b091493512324c14cca590bb0d800000000149e914423c74ab9d1cbba621669239171a51559e19719e0dbb12502286288a81a8803ceca8da476a0d929854521c8354152ba3088266d7309cf3309898b00afa6d338ad1483eb0000c1800062c3798bd8800af20870f680000005891d45a8603002d8f8000026660a83c934e2170080bf800094448000000002d35c3af700000000000a78d8c22a21f80000002b002099094c42650b987c8000b8600000000000000000000ab279c36b98a1a0aacf6e98a2d57e5b2171000149a0002bcb4a0000b3530cb094ce800000036d9ac40000002f55c526a559c0d080008fa64ea450000000162b630956a7752ab1b5916032637b3090d00004ec0670cd000015f00014580000000000e8275707193752ac2d84660000c2c01127529203146f500000010d86625040590000ca82670b852a82822f486c079a00054628611a465b70e8000ebead714f9574bc8a8b26900000009212da93e80008fe5380000a980006bdad7d9ce0002c43224bbe00024b000115e2a01249bf1a44a790000e0586c00031d8000000ac200020788541071ea8000eb8c8c1bfb138440000405800000097f67c1944000e0b6d9b1f465e91f1aa35b8da4000058b40901c000000000098a0002faa0f00009c06ef2488fba000000310000000018b0001af20000c78af030656c5e897b17bea862298bc520a1ac426b43c33c0002b2
  | 34 => 0x4ae3c0003b64d7aa9cb6e6353b7b7c511c29a4551528000b6550807cc6ea23a00000dd0dc0000001f7103e65a00012c0b8c9941af38c97ca00000519580000850000000000000000248000000067a0564000a7464a94400000003a48000a0c8643e980000bc56f6500df0e045225fe28540000006221a84a3a6e74e40001acc1a9666349c000a242ff9d4039460a1d1136451a8d9000000137e00042f8000c0c1c25e78000000aa24d5ab99c68237633b0393ac89d5798b986dc1a157196083f4ce16d1961529c8ff463a750f5c0f756d1118a7e7442312b48b06c04569aeec4ea72a4f40fa1238ca56be1a30bc432871f1781aecd8737f9021350e004d48d89736c052bb85a418891a087b92c1c84b468e2a788b81db00d28f17204d022ca9d83a07ce27eaf08cf2d1810f9a792f206161583945a87e44ac1e4d82e7ee7150a202f0cc612cb8346787680c7290889ea286b40c4400091d03aa5403fe000324367400cb770cea6788e6a054de8ad168800057fa75dc8868300004cd18c690317ada4370c5600e0744c7869365b18153b2a9713cadf0dca24432f8ffc0f402f404000000054f34e0000eaa89b0ad20559d00000e41e0933e86f00038f09ee66338f89f961895503996e460600000000000deb6702000000f8e2d00004d80005302bd00002ac0006e3336855400058334ac83003d25f16452cc0002a19fd1042834222057845a1ed00000000001a45d8ac4c20620626f323c4b07b300008e57700341a8000000000068c8000000ca300000006207352260000f080003500001a944f23a6000000011751b800000000000006d8e9c00011f00001fa0d738f0630000ccb6a3000000003a00000004320000000000000d0a6ea01616fe2fa08f335544e3237238e38ba6cef701114917e2dd47e9fdda0e0000e90001c209955df0000bae0000e7916c6f21e40269b81586d581dc25f51863ac0000c9115c9b53119c913c2b1b3e12ca1c48e275b89cf006c39106d0a883ba534403b10d19a50325d85953c400010780000003f700021a99002f764a1fc822c00000000011a64b623604bc04edee000382516c2c14292e78000e171fc812567a3523d491090c456e5b7aa6889c494118191578cc1a6c58b9d828a3e48aa7a40000005f08cf89100000000ded8b800040d9da8000000000225400024b5c116b9b4445000007a59f2000593000109e00045d13851bcad800000012200000000324000ba56ca83e861cda515a88b02521f600f9d18b963630b52c61192c350b6a0bd6961b136e9f8175600000020c968a5bf00017f91440910b5842cc24bf06dc1d883f624553a9a5918403b0538001ae600000038d80000000000901a4c5b02f325d8dd06943e534e8940801424b2908bec3a618a61ca8eb910000f180aa000000000d12297055bb1e400
  | 35 => 0xff476ab3a0499928818d8f1559c7430a000484b0b40000000000001a8ea9b00000003c200045a0000ca487921a9c38000507000000017aac4339800164e2ee2f783a4bda2ca332af0514e3a436c80014a69194271f196c679869b0285c1893301f869d378a540000225c6a5a63c49128e24b0a0001c0c000acd000139461a0000001afd386c8500006ad9f67526e7000001c573582882c0007780fa9d581800004c880012e8c871db84353c852426f8621570be45e688fc88e03554a355129e0006cd21edc9c17a000062c2a0a6a38400015fc69b61faf382e08f739b00cc7b2c392fdac25156330575b73c000a5862580000000003e5a8494000000000000ac400009f8000c2ed30000000000030200002f800039b0ee00001186ba1a6b4c824e7793c58e2c55c833391b3cd968517190859978e8f528
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x7a8c0400005200003c0048440c5600143e784e0a22005c46004c900600347064242c6e82605a7e32881c6c80720266002600000068365838840e5e124a2a763a20926200167c8e181a421028406a0074500830861e8a2e0054120000502002870218180080040e040410b0c784080040f65c8154c645480103d97e0153191520040f660649c6525480103e98191709495251c8b2488650c655086903c9761231594420048e241848c5651086903e97e1130594420040fa5c84549609440182c752094358b4151e0b208845d6629040183860e15709094151e0b10a87d95425050d03c9661672905410060e183855c241504012399819442d81410058aa4b84d946050401a3065a0642181410048ee63651086050401239981944218141004aa2498550c60504012399520943181410048e66254148605049d2b291e164218141006869cd851086050401a197361442181410068a9c9851086050401a297261442181410048e66254144605040123995a0a41181410050ea5d651c1411040143897594705044100706a0d651c14110401c198359470504410040fe61741d165c854742c925d0745972100436660631c141484014359114174185500040f65c84548615408b23890612315974022e0ea1d65dc141d000143897594705074024e26dd9831c141d00019187560c70507400040fe59859ca419012d03e9890175189400050d644405d4615000103c9761462505400060e1c185189415000182c752094358840567061d5434c162100016889250d30588400048d656819096110159c187550d30584400060e203855da4110001499970c93019120005a4644324c0644800103f985d074594201a40f2617559042c406903e98d917510a102750ea43645d44184001a306520530191100052665c324c06444001691910c93019110005b0644324c362440018387061472590102060e201755904204001c18405d5631081022f069d17558f400409389b8758d41d001024526a527458d1004001c1b751d16344010007061d47458d100407f2d09858d2144010
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xd021d49250d3058840
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x6
  | 3 => 0x1
  | 4 => 0x2
  | 5 => 0x4c
  | 6 => 0x4e
  | 7 => 0x138c
  | 8 => 0x5
  | 9 => 0x94c
  | 10 => 0x94e
  | 11 => 0x124c
  | 12 => 0x124e
  | 13 => 0x138e
  | 14 => 0x3
  | 15 => 0x8c
  | 16 => 0x8e
  | 17 => 0x150c
  | 18 => 0x98c
  | 19 => 0x98e
  | 20 => 0x128c
  | 21 => 0x128e
  | 22 => 0x150e
  | 23 => 0x10c
  | 24 => 0x10e
  | 25 => 0xa0c
  | 26 => 0xa0e
  | 27 => 0x130c
  | 28 => 0x130e
  | 29 => 0x180c
  | 30 => 0x180e
  | 31 => 0xa4c
  | 32 => 0x134c
  | 33 => 0x20c
  | 34 => 0x20e
  | 35 => 0x140c
  | 36 => 0x154c
  | 37 => 0xb0c
  | 38 => 0xb0e
  | 39 => 0x140e
  | 40 => 0x154e
  | 41 => 0x28c
  | 42 => 0x28e
  | 43 => 0x148c
  | 44 => 0xb8c
  | 45 => 0xb8e
  | 46 => 0x148e
  | 47 => 0x184c
  | 48 => 0x184e
  | 49 => 0xbcc
  | 50 => 0x14cc
  | 51 => 0x40c
  | 52 => 0x40e
  | 53 => 0x160c
  | 54 => 0xd0c
  | 55 => 0xd0e
  | 56 => 0x160e
  | 57 => 0x188c
  | 58 => 0x188e
  | 59 => 0xd4c
  | 60 => 0x164c
  | 61 => 0x104c
  | 62 => 0x194c
  | 63 => 0x94054
  | 64 => 0x4d
  | 65 => 0x138d
  | 66 => 0x180054
  | 67 => 0x409
  | 68 => 0x1609
  | 69 => 0x1049
  | 70 => 0x1949
  | 71 => 0x95394
  | 72 => 0x289
  | 73 => 0x1489
  | 74 => 0x2c9
  | 75 => 0x14c9
  | 76 => 0x125394
  | 77 => 0x1649
  | 78 => 0x10a
  | 79 => 0x11394
  | 80 => 0x181394
  | 81 => 0x98094
  | 82 => 0xb1514
  | 83 => 0x99514
  | 84 => 0x99554
  | 85 => 0xb0994
  | 86 => 0x98b14
  | 87 => 0x154994
  | 88 => 0x449
  | 89 => 0x129514
  | 90 => 0x155514
  | 91 => 0x148114
  | 92 => 0x11494
  | 93 => 0x14cd
  | 94 => 0x160114
  | 95 => 0x11614
  | 96 => 0x164d
  | 97 => 0x104114
  | 98 => 0x11054
  | 99 => 0xb8a14
  | 100 => 0xa0b94
  | 101 => 0x184a14
  | 102 => 0xa4d
  | 103 => 0x130294
  | 104 => 0x131494
  | 105 => 0x130414
  | 106 => 0x131614
  | 107 => 0x131054
  | 108 => 0x195314
  | 109 => 0x131954
  | 110 => 0xb9814
  | 111 => 0xbca54
  | 112 => 0xd4a54
  | 113 => 0x194a54
  | 114 => 0x1a89
  | 115 => 0x1354d4
  | 116 => 0x135654
  | 117 => 0x135054
  | 118 => 0xb0214
  | 119 => 0x140214
  | 120 => 0x154214
  | 121 => 0x140b14
  | 122 => 0xb1414
  | 123 => 0x154b14
  | 124 => 0xb1554
  | 125 => 0x141554
  | 126 => 0x155414
  | 127 => 0xb8294
  | 128 => 0xb9494
  | 129 => 0xb9614
  | 130 => 0xb8414
  | 131 => 0xb9054
  | 132 => 0x194b94
  | 133 => 0xb9954
  | 134 => 0x2cd
  | 135 => 0x185494
  | 136 => 0x185614
  | 137 => 0x185054
  | 138 => 0xbd4d4
  | 139 => 0xbd654
  | 140 => 0xbd054
  | 141 => 0xd54d4
  | 142 => 0x1954d4
  | 143 => 0xd0414
  | 144 => 0xd1614
  | 145 => 0x44d
  | 146 => 0x189614
  | 147 => 0xd5654
  | 148 => 0xd5054
  | 149 => 0x195654
  | 150 => 0x198d
  | 151 => 0x4954
  | 152 => 0x5554
  | 153 => 0xe89
  | 154 => 0x5814
  | 155 => 0x18c9
  | 156 => 0x9cd
  | 157 => 0x9ce
  | 158 => 0x12cd
  | 159 => 0x12ce
  | 160 => 0xe8e
  | 161 => 0x18ce
  | 162 => 0x128214
  | 163 => 0x74b
  | 164 => 0x40b16
  | 165 => 0xec9
  | 166 => 0xecd
  | 167 => 0x1a4d
  | 168 => 0x9c416
  | 169 => 0x12c416
  | 170 => 0x41716
  | 171 => 0x41616
  | 172 => 0xe89d6
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2625
  | 6 => 8132
  | 5 => 3664
  | 4 => 74
  | 3 => 1
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (107625+((h/875+packedAt gbK7 (97125+(h % 875)*12) 12) % 3812)*13) 13
  | 6 => packedAt gbK6 (428276+((h/2710+packedAt gbK6 (390336+(h % 2710)*14) 14) % 11807)*14) 14
  | 5 => packedAt gbK5 (232049+((h/1221+packedAt gbK5 (216176+(h % 1221)*13) 13) % 4397)*13) 13
  | 4 => packedAt gbK4 (5348+((h/24+packedAt gbK4 (5180+(h % 24)*7) 7) % 89)*8) 8
  | 3 => packedAt gbK3 (82+((h/1+packedAt gbK3 (81+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7f0f81e07c1fff8fc03e03ffc39fe48e41f64f
  | 1 => 0xfff001ffffe07ff0003fffffcc6407fc7e387f
  | 2 => 0x81fffe007fff83ffffc003c0307878f38fcf8c
  | 3 => 0x1ffffff800003fffffffc003f807f03f00ff0
  | 4 => 0x1fffffffffffc00000000003fff8003fff000
  | 5 => 0xfe00000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x33039064140ca68e42b212568189e48640d645
  | 1 => 0xc4300088a92049100104a8a90424013816281a
  | 2 => 0x1054a2004e5901a495800b01905828d08b4a8c
  | 3 => 0x218955350004224b2a3950022b805603600560
  | 4 => 0x41ee79de739670020c10600c3ef68003fdb000
  | 5 => 0x780060180318400c302182303f7f7fec000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeafcc8fce8fc88feeafcc8fce8fc88feeafcc8fce8fc88feeafcc8fce8fc88feeafcc8fce8fc88feeafcc8fce8fc88feeafcc8fce8fc88feeafcc8fce8fc88, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37139
namespace PEqualNP.Outside.L_meta_37139
open PEqualNP.Outside.L_meta_37139.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 13 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 17 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
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
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
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
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 21 := bs5_3_0
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
theorem bs5_4_96 : Interval s5Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 99 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 46 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 1 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 74 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_3488 : Interval gbAtlas 5 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3520 : Interval gbAtlas 5 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3552 : Interval gbAtlas 5 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3584 : Interval gbAtlas 5 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3616 : Interval gbAtlas 5 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3648 : Interval gbAtlas 5 3648 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3664 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)) (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 bgb_5_416)))) (concat (concat (concat bgb_5_448 (concat bgb_5_480 bgb_5_512)) (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640))) (concat (concat bgb_5_672 (concat bgb_5_704 bgb_5_736)) (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 bgb_5_864))))) (concat (concat (concat (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312)))) (concat (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536))) (concat (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 bgb_5_1664)) (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 bgb_5_1792)))))) (concat (concat (concat (concat (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)) (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 bgb_5_2016))) (concat (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112)) (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 bgb_5_2240)))) (concat (concat (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336)) (concat (concat bgb_5_2368 bgb_5_2400) (concat bgb_5_2432 bgb_5_2464))) (concat (concat (concat bgb_5_2496 bgb_5_2528) (concat bgb_5_2560 bgb_5_2592)) (concat (concat bgb_5_2624 bgb_5_2656) (concat bgb_5_2688 bgb_5_2720))))) (concat (concat (concat (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816)) (concat (concat bgb_5_2848 bgb_5_2880) (concat bgb_5_2912 bgb_5_2944))) (concat (concat bgb_5_2976 (concat bgb_5_3008 bgb_5_3040)) (concat (concat bgb_5_3072 bgb_5_3104) (concat bgb_5_3136 bgb_5_3168)))) (concat (concat (concat bgb_5_3200 (concat bgb_5_3232 bgb_5_3264)) (concat (concat bgb_5_3296 bgb_5_3328) (concat bgb_5_3360 bgb_5_3392))) (concat (concat (concat bgb_5_3424 bgb_5_3456) (concat bgb_5_3488 bgb_5_3520)) (concat (concat bgb_5_3552 bgb_5_3584) (concat bgb_5_3616 bgb_5_3648)))))))
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
theorem bgb_6_7200 : Interval gbAtlas 6 7200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7232 : Interval gbAtlas 6 7232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7264 : Interval gbAtlas 6 7264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7296 : Interval gbAtlas 6 7296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7328 : Interval gbAtlas 6 7328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7360 : Interval gbAtlas 6 7360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7392 : Interval gbAtlas 6 7392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7424 : Interval gbAtlas 6 7424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7456 : Interval gbAtlas 6 7456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7488 : Interval gbAtlas 6 7488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7520 : Interval gbAtlas 6 7520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7552 : Interval gbAtlas 6 7552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7584 : Interval gbAtlas 6 7584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7616 : Interval gbAtlas 6 7616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7648 : Interval gbAtlas 6 7648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7680 : Interval gbAtlas 6 7680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7712 : Interval gbAtlas 6 7712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7744 : Interval gbAtlas 6 7744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7776 : Interval gbAtlas 6 7776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7808 : Interval gbAtlas 6 7808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7840 : Interval gbAtlas 6 7840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7872 : Interval gbAtlas 6 7872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7904 : Interval gbAtlas 6 7904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7936 : Interval gbAtlas 6 7936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7968 : Interval gbAtlas 6 7968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8000 : Interval gbAtlas 6 8000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8032 : Interval gbAtlas 6 8032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8064 : Interval gbAtlas 6 8064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8096 : Interval gbAtlas 6 8096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8128 : Interval gbAtlas 6 8128 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 8132 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 bgb_6_576)) (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 bgb_6_704))) (concat (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832)) (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960))))) (concat (concat (concat (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216))) (concat (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)) (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 bgb_6_1472)))) (concat (concat (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 bgb_6_1600)) (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728))) (concat (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 bgb_6_1856)) (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 bgb_6_1984)))))) (concat (concat (concat (concat (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 bgb_6_2112)) (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 bgb_6_2240))) (concat (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 bgb_6_2368)) (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 bgb_6_2496)))) (concat (concat (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624)) (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 bgb_6_2752))) (concat (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880)) (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 bgb_6_3008))))) (concat (concat (concat (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 bgb_6_3136)) (concat (concat bgb_6_3168 bgb_6_3200) (concat bgb_6_3232 bgb_6_3264))) (concat (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 bgb_6_3392)) (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 bgb_6_3520)))) (concat (concat (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 bgb_6_3648)) (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 bgb_6_3776))) (concat (concat (concat bgb_6_3808 bgb_6_3840) (concat bgb_6_3872 bgb_6_3904)) (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 bgb_6_4032))))))) (concat (concat (concat (concat (concat (concat (concat bgb_6_4064 bgb_6_4096) (concat bgb_6_4128 bgb_6_4160)) (concat (concat bgb_6_4192 bgb_6_4224) (concat bgb_6_4256 bgb_6_4288))) (concat (concat (concat bgb_6_4320 bgb_6_4352) (concat bgb_6_4384 bgb_6_4416)) (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 bgb_6_4544)))) (concat (concat (concat (concat bgb_6_4576 bgb_6_4608) (concat bgb_6_4640 bgb_6_4672)) (concat (concat bgb_6_4704 bgb_6_4736) (concat bgb_6_4768 bgb_6_4800))) (concat (concat (concat bgb_6_4832 bgb_6_4864) (concat bgb_6_4896 bgb_6_4928)) (concat (concat bgb_6_4960 bgb_6_4992) (concat bgb_6_5024 bgb_6_5056))))) (concat (concat (concat (concat (concat bgb_6_5088 bgb_6_5120) (concat bgb_6_5152 bgb_6_5184)) (concat (concat bgb_6_5216 bgb_6_5248) (concat bgb_6_5280 bgb_6_5312))) (concat (concat (concat bgb_6_5344 bgb_6_5376) (concat bgb_6_5408 bgb_6_5440)) (concat (concat bgb_6_5472 bgb_6_5504) (concat bgb_6_5536 bgb_6_5568)))) (concat (concat (concat (concat bgb_6_5600 bgb_6_5632) (concat bgb_6_5664 bgb_6_5696)) (concat (concat bgb_6_5728 bgb_6_5760) (concat bgb_6_5792 bgb_6_5824))) (concat (concat (concat bgb_6_5856 bgb_6_5888) (concat bgb_6_5920 bgb_6_5952)) (concat (concat bgb_6_5984 bgb_6_6016) (concat bgb_6_6048 bgb_6_6080)))))) (concat (concat (concat (concat (concat (concat bgb_6_6112 bgb_6_6144) (concat bgb_6_6176 bgb_6_6208)) (concat (concat bgb_6_6240 bgb_6_6272) (concat bgb_6_6304 bgb_6_6336))) (concat (concat (concat bgb_6_6368 bgb_6_6400) (concat bgb_6_6432 bgb_6_6464)) (concat (concat bgb_6_6496 bgb_6_6528) (concat bgb_6_6560 bgb_6_6592)))) (concat (concat (concat (concat bgb_6_6624 bgb_6_6656) (concat bgb_6_6688 bgb_6_6720)) (concat (concat bgb_6_6752 bgb_6_6784) (concat bgb_6_6816 bgb_6_6848))) (concat (concat (concat bgb_6_6880 bgb_6_6912) (concat bgb_6_6944 bgb_6_6976)) (concat (concat bgb_6_7008 bgb_6_7040) (concat bgb_6_7072 bgb_6_7104))))) (concat (concat (concat (concat (concat bgb_6_7136 bgb_6_7168) (concat bgb_6_7200 bgb_6_7232)) (concat (concat bgb_6_7264 bgb_6_7296) (concat bgb_6_7328 bgb_6_7360))) (concat (concat (concat bgb_6_7392 bgb_6_7424) (concat bgb_6_7456 bgb_6_7488)) (concat (concat bgb_6_7520 bgb_6_7552) (concat bgb_6_7584 bgb_6_7616)))) (concat (concat (concat (concat bgb_6_7648 bgb_6_7680) (concat bgb_6_7712 bgb_6_7744)) (concat (concat bgb_6_7776 bgb_6_7808) (concat bgb_6_7840 bgb_6_7872))) (concat (concat (concat bgb_6_7904 bgb_6_7936) (concat bgb_6_7968 bgb_6_8000)) (concat (concat bgb_6_8032 bgb_6_8064) (concat bgb_6_8096 bgb_6_8128))))))))
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
theorem bgb_7_2624 : Interval gbAtlas 7 2624 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2625 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 bgb_7_512) (concat bgb_7_544 (concat bgb_7_576 bgb_7_608))))) (concat (concat (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 (concat bgb_7_736 bgb_7_768))) (concat (concat bgb_7_800 bgb_7_832) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928)))) (concat (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088))) (concat (concat bgb_7_1120 (concat bgb_7_1152 bgb_7_1184)) (concat bgb_7_1216 (concat bgb_7_1248 bgb_7_1280)))))) (concat (concat (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 (concat bgb_7_1408 bgb_7_1440))) (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600)))) (concat (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 (concat bgb_7_1728 bgb_7_1760))) (concat (concat bgb_7_1792 (concat bgb_7_1824 bgb_7_1856)) (concat bgb_7_1888 (concat bgb_7_1920 bgb_7_1952))))) (concat (concat (concat (concat bgb_7_1984 bgb_7_2016) (concat bgb_7_2048 (concat bgb_7_2080 bgb_7_2112))) (concat (concat bgb_7_2144 bgb_7_2176) (concat bgb_7_2208 (concat bgb_7_2240 bgb_7_2272)))) (concat (concat (concat bgb_7_2304 bgb_7_2336) (concat bgb_7_2368 (concat bgb_7_2400 bgb_7_2432))) (concat (concat bgb_7_2464 (concat bgb_7_2496 bgb_7_2528)) (concat bgb_7_2560 (concat bgb_7_2592 bgb_7_2624)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeafcc8fce8fc88feeafcc8fce8fc88feeafcc8fce8fc88feeafcc8fce8fc88feeafcc8fce8fc88feeafcc8fce8fc88feeafcc8fce8fc88feeafcc8fce8fc88
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276813000 * 2 ^ 32 + 4243127432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37139.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,3]⟩,⟨.or,[2,5]⟩,⟨.or,[2,6]⟩,⟨.and,[4,7]⟩,⟨.or,[1,9]⟩,⟨.and,[0,10]⟩,⟨.or,[4,5]⟩,⟨.and,[1,12]⟩,⟨.or,[3,13]⟩,⟨.and,[8,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813000 * 2 ^ 32 + 4243127432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813000 * 2 ^ 32 + 4243127432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37139

open PEqualNP.Outside.L_meta_37139 in
theorem PEqualNP.Outside.L_meta_37139 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813000 * 2 ^ 32 + 4243127432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813000 * 2 ^ 32 + 4243127432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
