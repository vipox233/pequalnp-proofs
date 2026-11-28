import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40982.Model
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


end PEqualNP.Outside.L_meta_40982.Model

namespace PEqualNP.Outside.L_meta_40982
open PEqualNP.Outside.L_meta_40982.Model
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

def SBf (j : Nat) : Nat := [7, 5, 5, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_40982

namespace PEqualNP.Outside.L_meta_40982
open PEqualNP.Outside.L_meta_40982.Model
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
end PEqualNP.Outside.L_meta_40982
namespace PEqualNP.Outside.L_meta_40982
open PEqualNP.Outside.L_meta_40982.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0xe421
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
  | 0 => 0xffffffffffe03ff81fffffffffffc03f1fffc7
  | 2 => 0x3fc07f00fffffffe0f80f81f80fffffe64cff
  | 3 => 0x3fff8000fffffffff000ffe000ffffff870ff
  | 4 => 0xfc0000000fffc0fffffff000000fffc0ff80f8
  | 5 => 0xfffffffff00000fffffffffffff00000ffff00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x186450a1802382180318d18a28e2c6190a95c3
  | 2 => 0xa929314696449469606a46a1b1255a6a664c5d
  | 3 => 0x5250a26b2a8928b2ad048b6c8249acb4b870ae
  | 4 => 0x6362c58dcd120edcd6b6e049248e3718df80f0
  | 5 => 0x8383060e0e1c30e718c70c71c7003820f56a00
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaaf000a000faaaaaaaf000a000faaaaaaaf000a000faaaaaaaf000a000faaaaaaaf000a000faaaaaaaf000a000faaaaaaaf000a000faaaaaaaf000a000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40982
namespace PEqualNP.Outside.L_meta_40982
open PEqualNP.Outside.L_meta_40982.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xd431
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
  | 4 => 2*((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 1)
  | 3 => 2*((h/1+packedAt s2K3 (16+(h % 1)*1) 1) % 1)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffe03ff81fffffffffffc03f1fffc7
  | 1 => 0x1fc07f00fffffffe0f81f01f80fffffe4ccff
  | 3 => 0x1fff8000fffc0ffff001ffe000fffc0f8f0f8
  | 4 => 0xfe0000000fffffffffffe000000fffffff00ff
  | 5 => 0xfffffffff00000fffffffffffff00000ffff00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xc2450a1402382180318a31a28e2c5150955c3
  | 1 => 0x5489314656449469606a0d49b125596664cc5d
  | 3 => 0xa930a26b6a890ebaad0496dca249ad94b8f0e8
  | 4 => 0x31a2c58d8d1228d4d6b6c091048e3638df00b6
  | 5 => 0xc1c3060e0e1c30e718c718e1c7003820f6aa00
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaacc880000eeaaaaaacc880000eeaaaaaacc880000eeaaaaaacc880000eeaaaaaacc880000eeaaaaaacc880000eeaaaaaacc880000eeaaaaaacc880000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40982
namespace PEqualNP.Outside.L_meta_40982
open PEqualNP.Outside.L_meta_40982.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xa400412c70400000011930400010400006c0080200003080000000ff31fe20fe31de43fc30fc31fd43fc43fc32fd20fe10dd43fd21ec21fe40fe43df32dc31ff40fe42fd10ff20ff43fd42fc40fe32fc42ff32ff30ff21fe41fc10de30fc20fe21ff42dd32fd40ff10fd32de31fe30ff41ee21dc30fc41fd41fd30fc21fd31
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x9800800202910215019d8002862503983c03c41c0000038a0604880093800100000d8287811a82380880a9828380240001948a010784820001800d0011734c821aea9e815e53d079ea710f394c21b6a9487d431c87aea2995b54830af280615e53086baa4185794f21aa28a655e510c6eea2995794c41f218843cf524cabea688730c621e6a1c43cf32086daa5085714d419faa2415d548c2bca6105794230b7a92216e51086b8a60857d4d41af284875f544ca78a8885794643af28e65e541086eaa3a15354a43aea9e415f53883cc8210f50c421afa9a817751483a8a2995714e21ae282877b50506e8a2a07908610afaa0635c538839c43185754c40aeaa2655d530839ca4185754c41bb28e855f548c6baa790d754e32af29c855d528c6d8a498d794c42e6188436e5290f9c6310de14141afa9a435d5310bb4a0185b94840afa9a41ce31086baa610d354830af298815e530cabea9995b149409faa2215e53c439a64905714132b6292835e510c39aa610d794031b6a96835c53482dca310db54840af29e85cd520c2dea498f388430afa9c435d520c6b8a2a1db94b31e629c43ce5290ebca7907350c21aea9e21cd32c839c8610f34ca21b729421cc218c2bca621d714d21e7a12656f525039884997908410e2188435d540c2baa7215714d10e721c435d5290fcca210d794631aea9e836c52442bca31857553329e2a2415d5490ebaa7085d14532afa98215f5250eb8a6a07594431aea9461e731086dca5a0dd54440bb28881cc210c39e6510dd14520e6a94875f540c2b8a2995794231af29e815e53842bca1995755031aeaa4636e520c2daa598ddd4540b7a92835d53d0abea91867d5143
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x6090830102cc1c038c18c04b080b010000800140000c03c1002b1185324824d6294f10d1185520c21d6414e21d1d48514ca1d6414c10d194c21842c7640c421931855290ec46154a439358853042c6618c421d1d88514ca4f658843093594210c2c4635042191185520c2e06050421935885050f47421453299185520c2c7650c421c31513248345321452093596430864f6255230d1944218c24c6154830b1590310864e6590e21b19845388658605513295185544cac4614cb209358a508c68d6414e21d1d855290e546154a43931953248255650c4219358a53d024d6294c41b198031086c46150c21b15943108744421453295185520c24d62d5031b1987538864e65d0932d1d85520c25661d4e20b1987424cb446154a43911855290e646154a43b1185520c24f6255231d114c210424d62d5030
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x100c000000018cc22238ac428287119c7625523090ae9b286210c447158a53d022238ac5aa061415d05308410a0ce9b10a29944575d9031087022a0c299241115d85308410
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 5 => 2*((h/37+packedAt s3K5 (800+(h % 37)*6) 6) % 50)
  | 4 => 2*((h/62+packedAt s3K4 (4455+(h % 62)*8) 8) % 165)
  | 3 => 2*((h/34+packedAt s3K3 (2280+(h % 34)*6) 6) % 60)
  | 2 => 2*((h/17+packedAt s3K2 (490+(h % 17)*4) 4) % 10)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfff81ffffffffff81fffff03fffffffe3e3fff
  | 1 => 0x7ffe03f81ffffffe0f81ffc1e03ffffc9ccff
  | 2 => 0x7ffffc001f81fffff001fffe003f03ff1f0c7
  | 4 => 0xf800000001ffe07fffffe0000003ffc1fe00f8
  | 5 => 0xfffffffffe00007ffffffffffffc0001ffff00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x3048c285100841080318a300a238b25212155b
  | 1 => 0x5291498a22928a31606a0d5414495ca4c8ccad
  | 2 => 0xa4e285135521d45aad04969ac09266397170c6
  | 4 => 0xc6c7162c79c5077cd6b6c0d291238f31fe00f0
  | 5 => 0x70418306186186718c718e319c00801adaa00
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeaeaea88888080eaeaeaea88888080eaeaeaea88888080eaeaeaea88888080eaeaeaea88888080eaeaeaea88888080eaeaeaea88888080eaeaeaea88888080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40982
namespace PEqualNP.Outside.L_meta_40982
open PEqualNP.Outside.L_meta_40982.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x4021c00000190040840530890d26c2ac0ff10fc32ff42ff20fd41fe31fc43fd40fe30fc21fe43ff31de43fd21de32fc31dd43fd31fe32ff32fe40fc40ff40fc10fd32fc42f421fd20fe10fe41dc32fd10fd30fc30fc20fe42ff21f721fd43fe20fd42fc41ff43ff41fe21ff30
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x1c00300045400c042808c3400006160040200698020418d480018000222000210518022000020042020400001176e52d06dea4885d145429f2a0655d53106f6a0a157d50328eaa065d643c8678a8907994821f210c413f54442eaa3994f550329faa2417551102eaa3a15794a32e7290655d5490eeea2995754e20bb28c435e53d02bca7a1758c821aeaa4659d540cadca4205b54b41b6a908176510c27ca9985714943b6292637651d0ba86410f10c821eaa18435e520cbc842105714d42afa9a435c53442b8a6905d94732cea1e85e432086bca7105754c10e6190435d53d0b3ea8a1f590c21aea9c43cc32886baa62057d4d20af298859d43102bea6a15d14520aea9885e732086eaa2186795032bb290435e5310eeca2205bd4931bc282857651882baa7a05d54620af29c43e542086bca7a0d794c41eb196436c52443cc8410ddd4520cea1c81775150abca6085794c40aea9e83d432c86b8a690f550f21af2948774514ca7aa99857d4d10afaa4659d4350a78a8885755032
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x9a558c0000063588e000020003854350821b1189430870d4354840a359032087465308620b159032086e06050821a559032086c6628c821a959032086c7640c821a559032c868d640ca21e19903208785640c8218759253882c46350821a15903208719431414299189510c21d6595032
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0xe81431814208642bb4c819043415d25308620
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
  | 6 => 2*((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/22+packedAt s4K5 (736+(h % 22)*6) 6) % 46)
  | 4 => 2*((h/54+packedAt s4K4 (2673+(h % 54)*7) 7) % 99)
  | 3 => 2*((h/21+packedAt s4K3 (798+(h % 21)*5) 5) % 21)
  | 2 => 2*((h/15+packedAt s4K2 (147+(h % 15)*2) 2) % 3)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xe07fffffe03fff81fffff07ffffe07fcf8fe3f
  | 1 => 0xff80fe07ffc0fffe0f81ff87c07ff83f6733c7
  | 2 => 0xffff0007fffffffff001fff8007fffff87c3ff
  | 3 => 0x7ffff03fffffe0000007fffc3f803f8
  | 5 => 0xfffffff8000003ffffffffffff800003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x230a144023820880318a30094716426428561b
  | 1 => 0x452628ca448e519606a8d485892aca296332c5
  | 2 => 0x8a144d148914a22ad0416950124d149285c16e
  | 3 => 0x1c58b1e712283bcd6b6c0c452471e723f803b0
  | 5 => 0x1060c1861c30c3718c718e6638018403d6a800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeaeaeaeae080e080eaeaeaeae080e080eaeaeaeae080e080eaeaeaeae080e080eaeaeaeae080e080eaeaeaeae080e080eaeaeaeae080e080eaeaeaeae080e080, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_40982
namespace PEqualNP.Outside.L_meta_40982
open PEqualNP.Outside.L_meta_40982.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x657f524c2f8a2a15f54843bd28087de4310ff2a021df94e42bea8c857d54cc2fea90877cc530bea8e857e53d06fca6905f94f20be2826578504c6fea818fec8010fd90621ec524c2fca6105f94d10fb90c43dd300c3f640905f54d10f721643df430cb7c80a05f54720f799041dd53042f8a8985f94632bfa8a817e5290b7e85215f54c41bfa8263be4250af8a8105fd5231de21083dc438cafaa2215fd4142bf29e21ee42ccafca421dfd4d10bfaa4417d54882fea4a1df95332fc98041de328c6fca418df54321bea8c817e53906faa5185f14540ef984617e54102faa7885f94020beaa6217e50106f8a610dfd4c21bea9483be43d0adaa5a1df54a40bf288217d5010af8a5085f94421bfa8a87bf40102faa121ef90a41bf2868374514c2faa690df95020bf29c217f5050ef8a898dfd5121fd986217f53886faa5a07ecc010ee988637c5150efaa8197d84110fda04817e54087dea498fd14530bf2a2617e520cafea7905f14f10fc18021de53042faa920df95321bf290837f54c8278a8986f10e41bf28c637d518cbb86418cf95021dfaa2437d53d0afaa7195f54730ef98e617d500c6faa020df94b31f6a12437e50842fca018fb94b43bf29885f731042fca621cfd5121bea9441df300c2fea2a14f15131df21a87ed420cafaa910df14d40de2a2637e540c3f28020774c832fd20021bc41d02baa7107750c43be29e43fa40c42fca9187b881209f2a041be43102fca5a1fdd0421bea80657c548c6fca898dfd4121bea9e417e51107d86410ef15130be2a4217c540cafea6905fd5332bfa8a417d52cc2fca221fe0c310f6908437d53d02fea790df14131bfaa443fa30082faa4885f54e20df2a4657d528c6f8a2905714d21df21883f840c82f8a4a0dfd5030bf28861f930842faa4185f54232be29a437c54486fea4086f50842dea0883f9304437a85a07bd0942bf284417e53d02f8a9905fd4d40b7a92637c514cb7e85a05f94742ef19261dc53486f8a4086f55232ee21865f4410877e84215f15321bea9c437e508c6fca690f794e20bea96837c54cc6fca4215dd4530bf29c817f54cc7be6218df54630bf29e857d530837e8320df54242ee19463795010fda85995f94a40bf29683f9404c3ea4210df95221dea12837d53d06faa6906f90540bfa94217d548c37c86a16fd0941bf29c87de314c6fca518df54e42f7210857f540437c8420cf15121bf29e437e5290f7a8621dfd5310df2a0437e51902fca010fdc4010fb98c63f431042baa6087e54341bf288635f5350afaa2105f14910fc28285bc43102f8a4985e54341ae29a85ed42c86f8a8905f94840beaa043ef32086faa6087b48020beaa2657a50ccb78a890fdd4530bf296617e540c7be65195f95110bea88877d544c7f4a018fe54031fc986417e52842fca9905f54231
  | 1 => 0xd52106fea9195fd4941bea96216f524c3f440105f15332fb98c21f850487daa420fe900409eaa4657c54443f680107e8c110fd184217f53842fea2995794c10beaa641df4390efca620df55031bf2a2437d548caf8a6106f55210bea8c217e500437e81205f94c10bea86877f544c37c87205f94641fd982617c50507daa5a1cf55021bf2a2417d538c7ee6298dfd49109f2a4657d5290efca998efd0441bfaa221f9408c3dea4986f10d42bf2a4657f530427aa9085f54f21fc106217e54106f8a8995f54430bfa9a85f820042e8a2a15f55240beaa0617e50cc6faa3a05f14d42bea94437e548437887a15f54440be2a4617e548c7f240106f55020fda8263f6310c7ba62985f54221bfaa2633f544c6fea5886f50040bc282857e53886fca8997b0ca21bf28c43ec32882faa7185f94b10bea94217d5310afaa9215f94743b7290837c5050ef8a988770c9309faa2615f53486fea9185fd4d41efa9a857d5010efca3995f94910fd286657d548c7f2a1997714d42df2a4217f504cbdca420fe90130bf2a0857e52043f4619077d4d21be29287ee21486fca5187d14542bf28e81df438cafaa9994f95210bf288816e52d0f7882a05f94820dfaa2617d520c6faa3a1dfd4d21bf286437d50d07da84215ed4131fc980617d54c877aa810df54e10bf284437f514c2faa8985f54732be29c417d53086faa2197b4c832bfaa2417e510cb7e8721df15030bfa92817e52087f481185f94a41bfa9e21f431843de41105f94442bf28e61df320cafca9885794e20bea86637f50506faa81077cc631fda0281ee320cafca1997754e20fa98863bf544c77a85a0fd44010bf29865f710842f8a090df54810dfa1683bd42502faa199774c730f7994417d51882fca2105f14d10bfa92637e54883ea8220de94341fd984617e53883f220085f14c10ef190637e5010b7e84a05f94c30fd28683775150bee82a0df94232de21c817e50d0ff62108770cb30bf2a6617e54042faa5a1fb90832fd080217f54087f620886f10a41f6190417e5410fee8320ef90541fb108437a500c6f8a7085f94030f7994437d53102fca120f78c932bda82857e518c37c83a05f946209eaa0417e5090fec8220df14940bf2806579500c6fca5a05f14b10f7212437d50907f281885fd5321beaa2417d50d0af8a9195f54e40f790c437e5190bde64997e50010bf286857e540cafca618fdd4542beaa2437e50102faa8887ec8220beaa663f840082faa720f7d0d43bfa9c417d52103f681905fd5020fc28263de304c3f460185b14930bda82437f54cc2faa8086fd0c43f7994657c53886f8a9985f94230fda82857e51c82faa420df14142be2a021be43906fea6106f95020fda8243ef20082f8a6907e94043f7a14857e520c2faa010df94643f6292637c54086f8a910db14931bfaa
  | 2 => 0xc0106100000000000f42400000020180480401c400bc03014060000100000070130000c010f71181701403000070943f03c550301b01008160070a0140740002c050383102c1601816074080240004c01024000042700c43088140100712c0501c000001b0040105c160b40001c01000030c4090140102447018040180200431004000200002016000000ac0201c08060020000200000000040000a0e861000021d40403000008100e80404808044000000200c0101c0000400044050040000019020c300c1175c130000600c131e4080240e00068008ca0040c0002d0640607c3e02c0200003030240380601c00110030200103c060000601c0006401004000180400070018030480f1254711400010050001203404000000000a00002000234c80c014021a80305006002060007800401000090040006c7900418004b801c030080200800094000040c140000140000c17000000000d0000b02c00be292637e50903e88390de54332bf298817d52cc6f0a090fdd0721de218837c514c2faa921df94c21bf284857c53507ee4290df94a32bfaa2657d54842fca021fbc8421bea8c87de32cc2f8a818df14f20be2a4416
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1540835b53141429e58054cca6c6254c109758c548826d6295130cd9085150a7661d52209e597300427a6015031d318d52107575314542c7d8d548ca5d6395121d654e100432c54d4930dc1475050acc624c730da181521065c6354910ad1854210b2c54d49318f992508865d63d5220ced53504c65d63d48109dd95310c65c6354b109758f528426f6254e40ce150504867a6095121cbd53524c63f64549109ed815190a7b6054d218f59252cc66c65509219d185534826e62150319b98b53c435b31540319e582534827a60d4f21ce552300835632145308f99252cc75853d41428f191538863f6454d21ae59210042b96010f42ae5804350a796094f21cd153214863e64d4c21bad89300832d540c821d9148514c26c6254e40cdd50514c279650c0108f59353c875432145309e195404c27b6054643bc185300c23d64d4f209b98a544c2ad62d0e43ab588415025e63d52209ed9510043d3314c2109dd85544c2796095121dccc4504c6f0614c320e990841c877351d41429798c540423d6590841cb553320827561d52209b58854c42776155120ce150504c74c528c5319bd89534863f64547309bd95320cb6b6054841b318d210865e6514d218f99454486b964083109e980530431d5410e329bd89544c26d62951319ed8152d0e7a6015321ab58b4310f39548c210c719153882796014d41cb90d521067960952319dd95100432c54909218fd9540102756114c208fd954210a6c62551309d58753c83585314142dc1445050bc8324c02097d8d52d035953c82209ed81544836960d4930d5185530425f635511097d95300c23e6414a109ed81534423e64d4f21d654f200431f6454e208f596540825f63551328fd954310eb46150b419ed95401031c6454c109e98253c867965080109e98054cca796015031dc145404c23d64d4c209bd89544c75753d4542cbd50524c67561153209e1815190b2c43548419e58354ccb2c5414931b3189314c36452d4530ce153504c6b56110c419e580540ca7860544329bd8954442776154d208f59052c42b96010e408f19151cc23e64d4e10c7d50534866e62153108f19153482766114c20ce580544c33b54d41219e18152d0e5e63d4a108f590520435453145429e582534867561d50309ed81544c72f5414930d6d4f50486e86050b329e580538871f6454c109b58a54cc71c548c9309e58353c86e46150b329b58b53c426f6254d10cb553320863d64948329798c548826d650c8208f99252cc2786054d219ed81528c67661d53329e980530863d64942218f191510ca7561d53328f994544c7a542d072197d8d524427461551308f593528423d6494d219b594320863e64d4f108f99052043585314121d3d89530437051901308f992500426e62953319dd95411065f63548419d594310436b6054b43
  | 1 => 0x863f6454c10dc147304c25d6594c10d68c9500c74d62d4d429e983540c63f64544329e596400423e6414c20b3189310c67960153218f19151c827a6015030ab58841d032d5290841bc185300823e65d0941d554f310425d6510c329798e544876b5214131bc58420042796015331d514f5150a7b6055132cdd53514c27661951309b189544c73a4314142d654d100425f6354b10dc580514c23e6414b10d654d400423d6494010cb548421063c6454e209e580530866c6255110ce50950d075953cc0109bd954210ad963880209b988540423d6494b309718d521073554d0421d314e424873b42543419bd8953042b46448421cd90c5150a6d6215010e310d420cb1f54d4d21da18152d0e776154d10d3d48324c31c5414d21ce10c5050b39544c0209dd95210863d6414a10ce15350487595308010cd54441d036b52d41319e18152106cd62d0c32cb551210867960d52219ed81544876752145308f994544c27a6094e429d98753c823e6414c219e1815190e3e64150218f191534425e63d5221cd153514c2d960cc8329ed95300c25e639402097d954310e786054a31b6583328cad8604c730b618d404c33443145429e596100423d65950219b596420ca3d64d4e10ae580439067761551219b98b538433b5414121cb55032082cf6350832d3d89538835b53141219d584540cb3954d00209b588548c73854901309e582544c65d63150109e59630082796094e42bc58640042b964080108fd9151c823e6495130cb553328cb5b53d4142d3d8d521065c63551219758c520433954c4210ab592320ca3e64951319ed81510ca3d6414e10cb553210866f65480209e98354cca7461551329e982548c74c6254c10ad185425063f6454d209bd95210876852141319e181544872d62151219b988540876461548419798c530423d64d4c219d586544c2766115032ae583411072d52d0441d64c5500c63f6454e218f990538423f6454d109ed81521065e6314810d5147314c3d331cc0109e583540c6f0604c4319758f548863e64d4f209e582544425e6394d218f590530867b60549109798f5404276611532097d8d544826d6215230cb149425026e62152308f590524426d62d4e109e181544ca7860551319e195304423e6494d219e980535076752d4530b6580438ca7a658c1109e980540cb4c5388521cbd53524c339544c210ae19130082776155132d614f504866d6215031bc185308423e6415020d6181530434c53509219b988548c6e860508328f992520cae56210721ae580431067a60d52218fd95411067a60153319e982534876852d4131d354c328827a60951319718d54442b86050b40b9185420cab960d0641ad18542d027a6014e218f590530823e64d4c20ced50504c66f6254d20c715353486d96010c32cb549411066d6295132ce18
  | 2 => 0x6000002207001984810000440005000145e07000380205042c41608000002004028243c3302840021700000048008014005089454000001814008f008002a003307800001b00798000000000003a03c02060b83c0a0001800001100808002d018a40c52118140c240e00000bf100241800000280600159848608008001c00028000000008c018000081008021c030001e00180a62a0180814084680000010104c4e000001c06300589404030218c0056128000c0001834060501070360000800000201b1c021200000000304dcc0002028028202338000000418180015439f51a00050200c08011ac000100898060b0b800020f002480211000145a160002f2c5414930dcd445050a5e63d48108f191534863d64d4f10c7150324c25c6354b408f191530425f654c832cd185540863e64149109e59440082b8644c3209758e500825d63943219758f540425e63943219d185544833454145309718d544826f6254e4197d8d54486f1600c6109b189534423e64951218f191524427b6548020c7d4c4350a756510421d654c300423f6454e20bc185304426e62951318f99352842e960cc820d60c9500c65f654c4319d987540c26c6254e41ad18542503595390010b918542c
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2000082280e000020009a00000300020004027001295da4210721ca0c628a809860c641895304322318c2a9083521c93154031d1086302841962452185425029838a84a8683a110c6150832d806430a6010651535864004298b808628a85895895110740a4ae221aa420e5165cc730042c4b8086a10654a5c04354841c52a4b068220e48631815210722310c2a98210e1d9544c020c1aa831a4210f09540c93008318aa0c2984219454d6108010c32c8a9c2008688640c93008318aa0c298041865915308010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x4000000a818010c6150832a0886550324c020e01540c8614c020
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 632
  | 4 => 473
  | 3 => 29
  | 2 => 3
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
  | 5 => 2*((h/280+packedAt s5K5 (17064+(h % 280)*10) 10) % 632)
  | 4 => 2*((h/227+packedAt s5K4 (17974+(h % 227)*9) 9) % 473)
  | 3 => 2*((h/37+packedAt s5K3 (1421+(h % 37)*5) 5) % 29)
  | 2 => 2*((h/15+packedAt s5K2 (180+(h % 15)*2) 2) % 3)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x3f01ffffe03ffff03f03f03ffff83ffd8c7e3f
  | 1 => 0x3fffffffffc07fffc003ffffffffc0fe0fffc7
  | 2 => 0xc001f80ffffffffffffc003f01fffffff063ff
  | 3 => 0xfffe000fffff80ffffffffc001ffff03ff83f8
  | 4 => 0xfffffff0000000fffffffffffe000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x915548aa238912b00ba0b90baa5a39658c2e1b
  | 1 => 0x220c514444872452c04155554cae48aa05d6c5
  | 2 => 0xb0a822668912486555640426613492d2b0616e
  | 3 => 0x431458912240e99a68a698089c32c215e83b0
  | 4 => 0x38c1860e1c3870ee38f38e38f00430c3eb7800
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfc88e080fc88e080fc88e080fc88e080fc88e080fc88e080fc88e080fc88e080fc88e080fc88e080fc88e080fc88e080fc88e080fc88e080fc88e080fc88e080, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40982
namespace PEqualNP.Outside.L_meta_40982
open PEqualNP.Outside.L_meta_40982.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa282140040000089040027fd5001fd3100ff14009fe5200ff04001fd21007f88401ff21007f4c009ff53007fc8003fc40007f90801fe41007f8c807fc4200ff94005fe53007f08405fe43027f54809fc5201ff10409fd5100ff08007ff41017f14c03fe2000ff90003fc30017fcc409ff51007f50801fd41017fcc805fc43007f44009fd50007fc4007fc5400ff84009fe51007f8c401fd4001ffd0c01fd20027fd4809fc51027fd4001fd4301ffd0009fd5401ffd0805fc3101ff95005fc32007f4c805ff30027f54c03fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x926000bf98a31007de4310803fd63c84057fb1a8627ff881310e7f8a39080ffe5450001fe98a2002ff4c930007fec0a180bf4318c401feb064212ffd4f20047f84388087fe2088443ff3044205ff18d10047f8c91880bbe4350c03fea022040ff14543047f8cb1086bff5008401f7908421fff1052101ff882a08affc428c4057f31a8401ff9413006ffe8690003fe3144001ff10a2008ff18231005fec4a0097fc53c8403fa0822000ff50910017faa7190fffc1050c03fea06200fff0ca3200ffc8088002fd64c8065ffa948200ff98540007fcc4a0043fe43c8047fe214423cff9824200ffea0a005ffe2008407fe2a28400ff58632005f8c4a080fbf429087dffa9c8400fec4110007fec0a080afc635001fff2164040ff995431effe61210cffc204c86dff284643bbfd9542137fe8190802ff604841fff2164232ff5424107ffec99080fff4190441ff28a4228ff10931015fcc519003fc2144045fe21c4200ef5923218ffe61208a7ff524c4097f32a6000bf18543187fc2120803fd604c403ff1028031ff98e4107ff8c990002bd648c81dfea9a4001bf18242015f8c61080ffc40904075f3204225ffccb21005fac81089ffe104c471fea8c6435ffd5132167fea518833fc3248005ff9846214ff94930005fac01080ffc42508017fb1a2003ff10d4200ffca09006fff5288401feb226216ff9954014ffaa09880bfb304c0097f32c8223ffd022101ff887208efff52508057e31c4224ff103211f7f8a32105bff5250005fea1a620fff19720107feca9084bfd54c8005ff1926403ffd0a4200dfcc12080bfc434c401fea1c420affd0f1001fe882a0802ff604c405ef98c620fff94a320a7faa498012fe6548059fea84621bff542210bffc201080afd638c803fea82800fff10821007fa829800ffd4350805fea1c6221ff842211e7fc612106bff5208401fe90a6000ff582211cffc20a1012fc658c4097f32a4230ff8c24101ffc80a180fff5450455ff084620eff9952001ff884a0077fc2048441ffaa24234ff991320e7fccb90843ff32c80097e32a4238bfd9632007f8c488003fd3248001ffb224200ff8c941005fec89906bfd5008453feaa26224ff04321107fcca9080bfc438c451ffa0a6202ff0c13207ffecb19007fa10c4021fe29e4035ffd4132007fc649082ffd53c407bff29c8406ffd0d10005fec91083ffc64c841dff2924028ff19131007fa861080afe6350403fe2826003bf5924104ff86588006fe6048405ee1926420bf58a21107f8a4908b7fc2050401ff20e4202ff0c532007fa639080ffd43500017eb262001ff94310007fac8990afff418c403ffa064001ff84140007fa8590803fe624c447ffa0c4218ff10c21047f8c52080bdf328c807ffa148203ffd054207ff8c79000efc640841ffe30e4000ff98530
  | 1 => 0x3fc2090407ffa028600ffd8943007f8c4a080fff545082dfeb2a8000bf58f10017d8651905bfe5150073ff302840fffd8242017fc651880eff64504057fb1a623effd424202ff8a688003fd6388407ffaa28036ff9023201fd884a100bdf308c877fe32a8401ff1031004ffcc7880fffc6050c05ffa1a6008ff0c64112ffca790802ff6408401ff20a4008ff18b10017fc6498807fe404c049ff1864201ffd0110167fea918812fc65c8413ff9962003ff10a41007fac48800bfc308c417ff32e2000ff50a32005fec299003fe4244001feb246400bf58a31005f8c4a00cffc504c8057e31a2003bf19321007fa829080efe6408405fe182623cff88242007fc65108e7fc205081fffb2e4004bf197100bffcc010877fe6048403ff986400fffc872001ffaa8a18bffd5250433fa2084203bf59242007fac520803fc214c0377f3084202bf98e21007fa629006bff5408403fea026030ff0c241047f8a388007fc404406bffb2a6401bfd914011ffcc9108abfc208c443fe104423bff149421dffacaa1003fe2148005ef29a602dff141410fffcc890873ff53c840bff31a202eff98d4101fde8521017ff3244011ff18e2001ff0431014ff8a49883fff65c841ffe2904203ff95241005fec49883ffc4290801ff18a400fff19642017fe62990d3fc644c807fe202861dff1412100ffc809000ffb40500017eb224202ff0c53100df8c110823fe41c4069fe20a643eff5424210ff861108e7fc3050805fe29a8635ff54532007fc64a000bdc328c41df7292403bffd4142005fec0a1047ff42c8001dfb22620fff080210dff8a51081ffc5144059fe2946225ff90f21007fec6a10effd5050811fe18c6208ff0c621007f842900ebfc3150851ff2a26200ff58f10007fac6a10e7fe2050803fe082202cff9963107ffec919007fc2050047ff2a44200bf587200a7fcca980fbff5290865ffa848203af99232025f8caa0002ff648c803fc2028001ff8c320177fe62a081bfc6444001efb1a4208ffd82210f7fe62908a7ff504c401feb0c8410ff94f2000ffa809000efe64c8057ff2a46210ff98f201c7faa51900bdc4350c6bfe2926403ffd064201f7882a000ffe5450867ff1026408ffd8241047fecb20803fd31c401df6a924002fd0c531047f86210803fd639042ffe1804201ff90310047f8cb88057fc3150007fea1c8403ff50e41187fc4120802fc6244011ff10e2020ffd4521017fe64a1803fe414402dfe2928020ff19521107faa2908bffd515045fffa8a823cff8424200ff860a000ffc4390807fba0c821cff55321007fa85880bffc525045fff28a822cffd423100fe8218800bfe308c437ffa84422aff88231017fe8719067fe5408401ff30c6402ff14d31005fcc32100fef4250815ff3262035ff94532017faa698047fc54c8005fe1
  | 2 => 0x10017fe60a183ffc639084dfba0e4200ffd8142047f8c81080afe634801dbe32a4002ff14d300b7faa4a002fff53c4065ffa8c822aff98231017fe6298897fc43c8453fea8a621cff543210bff8a010812fe65c84017fb264201ffc8110077faa8900a7fc654c4017f3148201ffd01300dffea310803fd648843fffa1a4202ffcc631007fa8790802fd6348407ffa1a8236ff10232007fac12083fff63c8445ff98c4208ff10621015f8c690063ff3108403fe282803affcc542067fcc690093fe10c840dfe2a22003ffd094304ffc8788003f46150841fea9a4229ffd4531005fec710823fc41904037e3004240ffd9543017fe6498003be4150459fea8c6200ffd85300b5fecaa0006fc6048411ffb046232bfd964103ffea6880dfff408c819fe31a4003fd106410a7f8a29803ffc42c80017fb1a803cff0c2420d7faa210802ef624c4037fb028002bf98f10067f8a690003bf644c011fe314621bff54621025f8caa0807fc404c037ffaa44202fdcc5311dffea2a10effd5150805fea9a6403fb10a42165fecb18802ff64480017eb122002ff0c93207ffc8519003f52108401ef18a6202ff8c530007fec8988d7fd524c801ff20a6000bf18b1000df8c0a1007ff404802bff98a8026ffd072102ffc86880cffe504c851fe20a6204bf1942101dfec8a1097fe63c8453ffaa26208ff94641017fca6a1823ff6308435ffa884202bf18f200057ec89800bff328c801ffb224000ff50f20007fac290002fd648c817feaa62002ffd4d4300df8c119003bd42504057e31c8232bf5964107ff8412100bfd314c0097f32e2008ff106311c7f8a319007de304c007fe20a8408ff94621107fca4908bbfc325045ffea9a8200bf9872000ff0609804bff52c80097e32a4001ff04130015fcc688003ff6048453ff28a6200bf58f20007fc849000afe6348419ff9924004bf9962100ffaa190097ff30c843bff2824202f710e32005fec0990b7fe505043dfe1924201ff1012001dfcc89000ffc5450c017fb0a602fff94941077f8a2900ebfc63508057f31a8000ff18943077f8ca90043fc43c8011ff28c6202ef10d43025fcca9881ffd5444011fe2084200ff4c9210ddfecb10837fe644806dfe0846400bf18931005fec0a18f7fc31908057eb1c6208ffd923100ffc2190003fd648c46bff2926409ff14f1001ff882a003fff63c80017eb1e4220ff5492100dfcc38800fff5490403fc102400fff8c821007fa8490002fd6090801ffb226401bf9813101df8c888003fe214c003ffa062000ff5093013ff84098802ff63484357f30c4208ff944210d7faca10803bd6408401ff2162026ff15321007fa64a0847ff41c804dffa164203ff95242017fc86a18fafd659086bffa8a6404bf9954300ff8209000efe64c4001ff1948229ff59531007fac6a00c
  | 3 => 0xea9a8000ff50d1000fb86098002fd6190807ffa1a8032ff94a41005f8c2990effd5350807fea0a8000ffd8543007fec89809ffe504c4077e324640fff18f211d7f864a106ffd5388419ff29a4002ff94e32197fccb2083ffc52c844bfe18e4202bf98c21127f86190802fd6308401fe994823cff1424217ff8a2a0812fe6550405ff1846422ff0ca21025fcca10883fc514840bfe21a202aff94231005f8c29800bef328c801df20a8003bf992311cffca0a1006ff634c03bfe0824201bf18241025f8caa18b7fc1050477ffb2a8400ff98532017d86499002ff644c07dff32c8400ef5094003ff8ca88002df6350805fe9926201ff4c32001ff884a18cffe404c805ffa9a6001bf181320d7faa610803fd418c401ffb128000ffd813107ffec39004bfe65c8003ff9862000ffd8532097fea990003ff634841fff1964001fd8431000ffc6090023fc6388407ff20a820fff0c8211bff8a919003ff21c407bff31c8400ff59110007fa651085ffe500847bff98c8403af19121007fa821082bff42c4005ff21a6015ff0c94014ffca498893fe20c8401feb1c842fbfd9541017fa651880bff538c811ffb148212ff5972007ff8c919073ff50c84097e32c823bff5494200ffca0a0023fc6308403fe1064040ff5414300dfec090037fc5448001feb004232ff54a411fffc20a181ffe6544005ee18c641cbfd97210dffca510803fe6150801fea0a6200ff18542167fca5188fbff5190801ffb126000bfd854200ffe60880fbfd5190801fe98a423bff949420effc8090802fc6250c65fea8c8203bf99131005fac890007f61044011fe32c6202ff0c543077fea690007ff2048001fe9904201ef90140007fe4288023fc6488461fe2848201bf98132007fa831080efc64c8039ffa964224ff9832114ffaa498803ff635047ffe102860fff14b2018ffe632080bfc4350c01feb224000bfd8930005d8c498853fd544c0056e31a4203ff5094100ff86190003fe2148407ffa0a8600ff5092100df8c0a1802ff625041fff290421bff54a21047fec910843fc31c8013ff29e203eff94642167faa51880bf7318c419ff21a4003ff106420b7fea2a0003fd6408401ff2126000ff5823200df8c0988effe5150871feb2c6401ff8c3100b7fca4a009ffc504c40dffa12201abfd94211f7facb2103ffc5290843fe2844200ff18540005fec2a0047fe54c80017eb046416ff54540007fac4a080fbc4190801feb22423ebfd964207ff88590803fd2108401feb04840fffd93201d77c86a10e3fd548c8093e32a400fff18232017fc60a1803fd2150055fe2846208ffd8e411cff8a0a10cbfc52904017fb12861bbf59621057f8a98806bfd520840bff29a2002ffd0d32017f8a7190b3ff518c403ff1064001ffc831000ffea190002ff63504097e32e4001ff8c1
  | 4 => 0x837fc6448003ff0826001ffd431001ffe8721003fd318840dff2a2200effd4920007fac2a1023fe4108401fea126203bfd8942137f88390807f81044071fea846435ff5513201fbe86a189ffe404c4297fb2a6000ef9923206ff884900abfe408c411fe3044208ff8c62101ffc82a0002fd60884017fb122002ff10d30047fec71080efc6448401fea144208ffd90210b77aa8a0012fc6588401feb1a401cff94721007fac990823ff628c403fea824008ffd93101b7fc2119003be4290443ff2044201ff8831009ffe8298006fe6090807ff2028408ff88421015fcc7208fffe6050c01fe30a4000ff58a31005f8c290073fd65c844dfa20e4201bfd851000ffe208800bfc534c803f61064010ffcc720017f88719007ff5044001fea1a4037ffd0632007fa62a000fbf4050807feaa28202ffcc932187fcc120883fd5448407ff2028212ffd472000ffc6098023fe3108401ff3126000ff5082101ffe86a10bffc65504537fb2a623cff94242007fac299003fe315002fff200420cff10d2000ffc209009ffe604c401df2128400ff98b10015fec49904bfd51c8069ffa026403ff5094010ffca11082efd65c4001ff10a8040ff14943007fec4a083ffc6090811fe3284208ff1931001f7e84a08bfff6550401f710a4201ff90140015fcc790807fe2044005fe182860fffd863201df8c89880eff615041fff2948401ffcc13007ffec119003fc62500017f30c6404bf995421aff8a299003bc644c007ff2a2860bbfd9710007fc849902bfc42c4007ffa1c822eff14d410eff8c090803ed210844dff2a64200bfd8f20025f8ca88003fc21500017fb1e4212bfd9720007fe429801f7c654401bffa0a400bffd4b10007fac69081ffd6544005ffa1a621eff14d210e7fea99083fff60c84017eb222011ff10720037fe828800bff308c84dff3264201ef1014001ffe80a0803ff604c807ffaa48433ff10132015b8c6a103ffc20c8401ff3128204bf995100fffe809080aff6450c03fea862000ff5093200dfec098103ff5250c1fff1964203af191300b7f8caa0003f62108427fe2a2603fff88143207fea0a1803fd6048401fea1e2006ff1091009ffe849800bfd538c411ffb2e2019ffd0c21007fc8490872fe620843bfe2024202ffd0e31007fcc518807fe10c4047ffa1c4207ffd4910165facb188c7fc3290407fe202820bff5971017dfacaa0807ff3048061ff2848209ff10f10007fc829080bfc324c407ff2128200f78c930097fca39002bff41c403dff9924204bf99532007fac6880ebfe6350801ff90a4000ef99021205fecaa1806fc6050405fea9a6200ffd8910007f8c29800bfe534c05dff9928200ff4c9400f7fcc6908cffc104c801ff18a4201ff54110017f86518802fd608c41bffa124001fb88320015fcc790007fe104402df
  | 5 => 0x8320007fac4a180efe648c8077f3226402ff94d3207ff8a51900bff3150c01f7b126201ff08120177fca6a080efc644c0017bb0a8400bf58a41005fec6a10bbff3050405fe18c6413ff951300f7fe609081ff55144003ffa826008ff18f10127f8a1908d3ff424c80fff28a2008ff18e411d7fe64a10b7fc605047dfea948431ffcca41007fa839083ffc6190839fea964200ff1853215ffe8118803fd61c80017eb226401ff4c31001ffe80a1003fe4288411ffb2c6237ff95232097faa790003ff2148419fe18a400fff0cb2017ffacaa0803fe424c401fbb0a8432ff54e4101ffc84a100fbf4250001ff2146208ff1802101fee82a082ff651c4043fe2044215ff14d40047f8a320863fc5308417ffaa62027ff1013100ffca190007fc30480057e31a4233ff981321cff8c0a108bff328841ffe3064200ff4c42101ff882a1807fe204c0037f3064203ffd09410fffe8490807fd3044033ffa004200f78c932017fc6099003fd32c8011fe084822aff1023119ff8c099002ff62c4001ff1962003ff90242005fec6900e3ff508c827fe3226003ff90940005fec990006ff6044001fb90a420dff95120017fa8719007ff4050011fe18e2036ff8823216ffcc0a08b7fe305042bff9928002ffd4d3214ff8a29880bef324c8017fb262001ff08310017fc869903ffe420845fffa9a8200ffd8d200b7fecaa000ffc5450401ff3122040ff9454303ffea888003fe6148007fea148201bfd89200f7fca690823fc518c427fe2126002bf18d41047f8a31089ffc104c437ff32c4208ffd802103ffeca88007ff5048003fe9062018ffcc8210bff880108effc51508097f32c6200ffd8d4000dfcc110807fe2048001ff1922000ff189311f7faa72101ff65144001ffb126201ff1014001df8c918806fd60c40017f3162008ff0423112ffe639083ffe52c80017eb1c820fffd8e421cff820a1006fc608c4097f32a8001ff08110005fec2a183ffc658c815ff2a6200bff14b10007fa839001bfe6444003fe1862001ff54130017fc8719023fe418c4075e3226214ffd9530207f8caa1803fe414c431f61904202f7cc131025f8cb1903ffc3290811ffb2c4208ff14421117fcc710803fd624c001fe90e4003efd0241025f8cb21053ff524c0077e3224001ff481100e7fea39080bdf314c041ffa9a4216ff14540024f8ca8801ffc5244007ffaa28608ff90621005fac688023fc1008425fea964003ff902410aff8c6a001efd65440077e3262015ff98d401adfaca99002bf6448401feb0a6022fb0ca21105faca9083ffc428c871ffa94641eff90d21007fcc321003dc6348403fe1822002ff8c53100ff820a0017fc3144007ff21a8204bf19532007fa851880bfd434c003fe2864003bf98a42005fac690003fd6050c11ffb162000bf5913100dfcc0a0
  | 6 => 0x3fba084202ff0c94316ffc40a0803fc6150c7fff2828640bf5954300ff8a1880a3fe644c43bff1024219ff15021007fa42880d7ff524c805ffa9c6200bf583210c7fcc6108e7fe30508077f3226034ff10932007f8c4980a3fc544c429feb2a6000ff5813203ffaa48800bfc434c8017fb226203bf986410d7fcca1088bef3288431ff2984200ffd852004ffe6388003fe21c80057e31c841cff547210bffc6010803fd6150c017eb162000fb18931017fea6988affc548c4057f30c6200bf5932111ff8a910823ff63c4003ff1828003ef10d42007fac0a1003fd624c403ff2064002ff0c23206ff8829000bdc314c42bff29a8000ff50b20005fec0a08f7fc5390835ffa984200ff8c7201affaa099003bf6448403fe282200fffd86420b5facaa006fff5388405fea1a6402ff90d3100778c89880fff4090877ffa9a8426ffd0f210a5faca98072fd65c8407fe2128220ff595210fff8849080ffe43508717eb2c6433ff84132197facb20863ef320841ffe1964200f7d8d4217ffea4a0803ff61508017e312600ebfd9520167faa91888bfe438845ffea828220ffd492107ff8439004bee52c8007feaa4820bffd4710077fca29000bfe438c401feb22601abf594210f7f8869082ffd51c4007dfa0a8419ff99021005fac71080ffc5450005ff1926014ffd5130105feca9087fff414846dff3046403ff50d41005fac12080fff4150441fea824205ffcc510007fa869080afc63c402dffa9a8002ffcc931007fac6a080efc644c81dffb2a4001ff5032000fdc4090073fd53c8469ffa0a6401bf98142207faa4a18e3ff548c807fe2048407ffd451016ffc20a0853fc524c03ffe322423dffcca42017fe6099002fd644c01dffaa24029bf59531127fca190863fe43084017eb246200ff98a4101ff886a084bed52c80037f300421bff5522100ff44190003fd6250011fe20e2003bf9932100ff84098002fe624400ffea8a2003ff90d40007fec888012fc6550807ff2148227ff1813100dfcc119003fd62c401ffe1046437ffd0a321bfbe8719006fe608c4015fb22620fff94b2114ffcca98807fd3048007feaa28400bfd91210a7baa69807ffc54484057fb1a643fff1414318ff8a720807fc304c05fff32a8211ff993200dffacb10806fe6050c69fe2a26403ffd0241047fca388003fd32c84097f32e401dff8c12101dfcc9108eefd65508037f316403cff04242015f8c79084afd65c800f7fb2a2000ff593201affcca990e3fe658c801ff1924040ff54543017b8649800efe6444017faa8e2002ff0c530047f821108037f6544007fe2028406ff10510047feca108a3ff404c4097f32c6422ff14e211bffcc9190c7be4390423ffa1e400eff14920017f8a71886bfd5408481ffa8a8600ffd8540007fcc2a18ebfc5350807feaa28001bf5
  | 7 => 0xb80000207c0004e000024060110380000000a0161701900a14a01c8280502e0180f0d3022000a4814084054008270021182c0040002cc0601e0040ac1080a026008000010181804d002014018050020a40040400002c1a83a846008130030141180280b800006014ca8070100000600c00005400025064000179380022bc0000a00e0080400001200c058710001b00100000000c0481900a118000a00ab590000fa00c0200003a0763543802b6140001e8630260080e0260080001981506e000000020240140080902a00c6701f5cc004028120240300004006000c0204d00a0984b8340000080480300c940042081b8330b68001107325180a12401c039560300240380203e05c350990101000500b1f203cc2833000004128000040040002709e038070070000002f8040000740f8480600e80084d00a0005e000b50068000322ba000100700342880981103211829009048078008340021740080d07800055003fd41480017e30a8034ff95132007fcc4a1803fd21480077f3224202ffcc131007fac61083bfd524800ffea9a2036ff1423201ff8a9210bbfc31504077e3244203ff10d4001ffca8a080fbc42904013fb2a4005ff0c910005f8c2a1003fd31c8001ff30e4003ff90e41007fe43108b7fc30504057f31c840fff1972114ffeca98807fc40c8005ff98a6001ff94110017fca6988ebfe5350833ffa084200ff581410a7f8ca98077fc304843dfe18a4203ef95140007b8c6a1003fd32c4045ff9844240ff949431d7fe60a100ffe4390805ffa1a8604bf9964200ff8a090002fd618c8037e3064203ffd054001f7882a0802ff648c449ff2064200ef19121147fe84988b3fd658c401ff18e4200ff58f201adfeca99083ff5048417ff2962002ffcc6320f7f8c690803ff6344007fe2a48214ff545300fffca890803dd314c01d7eb2a4000bf592210a7fea29802ffd52c4025fe28e4021ff8c221005bec69088fff42884057fb0a6204bf1953118ffca720803fd64c4031ff9804200ff58540007fa838800bfe304c407de21c8200bf58e42047f8c12080fbf4190403ff9828003ffd0942077faca90003fd608c457ffa146240ff5954300ff821900bfff5050405ff29c6200ff4c91000fd84090033ff3148001fe90e200fff18632006feca900effe6550871ffa8c6400bfd8f1007ffe421080afc63508013fb2a2000fec81200057ac8108dffc418c801fb90c4202ffcca31005fec6108e3fe518c827fe20a6007ff949100cffe841084ffe644c06bfe32a640fffd9642007bc6518803ff21500017fb0a401dff84121197fea72080bfd5350c07ffa128000bfd9110007fc839000fbc4250829ff28a6008ff19641177f8c6a083bfd5148057ff3246204bf1953001ffaa92108bfe5388401fea0a200effd4520005e8c2a10d7fd654c83
  | 8 => 0x8f0003d2058278180000d8000080e60084e80d05ee480b00e0380ec3f010000000fe8dc040028001190100009180d136004060030040a80389a0060000002b0060080402603a03000000002004060010bc00c008441000000001d0020480182400e0000083202c05c02004156014000270220a018802072928000020980000001400ecac0a80c01801801802180000101db05801c2d80e018010080e700201400000000008198250020004819900607403835020028b68350141740201b024024260041ff014518000580440d0079340342582f14c2140201e00205000806078000010010040342780001601c148683480a002976000038560010001f00a051134004000010cc004040030121040c80c00201c020000060182001e0040180c8870440161500507e02c00002002000060020121440e05a0aa334170020000000705c01200002801000220028420020001980200c0941e80000e028038000d0000258600180241282b0040481410c064050038010022d01580502e1400b0e701201405814066000990040002ac0400a03c0242a0000000080d80005e0380f03a07e0d83100e1880303
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc75d8d42006bc31d9121014fc765053101ebf605094001ebc6490720004fd7558910006bf705923201cfd70d8940006dd71d8d42006f753d854218ebd30d9131046be415923100cfc7648510005df735093207cfc7518940004ff7458d21044ff75d8f10066de63d8d20367af3299232006f673d8542136f474d854201cfc74d8d21006bc75d913002ddc7348510006dc50d8d4207cff7598a31006f763d8542004ff7159120247e952c8120024fc75d894100df87050510004ff7559132004fd768c910044ff7518520046f671d931018f9e4358e41006be65d9131004fd70d8532024fe75d912001dbe748ca41024fc75d8143014fc73d81410079c6418d212bebd10d913007ebc6450b20006ed54d8931006f4321854200cfe7158b10004fd75d85200047f7558d20004fd7558d101cef850d8142044fe7690b10024fc75d8540006dc70d8d21006ef62989310069f64d8d2101cfe7458910007ae6290a41004ff7058d2106ebc41d912015ebf42592312adbe76d9130046ee61c842107cfe72d854300cfc764c920004ff7650f10006ed64d8931116ec73d8931154ff7358d100067e64d9510364ff7650a320c6ee531893101ebc6450930004fd75d8d1000df870485100067f658852001dbc744c540006ee70d89310069c64d8d21006f7715913200cfe70d8c21024fe75189311b6fa3058232044fe7198a41044fc7198a410cdbc7448421024fe75d8931004ff75d8142005bd74c8540004fd75d8910004fd73189410de7c6588510044ff7358c21006ef51d893100cff76582321d79f7418d420067f6558d2026e7e10d9520046dc6358e411e4fd70d912012edf3158f21006ed621894000dbe70509400757e759852001cfc74d81211bedd54d8d42024fc75d8940004fd73d8941006de10d8d2126e7d70d952007fe652c8621004ff75d85200beed2018910024fc7558a31136f442d8542006ef62885400c4ec7258c21006ed701893100cfe76d81210047f7558021024fe7559120006be2059232005f47158930004fe7650d21006be6458232004fe768c540006bf64085301d6df32d8d4218edf3058e412367f71d95100c5dc73484210f6ed3258a31006f62018542006ed65d8931006bd6450a3101cff765092000dfa7088520005df7350a21024fe75d8943014fe731854000cfc7158b10154fd70d8d10046fb1058241044ff70d891001cff7650a21004fe7650930006df51d8d4201ebe6450a32005bd748cb101067c6548520366bd6399232006dc50d8d21006dd5358e41115ef724c621006ed7518931004fd74d853000cfc7058c2108ebc4359320006df638ca21006df63d854201cfe7458232006bf75d912108ebf415932012ef631d8532044fe7158e41004fd75d8f21004ff7458d10046bd7418b10006bf70d91310ecfd76c8710
  | 1 => 0xc9302bebc30d9130004fd75d8931016dc634c521006f761c8530005f47150921006be72d91300067f654c920004ff75d89400067c31d951001cfe74d8910024fe75d9310006f76198540016df604c530006bd6559021117cc31d8931046f7101854000cfc705913101cfc76505210c6ec3258c21116ef32d8e21136f441593210247c7558d20024fc75d9110006bd6519131006ef629894001ebf609054036fcc4218d42006df638c521006f765d8542006ee7518931006f77158d20044ff75d8b1018ebf6490531024fe75d8141004fd75d8d2112edc31d8f211ecfd73d9132007af62509401ae7c654c91018ebe31d9131014fe76d8d42005df7359121006dc7359110036bc6459110004ff735822107efb20580211a6bc645913200cfe705863211dbc744c621006f4615814201cfc74d853207ef860583212bebe50d91300ceb4421854226e7e70d9520006bc7159232055fb70585400067c755911007cfe72d9310014fc73d91200057f7558540004fe7690520005f77150821004ff7558021004fc7650530006be6599021014fe735911000dfa76c8120046bc3159021006f7619852031fe620484211d6be7359232004fd72d9231005dd7398542005bd740851007ef8205824200cfc7059321006ec6250531006df70d8d210ecfd76887200079f6418d21006df63905212367c20d951007cfe769072026e7f70d9520004fd7318910044fe7198a31004ff7458910024fe7558b100cef64318542004fd7558e41004ff70586420aedc6358d4000cfc7058642116ed32d8931047b441590212367d10d9510024fc75d85300079f648c930044fc74d8b10005df734853018fb431d91312367d70d95100c6de5358c21006ec54189310067d73d951007eef731893101cfe741852007ebc2059021005bf7448421006bc20d912100cfd72d8d201bedf43d9232136f443d854207cfc7259231006dd74d8d21006bd6290a41006df42d8d21006f5651854201ebc6490910044fc7650b1028ef531d853001cfe7418930006ec50d8931016de638c92001cfc7458a31006bc6290540134fd74d9321004ff705922114d7c7558131044fe71d8f10024fe7558d10046be74d8c21006f465185422d6bc31d913000ff271c4110016dc638c5200079f7350940006bf53590210c6ed4318931146bf42d9131046f970d931035edc4318943006ed501893107ebc32592320febc645912100cfe7650920007bb7050940004ff75589100067f32d9520014fe73582420ceed421894119cfd73d8f20005bf74485100feed4258a41004fd73d931022ef710d8540004fd72d9130014fe7318542024fc755931007eee4218943006bf7458e21006bf74591210067f650851009dbc745853001ebc6490530006df635092107cff75d93210ecff7058910035bc7448510006d
  | 2 => 0x6ed74d893113edd3058f102bf9e30d9130004fd74d8132004fd7559132046f441d9021006bd52d9121366bc43d89431fcff7059130005ec724c520015dc7350531046ef6298a412c5df735913000cfc7059231006f461d8142117e431d8931186bf40d9110006bc6458d21006ef6290531005bd748c92107cff7690b1000cfe70d854307cfc73d93200cebc4059021005df7350a31005ef725913126e7d30d9520006de6518d4200dfa72c8120046f71098720006ef62c851001cfd72d8d42004fc765052000efa76c4110004fd75d85320067f655092000dbe7690540006ef5018931137b442d854201cfd73d85430c6f53118532024fe75189301de7c6550910005bf7458530006bf644c5210067c64d9510024fe7559221004fd73d8121006bd52d9130004fd71d9130006ef42d8931006d763d8542046f451185420febc40d9121006bc30590212367c30d95100c7e7311893101cfe7458f210067f43d95100067c65d8910146bc644c52107eec32d8c21006f741d85320077b65c8120004fd768cb100067c73d951000cfe70986423679f3099232116ef3298632006df65d8d21035bc7458910005bf74585322b79e531913007cfc7398a41014fd7018530024fe7598a41006bd72d9121004ff7650f201bedf42d8d42007cf638852107cfc72d8d20014fc735912100cfe76d8131006be50d912101cfe74987200cebf4359021006ee51189311bede41d8d4200cfc7059132004fd75d92212bebe70d913007fac325923201cfd72d814201dbf7250941006be5059021024fc75d812116efa10d8141004fd7690910004ff7558d20004fd70185322367c70d9510046f473185421eedc6390921046f47018542006ee65d8931047b471990211b4ff7358d202d6bd31d9130006ef72591320f6dc6358d21014fd70d8930085dc7350b20006d4631854207cfc7258c21006f420d8542006ef6250931044ff745902107eec32189100febf43d9121046df7358c210057f7558520006dc6398542046bf60990212bebd70d913000cfe70d8d21006de75d8d211a6be64d91320ceb44318542005df735911001cfe76d91320ceb771590210067d74d9520306ed42d8940006ee4018931024fc7558642024fe75185402d79c32d913007ef66248421046bc4159310006ef541893107ef42158642007d463d8542004fd7598b100eeef2058b10044fc75d9231024fc75d8532005f77150910006f771591212bebc20d9130344fe769053107cfc7498910004ff7559130146bc6459131005fb7048510006f57518542006dc73591200ceb67418542046ee2198b101e6bf40d91200067c64d9520046bc2159021004fd72d913107ef461586322d6bf43d913007cff75189401d6be3059232355f77158d4111cff7259121004fd7650d10005df73509301b7da708
  | 3 => 0xd65d913107fe43288421024fc75d85430cef54018542005ec725913101ebc6450931174ff7359131024fe755902107ebe425932000cfe729872001cfd7318543004fe76c8530006df638cb1007eee321893106ebe64d91201d6bc53592321d6bd735923207f9f329923201cfe74d8f2001cfc7458231006be715923212edc63c85210c5ee73c8421006bf6498930006bd75d9130006dc42d8d21006f5631854201cbe74d8f10005f77150931004fe764c941136f664c8621046bc6059021006df638c54016ebf4059310046bf41d9221004fd755902118ebe43d9231006bc52d9121006be65d912101cfe74d8931046f671d9231024fe75d9121044fe768cb10006f5531854200cfe7058f21045bf7659021004ff7059232006be651912101cff7659231004fd7518542044ff70d911000cfe76d8132006bd6559232044fc73d8b1007ebc5259021047b44150631006bd5259021004ff7358321006ed76c8621007cc73484211d6bd5359232004ff7559221004fd73d8910006df6418d21114fd73d8e21005bd7090a41136f440d8542006ec60189310067f658c52007cfe72986421ccfd7650920046be74d8f1025eef20d8930004ff75d85400057f7558d20136f743d854207fac325902101cfc74583211667c658c51007cfe72d8d20024fc7558d20006dc6418d21047b671905411d6be43591320057f7558940006be7059021014fc7358021014ff7658e42004fd74d8f213479c3119131004fd71d8143006ed51189310067f6590910006bc7458720006ec6248510024fc7558b10004ff7158f20004ff75d89100ccff7650b210067f6590520024fe75d9021006bf6490930046de3158f1000df8704c510014de76d8d42005df73589102f5bd755094007ebe425902106ebf4258242006f430d8542006de60d8d21004fd75d8930004fd7398910007af625094100cfd74d8540024fe75d9130004f7715912011ebc42d9221046f671d8f100de7c658852001cbc7458e21024fc75d8d41137b443d8542006bd644c4210067f755823207eef2018930137b474d8542015de73905301967c6590510004fc764c54003d7c7558910124fe7608520006f73118542006bf6458d211bedc648c9300eff01048510024fe75189100067c6558d20005ef72585300c4ff764cb2101cfc7458f2001ebc6490921006be42185420c7cf3018931116ee31d8931005bd709094207cfe768c720006be705923207ebc6250940044fe71d9130004fd73d8520024fe75d8940006ec64189310067f654c510006bc52d9130006f650d85421d6bf31592321bdde7618d4201cbc7458d210247c75582320067f42d952007edf7358f21006be65d91301a6bc41d913200cfe7018910014ff764c5212afb830191302367c40d951001cfe7458221006bc649893107eee7218910
  | 4 => 0x9121014dc7359121006dd6418d21006bf6490921006f770d8542004ff7458e210cebe5459021006ec628854007cfc75d9321004fd75d8943014ff7658c211ae7c654c920044fc75d8b100047d75d8b10114ff764c421007ac64d893101cfe74587201bedc42d8d42365ef7259132014fe73d89400ecfd7158b102367c10d9510006bf525923201ebc6490a2113cfd764c51001dbe74c854001cfc745802107eec731893107cfe7218543006be105923209ebe54d9130006bc65d91300f6dc43d8d2101cfc7458c21137b74159321006df53d8d21346bf63191310067c63d95201d4fd74d9232006bf64c852100cfe76d814104edc32d8f10046bc10590210757c7558d202377471d951000cfe705913110cfd70d891031fe61048421044fc7418b10004ec7258d10004fd764c910006f61018542004ff7058f2101cfe74d813206ebc645912018ebf53d91310067c65d9110046f81058231014fe73d8540004fd71d9232264ff7650b20044ff7518540006f431d8542006bd645802107fcc324c821014fe73d91210047f7558d10004fd75d9131004ff7359120006ec32d8941006ee2018931047ad6448421044fc7158e41046bc71590212ddbf75905400aede63d8d40224ff7158d10004fd751894307fea52c8120024fc7558e42046de73d9221024fe75586320cdb47448421006bc10d9121024fc7558232006bd6599021046f410185322d79f31d9130006f452d8542006df41d8d211a6dd4358e42004ff75d854207cfe72d814301cfc7458f2107ebc7259021004fd7498a310addc7358940006bd7059232006df7359110006f75218542006f73018542005dd7390530007af7448421006be65191310c6ec7258c2101faf6290942024fc75d894307ebf7459232004fd72d813107ef76198720347b43119131014fc73d913018ebe73d9131146bf41d91310febe54d912101cfe74d8131004fd7398a4100df87050920006bf64c8530046de3158e41024fe7559231007ac744842107cff7648510004ff705923100cfc70d8d10005ef7250e21044fe71d912003e7e76d95100febe7619121004fd73d8540126f710d8520004ff7558221006f95058021005f77158930006bf6450510044ff7018530044fc751853007cfc768c910005ec724c7100047d7598910006f570d8542014fc73d912107df77648421044ff7518b10046f671d8e2100cfc7058a312bebc10d9130006f56118532136f642d854207ebd74d8f21035be7408510006de6518d2107ebf4218940006f552d8542005f77158d42045f7724842111ebc43d922107cff75d8f21006ee20d894100cfc70d894327ddf754c5300067f65d9120047e651c86210067f6559110006f670d8542005bd748c940006f66318542035f97098540024fc75d9120006f460d8542004ff75d9130006b
  | 5 => 0xcfc70d8e21005df73485101eebd43d91322377810d9510006df63985420febe64d91210067e74d95100f6de71d8d21006ed62189410079c648c930375ef7258d4212df7715893118ebd73d9131035bc7458d10006dc635854200cfe7018542005bf744c51000cfe7059232005ef7250521176de53d8d410cef554185421d6bf325923200cfc7058e4100cfc701854200cfc70d923113efa60d81310cfb67418542007b64318542014ff7158f100ecfd7698b10004fd7598910006f45318542006df638c910005fb704c920024fc75d913118ebc31d9131046ec2158a31006be40d9132024fe75591300cef74318542006de6018d42006ef41d893107edc3258c210c6ee4318931014ff764ca210067f6518520044fc7498720006b64218542006f6301854207ebd7418940006bd7359021004fd74185201ccff7059120014fc73582420c6ee3018931044fc7158a31014fc73d852001cfc7458d20006f43018542014ff7658e21014fe73d8142135f77150b2101cff76593210067c42d95201eedc43d9232006bf7559232146be644c42107ebc6450b2100cfc70d8d42006bf5159232014de73d9221006f56118543004fd7518543006bc51592320079e748c930006dc75d8d2101cfd70189401de7c6550920005f77159132005df7348421004fd72d8143006f410d85421bede648c93201cfd73189430057f7558121006f75118542005f77158132006f67618542024fe7558e41044fc7158a4116efa60d814116ef860581410057f7558142024fc7558f10004ff764ca41006f74118520004fd75d9021004bd74d8f2007cff759891001dbc744ca411d6de74d8d42005bf744c421136f654d85420c7cc32085301bedf41d8d421bedc648ca3107ef6628842100cfc7258f20005bf7458e21175dc7358941004fd7650910044fc73185420ccff765062136edf4318943004ff7358b1000cfc7059121136bc64c8521006bc65d9131044fc715923207ede3258c2101cfe76d913107ebf2159021004fd75d93201fcfd74d9130146bc42d9131115ec73c8621035be748c910006de6418d2100cfe7058e41044fc7159120004fd7690a31004fd76885400079d53d91302477865c8120044fe71d814218f9c31d9131005bd748ca21046ec2198a31006bf72d9131006ec42d893100cfc7158f1007cff75d923207cfc7598910046ec2158a4101cfc7458232006bf6450931116ed30d8931045f47150a21024fe75d85201d6bf305923207f9e748c93201cfe74d8d1001ebc6490531004fd74d8131006bd7059021004fd75d8540005ef7259110024fe7558d2100cfe7058a3107cfc725864201ebc6450932024fe75d854307cfc7650721004ff7559232014fe73d9221046ef7258b10004fd70d85430cebc6408530024fe75185200067f65c8510006bc30d
  | 6 => 0xc73509410bef510185200cebc4118941005f4715894307edc3258f2007cfc7258d10024fe75d81212b79c321913007fae729094207ebe5259021005df7350910006af64d8931007ac62509401fefa30d81431d6dc31d8d42006df63585420067d72d9510046f43118520186be7690540014fe7359021007ce628ca31004fd7118930006ec62581311d4fd7650932007b642d854202edc32d8d10006be50d91310c6ef3258c21004fd7558e42004ff7059132006ec51189310079c64d8d211eede5358e4201ebe6190a4100cfe705913207eee72d9320004fe769053007ef72198642014fe7359320044fe71d8d20044ff73d9131006bf65d913107ef46158642004ff7158242006ef6208540005f4715093233fe551c8621044fc715824101cfe7458b100067f73d952000cfe70d8d42024fe755823207cfc7258242004ff75d8941254fe769092015ebc4059231006df65d8d4207ebe7259021065f97098930006bf71d9121044fe768ca41004fd73d9120006ec65d89310067c65d9120007b47150940006de3218530014fe735891009dbe7498930006ef74d89310079f64d8d211c57c755823215edd43d8d41004fd75d8b10006dc71d8d4200cbc765094002edc3258231006dc7358910005bf7458720004fd7690931004fd7018943004fd74d8f10004ff75d8d1001cff7659320004ff7458b100eeed2058b10047e7724842107ebf6159232004ff7058c21005df735082110eef20d8910014fc7358642014fc735891007cfe72d9131004ff7558d1001cfe7458e21044ff75d9021014fe7398642006be52d9121044fc768c520047f0108851001cff76592211d6bd3259232004fd7559130004df73591201667c658c520006ef7258910176bf4359231046bc6359021006bc50592320079e748ca31065dc735092007cff7598b10004ff7558a3107cfe72d9021044fc7318b10014fc73593210467d75d8b100067f41d9520004fd7598632046bc6099021014fe7650932006f45018542004fd7690b1007ef46158720006bc20d9131004fd741893007ef72158642005f771591200067c43d9520006de3258231007cc724c530004fd70d8d4201cfc7458f10006f76148520004fd70d8931004fd75d9120004ff75d913201cfd71d8141006de30d8d4201cff7659130044fc768cb101d5be7390942116ec3258e21295df758c9301cef8605814236f9f4018d42014fc7359110006f751d8542006d463d8542006bc755902107ef97098910116ef53d8931006bc7458d20005ec724c521006f77158d2107eec2018941014fd74d8943006be52d913001ebe6450a311967c6590520044fc7690520006bd5459232006df53d8d4207fac3299021044fc7398720006f7321854201ebc6490721006f773d8542024fc755913007ede3258f20006dd64d8d21
  | 7 => 0x8142047b44150421014fc7358b102bebf20d913007cfc7418931006ed5218941014dc7359110006bf71d9130044fe71189100edf57198910006be659923201ebc649093026e7d10d9520024fc75d9132006dd72d8d21006bf6490931007b57190a4101cfe7458f20004ff764c9400067c31d952007ef576c862126e7c20d9520006f470d85420057d759852019cfd764c9200febe71d91210aedc31d8d40006bf6458931046f4411853225def7258d20006f410d853200cfd74d8940006dd52d8d21004ff75d8d21046f71018530046f6411854001cfe74d8f21006ef725911007cfe72d81410eef86058121014fe731891001cfe7458f10004f4715912007ede3258e4218dbe7619131004ff7058e41044fc74986321d6bd3059232146be64d9131006ec20d8931286dc32185300cdf7715042101cbe74189101d6bd6450a32005bf7458d100cef74218542006bd64582320c6ef32d8c21006df634c5212af9e3019130046f64198642004fd7558a31014fe7650531136f774d8542046ee7218b10006f47159132046ee72d902101fae7290a410c6ed5318931006f652d854207ef42158720145bc745813124eed201893007cfc7598b10004fd74d8520004fd71d8142007cd628ca31044fe7650f10004ff745823207ebe6299021046dc3158f10085dc7348720006f7619853000cfe70185201bf9c42d8d42004fd7650a31006dc40d8d21136bc435932121cfe769051009ebc41d913007cfc7259310004fd7559321006dc6358121005ef7258d10004ff7650d2104ddc7350b10005f47150930004fd73d8b1007ef761986320c6ec5318931004ff764c941004ff7158e42006bf74591200cebf7659021006dc20d8d21136b464c8521146bc40d91312bebf73d9130016dc638c540006bd73d912107ebc4259321014fe76d8d21005ef724c510006f731d8520004fd74189101a5bc7458132046df31d8f10006bf7559021024fe75d8d42007b97090540004fd71d89300f6dc30d8d210067f6508520047ae6448421006dc20d8d4200cfc7159310006df43d8d21006be6519130116ec31d89312feed4218940046fb105802100cfc73d8131006f761985320d67c65085100c6ef311893125cff7258d20005ec7259110006ef3218910004fd7398720005df7358542044fc7158c21036bc4159110006ef6298943015dc7350a32006b47159021024fe75d814207cfe72d8f2018ebc30d913107cff73d9132007cc628c53100ddc764c530024fe7559110005ef724c421004df7358b10004fe7688540044fc731854018ebf43d913118dbe7390a41016dc634c510004fd7559320004fd7558242047f251c41102367f70d9510014fe7359310006de50d8d2101cfe74d8121006bc7359021137e742d8542024fe75d8f10044fc73d9021006be70d91210079
  | 8 => 0x46bc6399021174fd76505311bedc74d8d421bede42d8d4211cfd74d92213679c7399232014de76d8d210067f43d9520046ec2198b101eede4358e42004fd75185400067e74d9520006be43d9110006bf6498530004fd75d8132046be7159021004ff7558b102eef641d8540006ec40d8931024fc75d91212eebc41d854032fe732884212bebf40d9130004fd70d9221004ff7359110004fc764c941004fd7418931006bf70d9121006ee101893100cfe70d894307ebe74d8f2107cfc75d9320006dc6518d21004ff7558642004fd73d81411bede648ca3101cfe76d9120014fe73d81412a6ee32d8930014fe7358241024fc7558242017db608c930006dd6518d420befa3058021006bf645812126e7c70d9520046ef6298a3119efa30d813200ddc708c930006ef5218931014fd741854307eee321893001cfe74d8d21004ff7650d20045ef7148421006bf72d91211d5dc73581422367f20d951001cfe74d8c21006bc649893007ebe741891007efb2058242006de65d8d21014fe76d8d410cdbc744c42101ebc6450510006bf6490a2119efa20d813200cfe7098a31006dc60d8d42024fe75189400f6df3058632004fd7558a41014ff7258f20116ec30d8931006dd5358c21014fe73d8121116ec43d893107cfc7258e4207fac4250b211bedc40d8d42116ef43d893107cfe7258c210c6ef3018931044fc7650c2107edc3258e42007d4734842126f6c20d9520136f44198a410067f6558910004fd7690530005bd72905410067c651852000cfe70d8931175dc7358141047e441c842107ebf2059021004ff75d9131004ff735872009dbc745893009ebe7619130006be6059021136f772d8542006bc65191310febf4058a4107cfc7498b10134ff7159121024fe7598720007b46190540004fe7650d201d6be315923215ebe5459231006bc52d913100cfe764c920006be6458021136bf4159321014dc7358910044fe7159231004fd768c94000cfe7059221007af3259021014fd74d814317d7c7558141006df7358d10005bf7448720006ee50d89310067f74d9520006bd52d9131004ef7648421045f47150a310247c755911007ebf6099232024fe75589100247c7558d101d6dc30d8d4200cfc70d9121007b76190540014ff7658f2007cfc76c8530006dc635814207cfe7218530004fe76485400067c41d951008dbc744872000cfc7059021006df7358d21006de50d8d42046f641185431d79e74d8d42006f77159120046f63118543046dc3158e41006be70d9131004fc764854023d7e76d95101bf9f41d8d4200cfc70d9131004bf7458720005ec724c540004fd7318940006be43d9120004fd768c72007ef571d9321006bc6458121004fd71d8943006df639092100cfe7688520046bc4159021046f64118542005bd748ca41004fd73d
  | 9 => 0xd71d91310f5dc7350921116ee63885210057f75591102367d71d9510006bc71d9130006ed541893100cfe705923101dbf7250940046df3118530004fd75d8f1007cfc7258e41024fc75582212d6be53d9130044fc7418532046f63198632006bc6519130007d4614c530005f47159132004bd7699021004fd74d8d211d79f3059232024fc7558d10004ff755863202edf3158231006bf65191311cebf40593200047f7558231016de634c7210067f65909200c6ee7318931004fe768c91020ff151c411007cff70d9120006be435931000cff7658242006dc10d8d21006f76198543044fc74d8c2107cfc75d8f21004fd7598a31006ed64189310cfb74150821006ec7259110045de718c531006ac64d89311f67c6590910004ff75d8132004be761912107e7d7598910006dd52d8d42006dc6018d21006f675185420079d5319130004fd70d8d41006ee64d8931006ec52d8931004fd74d8910176dc63505212367f40d9510014dc7358b10006de71d8d42006f761985420067c72d9510006ef511893101cbe76d912101cfe7458a3107dec7250721016dc638cb10006ef42189100fcfd71d9121006df63c852100cfe7650510006ec70d8931006bc6519121004ff764c540147b4415053107fb56448421014fe73d89101bebf7259232024fc7558321044fc75d902107cff768cb10004ff7359021005ec724c621014fd7258f2007cfc7258f10005bf744c72107ebf659923226e7c40d9520044fe71d8f20005ef7258131024fc7559110046f970d8f100067f654c520006dc52d8d42006bc7458e21004fd72d9310005df735912001cfd70d85400c6df3058c21046f86058231024fc7558d210cebf4059021006f76188520004fd73d8940004fd7690930046f8105822114e7c654c5102bcbe7619130004fd7118943044fc7158232046bf7459310126fa1058321004ff7058e21004ff7458021005bf7458131006ef7258d210cebf4018542006bc10d9131024fc75d8d4200dde704c530005bd749853000cfc7059221146be54d913111cff7650421006dc6518d422b79f3119130006df64d8d2107eec7418931024fe75d911000cfc70d9021006df638c94107ebc6459320044fc75d8f1001cbe7418b10004fd71d8d42004fd7518532137e442d85420fdbc7458d210cef74118941006dc64d8d21006fb705891003d7e7598910136f674d8542007b77448421005bf7458910006de54d8d21006ed52d893102edf31d8d10007b47448421004ff7559321004fd71d813201cfe74d8e2126e7c30d9520014fe73989100feee4258a41004ff7359321006bf64d8931006df72d8d21014fc764c921006ef65d8931004fd7558232006dc52d8d21115ee761893116cff7059110007af64189310cef54218542035bc744c510006be7559232136bc64c8530
  | 10 => 0x823110eed20d8910006f441d8532007ad6290a410067c7558d20006bd64507201d6be43d8d42014fc73592210067f6518910004fd71d8940006dd5358e4200cfd73d8930004ec72591312367e40d9510006bd5059021006f77159131065dc735852010cff7648720006bc6458931005ef72585431d6bc63509411bebf4159232004fd768853007cfc731891018ebe6390541004ef7259131006ec7258d100cef44318542005ef724c7210cef6741854200cfe7018931006de64d8d2107cff75d932012cff7158d21005dd718c930006bf6450d21004fd70d8943007e761885210067f74d9510004fd70d9121006be4059021006bf72d9130006bd50d912101cfd70d8d40044fc71d91100067f6550510004ff7648530134f77159121006ec10d8931004bd74d8c210067f7558d10005ef7250c21004ff7458c2107cfc768c9401bede54d8d4207eee4218941306ee42d8940024fe755913209ebc54d9130004fd72d853001cff725932001ebc6450d21006bd645042119edf3058f20044ff7598642006be51d91211e6bd40d9120005df7350b21044fc7418530005f47159120345be76d913101fb67190540006bf73d9121044fc7598632006dd75d8d4207cfe7218540004ff7648421004fd75d9321005ef7258d41046be5159021004df735911007ebc6599232006bd6458c21004fd7650720156df30d8d10115ee728ca21046f45118530004fd70d90210c6ed3218931014fe7318520006ec5018931006dc63d8142006bf65d9130006ee54d8931045bc7150941006bf645052100cfc7058632006dc10d8d42006bc60d9121044fc7690b103679c3199232004bd7418b102d6bd43d9130017d6618ca31046f651185322bebd50d913007cfc7318941006df7358910007b774d85421d6be6350941044fe71d8143006f473d8542006be535902107ebc4259232136f740d85421b4fd70d8d2007eee72d8f21004ff73589100febf40d9121006ed651893107ebc60992320067c75589100067c655911001ebc6450521004fd755923101ebe6450a2100cfc7018941004ff7650a31005bf7458931006df63185420cef44218542176dc32d8d412bebc70d91300067e72d9510006be53d9121004fe768c94001cfd72593200f5dc7359121006df71d8d42046ed72d8e21044fe71d9320006f665d8542004fe76085400067f7558d200c6cf30189310c6ec321853210cfe7618910006ed7418931004fd73d8542005fb7050510024fe75d853200cfc70d8d21006f56118530024fe75d8542004fe7688530014fe73d8520004fd75d8d4007ef571d8f212bebd73d91300d67c6508520006bc72d9131006be6498632004fd7559221006bf6450530016dc6350d211bedc648c932007cf7348421006bc7458910006ef32d8941006be51d9130005f77150b2018eb
  | 11 => 0x44fc7418520006be60d913100cfe70d9231004df7358910004fd75d8d2011ebf4259221004fd74d85320c7cc3118931046f42198642004fc7650910045f47150c21046bc4159231007d9708c930006bc64d8931006ef70d8931006bf54d912100feb62c8120007ac6418931044fc73d922100cfe7059321024fe75d8c210247c7558910044fc7650e21014ff70d9130006bc64d81210cdf47448421136f543d8542046f46108540044fe7650b10004fc764853001cfe7458d21006bf641853001cfc7458d21006ef6290931065dc7348520024fe7559232004ff7458321006fb50d8131006f550d85420ceb7401854208dbc74587200febf425864201faf7250941006bd42d8141046ee614842107eec4218910014fc73d8941006be52d913100cfc70d894107eec6208540136bc41d932126e7c10d95200067f65d8d1007eee32189430079f63909420057f755813200cfe7259320005dd718ca310067f65c852007cff7690910024fc75d8930004ff75d853018ebc6390541004ff7558231024fe75d8d21005ec7258d41024fe7559131136f640d854207ef7215872001cfe741853035cfe7690932004fd75d8543006be40d912107ef82058232006f753185420767e72d9520004ff764c7200247c755912001ebc645092000dbc7090540046bc6459021044fc7158e42004fe764c520006ec625093101cbc7458910024fe75d8530006bf7458d211bfcf42d8d42137b44150721004fd74d8931005bd719094207cfc7598a41006bf54d9130004fd768c540006df70d8d421bede648c930015dc73c8530135f77158941044fc7518532004fe7648530004fd7518b10006f651d8542004fd755824107eee72d9321004fc7650d21006f57018542186bd40d9110184fd70d9110006de52d8d21046bf63590211e4ff7459120014ff764c51000efb62c81201d6bf535923207eee5218941004fd75d85301fef86058143044fc7158d20006ee6518931005df735093100cfe70d894101cfe7458d2000cfc70d8543004fd7559110006df7359120005f77158940006be60990211d6dc6358d420067f755823111eed42d8941006dc63d81210e67c65c85101d6bf73592320067f6550d10007af3299021226f710d8530005df7358b100cebc5459021044fe711894307f9f3259232005df73581410cef57218542024fe7558f21004fd74d8930004fd70d9231006f763185422367c71d9510116ef3258e211d6bc7359232006f653d8542006f67018542005f47158d42006bd6450c21024fe7558021004fd7098642024fc7558720135f77150721044fe71d9232044fc764cb10004fd75189100cef74159021006bc65d912107ebe425932100cfc70d8c21044fc71d8d100febc54d912101ebc6490931014fc7359310176de43d8d411e6fa40582420247c755
  | 12 => 0xd7558632004fd71d9132004fd70986320069f735923200cfc70d8532006be6458632004ff7650530006df7358d200cfb44218542006f76518542004fd74d8e21006f47159120006bc7559232136f741d9321004fc765093118ebc43d9231006f7610854019efa60d81320079d748c930014fe7358a4100df87048520044fc7518b102367d20d9510006ec74d893116cfd74d93101d6bc435913207eec7518931044fc7318520187ba7090540046ee2158b10004fd73d9221006fb705911007ebf42d9320006bd51d9130006bf7459132016dc638c921024fe7558642004fd75d854207ebc20592320067f755911007cfe72d8131176df31d8d41006d76318542044fc7518520006dc41d8d212377610d9510005bd740852000cfe7098a4101cfd73d8143004fd7318520046f77318542004fd7598720006ec32d8910014fc73d9110006de321853201cfc74d8910016df608c930005ec72585431d69c7359232046f47518542024fc7558231044fe71d8d4000cfd72d9120006ee52d8931146be71d913100cff7658221006df628c930004fd7650b1001cbf7659021014fc76509321f67c6590920115dc7350a2107cfc74d8f2001cfe74d8f1007fe42048421005bf744852000cfe7648510014fc735822107edd73d923200cfe70d902107ebf6450b200f6f63158632006bd6450a2106dbc7448520024fe7518542004fd7518520005bd748c91011dbc7458e21006f42018542005bd7498931044fc764ca4100cfc7018543006bf5059021014fe76d8d10004fd7018543004ff7458f101bedf72d8d420067c75582312febc411894007cfc751893107cff768ca41046f86058241046f43118542007d463c8521024fe75d91320c6df3018931005f471509102bebf50d913007cfc73189400057f755893001cfe7418532006f56118542006de52d8d420c6ee3118931006bc60191211d6bc3159232006de30d8d4121ef5101854000cfe7159310004ff7059021006bf50d9121116ef73d8931124ff7648710004ff7259131004ff7558f201ad7c75581320fdf5719894100cfc7098a31004ff75582411b6df30d8d20014fe76d8d2026e7d72d952007f9d748c932005bd7190a41004fd70d9232045f47150821046be4159221016dc638c72114e7c654c5202bebd20d9130006dd70d8d211cfb87050940006bd72d9130006dd634c721046bc645062100cfc70d922101ebc6490520007d46318542136f572d8542006ee7018931184ff745911018ebe4358e41024fe7558a31006ec6290531046bd74d8c21006bf64d8121024fe7558321006df735912107dec73c8421006fb7058d20136f454d8542004ff75d8943056bf42d814101cfc7458e2116ebd4059310006bf545902101cfc745822107fb6644842107ebc2159232004ff75d8121006ef4218931
  | 13 => 0x8720006be20d9121005bf744871006dbc7458520014fe73d85420079d748ca3107cff75189432d7bb30d9130006ed6218930046bf10590211d4ff7359132024fe75d9231006ef62485101bebc40592321d6bf435923201cfd73d8943004fe764c910046bf745902101cfe74580210cdf6744842107edf628c932004ff7058e420cef44018542015dc735093201cfe745832126f6c72d9520006f451d8530006be71d913000cfe70d8532006ef52d8930006bf71592320067f658c91001ebe6450c21006be6319121004f47158d200d57c75580210c6ed3018931014fc7358720005f77150920006bc649853007cfc7258232137b74150b2113efa30d8131046f4411852001cff765931007cfc75d8f201bedc41d8d4222cff7650710006f463d85420c7e4311893101cbf7659232006dd71d8d211d6bc3059232116df3058e21006be6458c2134ef631d854319edd3058f20014fe73d9130055bc7448710006be75d9130004fd7218530005dd73085302bebe20d9130014fe7318b1001cff715931001ebe6450421045f47488421044ff75d92210cfb44318542005fb7048520004bf7458d200c6dc3218532004ef7259110004ff7458f21046f42198632044ff70189100767e76d9520006f750d8542046f67118b10014fe7398b10156dd30d8d10024fe7518530004fd70d8f21024fc7558910066df32d8d20006dc63d854211ebf40d92210067e63d9520006bf648c9211a5bc7458532006f660d8542006f65018542044ff7518543006f77158d10004fd75d9121004fd760853022df771591102bebf10d9130006f651d853200cfe76c851000cde768c930006f75118530004ff764c9100a57c7558930006be505923207cfc7258241006bd51590211fefa60d8143046ee2198a4112cfe768c521004fd74d8d20006be75d9131004ff7158232024fe7518b10004ff7558a41046ed72d9221024fe75d891000cfe7058642136f77159321024fe759863213edc764c530004fd70d9132356f641d854300cfe7058d21006be4358a410f4ff7358d21046de3158c21137b740d8542024fe7558242006dd638c9201fefa40d814300cfc7098a41006f475d854207cfc7259131044fc75d922107cfc7258632024fc7559120007d7614c530005df7348720005cc724c530024fe7558221376ee42d8943006df63581210067d73d95202d6be32d9130114fe768c921007b764c8521046dd73d9221014fe73d9021044fe71d8b10044ff7690720006ef5218930044ff75d8e2100cfd7418540136f754d854226e7c72d952007cff75d8f20005bf744c720006bd51d9121006f55118532005b47150941004fd7558b1007cfe72d923207cfe72d9120006bf6490720047b56488421007b464c852104ddc7348710024fc75d81411d7af3259232006dd53d8d41004f
  | 14 => 0x146bf40d9131006be601913100dbc7650940116df3258e2118ebe53d913118cbe761913100dfa70c8510005bd741891007cfe72d8d4126e7f20d952006ebc415824200cfe7058a41024fe75d85401ecff7459132007db704c530015dc73509302c4ff7359130044fc7650a310067c74d9510004ff74582312bebc73d9130005f77150b10044fc7118910006be7559021004fe76085301d5de76d8d42014fc735932007ebe74d8f20004ff75d89300067f6558520006bd54d9132024fc75d8d21014fe7358221046f4219872007ebc525923201ebc645053000cfe7198b1011cfe769092107cff7518941005df73585200067c6558910046bf6450621004ff7358642005f77158142006f45218542014fd70d91300757c7558520006be4059231024fe75d8d40024fe7558c210c6ef3218532024fe75d8131006bd7559021004fe76c8540005f97008530066dc3258d2007ebc3259021004fd75d8d41006bf64d8131006cc628c5310079c7350940004ff7058a41004fd768c520016dc638c941014fe73d894102ede63d8d10004de7618d210f5dc73581210cfb44108540006bf75d9130024fe75986421bebc648c921006bf6490520006f5731854213cfd73d8f10044fc75d8e2107ef970d8f20006ef764842101cbc7458d10005ef724c720005ef725814106ebf42d9120044ff75d9310024fe75d8f200067c41d9520024fe7559310005f77150a320ecfd71989102ddbd7590540017d7714c53007ebe425923200cfe7058c21044fe7690a31085fb705893000dde708c93007cfe72d9231006ee60d893101cfe7498a3101cfd70185400757c7559120006bd71d913001dbe748c941004fd73d9321266ef20d89400067c7558d10004ff75d814307cfc76909300067c75582322a6dc32d893007eec421893101cff7650510176de63d8d41004fd74d8f20116ec6388521004fd72d8d41006be41d81412367e20d9510006be63d912107ebe3259021006df634c9202367f10d95102f5bf7550940006bd70d9131006bf6450920006ef7258d20327e55248421006bd5259232006f551d8542005df7358940004fd7598a41004ff73593201bfcc42d8d42004fd7650f10006be6559232044fc7159231006f55218542006ec41d8931004fd7018542006ef628853000cfc7058f21007b77150941346f53118543006be2059021005f47150931004fd7318b10004fe7690910004ff75d8d2001cbe76d9130006df40d8d212d6bc32d9130005df7350b2004ddc7358b10024fe75d8132006df7358b10004fd75d91321d6bd3159232004fd7498b1001cfc7650921004fd75d8f200e67c65c8520006bd7159232006f56118520007d77348421004ff75593200fcfd7690a21006ec6288530006ef6298910044fc7158231004fd7558221006f4601854201cbc745
  | 15 => 0xc7358540006df75d8d42014fc7358241006ef62d8131006f77159110005f47150f2126e7f40d9520006dc54d8d21114ef7258d2107fe6624842101ebe6450b10116cc6388521124fd70989101bf9f7399232014fd7018930004fd74d8d100067e43d9510005f47150b210057f7558910004fd73d9021146bc54d9131046f8105824100df8704c920006bf7459130004fd7559121006bc1059232046f970d8b10005f47158940056bf425931007dbe72909420f6dc3158632006af6418931046ee72d8c21004ec7259110006f461c854007eee72d9232046f41018542135bc744c721136f464c85212bebe30d9130004ff7259110006be4359320004fd755872018ebd43d9131004fd7398b10005be7619121004fd7018941004fd7559131004fd75d8131006bf6519130005f4714c921004ff755913107dde728c932116f53198632006df6350d2110ef51098720015dc7350a31006dd634ca21006dd50d8d21006bd50d9131004ff7458632014fd70d853007ebf60592320fdbe76d91211bebe5459232006be73d9121006bf644853007ebc6459232006ec75d89311d5dc7358542004fd751893001cfe74d8b10004fd755832100cfc70986320067f65989100b57c75585400cef65418542004fd7218543014fc73d8142006bd6450b100c6ef5318931006be4359021024fc75d9130006de40d8d21006ef40d8931017d7618c5310079f644c530004fd75d8941136ed4298a41006bf6458530004ff75d9121006df74d8d21044fc7518542004ff7258241115ef724ca21006ef64d893106dbe7408520004ff7559231156fa3058231005dc724c5302a6ed32d8930006be609923200ddc704c530024fc7558e410f5de76d8d21007d763d8542006be30590210077b65c4110004ff7358a41044fc75d931000cfe70d9132006dc60d8d2107ebf655923222ebd74d8540044fe71d8d10007d6718ca31006ed621894300cfc7018910006df6350521004dd73d92210067f65d8520006be431854229eed3218930004ff7158d200cef6421854218cfd73d91310fcfd76505211b6dd30d8d20006fb7058d100067d71d9520006bf64d8530006be75d9121014ff7658f2100cfd7418940046fb1058231006be30d9121047b664884211d6be63509400067f72d951000dfa76c4110176bd4359231006be51d9131006de65d8d42014fe73d9120004fd7498910014fe735832100ff361c41100f6de53d8d212bf9c30d91300067c32d9510004fc764c520366df6218d42346be4318543006f741d852018ebe6390540004ff7558e411bedf40d8d42006dc65d8d2107eee4218940014ff7658e41006fb50d81210eefa20d8121004ff75d9120006f56118540006ef4118931004fd7498720006df7359131046bc645923107ebc6199232004f77648421006f620d8542
  | 16 => 0x813101cfe7418931006bd64484211bedc54d8d4200cfc7258720046bf6559021006bf3159021006ed50d89312d6bd53d9130014fe73d8b1012cfd73d8f2102edc43d8d10046bf65990211bedd43d8d42005bd7498930006f761c85400aede53d8d400cfe74218542005f47158d2001dbc7458e41014fd7158f1001cff7650531004fd764cb10046bf6190541006df63d8121004ff7558c21004fd7318540004ff745872000cfc701893100cfe76d8142004fc7650d20024fc7559221006ee40d893107ebc7259232006bf31d9121024fc7558a412d6bc53d9130005f77150921006f775d8542006bc6418530004fd768c94107ef86058232006dc74d8d2109ebe64d9130006ef6250531024fc7559321005dd73885300c5ee7348421006df54d8d21006f751d8530006bf54d9131005ec7250e2101ebf615094107eec20189311a6bf42d913200cfe70d911007cfe72d8d40046bc5159021125f77158910015de728c930006dd50d8d4201cfe74d8d20006dc7358b10006bd65d9130006de51d8d21006f431d8520006bc73d912101cfe7418910006be43d9121006ee51d89310079f73592322d6bf31d913000dbe70905400047f7558232024fc7558f2107ebe72592320067e73d9510005ec7258141004ff715923206dbe748c920006bc51d9121005ec724c510014fc74d8d4008dbc744c720004ff7650c21046bc655902101cfe76d9110136f643d854207cfe72d8c210fcfd72d9121005bf7458d20014fe735802107cfc7398b101bede40d8d4207cfe72d9130006f630d854200cfe70d8d10006ef75d89311b6de768c930024fc75d8142046f8605822107cfc764c7200c6ec3118931004fd755823101dbe74d8d42046ec6258a31006ec6518931024fc75d8d1000cfe70d8542006bf64509320067c7559120116ee53d8931044fc76885302367e30d951007cfc7650f20047e4104842100cfd71d91100247e76d9510005ec7258530044fc764ca211d79c7359232004bf7458d10006de51d8d42006f432d854201dbe7290a411bedd41d8d421cefa40d814207cfc7650720004fe7650931004ff7059121004ef7258d10024fc7559232046df7358f100cef47159021024fe7558720006dc628c531006ef7259121006bf7458910014fd74d8543014ff7658f1007cfc74d8f21044fe7650c2107cfc7498a31044fc7598642024fe7558f10046f63118530006df638c5200067f6558d10004fe7650d1007ef42158632004fd75d923200dbc70509400067f65485100057f7558530004ff7358242006f565d8542004ff75d8d41046be4159310006bc51d9130006f76158142006be40d913107cfe72d911007dec724c4211bcdf7359132006f465d8542004fd75d81410057f755802109dbe7498530006be63590211d6de53d8d4207ebf21592320add
  | 17 => 0x4fd7558f20004fd74d8121024fc7558c2100cfc70d8f2101cfc74d8132006dd51d8d21004fd7518940014fd72d8132004fd75d9110014fe7359120044fe71d8d42005bd7408540046f97018b1007edc6358f2101cfe7418b1000cfc7058d21146dd4358e41004ff7650910004fd7418532004fd73d9320044fc768c54007eec70189311057c75581210067c65585200067f71d9520016dc638c910004bf745891007ebc65592320067f73d9510046de3158e2116cfd765051007ebe5259232006b643185420067f659852007cfe7259232004ff7358021004f77158d201bf9f40d8d420247e759891001cfe74d8532006bf52d9130005df7358142036bc42d9110006f652185421d79c31592320067e64d9520004f7715913207fe65248421044ff7018540006ee75d8931014fe7358b10006f761d81420c6ef4318931006bd72d9131016de634ca21044fc76085401bedf54d8d42006dd75d8d21004ff715913218f9f30d9131146be7619131006ef32d8910006f551d8532316dd43d8d40006bd5359021004ff7059131136f464c862107fce728c932044ff751853001ebe649051000cfd74d8d4007ef7619864200cfc70d893101cbe76d913101dbc744854007ef72198632006bf6418930004fd7318542006ee501893100cfc7198b10004fd7558f21004fd755931007eec62c8510004bf7458d2107ebc60592320addc734854006ebc43d9120044fc7159130015de728ca3107dbf765923200cfc7650920005df7348520136f664c8521006f451d854201cfc7458632045ed76c86210067f6550d20004fd7098a4101ebe6450910024fe75d894100cfe70d9131004fd70d8542045be7190541004ff7259310116ed71d89312067c6550d10006bc64d8131006bf6450531004fe764c940007b67190a412bebd40d9130005bf744c520006bd53d9121005f77150c21006bc535902118ede5358e4100cff7658241046dc3158c2125cff764cb2000cfe7059021006bc32d9121004fd72d8d1026e7e40d9520004fd7558d2003e7e71d9510005f97088520006ec54d8931005bf744ca41004fd75d8e210067c6518910024fe75d9232004fd70d8941024fc755932007cfc72d9120006df50d8d210fdbc74581210067f65505200c6ec431893107ef82058321004ff7558720136bf4059321006ef6518931005bd729054007eef2098b10007b6421854200cfc70d8d4107cfc7518943116ed43d89310f4fd764c5210067f31d9510145be749893100cfe70d92320f4fd72d8d2118fb731d9131006bc53d912107ebf7459321024fe7558a41006bf50d913107cfc725902100cff7658321005f970c851000cfe70d9221004fd75d8d42046f775185421d5de7398542006ec20d894117e7c6550510004fd7650f21046f671d8b10046bf639902113efa10d
  | 18 => 0xd7559120024fe7558241006f77648421044fe7650e210079f73509410067d74d9510007b643d85421ccfd74d9320024fe75d8d41006ac641893101cfc74d852001faf7250940005df734871000cfe70d9321006bf64d8930006bf6488521006bf51d9130006ee2018941006be6399021006de20d8d2136eed4218943024fe75d814301cfc74d853012edf30d8f21005f771589430bcfd70189100067c75580211d6de7618d42117e731d89312367e10d951007cfc725911000cfc764c51011ebc6488521005f7714c921004ff7458f20015de73885302b7bb3019130044fe71d9310004ff7650e21024fe7558f20004fd72d9110005ef724c520006bc70d91210fcff74591210f5f5719893100cfd731853010efa2058221136f540d854207cff7158b10366be43d8943136f74159321014fc73d894000cfd73189300f4fd768ca210067c74d9520004fd75d8142044fc74d8e210ccfd74d9021066dc43d8d20047ad64c842101fbb60509400f6ee3258a31024fc75d891007cfc7598a31006f563d8542004fd7118940004fd7558c2107efb2058232044fc73d93100febe6448421006ec64d89312367d40d9510137b441c8540005bc7150940024fe75d8d2007ebe6299232006bf64885302367f30d951000dfa7008530036bf41d911007eec6290931046f77218542004ff7359310024fe7598a310047f7559110045ed71c8421014fe76d8d40006ef50d893101cfe7498910046fb10582210067c71d95201cefa60d8142006be10d912118ebe32d9131006ed6218931006bf6458930044fe71d8132004ff764cb10006be7359021114ff7258d21005df7358540046ec6258b10044fe71d9021014fd71d9131044fc7518540006bf5259021004fd7650d20006bf305902113fd8704c530004ff7650931004fd75d913000cfc70d9321004ff7650720004ff7258d10006bd6450721024fe75d8f2119cff7058d20044fe71d9231024fe75d893001cfe74d8520004fd7398642006bc63d912101ebc6450531004ff7558d21036bc43d911011eee42d8941006f663d8542044fe7158c21006f553d854235eed3218943006ed52d8941024fe7598b10017ce728c930006ef54d8931006bc6319121014fc7358a41004ff7558232006ee6418931007ac62509411cebd4059320006ee74189310cfb77159021006bf52d9121006df50d8d42116dc6388521004fd7690720014fc73d89100c6ed3118931005bf7448540006bc60d9131006fb50d8142006de60d8d4213ef86058131046ec6258a41005df73581212bebe10d91302bcff74591300067c65d8d100067c65d852007eee3298a31015de7308530006f453d854206df97098940046df634c71007eef70189311cebc765094000cfc7648520055be748cb102bebf30d91300c6cc3118931006ec4018931
  | 19 => 0x8e21024fe75d93201bf9f4359232046ec2198a41006bd65191210eefa10d81212af9c3019130006dc70d8d42046f671d9221004fd74d8c21004fd72d8543006df43d8d100fdbe748c9210069f6418d21005f77150a21004fe764c540005dd708c531004ff7359221014fc7359120014fe73d932117e7c6550520006df6518d42046f7101852001cfe74d853001cfc7458910044fe71d8930024fe75d922116efa40d814100cfe70d8f210a57c7558530004ff764c520004fd76c854002ddc73509101bebf765923207cff70d8d20005ef7250721006bd54590210f4fd768c72104dfb705853007ef820580210067f32d9510004fd70d932100cfc7058e420cef741d9021044fc7159320046df618c531117cf30d89310067f7558021134fe7690521006bd71d912100dfa71c4110006ef42d8910116ee32d8931006bc7059232046f46108530014fe7318940004ff7650930006bd51d91311cefa20d8142004ff7558e42006ee541893100cbe7690540006bd54d912107ebf2059232006bf325902107eec5218931295dd758c9301bedd72d8d42004bd74d8f21004fd7650c212aebf631913007cfc7259232006dd6518d21004fd72d8d400ffac4250921005f47150b20046ec2158b1001fb7615094107cff75189310b57c7558940004ff735912134df77159131005bf744c710014fe73d9110006be43d9221006bf5159021006bf32d912122cff7159110006ee7618931044fc760853007fcc3258c21006ec60d89310c5dc7350821006f610d8542006ef72591310cfe4421854228ef631d8530015df714c5301bddf7350a32024fe759891001cfd71d8d4107eec32189410c6ec3018931014fe7359121176dc6358d41044fc7158242016dc634c921134ff765082107cfc769093107cfc76c854007eef2018940135f6719072101cfe76d9121006df638c92107ef72198720046ef6298b1013ef850d813100cfc7018520044fe71d9132006ed51d8931044fc76885402d6bf32d9130006bf30d9121006bf51d9121004fc764c910024fe7559121036be64d9110004ff7558e210cef44159021006be20d9131007d763c85210067f6588510006f731d8542006bd54d913026e7d20d9520046bc6599021265ef7259120005f47158142014fe73d9320006f730d85422377771d9510005fb70509200057f7558141006fb70591300247e76d95200cef4411894107cfc7650f21006f752d8542044fc715902101cfc74d8d10024fe7558e42046f47418542006ed75d8931015dc7359232047e66288421056bc4359310264ff7259120046be2159021005df735092007cfe7258e42044fc74d8f10004fe769093100cfe7058e4207cff7018930004fd76085400f6de63d8d21006bf6418931007d5718ca31017ce728ca31006f610185320047f7559120004f
  | 20 => 0x5de7618d210ccf471590211d79c7418d42014fc73d8540046dc614c530006df635814236f9f4118d4200cfe70d8e21006dc65d8d4207cfe72d8d10006ef6208530006ed6218910004fd7558e21024fc75d8d2000cfc70d9132006dc735912107dbc73909422bdbe761913000cfc7098642045f4714ca21004fd72d814107ebf629094218ebc32d913107ebc6250941004fe7650520004fd7650f20006de70d8d21036bf4259110006ed52189310f6de72d8d21006bf645093000cfe70d8d410febc6448530006bd7559232004df7359121044ff75d923100cfc70d8542116ef7258e21004fe769093001dbc7488540004ff7259130126ed2098b100befa50580210079f744c530007b57418542006be1059021004fd75d8c21136f554d8542116ee73d8931005f77158d20004fd768ca412d6bd32d9130004fd759864226e7e20d9520006dd638ca413479f30191310eef71058720006bc7458d1007eec6208530004ff7559120006bf6458131006bf735902109ebc6459130005bf745852001cff765093207cfe7259021006ef725912024cfe768c92001cff76505210057d759891030dfb7058d400067f654c910006ec72591311bebf4059232015dc73485301d6de72d8d420067c6598520014fd72d913201dbe7408540006bd644c8210079c644c530014fc73d812107ebf4218941005bf744c5210cef74018542006dd51d8d42006f6651854201cbe74d8f20006bd6450910004ff7059321016de618ca31006f732d854206dbc744c520024fe755932000cfe7058e21004fe768c520006bc50d912126e7f10d9520024fc75d8d40016de638ca41004ff7458a311d6dc635092126f7820d95202367e70d9510024fc755923136f9c4218d42005df7350b1007ef721586320067f658c92000cfe7258f20044fe71d8940006bd75d913101fbb6090540066dc31d8d200057f7558232006de20d8d42044ff75185421bebc4159232004ff75d8543006de30d8d21004fd71d8f20006bc5059021044fc7650a2107cfe72d8530006df638c94000cdc764c530347b731191311c67c658c9100c6dc3118931006bc6458530044fc7598720006ee20d8931044fc7198a31214fe768c5102067c6550d20006bc75d9121116ef71d8931006bd645863207cfe7218b10004fd71d8d40044fe71d8c212bebc50d91300f6de43d8d21216f51018530004ff7559110044fe7118930006df634c510116dc4358e21006ec1018931006bf644c921005ef724c71002edc6358d101d6bc43d8d4207cfc739891000cfc72593201be9c648c93000cfe76d8143014fe73d9310006bc6290541006bc64d85300069c6418d21006bc7059021006dd70d8d4218ebe30d9131006fb7059120004ff75d8d400067f65d8d2007fac32992321a6bc644c921004fd7418b10004fd70d
  | 21 => 0xe31d913001cbc7458d20005bf748854015ebc648c521046f6311853207cfc7258231044fe71d91100f6dc53d8d2112cff764c821046bc6459221024fe7558e21117cf3258e21006be405923226e7e30d952007edf7358f200aedc32d8d40006bf6490521024fe75593210079f648c531046f65118542007cf628c9300cef64018542055bc744c710006be515923220f7865c4110007cc628c930006bf64909100067c6598910004fd72d854001fb66190a41364ff725913207cff7690a3100cfc7058e21286f53118530046bf7459231046be6199021004ff7558321006bd70d912101cfc745872037ef541185430067f42d95101d69e74d8d42016dc638ca21004fd75580210cef54118542004fd7558f10044fe71d894318ebc6390540004fd70d8d2118edc3258e41046dc3158e21004ff755912126e7f72d9520006f46148520145bc745893101dbe748c9402e6f5411854000cff73d9130005ec7250521005df73c8530006f610d8532006ee74d8931004ff7258f10014fd7418943004fd7558d21004ff7650b100cebf725902101cff765902107ebf745932007ebc6459321005df73509211d6be5359232044fc7518543004ff715913001ebc6490521046dc6358f10004fd73d9121006f653185421bedf7359232006bc75d91312367d30d9510014dc735912007eef7518931005df7358941006bf64905300067f6550910005ef725854007eef7418931024fc7559021006dc6018d4201cfc74d893109dbc7448530015dc7350931116ee43d893133fe552c862101dbe7190540007b7715094011ef541986420067f65d891000cfe7018532116ee30d8931006df43d8d20005f77150f21005b4715094018ebc4358e41006bd65191301d6de43d8d42005bd7408530006bd645082107cfc7518930006bd659923202df970985301d6dc435923207cff7518930006dc51d8d21044fe7118b10116ec32d8e2101cfc74d8930014ff764c9200c5ec734842100efb61c411000cfe705912126f6e20d95201d6bc635094001cfc7458b1007cfc75d9232006bc601913110cfe7608510016dc638c52100cfe764c510006bc51d91310bcfe76c8520047ae64c8421004bf7458e21136f441d9321005bf7448530004fd764c720006bf645092127ddd754c530004ff755902107eef201891001cfe7458c21006bd65d9121005f771509320067c32d9520024fe75d8d10024fe7518532005ec7258d1007ef970d9320004ff7258e41006bc64189310eef850d81210057f7558d10014fc735902101ebc645092118edc63905210cfb7719902109ebf42d9130006bd6490510006f450d8542006dd65d8d421d4bd7699232044fc75d8c2100cfe70d91210067f6559120044fe764cb10004fd75d894018dbc7390a4100cfe709863225edd73d893007dec724c721
  | 22 => 0x8931014fe73987201a6be644c821014fe7359221005f77150930066dc6358d20024fe75d9321007ac6488521024fe7518941014fe7358642006bf52d913107eee4298a411d6dc53d8d42005df7348540006df4358e21014fc73d8542006be605923211dbe748ca2101cfe7458231006f47158d202eef541d854018ede4358e410247c7558021007cf628c5312d79e53d91301a6bc40d9132004bd74d8f100067f654852007ef5719891001cfe76d9130046dc6358e210057f7558131024fc7558e211d6df31d8d42046dd73185300067e73d952007ebc6159232024fc755913207cff7018940024fc7558241116ec3298632124ff7158910006de6018d21006bf7059021006bf65d9121007af648852100efa76c812007cfc7690910044fe7159021006bf6190540006f73118520174fd74d92310c5cc7348421005f7714ca21136f641d8542004fe7650530004fd76c8530046dc6358c210067c73d952001ebe6450721006bf745911007ef860582420febc4358a41044ff768c720006f675d8542006bf65191210febf4158a410c5ef724c82100cfc70d9232007cc63885210247e75d8b100067e63d9510044ff7598632005ef724c52118ebf73d9131006bc64d8930014ff764c721117cc324ca211eebf43d913207cff768c910006ee60189310067c65d8d200f6df31d8d21006df63d8142004fd7558642004ff7648540006dd628ca310febc4258a4118ebc53d9131024fe751854307edc6358f2007edc6358e42004fd75d9231005bf744c540006bc64189302bebf70d91301d79c4350a3200cfc7059232004fc764c940046bd74d8f100067c6558d10014fc764c521006df638c721006bf7458d10047e6514842126f6f72d9520024fc7559131004ff7650d10006bf7458d200067f658c510006bd42d854000cfc701853200cfd71d8d10006f573d8542006ef62989411067c65485100ecfd7648510006dc51d8d42046be31590210cef454185420fcfd7690721006ee52d8941004fd75d8143006ef7258d1018f9c438ca41004ff7650520004ff75d813107ede3258f21115ee73c8621006ec42d8910044fc7158f20006bf648c521014fd71d8131004fc7650d10044ff75d8c21017cf628c932006be72d9131024fe75d8e2107cfe72d8f10046be41590211eedf6418d4219ef86058132135f67618542004fd72d8f10004fd75189410067f6590510004ff7558242006dd53d8d21006df6518d2107cfe72986320febf42d91211d6bd4359232006bd50592320057f7558231006bc7458d21024fe75189430aede43d8d4018ebf31d9131006f550185420cef543185420c4ff764c621007cf724c530006ef6258131004ff7458d2007cfc7518910044fc715913218ebd53d91312757e76d95200067e43d95200057f7559120046f860580212d6b
  | 23 => 0x6f67318542006bf74587200467e75d8b1007cfc75189411bedf74d8d42006ec52d8930005f47150920005bd748c94101cfc74d8d20006bf64d8d21046be7418b1000cfc765051000cfd73d853000cfe7158f10005ec725854001cfc74d813107dec724c720004fd7559232005bd748c920004fd71d912034cff7159131116ec53d89312cdfb70591301d79e43d8d42006bc64d8d21014fc735832100cfe7018543004ff7358241006bf64907210067c6559120004fd7018931046dc634c71000cfa76c4110006df638852100cff7658231044fc73986422377410d9510225f77158d10005bf7458121006bf5059232014fe73189410fdbc744c521004fe7650910004fd75189310079c744c530117cc328853007cfc7418930004fd70d9131006be6559021006bd5459231256ed2018940006bf75d9131006f461c85300c6ed7118931006f7715891000cfc7058a41006bc64581310067c63d9510006df75d8d2109ebc42d9130136f74198a41005bf7458132024fc75d8132004fd74d8b10014fe735932113cff7058d1007ebf42d9321044ff70d8d10004fd75d8121006bc70d9131056bc41d814100cfc7018943004fd71d8d2018ebf71d9131004bd741891007cfc7418910004fd75d9310004ff7559310005df7350531006ac62509400067f7558910046f77018542006de70d8d42006be60d912107ebf6199232116ed53d8931006df735913200cfe7018941006f441d8520046ee2198a3101ebe64507200067f31d9520004fd749863208dfb705894034cff7650631046ee2158a41006ed70d893107cfe7650f20046bc415922107df57288421006be601912107dec7250c210067f65d91100bcfe7688510176dc30d8d41366ee32d8943004ff7558f2107cfc764c721006be10d913107cff7518910044fc7650f1012ddc7350b2118cff745913107ebf6450b2111ebc6488530004ff75d853200cfc74d8141006be4359321004fd764ca4107e7e759891001cfc7458d10005bf7458d21017db604c530047b471590211657c755823107edc3258f2107cfc7259130006ec411893101fb761905411dd7c75581420fef641586420febc4158642004ff75d8141024fe75d91310cfb740185420f6de7618d21005ec7258131006bc64589302bfb830d9130004ff75d8d421c67c658c92018ebc73d913107eee5218931044ff7598720006df52d8d21046f81058021006dd53d8d4207cff7598a410f6df30d8d210f4fd71d8d21006f76108530006dc63185420cef75418542005f77150a31024fc75d8131004fd769052000cff76580211d6de63d8d42186fa4058241024fc7558632006df735913007cfe72d9320004fd7418530004ff7259231046bc6459310024fc75d893107cfe72d85402eebf42d85400067e71d95202aebf6019130116ef31d
  | 24 => 0xd65d8d21004ff7558f100f6df32d8d212c6df30d8d4001cff7659232006bc50d913101cbe74d8c21024fe7558d2001cfe7458d10006ec62d8131006bf53d91210067c43d951000cfc70d911000cfc76c8510004ff74582210067f41d951018ebd32d913106dbc7458d20006f74118532006bf5459232116dc32d8e210cdf67488421004ff7159320024fc75d8520006bc72d91301bebc5459232004ff75d9110007d76318542046dd73d923126e7f30d9520006bd649863207eef7118931046f46188520004fd73d91100067c42d9510086dc32d8132337e741c8421006f575d85420cebc435902112eed3298a31005f47150a32005bf745893007cfe7298910046df7358e2103d7c7558d10006ef401893101cfe74586320febf41d9121007af64d8931004fe768c941004fd7650d211a6be54d9132005fb704c510006f75018542006ef62989300cebc431854213edf3058f10004fc7650930006ee10d8931004fd70d8c21346bf61191310047f7558910046bf605902100cfd73d9130024fc7558021046bf41185420febc43d9121006de32d8132006f6601854202ddc735891000dde768c9302d6bf53d91300079c63909420eefa60d8121224ff764c71007cfc768c941006ef6418931046f77418542024fc7559121006bd54d9131346bc4318543004f4715913207ebc425932001cfd715931001cfe7498b100079c648c531047d6718c5310f6dc3258a3107ebd7418910024fe7558231004fd7650e21006dd54d8d21006df51d8d210067f7559120006bd51592321bedd40d8d42004fd71d9320006de10d8d42014fe7398a41327e55148421007b4715094100cfe70189431d6df30d8d420c4fd73d8c2107cfe7650f21016dc634c920116ef30d8931006f55118542136f742d854226e7d40d9520065dc7359120006df71d8d21006ef3218941006ef52d893136fcf4218d42004ff75d893118ebf32d9131046f671d902108ebc41d93202d6be73d9130045ef76484210079d74d8d4209dbe740853001cfe74d893009ebf41d913007eee72d8f20024fe75d8b10006bf649893107efb205832107ebc425902100fea72c812007cfc73d9321006ec51d8931005f47158132006bf51d9131004ff7058a31005f576c8621046bf7459221004fd751853002ddc7359110006bf7459131004ff7650f21006f46318542005bf744c621024fc75d854201cff7650721014fe7358720004ff72582310febe72d9121004fd7098a31044fc7690530035be7418910006de75d8d42006bd75d912101cbe74d8f21046ee2158a3107eec521893001cfe7498632016dc638c940005ef724c540004ff7058632006de74d8d210cebc4218542006df52d8d42004fd7218540024fc7558f2001ebe6450821006dd53d8d40046f671d8c211bedf435923203d7c7559110
  | 25 => 0x286c400c001039000c15e00700502ec0120000010034002005003800c010000032805401003303a00782ec03404a001811c15b008023003605e00d00100c2004000006c00c01000f000400200a02980e800e00d0210058006000031a5a802c0220ef007800e0290008444000002004800812e0080be8008e8a00e000005000e032001000c150003005004804a00600100701f4000002814400200108a801c222026015001400000000700780c60130030008000000017800002000c068802001406f000001c004000006800409201a3650138006000004806c0f802c05180400340f300580b0172017000800400e02f00a880807e0ad0190068010009001002801a009016829c00c020000039c03c00800001782aa00000880c802200001700341140000c981e001a022003800172a000000000c000000000000005a05b008801002001507a028c02a04800083b008800000080d8028006002800401c0010000134006006004802c15c0000000038024116008811000400000d811400002d00602ec02a001000075806200e000856c012001010000809201604b80040021d400e00000040080000074000000000801857600400c801c0c81470020034044004000002811e36502480002bc0c5003000400e01c002801c00c002000000000c00f00500d8010003000041400200900080b802a085048800000008904000442b0018008000c35a00301300fc0560000000024008000151002c2d00ff003011842e031001000000800000800480000fc005007401c01d002001000c05c005000000201900c000007c13c06082c406a00b00e000c00000e008000000000803301e40e404656600100d2002010800000600001983d8002001002836c24e00501b003c00600e00180d8008094001000001002c000002151a00c000000004408f01400000020050040000066017000817000003d01480700b200a0050004004039000030c0b00415a8800c048002000003c06600201386600180be0740000012013004800404a00701f01bc0000f905f00080d4014005825802207400000640a402d001800000200200581d0000244009803443600800004d000801600680d8008000000000400000100000442e600d00d00000022130060000192001000017802e01e08b800001800000800141fa00000680fc00c0001a0006c0020a600982b40020020540034002000073000001602b00000240000df02a0138000000000000012001000000fc00a002005818000203016b0128000341000003406200400e80140b2000000802000600f0040000052022001809800800300a802003e00000081ec000017545006000201500d000000208007ebe325923207ebd74d8f20045f47150b10044ff7518532006df634c9210cebf7159021044fe711894018ebf30d9131006d
  | 26 => 0xc008009801400201500603200aa006002004402600601e00f8012102002801800a01e042001c00204e001801c00e000011800010e2db00705a877000d132801c0ac00b00000a00081d1001800002a00100c800805e00401f00f80ac00002f025401c01100000a0002026000017401002501d009406002a000804800c01600100e8006009013813400a00200e801c12600e04001c014a001014000009c0130f1800000202f009804800e001003000c00000d000800c29a32e00100d8000002000000c0022211ea027800205a000001400600002300040f8182053053819a0000240044000008000016010201702c001000c00602212b806600d0000070236009019805003800000880d435209f00180240fe00000304180262e000d802825000109700180480000098000000019001800401805800680a00300c10368304344040000007400a04f00180440840240020010086010039800000400002e80a0000033000807000004703b807c00200900080200040080038714054013002810c01605800f800020000200e800004e00000880b40060150208270048041005808c1e8016003003420600300000100020a4012800000007b017807000a000000800402400000100440160750008084002055058802000a0020008cc000000101000f400e0000002d900ae00103880ac004029032000000c00f00400e40000701bf00700020d9013801c004019000000800401c000800400600c000002801611b012803801a1a1005000c00001e03701ec00e05008680080000a900800a80080000f5001066604900a000800001d00000000000090000000024081050800003000400080001440c200800000ac008004007c02a00000100000c40040020000000002005000000000002400c401227e00b80280000fa00104400020000d280e4012006070801008400100300a40060c000c014001a0000bc80109ec03400000f800200f014800001400100081980080140118000048002007811800003101e801400c01d002ae0000c001097000000200b005003800006d03c01080080200128004002007001001034800109780401c0001017000c0be015000064005402d000113800000003e8068002000009000000c009000000801800c00080a00ea00500580ec430002028000000200000700080000b500f00100041d0001801c0aa001058800003005700d8000014161023800c00000100001640280040010050142029002004000008100104780f002202e803c03c06e000003401000b001000c00000900200040120d20000140022226018005c0040140000008004003000811000600011c00380060a400200100401da009000001c026002834000604700b800c04e007028009c0ae0b8000803c056070009801c40a02a0028c8801401a00100100000220e
  | 27 => 0x400001400ac01600a000001405c01a00781883a6014052019403403200680240000030000138130004004000009c00000a80f80c0018007019800e03500080000080b400181c000600b00203a803000000000000de00000c8c2000e014049801401e009001000404e2b200400ac03c000000000034e00900a00e0028014003003c1f60640038000004037001001c068005004804c46800000180580160050360338024b6d013812401203900a800416a0000d9800000800106e006801a0010072c2845805d03b006808a00a0b0801800602100380c0006007001800004401d00081040ca00101c80400240170000110008006004804013e00100509f43ca00c03880a40cc00006500680040460028104000030020802802800200280fc0a20583bc000407c00603f007001200302e801004403b001805c0100830010074042009000000000602012b8e0807e021000001c00600300b818c00423507282e40
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8bc841d9315007553d07102c91900637e1d638c9200055ac20a1b0a8400a5c855c363508018deea312c0988022f61f64085300065bc26ec9084200a9d84dc763508018bae639eca90062b3a0e70189310465b430e2a128200cb6631c54250033968c838a8498802b520d651854200556422cbb126200caf641c931484019aee7b8ac8990029da1730d854213572c16e7b0a847cea731190624c515d4885990c2a100335dcc715913238f62188823126200a5f855c36348401938e9b9ac6900022f61e105923200573c12a630a8400e1c6554c644c00195eec3a242108121fa17764c52000717a94a5b226000c3c65dd131480018b8e7b2ac8900021fe1570189310056b41821b0a8400e2f54950624c40155d09386c4988063e2017558d210051fc2ae0b204200c6c75d89604c4018deea392c888002ad60675590210045fc22e23126000acd83d44624c40117d0e286c8908030f1d764581310056b40cca31a8400c5c73d9542440111b90ea9ac72083e2f21d64509100061e3a8c8b024200cb5861c5425006353d07106c8988030f5d754d913100557c22cbb126200caf741c9644400199ee6392c6880032d20574189100045fc22e430a6000c7475dc56448045998e7b12849880237e0d74189100047dc02eab224000cb471dc1640846f93eedb9ac9190032719373591210045fc22e7b122000cad74d8a624c42355d0e31284a00032bd9072505210046fc1aec99620008bf845ce61c80090fd0bbb286900023de0575591320056bc1acbb0a8408ab6819cd6408401938ec39a84a0002b360c50d89313ad4e432e91926019ab684cc861508111f10ea82c0108021fe15768c5200061e32ee890a400487c855c363504015ad02286c6a1002a7e0d65d91210061e32ee8b1a2000c3f75991608c8010fd0e3aac890003391cb7158d1000573408a1b126200caf64dc9604c40155b05306c8988030fd9574085200043f43ecab22400f8be87d51648c8090f90abb286900030fdd764581310062fb2ee6b224000a9d83d5164084111790eaa2c81080317d97735911000667b9ee4b222000ab48150b61500631790fb2262908022fa1b74485300061f3a6cb1922000c6c65dc96444007179083b24298003331db724c5300061fbaec8b024200a9d84dc76348433d2d07218c2a1002ad612701854248f4b3a6c630a8400aae82983644c40147d0b986c8909cead21032185421bd4f42041b1a8400c6c651c9314812999ee431ac2a10022fa1f64485300056c402ca31a8400c5d751d76350801938e9b1a62880033518c715814200672316e2a126200c9c735d5648c8018b8cbb9ac48803eaba0a305902118d4f418e1b226200ae880597624c4e7d4884100c2a11cf2d18871509400061fb2ee8b0a4000ad581997635080195ee5ba2c7108123be1d52d8941
  | 1 => 0xee438ac8990022fa1c50590210062e32ee6b0a4000c5f75dcd624400153908b2ec6908662fa1e105902100566c14c831a4200e1f54953634840117b0e106c898822ad20570590212ae4e3b0c898a600087e87d9561480ef53b07328c898003391cb71591310061fbaee8b1a2000c7765dc563480031f100baac8990121f21576085300043fc2ae1b1a84008be87191624c0011db0e280c4988023de057650d200062e39ecaa124000d94731c54250001968e838ac6900030fd95748c9101d64f43ee6b246408cb47159142c400717908b88c49800a3720d71189400063c32ee0a124000ccf631c931484111e902baac898003351cf715912000657ba6e4b1a2000a9d84143634840153b07328c8909faaba1864189310061e3aac8b0042008de8718d61508011df0eb10c4a08032b10472591100cd5b4244030a8400cac64dc9614c0010fb0bbb2829000327dd0735912040747986c831262008f687143615081d0fb0e196ca900022fe11764c9100062e32ee6a124000c9f835d062440015cb04280c2a108ab3a0c70d89310061ebaea9b224291e9684d8c615080156b01210c2a1022ad20564504210063632ee498a400087f855d943480011df04baac690802a7a0c10d91210065a3b6e2a128000cb7741c5644c8af53b0638ec8980030f1d065585200055ac0ee5b22600487c855c0625041f1d904b98c4880022f61371582321be4f326e6a146200c5c65dcd214800187eebb22c4980032dddb74484211d64e31ae91928200c3c75591608c8031e902bb28588002a761075d8d2100556412cbb2260008bf845c7604c80117f08baac688002bc20165d85420066bb1ee2a1242008f7815d56344001938e9b9ac6880021fa1c6558d100055a40acbb226000c6f65dc963440010fb0bbb26290003a561363185420062e398cab22200487e87dd5644800187aea3aec890802b560e60185420061fba8e8b122000c74651c5644800159b07080c4988121f215768c5400061e3aee8b1a2000c7475185605080717b0e31482a08030f1d464585300054ec18ebb224200a7585cc3615080155b0932ec4988031bdd762581310064fba6c6b0242008ef825d9434840117d0e282c919002b3a0850d8d420043f43865b2a4000ab681141648c80117d0e106c8908028f21173d951000656b90c520a8200da7621c5425000153d07300c89080a3720d76509100052e41ae9b2a200fe2e52d4964084011bf0eb28c6a1002b56066018d420447a40aeab1a40008f7815d5644800193ae9b1c64908021fa1c655911000557424ca3126219db3601c542500015b100b28c6908032d193714c9210c567418203126200c5f75d8d6048401968c9b8ac4980023de0575591210061f3a6cb1924073ab7840c8615080159d07106c4a080335dcf7159120006363aee4b222003
  | 2 => 0x165185422bc5e436e8b0a6000a9d841c7635080717d0fba2c6900032d9cc715902100c7c402eab0c8419cb771591410840153b07102c81080327d9373509311355b420e1b0a840fcac7299163084015a902b2ec6a10032b193725913100c6e432e610a60018be86dd2215004d96cc9b8a84108033318c7258d100051e42ae0b246400c7475dc5634406f59b05b8ec6a100327dd073589100074a320c298a6000c9f64dcd60484018eecbb8a8490002a72116518d210445e43ac8a1620008f7815d5634800187ecbba242880c7271cf64505310055ac08a0b246400aae84997624c4031790cba642a00030f1d47458d2038d67436c710a4200c7575d47615084559d06086c4988633318c724c5210061e3aee8b122073ab681d92428840187ecaba46490002b320d62189100066a31ee2a124200d8f741c9314c01f95d0e31284a023ab9e09731854200477438c4b026289ec74218c615080195ee8312c098802b560c10d85320064f3a6c71922000cd7731856050801998c4b84629880327d9373509210045f43ea6b2042008bf845d563884011bd0e086c69095f279db648c9300145f43ec8a1a4200d9474dcd210840155d09080c4988232d1c5645082100657b26e498a4200a9d83d51648c83356d08100c2a10022fa1f64581310045fc22eca122073cb4641c542c80ad53d0db24649800237e1d6418d210065bc0ae831220008bf8750b615001f1d904bb28688003271cc645812100666318e4a0a42008df835d9434800117b0e286c890a56ade11611854348f4a216c630a843aa9c835d5648c875938c6ba46490802b520d611852001c5f426e2b046400ab68390861509275cb05328c2a1003279db6418d210045ec3cca322620487c855d9434400199ee63128498802b9a0850185420066bbb6e69084218ace83100624c4011df0eb28c49889aada1353d85420054ec26e1b1a8400c6f651c9314404d968c9b8a849800e2f21175587200062e3a8e6b222000e976390c61508091bf0ea9ec6a10032b1d372589100054f41cca3224200cb7641c5624c033968c838a8490802abe0965191300046fc1ae430a8071ccc611c9314c0331790eb226210802a7a0c50590210064e39ec8a12405ac9e73d92414c0015ab07328c2a1002ade05755902107c76412eab18421f8bd86dd1210840196ec838a8498002a761050d8d4200746398c4a128000cb484dd9210843356908a98c2a1002ad61353d85420c666398c4a0a62088de87d0d638847553d06082c91900e2f2117558d2100637baee4b2220038bc841d9215000717d0fba2c68800317dd463581210045f43ec8b1a42028de839d9424406353906b2482881c31ddc46558d1001c6f43ec6a1a4208cd4615ce615080156b0339ac8108121f21570d8d210051ec2e61b224200c7765dc542440019c
  | 3 => 0xc90a8008cf0615c0214c0e756f0cb8c85208021fe1570d8c210064e326e690a6000a9d83d53644c4051b9063b284980022fa1f6458931006ca3a0e690842028dc835d06244001938edb9a84a0002ab60a65191210045fc22e630a4090ad68398c6150801938e9b9ac4880021fe15769052000557420a03126200c74651c563480019a8c638ac690002b620165d8d4207c76412eab1c8400c3c74d9562440015cb05180c2a1002ab20965191312bc5fc22e7b1280018bc865d0215000153b08386c6a100399d4a52d85420072ba9ca630a8400c5c731956244033d4ec231284a0802aee0165d91210066bb9ee2b224271dc6729c6328c401968e9b8ac488002b360f541893100747b20c518a6200c3f75191614c00153906b2ec89080317d9773485100054ec1ea9b224200c3d741d3654801196d0e38ac8108031d19771591200063c32ee098a2000cb4641c532484018e8ebb8ac690002a761353d8d2100636baea5b126000ab5848806150801968c838ac890002aee0165191310061fb2ee890a4000c3c75d91624c0015c904b08c2a00022fe11755872000556c24e1b12620487c855c363508019aec638ac0a1002a7a1265d8d2100656310e2a128031ab5811c3644c44d56d08286c2a10123de1d51d85420045fc22eca1c4200ae581140624c40117f08bb28690803a918b71509400146f43ee6b2242008bd849d9314800156b03218c2a100317dd773591200043f438cab0a4000cd463dc5605081f179093b464a0002a7e0d715923207f17296a4b246482ae581994624c4090fd0dbaac48821f39dc861581420046fc1aeca1a200fcac625d0215003396ec038a84a0002a7a1370d8d210047bc3ac230a4031ab581dcb644c4010fd0e32ac8900672d9907150a320063c3aee0b1220198bc87591210840153d07106c8909379ad8b65c812000656320e4b026200ad58314061508011db0e286c4988031d19471509100066bbb0e690842008bf845d5644c0018eeebb8ac6901cf2dd907150b200062fba8e6b2220028de87dcd644801f958e4b2286108063760f75d893001c5f424ec98a4000acf83544624c40193ee9b1a6290802a761020d8d210054f430c831a428ce944354c615080717d093b24298003391cb71591100061e3a6cab1a4000c6f651c9314800117f08baac898802ad60665191210445f43c86b262000caf741c9644c511d4885100c2a10dea7a1070d8d420064fba0e6b22200087e870cb654400196ee9b8ac690002b5205638c9201bd4f426c71962000cd473185605080187eeb322c010803331cf624851040e573b6c831262008dd839d9424400156f08b98c2a10032918871509400045ec38a1b22620087e87195634800187eea3a2c6900030fd97744c51000637b28e4b222000aad84083625040153b0932ec690802bce0
  | 4 => 0x350833968c838a84990023761e20d8d4200636b90e5b2a2000c5f7518d605080155b04282c8108063e2017558a3100566c1c803126200a7685cc0615080159d04386c6a10022fa1b744c5210056dc02cbb1a4200c3e7419462440015ad06286c2a10022fe1d651912100637b2ee498a4000c3c74d95614803396cc838a8488002a760e65d91210065ab20e2a14640087f855c36348401c5ea5296c898802a7a1260d8d2100667b18e498a2000aad84140624c4090fd0bbb28488003351cf61485200061e3aec8b024200c9c74d8d604840159d05baec6a1002a7a0f54590210062ebaea7b1a8418ccc631c93144101d1863b20c498802bae0165189310056b41cc1b0a8400ad58114363484019ace7b0cc2a10032bdd0628854000c76412ec98e4031c9c63dd1314840153d073aac8108023be09764c9100063c3aee0b1a2000c3d751d7644c0018eeca38ac8900022fa1c64581310043ec3865b2a2000c5f65dcd21480031bd0db9a4298002a7a126518d2107d56412c8a12203aa9e83141648c80187ce9b2842880038bd4a52d912101c5e422eab1c4200c3f65dd1634400195ee9b12c0988021f6177650d20006563a0c490a205aa9e831d7644c00193ee9b9ac8908122fe1d54d913100556c24203126200c3d75d53644c1259acedb18c2a10021fa1c65589100061e32ae8312200487e87dd5634406353d06086c8988030fd97744c5200056ac1ea3b0a6000ccc731c96444001998c7b9282908dea7a1210d8d4200572412c230a8600caf641c9614c0018becbb9ac48800637a1b73509300065a3a0c290a4000c5c75dcd64480011ef0eb08c2a18223d2057650c210243f43eeab046237a9e841d763508090fd0bbb286880022f21f644853000556c2041b126237c9c64dcd424c0015ab07386c2a10df27993735082100637b2ee4b222000c9c7418d60484014ed0a190c2a10023de1d631854200657326e49884257a9d83dcb644c0111e902bb2869008a37e1d628ca310055bc0acbb226000a3f855c1648c801878cbba2c6900023de057650d2111572c0ee9b126200aaf8254d64084011ef02baac898002b560660d8d4201c5e424ec10a6000ccc631c963504090fd0fbaac8881e339dc462581310062fba8e6b224000cac741c963440015c902b10c4980123be1d52d893138ce743ee690842048bf87553644c80155d09086c4988023761e6518d4207c5f43c86b2642088f6819d9424c00193ced3a46498002ad60450d91310054f42421b1a4200ad681997635080153d063aec8908032799373484210047bc0aec992200fccc7258d31c84018decbb926288002b520d61185420062fb2ee6a122019ab6840c0615080155b09300c498802a76126518d210447c432e010a6000aac84588624c4011bd0e286c6a1002a7a1353d8d210046ec1ce
  | 5 => 0x880e3e60375d85400074bc20c630a8400cb4631c542500015af06b28c2a10021f6177058f210cd5a4266030a8473ea66198a429046353d06286c8988021fe15701854200727a94a5b1a420f8ec825d563904011bf06baac890803171d463581420045f43ac89084200a9d848436348411968e2b22851883f2ba1072591100243e42aec10a8037acd82dd7635080153d09300c6908032b1d37258d210455b40ce0b204200a9e8314364484015af02b28c6a1003a519363c85210045f43ea7b224200c5d731cf654400156b02282c8108121fa177058f210061e3a8e8b122037a9e84143635081f1d9043b2629006333d80724c530006e2396c298a600087e871d562440011bb0e086c6a10023be1d64189310046f436e6a12428eae78258c61508014ef0ab80c2a1002ab60a755902139f522106430a8400a9d831c3644c4018b8e7b2a4290003331cf725911038ce7c3ac51946200c5c73d95644400153b073aac81080333ddb73484210055ac20a030a8400ad58388361508011bd0e086c6a100e2f2117558d100056dc02ca31a4200a75850cb615080117d0e322c0908028fa1072d951000557420a1b126200c5c731956148001d1ee631284a000339188715093100717aa4a9b126200c5c75d8d604840117f08bb28390002a7a0f72d912100746320c710a42038bc845d9324403159d07a08c498802ad61352185420ce5a38c86b204200c6c651c9634401f55d04282c8108038dd4651d91310243e42ae030a6400cac84dd9210840195f09bb24210802b3e096518d2100c6e41ae5b0262008ef825d5644400153b09306c69080317d9773509200064e3b0e898a6000a3f845cf65480014d90ab80c4988030f9d365085200cd5ac3c8430a84008bf845d563484ab5390ca98c8980121fa1776505200064e3a6e6b1a4222ccc63dc931484011f700baac890803279d9748c9301347bc0aeca162073da4421c542c8401b60e3b8284a01eeb9e0574189310062fba8e6b12200487c855da314805117b0dba26210802a7a1050d8d210045fc22ec98e4000aad82994644c4015ab02286c6a1002b920562189430043f438eab222000cb7741c5644803159d06280c4988121f215768c9100062e3a8e6b224000d8c641c9314c001c6ea328ec8908023be097558d200055ac0c8430a8400d9a709d2324c0018e8ca38a84901db27dcc64589300243f436eab0a4000a7585dc361508011bf06baac888066ada0e43185420062fb2ee6b0a4000ae482584614c0e58dee432ac690002a7a0e60d912100c77436e498a40008df835d821500010fd0e3aac6880023de1d61185400056b41c4030a84028dc835d5624400193906ba0c488003171cf654851001c5ec3c8430a84008df835d56348401b2ee638a84a009a2fe197190a410c56741ea23126200adb805946
  | 6 => 0x727a94a5b1a8400c6f751c963440031f100baac8909d327dcc64585300054f420ebb1a4200cd7631c542484018eecbb8ac8900022fe1d65191300045ec3cca32260008de8718d604844559d06286c4988122fe1d54d912139e5a320e2a164200e9463908615081156d02282c81086372d80724c53000556412ca3226000cd7731c563480051b906bb042a00030f1d6645802100556c3664b2042038bc84dd921084011bf06baac890003171d4635812100477c12eab226200ab481594644c0011df04baac72080e2f211760853000656ba6c410a8000a9d84d4f63508015d700b2ec498802a720d65191210055dc02cbb226200acd83d04624c4011bf06bb284880de3721f63509210455b40ea8b204200ab48150b605040117d0e322c49895f271db644c53001c5f426e6b162000a9d831416408401938c8b9c42980023ba1c50d89310053ac2e6030a840087e87d95634400117d0e286c898803175d475d8d2100566c1ca03126200aaf82594644c401878caba04288002b360c40189310054ec1c41b224200cb4641c5624c0018d8ea392c688002ad610301854200657b90e8b1c4200a9d8484363508018eeebb0ac0a10222fa1e43590210146e41aeab2242028dc835cb60504011db0f320c4988121f21570d8c210061e32ee8b122000cb6631c54250401938e6b228588066ada12301854200556c2421b1262008ef825d5644c00717908bb44298002b360e701893100556c14c03226200cb7641c5424c40155b08286c4988028f61432d91210046fc1aeab226400a9d8498063484018baeba9ec69083e3b20974189100447a40aeab204200ccc73dc9624400155d0532ec8988de2f219748c92100656326e4b026200ab58790c61508051bd07b92c1208232d1c56450a2118c5e436e8b02627cea431190624c4af5390ca9ec89800e3ba1f625093100557414c03226200a9e8399764484111b90ea9ac610802ab61260d893100733a8ca3b12620fc6f759d4624c4015cd03200c4988032760f7458e210043fc2ae1b1a8273ab682908615080156b02286c890802a7e1165d8d210046fc1ae5b028200a6c85588624c0010ff0abb284880023ee017558d210047743ec4b02620087f855c0614c83159d07280c498802b360f54d89310046f43ec6b0242028f980dd7624c0010ff0abb48488002a7e116518d212353d400e7b2a2000acd83d4b624c03f1790dba2c090802ae20165191210062e3aee6b12200087e871d5600840196ec838a84908031b5d752d893139ed3b88e89084256c9e7654f644c001b28e638a84a08030f1d06558d100052e41ae9b2a4000caf76dd121084e7968e438ac8108030f1d464581310055c402ca32262038bc845d5634801f17d0f21ac990002b520d65d854244f4a2186430a8400e5751947634840159b07100c49
  | 7 => 0x7c855d932440019a8c638a849080327a137358b102bd4ec18ebb2260038bc841d9414c00196ec838a84990030fdd464581210054ec1ceab2464088f4815d5644c80155f04b2ec8980028fa1730590210045fc22eca1a2000ab78454c6150801c3ea729ac81080237a1c63581420047b43ec2b0284008f687185605080153b0738ac9190023de1d65185420063bba8c2b028400c9e745d763508019a8e7b8ac488002b360c70d89310061fbaac8b046400a7485584614c0031ed0db8a8488002a7e0d65191210ce5a320e2a1260008df835d932440011bd0faa6c6908032bd9372585301be4e326e6a126400c3f751d1634400196883b8ac121002ab60850592323d76218aa23126200cb6861c5425000317908b8ec0a10121fa177058e210065ab26e2a1842008bd87d4f644840153b083aec6a107e2f61c20d912100477c12eca122000c9c741cd6244001968e9b8ac69024ba5a1363d85420061fbaceab246400e946418f214841156902b9ac810866ada1270185420043f438eab046446c7a76d9710440e736d0fba2421083e3b2097650c213e747980c83126200cb5711c5648c8011df0eb10c4a1866ada1250185420054ec1cca322623ac9e635d2329041136902ba464a08030f5d074d95100045ec26e6b162000c77651c542440051ed0db8a84988023d61e63185420055b42421b0a64018bc865d23250001958e9b92c68800387d9553191303fd57424c8312620fcac825d0624400156b09a98c2a1002a760e20d91310061e3a8c8b1260048df8754f635040187ecbba2c690002b560e60d85420062e32ee6b22203a8dc86dcd6050801968c638a84a088a3be09764c7200074ac26c7b0a84008bf845d8214c00199ee63128298802a760e60191210045f438c8b0a6086ad68618c615091bd2887298c2a10030f5d475d91310ce5a320e2a124000ab5819806448401938e7b22c0908121fa1f75582322d64e39ec8a1260038be84dd9214c001d18c83146498066ad21152185420064e39ac8a104271ec67118a314c4018e8ebb0ac0a10eaa7a0e7559232006e4396e098a6000a9d84dc36348401878ebb22c2980dea721a748c9300074aba0c630a84189cc825cc214c00717d0fba2c4880eaa720d64509100066bb1ee2b0284008be87d91624c00155b05182c810802bce0165d85420045f43ec8b024200d8c741cd210840156b03382c8108022fe1176885300061fba8c8b126000c77651c563480e3b8ee439a42108022f61c62905400046fc1aeab122000a6d850cb62504018f2eba86c0a10029be1570189310055b40ee5b22600fce652dd9210844d968c9b8a8498802b920562189400065a3b0e2a128000cb764dc5624c00156d02386c8988021fe15764c9100054ec1ce0b2464088f4815d061480111ed0e280c2a10030f1d47458d100
  | 8 => 0x4baac8989f72b9d864189310146f43ee6b222000cb7761d12108517d4884a90c2a1216b9e0961185320243e42aed1928019ab684d4c615081f1b90ea9ac72100327dd073591210043f43ecab222000aae82143644840717908b90c298002b5a0e65185420046f43ec6b028400a9d83dcb6448411179093b042a00121f21576905200065bba0e2b1a40008bf845d562440015ab03328c6908023be1d62189300063c32ee090a20008bd87d4d64084018b8e7b2ac2900032b9d362989310fc5ec3ec91924208c77759d461508015e100b28c2a108e2fe1d6290a41006563a6c490a200087e871d5608c40156b08386c2a10023ee017558a312b64e398c83126000c3c7419563480018b8ebb9ac888002b5a066018d4200556c10a1b226237acd821c363508111e902bb28518802a7a0f54d91210063632ee4b1a20008bd87843644840187ecaba0c4880666d20574085400045ec38a0b204200d8c741c9314c0051b906bb28588002a7e0d70590210243e42ae030a8400c9c74d8d31484011f700baac48809aada1020d854207c76412eab1a2000cb5641c5424400187eea322c0988033518f7158d420066bb18e2992420f8ec825d5644c00187eebb22c298002ad61250185420054f41c40b2042088be87d5164084014e90ab80c2a10c6a7a0c75d9131006d2310e2a128000c9d84dcd62c400195ec8392c098802a7a1371d8d210066bb9ec2b028400c3c655d021480011f700baac898802ab60850d912139f534148430a8400ad58199463508011db053b262a0002ad602431854200667bb0e69084200c77751c5644801f1d904bb48498802b6e0165d8d420045f43c20b24644dc7a76d9720480011eb0e280c2a100317dd76358142006563a0c4b026200c3f75dd16244001958c83926290a27a59d0631854200572c08a1b12620f8ec825d5644400196ec9b8a8498002a761375d8d42005734146030a8400c77651c54248001878cbba2c29007a3721b73581210046ec38a1b1a42008df8759463484d117d0fb2262908032bdd3725913112c6fc32e31946200c5c65dcd64480015ab0732ec2a11c6b3a0b638c7210054fc1ae0b246400ad6839c361508019aae7b0cc2a100339d8871509310146f41cec90a8055c9e76192324c00155f04b2ec8988021fe15760854039f52214a430a8400a5f835d365440015cd04286c2a10022f61e105902100572412a630a840faae82141648c8018eaea3aec2a1002ad60663191211365a326e2a124200cd473dc5644846f53908b1c649000e2fa1f74587200045fc3ec810a6089e974018c615080159906b10c4a080a3720c76485300c56741ea83126200ab5848c061508019caa3bb24210803171cf65589100064e422e7b2442008dd87d53634840153b063aec8988032d1d37158d214b567c1ac431286048
  | 9 => 0x54592320064fba6e6b1a428fcd67618c61508090fd0bbb26488002b360c50189310246fc3aa7b1a426d8de87d8d42484090fd0fbaac01083e3b20975189300045ec24ec90a6000acd82994634840159b05300c69080327d93734853000573408a031262088f4815d4614c00196ac9b8a8410803a3190628c53107c77438a031262028dc835d562c4001caea729ec2a10029ba1770d893144f4a420c630a8400c5c751cd624400153b06082c919002b360850d8d4200567410a1b1a42018bf8759241440011bf06baac5880032d19071591320043ec2eeca1a2000c9e83dd163884e756d0db26429080e2f21176c85300055ac242030a84008bf87594644c4ad53d06328c8980031b1d77258d100445e43ac8a184289ec44218c615081f55904b82c8108223d205731852000637b28e4b1a2000c3f7559160084011bf06b88c4a003e3ba0a764c5400046ec38a1b1a8400c6c651c9314400117f0fb246490802ab21162189100066639ee4b224200a5c855c363484015ab06286c2a10021fe15768c5400047bc0aeca12201e8dd87043634840155d04286c89880339dc87158d200063c3aee0b224000c3f759d5640847593cecba6c6a1022ada06435931000477c12eab1a20048f787547614c801d1ec831c4290802ad21161185201156741ea9b126200a3f845cf65440f3d8863a08c498802aba12601893101c5e422eab1220008ef87588624c4014bf06ba6ca900022fa1f645853001c76c16ebb1a8400aaf84594624c40717d0fba2c6908121fa1f75589100045ec38a0b2464008f787584614c01f958e4b22621089b2d9937150a3200667b98e4b226200ce552dd92108401938e7baac9190028f21173d95200062e3aec6b0284048df8754f635000156d09080c2990033518c7158d420056b40cc1b1a84008df835d9434840717908b98c2900062fa1b744854000536c2ee1b126200c7465dc542440018eeea38ac6901c733d8c724c7100447a40aeab224000c5f75dcd6444001ccea5290c2a10031d1d47158d200045e432e810a6000cac641c9644c40155f08b10c4988022fe1175591210056bc1ac230a8400a79801cf6544001878e9b2a62881ceada0a431854238e67388c518a6200aac82597644c4019a8e7b0ac0a10023be1d62189100062e398cab2240018be86dd1315000187eebba2c690002a760f72d91310051e42ae0b2042018bd84dd761500018e8ea38ac8900030f9d365189100047bc3ac230a8400c9e74dd763508af17f08b98c2a003eaba1b62509400047dc02eab0c8400cad64dc9430840153b06282c919002b5e0565d8d4200c7c402eab226200ea4621c542500011eb0f328c2a1002ad61332185420cd5b420a030a8400c3c655d2324406f938c9b9a84988032dd9071509200061fbaea8b204200ae582143615081f1d9
  | 10 => 0x31a8400cb574d84215000117b09bb24298003711c8614c5300066a190e2b1a40008be87591310840156f02b28c8908032bdd37258d2100556c14cbb226208ce651dd92108401b1ee839a4210802a76126518d420061fb2ee8b122000c9d64dcd42084031f50db824288022ada06755902107d56412e6b204200c3f655d021440019a8e638ac8900de37a1e20d8d420447a408eca12207ce8c31190624c4018daea3aec498802ab61265189310c56741c203126200cb474d85214806317d0f086c8988032b5d342189100c56741c803126200ab484584614c801938edba2629800327dd3735891001c5e422ec98e4000c3c655d232480011bd0e286c690803271cf64509210064e31ee8b1a427bae781590624c4010fb0bbb284880029da1770d85420043fc2aeca1a2000ab5819c1648c80196c8638ac8990021f6177058e210046ec1ee4b048200c7865dc121480015ad07300c2a10323761f628c9300047ac38a1b0a84028dc835c8615000153906b82c81080387d4e53d912100556412c920a2000e9574d8c615084736d0c38a84a08032b593724c4210043f43ecab1a4000a9d831436448401d488231282989c7b10c65118931006363a8c4b026289e944218c61508031bd0db9e4298002ae20165d91310054ec1821b224200a3d841cb654400156d02286c8909cf2d9c8715902107e56312e931262008bd8799464484090fd0fbaac690002a7a1020d8d210047dc02eab226400cb4731c564084019a8e630a42900022f61e10d9131006363aee4b1a4000ccc7318921440010fd0fb2ac4880031ddd771591200053b42865b0a8400d97731c5425040156d03382c91900333dcc725911038e66318e498e2000ad683140615086f938c9b9a84908030f1d365485100061e32ee898a2000cac641c964440018d8ca392c88800e2f21173d89100047ac0ceca126000c9c64dcd6048401d2ec7210c2a101a2f61f61905400061e3a6cab1a2018ccc73189424c43356909398c2a1002ba20165189311d54f41ce0b246400ccc761c9314c00193ac9b9a4210802ade0565191300455a40aeab204237a9e84dd76350801958c9b926290822ada0643590210051ec2e60b204200acd83dd3624c4019688638ac899003a518e43185420055c402cbb224200c9e761906348401878cbba2428800363d90724c53000556422ca312620087e871d563480015cb03200c4988063721973905300043fc2aed1928000c7465dc56348001958e9b12c09880335dcc715912000657ba0e4b1a2086d94431c5428c8010ff0ab80c4a08032b19072585300043ec2eec99220008df835d942c40011bd0fb1ac2a1002ade1152185420055ac26e7b0a8400c3c74d95314800717d0fba2c7108022fe117650d2000637baee4b1a2000c3c75dd163480011f700baac6880030fdd7
  | 11 => 0x100002c0b8000002bc0a003010000050000240e0e38080b04e8610c503a004120030040200c00610c0240d026002e280000815c000018000b0000028190040d8200020380180000300202cb4800000d50000010060440380c02e0300380617a1b4000000060240081200400c0281800004c0e1a80340105a000044988000000020580600800c1c4090c80021041082306a01c008000740240600c004004058110540181287f04402c000000026ec140000280280029d07205057c1f04ed641100a07e204020e804a10000865006000130010320081180a0620001881a00401404847002ee09e8050020007d029012004012a3012052109e60380001a80b00e3d80081b00002c0083b00404806000174070008130040001f82a000054010026ac1b4060010123e400810000068033de0120081814b0000046a02c0d2004098080042780580004a0000400200000c0197a03605c568020683280706d0022d80005201c030b68090040000111703c00c178870020040002000e22c0400206c0040291e066014000234800440019c004ac80004202e024b981300406c040040020281202400202c0400002e0780500000e0f44481f11000c0a8000d80040301e0c20840700d0020000102401a048158110020faac8254d64084015ad07106c2a10121f21570189310054ec1ea9b22600487c855d9424400117d0e106c8988023b61e65189310047bc3ac230a640faae829d564084018d8ea392c888062b320d511893100477c3ac431280008be87191634840193ce9b1c6490a5f2b5d3629894348f4ba06c630a8419ab684d48615080153b07306c8908122fe1d54d91300061e3acc8b04643ac9c635d2325000717908b8ec09920f2ddc464589310062e32ee6a12200f8bc87551648c8051bd0fb9ac58800637219738853007d57416a8b204200c6c65dc931440010ff0abb46488002b3a0e20189410056b41ccbb0a84028dc835d564480011df04bb286880232d185740854000557424c1b1262028de87dcd6244001938e6b224210802b5a0450d8d210055dc02ca322420487c855da42441095cf02b10c4a080327dd0635812100567c1ae83126200a3e850cb644847553d0fb9ac919002a760c50d91310061e3a0cab122000aae82994644c4015ab07100c2a10021fe1576085300063a32ee2a124000ce7721c564480b5938e7b224298002a7e0d75592320062e32ee690a2000c3c74d9521480015b100b2ec69080a3720d755911000566c10a1b1a42008dd8799463484015ab06086c2a10023761e20d8d210046ec3cc831a4200a5f855c3635080156d02286c8988029d61432185420045fc22eab1a40088bc87551648c40717908b9cc390002aba1020d89310054f424c831a4231c9c73d91424c40196ac9b8a85190022fe1176c85300056a40aca
  | 12 => 0x1e0ac0b00300607c000000a60000680204e004be0000142cc3281b0240940500004801c22008000428278a50ae01400800010000120090020500080f0340001b80e00000c0d03b15004c75000010034038110960000000000209c3c0000020ac060070041940201f0180643582d0ea000010110045f4000030062781b0000100680582d0f200409817014010010070d80e4028183d40502580a0f00350980900a301bf8000200080005001c004120030823b40005705601007011052004060000060a00c80000002c000080023c40184701618c2981303a0442621e00c0b00981300a0e8030c40002d40100000023c040790a200c0580100002c168004d2064020040180002800231c00c208d300003401803016bc4
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x62800a0080002cf9c8473104625053139ca92498494061508018948320574189100072119072185314c0e7a2442614321854200721dcc621c54250001a8442a0e2018542006a110c8254c6150801a1443614321854239d29a4a631c54250001c8473188715094039ca9249849c061508e72a492610301854239d29249641c5424400149493618715094039d29a477418a2150001494935907150910
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x94c
  | 6 => 0x94d
  | 7 => 0x94e
  | 8 => 0x2
  | 9 => 0x138c
  | 10 => 0x138d
  | 11 => 0x138e
  | 12 => 0x98c
  | 13 => 0x98d
  | 14 => 0x98e
  | 15 => 0x3
  | 16 => 0x150c
  | 17 => 0x150d
  | 18 => 0x150e
  | 19 => 0x9cd
  | 20 => 0x9ce
  | 21 => 0xa0c
  | 22 => 0xa0e
  | 23 => 0x209
  | 24 => 0x20c
  | 25 => 0x20d
  | 26 => 0x20e
  | 27 => 0x140e
  | 28 => 0x154e
  | 29 => 0xb09
  | 30 => 0xb0c
  | 31 => 0xb0d
  | 32 => 0xb0e
  | 33 => 0x1409
  | 34 => 0x140c
  | 35 => 0x140d
  | 36 => 0x1549
  | 37 => 0x154c
  | 38 => 0x154d
  | 39 => 0xb49
  | 40 => 0xb4d
  | 41 => 0xb4e
  | 42 => 0x1449
  | 43 => 0x144d
  | 44 => 0x144e
  | 45 => 0xb89
  | 46 => 0xb8c
  | 47 => 0xb8e
  | 48 => 0x1489
  | 49 => 0x148c
  | 50 => 0x148e
  | 51 => 0xcc9
  | 52 => 0xccd
  | 53 => 0xcce
  | 54 => 0x15c9
  | 55 => 0x15cd
  | 56 => 0x15ce
  | 57 => 0xd09
  | 58 => 0xd0c
  | 59 => 0xd0e
  | 60 => 0x1609
  | 61 => 0x160c
  | 62 => 0x160e
  | 63 => 0xe89
  | 64 => 0xe8e
  | 65 => 0x138956
  | 66 => 0x249
  | 67 => 0x289
  | 68 => 0x16c9
  | 69 => 0x1849
  | 70 => 0x14c9
  | 71 => 0x2c9
  | 72 => 0x150996
  | 73 => 0x3c9
  | 74 => 0x409
  | 75 => 0x1709
  | 76 => 0x1889
  | 77 => 0x1649
  | 78 => 0x449
  | 79 => 0x9cb56
  | 80 => 0x4c
  | 81 => 0x124c
  | 82 => 0x9d5d6
  | 83 => 0x8c
  | 84 => 0x128c
  | 85 => 0x589
  | 86 => 0x10c
  | 87 => 0x1789
  | 88 => 0x18c9
  | 89 => 0x180c
  | 90 => 0x130c
  | 91 => 0xa1496
  | 92 => 0x4d
  | 93 => 0x124d
  | 94 => 0xa0d16
  | 95 => 0x8d
  | 96 => 0x128d
  | 97 => 0x168d
  | 98 => 0x12cd
  | 99 => 0xb0211
  | 100 => 0xb0216
  | 101 => 0x140214
  | 102 => 0x154215
  | 103 => 0x155416
  | 104 => 0x28c
  | 105 => 0x184c
  | 106 => 0x16cd
  | 107 => 0x40c
  | 108 => 0x188c
  | 109 => 0x3cd
  | 110 => 0x170d
  | 111 => 0x24d
  | 112 => 0x2d6d1
  | 113 => 0x3ca
  | 114 => 0x45711
  | 115 => 0x28b
  | 116 => 0x59451
  | 117 => 0x15c591
  | 118 => 0x595d1
  | 119 => 0x58ed1
  | 120 => 0x21254
  | 121 => 0x184214
  | 122 => 0xbc214
  | 123 => 0x21854
  | 124 => 0x28214
  | 125 => 0x29414
  | 126 => 0x21494
  | 127 => 0x20294
  | 128 => 0x148214
  | 129 => 0x149414
  | 130 => 0x20bd4
  | 131 => 0x29554
  | 132 => 0x21555
  | 133 => 0x21414
  | 134 => 0x215d5
  | 135 => 0x21295
  | 136 => 0x128215
  | 137 => 0x3c215
  | 138 => 0x170215
  | 139 => 0xd4215
  | 140 => 0xec215
  | 141 => 0x17c215
  | 142 => 0x21715
  | 143 => 0x3d555
  | 144 => 0x203d5
  | 145 => 0x15c215
  | 146 => 0x15d555
  | 147 => 0x20d55
  | 148 => 0x3d415
  | 149 => 0x29494
  | 150 => 0x3d5d5
  | 151 => 0x188d14
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1695
  | 6 => 4275
  | 5 => 1603
  | 4 => 17
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
  | 7 => 2*((h/565+packedAt gbK7 (62715+(h % 565)*11) 11) % 1695)
  | 6 => 2*((h/1446+packedAt gbK6 (205200+(h % 1446)*13) 13) % 4275)
  | 5 => 2*((h/541+packedAt gbK5 (94577+(h % 541)*11) 11) % 1603)
  | 4 => 2*((h/19+packedAt gbK4 (1190+(h % 19)*5) 5) % 17)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffffc0fc01f803ffffc07ffc0c7cf8fd8c7e3f
  | 1 => 0xf803ff0001ffffffffff80fc739367320fffc7
  | 2 => 0x3fffffe0003f00fffffff83e387c3f063ff
  | 3 => 0x3fffffffffc000fffff03fc03f803ff83f8
  | 4 => 0x3fffffffffffff0000003fffc0003fffc00
  | 5 => 0xfffc00000000000000000003fffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x287ac02c505890b552c43964042428558c2e1b
  | 1 => 0xb0894b0020ab555a655c88a83191633205d6c5
  | 2 => 0x1119555b200426309a952d182e285c2b0616e
  | 3 => 0xa222669ac53598044e366c22dc03f8015e83b0
  | 4 => 0x443b8e379c6e38f800830c36ffc0003eb7800
  | 5 => 0xc78000038007000800304003fb5bd6a8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeaeafc88e080feeaeaeafc88e080feeaeaeafc88e080feeaeaeafc88e080feeaeaeafc88e080feeaeaeafc88e080feeaeaeafc88e080feeaeaeafc88e080, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40982
namespace PEqualNP.Outside.L_meta_40982
open PEqualNP.Outside.L_meta_40982.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs3_2_0 : Interval s3Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 10 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 60 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 165 := (concat bs3_4_0 bs3_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 50 := bs3_5_0
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
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 3 := block_range (n:=3) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 99 := (concat bs4_4_0 bs4_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 46 := bs4_5_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 29 := bs5_3_0
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
theorem bs5_4_384 : Interval s5Atlas 4 384 89 := block_range (n:=89) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 473 := (concat (concat bs5_4_0 bs5_4_96) (concat bs5_4_192 (concat bs5_4_288 bs5_4_384)))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 56 := block_range (n:=56) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 632 := (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat (concat bs5_5_288 bs5_5_384) (concat bs5_5_480 bs5_5_576)))
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
theorem bgb_4_0 : Interval gbAtlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 17 := bgb_4_0
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
theorem bgb_5_1536 : Interval gbAtlas 5 1536 67 := block_range (n:=67) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1603 := (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 bgb_5_288)) (concat (concat bgb_5_384 bgb_5_480) (concat bgb_5_576 bgb_5_672))) (concat (concat (concat bgb_5_768 bgb_5_864) (concat bgb_5_960 bgb_5_1056)) (concat (concat bgb_5_1152 bgb_5_1248) (concat bgb_5_1344 (concat bgb_5_1440 bgb_5_1536)))))
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
theorem bgb_6_4224 : Interval gbAtlas 6 4224 51 := block_range (n:=51) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4275 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 (concat bgb_6_576 bgb_6_672)) (concat bgb_6_768 (concat bgb_6_864 bgb_6_960)))) (concat (concat (concat bgb_6_1056 bgb_6_1152) (concat bgb_6_1248 (concat bgb_6_1344 bgb_6_1440))) (concat (concat bgb_6_1536 (concat bgb_6_1632 bgb_6_1728)) (concat bgb_6_1824 (concat bgb_6_1920 bgb_6_2016))))) (concat (concat (concat (concat bgb_6_2112 bgb_6_2208) (concat bgb_6_2304 (concat bgb_6_2400 bgb_6_2496))) (concat (concat bgb_6_2592 (concat bgb_6_2688 bgb_6_2784)) (concat bgb_6_2880 (concat bgb_6_2976 bgb_6_3072)))) (concat (concat (concat bgb_6_3168 (concat bgb_6_3264 bgb_6_3360)) (concat bgb_6_3456 (concat bgb_6_3552 bgb_6_3648))) (concat (concat bgb_6_3744 (concat bgb_6_3840 bgb_6_3936)) (concat bgb_6_4032 (concat bgb_6_4128 bgb_6_4224))))))
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
theorem bgb_7_1632 : Interval gbAtlas 7 1632 63 := block_range (n:=63) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1695 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 bgb_7_288)) (concat (concat bgb_7_384 bgb_7_480) (concat bgb_7_576 (concat bgb_7_672 bgb_7_768)))) (concat (concat (concat bgb_7_864 bgb_7_960) (concat bgb_7_1056 bgb_7_1152)) (concat (concat bgb_7_1248 bgb_7_1344) (concat bgb_7_1440 (concat bgb_7_1536 bgb_7_1632)))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 5, 13),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeaeafc88e080feeaeaeafc88e080feeaeaeafc88e080feeaeaeafc88e080feeaeaeafc88e080feeaeaeafc88e080feeaeaeafc88e080feeaeaeafc88e080
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808426 * 2 ^ 32 + 4236828800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40982.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[0,3]⟩,⟨.and,[2,6]⟩,⟨.or,[4,8]⟩,⟨.and,[2,3]⟩,⟨.or,[0,8]⟩,⟨.and,[5,11]⟩,⟨.or,[1,10]⟩,⟨.and,[9,13]⟩,⟨.and,[7,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4236828800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4236828800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40982

open PEqualNP.Outside.L_meta_40982 in
theorem PEqualNP.Outside.L_meta_40982 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4236828800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4236828800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
