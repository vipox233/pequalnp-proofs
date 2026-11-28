import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36709.Model
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


end PEqualNP.Outside.L_meta_36709.Model

namespace PEqualNP.Outside.L_meta_36709
open PEqualNP.Outside.L_meta_36709.Model
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

def SB : Nat := 7

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d SB k cs.length pool ws)

def mirrorSteps : List Move := [swapRows 50]

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
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) SB

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

end PEqualNP.Outside.L_meta_36709

namespace PEqualNP.Outside.L_meta_36709
open PEqualNP.Outside.L_meta_36709.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x3407282b700b77590ece0c26d80412000b00c400341221a3239b8900f7c084001652a000c9e01a3180b80000450000430820c244bff42fe42fd42fc42fe32fd32fc32ff41fe41fd41fc41ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xa417451483fe82907f90520fea0a41fc41483fe62907f8c520fe98a41fc31483fe42907f88520fe90a41fc21483fe80907f90120df20241fd40483f880906f10120ff98241fe30483fa60907fc8120fd90241fe20483dc40907fd5020bfaa041fe54082fca8107f55020beaa041fc54082f8a8107fd4c20bfa9841fe53082fca6107794c20af29841fd53082faa6107754c20aea9841fc53082f8a6107fd0c20ff21841fd43083f886105f94820ffa1041fe42083fa84107f10820ff99041ef32083fc64107f4c820fe19041ec32083fea2107f94420bf28841fd51082faa2107f14420ffa0841fe41083fa82107f10420ff98841fe31083fa62107f0c420ff90841fe21083dc42107f48420fe10841ec21082fca0107fd0020ff20041be40083fa80107f10020de20041ff30083fc60107f4c020fe18041ff20083de40107f88020fd10041fd20083da40107e48020ffaa6217f54c43fca9885f95310df2a6213e54c43faa9885f55310deaa6213d54c43f8a9885f15310ffa96217f52c43fca5885f94b10fea96217d52c43f8a5885f14b10ffa1621fe42c43fa85887f10b10ff19621fd32c43f865887fd0710ff20e21fd41c43f883887fc8710ff10e21fd21c43f843887fd0310fda0621fe40c437c81887f50310fe20621bc40c43f081886e10310ff90621fe20c43fa41887f08310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ffa1421fe42843fa85087f10a10ff19421fd32843f865085f54610ffa0c21fe41843fa83087f10610ff90c21f721843fc43087f48610fe10c21f421842fca1087fd0210ff20421be40843fa81087f10210de20421ff20843fc41087f48210fe10421ff10843ee21087ec4210ffaa2217f544437ea8884fd5110ff2a2217e54443faa8885f55110fe2a2217c5444378a8884f15110ffa92217f52443dea4885bd4910ff292217e52443faa4885f54910fe292217c52443d8a4885b14910ffa1221fe42443fa84887f10910ff19221fd32443f864887fd0510ff20a21fd41443f882887fc8510ff10a21fd21443f842887fd0110ff20221be40443fa80887f10110de20221ff20443fc40887f48110fe10221ff10443f620887f84110fb08221ff54042fea8087f95010bf2a021fd54042faa8087f15010be2a021ff52042fea4087f94810bf29021fd52042faa4087f14810be29021ff42043fc84087f50810fe21021fe32043fa64087f0c810bf28821ff41043fc82087f50410fe20821ff21043ee42087f88410fe90821fc21043e842085f94010ffa0021fb40043fc80086f90010fea0021fc400437880087e10010dc20021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xd42903f885206f10a40ff19481fd32903f865207fd4640ff28c817e51903faa3205f54640fe28c81ff419037e83207f90640df20c81fd419037a83207f10640de20c81ff21903fc43207f48640fe10c817e50903fe81206fd0240fda0481bf529037ca5206f54a40de29481be329037a65206f0ca40dfa8c81be519037aa3206f14640df90c81be219037a43206f086409f28481ff52502fea4a07f94940fea9281fc52502f8a4a07fd0940ff21281fd42503f884a07f8c940fe99281fc32503fea2a05fd4540ff28a81fd51503f8a2a05f14540ffa0a81fe41503fa82a07f10540ff90a81fe21503fa42a07f08540ffa0281fb40503fc80a06f90140bf2a081ff52103fca4205f94840fea90817d52103f8a4207fd0840dfa1081fe421037c84207f50840dea1081fc421037884207f8c840fe99081fc32103fea2207f94440bf28881fd51102faa2207f14440ffa0881bf41103fc82206f90440fea0881bd41103f882206f10440ff90881fe21103fa42207f08440bf28081ff401037e80207f90040fd20081fd401037a80207e50040dfa9081be521037aa4206f14840df19081bd321037864206fd4440df28881bd5110378a2206fc8440df10881bd211037842206f940409f28081ba50103fea9905fd5320ff2a6417e54c837ca9904f95320feaa6417d54c837aa9904f55320fe2a6417c54c83fea7907f94f20bf29e41fd53c82faa7907f14f20be29e41ff43c83fc87907f50f20fe21e41ff42c83fc85907f50b20fe21641ff32c83fc65907b8cb20fe99641ed32c83f865907fd4720ff28e417e51c83faa3905f54720fe28e41ff41c83fc83907f50720fe20e41ff31c83fc63907f4c720fe18e41ff21c83fc43907f48720fe10e41ff40c83fc81906f90320fea0641fc40c837881907fcc320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7107fd0e20ff21c41fd43883f887105f54a20ffa1441fe42883fa85107f10a20ff99441ef32883fc65107f4ca20fe19441ec32883fea3107f94620bf28c41fd51882faa3107f14620ffa0c41fe41883fa83107f10620ff98c41fe31883fa63107f0c620ff90c41fe21883dc43107f48620fe10c41ec21882fca1107fd0220ff20441be40883fa81107f10220de20441ff30883fc61107fc8220f790441fb20883fea8905fd5120dfaa2413f54483fca8905f95120feaa2417d54483f8a8905f15120de2a2413c54483fea6905fd4d20efa9a415f53483fca6905f94d20fea9a417d53483f8a6905f14d20ee29a415c53483fe86907f90d20fea1a41fc43483fe84907f90920fea1241fc42483fe64907f8c920f719241fd32483da64907f0c920ffa8a417f51483eea2905dd4520ff28a41fd51483f8a2905f14520fa28
  | 2 => 0x7fe8320efd0641fba0c83ff50907fca120df94241fea84837d50907f8a120ffd4941bfa9283ef52506dea4a0ff94941fea9283fc52506f8a4a0fb14941b629283ff425077e84a0ff90941fea1283bd42507f884a0ff8c941fe99283fc32507fe82a0fdd0541ff20a83be41507fea0a0dfd4141fda82837b50507fca0a0ff54141fe282837c50507f0a0a0de14141bf2a083ff52107fca420df94841fea90837d52107f8a420ffd0841ff21083fd42107f88420ff8c841fe99083fc32106fca220ffd0441dfa0883fe41107ec8220ff50441dea0883f541107fea020ff94041bf28083fd50106faa020ff14041ffaa6437f54c87fca990df95321feaa6437d54c87f8a990df15321ffa9e43fe53c86fca790f794f21af29e43fd53c86faa790f754f21aea9e43fc53c86f8a790ffd0f21ff21e43fd43c87f88790ffd0b21ff21643fd42c87f88590ffccb21ff19643fd32c87f86590ffd0721ff20e43fd41c87f88390ffcc721ffa8643fe50c86fca190ff54321bea8643fc50c87fea910dfd5221ff2a4437e54887faa910df55221fe2a4437c54887fea710dfd4e21ff29c437e53887faa710df54e21fe29c43ff43887fc8710ff50e21fe21c437d52887fe8510fbd0a21ff21443fd42887f88510fb10a21ff99443fe32887dc6510ff4ca21f699443fc32886fca310ffd0621ff20c43fd41887f88310ffcc621ff18c43ff21887de4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121ff2a2437e54487faa890df55121fe2a2437c54487fea690dfd4d21ff29a437e53487faa690df54d21fe29a437c53487fe8690ff90d21fea1a43fc43487fe8490ff90921fea1243fc42487fe6490ff8c921fe99243fc32487fe8290ff90521fea0a43fc41487fe6290ff8c521fe98a43ff21487ee4290ff88521f710a43ff50486fea090ff94121fea8243fc50486f8a090ffd5021bfaa043fe54086fca810ef950219f2a043fd54086faa810ef550219eaa043fc54086f8a810ffd4c21bfa9843fe53086fca610ff54c21bea9843fc53086f8a610ffd0c21ff21843fd43087f88610df94821ffa1043ef42087fc8410ff50821fe21043ec42087fe6410ff8c821f719043fd32087da6410ff0c821bf28843ff41087fc8210ff50421fe20843ff31087fc6210ff4c421fe18843ff21087de4210ff88421fb10843fd21087da4210fd48421ffa8043fe50086fca010ff54021bea8043fc50087fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681fe42d03fa85a07f10b40ff19681fd32d03f865a07fd4740ff28e817e51d03faa3a05f54740fe28e81ff41d03fc83a07f50740fe20e81ff21d03fc43a07f48740fe10e817d54903fea5207f94a40bf29481fd52902faa5207f14a40ffa1481bf42903fc85206f90a40fea1481b
  | 3 => 0x800800000000401400c00c00003800c00402000000000c00000c00c06c00800808000000400800401800c02800000c01800800800000400000001000000400800400401000405000400000c00406400800000000800400800801400c00402c00400800000004400000801c01801000800000800400000400002400800402400000c00000000001802800000000800000000000001803800404808800800c00801400c00000400800803c01400400400400800000000403400400800c00400000000000000001000000001c03002c00000800c00000400000c00001800404c02400002400400001400000401000000801802400402000000800400005c00402400c00400005800403006c00c013fea7a17f94f42bf29e85fd53d0afaa7a17f14f42ffa1e85ff51d0bfca3a15f94742fea8e857d51d0bf8a3a17fd4342ff286857e50d0bfaa1a15f54342fe286857d5490bfea7217f94e42bf29c85fd5390afaa7217f14e42ffa1c85fe4390afca5217fd0a42dfa1485ef4290bfea3217f94642bf28c85fd5190afaa3217f14642ffa8485fe5090afca1217f54242bea8485fc5090bfea6a15fd4d42ff29a85fd5350bf8a6a15f14d42ffa1a85fe4350bfa86a17fd0942f7a1285fe4250b7c84a17fd4542bfa8a85fe5150bfaa2a17f14542be28a85ff5050afea0a17f94142fea8285fc5050af8a0a15f95042ffa9885fe5310afca6217f54c42bea9885fc5310bfe86217f90c42fea1885fc4310afca4217fd0842dfa1085fe4210bdc84217f50842dea1085ed4210bfea2217f94442bf28885fd5110afaa2217f14442ffa8085fe5010afca0217f54042bea8085fc5010bfea9195fd5232ff2a4657e548cbfaa9195f55232fe2a4657c548cafaa7197fd0e32ff21c65fd438cbf887195f94a32ffa1465fe428cbfa85197f10a32ff99465ef328cbfea3197f94632bf28c65fd518cafaa3197f14632ffa8465fe508cafca1197f54232bea8465fc508cbfea8995fd5132ff2a2657e544cbfaa8995f55132fe2a2657c544cbfe84997f90932fea1265fc424cbfc6499778c932ffa8a657f514cbfca2997f54532fe28a657c514cbfea0995fd4132ff28265fd504cbf8a0995f14132ffaa0657f540cbfca8195f95032feaa0657d540cbf8a8195f15032bf29065ff420cbfc84197f50832fe21065fe320cbdc64197f4c832f699065cd320cbfea2197f94432bf28865fd510cafaa2197f14432ffa8065fe500cafca0197f54032bea8065fc500cbfea5a0ff94b41bf29683fd52d06faa5a0ff14b41ffa1683bf42d07fc85a0ff50b41dea1683fc42d07fc65a0ff4cb41fe19683ff50d07fca1a0df94341fea86837d50d07f8a1a0df55241ffa9483fe52906fca520ff54a41bea9483fc52907fe8520ff90a41fea1483fc42907fc6520ff4ca41fe194837e519
  | 4 => 0x319c0000001554001219101e140017d8000000000001cd9820000560b34001341c14000a15c1c00022d94e1ba088f842c8000001f98000001a48002250000000000000001c9c0000002d628935ccc8e18000000000d396b00000008042f49703421f9ef08d8001601d6c000b58000000d64b889a0000000000000000001a7800000000000000150c0440000000016312e162a2684f08f09011954a21aa3486088a82d800016d7a9d112700010e8000000000000001d4800094c000da0000000bb5b04549ad8e55049e69a20554fe91780000000022a80b80000000001084b8d4c309459bf00000000016500003c9758000000001df8001b14001bc91849e9950480002219541751ba400228008037c5c80011b8e510d0000001d3c000001248000b6815c0009495a1d1814d7a00000019362100018b08d5c90f08be9ab0000000000000001f48001f4140c698000000ad9bf80000012fc00115400000000000000000000068a2a0934000b600000000015f84ec5cce807f60506e8c02111791471818768000000600f301b8494a980018c00001dc000cc0000e600006c4474b317e96586197c1e3169dc21dfe2614f1b4013c0e8d880006e40005f80000000000006b40021219019b8550b3d9391a00f9e787bcb2c00117d1ac5900009c94791080000000000000000004d80023200018e6290000001e500004505c00022f000052800002401401000005c00000000000000400400800000802400000001c00400000400800401c00400000000002000001800c03c00801c00004400c02000000001004402c00000400400008000000400800c00400001002405c00001000000400000000000800001400400800800000403c00803400801c01800000402401800c01000000000400000000002800c00803003c02800000000000000c00c00002400001400800001800400800000400003800c00000000401000402401400c00000402001401800c04c02802800000c01c01000804401001c01007800002000800000c00801000400400c00400401400800000400000400800c00000806401c00400002400400c00000c00000000800005400c00000400400800400402000000000000000400000001400402800000000000002000000c00804c00400001000401800000000400000000000000400000002c01000000802800001000000000801000000c00000000800c02800800001800c00802400000002002000400000000001c00001800000000000401401000000400400000000800000001000800800800000000800400000800800400000003c05000000000402801004001800c00005402000000401000802000001400800400801c00400800000800000000401000001000001001000400000c00400c00403002001800000000c01000000000401
  | 5 => 0x114d8612059652ecbad7800022400019480000000000019d0c32171d4c000000000781c24328418000001adc00131d04d1644003980000000000000000000600000000000000004b1529a100016e4001cf00000000011287580909a8000000978d8000072c740f2c6b8a7159c9f02e9ba9dd85b00002ac0000007a4b94001d64000651d40678000000000bf8000001ad00010385e4db00000000000002600006d416a29c000000458fd80003600001f8000248000000fa80000014e09816940000000013900000000009b0002040d70ce8f69378002059d980007d8d58e480000ac8a000123caf15c80405890c4000000001829d280000000e1f79e580009299300021c1738000000001ac0000000f18000a240000000002980000017300000000000020f80000000019b01c90600005080000000000000000000000000000000000003313f96c0755c51ae85380000004d0df0000000001f022000004540020e88400017197cc0000000000017e54400c11d89c48b0000159fd9711301b08310edc0000017b1d341a8180ba9ee18b47f9094000001acc001d5d02c379f28c4c001f20d901251c0000000000001728000911fe16909397219913361d00014c1ae505c44967c000bd0000000000189e018b8000c880000000020904e99c8295b701410541c03a14241518745700011e210c0000000007c97fdb50e0933d3a13f4b700003c120c001fa9f58390001cbc8618c80000000001d800107c6c000004e300690001081ca00000020c8b9c002339480000000eb06e0c50001ff966400000028843800142c001040000001338001c280000006de3186cd1180000013e8de05587b02000000015514d40012087a80000000008c88180014bccb93b0ecc00022000000000143895cf700001f2162360000118cf00000005ae198a49c78999fc8000918d10001430002239968002078b083ec000001f500020298a827967918c0009d0001020c40174444001b98001ce00003f42a9cc4731ed80000000013d8b848f845ded0dc8001bfc0000000019a9564bf4ab12685fdf30e0d4edf387e9e48944000000001fb0000879864bc8001891a284f400000000179a1e8c80ea5f18c212c1f113088000d20fe1d800023e018f9400164000115800000000000000000000000016536d8002854d8e381550340016d8830d498e017829d5192996d40013e61811b1bdc000000000000000000dac000df8001064000001efd42800000181c0005a00022780017780000009616f93fc000000e10000001ffc811b79fe8e312f4bf16f00492c8001cf91303dc000000000001d00000000b7800199c13800000014a000cb000075dfb40000000b00000000007213440000001440000bc0005f5708000b8c6bc745490f59701b38001ec0f4166de910b0c04000a50ab4000
  | 6 => 0xa108000001f08002140b200000004e1889521aec8980000000016dc000001af1c68b40668f80e89399ccd144000b011f93100000002280cde702340c4f8d7c4000e685a80012dc000000000c1000000011d358fc0000d41e28a79364d18630c081d1a90519254ca50dc001988cd8ae0000000000001cb5714a806a41362595e85403840004980002bc74c4f8ef95008396acc780019a000000000000035a0a0000708000000000d796e0000000f20aa06a03e1da941c00000098800154c000598001f049d99e15809b84300000a15b04a8b90001ca8000001591878000a1c001cd4001571110701304c480000003b0000000000001d8473448c8ec1e47a0b490740014a8000000000198000c60000858000d5d6b8ac455c23000154890c46c0006d22d1ef9a057708dc648d74cedb612f10080014b5f80f880b622827108da98001809561dc9cb85a44210182f80000012309ee021360000001b48000a01290d21079bd90f9bc13d0210db90985bd260ec0f490e07e0850000000000000000001ca4000001ee52216a0000001324000d00000410000000000001ee8000000000000e14001afe341e38000000000000f24000001d50cd15782a0db62b9d2e011919f91d8c9c06611f0750000000000b80c70001211ac4e99bb4f1c5d8001b900018395a93191600013200019462e9588001c98000e79d620b192dde8ee55694996621d4001b59530c696d1805420f38641cc0259ef4871b00fc8001b20000000d695c00000000007ec0008b854c001c0a1e00013896e80011b4000000000000000ac10000012e4002004000000000000001f0c0000017f0000000000000000e28000000001068000001c880003961799a4000000000002311314000001a180020622d80000000019d8828059e24001120000000c5c0000000003b800130c00115c6b003c3a80000000000000000003f235800073c000000ea80000000021500005d02ecc14e05768000000000000001d380009580006d86c81717600017dda348080012f9f704c80000001f4000cf40014a4001aa0fd209843dc94ab80011520d0001618fa06f0000bfc000d142cc0014f42c0ce0000008001cac000000000218208000000000f60000f500003fd0b80000011a40004695b87b86ac000000001228dd4000cf8000000920d08000000000000af80000017d000085c789db87380003d106dd5a2b0725ff6044bc1be5978a19058795ae1bbdbed2d9e1a03850114036812800199427d8802d13dd025349899af80000004e42440000006581622221884780000000000005ec0001b0dd1410f9c0002b80000014f8000018000000001090000000000001374000000300000000d500015d1fb800132d8e94cc000f3c0000000008910d4000000001a8924c0001901000008d0a59c58000001d540000
  | 7 => 0x13f0d557e21f08fca40a087985f0001fec578ed8001698001bd1850c997c9084001cde3684a20aa2c00890700c807a00998d1a9e202f1a40ee98d9746071fd1c41251d45dd10d8d984842691e9ad4000000eb903c000000001f89010000000000000000000000000000000ae9d08000000000da80013c8a89488000000000464000000000000000b10000000000001848000114e900000000000000011895ac0013a8849e10aa9bcd08996082186c964b1c0000000d4000e70628b38d3cbbc3d4b2a1dca22104380001168000ba5920409bc58f00019f14198f80016804fc5ea299a09eb80000aa1a1f60000001eb1dc10c1239c81245449aa90ccb50670000000000748000000000001a50531c480000000012780000280000020b92a13b85217f49f8000ff8000c18000000001d3134dd74001bb81e1b69029e1d1c9ac8880000c65869e34000868b980008e9b319083e82512b8001508000ca8fba159e98908c91e40001e0c000001ea1ea80000008c0001be000138000000059d4b0710d61f69c0cea044c000000000002118000001b0c000001e81e8800000000155cef1d7c00116c9e20e18305661907f06200f0d45ba00002e5a389040008f55e00d8068002014dbd9405e1d8a270238001928000000f92148ee10440000021c80013682c4000be0001d92350d05240fe1cc828c7600010c8f79328d2800038ce4164a1292d00020311380000013522e00000000009400000000017d4000001b114e5b280013ec0010a181120086d468e00a101306a9610000001c100014e9badbe9af4ac8bb80005dd981df23300004c0000ba1ff0b19a68a280016a8000c54000000001bd6101608001eed788001e3c0000004416697554d0ec8d6c1ed68c580001408000b254b8001190001674ed59563091f60682b17b97499e8000461c60b45a00000ca11718587c0b140000014617405685111bc000000000ad00000000000002dc001280000000c380000020c1cd19f80010f15d8000000c1d2a98700000002fc000349d81c0412c000020000000000280001030000e20a915399996ec000000001c184880003f84700009303213e1a61fa09907fc888791d705b8dda2494c471a168bd8038001c31e600001a05d4000002328001c8c000000000001b8096c0022f88e593c7787b4954ff1fc0121a700000000000000000002e1180001a302a4001972138f362c8001ce94040103880716895f000079c639175de1bf5b18c5a080241670ed1d2089c050f9849c098000a64f11ab80014adc71199258f0047c000e59558001370d0c000cfd288d31400f283d98415fc3e4680001e08a2d85c7718d00001100000000000009cc0000011fc0000019583700020f13300005b50a86f8000c28001415da0000a600000016c8729c38000000000000000000a301e
  | 8 => 0x2b4dc0dfdbb00000021300000000009683512b1c00cd5910000001d780007d1b888e1cb0950000001ec80000018a0001a81214fb00011d12e800114a048001a58bb0000000001db22080016221b1599e2d6380000000005c400000033893ca6a2317f8428001d694c95102914509d40004910500016840000000013c0000318054000000a380020d8de8610
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x821043e63208410f94c821043f26008410bd58021043f160084109f992500427d64940109f98a500427d62940109f58650043772194010dd086500427d65d0010be597400437965d0010ded53400437954d0010be587400437a51d0010fcc8740043f021d00109fd96400427d6590010cf952400433d5490010bd98640042f56190010be982400433f6590010cf996400433d6590010cf196400433f5290010cf94a400433d5290010cf14a40043b66190010ed586400433e5190010edc8640043b42190010af98240042ba6090010cf942400427f65500109fd94400427e65100109f594400427c6510010cf950400433d5410010bd98440042f56110010ee500400433f6510010cf994400433d6510010cf194400433f5210010cf948400433d5210010cf14840043b66110010ed584400433e5110010edc8440043b42110010af98040043ba6010010cf94040042f96510010de59440042796510010be99040043ba6410010ded5040043ba5410010de55040043b95410010eed0840043ba4210010ee50840043b84210010fc98440042f96110010fc584400437a5110010eed0440043ba4110010ee50440043b84110010fcc8440043f02110010ee994400433a6510010ee59440043396510010eed8840043ba6210010ee58840043b86210010eed4840043ba5210010ee54840043b85210010ee8c840043b93210010ee0c840043bb6110010ee98440043b26110010ee58440043b16110010ee184400433a5110010eec8440043b32110010ee88440043b92110010ee08440043b021100109f59720042be64c8010af59320043b840c80109fd96200427d6588010db94a200436d5288010bd98620042f56188010f908620043b840880109fd9520042bf6448010af19120042df6348010b718d20042f76148010bd18520043b840480109fd94200427e65080109f594200427c6508010b798c20042dd6308010db948200436d5208010bd98420042f56108010f908420043b84008010af99310042bd64c4010ee103100437565c4010ed99310043b564c4010bd98b10042f462c4010fcd0310043b640c4010ed10310043f040c4010ec10310042f56184010dd94610043ba4084010ee10210042f96584010de59610042796584010be99210042f86484010be586100437a5184010fc94610043f32184010fc086100427f6544010afd9110042bc6444010bbd8910042ec6244010ee90110043b84044010bdd95100437765440109dd9510043b76444010ed19110043e76244010bd98910042f46244010f918910042e46244010bdd8110043765044010ed90110043b44044010bed95100437b65440109ed9510043bb6444010be99110042f86444010ee19110042b86444010fad8910043e86244010bed8510043f36144010de94510043f25144010
  | 1 => 0x43e75284110dd94a10443745284110f914a10443645284110fcd4210443b64084110ed102104427e62d50109f58b540427e61d5010dd987540427e60d5010de983540427d6595010cfd52540427e62950109f58a540433f64550109fd89540427c62550109fd85540427d61550109fd81540427d6055010de181540433d5415010bb98854042ed62150109f990540433e64150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109f980540437a60150109f993520427d64d48109f98f520427d63d48109f987520437661d48109f983520437a60d48109f596520436f52948109f992520427d64948109f98e520427d63948109fd91520427c64548109fd8d520427c6354810dbd89520427f61548109f585520437461548109fd81520427d6054810af99052042bd6414810b798c52042dd6314810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520427e6114810dd984520427e6014810de980520427f65d08109f997420427d65d08109f197420433e54d0810cf55342042f661d0810bd587420427f65908109f996420427d65908109f196420436e5290810db54a42042fa6090810be582420427f65508109f995420427d65508109f195420433e5450810cf551420436e5250810db54942042f76150810bd18542042fb6050810be181420427f65108109f994420427d65108109f194420427f658c8109f996320427d658c8109f196320436e528c810db54a32042f6618c810bd586320427f654c8109f995320427d654c8109f195320436e524c810db54932042f7614c810bd18532042fb604c810be181320427f650c8109f994320427d650c8109f19432043cd320c8109f992510433e64944108f992510427d6494410cf592510423d64944109f98a510427d62944109f597410433f54d0410cf153410427f65904109f596410433e5490410cf55241042fa6090410be582410427f6550410cfd51410433c5450410bbd8941042ec6250410bed81410427f65104109f594410433e5410410cf55041042fa6010410be580410427d65c8410b798f21042dd63c8410bd597210437565c8410bd98f21043d663c8410b598f21043d563c8410bd18f210437752c8410dd54b21042f560c84109fd96210427d6588410db94a210436d5288410bd98621042fa6088410be582210427f65484109fd94210427d6508410af99021042bd6408410db948210436d5208410f948421042fa6008410be580210437565084109d59421043b66408410ed59021042f66308410bd18c21042f66208410f998821043775208410f994821043755208410f954821043e74208410f910
  | 2 => 0x5210910db14842442f66110910bd584424427f658c9109f996324427d658c9109f196324433f548c910cf152324435f538c910d714e324436f528c910db14a324427f654c9109f995324427d654c9109f195324433f544c910cf151324436f524c910db149324427f650c9109f994324427d650c9109f194324433f540c910cf150324436f520c910db14832443cd320c910be98032442f9600c9109f997414433f54d0510cf153414436f52d0510db14b41442fa60d0510be583414427e6590510cfd52414433c5490510dbd4a414436c52905109f195414433f5450510cf15141442ef6250510bb189414436f5250510db14941442fb6050510be181414427e6510510cfd50414433c5410510dbd48414436c5210510ed504414427e65c8510cfd53214433c54c8510b798f21442dd63c8510d7d4f214435c53c8510dbd4b214436c52c8510be98321442f960c85109f996214433f5488510cf152214435f5388510d714e214436f5288510db14a214427c6548510cfd51214433c5448510d7d4d214435c5348510dbd49214436c5248510bed8121442f860485109f99421442be6408510af590214433f5408510cf150214435f5308510d714c214436f5208510db148214427e65d0110cfd53404433c54d0110dbd4b404436c52d0110bd98740442f561d01109f996404433f5490110cf952404433d5490110cf152404436f5290110db14a40442be6590110cf996404423e6590110cfd4a40443af5290110cbd4a404433e5290110cf54a404433c5290110eb14a404432c5290110af982404427f65501109f595404427c6550110cfd51404433c5450110dbd49404436c5250110bdd8540442f461501109f994404433f5410110cf950404433d5410110cf150404436f5210110db14840442be6510110cf994404423e6510110cfd4840443af5210110cbd48404433e5210110cf548404433c5210110eb148404432c5210110af98040443ba60101109f99720442be64c8110af593204433f54c8110cf153204435f53c8110d714f204436f52c8110db14b20442f661c8110bd587204427e6588110cfd52204433c5488110d7d4e204435c5388110dbd4a204436c52881109fd95204427d65481109f19520442bf6448110af191204433f5448110cf15120442df6348110b718d204435f5348110d714d204436f5248110db14920442f76148110bd185204427e6508110cfd50204433c5408110b798c20442dd6308110d7d4c204435c5308110dbd48204436c5208110af99310442bd64c4110cfd53104433c54c4110dbd4b104436c52c4110ee90310443b840c4110ee99310443b964c4110eed53104437a54c4110de15310443b854c4110ce15310443eb52c4110fa14b104433f5484110cf152104436f5284110db14a10443b75484110ed152104
  | 3 => 0x110bb98a54442ed62951109f992544423e64951109f98a544436e62951109b98a544427d6295110db58a544426d62951109f586544437561951109f58254443796095110bbd8954442ec6255110cfd91544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427f6055110ded81544427b60551109f994544433d5415110cf990544427e62151109f588544427e61151109f184544427e60151109f18054442be6515110cf994544423e6515110cfd88544433e6215110cf588544433c6215110cfd84544433d6115110cfd80544423e6015110cf580544423c6015110cf440544433f54d4910cf153524427e64d49109f593524427e63d49109f58f524436f54d4910ebd53524432f54d4910db953524436d54d4910db15352443ac54d4910cb153524436f53d4910f3d4f524434f53d4910dbd93524436e64d4910db593524436c64d4910dbd8f524436e63d4910db58f524436c63d4910dbd87524436d61d4910dbd83524436d60d4910af99252442bd6494910cfd52524433c5494910b798e52442dd6394910d7d4e524436f52949109f992524433e64949108f992524427d6494910cf592524423d64949109f98e524435e63949109798e524427d6394910d758e524425d63949109f98a524426e62949109f586524437561949109f58252443796094910afd9152442bc6454910cfd51524433c5454910b7d8d52442dc6354910d7d4d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109dd85524427f6054910ded81524427e6514910cfd50524433c5414910d7d4c524436d52149109f990524427d64149109f98c524427d6314910db988524427e61149109f184524427e60149109f18052442ee6514910db994524426e6514910dbd5052443af5414910cbd50524436e5414910db550524436c5414910eb150524432c5414910dbd4c52443cf5314910d3d4c524436e5314910db54c524436c5314910f314c524434c5314910dbd90524436e6414910db590524436c6414910dbd8c524436e6314910db58c524436c6314910dbd84524436d6114910dbd80524436d6014910db440524427f65d09109f997424427d65d09109f197424433f54d0910cf153424435f53d0910d714f424436f52d0910db14b424427f65909109f996424427d65909109f196424433f5490910cf152424435f5390910d714e424436f5290910db14a424427f65509109f995424427d65509109f195424433f5450910cf151424435f5350910d714d424436f5250910db149424427f65109109f994424427d65109109f194424433f5410910cf150424435f5310910d714c424436f
  | 4 => 0xf992528423e6494a109f592528433d6494a108f592528427e6394a109f58e528427f6454a109f191528427f6354a109f18d528436f6254a10ddd8552842de6314a10b758c528436d5214a109f990528427d6414a109f98c528435e6314a109798c528427d6314a10d758c528425d6314a10db98852843756114a10de980528427f65d0a109f997428427d65d0a109f197428433f54d0a10cf153428436e52d0a10db54b42842f661d0a10bd587428427f6590a109f996428427d6590a109f196428427f6550a109f995428427d6550a109f195428433f5450a10cf15142842f76150a10bd185428427f6510a109f994428427d6510a109f194428436e5210a10db548428427f658ca109f996328427d658ca109f196328436e528ca10db54a32842f6618ca10bd586328427f654ca109f995328427d654ca109f195328436e524ca10db54932842f7614ca10bd185328427f650ca109f994328427d650ca109f19432843cd320ca10be98032842f9600ca10cf953418433d54d0610be98341842f960d0610cfd52418433c5490610cf951418433d5450610bbd8941842ec6250610bed8141842f86050610cfd50418433c5410610b798f21842dd63c8610db94b218436d52c8610be98321842f960c8610dd59721842f663c8610f598f21842d663c8610f558f21842f463c8610ddd4b21843e652c8610dd54b21843e552c8610fc98321842f560c8610fc583218436f5288610db14a218436e5248610db54921842fb6048610be18121842be6408610af590218436f5208610db14821843e52108610bd59421843756508610ed99021843b56408610bd98c21842f46308610f998821843775208610f9d4821843755208610f914821843e74208610f910821843e63208610f94c821842f56008610cf952408433d5490210bd98640842f56190210cf996408433d6590210cfd4a408433e5290210cf54a408433c5290210ed98640843b56190210edc8640843b42190210cf950408433d5410210bd98440842f56110210cf994408433d6510210cfd48408433e5210210cf548408433c5210210ed98440843b56110210edc8440843b42110210ee98040842be64c8210af593208436e5288210db54a20842f66188210bd58620843e42188210afd9120842bc6448210b7d8d20842dc6348210bdd8520842f46148210b798c20842dd6308210db948208436d5208210bd98420842f56108210f908420842be64c4210af59310843ba40c4210ee10310842f565c4210dd59710843b664c4210ed59310842f662c4210bd18b10843b640c4210ed10310842f965c4210de59710843ba64c4210ee593108437a54c4210de153108427e62d51109f58b544433f62d5110cf98b544433d62d5110cf18b544433f61d5110cf587544433f60d5110cf583544433f5495
  | 5 => 0x42c427d6510b109f19442c433e5410b10cf55042c42f66110b10bd58442c427f658cb109f99632c427d658cb109f19632c433e548cb10cf55232c435e538cb10d754e32c436f528cb10db14a32c427f654cb109f99532c427d654cb109f19532c433e544cb10cf55132c436f524cb10db14932c42fb604cb10be18132c427f650cb109f99432c427d650cb109f19432c433e540cb10cf55032c436e520cb10db54832c43cd320cb10cf95341c433d54d0710cf95241c433d5490710be98241c42f96090710cf95141c433d5450710bbd8941c42ec6250710be18141c433e5410710cf55041c43b54110710be98041c42f96010710cf95321c433d54c8710b798f21c42dd63c8710cf95221c433d5488710db94a21c436d5288710be98221c42f96088710cf95121c433d5448710af99021c42bd6408710cf95021c433d5408710db94821c436d5208710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310be59740c437965d0310ded5340c43ba54d0310de55340c43b954d0310fc98740c42f961d0310fc58740c433f5490310cf95240c433d5490310cf15240c42bd6590310cf59640c433f5290310cf94a40c433d5290310cf14a40c433e5450310cf55140c42f76150310bd18540c433f5410310cf95040c433d5410310cf15040c43b94010310af59440c433d6510310cfd4840c433e5210310cf54840c433c5210310ee98040c42f96510310de59440c43ba6410310ded5040c43bb5410310ee95040c43795410310ee55040c43395410310ee15040c43bb4210310ee90840c43b94210310ee10840c42f96110310eed0440c43ba4110310ee50440c43b84110310ee59440c42b96510310ce59440c43bb6210310ee98840c43b96210310ee18840c43bb5210310ee94840c43b95210310ee14840c43ba3210310ee4c840c43b83210310eed8440c43ba6110310ee58440c43b86110310eec8440c43ba2110310ee48440c43b82110310af99320c42bd64c8310cf95320c433d54c8310db94b20c436d52c8310bd98720c42f561c8310ee10320c433e5488310cf55220c436f5288310db14a20c43b84088310afd9120c42bc6448310cf95120c433d5448310b7d8d20c42dc6348310db94920c436d5248310bdd8520c42f46148310ee10120c433e5408310cf55020c42de6308310b758c20c436f5208310db14820c43b84008310bb98b54842ed62d52109f98b548436e62d52109b98b548427d62d5210db58b548426d62d5210dd587548437a60d5210cfd52548427e62952109f58a548433f64552109fd89548427c6255210cf550548433e64152109f988548427d6215210dd584548437a60152109f993528427d64d4a109f98f528427d63d4a10dd587528437a60d4a10af99252842bd6494a10dbd4a528427e6494a10c
  | 6 => 0x35e534c020d754d30082ef624c020bb18930083cf324c020bdd8530082f4614c0209f994300827d650c0209f19430082ee620c020bb58830083cc320c020ee10030082be64c8020af593200835e53c8020d754f20083ae64c8020eb59320082ee63c8020bb18f200836f53c8020f394f200836d53c8020f354f200834d53c8020bb98720083ae40c8020eb103200835e5388020d754e20082ed6288020db94a20083ba4088020ee10220083da5388020f654e20082f96288020de94a20083ea5288020facca20083e83288020fa88620083e821880209fd9520082bf6448020af19120082df6348020b718d200835e5348020d754d20082f76148020bd18520083ba4048020ee10120082ef6548020dbd95200826f6548020ebd9120083ac6448020f3d8d20082ee6348020bb18d20083cc6348020b318d200836f5348020f394d200836d5348020f354d200834d5348020f9d8520082ec6148020f918520082e46148020bbd81200836e5048020fad0120083ae4048020eb10120083e84048020ea10120082fb6548020ded95200827b6548020eed9120083b86448020f6d8d20083d86348020f694d20083d95348020bed8920083eb6248020de94920083ea5248020fad0920083e84248020fcd8520083f061480209f98b54c427d62d5310dd98754c437960d5310cfd5254c427e62953109f58a54c43bb6095310cfd8a54c433e6295310cf58a54c433c6295310cf98654c433c6195310cfd8254c433d6095310cfd9154c427f62553109f18954c437b6055310cfd9554c43bb6055310cfd8954c433e6255310cf58954c433c6255310cf98554c433c6155310cfd8154c433b6055310cf58154c433d5415310cf99054c427e62153109f58854c43766115310de58054c42be64d4b10af59352c433e54d4b10cf55352c42de63d4b10b758f52c427e64d4b10cf99352c423e64d4b109f59352c433d64d4b108f59352c427e63d4b10d798f52c425e63d4b109f58f52c435d63d4b109758f52c437661d4b10de58352c433e5494b10cf55252c42de6394b10b758e52c436f5294b109f99252c427d6494b109f98e52c435e6394b109798e52c427d6394b10d758e52c425d6394b10cf95152c433d5454b109fd9152c427c6454b109fd8d52c427c6354b10dbd8952c42be6414b10af59052c433e5414b10cf55052c436d5214b109f99052c433e6414b108f99052c427d6414b10cf59052c423d6414b109f98c52c427d6314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f19742c433e54d0b10cf55342c427f6590b109f99642c427d6590b109f19642c433e5490b10cf55242c42fa6090b10be58242c427f6550b109f99542c427d6550b109f19542c433e5450b10cf55142c42fb6050b10be18142c427f6510b109f994
  | 7 => 0x4d0420d794f410835d53d0420bb98b41082ed62d04209fd96410827e65904209f596410835e5390420d754e41083765190420dd546410827f65504209f595410827c6550420cf951410833d5450420b7d8d41082dc6350420d794d410835d5350420bbd8941082ec6250420dd94541083755150420bed8141082f860504209fd94410827e65104209f594410835e5310420d754c410827f65cc4209f997310827d65cc420d794f310835d53cc420bb98b31082ed62cc4209fd96310827e658c4209f596310835e538c420d754e31082ee628c420bb58a31083cf328c4209fd95310827d654c4209f195310835e534c420d754d31082ef624c420bb18931082fb604c420be181310827f650c4209f994310827d650c420af99031082bd640c420d794c310835d530c420f3cc831082de63c8420b758f210835e53c8420d754f210837651c8420dd54721082fa60c8420be583210827d6588420d794e210835d5388420bb596210836d6588420db952210836c5488420bb98e21082ec6388420dbd4e21083ce5388420db54e21083cd5388420d354e21082ee6188420db54621082ed60884209fd95210835e5348420d754d21082be6408420af590210835e5308420d754c21083765108420dd54421083e52108420be98021082f96008420eb99021083ad6408420db950210836c5408420bb98c21082ec6308420dbd4c21083ce5308420db54c21083cd5308420d354c21082ee6108420f998421083e65108420db54421083e55108420fa98021082ed6008420fa580210827e64940209f592500827e63940209f58e500836f3294020db0ca500836e2194020db086500827d65d0020d794f400835d53d00209fd96400827d6590020cf952400833d5490020d794e400835d5390020bb98a40082ed6290020cfd96400833e6590020cf596400833c6590020cfd4e400833e5390020e794e400831e5390020cf54e400839d5390020c754e400833c5390020eb98a40083ad6290020cf94a40083af3290020eb0ca400833e5190020cf54640083ae2190020eb08640082be6090020cf942400827f6550020d794d400835d53500209fd94400827e65100209f594400827c6510020cf950400833d5410020d794c400835d5310020bb98840082ed6210020cfd94400833e6510020cf594400833c6510020cfd4c400833e5310020e794c400831e5310020cf54c400839d5310020c754c400833c5310020eb98840083ad6210020cf94840083af3210020eb0c8400833e5110020cf54440083ae2110020eb08440082be6010020ee980400833e50100209f59730082be64cc020af593300835e53cc020d754f30083cf32cc020ee103300827f658c0209f596300835e538c020d754e30082ee628c020bb58a30083cc328c0209fd9530082bf644c020af1913008
  | 8 => 0x209f988540836e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a60150209f993530827d64d4c20db98b530827e61d4c209f587530837a60d4c209f596530835f5394c209f992530827d6494c209f986530827d6194c2097596530835f5494c20d7952530835d5494c20d715253083cc6294c20d7d92530835e6494c20d7592530835c6494c20d798a530835c6294c20d7d86530835e6194c20d7586530835c6194c20d7982530835c6094c209fd91530827c6454c20d7d8d530827f6254c209f589530836c6254c209fd85530827c6154c20d7d95530835f5454c20d7951530835d5454c20d715153083cc6254c20d7d91530835e6454c20d7591530835c6454c20d7989530835c6254c20d3189530835f6154c20d7985530835d6154c20d7185530835e6054c20d7181530835c2054c20b798c530835d5314c209f990530827d6414c209f988530836e6214c209b988530827e6114c209f584530827e6014c20de980530827f65d0c209f997430827d65d0c209f197430835e53d0c20d754f43082ee62d0c20bb58b430827f6590c209f996430827d6590c209f196430835e5390c20d754e430827f6550c209f995430827d6550c209f195430835e5350c20d754d43082ef6250c20bb18943082fb6050c20be181430827f6510c209f994430827d6510c209f194430835e5310c20d754c430827e6494820cf992520823e64948209f592520833d64948208f592520827d63948209f597420833f54d0820cf153420835e53d0820d754f420827f65908209f596420833e5490820cf552420835e5390820d754e42082fa6090820be582420827f6550820cfd51420833c5450820d794d420835d53508209fd94420827d6510820cf950420833d5410820d794c420835d5310820be98042082f960108209f597320835e53cc820d754f32082ed65cc820db597320826d65cc820dbd4f32083ce53cc820db54f32083cd53cc820d354f32082ee61cc820bb583320827f658c8209f596320835e538c820d754e32082ee628c820db94a32082fa608c820be582320827f654c820d794d320835d534c820db949320827f650c8209f594320835e530c820d754c32083cd320c820be98032082f9600c820db594320826d650c820bb98c32083ce630c820dbd4c32083ce530c820db54c32083cd530c820d354c32082ee610c820fa98032082ed600c820fa58032082de63d4420b758f510835e53d4420d754f510835e5394420d754e510837751944209f992510827d64944209f98e510827d6394420d794d510835d53544209fd91510827c64544209fd8d510827c6354420af99051082bd6414420b798c51082dd6314420d794c510835d5314420dd544510827f65d04209f997410827d65d0420cf953410833d5
  | 9 => 0x147214833f5488520cf152214835f5388520d714e21483775188520dd14621482fa6088520be582214833f5448520cf151214835f5348520d714d21483775148520dd14521482fb6048520be181214827e6508520af99021482bd6408520cfd50214833c5408520d7d4c214835c5308520ddd44214827e65d0120cfd53404833c54d0120d7d4f404835c53d0120bb98b40482ed62d0120ddd47404837451d01209f996404833f5490120cf952404833d5490120cf152404835f5390120d714e40483775190120dd14640482be6590120cf996404823e6590120cfd4e404839f5390120c7d4e404833e5390120cf54e404833c5390120e714e404831c5390120eb8ca40483ad3290120cfd4640483b75190120cdd46404833c5190120ed14640483345190120af982404827f65501209f595404827c6550120cfd51404833c5450120d7d4d404835c5350120bbd8940482ec6250120ddd45404837451501209f994404833f5410120cf950404833d5410120cf150404835f5310120d714c40483775110120dd14440482be6510120cf994404823e6510120cfd4c404839f5310120c7d4c404833e5310120cf54c404833c5310120e714c404831c5310120eb8c840483ad3210120cfd4440483b75110120cdd44404833c5110120ed14440483345110120af98040483ba60101209f99730482be64cc120af593304833f54cc120cf153304835f53cc120d714f30482ee62cc120bb58b30483cd32cc120ddd47304837451cc120cfd52304833c548c120d7d4e304835c538c120f38ca3048377518c120dd14630483b8408c1209f595304827c654c120cfd51304833c544c120bbd8930482ec624c120f34c93048377514c120dd14530483b8404c120af99320482bd64c8120cfd53204833c54c8120d7d4f204835c53c8120ddd47204837451c8120ee90320483b840c8120ee99320483b964c8120eed5320483b854c8120f6d4f20483d853c8120fa8cb20483e932c8120fcd4720483f051c8120cfd52204833c5488120d7d4e204835c5388120ddd4620483745188120ebd5220483ac5488120bbd8e20482ed6388120f3d4e204836e5388120db14e20483cc5388120d314e20483e75188120db14620483e45188120d914620483eb5088120eb90220483ac4088120b798f54082dd63d50209f98f540835e63d50209798f540827d63d5020d758f540825d63d50209f98b540836e62d50209f987540827d61d50209f983540837a60d50209f596540833f54950209f98e540827d63950209f986540827d6195020cfd91540827f63550209f18d540827f62550209f589540827f61550209f185540833d5415020b798c54082dd6315020bd98454082f561150209f990540833e64150209f98c540835e63150209798c540827d6315020d758c540825d63150
  | 10 => 0x14827d64d45209f98f514827d63d4520ddd5351483b754d4520cdd53514837654d4520dd553514837454d4520ed153514833454d4520ddd4f51483d753d4520d5d4f514837653d4520dd54f514837453d4520f514f514835453d4520f98cb51483e532d4520ddd93514837664d4520dd593514837464d4520ddd8f514837663d4520dd58f514837463d4520ddd0f514837643d4520dd50f514837443d4520ddd8b514837742d4520dd90b514837542d4520dd10b514837732d4520dd8cb514837532d4520dd0cb514837760d4520dd58351482be6494520af592514833f5494520cf15251482de6394520b758e514835f5394520d714e51483775194520afd9151482bc6454520cfd51514833c5454520b7d8d51482dc6354520d7d4d514835c5354520cfd50514833c5414520d7d4c514835c5314520dd544514827e64145209f590514827e63145209f58c514836e3214520db4c851482f66514520dd99451483775414520edd5051483375414520dd95051483755414520dd15051483b45414520cd15051483775314520f5d4c51483575314520dd94c51483755314520dd14c51483d45314520d514c51483e63214520f94c851483776414520dd99051483756414520dd19051483776314520dd98c51483756314520dd18c51483774314520dd90c51483754314520dd10c51483776214520ddd0851483764214520dd50851483744214520ddcc851483763214520d98c851483753214520d94c851483743214520ddd8051483756014520dd480514827e65d05209f597414827c65d0520cfd53414833c54d0520d7d4f414835c53d0520ddd47414837451d05209f996414827d65905209f196414833f5490520cf152414835f5390520d714e41483775190520dd146414827f65505209f995414827c6550520cfd51414833c5450520b7d8d41482dc6350520d7d4d414835c5350520bbd8941482ec6250520ddd4541483745150520bed8141482f860505209f994414827d65105209f194414833f5410520cf150414835f5310520d714c41482ee6210520bb58841483775110520dd144414827e65cc5209f597314827c65cc520cfd53314833c54cc520d7d4f314835c53cc520bb98b31482ed62cc520ddd47314837451cc5209f996314827d658c5209f196314833f548c520cf152314835f538c520d714e31483cd328c520ddd463148374518c5209fd95314827e654c5209f195314833f544c520cf151314835f534c520d714d3148377514c520dd145314827e650c5209f594314827c650c520af99031482bd640c520cfd50314833c540c520d7d4c314835c530c520bb98831482ed620c520f34c83148377510c520dd14431482fa600c520be580314827e65c8520cfd53214833c54c8520b798f21482dd63c8520d7d4f214835c53c8520dd
  | 11 => 0x3f54d4d20cf153534827e64d4d209f593534827e61d4d209f587534835f54d4d20e7d53534831f54d4d20d7953534835d54d4d20d7153534839c54d4d20c715353483cf62d4d20d7d93534835e64d4d20d7593534835c64d4d20d7d8b534835d62d4d20d7d87534835e61d4d20d7587534835c61d4d20d7d83534835d60d4d20af99253482bd6494d20cfd52534833c5494d20d7d4e53482f66194d20bd586534827e6494d20cf992534823e6494d209f592534833d6494d208f592534836d6294d209f98653483766194d209d986534827d6194d20dd58653482756194d20de58253482bf6454d20af191534833f5454d20cf15153482f76154d20bd185534827f6454d20cfd91534823f6454d209f191534833c6454d208f191534836f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209f994534833f5414d20cf150534835d5314d209f990534827d6414d20d798c534827c6214d209f984534827d6114d20b7994534835e6514d2097994534835f5414d20e7d50534831f5414d20d7950534835d5414d20d7150534839c5414d20c715053483cd6214d20d7d90534835e6414d20d7590534835c6414d20d7d88534835f6114d20d7984534835d6114d20d7184534835f6014d20d7580534835d2014d209fd97434827e65d0d209f597434827c65d0d20cfd53434833c54d0d20d7d4f434835c53d0d209fd96434827e6590d209f596434827c6590d20cfd52434833c5490d20d7d4e434835c5390d20bb98a43482ed6290d20be98243482f96090d209fd95434827e6550d209f595434827c6550d20cfd51434833c5450d20d7d4d434835c5350d209fd94434827e6510d209f594434827c6510d20cfd50434833c5410d20d7d4c434835c5310d20bb98843482ed6210d209f997424833f54d0920cf153424835f53d0920d714f42482fa60d0920be583424827e6590920cfd52424833c5490920d7d4e424835c53909209f195424833f5450920cf151424835f5350920d714d42482fb6050920be181424827e6510920cfd50424833c5410920d7d4c424835c5310920cfd53324833c54cc920d7d4f324835c53cc920be98332482f960cc9209f996324833f548c920cf152324835f538c920d714e32482ee658c920db996324826e658c920ebd5232483ac548c920bb58e32483cf538c920db94e324836c538c920f314e324834c538c920bb982324833f544c920cf151324835f534c920d714d32482fb604c920be18132483af544c920eb15132483cf634c920f3d4d324836e534c920db14d32483cc534c920d314d32483eb604c920bb18132483e8604c9209f994324833f540c920cf150324835f530c920bb98832483cd320c920cfd53514833c54d4520d7d4f514835c53d45209f9935
  | 12 => 0x50620bed8141882f860506209fd94418827e65106209f594418827f65cc6209f997318827d65cc620bb98b31882ed62cc6209fd96318827e658c6209f59631882ee628c620bb58a31883cf328c6209fd95318827d654c6209f19531882ef624c620bb189318827f650c6209f994318827d650c620af99031882bd640c620f3cc831882fa600c620be58031882de63c8620b758f21883765188620dd54621882fa6088620be582218836e5488620db15221882ee6388620bb18e218836f5388620db54e21883e65188620db54621883e55188620fa98221882ed6088620fa58221883765148620dd54521882fb6048620be18121882be6408620af59021883e52108620bb594218836d6508620eb99021883ad6408620db950218836c5408620bb98c21882ec6308620dbd4c218836d5308620f998421883e75108620db54421883e45108620bb580218833e5490220cf55240882ee6290220bb58a408833e6590220cf596408833f5390220cf94e408833d5390220eb98a40883ad6290220ebcca40883ac3290220cf946408833d5190220eb88640883ac2190220cf950408833d5410220bb98840882ed6210220cf994408833d6510220cfd4c408833e5310220cf54c40883ae6210220eb58840883af3210220eb0c8408833e5110220cf54440883ae2110220eb08440883ba6010220af99330882bd64cc220f3ccb30882ee628c220bb58a30883cc328c220ee10230882be64c8220af59320883ba40c8220ee10320882ed65c8220db59720883ae64c8220eb59320882ee63c8220bb18f208836f53c8220db54f20882ee61c8220eb90320883ac40c8220be597208837965c8220ee99320883b964c82209f98f544827d63d51209f987544827d61d5120cfd8f544833e63d5120cf58f544833c63d5120cfd8b544833d62d5120cfd87544833e61d5120cf587544833c61d5120cfd83544833d60d5120cfd5254482de6395120b758e54482f66195120bd586544827e64951208f992544827e6395120d798e544825e63951209f58e544835d63951209758e544827d6295120db58a544827e6195120dd986544827661951209f586544837561951209d586544827d6095120de58254482df6355120b718d54482f76155120bd185544833f64551209fd8d544835f635512097d8d544827c6355120d718d544825c63551209fd89544836f62551209fd85544837761551209dd85544827c6155120dd185544827461551209fd81544837b60551209f994544833d5415120cf990544827e63151209f58c544827e62151209f188544827e61151209f58454482be6515120cf994544823e6515120cfd8c544833e6315120cf58c544833c6315120cfd88544833d6215120cfd84544833e6115120cf584544833c6115120cfd80544833d6015120cf48054483
  | 13 => 0xbe18131c827f650c7209f99431c827d650c720af99031c82bd640c720cf95031c833d540c720d794c31c835d530c720bb98831c82ed620c720f34c831c8376510c720dd54431c833e54c8720cf55321c82de63c8720b758f21c837651c8720dd54721c82fa60c8720be58321c833e5488720cf55221c833e5448720cf55121c82be6408720af59021c833e5408720cf55021c83765108720dd54421c82fa6008720be58021c833e54d0320cf55340c82ee62d0320bb58b40c833f5490320cf95240c833d5490320cf15240c82bd6590320cf59640c833e5390320cf54e40c833c5390320eb8ca40c83ad3290320cf94640c833d5190320cf95140c833d5450320bbd8940c82ec6250320cfd5040c833e5410320cf55040c833c5410320af59440c833d6510320cf94c40c833d5310320cf14c40c83ae3210320eb4c840c833e5110320cf54440c83ba6010320cf95330c833d54cc320bb98b30c82ed62cc320f34cb30c83b840cc3209f98f548827d63d5220db58b548827e61d52209f587548837a60d5220cfd52548827e63952209f58e548827e61952209f586548833f64552209fd8d548827c63552209fd85548827c6155220cf550548833e64152209f98c548827d6315220db588548827e61152209f584548837a60152209f993538827d64d4e209f987538827d61d4e20de983538835f5394e209f992538827d6494e209f986538827d6194e209fd91538827c6454e20d7d8d538827f6154e209f185538835d5314e209fd97438827e65d0e209f597438827c65d0e20bb98b43882ed62d0e209fd96438827e6590e209f59643882fa6090e20be582438827f6550e209f995438827d6550e209f19543882ef6250e20bb189438827f6510e209f994438827d6510e20cf953428833d54d0a20be98342882f960d0a20cfd52428833c5490a20cf951428833d5450a20bed8142882f86050a20cfd50428833c5410a20d794f328835d53cca20be98332882f960cca20f394f328836d53cca20f354f32882ee61cca20fa98332882ed60cca20fa583328835f538ca20d794d328835d534ca20bed8132882f8604ca20f34c832882ed650ca20db59432883ce630ca20dbd4c32883cf530ca20d3d4c328836d530ca20f314c32882ee610ca20bb58032882be6494620af592518837751946209f992518833e64946208f992518827d6494620cf592518823d64946209f98e518827d6394620b7d8d51882dc63546209fd91518827c64546209fd8d518835f635462097d8d518827c6354620d718d518825c6354620dd544518827f65d06209f997418827d65d0620cfd53418833c54d0620bb98b41882ed62d06209fd96418827e65906209f596418827f65506209f595418827c6550620cfd51418833c5450620b7d8d41882dc6350620bbd8941882ec62
  | 14 => 0x8254c833d6095320cfd9154c827f63553209f18d54c827f61553209f18554c833f6555320cfd8d54c833e6355320cf58d54c833c6355320cf98954c833c6255320cfd8554c833e6155320cf58554c833c6155320cfd8154c833d6055320cf55054c833e64153209f98c54c827d6315320db98854c827e61153209f58454c83796015320af99353c82bd64d4f20cf95353c833d54d4f20bd98753c82f561d4f20cf95253c833d5494f20d7d4e53c827e6494f209f59253c827e6194f209f58653c833e5454f20cf55153c827f6454f209f19153c827f6154f209f18553c82be6414f20af59053c833e5414f20cf55053c835d5314f209f99053c833e6414f208f99053c827d6414f20cf59053c823d6414f20db98853c827e6114f209f58453c83796014f209fd9743c827e65d0f209f59743c833e54d0f20cf55343c827f6590f209f99643c827d6590f209f19643c833e5490f20cf55243c82ee6290f20bb58a43c827f6550f209f59543c827c6550f20cf95143c833d5450f20bed8143c82f86050f209fd9443c827e6510f209f59443c827c6510f20cf95043c833d5410f20bb98843c82ed6210f20cf95342c833d54d0b20cf95242c833d5490b20be98242c82f96090b20cf95142c833d5450b20cf95042c833d5410b20be98042c82f96010b20cf95332c833d54ccb20cf95232c833d548cb20d794e32c835d538cb20be98232c82f9608cb20eb95232c83ad548cb20db94e32c83ce538cb20f354e32c836c538cb20bb98232c83ea608cb20fa58232c833e544cb20cf55132c82ef654cb20dbd9532c83ae544cb20eb55132c83cf634cb20f3d4d32c836e534cb20db14d32c83cc534cb20d314d32c82ec604cb20cf95032c833d540cb20d794c32c835d530cb20f34c832c82fa600cb20be58032c82be64d4720af59351c833e54d4720cf55351c82de63d4720b758f51c833e5494720cf55251c837751947209f99251c827d64947209f98e51c827d6394720db8ca51c836d3294720cf95151c833d54547209fd9151c827c64547209fd8d51c827c6354720af99051c82bd6414720cf95051c833d5414720dd54451c827f65d07209f99741c827d65d0720cf95341c833d54d07209fd9641c827e65907209f59641c833e5490720cf55241c827f65507209f59541c827c6550720cf95141c833d5450720b7d8d41c82dc6350720bbd8941c82ec6250720bed8141c82f860507209fd9441c827e65107209f59441c833e5410720cf55041c82ee6210720bb58841c827f65cc7209f99731c827d65cc720cf95331c833d54cc720bb98b31c82ed62cc720dd94731c837551cc7209fd9631c827e658c7209f59631c833e548c720cf55231c835e538c720d754e31c83cd328c7209fd9531c827d654c7209f19531c833e544c720cf55131c82fb604c72
  | 15 => 0x102bc654c840eb94932103ad524c840e78c932102bf614c840af18532102bf604c840eed8132102bb604c840af18132103b8604c840ae18132102bf650c840af99432102bd650c840af19432102be620c840eb8c832103ad320c840e34c832102be610c840af58432102be600c840ee98032102ba600c840af58032103b9600c840ae58032102be62d4440af58b511033f52d4440cf54b51102be60d4440ee98351102ba60d4440af59651102be6294440af58a511033f5194440edd4651103b86094440afd8951103af6254440abd8951102bc6254440eb18951102ac6254440cfd49511033d5254440edd45511033e5154440ee18151102be6214440eb98851102ae6214440af58851103ad6214440ab58851102be6114440cfd4451103b65114440cf54451103b55114440cd54451102be6014440ee98051102ba6014440afd9721102be65c8440af59721102bc65c8440af98f211039e63c8440a798f21102bd63c8440e758f211029d63c8440af18f21103ae52c8440eb54b21102be60c8440ee98321102ba60c8440af58321103b960c8440ae58321102bf6588440af99621102bd6588440af19621102bf6388440af98e21102bd6388440af58a21103af5288440eb14a21103ae3288440eb4ca21102be6188440ed94621103b55188440ebc8621103b72188440af98221102bd6088440afd9521102be6548440af59521102bc6548440afd8d21102be6348440af58d21102bc6348440eb94921103ad5248440ed94521103b55148440edc8521103ae2148440afd8121103bb6048440aed8121102bc6048440ee18121102b86048440afd9421102be6508440cf994211023e6508440af594211033d65084408f59421102bc6508440afd8c21102be6308440af58c21102bc6308440af98821103af5208440eb14821103ae3208440eb4c821102be6108440ebc8421103b62108440eb48421103b52108440af98021102bd6008440af98a50102bd6294040cf94a501033d5294040af98650102bd6194040cf946501033d5194040cf98a501033d6294040cf8ca501033d3294040cf0ca501033e6194040cf586501033f2194040cf886501033d2194040cf086501033a6094040ee59650103bb6294040ee98a50103b96294040ee18a50103bb5294040ee94a50103b95294040ee14a50103ba3294040ee4ca50103b83294040eed8650103ba6194040ae98650103b96194040ee18650103bb5194040ee94650103b95194040ee14650103bb2194040ee88650103b92194040ee086501027e63d53209f58f54c836e62d53209f98754c827d61d5320de58354c833f54953209f98e54c827d63953209f98654c827d6195320cfd8e54c833e6395320cf58e54c833c6395320cf98a54c833c6295320cfd8654c833e6195320cf58654c833c6195320cfd
  | 16 => 0xc62544409b189511033f4254440cf50951103786054440bb98851102ed6214440dd544511037651d0440dd54741102fa60d0440be58341102be62d0440af58b411033d52d0440cf94741103b651d0440ed54741103ba60d0440af58341103b960d0440ae583411027d6590440af59241102bd6590440cf59641102be6290440af58a41102be6190440cf54641103bb6090440af58241103b860904409fd9541102ef6250440bb18941102fb6050440afd95411033f6550440afd8941103af6250440abd8941102bc6250440eb18941102ac6250440cf54941103b76150440cf94541102bf6050440eed8141102bb6050440ee18141102be6410440dd94441103755110440be98041102f96010440af98841102bd6210440af98441103b66110440ed944411033d5110440ed54441103355110440ee98041102bd6010440ee580411027f65c84409f997211027d65c8440afd9321102be64c8440af59321102bc64c8440b798f21102dd63c8440db94b211036d52c8440be98321102f960c84409fd96211027e65884409f59621102bf6488440af99221102bd6488440af19221103af4288440eb10a21103765188440dd546211027f65484409f595211027c6548440afd9121102be6448440af59121102bc6448440db949211036d5248440dd94521103755148440bed8121102f860484409fd94211027e65084409f59421102bf6408440af99021102bd6408440af19021103af4208440eb108211033f4294040cf90a501033d4294040cf10a501033f4194040cf906501033d4194040cf10650102be62d0040af58b40102be61d0040af58740102bd6490040cf95240102f96490040de95240103ba5490040eed0a40103ba4290040ee50a40103b84290040be98640103bb4190040ee90640103b94190040ee106401027f6550040afd95401033f65500408fd9540102bf6250040af18940102bf6150040af18540102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040be18540103ba4150040ee10540102be63d4840af58f52102be61d4840af58752102be60d4840ee98352102ba60d4840af59652102be6394840af58e521033f5294840ebd4a52102be6194840af58652102bf6354840af18d52103af5254840cf94952102bf6154840af18552102be6314840e798c521029e6314840af58c521039d6314840a758c52102be6214840cfd4852103ae5214840cf54852103ad5214840af98452103b66114840ad98452102bd6114840ed58452102b56114840af98052103ba6014840ae98052102bf658c840af99632102bd658c840af19632102bd638c840af98a32103ae528c840eb54a32103af328c840af98632102bd618c840af98232102bd608c840afd9532102be654c840af59532
  | 17 => 0x8640af994219033e65086408f99421902bd6508640cf594219023d6508640af19421902bf6308640af98c21902bd6308640af18c21903ae5208640eb54821903ae3208640eb4c821903af2108640ed88421903ad2108640ed48421902be6008640af580219027e63d49409f58f525027e61d49409f587525036f5294940b7d8d52502dc6354940bdd8552502f46154940db548525027e63149409f58c525027e61149409f584525027e65d0940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940bed8142502f860509409f994425027e658c9409f596325027c658c940d7d4e325035c538c9409fd95325027e654c9409f195325027e650c9409f594325027c650c940dbd48325036c520c940f34c8325027e62d45409f58b51503775194540bbd8951502ec6254540dd544515027e62145409f588515027e65d0540ddd4641503745190540be98241502f96090540bbd8941502ec6250540ddd4541503745150540bed8141502f860505409f99441503b541105409f997215027d65c85409f19721502de63c8540b758f215037751c8540dd147215027e65885409f596215027c6588540dbd4a215036c52885409fd95215027e65485409f195215027e65085409f594215027c6508540af99021502bd6408540dbd48215036c5208540ddd4421503745108540de147405033f5290140cf14a405033f5190140cf14640503bb5090140dbd4a521027e63948409f58e521027e61948409f586521027f63548409f18d521027f61548409f18552102de6314840b758c521036d5214840bd98452102f56114840db94b421036d52d0840be98342102f960d0840af98f42102bd63d0840cf94b42103ae52d0840eb54b42102be61d0840af58742103ba60d0840af58342103b960d08409f59642102bd6490840af596421033d6590840af98e42102bd6390840af98a421033d5290840af98642102bd6190840af582421027f6550840afd95421033f6550840afd8d42102bc6350840ebd89421033e5250840afd8542102bc6150840afd8142102be6410840db948421036d5210840be98042102f96010840af98c42102bd6310840af98842103ae6210840eb948421033d5210840eb54842102be6110840af58442103ba6010840af58042103b960108409fd96321027e658c8409f59632102bf648c840af99232102bd648c840af192321036e528c840db54a321027f654c8409f595321027c654c840afd9132102be644c840af59132102bc644c840db949321036d524c840bed8132102f8604c8409fd94321027e650c8409f59432102bf640c840af99032102bd640c840af19032103cd320c840be98032102f9600c840ddd46511027e62944409f58a51102ef6254440bb189511027f6254440dbd89511026f62544409f189511036
  | 18 => 0xaf58241903b96090640bbd8941902ec6250640dd94541903755150640bed8141902f86050640afd8941903af6250640abd8941902bc6250640eb18941902ac6250640cf54941903b76150640cf94541903b65150640cd94541903b55150640afd8141903bb6050640ee18141902bd6510640cf59441902be6210640af58841903b66110640cf54441902bd60106409fd97219027e65c86409f59721902bf64c8640af99321902bd64c8640af19321902de63c8640b758f219027f65886409f996219027d6588640afd9221902be6488640af59221902bc6488640db94a219036d5288640ebd0a21903ac42886409fd95219027d65486409f19521902bf6448640af99121902bd6448640af191219027f65086409f994219027d6508640afd9021902be6408640af59021902bc6408640db948219036d5208640ebd0821903ac4208640af597409033d65d0240af98b40902bd62d0240af98740902bd61d0240be597409037965d0240de94740902be63d4a40af58f52902be61d4a40af58752902be60d4a40ee98352902ba60d4a40af98e52902bd6394a40cfd4a52903af5294a40af98652902bd6194a40afd8d52902bc6354a40ebd49529033e5254a40afd8552902bc6154a40af98c529039e6314a40a798c52902bd6314a40e758c529029d6314a40cfd4852903ae5214a40cf54852903ad5214a40af98452902bd6114a40af98052903ba6014a40ae98052902bf658ca40af99632902bd658ca40af19632903ae528ca40eb54a32903af328ca40af98632902bd618ca40af98232902bd608ca40afd9532902be654ca40af59532902bc654ca40eb94932903ad524ca40e78c932902bf614ca40af18532902bf604ca40af18132902bf650ca40af99432902bd650ca40af19432903ae320ca40eb4c8329038d320ca40af98432902bd610ca40af98032902bd600ca40af98b51903ae62d4640ab98b51902bd62d4640eb58b51902ad62d4640cfd4b519033d52d4640af98351903ba60d4640ae98351902be6294640af58a519033f5194640edd4651903375194640afd8951902bc6254640cfd49519033d5254640edd45519033e5154640af98851902bd6214640cfd4451903b65114640cf54451903b55114640af98051903ba6014640ae98051902bf65c8640af99721902bd65c8640af19721902be63c8640e798f219029e63c8640af58f219039d63c8640a758f21902bc63c8640af98321902bd60c8640afd9621902be6588640af59621902bc6588640afd8e21902be6388640af58e21903ae5288640eb54a21903ae3288640eb4ca21903af2188640edc8621902be6088640af58221902bf6548640af99521902bd6548640af19521902bf6348640af98d21902bd6348640af18d21903b72148640eb88521902bf6048640af18121902bf650
  | 19 => 0x1500867f6354021d7d8d500865f63540219f18d500875c63540219718d500876e3254021db4c950086be6414021af590500873e5414021cf55050086de6314021b758c50087795014021b798f52d02dd63d4b40bd98752d02f561d4b40dbd4a52d027e6394b409f58e52d027e6194b409f58652d027f6354b409f18d52d027f6154b409f18552d036d5214b40db94b42d036d52d0b40be98342d02f960d0b40db94842d036d5210b40be98042d02f96010b409fd9632d027e658cb409f59632d035e538cb40d754e32d027f654cb409f59532d027c654cb40bed8132d02f8604cb409fd9432d027e650cb409f59432d036e520cb40db54832d03cd320cb40be98032d02f9600cb40bb98b51d02ed62d4740ddd4651d027e62947409f58a51d027f62547409f18951d037b6054740dd54451d037651d0740dd54741d02fa60d0740be58341d02ef6250740bb18941d02f86050740dd94441d03755110740ed50441d02fa6010740be58041d027f65c87409f99721d027d65c8740b798f21d02dd63c8740dd94721d037551c8740be98321d02f960c87409fd9621d027e65887409f59621d036e5288740db54a21d027f65487409f59521d027c6548740bed8121d02f860487409fd9421d027e65087409f59421d02be6408740af59021d036e5208740db54821d03765108740dd54421d036f5294a409f98e529027d6394a409f986529027d6194a409fd8d529027c6354a409fd85529027c6154a40b798c52902dd6314a40db54852902bd65d0a40cf59742902be63d0a40af58f429033e52d0a40af98742902bd61d0a40af583429036e5290a40db54a42902fa6090a40be58242902be6390a40af58e42903ae5290a40cf54a42903ad5290a40af98642902bd6190a40ee98242902bd6090a40ee582429036e5250a40db54942902fb6050a40be18142902bf6350a40af18d42903af6250a40cf94942903ae5250a40eb54942902bf6150a40af18542902bf6050a40eed8142903b86050a40af594429033d6510a40af98c42902bd6310a40eb988429033d5210a40af98442902bd6110a40af580429027f658ca409f996329027d658ca40afd9232902be648ca40af59232902bc648ca40db94a329036d528ca409fd95329027d654ca409f19532902bf644ca40af99132902bd644ca40af191329036e524ca40db549329027f650ca409f994329027d650ca40afd9032902be640ca40af59032902bc640ca40f34c832902ee62d4640bb58b519037751946409f98a519027d62946409fd89519027c6254640cfd09519033d4254640dd54451902bd65d0640cf59741902be62d0640af58b419033d52d0640cf94741902bd60d0640dd94641903755190640be98241902f96090640af98a41902bd6290640ed946419033d5190640ed54641903ba6090640
  | 20 => 0x86ee6410821eb990420876f5410821eb950420876d5410821eb55042086ed6310821f998442086ed6110821f958442086e56110821bb980420867d65cc821cf953320873d54cc821d7d4f320867f658c8219f596320873e548c821cf552320875e538c821d754e32086f6618c821bd586320876d658c8219b59632086ee648c821bb19232087ae548c821eb55232086ed638c821db94e32087ce538c821f354e320876c538c821f998632086ed618c821f958632086e5618c821bb982320867f654c821cf951320873d544c821d7d4d32086ef654c821dbd9532086ee644c821bb19132087ae544c821eb55132087cf634c821f3d4d320876e534c821db14d32087cc534c821d314d32086ef614c821bb181320867f650c8219f594320873e540c821cf550320875e530c821d754c32086ee620c821f34c832086f6610c821bd584320867e64944219f592510867e63944219f58e510876f4294421db10a510876e3294421db4ca510867d65d0421cf953410873d54d0421ebd0b410867f65904219f596410873e5490421cf55241086ee6290421bb58a410867f6550421cf951410873d5450421b7d8d41086dc6350421bbd8941086ec6250421ebd0941086fb6050421be181410867f65104219f994410867d65104219f194410873e5410421cf55041086ee6210421bb58841087b541104219f597310873e54cc421cf55331086ee62cc421bb58b310867f658c4219f596310873e548c421cf552310875e538c421d754e31086ee628c421bb58a31087cd328c4219fd95310873e544c421cf551310867e650c4219f594310867c650c421cf950310873d540c421bb98831086ed620c421f34c8310873e54c8421cf55321086de63c8421b758f21086ee64c8421bb19321087ae54c8421eb55321086ef63c8421f398f21086ed63c8421f358f21086cd63c8421bb983210873e5488421cf55221086ed6288421db94a21087b65488421ed55221086f56288421dd94a21087e65288421f9d0a21087e44288421f98ca21087e53288421bd982210867f6548421cf951210873d5448421bbd95210876f65484219bd9521086ee6448421bb19121087ae5448421eb55121086ef6348421bb58d21086ef6148421db94521087e64148421f950521087e73148421f90c521086ec6048421bdd95210877765484219dd9521087b65448421ed55121086f76248421f9d8921087765248421f994921087e64248421f950921087e73248421f90c921086f46048421af99350086bd64d4021cf953500873d54d4021cf952500873d5494021ded42500873f64940219f992500867d6494021cf192500867e63940219f58e50086bf6454021af191500873e5454021cf55150086df6354021b718d500867f6454021cfd91500863f64540219f191500873c64540218f19
  | 21 => 0x5388521db54e21487e75188521af99350486bd64d41219f993504873e64d41218f993504867d64d4121cf593504863d64d41219f98f504867d63d4121ded4250486bf6454121af19150486df6354121b718d504877950141219f990504867d64141219f98c504867d6314121ddc84504876e21141219f98f540867d63d50219f98b540876e62d50219f987540877661d50219f983540867d60d50219f596540873f54950219f98e540867d63950219f982540867d60950218f59654087ac6295021af982540873f6395021cf98e540873d6395021cf18e540873e6295021cf18a540873e6195021cf186540873f6095021cf982540863e6095021cf582540873c6095021cfd91540867f63550219f18d540876c62550219fd81540867c6055021cfd9554087ac6255021af181540873f6355021cf98d540873d6355021cf18d540873e6255021cf189540872c6255021cf985540873c6155021cf085540873f6055021cf981540873d6055021cf181540863c6055021af990540873d54150219f990540873e64150218f990540867e63150219f58c540867e6215021db988540867e6115021dd984540867e60150219f58054086be64d4c21af593530873e54d4c21cf553530867e64d4c21cf993530863e64d4c219f593530873d64d4c218f593530876e62d4c21dd987530867e60d4c219f583530867d6594c21cf952530873d5494c21d7d4e530867e6494c219f592530876e6294c219f982530867d6094c21cf951530873d5454c219fd91530867c6454c21d7d8d530867f6054c219f18153086be6414c21af590530873e5414c21cf550530875d5314c21be98053086f96014c219f990530873e6414c218f990530867d6414c21cf590530863d6414c219f988530876e6214c219f98453087766114c219f980530877a6014c219e980530867d6014c21de58053086796014c219fd97430867e65d0c219f597430867c65d0c21cf953430873d54d0c219fd96430867e6590c219f596430867c6590c21cf952430873d5490c21bb98a43086ed6290c219fd95430867e6550c219f595430867c6550c21cf951430873d5450c21bbd8943086ec6250c21bdd8543086f46150c219fd94430867e6510c219f594430867c6510c21cf950430873d5410c21bb98843086ed6210c21bd98443086f56110c219f992520867d6494821d798e520867d6394821d758e520865d63948219f597420873e54d0821cf55342086ed65d0821db597420876f54d0821eb953420876d54d0821eb553420872d54d0821bb58f42086ed61d0821bb983420867f65908219f596420873e5490821cf55242086ee6290821bd98642086f561908219fd95420873e5450821cf551420867f65108219f594420873e5410821cf55042086f66110821bd584420876d65108219b594420
  | 22 => 0x621ebd0941886fb6050621be181418873e5410621cf55041886ee6210621bb58841886ee62cc621bb58b31886ee628c621bb58a31887cd328c621b798f21886dd63c8621bb597218876d65c8621bb99321886ec64c8621f398f21886ed63c8621f358f21886cd63c8621bb98321886f565c8621dd59721887d663c8621f558f21886be64d4221af59350886de63d4221b758f508877b50942219f992508867d64942219f98e508867d6394221ddc8650886bf6454221af191508867f6454221cfd91508863f64542219f191508873c64542218f191508867f63542219f18d508876e3254221db4c9508877950142219f98f544867d63d51219f983544867d60d5121cfd52544867e64951219f98e544867d63951219f58a544876d62951219f586544877561951219f982544867d6095121b7d8d54486dc6355121bed8154486f86055121cfd91544867f6355121d7d8d544865f63551219f18d544875c63551219718d544867f6255121dbd89544866f62551219fd85544877761551219fd81544877b60551219ed81544867c6055121de181544867860551219f994544873d5415121cf990544867e63151219f58c544867e60151219f580544867e64d4d219f593534867e60d4d219f583534875f5394d219f992534867d6494d21db58a53487756194d219f982534867d6094d21afd9153486bc6454d21bed8153486f86054d219fd91534873f6454d218fd91534867c6454d21cf191534863c6454d21dbd89534867f6154d21ddd85534867f6054d21ded81534867b6054d219f18153487786054d219e181534867e6514d21d754c534867e6414d219f590534875e6314d219f980534867d6014d219fd97434867e65d0d219f597434867c65d0d21d7d4f434875c53d0d21bb98b43486ed62d0d21bd98743486f561d0d219fd96434867e6590d219f596434867c6590d21cfd52434873c5490d219fd95434867e6550d219f595434867c6550d219fd94434867e6510d219f594434867c6510d21cfd50434873c5410d21d7d4c434875c5310d219f997424873f54d0921cf15342486f661d0921bd587424867e65909219f195424873f5450921cf15142486f76150921bd185424867e6510921d7d4f324875c53cc921bd98732486f561cc9219f996324875f534c921d714d32486f7614c921bd185324867e650c921f34c8324867e65d0521cfd53414873c54d0521bb98b41486ed62d05219f996414867f65505219f595414867c6550521cfd51414873c5450521b7d8d41486dc6350521bbd8941486ec6250521bed8141486f860505219f994414867e65cc521d7d4f314875c53cc521bb98b31486ed62cc521d794e314867d654c5219f19531486ef624c521bb18931486de63c8521b758f21487d663c8521f558f214876e5488521db152214876f
  | 23 => 0xf55042c875e5310b21d754c42c86f66110b21bd58442c875d53ccb21d794e32c875d538cb21bd98632c86f5618cb21d794d32c875e530cb21d754c32c87cd320cb21bd98432c86f5610cb21cf95341c873d54d0721d794f41c875d53d0721bb98b41c86ed62d0721d794e41c875d5390721cf95141c873d5450721b7d8d41c86dc6350721d794d41c875d5350721bbd8941c86ec6250721bed8141c86f86050721d794c41c875d5310721ed50441c86ee62cc721bb58b31c86be64d4321af59350c86de63d4321b758f50c875e53d4321d754f50c875e5394321d754e50c877b50943219f99250c867d64943219f98e50c867d6394321afd9150c86bc6454321d794d50c875d53543219fd9150c873f64543218fd9150c867c6454321cf19150c863c64543219fd8d50c867c6354321b798c50c86dd6314321d794c50c875d5314321de54050c867e63d52219f58f548876d62d5221dd987548867e60d52219f583548873f54952219f98e548867d63952219f982548867d6095221cfd91548867f63552219f18d548876f62552219fd81548867c6055221cf55054886de6315221b758c548873e64152219f98c548875e63152219798c548867d6315221d758c548865d6315221db588548877661152219f980548867d60152219f993538867d64d4e21dd987538867e60d4e219f583538875f5394e219f992538867d6494e21db58a538867e6094e219f582538867f6454e219f191538875f6354e219fd81538867c6054e21af99053886bd6414e21d754c538867f65d0e219f997438867d65d0e219f197438873e54d0e21cf55343886f661d0e21bd587438867f6590e219f996438867d6590e21d794e438875d5390e21bb98a43886ed6290e219fd95438867e6550e219f595438867c6550e21cf951438873d5450e21d794d438875d5350e21bbd8943886ec6250e219fd94438867e6510e219f59443886ee6210e21bb588438873e54d0a21cf55342886f661d0a21bd587428876d65d0a21dbd5342887ae54d0a21db55342887ad54d0a21bb58f42887e661d0a21bb58742887e561d0a21bb983428873e5450a21cf55142886f76150a21bd18542886ed6510a21db59442887ae6410a21dbd50428876d5410a21bb58c42886ed6110a21bb980428875e53cca21d754f32886f661cca21bd58732886ed658ca21db59632886ee648ca21bb192328876e538ca21bb58632886ee608ca21d794d328875d534ca21bdd8532886f4614ca21dbd9532886ee644ca21bb19132887cf634ca21db94d32887ce534ca21d394d32887cd534ca21bbd8532887e7614ca21f918532886ec604ca21f34c8328873f54d0621cf15341887af42d0621cf952418873d5490621bb98a41886ed6290621cfd51418873c5450621b7d8d41886dc6350621bbd8941886ec6250
  | 24 => 0x521067f63548419f18d521067f60548419f181521076d5214841cf953421076e52d0841db54b42106f661d0841bd587421067d65908419fd95421073e5450841db948421076d5210841bd98442106f561108419fd96321067e658c8419f596321075e538c841d754e321067f654c8419f595321067c654c841afd9132106bc644c841bdd8532106f4614c8419fd94321067e650c8419f594321076e520c841db54832107cd320c841cf54b41106be60d0441af592411073e5490441bd59241107765490441ed952411067f6550441bbd8941106ec6250441bed8141106f86050441afd95411073f65504418fd9541107af6250441eb189411073d5250441afd85411073e5150441eed8141106bc6050441ee18141106b86050441bdd95411077765504419dd9541106f76450441edd9141107765450441ed95141107e76250441f918941107b64250441ed10941107f36050441fc181411077b5094041cf192501067e62940419f58a501073f4194041cf506501067f62540419f18950106ee6214041bb58850107795014041b798f54c86dd63d5321be98354c86f960d53219f98f54c875e63d53219798f54c867d63d5321d758f54c865d63d5321db98b54c877561d53219f98354c877a60d53219e98354c867d60d5321de58354c867960d5321cfd5254c867e63953219f58e54c867e60953219f58254c873f64553219fd8d54c867c63553219fd8154c867c6055321cf55054c86de6315321b758c54c873e64153219f98c54c875e63153219798c54c867d6315321d758c54c865d6315321db98854c877561153219f98054c867d6015321d7d4e53c867e6494f219f59253c867e6094f219f58253c875f5494f21d795253c875d5494f21d715253c875f6494f21d799253c875d6494f21d719253c875c6294f21d7d8653c875d6194f21d7d8253c875e6094f21d758253c875c6094f219fd9153c867c6454f219fd8153c867c6054f21d7d9553c875f5454f21d795153c875d5454f21d715153c875f6454f21d799153c875d6454f21d719153c875e6254f21d7d8553c875d6154f21d7d8153c875e6054f21d758153c875c6054f21d754c53c867e6414f219f59053c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f21d794f43c875d53d0f21bb98b43c86ed62d0f219fd9643c867e6590f219f59643c867c6590f21d794e43c875d5390f219fd9543c867d6550f219f19543c875e5350f21d754d43c86f76150f21bd18543c867f6510f219f99443c867d6510f219f19443c875e5310f21d754c43c86f66110f21bd58443c873f54d0b21cf15342c875e53d0b21d754f42c873e5490b21cf55242c875e5390b21d754e42c86f66190b21bd58642c873f5450b21cf15142c875e5350b21d754d42c873e5410b21c
  | 25 => 0x6de6394941b758e525075f5394941dbd4a52506fa6094941be58252506df6354941b718d525075f5354941bed8152506f86054941d7d4c525076d52149419f98c525067d63149419f980525067d6014941bb994525076e6514941eb590525076f5314941f3d4c525074f5314941db94c525076d5314941db14c52507cc5314941d314c525076f6414941dbd8c525076e6314941db58c525076c6314941dbd84525076d6114941db504525076f6014941db980525076d6014941db180525067e65d0941d7d4f425075c53d0941db14b42506be65d0941cf99742506bd63d0941e7d4f425079c53d0941ebd4b425073c52d0941eb14b425072c52d0941af98742506be60d0941af592425075f5390941d714e425076f5290941db14a42506f66190941bd586425075f5350941d714d425076f5250941db14942506f76150941bd18542506bf6350941e7d4d425079c5350941ebd8942507af5250941cf14942507ac5250941edd8542506bc6150941ed18542506b46150941af181425067e6510941af990425075f5310941d714c425076f52109419f996325067d658c9419f19632506be648c941af592325075f538c941d714e325076f528c941db14a32506f6618c941bd586325067f654c9419f995325067c654c941af99132506bd644c941dbd49325076c524c9419f994325067d650c9419f19432506be640c941af590325076f520c941db14832507cd320c941dbd4b415076c52d0541f9d4b41507e452d0541edd0b41507b542d0541dbd4a415076c5290541af58a41507af5290541eb14a41507b75190541af982415076f52d4141db14b505067e62d41419f58b50507b964d4141ded4b50507eb52d4141dad4b505077a52d4141de54b505077852d4141fa14b505076852d4141eed0b50507b942d4141fcd0750507ba41d4141ded93505077b62d4141de98b505077962d4141de18b505077b42d4141de90b505077942d4141de10b505077a32d4141de4cb505077832d4141ded87505077b41d4141de90750506ee6294141bb58a505076f5294141db14a505077b5094141bbd8950506ec6254141dbd49505076c5254141dbd48505076c5214141de540505073f64141419f988505067d6214141cfd08505073d4214141cf90450506fa6514141de99450507bb6414141ded4850507eb5214141dad48505077a5214141de54850507785214141fa14850507685214141eed0850507b94214141fcd0450507ba4114141ded90505073b6414141ded88505077a6214141de58850507786214141ded08505073b4214141de90850507794214141ce50850507784214141de8c850507793214141de0c8505077b6114141ded04505077a4114141ce90450507794114141b798f52106dd63d4841dbd4a521067e63948419f58e521067e60948419f582
  | 26 => 0x54c832dbd95320ca6f654c832bbd8d320cb6e534c832f394d320cbcf434c832f390d320cbcd434c832f310d320caec604c832f3d95320cacf654c832d3d95320cbcf644c832f3991320cbcd644c832f3191320cbcf544c832f3951320cbcd544c832f3151320cbcf614c832f3985320cbcd614c832f3185320cbcf604c832f3981320cbcd604c832f3181320cacc604c832f34cb510cbcd3294432ddd46510ca7e64944329f592510cb6e3294432db4ca510cb4d32944329f982510ca7d6094432f34c9510ca7f64544329f191510ca7f60544329f181510cabe6414432af590510cbcd3214432dd544510cafa6014432be580510cabe64d4032af593500cbcd32d4032f34ca500cb7b50940329f992500ca7d64940329f986500ca7d6194032afd91500cabc6454032f34c9500caf76154032bd185500ca7f6454032cfd91500ca3f64540329f191500cb3c64540328f191500cb6e3254032db4c9500cb4d32540329fd85500cb7761540329dd85500ca7c6154032dd185500ca746154032f34c8500cb795014032dbd4a52d067e6394b419f58e52d067e6094b419f58252d067f6354b419f18d52d067f6054b419f18152d06de6314b41b758c52d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41af58f42d073e52d0b41eb94b42d07ad52d0b41af98742d07b661d0b41ed58742d06be60d0b41afd9542d073f6550b41afd8d42d07af6250b41cf94942d06bc6150b41af18142d076e5210b41db54842d06f66110b41bd58442d067f658cb419f99632d067d658cb41af99232d06bd648cb41db94a32d076d528cb419fd9532d067d654cb419f19532d06be644cb41af59132d076e524cb41db54932d06f7614cb41bd18532d067f650cb419f99432d067d650cb41af99032d06bd640cb41f34c832d06ee62d4341bb58b50d077b5094341cf19250d067e62943419f58a50d073f4294341cf50a50d067f62543419f18950d07795014341dbd4a529067e6394a419f58e529067e6094a419f582529067f6354a419f18d529067f6054a419f181529076d5214a41db94a429076d5290a41bd98642906f56190a41db949429076d5250a41bdd8542906f46150a419fd96329067e658ca419f59632906f6618ca41bd586329067f654ca419f595329067c654ca41afd9132906bc644ca419fd94329067e650ca419f59432907cd320ca41af597419073d65d0641cf54b41906be60d0641bd597419077565d0641ded42509073f64942419f98a509067d6294241cfd06509067f62542419f189509077950142419f98f525067d63d49419f983525067d60d4941ebd93525076f53d4941f3d4f525074f53d4941dbd93525076f63d4941db98f525076d63d4941db18f525076f61d4941db587525076f60d4941db983525076d60d4941db1835250
  | 27 => 0x329f984548cb7661152329d984548ca7d6115232dd584548ca7561152329f980548ca7d6015232cf953438cb3d54d0e32bb98b438caed62d0e32cf951438cb3d5450e32bbd89438caec6250e32e750c438cb3e5490a32cf552428cade6390a32b758e428cb3e5410a32cf550428cade6310a32b758c428caed65cca32db597328cb7751946329f992518ca7d6494632d7cca518ca7e60946329f582518ca7f64546329f191518ca7f60546329f181518cabe6414632af590518cb755114632af993508cabd64d4232bd987508caf561d4232ded42508ca7e64942329f592508cb6f32942329f986508ca7d6194232afd91508cabc64542329fd91508cb3f64542328fd91508ca7c6454232cf191508ca3c6454232d7cc9508ca7f61542329f185508cb7950142329f987544ca7d61d51329f983544ca7d60d5132cfd52544ca7e64951329f58a544cb6d62951329f986544ca7d61951329f982544ca7d6095132bdd85544caf46155132bed81544caf86055132cfd91544ca7f6255132dbd89544ca7f6155132ddd85544ca7761551329f185544cb7461551329d185544ca7f6055132ded81544ca7b60551329f181544cb7860551329e181544ca7e6515132cf550544cb3e64151329f984544ca7d61151329f980544ca7d60151329f997424cb3f54d0932cf153424cade63d0932b758f424ca7e65909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424ca7e6510932f3d4a324cade618c932b7582324ca7e64d45329f593514ca7e60d45329f583514cb775194532afd91514cabc6454532bed81514caf86054532af990514cabd6414532dd544514ca7e6414532cf990514ca3e64145329f590514cb3d64145328f590514ca7e60145329f580514cabe64d4132af593504ca7e64d4132cf993504ca3e64d41329f593504cb3d64d41328f593504ca7e61d41329f587504cb7b5094132afd91504cabc6454132bdd85504caf46154132de540504ca7e64141329f590504cb5e32141329f984504ca7d6114132be983540caf960d50329f98b540cb6e62d50329f987540ca7d61d50329f983540cb7a60d50329e983540ca7d60d5032de583540ca7960d50329f596540cb3f54950329f986540ca7d61950329f982540ca7d6095032cfd91540ca7f61550329f185540ca7f60550329f181540cb3d54150329f990540cb3e64150329f988540cb6e62150329f984540ca7d61150329f980540ca7d60150329f992520ca7d64948329f597420ca7f65908329f596420cb3e5490832cf552420cade6390832b758e420ca7f65508329fd94420ca7e65108329f594420ca7c6510832cf950420cb3d5410832b798c420cadd6310832eb508420caed638c832b358e320cb6e538c832f394e320caee608c8329fd95320caef6
  | 28 => 0x54451d0ade63d4342b758f50d0af661d4342bd58750d0b7b5094342cf19250d0a7e63943429f58e50d0a7e61943429f58650d0a7f63543429f18d50d0a7f61543429f18550d0b795014342d7d4e5390a7e6194e429f5865390a7e6094e429f5825390a7f6154e429f1855390a7f6054e429f1815390b5d5314e42be9805390af96014e42bb98a4390aed6290e42af5974290b3d65d0a42af9834290aed65d0a42db5974290ade63d4642b758f5190afa60d4642be5835190b7751946429f98e5190a7d6394642dbd0a5190a7e60946429f5825190a7f63546429f18d5190b3f42546429fd815190a7c6054642dd5445190b7b5094242cfd925090a7e63942429f58e5090b3f42942429f9865090a7d61942429fd8d5090a7c63542429fd855090a7c6154242b798c5090add6314242de5405090a7e61d4d429f5875350a7e60d4d429f5835350b5f5394d42bdd855350af46154d42bed815350af86054d42d754c5350a7e6114d429f5845350a7e6014d429f5805350b5f5390d42d714e4350aee6290d42bb58a4350aef6250d42bb1894350baf5290942af5864250abe60909429f98f5150a7d63d45429f9835150a7d60d4542ddd465150adf6354542b718d5150afb6054542be1815150b7551145429f98c5150a7d6314542dbd085150a7e60145429f5805150a7e63d41429f58f5050a7e61d41429f5875050b7b5094142b7d8d5050adc6354142bdd855050af46154142de5405050b3f64141429f98c5050a7d6314142cf9085050a7e61141429f5845050af661d4c42bd5875310b5f5394c429f9865310a7d6194c429f9825310a7d6094c429fd855310a7c6154c429fd815310a7c6054c42d754c5310b5e53d0c42d754f4310aee62d0c42bb58b4310a7d6590c429fd954310aee6210c42bb5884310abe60d0842af5924210b3e5490842bb5924210b6e5490842eb9524210aee61908429fd954210abf6550842cfd954210a3f6550842afd894210b3e5250842af1814210aef6550842dbd954210a6f6550842bbd914210baf6450842db9514210bae5450842eb90d4210bac4350842bb1854210ade63d4442b758f5110b7751944429f98e5110a7d63944429f9825110a7d60944429fd8d5110a7c6354442cfd095110b3d42544429fd815110a7c6054442dd5445110b7b5094042cf1925010a7e63940429f58e5010b3f4294042cf50a5010a7e61940429f5865010a7f63540429f18d5010a7f61540429f1855010ade6314042b758c5010af66114042bd5845010b795014042d758f548cb6e62d52329f987548ca7d61d52329f983548ca7d60d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cf550548caf66115232bd584548cb3e6415232d758c548cb6e62152
  | 29 => 0x44003000c003000000b0010003006c005000000b0010005000801100200000014001000400e0060005000803f001801f00600000000002002000700000030034001000c00100000010004040000c011000800000140010010001002400a00040020018002002c000003001400080020020002000800c000000000080030008013000000500540010000008002c0050000000000000200000030004000004000d00040030060003001000100080070020002003c008002800800140000000000002c00300000020008000001000b00000000044003000000a000c0240008004000001a00000010020004002c0000000002000000000040010000001001000000040010008000003c0100014006001002c00000010010000004c000006800100000010020002001800500040030004000001c014000800a000000200280000000001000000200940010008015000800c002800200000070058006000000100040050008000001c0010044001000000000080000004002000800d00000100144012000400e000000000a0002000000a0000001002c0110000001002400000c80060004014000c0030010000003400100900010014005000000500180000000003000400300100000004000000800c0008001000001f00000090040005000c0330038001004c007000001a0004003008000200040020018002001400b00000000004005008800000240000004000002000700000050064006000c00f000800300040000000008000c000001400a000000000a8023001400200040010010018000c00000440010008000000c004000400000240020010014000000600440020008001000000200000000000001001800a000000000040070088000001c0000054009005000000000150010003000000900000000000002000000200080020004003005000c00040000020008007400500080050020007001800f00100000000010000c009000000c0000001001c0020000008000c00200080000004000000c00e00000000008000007800000140020000000002000000240050000000001400b0030000000c0170004002000000e0010006001c00100280040050006000000c00540010000014000c0010014007000000900080050044000000c0000030000000800200180070004001000400b00880010010003001c00800080000030016000c002002000a002c001000801200235f5394f429f98653d0a7d6194f429f98253d0a7d6094f429fd8553d0a7c6154f429fd8153d0a7c6054f42d754c53d0af66114f42bd58453d0aee62d0f42bb58b43d0b7751947429f98e51d0a7d63947429f98251d0a7d6094742b7d8d51d0adc63547429fd8d51d0b5f635474297d8d51d0a7c6354742d718d51d0a5c63547429fd8151d0a7c6054742b798c51d0add6314742dd
  | 30 => 0x5000c0030010008001000400000050004012000000b0008007000800000000020054000000000b00040030024003000401800440130034001002c002000800b0018007000400200000060000000000800500100540004001000c00000400000030000000c04f000000000280050000001005c00b000000a0004003005c0000040002000000e002c000000800800200000000001000c00200000020000000000000200080010000000004c000001c00200100160020000000800a001800400040020008000000801000240050050002006c001003c0000014000007c002000400b00040040078000001c000000000b000c000004c00b0008003000000d000000500040000008003002000100040000000000003c00b00000030004005003000200140000034001000000c002c004000400000000000050004001c002003801600100120010005001000100000010004001001c000001c00e00000020018004001000e00100070000002001c0070030000003401b0024002000c001002002000100000018000001c00e000c00000040060000009001c0100008001007c000001801d0000002000000000000020000004005800000000010000020004800800000030024003000c004000800e000c00000000060000000000800400040000004007000c0310014003001402100100020000000000000000040000000001001400000000000040001000000a0048001001000000000000014002000000b000c0040000003001400000000040018002000000300480090020016000000d0004000000001700000110000014002c0020004002001c0050000000000400100000080008002000c0020004019000c000006c003000c0340010009000c00500000040008003000400f001c00500040010000010001001a0014003000c0010068005000000d0000012000400200040040000001010400c000c00d0014000000001e002c0000000000000800f001c00300400040020022000000200180060004002002000900040070004001002000600000100000012002c0000128000003c000005c00600a000a0004000000400d00000030010000000002000340000020002002c00d003c002000000700040010000001002c002002c00f00100010008000000400f000c001000c00e008c0040008011000000000a001c000000d0000007001000400000020008000005c000000000a001c0070020000000403a002c00100000010000005000005200080010000005000400300040090004000000000000280000000000003800800200010000007002c005002800800140000004006002000000080000000001000001a00000000010001000400300240000064002001001a00280000024000000c006000001700040020004000000401400140000010007001000000
  | 31 => 0x800400ac005001c00f000004000280200000002001800c00000160020001000000f000400a003000800080100000003005c00b003800000000020030003000c0000058010000c002000000a0008000000c006000001f000000800000080000000002000b00a4020002000000bc001000401d000400800a00000004004001c0060000002000c005000c000000000700000010000005000c0320030001005c00000000040024007000c00000080100018001000000100100030010006001800000440010000005001c0030008004000000f013000a00000000004001000c00200940000018007000c0030020001000800000080020040000001800000100010000008000400b000800100000010000006000c01500340030090000003400100040310000001001000c001400e006800e000c008003000800000030028012000000a0000000000800b004400c00000030004001000400c00040010030000001c0010018000000400200300040000008004400000240240000019005c001009c00a00000000000001002000600000100008024000001600000000008004005c00900180080014003002400d0000001000c000000800a00000000028000000400400340040044051000400000000080004000002c011003800200100110004012000c007000c0010000000000c0040020003000c006000c004000000f002400000040040010002002c00a0018000001c014000c009000400000000040000010001000100180030000005003800200300010030001010c004004400f00000030008000000c001000400b0000006000c004002800300040080014020004800d000400400440110038002000c002000400e00040000000000000c00600000010008004000c009000003d00b4000001800d003800400300020000003000401500040060000004001400200400000004008003c00000b40020000005008000000040020018001000c00f0004001000000000140040000004000000000580000000000005000200000000004000000000000000000010000000400d00040010014005001000f006c00d002c000000000500040000000006001c001000400a002400000040000044011000401d0004001000800700640000058000001c003001000000040080038000006c00e00280020010002001400c0008000000000500280070014006000000200000040000002000000c000000000040000000001003001400400010000003002c002001400500040150000003000c00c0004002000000400340060000007000800800040070008010002400a000c001000c01400a80000048002000400100100040004003002403e000400c000c00000000000000001001c000004c001000000000080010004007000c0040000004000c0050018001000000400200
  | 32 => 0x900100040008003000400c00000010018006001c0040008006001c0000004006007400c0004002002800100000000038004002c00a000000100a4000000000700000040000000000c006001c0090008000001400200040080000000002800000040070004004001401800000080004001001401a0008000000000000000020068004004c01a0008006000000000000250000003000000c0038000001000100000010024004000000400280000044011000c0010038003000c0080020006002402a00180240000004002000400000010000007001c009000000f0048005000000b000c0040014003007c016000400400dc00700040060008000000400100340010078005005000a0008005000000b001400e00ac0000000000001000000040010004004000000000e8003001000e003c000002000800000080004000000400a00c00010000009000000400200020000002000c000000000f002000500000000000001000c006000000200440060008008004400200000020080001000c00000000020004008000000d0004000000400000240000018007000400100a00030020006003000300a401300000020004000002401b000400000280000064000000800100180000008001001c0000010000000001d00000170004008004000000000000004006000000200000020000016000001d006c000000000000080000000004004c0000018005000c005001c01200000000010000000400000040000010000002400500100030008006002000e0000009000c008000c000001c0000008001000400500040020008002000000500000060000003000c021003c00700000000024000009000000180030014003000400c0000024004c00e002c004002c001008000100240010008018000c002001c0030000002000c007001c0090028000002c000001800000140010010000001c0090000004000001a006c00300340000000014000000e0000001000c000000000b00080030004002000000100000040018002000c005004c000001400100040000014001000000500280000000001000000400000030000000001000a0004002000400000040060000000000400b00100130050006002c002002801c00040020014006001c001008000200200010004000000800000980020000005000c0030008031005c00000040010000000001400900040010014000005000000380090040001000000400100000004001000002400040000000006000000f0014009000400c0000037000000f00040030008008000000000140020020001000800000000020004004001c004000400000040020004004001800800400040010004005c01b001401a000400b000003c00200130020006001400600140020004000001c000004000300040020004013000000100040060
  | 33 => 0xaf4a5270000d40679233d76880007225f508841c9db17a8ea0e4ae28bfa87ca0862aa2347c00005c27a46e5cbfa11adf98acea562908ad2455a932b3f9034475f4cb6078231ab05a5a0317a0a4bc4931c94a67960001b5000024085b700007bada087bd194c21a9b0202d992058f12620d40e33c1885928be015683c85e06f11ef86a65ec6a102294a7d97f44e8043eb79236d7781a902c0113863780b0bea1cba01f4b2c8b50e620a924500f4c3f48ca893225a83c5a6b931200000000002a783c28000000250e0000be400000004610ad39694000000180e00007f8000000000000910000000000000000002c21c8c000000000000003e85a5800093880fa7e053f8000276800000007fa25610000fb6937ab02a928000881000095cc0005bf2f6c0001c108b580008e783bc9fd00008662148b3384d81820a088419e4e0e9f04c2f223342e301a47f994f6143c4264d124be000227f1cf44c3bb01c767950f568aaaf387a517fe04b8f4700023ea1e10140797995884f6faa65d699c3940fd62f3930496aaea232894e468315e180bd4fe7cda4701ada3c36f89b282cd07470000000c2b000073d852e4ca8d542daa8fe3f5077068ab0fe4d31180c1021491390a9e2f947e4a761b3852980090018019009400000200000008029000000b00140020000022000c008000002c00040030000005001000f0004006001000e0000001000000000240060000005000400a001c0000008007003400000000020040001000c013002800a003000e005400600440020004002001800900000110004008000000000080020000014004000700000000004000000000c00140100010001000400600000000000003001000000040040028001000000600000050004005000000000040000000005000002600000000010021000c010009c00600000040028000001c0030000000000402a000c018000400000500000018003000001200080020008016001c000000000a0000000000000a000c0150000000001c0000000000005800000040050008000004c0000098007000800a00000040000000002c00000280010004001000000b000000000240000008006000401c0034010001c000000000400000020020000000400000100020008005005c0050010012000000900440030058003000400b000001d00040000000022002400700240020008002001c003002c00e0000001000002800100070008000001c0010010001002000b002000d00340000054001000c000003800000000010028001000c00c00d0004001400100000000000002000400000380000004001000802300f002500040000008004000402b0004001000c00200000050020000000400200280010058000000000a0038001003c005001800100300030000000003800800000080008
  | 34 => 0x299e39acdc260dafb24cd8655c1b096c6fea24095f26c86678da20000000a861b44000198a5fb26d50619808a7dc000ae019b69c597e60000c4e01d8f9eb63af7e7961df8b089fef1b69ccf000202400030eab3d27ccbfd133ca202cd2933a70c27fcf5e0f72fca9169738c36970e4880000133154300030607da264a00000002be4d3e3f5d89e0002bde43980000000a25ba7c00000000005b8952a2008602521256037704c2599230400013225fdc6b100000004dd000094d0b506069bc86d2169200007bd8801b9c35d91551c302f83475fd20000000512a1beb458000000020834a11001ce18ec3af000000014f393b00486f490c8b6680da0001f90b96a77b37fc65c8ad24aeb53189a0000f74b7d00000900f0c72f03ec9aa6d863f22b9714164385f4d8d4465c0005a62b15993a2e42f5415e5e1ac381d2900e000000031d20aa5efc73c08c8cb08baaaccb6b163a2178dfab43082c31869a8725c516a988528a1e2c583b3b08a6122b9444e8f80578aac82688ff65db0bc4700857854f8e7d10321b054e9e0a59228a669d2ad77dd99a528f093a8b30ea623a239a8d4a7ca1604214bfc03bb4620bc2c419f1b30c80000a28000bb795443cf9aa91c7915b70f800022b463f215ab8c0c98a3dab0565473c23ca000000093e80000002a9f00025500000cb44fea5f60001810b78800000026c337ca330021800049b275826cc000000032e2a985ea7190000bf7a4f25fb645603000000002e1a00000006a7df260000000a520b3e2468b465901c1e000000036d61ca000276a000000091b0700baf20be0c6c0000000000178c0004c51870194ad8500023bc0148000981a0dc00000007c224143b215b2ba980006e99b20000000058000000001a72b13cffa62aa2de000134e2db147b060064000000005f68c70a8420b200019f2c178000baba10485a90160b620446d8860a2e72adb8e406a937453526588020b09149aa93217636d83fc68f807eb8f9c8e94410444c1921e70293ae78f12ce90f2d2f37568e261da02c006ab1b49d0a352e2146c8c9145e94515cd3e702102588514015aa22baa2aec86d0fd586a8edebc70000000000000000004e888b877999b00000000360ad1c21200000002e3a4c819d620d6128a51216e4cd000029829c37e7989d713c0009a08d559b8a36a50900006a818a18a5c00091f00cc74b000006e0934621271a904000000027a868780007a00000109528600000005d7ad5c000215248192c6065c306ae0a5acaa9031e5ea0000a7f9f8a2cb85940002dca1ea20a0c0f0000a7d036a0000941000232b0000a6354bc000a9fa652bf200006e89e8849d8000000214aa6b1a1b777dca00fda58e59c175c610248a3da8f5238badb092d800006746227a885b807e26da21b98048bcc0004af800016f29640000000
  | 35 => 0xd000235000baa814af264c2bc4a0e2471eda32170fbad32cd800025661da0a585041baa6a0e530aae229666117ac0002982aad9c5b40e8000bb719d08361c84977186c0103104b678000345c44c230a0f406a91aa4b28000000184623d082f0000000a5795d27b66acd7c6181c824156254a1e2699b0a905746dfa9e26f0027c19185a20809428932e44508a703d8000b5e8000b2b0ef296e00005e2400001b4f260029d8d0374b7e1738a0a66e0ec29c51d4e20e0d6cc1b800000013e40002dae3a1cda64138d7800007de00027c462c9eacb6600000000000ab4ad34b03090500008ba16c903c965e8f422580006668ad84462f29a96db7468110fd89287780002f0955e9eb964124f82ea830cae64000c3823b08d7d69452c81c07221d6a40f455b0002298aa515adc452618109e61679887a4000098a04802061521c2cba2000020a1abe7de17587c04bae000288476483ea000000057f970f0000000a32637000000003cd88660d200002efddf29b80000a6e8000ab708d700016360001f600000000a2302b432b8bed2c48000a800b5213963f08202372a5f46aac44a74d0002b2430815361c39290a382670893a216443800000000006cc00006b323de0a3055e000101e000115ea1f0000af95f8e766a9b18101beba13df80118000000006048ef697a40652a06dc000000000000e645340001f540001ffe00000003e200007d9800066829920c7002826d9db65f28b4c22aabe2ad6f07e1b468c85ea825541a09009618a685c68ac29d889d485c2d5aa66a316111c6f4bd0800010584ae9482ace000000000000004581b2a86dae5588aaf0c67080001249edf08e0f6e00021ec596a13692a86723d9918c3e90e04a5c183c00021606d380003aa0efa2a10000b9363749896027663d52070680009a80000000000000000009b4800000012e300016c26370e0c0001fe565c46c437bd5080001b22c3cac6a00027da91e0c816dfe27503804ac0001212000171d0000000000156c547c9c000000fc3514b036180000000119e163608245d035d7112640000125a8e5a3680002d6f107e47425e9fb2a8a06bba810ee2ade0d127002cba3000b06b50214c0d95a3866b0c6e4688e7c0b10a17b3c9be40000000b3592ba03280000002afd16140008fa4c40a82a61a2e10000950800001508ee000000090c00000000d18000000000000000648000c34800041303251b2800000029a48aac000000000000000b2440c0009f581bc26a09b86751c8c0659f3a1b5268a85f1b01ac39ef0b8d05519548000754885cb97ebf86a6000064425e43ff237aaa14c29b8593dc7888c130000094757127e362234eb9a99c47d1147c848cc7c0c090a0732992a18d082a6e21a650000909abc4bd70a224a8c3502e355484387c8a812610a43e6b60b2879728e477b
  | 36 => 0x51902126443c6ff84b8a98162279b25f123803e5000000038d8bfb9ac00000001665634ae26000071a6c9967e00000005a0800000023c89ae40007580c473d9168a2b880000000eae0138954aea2a3a000166b2f45b98a4a000000000002d6a6fa000000092480000000000943272a47d0f68593aa730000a073eb894a9d427ac4ad4c781569aec8b0067a0000dae5ce9c902c4273ca145c7885905d60e59e3067e0f40aa1c000925b05a9bc80e34e4c00026109640001898402e94630d80007ef4e2a9a30f48a1328d000000000002ef42e617d60a740000001ce022b151622509274b9000000000000001bb776380008ba00000000000802000000003ae5e548be0ac8f2e8eb8616a8b28364100eb83723082a858000570a8350000000000000000000000000724034000000009eb042c0000000000bc880000002be6adb2f5ea1291e0000000000000007b74000000087c5ab8000ab889727ef8000a5d204c56ec00084f800000000000000000aa3445300029c2bc28e202b68952447a98a0e100005b11d88b1d4b3c7138cfe56002d24c30000000145cb1f8000955c7fe00000000000c452a080000001b7a65e0000374254eb5a85d848d800058800000000000c292c26213039eb6e00003f9a06a00016bc0000e880db00000001158499a823a77ad8d000000000494508a0aa6a9511f30502003a0001460219000065829862f81bda6d29de800000000002dce0762df20b38000000278a00023bab131f3400000000000cb8b4992782b010fc1630452419000c00aa0194ab84fa9010d4c107b08067f1a0a0000000c0de6ba00017f6ad5c0008960584910a09e00013b62c2aa702288b9f26fa3e626d18a4631864197e9b9259a0e4a11780002f0182e08e800035f80e2baa800036c258b44400c76ffdebb9ac9b606ef13ea00003fdaee48a107400000001e8c54bafe243a8648b3aae8900014727d4800081680003a103b66f000000000000000000000000000000000000000019ac000bd212b900000000f5455642f1714b0eaf5100009903d3186212c97b79aa20a600014d60000fac1598000a645cdc7a700008d1a10229497c80001b3a0fc947839d04f727e0346267ea3686727642a69aba29c872cb7400000000e08324076c0001aed04c000074c800074eab5c40a00003631bba57d00008f043be306e246187983d1c6046c54d00006649ab3bc389300000a6c56a307a0ea5f96165400009511332220f8e8fb00000000000000000000020478de1b7c000010d14463e20002e388a9831759352a20bb1510a24212c01f0c9e0bf04770000000948d50a7e4877a00024d04180000a2d1a1c475ad645bd0000a83f11068c0c193490098241c0000002f841d72802000000000029b500017b851aae60000129f4638000303800000000001ae129
  | 37 => 0x179b6601f9aa36800030580000002e2064e8a406daa4d700000001dd800026703080cf856e0000e607912d086ed1a363b8020a5b48000000000000000000001a877399a2f0000000ba400000c9240a3ff970276741a2ab1462a000069284898c400016e04c0c0003909142bdc0ab32d80d867e967be8fc8a36002d248000169e00000004030000000094728d1f283d9c0009bd20e1797e988b5104eabce9ea8134ddb88b9a4c8aa1074cacf8efc3df920ac0d400043d9cad4978830a0a4580000253c07307d44898000007158a0000fa044f000057a0000000053b3f60000000000069a0034712c7cc0e607ac000073e000147a00000007510000000229b99196864c9000001e0421129179684686b31532c046ba000000000d80002d060110000056a9016dd87297422c64741800086085e2b7200000000000790c000730926a00004ca6dfa03c5c2543c5aa80000000eb17052de6991e13a0000eda1ef1c34be000002759490b169cac5c48c660f1c44e000089f000122a00089160001512575cdcf9a9a25032f22690000000a16800061f80007295e7c53c80007db8ba0a4f88508760000a7b2e54c1180000002bea59eadb234b4129b841fce2f89514ba0011879a053875d1284a349394802c0004024d44a7c80008a84e000001dab0002a3fafb8afe3c414380002608acc289a0000ab653e80006e56c5f0c628300000000999800053a0000000000068265a31d59fdeabc0d006706162624534335680000000dbeab59680624826e39380000000000b8a8000000234c55d82f62e2800097c11f800019b71a092e60001dc27290bc60ea92720bf9d2224949141e4a88b635af36000000058415f800007dc0000000a4182df98aaaa85a98000a3a0a37bbe0000a905852000000000027947ae23f61bd8bf476ea1563a0cdb74c5931d072195280680001abb0ec077aa965956b7475f0eec22dd8666800000b242ce05649cfe0000c3901680000002fc309b06dc0288000000000013121a0000000041099aa8820ad6806c4f072ad65d27128465739f874f941ea07c17b474a91204ac22fe000059c74f800000002dd0002dea0001c728bf10f40000000000174a0dd00007850c4a00000008e066ce99bad680ae837ec27c000337145b0001e410f4a6fe95f80000000000000170c0002e0ab2a1ed70001ce40000000907000069e1308a47ab560000a430000000000036e8ef9908b2d00000000000703ac8d364915200020fcb2c033811f28b753b07fd0001cd6aa76e5022965886e6879864ba74aa2ba27716bd178bad07a2adc12a8b222c2e0001aa49201b14727dcb000008f3513000076a0f0460e840ead2dab94980cee56b1dd4580c000ba49208000000000000009c70f386a4d8a2a2b000090d820400000000000000371d84e78120ee41
  | 38 => 0xd99c3213b8a6637516a468ba2eb0001dd7318075a9bf30fc751800067b94e2000151a88d0df5b4d86c00000000000205c72e2e6400012580000000000000003219da0002dab0001f7c19089f496311900001f72aba40000000c580002b0027993463ce8fc003a00005cb10e784d445a4d904286e81dc6acf4316b64e0ce3ee995e577144ec1d07b8addc6e3000142c3fac00030600000000000aa0063a81ba5c68381f0298e95660dea03596add0c1508a8f98f1c2a716969042a90dc6970d38242c3127af494500019486731eae5a5cf4aaafc76e296aa1e148813623bd68fba2820c7f11fcc273191e45c17749594abaae81c962ce24f4b2299ea34d93727b3830455e0d1c02ba922452802592c0f08b609658628d01c32500000002d2c5be11a0400000013e6984c1123e59ba2df676f69d241409acbf3ec80a4f2a5c9291ca76e420b8bf11e6004e8f862579db2be2000009fa32d65a9d1a8980a420000000000000006a0000b070ba456cc000987800000000009d58194a968000000296a00000007c42b26ab9c00059c800000015b87ae800000012280002bb08d792e2c362c274cbcfa260de772906a5530db4c8c29d6a503f68000239cd7423221a204a028b6b089430d62b488cfd05a8cf9d942b289589ab5326675df42b96031a2109c74710165211e6e5c68fe0562639246729a2a094e40a678da5e8280285c6950e8a3d50b3017223bf6dc96d0ad42f8a064251a21cabaa738e89815129b48b4687637f16a17766e7a2ad18c017ea6c28239b6cbeea47e2360906b331cd408daf1e232c000856ecc48bb812c91aa4582bd000000008fe3358000149c00000018e84712548143a6d90000000285625e57680006f3800000019ba9dbdb42780af0200003321770649000000000000000000da4c1f05680f3800000000002ea0d0f997abb3bb30c30898f0b84a682c6b39e5cac162707a1f9ffbb8b136000000000000000000229d84d00007ba1f620000000bc68bc13d80000000000088880000001ab6af70000000301e2f5202225e190ec2709fe8cf030e24e20202808000842400000000008d001580001ad000006540000000000000000585f40002084945a48c42a1022c2c99913a18198afc927c09295069c11fe40f0996400009fc30104980000000a8f4ade0002c00666d6ca0f91ca143185f344b8517a7bc53f34f151e00002970000c0cbafa23cad0103e740032c000000082babbc3f667227a06dbab62d3183d089a05688e825c7b016b1000e58460c1e0000e2487a192889e8e5a0001dcd5859bed0a5084e030400039500bd000044200000003de800000000000001f0a49a03acabf214412457fa3ef301a00001b063f00009fe800070640007e1130a1e3a2d000006d68060226000092aac818a800006ee7861882000242000002
  | 39 => 0x22162bc1ed0000af8006a000046e000150238792420f8851e8718000ba7b0500000e0600000007694000000000065ced6000000000001003a7ba196abd1c049a100005918000000207c70c2e4400006b45a3655e047833415e5894375c024c1cac6ebb100000002a98501232e00000000000000bb90eac33611080000ca0a99c0000000dce0000cf657600000000e96a1cb02c0a6800004e09b1818e0e2a89800004399dfbd410923e580008a1299000028a800c0691668e02d0000edcbd022cf000046d55c8d220000000bcf84625eb80003ec21d40000000000000016900009a4296e00000008b84e760000ed073bed7692700007a91cce96f811c3021d8c40900429d0ec7a012a558711d7e2b1707c20a0921a01a057aa9f461c869198e8d52578464a062c04800058a1f8d44aa9e4a97ae9a3b280000002f643e3294232c800039dc0001a611ae8e2000087e28f29d70000000010c0000000605a47ac3880000000000b0600009b740000000d340000000000248e0000bf67198000000281e0002e621edaa863af85a157c9062243839c684048200008deb7600007ea9d03274977b14293534f0ae4922d9de22a2a7348a38c38372c43a28cd0259980cf01a3c00069d8e1222c0488bf80ec6a251a9e1ae66ca000000000025313f085620000000000000000000003208000000035a48d1a9400020306230dac77e80000000000338000041490709ddaf2a0b802a04069bcc53c0e5200023fc9b60d0a09426581d993fc2830000ba08000bed9522b5cc000000000055b93f400000005a8800000000009c36ea4b4c50efbac8ea366ced6277c1dc0756086851c107ebe81ac61990c2891204e6870af208479b100000000a5f00000000000b65b00200013560001dc474f114c409800009aa798131577f42583ca48b988872545089de80005e7895c8e38598000039b3a5ce329fca67e0002ee85ad00ce185448e33ea5029a18db27b1dafa00016020002439812013300028ec8af800080cde16000087a17ba4d479451ac91723b600007264cb00007b28000000000000004b00001a42000180a00000002c38448000000080a5aa6af198445f4a57400000000000000bdcaeec1fdc00043cc0000000000c2e80002a80000bfba12e28740009180000a0b814e669c4140000f18000092e000000000000000000000a8d00000000000ada0000bfc8000b14c0002ce966c1156b925dda31900024f02f296011aac3155520000c21997a97100008eac1da1c1977e86f25c8bc1264200000000000f58103c0000000ad200000000002a8c02f00008a14000000035e0000000a6f879a6cc8ac8af30000b7703f89f49ec21979c3c94b000000000003e50000a0f1a240001c6b5e2aadabd992b220f04d225580007049eed848104a0002116163c000b5228a20
  | 40 => 0x248e7c222ee926544d3580000a05560aee69bae21e00018336d601fcb25973e9e0269609098cfa7580e70ec864344904ab0a723323cc1858000057d95140002448570000063b37884294f5e312aa81ab0bc91a4c8b293660b5a2d26e065280540d073c0a9349f18a48357a9aa0192d7121616a8b21819f3349cea9af855935212c498fa3c05ca078a527834e0a3a0781719e288ed1acd00018c20001482572a0862b843d071f8169c2521acc151ae47ac164a6b889ab0f78ac41bc8ed22a8a77e0551cf4382494e2caa71258689e04df977082a17d9b1b0122765529112e8000aaf64ac7260e4c00014120001ed67fea7c83e42ed64bb8a4a668925c0000484b5995a45c1418e075acaa9048e9400003e000010f834812529b7150e0000000bc340002052a7502a0cf40002b2eb601c4c64b20c40002b6b00000006f0c00000000000000000a7e800073f000000000007ec4000000000096da80e8d61c426a215e47dd06063ec872145a53e05570ee612683ee712ac122eea908b56000096a1deea0993e80002b9a62a4a46697800000000002e6a3220002b231b3c3948e48000ae9d2706a58fe7000072b68082845d180005ed909a000000000000006ad03b01500e1435fc00024a1a140002fd8000169c4ea905901bc0004be8000a2c0000b18000043c0000000000000000000001f930000000000062c0000000b1124b427d8000a819fa665bc16e0001f9c1cc24e60000000000000000000007bf976400010d64e9a89ec2a06ce0002a9e2208000bda80001d249ed0002ac60e180000000000768c000152c0b5a63c000161dbad792800045200000000b9d066800000013ca40c2ed82bb4e80a22094800006c6b5f9c0d0001a5079a80009a60cfc47d9bf6955175a47280000002ac424980000000267bef8000b9f1742000000000000000000000b5b6b7cb730000340c0000000000b4e80004ba00000000095160a20e04e40000000cda0290a64bb400005f0adb400000000001843167e3adb5d2fd47c516fe40d0636613308893018b60002da58ab9294a9644fc04261c41200aac70b4000ace1e8774e4e3c000000053c400000000000000a448a4a89ca9d234a288e3b970d9a5a87f2a761638c5a86781ab6bf82720000e6c9e9834214002a35002b72000068010b0faa73b25ae000244e0cf4e7b56fd122b5adfed0002c848619c280088ef477b4000b6903fe00023e84bb29c400004c00000d4296613c85d48ff546f26c5423e364b75107a8572cbe00016420000f3ca07d704a5f982800022540000450a120d0e56a959a87308186636a20000000000000004ec82683e4ef76000000000000000002acaafe400085d0000000000027e800000005ba682c0006ae1d640000abe23daeee9362c3261a84182ba8d70a5cab529fc267ca9555a0a9e8
  | 41 => 0x603236e0000ac600000000ebc4005b3239c20e8fb4a655a12218a9b800000009f9800080b80005b38000b96c00000009500000513000000084280000982461b18800032b143a07d00000002f3c0c50d3a43699c6929800071b9bea301894c9b99c53681ab1c169916a0b7b1002d12b7e799ead100017d1bcb049350d25063a89d56034a26655415545c58000931ad1e3b6c000bc980009f3935720b460054840000002238000252578ea1f415ef05c8c3000067717fc000294000014f462f000000000000000000062aae89b183558cec0008ae000089c29cc85a23280000a5070eaec80002740270e7d05782e30bdea22820383b41b49766000265c9359a1845640004e68234b69aa61000000042b0000788067600022a8776a5707bc9bde0002f5419615b0a8e462893a300e0001fd099da91abdf0dc478d21fe33a1a4689a0e0e2ee000e8550d8402cc90d5aa67909ea81160672d5204aa02b95194a51cb858608aac7279c1440000053d490099db2715f6398682a89e072014bdd300e2a99663c0a2e8d995c93054710154a2ec31117014d686668449b248ee2b1406f53ba1a5c1c46f997440e69518000221abca151c7a3a9d942cb0a696f1d8461b98b1a2fda376e1a28b76f2bcaaa3e0f79d130a000021508bfda407b229a2a4b90fa0002c94153af8c3bf8fd1a7f0000226800016a00003a32a882c3230700000000000000000290e65b9fcdb9284d400014760000ff7845162e4d8eb0c9ed008c3118000000123e6bbc00000028549bbc000950c000000099a55180000001efa00000fe54b0000a1b000000000006ab1794b1e018757ade2c6d500004d1e5c5000024800000002040000753000032e927a000157469912d9265c00038688ae858ebd80001e9856f9db002027a200026721664072000000000026aa6b8053a47ca142b594000000271e09bcb261a5400035b42d0357200a6e0aa42bbfa147c40afac0002aa59c0800094e9bae84327fc0002e9d0bc800043602b0879000000000007dc5d5a82594b811d82fb4ea067c52aa3380d2874b2084dc00002e3679019167bd8000678800000000001d180000000a8e14b0bda8518944000000082d2cf065f800000028550002c5727b8000b8601422b99b0800000005618a38000000000012fc000089e1678b222a200490002f329f000000002e1c2b51432639a90452c07d600009ec5da1daa9bc659e057e3c90000000b37140d77d88db10ccfcc097087812f01e4345aa3e3c79bf01d812ea575ae9c0fb40507ad80000000ad599d07d25fc1ebfc2f19fe00014580001ee20001cd8000000000009a4085ea91ab985e474a24da26211cc601a2e200007b0726e004a589b780002f1021c0d1aa5e5a4a059afcd634270e24202a55ec9f9198088d09ed9a85bb0b09200006600000530
  | 42 => 0x285827a80004798a8c000149842015c4b0803549c2800016c4f820000000000222c5b683c1000000001b80004dd8000b8482b677700002f62444000000026f2b088af68203b3400083b27e2c26129e657272c4a7017e2924d564c7c410199454da7a97844f1836005a203269145d4a8b98fa8a20a782a90000662165e964afc589f908653e0902b9023d0511a8ba4a2b0be0f500db74799c855789600001fa400ae656000160a3799ed30000000108cd2a0000000c1a000084e154e19300000da26a748880000001aaa556800000006e000000006bd800000002ac28a91e80000eee0000e725201dcb81c225636281ec9000e3518e0dd2086abf42c202748f300007a599c362e0000b39000077a8000c08b09a0002ab44f480000001d36660ae8462ed202aed0e2656f40000001f3ea1080000001bb68910000a2d4be93f88a5c126c0c337340000002d88314a0920fbd5b6074a900335ddb40001fee946d24c6ef8644bd18000330074497993de2ab800000000000002b1a6a040000002fb84f999405f7b09d84c2bba90b9fec97baf961fc80006652ff898ba62c81d236c00011d40000690a9f23d60002e08773a8de23e000000000004e71dd11ae96ac0000000744800000000004018824000000060800ba8feaa6e0000000000150c42b8bbe1f800001d925da0001bdc000000000000005e80000000097461d0340b239bc280a8000bf1c00000000009e3968b00002aa96280007ead5f124b202544a5c620390520b6315608f82e9875796d834a55953f1307800017d80000472000192268750180000d6200000000001cc8a1c24524958000339800065a2ac300017322658000000000000000009a693c00000000aaa5b2c000058329e80008b64ed80dc00005a1eccaaf100000001cda0000000000225a5ac80007bba0eaa5b0db303dc1f6000018c54ca3005e996b85d140001a387860000000000043200014da0000000b916b4eb318000140a60c4539a6e31a8c2e2951cb6b152680205cbde000172400029c15c1c0009c400000000836b6851268991c4900025d86d930700000e7aa9dc00003b84dea360f287b461033658ff20f9e55a7450df89e70adf000000099a1c084a2170820ad2a914a59bebe56d282b31b462d28000000168cafc0c26bf98000897c0c40c7c00094480008108b24176cbf819b86b07ed8a26000000000000007250b8290306cc115091eb1459ae9789886432a8976ac92aca2c5f0c8b72983ab7d21c0f5ce022ed068a3e680000001dc87b996c80000af2c258000c358fd0ad930c82e9911288d80000001a29347800005f00007af85a200000009470000000124477d00009ba800083e2c590001bcf6e2850c000000037180001ab5a862000000ad883c40002e8600000004618e34a1a1082b01c000c158000000
  | 43 => 0x3800067a034c0000000000040409ea8db0000af670804d07428ce23d240f20000266ab64ec06889a9aa9c603e23b40002c100000000e9a009cfca00000000001d3482708e51bf19b50001dfcb95c4aa05e9604196800000000002ffd29895e888a61680005d5800063e0000c0980005860082000000000f640eb8300006c2c0006e5aca48498f628bda4e45e88a2c43a70384c099a84e1ac30578c5b5af2165681299d2a532ae3b2691162871ed0000166623a9e1a9191e7e2dba662224c7806242eeb9d8d02e2ac88d657e52a64d4000087206ac2518000abe8bec232618ab2e105b47c2eca68c800094b6a1a2770712752800000000000000a13b6d9c6a05d1c13235000094d866c8b6cf5a74bce1c7e80b9007725d2a5800000002cfc00002b90002dc600000000000000177a6f500000006430a01b5c06120000000000000059d9c180000d106332bf34bc27f878400000002b22125a432acc80005320000000000000013f0000000059a80000000000327138878182daae84e56982abc0a3390d098107c87349872b9fadec1b95aa881e800000020148aa520c58228824a09cf2bc4d3b06af102c11bc0007d6936a0001a95b351eb200029ceae7d5848be98ae16596c619f574eb5c80002ff51c056ba7ec2241bbd240642c0001a4400015943fa10883d1b09e8e8400008584d53248fcfb44959eb0282bc650800064d2ab20000164a44a6440002da9b4c1993000000000030e40002bf63fec00000e2b42b81800000616ec18400007ca8beab4023cea7980008dacccca1ea634b3a65b238c1ff66e52ff600021f65bc99c048b042b3602a248a35c5e4050f1a2a483e652db084352800000004a772008f1bff2ae03baa2738b60d08ac180000000000503a4cc00000003e10000b3dacde90d14c2000114091880003498000b8500009f7800028f83225d800006c10d0b98e176ab5b82fa969dd1084aa6b831b0e1002a8d21000255979d9a5682f000000000000000000767800005ac0000000000000231800029e008c24866cd075ba134ab80000daa8a700bf328c00000028640ee4000c0cd1c200000000448fc6000000046280007bfe14ea74d3d4017a3ee00011de3c5b02e13a21928f1a65000024b80000000595c7e3c3d1ff28c3848650b890a00007ae0002472000168e0002b138e88f279b5eb6e000276b0001406a8040000000a32185c00000002f000000007408f72a718fa89e0aab7a7a0000a9580000f6950b516800000004c68eb12968642aef0000000a9600009890d5720548e602e0f066ee0cc800000007bb000092400004542e4f0249cc45deafb400000000002df8a8a844a859968400025c20000000624ec349b05a0e0001be0ae98a4e0000c3a47205ac3aa9010559dd406381cb27fa58c80002e0e43390467f71f5e000000
  | 44 => 0x424c7a3941e782a842ea7d400007fa7b715b18fd000000000000000d6480496f69eb99063b91bc612d40b476981db0af95c831cc8ec6f9e8961a90bac8348406373000060898b427404570b0000067d84a270e00000000000460a1101dd0000b118000a30000000030ca00004740002efa0919eb38ffc0000001e8200030529a88000be38000bbc8000c4295cc4c010e0000237f7db2b98a1aaac2000197c6fcc000a0d2fd2151400000000002f4cde896d249a000000075c033a68570f8722aee22c60000652abc269c21dea919cdea030db8000069d03e1066025ad107b61130b40a5808e0843467b12646f51b0a932983e7ed067e5ad9f046e91ca3919ab7a9ceaca25f000008b6ad90505193e1c8a7e0b308ad0206ea48b3024945700a247faea8b0002cae9b1e65a0fa40000e9a29f7a1a5ea4e41238300895a4bd0cd4191566783da69c90a199928a5a97bd70ecc5030391bfe9cbeb88a2a478c9a6b1dc9f4c83ea4ba7d385f20002fe89e68199a4b0bb521d80009ab1a2b63d000089b0e445060b7671f2ee00b20f6c22ac81ac319ba8c399bd863381b28e9a814318d9740e068f87c827b018301a6abfd93812984fb354ad7c86e911a68e8de0ab790b656321b2577935c0510bdf17b20068b81b687d199305acd7005f3495f2598bbc054aaf63292fbc171050623000dca8edc6d4ce0c340002f18507a596c0c60da1af959833c92f29400f249839b402de8a765f1998616aaeb60001e3ebae9eb414925407d29b5388ea3f86fb169d208207e5270f324650000000000000028d400022f01cea01d1be00003b9c6e800000008a327f69ab9780511299496a4d11b6504f6000280a31099c70002cb200001ae00024e08496ed45360000917881e37d8000000219a1a5afd6632a3d34c6c00011ecb9658380df2ef6aa78ea57a15b51f824290f1cab40b40458800015d292a00000000000b20c2d8a149611b9b8c41c8656ea426a8dd95a80e293a7a6eea0774e42d58185586e027206e1000088f82e43ad00003a49a664acd15c098942059326cc44770667271de4220228035ba3fd1644b16567185090180be57f1ad40001c22bb492006f24000000230a1cfd9bc10818310000deeba589c206d18780001c87000120e397c00059d1f3895a8fea0df249e0de062e4e01e9a7eea524679d9905ed53f2060abe80000b3239fa5ba000000000026b700000007761a9b5fa00000000d5dbd287bf000000057b000000000006390dca00000009ef0fa6a570468a6cc00000015968c7074e1a5191a00020fe2bce6d00000ed40000a064bf863c8908000bf39185b6f1f5614421e211fab4a7e520e844c5500aec966e6a095a6c063020000235ab95a74672bc0001a8800078221ceac4278681b1e4600006cb0000000ae780001b416f000030f0000069aa2
  | 45 => 0xaeeb8641a70fa0001ca267d00000001ebc168000000d9ce20002b4d6b3eaee00000003642a5f00002120000000c0401785910c142eed3404c68f070000ea4a9105b65be85f811583d97318ee800020ef7f08a96200c51c9dc035b589a44a0e8a2edc1280004ef8f44b8bab3c86225d00001362186956930410be00002e687000007776dfe6eb209a0888b648829d6819d23af0fc0f0e0001f1ab68000000029f845dac9e2f1400061f079000000002c09542000170a8c788e27dfad180001cf80f18dda0001ec0ac9cd2c0000a800ec480487aad3c32695af958c000000279e3ee00000ca173f67c00000e01d7b4749c1cbc52f34145516600000008f7128c0001224000229e22d15418a693702f70d378748f7c7f81c2e53180000e41b188c085720002fa675b013c000146e62b084a0001b9ebe1800000000008e294c08f92754b975a7fa5dedd2711a3569d322c479eae045afa4fe06808da298a180a3da5fc8f6000000000000001a1600009400001d427f00000898696803590e2a0dc000bbf07d8370c09a00007962ac03ba00000007b545ae8098000000000046688d200004f20211afcb8787e26298dec39700005e3000066981ba7c548a33a612de466011035618649d9800078930f6000000066d077c4db0d4721816de74816076bd24680001354058942a0001946316c0003a540007d90000000000000000000000000b92091872489b295300147a80000363aa1c170130e29c2fda600ad460001ff43fe000072c400022f000000028faa9b183200000000c0000017a00002c680000001d1c0000000be08590a93a4540f0da8009d88a400007a000023fea56043000015d3617564349b800099e30b000017300002115000000000000000001e38b7f00000000000ad66e004d7ab5a110274586e217269f00ea35393da0d35c5d189855069b22329b7e9da0000000aa0c464bf31cfab4c9ca977417d4c09236255318f27eb2d146a451a88a2a98595741fe565ddd63c81ab5040a9d49e4e3861a998386b280007e18cc400014280e80000000000066761370000000b93064e476000000000008f35c54b4f848a36787542b90000a91c00000000006a7400000000005ee8bc30001e9e0000000a8308a010905beb2619660000000000203a74582a6a11303296c182492f0aee000000047a80002906052000053c8058000c37905ea70308e35e8656aab8df4803800000980004592a8e0000000837dfd44b854d07ec1c484a028c200008a97b6c0007b4ad0a00009920002a65c1a8c8a9b124dc00000000001c7098869786a1003c8c820d68351df1b29a806aee25f35249614000067b651008abf901f22d58000ab2da9c000000043b2fc2b139fd881a0f786fa0aec6d700000000dbcac78000879a6e40001c600002c2800000000a007f0396d4
  | 46 => 0x5605dc868ca6c98141d48c83388aa4b2618cd9abf96ba277a06927c98af1be98a05e2ec503c00c8694a838800008c63668478000082e0d8c41a5f844c85e61e1e174890f0000244ad191ee9cca2c8885027c0001341000083e000038cb6f80e630b400014de98c000291046d00003a789229e3205864f000047f934244b0ba239c0000000000000000000001914ae5951500014a4bc5c000b1cc3194d1633a52d224c760eb0a57bc000000021c87c0fbe25d8a4c8490e6631898341e09ce955f04358331e5243fe4ea4b51c26be53048857a4fc4ff80e1000189c15fc0003210000654115a7dea13f62e9def4b623b20002a49476a5f23406dde5a653bd9ad00002de0000b670840b68c2700000995201800010a85b3b1c00006c398bea319a2db01827515906ea089178e5cd8070104aae5b2d8bd67ac4066a492dc0985211c1b1ed67b1f2b7673a25ce00030080000000b9d074800020d045e80005088a6e9cc000082b0000000098243c907857c03d68818000415a9dc000119600022ac3f71a3452595510c8237e5df5f03415c0008c04b5e4511d780001b6e1d0abd646ea6a4b1dafcb9c007be95c8000404810aa1810fea482002a45985400000000ee0aa8434869f183800000000000000ddb4a39f218d826c0000155610080006adc000214a75e8742b6044a11d06cf00000001bf84b49e74ae90a0d1674b946948c5651fab580002fc92762a9cafb2cc8a2d90c0a1390f1317449ca6daf164da2158a35b0ae9b78f2aa0e950f5a81f16b612fdc32200294229020b63d74c85003c800030369aac64a35f1f70ad12d2e7930f8a4b2dff921100005f40000973202800000004f11e2e884811400014e647727dc95a00deb482ad87d0269e5fb87145c61b11be61da05751d980000000000298ec2a8fe12a18000000154a8e61788000066a0000e7800000000000000000000000008fc2310000280e53e0000000000000000000006b44000aa985890002a0e5719972000000000021a629fa0c00000e6a000000000000006bb800000000008ea196c75b800053100001b08c8066629bc0001f48027000021180e94bd9880a0124f638640ec7b8000026a6e667da908c6a30a56c3b8f22795af9c58e68a497f85cc386ebbe0dda53242359d59d4a01c17f8f347f8cda03be01087f2933e3390c7f8df07d05964a651c70000000299841f056a8bc80000002e7855c2e8e4790000593d7314b58422000000000020de12d0c1c00007f630dd3a40000000ae3a3c2000063d0000a1e00020b000022ce00020ca0002d38a26cd68975800000004e0000000000030d000000002d612a1c43800032a888f244152692c800031a00005890000429a6ed2274000a4d938a2dc06687ba97ea00015fa55606e42151ad2000106e0002736b60400000000000000000a
  | 47 => 0x6f7ca989be14ea2c52a5d894a74848e8000b0aa16c25a13ee0001488000000003c0000bba8f14c051bd09650554a548000b550000221ee32ae2239d8b0a1849dc4000070a7420000000ba1e9a00002df0000171c000121642c000000020545de16e456f03f19bcc00000007c400015b48568000088000019185f1b64800000019e90000de9000032737cc51284c800004d6b849db2aad4e38b363fb9d8251d19ca99aab3f36e685000011467800106000033c1c102280000c3c45ca6d3b55ad4a5848ff452e9a7a97d0d462df2e6ec3f562ac312aa38cb099800000009dbac3c889805ca600c487f88bf1119aa8200000001e213e2653800000000000000000a84afa26388e900000000733113494609940000929b3b000071700000001a2c00000000002088762a0a200008d982d80006ec000000000009eea82ca722be4209978f00014a256380000002e0252f087431e80000002d783f4962c1d600005cb80009d8097e000022e000139e00002cc50722b2a8e1e8497e1466817a7ea5a6ac1495dac66a900000a9984ec000090c6bc23360002c361cd000000000000000d026c7802c0350000a56800000020c8aa2abd07ee0000a060ca500400008140d0da088000783869c0000000000199c1020000b20ad6c0000000a9900001f1852384f2ce8080a620963e446bda003e176a5269bc2694b7a262239907c08318588000179007980006fba13908f9b369d261ee0000000b121be1000020e7c180000000ace2d99232abcacee1d7813e9e202ea4d21bf41abc63010740000000c431475b0c3abc000a3c00002dd00000001aea1cb5c8533ec00000026ee1d8ab752b5c7ce00000005bb8000095921025c12c2b3691fa52a1d7214617ad2d7006cb41182c0a78000bb1800094eda20000000066553d800004e320d00000002fa495900c6223400000000000001d8138e9bd66a29720435025e4b1e21c97028160001d7e0001cb413580000000000562117cb9a2e8c0a0d4cc9de2a14b9c8924649adda1a4c000000000007b87e80002f4e54e254a13398c598414aea9a0d604de000022496306c02ac063fb00c3bc05d0a7411b826a848c5b5a0945c0c832984999709480000238c7201880000000000000235c42414e09bd8b012f1c000111400012240008f68f4e000146436e80000001590c010337840000095b00003048d329bb000089c400000000000000ca600000007146874bd595ea390200c40a960c35a964547f2bfe0d2d2140e4e6283921d62577419eaeb07fc34bd43016d1f2c7672a72989aa3280d0ff9075014640fdccdb79c6187faad696179396a331dd210292e030bc96e21f8fec83c302f968800075d80000000904000204900016e600004a8a0c8000043c00020280000d5c0000caafec6a39e129d653848a0ea929e820103e48
  | 48 => 0xaf5800000007b7855300000000000000000237640c80007d600005f8035219c00002046f9e00007da0000000445c00000000000002774a4c012411a49e8000109caaf1e33ad50cbe81763d40000cc62a700005d50000000000030a8000549004c05805fc89d1d9681397260001af2aac2692000179c0000d1457b6aba89d8000000000075422b0000000035ca73e000000000000005ef8abf0000290af500000b88000492a7180000db4acd8c1a0ba268800000000002f080c7400000028a30002914a0a10b80000dc502219e062c2daa8b1f00a0000000bd10000905933a0001b2e18825a68bd00000000000594188e0002b340718ad100015680001ada0000bcb116507260c01eb000000000013b400013984eb0000c28a1da66c854f4cc89039782249c3300005db8b481c200002bde26e5d88000c1d99d86a2617a22a000089208980000060000116c000000070580000002b83000137c00022bab3f8c4c000251d17da59aa916bb600028ee0314aaa107300679225d41da84b6bf0089563a954000028ca60aadc46898a3a31500580000000194d936441908e27299f71d017400002bae8880e18c0031080002de5b6dd4ce2ff2ece3760de4b9d9ac01af00007f0c00024da0725c8a83e365056c1941486522a708a0904e2800009324f188ac3a16606d59750967da58bab0bef0000dde636a7240002b6a000184a0000000b389b5a00000001bc28dc0000000a90c0000000000a5dab9c15f00009778000c0c1f5c2169a7e078c0004940cd000008e468a1c2f046a9b053720642ff94262f400000001b8c0000000000025a00019a40002862b438000b068000aa850e46b99d4800000002eccb86000210b000123c921000000004440001e736f559ce46f80000002c1e000113681824c4000052d0001c8231d8b1c71a182600000000e917920002966698a15d437aa0213f505c0000beb00000003329d80207000035419560001002000066900000000616d4e749000023ea1dc26e9c6c000255c000052a0000000606137a2594a10abac00423705260dc8c980001ecc00013f60078000a53a7b867991a4b628c640931fe72d51adcbc1872f7bf00060e0859b6b78286b8f20baaca1b664f589ae1ca83561aa1d0e84cc000514aeb86eae01ebcba9f1c338bb211f513f049800081d9d86926294a87c8000000000056ad73475e8ae00a1471600014949488362162cbe1934a098a7c05e65008b428ad936b0f31a1a7a85fae9fa0330bd829a61e707450fec12ba558702b9193304260b68141163276411324d282ae0ab513e8f4909400000000000000a0ac000537800000021e007a2c420002da86b100000000639ae744f40c42f9223c80470002a3c00000001fd1dbf000285e05750b400000000002e6c000000000012c87c7013217863a4b7b9468
  | 49 => 0xdab3cf5c3b100323dc027850d8bf2783141618f9168715845c41aa8a05f30d0c5591b8e28a0eb09d68f2c1a11e4200000a08eaac2c644aabe0f02f746c6a22e5e4c647c430e1600015e9000286618c881695fc00000000003b58ab50a263802698f509f90aef0002402af3963e4672e42ac5aca0125021e0001976052a2c67b90a5e755161e6f2aa5404d05ca233000000009c1b97963463b9f993599004000104841da4a240da8380000000811888c29d0ca83c3e81c76b0ddd55f894201e80ac5ba8000199dbf20fae32600013ab0002b2c11a98688f46f5294ce4c2af694d212f86e6b67df0e29a81677f6b090000252e30b06de6c588f00000dd63f6e262839045840200000001a92000000063d94562b05eaa00000004b692b8a234000571c4fe698030a122db2d8d2225c8e827ee469823388c17db0cec0000002e705ec2b124f3b03a2849d2ea2f10070ae00000001c500000a18b0200000000000beb86789670009bf40c0a341193233b1102714a20224fadc237f8b6200b68215280dc9227243a5b000007cf07286b580003a3826d000229000000a59802ae4000109ec0f916b76b82f49c9803fa98e50bb2f15e65189f24964014cbde30283974576b4880007778a302f363c40002f9a0001aa27410000af166d6000220cc232b2500000008026384ab50000000000000029ca000000022c8359bf1888ebd89e6e3960ef614e5e66152a4ee36a11ce7ef185cc30af909b517a4b1540002e02314b57ad9d08c516eb0082ca4428000078a6641469e720002aaa2298000663000054f02dc00021fa1a200008975bf9799591c5352036aa688b9a3f00009c1800043089d90a9df007cba4409af234216c28e600025382be07e600000005c40000a14a636bc1e3211a8288a0e39c06b65ccf81bf965c0002e525c8e504aa40176a2a80002af09c60000b4e162896314d869eb50add61c28eb63170dea203d25401d0000000081200011e20001ff8000148e395cbe66d30e6706100000fe970660bc0000002932bec1e9219880003a730b4000053e0001e2a2600c22a248bd29e12bfc7599dca05a8000000221800000002022ef600010e800021086ec87ea544536e0002761000000000000008a1ab6900000000000000a42800000000f57b5000041b302a5870000000227c532ad5000009da00002925410000bff809e275ef11085597022127381b2418840140001e98b1ea0001720001c240000ed1928131039a1c0c00012b6a310fdeae4208c625800034b80000001b0632587946490000a9fdaf82bf0961330ae242ed86ecb4a80006b204a99a38c7e975c5f0abe2a304ad1f880a61812b92c699124015c011a90c1b215ee0308e938308148a2762a20000000bd3000058e2c52bbc0750bac00004160afa1ee9e1c18900004028e4660000007f5
  | 50 => 0x2856000098c000000064292aa7b1281a4e30ff07992c4a726b01c85faae1ad99da4502892006d9ea66f5cbe7730226a4b312048650d309d3a41e987088600000000000000000060f0000a914558000000000000019c574980007dcc0006d796516c700000000e41b1590cc3379fb71eaa10e8c1842e7ea040d96089ce8758be87a2965b52b04465f700082790b7226c1b3e2a521ae4550f9824467fe12819de68f306473429d71fb26323f38d4100000002e792f850699540000000000238c05b4ae86ab91b6b34181e00014549e4a8b89ca00002f30bee6e6400000029505120000000185600002e591b80000242cf836618d8889047a00013bcb7827b25ba10849df167c096242a4719fcbaca8b8e4b947320002aeaac10e280bb9f32a94800053ba648b7c40003dd9f126ee4eb27f2250a7e30a201519e9069213cc0002aab39b8ea00d708ce8d10a773c4a5a4bcc2b18a4e0e38000256e232ac610b5297b37c548cbc2eeb30001caa9952424099179a7e890ee29f000012dc436367000000000000000cce9422f6e81983642bc1aa727205c287fddcc8c21c7a5f380001ec800000017e400012c000000007f1b04e000248800021a8000000006f9c9e0000e0a91315c5a460a3f21b047077f9ec9ae2a67aa2199fa96cc23c7444000b3991757462c740cda6b614c9ffc4cfeab9b0f9900afd704256dd7488b9ce2cad7800040e12dc76f800048c08221b8859a9d3c3d861e8df0ae6eda2517400000013d085e02530000000c301ca8b6d577cc0d09e20a8800008b000054340005ac0000c3707ee839800000000003f8000000003a806b00000fcc0000001b529c24e3e00012929559ff044100009f60000bb694be1ac91b200025ec25f263000000001850296127ac101e32bfa3bec36b00015304a913b8281286e9b6cb925a8d7f8286aa57a40816c5f1000000019a900028be12b618c5cf251e5fc8cea53f291c50f8000b038000000000004ddb120001cee000000023441ca0e0ca163090d06b23000000024184e484da79400000002ab50002add00000000412272000000000000002f6c0003141a6a000280802357bc000132845f868600023dd1571aeb000000003d107400006cd4311637bd691b0000000079e0adc4e08000a0400008639c5800016621cd9f1e910477e093a20b72bad1a6ff0e5ea2cacfa00029548b5eac71b600000000bb014940000002e94164c0000738000b24ae4e03aceba000000013fc4f847b000030f910c000000048600009cba48274e00000000c8e288800066587e5ae881fa592d72aa64c00000000000401e5a4b4099e6b3911c59e208a5e095d0a8224762fc057e0cd507528ae9e20001bbb13700000002aac0002c68693880c493abfb4fb1c4
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x85b271994400429d38cca20021cc9c66510010c76ecb28800853a75d88400429cbaec4200218e5976210010b64e3b1080085b171d88400431cb2ac4200216cdc56210010b60e2b10800853a75188400429cba8c420021669cc6210010b32e631080085b27118840042d8b88c4200212e5d85210010b34e62908008599731484004394a90a4200216c9c63210010b62e3190800853b754c8400429c3aa64200216cdc53210010b60e2990800853a750c8400429cba86420021e24c83210010a72ebb0880086396598440042d8bb4c220021acd966110010d62cb30880085b272984400429dbaac2200216adc96110010b50e4b0880086b37658440042d9baac220021ccdd56110010f46e4b0880085b07258440043d0392c220021681c96110010a74ea30880086396518440042d5390c2200216a5c86110010b64e2308800853976944400431cbb4a2200214e5d72110010b34e7908800859973c8440042d9bb642200216c5db2110010b62eb908800873175c8440042d939e4220021e49cf2110010b24e7908800879173c8440042d839e4220021e898b2110010f42c590880085b271884400429dbaa42200212e9d82110010972ec10880087a12108440042d9bb04220021ac9d82110010b62ec10880086b17608440042d939842200216c1cc2110010b64e410880087a27208440043d1b104220021e81882110010f44a410880087a15208440043d11904220021e84c821100109a8e6b0c400856575086200431cb288110021ac9844088010d62c220440087a021102200423bb8eca90021a6d8c4048010d30c620240086b36110120043583088090021179cf65080108bae7b28400843e74194200421eba0ca10021179cc65080108bae6328400864d639482004326b1aa410021595d42108010d8ac6108400863965100200434d3188010021a658c4008010e52a420040086b26110020043d010880100218d59664c4010c6acab2620084d67398b100423aba8c5880216c5d840c4010d62ec20620087316510310043593108188021ac18840c40108eaed28c200863b74596100431c3a2cb080211e5d464840108f2ed28c20085d273c86100425c380c8880212e9da4044010c76cb202200863b651011004355b108088021aa1884044010c6ecbb222008637651911004333b2ec4880211d5d662440109ace731220084e6729891004333b28c488021a9d906244010d48c831220086c7631891004362318c4880219918a504401096ced202200863765901100435231480880212d9d84044010c6eca20220086a4621011004359b0080880218ed9764440108f2eb32220084ba74991100431db28c8880219ad976244010d50c9b12200866b651891004354320c488021b218c6244010dc0c5b0a200847a76945100431c324a288021ac1925144010
  | 1 => 0x104439229481082214d9d44084110e48a4204208846f725855404236392c2aa0210fdd95415010c5aa8b10a80864e639885404317322c42a0219398d6215010c9ac6b10a80866562984540421f3a4c3a90210f5d261d48108bce7b0aa40845d73d85520421f3a6c0a90210f5d3605481087ee8b02a40843c74581520422fb9ac0a9021171cd60548108deeca90a40862d645485204326b1aa429021879926314810c3ac9318a40861e6458c520430eb22c6290218b5926214810c9ac7310a40863564984520432cb1cc029021179cc65d08108bae632e840847575987420426a39ac3a1021179cc65908108bae632c840847975982420422fb9acaa1021171cd65508108bce632a840845d73195420423aba8c2a10218d55061508108f2ea302840866952181420422f398ca21021175cc65108108ece2328840843e74196320421eba0cb190211d5d6618c81087ee8b2a640843c74595320421f3a0ca990210f5d0654c810a98e6a926408475751853204332a90c2990212e9d3604c8108f2ea302640843e74194320421eba0ca190211e9c0650c810c9eca990640864d654c832042e438264190218edc164944108bce7314a20845d7398a5104296b90a9a08214d9c7545041087cec2a2820852d72151410421fbb2a8208210f9d3658841087ae9b2c420845e73d96210422eb9ecb108212e1d1608841087ce9b28420843d74d942104316b24a4108218b5915208410970e8b00420863565990210431ab2ac8108216c1c164084108eaea31842085c573988210423bbb2a410821595d442084109caed1904208565758c82104332b2c6410821995953208410d88c699042085e0704c8210423bbaac010821351cd6008410b60e8b00420843e7498a500421eba4c5280210fdd16194010878e8b0ca00846f725865004236392c328021559cf21940108f2ed28e80085d273c874004237396cb200211b5cb6590010c6aa930c800852e72d964004296b96cb200214b9ca6590010a5ae532c800853a70196400421f3b0a5200210f5d85290010a3ce6294800851d7314a400431bb2cc3200210f5da5190010b2ce790c80084b576086400429aba843200211b9c865100108dae432880084e4725844004297390ca200214b5c86510010a74e0328800843e76148400421ebb0a420021479cc5210010a3ae629080086346558440042d2392c2200210f5da5110010b2ce790880085b170c84400425abb042200214d5d42110010a72eb300800863965980400423dbb2a8200218e5974210010b64e3a1080085b171d08400431cb2a84200216cdc54210010b60e2a10800847b7558440042f0392c2200214e5d25110010a72eba08800863965904400429dbaa82200216adc94110010b50e4a0880086396510440042e939e4220021e8d082110010f408410880
  | 2 => 0xa590a218e15260c8510cd0a5306428863854583214431c2a6c090a219614f6048510c70a83024288658531812144335a90c090a210fddb540851087aedaa0428843f76150214421ebb0a810a21879935308510c3ac9a98428861e6414c214430eb20a610a218b9935208510c5ac9a90428862e641482144316b20a410a218d15261d0110cc8a530e8088664525874044297394a9202214b5ca5490110a5ee4aa4808852c72552404431732ea520221c3d4f529011087aed294808851e7394a404428eb9ca5202210fdd95290110a3ee6a94808851c7354a404429bb8aa5202218b9945290110e1ea6294808870c5314a4044237396caa02211b5cb65501108dee4b2a808846c72595404421f3b0a8a02219914b6150110c6ea830a8088664521854044297394a8202214b5ca5410110a72e12a0808843f765504044297b92a8202214b1c95410110a76e0aa0808853870994404431732ea420221c3d4f521011087aed290808851e73948404428eb9ca4202214b9ca5210110a72e1290808843f76548404428fb9aa420221471cd5210110a6ee2a90808853b7054840442973a8a4202218b9945210110e1ea6290808870c531484044317a94c0202218b14a6010110e56a5300808872852980404421f3acc9902210f1d564c811087eedaa6408843d76d53204421fbb0a9902210f5d854c8110c3cc9a9e408861d64d4f204430f320a7902218759053c8110c5cc9a96408862d64d4b2044317320a5902218b59052c8110ca8a730e408866452987204432a29ac3902219914961c811087ce9b2a408843d74d95204422f39eca90221175cf654811087ee8b2a408843c74595204422fb9aca90221171cd654811087cebb22408843e75191204421f3b6a8902210f1db544811087cec2a2408843c76151204422f3aec69022187d536348110c38a9b1a408845e7518d204430faa0c6902218715063481108bceda9a408845c76d4d204430fb26a6902218719353481108bcec29a408845c7614d204430fb20a690221871905348110c5ec9a92408862c64d492044327b1ea4902219318f5248110c5ec8292408862c641492044327b18a4902219318c5248110c6ea9b0a408863454d85204432ba9ec2902219514f6148110cc8a5b0a408863754185204431a2a0c29022195d4c6148110ca8a630a4088667521852044332290c29022187d526308110c38a9318408861f5458c204430e2a2c61022117ddb53081108baeda98408845f7614c204422ebb0a6102219398f5208110c9ac7a90408864e631482044326b18a4102218b99352c4110c5ac9a96208862e6414b1044316b20a588221cad4840c4110e50a4206208872854d4b10443942a0a588221d214c52c4110aace729420887275414a10443922a0a508221d1d4c5284110e88a6294208853675902
  | 3 => 0xd16094910878e8b04a48863a64582524421f3b6a8a92210f9d85454910c3ea9b1aa48861c54d8d524430faa0c6a9221871506354910c3ec9a9aa48861c64d4d524430fb26c6a9221871936354910c3ec831aa48861c6418d5244317b26c4a92218b1936254910c9ec7b12a48864c63d89524431bb26c2a92218d1936154910caec7b0aa48865463d85524421f3a6c0a92210f5d36054910c70c9b02a48865863d815244237bb2a4292214bdd15214910a58e8a90a48854f7354852442a639aa4292214b9d26214910a5ae9310a48854e7398852442a6b9cc4292210f9d0611491087ae8308a48845e73180524422eb98c0292218b99754149108daed2a0a48854e7395052442a6b9ca8292211bdd95414910a9ee6aa0a48854c735505244317328a829221939975314910e1ea9a98a48870c54d4c5244236bb4a6292214b9d25314910a5ae9298a48846f7654c5244297ba2a6292214b1d15314910e1ea8298a48870c5414c52442b2b88c8292219358c6314910ad2e0318a48854e73d8452442a6b9ec2292214b9d36014910a5ae9b00a48852f7458052442963a2c02922153dcd6014910a98e6b00a48852f7444052442963a2202922153dcd1014910a98e6880a48845e73d97424422eb9ecba12211d5c765d09108bee6b2e848845c73597424422f39ecb21221175cf65909108f2e1b2c848845f73596424422e39acb21221179cf65509108bae7b2a848845f73595424422e39acaa12211ddc565509108f6e0b2a848845e73d94424422eb9eca2122117dcd65109108b8e6b28848863454984424432a29cc2212219914a61109108e8eab088488654535844244332292c2212210f9d3658c91087ae9b2c648847571d96324421fba2cb192210f1d1658c91087ce9b2a648843d74d95324421fba2ca992210f1d1654c9108eee2b2a648847b7059532442a739ea4992210f9d3650c91087ae9b28648843f74594324421e3a2ca192211ddc5650c910a9ae6290648854e754c832442a63aa641922193995320c910c98ca990648870f544c832443862a264192218e152600c910cd0a5300648847875580324431c2a2c019221b24c9600c910c70a930682886385458341442373aec4a0a218bd536250510c58a9b12828846e751894144317aa0c4a0a218b15062505108dceda92828846c76d494144327b1ea4a0a219318f52505108dcec292828846c761494144327b18a4a0a219318c5250510c70a9b02828866b52d814144334296c0a0a218ed506050510c70a8302828866b521814144334290c0a0a214d1d54110510e48a4a08828845e7598f214430faa4c790a218715263c85108b8eab1e428861f5458f214430e2a2c790a2117ddb53c85108baeda9e428845f7614f214422ebb0a790a219398f52c8510c9ac7a96428864e6314b2144326b18
  | 4 => 0x3aa831a418846e7694920c42a6b9ca4906219318e5248310c98c6a92418863654d8520c431aaa6c2906218d9506148310c6aa830a41886665218520c4332a90c290621a6d8c4048310d30c6202418872a5210120c43583088090621879526308310c3aa9318418861e5458c20c430eaa2c6106211b5db5208310a9ce7a90418864d63d4820c4326b18a410621a698c4008310d32c6200418872b5210020c432731cc5aa4219398d62d5210c9ac6b16a90866a629835484334b14c1aa4210fdd95415210c58e4b24a50846f765485284326b1aa4294219358e6214a108bce7b2e850845d73d97428422f39ccba1421175ce65d0a10a5ce5aa6850852d7494b428426a39ac3a1421179cc6590a108bae632c850845e73995428422eb9ccaa14218dd506150a108bce6328850845d73194428421f3a6cb194210f5d3658ca10ccca4b0c650843e74d95328421eba6ca994210f9d2654ca1087ae932a650854c73549328421f3a6ca194210f5d3650ca10c9eca990650864d654c83284364992c0194213c1c5600ca1087ced2a2830863a54181418431caa0c0a0c210f5db5410610c9ac7296430864d6354b218432ab2cc790c219559563c8610da4c7306430854d7314a21842373b4a490c211b5db5208610a9ae62904308635655902184278b80c610c21715ce62086108eaeda9043084e576d4821842f1386a410c21715cc5208610bc4e029043085667510821842b33ac6410c21b118d32086109a8e6b00430843d7694a408428f398a520421475cc5290210b2ce790c81084b576086408431b2a2c220421391c96110210a5ce5328810852d72994408421ebb4a420421479cc5210210a3ae629081085a47258440842cb39e42204212d5d821102109a8e6b0c410864d639482084326b1aa410421b158c2108210c6acb326210863565593108426b39cc5884218e59664c4210c72cab26210852e72d875444296b96c3aa2218bd526295110c5ea8b14a88864e6398a544432731ac52a2219358d6295110cccc4b0ca88862f64d895444327b1ec4aa2218bd906255110c9ec6312a88864c631895444332316c2aa2219ad8b6055110cd0c5b02a88843f765505444297b92a82a2214b1c95415110a5ce5320a88852d72990544429ab88c42a2214bdc96115110a58e4b08a88854e7395352442a6b9ca9a922153dcd54d4910a98e6aa6a48870f54d4f52443862a6a7a922193d8e63d4910a9ee6b0ea48854c7358752442973a6c1a92214b5d360d4910a9ce7b06a48854d73d835244297ba2c1a92214b1d160d4910c3ea931ca48861c5498e524430faa2c729221871516394910c3cc9a9ca48861d64d4e5244317326a5292218b5935294910c9cc7a94a48864d63d4a524430f324c729221875926394910c3cc8b1ca48861d6458e524432b31ac3292210fd
  | 5 => 0x852e7218654c4296b90c32a6214b9cb6095310a5ae5b04a98851e7398954c428eb9cc4aa6214e5c26255310a76e0b12a98852f7258154c4296392c0aa6210fdd95415310c3ca931ea58861d5498f52c430f2a2c7a96218755163d4b10c3cc931ea58861d6498f52c430f322c7a96218759163d4b10c6cc930ea5886356498752c432b31cc3a96219558e61d4b10c3ca931ca58861d5498e52c430f2a2c729621875516394b10a9ce7a94a58864d63d4a52c4326392c729621539cf6254b1087aed2a0a58843f7655052c4237bb2a429621535ce6214b108bce632e858845d7319742c422f39ecb21621175cf6590b10c72a9304858845e7399542c422eb9ccaa16218e5506050b108bce7b28858845d73d9442c431b2a2c2216210f9d2658cb1087ae932c658843e7419632c421eba0cb19621535ca538cb10a9ce7a94658843e7499532c421eba4ca996210f9d0654cb1087ae832a658854e73d4932c42373b0a4996212e9d3604cb10c74a9b02658863a5418132c421f3a4ca196210f5d2650cb1087ce8328658843d7419432c42a6b9ca4196211bdd9520cb10a9eea990658854d754c832c432732a641962193195320cb10e1ca8990658870d544c832c42e438264196218e5526090710c5ca9b12838862d54d8941c43172a0c4a0e218b5506250710c74a830283886395418141c42d83828220e218e9526010710c3ca931e438861d5498f21c430f2a2c790e218755163c8710a9ae729443884b87458221c421ebacc810e210fdd56408710970e0b20438843d7695021c421fbb2a810e21535ce5208710970e8b0043886365458740c431cb2ca9a06210f5db5290310a3ce7a94818851d73d4a40c428f39ca520621475ce529031087aec294818843e7695140c431aaa6c2a06210f5db541031087aeda90818851e73d4840c428eb9ea420621479ce5210310a3ae7290818843d7614840c423cbb6a8206212e5db5410310b64e3aa081886396595040c42d9388a8206214e5d74210310a72ea21081885b27110840c42d5b9282206216a1c94110310d62c2208818853975d8840c429cba8c420621669cc6210310b32e631081885b27118840c42d8b88c4206212e5db5210310b34e7a90818859973d4840c42cd39ca420621665ce5210310e56a529081884b97614840c429dbaa64206214e1d53210310a74ea1908188539750c840c43c499064206218e5966110310b56e4b0881885a87258440c431cb28c2206216a9c86110310b52e430881886b16118440c42cd39e4220621665cf2110310974ec10881884b97608440c421ebacc9906210fdd564c831087aed2a6418843f7655320c42a6b9ca590621ac98440c8310a9ce7a94418843d75d9120c421eba8c8906210f9da5448310878ecaa2418861e54d8d20c430eaa6c690621879506348310c
  | 6 => 0x830f324a7980418759253cc020c3cc8a9e601061d6454f30082a6bae65980419359732cc020c72ca20660107195310330083c599081980419354e628c0208deeab14601064d5358a3008327b28651804187d92534c020c38c929a601061f6454d300830e322a6980419394f624c020c9aa7b12601064e531893008326a98c498041339db324c020a9aeb992601064f65cc9300832b29ec2980419554f614c020caca630a6010655531853008363990c2980419394d620c020c9aa6b10601064d650c8300831cb288018041aa588400c020f1064200601061e6494f200830eb24a7900418799153c8020c3ac8a9e401046f7654f200832731aa79004193dd953c8020c98eca9e401070e6454f2008386b22a7900419354e61c8020e1aa7206401070d531032008236bb4a510041c654c40880208f2ed294401045e7694d200822e3b4a69004187d925348020c38c929a401045e7654d200830fb22a690041871915348020caca7b0a401065553d85200832b298c2900419554c6148020c76cb202401063b65101200834c3188090041c654c4048020d60c2202401064f73d95200832639eca900418bd976448020c5eca322401064f65d8d2008236bacc690041339ce63480209cce331a401064f6518d2008347b20c690041a31906348020c9aea31a401046e76d4d200832631ea690041331da5348020a9aeb29a401064f6594d20082363b2a6900419318d5348020998eca9a401064f6554d2008327bb2a690041539d95348020a98eca9a401064c7654d20082263b2a690041c3d915348020e18c8a9a401066765d85200836231ec290041d154f6148020c9aa630a4010667651852008353b20c290041a91906148020d8ec630a40106c46318520083a2a98c29004199d4c6148020d8ca630a4010665531852008362a98c2900419154c6148020c9aa7b02401064c63941200836431e8090041d254f4048020dc0c3a0240104ae769012008317b2c8090041a318e4048020e1aa720240106a46190120082d538480900412b9d84048020c5eca202401068c631012008386a988090041a91844048020d90c6202401074953101200837030880900416a9d84048020d54ec20240106ab651012008395b288090041e2d8c4048020d54c620240106a86310120083c43188090041a218c4048020e56a6202401078a531012008394a988090041e254c4048020e12a620240107a36110120083543088090041e81844048020d40c2202401065b73d95200832c39eca900418ed976448020c76ca322401065b65d8d200832db28c690041a61906348020cb6cb29a401065b6554d200836431ec4900416a9d25248020e92a7292401067365d852008339b28c290041ac1906148020da0c630a40106e362185200828f398c52a621475cc6295310a6ce2314a98
  | 7 => 0x1904117dcd64944208b8e6b24a21045d7694c510830f324a6288418759253144208beeca98a21061e6454c510830eb22a6288411ddd95114420c6ac8a88a21045e73997410822eb9ccba08419354e62d0420c9aa6b16821045e73996410822eb9ccb2084117dcd65504208b8e6b2a821045e73195410822eb98caa0841175d763504208baea31a821045e7694d410822e3b4a6a0841179d953504208b8eca9a821064e53d894108326a9ec4a08418b9506250420c9ca6312821064d531894108332314a2a08419694f6050420cb2a7b02821063a54181410831caa0c0a08419694c6050420cb2a6302821067251181410822f39cca20841175ce6510420c9aa7316621064e5358b3108326a9ac5988419354e628c420c9aa6b14621054d75cca310821fba2ca988410f1d1654c420aa8e2a9a621064d53d893108326a98c4988419654f604c42087ce9b28621043d74d94310825c382c81884187992530c420c3ac929862105557194c310830f322a61884187591530c420a9aeb990621064d65cc8310822ebacc79084117dd563c84208baed29e421045f7654f2108236bb0a910841535cc5488420acae22a4421046d7518e2108237bb2a7108419398d5388420c9acaa9c421064f7654e21083263b2a710841d1dc55388420e88e2a9c421064d53582210830f324a610841875925308420c3cc8a98421061d6454c210831ab24a2108418d5915108420e8ca6908421065953980210832ca9ac010841535cc5408420acae22a0421046d7598c2108274b80c610841595c75308420a9aeb298421064e6354c210832631aa61084193dd95308420c98eca98421070e6454c2108386b22a6108419354e6108420e8aa730842107455394421083a329aa210841d254e6008420998e6b00421064d535802108355322c010841d254d60084208daec194a01064d5398a4008326a9ac520041479ce6590020a3ae732c801053671996400829ab8ccb20041479cc6590020a3ae632c801053a701964008386392a720041c354e6290020e1aa6b14801043d7694a4008296bae6520041c354f3290020a5aea194801070d530ca4008386a9c43200412b5d82190020e1aa610c801045e73994400822eb9cca20041179cc65100208bae6328801064d539884008326a9ac420041479ce6510020a3ae7328801051e73194400828eb98ca200414d9c46510020a6ae2328801053a70194400828ebaca620041c31c95310020e30e0a98801052e7214c400829d380a620041c354e6210020e1aa6b10801043d769484008296bae6420041c354f3210020a5aea190801070d530c840082d4b806420041c354e211002095aec108801070d5308440082d4b8042200418794e6010020c3aa7300801053975980400831cb2cc020041c694e6010020e32a730080105a9729804
  | 8 => 0xd62cc120c6cc9a8e609063564d47304831b320a3982418d59051cc120cccc428e60906656214730483a2990a398241539d6328c120e8c6428c60907185310230483c51908118241cc144408c12087ee8b2a609043c74595304821f3b6a8982410f1db544c12087cec2a2609043c761513048317aa6c4982418b153624c120c5ea8312609062c541893048327a98c4982419314c624c120c98ca992609047676d45304831bb26a2982418d193514c120ccec5a8a609066462d45304823b3b0a2982418dd90514c120c68c828a6090667621453048332310a298241d14c8514c120c70ca20260906a86210130483c49908098241cc144404c120c3cc9a9e409061d64d4f204830f320a7902418759053c8120c6cc9a8e409063564d47204831b320a3902418d59051c8120e30a6206409073051103204838c2a0a790241cc15051c8120ea0a628e40905667194e2048326b18a710241c3d505388120e18a829c409064d7614e20483a229ea310241c9d505188120e48a828c40907475314620483a2298a31024199d8c5188120ccac628c409052e75902204838629c8110241c91464088120a5cea204409070c53102204839228881102419358e62d5020cb2c7306a81045f73586540822e39ac32a0410fdd95415020c6aa8b08a81064d63988540832b31cc22a0419558e6115020c6cc8b08a81065663584540832ab1ac22a041999896115020cc8e4b08a8105567115253082aab88a929841479d06294c20a3ae8314a61054e72d86530828f3a0c329841475d06194c20caac230ca61043e74185530821eba0c2a9841179db5454c208bcec2a2a6105567115153082aab88a8a9841539ca6454c20a98e4b22a6105577159153082aa38ac8a9841561c16454c20a3ce9312a61051d7498953082ab38cc4a9841555c66254c20a9ce2312a61054e72d8553082a7394c2a984147dd16154c20a38e8b0aa61054c7258553082ac382c2a9841479d06154c20a3ae830aa610655611855308326314c0a9841931886054c208beeca98a61047671197430823ab88cba18411b5d662d0c20c9aa7316861064d5358b430823d380cb218411ddc56550c208e8e2b2a861064d53d894308236ba8c4a18419354c6250c20cb2a7b02861047975181430832ca98c0a18411d9c46510c208eae2328861053571153420832ca9cc1210419654d609082087cec2a2841053571151420821fbb2a821041939cd65cc820c9acb29e641064d539873208326a9ac1990410f9d3658c82087ae9b2c641065953582320821f3a6ca190410f5d3650c820a9ae4a98641064f654c83208326b2a64190419694d600c820a9aeb318641064d6598c32082a6baca6190411bdd9530c820c9cc6a98641054f7654c3208327bb2a6190419354e610c8208deeab00641064d53580320827238ac
  | 9 => 0xee8b2e629043c745973148317aa4c598a418b15262cc520c9ea7316629064c5398b3148317aa2c598a418b15162cc520c9ea6b16629064c5358b3148333316a398a419998851cc520ccac428e629043f74596314821e3a2cb18a4193995328c520e8a6428c629043e74d95314821eba6ca98a410fdd1650c520878e8b28629043e74194314821eba0ca18a410f9d6640c520878eab20629043f76d50314821ebb6a818a410fdd8540c52087aec2a0629061e64d4c314830eb26a618a4187990530c520c3ac8298629046e75988314832629cc418a419314d620c520c98ca990629063664d44314831ab26a218a418d990510c520c6ac82886290666621443148332b10a218a41d14c8510c520cb0a73006290670519803148364992c018a4187d5263c8520c38a931e429061f5458f214830e2a2c790a4117ddb53c85208baeda9e429045f7614f214832b318a390a419558c51c8520ce0a3304429063854d81214832c29ec090a418e1506048520cb0a6302429067351181214825c382c810a410fddb540852087aedaa0429043f76150214821ebb0a810a41879935308520c3ac9a98429061e6414c214830eb20a610a418d9935108520c6ac9a88429062c5498b404832629cc5a02419314d62d0120cccc428e809066562147404828f39ca920241475ce5490120a6ce32a4809053571952404828fb9aa920241471cd5490120a6ee2aa4809053471552404830f32ea7202410f5da5390120a6ce329c80905357194e404821fbb2a7202414ddc55390120a68e2a9c809061e6514e40482973ac65202418b9963290120e18a7194809062e654ca404838629a65202418d9975190120e2ea7a8c809071453d46404831b328a320241c5d4c5190120e28a628c8090726321464048392990a320241175cf65501208bee6b2a809043e76151404832629ec4a02418bd506250120c98a63128090667621454048332310a2a0241479ce5410120a3ae72a0809053671950404829ab8ca8202410fdd95410120a3ee6aa0809051c73550404829bb8aa8202414d1c55410120c3ccba98809043d7694c404829b38ca6202414d5c6531012087eeca9880905377154c404829a38aa6202414edc15310120a3cea298809061e6514c404838cb80a6202414b9d63210120c5ccb190809070c538c8404831732a6420241c314d3210120b50e0990809063665d44404838ba9ea220241c514f5110120e62e1a88809063665144404838ba98a220241c514c5110120e4c642888090725321444048399b80a22024187d4e6010120e36a73008090718539804048399a8cc020241cc146601012087ceb326609043c75593304821fbb6a9982410f5db54cc12087eec2a6609043d76153304830f326a7982418759353cc120c3cc829e609061d6414f304832629cc5982419314
  | 10 => 0x566758cb51483a229c65a8a41d114d32d4520aace7b26a29055573d9351482b2b96c9a8a415c5c364d4520a6ce931ea2905357498f51482b2b90c7a8a41d14c832d4520a6ce9b06a29053574d8351482ab39ec1a8a41555cf60d4520a6ee8b06a29053474583514830faa4c728a41871526394520c3ea8b1ca29061c5458e514830f326a728a41875935394520c3cc829ca29061d6414e514831b326a328a418d5935194520cacc7a8ca29065563d46514821f3b6a8a8a410f9d85454520c3ea9b1aa29061c54d8d514830faa0c6a8a418715063545208bceda9aa29061f64d4d514830e326a6a8a41179d85354520c3ec829aa29061c6414d514823bbb2a228a414ddd15114520a68e8a88a2905577354451482aa39aa228a4117dcd64145208b8e6b20a29063665d50514823abb4a828a41559ce5414520aaae72a0a2904777655051482abb9aa828a41551cd5414520c6cca2a0a29065665d4c514838baa6a628a41c51535314520e8ee5a98a2904757694c514829b3a4a628a414d5d253145208eeeca98a2905377454c514829a3a2a628a41959945314520e2ea8298a2907145414c51483a2b90a628a41599d63214520e4ea9190a290724548c851483a3a9c6428a41d114e3214520e4ea8990a290724544c851483a3a9a6428a41d114d3214520aaee6b20a2905547359051482b3b92c828a415cdc16414520acae4320a2905657298c514829b3a0c628a414d5d06314520acae4318a2905717018c51482b33948628a41595ca4314520ae4e1218a2905717090c51482b33908628a41595c84314520ae6e0a10a2905707050851482b33846428a415cdc13214520ae0e0990a290747734c851483a3b1a6428a41d118d3214520ec6e0990a290564704c851483b03826428a41d14c83214520a6ce9b00a29053574d80514829bba2c028a414d1d16014520aaee6b00a29055473580514829bba24028a414d1d12014520aaee6900a29055473480514822fb9acba0a41171cd65d05208bee6b2c829045c73596414822f39ecaa0a41175cf65505208bce732a829045d73995414822f3aec6a0a4187d536350520c38a9b1a829045e7518d414830faa0c6a0a418715063505208bceda9a829045c76d4d414822f3b0a6a0a41171d85350520c5ea9b12829062c54d894148327a9ec4a0a419314f6250520c5ea8312829062c541894148327a98c4a0a419314c6250520caec7a8a829065463d454148332316a2a0a4195d8c5150520ca8c628a8290667621454148332310a2a0a418e1536050520cb6a7b02829065853d81414833828ec0a0a418ed506050520c70a8302829065b53181414832c298c0a0a419cd446050520ce0a2302829045f73594414822e39aca20a418b1526210520c98a7310829064c535884148333310a220a4199588511052087
  | 11 => 0x4833830ec0aa2410fdd95415120a3ee6aa0a89051c73550544829bb8aa82a2414d1c55415120a3ce7320a89051d73990544829b38cc82a2414d5c664151208bee6b08a89045c735845448296b90c62a24147dcd6115120a38e6b08a89052f72584544829db82c22a2414b5c8611512087ce930ea69043d7498753482ab38ca9a9a41555c654d4d20aaee2aa6a69055471553534828f3a4c3a9a41475d261d4d20a9ee4b0ea69051e74d83534828eba6c1a9a41559c760d4d20aaae3b06a69051f74583534828e3a2c1a9a41879935394d20c3ac9a9ca69063754986534831a2a4c329a4195d4e6194d20c6ea8b0ca69063454586534832ba9ac329a418d9926194d20c6ac930ca69066562986534831b322c329a418d5916194d2087cedaa2a69043e76151534831baa6c2a9a418d1536154d20c6ea830aa690634541855348317b26c4a9a418b1936254d20c6ec9b0aa69063464d855348333b16c2a9a418dd906154d20c68c830aa69066762185534821f3a6c0a9a410f5d36054d20c70c9b02a69067061d81534822fbb2a629a4147dd15314d20a38e8a98a6905577154c53482aa38aa629a41479d26314d20a3ae9318a6905567198c53482aab8cc629a41879975414d208baed2a0a6905567195053482aab8ca829a4117dd95414d20aaee2aa0a69055471550534830f328a829a41c3d516214d20e18a8b10a69054d72d9053482acb86c829a41535c86414d20a9ae5b08a69051e74184534828eba0c229a41535c86114d20ab2e0308a69051e74d80534828eba6c029a4147dd16014d20a38e8b00a6905577158053482aa38ac029a4147dd12014d20a38e8900a69047671d97434823ab8ecba1a411ddc565d0d208e8e2b2e869047671d96434823ab8ecb21a411ddc56590d208e8e2b2c869062f5498a434832629cc521a419314d6290d20c76a9304869065853982434823c3aac121a419614d6090d208ece3b2a869047571d95434823bb8acaa1a411d1c56550d208f6e0b2a869047671d94434823ab8eca21a411ddc56510d208e8e2b28869062c54988434832629cc421a419314d6210d20c70a9306849065853d81424831daa0c0a12419614c6050920cb0a7306649064f73996324831732ea9192418b994548c920c9ccba9c64905667194e3248387aa0a719241c3150538c920c98a7304649063854d81324831c2a0c09924196d4c604c920a9cebb1a64905667194d32482373b0a699241c3d50534c920e18a829a649054e7614d32483273b0a699241539c4534c920e1ea8990649070c544c8324821f3a4c7a8a410f5d263d4520aace72a6a2905557395351482abb9aa9a8a41551cd54d4520e2ea9a9ea29071454d4f514829b3a4a7a8a414d5d253d4520a6ee8a9ea2905347454f514838baa0a7a8a41c515053d4520e8ae429ea290
  | 12 => 0xa0e418b9506250720c5aa8312839063a54d8141c831d2a0c0a0e418e55060507208bce7b28839045d73d9441c829ab8ca820e418b951621072087ce932e639043d7499731c83172a4c598e418b55262cc720c5ca8b16639062d5458b31c8333314a398e419998951cc72087ce932c639043d7499631c832732a6518e410f9d0654c72087ae832a639063a54d8131c831d2a0c098e410f9d3650c72087ae9b28639043e7499431c821eba4ca18e410f5d6640c72087eeab2063904b87059031c821fbb4a818e410f5da540c72087eecaa0639043d7655031c83a2994a218e418795263c8720c3aa931e439061e5458f21c830eaa2c790e419598e51c8720cacc6a8e439063a5498321c831d2a2c190e410f5d6640872087eeab20439043d7695021c821fbb2a810e418b95162d032087aec29c819070c534ca40c821f3b4a8a06418b553625032087aedaa0819043d7614c40c838629a64206416a1c1321032087aed2a6619043f7655330c83c499081986419a58a60d522087eecaa0a91045f73584548822e39ac22a4410f9d261d4e2087ae930ea71045f7654c538823b38ecba1c411d5c765d0e208ece332a871047571995438821f3b4a8a14410f5db5410a208daeda9865104cd76d4c32882e5386a619441535db530ca20c9aeda98651074a70d4c32882e5380a61944193d4e610ca20c9ea6b0065104e471580328829c382c928c418bdc96494620c58e4b24a31063b70592518831c382c928c411ddd951146208bce7b2e831045d73d97418822fb9acaa0c41171cd6550620a6ce3aa2831062c54189418831daa0c0a0c410f9d3658c62087ae9b2c631043e74d94318821eba6ca18c413a1c9600c620d9664b00631046d7598e218832731ea710c4153dcd5188620970e0b2043104cc7359421882a7b9aca10c418b5956408620b50e0b204310565719502188236bb0a810c413a5c06308620c98c7a9843105677154c2188272bb6a210c41789c35108620a9ee6a8843105e270144218826639ac010c41c3d4c329022087aed28c811051f73546408828e39aa3204412b5d82190220e1ea619081105a9700c8408821ebb4a22044147dcd5110220a38e6a8881104ad7608440883c41908118441331cd65c8220a9ee6b2e411062d659932088316b2ac9904419318f53c8220c9cc6a9e411063965993208831cb2ac9904414b5c863d5120a72e031ea89051e73d87544828eb9ec3aa2414b5cb61d5120a72e1b0ea89061f5498e544830faa2c72a2418dd526195120c6ea8b0ca89064e6358a544832b31cc32a2419558e6195120ccac530ca89065663586544832ab1ac32a24187d936355120c3ec831aa89064c63d89544831bb26c2aa24195d8f6155120ca8c7b0aa89063764185544832bb18c2aa2419518c6155120ccec430aa89065863d8154
  | 13 => 0x6508440c74e1328422062c72594211024f398ca10881275cc6508440974e0328422043e75d8c211021ebaec6108812edc16308440970e0b18422043e7518c211021eba8c6108812e9c06308440972e0318422049d739882110256bb6a4108818b5975208440b54e1a9042204ad761482110316b28a410881635cc5208440b4ae229042205aa701482110256bb464108818b5963208440b4ae3190422062d654c8211034631a64108816a1c13208440c5acb908422058d73c8421102d538642108818d596210844095eec908422062d6548421102d438242108812ddd92108440c6aca90842205b070484211024fb9ac010881271cd6008440a5ee4a8ca02052c72546501031b30aa328081c34c83294040a3ce790ca02051d73c86501021ebb04328081669cc6294040b32e6314a0206a96218a50102cd398a528081665cc5294040b64e2294a0205b17114a501025dbb265280812e1d93294040974ec194a0204b9760ca50103c499065280816a9cb6194040b52e5b0ca0206b26194650102d5b92a3280816a1c95194040d64c2a8ca0205aa7214650102d4b90a3280812e9db2194040972ed90ca02059a73c8650102ccb9e43280812edd92194040970ec90ca02066a6258354c822fb9ac32a641171cd6195320a5ce431ca9905367118e54c829ab88c72a641479cc6295320a3ae6314a9905367118a54c829ab88c52a64147dcd6195320a38e6b0ca99052c7258654c829db82c32a641479cc6195320a3ae630ca99052e7218654c831ab08c32a641479cf6095320a3ae7b04a99053671d8254c829ab8ec12a6414b9ca6355320a76e0b1aa99051e7398954c828eb9cc4aa64147dcd6155320a38e6b0aa99052c7258554c829db82c2aa6418d5846155320a3ee6b02a99051c7358154c829bb8ac0aa6414d1c5605532087eecaa0a9906365498753c831aaa4c3a9e418d95161d4f20c6aa8b0ea79055671d4e53c821f3a0c2a9e410f5d06154f2087aed2a0a79043f7655053c822fbb2a629e418e9916014f20c5aa8b1487906395418143c823b38eca21e411d5c76510f20c5ca8b1087906395498242c831d2a4c0216418bd96544cb20c5ecaaa265905c671d4d32c82e4b86a6996411b9d8534cb2099cec29a659070e5414d32c8386aa0a699641539d8534cb20c9cec29a659070e7414d32c8386ba0a699641539c4534cb20e92e029a659064c5318132c83872a26419641c3551320cb20c74a9300659063a5458032c8364992c0196418795263d4720c3aa931ea39061e5458f51c830eaa2c7a8e41559cf5194720c9cc6994a39043e7418d51c821eba0c6a8e410f5da541472087eecaa0a3904777654451c822fb9acaa0e41171cd6550720a68e2aa2839061e54d8d41c830eaa6c6a0e41879506350720c3aa831a839062e54d8941c8316aa6c4
  | 14 => 0xc3300a4206aa529805210354a94c0290812e9c66014840974e132c64204b671196321025ab88cb190812e9c0658c840976e0b0c64204b870586321025d384ca990812ddc5654c840968e2b2a64204b671195321025ab88ca990812e9c0654c840c58caa92642058c73549321025d386c2990812e5c3614c84087cea30a642043d75185321025cbaec0990818e5d7604c840974e3b0264204b9751813210355290c099081aa548604c840d346430264204ba71181321025d384ca190812d9c4650c84096ae232864204ba7019432102c6b9c64190812bdd9320c840b50e0990642058f764c83210347bb26419081a3d95320c840d1aca990642078b704c832102c63826419081e21c1320c840b10e0990642068d32984321025db82c2190812e1c1610c840f126530064204b975980321025d38cc019081a34c9600c84096ee2b0064204b47158032103c4992c0190816c1c5600c840976eab00642063b755803210355192c019081aa4c9600c840d1264b0064206b371580321025c38ac019081ac1c5600c840960e2b00642049e7398a511024eb9cc5288812e9c26294440970e0b14a2205b270d465110347b1ec4a8881a3d8c6254440d18c6312a2206a5711895110316316a4a88814d1c55254440b64e1a8aa2206ab621815110354310c0a8881a398e6214440d1cc6b10a22068d635885110316b16a228881a958a511444087eeca88a22062d62544511025bbb2a228881a95895114440a6eeca88a220637765445110393b92a228881c91c95114440e4cc4a88a220635625445110392b12a228881895895114440e60e0a88a220635519805110355314c028881aa58a6014440e62a3300a2206b2519805110358a8cc028881279cf65c844093ae7b2e42204ba70997211024f398cb90881275cc65c8440974e032e42204ba7018f211025cb80c790881a358e52c8440d1ac6a96422069a63983211034cb1cc1908812e5d660c8440d54a530642206a952983211034d31ac190881a658d60c8440976eab06422063b75583211025d384cb10881279cc658844093ae632c42204ba70196211025d386c7108812e5c36388440974e131c42204b97098e21102d5386a510881635cc5288440b4ae229442205aa7014a211034731a65108816a1c13288440c68caa8c42205a4725462110393a92a310881635cf2188440b54e190c42204ba70995211024fb9aca90881271cd654844095ee4b2a422049e73195211024eb98ca908812e9c06548440974e131a42204b97098d211021fbaac6908810f1d56348440976e0b1a42204b87058d21102573b4a4908818d1955148440e4aa4a8a42204b975d81211031cbaec0908812e5d46048440d54a430242206a9521812110359288c090881ac5446048440d664230242206aa21181211025d384ca108810f5da
  | 15 => 0x2e6594821902d2b8ca410c818b9955208640c5acb19043205a5718c82190316b2a6410c81a318d3208640b1ae790843204af76484219025bbb24210c8127dcd6008640938e6b00432045f73587525022e39ac3a92811bdd95214940a98e6a90a4a056471548525023bb8aca192811d1c5650c940a9ae629064a054e754c832502a63aa64192811ddd95114540ac8e4a88a2a066462d454150332310a2a0a819c1476050540c6ccaa0882a045e73197215022eb98cb90a819598f51c8540cacc628e42a045f73594215022e39aca10a810f9d66408540c5ac9a9042a063564d442150237bb2a4290819358d5214840ccaa4b08a42049f73587421024e39ac3a10812edc161d0840976e0b0c84204b970d85421025db82c2210812d9c4648c84096ae2324642047771595321023a38aca990811d9c4654c8408eae232a64204b970991321025bb8ac8990812d1c5644c840976e0b22642062c6454932102a639aa4990812e5d3604c840972e1b2064204b9701903210327b2a641908193595320c840b90e099064204bb745803210364992c0190813c1c5600c8408bce7314a22045d7398a5110327b1ec4a888193d8c6254440c98c6312a22062e741895110316ba0c4a88818b18b4254440a68e2a12a22066b621815110334310c0a88811ddd95114440ccac4a88a2204bb75583411031dbaac1a08814e5d76090440d1ec7b12822068f631894110346318c4a08818b5d46250440a68e2a9282206ab62d814110354316c0a08818ed946050440d56c430282206a862181411029abacc2208814ddd95110440c6eeca888220727725444110392392a2208818d5895110440e60e0a88822045e73d97211022eb9ecb90881279cf64c844093ae7b2642204b970d93211024f398c990881275cc64c8440972e0326422064d6394b2110326b1aa5908812edd160c844093ce6324422049d73192211031a322a310881591c95188440e4e84a8c422045f73595211022e39aca90881179cc65484408bae632a42204b970991211024fb9ac890881271cd644844095ee4b2242204bb70591211031a322a2908812e5d3604844087aebb20422062d65d082110256bb084108818b5944208440b4ae2210422052f72506501029639283280810f5da54900408f2ed2a480206b26190640102d5b9283200816a1c94190040d60c320a80204ba76105401024fb9ac3a9081271cd61d4840974e3306a4204b87058e52102d5386a5290812e1c16194840974e031aa4205aa70d49521025d386c2a9081a358e521484087eeca90a4204af765485210346b1aa429081a598e6114840d2ac7308a4206b070984521034b31ac229081a558d6114840c6ea4b08a4206a652584521031aa92c229081a95496114840d60e0b08a42069a63980521034cb1cc029081ac9866014840d62
  | 16 => 0x22f39ec2a9681175cf6154b408deeca90a5a04767199432d023ab8cca19681535ce520cb40a9eea99065a054d754c832d02e43826419681b24c9600cb409e0e2b0065a056672d4651d023bbb2a228e81179cf65c87408bae7b2e43a06566394721d032b31aa390e81179ce65087408bae732843a062e6454821d031b322a210e81179cf6154a408bae7b0aa52046f765485290326b1aa42948127dcd61d0a40938e6b0e852047671d96329023ab8ecb194812d9c4648ca4096ae2324652062d6494a329025bb8ac8994812d1c5644ca40a98e6a92652064f654c83290326b2a6419481179ce62946408bae7314a320477765445190339288c0a0c81a3d8f6250640d1ec6312832068c6318941903173a8c4a0c818b5d46250640c58c4a92832053676945419031b3b4a2a0c81c9d8a5150640e48c528a832073251d814190355b10c0a0c81aa1886050640e64a2302832045e73d97219022eb9ecb90c81279cf64c864093ae7b26432049e73193219024eb98c990c81179cf65886408bae7b2c432045e73996219022eb9ccb10c81279cc648864093ae6324432049f73591219024e39ac890c818b5925208640acae3290432062d6454821902d2b888410c816a9c35294a40b54e1a92a52049e73d85529024eb9ec2a9481a358e5214a4087eeca90a5204af765485290346b1aa429481a698e6014a40d32c7300a5206aa529805290354a94c0294812d9c7658ca4096ae3b2c65204ba70996329025d380cb194818b996528ca4096ce332a65204b571995329025d384ca994812e9c0654ca40b18e6a92652043e75185329021eba8c2994812e9c2650ca40974e032865204af764c832902c7bb26419481a3dd9320ca40d1eca990652068d654c832902c63826419481a34ca610ca40d1a64b0065204b771580329025a38ac019481a398e62d4640d1cc6b16a32068d6358b519029b38ea5a8c818b98952d4640d54c5306a3206a962983519031ca94c1a8c81279ce629464093ae7314a32053a70d4651902d9386a328c814d5db5194640c6aeda8ca32072672d465190392b96a328c814d9c35194640e64e1a8ca32053270d4651902d9386a2a8c810fdd9511464096eeca88a3206b2519805190358a8cc028c81279cf65c864093ae7b2e43204ba70997219024f398cb90c81275cc65c8640974e032e432049e73d96219024eb9ecb10c81279ce658864093ae732c43204ba70996219025d380cb10c81a398d3288640b1ae790c432049e73995219024eb9cca90c812e9c26548640974e032a432043f7558d219021e3aac690c812edc16348640970e0b1a43204ba709942190317394ca10c818e9c2650864093ce6328432049d73194219025d380ca10c810f9d7630864087aebb18432043e7518c219021eba8c610c812e9c06308640972e031843206
  | 17 => 0x18431e1c16550c21c5aa9b128610c6d751894308716aa0c4a18438d5536150c218eaea30a8610e3554185430863d380ca218431e5c06510c21c5ca8b108610c7575984430871b2a2c2218438b59654d08219cee2b1e8410ccf73587420862f39ecb21043175cf6590821c6aa8b0c8410c5e73d94420862eb9eca210438d9516110821c5acb3208410c6f765504208717322a8210431bdd561108219ceeab088410e677558442087532a2c221043a955161108219c8e0b088410e3554986320871aaa2c3190431b5d4648c8219cae23246410d697014e3208637baac31904339dd5618c821cceeab0c6410ea6545863208752aa2c319043391c1618c8218daeb3226410ce5711913208717b2aa899043719c7534c8218dcec29a6410d697014d32086673b0a699043c3950534c821e1aa829a6410dc97014d32086a73b0a699043939d8534c821e1ce829a6410f0d7414d32086a7388a699043d19c4534c821e94e029a6410d4d7014d32087a4b80a699043525c0534c821c98a63026410c5f7654c32087872a26419043c3551320c821d8a653086410e4e634ca5108716b2e85a08438b5516290421c3ca9b1a8210e1d54d8d410870f2a0c6a0843875506350421c5ca9b128210e2d54d8941087172a0c4a08438b5506250421c5ecba128210e3a54d81410871caa6c0a08438e9506050421c72a83028210eab42181410862f39eca20843175cf6510421c5ca8b108210e35655044108752b1282208436c1c14110421c5ca93166210e2d5498b31087172a2c5988438b55162cc421c5aa93146210e4d5398a3108716aa2c5188430f9d2650c42187ae93286210c3e74194310861eba0ca188430fdda540c42187aed2a06210c3f76550310861ebb2a81884393195320c421c3ca931e4210e1d5498f210870f2a2c7908438755163c842199ae63264210e8e5458f2108746aa2c7908431b5da5288421a9ae72944210c757694a21086e2b9ca5108431b5d66448421c5ecb2a24210e2f655512108637baac6908432b1d163484219d0e0b1a4210ccd73d8521086723b28290843a91914148421b88e6a0a4210de07050521086733b66290843695d03148421d8ac618a4210e3765951210871bb2aa890843719ce52484219cced2124210ce6760c9210869d386c9280434e9c0649402187ce931ca010c3d7498e500861fba2c7280430f1d16394021a74e12a2a010d3870551500870f2a6c6a8043875536354021c3ca831aa010e1d5418d500870fb26c6a8043871936354021c3ec831aa010e1c6418d5008727390c6a8043935c86354021cb2e031aa010c6e768c9500872631c64a80439318d325402187aed2a0a010c3f76550500870f2a4c628043875526314021c3ca8b18a010e1d5458c500863dbb2a0280439658d5014021a9ce7a94a5a056671d4a52d
  | 18 => 0x590e218f2e1b2c8710e4e5358a438863d384caa1c431e5c26550e2199ee6b0e8510e35541854288636bb6a821443395c4648ca21caaa630a6510d4e7694d32887273b4a699443535c2534ca21c9ca63026510d1d73153418861f3b0a8a0c43475cc5450621c76a83028310e38541814188755a10c0a0c430fdd9541062199ae63264310e4d6598f2188726b2ac790c439559663c8621caacab1e4310c3e7498e508861eba4c7284431b1d932542218f6eca80a110e1f6418d5448727b1ec4aa2439318f6255121ca8c7b0aa890e5b63d81544872c31ec0aa2439ad8b6055121c76c8302a890e5b63181544872c318c0aa2439ad886055121ce6c2302a890e3b74181544861fbb2a82a243471cd5415121a70e0aa0a890c3f74583534861e3a2c1a9a430fdd16094d21878e8b04a690c3e70d91534861f380c8a9a438b1936254d21c68c9b0aa690c3e74d81534861eba6c0a9a438ed936054d21c70c9b02a690e3a74d81534871cba6c0a9a438ed906054d21c70c8302a690e6b621815348739b08c0a9a438edd06054d21c70e8302a690c5f7654c534868e3a2a629a43561c15314d2187ee8b00a690c3c74580534863d386cba1a431e5c365d0d218dee4b2e8690c6e7598b434863d386cb21a431e5c36590d218eee2b2a8690c7b70595434863c382caa1a431d5c76510d218f6e0b288690c7870594434871a2a2c3a12439514d61cc921c9cca9906490c5f73595414870faa0c6a0a43871506350521c58a9b128290e3b54181414871c2a0c0a0a4393d4d62cc521c98a6b166290c3f74595314861e3a2ca98a434b1d15388521ad0e0a9c4290e3b70593504863dbb2a0282434e1d15014121ab0e6a80a090c3f7458c504861e3a2c628243635cc6295021a5ce431ca810d367118e540868f398c52a043475cc6295021a3ce630ca810d1d73186540868f39ec12a043475cf6095021a5ce5b04a810d3671d825408697394c6aa0434b1c96355021a68e2b1aa810d3b7058d540869c382c6aa043479ce6255021a3ae7312a810d3a70989540869cb84c4aa0434b9ca6055021a3ee6b02a810d1c735815408696392c0aa0434d1c56055021c58c4302a810c3f76550540861f384c9a98430f1c164d4c21c5ac9316a610e3564987530861fba2c1a98430f1d160d4c2187ee8b04a610c3c74582530861f3a6c0a98430f5d36054c2187aed2a0a610c3f76550530862fbb2a6298438e9526014c21c72a9300a610e3a54580530871caa2c0298439654d6014c2187ce1320a610c3c70590530871d324c0298438e5926014c21c76e9300a610e3874980530861fba2c0298430f1d16014c21c74c8b00a610e39645805308735312c0298438edd16014c21c70e8b00a610e7071580530863d380cb218431e5c06590c219cae33148610e2d5458a430863db82caa
  | 19 => 0x9190a0a0d72718c850506b8b8c64282834e9d13214141a72e8990a0a0d3a740c8505069cba06428283d24c83214141a72e5208a0a0d6b7250450506b43928228283539cf52948418bce6302a420c5d731815210637bb2a4290831edc1654c8418f0e0b2a6420c3d75d9132106a6b9ca41908353dd5320c841a9aea9906420c3d76952411063abb4a9208830f9c36550441c5ecbb128220e2f651894110746318c4a08838ed976050441c76ca3028220eab621814110754310c0a08838edd46050441c72a43028220e6765d894110733b28c4a0883b118c6250441a6aeb2128220e7365d814110739b28c0a0883acd906050441dc0c43028220c5f7358a501062e39ac5280834e9c34194041878eca0ca020d3870506501063dbb2a0280839398e62d5321c9ac7316a990e5a6398354c872cb1cc1aa6439a98a60d5321c76e9306a990e5a6358354c872cb1ac1aa6439a98960d5321a74e1aa4a990d3a70d9154c861fbb2a82a6439358e6215321cacc6b08a990e666258454c861fba2c129e430f1d16094f21ab4e1aa4a790d5970d5253c86aab88c929e43479d06294f21a3ae8314a790d5a7018a53c86acb80c529e43479d36094f21a3ae9b04a790d5571d8253c868fba2c129e43471d16094f21a98e4b04a790d577158253c86a7390c129e430f9d36054f2187ae9b02a790c5e76d5153c86ad386a8a9e43565c35454f218bcec2a2a790d4e7299153c86abb8ac8a9e43479d26254f21a3ae9312a790d1f7458553c868e3a2c2a9e4356dc16154f21ab0e0b0aa790d1e74d8153c868eba6c0a9e4347dd16054f21a38e8b02a790d4c7258153c86abb8ac0a9e43539c86054f218beeca98a790c3f7458053c861e3a2c029e439354e62d0f21c9aa6b168790c7a7019643c863cb80cb21e439554c6150f21caca73088790e565358443c869d386a9a16434e9c35450b2187cec2a28590c3f7655042c872b29cc2216439594d6110b21caaa730c6590e565398432c8726a9cc5a0e439354d62d07218baebb1a8390c5d7518d41c862f3b4a6a0e43171d95350721c9ca7b128390e4d53d8941c87172a0c4a0e439394c6250721c9aa63128390e5a53d8141c872ca9ec0a0e438e9506050721c72a83028390e5a5318141c872ca98c0a0e43c594d4110721b60e0a088390e4e5358b31c8726a9ac598e438799253d4321c3ac929ea190e1e6454f50c870eb22a7a86434e9d35094321c3ec929aa190e1c6494d50c870fb22a6a8643871915354321c72e1b22a190c5d7694c50c862fbb2a6286431edd9501432187eecaa0a910e1d5458c548870f322c62a4439398d6215221caac7308a910e6562984548861fba2c1a9c430f1d160d4e2187ee8b04a710c3c74582538861f3a6c0a9c430f5d36054e218beeca98a710e1d6454c5388672392c3a1c431e9c36
  | 20 => 0xe65d4c5250786b26a6292831b5da5314941ad4e1298a4a0d697094c5250637bb2a6292835adc15314941ad0e0a98a4a0f0d6414c5250696ba6c629283595c76314941a5ae8318a4a0e4d6318c52506a739ec229283535cf6114941a9ee6a08a4a0d4c735045250696ba6c0292834bdd16014941a9ee6b00a4a0d4c7358052506b3b8ac0292834b5d06014941a9ce6300a4a0d4d7318052506b2b88c0292832d1c563d0941c3cca29e84a0e2e65d4b4250787a98a5a1283c314c52d0941c58a530684a0cb6719834250732294c3212839514f6150941ca8a630a84a0e67521854250786298a4a12832d9d46150941c6cea30a84a0e9753185425074a298c2a1283a9d486150941d48a430a84a0c7b70596325063c382cb1928387993538c941c5cc829464a0e2d6414a325072ba9cc3192839914a618c941cc8a4b0c64a0c7a70d95325063cb86ca992830f9d6644c941968e2b2264a0cb87059132506a739ea4992831edc1650c9418f0e0b2864a0cb4715903250717320a419283535cc520c941a9cea99064a0d4c754c8325072732a641928393195320c941e88a629682a0f0c5314a415062f39cc5a8283175ce62d4141e96a7a96a0a0f2964d4b50506ad39ca5a8283565ce52d4141ab6e6a96a0a0d587354b50507a5a98a5a8283d214c52d4141e52e8296a0a0f296414b505079429685a82836c1c542d4141a72e9b16a0a0d5a73d8b50506acb9ec5a82835c5c762d4141ab4e7316a0a0d597398b505069cba0c5a8283d24c832d4141ad4e5b0ea0a0d6972d87505072731ea5282839358f5294141c9cc6294a0a0e4d6314a5050735316a1282839a58b50941418dceda92a0a0e4f63d49505072631ea4a82831b9d85254141c9ec6292a0a0e4c63149505063dbb2a0282835adc95014141ad0e4a80a0a0c5f73588505062e39ac4282834e9c34214141a68e2a10a0a0d3870508505069d38482282839a9975214141e96a7a90a0a0f2b74d485050795b26a4282831e5da5214141ab4e7290a0a0d5973948505063dbb2a42828356dcd5214141ab0e6a90a0a0e6a6514850507a5a98a428283d214c5214141e52e8290a0a0f2b64148505069d3ae8428283c6d4f4214141e30a7a10a0a0f2b52d0850507942968428283c6d4d4214141e30a6a10a0a0f2b52508505079429284282836c1c54214141ec0a5a08a0a0f2b52904505079429482282834e5cb6414141e64e3b20a0a0d3974988505069dba2c42828356dcd6214141ab0e6b10a0a0d7371588505069cba0c428283569cc6214141ab2e6310a0a0d7171188505069d3b684282834e5cf4214141a74e3a10a0a0d737150850506b838a84282834e9d94214141a70eca10a0a0d3b735085050795b928428283ccdc54214141a70e2a10a0a0f3071508505069838a84282834e9d23214141a72e
  | 21 => 0xa9a3a2a228a655c1c1511453287ce1320a29947b70590514ca3c382c828a654e1c16414532c5ee4b20a29962c72590514cb1a38ac828a658edc16414532878e0b20a29963870590514ca1c382c828a650fdd16014532878e8b00a29963b70593504ca3dbb2a0282654e1d15014132ae0e2a80a099559708c8504ca1fba2c2282650f1d16114132c76e9306a81966a62583540ca9d386a92a0654e9c3645503287eecaa0a81946d7694e320cb26baeca99065339c3654c832c9cedb2a641954e71d95320caa6b86ca99065535d6644c832a9eeab2264195c771591320cae238ac89906572dc1644c832b90e0b22641968d64191320ca673b6a899065729c3544c832b92e1aa264194ce76151320caa6bacc29906553dd5614c832b1ee8b0a641958c74585320cae5b82c299065721c1614c832b1ce830a641958d74185320cb62b08c299065639d3604c832b1ae9b02641954d75981320caa7baac09906563dd1604c832b18e8b0264195c771581320cae238ac099065935d4604c83299eec996a21947b70592510ca3c382c92886593dd93294432c98ec994a219747714ca510cba238a6528865531c1329443287ee8b04a21943c74582510cb26992c1288650f9d3605443287ae9b02a2194cf764c8510cb473226428865a359132144328eeeca88a2196c932980510cb64992c02886533dd932d4032d1cc8996a01968d644cb500ca663b26528065721c13294032a74e9a84a01943e74986500ca1eba4c328065331d93254032d1ec8992a01968c644c9500cae438264a8065b14cb6154032d8a6430aa01963970d91500cab538464a80655a1c13254032c9eec992a01954c764c9500cb263b264a8065c3d913254032e18c8992a01974b704c9500caa638264a8065d21c13254032c6ec9b0aa01963464d85500cba2996c2a8065934c86154032c6ec830aa01963464185500cba2990c2a8065998c86154032cca6430aa01964532185500ca67bb264280651edd950140328bee6b04a5a0c5c7358252d0637bb2a4296839358d5214b41968e2b2265a0cb87059132d06a639aa4996832d5d0614cb418f4e1b2865a0c7970d9432d0727b2a641968393595320cb41a5ae4324a1a0d387050a50d062f398c4a8683175cc62543418f6eca80a1a0c6f76548529069d38683284831edd950142418bce7306a4a0c5d739835250727b1cc7a92834b5d063d4941acae231ea4a0d4f7358752506a639ac3a92834b5d360d4941a9ce7b06a4a0d4d73d8352506b2b8ec1a9283539ce60d4941a9ae7306a4a0d2f74583525072731ea5292839358f5294941cb6a7304a4a0e6b52982525072da9ac1292839ad496094941cb6a7b02a4a0e5b531815250637bb2a42928353dcd5214941a98e6a90a4a0d6b7054852506b4382a42928317dcd60149418b8e6b00a4a0e4
  | 22 => 0x8003002c00002300880f405c005000801001400e001801401e003000000000c007000004c010001008000402400a02900100120220060020000003009800400a00600080000260020008014010001004004804a00600100080020010090004024011000002c000018006002400a000002800c00c001008801800800000a800000200c00b0024026002002002400000101e0004004008001003c00001d0028044006000005803802200e0020094002004011800c00600200200280000120000008000003007803400a000001007c02400c0168004006006006808004c002005808000200400380180120050008008018000001805400000700180b00c000100c803007a01d00b8000006000001802400a0040020030006008001000000a00000c801c01000400080180060000000050018007000800000801e02d800800200f010000800600400900000560180028010014004003001800a00400d0000012000000000000001f0008024000000016800800c00002d0000040007005801c00e001000800000201c00000000000020298034000013001001c000001002801800a008007000001400401a005400000b0000000038006000802400c0070190000000001006801c00400f002800400200000000000071ddc56094f428e8e2b04a7a145f7654c53d0b2aa9ac229e8517dcd60947428b8e6b04a3a161e7418d51d0b0eba0c6a8e851ddd95114742caac6a88a3a15357119250d0a3dbb2a02868517dd95314e42cb2a6b00a721477765445190a9d386852848517dcd61942428b8e6b0ca12147b765405090b2cb1aa02848517dd95314d42aa8e2a98a6a15587054c5350a3bb8ac029a851d1c56014d428eeeca88a2a1554735445150ab8382a228a8517dcd60145428b8e6b00a2a147b765405050aac39aa0282855c1c550141428eee2b18a0a14747158c5050a9d384842828517dcd61141428b8e6b08a0a155671d4e5310a2fbb2a6298850f5da54908428daed2a4842143e70d954210aab39ea3288851ddd951144428eee2b1ca0214747158e5010a9d38685280850f1d94294042a70e0a14a02145f735865010a2e39ac3280851edd95014042c9ac7316a91943f76550548cb1aaa2c22a4659358e6215232caac7308a91963664584548cb33312c22a465991c96115232c5aa8312871943f74582518ca1e3a2c128c650f9d3605463287ae9b02a31947776544518cb1ab22a228c650f9d2619423287ae930ca11955a70cc9508ca3dbb2a0284658dd906155132ccec430aa89967361d81544cb3830ec0aa2658ed906055132cd6c4302a89967361181544cb38308c0aa2658edd0605513287eecaa0a89953471550544ca9c382a82a2651edc161151328f0e0b08a89961c5458f424ca1fba2c1a8a650f1d160d4532970e0b20a29947776544514c
  | 23 => 0xd800a002000000800c004002000000e006003801803400a0000004024003003000c002001001805c01c000008801400400000b000c00000a00000040040060028064016002000000008600000001f0004000000800c024000002000000600900100700080010060004008001005001800800f00180240060340000014096004000007403001400a8004004012001003005a004002800000000000e802c00400200000180020260080060012002003000803e0020018004000000023800400a001000800000600d001001c00001700000100000000008000002013000002c00e00e007000000c00d000000000c01b00900180060030028014000003002000c00400100000b001c002010801801000000600040120020000000006000003803801200800c8010006019000801000e00b000000000200e005000000000100e001c000000002000402400b0038008002000009804800e00000e8000006002000003400a005000000403400100000900060050000008002002003002000200400a003800000500880b000a002003000000e01b0000004060006000802001e007013802806e01f005801c01200001480200020010018010000009002001001c000001000c00000000080000500000000000006000008801c01000000000240080020008014016008000000400001600a80000540000028000000016002800001200a00400000020190000000044001005004c08c004007001c012000000000c00200c001000002600801a800004c0000020048012003000000000000000d009000c0000030008008007000000400e03f00080340040080048000010061000000c0300060000000000011000000401a0060048040012008000003c01a01e00000c00000000038004066003009806c00e017000000c0180000010000000000000000000200b006001000200000300480060190008008018009000001400000d000800000a0060000044002001001000002c00000080300160060058030000000000000001a001001002000000b001815400a00300980240040140000020024000001002c032009001000402000100900000020010008044014000010003400805200000040820000008004000004000801800c00b00000100040000008000004009009800c00a00400e8014004004000800805c00b001004400600100a00b800a005000001401002d002003000a002002000c000004000000001c0040078020000000006800c00c00000080140040000010008000000003002c01002f0010000016017000800c000024002000400a006010802000000000100d8002005001802000200000000dc00201e000800000c00c00100080240020010018002002000000800000f00280540040020000008000006000000c00200d0000020004002002000c00202
  | 24 => 0x60000000516162d8f4852e107920000002eb4e249ad000028c0000003ca13c800012e058d9e10780000e087853e30390001ff4f1e13a99c394c4e20c47032c6557a000000000042039b3be903962614951101b998033235b802404c7cd5552f3c90e17a00000014426ea246c0000001cf800000102fb3b27731c40000002b8a4d0ef8917057b9f215ca695ae81ea2e45a346b35f59341865536a0145617f25991c200009d23e3ab09b00006c4254416b48d2dc165400000100340500010038030006002002002000800e000000000000000100600000010000014048000000001c02201600980080020050000000002000002001400200e007000800e01e0018008000000002002c0340020008024002026000000000e000004000400c004004800401801c004800000e00b000001400403b0008048004001006800000801800480580040050000000004004005009c0540080020024002016002005c008013000000000201a00f001000001d0040110020002008000000400d000800004c0030020000052009000000006e0120008000006002005007405000000b00000220000008000030001001800401c00b0020008002009000000c00c004000000400e003000800000000000e000800400a00200d0002006002001000000000200080180040020010016025000800c00e00100200b400800e0008004044003001803000e007002000001c015003008800a00a000003000c000006006407200000100000020040028040004001003000c00001b002800001200900000140020030068044006000003000c0080040008000002007001800403000000600b000200000180040060010008000000000001802c000000002002c0300100050000000000001800c00401100000040300170008004052031001800000c000003003000800e00000000080000008020028006002800c004009009805400000f002001806600b000000005c024011002001e00301a000c004009000000c00e0000080010000018000800801a003000800401c00000200a4002002005007c00a00200180000040000028000006000000000000000000180280000030038004000000000002400200400b8010014002003000c01800000180440040020010014022008009800000e007000002003000200000080080000000058002006003000c0000070000004040028002802c09c00000380000000020078000002005002000401000000e8028016014000801001a031000000800000000b000000600000980440000000098004010003011801c02600b002000400a01b001001c012009000001c0020010018034080000000806800000500900040060010010010000011006801c0020000050004000010000000000000900000040000060008000002002000002400000600e01
  | 25 => 0xa98ccd168040b88816c9a6bd87578295ad6a456ac40016ca4e068023253420001ca16957a873a0000bb913c1ba4989335af8dcf07781ec72e99200023b968834f29100005460b565f00013eca4068374192ce0000000d0140351948d8996000aa124bdbe0768d0b3fd94752441184161d3d6eee655f91da894036a5bd8ac854286dc34d129c42c5200000009a8e0a0000cc141c45759995027c36bd0d428714d40001ad0bd073a1dc8accb8fc665b655c86e49bb20336a12d8b5c8e754718912ac8275e2a928ccc2fc2c22e7d0632a267b5cd924e58a31da55d97a20c26aa6f54907c6372a0edb627253d3257856034c32402088fbe884b421452c217622209708a4000287f3c59780002068738000943a499d2000086e1c78e0cc82dfd00351a82b729f36d39ca00025f3cd0a749d8b561d18d6b48e3674e28a4db364c30e68374000e7768496f584e31a310069d1140215de85c138e58f11d154c5169725879ec185e00031b0000df80000da8ed41b622d0000439bca87d2b6087fa48366002073c0fc0c16f01bb80119ce2eb085710237729b00c568f9a030196d56e80c1965037d14a908d600000130ad66fc9510c3ae1535c38b051cd56a8185c479cae707d1d1893cae23ae21f0f820006df04182f200013e8000000caa682d79dc603410e20e38b4466d0cd9e246b1cf042c2a793fa4dbdfd8b4c000b5f37810cc93a97e10d334867a00028b26bec6880c91b1a4c07a6d81dc3530a52136575a4602669168ab00016f24583882bb4aa823e4d29519642c403700c58a5cb80000086c000224000000000028900031680005053b9000000005771e126502000063b8f0d42216736b8f9095b0005f480c06b0c7452b0415936bd6094328cac22f314a80005ee9bb47181114235100fe8000000a5b80027dcaf89f7be3a94000000000000012821c680000011a600000008440004df00034540007ae4d11f80458a0d4f300000000000000001b78a3d66c9dd000045a18291d2870a065f88000cb008400028cc000d85b99225400000000000006ea00058238d8c7aa0555180005814bb000000000000062b80004ab7680001ca07bc0005b60f119ba0cb47ddd4000068e5ec841d63c0a643faf057546392d79f5c2b440400000009f8e5832e160dad28ff2259e5487ac374d380a8ad26a304305890727702248000356e9b00000019748020000000118000000000000079800000007b855b00000000000000002550b9026dba1176936c1b070c1b989b65a0245e3c4000d891078628000b3963fa0c40000000e6f4f558c00000023a8264102ba4a6a061e8323eab6be22acf933e07eb38c61b3899500912a9141fb7adce67b409c27454e26253d89cfdbb42697320000c34579289367063e2e709fa47885a2dc31864fc3bf4909f170900001999fb80014
  | 26 => 0x54c00013788c45788200003adcab40005009301cc2cd764100015261c0cbb5e9c0004d90001a140003270dc4000d484e40000000000b605d3b05056e325e81802d926a2563c8b584a964c3b8ad883bd0de00b000169cd41299956057acab0e3a6b97a0a25cc98000bcad74000287b24a42b018d3b509e72e6a0c8b860270146c25c5a0eba8088f12884284800c6b352b2268d640b2b1bc653000369c36382e2d939ac864d2c5181b79cae9092dc97b98a665d3b0a0bc89ebae2c612553c6c2b136119418048a4531d5c80065f13d000156ce0e05a02488d52fb525a8f97c70006952ee9a55aba4df9b498025d942ebac15b07788ef80018114e14f6c58e00000023de7d42382a769840007fa0001bd00002b600000022e0ea8dcb7593aa175e1991c63438f8800000004ff793e4c4c8481d73cb7fa7a300d1349212b5b53251a165714ad05c8c8672e83944000d932f21ffc00031d069a7a053600013c800000081941280000001db00017ad763a0b4bcc0002480001f41e940448fc00000000003156f480014e6000155b5469644201729f0801036171d2cd40000000000ec60009c24780001910cedeb300000001b3000000139605625880012d697f4bc4001630dd0555e26536a33c10b1dcc6e40804749f4d9cea0a25634da8c44a501035e0a42000148318193528457490900f800000020620004b49c4995c0000000000658000498e95dd7d3ce2d2ed30aa4000723306209815a3d113f0000ef60950000cb130841019d2260a14d7b45cb32507c3280003a712b013bc06074879a0003ad0d50e12c3c62f8000d44bb11731e5c78c7270001645bd0a6d00025dc0008b60ba800149c65406bc000c030000aa94704ca3268628001224d29800398a000dd861108bc00000000019a855c2e2df627ed51a2cd9bf3a4c0fadd90002efa5f050c000244b361ab014c050daf301454b317000001e000305c00086300011da0005bb3a2cabcef42975b4455e9109d46a4a9f00ba260717af907ec0005d09e7c00062b264b56ae4c7468003518cc80e51be83d5794b711e408f48a2e0933380015cc4092163a38e7cc0b4d2368c07072d0c433dc01d61bb06a9f402e00055434609f20000000000000000447b07d1487640ac753a0000c9906b834000016967b6cd45ecf7e064000000e56800211d2040002e79eb4000c610000000000b788e0ee71bf6b5345eab040e28444f81e44a103d32941a48ba800031115497c2a16016c14dcd77791f482c04da9ff2690ae0de478117d16c4200d9a00019113869e2000319ce6a87a4350000cecb93800000111a0004a83650a1ae6c1b1358103099753d2e2cec6a7f5087ab419201311ab9884304e3279b7b89b85cc09aa3959321aa5561ee846002ca039e103d498d2280d104311d73f8a50d812e0b5ceb0d55fe3e8b
  | 27 => 0x22f08f16103e130a8fb070c7e743226e4deaac95a807c929440a00000013f80691b4aa0998e5906b1a4b0fc634b0af2a5503a76d0a200397c60d01f99400a12af130499688c80119eb33703ea8fd2e2ea80bbe63318e23984ee724000176da20000748836200000060d159c7e20003719331abc1ccec132600001470002f8076c589082315f942adc71195e83b700051413c0c245f45d84115a5c1b15721a254a6bd26980f1411e3f53d213757fc264890350c9168cb3efaab84dcd5646232c198a599209031d8d80000001c080005e3bc3ac48fb8253511c5a057f96d4970cad0388c806c199546cb937339005bfc0d502100004ccb2b2570029b164d78c20126c08a120ff1a5c96a7e25df818a7402004f00a94bfee02712a8654b213d35d80001482923d480000a2ac25b089412c0e5d6bfa67d9c89ef000000086a545723648ca289450eb2ac40000002ef0951ab45342465014f6a2454b74b230025c300001a93d40003bb36bbd5400000003b1912000274b830428c126c2095b92e0000000000f403ab3dbac01a9ec6400024f5d08d59b3d8001bee5965aa92f07fcb3d0003a8c0000005db8001bd400032ce2ddcaf1595a0c001b8c00047a172c0009304088001a970da8002c3a3aa000683c001bb8d3113a4a00abbbc39118000ae65fe00036d4fd4bd30000425c6ae860002a6440bd756a201b7bce5065851a68c04a5b34e351319e00005caf798bc13b4aa907c000d73110a8b88a69962cd87996360744e2164800c35075c205741edd212b90e5a6761700034bc0002886ef996cd90a4c42923a009400017834e6000e8a00000011089ab05985bc472e7c103445087c00000000016cc2c003c0e4dc002c73d62d0966c1d36dd07a1c7646d0959c5843e07880019897329a374380007f243173a0000bc2d1f52916ad0aa74400021d80000616ab95c8bd81389ae2ea40000005c815d8cf4b0b5fa8546a58b1c5c180000004ba345b5c80005f01cd04a56200475220e2001806c1b681bd067e1f198bad0cea56490977c5518a1f16a8d4528459a6c8dbcc5380006abd6f233461344587700000001dfad82f061730001b3967eaf33f200003f82f6001070c34001052d65ef722a5769f2a04000a74394a8f00008710000e994596a961b23db9fe158348162dbc4ab4609616d2ca2d805d82ac98709b03b170373be7f33884657782cd33f2a88ba61a242240662849cd22b0c602a8160597929a6d8cee5a40204d7842387ece40d36ad30e319c17e054bf341900cdc4304f774ebb5c0976b089246ecb230002458a8b9ee5d6340477cc546da4381a8457e34c1554d86b4996200003ee0d16c933bd15e9b451221acd42cca64300ff70583d185391003b12200ab9f6f0400002277b3823ceecc082215f26d64b600000008e10000000f008d712a8b47
  | 28 => 0x400020a9b280000bebcc0b6006d80cca82ce8542d0e63e69096e20000c31ab86719c44f840a944d7ca0b76fb2a7c0f70be301dfe99181ee419a8e15f0b7031423c84c89400000cedc84b031eca63809e8774b4539c0000005b4b528f20d0c0000001c2e1253978214122000693939509a14e0000421c0829e455000003274b1a4aee09fc00004f95dcb043b924c00007a018f20c0000e08dfc00000018da0000002704d06a8b4e78000000c104140001180e6a4a263d8e0ac456c38e647cf03519ba00d576000552d598d7c5d86b637e8000cfd0918d5530a753cbe301eb9404c5b6b38dbaaac73f70dc0e1a9a63de16516d60e08a4e06d87a2586f6b7fd93a4a7a9f0ab0f9ec7646c9ad0c2c0004488101d42a3a62ff02851834e5a900710c093b2fcb6589a9e9400fb6f4274c780e586e03b50bf07d98a8c8c0000000b7cdda0000d6575c00038d43c167807ca1500010e97f0c6230504c05e246b1e607791aa7d46d5087800000000000017b4cbf000000082c0000002a9c956653ca6120c6bc7583bf80606d6aef87561a4d9e89f4e400000000003c40000a367a31b995904f8e82194610400000073f2768000ccc4dd00019643e50d6ea70000e793251d0c822c8f5a51e76af67ef53604176fe0001ae800000000060118724ed0006328000000ceb0000001c720000000f480000000002f74d663a46dc0000b0c58e1a409d0c9c11630812a03203d50000b88000d5480000012fd6ff00028c54a289b0001524000b0620c8ca9b11b3c115000164a000598b539c944910cc09de84e1171611cc44192de0000c4010e2def318f51986d6472a881989a7f500000005e44a940230c19f03ef53c2b6c57ece15c490554b053980037980004de33b82342be3ee6810000000adf2dfc32f4ce0005fb008db221ec4c829803c80005cb17c40003744038d0c1e00006e28842612396089225d9a8e6e1d6ac153801e90000000000e110001c1c3a265e00013bd23854838c975690c7650b6882c3050000002ca95d4608000015458928268e931874e60a800118c9840006241f2cf380000003480abe9060002118000000000000174a00000021d458c6df5f101657680002480e703292425b4120ad086dc00009ba78e48031936780008c55c51864e72805407000000000000021780680003762a3c76e87360e19fe000b0e3000000000c5b17e8001c90c9c322800000079300000007da1ef000000171a0000000ade82e050a7b2a401fdcdf5e129e599c7770a02e5468e54a45421098d069d47d202c9e21571870678fb23b32e2049cf0c9070000ca582a86805483671f57561c3803d15c3a21ad97cc0000aa5d051c572e75b41568500005f6000019021e00000016017d600000008c99b0ccf31830a020f01d13ac9280007b82fd904c0000630003021aab854
  | 29 => 0xe409b2b4298ba059c2d3e414b571bd85a8035ba36e6b35889c5c65bf73c99a62cc1220001a9acf29d8a114000a9d866741592200070b298d4d693c01ba85b7f858130c39996c8dd62ae038d7ae00000016dd0141cbcf59dda9020000002e98f802a63660889ca400000039d943062928d00009e3c0700030cd6989446d0000157c34201d2164e0078d45084b013813720e83acd14b753af00bd2e3cc605c053ccfa22812d000000005406607b4ed6aca14ca4f8e3c7524a9ade844a56a4392dd933495d3d125995d0a1b6d7a5885c061e0b234281843fc1641b840008f90fe6ba202448c48a000000000029c1b24e9c5a635cb1d4171e5c475b0f90de4465e6a43c91e8bb411b4200009633e4329032a4f560f352dba81505dcadb684a8572da000092c87b67429a03e270f4ae054b70247213561b5d3a85c43f0ba8a6e1b754228403f44be29f890c02295b74193a800000039803a06f862f372028260e00000020b473be805010bf8fdac9565a81883e8000000193ce4400044103201010656fa80000002486e4a61cf180dd80000004561940859238000c6600000000003910f595ce00000060fc0019e34cf14d36d031c637554acb15641ad75209fc0000ff30f8eed842c34643f76c934e1c3c7171537863c6160eb06264d70d31671a3445f0003125ce22b56b800016fa4aa66d00000005aa0000000d0225d000071795ea3f634d1fc262abf2b293211e6000000191c04a60f58f8000fe00003788ae921b19124fd49c49e000568b6e4f3c1100000985128cdb54f51ecf142cb80035bcb921786258c359bc76e662120764000036687e0df6a084662de1612d5f1bc9ac01f05432d09a9c19454f00000015108210001ac805a53a0002b9e000c9e000371d3e237817684e419500000000004ac00019ab354b74e3e23d17a790854105087246b2000689a6ee000e260000f815660005ea8d900000004f9ab68c4200022a800065e00000007c20001cc1a52898f434c49921539be67f918a274d3063e9f5895352509dd256800413452d5449940a30cf36f6060c26815d1028430f6671572084bcc4e13ec40161458b50146837d099c00060780b191a0000e47a958ba00027ea01896b1e20001bd1316272d3a800135290c3683a64f9895a2bea14d22a88620a14ad8229081398000470d1e00012cfb64d9f7142ab568e47059915645a2a430836fa9a6a5c4e5b80000b414a0a551f200035600031aceaac1d00035959520000001b883800003318b0f59e9863a451356b60000b5b06c413208000266000000015d4000000ca60000000b820a00002e311601660000000adc00040a2ffd7258e583320a965ac3f0002bc01503a16b4c00064a491a98a36c2a2c34bba8000282ae14ba000037c3811e091d6fa4638265052f5f8cac1500f6c7505047549ab
  | 30 => 0xf405c4c71e78b6400075900002ae8fcbbb5f6a405786b6e5ee024c2890578e40ffd9da3dd346000000046f00018b45c20000000001a6c6b60002188000be8350324152e4aeed825b74c8a3b2238ea4e1c2a45af23e09c47404f490698fabee21d89d9a366590002b65a90181713b1a53d34a2059287400082de95a795b503ea89f1c0d0d898f59bad255ee0002d9a761862ccb104b105418cf43c2876800016948995d400000070da8a5cde000000096cb2eafb00023495f49b83e1a4e4087aaf50999808cc893244e84a0002d06b735ba0006066bc80000005e3080b3098e042a16916a5aa6d29697c00000097a5d580013f00003a080002961ca9f5351da1e10a7348000000acc000038629b4920000001548680721a2b5b5600000000006220006020bd40000005d9000000083a00000000000005232e480000e286905b8fbc0000fd8810e704684d897c3bdeddd00019ac0003266e5027950e7c94d500004d08ce49788fd4aa6a66d3f32121cba2444aa484bcd545fb8000bd298a5379bf8efc0039d526c00e46af03a754aed800000011dd9704f769bab156b02beae4c0011240d66d61789b0017ef081a3c00028574827c8cd27d8672b878fd67d6533276d16ac4f2062904d07e8d22a06eca2e9ec00000012d31f02a590a5a1a0f63ed3958aa267bdb900cc616000000000196842800030b4a4a2b147d80000000001a928c956a9e8ed20988326e20450630800000000000d8ecccf50d6251c23a41c00016b40ce79ab11aecc000bdf24280010705c24092f1da51c322ba24740b8c3a45f244000071f0679020000bb00889fe0a72ac40139cedd4c09dcca2cd1710ac36b371ec5d00fc05e85f8d103a538ea07c4b299d4b4a28c00004913531a9c5489667e047900000050b8000000000515000142f9be465339e0bbc7c262908d90d00041589c8936a9a17fa6460009362811c18ba411b37400002859f45b187420001f900024e049671b4c612702e80002b18000fb60006d8dccd3631f64b9818085c3464b20001578a202d823800006fa0000001d3478b11a141ce686680000484eef000736800016cb5a07480347748906e992c063c1260000cd99fc3e73961f749826ac06cb75dc1ed4f80028b06440006c537903b3e60737d2a35a48496e8a275c568b3365900c1cc24022f71619ec5ce1b1800171c96cebbafe85a130c10702e81e2000177925c38a4a121b03f81b941b640b3ec73e7f3565ba5c204d190c2883b23426998c80004023177490b8c000000470c001c325500002238908c2e0003675b4400031d1bf5ce000000011fed22b015383515ca82cb35f8af388c47529e9079846b6a1cfe33421ace90db15598b24d607e8ab4c84ccd1b7919ce181453218e00fe4a35759a0790be0bc2c6a3f8c5c1bf668899e206441133b22842a84
  | 31 => 0x3e0002d1998250b2c392e593ee89000178a0000773071ec80000006c61a79b1c92d513800079b0002e880009884cb2bc0ef0d8e1ff58a0000000c293d400000003204ee262560ea1ad3f136906ca1a53b86900009df260ce488167bb230ba60fd08e409e0ad9afcb026cb80011100994ce2392cdec8b6c2982c00017b750000069a6eb473cc113b2c473ce800042e18d23b077497a00037bab401b45a4696979e1da395000085e056b1a6d979ec668d520672c9c000c3b000000000044203ca53c880cefe9cb4c80009295d6cd4c60015358ead017fa0007510cfcaba079cfd3500cf25fb800000023ee325a45b6c51ecae17cb4d0fcc2db717209043827b38c221c9702ce066b54044e43ded9ddbc1447d01b0127c0349a78382a50bfa38433084634a8437000260192c8e2e2aa49927743fbfe060994a05052f0fe92f261421e150704449daec5ae8a1ecb3602aef8d80d860ad4b695c97e55a040017e600023a34d26d0d5b81480016ce76967530a850c72b4bc1be55ea65102433402547993fba9687840e25cd0acdb7e984e932add0946963d59445bd700038e32391c400062214362b904e40425a91620002740b75c920000000c6d43394952cf6348045bf40b2e518e42e93a69c69304e07368aa18c0e4eb0cbad50a753f853d97f1ab24b4113000118ec5170e800085e73d6e600006247e10000000482000000044db9c05800000000006995bf1499a740005a2b695a4a64b27d8000000ad74bab15a0009e441b80018c608e2ee94c0a6a1b0ec184b543cd143e881e9a70214f0900000001b2740b4fd20079b039ab38d540680f2ae19b021525e4a6c86068566d68b04a8946e40482b13fc2c943825181590005daa4dc58ad6270a1ffab783852410586cfe8e8cd6147dca0d1745601355ecd3339e25f435f4b686b839ca85e4d4888b51d16e5b0dee5f6d884796ae09484520006caadb2000d3b00024cc0005422cf80000005a83bae29c000a090f3800184c00006a1fa40000005418ef400b84b19f2e3da460003398000d4acec00003c90c22c345912dd900891b3a0c844260003d500018f452f68b27487d61bc0d097a16181dd80000019cc7c54e80ee20000000ec80001e61c200018d40000000a4001e886c2525dd55d1862942bfb6c2db2b223ae864762a08b722a0d5bc68f75e438d08b8e85532a4818703e6492377908000036095bcfe800000024340a494b00003dc0000000002b7501e0000000000cac000653aca0346a344a41770ac0bef00023b04cd90b00017bc9a2bb60001532b7c8da75716b14ec47880035c400000000030ab65c9ed74b1bbc7bebb69ade8100000000003000000a4f0a3e5b8000db658bb410000a0048c908800063f36998711be4a40000000a0325100011a40000002900000946e781fdb9f476094d03585
  | 32 => 0xf8d7885cd6270083ad04a75cb617b5de53c2e0067494caf212700f027bade000151c3b06a80b097a80001708000000e8abf91269ef5ad400060981b4ecebdb00013e95a8e4b19186d18a06265452754a1c000239a034312e131b8ae618e6a5c1b8e34465a5700e538904e0c2033e72144c60219451c8569ab6f702b0634ba4e60000001832000000171c00000040d00005768f780026795c60005e017e94dcc160000c216960242fbad640bc0005c10000f5508295dd47843a000138c29c4d6b5fd11a9c8000bd133914ec029df26f08b5cad3b0d0c6364192415586444f350a74c2f02c98b30d5172fa141c10a3739bba9cd0c2b9c3305dcc0a0003db1a0888aaf439014c807e9704ccaa95cb400071b88360006b109cceb9972be60002d3d6a26ae6d4a230bc338200bf76f0f22471fa1de0f7271424a11b12e1c0e14880002ad8dc0000001086d9901911227ae7a15e32e1c81ec7e1f91e5973d000000298868a38b17600010600005ae0001674d22716a37400000023c15a0ca42c1983117535e70a637393800004651d67301065f80000a1d14400069e2aac502e9548fa5381f2aee07a297c12cdf04b7e169c628f5570062c0001a562b32ed32203b0a3084754f04b700b8fcd8c874454880945a53f84520d02b8c8339500011382eb688969d7367ec1c52df00005e60001aac3240003e70000c58000482884829a3708000000deccfa1cc00015aae590d54384d285bad24a4acf410eff4f2bf90527be4608e79c0695f4990ebd6480431ed39e873d0c62b111652542aa11989e2868afd5fa32880ff76068c400110a23722412fc0fe0944b78000cd80000f00224fece3d3b108edbf02b449d36ddaec45b0d4a2f13ae97b32a8713b290001ec1e496604a990c86af9c0cb64eb000d7cebaeba3a8e437a0007200ce45505932117710baa11a61c919f3c26015137700dd2e9f727ac4502ee477478dfcf5ea4d3ff039032100048194913bc00036eaae0000c0d000078c506000101c9d5c3400015caca581899b06e11f4d3e0006cc3a30a46d7a6ad99240000003652549886d55658a20d098c18163c00190ee83af689bfb766d56502bb078052a71c370487e32e17222e82f8b160d71b140eb42612600a0ea2bce476a5d3b310905e587cc3a8a985d217d45c930207501054c24af6ae83b939444c0cf8a587640076b389e10ca68d34a9620794dc24501455b907085b98d5f53adc33612318c220002030001d6a71750380018848bf00013fc00000072f22ac30054c4e49b9c5711af71100000000003dfa909d6c16300001d40000003e52d0c000ae54caa4d47963f04779c2c30eae5e8917c9a501d01af8001898c9446a08dbcea36e48235615364601ce66dd3f29b36d09578000b8524366209a0000135e5d9a38b2795f2076ad12461f10000000b
  | 33 => 0x2203268657adac6f0001d2800000535abaacc6256d739000059f0000000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x3210220b418018d3214520a18805905308520b10815c05310120b20804c85110120b0a858c8408c120f0232144408c120e0853188404c120e08654c8404c120e2062144404c120f0132144404c120918805d06154c20a14845846154c20a50805846154c20c45531c5600c820a1880591530c420a49801d9530842084c8754d6008420e0a6454d6008420c0d7654c2190020d08721c15310020d09535c032100209a0815c03210020c0d7654c2110020988835c02110020d09535c02110020d09535ca6010020b0985cc840cc020e0965cc840cc02084f87d97324c020a4585cc8614c020e0953588400c020e09650c8400c020e11531844048020a4681dd9534802084e869d95348020c0c76d915348020c0c761915348020a448654f6148020a468654c6148020a448654c6148020e076454c6148020e046454c6148020a488654f4048020e41531874048020a0c8654e4048020c0e7654e4048020e05531864048020a0c8654c4048020c0e7654c4048020e05531844048020a488654c4048020e41531844048020a8a8398c4048020aa28198c4048020e098518c4048020e0863d4c4048020a888694c4048020b098594c4048020a288654c4048020a888654c4048020e0b8654c4048020b0a8654c4048020b088654c4048020e088654c4048020a088654c4048020d0a7654c4048020e0a7654c4048020e8063d844048020f0153d844048020e09531844048020e23651844048020e83631844048020e80631844048020f01531844048020e23531844048020e82531844048020e21531844048020e81531844048020e01531844048020d0a7454e524802084e87995320cb10d0a541c1320cb10b0a83d4a5210310d0973d4a5210310b0b854c83210310d0a754c83210310ca1725846110310a45839486148310b09839484048310e08639484048310e2252184404831084f8758f5208310b0a83d484008310e0963d484008310cc1321c5600ca10ac18018d3208610c49635c06314910a48854c9600c910c48754c9600c910e08544c9600c910c31651c16408410a458518d3208410cc0631c13208410a25821956110010990835c74210010c31651c54210010a3281dd96510010990835c76210010c31651c56210010c29765485210010d09735485210010839861d53210010d09754c83210010992839ca6110010d83731c96110010d80731c96110010c29655c8611001099283ddb21100108b1861cc2110010931851cc2110010ca1769c82110010b81839c821100109a187d8821100109a1871882110010ca1761882110010b21851882110010b818318821100109a1878c82110010d80734c82110010a90835844088010c457558c2108010e096354840080109a1870844008010b21850844008010e81630844008010a928398840c4010
  | 1 => 0x12b94824030f004066a000000c04c2b721c16414532c28721c16414532c30711c16414532a8481590644c832a8880590644c832988805d0614c832a8484584614c832ac080584614c832c88641c13254032ac0804c86154032a4681dd93254032c0c76d913254032c0c761913254032b0a84dc13254032a44864cb6154032a44864c86154032e07644c86154032e04644c86154032a60804c86154032e43804c86154032a44804c86154032e40804c86154032a4980d95320cb41e04531486150941d13531c54214141d10531c54214141d23521c54214141d20521c54214141932819db4214141930815cf4214141930815d13214141930815d03214141948805d5320c841d12531c14110721a19831506050621c30741c56014c218e0805c4644c821d0a545c0534c821d09545c0534c821d0a745c0534c821d09745c0534c821c48865c0534c821d0b845c0534c821d08845c0534c821d40815c0534c821ca1621c14110421c84641cd4148421ca0641c14148421a848458c3148421ac08058c3148421a18805506354021a4b854c9600cb40cc1321c5600cb40e046318a5150640e23629446050640e20629446050640a88804c9600ca40c85321c5600ca40d06739cb5194640d22729c35194640d21729c35194640a2a809955208640a0d8518d3208640a898018d3208640c49651c1320c840cc1321c5600c840d04731c95110440d20721c15110440a15831915188440c25655c44208440a2581195524c840a8883548604c840c89861c1320c840c8b651c1320c840c89651c1320c840a88804ca610c840988874ca600c840c85321c5600c840988874c9600c840d81321c5600c840c8b874c9600c840a88874c9600c840c88874c9600c840c8b754c9600c840e0b754c9600c840e8132dc5600c840c89321c5600c840e81321c5600c840ca2321c5600c840ca1321c5600c840c81321c5600c840aa0805c46254440d04731c95114440e06635895114440e05635895114440a26875895114440a24875895114440e07735895114440e04735895114440c33761c15114440d20721c15114440e21621c15114440a898098d3288440c8a631c13288440a15831955188440a15831955148440e21525446048440c0d655cc5208440c25655c45208440c25655c632084409a0805c63208440a0d8518d3208440a898018d3208440c88631c13208440c0d655cf2108440c29659c32108440c29651c12108440c31651c12108440c89735886294040c89764c83294040c15735846195320d0a745c0534cb20e0a544c9600cb20a30815506050720a0d8614d3290320a0d8614d3210320d08531c13210320c47531c5600ca20c2b721c16494620a3281d5060506208ca87cc9600c620c29651c16408620a498018f5308620d0b535c032102209a0815c
  | 2 => 0x9f1ac7734ef30b0f035e3c21600390001b6003a09a40d0b34a3b144b34190a1980602820164b03fc180f808c10b83c4f91bc560f4c61b4021284407c78baae2000a92a085370ef294003f80003d00184ac101012a90eb38d7030322c84d29cb640834150133585f2487526c392aa7a94857238db3149e170653d0ba24c68118af1b87b280c43f40ca0cd3424ec078c925c84094141d89d00c1038c000004b0002c800ed0b46cbdc263ac6702420960111ce4e834d13ec47228981e07f0c4acac6240a40713c41088490005b2a6a608c43284cb1e488b2e6023ca33308cac4191f4cf39cea2ec6a240b5000bd3602a04e880009421c2f32200254453d8960750d990990e87a14c55140e6208b6b54c1430de1782b0a0df000d90e0b71750820ec00c0ae1fa0006ccd2e40000000000000000e000211f0bf1b08b000000000014e003a400000b40d8ee136120c6da39401010d01c817070e1434bc27074858ad0000020400000000fc083d47e000000d4fc0b8d8be8802880000071000000cc42068000547030cb58000b31c00350d22acf22350e0001580107374c2120890004e0dc001300018891000861d00000000000000008c3e063000001cc0009cada90690145a000afb28001cb05000c81aae0000be020000d01010000f0012004130600806100101c1a470380822000003c0c000580400020688c00060a010041e0c00c98050101c28000a00008000300010050680808010701c0c0d008081204028080201000084011040140202588400c010001034000104c
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x1c1c42f001e5000014309178040c0622000030f56e8036046892e0000004800000e000161000d15002c0193e4c2840200c1020001080821580a53804c86154032c0443108b80a699043840862057014d320872010840ae029a6410d10e55321c5600cb40a404826438ac01948148291e1d32580321029012e996e2b00642052025d321c5600c840c02438e6b12a228881420975887054451103800e6b10e0a88a220608594805c63208440a04ca8c638264108814099614c704c840c83206a640ae0190811064054c815c032100208844c2a6b80422004160291e1953101200824152d432a6202401058025953d844048020b014b2a630880900416009654c6110120082215313aa64190818858064e521844048310905cc2c7a9080106218817660e7208440043042ecc28c410880086205d9831882110010a40cb0e69904220021501951cd32084400431030eb18422004008680615630844008010
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 29
  | 6 => 1134
  | 5 => 6283
  | 4 => 3769
  | 3 => 271
  | 2 => 33
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*5) 5
  | 7 => packedAt gbK7 (i*16) 16
  | 6 => packedAt gbK6 (i*27) 27
  | 5 => packedAt gbK5 (i*38) 38
  | 4 => packedAt gbK4 (i*49) 49
  | 3 => packedAt gbK3 (i*60) 60
  | 2 => packedAt gbK2 (i*71) 71
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (6+((h/1+packedAt gbK8 (5+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (548+((h/14+packedAt gbK7 (464+(h % 14)*6) 6) % 56)*6) 6
  | 6 => packedAt gbK6 (36846+((h/519+packedAt gbK6 (30618+(h % 519)*12) 12) % 2489)*12) 12
  | 5 => packedAt gbK5 (274818+((h/2576+packedAt gbK5 (238754+(h % 2576)*14) 14) % 10201)*14) 14
  | 4 => packedAt gbK4 (203349+((h/1436+packedAt gbK4 (184681+(h % 1436)*13) 13) % 5171)*13) 13
  | 3 => packedAt gbK3 (17187+((h/103+packedAt gbK3 (16260+(h % 103)*9) 9) % 374)*10) 10
  | 2 => packedAt gbK2 (2415+((h/12+packedAt gbK2 (2343+(h % 12)*6) 6) % 53)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffffffff80ffffc0ffffffffff80ffc7ffe3f
  | 1 => 0xc07f01fffffffffff03f03f03fffffff911fff
  | 2 => 0x7ffe03fff01fffffc003ffc1fff07fe1e3c7
  | 3 => 0xff800003ffffe03ffffffc0001ffff83fe03f8
  | 4 => 0xfffffffc0000003ffffffffffe000003fffc00
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4309142808e2448402cb14b1425884a4266e1b
  | 1 => 0x95224c5191248918b015415434ab19499114ed
  | 2 => 0x2a4c289aa241d22d5540926d9135a472e1a346
  | 3 => 0xc68b163448903b669a6d80921c6ce237a03b0
  | 4 => 0x3070c183870e1c3b8e38e38e38070843ddd800
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xeaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880eaa8c880, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_36709
namespace PEqualNP.Outside.L_meta_36709
open PEqualNP.Outside.L_meta_36709.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_32 : Interval gbAtlas 2 32 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 33 := (concat bgb_2_0 bgb_2_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_128 : Interval gbAtlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_160 : Interval gbAtlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_192 : Interval gbAtlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_224 : Interval gbAtlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_256 : Interval gbAtlas 3 256 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 271 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 bgb_3_96)) (concat (concat bgb_3_128 bgb_3_160) (concat bgb_3_192 (concat bgb_3_224 bgb_3_256))))
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
theorem bgb_4_224 : Interval gbAtlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_256 : Interval gbAtlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_288 : Interval gbAtlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_320 : Interval gbAtlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_352 : Interval gbAtlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_384 : Interval gbAtlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_416 : Interval gbAtlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_448 : Interval gbAtlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_480 : Interval gbAtlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_512 : Interval gbAtlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_544 : Interval gbAtlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_576 : Interval gbAtlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_608 : Interval gbAtlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_640 : Interval gbAtlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_672 : Interval gbAtlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_704 : Interval gbAtlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_736 : Interval gbAtlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_768 : Interval gbAtlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_800 : Interval gbAtlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_832 : Interval gbAtlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_864 : Interval gbAtlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_896 : Interval gbAtlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_928 : Interval gbAtlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_960 : Interval gbAtlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_992 : Interval gbAtlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1024 : Interval gbAtlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1056 : Interval gbAtlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1088 : Interval gbAtlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1120 : Interval gbAtlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1152 : Interval gbAtlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1184 : Interval gbAtlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1216 : Interval gbAtlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1248 : Interval gbAtlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1280 : Interval gbAtlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1312 : Interval gbAtlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1344 : Interval gbAtlas 4 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1376 : Interval gbAtlas 4 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1408 : Interval gbAtlas 4 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1440 : Interval gbAtlas 4 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1472 : Interval gbAtlas 4 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1504 : Interval gbAtlas 4 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1536 : Interval gbAtlas 4 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1568 : Interval gbAtlas 4 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1600 : Interval gbAtlas 4 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1632 : Interval gbAtlas 4 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1664 : Interval gbAtlas 4 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1696 : Interval gbAtlas 4 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1728 : Interval gbAtlas 4 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1760 : Interval gbAtlas 4 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1792 : Interval gbAtlas 4 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1824 : Interval gbAtlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1856 : Interval gbAtlas 4 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1888 : Interval gbAtlas 4 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1920 : Interval gbAtlas 4 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1952 : Interval gbAtlas 4 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1984 : Interval gbAtlas 4 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2016 : Interval gbAtlas 4 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2048 : Interval gbAtlas 4 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2080 : Interval gbAtlas 4 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2112 : Interval gbAtlas 4 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2144 : Interval gbAtlas 4 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2176 : Interval gbAtlas 4 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2208 : Interval gbAtlas 4 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2240 : Interval gbAtlas 4 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2272 : Interval gbAtlas 4 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2304 : Interval gbAtlas 4 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2336 : Interval gbAtlas 4 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2368 : Interval gbAtlas 4 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2400 : Interval gbAtlas 4 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2432 : Interval gbAtlas 4 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2464 : Interval gbAtlas 4 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2496 : Interval gbAtlas 4 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2528 : Interval gbAtlas 4 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2560 : Interval gbAtlas 4 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2592 : Interval gbAtlas 4 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2624 : Interval gbAtlas 4 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2656 : Interval gbAtlas 4 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2688 : Interval gbAtlas 4 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2720 : Interval gbAtlas 4 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2752 : Interval gbAtlas 4 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2784 : Interval gbAtlas 4 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2816 : Interval gbAtlas 4 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2848 : Interval gbAtlas 4 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2880 : Interval gbAtlas 4 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2912 : Interval gbAtlas 4 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2944 : Interval gbAtlas 4 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2976 : Interval gbAtlas 4 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3008 : Interval gbAtlas 4 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3040 : Interval gbAtlas 4 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3072 : Interval gbAtlas 4 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3104 : Interval gbAtlas 4 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3136 : Interval gbAtlas 4 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3168 : Interval gbAtlas 4 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3200 : Interval gbAtlas 4 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3232 : Interval gbAtlas 4 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3264 : Interval gbAtlas 4 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3296 : Interval gbAtlas 4 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3328 : Interval gbAtlas 4 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3360 : Interval gbAtlas 4 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3392 : Interval gbAtlas 4 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3424 : Interval gbAtlas 4 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3456 : Interval gbAtlas 4 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3488 : Interval gbAtlas 4 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3520 : Interval gbAtlas 4 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3552 : Interval gbAtlas 4 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3584 : Interval gbAtlas 4 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3616 : Interval gbAtlas 4 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3648 : Interval gbAtlas 4 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3680 : Interval gbAtlas 4 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3712 : Interval gbAtlas 4 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3744 : Interval gbAtlas 4 3744 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3769 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)) (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 bgb_4_416)))) (concat (concat (concat bgb_4_448 (concat bgb_4_480 bgb_4_512)) (concat (concat bgb_4_544 bgb_4_576) (concat bgb_4_608 bgb_4_640))) (concat (concat (concat bgb_4_672 bgb_4_704) (concat bgb_4_736 bgb_4_768)) (concat (concat bgb_4_800 bgb_4_832) (concat bgb_4_864 bgb_4_896))))) (concat (concat (concat (concat bgb_4_928 (concat bgb_4_960 bgb_4_992)) (concat (concat bgb_4_1024 bgb_4_1056) (concat bgb_4_1088 bgb_4_1120))) (concat (concat (concat bgb_4_1152 bgb_4_1184) (concat bgb_4_1216 bgb_4_1248)) (concat (concat bgb_4_1280 bgb_4_1312) (concat bgb_4_1344 bgb_4_1376)))) (concat (concat (concat bgb_4_1408 (concat bgb_4_1440 bgb_4_1472)) (concat (concat bgb_4_1504 bgb_4_1536) (concat bgb_4_1568 bgb_4_1600))) (concat (concat (concat bgb_4_1632 bgb_4_1664) (concat bgb_4_1696 bgb_4_1728)) (concat (concat bgb_4_1760 bgb_4_1792) (concat bgb_4_1824 bgb_4_1856)))))) (concat (concat (concat (concat (concat bgb_4_1888 (concat bgb_4_1920 bgb_4_1952)) (concat (concat bgb_4_1984 bgb_4_2016) (concat bgb_4_2048 bgb_4_2080))) (concat (concat bgb_4_2112 (concat bgb_4_2144 bgb_4_2176)) (concat (concat bgb_4_2208 bgb_4_2240) (concat bgb_4_2272 bgb_4_2304)))) (concat (concat (concat bgb_4_2336 (concat bgb_4_2368 bgb_4_2400)) (concat (concat bgb_4_2432 bgb_4_2464) (concat bgb_4_2496 bgb_4_2528))) (concat (concat (concat bgb_4_2560 bgb_4_2592) (concat bgb_4_2624 bgb_4_2656)) (concat (concat bgb_4_2688 bgb_4_2720) (concat bgb_4_2752 bgb_4_2784))))) (concat (concat (concat (concat bgb_4_2816 (concat bgb_4_2848 bgb_4_2880)) (concat (concat bgb_4_2912 bgb_4_2944) (concat bgb_4_2976 bgb_4_3008))) (concat (concat (concat bgb_4_3040 bgb_4_3072) (concat bgb_4_3104 bgb_4_3136)) (concat (concat bgb_4_3168 bgb_4_3200) (concat bgb_4_3232 bgb_4_3264)))) (concat (concat (concat bgb_4_3296 (concat bgb_4_3328 bgb_4_3360)) (concat (concat bgb_4_3392 bgb_4_3424) (concat bgb_4_3456 bgb_4_3488))) (concat (concat (concat bgb_4_3520 bgb_4_3552) (concat bgb_4_3584 bgb_4_3616)) (concat (concat bgb_4_3648 bgb_4_3680) (concat bgb_4_3712 bgb_4_3744)))))))
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
theorem bgb_5_3648 : Interval gbAtlas 5 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3680 : Interval gbAtlas 5 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3712 : Interval gbAtlas 5 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3744 : Interval gbAtlas 5 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3776 : Interval gbAtlas 5 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3808 : Interval gbAtlas 5 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3840 : Interval gbAtlas 5 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3872 : Interval gbAtlas 5 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3904 : Interval gbAtlas 5 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3936 : Interval gbAtlas 5 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_3968 : Interval gbAtlas 5 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4000 : Interval gbAtlas 5 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4032 : Interval gbAtlas 5 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4064 : Interval gbAtlas 5 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4096 : Interval gbAtlas 5 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4128 : Interval gbAtlas 5 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4160 : Interval gbAtlas 5 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4192 : Interval gbAtlas 5 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4224 : Interval gbAtlas 5 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4256 : Interval gbAtlas 5 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4288 : Interval gbAtlas 5 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4320 : Interval gbAtlas 5 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4352 : Interval gbAtlas 5 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4384 : Interval gbAtlas 5 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4416 : Interval gbAtlas 5 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4448 : Interval gbAtlas 5 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4480 : Interval gbAtlas 5 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4512 : Interval gbAtlas 5 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4544 : Interval gbAtlas 5 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4576 : Interval gbAtlas 5 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4608 : Interval gbAtlas 5 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4640 : Interval gbAtlas 5 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4672 : Interval gbAtlas 5 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4704 : Interval gbAtlas 5 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4736 : Interval gbAtlas 5 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4768 : Interval gbAtlas 5 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4800 : Interval gbAtlas 5 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4832 : Interval gbAtlas 5 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4864 : Interval gbAtlas 5 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4896 : Interval gbAtlas 5 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4928 : Interval gbAtlas 5 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4960 : Interval gbAtlas 5 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4992 : Interval gbAtlas 5 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5024 : Interval gbAtlas 5 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5056 : Interval gbAtlas 5 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5088 : Interval gbAtlas 5 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5120 : Interval gbAtlas 5 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5152 : Interval gbAtlas 5 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5184 : Interval gbAtlas 5 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5216 : Interval gbAtlas 5 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5248 : Interval gbAtlas 5 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5280 : Interval gbAtlas 5 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5312 : Interval gbAtlas 5 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5344 : Interval gbAtlas 5 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5376 : Interval gbAtlas 5 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5408 : Interval gbAtlas 5 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5440 : Interval gbAtlas 5 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5472 : Interval gbAtlas 5 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5504 : Interval gbAtlas 5 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5536 : Interval gbAtlas 5 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5568 : Interval gbAtlas 5 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5600 : Interval gbAtlas 5 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5632 : Interval gbAtlas 5 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5664 : Interval gbAtlas 5 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5696 : Interval gbAtlas 5 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5728 : Interval gbAtlas 5 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5760 : Interval gbAtlas 5 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5792 : Interval gbAtlas 5 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5824 : Interval gbAtlas 5 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5856 : Interval gbAtlas 5 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5888 : Interval gbAtlas 5 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5920 : Interval gbAtlas 5 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5952 : Interval gbAtlas 5 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5984 : Interval gbAtlas 5 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6016 : Interval gbAtlas 5 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6048 : Interval gbAtlas 5 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6080 : Interval gbAtlas 5 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6112 : Interval gbAtlas 5 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6144 : Interval gbAtlas 5 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6176 : Interval gbAtlas 5 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6208 : Interval gbAtlas 5 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6240 : Interval gbAtlas 5 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6272 : Interval gbAtlas 5 6272 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 6283 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))))) (concat (concat (concat (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928))) (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)) (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312))) (concat (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)))))) (concat (concat (concat (concat (concat bgb_5_1568 (concat bgb_5_1600 bgb_5_1632)) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824)) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920)))) (concat (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))) (concat (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304))))) (concat (concat (concat (concat bgb_5_2336 (concat bgb_5_2368 bgb_5_2400)) (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496))) (concat (concat bgb_5_2528 (concat bgb_5_2560 bgb_5_2592)) (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688)))) (concat (concat (concat bgb_5_2720 (concat bgb_5_2752 bgb_5_2784)) (concat bgb_5_2816 (concat bgb_5_2848 bgb_5_2880))) (concat (concat bgb_5_2912 (concat bgb_5_2944 bgb_5_2976)) (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 bgb_5_3104))))))) (concat (concat (concat (concat (concat (concat bgb_5_3136 (concat bgb_5_3168 bgb_5_3200)) (concat bgb_5_3232 (concat bgb_5_3264 bgb_5_3296))) (concat (concat bgb_5_3328 (concat bgb_5_3360 bgb_5_3392)) (concat bgb_5_3424 (concat bgb_5_3456 bgb_5_3488)))) (concat (concat (concat bgb_5_3520 (concat bgb_5_3552 bgb_5_3584)) (concat bgb_5_3616 (concat bgb_5_3648 bgb_5_3680))) (concat (concat bgb_5_3712 (concat bgb_5_3744 bgb_5_3776)) (concat bgb_5_3808 (concat bgb_5_3840 bgb_5_3872))))) (concat (concat (concat (concat bgb_5_3904 (concat bgb_5_3936 bgb_5_3968)) (concat bgb_5_4000 (concat bgb_5_4032 bgb_5_4064))) (concat (concat bgb_5_4096 (concat bgb_5_4128 bgb_5_4160)) (concat bgb_5_4192 (concat bgb_5_4224 bgb_5_4256)))) (concat (concat (concat bgb_5_4288 (concat bgb_5_4320 bgb_5_4352)) (concat bgb_5_4384 (concat bgb_5_4416 bgb_5_4448))) (concat (concat bgb_5_4480 (concat bgb_5_4512 bgb_5_4544)) (concat (concat bgb_5_4576 bgb_5_4608) (concat bgb_5_4640 bgb_5_4672)))))) (concat (concat (concat (concat (concat bgb_5_4704 (concat bgb_5_4736 bgb_5_4768)) (concat bgb_5_4800 (concat bgb_5_4832 bgb_5_4864))) (concat (concat bgb_5_4896 (concat bgb_5_4928 bgb_5_4960)) (concat bgb_5_4992 (concat bgb_5_5024 bgb_5_5056)))) (concat (concat (concat bgb_5_5088 (concat bgb_5_5120 bgb_5_5152)) (concat bgb_5_5184 (concat bgb_5_5216 bgb_5_5248))) (concat (concat bgb_5_5280 (concat bgb_5_5312 bgb_5_5344)) (concat (concat bgb_5_5376 bgb_5_5408) (concat bgb_5_5440 bgb_5_5472))))) (concat (concat (concat (concat bgb_5_5504 (concat bgb_5_5536 bgb_5_5568)) (concat bgb_5_5600 (concat bgb_5_5632 bgb_5_5664))) (concat (concat bgb_5_5696 (concat bgb_5_5728 bgb_5_5760)) (concat bgb_5_5792 (concat bgb_5_5824 bgb_5_5856)))) (concat (concat (concat bgb_5_5888 (concat bgb_5_5920 bgb_5_5952)) (concat bgb_5_5984 (concat bgb_5_6016 bgb_5_6048))) (concat (concat bgb_5_6080 (concat bgb_5_6112 bgb_5_6144)) (concat (concat bgb_5_6176 bgb_5_6208) (concat bgb_5_6240 bgb_5_6272))))))))
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
theorem bgb_6_1120 : Interval gbAtlas 6 1120 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1134 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 29 := bgb_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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

theorem boundgb (cert : Complete gbAtlas) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 5 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xeeeeeeeeeaa8c880eeeeeeeeeaa8c880eeeeeeeeeaa8c880eeeeeeeeeaa8c880eeeeeeeeeaa8c880eeeeeeeeeaa8c880eeeeeeeeeaa8c880eeeeeeeeeaa8c880
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372968 * 2 ^ 32 + 3974686944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36709.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.and,[0,5]⟩,⟨.or,[2,7]⟩,⟨.and,[3,4]⟩,⟨.or,[8,9]⟩,⟨.and,[1,10]⟩,⟨.or,[4,6]⟩,⟨.or,[1,8]⟩,⟨.and,[0,12]⟩,⟨.and,[13,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3974686944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3974686944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36709

open PEqualNP.Outside.L_meta_36709 in
theorem PEqualNP.Outside.L_meta_36709 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 3974686944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 3974686944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
