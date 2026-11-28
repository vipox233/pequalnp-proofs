import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36721.Model
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


end PEqualNP.Outside.L_meta_36721.Model

namespace PEqualNP.Outside.L_meta_36721
open PEqualNP.Outside.L_meta_36721.Model
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

def SBf (j : Nat) : Nat := [6, 4, 6, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_36721

namespace PEqualNP.Outside.L_meta_36721
open PEqualNP.Outside.L_meta_36721.Model
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
end PEqualNP.Outside.L_meta_36721
namespace PEqualNP.Outside.L_meta_36721
open PEqualNP.Outside.L_meta_36721.Model
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
end PEqualNP.Outside.L_meta_36721
namespace PEqualNP.Outside.L_meta_36721
open PEqualNP.Outside.L_meta_36721.Model
def s2K5 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xa714aa67ac10062218e5a402e00042020001a4a83021882006006fe65f8cbe997c32fe63f8c7e98fc31fe43f887e90fc21fe61f8c3e987c30fe41f883e907c20fe21f843e887c10
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0xe08400401b227ca802e840000a507093c9458c068cc003a18ca400691131a48b0a0098110000038f080404530030c059718002d90732b541ccad90632b5418cb34c832ae42cc6b50b31ae428c6b50a31d5310c6790f219d43c86790e219d43887948421af424c2b10930b7414c2d10530ae420c2b50830b6410c2d504309f43482710d20b741482d105209e43082750c20b641082d504209f43442710d10af42442b109109e43042750c10ae42042b50810
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 24
  | 3 => 39
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*4) 4
  | 4 => packedAt s2K4 (i*15) 15
  | 3 => packedAt s2K3 (i*26) 26
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (5+((h/1+packedAt s2K5 (4+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (400+((h/8+packedAt s2K4 (360+(h % 8)*5) 5) % 29)*6) 6
  | 3 => packedAt s2K3 (1092+((h/13+packedAt s2K3 (1014+(h % 13)*6) 6) % 47)*7) 7
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbff7fffe3ffff1ff
  | 1 => 0xffffffffffffffffffffffd5f8e73fc71c7e93
  | 3 => 0xe6ff07cff81f8f1c
  | 4 => 0xf8fff80fffe00fe0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4010000009040025
  | 1 => 0x2a264a4642496692
  | 3 => 0x1942d41a90932b18
  | 4 => 0x78486ad24c24dc0
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 27 s2Pos s2Neg, 0xeeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88eeaaaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36721
namespace PEqualNP.Outside.L_meta_36721
open PEqualNP.Outside.L_meta_36721.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x130a009c000288800000780290c000070690021226c797186000d002c002006472b26680042080e80388d4150000025000001f2c4800012a8400020028005040000100181810418080ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x49464760040ac008c467c00220000480026200000287256428a0000301eb22e506070864a00001600849206002ab0546aa40c083e7e002c000e9e0034a890960012106c00360000884c4e984400003c787a3874581c9c00020000a600001a802400a09a660aaa5e68005c6e5a6218aea25232823a8e140e0c98706000000e18081020000702141810a042851000383001a7ca5a1cf55243b7a92876c5250f3ea6a1ebd49439e29287ac5250e58a4a1cf950439ea9c853e5290abca6215754c42cf298853d5310b3aa6214754c429f29085ae5210a7ca9994f55332cea1e65ac42ccaeca3995d547329faa4653c548ca7ea8994f15132cea1a653e540ca7aa8196b10832b7a92836c52506bca620d754c419f2a6633d54cc73a8798db94b31b6a96639d434c67ca818cf550319f2a4433d54886bca710d754e21d6214433f5448678a890eb10821af29e815d53d02dca5205b54a409f2a6613d54cc33a87184f950309eaa0619d430c2dca4185b54830bb2886175510c35885904f952209eaa4413f5448278a89057d4d20ae29a41ac42482eea2905d145209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x1c49a30293002678040000000aa0000001600000400002e380888180b00818000500000a82242041000030c6254c42a318943cca8d6310b32c910a51ccb15435473287195434ca2d6510832a318943cc70d4354b31a3189434c62c6255031a358c428870e5310a218758c544868d63108218b18954cc28c6250e30a3189430c30d4354830c550d510c28d6310b208758e548828d6310920c314c42483244214520
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x4008062a8282b988528e65411c9435473281aed2988510d047250d510c206bb0a621241415cc4214520
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
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (802+((h/14+packedAt s3K5 (704+(h % 14)*7) 7) % 69)*7) 7
  | 4 => packedAt s3K4 (2640+((h/30+packedAt s3K4 (2430+(h % 30)*7) 7) % 119)*8) 8
  | 3 => packedAt s3K3 (998+((h/8+packedAt s3K3 (950+(h % 8)*6) 6) % 48)*6) 6
  | 2 => packedAt s3K2 (300+((h/2+packedAt s3K2 (294+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffff83fffffff03ffff83ffc1fffffcf1f1ff
  | 1 => 0xf07fffc0fe0ffffc1e0ffc3ffe1e07ff4e3e4f
  | 2 => 0xff81ffff000fc3ffe00fffc3ffe007038fcf8c
  | 4 => 0x1fffffff003fffff00003fffff803f00ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x2004088824020000a41280444022914810d095
  | 1 => 0x451891064894a12c0a852429921422b146264a
  | 2 => 0xa32d22921d2906556109ca82e540541a8b4b8c
  | 4 => 0xca51c4249181ab9a53a0622339996023e00d60
  | 5 => 0xc618738e1ce33e39dce7330311180c3fdb000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaea8888eaeae8e8eaea8888eaeae8e8eaea8888eaeae8e8eaea8888eaeae8e8eaea8888eaeae8e8eaea8888eaeae8e8eaea8888eaeae8e8eaea8888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36721
namespace PEqualNP.Outside.L_meta_36721
open PEqualNP.Outside.L_meta_36721.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0xa2e74027001091e26680005400025000000000000000001180440000000000001200000001d080006000c00000012a005960018008367c00556a00111a387800098a000040019488010338014838202001020e0000a1000003ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x25400349c322624200c48503c90449e7ca200048a1a36a8944c64086c16708618ac687e4e52822eb0001298107800662200580e3e4a3a0aa67a5e928406289a462a1c1e008800000000ae8c00aa8e006274000096000000000060a4806a38a05c426e5a40b22c5600727614300a002000204c8000094100a3470000146800048f17080070616327ca5a1cf55243b7a92876c5250f3ea6a1ebd49439e29287ac5250e58a4a1cf950439ea9c853e5290abca6215754c42cf298853d5310b3aa6214754c429f29085ae5210a7ca9994f55332cea1e65ac42ccaeca3995d547329faa4653c548ca7ea8994f15132cea1a653e540ca7aa8196b10832b7a92836c52506bca620d754c419f2a6633d54cc73a8798db94b31b6a96639d434c67ca818cf550319f2a4433d54886bca710d754e21d6214433f5448678a890eb10821af29e815d53d02dca5205b54a409f2a6613d54cc33a87184f950309eaa0619d430c2dca4185b54830bb2886175510c35885904f952209eaa4413f5448278a89057d4d20ae29a41ac42482eea2905d145209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x18a0180004800003804020000002260000000246a2a0000000000000402c58002001ca8000003000cb9401e00000000000000000000000080020000008030c6254c42a318943cca8d6310b32c910a51ccb15435473287195434ca2d6510832a318943cc70d4354b31a3189434c62c6255031a358c428870e5310a218758c544868d63108218b18954cc28c6250e30a3189430c30d4354830c550d510c28d6310b208758e548828d6310920c314c42483244214520
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x22801800080104282b988528e65411c9435473281aed2988510d047250d510c206bb0a621241415cc4214520
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
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (802+((h/14+packedAt s4K5 (704+(h % 14)*7) 7) % 90)*7) 7
  | 4 => packedAt s4K4 (2640+((h/30+packedAt s4K4 (2430+(h % 30)*7) 7) % 109)*8) 8
  | 3 => packedAt s4K3 (1006+((h/8+packedAt s4K3 (950+(h % 8)*7) 7) % 74)*6) 6
  | 2 => packedAt s4K2 (302+((h/2+packedAt s4K2 (294+(h % 2)*4) 4) % 15)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffff83fffffff03ffff83ffc1fffffcf1f1ff
  | 1 => 0xf07fffc0fe0ffffc1e0ffc3ffe1e07ff4e3e4f
  | 2 => 0xff81ffff000fc3ffe00fffc3ffe007038fcf8c
  | 3 => 0x1fffffff003fffff00003fffff803f00ff0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x2004088824020000a41280444022914810d095
  | 1 => 0x451891064894a12c0a852429921422b146264a
  | 2 => 0xa32d22921d2906556109ca82e540541a8b4b8c
  | 3 => 0xca51c4249181ab9a53a0622339996023e00d60
  | 5 => 0xc618738e1ce33e39dce7330311180c3fdb000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeae8eae8ea88ea88eae8eae8ea88ea88eae8eae8ea88ea88eae8eae8ea88ea88eae8eae8ea88ea88eae8eae8ea88ea88eae8eae8ea88ea88eae8eae8ea88ea88, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36721
namespace PEqualNP.Outside.L_meta_36721
open PEqualNP.Outside.L_meta_36721.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x440100c12a0d10060008f00600212820699381d382004c9292c10eaa4c00f174694a910c2802b482c280007cd8e000c001d04304704a000040ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21ee21fd21fc21ec21ff40fe40fd40fc40ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa617c514c3be6298774c530f710a61ec214c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c3dca4185b94830bea9061ed520c2daa4185f94430fb2886176510c2faa2187d54430baa8861de310c3b862187b88430f6108617e500c3be60187e8c030ee98061f9300c2fea9905f95320beaa6417c54c82fea7905f94f20bea9e417c53c83de85907b90b20f6a1641ec42c83de65907b8cb20f699641ec32c82fca3905f54720f790e41ee21c83da43907b08720f7aa641ee54c83daa9907b15320f7a9e41ee53c83daa7907b14f20f7a1e41ee43c83da87907b10f20f7a8e41ee51c82dca3907b54720f628e41ef41c83dc83907b50720f620e41ef31c83dc63907b4c720f618e41ef40c83dc81907b50320f620641ef30c83dc61907b4c320f6186417f54882fca9105f55220be2a4417f53882fca7105f54e20be29c417d52882daa5105f94620bea8c41ee21883d843105f94220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c53483de84907b90920f6a1241ec42483de64907b8c920f699241ec32482fea2905f14520f790a41ee21483da42907b08520fd90241ee20483dea8907b95120f6aa241ec54483dea6907b94d20f6a9a41ec53483de86907b90d20f6a1a41ec43483dea2907b94520f6a8a41ec51482d8a2907bd0520f720a41ed41483d882907bcc520f718a41ed31483d862907bd4120f5a8241ef40483dc80907b50120f620241ef30483dc60907b4c120f6182417f54082fca8105f55020be2a0417f53082fca6105f54c20be298417e52082dca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa9621ef52c42dea5885f94b10bea96217c52c43d8a5885b14b10fb20e21f541c43ec63887d4c710f710e21ec21c43de41887b48310bfaa4217e54842faa9085f15210bfa9c217e53842faa7085f14e10bfa94217e52843dca5085b94a10bea9421ed52842daa5085f14a10bea8c21ee21843d843085f94210f790421ed20843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb20a21f541443ec62887d4c510f710a21ec21443de40887b48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2087b88410f6108217e50043de40087b48010fb88021fa10043ea20087e44010
  | 1 => 0xe511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331bf29663ee52cc6dca598df54b31f6a96636d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63de438c7ba8718df94a31bea94637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c6fea498fbd4931b7a92637c524c7d8a498db14931fb98a63de314c6fea098df14131bfaa0637e540c6faa818df15031bf29863de430c7ba8618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f721443ed42887d88510fbcca21f719443ed32887d86510df94621f790c43f721886fca110df54221f7aa443ee54887daa910fb15221f7a9c43ee53887daa710fb14e21f7a1c43ee43887da8710fb10e21b728c43ef41887dc8310fb50621f620c43ef31887dc6310fb4c621f618c43ef50887dca110fb54221b6a8443ec50886fea890df95121beaa2437c54486fea690df94d21bea9a437c53487ee4290fb88521bfa82437c50486fea810df95021beaa0437c54086fea610df94c21bea98437c53086fca410fbd0821f721043ed42087d88410fbcc821f719043ed32087d86410df94421f790843f621087da4210fd48421bf280437d50087dea810fb95021f6aa043ec54087dea610fb94c21f6a9843ec53087de8610fb90c21f6a1843ec43087dca210db94421f328843ef41087dc8210fb50421f620843ef31087dc6210fb4c421f618843ef50087dca010fb54021b6a8043ec50086fca7a05f54f40dfa1e81bd43d02fca5a05f54b40bf28e817d51d037e83a06f50740f710e81ec21d02faa9205f94e40bea9c817e52903dca5205b94a40bea9481ed52902daa5205f94640bea8c81be419037883207b88640f610c817e509037e81207ed0240bfa9a817c535037e86a06f50d40bfa92817c52502fea2a05f14540dfa0a81bd41503dc42a07b08540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea98817e52103dca4205b94840bea9081ed52102daa4205f94440fb288817651102faa2207d54440baa8881be411037882207b88440f6108817e501037e80207e90040dea0081f940102fea9985f95330beaa6617c54cc3bc87987750f30bf296617d52cc2fca3985f54730ef98e61dd31cc3dc43987b08730bfaa4617e548c2faa9185f15230bea9c617e528c3dca5185b94a30bea9461ed528c2daa5185f94630bea8c61de318c3b863187b88630f610c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130ef21a61dd434c2fea4985f14930bfa8
  | 2 => 0x10010010000000008008008000000018008000000000000000000008000000000018000000018008000000000008018000000000010010000028000018008000000000000000010008000000000000010000008010000000010010000008000000000000028000000008008010000000000008060010008030000008008000018000000000000018010008008000000030000000008008020058000008010000000000000008000000008000000000000000000000000008000020000000000018000000000000008000000000008000018000000000018000008000010000000000000010000000000000000000018000010000008008000010010000000000000000000000000000020008008010008028010000068020000008000000000000008028000018010000000008000010000010010008000000000018000028000010008028000000000000000000010000000000000000000008000008000000000000008008058028000000028008005f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250fdea4a1dbd4943be29287ec5250ed8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85bd4350bde84a16f90942bfa8a857c5150afea0a15f14142bf2a0857e5310bbca6215794c42bea9885dd5310abaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccbde85997b10b32bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c657e528cbdc85197b50a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbc86997750d32f721265ed424cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf298657e520cbde84197b10832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d06fca5a0fb94b41b7296837d52d07daa5a0db54b41bf286837d50d06faa920df94e41bea9c83bf439077a8720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41bfa9283ef52506dea4a0df14941f6292836c52507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077a8620df94841bea90837
  | 3 => 0x809610000000017200051a0011b266000001878d554c0e8e22c73360000030a2f01cc5380000000012800000000552950000000001e5d6000000a0122af40000000000000000000068000000001c4002f100000000000018000000ee0000d8fb9c9000000000000004b4000000a0000000000008611500018072c000000008e000000178000e0087000000000000001785a8002fcbed780000000014d8006180000026900030c0012400000126800000904750db46600000000000000000b9464a096a80030c818002ed0000001587f000000000000000018980000085000000000000001510006fc0022e48c000000000004b8760000000000030d000000000d3000000000000003f5242232de0000010600000000000000000000000000000000000000000000190001088000000011ca5b02e000e38003ba404c6a6528cb3c4989c00000169842000000002340000000000063e000b0000000b9c378005ca2ac38308000000000000006f89f9e30000015480038c8ac0000000000000000000000000002ceacd460000005400300055e800000000000000000000000000000000000bab1d242674990003ae000000000002a42c00019a0006e9fb00000007000008a187895d0007b80001353c000000000000001a869000b6400000000000988003184b18c8f817c0a8e90000da000000000000b400000000988a5800000c2c0025710800000000000a0c000001f2000738000000000000011a0013f04a000570d891c32e0000029f000000002a00dc221600053be4316c19935e984e50000000000000000000000000000000000000000000000000000000000000000000bb000000000002ec25400000000000f828121c00000000000b98000000000000004b4d0b2c0001d00000000000000008000001b20000000000000000000000000002c5000000260000001b0290000003513900007c0000000020800000000000000000000640000014a2be5f17484d0000017e800000000eb00060ac38000000001146f8000000012791a42c001831a51448d40000017e00000000000610000000f00009e0a50000015930304e0011f0005921a8002db000000000004960003a800000000002be0140012b000000000000280002bce780000000097800000000000000006b80023c4f4a9481000000000678000000009d000106000000000000008aa1752e000000003b80000000026a53d6b22d3480000019122663c00000000001090000000012e000000af0100c64f2b5c00000092000000000ee000f90003ce00000000000000001963f8000e98f7000b817b80000025c000000000000000000087800000000000001410000000000000000000000000000000000008038000008020000030000020000000008000000028000028008000000000
  | 4 => 0x7f1092660000000000013895290000001541ed420000208004ea4000000063ca68000004dead800000412000200000ba001568002ee9ecb59ab0000000000000000000000000000000003f200000000216000000004480000025100040c000b4000001608000000000000044e00164000000a840000003eae80000000000000000000000220651a40000016d3f000000000000000000000000013e27d000960598001840d0000680007e800000244001770000000006500063676100800000000000000580000000000000000000000000000005e4ab031b071f84647900019c000002b000000000000000000000000006f4000790000016f8000007a80000031600000000000000e191f4c80000016400000000000000c44000fb3fa8bc0023b000000002f423a00000000000000001ec0001f800000000000002de0000000000059c00000000488a645726c480000000000009dd4e80000000000000000001778000000005bb040005cc00000000000000000005a8000230000000031c0000010e800000001688000cc6b4000000620017a8001a0a900014d00000000198000000000006342a000000030794000000005d0520000000000028e00000000120000be5558f63708b0109db0006f0000000008640018e4e616c000000006c02c8ff000001669fe48650800000000000000000001896e08b3e65a00000000003c0000000000000000000a2cf0a7102859898000000ad4c900000000000000000414001950000005880038200000000000000001c50000014501200056cf880000000000000000000000000000000000000000000182000a9c1497f5d000000000000001681aa3d067c9c9a03422606b80044200000000000b854e189228000000005264a518280414bfc04ab800085400000624b4800000000000000000000000003b000000001ac000c080000033c000000cc2f2000000001e05ec0000008c0005623f00000000000000b100000000000047000002000002a210499c00000070001148c700088071127600814ce32000000000255000000000000000000000040e0b8001440000016600000055400000000000a609e0007d05305f0e846d188000000015180011e00000000000000d181b000a580010800011c000601e82000000000032c00000000000000000000006d067000000001ef21a45c000000780000000000000000000000c5c001b50008f42180056e000000000000000000000087000000000000000001d00013a0e434c28c0000048e0000000000000039000000b1844800000000000000000000000000009112a533660016a0e6000000002500000010180049cc251b98a000c6130033000834000e50009500000056800000000000aec000000000000000000087c001a800000000000000a60000000000000
  | 5 => 0x30122000000000364214001ba408000e893700000000010494000001260006500000000054c00000000001110000d60000000b2d82680000020e0010409b000514000001c24d0ab2f800000000000000b740011851e79137000000000c980000000142800000000000000004580000056200000000000768568b223c000000000600000005700000000000000560e100027a0009d800000000000002ca00060970000098e70000900f50580000000000000000000f49630aa250aa25a26c79800000000000000000a23cc4c8000000000000000000000000000000000000005c400000000000002635944287d00012c000000f5000000000810000000007c000000a70002bc0000026d00000000016000964b9000000764918000005a400000000314001471dac4027800000898001b434e000000de000000001f52f49e0040000000017e000000520d10000a6000000000009d80008a36e0000000000000000000000000000e000000124a8900000000000000000b091121e00157076000b0c30a6b12072000000000000000000000004313e0006217980000000064a880000000007b0007780a800000000001cc000a44002bf2569145080000000000000000000000000000000028700055c001bb2b20006b000000000000004362e800000000000f5a0c0000001ba5d000000000004fe0000023a17a0004faaa30200000000006000c2839000500ea800188ae400000000001422940fa6e4000000000000014339a000a90560003aca485a48400068a6a352b68490000008a109b160000000001100000000000300000002e25fc000000e30009302a0000000000001900000000000000190002f60000000008c01a3a4b709d3ec000ad1120000018a000000000002fa000000000002500000000000007000252000000000003061e8be8000000012f0000006685b0000007fc038dc0006d80000000000000000000001718b84349c0b10000000000000000049400000000000000000b87898a800000ba8e800000097c778003a883c6c0000000000029200008800000000000c8000000000002ec000000000001600fc9c1870000000002f000000000000007800020e00000
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x31482e9600c5209b996404826e6510120b398c40482cd6310120b998440482e561101209b996304826e650c120ab99030482ad640c120b998430482e5610c1209b98b540825e63150209758c540826e62150209d984540827561150209b98b530823e6414c208f590530826e6214c209d98453082756114c209b596210836651084209bd95200827b6548020da949200825e63953109758e54c426e62953109b58a54c426f62553109b18954c423e6494f108f59253c426e6294f109b58a53c426f6254f109b18953c436661d4b10da58352c43666114b10da58052c42e96088710ba58021c42e661c8310b918520c426e62d52109b58b548425e63152109758c548426e62152109b588548426e62d4e109b58b538423e6414e108f590538426e6214e109b588538423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f99454443356115110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d10d5584534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109b994524432f5414910cb150524434f5314910d314c524426e61149109b184524433454905109d1954144354538c5109d195314426e6588510cbd52214432c5488510d3d4e214434c53885109b994214432f5408510cb150214434f5308510d314c214426e65c8110cbd53204432c54c8110d3d4f204434c53c8110b9987204426c6548110cbd51204432c5448110d3d4d204434c5348110b9185204425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540427661150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c109d984530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d53548109bd81520426d60548108f990520423d64148109798c520425d63148109b988520426f65884109b596210432e5488410cb552210434e5388410d354e21042e960884109bd94210426d6508410cb950210432d5408410d394c210434d5308410ba580210426e62940109b58a500426d65c8010cb953200432d54c8010d394f200434d53c80109bd95200432e5448010cb551200434e5348010d354d200433554c4010d554f100427965840109dd9510043355444010d554d10043e120440109ed9510043e22144010
  | 1 => 0xc26d62152309d984548c27561152309b986528c26c6154a308fd91518c23c64546309bd89518c26c62546309bd96218c26d65886309bd94218c26d6508630ba580218c26f62551309b189544c27761551309d185544c26e62151309b588544c25c6550d30c7151434c26e62d45309b58b514c25e65cc530a7593314c3675108530d9144214c2e960085309b98b540c26d62d50309d987540c27561d50308f596540c23e64150309798c540c26e62150309b588540c27661150309d584540c32e5494830cb552520c26e6194830cb951520c32d54548309b185520c3365494430cd552510c3665294430d954a510c3676294430d918a510c26f62544309b189510c3365454430cd551510c3665254430d9549510c3676254430d9189510c25d658c430c7552310c355518c430c7550310c355510c4309bd96210c26d6588430cb952210c32d5488430d9946210c36551884309bd94210c26d6508430cb950210c32d5408430d9944210c3655108430c7553300c35551cc03097d95300c31d544c030d5545300c27b654c0309798c54c825d63153208f99053c823d6414f20cb55042c82ce6310b20b358c42c82ae640cb20ab59032c834d530cb20d994421c82e960d5320cb55054c82ce6315320b358c54c82e96015320ba58353c82ae6414f20ab59053c834d5314f20ba58053c826f6550f209b19543c826e6510f209b59443c838d4310f20ab99351c82ad64d4720b398f51c82cd63d4720ba58351c82e960147209b99741c826d65d0720b398f41c82cd63d07209bd9541c826c65507209b99731c826d65cc720ab99331c82ad64cc7209bd9531c826c654c720b398c40c82cd6310320b998440c82e56110320ab99030c82ad640c320b998430c82e5610c3209798c548825d63152209d984548827561152208f990538823d6414e209d98453882756114e20d9946218825f63551209718d544827761551209d185544825e63151209758c544823f6454d208f19153482776154d209d185534823e6414d208f590534826e65d09209b195424832c5450920b398c42482cd63109209b997324826c654c920d314d32482ae640c920ab590324826e65c8520d914621482e96095120b3d8d54482cc6355120b9d8554482e46155120bad81544832d5415120b398c54482cd6315120ba58253482af6454d20ab19153482e76154d20b918553482eb6054d20ab99053482ad6414d20d354c534826f6550d209b195434826e6510d209b594434838d4310d20ba58251482af6454520ab19151482cf6354520b318d51482eb60545209b997414826d65d0520b398f41482cd63d0520d9147414826f65505209b19541483645110520ba98041482e960105209b997314826d65cc520ab99331482ad64cc520d9147314826f654c5209b1953148364510c520ba98
  | 2 => 0x62551319ed81544c67860551319b583524c66d60149318f990504c63d64141319b988504c66d62141319bd89540c66c62550319b988540c66d62150319e980540c67960150318f992530c63d6494c3197596430c6d56190c31c7151430c69d64cc43197d95310c677654c4319b98a500c66d62940319798c54c865d63153218f99053c863d6414f219798f548865d63d52219798e548865d63952218f993538863d64d4e218f992538863d6494e21cb95142886ce6310a21b358c428874e534ca21ab99032886ad640ca21b398f54886cd63d5221b9987548872f5495221b398e54886cd6395221b998454886ae64d4e21ab59353886e661d4e21ab99253886ad6494e21d3d4e53886e66114e219bd95438866c6550e219b994438866d6510e21e350c43886ce63d0621b358f41886ae64cc621ab59331886ae6414221ab59050886ce6314221b358c508865e63951219758e544866d62951219bd89544863e6494d218f592534866d6294d219bd89534865e63150219758c540867a60150219e580540863e6414c218f590530867a6014c219e580530866d65908219b594420872d5410821b398c42086cd63108219b596320866d650c821ab99032086ad640c821d354c320866f65484219dd9521086e661d5021cb55054086ce6315021b358c54086e66115021ba98054086e96015021b998753086ae6414c21ab590530874d5314c21b998453086ea6014c21ba58053086e661d0c21b958743086e66190c21b9586430866f6550c219b195430866e6510c219b594430878d4310c21d9986510866d65d0421b398f41086cd63d04219bd9541087a541104219b59731086ae64cc421ab593310866f654c421f14c431086ae6414021ab59050086ce6314021b358c500866f6254f409b18953d026f62547409b18951d029d63d07409b986529026c6154a4097d8d519025c63546409bd89519026c62546409bd96219026d65886409bd94219026d6508640ba580219026e6214d409b588535031c5350d409b98b515026d62d45408f997415029d63d0540d9d4421503645108540ba580215034e5394840d354e521026e6194840d394d521034d53548409b18552103565394440d554e51103665294440d954a51103676294440d918a511026f62544409b18951103565354440d554d51103665254440d954951103676254440d9189511023d6590440c754e41103355190440c754c411033551104409bd96211026d6588440d394e211034d5388440d9946211036551884409bd94211026d6508440d394c211034d5308440d994421103655108440c754f401033551d00408fd95401031d5350040cd545401027b65500409bd8954cc26c62553309b98854cc26d6215330c715143cc26f62547309b18951cc29d64cc7309b98b548c26d62d52309b988548
  | 3 => 0xfb09130e0000000000000016800000589278000000001f8160000000000080200000800800002004000010020000080100000c00802008008008020000080000000000c00800000000000010020040000300001000803000008000000000000000301a0180080100400c00000000000000040000040000100a000000010000080000100200002800000004000040000040000200000000000008000000000040040000000000800000000004000040040180000201200000801000010008020000000400600400400003006004000040080000000100000400805010000028020000000000000200000803000000000000000240280200800000000000000000040000000000300001000802000004030000020040100300001800001000004010000000000000000000000001000000008000100000000000a024058020040040000000000000800000010000000060000100000000000001000000000000000000180100000000003006014018030000040000400000401000002018000010020026f62547439b18951d0e6e62943439b58a50d0e6f62546439b1895190e6e62942439b58a5090e6e61d49439b5835250e6e61149439b5805250e6e62d45439b58b5150e6e62141439b5885050e7661141439d5845050e9d6490c438fd954310e5f6550c43a7d954310f1f6550c43e3d894310f8c6250c43e350e5210e6e61948439b5825210f1d4354843e350d5210f2f4354843d390d5210f2d4354843d350d5210f0d43548439b1855210e6f6054843c750e5110e6f62544439b1895110e6e62940439b58a5010f1d4354043ab18943d0b1c5350d42d31895310b1d53d0842d354e4210a3f6550842c754d4210a6f6550842d354d4210a7661d53329d58754ccb1c5450f32b318943ccb8d43d0b32b358c42cca7661951329d586544ca6f625513297195434cb1c5450d329b996424ca6c6550932e350d424ca3d6595032cb189540ca3e64150329798c540ca6e62150329b597420cb2d54d08329b594420cb2d5410832b358c420cb1d54cc832cb552320ca5f654c832c7551320ca6f654c832cb551320cb4e5394b41d354e52d066d6094b41d394d52d074d5354b419bd8152d066e62943419b58a50d066e6294e419b58a539071e5350e41a758f419066e62942419b58a509066d60d49419b580525065e63141419758c505066e62141419b588505066f6254c419b18953106b561d0c41a758f411063f65504419dd95411066e62940419b58a501066e62d53319b58b54cc66e62153319b58854cc72e5494b31cb55252cc66d6094b31cb95152cc72d5454b319bd8152cc66e62943319b58a50cc66e62d52319b58b548c66e62952319b58a548c71e5450e31a7593318c66e62942319b58a508c65d63951319b98a544c66d62951319bd89544c66c
  | 4 => 0x4ca000e49df000000000000000000000000000000000000000002550da000000005d23240000000000177000000000da0000000016ba4b0004c0002794380691900013418cd60003f60001d0000000000004a00000000000000000000000004ac000002a4000a20c0000000000002ee000000001da15400000000850001e50001d85014b202bdcea2c4000189689f53967a8bd81c000a94000004c248946839000604fe0f000000000000000318000000a80000000000084400000000000000003de000000fe000ab800000048000e31ba46a3e4000000005140019e14c0015480000000000000000aad3a8330001e40006c4426208410a000000000001de0000030c0000011c2e600000000000000000000000009a8000002ec42400000000ac543a011f4b94279600c000000000000001448000000000000051e0000000000000158000098358c4a50228a040000000083800000000000000000be000002432345fd19a00000000000005a0000000000000016c0004ec66400012136bb000000176000c50000009e00020360e0000000043ebf800000000000000000003440001d6008a4b42db21c4302d84d000140000000008f40004e20034cdd8000000000000000000000000450000000400000000000000050800099000000002a42a016930000000a4871800000000000000000000030a000000001be56a25c1e9925ac0002995c00000000000000b48bf00033e91054800000000000000007dc90000000000001540000002b000000a40001aa0008ac8f00044c0e000000000568000005a6574292ce48e764a79534ee704001dd1168b8000000008b00023a22e70cba8b700036d4f00060a858002a7000000101340000000000039a00000000000000000000003400003227e0018400000000000185000000001e02d20017da3c4c64d80000000000000000050000001610001782b80000000049000000000d88000000000000016c3515600025a6a0000004720000008700095caaa400003f0001974407417e27f0000008216625e2f00000000000000253000174000000004700024c000000002a80009e800000000001368000008c4a080031e35d4a000000000000610000000014a000000b5059286538e00003d00000025e3da000011d554c5441514c0000000000000029c5209c5420000017d000000049c50d6000000ca0006689d1725e096cf4800000000c22543f48bcf322a344998000000b00000000000000000000000001082d434879c0000000030474ac000043cd39490009487080000000086abc00000000000000000000000003540012c000000000000000780000000209c000002bc00000000000000c6000408000000000009b81480000000000000000c04c12d539e4c4c70005c40000013d26e000882f418e398
  | 5 => 0x1271160000000000046000000000000124000005b40000000000000000000000000f98000000001700013e0012c800000000428005860000007800000000066000000a30c54a20007392a00000067a185f2000001250000000007c4348480b800000c2c002990004f001800000758000002be2c0002cb08c3c4e6000000001678c35000b0d32e4000c254b00060c62c5880036e000e89d300041c528000000000007b000000058000003dc000004d620c000004f86a4000003ae000888ff0f4000d01b33c600000000000000000002b2000430000000010615b1b87fc4100000003d0f1c4326a705c800000000c30d90620000000000000105aed0000000000055a1c40000037aa74e40006081a000000510888000000005bc00000000000002561122ac6100000037d4300000000000000000000000000000014d2930000000001449a6e4931ad2b088c00000000060000000007c539800000000b80005721a4ca00052e00000000142b74000002720010d8b30000000016b000000000f31e4815488bf00c000a0000330a80000000004140000000000000000000020002f1000000d729f0000006e8000003a800000000640000962300014580035e8ec7da985e6aec8eaaa56e5b4000002900000000000004d3107f0200000019d23e7f4000000000001e00039c000720900000d400000000a8c002cc37800000000000bf56ca4236a000001320000000021300000000000000bd800000000000002cd00000000000000000000000001700000057e5e8c1a9b0ce000df800000b082080005e000000000002f4000000000000025a3fc0003800000000000000276818001031c40007a8d81e800171800000000000430a2b1c4e80000041800000000000000003e400000000000000000000de000000000000000000017c00051800000000bc80006c0000000041000000000000001818002ae000000000000000000032c0006900041e194fc0000000000000029a088002150009c899800514000621913e85c400000000000ba000000924b380000000173800000000f1064000000000000000000284b000000000000000000026f0000017f8005669286d14701a8740000000085c6f0720000dc000af15a3343b8ae0002e800030360000728000000000025d000a0c510a8088000000000000000017352a001038000000013a25c000001578000000017a800000709338005745f00200000000000124000b0400000000000421a535676800264000000000001dc6700000000000000000000000ee000000ba800000000000550000002215e80041a66d2c000000000db01b5d66341f2dc3c80000000000000163000570ac83980000080800000000000e39650000003700051c0000027b0846e02291b0005b0970001269a52f913000000000001640
  | 6 => 0x44e7e4670000001d400000018000000004688f80000000048400000158a140000045a0000000000000075aa2000be04500016a32c0003400001d20a48000000002e0000000001b2000000001a1000b24000004d80000000011ab8489000000250000000005e00000004200000000000000940000000000727e0000554207e000000000000000004600000012134209170828002f203e9c4000c8000000f80815bc0000000000000000000000558e922424e1f44f000000c0800000032000000000d40011b8cc1f08940000048a00000080000760000001d80000000000000091adf2c6a08700470000010c8000000000000004c408000000e8000000f600000047800000000d18000000007427d3942380000027000000000000000119ec0000000000026a0017d00000000174000000000ef09858a000158250005b80880000046400000000000000b4000000000000000000500022a600ed8000009c00019512a3f55a12946cad80013e076000001e157c7acb200000000164000000a3000000000000f700000000000000000000858000000000000000000000000594bbd230000000011f80000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x5c42e0001b153c00b255eb0980043999400010110c3c01d649ce074c11a8c00d092460000000088023006c280000059f340000a52dd89802b558332a04a12035501860c040030a240000a041060000309c1eeca1aa421e0c7650d5210f06a18c2a90878350f6054843c18caa1a849960d5458c420ca86b94a6a1c83435ca5450e31a1ae42a28618d1970151430c686b9ca8a1443435d2534ca21a1ce7aa4a910e0f5458e54886873a6a729c43835935394e21a1eeaa188710e0e6550c4388706aa2c62104383591530c821c1aa8b18a810e29545805408706b22a6298439254d6014c218d2e032a8610e0d6550c4308686b90a6a1a81981456008540a1ae42a2879850d72151434c33028ac010a61835516310b20c1ac8a98659060d5458c54c8306b22a629e41835954310f20a1ae62a2849050d7414d324828639aa82a241491c55415120c1aa8b18a89050c7454c5348306b22a629a41511c55314d208c8e2b28869050c7550c4348306b2a8621a419198c51d0520c4cc828e62906626158052c43122a0c2902219114c6148110c52a8b004208649535802104390aa24088021d054d2044010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1882010288a0681dd9435484380e879954310e21a04815516315120c05641c55314d2080c875954310d20a04815954310d20
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 801
  | 4 => 781
  | 3 => 56
  | 2 => 6
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
  | 6 => packedAt s5K6 (788+((h/14+packedAt s5K6 (704+(h % 14)*6) 6) % 53)*7) 7
  | 5 => packedAt s5K5 (24831+((h/267+packedAt s5K5 (21627+(h % 267)*12) 12) % 2057)*11) 11
  | 4 => packedAt s5K4 (32538+((h/260+packedAt s5K4 (29678+(h % 260)*11) 11) % 1823)*11) 11
  | 3 => packedAt s5K3 (2870+((h/18+packedAt s5K3 (2744+(h % 18)*7) 7) % 74)*7) 7
  | 2 => packedAt s5K2 (366+((h/2+packedAt s5K2 (360+(h % 2)*3) 3) % 8)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xe0fffff07fffff81fc3fc3fffc3ffffd11f1ff
  | 1 => 0xff07e1ff83f0fffe1fc3fc383fc383feee4e4f
  | 2 => 0xfff801fffc00f8ffe003ffc03ffc03830f8f8c
  | 3 => 0x1ffffff00fffffc00003ffffc03f00ff0
  | 4 => 0xfffffe00000000ffffffffffc0000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x22004011002000002004404884048888009095
  | 1 => 0x44518222194150160c4184111841117066464a
  | 2 => 0x8a32d54528eaa1aae222ea82aea82a1b0b8b8c
  | 3 => 0x1ca51988528832cd56a8220433327023b00d60
  | 4 => 0x10c6110e630cc4f19b33332702204043dd6000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xeeeaea88eeeaea88eeeaea88eeeaea88eeeaea88eeeaea88eeeaea88eeeaea88eeeaea88eeeaea88eeeaea88eeeaea88eeeaea88eeeaea88eeeaea88eeeaea88, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36721
namespace PEqualNP.Outside.L_meta_36721
open PEqualNP.Outside.L_meta_36721.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2aec35a58c0e0056fc25c73010460020b9ab138f5184d9c120009d48a44002eaa2add3a150b0c015ca24ac0072d9400c00bafa62264f54a879648b426bc02a00013000002200061c0020200080080c40510280010004606060405ff53015fd4c03fe53017f54c017d5300ff14c03fe43007f50c03fc43017fd4805fe52005f94805fd52017f148057c5200ffcc801fe32007f4c803fc32017fd4405fe51017f54405fc5100ffcc401fe31007f4c403fc31007fc8401fe21007f48401fc21017fd4005fe50017f54005fc5000ffcc001fe30007f4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1c200aff10e1001ffec50800eff6284007ff3142007bf98a1001ffac508002fd6284007fe3142003bf18a1005ffea50802ffe5284001bf294200bff54a1005ff8a50802f7c5284015ff9942000ff8ca10007fa650802bfc32840137eb0c200bffd461005ffca30802ffd5184017fe28c200affcc610007fc6308003fd3184015fe18c2000ffc8610007fc4308003fd2184001fe10c2003bf9821001ffea10800ffe5084007fea842003ff1421001ffe610800ffe3084007fe9842003ff0c21001ffe410800ffe2084007fe9042003ff0821001ffe210800ff71084001fd8842009ffd951004dfeca880037f65440013fb2a2009ff99510015fcca88027fd65440137eb2a2009ff19510015f8ca880277c65440053e32a2000ffd8d10005fec688003df63440016fb1a2008ff98d1000dfcc688003fd63440017eb1a2008ff18d1000df8c688003dc63440036e31a2009ffd4d1004efea688023fe5344013fea9a2000df54d10047f8a688023fe4344001fea1a2008ff10d10007fec488002ff6244001f7b122000bbd8910007fcc48801efe6244001feb122000bf58910007f8c48801efc6244001f63122000bb1891004ffea488027fe5244001bf2922009ff5491004ff8a4880277c5244011ff9922000ff8c910007fa6488023fc3244013ffa8a2009ff9451004ffaa288027fc5144011ff98a2000ff8c510007ec6288003fd3144001fa98a2008ff0c510007fe4288003fe2144001fe90a2000ff0851004ffea08800ffe5044013fea822003ff14110047fe608800ffe3044001fe9822003ff0c110007fe408800ffe2044001fe9022003ff08110007fe2088003fb1044007ff0822003fd8411001ffeca0800eff6504007ff3282002bf9941001efcca0800a7e6504007feb282005bf5941001efaca080027d6504007fe3282003bf1941001ffec60800eff6304007ff3182001bf98c1001fbcc608006de6304007feb182000bf58c1001fbac608002dd6304007fe3182003bf18c1002ffea6080177f5304009ff2982005ff54c10006faa608013fc5304009ff2182000ff50c10027f8860800fff62040077fb102003ff9881003dfcc40800fee6204001773102003ff58810005fac40800fed620400176b102003ff1881001df8c408017ff520400bff2902000df9481002ffaa408017fc520400bbe2902004ffcc810007fc6408003fd3204009fe1902006bf9841002ffea208017fe510400bfea882005ff14410027fe6208003fe3104001fe9882004ff0c410007fe4208003fe2104001fe9082000ff0841001dfcc00800fff5004007ff2802003ff5401001ff8a00800fff3004007ff1802003ff4c01001ff8600800fff2004007ff1002003ff4801001ff8400800fff1004007fb8802003ff8401001ff4200800ffd1004007fa8802000fe44010
  | 1 => 0x6fc6348021ffa9a4010dfd4d2007ffca690043fd5348001bea9a400fff14d2007ffc8690003fd434801ffe21a4010ffd4920087dea49001ffe524800fbf2924010ff5492003ff8a49001f7c5248021f62924010db1492007ffe649001ffe3248001f71924000ff4c920007da649001ffc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4000bf18520087fea290043fe5148021fea8a4010ff1452007ffe6290003fe3148001fe98a400fff0c52003ffe4290003ef2148001ff10a4000ff48520007da429001ffc2148021ffa824003ff94120087faa09000ffc504801fff9824003ff8c120007fa609000ffc304800fff9024007fec812001ffc409000fee2048007ffb284003bfd942001ffcca1000afe6508007feb28400ebf5942001ff8ca1000efc6508007ffb184003bfd8c2001ffcc610006fe6308007feb184000bf58c2001ff8c61000efc630801dffa98400edfd4c2006ffca61003bfd5308001bea98400dff14c2006ffc8610003fd430801bfe2184007bf9882003ffea41001ffe520800fbf2904007ff5482003ff8a41001f7c520800fff9904007ff8c82003ffa641001ffc3208007ffb084003ff98420005fcc21000ffd61080017eb084003ff18420077fea21003bfe510801dfea88400eff1442006ffe6210003fe3108001fe988400dff0c42003ffe421001ffe2108001f71084007ff4842003ff8421001fec21080077f3004003ffd402001ffca01000ffd5008007fe2804003ffcc02001ffc601000ffd3008007fe1804003ffc802001fde401000ffe2008007fd1004003ff4802001fda401001ff9200800dffb2e2006bfd9710037fccb8800afe65c400dfeb2e2006bf59710037f8cb8800afc65c4001ffb1e2000bfd8f10067fcc788006fe63c4001feb1e2000bf58f10067f8c788006fc63c400dffa9e2006dfd4f10067fca78801bfd53c4001bea9e200cff14f10067fc8788003fd43c4019fe21e2000ffd8b10005fec588003fe62c400f7f3162000ff58b10005fac588003fc62c400f7e3162006ffd4b10037fca5880037e52c400dfea962006ff14b10036f8a588033ff32c4001ff1962000ff4cb10067f8658801bff51c400dff28e2006ff54710037f8a388033ff31c4001ff18e2000fd8c710007fa6388003f531c4019fe18e2000ffc8710007fc4388003fd21c4001fe10e2006ffd431001ffca18801bfd50c4007fe286200cffcc31001ffc6188003fd30c4007fe1862000ffc831001ffc4188003fd20c4007fe1062003ffd961001dfecb0800ffe65840057f32c2003ff5961005dfacb0800ffc65840077e32c2003ffd8e1001dfec70800ffe63840037f31c2003ff58e10005fac70800ffc63840077e31c200bffd4e1005efea70802bfe5384017fea9c2000df54e10057f8a70802bfe4384001fea
  | 2 => 0x30007ba8698007fc434c001ffb126000bfd8930007fcc498003fd624c001fe3126007bf189300b7fea49805bfe524c001bf2926016ff549300b7f8a49805b7c524c02bffa126000ff90930007fa8498057fc424c003ff9926001ff8c93000ffa6498007fc324c001ffb0a6000bfd8530007fcc298003fd614c001fe30a6000bf185300b7fea29805bfe514c02dfea8a6016ff145300affe8298003fe414c001fea0a6015ff1053000ffe6298007df314c003ff18a6001ff4c530007ba6298007fc314c001ff90a6000ff88530007fa4298003fc214c0037fb026016ffd413001ffca09805bfd504c007fe2826015ffd013001ffc8098003fd404c007fe2026001ffcc13000ff6609800ffe304c007ef1826003ff0c13001fb86098007f8304c00fffb2e4007bfd972003ffccb9000afe65c800ffeb2e4014bf5972003ff8cb9001efc65c800fffb1e4007bfd8f2003ffcc790006fe63c800ffeb1e4000bf58f2003ff8c79001efc63c8029ffa9e4014dfd4f2009ffca790053fd53c8001bea9e4013ff14f2009ffc8790003fd43c8027fe21e4007ffd4b200a7dea59001ffe52c800fbf2964007ff54b2003ff8a59001f7c52c800ff62964007db14b2003ffe659001ffe32c800ff71964007ff4cb20007da659001ffc32c800fffb0e4007ff98720005fcc39001ffd61c80017eb0e4007ff187200a7fea390053fe51c8029fea8e4014ff1472009ffe6390003fe31c8001fe98e4013ff0c72003ffe439001fef21c800fff10e4007ff48720007da439001ffc21c8029ffa864003ff943200a7faa19000ffc50c8027ff9864003ff8c320007fa619000ffc30c8007ffb2c4003bfd962001ffccb1000afe6588007bf32c40029f9962001ffacb1004afd6588007beb2c40009f5962001ff8cb1000efc6588007ffb1c4003bfd8e2001ffcc710006fe6388007feb1c4000bf58e2001ff8c71000efc6388025ffa9c4012dfd4e2008ffca71004bfd5388001bea9c4011ff14e2008ffc8710003fd4388023fe21c4010bf58a20097fea51001ffe528800fbf2944012ff54a2003ff8a51001f7c5288023ff9944007ff8ca20007fa651001ffc3288007ffb0c4003ff98620005fcc31000ffd61880017eb0c4003ff18620097fea31004bfe5188025fea8c4012ff1462008ffe6310003fe3188001fe98c4011ff0c62003ffe4310003fe2188001f710c4000ff4862003ff84310003ec21880077f3044003ffd422001ffca11000ffd5088007fe2844003ffcc22001ffc611000ffd3088007fe1844003ffc822001fde411001ffb2088021ffb2a4010bfd9520006feca900027f6548021ff32a4002bf99520087faca90042fd6548021fe32a4002bf19520086f8ca9000a7c6548001ffb1a4000bfd8d2007ffcc690006fe6348001feb1a4000bf58d2007ff8c69000
  | 3 => 0xe2924207df149210effe649081ffe3248401fe9924207ff0c9210f7fea29087bfe514843dfea8a421eff145210effe6290803fe3148401fe98a421dff0c52103ffe429081ff72148401ff10a4200fb88521007fec090802ff6048401ff3024200ff58121007f8c09080efc604843dffa82421eff941210f7faa09087bfc504843bff982421dff0c12103ffeca1081eff650840fff3284202bf9942103ffaca1086efd650840ffe3284207bf1942103ffec61081eff630840fff3184201bf98c2103ffac610802fd630840ffe3184207bf18c210dffea61086f7f5308435ff298421bff54c21006faa61086bfc5308435ff2184200ff50c210d7f8861081efe620840fffa90421bfbd482103ffca41081f7e520840ffea904207ff1482103ef8a41081fec520840fb62904207ffcc82103ffc641081fee320840ffe9904200fb4c82103ff86410872fe6108437ffa88421bff944210dffaa21086ffc5108435ff9884200ff8c421007fa621086bfc310840fff9084207fbc842103ffc421081ff6210840ffe9084200fb4842103fea421081fff600840fff3004203bf9802103ffac010802fd600840ffe300421bffd40210dffca01086ffd5008437fe280421affcc0210d7f8601080fff658c0077fb2c6003ff99630015fccb1800ffd658c0337eb2c6003ff1963001df8cb1800fff648c0077fb246003ff992300bdfcc91800ffd648c0017eb246003ff1923001df8c918067ff548c033bfaa46018ff952300cffaa9180037d548c031fe2a46001bf58e3000ffea7180077f538c003ff29c6001ff54e3000efaa718007fc538c003ffa1c6001ff90e3000ffa8718007fc438c007ffb146003ff98a3003dfcc51800ffd628c0017eb146003ff18a300cffea518067fe528c001bf2946019ff54a300cff8a5180677c528c031ffa146000ff90a30007fa8518063fc428c003ff9946001ff8ca3000ffa6518007fc328c007ffb0c6003ff98630005fcc31800ffd618c0017eb0c6003ff186300cffea318067fe518c033fea8c6019ff146300c7fe8318003fe418c001fea0c6018ff1063000ffe6318007fe318c001ef18c6001ff4c63000ff86318007dc318c001ff90c6000ff88630007fa4318003fc218c0077f3046003ffd423001ffca11800ffd508c007fe2846003ffd023001ffc811800ffc408c007ff9846003f7cc23000ff6611800ffc308c007fc1846016ffd95300b5feca9805bfe654c0057f32a6016ff595300b5faca9805bfc654c0057e32a6000ffd9130005fec898057fe644c02f7f3226000ff59130005fac898057fc644c02f7e3226016ffd51300b6fea898057fe544c02dfeaa26000df551300aff8a89800eff634c003ffa9a6001dfd4d3000ffca698007fd534c003bea9a6001ff14d3000ffe8698007fe434c003ef21a6001ff50d
  | 4 => 0x8037d544c445fe2a26201bfd8d3100ffea6988077f534c403ff29a6201ff54d3100efaa698807fc534c403ffa1a6201ff90d3100ffa8698807fc434c401ffb126200bfd8931007fcc498803fd624c401fe3126207bf1893111ffea49888ffe524c401bf2926223ff5493111ff8a49888f7c524c445ffa126200ff90931007fa849888bfc424c403ff9926201ff8c93100ffa6498807fc324c4037fb0a6223ffd453111ffca29888ffd514c447fe28a6222ffd0531007fc8298803fd414c445fe20a6201ffcc53100fee6298807fe314c401ef18a6201ff0c53100fb86298807f4314c401ffb026200bfd8131007fcc098803fd604c401fe3026203bf1813111ffea09888ffe504c447fea826223ff14131117fe809888bfc404c403ff9826201f7cc13100ff8609881fff65c840f7fb2e4207ff99721015fccb9081ffd65c84437eb2e4207ff1972103df8cb9081fff63c840f7fb1e4207ff98f2100dfcc79081ffd63c84017eb1e4207ff18f2103df8c790887ff53c8443bfa9e4220ff94f2110ffaa7908037d53c8441fe29e4220ff90f21007fa8790883fc43c840fffa964207ff94b2103efca59081ffd52c840ffe2964207df14b2103ffe659081ffe32c840ffe9964207ff0cb2110ffea390887fe51c8443fea8e4221ff14721107fe6390803fe31c8401fe98e4220ff0c72103ffec19081ffe60c84077f3064207ff58321005fac19081ffc60c8443ffa864221ff9432110ffaa190887fc50c8441ff9864220ff0c3210e7fecb10872ff6588439ff32c4202bf996210e6fccb1080a7e6588439feb2c421cbf59621006facb108027d6588439fe32c4202bf19621007fec710802ff638843fff31c4201bf98e21007fac710802fd638843ffe31c4201bf18e210e7fea7108737f538843fff29c421cff54e21006faa71087ffc538843fff21c4200ff50e210fff8871087afd6288439ffa94421cfbd4a2103ffca51081f7e5288439fea944207ff14a2103ef8a510873ec5288439b6294421fffcca2103ffc6510803ee3288401fe9944200fb4ca2103ff8651081efe6188439ffa8c421cff946210e7faa310873fc518843fff98c4200ff8c621007fa631087ffc318840fff90c4200fbc862103fee4310803ff6088401ff3044203bf98221007fac110802fd6088401fe304421cffd42210e7fca110873fd5088439fe284421fffcc2210fff8611087bff654843d7fb2a4200dfd9521004feca9087bfe65484057f32a421eff595210f5faca9087bfc65484057e32a421edf19521014f8ca90803ff63484017fb1a421dff98d2100dfcc690803fd63484017eb1a421dff18d2100df8c69087bff534843dbfa9a421dff94d210f7faa6908037d534843bfe29a421dff90d21007fa8690877fc434843dffa924207ff9492103efca49087bfd524840ff
  | 5 => 0xca3203ffec31901ffe618c8017f30c6407ff58632005fac31901ffc618c853ffa8c6429ff9463214ffaa3190a7fc518c851ffa0c6428ff1063200ffe6319007fc318c80fffb046407ff9823201dfcc11901ffd608c8017eb046407ff1823214ffea1190a7fe508c853fea846429ff14232147fe81190a3fc408c803ff9846401ff0c23213ffeca9909eff654c801bfb2a64009fd953213ffcca9900afe654c84ffeb2a6427bf5953213ff8ca9900afc654c84fbe32a64029f19532007fec899002ff644c84dff3226417bf99132007fac899002fd644c84dfe3226417bf1913213ffea89909f7f544c84dff2a26427ff55132006faa89909bfc544c80f7fb1a6401ffd4d3200efea699007fe534c803ef29a6401ff54d3200efaa69909fdd534c801aea9a6401ff14d3200ffe8699007fe434c803ef21a6401ff50d32007ba8699007fc434c8037fb126427ffd493203ffca49901f7e524c84ffea926407ff1493203ef8a49909bff424c80fff2126400fb90932007fa8499003ed424c80ffe2126401ffcc93200fde649901ffe324c80fef1926407ff0c93203fb86499007ec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6400bf1853213ffea29909ffe514c84ffea8a6427ff14532137fe829909bfc414c803ff98a6401ff0c532007fec099002ff604c801ff3026400ff58132007f8c09900efc604c84fffa826427ff9413213ffaa09909ffc504c84dffa026426ff1013200ffe6099007fc304c84bffb2c6225bfd963112ffccb1880afe658c44bfeb2c6225bf5963112ff8cb1880afc658c401ffb246200bfd9231127fcc91885efe648c401feb246200bf59231127f8c91885efc648c44bffaa46225dfd5231127fca918897fd548c401beaa46224ff1523100dfac718807ff538c403bfa9c6201ff94e3100ffaa7188077d538c403fe29c6201ffd0e3100ffc8718807de438c403fea1c6200f750e3100ff88718803ff628c401ff3146207bf98a31007fac518802fd628c401fe3146225ffd4a3112ffca5188037e528c44bfea946225ff14a3112ef8a518893ff428c401ff2146200ff50a31127f88518807ff328c403ff1946201ff4ca3100ff86518806fe618c44bffa8c6225ff9463112ffaa318897fc518c449ffa0c6200ff90631127f88318807ff318c403ef98c6201fdcc63100ff86318807f4318c401ffb046200ff9823101dfcc118803fd608c4017eb046200ff1823112ffea118897fe508c44bfea846225ff14231127fe8118893fc408c403ff9846201ff0c23100fb8611888fff654c4477fb2a6223ff99531015fcca9888ffd654c4477eb2a6223ff19531015f8ca98803ff644c4017fb226222ff991310bdfcc898803fd644c4017eb226222ff191310bdf8c89888fff544c447bfaa26222ff9513111ffaa898
  | 6 => 0x80000200000080000200200680180101480400180480000500580100000000900080a00400180200200200080100400900180101700100280c00080380400000200101680500180080000000000000180100000000e00100380100000000200400180200780000200000080400100080080380000000500080080f00000080180200100781280000000100000200100080280000480000100080000280380700180080980900080180880000200180180080200000000780000c80480400200700100080b8000037f6454c013fb22a62cdf99153006fac8a98b37c6454c03bfb1aa6019fd8d53016bec6a98077f4354c03bf21aa601df10d53006fec4a98037e6254c01beb12a600df1895303cf8c4a98b37f4254c59be212a601dfcc95300ebe64a98077c3254c01bfb0aa600df98553006fac2a98037c6154c59bfa0aa62cdf1055300efe62a98077c3154c01bfb02a600df98153006fac0a98037c6054c59bfa02a62cdf1015300efe60a98077c3054c57ffb2a862bbfd954315ffccaa180afe6550c57bf32a86029f9954315ffacaa18aefd6550c01beb2a86009f5954315ff8caa180afc6550c037fb1a8601ffd4d4300efea6a1807fe5350c03fea9a8601df54d4300ff8a6a1807fe4350c03df21a8601ff10d4300fb886a18079c4350c01ffb128600bfd8943007fcc4a1803fd6250c01fe3128607bf1894315ffea4a18affe5250c57fea92862bff1494315ef8a4a1807ff3250c03ef9928601ff0c943007fec2a1802ff6150c01ff30a8600ff58543007f8c2a1802fc6150c57ffa8a862bff9454315ffaa2a18affc5150c03ff98a8601ff0c54300fb862a1803ff6050c017fb028600ff98143007fac0a1803fc6050c077e302862bffd414315ffca0a18affd5050c57fe2828601ffcc14300fbe60a1807fc3050c0fbfb1ca407df98e5203efac7290027d639480fbe31ca42adf90e52006fa87290ab7c439480fbf314a4079f98a5203edcc52901f7f329480fbe194a407dfd865203efcc32901f7d619480fbe30ca42adfcc652156f8632901f7f609480fbf304a407df5825203ef8c1290ab7f3094855be184a407ffd963203dfecb1901f7f658c80f3fb2c6407ff99632015fccb1901ffd658c8537eb2c6407ff1963203df8cb1901f7c658c80f3e32c6407ffd923203dfec91901ffe648c82f7f3246407ff59232005fac91901ffc648c80f7e3246429ffd523214efea9190a3fe548c853feaa46400df55232147f8a919006fd638c803ffa9c6401dfd4e3200ffca719007fd538c803bea9c6401ff14e3200ffe8719007fe438c803fea1c6401ff10e3203dfcc51901fff528c80fff2946407df94a3203ffaa51901ffc528c80fbe2946407ffd0a3203ffc851901fee428c80ffe2146407ffcca3203fbe6519007ef328c80ffe1946407fb0
  | 7 => 0x397ac99fc00032d0001769685093583c3c019a04f33f2bba12bd054be0750a342a20001c12c49b1864781582af45b5063139a380026610c43f04b1fb80037a1e30864b84f048eab729357e9b13f90850484261fc8313e9d770d20e9a3017300056693e00000036b9c00000004f70003ea33a000000000000000060bc43e51978e1cb30005accc91a58cd80009087d3c94ef15e000441343da21c321c4fa00052100025e00051911302295f0003c70000001bb0003650000000c825743e00000022c1af0001915d85ad34cb4e844ca947e2e01bd8005be0003f855d4533c580d800000023b4436ac7000003e8912854390003063ff8a121509e4c6196a6cdc937b0488b4b5980780080000380000080180780000700480380080880000380400780000000100100282a80080180000100300200300180080000680780000001b00180400b80180080500380080180000300100000580080000080281080000000000000080500080900100100280600500980380080180100f80080000280100201180580080001700080f00280680000180400180000000000a00400180380100000100100800100000100000380000380200200380280180080000500080180300080180100180180600180480300000200400080600180080000000280300100100200000080980380480d00000000080200380100080100080000000100000100800200400100000001200200080700100280200080100280100000000000380000080400000400000680400800000000700180000000000000000a80080000280080400200100000480000580180100000000b80480080100000080180000800280200480180080080000200080100080c80280200100100180780000000580a00080080000000100000380000380100000000280000000800800680080480c00100580100300000780000380680000100300100000200180280080200080580400000000080000100380400d00180000080a80800000780000180000080080400400280080080000080280180000180100000000080200100280800000500000781300100600300180300180100800000080000080100880300580600000400100400380000180000000380900000000080380000400280000180280500000600000f80081200800000280380c80100600b80400980c80000800580780180200080000c00500600280800780000200880a00080000580c00100080300000000380580000c00400400000800600200100400000000000000080100280380280080000280000300300100080380e00a80200000000580000300000100300400000000000080180380300000280080080000000080080000000080780080400000300280080000300180480781380280400380000000e000001008801000
  | 8 => 0xb1630fa8002372873f000c3c000000000000012f82e000000398a7f0000000000000003b90000000fd33c0000003232b63f10003c50835a64c300012549980006a201a6300000059d5130001e400000035924b4e1b28aa72c4182000023580a880dc0000b418912408d0841555cf15d070ccc34012827510a5ae314c0d0564ebb1f0960c4dc22e4a975de2ad339063b4502c5625d525a5b707c23128f4ff1a31be9320001238920680001802d054f27112480053700000044600004e0000004130000f500000036e0001621ef8000bf19a0095020003c15bf0004d03fa0002078003dc000438c920002e242c00053e3071d38005110000000001eb2cb0004850003eb82100050a0c38ef4df2e700002221d15a0e728e0e8bc80dd0d02008000b789d5880001f08000000000000000000000000003a70000001840003be2a50000bd0000005aa0e24ab0000590000000002e3ba52891ed1f81e1a09cfe5b51f744d144224c2b44755627b4e108e57bd3d34154d0fe2d51e22053eaa09410096a9900030400043c41739f45e49423280035217e1764eb0003f63fb12eb643273ddc37b2539236653806e4e826f4833aa22400050800b2ae3c7c06c584f51790374840fb4004c500023b35c00006b599d291561c0d042610000001cd36200018c4200000000001f62e628d0000001f180000001b8000990000000000000001fed8e5b0b4bb4e250b878004e72a41200002940000de3200001120ec5dc000347b2a24cb5100000000051622900008b4310725b1532094da73b18163cd24fd3c56f0001e70c200000000000000029e0005b34fc0005ba00054c1d94e200031a5e25703860000c00a00001c600001ac972bd4ad4484ed4682c8c1f3c6bcfc270f84ecbb38000ac03826b0004cf33180ebfc1d1987173af3aa1235027077c7d23a0141cb04454600000012d03d0002a60001f50003488000023e9099daf9c814d0005005952ec0c5000000041bbd3a78428e48001fda5838f147541ba84bc3722625712c68a55b82d60005492141a6000062b46d4e4e60004db33380007880035604689c09380009da6525042d0d61ec5920cbc479fe59f1cf47c389a9d4fb0305451004d12ca21914a33d45648d00050349935e46b288b27bec4ae000297d0b32829c09b86e87f27e4028aa0001dc0041923bb384a335794a02954f43542010702a22a059e51818300000000000030e0003c49ff800569105c03273000370000039098a4d29b0b6bb4975aa30e3d761a237154459622a1d295b0ee43710fcf81420ccd2a1a40195854fd56511f3ad4e900000000054859a8e5b3b5231d55adbf190554b04d579d5307e0170db1c54615a456cb44dce1fd4725430d30c2ad1c1d091d911140002c3000000000287c5503fb34a4a0001600000c30002f0438079b870000
  | 9 => 0x33000000016f9a90002021c7049cb90005200000000188001c20000000005903cb00022d1ba10700017f1d217743a23e2be00014280000000032c00017a0000820000001042e932e0000745c74d2043021a46dda0e61c91bcb9028200001824e1453f4237d1d2fe0000b700000016d28346f11e0360000005680001f002640f0002b122b0005940003cf0004790e790b0003085724d416c35b0000954085312f858734b17018b05847b38adcd45d129ba325f405bae0000000000000000000000000c91a835f3e44da24adb641516b95313439b00000058b01d000040ac70c721680050e16c8000003dd0002520000002fb00000000000023d1880001ee0a84873000001ba80000006d47720e0005a300000048c136000000245b732961ef00058325c45731708111080002f0062638000001310000001e913800000000047100042f00000027719f1a70000254e08000660000000000000003094d82460133ee34d0000000fbd402c100000000000031e0002f7514111bd112899c28000055f38847f0003d5095d2526c5365b1da78eb3858ec8003d92200002f60550005b424900000000000018545a0001181a11461078000002b22cd204afa4a30000002478002765d02ed00033e56bcc20002db51210900e2cf20c26a2980473b32f50ba0981f92645cb28c1d13952fd29f04c21780000012dc8b4b21431e3c2300040acde39e1c112f51e11d5db2030610013110004ea00000034a800489a1a0000000004ba00056300057d800245000541350571d7f15c3a400000051735d498d6b11753b08a41a16101e00012684a3db3333d33e024418d4cb5755471de57fa51ce000007800000057cc060530345a15cc4692483d711280000009f00000010e22700024d8000000001e2baf3195b20ab368a43ad91d4a448003b14b50001fa4641948b506d8000004089404b600032405a1ff0f21f42c2368177d103cc23939306f0bc1db00000000000028129a05e000206930370c88d980cc000442000000000404ce50000002b54801a2c1c4ec3751940f9b2f4bd5614d50000002703313ce8004b00760001bd0001164f609b1335600ed47320f1ab0000000413c987700026d0001be5c80000893b0d4200012580000038d0000000000ad0002590da0003972e104aa5131d208bbf25b0000115a91ea43436d0000005d350f1485d10a94d900000013a1990b220446021b4502085c61264143843f25c30003a98002783b292e57b00000012c800097c0c2a80ca2383308001fb57e4125a84400000000001508001788001024960cb2181e144515033f5663bc0f4129000000313205d8d8f600008c56437432980000000006000038912780055000020d5265c50004ee1aa1df55517d1a5332c3300015e8001750500003a887180046e4320004d738
  | 10 => 0x1a0b05b953c80000041e4b4425535065421233b1609ed2203c52b5d653a3fd4c104644e2a92279782412d22c05c43a255b16b27946a4284015e03352161e0af35d743dc493b424c371c5139415101548e0002e80001a48003eb03f235ac600003d8003fcaf93fd8080000fa25d09cb550620004761ee94f57a4a50004c722e2c7cca0521e003358659700052700500000059a0000003818001889e8493334221372d5100023f00c9f3369a8a1b8dd43ca0001a68d75a500000024f0000b938e07949f4dd00f4590000001bf3610000004c800034a0004fbb791110002269544c400003b572971a122ab13b36a0001b04e4000219995a4213d03a1e50000b653353930a1965594a200023c0eba1e409972a474cd30d0a72fec194953ce000290106ca703e05f0a420754ca4b8002dd22f0403df26000001b2f400000008010820b2768005150398000003910000cd12a39c0f700055737803aa530e6adc15f9cc38a0870072562cc2ee0000002ef10f1f2452800202c055659ae37fdca2aa00046c0000002c938c34c00049e00000000000027a0005674079193739b6910584143800045404170ba6b4dd3031243534f9a7b6f49d52c160a104e30b33184630000005a98000438004914a10a080000019b0673f300000046255c50d58cc9c3af951c7a2d416752851c36027c2433023a65d2047c039d4000097385174ad84a419e0000eabd039d0002ac3b80a20001523268000003d4000358a2500058c13186cafc0102543771ca00018682d32fbd83cbd98de11212da0f12234bb0000001bf8000005521ad1798000000000f910ab7e80059c3ab0000004f932645c4d60000768002911b5ae30bb00d06c1e61663053380003e700000022800051f58a00057a80000045f28d80000000007b00037f40b21f16edc000000000041100024980030155a5a02bf0002671b602b0c180016190302458f4aa2e44ce41b3e600000000000046d00000032b0001ce00038200030f1570000730d90003d24443b73da1493e11903b2172109d584af0c11b9383ad1380bcd8000cadbd3d62eb578a1300000051a00056e1222b953f1b7d7c0fc80042956c2f12ce1150000002348cf26b92700a00059b10127d4433e8965141b7e54a1878f305b5993a100013500008840a0001c43323375dd36318107a218d733f0b5a1dd3494364243e81b50321c196db9804930b48600000018a4d3000248b1c2368001d70000c60d500037d43b2ea2038ea0000000000000000000000000003888000003220001b41373b03813f52ff00013f5801393c896e0000002e5000225a401b82a4a844c01309da21136b00000000022637c81231456a1b38af06f99706337dc2e1b4bac0002d72c500004580014c0001710000000000003e20ce3ed00056d46600013c1234ac000000000000
  | 11 => 0x3f389fdb00003765013c35aeabc3801b24304673471d6321189c090929ac0691088d13ef04b8fc39905d3458d818e00009400002a1b704248201991c55453452d0e080048817c1741692174b725501a3105782989414160001bc4220000001d30354bf47526ab153533c20f02b34a5ab043d40e0000000000619538e14b12b80005813dc8001bbbc62de5c12d2dac4a85890003c1b41c523ca92abf710d4742360003a90e84893435df0642df0000001f13c2dab17b3b60000be0900290003fe94e30c24ec983868d40000e944c0e403cdaf4653420510b12684903032bb08f024952c2bb4634f5aa8e2a7209a58d16457d37c561a064f24dc19d0000b5dabb830932223ff3290ae5bb1b316a20a5bc0201448000711d008e81f000369000000342c4f00000000000000000000008f94b00031b19539616f57433636700005c4540000002324020b800000027434851b0e03cc9930002f20002ba40750700000023440090648f00000000000050c27580b95955e0df05739a2d30280004a612b5d94e68df80000000026e28634985452426d83bb828e33a00ff3b504f48a36c3e309aa924180e50c459318f19852e44b2692b400352f28b0de9b9c9a58bae9bde4811d84f10a62c844a0003fe58211b3570000001
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd705881001eec705881001eef505881001eee505881001eed505881001eec505881001eef305881001eee305881001eed305881001eec305881001eef105881001eee105881001eed105881001eec105881018d7f769481003e7f769481003c7f769481018e7e769481018d7d769481017e7d76948100047d769481003e7c76948100057d739481018e7f63948101567e639481018f5e63948101565e63948100067d639481018f5d63948100065d639481018e7c639481019d7e729481017f6e729481018e7f629481003e7e629481018f6e629481003e6e629481017e7d629481018f6d62948100066d629481003e7c62948101967e619481018e7e609481018f77109481018f7a109481018f75109481003cff768c81001cfe768c810004fd768c81001cfc768c81017d7f758c81017d7c758c81014e7e658c8100067d658c810146be648c810006bd648c81000ede638c810006dd638c81003eee628c810006ed628c810004ff764c81001cfe764c810004fd764c81001cfc764c8100057f754c81002d7c754c81013e7e654c8100067d654c810136be644c810006bd644c81000ede634c810006dd634c8100075d534c81003eee624c810006ed624c810005f7714c810005f4714c810064ff768c41001cfe768c41000cfd768c41001cfc768c41012e7e658c4100067d658c410126be648c410006bd648c41000ede638c410006dd638c410006ee628c410006ed628c410066f6618c41001dfa708c410005f9708c410064ff764c41011e7e654c4100067d654c410116be644c410006bd644c41000ede634c410006dd634c410006ee624c410006ed624c410066f6614c410004fd76c841010e7e65c84100067d65c8410106de63c8410006dd63c841003eee62c8410006ed62c8410004ff768841003cfd768841002d7e75884100057d75884100e67e65884100067d65884100fede6388410006dd638841003eee6288410006ed62884101876c528841001dfa7088410005f97088410004ff76484100057f754841002d7c75484100f67e65484100067d65484100eede6348410006dd634841003eee6248410006ed624841003cff760841001cfe7608410004fd760841001cfc76084100de7e65084100067d65084100d6de6308410006dd630841003eee6208410006ed620841017f6c520841001dfa7008410005f9700841001dfb7644010006fb7644010004fb76440100077b754401016f78754401001f7a654401001f796544010007db7344010007d8734401001fda634401001fd9634401016f7b5344010007795344010007eb7244010007e8724401001fea624401001fe962440100077a524401016f78524401001dfb714401001ff37144010176fa614401001ff2614401016ff2514401016ff15144010007f22144010007f12144010
  | 1 => 0x8c1001edf5058c1001ede5058c1001edd5058c1001edc5058c1001edf4058c1001ede4058c1001edd4058c1001edc4058c1001edf2058c1001ede2058c1001edd2058c1001edc2058c1001edf1058c1001ed71058c1001ede1058c1001edd1058c1001ed51058c1001edc1058c101a57f7654c100067f7654c100047f7654c101a67e7654c101a57d7654c100067d7654c100047d7654c101a67c7654c100057f7454c101a67f6454c101667e6454c101a73e6454c101663e6454c100067d6454c101a73d6454c100063d6454c101a67c6454c101b57f7354c1002f5f7354c101a67f6354c1000e7e6354c101a75e6354c1000e5e6354c100267d6354c101a75d6354c100065d6354c1000e7c6354c1017d7c7254c101a67f6254c101ae7e6254c101a76e6254c101a76d6254c101a67c6254c100275f3254c100667e6154c101a67e6054c101a7771054c101a77a1054c101a7751054c10004ff7650c1001cfe7650c10004fd7650c1001cfc7650c1002d7e7550c100057d7550c1015e7e6550c100067d6550c1000ede6350c10006dd6350c100279c4350c1003eef759881003e6f759881003eee759881003eed759881003eec759881003e6c759881003eef739881003eee739881003eed739881003eec7398810006ef53988100066f5398810006ee5398810006ed53988100066d5398810006ec5398810006ee4398810006ed4398810006ec439881003eee719881003eec7198810006ef5198810006ee5198810006ed5198810006ec5198810006ef3198810006ec319881001eef709881001eee709881001eed709881001eec709881001eef509881001eee509881001eed509881001eec509881001eef309881001eee309881001eed309881001eec309881001eef109881001eee109881001eed109881001eec1098810004ff75588100067f75588100047f7558810014fe7558810004fd7558810014fc75588100067c75588100147c7558810004ff735881000cfe735881000cfc73588100067f53588100067d535881001eef7258810006ef5258810006ee5258810006ed525881017e7c5258810006ec52588100066c5258810006ef3258810006ec325881003cff715881003cfd715881001cff705881001cfe705881001cfd705881001cfc705881001eee205881001eec2058810006ef75588100066f7558810006ee7558810006ed7558810006ec75588100066c7558810006ef7358810006ee7358810006ed7358810006ec7358810006ef53588100066f5358810006ee5358810006ed53588100066d5358810006ec5358810006ee4358810006ed4358810006ec4358810006ee7158810006ec7158810006ef5158810006ee5158810006ed5158810006ec5158810006ef3158810006ec315881001eef705881001eee705881001ee
  | 2 => 0x6df634c11000edc634c110006ef624c110006ec624c110005f7714c110005f4714c110007d5314c110004fe76c81100067f65c81100a67c65c8110006df63c811009edc63c8110006ef62c811003eec62c81101cf6c52c8110005f671c8110005f571c811003cff7648110004fd764811003cfc76481100057f754811004d7c75481100067f65481100867c6548110006df634811007edc6348110006ef624811003eec62481101c76c5248110005f77148110005f4714811001ff010481100067f65c41100367c65c4110006df63c4110066dc63c4110006ef62c4110006ec62c411001df671c411001ef761c411001dfa76c411001efa76c411001cfa76c41100077b65c41101bf7865c4110007db63c4110007d863c41101bf7b53c41100077953c4110007eb62c4110007e862c41100077a52c41101bf7852c411001dfa71c411001efb61c411001ff361c4110007f231c4110007f131c41100067f73594100047f73594100067e73594100067d73594100067c73594100067e43594100067c43594100067f72594100067e72594100067d72594100067c725941003c7c72594100067f32594100067c325941002e7f71594100067e715941002e7d715941002e7c71594100067f31594100067c315941001e7f705941001e7e705941001e7d705941001e7c705941001e7f305941001e7e305941001e7d305941001e7c305941001e7f205941001e7e205941001e7d205941001e7c205941001e7f105941001e7e105941001e7d105941001e7c1059410004ff7558c10014fe7558c100067e7558c100147e7558c10004fd7558c100067d7558c10014fc7558c10004ff7458c100bcfe7458c100bcfc7458c100067f5458c1001edf7358c100267f5358c10006df5358c100065f5358c10026de5358c10006dd5358c10026dc5358c10006df4358c10026de4358c10026dc4358c10004ff7258c1003cfc7258c100067c5258c10026df3258c10026dc3258c1000cff7158c1000cfd7158c10024fc7158c10026dc3158c1001cff7058c1001cfe7058c1001cfd7058c1001cfc7058c1001ede3058c1001edc3058c1001ef71058c1001ef51058c10006df7558c10006de7558c100065e7558c10006dd7558c100065d7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c100065f5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006de5258c10006dd5258c10006dc5258c100065c5258c10006df4258c10006dc4258c10026df7158c10006de7158c10006dc7158c10006df5158c10006de5158c10006dd5158c10006dc5158c10006df4158c10006dc4158c1001edf7058c1001ede7058c1001edd7058c1001edc705
  | 3 => 0xf63949100075f63949100065f63949101567e63949100067d63949101567c63949100075c63949101565c63949101cd7e72949101cf6e72949101ce7f62949100076f62949100066f629491003e7e62949101ce7d629491003e7c62949101cf6c629491003e6c629491018f76109491003cff768c910004fe768c910004fd768c91003cfc768c9101cd7f758c9101cd7c758c9100067f658c91014e7c658c910006bf648c910146bc648c910006df638c91000edc638c910006ef628c91003eec628c910004ff764c910004fe764c910004fd764c910004fc764c9100057f754c91004d7c754c9100067f654c91013e7c654c910006bf644c910136bc644c910006df634c91000edc634c9100075d534c910006ef624c91003eec624c910054fe768c5100067f658c51012e7c658c510006bf648c510126bc648c510006df638c51000edc638c510006ef628c510006ec628c510005f6768c510056f6768c51000777658c5101ef74658c510005f7748c510005f5748c510007b7648c510007b4648c5101ef77548c51000775548c510045f5738c510007d7638c51000ef6638c51000ef4638c510047d4638c51000ed4638c51004777538c51004775538c510047d6438c510007d5438c510007e7628c510007e4628c51000776528c5101ef74528c51001df6708c51001df4708c5101e7d6308c5101e7d4308c51001cfc764c5100067f654c51011e7c654c510006bf644c510116bc644c510006df634c51000edc634c510006ef624c510006ec624c510047d4314c510005fb704c51001df8704c51001df4764c51000ef4764c51001cf4764c51000777654c5101df74654c510005f7744c510005f5744c510007b7644c510007b4644c5101df77544c51000775544c510045f7734c510007d7734c510007d7634c51000ef6634c51000ef4634c510047d4634c51004777534c51004775534c510007e7624c510007e4624c51000776524c5101df74524c510007f3704c51001df6704c51001df4704c510007f0704c510047d7304c51001cfe76c851001cfc76c85100067f65c851010e7c65c8510006df63c8510106dc63c8510006ef62c851003eec62c851001dfa70c8510005f970c8510004fe768851004d7e75885100057d75885100067f65885100e67c6588510006df63885100fedc6388510006ef628851003eec62885101d76c528851001cfc76485100057f754851004d7c75485100067f65485100f67c6548510006df63485100eedc6348510006ef624851003eec6248510005fb704851001df87048510004fe76085100067f65085100de7c6508510006df63085100d6dc6308510006ef620851003eec62085101cf6c520851000cff764c110044fd764c11000cfc764c1100067f654c1100b67c654c110006bf644c1100aebc644c110
  | 4 => 0x8910007cc63d8910006cc63d89100076f53d89100076d53d89101ffe610d89101ffe410d8910006ef75d8910006ee75d89100066e75d8910006ed75d89100066d75d8910006ec75d8910006ef73d8910006ee73d8910006ed73d8910006ec73d8910006ef53d89100066f53d8910006ee53d8910006ed53d89100066d53d8910006ec53d8910006ee43d8910006ed43d8910006ec43d89101feef71d8910006ed71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef31d8910006ec31d8910006ef70d89101feee70d8910006ed70d89101feec70d8910006ef50d89101feee50d8910006ed50d89101feec50d8910006ef30d89101feee30d89101feec30d89101feee10d89101feec10d891004d7e75989100057d75989100067f65989100067c6598910045de7398910005dd7398910006df6398910006dc6398910006ef62989100057f755891004d7c75589100067f65589100067c6558910005df7358910045dc7358910006df6358910006dc6358910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7358910006df7358910004df735891000cfe735891000cfc7358910006dc735891000cdc73589100067f53589100067d5358910006ef72589101ce7c5258910004ff7158910006f77158910004ff7058910006fb7058910004fe76189101cd7c75189100067f65189100067c6518910006df6318910006dc631891003eee6218910006ed62189101cf6c5218910005ee7618910006ee7618910004ee76189101cf6f75189101cf6c7518910006ef65189100076f65189100066f6518910006ee6518910006ed6518910006ec65189100076c65189100066c6518910006ef6318910007cf6318910006cf6318910006ee6318910006ed6318910006ec6318910007cc6318910006cc63189100076f53189100076d53189101f7e610189101f7e4101891003eef751891003e6f751891003eee751891003eed751891003eec751891003e6c751891003eef731891003eee731891003eed731891003eec7318910006ef53189100066f5318910006ee5318910006ed53189100066d5318910006ec5318910006ee4318910006ed4318910006ec431891003eef711891003eed7118910006ef5118910006ee5118910006ed5118910006ec5118910006ef3118910006ec311891003eef701891003eee701891003eed701891003eec7018910006ef50189101f6ee5018910006ed50189101f6ec5018910006ef30189101f6ee30189101f6ec30189101f6ee1018910006ed10189101f6ec101891003e7f76949100057e76949101ce7e76949100047e76949101ce7d76949101cd7c769491003e7c769491003c7c76949100057d73949100067
  | 5 => 0x6df50d8d101e6de50d8d10006dd50d8d101e6dc50d8d10006df40d8d101e6de40d8d101e6dc40d8d101e6de20d8d101e6dc20d8d101e6de10d8d101e6dc10d8d100057f7558d1004d7c7558d100067f6558d100067c6558d10005bf7458d1020dbc7458d10006bf6458d10046dc6358d10005ef7258d10005ec7258d10004ff7558d100067f7558d100047f7558d10014fe7558d10004fd7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d100bcfe7458d100bcfc7458d10006bc7458d100bcbc7458d100067f5458d10044ff7358d10006df7358d100467f5358d10004ff7258d10006ef7258d10004ef7258d1003cfc7258d10006ec7258d1003cec7258d100067c5258d10054ff7158d10006f77158d10064ff7058d10006fb7058d10005de7618d10046de7618d10004de7618d100475e7518d100475d7518d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d100075f5418d100075c5218d10047d57118d10206df6118d10207d61018d10207d41018d100067f7654d100057e7654d100067e7654d100047e7654d100067d7654d100057c7654d100067c7654d100047c7654d100057f7454d100067f6454d100073f6454d100063f6454d101667e6454d100067d6454d101667c6454d100073c6454d101663c6454d100457f7354d1004f5f7354d100467f6354d100075f6354d100065f6354d1000e7e6354d100467d6354d1000e7c6354d100475c6354d1000e5c6354d101cd7c7254d101ae7e6254d101ae7c6254d100475f3254d101a7761054d10004ff7650d10004fe7650d10004fd7650d10004fc7650d1004d7e7550d100057d7550d100067f6550d1015e7c6550d10006df6350d1000edc6350d100479c4350d1003cfe76d891004d7e75d89100057d75d89100067f65d89100067c65d8910006df63d8910006dc63d89100076c52d8910004ff75d8910014fe75d89100067e75d89100147e75d8910004fd75d89100067d75d89100047d75d8910014fc75d891000cfe73d8910004fd73d891000cfc73d89100067f53d89100067d53d8910006ef52d8910006ee52d8910006ed52d89101ce7c52d8910006ec52d89100066c52d8910006ef32d8910006ec32d891003cfe71d891003cfc71d891001cfe70d891001cfc70d891003cee76d89100076e75d89100076d75d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d
  | 6 => 0xe634c610006dd634c610005fb704c61001df8704c61003eee62c8610006ed62c861001dfa70c8610005f970c861005d7e75886100057d75886101feef628861003eec628861022f6c528861003cff76486100057f754861005d7c754861003eee6248610006ed6248610005fb704861001df870486101f6ef620861003eec62086102276c520861001df976c4210006f976c421021f7b53c42100077953c42100077a52c421021f7852c421001ff271c421004d7e76d951004e7e76d95100147e76d95100057d73d95100067e63d95100067c63d95101cd7e72d95102177610d95102177410d95100067f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067e43d95100067c43d95100067f72d95100067e72d951003c7e72d95100067d72d95100067c72d95100067f32d95100067c32d95102167f71d951004e7e71d951004e7d71d951004e7c71d95100067f31d95100067c31d95100067f70d95102167e70d951004e7d70d95102167c70d95100067f30d95102167e30d95102167c30d95102167e20d95102167c20d95102167e10d951004e7d10d95102167c10d951000cfe76d8d1004d7c75d8d100067f65d8d100067c65d8d10046de63d8d100075f53d8d10004ff75d8d100067f75d8d10014fe75d8d10004fd75d8d10014fc75d8d100067c75d8d100147c75d8d100bcfe74d8d10004fd74d8d100bcfc74d8d100067f54d8d100467f53d8d10006df53d8d100065f53d8d10046de53d8d10006dd53d8d10046dc53d8d10006df43d8d10046de43d8d10046dc43d8d1003cfe72d8d10004fd72d8d100067c52d8d10046df32d8d10046dc32d8d1000cfe71d8d1001cfd71d8d1000cfc71d8d10046df31d8d1001cfe70d8d10044fd70d8d1001cfc70d8d10046df30d8d10045de76d8d1000cde76d8d100075f75d8d100075c75d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dc64d8d100075f54d8d100075c52d8d101e7d771d8d101e7d610d8d101e7d410d8d10006df75d8d100065f75d8d10006de75d8d10006dd75d8d10006dc75d8d100065c75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d100065f54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10006de72d8d10006dd72d8d10006dc72d8d10006df52d8d10006de52d8d10006dd52d8d10006dc52d8d100065c52d8d10006df42d8d10006dc42d8d101e6df71d8d10046de71d8d10006dd71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df41d8d10006dc41d8d10006df70d8d101e6de70d8d10006dd70d8d101e6dc70d8d10
  | 7 => 0xc710005f5744c71024777544c71000775544c710007d7734c710007d7634c71000ef6634c71000ef4634c710067d4634c71006777534c71006775534c71000776524c71024774524c71001df6704c71001df4704c710067d7304c710006ef62c871003eec62c871001cfd76887100357e75887100057d758871003eee6288710006ed628871023f6c528871001dfa7088710005f970887100057f75487100357c7548710006ef624871003eec624871001cfd760871003eee6208710006ed62087101976c520871001dfa7008710005f9700871000cff764c31000cfc764c31000ede634c310006dd634c310005f7714c310005f4714c310007d5314c31003eee62c8310006ed62c83101976c52c8310005f671c8310005f571c831003cff76483100057f75483100357c754831003eee6248310006ed62483102376c5248310005f77148310005f47148310004ff7558e10014fe7558e10004fd7558e10014fc7558e10004ff7458e100bcfe7458e100bcfc7458e100067f5458e1001edf7358e100567f5358e10056de4358e10004ff7258e1003cfc7258e100067c5258e10056df3158e1001cfc7058e1001ede3058e1001edc3058e1001ef71058e1001ef51058e100067f7654e101a67e7654e100067d7654e101a67c7654e100057f7454e101a67f6454e101667e6454e100067d6454e101a67c6454e101b57f7354e1005f5f7354e101a67f6354e1000e7e6354e100567d6354e1000e7c6354e102257c7254e101a67f6254e101ae7e6254e101a67c6254e100575f3254e100467d6154e101a67e6054e101a7771054e10004ff7650e1001cfe7650e10004fd7650e1001cfc7650e1005d7e7550e100057d7550e1000ede6350e10006dd6350e100579c4350e10004ff7558a100067f7558a100047f7558a10014fe7558a10004fd7558a10014fc7558a100067c7558a100147c7558a10004ff7358a1000cfe7358a1000cfc7358a100067f5358a100067d5358a1001eef7258a10006ef5258a102267c5258a10006ec5258a100066c5258a1001cfc7058a1001eee2058a1001eec2058a1003e7f7694a1018e7e7694a102267d7694a1003e7c7694a100057d7394a1018e7f6394a101567e6394a100067d6394a1018e7c6394a1019d7e7294a102276e7294a1018e7f6294a1003e7e6294a102267d6294a1003e7c6294a101ce7d6194a1018e7e6094a1018f771094a1003cff768ca1001cfe768ca10004fd768ca1001cfc768ca102257f758ca102257c758ca1003eee628ca10006ed628ca10004ff764ca1001cfe764ca10004fd764ca1001cfc764ca100057f754ca1005d7c754ca100075d534ca1003eee624ca10006ed624ca10005f7714ca10005f4714ca10044fd768c6101e6df638c61000edc638c61000cff764c61001cfc764c61000ed
  | 8 => 0x64fd73d8f100667f53d8f10066de43d8f1003cfe72d8f10004fd72d8f100067c52d8f10006f671d8f10066df31d8f10006f970d8f101e6de30d8f101e6dc30d8f1000cff7658f10066dc6358f10004ff7558f10014fe7558f10004fd7558f10014fc7558f10004ff7458f100bcfe7458f100bcfc7458f100067f5458f10006df7358f100667f5358f10004ff7258f1003cfc7258f100067c5258f1001cfc7158f10066dc3158f10066df3058f100067f7654f100067e7654f100067d7654f100067c7654f100057f7454f100067f6454f101667e6454f100067d6454f101667c6454f100657f7354f100375f7354f100667f6354f1000e7e6354f100667d6354f1000e7c6354f101957c7254f101ae7e6254f101ae7c6254f100675f3254f10004ff7650f10004fe7650f10004fd7650f10004fc7650f100357e7550f100057d7550f10006df6350f1000edc6350f100679c4350f100357e75d8b100057d75d8b100076c52d8b10004ff75d8b10014fe75d8b100067e75d8b100147e75d8b10004fd75d8b100067d75d8b100047d75d8b10014fc75d8b1000cfe73d8b10004fd73d8b1000cfc73d8b100067f53d8b100067d53d8b10006ef52d8b101967c52d8b10006ec52d8b100066c52d8b10006f671d8b10006f970d8b101feee20d8b101feec20d8b10004fd7698b10006ef6298b1003cff7658b100057f7558b100357c7558b10004ff7558b100067f7558b100047f7558b10014fe7558b10004fd7558b10014fc7558b100067c7558b100147c7558b10004ff7358b1000cfe7358b1000cfc7358b100067f5358b100067d5358b10006ef7258b101967c5258b1003eee6218b10006ed6218b101976c5218b1003e7f7694b101967e7694b101967d7694b1003e7c7694b100057d7394b100067f6394b101567e6394b100067d6394b101567c6394b101957e7294b101976e7294b101967f6294b1003e7e6294b101967d6294b1003e7c6294b1003cff768cb10004fe768cb10004fd768cb1003cfc768cb101957f758cb101957c758cb10006ef628cb1003eec628cb10004ff764cb10004fe764cb10004fd764cb10004fc764cb100057f754cb100357c754cb100075d534cb10006ef624cb1003eec624cb1001cfd768c71000ede638c710006dd638c71001dfa708c710005f9708c71001df5768c71000ef5768c71001cf5768c710005f7748c710005f5748c71024f77548c71000775548c71000ef6638c710067d6638c710007d5638c71000ef4638c71006777538c71006775538c710067d6438c710007d5438c71000776528c71024f74528c71001df6708c710007f2708c710007f1708c71001df4708c7101e7d6308c7101e7d4308c710024ff764c710006df634c71000edc634c710067d4314c710005f7764c710026f7764c710005f7744
  | 9 => 0x46148520007eb704852001dee704852001dec7048520007e8704852003eef604852003feb604852000cff764c12007cfd764c12003cfc764c1200067f654c1200b67c654c120006df634c12000edc634c120005ef724c12003dec724c12025f6c524c120004ff7558c20014fe7558c20004fd7558c20014fc7558c20004ff7458c200bcfe7458c200bcfc7458c200067f5458c2001cff7358c2001edf7358c2006e7f5358c2006ede5358c20006dd5358c2006ede4358c2003cff7258c2003cfe7258c2003cfd7258c2003cfc7258c2003e7e5258c2003e7c5258c2003ede3258c2003edc3258c20004ff7158c20004fc7158c2006edf3158c2003eec2158c2001cfe7058c2001cfc7058c2001ede3058c2001edc3058c2001eef2058c2001eed2058c200067f7654c201a67e7654c200067d7654c201a67c7654c200057f7454c201a67f6454c201667e6454c200067d6454c201a67c6454c201b57f7354c200775f7354c201a67f6354c2000e7e6354c201a75e6354c2000e5e6354c2006e7d6354c201a75d6354c200065d6354c2000e7c6354c2003d7e7254c2003d7c7254c201ae7e6254c201af5f3254c201af5d3254c201af6c2154c201a67e6054c201a76f2054c201a77a2054c201a76d2054c201af792054c20004ff7650c2001cfe7650c20004fd7650c2001cfc7650c200757e7550c200057d7550c2000ede6350c20006dd6350c2006f9c4350c20004ff7598420014fe7598420004fd7598420014fc759842000cfe7398420004fd739842000cfc73984200067f53984200067d539842003e7e529842003e7c529842001ef67198420006f65198420006f5519842003ef7219842003ef4219842001ef6109842001ef41098420004ff75584200067f75584200047f7558420014fe7558420004fd7558420014fc75584200067c75584200147c7558420004ff735842000cfe735842000cfc73584200067f53584200067d535842003e7e525842003e7c525842001ef77158420006f65158420006f5515842003ef7215842003eec215842003ef4215842001eef205842001eed205842001ef6105842001ef41058420004ff768c42001cfe768c420004fd768c420006f6618c420006f5618c420004ff764c420004fd764c42001cfc764c42000ede634c420006dd634c420005ef724c42003dec724c420006f6614c420006f5614c42003ded7688420006ed7688420004ed76884202576e75884200076d75884200e6ee658842003eec658842003eef6388420006ed63884202576f53884200076d538842003dee718842003fe67188420006ed61884201fded70884201feee608842003fea6088420066de63d8f10004ff75d8f10014fe75d8f10004fd75d8f10014fc75d8f100bcfe74d8f10004fd74d8f100bcfc74d8f100067f54d8f10
  | 10 => 0xc92013e7c654c920006df634c92000edc634c9200075d534c92003f6e524c92003f6c524c920005fb704c92001df8704c92001dec764c92000eec764c92001cec764c9200076f754c920085ee754c920085ec754c92028f6c754c9200856c754c9200076f654c92028f6c654c920005ef744c920005ed744c920006ef644c920006ed644c92028f6f544c9200076d544c92003def734c92003fcf734c920007cf634c92000eee634c92000eec634c92007fcc634c92000ecc634c92007f6f534c92007fce534c92007f6d534c92028fcd534c9200074d534c92007fce434c920007cd434c920005ef714c920007eb704c92001dee704c92001dec704c920007e8704c92003eef604c92003feb604c9200067f65d85200067c65d85200076c52d8520004ff75d8520014fe75d8520004fd75d8520014fc75d852000cfe73d8520004fd73d852000cfc73d85200067f53d85200067d53d85202267e52d85202267c52d8520006f731d8520006f431d85200857e75985200057d75985200067f65985200067c65985200076c5298520006f761985200057f75585200857c75585200067f65585200067c6558520005df735852007ddc73585200076c52585200067f65185200067c65185200076c5218520006f56118520004ff7518520014fe7518520004fd7518520014fc751852000cfe7318520004fd731852000cfc73185200067f53185200067d5318520006ef521852017e7e521852017e7c5218520006ec52185200066c5218520006ee3218520006ed3218520006f73118520006f4311852001cfe701852001cfc70185201f6ee20185201f6ec2018520004fe768c520004fd768c520004fc768c5200067f658c52012e7c658c520006df638c52000edc638c52003dee728c520005ed728c5202876c528c520004ff764c520004fe764c520004fc764c5200067f654c52011e7c654c52027f6c524c520005ee76c852003eee76c8520004ee76c8520085ee75c852003dec75c85200076f65c85202776c65c852003def73c8520005ed73c85202776f53c85200076d53c8520006ec61c852001dee70c852001dec70c852003eef60c852003feb60c852001cfe76885200857e75885200057d75885200067f65885200e67c658852026ded728852003f6c5288520006f76188520006f4618852001dfa7088520005f9708852001cfc76485200057f75485200857c75485200067f65485200f67c654852003f6e524852003f6c5248520006f76148520006f46148520005fb704852001df8704852001cec76485200076f7548520085ee7548520085ec75485202676c75485200856c75485200076f65485202676c6548520005ef7348520005ed73485202676f53485200076d534852003def714852003fe77148520007e76148520006ec6148520007e
  | 11 => 0x3c7e72d95200866e72d95200867d72d95200866d72d95202be7c72d952003c7c72d95200067f32d95202be7e32d95202be7c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f31d95200067c31d95202be7f21d95202be7c21d95202be7f70d952018e7e70d95200867d70d952018e7c70d95200067f30d952018e7e30d952018e7c30d95202be7f20d952018e7e20d95200867d20d952018e7c20d952018e7e10d952018e7c10d952000cfe76d8d200857c75d8d200067f65d8d200067c65d8d2007ede63d8d200076c52d8d20004ff75d8d200067f75d8d20014fe75d8d20004fd75d8d20014fc75d8d200067c75d8d200147c75d8d200bcfe74d8d20004fd74d8d200bcfc74d8d200067f54d8d2007e7f53d8d20006df43d8d2007edc43d8d2003cfe72d8d2001cfd72d8d2003cfc72d8d202b67e52d8d202b67c52d8d2007edf32d8d20004fe71d8d20004fd71d8d2007edc31d8d2003cfd70d8d2007edf30d8d200057f7558d200857c7558d200067f6558d200067c6558d20005bf7458d202adbc7458d2007edc6358d200076c5258d20005f77158d20005f47158d20004ff7558d200067f7558d200047f7558d20014fe7558d20004fd7558d20014fc7558d200067c7558d200147c7558d20004ff7458d20006bf7458d20004bf7458d200bcfe7458d200bcfc7458d20006bc7458d200bcbc7458d200067f5458d2007cff7358d20006df7358d2007e7f5358d2007ede4358d2008cff7258d20006ef7258d202a67e5258d202a67c5258d20004ff7158d20006f77158d20004f77158d20004fc7158d20006f47158d20004f47158d2009cff7058d20006fb7058d200067f7654d200057e7654d200067e7654d200047e7654d200067d7654d200057c7654d200067c7654d200047c7654d200057f7454d200067f6454d201667e6454d200067d6454d201667c6454d2007d7f7354d200875f7354d2007e7f6354d2000e7e6354d2007e7d6354d2000e7c6354d200076f7254d2003d7e7254d2003d7c7254d200076c7254d2003d6c7254d2007f5f3254d201af7b2054d201a76e2054d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200857e7550d200057d7550d200067f6550d2015e7c6550d2000ede6350d20006dd6350d2007f9c4350d2029f6c5250d20005ee768c92003eee768c92003f6f758c920085ee758c92003dec758c92003f6c758c92003d6c758c9200076f658c9202976c658c92003def748c920005ed748c920006ef648c920006ed648c9202976f548c9200076d548c92007ded738c92000eee638c92000eec638c92007f6f538c92007f6d538c920005ed718c92001dee708c92001dec708c92003eef608c92003feb608c92001cfc764c9200057f754c9200857c754c9200067f654
  | 12 => 0xd7654e200047d7654e201a67c7654e200057f7454e201a67f6454e201667e6454e200067d6454e201a67c6454e201b57f7354e200975f7354e201a67f6354e2000e7e6354e2008e7d6354e2000e7c6354e2003d7e7254e2003d7c7254e2007e7d6254e2008f5f3254e201a67e6054e201a76f2054e201af7b2054e20004ff7650e2001cfe7650e20004fd7650e2001cfc7650e200957e7550e200057d7550e2015e7e6550e200067d6550e2000ede6350e20006dd6350e2008f9c4350e2000cff764ca2001cfc764ca200057f754ca200957c754ca2013e7e654ca200067d654ca2000ede634ca20006dd634ca200075d534ca2003fcc324ca20005fb704ca2001df8704ca20004ff7598620014fe7598620004fd7598620014fc759862000cfe7398620004fd739862000cfc73986200067f53986200067d53986201967e52986201967c529862001ef6719862001cfe709862001ef6109862001ef41098620004ff7558620014fe7558620004fd7558620014fc7558620004ff735862000cfe735862000cfc73586200067f53586200067d53586201ce7e52586201ce7c525862001ef7715862001cfc705862001eef205862001eed205862001ef6105862001ef41058620004ff768c62001cfe768c620004fd768c62012e7e658c6200067d658c620006f6618c620006f5618c620004ff764c620004fd764c62001cfc764c62011e7e654c6200067d654c62000ede634c620006dd634c620005ef724c62003dec724c620006f6614c620006f5614c6200957e75886200057d75886200e67e65886200067d658862003f6e528862003f6c5288620006f66188620006f5618862001dfa7088620005f970886202cf6e75886200076d75886200e6ee65886201ff6e65886200e66e65886201ff6d65886201feec65886201feef6388620006ed63886202cf6f53886200076d538862003dee71886201ffe66188620006ed61886201ffe561886201ffea70886201fded7088620007e9708862003eee60886200057f75486200957c75486200f67e65486200067d6548620006f66148620006f56148620005fb704862001df870486201f5ed760862003eed76086200deee65086201f76e65086200de6e65086201f76d65086201f6ec65086201f6ef6308620006ed63086202c76f53086200076d530862003fe67108620006ed610862003def70086201f5ed700862003fea60086200857e76d95200867e76d95200147e76d95200057d73d95200067e63d95200067c63d952003d7e72d95200876e72d952003d6e72d95200876d72d952003d7c72d95202bf7b20d952018f6e20d952018f6c20d95202bf7820d95200067f73d95200067e73d95200067d73d95200047d73d95200067c73d95200067e43d95200067c43d952018e7f72d95202be7e72d9520
  | 13 => 0xcb200076f754cb200a5ee754cb200a5ec754cb202f76c754cb200a56c754cb20005ef744cb20005ed744cb2003eef644cb20006ed644cb202f76f544cb200076d544cb2003fcf734cb2000eee634cb2003eec634cb2009f6f534cb2009fce534cb2009f6d534cb202f7cd534cb200074d534cb2009fce434cb20007cd434cb20005ef714cb2001dee704cb2001dec704cb20004ff7598720014fe75987200067e75987200147e7598720004fd75987200067d75987200047d7598720014fc759872000cfe7398720004fd739872000cfc73987200067f53987200067d539872001cfe729872001cee7298720006ef529872003e7e529872003e7c529872003eec529872003e6c529872003eee3298720006ed329872003ef6719872003eef219872003ef7219872003ef421987201feee209872003eec2098720004ff7558720014fe7558720004fd7558720014fc7558720004ff735872000cfe735872000cfc73587200067f53587200067d535872001cfc725872003e7e525872003e7c525872003ef7715872003ef7215872003ef42158720004ff768c72003cfe768c720004fd768c72000ede638c720006dd638c72003dee728c720005ed728c7202ef6c528c720004ff764c720004fd764c72003cfc764c72003dee724c7202e76c524c72003def7648720006ef76487200076f75487200a5ee75487200a5ec75487202df6c75487200a56c7548720005ef7348720005ed73487202df6f53487200076d534872003fe77148720006ee614872001dee704872001dec704872000cff764c32003cfc764c32000ede634c320006dd634c320005ef724c32003dec724c3202a76c524c3200067f73596200047f73596200067e73596200067d73596200067c73596200067e43596200067c43596200967f72596202d67e72596200067d72596202d67c72596200067f32596202d67e32596202d67c32596200067f71596200067e71596200067d71596200067c71596200067f31596200067c31596202d67f21596202d67c215962001e7f705962001e7e705962001e7d705962001e7c705962001e7f305962001e7e305962001e7d305962001e7c305962001e7f205962001e7e205962001e7d205962001e7c205962001e7f105962001e7e105962001e7d105962001e7c1059620004ff7558e20014fe7558e200067e7558e200147e7558e20004fd7558e200067d7558e20014fc7558e20004ff7458e200bcfe7458e200bcfc7458e200067f5458e2001edf7358e2008e7f5358e2008ede4358e202a67e5258e202a67c5258e2008edf3258e20004ff7158e20004fc7158e2008edf3158e2001cfc7058e2001ede3058e2001edc3058e2001eef2058e2001eed2058e201a57f7654e200067f7654e200047f7654e201a67e7654e201a57d7654e200067
  | 14 => 0x45f970985300057f75585300b57c7558530005bf74585300adbc7458530005ef7258530005ec7258530065fb70585300b57e75185300057d7518530006f56118530004ff7518530014fe75185300067e75185300147e7518530004fd75185300067d75185300047d7518530014fc75185300bcfe7418530004fd74185300bcfc74185300067f54185300067d541853001cfd73185300267f53185300267d5318530026de4318530006dd431853003cfe7218530004fd72185300067e52185300067c5218530026df3118530026f63118530026f53118530206de3018530206dc3018530004fe7690530004fd7690530004fc7690530006bf64905300bebc649053000dde7390530005dd73905300079d4390530004ff7650530004fe7650530004fc765053000dde735053001cdc764c530005df744c530005dd744c53031f5f544c5300075d544c5300075e524c53031f5c524c53000ddf714c53000fd7714c530007d7614c530006dc614c530007d4614c530007db704c53001dde704c53001ddc704c530007d8704c53000edf604c53000fdb604c530004fe76c8530004fd76c853003cfc76c8530006f761c8530006f461c8530004fe7688530004fd7688530004fc76885300b57e75885300057d758853000dde7388530005dd7388530006ef628853003eec62885303176c5288530004ff7648530004fe7648530004fc76485300057f75485300b57c7548530004fe7608530004fd760853003cfc760853000dde7308530005dd7308530006ef620853003eec62085302a76c5208530006f76108530006f4610853001dfa7008530005f9700853000cfe765013030cfd765013000cfc7650130005df735013000ddc73501300079d4350130004ff7558f20014fe7558f20004fd7558f20014fc7558f20004ff7458f200bcfe7458f200bcfc7458f200067f5458f2003edf7358f2009e7f5358f2009ede5358f20006dd5358f2009ede4358f2001cfc7258f2003e7e5258f2003e7c5258f2003eee4258f2003ede3258f2003edc3258f20004ff7158f20004fc7158f2009edc3158f2009edf3058f200067f7654f201ae7e7654f200067d7654f201ae7c7654f200057f7454f201ae7f6454f201667e6454f200067d6454f201ae7c6454f203057f7354f200a75f7354f201ae7f6354f2000e7e6354f201af5e6354f2000e5e6354f2009e7d6354f201af5d6354f200065d6354f2000e7c6354f200076f7254f2003d7e7254f2003d7c7254f201af6c7254f2003d6c7254f201af6e4254f201af5f3254f201af6e3254f201af5d3254f201af6f2154f20004ff7650f2003cfe7650f20004fd7650f2003cfc7650f200a57e7550f200057d7550f2000ede6350f20006dd6350f2009f9c4350f2003dee7250f202ff6c5250f2003def764cb2006eef764
  | 15 => 0xd72d91300067c52d91300aebc42d9130004fe71d9130004fd71d91300aebc41d913000cfd70d91300aebf40d91300aebc645913035dfb7059130004ff7559130014fe7559130004fd7559130014fc755913030cff7359130006df735913030e7f5359130004ff725913003cfc72591300067c5259130004ff7159130004fc715913035cff7059130006fb70591300067f76551300067e76551300067d76551300067c76551303557f74551300b73f74551300ae7f64551300073f64551300063f64551300be7e64551300ae7d64551300be7c64551300af3c64551300be3c645513033d7f735513033d7d73551303467f635513033f5e43551302a57c725513034e7c62551300af3f425513033f5f315513033e7f605513033f7b30551303475e30551303475c305513033f78305513001ddc7650d300bedc7650d3001cdc7650d303375e7550d300075d7550d3000ddf7450d3000f9f7450d300079f6450d300bede6450d300bedc6450d300af9c6450d300be9c6450d300af5f5450d300af5d5450d303375c5250d300af9f4250d30005df7150d300af9c4150d30007db7050d3001dde7050d3001ddc7050d30007d87050d3000edf6050d3000fdb6050d300af9f4050d300b57e75d89300057d75d8930004ff75d8930014fe75d89300067e75d89300147e75d8930004fd75d89300067d75d89300047d75d8930014fc75d89300bcfe74d8930004fd74d89300bcfc74d89300067f54d89300067d54d893001cfd73d893008e7f53d893008e7d53d893008ede43d8930006dd43d89302a67c52d893008eee32d893008eed32d8930004fe71d8930004fd71d8930006ef629893007df970989300057f75589300b57c7558930005bf74589300adbc7458930005f77158930005f4715893009dfb705893003eee6218930006ed621893003e7f76949302a67e76949302a67d769493003e7c76949300057d74949300067f649493032e7e64949300067d649493032e7c64949302a57f73949301557d739493018e7f63949301575e43949300075d43949302a57e72949302a76e72949302a67f629493003e7e629493003e7c62949301575f31949303267f60949301577b309493018f5e309493018f5c3094930157783094930004fe7690930004fd769093003cfc76909302a57f75909302a57c7590930006bf64909300bebc649093003eee6290930004ff7650930004fe7650930004fc76509300057f75509300b57c75509300073d54509300079d4350930004ff75d8530014fe75d8530004fd75d8530014fc75d85300bcfe74d8530004fd74d85300bcfc74d85300067f54d85300067d54d853001cfd73d85300567f53d85300567d53d853003cfe72d8530004fd72d85300067e52d85300067c52d8530056f631d8530056f531d8530006f76198530
  | 16 => 0x4a3018e7f6494a3032e7e6494a300067d6494a3018e7c6494a302b57f7394a301557d7394a302a67d6394a3019d7e7294a302b76e7294a3018e7f6294a3003e7e6294a302b67d6294a3003e7c6294a301575c3194a3018e7e6094a3018f5f3094a301577b3094a3018f783094a3003cff7690a3001cfe7690a30004fd7690a302b57f7590a302b57c7590a3003eee6290a30006ed6290a30004ff7650a30004fd7650a3001cfc7650a300057f7550a300cd7c7550a300073d5450a30005df7350a3000ddc7350a3003eee6250a30006ed6250a30004ff7598630014fe7598630004fd7598630014fc75986300bcfe7498630004fd74986300bcfc74986300067f54986300067d54986300667f53986300667d539863003cfe7298630004fd72986300067e52986300067c529863001ef67198630066f63198630066f5319863001cfe709863001ef6109863001ef41098630004ff75586300067f75586300047f7558630014fe7558630004fd7558630014fc75586300067c75586300147c7558630004ff7458630006bf7458630004bf74586300bcfe74586300bcfc7458630006bc74586300bcbc74586300067f54586300067d54586300467f53586300467d5358630004ff7258630006ef7258630004ef725863003cfc7258630006ec725863003cec72586300067e52586300067c525863001ef77158630046f63158630046f53158630046dc315863001cfc705863001edf305863001edd305863001ef6105863001ef41058630004ff769063001cfe7690630004fd76906300bebc6490630006f66190630006f56190630004ff7650630004fd765063001cfc76506300bebe6450630006bd6450630005df735063000ddc7350630006f66150630006f561506301e6df648c630006dd648c6303775f548c6300075d548c6300075e528c6303775c528c63000dde718c63000fd6718c6301e7d6618c630006dd618c6301e7d5618c6301e7da708c6301e5dd708c630007d9708c63000ede608c63000fda608c63003cff76c863001cfe76c8630004fd76c863000dde73c8630005dd73c863003eee62c8630006ed62c8630004ff768863001cfe7688630004fd76886300cd7e75886300057d758863036f6c5288630004ff7648630004fd764863001cfc76486300057f75486300cd7c7548630005df734863000ddc734863003eee6248630006ed624863003cff760863001cfe7608630004fd760863003eec62086302b76c520863001dfa7008630005f970086300bcfe76d91300aebe64d9130004ff75d9130014fe75d9130004fd75d9130014fc75d91300ae7f54d91300aebe54d9130006bd54d913001cff73d913000cfe73d913001cfd73d913000cfc73d91303667f53d91303667d53d9130366bf43d9130366bd43d913003cfe72d9130004f
  | 17 => 0xdd7e7550c210057d7550c2100ede6350c21006dd6350c210d79c4350c2103dee7250c212ff6c5250c2103def764c821106ef764c8210076f754c8210ddee754c8210ddec754c8213976c754c8210dd6c754c821005ef744c821005ed744c82103eef644c821006ed644c8213976f544c8210076d544c82103def734c82103fcf734c82100eee634c82103eec634c8210d76f534c8210d7ce534c8210d76d534c821397cd534c8210074d534c8210d7ce434c821007cd434c821005ef714c8210feee614c82103fe6614c8211f5ec704c8210fcff768c42103cfe768c42100cfd768c42103cfc768c42100ede638c421006dd638c42103dee728c421005ed728c4212ef6c528c4210fcff764c42103dee724c4212e76c524c4210d7d4314c42103def7648421006ef7648421004ef76484210076f75484210ddee75484210ddec75484213876c75484210dd6c7548421005ef7348421005ed73484213876f53484210076d534842103def714842103fe7714842138eee614842103fe66148421387e65148421387e551484211f5ec7048421004ff75580210067f75580210047f7558021014fe7558021004fd7558021014fc75580210067c75580210147c7558021004ff735802100cfe735802100cfc73580210067f53580210067d5358021006ef525802103e7e525802103e7c525802103eec525802103e6c525802103eee3258021006ed325802103eef2158021006ed215802103efb7058021006fa5058021006f9505802103efb205802103eec205802103ef82058021004ff7559230014fe7559230004fd7559230014fc755923001ebf74592300c67f545923030e7f535923030e7d535923030ebf435923030ebd4359230004ff725923003cfc72592300067c5259230004ff7159230004fc71592300c6bf415923030edc315923001cfe705923001cfc705923001ebe405923001ebc405923001edf305923001edd30592300067f76552303467e76552300067d76552303467c765523037d7f74552300cf3f74552303467f64552300be7e64552300c67d64552300be7c645523033d7f735523033d7d735523033e7d63552302b57c725523034e7e62552300c73f425523033f5c31552303467e60552303475f305523033f7b3055230347783055230004ff7558a300067f7558a300047f7558a30014fe7558a30004fd7558a30014fc7558a300067c7558a300147c7558a30004ff7458a300bcfe7458a300bcfc7458a300067f5458a300067d5458a3007e7f5358a3007e7d5358a3001eef7258a30006ef5258a302b67c5258a30006ec5258a300066c5258a3007eee3258a3007eed3258a30004ff7158a30004fc7158a3001cfc7058a3001eee2058a3001eec2058a3003e7f7694a3018e7e7694a302b67d7694a3003e7c7694a300057d749
  | 18 => 0xe7654d210047e7654d210067d7654d210057c7654d210067c7654d210047c7654d210057f7454d210067f6454d211667e6454d210067d6454d211667c6454d210ed7f7354d210f75f7354d210ee7f6354d2100e7e6354d210ee7d6354d2100e7c6354d2103d7e7254d2103d7c7254d210ef5f3254d211af772154d211a67c6054d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210f57e7550d210057d7550d210067f6550d2115e7c6550d21006df6350d2100edc6350d210ef9c4350d2100cfc764c9210057f754c9210f57c754c9210067f654c92113e7c654c921006df634c92100edc634c9210075d534c92103fcc324c921005f7714c921005f4714c921104fe768c5210067f658c52112e7c658c52100cff764c5210ecfd764c52103cfc764c5210067f654c52111e7c654c521006df634c52100edc634c521005ef724c52103dec724c5210f57e75885210057d75885210067f65885210e67c658852103f6e528852103f6c528852103df6718852103ef7618852139f6e75885210076d75885210076f65885210e6ee65885210e6ec658852139f6c65885210e66c6588521006ef6388521006ed638852139f6f53885210076d538852103dee718852103eef618852103fe76188521005ed70885210067f65d81210067c65d8121004ff75d8121014fe75d8121004fd75d8121014fc75d812100cfe73d8121004fd73d812100cfc73d81210067f53d81210067d53d81211967e52d81211967c52d81210f57e75981210057d75981210067f65981210067c6598121006fb60981210057f75581210f57c75581210067f65581210067c6558121005df73581210eddc73581210067f65181210067c65181211feef621812101efa6018121006f96018121004ff7558c21014fe7558c21004fd7558c21014fc7558c21004ff7458c210bcfe7458c210bcfc7458c210067f5458c2103edf7358c210d67f5358c210d6de5358c21006dd5358c210d6de4358c2103cfe7258c2103cfc7258c2103e7e5258c2103e7c5258c2103eee4258c2103ede3258c2103edc3258c210d4fc7158c210d6dc3158c21004ff7058c2101cfc7058c210d6df3058c210067f7654c211ae7e7654c210067d7654c211ae7c7654c210057f7454c211ae7f6454c211667e6454c210067d6454c211ae7c6454c213057f7354c210df5f7354c211ae7f6354c2100e7e6354c211af5e6354c2100e5e6354c210d67d6354c211af5d6354c210065d6354c2100e7c6354c210076f7254c2103d7e7254c2103d7c7254c211af6c7254c2103d6c7254c211ae7e6254c211af6e4254c211af5f3254c211af6e3254c211af5d3254c210fe7e6154c211af6f2154c211af762154c211af752154c211a67e6054c21004ff7650c2103cfe7650c21004fd7650c2103cfc7650c21
  | 19 => 0xca210ffce434ca21007cd434ca21005ef714ca21007e7714ca21007e4714ca2103eee614ca211fdec704ca2100cfe768c62103cfd768c62112e7e658c6210067d658c62100ede638c621006dd638c62103dee728c621005ed728c6213bf6c528c6210d4ff764c62111e7e654c6210067d654c6213b76c524c621005ed76c862103eed76c86210e5ee75c862103dec75c86213af6e65c86210076d65c862103def73c8621005ed73c86213af6f53c86210076d53c862103fe661c86213afe651c86213afe551c86211fdee70c86210e57e75d82210057d75d82210067e65d82210067d65d82210076c52d82210067e65982210067d65982210076c5298221006fb60982210067e65582210067d65582210076c5258221004ff7558221014fe7558221004fd7558221014fc7558221004ff735822100cfe735822100cfc73582210067f53582210067d5358221006ef52582211ce7e52582211ce7c5258221006ec52582210066c5258221006ee3258221006ed3258221006ef21582210e57e75182210057d75182210067e65182210067d65182210fdde7318221005dd73182210076c521822101efa6018221006f960182210f57e76d95210f67e76d95210147e76d95210057d73d95210067e63d95210067c63d952103d7e72d952103d7c72d95213a77721d95213a77421d95210067f73d95210067e73d95210067d73d95210047d73d95210067c73d95210067e43d95210067c43d95210067f72d95213a67e72d95210f67d72d95213a67c72d95210067f32d95213a67e32d95213a67c32d95213a67f71d95210f67e71d95210f67d71d95210f67c71d95210067f31d95210067c31d95213a67f21d95210f67d21d95213a67c21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f30d95210067c30d95213a67f20d95213a67c20d952100cfe76d8d210f57c75d8d210067f65d8d210067c65d8d210eede63d8d21004ff75d8d210067f75d8d21014fe75d8d21004fd75d8d21014fc75d8d210067c75d8d210147c75d8d210bcfe74d8d21004fd74d8d210bcfc74d8d210067f54d8d210ee7f53d8d210eede43d8d210ecfd72d8d212ee7e52d8d212ee7c52d8d210eedf32d8d2103cfd71d8d210eedf31d8d2101cfe70d8d21004fd70d8d210eedc30d8d210057f7558d210f57c7558d210067f6558d210067c6558d210eedc6358d21004ff7558d210067f7558d210047f7558d21014fe7558d21004fd7558d21014fc7558d210067c7558d210147c7558d21004ff7458d210bcfe7458d210bcfc7458d210067f5458d210ecff7358d21006df7358d210ee7f5358d210fcff7258d21006ef7258d212e67e5258d212e67c5258d21104ff7158d21006f77158d21004ff7058d2101cfc7058d210067f7654d210057e7654d210067
  | 20 => 0x67d70596210067c70596210067f30596210067c30596213e67f20596213e67c20596210e57e75d8e210057d75d8e210067e65d8e210067d65d8e213ddbe74d8e21005bd74d8e210fede63d8e210076c52d8e21004ff75d8e21014fe75d8e210067e75d8e210147e75d8e21004fd75d8e210067d75d8e210047d75d8e21014fc75d8e210bcfe74d8e21006be74d8e210bcbe74d8e21004fd74d8e21006bd74d8e21004bd74d8e210bcfc74d8e210067f54d8e210fcfd73d8e210fe7f53d8e210fede43d8e21006ed72d8e212ee7e52d8e212ee7c52d8e21006f671d8e2101cfe70d8e21004fd70d8e2100cff7658e210e57e7558e210067e6558e210067d6558e210fedc6358e210076c5258e21004ff7558e21014fe7558e210067e7558e210147e7558e21004fd7558e210067d7558e21014fc7558e21004ff7458e210bcfe7458e210bcfc7458e210067f5458e21006df7358e210fe7f5358e21006df4358e210fedc4358e212e67e5258e212e67c5258e210fedf3258e2103cfc7158e210fedc3158e21004ff7058e2101cfc7058e210fedf3058e210057f7654e210067f7654e210047f7654e210067e7654e210057d7654e210067d7654e210047d7654e210067c7654e210057f7454e210067f6454e211667e6454e210067d6454e211667c6454e210fd7f7354e210e75f7354e210fe7f6354e2100e7e6354e210fe7d6354e2100e7c6354e210076f7254e2103d7e7254e2103d7c7254e210076c7254e2103d6c7254e210ee7d6254e210ff5f3254e211ae7e6154e211af772154e211a67e6054e21004ff7650e21004fe7650e21004fd7650e21004fc7650e210e57e7550e210057d7550e2115e7e6550e210067d6550e21006df6350e2100edc6350e210ff9c4350e213d76c5250e21005ed768ca2103eed768ca2103f6f758ca210e5ee758ca2103dec758ca2103f6c758ca2103d6c758ca213cf6e658ca210076d658ca2103def748ca21005ed748ca21006ef648ca21006ed648ca213cf6f548ca210076d548ca2100eee638ca2100eec638ca210ff6f538ca210ff6d538ca21005ed718ca2103fe6618ca211fdee708ca2100cff764ca210057f754ca210e57c754ca2113e7e654ca210067d654ca2100ede634ca21006dd634ca210075d534ca2103f6e524ca2103f6c524ca21005f7714ca21005f4714ca210fdef764ca2100eef764ca2100cef764ca210076f754ca210e5ee754ca210e5ec754ca213c76c754ca210e56c754ca213c76e654ca210076d654ca21005ef744ca21005ed744ca21006ef644ca21006ed644ca213c76f544ca210076d544ca2103def734ca2103fcf734ca2100eee634ca210ffce634ca2100ece634ca21007cd634ca2100eec634ca210ff6f534ca210ffce534ca210ff6d534ca213c7cd534ca210074d534
  | 21 => 0x77150931005f471509313fcfe76905310bebe649053100cfe76505313f4fd765053100cfc7650531005df735053100ddc7350531006df648c531006dd648c5313ef5f548c5310075d548c5310075e528c5313ef5c528c53100dde718c53100fd6718c53100edf618c53100fd7618c531005dd708c531004ff75d8131014fe75d8131004fd75d8131014fc75d81310bcfe74d8131004fd74d81310bcfc74d81310067f54d81310067d54d81310667f53d81310667d53d813103cfe72d8131004fd72d81310067e52d81310067c52d8131066fa30d8131006fb60981310057f755813111d7c7558131005bf7458131115bc7458131005ef7258131005ec725813111d7e75181310057d7518131115be7418131005bd74181311e6df6318131005ee7218131005ed721813101efa6018131006f96018131004ff7558f21014fe7558f21004fd7558f21014fc7558f21004ff7458f210bcfe7458f210bcfc7458f210067f5458f2103edf7358f211067f5358f21106de5358f21006dd5358f21106de4358f2103cfc7258f2103e7e5258f2103e7c5258f2103ede3258f2103edc3258f21106df3158f2103eec2158f21004ff7058f2101cfc7058f21106dc3058f2103eef2058f210067f7654f211ae7e7654f210067d7654f211ae7c7654f210057f7454f211ae7f6454f211667e6454f210067d6454f211ae7c6454f213057f7354f2110f5f7354f211ae7f6354f2100e7e6354f211af5e6354f2100e5e6354f211067d6354f211af5d6354f210065d6354f2100e7c6354f2103d7e7254f2103d7c7254f211af5f3254f211af5d3254f211a67e6054f21004ff7650f2103cfe7650f21004fd7650f2103cfc7650f2110d7e7550f210057d7550f2100ede6350f21006dd6350f211079c4350f210ecfd768c72100cff764c72103cfc764c72100ede634c721006dd634c721005ef724c72103dec724c721107d4314c721004ff7558321014fe7558321004fd7558321014fc7558321004ff735832100cfe735832100cfc73583210067f53583210067d535832103e7e525832103e7c525832103efb705832103efb205832103ef820583210e57f76596210e67f76596210147f76596210057f73596210067e63596210067c63596210e76f725962103d7e725962103d7c72596210e76c725962103d6c72596213e77721596213e77421596210067f73596210047f73596210067e73596210067d73596210067c73596210067e43596210067c43596210e67f72596210e66f72596213e67e72596210067d72596213e67c72596210e66c72596210067f32596213e67e32596213e67c32596210e67f71596213e67e71596210e67d71596210e67c71596210067f31596210067c31596213e67f21596210e67e21596213e67c21596210067f70596210067e7059621
  | 22 => 0x823112d7c7558231004ff75582310067f75582310047f7558231014fe7558231004fd7558231014fc75582310067c75582310147c7558231004ff74582310bcfe74582310bcfc74582310067f54582310067d54582310467f53582310467d5358231046de4358231006dd4358231004ff725823103cfc72582310067e52582310067c5258231046df3158231046fa30582311e6dc305823112d7e75182310057d7518231125be7418231005bd7418231005ee7218231005ed721823101efa6018231006f960182310bcfe76d9131116be64d9131004ff75d9131014fe75d9131004fd75d9131014fc75d91311167f54d9131414ff73d9131414fd73d91314167f53d91314167d53d9131416bf43d9131416bd43d913103cfe72d9131004fd72d91310067c52d913100cfd71d9131116bf41d9131416dc31d913101cfe70d9131004fd70d9131116bc40d9131416df30d9131116bc645913140df77159131004ff7559131014fe7559131004fd7559131014fc75591313f4ff7359131006df73591313f67f5359131004ff725913103cfc72591310067c525913140cff7159131006f771591313f6dc3159131004ff705913101cfc70591313f6df30591310067f76551310067e76551310067d76551310067c76551313557f745513111f3f74551311167f64551310be7e64551311167d64551310be7c645513133d7f735513133d7d735513133e7f63551312e57c725513134e7c62551311173f425513133e7f615513133f77315513133f5c315513133f7431551313467c605513133f5f305513111d7e75d89310057d75d89310076c52d8931004ff75d8931014fe75d89310067e75d89310147e75d8931004fd75d89310067d75d89310047d75d8931014fc75d89310bcfe74d8931004fd74d89310bcfc74d89310067f54d89310067d54d89310fe7f53d89310fe7d53d8931006ef52d89312e67c52d8931006ec52d89310066c52d89310feee32d89310feed32d893101cfe70d8931004fd70d8931006ef62989310edf571989310057f755893111d7c7558931105f7715893103eee6218931006ed62189312e76c521893103e7f76949312e67e76949312e67d769493103e7c76949310057d74949310067f649493132e7e64949310067d649493132e7c64949312e57f73949311557d73949312ee7f63949312e57e72949312e76e72949312e67f629493103e7e629493103e7c62949314067f61949311577731949311575c319493115774319493118e7c60949311575f3094931004fe7690931004fd769093103cfc76909312e57f75909312e57c7590931006ef629093103eec6290931004ff7650931004fe7650931004fc76509310057f755093111d7c75509310073d5450931005df735093100ddc7350931006ef625093103eec6250931005f
  | 23 => 0x6f96018132126be64d92313fdf671d9231004ff75d9231014fe75d9231004fd75d9231014fc75d92314167f53d923103cfe72d9231004fd72d92310067c52d92313fcfe71d9231006f671d923101cfe70d9231004fd70d92310bcff7659231126bc6459231004ff7559231014fe7559231004fd7559231014fc7559231006bf74592311267f5459231126be5459231006bd54592313f67f53592313f67d53592313f6bf43592313f6bd4359231004ff725923103cfc72592310067c5259231126bc425923100cfc7159231126bc4159231004ff705923101cfc7059231126bf40592310067f76552310067e76552310067d76552310067c76552313557f745523112f3f74552311267f64552310be7e64552311273e64552310be3e64552311267d64552310073d64552310063d64552310be7c645523133d7f735523133d7d735523133e7d635523133f5e43552312ed7c725523134e7e62552311273f425523133e7e615523133f5f315523133f77315523133f7431552313467e605523133f5c3055231125df7650e310bedf7650e310bcdf7650e314275e7550e310075d7550e3100ddf7450e3100f9f7450e310bede6450e311279e6450e310be9e6450e310079d6450e310bedc6450e311275f5450e311275d5450e314275c5250e311279f4250e31005df7150e31007d77150e31007d47150e3100ede6150e3100fd66150e311279c4150e311e5dc7050e311279f4050e3112d7e75d8a310057d75d8a31125be74d8a31005bd74d8a310d5f671d8a31006ef6298a310057f7558a3112d7c7558a31004ff7558a310067f7558a310047f7558a31014fe7558a31004fd7558a31014fc7558a310067c7558a310147c7558a31004ff7458a310bcfe7458a310bcfc7458a310067f5458a310067d5458a310ee7f5358a310ee7d5358a310eede4358a31006dd4358a312ee7c5258a310eeee3258a310eeed3258a31004ff7058a3101cfc7058a3103eee6218a31006ed6218a310fdf67118a3103e7f7694a312ee7e7694a312ee7d7694a3103e7c7694a310057d7494a310067f6494a3132e7e6494a310067d6494a3132e7c6494a312ed7f7394a311557d7394a312e67d6394a311575e4394a310075d4394a312ed7e7294a312ef6e7294a3103e7e6294a312ee7d6294a3103e7c6294a3141e7e6194a311575f3194a31157773194a31157743194a3118e7e6094a311575c3094a3103cff7690a31004fe7690a31004fd7690a312ed7f7590a312ed7c7590a310bebe6490a31006bd6490a3103eec6290a31004ff7650a31004fd7650a31004fc7650a310057f7550a3112d7c7550a310073d5450a310079d4350a31005f77150a31005f47150a310bcfe769063100cfd769063100dde7390631005dd73906310079d4390631006fb60982310057f755
  | 24 => 0xf5450d321375d5450d32007cf7250d3203dde7250d3203ddc7250d32007cc7250d3200edf6250d3200fcf6250d322ff5e5250d322ff5c5250d321379f4250d321379c4150d321379f4050d32455ee769093203eee769093203f6f759093203f6c75909320076f659093244f6c659093242ded74909320beee64909320beec64909321376f54909321376d549093203fcf739093200dee739093203dec739093203fcc739093203eef639093203fcf63909324476f5390932447ce53909324476d539093244fcd53909320074d5390932447ce4390932137cd4390932005ee7190932005ed709093200cfe765093242cfd765093200cfc76509320067f655093243e7c6550932005df735093200ddc73509320075d53509320079d435093203f6e525093203f6c525093203fcc32509320beec765093200cec76509320076f65509324376c6550932007cf735093200dee735093200dec735093242fcc735093203eef635093203fcf635093242f6f535093242fce535093242f6d5350932437cd53509320074d535093242fce4350932137cd43509320078d43509320067f65d85320067c65d85320075d53d8532004ff75d8532014fe75d8532004fd75d8532014fc75d85320bcfe74d8532004fd74d85320bcfc74d85320067f54d85320067d54d853203cfd73d85321067f53d85321067d53d8532106ed72d85324067e52d85324067c52d8532106f631d853201cfe70d8532004fd70d853213d7e75985320057d75985320067f65985320067c6598532135be7498532005bd74985320075d5398532006f761985320057f755853213d7c75585320067f65585320067c65585320075d53585320067f65185320067c65185320075d5318532006f56118532004ff7518532014fe7518532004fd7518532014fc75185320bcfe7418532004fd74185320bcfc74185320067f54185320067d541853203cfd73185320d67f53185320d67d53185320d6de4318532006dd431853241e7e521853241e7c5218532006ee4218532006ed42185320d6f5311853201cfe7018532004fd70185320067f65d81320067c65d81320075d53d8132004ff75d8132014fe75d8132004fd75d8132014fc75d81320bcfe74d8132004fd74d81320bcfc74d81320067f54d81320067d54d813203cfd73d813209e7f53d813209e7d53d813209ede43d8132006dd43d81323267e52d81323267c52d8132006ee42d8132006ed42d8132004fe71d8132004fd71d813209efa30d813213d7e75981320057d75981320067f65981320067c65981320075d5398132006fb60981320057f755813213d7c75581320067f65581320067c6558132005bf7458132135bc74581320075d5358132005f77158132005f471581320067f65181320067c65181320075d531813201efa6018132
  | 25 => 0x95324867c42d95321567f32d95324867e32d95321567d32d95324867c32d95320067f71d95320067e71d95320067d71d95320067c71d95320067f41d95320067c41d95321567f31d95321567e31d95321567d31d95321567c31d95324867f21d95324867c21d95320067f70d95320067e70d95320067d70d95320067c70d95320067f40d95320067c40d95321567f30d95321567e30d95321567d30d95321567c30d95324867f20d95324867c20d95320bcfe76d913213d7c75d91320067f65d91320067c65d9132136be64d9132004ff75d91320067f75d9132014fe75d9132004fd75d9132014fc75d91320067c75d91320147c75d91321367f54d913203cff73d913203cfd73d91324467f53d91324467d53d9132446bf43d9132446bd43d913200cfd72d913247e7e52d913247e7c52d9132136bf42d9132004fe71d9132004fd71d9132136bf41d913201cfe70d9132004fd70d9132136bc40d91320057f755913213d7c75591320067f65591320067c6559132136bc6459132475ef7259132004ff75591320067f75591320047f7559132014fe7559132004fd7559132014fc75591320067c75591320147c755913242cff7359132006df735913242e7f5359132474ff7259132006ef72591322fe7e52591322fe7c5259132004ff7159132004fc7159132004ff705913201cfc70591320067f76551320057e76551320067e76551320047e76551320067d76551320057c76551320067c76551320047c76551323557f745513213f3f74551321367f64551320be7e64551321367d64551320be7c645513233d7f735513233f5e735513233d7d73551320075d735513234e7f635513233f5e435513203d7e725513203d7c725513233e7f62551321373f425513233f6f325513234f5e325513234f5c325513233f6c32551323467c605513213f5f7654d320165f7654d3213f5c7654d3203d5c7654d320165c7654d3203c5c7654d320075f7454d320055f7454d3246f5e7454d320075d7454d3246f5c7454d320075f6454d3246f5e6454d320075d6454d3246f5c6454d320075f7254d320074f7254d321af5e7254d3203d5e7254d3213f5d7254d321af5c7254d3203d5c7254d320074c7254d3200f5f6254d3200e5f6254d3200f4f6254d3246f5f4254d321af5e4254d321af5c4254d320075f7154d320075e7154d320075d7154d320075c7154d3246f5f4154d3246f5c4154d320075f7054d320075e7054d320075d7054d320075c7054d3246f5f4054d3246f5c4054d3203ddc7650d320bedc7650d3203cdc7650d32465df7550d3245f5e7550d32465dd7550d320075d7550d320055d7550d320075f6550d3245f5c6550d3200ddf7450d3200f9f7450d320079f6450d320bede6450d320bedc6450d321379c6450d320be9c6450d321375
  | 26 => 0x14fc75592320067c75592320147c755923203ebf74592321467f5459232146be5459232006bd545923242e7f535923242e7d535923242ebf435923242ebd435923203cfe725923203cfc725923203e7e525923203e7c525923203ebe425923203ebc425923203edf325923203edd3259232004ff7159232004fc715923203eec2159232004ff705923201cfc705923203eef20592320067f765523203d7e765523234e7e765523203c7e76552320067d765523203d7c765523234e7c765523203c7c76552324957f745523214f3f745523234e7f64552320be7e645523234f3e64552320be3e64552321467d645523234f3d64552320063d64552320be7c645523233d7f735523233d7d735523233e7d635523203d7e725523203d7c725523234e7e625523234f3f425523234f6e425523234f5f325523233f6f325523234f6c32552323467e6055232004ff7598632014fe75986320067e75986320147e7598632004fd75986320067d75986320047d7598632014fc75986320bcfe7498632004fd74986320bcfc74986320067f54986320067d54986320fe7f53986320fe7d539863203cfe729863203e7e529863203e7c529863203eee429863203ef671986320fef5319863203ef7219863203ef4219863201cfe7098632004fd7098632004ff75586320067f75586320047f7558632014fe7558632004fd7558632014fc75586320067c75586320147c7558632004ff74586320bcfe74586320bcfc74586320067f54586320067d54586320ee7f53586320ee7d535863203cfc725863203eec725863203cec725863203e7e525863203e7c525863203ef771586320eef6315863203ef7215863203eec215863203ef42158632004ff705863201cfc705863203eef2058632004ff75582320067f75582320047f7558232014fe7558232004fd7558232014fc75582320067c75582320147c7558232004ff74582320bcfe74582320bcfc74582320067f54582320067d545823207e7f535823207e7d535823203cfc725823203e7e525823203e7c525823203eee4258232004ff7158232004fc715823203efb705823207efa305823203efb205823203ef8205823248d7e76d953213e7e76d95320147e76d95320057d74d95320067e64d95320067c64d953203d7f73d95324875f73d953203d7d73d95321575c73d95321575e43d953203d7e72d953203d7c72d95321576f32d95324875e32d95324875c32d95321576c32d95320067f74d95320067e74d95320067d74d95320047d74d95320067c74d95324867f73d953203c7f73d95321567e73d95321567d73d953203c7d73d95321567c73d95321567f43d95321567e43d95321567d43d95321567c43d95321567f72d95324867e72d95321567d72d95324867c72d95320067f42d95324867e42d
  | 27 => 0xd75d85430047d75d8543014fc75d85430bcfd73d85434aedd73d854340e7f53d854340e7d53d854303cfe72d8543006ee72d854303cee72d8543004fd72d8543006ed72d8543004ed72d85430067c52d854340ef631d854340edc31d854301cfe70d8543004fd70d854340edf30d85430067e65985430067d65985434179c4398543006f761985430067e65585430067d65585433f79c435854315d7e75185430057d75185430067e65185430067d65185433ff9c4318543006f56118543004ff7518543014fe75185430067e75185430147e7518543004fd75185430067d75185430047d7518543014fc75185430bcfd73185433fe7f53185433fe7d531854303cfe7218543004fd72185430067c52185433fef5311854301cfe7018543004fd701854301cfe76d814315d7e75d81430057d75d81430067e65d81430067d65d814335f9c43d8143004ff75d8143014fe75d81430067e75d81430147e75d8143004fd75d81430067d75d81430047d75d8143014fc75d81430bcfd73d814335e7f53d814335e7d53d814303cfe72d8143004fd72d81430067c52d8143004fe71d8143004fd71d814335efa30d81430067e65981430067d65981433679c4398143006fb60981430067e65581430067d655814330f9c435814315d7e75181430057d75181430067e65181430067d65181434a79c4318143005ee7218143005ed7218143005f67118143005f5711814301efa6018143006f960181430067f7458e520047f7458e520067e7458e520067d7458e520067c7458e5203e7f7358e5203e5f7358e521567f4358e521567e4358e521565e4358e521567c4358e5203e7e7258e5203c7e7258e5203e7c7258e5203c7c7258e5203e7f4258e5203e7e4258e5203e7d4258e5203e7c4258e5203e7f3258e5203e7e3258e5203e5e3258e5203e7c3258e5203e5c3258e520067f7158e520067e7158e520067d7158e520067c7158e520067f4158e520067c4158e521567f3158e521567c3158e5203e7f2158e5203e7e2158e5203e7d2158e5203e7c2158e520067f7058e520067e7058e520067d7058e520067c7058e520067f4058e520067c4058e521567f3058e521567c3058e5203e7f2058e5203e7e2058e5203e7d2058e5203e7c2058e522fd7f7650e5203d7e7650e522fe7e7650e522fd7d7650e520067d7650e520047d7650e5203d7c7650e5249d7f7350e522fe7f6350e522ff5e6350e521567d6350e522ff5d6350e520065d6350e521573e4350e521575c4350e521571c4350e522fd7f7250e5203d7e7250e5203d7c7250e522fe7e6250e522ff6e6250e522ff5f3250e520057f7150e520057c7150e521575c3150e520057f7050e5218d7c7050e521575f3050e52004ff75592320067f75592320047f7559232014fe7559232004fd7559232
  | 28 => 0x81530b55d73981531b67f63981530cf5f63981531ad7e72981531a76e72981530056e72981530057d72981531a76d72981530056d72981530067e62981530067c62981534df5f32981530057e71981530057d71981530067e61981530067c61981531a57e70981531a67f60981530077b60981530057f74581531657e74581531657c74581530067f64581530067d64581534d57f73581530075f73581530cd5f73581534d67f63581530b75f63581530057f72581531ad7c72581530067e62581530067c62581534d75f32581530057f71581530057c71581530067f61581530067d61581530077b60581531a67e60581534cd7e76181531657e74181530057d74181531a57c74181530067f64181530067d64181530157f731815300d7e73181530157d731815300d7c73181531b67f63181534c75f63181531ad7e72181530057d72181530067e62181530067c62181534bf5f32181530057e71181530057d71181530067e61181530067c61181531a57e70181531a67f60181531a77a60181531a67d60181530077960181531a77a30181534bf7930181533557f765954315e7f76595430147f765954333d7f73595430075f73595434b55f735954333f3e435954333f5c435954333f1c43595430076f72595432fd7c72595430076c72595430056c725954333f5f325954333f5c315954333f5f305954333e7f735954333c7f73595430065f735954333e7e435954333e7d435954333e7c43595430067f72595430066f72595430067e72595430067d72595430067c725954303c7c72595430066c725954303c6c725954333e7f325954333e5f325954333e7c32595430067f71595430067e71595430067d71595430067c715954333e7f315954333e7c31595430067f70595430067e70595430067d70595430067c705954333e7f305954333e7c305954303cfe76d894315d7e75d89430057d75d89430067e65d89430067d65d89434779c43d89430076c52d8943004ff75d8943014fe75d89430067e75d89430147e75d8943004fd75d89430067d75d89430047d75d8943014fc75d89430bcfd73d89434767f53d89434767d53d8943006ef52d89432fe7c52d8943006ec52d89430066c52d8943476ee32d8943004fe71d8943004fd71d894301cfe70d8943004fd70d89432fd7c75989430067e65989430067d65989434479c4398943006ef62989430057f755894315d7c75589430067e65589430067d655894342f9c435894315d7e75189430057d75189430067e65189430067d65189434579c431894303eee6218943006ed62189432ff6c521894315d7e75d85430057d75d85430067e65d85430067d65d854340f9c43d8543005ee72d8543005ed72d8543004ff75d8543014fe75d85430067e75d85430147e75d8543004fd75d85430067
  | 29 => 0x57d71989531a57e70989530057d70989530057f74589531657e74589531657c74589530067f64589530067d645895352d7f73589530075f735895314d5f735895352e7f635895313f5f63589530076f62589531ae7e625895352f5f32589530057f71589530057c71589530057f70589531a57c70589535257e76189531657e74189531af3e74189531653e74189530057d74189531af3d74189530053d74189531ad7c74189530067f64189530067e64189530067d64189530067c64189530157f731895300d7e73189530157d73189531af5d731895300d7c73189533067f631895351f5f63189531ad7e72189531ae7f621895303e7e62189531af6e621895303e6e62189531ae7d62189530076d62189530076f42189531af6c42189531af5f32189531af6e321895348f6d32189530057e71189530057d71189531a57e70189530057d70189531657e74d85530057d74d85531657c74d85530067f64d85530067d64d85530157f73d85530157d73d85535067f63d85535175f63d85531ad7e72d85530057d72d85530067e62d85530067c62d85535075f32d85535077631d85535077531d85531a57e70d85530057d70d855350d7d76985531657e74985530057d74985531657c74985530067f64985530067d64985534f57d73985530075d739855311d5d73985534f67f639855312f5f63985531ad7e72985530057d72985530067e62985530067c62985534f75f32985534ed7e71985530067f61985530077761985531a57e70985530057d70985530057f74585531657e74585531657c74585530067f64585530067d645855350d7f73585530075f735855312d5f735855350e7f635855311f5f63585530057f72585530076f72585530056f72585531ad7c72585530076c72585530056c72585530067e62585530067c625855350f5f32585530077761585530067e61585530057f70585531a57c70585535057e76185531657e74185530057d74185531657c74185530067f64185530067d64185530157f731855300d7e73185530157d731855300d7c73185534ee7f63185534ff5f63185531ad7e72185530057d72185530067e62185530067c62185534ef5f32185534f57e71185530067f61185530077661185530067d61185530077561185534ef7631185534ef7531185531a57e70185530057d70185531657e74d81530057d74d81531657c74d81530067f64d81530067d64d81530157f73d81530157d73d81534ce7f63d81534e75f63d81531ad7e72d81530057d72d81530067e62d81530067c62d81534cf5f32d81530057e71d81530057d71d81530067f61d81530067d61d81534cf7a30d81534cf7930d81534d57d76981531657e74981530057d74981531a57c74981530067f64981530067d64981534dd7d73981531a75d739
  | 30 => 0x700000000000002000000000000020014002000c00000040010000003000c00400000000000000000c00000040000000000000000000000010008001000000500040000000000000000000000000000001000800200040000000000000400400180000000001000c001000000000000000004000000800000040010000000000000100000000000001000400000000020000001000800600040000010001000000000000000000001000400000080010008005000c0020000002000000000040020000001000000000000000000000000400100040010018000000000000000000000000001800b000000000000040000000000800200040000000001001000300000030000001000000200080020000000000800000080020004000001400100080035557e76d915333d7d74d91531667e64d91531673e64d91531663e64d91531667c64d91530157f73d915300d7e73d91530157d73d915300d7c73d91533567f63d915354f5f63d91533573f43d91533573d43d91531ad7e72d91530057d72d91533575f32d91530057e71d91530057d71d91531a57e70d91530057d70d915333c7d74d91533567f73d91533567d73d91530147d73d91533567f43d91533563f43d91533567e43d91533567c43d91530067f72d91530067e72d915303c7e72d91530067d72d91530067c72d91531667f42d91531667c42d91533567f32d91533565f32d91533567e32d91533567d32d91533567c32d91530067f71d91530067e71d91530067d71d91530067c71d91531667f41d91531667c41d91533567f31d91533567e31d91533567d31d91533567c31d91530067f70d91530067e70d91530067d70d91530067c70d91531667f40d91531667c40d91533567f30d91533567e30d91533567d30d91533567c30d91535457f76591533557f74591530073f64591531667e64591531667c64591531673c645915333d7f73591530075f735915353d5f735915333e7f635915315f5f63591530057f72591530076f72591530056f72591531ad7c72591530076c72591530056c72591531673f425915333f5f32591530057f71591530057c71591530057f70591531a57c705915303c7e76d89531657e74d89530057d74d89531657c74d89530067f64d89530067d64d89530157f73d89535375f73d89530157d73d89535267f63d89535375f63d89530076f42d89530076c42d89535275f32d89535276e32d89535276d32d89530057e71d89530057d71d89531a57e70d89530057d70d895352d7d76989531657e74989530057d74989531ad7c74989530067f64989530067e64989530067d64989530067c64989531557d73989531af5d739895313d5d73989533067f639895314f5f63989531ad7e72989531ae7f62989530076f62989531af5f32989530057e7198953
  | 31 => 0x7000000000200070010000000000200000070000003000000100040020000007000c000002000000000010008001000000000000010014005000000600000000000001000000100240000000007000000100040090000001000000000040000000001000800100040020000001000400100000030004004000400000000000004005000c0020000000000000100000000000002001c000000800000040030000000000c0000008000001800000100010000000000000200000010004003000000000000010000001001400000000000008003000000000040060000000000000100040000000004000c000000c0000008001000000100040000000000000000000000050004001000400000000000004000000000e00080000000000000000000000000000000000000000080010000001000000100080020008000000c000000c001000400100000000000001001000000040000000000000400400040000004000000000000000000004000002000000000050004000000000000000000014004000000000000010000000000000000000000008000000000100000000004000000000200000000000000000000100000040000000000400300080010018004000400000000000008001000000400000020000002000800000040010000003000400000040050000001001400300000000004001000400000000020000000000000000040000010002000000200000000000003000c00000040000000000000400100000000014000000c0020004001000400000000000010000001000000140000000000000000000140000000000000000000000020000000001000000000000000002000800000200000000004000000000000030000001000400200000000008002000000200000010008003000000000000040000000000000000000000008000001c000000800300000020000003000400000140020004000001000000080000000000000400000040010000003000c0000000001001000100080000000000000000100000000000006000800200000040000000000000000000050004000000400000000000004000001000300000000004000000000100000000000000000000500000030014000001c002000400000040010004000000000000000010000000000400000040000004002000400000100000010002000000100000020000002000c00000000010004000000000000100030000001000000000040010000001000c002000000200080000000001000000000000000008000000000000000000000002000000100000010000001000000400000010000001000800000000010000000000800000000010000002000c004000000200000010000000000000000080000000004002400100080000000000000000000000110000
  | 32 => 0x14000001000000000020000002001c00100000000000000000000200000000000000000c00000000010000000000000000040010000000000000100000010000002000000000000000000000000000000140000000003000800500000030008002000000000000010000000000c00000000050004000000c001003c0010000000000000000000010004000000800100080050000000000000000000040000000000000100000000004000000000200040000004003000000300000000000000001000000000000000000000c0000004001000000000000080000000000000100000000004000000800400000000008004000000000040000000000000000000000010008001000800100080000000001000c00500000000000000000800000000000000000000000100000000000000000000200040020000001000c0010004002000000000000060000000000800300000020000000000000000080010000000000400800080050008004000000000000040000001000400100200000004001000000300000040000000000000e000400300040010004001000000000040000000001000000000000000008000000c000000000100000000000001000c000000800000000010004001000000200000000000000000400000040040000000001c0000000000001000100000010000001000000100040020000004001400000080010000000000c001000000000000020004000000000000040090000001000000000000020000000000000100080010008000002400000040000000001000000b000c0000000000000000000000020000002000800700040000004000000000100000000000000000c00000000000010000000000000000010008002000000300000010004006000000000000000004000000400100000000004001000400100000000008001000800000040000000005000000000000000000000000000000000020000000000400100080010000000000000300040000000001000c0030010001000000000080010000000000400000040000004000000c0050000000000400300000010000001000c004000000200040000004000000400200000010000007000400200000000000000000000000000000000000000000700000000004004000c00100000000004002000000000000020000004000c000000c000000000100040040008000000800000000000000002000c0000000000000000400000000000002000c003000000000080000004009001c000000000100000000000003000800000000000000000000c000000000100040000000000000c001000800000080030000001000000000000050000000000000000000010000004000400100040010000000000400000140000004002000c000
  | 33 => 0x2000000000180000000000000000000100010000000000000000040010000001000400000080000000000000800000000030000000000000000040050000006000400500080000004000000400000000000004001000400000280010000000001400000000000000001000000000000040000000000000400040010010002000000100040000000000000c0000000000000400100040000000002000c0000000000000400800180020000002000400400000000000001000c00000000000008000001000000000000004001000000000040000004002000800000000020010000000400000140000004001000400200000000000000001c00000040000004000000800000040000000002000400300240000000000000000000000000008001000000000100000000000000000000000010004001001000100040000018005000c000000c001000000000040050000002000c0000004001000400000000000014001000c00100000000000003000000100080000008000001c0030024000000000200140020008002000000100000000000005000400000080000004000000400100000000000000000000000000010000001000000300000000000000000800000000040008000000c001000c00100040020050001000400200040030000006000000000000000004001000800000040000000001000000400080000000001001000300000010004000000000100000030004000000000000000020000000000400000040050000001001000000000000000000000000000000000000006000000300040000008000000000100000000018000000400000100010000000000000000000000000005000000500000030000004000000100000000004001000000000040000000000000400300000000000002000000000000000000000000400000000000000001000000000080000000002000c003000400000040020004000000000500040060004000000000000000020018000001c000000000100000030000001000000500000000004000000000000100030000003000000100040000004000001000000100060000000000c0030004001001000100040000008001000c00000000010000004000000300200010000000000000000000000000000000000000040000018003000000000000010000000000400400000010000000000000000180010008001000000000000020000000000800000000010004000000c000000000000080000000004001400200000000000000000000100040000000000000c00400080010000001000400100200010000001000000000040010000000000800800000000004001000000000000000000000000000400140010000004000000000000020000000000000000080000018000000000000000010008000000
  | 34 => 0x113c78b4000000000042a800000000000000000564800000000320160c9600000000000000000000064223c9000162c0f4800000001e80000000953c0001ad09ce4ed000039180000000e5f000000000000000001ca8000157a0000000000000026480002c7000000000000001ff18a88000000161a000180800000007ab800076589522468000635800029b20e600019fb2eb0000000149e0000000a1d961c000000000000000000fa4622c00007bc5bc0000000000000000000000000000000000000000006224afd0000000943800000019520000562088a79e3308b026161fc850f1f9a00000009ef213e52985f447ec00000002e0000000047489b8908000000004c4000186c2310a0e000235a000000085f90e4a340000000244c0328000767483a4b58b5a000000000000000000be800000000000d1c00000000000021935800000019b2000000092000b10000000469c0008c2800027c0a120000000000000000023800000000172000000000000000c1c000246230b870300000001b88000000000000000000000d1600000000000da630a0b90828800000010c806d000000000000000cc828d80000000236000000000000000000000139800000000003910000000264e19e8e3d8dd800000000000001d06000000075d400099b800057b1a94000246c8a50000000000000000003e21b2e6a2800048b800000005d03a100000001b2600011580000000000000000000002d78000000067040f0000000061900022180000000000126c9160000000061187a98a9000000000012ac00000000001a122b70000915819a8d30000000000000000000000a3e000000081580000000000000000000000000001b6500000000000000000000000000000000000000000000000001f28000000000015800001c057ba0000e8c00000004b00b8e000239850a0d824b40dfe46280000000d3c98c800052100009fc00009ac0000653800000000000002664000000000000000000000000000034c0000262800000000000000000000050400000005f380003ca1f5b00002b00001a6e0254000000000000000002de002c680d9047f0a62c0001a5400000000001e3e00000004bcc00000000e74198000000000031b40000001ede0000000000000017d404200000004719274000c00200000000000000000c003000c000000c002000000f00040000000000000000000100040004000000000000040000004001000c00000000010008000000400000140000010001000c00200040000000000000000000000010004001000800200040060000000000000300000000000001000000000000000008000000400100040000000000000c00000000000000000000000000040050008003000000000000000008000000000000000000000004000000
  | 35 => 0x789ba800000012e00000e64000000000000002260000000074d0000000000000049940000001b100000000000263c00010b21338000000030600000000c3400069c00001f3000063c8000000000000004170000000000000008f0cae366800000000000000f97026993674e80008729c7e00000000001236445800050d96a8000063261727dc00018b67ac1ade000000000000000001bdc0001fc700008882e1000000006460000000000000000000004618000000000088f000000011d963a894600000000000000690209600000cc0000cd400000000000000000000007286f4000000000000303ad80000000000008c16e0000b6c00024ec00003960000000000173c00018f46a99d742f08000a22800000000000000000000000000000001f600005f127e24d0800006e4000000209000000003e81dfe0000000000000054f800000000000000147490800075a4000000010600003c809e844031a93531cb00000000000539000000000000000000000041552a80000001aa700000000000000000000000000000000b4300012ef1370000000000000000000000000303800087393394f19d2c000000083413a7000261e0000056000000000014c61d85ffc00000000000000000000000000005fe400000008ae0000000000000000000000000000000000023790a746a00002f506820000000711833a00000005080000000000000021ec393000000004d7000000021900000bd8000000000000011c5549000000019440ad800000013980000000000000000000000000000000000073c9d0a64080000000a028ad80004098f20000000046d800000000000000000000000000021d800018ee000000000011f9947879a743175a00000000000e3100000000001d34236978b67614ae88c000000000000000000000239a97f40001f781160000000a380000184967800000003cd8000000000087300000000000000209c0001359000000083f893e134000000000000002820000000000000000000000000000000000000000000000000000000008cc9dec1a80ece00000000000000000000000000000001cc06434dbc1d80dae00000000001ca400007f6000235269e0000000000000010641c08c0416b4fca6b3034005c633c00001a2000011e0754000000156057f80000000000000074fa0c0000446400029780000000000898000000000000000000000050e7948000000000061800007c9000000000000002546831000000000000000ad000000004d380000000000000000093c800021f5110776800000000001ab0ff4885d79c6e60000000000016780000000000000026e0001f3a28b00006b50000000000000000000001b6400000000000000000000000000000000e5e00000006d00000000000068b800000000000560000000000000
  | 36 => 0xde8da00000ef800000000000000395000000000001ba40000000000000000000000004968000000000000000009f90e3307d00000000000000000018bc0008628dea0000000000000000000000000000000056c000080e0000000000000072080000000000000000019780000000000985c0000001784000107c00000000000dca000000000000000000000000095e00000006b61cd6716800041482ec000000032ad8ca8c68846000000079517c089200000001d9032c8000643a006a088b210000000451800000004381724000000000000000000000000100dc3000002de0001c48000100e4c2000007080000000000701800000005a4000000067680001e41dc6000146a00000c46ae9fb869316f01d9800000023900000000000000000000007d080000000000000000088310b600000000001aac29280000000000282911e26111781af86169f380000000000000000000000000000000000062d4f080006ee0000049c000000000000000000000000000000000000000000000000201e00000e43ce800000013ea000000000000080000000000000000000000000000000000065a25390000e2e5a4800000008f28fa22a86ce0f907d6800040c800000027a4000258c80407da000032e000000000000000000000132255402340000000000a3781483dd962a30987aa000000000022d60000000962000000002dc000000062484162a6a558000000030900000000000037c0003f196ba00000000000000000227c00018fb000057aa128000000000000000000000000713000000000008db20688ee815a000000000000000fca2ec76880007c209d9000183087487960000000000000086e0f800000a460000000000188e00000000751eb1000000006385035d4a02d1d744360001f6802400000b313ae000246a000230c0000000000000014a8000000284800000000000000000000000000000000000000151100000000001e760d9a6b24e7a25800000005bb0af40000000000018100000006150bbe218800007800009524000000254c00012ea000000000000000000000000000000000008b5000017680008efc00078a62de000000000012944dc90ce6f28df11bb400000008cc00000000000000004000003d81f6000250c68424400002188000000088d9267000000000000000000fec00000000000000000000083094cb4cd1d2295f80001ee0e9000024ca0001544000226618a0d6c59a1b665564000000000000000000000000969ce0a200046e19300008a580009fda64a4ee83ca1f94000000146e000075a00009e2000000031580000001c0200000006dc845a875264c000231e367000000000000001e065c723eb4dd04e81d70d9400000000000b007c600003c724d303a871000025ce000000073800000002568502a7027c38f
  | 37 => 0x1f8000000055395347fea56400000000000000091000000000000000000000075400000002fc8000000000044a1f7900008ca5b4949aa308cb40000a8e00000000000000000000000000008e38ac72ce00001d263500000a09000000043400000000f8600015d000000000000cf68b08000000000000004283299a7280b130c0000000000164e000000005f000098280000000000000000000014d40000000000006223bc00044100000000a7a00000000122426000000000021fe9318000000000000023843e2800067b0000000000078acf4800004704b914b800000000000000000000000000005bf87510001ff2000000000000000001fc40001ca600000004cdc0008f080005d956aa000010a057a4e83aa00000000000664800015d00000000bca0000000000010e53b400000004f084980006c100008c4871400000000002370000000000000000002618000000030dc000254089045200000002274000256a0000000000000000000000000000000000000019c2000117e0000000000000000000004299e6c000000000008f0000000000000002fb1862785000000000003b3547c000196a13bd4e8000000000000000001c7812d03cc020000050a9170000044892928d22ddc00040240000000000000000000000000000000a35000000000000000000000100a000062e00019960000000000000000008f60000000000000083a40005e5800000000000000344655c000347800000000009af000037e0000000000000000000000000000000000000000000000000085400000000000000000260e70b800000000000000000000000039ec0000000000000000030200007c6800077f000029e000000000007df000000012920001bfe000000000000007de800000000000000000000000019400002c30188000000000000005a700000001de066380008b6903400000005e880007d0000000009420000000000000083d00dc10a50d8000143a24f0000980c0000001a644b28000000142c66e204806d80000000c0c000000000000000000fda8610d0874fa5ba877234053f8b7c000000048e40001ab400000000000000000000000000000000001aa2000000000020eb00000003059a050000000000000053c80001a223d20000000000000000000000001cbc000000000000000000db03a5834200000001d60000000000029417ee26e8000000253c00012a800000000000000000000073b00000000af000000000000000027262000000000000000000000000000864589d924bf000000022700000000000000000000007808bee0000000000000000000000000000a280000239800000026881118000000000085680a60000c428f7800000000000d2817907f8000109e37c1a30000000000000000000000000000000000008dc00000006
  | 38 => 0x1e466400000000123e1b5c00000000000000000032103d210000000000000000000000000000000004250d28706d2087909e12000002235790863b5451a000000000000000000d18000271260da254000222c48c47c60df8a060000000000000003c800021f80003d680002d5000033600002bd8ede00000008f41d6a0000000000211a00014e7000165a000000000000000001d32861800068049bc3e51f8e00007680000dffa1691b411a531e000000000005be29d8000000011d00000000001bbc319800000000000001d4600023ea05d4d9671e879e87c13f400025aa00000000b2800000017da00000005488000000000000000004388a6400026448b48000000000000010410000000000000000000001dd800008d12ce76a00000000000746151c66d8f7400000000001ebb00015a60000000000000000013680000e01000000020f800000000000000ef2000056a000000000000009eb90a44ce800000000000000000836e86a0000000000008c06a8000000000084c8000000000000000000000000000000000000000000000645c00000000003be800000000008390e5807987ae00003503a380000001744000000000000003818000000216a000000077c879c5e4000094c62cc94e8336717000000000000000000548400000000000000a320001a3a00000000000000000000000027e800015438cc2150000000000000009d10000000000000000000000000000061a4f689f6000000000000009558e7f000000000000000000000000216b000000000000000001dc8000148800000001d4800000000000000000000000061f93f60000000000000000000000002151a180000000000000000000001e0e7c59eb400020b4646000030d40ce0e0d53c0bb8000000200e147899b000000000000000000000000000000022fe00a26ee0f1800000000000002290431095616e12cc7259d7600022b8a2b977800000000000000000000021380009330000000000000000000002594019043a00000000000b4200000000001404000000000000002698000000000000009de207a30200000000968000000000000000000001c601f8a652000000000000000000000000035c0f59f520001c5f00000000000000000108c00026a000000000000c1200000008b8069a00000008b200001d8800000000000001c2f000078802b000019600000000000000000000002250001eba00012240001ac345d80007cf206a000000052d80000000c9255b21ae1f986929cd91e6000176a00009a86780ff39f79b60a398000000051c29a8000230000047745280000000825259e00002f2000000000000007bb030c0001e4c000183c000000000024600000000000224a906000000000000000000000000000000005d9800008180000d95
  | 39 => 0x45c73080000000000898800000000003af13b0000000000000000001d9a000000000000000001ec400000000000000000000010f83a30ee835500000ee32a800000000006619b942770000000000000000000000000000000012f50f1000000017980003cf84986c716c40000000048c000000000000000000001c32000000000000000000000355000000000005d780003ab920c0cf8000000000070e8000074007c33100006ae038a39e000045d10ae0000000000000000000000000000000000000000006a6021100017de6e49c6280880000000000000243e00019df000000030d800000000009c2263800000000000000000000000000000000000270c5760cf00000000daf99700000000000000000000000000000000000067600000000000b4c00000005438000000195c7eea1fa21800009f280000000000286800000000000830b220000000000000000000007bba43a000000000000007dd4d64000000090694c37f542150001ba077598c052725cb00000000000000000000000000006df059c2cec000000000055000005888000000000000000000000000000000000000000001b2000003670000daa000000000000002cd206600028d6000000080096503238000000000080f800019080000000000000000000000004c080009f80000000070800000000000000976800000021b62560000000000000000007e28b065e0800000023062640e414020000000000000000000000000325d6bc00006ca000000000000000000ff60000000000000000000000000000000000003580008d5800000009800000000000000021600000000000606800000021e112580000000000000000000000000000000000000000001e26cd22986c890887a6931a36883bb34b236832640005cbc00085b16a60000000000000000023c600000005618ce600015489008000000000003480001440000000000000000000000000000000000000000002190832800041d80006881b70000006a00000006b59b062a916b88630000000000000020002eee32e017819e00006a2000000000000000000000000000023e1fde00003d002b9f4690da5ff000000000000000000000089c8829500cf24caa178000000000000008608000000003600000000000eda000000094c8000000000000000006a1800000000000000000000000086c000000000000000000000000000000000000000000101e00002d600000000001be20000000000000000000009f0000000000000869a1300005ea7b580000000000000000006d40000ee40000000000984800000000000001efe0000a10000000046320280000442000017700000002d49e8a8de800010d00000001e3a4408000000000000000000001edc0000000603000000000000001204000000000000007890000
  | 40 => 0x21a152a00010a2322000000000000000000988885a0000000000000000000000000000000000000000000db80000000000000000000006a42ea800000000000e38468000000051300000000000000252e000080806321a622497fc000000000000000001f5d00000000001433000000000000000000000000000000000002120d3a000000046f80004f9800000017182e2a31062b8000000000000000003ae00000000994000000054ddee482e00f80000000754c0002dd68b00000000000136000003a400006e8000000099c000000000005e980002ff800037d21e300012d200017d20000000000000000000000002450000000000000001a10c23000000051e0000942197625de08e7a300fe88adda01cc000065900000000000572800000000000000bf000005020000000000000000000006c0222e67e00000001f9000027fc000002700000000001d4e0000bd000000000000000000209853c000000000000000ee65171304396a0a8563209a077026a0fd16b08300d60000208027b8000343800031c18d40001d5c426c00000000000000ee98ea00000000000000218e2a400000002427000000000014380d3087876a80000001af68d980003c300000000000688c0005eb800000000000000e6200000005fe1ac00000b9181116fc0000000000224e000000000027929b30000000000000005c00001b156d50000000000000022f85c8800000000000000000241c0008150b5030d0fbf0000000116000000018040001ed875c00000000000000000000000000001a7190bc000000000000000004438500000000045b1f140000000000000000023860000fc299d000000965fb9c70b8001b47ea0a11d1a1a70000000000000021c6000000000016a2000000000022196319db83ec105e0000000000000000000006f19bc200000001b80000000000000001c61bc1d6c000000000012e29b88000168000000000000000000000193c0001c220a8000000005a60000000000000000000000000000000000082b0000000000000000000000000000000000009990000000000000000000000000000000000065c80000000acc00000000e945fa564265e00022f400000000000000000000000000003e88dc800000000880000571000000000001e880000000000260865a00000000002433000196631ac0000000338000190c000000000000002418000000069100000000000000761000000014003c6c00000026e8534800000014be00000000000000000000000014cf000000000000000000000000187c0000000000240c00000000288000a26800000000008559f6648e00001a011e209e230077400003b09ab420f03718d180002238000000000000011c8000000000024980001d5e0000000000205e0000000000174c0000000000
  | 41 => 0x61d36000063f00000000ae03070001f74349098e000000000000006a3800000005fc435400000000000000000000000000004b00000000a2a000000000006ac0000000000000000005a812147590ace0000c9e1b2085e0001c3e4ab8000275247e0000ba86bb987600000007770b36000000049e0000a3a1d2a4030db1000000000000000000000000000078c029c0000000000000000000007e08000000000000000000000000000000000000000000000274000067ae03022500000000000372c000000000000000b00000000337000000009050000c3c08a00007cb036000000000000000000000000000000001fe600004d400000006008000000000029806867ef80000000000000000000000000001a16673400000003f893d0000000000085c000000002700000e0c00000001a2400000000000000000000000000000009bb0728317132c71610f000000004b1071a3af800000000005e25b160000000000139c000000000000005a78d2200000000000000623077d6af000019f800000000000000000000000035e00009d780000000000000000000000009e4094c000000012b000000000000738a4c0000b2700000000001d8870b00400001afa00013540001bcc46a400000000002a4800000000000001ae02fd070c000072e3df000000007a69248e100000000000000036900000000000000000002fa7cc6198000000000073f8000a1f07f000015e68600000000006f6fa1fd622a1bac03680000002576000000000000008790000000000000014320000000032c00000000000000f18000000095799b40002842000000000000003648000000000027300007a480007268d3400018860000000385000000000000000000189000000008762814000000000000019e1000000000000000001ea40000a9e6ca00000000000000000080995bc0001e5a00000000000000630800000000000001b2c7caa7ea00000005df20fa168a72c000000043f000000000000000000000000600023ee13f80009c9800000000000000d400000dd23f605a5509a0620000a5c0000000000002600000006aa800000000000000000000000039a0000000000071d0000000000000000000000000000000000000000001022541c00000000000001fa61668000753117c40602fe00000004fe800048a89be5860dd800012b00000000000000000000003bb00004a60000000146600000000d50000000000000000000000000000000016d096c0000000000000062d2590837400001193750001caa00000000001940882000000000000001bd05260000000000000000000000000000000000000000000000000031e8050000099d0cc000000006982be9f1a0e200000000000000000000000000000001fd881d840624b0000000000000000000000000000000
  | 42 => 0xec000000000021403fa260575b80000000000000000000001c88fc13267588000000212200000000000054549400020680003f021e6000000000001b000000000000000773205a2704000000201a00019cc000000000003c0000000000000000001ece4f28000000000094a8fb8000000031897be0000afe8138ad424c19c021f15680ec000000005b685d8000000050a1fc977400006400000000000000009ac0000000000000000046c800000000004ca017d0000000000000000013fe098209292881040fd800000000000000a1e0000000000267a000000000025f22cc800000000005150000000000000000000000fbe000000000000000001c0e0000000000174a8ab000043b000078d274800014680c29f7874a110b0000698542885c4268f5e0000000000181900000000000000000164840b972e0000000000278e0000000381400000024767148000000000000001de0001f38000107a52c80ad00000000000e82a2880009d1800000000000000000000000000000002f4a07000004cc4a7800000000000000000000259c000000000000003a88000000000000000000001ca269ce11529b80007618542a0f0000000000005240005990000000000000000004868000000000000012b400002047ac80000000efc0000000000000000028c40001e0400000000000000000024c3cf00000000000000000000000002029535123405a0000000000000000000008e2838600013a44a8a61c00013f02dd0000265800089080000000c7a6e680000000000000000000000004698c4a1dec00000011243fb800055d800085700000000000000141a43465a5000000002a84d1000000066a80000000e723d0822649716e800000006c090500000000000000000000000000bb0000000000019c8013032c00000000000000000000000000000000000000000000000000000e66000146d00000006f991d300000003d8000060880008ce000036d80006478480000163e0b900005d08389000000000000000000000000064100000000000000946800000015d6949a6fe000000000000000000000000000000001b724604bc000000071b80000000000000000000000003eb9fa8880c0000f8225073d800000000000000000000000099e0000000000000000006e300000001e883b108ec000283e00000005b780000fe8000000000055f8000000000000000000000000801127600000009700e9828900007248000000136400006e4000000000000000000000270935a48889d80000000984137a7360000000000065c194c00000005738000000000000000005c780000001f1c0000000179000000000005708000000000000004d6000000083180000000000000245a0000000000012900015b076d1e1100000000000000000000000000000001f9568
  | 43 => 0x567800000000000000bdc186d2bc166c3300000c0600000008df8000000000000000000000e04184e8b4000213000000001ff052c2b921f831bc5663028000000000000000000000000a0400006289c4242d6362000000000000000001142000036c85a0000000241e984cf7e5b280005958f8e000000000000007a000000002660a000ade204890025a04ec0001a7600000005ab8000751c4ca1c448fc000003c8f7248a24040000001ad20001ee200000000000dde37765c6000000000000001b98f40a0a00000002169000000000000008030c9c56583e44cc80007a5800000000000000000000000000000003600000000060035b800026740002355a2200013300000ed6a32a8aa6ca84d800000000e400000a38000000253800008be030400000003c488f80000000000a278d8c64c80000000000000000005a000071c20d956d800000000005238000842c00000000004d58000000000000026800000c021c38000000026611b453400003fc975871c90000000000000000000000000000008a2000000008ac00005768000000000022d0b4e5e3c0000000000000000063e8000000000000000000000ca974805e0000191c000000000000004bd00009aa80000c0dd3c7228000000000060900ec0000f2f0001706000132f0001d120000000000000000000003fc8000000168636a173e4c500005030cbc408153261193907f199e200007ee0001a26000062200000000000000000000000013a6000000000000000000000000014637bdfea00000000001e840000000581000000000000000000000000050900009170d4e00000000001b4200000000000d9871860d53b803742ad800000000000000000000000000023ce00000000000000000225e000000000000000000aca00000006b2800061e23a60002146374000000009bd0d380000000fce000017305bc0001cc8f7a1b5000000002c81badcc400000006ba8000000270e0000000000259a2660000000000000000000000000705953800000000000000000000000024c423b86d22dba654000263a00000000001d60000000000010700000000082000000015de00000000000fdc7d7000000025e8000000081400000000000000046b000000072780008948e1b00000000001fec4c4000016400000000000000000000008c60000e190000000000000060780000001280000156a00017400000000000000000000002148d1300000003a292f87c0d1a5000269e0000000000000001ea5160000a2e00027ee00000000000f1a00000000488c140000000282000000003ee0000000000000000000005ac800024490fe00000006e080000001281476c000000091482c9c5d6ab800097f09132ed1ef40000000279800000000009e980007178000576c0009cc00009549e560000c
  | 44 => 0x15ee0000c86000000019f00005430000000288e00000001070d5665f00005ed8000000000000000000de9c2a2dc000073e0000000000000000000001072835c0a5000000000014bc0001f3600011ce0000c5a000000000000000000000475c7a0000065574780000000000000053c7701cda000000000000000000000000000000019e8388895c4e50000567544a73e8fd4371c00097d00000000000000166c2f19572980064500000000000e8100000000000000000000000000006a70ff108b00006d1800000000001be1e220001e17000000000000000000000409c8269c6a50051f8000996a6080000000352000000000003f8a4640878000000000036cc0000000bc80000000000000009b00006ac95ae9020000000000013a8000000000000000003e780001c49e94000132e00000000000000000000000026be000000000019d6000000000025a00000000732800000000001f700000001bed075819c28d006e000000092d1adc000210c0000000902dc3831120c820400007fa0000682042029100000001140092800012303489b508d6510000012a40009c6000000000000000000000261600013cc6f2000000010488d900000000000000000000005230000000000000016600000000000000000032e8000000254e0000000000277400000002184f5600000008af8000017000000008e08c9800000000000000000000000066092284a6827e00012605ec1d0200017fa91e18dc00018cc497a8720000571000000033f8b48000000014c9b185b080000000000182800000024d08f61fbc43b970d000000019fc0001b58000000000000000007e880000001518000281c6de0dbe78300008ff800000000001ddc000000000000000000001c1a0001640000000000000002e50000000000000000002214000000000000000000000000000000000013aa7b8000000000000000b9a00000000000000a2f007800000000000000000000013815f26df80000b08000000136a00003da000000000012a6000016000027700000000000000000011fe8dc80009c2800000000000000000000000064e16d0948877f698020a5e365375bfc3e600000004160000699908400000000000000151025e000000089b8b6499a800043d40006fd820d000000000000000030000000000000000000000000000000000000000001a80000000000013de363836852884ee5b5036239d0145000153a1c4d8824a18f5818a8000000000096f0000080800000000008ab80000000e560001d047d200004018000252958800018f614f99586c3400000000000000000000229a000000029d1654000172c6a30804000000002d000001c000000000000000000000000000000000000a1600010de39a800000000001b117103f4dad0038800000000000
  | 45 => 0xa6800000000ac9fca5fb282e248030e000000066c000000000000000e380000000000000069b00000000000000000048780003a50b1040f80000001266000000004a0000000000089d80000000000000000000011dc337800000000000000000448000000000d06bd00000000000000000048f00002d1a1440000000000000019d28180000000000002a83a80000000000000000000003f016c00009f680002e2039200018c3795d8e0000183423a11ba8299d3845985a364194cc1810eb2000000000000008148000000000000000009fc800000000000000000000214500018e40000b200000000325400062a0b0846f00000001a456ed046c1274000195800000000001c80d7a0000000000000000000000000000a1600000000000000000000000000001bfa00003d46a145173e583e8878800000000000001b363160000000193a2b000000f3d23a00017b222724fc0001c190a0a79600023ae00026f819a000088a800000014560001fb60000000000000000000000000000000025400000000000bce725105c13e9c0a000000062921119e70000000211200001a4000000000006960000000a190000839c0000000000000000000000000000000000257a15212950000bea46e07d672b00000000000a1a000000000005ce8000000000065b800000002fa000000000000000000000000000000000005c5000074c00000000000000078e8650b260000000000000084240003980bc4047c28634d9a754729fe4000176800000000000cd626300001a9400022b00000000000000166a000000000000000000000000000034980002141c7f32293e20000000000000000003cd642800000024c88b10d2000001b30000000000000000000000000e0e00000000000000000000090d0000000224600000008de00009d621c400000003d71a927d5db869bc0df297540000000a800000000000046a000000000021a415c8404126e6b8000000072f8000000238226ca85e00024e6000000097b167e0000000000000000000009b411c4000103b16a40006cac000000000000000000000c1e93000006251e9000007b25a088180140000000000000000009ef800008e00000000000161000000000000000aa80000000000000000000005cc80003ab00000000000000000000026a2000000000000000000000000006000000000000000000000000020720000000000000000000008a016c000000000000dfd3584d880000483609800000003140000000000000000018383b300000001c3400000004180000000000000000000002880000000000000008e31e015f6000070f140e0ec8ac60000000000000083b9d2ea33800000000000000000000000000000008ea400000000000000290000000000000000000ffe170400084ea73a5be8
  | 46 => 0x7bc4000000267224d000075fa80a8da8000183e8783c91a52022111400000000000dc619b043c0000000000054019280000000000000000000000005b90c20000000000000000000000435c00059e876e000000000025d70000000352820300000000000000000031a0000000000000000000006c28000532973400025b8000000009002d2000000000000000001d0800024d70000000000000000000002c1420f5e3000021a80000000000000260c571a2e400000000000000000152c00008aa00000000000000000000000012ba0000000000000000000001a2c00000000000000000311c000000000000000000000faa000274c000000000000000000000000000050418680000b1e69bc0003401fa449f11920000000895910097092a45b691680eb01ea00004a86be00000000000000000000012726e40000000000043c9f8000000000000000000176455480005518000143c0009e0147600000000000000000000000018843568000000000053700000002284000169000000001d414ec00000000000cfa0000000000000067f800000000000000000000000000000003970000201800000000000000000000225a00000000a5800005700000000000000128e00000000000000000000086a0000049400000000000000000000000000000000000000162023055885360001f1240a96c6a2c9d5200000009a100000000f1f000193e00026ce0000000000194a80d000000000000000000000000000000000f8a50231a4000000096a919938c00000006cf8000540003a2f68000000000008e80007d780000000ada6f48b7e909000000004929c8800000000004ec40000000000000000000000008ed00007e5893810f5a6880480007c1800000000009868000000000015180004e5c0c60001f0200007a400000006faa42d1d183460000000735000000000000000000008000000000000000000000000000000005dc00000000000000000000000000000000000000085d000000009ae03791987fd000e000000000027d400000000001fb00000000000000000003ce1a1c000000000000000000000aa200025f609d8000000268a0dcc0005f50000000000030b000003c00000000000000000018ccb924e8d45b000000056e0000436935c0001cee73c000018c65803a24ec86aa00000000b280000000000239e0001262000219c00000000000000000000000000009c1800000000009a09816776060c000221000000000001d56000000000023e40000c5e10ec00000020dc0000000000000000000000000eea0000c490000ce4000000000000000000000000000000000001191828000000000015ac00000000000000000000000000000000000994000036b40004de13c81a3cdf00000000000000068f000000000000000000
  | 47 => 0x6141a0c0000000000000000089c8000000000000000000000902000000001398ce00009650001e823ad20d19e6a0d325c55820000903000000000000000000000000029a84a90420992662000099f00000000000f6a115800072b8afc32b02581d28ab2000000000002463ea00000000000000000000000000000000531463a403dae82c7e7ec698800000005d651789867f8a5de1b7849c5e600000000000000182c2a105a10000a4246b80000000e9a0001712000119e000000059f00000001a84000000000000000000a3c00016700001a820000000000285c00011fa000000077e00000000000874021c6a80000000000041a000093a86c200000000001b5e0000000000250504e9ea00001acf90c8000000000000006100e78cf000013c00000000000000000000000000000000000035a00008889a3e6eac25081b16b60000000000000022262007f313ee00009220000000864c000000000070481a80aa8e3a6740000000000000000002860000000000000000000001e0800008b66398000000134a442a23200000008db840800000000001182000000000014185208000000000077980001bb0000000000000002b4000000a43a80009cd000075626a48b3859f000181c0000f2600000000000000000153602e0000000000000011ea000000096c0000000000064b80001fb0000000276c000252816ac0000000000000000000000008cd000000016be4525d7c3201c6a00002008fda4b2000000000000000000000000000000000000000e800000000000000000023c80000000000000016b000000000005568000000035e545000000013d812680000001a5a000000000007dd45e8df66c900000000000000000007640000000000000010c00025e166980000fb000000000005d8248c62ea86222880003cac00000018a7044a7620000000a1b00000000000000000000000000000000000000017789e80000cee3ff1138000000097600000001fd46a900000500000000000000000000000000000000000025c9000145800000000000000000000035c179a9b60cda875a05c11811b78550000000000012dc0000000000000047200000002830000000000012380007ad800000000002d020f20f6000080a80000000000000000000000000002890000000000000000000000000000034b800040d80003a80de638b000035d89167504000606230e00000000001cd20000f542f580004274000000000000026c200000000000000000000000000000000000000000040a62e853f0000000000000000000000dc28a81d78857676a000000037b1e4000000000000ee825e91f40000000a3180001ff800000000000000000000000000020bc00000000000000449800091180000000000709000000024fe5c1000000000000000617000
  | 48 => 0x2628bc2160000000000017200000000a058000390000000026e4000000000000002b49afe000000000000000000000000000000000000af00008be800072040008fe800043bc000000000045a8fb6000206e000000000000002728000000000000000000000e120001d9e0000000122934432080004e19d2490a8000000000000023be00000000000000000000000000000000000000219600000007879738000000013898f806491b91d38cb6000000000000000001d6828a991a0000000669000000000000000000149241c0000000544000000000000001f5400000000002598000000000000004ac800034f8deb8060f920000000000275247da8e462618fc4c5a2ba73718a09d70000082ced402d80000000000319000000000000000ae200000000000000000000000010cf00000008b6000000000005e900000001c648a7800000000000000f1487ac62600014a84a100007b680009e2126e59c66ca8b291086d8800000000004358000000242e000000070d800000000c04e0a0746d609621131a06580000000000004fc8000000000000021aa40fc0140001874000104a11f8000559000053e0000000021200000003790000000000000000000a480001b003161d100002ec80000000000000000000028b629f80000000ce20000000000000039f24bc00021040000000000189000004aa00000000000c760000000000094891f07c20001a0e2051f880001a44000172a000011b00026a800017b800025c800000002538000000000000012e6000000090a00009c00000000000000016e674580000001b0e0000000000274a000000000007a80001cb424b8db833000002a7104c000244e00000005c3800000000000000000650c000000166b5731dde000000037b800000000000000000000000000000000000000157800098d8000000000000026c0a0b000000000000000000512000000016839c58d6a2c386e700024941fe000000000001ae8000345000000000000001502275800001d80000000ce51a140000000000000000032e0000056c5aa508800000006cc3ae800000000000001bfc00022066670000000204c0769331023d9740000000000000000021a000000005b7000049a000000000000000000000000000000000000508000000000000009b80000000000000022a600716943f800003941c1c574c000152800047413460000000000000000000001878000000000007b043000000005700ba217700000000000000000000012c83e9a3a2000000000000000000b182a8000088718880000000000000009e4000000000059b9090000000000000000001ae44aa80000000bf800012da49452c2344987232400000002468000097800000000b117000001cd00000000000039499980009b100003ac19ef0002566000000
  | 49 => 0xa80001ce400000007898000000000000020be000000060b80000000cfc0000000000000000020ef79800000000000000000000000000000000000000000023e000005c427f800000000000000000000000000000000000000000000000000000000000792000011899e400000000001d500000000000000050211538a72282507815200015ba42f00000001a4171b12de99f801e0001fb24e102d052c26f2057608658a09b0000000077a000011d0592466a53400000000000000000151a000137e8cb00000000000000285000019fd000000036d00a8000242b000000000000000000000089072a1e10000000000019100000000000996000000000007e81cf4000000045c8000000000000021c20000000000000000000000000d0258e00003e6c00081f00000000000000209e000000000002ba097203c000000000016b400000000000000000151600018ac0000000000000000000001f50f2e2e7800000014d8654de6a00012b500000009ad00001d30000000000026eda0a00008810000c409f200009e803dc6080000000000092200000000000000241200000005399bee9128000178800068c4c5030940002e821070000000000000000000f1000000000000000484000000000000026ae0000000000000000004c000018fe0001c8e00011de61a80000001978000000023f80000000138000227a0001d63000000000000000000000000000000000000000000000000024c80000001d4000026f4000000000000008aa80009a40b71510a4ae7cc0d0a64a9bce8471dbe5a581f0044164c41ce4226cf0000597a10600020e10e800008c1228c27e8000a03873a43183567b2800000000004ee116e52012183771cde11f07d200000000001b5a426000065b1f20400000067c0000809128a9ce0ac21d0800090a40000000000000030000000009541c5b6558000000000002c86c6127902461590547bc268c823251008a960a000000033300000000000000000000012580650000470c000000000000027d000000000000000272030f90105380000000000000000000001e6000000018d2000000000011566b1109c64587be7ae478c9a18000772970a757400000019a20000000000000000000000000000000000041de732468dc72000111b00000000000000000000000000006bc9206613800005a800093e400055f00002f00000000000000009a1000000000012b77e525a2207174800016020bf00001a4000000000002c2400097e1a7a000000000000000000000000000000000000000000000000000017160000f2c0001c2600013d2000000063a00000001a0411395a400021b4000000000000000002322000000000016625d88000000000000024420499c084eb12fa7ff98c842c42a6000177e000000000018aa2f800002d1000000
  | 50 => 0x129910686f00000000b7a00016c8000264600018644329d8200000000002503000000000000009a58000211000000000000000000000000000004f400017550000000000097400000000000000000219a0000000000089e137d00b99b000000000003f5542e000000047683de155da9a000000000016080000b3e000000040b000000000000000618000046667c80000000000000000000000000000000845a6d606400000001a3868a0000000000000014ce00008807bf000079b891e0000000000000000000000001e700000e36000000061000000000d5000000004a71cb24dae72a6201ac800000005ea00000824000000000000000005fc80009c9275600005c20c88000000000000012c60000000000000000000000000ee22e4c00000000000000000000000000000002cc000000000000001f920000e6e000000000000006ce9f64000000000015e8000112e6488ef000026fa658a23a498dee679400005720000235cba42f980001cd800044e8000000000018340001c1800000000000000fe6000000000020fc000068a00000007124000000136e000000000000000000000000000000000000000000378800000000000dc25720001c9c0000000000000000000000000f9c0000d0c00000009d81ef82af8450000000025d80000000000000254890c000000024b83eb180e6681ce28898000a3680000000824000000000000002d6040c57491127874207000000000000000000000000000000000004a20000626a1da000000004727f400000000000000000000000014a00000000000000000000000000000000000000000000001130000000000000000000000000000016b8000000000046895122598000000000000000001aa0000361800059100000002214000285252d1e20594978637b400000000000000000000008e1fe80000000000000000000000000000000904400094100006f0000000002ae3948aaa00001a10001b141f1000000000000000000000000056a00000000000000000000000009ab00001b6a4d238c0fbc04c1ef600006ce000000000019f6000000090b00000001cb3112800000000000000000707a71e000000081600001ce19ba0000000050c0002a2849400000000001bb2000000040957269fe800017e0000000000085d4000000000000000000000000000000000011e40000000000041e00000004ea2110000000000000006f600001a51d4d76f156e00000007b1800066125e64e800000001baa54a18a500000009258000000000008411446e980000000000169c00000028f00000e0800000000000000000000000000001e500004eca77a0a000002ab0000000000003e8000000000000022341e2800000000000908000000000000016a483e4ea600017f40000000a0ca01600010
  | 51 => 0x87e0c1167200021e05f0800000000007e1000000000000000000071016253a9ea8000000000020ba0860000663400000024d4000000000000002888000000000084524a8644a88c4bb09da000000000000006da041a00014da00000000000000228168a26d22640000000000000000000005f0c000480137600000000000000a3019a8000000000020ce00000000000dfa000083800007b40000f810000000887800000000000000000981800042f8000243800000000000000000000000000000000000000000168e0000000000000000005070000657911000000020df2268fd2000161000018320000000a1980000000000000274200000006ef80006fec000000000010080001a8e6dc81e000061325ae000000097f800000000000000000000000000000000000000404400000000007cf8000040915e0000000000000000000004528000000000063b00001cf800000000000000b9c00000000dc82c0000100700000000000000000000085c8000000185200009364bc1c84000000000000000000000000000012e6804000228e0001c5670c45d456880000000000000000000000000000000000000000000000001ba200027fe00000720000000000092a00000005104000000000050091ec8ee007e000000000013187a3a75a000000000008d400000000000000000000000000000000000000163099a000000000000000000770a6249e61ba4485a7b07e18e9c22100002500000000000000000000d484000001b0c00017e20000000000084c1554aff7d9e6d2000000000000944754c2172c25ee000144e9df000061680007550d5f59b400057d00000000aa54928b6800008fd05080000000000000000000016d80000000000173600000000001b3237800000000000000000000000000000f227acc573000178000000000000000858a7667db0d1017a1ab6670d49276280000a5000000017e66b1d30600000000000000000000095b800000005bf053970c00000000001016589800000019ff96380000000000000000093e0000000000000000006e580fc000000000012a00000000000141600000000000000427800000002d890944c29ea988a00017670590000000260700000000000d2aa04800000020e800000006e28000a2e13527472060000000000006a62ee000000000005ba9e66152c0000001392000271400000004af800000000000001235000184400000000000000000000000010fa0000000000133844ca88400000000000000000000000000000000000000000022f00003a200005dc8b769f4a216000000000000006378000000000000000007c8800054b8000a11000000010b42ae8000000000000000006d48000000111c96100000000000000000000000000001c20000000000024a0000000064c16e254800000
  | 52 => 0x4a76e2998f700d6800024e9e1a4c480996d85e7c7438000a1186aa000210100021a20001d8c00004f99bd97c800000002c4a3f85831a2c4d880eb29893c418d800000000000000000654000000000000c6000094b03f93c1066600000000000000000000000000000001af100000000d900000000000000000000009640001a5e000000006080000000000000000058900000001082697278200006b60001574475800000000009cba0d40000034000000000000008a28000000000000000009ca000000005f200000000000000000264000028540001f0c00000000001df633380000001b4e65f8000000000000000004dc00a07a70000190c11929501e4000000000000000000000000158000000000000120000000000019ae042054f00021f40000ad8a2200000000000612149458d820e0000000000000034c8000000150900000000000f320000654428000012f8cbe617992c00000000000000000000057a800062700816b3800000000000000000000159c5918000000000072e1b5610400000000000566800082ba4704951a9686780000000000000000000000009151b30000028c820919c0000000000000000018b20000000692800000003989d3a4be1a0467d8528384062936c5ab0000000000000000000000000171800081f800000000004760000025800004600008fd000070ac7e000014f67c7800091780000001f3200000004008000000000000000000001ce871a1dba9b19bb000013803b180000000d4100000006580f308480000000214b0000000000000000000000001f70000000000003289da1db00000000000000000000000000000174800000000006bf000000000000000000937000061080000000924000000000000004b700000000000000000000000000001e72000154a0000000000000067a8000000000000000000000724000000000000000ff800000000000000ae80000000000000000000000000000000000000000000000000000000006e80000000000000079200000008380000000000000021e70000000000000000000006a2000000000000001d5f0000000000000015c23f20000000000127a000038000000008f5000000000000000407380e1926c3e4e2793c454000254a7be86f268fc00000000007f480005d725ea0000e3ea159248248c0000000fde000000038ec00000000001cd000027f0000389928c00003594bb89880000000629800068901ae0aa1dfa630400096a40001675eea0e3400068785990000000000000000000000000ce000000000000000000000000000004d2097e446a5ac0000f08749800093d80a4000000062c000098b800012ec16c82200003aae3bc1ae00bc0000000000006c0001434000000031f00004e200000000e2a0000000000269a1cf00000000000102a
  | 53 => 0x615000000000018960001508358ce480000000000000000000000001e3800000000001632000000000000000000000000146c7aa800000000001ba8ec087ed5936f6800089a8000000000052280000000000000000000003a1000000000025b631180f400000002f9000000015dc0001ed2000000000000000000000604000090c677655ec000000000000017a000000000000b3a00000004659474000000000007b000000000000000000000029580002cfc000488c9c400003786b184850000c60434800000020a00fade7e00000000000000a0e800080e157843e22207adc0007749948000000000017dc000000045923b098980000000000380800093b984a3ec80007fda6a64bf967300000000000f84020c00000000001b413b60000000139490800000000002720000000070ccb5c000000000008a435f800000013e000000005c926ba0000000524000000000001c6000000000007db855300000007eb80000000000000000017b80004c00000000000000000005784f34000000084600006d2992600000000000000000000071f00000000000000000005501c04781282797800062ac000268800000000000001324000000000005ec000214900024f024a0000361000097950e60001763000000000022409d52152000000000003e9000000013542e688380001e08a964a40000093800000000000000bae66b00000000000000000000000000000000a33066e0001f97222963a690a2d00000f2a00000000001c1014325868c91d100001bba7af80000001c633758038000000067ba824000130a88280007750bb7000138e4550000000000000000009b9800000007e800028860000b820001cba000104e0000f1046c0000722054900002a20002486000042e000000000023e602283fb00000003595bb6000160e02e8000000000079e80000000a140000000000097c000000000000008f58e1600025444d947c0000212c000000010b0f0a000000000000000001092405000000000000000000000145200000000002008000216e4620ddb00000009628bde00011f7672800083fc00030f80001c000003518000719800000000000000c380000745000000000000000000c480000bba85f000000000000000000000000044d0d583879d4468a80000001746000000000000006c20000a0304da9f1260200000000000000000000000012200000000000104600012307d28000000000000000000000000000068d3318c8c000000008517ea5788000000000000025c400017924e280000000000000000000000000001f0a26b000000000000000000000000000026042e984129fe000000000002680c720000000000171a1628000000000000000000a200008b71bae79880000001c04000000087b819605d000013ccc4f00000000000000
  | 54 => 0x60000000000000000000008d600000000ac40000000000000000000003e08000000000000000000000000000000000010380000000000000000023ca00000000000000000000000020f10000f6e0000000000000000000000000704000000000010d378dc0000000000a2f851233a00000000fe400020cc000000000000000000000000000000022151a78000000013e3c58c2a00000000001c4e0000e4a0001190000090f0000000000000000012320be28a600000003641bc41b61e1539ea74000000000000000000000000000002b580000000556811800000000000e2c0000001d4830c99ce9a49f7247c800063c4000000000000000000000000000000000017bc000000000000007a99dea0000000000000067b40000000e4e00000000000000000127e0000000000000021c8000000017a5b81e32000000000018c500000007d40000315130e30ea482a0d99de65680000000000000000000000000000000000000000000007b308e272000008229d7277c00000000000000000000000000000000000113600006e500017fb0000ff08c70000000000014e80004cf00000000000000000000000000000000a3b1d420000830000198c5da488c00024de57c000033e0000000000000000006db000000000000000000000141c105000000000000000124000000045300000001e100000000121800079a0000000000000000000000e6c000000000023b600000000000000a32000000005f6000000015440000000000000000085980001090dc42fd80001c7903000026b600000000000000000023e000223816ea4520002562000000000018e20002530000111800000006652596554015000018da52b21f244b17d96e7000000000000fa800000000009390000000000012da2fc3c38000007c0001488000000000000000000001f34000000069200007f71d7a00000000a2800000000001e022e600000001d200000000000000253601a0000000000082c1d00000175000000009ec80002bb0ce98d0906c37a0000076e6fc99f16340002524000000088a000000000000000d060000000000226c0000000000055267500003d9899c53b800000000000001bde0e30b0a000000000002c61f40d4400000000001ee800028020000000000000084d85470001a148520186000215e000000000000000000870000000000004e700000005999e9e8c5800033480000001a340000d9e731a1c096f800000000000001a11666800000000000000000a079a950df0000000000000000000000000354800000000000001a6a73f060800000000000af30000000000000000000000000000631d1c00e20ae0000000000000000000000a27151e000000000014d0000224b61b9542484543e8ac8000000000056a800010899fa0001b501bf80000000000000
  | 55 => 0x249c000084a000000000006ab000000067983246808e7653d0000000000077101f28d10b2c0000a529b20b660000000000000000000000000000a3ba202000000000027b8000000076980000000426000000000000009ee800000000000000478345c00021e978800004a50dd8000000000000000000000f00000000000022c6457000000000000000000000051f00000000000edc7fb8000000206400000000000bbc41581d70001b6e7ca0000174400000016f67f6800000000000e1c0002320000205a7a200021425a3213c0000e42000000000000005a00000000066a51c800000000000000000000000000000000000000000000000000000000000290286e9740b6f62f9c0c31f8e929c30000817400000004d241c40000000000000000057d80004750000000000000000000000bcc00000000000092458000000000000001caf000000000000000000000000158a000000006ec0000000000000000000000000000662052800000000000000000000000000000005ff8000000000000027a8000000029200000000000000000069424aa000000000008568b017b429c800069389f846500000000000000000000000004fe000000002ce7241b5c7c98000000062c89f8000000003e41005c700000002cf17e842ccb4111e8000000000000000000001ac20000000000000053080007b515042109e0a145a78c72300005d6000000015e400000000000000000076c00000004bca03a00011c75550b16000054e000000070600000000000000000000000000000000000000099d800000000005048000000000000000000001fa77d580000000000255161200016140a9000025100000000000000000000000000002648000192886e9bf0306120200000004f4000000003be00016880000000000000000000002bb80000000000161800000024140000000000000012100000000000000000000000000000000000124000000000000f8c000000010380000000000000025297480000000000000210a493c0000000000891100d93080007960000000250a00000000001b842218000000000000000000000000000000000010ed7d64000000000000000000000000000000008c920a000000032a08742a6000000000000000fba5db0bfc000000000000000000d660000000000000031b000082120e3000049007600000000000000000065e800000000000000000000089677b800043d00004e68000000000000008c39649d9800000000000000000289400000000000000000000000000001be8000026240e000000000009aa4fa0000000000000005269c4051484380000000a888538000120800000007f415400000000000000000049a40000000dcc080507e000020500006ee000000000000000000000000000000000000000b9840710f
  | 56 => 0x5500000000000000000251c00000001530000000099e28c25120c9851876d9f6200027848f019bc1938eaa0000ca430696f8605126100020f69a61fce000000001482e2437039a80da46e4f3860b000007451690c26e380008d799fc23400663b1c0820000000000000000000000ba0000000191900000000000000000000063c06dc388000000000000000000a09912a945032011793d600000000000000733000025c800087a055400011cc00000000ea800006022880001a2f4ef000000000000000000000289665797d64ba09f247c000000000008fb000000020a4927a3ac000000098f8000931c0006748c74000133e78140000000000000000061c0000000255a929800000000000000000000000054180000000000000000084d000098640005960000000000031480007dd8506952c0000002100000180a25f657c09cdabe7b020cfa101f6a000000000021b200ba0de24111ac0000000000000000014ba00000414a580002fea5a40660b045f7d5b232600a70000000000000049c0000000178e000000075280005381212332800007e800004f00000000d62000105a6d10fe3000000000000002dc80009e1800000000000000000978c00015f9b1e00000003a91e2e6dbc0000000000000000000000000001934000000025c000059d000000000008d80568000000000018d80ed80000000000085958e4638c4e068c0008bb9aec000000098a0cf488480009cf000000000002a08eca00013fc7638000000000000000008478e1829f24d5036400087f1ada000228600011fc00022784d40000000000000000000001ed00001a7e32820fd0000000000000041d1ec220d800024458a34c88000886800000000008ca800067180008ca0000000000000009b600000000001f44000000000000000000b73000000000000000000000000000000012f61d9000023840008bd8afa514207a7df8000000000000022bc000000000000000000000021187a00000000000e700000000000027400027c2000000000023c4000000000000001ad544600000000000000000000000000000000183000000006e000000000002a540000000ed2000000000000000ea000000000000000000000000000000000000000106000000024ac0000000000283495e000000000000000000000000049189ea34680003d380000000c103d9252000000005a610b00001d947e7000055600000002320000000018800000001b9e00000000000000280000000000000000e3f00000000000000000000000000000000000000000000000000000000000000000003b40000000000000000000003f10000000126a00000003d3168400000009d400000001a5800000004c7000000023e200000008931a560000000a0a83ae0000000000000032100002c8c00000009e400
  | 57 => 0x4238000977000000003b800000e0000000000000000000000000000048b000000000000000000000000071285940001cce98c000000000003b2c00000000000000000000000000000000000000000000000008e37b0c86e00000000000000000000025680000000000000000097800000000000000000000000000001c5400000000000000000000095b14601d0078b0000000000000013e0000000125000001ac0000000000000000010100001faa00000000069fad5499af079e277245480000000000590a84e000000000000000001ae632748b8000000000000005a68000000000000000000000000000000000022ea1714000275c000000000000000001df80000000000010c00049900000000000307c000000000000008b266f800042f4000a2e80000000000000000000000007b14000000000000000001da800000000009eb2874053234e00017020000000000000000000000000000000000000000000000000000000000000004ef8000000000000009c00000000000058041a882a0279d806c2556679280005bd17f60000d7200000000000000000042a00000000000000000178a000000000013a200000000001ffb000000000006bc0000172000000028e1f58000147a4b61c8650506af0000f6c00000007c100000001e3c000000000000003890000000000000000000000f4a0b500008ec97c60000000000000040110e80000000000000000000000000669000000000000000000000000000000007740001dae00000000000000000000000000000000dba82a9c0b000000012900000000c4300000000000000597167600000002a304f6000000035d000094f800000011e80ab0c78313068e0000000000114e77920d200600000000000000039c80b9496509c00000027780001c45000000000000009f61e2a00000000000000000000021bc58200000000000ac9000000053780007a600002ac26de3c086fc000000000018c400000008d2800022c000000000000000000000000028a00008f6800000000000000000000000000013580002501000204a00000000000000000000023e800000015ef7d300000000634055921c3ed1fd091c800054c26140000000000000000000004ad800000000000000c228ad0000000000000025e200000000000000a2900007eb00000001e442b9853025b80003f30000000125227b04a2111159800000000000000000000011d90d40000000732287000000001760000655142d0f0880c09f1ff0172c5a860f89d200000000001616453400000000000000e9e000025600000004e580000001234000000000000000000000a370511000078d0000000000000000000000001f2e161417f00000006e200000000000000000032c19200001012000000000000000001e360000b8c0001d
  | 58 => 0xab864501d29a700000000af215bc00000005f09792314000000000000000002518000000042b68ea00000000001eac000000000010c000000006da80000000000000000026fc000000000093826562d28000000000070d504472d80002338000000000047b80000000000000000092380001c9800004a9de2000000000000000000000000000055c000000000000000000000000000008020000000a2b05cd0e887220000000000070a0000000000000082d8e7e52300009d90000000000000000008890ff80001470000268e000000000012b88490000000280800000000ca80000000f6200000000001c9851900000000000000000000000000002882000235c12e0000000000000026da83b0000000000000024ce00010ba06100000000a26000000021b0aae00006022ed9c400000000000000058b80000001a3200000002c500002f8800000000000000000000255c12c80006278000000000000017dd00000004690000000000034e0453148155c4600000000000000000003fbc00077d058700000001739c76000000080c800000000006b8800000000000000000000000053100000000e8600003320000000000000000000000000000170e3c100000000c40000000000000016200000000000241709c800000000000000b2ea050fd1000000000015840000000000256000021be0001c500000000000000000000000000000000000000015390001bd62781a3d1ace73e5b30000000225c7e7800046a89217a180000000000219a5b238e4db278a00000000f1e000000000000000000000000000020d0000149c000000000000000001eb00000000000000000000000000000000000000042290786dd289843cc00019e00000000000000000023b400000000001d7800011453403bd800000000000001c2800010e01ed80002a5000000021de2c90000000000000018b896980008720f98000000000025cc634000000018410001a4600000000000000000217a0000000000000000008d3000000000014d677380001920000000000007b80000000000711e69400001765c44ef40000c300000f720000000000000076913dc6fb17ac000000000008ba00000000001be40000000644254d00008a600006a9000220400017cc000198000000000000000000000000000003f94000000000000017530002574651c0007af40000001d1437008320001a7c48dc1bc000000021b40000001462000000084a0000000000096d0000000000000015b4000000000000000000000000000000000009e514df000000000019dc53200000000000000000000000008360000a0180000000000000066000000001ee920e60180552960b252da85cf4f904de79900008561d5a57608286f80000425a4d870b602038f1b48128250600022f20000822000101a0
  | 59 => 0x5878b1a0000dd400023884430000000000092d80004f5204000000000000000853261507b400000000008ff00001df17762498000000287a000172800000007ae000000000006a400000000000000012c0002448000035800000004c80d040000000000000000000000000000000000000000000000000000000018e00003288000000000004c86b00000000000000050a5f981ef05ca00000000000a86000000000000005d84f4600000000000000000000000000000000ad9000198a0001ce6470800000014060001486000000084215d400001660e059248590000000254205f80000001f8c8e80000683da1a000000000000000000ed000000000001ef200000000000000000052e0000000000000060e80003f400000000000511000000000000000b2a00000000000aa600000000000000000174e8e50c00866000000000006dd8000000000000000001dc9e0005100000000000000000000000000001b6b00003bc0001d9c0b68ac800006f60c4800000028f235315940000000293800006c97e03f5857c000000012201366660000000000000005fe092000056f80000000e1a0000000000000000000008dd0000000213800000000001812690d6ee0001a0c000000000025fa8a48000000000047d4000000000000000000000000000022e00024fa00000001b5554c000000038a0000000000000000000000ab440e800000000000000000000000000000000000000705c0006fca4b023496fd0000d8a000000000016f20000630000029816c9cea000000000001cc53020f86b2400000015fa3ce000018f134c194db80173055c4df00000000000000180000000000000000000000000000000000000000000044f9bf933a9e5c6519a3000000007938abc3c180002360000000000037f00008e4935e78b0000000000041b800000000006ea1ec831b92333b60000000000059284fc42e1f7b0e08000000000024300000000000000000000015f800017ca7a89ed78f3002467d00001ac400020ba6420000000000000000000006cb40004a6c1008a9226800000000000000000017800000000001f4e0001f600000c710000000000000000000003508000a36000049584528cf817b00000d801295fc60a800000000000000b600000f44181800012e80000000000000013400000009f5a0d697c0efe00024163f209600001a7400000008c6054d00000009211a9e000091000000000000000000017000000000000a3a015c000000000093687ce0001dac000233a00000000000000000000000014fa5fc00e60c080002e58000000000000000000000000000000041d4d7c19ae30800006b242026010000000000000023fd15000002130d6e7e60000786000000000000006641c0d000212e000000091d0778000000000002ea1a9c0000000
  | 60 => 0x18f8000000258200000000000000680124c00000000c20000000000007f0ffa0000000000082ca0e000083680000000000489800013917d000000000000000000090a0000000165a84c00001a03da000062f0000673dfe081080001f2000000021f6840a6344e94000326c000000000006f8c9a00000008e58000000000076c800000000000000000287000080700001de80000001a361630000000000000015e00001fc07ed000024717543c4800011fe3aa0da97940350cd038d0000468243c2718000000000009a00000cd00005cc0c688e90000000061c3871430000249000000004840000000000000000004a662e27afc55a1319e161f9001d00000007110e009df8fea7c420f0000000027d05f3000000000000000001122000065200015560000000a248000000000000000000d5d63c90e261b4b340005aac00000000000000f500001bf800000000e14000000000000000000000000787000000000003d48000000000000020e510c82f00000000000000000019c400000000e3c00092e8000373a62a0e9865c2d88ee4230a1ac000240a00000007ec50624fb0000000000000014a4000000000000001dc000000027b400023486c48000a068000000000080280000000a700001bd40000000000102800001148e70672000199e000133668840004610820000099a00000005e7800000000000000bd8000241038c92449ed9c140000dda00000005de9ebc00000000001d663bb8aea00000000000000000000000004ae04b80000001e18000000000000007fe18500000000000000000000c28cd9708000155e60f400000025ca00000005ea9dff000000000000000110016001075690180000000000000000000006ae0000b862be28e226900005dba3a7159115a79d0dac1838000000000028101f83bae0fb7c000009c100003e68000000000000016060bd198800000000000558296a59b00025d40e7c31c00000004d99a1c2d58000000000049392d40000000000000000000cf000249a15b8000000000095c000003a000000010ac5b3800000000000001ca000000000000000000000000025a813c800000000009e280000a79660000071623d0000046800023a800000015a0357247a00000000000000000000000000008d517e4000000000000006d300000000000000057800000000000000000000000000000000664000000000000002cf48e45d59b1a000000053896d6000000000000000000000000000075140006509bf44d340000000c941639c000000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8ef8754562040011d90ea8ac40800ebaa00515881000574c00a2b1020008ee87cc562040011db0f98ac4080029ba17315881000536c2e62b102000aae84cc5620400155b0998ac4080029ba14315881000536c2862b102003aea800c562040015d30018ac4080021fe0d769481003c3f412ed290202fc6e825da52040638db04bb4a40801e1f20976948100043fc32e72902000c3e645ce52040558bcc6b9ca40801f1b98973948100043ec3ac72902000c5d7358e52040018bd0eb1ca4080031761d63948100062eba2c72902033c5e7258e5204001c9ce4b1ca4080c795c41639481018f2a882c7290202fa6f8758a52040678df0eb14a4080031b5cd62948100043fc2aed190200287c855da320400f0fd0eb2c640801e1f21d658c8100061fbaac91902000c3c7559232040071bf0eb1c640800317dd5638c8100062e3aac7190202fc6f7558a320405f8d8eab14640800a1f217764c81001c6e41eec990200087f855d932040050f90abb264080021f61b754c8100061f326ea990202ac5e63dd532041218dcc5baa64080021fa1d654c8100043e43aca9902000c3f755913204001878eab22640800e3721d634c8100062fbaac69902000c5c7558d320405f2b90ea9a640800297e19534c8100052ec32a69902000c5f7654d32040018baeca9a640823787991534c8100070eb22a69902035e4e6254d32040071d90eb1264080031bdd5624c810006363aac49902000e4d53589320400196ac9b8a64080033558f714c81000672b16e299020008f5861c5320400196ac838a64080033558c714c8100066cb1ae1188200287e85dda21040010fb0bbb442080cb1b14b76884100043fc32eb1082000c5e635d621040f98dcc4bac42082b21fe1d65884103e43ec3acb1082007a6c8259621040018bceab1c4208003175d5638841000726292c710820038ef8758a21040394d90ab1442080031b9d5628841000636baac51082000ce9625c22104001ad0a4b84420800a1f217764841001c76416ec908201e87d86dd521040018bcc7baa42081d31b98b75484100043f43aca908200587c8759521040018beeab1a4208003171d5634841000637baac49082000c6c7558921040071db04bb042080bf1b149760841003d36412ca1082003c7a705942104001c98a4b18420800f369c163084100dd3642ac41082000c79655c021040019b2c6b80420801f3a989700841017eb4292e01082000c7875dd910040018f70bbb220080031e21776440100066dc1eec8802000cd883dd910040018f6a7bb220080033ae0b764401000674416ec8802000c7852dd910040018f6edbaa200800336ddb73440100066dbb0e68802000c7b7654d10040019d6edb9220080033add872440100063dbb4a48802000b71858851004157ec0a510a2008002dce152144010
  | 1 => 0xd0eb1aa6080d31761d6354c100152e43ac6a982000c5f7458d53040014bf04b1aa608003171c96354c101a72b882c6a982034e551058d53040050fd0bbb286080021f6177650c100064e21eeca18200287e855d9430400193886bb286080021fe197550c1033e2f31aeaa18202f96c825d543040010ff0eb2a86080021f61d6550c100070e21acaa1820038dc8758d43040018bceab1a8608003175d56350c100bd4e422c6a182007a6e87d4e620400f4d90fa9cc4080029b61353988101a536c2ca73102000e4f5394e620400f4dd0ea9cc40801e9b21d539881000537c22a73102000e4f8354e620406bc9ce6a9cc4080d7935cd53988101b537428a73102000a6e8590e62040014db0b21cc4080029ba15439881000536c2a8731020078ee8710e62040011db0e21cc4080029ba14439881000536c28873102000e8d4310e62040011df0ea8cc40801e3b21d519881003c7743e6331020008ed87cc662040014dd0b98cc4080029b617319881000557426633102000aad84cc662040014dd0a18cc4080029b61431988100143f43eeab10200087d83dd5620400f0fd05baac4080c71b60b755881003c3e416eab10203187e871d562040014bb063aac4080021fa1f53588100143e43ea6b10202fa6e82d4d62040010fd0ea9ac4080021f21d535881000e2f39aa6b10202fa6c8254d62040071dd0fa92c4080ce9ba175258810016363aca4b1020038ec8754962040634df0aa92c4080031bdd4525881000567418a4b102000acd8314962040634dd0e292c4080bf1ba1c525881017f27418a4b102000a6d83149620405fc9b06292c4080029360c525881003e37b80a4b102007c6d7014962040071dd0f992c4080029ba17325881000536c2e64b102000e4d53cc962040014dd0a192c4080029b61432588100055742064b102000aad840c962040014db07baac4080ce9ba16755881000567418eab102000acd831d562040634dd0e3aac4080031ba1c755881000727418eab102000a6d831d56204001c9b063aac4080029360c755881019e37b80eab102033c6d701d562040014dd0b39ac4080029b616735881000537c2ae6b102000a6c855cd62040015c902b9ac4080029ba14735881000536c28e6b102000aae841cd620400155b0839ac4080029ba1f53588100053643ea6b102000a6d84d4d62040694db0b29ac40800393d4e53588100053743aa6b102000a6c8754d62040014df08a9ac40800393e0d53588100072739aa6b102000e4d7354d620406d4dd0a29ac4080029ba16435881000536c2c86b102000a6e8550d62040014db0aa1ac4080023ba1c435881000476c3886b102000a6e8510d62040014db0a21ac408003a350c43588100053742ce2b102000a6d859c562040018d8eb38ac4080031b1d4715881000733a8ca2b102000
  | 2 => 0xf31594100043ec3e62b282000a3e84cc5650400147b0998aca080029ba0b315941000536c1662b28200087e870c565040010fb0e18aca080d21f61e7558c101a52ec1ceab182036a5f835d563040050fd0bba2c6080021f6177458c100043ec3ea8b182000a5d83d5163040071bd0fa9ac60800317dd75358c101b62f43ea6b182000a5d84d4d63040014bd05a9ac6080db95c435358c101b72a886a6b1820038dc8754d63040071bd0fa1ac60800297a174358c100052ec2e86b18200287e85dc963040010fb0bb92c60801e1fe1c5258c100043ec38a4b182000a3d8414963040014bb06292c60800317dd67558c100052ec24eab182000a5e829d5630406dcae213aac6080db954427558c100062fc3aeab182000a5f845d563040014b904baac6080d395c417558c101a72a882eab182000a5e85dd163040014bb0bba2c60800297a167458c100052ec2ce8b182000a5e851d163040014bb0a3a2c608003275d07458c1000567410e8b182000acd821d163040014bf0faa2c6080029761f5458c100052f416a8b18206fe5710d5163040dfcaa21aa2c6081a2976165458c100070faa4a8b182000a5e85dc963040014bb0bb92c608003175d77258c100052fc2ae4b182000a5c855c963040018baeab92c608002b52057258c100052f428e4b182000a5d851c9630400153d08392c608002a76107258c100046f438a4b1820008dd87149630400153d08292c608002a76105258c100052fc38a4b182000c5e8714963040014bb0e292c6080031761c5258c100042ec38a4b182000e1e8414963040014bb08292c608003876105258c100050ec20a4b182031a5e821496304067c9e40292c6080cf934805258c1019f2b880a4b182033e551014963040014bd0ba12c608002976174258c100046f43884b1820008dd8710963040014bd0a212c608002976144258c100052f428e2b182000a5d851c56304001caea328ac608002b3e095158c1000566412a2b1820048de87d0563040011bb0fa0ac60800297a174158c100052ec2e82b182000ace82d05630400159b05a0ac60800297a144158c100052ec2882b182003ada8010563040015b30020ac6080069720f7654c100062fb9eeca98200087d84dd953040050ff07bb2a60800317e0f7654c100143ec1eeca982034c5c83dd9530400f0fd05bb2a60801e1f20b7654c100062f996eca982000a5f835d953040018bee6bb2a6080021fe117654c101b43fc1aeca982000c5f835d9530400f0f904bb2a60800317cc97654c100043ec36e8a98202cc3e64dd153040d58bcc7ba2a6080021fa1d6454c100061fba2c8a982000c3e87591530400187b0eb22a6080db0fdcd6454c100070fb9ac8a982000c3c725915304001c3e64b22a6080d38dc416454c101a71a882c8a982002a5e8758d530406d8b
  | 3 => 0xa992200087c87d95324400187eebb2264880030f1d7644c91003c6f43ec69922000c5f75d8d32440018b8ebb1a64880e65721d534c9100052f432a69922000a5c8654d32440018bceca9a6488003171d9534c9100070fb22a6992208de1c6454d324406bc98c4a9a64880063ba1f624c91000637baec49922000c6c75d893244001c9aa7b1264880039518f658c5100074a31ec918a2000e94631923144001a6ae8aa4628819f9518d548c51000d6b436c718a2000cd676d8e31440015a90ca1c6288003b118f628c510006733b0c518a2000ea46418a3144001d88c631462880ab9518e528c5100072a18eca98a203ccd870d8d3144001d8862312628810b1d1db654c5100072a31eca98a20038f4865d131440073e100ba262882cb2d1db644c51058e5a3b0c898a2000e946319131440d18e8ecaa26288007351db734c5101e66a3b6c698a203fce476d89314407d9c8ec3126288003a9190624c51000762318c498a2031c74769493144079ba6e6382628800a1f216768851022636294ed10a201c87c865d621440018b8c6bac42881f31b18975885100043fc3ecb10a200987d87d96214400f4dd05b2c4288003179d763885100062ebaec710a2000e4c52d8e21440394dd0bb1442880031b9d7628851000636baec510a20b087e86dd521440018b8c7baa42881d31b18b754851057c3f43eca90a204287c87d9521440018beebb1a4288003171d7634851000637baec490a2000c6c75d89214407f9d0e1b1242880e71b14a760851003d37416ca10a2000e4c52d8c21440374dd0bb1042880033918b714c1100066bb18e29822000ce4621c530440073a90e98a608800eb5219314c11001de8402629822039c6c529db204400f4dd05b2e40880039314b63c81100a53742ec59022007ce4629c72044073ac8a538e40880021fe1576481100143e42aec90220008df835d920440031b906bb240880021fa1b75481100062e31eea9022057c6c62dd52044063ae021baa40882ba1fa1f65481102bc3e43eca9022007a6e82d9520440018beebb1a4088003171d7634811000726296c69022010a6e85d8920440018deebb1240880031b1d762481100066a31ee29022000cd4631c520440019cec438a40880035914871481102163d3b6cb882203ccda76d8f10440039b4ec31e20880071e9d953c41101fe753b6c58822007cea7618b10440010fb09b9aca0801e1fa0b73594100062fb9ce6b28200087e8790d65040010fb0f21aca080021fa1c43594100043ec3886b282000a6e8210d65040014db0421aca0801e1fa1f725941003c3fc3ae4b282000a5e831c965040014bb06392ca0801f1b9c872594100043f43e64b28200087d87cc965040010fd0e192ca080021f61c32594100051f42064b282000a3d840c9650415b4f30138aca080161fa1
  | 4 => 0x244001c9eca318c48800393194631891000747b20c63122000e8c6418c6244001c9d0a318c48800393614631891000727ba8c63122000e4c7518c6244001d8b02318c4882cfb1840631891059f62080c63122000a6e86d4c62440014d90da98c4880031b9db531891000717b26a63122000e2c64d4c6244001c9ec7a98c4880039318f531891000537432a63122000a6c8654c62440018dceca98c4880038bd91531891000716322a63122000e4f6354c6244001c98c6a98c48801e9ba1f531891003d3643ea63122000a6d84d4c624406b4db0b298c48800393d4e531891003d3743aa63122007a6c8754c62440014df08a98c48800393e0d53189101af2739aa63122035e4d7354c62440c14dd0a298c4880029ba16431891000536c2c863122000ae68190c62440015cb03218c4880029ba15431891000536c2a8631220078ee8710c62440011db0e218c4880029ba14431891000536c28863122000e8d4310c62440391df0ea88c48801e3b21d511891003c7743e6231220008ed87cc462440014dd0b988c4880029b617311891000557426623122000aad84cc462440014dd0a188c4880029b61431189100053742e603122000a6d85cc062440014df0a880c4880029b215101891000567c1a203122000acc83440624400f0fd0d3b4a4880e71b18a76949100043ec1ced292200787e829da524400f0f9053b4a4880e71b20a76949100043e432e72922000c3c645ce52440558b8c6b9ca48801f1b18973949100043fc3ec72922000c5d73d8e52440554bd0db1ca488003179db63949100062e3b6c72922000e1f64d8e5244001c98c5b1ca48800317e1f63949100062e43ec72922000c5d74d8e52440018bce5b1ca488003939cb63949100043fc3ac7292200787c8758e524400147f08b1ca4881968f211639491000537c12c72922007a6c8258e52440014bd0c31ca488003179d863949100062e3b0c72922000e1f6418e5244001c38c831ca48800393188639491003d37436c52922000c6e76d8a52440738d8edb14a48800393d8f62949100072631ec52922039a6d87d8a52440018db0fb14a4880031b5cf62949100143f42ced192200087d859da32440010ff0abb4648800a1f215768c9100045fc22ed19220178bc845da324400f1d904bb4648801e1fa1f658c91003c3e43ecb1922000c3f75d923244001878ebb24648800317dd7638c9100062e3aec71922039c6f75d8a32440738d8ebb14648800a1fa17764c9100043ec2eec99220178be84dd9324400117b09bb2648800a1fa16764c9100043ec2cec992200087f855d932440050f90abb264880022fe11764c9100bc5e422ec99220008ef825d932440011ef02bb2648800a1f214764c9100043f436ea9922000c3c64dd532440558b8c7baa64882431b18b754c9100043f43ec
  | 5 => 0x80029ba1443d891000536c2887b122000e8d4310f62440371df0ea8ec4880fe3b21d51d89101fc7743e63b1220008ed87cc762440014dd0b98ec4880029b61731d89100055742663b122000aad84cc762440014dd0a18ec4880029b61431d89100053742ee1b122000a6d85dc362440018dcebb86c4880031b9d570d89100053742e61b122000a6d85cc3624400f8d8c4bacc488003179cf65989100062f398cb3122000c5f655ce62440018b8cab9cc48801f3318973989100062f3aec73122000c5d75d8e624400193ce9b1cc488003275d363989100062f3a8c73122000c5d7518e624400193ce831cc488003275d06398910006373aec53122000c6d75d8a624400199ce7b14c488003335cf62989100143f436eab12200087e87d9562440018b8e7b2ac4880021fa1c65589100062e398cab122000c5f65dcd62440018b8cbb9ac48800237a1f63589100062fbaec6b122000c5c75d8d624400193ee9b1ac488003271d363589100046f438c6b122000c5f7518d62440018b8ea31ac48800327dd063589100064e3a0c6b12200087d83dd562440011bf06baac4880063720d755891000477c12eab122000c5f75dcd62440018b8ebb9ac48800327dd373589100062fc2ee6b122000c5c85dcd62440018bca5b9ac4880031714b73589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100043f43ea6b12200287c87d4d624400187ee9a9ac48825b0f1d353589100062fb9ea6b122001c5c73d4d62440010fd0ea9ac4880021f21d53589100061fba2a6b12202cc3c7454d62440018bee6a9ac488007171cd535891000637baee4b122000c6c75dc9624400199ee7b92c488003331cf72589100066a39ee2b12200287e859d862440010fb0b3b0c4880e71b94a76189101ce36294ec3122007a6e82d94624400f4dd04328c488003171d7631891000726296c63122000c5c7518c6244001c98a4318c4880023be1d621891000537c2ac43122000a6c85588624400159f06b10c488002b320d62189100053742cec3122000a6d859d862440738d8eb3b0c4880031ba16761891000636c2cec3122000c6e76d9462440014db07b28c4880023b61e65189100056741cca3122000acd8399462440011df0eb28c488002b3e0d65189100056641aca3122000c6e76194624400f4dd0e328c48801e9b21c651891000536c18ca3122000cce76d8c6244001c9ecbb18c48800393197631891000747b26c63122000e4f85d8c6244001c990bb18c48800393dd76318910007263aec631220008ed8798c62440014dd0b318c4880029b616631891000557424c63122000aad8498c62440011df0eb18c4880029be1563189100053642ac63122000aaf8458c624400155908b18c4880029ba14631891000536c28c63122000cce7618c6
  | 6 => 0x143e42aeca1a20008df835d943440011df04bb2868801e3b2097650d100143f428eca1a200087d851d94344001938863b286880021f2197550d1033e2e31aeaa1a203996c825d543440010ff0fb2a86880021f61f6550d100070e21ecaa1a20178de87d8d43440018bcebb1a8688003175d76350d100bd4f426c6a1a203987d87d9762440734dd05b2ec4880e61f61c65d89101cd37410cbb122000c5e75d8f62440018baebb1ec488003179d463d89100062eba8c7b122007c6e7614b624400169b06296c48800393d8c52d891000726318a5b122000a5d839d762440010ff06baec4880031be0975d89100143fc3ea7b12200087d87d4f62440734dd05a9ec4880021fe1d53d89100043ec3aa7b122001c5c7354f62440734d904a9ec48800b1b9d652d891001477c3aa5b122000c6d7514b624400159d06296c488002b360c52d891000536c38a5b122039c6d8714b6244073c9d06296c4880029b60c52d89101cf26c18a5b122000a4d8314b624400f8dce2296c48801f1b1c452d89100053742e65b122000a6d85ccb6244001c9aa7996c4880029ba1432d891000536c2865b122000aae840cb624400155b08196c488002d360e75d891000536c3ecbb122000a6d83d97624400159d0732ec488002b360e65d891000567c1acbb122000acc8359762440014db0632ec48800393d9763d89100072632ec7b122000e8f64d8f6244001c9f0bb1ec4880039321763d8910007273aec7b122000e4d75d8f62440014dd0b31ec4880029b61663d891000557424c7b122000aad8498f62440014df0ab1ec4880029b21563d891000557c22c7b122000aac8458f62440014dd0a31ec4880029b61463d891000727b28c7b122000e4c6518f6244001d1ec831ec488003a319063d891000727428c7b122000e4d8518f6244001c9cea31ec488003935d463d891000762c08c7b122000a6e86d4f62440014d90da9ec4880038bd9353d891000716326a7b122000e4f63d4f6244001c98c7a9ec4880029ba1953d891000536432a7b122000e2f6454f6244001c58c8a9ec48800393d8d53d89100072631aa7b122000ace839d7624400159b073aec48800393a0e75d891000536c1cebb122000e4d839d7624400149b073aec4880031be1d75d891000537c1aebb122000a6e85dcf62440014db0bb9ec4880029ba1673d891000536c2ce7b122000aae849cf624400155b0939ec4880029ba1473d891000536c28e7b122000ae6811cf624407f5cb0239ec4880029be1f53d891000536c3ea7b122000a6d84d4f6244001c9ea729ec4880029be1d53d891000536c3aa7b122000a6f8454f6244001c9f06a9ec48800393dcd53d89100072639aa7b122000a6e8590f62440014db0b21ec4880029ba1543d891000536c2a87b1220008ee8710f62440011db0e21ec48
  | 7 => 0x3d84149634400187ee8292c6882d30f1d05258d100052ec18a4b1a2000c6f72149634400f8d8e4292c688003391cb7158d100062f3b6ca31a2000a5d87d9463440014bb09b28c68800297a0b6518d100072ab8eca31a20008dd8799463440014bd0b328c688002a7a126518d100054ec24ca31a2000ace82994634400159b05328c68800237e1d6518d100054fc22ca31a2000a9c84594634400159f04b28c688002b32096518d100052f430ca31a2000c5e7619463440014bf0e328c688002976106518d100052f410ca31a2000e56711946344001caae2328c688003279db6418d100070fb2ec831a2000e1c65d906344001c3f0bb20c688003872176418d100070f3aec831a2000e1d75d906344001d2ae3b20c6880023761e6418d100052f42cc831a2000a5d85990634400153d09320c688002b3a0a6418d1000566c14c831a20008df8759063440014bf0ab20c688002972156418d1000567c12c831a2000acc8259063440014bd0a320c688002976146418d100064f3b0c831a2000e1f651906344001c38ca320c688003879d46418d100070eba8c831a2000e957119063440014bd0daa0c6880029721b5418d100070fb26a831a2000e1c64d5063440012bb0e290c68800297a185218d100058ec20a431a2000e1f641486344001c38c8290c6880b28fa137654d100051ec26eca9a2035a6e82dd953440014db05bb2a6880021fa1a7654d100062e31ceca9a2000a5d839d953440018bee73b2a6880021f6127654d100043ec1ceca9a2000c5d839d9534400f0fd053b2a68800317cca7654d100051fc22eca9a202ca3c845d953440014bf06bb2a6880029be097654d101ad36412eca9a200087e861d953440018bee63b2a6880021f6107654d100143fc18eca9a2000c5f831d953440050fb063b2a6880031720c7654d1003c3f410eca9a200787c821d953440018be643b2a6880031d8c47654d100063a988eca9a200087e86dd15344059878c9ba2a6881ab1718f7454d100043e43ec8a9a2000c3f74d91534405947d0db22a6880030f9db6454d100061e3b6c8a9a2000e1c63d91534400187f0fb22a6880030f21f6454d100061fb9ec8a9a2000e1f73d915344001878e5b22a68800387ccb6454d100043fc3ac8a9a200087c8759153440014bf06b22a6880069720d6454d1000537c12c8a9a2035a6c82591534400147d0c322a6880030f9d86454d100061e3b0c8a9a2000e1c6319153440034bd0db1aa688003171db6354d100070fb26c6a9a2000e1c64d8d53440018bf0fb1aa68800a97a1f6354d100152e43ec6a9a2000c5c87d8d53440018bee9b1aa6880029760b6354d100062e396c6a9a200287e85dd943440010fb0bbb2868801e3ba0b7650d1000476c16eca1a200287c859d94344001938873b286880021fe157650d100
  | 8 => 0xc296c688247179d852d8d100058ec20a5b1a2000e1f6414b63440014bb09baec68800297a0b75d8d100062eba8ebb1a2000c5e871d763440014bb083aec68800297a0875d8d100052f42ce9b1a2000a5d859d3634400193ee93a6c688002b3a0a74d8d1000566c14e9b1a2000a5f855d363440014b90aba6c68800297a1474d8d100052ec28e9b1a2000ad6811d363440795ab023a6c68800297a1f54d8d100052e43ea9b1a2000a5e82d536344001c3ea92a6c68800297a1772d8d100052ec2ee5b1a2000c5f75dcb63440014bd0b396c6880029761672d8d100054f424e5b1a2000a9d849cb63440014bf0ab96c6880029721572d8d100062fbaae5b1a20008de8714b63440011bb0e296c688002a7a1052d8d100054ec20a5b1a2000a5e8714b63440018bd0e296c68800217a1c52d8d100062ec38a5b1a2000a5c8714b6344001c3d08296c6880029761052d8d100070ec20a5b1a2000a1d8414b63440014bd0ba16c6880029761742d8d100046f43885b1a20008dd8710b63440014bd0a216c6880029761442d8d100052fc2ae3b1a2000a5c855c7634400153f08b8ec688002a721171d8d1000567c12e3b1a2000acc825c7634400159f04a8ec688002b320951d8d101e46f43e83b1a20008dd87d0763440014bd0ba0ec6880029761741d8d100056741683b1a2000acd82d0763440014bd0a20ec6880029761441d8d100052fc2ae1b1a2000a5c855c363440014bd0ba06c6880029761740d8d100062e31eeab1a200087e87d956344001878e9b2ac6880021fa1c6558d100061e3a0cab1a2000c3f65dd16344001878cbba2c6880032718f7458d100061fbaec8b1a2000c3c75d9163440018decbb92c6880031b1977258d1000657b26e4b1a2000ccc63dc963440018deca392c6880031b1947258d1000657b20e4b1a2000ccc631c963440050fd0fbaac6880021f6137558d1003c3f416eab1a20008bf845d5634402f17908baac68800237e0d7558d1000477c12eab1a20078ec825d563440010fd0e3aac68805e2fa1f7458d100061fbaee8b1a2000c3c75dd1634400187f0bba2c6880030f2177458d100061fa9ee8b1a2000c3d53dd1634400187eea3a2c6880030f1d47458d100043f43ea8b1a200287c87d51634400187ee9aa2c68805f0f1d35458d1049636396a8b1a2000c5f75dcd63440018b8ebb9ac68800327dd37358d100064e3a6e6b1a200287e85dc963440010fb0bb92c68801e3ba1f7258d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000667b9ee4b1a2000c6e85dc963440018db0bb92c6880031bd537258d1000637a9ee4b1a2000c6d53dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c6880021fa1c5258d1003c3e438a4b1a2000a
  | 9 => 0x62c83100a53642ac59062032d64529c720c40214d90ab1241880035914871483100143f42ee4b1c200087d85dc9638400147b08292c7080029760c5258e100052fc1aeca9c2000a5f8359153840034b906b22a70800a1fa177650e100043ec2eeca1c204496c825d543840071b90eb1a870805ea72116350e100143f43eeab14200087d83dd562840638db05baac5080c61fa1c7558a100043f43ea6b14200287c87d4d62840010fd0ea9ac5080021f21d5358a1022536412a6b1420038ee87d4962840674dd0ba92c5080031bdd75258a1000637ba8a4b142000acd8314962840634dd0e292c5081131ba1c5258a1022727418a4b142000a6d831496284089c9b06292c5080029360c5258a100043fc2aed194200287c855da32840898d8eab1465080021fe15764ca100143e42aec99420008bf845d9328402f17908bb265081125721d534ca101af27312a699420038ec8758932840018d8eab126508006b320d624ca1000726a9ac4994203e8ef8758b21840018d8eab1243080028fa1263d95100051ec24c7b2a2000a6e8298f65440014db0531eca880261f61c63d95100062eb98c7b2a200087f845cf654400f0f904b9eca88003175cc73d95105ad3b408e7b2a2042a75811cf65440010fd0f21eca880021f61e43d95100043f43887b2a200087d8710f65440014dd0421eca880029b60843d95100052f41ce5b2a2000a5d839cb654400f0ff0eb96ca8801f1b9c872d95100043f43e65b2a200087d87ccb65440010fd0e196ca880021f61c32d95100051f42065b2a2000a3d840cb65440850fd0f98eca880021f61f31d95100051f42663b2a2000a3d84cc765440014dd0598eca880029b60b31d95100043f43863b2a200987d870c7654405b4ed03b86ca880021fa1f30d95100043ec3e61b2a2001c5e76d4f63440014bb07baec6880029760c75d8d100043fc2ae9b1a200287c855d363440010fd0faa6c6880029760f54d8d100062ebaea7b1a2000c5d87d4f63440014bb09a9ec68800297a0b53d8d100146fc3aa7b1a2000a5e85d0f63440014bb0ba1ec6880021fe1572d8d100143e42ae5b1a200087e8714b634400f0f90e296c6880028f61052d8d100052ec18a5b1a2000a5e861d763440014bb09b2ec68800297a0b65d8d100054f424cbb1a2000a9d84997634400159d0532ec688002b360a65d8d100054fc22cbb1a2000a9c84597634400159f04b2ec688002b320965d8d100052ec20cbb1a2000a5e821976344001c3ecbb26c6880038719764d8d100070fbaec9b1a2000e1c75d9363440014bd0b326c6880029761664d8d1000567414c9b1a2000acd8299363440014bd0a326c6880029761464d8d100052f436a9b1a2000a5c86d5363440d58bcedaa6c68800387d9354d8d100070e326a9b1a200095e8714b63440014bd
  | 10 => 0xa984000a5f835d953080d58bcc7ba2a61000a97a1d6354c200152e43ac6a984000c5f7458d53080034bf04b1aa610006976096354c2003e2f392c6a984007c5c7258d530806bc9842b1aa6100d393c816354c201a726902c6a98400287e85dd943080010fb0bbb2861019f1798d7550c2003cb6412eaa1840038dc8758d43080018baeab1a861005ea72116350c2003c76412eb30840038f587946610800f5c904a8cc21000a1fa1f75584203a636396eab08400087d83dd561080391df04baac21001e3b209755842057e36390eab08400087e87d4d61080050f90fa9ac2100021fa1d53584200043e43aa6b084002c747594561080071e90ea8ac2100021fe15768c4200143e42aed18840038f58798631080010ff0abb2621000a1f215764c42000476c36e498840038f48758531080018dceabb442100031bd4d768842000636bb2eb1084000c6d7654e2108001c9ac6a9c42100729b21561884200043fc2ae5b1e200287c855cb63c400147b08296c7880029760c52d8f1000477c12eab1e20078ec825d563c40014bb07aa2c78800a1fa177258f100043ec2ee4b1e2000a3d8414963c40014bb06292c7880031bdc85258f1003e36390a4b1e2000a5d839d953c40014bf06bb2a7880029be097654f101ad36412eca9e2001a5e83d9153c40014bb07b22a78800a1fa177650f100043ec2eeca1e20078ee82dd943c40011db05bb2878800a1fa147650f100043ec28eca1e203296c825d543c402f1bd0fb1a878805ea7a136350f1003e373b0a5b162000b4d8314b62c40010ff06baec5880031be0975d8b100143fc3ea7b16200087d87d4f62c40010ff0ea9ec5880021f61d53d8b1019536412a7b162000c6d75d4b62c40018daea296c588002b360c52d8b1000536c38a5b162032c6d8714b62c4065c9d06296c5880029b60c52d8b1019726c18a5b162000a4d8314b62c4001cc8a538ec5880039a14970d8b100143f43eeab16200087d83dd562c40011df04baac5880021fa1c7558b100043f43ea6b16200287c87d4d62c40010fd0ea9ac5880021f21d5358b10006363aee4b1620008ef8758862c40014d90ab10c58800a1fa16768cb100043ec2ced196200087f855da32c40050f90abb4658801e3b209768cb10196363aec5196200287e859d932c40010fb0b3b2658805e2fa12764cb100045ec24ec996200087f855d932c40050f90abb265880ca5721d534cb101af26312a699620018ee87d8932c40018d8ebb126588006b3a0f624cb1000726a9ec499620038f586dd231c40d18eaecaa463880034d5d1548c71018e3abb4a518e20038de87d8d31c400136b09bb26388002f4603634c7100e53642ac510e2000d68525c221c40018d8ebb1243880023be1d62087100dd3642ac410e2032d68525c021c40073a90e98a61880fe3be1d
  | 11 => 0x480015c902b24649001e5b21d548c92000696ba2a9192401096c855c632480670fd0dbaa64902461fa1f654c92018c3e43eca992400795c8754d32480014bd0ca9a649000297219534c920326b4296e0992401096e87dd532480558d8edbaa64900ab9318f754c9205bcb743eca9924031c6c76d953248001c98c7b2a64900425b217744c92001c76432e8992401096c855d1324800359907b226490003a390f644c92000c7643ac89924001acc8359132480015c902b2264900025b21d544c920346363b2a89924067e4c63551324800359d0db1a649004353e1d534c92003da743aa69924007b4c8754d3248021a990ea9a649001e5321d534c92000727c32a69924000b4e8654d32480016990ca9a649000393219534c92000526432a69924001e4f7654d3248003c98eca9a6490002d3e11534c92000727b22a69924000e4d6454d324806bc9ec0a9a64900d7d2d81534c92000566432869924000b4d8550d3248001d1ac8a1a64900fa3ba1b714c920006b43aee09924000f4953dc13248001ad6ea3826490003d254c704c920005a6c18a5b0a4000ab684cc761480012db0e294c2900029ba185298520005a6c18a530a400287e86dd561480630f90dbaac2900021fa1f65585200062e39ecab0a400087e8719561480018b8e632ac29000317d9773585200062e32ee6b0a400096e87149614800169b06292c29000353dcc52585205b6a6398a4b0a4033c6d7219461480014dd0c290c290002d360c52185200047bc3ac230a4000ad483584614800f1d904ba8c290007179cd53185200062eb9aa630a402fa6c8254c61480018deea290c290002b360c521852000572c08a430a402fc6e87148614805f8db0e290c2900bf93a0c521852000536c18a430a402fe4d83148614800149b06290c2900bf99a04521852017f32c08a430a4007c6d70148614805f4d90b190c290002b960632185200053642a6430a4000e4d534c861480015cf02990c290002ada13311852000572c166230a4000e6452cc46148001cc8a4188c2900021fe15768c5200143e42aed18a401096c855ca31480050fd0bbb262900021f617764c52000636296ec98a4000c6c521d931480018d8cb3b642900031bd4e76c8520006373b6cb90a4000c6e7654f2148001a9ae6a9e42900ce1f21975885200043ec3ecb10a402fe64521862148073ad0a4b8442900ce1fa1b75485200043f43eca90a402fe66521852148065ad0a5b8242900425ba1f7548520004b743eca90a4031c6c76d9521480212d90bb9a429000e3b2197348520084b642ae690a400096c8754d21480018d8ea30a429000399d946148520006b43aee090a4000d6b751c121480212dd0bb9260900029760f5458c2001c6e43aa6b1840018ed82dc563080050fd0a38ac6100021f6147158c2000d2e41eec
  | 12 => 0x15a9ba0b75d8d200052ec18ebb1a400087f855d363480050f90aba6c6900021fa1f54d8d200052ec1ea9b1a400287e859c763480010fb0b38ec6900021fe1571d8d200143e42ae3b1a40008bf845c7634802f17908b8ec69001e3b20971d8d200043f43ecab1a4000c3c74d9563480010fd0e32ac6900030f1d06558d200061fb2ee8b1a4000c3c65dd163480012dd0e292c690002cb6105258d2000697ba0a4b1a40b8d2c74149634800169b06292c6902db9318c5258d200063bb2ee2b1a4000c7465dc56348001ac8a5b8ac6900031dd947158d200063a328e2b1a4000cd4631c56348001ac8a438ac69000a1fa1f7558d200043ec26eab1a40008bf845d5634802f17908baac6900023de057558d200047a40aeab1a400087e871d5634802f17d0fba2c6900030fdd77458d200061e3aee8b1a4000c3f85dd163480018790bba2c6900030fd4f7458d200061ea9ee8b1a4000c3e52dd16348001878a5ba2c6900030fdd47458d200061e3a8e8b1a400087e87d5163480050f90faa2c6900030fdd35458d200be1e3a6a8b1a4000c9c74dcd63480018eeebb8ac6900031d1d77158d200065bba6e2b1a4000cb474dc563480018eea9b8ac6900031dd4f7158d200063aa9ee2b1a4000c7652dc563480018e8a5b8ac6900031ddd47158d200063a3a8e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a4000c77541c563480018eea638ac6900031d54c7158d200066b218e2b1a4000c76521c563480018e8a438ac6900021fa1a7654d200052ec1ceca9a400087d849d953480010fb073b2a6900031760e7654d2000636c14eca9a4000c5f329d9534800147f08bb2a6900b28f2117654d200052fc1aeca9a4000a77815d953480014e902bb2a6900021fa187654d200043ec20eca9a400287f831d953480050fb063b2a69001e1fa087654d2003c3e410eca9a4000c5f321d953480018dc643b2a6900031b4c87654d200043f436e8a9a402cc3c64dd153480010f90fb22a6900030fdd36454d200043fc3ac8a9a400087c8759153480014bf06b22a6900069720d6454d200053bc0ac8a9a4000a7481591534800f2dd0fb92a6900d29ba1b7254d20006373b6e4a9a4000c6e761c9534800165b08392a69000a1fa177650d200043ec2eeca1a4000c6c52dd943480050f90b3b286900032710e7650d200043fc2aeca1a400287c855d943480011bf06bb286900023de057650d200047a40aeca1a400287e851d943480010fb0a3b286900032710c7650d2000636290eca1a400087c865d5434800f2d904baa86900021fe1f6550d200043ec3ecaa1a4000a5d83d954348001c3887b2a869005e3721d6350d200bd4e422c6a1a4000ad48158d43480212dd0b3b4649001e5ba1f658c920084b642ae91924001acc8359232
  | 13 => 0x6363aeec90e40af96e87dd521c80018deedbaa43900525b21773487200a4b642ae690e400096c8754d21c80018d8eb30a439001f331c9634c3200a4b742ee4986400087d84dcd65880018bee739acb100021fa1e43596200043ec3c86b2c400087e8710d65880010fb0e21acb1016a9ba08435962000536c1086b2c40b9a7b805c965880010fd0f992cb100021f61f32596200063bb8ce2b2c4000a6f825c565880b54d904b8acb100021fa1f31596200043ec3e62b2c4000a3e84cc5658800147b0998acb1016a9ba0b315962000536c1662b2c400087e870c565880010fb0e18acb100d21f61e7558e200051ec24eab1c4034a5d839d5638806d4bf06baac71000a1fa177458e200043ec2ee8b1c400087d87d5163880050fd0bb8ac7100021f6177158e200143f428e2b1c400087d851c563880010fb09bb2a71000a1fe0f7654e200143ec1eeca9c4000c5f32dd953880698de41bb2a7100d31b4837654e200052fc1aeca9c400087f845d9538806d0ff06bb2a71000317e0d7654e200062f992eca9c400087d86dd153880010fd0eb22a71000297e0d6454e2000d2e41ac8a9c400287e85dd943880010fb0bbb2871000a1fa157650e200043fc32eaa1c400796c825d543880010ff0eb2a87100021f61d6550e200070e21acaa1c40038dc8758d438802f53908b1a87100021f61b754ca201543f43aca994409187c8759532880b5c9864b2a651001e5721d534ca200052fc32a69944000a5d8654d328800f69904a9a651003f93589534ca200062fb9aa6b0c4001c5c7354d61880071eb0f30c63100031b997724c62001c7a43ac298c400087f865d621880010ff0eb2c43100cb9914a61886201cf33292c310c4039d6a525c221880014df0cbac43100729ba15638862000537c32a710c4000d69755c221880010fb0dbaa43100021f21d65486200dd3742ac610c4000a6f8654c21880210fb0e31eca900028fa1063d95200051ec20c7b2a4000c5d7318f65480af4dd05b9eca900c69b60b73d952000636b96e7b2a4000c6d725cf65480010ff08b9eca9001e1fa0973d952003c3e412e7b2a4000a3e841cf654800147b0839eca90003175cc73d95202bd37410e7b2a4031a6d821cf65480010fd0f21eca900021f61e43d95200062eb9c87b2a400087e8710f65480010fb0e21eca9015e9ba0843d952000536c1087b2a403187e87ccb65480010fb0f996ca9015e9ba0b71d952018d36c16e3b2a4000c6e729c765480af4dd0438eca900c69b60871d95200043f43e63b2a400087d87cc7654800147d0998eca900028f61331d95202bd3741663b2a4000a6d82cc765480010fd0e18eca900021f61c31d95202bc3f43e61b2a400087d87cc365480012dd0e296c690002cb61052d8d20005a6c18a5b1a40038ed82dd763480014bb07baec690
  | 14 => 0xd8414b614c0014bb06296c29801f1b9c852d853000636b90a5b0a60008f787584614c0015c904b08c29800a1fe1d75185300043fc22ea30a600787c825d4614c0050ff0faa0c2980021f61f54185300043fc3aa830a600087d87550614c02f938e8a18c2980021fe1572185300143e42ae430a600787f87948614c0010fb0f290c29801e1fe1c52185300043ec38a430a6000a3d84148614c0014bb06290c2980021fe1576905300143e42aed20a600287e851da414c0010fb0a3b4829800667e1d43905300bd4e4328720a6000c9e7650e414c0050fd0a3b282980021f614765053001c6e432e898a600c8de87185314c0050fd0b3b642980021f61676c85300143f428ed10a600087d851da214c0394dd0bb14429800a1fa1676485300043ec2cec90a600087f855d8214c0050f90abb042980022fe1176085300bc5e422ec10a6007ccc625cc214c0374dd0bb1042980039914b610853000732290c210a60078f8865c0214c0a9ad0a4b8042980033c185700853001d4e43286a026001c9c7650d404c00773100a1a809800e3b2097558f200052ec1ea8b1e40078dc8754d63c800f59904a9ac79000a1fa177158f200043ec2ee2b1e40178be84dc563c800117b09b8ac7900069720f7654f200052fc1aeca9e4034a6c825d953c80d58bcc7ba2a79001e5b20b7454f200152f43ac6a9e4002a5c8758d53c80018bee8b1aa79001f179c96354f2003e2e392c6a9e4035e4c7258d53c800f898e4b1aa7900d7939096354f2003cb743ee4a9e4000e4d63dc953c80050fd0bbb287900021f6177650f2001c77416eca1e405fc6c52dd943c80cf8bcc6baa879001e5b2097550f2003c6e43ac6a1e4000c5d7558d43c802f53908b1a87902ea5ba1f754cb200a4b642ee8996401496c855d132c80012d90eaa265900038b591544cb200a6a7c3aa69964007b4e8754d32c800f6990ea9a65900d75321d534cb2003ca643aa69964000e4f8654d32c806bc990ca9a65900d753dd9534cb2006f27bb2a69964000b4f8454d32c806bc9ec8a9a659000393591534cb20005a6c2a869964000e8d6450d32c80071dd05bacc39001e9b20a759872056637394eb30e407cc6c525d661c80050ff0ebacc39001e9b20975987203e637392eb30e400087f835d661c80018df04bacc3901f31b20975987200143fc3ea730e400087d87d4e61c800f4d905a9cc3900021fe1d53987200043ec3aa730e4007a6c8254e61c800f4dd0ba94c3900031b5d7529872000572c0ea530e4000a6c854ca61c800399ce6994c3900039354d329872001c76412eab0e400287e85dda31c80010fb0bbb4639005e2fa13768c7200045ec26ed18e40038ee82dda31c800f99ce4b1c63900525b215728c7200143f42eec98e400087d85dd931c80071dd05bb263901731b14b764c72000
  | 15 => 0xa3a2c3180021fa1f54586300143e43ea8b0c6000c3f74d51618c02f878e9aa2c3180029760f545863049636396a8b0c600087e87551618c0010f90eaa2c3180030fdd154586300be1e3a2a8b0c6069c6c72551618c0050fd0bb92c3180021f617725863000637baee4b0c6000c6c75dc9618c00195ee9b92c3180032b1d372586300063742ee4b0c6000c6d85dc9618c0018dea9b92c3180031b553725863000637a9ee4b0c6000c6d53dc9618c0018deea392c3180031b1d4725863000657ba0e4b0c6000cac741c9618c0010fd0f292c31801e1f21e52586300061fba4a4b0c6065c3c74949618c0018dee5292c31801f1b1ca52586300043f438a4b0c600787c87149618c00147b08292c3180030fdd052586305a61e3a0a4b0c6000a5d83149618c0018dee4292c31801f1b1c852586300043fc2aed20c600287c855da418c0071eb0f30c831805ead21161906300043fc2aeca0c600287c855d9418c0011df04bb2831801e3b209765063001c7a43ac2a0c60408df87586318c00153f08b0c63180fa3be1d62c86300143f42eed10c600087d85dda218c0018d8a5bb443180031b14976886300043fc2aec90c600287c855d9218c00117f08bb2431805e2f2117648630006363aac490c600087f855d8218c0050f90abb0431815b1b14976086302b6b4292e010c60028bf87553644c0010ff0ab96c89800a1f21572d91300051ec20a5b226000a5d8314b644c0010ff0ab8ec89800a1f21571d913000c6e41ae3b2260008ef825c7644c00f1d904b8ec8980023be09755913003c76412eab2260008f7815d5644c0011e902baac89800a1fa1772591300043ec2ee4b226000a5d83149644c0018dee4292c89801f1b1c852591300143f428e2b22600087d851c5644c00147b093b2a8980028fe11765513000537c12ecaa26069a6c825d9544c0014ef02bb2a8980029d20576551300bd1f436c8aa26002a3e87d91544c0054790fb22a8982ef0fdcf64551305de1eb9ec8aa26000a3d82d91544c001878e5b22a8980b3171d97550d303558fc22eaa1a602ce1c645d5434c00169904baa869805ea7a1b6450d302046f436e2a1a6000a3d849d7624c0014bb073aec49800a1fe1d75d89300043fc22ebb12600287f87d53624c0010fb0faa6c4980021fe1d54d89300043ec3aa9b126017c3c74553624c0a94d904aa6c49805f271d143d893000477c3ac43126000ae481588624c0634b90ca1ca498003475d1439493032f0e32287292600287e859da424c0010fb0b3b4849801e3ba0a76909300043fc2aed212600287c855da424c00187eebb24849800a1fa1676509300043ec2ceca12605493c87551424c00187cecaa284980030f1d954509300064e3b286a1260078ee82dd7614c0011db05baec2980021fe1572d85300143e42ae5b0a6000a3
  | 16 => 0x350c215d4b743eea990421b96c85dd132084372d90aba264108025b21d544c82100716b22a8990421bd4f8754d320840f69d0ea9a641081ed321d534c8211aea643aa6990420794c8754d3208401c9f0ca9a64108d793219534c8211aea7bb2a69904220e4f7654d320840169f08a9a64108d793d91534c82100726b22a6990421fe4e6154d320846be8cc2a9a6410802d3615434c82100746b22869904207cce7258e31084372d90ab9462108031b1d7764842100637a9eec9084200ce651dd921084019caa3bb24210abe5ba1f754842100637bb6ea908421b96c85dcd21084011df0cb9a421086e5b2157348421004b643aa69084200c6f7654d21084071db05baac01095f1b14b75580210143f43eeab004207a6e82dd560084af8d8e5baac0108021f60f75580212be37416eab004200c6d82dd5600840f4d9043aac010abb1b1c875580210043f43ea6b00420287c87d4d600840f4d905a9ac0108021fa1d53580210043e43aa6b004207a6c8254d600847d1dd0fa92c0108031bdd752580211f575406a4b00423e8ec874c960084014d90a992c010807331cd325802100726a9a64b00423e8ec8748560084014d90a90ac0108faba20121580210163c3aca0b004207aea8294160084afcd0a5282c01081e3e21d50580212d734292a0b00420287e85dc9648c0010fb0bb92c9180028f61052592300052ec18a4b24600287e851c5648c0010fb0a38ac9180028fe1176552300143f43eeab14600087d84dd5628c0638db05baac5180029760c7558a300043f43ea8b14600287c87d51628c0014bb07aa2c5180021fa1d5458a300043e43aa8b146056a6c82551628c0674dd0ba92c5180031bdd75258a3000637ba8a4b146000aad84149628c00159b06292c5180c69ba1c5258a302b637438a4b146056e2e84149628c0014db08292c51815b8b6105258a3000516c20a4b146056a6f83149628c0adc9d06292c5182de9b60c5258a302b726c18a4b146000a4d83149628c0018d8a438ac51800257e0d7494a300043fc2aed214600287c855da428c0ad8d8eab1485180021fe157650a300143e42aeca1460008f7815d9428c0011e902bb2851815a4f21d5450a3034f17312a8a1460038ec87589428c0018d8eab12851805eab2116250a3000716aa2c4a1460008ef825d6618c00f1d904bacc3180021fe1572986300143e42ae530c6000a3d8414a618c0014bb06294c31801f1b1c852986300143f43eeab0c600087d84dd5618c00f0fd05baac3180022fe1175586300bc5e422eab0c60008ef825d5618c00f1d904baac31805e2fa1f74586300061fbaee8b0c6000c3c75dd1618c00187f0bba2c3180030f21774586300061fa9ee8b0c6000c3d53dd1618c00193863ba2c3182cb27cc374586305964e986e8b0c6000c3f751d1618c001878e
  | 17 => 0x2a4274a6e8210f65484014db0421eca909c29da0772d95210043f43e65b2a420087d87ccb65484e90fd0f98eca908021f61f31d95210051f42663b2a4200a3d84cc765484e94dd0598eca908029b60b31d95210043f43863b2a421e87d870c765484e94dd04386ca908029b60870d95210043f43e61b2a420087d87cc365484010fd0e186ca908021f61c30d95210051f42061b2a4200a3d840c365484e94dd04186ca908029b60830d95210053b40861b2a4200a75810c365484014bb07baec6908028f61075d8d210052ec18ebb1a420087f855d363484050f90aba6c6908021fa1f54d8d210043fc2ae1b1a420287c855c363484010fd0fb2ac6908021fa1c6558d210143f43eeab1a420087d84dd563484011df04baac6908021fa1c7558d210043f43ea8b1a420287c87d5163484014bb07aa2c6908031b1d77258d210043f434eca9a4200a5d839d953484010fb093b2a6908021f60e7654d210062ec1ceca9a4200c5f329d953484014bf06bb2a6908029be097654d210043f430eca9a420087d841d953484050ff063b2a69080a1f60c7654d210062f990eca9a420087e86dd153484010f90fb22a69080697a0f6454d210052ec1ec8a9a420087f8759153484010f90eb22a69080a1fa177650d210043ec2eeca1a42008ed82dd943484050f90b3b286908021fe157650d210143e42aeca1a42008fb805d943484071f100bb2869080a1fa147650d210043ec28eca1a420087c865d5434840f2d904baa86908021fe1f6550d210043ec3ecaa1a4200e1c43d95434842f1bd0fb1a869085ea7a136350d210043f436ea992429187e87d9532484550f90fb2a64909d3930cb654c92103cae43aa69924200a5e8654d32484014b90ca9a649081ed3209534c9210063632ee498a420787c865d6214840f0fb0fb2c429081e9b21975885213e6373b2eb10a427cd66715d621484394dd0db2c42909d399d8765885210e53642ec710a421ca6c8558e21484014d90ca9c429081e3b21970885210063632ae110a423fce8605c221484071d904baec09080a1fa1b75581213a43e436eab02420087e87d9560484018b8e7b2ac0908021fa1c65581210062e398cab024200c5f65dcd60484018b8cbb9ac0908023ee1d601812103c76412eab184200a5d83d51630840f1b90ea9ac61081eb32095358c2100d2e41eeca984200a5f835d9530846b4d904bb2a6109ab1798f7454c2103cb6416e8a984202a5e8758d53084054b90eb1aa61080317dd16354c2103e2f392c6a984207c5c7258d530846bc98e4b1aa61081f131c96354c211af27212c6a98420796e87dc95308401c9ac7b92a61080a1fa177650c210043ec2eeca1842078ee82dd943084bf8d8a5bb2861099f1798d7550c2103cb6412eaa1842078dc8758d43084018baeab1a861085ea72116
  | 18 => 0x845987cc9ba2a7108021fa1f6454e210043ec3ec8a9c4201a5e83d9153884014bb07b22a7108021fa1d6454e210061fba2c8a9c420796e87dc953884018daedb92a7108031b5d87254e2100596c20e4a9c420287e85dd943884010fb0bbb287108032710f7650e2100636296eca1c420287e859d943884010fb0b3b287108023760e7650e210143f42aeca1c4200c9c435d943884050fd0a3b287108021f6147650e2100636290eca1c420087f865d5438840f2d904baa87108021fe1d6550e210043ec3acaa1c4200a5f835954388401c3886b2a871085e37a1f6350e210bd4f426c6a1c421c96c855da328840f2d90eb2c65108725b215748ca2100d6741ec9194420796c875523288401a5ae8aa465108725b215718ca210043ec36ea994422a87e8759532885230f90eb2a651081e5721d534ca210052fc32a69944200a5d8654d3288501acca5b8a65108033558c714ca2141eb2290e2994421c96e87dd532884558deedbaa65108ab9398f754ca215ecb643aca9944200c6f765953288401c9cc6b2a65108725b217744ca210e4b642ae899442018ee87d91328840359d07b226510806b3a0d644ca210074721ac8994420096c8755132884cf8deecaa2651099f9398d544ca2100d67c32c6994421cd4f8754d328840f69d0ea9a651081ed321d534ca210e6a643aa6994420794c8754d328840169f0ca9a651080393e19534ca2100527c32a69944200b4d8654d3288401c990ca9a651080793dd9534ca2100f263b2a69944200b4f8454d3288401c9ec8a9a651080393591534ca211af2730aa69944200acf8650d328840169b0aa1a6510803a3d91434ca21006b3baee29944200f4553dc53288401ac8ea38a6510803d154c714ca210e4b642ae518c4200c6e655db21884018daecb2e4310803535cd53c8621004b6c38a5b044200a6d8614b608840169b06296c110802d360c529822100536c30a4b044200b4d8314960884018bee6a9ac110807171cd53582211cd36412a6b04423f8ee8714960884018daea292c110802b360c52582211fd75400a4b044239c6e8714960884738db0e292c1108e793a0c525822100536c18a4b044239e4d83149608840149b06292c1108e79aa0052582211cf34c00a4b04423f8ee878c960884734d90b192c1108029b215325822100726a9a64b04423f8ee87c85608847f5d50190ac11080a1fe1975182210043ec3cca3044200c5e7399460884010ff0eb28c110803179cd65182210062f32ae63044200c5d655cc60884012db0e290c110802d360c52182215e6a7398a43044200d4d7314860884011f70eb00c1108028fa1263d95210051ec24c7b2a421e87d8718f65484018bae631eca908021fe1173d95210062eb98e7b2a420087e8790f65484010fb0f21eca908021fa1c43d95210043ec3887b
  | 19 => 0x21fe1572d81310143e42ae5b026200a3d8414b604c4014bb06296c09881f1b1c852d81311e64fb1ae830262008fb87580604c4014bb07aa2c79081e3721d5358f210143f42ee0b1e420087d85dc163c84034b907bb2a79080297e0d7654f213562f31ee8a9e4202a5e8758d53c84054b90eb1aa79080317dd16354f2103e2f392c6a9e4207c5c7258d53c846bc9842b1aa7908d793c816354f210143f42eeca1e420087d85dd943c84cf8bcc6baa879081e5b2097550f2103c6e43ac6a1e4200c5d7558d43c842f53908b1a87908721fa1e63596210051f424c6b2c4200a3d8498d65884018bee731acb108031bdcb73596210043ec26e6b2c4200a3e849cd658840147b0939acb1080317dce73596213e537414e6b2c4200a6d829cd65884014df04b9acb109f29b209735962100637b92e6b2c420087e8790d65884010fb0f21acb1080317dce43596210043f43886b2c420087d8710d65884f94dd0421acb108029b60843596210e537c12e4b2c42bfa77815c965884010fd0f992cb108021f61f32596210e43f43e62b2c420087d87cc5658840147d0998acb108028f61331596213e53741662b2c420087e870c565884f90fb0e18acb108031b1cb70596213e537414e0b2c4200a6d829c165884014df04b82cb109f29b20970596210043f43e60b2c420087d87cc165884010fd0e182cb108021f61c30596210051f42060b2c4200a3d840c165884f94dd04182cb108029b60830596210053b40860b2c4200a75810c165884010fb0f32ec7108030f9d265d8e210043fc3acbb1c4200c3e74597638840187ccaba6c7108030f59574d8e21004b6c38a5b1c4200b2d8414b638857da5ce8296c7108034b5d052d8e21005a6c18a5b1c42bce4e6314b638842f17d09baec7108022f61375d8e210043ec3cebb1c420287f875d763884010ff08baec7108030f9d674d8e210061ebace9b1c42178bf875d3638840187ceaba6c7108030f5d574d8e210061f42ae9b1c4200c3d855d3638840187ea6ba6c7108030f54d74d8e210061f292e9b1c4200c3c525d363884050ff0faa6c7108021f61f54d8e210be1f3a6a9b1c4200c3d74d53638840196ae938ec7108025b61c5258e2100596c20a4b1c4200b4d8314963884014bb073aac71080297e0d7558e212e536412eab1c420287e85dd163884010fb0bba2c7108021f61f5458e210052ec1ea8b1c4200a9e84dcd63884050fd0bb82c7108021f6177058e210043ec26eca9c420287f83dd953884050fb07bb2a71080317ccb7654e2100637196eca9c4200c6d32dd953884010fb0f3b2a7108b28fa127654e210051ec24eca9c4200a5d839d953884014bf06bb2a7108021fe117654e210043fc1aeca9c4200c5f835d953884018df04bb2a71080317cc97654e210043f438eca9c420087d86dd1538
  | 20 => 0x36c14ecaa46200a3f845d9548c42f47f0cb22a91880a8fa1d64552310151e43ac8aa462c0c3f73591548c58187ae6b22a9188028fe0964552310061e392c8aa4622cc5f765d5438c4d563f08baa87188b3879917550e31005a6412eaa1c6217a9f86591438c4fd1bb0db8a8718803555d77150e310143f43eeab14620087d84dd5628c40147b083aac5188029760c7558a310043f43ea8b14620287c87d51628c4010fd0eaa2c5188021f21d5458a310be1f3a2a8b14625da6c82551628c42f93ce8a1ac5188023be1d6218a3132d2fc32872946200d1d7450e528c4cbc3cc8a1ca51880a1fa167690a310043ec2ced214620087f855da428c4050f90abb4851881e3b2097690a310061fbaac9214620087f855d9428c4050f90abb285189764f21d5450a310061fbb2a8a146200c3d76551428c40193eeca1a85188063d6187150a31006caa18e2a146217a9f8650e418c40393aeca1c8318802e5e0543906310143f43eeab04620087d84dd5608c40f0fd05baac1188021fa1f54582310143e43ea8b04620087e87551608c4010f90eaa2c11885f279d143582310143f42ee4b04620087d85dc9608c4010fd0f292c11881e1f21e52582310043f438a4b04620787c87149608c40147b08292c1188029760c52582310047dc3ac0304620087f855cb644c4050f90ab96c8988028f61052d91310052ec18a5b22620087f855c3644c4050f90ab86c8988023be09755913103c76412eab2262008fb805d5644c4071f100baac89880a1fa1772591310043ec2ee4b226200a5d83149644c4018dee4292c89881f1b1c852591310051ec24ecaa26200a3f845d9544c4014df04bb2a8989a69b20976551310053dc02ecaa26268a78805d9544c40f8dcec296c498802cb61052d8931005a6c18a5b126200a5d839d7624c4050ff0ebaec4988021fe1175d893100637c12ebb12620287f87d53624c4010fb0faa6c4988029760f54d89310043fc3aa9b12620087d87553624c4b94d904aa6c4989729ba1752d893100636baea5b126200c6d7514b624c40155b08296c498802b360c52d893100536c38a5b12625cc6d8714b624c4b9c5d08296c4988029b61052d89312e716c20a5b126200a2d8414b624c4b94df06296c49897393a0c52d89315ed36c18a5b12625ce4d8314b624c40149b06296c4988031b14970d893100477c3ac43126200a6c85588624c4012bf06ba4a49880a1fa1676909310043ec2ced212620087f855da424c4050f90abb4849881e3b20976909312e6363aec5212620287e859d9424c4010fb0b3b284989724f21d545093134f16312a8a1262178ee87d89424c4018d8ebb12849885eaba13625093100716aa6c4a1262018f686dc5424c42f1bf0eb24629880637219708c5311e66c302e118a62008ef825d7604c40f1d904baec0988
  | 21 => 0x7654e424c98b69f08a9c8499316d3611539093242ea6ba2a721264019ce839c6424c801a9aa738c84990067320d7090932006a6a9ae121264b487e87d95424c8550f90fb2a84992438b10b6550932004af43aa6a12640095c8754d424c80f4b90ca9a849901ed320953509321af86212a6a126407a9c8650d424c803938eca1a8499002c7615435093203dc641286a12645ff0e5250d424c8bfe18a4a1a84990ab1b1db655093200716326caa126400d4f8754d424c80169d0ea9a8499002d321d5350932006a643aa6a126407b4e8654d424c80f6990ca9a8499007539d9535093200ea63b2a6a1264c5b4f8454d424c91be1d08a9a8499316d3611535093200786c22a6a126435d4f7454d424c86be1ee8a9a8499003c3d91535093246f86322a6a126407b8e8650d424c80f7190ca1a849905fa3219435093200ec73b286a126417e8c7650d424c803918eca1a8499312e3e15435093261f8742a86a1264c4b8d8550d424c801e1b0aa1a8499002c3615435093200787b2a86a1264c3f0c6550d424c9238dae432ec2992029721953d853200c76c16ebb0a6400a5d83d53614c8d58dae5aa6c29905f0f9d154d85320061eba2a9b0a6400c3e74d96614c80187ce832cc2990030fd9574985320061e32ae930a642795f8754e614c8bb4b90ca9cc299237479d153985320068eba2a730a641dd4d7254e614c80196ae9b0cc2990039554f61985320043f43ecab0a640087e87195614c9798dee432ac29909e5721d53585322e52e432a6b0a641fd4f7254d614c9074b90ca98c2990023de1d61185320072aa9ac230a6417c9c7450c614c801c5aa8a10c299003a350d42185320043fc2ae030a640287c855c0614c80117f08b80c29905e2f21170185323252e432a7b026417c9c7450f604c801c5aa8a16c099003a350d42d81320143f42ce3b02640087d859c7604c82f17d0938ec0990022f61271d81325b636b90cb302642795f8754e604c8ad4b90ca9cc09903f535c953981320072ca9ec1302640287e86dd5604c9210f90dbaac0990021fa1f65581320061e3a6cab02640087e87195604c801878e832ac0990030fd9774581320061e32ee8b02642795c8754d604c8a94b90ca9ac09900347dd1535813246e8e3a2a6b026411d4f7254d604c8018eecbb8ac0990031d1977158132006aaa9ee2b026400c77651c5604c8018e8ca38ac0990035554c715813248e36b90ca30264c2a5c8654c604c8011f70eb00c09901e3ba0b75d923100476c16ebb24620087f855cb648c4050f90ab96c9188029760c52d923103e37390a5b246200c6d7214b648c4010ff0ab86c91880a1f21570d923160d5b40ee8b2462028bc87551648c4050fd0bb92c9188021f61772592310051ec20a4b246200a5d83149648c40147b093b2a9189a69ba0a7655231005
  | 22 => 0x32ac89900a1fa1f755913200477c12eab22640087e871d5644c8018d8ebb92c8990021fa1a76551320051ec24ecaa2640087d849d9544c80187b093b2a89901e1fe0e765513203c3ec1cecaa26400c3f429d9544c80147f08bb2a8990029be0976551320043f430ecaa2640287f841d9544c8050fb083b2a89901e1fe0c76551320062f418ecaa2640787d831d9544c8018bb063b2a8990031790c76551320062ea18ecaa26400c3f421d9544c8018dc843b2a8990031b508765513200637990ecaa26400c6c321d9544c8d34b90cb9aa899322c7e11735513254e2e3b6e8a9a64c795e86dd1534c8cf2bb09ba2a69900353e0b7454d3203caf416e8a9a640795c82dd1534c801a9905ba2a6991ab17d8b7454d32356a7b16e8a9a6400a5f865d1534c86b4b90cba2a6990af171d97454d32005a7c12e8a9a6435b4c825d1534c91f2b90fb22a69923f171db6454d3262f0f326c8a9a642795c87591534c8bf8b8ecb22a699317871916454d32475a7c12c8a9a640795e87dc9534c8054bf0db92a6990d7171db7254d321ada743ee4a9a6401b4c86dc9534c86ba9cedb92a69931b531db7254d32005a6c26e4a9a6400d4f74dc9534c801a9ae9b92a699002d3a077254d32005a6c06e4a9a64a4b4e871c9534c86ba9d0e392a6990aad3a187254d321af27430e4a9a6407d4e761c9534c80fa98ec392a6990d7c3a107254d32005a6c20e4a9a6435f0d841c9534c80161b08392a69900353dd07254d32006a6ba0e4a9a6400b4e811c9534c80169b00392a69928b171db7154d321ada7416e2a9a6400b4d82dc5534c801a98e5b8aa6990d697a1a7154d320052ec34e2a9a6425c5c769c5534c86b69d0538aa699002d360a7154d320052fc32e2a9a6435a5c865c5534c8478b8ecb8aa699002d3e097154d321ada6412e2a9a6400d4c725c5534c93f8b8ec38aa699273171db7054d321ad2f434e0a9a6400a5d869c1534c8338b8ed382a6990d6d3a0a7054d32005a6c14e0a9a6400d4c729c1534c8014bf0cb82a6990d6972197054d320b62e3b2e0a9a6400b4f825c1534c86b69904b82a699263171d87054d321ada7410e0a9a6400b4d821c1534c801a98e4382a69917e972197550d321662e3b2eaa1a646ab1f845d5434c859c38c8baa869917ed32097550d320062fc32eaa1a640795c865d5434c8018b90cbaa869901e172197550d32354afc22eaa1a6400d1f845d5434c801a9f04baa869901e572097550d32006a6412eaa1a6467c5f625d5434c8cfa9ec4baa869923747d097550d3203cafc3ecaa1a6490c5c76d95434c801c38c9b2a869905ea7a1b6450d32006a6baee4a1a6400d4d751c9434c801a9f0ea9c849901ed3a1d539093203da643aa72126435d4c8754e424c80f69d0ca9c849901ed32195390932456a73b2a72126435e4e
  | 23 => 0x58e520043ec3880b1ca400c3f7410163948554bd06202c7290029760c4058e5203d3741080b1ca400a6d8210163948014ed02202c7290029d6044058e520052fc1aeca1ca400e1c435d943948018bf06bb2872901e1fa097650e5203c3e412eca1ca407c5f8758d439480f8b90eb1a872900387e116350e520070e422c6a1ca48fc5f7458d4394855c3ee8b1a872901f179c96350e5203e2e392c6a1ca45fe1f4258d43948bfc3a84b1a8729003871056350e520070fa02c6a1ca40787e86dc543948010fb0db8a872901e5ba0b7150e52004b6c16e2a1ca40787e861c543948010fb0c38a872901e1fa1b7050e520043ec36e0a1ca40287e87dd5648c80f0fd05baac91901e1f20b755923265e2f996eab2464cbc5d32dd5648c9970fd0e3aac91901e2f21d54592320bd1e426ecaa46400a3f845d9548c80f87f0eb22a91900a8fa1d64552320151e43ac8aa46407c3c87591548c80f0790eb22a91932b0fdcd64552326561eb9ac8aa46407c3e72591548c80f878e4b22a9191a787cc9645523234f0e992c8aa46469e2c21591548c8d3c5e40b22a91900a1fe1d759863203d36412eb30c640087f845d6618c8018df04bacc31901e1fa09759863203c3e412eb30c647cc6c825d6618c8050ff0faa4c3190021f61f54986320043fc3aa930c640087d87552618c8050fd0fbaac3191d31b1cb75586320043ec26eab0c640787e82dd5618c80f0f905baac31901e3b209755863257e36390eab0c640087e87d51618c8050f90faa2c31924b1b1cb54586320043f43aa8b0c640087c87551618c8d38d8e4aa2c31900a1fa1f755823203d37416eab04640087d84dd5608c80f0fd05baac11915f1ba0b755823200636c16eab04640787c82dd5608c8010fd0faa2c11900a1f21f54582320043f43aa8b04640087c87551608c9272bf06ba6ca990029da0664d95320053ac0cc9b2a642787d87193654c80187ae8326ca9924e1fe0d74d95322fc3ec1ae9b2a6400c3d741d3654c8554bd063a6ca992429760c74d953248537410e9b2a642aa6d821d3654c8550fd0fa16ca990021f61f42d953248537416e3b2a642aa6d82dc7654c8018eae238eca990021fa1f41d95320043ec3e83b2a642aa5e83d07654c8014bb07a0eca992429ba0b41d953200536c1683b2a640087e87107654c8010fb0e20eca992429ba0870d953215536c10e1b2a640087e87d03654c8010fb0fa06ca990021fa1c40d95320043ec3881b2a642aa5e83103654c8014bb06206ca992429ba0840d953200536c1081b2a6400a7681103654c8014eb02206ca990028f61375d91320051ec20ebb22648fa5d831d7644c8050fd0b38ec8990021f61671d91320043fc2ae3b22640287c855c7644c8010ff0ab86c89900a1f21570d91320043f43ecab22640087e87195644c9938dee4
  | 24 => 0xa8600c5d739d76150c050ff0ebaec2a1803175cd75d85434b43fc1aebb0a862c87d835d76150c0f0f904baec2a18031b9d672d854300636bace5b0a8600ccd739cb6150c010ff0ab96c2a180a1f21572d8543006373aae5b0a8600c6d755cb6150c0199ae6b96c2a18031be1572d85430063642ae5b0a8600c6f535cb6150c018daa6b96c2a181e1fe1c52d85430043ec38a5b0a8600a5d8314b6150d698bae6296c2a181f1b9c852d854300636b90a5b0a8600a6c825966150da34bb0732ac2a1b438710d655854300536412cab0a869695f835d46150c01a3886ba8c2a197e5b20975185430043ec3cca30a860087f875946150c014d904b28c2a18023de1d611854360f4a21ac230a860087d879d46150c011df04ba8c2a181e3b20975185430143fc3aea30a8600a6c825d46150d2d0ff06ba8c2a18b21f60d751854300637c12ea30a860787c825d46150c018d904ba8c2a181e1b20975185430043fc2ae430a860287c855c86150c0f0ff0e290c2a18021f61c52185430052ec18a430a8607c6c721486150d2d2bf06baec0a18034710d75d81432fcb6412ebb028600a6c825976050c010fb0f3aec0a18023be0975d814303c76412ebb02860287f875d76050c014d904baec0a1a5a1fe0d75d81431643ec1aebb028600c6f825d76050c0f0f904baec0a18031b20975d814303c36412ebb02860087f855cb6050c050f90ab96c0a181e1fe1c52d81430043ec38a5b028600a5d8314b6050c0f8d8e4296c0a1b3e9760e65981436770e21acb3028600a6c825966050c014d904b2ac0a180a1fe19751814333c3ec32ea3028600d1c435d46050c010fb0f328c0a1b369760e65181434b62eb9cca302860087f875946050d99c3886b28c0a18029b20965181430063732ce43028600c6d659c86050c01b1887390c0a18031b995721814300636b2ae43028600d8c435c86050c018eccb388c0a18031d5967118143006ca21ce23028600c76655c46050c018eacab88c0a18036510d71181430047dc3ac03028600c3f43dd1639480f0fd05ba2c72901e1f20b7458e5247e1fa16e8b1ca400c3f749d163948bf4bb073a2c72924e97e0d7458e520061eba0e8b1ca407a6e821d163948554db043a2c72901e9ba0b7158e5215536c16e2b1ca400a3e849c5639480147b0938ac7291729760e7158e522ed2fc1ae2b1ca400c75711c563948010fd0fa0ac7290021f61f4158e520061fba682b1ca42aa5e83d0563948014bb07a0ac72901e9ba0b4158e5200536c1682b1ca40087e8710563948010fb0e20ac7290aa97a0c4158e520052ec1882b1ca454a5d839c1639480147f08b82c7290028f2117058e522b52fc1ae0b1ca407a6e821c163948554db04382c7290021fa1f4058e520043ec3e80b1ca42aa5e83d0163948014bb07a02c7290021fa1c40
  | 25 => 0xd4f2bf06ba0c0a98b21f61f64181531661f3a6c8302a600c3d74d906054c014d904b20c0a98028f610621815303e37390c4302a600c6d721886054c4b2bf06b88c0a98025be0971181531acb6412e2302a60087d879846054c012f70eb00c0a9b66d6e0d601815333d8f426e6b2a8600d1f74dcd6550c018deedb92caa180353dcf72595430078621ee4b2a8600c6f761c96550c01a9ee6392caa1803c310c725954303e37c30e4b2a865fc6d861c96550cbfa9d06392caa197f5360c725954349e37b18e4b2a8600d2e431c96550c01a9886392caa18034310c7259543006a6188e4b2a8600d4f301c96550ccf8bd0fb9acaa1b6317dd373595430070fba6e6b2a8600a5d82dcd6550db1c3e85b9acaa181e1fa1f725954303c3743ee4b2a8600e4f83dc96550c01c9907b92caa18031bdcf725954300727b9ee4b2a8600a5d839c96550c014dd05392caa180297e0d725954303e37390e4b2a8600c6d721c96550c014dd0e392caa18031ba1c725954300727418e4b2a8600e4d831c96550c018dee6392caa180393dcc725954300636396e2b2a8600a5d839c56550c014dd0538acaa18029b60a715954300636394e2b2a8600a5f835c56550c014df04b8acaa18029b209715954300636392e2b2a8600a7b805c56550c014f100b8acaa18031b1c8715954300636396e0b2a8600a5d839c16550c014dd05382caa18029b60a705954300636394e0b2a8600a5f835c16550c014df04b82caa18029b209705954300636392e0b2a8600a77815c16550c014e902b82caa18031b1c870595434b4afc1aebb128600d1c435d76250dad4bb0732ec4a1b5f8710d65d89432fd36412cbb128600a6d8614b6250c0f8dcec296c4a1802d360c52d894364f86218a5b12860087d879d76250dad4bb073aec4a180a1fe1d75d89434b43fc1aebb12862c87d835d76250c018df04baec4a197e9ba1752d894300636baea5b128600c6d7514b6250c0159b06296c4a18029b61c52d89432fe36c38a5b12865fa6f8314b6250cbfc9d06296c4a1b569b60c52d89432ff26c18a5b128600a4d8314b6250c018d8a538ec4a18031b14970d894303d37414cb3128607a6c825966250cbf8d8ebb14c4a18034710f755894362d2ec1ccab12865fa6e829956250cbf0f90eb2ac4a1b538710d65589432fd36412cab128600d1c435d46250cbf2d904ba8c4a18021f61e65189434b62eb9cca3128607a6c829946250c010ff0eb28c4a181e9b209651894300477c3ac43128600a6c855886250c01a3886baec2a1b4e9760e65d85434b62eb9ccbb0a86d2e1c435976150c014d904b2ec2a18031b99672d854300636b2ce5b0a8600d8c439cb6150c018dccab96c2a18031b59572d8543006c621ae5b0a86178dd83dd76150c0f1dd05baec2a18023b60b75d85430043ec3cebb0
  | 26 => 0x69b2096458953726a7b9ec4b12a63596c825d06254c6ba5884ba0c4a98030fa1974189533061fb1ae8312a600d1f635d06254c6ba5904ba0c4a98d70fd89741895303e1f312e8312a635c3d625d06254c0f878c4ba0c4a98d747cc974189531ae97192e8312a635d1d325d06254c01a5a64ba0c4a98d74b08574189531ae97902e8312a62c87d87d906254c5987ce9b20c4a98030f5d3641895303d37416c8312a600a6d82d906254c010fb0f320c4a98030f5d2641895353e2eb9cc8312a607a6c829906254c5987ce8b20c4a98029be09641895303d36412c8312a600c3d741906254dc78bae6320c4a981e9ba086418953004b7c3ac4312a607a6f865886254dc569f06b10c4a98029b61b421895300696ba684312a600e2e64d086254c01c5ac9a10c4a9a9e57e0d74d85531643ec3ec9b0aa62cc3e74d936154c0187ae9b26c2a98029b20964d85530051ec20c5b0aa607c6e7218b6154c018dae4316c2a98029da0462d85531661f3a2c930aa600a6c825926154c0f8dce5314c2a98031b5ca62985530053ac0cc530aa600a3d8418a6154c0f8d8e4314c2a9b87555cf61985537062fb9ec8b0aa684c5f735916154c014d904b22c2a980353dcf725855300637b26e4b0aa600c6d64dc96154c01a9f07b92c2a98035320f725855300637b1ee4b0aa600d4f63dc96154c01a9ee6392c2a981f1be18725855300637b20e4b0aa600c6d641c96154c6ba9d06392c2a98d75360c725855330637b18e4b0aa600d4f631c96154c0f8d8e5312c2a98028f610625855300637b90c4b0aa607c6c721896154dbfaaee7b0ac2a98031b1ca61585531643ec3ec830aa62cc3e74d906154c0187ae9b20c2a98029b20964185530051ec20c430aa607c6e721886154dbd6ab07308c2a98021fe1d611855300536412c230aa600977875846154dbb6af06b08c2a986657e0d70185531a43ec3ec9b02a62cc3e74d936054c0187ae9b26c0a98029b20964d81531a43ec38c5b02a600a3d8418b6054c0f8dce4316c0a988e5760e71d81531a43ec3ec3b02a600c7671d876054c014d904b0ec0a9b73175cf64981533362eb9ac9302a600a6c825926054c0f8df0d394c0a98031bd92729815300636b24e5302a635d4e839ca6054c6ba9b07394c0a98db1bd8e7298153006a7b1ce5302a634c6f609ca6054c698dac1394c0a98031bd91729815300636b22e5302a600d4e835ca6054c01a9b06b94c0a98db1bd8d7298153006a7b1ae5302a607c6e7298a6054c0147b08314c0a981f1b9c8629815300636b90c5302a600c6e729866054c018dce430cc0a9b6f565cf60981531a43e43ac8b02a62cc3c745916054c014d904b22c0a98031bdca625815303e36394c4b02a600a3d841896054c0f8dce4312c0a98021fa1f615815300536412c2b02a6dad5b73d816054
  | 27 => 0x12000004800800800000c00640020000000000002016002000002401f014007c004005005000001200c00c001c01002000280100ae01700f0050000023003000000000300500280020030110070000002008800000e006005002401202b00180080240030008014024003000004802a003004801800200e00900140160010018074014000002800400800200200640000030000000000001002001c02200e00e800c00600100f80140040000038128084000005000000000b00f8004006001007800c000000002800000c003007800c03c003000801800202e0048020038002001001000002e003000000000e0010004076040000004c00201c0018040014000000800800e01d0000014000000000801000000600000000000170000064010009000000000601a0058000000007000002c01800600000300040010108024000003009804c000003001002000004000500000240310028010000000000004008800a000017803a004001800002200700180100000010010018004000000000000c002000801c01000000100000800030010084028001002800c0000000010014004006000003400800d002006800c005007800004400b004002400000c0020004006000002800000600d000805c0020010000000004001000000000200000000000000060010004002003007800800a006002004000000800080640040060018000002001000800406201e003000000200312cafc1ae3b22a60195c835c76454c012df04b8ec8a98d65b20971d91533552f41ce5b22a6e5a5d839cb6454c0f0ff0eb96c8a99aa97a0c72d915354d2ec18e5b22a607c6e721cb6454c018dae4396c8a9b8297e0d71d91533552e41ae3b22a600a6f825c76454c014d904b8ec8a99aa97a0c71d915354d2ec18e3b22a66aa5e83dc36454d534bb07b86c8a99aa97a0e70d91536e52ec1ce1b22a600a6e829c36454c014db05386c8a98b30fddb64591537368fba6e6b22a600d4f73dc96454c018db0db92c8a980353e0f7259153006a641ee4b22a600c6f63dc96454c01a9ec7b92c8a980353dcc725915303e37c30e4b22a635c6d861c96454c6ba5d08392c8a98031b990725915300636320e4b22a635d4e831c96454c6ba9b06392c8a99831bd8c7259153006a7b18e4b22a6a795f835d36254c6b0fb0fb26c4a98b30f9d364d89530061eba6c9b12a635a6c825936254c014db0da16c4a981f1b9db42d895300716b2685b12a600a6d8610b6254c0f8dcec216c4a9802d360c42d895311caec1ce3b12a62595f835c76254c332bf06b86c4a9b97175cf64989530061eba4c9312a607a6e829926254c014db05324c4a98b30f9d1649895345e2eb9ac9312a607a6c825926254d8da9ae7b14c4a981f1b18a719895303e36312e1312a60087e87d916254c6b0f90eb22c4a98d
  | 28 => 0x100080100010008004010009000000801c0020010020008003008004400000100100000060000060008000001007001401402800380c0028040006806000a00000080b400007f0000020008001000000800201b0098028004020000001003a0270038060002004001008807000301500fc00000c0010010012007009004800c0080010028038008002001402e02100180140180060038034002003004005803e0060048004028000002000400a001007807800000200a00fc0000020098008000000000002800c0410040004000002000000c0200160130000006012000002c00400b0000084042000002806801c002000004c00c002001805c00000600000500020030038000002001000800c000001000800000402300000180020100080008018005000000800801a0108000010000007001800800700c00500000000028088022001006801800600e0018014000011001000000600f0000018006011008807c01400200200bc0000140000008000000006803c0000000000008000004001020000200302480180580000048000004027000000c04200a006800000a04b00500c4008000000000402200400b000000a0080118034002000000000c0080010000000000010000801c00200600680840000100000008008014001002c0000000018004006001001810009e00601b001000000202c804c00200100000000020000020140000047009000400000000000000320170038000002001003001800200600800a0002005013012400c01f000004c00801f011800801400000000480d0008001003800003b009800402400e0000060030000006000001a007000801c00001900300000040010008000002009002000400000400b8000002030006004800800d004800001200300000080480000018088010005000000800000d000000800600000c801c00000200080540000090018048000000000000c002000001002405e00b01b004000600f000000000200300000180080130058010000013003000c01c00300000440020070028004000006000005806c00000a804400601000180180280040088064076002005000401800700900180080030058040036009000802c00200001f8018008001000000800c00a0000110004009001002c00c0080018014050000000000c0e400b001800c00000000d0000028000000018002e00f001002803e0000020004016000000000001200300180200ac003003000000a005000000001c001001000000000000180b400601d0008004040002000800800a000002802001400b00080080020000008000012016000802000000b016000000c013000000000c00400a000c00a00f00080140b8006004004003604d000001c022002029000001a0050028008002001000802400e003000000002a00100080300
  | 29 => 0x13d1368c85a835146db0006178000d4600000000011446b54dab4780005ef30b8000e0297008000000004c116129080005caa65000075d96415193b4000d7e4c826ac00000000002c05b293d0002d0000000006811a5cc2e5b3f49c24000d1a0000001d7c2576e6141c1922dd50980000c6e233de8569b3e00000033bd9fc08f5d72564000e1e3e0129d1327dd00019887171920e18001afb63f0000e393005d821ac0019d80005d020d2e3e0004f140000002f10000a9000000000032b0fd4adf0b980000005dee5c8626000000000000053f83a40230181a65555acb1f075f5574920001796dab95b88cc62cbfe6d29aac202a9709c370c43a00f00180000040028000002004000000400e0010000000010000000001400c01a0000024012002001004407400000100080000220068070008002001800800400200000100a00030040008014002001004000600100780240000010000028032001000000000001e004000000e049005002800000101a000c048001005803000200e00300580020000010034016005001800000c005007000c01204701881d812c009000001c054007002803000200200a801c00e0000010044048031001806004c000001800000000200900040020070030000000008000806c00a04200980040840010060044016038004000000000300000040080060030000000001001800004400f00300200000000000014000005000801000c01000200240040000000000010007000001c00602b0068038142003005000800800000a001002e0000000008008000009800000e0000000014060026003000003602800180a0010002001007c000000004802c010000000006c02009d0080000038008000001400000800780000020000030004004002000803c00601b008803000000a00700b0008028004801801800700d000c014000005800000a015005001c006000005800802a0020048018036000006002800600d001000c00e000004001800a0000000004032000000000800000f001003801e0000000000000000002800400a002001800800000c005002000000f0088000004001006000401000000100140000010038000006001002800c00001a002003801a00b0020064006002022801801e0000080010000000003004000c01800300f4006000001804000000e00000080060140020010000001012805400000b002806401e0a7008800c00c012000000000e00d0018000000001009806400200300d000404803200001b00020160048000010001017800001200900b000000a040000000400000100b0008000003000001c01e01e01b005800600400280080060040000010016001007001000001000000000120010020008000000004800c02001900d0004012001001000800000b000800001e000002803c0040000
  | 30 => 0x24c473867560a84c4829f1535e00000027e0000e7549980006fe01615312b5d249fe353177916800010e000000042c1e188b534018908dd3f09aa7d21441b8888c5a2408bb84ce62bc6141645732d594ac058801c28c426ad5019617f6c7224dab8e9a376a7253605e831d0f801420c21c7b8e9cec7170f40b8522a309bb013b0676d720001c943a800030500000005d617f8001c2869347828bccd760161f204c0000005b48001ab030c8868b4bd6e0b68b7a61bcd4ba961e32d54a89a52d90bf7c362a7695b7fcef0a0b3a32a756263ded9022193a4b920bc9364c1e573504b1e81ca9c822a2fdf65486f45cabd544e05b506accca28d8d45aa8000b00cd39621880002674e3090c000be2db300006ca1ceb41a7a4bc42851a60ac483f1a76c82ded9287124108d5092e3f032c08780003c82bc8e95dcee826383119c0e6dd4bd9d5c54a7316dfc2d0000e0a0f48dde000e1c19a1f28eda13f42b9980f022f62fb23e067460d3d10e886bcb9832195846230000000001306650000333c5abad222381980000000002cdd858000000136dd3a24f8000dd09302a08003718423b550001e5000000000000005b6975e020f644561130b1ad440e02a271e2f4ecbecfd6530f395183a78000a34fa036f000383c6cc2f9a0a035600000018518a6000d691fd3759da221f2fd54ec5ce1373f40b054de8b309b0f6a37fcc90cb2ff077c0d15d8b055a183888003a191ec1682c8f51acca9cc4f1b1dd52683963fb3786c13333dca442be49f08000bb098edca70f90e8c880002a7447514814a506017c46cde36c005243dcaaa226b3ee3e80001284d90f5ae102bdb2a50ba44a18da51823e2e509828cc0d02eb9ba86ab668d044ae311c8b4c411a5a36cadc4f46f537edaec3b4316881481208d23faf3c7f8388600ae7041d3793b0abe54989062570001ce4e7a21068b5c48a601573790304cd82b1474542d3e3353a7e85ccaf256ca955be01e76b9b7ad710651e99094192036baf992e4a4851c1cd3543dac62bdf3f8b0d4886345f000190032b06c3491c90b3e68731ec94600048bb6e6cc200057a32c1739b90358564c0004bb50ba654cc60000000001b7ebbc30c8350b4197d46eba65da01f533d8e10fcee7e2b4a0c19d06699f31ee8a4043b5eaf1d8c4c7e240580018de7340001bc40ca1f95132d7c00042724600016d840e6288000000000328bb75d22a1642fa6e5336564182f629c9ed4f00018ee8989ce000000123c0d20000b341e2ade51ab7fb3dc11b303a58d90a70800007256783a300000002080005e26b0800013100027819a807f00022a40002f58d400000000006bf9730000d9375c09116dabe3000055c0000006fcd0b8b505815630000f3ccfa6849e9d5c028725431015fc4d700000002a47a3491066000040c4722f300000006590
  | 31 => 0xbb907292af00d2ee4e44632202187fd3141a14e1893f7612a2d9b286766009e8649ab63aa384cfac4eea9f0a751dcb002a4803464aa4108cd52e8860c34a6b1701ecdb00fb988868486554c283959439e0461fb13b27021149700932b634778ef25be9be2cd94cc09454b6399a7c00d9014db92d56ecdb368c2a9d1c0234214f7f03d39041d73161d02a1a6a918c29d2e78671a6a99122861a7ba51d5891101eaf8022087e70e9e0882ad7c1131fbd718527275a5662420473a3a1219ce2b950dad2041e6812cef6d683d27564c9f85caa9b605da2d856ac4d45e13209f21834a19ea86c4abc002982558a6d542e000160ed65dec1c9d3e35410000ef124000042c204800000063a1f0d33a0002dd00005c6a304fd93085a85b03df06318cee5c5788b3eea22911df89505a742025fab84dce1ca6ec85c861c8825ad92e0b3a74d3f2b6d491e76749e0056a181f3391362c08a49537d350d1c4000524aaad8da3a1b6fac9c05841603da9197a01e5c9d38b4a84da96a827b00dc4026feb3c4b0878504b828da769fcd14b3688377a94afb2fc4b80000003633b4c00000005b5430841000000000000066829e80868886588e807ae46e0e712747dd0006b296e080c00000037c20000000000ef48540003349048ab600037e08800001e50002fa40006530000f309f43df3fc348c7a044236f07019d645322416f5bb4424529144977ca2b0e58e85382d4765388dd3127322da8e254dadc83528a8486639800020b8c1cd2a62d179969c5b40000fa11281cc6692de1508e3e71397c063eb1b66f827d98852152d9f8c6eb0df2ee37129c9b2f7578b580000fc414aead7ca000452b008d249f22602fffd18abf0000000bfa6b239300014ac2be228a44c0006204051990000d5b80007d701000054700007b70002ac01340002e8285085afdc0005feb7800000233da20d0cf23ef3b618855f40000003b6d3665a437a8ad94615832f1957d9088bb087380900e9c351601e80ec00040e80011e69875e28001404df16ef8001d9290a0002828c6e36d637d4dc9fa07872c14ac71400000000000000005b40a40f8861b40499e065056b4f0f46c7b838646782d86063b61179f1942ad0648e07be36683b4062ddcaf04c6198b8060000005ea8cb250088471fa81113464f3ff01acaba0003cd34940168791c5991f8a00410000001aa82c309688b0c7ae566dc37b2d8688a0bf29682ec5b11b64031914bc8e47313000039021a0ec61f4224145ab8d4a275300017813a1000422009c000000190afd60001f2195124506e0000001718f64b9b63180009e40322e1392c0000001841adcd427e6737ace860aebb4f1c7bd8dccbd2c322e0000bc929794113bc67f212b13929415b0cf1ed42220b717d0d20e3490b4762aa0194c07566832f4e064b6bb9cbece0
  | 32 => 0xc9540c98b9c70ac925f0e0ac92ec075280000005c50001164000ddb2ff3566b1cb5a0002f0fbec00000022700004183a78c2a4f82b5800153589eec82bf989c25c8b76463470000b17000000189000060e8288dfabf34360932000000630000000002180021f04e7d204b11fb5b7d227201939870412c1f61d403080005bd20e1d2e3f64c50319d124fd99c861d84e73e7508bff83c30e8ae8000b92a9c082877d7120ba1592c485c851900005791aaada6d1ce6e470b0469f8a80d1ebb00000001a289c24538001064000156a79c0005112e6852d9240ad632d5a87bc4cd3ffae59c663b20002a95288d9b22093dcb99bcd23a39481b4dde1bb1299cce00064b90885b8bf9164dca0db23eaded89542b2638f721a02232d7eac7876977668b604a328000000463b58847bebd335872f39e8475de9b411a9416f0034f93b6641225a63015031394f20992497073699bcc126831293deea5e0df6e09a795a9ae702bb9a8f8682b331e70381403c06ffcbe06328e31648e00d8e643d1124d135ab94aba80745dc1b409eb12c15279f5f58ae08faa1d4e9df384acd4058e8fb86a6c4301c837820cb61e783b18000000430800000095b00016ece224e01251fcdd2ad7553588042522651535eb0d118181b719d916000000010dc6262525619840bcb203cf44aad2dcdf23bd1500f1814438f22551645aa6badb3177e0b7bf58499c545e8bd70df0dcc6875711ad8c084de162b034f149cfda58adb2d40191f5ac051f21c5f31306c23cb9529facd99d250317651c04244a46dd85391be368d4380c23fc29b53f9b4971600030e20f80000002358000a9e0000003448f1e0001c91ab8e36a786f69a69b0c57a2ea9874ba4928e9b1c8cd7c5f127d956842218f5929f1c6ae6b8499f044a8a88f233865c4826d8663b9cc0543c262b07143c0068a7b2e0d55245059413158c270a07c97c3c0be326d08d7728ab8241693a1364bd4c1b377a9389b84ffaf7c3143ad3b88000bd6ce15fb723400019047b8f860226ba00b8b2a0002ea551b61c83259654f2990553084587092d47e4100f6299400000000012247135b600033f047edef56a87d95cc5bc074afa9a840c5a58b6d8b0e3450000aa2d4000018e65fca54e0602e21680a89a74253464bf02cc17a0001a6e73b09d05e84b40f70001876c0600010d20196a6a7c6fa940062b3a61904b28eecee06b0987973c6d76f726718ea5467261e4152221796852196fabb71030d7f70a48405ce5d45aa81c000000045c95589000019e68cd73685d4d769673eb81c9b24ccd08489c85c40000000000e26e8f1e1c0005a2ebc49f07495100002e53705b8e77c3cda43cbb1e450002934d15e843cc1070000bca1fbbab9afa7cb40ba004bf6000000200d61e0001b805a572e86d32a000000000075c84c90047cf000
  | 33 => 0x61dd469259018f1ba558019500032bd3c80000002c29a00a53604328433400000324ed88491a48d9ef1186000387000000000000000000009feb2b26fcbe8e491bb5cfd0b20006d6b6c42a085b1add4d85aeb651e3b7b14ba35046636141480097658000ed4e2166589c448ca621ca0ded67abe9935360827c9a843a327c0008ab67cd48ccdea206c0b48400068274e2d9045438d4d2000c06c8511d4b6201d6ca06869e107e6edf74819b20004ba5849dcdbcf00004f288d7772fe4818dc8e1e00743ba8a10f62830b2232db9e40b000000047c24e1f4417a0004e14b0165c3b80000001f80c4a0001b0c00000000004ebad1a2ec6641425687c832f2af240083c10f7130b2ddbc6cd67d84cc0b211c1f4945c5329960078e1fb3a062d6daaec1985534a9af9000085300027bc3608fb014adb8000a2a6cf2d780001bc000182d14cd844f30acf3048900589570558ab871c89e49548da0000000fe80004c20001056ba50626e8c00080e69d30405f84d139204951e43da56413d5d3cc524942c311d6ca3710018860425303632e12da55261e90decb666a4c88e1cf9864a0e82941a983d300036818700463b8168c1c6dfbebd09d880e4352c0000101ecca2a8a7cc8629c52d0ac98ab56e33098f48fdfcd71182117c015ad8e38aa59a706a0710b3c0008240000f740000005410d38bee00000039280b733020d251cc6a256eb600003d4edc4fa8b1d67647c000082816632331e00016d70000001dac0286521ce000176643f530a10c0003db354000000082021a683d9060001c8831acfa57e6a0ac340a661470601cc0b409b1308b4054f61288e5a56bb281f03680e0409bdeede376013892d1348000f060c13229b154786f02789e94c540183a4101436ab5834e18b24286ca000378a8b8a756e5d664ed01db6551d283f65ec000049c0001b897009998e59df018b78530c6a2ae19b6c6088de1001ea1c76c01ee71521d3641b21eb7dd455481000109af655ce05ea926b9e9d4398084016304e000255027826c680800110647b0000001c4484e45d33b4c5894e3d314c8000a3258111901ac2bf2dac0013308725581e1c40e69513996fc9dcc783ae0d35ac80cf33f075cbca992000235d154bdd0db9e4db1da8351f00000bc5620002f1c0a4dd13db8dc348a00025497a9a0497c6d9318882e59a00017f1b6e0000dea0a9097be722f9a000000003729f3abce9ed2cc1970201c37364af8958ee4250f02c91b2c1476a94e0e2c6d662f07740009d4d533b8ceac103243800000098d6bda051ad43e3efa34d4112b578002dc2c620739df419d3f8e8518e92d981844dd08a55400077900000000000e100000017dc26d0000000000000605f5920001d958e2f8562d0007070000000e406662484000a583e0802800000018a91bc0008c257e0a7c00
  | 34 => 0x820006fee7114f600067c3b294bc6aff3a336d09603308d1e180aa0005a908841282edb042100328dc55b7b792e5aa3700e0001b5064b8c6bb5ca5cc366b014c01de0005d082cf7a4af3434a118036ca9e22832bc02ea4000000000071c00000009260005272fed1222c00302fb4000a966ea000084cb575c091885bc8b11ab0001c2a8e528100000000000000001d9c0001dd1530861ab175005201ea0000000001b800006ae80004edee560d31b1b830001c280000009d300025c4000ca53acb6649567432d70d2e8e699a31989d028400015517a400000048f9004000008de14001a70dd6e7b27c144a850338aa51b2500054083b01102bb2f8de0034253c00000019e8e2b1a0b97c00045b314a45a1e0dac4129bc95a06cf353c00117ed4652e1ec57a266632c8b732c21fd01211c8a862a3f3c990785c3a841fb47ca1c18e006d9387e2b676f40c35480b614649abc60e92f411302d63c2f20042a286e2c8f380358d3260220af94152622ce08b1dbc6331a6632b4f511256f4ba2205af28542caad3ca9cc3f3a5a358ca71223f911f97aee7f4340a398d41e23c48961abc69b02b1138e6a358612082178bc355fd1028302000040380cf101af3672f10f401070002a852ba98b3e89a453460004de09df5dc3e500007e8b5ee1648a31f4cf85a96b795c085aaa04eeb9b00001fc08b947c5979bd42912f1cdc96c3af8c2d656d036c35d987c23e08000001ae5d440000a3c000e5a32600015ae000277deec07e0dd34a05a80005a06dcb4a59ba6c14a02ae8000aa26aaa97cfb66f91448f44c3d32bab629c82148052a200004ee0000000734000d448000000a6282301d000000000000004d4d100005e10711210c9360c3a2ced200011f699d5a6510661329195c00030600011fc32903e0caa74ebf13e698d8eb6956dea138c2cab305ec8779abe0256d1b726847202763ab398929d50b037a42e24ac49e513d9c43272bb16e410ee17761b08d34c8354982ea929e1c821e1c75d0edc91a532701b80352ab09916102476e694a1976af733a128f770259190317d8e4bfec21300dcb294932d23f4986b4237438229ca0001aeafc90e219c000000000039aa29000009609faefae7c96e000000394000026e0b800007188af4562579b343f85571e3400000069c8000000000754136196804953ea72c9c8be82069fc5916a144540f583f000008580002cca210be03398400000000c51bae526b5f80011d0b378bbb7418c86aa042bac0a02bbadaee6d0eb4e093dfa793ba4a850002069b84948000374b662c961d2159447287066991dc00092344586b19ee77b4f12814f3ae3d4a8137c00051500024d4b10457610a7bbb151400002b9d3800005b52fc03104684d10f96739bef56580780086bc037ae768b09fd3010f3c4c549f67f80018d7a1f5d
  | 35 => 0x400bdcf2ccf512ea5449162c8aac9d04d52b141a916ac24604806aa3a8000d313599368842adc4a0b4b57ee0bc5a196b1aac33f3b180000000002481ed983865e000394dc0a02664090e594900050195c80002f38001474346139767925800064d000365d1c2460000000000000058d27add149122830f1900093259922486d00c05daaee5856b805a2918d6c01e65e5dc644122c83ec08e8a930002ff920d3b4317000088ccba9ac17f5f50000d5a709000094a0006a500000005e158300000c22621d51c6079601a00024a85da87600000010360004abae356200000000000000ee214d16cc6e3ce000010d9a5ccb603b80000f999f71b80001b220b0003b4995081012c4001232df181000ac6d2de20000001b679089ac80014e2245474b0a896675d2cdc39817e00039eb0144bc1d6481366130a21900000014eea080000de00001ad09db8680007913fcadcd9dc87f34b0d9678a96f57b37100009f9730213e66eaff000000040600057803a8000aef0002dfdbaa62f19b21cc80069d000000000042b49615161feb490002c89ab60000000001b7a0000002e50a520001e68001db2000000162978251e1f3d74c888cbe7288e0e0000000001d4895ee71000369c4d10000000001aa2b9a3d800000009652b03048000241f5181f46c2ed859c3acc1e648e2c5b2dc741be66d101c441a3122c91ce1ca8e666851ae4530bf41ea2509270bce53a167cada063bb12d05b6d4882c3e7851466156f98a4836cb47688a4395f0b7c102360d99c6d13dedbbc706c3927f39f526c612183591885226808eeec88ac1a9b088ff422a5be3fbb4983706c47622e99b7c21851c191c75846d07f0321c6a0695cea5a586028a0262a40224a3400000002a8a470002f18ee800039e108c0008e600000001b30911d89a643761141b16e453a020c32b6604620dfe0a7975c8603f0f1b11e03fe0000001499bcc1b213580007320002410000eca16e734a3fc00033d35a000112e0db5591bdd490a328000000c90a4bb612ba8000000037c0000001b96ee00009986eb0812c554e658d37c0000f9076401a00011e81be0001b0000000044c00000000000002d6b8a812f0001a40e0a2601960000000aec3807a587fec2229e9d6176800051e9ca800039f0002ba0450a765598000000d1522f10e0a74bda0459902f2e2f94ab0000248abe800207866a00000023c414a45576624a4e724f352bbab58ae0000000545bf52353193a98502ea2246ae196fc00e8f811a9a1e8d40b3a98d9564801920d547d7e414959bd98fc22528c02b01cee64021263959892e25098f6bdc97a003ef4cf2457d07902e1c52c796dd000010400058fb3901fab4412d8f9d69897358c16507c42b4040a1ad374e3059fb52c6c0d9ba45271cb1816c68838453760e467303e0e9c0004e684a0b
  | 36 => 0x35c8640000001bf2186000381000050b000000034439d69e64dcf70987d7e800000000039bb314c706ee00000007dac2d00005846bdc0a721b03c76b9254e888542305cb572bb358d9a1246892d00badb4d9709e00002322ce56b4000d6d5d21d1497ad6e54025e499236b3fd8c98bf40006bcc00104edeff5580007921a02ee8504384d2f37237740000000000d009a6e7c30d09c0000ab965e2f8fc9a03c30f8908eaa34431c80000003ed9be8cc940233c21b4ebc76a91600011c4fb2432017a3f00002f5000078c8080003f811b0000153660a48e810079648800115a0005351d82d58c5300000007190003bf26a557a0003d213893d087d3be9551c32939000038000024954d0000fa650851d00017eaea70000000aab00000000000000004e94db000044954900009a8b246961e2c4800003d5c7f395ad962f680540ea5a995e80001bd0006340001a1020e7472807188b397730e5502c6dc60b28c539491833921d513c8ed4a908f17fe036d5a12c06e6c445ae3a4c2b08d01ae249805a00036a13c1a9cc86000188d3ae63e00000000006670e3244143217d62da9647fc5a48000bac00036a0002b04000dee800379564600004c0001d00000581873c71d393602c20c0000000003a0da2600014a8298e61d8b80000006b68876d53b14d1c17876a33a82ac00000000000003b81b3552800075e16c2cdb71eeb53a0031e6a18c56728d9c336b4641ea348a684ea022121400072b64119e933c3970d203140a221626908887020002962b10b5500034306e6c84ba70000254d3c231390b64400000000031a4e8800060b97e4ace000222a998f911a5284994b80f0003c715d039b0b51578d1c10c6a20000b4800000038a800157cb958639f547e8c688df67a86301d831b40049fe885638a5dcfb40000001671b683d80b599a03d6e0d00038d186412b000000000041d6b30edcc766ff557804d6425a6196943472cd5311d97d54d000068280000000005689721b5ca391e50001cd6000000353e0008a13fb000000066d560c24842eae96fd0000ba268c6688a5187429c000233849a98f00000008f2c1f208825811c3b90dd45198ba0b90a635a16f2000509f2753b09665348000000866000332003ee88000119952abad3589f7800029338234595aca433b70b6860c42780001000002b48000000d8c89d6980001bf02fd30a4ae9bcd66c503931109e85a86bba6000070b2b40000322a890000000000000556067d7140ed381ab900000000000b4ccea4cf0dd29b9b03e682b191d9cc65130000000e920005d7af5b39dcd55253aa406e7a100000000000005e181f81140005d41fd40007420000000e982b000000015a83221a8ac6415c7292c492484a254700025ac928c8759602f9d62afb1d9aee84f652d73ba7c4c60bdc00027d19346404
  | 37 => 0x11a6bde422903c7820f439022b89a068930b362521827f60177cb2d0e7b1d580844fcec1315874c9341aa3420c056e432e09506a551a8d85172818aa00c46ba00404c649b4178ba5d743adb881f089acd481888f2b56a82c661b91c9de193585b129694bc855bb0648c280d1778c5ef5ede5c1e249cbb40003ce0001c10a991d87318cdc1476d5904ce7451b04d1b818d6a104abdbed66ada47179cbcd7aa7e28d29e53bbaad000348913e4282d3800153e17475b374c6c600fe5d1cb80000005278000d030005220cf94d85d00002434d600b0b52dc3576c000746b2cc1d04cb5ab19dd23adcb5a3c9bc88037a000181553668d5ae9eac6eed28683a5f87601ab1878000b2dd335ba00016e20005c700000000002ed893c0000000d8800000045d61da178b8ea8f24f2685db438d80006659301c100003ec6342a80ea8420612d711c568d80003c414114e53620000000ca61472fb6512fb000026be1491958620000002055c5099700000000007df000000000073600016dd68d9f637f10f85434ce00035e00760000000001d7e0001014001bce00043008f5b187dc00002cabc8d0b4b9143d23fd7aeabb36ee0c7726ca0001c4a0000000001cbc0000000000000bf63bb80007ea00000007900000002cf000000057169a062c00002800000009400500001f460004dc0003094000b110a180003dae2e00000000601bf3ddd5f0acc8a0000000000000000035c149600013e800000035f00005ed93683343721220003f943c00000000003cab370000390883f63d11c7c93fe27dc15414502b8000c68a1c619acb4a6a0a74bc27590f49dc0000001cae0004ca349c00000000014580000007059dfdb2aeaa576857159eb7044b3000d9600037600015db0002512b74ba88551f90df81dc6f4217b9196a9698124309800000042b0000000000000237000000012140004bedaf1847ac8c558c02d2ac5800014d6b58fedc622c42a4400170800018ec000dd40005522b6052e4f80001860b880005eb00005bb00000023d40006552cd5c50645213399a305ace3460f0a75af32d3bb1fc7c47aa88d594b3e430a8bd74faa189ce13429133583002f33f226b9744b9301721259e40124a58c5a0c86da048391121203e26e8000c004b20000c706703b3b70a8ec8f4aeb51e4554d90c7480036caf6628423aa5312ec00016300976d686a3fd0e76000624000266415e9884633525a3a21b2c2b974600bf82c101d077639b3452890d5a0001ad00007d4000055952a000d3c62ab6701326571a180016c400064f1897c30b4d14b2dd51f46061863b4c004b870003995273326e2cb67200000020fa7f6
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x141d949d463d891003e139d98314b6244001a0d84d8c52d8910004936606314b6244001a0d8418c52d89100040f6538754f624400f84e7160c52d891003e131c58314b624407384d7060c52d891000493259839d7624400124e989d763d89100058365275d8f624400124d989d463d8910005836527518f6244001a0e8460e75d891000683611839d7624403784e7160e75d89100e6131c5839d7624400122d94e1f53d89100048b6538754f624400106f9761543d891000623a1d4310f624400144d939d770d89100051364e755c3624400105e9814b73589100050765052dcd624400141d941d763189100058365052d8c624400141d941d46318910004936605218c624400160d9414863189100049364e859d8624400144d93a16761891000493a6075d8c624400160d941d76318910004936607518c624400160d941d4631891003c1b25d8550c624400188d8750c431891000513e4d87d8a524400103e981d7648c9100050765075d8e324400105e981d7634c91003c17a5e8654d324400505e989d9534c910004172607654d324400181c87d91534c9101cd1325d53d89324400124e9814b63885100058365052d8e214400124e9814b63085100058365052d8c214400124e9814b63c81100058365052d8f204400124e9814b63481100058365052d8d20440014669614871481100055164c521c52044001c4463148714811000487650825d5630400188d746087458c100048765387149630400184f2061c5258c10006134818714963040018571061c5258c100061544187149630400181d87a105258c1000607a1d84149630400181d876105258c1000683c81841496304001a0d206105258c1000685c41841496304001a15106105258c1003c1b24984dd9530400142c9261d6454c100040f66072591530400141d941c96354c1003c1b24985dd9430400148d9210f7650c1000523648435d9430400f06c9261d6550c100058364843595430400144c925d56350c1003c1b25d8550e620400188d8750c43988100040f6508754d620406584e7160c525881017e131c583149620400f84f7060c525881003e135c1831496204001a0e8460c755881000683611831d5620402984f7060c7558810086135c1831d5620400122d9421f53588100048b6508754d620400124c985cd53588100041b25d8550d620400188d8750c43588100051364c759c5620400144d931d471588100040f66075592320400141d941d5638c810004176607558d320400f05c97619534c810004172637654d320400505c985d9534c8100060721d6454d320405f44c9754d624c810004936605258e210400160d9414963884100051a658525c22104001549931497088410004936605258c210400160d94149630841000712149635c021040014599314b7644010
  | 1 => 0x40fa6052dd1634800141d9314b7458d200050d65052dc563480014559314b7158d2000519249531c56348001435941487158d200051564c521c5634800144d9314b7650d2000523648439d9434800109d9810c7650d2000523648431d9434800106d981487650d200051364c521d94348001c0c431487650d2003c1ba4b87d95434800121d9810f6550d200058364843d95434800f12c985d1548c92003c17a5e8654d324800160d9418f654c9200061318c87551324800124e96a19534c92032493a5c8654d324818524c97219534c920004936508654d324800124c98d91534c92000683e136454d324800124c98591534c92000d1325d6454d324800164491591534c92003c5325d8550d324800124c96615434c92000ca32616450d324800348c97591434c920005a12456450d32480c95489754f704c9201ce1a5c28614a61480739497060c52985205bc5325d83149614800190c7460c525852019652dc183149614800114f98dcc52585200064361373149614800184c825cd531852000691e45831486148001a449160c521852003e135c18314861480012659814b31185200058965052cc46148001a268414b31185200059164c52cc4614800126598148311852000589650520c461480016459314831185200050b65052dd9314800144d9314b764c5200050b650521d9314800144d93148764c52000519a5f65185214800f06c926177650c2003e0b1c98414963c400f84c7260c5258f100060b6137214963c400184d83dc85258f1003c1b249851d943c400f84e7660c52d8b100051965c529c762c40016459314a71d8b100051a65c525c362c40016499314970d8b1000493e6153d8932c40015499314970887100055164c521c520c400f06c926177650e100049326153589328408944c9754d624ca100048765282d97634400121c9661052d8d10006079d98414b634400181e87d9052d8d100048765282dd7634400188f7460a74d8d10004876508714b634400181e87a1052d8d1000607a1d8414b634400181d8761052d8d100050b65285dc9634400144d93a177258d100040f25d84149634400f82c726105258d100040fe6374149634400f05c9760c5258d1000607dd183149634400181c7460c5258d1003e131c983149634400182d84dc85258d100061360f72149634400105d97a0b6518d100048765282d94634400121c966105218d1000487e6364148634400181d87d905218d100060761c64148634400f06c926107654d100050ba4b87d91534400103e981cb6454d100050765072d8d534400148d9210e7650d1003c1b249851d9434400148d9210c7650d1000525a44431d943440014999010c7650d1003c1ba4b87d95434400160d9210f6550d100051324975d8d434400141d949d763d8910004176627518f6244
  | 2 => 0x840112d985d052d8e215ec93e598314b638840190e7460c52d8e21006435d18314b638840103d9814974d8e210050764c525d3638840109d9810f7650e210052364843dd9438840106d9814b7650e210051364c52dd94388401c0c4314b7650e2100523648435d9438840144d931487650e2100487a6043595438840160d9210d6550e2103c4b26174552328840160d9498d654ca210061398c87551328850724e97e19534ca214049325f8654d328840124d94e19534ca2100493a608654d328840124e98d91534ca2100d13a5f6454d328840124e98591534ca2100683e116454d328840f14c97615434ca2100493e598550d328840328e98d91434ca2100d23a5f6450d32885075449754c714ca2117e199c58614b608845f9467160c52d82210061320b7354d608857b14f9760c5218221006439d18314860884659467160c52182210045366173148608840190d845cc52182210141725d83d91534840160d9210f6550d2103c9324983d51630840f44c92dd16354c2103e13a1d63dc9530840f44c925d56350c210060b21d64551320840f14c97615434c821006836156450d320840144c9754d32580210050b650521c5628c00144d931487158a300048b26154589428c0ad42c975516250a3003e0b1c98414a618c00f84c7260c52986300050764c85dd1618c00181f7460f54586300050b65285dc9618c00144d93a1772586300051364f54dc9618c00103c97610525863003e0b1c984149618c00103f98dd0525863000607dd183149618c00181c7460c525863003e131c983149618c00182d84dc852586300061360f72149618c00142d9414b76886300051364c52dda218c00142d9414976886300051364c525da218c00f84c7260c52591300061360f72149644c00f06c9261471591300050764c72d91544c00184c762097550d3000683190825d5434c00503e989d9545093003e0b9c98414b614c00f84e7260c52d85300060b6117214b614c00184d835c852d853003c1b24987550614c0016259414b61085300059164c52d84214c0012659814861085300058965052184214c00164593148610853000718148615c0214c00f24c9260f5458f2003d1324b7458d53c800f84e8758f7254f2003d132497558d43c800182c87591544cb2003c5325d8550d32c8001a0d85591434cb2003c93261534ca61c800144f9754d329872001417a5f83591538800160d9210d6550e200051ae59755c2218800181d845cc63d952000607611731cf65481cf12c976105258d200068318d8414963480c992b706105258d200044be6374149634816f24c9660c5258d2000643dd183149634800190c7460c5258d200054965052dc563480015459314b7158d2000525650631c56348001525941487158d200055164c521c56348001c44631487158d2
  | 3 => 0x430051364c855cb6150c0142d94d4d72d85430041765d8314b6150d2381d7460c52d854303e139c98314b6150c0184d835c852d8543006135cc825966150c01a0c43209655854300447a60435d46150c0150d9210d751854374e43208435d46150c0f06c9261e651854303e131c9831486150c0111e9810d75d814300543648435d76050dd390c8210d75d814303e131c98314b6050c01a0c43209659814300613dcc825956050c0150d9210d75181430068310c825946050c0f06c98596721814300463660439c86050c0144d93995721814300463660435c86050c01c0d6510d721814300519249659c46050c015859210e71181430051564e655c46050c0146492595711814300705594435c46050c015859210d711814300564640435c46050c0103f985d07458e5200607dd183d05639480182f7460b4158e5200607dd183101639480182f746084058e520060ddd181101639480121e9810d7650e5200583648435d9439485560d922116350e5203c1b24987552618c80f06e92a1d545823200507652831d9544c80f81d83d08765513203e1360e421d9544c80f84d8350876551320070350d421d9544c80f84d83cc876551320050b650321d9544c80f84d830c87655132006131db825d1534c80190d84dd37254d321ad1325974dc9534c80190e976107254d3203e439d9841c9534c80f90c766107254d3200643613741c9534c80f44c965d07254d32006131d982dc5534c80150d941cb7154d32006131db825c5534c80f84c861c97154d3200543650725c5534c80184c7660a7054d3203e13a18729c1534c80150d941ca7054d32006131d9821c1534c80150d941c87054d3203c17a63865d5434c80184c86e097550d3203e13218825d5434c8bf44c965d77250d3203d13259751c9434c80114f9854e719093200453261535c2424c80f21c96615435093203cc32498550d424c86b50c9761153509322fd832598550d424c859a0c86615435093233f031d98550d424c801a0f96615435093203cc32598550d424c801a0c96615435093203cc3e636550d424c921a0c86d954350932157031db6550d424c8d584d7260f54d85320060760e74196614c8018578754d61185320060760c74195604c80f84e7260c52d92310061360d7214b648c40f06e92e1570d92310050764c72591548c40184f762097550e3100683990825d5438c40503c985d95450a3103c1ba4a87551608c40f84c7260c52591310061360f72149644c40f82e7661052d893103e139d98314b624c40142d9414970d89310051364c525c3624c40122f9855362509312e50b25d54d89424c40f82c7261052d813103e131c98314b604c40f06c926177650f21006076137398d658840181d84dce73596217444be5d8414b6388401a0e6361052d8e2141e499c58414b638
  | 4 => 0xaa370000e329e3e0e61042566ccaa0410756b41f8b22fd0ec000880001564091b0000007701527300051800000820ac84000075c658b10845e42d80015c7f4dd96f03e79c000f50001806207610e0002b9fe2107906c8003a70000020e130320f58003e05a4c044d2e51540000e1681e4000d30ca000188d80685cc1c19400029a00004a808240e92a40081c92097270830bfc001d800100a130e55b5059df2cc2bcc6c783f25b0638431731e8df04d85a4d8b89c53ba05c730ad1f66e45c9cf1fa844bf11f3847fc000000000005d800088154020041500000000000ac000b4000000000003010040140500c0200004044010200300c04034010140003c0703800004160140a0502c008100081102418000070002005022060390341c0040200407040020080205c0901412000120700900c070140002c00004090000b000150100a004000000105815008160002402805004000040004c000040e01400004000280400c0209003010050140b048020180910025004010000000c0411c10014061ac050000601005008000200c0000300c010040300405000060000000009014240380302c0f04c0000020064030140d008020380001811000040040c01402048040100400431010020080b0340002c0203e139d98310b6254c0f82e825d364189530060b5d182d906254c0142d97993421895303e0b9c98418b6154c0182d845c862d85530060b9d0825926154c0106f98593725855303e0b1c9841896154c0182d84dc862585530041b261645ca6054c0f82e7261062981530060b6117218a6054c0182c74209645815303e0b9c9841886054c0182d845c8621815333c4766374dcd6550c0130e9810f725954300543a5c43dc96550c0160e9610f7259543004c3660431c96550c0150e9710c725954300583a58431c96550c0114d9810c725954300513a58431c96550dd550f9810c725954374e43a60431c96550dd550d9810c725954300643660431c96550c0110d9810c725954300543a58431c96550c01c0e9610c725954374f03a18431c96550dd3c0d8610c725954300543a44431c96550c0150d9010c725954300513a58311c96550c0150c940c4725954300513a5b301c96550c0150c94cc0725954300683e1383dc96550c0144e9720f725954303d1324e871c96550c01a0d8460c72595430061360c729c56550c0186872e0171595430061a1c8805c56550c0184f831c97059543006191cb815c16550c0186472205705954300447a60435d76250c0150d9210d75d89430068310d8614b6250c0f84e7660c52d89430051364c529c76250c0144d9314970d89430054364843dd56250c0150d9210d751894374e43208435d46250c0150d9210d75d85430068310c825976150c0118d9810e72d854300463660435cb6150c01c0d6510d72d85
  | 5 => 0x9d9870000000000c14a00045919000684111b1000114000c1282234941c60000007f516000224b398d000000001533081a6001d833e6b0000000000f4b21320001524d9b41452900008e13a54af700020a2d8000001e25206903bb9b38a0013f0e28401f0832eb1b8d01d419c07000204000780c1d0e2c600285945218160f68003f0334000003d473a2a08533047812000042324e1814124424e01f5000000508e424406a7299501479800907238000630000222cc3a8dd305344000091de746ed8a01e4554811d61347a4e207c31004c3203600613c238db396000a59d0180000000cc000000b10673bc6f47b06f354265029c723a0088b9b508d000ab12c3c41b49f1762f660c5a82f3460000014730074c0007f1d01285515f000230604003b84b86a927268000b6d5e10016863c003a20000020d0000002b09aad400000000170000fd80019e3cc0008200025808cd6186000001000005d0eed1517a06cf611280e240d58000b84d40000000039c5ac631ee6e82811a2dc292ce9461f46c00e47e286058bc0003c2480128ea11e3b4e94953112280009f0cc09cc9958351528000060d248c000234062f86297d0000f0e900b10c1aa7c98cb92614d31a41a812c989fc2876e0891e49264a4288463440d43740021e62cd90003d07c49b8003ca3a5050d032e434538b02a06405d1681bc328cf0913cf164cc9a82f81b02995130d4041714e3381c2c90f42c27e8130082721481d0fe2140cc0794c184210db987b023f06b8ddbe81c07818c000556080a18000785305d8ee5680000003756cdbde30006d8898da2b80a42f42c00020e97c122600004f0041507645b96b2423fcb29260346a60017a0002b0758ca8db4b42f89c0007a633ddcb90175090002307340012f2a4384559f301a1ec029140cd12066da50982fe1c9863782fc9c5bf2786443405e35283c5493d40c7dccd81909c628a10e02e4288a48322744403583701363c2499a2fe6f23918e00004200103304184b80bc2ae808929892886b80c15d22251e9994d0c45d4ed0df050388bb8203940003a1f23de580d39f6000704181c1856000000c88d450642c7d22b6bce7094000658000000000a8830733
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x38e888dcf0c8bd04741228cca4ec842040447ce46414f4180000acc4d098a89d000008604800e000003c6895086c1c5c2c5890b4300034807004d4004cc0d8a000b07800505400fc0c10f800b88c24000000040010a38110220013c00180000030006123c13aa10ea7a6043dc96550c0180753330218e4b2a86e9c036999810c725954300601b314b086392caa180210da8250311c96550c01284d0128188e4b2a86008436a094cc0725954300501d4e21b0c296c4a180220da910c825976150c01406d3886412cbb0a8600a81a844320965d854300601b30b2886b96c2a180220da910c825956150c010865432421aea30a86008432a19210d75d814300441b5221904b2cc0a180220da910c825946050c01406d3886412ca3028600a8268043209651814300601b30b2886b90c0a1802c04a2594435c46050c01a02b2b2421ae23028600d045959010d711814303e01b06ca0643b2a89901f00c86650725c5534c80f80743328394e0a9a6407c0325c96615435093200441b5332104baa871880220da998d8414b6388401807cbcc6c20a5b1c4200c03e5a7460c52d8e2100481b52218a5bb2871080280da810c52dd94388401806cc086296eca1c4200a036926321d544ca210040994eca70ca9a651080280da420b7354d608840f40653b0ab228699042008836a4642097550d300048c352290c2b804298002c21a4148615c0214c001620d18a430ae010a6007a0329d85591434cb2000441b5231b08292c69000300c9718d8414963480018064b0e8c18a4b1a40009116a4631487158d2000580b48318a438ac6900034059418c521c56348001212d2124a98e2b1a40009036a4431487650d2000501b50218a43b2869000300d9810c521d94348001406d20c643aa8992400081329d94219534c92000501b48412e6a98c290002a06a4e45831486148001113d43282966230a40008896a68414b311852000640d08c98a5988c290002444a664c521c52044001222d48c6290e29022000d01650631487148110007082408830e292c608003a0120441841496304001224d48a4b1ae01082000b026905258d7008410
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x8c260a000420005005b1a999810c7259543004806b1a9c4361852d8943004404ba5959210d7118143005400b25959010d711814300400dba6604314b7650e21004405ba650631487158d2000400dba660431487650d20
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x6
  | 3 => 0x1
  | 4 => 0x4c
  | 5 => 0x4e
  | 6 => 0x138e
  | 7 => 0x3
  | 8 => 0x94c
  | 9 => 0x94e
  | 10 => 0x124c
  | 11 => 0x124e
  | 12 => 0x138c
  | 13 => 0x8c
  | 14 => 0x8e
  | 15 => 0x98c
  | 16 => 0x98e
  | 17 => 0x128c
  | 18 => 0x128e
  | 19 => 0x150c
  | 20 => 0x150e
  | 21 => 0x9cd
  | 22 => 0x9ce
  | 23 => 0x5
  | 24 => 0x12cd
  | 25 => 0x12ce
  | 26 => 0x20c
  | 27 => 0x20e
  | 28 => 0x140e
  | 29 => 0xb0c
  | 30 => 0xb0e
  | 31 => 0x140c
  | 32 => 0x154c
  | 33 => 0x154e
  | 34 => 0xb4d
  | 35 => 0xb4e
  | 36 => 0x144d
  | 37 => 0x144e
  | 38 => 0xccd
  | 39 => 0xcce
  | 40 => 0x15cd
  | 41 => 0x15ce
  | 42 => 0x164c
  | 43 => 0xe8e
  | 44 => 0xecd
  | 45 => 0x94056
  | 46 => 0x95396
  | 47 => 0x4b
  | 48 => 0x140056
  | 49 => 0x1649
  | 50 => 0x138b
  | 51 => 0x449
  | 52 => 0xec9
  | 53 => 0xecb
  | 54 => 0x1a49
  | 55 => 0x138956
  | 56 => 0x98956
  | 57 => 0x94b
  | 58 => 0x140956
  | 59 => 0xb4956
  | 60 => 0x1449
  | 61 => 0x144956
  | 62 => 0x209
  | 63 => 0x1409
  | 64 => 0x249
  | 65 => 0x94d
  | 66 => 0x14c9
  | 67 => 0x139256
  | 68 => 0x124b
  | 69 => 0x141256
  | 70 => 0x99396
  | 71 => 0x141396
  | 72 => 0xb5396
  | 73 => 0x145396
  | 74 => 0x140096
  | 75 => 0x9c996
  | 76 => 0xb0996
  | 77 => 0x98b16
  | 78 => 0x154996
  | 79 => 0xb4996
  | 80 => 0x144996
  | 81 => 0xcc996
  | 82 => 0x15c996
  | 83 => 0xe8996
  | 84 => 0x9cb
  | 85 => 0x98d
  | 86 => 0x12cb
  | 87 => 0x134b
  | 88 => 0x21296
  | 89 => 0x141296
  | 90 => 0xa4b
  | 91 => 0xb1516
  | 92 => 0xb4b
  | 93 => 0x144b
  | 94 => 0xcd516
  | 95 => 0xe8b
  | 96 => 0x1a4b
  | 97 => 0xa0c
  | 98 => 0x1409d6
  | 99 => 0xb49d6
  | 100 => 0x168b
  | 101 => 0x164d
  | 102 => 0xe89d6
  | 103 => 0x104c
  | 104 => 0x1049
  | 105 => 0x104b
  | 106 => 0x1a8c
  | 107 => 0x180c
  | 108 => 0x130c
  | 109 => 0x1412d6
  | 110 => 0x1452d6
  | 111 => 0x1a89
  | 112 => 0xb0216
  | 113 => 0xb1416
  | 114 => 0xcc216
  | 115 => 0x140b16
  | 116 => 0x14cb
  | 117 => 0x155416
  | 118 => 0xb5416
  | 119 => 0x145416
  | 120 => 0xcd416
  | 121 => 0x15d416
  | 122 => 0xe9416
  | 123 => 0x140d
  | 124 => 0xbcb
  | 125 => 0x144b56
  | 126 => 0xb8c
  | 127 => 0x28c
  | 128 => 0x16cb
  | 129 => 0x184c
  | 130 => 0x148c
  | 131 => 0x24b
  | 132 => 0xe9456
  | 133 => 0xd0c
  | 134 => 0xd0cd6
  | 135 => 0xd0e
  | 136 => 0x160c
  | 137 => 0x160cd6
  | 138 => 0x40c
  | 139 => 0xe8cd6
  | 140 => 0xcce96
  | 141 => 0xeccd5
  | 142 => 0x188c
  | 143 => 0x178b
  | 144 => 0x17cb
  | 145 => 0x44c
  | 146 => 0x1a8b
  | 147 => 0x18cb
  | 148 => 0x10c
  | 149 => 0x16cd
  | 150 => 0x1a4d
  | 151 => 0x14c
  | 152 => 0xce
  | 153 => 0x198c
  | 154 => 0xa4c
  | 155 => 0x134c
  | 156 => 0x168e
  | 157 => 0x2cc
  | 158 => 0x14cc
  | 159 => 0x24e
  | 160 => 0x19cc
  | 161 => 0xbcc
  | 162 => 0x16ce
  | 163 => 0x3ce
  | 164 => 0x1a0c
  | 165 => 0xd4c
  | 166 => 0x170e
  | 167 => 0x18ce
  | 168 => 0x194c
  | 169 => 0x178e
  | 170 => 0x74c
  | 171 => 0x1409405e
  | 172 => 0x19cb
  | 173 => 0x4956
  | 174 => 0x14b
  | 175 => 0x2cb
  | 176 => 0x2c9
  | 177 => 0x289
  | 178 => 0x1489
  | 179 => 0x24211
  | 180 => 0x44d
  | 181 => 0x95456
  | 182 => 0x44994
  | 183 => 0x98454
  | 184 => 0x44995
  | 185 => 0x129516
  | 186 => 0x5cb
  | 187 => 0x131054
  | 188 => 0x45414
  | 189 => 0x140454
  | 190 => 0x45415
  | 191 => 0x141556
  | 192 => 0xb9054
  | 193 => 0xb8294
  | 194 => 0xcb
  | 195 => 0xe8d0cde
  | 196 => 0xd0cce9e
  | 197 => 0xcced5
  | 198 => 0x170cd6
  | 199 => 0x58b
  | 200 => 0xcd796
  | 201 => 0x45894
  | 202 => 0xd1054
  | 203 => 0x194b
  | 204 => 0x104114
  | 205 => 0xced5
  | 206 => 0x105314
  | 207 => 0x12ced5
  | 208 => 0x104b94
  | 209 => 0xb4ed5
  | 210 => 0x105854
  | 211 => 0x16ced5
  | 212 => 0x104d14
  | 213 => 0x188454
  | 214 => 0x170ed5
  | 215 => 0x105894
  | 216 => 0x1a4ed5
  | 217 => 0xd2d6
  | 218 => 0x1692d6
  | 219 => 0x1689d6
  | 220 => 0x1789d6
  | 221 => 0x25456
  | 222 => 0x24b56
  | 223 => 0x16d456
  | 224 => 0x179456
  | 225 => 0x16cb56
  | 226 => 0x3d5d6
  | 227 => 0x58e
  | 228 => 0x1715d6
  | 229 => 0x178cd6
  | 230 => 0x18d796
  | 231 => 0x98455
  | 232 => 0x140455
  | 233 => 0x58e93
  | 234 => 0xe8593
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 47
  | 7 => 1507
  | 6 => 5242
  | 5 => 3816
  | 4 => 532
  | 3 => 67
  | 2 => 7
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
  | 8 => packedAt gbK8 (1376+((h/22+packedAt gbK8 (1222+(h % 22)*7) 7) % 80)*7) 7
  | 7 => packedAt gbK7 (63439+((h/640+packedAt gbK7 (55759+(h % 640)*12) 12) % 2535)*12) 12
  | 6 => packedAt gbK6 (279980+((h/2026+packedAt gbK6 (251616+(h % 2026)*14) 14) % 15636)*14) 14
  | 5 => packedAt gbK5 (243760+((h/1432+packedAt gbK5 (225144+(h % 1432)*13) 13) % 5157)*13) 13
  | 4 => packedAt gbK4 (39280+((h/204+packedAt gbK4 (37240+(h % 204)*10) 10) % 735)*11) 11
  | 3 => packedAt gbK3 (5581+((h/22+packedAt gbK3 (5427+(h % 22)*7) 7) % 82)*8) 8
  | 2 => packedAt gbK2 (652+((h/2+packedAt gbK2 (644+(h % 2)*4) 4) % 10)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffe03fc07fc0fffff03ffffff44f3c7d11f1ff
  | 1 => 0x7ffc1ff83ff0780ffc1e03ffbb4d38eee4e4f
  | 2 => 0xf83ffe0003fff800fffe00380c38e3f30f8f8c
  | 3 => 0x3ffffffc000000ffffffc00fc0fc03f00ff0
  | 4 => 0x3fffffffffffff000000000fff0003fff000
  | 5 => 0xffc0000000000000000000000ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8400200044008a21002288a20010434009095
  | 1 => 0x682c0d88191050464414115c194518866464a
  | 2 => 0xd0356e0422ead00abab402a06c28a2d30b8b8c
  | 3 => 0x4239b56d68084010cf3997008ec0f803b00d60
  | 4 => 0x843e39b6733ce65c021004010f7e0003dd6000
  | 5 => 0xe7102038403084600c2118060fffff6c000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeae8eeeaea88eeeaeae8eeeaea88eeeaeae8eeeaea88eeeaeae8eeeaea88eeeaeae8eeeaea88eeeaeae8eeeaea88eeeaeae8eeeaea88eeeaeae8eeeaea88, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36721
namespace PEqualNP.Outside.L_meta_36721
open PEqualNP.Outside.L_meta_36721.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 7 := block_range (n:=7) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 39 := (concat bs2_3_0 bs2_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 24 := bs2_4_0
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
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
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
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 90 := (concat bs3_4_0 (concat bs3_4_32 bs3_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 44 := (concat bs3_5_0 bs3_5_32)
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
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 90 := (concat bs4_4_0 (concat bs4_4_32 bs4_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 44 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 6 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 56 := (concat bs5_3_0 bs5_3_32)
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
theorem bs5_4_608 : Interval s5Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_640 : Interval s5Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_704 : Interval s5Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_736 : Interval s5Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 781 := (concat (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat bs5_4_288 (concat bs5_4_320 bs5_4_352)))) (concat (concat (concat bs5_4_384 (concat bs5_4_416 bs5_4_448)) (concat bs5_4_480 (concat bs5_4_512 bs5_4_544))) (concat (concat bs5_4_576 (concat bs5_4_608 bs5_4_640)) (concat (concat bs5_4_672 bs5_4_704) (concat bs5_4_736 bs5_4_768)))))
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
theorem bs5_5_672 : Interval s5Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_704 : Interval s5Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_736 : Interval s5Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_800 : Interval s5Atlas 5 800 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 801 := (concat (concat (concat (concat bs5_5_0 (concat bs5_5_32 bs5_5_64)) (concat bs5_5_96 (concat bs5_5_128 bs5_5_160))) (concat (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)) (concat (concat bs5_5_288 bs5_5_320) (concat bs5_5_352 bs5_5_384)))) (concat (concat (concat bs5_5_416 (concat bs5_5_448 bs5_5_480)) (concat bs5_5_512 (concat bs5_5_544 bs5_5_576))) (concat (concat bs5_5_608 (concat bs5_5_640 bs5_5_672)) (concat (concat bs5_5_704 bs5_5_736) (concat bs5_5_768 bs5_5_800)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 44 := (concat bs5_6_0 bs5_6_32)
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
theorem bgb_2_0 : Interval gbAtlas 2 0 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 7 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_64 : Interval gbAtlas 3 64 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 67 := (concat bgb_3_0 (concat bgb_3_32 bgb_3_64))
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
theorem bgb_4_512 : Interval gbAtlas 4 512 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 532 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224))) (concat (concat (concat bgb_4_256 bgb_4_288) (concat bgb_4_320 bgb_4_352)) (concat (concat bgb_4_384 bgb_4_416) (concat bgb_4_448 (concat bgb_4_480 bgb_4_512)))))
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
theorem bgb_5_3808 : Interval gbAtlas 5 3808 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3816 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672))) (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800)) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928))))) (concat (concat (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 bgb_5_1152))) (concat (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)) (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504)) (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 bgb_5_1632))) (concat (concat (concat bgb_5_1664 bgb_5_1696) (concat bgb_5_1728 bgb_5_1760)) (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 bgb_5_1888)))))) (concat (concat (concat (concat (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)) (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 bgb_5_2112))) (concat (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 bgb_5_2240)) (concat (concat bgb_5_2272 bgb_5_2304) (concat bgb_5_2336 bgb_5_2368)))) (concat (concat (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)) (concat (concat bgb_5_2496 bgb_5_2528) (concat bgb_5_2560 bgb_5_2592))) (concat (concat (concat bgb_5_2624 bgb_5_2656) (concat bgb_5_2688 bgb_5_2720)) (concat (concat bgb_5_2752 bgb_5_2784) (concat bgb_5_2816 bgb_5_2848))))) (concat (concat (concat (concat bgb_5_2880 (concat bgb_5_2912 bgb_5_2944)) (concat (concat bgb_5_2976 bgb_5_3008) (concat bgb_5_3040 bgb_5_3072))) (concat (concat (concat bgb_5_3104 bgb_5_3136) (concat bgb_5_3168 bgb_5_3200)) (concat (concat bgb_5_3232 bgb_5_3264) (concat bgb_5_3296 bgb_5_3328)))) (concat (concat (concat bgb_5_3360 (concat bgb_5_3392 bgb_5_3424)) (concat (concat bgb_5_3456 bgb_5_3488) (concat bgb_5_3520 bgb_5_3552))) (concat (concat (concat bgb_5_3584 bgb_5_3616) (concat bgb_5_3648 bgb_5_3680)) (concat (concat bgb_5_3712 bgb_5_3744) (concat bgb_5_3776 bgb_5_3808)))))))
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
theorem bgb_6_5216 : Interval gbAtlas 6 5216 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5242 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 (concat bgb_6_576 bgb_6_608))))) (concat (concat (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 (concat bgb_6_736 bgb_6_768))) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)))) (concat (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280)))))) (concat (concat (concat (concat (concat bgb_6_1312 bgb_6_1344) (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440))) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)))) (concat (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760))) (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920))))) (concat (concat (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080))) (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240)))) (concat (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400))) (concat (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496)) (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592))))))) (concat (concat (concat (concat (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752))) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912)))) (concat (concat (concat bgb_6_2944 bgb_6_2976) (concat bgb_6_3008 (concat bgb_6_3040 bgb_6_3072))) (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232))))) (concat (concat (concat (concat bgb_6_3264 bgb_6_3296) (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392))) (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552)))) (concat (concat (concat bgb_6_3584 bgb_6_3616) (concat bgb_6_3648 (concat bgb_6_3680 bgb_6_3712))) (concat (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808)) (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904)))))) (concat (concat (concat (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064))) (concat (concat bgb_6_4096 bgb_6_4128) (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224)))) (concat (concat (concat bgb_6_4256 bgb_6_4288) (concat bgb_6_4320 (concat bgb_6_4352 bgb_6_4384))) (concat (concat bgb_6_4416 bgb_6_4448) (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544))))) (concat (concat (concat (concat bgb_6_4576 bgb_6_4608) (concat bgb_6_4640 (concat bgb_6_4672 bgb_6_4704))) (concat (concat bgb_6_4736 bgb_6_4768) (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864)))) (concat (concat (concat bgb_6_4896 bgb_6_4928) (concat bgb_6_4960 (concat bgb_6_4992 bgb_6_5024))) (concat (concat bgb_6_5056 (concat bgb_6_5088 bgb_6_5120)) (concat bgb_6_5152 (concat bgb_6_5184 bgb_6_5216))))))))
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
theorem bgb_7_1504 : Interval gbAtlas 7 1504 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1507 := (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat bgb_7_288 (concat bgb_7_320 bgb_7_352)))) (concat (concat (concat bgb_7_384 (concat bgb_7_416 bgb_7_448)) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))) (concat (concat bgb_7_576 (concat bgb_7_608 bgb_7_640)) (concat bgb_7_672 (concat bgb_7_704 bgb_7_736))))) (concat (concat (concat (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928))) (concat (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)))) (concat (concat (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216)) (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312))) (concat (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)) (concat bgb_7_1440 (concat bgb_7_1472 bgb_7_1504))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 47 := (concat bgb_8_0 bgb_8_32)
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
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 33, 37),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 18, 22),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeae8eeeaea88eeeaeae8eeeaea88eeeaeae8eeeaea88eeeaeae8eeeaea88eeeaeae8eeeaea88eeeaeae8eeeaea88eeeaeae8eeeaea88eeeaeae8eeeaea88
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372968 * 2 ^ 32 + 4008372872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36721.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,2]⟩,⟨.and,[1,6]⟩,⟨.or,[0,7]⟩,⟨.or,[3,4]⟩,⟨.and,[2,5]⟩,⟨.or,[9,10]⟩,⟨.and,[8,11]⟩,⟨.and,[3,4]⟩,⟨.or,[0,13]⟩,⟨.and,[1,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4008372872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4008372872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36721

open PEqualNP.Outside.L_meta_36721 in
theorem PEqualNP.Outside.L_meta_36721 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372968 * 2 ^ 32 + 4008372872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372968 * 2 ^ 32 + 4008372872) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
