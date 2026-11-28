import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37261.Model
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


end PEqualNP.Outside.L_meta_37261.Model

namespace PEqualNP.Outside.L_meta_37261
open PEqualNP.Outside.L_meta_37261.Model
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

def SBf (j : Nat) : Nat := [7, 6, 6, 7, 5, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37261

namespace PEqualNP.Outside.L_meta_37261
open PEqualNP.Outside.L_meta_37261.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x1036bd1960e342000000c003800000560512c509870000008803e243035c786242eb4a8f3a649294084d2704a82931628a084a00604024b0800001cc0417c0ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1d9a8361f3f0682432301d030442f10c4a633d0a822270120006553281072010a0000c5a22a14007d000c46e200005452723b0b4006f40800102b250000a001e8001a16000000079230b0128328974c87100000a86727a086a1e080d0000e2d9acb85f0390878192b89896001f800907b3682c8e590014c82613b884d80c340c0f05012130923605000660000000004e118b8004d371d4c428201c0003a111cca413000742e841f03cf8582b1a4002f33000fe380e0081810209098081804000018240410ac080828003c04300000002c082c00080098240808180c0c481000009e7ca721cf54a439ea8c873e5090e7ca621e794c439ea90873d5110e7ca021cf94f429ea8e853e50d0a7aa92157d4d42ae29a859f5350a78a6a16714d428e29a85af5250a7ea2a14f141429f2a0853f54cca78a9994f952329eaa4659c438caeca3195d546329faa2653c544ca7ca8194f55032ce218653e53d067aa5a0cf943419eaa4835f53506b8a6a0e7d4d419e29a839c5350638a6a0cfd4941dba8a833c505067ca820cfd53319e2a6633e548c67aa918e710e31b7294636d528c67ea898cf151319f2a0633d540c7388618cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710cf951219eaa2433e540867aa810f948421af29c815d539027ca7206794e408f29c819d539027aa5204f546409f284813e531027aa4204f544409f28081ba501027ca9984f55330ce21e613e548c27aa9184fd51309e2a2619c434c2dea4985b14930bba8a6174514c27ea8184f150309f2a6413d54c827ea9104f152209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209f2a6213d54c427ea9084f152109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x68049e81602ec0002670090000628800088000e01402cc90304000600aa80800000080000c80c68718d51d0a1e63943428d58454ccb14439463287594430ca8d6210c328718d52d061e63943418b58854cc70c4394a3187594430c6956110c318718d544863860551218718d540861c63548408718d511030c4314930c510c514c21e63d50308b588540c23561150308718d54c821e63d52208718d54c421e63d5210
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 5 => packedAt s0K5 (864+((h/16+packedAt s0K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s0K4 (3970+((h/44+packedAt s0K4 (3618+(h % 44)*8) 8) % 161)*9) 9
  | 3 => packedAt s0K3 (1036+((h/8+packedAt s0K3 (988+(h % 8)*6) 6) % 45)*6) 6
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffff83fffffffc0ffffffff81fffffe3ff1ff
  | 2 => 0xc0ffffc0fff83fff07c1e0fffe1fe07fd13e73
  | 3 => 0xff03ffff03ffc1fff801ff07ffe1ff81e1cf9c
  | 4 => 0x3fffffc0001fffffe0007fffe0001fe0fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x44100888209000002942410900222a280650a5
  | 2 => 0x92299106492270cb0290a8d2b2154154d12652
  | 3 => 0xa4aa2121a46135550213a44d5419505618b18
  | 4 => 0x2cb344a49074a5a69cf4108769980619ba0de0
  | 5 => 0x30c38738e38739f8e739dce071111861fdf000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0fcccccc0fcc0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37261
namespace PEqualNP.Outside.L_meta_37261
open PEqualNP.Outside.L_meta_37261.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x25450a0070180258000190002400bf43bd43ef32ec32bf41bd41ee21ec21be40bc40ef20ed20
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x394c01a400020440a4c26aa3a1d994732c6a18651d53d069ca710e9504218ea9881355110298a6905914520
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 10
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (212+((h/4+packedAt s1K4 (192+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s1K3 (282+((h/3+packedAt s1K3 (270+(h % 3)*4) 4) % 13)*5) 5
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff83ffffffe07ffffffff03fffff1ff1ff
  | 2 => 0x83f03ffc1f83ffff870783e0ffc3c1ffea4e4f
  | 3 => 0xfc003fffe003e0fff807fc00fffc01e0f38f8c
  | 4 => 0x3ffffffc00fffff80000fffffe00fc0ff0
  | 5 => 0xffffc000000000ffffffffff00000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x80200088010000000808842210044422009095
  | 2 => 0x28c65910ca255865834323446642895c6a464a
  | 3 => 0x196aaa29474a89aab885e90abaa81586b38b8c
  | 4 => 0x528d34429460d2d355d04210cd333808dc0d60
  | 5 => 0x630e387318731cfc66e6739c0e222110ff6000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafaaaa0a0faaaaaaafaaaa0a0faaaaaaafaaaa0a0faaaaaaafaaaa0a0faaaaaaafaaaa0a0faaaaaaafaaaa0a0faaaaaaafaaaa0a0faaaaaaafaaaa0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37261
namespace PEqualNP.Outside.L_meta_37261
open PEqualNP.Outside.L_meta_37261.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x8ee21ec21
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
  | 0 => 0xffffe07ffff083fc3fc3fffe1fffe0113f3fc
  | 1 => 0xf07c3ff83e1fffc3fc3fc381fe1c0ffeeccccf
  | 3 => 0xff803fffc01ffffc003ffc01ffe00fff0f0f0f
  | 4 => 0x3fffffe00fffffc00001fffff003f00ff0
  | 5 => 0xffffc00000000ffffffffffe00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x6108023084001004404c048c6024621801515c
  | 1 => 0xa5104451902a0141c4144114a208a4a864c4c5
  | 3 => 0x422aa8a20d548a9c222aa829554149530b0b0a
  | 4 => 0x8a5331052906aceaaa82204199938063b00ea0
  | 5 => 0xc6221c63198cf333333327011020183dea000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeaacc00eeeeeeaaeeaacc00eeeeeeaaeeaacc00eeeeeeaaeeaacc00eeeeeeaaeeaacc00eeeeeeaaeeaacc00eeeeeeaaeeaacc00eeeeeeaaeeaacc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37261
namespace PEqualNP.Outside.L_meta_37261
open PEqualNP.Outside.L_meta_37261.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x6548894eac01a1800000004c0000861500005c41f02000005000e804438da540980003c016a358840001ea49241a143823850c802c1800b202808280000000100343830008282ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x14640662003c5a43077236235c005e675773417153423a654d63254b0066690024000000332b5f00000029001a030068002200510000004f5b4a08276f1c1b443000001f45000059287400000000005200000e5d004c2e31000000206046003d0000260d6c3b6b00004e0b1d0954003402213f002f5055323713004700116a356e2a1e00001538000f000a0c2c6149012d704800580016046d3e0039194000121000001756000018050000000007030002000091000300000180828000000101810000818000808101000a8180808380006750c43b7290876d5210e7aa9215794e42aea9c85775150ae8a2a16bd4942dba8a85b45150a7ca8215794c42aea98859f42ccb3a85994f952329eaa4655d538cb5a85196b50932bba8a6574514cb9ea49967d0932e7212659d424cb9a84996350932eba8a65d4514ca7ca8194f55032af298655e53d06baa7a0db94b41b6a96833e54cc67aa998db94b31b6a96633e54c867aa990d794f21aea9e43ad428879a6510cf950219eaa0435e53086baa610eb50821e6990437a50086f2a010dd94640baa8c815f53502b8a6a05794c40aea98816e52102daa4205d94440baa888176518c2eaa3184fd51309e2a2613e540c27aa8185b94830b6a906176510c2eaa2184f953209eaa6415e53c82baa7906b50b20e6996417651882eaa3106b50920e6992413e540827aa8105794c20aea98417651082eaa2106dd0b10daa1621d732c43aa65885d546109faa2213c54442bea6885714d10b7a92216c524436ea8886d15110eba9a21d453443cea4887914910dba1221b542443ae6488754c910f9a8221f220443e240885d94410
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x20049c280000000000818b8698008002202800402c31440000e580000a9a90001e0800c00000c0c350d5210f254214532a3592424cac46150932e1d85424cb846150932e150b514cb854214532c354d420870d544c821ca5095008749325402193588535022d6215130c354d42c830d544cb20e150932c43245414910d114c52442346550910951953244385424c910e850920443c13248110
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x500180a0cebb0a84994877650b514ca823aa849922181195424c910
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => packedAt s3K5 (841+((h/15+packedAt s3K5 (736+(h % 15)*7) 7) % 67)*7) 7
  | 4 => packedAt s3K4 (3471+((h/39+packedAt s3K4 (3159+(h % 39)*8) 8) % 170)*8) 8
  | 3 => packedAt s3K3 (960+((h/8+packedAt s3K3 (912+(h % 8)*6) 6) % 44)*6) 6
  | 2 => packedAt s3K2 (199+((h/1+packedAt s3K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x83ffff07fffe1f07f0fe1fffc3fff81e89f3f3
  | 1 => 0xfc1e1ff83c3fe1f8ff0fe1c1fc383fe176cd9c
  | 2 => 0xffe01fffc03fffff000ffe01ffc03fff870e1f
  | 4 => 0x1fffffc001fffff00001ffffc001f80fe0
  | 5 => 0xffffe000000001fffffffffe00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x884001108000200010120244404888440050b1
  | 1 => 0x19442231905402287106208cc41192c432c594
  | 2 => 0x208954420aa91153088954112a822519850a0a
  | 4 => 0x729598852a0d559daaa11021b3270189d80f40
  | 5 => 0x431910e6333199e6cccd993822040611efa000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeaeae0e0eeeeeaeaeaeae0e0eeeeeaeaeaeae0e0eeeeeaeaeaeae0e0eeeeeaeaeaeae0e0eeeeeaeaeaeae0e0eeeeeaeaeaeae0e0eeeeeaeaeaeae0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37261
namespace PEqualNP.Outside.L_meta_37261
open PEqualNP.Outside.L_meta_37261.Model
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
  | 0 => 0x1ffffc0ff0f87c3fc3f87fff87f0383e99f793
  | 1 => 0xe0787ff0ffff87c3fc3f8703f87fffc166c9fc
  | 2 => 0xff807fff00fffffc003ff803ff803fff870e1f
  | 3 => 0x7fffff0007ffffc00003ffffc001f80fe0
  | 5 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x4310046201108004c04809198091888c085391
  | 1 => 0x490088a240400881441882288824928422c0b4
  | 2 => 0x842551042aa445582225504255022531850c0a
  | 3 => 0x96566248a835566eaa844093664b0119d80f40
  | 5 => 0x1864438cccc667b3333664e0440c0621f7a000
  | _ => 0
def s4Atlas : Atlas := ⟨4,rawDecor 47 s4Pos s4Neg, 0xeeeaeeeaece0ece0eeeaeeeaece0ece0eeeaeeeaece0ece0eeeaeeeaece0ece0eeeaeeeaece0ece0eeeaeeeaece0ece0eeeaeeeaece0ece0eeeaeeeaece0ece0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37261
namespace PEqualNP.Outside.L_meta_37261
open PEqualNP.Outside.L_meta_37261.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d02fca5a05f54b40dfa1681bd42d02fca3a05f54740beaa4817e53902faa7206f90e40de21c817e52902faa5206f90a40de214817e51902faa3206fd0640dea0c817e509037e81207ed0240bfa9a817c53502fea4a05f14940dfa1281bd42502fea2a05f14540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840f7290816e52102faa4207b54840b6a9081be421037884205f94440fb288817651102faa2207d54440baa8881bf411037a82205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef18e61dc31cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c3eca3185d94630bea8c61f5518c2eaa3185f94230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa92617c524c3be6498774c930bfa8a617c514c3bc6298770c530fd98261de304c2fea8185f95030beaa0617c540c2fca6185f94830bea90617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3905f54720fda0641f840c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620bea8c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20f721241ed42482fea2905f14520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa88417e50083f680107e10020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c43ee63887d0c710fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10ef29c215e53842faa7087754e10aea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fda0421f840843f461087e4c210fd10421f920843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb20a21f541443ee62887d0c510fb10a21f521443f680887e10110fd18221f930443f440887e48110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xe5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7c87a16f10f42bf28e857d51d0afca1a15f54342beaa4857e5390bbca7215794e42bea9c85dd5390abaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42df21a85bc4350bde84a16f90942bfa8a857c5150afea0a17ed4142bda82857c5050bf0a0a15e14142bf2a0857e5310afaa6215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332efa1e65dc43ccafca3995f54732bf286657d50ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbe86997710d32f799265de324cafea2997dd4532bba8a657c514cbe8a2995d14532bfa82657c504cafea8195f95032beaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c837e52906faa520df94641dfa0c83f741906fca120fe94241bd284837d50907f2a120de54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa92837c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620df94841bea90837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc7be6598f74cb31bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518f78ca31ee194637e518c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c6fea498df14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f7d0c31ee218637e520c7dca418db94831bea9063ed520c6daa418f78c831ee190637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21f719643ed32c87ee6390fd0c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21f719243ed32487ee4290fb88521bfa82437c50486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21ef298435e53086faa610f754c21aea98437c53086fca410df94421fb98843f431087de4210fd88421f690
  | 2 => 0x1ed198004da7c41b8380000001408c4a25307e9330009993421015621c3508a28a784c588f22a4613180030052927a0526071c9e04a1942e12fa550006d0fca213dc494151433d27652b9103224908010e24694caf1962b2780d80e32e42f5208ed2521d4c60000000005a0b02f836c000774906b4b70d82767000017503e83c430000c2624078522de1f9120012065a024a732686a4b803e46c208340bb2da11d231c106a5d0550002164bc631543209ac8685416e4d8fe00033a511378004700003594b00056c96a294122a07102027c9400025b364000000001862489ea6c2ca0ad3b0002c2138001aa00028d23a01000000f3a223bc1146d2171fe78d1a9ec4404e44980c00000004000042000b49a017e9844e244000730e48044ea00000042000088118001be0001e02d22c408a09ac000518d72080005000007324c0000000000000026a5c1ba0e800000098310970f511a6710c1a74b22453295a1c060d200883783b04589f47e8dc310002280010a08419c024a723c270298b122c4389743c0b31c86e02f9281345c42d87d0cc7442b94231c5d8472251b89b82b1a32cc10cee1d0212050321811a2754de8c81e20000a9cd4223e12d17a33e000aea314a86a04a11931e3d8000004a46d4fd15f08c855171eb2f02d52103d24e8345905a242654ff9732d461cc111c2a40bc4081c1ac164038d930c54c678f02223541721d1f2684c422b1365544f0fb1e61e40313a3d48785624d2926490b2674c05fcca1ed01a348e90e81781bc709773b076cb010f3363241f880184570b19e41ee51c5781e38a560fba4b4047cca69ab3082b8380511f86f8ef8893e839c0ba4c27e475392030f82f81a04112a4c42a99820c6bc2221f434768259a50ec90ccf1b6006430ee85c02c6145b16b2fa178962193e088c3291e2f67088d197120698d890748a03c0500c570dc25004020800e1e8020bc1900c020d00003800000000000405c0003c0a0000500000000192a006020000040200405024000542c0001e00009000000080b08840104010140001c00044030000d01c07000120000c008020000100c050402a0001101c07008230001d0000000001008220380c0400004c0002805008060040c00000058000c070008060000000404000000100308438000010000a00800000070000000803000000880200400000460340300c850140000c09024010100900c260201a0140d18c0500011004030000f01001074a500026000920000c024030000001c06024020080704007004000200201803000030000b034050240d0b00101001bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877
  | 3 => 0xd98003940c48d8f41de9dc6a09d00a075130a225470c7d097426041249bf40c3b81b1c409e06c000000008e4cc80006020c9b86c0b00000023b00000103871372100699d43c4334000002261408906d1bc9a4f4234396838fb00000082c098b10007f45682700062801000000000000004e88c00000019814c639483cc3940024a0000005225604c6ec910d014e1a4a78744bc060bf2124c4284001ba3e4404bc8002ce001350000242606288501c32c0018d0000b0000000000000000020a000aba2a3ae000000002640007f0000004d40016c39c410000002a00012c0ba00042805896000831271fb1520c91e8670228bc3d00a45a9c4fc1e52c8000128f2076304f780047464d320630003ac3f99a000295051c800006519000348264e300017247c0023e0ba3a839039000000001a23a6000000000000008b8003ac81000000034000000480004ad0da702407f8000002a2000148004007d48415636e3a5140e6140300120600661b9139cf1ae
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x831cc27661d52309d587548c26e62152309b588548c27661152309d584548c23e64946308f592518c3366494630cd592518c3726094630d5947308c23e64951308f994544c31d6315130c7152434c25c6550d30c7153324c31c544c930d3149324c2d4614c930c7152314c29d640c530c7150314c2cd620c530b6980314c2d6618c1309798c540c26e62150309b588540c27661150309d584540c25f654c0309ed95300c25e63d53209758f54c823e64d4f208f59353c82776154f209d18553c82e86050b2097d8d51c825c6354720ea50b40c82e96210320ea90840c825e63152209758c548827661152209d584548827661d4e209d587538823f6454e208f191538823e64946208f592518823e64951209ed81544823e6515120cb588544823e6494d208f592534823f6454d208f19153482776154d209d185534832c54909209b195424833854c81209798f540825d63d50209d987540827561d50208f596540833860550208f990540825e63150209758c540826e62150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530823e6414c208f590530825e6314c209d98453082756114c20cd95251083355494420d594e51083555394420cd95151083355454420d594d51083555354420ce553400837151d00209e59440083715110020cb553200837151880209bd95200832d54480209ed9520082b86448020dc545200833661953108f99353c423d64d4f108f99053c423d6414f109b98853c426d6214f108f99352c423d64d4b108f99052c423d6414b109798c52c425d6314b10cd95141c42d46350710ad59031c42e5620c710b518d21c425e63d52109758f548425e63152109758c548426e62152109b588548435a6094e109798f528425d63d4a108f990528423d6414a109798c528425d6314a10b658c40842e96210210ae191308435a534c210ae191208435653c4210ae993108425f63551109718d544426f62551109b189544423f6454d108f191534426f6254d109b189534423f64549108f191524425f63549109718d524423e64149108f590524425e63149109758c52442f260905109d19541442d463505109d99731442b5640c510b958831442f2600c5109d19521442d463485109e99740442d96310110ba58840442f26110110ec50440442f2618c1109e19530442b8644c110f40c530442786548110ae19120442ba64c4110b598e104427a60d50109798c540425d63150109b988540426d62150109d984540427661d4c108f990530423d6414c109b988530426d6214c109e980530423e64148108f590520425e63148109758c520427661148109e980520423e64944108f592510425e63940109758e500427965840109dd95100427b6544010
  | 1 => 0xca3d64145329e980514ca796014532cd990514cb356414532d5d0c514cb544314532d58c8514cb726014532dc580514ca5e63d50329d984540ca7561150329e980540ca7960150328f992520ca3d649483297d95320cad4614c8329bd95320ca3f64540328f191500ca5e6394b419758e52d06b86050b419798e509065d6394241d698e50907596394241ced06509071c53d0d41c714f425071c5350941cb14942506b86050941ae982415063f65504419dd95411063e6494b318f59252cc6d4614cb318fd9150cc63c64543319e983548c67960d5231a7992328c66e62951319b58a544c65f635513197997324c6d4614c9319b98b540c66d62d50319e983540c67960d50318f596540c71c63550318f990540c66e62150319b588540c67a60150319e580540c71d54d0c3197594430c6d56110c31cb952520c72d5494831cb951520c72d5454831d3d0d520c74c4354831d9185520c65d658c831a7992320c74d528c831d3548320c74d52cc43197d95310c74d524c4319dd95310c73a5494031ce552500c76a5294031da54a500c73a5454031ce551500c76a5254031da549500c65e63d53219758f54c867b60553219e18154c863e64d4f218f59353c86e4614cb21f14cb31c86e5620c721f18c831c863f64543218f19150c867a60d52219e583548865f63552219718d548863e6414e218f590538867a6014e219e580538865e63942219758e508865e63951219758e544865f63551219718d544867b60551219e181544865e6394d219dd85534865e6514d21d3588534874c538c9219b195324875453c85219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c755153087546154c218f990530863d6414c219798c530866e6214c219e98053086796014c21d554f3108675650c421d354f210866f6548421d354d21086776548421b518d210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d50087733154021dc0c550087722154021dc485500865e6394b409758e52d02b86050b4097d8d51d025c6354740a798e429029c63506408f99742502b86050940c754e43102b96010c40d394e521034d5394840d394d521034d5354840cb90d521032c4354840da181521023d6590840a798e421032d5290840cb54842103565394440d554e51103665294440d954a51103726094440d594d51103555354440d994951103655254440c754f411032d52d0440a718d411031d5350440cb54941103365150440cb54b401023f6550040cb549401027b65500409b98b54cc26d62d53308f99252cc23d6494b30b518532cc29d640c730b358
  | 2 => 0x194001aa538000032c00220e0b68000000000010800001ba9d31aa0b720a000000009e800000fc97a98b69fc000000021c4a8006ba54c2a2e0027e3609a9220ae397a679cc2401812096cf18e9800078b5e3f910cc2e283b7034000000000019c4c000b51be77208dd2c817a4eb38000f89475b78e880000000001ee1e800000000000074332b81c2c49c4d4960002ca7ab6c00000929728506027020001880431ce2b9ce512ce9a96b996ad0000000001011400000d1b0800000003001fadcd5b1055000001f2000ac9b2b25a2b073a8800000001241f222000004dae4001e401000d600000174d403c00000a1000ce00037aa0900b609800002a40000000264de9a2a88000000000000000c47e800c8b96478007527c000000000000000000008e00600000d10e8142065e0000005854250559c0698008c080bbac40029035b4a8f80087800b080000158000000000030000000005f25600000b0102000a2388d2681b002b04001b2ce9f0e02be00000002340000000000000000000000142a30980000c39a443b04a000000000e002280037600000002d81c32661b2ed38c80cb02001440b000000f6000000019200000000000000000000000000035a000c646b900000086266cda2c0e86e0025cc504400000170000008e000a800000000005b2bc8a8a600000b30000023200000cf800001b607210c1998748003739a00000488000035c00212000000015c003a80000000000000722234c001387e09e00000c600020ab61d3a40011c088005180000236000000000000000961000018a9d8007d85200000133a0810fa80b1e002700000000200003aa0000000002db800000000d3549c8007a000e18001a15a719340017000c0801002000000000000400000000300200000000040080000416004000040200401010000000201c030000e0100000000004040540700809008000100001c000080700005004000000500c04004030000100002000020000100416004000040100402000000000801801028100040000401004000000300c030000302002008020000f00c00014000040100800018020040301c020080300817038000000000000018000000101800000020000002000000000000200400000000240000409008000067a60947439e58251d0e7661942439d5865090e3f6550c4397d954310e7a60947429e58251d0b1e53d0a42ab98a4350a9e63909429798c5050a5d63141429d9845050a756114142d698c5050b596314142ce90c5050b384314142ce9085050b726114142dc5845050a3f6550842ae1814210a6f655084297d8d5110a5c63544429e98354cca7960d53329d98650cca756194332c7953328ca7661951329d586544ca7761551329d185544ca7b60551329e181544ca5e65d0d32b398b434ca9e648c9328f990514
  | 3 => 0x933848330cd8224000b4a78006139e0028e7f980bf05a0014aba2aa86b6ac90b2640002e940000006a16ebe01e599bc368000008a000f091bae6e2fa000000017e00000002f6000002e0000000048000df000000002f04ea1976001080000000000cd000ca80059000002a60012641b0e001e0001f4000000013ce2000000004100076b620001a85a9200348b59c8ec2de2a8000a9e657b66531ca000000000000000a5000439a4000000000000000230121992e001b4000764f80000162000009e3163e2a800000000ea6b000000b0668861b038bf800001120026e002b80023cae8e03c800bb000000cc3bad20023a002b46300096800bd05418800bcaac0000002000d0800000f4000000000000000460002128a7780024800a713a1926200014003ac002681a8160029a00226002ae458000c00000280430002f800e30e4003204280000132b4046158a030b92001d800182b180000000d903600000292ea1e0ae548ce000ca908000b8000000094b284a02452000df8007b000350000000000000000000000000000000000026a002f0e619600
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xb54e05770530f00a0080c05192404c000401160735609b49a1900648c50029a79b4a9ca4314142a34e7210a0a1651635845050aa33968628a65459d23214532c62c8b00a299618531814250714290c0a1283515c44354831ac2e030aa418e0e6454a320c662bb46418e43541cd2154021a52e021aa42056171181521030731aa5210818318d5250440c28a830a649864452185324c20ebb0a818a6183151620c530952ed21081906306454520082c839a8220221a458d4110110d42c4a088088591740c530443483206298221705c8314c110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x8100000c8073589411011089187190314c110c80645c8314c110
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
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (718+((h/13+packedAt s5K6 (640+(h % 13)*6) 6) % 49)*7) 7
  | 5 => packedAt s5K5 (19164+((h/210+packedAt s5K5 (17064+(h % 210)*10) 10) % 759)*11) 11
  | 4 => packedAt s5K4 (19544+((h/157+packedAt s5K4 (17974+(h % 157)*10) 10) % 829)*10) 10
  | 3 => packedAt s5K3 (1475+((h/9+packedAt s5K3 (1421+(h % 9)*6) 6) % 35)*6) 6
  | 2 => packedAt s5K2 (184+((h/1+packedAt s5K2 (180+(h % 1)*4) 4) % 11)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe1ffff03fc7c70f1e3f1fffc7e0707c19f793
  | 1 => 0x1fe078ffc3fff8f01fc7e381f8ffff8066c9fc
  | 2 => 0x1fff80fffc07ffffe007fc01ff007fff870e1f
  | 3 => 0xe00000fffff800fffff80001ffff8003f80fe0
  | 4 => 0xffffff00000000fffffffffe00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x42431011880888010609048cc1231118085391
  | 1 => 0x44490122890201200a4321144849250822c0b4
  | 2 => 0x88842244109500562004482112044a61850c0a
  | 3 => 0x819654892281929b54900049a4960232d80f40
  | 4 => 0x1118600e332624ec9926927000180c4377a000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0feeaece0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37261
namespace PEqualNP.Outside.L_meta_37261
open PEqualNP.Outside.L_meta_37261.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x12d50f0b1a6a317110001c00007803660014b11284020000400f10a9ca63e19d2f6e41a2c3629115481d5bb062ccb20815e80289400000491b30060e0d2638b9d4e38146800038000000d080042c1802a0400001ffd5007fe5401ff55007fc5401ffd4c05fe5301ff54c05fc53007fd0c05fe43007f50c05fc4301ffd48077f5201ff94807fd52005f54807fc52007fd0801fe42007f50801fc42017fcc801fe32007f4c805fc3201ffd4407fe5101ff54407fc51007fd0401fe41007f50401fc41017fcc401fe31007f4c405fc31007fc8401fe21007f48401fc2101ffd4003fe5001ff54003fc50007fd0003fe40007f50003fc40017fcc003fe30007f4c003fc30007fc8003fe20007f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x824001ff04120027fecb88012ff65c4009ff32e2003bf99710027facb88026fd65c4009fe32e2004bf19710027fec988012ff64c4009ff3262000bf99310027fac988002fd64c4009fe3262004bf1931004ffea988027fe54c4013feaa62009ff15310027fec788012ff63c4009ff31e2002bf98f10027fac788002fd63c4009fe31e2004bf18f1004ffea788023fe53c4013fea9e2008ff14f10007fe8788023fe43c4001fea1e2008ff10f10027fec588012ff62c4009ff3162007bf98b10027fac588002fd62c4009fe3162004bf18b1004ffea5880277f52c4013ff2962009ff54b10006faa588027fc52c4001ffa162000ff90b10007fa8588003fc42c4011ff9962000ff8cb10007fa6588023fc32c40037f30e2004ffd4710027fca388013f651c4009fea8e2009fd54710027f8a388013ff41c4009ff20e2004fd90710027fa8388003f541c4009fe20e2004ffcc710047ee6388013fe31c4009fe98e2004ff0c710027e86388013ff21c4009ff10e2004fd88710027fa4388003f521c4009fe10e2001bf5831000ffea188007fe50c4003fea862001ff1431000ffe8188007fe40c4003fea062001ff1031000ffe6188007fe30c4003fe9862001ff0c31000ffe4188007fe20c4003fe9062001ff0831000ffc2188007f610c4003fd0862001ff0431000fe8218801bff654400d7fb2a2000dfd9510004feca8801bfe65440077f32a2006ff59510035faca8801bfc65440077e32a2006df1951001cf8ca88003ff64440017fb222000ff99110005fcc888003fd64440017eb222000ff19110005f8c88801bff544400dff2a22006ff55110037f8a888003ff63440017fb1a2005ff98d10015fcc688003fd63440017eb1a2005ff18d10015f8c68801bff534400bff29a2006ff54d1002ff8a688003ff434400bff21a2000ff50d1002ff88688003ff62440017fb122000ff9891003dfcc488003fd62440017eb122000ff1891003df8c48801bff524400dbfa922006ff94910037faa4880037d524400dfe2922000ffd0910007fc8488003fd4244001fe2122005ffcc910007fc6488003fd324400bfe1922001bfd8510037fea288013fe514400dfb28a2006ff54510037eaa288013fc5144001ffa0a2004ff90510007ec8288003fd4144001faa0a2004ff1051002ffe6288017f73144009ff18a2000ff4c510027f86288017f43144001ff90a2004ff88510007ec4288003fd2144001fa90a2004ff0851000dfec088007ff5044003ff2822001ff5411000ff8a088007ff4044003ff2022001ff5011000ff88088007ff3044003ff1822001fe8c11000ffa6088003f93044003fe1822001ffc811000ffc4088007fa2044003fe9022000fe4811000ff84088007ff1044009fd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x7ff504c003ff2826001ff5413000ff8a098007ff404c003ff2026001ff5013000ff88098007ff304c005fd9826001ff8c13000fbc6098007fc304c003ee1826001fe0c13000ffc4098007fc204c003ff0826001fe8413000ff8209801fff65c800f7fb2e4007ff9972001dfccb9001f7e65c80073f32e4007ff5972006dfacb9001f7d65c80013eb2e4007ff1972003df8cb9001fff64c800f7fb264007ff99320005fcc99001ffd64c80017eb264007ff1932003df8c990037ff54c801bff2a6400dff5532006ff8a99001fff63c800f7fb1e4007ff98f20015fcc79001ffd63c80017eb1e4007ff18f2003df8c790037ff53c8019ff29e400dff54f20067f8a790003ff43c8019ff21e4000ff50f20067f88790006fe62c800fffa964007dfd4b2003ffca59001fee52c800ffea964007df54b2006fdaa5900036d52c800ffe2964007ffd0b2003ffc859001fee42c800ffea164000fb50b2003ff8859001fff32c800fff1964007ff4cb2003ff8659001fff61c800fff30e4004bf9872003ffac390002fd61c800ffe30e400dffd472006ffca390037fd51c801bfe28e4000ffd0720007fc8390003fd41c8001fe20e400cffcc720007fc6390003fd31c8019fe18e4007ffc872003ffc439001ffd21c800ffe10e4001bf5832000ffea190007fe50c8003fea864001ff1432000ffe8190007fe40c8003fea064001ff1032000ffe6190007fe30c8003fe9864001ff0c32000ffc4190007ee20c8003fd1064001ff0832000fd84190007fe10c8003fe086400bffd952005dfeca9002ffe65480077f32a400bff5952005dfaca9002ffc65480077e32a4000ffd9120005fec890003fe64480017f3224000ff59120005fac890003fc64480017e322400bffd512005ffca89002ffd5448017fe2a24000ffd8d20005fec69002bfe63480057f31a4000ff58d20005fac69002bfc63480057e31a400bffd4d20057fca69002ffd5348015fe29a4000ffd0d20057fc8690003fd4348015fe21a4001bfd892005ffea49002f7f524800fff292400bfb9492005ffaa4900037d5248017f6a924000db5492003ff8a490003ff424800fff2124000fb90920007fa8490003ed424800ffe212400affcc92003ffc6490003fd324800ffe1924000ffd8520005fec290003fe6148001feb0a4000ff18520025f8c29002fff5148017ff28a400bff5452005ff8a290003ff4148001ff20a4000ff50520007f8829002bff3148001ff18a4000ff4c520057f8629001fff2148001ff10a4000ff4852003ff84290006ff6048003ffa824001ff9412000ffaa090007fc5048003ffa024001ff9012000ffa8090007fc4048003ff9824001ff8c12000ffa6090007fc3048003ff9024007fec812000ffc4090007ee2048003fe1024001fb0812000ff04090007fe1048003fd0
  | 2 => 0x40097f885a0047ff32d0001ff1968000ff4cb4008ff865a004bff61d0001ff30e8004bf98740007fac3a0002fd61d0025fe30e8013ffd474009ffca3a004ffd51d0027fe28e8012ffd0740007fc83a0003fd41d0025fe20e8011ffcc740007fc63a0003fd31d0023fe18e8000ffc8740007fc43a0003fd21d0001fe10e8001bf5834000ffea1a0007fe50d0003fea868001ff1434000ffc81a0007be40d0003fd2068001ff1034000f7881a0007ff30d0003ff1868001ff0c34000ffc41a0007fc20d0003ff0868001ff04340087fecaa0042ff6550001bfb2a80009fd9540087fccaa000efe6550021feb2a8010bf59540087f8caa000efc6550021be32a80039f1954000dfec8a0043ff5450021ff2a28010ef95140087faa8a0043bd5450021fe2a28000ffd8d40005fec6a003ffe63500057f31a8000ff58d4007ff8c6a000afc6350021ffa9a800fff94d40087faa6a003ffc5350001ffa1a800fff90d40007fa86a003ffc4350001ffb128000bfd8940007fcc4a0003fd6250001fe3128007bf18940087fea4a00437f5250021ff2928010ff54940006faa4a0043fc5250001ffa128000efd0940007fc84a0003fd4250001dea128000ff1094007ffe64a0003fe3250001fe992800fff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a0012fc6150021ffa8a8010ff94540087faa2a0043fc5150001ffa0a8000ff90540007fa82a0003fc415001fff98a8000ff8c540007fa62a003ffc3150001ff90a8000ff88540007fa42a0003fc21500037fb028001ffd414000ffca0a0007fd5050003fe2828001ffd0140007f680a0007fe4050003df2028001ff1014000f7880a0007f84050003ff9828001ff8c14000ff860a0007fe2050003fe1028001ff8414000ff820a003bff654c01d7fb2a600eff9953001dfcca9803bfd654c01d7eb2a600eff1953001df8ca98003ff644c0017fb226000ff99130005fcc898003fd644c0017eb226000ff19130005f8c89803bff544c01dff2a2600eff55130077f8a898006ff634c005ffa9a6002ff94d30017bca69800bfd534c01deea9a6002ff14d30017fe869800bfe434c005ef21a6002ff50d30007ba869800bfc434c001ffb126000bfd8930007fcc498003fd624c001fe3126007bf18930077fea49803b7f524c01dff292600eff54930006faa49803bfc524c001ffa126000ff90930007fa8498003fc424c005ff9926002f7cc930017fc649800bfd324c001ee9926002ff0c930007fec298002ff614c001ff30a6000ff58530007f8c298012fc614c01dffa8a600eff94530077faa29803bfc514c001ffa0a6000ff90530007fa8298003fc414c005ff98a6002ff8c530007bc629800bfd314c005fe18a6002f70c530007fe4298003fe214c001fe90a6000ff0853000dfec09800
  | 3 => 0xf31a4202bf98d21007fac690802fd6348431fe31a4202bf18d21007b8c69080adc6348433ffa9a4218ff94d210cffaa690863fc5348401ffa1a4218ff90d21007fa8690863fc4348433ffa924219dfd492103ffca490867fd5248401bea924207ff14921007fe849081ffe4248401fea124207ff109210c7fe649081ffe3248401f71924200ff4c921007da649081ffc3248433ffa8a4204ff945210cffaa290813fc5148401ffa0a4204ff90521007fa8290813fc4148431ff98a4204ff8c521007fa6290813fc314840fff90a4207fdc8521027fc4290813ee2148401ffb024200bfd81210bffcc090806fe6048401feb024217ff1812100df8c090867ff504842fff2824219ff541210bff8a09085ffe404842ffe2024218ffcc1210bffc609085ffc304842fff1024207ff081210bffc2090813fc1048409ffb284204bfd9421027fcca1080efe6508409bf32842039f99421027faca1085afd6508409beb2842009f59421027f8ca10812fc6508409ffb204204bfd9021027fcc810802fe6408409df3204200af99021027fac810802fd6408409deb204200af59021027f8c810812fc640842dffaa04216ff950210b7faa81085bfc5408409ffb184204bfd8c21027fcc61080afe6308409ef3184202b798c21027fac610802fd6308409eeb184200b758c21027f8c610812fc630842dffa984215ff94c210b7faa610857fc5308401ffa184215ff90c21007fa8610857fc430840f7f3104207ffd482103efea41081ffe520840ffea904207df5482103ff8a41081fff420840fff2104207ff5082103ff8841081fff320840fff1904207ff4c82103ff86410812fe6108409ffa884204ff94421027faa210813fc5108409ffa084204ff90421027fa8210813fc4108409ff9884204ff8c421027fa6210813fc3108409ff9084204fbc8421027fc4210813f62108409fe9084204fb4842103fea4210813ff6008409ff3004201bf98021027f4c010806fa6008409feb004200bf58021027f2c010802f96008409fe3004201bf180210b7fea010853fe500842dfea804214ff140210a7fc8010853fc400842bff9804214ff8c0210a7f8601081ffe200840ffe1004204ff84021027f8201084bff65d00277fb2e8013ff9974001dfccba004ffd65d00277eb2e8012ff1974001df8cba0006fe64d0027ffaa68012ff9534009f7ca9a004ffd54d0027deaa68012ff15340097fec7a0047fe63d00057f31e8000ff58f40005fac7a004bfc63d00057e31e8013ffd4f4008ffca7a004ffd53d0023fe29e8012ffd0f4008ffc87a0003fd43d0025fe21e8012ffd8b40007fcc5a001efe62d0001feb168000bf58b40097f8c5a004fff52d0027bfa968013ff94b4009ffaa5a00037d52d0027fe2968012ffd0b400077e85a0003fe42d0001fea168000ef50b
  | 4 => 0x813dc314c405fa18a6200ffd8131005fec098883fe604c4037f3026200ff58131107f8c098806fc604c443ffa826220ff9413110ffaa098883fc504c441ff2026220ff10131017fe609880bfe304c405fe1826220ff88131107f84098883fe104c409fe0826207ffd972103dfecb9081ffe65c84077f32e4207df9972101cfccb9081ffd65c843f7eb2e4207df59721004facb9081ffc65c840f7e32e4207ffd932103dfec99081ffe64c84017f3264207ff59321005fac99081ffc64c840f7e326421fffd53210fffca99087ffd54c843ffe2a64207ffd8f2103dfec79081ffe63c84057f31e4207ff58f21005fac79081ffc63c840f7e31e421fffd4f210f7fca79087ffd53c843dfe29e4200ffd0f210f7fc8790803fd43c843dfe21e4207ffd4b2103efea59081ffe52c840ffea964207df54b2103ff8a59081fff42c840fff2164207ff50b2103ff8859081fff32c840fff1964207fb8cb2103ffa6590803ed32c840ffe196421fffd4721027fca39087ffd51c8409fe28e4200ffd0721027fc8390803fd41c8409fe20e421effcc721027fc6390803fd31c8409fe18e4207ffd832103ffcc190806fe60c840ffeb064200bf5832103ff8c190806fc60c843fffa86421dff943210fffaa190877fc50c843bff206421dff103210f7fe6190877fe30c843bfe1864207ff8832103ff84190877fe10c8409fe0864204ffd9621025fecb10813fe65884077f32c4204ff596210e5facb10813fc65884097e32c4204ffd9221025fec910813fe64884017f3244204ff59221005fac910813fc64884097e324421cffd52210e7fca910873fd5488439fe2a44204ffd8e21025fec710813fe63884057f31c4204ff58e21005fac710813fc63884097e31c421cffd4e210dffca710873fd5388437fe29c4200ffd0e210dffc8710803fd4388437fe21c4219bf58a210e7fea5108737f528840fff294421cff54a21006faa51081ffc5288401ffa144207ff90a21007fa851081ffc4288437ff9944207ff8ca21007fa651081ffc32884097f30c4204ffd4621027fca310813fd5188409fe28c4204ffd0621027fc8310813fd4188409fe20c4204ffcc621027fc6310813fd3188409fe18c4204ffc8621027de431081ff72188409ffb044204ff9822100dfcc110813fd60884017eb044204ff1822100df8c110873ff5088435ff284421cff542210d7f8a11086bfe4088435fe204421bffcc2210d7fc611086bfc3088435ff1044207ff08221027fc2110813fc1088433ffb2a4219bfd95210cffcca9080efe6548433feb2a4219bf595210cff8ca9080efc6548401ffb224200bfd9121007fcc890802fe6448401feb224200bf59121007f8c890802fc6448433ffaa24219ff951210cffaa890867fc5448401ffb1a4200bfd8d21007bec690802df6348431f
  | 5 => 0x8c41027fcc62080afe6310409feb188200bf58c41027f8c620812fc631044dffa988225ff94c41137faa620897fc5310425ffa188225ff90c41007fa862084bfc4310409ffb108204ff9884103dfcc420813fd62104017eb108204ff18841137fea42089b7f521044dff2908226ff54841006faa42089bfc5210425ffa108200ff90841007fa842084bfc421044bff9908200ff8c841007fa6420897fc32104097f3088204ffd4441027fca220813fd5110409fe2888204ffd04410277e8220813fe4110409fb2088204ff504410277a8220803f54110409ff9888204ff0c441027fec020813fe60104037f3008204ff58041005fac020813fc60104037e3008226ffd4041127fca02089bfd5010449fe2808224ff90041097f88020897ff3010449ff1808224ff0c041127fc4020893fc2010409ff0808204ff04041027fecb18812ff658c409ff32c6203bf99631027facb1888efd658c409fe32c6204bf19631027fec918812ff648c409ff3246200bf99231027fac918802fd648c409fe3246204bf1923111ffea91888ffe548c447feaa46223ff15231015fac71880bff538c405ff29c6202ff54e31017f8a71880bff438c401efa1c6202ff90e31017fa871880bfc438c405ee21c6204ffd8a31027fcc51881efe628c409feb146200bf58a31027f8c51888fff528c447bfa946223ff94a3111ffaa5188037d528c447fe2946200ffd0a31007fc8518803fd428c401fe2146202ffcca31017fc6518803de328c405fe9946202ff0ca31017b86518812fe618c409ffa8c6204ff94631027faa318813fc518c409ffa0c6204ff90631027fa8318813fc418c409ff98c6204f7cc631017ee6318813fc318c409fa18c6204ffd8231027fcc118806fe608c409feb046200bf58231027f8c118806fc608c447ffa846222ff9423111ffaa11888bfc508c445ff2046222ff10231017fe611880bdf308c405ff1846202ff0c231117fc411888bfc208c409ff0846204ff0423110ffeca98886ff654c443ff32a6203bf9953110ffaca98886fd654c443fe32a6203bf19531007fec898802ff644c401ff3226200bf99131007fac898802fd644c401fe3226200bf1913110ffea898887fe544c443feaa26221ff15131025fec69880bff534c405ff29a6202ff54d31017f8a69880bff434c405ff21a6202ff50d31017f88698803ff624c4017fb126200ff98931007fac498803fc624c40f7e3126221ffd493110efea498887fe524c443fea926200df5493110ff8a498803ff424c401ff2126200ff50931007f8849880bff324c405ef9926202ff8c931017fa6498803dd324c405fe1926202bfd853110ffea298813fe514c443fea8a6204ff14531007fe8298813fe414c401fea0a6204ff10531017fe629880bf7314c409ff18a6204f78c531027f86298
  | 6 => 0x1feb168200bf58b41097f8c5a089fff52d044fbfa968227ff94b4113ffaa5a08037d52d044ffe2968212ffd0b410077e85a0803fe42d0401fea168200ef50b41097f885a08bfff32d0401ff1968200ff4cb4117ff865a089fff51d0409ff28e8227ff54741027f8a3a08bfff31d0409fe18e8212ffd8341177fcc1a0806fe60d0401feb068200bf58341097f8c1a0806fc60d044fffa86822eff9434113ffaa1a08bbfc50d045dff2068212ff1034117ffe61a08bbfe30d045dfe186822eff88341177f841a08bbfe10d0409fe0868204ffd9641025fecb20813fe65904077f32c8204ff5964116dfacb20813fc65904097e32c822abf5924116ffea9208b7fe549045bfeaa4822dff15241027fec720813fe63904057f31c8204ff58e41005fac720813fc63904097e31c822dffd4e41167fca7208b7fd5390459fe29c8200ffd0e41167fc8720803fd4390459fe21c8204ffd8a41027fcc52081efe6290409feb148200bf58a41027f8c5208b7ff529045bbfa94822dff94a4116ffaa5208037d529045bfe2948200ffd0a41007fc8520803fd4290401fe214822cffcca41007fc6520803fd3290459fe1948204bf98641027fea320813fe5190409fea8c8204ff14641027fe8320813bf4190401fba0c8204ffcc641027f86320813ff6090409ff3048201bf98241027fac120802fd6090409fe3048201bf1824116ffea1208affe509045bfea84822bff1424115ffc81208affc4090459ff984822bff8c24115ff861208affe2090457fe1048204ff84241027f821208abff65504557fb2a822aff9954101dfccaa08abfd65504557eb2a822aff1954101df8caa08abff5450455ff2a2822aff55141157f8a8a0803ff63504017fb1a8200f7d8d41005bec6a08a7fe63504057f31a8200ff58d4114ff8c6a080afc6350401ee31a8202b718d41157fea6a08a7fe5350455fea9a8229ff14d41007fe86a0803bf4350453ff21a8200ff50d410077a86a08a7fc4350401ffb128200bfd8941007fcc4a0803fd6250401fe3128207bf18941157fea4a08ab7f5250455ff292822aff54941006faa4a08abfc5250401ffa128200efd0941007fc84a0803fd4250401dea128200ff1094114ffe64a0803fe3250401fe9928229ff0c941157fea2a0813fe5150455fea8a8204ff14541007fe82a0803f74150409ff20a8204ef9054114ffe62a0813fc3150401ffb028200bfd8141147fcc0a0806fe6050401feb028228ff1814100df8c0a08abff5050451ff282822aff54141147f8a0a08a3fe4050451fe2028229ffcc141147fc60a08a3fc3050451ff1028228ff08141147fc20a0813fc1050409ffb288204bfd9441027fcca2080efe6510409feb288226bf59441027f8ca20812fc651044f7f3208226ffd5041097fca82089bfd5410425fe2a08204ffd
  | 7 => 0x21002fd601080ffe3008401bf180421b7fea0210d3fe501086dfea808434ff140421a7fc802104bfc401086bff9808434ff8c0421a7f8602101ffe201080ffe1008434ff840421a7f8202101fff658c80f7fb2c6407ff9963201dfccb1901f7e658c8073f32c6407ff5963219dfacb1901f7d658c8013eb2c6407ff1963203df8cb1901fff648c80f7fb246407ff99232005fcc91901fbe648c8015f3246407ff59232005fac91901fbd648c8015eb246407ff1923203df8c9190cfff548c867ff2a46433ff5523219ff8a91900afd638c805ffa9c6402ff94e32017faa71900bfc538c805ffa1c6402ff90e32017fa871900bfc438c80f7f3146407ffd4a3203efea51901ffe528c80ffea946407df54a3203ff8a51901fff428c80fff2146407ff50a3203ff8851901fff328c80fef9946402fbcca3203ff8651901fec328c80fffb0c6407ff98632025fcc31901ffd618c8017eb0c6407ff1863219ffea3190cffe518c867fea8c6433ff14632017fe631900bfc318c805ee18c6407ffd823203ffcc119006fe608c80ffeb046400bf5823203ff8c119006fc608c867ffa846432ff9423219ffaa1190cbfc508c865ff2046432ff10232017fe611900bfe308c805fe1846407ff8823203ff841190cbfe108c865fe0846431ffd953218dfeca990c7fe654c8077f32a6431ff5953218dfaca990c7fc654c8077e32a6400ffd9132005fec899003fe644c8017f3226400ff59132005fac899003fc644c8017e3226431ffd513218ffca8990c7fd544c863fe2a26407bfd8d32017fea69900bfe534c805fea9a6402ff14d32017fe8699003df434c805ff21a6402ff50d32017f8869900bdc434c8057fb126431ffd493218efea49901ffe524c863fea926400df5493203ff8a499003ff424c80fff2126400ff5093203ff8849900bff324c805f79926407ff8c93203fbc649901ffc324c80fee1926402fb0c932007fec299002ff614c801ff30a6400ff58532007f8c299012fc614c863ffa8a6431ff9453218ffaa2990c7fc514c805ff98a6402f7cc532017f86299003ff604c8017fb026430ff9813200dfcc099003fd604c861fe3026401bf1813218ffea0990c3fe504c863fea826430ff14132187fc80990c3fc404c805ff9826402f7cc132017fc609900bfc304c861ff1026407ff08132187fc20990c3fc104c825ffb2e8227bfd974113ffccba080efe65d044fbf32e82039f9974113ffacba089efd65d0401beb2e82009f59741097f8cba080efc65d044fffaa68212ff9534113ffaa9a084bfc54d0425ffb1e822fff98f41015fcc7a0803fd63d04017eb1e8212ff18f41015f8c7a089fff53d045fff29e8227ff54f4117ff8a7a084bff43d0401dfa1e822fff90f41007fa87a0803bd43d0425fe21e8212ffd8b41007fcc5a081efe62d040
  | 8 => 0xf0c3421f7fc41a101ffc20d087dff086843eff0434203ffecb2101eff659080fff32c8403bf9964203efccb2100e7e659080ffeb2c843dbf5964203efacb210027d659080ffe32c8407bf196421d5fac9210f7ff549087bff2a4843dff552421eff8a92101fff639080fff31c8402bf98e4203fbcc72100ade639080ffeb1c8400bf58e4203fbac721002dd639080ffe31c8407bf18e421effea7210f3fe539087bfea9c843cff14e42007fe87210f3fe4390801fea1c843cff10e4203dfcc52101fff529080fbfa948407ff94a4203ffaa52101f7d529080ffe2948407ffd0a4203f7e8521003ef429080fff9948407ff0ca4203ffec32101ffe61908097f30c8407ff58642005fac32101ffc619087bffa8c843dff946421effaa3210f7fc5190879ff98c843cff0c64203ffec12101ffe60908037f3048407ff58242005fac12101ffc60908037e304843dffd42421dffca1210f7fd5090877fe284843bff902421dff881210f3ff3090877ff184843bff0c24203ffc412101ffc2090877ff084843bff042421d7fecaa10eaff6550875ff32a8403bf995421d7facaa10eafd6550875fe32a8403bf195421d7fea8a10ebfe5450875feaa2843aff15142007fec6a1002ff6350873ff31a8402bf98d42007fac6a10e7fc63508057e31a843affd4d421cffca6a10ebfd5350873fe29a8400ffd0d421cffc86a10e7be4350801fea1a8439ff10d421cf7886a10ebff5250875bfa928407ff949421d7faa4a10037d525080ffe2928400ffd0942007de84a101ffe425080fdf2128439ffcc94203ff864a1003ff61508017fb0a8400ff98542007fac2a1003fc61508097e30a843affd45421d7fca2a10ebfd5150875fe28a8439ffcc5421cff862a1003ff60508017fb028438ff9814200dfcc0a1003fd6050871fe3028401bf181421d7fea0a10e3fe5050875fea828438ff141421c7fc80a10e3fc4050873ff9828438ff8c1421c7f860a10e3fe205080ffe1028438ff841421c7f820a101fff651080f7fb288407ff9944201dfcca2101f7e65108073f3288407ff594421b5faca2101f7d65108013eb288407ff1944203df8ca210defe641086dffaa08412ff950421b7faa82104bfc541080fffb188407ff98c42015fcc62101ffd63108017eb188407ff18c4203df8c6210dbff531086bff2988436ff54c421aff8a62104bff431086bff2188400ff50c42097f8862101efe621080fffa908407dfd484203ffca42101ffd521080fbea908407ff1484203ffe842101fbf421080fff2108407fb9084203ffa842101fbd4210801f6a108407ffcc84203ff8642101fff611080fff3088404bf9844203ffac221002fd611080ffe3088436ffd44421b7fca2210dbfd511086dfe2888435ffcc4421aff8622101fff601080fff3008401bf9804203ffac0
  | 9 => 0xc05ef21e8602ff10f430177887a184bff62d0c01ff3168607bf98b43007fac5a1802fd62d0c25fe3168645ffd4b4322efea5a1917fe52d0c8bfea968645ff14b43017fe65a180bdf32d0c05fe1968612ffd8743007fcc3a1812fe61d0c01feb0e8600bf58743097f8c3a1917ff51d0c8bff28e8645ff5474322ff8a3a180bff31d0c05fe18e8602f70c743097fec1a1913fe60d0c037f3068600ff58343005fac1a184bfc60d0c037e3068645ffd4343227fca1a1917fd50d0c89fe2868644ff90343097f881a180bff30d0c05ff1868602ff0c343227fc41a1913fc20d0c89ff0868644ff0434321ffecaa190eff6550c87ff32a8603bf9954321ffacaa190efd6550c87fe32a8603bf19543015fec8a190fff5450c87ff2a28643ff5514321ff8a8a180aff6350c05ffa9a8602ff94d43017faa6a180bfc5350c05ffa1a8600f7d0d43017fc86a180bbe4350c05fe21a8602ef10d43017b886a1803ff6250c017fb128600ff98943007fac4a1803fc6250c0f7e3128643ffd494321efea4a190ffe5250c87fea928643ff14943017fe64a180bfc3250c01ffb0a8600bfd8543007fcc2a1803fd6150c01fe30a8604bf1854321ffea2a190ffe5150c87fea8a8643ff14543017fe62a180bfc3150c01ffb028600bfd8143217fcc0a1806fe6050c01feb028642ff1814300df8c0a190fff5050c85ff2828643ff54143217f8a0a190bfe4050c85fe2028602ffcc143017be60a180bfe3050c05fe1828642ff88143217f840a190bfe1050c85fe0828600dfd9152006fcc8a90037d6454801be322a400dfd8d5220efcc6a90037d6354883be31aa400dfd0d5220efc86a90037d4354883be21aa403dfd895201cfec4a900f6f6254883bf992a407df0c952006fec2a90037e6154801beb0aa400df1855220efe62a91077c3154801bfb02a440df98152006fac0a91037c6054881bf202a440df1015220efe60a91037e3054881be182a440df8815203ef840a91037e1054881be082a412ffd97421bdfecba10dffe65d08077f32e8437ff597421bdfacba104bfc65d08077e32e8437ffd5342097fca9a10dffd54d0825fe2a68412ffd8f421fffcc7a100afe63d0801feb1e8400bf58f42097f8c7a100afc63d086fffa9e843fff94f421bffaa7a10fffc53d0825ffa1e843fff90f421ff7c87a1003fd43d0825fe21e843fef10f421bffea5a10df7f52d080fff2968437ff54b42006faa5a101ffc52d087fff9968407ff0cb42097fec3a1003fe61d08097f30e8400ff58742005fac3a104bfc61d086fffa8e8437ff947421bffaa3a10dffc51d087fff98e843fff0c742097fec1a10fbfe60d08037f3068400ff58342005fac1a104bfc60d08037e3068437ffd43421f7fca1a10dffd50d087dfe286843eff90342097f881a10ffff30d087dff186843ef
  | 10 => 0x1400001400400000c07000004405401801401400401c00000400802c0bc00001003000400800802403800000c02400c01002001c06002800c01003404800000400800000000c0200bc00402400000003c00800803402402002c00400000000002400000000801000400000c01000000401012000000000003400401800400000c00403402000006800004400009801002000000000c00000c00c00001c02000400400000001400c00400000003400400000001405000401000400001801000c06c00801800800804804000401803800000c04406000000800800000000801400000806400000001002800400000007800400800000004400000400801000002400804000c00400400401400001c00400c03c04004403003400004400400000404404400000c03000800004402800000807800000002000400c00000400801400400000400002400000800800000000000000000c01c00000c00400001401000402402402000404c00400003405400000000000000401402000403000000800c01800800000000000400001000000800802400402c01800000802c00402401800400000001400400000801800401000000c00801803400000000001002000400400000002403c00000000000801000400001800c0040080040a009c00802405003801803c00000400c04400400c00000803800800000000400c02001801000400007000000401400402801801c00403c00800002000800c02801001400403801000800000c00400000800400001c00004801c00001000000400800c00400003808800000000000000400000003800800401000002003000400001001000401000400002800002000000000c00001001000800c02404800000400000001000401003403400400800803000000400400000000400002000400400400802800000400000000400400000000000404804000000005c00c00000800401800001400401400c00c02400400005402c04000001002400401000001800402402400000009000800403001c00400000800400001400000000000400c00400400000005008802000800000401000401800407400800001801c00001001400401000400c02800000000001000000001800800c0040080080000b000003800000003001401c00400403001c01400400000000000001800400800000000410000000000000400001402001400c00800001400400001001400000802c00402405000c04009800401000c03c01001401401800000803002000001000c00000006800000000800c00001000025ffb2e8645bfd974322ffccba180efe65d0c8bfeb2e8645bf59743097f8cba180efc65d0c057f3268645ffd5343097fca9a1917fd54d0c25fe2a68602bf58f43017fea7a180bfe53d0c05fea9e8602ff14f43017fc87a180bbe43d0
  | 11 => 0xbe00c41fc000000191813a7f928d060c71c6a7000169000063a00012783c800032c0d407a439023202d050a53013517ec4f28282221a7c4148303ef8dec9ac7922fe1f701a000022d97b846033227680010f80002fd0000b368830e7814024e56425595e8ad854219a1ca81582ea25788b83602d10b3852c9526d912c12b0f1800000013a90846780f080000003d600008cc00022c0001b3d00864e42197440007030000310000000000000053000000000000000001b904bc94612000017c40001e30001138de200000000000004cd00000000007e2318011cb2467338083f478c2491398dd8a8e89528b0370f5685d11c1ce49983f833592089fe47a0001c980000410528990b62812447000000012e00015ec71002f2e780582785312d91d940001d522d0dac1c200036b96bc0001ee0001ab000000016e86c487a63239905d01a87c240280000005e800218049bc29e13d99c89023de0001f6d0140000cb0c4c37e62134600710c06e031a1c1c3f443f0d09a802c200000000001240000b99b180c22fc00017f421079003e00011020be0a69e440007631df0000e120003c59fe00004860000b4c4560001ef80000002bb1c6895c00052313f8f6828032a00020e03a67e800008c86c84a527e934c000000000000026c38f00004887b652b443100cc544f700000f400000000000004fc0000a500005c61763ae0000f2c5b60001e6ced467a0d5890112817b000021063a3330000ae4e1a05b336892093647c13b8b840001970618630f3e18a3d5059417e57d2c09c74d822013b4a00d07e40b35c95402fa72b2d321ecfca0000d00e28ddc61f34a0000c4882a1491858b661c13f087ec00000040d15389c409704796680000000e28ee8b5672d16794082567bf272046812668526522dc000000000000000061200010b4d8079500000001da2371b00f44bc200000015e0000808000188cd0e48c21700003020000000130a7466300017040000de0f503c88de0001f20a4cbc60003c780002b04c04111fd06f401914a03cceda7c8141000034c0000c90000dbc31a146000107400000018cc0000000329510b1a6c320110f85e6000131800115e2f12c280000005d63d31de07984b217a0c34ebc4bf1738890ee02500819298f2e8491079a5cb9061c0000b000006ef11e012000004401c01401001c00800000000000801000000000003c01c00001800000400002001400401401800000803000000000805c00000802c04c00000004000000400800400000c00803403001803000402001000000000000001002400403400000800003803001400400002400000803000402800401800800400000000c01c00800001400000000000000801000002c00c01005801000c00003800001401c00007800000000001c02400000c00004400002402002800
  | 12 => 0xa1a42720c14383da5d72f21ec80007401dda2c000070600000007b0000050943c7fe45822398f4d3400300f1430fd439a15a0c444241870000000000000000107c0004e80bf1bb0d365f509d8d843883e514e0f9c67c04a2fb06b90dc4200b115b4eb04260fa1b58f8a0003ce88140000002ee13f002a000000137c0880000000908172000000000051229a00000000002fa0001c000000004089ad80c82180000f540000000000000a3c06d3ba8d1c10c83417701a40d81073088000df820c30d9db10ee0000bca18917034517c800000000000004180000000000b8843c0e0000165801269625a0000dd41b7000000000062609f9f98e6a71812a9b7d14811616f8e5911249a0faa22806a0f13889e64cf249109a9b4504c2711c08a80cfc03610418a50380242d39ff4a2641a0e0162c2e403316b0ce88d823e0e3912416a68f2d41f4ccc05da04b01c0a404bd23b18b0d9a58f1511c085fc0d116618fc2dc00000001d40005a928800005bc0f500000009e67b3450953400086d000142000000000000000003a600000007185c512c8c007ba5eb27180007640000000ecc268000420a1701e80002c000009ca0000000000000000265800103e3b00bd0aad0aa0c5000094c00055a00006746ac6e402b0d6043a3d9209852054a0002ef8a00fdc15b17013700001851a580d0e242a70760000b060000000d540000003000b1457a3040000f98f9e000000000096600000021111260001d88000f420000001e380000002b0000088a7b93c980e8c7624b00000005ca0002998c647ec5513911494efe36f21d80005460002c121f8ea400044f941800000010d953c7ee0d539b929c0fa4ec01b800098643c0000c8cb3a0130a800000006c709b80000006b0329000005a2c43938000000186084800000053245a000102010a34000000001f000003e1064691429057819860620789bc2044ee0d60000fc05ed1db8000000000000187400083b0001958738000231918400000004f8000b9c64d129112c0003e200015650a84253b71ce876845f165085c5022761ae80000001b21870f8c75839529096384d600000012f050800030a80000001e80001a6000058621a80000008ac42fa1c845e7470000b986b464016a0020b5400019c9be80ba04e0001ccc14c00000000005d20002b400006a2436413800028c000435216851e0001b80aa4a4e02c00020900000001e58c9058200000000011000000011a34000000226105866270f24790bcf705ba3a494a800005c24c00000005e90000cbc9aa3022cf801c860000000000101200008780000003f000000006584e640317d10261dd37c89947a60000ff8000e963c40000000000000000042c8d000040597c8000000370957c39465c0da00000f60001d58da40d47440750000f861dc03712240003291
  | 13 => 0x15cc2240b61b18ad8aaa3370ba87943502fd04416208200c61df8ac81a667d42400850460ff29f017831e3ca2801350fc80a41eb95c04881113ae82008d460b38619788ea50104d00003cc000000099c1d60001b28c9cfba54000000000004373730fc400034614b0000f2864a3dd8e1c0006ba00005dc46800022e000109665d0001ea08d223545310e0f1a3c330b8bd8e6200000014884460000000bc8748000000224445a0003b1000000000000000000000000000000638000099845068818d0000da07a80000000464d1600007414b0000000000000078047440613140001803e900000160002f380008dc37d2d180005063491380abc000152148a1145360ca2bc812423638005d9f04c6e66226e80008840003ab800000049504c800109800012f8980086644000008c0e830802300000002cb00000005d04700000fb404e000282818ccc88a82c60000fec8162c81d400000000000000192773000000000085113c00000008172e4a0040000003b38e449ec000035847c0f00003c21d3800069c35721e8f9674113308e82a800000019540962471580d5c70a0f62159ad4cfe0102310cd4c080002161ee874a6842b51e1ccd21300e620849824791680c244626ad04f1664d7c3a818600009ae2863bd8d2800040530108d80006d42251010bee2141fd161080e2e426c0d04ce806f29f8bac45284f2419a08c1a000000000069a00000000000000000000afc0000000001cc00005a10ed0000ea83c100000004048a335282f40006cc27d80006dc2da1d00000000507000000000000035917c005600000000002d40003f88d98c5e7563ff9a28f801fc28e838ce8c48e3e300a00000010000060bcc13a00000000006b43041f44f465c3000195000086400016e00aa517418933cacc0002a580000007c43daa22c3366f312a18d49f000022022141ee14912e8000c141051268000eb60002500000ffc5b700016b0b0e0fa000000045000022b8270e7078306c0d64f6e0ae438914c9ce1cb3ba22cc7521261f0882cc8e1a21cd9030f686b8244020ccae2d83bb19240005de1cc1a90ed619928f9d904b6645069000000083720499c023a07718a2194fbc493190985057c3ec1069b1461634e43c94b51342ad29aa2d811200a19e1b080004770f00e782c6000000199c0005bc0000fd08005982e00d000001af00018940007f308722700000002ba1c5460c00000019dc0000001fa93d0ade00000000000000003eb9cfc0000002df00f8a9216f000000000027227000000000003fe066000000000d00000004eb000122c00000039711340000aa3d28000000000000216c4ac6f5379033459a6a63ea0000cd400039e000049e0004330e843b28a70000000e320fb01007f41900000001a2000000039180001de000000217800000018f171c
  | 14 => 0x4f44210c597fcf8e1f83bba0b804c09801106707d44f921995c4d2a10c310190c34e422441159c1600000c4800012a30319281cc93a4340590000e2c54a20a02140000000000e5ce8a0000cf883856e7d80d505c45a488d1e4800040c38600019687900003a111987467d92189fec65a52600000000000000cd000000016d3c40cec00000008c16b800000000010c8d0686b10a8530b8836d1d50398aec0f90918888e480583c48580d3a6a342c9c390a07710000894aa800038e1fb40002a4000000000041725c0d3cbf06812791b10ea600000000010ce83c153000060200000016d48aa7a025c98d80001a5337110470606823e800000024a0001b6c3e456e00012d4dba4280001d3c0006b100000000003431910000e360000000f40a8c0b7000176ccec2680000000ba660700300000006ed06383b800000000000003a4000439800104a0000c980000006930c1049015682900003900000000c8800000000000000000002c33e7021c88c74c027800000063c00000000000fc00000000001a91c222302be00028a80000000003378dfc8fc37908e04e40004b6000227480c73e3550504b5a8390f1023431048522815707d04592ff0000d4419039d9148a285090091df8aba1b600000008e467c22899200001440000898ab60002978114e2089910d00008ac00038f97648c080f03b0fe411672f3fd0f1497c75f37580000003fc0de12700005bb0929b549240000000000000000071000000033000004c819c666000000000000029c80000006890000000d7836a00012ec5164c7041179465c74d458a28051c65100014649e22393d898647284b1000000000060327d000082a0001cf800000000000000000000003840000000000000225c2d00001959cd030803c2a60bc03bc00028d8000670000000000042648a0001d80b6800000000009c200019407600f28a514b9f9cdec00036e07dc00068e2bf00000005623e800b80760000001ba0c5060f05104a800001f35e8050bd400000000000001210001e6881089205180001222f7000000000000005018680006ca34c88fcabc5243c007a49b424543c00744388aa1dc9348b604c82a28000000000000000000089e2580000cd817c2e5965caae47b1fe8fbc0a81ad0f994d0e267a90e1800000035f0cf0ee00000e90a7984075a33f000004408049400000000001ec0000e7502a25c000088000028a26c93a4e081420000000000352000203800a1b93941d6808449631c84f82aa87d2218d7800000012300000000000001f3000021f38d0000b9a0000001ec107c00000022ad0402ef1ba800000059c100000040600018d80004b42dc42500000000003be173000029f0001fdc00088813080000005891de8e4d08c0002bb93bc42c80218900000000d9248029c346833000000000004d
  | 15 => 0x1fd803c0004480b80000c7c4db3de035ce2875132c800000000033a800000000000000000000000ef800000000036400010e056b1b9800000000000006e80000620000000000000000000000000044d9da00000a90001abc00060e37f00010300002c880000006052de8af0ede377156113cd521be43a81c47dc05929da23c18412806e8a1cd7e0320ae82a01367f23110e242a220720e8230a3861e2f0000063041c0409b24bb0575285000000030500016504d81e723899ec92e41e000000037a0003909f5463e48415d00000003fe3d200005d86423e50e08114000000000049c58a13700e400000000000000000003ac800058e3e040d92a868400006d800075e3170000b249444ba28c1c1400074a0da9cd80004ad05681f8c9e00000000000006e73280f70d6e8983d79de88e68b50588000c2678541a800079e000108800000000034800006a80002dc84c40ae89605994f00000af3540514f0400000022b400000026700000001a42f60000fd80001db22400003780001eb40002a80738df8ba806700600000001432a080010ae2ae000000000000000000000005a22be14d8a220000bc00000601d41ae00000005f300003000000000000c803ac0000330000384153434954817430a0e690a460e00000000000004d1000006c0000001c580000007da2a99e6000042a00000000006e341e800000008e11e800000086106584a420200016b800007e0002ab21fc00015700000000004a425717bc75c0002439e28b8c5bf36d00009e01eb11d94a08322a1115132431c000000127cae400000019300000004169178b3c156000000001c6383680000df08680000000f9288703004346a600017f80000000000e81fa42cc1bb41780004da0000001eb80002c600021bc0000001de00000006fb000196c0003eb13e8538ec2000000119c00000001c00000006313c09facf384f503d1de4de813d00004b05900001b1168000021040e800048257f0ed969400086c2948000f580000000c40000000000000000000000000000006d83cf0000000000442035800009000000000004a8394890c0001d707297080000000d99410128840000040000082b1e7152053a8630e48acc0007f0000000051a3b524680340a216b0001c7804a15a000000000000006780002d800015c00006b60000b20654e864c22072034ba480017d8c58c967a205c1d98e9081e08221608ba24c000000080270a2509034000000000000000000000009f022e0000001a78c185613db1b4ce4a52e0000e884420000000dd0a7a0000000e48bf27720000000bba25e37f80000000001e3882402e46d330908c61e3a73158d206981ef03900010a653845901680a41fe31707e439c5d006d0db0000000029a1582206ab0150b085542692121b2ca6e6e219b00003ec41216a872
  | 16 => 0x2700001e10000d760003e686506ce00037821d00007203139b48000000060800000011300010440000001cca2b80000001b8800000061806f964c05200021c9ef4ca65d543b0b6cfea2b11931a4825a2b50e310e800070b0a38000cbe59502f86e0d9c33d2358864efa000000000098800024c80000007be000000106c7a72b299c4c5a3cd42691941787d608a8000eaa000000000090025100000010587e30ac999400000000000000004c60ae0a6400000037ea2e40005632ac00008140000000000a166b33509cf444e0003962050000000024182400000014a8000e2e6f713a000000007f17c13f80006e9320a01c000000454847800000000008104c44b720d800051017f3430b640008a2000140c0005ca42700007e445407813403e200017a8000fde5e223f800000031528919a059c81923c1e187d21d12a195a508e6e51f98bb44ea29000000002d200
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x74250510007b54250510007f3705051000df6705051000df47050510147f07050510026f76050510027f36050510147f23050510147f22050510014ff764c51000cfe764c510104fd764c51000cfc764c5100067f654c51010e7c654c510006df634c510016dc634c510275f7714c510027d4314c510005fb704c51000df8704c51000cfe76c851000cfc76c85100357e75c85100057d75c85100067f65c85100fe7c65c8510006ef62c851003eec62c851000dfa70c8510005f970c85100a5f67688510026f67688510025f7758851026df57588510007776588510267746588510025f77488510005f5748851002df67388510025f473885100bdf5728851003ef6628851003ef46288510267775288510007755288510027f3708851000df6708851000df47088510027f07088510026f76088510027f360885100d7f230885100d7f2208851003cff764851000cfe76485100bcfd764851000cfc76485100067f65485100ce7c6548510005df734851002ddc7348510006ef624851003eec6248510005fb704851000df87048510027f0104851000df4764851003ef4764851000cf4764851025df7754851025df57548510007776548510257746548510005f77448510005f57448510007d7734851002df6734851002df47348510007d4734851002dd47348510025f77248510027e77248510007e7624851003ef6624851003ef46248510007e46248510257775248510007755248510007e63248510007e53248510007f3704851000df6704851000df470485100bff07048510026f76048510027f360485100bff230485100bff22048510025f8764c110016f8764c110024f8764c1100077b654c11024f78654c11000dfb734c11000fdb734c110007db634c110016fa634c110016f8634c11002fd8634c11002fda534c11024fd9534c11002fda434c110007d9434c110005fb724c11024f7b524c11000779524c11002fdb324c110007d9324c110007f3714c110025fa714c110025f8714c110007f0714c11000efb614c11000ff3614c11024ff2514c11024ff1514c110007f2414c110007f1414c11002ff3314c110247da314c110247d8314c11002ff0314c11002fd0314c110007f2214c110007f1214c110025f8764811003ef87648110024f876481100077b654811023f786548110005fb7348110005f9734811000dfb724811000feb7248110007eb624811003efa624811003ef86248110007e8624811023f7b524811023fea524811000779524811023fe95248110007695248110007ea4248110007e94248110007f37148110025fa7148110025f87148110007f0714811000efb614811000ff3614811023ff2514811023ff15148110007f24148110007f14148110237f33148110237f03148110007f22148110007f12148110
  | 1 => 0x49100067f635491020e7e63549100067d635491020e7c63549102ad7f72549100376f72549100067f625491003e7e62549100067d625491003e7c62549100077671549100077571549102067f61549102a77731549102a77431549102067f60549102077a30549102076f20549102077a20549102076d205491029f7b1054910207761054910207741054910207781054910094ff76d0910004fe76d0910004fd76d0910094fc76d09100067f65d09101be7c65d0910096be64d0910006bd64d0910006ef62d091003eec62d0910025f671d0910005f571d091003cff7690910004fe7690910004fd769091003cfc76909100357e75909100057d75909100067f65909101ee7c6590910006bf6490910006bc649091002dde7390910005dd7390910025f67190910005f5719091000dfa7090910005f97090910004ff7650910004fe7650910004fd7650910004fc76509100067f65509101d67c6550910006be6450910006bd645091003cff7610910004fe7610910004fd761091003cfc76109100357e75109100057d75109100067f65109101b67c6510910006bf6410910096bc6410910006ef621091003eec6210910025f67110910005f5711091000dfa7010910005f9701091003cff768c910004fe768c910004fd768c91003cfc768c9100357e758c9100057d758c9100067f658c91019e7c658c910005be748c910005bd748c910006df638c910016dc638c910025f6718c910005f5718c91002fd4318c91000dfa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c91018e7c654c910016de634c910006dd634c910005f7714c910025f4714c91002fd7314c91000dfa704c91000cfe76d051000cfc76d05100357e75d05100057d75d05100067f65d051013e7c65d0510006bf64d0510096bc64d051000dfa70d0510005f970d0510125f67690510026f67690510025f77590510295f5759051000777659051028f746590510145f57490510096f66490510096f4649051002df67390510025f47390510005f5729051028f77529051000775529051000df6709051000df47090510026f76090510027f3609051015ff2309051015ff22090510094ff765051000cfe7650510144fd765051000cfc76505100067f65505101567c6550510006bf6450510006bc6450510005df735051002ddc7350510005fb705051000df8705051000df47650510146f4765051000cf47650510285f77550510285f5755051000777655051027f746550510025f77450510027b77450510007b76450510096f66450510096f46450510007b46450510007d7735051002df6735051002df47350510007d4735051002dd47350510007b74350510007b54350510005f7725051027f775250510007755250510007b
  | 2 => 0x4fd72d8d100067f52d8d1002edc32d8d10024fe71d8d1000cfd71d8d10116f571d8d1000cf571d8d10024fc71d8d1002edf31d8d1002ef731d8d1002ef431d8d10024ff70d8d1000cfe70d8d10024fd70d8d1000cfc70d8d10116df30d8d10116dd30d8d100057f7558d100357c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d1002edc6358d10005ef7258d10005ec7258d10275f77158d1002fd43158d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10094fc7458d10006bc7458d10004bc7458d10114ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1003cfc7258d10006ec7258d1003cec7258d100067f5258d1002edf3258d10274ff7158d10006f77158d1002ef73158d10246de3158d10246dc3158d1002ef43158d10104ff7058d10006fb7058d10094ff76d0d10004fe76d0d10004fd76d0d10094fc76d0d100067f65d0d1022e7c65d0d10006df63d0d10016dc63d0d10025f671d0d10005f571d0d1002fd431d0d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d1021e7c6550d10005f77150d10025f47150d1003cfe76d89100357c75d89100067f65d89100067c65d8910004ff75d89100067f75d891001cfe75d8910004fd75d891001cfc75d89100067c75d891001c7c75d8910094fe74d8910004fd74d8910014fe73d8910004fd73d8910014fc73d89100067f52d8910006ef32d8910006ec32d8910024fe71d8910024fc71d8910024ff70d891000cfe70d8910024fd70d891000cfc70d89100d6ef20d89100d6ed20d89100357e75989100057d75989100067f65989100067c6598910006ef62989100bdf571989100057f75589100357c75589100067f65589100067c6558910005bf7458910005bc7458910005df735891002ddc73589100edf77158910004ff75589100067f75589100047f755891001cfe7558910004fd755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910094fc7458910006bc7458910004bc7458910004ff7358910006df7358910004df7358910014fe7358910014fc7358910006dc7358910014dc7358910006ef72589100067f52589100ecff7158910006f771589100bcff7058910006fb70589100d4fe76189100357e75189100057d75189100067f65189100067c6518910005be7418910005bd741891002dde7318910005dd731891003eee6218910006ed62189100067f76549100057e76549100067e76549100047e76549100067d76549100057c76549100067c76549100047c76549100067f64549100067e64549100067d64549100067c645
  | 3 => 0x610d95102b77410d95102b77810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067f32d95100067c32d95102b67f71d95102be7e71d95102b67d71d95102b67c71d95102be7e41d95102be7c41d95100067f31d95102be7e31d95102be7c31d95102be7e21d95102be7c21d95102b67f70d95102b67e70d95102b67d70d95102b67c70d95102b67f40d95102b67e40d95102b67d40d95102b67c40d95102b67f30d95102b67e30d95102b67d30d95102b67c30d95102b67f20d95102b67e20d95102b67d20d95102b67c20d95102b67f10d95102b67e10d95102b67d10d95102b67c10d95100067f65d91100067c65d9110004ff75d911001cfe75d9110004fd75d911001cfc75d9110014fe73d9110004fd73d9110014fc73d9110006be43d9110006bc43d911003cfe72d9110004fd72d91100067f52d9110024ff70d9110024fd70d911015ebf40d911015ebd40d91100357e75991100057d75991100067f65991100067c6599110006bf6499110145f57199110094ff759911001cfe75991100967e759911001c7e7599110004fd75991100967d75991100047d7599110094fc7599110094fe7499110014fe7399110004fd7399110014fc739911003cfe7299110004fd72991100067f5299110144fd7199110096f57199110174fd7099110096f970991100057f75591100357c75591100067f65591100067c6559110005df735911002ddc7359110005ef7259110005ec7259110175f77159110004ff75591100067f75591100047f755911001cfe7559110004fd755911001cfc75591100067c755911001c7c7559110006bf7459110004ff7359110006df7359110004df7359110014fe7359110014fc7359110006dc7359110014dc7359110004ff7259110006ef7259110004ef725911003cfc7259110006ec725911003cec72591100067f5259110174ff7159110006f77159110144ff7059110006fb705911015cfe76191100067f65191100067c6519110006bd6419110094ff751911001cfe7519110004fd7519110094fc7519110096be7419110014fe7319110004fd7319110014fc7319110006be4319110096bc431911003cfe7219110004fd72191100067f5219110024fe7119110096f57119110024fc7119110024ff701911000cfe7019110024fd701911000cfc7019110096bf4019110126bd4019110014fe76d8d100067f65d8d100067c65d8d1002ede63d8d10025f671d8d1000df571d8d1002fd731d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10094fe74d8d10004fd74d8d1002edc43d8d1003cfe72d8d10
  | 4 => 0xf10024fe7650f10004fd7650f10024fc7650f10006be6450f10006bd6450f10005f77150f10025f47150f10004ff7558b1001cfe7558b10004fd7558b1001cfc7558b10004ff7458b10094fc7458b10004ff7358b10014fe7358b10014fc7358b10026ef7258b100067f5258b10024ff7158b1000cfe7158b10024fd7158b1000cfc7158b10026ee2158b10026ec2158b100beef2058b100beed2058b10026fa1058b10026f91058b100067f7654b1029e7e7654b100067d7654b1029e7c7654b1029e7f6454b100067e6454b100067d6454b1029e7c6454b1029e7f6354b1020e7e6354b100067d6354b1029e7c6354b102ad7f7254b1004f6f7254b1029e7f6254b1003e7e6254b100067d6254b1003e7c6254b1029f767154b10007757154b102067e6154b1029f764154b102f7773154b1029f743154b1029f762154b102067d6054b102076f2054b102076d2054b10207761054b102077a1054b10207741054b10094ff76d0b10024fe76d0b10004fd76d0b10024fc76d0b10096be64d0b10006bd64d0b10025f671d0b10005f571d0b1003cff7690b10024fe7690b10004fd7690b10024fc7690b1004d7e7590b100057d7590b10045de7390b10005dd7390b10025f67190b10005f57190b10004ff7650b10024fe7650b10004fd7650b10024fc7650b10006be6450b10006bd6450b10025f67150b1003cff7610b10024fe7610b10004fd7610b10024fc7610b1004d7e7510b100057d7510b10025f67110b10005f57110b1003cff768cb10024fe768cb10004fd768cb10024fc768cb1004d7e758cb100057d758cb10005be748cb10005bd748cb1003eee628cb10006ed628cb10025f6718cb10005f5718cb102efd4318cb10004ff764cb10024fe764cb10004fd764cb10024fc764cb10016de634cb10006dd634cb1003eee624cb10006ed624cb10005f7714cb10025f4714cb10047d7314cb10025f77650710006f776507102e5f775507102e5f57550710027b77450710096f66450710026f46450710007d77350710045f67350710045f47350710007d47350710045d47350710007b74350710007b54350710005f772507102df775250710007755250710007b74250710007b5425071000df6705071000df47050710025f77648710006f776487102d5f775487102d5f57548710005f77448710005f57448710007d77348710045f67348710045f47348710007d47348710045d47348710027e7724871003ef66248710026f462487102cf775248710007755248710007e63248710007e5324871000df6704871000df470487102c57e76d95100367e76d951001c7e76d95100067e63d95100067c63d95100057d72d95102b77771d95102b77471d95100077731d95100077431d95102b77a30d95102b77a20d95102bf7b10d95102b77
  | 5 => 0x24fe76d85200076d52d8520004ff75d852001cfe75d8520004fd75d852001cfc75d8520094fe74d8520004fd74d8520014fe73d8520004fd73d8520014fc73d85200067f52d85200067d52d852000cfe70d852003cfd70d852000cfc70d85200eef710d85200076d5298520006f761985200057f755852005d7c7558520005bf7458520005bc7458520005df7358520055dc73585200076d52585200076d5218520026f66118520006f56118520004fe76d0520004fd76d0520094fc76d052005d7e75d05200057d75d052003dee72d0520005ed72d05200076d52d0520007ad42d0520004fe7690520004fd7690520024fc7690520006bf6490520006bc64905200076d529052000dfa7090520005f97090520004ff7650520004fe7650520004fc7650520005df7350520055dc73505200076d5250520007ad4250520004fe7610520004fd7610520024fc7610520006bf6410520096bc641052003dee7210520005ed72105200076d521052000dfa7010520005f97010520004fe768c520004fd768c520024fc768c520006df638c520016dc638c5200076d528c52000dfa708c520005f9708c520004ff764c520004fe764c520004fc764c5200076d524c52000cfe76885200076d5288520006f76188520026f4618852000dfa7088520005f9708852000cfc7648520005df7348520055dc73485200076d5248520006f76148520026f46148520005fb704852000df87048520094ff759931001cfe75993100967e759931001c7e7599310004fd75993100967d75993100047d7599310094fc7599310026be7499310006bf5499310096bc5499310014fe7399310004fd7399310014fc739931003cfe7299310004fd72993100067f529931000cfe7199310026f6719931000cf6719931000cfc7199310026be4199310026f64199310026bc4199310096bf4099310176bd4099310004ff755931001cfe7559310004fd755931001cfc7559310026bf7459310006bf5459310006bc5459310004ff7359310014fe7359310014fc7359310004ff725931003cfc72593100067f5259310024ff715931000cfe7159310024fd715931000cfc7159310026be4159310026bc4159310146bf4059310146bd4059310004ff7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f10094fc7458f10026df7358f10004ff7258f1003cfc7258f100067f5258f10046df3258f10024ff7158f1000cfe7158f10024fd7158f1000cfc7158f10026f47158f1000cf47158f10046f73158f10026de3158f10026dc3158f10026f43158f10106df3058f10106dd3058f10026fa1058f10026f91058f10094ff76d0f10024fe76d0f10004fd76d0f10024fc76d0f10096be64d0f10006bd64d0f10025f671d0f10005f571d0f102ffd431d0f10004ff765
  | 6 => 0xf7358d2032cff7258d20006ef7258d200067f5258d20004ff7158d20024fc7158d20184ff7058d20006fb7058d20186fa1058d20094ff76d0d20004fe76d0d20004fd76d0d20094fc76d0d20006bf64d0d20096bc64d0d2003dee72d0d20005ed72d0d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20006bf6450d20006bc6450d2001e7f76549202067e76549202067d765492001e7c76549200067f64549200067e64549200067d64549200067c64549200067f635492020e7e63549200067d635492020e7c635492003d7f725492005f6f725492003e7f625492003f6e425492003f6c42549203276f325492003f6e325492003f6c325492029e7c615492003f6f215492003f6c21549200077b705492020778705492003e7f605492003f7b20549202076e205492003f6c205492003f7820549202077a105492005f6f765492001e6f76549202076c765492001e6c76549200076f74549200076e74549200076d74549200076c74549200076f64549200076e64549200076d64549200076c64549200076f73549203276e73549200076d73549203276c73549200076f63549203276e63549200076d63549203276c63549200076f43549203276e43549200076d43549203276c43549200076f71549200076e71549200076d71549200076c71549203276f31549203276c31549202076f70549200076b70549202076e70549202076d70549202076c705492020768705492003f6f605492003e6f605492003f6b60549202076f40549202076e40549202076d40549202076c40549202076f30549202076e30549202076d30549202076c30549202076e10549202076a10549202076c105492000cfe76d092000cfc76d0920006bf64d0920096bc64d09200076d52d092000dfa70d0920005f970d09201a5ee769092003eee769092003def759092003f6e759092031ded759092003f6d75909200056d75909201c5ed7490920096ee6490920096ec649092003fce739092003fcd739092000dee709092000dec709092003eef609092003feb60909201dfea1090920094ff765092000cfe76509201c4fd765092000cfc7650920006bf6450920006bc64509203176f52509200076d525092003fac4250920005fb705092000df8705092000dec76509201c6ec765092000cec765092030def755092030ded755092003def745092003faf7450920007af6450920096ee6450920096ec6450920007ac6450920307ae4350920307ac4350920007eb705092000dee705092000dec70509201c7e8705092003eef605092003feb60509201c7af40509201c7ad40509201c7ea1050920014ff764c92000cfe764c920184fd764c92000cfc764c920006df634c920016dc634c9200076d524c920005fb704c92000df8704c92003fe8204c920
  | 7 => 0x872003efa205872003ef920587200bef71058720094ff76d072003cfe76d0720004fd76d072006d7e75d07200057d75d072013e7e65d07200067d65d0720096be64d0720006bd64d072003dee72d0720005ed72d07200076d52d0720007ad42d0720024ff769072003cfe7690720004fd769072016e7e65907200067d65907200076d5290720004ff7650720004fd765072003cfc76507201567e65507200067d6550720006be6450720006bd6450720005df7350720065dc73507200076d5250720007ad4250720024ff761072003cfe7610720004fd76107201367e65107200067d651072003dee7210720005ed72107200076d5210720024ff768c72003cfe768c720004fd768c72011e7e658c7200067d658c720336df638c720016dc638c7200076d528c720004ff764c720004fd764c72003cfc764c72010e7e654c7200067d654c720016de634c720006dd634c7200076d524c720004ff75d912001cfe75d9120004fd75d912001cfc75d9120006bf54d9120006bc54d9120014fe73d9120004fd73d9120014fc73d91200067f52d9120024fe71d9120004fd71d912003cff70d912003cfd70d91201debf40d91201debd40d9120006bf64991201c5ed7299120094ff759912001cfe7599120004fd7599120094fc7599120094fe7499120014fe7399120004fd7399120014fc73991201c4fd7299120096ed72991200067f5299120024fe7199120004fd71991201f4fd7099120096f970991200057f755912005d7c75591201f5ef7259120004ff75591200067f75591200047f755912001cfe7559120004fd755912001cfc75591200067c755912001c7c7559120006bf7459120004ff7359120014fe7359120014fc73591201f4ff7259120006ef72591200067f5259120004ff7159120024fc71591201c4ff7059120006fb70591201dcfe761912005d7e75191200057d7519120006bd6419120094ff751912001cfe75191200967e751912001c7e7519120004fd75191200967d75191200047d7519120094fc7519120096be7419120006bf5419120096bc5419120014fe7319120004fd7319120014fc731912003cfe7219120096ed721912003cfc72191200067f5219120024fe7119120004fd711912003cff701912003cfd7019120096bf40191201a6bd4019120014fe76d8d20056de63d8d20004ff75d8d2001cfe75d8d20004fd75d8d2001cfc75d8d20094fe74d8d20004fd74d8d2003cfe72d8d2000cfd72d8d2003cfc72d8d200067f52d8d20056df32d8d20024fe71d8d20004fd71d8d20056dc31d8d2003cff70d8d2003cfd70d8d20196df30d8d20196dd30d8d20196fa10d8d20056dc6358d2032def7258d20004ff7558d2001cfe7558d20004fd7558d2001cfc7558d20004ff7458d20094fc7458d20194ff7358d20006d
  | 8 => 0x3e7c20597202067f10597202067e10597202067d10597202067c1059720094ff759932001cfe7599320004fd7599320094fc759932003ebe7499320014fe7399320004fd7399320014fc7399320006be4399320096bc439932000cfe729932003eee729932000cee729932000cfc729932003e7f529932003e7d529932003ebe429932003eee429932003ebc4299320024fe7199320004fd7199320096bf40993201f6bd4099320004ff755932001cfe7559320004fd755932001cfc755932003ebf7459320004ff7359320014fe7359320014fc7359320006be4359320006bc435932003cff725932000cfe725932003cfd725932000cfc725932003e7f525932003e7d525932003ebe425932003ebc4259320004ff7159320024fc71593201c6bf40593201c6bd4059320004ff7558f2001cfe7558f20004fd7558f2001cfc7558f20004ff7458f20094fc7458f2003edf7358f20066dc4358f2003cff7258f2000cfe7258f2003cfd7258f2000cfc7258f2003e7f5258f2003e7d5258f2003ede3258f2003edc3258f20004ff7158f20024fc7158f20066df3158f20186df3058f20186dd3058f20094ff76d0f2003cfe76d0f20004fd76d0f2003cfc76d0f2022e7e65d0f200067d65d0f20016de63d0f20006dd63d0f2003dee72d0f20005ed72d0f20004ff7650f2003cfe7650f20004fd7650f2003cfc7650f2021e7e6550f200067d6550f2003f6f7654b2003d6f7654b203566f7654b200076f7454b200076e7454b200076d7454b200076c7454b2003f6f6454b2003f6e6454b2003f6d6454b2003f6c6454b200076f7354b2034f6e7354b200076d7354b2034f6c7354b2003f6f6354b2003f6e6354b2003f6d6354b2003f6c6354b200076f4354b2034f6e4354b200076d4354b2034f6c4354b200076f7154b200076e7154b200076d7154b200076c7154b2003f6f6154b2003f6e6154b2003f6d6154b2003f6c6154b2034f6f3154b2034f6c3154b202076f7054b202076e7054b202076d7054b202076c7054b202066d6054b202076f4054b202076e4054b202076d4054b202076c4054b202076f3054b202076e3054b202076d3054b202076c3054b202076e1054b202076c1054b2003def7650b20006ef7650b20345ef7550b20345ed7550b2003f6e6550b2003f6d6550b2003faf7450b2003faf6450b20096ee6450b2003eec6450b2003fac6450b2033fae4350b2033fac4350b2000dee7050b2000dec7050b201c7af4050b201c7ad4050b20004ff755872001cfe7558720004fd755872001cfc7558720004ff7458720094fc7458720004ff7358720006df7358720004df7358720014fe7358720014fc7358720006dc7358720014dc735872000cfc725872003e7f525872003e7d525872003ef7715872003ef7215872003ef4215
  | 9 => 0xd75d853001cfc75d8530094fe74d8530004fd74d853000cfd73d8530276dd73d853003cfe72d8530004fd72d85300067f52d85300067d52d853036edf32d8530006dd32d853036ef631d853036ef531d8530246dc31d8530014fd70d8530276f710d8530006f76198530247d4319853002df970985300057f75585300757c7558530005bf7458530005bc7458530005ef7258530005ec725853002fd43158530045fb7058530026f66118530006f56118530004fe76d0530004fd76d0530094fc76d05300757e75d05300057d75d0530015de73d0530005dd73d05300079d43d0530004fe7690530004fd7690530024fc7690530006bf6490530006bc6490530015dc739053000dfa7090530005f97090530004ff7650530004fe7650530004fc7650530005df7350530015dc73505300079d4350530004fe7610530004fd7610530024fc7610530006bf6410530096bc6410530015de7310530005dd731053000dfa7010530005f9701053000dde768c530116de768c53000cde768c530245df758c530365dd758c530245df748c530005dd748c530006de648c530006dc648c530005dd728c530336dc628c53035f5f528c5300075d528c530015de718c530017d6718c530246df618c530007d7618c530247d4618c53000dde708c530117da708c530247d9708c53000ddc708c530016df608c530017db608c530117da108c530004fe76c8530004fd76c853003cfc76c85300757e75c85300057d75c8530015de73c8530005dd73c8530007cd32c8530004fe7688530004fd7688530024fc7688530245df7388530015dc7388530006ef628853003eec628853000dfa7088530005f97088530004ff7648530004fe7648530004fc7648530005df7348530015dc7348530007cd3248530004fe7608530004fd7608530024fc76085300757e75085300057d7508530005be7408530005bd7408530015de7308530005dd7308530006ef620853003eec620853000dfa7008530005f970085300067f74597200067e74597200067d74597200067c74597200067f73597200067e73597200067d73597200067c73597200067e43597200067c435972003e7f725972003c7f725972003e7e725972003e7d725972003c7d725972003e7c725972003e7f425972003e7e425972003e7d425972003e7c425972003e7f325972003e7e325972003e7d325972003e7c32597200067f71597200067e71597200067d71597200067c71597200067f31597200067c315972003e7f215972003e7e215972003e7d215972003e7c21597202067f70597202067e70597202067d70597202067c70597202067f40597202067e40597202067d40597202067c40597202067f30597202067e30597202067d30597202067c305972003e7f205972003e7e205972003e7d2059720
  | 10 => 0x91303acfe76191300757e75191300057d7519130006bd6419130094ff751913001cfe75191300967e751913001c7e7519130004fd75191300967d75191300047d7519130094fc7519130094fe7419130096be7419130006bf5419130096bc541913000cff7319130014fe731913000cfd7319130096dd7319130014fc7319130096bf4319130096de43191303a6bd431913003cfe7219130004fd72191300067f52191303a6df3219130024fe7119130004fd71191303a6dc3119130014ff7019130014fd7019130096bf401913039ebd401913000ddc7650d30216dc7650d3000cdc7650d30395df7550d30395dd7550d30015df7450d300179f7450d300079f6450d30096de6450d30096dc6450d300079c6450d30005df7250d3038f5f5250d30245dc7150d30007db7050d3000dde7050d3000ddc7050d30217d87050d30016df6050d30017db6050d30217da1050d3003cfe76d8930004ff75d893001cfe75d8930004fd75d893001cfc75d8930094fe74d8930004fd74d893000cfd73d89300067f52d8930386ee32d8930386ed32d8930024fe71d8930004fd71d8930014fd70d893032eef20d893032efa10d89300757e75989300057d7598930005be7498930005bd7498930006ef6298930055f97098930065fb70589300757e75189300057d751893003eee6218930006ed62189300067f76549300067e76549300067d76549300067c76549300067f64549300067e64549300067d64549300067c645493020f5e73549300075d73549302067f635493020f5e43549300075d43549302ad7f72549300776f72549300067f625493003e7e625493003e7c625493020f5f325493029e7c615493020f5c31549302067f605493020f7b30549302075e30549302075c30549302077830549302077a1054930004fe76d0930004fd76d0930094fc76d0930006bf64d0930096bc64d0930015de73d0930005dd73d09301ff9e43d0930004fe7690930004fd769093003cfc76909300757e75909300057d7590930015de7390930005dd7390930004ff7650930004fe7650930004fc7650930006bf6450930006bc6450930015de73509301cf9e4350930004fe7610930004fd761093003cfc76109300757e75109300057d7510930015de7310930005dd731093000dfa7010930005f9701093000ddc764c93003edc764c93000cdc764c93037ddf754c93037ddd754c930005df744c930005dd744c930006de644c930006dc644c930015df724c930017cf724c930007cf624c93003ede624c93003edc624c930007cc624c93003ecc624c9303775f524c9300075d524c930245dc714c930007db704c93000dde704c93000ddc704c930187d8704c930016df604c930017db604c930187da104c930024fe76d8530004ff75d853001cfe75d8530004f
  | 11 => 0x176f710d85400857e75985400057d75985400067f65985400067c6598540006f761985400057f75585400857c75585400067f65585400067c6558540005df735854007ddc7358540005ef7258540005ec72585400067f65185400067c6518540026f66118540006f56118540124fe76d05400857e75d05400057d75d05400067f65d054013e7c65d0540097b840d054000cfe76905400067f659054016e7c6590540006f76190540026f4619054000dfa7090540005f9709054000cfc76505400067f65505401567c6550540005df735054007ddc7350540006f76150540026f46150540005fb705054000df87050540147b84050540174fe76105400067f65105401367c6510540004fe768c540004fd768c540024fc768c5400067f658c54011e7c658c540006df638c540016dc638c540004ff764c540004fe764c540004fc764c5400067f654c54010e7c654c540004fe76c8540004fd76c854003cfc76c85400857e75c85400057d75c85400067f65c85400fe7c65c8540005be74c8540005bd74c8540004fe7688540004fd7688540024fc76885400067f65885400e67c6588540006ef628854003eec6288540004ff7648540004fe7648540004fc76485400067f65485400ce7c6548540005df734854007ddc7348540004fe7608540004fd7608540024fc76085400857e75085400057d75085400067f65085400b67c6508540005be7408540005bd740854007dde7308540005dd7308540006ef620854003eec620854000dfa7008540005f9700854000dfa76d014000efa76d014000cfa76d01400077b65d01403bf7865d014000dfa74d014000fba74d014000efb64d014000fbb64d0140097ba54d01403bfb954d01403bf7b52d01400077952d0140097bb42d0140007b942d0140004ff75d913001cfe75d9130004fd75d913001cfc75d9130006bf54d9130006bc54d913000cff73d913000cfd73d91303b6bf43d91303b6bd43d913003cfe72d9130004fd72d91300067f52d9130024fe71d9130004fd71d9130014ff70d9130014fd70d91303aebf40d91303aebd40d9130214fd7699130006bf6499130215dd739913007df97099130094ff759913001cfe7599130004fd7599130094fc7599130094fe7499130214fd7399130096dd7399130096de439913003cfe7299130004fd72991300067f529913008edf3299130024fe7199130004fd719913008edc3199130224fd7099130096f970991300057f75591300757c7559130225df735913008dfb7059130004ff75591300067f75591300047f755913001cfe7559130004fd755913001cfc75591300067c755913001c7c7559130006bf7459130224ff7359130006df7359130004ff725913003cfc72591300067f5259130004ff7159130024fc7159130214ff7059130006fb705
  | 12 => 0xf65d0d4022e7c65d0d40097b840d0d4000cfc7650d400067f6550d4021e7c6550d40006df6350d40016dc6350d40005fb7050d4000df87050d40217b84050d4003cfe76d89400857c75d89400067f65d89400067c65d8940004ff75d89400067f75d894001cfe75d8940004fd75d894001cfc75d89400067c75d894001c7c75d8940014fe73d8940004fd73d8940014fc73d89400067f52d8940024fe71d8940004fd71d89401f6ef20d89400857e75989400057d75989400067f65989400067c659894007dde7398940005dd7398940006ef62989400057f75589400857c75589400067f65589400067c65589400857e75189400057d75189400067f65189400067c651894003eee6218940006ed62189400067f76549400057e76549400067e76549400047e76549400067d76549400057c76549400067c76549400047c76549400073e74549400073d74549402067f64549400067f635494020e7e635494020e7c63549402ad7f72549400876f72549400067f625494003e7e625494003e7c625494029e7c61549402067f60549402073e40549402073c40549402077840549401a4fe76d09400067f65d09401be7c65d09401a5be76d0940006be76d09403ddbf75d09403ddbd75d09400073f65d09403d73c65d09401febe63d09401febc63d094003ebe62d094003ebc62d09403d73f52d09400073d52d094000dbe70d094000dbc70d0940096bf60d094000cfe76909400857e75909400057d75909400067f65909401ee7c65909401c5bd749094007dde7390940005dd7390940006ef629094003eec629094000dfa7090940005f9709094000cfc76509400067f65509401d67c6550940006ef625094003eec6250940005fb705094000df8705094000dbc765094003ebc765094000cbc76509403cdbf75509403cdbd75509400073f65509403c73c65509401cebe63509401cebc6350940007af7250940007af625094003ebe625094003ebc6250940007ac62509403c73f52509400073d5250940007bb705094000dbe705094000dbc70509401c7b870509401c6bf60509401f4fe76109400857e75109400057d75109400067f65109401b67c65109401f5be7410940007ad4210940004fe768c940004fd768c94003cfc768c9400857e758c9400057d758c9400067f658c94019e7c658c940005be748c940005bd748c940006ef628c94003eec628c940004ff764c940004fe764c940004fc764c9400067f654c94018e7c654c940006df634c940016dc634c940006ef624c94003eec624c940024fe76d85400067f65d85400067c65d8540004ff75d854001cfe75d8540004fd75d854001cfc75d8540014fe73d8540004fd73d8540014fc73d854003cfe72d8540004fd72d85400067f52d85400067d52d8540006bf42d8540006bd42d8540
  | 13 => 0xb401ddbf7650b40006bf7650b403fdbf7550b403fdbd7550b401cebe6350b401cebc6350b40097af7250b40097af6250b4003ebe6250b4003ebc6250b40097ac6250b403f73f5250b400073d5250b4000dbe7050b4000dbc7050b4003cff768cb40094fe768cb40004fd768cb4009d7e758cb400057d758cb40095be748cb40005bd748cb40004ff764cb40004fd764cb40094fc764cb40016dc634cb40096f76198740026f46198740024ff7658740005df735874008ddc7358740096f46158740004ff755874001cfe7558740004fd755874001cfc755874000cfc7458740004ff7358740006df7358740004df7358740014fe7358740014fc7358740006dc7358740014dc7358740004ff725874003cfc72587400067f52587400067d5258740006bf4258740006bd4258740096f74158740096f44158740146f71058740144fd7690740026f4619074015cff7650740005df735074008ddc7350740024ff768c740094fe768c740004fd768c740016dc638c740004ff764c740004fd764c740094fc764c74003cff76c8740094fe76c8740004fd76c874009d7e75c87400057d75c8740095be74c8740005bd74c8740024ff7688740094fe7688740004fd7688740004ff7648740004fd7648740094fc7648740005df734874008ddc7348740024ff7608740094fe7608740004fd760874009d7e75087400057d7508740095be7408740005bd740874008dde7308740005dd730874000dfa7008740005f970087403ed7e76d95400867e76d954001c7e76d95403e73f74d95403e73c74d95400067e63d95400067c63d95400057d72d95403e73e40d95403e73c40d95403e77840d95403e67f74d95400867e74d95403e67d74d95403e67c74d95400067f73d95400067e73d95400067d73d95400067c73d95400067e43d95400067c43d95400067f72d95400067e72d95400067d72d95400047d72d95400067c72d95400067f32d95400067c32d95400067f71d95400067e71d95400067d71d95400067c71d95400067f31d95400067c31d95403e67f70d95403e67e70d95403e67d70d95403e67c70d95403e67f40d95403e67e40d95403e67d40d95403e67c40d95403e67f30d95403e67e30d95403e67d30d95403e67c30d95403e67f20d95403e67e20d95403e67d20d95403e67c20d95403e67f10d95403e67e10d95403e67d10d95403e67c10d9540014fe76d8d400067f65d8d400067c65d8d4007ede63d8d40004ff75d8d4001cfe75d8d40004fd75d8d4001cfc75d8d4000cfd74d8d40014fc74d8d4007ede43d8d4003cfe72d8d40004fd72d8d400067f52d8d4007edf32d8d40024fe71d8d40004fd71d8d4007edc31d8d40226df30d8d400057f7558d400857c7558d400067f6558d400067c6558d4007edc6358d4039cfe76d0d400067
  | 14 => 0x14fc735802100cfd725802103e7f525802103e7d525802100cfd7158021026f6215802103ef52158021024ff7058021026fb7058021006fb50580210a6fa5058021006f950580210a6f850580210a6fa40580210a6f84058021006fb30580210a6fa30580210a6f8305802103efb205802103ef82058021026fb1058021026f81058021006fb7558021006fa7558021006f97558021006f87558021006fb7458021006fa7458021006f97458021006f87458021006fb5458021006fa5458021006f95458021006f85458021006fb7358021006fa7358021006f97358021006f87358021006fb5358021006fa5358021006f95358021006f85358021006fb4358021006fa4358021006f94358021006f8435802103efb725802103efa725802103ef8725802103efb525802103e7b525802103efa525802103ef9525802103e79525802103ef8525802103efb425802103efa425802103ef9425802103ef8425802103efb325802103efa325802103ef9325802103ef83258021026fb7158021026fa7158021026f87158021026fb5158021026fa5158021026f95158021026f85158021026fb4158021026fa4158021026f94158021026f84158021026fb3158021026fa3158021026f93158021026f83158021026fb2158021026fa2158021026f22158021026f9215802103ef12158021026f82158021014ff7658f40096dc6358f40004ff7558f4001cfe7558f40004fd7558f4001cfc7558f40014fd7458f4000cfc7458f40096df4358f40096dc4358f40004ff7258f4003cfc7258f400067f5258f40004ff7158f40024fc7158f40216df3058f403acff7650f40016dc6350f4009d7e7598b400057d7598b4008dde7398b40005dd7398b40096ef6298b4003eec6298b4003cff7658b40096ec6258b40004ff7558b4001cfe7558b40004fd7558b4001cfc7558b4000cfc7458b40004ff7358b40014fe7358b40014fc7358b400067f5258b40096ef4258b40096ec4258b40004ff7158b40024fc7158b401c6ef2058b400067f7654b400067e7654b400067d7654b400067c7654b400073e7454b400073d7454b402067e6454b4020e7e6354b400067d6354b4020e7c6354b402ad7f7254b4009f6f7254b4003e7e6254b400067d6254b4003e7c6254b4029e7e6154b400077b7054b40207787054b402067d6054b402073e4054b402077a4054b402073c4054b4000dbd76d0b4003ebd76d0b4000cbd76d0b40095bf75d0b4040dbd75d0b401febe63d0b40096bc63d0b4003ebe62d0b40097ae62d0b40097ad62d0b4003ebc62d0b404073f52d0b400073d52d0b4000dbe70d0b40097ba70d0b40097b970d0b4000dbc70d0b401c4fd7690b4009d7e7590b400057d7590b4008dde7390b40005dd7390b4003eec6290b401dcff7650b40097ac425
  | 15 => 0xe525902103ebd525902103e3d525902103ebc525902103ebf325902103ebe325902103ebd325902103ebc3259021026bf7159021026be7159021026bd7159021026bc7159021026bf5159021026be5159021026bd5159021026bc5159021026bf3159021026be3159021026bd3159021026bc3159021026bf2159021026be2159021026bd2159021026bc2159021006bf7059021006be7059021006bd7059021006bc7059021006bf5059021006be5059021006bd5059021006bc5059021006bf3059021006be3059021006bc305902103ebf205902103ebe205902103ebd205902103ebc2059021026bf1059021026be1059021026bd1059021026bc1059021004ff7558c2101cfe7558c21004fd7558c2101cfc7558c21004ff7458c21094fc7458c21024ff7358c21026df7358c21006df5358c210aede5358c21006dd5358c210aedc5358c210aede4358c210aedc4358c2103cfe7258c2103cfc7258c2103e7f5258c2103e7d5258c2103ede3258c2103edc3258c21024fe7158c21024fc7158c21026de3158c21026dc3158c21026ef2158c21026ed2158c21004ff7058c2100cfe7058c2100cfc7058c210aedf3058c21006de3058c210aedc3058c21006df7558c21006de7558c21006dd7558c21006dc7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c21006de5458c21006dd5458c21006dc5458c2103edf7258c2103ede7258c2103edd7258c2103edc7258c2103edf5258c2103e5f5258c2103ede5258c2103edd5258c2103e5d5258c2103edc5258c2103edf4258c2103ede4258c2103edd4258c2103edc4258c21026df7158c21026de7158c21026dd7158c21026dc7158c21026df5158c21026de5158c21026dd5158c21026dc5158c21026df4158c21026de4158c21026dd4158c21026dc4158c21026df2158c21026cf2158c21026de2158c21026dd2158c21026cd2158c21026dc2158c21006df7058c21006de7058c21006dd7058c21006dc7058c21006df5058c21006de5058c21006dd5058c21006dc5058c21006de4058c21006dc4058c2103edf2058c2103ede2058c2103edd2058c2103edc2058c21026df1058c21026de1058c21026dd1058c21026dc1058c21094ff76d0c21024fe76d0c21004fd76d0c21024fc76d0c2122e7e65d0c210067d65d0c21096be64d0c21006bd64d0c21016de63d0c21006dd63d0c2103dee72d0c21005ed72d0c21226fa60d0c21004ff7650c21024fe7650c21004fd7650c21024fc7650c2121e7e6550c210067d6550c21006be6450c21006bd6450c21016de6350c21006dd6350c21005f77150c21025f47150c21216fa6050c21004ff755802101cfe7558021004fd755802101cfc7558021004ff7458021094fc7458021004ff7358021014fe7358021
  | 16 => 0x94210267d71594210267c71594210267f41594210267e41594210267d41594210267c41594210267f31594210267e31594210267d31594210267c31594210267f21594210267e21594210267d21594210267c21594210067f70594210067e70594210067d70594210067c70594210067e40594210067c40594210067f30594210067e30594210067c305942103e7f205942103e7e205942103e7d205942103e7c20594210267f10594210267e10594210267d10594210267c1059421094ff759902101cfe7599021004fd7599021094fc7599021024fe7499021026be7499021006bf5499021096be5499021006bd5499021096bc5499021014fe7399021004fd7399021014fc7399021006be4399021096bc439902103cfe729902103cfc729902103e7f529902103e7d529902103ebe429902103ebc4299021024fe7199021024fc7199021026be4199021026bc419902100cfe7099021004fd709902100cfc7099021006be4099021096bc4099021096bf7599021006be7599021006bd7599021096bc7599021096bf7399021006be7399021006bd7399021096bc7399021006bf5399021006be5399021006bd5399021006bc539902103ebf729902103ebe729902103ebd729902103ebc729902103ebf529902103e3f529902103ebe529902103ebd529902103e3d529902103ebc529902103ebf329902103ebe329902103ebd329902103ebc3299021026bf7199021026be7199021026bd7199021026bc7199021026bf5199021026be5199021026bd5199021026bc5199021026bf3199021026be3199021026bd3199021026bc3199021026bf2199021026be2199021026bd2199021026bc2199021096bf7099021006be7099021006bd7099021096bc7099021006bf5099021006be5099021006bd5099021006bc5099021006bf3099021006be3099021006bc309902103ebf209902103ebe209902103ebd209902103ebc2099021026bf1099021026be1099021026bd1099021026bc1099021004ff755902101cfe7559021004fd755902101cfc7559021024ff7459021026bf7459021006bf5459021006be5459021006bd5459021006bc5459021004ff7359021014fe7359021014fc7359021006be4359021006bc435902103cfe725902103cfc725902103e7f525902103e7d525902103ebe425902103ebc4259021024fe7159021024fc7159021026be4159021026bc4159021004ff705902100cfe705902100cfc7059021006be4059021006bc4059021006bf7559021006be7559021006bd7559021006bc7559021006bf7359021006be7359021006bd7359021006bc7359021006bf5359021006be5359021006bd5359021006bc535902103ebf725902103ebe725902103ebd725902103ebc725902103ebf525902103e3f525902103eb
  | 17 => 0x67e64549210067d64549210067c64549210067f63549210075f63549210065f635492120e7e63549210067d635492120e7c63549210075c635492120e5c635492103d7f72549210cf6f725492103e7f625492103f6e425492103f6e325492100777715492100774715492103e7f615492103f77215492129f6e215492103f6c215492103f74215492103f6421549212067e60549212067c605492103f6f2054921024fe76d0921006bf64d0921096bc64d0921006df63d09211fedc63d0921025f671d0921005f571d0921024fc7650921006bf6450921006bc6450921006df63509211cedc63509210076d5250921005f77150921025f4715092103fe42150921005ee768c92103eee768c92103f6e758c92103f6d758c92103fae748c92103fad748c9210c5ed738c921007cf638c921016ee638c921016ec638c9210c7cc638c921016cc638c921025ee718c921025ec718c92103eef618c92103fe7618c9212efce318c9212efcc318c921024fc764c921006df634c921016dc634c9214176f524c9210076d524c92103fcc324c921005f7714c921025f4714c921025ec764c921016ec764c921024ec764c92103def734c92103fcf734c921007cf634c921016ee634c921016ec634c9210c7cc634c921007cf434c9210c7cc434c921007e7714c921025ee714c921025ec714c921007e4714c92103eef614c92103fe7614c9210c7cf314c9210c7cf304c92103cfe76d05210cd7e75d05210057d75d0521006bf64d0521096bc64d0521006df63d052117edc63d052103dee72d0521005ed72d0521094ff7650521004fd765052103cfc7650521006bf6450521006bc6450521005df73505210c5dc7350521006df635052114edc6350521005ef725052103dec7250521027e42150521014ff764c5210c4fd764c52103cfc764c521006df634c521016dc634c521005ef724c52103dec724c521007cd324c52100cfe76d8121006df63d8121006dc63d81210befa60d8121004ff75d812101cfe75d8121004fd75d812101cfc75d8121094fe74d8121004fd74d8121014fe73d8121004fd73d8121014fc73d8121024fd72d812100cfc72d81210067f52d81210067d52d812103cfd71d812100cfc71d81210befa20d81210befa10d81210057f75581210cd7c7558121005bf7458121005bc7458121005df73581210c5dc7358121006df6358121006dc63581210bef860581210067f74594210067e74594210067d74594210067c74594210067f73594210067e73594210067d73594210067c73594210067e43594210067c435942103e7f725942103e7e725942103e7d725942103e7c725942103e7f425942103e7e425942103e7d425942103e7c425942103e7f325942103e7e325942103e7d325942103e7c32594210267f71594210267e715
  | 18 => 0xc7059121004fe7619121006bd6419121094ff751912101cfe7519121004fd7519121094fc7519121096be7419121096be5419121006bd5419121014fe7319121004fd7319121014fc73191210067f521912100cfe7019121004fd701912100cfc7019121006be4019121096bc4019121014fe76d8d210c6de63d8d21004ff75d8d2101cfe75d8d21004fd75d8d2101cfc75d8d21094fe74d8d21004fd74d8d21006df53d8d210c6de53d8d21006dd53d8d210c6dc53d8d210c6de43d8d210c6dc43d8d21024fd72d8d210067f52d8d210c6df32d8d2103cfd71d8d210c6df31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d210c6df30d8d21006de30d8d210c6dc30d8d210c5de76d8d21014de76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d212efcf72d8d210075f52d8d21337d721d8d212efce21d8d212efcc21d8d21337d421d8d21006de60d8d21006dc60d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d212eedf72d8d21336de72d8d21006dd72d8d21336dc72d8d21006df52d8d210065f52d8d21336de52d8d21006dd52d8d21336dc52d8d21336de42d8d21336dc42d8d21336df71d8d212eede71d8d21006dd71d8d212eedc71d8d21006df51d8d212eede51d8d21006dd51d8d212eedc51d8d212eede41d8d212eedc41d8d21336df21d8d212eede21d8d212eedc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006de40d8d21006dc40d8d21336df20d8d21006de20d8d21336dc20d8d212eedf10d8d21006de10d8d212eedc10d8d210c6dc6358d21004ff7558d2101cfe7558d21004fd7558d2101cfc7558d21004ff7458d21094fc7458d210c4ff7358d21006df7358d210dcff7258d21006ef7258d210067f5258d210f4ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21005de7618d210c6de7618d21004de7618d210c75e7518d210c75d7518d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d21006de6418d21006dd6418d21006dc6418d210c7cd7218d21426df6218d210075f5218d2141edf6118d2141fd72118d21427ce2118d21427cc2118d2141fd42118d21006de6018d21006dc6018d21094ff76d0d21004fe76d0d21004fd76d0d21094fc76d0d21006df63d0d21016dc63d0d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006df6350d21016dc6350d2101e7f765492129e7e76549210ce7d765492101e7c76549210067f6454921
  | 19 => 0x9221014dc73592210067f5259221024fc7159221026be4159221026bc4159221004ff705922100cfe705922100cfc7059221026f71059221004ff7558e2101cfe7558e21004fd7558e2101cfc7558e21004ff7458e21094fc7458e21026df7358e210067f5258e210dedf3258e21024fc7158e21026de3158e21026dc3158e21026ef2158e21026ed2158e21004ff7058e2100cfe7058e2100cfc7058e21094ff76d0e21024fe76d0e21004fd76d0e21024fc76d0e21096be64d0e21006bd64d0e212fedf63d0e21016dc63d0e2103dee72d0e21005ed72d0e21004ff7650e21024fe7650e21004fd7650e21024fc7650e21006be6450e21006bd6450e2101e7f7654a2101e7c7654a2129e7f6454a210067e6454a210067d6454a2129e7c6454a2129e7f6354a2120e7e6354a210067d6354a2129e7c6354a2103d7f7254a210e76f7254a2103e7d6254a2103f6c4254a2142f6f3254a2103f6c3254a21007777154a2129f747154a2103e7e6154a2103f6f2154a2103f772154a2103f672154a2103f742154a212067e6054a212067c6054a2103f6f2054a21096be64d0a21006bd64d0a210076d52d0a21025f671d0a21005f571d0a21006be6450a21006bd6450a2103fac4250a21005f77150a21025f47150a21014ff764ca21024fc764ca21016de634ca21006dd634ca21005f7714ca21025f4714ca21004ff75582210067f75582210047f755822101cfe7558221004fd755822101cfc75582210067c755822101c7c7558221004ff7458221094fc7458221004ff7358221014fe7358221014fc73582210067f52582210067d5258221024fc7158221026fb70582210d6fa30582210d6fa2058221026fb1058221026f81058221004ff75d912101cfe75d9121004fd75d912101cfc75d9121006be54d9121006bd54d9121014fe73d9121004fd73d9121014fc73d91210067f52d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121006bc40d91210cd7e75991210057d7599121006bf64991210c5de7399121005dd7399121094ff759912101cfe75991210967e759912101c7e7599121004fd75991210967d75991210047d7599121094fc7599121094fe7499121014fe7399121096de7399121014de7399121004fd7399121096dd7399121004dd7399121014fc7399121004fd7299121096ed72991210067f5299121004fd7199121096f5719912100cfe7099121004fd709912100cfc7099121005df73591210c5dc7359121004ff755912101cfe7559121004fd755912101cfc7559121006bf7459121004ff7359121006df7359121004df7359121014fe7359121014fc7359121006dc7359121014dc7359121004ff7259121006ef72591210067f5259121004ff7159121006f77159121004ff705912100cfe705912100cf
  | 20 => 0x67e40597210067c40597210067f30597210067e30597210067c305972103e7f205972103e7e205972103e7d205972103e7c205972129e7f10597210067e105972129e7c1059721094ff759932101cfe7599321004fd7599321094fc759932103ebe7499321014fe7399321004fd7399321014fc7399321006be4399321096bc4399321024fe729932103e7f529932103e7d529932103ebe429932103ebc429932100cfe7099321004fd709932100cfc7099321004ff755932101cfe7559321004fd755932101cfc755932103ebf7459321004ff7359321014fe7359321014fc7359321006be4359321006bc4359321024fc725932103e7f525932103e7d525932103ebe425932103ebc4259321004ff705932100cfe705932100cfc7059321004ff7558f2101cfe7558f21004fd7558f2101cfc7558f21004ff7458f21094fc7458f2103edf7358f210f6dc4358f21024fc7258f2103e7f5258f2103e7d5258f2103ede3258f2103edc3258f210f6df3158f21004ff7058f2100cfe7058f2100cfc7058f210f6df3058f21094ff76d0f2103cfe76d0f21004fd76d0f2103cfc76d0f2122e7e65d0f210067d65d0f21016de63d0f21006dd63d0f21004ff7650f2103cfe7650f21004fd7650f2103cfc7650f2121e7e6550f210067d6550f21005f77150f21025f47150f2103def764cb210aeef764cb2103f6e654cb2103f6d654cb2103fcf734cb2103fcf634cb21016ee634cb2103eec634cb2103fcc634cb21007cf434cb210f7cc434cb21025ee714cb21025ec714cb210f7cf314cb210f7cf304cb210fd7e75d07210057d75d072113e7e65d07210067d65d0721096be64d0721006bd64d072103dee72d0721005ed72d07211567e65507210067d6550721006be6450721006bd6450721005df73507210f5dc7350721005ef725072103dec7250721014ff764c72103cfc764c72110e7e654c7210067d654c721016de634c721006dd634c721005ef724c72103dec724c721007cd324c721027d4314c721004ff755832101cfe7558321004fd755832101cfc7558321004ff7458321094fc7458321004ff7358321014fe7358321014fc7358321024fc725832103e7f525832103e7d525832103ef6215832103ef5215832103efb705832103efb205832103ef820583210eefa1058321094ff759922101cfe75992210967e759922101c7e7599221004fd75992210967d75992210047d7599221094fc7599221026be7499221014fe7399221004fd7399221014fc73992210067f5299221024fe7199221026be4199221026bc419922100cfe7099221004fd709922100cfc7099221004ff755922101cfe7559221004fd755922101cfc7559221026bf7459221004ff7359221006df7359221004df7359221014fe7359221014fc7359221006dc735
  | 21 => 0xe7498931005bd74989312eedf6398931006ef62989310c5f571989310f5f7715893110d7e75189310057d7518931426df631893103eee6218931006ed62189310067f76549310067e76549310067d76549310067c76549310067f64549310067e64549310067d64549310067c645493129e7f63549314457f725493110f6f72549310067f62549310076f62549310066f625493103e7e625493103e7c62549310076c625493103e6c625493120f5f325493120e7f615493120f77315493129f5e315493129f5c315493120f7431549312067e60549312067c6054931004fe76d0931004fd76d0931094fc76d0931006bf64d0931096bc64d0931004fe7690931004fd769093103cfc769093110d7e75909310057d7590931015de7390931005dd7390931006ef629093103eec6290931004ff7650931004fe7650931004fc7650931006bf6450931006bc6450931006ef625093103eec6250931004fe7610931004fd761093103cfc761093110d7e75109310057d7510931015de7310931005dd7310931025f67110931005f57110931024dc764c931006de644c931006dc644c931015df724c931017cf724c931007cf624c93103ede624c93103edc624c931007cc624c93143f5f524c9310075d524c931007d7714c931025de714c931025dc714c931007d4714c931025d4714c931016df614c931017d7614c931014fe76d0531014fc76d053110d7e75d05310057d75d0531006bf64d0531096bc64d0531015de73d0531005dd73d0531094ff7650531014fe765053114cfd7650531014fc7650531006bf6450531006bc6450531005df7350531015dc7350531027d4315053100cfe76d8131106fa60d8131004ff75d813101cfe75d8131004fd75d813101cfc75d8131094fe74d8131004fd74d8131024fd73d813100cfc73d813103cfe72d8131004fd72d81310067f52d81310067d52d8131046df32d8131006dd32d8131014fd71d8131046f731d8131436de31d8131436dc31d8131046f431d8131106fa30d8131106fa10d81310057f755813110d7c7558131005bf7458131005bc7458131005ef7258131005ec7258131106f860581310067f74597210067e74597210067d74597210067c74597210067f73597210067e73597210067d73597210067c73597210067e43597210067c435972103e7f725972103e7e725972103e7d725972103e7c725972103e7f425972103e7e425972103e7d425972103e7c425972103e7f325972103e7e325972103e7d325972103e7c32597210fe7f715972129e7e71597210067d715972129e7c715972129e7e415972129e7c41597210067f315972129e7e315972129e7c315972103e7f215972103e7e215972103e7d215972103e7c21597210067f70597210067e70597210067d70597210067c7059721
  | 22 => 0xa31004fd7650a31024fc7650a31006be6450a31006bd6450a31005df7350a31015dc7350a311cf9c4350a3103cff7610a31024fe7610a31004fd7610a3111d7e7510a310057d7510a31015dc7310a31025f67110a31005f57110a313375e758ca313375d758ca31005de748ca313379e748ca310059e748ca313379d748ca31335dc748ca31015de728ca31017ce728ca312eedf628ca312efce628ca31336dd628ca312efcd628ca313375f528ca313375d528ca312efd6718ca312eddd718ca31337d5718ca31016de618ca31017d6618ca312efcf218ca31005dd708ca31004ff75582310067f75582310047f755823101cfe7558231004fd755823101cfc75582310067c755823101c7c7558231004ff7458231094fc7458231004ff725823103cfc72582310067f52582310067d5258231024fe7158231024fc715823102ef73158231026f43158231026fb7058231116fa3058231116fa2058231026fb1058231026f81058231004ff75d913101cfe75d9131004fd75d913101cfc75d9131006be54d9131006bd54d9131024ff73d9131024fd73d9131166bf43d9131166bd43d913103cfe72d9131004fd72d91310067f52d913100cfe70d9131004fd70d913100cfc70d9131006be40d9131006bc40d913110d7e75991310057d7599131006bf6499131005ee7299131005ed729913114df57199131094ff759913101cfe75991310967e759913101c7e7599131004fd75991310967d75991310047d7599131094fc7599131094fe749913117cfd7399131096dd739913103cfe7299131096ee729913103cee7299131004fd7299131096ed7299131004ed72991310067f529913117edf329913114cfd7199131096f571991312fede31991312fedc319913100cfe7099131004fd709913100cfc709913117df77159131004ff755913101cfe7559131004fd755913101cfc7559131006bf745913114cff7359131006df7359131004df7359131004ff725913103cfc72591310067f525913117cff7159131006f77159131004ff705913100cfe705913100cfc7059131164fe7619131006bd6419131094ff751913101cfe7519131004fd7519131094fc7519131096be7419131096be5419131006bd5419131024ff7319131024fd7319131096bf431913112ebd431913103cfe7219131004fd72191310067f521913112edf321913144ede311913144edc311913100cfe7019131004fd701913100cfc7019131006be4019131096bc4019131004ff75d893101cfe75d8931004fd75d893101cfc75d8931094fe74d8931004fd74d8931024fd73d89310067f52d8931006ee52d8931006ed52d89310deee32d89310deed32d893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931006ec20d893110d7e75989310057d7598931005b
  | 23 => 0x4ff764c841004fd764c841024fc764c841016de634c841006dd634c84103eee624c841006ed624c841005f7714c841025f4714c841025f77650441006f77650441004f77650441025f77450441027b77450441096f66450441027b66450441097b65450441467b55450441007d77350441007d47350441467775250441007755250441004ff75580410067f75580410047f755804101cfe7558041004fd755804101cfc75580410067c755804101c7c7558041004ff7358041014fe7358041014fc7358041004ff725804103cfc72580410067f52580410067d5258041026f64158041006f54158041026fb7058041126fa5058041006f95058041096fb4058041096f84058041126fa3058041126fa2058041026fb1058041026f81058041094ff759923101cfe75992310967e759923101c7e7599231004fd75992310967d75992310047d7599231094fc7599231026be7499231096bf439923117ebd439923103cfe7299231004fd72992310067f5299231024fe7199231024fc7199231026be4199231026bc419923100cfe7099231004fd709923100cfc7099231004ff755923101cfe7559231004fd755923101cfc7559231026bf7459231006df735923114ebf435923114ebd435923114edc4359231004ff725923103cfc72592310067f5259231024fe7159231024fc7159231026be4159231026bc4159231004ff705923100cfe705923100cfc705923114edf30592312fddd76d0e31006dd76d0e31015de74d0e310179e74d0e312fedf64d0e312ff9e64d0e31006dd64d0e312ff9d64d0e31335de72d0e3145f5f52d0e312ffd671d0e312fddd71d0e31007d571d0e31016de61d0e31017d661d0e312ff9f41d0e312ff9d41d0e31005dd70d0e31004ff7558a3101cfe7558a31004fd7558a3101cfc7558a31004ff7458a31094fc7458a31006df4358a310c6dc4358a31026ef7258a310067f5258a310c6ee3258a310c6ed3258a31336dc3258a31024fc7158a31026df3158a31026dd3158a31026ee2158a31026ec2158a31004ff7058a3100cfe7058a3100cfc7058a310c6df3058a310067f7654a3129e7e7654a310067d7654a3129e7c7654a3129e7f6454a310067e6454a310067d6454a3129e7c6454a310075f7354a3120f5c7354a3120e7d6354a310075f4354a3120f5c4354a314557f7254a3111f6f7254a3103e7e6254a310067d6254a3103e7c6254a313375c3254a3129e7e6154a3129f5f3154a3120f773154a3129f743154a312067e6054a312067c6054a3120f5f3054a31094ff76d0a31024fe76d0a31004fd76d0a31096be64d0a31006bd64d0a31015de73d0a31005dd73d0a311ff9c43d0a3103cff7690a31024fe7690a31004fd7690a3111d7e7590a310057d7590a31015de7390a31005dd7390a31004ff765
  | 24 => 0xc63509410079c63509411ce9c6350941007af7250941007af625094103ebe625094103ebc6250941007ac625094103eac62509414873f52509410073d5250941007b77150941025be7150941025bc7150941007b47150941004fe76109411557e75109410057d751094147dbe7410941006df63109411aedc6310941004fe768c941004fd768c94103cfc768c9411557e758c9410057d758c941005be748c941005bd748c941006df638c941016dc638c941004ff764c941004fe764c941004fc764c941005be744c941005bd744c941006df634c941016dc634c9410079f434c9411557e75d05410057d75d0541025be74d0541026bf64d0541006df63d054117edc63d05410977675d05410977575d0541025f674d0541026f764d0541027b764d0541007d763d0541007d463d0541097b743d0541007b543d05414777752d05410077552d0541097b742d0541007b542d0541005f570d054100cfe76d8141006df63d8141006dc63d8141146fa60d8141004ff75d814101cfe75d8141004fd75d814101cfc75d8141024fd74d8141014fe73d8141004fd73d8141014fc73d814103cfe72d8141004fd72d81410067f52d81410067d52d8141006bf42d8141006bd42d8141146fa40d8141146fa10d81410057f75581411557c7558141005df735814114ddc7358141006df6358141006dc6358141005ef7258141005ec7258141146f86058141004ff7558c4101cfe7558c41004fd7558c4101cfc7558c41026df7358c4112ede5358c41006dd5358c41096df4358c41096dc4358c41004ff7258c4103cfc7258c410067f5258c4112edf3258c41024fc7158c41026bf4158c41026bd4158c41026de3158c41026dc3158c41004ff7058c4100cfe7058c4100cfc7058c4112edf3058c4117cff7650c4117ebe6450c41004ff755884101cfe7558841004fd755884101cfc7558841004ff7358841014fe7358841014fc7358841026ef72588410067f5258841006ee5258841006ed5258841096ef4258841096ec4258841026bf4158841026bd4158841026ee2158841026ec2158841004ff705884100cfe705884100cfc70588410067f765484129e7e76548410067d765484129e7c765484113e7e645484120e7e63548410067d635484129e7c63548414557f72548411376f725484103e7e625484129f6e625484103e6e62548410067d625484129f6d62548410066d625484103e7c625484129e7e615484129f3f415484129f76415484129f3d41548412067e60548412067c6054841004fd76908411357e75908410057d759084112dde7390841005dd7390841004ff765084146ebe6450841097ac425084103cff768c841024fe768c841004fd768c8411357e758c8410057d758c841095be748c841005bd748c84103eee628c841006ed628c841
  | 25 => 0x8d412fedc21d8d41006df70d8d41006de70d8d41006dd70d8d41006dc70d8d41006df50d8d41006de50d8d41006dd50d8d41006dc50d8d41006de40d8d41006dc40d8d41006de20d8d41006dc20d8d412fedf10d8d41006de10d8d412fedc10d8d4114edc6358d41005de7618d4114ede7618d4114f5e7518d4114f5d7518d41006df6518d41006de6518d41006dd6518d41006dc6518d4114f9d7418d4144edf6418d410075f5218d4144f9e4118d4144f9c4118d41006de6018d41006dc6018d41164fe76d0d41016dc63d0d41005be76d0d41166be76d0d4114dbd73d0d410079f63d0d41016be63d0d41016bc63d0d4114f9c63d0d410169c63d0d41005bd72d0d414a73f52d0d4114f9f32d0d41025be71d0d41025bc71d0d41096bf61d0d412ff9c31d0d41024fc7650d41006df6350d41016dc6350d41005f77150d41025f47150d41025bc7650d41016bc7650d41024bc7650d4114dbf7350d410079f7350d410079f6350d41016be6350d41016bc6350d4114f9c6350d41005bf7250d4149f3f5250d41007b77150d41025be7150d41025bc7150d41007b47150d4114f9f3050d41006df63d8941006dc63d8941004ff75d894101cfe75d8941004fd75d894101cfc75d8941014fe73d8941004fd73d8941014fc73d89410067f52d8941006ee52d8941006ed52d894100cfe70d8941004fd70d894100cfc70d8941006ee20d8941006ec20d89411557e75989410057d759894114dde7398941005dd7398941006df6398941006dc6398941006ef6298941005df735894114ddc7358941006df6358941006dc63589411557e75189410057d7518941006df6318941006dc631894103eee6218941006ed62189410067f76549410067e76549410067d76549410067c76549410067f63549410075f63549410065f635494120e7e635494120e7c63549410075c635494120e5c63549410073f43549410073d43549411557f72549411576f72549410067f62549410076f62549410066f625494103e7e625494103e7c62549410076c625494103e6c625494129f3e41549412067e60549412067c6054941004fe76d0941006df63d09411fedc63d0941005be76d0941006be76d0941005bd73d09410079f63d09411febe63d09411febc63d09410079c63d09411fe9c63d094103ebe62d094103ebc62d09414973f52d09410073d52d0941025be71d0941025bc71d0941096bf61d0941024fe76909411557e75909410057d759094148dbd749094114dde7390941005dd7390941006df63909411e6dc6390941006ef629094103eec6290941025f67190941005f57190941024fc7650941006df63509411cedc6350941006ef625094103eec6250941005f77150941025f47150941024bc7650941005bf73509410079f63509411cebe63509411ceb
  | 26 => 0x26dc3158e41004ff7058e4100cfe7058e4100cfc7058e4114cfd76d0e41016dc63d0e41014ff7650e41016de6350e41006dd6350e41005f77150e41025f47150e41004ff7558a4101cfe7558a41004fd7558a4101cfc7558a41004ff7358a41014fe7358a41014fc7358a41026ef7258a410067f5258a41026bf4158a41026bd4158a41026ee2158a41026ec2158a41004ff7058a4100cfe7058a4100cfc7058a41026f71058a410067f7654a4129e7e7654a410067d7654a4129e7c7654a411567d6454a4120e7e6354a410067d6354a4129e7c6354a414557f7254a4116f6f7254a4103e7e6254a410067d6254a4103e7c6254a4129e7e6154a4129f3f4154a412067e6054a412067c6054a4116d7e7590a410057d7590a41165de7390a41005dd7390a4103eee6290a41006ed6290a41025f67190a41005f57190a4103cff7650a4103eee6250a41006ed6250a41005f77150a41025f47150a4116d7e7510a410057d7510a41007ad4210a4103cff768ca41024fe768ca41004fd768ca4116d7e758ca410057d758ca41005be748ca41005bd748ca4103eee628ca41006ed628ca41004ff764ca41004fd764ca41024fc764ca41016de634ca41006dd634ca4103eee624ca41006ed624ca41025f576d0641096f576d06410977675d06410977575d0641027b674d0641097b654d06414afb554d06414af7752d06410077552d0641005f570d0641004ff755824101cfe7558241004fd755824101cfc7558241004ff7358241014fe7358241014fc7358241004ff725824103cfc72582410067f52582410067d5258241026fb7058241006fb505824115ef8505824115efa405824115efa305824115efa2058241026fb1058241026f81058241014fe76d8d4114ede63d8d41004ff75d8d4101cfe75d8d41004fd75d8d4101cfc75d8d41024fd74d8d41006df53d8d4114ede53d8d41006dd53d8d4114edc53d8d4114ede43d8d4103cfe72d8d41004fd72d8d410067f52d8d4114edf32d8d4114edc32d8d4114edf31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d4114edf30d8d41006de30d8d4114edc30d8d4114dde76d8d41014de76d8d41006df65d8d41006de65d8d41006dd65d8d41006dc65d8d412ff9f74d8d410075f52d8d412ff9e41d8d412ff9c41d8d41006de60d8d41006dc60d8d41006df75d8d41006de75d8d41006dd75d8d41006dc75d8d412fedf74d8d4114ede74d8d41006df54d8d41006de54d8d41006dd54d8d41006dc54d8d41006df72d8d41006de72d8d41006dd72d8d41006dc72d8d41006df52d8d410065f52d8d41006de52d8d41006dd52d8d41006dc52d8d41006df71d8d412fede71d8d41006dd71d8d41006df51d8d412fede51d8d41006dd51d8d412fedc51d8d412fede41d8d412fedc41d8d412fede21d
  | 27 => 0xd63d0f41016bc63d0f41005bd72d0f414c73f52d0f4117f9f32d0f41025be71d0f41097b671d0f41097b571d0f41025bc71d0f412ff9c31d0f4112cff7650f4121e7e6550f410067d6550f41005bf7650f4112ebf7650f414bf3e6550f410073d6550f410979f7350f41016be6350f41016bc6350f41005bf7250f414bf3f5250f41025be7150f41025bc7150f4117f9f3050f4113d7e7598b410057d7598b410067e6598b410067d6598b4117dde7398b41005dd7398b41096ef6298b4103eec6298b4113d7e7558b410067e6558b410067d6558b41096ec6258b41004ff7558b4101cfe7558b410067e7558b4101c7e7558b41004fd7558b410067d7558b4101cfc7558b41024fc7458b41004ff7358b41014fe7358b41014fc7358b410067f5258b41096ef4258b41096ec4258b41006ef3258b41006ec3258b41004ff7058b4100cfe7058b4100cfc7058b410057f7654b410067f7654b410047f7654b410067e7654b410057d7654b410067d7654b410047d7654b410067c7654b4120e7e6354b410067d6354b4120e7c6354b410073f4354b410073d4354b4113d7f7254b4113f6f7254b4103e7e6254b410067d6254b4103e7c6254b412067e6054b412067c6054b41024bd76d0b410973e65d0b410973d65d0b41005bd73d0b411febe63d0b41096bc63d0b4103ebe62d0b41097ae62d0b41097ad62d0b4103ebc62d0b414b73f52d0b410073d52d0b41025be71d0b41097b671d0b41097b571d0b41025bc71d0b4113d7e7590b410057d7590b411ee7e6590b410067d6590b4117dde7390b41005dd7390b411d67e6550b410067d6550b41005bf7650b41006bf7650b4146f3e6550b410073d6550b41005bf7350b411cebe6350b411cebc6350b41097af7250b4103ebe6250b4103ebc6250b4146f3f5250b410073d5250b41025be7150b41025bc7150b4103cff768cb41094fe768cb41004fd768cb4113d7e758cb410057d758cb4119e7e658cb410067d658cb41095be748cb41005bd748cb41016de638cb41006dd638cb41004ff764cb41004fd764cb41094fc764cb4118e7e654cb410067d654cb41095be744cb41005bd744cb41016dc634cb410079f434cb41005f7714cb41025f4714cb4100cff76583410067e65583410067d6558341096f86058341004ff755834101cfe7558341004fd755834101cfc7558341024fc7458341004ff7358341014fe7358341014fc7358341004ff725834103cfc72583410067f52583410067d5258341006bf4258341006bd4258341096fb4058341096f84058341176fa1058341004ff7558e4101cfe7558e41004fd7558e4101cfc7558e41026df7358e41166de4358e41004ff7258e4103cfc7258e410067f5258e41166df3258e41024fc7158e41026bf4158e41026bd4158e41026de3158e41
  | 28 => 0x493218f6f725493203e7f625493203f6c425493220f6f325493203f5e325493203f5c325493203f6c325493203f4c325493229e7c615493220f5f315493203f6f21549322067e60549322067c605493220f5f305493203f6f2054932014fe76d0932014fc76d0932006bf64d0932096bc64d0932015de73d0932005dd73d09321ff9c43d09320076d52d0932094ff7650932014fe76509321ccfd7650932014fc7650932006bf6450932006bc6450932005df7350932015dc73509321cf9c435093203fac425093203fcc3250932004ff75d853201cfe75d8532004fd75d853201cfc75d8532094fe74d8532004fd74d853203cfd73d85320067f52d85320067d52d8532006f751d8532006f451d85320f6f631d853200cfe70d8532004fd70d853200cfc70d8532006f7619853218d7e75185320057d7518532005be7418532005bd74185322eedf6318532026f66118532006f56118532185fa7018532005f9701853200cfe76d813218d7e75d81320057d75d8132186fa60d8132004ff75d813201cfe75d81320067e75d813201c7e75d8132004fd75d81320067d75d81320047d75d813201cfc75d8132094fe74d8132004fd74d813203cfd73d8132014fd72d81320067f52d81320067d52d8132024fe71d8132004fd71d8132186fa30d8132186fa20d8132186f860581320957f765974113e7f765974101c7f76597410967f63597410067e63597410967c63597410057f72597410967f62597410967c62597414cf3e41597410973c41597410967f60597410067e60597410967c605974113e7f74597410967e745974113e7d74597410967c74597410067f73597410067e73597410067d73597410067c73597410967f43597410067e43597410967c43597410067f72597410047f72597410067e72597410067d72597410067c72597410967f42597410967c42597410067f32597410067c325974113e7f71597414ce7e71597410067d71597414ce7c71597410967f41597414ce7e41597410967c41597410067f31597414ce7e31597414ce7c31597414ce7e21597414ce7c21597410067f70597410067e70597410067d70597410067c70597410967f40597410067e40597410967c40597410067f30597410067e30597410067c30597410067e20597410067c20597414ce7f10597410067e10597414ce7c1059741014ff7658f410067e6558f410067d6558f41096dc6358f41004ff7558f4101cfe7558f41004fd7558f4101cfc7558f41024fc7458f41096df4358f41096dc4358f41004ff7258f4103cfc7258f410067f5258f4117edc3258f4117edf3158f41004ff7058f4100cfe7058f4100cfc7058f4117edf3058f41025bd76d0f41016bd76d0f41024bd76d0f410973e65d0f410973d65d0f41016be63d0f410979e63d0f410979
  | 29 => 0x6bc50592321cebf30592321cebe30592321cebd30592321cebc305923203ebf205923203ebe205923203ebd205923203ebc2059232006be1059232006bc1059232004ff755863201cfe7558632004fd755863201cfc7558632004ff7458632094fc745863203cfc725863203e7f525863203e7d525863203edf325863203edd325863203ef771586320c6f631586322eedc315863203ef7215863203ef42158632004ff705863200cfe705863200cfc7058632004ff755823201cfe7558232004fd755823201cfc7558232004ff7458232094fc745823203cfe725823203cfc725823203e7f525823203e7d525823203edf325823203edd3258232004ff7158232024fc7158232056dc315823203efb7058232196fa305823203efb205823203ef82058232196fa1058232004ff75d913201cfe75d9132004fd75d913201cfc75d913203cff73d913203cfd73d9132006dd73d91321e6bf43d91321e6bd43d91321e6dc43d91320067f52d9132024fe71d9132004fd71d913200cfe70d9132004fd70d913200cfc70d91321e6df30d9132006bf64991321ff9c43991321cded7299132094ff759913201cfe7599132004fd7599132094fc7599132094fe74991321fcfd7399132096dd73991321febe4399132096bc43991321ccfd7299132096ed72991320067f5299132024fe7199132004fd719913200cfe7099132004fd709913200cfc70991321cf9c43591321fdef7259132005f77159132005f47159132004ff755913201cfe7559132004fd755913201cfc7559132006bf74591321ccff7359132006df73591321cebe43591321cebc43591321cedc43591321fcff7259132006ef72591320067f5259132004ff7159132006f77159132004f77159132024fc7159132006f47159132024f47159132004ff705913200cfe705913200cfc70591321cedf30591321e4fe761913218d7e75191320057d7519132006bd6419132094ff751913201cfe75191320967e751913201c7e7519132004fd75191320967d75191320047d7519132094fc7519132096be741913203cff731913203cfd7319132096bf43191321aebd43191320067f5219132024fe7119132004fd711913200cfe7019132004fd701913200cfc701913203dde76d0d32006de76d0d3203cde76d0d32015de74d0d320179e74d0d32006df64d0d320079f64d0d32006dd64d0d320079c64d0d3203dde72d0d32007ce72d0d3203dce72d0d32007cd72d0d3203ddc72d0d32016df62d0d32017cf62d0d324d75f52d0d32005dd71d0d322fedc61d0d32005dd70d0d3201e7f765493220e7e765493220e7d765493201e7c76549320067f64549320067e64549320067d64549320067c64549320075f735493220f5c735493203e7f63549320075f435493220f5c435493203d7f725
  | 30 => 0xd305963220e7c305963203e7f205963203e7e205963203e7d205963203e7c20596320067e10596320067c1059632094ff759923201cfe7599232004fd7599232094fc759923203ebe7499232006bf5499232096be5499232006bd5499232096bc5499232096bf43992321febd439923203cfe729923203cfc729923203e7f529923203e7d529923203ebe429923203ebc429923203edf329923203edd3299232024fe7199232004fd71992321fedc319923200cfe7099232004fd709923200cfc7099232006be4099232096bc4099232096bf7599232006be7599232006bd7599232096bc7599232096bf73992321febe73992321febd7399232096bc73992321febf53992321febe53992321febd53992321febc539923203ebf729923203ebe729923203ebd729923203ebc729923203ebf529923203e3f529923203ebe529923203ebd529923203e3d529923203ebc529923203ebf329923203e9f329923203ebe329923203ebd329923203e9d329923203ebc3299232096bf7199232006be7199232006bd7199232096bc7199232006bf5199232006be5199232006bd5199232006bc51992321febf31992321febe31992321febd31992321febc31992321fe9c319923203ebf219923203ebe219923203ebd219923203ebc2199232096bf7099232006be7099232006bd7099232096bc7099232006bf5099232006be5099232006bd5099232006bc50992321febf30992321febe30992321febd30992321febc309923203ebf209923203ebe209923203ebd209923203ebc2099232006be1099232006bc1099232004ff755923201cfe7559232004fd755923201cfc755923203ebf7459232006bf5459232006be5459232006bd5459232006bc54592321cebf43592321cebd435923203cfe725923203cfc725923203e7f525923203e7d525923203ebe425923203ebc4259232004ff7159232024fc7159232004ff705923200cfe705923200cfc7059232006be4059232006bc4059232006bf7559232006be7559232006bd7559232006bc75592321cebf73592321cebe73592321cebd73592321cebc73592321cebf53592321cebe53592321cebd53592321cebc535923203ebf725923203ebe725923203ebd725923203ebc725923203ebf525923203e3f525923203ebe525923203ebd525923203e3d525923203ebc525923203ebf325923203ebe325923203ebd325923203ebc3259232006bf7159232006be7159232006bd7159232006bc7159232006bf5159232006be5159232006bd5159232006bc51592321cebf31592321cebe31592321cebd31592321cebc315923203ebf215923203ebe215923203ebd215923203ebc2159232006bf7059232006be7059232006bd7059232006bc7059232006bf5059232006be5059232006bd5059232
  | 31 => 0x94420067e73594420067d73594420067c73594420967f43594420067e43594420967c435944203e7f725944203e7e725944203e7d725944203e7c725944203e7f425944203e7e425944203e7d425944203e7c425944203e7f325944203e7e325944203e7d325944203e7c32594420067f71594420067e71594420067d71594420067c71594420967f41594420967c41594420067f31594420067c315944203e7f215944203e7e215944203e7d215944203e7c21594420067f70594420067e70594420067d70594420067c70594420967f40594420067e40594420967c40594420067f30594420067e30594420067c305944203e7f205944203e7e205944203e7d205944203e7c20594420067e10594420067c1059442004ff7558c4201cfe7558c42004fd7558c4201cfc7558c4203edf7358c42096df4358c42096dc4358c4203cfc7258c4203e7f5258c4203e7d5258c4203ede3258c4203edc3258c42004ff7158c42024fc7158c421aedf3158c42004ff7058c4200cfe7058c4200cfc7058c421aedf3058c421fcff7650c4221e7e6550c420067d6550c4203def7650842006ef7650842004ef765084203f6e655084203f6d655084203def745084203faf7450842096ee645084203fae6450842097ae54508424dfad5450842097af4350842007ad4350842004ff755844201cfe7558442004fd755844201cfc7558442004ff7358442006df7358442004df7358442014fe7358442014fc7358442006dc7358442014dc735844203e7f525844203e7d525844203ebf425844203ebd425844203ef77158442096f74158442096f4415844203ef7215844203ef42158442004ff705844200cfe705844200cfc7058442004ff755804201cfe7558042004fd755804201cfc7558042004ff7358042014fe7358042014fc735804203e7f525804203e7d525804203ebf425804203eee425804203ebd4258042006ed4258042004ff7158042024fc715804203efb7058042096fb4058042096f840580421a6fa305804203efb205804203ef820580421a6fa10580420067f74596320067e74596320067d74596320067c745963220e7f735963220e7e735963220e7d735963220e7c735963220e7f435963220e7e435963220e7d435963220e7c435963203e7f725963203e7e725963203e7d725963203e7c725963203e7f425963203e7e425963203e7d425963203e7c425963203e7f325963203e7e325963203e7d325963203e7c32596320067f71596320067e71596320067d71596320067c715963220e7f315963220e7e315963220e7d315963220e7c315963203e7f215963203e7e215963203e7d215963203e7c21596320067f70596320067e70596320067d70596320067c70596320067e40596320067c405963220e7f305963220e7e305963220e7
  | 32 => 0x67d6550e42016de6350e42006dd6350e42005ef7250e4203dec7250e4203ded76d0a42096ed76d0a4203f6e65d0a4203f6d65d0a4203fae74d0a42097ae54d0a424ffad54d0a4203fce63d0a4203fcd63d0a42005ed70d0a42004ff755864201cfe7558642004fd755864201cfc7558642004ff7358642014fe7358642014fc735864203e7f525864203e7d525864203ebf425864203ebd425864203ef7715864203ef7215864203ef42158642004ff705864200cfe705864200cfc7058642004ff755824201cfe7558242004fd755824201cfc7558242004ff7358242014fe7358242014fc735824203e7f525824203e7d525824203ebf425824203ebd4258242004ff7158242024fc715824203efb70582421defa405824203efb205824203ef820582421defa1058242014fe76d8d421cede63d8d421cf9e43d8d42004ff75d8d4201cfe75d8d42004fd75d8d4201cfc75d8d4203cfd74d8d4203cbd74d8d421cebe43d8d421cede43d8d421cebc43d8d420067f52d8d421cedf32d8d42024fe71d8d42004fd71d8d421cedc31d8d4200cfe70d8d42004fd70d8d4200cfc70d8d421cedc6358d421cf9c4358d42005f77158d42005f47158d421e4fe76d0d421cdbe74d0d42016de63d0d4203cfc7650d421cdbf7450d42006df6350d42016dc6350d421cf9c4350d42005ef7250d4203dec7250d4201e7f76549421be7e76549421d67d765494201e7c76549420073f74549420073c745494203e7f64549420067f635494220e7e635494220e7c63549424f73e43549424f73c435494203d7f72549421d76f725494203e7f625494203f3e425494203f3c425494203f6c425494203f2c42549424f76f325494203f6c325494229e7c615494203f6f21549422067e60549422067c605494203f6f205494203dbe74d094203ebf64d09424ef6f52d09420076d52d094203dee74d094203eef64d094203faf64d09424e7ae43d0942097ac43d0942005ed70d09421d57e75d85420057d75d8542004ff75d854201cfe75d85420067e75d854201c7e75d8542004fd75d85420067d75d85420047d75d854201cfc75d8542014fe73d8542004fd73d8542014fc73d85420067f52d85420067d52d8542006f731d8542006f431d854200cfe70d8542004fd70d854200cfc70d8542006f76198542005df73585421cddc7358542026f66118542006f5611854200cfe76d81421c6fa60d8142004ff75d814201cfe75d8142004fd75d814201cfc75d814203cfd74d8142014fe73d8142004fd73d8142014fc73d81420067f52d81420067d52d8142024fe71d8142004fd71d8142006fb50d81421c6f850d81421c6fa40d81421c6fa20d81420057f75581421d57c75581421c6f860581421b67f74594420967e74594421b67d74594420967c74594420067f735
  | 33 => 0x76198742026f46198742096f46158742004ff755874201cfe7558742004fd755874201cfc755874203cfc7458742004ff7358742014fe7358742014fc73587420067f52587420067d5258742096f74158742096f44158742004ff705874200cfe705874200cfc705874200cff76583420057f75583421bd7c7558342096f86058342004ff75583420067f75583420047f755834201cfe7558342004fd755834201cfc75583420067c755834201c7c755834203cfc7458342004ff7358342014fe7358342014fc73583420067f52583420067d5258342004ff7158342024fc7158342096fb4058342096f840583421f6fa20583421ee7f74596421ee7e74596420067d74596421ee7c74596420067f73596420067e73596420067d73596420067c73596420067e43596420067c435964203e7f725964203e7e725964203e7d725964203e7c725964203e7f425964203e7e425964203e7d425964203e7c425964203e7f325964203e7e325964203e7d325964203e7c32596420067f71596420067e71596420067d71596420067c71596420067f31596420067c315964203e7f215964203e7e215964203e7d215964203e7c21596420067f70596420067e70596420067d70596420067c70596420067e40596420067c40596420067f30596420067e30596420067c305964203e7f205964203e6f205964203e7e205964203e7d205964203e7c20596420067e10596420067c1059642004ff7558e4201cfe7558e42004fd7558e4201cfc7558e4203edf7358e42006df5358e421e6de5358e42006dd5358e421e6dc5358e421e6de4358e4203cfc7258e4203e7f5258e4203e7d5258e4203ede3258e4203edc3258e42004ff7158e42024fc7158e421e6df3158e421e6dc3158e42004ff7058e4200cfe7058e4200cfc7058e421e6df3058e42006de3058e421e6dc3058e42006df7558e42006de7558e42006dd7558e42006dc7558e42006dd7458e421e6dc7458e42006df5458e42006de5458e42006dd5458e42006dc5458e4203edf7258e4203ede7258e4203edc7258e4203edf5258e4203e5f5258e4203ede5258e4203edd5258e4203e5d5258e4203edc5258e4203edf4258e4203ede4258e4203edd4258e4203edc4258e42006df7158e42006de7158e42006dd7158e42006dc7158e42006df5158e42006de5158e42006dd5158e42006dc5158e4203edf2158e4203ede2158e4203edd2158e4203edc2158e42006df7058e42006de7058e42006dd7058e42006dc7058e42006df5058e42006de5058e42006dd5058e42006dc5058e42006de4058e42006dc4058e4203edf2058e4203ede2058e4203edd2058e4203edc2058e42006de1058e42006dc1058e421ccfd76d0e4222e7e65d0e420067d65d0e42016de63d0e42014ff7650e4221e7e6550e42
  | 34 => 0xd5220f5f3050d520057e74d85520057d74d855220d7e73d85520057d73d855220d7c73d85520067f63d85520067d63d85520fe7f62d85520ff6f62d85520077731d85520077431d85522057e70d85520057d70d85522057c70d85520057e74985520057d74985520067f64985520067d649855220d7e73985520057d739855229d7c73985520cd7d729855229f6d72985520cd6d72985524567f62985520e76f629855229d7e719855229e7f61985520077761985522057e70985520057d70985522057c70985520067e60985520067c60985520057f74585520057c74585520057f73585520075f73585520055f735855220d7e735855220d7c73585520075c735855220d5c73585520067f63585520067d63585520e57f72585520076f72585520e56f72585520ce7f62585520cf6f625855200777615855229e7e61585520057f70585522057e70585522057c70585520fd7e76185520057e74185520057d74185520067f64185520067d641855220d7e73185520057d731855229d7c73185524567f62185520b76f621855229e7f611855229f76611855229e7d611855200775611855200777311855229f7431185522057e70185520057d70185522057c70185520067e60185520067c60185522057e76d81520057e74d81520057d74d81520067f64d81520067d64d815220d7e73d81520057d73d815220d7c73d815206f6f72d815203d7e72d815201d7d72d815206e7f62d815206f6f62d815229d7e71d81520057d71d81522067e60d81522077a60d81522067c60d81522077840d81522077a20d81520057f74581520073f74581520053f74581520057c74581520073c74581520053c74581520067f64581520067d64581520057f735815220d7e735815220d7c735815250d7f72581520076f725815250d6f725815205e7f625815205f6f62581520057f715815229d7c71581522057f70581520077b60581522067e60581522067c6058152207786058152014ff7658f42096dc6358f420979c4358f42004ff7558f4201cfe7558f42004fd7558f4201cfc7558f4203cfc7458f4203cbc7458f421fede5358f42006dd5358f42096df4358f421febe4358f421febc4358f42096dc4358f420067f5258f421fedf3258f42004ff7158f42024fc7158f421fedc3158f42004ff7058f4200cfe7058f4200cfc7058f421fedf3058f421acff7650f421fdbf7450f420979c4350f4201e7f7654b4201e7c7654b420073f7454b420073c7454b4203e7e6454b4220e7e6354b420067d6354b4220e7c6354b425073e4354b425073c4354b4203d7f7254b421bf6f7254b4203e7d6254b4203f3e4254b4203f6e4254b4203f2e4254b4203f3c4254b4203f6e3254b4229e7e6154b4203f6c2154b422067e6054b422067c6054b4203f6f2054b42096f
  | 35 => 0x67f52d8143024fe71d8143004fd71d8143216fa40d8143216fa30d81430057f755814321d7c7558143216f8605814320d7e73d91520057d73d915220d7c73d91521ee7f62d91521ef6f62d915229d7e71d91520057d71d91522057e70d91520057d70d91522057c70d91520073e40d91520073c40d91521b57e74991520067f64991520073f64991520063f649915220d7e73991520057d739915220d7c73991521d57d72991520076d72991521d56d72991521be7f62991521bf6f629915229d7e71991520057d71991522057e70991520057d70991522057c70991520067e60991520067c60991520073f64591520067e64591520057f735915220d7e735915220d7c73591521bd7f72591520076f72591521bd6f72591521d67f62591521d76f62591520057f715915229d7c71591520057f70591520077b70591520057b70591522057e70591522057c70591520077870591522057870591521ed7e76191520067f64191520073e64191520067d64191520073d64191520063d641915220d7e73191520057d731915220d7c73191521b67f62191521b76f621915229d7e71191520057d71191522057e70191520057d70191522057c70191520067e60191520067c60191520073e40191520073c401915220d7e76d8d520057e74d8d520057d74d8d520067f64d8d520067d64d8d5220e7e63d8d5220f5e63d8d5220e5e63d8d5220e7c63d8d5203d7e72d8d5201d7d72d8d5219e7f62d8d5219f6f62d8d5220f5f32d8d5229d7e71d8d520057d71d8d5220f5c31d8d522057e70d8d520057d70d8d522057c70d8d520067e60d8d520067c60d8d520057f7458d520057c7458d520067f6458d520067d6458d5220d7f7358d520075f6358d5220e7e6358d5220e7c6358d5220f5c6358d525157f7258d520076f7258d525156f7258d5218e7f6258d5218f6f6258d520057f7158d52007777158d52005777158d5229d7c7158d52007747158d52005747158d520057f7058d522057e7058d522057c7058d520067e6058d520067c6058d5220f5f3058d520057f76d0d520057e76d0d520057d76d0d520057c76d0d5220d7e74d0d5220d7d73d0d5220f3e43d0d5220f5e43d0d5220f3c43d0d5203d7e72d0d520076e72d0d5203d6e72d0d520057d72d0d520076d72d0d520056d72d0d5203d7c72d0d524467f62d0d5222f6f62d0d5220f5f32d0d5229d7e71d0d520057d71d0d5220f5c31d0d522057e70d0d520057d70d0d522057c70d0d520057f7650d520057e7650d520057d7650d520057c7650d5220d7f7450d5220d7f7350d520075f4350d5220f3e4350d5220f3c4350d5220f5c4350d520057f7250d5203d7e7250d5203d7c7250d524467f6250d5221f6f6250d520057f7150d5229d7c7150d520057f7050d522057e7050d522057c705
  | 36 => 0x2001800800040070000000002c002000400000000000000000003800b0000002003800600280050010000000000000080000010007000401c0024000000c0000018001000000500040010000001000c0000034002002400500c000300040020000000001000b00100000000000000401500700000014001000c004000400400080000010013002c0000018001002000000080000000000000001200000000030000000000b0014000000c001001c000000400100000020000010000400b000c01100000070048000000000000140050008006001800400000020000018000000300140000004001001800b0000009000c0010004002000000f0000001002000000000080000010001c0020000012000400300400220010000000c0060000000001c0000000002000400122d7e7598b430057d7598b43096ef6298b4303eec6298b43096ec6258b43004ff7558b4301cfe7558b43004fd7558b4301cfc7558b43014fc7458b431cebe4358b431cebc4358b430067f5258b43006ee5258b43006ed5258b43096ef4258b43096ec4258b431ceee3258b43004ff7158b43024fc7158b43004ff7058b4300cfe7058b4300cfc7058b43096f76198743026f46198743096f46158743004ff755874301cfe7558743004fd755874301cfc7558743014fc7458743004ff725874303cfc72587430067f525874314edf3258743096f74158743096f4415874314ef631587432fedc3158743004ff705874300cfe705874300cfc705874300cff76583430057f755834322d7c7558343096f86058343004ff75583430067f75583430047f755834301cfe7558343004fd755834301cfc75583430067c755834301c7c7558343014fc745834307ede4358343004ff725834303cfc72583430067f525834307edf3258343004ff7158343024fc715834307edc3158343096fb4058343096f84058343226fa3058343015de74d0d430179e74d0d43016df64d0d430179f64d0d4351f5f52d0d43005dd70d0d43004ff75d894301cfe75d8943004fd75d894301cfc75d8943006df43d89431febe43d89431febc43d89431fedc43d89430067f52d89431feee32d8943024fe71d8943004fd71d894300cfe70d8943004fd70d894300cfc70d89431fedf30d894321d7e75989430057d7598943006ef6298943005f77158943005f4715894321d7e75189430057d751894303eee6218943006ed6218943004ff75d854301cfe75d8543004fd75d854301cfc75d854303cfe72d8543004fd72d85430067f52d854317ef631d854300cfe70d8543004fd70d854300cfc70d8543006f761985432fedf6318543026f66118543006f5611854300cfe76d8143216fa60d8143004ff75d814301cfe75d8143004fd75d814301cfc75d8143014fd74d814303cfe72d8143004fd72d8143
  | 37 => 0x10000002c011000000000100010014002001000300000060028005001c000006c0010018000003c00b0030000000000500000020000009000000100040000008000000c002001400000040060004002001000300300010000001000000100000000000001000001100080000018002000400d00000000000000000c00b008c01c001c006000000c00000040020001001000500080030000006000400000700010008000001c00d000c000002800000000050000001003000100100040000002003c00400040000020005001000500180020000001000401a00200030008000000400800140030004000000800300140000074002000400000000020010000001c0020018000000c001000400100040000008000000400700200030000001002400c000000300040090004012000c005003800000a40070058011000c0000004008000c0050024003002000200000090008001000400300000000018008000401a0004001000c00500040000050000000c002000c000002800500300000008000000c00900000030008000001400000080010004001001c022000800200100000004002000800700040010000000000800000280000000001000c0000010003000400100080010000002000000e0008010004c008000000000240000004008001c00100200000034012001c0000000001000400000000010000002001000200040060008000000c00100200000010000000c000000c00500080020000000001802900180040004005001401d00080080020007006000800000050000000000c000001800100000040000000000c002000c0040008000000000100040030010004002c001000000b000c001000400d0010001000000b0008005000000400040010000000004c008001800000000010034004000c00500380000000001000400100240000004000000800200000030000000000000000040040004002000c0080028000002000100600000000005000000600000020000001001c01b001c004000800000200020000003003000200000020000002001000200000180000002000000000000020000001000c0030000003000800300080010018000002c0000000001004800200180030008000002c0030028004000c00300000010014000000800d00000030000000000000000200010008000004c003000000200040000004002000000500000050004000004c0010004000000001b00180040004008000000e00180000000000000400200040020044000000c011007c00a00100000000008000000000100050000002002800100240130000000000400200200060000000001000100040020008003003400000000000018012000000c001c0010038000003c0000028002000000a0018000002400200040010004004001c0030000002001c00
  | 38 => 0x400300ac007000400000040000000007000c005000000100000070010000001400b003400500140040014004000000000040020028000000800100180000000009000800e001000a0004003000400100080000004007000000400080000000000002c00200140060000012000c0100000001000000700000000010000002002500040020048001005800200040020000005001000900080000000000000c003001c000000c00100080020004000000c00100040080000001000000200180040008017000400000040000008006000400600180000020001000400500100090004000005c0000084000000000a0000002006c000000401100000000018003000c0060004002000000100040030008004000800e00100000000001000c002000c00000000020008003000c00200100090004000000c006000800501380200014015004c012000000f00200050000002000c0000004003001c002000800100000000000002000000d000000800080000014000002401d000400200080060018002001000100000040008000005800000080020004001000000100040000004006002000d00040000000003000c002000800100000010018002000000200300080004006000400200000010018000000000500080000008005000c0170004000000400000680010004006002800400140010014009000000800000020048007002800300100150004001001000a003000b0004000004000600100000000004000c00100180000000008002c00700080060008001000001c00000090000001000000100180000004009000800e00040010004000000000100600020000019000000000040020000005001400000040020000003001400300140020000000000000100100030014008000c00000000090010004000000500000030010000000c017002c00c001000500100020008001000800700100010024010000800100000040000002000000500200000004005001c002003c009000400200000000000013001c0000004000001400100280190014000000000d000000100100060000001002800100140060000005006c00400080010018001000001c000000d0000001001800000040070014001000c000000000d000c000002800300000000028003000800600080010004000001800a00000000004004000000500040070000006008000b000000000000080000006000000200080010024001007000000000060020000000000c004c001000000c001400000040030008000001c00000080000000004002c00100080030008000000c00200080060000007003c00000280020004005000800000100000010000000400b000000000040050000001000c0010000011000c006000000c00180010020004000000000000280000001000400b000800100
  | 39 => 0x100000080006000400100000000000000000c0000008014003400f000800a00340000044002000001000140000000002000400f000000d00000010020001000c0060018002000800000040000000004000c006001800800000010020000002800000000080018000000c0000004001002800100240000004003001c002000c0000004002000c00000000010004002000c00600000040008012000400200000120004001000400700000020008010009c000001000300000020008001000c001000000000000010000016001c0050020001000000c00000020018009000800b0014007000000e00180000004001000000400340040000001001c001001000100000060050000000c00100000010028000000800100000000004002000000100000030000000000c0000000004001c0020094001000800400100000010006000c00300000020004001001c0090004001000401500040080024000002c0000000000003800000a4024000000000000000000007002800200000000028031002c0020000000000000400040010004002000401100540000054000000c000000001f001001b000c0020090000001c0020004001001c0010000001001c00000000060000003000000600000050008009000400200140000030000000000b0014002000001000100090004004000800a000000c0028001000001300040000040015000400400000010014001001000200200070008004001c001000000f0008002000000b00000000000002000c018000400200280240040002000000b00000000008002000400400140020038000000000100040030078002000000c00280020004005000001400080020004001000800300100020004014000c001001800100000000008000001400700180020030003001800100000000000001000c0130008000001800100380010014001000000100000060004001001c0000004007005000000140000000000001000400000000028000001000100000020040000001000200040000000000000c007000000300000020020006000000600000020000000000c00200280000008003000800e006000300000110000001000000700100000000007000400100000030004001006c005000000300180010000008000800000000070008005000800900040070000000002c000002c001001400000040010000001004400100040000000001000400d000000000040010004003002c00d000800200000050000014006c00400000000000009000c00e000400000040020058000000800500080140010004000000b00200000000000000c006001c0080000002000c0000018001000401a000000000580030000002001c0020018014000c000004800800100020000000000000000040000020000005c001000400b000000200000
  | 40 => 0xb7c9ce87da0000000680800085fa8720709dca00000000000000492a7be17d939e1528b9a4151a10083a274b48a5445a6080811d8000577028c2620aa841d907c51aa47855f8a6000017b600f98a838317c6804800039a8000bf39e660001cca00002ce3440730378307836e178c83409660002fae1630b18b559c8eacb03aca0710f87fb920085b21d8022856a3ad1fc6977ae4296e000027b80002df03d81d89b5000014520a69af60000000c321760b5ba0d80002e500001b3a00026663a524302080b24000240425e17b4904a51e2aa9238b1a16262548eb21759b6e577949aa488d2c25085ec00000000000000be1800034a00000001cd41de09e03811d88b0e287032d24e236986b67d4800029680002399ed088719e40a08e1a6158a240608cf86220000000211a8d608060000000000000000000000000fb203d22ec05a800017800000000af40000000000048a6170000a728000000000000020640e910e43898000b5c112ca9300001e01a1c38080000002c5e00008c400000009dc00000000000c2785542732fd2000000051bae6c0ee084eb1500006b1a82e9f91d0600007429db0000000000091cb036000085e000000000000008be8ca0c291e340000f6cb8c227a81e9d74ba724b219f92da0089b365dc065a281aa546ea9d1ca85120411014822d81c5e11c97d21dd93d01e82a2a8980c90466a61222517de00025a6000302651d21fa3b000000001c0e81604107da175873b00001451e0e2b6909604f2d760000fd4bcc1cc01329b8e591997888000008210c86b8b18c01cf245c79e19d89ee9c7e0002d3c17080cc00026580000f841999688751800032586920001e28bd89a7a0001dde000000000000000000e3000000003788976000000000012648850b70000246eb1aae4a9bc230600014e28d42310a1b8dfeabc096e54d80006392be26ba9dbe1b9030aab6049a0000000000000000000009909d849cc18b0530000000000009a8110c771816833586145e39ed6609a79c51c300ca9797ea0000000000800800040010044002001400400040170000000000000000500040000000000000800700010000000004400100080000000001001400000000000008000002000300180010000000000800300100020004001000c0000008000006800000000060008004000c002000c000003000600180070018000000c004001400100240100018000000400f0004001000000b00280040034000000400a0008004000000c00180000014000000800a000c003001c0010000000000000600100040004001001c000001000000080000004016001000200180060034011000000300000000000005000800000040060000007002c000000400200040000000006009400000100090000005000c00500000000014013000800300100000
  | 41 => 0x71f00005fcb03e69881d80000000221000000030da4e68aea6982c7a93b1db4000145400014d200000009f3877e444a8d2bbc07000348000aa7a25848b00003bba8d05da1f9819c932c71b308c3d526ba81712c0b35aad068b900c0e814d48028e5abd99cea65716a619214acbeaa35465faf2aa3d00000002b428a8033a6e58ed2ae8000019780004f28000baf00003ff1bb838a017ca9a0f4490b806616c8386219000031900006c800004890e0e1f9ac04a942cbc44c800000000000000000b979b7a00000000001c8c00008a8ab89ffe91216cc0002d5224895b20992fda000274e50f8a0c00007fe30485409992dfa95002e80001c728f318444d38f66bf8a4da0000aa23658bd203a1b10000056800009ac00027f40000000a85a3d448d88d03e2805a0002808b1813c400013102ad8000510a66a3e211160458680646885c0000000000000020e283c106221aab2110a36915ec00013d6013a6c80000000000000000000004a285b84fd2c1c96aa944884215691413cc000000000000002b7000045f95a89cf02c4561a272000181200000000000c9a86c800000024be000089200004420000000085000094b0000000000048d01f4641222265ea22800030b89b60000ac2000092089920a7176e00000002c194600fd817e69c1e5e0211c9c9c79be40001cb60e69fbc8df0c8a0001e9c0001c1c0000ae41408000a04ad863bb000000020e80002c5a00000001171b8c0002fde3a788885d28000be305fa0000bc80001d7600000004f200000739b840248000000000000003e41b58000115293a0000000048237a72f800000017067feabb4ad3000068f8c2664c800000028249ec9db859e285a00009f610a02ee8b780008e8a004af380009989cba0000000000290a552a09e1bf16a882e9bb40500000000000000029d60001e6435e00007eb00f600008580001c600002c4a0000058377000000000003528d24ad39e964d5a9f28a4800070208c2a4fa1b000019cc8ac84006da80007080c3c988800062004b880f1918988298234100008e599fc00022884d18000b19b0b400000007941a5e18780003580d3403230743d5b0d0b472b30c1c15b0ae69eee05880003960a902cb95400002798000000001004200002b9e74527f68268000000000021a28dea002c7814590507c2941e6e180007e2acf8b9f815c67795a05fd269abfe18de0190b82851264c1981c0a3172cdcbcf800015f2c0e3f480000000b76205164000010680000d8e84880000000ed00000000000000089123dc3e0800087e0f68b1b00003642fdc000091c734a3ba00006feaaf8ed65ad0684000260600000140000000017000000000009fba4b032b893a7538000ba089f26848000848185a9e580000001d3c0000000000230c00013e047508e83c206c256d225e9082
  | 42 => 0x8e7424d994c000000033f852a0e5000000010922d7103c8ae90e28b320e21d1afeaaf4029e39804ea9b8213a2ea8000bbf800012a1e7e597aaf458f0b22902000000017cc00026a8ace00000000d2e47816b8a1e9ec83da930620a0152c3282947a90c181ce87226ca8000ba626e65430f0400015380f80000000000000020c619720980002862c0100001379bd485a1e08714281a2b091ea7251e90610800090f00004cc8fbe01f08747261e2e0efaef47f980000002d4200008ec00002f61e3800000000000000000000112a0000000a5397ca0001aa8000000025ca2e8a212ca28a12a9c00016248a7a5dc16b1ee03679d600002e8664ba91a13b80084b72ec65fa08007be0234a26a58a12f2f02b0912d403080003801a008cc04ac16980c47951094357856c88e1f480001390000085a6089600506a8ca6d92a127890f260002b36007886c6a880000002eae36c000000d0000b2b0000000012e000000094412c6000000009ba56650c8000000000000000004e9192c9319b269249dea0d92fd600020b063e013a00018b200000005e5800057580000000dee0000000a6622f4b512c320002d84000154c111a6680cb00005f580000000000077209c61c8b089608f1a17a933e000000009f0000621a19200015f600000000002b20baa29c07330cacbd20000a4c21908671800605800000025fc49d1380ab520221908000791af8a000000019e80009de972aa61000083100000000000769800054c1f500000000b4380000002bfe00000003e3a24a225800000002b4000130a0001f4455080000000000000000001e00006dd87fa000087e0001778973a0f83f90000c0800000000000a5c1d70a388000aabafc80001114000171a6671a4256011fc34804508f9800000000003c000007fe00001da14f2b37a5ba67e8a500401d7c8afa1a800000000001dd6b5518520000e6860a8000a8380000000000287902c0002c02000265a45ead16b76905c000000000000000000d489260e980001ad44a09d9c18e94a0a5ea8c21ac800060f0018000000071d2d980001f56200a17c2f8928831f2f6c60185182122524a45206e0001cf8a16000095680002be09e4c2a0b5e5d20000b48198400014fe2a32bb636b0d3ebc6aac200000a0104a67c4a000005118bde0002d4a00000000000de8497800098508240000000000000000030d600012b45288000220996a00000000002dc6000224818b908c80d000028224ca1191464934199e00000004de00000000000000000000020b893c00000000000952000000003bc0002c5697e2e4c4ab898400022c875880debb3a0681c4800000000003e017e20000e7c000000000000005a1ac08810152400000008908000be91ff200012be706993e9298000000000032f13bc0692a94000068c00000000000000
  | 43 => 0x800020700002b0600011a600020f408119c23c897ecbdf93621a890c80c68f3a7e39aba0002f4a3a701ccbed92128dca22a81288320e9a3f83a900009ff019a48b8000a9c034c000154ec0a037438400004a916600478f4c58080943f28000bc50ed80000ca22f5853471894bc0001e620002b8a0000000b5e80009d4b0c45d900000000000bee00000000000000000000000000001b382e50b6610b800009e000000027320001e30064804420a8000000201e00003f400000000000000000000000000000000000579800000021660002940486ab70000000000000000000000000087a9d2a09400026f40002de89bb871047f800015d9916695910428a80008c6144a34aab1ea39000000000000002f500000000000000007b884463dab8497b8c0a89b800044f285c00030a60000000c0e923200014f800000002fb87f400000000002e8400000005958000c25af1640ea9e494607ba078071c992222e789a5e887b000000000000000000000000000025b698c897c0002afe8c9aeea4fe8bb681d000000000002a518620000000000201ab6e868e0911b4406800000389b0000002089ac800000000000002df066b80000000000000000000018da0000000000000082b90b011d1e060002c2800000000001cc2647800000009ce20f27ac00000000002774ad1800089f00002ad1e5c3ef1636000254ea879ab600029ea01f932a23c8000000000000003900598f70623b06047b1f3ea242424a7f1ab08b81fd64e700000001b989dd9f349a5111caa686fa000000000000007f300000002e00000213632d84d41ba0cda02d90562d09efa03924143472c2c029168416f1eea6911f9ca0a102e00024a0b632b52000000068a8732c24a464000231665218187a9800000000000098d98abe80003851d50228a3520eb800079803d695426742b58000000054e0000e7e756229618999909c721d221f2e56a9f224c00000000002142513a65000030de14e000000000002d92a747061024bd100007410000459800079d80003cf26d482c9dda0000000869af2c0002fcc00008ba4b9800000000006400dc63b11342b0b800000000000001c00841a9a03f302426bc00003dc9a7496f2442000000005188d863880a800021ccb7601ea3af1f4e000193a000200c4f48f32000000000020a69009a2467d30981e204aab600ba2c130b1e0000000a58a728bc12f200d79218002af909982cae63318f03a9af88af5a6d2bf8088a76585d894581c600000000002ff69d51abe6471e00b91aec80000000311800089a00000ee80000000a8e000056400018084ef81fe000128c000214c00014c49868f9a697134c7098c1a156169677806a67ea07500000a9c87da8304f9800000000008fbb022be5a1da1128a5c0000e4400e26dc2cf8bf60fc8000000257e733
  | 44 => 0xe18f2193850e000031066327360000000976a8808350000a198fd000000009860d583cb058663f800015e80006eb800029f908e0000000a0f9b4c332a6f24d280ca982020a00000002102ffc55f000096500000000000621114808815628ffa3b69528000000062c000000000029f871490d800001ba9780ca6bab101c0001a200002212c019d3600000007d9036c00008f430c926064a0024b9a00005fda3b80000d70a57000060509b6113a6c2000223637e8b8a355166245a98787e8a99e40da47a000123000021d48dd870a000000000015503889358576000052480000000000bed00006f800003a5800000000004089b945db0b583e42b28000022e62b80005b023340002912090176a0000000000000000000000000336767acfa53928f8794b000000000094f00001b680002fa937c1b517384368ede0002cba000028e00000000000000b87821a644158a2238a348b02060b490ba60000b30000093459b00006e8af820b8190a000000034180004d7000000005e200000005f9000065a07b69c92fc67638f40c3aa29c23f2418a399ca2245221eb6d17369710cf6000190c8281448a6e000000015d48a2904217f242c6fca6d054b96d867e00dc2668a6a00004020000bc6658800000024c40789d0a5e2243ebec23c21822c8a000000052c800000006568eb2902bd09bce2ac18ac6df21be05d00004650b90000000005e00000002baa6b3800000000009e480005a3064c7290e784a48000898859ca5b8000a8d08108f380000002ef6b8485c0617800012b96ca7b48000000074a80ea4165570ba4000000000000009ed0836a3002da9582398402ab14000072e968000c0002d0c86290584c096ec60ca66c1c516fab3318bec2c0404778a91c4121c5a80387926d82988074aa3e3ba8782188852c54700002b000002f38e18bc21c5616580000000000b1c08e400024547fd000019d04c69f08000a4bb0aea0982fc000000000000005f7114c4ba900e759800040003484748000878194e125ae0c9b91e8870a0000000000044b80009400590000097498b0000ad4175c5dd142235728f2560956ab64a3d019a205a17785240001b34afbafe40001e9e77215c283203d089700000002ce232115ee46f8c50b1f0b748241480b7f1e841a79af8683233883c840a000000000027f00000000a2b2ebe00000003fd140a00012e872596ce9e20344b0d1cf01f88d685df1b169561eaa2ba21c409d183e04b0e421710634ab486c686d2b4a2a184dc49d81b66d4a57a4c514a81752a6e782800005e826800024fa7d1988c6b998466a3121e00020803e48000026800098f80002430caa00000005270c6200006f42389bc67c18958656800000000000002f8400000000000000b7500000002aca349941c903216e97c21120001d18c20ad484dc891
  | 45 => 0xba0151ec629c92fa3b927fe8230a123b205288dd289230100d88898000000104600000000f7800000023bcbaa80000000000000000000019125e00000b2921fe0000000000249e0002a8232cadb800026ae00000002a1199600003520002126294a252b4e000027c26840540b0e0001e6c5791f9e000000000027660001be608f155aaf11a5200000000002e5a9c980004af0b8c9b5aa8a000075e456257c5b22624b7e2686000000000000006ef000037e00005c59d5c00000003fb89fa0000dd00b92d1a17f8a38bb00000b590000000000020881ec7c52a480001a90000000097d11d000000004c623140000bba9381ee658490baa7c27942841d2c0002c2a000277e14d8c22c19124e000000003a8000000301600006062c122541091efc7e41ade000000058e0000bfc80008c09dc000007b22999fce7c7213294bade468e15d22872744280a8480001dd29ee00004bc80000520000be8800000000000002fd050405ba912a7da0002b9c00000009839e4e8e08a5e85a9338bd4857200a80004b7a1aa2030000a83220aa148fb4ba49da00000000a80906401488b49688dea21a8d4e8c72444000000082900000002cc200000000001210a8c81aab5b03c036110801ba80009bf92c2319af0c40692d2000000000014fa766800000007b8000149e0000000096000000000000000d924dd04fc5009f6e75b143810c1a1418c22ce61f1f8c1ca2e3ca73015e00004580000dde25586ae58d00009fb07be1e281045bda584000000000000007cbab160000c0600018b41a1adaa1fb2dc400000000002b6e000000000000007d29d4a8e78968b192e5823e8f5a0001b023b1800085500000d4167e3be00006c78000000300e22e00004422b8e97b2f100182b4835ea7144c02ddc35ba63852906888b7021600001080d08c78b451f74310811c00011b4559106a0b00ad02f71c4a47d8d0aa2390901f2a53663390400931cd6a9083a82ffa7400da1eb20a02dd07b3800067b86940002f7a8bf800003e07f800000000002276000000000000000002a04af6800058118944328000b79823213b01f600007569ef1a86030000030fa2f006fae7c0000ef200017009870000a841db6877800014c000005680008c880006bd260000000009788000bb70000000117c01898a20000cc40001b0c00000000da9d020000834056000017a1f8452aac886b81feca151898a3e9e8cb4c10d4094153e0000000aa103300b5000035f8c28000000000000000000000000000083c2b028c69458c0c80005840ce47ab847804e04849f22822921000021580007ad000000010b652d80000000000909800083b05b000019827198000000000000000006ae207e000297600000007f290208b90408c3c27d0671856222900005aa914a98c0da011f8c3ab6904a2b64307c85
  | 46 => 0x29f01807f79f0c7cc09da2728000000017600000d09180000087800000000008a6800000011180001a546e7a0aa967875200016749da1f92736198878da8141f0adc030b8000852269ea9905f25211f2a379adb0a6706be90d2d5c3c4286a00000000000abe00030a2458000025c060200016ba675825a544a2900001468ab9079400024c8000000067500000000616000095e000000000000da00000000001b92263064000003f845924d8a4c853212516c28f1000000005da00004c40002312839217612417820002b344f0adec06b21f263e800024400000002c064dc00007ee2956000169c5ff8000169000081580002fc9d300840b1caec993000011787b617264182bb06a293127422e02000230e42200000000a7a0a8800016888600002e288cc8a9e860946c00014b4b0d88aab0523087c41e1ca2895660e0ada256499444a8ab2e1b2161a4ca073e2eb8b36a1e162cac610e0be502b68092cb46f700ac18c8000020800000016b648380005e483620000000629000012f9b2832ea73861fa7aa00015720002a3c851a104bc7a32a32a1bfe0000000be48e2ea68838a00025ae0000000a8c00000002ca00002b74000184884bad026d6069811f0000000051225e9f327b01d78631acd260e90066af0bc29c5938646900006c2942e71700000000000000292a000305a000309c00028fc00009ae1c58fec000000024987aa5ab94406939b5e0dc1ca0adc959ca710202afea446923a6f62a6000033a0318000000079626ca00000006839f86b4b80006328000065a8e0000230ac068ef66cc000000000fe98092423a3800028b07b0360a84042e14260003066c2385420001d3a0000d50737199806100002eb0000000136e0000000b20a3480000000b69ac5c000000029892660000000899ae8e4128c5e00000000001cac0000ce277c8000535800000001900001dee0000000c3a05505e11d2000027c67fd800000019da9952adc0002a3600000f00002d065ef926c138a33c0000000000126800000002ab8000a5f000033380004919f3611a80005548384000156e58c9cf4000282c09c9c1010e8a180001b2c5860000923000000006440000000496a8b06928df0000000018f80003e88000b5d04160000000000000000000000001e2a000151a0000e4e6e418d446c04384ac2ae800029d05402278000299000030d200000000000000bf297c869d80004d68488666992431a8ad80000912c092d285b4a0861bb9c2c5e2b04013a2aba6b916067211dd8961a3a83f628e804faab239180048e207ce8eaa01051e8000b26a578aef1106668294669a00000001728068947200000008cb000043a0c824228000a9aa88200010f49f00000b3a80000001d2e2c9ab56289802e15f99c089a8fc66860876bad8850a418ff059280d6a2a86
  | 47 => 0x2b8682042cb4fa44eb6680006038fc0beca25a000292400000001cb000035c92ca9c4800000000002da80000001c34000247c5e90eae00000001d69ac00002ce04b880002d42c3cba68000000277c000000010faf6a00000002c4297e000234c0002f400af23f000002e200000008eb8000000000097aaa80000000000021e40000000000239200000003d3800000023e84e9808e157000069f00006fa081e7cb0d5ab91000066909b400027081b30daa0aa000000028d886d97b88fdb0aa0000000000107a08f800000011a8a35036600000009f5000077e800000020fa4622cd8c020ef0ac9121c205800039480000a28000000280e6a993f22698000b0293880000000000251a85d21f076600000002ea60002c4c6b42b3e3b2832681aaf5c5ff190274925ca00010d26d88ffe3d8800018d8000000000048a800001aa41000000000000cee0001e700000314000123ac201dc246d80003b8137e1c30000070184a000000071c24560000000b8403e80000000ba59fe84d9800031d001a59ea13e00000009d6000021e0000000000051f1e6a71500007888470b5408549e9026232728100002ac0af780009ed960847d000004dad2c24a038000016680000000b9bae6600000000000000bc18a6e12019460002b40143000000000000002b003a100000002dfe00000001b880000000a8a57403b642d15b6043800075ea12c116a2c200017e69ad9b1800018380ff835691a82ca7ec2164be702b21bc215aafd248012802280000dda105000000000003b301d65e780b20002cfe0000000c21800000000000000000000000000026bc0e20000488076473b8e389c190ae0002eee27b18eea6f07a806e0c30b3410f05a4a570000000000030c000000005622a56739159a8f280000000b7895b09a2041ae526d9800053c000007e8fae039800000000002fe0000000000000000000c71afe3c7044c8aa800000026287160d025052b60000000000000005ab26268c900000bc000030d000064d0924893ab58b47ad12165169e36eaf2e2650b729a89f7ca1d129a4d10164a6690a201584ba1182f647a5000023a9d1e000094a7108cdc314aa208ada572433ab806a0024e1d016288ab033269fa07c52f83729a58000000093200000008f60d3a6b89286000000014700004820bca00024cc55a00002ec2faca412a22a801fd20000000000042600009020000000000000000007cc0000000bf60000b3c80000000000000000002700000001a72151098e220220499192cc303adbe2938a5495ba6c6866a3da4f3967c5d00b48a8b00005dd80001868dd80000758274800092229c600002965ebaa8c08e086e7908000000000000005a88e50000bf0800000010988bf1f16000055a00024f267a0c449fe2580743268a7b5143400000007248000a3f87980
  | 48 => 0x17b80000000000000030e000000064f2fbc00009f80002ee40001b746b2166e4cd91cc72280000000be682f04cc0001cbc73199eca272dd25cf892c2b9804a5ac1a9844d1ebeaf0a60a0000eb60000000907a51cbc9308aaa4000091dacb0000000071ea24093e152a0628000a3a94789660000682974c2ff30728121e8e8300000825a41a52bae8c000210e46115ae628270a838000029da4e42ee00001f19c8072400000000000000000053d17d485814ca00011400002846b09800016bab3a54f27dc0000510779296a00000003829e725610000000000000004f01fa80000000df648989e261c07d22e81bb200006ac6308000ac3800000000005a0ad405a680000001128bbea5060000ae200000000000000abd98b642a309a48f107ea2e99a852e1964b249fc4b06891e3a2a55e1d12cc84b4032a3220b2c8021b7059412ee000000065588f08a500007d3080a87380003be8dbe0000000902ada0b5809c200029c8000029027f97ba6998c5aa45a920000000072a2bb8000115400028ce9798be89e12f5a536843432c095472e000054422d48018fdc00000003621828000000031d9bf80001d8a3d91cc4b1380005f00000bfe8826000000000000008071f8037580006da000000000005460000000000000000000000000000000000000008610fea0000e6420c0f36493000000017240000000a549f18587a610000000080000007d0959e4670b9c1de99f00bca81e22f21ac29b0fa465400004d51d107a1822c51d99aa54204c86b28000451013278781fc2c68f304ee835c5e60000bb4848cbdba7d299eaba6b238c0018728bea27800097e9f964c70e1c1f598761f920f60002e140002b6256380002e20f129cd2cb20d280004b3800055781e82411b0874d1f020b60000ae9294aa2a2d94000000010f2c7e00000008f200000b786286f114369c608ac63b00008ceaefc00005b40002896a6280000001b2e34499bc00022e6861a4b8be60000af31534358a50233a80001ad07dc000247000000003df13b69ae0b0200018d8679a9fe9812aecb882ca880581261da82cc737942c00029ceb9809bc000000000021d65852c461149b3cb3b0000aac30c6a4980000000718c1380001a715c84ffa04424c00000000c9eaf90c0c19b0000a5d170e000235e96300000000c8e88f2ce4000089a000000037f1102661a43600020545630000b08966445a00000000000c062e4eade1ef00002c6eaaf1bac0bf959400000003ec09c41300000c16000000001d4000000000028c600010ec000000000019a23c080002e10d1e000000000023801d39a6a2958000aae00000b5a9867e693a20002cce0000000b6baa1a00025cc35093765371f040000b340002742af2961cb89128e0002d96842aaa61db964855189d8a7d0e5c04a1fe286512782cc8
  | 49 => 0x67079c91b00006d39520bd782f81f200005d5805e8882c20439853e68a1c1400017a8b40142a4bd2c0c117939465094164439a345eaad7e29907087af07b49f2800031f95c600000001990c407858000641800075b80000002e5c93711b2343af00b8b96ee334301e2930ffa8a08d401948a687ada4a400017423138d083de15ce5a002c6c0a80006a821242c800000002dce2810000b9d80000000000631000060b9c2a00027a200014a600000000620de4af81b823bd2d882480000000000642ca7506ea00002918000000230000000000001bba84315be00027de71a8dd4ad980000000000413a88600005caa2c874c62084da8de000031e80003d20b7e00000000000000781000002b80000001b484d912284498bfa0000000591000038914860001dbc0001f1e4050000819800000000006651970be00000000068270880be000290c3b6868a6f0124030b00000001da28ed0000b829e4cab1895090e8000a8a0000957223a000186033d000000011f801c037e1828aa600011bc00000009c3800057a800000001421bb2f3476c9b9a773938c0c08e86719076c871866a099800025b00000001ba692a000045c9a8e5f1000026a094c00019a61ae08d4000000008d929634c013476a00008701182ad90102c170000a99806823793ecc0b00000002ade00000002bc8a00000000005300005b81e3a3518000a0c96420a900003d280001412b5c9d719f25d392d63aeb0e22700db6c120f6e0001fbe6381f6c8d59ede0001e4a0c79b8a0000000000000085417141548000aad80005f0aad60000000000249cc3300008528f96a77b05080c9d420442e1a6d50e3400019147488b0a0000000a9887e8000000037120ee3900aee97580002af00009ec000071e28600002dca00001bc00000007c3a11e6420ea2659846e00000000003068000000000015fc8459c4c212ae940000e16000000011b1aee124970a1b009b800023ec45480002ed0000000000000030bc3aaa3868818c5424f0000000179000029e6b4d906c0001f24000000009f80000001dfe12c9b782a093309dc917436c9874997b01c86f0e360001f8889b0000500000000029e28e384620000000000000095180000002b220002b7a992a49478510527ae121675a122200008b23ab232045d80009c300008f7abec0002682000000018900b80c59bde00000007e080c668b1e1a593033ebc3a5a877f1d0026288f66f6150e4952c942e00000a6d05be9f30ed40d02ee800000000f880000710000000000008608cc00013924378000555303c00000000000d6aa1a1a2600000000fa800083a80000000000bd59dac0001d1a0000c100001c40a54239070f0790455800076c2a76976135200030e08349d40232000000005f838f8724af71952648000000000005fc05820002fbe
  | 50 => 0x25bc80000001b409e280000000000000000000000000001a88000000037d00000002c98be819f600000000001f60138000000000006f4835a9a600000002f3c65d0ba80000276b7880003a80fa6abc879a60d9e3866fa5ac000213000022b44c7852000000000002e38bdd00000001a3000000ec05b80000000c980f30000a01800000017460000000b858000046800000000003b980000001840259000028e83e6000000000000000000000000287c9cb86387da800076089dc6fd0000000250e00024668b425b423fa0022b10ff69ba8d6432000000002b960000000000236a1dc000044e822400000008b1283431200006151e9a000038c0ec2e641348998a6e91965c6000000000001c1974412d8000bc8aa98867909c6259a3c1620b6e8d8aeb42260592a6c00007ea80000000000a6f8f580cd00002ca000000000007de00000000000c1b000000000003130ece9db9e1020f80000002c7417d2e908be00002a4a10814b800036ba596a93a4009c4000000009a400012701ca84e63ee9f58ac2979c35d0000000159600000009f82f360001f285b5800000028185f80000000181eb7d8a4a8138e2a0001c0c8288000000000000000000001d8652e8e0649e80005bf20b61f6000000000001f7800043087c445b000000012f6af480000002d7259c8a3649fa53a1b603122828f767208000000082e4eb9b5c74a8e3c0000c560001dba63f1eccb83950234da28e0002592b259c1667f9e4465288ca000300a74e1b5a57120c281c8000413127c419954881400008d1000000000001dd21e800000001b7000295912944bc06620000000b460cc600000000002496000160abdc0faa1fda6b4268000000023a60a98206000000020ea888908914ea8708ae00000005d8a110a82000051880002ca80000000000a600000000000003ca67e00017940000a20000000000000000001940ba81262aa90b540b49d9200000005f42dbc8d18620aefaee296c9d3e4be02000000e706fda68e33813a09d68000866000055ea8dc00000000c20000000000009587d454ca37e3058dec2118e32000305e2602d82a47800026c2ffe0001fdc2d115e0ad12e7a38480002beacda00011980c910fc00000007bb1e320000f987770000000000000029d8569a4b473a000066b2f782d698b800025c69d92972674170457c9ebaa5680360002db61018000b531dcc5142d5ea749bee36a22a29d802463f98d327f22680c15947ebbc8b4a08c234e6e204b035d8ff858e8fda62413e481197da2d319b26711b0e0260a40b7ca8c4373a9107b2aae670b970c1b4167646413acac48c6c1c78000bfa0000b5f12aa7bf8000bd629e0000000000000000002c5029e1eb099e2cb80002d10000034669622ee970800062a8000954800000019920002938c33909e0000000b16
  | 51 => 0xd81f873f24ea35f00004c80000ae1800000010700001bc20000000000000012988860001b0486300000001c120002c4428685e63450af60001bfc0000000000095c47226ac00000000000000000260c00000000000000a57923e80c2e180001ca61d217a64cd2b102ef85d27ce09380449a041ff1ba08cb8b3c9cfa4e84680c203e804d8822a2d2c370d38872a36e4ec1a166bb05e400020284480000229ae487f022983f115f46c5300210daaa08e716e89130dc853400902f019b692286183ce15b802c218047587841e8afc035314ceb218edc5fba56244418eab810d1a19f240e06ca3fc57f8000994a4d44bf9ee400000000000a42000000013f80000001ff02fd030ca8b80000000292bc2914200f18f4000000042a800078f1ef4ac7000043fa406beea63a7d99dec0a11f1a3cba03800000005238000bbb06100e700007c98f6000017669c100005df8000ba0000000011aa00000000db800015c175200003200c8913e36f0000000000000000000002a4600007d02c480001800d667c82aea4fe2d8e00026da000000060c1258000145e91680000000e7657a2d680001630000099e0001a965af150a1271c0685e8546173860e0550e5e98f00008d71b1a157b0386248fb87b09c3e000103200009b20002a44271800000023c62d00b989339c469070000696965c146a12a000282a4fc00d4013000000016c637480008692aa287f2d3a0d5294c44e0000a77097eb4aafa8b89a79e8b60bd8b100000780ab924e5aa960001aaaa769d727f527a8508274c87d247e85c800094a1c020b99d900002fa67cf016c0001b7e43011b8b950d9a1e91daa87b82b09d185220001d5a94507f2b2aa4fe275a89809b0f18a6900a286b998042913eab8890d67b696f85de9670aab2e4041124401261ffc7d7184e4f51a84a9715145d7af1c0e629b252202ec3ca000073c8ea8b58800000000000001976504a1e600000000000000000228ca9000000002140000215c058000000000001600000000009e21c9f000002b5a30218d073f81b4941085268e8000ba2800000009ba7dea9585e68a882582bf661990343e312d8955af18622a3842a580001638500388285e4c880009eb9fa48d287a60002bea0002b7e30900003dd30d88830a2e1eb040e000192204c000000017fab5614940002f680001b12a292e6249580007f80000477800000022ea23580b42a680000000000b2403380000000b7aae702b32c84072a0ceb2d92022a82da80001a36033a3f4000081200013b44d4000000000000002cbe15307360002b6a0000fa843c84f860105982f8070404a9ef634580000000000c28000000011468f918508af26fa04600002b4a790c2da7f274480004aa1100b62ad46858841e4a1042a09529a80000b464ae2820b8a998e0000000baca88a0000a3
  | 52 => 0xc000011c427f235a0de075caca8048000298c00018682d3ae6a93f02ae4ad80000000000000119e0001c686edaf12a948bd03ca9df4bb502ba15e28f04b810020baab820000000b05add6206aff4a65a8386a0a2f631c8e5088f83ce61ab07e57000001c099ca0000fde14228f60000000000051e734202c5412c52000105a00000000002a925a90000b4c8000b39aa4a16a800000000fa00000000000cf2a4006de000126eb0f969415d156c0001cf639c8fc89a90f2053800001cd000099c29f665600000000000a030000840098661603ec230014e0000000b3c2948a9e1e2000004d075300004ac86d29f1000000000006c92d4e000000000000006f59b5699c925040a25087548d860002688000163e0000032c110e6e26f8d944fd8000000000000029ac00000003c505846770e1ea2528160001324b670000084ac302e195cab1088903632ca6236800040994c8aad00002f31cb49a7005000000007eca69008a896a03f17f8000000069b800000026b090a2a8e00010742039aa40a624bc0000000a9b06906be80002c52cf693781f22b20000b0ea1020001b80288aff0a10800089194ea24b800000000003822018000284425110cc42fa9a644d85cc3e7aa06238000073800005eb1c4875f800000011e8123800000000000002f723e5000000024324ea000045c000002a80000002ed0bce80007a003f007428041088000000000054eaa860000f9c8ef912200000003c78000acc8000c040000acf2452a6d800002308f876930424a417ce00000005330b387862dee4770000b3a22a63ba0000000094666e070e00021a261306f63ed98e6ae6000000a0000b8e8b56000000056896dc1af2c721290f0c000245e779a5f200003dc00000001b2800065f000000000000dd80000f5000055580000c1800049a99544ec800000000000002c1e3a41ac44c300000002b0c000000095a00004c380000000796a331ea85b1279a606a9fa67808b60000000000272a0002eda0000ace0000000000259c00025b0000000001d000000000000000000000000024a98645cb0000b0400006271a220002188ab6800000014568b18000000000088cafc43d7800000000003d4262a60929340001dd400b0000155a5c058823a4a461a401aa1d165b92c4856a9ab20432b5eabb84824c593aa4ee00a6a3b11c2b3f2640048a042c0514e8a7b2cf4c1d8000afc8096b2300000000b920af8be43cd0a5806605f0000000070900000000b160df0f5c882253e40f94c600017bca50800046b8726c1a8000462800095da2a489c15066f427a080f9dd0c2e800093bac8093d22ca4298000a0d9ce6000102a8e80f242ac8000b8d192681b000040e13de4718fc202e8e3a5259b4a00012446dc8df200030ee3eb10a0895800075a81ae307adb219e00000002f2643
  | 53 => 0xa003c80001f7682380004b20000b18937a067a76a141a0cc5ba8000330000000014eca70a304bbe2d08a1b02d04db000000000007f92782000090600000009c68000000250a1eb8000ae41720000000063a00008368b6c1ac0ad43a48a2892b800043e89e600000003e1800009aaea2000236860716be000000000000000001418000202e01ba1c2000000035593fc924234200000009a9800089fa65616d8d186918000020000039582868cf94b05199e48b7091a2556222457c2a7e8538000000264493da978a648000240308400027e60001ee86081bcc9a32b8c00000000a8162a33b23e24f70cf01950c6044907ee28c000030da0926b680000049bec000000068ca9ee00026aa0e8a13465b10780c01b1c77a2994602965883f86aa69413e872baec40001e400001c320000000000094e6c8800000000000001b0658326e25b9800066e873800020782b78000000078c000000012180000002520000118e5a390d027519b084500006a4a8ee01d97b03ac27d82bf86e64f60a483df9f5a20119c8a960566c0480008f000000001c76ae20000bb78a743f8acee1ef11ee00000001a6916286e836005122a8000000067391ce000058a000000000011fa4e3800094c9ee21771bca8f4ad348d9047a9b3272c3d48d9c06a1f723cf9c88727a588362abba6322eba7b1189a1c682522b19d285c7018e1d5149832526ce04508701a80d0c4479690324a84c9a4a43820602aaa35ae9e3a300001b100009970d00a89a53423702c850a15a492a962e7a6136a7a8a21691d16f407780000001fd0517000020b000007c000030a8000511065078b120a5ccaeb800000000b0aee6000000000015167110ee270100005b680007592f8e818a280a9c80eec1b80009668000000000056f000000000009358000a23308811a0000000000035b000027780007c223fa953138a8fa8ae0402064a0529fba17223e0abe00000e39072ac6800000026c44c21f3aadb000026400002fb1caa5cf2f9a0920088a9e889c86e1cb26fc0046b00086262e82225b7a93680aa5a477c250c4cf000042680000001e7c5cd000079580000000000476041c00001a600023369938000a29800074c93482ae800000017102a900000002ba2072000000011929e980000f080006008bd400006f25031af20ecb04a4e080005768f060000cc20000dca000000088b2bac4600e483929a788378156000115043a88be00000007bcae1c33224a206c12c40000000000059e08e972e84e1a0647880006ef800059484f279eb0ec2741fea37092a63fc9f946a711e4a9698dc558293c73eb0b200000000001e12a1281e67ed000097da0b4aff28644c68b8e84a000060d1c8640c2964250000000000006fe800029c000000000005b51e8a0001ad6c241598808239a0000000bca1012757ac
  | 54 => 0x5287b72bf09e1929c4061ab425200001198c388ae11e6a02827a61b000087700000000000089800000000000002d780000000000000000000003a22cc4bfb0c1c0000000000000027a8a162280000aa21ac24922f7647000001b800000000000854a9682c3000096388ce00000000000f7a7a830628f5849ec350000726800024380007c480bc00000000000a3e00000000000000005a9aa0000612a13853aaaa8000334abc6083298ea1d850a1390d224d025542ce986e9d78260135a722a2e0e6cb3508420001be23360000bf98c8c61e860c00000003732f4c99d989e305165ab31abe6c1e80000000aec00000000000000a439c3094980007ed800000017a200022185731e926d0a1d0a980000000007a94aabae0001a9e5888000398841abb312ec0ca17508e30ab81a58000168021c2bf16d05c22a0a70e90c61f0076679a24e62e5a0ac0f196660000f0ab9c810a23184ce000115c56417a013d800097f8c5833780008c79d5600000002da1d94472889e000132e00000000000000000002060424c000000000000000000000000014e6000180c260878676000000002a3a31280000000000021a6c0000000000000000000000000108426700006fa839600030c226aa5d08ca033c8149d48b9d0e7a0001f70000270255d170200026de2fc1b9c40130949de091698b86701fc1fae061a5be47c83047d51fa000018d6783302e4630000afa0000339990e0002928ab330be0e4800050189622f6ad042198000000000047c00008208f426ec106e19d921400015704fb8c6e98d94ee4040c6866d03584ae825c74994fca0ea90800022da000000065b801032f9616000251277e256a81da1a07d015ac5e1888c00019d246e80000001544b820000000062a00000005c781da000000094e2c9c59a859a713943c5011a6c54b0000000164e5cc29540ea998a00000004830000857ad9ea009dae00000006b61d8c9fa957841880009e013daa368072421a2b028f066e4ab16f0207001c3afa4686298fe077d825e00e8fe8092a7e2c119f6223ba03650c00006ab0cfa4e626ec1b3a088a5b151e1c81408a2800000000e66000000036d22644178fd65a299ea407800038b173a5bf876056e800000000009188000000000013eabc02e780000002d5a95d29e8000296000009080000000707800000001700e78000446890aa2f2522926893e00000000000000687b0340000d528e29fdac2b00000001cb00000000530a1eab32b052af6000064a9e8200000003700000000000000000000000000b720000bd500000de8af00bd1ad20000000837171248180007f088b04d8000023490ee6cfab6833f2afc9642196b061eac0001a9a00000006f680000000000000000000023b26b319360d3800e0000000856084cab391da3c5abc813080004a600002
  | 55 => 0x27627510000634a13c699000088d0efc0000000503945a6cc80009fa044400025d200024ac98d00001581adc82f80000000c7010c95f800021e20000ec2c150000000143a0000a1400024ba00000006868000693000000000008461ce25132f9e6d180000002f386db2d6a7d7adac0cb95fa000000009c2250a3224b6ae530e4548925c4bf06f80a22ec264e2d660f115e200000008db00006ab9e6e0ed20a800c0000b8d80000109d545a8ad2652426160002026b77854805ca1c8595053c7df9c6e0000d4462f1c361dc8ca40651384ac114f60f481e479691862911e7400012a015ba2ae8d8000000002faab12ed80000da28b5818caea0000c399cc8000000039514de3a6a18e0000f0e2c023400000000a860e4c3602ae04d7a720bf52ed62ef148a10300000000e828132f6013d17222ab00000000124b8f800049c90dc0001c38a158000000000000027000002e889e392e400017b297900000ab27d6000000000000000000000000000000020e60000000000000078fa230000000032e000033500002f11dc44f893689160000420af4e80500009d2077c000000000002dc115948c42b00000ff16b2000175aa2d063c2d886a4283b030987a20e4f010bc43128ae0000000b04879eadd83ee65ca92c6f224d29bf22e20001a4800000000000ccc0f6800094c115a0001130196211c0002b26aaa0000a140bb24058000678a78c00000e000000000000000950800000000000000000000205e832800000020d63008efe8fc80005a800003ae195e4a7800000014d8000006c45baf7cafe00003a00000112095a5f617721810000b8180008808000000000000000000002a389d583ca2722de0a8909f4494a0fc4c99ae8457a48612d00007e98000b8c800000000000002286000000000000008dc00005498f468ec160e00000008bc800000013c600029d400009966bf1ba4a1f80005d50000b1d80000002eca00000000001d0e4ce80001f800002d480002b285260002bd400006467c8a5c8bccadf40feafee0000000bd1a6e8a6b85d03f395760000000b732c9e000296699bad0a7f614248d980000001cda000091a0000000000000000000009309a940002ee05b8a6be9be25d434f11ac90a8b7a4c12b54bac182c6582ea49fea170b9e28b627a00001719
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8f4865c4424400b3a906b88848801f3918971109100247c432e0212200387c859da32440010ff0abb4648800e1f215768c9100043e432eb192200087f87d9632440010fb0fb2c64880030fd96748c9100061e32ce9192203fc9c639d2324414fb28633a464880030fd95748c9100061e32ae91922000c9e74d8e32440031e90cb8c64880123e219708c910236e818ae1192200387e85dd932440010fb0bbb264880021fe15764c91001c3e42aec99220008bf845d9324402517908bb2648800237e0d764c91000477c12ec99220078dc8758d324400153908b1a648801eb3209634c9102466a38ac699220018f686dc532440018e8cbb8a64881621f21975d05102b43fc3ecba0a200087d87d9741440018b8e7b2a8288003271cf64505100064e398c8a0a2000c5f65dcd41440018b8cbb9a828815b1d1db6550510006aa39ecaa0a2000d9473d914144001c6eca3228288003651cc645051002ceb43ee6a0a2000cd476dcd41440019a8ec39a8288017651cf4350510024da43a86a0a2000de220dc941440818e8eca928288153551cd5250510006b3b92a4a0a20a7d9473d09414414db28e6a128288003741cf70505102bf2a18eca98a2086dd031dc131440b10f90cbae428815a1fe1f65c85100043ec3ecb90a20059d4835d221440014e90ca94428801f9998952885100062e39eca90a2000c5f65dcd21440018b8cbb9a4288003331cf624851000c7d436e090a2056c7476d952144001aa8e7b2a42880063d219744851002cea41ae890a20059d687dcd21440cd9a8edb9a428820f351d87348510006e239ec490a2000e6765189214400178b063124288003711cc62485100053a432a490a2007c747654921440a9aa8e6a92428801f99189524851002ee239c6490a20049e4874c921440015c90c9924288003741cf70485102be3c3b6ca9822000f5031d9530440917a102a1a608814f1e1d9524c1102a7a818aa49822048bd0814c9304414b7a10638a6088122f420e414c11002de841a829822000f914350530440917a10710a608800378dca214c11002de841a429822000fc13248530440af8f0edb2a40880127ca077348110236e818ee690220048f8865cd20440016d30a3124088002ea61062481100053c432a49022007c78765492044001cd70ca924088002daa195248110005b4432a49022000e6886549204400fcd6eca92408801f9a1d95248110007b140aa49022000f61815492044081cd6c2a924088103d8d855248110527b198aa490220a4f603154920440016d30b2124088003d854b7148110007b0a90e29022000f6152905204408d7a106a0a4088003d85494148110007d0a12829022004cf0768852044001ec2a510a4088006bc2192148110026783b2429022046bd083485204400fdc0c490a4088003d85492148110
  | 1 => 0xd0fb2ac488003171cf65589100043f438cab122000c5c73195624400187ecbba2c4880030f19774589100061fb28e8b122000c3c651d162440018becbb9ac48800317197735891001c3f43eeab1220008bf845d5624402517908baac48800237e0d75589100146e41aeab12200087e871d5624400187eebba2c4880030f1d774589100061fba8e8b122000c3c751d162440051bd0fb9ac48800317dd773589100062e3aee6b122000c9f74dcd6244001938e9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac4880032b1d372589100066639ee4b122000c3f74d496244001878e9a92c48800317dcf52589104462e39ea4b12200687d87d9462440018bce7b28c4880029b60b65189100062f398ca3122000a6d8219462440b18eae2328c4882a31e5c065189100061fb2ce83122000c3c659d0624400187ecaba0c4880030f19574189100062fb2ae63122000c5c655cc62440011df0eb10c488002ab21162189100056641ac4312200087e869d952440014db053b2a4880021f60a765491000636c14eca922000c6f209d952440018da413b2a4880028fe1176549100051e422eca922000a5f835d952440834b906bb2a4880029be0976549100063ac08eca922000c77311d952440018e8623b2a4880031bc8076549100063d100eca922000c6d201d952440010fd0f322a4880021f61e64549100043fc3ac8a92200087c8759152440014bf06b22a4881069720d645491000537c12c8a922007a6c82591524400f4dd04322a4880029b60864549102053ac0ec6a92200087f8758d52440010f90eb1aa4880028fe1163549100051e422c6a922000a6f8258d524400f4d904b1aa48800e1f21f62549100043fc3ac4a92200387c87589524400147f08b12a4880028f21162549100052fc1ac4a922041a5c8358952440018e8ed38aa48812ed960a71549102053a432e2a922054b54835c5524409b6cf04b8aa48801e2fa1276d09100043fc2aeda12200387c855db424407f53906b26848801eab20964d091000c7a432e3a12200387c859da42440010ff0abb4848800e1f21576909100043e432eb212200087f87d9642440010fb0fb2c8488003179cf65909100064f39ec92122000c9e7319242440018becab9c848800317195739091000c7a432e321220048f8865c242440070fd0bbb284880021f61776509100043fc2aeca12200387c855d9424400117f08bb2848800237e0d76509100146e41aeca1220008ef825d9424400117d0f322848801e2f21d64509101cd4e41ac8a122007aac8259142440070f90b3b084880021fe15761091001c3e42aec21220128bc845d842440011bf06bb0848800a3720d761091003c76412ec212200087c865d442440010ff0fb2884880021f61f65109100045ec3ec82122001
  | 2 => 0xc43d95100043ec3887b2a2000a3e841cb654400147b08396ca8800297a0c72d95100052ec18e5b2a2057a76811cb65440ad4eb02396ca8815a9ea0072d95102bd3cc00e5b2a200087e870cb65440010fb0e196ca880123e60375d91100043fc12eb322200387f87d4a64440010fb0fa94c8880021fa1f65591100062e39ecab22200087e8719564440018b8e632ac88800317d9773591100062e32ee6b222000c6f65dc964440018d8cbb92c8880031bd94725911000636328e4b22200387e87dd564440010fb05baac88800237e0d75591100146e41aeab2220008ef825d5644400f1d904baac8880021fa1c75591100146f43ee6b222000c5f75dcd64440018b8ebb9ac88800317dd473591100062e3a8e6b222000c9f741cd64440018deebb92c8880031b1d7725911000667b9ee4b222000ccc73dc964440018df0bb92c8880031b217725911000637ba8e4b222000c6c751c9644400195ee8392c88800333dcc725911000666398e4b22200087e87d4964440070f90fa92c88800317dcf52591104462e39ea4b222000c6f72d49644400f8d8e5a92c8881631d5c465191100045fc3ac83222000a9c83590644400155904b20c8881571d5c752191102b63ab8ecbb1a2000e5731d9763440b18eae232ec6880063d60775d8d102ae3ab8ea5b1a200087e87d956344001ca863b2ac6880021fa1c6558d100061fb2ee8b1a2000c3c65dd1634400187eca3a2c6880030f1947458d100064e318e8b1a2000d94311d163440018decbb92c6880031b1977258d1000637b28e4b1a2000c6c651c96344001998c6392c688003710c47258d1001c3f43eeab1a200087d82dd5634400117f08baac68804a2f2117558d1000477c12eab1a20078ec825d563440010fd0e3aac68804a2fa1f7458d100061fbaee8b1a2000c3c75dd1634400187eea3a2c6880030f1d47458d100064f990e8b1a2000c9e311d16344001938623a2c688003271d37358d1003c7743ee4b1a2000c6f75dc963440018d8ebb92c6880032bdd37258d10006563a6e4b1a2000c6f85dc963440018d90bb92c6880031bdd47258d10006363a8e4b1a2000caf741c96344001958e8392c68800333dcc7258d100043f43ea4b1a200387c87d49634400187ee9a92c6880030f1d35258d1000637b96a4b1a2007c6c72d4963440010ff0abb6868800e1f21576d0d1000c7a432e3a1a200387e85dd943440010fb0bbb286880021fe157650d1001c3e42aeca1a20008bf845d943440011bf06bb286880023be097650d1003c76412eca1a20018f686dc543440014db05baec4880029b60875d89100043fc2ae9b12200387c855d362440011bf06ba6c48800a3720d74d89100043fc2ae7b12200387c855cf624400117f08b9ec48804a2f21173d891001c3f436eab12205687c86dd562440010f
  | 3 => 0xa924040d6a87dc1524800f6d50db82a49001eda21b7054920206b53b6e0a924040d6876dc15248001ad6e9b82a4900035a5d37054920005b4c0ee0a924040c6e7654b4248001c5ec8a9684901035a9c152d0920006b4a92e1a124007c6f605d6424800fad6c0bac84900035a8417590920206363b2a4a124000e2c645494248001ad2a5b8284901031b1d9524c92020f2631aa49924000d6952dc13248001ccaa5b0cc29002e5b21d525852000697ba2a4b0a4000d2c745496148001a9ee6a92c290193531cd52585200047bc3ac230a4000e655258461480031d90cb9682900025be1d52d0520004b6c3aa5a0a4040d6a7054a4148001ad2a4b84829000a37a0e76505200046ec1ceca0a4000c6f7654941480018d8eca92829000353dcd5250520326a639aa4a0a4000cac7650941480c1b18e6a1282900021fe15761052001c3e42aec20a40018ec865c841480018dceca9082900031b5d95210520206b5382a420a4012cb8645c04148001ad2a4b8082900021fe15768c52001c3e42aed18a40008bf845da314802517908bb462901035a9c1528c520006b4a92e118a4000c6f7654931480018d8eca9262901031b9d95288520206b5382a510a4000e6552d862148001ad2a4b8442901031b1d95248520006a7b9aa490a4064d4c7354921480a7cc8c2a9242900035a54b70485200245e422eb3262012c3c845d664c40010ff04bacc98804b0fd0175993100061ea02eb3262000c3d75d5264c40070ff0fa94c9880021f61f52993102ae3b38ea532620048be87d5164c400187eebaa2c988012ada07545931000c7a40aeab1e2055c7471d4963c40031e902bb287880122f21d6450f1001c3f42ee8b16200087d85dd162c40814ed03bb2a58814f1d9c77654b1000537c12eca96200087e8799152c40010fb0f322a5881029da066454b1000537c12c8a962007a6c8259152c40014df04b1aa58801e9b2096354b102053a40ac6a96205eb54835c552c41576cf04b8aa58800e1fa177650b100043ec2eeca1620018f681dd942c40091790eb22858801eab2096450b10044ea41ae221620aad94319d232c40031e902bb265880123721d634cb100266a38ac699620048ec8758932c40099c8e2b12658822675a1f7350710046ca39e86a0e20049b48750d41c40bdaa8e6a92838800359dc95250710556ca39e84a0e20a9d947350941c40113a906ba2438821275a1f73487102f6aa39aa490e2007e646254921c4011b88e719243880127921d3248710004bb43863b2a2000b35840c765440016cb0418eca8815adca0031d95102b53d406e9b2a2057a7980dd3654400187ee93a6ca880030f5d074d95102bd3b408e9b2a2056a75811d365440af4ed03b9eca8815a9d60773d95100062eb98e7b2a2056a7a801cf65440af4f30039eca880021fa1
  | 4 => 0x3c80091e902bb287900029b61a7454b2000537c32e8a964000b6b805d152c80816d100ba2a5900034b5d07454b2000537c32e6a964000b67815cd52c80016c902b9aa59001e9ba1b4354b2000536c3686a964000a6d869c552c80014df0cb8aa590002d3e0d7154b2034da641ae2a9640008df835d561c80051b906baac39000a37a1f73587203362fa96e6b0e4066c5d52dcd61c80070fd0abb683900021fe1975d07200043fc3acba0e400087d8759741c80012df0ea9683900025b61d52d07200046fc1aeca0e40028dc835d941c80018b8e6b2a8390003271ce64507200064e39ac8a0e4000c5e65dcd41c80018bacbb9a83900031bdd9525072003e363b2a4a0e4000d4f7354941c80d3a98e6a92839001f2b1d9425072033ec639a84a0e4007c6e7259441c80018dacab90839001f1b9d9521072000636bb2a420e40668df835d931c80095a902b1a63900031bdd9524c72003e363b2a498e4000c3d75d53644800155b05aa6c8900021fe1571d912001c3e42ae3b22400387e87dd5644800117f08baac8900023ee0175591200043f438eab224000c3c75dd164480010fd0fa92c89000e1f21f52591200063c3aee0b2240008bf8759064480014790ab20c89004a2f21175191200961e422ea322405587f825d4644802587e80ba8c8900030f50175191200061ebaea8322400387f87d4864480010fb0fa90c8901571b5cb52191200046fc1ae232240028dc835c4644800117f08baac69004a2f2117558d200047bc0aeab1a40048f4815d563480010ff0abb6869000e1f21576d0d200145e422eda1a40018ec865cb43480010ff0abb2869000e1f2157650d200047bc0aeca1a40048f4815d9434800517d0fb2286900021fe1d645492001c3e43ac8a92403d87e8719152480810fb0e322a4901029b60b635492056727996c6a924007a7a86dc152480814dd0d3a2a4900029b61a74549201be363b4e8a924040b6a809d152480016d3013a2a4900029be19745492020536432e8a924000b6b805d152480816d100ba2a4900db1b1d8745492000696ba0e8a924000e2f6499152480012df0eb22a49002e5b21d645492031cb7438c8a92404096d871915248001c5ac8322a4900cf1b1db7354920006b4386e6a924000a6f865cd52480814d90cb9aa4900c71b1d97354920005b3c0ae6a924000b64815cd52480016d700b9aa490102da2017354920006b4382e6a9240ace4e63d8d5248159c98c6b1aa4900029ba1b435492000536c3686a924040b6880dc552480814dd0d38aa4900029b61a71549200e6363b4e2a924040b6a809c552480016d30138aa4900029be19715492020536432e2a924000b4f835c552480c969906b8aa490002dae017154920205b4402e2a924016c6c761c552480816d50038aa490002da6007154920205b543ee
  | 5 => 0x31ed9570085400063c32ae010a8000ceb625c021500f98f4edb2e80a01f38ed9365d01400053c432a5a028000c3d75d53644c00153b07aa6c8980021fe1571d913001c3e42ae3b22600387e87dd5644c0010fb05baac8980022fe1175591300043f438eab226000c3c75dd1644c0010fd0fa92c89800e1f21f52591300045fc3ac83226000a3c85590644c02517908ba8c89804b0f21175191300043fc12ea3226012c3f405d4644c00187a80ba8c8980030f5d7541913001c3fc3ea4322600087d87d48644c0ab8bae7a90c898003350c571191300043fc2ae9b12600387c855d3624c0010ff0ab8ec49800e1f21571d893000477c3ac43126000a6d829d9524c00147f08bb2a4980028f211765493000537c12eca926000a77815d9524c0a74e902bb2a49801e9ba0b645493000536c16c8a926007a6e82991524c0014db05322a4980021fe1d64549300043e43ac8a92600087e87191524c0010fb0e322a49810297219735493056da7c12e6a926000b54815cd524c0814b90ca1aa4980021fe1576d093001c3e42aeda1260018dc865cf424c00f1b9073b4849800637219739093001c3f428eca12600087d851d9424c00f55d05b22849800637219731093003c7c432e021260018dc865d1324c0913a902ba2649801e37a1e644c93003d67414c89926007ace86d89324c00f8b8eca92649801f93189524c93000c6ec1eebb0a6055c5d73d4b614c1071bf0e996c2980023de1d611853000c6e432e7a0a60018dd839da414c0091f10cb84829800a3720c765053000c6f436e6a0a600299c8750d414c001938eca1a82980021fe15761053001c3e42aec20a60018dc865cc414c0091f10cb80829804b2e19170105300046ec3cc918a6040c5e7654a314c00b3ab0fb0c62980063721973c853003e663b26590a60018dd839da214c0010ff0abb4429800e1f21576885300045fc22ed10a60128bc845da214c0091f10cb84429800a3720c764853000c6f436e690a60029cc874c9214c001998ec99242980123720e760853000c7c404ec10a60018dc865cc214c00f998c4b984298003335cf62085300247c432e010a6000ceb625c0214c00187ee93a2cb9001e9ba0a745972034536c14e8b2e4000a7b805d165c80814f100ba2cb900030f5d074597200062fb9ce6b2e4000a77815cd65c80014e902b9acb900021fa1c43597200043ec3886b2e4000a5f835c565c80014b906b8acb900021fa1c31597200043ec3862b2e4000a3e840c565c800147b0818acb9001e9ba08315972000536c1062b2e4040a7a800c565c80014f30018acb9001e2f211739932003c5f43c86b26400387e85dc564c80010fb0bb8ac9900023de057558f200247a40aeab1e4007c6e7259743c800f1bf0eb1e879001f339c963d0f2000636b2ae5a1e40008f7815d94
  | 6 => 0x43fc2ae3b12800387c855c762500018bce7b2cc4a0003179cc65989400062fb2ae73128000c5c655ce625000f998c4b9cc4a0003335cf62989400043f43ecab12800087e87195625015f87ee832ac4a00421f61f651894000536c16ca312807dc3d7419462500014db04328c4a00023be1d62189400043f434eca928000a6d829d952500018db053b2a4a00031bc8276549400051fc22eca928000a6f825d952500014f700bb2a4a00030f61076549400061f200eca928000c3c401d952500018f0803b2a4a00031bc80765494000636900eca928000a3e869d15250001878ed3a2a4a01e6cb60a74549402051e432e8a928000c3c765d152500f765f04ba2a4a0102ce201745494003d37416c6a928000a6d82d8d52500014790ca9684a001f8b98952d09403ec3e432eb212807c87f87d9642500010fb0fb2c84a0003179cf65909400062fb2ae72128000c5c655ce425000f998c4b9c84a0003335cf62909400063c32ee0a12807cc3c76d954250001c5eca31284a00028f219525094003e1e3b2a4a128007e2c62549425006d0f90cba884a00021fe1f65109400843ec3eca2128000e2f6550842500070f90b3b464a001e2f212768c9400043fc2aed192800387c855da325000f1d904bb464a00021f219758c9400043fc3ecb192800087d87d96325000187ecb3a464a00030f196748c94000c5e432e91928000c3f655d23250001878caba464a00032b5d3628c94001c3f42eec992800087d85dd932500051dd0fb1264a02bb0f5d0659854001c3f436eab0a800087e87d9561500018b8e7b2ac2a00021fa1c65585400062e398cab0a8000c5f65dcd61500018b8cbb9ac2a00031bd9772585400063632ee4b0a8000c6f651c961500018d8ca392c2a00023de1d611854013c3e432eba0a800087f87d9741500210fb0fb2e82a00031e19570905400062e39ecaa0a8000c5f65dcd41500018b8cbb9a82a00036610373505400043fc2aed18a800387c855da31500011df04bb462a001e3b209768c54001c3f42eec98a800087d85dd931500070f90b3b642a00021fe1576c854001c3e42aed90a800087c865d721500010ff0fb2e42a00021f61f65c854000c5e432e990a800087f855da21500070f90abb442a000237e0d76885400146e41aed10a800387e85dd921500010fb0bbb242a000a37a0e76485400046ec1cec90a8000c5c73d9521500018becbb9a42a000317197734854001c3e42cec10a80048bc849d821500010ff0abb042a000e1f21576085400043e432ea10a800087f87d9421500010fb0fb2842a0003179cf65085403e63d386ca10a8000c3f659d02150001878cb3a042a00062f21974085400061fb2ae810a8000c3c655d021500018becab9842a000317195730854003e66312e610a8000cad74d88215000199ae7b1042a
  | 7 => 0x1f5495163084014bd0bb82c610802976177058c210256b40ce0b184200ad5819c1630840f59904b82c61080237a1c5058c210046ec38a0b184200a9e84141630840153b08282c61081eb3a085058c2100566c10a0b184204ad68114163084015ab02282c61080237a1c4058c210046ec3880b184200a5e8510163084014bb0a202c61081eb3a084058c2100566c1080b184204ad68110163084015ab02202c61081f1b9c965d0c210246fc3ac7a184207cce7258f43084018dacab96861084b2b99172d0c2100666b1ae5a1842048f4815d943084091790eb2286108123721d6350c210065ab26e2a184200cd563dc543084031eb03b9ac0108123ea1f50580210247c43aa0b004200a7a85cc160084014f30b982c010802aea1075580210055cc20eab004200ada831d560084015b3063aac01081ebaa0875580210a574c10eab004204af2811d560084295e3023aac0108029ee1574580210053c42ae8b004207ae8825d160084014f50a3a2c0108029e61474580210056d418e8b004200ad9831d1600840f5d5043a2c010852ba608745802102579408e8b004214af1811d1600840f5d505aa2c010802ba60b54580210071daa4a8b004204af281dcd60084295e303b9ac0108029ea1673580210053cc2ce6b004207ae8825cd600840f5d505a9ac010802ba60b53580210072da9ca6b004200af38154d60084095e102a9ac01081ebaa0b435802100574c1686b004200af38150d60084095e102a1ac0108029ea1443580210053cc2886b00420387e85dc562d00010fb0bb8ac5a00028fa127654b4000536c14eca968000a6f825d952d008147b0d3a2a5a00030fdda7454b403fd96c14e8a968000d38709d152d000147f0cba2a5a00030f1d97454b4040d97c12e8a968040b38805d152d00018f2edb82a5a00034e5d37054b4003e1ebb2a5a168007e2e6254b42d007353d07bb285a001f8b1895250b4003c5ec22ed19680008f7815d932d00091e902bb265a000237e0d75587400146e41aeab0e80028de87dcd61d00018bee7a92c3a0223171cf52587400062fb9aa4b0e8041c5c7354961d00018dee4a92c3a001f1b1c952587401fe4e39e84b0e8039c9c7350961d000f958e4a12c3a000237e0d76887400146e41aed10e80008df835d921d00051b906bb243a00122f611760874000537414c7b2a8000a6d8298f65500018bae639ecaa00021fa1c43d95400843ec3887b2a807ba3e841cb65500f947b08396caa00021fa1c32d95400043ec3865b2a800087e870c765500010fb0e18ecaa00028fa1031d95400051ec2063b2a8000a6e820c765500014db0418ecaa01f29ea0031d95400053cc0063b2a800087e87d9563500010fd0e32ac6a02c30fdd06558d4000536c16ebb128000a6d821d762500010ff0ab9ec4a000e1f21573d89400
  | 8 => 0xebb1e8290803175d763d052109656322e5a0a4200ccc635cb41484011bf06bb2829080a3720d765052141c6f436e6a0a42008de87d8d41484cd1b90fb1a829099b331cb634c521024e643a6498a4204acc864c931484097890299262908063d20573d812103e36392a5b02425d8dc86dcd60484011bd0fb1ac09080317dd763581210062e3aec6b024200c9f74d8d6048401938e9b1ac09080237a1c63581210062fba8c6b024200c5c7518d604840193ee831ac090803271d063581210061fba4e8b284200c5f739cd65085634ef02b9aca108129d20573594210043f43886b28420087d8710d650840147d08382ca108028f61070594210052f418e0b284200a5d831c1650840f4dd04382ca1085a9b60870594210253b408e0b284216a75811c165084010fd0e202ca108021f61c40594210052f41880b284200a5d83101650840f4dd04202ca108029b60840594210253b40880b284200a758110165084010fd0f982ca108021f61f30594210253b40c60b284200a75818c1650840917908bacc81084b0fdd754990210245e422e7320420087f855c264084070f90ab84c8108122f21170990210961fbaceb3204200e1f5394e640840147f0ab84c8108028f21570990210945f438a132042008bd87142640840153d06284c810802a760c509902103d57410a13204200aad82142640840956d02284c810802ad60450990210051f42e613204200a3d85cc2640840956d03184c810802ad60630990210245f43ea8b204200c3f75d51640840f55d05aa2c81080f0f9d654590210245e43aa8b2042048be8790d640840147d0a21ac8108028f61443590210051f42880b204200a3d85101640840153d06202c810802a760c405902103d5741080b204204ab681101640840187eeb3aac81081eaba0a755902100556c14eab204204ab4815cd640840147d0a39ac8108028f614735902103d57416a6b204200aad82d4d6408401c3ea729ac8108028fe1570590210051e42ae0b204207aac825c1640840147d0a382c8108028f61470590210054f418e0b204200a9d831c1640840f55d04382c810802ab60870590210255b408e0b204200ab5811c1640840117d0e282c8108022f61c50590210054f418a0b204200a9d83141640840f55d04282c810802ab60850590210255b408a0b204200ab581141640840147d0b982c8108028f61730590210255b40c60b204200ab5818c164084091e902baac61081237a1f5358c210062fbaea6b184207ace82d4d63084091b90ea9ac61080e1fa177058c210043ec2ee0b184204ad6818c163084018beeb3aac61081eb3a0a7558c2100566c14eab184200ad7815d563084095a902baac61081eb3a0a7458c210256a40ae8b184200a5e851d163084014bb0a3a2c61081eb3a0b5458c2100566c16a8b184200e
  | 9 => 0x724c721024e643a6498e4204bc4814c931c840117f08baac19084a2f21175583210043ec3ea532442008df835d564884051b906baac91080a37a1f73592210062fb9ea4b244288c5c73d49648840553906b26871084a3be1972d0e212fc6fc1aeca1c42048bc87591438847b0fd0f322a51080297e0d6454a2120d2e41ac8a9442b3e4f3258d528840f6c905b8aa5108fea720d64d0a2100716b22a5a144200d65525c7428847353906b228510813351c5634ca2101c3f43eeab04425787e871d560884014db043aac1108021fa1f52582213543e43aa4b0442038bf87553644840147b0a206c890802ab60840d91210055ac0881b224212c3c645d6644840187aebb24c89080e1fe1f52991210043ec3ea53224288c5e73d4a64484018bae7a94c89080237e0d75591210146e41aeab2242008fb805d564484031f100baac89080317dcf52591214462e39ea4b22420387e85dc564484010fb0bb8ac890803351cf71591210045fc3ac8322420087f855c064484070f90ab80c890803175d753d8d2101c6fc3aa7b1a420087f855c363484070f90ab86c690802a7a1265d8d210054ec24cbb1a4200a5e8599363484014bb0b326c690a0f179db52d8d210062eba8ebb1a4200a5e859d363484014bb0b3a6c69080387d5254d8d210052fc2ae1b1a4200a5c855c363484bb5ad02386c69099ab560470d8d210046f438a1b1a42008dd87143634840153d08286c690802a761050d8d2133567410a1b1a4200acd8214363484bb5ad02286c690802b560450d8d210046f43881b1a42008dd8710363484014bd0a206c6908029761440d8d213356741081b1a4200acd8210363484bb5ad02206c690802b560440d8d210046ec3c21b1a42008df835d563484011ef02baac6908023761e6518d210054f424ca31a4200a9d84994634840159b05328c69080237e1d6518d210056bc0aca31a42008dd8799063484014bd0b320c690802976166418d210046fc3ac831a4200ad58198063484011ef02bb2869084a37a1f6350d2101c3f43cc8a92420087d8799152484834bd07322a4908029760e64549210052fc1ac8a924241a5c8359152484014df04b22a490a0e97a1b6354921337a210ec6a924266c5f72d8d5248401c9ee5b1aa49099b93c83635492142d37c12c6a924266a5e8618d5248565c9ec431aa490a0fd108463549210072a31ee2a924200e54631c5524840f6c90438aa49094f1b1d9525092100716322a4a12429ee4c6354942484a7ac8e2a9284908033518f715092101567436c71924200cce76d8e32484bb9a8e3b1a649094f1b1d9524c92120f2631aa49924253d647154932484bb998edb1a6490802b3a1b434c921016663b686992425ddc7731c532484017c30038a649084b0f19175d05210062e31aeba0a4200c3d75d9341484018bc
  | 10 => 0xb226200ab581103644c425878c8bacc8988030f5d7649913133667b1ce53226200caf645ca644c425958c8b94c8988021fe0975991310063742ae53226200c6d855ca644c4070ff0fa94c8988021f61f529913103e37396a53226200c6d72d4a644c4011bf06baac89880317dcf52591310045fc3ac8322620087f855c0644c4070f90ab80c89884b2e101701913101c77c3aa5b12620087f855c3624c4070f90ab86c4988029b61420d893100556c2041b126200acd83083624c4015cb02106c49881f1b18975989313364fb1ce93126207cac625d2624c4018daebb14c4988032b5d3629893100477c3ac43126200a3e84dd9524c40147b09bb2a4988029b60a76549310052fc1aeca926200a6f825d9524c4014ef02bb2a4988021fa1e64549310043ec3cc8a926207a6e82991524c4014db05322a49880297e0d645493100537c12c8a926207a6c82591524c40f4dd0db12a49880e9ba1f625493101d3643ec4a926200a6d80d89524c4cdc9ec6312a49881e3b209769093103e36312eb21262049d4815ce424c4018daebb148498803335cf629093101c3f42eeca12620087d85dd9424c40f1e90cb88849881e37a1e644c93103d67414c8992625fcd471991324c5139a8e2322649881f171d9524c93103f26312a49926253d5471549324c4093ad0fb8a649884b0f19175d05310061ebaec9a0a6200c9c64dcd414c50d5a902996c09899b33d8c72581310061fba4e8b2e4200a7b805d165c84014f100ba2cb908030f5d074597210062fb9ce6b2e4207a6e829cd65c856b4db0539acb908029de05735972129d3a40ae6b2e4207a6e8290d65c84014db0521acb908021fa1c43597210043ec3886b2e4200a5f835c565c84014b906b8acb90ad29be0971597210051fc22e0b2e4200a3c845c165c840147d08382cb908028f61070597210052f418e0b2e4200a5d831c165c840f4dd04382cb9087e9b608705972129d3b408e0b2e4200a75811c165c84010fd0e202cb908021f61c40597210052f41880b2e4200a5d8310165c840f4dd04202cb908029b608405972129d3b40880b2e4200a758110165c84010fd0f982cb908021f61f305972129d3b40c60b2e4200a75818c165c840f4dd04182cb908029b60830597210052f41c20b2e4200a5d8384165c840f4dd05082cb908029b60a105972103c5e422e7326420087f855c264c84070f90ab84c9908023ee01755932100c7c402eab2642078be8790d64c840f55d0521ac99080e1fa177058f210043ec2ee0b1e42078df8758f43c840f59d0da1a65908021fe1975d07210043fc3acba0e4200c5c7359541c840f8d8e4b2a8390803271ce64507210064e39ac8a0e4207cac7259141c84018bccbb9a839080317597735072100636b2ee4a0e4207c6c7259531c84a7ca862b2a63908031b597
  | 11 => 0x504014df04bb2a4a08029ee0176549412053c402eca928241a5e86d8d5250401c9ee5b1aa4a09078718f435494100596c1686a928253a3c8650d525040f4dd0db12a4a080393d8f62549410072631ec4a928203a6e87d8952504074d90fb12a4a08029b603625494100727b18c4a928200e4c63189525047f1790cb9e84a08fea7a1b63d09415070e31aa5a128207e2c6254b42504018b8c6bac84a081f1b189759094144c6e432e721282008dd87d8e42504018bcebb1c84a0803175d7639094100636baec52128200cd463dc54250473938c7b9a84a08e6a7a1b63509412fe4e3b6c6a128289c9c7618d425040155d0db9284a0a73a318f725094103d57436c4a128200e8c63d894250401d1ec631284a0803a318c625094103e1e3b2a4a12829ee1c63549425040fc58c4a9284a0803a518f71509410074a318e2a128200c5c635d442504018bcebb1884a0803175d7631094120e2e31aeb192823fc9c639d23250473938c6ba464a0803179d7638c9410062ebaec71928200c9e74d8e32504070fd0a3b264a08021f614764c9411fe4e31ce899282048bc865d1325040f59d05b1a64a0803271db434c9410062e31aeba0a8212d34415d741504018bcebb1e82a0803175d763d05412fc6e436e6b0282008de87d8d60504018beebb1ac0a0803171d763581410046f438c6b028200c5f7518d60504018b8ea31ac0a080333d8f72581410066631ee4b028200ccf631c96050401998c6392c0a08123721d5358c410247643aa4b108207a6c82dd952104014df04bb2a42080e9ba1d625484101d3643ac4a908253e2f4158952104a7c5a82b12a4208029be01625484101c3f42eeca10820087d85dd9421040f8dcc4bac64208031b5d5628c841096573a2c51908204cd47158d32104091d90eb126420813391c5624c8410965b2a6eca088200cb554dd941104018eea5bb2822080335ddb73504410066bbb0e6a088200c777654941104070fd0fbaac0208021f60b75580412bc3f438eab008200a6d821d560104010fd0fa92c02080e1f21f52580410043f43aa4b00820087c8754960104091f10ea82c0208021fe09759923101c3fc3ea5324620087d87d4a648c5131bf0eb2687188029be097654a310043f43cc8a94620087d87991528c4014df04b22a51881e9b2096454a310062ebb6e6a946266b4e82d0d528c4cdc9c64b12a51899a6721173d0a3101c3f42eeca14620087d85dd9428c40f55904b22851880a7520d7110a313364fb14e91946266c9d629d2328c4cda3ea53a4651899b4754a748ca3141e4f30ce9194623fd96619d2328c4070fd0fbaac1188021f60b75582312bc3f438eab04620087e87d49608c4070f90fa92c1188021fa1d52582310043e43aa4b0462038bf87553644c40147b0a206c898802a760c40d913100556c1081
  | 12 => 0x84b8bd096598b410062f32ae73168200c5d655ce62d04014db053aac5a08029be097558b4101c3f42ee6b16820087d85dcd62d042555d09992c5a080e1fa177058b410043ec2ee0b168241a5e839d952d04014bb073b2a5a08029b60a7654b4100537c12eca968200c6f825d952d04010fd0e3b2a5a094e8f61b4354b4100596c1686a96823fc9e635cf42d040147f0ca9685a081f0f5d952d0b4103f17312a5a16823d87f865d642d044f0ff0eb2c85a0803179cd6590b410062f32ae72168200c5d655ce42d040187eecb2a85a08e62f61b7350b410051fc32a4a168207e2c6254942d04070fd0abb465a08021fe19758cb410043fc3acb196820087d8759632d042587ce8b2c65a08030f995748cb410061eb2ae91968212c9e7458e32d040917d09bb265a08126d205744cb412feca38e869968200c7665dc532d04070fd0bb82c7208021f6177058e4101c3f42ee0b14820087d85dc162904014df04bb2a5208029be096354a4103d36412c6a948207cce625ce429040199ae6b1485208032b5d1628ca410247643ac49948200c5d75d4f63504071bf0ea9ec6a08021fe1570d8d4101c3e42ae1b1a8200ace82997635040159b0532ec6a0a23179db52d8d410062eba8ebb1a8200e1f5495363504014bd0b396c6a08029761672d8d4100667b94e5b1a8200a5e851cb63504014bb0a396c6a097ea761072d8d410052f42ee3b1a8200a5d85dc7635040159d05b8ec6a0802b360b71d8d412ff2b28ea3b1a8200a5f855c363504014b90ab86c6a097eb5a0470d8d410056ac08e1b1a82008de8714363504011bb0e286c6a0802a7a1050d8d410054ec20a1b1a8200ace82143635040159b04286c6a097eb5a0450d8d410056ac08a1b1a82008de8710363504531bb0e206c6a080297a1440d8d410052ec2881b1a8200ace82103635040159b04206c6a097eb5a0440d8d410046f43841b1a82008dd8708363504014bd0a106c6a08029761420d8d410054f42041b1a8200a9d8408363504bf5ad02106c6a0802b560420d8d410046ec3c21b1a82008dd87994635040153b09328c6a0802b3a0a6518d4100566c14ca31a82008df8759463504015ab03300c6a080aa7a1b63d0d410064f3b6c7a1a8239c9c635cb43504bf9a8e3b1a86a080b271db7350d412fe4e3b6c6a1a825fd97731c543504071df0ea96c4a08021fe1570d894101c3e42ae1b128200a6d85083625040155b08106c4a0802b960420d894103e36312eb3128200c5e75d8e62504018baebb1cc4a0803179d463989410062eba8c73128200c6d75d8a62504011bd0fb1ac4a080237a1c63589410062f3aec63128200c5d75d8c62504018bcea318c4a0803175d4631894100477c3ac43128241a5e83dd952504014bb07bb2a4a08029b60a76549410052fc1aeca928241a5c835d952
  | 13 => 0x43ec2ee2b246400a3e85101648c80147b0a202c919002a760c405923203d5741080b246400ab681101648c80156b02202c9190030fdd6755923203d57414eab246400aad829d5648c80147d0bb8ac9190028f617715923203d57414e2b246400a9f835c5648c80f55d0428ac919002ab60851592320051fc2ae0b246400a3c855c1648c80f55904b82c9190028fa1470592320051ec28e0b246439a9e831c1648c80153b06382c91901eaba08705923200556c10e0b246400ab6811c1648c80156b02382c9190022fa1c50592320045ec38a0b246439a9e83141648c80153b06282c91901eaba08505923200556c10a0b246400ab681141648c80156b02282c9190e6a7a0e10592320054ec1c20b246407aae82041648c80155b04082c91901e3760f75d913203e2eb9ea5b22640087f855c2644c8070f90ab84c8990023de0575591320247a40aeab2264008fb805d5644c8031f100baac89922b1d1c752591320063ba96e2b226400cd7731c5644c80117f0eb20c8992221fe09751913201c3fc3ea4322640087d87d48644c8731bb0fb2686990e66761f64d0d3203c6fc3ac9a1a645fad481593434c80f39f0eb9686990e7639d172d0d3241c6e432e3a1a649ea6d82991524c8014ef02b22a49914e9d20564549321ec3f438c8a92644187d87191524c8838bcedb9aa49901ed3a0b735493203d2f43686a926407b4e82d0d524c80f33908b9e84991071b9d952d093200717b22a5a126441d4e7354b424c941e1886a9684990023de1d61185320043ec3cebb0264b9a6d829d7604c8070ff0ebaec0992221fe0975d813201c3fc3ea5b02640087d87d4b604c8d50ff0ea96c0991061f61d52d813200c6e41ae3b026412a3e8498d65d0425c3e8731acba084a8fa1273597415c51ec24e6b2e8200c5f739cd65d042547d09392cba0ade8f61272597410052f41ce4b2e8200a5d839c965d042547d09992cba08028f61332597410043f43864b2e820087d870c965d052b47f08b8acba080297e0d71597410052e41ae2b2e82b6a3f845c165d042547908b82cba084a8fa10705974113d1ec20e0b2e8200a5e831c165d04014bb06382cba08029ba08705974100536c10e0b2e8299a76811c165d04014eb02382cba08021fa1f30597410043ec3e60b2e8299a76818c165d04014eb03182cba084a8fa1030597410051ec2060b2e820087e8708165d04010fb0e102cba084a8fa1020597410051ec2040b2e8200a5e8308165d04014bb06102cba0a669da0420597410053ac0840b2e8212a3e8484165d040147b09082cba080297a0e10597410052ec1c20b2e820387e85dc163d04010fb0bb82c7a08030fdd96550f410961f3a4cb3168200c5e7399662d04014db0532cc5a089e1fe1d6598b410961f3a2cb3168200c5e7359662d04014df04b2cc5a0
  | 14 => 0x6819c163908015ab03382c72100237a1c5058e420046ec38a0b1c8400a9e84141639080153b08282c72101eb3a085058e4200566c10a0b1c8400ad68114163908015ab02282c7210f237a1c4058e420046ec3880b1c8400a5e8510163908014bb0a202c72101eb3a084058e4200566c1080b1c8400ad68110163908015ab02202c72100237a1e1058e420046ec3c20b1c8407ace82041639080159b04082c7210033358f7250e420146f41ee2b0484008dd83dc5609080f87ae9a96c6a10021fe1570d8d4201c3e42ae1b1a8400cd4631c56350801b288638ac6a12736310f7250d425fe1f3b6e8a9284bec3d761d1525080f47b09b1aa4a12f793ccb635494203e973a2a5a128407e2f6454b4250825b5680b8684a10021f61f52d85420b43fc3aa5b0a8400ab5840c761508015cb0418ec2a10023de1d61185420056a41ac230a84008f7815cf60508091e902b9ec0a100237e0d71d81420146e41ae3b028400c5f739cd65108014bf06b8aca210029720d71594420043f43862b28840087d870c5651082547d0818aca210028f610315944203d3741062b288400a6d820c565108014f50018aca210029e60031594425e51fc22e0b288412a3c845c1651082547d08382ca210da8f61070594420052f418e0b288400a5d831c1651080f4dd04382ca210da9b60870594420053b408e0b288400a75811c165108010fd0f982ca210021f61f30594420053b40c60b288400a75818c165108014bd07082ca210029760e105944201c3f42ee0b18840087d85dc1631082595ca9bb284210032b55376508425dd57c3286a1084008df835d561108051b906baac22100a37a1f73584423362fa96e6b088466c5d52dcd6110825d5680a12c0210030fdd2745963203d37414e2b2c64baa6d829c5658c8014bf06b8acb191069720d71596320051f420e0b2c6400a3d841c1658c8834bd06382cb190029760c705963203d37410e0b2c6433a6d821c1658c8014ed02382cb190029d60470596320043f43880b2c640087d87101658c8834bd06202cb190029760c405963203d3741080b2c6400a6d82101658c8014ed02202cb190029d604405963220d2f41c20b2c6400a5d83841658c80f4dd04082cb190029b608105963203c5e422eb3246412c3f75d52648c8010ff0ab84c91900e1f21570992320961fbaceb3246400a9f835c6648c87f53d07a8cc919002a760f51992320054fc1aa3324643fa9c83546648c80147f0ab84c9190028f21570992320945f438a132464008bd87142648c87f53d06284c919002a760c509923203d57410a13246400aad82142648c80156d02284c919002ad60450992321fd4f41c213246400a9d83842648c80f17d0faa2c9190030fdd7545923203d57416a8b246403c3e75951648c80f1790eaa2c91900e1fa17715923200
  | 15 => 0x9b20c2a90029e2016418552514b7c12e630aa453974815cc61548012ef0eb08c2a9002d520d611855261db3c12c230aa400a3d8418061548018f2e0300c2a901e5ba0a74d81521d4b6c14e9b02a43796f825d3605480f2d904ba6c0a91021f61f64d81520061f3a6c9b02a400e3840d9360548010ff0eb26c0a91029e20164d8152514b7c12e7b02a40796c825cf60548012ef02b9ec0a914e5d20573d8152004afc1ae3b02a44195c835c760548392df04b8ec0a901e5b20971d81520061fb16e8b02a400d2f62dd16054801a5e41ba2c0a90034b48374581520061ec30e8b02a400c3f621d16054801a5ec43a2c0a90030f98074581520061e300e8b02a400d38601d16054801a5e403a2c0a90034b48074581520043f43ec8b02a400c3c74d916054801878e8b22c0a91029e201645815200697ba6e4b02a400d2c74dc96054801a70e9b02c0a930b5adcb60581520946e43aa6b1e8407c3c74d4963d080f47908b1aa5a100e1fa1f75583420043f438eab068400a6d821d560d08010fd0fa92c1a11aa1f21d52583420146f41ee2b0684008dd83dc560d097f4df04ba2cb210029ee0174596420053c402e8b2c8400c5f739cd659080f4dd0521acb210029b60a43596421ec3f43886b2c840087d8710d65908010fd0e18acb210021f61c31596420051f42062b2c8400a3d840c5659080f4dd0418acb210029b60831596420053d40062b2c8400a79800c5659080f4dd05382cb213069b60a70596420051fc22e0b2c84c0a3c845c1659087b47d08382cb210028f61070596420052f418e0b2c8400a5d831c1659080f4dd04382cb210f69b60870596420053b408e0b2c8400a75811c1659080f4dd05202cb210029b60a40596421ec3f43880b2c840087d8710165908014bd06202cb210029760c405964203d3741080b2c8400a6d8210165908014ed02202cb210029d60440596420043f43e60b2c840087d87cc1659080f4dd05182cb210029b60a30596420053b40c60b2c8400a75818c1659080f4dd04182cb210029b60830596420052f41c20b2c8400a5d83841659080f4dd05082cb210029b60a105964203d3741020b2c8400a6d8204165908018beeba9ac72101eb3a0b5358e4203c6e43aa6b1c840387e85dc163908010fb0bb82c721002b5a063058e420056ac0c60b1c8400c5f759d5639080f59d053aac721002b360a7558e420056bc0ae8b1c8400ad4815d1639080f59d05aa2c721002b360b5458e420070faa4a8b1c8407acc825c563908014bd0a38ac721002976147158e421e54f420e2b1c8400a9d841c5639080f59d0438ac7210f2b36087158e420066ab88e2b1c8400ada801c563908015b30038ac72101eb3a085158e4200566c10a2b1c8400a5e85dc163908014bb0bb82c72101eb3a0a7058e4200566c14e0b1c8400ad
  | 16 => 0x400806400000802000000001c00000c00001c00400800000400400000400400800400000000402800800000800c251d90ea92c5a180e1fa177158b430043ec2ee2b16860387e87dd560d0c010fb05baac1a18021fa1c755834300536c10eab06860087e87d4960d0c070f90fa92c1a18021fe1570d894301c3e42ae1b12869ccad74d8a6250c011df0eb10c4a18023de1d6118543514b7c12e7b22a400a3d86903645480165b05206c8a90028f61840d915200596c1081b22a4c7d2d72d92645480147b0fb24c8a90030f61f649915263e1eb96c9322a400e2f645ca645480147b09304c8a90031e5c260991520051ec20c1322a49fd2f74dc964548812f50fb82c8a90035adcb7059152006b5c16e0b22a400c7b62dc16454801ad6c5b82c8a90031edd870591520069dba0e0b22a400d6b721c1645497d65b05320c8a90021fe1d64191520053c402c8322a40093f87590645498d65f04b20c8a9002ce20164191520051fc3ac8322a400c3f87590645480107f0eb20c8a931a8fe09641915200717c12c8322a400e3b80590645480147900b20c8a90038e20164191520051c402c8322a40095f835c464548832b906b88c8a90725be0971191520061eb22e0322a400a3d84180645480147f0d200c8a9002cb60a40191520051ec3080322a400b2d821006454801c70c0200c8a90de5be0974d8d5203cb6412e9b1aa44187d87d93635480187ce9b26c6a910697a0f64d8d520053c402c9b1aa44187d87183635480147b08306c6a910697a0c60d8d520053ac08c1b1aa400c3c7459163548014f100b22c6a931753dcf7258d52006b3b96e2b1aa400c7762dc56354801acec5b8ac6a900359dc87158d5229e3ac30e2b1aa400c77641c563548018eac838ac6a900355d8c7158d52006aa318e2b1aa48ac77621c56354801acec438ac6a900355cc07158d520063a38cc0b1aa400a3d8418163548834bd06302c6a90029d6046058d520063a388c0b1aa40096d82ddb43548a72ed03bb686a90025d60776d0d52004b7c12eda1aa40796f875cb43548072dd0cb9686a900e5b21972d0d525ee9721ae5a1aa4bdd2c435cb43548012df00b9686a90021fe1970d0d520043e432e1a1aa40096d82dd943548012df04bb286a90025de057650d5229cba40aeca1aa40097b805d943548812f100bb286a90ea5b60a74d855229c3ec3ec7b0aa441c5e73d8f61548a74e902b1ec2a90029d61b31d85520053ac3063b0aa400e57630c761548016cb0418ec2a90030f9d164985520053c402c930aa4c4d6572d86615480147b08304c2a90029d604609855220caf43ee6b0aa400c5f62dcd6154801a9ec5b9ac2a9107171cf635855229c3e43ac6b0aa400d4f73dc96154801a98e7b92c2a9003551cf61585525a6b3b96c2b0aa43796f825d0615480187ce
  | 17 => 0xc02800800002001c00c06006c00002400002c00c01c00400c00c00400000003000802c02800000002002000003800000000001c00400c00000403800400000000000400000000800004c00800000c00001400000000000001400400001402c00001401002004800000400c01400001800000000000800400000001000400400400000400400001c00c03000800001400800c00000000000800801000801002400400001000003800402800000405001000000000000400c01000801800005c00c00800400401000000400800000000400000000001001400401408400002402000000001000400004c00c00000403000801400000400400002000800000000401800c00800800000000000800000000005400c00801800401800805400002004000402000800400000001400400001400000400801800000400400800401801000003c01c01400c00400000002401c01800400000006c00000001400001000c00801000401000001003000800000c00000403001400c00002000002801406400404400400000000000003000000800004400000c01c00000400003c00000000000801001c00006801800000c00000800c00800c00403c00c00401000400801000001400c00400000802000403000803407800801c00002c00000c00000000c02402000001400002c02000800000802800c00000c00000800800801800800400400401c00800000801800801003000400800c00803400802c00403001c00000001c01c00400001400400802400000800400801000401800804001c00002000002801000401000400001800007800c00000000402400400400002000c00000401800800c03001000800804000000400c00400401802c01800000002001400000000001c01003406801000400400000000000002000004401000000000800c01000800000000003800004002800000401c00000000400000400001800c00400000800001800000400400000800400c00400000400800800400c00400000800003000000800808000800000000800000000400002000003800400c00000001800401400800000403c00000400400000001403400400800803000000000000800000000401002400c00003800400000000400400002002400000400003000000000001000003400402800400000c00000000001c0000140040080cc01401800000002c00800000000000001800400c00c04401400001000401400000000c01c00000400c0140340000140080ac00c00400000000000001003c02000400c00400000c0ac00000800400001405404000800400400800000002c00c00400400402003000001000400400400801401400000000800801400000c00001c00c00000c00400000400000403800000001800400002801400800c00802800400000c00000c0040
  | 18 => 0x9f4408000000382159000072c4e80000000220000000000058a000000000029a5601bf80000007d52d113340003c80b707fc00057828a05d42ba7d81ea01e05a0000429110000000000000000000000da00010ac17c00000000000003ef80011ce0002a2a188b664002e59104b7891d2a1033400000041e9b0c1343740000aac0002fa0819ac400016207a80e400042c1d88000a560350148f4000028f1c583005c612b06c07c41221ce38d8e40f4c3e2219000000000000024440000000f41c60b98343085800092a0000799f2400056f0870000c1a204000000000055745180011b846200006380045c510c03f120a71600015508c83c20000ed800060b000219c00010a0001b202320003638a8422447c17c9ba80006f816a80000001aa0000000e6a2e00090c48e0214b18886b8d7c8860a0000000000011384240000001fb8cdcc7a00000000004b630a000000000091b000000101e0001b424c01be384159800062c0000000a040005340588000cd44f53b7a2e0000597262000000000009d000000047529500002ca000000000108e000000139400000040321c494825727984cc37e0000cc911000063700000004bc0003168b7c00000005200000008fb090092c8c200000000000000000000000d50000000157cd6832c0000dec3da480000000027e6a600007944387f404785f40007510000a88000000000000000000000000000001463f6800000026c0000000b9c0001f996c400000000000000002bf000000000000036080000007e130380000001760000bd4c4e52822d81c0a48000320000000015b38b88cc0000000169f90cb000005b00005684671a702b10487cc41d8b7810c8550ce14b400000005011303604ee0100d3c15232400000000005c000011a400092800008385d241d39698b840a5fc11da4ac28e75d000000000000025f9108e943c000000011a077200000000002990001e9c0000000899e04e920000000000bf22651f08000000000000000000081f3b60ca0a068df16d0790daa00024d959019e84920100005e0000398145c000298000160c0003d2405000000092a000086c00007e4759e6499800000e0c00d305e400000010300001af84c8728043211800027884600000000000001fa00006182340360000de464b3da00000008760000000000000465800000000000000000000001cf9e5041a4570001e440005751528000bc600041f800000000000000000000002838000000000000215c00000044e80010ee00013e1569200135000001000800401800002400c01001800400400c00400000000804400400800401400000000001801001000000000801001400c01c02800000004400800004000407003000800800002000000800000400400002000c00003800800803404000001402805c00401400000
  | 19 => 0x5c4a382623d80158f800790001154f088b925087d4b8212c0ee8f1c58876b0fd00000004e40001d70000000196821cd4037019a0d3120e2e145009dc9be36f0ec00300000003f819dc4ea000000066000066f0000ce51a24e631a81900004a2407066826c2dd46c09b4e5252c0ca23e00001a121f21e8000000000015d1602d221e8a8c7328ca03b9bdc40c00000000000000000000000930000000000000032f00000000000172f5800000000032c899000000036e1e311241a00000a780000ab000000097800000021bce683dd3a70308000000000000059012d3420000c0200023c1df46f400030ca2f40000b80000808d1800004707ec000644000153400604200017688a26fb33680000000004089828b9265b15681e871e0000000338cf40000000000000000146901078200000000000000001b7075075274c28d05d0e062b633c0fb00005371b900008520001b000000000000000000b6a2500b980006f83770000ce800089f4270e7400000027d0000e1e0002a0000054e89800300000003ef38a8d290780000f58000000000000000101600019189c024c62f0000270c9469f22e80000000000000000aa4388000142c0008ed00000000000000ef0000d320ae2699874d0c41b00001d80004ad46e800046c00041080000007a1000000000000000000009f20000000444ba20003a016d10f6668000000048641100000000006422a600000000001880000fd20302df000000000019c0000000000424085918a48f32a8000d12000005a4246266653ef18d0e489242999a5d12c3852038000aa68140e49db80000253c8248c6820003770000b6e1b12bb84d000019700000000006313089a5479a776000000000052700017c11360b02330d9000076d0001bb407a0000000000a3a00000007cd00000000006000000003579080a7600000000988da7971cda1f000010f3ec9a3400035b3229f94e5c1be063800111205c0001cc499424e000176000000000000001c459d458a0d84d44fb00d034877c67214815a40281b939196142283750001bd0000598000000098448d00000004e86b71ec8cac0003a02c68708e266c91e5945901054840e03246963ea0298000b640a73459cb00b60ed00010fca8600048c80000000000001f291a600000000009de00045f000000085f2e3a04800002300000000003f00001a9c00090600000009565473611d211780b2000000111a4ce27c15e4cfe0d53599560d068c001d80009380000001f091c411b0c08000ee20000000000dca0003b18000d8a0a539f9018000000000209d06e000000000000a0000001bd8d9c00000000000000000000000cfc5d516b8b600000f61f419cc8ca2351018f3062e0b700b0c801fe1820340e8800040115e177423a10500005b50682ef044000000091030180000005
  | 20 => 0x4c82a700001124963b980000004fe18d00007700000000a988e681a38814e40000003111ac80003f125b80000000000080000b204d0260a2209504080000970d9457c3d70000700381000000000039841281141fc8440ee125d1cc2c120916bd21a71c3660ae8bc00002eb9d0c6c60000000000fb804f14e18a00003b03570194664838000068c0000000000000ed400000000008d40000001bbc00000030200000007830001ebc0000003a810ecdb06d31711d5830c14c15a88f442e8db19a8c3c7e48a930d0000f7429d0fc0ec870600018c000070e00000004a40001c022591fcdc4851000030c00070c15c00000502a0000000000000035d00001b477e000033006800014a0000fb40001151e6d1c882007e943800000000000000000002241e74c520000001ac03180000000bf8cb81b60700ac07c664c17b1478a262cb40b8274c1c0000e7800093e80d00000002be2e806f00000820003fd00000000010000c342c200021100000aa000253000098000000000000000003d40188d523b546a16684928c32c39698cc43041a38c852264091eb89480000003eb1708a222bb000000000070608c1b3c55043430c136c0000003f38000f3826807600012380000b380000000003eb80000001d735aa01d0e450800013800003aa000072c0000840000000000000496000023e3550000a1052c5f30000001242092418185800000000006bc0007d3000000000068f000000000065600000000000000000000f9c6643db800000052600010cc0002012fc22d09e865d00017d82020000001b400003bc000164c1260000c91d1020e5c34439ab10d4395000106511844e45a80000005360000000d5a2c3000000000000011c8eb80002af0000c885920001ff80002f63ab0000f6c000000000066c9400000002298cc60004520000ff611e2ce1388fe24270001a6cafa303372000067682b00002a8000000000000084236521b00000007f700013dc88e0002aca35400079a0000000dcc14a2c48b9881400000000004780003de88e80003300001d7c00003f218000075a16c34880000001c4000087865c0001b3000116400043f99504ec0000000694b0c39c392a1010580000f800001ac78715f00011e285a00000000007ab000000000075825f0d640e68ea15200000000003d10d101501bb0c5800000034029a8b44bd00000001eb000000000000000004e10f780000003d1000000000086c02811280000400d6888066600008d00008dc0000001b840008782551434946000000000110050217ea4500c21d90e8166483033c3281d0522c5d43388148f6c4ed4858b1d0bc3ba00020f800073200000005ca000425000000045f000000091c0e52121fd80000004119ddcc8e89100005e4a401d50f116e51dc666117800018c6d71a89b6cde27803ac9
  | 21 => 0x1540f8a9012f295b000000000000000005310001e54dfe636294a25522400000000006c200000001100007db48c17280000000000000c1e5cd2fd00001d000000012246ae0000b4000015a00000000000006062d00fec0007111af00007da7d200015780002d60d980000000000ed1a4800054b2f490680001250518000000000000122c000680000020800000038700000007d4000032c59835c2ff1ff856e00004f800097400001f21a0f9e76025c91e805657f3118ca42a0000426a4b88540000ed80000006430001b490fa40300000011040000001a50000000000152400051b00015b4000000000000000090300015d80005e642c0e992049083c50e9083c67500017c80000002cb000000000000011dc000000000019c90c2482168d48efe0dc0f3000000021f01200007bc0003f78000f903b44278a086ce5511d391c44e67b224822b481a13d28018410624da0ce836c0003eb40081d03d400000023480000001be80b000082e0001b800002471de80000004813bd800000056742612280003b734287d02aa000000194c00089040da4980ea69c1eb0000bce00000007b000017a000124430a523187000000000031200382b800000000000000000001d9832263339c000000000000016b444831533d81a427c8433b4225c00051900000004328a72891b50cc25ac2ae1e7cae03b925a21c00b22001ef96e89d691e1451f441943971b99160ae60c10dea3b063e5e20bc0000b1000029c00000005c40e50f940000833890f146387cd053131c08c000000121cf621df1231c9889e53f2b501380005ec0001a680002d414600000000bb0fe00f00007dd000025000000033ca1a50dc85b3cb1ffc0002110f38128a9471e193800003a0000000000ee80000000000000000327800000077c47918980000003b380000008aa18491c90a000042a19780000000000000b9e0000041d4848400017fa1d52620001589b7c5b60000001af50e800016980784583fc000000000003200007e400000000004107f00be000156c38a0002b293748c035302d00011900000000b3842881e000102c00028e45b9ecd1b4207000227800000042588c51384f230d82e4ad68ba25380000000000000000d3a000297800089a70000013240000002bf1778e96000209800000025a40200004a87821f300009b000000008a46360313f613b0c3c2cf206000105a71936016ec25e6f50f9000058079e0cf058d2185c8172012c6fc62044d169c1901d61859d184ce0811f485c89241560108eb06283f900004086d40000000000000000000000000000024c85500000002f096ad0c0899111000000000029e92a400000000004a80000003d6800000000000011a01f600000000010a653c1180bb49701d300000000000000000e78000336000107117e00038e8e4cbfe
  | 22 => 0x67c117c235800000028497d03fc00000002891260000000000cfa000000000102c000000000012a00032096b918e4170cb1a845e48cc03da4544a22250dd12c013677a33e1c3416620a18f16102923a345600001f400000012f43c267000000000000002688258f7600000000000000000000000000414000000000000013f800000092d18ea35ccbe56315607350c201834990bce501690000000e0872043284b811a04829d0690f860000f48f1914a28900000009340000000b34b8c46300000002841392bd242871a000395000000058f000112448a00000000000de0f43851af090818707800002a400007c84a000081041480006903e447b95988200000fb9ea84a632612b199c00e37808000dc482649000000000048800000003200000d598ec88a000374a378b4647441107040ba5aa0860ecc8b87982bd8e24ba46b63109fc8c8c0000000ff80000eb1a100000004560000000ca4144241800045a000401800000000f3dc95540000001bc9fcc0008cd2db09b800000027800012084d2173888c0000001c7048ce285df3ad0124d102eb1300efc2ee27127189347ea1592b1063c9d242607210587f46e706208f89bc29a25708546ac0000738e28d887ea00000000007cb0000db407438627518200000004719ae11760f21e99428d5602744a194524a14533b00000000e34458000a2a22e2588ca8a0c3af1dda284000106000187ccd620b4420a6c3c03492618d341d272713d220c22e63c12a8a7c0000602218aa4cc08fd2ee000000022836d00000000000001da46b08e813f15b845600d35f80000006fd2c6005493a64e0151c7c24e917000000041800036c965000000000016e000026f1bb12500005f11cd2438d4470b10d243c0008b315504ecd140000000000eaa0b50001164fcc92900010e0ce86390e40000f128663c793c4e8a61700000002e2000000189400069e0000000066835000200800063f0000000000435431893c17e01904616904c20000dc0b1911c01f3098dc411639242103740440002828000cdc00000000006321bc41500004be000000000000000000000005b23500000000000000000093000033e39b80007220002d4160882a6050c223f80003ce2e9a228a5c30513917410da00000012302e07a011917ec03600002a0e848ec0000001a080000000001ba00004d6000025c0003da04500004125610000d8800000047780000c67eb23e83a8a7c8ab03e800088c1303480000a8882f2a088dc90a6aa004800000072231d00000000000b5800000066c4131cd80000003fe1460ebc2b92f70000d480003fc8000f5246b0ac0cf434e306343a4880003c92809dd4f8827b3df90b80006ec17a20740000001e2000031a2dc2c500001cc000432000041e0001ea800084a00000017640000001928000e123a80b2
  | 23 => 0x2c000000013d86ba0000000000d9a47b00000000007070000000ad04fc0ca89acc288f047c94888a60002d084850f200000004540007e00a080284ba6a53a109e00001fd0000000000131110800049473c0391bc07b0000414000096c0380a88000f1604d18412c800000001b153c00006a2ab000000019f13300004d245030aa3cccd20000001cbd0825d62028000000000157056800000000000001685723408598bde1a24631830f268f5149a4bcc9a7d00001d888d800031500000088e936300000003c327e800029c00000022bc60426300012bc0000112499c680000001f70000de600000000000000000a4000000000000000000000f80001d50f460000e8800021017f0000a1c00000000000010d6000037000000075b0680000eae3313b818e00002260001808000000000000000059e000223c32691f07b8c1c5f840f472a3fc0001f600001ac3147f53719f18fdc65734b000017a8e100980000000000170a141300d40000a2c4267050001ce400000040c90ac0002864399d1ca8c000040000047000029297d4ef02802529ef800000021ba30400005100000000004b526a80011888a20001aec0000000000a20c640000000000000792454000116c1e3000205414200026a000010a0002ae96f48a4733000000000083212c8da4b602ec2d298010668ae48d0bcc1c250439d000000000000002bc0007e23a6811c7c000000000001de0003471e2000007c175000017876447d000005e0991090d1800000000007309b20003a78000000000036800124e5951788000cb40004679c8430673d0000bec0000003d211bc0000d9000131860200005d091000000012c0000000143490084000029100010c42486de3518000f1c7023da8d5000013700000000003a517b8000b2451012000006d67e32c703b89664d70000000a4200000009e40cc000000000000000000000000000002f51848f0a4821a2a0e8df261c0a9862047e6fe4098d680006eb14b800036a00028780000000000000470ef22c20000e30d960000d492ec0000000000000bb615e00022140000003a9800000073e0001920b166dd00021744fa00041c843519c138000217100a6d6422933cb7e2ee3de23242d48e03dc0b2800063e2c0071800000000010e8c6036c42ca03000058123c87b80003cf3c6855c000000000000000045a000000081c6b900021f818a8f404f0a491b23fd368874843a18900000000000000001d8436e00000010f000000002615d083e000000035c34c00006881602445fd000147c00000000016a400060900001fc0004dc3c3000029e7e82f693140000000d900000004ff3d2800093c7f800000000000000000f70b2228337e034c0000000001caca6017e02f0cfd1ec47e0481c209ce00040498b0b361a821c800022c1ac37d0af499
  | 24 => 0x18ace760710e39d948e00000000000a644280b7870d1840003e3800095829522a11787ce3ca28600000000f100008200000001fb1ff40008fc02f8000bee00000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x220010898180001c0d0000068000000000088000001f808b99238c000f002010001509000015801a000000000000020023169b0e9126a5801a9e96000000002480000d801b80000a80002a00188585178002a99c80000ca9251207800000002726228817000a04840000280313801400000000000f8000210000000b1298002781000000000380000000000e001d802891930024000607219e0000002080001f149d1981c000000041c14080000000c000404240004000000000014000000080183b87e0164191520060ee1c80590645480183997201641915200686a4c805906454801a199320164191520068a648805906454801a329120164191520068c6448059064548014389059170191520040f65f8690064548012399818040191520068a608601006454801838742016458d520051c241641c5635480145696cc07158d520060d610711816354801a476360831d85520060e9d0805926154801839845c060185520058a64840d93605480142c9648074581520060e20074591605499524d92a177058e420051364a655ce62d040144d929957390b410050b64a655d232d057ba0c6360b43549410040fe61741d165c8401438905d074597210048b64a851cd640840122d92a17305902164c9364a851d1630859324d92a177058c210049a64a859cd600840126992a1443580210040fa60765d152d0001838801d97454b400044ee6174dc152d000143b965d37054b400050b64a401d9525000103d9810076549400050b648401d95250001838801d974549400040f261405d4644c0014c5920c571191300040fe61741d165c8001528905d07454b200040f261405d4644800142c965d074549200048be6164191524800142c9759064549200055864470dcd524800186476205735492000558644705cd524800706c9761b43549200061a1d9801c55248081468965d3705492000619e1d52584614800706c985d952105200040f261405d664c400103f985d074d951000515a5c31d956344001585920c47458d1000523648311d163440018697060865189100050b648655d0624400144d9219573189100041d660311d9524400144d9219573909100050b648655d2324400189471211634c91000471660731892144001854732195248510004d4a6031d953044001711940c7654c110005d064831d9530440913909850d414c110244f0261324853044081660966055248110525d024d815492044149b40835494148110646e020d42505204400166096549214811003f181d9524852044149b40835492148110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x4008000303197644805906454801908c9b22402c8322a400c88649912016419152
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x94c
  | 6 => 0x94e
  | 7 => 0x3
  | 8 => 0x138c
  | 9 => 0x138e
  | 10 => 0x98c
  | 11 => 0x98e
  | 12 => 0x150c
  | 13 => 0x150e
  | 14 => 0x9ce
  | 15 => 0xa0c
  | 16 => 0xa0e
  | 17 => 0x180c
  | 18 => 0x5
  | 19 => 0x180e
  | 20 => 0x209
  | 21 => 0x20c
  | 22 => 0x20e
  | 23 => 0xb09
  | 24 => 0xb0c
  | 25 => 0xb0e
  | 26 => 0x1409
  | 27 => 0x140c
  | 28 => 0x140e
  | 29 => 0x1549
  | 30 => 0x154c
  | 31 => 0x154e
  | 32 => 0xb49
  | 33 => 0xb4e
  | 34 => 0x1449
  | 35 => 0x144e
  | 36 => 0x289
  | 37 => 0x28c
  | 38 => 0x28e
  | 39 => 0x184e
  | 40 => 0xb89
  | 41 => 0xb8c
  | 42 => 0xb8e
  | 43 => 0x1489
  | 44 => 0x148c
  | 45 => 0x148e
  | 46 => 0x1849
  | 47 => 0x184c
  | 48 => 0xcc9
  | 49 => 0xcce
  | 50 => 0x15c9
  | 51 => 0x15ce
  | 52 => 0x409
  | 53 => 0x40c
  | 54 => 0x40e
  | 55 => 0x188e
  | 56 => 0xd09
  | 57 => 0xd0c
  | 58 => 0xd0e
  | 59 => 0x1609
  | 60 => 0x160c
  | 61 => 0x160e
  | 62 => 0x1889
  | 63 => 0x188c
  | 64 => 0xd49
  | 65 => 0xd4c
  | 66 => 0xe89
  | 67 => 0xe8e
  | 68 => 0x18c9
  | 69 => 0x18ce
  | 70 => 0x98954
  | 71 => 0x98956
  | 72 => 0x9ca
  | 73 => 0x9c956
  | 74 => 0xb0956
  | 75 => 0x94b16
  | 76 => 0x140956
  | 77 => 0x95416
  | 78 => 0x16c9
  | 79 => 0xb8956
  | 80 => 0x94b96
  | 81 => 0x148956
  | 82 => 0x95496
  | 83 => 0xd4a
  | 84 => 0xd4954
  | 85 => 0x1a09
  | 86 => 0x14c9
  | 87 => 0x134a
  | 88 => 0x2c9
  | 89 => 0xb1396
  | 90 => 0x138b16
  | 91 => 0xb9396
  | 92 => 0x138b96
  | 93 => 0x15ca
  | 94 => 0xd5394
  | 95 => 0x18ca
  | 96 => 0xd0994
  | 97 => 0x98d16
  | 98 => 0xd0996
  | 99 => 0x99616
  | 100 => 0xd4994
  | 101 => 0x1709
  | 102 => 0x144b
  | 103 => 0xd1514
  | 104 => 0x150d16
  | 105 => 0xd5514
  | 106 => 0x8e
  | 107 => 0x1449d6
  | 108 => 0x9d456
  | 109 => 0x124c
  | 110 => 0xcc9d6
  | 111 => 0x9ccd6
  | 112 => 0x128c
  | 113 => 0xe89d6
  | 114 => 0x9ce96
  | 115 => 0x589
  | 116 => 0x10c
  | 117 => 0x1789
  | 118 => 0x130c
  | 119 => 0x180a16
  | 120 => 0xd0a16
  | 121 => 0xa0d16
  | 122 => 0x188a16
  | 123 => 0xa1896
  | 124 => 0x1949
  | 125 => 0x749
  | 126 => 0xd1816
  | 127 => 0x180d16
  | 128 => 0x189816
  | 129 => 0x181896
  | 130 => 0xccb16
  | 131 => 0x24b
  | 132 => 0x3ca
  | 133 => 0xd5414
  | 134 => 0x168a
  | 135 => 0xccb56
  | 136 => 0x1a0c
  | 137 => 0x58a
  | 138 => 0x1a0a
  | 139 => 0x18d456
  | 140 => 0xb8296
  | 141 => 0xd1856
  | 142 => 0x184b96
  | 143 => 0xb9896
  | 144 => 0xd0b96
  | 145 => 0xb8d16
  | 146 => 0x188b96
  | 147 => 0xe8b96
  | 148 => 0x18cb96
  | 149 => 0x185496
  | 150 => 0x189856
  | 151 => 0xe9856
  | 152 => 0x18d856
  | 153 => 0x104a
  | 154 => 0x18ccd6
  | 155 => 0xd0416
  | 156 => 0x188d14
  | 157 => 0x188d16
  | 158 => 0xd4d14
  | 159 => 0x189616
  | 160 => 0xd5894
  | 161 => 0x128e
  | 162 => 0x170e
  | 163 => 0x18ce96
  | 164 => 0xd49895c
  | 165 => 0x249
  | 166 => 0xd0954
  | 167 => 0x188954
  | 168 => 0x14a
  | 169 => 0xd1394
  | 170 => 0x189394
  | 171 => 0x139416
  | 172 => 0x98d54
  | 173 => 0x9d716
  | 174 => 0x74b91
  | 175 => 0x75611
  | 176 => 0x75791
  | 177 => 0x216d6
  | 178 => 0x3cd52
  | 179 => 0x140d54
  | 180 => 0x155416
  | 181 => 0x154cd6
  | 182 => 0x185316
  | 183 => 0x184d16
  | 184 => 0x184e96
  | 185 => 0x150d54
  | 186 => 0x15cb16
  | 187 => 0xd1894
  | 188 => 0x41316
  | 189 => 0xd0d54
  | 190 => 0x40d16
  | 191 => 0x161896
  | 192 => 0x160116
  | 193 => 0x160996
  | 194 => 0x151296
  | 195 => 0x21416
  | 196 => 0x154b16
  | 197 => 0x1715d6
  | 198 => 0x41896
  | 199 => 0x160d16
  | 200 => 0xd09895c
  | 201 => 0x20d54
  | 202 => 0x160d54
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2234
  | 6 => 6265
  | 5 => 2354
  | 4 => 85
  | 3 => 3
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
  | 7 => packedAt gbK7 (91586+((h/744+packedAt gbK7 (82658+(h % 744)*12) 12) % 3243)*13) 13
  | 6 => packedAt gbK6 (329952+((h/2088+packedAt gbK6 (300720+(h % 2088)*14) 14) % 9097)*14) 14
  | 5 => packedAt gbK5 (148294+((h/784+packedAt gbK5 (138886+(h % 784)*12) 12) % 3758)*13) 13
  | 4 => packedAt gbK4 (6174+((h/28+packedAt gbK4 (5950+(h % 28)*8) 8) % 163)*8) 8
  | 3 => packedAt gbK3 (246+((h/1+packedAt gbK3 (243+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3fff8781e1fc3fffe1fc0380fc28a67c19f793
  | 1 => 0xc1c07801fe1fc380fe1fffff005759b066c9fc
  | 2 => 0xfe007ffe001ffc00ffe003ffff9861c3870e1f
  | 3 => 0x7fffffe00000fffffc0003e07e03f80fe0
  | 4 => 0x7fffffffffff0000000003ff8003fff000
  | 5 => 0xffff8000000000000000000003fffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2430080602404866024188218000214085391
  | 1 => 0x40851000a20c410a2209492a080308b022c0b4
  | 2 => 0xb4082b320012a81095402254e1986141850c0a
  | 3 => 0x10124dd555400024d992b00432e07602d80f40
  | 4 => 0x20207669999b32780000c018437d800377a000
  | 5 => 0x393c0070110220401103006083fefde8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeeeeeafeeaece0feeeeeeafeeaece0feeeeeeafeeaece0feeeeeeafeeaece0feeeeeeafeeaece0feeeeeeafeeaece0feeeeeeafeeaece0feeeeeeafeeaece0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37261
namespace PEqualNP.Outside.L_meta_37261
open PEqualNP.Outside.L_meta_37261.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 26 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_128 : Interval s0Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 134 := (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 (concat bs0_4_96 bs0_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 48 := (concat bs0_5_0 bs0_5_32)
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
theorem bs1_3_0 : Interval s1Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 10 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 12 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
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
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 24 := bs3_3_0
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
theorem bs3_4_96 : Interval s3Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 117 := (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96))
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
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 29 := block_range (n:=29) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 29 := bs5_3_0
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
theorem bs5_4_448 : Interval s5Atlas 4 448 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 473 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat (concat bs5_4_96 bs5_4_128) (concat bs5_4_160 bs5_4_192))) (concat (concat (concat bs5_4_224 bs5_4_256) (concat bs5_4_288 bs5_4_320)) (concat (concat bs5_4_352 bs5_4_384) (concat bs5_4_416 bs5_4_448))))
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
theorem bs5_5_608 : Interval s5Atlas 5 608 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 632 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 (concat bs5_5_96 bs5_5_128))) (concat (concat bs5_5_160 bs5_5_192) (concat bs5_5_224 (concat bs5_5_256 bs5_5_288)))) (concat (concat (concat bs5_5_320 bs5_5_352) (concat bs5_5_384 (concat bs5_5_416 bs5_5_448))) (concat (concat bs5_5_480 bs5_5_512) (concat bs5_5_544 (concat bs5_5_576 bs5_5_608)))))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 3 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_64 : Interval gbAtlas 4 64 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 85 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_2336 : Interval gbAtlas 5 2336 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2354 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 (concat bgb_5_960 bgb_5_992))) (concat (concat bgb_5_1024 bgb_5_1056) (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)))))) (concat (concat (concat (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)) (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)))) (concat (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568)) (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))))) (concat (concat (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 bgb_5_1856)) (concat (concat bgb_5_1888 bgb_5_1920) (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)))) (concat (concat (concat bgb_5_2048 bgb_5_2080) (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176))) (concat (concat bgb_5_2208 bgb_5_2240) (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336)))))))
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
theorem bgb_6_6240 : Interval gbAtlas 6 6240 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6265 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))))) (concat (concat (concat (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928))) (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312))) (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536)))))) (concat (concat (concat (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728))) (concat (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824)) (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)))) (concat (concat (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016)) (concat bgb_6_2048 (concat bgb_6_2080 bgb_6_2112))) (concat (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)) (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304))))) (concat (concat (concat (concat bgb_6_2336 (concat bgb_6_2368 bgb_6_2400)) (concat bgb_6_2432 (concat bgb_6_2464 bgb_6_2496))) (concat (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592)) (concat bgb_6_2624 (concat bgb_6_2656 bgb_6_2688)))) (concat (concat (concat bgb_6_2720 (concat bgb_6_2752 bgb_6_2784)) (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880))) (concat (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104))))))) (concat (concat (concat (concat (concat (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200)) (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296))) (concat (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392)) (concat bgb_6_3424 (concat bgb_6_3456 bgb_6_3488)))) (concat (concat (concat bgb_6_3520 (concat bgb_6_3552 bgb_6_3584)) (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680))) (concat (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776)) (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872))))) (concat (concat (concat (concat bgb_6_3904 (concat bgb_6_3936 bgb_6_3968)) (concat bgb_6_4000 (concat bgb_6_4032 bgb_6_4064))) (concat (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160)) (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256)))) (concat (concat (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352)) (concat bgb_6_4384 (concat bgb_6_4416 bgb_6_4448))) (concat (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544)) (concat (concat bgb_6_4576 bgb_6_4608) (concat bgb_6_4640 bgb_6_4672)))))) (concat (concat (concat (concat (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768)) (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864))) (concat (concat bgb_6_4896 (concat bgb_6_4928 bgb_6_4960)) (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056)))) (concat (concat (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152)) (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248))) (concat (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344)) (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440))))) (concat (concat (concat (concat bgb_6_5472 (concat bgb_6_5504 bgb_6_5536)) (concat bgb_6_5568 (concat bgb_6_5600 bgb_6_5632))) (concat (concat bgb_6_5664 (concat bgb_6_5696 bgb_6_5728)) (concat bgb_6_5760 (concat bgb_6_5792 bgb_6_5824)))) (concat (concat (concat bgb_6_5856 (concat bgb_6_5888 bgb_6_5920)) (concat bgb_6_5952 (concat bgb_6_5984 bgb_6_6016))) (concat (concat bgb_6_6048 (concat bgb_6_6080 bgb_6_6112)) (concat (concat bgb_6_6144 bgb_6_6176) (concat bgb_6_6208 bgb_6_6240))))))))
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
theorem bgb_7_2208 : Interval gbAtlas 7 2208 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2234 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800)))) (concat (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928)) (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)))))) (concat (concat (concat (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)) (concat (concat bgb_7_1248 bgb_7_1280) (concat bgb_7_1312 bgb_7_1344))) (concat (concat (concat bgb_7_1376 bgb_7_1408) (concat bgb_7_1440 bgb_7_1472)) (concat (concat bgb_7_1504 bgb_7_1536) (concat bgb_7_1568 (concat bgb_7_1600 bgb_7_1632))))) (concat (concat (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760)) (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 (concat bgb_7_1888 bgb_7_1920)))) (concat (concat (concat bgb_7_1952 bgb_7_1984) (concat bgb_7_2016 bgb_7_2048)) (concat (concat bgb_7_2080 bgb_7_2112) (concat bgb_7_2144 (concat bgb_7_2176 bgb_7_2208)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 18, 50)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 5 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeeeeeafeeaece0feeeeeeafeeaece0feeeeeeafeeaece0feeeeeeafeeaece0feeeeeeafeeaece0feeeeeeafeeaece0feeeeeeafeeaece0feeeeeeafeeaece0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277071594 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37261.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,4]⟩,⟨.or,[1,6]⟩,⟨.and,[3,7]⟩,⟨.and,[4,5]⟩,⟨.or,[2,9]⟩,⟨.and,[1,10]⟩,⟨.or,[8,11]⟩,⟨.or,[4,5]⟩,⟨.or,[2,13]⟩,⟨.and,[0,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37261

open PEqualNP.Outside.L_meta_37261 in
theorem PEqualNP.Outside.L_meta_37261 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4276808928) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
