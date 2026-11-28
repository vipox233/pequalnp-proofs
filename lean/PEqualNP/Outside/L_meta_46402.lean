import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_46402.Model
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


end PEqualNP.Outside.L_meta_46402.Model

namespace PEqualNP.Outside.L_meta_46402
open PEqualNP.Outside.L_meta_46402.Model
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

def SBf (j : Nat) : Nat := [7, 7, 7, 7, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_46402

namespace PEqualNP.Outside.L_meta_46402
open PEqualNP.Outside.L_meta_46402.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x6a40121600008207c9824400005006c0001c305231a793915064a1d001ce212e98300022401a00550164a3c2004800c040080832a8611c4c7ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1d830f190e0000001e00138000001a000000008f88800000001f8000000000161a880500000b170480121b0a00108006801e81800b9b928e801f0419980901000007801c899c200c860a800c0005800000000000000015000000000d8291020d11800000001780148000100000000000000000000000000000140380188020801587001680131d08880080001008c04000526dca521db54a43af29c855d5390a7ca9994f553329f2a4653d548caeea2995d14532e6990657a50906f2a120cf950319eaa0636e520c6daa418de94031bca80633e540867aa810d794c21aea98437a50086f2a010dd94640baa8c815e53102baa6205b94840b6a90817651102eaa2205d94630baa8c613f544c278a8984f950309eaa0616e520c2daa4185d94430baa88617651882eaa3104fd51209e2a2413e540827aa8105794c20aea98417651082eaa2104f953109eaa621b654c436aa9885d54610f9a8221f340443e080887c8c110f898221f220443e240885d94410
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x18000000000000000000290000208009c580514cab264d4110b458c40442e16210110ac19130442b06448110
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 42
  | 4 => 66
  | 3 => 6
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
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*2) 2
  | 5 => packedAt s0K5 (742+((h/14+packedAt s0K5 (672+(h % 14)*5) 5) % 55)*7) 7
  | 4 => packedAt s0K4 (1870+((h/22+packedAt s0K4 (1782+(h % 22)*4) 4) % 135)*8) 8
  | 3 => packedAt s0K3 (230+((h/2+packedAt s0K3 (228+(h % 2)*1) 1) % 30)*4) 4
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3fe1fffc1fe3f8e1c71f8fff8fc1fc1e09f673
  | 2 => 0xc1fe0e3fe1fc7f1e07e3f1c1f1fe1fe036cb9c
  | 3 => 0x1fff03ffe007ffff803fe01fe001fffc70c1f
  | 4 => 0xfe00003fffff801ffffc0001ffffe001f80fe0
  | 5 => 0xffffffc00000001ffffffffe00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x84242004440401000104824482444444005231
  | 2 => 0x9444a048c480a0240321908c9094494412c294
  | 3 => 0x288844910849500ac802241124089298c50c0a
  | 4 => 0x8194922114012535448002149298089680d40
  | 5 => 0x31118c039992649da693493800310311bfa000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfffcfcccfcfcfc00fffcfcccfcfcfc00fffcfcccfcfcfc00fffcfcccfcfcfc00fffcfcccfcfcfc00fffcfcccfcfcfc00fffcfcccfcfcfc00fffcfcccfcfcfc00, s0N, s0R, (fun _ _ => 0), s0I⟩
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0xa4024007c00a001411b0064022001801e388488c202518e00541964e5140b2e7421a4c2100724046801e4cc2500046d207e342f20ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xa800000000000178000000000000000000000001c8000141c00050001808000000000001e108d0000000000000a000000031308000000000000040000000001000c8580001680000b9380001989800000000700000000001d800000001f82800000000000000e800000048000000011800da0000000000786801a800002000f00000f9d10001a001900001600188000000e1b9103801298001e800b00000000001f00000000170020800895800012000000000000000c000915000000001b00001480000000000600000008010080000adca521db54a43af29c855d5390a7ca9994f553329f2a4653d548caeea2995d14532e6990657a50906f2a120cf950319eaa0636e520c6daa418de94031bca80633e540867aa810d794c21aea98437a50086f2a010dd94640baa8c815e53102baa6205b94840b6a90817651102eaa2205d94630baa8c613f544c278a8984f950309eaa0616e520c2daa4185d94430baa88617651882eaa3104fd51209e2a2413e540827aa8105794c20aea98417651082eaa2104f953109eaa621b654c436aa9885d54610f9a8221f340443e080887c8c110f898221f220443e240885d94410
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x901802a0079c580514cab264d4110b458c40442e16210110ac19130442b06448110
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 42
  | 4 => 66
  | 3 => 6
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (6+((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 2)*2) 2
  | 5 => packedAt s1K5 (728+((h/14+packedAt s1K5 (672+(h % 14)*4) 4) % 55)*7) 7
  | 4 => packedAt s1K4 (1826+((h/22+packedAt s1K4 (1782+(h % 22)*2) 2) % 210)*8) 8
  | 3 => packedAt s1K3 (234+((h/2+packedAt s1K3 (228+(h % 2)*3) 3) % 10)*4) 4
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x3fe1fffc1fe3f8e1c71f8fff8fc1fc1e09f673
  | 2 => 0xc1fe0e3fe1fc7f1e07e3f1c1f1fe1fe036cb9c
  | 3 => 0x1fff03ffe007ffff803fe01fe001fffc70c1f
  | 4 => 0xfe00003fffff801ffffc0001ffffe001f80fe0
  | 5 => 0xffffffc00000001ffffffffe00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x84242004440401000104824482444444005231
  | 2 => 0x9444a048c480a0240321908c9094494412c294
  | 3 => 0x288844910849500ac802241124089298c50c0a
  | 4 => 0x8194922114012535448002149298089680d40
  | 5 => 0x31118c039992649da693493800310311bfa000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfffafaaafafafa00fffafaaafafafa00fffafaaafafafa00fffafaaafafafa00fffafaaafafafa00fffafaaafafafa00fffafaaafafafa00fffafaaafafafa00, s1N, s1R, (fun _ _ => 0), s1I⟩
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x38580180a6c600003c000269c000481cf901088a0000003170469601548c8803c0091d4c0058000105200000025000ca8032a0000003558042000290038480000008439838a00ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fa10fd10f510f910f110fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x56162b5929104a1a010a5e060023003002376c5f00005b3b321d6900000038223f4b03575c680749003c0e093d00631c1e4f1343366f00272a0018517128256e4e48000000412635330800476400006a0000050c55005266201b1700535a65006272001f2446000000120034586d00212e00000f4d044c2c002d603a0045110d500076610b704400731519673e5d6b31002f7439000040544275143028c30268208278410a08058000b3160803140020003100022a60021876e52d0edaa5a1db94a43b6a94879d4310ebca7a15754f42af29c855d5390b5a84214f953329eaa6653e548ca7aa919734c832bd284837950906bca620d754c41b7290836d52106f4a020de54041bd2846379508c67ca818cf55031b7290636d520c6f4a018de54031bd2844379508867ca810cf55021af298435d53086f4a010de54021bb28c817551902bca6205754c40b7290816d52102eca2205d54440bb28c6175518c27ca8184f55030b7290616d520c2eca2185d54430bb28c4175518827ca8104f55020af298415d53082eca2105d54420baa8c217951842e2a3087cd4110f9a0221f240443e280887c10110f998221f230443e260887c0c110f990221f220443e240887c08110f9a8a21f341443e482887c50510f820a21f331443e462887c4c510f818a21f321443e442887c48510f810a21f354443e4a8887c55110f82a221f353443e4a6887c54d10f829a21f343443e486887c50d10f821a21f352443e4a4887c54910f829221f342443e484887c50910f821221f332443e464887c4c910f8192217651042f4a0087c44010
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x6400e0000400c0000000006cac94fc1800a88068c8d070283800842c5054007c4c24c43408dc40b0d4209c00100000f8f030580000a074d80000001cf400003c4400008800ec90005c007800e4008c0c006014b40000b8a4004800bc000000cc00000098000000e801b001040040500882001608384ab498c40442d16310110b898840442e16210110ac99030442b1640c110b898830442e1620c110ac99020442b16408110b498c20442d16308110b498c41442d16310510b898841442e16210510ac99031442b1640c510b898831442e1620c510ac99021442b16408510b498c21442d16308510b4d8d54442d06355110b8d8954442e06255110b498c54442d16315110b898854442e16215110acd9153442b06454d10b8d8953442e06254d10ac99053442b16414d10b898853442e16214d10b898b43442e162d0d10b898a43442e16290d10e450c43442b36454910ac19152442d36354910b418d52442b26414910ac59052442d26314910b458c52442d263d0910b458f42442d26390910b458e42443a14210910ac99332442b164cc910ac99232442b1648c910f04c832442716194010
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 119
  | 3 => 64
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
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*2) 2
  | 5 => packedAt s2K5 (765+((h/15+packedAt s2K5 (720+(h % 15)*3) 3) % 74)*7) 7
  | 4 => packedAt s2K4 (3447+((h/39+packedAt s2K4 (3213+(h % 39)*6) 6) % 155)*8) 8
  | 3 => packedAt s2K3 (2537+((h/21+packedAt s2K3 (2432+(h % 21)*5) 5) % 105)*8) 8
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xe1fe1fc7f0fe3f1c718f8fc3f1f87f0f0b3673
  | 1 => 0xfe1fe1f8ff0fc7e381f1f1fc3e3f87f015cb9c
  | 3 => 0x1ffe00fff007fffe01fe003fc007ffe60c1f
  | 4 => 0xffe00000fffff803fffe00003ffff800f80fe0
  | 5 => 0xffffffff00000003ffffffffc0000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x24424408122040200082824890491122011231
  | 1 => 0x44444401222008040090908892111222014294
  | 3 => 0x1988889244449601b2012411248224cc660c0a
  | 4 => 0x88819924888c024ad524002229266044b80d40
  | 5 => 0x111111800cc924936949493300044088dea000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xffeeeeeeeeeeee00ffeeeeeeeeeeee00ffeeeeeeeeeeee00ffeeeeeeeeeeee00ffeeeeeeeeeeee00ffeeeeeeeeeeee00ffeeeeeeeeeeee00ffeeeeeeeeeeee00, s2N, s2R, (fun _ _ => 0), s2I⟩
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0xa900250000a210000d9e009c006001c5a200808831e5c618003400000080191ca499a00108003a0001c4c54000008c0000028f9624004a81000080000420010631f100ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x38000278000a000000540000061c1a7e80001400004c7a7044005c00667640001e24483c322274183a042a160e345a10524e6e2e367c586a426c60465020824a682c006264723e5e002800560c0026300008000012253c008022685a108000781a238adca5a1db54b43d729687ad52d0e7aa921e7d4d439f2a0875e53d0abaa7a14f953329eaa6659d438ca7ca8194f55032cea186576510caeaa2195e94032bca80655e53106baa620db94841b6a90837a50106f2a020cf953319eaa6639d43cc73a8698dbd4931b6292633e540c67aa818db94831b6a90637a500c6f2a018de94221bca84435e53102baa6205b94840b6a90817651102eaa2204f953309eaa6619d43cc33a86985bd4930b6292613e540c27aa8185b94830b6a906176510c2eaa2185d94620baa8c416e52c42daa5885b94a10b6a94213f5444278a8887c44010
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x288020100184a398b5350f154354432c650d500cb0d4314931c350c524c21d6315110
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 42
  | 4 => 66
  | 3 => 6
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*2) 2
  | 5 => packedAt s3K5 (728+((h/14+packedAt s3K5 (672+(h % 14)*4) 4) % 69)*7) 7
  | 4 => packedAt s3K4 (1892+((h/22+packedAt s3K4 (1782+(h % 22)*5) 5) % 86)*8) 8
  | 3 => packedAt s3K3 (234+((h/2+packedAt s3K3 (228+(h % 2)*3) 3) % 10)*4) 4
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1fe1ff1fc1f1e3e38c7f1f83fc7070fe27349f
  | 1 => 0xe1fe1fe3fe01fc7c0f8fe3fc1f807f0e59c8e7
  | 2 => 0x1ffe003fffe007ff00ffc001fff800f9e0f07
  | 4 => 0xfe000003ffffff9ffff000001ffffff1e00ff8
  | 5 => 0xfffffffc0000001fffffffffe0000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x4c2c42204c22440084130488cc11126203148b
  | 1 => 0xc444c4048464808404852118548226240948a5
  | 2 => 0x98888e4918c0c94d900e4831992704489e0d06
  | 4 => 0x111092210100122920004202484881600250
  | 5 => 0x111118003189125b4a489263000c0881f4a000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xfefeeeeefefe8080fefeeeeefefe8080fefeeeeefefe8080fefeeeeefefe8080fefeeeeefefe8080fefeeeeefefe8080fefeeeeefefe8080fefeeeeefefe8080, s3N, s3R, (fun _ _ => 0), s3I⟩
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x81300364110e2a786144608f8614004810000c8024000255210e0d009cea8341cb11060028000849a400600081e2cb8cc1842d0840588405ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x1080138f001280158b0680021d8000121e9a800000801c051895160c870e1a1d1b8290042081800880080e9b0020001e010a8019169f180f9113048d0609001f8d9c948c000380058a1989800b801797140007801183030000010800402c000128b05e1c2b8166dca5a1db54b43d729687ad52d0e7aa921e7d4d439f2a0875e53d0abaa7a14f953329eaa6659d438ca7ca8194f55032cea186576510caeaa2195e94032bca80655e53106baa620db94841b6a90837a50106f2a020cf953319eaa6639d43cc73a8698dbd4931b6292633e540c67aa818db94831b6a90637a500c6f2a018de94221bca84435e53102baa6205b94840b6a90817651102eaa2204f953309eaa6619d43cc33a86985bd4930b6292613e540c27aa8185b94830b6a906176510c2eaa2185d94620baa8c416e52c42daa5885b94a10b6a94213f5444278a8887c44010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x290820180005a398b5350f154354432c650d500cb0d4314931c350c524c21d6315110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 42
  | 4 => 66
  | 3 => 6
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*2) 2
  | 5 => packedAt s4K5 (742+((h/14+packedAt s4K5 (672+(h % 14)*5) 5) % 55)*7) 7
  | 4 => packedAt s4K4 (1914+((h/22+packedAt s4K4 (1782+(h % 22)*6) 6) % 86)*8) 8
  | 3 => packedAt s4K3 (234+((h/2+packedAt s4K3 (228+(h % 2)*3) 3) % 10)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x1fe1ff1fc1f1e3e38c7f1f83fc7070fe27349f
  | 1 => 0xe1fe1fe3fe01fc7c0f8fe3fc1f807f0e59c8e7
  | 2 => 0x1ffe003fffe007ff00ffc001fff800f9e0f07
  | 3 => 0xfe000003ffffff9ffff000001ffffff1e00ff8
  | 5 => 0xfffffffc0000001fffffffffe0000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x4c2c42204c22440084130488cc11126203148b
  | 1 => 0xc444c4048464808404852118548226240948a5
  | 2 => 0x98888e4918c0c94d900e4831992704489e0d06
  | 3 => 0x111092210100122920004202484881600250
  | 5 => 0x111118003189125b4a489263000c0881f4a000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfeeefeeefe80fe80feeefeeefe80fe80feeefeeefe80fe80feeefeeefe80fe80feeefeeefe80fe80feeefeeefe80fe80feeefeeefe80fe80feeefeeefe80fe80, s4N, s4R, (fun _ _ => 0), s4I⟩
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x132e002800010000000000d0e291a100a921e4a7010f282000000000000064000000000000a002c00000003aa4c0000301912400000000000000000264000000167c7000000000000000000000002c0000000000010000000000081b1288000349d586005400c4ba01202ff43bf43fe43de43fd43bd43dd439d43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x640000003c00000000a40000010c00013800019800400038b978f4000c00718434000155c8000055000000011800e8ac00000051bc000001106c00b46001c40170882564a00114009c018001480190000001acfc0000c400004c5cc12db07dd0200000000001cc000000008c00000004ed4ce068d8751cb000e4018974a9612430000000798d34017c19096c08f99c0000000001580000852001b8015dd400f04594000080bc5801a8013cd4009400001c2dd8000168480000000000dcd000cc00000000000010000000000001440001501529409000293001c000980001a000000001a50401b4000000000000000000c80000002402c21824812424c040e042062280024213d5490ebaa921c755243cfa9a879f5450f3ea4a1e794943cea92879c5250f3ea2a1e794543cea8a879c5150f3ea0a1e794143cea82879c5050e7ca821d794c43cea18875e53d0abaa7a16750f42cea1c859d4350abca6215754c42cea1885765110aeaa2215e94042bca80853e54cca7aa9996750f32cea1c659d434ca7ca8194f55032cea186576510caeaa2195e94032bca80655e53d06baa7a0e750f41cea1c839d43506bca620d754c41cea18836e52106daa420de94041bca80833e54cc67aa998e750f31cea1c639d434c67ca818cf55031cea18636e520c6daa418de94031bca80639d43c86f4a190de54321cea1c437a50886f2a110e750d21cea1843e521086bca7a05754f40cea1e819d439033a86a05794c40aea98819d43102dca4205b54840bb2888175511027ca9984f55330cea1e619d438c33a86984f950309eaa0619d430c2dca4185b54830bb2886175510c33a87905d94720baa8e419d43882eca3105d54620cea1a419d43083d240106750f10b7296216d52c433a87085b94a10b6a94219d434433a86087c44010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x5ca000c80000147cb4b8ec001c10cc000000c028005400780000e4c498044cbc3c68d4ac80f02074f40c84dcd0b070a46c8c5058a82464089c18342c40f84888fc94e8000000600000000000e0003844d800309067041d6801800d0c5003008880a5d855250e946154943a6d815250e986054943a59845250e956114943a69805250e996014943a3d895150e8c6254543a6d815150e986054543a39885150e8d6214543a69805150e996014543a3d895050e8c6254143a5d855050e946154143a39885050e8d6214143a59845050e956114143c550e5110b154354442c650e5010b194354042c550e510cb154354432c650e500cb194354032c350e521070d4354841c650e50107194354041c350e520c70d4354831c650e500c7194354031c650e50c87194354321c650e50887194354221e150d210870d4394840c350d52103154394440c550d511021d6355030c350e520c30d4354830c550e510c3154354430c550e51c83154354720c550e51883154354620e250d200830d4394b10c350d52c430d4394a10c350d52843914344010
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 119
  | 3 => 64
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
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*2) 2
  | 5 => packedAt s5K5 (765+((h/15+packedAt s5K5 (720+(h % 15)*3) 3) % 115)*7) 7
  | 4 => packedAt s5K4 (3369+((h/39+packedAt s5K4 (3213+(h % 39)*4) 4) % 242)*8) 8
  | 3 => packedAt s5K3 (2537+((h/21+packedAt s5K3 (2432+(h % 21)*5) 5) % 84)*8) 8
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x78fe1e3c7f0f1e3cc63f1c387f1c387f29349f
  | 1 => 0x7f1fe03f8ff01fc707c7e03f87e03f8751c8e7
  | 2 => 0x801fffc00fffe007f807ffc007ffc0079e0f07
  | 3 => 0xffe000000ffffffbfff8000007fffff8e00ff8
  | 4 => 0xfffffffff0000003fffffffff8000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xac2c44881622440420b04893304893109148b
  | 1 => 0x16444c901226480902452113152113121148a5
  | 2 => 0x488881924440c9148064982264982241a0d06
  | 3 => 0x20011122488810029490020440922440e00250
  | 4 => 0x4011102000889122a520922440020440e4a000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfefefe80fefefe80fefefe80fefefe80fefefe80fefefe80fefefe80fefefe80fefefe80fefefe80fefefe80fefefe80fefefe80fefefe80fefefe80fefefe80, s5N, s5R, (fun _ _ => 0), s5I⟩
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x1ba200b0baa2649980000002746b990000a0002707c0ad00c500b340020f3a0000d002403a1cbc3297664018106c534068489e389582672d42942031b2b00543800090b0000b34000082051541100206c82b037fd500bfe54007f5500bfc54037fd4c09fe53007f54c09fc5302ffd0c09fe43007f50c09fc43037fd4807fe52007f54807fc5202ffd0807fe42007f50807fc42027fcc807fe32007f4c807fc32037fd4405fe51007f54405fc5102ffd0405fe41007f50405fc41027fcc405fe31007f4c405fc3101ffc8405fe21007f48405fc21037fd4003fe50007f54003fc5002ffd0003fe40007f50003fc40027fcc003fe30007f4c003fc3001ffc8003fe20007f48003fc20017fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x826000ffd9520005feca9003bfe654800d7f32a4000ff59520005faca9003bfc654800d7e32a4000ffd9120005fec890037fe644800b7f3224000ff59120005fac890037fc644800b7e322400effd512006ffca890003fd544801bfe2a24000ffd8d20005fec690033fe63480097f31a4000ff58d20005fac690033fc63480097e31a400effd4d20067fca690003fd5348019fe29a400dffd0d20067fc8690003fd4348019fe21a4001bfd892001ffea49000ffe5248007f72924003ff54920007daa49000ffc5248007ffa124003ff9092001fdc849000ffd4248001f6a124003ff1092001ffe649000ffe3248007f71924003ff4c920007da649000ffc3248001ffb0a4000bfd852005ffcc29000afe6148001feb0a400bff18520015f8c29003bff5148017ff28a4000ff5452005ff8a290037ff4148017ff20a4000ff5052005ff88290033ff3148017ff18a4000ff4c52005ff8629000fff2148007ff10a400bfb8852001ffa429000ffc2148007f610a4001bfd812000ffea090007fe5048003fea824001ff1412000ffe8090007fe4048003fd2024001ff50120007f28090007fc4048003ff9824001ff8c12000ff46090007fd3048001fc9824001ff0c12000ffe409000ffb2048003ff1024001fb8812000ff84090007ec2048003fc1024001ffc412000ffc2090007fc1048001ffb2a2000bfd9510057fcca8801afe6544001feb2a2000bf59510057f8ca8801afc6544001ffb222000bfd911004ffcc888016fe6444001feb222000bf5911004ff8c888016fc6444015ffaa22009ff95110007faa888027fc5444001ffb1a2000bfd8d10047fcc688012fe6344001feb1a2000bf58d10047f8c688012fc6344015ffa9a2008ff94d10007faa688023fc5344013ffa1a2008ff90d10007fa8688023fc4344001ffb122000bfd891003ffcc48800efe6244001feb122000bf5891003ff8c48800efc6244015ffa922007ff94910007faa48801ffc5244013ffa122007ff90910007fa848801ffc4244011ff9922007ff8c910007fa648801ffc32440037fb0a2002ffd4510017fca28800bf65144005fea8a2000fd54510017f8a28800bff4144005ff20a2002fd90510017fa8288003f54144005fe20a2002ffcc510017fc628800bf63144005fe98a2000fd4c510017f8628800bff214400ffb90a2002ff88510017fa428800bfc2144005fa10a2001bfd811000ffea088007fe5044003fd2822001ff54110007f2a088007fc5044003ffa022001ff9011000ff48088007fd4044001fca022001ff1011000ffe6088007fe3044003fd1822001ff4c110007f26088007fc3044003ff9022007fec811000ffc4088007fd2044003fe1022001fe0811000ffe208800bfb1044003ff0822001fd8411000ff82088007f41044003fc0822001fc04110
  | 1 => 0xffc3154031ff90aa017ff88550007fa42a805ffc21540037fb02a001ffd4150037f6a0a8007fe5054003bf282a001ff1415000ef8a0a8007f85054003ffa02a001ff9015000ff880a8007ff3054003ff182a001ff0c15000ffe40a8007fe2054003fe102a001ffc415000ffc20a8007fa1054003fe082a000ffd9540005fecaa005bfe655000d7f32a8000ff59540005facaa005bfc655000d7e32a8001bfd914002ffea8a0017fe545000bdf2a28005ff551400077aa8a0017fc5450001ffb1a8000bfd8d400affcc6a0012fe6350001feb1a8015ff18d40025f8c6a005bff535002bff29a8000ff54d400aff8a6a0017ff435000bdfa1a8005ff90d4002ffa86a0003bd435000bfe21a8000ffd8940005fec4a0053fe62500077f3128000ff589400a7f8c4a000efc625002dffa928014ff94940007faa4a0053fc525000bffa128005ff9094002ffa84a0017fc425002bff9928014ff8c940007fa64a0053fc3250001ffb0a8000bfd854009ffcc2a000afe6150001feb0a8013ff18540015f8c2a005bff5150027ff28a8000ff5454009ff8a2a0017ff415000bff20a8005ff5054002ff882a0057ff3150027ff18a8000ff4c54009ff862a0053ff2150027ff10a8000ff4854009ff842a0006ff6050003ffa828001ff9414000ffaa0a0007fc5050003ffa028005fed014000ffc80a0007be4050003fe2028001ef1014000ff080a0007ff3050003ff1828001ff0c14000ffe40a0007fe2050003fd1028001ff0814000ffe20a0007fe1050003fd0828001ff04140007feca98002ff654c025ff32a6006bf99530007faca98002fd654c025fe32a6006bf19530007fec898002ff644c023ff3226005bf99130007fac898002fd644c023fe3226005bf19130097fea898047fe544c001feaa26011ff1513000dfec698013ff534c009ff29a6004f794d30027faa698003dd534c009fe29a6004ffd0d30027fc8698013de434c009fea1a6000f750d30027f88698003ff624c0017fb126010ff9893001dfcc498003fd624c021fe3126003bf18930097fea498043fe524c001fea926010ff1493008ffe8498043fe424c001fea126010ff10930027fe6498013fe324c009fe9926004ff0c930007fec298002ff614c01fff30a6002bf98530007fac29803ffc614c0057e30a6012ffd453007ffca298003fd514c01ffe28a6011ffd053007ffc8298003fd414c01ffe20a6004ffcc530027fc6298013fd314c009fe18a6010ffc853007ffc4298003fd214c01ffe10a6001bfd813000ffea098007fe504c003fea826001ff1413000ffe8098007fe404c003fea026001ff1013000ffe6098013fb304c003ff1826001f78c13000ff86098007dc304c003fc1826001ffc813000ffc4098007fa204c003fe1026001ffc413000ffc2098007fa104c003fe0
  | 2 => 0x31107fc8498803fd424c441fe2126204ffcc931027fc6498813fd324c409fe1926202bfd8531017fea29880bfe514c405fea8a6202ff14531017fe829880bfe414c405fea0a6202ff10531017fe6298813f7314c405ff18a6202f78c531017f8629880bdc314c405fa18a6202ffc8531017fc429880bf6214c405fe10a6200ffd8131005fec09887ffe604c4037f3026200ff581310fff8c098806fc604c445ffa82621fff941310fff8a098887ff404c43fff202621fff10131027fe6098813fe304c409fe1826220ffc81310fffc409887ffc204c405ff8826202fdc4131017fc209880bfc104c401ffb2a4200bfd95210f7fcca9081afe6548401feb2a4200bf595210f7f8ca9081afc6548401ffb224200bfd91210effcc890816fe6448401feb224200bf591210eff8c890816fc644843dffaa2421dff95121007faa890877fc5448401ffb1a4200bfd8d210e7fcc690812fe6348401feb1a4200bf58d210e7f8c690812fc634843dffa9a421cff94d21007faa690873fc534843bffa1a421cff90d21007fa8690873fc43484057fb124203ffd492101ffca49080fee5248407fea924200fb5492101ff8a49080fff4248407ff2124203fb9092101ffa8490803ed4248407fe2124203ffcc92101ffc649080fee3248407fe9924200fb4c92101ff8649080aff6148405ffa8a4202ff94521017faa29080bfc5148405ffa0a4202ff90521017ec829080bfd4148401faa0a4202ff10521017fe629080bfe3148405fb18a4202ff4c521007ea629080bfc3148405ff90a4203fdc8521017fc429080bee2148405fe10a4202fb08521017e84290803ff60484017fb02421bff9812100dfcc090803fd6048437fe3024201bf181210f7fea09086ffe5048437fe282421dffd01210dffc809086ffc4048439ff982421bff8c1210dff8609080fff2048407ff102421bfb8812101ff8409080fec2048405ff8824202ff84121017f82090806ff6554001ffb22a000bfd91500d7fcc8a8016fe6454001feb22a01aff1915002df8c8a801bff545400dbfaa2a006ff95150037faa8a80037d545400dfe2a2a000ffd8d50005fec6a8067fe63540097f31aa000ff58d500cff8c6a8012fc635400dffa9aa006dfd4d50037fca6a801bfd5354001bea9aa006ff14d500d7fe86a8067fe4354001fea1aa019ff10d50007fec4a8002ff6254031ff312a003bf98950007fac4a8063fc62540077e312a006ffd4950037fca4a801bfd525400dfe292a01affd09500c7fc84a8003fd4254031fe212a019ffcc9500c7fc64a8003fd3254031fe192a000ffd8550005fec2a805ffe61540057f30aa000ff585500bff8c2a800afc615400dffa8aa006ff94550037faa2a801bfc5154035ffa0aa017ff90550007fa82a805ffc4154033ff98aa017ff8c550007fa62a805
  | 3 => 0xe322a205bf19151037fea8a881b7f545440dff2a2a206ff55151006faa8a881bfc5454401ffb1aa200bfd8d5114ffcc6a8812fe6354401feb1aa229ff18d51025f8c6a881bff535440dbfa9aa206ff94d51037faa6a88037d535440dfe29aa22affd0d5114ffc86a8803fd4354453fe21aa200ffd8951005fec4a88a3fe62544077f312a200ff58951147f8c4a880efc625440dffa92a206ff94951037faa4a881bfc5254455ffa12a228ff90951007fa84a88a3fc4254453ff992a228ff8c951007fa64a88a3fc32544057fb0aa202ffd4551037eea2a880bfe5154405bf28aa202ff14551016f8a2a880bf45154405ffa0aa202ff90551017f882a880bff3154405ff18aa202ff0c551017fe42a880bfe2154405fe10aa200ffd8151005fec0a889ffe60544037f302a200ff5815113ff8c0a8806fc605440dffa82a206ff94151037f8a0a88abff405444fff202a227ff1015114ffe60a889ffe305444ffe182a228ffc815113ffc40a889ffc2054405ff882a202fdc4151017fc20a880bfc1054401ffb2a8200bfd9541137fccaa081afe6550401feb2a8200bf59541137f8caa081afc65504057fb228205ffd514102ffca8a0817be545040bfeaa28200ef5514102ff8a8a0803ff63504017fb1a8225ff98d41025fcc6a0803fd635044bfe31a8204bf18d41137fea6a0897fe5350401fea9a8225ff14d4102ffe86a0817bf435040bff21a8205ff50d410077a86a0817fc4350401ffb128200bfd8941127fcc4a080efe6250401feb128224ff1894101df8c4a089bff5250449ff2928200ff54941127f8a4a0817ff425040bff2128205ff5094102ff884a0897ff3250449ff1928200ff4c941127f864a080aff6150405ffa8a8202ff94541017faa2a080bfc5150405ffa0a8205fdd0541017fc82a080bbe4150405fe20a8202ef10541017e882a080bff3150405ff18a8202ff0c541017fe42a080bfe2150405fb10a8202ff08541007fec0a0802ff6050447ff3028201bf98141007fac0a088ffc60504037e3028226ffd414111ffca0a088ffc505040bffa028205ff9014102ff880a0897ff3050447ff1828223ff0c141127fe40a088ffe2050447fe1028202ffc4141017ee20a080bfe1050405fe0828200ffd9531005feca9888bfe654c40d7f32a6200ff59531005faca9888bfc654c40d7e32a6200ffd9131005fec898887fe644c40b7f3226200ff59131005fac898887fc644c40b7e3226222ffd513110ffca898803fd544c443fe2a26202bfd8d31027fea698813fe534c409ef29a6204ff54d31007baa698813fc534c409ffa1a6204ff90d31027bc8698813fd434c401eea1a6204ff10d31007fec498802ff624c441ff3126203bf98931007fac498883fc624c4077e3126222ffd4931107fca498803fd524c441fe2926221ffd09
  | 4 => 0xafc615480dffa8aa406ff94552037f8a2a90dbff4154869ff20aa434ff105521affe62a90d3fe3154869fe18aa403ffc855201fde42a900ffe2154807fe10aa400ffd8152005fec0a90cffe60548037f302a400ff5815219ff8c0a9006fc605480dffa82a406ff94152037f8a0a90dbff4054867ff202a433ff101521affe60a90cffe3054867fe182a403ffc815201fde40a900ffe2054807fe102a434ffc415219ffc20a90cffc1054801ffb2a8400bfd9542197fccaa101afe6550801feb2a8400bf59542197f8caa101afc65508077fb228405ffd514202ffca8a1017fd545080bfe2a28400ffd8d42005fec6a10c7fe63508097f31a8400ff58d4218ff8c6a1012fc6350865ffa9a8431ff94d42007faa6a10c7fc535080bffa1a8405efd0d4202ffc86a1017fd4350801dea1a8405ff10d4201dfec4a100fff5250807ff2928403ff5494201ff8a4a100fff425080bf7a128403ff9094201f7c84a100ffc4250807de2128403fb1094201ffe64a100ffe3250807fe1928400ffd8542005fec2a10c3fe61508057f30a8400ff58542187f8c2a100afc6150865ffa8a8430ff94542187f8a2a1017ff415080bff20a8405ff1054218ffe62a10c3fe3150861fe18a8403ffc854201fde42a100ffe2150807fe10a8400ffd8142005fec0a10bffe60508037f3028400ff5814217ff8c0a1006fc6050865ffa82842fff9414217ff8a0a1017ff405080bff2028405ff1014218ffe60a10bffe305085ffe1828403ffc814201fde40a100ffe2050807fe1028430ffc414217ffc20a10bffc1050801ffb2a6400bfd9532177fcca9901afe654c801feb2a6400bf59532177f8ca9901afc654c801ffb226400bfd913216ffcc899016fe644c801feb226400bf5913216ff8c899016fc644c85dffaa2642dff95132007faa8990b7fc544c8077fb1a6404ffd4d32027fca699013fd534c809fe29a6404ffd0d32027fc8699013de434c809fea1a6400f750d32027f8869900eff624c807ffa926403ff9493201ffaa49900ffc524c807ffa126403ff9093201ffa849900ffc424c807ff9926404fbcc93201ffc649900fde324c807fe1926403f70c93201fd86499003ff614c8017fb0a642cff98532015fcc299003fd614c859fe30a6402bf18532177fea2990b3fe514c859fe28a642dffd0532167fc82990b3fc414c809ff98a6404ff8c532027f8629900fff214c807f790a6403ff8853201ff84299003ff604c8017fb02642bff9813200dfcc099003fd604c857fe3026401bf18132177fea0990affe504c857fe282642dffd013215ffc80990affc404c809ff9826404ff8c132027f8609900fff204c807f79026403ff8813201ff840990b3ff104c857ff082642bff04132015fecaa8803ff64544017fb22a22aff9915102dfcc8a8803fd6454455f
  | 5 => 0x51531f6fca8a981bfd5454c0dfe2a2a606df15153025fec6a9813ff5354c0defa9aa604ff94d53026fca6a9813fc5354c09be29aa604f714d53027fe86a9813fe4354c09fe21aa600ffd8953005fec4a98f7fe6254c077f312a600ff589531eff8c4a980efc6254c0dffa92a606dfd4953037fca4a981bfc5254c7dffa12a63dff909531eff884a9813ff3254c09ff192a604ff0c953007fec2a9802ff6154c79ff30aa602bf98553007fac2a98f3fc6154c057e30aa606ffd4553036fea2a981bfe5154c0dfe28aa63effd05531e7fc82a98f3fc4154c09ff98aa604f7cc553027fc62a9813fc3154c7bff90aa63cff885531e7f842a9803ff6054c017fb02a63bff9815300dfcc0a9803fd6054c77fe302a601bf18153037fea0a981b7f5054c0dff282a606ff141531f7fe80a98effe4054c77fe202a604ffcc153027be60a9813fe3054c09fe182a63dffc81531dffc40a98effc2054c79ff882a63bff841531dff820a9803ff6550c017fb2a863aff99543035fccaa1803fd6550c017eb2a863aff19543035f8caa1812ff6450c0bffaa2863aefd514302ffca8a1817fd5450c0bfe2a28605ef15143025fec6a1813ff5350c75efa9a8604ff94d43027faa6a1813fc5350c09ee29a8604ffd0d4302fbe86a1813fe4350c09df21a8604ff10d430277886a1813dc4350c09ce21a8600ffd8943005fec4a18e7fe6250c077f3128600ff589431cff8c4a180efc6250c75ffa928639ff949431cff8a4a1817ff4250c0bdfa128605ff9094302ff884a1813ff3250c09ef9928604ff8c943027f864a1803ff6150c017fb0a8638ff98543015fcc2a1803fd6150c71fe30a8602bf185431d7fea2a18e3fe5150c71fe28a8605ffd054302f7e82a1817fe4150c0bfe20a8604ffcc543027be62a1813fe3150c09fe18a8639ffc85431c7fc42a18e3fc2150c01ffb028600bfd81431bffcc0a1806fe6050c01feb028637ff1814300df8c0a18ebff5050c6fff2828637ff1414302ffe80a1817bf4050c0bff2028605ff10143027fe60a1813df3050c09ff1828604ff0c1431cffe40a18dffe2050c6ffe1028638ffc41431bffc20a18dffc1050c077fb2aa400ffd9152005fec8a90dbfe645480b7f322a400ff591521b7f8c8a9016fc645480dffaa2a406dfd5152037fca8a901bfd5454801beaa2a406ff15152007fec6a9002ff635486bff31aa404bf98d52007fac6a90d7fc63548097e31aa406ffd4d52036fea6a901bfe535480dfea9aa400df54d52037f8a6a90dbff435486bff21aa400ff50d521aff886a900eff6254807ffa92a406fbd495201ffca4a900f7e5254807fe292a403df1495201fd8a4a900fff4254807ff212a403ff1095201ffe64a900ffe3254807fe192a400ffd8552005fec2a90d3fe61548057f30aa400ff585521a7f8c2a9
  | 6 => 0xa112ea4a00a294a760001428000002a8ab00000000000002080000a321ea051c9a9e8000002a48002248598001498000e39dc8001fb2b080000000000016f0000000001eb15b11b8001f48001d70000000001898dfa23a880cb8000000d116c86a0000b58951d1969a4e0000000000001580f796d0000b892d8000000000002749bd1818a70f618513180000029800001baab2759e094f94222280028d0000000001860000509591db95a906a3400008a20d9d88002660002458002b40001dc25480000000019c22e1ce0000cd0000dc0001be0000001188048000918000000000ef80000019a8f88000001890000001e800000007580000026a0d912605b8c005e8618000001ed80000000000000000008e2520000000000f38000000000000c2000400390400006608040005210000e1812918001080000000160c0000480210271004020000000241002028804000c028000004420004200401404600a4c00054100a420800000020200011886100000304420804058c62004020840000064084eb0000030040000610000000c4000c0008001000230800318c06000000042008420100600088012840194230210230001008220002f58800004001044000800280011044008000000a0198030840608c400000302864300240000118001004030006300000208060100000062080a02088508060004040048411800000240080d0080000160000041000018000080e008081500020108008003490e008c07098c001400180060580408c8003423200200800018420180230040020460000020802002dfecaaa016ff645500bffaa2a806efd515402ffca8aa0177e545500bfe2a2a805df1515402f78a8aa003ff63550017fb1aa842ff98d54025fcc6aa003fd6355085fe31aa804bf18d54037fea6aa01bfe5355085bf29aa806ff14d54036f8a6aa017ff435500bff21aa805ff10d54007fec4aa002ff6255083ff312a803bf98954007fac4aa107fc62550077e312a806ffd4954036fea4aa01bfe525500dfe292a805ffd095402ffc84aa017fc4255085ff992a841ff8c95420ff864aa003ff61550017fb0aa840ff98554015fcc2aa003fd6155081fe30aa802bf18554037fea2aa01b7f515500dff28aa806ff1455402ffe82aa017bf415500bff20aa805ff10554217fe62aa103fe3155081fe18aa841ffc8554207fc42aa103fc2155001ffb02a800bfd81541fffcc0aa006fe6055001feb02a83fff1815400df8c0aa01bff505500dbfa82a806ff94154037f8a0aa017ff405500bdfa02a805ff9015402ff880aa10bff305507fff182a83fff0c15420ffe40aa0fffe205507ffe102a840ffc41541fffc20aa0fffc10550097fb2aa600ffd9153005fec8a98fbfe6454c0b7f322a600ff591531f7f8c8a9816fc6454c0dffaa2a606ff9
  | 7 => 0x1b30000e72c20001c50000000000000000001a12a60001160000000000da8000590000001df93ea4e8000b9ab1a5100000000000000000000015300000c0838002a51808ed97e9411a902205daaa80025a2b20002230fe97114a80000000000010180004080000000900000000000023c0a92c40d01af9958419fd21e0f90eb1f58938d38000000f18202a728ea412720000e100000000000000000023aa370332bea0c8000000000000000002738000000000000532a78000312a90521520000b780014c00000000000006e00026b1529ab80020e911000145ab50000000001a5110000065a2c2989330de8d720580003e00000f919a561768001738a80000000000000138002890000000000000930001949a38000000002099b880000000000000000000000020780009b9ef89e8000000000c61e00000858bbab60000001770001020c32bc0020a38000fd1b91320b180000000000b80000000000000025f800126aad80000002b000000257929a9d0000110cf29c0000000089d920083386f8002849e582780004300000013f0000e28e000000005b00000007180000023801f0318000af0000002361dd984800000000040211a0d1968000001ee9aa0000000001c280000000000000004f80000027b0000582b88978000000000000000001950000000000000000000000000000000000000878000000002308270000000000001a80000208002b909f2528000000000001d48f727e00000001900000000000000023493e1bc96a8000018118000000002969dd069a6fa4421b8000002788000498000458f30c68b082b9e20b31c18000000001f0a9a00000000000000020680000024da9400000014e00019b81700015500019880000000019e0241ef00000000000000000000000013d80022c80000000016b80006f00018b0001d420404287f10b88480012700000016300007100010d112000283a3d9382c504700009d80027a00021a80003f8ee96500000005d00023300003600000000000027c8001008000528000561c39ea9da19c800000000000000171a502b823e0002be1af0001900c418c00000007b8000000001c20001e31f29a70000000351f88568000001791638960000000000000000788000000001d800000015c0790000000002130009f78588d194705c8c7094aa180000023ba498000000000001e98249098d31f626221c80004d0001e600000009a2319fd8002950391ae8478000001e71a89600000000001f680023f12500021b0000000000e61351a08002091910fb15ba6e11590e8369c5aa29cba2e853a6c022a031bd82918e8d78e812880000000000000020f28b2900000000be0000000cd8000002592ae8000000001ca8000000000000940001b295faa68b48000caaa829100007685000010622983580000
  | 8 => 0x8a9bc23c8688f809d00023500021a00000011c93a01ea7ea278ce07e8001b18000000e780024b800000063a1018f8000001e400000015700002d8000000000001c90000000700000a200000020000000012080000024f0000000000000000000000ef00000000022580000000000027780016c0000002a98000000ff00000008f24025b90783426e8a593d10f24080023a2c48000000000001cfa9c9cd8000000000f98000002a41ff0000000078000002c100000006800000020babf1568aea568000000000178000002150ae202000000000000012a1601a00000000022b83f0002640b800000025d00000017303980013c80000000010c80025400018880000000000000007c00003c8812432289218000000000002268002af00019180000000027800000000011a8002580c281220480018d9938000000000001578001ac00000000000006600002f0001728001df0002ad0ca00f00000e11b07795e034800055a420000002630000000000000000000000001b980002a0001640000001f400011d1920001210000000000001881a694c8000830000000000000000000000000001148000002958888000001430002210000ff9328001540000001eb80000000000015d8002c28002368002bfa918000ed1379ed0000002740df2828000000002bb0e497400000000011800000028f800112a702c303e8c88001e50000000002bb8000000000000000d204c00000007821200b0000000000002b6800000000148a6d0000000002220000691bb00000020180000028087a08680016f975a868000000000000002bc9539a18001be800000000000064000000000000159aa113688d80000000011e1c0287a2b00012b00000d97e04880e9ab08c00000000000000000000000026700002a800000000203864a5e9688000000000000af80004486d8001e299d0450001f38000000000002b380008a80000028000009c1d69b72c789221785f8720808a18000000dc8000000e18000211980000fb80028417a2818001092192480002a022a2c58000000000001b200000000017f93880000009882800000000000014d800000000127800009800137000000000000000108266a60a3e82507e0d680020e00000000a80000000000000003b12000000022d9232490001691f70000bf14b80000000000023b00000025700000029b0001ea0000cc0422108000f524281d0001780000002550e90000001f20000000000000000000b68000000002a2095a0c0ad2089050b20000002b70000000000bd8180000000000000302028070000000000b42128002a08000001e480013aa4480000000021589994180010a21680000000008207f800054ab59e90600d80001ca0000000000002c18a880000000000023217c0002291259e12a59839b1165800000025975
  | 9 => 0x6a3986700000026980024f84600000000000026a80000000000000017b23d0001810000db00000d00015f0002bd1ba00029f9130002ae0ce8f0a4a97480000000029200000000026f0002681628981fa10e2390e898000000012c01d80000000000014f0000001480000000aa8000ad8002861d084e0492c3a140000001620000001ec0000000000000002ab80015ea830000000000610000000002b980008b89280028719d8000001478001450000001b610a8f010d9c88000ea000000000000000285a5c8d98e085194e800263929043a7315d0000000db8d0a790219070fd8ab8289618069cd0000002538000000000198760c19a296e8000000001970001240000000000000000b900009918c8000001a48001bf0000000570000f413c00000000000000016b0000000000000000001722ac80020faaf95c80009a80000027f9f812f1a78160c981b1b40000000001ff86a800000000000262a419d31561010002260002690000000000000c08000002888370000ba80004428d88180000000000002c00029a8002180000b10000000000000000a01f10000f69c80ac0000000000000001979bb8002208541509fe80000000025d80000000000000000000000000000007080028e00000000021f80017d0001841cb0001a5800000000063265000000155a970000001b581c01880000006c000000268a4780029980000019081500600000000000000000000011900012480015013b80000000001416780000000022180005a0002b28000001c405e00000003d80000007d80004d80000000000007d0000000002598ee1f1933837a240001a98002b31b78000e411d9b008702c9940ec0f222a9359a200000000000009b09e0000000851d793b12200024624726b8001ba80000000000006780000000004b00000000000000018700010480005a82980000000021d0001760321c680000000015a0d580000019f00000000000000001c80000027080008d00000013400012b94a0000000000968001c485c000130206000261000057a9d80000000011796480000000000000020a8000001ee0000001fba9f1b680000000000022f9138000000000000e5ac70000002488000bc9038b50c3a5e1d392a28100000000000000004c8000001db04f0000000000e22c680000024683d0000000001fe000000000000000272a1d82d0000fc9f9ab48000001a00001a4170a5c00016da148000000a680000000000006b0000001449ce9088000cc9d98000d2832a929de00828c1789c10000c7800186800000000000000002a9b8000000000000000000000001f30e30000000000000000058bf90580027c00000000000022000000011f80000004680000018e00000024b0000001830002508001cc80013f80008410405f0000dd9fa830ab11fc8b28de1589
  | 10 => 0xa08000000000002990b0233a7700019a1aaa2f18f1b08a280008c80000028b800000238a6580008622700000000000000001591e841217000000000275199122800000103000014aba00000011509114080000000000001e000000000073a8a09c9960970000000000000000000000000000aca378002ba8000000001c098580025f0000000c80002518000c900012c80000000000024c8001118000a98aa00000006ca55a5300000000000000020700020b0000230000c111f1d00c480000004ea3017b80000000000000027980014400000002f80000427f02e00000000000010b0000000000000000000000001a300007307518296721980013491c2960770001f000000000003b8000f288b0000000f48000000381ac8000000000000ec98d0001b4a138748000000000002939610000000001930001ad80000000028f0001daa7d8001de9168000e5114089000000000000000000177a67aac0ea81000000000011080000000000000000000000000000028998780010f80004a92f95187280024d29e1e38f10000001c31fc04a1661608239d298b88e8000000000000d500026485500000021f07986699e80000000000000007402e8000002329402b7946a35a7babd87c8000000c50000000001a60002909eca8a9e68000000000be90c0000000001511c78001e780000003c0e6a82038800000000271800000000000123810800000000000000000016a1c0620000000001390bb0b606519b0001cf03a9170d40001f50000fa0000000bd00007a9681282852312aa00000000000397c8608000c20b39f90908001b80fc0000000fa80014b17da439668a52710881bf80000000000000000000024500000023fa010000510000ab00000012e17a8000260000000000000002618000000000000000000001998000000002280000000002a30000000000000000b700026c80008280000000008f80000000100000020a0000d626d93980025b08986d0eb8001b39d20f58900050000000000001cc08017f0002188cb2110a406e8000d494907b16a0000000001d592d1701c600010001a813258ac60000000000000001310000000000e98000cf8001028000001308000000000000000000000000000000000000000000000a60000000000000000000000000000000002a38000000000001e8a9792aa2500c80000325a8002c004b80002684800016e1d11ad27a80014d1d51c71b515491a14618222d1361e18da27d28c8a7ac086283a2930dd19f9ae0bc00000017980000000000000000000006b80000001f89f8000a48001d60fe00000000000000019280024c0000000000000000002600d880000000000014398a0ba0000c580027
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x23054510247f3205451013ff0205451000df4765051002ef4765051000cf47650510005f77550510005f57550510015f77450510017b77450510007b7645051002ef6645051002ef4645051004fb4645051004fb65450510007b55450510005f7735051004fb74350510007b5435051003df6725051003df47250510006f76250510006f56250510007f3705051000df6705051000df4705051011ff0705051000df07050510016f76050510017f3605051011ff2505051011ff2405051011ff2305051023ff3205051011ff0205051000df4764c510026f4764c51000cf4764c510005f7754c510005f5754c510005f7744c510005f5744c510015f7734c510017d7734c510007d7634c510026f6634c510026f4634c510047d4634c510047d6534c510007d5534c510047d6434c510007d5434c51003df6724c51003df4724c510006f7624c510006f5624c510007f3704c51000df6704c51000df4704c5100fff0704c51000df0704c510016f7604c510017f3604c5100fff2504c5100fff2404c5100fff2304c510237f3204c5100fff0204c510015f87654110036f87654110014f8765411000dfb755411000f7b75541100077b6554110036fa6554110036f86554110057786554110005fb74541100577b5454110007795454110005fb73541100577b535411000779535411003dfa725411003df87254110007f37154110015fa7154110015f871541100bff07154110015f0715411000efb615411000ff361541100bff25154110057f151541100bff24154110007f141541100bff23154110007f1315411022ff321541100bff02154110015f8765011002ef87650110014f87650110005fb7550110005f9755011000dfb745011000fbb7450110007bb645011002efa645011002ef8645011004fb8645011004fba5450110007b95450110005fb735011004fbb4350110007b9435011003dfa725011003df87250110006fb6250110006f96250110007f37150110015fa7150110015f8715011009ff07150110015f0715011000efb615011000ff3615011009ff25150110007f1515011009ff2415011004ff1415011009ff23150110007f13150110227f3215011009ff02150110015f8764c110026f8764c110014f8764c110005fb754c110005f9754c110005fb744c110005f9744c11000dfb734c11000fdb734c110007db634c110026fa634c110026f8634c110047d8634c110047da534c110007d9534c110047da434c110007d9434c11003dfa724c11003df8724c110006fb624c110006f9624c110007f3714c110015fa714c110015f8714c11007ff0714c110015f0714c11000efb614c11000ff3614c11007ff2514c110007f1514c11007ff2414c110007f1414c11007ff2314c110047f1314c11021ff3214c11007ff0214c110
  | 1 => 0x8d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100367e6554d100067d6554d10026de6354d10006dd6354d10015f67154d1000dfa7054d101dff01054d10004ff7650d10004fe7650d10004fd7650d10004fc7650d1002ebe6450d10006bd6450d10026de6350d10006dd6350d100479c4350d10015f67150d1000dfa7050d101bff01050d1001cfe76d891003eee62d8910015f671d891000df571d891003fe721d891000dfa70d8910015f970d891003feb20d8910257f010d8910034fe75d8910004fd75d8910034fc75d891002cfe74d8910004fd74d891002cfc74d8910024fe73d8910004fd73d8910024fc73d89100dcfd72d891000cff71d8910014fe71d891000cfd71d8910256f571d891000cf571d8910014fc71d8910266f641d8910266f631d8910266ef21d891003ef721d8910266ed21d8910266f421d8910014ff70d891000cfe70d8910014fd70d8910266f970d8910014f970d891000cfc70d8910256fa40d8910256fa30d8910256ef20d891003efb20d8910256ed20d8910256f820d891001cff765891003eec625891024df7715891005fe4215891025dfb70589100dfe820589100dff01058910004ff7558910034fe7558910034fc7558910004ff745891002cfe745891002cfc7458910004ff7358910024fe7358910024fc7358910254ff7258910006ef725891003eee525891003eee425891003eee325891024cff7158910006f7715891005ef6415891005ef6315891003ef7215891005eee215891005eec215891005ef421589100dcff7058910006fb70589100defa40589100defa305891003efb20589100deee20589100deec20589100def82058910004ff7654910004fe7654910004fd7654910004fc76549100067f65549100367c655491001eee6254910006ed6254910005f77154910015f4715491003fe72154910005fb705491000df8705491003feb205491019ff01054910004ff7650910004fe7650910004fd7650910004fc765091001eee6250910006ed6250910005f77150910015f4715091003fe72150910005fb705091000df8705091003feb205091017ff01050910004ff764c910004fe764c910004fd764c910004fc764c91001eee624c910006ed624c910005f7714c910015f4714c91003fe7214c910005fb704c91000df8704c91003feb204c91015ff0104c91000df47654510036f4765451000cf47654510015f77554510017777554510007776554510036f66554510036f46554510057746554510005f77454510057775454510007755454510005f7735451005777535451000775535451003df6725451003df47254510007f3705451000df6705451000df4705451013ff0705451000df07054510016f76054510017f3605451013ff2505451013ff2405451013ff
  | 2 => 0x2cfea214c120087e8214c120034fe76d95100567e65d95102b7f010d951013cfd75d951002cfe74d9510004fd74d951002cfc74d95100067e54d95100567c54d9510024fe73d9510004fd73d9510024fc73d95100067e53d95100567c53d951001cfe72d9510004fd72d951001cfc72d95100567f52d951000cff71d9510014fe71d951000cfd71d9510014fc71d95102c67f51d95102c67d51d9510014ff70d951000cfe70d9510014fd70d951000cfc70d95102b67f50d95102b67d50d9510034ff76595100567c65595102adf771595102bdfb705951013ff010595102b4ff75595100067f7559510004ff745951002cfe745951002cfc74595100567f5459510004ff7359510024fe7359510024fc73595100567f5359510004ff725951001cfe725951001cfc72595102acff7159510006f7715951013cff7059510006fb705951002cfe76d911004ebe64d9110297f010d9110034fe75d9110004fd75d9110034fc75d911011cfd74d9110024fe73d9110004fd73d9110024fc73d911001cfe72d9110004fd72d911001cfc72d911000cff71d9110014fe71d911000cfd71d9110014fc71d91102a6bf41d91102a6bd41d9110014ff70d911000cfe70d9110014fd70d911000cfc70d9110296bf40d9110296bd40d911002cff76591100057f75591100557c755911004ebc645911028df7715911029dfb705911011ff01059110004ff75591100067f75591100047f7559110034fe7559110034fc75591100067c75591100347c7559110294ff7459110006bf745911004ebe5459110004ff7359110024fe7359110024fc735911004ebf4359110004ff725911001cfe725911001cfc725911028cff7159110006f7715911011cff7059110006fb7059110004ff7655110004fe7655110004fd7655110004fc76551100367e65551100067d655511002ebe6455110006bd6455110015f6715511000dfa70551101fff01055110024fe76d8d10046de63d8d10277f010d8d10034fe75d8d10004fd75d8d10034fc75d8d1002cfe74d8d10004fd74d8d1002cfc74d8d100fcfd73d8d1001cfe72d8d10004fd72d8d1001cfc72d8d1000cff71d8d10014fe71d8d1000cfd71d8d10014fc71d8d10286df31d8d10286dd31d8d10014ff70d8d1000cfe70d8d10014fd70d8d1000cfc70d8d10276df30d8d10276dd30d8d10024ff7658d100057f7558d100557c7558d10046dc6358d1026df77158d1027dfb7058d100fff01058d10004ff7558d100067f7558d100047f7558d10034fe7558d10034fc7558d100067c7558d100347c7558d10004ff7458d1002cfe7458d1002cfc7458d10274ff7358d10006df7358d10046de5358d10046de4358d10004ff7258d1001cfe7258d1001cfc7258d1026cff7158d10006f77158d100fcff7058d10006fb705
  | 3 => 0xb605492019fea405492019fea305492000dec765092002eec765092000cec7650920005ef7550920005ed755092001def745092001faf7450920007af645092002eee645092002eec645092006fac6450920005ef735092006faf4350920007ad435092005dee715092005dec7150920007eb705092000dee705092000dec705092017fe8705092001eef605092001feb605092017fea405092017fea305092000dec764c920026ec764c92000cec764c920005ef754c920005ed754c920005ef744c920005ed744c92001def734c92001fcf734c920007cf634c920026ee634c920026ec634c920067cc634c920067ce434c920007cd434c92005dee714c92005dec714c920007eb704c92000dee704c92000dec704c92015fe8704c92001eef604c92001feb604c92015fea404c92015fea304c920014fe76d852001dee72d852000ded72d852005ef661d852005fe621d8520034fe75d8520004fd75d8520034fc75d852002cfe74d8520004fd74d852002cfc74d8520024fe73d8520004fd73d8520024fc73d852000cfd72d852024eed72d852000ced72d8520014fc72d85202e6ee52d8520006ed52d85202e6ee42d8520006ed42d85202e6ee32d8520006ed32d852005eee21d852005ef621d85202e6f521d852005eec21d852000cfe70d852001cfd70d852000cfc70d852024efa40d852024efa30d85202e6fb20d852024eee20d852024eec20d852024ef820d852024ef710d852005ef4615852005fe421585202ddfb7058520004ff7654520004fe7654520004fc7654520005ef725452001dec7254520005fb705452000df87054520004ff7650520004fe7650520004fc7650520005ef725052001dec7250520016f6615052005fe62150520004ff764c520004fe764c520004fc764c520005ef724c52001dec724c520016f6614c52005fe6214c52001df8765012002ef8765012001cf8765012000dfb745012000fbb7450120007bb645012002efa645012002ef8645012006fb8645012006fba5450120007b95450120005fb735012006fbb4350120007b94350120007eb725012001dfa725012001df872501200a7e8725012000efb625012000feb62501200a7ea5250120007e952501200a7ea425012006fe942501200a7ea3250120007e93250120006fb61501202d7ea21501200a7e8215012001df8764c120026f8764c12001cf8764c120005fb744c120005f9744c12000dfb734c12000fdb734c120007db634c120026fa634c120026f8634c120067d8634c120067da534c120007d9534c120067da434c120007d9434c120007eb724c12001dfa724c12001df8724c120087e8724c12000efb624c12000feb624c120087ea524c120007e9524c120087ea424c120007e9424c120087ea324c120067e9324c120006fb614c120
  | 4 => 0x952002cfc74d9520024fe73d9520004fd73d9520024fc73d952000cff72d952001cfe72d952000cfd72d952001cfc72d95203467f52d95203467d52d9520014fe71d9520004fd71d9520014fc71d952001cff70d952001cfd70d95203367f50d95203367d50d9520034ff76595200767c655952032def725952033dfb7059520334ff75595200067f7559520004ff745952002cfe745952002cfc74595200767f5459520004ff7359520024fe7359520024fc73595200767f535952032cff7259520006ef7259520004ff7159520014fe7159520014fc715952019cff7059520006fb705952002cfe76d912006ebe64d9120034fe75d9120004fd75d9120034fc75d912017cfd74d9120024fe73d9120004fd73d9120024fc73d912000cff72d912001cfe72d912000cfd72d912001cfc72d9120326bf42d9120326bd42d9120014fe71d9120004fd71d9120014fc71d912001cff70d912001cfd70d9120316bf40d9120316bd40d912002cff765912006ebc645912030def725912031dfb7059120004ff7559120034fe7559120034fc7559120314ff7459120006bf7459120004ff7359120024fe7359120024fc735912006ebf435912030cff7259120006ef7259120004ff7159120014fe7159120014fc715912017cff7059120006fb7059120004ff7655120004fe7655120004fd7655120004fc76551200367e65551200067d655512001dee7255120024fe76d8d20066de63d8d20034fe75d8d20004fd75d8d20034fc75d8d2002cfe74d8d20004fd74d8d2002cfc74d8d2015cfd73d8d2000cff72d8d2001cfe72d8d2000cfd72d8d2001cfc72d8d20306df32d8d20306dd32d8d20014fe71d8d20004fd71d8d20014fc71d8d2001cff70d8d2001cfd70d8d202f6df30d8d202f6dd30d8d20024ff7658d20066dc6358d202edef7258d202fdfb7058d20004ff7558d20034fe7558d20034fc7558d20004ff7458d2002cfe7458d2002cfc7458d202f4ff7358d20006df7358d20066de4358d202ecff7258d20006ef7258d20004ff7158d20014fe7158d20014fc7158d2015cff7058d20006fb7058d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200367e6554d200067d6554d2001dee7254d20004ff7650d20004fe7650d20004fd7650d20004fc7650d2002ebe6450d20006bd6450d20026de6350d20006dd6350d200679c4350d2001dee7250d2000dfa7050d2000dec7654920036ec765492000cec765492001def755492001f6f75549200076f6554920036ee6554920036ec65549200776c6554920005ef74549200776f54549200076d5454920005ef73549200776f53549200076d535492005dee715492005dec7154920007eb705492000dee705492000dec705492019fe8705492000de8705492001eef605492001fe
  | 5 => 0x14fc71d9130024ff70d9130024fd70d9130386bf40d9130386bd40d9130386fa20d9130386fa10d913002cff765913008ebc645913037ddf7359130005ef7259130085ec725913038dfb7059130004ff7559130034fe7559130034fc7559130384ff7459130006bf745913037cff7359130006df7359130004ff7259130006ef7259130004ef725913001cfe725913001cfc7259130006ec725913001cec7259130004ff7159130014fe7159130014fc71591301bcff7059130006fb70591301befa20591301befa1059130004ff7655130004fe7655130004fd7655130004fc76551300067f65551300367c6555130025de73551302175e535513000ddc7654d30036dc7654d3000cdc7654d30025df7554d300275f7554d300075f6554d30036de6554d30036dc6554d300975c6554d30005df7454d303775e5454d300975c5454d300975f5254d300975f5154d30007db7054d3000dde7054d3000ddc7054d301dfd87054d30026df6054d30027db6054d301df5f5054d301df5d5054d301dfda2054d301dfda1054d3000ddc7650d3002edc7650d3000cdc7650d30005df7550d30005dd7550d301d6de6550d301d6dc6550d30025df7450d300279f7450d300079f6450d3002ede6450d3002edc6450d3008f9c6450d3002e9c6450d3036f9f5450d3008f9c5450d3008f9f4250d3008f9f4150d30007db7050d3000dde7050d3000ddc7050d301bfd87050d30026df6050d30027db6050d301bf9f4050d301bf9d4050d301bfda2050d301bfda1050d3001cfe76d8930086ee62d8930034fe75d8930004fd75d8930034fc75d893002cfe74d8930004fd74d893002cfc74d893000cfd73d893001cfc73d8930366de43d8930006dd43d8930006ef42d8930086ec42d8930086ee32d8930366ed32d8930014fe71d8930004fd71d8930014fc71d8930086ef21d8930024fd70d89302eeef20d8930086ec625893035dfb7058930004ff7654930004fe7654930004fc76549300075d5354930004ff7650930004fe7650930004fc76509300079d4350930014fe76d853007ef661d8530034fe75d8530004fd75d8530034fc75d853002cfe74d8530004fd74d853002cfc74d853000cfd73d8530014fc73d8530356de53d8530006dd53d8530356de43d8530006dd43d853001cfe72d8530004fd72d853001cfc72d853007ef631d8530356f531d8530024fd70d853026ef710d85300057f75585300957c755853007ef4615853034dfb7058530004ff7654530004fe7654530004fc76545300075d5354530004ff7650530004fe7650530004fc76505300079d4350530004ff7648530004fe7648530004fc7648530006ef624853001eec624853000dfa70485300dfea2048530034fe76d95200767e65d952019cfd75d952002cfe74d9520004fd74d
  | 6 => 0xc7258d403e5fb7058d40004ff7654d40004fe7654d40004fc7654d400067f6554d400367c6554d4002dbe7454d401f73e5454d4000dbc7650d40026bc7650d4000cbc7650d40005bf7550d40005bd7550d401d6be6550d401d6bc6550d4002dbf7350d4002f9f7350d400079f6350d40026be6350d40026bc6350d400af9c6350d400269c6350d403df9f5350d400af9c5350d400af9f3250d400af9f3150d40007bb7050d4000dbe7050d4000dbc7050d401bfb87050d4002ebf6050d4002fbb6050d401bf9f3050d401bfba2050d401bfba1050d4001cfe76d89400a6ee62d8940034fe75d8940004fd75d8940034fc75d894000cfd74d894001cfc74d8940024fe73d8940004fd73d8940024fc73d89403d6bf43d8940006bd43d89400a6ee42d89403d6ed42d8940006ef32d89400a6ec32d8940014fe71d8940004fd71d8940014fc71d89400a6ef21d894002cfd70d894030eef20d89400a6ec62589403cdfb7058940004ff7654940004fe7654940004fc76549400073d5454940004ff764c940004fe764c940004fc764c9400079d434c940014fe76d854009ef661d8540034fe75d8540004fd75d8540034fc75d854000cfd74d8540014fc74d85403c6be54d8540006bd54d8540024fe73d8540004fd73d8540024fc73d85403c6bf43d8540006bd43d854001cfe72d8540004fd72d854001cfc72d854009ef641d85403c6f541d854002cfd70d854028ef710d85400057f75585400b57c755854009ef461585403bdfb7058540004ff7654540004fe7654540004fc76545400073d5454540004ff764c540004fe764c540004fc764c5400079d434c540004ff7648540004fe7648540004fc7648540006ef624854001eec624854000dfa70485400dfea2048540034fe76d95300967e65d95301dcfd75d953002cfe74d9530004fd74d953002cfc74d95300967f54d953000cff73d9530024fe73d953000cfd73d9530024fc73d95303b67f53d95303b67d53d953001cfe72d9530004fd72d953001cfc72d9530014fe71d9530004fd71d9530014fc71d95300067e51d95300967c51d9530024ff70d9530024fd70d95303a67f50d95303a67d50d95303a6fa10d9530034ff76595300967c655953039ddf73595303adfb70595303a4ff75595300067f7559530004ff745953002cfe745953002cfc745953039cff7359530006df7359530004ff725953001cfe725953001cfc7259530004ff7159530014fe7159530014fc71595301dcff7059530006fb70595301defa105953002cfe76d913008ebe64d9130034fe75d9130004fd75d9130034fc75d91301bcfd74d913000cff73d9130024fe73d913000cfd73d9130024fc73d9130396bf43d9130396bd43d913001cfe72d9130004fd72d913001cfc72d9130014fe71d9130004fd71d9130
  | 7 => 0xd50004fc7650d500357e7550d500057d7550d50006bf6450d5002ebc6450d501d73f5450d50006df6350d50026dc6350d501d75f5350d500cf9c4350d5001cfe76d89500c6ee62d895000cfd75d895001cfc75d895002cfe74d8950004fd74d895002cfc74d89504367f54d89500067d54d8950024fe73d8950004fd73d8950024fc73d89504367f53d89500067d53d89500c6ee52d8950436ed52d8950014fe71d8950004fd71d8950014fc71d89500c6ef21d8950034fd70d895032eef20d89500c6ec625895042dfb7058950004ff7650950004fe7650950004fc7650950004ff764c950004fe764c950004fc764c950014fe76d85500bef661d855000cfd75d8550014fc75d855002cfe74d8550004fd74d855002cfc74d85504267f54d85500067d54d8550024fe73d8550004fd73d8550024fc73d85504267f53d85500067d53d855001cfe72d8550004fd72d855001cfc72d85500bef651d8550426f551d85500bef621d8550034fd70d85502aef710d85500bef4615855041dfb7058550004ff7650550004fe7650550004fc76505500073d5450550004ff764c550004fe764c550004fc764c5500075d534c550004ff7648550004fe7648550004fc7648550006ef624855001eec6248550006f76148550016f46148550034fe76d95400b67e65d95401fcfd75d954000cff74d954002cfe74d954000cfd74d954002cfc74d95404167f54d95404167d54d9540024fe73d9540004fd73d9540024fc73d95400b67f53d954001cfe72d9540004fd72d954001cfc72d9540014fe71d9540004fd71d9540014fc71d95400067e51d95400b67c51d954002cff70d954002cfd70d95404067f50d95404067d50d9540406fa10d9540034ff76595400b67c65595403fdbf745954040dfb7059540404ff75595400067f75595403fcff7459540006bf7459540004ff7359540024fe7359540024fc7359540004ff725954001cfe725954001cfc7259540004ff7159540014fe7159540014fc71595401fcff7059540006fb70595401fefa105954000dbc7655140036bc765514000cbc765514002dbf755514002f3f75551400073f6555140036be6555140036bc65551400b73c6555140005bf73551403f73e53551400b73c53551400b73f52551400b73f5155140007bb705514000dbe705514000dbc70551401ffb8705514002ebf605514002fbb60551401ff3f50551401ff3d50551401ffba20551401ffba1055140024fe76d8d400aede63d8d40034fe75d8d40004fd75d8d40034fc75d8d4000cfd74d8d40024fc74d8d400aede43d8d403eedd43d8d4001cfe72d8d40004fd72d8d4001cfc72d8d40014fe71d8d40004fd71d8d40014fc71d8d4002cfd70d8d4037edf30d8d4037efa20d8d4037efa10d8d400aedc6358d40005ef7258d400a5e
  | 8 => 0xefb74350521007b54350521007e7725052101df6725052101df47250521127e47250521016f76250521017e76250521127e65250521007e55250521127e642505210efe54250521127e63250521007e53250521467e62050521127e4205052101df4764c521026f4764c52101cf4764c521005f7744c521005f5744c521015f7734c521017d7734c521007d7634c521026f6634c521026f4634c5210e7d4634c5210e7d6534c521007d5534c5210e7d6434c521007d5434c521007e7724c52101df6724c52101df4724c521107e4724c521016f7624c521017e7624c521107e6524c521007e5524c521107e6424c521007e5424c521107e6324c5210e7e5324c52145fe6204c521107e4204c52100cfe76d812101dee72d8121015ed72d81210defa60d81210dfea20d8121034fe75d8121004fd75d8121034fc75d812102cfe74d8121004fd74d812102cfc74d8121024fe73d8121004fd73d8121024fc73d8121014fd72d81210deed72d8121014ed72d812100cfc72d81212deee52d8121006ed52d81212deee42d8121006ed42d81212deee32d8121006ed32d812101cfd71d812100cfc71d812125ef641d8121006f541d812125ef631d8121006f531d81212def721d812125eee21d812125eec21d812125ef421d81210deee20d81210defa20d81210deec20d81210defa10d81210def860581210dfe8205812102cfe76d91500d6be64d915000cfd75d915002cfc75d91500d6be54d9150456bd54d9150024fe73d9150004fd73d9150024fc73d91500d6bf43d915001cfe72d9150004fd72d915001cfc72d9150014fe71d9150004fd71d9150014fc71d9150034fd70d91503febf40d91503fefa10d91500d6bc645915044dfb705915000d7c765515002e7c765515000c7c76551500357f74551500373f74551500073f645515002e7e645515002e7c64551500d73c64551500057f73551502167e63551502167c63551500d73f41551500077b705515000d7e705515000d7c70551501ff7870551500367f60551500377b60551501ff3f40551501ff7a1055150024fe76d8d500cede63d8d5000cfd75d8d50024fc75d8d5002cfe74d8d50004fd74d8d5002cfc74d8d500cede53d8d50446dd53d8d500cede43d8d5001cfe72d8d50004fd72d8d5001cfc72d8d50014fe71d8d50004fd71d8d50014fc71d8d50034fd70d8d5039edf30d8d5039efa10d8d500cedc6358d5043dfb7058d5000d7c7654d500267c7654d5000c7c7654d500057f7454d501f67e6454d501f67c6454d500357f7354d500375f7354d500075f6354d500267e6354d500267c6354d500cf5c6354d500cf5f3154d500077b7054d5000d7e7054d5000d7c7054d501df787054d500367f6054d500377b6054d501df5f3054d501df7a1054d50004ff7650d50004fe765
  | 9 => 0xc645912148def725912149df77159121004ff7559121034fe7559121034fc7559121494ff7459121006bf7459121004ff7359121024fe7359121024fc73591210eebf435912148cff7259121006ef7259121184ff7159121006f77159121004ff705912100cfe705912100cfc7059121004ff7655121004fe7655121004fd7655121004fc76551210367e65551210067d655512101dee7255121024fe76d8d210e6de63d8d21034fe75d8d21004fd75d8d21034fc75d8d2102cfe74d8d21004fd74d8d2102cfc74d8d21164fd73d8d21014ff72d8d21014fd72d8d21486df32d8d21486dd32d8d2101cff71d8d2101cfd71d8d21476df31d8d21476dd31d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21024ff7658d210e6dc6358d2146def7258d2147df77158d21004ff7558d21034fe7558d21034fc7558d21004ff7458d2102cfe7458d2102cfc7458d21474ff7358d21006df7358d210e6de4358d2146cff7258d21006ef7258d21164ff7158d21006f77158d21004ff7058d2100cfe7058d2100cfc7058d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210367e6554d210067d6554d2101dee7254d21004ff7650d21004fe7650d21004fd7650d21004fc7650d2102ebe6450d21006bd6450d21026de6350d21006dd6350d210e79c4350d2101dee7250d21015f67150d21015ec7654921036ec7654921014ec765492101def755492101f6f75549210076f6554921036ee6554921036ec65549210f76c6554921005ef74549210f76f54549210076d5454921005ef73549210f76f53549210076d5354921007e77154921015ee7154921015ec71549211a7e47154921015e4715492101eef615492101fe761549211a7e641549211a7e631549210ddee70549210ddec7054921015ec765092102eec7650921014ec7650921005ef7550921005ed755092101def745092101faf7450921007af645092102eee645092102eec64509210efac6450921005ef73509210efaf4350921007ad4350921007e77150921015ee7150921015ec7150921187e4715092101eef615092101fe76150921187e64150921187e631509210ddee70509210ddec7050921015ec764c921026ec764c921014ec764c921005ef754c921005ed754c921005ef744c921005ed744c92101def734c92101fcf734c921007cf634c921026ee634c921026ec634c9210e7cc634c9210e7ce434c921007cd434c921007e7714c921015ee714c921015ec714c921167e4714c92101eef614c92101fe7614c921167e6414c921167e6314c9210ddee704c9210ddec704c92101df4765052102ef4765052101cf47650521015f77450521017b77450521007b7645052102ef6645052102ef464505210efb464505210efb65450521007b55450521005f77350521
  | 10 => 0x5131025de73551312175e5355131015dc7654d31036dc7654d31014dc7654d31025df7554d310275f7554d310075f6554d31036de6554d31036dc6554d311175c6554d31005df7454d314e75e5454d311175c5454d311175f5254d31007d77154d31015de7154d31015dc7154d311e7d47154d31026df6154d31027d76154d311e75f5154d311e75d5154d311e7d62154d311175f5054d311e7d71054d31015dc7650d3102edc7650d31014dc7650d31005df7550d31005dd7550d311d6de6550d311d6dc6550d31025df7450d310279f7450d310079f6450d3102ede6450d3102edc6450d3110f9c6450d3102e9c6450d314df9f5450d3110f9c5450d3110f9f4250d31007d77150d31015de7150d31015dc7150d311c7d47150d31026df6150d31027d76150d311c79f4150d311c79d4150d311c7d62150d3110f9f4050d311c7d71050d3101cfe76d8931106ee62d8931034fe75d8931004fd75d8931034fc75d893102cfe74d8931004fd74d893102cfc74d8931014fd73d89314d6de43d8931006dd43d8931006ef42d8931106ec42d8931106ee32d89314d6ed32d8931024fd71d893146eef21d893100cfe70d8931004fd70d893100cfc70d8931106ef20d8931106ec62589314cdf77158931004ff7654931004fe7654931004fc76549310075d5354931004ff7650931004fe7650931004fc76509310079d435093100cfe76d81310fefa60d8131034fe75d8131004fd75d8131034fc75d813102cfe74d8131004fd74d813102cfc74d8131014fd73d813100cfc73d813134ede53d8131006dd53d813134ede43d8131006dd43d813101cfe72d8131004fd72d813101cfc72d8131024fd71d81310fefa30d81310fefa10d81310057f75581311157c75581310fef86058131034fe76d95210f67e65d95211a4fd75d952102cfe74d9521004fd74d952102cfc74d9521024fe73d9521004fd73d9521024fc73d9521014ff72d9521014fd72d95214c67f52d95214c67d52d952101cff71d952101cfd71d95214b67f51d95214b67d51d952100cfe70d9521004fd70d952100cfc70d9521034ff76595210f67c65595214adef72595214bdf771595214b4ff75595210067f7559521004ff745952102cfe745952102cfc74595210f67f5459521004ff7359521024fe7359521024fc73595210f67f53595214acff7259521006ef72595211a4ff7159521006f77159521004ff705952100cfe705952100cfc705952102cfe76d91210eebe64d9121034fe75d9121004fd75d9121034fc75d9121184fd74d9121024fe73d9121004fd73d9121024fc73d9121014ff72d9121014fd72d91214a6bf42d91214a6bd42d912101cff71d912101cfd71d9121496bf41d9121496bd41d912100cfe70d9121004fd70d912100cfc70d912102cff76591210eeb
  | 11 => 0x79f6350d41026be6350d41026bc6350d4112f9c6350d410269c6350d4153f9f5350d4112f9c5350d4112f9f3250d41007b77150d41015be7150d41015bc7150d411c7b47150d4102ebf6150d4102fb76150d411c79f3150d411c7b62150d4112f9f3050d411c7b71050d4101cfe76d8941126ee62d8941034fe75d8941004fd75d8941034fc75d8941014fd74d8941024fe73d8941004fd73d8941024fc73d8941536bf43d8941006bd43d8941126ee42d8941536ed42d8941006ef32d8941126ec32d894102cfd71d894148eef21d894100cfe70d8941004fd70d894100cfc70d8941126ef20d8941126ec625894152df77158941004ff7654941004fe7654941004fc76549410073d5454941004ff764c941004fe764c941004fc764c9410079d434c94100cfe76d814111efa60d8141034fe75d8141004fd75d8141034fc75d8141014fd74d814100cfc74d81413bebe54d8141006bd54d8141024fe73d8141004fd73d8141024fc73d81413bebf43d8141006bd43d814101cfe72d8141004fd72d814101cfc72d814102cfd71d814111efa40d814111efa10d81410057f75581411357c755814111ef86058141034fe76d95311167e65d95311e4fd75d953102cfe74d9531004fd74d953102cfc74d95311167f54d9531014ff73d9531014fd73d95315267f53d95315267d53d953101cfe72d9531004fd72d953101cfc72d9531024ff71d9531024fd71d95315167f51d95315167d51d953100cfe70d9531004fd70d953100cfc70d95310067e50d95311167c50d9531516f710d9531034ff76595311167c655953150ddf735953151df77159531514ff75595310067f7559531004ff745953102cfe745953102cfc745953150cff7359531006df7359531004ff725953101cfe725953101cfc72595311e4ff7159531006f77159531004ff705953100cfe705953100cfc70595311e6f7105953102cfe76d913110ebe64d9131034fe75d9131004fd75d9131034fc75d91311c4fd74d9131014ff73d9131014fd73d9131506bf43d9131506bd43d913101cfe72d9131004fd72d913101cfc72d9131024ff71d9131024fd71d91314f6bf41d91314f6bd41d91314f6f621d913100cfe70d9131004fd70d913100cfc70d91314f6f710d913102cff765913110ebc64591314eddf7359131005ef7259131105ec72591314fdf77159131004ff7559131034fe7559131034fc75591314f4ff7459131006bf74591314ecff7359131006df7359131004ff7259131006ef7259131004ef725913101cfe725913101cfc7259131006ec725913101cec72591311c4ff7159131006f771591311c6f62159131004ff705913100cfe705913100cfc70591311c6f71059131004ff7655131004fe7655131004fd7655131004fc76551310067f65551310367c655
  | 12 => 0xf3054d511e7771054d51004ff7650d51004fe7650d51004fc7650d510357e7550d510057d7550d51006bf6450d5102ebc6450d511d73f5450d51006df6350d51026dc6350d511d75f5350d5114f9c4350d5101cfe76d8951146ee62d8951014fd75d895102cfe74d8951004fd74d895102cfc74d89515867f54d89510067d54d8951024fe73d8951004fd73d8951024fc73d89515867f53d89510067d53d8951146ee52d8951586ed52d8951034fd71d89514aeef21d895100cfe70d8951004fd70d895100cfc70d8951146ef20d8951146ec625895157df77158951004ff7650951004fe7650951004fc7650951004ff764c951004fe764c951004fc764c95100cfe76d815113efa60d8151014fd75d815100cfc75d815102cfe74d8151004fd74d815102cfc74d815141e7f54d81510067d54d8151024fe73d8151004fd73d8151024fc73d815141e7f53d81510067d53d815101cfe72d8151004fd72d815101cfc72d8151034fd71d815113efa50d815113efa20d815113efa10d815113ef86058151034fe76d95411367e65d9541204fd75d9541014ff74d9541014fd74d95415767f54d95415767d54d9541024fe73d9541004fd73d9541024fc73d95411367f53d954101cfe72d9541004fd72d954101cfc72d954102cff71d954102cfd71d95415667f51d95415667d51d954100cfe70d9541004fd70d954100cfc70d95410067e50d95411367c50d9541566f710d9541034ff76595411367c655954155dbf745954156df77159541564ff75595410067f755954155cff7459541006bf7459541004ff7359541024fe7359541024fc7359541004ff725954101cfe725954101cfc7259541204ff7159541006f77159541004ff705954100cfe705954100cfc7059541206f71059541015bc7655141036bc7655141014bc765514102dbf755514102f3f75551410073f6555141036be6555141036bc65551411373c6555141005bf73551415573e53551411373c53551411373f5255141007b77155141015be7155141015bc7155141207b4715514102ebf615514102fb761551412073f51551412073d5155141207b621551411373f5055141207b71055141024fe76d8d4112ede63d8d41034fe75d8d41004fd75d8d41034fc75d8d41014fd74d8d4112ede43d8d4154edd43d8d4101cfe72d8d41004fd72d8d4101cfc72d8d4102cfd71d8d414eedf31d8d414eef621d8d4100cfe70d8d41004fd70d8d4100cfc70d8d414eef710d8d4112edc6358d41005ef7258d41125ec7258d41545f77158d41004ff7654d41004fe7654d41004fc7654d410067f6554d410367c6554d4102dbe7454d411f73e5454d41015bc7650d41026bc7650d41014bc7650d41005bf7550d41005bd7550d411d6be6550d411d6bc6550d4102dbf7350d4102f9f7350d41
  | 13 => 0x91325c5ef7259132004ff7559132034fe7559132034fc75591325bcff7459132006bf74591325b4ff7359132006df73591321ccff7259132006ef7259132004ff7159132014fe7159132014fc71591321ceef2159132004ff705913200cfe705913200cfc70591321ceef2059132004ff7655132004fe7655132004fd7655132004fc76551320067f65551320367c6555132006bf645513202ebc645513201ddc7650d3202edc7650d3201cdc7650d321d6de6550d321d6dc6550d32025df7450d320279f7450d320079f6450d3202ede6450d3202edc6450d3216f9c6450d3202e9c6450d325af9f5450d3216f9c5450d32007cf7250d3201dde7250d3201ddc7250d321cfcc7250d32026df6250d32027cf6250d321cf9f4250d321cf9d4250d3216f9f4150d321cfcf2150d3216f9f4050d321cfcf2050d32014fe76d8532166f661d8532034fe75d8532004fd75d8532034fc75d853202cfe74d8532004fd74d853202cfc74d853201cfd73d85324cede43d8532006dd43d8532024fd72d8532166f631d8532166f621d853200cfe70d8532004fd70d853200cfc70d8532166f710d8532166f4615853200cfe76d813215efa60d8132034fe75d8132004fd75d8132034fc75d813202cfe74d8132004fd74d813202cfc74d813201cfd73d813235ede43d8132006dd43d8132024fd72d8132014fe71d8132004fd71d8132014fc71d813215efa30d813215efa20d813215efa10d813215ef8605813202cfe76d9151156be64d9151014fd75d9151156be54d91515a6bd54d9151024fe73d9151004fd73d9151024fc73d9151156bf43d915101cfe72d9151004fd72d915101cfc72d9151034fd71d915155ebf41d915100cfe70d9151004fd70d915100cfc70d915155ef710d9151156bc645915159df771591510157c765515102e7c76551510147c76551510357f74551510373f74551510073f645515102e7e645515102e7c64551511573c64551510057f73551512167e63551512167c63551510077771551510157e71551510157c71551512077471551510367f61551510377761551512073f41551511573f4055151207771055151024fe76d8d5114ede63d8d51014fd75d8d5102cfe74d8d51004fd74d8d5102cfc74d8d5114ede53d8d51596dd53d8d5114ede43d8d5101cfe72d8d51004fd72d8d5101cfc72d8d51034fd71d8d5150edf31d8d5100cfe70d8d51004fd70d8d5100cfc70d8d5150ef710d8d5114edc6358d5158df77158d510157c7654d510267c7654d510147c7654d510057f7454d511f67e6454d511f67c6454d510357f7354d510375f7354d510075f6354d510267e6354d510267c6354d5114f5c6354d51007777154d510157e7154d510157c7154d511e7747154d510367f6154d51037776154d511e75f3154d5114f5
  | 14 => 0x20cff7259542006ef7259542004ff7159542014fe7159542014fc715954220eef2159542004ff705954200cfe705954200cfc705954220eef2059542024fe76d8d4218ede63d8d42034fe75d8d42004fd75d8d42034fc75d8d4201cfd74d8d4218ede53d8d4218ede43d8d42606dd43d8d4202cfd72d8d425b6df32d8d42014fe71d8d42004fd71d8d42014fc71d8d425b6ef21d8d4200cfe70d8d42004fd70d8d4200cfc70d8d425b6ef20d8d4218edc6358d425fdef7258d42004ff7654d42004fe7654d42004fc7654d420067f6554d420367c6554d42006df6354d42026dc6354d4201dbc7650d42026bc7650d4201cbc7650d421d6be6550d421d6bc6550d4202dbf7350d4202f9f7350d420079f6350d42026be6350d42026bc6350d4218f9c6350d420269c6350d425f79f5350d4218f9c5350d42007af7250d4201dbe7250d4201dbc7250d421cfac7250d4202ebf6250d4202faf6250d421cf9f3250d4218f9f3150d421cfaf2150d4218f9f3050d421cfaf2050d42014fe76d8542186f661d8542034fe75d8542004fd75d8542034fc75d854201cfd74d8542024fe73d8542004fd73d8542024fc73d854252ebf43d8542006bd43d854202cfd72d8542186f641d8542186f621d854200cfe70d8542004fd70d854200cfc70d8542186f710d8542186f4615854200cfe76d814217efa60d8142034fe75d8142004fd75d8142034fc75d814201cfd74d8142024fe73d8142004fd73d8142024fc73d81423cebf43d8142006bd43d814202cfd72d8142014fe71d8142004fd71d8142014fc71d814217efa40d814217efa20d814217efa10d814217ef86058142034fe76d95321767e65d95321ecfd75d953202cfe74d9532004fd74d953202cfc74d95321767f54d953201cff73d953201cfd73d95325ee7f53d95325ee7d53d9532024ff72d9532024fd72d95325de7f52d95325de7d52d9532014fe71d9532004fd71d9532014fc71d95325deef21d953200cfe70d9532004fd70d953200cfc70d95325deef20d9532034ff76595321767c65595325d5df73595325e5ef72595325dcff75595320067f7559532004ff745953202cfe745953202cfc74595325d4ff7359532006df73595321ecff7259532006ef7259532004ff7159532014fe7159532014fc71595321eeef2159532004ff705953200cfe705953200cfc70595321eeef205953202cfe76d913216ebe64d9132034fe75d9132004fd75d9132034fc75d91321ccfd74d913216ebe54d913201cff73d913201cfd73d91325cebf43d91325cebd43d9132024ff72d9132024fd72d91325bebf42d91325bebd42d9132014fe71d9132004fd71d9132014fc71d91325beef21d913200cfe70d9132004fd70d913200cfc70d91325beef20d913202cff765913216ebc64591325b5df735
  | 15 => 0xc73d91521b6bf43d9152034fd72d915260ebf42d9152014fe71d9152004fd71d9152014fc71d915260eef21d915200cfe70d9152004fd70d915200cfc70d915260eef20d91521b6bc645915263def725915201d7c765515202e7c765515201c7c76551520357f74551520373f74551520073f645515202e7e645515202e7c64551521b73c645515202e3c64551520057f73551522167e63551522167c63551520076f725515201d7e725515201d7c725515220f6c72551520367f62551520376f62551521b73f415515220f6f21551521b73f405515220f6f2055152024fe76d8d521aede63d8d5201cfd75d8d5202cfe74d8d52004fd74d8d5202cfc74d8d521aede53d8d52636dd53d8d521aede43d8d52034fd72d8d525d6df32d8d52014fe71d8d52004fd71d8d52014fc71d8d525d6ef21d8d5200cfe70d8d52004fd70d8d5200cfc70d8d525d6ef20d8d521aedc6358d5262def7258d5201d7c7654d520267c7654d5201c7c7654d520057f7454d521f67e6454d521f67c6454d520357f7354d520375f7354d520075f6354d520267e6354d520267c6354d521af5c6354d520265c6354d520076f7254d5201d7e7254d5201d7c7254d521ef6c7254d520367f6254d520376f6254d521af5f3154d521ef6f2154d521af5f3054d521ef6f2054d52004ff7650d52004fe7650d52004fc7650d520357e7550d520057d7550d52006bf6450d5202ebc6450d521d73f5450d52006df6350d52026dc6350d521d75f5350d521af9c4350d52005ef7250d5201dec7250d52014fe76d85521a6f661d855201cfd75d855202cfe74d8552004fd74d855202cfc74d855257e7f54d85520067d54d8552024fe73d8552004fd73d8552024fc73d855257e7f53d85520067d53d8552034fd72d85521a6f651d85521a6f621d855200cfe70d8552004fd70d855200cfc70d85521a6f710d85521a6f4615855200cfe76d815219efa60d815201cfd75d815202cfe74d8152004fd74d815202cfc74d815242e7f54d81520067d54d8152024fe73d8152004fd73d8152024fc73d815242e7f53d81520067d53d8152034fd72d8152014fe71d8152004fd71d8152014fc71d815219efa50d815219efa20d815219efa10d815219ef86058152034fe76d95421967e65d954220cfd75d954201cff74d954201cfd74d95426267f54d95426267d54d9542024fe73d9542004fd73d9542024fc73d95421967f53d954202cff72d954202cfd72d95426167f52d95426167d52d9542014fe71d9542004fd71d9542014fc71d9542616ef21d954200cfe70d9542004fd70d954200cfc70d9542616ef20d9542034ff76595421967c655954260dbf745954261def7259542614ff75595420067f755954260cff7459542006bf7459542004ff7359542024fe7359542024fc7359542
  | 16 => 0x855301cfc72d85531e6f651d85531e6f631d855300cfe70d8553004fd70d855300cfc70d85531e6f4615855300cfe76d81531defa60d8153024fd75d815302cfe74d8153004fd74d815302cfc74d8153034fd73d815301cfe72d8153004fd72d815301cfc72d8153014fe71d8153004fd71d8153014fc71d81531defa50d81531defa30d81531def86058153034fe76d95431d67e65d954302dbe74d9543025bd74d95431d73f54d9543025de73d954302ddd73d95431d75f53d95436579c43d9543214fd75d9543024ff74d9543024fd74d9543656bd74d9543024bd74d95436667f54d95431d6bf54d95431d63f54d95436667d54d9543666bc54d954302cff73d954302cfd73d9543666dd73d954302cdd73d95436567f53d95431d6df53d95436567d53d9543656dc53d954301cfe72d9543004fd72d954301cfc72d9543014fe71d9543004fd71d9543014fc71d9543666bf41d9543656df31d954300cfe70d9543004fd70d954300cfc70d9543666bf40d9543656df30d9543034ff76595431d67c655954364dbf74595431f73c545954365ddf73595432175c53595432179c4359543654ff75595430067f755954364cff7459543006bf74595431d6bf54595431f67e54595431f67c54595431f6bc5459543214ff7359543006df73595431d6df53595432167e53595432167c5359543216dc5359543004ff725954301cfe725954301cfc72595431d67f5259543004ff7159543014fe7159543014fc71595431d67f51595431f6bf4159543216df3159543004ff705954300cfe705954300cfc70595431d67f50595431f6bf4059543216df305954301cfe76d89435c79c43d89431ceee62d8943034fe75d8943004fd75d8943034fc75d8943024fd74d894302cfd73d89431ceee52d89431ceee42d89431ceee32d8943014fe71d8943004fd71d8943014fc71d8943006ee21d89431ceec21d894300cfe70d8943004fd70d894300cfc70d8943006ee20d89431ceec20d894318f9c43589431ceec6258943014fe76d85434ff9c43d85431c6f661d8543034fe75d8543004fd75d8543034fc75d8543024fd74d854302cfd73d854301cfe72d8543004fd72d854301cfc72d85431c6f641d85431c6f631d854300cfe70d8543004fd70d854300cfc70d854312f9c4358543005ef72585431cdec72585431c6f4615854300cfe76d814338f9c43d81431befa60d8143034fe75d8143004fd75d8143034fc75d8143024fd74d814302cfd73d814301cfe72d8143004fd72d814301cfc72d8143014fe71d8143004fd71d8143014fc71d81431befa40d81431befa30d81430af9c4358143005ef72581431cdec72581431bef8605814302cfe76d91521b6be64d915201cfd75d91521b6be54d9152646bd54d9152024fe73d9152004fd73d9152024f
  | 17 => 0x4010800008c43280201044708c6710405008001080018420494070000408401000a2000472004318025280014002110c63000031002608820000023002320c600800000824014001000000060000000040318420008a190000080010080008840004600002100002080071180100c0300c60314020040128420004002000100045030001080b014000000000841000001002200400018001000010cd038420024242002000522184053800008443024fe76d8d540357e75d8d5402d7d75d8d54216de63d8d542175e53d8d5402cfd75d8d542167d75d8d5402c7d75d8d54034fd74d8d5466ebf54d8d5465e7e54d8d5465e7c54d8d5465ebc54d8d542167e53d8d54216de53d8d542167c53d8d54216de43d8d5401cfe72d8d54004fd72d8d5401cfc72d8d5466e7f52d8d54014fe71d8d54004fd71d8d54014fc71d8d5466e7f51d8d5465ebf41d8d5400cfe70d8d54004fd70d8d5400cfc70d8d5466e7f50d8d5465ebf40d8d54216dc6358d542175c5358d5401cfe76d895420eee62d895402cfd75d8954034fd74d8954024fe73d8954004fd73d8954024fc73d895420eee52d895420eee42d8954014fe71d8954004fd71d8954014fc71d895400cfe70d8954004fd70d895400cfc70d895420eec6258954014fe76d8554206f661d855402cfd75d8554034fd74d8554024fe73d8554004fd73d8554024fc73d855401cfe72d8554004fd72d855401cfc72d8554206f651d8554206f641d855400cfe70d8554004fd70d855400cfc70d8554206f4615855400cfe76d81541fefa60d815402cfd75d8154034fd74d8154024fe73d8154004fd73d8154024fc73d815401cfe72d8154004fd72d815401cfc72d8154014fe71d8154004fd71d8154014fc71d81541fefa50d81541fefa40d81541fef8605815402cfe76d91530357e75d91530257d75d91531f6be64d91531f73e54d9153024fd75d915364e7d75d91530247d75d91531f67e54d91531f6be54d91531f63e54d9153676bd54d91531f67c54d9153034fd73d9153676df53d915364e7e53d915364e7c53d915364edc53d915364ebf43d915301cfe72d9153004fd72d915301cfc72d91536767f52d9153014fe71d9153004fd71d9153014fc71d91536767f51d915364edf31d915300cfe70d9153004fd70d915300cfc70d91536767f50d915364edf30d91531f6bc64591531f73c545915366ddf735915301cfe76d89531eeee62d8953024fd75d895302cfe74d8953004fd74d895302cfc74d8953034fd73d89531eeee52d89531eeee32d8953014fe71d8953004fd71d8953014fc71d895300cfe70d8953004fd70d895300cfc70d89531eeec6258953014fe76d85531e6f661d8553024fd75d855302cfe74d8553004fd74d855302cfc74d8553034fd73d855301cfe72d8553004fd72d
  | 18 => 0x1d253da00000000004f400000017184ee620537800100a46018a80014b608c000000111c4de35f2278a7a2e021c1d084660004cb9ef90be0000000000d9e28a0000fd14f60005980000000000000000000066951785380000000001e288de0003d00000000316000000000085d000012134a000000059535a0000000001548000000000002a62717a800000026c3e00670000b910000220eac9e85770e5c6020171ec163c31c1570a2a0046ba6db59880003b8b873c18000ec600032080001647180000000000000133acf172c0000000000afcaa8044829c00000000000000000001d111540000000000000ee00000001dfc85c0000000b4c000bc236a85b0e7e000000000000068e52321fc0001bf5880924d2c0000002cb11faad300026e4c2a9424788000000000000253000000000000016c40000001ab00009862d700000000004cd000000000048f13fcdae35f5b012e0000000000000000007d090000000000038480000005f100000000000000c380ec00000039c87b8000000000258504c1de0000048004000232800000000000025e4a6e7ee42780007740000000ea4000000000000000000000006f117000000000001344c6000000000000000000000008e00000000000000000290800056a0b21168b4aae73a1a4091783100000001206551000000000002400000003c600000002800001e8410a1200000000000000000b713748b393329f40000000f908a80002bccb700001dc00013fc27c0002c7911e05400000000000000b7102180201080001401004200804118001180c00840008440100000140010042100411204000942200020014001420004600804000007220201880340002382630800200001100440800000001004e0000200888118562100870042008c201806048001100800806020400004050800108c2200c0000040080201982108c001042008422300827080601023100a61040200c20214241002c0040808c0021001084001004000807000600900018021188410806108022080001cc0100000a8081080000900000022280835800210000288c00846210424084203840008480000042802040000108802086400000014c108001080c228003401a3080462802009c001004120481084210000218467000010812218003380011902000041108c01852001c00088c608c2108822400020844000820004211816001424180a000c4008020084674800d0804908460000c118000001000000500020280020000100401280040812414c80204e520501004000004138c840900208080080010192218800104e02800018405008015080000ca1110431000200420180204002210062300c5000c0284a008806188010040400427088000202808c02080200004008422000620000000400188000044000
  | 19 => 0x3d70cb40001c6000000171e00000012f479c14c00021d00000000000000fa01dd00500015aa00005b0000dee00010c0ca800026b08e00015c80000001d2868a00013e981000087900000002f249000000000006cc00000000003824c9000000000000000000000002f3800000056931926252d68bb55f25c50760000001d4c3e80000000000000b260000000a2813f4328bf529a0003cb8000000b0954c000006400032a80014a497b4fb28e14ea0000d78a5800027400000000000005a193403920005632704d8649b000000000000000006cc0000000e380008d619a000050057e03c0002910000a720002ea43605b5000010153a59304080000000000000000e7417c08580000000a300022484780003bd800122a68b1118000cb81010001bc40000002f28000000ade000000167621d26d97b91a29df5bba055266a760001d5c0000000000000000aea209000000000000000000005d1000000000000000000000004cc00000000008eb35000007d600000022c080e000000000000000047a2e940006600001a6c00000000000000000000000000000aca00000000008424b780000005f300000000000005b3800040e0005508000000000000000000020d000000000088700000000002b40bd29dced00000471dd8000b611df96fc00092a41f84d0000a691ecabfcb6624100009746f0a2306f0928000b7d08980004ca0d85141f440009a900000007d80000000608dd89c6382093464c1eb2d6a5810d832e5ef80009ca81b011800022a79247298200008910001de4e380cc0330000718bcb4df800000000000000017500000002a5d6caa640000e9cae4b0656f82f82b052d000097c9e600046a800000051a5039bed5a855500013480000001fb00008d0a7400000017aaadb00000016f404d000000079a00000027904420004b380017180000000000000000000000113200037a80013420000001c9800004a0000000000000000000076200000000006b800041b800000000007a00012b2000000000047208000001dd0060463d60458044bba1e28fa092826a000000090497a00000005f8ada0000ce000063f3e607a919e0000c31da88a49b61120000e7a43d31c06201d00004380000ffa6a552280014a662f3e22a303422ec26f80005100000002e68000000000222c00063a003806800000000006dd1ce5bd0000fe502e0000001d40eda3dd000000177c00000000000000000000000dce000000000000000000000000007b6000000179c00026c00001f83950000000918aa20920070c5c2de1ac8000000000098000000000000001c57ae1944e213ac0004ca1910000e6a3ad0000ff84eaa2500000013c45c00428eac0000001b2209c0003e63862b2ce362d00582e0c0007b32fe21680000000000000000866000000000035401a800
  | 20 => 0x2e8000000000000000000000034f0000000a120000000000a794908000000a020000000000000000000000093c27e80010b096400000000000000000000cee946128a8c8000a4000000008680ee000000000000023d92584e68dc0002d20b3cafe00009bc45a0000000fa8000000000058c0000f12cb09481960000000b940000005892dfc640a6746080000000000002f000007fe000000058a0000002e7000064500009549b441b000000000000001a1f88be43af000000000000000000000008000000000a229a709b29a1346aa900000014d60001faabc14c24f754c8000000000000000098e00051f000074868a3b3952c31e666566800074c29339494140000000000000ce60000000bc800029000003bca000000ca800000037a20a000000000000028e508800008a0cb15ba000000128ca1c00000000008660b812989c00c0000000151c57200000000003220000000000d7492700024d80007200000000000000585102000c7b04c0184ca02bc90ef9ced1ac0000c00734fb6000000000000064d000000000000000000000000000002b640060000000e2400000000011d80000002ec127400000047400000008e10002440a5e6650000000000b76000000000005200020f52fc000000041c0000000000000000bb400028140000000000000404aec1dd83181f6000000000000000000000000000001a980000009e00000000d6c00000015817a2000000000105600019f1fc800034834480016880000002eb80000002058000aea000000000000078500000000000000000000000447355142cb0c3792842a1411e7861bfa9b40006b941ca4301a88675778f5d32629f42180000003002d32e380e80000d500000000000ff00000004fe1570000000000000114026a616000000000000000000000004a7459800000065d0000ac8dbc5e60000000000a6e0002d240006c50df00013a82150000000000340221af4000098a000000000000054b0000000b1800000000000005528001702b0b0000000000000000000158424e000000000091400000000000000d4800000000023a80000000000000000aa421922c0000fce00000000007e400037d173800032742892d131e00031e00000000000001664000462000000000000000000000001d500080000dc000000000000000000000013b20003cd1ae000069c000000000000001420940000005e20000000ab100000000000000000000000000000000084a0000000b2c7b8000000000000085e00000002b240e2568000000000000000015630f0628c48000000000261401c00000000017b89415e30000000a2b4b3000000000058000000000000000f400000000001f8c0006ee000024c0000000000000de8000000000000000018d994c0aa3210000000e8a427371800000000
  | 21 => 0x70000000000388000000003a00000000000000000000000000000000000000000000019ec5c46b419d8f686a2000532a134242000000000085400000000002240001d811580000000af8000000170330a60c0000000001fa8f008300e8800000062c000000065e5fa0001f280421f84a800012020a642002840000000000e180000641e2000000000016380006560bb47c2bf497e30b3bbacd81a400000000000000000001074f1c39c00027b8db0a133509d5478c9073188c740009404a781cd402b080001cc80001f900000000000000001df8000000000000021831e468172480a0003dc00b084ca5a1f1a4e0000000000123c3760004a48804b6c000000000164400000014c80003660000c1800000011d800000000000000000005c324180006326144fba31d46e8290000e800000001a2011000000023d14c4000a8344e000113e9820000000000000000000000089d000000000000000000000000002e100000000000002a215cc5a42ae2b400001ce4ec2f74a7e5ff0001bf136a0000ed80000000002330000000b930000001340691396a8ec00000041006240001d30001bb508aa8d4f4800000000000003980008f600016711466e81f2a91c00000000013841f000000000016d6bcd27619b4000000000098d5c008a10515fc39e000000000000000000000005ce25e570a3484841b14fe1c94c36b1f000000103a2270000000980368000000000048700000000001370f900000007aa00000001da4b5000000000000000000000000000001f3c000000000000046400059005994ac636277279921a27117700000000000000000cfebda5ac80000000002520f300004310000000000b11023971c0000001ba000000000000029e098684c3b100000000000002cb800000000028d400013b482000172e0005ef2575714796000075d51c63b00001040007e62a01abc7005b452f8000000000000000000000000012785f048d1af0000000072052000020800000005400000000000000d56b9000000000007dd28f80000008fb5602b5cd942a300000008d20002241d813780580002474b1497714d29447aab9f00028f40000000000000000be154f80000000a50000001534a9340f10ac0000d908c89e000000000000010d067646b8000424000000000000042d00000000000002c592696ac0002c08984a588c832400000000001660f207f63130000001148723000110000000000000000003f8155800000000000000000000001778000000000000000055053a00000000000000000000c9c000000000103800004800002004700000001126a66046800096200039e1a0000000000000000008465100aec0007c2082800000000000009914ba2ea14593ec0000b400000016bc000000000000037320f00015d200000000010c200000000
  | 22 => 0x3d89e00002c19a201d247d387163887c00000002080009f93a5a578000000354000052200021aa6100529252fb06a018ebbf0001030b0800000000000ce00000000014365f840b21dc0000183dd093cd26b7800000000000000000ce80000002d1800000000017a2c0400000000000012a800003409d8562af25d7ab1561c000461143c00041900016f94e00000000000582000000000000056442700000000001099b809761f013d9b40a1a54825d23155140000001dd41780003959acca9c61200025a000000000000006520005d6800000000000000000006740000c9400056d13423f06aaa7100000000000001fe800000088c0000000000000269a4452ae7330c69750bd400000000009728060a200000005e1000000000000034900007de000000000000085b3c121d8952a0b443014c07066f13f88f8000bac2e800002a6000000161c0000004cd86b12fa20900020b800000048d2d3d06650315c00000000e000000000003df00000000004f200000000000000001a0400000000008a400080f4ca000000064310880000008e60a121bd0180000001f5c000000000000000000052c00000007b200017d1512000000000000000000000000000000002ce800000021d80000000003709b7400000000021f4a70930000000041038d2e500010b800000000000002a500026780004fc1ea2ac109600000029a864800000000000008470000000000000000000000000000012c8c3c0000001d74000b4036300000000000001adc0005f700000000000000001bf400000034e80009d474800023193c6403000000005a000000000000000000020c40000005280be8000000140800000045e0000000000459107138000000000000000fe5393fc048c3b265100000000002dd0f4816800000000028700007d543c000154e0843e298840000003b9ae84f76000000000000000000014a0000000000156000000016020680000000000000b9845c5eb274c00000000008ac0000001170f58f7a0005b313541a644150180008e40000869254000af61f8a5d965400004f069c3ce6eb1bda9048da8562cb80cc00014100000000000000000000bb800051a037c00000000000012b4000000000000009f000000022e20c0000878000000000152400000000000000000001b1257169c0db00024e96f20004420ffd4349f22e92ad49e870759a1a694442f13658c248e600000000000000000000000a46000497800000000000000000000000002b24000000000000000000031f17c09f27a4099ac0cfe892600018e40f000054380015000002e6a63000089b00015d05c2000446800176400015f2c84000000000000013600014a20453e2098178180000000005780000000003b08000000000000000000000000000000000000002dc88781290002ea8f4c3
  | 23 => 0x8570000000000000000204800000046190b1330000000242c2545060000000000000000000000000050c1508716a92000048800029800000000000000000000d889700000001558000000267400075200000000008190000270234000356955000014349b8a7400000000000005cc000102800000000036397a138a8503a60f4c0000001b880003fe29c000000000001300024b80000001d5000161e00000018dc00000000016c40000003c6229c5b448100000000000865e9971400040157a06c93b600000000000000964eb03e80000002338e4000093b00000000000002b4000088a5ba00000000000005a6022cb506fe000000131c8b61401d10d3000019e2a500000000002a700000000002b611da73e00028a8a6a605000127ca8c00000000000007274be00000000002298000000000575a72d730838000175800017400018949504200e1884000000000018445b686000000000003ed50e80002047ad00003a800000017f00000da75a0002f6ced80002b38000000000591ad7c1e460f1c7800000023a000093000033f58b80000008ff293220c000690000000155e00000000005c82563600ef8ca0b530001ea00008df000000000032300014792be00000000000007285a68eb0000000000000000001f0000000000b243fb8000b3486b41e000000020341b245800000040c1a89004000000000000039a0002cc80000000001a3458c0000000d240002d917f80000000000002eec5420001e08000d92b3d47800000000000000ff0f460000001fe40000ec0000000000a632b78000a0e00047b80000006334fe80000006784e700000000000000fa40000d14041650d9c1c200008f400019b0000db840c00033580000004025c48000a8607a59683e55f04f10001c3400000045c800000015a0000000000000000271c00000000000000002a900004f833018a51b0b20cd88a0000000069834e3b300004360000000000000000000000000098736f8000000000000000027200000000000003111e78394000719000000000000006aaaa93fe00000000000000000002dc003265705e8bccc8e000000000000000009780011540000002f28bd60004ea800000000000029800000003c800009da2b32822820b222fb000000000054f49f000000061700007285ec00050a800087e00000005f4aecae50000000d3267c000000032400009680009320300000c1098400000000000007da3cf2bb4a660005411ac40001760000000000000284a7bc7660003460001120b470000000000b9b0000d1c000bb900000000000004a180003440000000cc120c06b436800000000000000004443a5000000000000000013740000000ab00fce8044e00000001ea04b00028c400016000000000004c83ce00000000c93cda5880009b14ed2eac0008bf0001
  | 24 => 0x2a200015c4000008032912e8ec0001ad44802e932d0000000000000000076e00005c82a000000012c87ec00006f00029893985450b408c00007c600017550280003e0867c0000000fd00b905e0a928c80000000ff23f0fe8000297000000000000000000000000005a800000008fe0000000ef800055d8000a2c1540d3000000000000009881c292c0b7800000000056180015360001b380000003cb5ab94c00000002678000b408da0001054ed20005bf2edc056bbd00000003a00001e3aaf40007300f104a0d4e9dc00000000005292a9800000000039c0000dac3600000a341ac9521cf2e74d904cb20c00015e287b16c2e182fe9ba1c8800000098b5052c4d422000000000035c96e00017b5798000341944c8ae000248907c0009323af80005a400002280000005a9000000000000018f8a980000000001d396668ba556800000075938a29500009e138f29cc00000008ead8c6d80005081e5401a0000aa813c0000004dc00012acb1454221a915c3360000000a185c14a8815c8c600000014ec1ba01b00008581c400033f000000050200006800000000000000236000000000147e0000000000000b350b592a928883a0000784fd610e0000000000000329000068600000000000001723ccaee0000000000000000005f00008a000041018b92289882891d180015d09fa0000000000000000000000000000000000000004e180009b2a4f00000003fa00044a000082c00000020400a20001c18000f3a7ed000168423e8691231d1942c82200026cd45800000000000001180000000000000000000000000000001880000000000000000000000000000000018700000000003a3800000055f0000a3000080d03f02e822000010780009c80001b49d94000000000000000000000000000000000000000cf20000e600000000000000ab132200000000008649a8000000127a2480002ac800800000000000000001cc000000000000016343703a1000000000048000000000000000000c6000000000025cc00000036d034000000000008d8000000000117c0000260000078bc055b000000000096c00024000000001e180015ea0000000dd515ebd2000287c0003b5390800070800000022b16c8bb3000000000078b0000000000042000157400000000000000008800000000000000000000000000056e00007786755109c5ccb0b27157800054822f09d208c0001e40001648000302136882ccd46065ad8e3800000029e22840000005aa80011c411102f0001638000000199c00047f00000010e644f55b285c00000003c926154000000029f400052e0cc80000000005c581d8c940005942c3489407b0000000a6881f0001de050823f3a78b246642e30001e0400000034ba83084640d000000063400003a80000000000000000000
  | 25 => 0x43db000000000073700015880000003891edc000b920000000b787e400000009c6af90000000000000000155c00051d00000006de000000000000000000000003ec0082c48000f8600000013580000000001f600004f80000000000aa31a90000000000000000000036a00000008ee000151000000000000000001ec5210001594454a590cb1a9919c0004d780015220f300012b95f800012218acbd20003fd000149604c00016c80001d400000000229130001af4e4400000000004ae0251cb1cc5652197321031000000005100000008de2491fa0d52a9542a2e88ad67ab123a72149245400000016568591a10000bde0000a48000c804a50000000000a5700024140000002bd06b4872000442800102645d2d5800052a44c5ae00011681bd32c958d0aa5980001c0c00061c000000163a8b1292a295618b7c0000000000b6f0000a14000000000000000000005700000b8000000000000000049180000000003751654aee69f5d32e7896e0000002480e220695c100000000004f800011c871f0000001408acc3af00000000000000000000000000000054eb7500000002fc000000116cc987d4000273c89200000023600000004ef00000009550a780007840000000000bc4ad100000000000005e2a8b40002d70000f846e400000028cc000000000000060a60100000000005fe55e26897a89ac0000ddc0000000000001164000000049562c88200000010e21d6000000066600000016dc20c000000000000000025e00000000000000a0c6140003572d50b040004a28c50f9a8ad08480002b862a00000007dcb6900000000000002a529f000000049c860c8d4a8f2c026d000029e15d0000000b450000000638b7b314000000000021b00000002c200000000000000000000000000000025d1b60001a52d6885ea7f303800170a00000000007e00002148700f5e6f800000000000000000000fde00041a2e8c00000002800000000001ad80000008ab0a42a99360b0426b80002d243a3169e1c00000011a10a12143850001cd88a2afa00028904b000000000000006bb000000000000000000002ea0000000000d4828200000007802d60618000b5e0005aea02444a0001d7071004000000019880002cf000000178654115e2acc07200000000000000003778390000000000274451c06c1db23bc0003995a1037068284a5ba06943ee0000718000c8878832da6dc0000000000000000000000000101c630000000042800000000010a619d2738db428e80b00014f800000000029b01581c80000000000000000000000000000004ac0000003c680000009d00001ea400000000000013ca94a0e0800013a00000005dd17c38759f96c11c6152360ac1d5740fd57d80000000000001bc8fbe0001a6800158e00052680000004cd38d2d48000000000
  | 26 => 0x3f800000000000000d8ce040001f0000000094b0c08000000000000000000010800018748f0ac84d3267c0000560000000000000000000125200000000000000004d915e400000001b1f380007e15ec00013804d45131838b72000000000000000000000000006e61758fccf3e48400004780001620f7a59455a774264a5b4000710000000000067d0001b8978200000000000005e41e4a35019e88a23e27b046a44d3d127ed5ee00000000000007a7000000129c0001e51071384b6a000000000046e0002ae400000050a22889cc7c701e800137a7e90000000b3a3930000cc4000a860001d3516e00030480000000000001f704a06d100006e944e00019a000007c9ca58280003ca000000128400015d00026900000000000cdc0000001ef000000068700024c400000058a8000000000125987c000a5537fa2f40285d73b78000000000000000000000000000000000002211f240000000000000f786d934a06141806cd0219e6000000000023a90c400000000000000000000000000b94158000153c0000bc26f971046c50f146000000015e8000000000000002400092400000e8e1ebb11ce82fc06e0004a4049891c0004208001604000000176836800000000005f226659f2470b100003ef0000f28aae2b6000000000041500000003b2000000000000056900000000000000000000b5834200000009eb3371fd400041328821d5354000000000000061000000000000000000e051340000000000e5400000029e8372a5c4ba1ac0bd88f33e90f48000000118800000000000025d57000000001640956000000000010e0000000b7000000000780017400000000000fb2789000000000000000013e93a40003410000278000000000100e72e50700004002724d700011a675800000000000002110d18000917000000170800016a9fd8000000031945d56e1e000000015168a90002ed9732000000000000076b0000cf4e820000000000000bb53c8909125095b0db1a3cbea02a0c812bca4897826e09142641d8000000000000004880000007e500000000000000001e941ae000489016c04e00000000000000000001830000000202000000000000000000008245b717745863762e993bcaa060300004e111215b41a8ea11ea72f12d0b50000000000000000000000019780007a100008805a264b0f99448a5600046480006ca0003b88000000000000000000000000028b8000b73000000000018b05b9d6cd78000338a90c000ad641f03352c60000000ad481e09521b800124400000000000000000001f800000000002d2c00000054800000000001cf95c00000000000000b3ea7e2b0adb40000002d380000000000000000000000000000149427910e23100e06b20000df164a7b44fa942941ab9500000000000000000000b4
  | 27 => 0x9bb4fc0000b9e000000000133800000002d400026000b0264000000000000050c6f90001cd0000b2f0001c2c0000000000000f6a4d100007b10920002fc8dc093802f0000000ef449700000000000000000000000000000000000000050000003ea92b25f07f03260000001c145d000000000000000b14b505841ee0004440c3419006a20000003480da32781840000002a60a3c00065f0001efcde682c12e00000000003f9896c4867b95a8800000000030580c4aac42100000011b29812aca75c5be75427411e40006703f62a04d2a5661490000618b37000000000000030c9c4c00000000015f40000004a38194eb8b680000000ce455a1620e6c50e27e56080000008724ee946ccc800044c23351f415e09700001242a0000000132a00000000000003bd5ec9c0480c37d274840cc1a04e48c03acdca59b2e200017c4000000000000000000000008c20001c50ee40000aa0000304000000244a14899c00000000000000001ab80000000004c415f0896a5e15b95e0296000000000000000031a94704dc37e5d200000000003a88000000686000218c00057b0000f9c000000313000000000000000000000000000001452000000000000000000014d8944b1b0002f3c00087e18417200005e30002f20000b4a00012c0000b1a2ef998d12c0000000000c4695304a00000000005a080000000000002e9ce2a00033d085c000000479000000000000012b00005de00023e4ae696900000016d80000000000000000369800000000000000000000000b88000000000000232d21c3e24f518280006851f2000000014d29008680000004b90000ec8000000000000000037806ac00021f0b6929941254d02c9fc50dca0f5a302cc00000019c8000c046dc55face02e6000000000000000000000009400002629e3cff648b00025fc00035a00027344705cb14c986896c00019400004d21460000c0c214649380000096658c00000000000004ac1afc0003b449f800019c1670000000000be02431e4c10618456710c081252a23888dcbf612c0bd9b486acb8d47722052680001669f4c9821270f300009106f6487ab3d5883f73eb00000000000002b8cc68204087a8640009960002ae0000a4e5e396ec0000ad51d00000000000000000f080001ac1578000000000000000087a293800000000014d8000346000484800036a000000000000061800000002d45aa000002c0008b528a80000920001a78000c448a60000014cd03944191ffcca89e7524000140c87c1a8111000000000000000000005260f440001cb20b80000000000000000da856e078000000000000000000005d927a9b08000000000230131a0002b8aad000000048f80000000003e5976d0c82540000000000000000000000000048400000000003832ce4efa000000000105000000
  | 28 => 0x411000148919800000024b45946294d5839c3b44740610000bfa00000028f0b58361000000000072c00000011ba22c4749c7433c00015b00000000000000000000000000124c3e29350000000000000000272444c00000023290141c515500005ee44648d8630c487161a5995800014a00028c00006a331e90280f8b1937200000004640000000000000385000112a33548c9db8000aab000000000064600007b4000000000000000000041680000007720000000e107b100000000001d200000002a200000000006d600000012140000000001388262804000000000000000004f40000000001c90b0a0000002ec00000fe0001ff08342ed5de00000009f31c9000132000000600000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8ee86dc931480033d501b9262900027a21d525012000794aa2a4a024000f89434c940480035d305b0a809000e3e219744c120004f443aa49824000f49535493048001f1286a126090006ba60b614c1200061eba4a9b2a2000a5e8395365440014eb032a6ca880029e60254d95100051f424a7b2a200087f855cf644400d0f90ab9ec8880035c04375591100343f43eeab22200087f855d954440091bd063b2a8880023760c765511001c77410ecaa220008ed821d9544400b0f90eb2aa88801a2f21d64551100043fc2ae9b1a200687c855d36344001ae021baac68801a1fa1f7558d100043fc2aeca9a20058be841d9534400117b083b2a68800e3ba087654d1000476c10eca9a200487c87595534400d1b90eb1aa6880021fe157650d100343e42aeca1a20008ef825d943440071d904bb2868801a1fa147650d100043ec28eca1a20038ee821d943440011db043b286880122f21d6450d101d51e42ac8a1a2004a9c83591434400b1b90eb1a86880ea972156350d1002d4e422c6a1a20018fa87dc1624400117f08bb2a4880162f21176549100046fc1aeca9220048dc835d952440070fd0fb2aa48801a3b21d625491005e7238ac4a92201bce87058952440031ed0db8aa4880067ca0371549100147d436e0a9220029f281dc152440010ff0abb2848801a1f21576509100046fc1aeca1220048dc835d9424400b1d90eb1284880063da1b715091000cf9406e2a1220028fa86dc142440053e503b8284880021fe15764c9100343e42aec99220008bf845d9324400b17908bb264880123b21d624c91000c7b436e299220019f280dc532440051f50db82648800a7ca07704c91000cf8406e8a8a20019f080dcd51440033e50fb82a2880067c2037550510006b9286eaa0a20018f4865d541440033e100baa82880067c203735051001578c06c4a0a20058f48758941440033e50fb8282880067c203754c510006b9286ea98a20018f4865d531440033e100baa62880067c203744c51000c7a432e898a20079e4825d131440033e100ba2628800abc603624c5100247a43ac498a20019f287dc131440053e103ba2a08800a7c2077354110014f943ee2a8220009f0875055044001e62a8a0aa0880027c21d3154110007a8a9a62a8220029f081dd54044001ae4a3baa808800a3e2197550110014f840aeaa0220029f081dcd40440035e303b1280880163e21d6250110014f943ee2a0220009f0875454044001e62a8a8a80880027c21d3150110007c8a1a62a0220029f081dd53044001ae4a3baa608800a3e219754c110014f840aea98220029f081dd130440051f10cba2608801e7a209744c110014f840ae89822001af181d8930440091f10eb12608800a7ca1f714c110004f843aa29822000f515354530440013e10ea0a6088003e450d414c110
  | 1 => 0xd07b2286a881637a1f6350d5102d4f426c6a1aa2d0c3f75dd1655040b27b0bb9aa8a08121fa1f6554d410252f41ecaa9a820599d83dd543504051790cbaa86a0812a7a1b6350d410264e39a87b128200e8d43ccb6250401878ecaa2a4a0803271d9434c9410264e39a87b0282038ee87dc9644c4011df04bb2a89880e3b20976551310047dc02ecaa262018f8805d9544c40b0fd0fb2aa8988168fa136555131024aec2ee8a9a629cd1e54dd1534c40933b09baa8698a6f47d537550d310146e432eaa1a6205a9e86d91434c40b938e8a1ec498803a350f42d89310062e3b2a6a926200c9c7650d424c40b938e8a1ec0988063d20572d813102c3e43acaaa24205a3c8459554484090f90eb2aa6908129720d6554d2100477c12eca1a420687e851d943484010fb0a3b286908063ea007650d210047cc00eca1a42048bc87591434840953906b2286908163721d6350d2102d4e422c6a1a42029e481dd152484053c903b9aa49080a79a1f715492101476432eaa1242029e4815d542484051d90cbaa649080a79205754c92101476432e899242009e4875494148401e4aa8a928290803e150d325052101c7a432e898a42009e4875493148401e8aa6a926290803e150d424c52125d7240aa5b024202ce57250760484059cae498ec0908161f21573d91500243e42ae9b1aa00187c865d5435400917d0fb2286a8012a7a0f6450d5002c6f43ec6a1aa005a9e84d8d43540051dd0fb1242a800e3da1f614855067e1fbaee8b2a800593d85dcd545000917908baec6a00121fa1f6554d400252f41ecaa9a800599d83dd543500031790cbaa86a0012a7a1b6350d400264e39a87b128000e8d43ccb6250001878ecaa2a4a0003271d9434c9400264e39a87b0a8000c9c7650d31500051dd0fb1242a000ab9a0762485400246e41aebb2260038ee87dc9644c0011df04bb2a89800e3b20976551300047bc0aecaa260028f4815d9544c00b0fd0fb2aa8980168fa136555130024aec2ee8a9a606ed1e54dd1534c00933b09baa86981b747d537550d3000c6e432eaa1a6005a9e86d91434c00b938e8a1ec498003a350f42d89300062e3b2a6a926000c9c7650d424c00b938e8a1ec2980063e20172d85300064e3b286a0a60028ee87d89214c0055cd03b1242980161f21d655512002d1e422caaa2400487c8759553480094b906b2aa6900023be097650d200343f428eca1a400087d851d943480051ed023b286900023d6047650d200245e43ac8a1a4004a9c83591434800b1b90eb1a8690016a72116350d2000cf4406e8a9240019e880dcd52480033d50fb82a4900063b219755092000cf4402eaa1240018ec865d532480033d100baa64900063b219744c92024d74402a5b0a40018ee86dc951480071f50db82a2900063ba1b725052000cf5406e4a0a4001
  | 2 => 0x48001a0760265480000000001a200000000d400058110c0220ee049443c1d64894c7405e028000010a002020000000000000da1d80000000002826c8000019a508008b0009f8000000020800002200012a248000003e56976000e000000678000a8e45211c6e23e5597c33800a014629a54228845e17a8c0a8061086c14e618fc3ca52938609720e4d13c1300086a662780043000441f85a09c000009c8b431836609240001e0001c1e8000a21e962707a8009e18e388d8822626714a4500006800780326ba40588004c9a80b8b83d26e1a900281b4002748125a749640018400000000e8040c8658000000000030468002c0001b890001387688c2024c0923c2a9661080000a148e85a0316c3e00000046158209a0b6640000022a600008712681916722382b84e000524f83c560681b07c4b0ec289e60004a2b1045f95e14086551889583479000189a61e11e358743292e238fa050d0291280196e000bc7122697a601710648000750ea000006fa506e9a47318c448be2ea4688a34199026d864002007a0b200000718047c87e00224501365d04086198001ca8ca6a541ee7781602172908704c170848cc8a0c20b10e648e6379fa8d9187f094739aa311f60e09a349ec1c9f04e8966b0987d21062a7a0024a1503a3d9947022e6f16a03960000dc002640020c000003f80000276001e27f8000015c0020a8580000000001dc9f0220024870a6c0024460908300130920438800810c18310620838304600d0470843001400c01810003c324e0c629e02e0c109c25f4804400882000000073470001820012021400080c30550060000801030804430c020c04025a587eebba2caa1802baa0221d89430057340c41b1286008ef825c36150c071d904b86c2a18036310f725854300477c12e3b0286038ec825c76050c01b1887b92c0a18168fa1b645515265e1e326e6aa2a4c9c5c63dd153548094bd0db1aa6a900e1f2197550d521f61e322eaa1aa442c5c635d5435480917d0fb2286a9012a7a0f6450d5202c6f43ec6a1aa405a9e84d8d435480d1dd0db9286a90170f1d154d85520262e39aa7b0aa405c3c7455360548098b8e6a9ec0a93470fdd774595420243f43ecaa9a84068de87d8d535080953d0db1a86a1013271cd43d85420264e39a87b0284008f7815d9544c8051e902bb2a8990023ee01765513200c7c402ecaa2640587e87d95544c80d17d0fb22a899016a7a1b6450d3202e4e3a287b0a64028ec825c3614c80b938e8a1ec0990063b20971d81320143e432eaa1aa2048be87d91435440953
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x460800a2030064921d5454941484019448754d524c5210064a21d5454940480019488754d524c1200066421d434c540440019908750d414c110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x2
  | 3 => 0x3
  | 4 => 0x4
  | 5 => 0x5
  | 6 => 0x6
  | 7 => 0x94b
  | 8 => 0x94c
  | 9 => 0x94d
  | 10 => 0x94e
  | 11 => 0x98a
  | 12 => 0x98c
  | 13 => 0x98d
  | 14 => 0x98e
  | 15 => 0x9ca
  | 16 => 0x9cb
  | 17 => 0x9cd
  | 18 => 0x9ce
  | 19 => 0xa0a
  | 20 => 0xa0b
  | 21 => 0xa0c
  | 22 => 0xa0e
  | 23 => 0xa4a
  | 24 => 0xa4b
  | 25 => 0xa4c
  | 26 => 0xa4d
  | 27 => 0xb09
  | 28 => 0xb0c
  | 29 => 0xb0d
  | 30 => 0xb0e
  | 31 => 0xb49
  | 32 => 0xb4b
  | 33 => 0xb4d
  | 34 => 0xb4e
  | 35 => 0xb89
  | 36 => 0xb8b
  | 37 => 0xb8c
  | 38 => 0xb8e
  | 39 => 0xbc9
  | 40 => 0xbcb
  | 41 => 0xbcc
  | 42 => 0xbcd
  | 43 => 0xcc9
  | 44 => 0xcca
  | 45 => 0xccd
  | 46 => 0xcce
  | 47 => 0xd09
  | 48 => 0xd0a
  | 49 => 0xd0c
  | 50 => 0xd0e
  | 51 => 0xd49
  | 52 => 0xd4a
  | 53 => 0xd4c
  | 54 => 0xd4d
  | 55 => 0xe89
  | 56 => 0xe8a
  | 57 => 0xe8b
  | 58 => 0xe8e
  | 59 => 0xec9
  | 60 => 0xeca
  | 61 => 0xecb
  | 62 => 0xecd
  | 63 => 0x1049
  | 64 => 0x104a
  | 65 => 0x104b
  | 66 => 0x104c
  | 67 => 0x9c953
  | 68 => 0xa0953
  | 69 => 0xa4953
  | 70 => 0xb4953
  | 71 => 0xb8953
  | 72 => 0xbc953
  | 73 => 0x1d09
  | 74 => 0x1409
  | 75 => 0x1b8a
  | 76 => 0x128a
  | 77 => 0x1d49
  | 78 => 0x1449
  | 79 => 0x1bca
  | 80 => 0x12ca
  | 81 => 0x1d89
  | 82 => 0x1489
  | 83 => 0x1c0a
  | 84 => 0x130a
  | 85 => 0x1dc9
  | 86 => 0x14c9
  | 87 => 0x1c4a
  | 88 => 0x134a
  | 89 => 0x9c992
  | 90 => 0xa0992
  | 91 => 0x1b4b
  | 92 => 0x124b
  | 93 => 0x1ec9
  | 94 => 0x15c9
  | 95 => 0x1bcb
  | 96 => 0x12cb
  | 97 => 0x1f09
  | 98 => 0x1609
  | 99 => 0x1c0b
  | 100 => 0x130b
  | 101 => 0x1f49
  | 102 => 0x1649
  | 103 => 0x1c4b
  | 104 => 0x134b
  | 105 => 0x1b4c
  | 106 => 0x124c
  | 107 => 0x1b8c
  | 108 => 0x128c
  | 109 => 0xe89d6
  | 110 => 0xec9d5
  | 111 => 0x2089
  | 112 => 0x1789
  | 113 => 0x1c0c
  | 114 => 0x130c
  | 115 => 0x20c9
  | 116 => 0x17c9
  | 117 => 0x1c4c
  | 118 => 0x134c
  | 119 => 0x1b4d
  | 120 => 0x124d
  | 121 => 0x1b8d
  | 122 => 0x128d
  | 123 => 0xe8a16
  | 124 => 0x1bcd
  | 125 => 0x12cd
  | 126 => 0x104a14
  | 127 => 0x2249
  | 128 => 0x1949
  | 129 => 0x1c4d
  | 130 => 0x134d
  | 131 => 0x1b4e
  | 132 => 0x124e
  | 133 => 0x1b8e
  | 134 => 0x128e
  | 135 => 0x1bce
  | 136 => 0x12ce
  | 137 => 0x1c0e
  | 138 => 0x130e
  | 139 => 0xb4b11
  | 140 => 0xb8b11
  | 141 => 0x1eca
  | 142 => 0x15ca
  | 143 => 0x1d4b
  | 144 => 0x144b
  | 145 => 0x1f0a
  | 146 => 0x160a
  | 147 => 0x1d8b
  | 148 => 0x148b
  | 149 => 0x1f4a
  | 150 => 0x164a
  | 151 => 0x1dcb
  | 152 => 0x14cb
  | 153 => 0x1d0c
  | 154 => 0x140c
  | 155 => 0xe8b56
  | 156 => 0xecb55
  | 157 => 0x208a
  | 158 => 0x178a
  | 159 => 0x1d8c
  | 160 => 0x148c
  | 161 => 0x20ca
  | 162 => 0x17ca
  | 163 => 0x1dcc
  | 164 => 0x14cc
  | 165 => 0x1d0d
  | 166 => 0x140d
  | 167 => 0xe8b96
  | 168 => 0x1d4d
  | 169 => 0x144d
  | 170 => 0x104b94
  | 171 => 0x224a
  | 172 => 0x194a
  | 173 => 0x1dcd
  | 174 => 0x14cd
  | 175 => 0x1d0e
  | 176 => 0x140e
  | 177 => 0x1d4e
  | 178 => 0x144e
  | 179 => 0x1d8e
  | 180 => 0x148e
  | 181 => 0xe8cd6
  | 182 => 0x208b
  | 183 => 0x178b
  | 184 => 0x1f0c
  | 185 => 0x160c
  | 186 => 0x20cb
  | 187 => 0x17cb
  | 188 => 0x1f4c
  | 189 => 0x164c
  | 190 => 0xe8d16
  | 191 => 0x1ecd
  | 192 => 0x15cd
  | 193 => 0x224b
  | 194 => 0x194b
  | 195 => 0x1f4d
  | 196 => 0x164d
  | 197 => 0x1ece
  | 198 => 0x15ce
  | 199 => 0x1f0e
  | 200 => 0x160e
  | 201 => 0x224c
  | 202 => 0x194c
  | 203 => 0x20cd
  | 204 => 0x17cd
  | 205 => 0x208e
  | 206 => 0x178e
  | 207 => 0x196251
  | 208 => 0x196252
  | 209 => 0x196253
  | 210 => 0x196254
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1424
  | 6 => 3043
  | 5 => 322
  | 4 => 6
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
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*2) 2
  | 8 => packedAt gbK8 (1660+((h/20+packedAt gbK8 (1560+(h % 20)*5) 5) % 79)*7) 7
  | 7 => packedAt gbK7 (55058+((h/474+packedAt gbK7 (52688+(h % 474)*5) 5) % 2893)*12) 12
  | 6 => packedAt gbK6 (151134+((h/1014+packedAt gbK6 (146064+(h % 1014)*5) 5) % 6182)*13) 13
  | 5 => packedAt gbK5 (19640+((h/107+packedAt gbK5 (18998+(h % 107)*6) 6) % 419)*10) 10
  | 4 => packedAt gbK4 (424+((h/2+packedAt gbK4 (420+(h % 2)*2) 2) % 10)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x63f8fc0fcc63f1c0e0ff1c0e0ff0227329349f
  | 1 => 0x7c7f1ff0307c7e00ff07e00ff070459c51c8e7
  | 2 => 0x807fe0003f807fff0007fff0007199e09e0f07
  | 3 => 0xff8000003fff80000007ffffff8e1e00e00ff8
  | 4 => 0x3ffffffffff80000000fe000fff000
  | 5 => 0xffffffffc000000000000000000fffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x209824218420b042223304222310003109148b
  | 1 => 0x242908609024520446152044612000941148a5
  | 2 => 0x807240c31480649604264960424089e01a0d06
  | 3 => 0x4900010429490008084092898c061600e00250
  | 4 => 0x2082a52092898c00080840b6000e4a000
  | 5 => 0x5244938e0000003010800301080dff4a000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfffefeeefefefe80fffefeeefefefe80fffefeeefefefe80fffefeeefefefe80fffefeeefefefe80fffefeeefefefe80fffefeeefefefe80fffefeeefefefe80, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_46402
namespace PEqualNP.Outside.L_meta_46402
open PEqualNP.Outside.L_meta_46402.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 6 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 2 := block_range (n:=2) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 66 := (concat (concat bs0_4_0 bs0_4_32) bs0_4_64)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 42 := (concat bs0_5_0 bs0_5_32)
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
theorem bs1_3_0 : Interval s1Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 6 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 2 := block_range (n:=2) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 66 := (concat (concat bs1_4_0 bs1_4_32) bs1_4_64)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 42 := (concat bs1_5_0 bs1_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 64 := (concat bs2_3_0 bs2_3_32)
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
theorem bs2_4_96 : Interval s2Atlas 4 96 23 := block_range (n:=23) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 119 := (concat (concat (concat bs2_4_0 bs2_4_32) bs2_4_64) bs2_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 45 := (concat bs2_5_0 bs2_5_32)
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
theorem bs3_3_0 : Interval s3Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 6 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 2 := block_range (n:=2) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 66 := (concat (concat bs3_4_0 bs3_4_32) bs3_4_64)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 42 := (concat bs3_5_0 bs3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 6 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 66 := (concat (concat bs4_4_0 bs4_4_32) bs4_4_64)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 42 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 64 := (concat bs5_3_0 bs5_3_32)
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
theorem bs5_4_96 : Interval s5Atlas 4 96 23 := block_range (n:=23) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 119 := (concat (concat (concat bs5_4_0 bs5_4_32) bs5_4_64) bs5_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 45 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_4_0 : Interval gbAtlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 6 := bgb_4_0
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
theorem bgb_5_320 : Interval gbAtlas 5 320 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 322 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) bgb_5_64) bgb_5_96) bgb_5_128) bgb_5_160) bgb_5_192) bgb_5_224) bgb_5_256) bgb_5_288) bgb_5_320)
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
theorem bgb_6_3040 : Interval gbAtlas 6 3040 3 := block_range (n:=3) (by decide +kernel)
theorem ggb_6_0 : Interval gbAtlas 6 0 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) bgb_6_64) bgb_6_96) bgb_6_128) bgb_6_160) bgb_6_192) bgb_6_224) bgb_6_256) bgb_6_288) bgb_6_320) bgb_6_352) bgb_6_384) bgb_6_416) bgb_6_448) bgb_6_480) bgb_6_512) bgb_6_544) bgb_6_576) bgb_6_608) bgb_6_640) bgb_6_672) bgb_6_704) bgb_6_736) bgb_6_768) bgb_6_800) bgb_6_832) bgb_6_864) bgb_6_896) bgb_6_928) bgb_6_960) bgb_6_992)
theorem ggb_6_1 : Interval gbAtlas 6 1024 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_1024 bgb_6_1056) bgb_6_1088) bgb_6_1120) bgb_6_1152) bgb_6_1184) bgb_6_1216) bgb_6_1248) bgb_6_1280) bgb_6_1312) bgb_6_1344) bgb_6_1376) bgb_6_1408) bgb_6_1440) bgb_6_1472) bgb_6_1504) bgb_6_1536) bgb_6_1568) bgb_6_1600) bgb_6_1632) bgb_6_1664) bgb_6_1696) bgb_6_1728) bgb_6_1760) bgb_6_1792) bgb_6_1824) bgb_6_1856) bgb_6_1888) bgb_6_1920) bgb_6_1952) bgb_6_1984) bgb_6_2016)
theorem ggb_6_2 : Interval gbAtlas 6 2048 995 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_2048 bgb_6_2080) bgb_6_2112) bgb_6_2144) bgb_6_2176) bgb_6_2208) bgb_6_2240) bgb_6_2272) bgb_6_2304) bgb_6_2336) bgb_6_2368) bgb_6_2400) bgb_6_2432) bgb_6_2464) bgb_6_2496) bgb_6_2528) bgb_6_2560) bgb_6_2592) bgb_6_2624) bgb_6_2656) bgb_6_2688) bgb_6_2720) bgb_6_2752) bgb_6_2784) bgb_6_2816) bgb_6_2848) bgb_6_2880) bgb_6_2912) bgb_6_2944) bgb_6_2976) bgb_6_3008) bgb_6_3040)
theorem allgb_6 : Interval gbAtlas 6 0 3043 := (concat (concat ggb_6_0 ggb_6_1) ggb_6_2)
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
theorem bgb_7_1408 : Interval gbAtlas 7 1408 16 := block_range (n:=16) (by decide +kernel)
theorem ggb_7_0 : Interval gbAtlas 7 0 1024 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) bgb_7_64) bgb_7_96) bgb_7_128) bgb_7_160) bgb_7_192) bgb_7_224) bgb_7_256) bgb_7_288) bgb_7_320) bgb_7_352) bgb_7_384) bgb_7_416) bgb_7_448) bgb_7_480) bgb_7_512) bgb_7_544) bgb_7_576) bgb_7_608) bgb_7_640) bgb_7_672) bgb_7_704) bgb_7_736) bgb_7_768) bgb_7_800) bgb_7_832) bgb_7_864) bgb_7_896) bgb_7_928) bgb_7_960) bgb_7_992)
theorem ggb_7_1 : Interval gbAtlas 7 1024 400 := (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat (concat bgb_7_1024 bgb_7_1056) bgb_7_1088) bgb_7_1120) bgb_7_1152) bgb_7_1184) bgb_7_1216) bgb_7_1248) bgb_7_1280) bgb_7_1312) bgb_7_1344) bgb_7_1376) bgb_7_1408)
theorem allgb_7 : Interval gbAtlas 7 0 1424 := (concat ggb_7_0 ggb_7_1)
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 2, 34)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfffefeeefefefe80fffefeeefefefe80fffefeeefefefe80fffefeeefefefe80fffefeeefefefe80fffefeeefefefe80fffefeeefefefe80fffefeeefefefe80
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4294901486 * 2 ^ 32 + 4278124160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_46402.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,1]⟩,⟨.and,[6,2]⟩,⟨.or,[7,3]⟩,⟨.or,[0,1]⟩,⟨.or,[9,2]⟩,⟨.and,[8,4]⟩,⟨.or,[9,11]⟩,⟨.or,[8,4]⟩,⟨.and,[10,13]⟩,⟨.and,[12,5]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4294901486 * 2 ^ 32 + 4278124160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4294901486 * 2 ^ 32 + 4278124160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_46402

open PEqualNP.Outside.L_meta_46402 in
theorem PEqualNP.Outside.L_meta_46402 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4294901486 * 2 ^ 32 + 4278124160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4294901486 * 2 ^ 32 + 4278124160) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)