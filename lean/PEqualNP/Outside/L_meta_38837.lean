import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_38837.Model
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


end PEqualNP.Outside.L_meta_38837.Model

namespace PEqualNP.Outside.L_meta_38837
open PEqualNP.Outside.L_meta_38837.Model
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

def SBf (j : Nat) : Nat := [6, 7, 3, 7, 7, 8].getD j 0

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

end PEqualNP.Outside.L_meta_38837

namespace PEqualNP.Outside.L_meta_38837
open PEqualNP.Outside.L_meta_38837.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x2000000000100000001240df30de32bc41dc32bf42be40dd30bd42be41dc31de31bc40
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x8c020013651903288218cd145429c282854c524c2a8a2985594632
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 7
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => 2*((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/25+packedAt s0K4 (192+(h % 25)*4) 4) % 12)
  | 3 => 2*((h/9+packedAt s0K3 (189+(h % 9)*3) 3) % 7)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xfffffffe07fffffe07fffffffe03ffff1ffe3f
  | 2 => 0xffc07ffff80fe03ff83ff81ffffc0f80e79fcc
  | 3 => 0x3fff81ffffffffffffc0ffe03ffffffff8e3ff
  | 4 => 0xc00001fffff0003fffff00003ffff000ff03f0
  | 5 => 0xfffffe000000003fffffffffc0000000fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4a4508423122490a014b2a294a2194aa0b2e15
  | 2 => 0x929314a450e485565815591596e48d066596cc
  | 3 => 0x210a252882491424aa809544254a2a54b0c16a
  | 4 => 0x3a2c59d12481d9bb34e6061939b3c418df03b0
  | 5 => 0x3c3061e1c70e1e3dc738e79e01c30860fef800
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fc00cc00fcc0ccc0fc00cc00fcc0ccc0fc00cc00fcc0ccc0fc00cc00fcc0ccc0fc00cc00fcc0ccc0fc00cc00fcc0ccc0fc00cc00fcc0ccc0fc00cc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_38837
namespace PEqualNP.Outside.L_meta_38837
open PEqualNP.Outside.L_meta_38837.Model
def s1K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x31500000a00070000024104008208404200054102a48dfc42fd40fd31fc40be40ff31fd21fe43fd32fc43bc40ff40fd30ff41fe30fe42ff21fc10fc31fc30ec21ff43fd41ff20fd10bf43bd43ff32fe41fe21fd20fe40ee21bf42ff30fe31bd42be41ff42bc41fe10fe32fd42fc20fe20fc41fc21fd43fc32ff10
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x70005a283810b8481140086810005830a80030900028180008681930014800000c48d03d20118000d00850c830004958c80031b05801b00000e080b00a4800280800900a7828d020300a5eb95021baa8e655c53482d8a4a0cfd4d429f2a4653c5050b5a84194fd51109ea90833f540427ca99979086109ea9c813c548c67ca810db948309ea96873d540c35842205b94621d7aa4436d52d0f68a2a14f953109e2a4613c54886e8a2904fd52309e28287ad4388678a8884f553109e2a241345150b5ca5a1cf54e41f2988433e50903cc6210eb106219eaa0633d544cad8a4984f553209fa92873e51903c842086b086409f28081af4388678a898cf548409f286853f548867ea898e7d4d43b6a90813d54cc27ca9085b54b41d6a12413e54c827aa8106b90621b729683775150aeea2986b54840d6a10433d52903688390d714d109e2a441b6511067aa9195b54b319e2a24374514c27aa7a14f55242b7290813f548c6daa5084f54c409eaa6656d520c3588210cfd512096a90816e52d0edea4a0ebd08219ea98836e52cc67ca320eb94840afa9a413c54042dea4886b50c219e28a873d529067ea890cf953309f288833e540caf6a098cf151309eaa4873e5410b58a910cfd5220b7a9263ad42ccaf0a098cf95031b7a92613d54842dca210f9d0421d7a1843ad540875c42204fd5130baa8861b4410876ea2a14f94041bba8a416e52843c88210eb54b43d7208433e544caeca2184f95321d6a16413d54cc7cca210cf950309e28a853e540827ca2206b88640afa9a213d54c867aa8196bd4942d7a14433e54cc6d8a4884b54b439f28e856c524c774a0204f950439f28e873e50d0ee8a2a15d947329eaa0433e50907488210eb50a21
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x35040044282ac30005c12020010030070170c60080000ce5f5a4f0038bd9621102e0604c421a918542cca2c65509208b18552d0ea66010421c918552d0e3860551328918552d0e2d6294241a9191310862d6214143c9d8552d0e2d6215231a9987548861d6315010a358c54886a461509208b58a54c421d6315221a918552103265408610a959441087246154840c950a51cca2461548408bd89539032651086408b185521032752145428b58a54cc23661d5220a918542c822e65d0e21c915021042a661152218d59441086646154b438d18552d0ea4648c4218d185544ca2d62152308d185521022d65d0c21c314d42482a563104218b58854043276154840c9508514822f6254e418b58a540c7276214542a9185420ca2d65084408b58a544caa46150c21a9d9441086a46154b43a998641086646154840
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x409800c00212bb0a810821099c76254e40848e2b14a99850573150210421238ac4282878114c6150920a0ce7b10a2a142575192310861238ac42a461215cf6510421
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s1K6 (i*5) 5
  | 5 => packedAt s1K5 (i*16) 16
  | 4 => packedAt s1K4 (i*27) 27
  | 3 => packedAt s1K3 (i*38) 38
  | 2 => packedAt s1K2 (i*49) 49
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 6 => 2*((h/1+packedAt s1K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/30+packedAt s1K5 (800+(h % 30)*6) 6) % 50)
  | 4 => 2*((h/76+packedAt s1K4 (4455+(h % 76)*8) 8) % 165)
  | 3 => 2*((h/41+packedAt s1K3 (2280+(h % 41)*6) 6) % 60)
  | 2 => 2*((h/10+packedAt s1K2 (490+(h % 10)*4) 4) % 10)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0x7fffffe03f81fffe0f81fffffc1e03fc9fe67
  | 3 => 0x7e07ffffc001fffff001f81fffe003ff18f87
  | 4 => 0xf8007fffffffe07fffffe001ffffffc1fe0ff8
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x3021088c48910408052925923012299212b0ab
  | 2 => 0x5246311439222931605a0ae4d64142a4c95665
  | 3 => 0xa48b5a289075525aab0513316ab40539718b86
  | 4 => 0xc614644122460364d29640418d299601ac0d50
  | 5 => 0x7187871c3879c7f1ce79c780e311831ffe000
  | _ => 0
def s1Atlas : Atlas := ⟨6,rawDecor 61 s1Pos s1Neg, 0xfaaaa0a0faaaa000faaaa0a0faaaa000faaaa0a0faaaa000faaaa0a0faaaa000faaaa0a0faaaa000faaaa0a0faaaa000faaaa0a0faaaa000faaaa0a0faaaa000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_38837
namespace PEqualNP.Outside.L_meta_38837
open PEqualNP.Outside.L_meta_38837.Model
def s2K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s2K2 (i*4) 4
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 2 => 2*((h/1+packedAt s2K2 (4+(h % 1)*1) 1) % 1)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x5fc7ff3c7ffe03fc
  | 1 => 0xffffffffffffffffffffffeff8e7ff8e0ffccf
  | 3 => 0xfffffffffffffffffffffff7ff07fff00fff0f
  | 4 => 0x7bfff83ffff00ff0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x2072404c1262615c
  | 1 => 0xffffffffffffffffffffff90960a1484a4a4c5
  | 3 => 0x920d42921494b0a
  | 4 => 0x60486b249818ea0
  | _ => 0
def s2Atlas : Atlas := ⟨2,rawDecor 27 s2Pos s2Neg, 0xeeaacc00eeaacc00eeaacc00eeaacc00eeaacc00eeaacc00eeaacc00eeaacc00eeaacc00eeaacc00eeaacc00eeaacc00eeaacc00eeaacc00eeaacc00eeaacc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_38837
namespace PEqualNP.Outside.L_meta_38837
open PEqualNP.Outside.L_meta_38837.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x6450025820600000122810c5049006041041fd10fc40fc41fe30fd42de30fe41f421ff43ff32fd43fe31ff40fd32fc30fc32bc42fe20dc30ff42fd41fd20fc10fe42fd31ff41ff20fc31fe40fd21fe21ff21ff30fc42fe10ff10fe32fc21fc20fd30fe43f721ff31be42fd40fc43
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x3c480000048106085b10002006163c180040c024c0008820600100002c48f20000816c080000018322000850014000820c04200141038208001d7d4d209faa2653f54486b8a6904f55010ba28a81d5510c3ae42186b10a21bba8a817651ccaeaa321db94b31cf2a0617751483b060105d94440b7294877651886dea4a05d946439f294859d5310a7ca9994f952219faa22177514cbca6410eb10932bb28c413e5210b688410f5c86309eaa4436d520c3cc6410e794c42afa9a213c544cae8a2907394830b6292819d540c35885194f95220ba28a65ac420867aa9995d54440aea9e81e4420867ea8906d90821aea9e21cd520c2f6a0995754c42ba28a85d830c82bca1185d94430d6214413e54042eea2a15b14910f210c415e530867aa9105794f10af29885b541106eaa2185bd4941af28061d4210c33884184f95030aea9e417652086eaa3997694030eb298433c54486bea6a06b948429e2a2215c53442eaa3a15794f20ce21461d4218c3ce8410d754c21da216437651d0ad8a4a0e7908309eaa6633d540c2f0a0997554c21b7a92213c54482eaa3105b948309f2a6636d5290fc842106b10820b6a96635e53d036c8590e790a30d221043e652087aca2185714d40
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xc00840000000000002806000000080f300001085c095594210c22c6255010c910a51882a462504419918951103284214132f008430083844208430c3551520c3855310821c9108514cb265408620c354c42086c56310821e198c42087856310821d1549510c2e0604c821a91913208786531082187594420c2a66290821e210830083844208630
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x8090aed2988410d057598c4208702b288410861415d44208430
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
  | 6 => 2*((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/29+packedAt s3K5 (736+(h % 29)*6) 6) % 46)
  | 4 => 2*((h/67+packedAt s3K4 (3159+(h % 67)*7) 7) % 117)
  | 3 => 2*((h/36+packedAt s3K3 (912+(h % 36)*5) 5) % 24)
  | 2 => 2*((h/8+packedAt s3K2 (196+(h % 8)*2) 2) % 4)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xff01ffffffffffe07ffffe03fffffffe3f1fff
  | 1 => 0x7ffe07f01fc07fff83e07ffc1f07e03fd9e267
  | 2 => 0x7fffffffe0007ffffc007ffffff8003fe1ff87
  | 4 => 0x800007ffffff81ffffff80001fffffc1fe03f8
  | 5 => 0xfffff800000001ffffffffffe0000001fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x14c11124488104014a49641230a29a20b0cab
  | 1 => 0x2a14b321c91aa4e5816c2ad50d4742b4d96265
  | 2 => 0x4c28644483a3492aac104d1a56d1051960b786
  | 4 => 0x68b1468912320db34a59019218e59611f40350
  | 5 => 0x70c1870e1c3c71dc739e71e380861821bfd800
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeae0e0aaaa8080eaeae0e0aaaa8080eaeae0e0aaaa8080eaeae0e0aaaa8080eaeae0e0aaaa8080eaeae0e0aaaa8080eaeae0e0aaaa8080eaeae0e0aaaa8080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_38837
namespace PEqualNP.Outside.L_meta_38837
open PEqualNP.Outside.L_meta_38837.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x10040000000b0460001880002d20010020850020000000000000430c000004000100b012480fd42fb20fd10fc30ff10fe10ff32ff42ff31ff21fd32fc20fd43be42fe43fe21fd30bd43fc43ff41fe32fc10fc32fc40fd40ff43fc42fe41ff40fe42fd41ff30fe31fe30fc21fd21bf43bc42fc41fc31fd31fe40fe20ff20f820fd20
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x8940000138100182a98100000000c05e0000000020090005006000000643850e0c0222c28c9f00040000c3061e0a0c0040000700155e53d06dca5984fd5121b7a92213e54ccaf4a1995714d21d621041b943c837286104f151209ea9c853c544ca7ea9194f552209f2a4419d43ccb7485907a08420dc21641ac42882daa5986e108209eaa061ba420833ea6a1cfd5132d42104178504ca78a890cf55010f42104177514ca7aa8196750c31bd280837a520827ca998fa4c820bd284417850486dea4a04fd5120bca80633d5490ef0a0a15ed4142cea98859d434caf4a018ded41329eaa0633c544437686106794c428ea9885ea520827ca818dd14532b6292217a50886d8a4a04f94a429e292875d5310b3a8718de540419f2a0617a50d0a78a9197ad0820af298853e52d0e7ca9985e542219f2a0877950d0a7aa998eb94842afa9a213d5310af2a1994f95221f5108416d520c67ca8086ed0f20ae29a213d54ccabaa7a0cf94842bda82433f544427aa9985b94831afa9a43ea320827ca8194f55221
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x101000a000400000101000201221000100000700e0002e0614c820aa18943082a8644c820e250d32083154314532a658c420828d631082087195434ca686254041c350d520c61d6395221a658c42c828d6310a20e298c42082aa6290820aa99221082896310820b258c42082a96310820aa19232083896310820
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x44897399221082443b28699041a050c614c820
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
  | 5 => 2*((h/50+packedAt s4K5 (736+(h % 50)*6) 6) % 46)
  | 4 => 2*((h/61+packedAt s4K4 (2673+(h % 61)*7) 7) % 99)
  | 3 => 2*((h/35+packedAt s4K3 (798+(h % 35)*5) 5) % 21)
  | 2 => 2*((h/8+packedAt s4K2 (147+(h % 8)*2) 2) % 3)
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xc0fffc07ffc0ff83ff81f83ff87fe03de473e7
  | 1 => 0xff01fff81ffffffc0fffffc0ff83fffe7f8c7f
  | 2 => 0xffffffffe000fffff001fffffffc003f87ff87
  | 3 => 0x1ffffffff03fffffe0000ffffffc3f80ff8
  | 5 => 0xfffe0000000003ffffffffff00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x5614c47144992980b3b05a19582722a4e431e3
  | 1 => 0x824c4890c90840940492aa48288149a82d842d
  | 2 => 0xc29112283a2922d504134a2b548051302de86
  | 3 => 0x28b1a24412301b4a69640430c6729603d00b50
  | 5 => 0x30c1c3871c3ce3f38e79c73c04631823ff6000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xece0ece0ec80ec80ece0ece0ec80ec80ece0ece0ec80ec80ece0ece0ec80ec80ece0ece0ec80ec80ece0ece0ec80ec80ece0ece0ec80ec80ece0ece0ec80ec80, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_38837
namespace PEqualNP.Outside.L_meta_38837
open PEqualNP.Outside.L_meta_38837.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x663fb10442fca1205f94342bfaa661dd300c3d86510df55031bf28441ef4290afea6a06f90840beaa241df308c3dc85996f90942dfa0c817e510c6f8a6a0dfd4810bf28821ef328cafaa5185f94440ef182617d520c7da64195f94241dfa12837e53c82faa3197d50441fba0a837e52d07ec6218fb54b43bea8683ed52106f8a098ef95021f729687f551103de65105f55330bea8c21bc43102fca621df54021bea86437f544c27ca9887d90431efa1a877d52903dca5885f95321be2a443f65110afea610dfd4532be29c43f621086fca1196f90d43ef994657e52042fea098fd48421bb288855d53102f8a8985fd5232f6a90817c54442eaa3a1df94a30beaa263ed21086d8a498dfd4910be29c417e52d03dea4a05f54d10fc282856c524c3de85105f14142bf2a2637c540c6f8a9106f90140bfa9a43f541c43ee6210df54443bf29621df320caf8a2987b50b21bea90837f53506f8a9906fd5130f6a90637e544cbbc64995f94321bf2a221ef21082faa021ded4142bf29c857e5310b7ea8905fd4f20bf290437e53903dc4290cf95031be2a2417e53083ea82885fd4e20bf29e21bf41906fea8905f55310dfa0881ed20082faa2205b54b43bea9e217c54043d885105794c40fb988217e53d02fca318df94343bea90817f50506fca4186f50b41bf28085be54c42fca4885714d21bfaa4437c504ca7ca810db94b43bf28887bf4210bda6490df94c41bfa9e437e51ccb7e8220df15210beaa4837d508cbd8a4a05f14a10bea98437f5050efaa0197dc4210be29221ed42482f8a0a1dfd5320fb08221ec32082fea8085f55332bf2a0217c534437a80207e48020beaa6417d54042fea090df54430be29e417c54c86fea6085fd5032bf28e617c53086faa5105f14520de2a241ef320877a86a0fd0c721bfaa643ed420cafca3905f54e40bf28e817d51c82fea2a15f54e42bea8c417f5250ff621086f10a40bea84437d52cc6f8a6a17bcca21bf280657e52907f681905f95332de2a261de328c6f8a4985f94842be2a041f5410c7dea498df14c10f7a92617a500c6f8a998df94a10be29a437c53842fca6205fd4c20bf280217d548cbda85905f94221bf29065bf4390ff081905f94231bf280837d508c6faa921df54a41dfa0481f741906dea4a06f55021be2a0657e528cafaa8985f94442ef298817e510c2faa3217bcc932bf298437c524c7de40105f14d20bf28c617e530c2fca9085fd4520bf2a0657e53d07f440105f55121bf28041dc328c6faa6207e4c110bea8e87ed42487baa6205f54c41bf2a0617651d0efca721df14b10bf28c817e52082fca890df54e30fb20a437f52507bc86987ed4142fa18c21f641cc7b86418df54f41bf28683f5310c6faa718ef95031bf29687ee42c877a8621fd54442b7290837e5290b7a84215fd5030
  | 1 => 0xd53487e8a2987dcc631bfa9a41bf4290af2a018df15121fd18221bc42102dca418cf55031ef18a637c548c37c87207790f30beaa643ed21082fca5207d14532fb288817c53c43ee20085f55110fda0281de4310ed8a4a05f94f21be292876e52102fca1185f94743be298417f53442fca820df15131bfa82657e53d0afea0a17d90621bea8e817e500c2fea7085f54332be290213f544c2fca9885f55331fca00817c54cc2faa5085f95331bf288417c515037e80204f55021dea1e837d52886faa3995fd4b10bfa8a817d500c6faa1a1df54f21bfa9a857e500c7dc84905fd4940f7190657c50487ea8398df54241bf2842174514cafaa210778c831bea9661ef21883dca420df94c31bf2a4617c548cbea20084f55310bf29c837d50107be6218df94a31f721085ef42082faa710df55240bfaa265ec524c2faa7105f54243bba8a61f721486fea7885f55210f7990417e51886fca821fb50b32f721641ee420ca7ea89077cc631bea98217e53443dca4205fd4e21bf28c417e544c3e86210df54f20bea8e617e540c6fea9087ed0240bea96837e5090afca2197dd4532bf2a6617e518cb7c86207e44010bf298217f54082fca81077d4d21bb28881fb20483ee6390df94841bfaa221f541487ba6218dfd5332beaa061755110adaa5885bd4931bf2a0857d5210ff4a018fb88120bf298657f5150ff480205fd4a10dea0c81f930842fea818efd0c43bea9c653c54482fca418df15021efa1c873c544c3d884105bd4930bf2a043f651d0efca7105f94b30beaa0417d52043ba86985f54042bfaa4637c52503d865105f94641bf290817c54c42faa3185f54c20bfaa2437e53483de4210df54742bf2a46577514cbee4310fb14931b6a90637e50103e862085f54643bf28665fb304c3ea8310df94642dfa1e837e5210efea498df95120f7a12857d5310afaa7a15f94441dea0883bd54c42f8a6a07e8c210ba28a61f7514c37c85207750f30f7192437d544cbde4310df54432bea9c837c50506faa918df94021bf29c21dd4310f7a82207b90921bea8663f9300c2fca3a17dcc610bea8885ef20882f8a8997b94831bf2a4637c53c86f8a2a15f94243be2a061fb20882f0a0a16f55031fb20e217d53d03be60185f54830beaa461ed32c87f680105f14941ee990657f548c3eaa3a1df94e21be28a65f840082dca5886f90541beaa0656d52106f8a9996f10e40f6a96217551103ec82885f54342dfa1683fb308c2faa7085f55021bea94637f54cc6daa4205f95040dea12837f514c2fea810df54242beaa4437e54886fca521df54b40f6190437d5290ef8a918df95320bfaa2637d52c43ee6298df94643bfaa4417e54882fea4985fd5310fca8063ed21882fca598df55220ee29a43fa10042faa9215f54910afa9a43fa300c2f8a2a1df54640bf28
  | 2 => 0x1c59108c2a01009000010040523800000170080000c000000f0140e004002b4310180700c0f06c030780000c0c1cc020140a1800029c000692b0a4fc0081909c020150c0003e0000307400050940580a2f01f004ca0180002c0002835004000645b090103cc0a00c400980003000000110042f0040004831018011580900c14028590141000007008340401d018070000f0bc0a00c013097c0143d00c12008180002f1585e0001500001018010840704c08004000b4080285e0cc180042f06402174000044b0b40007c060081535c0400805000000140006c3802802274080001401c10190060000005c6800c1202c104e40c11425004011580208c0601c13074810000e0002604400504000501f0ac320080d0106f0c41180c21bf288437e534877e86a0fd90441f7196437e5010fda84215f54d20bea96877
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x514ca776154d20ba181424827661d4f20cb55252c426d6294410c754f41102746155132b5185320ca746154c20d314e324873954540319b98b540c65e63d4a109d98654cc27561d4f208f59251042e962103208f992544c27561152329b98a518c2756195131bc185308436452d45309b189530427765504419b5885150f3a54540319b189544c66c62551309798c52042786055131ae583411027461551309b98a54cc63d65950319b988540827960d53329bd895010ee5620c7219dd95310c67b65440109bd89544c2e86050b21d514e414873654504318f99352c423d6414c208f592518c2796014e219b98a544c23e64150319b988530876552547439dd85544ca7a60d5031b9189310c63d64d4f208f990514ca6e62953308f992518c32f54d4930da94a500c73564145328f19152443555354440dc905500c66c6254043cd153514c27b60551209b58a544c23e64946209d58654cc26d65108209b596420cba84210020d9148514c23d6494d209b98b53c432d5454831ba18142486756590431b518d210866e62d5330cd95141c427b605513297195434c23f6454d209b98854042796014c21b9185320ca3e64944109d195414863d64145329d986544cb2e54548319b988540c65e63152209ed81544c63d6414b109b5973208766425444297d95320ca5e6514d218fd95401026f6548421cd150514c3655294440ad987435072e5494b109d584540ca5e6315010c754d411023c6454d20e9509414863e64d4c219bd89544425c63549108f59053c426d62153109d98454042766114c209758f52842e86050842d354d521036552947438f59053887aa42103209ed95200825f6550c439b189539073651504409bd89534426e62150309b588540c63e6494d209d984540cb35540c4219b18954442e56110820ce552500c67661153208f994544c23f6454321bc58031842746154e42cb550320863e6414c218f992544832c54149309b98853c436b4214142d954a410c63f6550441cb15242482756114c20ce952500c67561153208f592518823d6414c21c754e43102e9600c820d9cc8514ca6d6295331cb55152c427661150308f19153442e56110a20d95095110a5d63951219758c520427561951309b58b54cc26d6215231cb553320863e6414b109bd89534874e53948409b189534425d6315210da949500c73754d45308f191500ca5e6394d219dd85539026c6254e40d354c320826c62543319b988548426d62150308f596540866f6254e409b58a54cc2746154e40ab19120083356115120d914b314c63e64d4f209d984548c32d62151209d584548826d6215210cd55331086746154d209d587538825f63549109b594320867661152209b588544427960d52219d594310867765484219d584540c34c5388521d954a41107655290710
  | 1 => 0x6010c434d70280c00270a8007007028007a00000080002050c004103103042340307006167b80412000400400300d8080610078202e00000200c47048280403024007658000340203040000c18030044e019bd89530426d6214c109b988544425e63152109d584548c2776155130cb152204834c5390921cb151424826f65508429718d54443545350521cd552210866d62d4e10cdd50514c2756115020cd5095110a6f654c832dc505500c6b860508429bd8950cc72e5454b109bd89534832f5414930b318d210867b6550040d314d4248678654c1108fd9150cc76752d45309bd89544836852d0140cb54b411026e6215231d594e51102e86050832c758c544c36952540319b58a544c67661150219b98a544c6746550510ab58b43d06d56390431d58c8514ca5d6315010d9185520c6ac6250040b318d21082b561108409ed95300c26d62d53108fd9152442e4614cb219e59610042776154c209758c548825d6315020d314d324876652547439b588548c23f65508428f990540866d65d0820d314a314c74d6214d219b98a51042cc63486208f593530874d53948409b58b53c42ad62d0d419d58654ccb3661950319d584544832c52901409b98b53842e86050b20cd98454482776544010ce153204836651486209b195424832e5450b329d984548cb655254440cb55321086776154d109b58a544ca3e6414c20c7152434c26e62150219798c540827860551219e580540cb665294440d554c310436552504319d984540823c6454321ae18142d066f6254e4197d95310c63e65151208fd9153442e86050b32b9185324872d52504409b195324876652947439d987538833661953109b58b540c63e6414e21d9d48514c23f6550c43cb54b411063e6414f10ad584429026e65909209e983548863d6414c109718d544877160145309b588540426e6214c109dd855390a6f6548020f18c831c873742544429bd89544c67960d50318f990530435553944408f590520426f6254341cb54a421023e64d4f108f990520426e62145439e980538866e62946409e98053042776154d219e980530865f654c0309ed81544867965100209d594310426d62946309d586544cb6552504419b988548c32d5448421da54a500c6b96010c40d514f214865e6395121ba189401034d528c8319e181544ca7a6015031cb153524c23f64540329e98354cca6c6550921ae181425074e53548409b58853c427661951309798c540c23c6454331cb549411065f6355110cb552520c75653544409b996324873554484219d98654cca7661151209e580540c7686054840ae191200823d64d4b109b98854c426d650c820d9949511026c625434197d8d54487655250710cb952520c66e62d5310f10c8310873a4214142b3189310c63d64d4f109e980540ca6d6294640cd99
  | 2 => 0x480300c4cc40003014041f84400004d004082e02b5c0000020a00a0d1b0080e26038a00000000384405108080a090183c0c000055804290001800150026c2c021ba041a09000042c0800310000000000002a0a000020001818000402800060002818000b01800001a020241a0500018000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x2200000920004000200000030002508120001511c5530c820a4ae22a28490644639452188292ba0c2a9063581c14254442a60e0a12a2214c47258e410c78229a84a0a43c1550320c421c90a63028490e155418d2108712b12c22a2419114c614c921a4ae32a285994a8725834110254392c0218812a1d1600c820c54a830285995447254c3104252ba0c299243681c14250521c1aa831a4210d257494521883142a0c0a1241685c44210020
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x2000000808a21819506050b32d00531c14250521c057418e5148620a21811506050920c057414c614c921
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
  | 5 => 2*((h/226+packedAt s5K5 (16632+(h % 226)*10) 10) % 616)
  | 4 => 2*((h/173+packedAt s5K4 (15732+(h % 173)*9) 9) % 414)
  | 3 => 2*((h/29+packedAt s5K3 (1225+(h % 29)*5) 5) % 25)
  | 2 => 2*((h/15+packedAt s5K2 (300+(h % 15)*3) 3) % 5)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffffffc07ff0fc1f0f0fffffff0fc0781ff3e7
  | 1 => 0xf01f87ff83ffffe00ff1f0f01ff1fffc64cc7f
  | 2 => 0xffe007fffc00fffff001ff001ffe007f870f87
  | 3 => 0x7ffffff07fffffe00001fffff87f80ff8
  | 4 => 0xfffff800000007ffffffffffe0000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x114500470821100303023111cb0245080951e3
  | 1 => 0x24c24c89194844a08590d8a24590935424c42d
  | 2 => 0x428b551230eaa56d90816a8496a40a65870e86
  | 3 => 0xb142224428032562a24000918492c02d80b50
  | 4 => 0x8c184438630cc798ccc98cce0080304776a000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeaaec80feaaec80feaaec80feaaec80feaaec80feaaec80feaaec80feaaec80feaaec80feaaec80feaaec80feaaec80feaaec80feaaec80feaaec80feaaec80, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_38837
namespace PEqualNP.Outside.L_meta_38837
open PEqualNP.Outside.L_meta_38837.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x68c800010074010100002a24310d0400029c414a0800401830a0017f90c07ff41027f55003fe21027fd4801fd3201ffd00017e52027f54009fd53007f4c009fe50005f54c05ff3001ffd0801fd31017f0c001fe42027f14007fe54007f8c001fe20027fd4001fe40007fc8409fd51007f50401fe1001ff10009ff5300ff0c401fe32007f48005ff32017f94c05fc32017fcc401fd10025fd4c07ff43017f14c05fc4300ff10401fd43007fc8003ff10007f08009fd52027f14803fc5101ff150097c5200ff94403fc10027fd5001fd40007f50809ff5101ff10801fd2100ff08403fe41027f94803fe31
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x1c4040df1025202ffac3100dfff658c80bf79004026ffcc64001df8c88804ffe6448001fea1c2005ff8c21002ff820880b7fd52c8407ff20a8620ff1523002ffac710043ff65c8061ff29a8203ff1514301ffe8521007fe5148407ff20a8005ffd0020087faa39000afe63500077f3222000bf58f2000ff8a30800bdf328c833fe30e4005ff9002002ff8cb1800bfd534c443ffa8c602eff15131025f8ca880d3ff514c80bff1826014ff94920025f8caa1812fe655080bfe2804018ff54e2000fe882a0812fc655040bfeb148009ff14e1002df8c50810bfe6550c01ff3128020ffd0a3007ef8a41000b7d534c80bf79044005fe8c210017fea7180027d6588063ff282823fdf90e52017fea6a1802ff644c07fbe21ca442ffd4943005fcc51802ffd528406fffaa4641cff145301a7faa099003bc644c073ff29a8400ffd8232017f862990037e5248401feb264205ff1864003ffca8880037f6154c01ff90c4000ff4c91002ffccb08007ff4144001ff3024203ffd094308ff84290003fe32480017fb226434ffd95321bffacb1907bff654c0077f324200cfed002000ffa6390803fd604c40b7e3204001ff8c721007fac690093fd5350001bea9a8000ffd8132197f842990dbff418c807fea128200ffd8321137fca7200d7fc108c847fe1928000bfd932101ffe80a08d3ff504c851ff21a421eff54930007f8c4a0816ff6284001bea9c8427ff14a4008ffe2090067fe51c8081be214a400efd9120007e8c2990027f654c80bfeb2c8002ff0c93102dfcc120003fc6250c03fa10a4224ffd9540097f8c6900d3fd514c829bfa9a403dff54242005fac321003ff618c881bfa1ca40fffd4c2000ffc8298802ff6050429fea8a4043df88553015fec8a18037d6194869ff2926401ff4c610007fe42a0017fd508c047fe31a8005ff1962000ffc630803ffd5308061ff992823bff0c642017fea698807ff31c84097f32c8400ff9091014ff8849080bfc318c073ff9928400ff58143187f8c6a085bfc3288003fe20e4200ff58f20177fe849880bfe324c8017eb22403dff5964200fec439080bfd314c05fffa926229ffd0d2101f7880a08ff7f309480bf7102403dffd4242017fc629800b7d5350c01bf2964000ff581320bff8a910007fe2144001f71964203ff1514002ffc4108023fd544400bff282401cff1053002ffa8108016ff658c007dfa1a8201ff0c5310affc831000b7d538c085fea828605fd04110007fe4210017fc40c80097f32c4018ffd4a201effca521007fc418400bff31c2002fb0ca32005fec88803bfc3208001fea026004bf195300a7fcca90002fd644c40bfe9844000bfd854302ffac8100d3fd654c805fe18a8605ff8c1100d7fc8790006fd61c8401fea1a2004bf1952001ffa8320006fe614c80dfe29a2005ff18e20
  | 1 => 0x3fd304800bfeb0c6000df18252007fec88800ffd549000bff204602affd41211e7fcc721017fd20840037eb0c2034ff1953211ffca6a001fff4344005df21a8611ff9052003ff884880f7fc5090855ff32a4203ffd014309ff8a890017fd648c0557eb2a4202ff90e32007fcc498007ff41c8401fea0c4005ff98e4001dfcc99080efe644800bfe0842028ffcc121005fac9900fb7c2194807fea1c8005ff18a30087fccb9010b7c5250c01f7216403dff54e4201ffa82a0003ff614c055ff2924201bd1853218ffccaa0803fd424c401ffb12602cff953211f6fe212909bfc539000dfe21a2002dfcc15300dfcc3190e3fe315080bfe08260049f1953201dfcc810003ff63c845ffeb2a620eff94c2000ffe8308003fe424c0317eb2c4001bfd8110007fec0988e3fc6150821fea864005bf192300d7fcc790097fc5190001bea9e4000ffc81101b7fca91900aff634c827ffa124014ffd4d20046f8ca88017fc508c005be182a605ff0c110217f8a0a18f6ff6590807efa1a8600ff8c921007fa851000a7f6354c05fe192640aff95210037fe6088017f810840017fb128205ff19210007fa82100037d6394807fea128032ff1853200dfcc321017ff6408005ff9926200ff4ca1010ffea518003fd64c8005fea9a8610ffd43201d7f8a4a1003fd639084ffea948036ff10a32197fc8299016ff65080037f3164202ffd0e320effca89800bfd324c003ff10e4202ffcc53019ff8a899017fe405000bfe324402effd013101ff882a1002bf64480757eb2a8400ff90b21017fa869800bdc4350c55bfa9a4202ff54e30007fa84100d2fd654c83bffa0a6039ffcc542006feca908037e6254c29ffa8a4002bf18d10005fac690017fe4088053fe2024200ff5814101ff680a005bff3288021ff2964001ffc41211fef8c729097fe3190003fea8a4200ff4c640004feca90817fc618c073fe31a843cff0ca421a7fea49900bbc4350c5bfeaa64205ff19420017be60a18c7fc5250401f72124000ff58f2102fbe6118003fb6050857fe31e422fdf14931007fcc1908a3fc6348467ff3226400ff90a1016dfacb9080bff534c807ffa028003ff9064219ffe8499017ff4088087be082a608bf5951001ff8a921003fc624400bde2028019ff0872000df8c3900abfe5048401ff1964000ffc863002ff8a11000bff308c801fea1e420effcc82002ff8c7200037d5348031be2944001ff88610017de6519023ff544403dfeaa26000bfd9232017f86119073fe214c001fe3126004bf9952000ff02088017fc5050049be292800bff5521008ff8629000efe648c801fe902202fff141310fffc83180136e629480bff2864002ff0ca30005fec89880bfc534c005fe1928605ff994200a7fea0900f7ff53908057e31a4005ffd8c201effea521067ff10c800b7fb
  | 2 => 0x4203ff8c888002f86050875fe2828405bfd8510087faa790002fd6384001fea126405ff0c21000ffa43080afff30c840bff31c402bff10f2102df8cb1000afe628c8037f30a6004bf9964009ffe80900537c524800fff322200aff10a1014ff8a89087bfc654c001ffb246400bf58d101aff8431902bff438402bfe20c4000ff4c420016fea719006ff6450411fe32a2037ff54632157feca9080ffc41500077f3226402ffd0d30007fa429800ffd5450467ffa02640dff8c420017fca718027fc4384003fe10a4201ff9451002ff8a09005bff318807dbe30ca405ff5921002df8cb1800efc644c05dfe3226236ff99232017fca6a180ffd435040bffb2c2002bf18d40157fea490817fe2008001feb128200ffc8720017fe6499077fc424c057fe29e4202ff10d3006ff8821000efe644c047ff98a8000ff9813117ff8ca98812fe6548453ffa12422bff0c321007fa8318007fe215045bfe32e4205bf18e2001ffc84a10abff534846fff284643dffd464202df8c0a08d7de318c80bfea00401aff0cb20015f8c690803fd32900017fb026405bf1964001ff8832000eff6250801fb90a4205ff59630007fec6a0007be41504557fb2a4200ff4cb21025fcca88003ed3248489be202a602ffcc1300cffc8390016ff648400bff904201bff15320007fa851800bff328c00bff984202fff1493101ffaa8a1003ff61480017eb046402ff10e32007fac2a1002fd628c029fea9a4000df9491018dfecaa0817fc404401dff988403adf195421f6f8632900fff41900017fb0a801effd51301e7fe65210c3fc5350401fe9864010bfd9720086fea7900d37c524c86bff28c6402df90d53016f886a980fef42508017f3142031ff5494102ff44010053fd5048001feb0a8003ff50d421cffcc6a1097fe2190085ffa8a8600bf1894302ffac9100037f6094807dfa0a8618ff14a200a7fea4900ebfd525080bfe1826000bf58a10087fea59003efd6508003fe20a8234bfd9532127f8a4a00037e6054c07fba0a8201ff14721025fccb1906fff42c805bffaa64201ffd4521007fe42900d3fc504c80dff21a2010ffd4720007fec121016ff6488005fb98a6210ffd4f2007ff8a410007ff3150455fea824221df14a3001ffe8121017fc630807b7eb2c8401ff50531005fac89800bfe534c473fe29a8401fb8852111ffe64a00037f6054c05fd9826002ffcc94302ffec9180037f649480b7f3046403ff90a4001fd885210037d534847bbe2948400dfd9153097f86490007fc10c84097f32e4044df1095321efcc2a9807fd2144003fe18a4200dfd954202ffe81180dbfc408c801de3224000ff9814305ffea90800bf8304c00bfe32c2000df94a32017faa699067fc31c8003ff18a8202dfd0d53187fcc6a085bfe5388001ffb126202bf98f20157faca9080
  | 3 => 0xe9904003bfd81401effecb21003fe4288001fea164000df589531bffea31900bfe318c0013fb2a2000ff58d4200dfcc3200a7ff40484077f3224203ffd5141005fac7100f3fc639080bfb0822018ff55220017fa8698807fb1084001ff304642fff54931005fac31804bfe6348003fb20a2005bfd9140007fa43200ff7c329480bff2826003ff106421cff860a1023ff5044005ff18a8641ff98543156f8a49080ffd4350055fea9a4200ff189311e7fe6321003ff6190807feaa28003ef102421d7faa6a104bfe53480037e30a6037ff54232005fac918057fe2188001ff2104000ff505201a7f8a499007fc514c40bff324601fff1063000ffc8290807fc10504077e3264008ff9491002ffc6110017fc6284075fe32a8400bfd8d1000ffca30800fff4390035ff9964022ff88540007fa871008bfc6150001ffb226005bfd8c20017f8a698817fd408c045fe28a8005bf18142007f8c1210bfff654c455fe2824238ff8854200ffe629890f7c2154c05bea9c64049f196321a6f8ca9900ffc4390001fe312801cff94530005fac31000afe6390805ff29a642cff10321006fca590857fc5188007fe20a862bff90f21017f8631903ffd540800bff9848005ffd8a1001f7e84a08d7fe618c8057e31e4002ffcc543017fe6318017fe6484021be2964000ff8c91000ff8a2a085bfc5388085feb2a8638ff04142005fec990003fd4308047fe29a801bff19320015fcc79086fff40c8007ffaa28400ef5064000ff882988037c6254c0bfe184800dff88420005fec2900dfff508c80bfe2864005ff8c02002ffca0880effc619081dfe2984040df99252037f8c688003ff64c840bff30c4018ff54a20007fa8490002ff615080bfe2042005fdc42101eff8a521002fd61900057e31c8401ffc4110006fca50810f7f1054c49fea92803affd9542017fc86980237f534400bfe0848001bfd85211f6fc8329003ff625006fff2946401ff0851002ffec318007ff41504057f31a200dff1442002ff88098007fe314c435fe31e4000df9493000ffaa28800ffe5450463feb2a8200ffd8d2101d78c89006ffb40c803d7eb2a6005bf18630156f8ca90807ff214840bffb2c8024bfd9540007fa64a08e3fc5150813ff21c2000bfd8910024f8ca90817fd6308001ffb028405efd0240007fa63100f7fc6590801feb12622cffd0f2102ffcc91004bff3248007ffa0a8408ff59510005fec690803ff64c8059fe216420fff54820006fac9290037e609480bff32c6003ffd5240015fac718087fc528c00bff2024042ff149430affc6310012fc654c801fe98a8003ff9524000fb862988a3fc3248445ff18a8040dfd0a52007fac1190f3fe5390807ff2128201bf185321affe2119002fd640800bfea044003bf19321007fac190807fb10440017eb1c8403ff951
  | 4 => 0x2fd624405bffa864200ffd854301ff880a1017fd5084003fb8828241ff8854320ff8c2a1806fc6150c0dfe1922027bf596400f7fea298003fd61c8005be18aa642ffd9543006fec7290127e6294803ff20a2005ff0c020197f8a299007fc104c401fe98a401eff5413001ffc86a080ffd5490805fe18a6001ff0c61008ffc6290017fe509000bff0822028ffcc921197f8829900b7d534c001ff214602dff94b21017f8a699003ff6448431ffaa44000ff5913003ff8a888003fd304403dffa826000bf5922002ffecb100b6ff65c8407f7a148428ff94d21025fcca100037e5250807fe21a8205ffd42101dff8a3210c3ff3050407ffaa28000ff58d4101ffa872100bfc538c00bff1024002ff4c6301a7faa499002ff6448405fe1946400ff58532007b8c69080afe634800bfe3084000ff50120047fea488043fc52c8001eea1a6001bf18632007fc65909137f4254c4bff28c8001ff50521007f8c0a1803f9304400bdf2028000df94a4010ffaa91802ffe528400bfe0828002b718d2102ff88120016fc638400bfe0844011ff1052001ffaa8a1823fe654400b7e30c8008ffd4d1001ffc86a1003fd605086fff32c640bbf596101fefe652900bfd438c017bfa9c2007ffd09101bef8cb190f3fc5390825ff98a403fdf98e5201ff884a080fff435041fffaa0401fff88630007fa651007bfe524c003ffa0a6205df99620157f8ca908f7fd529086bff20c6441ff145430a7f8a490003fe328400bfe9004002ff4c931017fc62990b77f53c84437eb2c6000ff98931025f8cb21007ff10c840bef1826001ff087210d7fca790003fc604c403ff28e4236ff15232007fa8490803ff6350407dfa148400ff58d10025f8ca90807fd51c8403ffa8a2039ffcc14201ffe86a1003fd41c8001ef1926417ffd062001ff886a10ebfe655082fff2a44005ff040200fff8a3181037f4094805ff1926003ffd054000ff84308033fe5408007fe2128403ff10a4002ffcc210007f431c8407ff2a28002bfd893216ffacb9080efd649080b7fb20402eff99131017f8a6a18dbff428c80b7e3284000bf18941025fccb908dfff528c801fe992802dff94321007fac4980befd654c443fea946024ff59540217faa4a1803fe424c4017fb026201ff5461001df8c919017ff108405fff32a6204bf99530047faa088002bf644c0097e32c6400bf5863202ff0812000bff314c805ffa9c643bff8c642187f860a0802ff624c407ff2128005ff9032002df8c910002fe6290039fe10a6022ff9854001ffc8720002fd639003dfea8a6002dfd4d3002ffca108016ff648c001ffb1a8401ff885310e7fe20980bffd544c403fe18a2029ff991211c7fcc2a10fb7c4194801feb0a4000df54d100077a84a0803fc60c847fbe184a40cffd0420015f8c6a0817fd6108001f
  | 5 => 0x8610087facb900a3fe6348489bf322a605ff5424002ff86118007fd51504057f31a8200dfd9510017f860a18037d5390001feb0c6401ffc414116ffea59080ffe435004bfe18c8001ff4c52101ff080a005bfc438800bee1826016ff90e20007fcc1210c77f5350411be2922000bf5932101f7e8320003ff634800bfe3204009ff0ca1005ffea508002ff625000bff32c4003ffd52420d7f8a790017fd6384069ff32a6437df14a32006fca41001fff4044021fea964000ff58d21007fc8499002ff60508037fb1a623aff59542017fe8698803ff6344001fbb0a6400ffd8143005fcc488003fe4248075fea8a8400ff5894002ffc80880dffc658c875bfa9a8401ff90610007fa819004bfc5348001fe90c400aff1521008ffcc290017fc504406dfe3246405fe0c23000ff88290806fe6150c29feaa2403bff04242167fe85908cffe544c801fe90a8002bf98e2000df8c2a1017ff509000bfe984200eff90c20005fac6908e3fc2150801f69964202ffcca3202dfcc0100cfff414c801faa0a201dff151300077c852000bff304c44fff2948005fe10020007f26108077fc644c02fffa1c4017ff10a2010ffea918047fe2148007ffaa28638ff9454201dfac92000efe648c029fea924000ff1813201ff884a0012fe6550449ff32a8002ff50d3218ff8caa0807ff31484057f31c2004df98a5202ff8211800bec324c80bff1824036ffd0232007fa8690003fd31c8007fe21a800bffd4e10057fe8508017ff6484033ff18e402aff14921017b86499007fe5150401bfb0ca41effd4930007fa4210002fd6290001ffb0e401dffd0930007f24010006ff614c483fe0828614ff595201d7fca0a11137c6454c19ffa184005ff98630017f8609880ffe5490805ffa9a6027ff5464002ffcc508002fb6050807ffa0c8405bfd8e1002ffe611008fff3050023fe28a400cff10820047faa688016fe608800dff31a2000ff58242015f8c6a1003ff64480017fb1a8000ff1823200ffea39080b7f6354c017eb222002bf98d2102ffcc610093fc655000bff9044000dfd95201dffc4321012fc654c401ff3128205ff0c22002df8c610097fc2190003f610a4200ff58530177fca898822ff6544001ffb028242bf59543007fec488002fd61c8003de20a8234ff55132006fca4a08b7fd50c841dfe2184000df54f210cff8839000efc644c46ffe2846405ff0c14002ffac50806bff31c8041ff2a460009f18953197fc4299007fc31c8489bfa0aa642bfd954300ffe428800b7c3254c4fbfa9c8002ff4ca3001ffca8a190f7e4154c07fe2028205ffc424000ffea30800fff4150c0bff9804020ffd063000df8c321007ee21c8401feb024200dfd895302ff8c310012fe658c005fea9c6400df54e10025fccaa190bfc6550c5fffaa26200ffd8943007f64110
  | 6 => 0x7fe3224009ffcca10127faa2a000ffe43908637eb2a8200efd913016ef8a59080afd638c805f79926400bfd8f2100dfec2a0807f4314c449bfa9a8022ff0854014ff8c8908037d43948497eb2a8005ff102300c7faa310016fc604c47dbf10ca400ff50d2105ef8a50800bff304c87fbf98ca403bfd9142226fe80a9803ff6048403ef18a620fdfd4c2007ffaa21000bff438c005ff9926000fec8120007fac4a1807fe2148401efb1a4205ff59420007f8c090817fe5050007fe21c8405ffcc23002ffe8108017fe6590005fe21a6400bf58242017bc8698053ff54480016fb1a4200bfd8121005fec69000ffc549004dfe1948001ffd454102df8c090837fc2108057ff31e4200ffd853216ff8a190817fe50880037f30a8005ffd963001ffe8721002fc624c00dff29a2001bf98630017fc86a180bfe438c001feb224204bf9953102ffc8108007fe514c463fea82821bff9532002ffe2010003ff644c46ffe2946403ff9064001dfcc8988abfd5448401bea9a8200ff9814201ff88521017ff6508039fe30a6000ff4cb2000dfcc29000bfb308c0097f32a6403bf99320197f82099052fd65480013fb2a8400ff90b2002ffc8098007fd4144003fe18a822cff1932102ffec710016fc6050c05fe1826438ff0c5420f6f8a49800bfc4350c47ff31a8000ff5854319ff8c8990c7ff505040bfe2842034ffd51321d7fea2a1003fd218c0057f31c8022ff94540017f88718002fd644844fffa948015ff9462016ffaa7908127c655080bff2804005bf9832106ffca210003fd644c4097e32e4002ffd0d430a7feca90017fc504c007dfa0a8402bf18f2100df8c2a0006ff624840bfe0824027ffd4e40107f885180037d609480b7fb1a6000df54d42015fcc6a1003fe3290007ffa1480009fd9632006fca498817ff6190003fe28a4203ff109430dffcc9900c7fe525045dfe2126210bf59720017fca719002fc624c479ff9848403ffd0d40005fac91900ebc644c001fea1e4000ff5091002ffec21000bfe434c451fe29a423edf8c652005f8c4a00537c654800bffb148000ef9094202ff8cb200f3fc309080bff9004000bfd912005ffaa7080abfd5248401fe9924000ffd89410077a86a0843fd54c805f7fb2a6227ffd46401d7fea0a1077fe644c05bffa9e4205bf18e401c7fe20a1017ff6188059ff3264205ff8c32002ff88110002fd63c84017eb184010ff19720006fac0a98177d6588001ff1928213ffd05200f7faca98073fe414c027ff2a24005ff10140006fca51000bfd534c033fe28e402bff0cb210cffc4390006fe6188001bf29280009fd95200f5feca98012fe658400dff992203aff94942167f8a990807fe3148403ff20e421cff98530007fe429800bff3050c03fe10a8202ff0c930017f88698817fc40080077f3244001ffc
  | 7 => 0x210c7fd535040bff3148003bf191320cffcc39006ffc42c807bfea8c8401bf1852002ffec91000bfd438c819ffa104000ff50a32024f8ca880d7fc418c81fff2904000bf5832105ff8a508002fd644c80bfe2024000ff50b210dffe8790012fc655080b7f304601eff14930006fca49000b7d534c40bffb1c8002df8c553137fe6520012fc65c8401ffb1c8421ff5463002ffac720017ff108c007de2128401ff4c51002df8c310003fe604c8077e322402bff94f21197fca2990d7fc518c8013eb1ca43dff942421bffaa5190fb7c1094801f6a164005ff542200d7f88790007fe3144001ff3122005ff1923020ffe20a18bbfc404c40b7fb2c8003ef10a40006faa7100bfff504c405bfa9c6000ffd8542016fea6a187ffc218c00b7e3084041ff085430a5fac51004bfe4348027fe212403bff94642017fc649890bfd5150c03fea0e4203ff1024200ffc82a0817fe508c001bfb2a6424ff5414002ffe812000efc6448407ffa128200ff5011021ef882a9827fe538402bfe18c4037bfd9632187f864a08abff544840bff1022005ffd4220007fac89006bff30c8001feb1a8022ff0c54002ff8c708003fe6250c017e312200fffd442013ef8a5200bffe524c40bff30c8005ff98a30007f8c0a109bbe4390067fe2026400df54c2002ff86190002ff63c8085ff2828602dfcc55300ff8209080bfe534c049ffa828000ff485200a7f8ca90002ff624c003fe20a202dff99721007f8c0a0807fd418406f7eb2c6400df59153206fe8329017fd658800bfea804000ffd9132127fca4a0017fd6584003ff98a2001ffc4131006fca51800ffc5450483ff28a8605ff142401d5fecaa1017fd628c007fe2028602ff8c632117fe20a0037fc3108021ffaa64018ff94a2001ff68120023ff6544027ffa1a402cffd0321007fe4320003fd414c025fe21a4005ff0811002ffec51800b7f3254c01fe9924202ff90d320a5feca90017fe640807bff32c841bffd0720007fc64a0002ff614c00b7f3042000df5855302df8c099007fd514c43fff28c6003ff15142007fa8498017ff5008063ffa928201bf98420007da8490017fd619003bffa026000ff5911000ff84298803fe3288001bf2948400ff50a1001ffe84a107bfe654c057ff9964205bfd9620007fc8490847fc6148063ffa9a8205bf98242016fea6988d7fc618c831bfa9c402fff9413113ffaa720003fe6050401ff1904002f70c6321f6fcc329006fe6150853ff2a24200ff58642007fec790002f7614c8093e32a4012ffcc12002ff82190002fd6108001f71924205bf19610197fcc2990c7ff6550401ff902403affd4d4200ffe8290803fd6244067fe2126402ffd0d32017fe6319057fc218800b7e324203affd494201f7887200127e658800bfe1824005ffc4220047f8a488003fd644c82
  | 8 => 0xa8160044fc01dbc0100400f8000143a4b88250060000106307801803001002b203661022c0000000100a004018350980080300005a1841c8c4062024140260402d00780702200406812158460099630021980001500800c1d031000088048001ca00c4389f046090060010000640b82208a03c0000101c06802012010000050030d40480e00100600409000056758000067d40100302700c2e00347d0000300446902a0745b80001a5b00b8040140100d8080000440301901c070000000360700884c2060200306301601c028020000000000400e1c80205e00032c1900703c0940680007000c0a8190000c8368000480940480200402c2f83401204c110030020143f804084010000000020201e0000e80040b8160ec1480000600c0105b00106a0100f0e50ba008000020000280000d000028200200520500001e0000580f80c006000278770740401786000c05c040000000d80588b0b404c048130080002301b00e078000080020040680000eba80701e00e018028520760fc0602d00001800021b1c000028060020085c802052000108040160d40000005001c240080000281381e09a0000380600015c0081100200c038350040ec6483a026034000020d01b4078040023580000403c090078040021f8028000000000200002823800a0a20c0b48e80b094080118000fc0140b8080277c0160000021484ba0b0080884480100c000080000291d0f1800000024070070040380204a00e000040a318a0782d0000062c80280001c0003601a00e201ba8001020242e9020360041000d000dc00c8360fa09c2a02801c3000a02c000000028200080800b00100001c080180000602200700c0000b8100080e40898507c14c1281a000be40b8000000c41b0000440b4110622ca0700600600e09c01889000000037f30e4031df1494100ffe6308012fe6550077ff30c8417ffd0a2002ffea118002ff6050c0bf69004002bfd8d43016fea69900ffd4290049ffa928005ff08210217fea0a1802ff6250c65ff8826404d7d8d530dff08190007ec21c8423ff28a402dffd972101dfcc521037fe4108001ff2146402bf98c2000ff8a288002fd6484031ffa8c4018ffd4e20067f8a810093ff5350081be324a424ffd454001ffe80a10a3fc4348405ff1946039ff0c94201ffe84a010bfe5250c0b7fb2c2031ff14141085fcc410087fe528c001be302a600ffd8540007f460880b7fc52c8407ff20a8405ff4c020007f0c0a1017ff6384051fe1824237ff55232006fecb1900fec425080bfe3148034ff941321affc43190eb7c5250801fe90e4000df94932005fec6a0823fd5244001feb24642bfdcc721005fec6a10efff10908017fb0a642fff5413107ffea410012fc6550087be30aa602bfd81301d7faa0a10f77f5390803ffa8a6202ff14e321dff843
  | 9 => 0xdc4280200e0280100981f00c060009510017000b0070015180115f010014008780021cc098070261a00381400401800001088078080130b436c049140000b800000042278008a40000a81904208a00c0185100001c0086e000000000007a803808857000000e70d70ac0140080f0bc0000e00200c0000000100c0a80000104a01c5d008832000078000020e8020000e41bc0280a01e0940003004000c010230ac0101a0700060000480810c0200504e02c1d002801000020090171380040b1150361340000928e00c0004404e000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe43d96320067d74d95202573f4094a40006be52d9130004fd75d89401fe7f63949320057f75586320067d75d893035e7f6318953006f675d8532004ff755913115f773154f21005bf744c110024fc75d853256f3f43d915301cfe7458f210167e6354e422567c7694820267784054e400067d7654d1050f7930d81532267e6454f21006dd50d8d21006f821181420367f5358630024fe75d8d410067f62949100067f6558d201873f4354d412667e6054f210dcff7650820004ff75d9121024fe75586201fd7e7398252007b542505100067c659813236fbb30191300067c5258630024fc75d8f200075e528c9320067a52181420e4ff7158d102c7e95248020016f8638c1100067d6494920024fe75d911002cfc7098a101aef46158632005bf7458132004fc7650d210167c6354e20004ff75d8930066fa41181420067f65c85202576e20d95200067c65d85323deed32d893115e7553d85322057c7458e52005f7714cb20006be53d912002ff3618c1101fd7d739493002cfc7690a100dfeb4050b20024fc75d8d41004fd74d8f210067f6494921166bc64c852009dbc744c1200067c65d8d20006bc6458d200acfe76c85200057f75585321567c65485200079d43505301fe7e63949400067c525913224f7465505101fd7e73586520076f7550b202667c7654e20004fe7650d200247c75591210057f758ca40004fd71d81320057d7418153004ff7650d10004ff7558632006f970d8f200067e525864228e7d70d951000cfc71592201fe7e31d96320967f5358d2015fe7318cb21004fd7598a40006dc70d8d210063f651912005d7c7550a102057e74d8e5200cfc7158232006bf6490910004ff71582423af3c5250640004fb764802015ef432d853201eec64909200067c52d8930014fd74d85430047d73d95421aede618c932006be71d91200067d72d95101476f538c9211ff5c3194a320067c40d95212077b4094a40006bd51d91300167e6354c2017e7c654c520007b543505100067c5258a1014ebf4258642016dc634c12015fd432d853226d7f7354f21004ff7258d1002fea6248020006ed6290a3028e7c41d9510024fe75d85400367f5358d100067c7158e520067c7558a3037efa30d8143006f7715913102e7c40596201ef5f7354e4202ebe40592200067f63949200076c72581530057d75d894102dde7050d3002cfd7058420006bf644c1201fd7f7394a3002cfc7258f2016e7e62d8652004fe76c8530246be405911047eee42d8941006bf6450520014fc7398a1044cff7359131006dd54d8d2101cfe7458321004ff75d89430067d53d81212067e6459252005ef7259110004ff75591102157e75181431c6f461509322657c741815300cfe7158a3001cfe74d8d10006bf54d913000cfe71592301f57e71182523076c7550920
  | 1 => 0x4a32004ec72591102676f2054c20006f465d85320a57c7558d20004fd71d81422567c70d9520005f87050b21004ff75d89310857e72182521276e72949402067c72d9542116f641d8540006be61d913004fda434c2100067e74d9632006f552d85320057e7654d4202ef87118142007e97090b20006bf75d913000cfc7159130006bf745932000cfc71d89300067f62949403c77753c85212273e64d9153004fd7650f210067f6550d210075c6518d210067852d814201cfc74d8f20024fe7558720004ff7558e2000cfe71d8f2000ff36050510004fd764863021e7c6154d200067f30d95200057f75509100057f758c921007d463c8521006fb52d8142015df7450d30006bf64d8530006f87059121014fe73d8141004fc7650d20024fc7558e42024fc75d89314277553185320076f7254c20005f870585420047d75d85430057d72d81533076c52509200067f7654d100067d6550e201fe7c6394b20006bf7459121014fe72d8d20006bf6450921004ff7598a30015de728c9321a67e72d95322076c4294a42004fd72d91311be7c658c9100067c65d8910146dc43d8d2113d7c754ca400067f4259620005df73486200047d73d95100057f71589532073c4294a400067f7058e5202eef2059220006ec52d894002ef410586400067e73d95101f57c71d8e5221e7e6154d400057f75484201ce7f535913200cfe71d81422576c20d95200067f65d8d100067f6518132007e942c81200defa41d814202cfc7058620005f870591320067f65d91321be7c658c92002e7c20596201ff6c32d95320057f7548620096ed3258a300067c65591200067d6458252004fd75d9132006f642d8532197b6741853201cbc7458d202677a30181530dfaf4150b20197b57418532006f851181420067f5358a100077953d81420047f7558a40004fd76c853041f6c754cb2102fdb734c210004fd76486400067c41d95322067d72d95424a4fe72d9232004ff7058e421fd7f7394931004ff7458910317ac2019120005fb704ca201557e7598121196f43158f210247c75d8d20006bc71d912021e7c61585531f7746158652006ef7259132024fe7558a100057d73949400067f7558640005df73589411f67c6194a321aedd71d8d210057d7498953005f7715813202df976c82200067e21d96320d4fd73d8f2011ede43d8d402257e74189532e7ac40909200b67f53d893002cf476505101fe7f72d95322667f6098153004fd72d854002ef610584201acde7618d210067f70d9632076ed32189303c77452c8521014fe73189100057d73949412073f4194a4002e7c10596203879f73d9130006f77158d21005bd74d8f2001cfc7458d1000cfc715913200cfd74d89410367f6354d100057d73d82520067f42d9521004df73591100067f735962015ede63d8f211fe7
  | 2 => 0x4ff7458232007b8744c2100267d7694a420057e7654d2102eec2058a30024fc7558a1002ef61058620007bb705094100cfe764811007f5f7354c20004fd75189402657f7654e20004ff7690a1001cfc74d8910014fc73d9120004fe764c940004ff70591211aedd51d8d210076c521893130f6c65909201363d53d9130004fd71d8f200067d71d9520006ef4218910005bf744c3200057c7254e20004fe765093001edc7650d30007776518532024fe75d85420247c751891035e7c4318953006de54d8d2102cfd72d9120005ef724c42001cff76501200067b53d814201cfc72d9120004fd7650d21024fe75d91200076f65509202577a209482036dbe76d913009ebc41d912002cfc7058a10024fc75d89414c73c65909422667e6054c2025d7e7694921004fd75d81310067e6294a1000dbc7650941004fd7518931136bc32d913021f7421d85531ce7f5359232024fc7598a100157e73d91530067f65591210067d6550a200067c30d952121e7e6154d421fd7f7394a321aede31586323e7cc2118d2109fac6450920146dc53d8d21006df54d8d211379c73d913001ebc645013011ddc735854008cff71589100067c625815300cfe7158242007b97090a400c76e7294a20006df634c120004ff735932001dbc744c6401aef4215863202e7c3059620496dd43d8d410247d73189530067d61581530067e61982520067d62189530067d75d8940006be43593202ad7e7294a10004fd7498a1002dec765092011ede63d8d40006bd70d9120004ff7559120194fd764c921006fb60982320057f7059153004fd73d89100057f73592522567c6094921004fd73989103076f5350920014fe76d8d40016ee634cb2101cfe76d91201467d53586320057f7650e522567c6194a4001eec6450b200067d6394a420067e73d954201cff76592320067c5218941197e4314cb211aedf71d8d210067e6198153024fe75d85320073f6454d2000cfe71d8d100067d6394a403cf6c754c9210067f65981212675e6354c20006df63981210067c74d95320075f758c93202cfd74189400067765d8532004fd7198a30005bd71909421fd7e73d825201cfc74586200dfb84090b200067f6318252005fb7050a305075f63181530047f7654e200067c525923201cff7650110006dc64d8d210067c65d812104ef531d853009eed4258a40004ff7558d100067c6118953004fe72d8d100defa40d81423879e30d9130007e93248020196f673d85322567e7694a30006f750d8532006f875d814200cbf76506400247c75d8d2135c7e72d963202cff7058a101f57e7158252006dc6518d21024fc75189300067f32d9520006bc75d91200067c65582323af3f5350640004fd71d8d4021d7e76d85530076e52909200057d72d91530067d7458e520067d53d85401fe7f769
  | 3 => 0xf53d91300073c74581531f67c61949401a67e6258e520ddfb70503200bcfe76909200057d75d8943067e84218142005ec72503200067f61d81534f56e72d92520067f53593210eebc645913002dee7090b200076c52189302667f6454c2002df476505100067c5258910014fd7258c2000dbe71509412557c7398252024fe7598a302567f6098252014fc7318910005f87058943007777154f21004ff76507200067f65d8d210067f7558d20005df73591102bfeb4248020004fd76c86400077865181421aede31d8f212667c6054d41006dc63581210067f755842000cfc7198a4019fac42509320047d73d9520004fd75d8530005bf74c864002cfe70d913202cff71189102667c7654e1002cfe7098a30006bf6490930006bf72d9130006bf53d91200057f7550b202e6be40d93200defa43d8142006de52d8d2102cfd7690b200076f7254d42005ef7650b202567f6394a1001cfc74d89312667e7654e102667f6254e1015fd73158f2108ef621d85200076d5350b20454ff74591310067d70d95320067c4158e52136bc31d913002cfe7059020004fd71189401fe7c63d8e52005f5718cb21004ff764c720006bf745891013d7c758ca4009cfd7690a20004fd70d85430067f6494910257771094a102567e10d952001cbe74d8f20006f575d8532004fd74d81211fe5c3258e5201cfe74587200047d73d95212267c6454d211fe7c6394a42005fb70509210067f64d81532557e70d8e52196f67618532006ec52189311e6dc3258e42024fc75d8121006bd52d9130004ff7259230006f440d85320065d73d9632006ee7218910146de63d8d210067c32d95420075f6394921006dd65d8d211ff4f3294a320247c7558d10006fb3218142006f95318142005ef7258131005ef72504201557c754c921006bd75d9120006bf75d91201f76e2194921004ff75d8d21014fe73593201f67c10d95214267f5318931007776158553006df7359131024fe7558910096fa30582322867e20d9510186dc30d8d4101fba60506400057f7558131014fe73d9320166bc40d93212267c6454f211c6f46158542006bd6490a32024fe75586400067f71d9520005fb7050931006bf6450b210067c74596200067c52593210067f7654d411d57c755814201fae72909420067c43d95100067c64d9521004fd7559130014fe73d91211f67e6294b21006fa21d81420067d73d95200067c71d96322267e64d9153185dc73581412b57f7354e100067f75591201afd431d8f211e4ff73d9132024fe7559220024fe7518940004fc7258e40004fc768c941007af74509200a57c75509200067f5318941006f9631814201ebc64505302657c70591530067c52d91302057e74586522067f74d95422867f71d951015df67618532006bc52d91200067c6598232006bd65d9120
  | 4 => 0x9120016bc7650d41016bc6350d410067e70d9632024fc7559220095dc73485201fe7f609493028f7641d951002cfe70d911016e7c65c85202cefa6248020004be7619120016ee638c921006dd73d92320d67d5398a300067d6294a10386bf64981431f77671949414ed7e72d8e52004fc7650720006bf745923200cfe76d853221d7e7159153005ec725911002df87050a1012df4714ca400067e525863001cfc7458910004ff7558e10004df73589100057c7254d100c57c75486201fe7c63949211867f6354d410067c64d95100067e7458e52014fc73d8141006bc645852001cfe7458a10006bc61d9120066ee421894002cfc70590200e7f2414c110006ed6250a3021e7d6154e1002efa60181411d57c75d8d420067e3159620005bf74585200247c7558632005f7714c8200165e6354e1004edc3258e1001cfc74189311f7742194921004fd75584200067c21d9632316be40189400067c75591214c73c52909420067d74596201fd7e7318252007ad4250720066f854181420067f5358910006ef72591211f67e31d952147eed42d89412067e42d95420247e75d89412067e6494a201f75e31949310d6ee3298a300067c75589100067d6394920024fc7559132014fc7318941004fc7650d100476e72949100067e61d915308df970989100067c6294931014fc73d91100067f7654e4002cfe76c86401475c6354d2106cff7648720197e4714cb210167e6354d21007757194941005fb7050a320076c72585531f67f10d9521006fb70591202253c74581531f67f61949210067f70d9521004fd7558242006ec52d8930196f410d8532006bd54d9120004fe72d8530006bf50d9130004fe76c854002efa73181420076e528c9211f77810949100f57c755893002e7f1059620066fb40590200067f655092102cfe70d8d210073e52506400067c65d9110006fa51d8142006fa65181420057f754ca20004fd72d8d411d57c75585420057d73d951002eee2098a101fe7c43d95322267c6454d10006de65d8d212557e70d9252006be611913021f764154d100067e52d813102cfc764ca40016dc638c9410067d63949102573e40949400067c7654d211f73e41949410076f654c921006f76148520006f47158d200057f754c9411fe7d72d9532024fe7558d1049f5c658c932006f742d85321ff3c4350e5200cfe71d81320167e6354d411c6f641d85420067c7558420007e8705092000cfc764c1100057d75181310067c31d954201dbe744c9412667c6154e20004ff75d8141004ff7650a101d75f7354d42004fd75586402076f42d954209ebe54d9120006be73d9120006bf65d9120006dc73589101aedd10d8d210247e76d952115e7f6354f2142f6c528cb21004ff73586400f57e75d89301fe7e6394b200257d73d8153006ef62509311367
  | 5 => 0x1f57c7150e521e4fd73d9132006fb6518142067e97218142007785218142006f55158630006df7358d2109dbe76d91200067e7418953067ac42508203779c301913000cfe76d8530006f542d853221d7e719895300df8714c2100067c6598121004ff75d8d102e6be20d91202157e75d89430d67d6354f20006ec624c940004fd70d8943006f450d853200df471501101ff5c31d96321aede71d8d210067c74d96320957f7354d20014fe7359220024fc75d8d4002cfe70d852015ef543d85320067c42d952001cfd73189434bf5e3194a320067e75d894109ebc43d91201fc7d73d953221f3c4154d410ef3d751913001cfc7458632476bc4018941004ff705863215ef663c85211f67e6194b20007f1418c11000fb77450510386be70d913002cfe70d91310067f659823201cfc7458232004ff7559220006f731586200057d71d81534a5ee72d92320a57c75585200057f75509320e6f421d85302567f63948200057f70586520067e61182521c6f621d85421fe7f62949320065f6354d210057c725855320cff7159131024fe7558e420267d7694a32024fe75989100065c75d8d210067e64d95320067f74d95322657e70d91531cedc31d8d42004fd7559132016cc634c921427e732185320047f7559232024fe75d894002cf870591320067f7694a1001cff725902035d7e7694a32005df73487202667c6154c20066bc4259020006fb65d8142004ff71592300067c6558d2001cfc765032002cfe768ca10016de634c420347784094b2004e7d53d85304ae7e7694932004fd70d91311f57e7158e5201ebe6450a200067c52d813201eac64909201fd7c73d92521557c758c9210457c75189100067f41d95200057f74582521fe7e73d9532007b77150941004fd72d8d401f7762194b21146de72d8d21006f46418532004ff7358720004ff7158e201fe7c6394941004fd75d853200ced768cb214e57e72d86520f57c75509300067f6598142024fc75d91310067d6494932014fe73586400075f73591530067f40d95201b6bc4059232005f87058d420067e6258553004fc725863028e7d10d951000cfe71d913027dfb70591100047d75d8941004ff75d932001cfe745863001dbc744ca40006bd6490b210a57e7294920095dc7358520004fd72d9130024fc7558630006f976c82202576d20948201afd6315863220ef641d8543006bf7459110136bd32d913021e7e61d8553016ec634cb21006f461981320ef9c6450d301aed763185320067f62949300066e2118953005bf74585300067f7558a301c4ff71591210e5f9738c1100067f65d813201ebc645011015f6f538cb210065d6354e10066bf41590200067c75586320057c7254d410067f65585201f67c7694b212073e64d92520067c6558d100c47e7694920006fa5318142006bd50d
  | 6 => 0x771591321557c7558d2145df7715913102cfd73d8530006ee72d8f2111edf30d8d40005bf74486400067d6454c20066fb41181420067d7694a10024fc7558a3000dfa714c110004ff75591302073c4094a420076e5250920356fa30d81312276f4254d42004fe76909100267e769482011ddc73485404b4ff7650a322567e6058252024fc7558d210067c32d9510004fd75d9232004fd7558f21006f821d8142094fd768ca200057f715825250e7f63d8153005bd7190a40006f861d814200cfe7158d2023778528c1101475d7518d21024fe75d8131024fe75d89310057c7254f20006bc61d91300067f43d9520006f670d85320067c73d9521007777154e100067d6494a320067f6218953006df75d8d2149f5c758c932004fc7258d1039c7e7694942006bf54d9120014fc7259232006f77158d100067e72d96320067c52583210077652c85210067c52d8d400d67e6254c20016de638c820386bc10d91300247e7558e20006bc53d9120004fd755923000cfc71d8d420edbc745853002efa74181422067c40d95420067c61d96321f76c219492101cfd769082000df4714c92154d7e76189530defb74d81421fe7c4358e520075f75d8d2102cfc764c62002ef97218142006fb71d8142024fc75d81321fd7e7218953004ff7650e200077b53181422b67f639815302eee2058a10006f56150420016de634c320006df7358f21006df63909210876e7294b200057f758cb210067a52d81421fe7f30d96320067f7558d1035e7c32189530057f754c9100eebf42d91302e7b84090820006ef62c8110004fe72d8d40476bf4218941004fe7650d100a67d20d952000cfd76c84200067f65d85420067f63d86521fe7c72d9532005fb70486200067c70189531ff5c3258e52024fe75591200067c5298a402567e7694a4002efb71181420047f7558a100157c731895317d7c755893117d7e75d893100cfc7158f20024fe7558e1015ef430d8532195f67198132007bb744c1102576e721825255d7f73591531a57e75981320075f6358e520076f758c9210457c7558d10006ee72d8f20006be71d913002de87050b200067f31d9520456bf41d9131004fd765091009ebf4158a40006bf65191302273c7454e40014fc7359020004ff75d8542005f7715092108cfd76c8620006bd72d91300e6f451d853002df8704ca200257d73d85531bf6e62d8e52014fd7690a320077b605815301cfe74d8132006ec32d89102076c4294942005ec724c6202667c7654c20005fb7058941014ff7658f21247b640505100057d71d8e5200cfe7158f20017ce728c9320fedd31d8d1002cfe70189410ccff76481101afc4318cb21006dd52d8d2109ebc4258a40004df7359121007e7714c921006fb5118142066bf435902002cfc7018910024fc75591300467e76d9510
  | 7 => 0x96200067f659091039d7e729494000cbc765094102cfd72d8d200067f71d954221f747154f210067d6494b2101fae7290a401fe7c32d95322667e7654e400057d75d89300067c52587201ff5c32d9532245bc7050d4102cfd74d8d4001ebc64501200c67e76949200057d749825219dbc7458132004fd7558a100047c7654d100073f645925201cbe76d91300067c525913002cfe7058e400067e4159620014ff764c120005bf74481100057c7254e42006de70d8d21007d9434c110004fd7558c20114fd7650110005fb70507200067d64189530067c655813221d7c71d91530067d7654d40014dc735911001cfd71d8941004ff7359020004fe72d85400057f7550820014fc73582420067c7558a1011d7f7354d400067c769493100ef6614c420024fc7518943004fd71d894001ebe6490b20006f96018242004fe7650f2128e7c31d95101f77b10949102073f4294a42004fd7018941066fb4318142004ff73591100067d71d96322667e605815355d7d74d91531fe7e6394a20196f710d8532004fd7598910024fe7598a1000cfe71d8143196f631d85320065c65d8d21005df735891000ef66150620006f96018143005ef72503200067d7654d4216d7c754cb21195ed738c9210057e72d915325d7e7294941006ef7259110006fa73d8142006df634c9210377b538c110006bc651913021f74615855329f78524c2100067c10d954202df870509202267e6454d201e67f6454d420067d5358a401acff7358d212057c74d825208ef461585200067c52d89430067c5259210004ff715823200df671c81100067f535832120cfd74d91310d67f53d813236f3d53191300067c6198153006f851d81421ef6e7294a420067e64d95100075e31d963202eef7258a100067c52d8141006bf71d91201ff5f3050e52006bc745891002cfd71d91101aef76318532014fe7358a1040cff7258d2118e7e6550620007d6321853211e7f53d8d401cebd43592322267c6454d200067f65181420067c52584200067f649493001cfd72590200067d53d852000cfe71d9320006df638c910004fd71d9130014fd74189430067e75d8940007ba42181421f76e2194b210067f65c8110136bd43d913002cfc7650a30005f571981322567f6194910005df73509320067d7018953015dc7348530066f84218142004fd74d89300067f65182320057d70189531c4fd765092102cfe70d8d100067c629494135e7c31189530067c70d95421467d6354d212567f60182522267e6454d103076c65509200067f5398a40074fc7258c200067c65d8232024fe7518943386bc20d9130466bf43d9131006df7358f2002e7c7059620006bd51d91200057d7394a20006df50d8d210167c6354d402257e7458153006fb609812135d6e72d963201cfe74d8d2012ef64158640006f
  | 8 => 0x77765d8532004ff75d8d422067f60949400067f65d8d42014fe73584200067f65585420beee42d89400065d6354c201373f53d913000cfc71d8d10004ff75d8121004fd72d814102cfe76908202257c74d89531f67e61949322067f7694a420057d74981530067c30d95420067f7558a400067c769493035d7e729493002cfe70592300857c75487200067e43596201f57c71d92521f77710949410073c52d91300066c52189301d57e7598142006bd6250640004fd7558720024fe75592320066c211895300cff7658632004fd72d8530014fe73586420067f7559121006dc40d8d2135e7d3218953004fc765052020fb71050d41005ec72506200057d7318252015de7390a320067f6558532006be52d91200047f75584201f67e41d952101cfd71d8d410057d7598121005fb7050b21076dc3258c200076e528cb21005f870591210057d719825234f7b4054f200067d62949100057f758ca101fe7c31d953200cfc71591201fd7c735865202cfe7690a300065f6518d2100df47158f2100cfe76d854200dec714c921004fd70d8d21006bd6519130006fb30d8142004ff76c86401fd7d73d8e520067f769493111e7f5359130386bc30d9130386bc50d913000774715815309dbc7458520004ff7650d200079f6350d410067f53587200057d7394910006f761c85300cdfb705891037cff7059130004ff75d8d2021d7e71d815301dbe748c94156e7f63d91530067f75586421ccff73591323e6f4311893101ebc64505205355f73585531a76e72949322067e64949320076e72d92520ddbe74d8f20006fb31181420057f7548630006bc65d912021e7e6154d202667c6254e10006f953d81421e67d53d92322667f6454e200057f754cb201cedc6358d420067f75d8d2001cfe7458f200057f7558542004ff7558c200067e7654d21006bd64504202567c6494a100057d709895321d747158153007e5718cb212e7ae4090920004fd7558d200067f654c1204667d53d91310067f535921002f7965c8220005f970c8720004fe72d913126d7f7354d4102fea72c822006cfe7298910006f96018321006f5615062002cfd74d894002e7e305962001faf72509414b67f53d89430067f65592320067c73d9520004ff75586401ff4c329493204f7b534c210006bf6450930004fd70d912102cfe70d85320eebc644c120006de6418d21006bc62509410067f5358420006f840d8132227774154d4101cff7650a20006bf6418930006bd71d91300057f7548640006f4715913219edd4358e420067f53d8141006bf73d9120004ff75586420067f65501202067d43d9542006ef7258d1015f7553d8532006ef52d89311fe7f32d9632004ff7358620006ef52189300057d70d91531fe7f73d9532004fd73d9321414ff7259121024fc75d913202e7e405
  | 9 => 0xf6458153066f9411814202ef973181420067f5358620004ff7648530004fd70d893102eee7298a10006bc31d9120004ff7458620005ec72581310057d73d95423b73c5290a40004ff76486301ee7c659092133f6f5390b20024fc7558321024fe75d9121136be31d91304a67d5318943006bf10d9130006fa65d81420067c52582421c7b7105094101cfc74d8132006df6350d210067c6218153024fc7558a40006f963d814202eef7258a30135bc7390a400047c7694910004fb70591320047d7654e200a57c72d95201f67e61d8652007b77150d412067d74d9542004ff74587200057f745865203779534c110006bf64c81200077865d81420067f76949100dfe842d81420063f6454d200257f7318953004ff765093116d7e75d832135e7f73189530dcfd74d9320004fd7559220005f97090b200067c4018953004fd73d9120006be75d912023dfa768c1101a67e76d953202df87050930246bf6450620004ff7158d200066c52d89313675c5250d3018d7c75581410067d6548620136be4358e40186de43d8d4102cfc70592300067c61d9153006bd74d8f20005df73484201b6dd43d8d424ce7e76949422e7ae6290a4013f5f7354e401f6746194932024fe7558c2001cfe7458e1002ef975181420077953c81200047d75d891002eee7298a30257784094820006dd6350e1002cfc7058e402667e6054e4008df47158d204c73f5390942004ff75d81421aedc10d8d212067e6294a4201cfe7458910004ff7650e100247c75584200067d70d9521014fe73591200067c52d91200067c52586201c7b471509410067c6558520006fa50d8142007d87050d301f67d31d9521456bd41d91312567d60182520047f7559132006df42d8d2100cfc7648110024fe7558f2102cfe768c8200067c655891000cfc71d923202ef87318142024fc7558c20004fc768c910004fc72586400057c7654d42006bc32d9120006ef624c9400076e21d895302dfb76480200067d53d854202cfe7018943006dd70d8d21066ed42189400075d6354e4215edc3258f211f67e6194a420247c7558d200057f7458e5200cfc71d8132007797094b200057f7558d200067c6558d210076c521894002cff70584200067d654c6200067e43d95210073d7494a4233f6c5290b202576f2094a200076f7258553004ff7558720024fe7559130004fc7259130066ef7650b202276f4254e42006ee6290a102067d42d954202ef84098a400067e76949300067f654c91002dfa72c8120016f8764c1101f67e21d95210067f6590932014fe76d8d1016d7c758cb211257c7558540006ef62989410067f655052001cfe74586320067e21596201f67f6194941016de6350e10005df735063002cfe70d8d413d76c758c9210247e75d8930004ff7158f20004ff768ca4053e7f63d8553
  | 10 => 0x4d200067c1018953014fc7358420004fc76509300067452d8532005f970c842040def7258d211575f7354d2102cfd73189300067c7559120007cf634c921006dc50d8d210167e6354f210057f7558d2100cfe71582321e67f53d9132006ec62909310167e6354e40004fb70591210076d62189530067e73d9521006f86518142007af6250941006be43d9110024fc75d854302dfa70c87202176e6250e5200df4714cb21004ff75589103b73f5390a400076e72d96321fe7c3158e520057c7254c20005fb7050a1002ebc4059210006f751d85300077a521814254f6e32d89530067f73d95420067c76949410067f42d9510245bc705094101dbe7290942006bf6498930196f641d85322657d7654e200c67f725962002cfe70189310067f41d96320067f10d9542004ff70592320057d75d8543146dc30d8d210dcff70591201a67c654c921267781054e100dfb840d9320024fc7559210006f970989100a57e76d95200057c7654d10004fd71d9320016ee638cb2115fe7714cb21004fc764c94103dbc744c110004ff764ca40006fb32d81420047d75d893101cfe76d9131024fe75d8941006ef6298910006ed6218931035dc7359110004ff75d81430067f658c9210247e76d9542006bc73d91200def854d814205d7c754ca10006be61d91200a67c654811007f6e729482002e7e7059620014fd71d8931006f674d85321f67c71d95212667e6054e1002cfe70d8d4220ef421d8543004ff75592300057f75589311fd7f7350e520067d74d9510014fc73586402657e70981530067d658ca200067f6158153006bd72d91200057f75581210067f53d91200057e72d85530067c64d8e520067c75586301f57e7150e5215ef77158f21004ff72591100076f758cb2115ef731d8f210067c65182320067f421895302edc3058e100067f7654e1001cfc7498a1000df47150921006f960182321ff5e7394a3245e7d53d85431fe7c3258e520077b654c110006f8631814202cfc7650a20024fc75d8d10024fc75591202657c7118153004ff755824200cfe715932021e7c61d8553006bd52d912002cec76509200067f65d9120004bf7458d104b67f6254d42006bf64d85201ff6f3294a321fe7d73d96321373e4354e400047f7558630004fe72d854300cfc71d93200067e52d81320067c6558d42037d8634c11000cfd70d8d10014fc73d8540006ed62189432667c6054d422267c6454f201f67d21d9521007eb705092001ebf6150d410075c5218d210067c52d91320067f71d96321ff7b309493001eac64509200067c7559132004fd73d89412067c64d9252006f752d853201ebf6150941006ee21189300247e75d85432867c40d951009ebe7619120024fc75d891044ddf7359131006ef42d89100b6dc3158e201b6bf41d8d420d4ff768c8200067
  | 11 => 0x67f755823201cfc7458f21004fd7558e103de7d53d893135e7c3018953194fd73d8f211fe7e63949100067f74d95200067f42d9532014fe7359020004ff75d8d4105d7c758ca100767d5318930006f564185320367f53d8d10004ff7650a300047e72d9510004fe765093101ebe6050640185dc735894101cfe74d8532007777154d4100cfd72d8d21006fb60981310dfe84090b200067d6454d213deee32d8931076ee321893001cfe7690a3200ef461c8530024fe75189310057d71182520057f75585400057d75d832115fe732d8532004fd70d8d420057f745895300577715895301cbc7458d10004fd71d89430067c7694940014fe73d89410247e75d8910415ef72591212067d6494a400e6f461585300077852d81421fe7f31d9632016fa634c210004ff7558a3015e7753d85323376c7550b200067e6298153006bf644c920004ff7358910006f6651853221f7661d85530e5f4715893002cfd73d8930006f464d8532006df7358d101ff6f32d9632005f77150f2116d7e7598321006dd634ca200067f6550d1015ef630d8532094fd70d8d20004fd72d814301cfe74189300d6dc6358f2001dbf725094100cfc71d91320067f6394940004ff75d93210defb40593200077a528c1100067c41d95200067d7654f2121e7e6154e40006bc64d8530014fc73586200a67e72d95201e67d6354e42024fc75591212657c705895301ebe6490b210067d53989100dcff769082006eed21189101fe7f43d96320067f53582420057d7394a420067c6559232004fd74d8530006df7359110036df30d8d100067e5258321024fc75d8d4200cfc76c8110004fd7650f20056f541d85400067c52d8d100057f7558930004fd76c85400267d7694b20006df638c941246bc40d81411ff773194931006bd65191201dfe421909210167e6354e10007b764505100067f61d82520067e7654d100057f758c92000774521853202efa60182320067f6598910014fc73593211f67f7694b210067e6294a40006ed6290a1009ebe64d91200057d7394b202667e6054e200076c7254e20135bc73506402073c4394a401f67f6194931006f76198132006dc63d8121005f7714ca402067f72d95421557c75591212867c20d95100067c61d95320073e5290942005fb7050420194ff7158d21006df63509210c57c7550a20004fd70d8f2101cfe74582322e6bf72d912021e7e6154c2011ebf4359230006bf50d91200067c61d95420067c40d9532004fd75586320067f40d96322867c10d95100067f73d95100067d6358652004ff764c6202057c74d8652006dd64d8d212067e6494b2001cfc7458a300067e7359620006bf64909201fe7d32d9532014fc76509320067c52d81211f76c2194b211f57c7158e52004ff7558d210876e62d825221f747154e100073c645
  | 12 => 0xd6454e200d4ff764c8202677a6018153024fc75d8142004ff7598a400067d649493015df77158931004ff72591312067e64949210067e6458e522057e74d865201cfc7458630006f7715891001cfc741891002cfc70d8d1002efb62c812002cfe7058e100073f64949300b6ed32d8930024fc7558620006fb73d8142006f852181421fe7c6394942004fd731894102dfb764c21000ef661c86300067d53189100073c52d91202567c60949310debf41593200067e525872000cfc7158e420beed42d89400067d7654c20004ff75d8d400057c769491002cfc70d911007d7c7548420005f7714c921004fd75d8d101ed7c755864200674651853202eee2098a4000dec714cb211afe4318cb210067c21596202567f6494a100247c75586402f77b4054c202667e7654c200067c52586320067c7694910004ff75d92320267e7694b200f67c654c11001fba6090a401f76e21d95210defb41d81420067f74596200f67c654c120064fc725902000cfe76c8110024fc75d81431b6bc6459232006ec7259110014dc7358910024fe75d93210067c61d92523e7cd7218d2102cfc7058e2002ef9711814202dec7090920096dc31d8d2011e7d5359230004fd70d9232066f841181422e7ac4090b200ddbc744c3200a47d7694a20064ff7650b200067d6454d100067c75d8d21004fd764c6201aedf10d8d2102cfc7058642006fb7058d100067f65509100067c52d85401267c65501100057f71581533779e30191300067c10d95322867e70d951002cfc70592200077b53d814200ef661c84200076c52d89400057d75d89401875c6354d41006bd54590201267c65501200057c7254d422075f4350e520247e72d95202867c30d95100067e62d8153006bf65191202073c42d954202ef41058630024fc7558f2123778658c110014fe73589100057f754c820006bf52d9130006de31d8d420077a7094b200967d5358a30006fa63181420167e6354d200057d75d891002eec2098a10014fd768c820247b661506400057f75581410067e64989531f67f72d9521014de76d8d211d76e72949420077a524c210024fc75d923219ebc6459132004fd7418910196f621d85320067d6494a100067f6518121004fd75d8d4040ef76218532016ec634c9210077771589530067e71d95420debf40593200067d5358640004ff7258e101467f6354d210057f7250e5201cfc7458d210057c7650e520067e52d814101cfe7458e2000cfc71d911004e7d6354e10005ef724c3202067f42d95420057f7058e521476d534c92115ef643d85321ce7d6454e420067e525842002cfc70586302073f41d9542014fe76d8d2002cfe7058c20006f775d8532096ee3258a30016dc634c92002cff73d9130014fe768cb21004bf74589104277753185321fe7d6394a30004fd75d8943
  | 13 => 0x863021e7f6054d101363f53d91302263e64d91530067c655913221f744154d412ad7e7294a201867d535913100df4714ca10006dc6418d210076e5290b202575f3094a3021d7c71d89530076e72d86521f67c6158652066fa541814221f7b1054e10024fe75d894302eee7298a40006f571d932102cfe7650e202067e41d954200cfd72d91212557c70586520067c52d8f210057f758c9410057d75181432b57f7354e2002df87050720006ec21189302e6bc20d91200067c71d95320075f73581532077b409494002ef51059210004fe764c941005bd748ca400067f10189531fd7d7394932014fe7358720014fc73d9130197e57218532005f97090820006dc63981212267e64591530167c6354d100076f754c92115ef632d85320067d64d81533376c5250b20004fd75d814137dfb7059130004ff75d8532004fd7559110006ee6250a1019ebc40d9132476ee4218941006df65d8d210067c75582320067e6198953386bc70d91300067c61d95200167c6354e400067e7654d42196f651d8532006fb53181420067f6550932267761054d1000cfe71189102667c6454c200067c73d951001ef46450510006fb31d814202cfe70d85431f67c21d9521006f765185322067e6494a101a67e7258e521fd7f73949300defb43d8142005bc72506401f67e61949305567f6358953116f461585400defb40d9320006df70d8d211467f5358632006f574d85320cef661d87200067c65d81320073f53d912001ebc64909300067d7058e52006ee72d9320006bf745932142f6c758cb21015dc7358632005fb70509201f67e71d95211f67e6194a200067f6158252247b5615064001cfc7498910007e532c8521014fc73d85420067c7518910004ff75d8f2001cfd71189412e6bc10d9120024fc75989100067f6518910005bf7458d10006dd6350c200077970948200067f53d81210067c4058e522e6be70d91202557c71182522567f72d95200457c75509102557c7198252007ea32480200057f758c9400063c52d9130005bf73509410057d7650e52006be41d91300075f65d8d2137e7d53d814300cfc71582422e6bc4058242024fc7559230006f4615813202efb618c110137b830d91300b5dc734862009ebf42d91200057c72581530a76e625825207d6e72d825202efa60183210067e7654d20006f840d8121196ef614c9210057d70d8553004ff73583210a57c754c92018e7c65505200067f53d8540006bc6119120014fd70d85300def842d81420076c21d89530047d75d89302167c6550d2121f743154f211aedc71d8d212057e74182520def874d8142024fe7558a400067f6559110386bf73d9130006f551584200067c61d8e520057f7559120007bb64c8120004ff7558e42006fb70591100247c755891025774109491001cfe76d91320067
  | 14 => 0x2cfe70d89430067d63d8252006f664185320067e6159153024fc7558e20006df52d8d211b7ac4250a32006dd6518d212067e6494b211ce7f6354d4200cec764c9210067f715962000ebe61506402e6bc50d9120004ff7558232004ff7058d211dcff7459121004fd73d91210076e62189530067c7654d4002edc3058e200067c7654f211dcfd71d912117f5f63585532273f4154d422067e40d9542004ff7458f2101cfe7458d20014fe76501302567e7694a1000df6718cb2102cf8705902001cfe741891002dfa70c84202e6bc30d9120005bf745891036f9e73191302067e64949300067f30d95214ff793018153037da434c1102557d7694a201ff6c3294932004fd71d9120136bd31d9130004fd75593200073e5290a40004ff71592321f67f71d9521004ff7458d210067f7118953066f9541814201cfc74d8d103376f5350b20004fc7258e1000dbc7150941066be54590200067f64949200077b60582520067e525824220ef46158543024fe75592100057f7550a30066fb4018940006ec7258d10005bf74583210075d43949300a57c758c92002e7f30596200057d739482002eec2058a10004fd75592100067c65d912000cfc71189430057f755894002cfc7650e200067c7058e5203dbc7458d100067e62d8553006be21d91300067c63d952128e7f10d951002ff3614c11002cfc7058a402557c73182520077471589530d67f6354f20014fe73d8540005bd74d823202df670505101f77421d95210457e75d8910006dd638cb20006df73591301fe7e639494200dee718c921014fc7359110386be30d9130024fe75d92320067c43d952001cbe76d91200067e6158e520067f65d91210247c7559110014fc764c320005df7350130005ec724c420136bc73d9130006dd6350e20005f571c811002ef771586203a5fb7058d400057e72d951017d7e75181312567e20d95200066c521894002edc3058c200073f6459153006bf6450d20014fc7358a101def64158642004fd7558a300067c64189530067c65d8d21007d632d853200cf8764c1100067f649895300cfc7198a30014fc73593200067d6454f20004fe72d9110006df634c920094ff7358d200067c63d9510006fb7059130006f731d852002efa75181423cf6c654c92128e7e31d951001ebc64506305857e76d91532567c6394a1019ebf42d91320debc425932000cfd72584200073f65d9120006f774d85321d67c65509210067d7654d20006ef5218940004fd765072002cfe76c86302877610d951000cfc765011021d7471589530167c6354c200076f658c9210067d65c8620016f8634c1100057f755853021e7c6154d420067e52586200067f4258e521f67f21d9521007795348020004fd71d923202fdb734c11014fac4250921316bf6219120004ff7159120024fe755
  | 15 => 0xf7258530004ff7058f210e6f661d85301aede41d8d21024fc75d85300067f639491015e7d53d85320d67f5398a3002ede3058e10004fd755863001dbf715064000cfe7158e202273c40d91532067e43d9542416ef21d8941014fe7318940006bf64509320065c52d8d212067c6459252004fd7598a10447773194b2106eef21189102273c4054d412567c6394a2002df87050a2026d7f7354d10024fc75592320057d75981322667f60181530067f65d8142396bc40d854001dbe7290a400457c7558910006f77158d2001cbc74589100057d73949421d67e72d9542006ed6250a101fe7e31d953201cfc74584201fd7e73d92520076f72581531cede63d8d420057f74585530067f75d8d42006de6518d210067652d85321fe7c3058e520067c5298a30116f661d85400067c75d8d420767d6354c2002eed20590200067e76949312567e6094b21007b8744c110007ba42d8142006fa53d81420077765c8521006ee2118940006fb51d81421d76e62592520067d75d89412257c74989532067c6494b211c7e421509212257c74589530067c42d96320067d6458e52005fb705093018d7c754c94101cfe74d8131014fc72586321fe7c30d9532006bf7458d20066f84318142004fd74d8532006bd645072001cfe7458d2100cfe71d894002cfc7059121004ff764c9410067d53d89410fef63158630024fe75d91310075c63949211fe7e63948201f67c6194a42004fd7398a40024fe75d813201cfc7458e100057f755823200cfd73d9131006f96518142004ff755912116f5f7354f21426ed3218931004fd70189430067c74d95210067f32d952100cff768cb210a67d7694a20245bf765064025d7e7294910006ec62509310ddfb7058940004fc765053002fb840501300067e21d95420057f7559121004fc7259110276fa10d81310076a52480202675d7398153035dc73589100067f10d95321fe7d43d9532004fd75d8f20006fb60981321dcff71d91210067e74d9521006be63d91200067e52d8121006fb60983210067f32596201e6de4358e42006fa6118142165bc7458321006ed62189301aedd72d8d21006bd645032015e7f53d8f210067d53d8142024fe75d8141006dd53d8d412273c4254d422575c30949300067f7654d2140eef21d89310acfe76189100067c65591210067c52d8d41004fd75d8520004ff735912102ebf745902035e7d4318953274ff7058d10097cc324c9200067e31d9542024fc75d9130004fd7518930004fd75d8d2002cfc7648520007af7450b20247b71050640227784054d401fe7d6350e520857c7550b20014fc72d8d200067f6494932006bf64485301257c754c94009cfd76501201f57e71982522667c6454e20024fc7598a30006bf64509201e6bd43d9132004fd72d85432673c4054d402567c6094932
  | 16 => 0x8e4200df8764c11002dfb72480201f57c71d825202dee70509200057f74581530d5dc7348720024fe7558d210165c6354d2102cfc72587201f67c61949202257e74d89530a67c72d95200055d7394a320e6dd3158e101be7e62d8e520067c52d8530006ef6298940004fd75591210065f53d8d2102cfc70592320047c7654d21004ff7058642024fc75d93200057f7550a321ff5f3294a32005dd7390a322067c6494930006f865d81420067f655814204ede4358e1002e7e1059620004ff7648640006ef52d894021e7f6454d4100cf47158d20006bc65191201fd7e735925202df87050f20004fd75d912100dee718cb210067d7654e1002cfc7058420016cc638c92100cfc71d8d401cede43d8d42005ec7250420024fc75582422667e6054e423276c52486201f67e61949402667f6354e40005df734864002efb74181422257e7498153095f97098930006de3158e20014dc73591212577a70948200067c65d8d100b4fe768c9201567e76d9521196f451d85320067d70d954201ebc6450b21014fc73d91210067e74596202067e6494931004fd7418931014fe7359210024fc75d85420267d7694b2102cfd73d913002cfe705921004e7f53d85300067b65181422667f6354e20004fd764c9101257c758c940007bb74480200073f7550941006f853181421ee7e62d92520b67d6354e201bd7c7559232024fe75591320d6df3058f20004ff74583210067d73d9521024fe75d8d10004fd75d81430077a52d8142006f975d8142004fd75d91101f67d72d9521004fd7690931005df73486302676e2054d200debe64d93200056f7258153006f863d81420076c7254e42006df43d8d100067f6454f211f76c21d95210067c41d96322273f4254d4100cfe7118943024fc75591310fedf31d8d10004ff765091008df4714c9200dfe84050b2025c7e769492101ebc64506200047f7558d20007e87050b200967d5358232006be51d9130136bf70d9130006be74d8f20016ec638cb21024fc7558232006df73591211867f53d8d412267e6454c2002ef6105864009def745092003dbc7448110006bc611913000cfe7198a3015e7d6354f2100cfd73d813121e7c6154f20004fe769093100cfc7159232006f731d85420057f7548110004ff768ca1001ebc64909100067f6454f200057f755092101ef664505100057f7559132004fd75586420d6fa30d8132004ff75d85431a57c7558132014fc73d9320005df73585422073f43949412057e7458e520067e7654d411aedc618c93221f747154d41004ff7650d21257784094a40004fd70189310bcff72591200076c52d8930136be32d91304ef5f63189531fe7e6394a42007db7050d30006bc75d913000776521853200cfe71d8d200067d76949410def941d8142004ff7458632196f672d8532005e
  | 17 => 0x14fe7359110004fd74d8131006fb60982421fd7c73592520157c7318153014fe73582420aef43158620146dc6358d211adde7618d210debc64c81202567e60948200067d74d9632004ff7159130006ed62189410067e7654e420066c52d89400056c725855301ebc6450930096de63d8d2001cfc7458e200247e76d952002cfe70d8941016de638ca1015ef730d853202df870504202257e7458553004fd7558321186de53d8d4112cff74591101e6dc63909212257c74d85530073c52191302677a3054e101ee7e6590a200047d75d89402867e40d9510014ff7690a3238efa40d81410d57f7354f2035e7e3018953004ff735842015ef553d85320067d7158e520defa64c8120006f7615813203fb743505100067c651814228e7d71d95100067c65d8542004fd75d8d212675d6354c200067f755863215df7714cb21006bc64189301debf41d9121007ad6490b2001ebe64504200067c52d8520006f95118142006fa5218142004ff76506200077452d8532005ee76909200077953c822002df8705091010f6e7294a300deee4298a40066bb4118142004ff73592203e6dc31189311f67e6194942024fc75d93210067e5258632024fc75593200257f73181530067f65d85320067c5258d210067c5258f2002efa711814254e7f63d8953004fd768c9401c6bc76509410067e7654d40004ff7358642136bd73d913001eee6490b20004fc764c7201fe7f6398953004fd7558d210067f1058e521fe7e3158e520073f6494920014fc7398910014fd72d913202ef771584200057c7254e40004fd74d81322a6fb764c210004fd7558910006bd73d91200a67e76d952000cfc71189100457c755911001cfd72d8d4200cfd7318931004ff7458d200067c525902039d7e76949421aedd31d8d2128e7e41d9510005fb70591320257d7318153004ff75d81314f57e72d92520057d70d895315f6d534cb21004fd73d81410067d53189401f67e10d95210167c6354f210047f75586322667f6454d4001cfc74583210def864c81201afcc318c9210057f75509310057d759823218d7c758c941006ef32189101257e75d89400165c6354d41066fb541814220ef661d8543006be31d9120004ff7358a40006bf10d9120004fd75d8121024fc75d894035f6d32189530067e52d8540006f87059132014ff764c32056f3d43d91531aede21d8d212576f209482013f6e7294a40004fe76485300067d63582521bd7c755823200cfe7158e40006f461d81320247c72d9520004ff7559320426ef764cb210047f7559110004fd76506304a67f53189430c76e629825200cfc71d8d200167c6354d201873d5350d41006ed62189400857e7294b20014fc7359220006ec628c9400d67f5358f202072c4294942146de43d8d21006be65d91301a57c755093200cfe715
  | 18 => 0xd4358e402567f64948201e67f53d92320067e21189530067f65909202257e749895302cfe7098a40006bc51d9130016dc634c921014fe76d8d211557c75d8d210057f754ca40014fe73d911028e7e21d9510006ef62989430167c6354f200157c73d91532567c6194a200967f6354d200ccff76484200067e43d95100057c72591531a67e654ca200067e6258153006be611912000df4714c9411e57f7354e4255e7f6359153004fe72d8131014fc764c1201fd7e73d865201ebc6490920006df64d8d210067f40d95210067d7694a40004f77159132024fe7598a400077553505101fc7f73d95322567c60949410057d7598242024fe75592300067f65d8520004fd75d854302cfc7059132094fd764c120167ac4250b210067c64d95200067e7159620006ef62989300067c6198953014fe7359121024fe7558f20006bd649082000df471481101576e72949210067f41596201aedf638c92100cfd768cb214d6ee42d89430067c6159252014fc73583210aeed21d891002e7f40596200067f5358a40165f771589410067f6394b2100df8714c11036f3f5319130007cf734c9210067e41d95321aede51d8d2101faf6290942005fb70589431adef734c921006bc64d85200e4fd764c1102567f6294a1000cfc72d8520006f650d85320067c31d9520006f564d853203dbc7458910004fd73d8940176be64d91312073e7494a42006df634c1100076e5250b202067c64949211fe5c6358e5200dbc7650d4101cfd70d8d4009fad72191200057f7558943006f96018121245bf70506400067c52d9131006dc73591100067f65581210067c521894300cfe715913202ebe405921015f7753d853217f6e7294931036de63d8d100067f53d85200073c65d912000cfd74d8d41004ff7558a40024fc75d8d200067e75d854321e7f6254d211567e62586520067c6518132006bc21d91302557e70d8652014ff7658f20004fd741893001cff76503201ff5f32d9632115f4714c940024fe755864215ed463c8521145de739812135e7e43189530057d74d8e52004fd7598a30016de638cb2105f5f7354e101467f5358d210247c75586420057f70585530067c52d923200cfe76d8540014fc73586420057e7654d200067c75d8d202263c6454d2002cff71d8d1000cfc7258f210067f65c8120016fa638c1100067c5258a40006fa63d81420067f6598132006f571d8f210067c65d9132004fd7558a40006dd638ca1000cfc71d8943014fe73d8142004fc768c9400057d71d92522867e30d9510246bf6450630004fc764c9400067f53590200067e7654f20066b8421814202dec7050920476ed4218941004ff7358a1039d7e7294a420067c32d95200073d5350941006f665d85321f57e71d92520063f64949300dfb840d82420247e76d95102076f4294a42
  | 19 => 0xc8200057e72181530067c71d95200067e6294a300047f75591202673f4054e4014ebc6459121136bd53d9130024fe75593202067e6494a3000cff76587203567d53d8131006f765d85320057f75591100067e70d9532004fd75582320067e21d9532006ee21d894019ebc644c9200057e72981531f67d6194a102e6bf6490a2000dfa718c1100defa54d8142006f873d814220fb47150d41006f474d853202edc3058e400067d53d8910006f454d8532004fd768c9410057d74d815302ef87059020006be41d912002e7d20596200067f7654d42006bf64589301f67f41d952121e7461585531fe7e43d95320075d7394a320057f7558d4201ebe6490a321fe7e63949210067e6258953006f960181410067f71d953202df8704852048df77158d410067d6454d20067eb421814202cfc76504200067f43d95210067f7158e520057d74d8252006f970d93201f67f31d95210167e6354d401bf6e7294a3201cfc74d8121005fb7058d421afd4318cb21004fd764c720004fc72592100057f75485201ccfd7650932004fd75593210067f6454d21004fd74d8f20006ef521893100ef762c85211e6dc6358e42257783094a3002df87050b20004fc764c9101def4215864207f6e62182520067f43596200067c73d9542004ff72591300067f3159620004fd70d85421ed7e7598242006fb53d814202edf7358e20006795318142006bf64c853002dee72c8120136bd70d91301f77641949100067d5358642014fd70d91300067c64d9532004fd72d8d1021d7e71d915302ef410584200057f758ca202067c6494910006bf6458530004fd7690a10004fd71d8d20006ec2118940006f852d814202cfe7098a100b4ff7258d2013d7c7548640016be6350d41004fd75591200eebf4158e4028e7d21d95100076c7254c201fe7c43d96324a4fe769093201cfe74d85301fe7e63949410077465185320067465d853202cfd72d85200067d7159620006bd6290a40014fe76d8d41006f973d8142004fd70d9132006de31d8d200067c42d95211afe6718cb21014fc73589100067f75589100077765505103e4fe72d8f2102cff7058e10007f37050510006bf70d9120007ea7090b200047f7558d1000cfc76509210067e64d9520004ff7690a30006f8321814200cfe7159232006bf52d91201fe7e30d95321b6be64d9232006f871d814207d7c75508204067e7694921024fc75d8d210067c21d95422e7ae20d912002cfd71d8d1015ef732d85320067c42596200067d73d9542007f1414c1101ff3e4350e520fef64158630005f7715011000cfd70d911021e7d6154f210065c6518d2101cfc74d81310067e61d95202157e75d854300df672c852128e7d31d951000dec718c9210067f6558632014fd74d8943004fd74d8d200057c7254d2135d7e72949320eed
  | 20 => 0x4ff76909102e7ba7090a40014fc73d85201ccfd74d92320067e7558e201debd41d9121004ef7258d100067f6458e5225d7e76d95210a75f7354d20005f870589412b67f6318153004fe764c5202575e30949300067c65585420076d53909200377b534c110024fe75189410063f53d91201fe7f4358e52007b864c81200257f73d8153006fb70591210067c1058e52136bf32d9130006dd5358e421ff5c4350e5200cfe7159130006dd634c420386be50d913002df87050c200067c5258e42004fd7650a30006f950d81420067c52d85421576e6258652004fd71d81430067e52d85300077b60982522057c745825202cfe7650e10006fb75d8142005f57190b2100cfd73d89310067d53d89400dcfb70591200067f639494100cf471591320067c52d854309ded7490920014fc73d93210065d6354e420267e7694a4221d7e71d895302ebc40590200065f63949212ff7b53c81200067f65d86321afce21d8d21006bc649893002ede3058e20006f8311814212ebf41d91100067e4158e522957e76d95100def841d8142006ef628c94000ef661504200076c7254d4201cfe7498a3003ebf40d91102567c61948200067f65d8910066fa42181421fe7c7258e520ef3e75191300457c7548110005ec724c1204b5ef72591322e6be30d91201f57e71d8e5202df470505102273c4254e400067f7518910004ff715922039d7e76d9542024fc7558d10166be64d93210066c521893121d7c71989530067d74d9532076de4358c200067f53d85420057f754c921004ff7458e2035d7e72d96320247e76d95320ceed2198a10006ef72591200257f73d855301ebc645092109efa40582420057f7550b21036f531586300057d71d9153004ff7158a30004fe72d8d410057f75585200047e7654d212277b4054e4010d7c7548630006f5719891015ef653d853244edf31d8d4100cfe71d89300067c7654d2001eec76509200067c65d8d42006bf64d8930014ff7258c202667e7654e202e7ae4090b200067f658c91001cfc74d852002df87059320006ed62189102e6bc70d912028e7c71d95100057d73d9521024fe75d9320355fb705853017d7c75581310067d6398252016dc638c910006df63181210067d6458153007796018153136bf30d913002ef840590200247c7558a1022f78524c1100267d76948200067f7654d40006ef52d89301fe7d31d9532024fc7558e10006bc63d9120024fc7518910014fe735862002efa60181320def954d81420076f754cb2100cfe7118930014fe73d85422057e7458252004fe768c9400067f654c9202273f4154e40005f7714ca1015edc6358f210067e71d95320063c52d9120006f9521814200cfe76d85431ff6f32d95322ff7852c81204667f53d91310a57c755912002ede3058c20004ff7598a1002cfc768
  | 21 => 0xd76506201fe7e4358e520067c659814201eee6450b20006bf64485202567c7694a405275f63d815301ebf62909420057f7558d1001dbc74c8640006f741d85321be7c658c9210067d6550620016de634ca2002cfe768ca400076e72d825202ef410586201f77641586520867e62d82520067f53989102567c10d95203fcfe7690921065fa7448020006bf64d8d20006f740d85320067f75d8d10004fd75d8941004ff7518931196f661d85320247e7694a320067d75d85432b57f7354c200073f531912021f6e2154d210867e629482002e7d405962020ef631d854302ef7715864002cfc70d85201367d6354e40176bc40d91311fe7e6294a320057f75485300067f32d9542004fd7558e4002cfe76d814300cfc71d8143005df73581212557c7050e5202eee2098a30006bf644c5200067c65d9121004ff7648540024fe7559110006f46118132006f76418532004fd7498a3000cfc7158e200057f758c9102677a2054c200067f7654c20004ff7650520004fd7558f20016df6050d3015ef572d85320067e74d95320def843d8142004fd764c640074ff764cb20006bf74583210fef6515863000cfc71d91300057f75485400067d5398a100067f7694a30005fb7050a2050f7a30d81531ef6e62d92521e67f5358e423f76c52909211aedc51d8d211ff5e439493002eed2059220196dd3158f21014fe73d8940024fe751891002cfc7059321014fc7358a4001cfc74d8f21016ec764c92110f5f63981531ff5c3294932005f870509321fd7d7394a30016dc6350d2100ef661506300057c7250e52134ff745913045e7f53d8543427e432185320257c7259252006ec62481102667c6054d210247c75591320057f71592521b5be74d823203ef541586403fcfe72d93211fe7e32d9532004fc7650931005bf7458d200067f6558d42006f664d85320075f658c9321afcc318cb21006be21d9120065f87448020014fc735921001cfc74d8532024fe75586322667c6154e40004ff764c5400073c521912032f6c52c8620006f965d81420b6de4358e201fe7e63d8e5201cfe741893101ebe6090a400075d73d9632006f751d8532006dd75d8d212e5bd7090a40004ff75d8520005bf744ca402167e6550e200067f30d954200cbc7650d41006fa61d81422e7ad6290a40005f77158d2001cfc7458c200c57c754ca200067c52989100077b65c81202567c40d9520004ff7359120006be43d9120006ec42189100257f73d91530067c71d95420057d7394a400063f65d9120075dc734842003ebc42d91102ad7e72948200067c7654d421f73c41949410067d75d893102efa60181421a55d73989530debc435932003ebc64591102e6bf641814202edf7358e100067d6394b201aedc21d8d21004fd74d89100067c74d9520005b87050941004ff7159320
  | 22 => 0x895300cfe715912002ddc7650d300057f755923200ef760505100067c52d89312067e74d954201ebc6450d2004e7f5358e1008cfd7648110004fd7650a100767f53189300057f75581320047f73596200047e7654d100067c6198252014fe7358a4002cfe70586400067c52591100067e71d95200057d73949210067c625855321f3e4154d410057f705925236fb83019130014fc73591200067e70d954202efa768c11018d7e75d89411275f7354d402067e64949200067c755864006ef6315842015ef473d8532006bd6350640006bc71d91300067e64d9521146df30d8d21006bc7458d201aedf21d8d21006bf74591200167c6354e4208eed2158a102bfe8424802002ef710592100067c5258a30006bf648c92001cfc74d8d2001cff765093221d7d71d8553014fd72d853228e7c21d95101f67e6194920004fd7398a100067f64d8e52186dc6358d41006be51d91200057d759814200cfc72593210067f70d95200067c75592322067f64949423cf6c524c92102cfc764c420006dd53d8d210073c64949300067d6294a401def661d86422567c20d95200247e75d89400067c52d8d2102edf30592300077652d85320056f725855300cfe71d9232136be53d91300057d74d85530247e75989100867c65c81100defb54d8142004fd71189430067f6454d100067f6550d200076f755092001cfe7458a30007796018252006fb61181421d67e62592521f57e7159252006f853d81420867c65c81200179f7450d3039d7e7294942147cc634c9212067c6494920006ee72d9321004ff7458a100067e52d85200067c525923000cfc71590202657e7098953006f442d85320067d7359620135be7390a40006bd71d9120005ec7258530006ee21d893019ebf41591321f57d71d86520066c52d893002cfc7058632004fc72591311fe7c6394940386be10d91300067c52d8d42005f7714c1100dfeb7050b201cedc6350921004ff75d89100067c52189300067d6394921414ff7650b211d67e6550a202667d60181533e6ed2118931024fe75d8d420067c5259131006fb7058d200067e2158e521c4fd74d932102cfc7650a102657c7058553006bd6450c200067c65586320f55d73981532076c42d95420067c21189532067e6494a320067d7654d211257c75589401fe7c7694a320067d6494820014ff764ca20006dd5358e10006dd6418d2110d5f735815321e7e6254f215167f63581531f67d41d95210057f7358652004ff75592321afcf638c9210eebc54d91300073f6519120006bc74583210067c6118153006dd638c82002eec2098a400067c5258e1014ebe64d91211fe7e6358e520067e71d96320067f42d95202076f42949422067c7694a422267c64d91530deed4298a400067e61181532257e745895335e7e6250e522067e6494910004f
  | 23 => 0x4fe72d814111edc31d8d4021e7661d85530247c7558a302c77852480200067d73d951028f7810d95100067f5318910014fd7118931006be75d91300067f53592200157e731815357f5f63d915312ebd41d91100073d53506400247c7558d21007bb705064001cfe7458d10007af64909201ff5c6358e523477b4094b20004fd75d91310057d71d895335d7e72989530067f535911001cfc74587200367d5358630006dd634c3200067d5358a100067f53d894115ef73158f210067c21d9532004ff75989100067c7458e52004fc7650f200067e63d9520004ff75d89413e6de311893101cfe72d912000cfc74d854028e7f21d95101fd7c72d9532004fe768c94100cfc71189300067f6558d10004ff71590202257c74d8153195f4715813200cf676d85320167c6354d212567c30d952016f6e62d865221f742154d21024fe7558e2015ef743d8532007d763c85210067c65d86320067c5259220006fa52d8142006bf51d91301afce318c9210067c65d81420057c7254f21267771054e100067c52d814321d7c7158153036dc6358d1002df870508200056c7254e204267d531893109faf41509202567c6294a100067c65d85203e4fe768c9212657e70d895318d7c75589414d5ef7258d422567e70d9520004ff75d8540006f470d85320067f65509202567f6494a200067d6318252396be40d85400967f5358a30016ed768cb210067c6518121005fb7050910004ff75d813202eef62c8120146df32d8d21006fa75d814200cff765864202cfc764c9200967d6354d20004ff7558a100073f7454e40006de50d8d2100fe762c852102cff705921002cfe70d92321f77431949311e6de5358e421ee7c659091000dec718cb2102cfd76c87200067f535864021f781054d101475e7518d210257c7258652016ec638c9211cedf32d8d420057f758cb20006bf64501101ee7c659092021d7e71981531476d538c9210057f715915335e7d3118953024fe75d8d40207774194941014fc735912111e7f53592301afd421d8d2121e7f6154d21005fb7058542466bd43d913101ebc64509200057f7550a1000cfe764c92102cfe70d8f210067c521891002e7d305962001fb76150d410367d6354d1000cfc71d89400457c754c91002efb75181420067f6494931426ee3218931004fd769091021e7c6154d40024fc75586323de7f53d89310067f7654f2128e7e71d95100067f7654f200057d70d8e520067f65d91100067c52d8941004ff75189302667f6354e10005f7714c920004fe764854016f6e7294b210067f5359121066fb4218142006f761d8132005bf7458930006f951d81421aef431d8f210dfa84090b20024fe75d91300067f6494a321fe7c32d96321bd7c75586320167e6354f201867f535913102cfc705864001cfc7458f200067f629
  | 24 => 0x530d8532005bf744c1201aede10d8d212067f40d95421fd7d739493102ef771586300067f73d952014ebc6448530004fe769093001cfe74d8d210067c755911002edf7358e400077a524c110015dc7350130004fd7198a40006ec21d89400067e7058e520a67d70d95200057c7654d2021e7e6154f200063f64949200067d7558e201f57f7658652007b874480200d4ff7058d200057f754cb21006f96118142006fa71d814201dbc74486400077553c8521066f9421814202cfc764ca100c67c72596201cebf43592320257d73d89530ceef2198a101fe7c6358e52006dc65d8d21006fb6318142006be63191200067c41596200067c7558642004fd71d893035e7d7318953006dc54d8d2135e7f32189530067e7694940005f7714c9402667f6354c20004fd75189430047d75989102c77b53480201f67c61949320077a52c812000cff7690b210067d70d96321f67c41d95210eebc42d91300075f6518d210267e7694a322557c705925204ede5358e100157e73189532e7af72d91201f57c71592520075c65d8d210457c758c9100065f75d8d210856e72182522d76c52484201fd7e73582520067c52593201a67c654c910006f96018131007e632c8521004fd75591310067c7558d101b6bf415923202efb73181420067d769493002cfc76506200057d721815302fe8204c1200067f65d923201cfc7458d2000cfe71590200067b65d81420075f6354d2102ced7690b200fef421586302567c6094942004fe768c9100067f30d9510004ff7458e100067e52d854237e7f53d81431afcc21d8d21006ef32d89100adf4714ca201a67c654c9200067c52586401aeef618c921005ef7258d10376bf631913001cfd73d81430067f6590a322057f7659252006df73591320cef71058720004ff7650930014fe73d8520146de7618d21017cf628c932004fd75d8d4102efa60182420aeef21d89100067d649895321f762154f21016de6350e20014fc7650130036dc43d8d1000cff73d913102eee2058a40007ac62509410d6de63d8f20004ff75d91311fd7d7394a3215fe7314cb21006bf7459131004fc76509100247e75d89311b6bc42592320067f63586520eebf41d9130024fe75d8f200167c6354d4135e7f3018953014fc74d8d4002ddc7050d3001cfc74d853002cfc705921001cfc74d8d2100cfc71d8f2000cfc73d85300267e7694b211bd7e7598232005f771481100067c525912102cfc7650920066f943181420eebf40d91302676d2054c205475f63d8553005df73591210067f7654e200257f73d89530b67d53d8930006f5651853202cfd7058a102057c74586521fe7c31d96320067d75d89430075c75d8d210067e64d96321ce7f53d8d420247c75586300b6ee32d89300c57c758ca201c6f661d85420a67e625825218f5f7354d41
  | 25 => 0x4a40007f0705051007d7e72d8252006f952d814221d7e715815305f6e7294a102067f43d9542004ff75584201ee7c659093208efa10583211fe7e6394b211ff6c3294a321ce7d5359132004ff7158e422567e6094a200dfb840507200067c2158e523ef6c52509212273c4054e420067e75d8943004ff735921000cfe715922043f6c5290b2102df8718c11006ef64158420006f831d81422557c7058e520067c75d8d10004fc76c853002dfb734c11008cfd70989102057e74d82522577a6018252024fc7558642014fe73d8910257781094a100073c64949201cd7f7354d4215fe772d85320067c655853202cf8705912101cfd71d81410067953d81420073f65909420067e64d8e52004fd7558e42135be7350640005bd744c9410dfeb72d814202ebc405923022f78654c1100076c52d89311ce7d53592320d67f53d8f200067c73596200063c65d91200057e7654d10006bc51d912021f6c2154d214ed6e72d8e520047e7654d2002cfc7058a301467f53d8d210dfeb42d81420067c52d81422567e6094a1011cff735913002ef874181421f67c61949300cef461587200073f7458153004fd74d8d21004fd70d8d410047e769491001cfc7498a30004fd7690a3000cfd74d8141166bc42593211fe7f30d953202ede3058e40004fd73d8121024fe75591212067c42d95421c6bf4159321006dd638cb2101cfe7458c20007cf734cb213feed2118941006dc75d8d210ddfb7050b20006df6518d211476f534c92102dee70909200057f7150e5215ef463c8521006f971d81422567e6094a4000ebc61506400057d71989530076d535092015fce638cb213bf3e4394a4002cfe70d89310053f745815302cfc72593200fff2418c1102067f6294942004ff75586202657c71981532ff7865c81200067f535932011edc6358d40024fc755932101cff76593201fd7c73d86521fd7f739493202ef864c822002fb840503200457e75989102673e4054d40024fc7518940004ff75d8f21005bd74989302067c6494b20005f771589300067c52d8f20024fe7558a300047f75586400075d7398953014fe7318941137bb30d91300067f7694940004fd74989100067d7259620006f832d81422867c70d9510005f7714c941004ff745863002ebf74592200057d74d86520067f10d95200067e31d95200057d75983210857c754cb20146de53d8d21004fd764ca400067f32d951034f784054f20005fb7050f200067f6558132004fd7558620006f561c8630136bf43d9130004ff76504200047f75586422276c4254d422667c7654e40004fd76c86302067f41d95420077b75480200067f65d812102dec7090b20006bc21d9120024fe7558d202267e6454e20004fd71d8d4201fb76150941006be65d912040cff764cb211567e72d9521014fc731894015ef
  | 26 => 0x11cfd76501300247c75d8d102567e6094a3021d7e7158953006fb50d814241f6c524cb213c77465c8521006fb6098142006bd53d912017d7c7550931006bf30d91200067d6454f210067d6394a10096dc6358d20004fd75592322167c6550d100067e621815300fe672c8521004ff7518910006f960181320ccfd71989100067e73d95200257d7318953005bf74581310257d73d91530067e74d95102167c6550d200767f5358c200067c52d93210076e21189530067c5258e2021d7e7118953006df40d8d210067c5258232006f77159110015dc73509320057d711895302efa601814301cfe74d8f202063c6459252007ad42505203e5ee768c9210067c42189530067d7694a302276c4254e42004fd7558e20017db6050d302257c74585531f67e6194a302867e10d951000dee714c921006be651913001ebc6490a203e5ee72d8f210067c659891021f7b1054d1035e6d321895308ef431d85200167e6354e200067e411895327efa10d81410067c5258f2135e7e311895300ded768cb21004fd75d891002ebc40592200857c758cb202273f4254e420067c52d9320005dd73981210077b6518142004ff75591320073c651912010d7c7550a30004ff7559321195f471591320157e73d8553004ff75d9110006dc7359121004ff725864021f7410d855346f3c75509411fe7e6394a100067c40d963200df4714c91002efb614c110006fa3118142005f9708cb20006fb40d81321aedf51d8d2152d7f7358553006df6358121004ff75189430067e61d8e5200cfe71d91200defb72d81424b4ff725913202feb62c8120006bf6458d2027cff70591103d76c658c921006ee6290a3021f6e2154f210067d7654f20005ef7258141004fd7650d10006f770d8532024fc7558d200067d74d95210067f53d814202cfd74d85400067d71d9542024fc75584200867f76948201f67e61948200067d7654e40014ff764c1100067c6118252004fd73d932002cfd7118910246bc40591100067c52d853202cfd7058e10006bf64c8520024fc7558e401f57e71d82521fe7f32d95320defa42d81420057c7254e1000ef661c8720006dd5358c20136de4358e400067e6294910004ff75d89401f67e6194a400057f72585535157d76981532667f6154d10004ff75189415157f7358153006f861181420067f31d9542006ec21d89301be7e76d96321367d53d91300067e61d9252024fe75582420067d531894100dbc7150d41004fd72d813100df47150f21006bd6490b204e56e72d8652024fe75d8930005ec725012002cfd70592100057f7550920005ef72585402067e64d92521f7662194b2102efa60181310047e7654d42004ff7518940006ec5218930005f771591320067c5258c20014fd71d9131004fc7648530136bf31d91300067f65591321fe7e639
  | 27 => 0xc6350d4101cfe7498910004ff70593211fe7f3058e520067c10d96322ad7e7294a300067865181420067c62949100067d6494a200067c65d923237e7f6054d40036dc32d8d10004ff75d85300057f754ca102063c649493002cdc7650d30005df73485202e6be50d91200067f62949410067d71d9532015dc7348630006bf745913000cfe764c1102567c6494a302ef7b40948201d67c6550910005f77158943006f764d8532116f710d8540196f441d853202efb72181420047f7558910024fe75d8121004fd75d8f21005fb7059121006bf32d91200067c7118953004ff7650c202067d40d9542024fc7558f2002eef205902001cbc7458321004ff7158e40004fd75d8931004fc764c5401aedf31d8d210057d71d825215f6d538cb210067c5218940006f5614c4200067d63d865200cfc71d91202ad7e7294a401879f3050d410057f7558941004ff764c9101fe7d43d963221f771054d410067c7654d4115fe432d8532024fc75d81410067d64949100067c43d952102df87048620067bb41181420067d5358910004ff76c86300075f6354d414ddee72d8e42006dc42d8d210d6ed3298a30135dc73486401fd7d7398953005fb7050c20004bf74583210b67f5358e2002cfc7058f21005fb7050932004fd7650e104873c5250d410067f53d93210067e7654f210067d6294a30006ef7258d202ae7e629825215e7f5358f211fe7e63949201ff6c32d96320076f625895302dfa708cb200067f53d9320004ec7258d10007f3714c1100247c75591200075f73589530967f53582320057f758c820317ae20191200057d7598910014fe7398910006ef72589101a76e6258e520067d75d89100067f72d95100defb4098a4001cfe74d8121006fb76480201ee7c6590a32024fe75d91321def461586422667c6454e101aedf72d8d21004fd74d893135d7e76d95320057f7058953004ff768c9100067f6394921004ff75586300067c61591531557c7550921016ee634c9215557d76989531f67e6158652014fe73d932100cfe7158a4001cff76509210076e524c9210857e75d87201fd7c735825200df4714c1100def840593200bebf42592200067f62949310e6df3158e1003fb464505100067f63949420067e525864011ebd43592302057d74d925202dfa7090b200066e72d963228f7b10d9510135be76191300067c71596200067d6494a30024fe75591311bd5f73589530057f735825202cfe76d81312057c72d9542014fe76d8d42004fc7650f212e7ac20d91200057d7394b2102e7d7059620004fd75d814215e7f53d85320067d769493102edf7358c200d7cc324cb20024fe75d85430dfbb4059320004fd764ca100067f42d9632006bf645013008ef661d8520004fc764c52002cff71d91100067d64949210067d64949312257c7458153
  | 28 => 0x81422df6c52c8420386bf641814302dee7050b200067c42d9510004ff764c4201a75f6358953006bd6450a20004fd75d8d4202ded7690b200057c7254d2000777615865220df4715894325d7e72949311373c4354e4009cfd70d9120005f77158d421fe7c63949100067f40d9510024fc7518931007d9434c21014df571989410057e769491009ebc54d9120004ff76506300067f63d82520067f7559232014fe76509320067d61d815315ef753d853251d7d73981530067d61d8252024fe75d891001cfc74189300165e6354c202567e40d95200067c63d95200067e41d952031f7b53c82200047f7558a30004fd71d91322257e74d85530057e72d815302ebe40590202567c6394a402567c649482006ef651584200077a52480201c6bd4159321106dd43d8d401c6f431d854217e7e654c6200067f7654d20004fd751894102cfc7059131004ff75d91301cddc73585420a76e72949202567c7694a3002de87050920006bf6450530024fc7598a400067f6550a3201cfe74d8930004fd73d85423e6df6218d21076de5358c2000cfc7158a400067c74189530debc645932002cfe70586300067c63d9542014fe73d812101dbe748ca404a6ed3218943006ef62481100defa74d81422067d41d954202cfc7650e104a67e6254e4202cfd768cb2028e7f41d95101fe7c30d9632004f77158d200067c629493001cfe7458420004fd73d91100b6df3258e202257c741895335f6e32189530a57d76982520067d64d8e5246f3c52509410057f7050e52267784054c200f75f63581530067f53189400165e6354e422072f4294a4209cff7459120007757194b2121f7631d8553006df43d8d21014fd74d81430067e7694910007af645092002cfc764c6400073d53909420cdf4714cb200056c7254e420067c65591100067e769494102efa601812100cfd7690b21175bc745813108eef2158a1031f7852c8220006fb61d8142006ec42d89100067f75591100076f7254e2021d7c711895302e7e205962000cfc764c921006ee72d92321f774215865202ef61058630004bf7458d20275fb7058d10005fb704c920024fc75d911002cfd71d89100deee629082002cfe7650c200067f7558a1000cfe711894001cfc7458a100067f6558910006bf74591321873f5350d4101ebe64908200deb864c8120067b842181422676f2054e203deee768c921015dc73506302657c749815302f7a65c82200067c65581421f7743194b210067f41189531aef631586321d67c65509200aef641586200a57c75d8d20006fa7618142006f452d853209dbc7458d2000dfa714c210427d4321853202cfc7058d210067e7158e520067c4359620006bc63191200067d71189530047f7558d210057f75509300067f40189531afce318cb2121e7f6154d411a57c75591321879
  | 29 => 0x21e7e615855300678521814221f6c2154f210067c62d81530057d7394a100067f7018953024fc75d9120096df30d8d201557c7558121014fe7398a401be7e658ca2050d7e76181532073f419494221d7c71591530067c5258642004fd7650e201f67c72d9521004fe7650d2100cfe7198a40006df6418d21004ff75d912002eef7258a40024fc75d854001cfe7690b21006de74d8d210def943d8142004fd7650d20247b840504200067e6418953024fc75586400067c7654f20176bc644c520024fe7558e400067e7018953005df73485300067f70d95320067e21d952001eed7690b200457c75d8d100067f64582520cefa10d8121186de63d8d41004fd75d912000cfc71d81420067e61d95322073f4159252004fc72592300067c65581210067c7654d10005df73585400247c75d8d425757f76591530067f41d953200df67190b211f67d10d952100cfc7158a301def461909320067f6394b200077953181420067f65481102567c7694a1002edd3059230006ef629893102e7d10596200067e75d891002eec2098a302657e7018953166bc64c8530014fe73593210067d6494b20005bf744c6402073c6459252005df7348540196f461585320c67e725962003ebc43d91101aedf41d8d21004ff7258e402057c74d8e520067f64d82520067f40d9532005fb70508200d5fb70589300ccff70589101f67c6194942006df7358d200057f75581420967d6254e20005ef7250620005ef7250120024fe75d8d21004ff7558f210067e63d95212b57f7354e4002cfe7690a100067f43d9510016de638cb2001fb7715064021e7e6154e4215f6f534cb2100ebf765064021d7c7158953145dc73581212c778754802000cfe71d913228e7f31d95104d6bf41d89430067c70d96320d67d53d81320057d75d87200047d75d894321e7c6154e4200ef66148620006dc74d8d2101cff76593210067c52d8d20014fe73583212657e7018153024fe75d81430067c7558d21006f554d8532136bc4358e400aef621586203fdee72d93212567c63948200067c629815325d7e72949210def840d93200067d7654d4127ebd74d8141004ff7158c20006dd74d8d211d67e76d9542006fb5218142006f810d814200cfe71d9110004fe7650910006bc645853001cfd73d89432675d6354e100075f73585531fe7d73d95320157c73d85533e5de76d8d2146f3f53509411aef661d863207d7c754c8202675e6354e1002eee2058a30005bf745812101eee64909200247c7258e52004fc76485402073f4150e522e6be10d912001cff76501301567e65486201f77b1094a1000cff76486200c75f7354e20006f654d85322567e30d952009eee4258a40005ef724c620004fd73d8520024fc751894135e7f43189531f67f6094910024fc75d893035e7f31189530defb42d
  | 30 => 0xc41d954209ebf41d912002dfa7090820006f4651853200cfe7650110006bf71d91300067e75d8930006ee6250a300067f53d8910024fc75d85200077465d853200dbe7150d410167e6354d102273c6459153006de31d8d400067c6498953005f7714ca200057c7254d400067b5318142166bf42d9321007b8705094101cff765913109ebf40d9120006f761181321f7767194b21195f676d8532006f570d85320067f53591201c5f47158d4201ebe64503200057d70d92521ff7b3094a304b6ee32d89430057f72591530067d63948202073c40949410f76e7294930004fd75d89300ddfa7618142024fc75d91210057d7198153005f9708c820005ec72585402573c409494015ef443d853207d7c758c8201fe7f31d95320067c7558d2011e7d6454e400067f53d91211f774419494100cfd74189410067f5358642004bd74d8f200076c21189530057f7158e52006bc52d91300057f7558642006bf65d91301a57c755853202cfc76506300065f65d8d21006f961d8142006f830d8142016dc638c921006f565d85322157c75589430067d74189530057d75d8931006bf6458520007cd638cb21006f56148620014fc73d8142005bd748c94102feb7248020014fe73d91200067d5358321006bc64d8d20024fe755842002cfe70d85420067c52d813103779538c110004fd73d81421fe7f43d95320067f6358252006df73589100067e63d9542247b870506401f67c61d86520057d7418953005df73581410057d73d9520066f840189401d67c6550932004fc7690930006bf51d9120014ff7658e4201ef476505100057d72d855302df87050a300057f75589100067f65d8d200057f754c920426f73118931004fd7558d10024fc75590200067e52d81423879c30d91302073c42949422077840949404376c5250b210067f65485202ae7e62182522067c64949310067f10d96320067e43d95202073e749494114ebc6448520004fd75590200eebc41d91300067e61d9632004fe72d91300067f74d9521005ec7258d1035d7e7294a320067d7654e420067c52d89101afcf72d8d210dfeb4090b2001dbf7350d410edbc74589300eebe64d91300079f6450d300fcff7358d10006f550d85321aedc3158632004ff7458a300057d73d9252096df32d8d20014fc73d8941004fc76909101aedd41d8d212557c749825236ebf6019130004ff764c6402567c6494a20004ff764ca100beee76909201fd7c73d8252024fe75d853002cfc764ca200967f53d8d2026d7f7354d210067d7694910004fe76505301e6de63d8e420057d7298153024fc75589100067f654c5200067c42d953202dec7050b200067765185320067c52d9121004fe764c91015cf77158d212267e6454f20006bc64d893001cfe74d89312e6bc40d9320004ff7558321004ff7458c20
  | 31 => 0x95210067c5298a100057d74d8953267741054d100067f7458e5221f7641d8553004fd71189301f67f64949414deed4218943186dc32d8d41024fe75d8f210067f4158e52004ff725863001cfe7498a101fe7c639492018d7e75181410cef4215872030f6c529092028e7d41d9510006bf31d912009ebf43d9120006bf7458d10316bc4018940196df3158f210067f53d894000cfe76509210257c7258e52006fb70591320067f74d95100057e769492000cfc71189402567f6494a300067f654c110014fe7398a101b6be545923202cfc76486400057f75487201ff5e63d8e5215ef453d85320067f755913200dec764c921006fb63d8142005be761912001eec6490b200067f74189531acfd71d8d21004ff73582421fe7c6394b210067f4058e520067c5258e402667f6454e10005f870509210067c6458e522567f6394a200076e524cb212557e7018252007db634c110006dc6318121166bc645932116d7c7550b212067c6494a32004ff7359321006fb40d81210067e52582320def972d814211e7d5359130114ff71591100067f6494b2100de4714cb21004fd7690930006bd54d9130176bc6459131024fe75582320067d6158252006bc65d9130006be72d913002dfa708c82015ef773d85320067d6394a200067c7654e42004ff7650f2140def764cb211aedc31d8f210ef9f4150d303567f53d813101ebe6450c20024fc75591100077771581530067d7654e202576e209492002cfc7058e4209ebe72d91201f77661d8652006ec52189400067e61189532073f4294941004fd751891002e7f205962056d7f74591530067f76949411f67e6194a320076f6298953004fd74d852011e7f6354d401d57c7558d4202cfa76c81200067c32d95210eebe54d913000cfe76d85200067e7598910016dc634c1100067f6494b2001cfc7258642004ef725911019ebe64d913201cfe74586200e6f631d8530006fa2118142006bc72d9130016fa634c110005ec72581410a67d72d95200067f6559120066fa431814201cfe74d8f210e6f710d853000dee714cb21006fb70589100067c32596200067f655011001cfe76d913002cfc7650c2038dfb70585402057e74982520067e52d853204f79534c21000cfc715932006ef42158420006ba4218142136bf53d91300067f65d82320076e72d8e52076df3158c2001cfc765012024f7753505101f67c6194b2009ebc64591200067c52d894021d7f7658553006bd5459232005777158153014fd71d8131004fe72d8143004fd73189101f57c715825202cfc76486300067d53d814102cfe70d91214b67d53d894335e7d30189530077b658c1101b6bc648c920016df628c9320067d6454e100247e75d894324f7452505100067e70d9521004ff7558e4001cfe74d85200475f7354d10024fe75593212067
  | 32 => 0xdefb705932002ebf74592300073d74949412577a3094a100067d535842000ef4614852002e7f70596200067c52d91101acff71d8d21004ff75592100067d5358620004ff72592101fe7f3158e520067f7694a400076d5390b200875f7354f200067c70d95210067f6454d200077b65d8142004fd72d91100167c6354d42006bd65d9130004fd73d85400067c74d95101bd7c7550a32006f561c8720005ec724c32002ebf7459210006f652d8532005ef724c1201fe7f3258e52024fc75d81311e6bf43d9132116bf415921021d7c71d81530075c52d8d2114dbc74581210247c7558a40005f7714c9102277b4054d400077a52c82202567c6194a302567f63949300067f5398a101aedc41d8d210deee625082000cfc7158e40116bd41592100067c7558a400047f7558232006de75d8d21007bb744c210004fc76909311fe7c73d95320067c65189101f67461586520057d739492001f9f7350d410076f659092000cfc7158c20005f87050a320067e61592520076f7254e420eebe76191302073c425925249f5c528c932004fd74d8d1028e7f70d9510006f960181424af5f63d8953004fd768ca1002ee97218142006fa31d81420067c6294940006bd50d91301fe7d30d95320057e7650e521bf5f6398953006fa5118142006f561c84200edbe7498930006be65191201367f5358e4015ef772d85322877410d951021d7e71181530047f75591212267e6454e102567f6494940005fb7048520006bc64589300067f6590921247b44050510005bf7250d412c7ea5248020006fb10d81420057f754c940004ff7650f2002cfc768ca1021e7e6154e20004fd7650c202567e6094a3206df4714c8201f67d71d952102cfe7018910004ff7558f2002fd8304c120006ec52d89310067d5398a40004ff764c940004fe764c540004fd768ca402267e6454d2101cfe74d89102067c74d95420067d6590a20014fc73d8940134be76191300e7f0714c11002eec2058a402257e74d81530f57c75585300067f75d8d210067c4258e52004fd75d9130004fe7650f200067c525912002ef87518142004fd75d81321d67c6550a320067c31596200065f6354d41006fb609814101ede6450d300073d439494109fac64909200067f6558d2118f6e7294941006f754d85321f67f63949312267c645915302df8704c920065b874480200067c72d95103e7ce2118d211ff7830949300bfac4250a20014fe73d913001cfc74d89300067e63d95100047c7654d201fe5c639492125776109491000cfc7158d200067f755863030f6f53909201373d53d9130006f551d85320067c70d9532005df73585200067f6418953004fd75d8540016de6350c201f75c319493101ebe64507200067d5358720004ff75d91322067e6494820006de64d8d2121d7f71585531f67c31d
  | 33 => 0xc41189533e7d42118d210dfb842d814200cfe71d8d42004ff745842001cfc7258e42014fc73d891000cfe71d89430057d70d865200cfc71592300067c21d952000776525051052e7f6358553004ff70591310057d7118153024fc75d89430067c521893102cfe7650a10014ff764c921004fd764c4201e75e6354e422067c43d9542004ff7650530004fe76505200057d73d86520057d73982520067865d81421e67d53d91320067c5258d20004fd70d8532197e4714c92135d7e769493209df9709894001cfd72d854200df77450510014ff71d9131014fc7398a400f57c75485305557f735895301cfe76d91102567e6094a421afd431d86320063c6519120024fe75d8520004fc76c854035c7e769493203ebe64d9110006df53d8d215655f735915354f6d32d8953006f475d853201cfd70d85400056c72581530067e72d9510006bf64501203d76c528c9210073d5390a400067f53d9110004fd75d932025d7e7294b21004ff764c5200067c5258d10004fd70d93212657e70d85530067e61d95420067d654ca203e6df6118d21004ff7158a400067d53582420057c7654d21024fe75d8d200dfbb41d81420067f654c921004fd768c910147cc638c921006ef62909310defa64c82200075f53d8d21004ff7558d2002ebe405923001eee645092001edc6450d301ff6f3294932145dc73591210a57c7548520004ff7458d100247c7558232006f850d81420067e74d952002ef8634c210024fe755902053f7531d85531f67f62949210067d7598910006df74d8d210047c7654d420167e6354d42006ec62c811016e7e65c8620006fb60981431e4ff74591320067f70d9542007ea42c8120004fd70d894101cfe76d9121004fd75d93210ef9d73191303febd74189410067f7654e4200cfe7158c2002cfc7690820004fd76504200067d76949400067d64d82521fd7f7450e522e7b840182421fd7f7658e52004ff755902014ebc40d91210067f76949300067f65582320057d74182520057f72581530067d6394b21386be20d91300067c64d963202cfe70d93210067e7118953024fc75d8f212063c649492002cfc7058c200056c7254d42004fd75d85420057d7518141006f561506300067c62d8553006ef7258d2102cfe7058a100067f7558d212257e74181530073e525094114ebc405864202cfc7058e1003fb74250510024fe751893001eec645092002cfe764ca100247c7559232024fc75587202557c741825202cff71d8910006ec32189100167c6354e100077b609815302cfe76d814108ef710d85200067f6398252136be73d913000cfe71d8d40006df63d81210056c7254c200dfae6490b201257c7548540006bc7458d10006bd75d91300d6dc3258f202067c6494932006dc52d8d21145f57198931005f870509310067f73d9521
  | 34 => 0xd0024026089000018d7d60af000000800605a01c00002ac00003d007802201000e36d405400602300109ca0340000064178006000022400400100000f00c801a000810803e07f000004470e0000021ea4016005000011c01200e010004400600300100fc05200d015002800400201e002c02e000003800400a027004806000c00701f00314f21180e5000000000a00084dc03a00700d04dc02601a0170fec00200202100002d600600000080004c9006000c008001000000400000601180100024cb3940004000008003801000600101e800c0a601900200500500083458908018043001802c00603c048026400800000080c0010180000801c04809c01a800400200d01d000402a00001b806407e2a5018006c2a20000040090018006012000c00001c01500100180010000004496039000000005c00303a800001200400180080281e332980280000a0046808402e001000003c2da00401981d80a600402380640a6189a72801c00602c01501800b808f002812804800400c000807a000000000800e012002000400003f000802800415800000000b201b009001001600000000280d000b001000000e000037005c0ca32c00200b00240420090134004000018411400001700283d8010002003800c00400c00183040180160020018000000005007800c00a000803c3fc00900008a006a09e000003c00202c000002400e0000018150000208000804c1cc000018040c002006040003400000a00b000c0620002d1004c04805704b000003601900b806808401401985041aa08000000280b60ea0060000316001010801c000008000000800004e00600ac00200101782e410201e0060030000002003803405a000266039c0400003a4000c548031002000409000000680b000000b00080080b611507e026415606c00200b01800331b9073401601d00000f000205c055800c43e00000d0408072000002000401e000048000002002901e000885c11b007804800000500283d0012000000002c000000002005402e05fb009efc02000f00000d00020d2002001c014454000000000602c00380000b606e07d0000bc2000006001000800000283700c05f301a00e000009b009000801c056018803805260700080000460030010040024010004003803e087010001408c08900aaa0807a00001480083ca00d000800004a00005a800c3cc006002135c00000000000f4018007012002c0060020068000002326024fe75d8142004fd73189400067e41d96322175f63591531f57c72d9521004ff71591320067e75d89310067c6158e5201ebc6450932136bc53d9130006f771591210067f74d9632014fc735872014ebf42d9121024fe75583210067f658c920004ff70591323a6fa40d8143004ff7458f2001cfd73d8543014fc73d81210057f7550a200067
  | 35 => 0x1006001005c00a02200d400e00d03b007c00000101a800000600300bb4d013c00b00204702dc00100080040000050140000000020000008400404201500583b800200180f000000b00300700060000010000002010401049800a0720028050000083000007801e001013001c002005028001000000303c006c00009e001009401000000b003c00602a01a000cacc0010a10004046000000004401401a00a80540620020e1810400000300980e815a05300580043ba006016800003a002001aed80280065a70028054012015001401000401e000000202d0790004000029000801803e3a200100006c4005003000001c0021940000032000010000000402a008814864008400000000040af00200000260010000044002008000000001e061001000803e00e0009dd80060600bd5628024000005800c00204900f00000121c2004000c01007912e0020018002017801c01a04c00080ec00e08100b006c06c00000001680007a0007000401406802c001c0400bc0b703b814a0010110ddc02114c00600201540050a300981e2000011000000200100f8018008000001802c03c03f13681640a605a1f600400d800400000b4002085000800c0160050060008048044391938402e10b00e0064006002005002400000100200441680c900201a055e1a43f1801001201300200500000240ba0010004003002805801609700a836400a00b003801400000000d801c00e00a00000c80b40010c881240020500000d700c60be001800402d28a000005c0e600603a80a0014036000000c00e00c00200a08de00400400580961a8000812401c02a0018000046000000003c01c00001d0094002000013800003000006600040c8011007800c0c8089037015007e00000181e05ee191000817c0c802700c0ab40e2000017800c02601101883d80bc03d000002800003500700dc04c000002802401801b090005800c02a000800000801300e8260002000011000000200200000a801e016001007001001e0ad00000041fa014000019200002789c4052005016806c00e02f00000b00100000fc805c04c012001800005200001487782d600e053000c0002c2004000000000024381fc04001d00380002f2006003823400600101d8058360002000031c02109f0f1800000000f013801c000756002808000005c000000000400800d802001c029000054c000002000807800818700b838001416e00c802800000616d006c02c0d600181b80420000ec0060004011000185800e01576f807001600a0000040000894044808c04400e000012000004101680009203851a8815003a008000800c01c001000024c4541450000000000001002801001c01300380cc04800317688402280042df0000018098001000002400401b000c01e2c300403c000204501480300160000
  | 36 => 0x1010401a00200000584e403006c80000fe00e000000409e000000002400267c497000005c003298808c080001000005800000001480680000061c7803400c00000580100b600000003a406c002000001401200811e803c04a03400000b812201a002816c0161a62f3800401c1a302f003800000f00480f000a3af0018048022000002803801804d010803c07203400080480ce0000160768000005008000000e026002811912c00a00209e002403d000810808c00500b807c00a6ca00081e400001f000000402609a001801c00400a015000001800017a009002c019004037c00000c00400000fa000000000c07405b20c801405a00f0210730046004001010000000306d0040000039005000806001400100ac00000200f01bc0c600600080780be02500580f463a00400e001c00a00e008800002200901a800002800301a807400824b002004000801e000003c01a077000801001c0cb08f83c000004703f00140220530030014018073028800000801800001d1a181cd001023800e028001804810a01600300b00ce0010bf804c01a00002a800000a10e2a3833c000009035814000600300180100460090510000014008001000000c001000800415e00900181442a0000011002c01e0a2008001000c01f0000000014009000801000000709a818c00c009004000803e00100000280180000938000914218007004001c1ed05b88fc01209000e00e000008202d000c0980000000f0c02e000004801400600302c807c10201e14f814c03c000012800000600000901d000a16c000004c000002000006004001a000002800000f01d000401c046058000001e00700001ec09e00a01680f403a000015005005e1f70000030018019008012407000391c00180003a005700b4018029008004000800b004949008e00000b00000de02b0078244030000001001c00008400080000c200001d800000a003007800c000002004800000e00002d91601be04100400440340750008014000001010000400606a004819000000e04880240480091cc800007a01604b001c0ca1d800101a8008013009003013605a033001800600002e80a801e069006000c04a02e00000b800a00503c80080aa55c00700200c20000070020006034007803800000b22700480060090148054000007004000402a03c01a8014000013000000001800200480280060b30000020016007199001400000013300ec0121b500000000060030030008000025000006001a0070000080050008028400800000a00007ec002041000012c072012412005c00a02000380080340190021dbc00000e0008000058000003804401e00100281d8006a7100000b400800602183d003e00000d059000400000100000060111d78038002001000000803606f0010030000132001800000800500d007c
  | 37 => 0x6012011825400e07f00e800403602705e8ce0000005003007c00c036014023000200b01500940180000088748096023001805402c01102f0ac0066002000001c01217406000000fa0000078020000000000806408400000300180201ab001001c0020051b7003411a343006877c020016008002402c03b0028134000002000000800603000c8c5001000102c000000e000001016c0f002000e8178018133015002c2300db03c800812e00f000813036a00c0008000022002002805cd96011003808400003700000bc036017008000000001b000007401c00409e800c01094f04a0014006008003800012c01a006007800603704280000180000048000cfa0510000014002004043004c7ae03a075017c2d80050000049a8000063c80340000cf0d900707d20141f980a000e00200100180001790000000000003018815812205400000280080000e3804cbe401600300442d0420
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87d8718f65508b78dce5b0ec1290029d219535051067726188a431262579eb8750b204800187ae8320c4a98029b60c52189400061fba8c8b0a400087d859db214c0090fd0b396c6880023ba0b75d8f210243e428ed1922000c5f75dcd62440018d8ebb92c888003361cc705912102e743b0e0a124000a75859c3614c8010fd0e3aac8990021f61f42d96323845e436e8b0a60008bd849d943c80014bb06108c4a9803179cf659812100732308e4b0aa600c75719866054c0187ecbba2c4880030fdd26458e520053ac0cc8312a600a6e8210163948031e902baac8990029ba1b758c9210243e42aeca0840008fb805d5644807f4bd0730ac7293d71b58c7254e420043f43e65b2a2000a75819d953c80019b0c7b8284908028fe1572d91300043f43aa6b0c80b8c6d631c9538800147d0a39ec8900031d5c47118953006b2396c2b0aa60087d83dd562441010fd0f292c3210029e614631814200732108c5b0aa60487c87d4d61080014f50da9ec0a112b5adda52480200043ec2ee4b0c600087f855c763480010fb073b2a6880fe9720d6458e520053dc02c929264b7a6d83148624c0090f90e292c8880021fe1574d8d200051fc22c7292405ccb870d9142480018ecedb8aa6a08032dd93714c92001d56422c4a142000a79800c565880310fd0e192cb101af171cc52591101fe36bb6eb19642058f686dc520440014ed03382c72900a3720c76485300dc7dc02eca142000ab9840c460508014d904a9ac5080031ddd461581320053dc2ac63028400c77761c56254c051b906baac8880028fa16611912002c6e43ac6a1840d7a6e821d36548401c76a7210c0a10031b61772591100043f43ecab246400ae982103604c8010fb0e21acb1009b271cf64485300061e32ee8b1a200087e87d4d624400717908bb264883531bdc85258d210062e42ee6b2242008f9809d9424c4090fd0bb82c7908023de057558d2100636328e49824000a5d83149608c80147b0632ec8900031d90676949100053ac08c8b1ca44ca788059153484010ff0ab96c8980afb118d32c85210043fc2aeca14600487e85dd943480010fd0fa9ac5080029760f4258e5215e6a31ee299242cee6431148624c401958c8392c2980fe1fa1f42d953272d3b430a5b0a6400a7a86d4c60508010fd0fa16ca8816b1b9c961d82520243ec18eca9a20f4c6e72593639480117f08baac898002cb20953509410162e39aa6b12200487e85dc9618c0010fb0fa0eca902e31bdc8655813200637ba8e4b1a200487c8714963440010fb0bb92c9180021fa1f6558d1000537410cbb122000c6f851c964440010fd0e32ac8990031760e7654d102061e3a4a4b06423a87d870cb65508010fd0e21eca9092f0f5d052d81410043fc2ae9b1a2000a3f855cb64480014bb073b2a7908030f5d475d9130
  | 1 => 0x90abb285181128f2117654d1000536412a63122000a3e8408765480090fd0b3b284880129721d6354e420146e41aec90c8000ab984d4860508c517f0eb1485203a69ba0b65d923200c7a40aeab1c8400a3e849876548007974ec32640900ff1798f758c82002e74382c4a146073c6c7214963908ab0ff0eb14a50812f1b5c852d81210053bc0aeca9a2000e6852cc8605080717d09bb262900021fa1c525864201c5e422eab1a40038bc845d560c84031ed03baec7900121fa1772591300045f43843b22600087e8710d65880018f4603b2a6880021f21e525863000c5e432e89928200ab984dcf60508b9958edb2284900032e1d37058d200043fc2aec90c801887e87949608c84da3ce6a9c85200121f215711893000536c3443b12a60087f8754f624400147b0838ecaa125e97a1863949210051fc22c52922000a6d821006254c0147b0b986c890002ba20953181420043f438a4b1a2000c6e611c95308001968c9b8a64900032eddb74480200043f43821b2c64008bd87994644c0018eaedb8aa70809a2f21f644c12000477c12eca122000e1f5495363484010fb07baac50800327dd073591100053d404c3b2a84008bf845d563480010fd0fa0eca903769b60c52d89310052fc1aeca9a2000c6f53dc963440018bee73b2a6908038d19365505100043fc2aeca1a4000a5f835d953840018dec8392a7102769760f741895300537c12eca9c8000a5d83dd763440010fb0e186ca90b2733dc863581213855d400e3b226000c5d73d8e52484018e8c5b8ac0a98029760c75d8d100047dc3ac0302620487c87d4d62900692bb07396c0a98021fa1f655812101d4e43286a0a6000c5f751cd62440379d0edb8284900028f60c651912000637b20e4b02a604a5c87d8d53504014bb073b2a6908029ea1430d81420062f438ebb1a426ba5e86dd6324c8010fb0f986ca880029e61730d81422261e3a2a6b12200087d870cb6544001d4a84216c2990031dd977158d200243fc3ea7b1280bce2e2019464480814db0438ecaa10029ba08741895300c7b40cec9928000d3774dc56054c0b1b90ea9ac7080031758c7254e100062e3aee6b22200087d87043654c8014bb073b2a6a10022fa1b744c12060537410c3304a400c5f73d4d64484018f6a7b82c8908029de1564d85322543e43ac2b04a400a5d839d953c80950f90eb1ac129002ae61031d81420053b42cc830a640087e87d9563484d78b8e6292c8908028fa1663d91200062e3a8e6b224200ae582103614c80147b0810ac72900237e0d7558d216d53b42cca30a64008bf845d932440b9974edb2640900029ee1563d81420065c326e09924000a5d839c563948018d8ebb1284989021fa1e21d95420064e39ec890a400087c825d76150c958daed29485900023be09755911000637394e1b2c643a
  | 2 => 0x764581531f43e43ac6b0ca400a6c825d953900011df04baac72000317997734862000636308e4a9c8400c7575186604c86b9aced196c2990121f2157650a100061fba4e8312a60487e851d943c8401976ec3a24010003535ce72d96320051ec2cc63224000a5f8359252484015e102b18c0a10032b1d37258d100053cc28c7b028448db1811c142504090f90fa9ac8880023d60775d8f200243e42aec9942000a5c8559063484015b100b20c6908021fa1c43d95200053c42ac3b028400a6e82d4f6244001938e7b22c29000e2fa1f7458d20006563a6c490220008df835d5624419b8eee2292c6908021f61f41d96320243f416eab12200487e87dd5644840187eea3a2c4880021fe1570d8d420062f398cb3024226cb876dd1304400117d0f886c890002ba60a511814200637b1ee4b0aa600a6e82d006254c090fd0fbaac688002d920562189530055a43286a0a20058bc8759141080018d8ca39280900021fa1c52d8d200163d3b2a79024000c7765dc5635080149b06290c4980031bd977258d102553c402c92926400c3f7454d60c84018bec6392a6a08031d197715913267726108ca31a4200c5f751cd64440010fd0e292c3190032ddd37158d20005a6c18a5b126000c3c75d91614c00b1f100bb282100035add47050b2067d2f430a431a420087d879846054c014eb03382c7290030fdd274d96320053d42cc23028400b4d83dd6324840b9d0e0b1285081226e201744c9410152f41ec8a9e4200c7a75d8260508018bf0fb1aa69080327d9373585200071d294843028400c5d631c953081a559f04b28c6908023be097558d100043f43821b2a6400a7a85cc860508a10fd0e3aac2100028fa1663191200062e398cab0a8400cb474d85604c8051bd0fb9ac488002ab20965191300063a3b2e3292823ea6d821d365484015b10ca1a60880023da1c6158132006b5300e4a9840008fb87580605057d8dee4292c8900021fa1f654c9102051f426c7296400487e859d9214c0ab8f0e0292c8100173c1c161504200053c42ac2302840087e8790f654408927908b86c2a98021f61f315962000636b20e4a984000a3e82d4f64480651e90db8ac0990031bd4c7258d100053cc28e7b02840087e869d9534800165b0810ec4a98162f21d6450c200043f438eab0c640087e8719562440010ff0aba6c6908121f20973d95200061f3a8c9b126000c3c76d9153480010fb0fb14a4880028f61061d8e5215f6231c6590a4200c5f655ce428c8011ed0e206c29912a1f61f61d82520243fc1eeca9c4000c75711c7658c8014f505a9ec0a100393d4a52d8d211fc3fc32e7294403fc5e635ce52880011bf06bb2868818e9ea1a52c81200043ec3c43b2a4000a3e8418763948011bf06bb2648806f2e1937050920256b4384a4a124000cac401c964440090f
  | 3 => 0x4a984000cf3711c1644c8018dee4292c888003939cb63949210061e3aec8a126000c6c65dc940480090fd0fbaac919003179d463981210053bc0aeca9c8000a6c8258e524400153b09b86c6908031bd8c72581530051ec2ee5b226000a748550b614c8090fd0fbaac8990173a1c26250a304ed2ec18e0312a600cb471d91624c0874ed033b2a790003271cc64585200063a38aca99440009f08750530440010fb0bbb287901736add07050b200063bba8e2b226400e6672194614c8014dd05bb4a4a02fb1bdc865581420043f438eab224000a6e82dda52440010fd0e32ac6908fe97a0c40d963281e2fb98c4b0aa60087d85dd941c80010ff0ab86c6908030fd977458d200051ec2043b2a4000d36715d25250401c58c8290c4980021fa1f535912101c5f43ee8b12207396e82dd56190801976c838285908021f61771593200063dbaee0b224000e3574d94614c9994df07108c4a9803271d063581210051fc22e4b2c4000c6e601c96054c010ff0eb10c4a9803171d763581210043ec1eeab0c843ec3c7694942504011ef02bb2869006e6e21170c87200052ec1c42b1ca400c5f731d5618c8990fb0fb0ec0a98121f21574d8d100063c296ec9004000c9c64dcd61480014db04206ca99032aea133218142006563a0e4b1a200487d83dd953880071eb03baec6a080297e0d7654e200043ec2ced192803495d839cb6154c7f0f90cb9ca4900029ba0875189107671d426a630284a695f835c46254c9b87ae9a9ec0a0b1e9be0c52d89302643ec3ec9b02a6018f687dc56348001a72a638284a0803331cf72589100043ec3862b2c40bbc7b70149644808147d09bb4a4980030f1d86454d200055a40aca3226002a5e83d9153c8175c7084328c0a1002bc20563d81420655d424a23028503a5f835c46254c031ed0fb8ac8990031d9047654d100058ec18a432260c4c3e72d92524c0018e8cbb8ac0990021f61d6394a2000636c38a431262daa6f83148624c4011f700bb28690802ae60031d912000537c12c72922055e6972148605080199ee7b92c8880029b20953d894100637b28e4b1a203ea6d821cf6548401cd6ed29240100030f9cb64949200045f438c8b0a6000e2e7219464480018dc41396ca880023be1d62189107de37390c3b1ca40087e87cc765480090f90fa9ac5080030f5d052d8f200061e3aee8b122000a7b8558060508018beebb9ac6908021fa1f4158e520043ec3e63b2a4000a5d831c3658c8018e8ebb8ac6900039318f654c9210053ac0881b2a64d9ace82dcd63c840147b0b10ec8900021f61776c86400063bb8ce2b1ca43ec6c76949324840b1ed0db8a6488002ae61231181422acbd43ca4900400087d85dc963840014db0f108c4a98221f61c63d95100043ec1eeab22203fa6d821c563948014ed0ba16c2990031d1c
  | 4 => 0x394801970c8382c8990029e616611814239e1e3a0a4b1a4085a6e8218763948010fd0ea9ac4881021fa1f32d9542006b5a00e4a98400087d8710f6548001c98c7b2c649080395d9463c85210052f41cc9b2a420087f855c0624c47f8bce7b2c85190021fe1d6454d100061f3b0ca3224000c78751c164484018dce53b4a4980121f21576486306c637310e4a9e42008bd84dc1618c8019d0c438284988032d1c46458d2000477c3ac4312826bb4e82dd6324c837d50c8a16409036a9de0c65185320051f420e3b2c640087d859d932504010fd0e3aac8880035358c7254e420243e428eca12200487f875d762440018bf0fb1ca4908021f617725913000536412c3b02a60087e87149608c8018becbb9a42901130f9d1649895320717324a521640daa7686948614c8d78b8e6292c4880028fa1021d96322553d40063b2a400087e870cb65484014db05324c4a9ab257e0d74d89532543f438a4b14600087e87cc365508894ed0db8aa6a0aeb9a5c865181420063a38ecab2264028de839d921500018b90bb9ac8880021f616765093022536c30e4a9c8400d4f731c96154c998e8eca9a82880030f1d764509200043fc2aeca1a420487e86dd560508878ece3b0ec0a98029ba0b65509100243e438a4b24645587f8758a528c0954b90ca1ca49800317dcc52591102043f43acaa1440c6cbb70191624c0010fb0fa9ec4a0002ae61251181420043ec2eeca0a40c4a3d8314b644c0014bf06bb2a6100021fa1f30d952000636c30e4a9c840087e861da52440051b906bb282100032b1d372589100063c32ee0a124000c6d829d953508990fb0e316c0a98021f6177650d210052ec1ceca9a2000caf741c963440e747904328c8900121fa1b755852000726b18e4a9c8400a7685103614c8014db05a08c4a9b6eb9e0562189312ef1da0eca3028400f914350530440094b90eb1aa610002ade0565d91307253ac18a5b0a64d8e6732194614c8011bf06baac8908021fa1f41596200052ec1880b1ca400c3c65dd130480011ef02baac6880021fe0d75989100043fc2ae5b0a603f87e8759532880814db05b9ecaa10021f61f4258e520246e43aa6b1c8400a5d839d163948018bee6292c4880121f21c525863001c5e422eab1a2000a788558c605080b1d90eb1285080029d21564d85320063a32ee2992400487e87dd562840950fd0f996ca900028f614611913000536c18a5b1280bbc7a76194605084da38e6a9a83200121fa177258d100062fb2ae730242008be870c764480010fb0f986ca900030fdd774591200043ec2eed90c60038bc845db214c00155f04b28c8980162f21d54590200061eba8c9b12600487c855d062440018eaea3aec2990031d197714c11000657ba6e4b1a2000c6e821da52440015ab03328c6908036cdc47050941006b4200e
  | 5 => 0x80029e61671d81420053cc04c3304a469e386454f20480014dd05a08c4a98121fa1776909100055c422c03026402c5c73d4d64484e7878e8292c4880021f616768c91069f2a10eca31a4200a3e8599464480014f30a086c0a10029ea1673d81427b537410c2304a402c5c7354d61c80014f50b986c0a10163721d634c42000637b1ee4b02a600a6e821da5250511e8865296c299003175cc63d95201fe2e31ae729284edaeb82584605080187ae83a0c4a98022f613764c5200052fc1aeca9e4200ae88258060504010fd0f992cb100030f197745813200574c00643122000a6c8254e62840019e0c238284990029e61661d81421fc3f43c43b2a6448ab88059141080018ecea30cc09912f1d1c452591320043ec2eeca1a4000c5d731cf65509fd65d05b22c92912f1d1c45258d201f61fbb4a4a0c800caba84d486050819b66c238284a09124f2117018953256b4386caa124000ce471d8932500090f90aba6c69090e5da1f71589530043f43ea63122000a6e82dda524c0090f90a3b264880031ed977058d420053ac0880312a64a87d87d93609480317b09baec0a086f2e193705093000666398e4b2220058f487545618c0090fd0fbaac5180031e197705913228c3e43eca9022000c9c741cd6244037d50c921640901a3ca10a52d81420065a3a0e2b1a400087f855da32504090f90e292c3200029ba0876949310053741062b2c4000c3c749896054c81a5ce529484a100e2f21076505300061e3aee8b1a400087e871956050801878cbba2c4880021fe1571d8d400162e39ea6b222000a6e821c46254c010fd0e3aac6880029b2096454d1000636c36e4b0aa60087e8719560484010f90fb2a84880029760c75d8d2000726b9ce5b2c640087f855cb605047fc9ec529464990fb99d8a52c85210053ac28e9b0a6488e5431d97618c8011d904baac72015f3a9c970d93200146e41ae23128026ab980dcb644c0051f50db8284980029d205621895300696212e72928400a7b805d953508019c8e231264a00021fa087654d1021d3a40aeca9840058fa809d9424c4018d8c2392a6a10029be0974596200063c3aeec9004000c77761c56054c010ff0fb1ca4880063ea1b70509100247bc3aa3b0a6440a3e8408765508091790eaa2c9190028f60c52d91200051ec24eca9e4000c6e611c95388211a9ae7b14c4a99571e1c052591211ff2631eeb192420087f855cb64440014dd05b2c84880121fa1676c853043537410e3b2a8400c3f7414960c840147b0838ecb190030fd9774585200063abaea3b0a6000c9c74dcd6244001968e3b22c6900121fa1f75584200051ec20e0312a600a5d8314b63508014dd043b4a498177ca10a52181421fea7c12e729464008be87d9161480011f30e188c0a10028f21170189534bfa218ca51964200a3d84c416
  | 6 => 0x52ec18a4b1a2000c7471195635080517d0fb22869033b1b9c852d8f210043ec2ced19282b8c6f631c953880018d8cbb92c6880121fe1f53d8941006963a0e4b02a643a76819896154c014d904bb2a6a03d75398c7254e420047cc3cc230284008fb87580604c8090fd0b3b264a00031dd977159132006363a8e4b222000d4f63dc96154c014f50018ecaa10021f61c31d95420055dc22a430284008fb805d56448401c5ae4328c8900021fa1f41189530062e3aec69924243a768118b6154c018daeba96c4988021fe0d75d89100051f420e0312a6d8e5432194614c80187cedb22a6900121f21f53591210062fc2ee6b22200487e85dda32440014dd04206cb190021fe1d6454d210061fbaec8b0a6000a3d83d9764480010fd0e292c8990021fa1c43d95100047dc3ac2302840087d879d7624c4058bce6a98c4883b38e10b531814221d3a40aeca9c800487c855c7634800157309a98c0a11236a60870509410053bc2ac830a6400d64211c95348401976c838284909eeb3a1b734c9210243f42eeca0a4000acc83588624400b1b90ea9ac6100030f1d065581211fe2f39ac7304a400a2d840846254c010fb0e296c2a18021fa1f655813225536c10e9b2a4000c3c74195634800159d04206c6908029ba0840d95210052ec2ce9b1a4200ad783590614c8018dcec392a6a10021fe1f63949200062fc2ee6b122000cb471d9132480014bb063a8c4880021fe1571d913200636b20e4b02a60487e85dc963900a10fd0e3aac3200021f61e75d854335e2f318e4a9840d8e4e83148624c4014f30130cc0a9802b560f51d85300053b40880b1ca400a3e859cf6448175cd084290c0a1003171cf65591100061e326eab224000c5f75dcd64440010fd0c3b2a6900039519463c852100636392c2b02a6008bf87594644800147b0810ecb190029b60a6198953006563b284a0a4000c5c7319561480010fb073b2a6900034bd047254d421fea7394a5192640087d8754f62440018b8ebb9ac6908121f21573189100062e32ae73024200a3e84187654c8011f70eb28c0a10029d60464d8e5222597426e4a9a84b9e4c3214963080011ef02baac7200021f61f32d95202ac3f436ea9924000c78651c1615080147d0b986c8900029760c5258c2000c7a408ec99220038be84dda32840018eee230cc0a9b829da185218532006563a0c4902200487c855c462500014db0418eca900028f61463d912000666b18e4988400087e87195608c975c5d08290c4a010e9d20662d85530043f436eb1924200cf061dc1424c80b1f100baac8908028f61673d912000537416a63122000c5d75d4f63484035c90c99642908029760c1058e520062eba8ebb1a4283a6e821c563948014dd05880c4a98031719773585200063bbaee2b1a40008bf845d564480018deebb92c88
  | 7 => 0x68521c142c8401c9b06108c4a980297a1670d8d210056bc1aca30a640487c855da424c4010fd043b4a488162daa0b605825200477c12eab224043c74715856054c012db0c392a710003351cf71591210243f42ee2b1e4000c3e7619153480018d8ca392c68809b271cf645013000556422c43122000c7b75dc164484090f90ab96c6881b72e1d8744c1100052fc38ca31a4200c6c851c9644407fc98c7baa64908173a1c26250a106772a108ca31a4200c7b651c1635080147b07b28c8900029be097654d410056dc02c9b1a4200a7985cc760508014b90ab86c69080339dc87158d200062ec3ea7b1a42cee4f62148634847fa9cc4b9ca5190021fa1c65592322b52fc1aeab1c40008ee82dda42440090fd0bbb287900031b184725855300637390e3b2c6405ae88650b2048001878ea322c2981028fa1061592520071b3a0ca30a643fa5e83087658c8058bceda9ec6908021fa1f655913201c6f43ec6a1a4200a5f835d953480018dccbb9263100fe9b60871d95321fd2e41ac9292204ca5d839d5638800147d0b21ec8900031dd9771581325ee3db86a6b22406ba5c8219463485a9ccec4290c2990021fa1a7654d100053d416a63028400c7b65dc16150801878e832ac2900029761664d8d210043ec2ee2b244000a6e821d36544001aaee638ac4a98ff1718f758c9410047dc02eab226400aea820c460508090ff063b2a6908021fa1f53591200052f430ebb1a4200a3e84187658c8018daec392a71000297a1c52d8d210052f41881b2a424a87e8714962901994db07108c4a98030f54f7458d1000537410ed292802c8be871894250401c76cb210c0a117b4e1d1534802020716324a4a1240cee4e2119463484031e902baac6100031d1c46558d200061e3b6eaa128200a6d868846254c014bb07b22a790003271d3634c1100062fb1eeb1924200d69801c953080018eec7b8ac4a9a1e9ba0861d92520043f43865b2a2000a5d83148624c0011bf0eb28c690803995c421189530053cc2e62302840087f855d93284001c5ec8296c4980028f61463191200045ec26ebb1e4000e4e7219463484011f70eb00c190922ec201425051001d5643284a0a4000a5f85593634840b1e90eb0a83102eb9a108651814234794204a52164000c3d741d36548401ad6ea38284902e31bdc85258d2079e36b18e4a9a8400c5c76d8d53485f36cd05b0ac32900a9720f7654c20005b4c00e4a984000c9f74d8d60485998dec4392a6908121fa177650d2100656320e4b222056c7870d4d64080e70fd05baac321342b360a6418d210043f416eab0c800487c855d9434400155b05318c8900035aa007254c202543e43eca90a4000c6f641c9530807fa9904b9ca5190031d1d4715913200566c18a4312600487c855d943484014f700b24a49080317dd763509210
  | 8 => 0x6bb4a4a08028f61643d91200061fbaee8b1a40c2a6e82d8e609487f8b90cb9ca5190031be0975d893126c3fc1aebb12620087f8754e62440018bae639eca9000e2fa1f7458d1000637c12eca9c4017aae86dd142480e747d0d29484a10031b6177258d1001d57426c4a126200c6e721886054c814db04386caa10021f61e75d89430051f424e2b2c404ba768694b21484954f100b24a4100021fe15768ca100043fc3ac9292200087e869d953485cb4eb07296c2990023be09764c6400066bb98e2b1a4000a798394860509b54db06290c4988029ea1432181420052fc1aeca9a8400c6f53dc9644400169b06290c4988021fe1571d91300063632ee4982400087c8754d61900014dd05b2ec48820e9ba0871d95321f6363b6ca992425087c86dd56244001968e2322c4980031d5d751d85320072c31eca9822000b2c8254e429000147d0931eca900ff1718d73949200043fc2aeca12200487e87dd5619080117b0f886c89800e2f211701893100c7a40aeab1c8000d34741c56054c7f4bd06206ca990029ba16211893000596c2042312a600c7b65dc1424407f0fd0f10ac7290031b6187254e200053742c423128035dc471dcd32c840117d0e322c6900d7331db634c9210043f43863b2a406b87e87d9532484014bd0b326c69092e9d20865185320062fb2ee6b224200c757118460948d74bd06200c4a98032edd070591210062fbaee6b2242008fb87580608c8bbc7085290c0a10030fd97744c11000536c1063b2a845cdab741c1424800187ee7b22a6900028fe1571d91300062e418eca9a423e87c87d9542484a10fd0e3aac3180121f21576486400062fb2ee6b0a841baba86d9320480018dee9396cb190028f61310d952000672396e2b1a2000a3e84087654c8010ff0ab96c0988121f2157650d20006363a8c4a12620087d8754f625040155d0418ec8900032d1d061581320063aa9ee2b226400c6d7514b624c4014db04320c4a98121fa1676509300063bb2ee2992200087c879496190099ad0e0a9a85902661fe1d6494a320062eb98e7b2a200087e87195644840147d09882c7290022fa1c64585200043f43aa6b14804c87c875856054c01a70a438284a08029d60474d95210243fc18eca9a2000c6f631c96154c0147d0bb96c8980031e194705913278575c12ca3028400c3f65dd160484018f6cbb82c8908028f61731d91200072b18ecab0c640087d851d9414c0014dd05bb4a4a08021fa1c40d95212863c386caa122000d1c74dcd6054c8947d0830ec8a98033adc870591210043f438cab0a8400a5d83149638412f8bcedb28c690bab1b5ce72d963220716324a5212404a87e871496284001ac8e3baa659095b9a5cb53181420061f3a6cbb046400d4f631c96054c010fb0b3b242980030fd4d74d8f2039e1f3b0a5b226000d
  | 9 => 0x65509200047cc3cca3028400d38751c142504010fb0ea9ec4a00031ed97705913202c6e43ac6a1c400087e8754d61908010ff0ab96c6a0002da60e52480200a43ec38c7b2a4000a3e840846254c7d4790ca1ca4a080237a1c63581212672cb9aa6302840087e8714964441cdb50843828499002a7a1370d8d210243e42ae9b1a4000c74715d953504090f90abb484880028f6136394b2035e2f318e4a9c8400a5d8314b635056f2dd05bac64101a29ee0164949202b63c386a6b2242008f687d85604c80117f08bb286880021f61c10d954200536c10e9b2a2000c6f65dc964440bdc7682a98c0a10021fe15768c9100052fc1aeca9c800487c855da32440090f90abb465080028fa1864949200051f42042b2c400087f835d762504890fb0e30ec8a9802cb20953909420243e42aec99220629ba87dd120080090fd0bb92c8880022fa1f64585300061fb22e7292400087f855d9434408987ce9b20c4a98029d61770d853262e1eb9ec92926000a7485590614c8090fd0bb8ac7100029b21562189400043e43aa6b12200087e870c3655080317b09ba8c4a08021f61676485400a43ec3865b2a4000aea820c760508014ed0a3a6c2990021fe0f75591320055bc0aca32260058f8805d942841e34f50c296c0a1003175cf63949420243e42ae1b1a8202c5c73d4d62440051bd07bb484880021f61b7150e520053d432a7b0284efa7a8599460508014ed0b386c2990022fa1c21d91200052ec18a5b1a8000c5f73d4d6244001ccea5296c2990121fe1f53d891000536412eca9a8200a6d829906254c010fb0f996ca880029b60841189531fd2e41ac92924200a3d84dd9534818f4db06296c4980031b5c862d855300726c18a4312600087f8758e5244001c9865b2a6490017369c1638c82000667b98e4b22204c87c875916054c010fd0e32ac2900063d205764ca400243e416eab1220eea7a861486050801cd6a5290c0a10121f21f53589100043f43ecab0a8400c5f73d4d644400117b0f886c8901de8fa1864949301f733b16cb90a4200aaf8259464480090f90abb2621000237e0d76486401fe2fc32e729464038be84dda32440010fb0e21eca880ff1718d73949210045fc3aca3226000c77719856394891b650238284a0ac70f9db53d91200061e32ee8b024200c75711846254da38bcec328c6908029ea1432d81420051f42063b2a40008ec825d5644c02717b0e10ec8900031918472585530043f43ecab22206b87e82dd5618c8014f307296c0a10021f61c31d95200051f426e1b2c6400c7553dc563481a7c9ae5b28c690bf31b9ca61d8e5200477c3ac43128000c6c72d856054c01c6ea92a6c2992229de0563949210043f438cab0264028dc835d564484018f6a7bb240100029ea195318142006963a6e4b02a600c3f65dd1204407f4b9
  | 10 => 0xb264044c3c7454d60c84018db0f108c4a9803171d463581210065db20e0a126451c7876d9530441c3ca865b28c29900347d8f745815300526c18a43126202ace86d8d32484014dd05bb4a5180028fe117654d1025e36390a4b064200a5d8510363484090fd0fbaac4880031721773589100045f43ec8b126040a3e86d9252480015e700a16c2990031e9977050a20006363aee4b1a4288f4431dd632c84010fb0fa12cb100021f61e2158e521f43f43e65b2a423ea748158d61948010ff0eb14a4880038b193655092058e1e3a6a6b122000a5f8358a52440018b8e632ac8881121f60d75d854300637394e3b2c640087e82dd5644400b1b90eb1a87080029760c52d8f2036c5f43ec898240bbe3b60148644800187ae9324c4a98023de057650d2100795ba4a490040b9c6f631c953080010fb0fa16ca908fa9da0776949300061fba8c8b0a604493e87dd16054c018df0c392c2a990e9d2057654d200051f420e3b2a6400c6e85dc964440051b906bb284880030f19173949202c537416e1b2a4043c7471d856054d9dc9ae4328c690802bce0563d81420243f428eca0a6105e5461dcd6154c018f0cbb82c8908021fa1c75586420053bc0aeca9a4000c7775dc563484014dd05bb4a4988030fdd353583210052ec1eebb1a4200c5c73d9562440010fb0f986ca908029be0964949100052ec1ceca9a4000c5c65dcd644840b3d101bb285903829da1865185326fe73b90c2b026400a3d84c4365509a3caec6290c2990021fe1572d8d4100735c12a63028400c6c7518932500090f90ab96c6a080e3b2097558e4273574c14c63028400c5d75d8e604840117b0e10ec8980021fe1570189410061eba0e9b2a200487c855c062504018eccbb8a65100021f60f75591212053a432e3292823fa5e83187639480155b08108c4a00030f5d754d91200055cc04ca322400087d839cb6544001878e8312c0a98fe97a1b639492121c3ec1aebb126200c5f65dcd64441d769b07310c4a99321f61e7558e201fc3e432e72928400a3e86d4f64480958d8ed29284900029760c40d96326d53ac18ca30a640087d859d932440a50fd0dbaa40880031d1c564581530063dbb4a4900400487f875d76150c010fd0fa0eca99003271d37358d1000579c0ac63028400cdb73dc1644840147d0a196c89012ada20b75480200043f430eca9a4200c3d741936394801cd0a4190c0a10121fa1772592100052ec1881b2a4200a6c85588624c095cd2e5290c0a13029ba0a715962063d37416cb3046400a6d8210163948010fb0bbb264880af9518d53c85210051ec24c3b2a4000c3c74d9520440011df04baac8988030fd9774581320062fb2ee6b122000a5d8314b63480018d8e4292c8880121f2157650630006a7b1ee4b02a600c5c639d9534840147d0838ac7291ce1fa1f
  | 11 => 0x8c0998daeca9c85900021fa1f41d96320043e43eca992204ac7870d9542480010f90fb2c64880021fe1572d8d100243e42aed19280058ec87589428c1cfb508438285190021fe1571d8d420043e43ac8a9a4051a76811d36544001cd504290c0a10022f61272d85301fea7396eb19264008dd83dda42440e157708b00c0a180297e0d7654f20007943a4a490040058df8758e32840014eb03bb4a4982eb8e10852181426d637390c3b2c6400a6c8254c625044d17d0f886c89800317dce735962070fa2194a430a6400a5d83dd7634800147908b92cb100032dd937158d202061f3a6c9b1ca400c3c74d95624407d8f0ed29260883d29ba0b73d95424bf2bb1ca430a640487e85ddb218c0018eee330ac8a9b8ab960a64185321fd2f41e84b1ca400e5b8354f605080187ee9292c1908028fe11701895365e2f3b6c72924200c3d741d3658c8019a8e3b1a64902d75aa1e52480200043f436e2a1ca40caba84084605087f0f90fb2a84990122fe1d54d91200069a38eeaa128204a5c87d8d53484011d904baac8988030f1d764585200243e42aed1928200d5763dc56254c01a5880392a7210031d0407654d100043f438a4b0c8000cb8621c142504010fd0dbac64900031ddc671d963200733410a5b0a6443c3c7654d425048147908b1ca490002d360f758cb210053741080312a600a768119163948010fd0c392a6908fe1f21e52586320061ea9ee8b1a400087e8790f654800169b06296c49880a3b61c628c9400243fc18eca9a4000a3d8408565880954f100b24a4908031bdc85258e400051f436a6322400087e87cc765508019aee638ac8990033cdc7705913200735410a5b028400c7763dc56054c018eeebb8ac8990fe9720d62949100043f43880312a600c7953dc1644c8575ad06206c2990021fa1e43d952100537416e1b2c64008f7815d93244001c5ce5b24a4980121fa1f75586320065bb26e2b12600087f855d93190001c5885b2a84908030f5d07458e520043fc3aa7b12800087e871d56348401b56c438284a09cf0f1d05258d100072dc1aa63028400c3c765d2525040147d09886ca900121fa177650d1000536c38a5b126240a3e840c76550801c5885b2a851900237e0d711894015f6231ee29924200d4d631c953080010fb0e292c7100038b19365909200052fc1ac92922000a3d84c43658c80147b08108c4a98030f1d47458d10004b7410eca1ca44ca78805d953508018f6a7b82c8990021fa1c31d95420043fc2aec9922000a3d84087654c8018beebb1a64908332e19070509320043ec3c43b2a8400c5c63dd5634840117b09bb4650800359184725855300657ba0e4b222000cbb741c1644c8890fb0fb20c4a981297a1f6354d4135c3f436eaa126400e8c42d8d42484018bae6b1cc1290021f61f41189530243f42ee2
  | 12 => 0x31e19770509100043ec3aa73122000a6c825856054c01878ea326c6900028f61031d95200043f43881b2c640087e87103654c8090fd0bb92c918003171cf65585420069da98e0a12826b87e82dd5608c80187cedb28c8900030f197744c11002c7a43aa2b08400295e839cb6154c810f90f292c3210063d2057558d202af35390a43028400c5c751cd62440010fb0f21eca880028f21571d9120266b4382a6a12400487c8714961908375750810ec0a10032d1937158d200043fc2ae1b1a820087e870cb65508014bb073b2a6a00028f61661d91200061fb1ee8b02a600c5c73d9521480014ed02206cb190163e20175590200043ec2eec98e406b87c8759532880018df0a392c688002bae0953181422563d3b6cb9024000c7465dc532440014dd0418ecaa10023761e6518d210053d42c43b028400c7571187649480147d0b10ec8983331bdc865585320061fba2a6b122040a3c8458a52440010fb0dbaa431000237e0d755911001c76c16ebb1a840caba8414460508010fb0e21eca9080a3720d755891039e36b90a5b1a840cab88454860508018bb073b2a6a10121f21571d8d420152f436c6a9a8200a3d851c7644c001c5ce5b24a4900031d5c661989530063c328e0b1a8400a3d84187658c801c70ca326409000317dcf755863222537436e4a9a8400c6c601c953508010ff0fb1ca4908ff1b1db754c9210062eb2ee690c4000a788558f60508018b8ebb9ac4880034b6107254e4200726b1ee4a98400087f855da32900010fb0dbaa65102f38b90052189400063db2ee0a12406ba5e830846254c010fd0dbaa84880030fd97744c1200053d404c7b2a8400a6e82103654c8018dc423b2a6908121fe1c52d85430061e3a8c8b0a4005a7a800c565880014ef02bb2a7210021f61f42d95100043ec3cebb122040c3f765d25290801878ebb26c69009aae60071d91300243e42ae3b22403ea7481592524c8014f50b108c0a10031e4c07654d1000716320a5b126000a7a8518f60508014f50b30ec0a10033318c7258d100053742c43b12803ea748158e52480018eae238eca990062fa1272d854000556c20a43128000ad58199063484014f30bb8ec0a10024fe1170189531f53b40881b2a4200a6e82dd462440018e8c3ba2c2a980387dcf6454d200062fb18e4a9a4200c7765dc532480018daea296c4a01f2b5a1b63c852175537c32c4312a600c3f74149634406b5ad02206c6908038d9d365185320043ec2eeca122000a798314b60508e78dae4328c0a100353d8c72585530053cc18a43028400aea82944605080157108b00c0908031ed94705913200c5ec26eca0c6000c5d839d953484d78b8c6392a6a08022f613764853000637ba8e4b22200087d83dd564480e5976c238284a08021fe1d6454d200061e3aee8b1a200087e8714961
  | 13 => 0x51f430ca3224000e3953908605087f4bd07b26c7290029760c40d95320043ec3820b1ca4008bf845d943480018e8ebb0ac0990030fdd47458d1001c7ac0eea312824ce5a7354c60509a98dee432ac6908028fa106158e520062fb2ee6b0a400087f8758e52485b1ccae4328c2990121fa1f7558d210065c326e090a4000cb876dc142504019b0e7b82c8908121fa1f75591202ef1c216ca3028400e1f5394f644800317d0fb2285908029b60831596200063c3aee0b224000c3f75dd1624408147908bb4a4980029ee016454d210052ec18a4b1c8400a3f845c1639480147d09886cb190121f215764c6400051fc22ed29260038be87dd160c85630ff06baec4a18fe1fa1f4258e520045fc22eab1a200087d87d0565880014ef02bb2a6a10031b0807654d200053cc2e643028400d38751d120080018e8ebb8ac6908023be1d62189300063a296e2b1a404ac6c76d954248001878e9b2a60880038e61353181420152fc32c6a9c8400c74611c96154c0b1f100baac8990028f2117058e520043ec3cc2304a40487e859da32500014eb0ba0ec2990032d1d37158d200047dc02eca1a400087e87195614c9e78dec6392a6a11ae1fa1f654c9200243e42ae3b22600887d87d9762441fb8dce5b26c7290032ddd361581320062eb98e7b2a4307d4f73d896254c01878cbba2408800237e1d6418d211fc3e43ca4b046400ce4611c9614c00b9b0e0b1a86100023ee1d60182427fdadc1ac0302a600ae581108624408987ce9b26c0a98029760c75d8d210043ec2ee4b22623f87e8799163948018dee5312c0a980396d4e53d8142004bdc3ac0304a400a3e851c7644c0090f90ab96c8981028fa1310d95420243f42cec99220048df8754f63504018eae2308c0a98032e1d8705094100556c2043b128000a3d85984644807d0f90fb2a6490c07565cf6098153006363aee4b224000a76811d3658c8010ff0ab88c498002bce0164d853200574c1081b024200a3c855cb644c1f16d505b04c1290031eddb75480200047bc3ac830a644ca78805d953504094bd0eb1aa72100317dd473591210062e39ecab22423f87c865ce52484014f10ab00c0a10023de057558d200043f416eab0c6000a3d841c563948010fd0e202c7290021f61c4058e521fd2f41820b1ca440e2c64dd5424807f8b8e6b1ac329032aea12211814275e2eb9ce5b2c6450a7a801cf65440018eae330cc1290031758c7254e420051e42ae3b2260058fa870c460508090fd0b3b464a08028fa1621d91200051f428c3b226000c74719896054c810fd0f30ac9290029ba0b7694a4000c76412eab06423ea6d82dc36548401cb6a7298c0a13de9ba0b63182520043ec3cebb12820487e86dd5624400755908b12851800b331db734c9212d537416e1b2a4200c7452dc5644c87d0fb0fb1ec329
  | 14 => 0x685d07614c93b4bb06388c4a98021fe1d649492000636a98e4b1a20cfa5e861946348401878ebb2264900031d98b71589530053dc2ac3b028400a5f8559063484010ff0eb24a4908fa1f21b75581210046f43ec6b024286a6e82185649487fc9ec5b2c64990021fa1c10d95422543e43eca992400087f855d0624400147b09886ca990121fa17764c5200063db2ee0a124200c6f531c964440019b6c7b8284908022fe1176509100053cc2864302840087e8794961900014d104a98c0a10029e60c65181420055cc04c2322403f87f8758e60949c14eb07b28c2990031b9ca769494025c3f436eaa124200d3a521c142504994f501bb2a6a10030fdd764485300064fb26e690a6000c5c65dcd644400317d0fb2282980121f21572d81410061fbaee8b1a200087d85dc163c84090f90ab86c6908029e6037654d422853ac08e9b2a2000a3e8614b6448001878ebb22c6900031dd97714c9210051ec2e65b224000a5d83dd3658c8018f6ca38285190031ed9470509210061e3a6cab1a40008f7815d563909738dac6392a6100031e19770509322043e436eab028400e2d84148625000169b0610ec4a9803175cf63949200061fba4c4b02a60087d85dc563880018d8423b2a6908121fa1f7558d200047bc0aec994800096f875886254c090fd0bbb264880021fa1c1058e520062e32ee6b122000a5c8714b63484018dce4316c2a98030fdd764509300063dbaee0b226444a3e849d953c81b5c9d06108c4a98029760c5258e2066f2bb08a431a4200a7b8558460508094bd0fb1aa6909561fa1b75509202051f436c9292600087d83dd561900018d8cbb92c8880029760c5258e400069a3a6e2b02a600c5c73d95614819b8ecec328c2992c61fe0d75d85430062fc1aeca9c400087e870c565880019b6c63828490aeb8ed04521814200536c38a5b1280058f48758531080014ef0aa16c2990021fa1f65481100053740042312a600a6d82d006254c010fb0f21eca901ce1f21d6550a2028e3a38eca992204387d8718b6154c010ff0abb285080021f61c40d95320053b42ee1b0a6443a7686d856154c018e8cbb8ac6a10029d61664d85320053cc2e65b02844b96c825d660c8401878ebb22c4980031b54f7258d100243f42eed90c80cee4e31148624c4018dae4316c0a98031b1c852591307753d430ca30284b2e547158d5384001878ea3a2c4880163d21d61506300043f438eab24643ec77765c652c84018e8ebb8ac8990030f1d77459120006a7b98e4b02a63f87d87d9363948018d8e4292c7201675a9c96018252006363aec49928000a75811d3658c8018f0ca38284990030f9d065d8232006b3b96e2b02a60087d87887654c8014bf06b22a6909c38e94350d91300043f43ec2b02a60087e8719564440015cd04206c2993771b9ca61d963200
  | 15 => 0x631ecaa12eb9ad005218940196723b6e2992420087e870406254c018f0a5b82c8990028f61432d91205d734200a43128000c5c63dd54248401aaee638ac0a9802da209531814202c7c402eca184000c6d8714b624c4016d70b19240100029ea1463181420047bc3aca30a64bde3b60d4c64480010fb0dbaa85100021fa1c52592326f72a38ec6a9a8200a7581993654c87f0f90eb22c7290d63721b73581210061e3a8c8b1a4000a3d840c765508010fb0f98ecaa135a9ba0873d952100537416e3b2c6400c7475dc563440014eb02380c4a98029761670d8d2100536c1081b2a420087c87592524400159b04206c69080353dcf72581532563a3b4a4a0a200487c87149618c8010fb0e206ca908030f1d365585202243ec1aebb128600a3d84c406254c010fb0f3acc4880029b20953189400056dc1ac23028400a3d851cf64480014bb06290c49880399a042118953006b2390e2b02a6058f8805d5644c4015b700b20c6908029be097654d210043fc2ae5b028650c7476d9541440018eaedb8aa790aeb8ed04651814200637328e498c4073c3c7414960c84014eb02202c7291030f1d16458e521fe2f31eeb1942040e2f6294a42508818d8edbaa84901736a1c364509207953d434a5b02840087e871d5644840b970e0b2285100023ee01765091000637308e4a9c8400db0711d1304400187ecaba6c1190032e1d370589100063b080eca9a20c1a7b805c965880018dce4316c0a98029760c75d8d420061fbaec9192400087d85dc563c807f4bd0710ac7290121fa1b75581321fe2e31eeb192420087d859d942440010fb0bb92c68800e2fe1d74d8f200063a38ecab1a4000a76811d365480090fd0b3b284988029760f6454f210043ec28eca1e425cab880592420800147d0c290c8900029da066498953004b7414eca1ca43f87c87d9632480010fb0bbb464880021fa1f53591100052ec2cc831a420487e85dd931c80014f30632ec0a10ff17dd97394a320064fb26e690a4044c3f76d916454c018b8e632ac4880121f21572d91100047dc3ac0302860087e8719564480090f90ab8ec9190038b5cb65191200062e398cab224200acd83148624c5cb4ef07296c2990021fa1f31596200053cc2865b028400c75711c7655087dacce32946590ae31b9807254c202e55d40063b2240bae6b4214860508019d0e5b82c8880029761f6518d210043ec3e82b1ca400c3f75d9142480090ff0ebaec4988021fe15764ca4000536c2042312a6bce2c4014862500bbcd2e5b28c0a13be9ea1a52181420243ec18eca9a8400c7b65dc1428c8018bae6a98c4880aa1f61c63d95210043e412e7b2a200087f855da325007d4ed04328c2990029760c525863200716b14a52148000c6f721896154c010fb0bbb262903170fdcf64949300052ec1880312a600a7
  | 16 => 0x2586300053d42cc7b028400a79801c46254c014f30018ecaa10121fa1b75581210063db28e0b22420087d87ccb65484010fb0e200c4a98029760f71d96320043ec3861b2a8400cad641c940c80090fd0bb92c7080021fe1576909100043f434eca9a840087e870cb65480011df0eb10c4988030fd4f7458d100061e326eb1924000c6d641c953880010fb0fa9ec4a0b5697a1852d8d210043f438cab0c640487e87dd561900010fb0fa9ec4880021fe1572d854000536c30e4a98400087f8754f6250401878ebb2242980038b1096550a200043fc3ac7292403ec6d7694a32c840147d0818acb100031358c7254c200053c432a7b028400a7681dc3658c80157301318c8900032ddd07158d200063a30eeab0a6400c7b651c1615080117f08baac1908030f1d0655813200574c1062302840487c87d4d6190001a3ee9b9ac0a9adb6a10072504200047dc3ac63028400d67721c56054c015d100b10c4a08fa1fa1d65486200063bbaec2b0264008ef875886250c014f10ca98c0a10031d197714c9210243fc3ea73122000a6c8259252440014f50b318c0a100e2fa1375d8f200064e3b286a0a600087e861c9534400195cedb2484900021f61f42d95320052fc2ae9b1a4200c5f7558e32080014f700bb2a6a08121fa1772591310243e42ae3b1a800487e87dd5618c0011df04bb264880121fa177458e200043f438cab1a840087e861c9534800127f08b86c2a99a31e9db65181420071742042312a6018bc8759141c80015730838ec0a10023ee1d601814221e3bbb6c2b0aa600c5f65dcd6048401938c9b9a42903a29ba0b6550a320065a326e2b126000caf64dc9614c00117b09bb46488002da20953d81420061e3a8e8b1a4000a7a85cc46050801878e832ac4880021f6177258e400051ec26ed292605cea97290860508011d904bb286880030f19375485200064fba6e6b12200087e8714961080010fd0fb2ac299002ba60831d814221d3a40aeca9a8000c6f651c9644400169b06290c4980021fe15764c42000716216caa126448ba88050941c800147b0938acb100021f61f41d95320052f410ebb1a4200c7b751c1644c8019a8e2b1a65100163b61e6290a3000716314a4a128200c6d861c953080011ef02baac8990031d1977158d2000536c2442312a600a5e85990634849787ae8290c4a08030fdd764485202061e326eaa124043c3f7654d41900018d8c2392a610002b5e056518d210046fc1aeca1a4200c3f7414963480090fd0bb8ac910002b6e0d61d81420053b40cc9b2a640087e8714b6348401a5ee8392c0a98021fa1f6558910006abb1ee2b02a600a6d82103658ca01ab6e7b02c0a980297e0d7458e520064fba0c6b024200d68751c142c8019970c838285908029e60031d95200043f430eca9a2005c78605d660508018bae
  | 17 => 0x9c40bae6b4219460508018eee3388c4a98023d61e65185322653c402c8b02a60087e8790d658800147b0838eca99002b620164d8d210243e42ae5b02620087d8790f6548401a5ee9b92c0a99028f21163949100243e42ae031262e8a6e82d95648c8018f0cbb828490af38b08065191200061fb2ee8b1a204b87e86dd532484018da643b2a6908031e14b705912101c5f424e5b0a6000c3c65dd163480018bee6a9ac3902de9be0c52189300243f42ced2126000a3d850c764480011f70eb00c0908031dd4f71591320043f438eab1a4000c5f75d8d60484e1b36e838286980121fa1f7558a4039e1f3a0a5b1e40038bc845c3614c8018e8e2312c0a9803351cd61486200051f42e63b2240008ec825d9319000147d09886ca990030f9db649492001c7743ec4a12620087d85dc9619007f8bcc4b9ca5190039918772585530063dba8e0b224200c3f749d1658800117f08b86c29915b9a9cb53181420246fc3aa7b1a42008ef825d563484011eb0f320c29912b960c3654c1200045f43ec8b1a4000c7471d9563508e1938edb228698003175cc63d95102261e3a6c8b02a6008bd879946448001c9b06290c4988029e61431181420052f42ce9b1a4200c7671196604c8014ed02200c4a98121f21570d8d420061e3a6ca982400087e87d95428c8014bd0ba16c6908167aa1f70509200043f43ecab0c6400c7471195644c8010fd0fb2ac29000e2fa1376485300072a30eeb1926400c9f741cd62440018e8e232ac09932a97a166518d2100537410ed29220018f4815d5644c0010ff0eb24a499002b560c40d853200477416ed1922000a77815d953500014f50a086c0a10163b61e6290a1000637390ed2926200a6c825d9534400156f08b86c29930a9b20973596200069bba0e2b02a600c7975d82605080717908baac488002b660c40d81320063a32ae33026400c3f75d916348001cc8c2108c4a98030f1d764485200063c328e0a124200c6f825d7624c0014b90ab26c690802ad21170d853201e563b6e8a124000c6f825d762500010fb063b4a4880029ba1621d89300252f43ac6a9c200087e8714964484014f30a18ec0a10021f6177458e2000734412a63028468e386494b20480018db0e296c4a00029ea1771d81420053b408c9b1ca4008dd8799063484018e8ea38ac6903a69ba0b6590a3265e2f396c72924200c3f7414962440019e0e3b82c8990029ea1431181420053740442312a600c3c74d95634400187eebb22c4980121fa177650910006363a8c5192800487c87d4d61908d7a9ce518ecb190021f617769091000556c1063b224040a3e8498564948010fd0e292c6908032bd9072585300063c3aee0b226400c75711c765480010f90ea9ac5080021fa1f535864200476412eab20404a87e871d56284001ca8cb190c2990021fa1e5
  | 18 => 0x89c58c8a9c84900121f215768ca400655d426a63028466a6e821c365508010f90e314a4880029b60b10189530066a39ec290a40008df835d941080014bb0ba16c69080297e0d7654d410062e32ee690a4000c6f861c96054c010f90ea9ac3210023b2097558c2006755414843028400c5d839d9534800195ec8392809038eb9e09651853200637b90a4b1a2000c6d8714b624c0018b8e632ac0908021fe15769093100c7a40aeca1a400487f8718a52440014bb073b2a6a08031ed9770509320061f3b0c92924000c6c75dc96348001878cbba2c2900029ba0870d96320655d42062302843ea3c865d252504015e302206c090803171cf6558121006b43a8e0a12400ccb8641c142484ab0fd0dbaa429001297a1d6354c20006363aee4b1a2000aac82597644c0018beeab1c65080030f5d764d893035c3f416eab246400c5c75dcd64484018f0cbb82c6a11028fa1071d95420047cc3cc63028400c6c851c963440054b906b22a6908028fe1163949100043ec3e64b2c400087f855c764480011f700baac8988029d61440d85322543e43ac8b04a400a3e84c406254c090ff0ebacc4880028fa1461191300dd5dc32e12148000ccf731c963440010fb0e192cb100029760c74d96324463b3b6ca30a6400c5c75d8d42484018bae631eca908029be097654d200063ba9ee2b1a4000a5d8314b614c0090f90ab96c2980030fdd46458d200043f43ecab02844b87e87d9521480018b8cbb9ac0908031e1d770591210053bc0aeca984000c5f7314964484014df04b9acb1000359dc8715895322716322a6a124000a79850c3605087d8e8e2b0ac1290021fa1d5358a1000537c12eca9a800487c87149608c973a9cc6392a6100022f61c31d91200053d42e63b028400a75819926254c018f6ca38284990021fe1572d85430066db98e0b224200e385290860508014790ab96c890003179d763981210052ec18e3b2c6400c6e729da524c4014bb0610ecb190023e61c31d81420047ac0cec9928055c7870149644c8014f30b31ec0a10121f21572d85401f53b408e9b2a4200e2d840846254c014db0538acb100021fe1571189406ed37c18a5b126269f284054e42c80014ed02380c4a98029da0440d95320043ec3ea731220e1e6572d94614c8018dce43b4a4a00d6f120d718cb2121cbb43ee2b02a60087d839d953484ab6d50f292401000297e1570d8d210152e41ac8a9a2000a6e821c7658c8090fd0b3b464880021f21d63949100063a38eca9924000a7a850c760508018dee4312c0a98029760f70d963200636390a4b226200a798598c60508018baea31cc0908029b21562189310043f43ecab046400a3e841c46254c01938e9b1ac0908028fa1431d91200061e3a6cab02420487c855d942440014bf06bb2a6a00028fa1463d912000636308e4a
  | 19 => 0x29e60f65181420053c436a7b02840087f835d762500010fd0e292c8900062fa1f64505200053cc04c7b2a8400c7565dc532880018beebb1c64a08034edd470509410055cc20a2302843fa5e831016394801b50c438284a08030f19375485300063a3a8c2b026400c6c209cb65440054b907bb2a7080121f21f535912035e2e318e4a9a420487c855cb644c40317b09bb2831036b99cc421189530063bba8e2b1a40058f487585410800147b0931eca901ae1f2087654d200052ec1ceca9c8400c78751c1644c8018d8ea392c6880031ba187254d422653c402c8a984000c6d749cb658c8018b8cbb9ac2a10021fa1f53584200243e42ae5b0a8600c6c72149634400b8f0e0b2a85100021fa1b754c9101ff2631ca49924200ad583990614c80197081b82c3210029e21b531814200476412eab1a20048bf87553644c0018bae6b1ca510002dae15324802000637430e4a9840038f686dc53250481878c9baa84980031b8c87654d210052ec1eebb1a840487c855c7644c801ce6a3288c0a10029ea1671d81420053bc0ac9292640487f875d7625040147f08bb2a6a000317dcd63582520062e3a8e6b222000e5563dc553840014ef02b10c4a9c2747dd3735915302c7c402eca1a42c3a6c825d165880010fb0f996caa10021f60e769491035d2f434a519264008f7815d5644c0090f90ab96c0a19774e1d25248020316d4200e4a06404a87d87d8f60948014bb06296c6909af1798c7254e1001c5f426e0b0c6400cb774185604c9958bcec31ca4908030f5d074d95320055dc02ca3224000c6c601c96054c018eaebb0cc0991ce1fa1f65509321fe2e31eea992424ad687094942c80bdc7084a98c0a10029e20953181420053cc04c3b2a8400c6d87148625000117f08bb642980025ba187254d420053cc2ce7b028400c7865dc161508010ff0abb283180021f60f75591320061ebaea9b2260a695f835c76054c010fb0b396c6880121fa16764c9410061fba0c4b02a61baba840c760508015e700b20c2990029ea0071189530243fc3aebb12600087e829d953440018dcc0392a7210029e60f65d81421543ec3865b2a420487e85dc961900010fd0e32ac68841ad3e0d621895300637b90a4b22600087d83dd561080010ff0abb243180021fa1f615825200637100eca9a4000a5f835da52504010fd0fa12cb102021fa1e525842000476412eab222000a3e8518c64481d9c7683a98c0a10030f9d764d89300053a432a790a420087e82dd563440014f300308c1290031d98b71581534043f43ca4b0c64008df835d9424400187eea3a2c6900030f5d074d95200052f42881b1a4200e4d631c953080019d6c438284988021fa1f6558d206e567c1ac43126200a3f855c764480014dd05bb4a5080031ddc671596200063c328e0b2242c8aeb80588625
  | 20 => 0x3ec2cec9928000c3c74d95604c8018eae230ec8a98031b5d452d893000637308e4b0aa65587f8758a5290111ca8c729642908023be097558d207253bc18a5b0a64028de87dcd64484018bf063b2a6908028fa102158e520051ec28c3b226000ad88358760508bbc7683290c0a10fb591c6524cb215d636390a4b20400087d859d9424c4019a8c7b8a8490802ad20565d91301fc3e436eab0264018ed82dd760484018f0ca3828519003351cf71589100061ebb6e8a9c8000a7a85ccb60509738d8e4292c6100029b20953d89100043f43ecaa12200087d87103658c80155f04b2ec898003599c7758cb217053bc1eca30a643ec7471d95324840147b0818acb100021f60f7558a400052fc1aeca9a42028ee87d8932500014eb0ba16c2990121f21572d8d400043f438a5b1a8400e2f64148624c00147d0c322a6901030f1d1645825220717b16cb2128435cd471d8d32484014dd053b2a7908030f54d74d8f2002e5c382c8a084003aae86d91424800117f08baac4880023de057558c2000477c12eca1a201bea864dc142480018e8423b2a6908022fa1c645893058e1e3a6a6b06420087e8714b634408947d09bb2a6900021f21d5358a400071ba8ca3b224000ad583994614c8010fd0fa9ac52015a1fe0d7654e20005a6c1842312a6048fb87543605087d0fd0fa16ca908030fdd7644c9200046ec3881b1a4200c5f7358d61948054bd0db1aa690afe9ba0874d95200043f43ecab1a8400a75811d365480010ff0fb1ca4a1002b620d61181422e5d4422e12164000a3d8598f64480011f50e18ec0a10029b21953509200043ec2ced2126000e3b6519320480011df04baac8980021f61e43596200043f43c42b2c4000a778158e52480011eb0e206c2990163e2017650a300146f43ee6b22200487f831d95350801878c9baa64900031b1c862585530063ab88e2b1ca400c6c651c964440010fb0bbb286880035a14870509212fd3cc34a5904404b87c875952188019d50c838284900031d18775509320046ec1cec90a8000d6472dc56054cd34f700b22a6900031ba177258d100046f43881b1a420caba848c460508018d8cb3b484900030fd907254d200043f43ea6b0c8000b1d8314b644c0012f70eb00c0a98021fa1f30d95210243f42cec90a8000c5c7359521880018f2cbb8285100029d616641853200739a8ca3b0284b9e4e83148624c0014dd04208c4a98029da06641895301c76c38c5212623f87e8798563948014d904a9ec4a00029de057654d2100726b1ee4a9c84b3da8744c920080014ed0d29282880038e196421814200c5e432e91928200c757118763948014f104a9ec0a10038dd4651d913021d3a40aeca9a84008bf845c0624c47f8bce7b18c1290028f61071189530053741063b2a4000c9c64dcd214c0014b90aba6c6908
  | 21 => 0x8418764948010ff0abb282100031b9c876949303865c386c8a126000c3f75191624c0874e902bb2a7210021fe1571d9232006abb9ee2b12a651a79801cf65440018ecebb0cc0991130f1d164581530051ec2c43b226000a5f8359153440010fd0e3aac4880031721f6354d210243fc3aebb1286b4da8748c920080018ece3b2cc0991331b1d953509200243f43eeab046400a3d84dc3658c8010f90cb9ca4881128fa1b6454d2000578402c9b0a640087d87d0b6548001a76ea3a2401000317dcd53589100243e42aec9948000a3e85ccb64480090fd0bbb2839036b990c421189530061e3aec9192403ea7681d8f61948018e8e3b2ac0990ff9318e528c9210053ac0ee1b2c640087c8759153440018d8ebb1464a0002ae61332181420243f43eeab2220bce2f6214864481c94ed0d296c2990028f6106158e523155d41484302843f87c87592528c8010fd0e32ac6900034ba107254e4201d57436c92124044a3c845d9534818947f06296c8980032b19372585300043f43ecab22405187e87cc36544001878caba6c11900317dd463581210043f43aa6b084000ccc73dc964440014dd043a6cb1912a1fa1f42d95200052fc1aeca9c84d8a6d830846254c014f30b108c0a10032b90072591100051fc22eca9a4000c77655c6604c801c6ae8328c29912a1f21f655092000537c12c8a9a2000c3c7419563440014ed0b326c2990029b61c52d89300053ac0881b2c6400ab98488460508018deebb92c6883ead3a0b6358e5200578402c830a6448ba88050941480090ff0ebaec4a00028fa1661d912026e1eba6a63128200a3d84187654c8375750838ec0a10021fa1c5258d200057240ac431260018bc845c36150801caec7b8aa6a08029760c52d8131006a7b9ee4b0aa600c3c641c953480014dd05ba0c4a98021fa1b758c9100243ec3cc5292200087d87043658c8010fb0bb92c8881ce4fa1e52509410053ac0881b2a4200c3c75191624c07f4bd07322c7290031e1977050a320043f43ecab22426b96e82dd5618c8015ab02206c6908121fa1f658c92026734b92a63028400cb8641c164484010fb0bb92c90800395d96321853200637b90a4b226204a5c8758d5384001ccce2108c4a98021fa1c30d95210043fc2ae63122000a6e82dd3658c801aaee7b8ac0a98030fd4f7458d201fe2e39ac6b04a400c5f85dcd64484018e8e33b2a7908031b61c52189300061fba4e8b1ca40087e87d9632441074dd0430ac7290021f61f30d9542064dc422e19084000cf0711c1644c8010ff0ab96c8988029b219539092000637308e4a9a8400acc8254d63080018f6eca9a401041317dce62585530061eba8ebb22400087d870406254c6bb88e3b9a64908121f60c7654d2139c3f43ecaa124200a5d8314b63c84018bee63b2a6908021f21d6454d21004
  | 22 => 0x5900000100e00500200300502400000100000000001a0000000090010010010180d000713600c00f3080570000c001201400001740a01b00600002700504e03c00018e00003e00000301e00a01e00600000300002800007e0172230004d600d00701a00800900000000800000301000e01200002f0160052dd01c02251500700500f0070b600b32e00601d00b04200100100900000300000f00701300102c00400000100c00400300900501a00301600400e00d01500702200100000d00000600700a02900401701e00200300031200300e01b0a100100800b0000080085590080090f200301000a01c03003e1b900b0a100302800f49400000a005bcb00901826c00600700f0720090100310020c904900000407e01256901958200302f00b00800500d00700007d00000101d02100906703b0034170045e907000700901423400200900002900f00901c00501493e0000440700f300007c25301333205c00b00089b03100100300b1a101300000110e17101d01b41600f05707404100100054e00300501700000f03b04900200042300200000603e04500703d01142300400800104500014e02b00929600000103b0010010030390100920110a900000000200036473f4fe02700000001300000100100400a0060000016cb00000905c2dc2b70010030000106f100200401304900000408300100000f00400401500000001305905404a00b00412300600500202500006319c00a00401c06300128d00905900301401503f04c01404184900100700f01e0b62700000050110030840080040040000004a903001000d00900009b00202400b00700303210d00200700f00345501b00300002401500b00019b0b800500700101000108c01b00000e0030b417a00100200300500005400600204500006d78e01e01600601900e0b301500c01604401e0b803f0000aa05700400300002c00e78b01004601100000202c00000100700c00000000803d17a005107020028ac100000005600402001d0000060043d602d00200200d00204a00200d0770dd01602300c0020040111d904302a0000af16400102002501a00602502107d51102e08c0141c528d00d07f00d07401e1f400602100900200402f00700001000404500000400b00200611e0810080008d50070a41cf1eb0060000a400100100400f0080270159ce00000501d0ed00001c11100101400509800700301c00d02e2ac06a04a6d53360000080004260090310050043e43aa631220d8e6432194614c8019b0c63828490c0b55dcf61585530055cc0c843028400af08050b614c80b1f1003b284880ff9398e528cb210043e43aa6b084000a6f825d953440014bb07326ca908030fdd353589100053d428e7b0284d8e6731148624c4090fb063b2a6900029e61621d81420061fbaec8b0a4040a3e
  | 23 => 0xa02c00075200001202800300607c24600011200d33e35504700000700724e00000d03205d00300000c00900728f01b05e00300100000300103c05900300001c00001200200200500200100000b02476000000200c0010e21310013800090e400000000601508c02a2df0000850ff00800b00108901100800104e00400501400000a0b302e00700300700501200000900001100004602700100a03c00606502100a0000130082e701500106100000f00e02900300000605301700107c01a0000020041cc00400e02b0c30150d900e04400002000200405500700b01114e00100101200b00000001300000100009802f02d01805908600005600000102101300600300400100f00000b04900200600a00d06700100c0110000500070050130240060060330000350024b40010510590340000a409700000c07250c36100202400700304207c00200c1f800c00408901300e00e00101600008e02b0ce01300408701b03618400000200100426d00c00000f20d05c01d00300535f00001600608401501b00000101f02000512f02800801729b01700100e00a01200101700402000501904d01300100200005d00701800700000304312200002005c00000008100000000001b0030130050090090090000d002f1fc00e0003de00600000000100102700000100400a00103a01d00d51d03b00100402b00d78405c00305600e5be0650b000000200600200518500f06700801e00000b74f00300804a14c00000901301126600a00e01101101500801800601d00100902303901300300302300b00210a02503c00100706a00000704604f02d00011b00036f00001a00600101000006a03900107603601806900003600100969c0045d200071c0c805600a00717700000e00067902d09d03e0000600252730300030d500a0110041a860276700600601205b00f00000146800
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2e9c0184c0c0210044d83400000000000803a0400300000860a0000000399806e0000006040156c0030040000030e080020044b660401c95390801870801c564581530070addb749492008001077985c47158e5285e079d98314b644c001a0f6460c5218930006929cc8254c6050801469961007254c200059264c520c860508018a8801d942505200054a251801c95308001077985c471d96320068319183148624c001a479160c5218931006071d183149634421592a871d252480201fc9325983dd632484014669718772585536d691a0861dd6324c801077985db7154e100041b660611c95308111456978c7655863200519a4b719c7658c801866821c67654f216c6139c98314b63c840144d931807254d420061360c72149639017384c7260c5258c20006925cc8254c6050801c4773184725855300519a4b711866054c01075989db7154d410041de6176dc553c84019908750d414c1100060b1d88254d4250401a2b4120953181420049364e808846254c01a0c6460c52d89300051364e861c9530800124d93a1621189300241764e87d046254c01c4863148705092100619208715d95350401870801c57654d410045a660401c9530800146a909847254d42024172617354c624400142d949847254e200040fe61741d163949eb84c7260c5258e420049a24985cc46050801a449160c52189310040fe61741d06254c0144d931847254c200045aa5f858c920080014669718472585530060b9c9841876394975a2a8414b32181425d70a190751c1424800182e7261061d96320040fe61741d3658c80144d932147258d1000689610610846254c0144d930847654d210061c5c5801c46254c018687021953509200061a1c282d9542441b1a476160c52189310060b612721c7658c8016909650d414c1100058a24953908605080184d831c85258d100069160c610846254c015289254c70509415e58a2417219464480018647120961581536d71118c211c9534856f44e92dd5638c8200060b5d2821d3658c801077985c471189530040f66274197608c80144d93d907254c20006079d18314b63c800142d941847254c200051a241641c96054c01c2862948705094100683a0d840846254c016259408462d8553
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x1
  | 6 => 0x94c
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x124c
  | 10 => 0x124d
  | 11 => 0x124e
  | 12 => 0x8d
  | 13 => 0x8a
  | 14 => 0x8c
  | 15 => 0x8e
  | 16 => 0x150e
  | 17 => 0x98a
  | 18 => 0x98c
  | 19 => 0x98d
  | 20 => 0x98e
  | 21 => 0x128a
  | 22 => 0x128c
  | 23 => 0x128d
  | 24 => 0x128e
  | 25 => 0x150a
  | 26 => 0x150c
  | 27 => 0x150d
  | 28 => 0x9ca
  | 29 => 0x9cd
  | 30 => 0x9ce
  | 31 => 0x12ca
  | 32 => 0x12cd
  | 33 => 0x12ce
  | 34 => 0xa0a
  | 35 => 0xa0c
  | 36 => 0xa0e
  | 37 => 0x130a
  | 38 => 0x130c
  | 39 => 0x130e
  | 40 => 0xb0c
  | 41 => 0xb0d
  | 42 => 0xb0e
  | 43 => 0x154c
  | 44 => 0x154d
  | 45 => 0x154e
  | 46 => 0xb4d
  | 47 => 0xb4e
  | 48 => 0xb8c
  | 49 => 0xb8e
  | 50 => 0xcca
  | 51 => 0xccd
  | 52 => 0xcce
  | 53 => 0x15ca
  | 54 => 0x15cd
  | 55 => 0x15ce
  | 56 => 0xd0a
  | 57 => 0xd0c
  | 58 => 0xd0e
  | 59 => 0x160a
  | 60 => 0x160c
  | 61 => 0x160e
  | 62 => 0x164a
  | 63 => 0x164c
  | 64 => 0x164d
  | 65 => 0xe8a
  | 66 => 0xe8e
  | 67 => 0xeca
  | 68 => 0xecd
  | 69 => 0x9c956
  | 70 => 0x12c956
  | 71 => 0xca
  | 72 => 0xb89
  | 73 => 0xb8956
  | 74 => 0x1649
  | 75 => 0x44a
  | 76 => 0xec9
  | 77 => 0x1a4a
  | 78 => 0x168a
  | 79 => 0x180a
  | 80 => 0x14c9
  | 81 => 0x134a
  | 82 => 0x14a
  | 83 => 0x9d256
  | 84 => 0x4c
  | 85 => 0x449
  | 86 => 0x1a49
  | 87 => 0x98095
  | 88 => 0x98096
  | 89 => 0x99516
  | 90 => 0xb0096
  | 91 => 0x154096
  | 92 => 0x1609
  | 93 => 0x164095
  | 94 => 0xec095
  | 95 => 0x150996
  | 96 => 0xd0996
  | 97 => 0x160996
  | 98 => 0x409
  | 99 => 0x151296
  | 100 => 0xb1296
  | 101 => 0x155296
  | 102 => 0xd1516
  | 103 => 0x161516
  | 104 => 0x165515
  | 105 => 0xed515
  | 106 => 0x138c
  | 107 => 0x44c
  | 108 => 0xe89d6
  | 109 => 0x10c
  | 110 => 0x589
  | 111 => 0x180c
  | 112 => 0x1789
  | 113 => 0x138d
  | 114 => 0x1849
  | 115 => 0x44d
  | 116 => 0x168d
  | 117 => 0xb9316
  | 118 => 0x161316
  | 119 => 0x165314
  | 120 => 0x154b16
  | 121 => 0xccb16
  | 122 => 0x15cb16
  | 123 => 0x140c
  | 124 => 0x3ca
  | 125 => 0xd0b16
  | 126 => 0x160b16
  | 127 => 0x40a
  | 128 => 0x140e
  | 129 => 0x170a
  | 130 => 0x188a
  | 131 => 0xcd556
  | 132 => 0x20c
  | 133 => 0x15d556
  | 134 => 0xd1556
  | 135 => 0x161556
  | 136 => 0x165554
  | 137 => 0x18ca
  | 138 => 0x178a
  | 139 => 0x184c
  | 140 => 0x148c
  | 141 => 0xd0b96
  | 142 => 0x20d
  | 143 => 0x140d
  | 144 => 0xe8b96
  | 145 => 0x16cd
  | 146 => 0x144d
  | 147 => 0x15ccd6
  | 148 => 0x40c
  | 149 => 0x170e
  | 150 => 0x188c
  | 151 => 0x1655d2
  | 152 => 0x160d16
  | 153 => 0x188e
  | 154 => 0x170d
  | 155 => 0x3cd
  | 156 => 0x20e
  | 157 => 0x3ce
  | 158 => 0x40e
  | 159 => 0x14c
  | 160 => 0xce
  | 161 => 0x198c
  | 162 => 0xa4c
  | 163 => 0x134c
  | 164 => 0x168e
  | 165 => 0xbcc
  | 166 => 0x144e
  | 167 => 0x19cc
  | 168 => 0x16ce
  | 169 => 0x1a0c
  | 170 => 0xd4c
  | 171 => 0x104c
  | 172 => 0x18ce
  | 173 => 0x1a8c
  | 174 => 0x194c
  | 175 => 0x178e
  | 176 => 0x74c
  | 177 => 0x1a4d
  | 178 => 0x9ced2
  | 179 => 0xcc095
  | 180 => 0x15c095
  | 181 => 0x9296
  | 182 => 0x20095
  | 183 => 0x8454
  | 184 => 0x45294
  | 185 => 0x44094
  | 186 => 0x44095
  | 187 => 0x45515
  | 188 => 0x44411
  | 189 => 0x1a5515
  | 190 => 0x45295
  | 191 => 0x99616
  | 192 => 0x129556
  | 193 => 0x129516
  | 194 => 0x1283d6
  | 195 => 0x128416
  | 196 => 0x130454
  | 197 => 0x131654
  | 198 => 0x11514
  | 199 => 0x128454
  | 200 => 0x9515
  | 201 => 0x3d292
  | 202 => 0x3c452
  | 203 => 0x15c452
  | 204 => 0x45414
  | 205 => 0x45554
  | 206 => 0x443d2
  | 207 => 0x3d652
  | 208 => 0x3cd12
  | 209 => 0x455d2
  | 210 => 0x3da12
  | 211 => 0x1643d2
  | 212 => 0x45712
  | 213 => 0x15d652
  | 214 => 0xb15d6
  | 215 => 0xb1616
  | 216 => 0x44214
  | 217 => 0xcc3d2
  | 218 => 0x20454
  | 219 => 0x21554
  | 220 => 0x3d5d2
  | 221 => 0x140454
  | 222 => 0x18ced2
  | 223 => 0x21294
  | 224 => 0x21654
  | 225 => 0x164214
  | 226 => 0x20d14
  | 227 => 0x21a14
  | 228 => 0x154454
  | 229 => 0x155654
  | 230 => 0x8cd5
  | 231 => 0x95d5
  | 232 => 0xd0454
  | 233 => 0x160454
  | 234 => 0x45654
  | 235 => 0x3ccd6
  | 236 => 0x1a4095
  | 237 => 0x9415
  | 238 => 0x9655
  | 239 => 0x8455
  | 240 => 0x9a15
  | 241 => 0x151655
  | 242 => 0x150455
  | 243 => 0x44d14
  | 244 => 0xd03d6
  | 245 => 0x45614
  | 246 => 0x9556
  | 247 => 0x83d6
  | 248 => 0x128096
  | 249 => 0xb0216
  | 250 => 0xcc3d6
  | 251 => 0x203d6
  | 252 => 0x1403d6
  | 253 => 0x1603d6
  | 254 => 0xd0416
  | 255 => 0xd2d6
  | 256 => 0x1692d6
  | 257 => 0x1689d6
  | 258 => 0x16d456
  | 259 => 0x3d456
  | 260 => 0x15d456
  | 261 => 0x1a4ed2
  | 262 => 0x3d5d6
  | 263 => 0x1715d6
  | 264 => 0x170cd6
  | 265 => 0x18d796
  | 266 => 0x40451
  | 267 => 0x44114
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 1850
  | 6 => 5825
  | 5 => 3072
  | 4 => 88
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
  | 8 => 2*((h/35+packedAt gbK8 (1664+(h % 35)*6) 6) % 64)
  | 7 => 2*((h/630+packedAt gbK7 (68450+(h % 630)*11) 11) % 1850)
  | 6 => 2*((h/2018+packedAt gbK6 (279600+(h % 2018)*13) 13) % 5825)
  | 5 => 2*((h/1052+packedAt gbK5 (181248+(h % 1052)*12) 12) % 3072)
  | 4 => 2*((h/57+packedAt gbK4 (6160+(h % 57)*7) 7) % 88)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xf83e03c0ffffffffe0ffc01f063ef2381ff3e7
  | 1 => 0xfc003ff07c1f803ff07ffff19d93fc464cc7f
  | 2 => 0xfffffc0007fe0003fff8001fe1e1c3ff870f87
  | 3 => 0xffffffff8000003ffffffe0fe01fc07f80ff8
  | 4 => 0xffffffffffffffc00000000fffe0007fff000
  | 5 => 0xf00000000000000000000000fffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x900600c048c28a39604e4151020a72180951e3
  | 1 => 0x894021590351d048a90294da08d816c424c42d
  | 2 => 0x2adae40805b44092da90028c6161816d870e86
  | 3 => 0x4ad4aa2d000012314e52b00b601e802d80b50
  | 4 => 0xf31b33ca63965c008000c08ddf4000776a000
  | 5 => 0xc001c030c021860010c63010ffbfffb0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaece0feaaec80feeaece0feaaec80feeaece0feaaec80feeaece0feaaec80feeaece0feaaec80feeaece0feaaec80feeaece0feaaec80feeaece0feaaec80, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_38837
namespace PEqualNP.Outside.L_meta_38837
open PEqualNP.Outside.L_meta_38837.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 7 := block_range (n:=7) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 7 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 12 := bs0_4_0
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
theorem bs1_2_0 : Interval s1Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 10 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 60 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 165 := (concat bs1_4_0 bs1_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 50 := bs1_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 1 := bs1_6_0
theorem alls1 : ∀ k ≤ 6, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 1 := bs2_2_0
theorem alls2 : ∀ k ≤ 2, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
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
theorem bs3_4_0 : Interval s3Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 117 := (concat bs3_4_0 bs3_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 46 := block_range (n:=46) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 46 := bs3_5_0
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
theorem bgb_4_0 : Interval gbAtlas 4 0 88 := block_range (n:=88) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 88 := bgb_4_0
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
theorem bgb_5_1536 : Interval gbAtlas 5 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1632 : Interval gbAtlas 5 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1728 : Interval gbAtlas 5 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1824 : Interval gbAtlas 5 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_1920 : Interval gbAtlas 5 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2016 : Interval gbAtlas 5 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2112 : Interval gbAtlas 5 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2208 : Interval gbAtlas 5 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2304 : Interval gbAtlas 5 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2400 : Interval gbAtlas 5 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2496 : Interval gbAtlas 5 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2592 : Interval gbAtlas 5 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2688 : Interval gbAtlas 5 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2784 : Interval gbAtlas 5 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2880 : Interval gbAtlas 5 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_2976 : Interval gbAtlas 5 2976 96 := block_range (n:=96) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3072 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 bgb_5_288)) (concat (concat bgb_5_384 bgb_5_480) (concat bgb_5_576 bgb_5_672))) (concat (concat (concat bgb_5_768 bgb_5_864) (concat bgb_5_960 bgb_5_1056)) (concat (concat bgb_5_1152 bgb_5_1248) (concat bgb_5_1344 bgb_5_1440)))) (concat (concat (concat (concat bgb_5_1536 bgb_5_1632) (concat bgb_5_1728 bgb_5_1824)) (concat (concat bgb_5_1920 bgb_5_2016) (concat bgb_5_2112 bgb_5_2208))) (concat (concat (concat bgb_5_2304 bgb_5_2400) (concat bgb_5_2496 bgb_5_2592)) (concat (concat bgb_5_2688 bgb_5_2784) (concat bgb_5_2880 bgb_5_2976)))))
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
theorem bgb_6_4224 : Interval gbAtlas 6 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4320 : Interval gbAtlas 6 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4416 : Interval gbAtlas 6 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4512 : Interval gbAtlas 6 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4608 : Interval gbAtlas 6 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4704 : Interval gbAtlas 6 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4800 : Interval gbAtlas 6 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4896 : Interval gbAtlas 6 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4992 : Interval gbAtlas 6 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5088 : Interval gbAtlas 6 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5184 : Interval gbAtlas 6 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5280 : Interval gbAtlas 6 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5376 : Interval gbAtlas 6 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5472 : Interval gbAtlas 6 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5568 : Interval gbAtlas 6 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5760 : Interval gbAtlas 6 5760 65 := block_range (n:=65) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5825 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat (concat bgb_6_288 bgb_6_384) (concat bgb_6_480 bgb_6_576))) (concat (concat (concat bgb_6_672 bgb_6_768) (concat bgb_6_864 bgb_6_960)) (concat (concat bgb_6_1056 bgb_6_1152) (concat bgb_6_1248 bgb_6_1344)))) (concat (concat (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632)) (concat (concat bgb_6_1728 bgb_6_1824) (concat bgb_6_1920 bgb_6_2016))) (concat (concat (concat bgb_6_2112 bgb_6_2208) (concat bgb_6_2304 bgb_6_2400)) (concat (concat bgb_6_2496 bgb_6_2592) (concat bgb_6_2688 bgb_6_2784))))) (concat (concat (concat (concat bgb_6_2880 (concat bgb_6_2976 bgb_6_3072)) (concat (concat bgb_6_3168 bgb_6_3264) (concat bgb_6_3360 bgb_6_3456))) (concat (concat (concat bgb_6_3552 bgb_6_3648) (concat bgb_6_3744 bgb_6_3840)) (concat (concat bgb_6_3936 bgb_6_4032) (concat bgb_6_4128 bgb_6_4224)))) (concat (concat (concat (concat bgb_6_4320 bgb_6_4416) (concat bgb_6_4512 bgb_6_4608)) (concat (concat bgb_6_4704 bgb_6_4800) (concat bgb_6_4896 bgb_6_4992))) (concat (concat (concat bgb_6_5088 bgb_6_5184) (concat bgb_6_5280 bgb_6_5376)) (concat (concat bgb_6_5472 bgb_6_5568) (concat bgb_6_5664 bgb_6_5760))))))
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
theorem bgb_7_1632 : Interval gbAtlas 7 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1850 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 bgb_7_576) (concat bgb_7_672 (concat bgb_7_768 bgb_7_864)))) (concat (concat (concat bgb_7_960 bgb_7_1056) (concat bgb_7_1152 (concat bgb_7_1248 bgb_7_1344))) (concat (concat bgb_7_1440 bgb_7_1536) (concat bgb_7_1632 (concat bgb_7_1728 bgb_7_1824)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 64 := block_range (n:=64) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 64 := bgb_8_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 7 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 3 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaece0feaaec80feeaece0feaaec80feeaece0feaaec80feeaece0feaaec80feeaece0feaaec80feeaece0feaaec80feeaece0feaaec80feeaece0feaaec80
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808928 * 2 ^ 32 + 4272614528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_38837.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,5]⟩,⟨.and,[0,2]⟩,⟨.and,[2,3]⟩,⟨.and,[1,2]⟩,⟨.or,[1,7]⟩,⟨.or,[0,8]⟩,⟨.or,[3,6]⟩,⟨.or,[4,9]⟩,⟨.and,[10,12]⟩,⟨.and,[11,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4272614528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808928 * 2 ^ 32 + 4272614528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_38837

open PEqualNP.Outside.L_meta_38837 in
theorem PEqualNP.Outside.L_meta_38837 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808928 * 2 ^ 32 + 4272614528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808928 * 2 ^ 32 + 4272614528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
