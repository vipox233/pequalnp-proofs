import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36362.Model
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


end PEqualNP.Outside.L_meta_36362.Model

namespace PEqualNP.Outside.L_meta_36362
open PEqualNP.Outside.L_meta_36362.Model
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

def SBf (j : Nat) : Nat := [7, 6, 8, 7, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36362

namespace PEqualNP.Outside.L_meta_36362
open PEqualNP.Outside.L_meta_36362.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xa2e00026262100b080110746181210060a8e340009b000000000012802078f941e14e8324000000000c9100000244e34000002400018000160000e00020200002023400d0000101ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xe50171a000194e01b80144963800689a900001b200ada1b009860000b40284a740091000a00000001800000000000030003de0442fc0066a5400000143960038fbe000119066ec58074c5e9e00bd50000d8000000000000440005c00001009011c000000000011000304040000600082021000212000030020082bda8287785050edca421db54843bba8a85745150abca6215754c429faa2653c544caeea2995d14532bda826578504ca7ca8194f55032b7a92836c52506f4a020de540419f2a6633d54cc6dca598db54b319f2a4633d548c6f4a118de542319faa2433c544867ca810cf55021af298435d53086f4a010de54021afa9a815c53502eca2205d544409faa2613c544c27ca8184f55030b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f209f2a4413d54882eca3105d546209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (i*5) 5
  | 5 => packedAt s0K5 (i*16) 16
  | 4 => packedAt s0K4 (i*27) 27
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s0K6 (6+((h/1+packedAt s0K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s0K5 (731+((h/13+packedAt s0K5 (640+(h % 13)*7) 7) % 69)*7) 7
  | 4 => packedAt s0K4 (1875+((h/21+packedAt s0K4 (1728+(h % 21)*7) 7) % 122)*7) 7
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x7ff03fffff8307fe0ffc1ff0ffffe018e73fc
  | 2 => 0xf83ffc0fc1ffff83ff07fe0ff0f01ffef38ccf
  | 3 => 0xfffffff001fffffc0007ffffff001fff03ff0f
  | 4 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 5 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x309118a290425014a849d0930194d21886315c
  | 2 => 0x52922864129212816942528510a154a8b284c5
  | 3 => 0xa1245101a524252c1084a52aaa028953015b0a
  | 4 => 0xc52882492034a9ca5290210ccc4b0063580ea0
  | 5 => 0x630e38e39c73e739ce739c0888c1183efe000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000fcfcfc00fcccf000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36362
namespace PEqualNP.Outside.L_meta_36362
open PEqualNP.Outside.L_meta_36362.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x730025190000090280df43be43bc43dc439c43bf42bd42df32dd32
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x23802030089400aa1805611e5390e5aa421d354843c7290871d5210f1aa421c3548438e29a851c54cca38a8996350932
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x20c6550932
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 11
  | 2 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | 2 => packedAt s1K2 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (156+((h/3+packedAt s1K4 (144+(h % 3)*4) 4) % 12)*5) 5
  | 3 => packedAt s1K3 (309+((h/3+packedAt s1K3 (297+(h % 3)*4) 4) % 15)*5) 5
  | 2 => packedAt s1K2 (39+((h/1+packedAt s1K2 (38+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xe0fffe0ffff87f83ff0fe1ff87fe0ffd1cf3cf
  | 2 => 0xff07fff07fff87fc1ff0fe1ff87ff07ee33cf3
  | 3 => 0xfff83fff83fff8ffe000ffe3ff8fff8303cf3c
  | 4 => 0x3ffffc0000ffffff0003fff00003fc0fc0
  | 5 => 0xffffc000000000fffffffffc00000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x2810822210908000a5012024809205280c5145
  | 2 => 0x42410441212008140a1042090824a050612492
  | 3 => 0x842228840a4441a94088954255094a03028a28
  | 4 => 0x16b5b129487552ce73aa1103e640631bb40fc0
  | 5 => 0x18c621ce738664f39cccf99044018c63dbf000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfafafaa0faa0faa0fafafaa0faa0faa0fafafaa0faa0faa0fafafaa0faa0faa0fafafaa0faa0faa0fafafaa0faa0faa0fafafaa0faa0faa0fafafaa0faa0faa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36362
namespace PEqualNP.Outside.L_meta_36362
open PEqualNP.Outside.L_meta_36362.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x4817e53903bca7205794e40bea9c81dd53902baa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa9281ef52502dea4a05f14940f6292816c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330efa1e61dc43cc2fca5987b94b30b7296617d52cc3daa5985b54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7185f94a30bea94617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130efa1a61dc434c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa4185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef42883d885107b8ca20f6994417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4107bd0820f621041ee32083da64105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd18421f930843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb10a21f521443f460887e4c110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f721465ed428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbdc84997b50932f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41f7294836e52906faa520fb54a41b6a9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63df438c7b88718df94a31bea9463df328c7ba6518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131bfa92637c524c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f7d0c31ee218637e520c7dca418db94831bea9063ed520c6daa418f7cc831ee990637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21f7a1643ec42c87dc6590fb4cb21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f7a1243ec42487dc6490fb4c921fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0xc000001170007809d19a3ac4ec4d1632ac43cb0800322001058000000000f800248000000002ae0004a80023e0000014b4a80010326a0000000000000000057000118048c622e3c81e81300000095c30240000a306d8473ce7280000000000000000184020000000002c400000108465158c14ca000288003ea0c0788cb18a0002a8660f0848c91373b2448000fe4eaa38e49a752e99d0210427e008c1976000000fd97c3e2925089d84bca0c520bf0401ac8082e000001430ea000904000233f286400285120000e30000d278cd71e647c7300b0933dc000001b1000000000bc00a0000026b4ac000488be000434d4800000000e7800000000000f200091c000003084846b0000006ac6a8ce3961690a9dd0001d0bd07b400934259b209816c3280a4e00000018b3840193b19d2261081ca341e8690000190000005b1ce000000250531100c40000028e0005aa2c0000000006747a0f400000000000388d92507f83ca7e4c437800223000000a28000346e87122130a00000000166a34000003300011880000047400000466000000002386c00021008a280c98000060010680047200128062526744000ef344000000000000013200002a0002a17d2669bc6e0000006f8000004707508c0f5000034efa20346000002020009187c800000000000000005c8eb95e09a2a07c2870f87888d81d2ce5010e8001ba000f28000000004e9702340000003a000450001c4000000004008000060000080d00001805006000004018020020000000200200400004004010000000000080000100000c0280000800c008000080100300500402c040020060000000700000400001000018008000040200200003202403800000008020000040000880000400c0000500c00800806002024000030120140000000004c000020000040180000400c0000600e0a40080002c000038000000040400b00001c0580100000801009006014028040020280080101c000000050020040080000000c0000000406002806000008000000020040000e000000008010080140480600600c008010000000000000000000006010000028140280000c80000200001004004004008000020000000500600001802000000000010000000d000002000000010000000180201600800800bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0x1370000009ec88800064000000830924147985c4b20f0a40000000009a000154174fea140000003518e39a93000000000000000000003400000009c6d0449e14b62b00002c284000001320004000001000000000168000000360000004c1360000000000000044c000000bb000000000eb406000000212c44bd0400042e560e08ff0005b529000000000c3000000000e91770186280016519e248209c843e3188f03e2f0060390f714616125a804762f414a2552031d27a911be7a41da681ec5b81793c16057c0025c2c8000000000001100008a0002bc03a371881a04d800000000e2800000a3c2c800502000001250de408000b71c0000000000008309c81c1c223509a63000000000003a69447607600000000000000078139201fa0b4230612e8a24001444e200000000254938910110be0002b8b4000000f4000000968918001745ecbf99926c2b53b8000001fc001f300004c000000e6000a48814c20040022225a8054580035a000001d00000000022f0006d400000000000b89691049800018f262000db02a350600b993d152678000342560002400032000000000000000001b7000000bf242000000000e62a494d330000003c0ad8004481c0000d800050d240001160a0001502d439d1412e3d897cb018713e568d280012c700f68864f81b465159132000000000003b40014d328000ed8000007c8000b8000238511ff4147680000012e0002b21e48a0004f19f37e7c000000000088000374ba4551d2780002713914c01691000000028814b31750000acee24300042c0020728c18c0021a2d69f4281380122e4000da24c8703714120c621180ab0000903ea1845a65452a8814e3001a94a44e7a8000d7214000000000008c87d80052830d1f81b4780fc0022a09e570fd0000000000000e41c001412690002c8aa8000002993680041ea10a71794aa6b0fc0000000007280446a574479b93ec334938003de0009a8000005513c8fa32e6ec6911600070c7407500003c0000000000000000128001250000000000000000000000000000000d0840000858770000003900000000041d39a7f000000000003700002900035e0000000010a178de0000c8000000c92066f40000029e424000173360009f0333547dcd991006c7ac129822522006a0000009d0d0000000000698003bc75443a7a0000003b83821086cb61fc000544c690c21c0014500034c3f050953000a48cb0e90fc0011b16f258961148d13e8624661c7000320000000000004c0001c68254a8000006042199c52
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x53c823e64947208f59251c825e63d52209758f548823e64d4e208f593538823e6494e208f59253882cd6310a20ab191328823f64546208f191518825f63546209718d51882ae64886208f992544826f62551208f994544823e6494d208f592534826d6294d208fd91534823c6454d209dd8553482746154d209b997214832c54c8520cb151214832c54881209798f540825d63d50209d987540827561d50208f596540832c62550208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20d398a530831e5454c20c7551530823e6414c208f590530825e6314c209d98453082756114c20cb553420826d6510820b358c420826d658c820cb55232082ac644c820cb551320834e534c820cd95251083355494420d594e51083555394420cd95151083355454420d594d51083555354420d9d0951083644254420d98c9510836532544209b59621082ae6488420d954621083655108420d9547200826f6548020ab191200836551480209ed95200826e62d53109b58b54c425f63553109718d54c423f6454f108f19153c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c423e6494b108f59252c425e6394b109758e52c425e63d52109758f548426f62552109b189548423e64d4e108f593538423e6494e108f592538426e6294e109b58a538423f6454a108f191528423e6414a108f590528425e6314a109758c528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c715053443596014d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910d9584524436452885109d1952144358538c1109e195304425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b588530427a6014c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109d984520436552c40109e596100435953840109dd95100436552440109ed9510043595344010
  | 1 => 0xc63e649513197d8d544c63e6515131c7152314c66e62d50319b58b540c67a60d50319e583540c63d6595031c718d540c63e64150319b988540c66d62150319e980540c6796015031c7553430c65d6510c31b3588430c72e5494831cb552520c72e5454831cb551520c71d54cc831a7191320c71d544c831d3949320c65f654c431a7191310c677654c431ce952500c7395494031da94a500c7695294031ce951500c7395454031da949500c7695254031d6d0d500c7584354031d6cc9500c7593254031d6cc5500c75931540319798f54c865d63d5321cb18954c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c874e6294f21c795153c871d5454f218f99053c863d6414f21cb55342c86cd6310b21cb55232c86ac644cb21cb55132c874e534cb218f993538863d64d4e218f990538863d6414e219e98053886796014e21cb953218865f63551219718d544867b60551219e181544863f6454d218f191534867b6054d219e181534863e6414d218f590534866e65d0921b358c424866c654c921ab19132486e4614c921ab992214863e64141218f590504865e63141219758c504866e62d50219798c540865d63150219e980540867960150218fd91530863c6454c218f990530863d6414c219b988530867a6014c219e580530863e64948218f592520865e63948219758e520863e64944218f592510866f65484219dd95210863f64540218f19150086ad6210f409b98a51d026d6294740a718d41d026e6294e409b58a539034e6294e40d358a539031e53d0e40c794d439031e5390a40a758c429031e5310a40c794e41902ae6290640c794c419031e53d02408f99443502ad6210d409798c525025d6314940d398c525034d6314940cb90c525032c43149408f997425032c52d0940cb149425023e65d0540cb14b415029c6350540cb149415029e6390140cb14a405023f6550c408f596421029d631084097d8d511025c63544408f59641102ae62904408fd9540102ac62500409ed95401026e62d53309b58b54cc31c63553309b98854cc26d6215330c755343cc2cd6210f30cb95252cc32d5494b30cb95152cc32d5454b30c755332cc29c644cb30c755132cc34e524cb30a719131cc31e548c630c7950318c2d9600c630c7953308c26f62551309b189544c27761551309d185544c25e65d0d30b3588434c23e64149308f590524c29c644c930b6181324c23e64145308f590514c26e62145309b588514c25e65cc530a7191314c29e648c1309798f540c26e62150309b588540c27661150309d584540c23e6494c308f592530c23f64548308f191520c23f64544308f191510c25d658c430b6580310c23e64940308f592500c25f654c0309ed95300c25e63153209758c54c823f6454f208f19153c823e6414f208f59
  | 2 => 0x10c0008e9b80000b47791a03e2d80014e000000d89fb0000006a05f00075800057316340bb07132c00102000000478f481518c3cc001d30044f0be0003246b109000000620000e612200000000000001068000005181590b3cc0001f0002c618c6609712880c4219516e6e8901802520a4001cf0005ec000001805e8db80f1e82981d0522dc6d8000002ba7e4398422b4000002113063484c08c0624dc9919300e5d4009992b822c000170003a8890003765341e2082cc2a8f19c32842cc9d12a0f2000f78300003b90b149000000000003a47b03c1f02d8000d316d2900000010f23200000000210588f70834343602200000a0bc2d9c93f83a40011c00047c0000033600000025000194f216a0cc0004400000052c001471a6540000e531c00008008040000001400008010080202c030280f0180300c010040b000000040f0000100412000010040700000000010080c0000c000000240104c0500804004000100002800008000140d00404004060340001c00000010200201c11000040000301c0303c0100c00018020000101000010000440201400008000040000c04000000040000c06024000040000002000000040c0180101c0201000000010040000407000070000d00c0003801004000140100007000060080103c0000400008040040000009018080001f0000800c010000200c00008000000800004000020066e62947439b58a51d0e6f62543439b18950d0e3f6550c4397d954310f2f4354843d390d5210f2d4354843d350d5210e5f63547429718d51d0a5e63943429758e50d0aad6210e428f9974350a3d6590c42c754e4310b1d5310c42ab5884310b1d53d0842d354e4210a3f6550842c754d4210a6f6550842d354d4210a7a60d53329e58354cca3f64547328f19151cca3e64943328f59250cca7661d52329d587548ca3e64946328f592518ca3f64542328f191508ca3e64951328f994544cb1d6315132cb588544cb1c5490d3297195434cb2c5490932e390e424ca6c6550932e350d424ca3d65950328f990540ca5e63150329b988540cb1d54cc832cb552320ca5f654c832c7551320ca6f654c832cb551320ca9d6310b419798e50d065d6394341ab588439065e6394a419758e529074e6394a41d358e529072e4394a41cb10e529072e52d0a41cb949429072e52d06419b988535066d6214d41d3988535074d6214d418f997435071c53d0d41c714d435071c53909418f994425069d6310941c714c425071c5390541ab98a415063d6590c41ab588431063f65508418fd95411069c63504419dd95411066f62540419b189501066e62153319b58854cc63f6454b318f19152cc63e64943318f59250cc66e62d52319b58b548c6cd6210e318f992528c63d6494a31a7191328c63f64542318f191508c66f62542319b189508
  | 3 => 0x1db0281d80020e000750002151be3e0ec09a1960004f8401002b4c810c0000007b1592bc0004b02e30400053800046451030371825582986d034204809b00002ecb9864000768bf8c3000000001ab2360e0529ea1ee4bc8700b3bc000629b931e038000001945441e9440001d055800148000ef92c000338000000000000000000c31c000000001ec0000000048c000000000005a9770680e4138000007949b130012000d70e8384000da000090000001282f2000ab8000005d0000000007cc109221fc4400019721a000a28000000000004a00000071118308000e009b0f81300012639c0000014a2f0188ac0f213c4280400000000006a07000000e200000010c9c8500007f4970ac1ae0000010300000000000000408df8002ca0002281d2fa68c000000001605c8000000000005e0004b46410717a7044a85d1a23f0001253c004c4783f41200cd013b26250cd68a32e02e8000e41521d4759fe1c0000f58fb00007800000044000df1343f4828000000005840514c18424c921691200b000000076624719b502c7205e0001ba6cc511c71c2118b400020a364410000000009f8244261f40014003656c5a1dc1f4840b59cc1d87183b98d06a358f916f0003fd029f138a82c1b0000004f4000001601bc0015f08e33c2a133000000d08000006c8000000ac000001163e8000001353fe41000187000238590b822672c3f0200e4850468003a200000000000650000de13a000000f12e23f43086a17e1343811509e6bc0006700036c7c9a70007342a95300059c0e069024861010000c03d4571410087549c0283ea39c541000006180005c1b4418360002126f4080003c20010b99f0004f8d10ed0f41a0588001b84ac492012c0324509aa334168001270820645f1e72c80010000022e09857800000000001543ae00000000242224001dd432740d20002aa0003709c34a5f800000132000151a90007d86680033a678f106b1e083cc0832030000e51d9092830089ed1146a0cc000314670a7952000000428000001fc0004b3ee000001bc0005c80000c140144c600000044400191000138c28000007e0001e81aa000438000663102c80
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x2893406041c551130e40800601500004301758248b00f4c4b380100058358d6215132a1ae72928520d0d7214d435070629cc520a83435c86355031838ecaa26418d497210d500c68c3a264a8063461d13154031a1ae6312a990c2c7655132c8686b94a6a1c818394e6290640a1ae629284a060c631494150307318a520281435c86355330838ecaa2659861a54580318c286b98c4aa0410b1d9544c820a8ae6212a210524744c95108313322a310841891915148020
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x10640080d8714e629054180d8794e629064080d8718c525054080d8798c5290140
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (i*5) 5
  | 6 => packedAt s2K6 (i*16) 16
  | 5 => packedAt s2K5 (i*27) 27
  | 4 => packedAt s2K4 (i*38) 38
  | 3 => packedAt s2K3 (i*49) 49
  | 2 => packedAt s2K2 (i*60) 60
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (6+((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s2K6 (718+((h/13+packedAt s2K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s2K5 (20359+((h/221+packedAt s2K5 (17928+(h % 221)*11) 11) % 1059)*11) 11
  | 4 => packedAt s2K4 (22272+((h/179+packedAt s2K4 (20482+(h % 179)*10) 10) % 782)*11) 11
  | 3 => packedAt s2K3 (1265+((h/8+packedAt s2K3 (1225+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s2K2 (243+((h/1+packedAt s2K2 (240+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x87fff83ff87ffe0ff87f87fe1fc0fffd38f39f
  | 1 => 0xf81fffc1fffe1ff07f87f87fe1ffe07ec73cf3
  | 3 => 0xffe0fffe007fe3ff8007ff8ffe00ff8307cf1c
  | 4 => 0xffffff8003fffff8000fffff0003f80fe0
  | 5 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xa0840888409400029809009402442a30185185
  | 1 => 0x2421104902020502082882220924148432432
  | 3 => 0x114aa214354906b50444d50b540a950b058e18
  | 4 => 0x5594c4a1240d4b29cd50440d992c0613a80bc0
  | 5 => 0x66188739c67193ce7667664110301863f6f000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeeeee88eeccaa88eeeeee88eeccaa88eeeeee88eeccaa88eeeeee88eeccaa88eeeeee88eeccaa88eeeeee88eeccaa88eeeeee88eeccaa88eeeeee88eeccaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36362
namespace PEqualNP.Outside.L_meta_36362
open PEqualNP.Outside.L_meta_36362.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x5873864a1d0a28013207938100a941f005c4801e892004c0002342a44250054011240060000015ad4018d0200b01800858d8e1a600000402800050000a6040102ff43fe43be43fd43fc43bc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21ef21fe21fd21ed21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xb8066a74185e3ec0868e04001ca6a0007c9400889800901400960068583a784a4cba62005a76280cc2122e9ca45040b680aa20545c0008004830160046a83482ae0066563c9e2c720000361a10006e6c441e60b00a92844eb400009a384222be002a000070c464bc8c00a2327a52ac7e24260e028a00b2240400f4c38380441408004007061034014060450004001842018018073e5390e7aa321cf94c43cf298873d5110eeca2215d544429f2a4653d548caeca3195d546329faa2653c544ca7ca7a0cf55241b7294836d52906bea6a0d714d41cfa9a833c5350738a6a0c714d41dba8a833e54106dca420db548419faa6633c54cc67ca918cf55231ce21c636e528c6daa518cfd51319e2a2633e540c67aa818e710c31b7290636d520c6f4a018de54031d721e43ac43c875e8390eb507219f2a4433d54886daa510ed50621daa0a43ae43487588690f9d4521d7a0a43e6414875a8290f950521d2a0a43e731487c86290cf950219eaa0436e52086bca7205754e40b7a92816c525033887984f952309eaa4613f544c278a8986710d30b7a92616c524c2eea2985d145309faa2413c544827ca8104f55020af298415d53082eca2105d544209f2a6213d54c42dca5885b54b10f290e21e5214427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x6980209863805a888000048079472400c00000040008000020400a1c3000044021d6510c31c610d500c68c6350721a518d41886946350521a958443486a56490521a318d41486c46350521e1d8d41486a46350521e118d41486846350521a9d9331486a5640c521e110c31486e1600c52199584525031443145308718d54c43255448710
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x8084857610c314874021ac018a43411cd5448710
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
  | 3 => packedAt s3K3 (840+((h/7+packedAt s3K3 (798+(h % 7)*6) 6) % 36)*6) 6
  | 2 => packedAt s3K2 (149+((h/1+packedAt s3K2 (147+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffff07ff0fffe0f8787fffe1f81fffc0ff39f
  | 1 => 0xf03fff83fffc3ff007f8f0ffe3ffe07e313cf3
  | 2 => 0xffc1fffc00ffc3fff800ff0ffc01ff83c1cf1c
  | 4 => 0x1ffffff0003ffffff000ffffe0003fe0fe0
  | 5 => 0xfffe0000000003fffffffff000000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x11081110812800028181211404882a30065185
  | 1 => 0x2485220928426250424858a32125414a112432
  | 2 => 0x429544286a9226b548409a8b4815950ac18e18
  | 4 => 0xb288942401889299492000c925806116a0bc0
  | 5 => 0x8c310e738ce333ce6764ecc100611863bdf000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xfefea8a8ececa8a8fefea8a8ececa8a8fefea8a8ececa8a8fefea8a8ececa8a8fefea8a8ececa8a8fefea8a8ececa8a8fefea8a8ececa8a8fefea8a8ececa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36362
namespace PEqualNP.Outside.L_meta_36362
open PEqualNP.Outside.L_meta_36362.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x427000600000004000f82000160406016ae1a9921b185d2883c5471d00403800001489005800b0ac452f0001380440001a0244c8030a0a0000491aa1e00030260002b000000103040401514007800a00001ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21f621fd21f521fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x3226400001c03400000003800010020c0000288009800000009a0000000e47100000001700000000000000f622001840040000010c370001c000000000dc0000000000000000e6001900000271d9dc06000000000591e800000000000000000000000000000005b148005e330300000003f8b03a1031880280000000000010a00da872a974d21a2b8000000001bc00003a0000000000c45636091100000488013a8a520008200001e490001a000008b4217d129a4600944854e150a63f2e000166600000ac2a0c82400a11d000003900128001b00000000033801247800044006847800000000000009e44000e0000e07c8c000024c005800000002d00000000000000f88e000002c000400000000a93cd40000000d6900980000004c1689c0f259d4ca0024800c000000007c810026c6045000006a52000f000000000000004a00000004688c089700280006c000012c5e13090fa0c51800a04700000c400001d904000c0000a2e000008400000000000001f93e000510c000000254007a0f09400280000003020000000028000001020040001000100005008000000000040000000000400000000000010000e01000000a020001404050080416010001c000000dd94643baa8c873e5390e7aa521cf94643db28c87365190f6aa321cf542439f298879e5310e7aa421cf944439ea80873e53d0a7ca3a14f543429eaa485765190aeaa3214f14d42d7a92853c5150a7ea0a14f95042bb28885755110a7ea9994f153329f2a4653d548caeca3195d546329faa2653c544ca7ca8194f55032bb2886575510caf4a0195e540329f29c833d529067ca320cf54241b7290836d521067ca620eb948419ea9083ad521065aa420cf94441db288833d501067ca998cf553319f2a4633d548c6dca518db54a31da20c633f544c678a898ed105319faa0633c540c67ca990cf55321d6a16433f5488678a910ed90621da20c43b75488768a910ed90e21da21c4375528876e8510ed50a219faa2433c544875a8490ed90521da20a43b75448768a890ed90d21da21a43e7524876e8490f990921daa1243e5424874a8490f9cc921f2192433e540867aa810dd944219f29e813d52d027ca3a06d88740da90e813d54902eea2a05d145409e29a813f525036ea2a04f14540da28a8134515036c42a06d48540dda82813e541027ea9984f153309f2a4613d548c27ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f55320bb28e417551c83ca43904f952209eaa4413e544827aa89079485209f2a0413d54082bca6105754c20bb2884175510827ea9884f153109f2a4213d548436883084fd51109e2a2213e540427aa8085794c10aea98216e52042daa4086d10410
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x5830068d50251e2c0975cd820e560000000b46b804750954821d2826500370a699805400010140cd8900780125e0161800a4e00004403100c130064000073201da2463139f72020428c18080000048481002020934440079958a5190e2d6294643a958a5190f2662946438d58a5190f2562946438958a5190e3461540438d98653d0a3461543428d98754cca3661d5132c998552107255294441a9588418c7255210631a9588414c63661d50318b588540c63960150318798f548869663d5221a958b54886a562152218d996438862c65509218d99643486a56210d21a959242486a66550921a919542486a46350921a9d8142486a764cc921a959032486e1600c9218d98653d0325524874099588515022d6214540a9588515032662145408d5885150325621454089588515023465885408d195215023661d53308d185548c32554487208d185548821c63551208d185544832554485208b58854c42a562106108d59441043155310410a958841043255210410
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x1120018e800c412940212b90c2a8087415ce615484190ce732a8490c2675d933248612b94c329e81095ca61d533084ae430aa918504735512148302a9ac420821095d95210410
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 5 => packedAt s4K5 (912+((h/16+packedAt s4K5 (800+(h % 16)*7) 7) % 80)*7) 7
  | 4 => packedAt s4K4 (4950+((h/55+packedAt s4K4 (4455+(h % 55)*9) 9) % 347)*9) 9
  | 3 => packedAt s4K3 (2420+((h/20+packedAt s4K3 (2280+(h % 20)*7) 7) % 80)*7) 7
  | 2 => packedAt s4K2 (502+((h/3+packedAt s4K2 (490+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfffffc3f0fffffc1c3c3fffe1c1ffffe07f0ff
  | 1 => 0xf0fffc00f8f87fe03fc787fe01c3c3f393c93
  | 2 => 0xff07ffff00ff87ffc007f87ffe03fc1c1cf1c
  | 3 => 0xf0007ffffff0007fffff8007ffffc001fe0fe0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x1000408120200004080908804050510025025
  | 1 => 0x62634886a5154c4e21642c5720c8a8ad192c92
  | 2 => 0x84255112812844d2a4204d4349403285418518
  | 3 => 0x208a2224080111250a49000492928008ac0ac0
  | 5 => 0xc8cc43b8ce4e6679f3b2766103032331f7f000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfea8fea8faa8faa8fea8fea8faa8faa8fea8fea8faa8faa8fea8fea8faa8faa8fea8fea8faa8faa8fea8fea8faa8faa8fea8fea8faa8faa8fea8fea8faa8faa8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36362
namespace PEqualNP.Outside.L_meta_36362
open PEqualNP.Outside.L_meta_36362.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x388000a1ea0c25004008e0058000268400d362c1064e009290e10a2a4c68f1522011800a2159744252003a7cc8c0604000608002404d240040ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xdd550000008818e8500000011564e40000005400000000013c0000994c000034011c4cf4004150012cd9100044fc00000000000000d40080300038ad3548009cecc128cc5804000121596000000000680168009400000000f0b86400000000007000200000000104000000004828011800006cf94400910800015c0010140000742d241c60d0e1310cb03c008c007c00a45c0024000000c8000000080000000001400000000000000000a00cb538a80000840000000000000078000000c4bc00020800060c0204000004040a04000002000000020e0404000000020205765190eeaa321dd94642baa8c853e540ca7aa819734c832bb2886575510caf4a0195e540329f28c833d50906bca620d754c41b7290836d52106f4a020de54041cf298839d531075ca420eb548419f28883b65110774a020cf54041dca808339501067ca998cf55331b7294636d528c7688318cfd51319e2a263b4414c67ca990cf55321af29c435d53887688310cfd51219e2a243b4414867ca3a04f55240bba8a8174515036ea2a04f14540da28a81345150376a0a04f950409f2a4613d548c2dea4985b149309f2a0613d540c2dca4185b54830bb2886175510c27ca9104f55220afa9a415c534827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f55210da20c21b9408427ea8884f15110dca02213e540427aa8085794c10aea98216e52042daa4086d10410
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xb0e72e006c0c00081a0000148a4212a80616a0a98401e09000200004504327493254032c354d521071a5354041c654d501072a5254041ca54950107255210631ac580418c6b16010531c554c41886b16010621ac58041487166314540c558c51503266214540c9588515033160145408d185548c2346155220ac58041842b061502108e19540442356510410c554c41043255210410
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xc0840000101885496010631c22a6b008310e05635885150308b1ac028a81885896014540
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s5K5 (788+((h/14+packedAt s5K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s5K4 (2697+((h/30+packedAt s5K4 (2457+(h % 30)*8) 8) % 193)*8) 8
  | 3 => packedAt s5K3 (998+((h/8+packedAt s5K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s5K2 (249+((h/1+packedAt s5K2 (245+(h % 1)*4) 4) % 11)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe1fe3c7e3fffe1c71f8fc0c707fffe19c0ff
  | 1 => 0xf1fe3fff803c78fe07e3f1fff8070e1e667c93
  | 2 => 0x1ffc03fffc07f1ff803fe00fff80fe1878f1c
  | 3 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 4 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4028004410502000420502480101429008c025
  | 1 => 0x24448c080c88910601209086c832244c221c92
  | 2 => 0xa88094912409402a8802a41252500944870518
  | 3 => 0x41529224820125515480024a4a4a009700ac0
  | 4 => 0xc919300371326499e693493800c0c191dde000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36362
namespace PEqualNP.Outside.L_meta_36362
open PEqualNP.Outside.L_meta_36362.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c38182140400004085000238085000000102ffd5009fe54007f55009fc5402ffd4c07fe53007f54c07fc53027fd0c07fe43007f50c07fc43017fd4805fe52017f54805fc52017fd0805fe42017f50805fc42017fcc805fe32017f4c805fc3202ffd4401fe51007f5440bfc51027fd0401fe41007f50409fc4101ffcc401fe31007f4c407fc31017fc8405fe21017f48405fc2102ffd4003fe50007f54003fc50027fd0003fe40007f50003fc4001ffcc003fe30007f4c003fc30017fc8003fe20017f48003fc20007fc4003fe10007f44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x826001ffd013000ffc8098007fd404c003fe2026001ffcc13001ff66098007fe304c003ef1826001ff0c13000fb86098007f8304c003ff9026001ff8813000ff44098007fd204c01ffc9026001ff0813000ffc2098007fc104c00dffb2e2006bfd9710037fccb88016fe65c400dfeb2e2000bf59710037f8cb8801afc65c400dffb262006bfd9310037fcc988012fe64c400dfeb262000bf59310037f8c98801afc64c401dffaa6200dff95310007faa988037fc54c400dffb1e2006bfd8f10037fcc78800efe63c400dfeb1e2000bf58f10037f8c78801afc63c401dffa9e200cff94f10007faa788033fc53c401bffa1e200cff90f10007fa8788033fc43c400dffb162006bfd8b10037fcc58800afe62c400dfeb16200bbf58b10037f8c58801afc62c4017ffa96200bff94b1005ffaa58802ffc52c4017ffa16200bff90b1005ffa858802ffc42c4017ff996200bff8cb1005ffa658802ffc32c40037f30e2006ffd4710037fca38801bfd51c400dfe28e2006ffd0710037fc838801bfd41c400dfe20e2006ffcc710037fc638801bf631c400dfe98e2000fd4c710037f8638801bff21c400dff10e2006fd88710037fa438802ff521c400dfe10e2001bf5831000ffea188007fe50c4003fea862001ff1431000ffe8188007fe40c4003fea062001ff1031000ffe6188007fe30c4003fe9862001ff0c31000ffe4188007fe20c4003fe9062001ff0831000ffc2188007f610c4003fd0862001ff0431000fe82188003ff65440017fb2a200aff9951002dfcca88003fd65440017eb2a200aff1951002df8ca88003ff64440017fb222009ff99110025fcc888003fd64440017eb222009ff19110025f8c88802bff5444013ff2a22000ff5511004ff8a888003ff63440017fb1a2008ff98d1001dfcc688003fd63440017eb1a2008ff18d1001df8c68802bff5344011ff29a2000ff54d10047f8a688027ff4344011ff21a2000ff50d10047f8868801fff624400f7fb122007ff98910015fcc48801ffd624400f7eb122007ff18910015f8c48801fff524400fff2922007ff5491003ff8a48801fff424400fff2122007ff5091003ff8848801fff324400fff1922007ff4c91003ff86488006ff6144015ffa8a2006ff94510007faa28801bfc5144013ffa0a2006ff90510007fa828801bfc4144011ff98a2006ff8c510007ec6288003fd3144001fa98a2006ff0c51003ffe428801bfe214400ffb10a2007ff4851003fea428801bfc21440037fb022001ffd411000ffca088007fd5044003fe2822001ffd011000ffc8088007fa4044003fea022000fe5011000ff88088007ff3044003ff1822001ff4c11000ff86088007ff2044003ff1022001ff4811000ff84088007ff104400dfd8822001ff8411000fec2088007fc1044003fa0822001fe04110
  | 1 => 0x3fe6154001feb0aa000ff18550035f8c2a8017ff515400bbfa8aa005ff9455002ffaa2a80037d515400bfe28aa017ffd0550007fc82a8003fd415402ffe20aa016ffcc550007fc62a8003fd315402dfe18aa015ffc85500affc42a8057fd215402bfe10aa001bfd815000ffea0a8017fb5054003ff282a001df9415000ff8a0a80077c5054003fc282a001ffd015000ffc80a8007fc4054003ff982a001ff8c15000ff860a8007ff2054003ff102a001ff4815000ff840a8007fe1054003fe082a000ffd9540005fecaa0053fe655000b7f32a8000ff59540005facaa0053fc655000b7e32a8001bfd9140027fea8a0053bf5450009ff2a28004ff55140027f8a8a0013bc5450001ffb1a8000bfd8d4009ffcc6a000efe6350001feb1a8013ff18d4001df8c6a0053ff5350027ff29a8000ff54d4009ff8a6a0013ff4350009dfa1a8004ff90d40027fa86a0003bd4350009fe21a8012ffd8940095fec4a004bfe62500057f3128012ff58940095fac4a004bfc62500057e3128012ffd4940097fca4a004bfd5250025fe2928004ffd09400277e84a0013fe4250009fea128012ef50940027f884a004bff3250025ff1928012ff4c940097f864a0003ff61500017fb0a8000ff98540007fac2a0003fc615000d7e30a8014ffd4540007fca2a0003fd5150029fe28a8004ffd05400277e82a0013fe4150009fea0a8000ef50540027f882a004fff3150001ff18a8000ff4c54009ff862a004bff2150025ff10a8012ff48540097f842a0006ff6050003ffa828001ff9414000ffaa0a0007fc5050003ffa028004fed014000ffc80a0007be4050003fe2028001ef1014000ff080a0007ff3050003ff1828001ff0c14000ffe40a0007fe2050003fe9028001ff0814000ffc20a0007fa1050003fe0828000ffd9530005feca98047fe654c00b7f32a6000ff59530005faca98047fc654c00b7e32a6000ffd9130005fec898043fe644c0097f3226000ff59130005fac898043fc644c0097e3226011ffd5130087fca898003fd544c021fe2a26001bfd8d3001ffea69800ffe534c007fea9a6003ff14d3001ffe869800ffe434c007fea1a6003ff10d3007ffec49803eff624c01fff3126002bf9893007ffac49803efd624c01ffe3126002bf1893007ffea49803ffe524c01ffea92600fff1493007ffe849803ffe424c01ffea12600fff1093001ffe649800fdf324c007ff1926003ff4c93007fba649800ffc324c001ffb0a6000bfd8530007fcc298003fd614c001fe30a6006bf1853008ffea298003fe514c001fea8a6011ff14530087fe8298003fe414c001fea0a6010ff1053001ffe629800fdf314c007ff18a6003ff4c530007ba629800ffc314c01fff90a600fff8853007ffa429803ffc214c0037fb026001ffd413000ffca098007fd504c003fe2
  | 2 => 0x3101ffe871880ffe438c407fea1c6203ff10e31037fec51881aff628c40dff3146202bf98a31037dcc51880aee628c40dfeb14621dbf58a31037dac518802ed628c40dfe3146206bf18a310effea518877fe528c43bfea94621dff14a310effe8518877fe428c43bfea14621dff10a3101ffe651880ffe328c407fe9946203ff0ca31035fcc31881bff518c40dff28c6206ff54631037f8a31881bff418c40dff20c6206ff50631037f8831881bff318c40def98c6203fdcc631037f8631881bf4318c40dff90c6206ff88631037ec431881bfd218c43bfa90c6206ff08631037fec11881bfe608c4037f3046206ff58231005fac11881bfc608c4037e304621fffd42310e7fca118873fc508c43dffa04621cff902310e7f8811880fff308c407ff1846203ff0c2310effe4118873fe208c43bfe904621cff08231037fc211881bfc108c401ffb2a6200bfd95310dffcca98816fe654c401feb2a6200bf595310dff8ca98816fc654c401ffb226200bfd91310d7fcc898812fe644c401feb226200bf591310d7f8c898812fc644c437ffaa2621aff95131007faa89886bfc544c40d7fb1a6203ffd4d3101ffca69880ffd534c407fe29a6203ffd0d3101ffc869880fde434c407fea1a6200f750d3101ff88698867ff624c4337fb126219ff98931015fcc498867fd624c4337eb126219ff18931015f8c498867ff524c433ff2926219ff549310cff8a498867ff424c433ff2126219ff509310cff8849880fff324c407ff1926203ff4c93101ff8649880eff614c437ffa8a6206ff94531007faa29881bfc514c435ffa0a6206ff90531007fa829881bfc414c407ff98a6203fdcc531037fc629881bde314c40dfe18a6206f70c53101fe86298867ff214c40dff10a6219fd885310cffa4298867f5214c40dfe10a6200ffd8131005fec098863fe604c4037f3026200ff581310c7f8c098806fc604c437ffa826218ff941310c7f8a09886bff404c431ff2026218ff1013101ffe609880fdf304c407ff1826203ff0c1310cffe4098863fe204c433fe9026218ff081310c7fc209881bfc104c4037fb2aa000ffd9150005fec8a805ffe64540097f322a000ff591500bff8c8a8012fc645400bffaa2a005ff951500befca8a8017fd545400bfe2a2a005df15150007fec6a8002ff635402dff31aa003bf98d50007fac6a805bfc63540077e31aa005ffd4d5002efea6a8017fe535400bfea9aa000df54d5002ff8a6a805fff435402dff21aa000ff50d500b7f886a8057ff625402b7fb12a015ff98950015fcc4a8057fd625402b7eb12a015ff18950015f8c4a8017ff525400bbfa92a005ff9495002ffaa4a80577d525400bfe292a015ffd09500affc84a8057fd425402bfe212a015ffcc9500affc64a8057fd325402bfe192a000ffd8550005fec2a800
  | 3 => 0xe202a22affcc151147fc60a88a3fc3054453ff902a228ff8815114ffa40a88a3fc2054451ff082a206ff04151037fecb2081aff659040dff32c8205bf99641037facb20802fd659040dfe32c8206bf19641025fac920813ff549044fdfaa48204ff95241027faa920813fc5490409de2a48206ffd8e41037fcc72080efe639040dfeb1c8200bf58e41037f8c72081afc639044fffa9c8226ff94e41007faa72089bfc5390409ffa1c8204efd0e41027fc8720813fd4390401dea1c8204ff10e41037fec52081aff629040dff3148202bf98a41037fac520896fd629040dfe3148206bf18a4112ffea520897fe529044bfea948225ff14a41027fe8520813fe4290409fea148204ff10a4112ffe6520897fe329044bfe9948225ff0ca41035fcc32081bff519040dff28c8206ff54641037f8a32081bff419040ddfa0c8204fdd0641037f8832081bf4419040dff98c8206ff0c641037fe432081bfe219040dfe90c8206ff08641037fec12081bfe60904037f3048206ff58241005fac12081bfc60904037e3048227ffd4241127fca120893fc5090409ffa048204ff90241027f8812089bff3090449ff1848224ff0c24112ffe4120893fe209044bfe9048224ff08241037fc212081bfc1090401ffb2a8200bfd9541006fecaa08027f6550447ff32a8205bf99541007facaa0802fd6550447fe32a8205bf19541006f8caa08167c655040d7fb228204ffd5141027fca8a0813fd5450409fe2a28200ffd8d41005fec6a088bfe63504077f31a8200ff58d41117f8c6a080efc6350447ffa9a8222ff94d41007faa6a088bfc5350409ffa1a8204ff90d41027fa86a0813fc4350443ffb128221bfd894110ffcc4a080afe6250443feb128221bf5894110ff8c4a080afc6250443ffa928221ff9494110ffaa4a0887fc5250409ffa128204ff90941027fa84a0813fc4250443ff9928221ff8c94110ffa64a0887fc32504097fb0a8223ffd4541037fca2a0803fd515040dfe28a8204ffd0541027ee82a081bfe415040ddf20a8206ff105410377882a0813f44150445ff98a8206ff0c54110ffe42a081bfe2150443fe90a8206ff08541007fec0a0802ff6050441ff3028201bf98141007fac0a0883fc60504037e3028223ffd4141107fca0a0883fc5050409ffa028204efd0141027fc80a0813fc4050445ff9828220ff8c141107f860a0887ff2050441ff1028221ff48141107f840a0883fe105040dfe0828206ffd9631035fecb1881bfe658c40b7f32c6206df9963102cfccb1881bfd658c4017eb2c6206df59631004facb1881bfc658c40d7e32c6206ffd9231035fec91881bfe648c4097f3246206ff59231005fac91881bfc648c40d7e324621fffd52310f7fca918803fd548c43dfe2a46203bf58e3101ffea71880ffe538c407fea9c6203ff14e
  | 4 => 0x80ffe3250c07fe9928603ff0c943007fec2a1802ff6150c01ff30a8600ff58543007f8c2a181afc6150c65ffa8a8632ff14543027fe82a1813fc4150c09de20a8603ffcc54301fbe62a180ffc3150c63ff90a8631ff8854318ffa42a18c7fc2150c01ffb028600bfd8143187fcc0a1806fe6050c01feb028630ff1814300df8c0a18cbff5050c61ff2828630ff14143027fe80a1813bf4050c09ff2028604ff1014301ffe60a180ffe3050c07fe1828631ffc8143187fc40a18c7fd2050c61fe1028630ff84143187f820a1816fd659440dffb24a206ff99251025fcc92881bfd64944017eb24a206ff19251035f8c928817ff549440bff2a4a22fdf9525102ffaa928817fc549440bbe2a4a206ffd8e51037fcc72880efe639440dfeb1ca200bf58e51037f8c72881afc639440bffa9ca205dfd4e5102ffca728817fd5394401bea9ca205ff14e5117ffe87288bbfe4394401fea1ca22eff10e51037fec52881aff629440dff314a202bf98a51037fac5288b6fd629440dfe314a206bf18a5102ffea528817fe529440bfea94a205ff14a5116ffe85288b7fe429445bfea14a22dff10a5116ffe65288b7fe329445bfe994a22dff0ca51035fcc32881bff519440dbfa8ca205fdd4651037f8a32881bf4519440dffa0ca206ff10651037fe632881bfc319440dff90ca206ff88651037ec432881bfd219445bfa90ca206ff08651037fec12881bfe60944037f304a206ff58251005fac12881bfc60944037e304a205ffd425102ffca128817fc509445fffa04a22cff90251167f881288bbff3094459ff184a22cff0c25116ffe41288b3fe209445bfe904a22cff08251037fc212881bfc109440d7fb2aa200ffd9151005fec8a8803bf64544015fb22a22bff99151025fcc8a8803fd6454457fe322a204bf1915100778c8a8812bc645440bffaa2a205dfd515102ffca8a8817fd5454401beaa2a205ff15151007fec6a8802ff6354455ff31aa203bf98d51007fac6a88abfc63544077e31aa205ffd4d5102ffca6a88ab7e535440bfea9aa205ff14d5102ef8a6a88afff4354455ff21aa200ff50d51157f886a88a7ff62544537fb12a229ff98951015fcc4a88a7fd62544537eb12a229ff18951015f8c4a8817ff525440bbfa92a205ff9495102ffaa4a88a77d525440bfe292a229ffd095114ffc84a88a7fd4254453fe212a229ffcc95114ffc64a88a7fd3254453fe192a205bfd855102ffea2a8817f7515440dff28aa206df94551037f8a2a881b7c515440bfa28aa22bffd0551037f882a88abff315440dfe18aa229ffc8551037fc42a88a7f62154453fe90aa229fd48551037f842a8803ff60544017fb02a228ff9815100dfcc0a8803fd6054451fe302a201bf1815102ffea0a88177f505440bff282a205ff1415115ffe80a88a3fe4054451f
  | 5 => 0x9154027fea8aa017bf5455009ff2a2a804df95154027f8a8aa0137c5455009de2a2a800ffd8d54005fec6aa0e3fe63550077f31aa800ff58d541c7f8c6aa00efc635500bffa9aa805dfd4d5402ffca6aa017fc5355009ffa1aa804efd0d54027fc86aa013fc435506fffb12a837bfd89541bffcc4aa00afe625506ffeb12a837bf589541bff8c4aa00afc625500bffa92a805ff9495402ffaa4aa017fc5255009ffa12a804ff90954027fa84aa013fc425506fff992a837ff8c9541bffa64aa0dffc3255001ffb0aa800bfd8554007fcc2aa003fd6155001fe30aa806bf1855402ffea2aa0177f515500bfe28aa804ffd0554027f882aa0e3ff3155071fe18aa837ffc85541bffc42aa0dffd215506ffe10aa800ffd8154005fec0aa0dbfe60550037f302a800ff581541b7f8c0aa006fc605500bffa82a805ff9415402ff8a0aa013ff4055009ff202a804ff101541c7fe60aa0dbfe305506dfe182a837ffc81541b7fc40aa0dffd205506dfe102a836ff841541b7f820aa00eff6554c01ffb22a600bfd91531affcc8a9812fe6454c01feb22a635ff19153025f8c8a9817ff5454c0bbfaa2a605ff9515302ffaa8a98037d5454c0bfe2a2a603bfd8d5301ffea6a9817df5354c07ff29aa603df94d5301ff8a6a980f7c5354c07ee29aa603ffd0d5301ffc86a980fde4354c07fe21aa634ffd89531a5fec4a98d3fe6254c057f312a634ff589531a5fac4a98d3fc6254c057e312a605ffd495302efea4a9817fe5254c0bfea92a634df5495302ff8a4a98d3ff4254c69ff212a634ff509531a7f884a980fff3254c07ff192a603ff4c95301ff864a9803ff6154c017fb0aa600ff98553007fac2a9803fc6154c0d7e30aa605ffd455302ff8a2a98177c5154c6bffa0aa635ff1055301ffe62a980ffc3154c69ff90aa634ff885531a7fa42a98d3fc2154c01ffb02a600bfd815319ffcc0a9806fe6054c01feb02a633ff1815300df8c0a9817ff5054c0bbfa82a605ff9415302ff8a0a98d7ff4054c67ff202a633ff1015301ffe60a980ffe3054c07fe182a634ffc815319ffc40a98d3fd2054c67fe102a633ff8415319ff820a9803ff6550c017fb2a8600dfd9543004fecaa18cbfe6550c0b7f32a8600ff59543005facaa18cbfc6550c0b7e32a8600df1954302cf8caa180eff6450c09ffaa28604ff951430277ca8a1813fd5450c01deaa28604ff1514301dfec6a180fff5350c07ff29a8603f794d4301ffaa6a1803dd5350c07fe29a8603ffd0d43027be86a180ffe4350c07df21a8603ff10d4301f7886a180fdc4350c63ffb128631bfd894318ffcc4a180afe6250c63feb128631bf5894318ff8c4a180afc6250c63ffa928631ff9494318ffaa4a18c7fc5250c09ffa128604efd0943027fc84a1813fd4250c63dea128604ff1094301ffe64a1
  | 6 => 0x944ae0a24973ed2953b60000bd1db50b0353b340f1c40002361b70004604d64f02f224b4f40f92782e40ee3aa20823e07c25104328d1a334e3633ca0000f54071112632791c719e0001cb4200004b13841bb00023b0001953e500019d1801722190ba4f128f3ac0f24c83354b733447c00003e0000003bb0f10000000000004980ab40900000007740500007f00038e3672663a405b3441c11f12880004a33264e013d2132570003232d50a820a3580004cb5104e81440001cf01239117800019121804f0c30003f30001740002ff0000003430000b84a12870e831700005947d23525c26c0d116a3381ee27c4ff42c00004832a1a50b01560141ad0b518b4f33b74e61ef18521c01c1074940e421b31c0451931282c10db45d49506a16d4404312cd2c52063710000002f713a3d312917b2f437c0fa0004500400003874e54b83a24231e906d2c820d0610000003f43e83763d83ff05509921f1233de1dd00000000024d30813134600030339531145552b0000003220c807b02e5031640000c40000653f100009b1f722a26f2b800046352e48606e17f009002000000000000300001101a078000000220000200501000c0402205c00009007004000000090000000004a02a0202701a01202c00002032004000080100100282500a0000d8110260000000001e010050170020080100007e00000802002078000250480200000300400001804000010000010000080000c0020200b803010000028050260100000101c010028000040400802200604c160030060300000000c0140c80003e0000180c0080040181300a0000400500004c050030040340600102e000010050000cc028090000ac00025000000008000000000100b0080140080400e0040501c00001c0480100a000070120100000680900204401803000018018000160102901000201c008020000180400802e01c0880400c1740100203a0300000600e06c0400101201000000004000008190020680f80101200c008000000300d80a0040e40280000001c0400100200005810000044000010181100280005e0680a01a00a008000030000b41103e0c81101e81c0040700200309400003801004008180040420480380000003c040000000100580301a0080c8070000080e002002028010040720100000003c03c000000000080480a0000a00100600400001013012014008070060140000b026058058040440000280100200400800004004000130060300000004a054008080080040000000000c0200100600c0e00000400c058250060800180e0000440c00004a0242d00600e0040083b000000000000100040100d034018010020000540280500001402000032004008000040140180001a0000e80a016014078130280100300000203c0500100001405800030028097fb2aa804bfd
  | 7 => 0x31f61b43283090e22280665130ec15450000043e41600f4f62b62a436c0000002be3ce0000723140000000700000cc45f4670002e835a0002123ec3572233e42320e74ea2624cc38b3831352a04d344c13441800036212b0c151b02d0b61aa1592341082b015852836e28b0001f22c93d04b22f11962dc44b27e48f4c92d31ea1ca18336411c2090bc16c03d4792bb3cc08c29700b52d1bd19b1a700d5181df0ac1f41860052842162a249343c33a4aa2bc3c11500fd4524cf00040340b41e3a84be40d00032b17905305e35127211301009f08724534032d46c0711491041b52fe07e20322c08b30145a22d1e10493971753f64e21cd50d0a726b1420eb2d639d30d02926426d4011903ae4444b54e32b12981e424138a2d85201731522f834a3fc14e2934ed12250208e2a70da4c551241c3e148343b3c747a0e55270242eb3521a944138008f03f1143eb22150f00046d0c201b0b327448200000017000000000000003c53122715531000005816915302823838800000000c0cd0003e950a0a14c30000443b000040c4bb4320000850000ed4610000002f33e70b42153861e610c25f0002890a531f4c714c2db49f52446906f4df27d02b2ca29002c3591c037a1481a412520e2da0c70cf0fe19927718a4fb26e00000023913343509d0df39e0693240760814774f544817e0f04141452104e116813749220c1dc3390000fc09200000013b19f33300000028145112e22f00034500030a0223793db0003ef15b00000a2174d424239600000000000047e0002e925300003a33d0003071b20002ba1010673f51c342145600000011f38f43001345800016000001e0000005260000002ce52f4c412a2de0000000002bf1d33a523102f1fa20000000047f39a3470003f95080000000000000834662a90000af0000914d200025b22028600045e49a12448a04120f0000000001471eb2b321a51d37d4283134240001ed0b75230cb50e31b4b60010630001060000003420d952c3372023561c905227a3d704b22437e45c4960001384fa0003c000002000000051e22b33600036d1362443753cf0954494b92a348b44a1844000000730000be2d03a02d21ce0f315e4f83e34ad3fe2594b30002583a70003b940249b52500000041300000000053000000029d44519c0780ad0d613e17a0d40543193f22af1a61d928a31839304e42e10b05f1f342d33246e4d935e3cb1d50001fc3020002610324873271190ef49e2294734ac00038200e2ed2e13c52ef2760004f25223d53d43734a44742bd37209829a1e83610002fb47100021e21d18230e04a2a14473af0194ec36b0a600035401537f1620002922750004890000003bc0000002f941a2c211600000000014f26917100000000043a5072a61f93500000004fd18d15a2ae0001f84814251210e938c1
  | 8 => 0x1411bf4651d84c132c4fc4b04120e63b80034ce11e4194a71fd1d651f2cb44f32e00816613210f0000000000d24423941c52714b403646b17d2f00962470000004380001e700051c0002e500029e00001800000024f0ea0000791ac25a2c427f00038900015f3ea00044331a35f0680000000090381182b913f0000002e74ef10a3690f611a30b08925e4761a833b0ff21107d2ac12d2dd3c41d706c4884530d829b05d24a2fd3b200000000042f0003740332072500004ba0c03491b83813be14b1430004d541b1a24900162e235539831e1c608636a1ae0004570dd1cc1173f71302704720024c21bc4de4341e23d62940b93b50425062b523d4a83783b409430c2822043e049c33e1d123f4060262222ea01a4e43a951509e35d4113da3fa4dc2d70643c95172cc16b18741f35b04c1a10fb0000071020bf2d44e948d03b0232a548e2493c32b71fb2ad33105751134c3054ee1be3ba0f81101d03904684040f44f71b12fc0a915d4170000004d11091c209a39b3a313c1654084c61ff00030423c17636528c4ca18f3cd05647b14a12c3ab0001f04260000000000880000000000754fe0001ec0000000b220500028e00016f0843662140000000312e606034d0004a53250004d70820a34cd2e049d29c25d0002b22250aa0460804bf2f500051443d0000a03a103724c26514619218e2331b94dd51626a0a429634b2a81771894f934f29930f00030600002500600052a35c0004da31d44d3290dc02143319a0c61ba08a2d11de0bb11529f1c80e30110003531883dd50543f01f00012748414d11246f46a00000004701d2cf0002460004a637700000000038d18100000000024e3ee2f62673853d91e01b64643b107a3603e611b00000040e5093ad00000047800040a0000270004e73e20ae0f700029114022e3c80930d34853211984593fb15c2c008d48c2554d800041d1974eb0d505110d0003bf4c03154a02832604ab11d5211fe00044e15120b00015723a09751a1e50002371630b110e0ce27b05c42a33f1030175014620004db4373202c35293f02400001610e02562853bd0003411264bc0000300d718c1b016e43650449100036800050c36f02a3d10002df4992e317c1da0d047031610505a2d939c0002803004af0c945b42b04d0000004152c70500340004101a037b00033c2ee1ab06b0003dc0000de4541203920e14392522480743c63fd3d22fa09c39f3701002aa12f1d41e31391af0c51d21f53482683df2ab2c60004272260004a91675194d00002012b42ec0623124294800000000ca4222303f80903a62732540003992434bd4750040000390003304a232f3c24461b
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf7259110014fe7259110004fd7259110014fc725911020cff7159110006f77159110104ff7059110006fb7059110004ff7655110004fe7655110004fd7655110004fc765511001cfe76d8d10046de63d8d1002cfe75d8d10004fd75d8d1002cfc75d8d10024fe74d8d10004fd74d8d10024fc74d8d10004ff72d8d10014fe72d8d10004fd72d8d10014fc72d8d10006de32d8d10046dc32d8d10034fe71d8d1000cfd71d8d10034fc71d8d10046df31d8d10006f621d8d10006f521d8d10034ff70d8d1000cfe70d8d10034fd70d8d1000cfc70d8d100e6df30d8d100e6dd30d8d10046dc6358d10205f77158d10004ff7558d1002cfe7558d1002cfc7558d10004ff7458d10024fe7458d10024fc7458d100e4ff7358d10006df7358d10004ff7258d10014fe7258d10004fd7258d10014fc7258d10204ff7158d10006f77158d10006f62158d10006f52158d100c4ff7058d10006fb7058d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d1002e7c6554d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d100557c7550d10006bf6450d10026bc6450d1002cff765451000cfe7654510144fd765451000cfc76545100067f655451002e7c6554510005bf745451004dbc7454510005fb705451000df87054510024ff765051000cfe7650510104fd765051000cfc76505100057f75505100557c7550510006bf6450510026bc6450510005fb705051000df870505101fdf6768c510036f6768c51003776758c51003775758c5100c5f5738c51001ef6638c51001ef4638c510035f7728c510037e6728c5101f5f5728c510037e5728c510005e5728c5101eef7628c5101eef5628c51000df6708c51000df4708c510036f7608c510037f3608c5100e7f2408c51001cff764c51000cfe764c5100c4fd764c51000cfc764c510006df634c51001edc634c510037d4314c510005fb704c51000df8704c51000df4764c51001ef4764c51000cf4764c510035f7734c510037d7734c510007d7634c51001ef6634c51001ef4634c510047d4634c510047d6434c510007d5434c5101e5f7724c5101e5f5724c5101def7624c5101def5624c510007f3704c51000df6704c51000df4704c5100c7f0704c510036f7604c510037f3604c5100c7f2404c5100c7d7304c5100c7d5304c510035f87650110026f87650110034f8765011000dfb745011000fbb7450110007bb6450110026fa6450110026f8645011004fb864501101d7bb545011004fb8545011004fbb4350110007b9435011004fbb42501101cfb94250110007f37150110035fa7150110035f87150110007f0715011000efb615011000ff3615011004fbb4150110007b94150110007f23150110007f131501101cff221501101cff12150110
  | 1 => 0x931000cfe7159310034fd715931000cfc7159310036be4159310036bc4159310106bf4059310106bd4059310036fa1059310036f91059310004ff7655310034fe7655310004fd7655310034fc765531002e7e65553100067d6555310004ff7558f1002cfe7558f1002cfc7558f10004ff7458f10024fe7458f10024fc7458f10036df7358f10066de4358f10004ff7258f10014fe7258f10004fd7258f10014fc7258f10034ff7158f1000cfe7158f10034fd7158f1000cfc7158f10036de3158f10036dc3158f10036f62158f10006f52158f100c6df3058f100c6dd3058f10004ff7654f10034fe7654f10004fd7654f10034fc7654f1023e7f6554f1002e7c6554f10004ff7650f10034fe7650f10004fd7650f10034fc7650f100057f7550f100757c7550f10236bf6450f10026bc6450f1001ede6350f10006dd6350f10035f7764c71022ef7764c710037d7734c710037d7634c71001ef6634c710036f4634c710037d4634c710067d6434c710007d5434c710225f7724c710225f5724c710036f7624c71021ef5624c71000df6704c71000df4704c7100c7d7304c7100c7d5304c71002cfe76d95100567e65d9510024fe74d9510004fd74d9510024fc74d95100067e54d95100567c54d951001cfe73d9510004fd73d951001cfc73d95100567f53d9510004ff72d9510014fe72d9510004fd72d9510014fc72d95100067e52d95100567c52d9510034fe71d951000cfd71d9510034fc71d95100567f51d9510006f621d9510006f521d9510034ff70d951000cfe70d9510034fd70d951000cfc70d95101667f50d95101667d50d95100567c6559510005bf745951004dbc7459510215f77159510164ff75595100067f7559510004ff7459510006bf7459510004bf7459510024fe7459510024fc7459510006bc7459510024bc7459510004ff735951001cfe735951001cfc7359510004ff7259510014fe7259510004fd7259510014fc72595100567f52595100067d5259510214ff7159510006f77159510006f62159510006f52159510144ff7059510006fb7059510024fe76d911004ebe64d911002cfe75d9110004fd75d911002cfc75d9110006bf54d911004ebc54d911001cfe73d9110004fd73d911001cfc73d911004ebf43d9110004ff72d9110014fe72d9110004fd72d9110014fc72d9110006be42d911004ebc42d9110034fe71d911000cfd71d9110034fc71d911004ebf41d9110034ff70d911000cfe70d9110034fd70d911000cfc70d9110126bf40d9110126bd40d91100057f75591100557c755911004ebc645911020df77159110004ff75591100067f75591100047f755911002cfe755911002cfc75591100067c755911002c7c7559110124ff7459110006bf7459110004ff735911001cfe735911001cfc7359110004f
  | 2 => 0x4fd71d9130276df31d913001cff70d913001cfd70d9130266bf40d9130266bd40d9130024ff76591300057f755913008d7c7559130086bc645913025ddf7359130005ef725913007dec7259130005f77159130005f4715913026dfb7059130004ff75591300067f75591300047f755913002cfe755913002cfc75591300067c755913002c7c7559130264ff7459130006bf745913025cff7359130006df7359130004ff7259130006ef7259130004ef7259130014fe7259130004fd7259130014fc7259130006ec7259130014ec7259130086bf4259130006bd4259130004ff7159130006f77159130004f77159130034fc7159130006f47159130034f4715913009edf3159130184ff7059130006fb7059130004ff7655130004fe7655130004fd7655130004fc7655130034fe76d853002cfe75d8530004fd75d853002cfc75d8530024fe74d8530004fd74d8530024fc74d853000cfd73d8530004ff72d8530014fe72d8530004fd72d8530014fc72d8530006f741d8530006f441d8530256f631d8530256f531d853000cfe70d853001cfd70d853000cfc70d8530206f710d853008d7e75985300057d759853007dee7298530005ed7298530006f76198530045f97098530065fb7058530036f66118530006f56118530004fe7694530004fd7694530034fc769453001dde7394530005dd7394530004ff7654530004fe7654530004fc76545300067f655453002e7c6554530005bf7454530085bc7454530004fe7690530004fd7690530034fc769053001dde7390530005dd7390530004ff7650530004fe7650530004fc76505300057f755053008d7c755053000ddc764c530036dc764c53000cdc764c530006df644c530006dd644c53024ddf724c53024ddd724c53001ddf714c53001fd7714c530007d7614c530036de614c530036dc614c530007d4614c530247d6214c530247d5214c530007db704c53000dde704c53000ddc704c5300c7d8704c53000dd8704c53001edf604c53001fdb604c5300c7da204c530247d9204c5300367f7559710004ff7459710006bf7459710004bf7459710024fe7459710024fc7459710006bc7459710024bc74597100767f5459710004ff735971001cfe735971001cfc73597100067e53597100767c5359710004ff7259710014fe7259710004fd7259710014fc72597100767f52597100067d5259710034ff715971000cfe7159710034fd715971000cfc71597100367e51597100367c5159710036f62159710006f521597101467f50597101467d5059710004ff75593100067f75593100047f755931002cfe755931002cfc75593100067c755931002c7c7559310036bf7459310004ff735931001cfe735931001cfc7359310004ff7259310014fe7259310004fd7259310014fc7259310034ff715
  | 3 => 0x87050d40026bf6050d40027bb6050d40187ba1050d40034fe76d854002cfe75d8540004fd75d854002cfc75d854000cfd74d854001cfe73d8540004fd73d854001cfc73d8540004ff72d8540014fe72d8540004fd72d8540014fc72d8540006f751d8540006f451d85402a6f641d85402a6f541d8540006f731d8540006f431d8540006f621d8540006f521d8540024fd70d854020ef710d8540006f7619854004df970985400057f75585400a57c755854006dfb70585400a57e75185400057d751854009dde7318540005dd7318540095ee7218540005ed7218540036f66118540006f56118540004fe7694540004fd7694540034fc76945400067f659454002e7c6594540025be7494540005bd749454017f3c549454000dfa7094540005f97094540004ff7654540004fe7654540004fc765454002e7e65545400067d6554540005bf7454540025bc74545400a73f545454000dbc7650540036bc765054000cbc76505400073f75505400a5be75505400a5bc75505400073c75505400a53c7550540005bf735054029dbf725054029dbd7250540025bf7150540027b77150540007b76150540036be6150540036bc6150540007b46150540036b46150540007bb705054000dbe705054000dbc7050540107b87050540026bf6050540027bb6050540107ba1050540004fe768c540004fd768c540034fc768c5400a57e758c5400057d758c540025be748c540005bd748c540095ee728c540005ed728c54000dfa708c540005f9708c540004ff764c540004fe764c540004fc764c540025be744c540005bd744c54001ede634c5400079d434c54002cfe76d953008e7e65d953019cfd75d9530024fe74d9530004fd74d9530024fc74d95300067e54d953008e7c54d953000cff73d953001cfe73d953000cfd73d953001cfc73d95302967f53d95302967d53d9530004ff72d9530014fe72d9530004fd72d9530014fc72d95300067e52d953008e7c52d9530034fe71d9530004fd71d953008e7f51d953001cff70d953001cfd70d95302867f50d95302867d50d953002cff765953008e7c655953027ddf7359530005ef725953007dec725953028dfb7059530284ff75595300067f7559530004ff7459530024fe7459530024fc745953027cff7359530006df7359530004ff7259530006ef7259530004ef7259530014fe7259530004fd7259530014fc7259530006ec7259530014ec725953008e7f52595300067d5259530004ff7159530034fc715953019cff7059530006fb7059530024fe76d9130086be64d913002cfe75d9130004fd75d913002cfc75d9130184fd74d913000cff73d913001cfe73d913000cfd73d913001cfc73d9130276bf43d9130276bd43d9130004ff72d9130014fe72d9130004fd72d9130014fc72d9130034fe71d9130
  | 4 => 0x455002f7771545500077761545500367e61545500367c61545500077461545502ef7621545502ef7521545500077b705455000d7e705455000d7c705455014778705455002e7f605455002f7b6054550004fe7690550004fd7690550034fc769055002d7e75905500057d7590550006bf6490550026bc64905500bf3c5490550004ff7650550004fe7650550004fc76505500057f755055002d7c7550550004fe768c550004fd768c550034fc768c55002d7e758c5500057d758c5500adee728c550005ed728c550004ff764c550004fe764c550004fc764c55002d7e754c5500057d754c55002cfe76d95400a67e65d9540025be74d954000dbd74d95400a73f54d95401b4fd75d954000cff74d9540024fe74d954000cfd74d95402d6bd74d954000cbd74d9540024fc74d95402e67f54d95400a6bf54d95400a63f54d95402e67d54d95402e6bc54d954001cfe73d9540004fd73d954001cfc73d95400067e53d95400a67c53d95402e6bf43d9540004ff72d9540014fe72d9540004fd72d9540014fc72d95400a67f52d95400067d52d9540034fe71d9540004fd71d95400a67c51d9540024ff70d9540024fd70d95402d67f50d95402d67d50d954002cff76595400a67c65595402cdbf74595400bf3c5459540005f77159540005f471595402ddfb70595402d4ff75595400067f75595402ccff7459540006bf74595400a6bf54595400be7e54595400be7c54595400bebc5459540004ff735954001cfe735954001cfc73595400a67f53595400bebf4359540004ff7259540014fe7259540004fd7259540014fc7259540004ff7159540006f77159540004f77159540034fc7159540006f47159540034f471595400a67f51595401b4ff7059540006fb705954001cfe76d8d4009ede63d8d4002cfe75d8d40004fd75d8d4002cfc75d8d4000cfd74d8d4001cfc74d8d4009ede43d8d402c6dd43d8d40004ff72d8d40014fe72d8d40004fd72d8d40014fc72d8d402c6bf42d8d40006bd42d8d40034fe71d8d40004fd71d8d40024fd70d8d4025edf30d8d400057f7558d400a57c7558d4009edc6358d40005ef7258d40095ec7258d40005f77158d40005f47158d402bdfb7058d40004ff7654d40004fe7654d40004fc7654d4002e7e6554d400067d6554d40005bf7454d40025bc7454d400a73f5454d4000dbc7650d4001ebc7650d4000cbc7650d400073f7550d400a5be7550d400a5bc7550d400073c7550d400a53c7550d40006bf6550d40006bd6550d40025bf7350d400279f7350d400079f6350d4001ebe6350d4001ebc6350d4009f9c6350d4009f9e5350d400079d5350d402b5bf7250d402b5bd7250d402aebf6250d402aebd6250d40005bf7150d40236bc6150d4009f9f3150d40007bb7050d4000dbe7050d4000dbc7050d40187b
  | 5 => 0x1ddc7354531037d43154531024ff765053101cfe7650531114fd765053101cfc76505310057f75505310dd7c7550531006bf6450531026bc6450531005df735053101ddc7350531037b4415053100cfe76d81310c6fa60d813102cfe75d8131004fd75d813102cfc75d8131024fe74d8131004fd74d8131024fc74d8131034fd73d813100cfc73d8131004ff72d8131014fe72d8131004fd72d8131014fc72d813101cfd71d813100cfc71d8131006f621d8131006f521d81310c6fa30d81310c6fa10d81310c6f86058131024fe76d915002d7e75d915000d7d75d91500bebe64d91500bf3e54d915000cfd75d91502ce7d75d915000c7d75d9150024fc75d91500be7e54d91500bebe54d91500be3e54d915032ebd54d91500be7c54d915001cfe73d9150004fd73d915001cfc73d915032e7f53d9150004ff72d9150014fe72d9150004fd72d9150014fc72d9150034fe71d9150004fd71d915032e7f51d91500bebc41d915002cfd70d91502cebf40d91500bebc64591500bf3c5459150005f77159150005f47159150325fb705915001cfe76d8d500b6de63d8d5000cfd75d8d5001cfc75d8d50024fe74d8d50004fd74d8d50024fc74d8d500b6de53d8d5031edd53d8d50004ff72d8d50014fe72d8d50004fd72d8d50014fc72d8d5031e7f52d8d500067d52d8d50006de32d8d500b6dc32d8d50034fe71d8d50004fd71d8d5002cfd70d8d5027edf30d8d500b6dc6358d50005ef7258d500adec7258d50315fb7058d5000d7c7654d5001e7c7654d5000c7c7654d500bd7e7454d500bd7c7454d500067f6454d5002d7f7354d5002f5f7354d500075f6354d5001e7e6354d5001e7c6354d500b75c6354d500b75e4354d5030d7f7254d5030d7d7254d503067f6254d503067d6254d500057f7154d5023e7c6154d500077b7054d5000d7e7054d5000d7c7054d5019f787054d5002e7f6054d5002f7b6054d50004ff7650d50004fe7650d50004fc7650d500057f7550d5002d7c7550d50026be6450d500bf3e5450d500075d5350d50034fe76d855000cfd75d8550024fe74d8550004fd74d8550024fc74d855001cfe73d8550004fd73d855001cfc73d8550004ff72d8550014fe72d8550004fd72d8550014fc72d85502fe7f52d85500067d52d85502fef651d85502fef551d8550006f741d8550006f441d855002cfd70d8550216f710d8550006f76198550055f97098550005bf74585500bdbc7458550075fb70585500adee7218550005ed7218550036f66118550006f5611855000d7c76545500367c765455000c7c76545500073f74545500bd7e74545500bd7c74545500073c74545500bd3c74545500067f64545500057f73545501567e63545501567c63545502f57f72545502f57d72545502ee7f62545502ee7d625455002d7f715
  | 6 => 0xc7558231004ff7458231024fe7458231024fc7458231004ff7258231014fe7258231004fd7258231014fc7258231034fe715823100cfd7158231034fc7158231036df3158231036dd3158231036f62158231006f52158231036fb70582310e6fa40582310e6fa3058231036fb1058231036f8105823102cfe76d95310de7e65d9531024fe74d9531004fd74d9531024fc74d95310067e54d95310de7c54d9531034ff73d9531034fd73d95311767f53d95311767d53d9531176de43d9531004ff72d9531014fe72d9531004fd72d9531014fc72d953101cfd71d95310de7f51d9531006f621d9531006f521d953100cfe70d9531004fd70d953100cfc70d95310de7c6559531005bf74595310d5bc7459531345f77159531174ff75595310067f7559531004ff7459531006bf7459531004bf7459531024fe7459531024fc7459531006bc7459531024bc74595310de7f5459531154ff7359531006df73595311567e53595311567c5359531156de4359531004ff7259531014fe7259531004fd7259531014fc72595310de7f52595310067d5259531344ff7159531006f7715953123e7e515953123e7c5159531006f62159531006f52159531004ff705953100cfe705953100cfc70595310de7f5059531024fe76d91310d6be64d913102cfe75d9131004fd75d913102cfc75d9131006bf54d91310d6bc54d9131034ff73d9131034fd73d9131136bf43d9131136bd43d9131004ff72d9131014fe72d9131004fd72d9131014fc72d913101cfd71d91310d6bf41d913100cfe70d9131004fd70d913100cfc70d91310057f75591310dd7c75591310d6bc645913133df77159131004ff75591310067f75591310047f755913102cfe755913102cfc75591310067c755913102c7c7559131134ff7459131006bf7459131114ff7359131006df7359131004ff7259131014fe7259131004fd7259131014fc725913133cff7159131006f77159131236be4159131236bc4159131004ff705913100cfe705913100cfc70591310d6bf4059131004ff7655131004fe7655131004fd7655131004fc765513102e7e65551310067d6555131005f77155131035f47155131035dc7650d31026dc7650d31034dc7650d310075f7550d310075c7550d31006df6550d31006dd6550d3101ddf7450d3101f9f7450d310079f6450d31026de6450d31026dc6450d310d79c6450d310d79e5450d310079d5450d310d79f4250d313379d4250d31007d77150d31035de7150d31035dc7150d31007d47150d3101edf6150d3101fd76150d312379e4150d312379c4150d31337d62150d31337d52150d31005df7050d310d79f4050d3102cff765453101cfe7654531154fd765453101cfc76545310067f655453102e7c6554531005bf74545310d5bc7454531005df7354531
  | 7 => 0x9631014fe7259631004fd7259631014fc72596310fe7f52596310067e52596310067d52596310fe7c5259631034fe7159631034fc71596310367e51596310367c5159631036f62159631006f52159631004ff705963100cfe705963100cfc70596310fe7f50596310067e50596310fe7c50596310067f74596310067e74596310067d74596310067c74596311567f73596311567e73596311567d73596311567c73596311567f43596311567e43596311567d43596311567c43596310067f72596310067e72596310067d72596310067c72596310067f42596310067e42596310067d42596310067c42596311567f32596311567e32596311567d32596311567c32596310367f71596310367e71596310367d71596310367c71596310367f41596310367e41596310367d41596310367c41596310367f31596310367e31596310367d31596310367c31596310367f21596310367e21596310367621596310367d21596310067521596310367c21596310067f70596310067e70596310067d70596310067c70596310067f40596310067e40596310067c40596311567f30596311567e30596311567d30596311567c30596310067f20596310067e20596310067d20596310067c20596310367f10596310367e10596310367d10596310367c1059631004ff755923102cfe755923102cfc7559231036bf7459231116bf4359231116bd4359231004ff7259231014fe7259231004fd7259231014fc7259231034fe7159231034fc7159231036be4159231036bc4159231036df3159231036dd3159231004ff705923100cfe705923100cfc70592310f6bf4059231004ff7655231034fe7655231004fd7655231034fc765523102e7e65552310067d65552311beee6255231005f77155231035f47155231006ef7558a31006ee7558a31006ed7558a31006ec7558a31006ef7458a31006ee7458a31006ed7458a31006ec7458a31006ef5458a31006ee5458a31006ed5458a31006ec5458a310eeef7358a310eeee7358a3134eed7358a310eeec7358a3134eef5358a3134eee5358a3134eed5358a3134eec5358a3134eef4358a3134eee4358a3134eed4358a3134eec4358a31036ef7158a31036ee7158a31036ed7158a31036ec7158a31036ef5158a31036ee5158a31036ed5158a31036ec5158a31036ef4158a31036ee4158a31036ed4158a31036ec4158a31036ef3158a31036ee3158a31036ed3158a31036ec3158a31006ef7058a31006ee7058a31006ed7058a31006ec7058a31006ef5058a31006ee5058a31006ec5058a31006ef4058a31006ee4058a31006ec4058a3134eef3058a3134eee3058a3134eed3058a3134eec3058a31036ef1058a31036e71058a31036ee1058a31036ed1058a31036ec1058a31004ff755823102cfe755823102cf
  | 8 => 0x17f3f40d954137e7f74d954117e7e74d954117e7d74d954117e7c74d95410067f73d95410067e73d95410067d73d95410067c73d954117e7f43d954117e7e43d954117e7d43d954117e7c43d95410067f72d95410067e72d95410067d72d95410067c72d954117e7f42d954117e7e42d954117e7d42d954117e7c42d95410067f32d95410067e32d95410067d32d95410067c32d954117e7f71d954137e7e71d954117e7d71d954137e7c71d954117e7f41d954137e7e41d954137e7c41d95410067f31d954137e7e31d954137e7c31d95410067f21d954137e7e21d95410067d21d954137e7c21d95410067f70d95410067e70d95410067d70d95410067c70d954117e7f40d954117e7e40d954117e7d40d954117e7c40d95410067f30d95410067e30d95410067c30d95410067f20d95410067e20d95410067d20d95410067c20d954137e7f10d95410067e10d954137e7c10d954111e7c6559541375f7715954117cff75595410067f755954115cff7459541006bf745954113cbf7459541004ff735954101cfe735954101cfc7359541004ff7259541014fe7259541004fd7259541014fc7259541374ff7159541006f77159541004ff705954100cfe705954100cfc705954117d7e761954111e7e761954117c7e761954136e7f641954136e3f64195410067e63195410067c63195410067f62195410067e62195410067d62195410067c62195413667f611954136777411954136f3e411954136f3c41195413677441195410067e60195410067c60195413673f401954101cfe76d8d410067f65d8d410067c65d8d41116de63d8d4102cfe75d8d41004fd75d8d4102cfc75d8d41034fd74d8d41116de43d8d410f6dd43d8d41004ff72d8d41014fe72d8d41004fd72d8d41014fc72d8d41024fd71d8d4135ebe41d8d4135ebc41d8d41116df31d8d4100cfe70d8d41004fd70d8d4100cfc70d8d410f6bf40d8d410057f7558d4111d7c7558d410067f6558d410067c6558d41116dc6358d41355f77158d41004ff7654d41004fe7654d41004fc7654d410067f6554d4102e7c6554d4102cff7654541024fe765454115cfd7654541024fc76545410067f655454102e7c6554541005bf7454541025bc7454541037b4415454100cfe76d81410067f65d81410067c65d8141106fa60d814102cfe75d8141004fd75d814102cfc75d8141034fd74d814100cfc74d814101cfe73d8141004fd73d814101cfc73d8141004ff72d8141014fe72d8141004fd72d8141014fc72d8141024fd71d8141106fa40d8141106fa10d81410057f755814111d7c75581410067f65581410067c6558141106f860581410367f7559631004ff7459631024fe7459631024fc74596310fe7f54596310067e54596310fe7c54596311567f53596311567d5359631004ff725
  | 9 => 0xe76d8151006bf64d8151006bc64d8151146fa60d8151034fd75d815100cfc75d8151024fe74d8151004fd74d8151024fc74d815101cfe73d8151004fd73d815101cfc73d8151004ff72d8151014fe72d8151004fd72d8151014fc72d81510767f52d81510067d52d815102cfd71d8151006f621d8151006f521d8151146fa50d8151146fa10d8151005bf745815115dbc7458151006bf6458151006bc6458151146f860581510367f755964113ebf745964115e7f545964113ebf545964113e3f545964115e7d545964115ebc5459641004ff735964101cfe735964101cfc73596410067e535964113e7c535964115ebf4359641004ff7259641014fe7259641004fd7259641014fc725964113e7f52596410067d5259641034fe7159641034fc71596410367e51596410367c5159641004ff705964100cfe705964100cfc705964113e7f5059641004ff7558e4102cfe7558e4102cfc7558e41036df7358e41136de4358e410d6dd4358e41004ff7258e41014fe7258e41004fd7258e41014fc7258e41034fe7158e41034fc7158e41036de3158e41036dc3158e41004ff7058e4100cfe7058e4100cfc7058e41136df3058e41004ff7654e41004fd7654e41034fc7654e4123e7f6554e4102e7c6554e41005bf7454e41025bc7454e4113f3f5454e41235bf7650e4101ebf7650e4101cbf7650e410073f7550e4113dbe7550e4113dbc7550e410073c7550e4113d3c7550e41236bf6550e41006bd6550e41025bf7350e410279f7350e4101ebe6350e412379e6350e412379d6350e4101ebc6350e411379e5350e410079d5350e41236bf6250e41386bd6250e41235bf7150e41007b77150e41237b47150e41026be6150e41027b66150e412379f3150e41004ff755824102cfe755824102cfc7558241006bf545824104ebc5458241004ff735824101cfe735824101cfc735824104ebf4358241006bd4358241004ff7258241014fe7258241004fd7258241014fc7258241034fe7158241034fc7158241036bf4158241036bd4158241036fb7058241126fa4058241036fb1058241036f8105824102cfe76d954111e7e65d9541034ff74d9541034fd74d954117e7f54d954117e7d54d954101cfe73d9541004fd73d954101cfc73d954111e7f53d95410067e53d954111e7c53d9541004ff72d9541014fe72d9541004fd72d9541014fc72d954111e7f52d95410067e52d95410067d52d954111e7c52d9541024fd71d954111e7f51d954100cfe70d9541004fd70d954100cfc70d954111e7f50d95410067e50d954111e7c50d95413657e76d954102c7e76d95410067e63d95410067c63d95410067f62d95410067e62d95410067d62d95410067c62d954117f7741d954137f3e41d954137f3c41d954117f7441d95410067e60d95410067c60d9541
  | 10 => 0x9151006bc62d915113f3f52d91510073d52d915113fb751d91513bf3e51d91513bf3c51d915113fb451d9151007b621d9151007b521d9151006be60d9151006bc60d915113f3f50d91513bebf75d915115ebe75d915113ebc75d9151006bf73d9151006be73d9151006bd73d9151006bc73d915113ebf53d915113ebe53d915113ebd53d915113ebc53d9151006bf72d9151006be72d9151006bd72d9151006bc72d915113ebf52d915113ebe52d915113ebd52d915113ebc52d9151006bf32d9151006be32d9151006bd32d9151006bc32d915113ebf71d91513bebe71d915113ebd71d91513bebc71d915113ebf51d91513bebe51d91513bebc51d9151006bf31d91513bebe31d91513bebc31d9151006bf21d91513bebe21d9151006bd21d91513bebc21d9151006bf70d9151006be70d9151006bd70d9151006bc70d915113ebf50d915113ebe50d915113ebd50d915113ebc50d9151006bf30d9151006be30d9151006bc30d9151006bf20d9151006be20d9151006bd20d9151006bc20d91513bebf10d9151006be10d91513bebc10d915115ebc64591513b5f7715915113dbe761915115ebe761915115f3e751915115f3d751915136ebf651915136e3f651915115f9e731915115f9d7319151006be6319151006bc63191510073e53191513af3c5319151006bf6219151006be6219151006bd6219151006bc62191513af3f52191510073d5219151376bf61191513afb7511915136f3e511915136f3c51191513afb45119151007b62119151007b52119151006be6019151006bc60191513af3f50191510357c76551510267c76551510347c765515102d7f745515102f3f74551510073f64551510267e64551510267c645515115f3c64551510263c64551511557e73551511557c735515115f3f43551513a57f72551513a57d72551510077771551510357e71551510357c715515100774715515102e7f615515102f77615515139f76215515139f7521551510057f705515101cfe76d8d5102d7e75d8d51006bf64d8d51006bc64d8d51156de63d8d511575e53d8d51034fd75d8d510347d75d8d51024fe74d8d51004fd74d8d51024fc74d8d510fe7f54d8d510067d54d8d511567e53d8d51156de53d8d510fedd53d8d511567c53d8d51004ff72d8d51014fe72d8d51004fd72d8d51014fc72d8d510fe7f52d8d510067d52d8d5102cfd71d8d513967e51d8d513967c51d8d51156df31d8d51006f621d8d51006f521d8d5100cfe70d8d51004fd70d8d5100cfc70d8d510fe7f50d8d51005bf7458d5115dbc7458d51006bf6458d51006bc6458d51156dc6358d5138df77158d51004ff7650d51004fe7650d51004fc7650d510057f7550d5102d7c7550d51006bf6450d51026bc6450d510073d5450d5101ede6350d511575e5350d5100cf
  | 11 => 0xcfe76d81430067f65d81430067c65d8143186fa60d814302cfe75d8143004fd75d814302cfc75d814301cfd74d8143024fd73d8143004ff72d8143014fe72d8143004fd72d8143014fc72d81432bebf42d8143006bd42d8143034fe71d8143004fd71d814326edf31d8143186fa40d8143186fa30d81430057f75581431957c75581430067f65581430067c6558143005ef725814318dec7258143005f77158143005f47158143186f86058143036bf745925117e7e545925117ebe545925117e3e545925111ebd545925117e7c5459251004ff735925101cfe735925101cfc735925111e7f5359251004ff7259251014fe7259251004fd7259251014fc7259251034fe7159251034fc71592510367f51592510367d5159251036be4159251036bc4159251004ff705925100cfe705925100cfc705925117ebf4059251004ff7458e51024fe7458e51024fc7458e51036df7358e51176de5358e510dedd5358e51176de4358e51004ff7258e51014fe7258e51004fd7258e51014fc7258e51006de3258e51176dc3258e51034fe7158e51034fc7158e51036de3158e51036dc3158e51036f62158e51006f52158e51004ff7058e5100cfe7058e5100cfc7058e51176df3058e5123d7f7654e5101e7f7654e5101c7f7654e5117d7e7454e5117d7c7454e510067d6454e5102d7f7354e5102f5f7354e5101e7e6354e5123f5e6354e5123f5d6354e5101e7c6354e511775e4354e5123e7f6254e513c67d6254e5123d7f7154e51007777154e5123f747154e5102e7e6154e5102f766154e5123f762154e513c7752154e51004ff7650e51004fd7650e51034fc7650e510057f7550e5102d7c7550e51026bc6450e5117f3e5450e5101ede6350e51006dd6350e510075d5350e51004ff7458251024fe7458251024fc74582510067e54582510567c5458251004ff735825101cfe735825101cfc73582510567f53582510067d5358251004ff7258251014fe7258251004fd7258251014fc7258251034fe7158251034fc71582510367f51582510367d5158251036f62158251006f52158251036fb7058251166fa5058251166fa4058251036fb1058251036f81058251024fe76d915115ebe64d9151034fd75d915115ebe54d915113ebd54d915101cfe73d9151004fd73d915101cfc73d915115ebf43d9151006be43d915115ebc43d9151004ff72d9151014fe72d9151004fd72d9151014fc72d915115ebf42d9151006be42d9151006bd42d915115ebc42d915102cfd71d915115ebf41d915100cfe70d9151004fd70d915100cfc70d915115ebf40d9151006be40d915115ebc40d915115dbe76d9151024be76d91513bf3f75d915113f3c75d9151006be63d9151006bc63d91510073e53d915113f3c53d9151006bf62d9151006be62d9151006bd62d
  | 12 => 0xd32d95433ee7c32d95430067f71d95430067e71d95430067d71d95430067c71d95434067f41d95434067e41d95434067d41d95434067c41d95433ee7f31d95433ee7e31d95433ee7d31d95433ee7c31d95430067f21d95430067e21d95430067d21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d95434067f40d95434067e40d95434067d40d95434067c40d95433ee7f30d95433ee7e30d95433ee7d30d95433ee7c30d95430067f20d95430067e20d95430067d20d95430067c20d95430067e10d95430067c10d954302cff76595431967c65595433f5bf74595433fddf73595433ecff75595430067f75595433f4ff7459543006bf74595431c4ff7359543006df7359543004ff7259543014fe7259543004fd7259543014fc7259543004ff7159543034fc7159543004ff705954300cfe705954300cfc70595433ed7e76195431967e76195433ec7e76195433df3e74195433e73d74195433e67f64195433e75e73195433df5d73195433e67f63195433df5f43195433e73e43195433e73c43195433e75c43195430067f62195430067e62195430067d62195430067c62195433df3f42195430073d42195433df3c41195433e75f31195430067e60195430067c60195433df3f401954301dbc765514302ebc765514301cbc7655143025bf75551430273f75551430073f655514302ebe655514302ebc65551431973c65551430079f735514301dbe735514301dbc73551431c79c7355143026bf63551430279f63551431c73f53551431c79e53551431c73d53551433d5bf72551433d5bd7255143235bc71551431973f51551431c79f3155143005bf7055143025dc7654d4302edc7654d43024dc7654d4301ddf7554d4301f5f7554d430075f6554d4302ede6554d4302edc6554d431975c6554d430079f7454d43025de7454d43025dc7454d431af9c7454d4301edf6454d4301f9f6454d431af5f5454d431af9e5454d431af5d5454d431979d5454d430071d5454d431975f5254d433cf5d5254d431af9f4254d433cf9d4254d43005df7154d431975c5154d431af9c4154d431975f5054d431af9f4054d43034fe76d85430067f65d85430067c65d854302cfe75d8543004fd75d854302cfc75d854301cfd74d854333ebd74d8543024fd73d8543004ff72d8543014fe72d8543004fd72d8543014fc72d8543356f641d8543236bc41d854333ef631d8543006f621d8543006f521d854300cfe70d8543004fd70d854300cfc70d8543356bf40d8543006f610d8543006f410d85431957e75985430057d75985430067f65985430067c659854318dee7298543005ed7298543006f761985430057f75585431957c75585430067f65585430067c65585430067f65185430067c6518543036f66118543006f56118543
  | 13 => 0x81543267f51d81541b6fa50d81541b6fa40d8154005f77158154005f471581541b6f86058154024fe76d91531aebe64d915301cfd75d91531aebe54d915341ebd54d915302cfd73d91533f6bf43d9153004ff72d9153014fe72d9153004fd72d9153014fc72d9153034fe71d9153004fd71d91531aebc41d915300cfe70d9153004fd70d915300cfc70d91531aebf40d91531aebc6459153415df735915301d7c76551530267c765515301c7c765515302d7f745515302f3f74551530073f64551530267e64551530267c64551531af3c64551530075f735515301d7e735515301d7c73551531c75c735515302e7f635515302f5f63551531c73f43551531c75e435515340d7f725515340d7d725515323d7c71551530057f7055153034fe76d855301cfd75d85533467d75d8553024fe74d8553004fd74d8553024fc74d855338e7f54d85530067d54d855302cfd73d85533467e53d85533467c53d8553346de43d8553004ff72d8553014fe72d8553004fd72d8553014fc72d855338e7f52d85530067d52d855338ef651d855323e7c51d8553346f631d855300cfe70d8553004fd70d855300cfc70d855338e7f50d85531a5ee7298553005ed7298553006f76198553005bf74585531adbc7458553036f66118553006f5611855300cfe76d815319efa60d815301cfd75d8153024fe74d8153004fd74d8153024fc74d815302cfd73d8153004ff72d8153014fe72d8153004fd72d8153014fc72d81533167f52d81530067d52d8153034fe71d8153004fd71d815319efa50d815319efa30d8153005ef72581531a5ec725815319ef8605815302cfe76d95431967e65d95431c4fd75d954301cff74d954301cfd74d95434067f54d95434067d54d9543024ff73d9543024fd73d95433ee7f53d95433ee7d53d9543004ff72d9543014fe72d9543004fd72d9543014fc72d95431967f52d95430067e52d95430067d52d95431967c52d9543034fe71d9543004fd71d95431967f51d95431967c51d954300cfe70d9543004fd70d954300cfc70d95431967f50d95430067e50d95431967c50d95433e57e76d954302c7e76d95433ef3f74d95433ef3c74d95434075f73d95433ef5c73d95434075f43d95433ef3e43d95433ef3c43d95433ef5c43d95430067f62d95430067e62d95430067d62d95430067c62d95434073f42d95430073d42d95434073c41d95433ef5f31d95430067e60d95430067c60d95434073f40d95433ee7f74d95434067e74d95433ee7d74d95433ee7c74d95433ee7f73d95433ee7e73d95433ee7d73d95433ee7c73d95433ee7f43d95433ee7e43d95433ee7c43d95430067f72d95430067e72d95430067d72d95430067c72d95434067f42d95434067e42d95434067d42d95434067c42d95433ee7f32d95433ee7e32d95433ee7
  | 14 => 0x304f00000101600f00100100a02100000300100b01700501200000000400600000000006600000000a00100000201600100102f00000600c01000c00a04200801602002c02a00d00501701101200100600200002800100800000400600001900102700400200300000f00000000400703100700100000101607401000d00100e01000100100002e00300400e00e00709100000300800900601100200000a01b04c00000501c00500401b03b00000000402d01500400201300200600700006100c00701600202900501a00100001500000600a00200200100600700000300800b00707200e00d01201201900200100100200007a00100101d01e00500c0000000000000020040040030010000030010000000a000000b00001301706800000c00400000a00300300100300200101700100200700801200f00000000d00900000301c00100000001100a00800200100c00009c00000800800700900000100200100007500200000101601200500000201700200500802600a00200200700200200100000001001201400000401b00300200000200300100200300000500503d00600001e00100000000000100001a00000401701600400100600c00000000300800200600000f00300001400000d00100701200b00700101900804c00600000a00500400604d00701d00300401700000100d00300202200c02600200c00300100c00000400b00900000100300400a03000300004200000200000200700100101400400000400600300000a00000300500000000305800900000200000000000e00200101800001200100000101800003600001400100600400000800400c00703400400400f00a00300101f00202200100e00202400000000000100200000200100000800e03200b01cfe76d8d541c6de63d8d54024fd75d8d5402cfd74d8d541c6de53d8d541c6de43d8d54004ff72d8d54014fe72d8d54004fd72d8d54014fc72d8d54034fe71d8d54004fd71d8d5400cfe70d8d54004fd70d8d5400cfc70d8d541c6dc6358d54034fe76d8554024fd75d855402cfd74d855401cfe73d8554004fd73d855401cfc73d8554004ff72d8554014fe72d8554004fd72d8554014fc72d85543b6f651d8554376f641d8554006f621d8554006f521d855400cfe70d8554004fd70d855400cfc70d8554006f610d8554006f410d855437e7f65985543bebf6498554006f7619855437e7f65185543bebf64185541bdee7218554005ed7218554036f66118554006f5611855400cfe76d81541b6fa60d8154024fd75d815402cfd74d8154326bf54d81542de7e54d81542de7c54d81542debc54d815401cfe73d8154004fd73d815401cfc73d81543267f53d81542debf43d8154004ff72d8154014fe72d8154004fd72d8154014fc72d8154034fe71d8154004fd71d
  | 15 => 0x1b88fc5400a30bd25f873475312318b4e6c9921c08ae0c605cf1ac80011c80550a895380009371cb00008da34a09300008140003fb80000006ea38d904c7da0004a996b4fec23d2a885fc1e07a9094a35800003700000000007c83968000e726ee12a933d3127ae3bc8a007a210f00010fcbe419807019f87be31245593ac0f267d2dc8c1083e05a19c1a8c5ae1fc4828374a521dd424833d2488923db125439a34f4819b450823da3d613ecf142cf22e8000eec0cb1188000a9a1284158e7000062c19ca5b12707d04601c0cd8c60a4119404d120ec096a5008b437841a1da0e9e3a625ea16c12823925f1f60f7446642f84c4292443340170474406e49795287b001b3fc8ed8b500a125611ac5742052ef88346766cf0ad01e12341802d90490e42985011a59070c55f2040bf10fe5f540d80507d27b11b718f8c1a29410084640b217d2f396f0cf42f70ab02c910a62f00781e90dc98c2f1083805a15834b9bbd0ba8d537c11789308094382210c5c3903958f3836e66a16084683466e2260a59cc6c33c0551df91bc7e946c92d891e0d138313bd0ca8d433c191cb6603329917284d85c932d8308fbc8ac4869214f320100329a903a45962568ae51c200401700000301000100201500001300500400600000300000400b00000000e00f01100300400100000200003700200100000100100301100600300e00f00d00a03300200100202301300500001100101400a00000c00000000000503400000d00b00000300100300000800100300703301000000000000000e00100100100a02700e01600800a01e00000200200400700000200300100100500100000000000000001a00300000000900400e00301401200601000800501000100000100100000300004b01803e00300900200100900e00300300000000702500000100301100000000400300000000600300101700d01103100000200100200f03d01800400f00600600101100801202300a02002a02c01900101600f00407002201500200000000100004b02e00f01d00200800b00000b00000201700201a00500000800900700700a00100000102f00100000001400300200100000000100200100000600400700a00100000000201202b00000000100300500a00e00000600000000000400300000600800303c00100300102e01901200f00200d00000500f00301105002200000000501700403d00800500300200500900000000000a00300200000000000200d00000400a01700000100000d00200002700300200400100007000200500301100809b00301000000100301d00200300400300301500200002900400000200000f00002100300201a00c00000500500600a02903600400400102500000300000000e00003b02600400100000900101c05000300001200f01a005000009009
  | 16 => 0x22dc63c63300000001de00000015a5002000164119400000018e1fac90647f000064c000026115800000044e3668000e960521b18810f5e75c379800065e01d22b096ca240000000a8d062761000187917c7290ea00004ba2922ad19b400010d03b21bd2c60000bb9648ef400023c000000041d00009240005684670da000078d30da41ccee7463a2a15530e83f00294809905db4ac81a8d4468c2998ff83a064418981912562a93ee1fb841095d42199248ce40b2b582640fe7e61a91b2888a2dd0e0882c8c808d10009dc71c0f60dd0010aae00003ba0c043a00043a14d491238d21b0d745541cc4241200e0813635ba03c1086d03b700005881b92ae1d0463e90436e197075a23c05c000082850d1d4a5c04427190a0239c8962c74080000968000000061c32e5ec3de9bc40000001c91ecc00024c0000af4b4a0000070f247a682218080005aa6c743a90c400055922a9ddc85a000175800026a20908102450b459d2d800003a689a1d5820c00014507b80007b60000601574b8400016c860cc0636700001f0f780000000000946860485025c0000e600015892622da0000000ce44ee025a0f92ac0000001ef804a0000001b7909626004b19a40689143d20c3c0005e14a4a04c6b60000000a140000581241c88ade7872470f486608f51e01e191d43aa07c8c9904a0003c4986891a2a429d89acf8892c16f000129475835c248445e04800000001724c30d023c088200025120e50ec64c02086e033c2131d2a3a452006101c9bc09da8cd29d1da4b1691d3e88bc8f8273e31a1edc27e6c82a982f43a225330b0da46367953c10b002945d033812449028001bb8270d6422913707a8a383d52628f411f46b34bea320c3207039325d8d061f71770d84bcc7e0313085451e5c64b0829111896a04721f80006410d413dc7c492e00003d50fa4c716f906496252817f22e01564d84c7059d3226244bd139c77e6cb0d2062461261419a14540001db00000ec1e43703708cb800069a2c30894be21d8401066420c35517c19ccb5884c4311f003043b92aa93484946ff2160000c222e61bc9a48d6c000000220c92622314411e8b8603e15082241be83d26d9f7c7907f146794bc5da66800000000008dd4341328fce6604ac1ba067c58c4100e783de72e1918eec8ec38f4a78948dd685705e12b89a21cb35f08b4c122432eb24988a23e7054896906a0ca3118428aec899204a2a825637b0bc0d089e43a44a70dc4d0436c34319ec4b208a2af1794df46674578a9d0709933b28d3405e5732b884e87f65241859c44dfa3a146918d475e5042c19e44f1e96811b10182c27dd17a06f834e49213412a5308459245037826649900a8388d1019647f9b7c01219210626091421cf0f697ac3442a849aa054f9a69e0728df8db45b5288249400036a1
  | 17 => 0x29e1cecb4291b17b1e0c3ce71807700000005e9000000001498d3010a1c7ba0000000000e1042f4051d00d4c4d700c964c0000002e9013820892800007d800000018504c800092d42e08c033e00000012c92469450001f2801807d1e50c5823633f47f000111640e3fa192809256d2e297fc00014c1e180010d862a0001dcc45400000013f00004420f4800045000027000008462ca18e9b38e027d63979a9d0940004ba00006c077c1cc12a89bc4f00910db421289c1ab8000fd000041b0e64a3000004096690383ba00005980000cc10d02092661c20639c904c40000338110ad432200b800000000014e94ac336979000000094a87b2441838f0a08c0001ccc58a46813994885388bf1a70000c268331578790ffa55b3dca02ca6070c2f701409f21b41e201ad06e0000001da800000738f09e400047520b8ac40007920de00480d27201a20e30bd46210ce0000406618398034c5d28c20001e3000017b21a90a0ff895a0bca534be04f14431ce800079600000002da000082a19c7b20001740c5c9a893900016d00005f30000369220000485826ceaa07445e9b98526687234811d18a04540722a08c603d170193c1d64370ff150cdee14200020a02a067f000000022800000006c4d2c00001a8000f8e4741010ee05c83de1da000016a81f2961f552dc308152815c000585459800061a0003b687684ac73400000000000020001e044a84e600024544769460000000bde00049002182b62740a3993862200035595d01301c900000000000a00000694cac000000224513c2cb00000007402ef24d231c0006e72c1199000017c2438d04ba60000fc813c000218062801923c34c0f41f3cc7800002b22d089a7b40000cd50cc00038726400000003b385387dc0000000cad10e3884441f5c4208403ed000113a00020e0000acc9114b9a25050862542708785a057518ca4085165422db17f077c08010b09c8f6093f2111400bbc0004a5a200f8400038e1b3078c66300020b00000000001d300000001b99ac5042851000188098c1dc24315203089120e19944cea88a214950027a12a3f292fc5d47ab4830e747cc16339a8e5110427d28707f493873c32308b109a52d0c682f8aa014d37b086c36470d3e1a158ec65ce39c0294baa0003b600007f85310d30d9076a00047d89c47464271448310fe4000000192096a36b3b5a5c4a82536000000000000006c03f89d07aa00020105685a21cf9dc07ec4620f29940cbe64524da4f8dda77b1f2225c00027f08a97e4d0a28e2fd86383ea24b00000007c053f0bb0620d7e1950eb1eb50e22112c3a5c8c7a18a18c0000caa6d62b2129c48451907a000000000000025447e200021907c4e2034546b840400000026e8e548f25fa2ce0fb08a60002659e78c0058849483e80000c109805740006e014d8000
  | 18 => 0x11be7283891fec82c00000016ec57849f000141c78e8900001c4d284762000116c000000072149c4407bf0001ba40007d900000000006273af1aa8cdc3073218c406749220001628ff44ec0000c00f164342c008880004d90000594a1470f00005880003f236099509883b02c78cb0634716006853d07409a01b23ac57668a31d23b91b800000001181a80000000e000d05d811d25e05863910000000daa2ad1ab2618fc20954c500000000003bc0ffc11080744a8fd01900003fc1090fd483b42a08282684113c820584f000000016040002143988000ede64006705a80000600d996e8f1c1b648499480007d42520000e925da0b798ad0521114120e5c9740000ce8de92c00000000000a8e24036ba3b41a01732a21ad08a08f823883a005643b1b3021400032a3ce1f2cb305af36a1a8488e6e44ad80908083d718311c90303f046d8940b805d731ca1a470671f12f8fe841e0f12278c90ce81ca00891704642cc4728510bee67629c86b00001c5198855100647b00b2430f4e0e717a9dc80008452df04844f60000001ab40ea02a010a3d80be051000243cb2e48b00002fc0005a300015605fe6ec0c0889d15a86415a84dc83c17435d829cce28473a3a3988d809f3d296345a60713ce9fb0c0241a27216dd11e7940eaa31903228229a11180001434170000de40000de80000002c24661b940002b02b6138887209000006fc15e1df031903c4b039b25c8000adc9002100bec3765cd01880000f65600001060000000458a46123e01f0e202d8dba5614369a54000000000046000000013a8000c3e4da0e305b06fa3401ad000000065e000226128200000000012ea4b3000000038e00036209bc3540ff000138c00045807c000000025e000000018670215b897126042e3a112a00001173259ed53104cc4ab81b465200000015580000002680acc78a18543d0000000567450000000073f00002752ca3bc4aa0a542764ff05a1c1409457f0ab9468920029479017470a584439078cf766664c5a07436a4f40fa245cfea3930040d24cba72506d8ef479e81446d20b4b5c00000007e889044023714f8bb216b0001278d920001f096ac0002b60000000bd09662129f2444c3b7087000046a191350113066e5ed3f78d4cf4c0ac081800005007e0af838cd4a8894619fc0c108a43f19644e468a9275000024a1482ca80006e4000059982c44893416480000000001fb800070e00b0000b8c6de5e021f1af400000000000011440000000000d7818b00012dc00075600000008d40000181b480002be24615f116c8c12d2183c0000004bd800000000013f105450c4c24408000aa823326f8938cae3b341e0bf40007d2272a5b44708a52291d6464e3584648d946661ec4a810000004443420fd44ec2192dc1e683d68730d803f11a250c03323806e8000
  | 19 => 0xc45c987000000037d8c84b327a837f06bcfb665a15914082388d83cb8d7883608f0000000d5030e0aca24d2a449d2909ca86a83e822b800c00021f2be98c80007a20001fb4e000d9000000062a2f034784e10bc8ec2ff000109e70b43b9ab853e05b3b209911a01e011f14986fe062331251000034b38503cc97607234991282bc6c024a140d13e8610971a509404b00d68000df86120000d88a360002ee142020077f28484300003200a912989a68261d416fca5452507e813439c0930c79d9887001e0d716790f279f16a1cc919429a2c724652aa46f19b1c511d07150d58c0c3c47c53a81c7475c75b1288c08b4c2f3291875c15c2631a41d0cb2088d23995e53020001689bd4a709360fd842090827c1a19370a8c0003b8a5a501a0000000000000752000249c2e053700023cc87a54b02016a8aca1e63c41aa40988631a31035202305043994c55859f2a90d700b88bc2831cdd08860417100e8df2000396153d2bc000000022c07e7a349e80007f05453aa048cd5e0001c51df428c0e949d91f08be2993dc010c0004e934099e4e880000000000818269000000000030c33e0370cc28e30000b34ba20000630fa800061d28590f013c12700024702fc4e13ae9b1427c4fa122a2980003f917090840008594041a40d8680530393545441123f205c83fe49738b81ccdb606c17284580006b0000168000024d0000004ea28b22bd06a48569320ec9774c6282f00009c08fc92a00005a4db05c716b13340007cc000175000012000007c91740000000fcc27200000000006a281e2e424590a68f10c31d282e210b34e2600b5200027c1d204ce89b3e31ad400000048418a4cca57b000000040c0b100000010642f928e8080a98000153158c0443b209600f0f0068e2130cb4e4e0272e580003800000000e08438000083a0480000bb009a57c32841008f00000000003030b482aa00000010046500383a71e84d741102018d407c621212388d00005c44359a34aee94847780011a669d40b9cf474e4f505d000000040700000007de81a3141a447987740a99444c1862228b80007d62070d0a5711ee7ff0f0a0a852c2e716d800115c98f00014f492c0001c4a4f000000027e8298c2a1ee00023f40006d92671a600000004b780000000ad3cc00007160d70ef07e02962411ea093cebe97700e2438f3600007d9ab00304d613698dc1c24a12d888b90b00003f10000c2029e44b253114e00000016240004024b11650eea00000005a0000850000066914686a2de99ac0004770000f3479625700017d852263817d00000000000001048c7696b3b0147d1f866f0541c251886f44711e806ea7ce0000a5c0644610b2024851a97c34d8f089e618c08983343e665825e0a28bfa4540001478d168062028f700000b72828cf408459b47a1b8c75833228984f
  | 20 => 0x122169c2ea37c07514b911c28c27b0f580a64b82fc260c3e051616322c023a31413d1b08eae3c10580b70a1e43026019350f07fe3211b4cc0a2ae1af920916a71a2579f4c4cc0d602a0c950844fe40613242828f906aa44c7fa43328a185c32028115f91f528e43a4bf97d0cb287c05100b0bc62ce49d0068f2634723811244d485202f1790afc0000690570000384000000000000000007200002ab14199b000057010b800000069f01715c904e3b114c1fcd1960000001d340007071788000f6411f16c1e107ca00009791804c24ab45d8bb108c81107681bcd320c94a190a8eb45491328580af03760b718fcd725c
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8ee871c9654c0018deea392ca9800333dcc72595300143e43aa4b2a6002c6c72549654c00b0fd0fbaac89800a3ba1f725913000637baee4b226000c6c75dc9644c0010ff0ab92c8980161f21572591300047bc0ae4b2260068f4815c9644c0011dd0e392c8980031bdd47259130006363a8e4b2260028bc87509644c00d1ed0fb8ac8980031ddd771591300063a3aee2b226000ce772dc5644c0019c8e5b8ac8980031ddd471591300063a3a8e2b226000ce7721c5644c0019c8e438ac8980021fe15765513000477c12ecaa260028ec825d9544c0011ef02bb2a89801a3d20576551300056ac1883b0a6000af180107614c0011ef0eb08c29800637219739453000cec402e728a60048be849d9514c00117b093b2a2980030f1d3655453000c6e432e720a60019d8805ce414c00b0fd0b3b282980021f61676505300346e43ac898a60019da87dc1314c00917d0fba2cb881b70fdd474597100343f43ca6b2e2080c3c7494d65c400117f08b92cb880122f21172597100343e43aa4b2e2087c3c7454965c410b968e890acb8800399549215971002c3f43eeab26206dc3f741d564c40010ff0ab92c9880161f215725931037c3fc2aecaa620778bf845d954c400d0f90eb2aa9880128f211655531001c3ec2eeca9e20008bf845d953c400917908bb2a78800e2f6137650f100043fc2aeca1e200587c855d943c400d1b90eb1a87880030f5d254d95100053cc04a9b2a2000a758194b6544001ccca490eca880122fa1f74595100061fba8e8b2a200087f855c9654400117f08b92ca880122f21172595100046fc1ae4b2a20038dc835c965440050f90ea92ca8821f0f1d152595100065a3a6e2b2a2086cb47488565440051e90e90aca882172d1d1215951000732a9242b2a2000c3d75d53644400147d0b216c8880161fa1f75591100061e3aee8b22200087f855c9644400b0f90ab92c8880022fe1172591100046fc1ae4b2220038dc835c964440018e8ebb8ac8880021fe1576551100045fc22ecaa220008f7815d954440059cce490ec688213b10c921d8d100043fc2ae4b1a200587c855c9634400117f08b92c6880122f2117258d100046fc1ae4b1a20028f487485634400117f08bb2a6880122f2117654d1000477c12eca9a20028ec825d953440070fd0fb2aa6880161fa167650d100043ec2ceca1a200087f855d9434400b0f90abb286880023be097650d1001476412eca1a20008f7815d9434400717d0fb2286880030f1d76450d100061e3a6caa8a2000c3c75d91414400d9cec0b94628801b78d81728c510006f1202e518a20018fa86dc13144009970eca1a80880eace2154350110005e8c18e2a022000be1821c540440033710ea0a808801b2e1d941501101d59c42a82a022006db07150540440017c30518a8088003e450d3150110
  | 1 => 0x8e890aca988039954921595310061ebaea9b22620587e87dd5644c401878ebba2c8988021fe15725913102c3e42ae4b2262008fb805c9644c4031f100b92c8988021fe1576551310045fc22ecaa2620487c87595544c40947908b2aa89880e3da1b71551314062e3b6eaa1a627bc5c761d5434c401c3ca9b2a86988123721d6550d310070eb2aa8a1a6246b9481551434c401aaeea38a86988030f1d365545310061e3aec8a0a62008bf845d7604c40917908baec0988021fe1574d813102c3e42ae9b02620187d85dcb6454001968c838ac8a80034d150715915000666196e5b1aa000a5d858cb63540070f90ab8ec6a80022fe1171d8d500245e422e3b1aa07c87e87d91535400b0f90a3b286a80030f9507650d5000c3f436eaa1aa00595c8754d43540011df04b9ec2a800a3b20973d85500053ac2883b0aa000af180107615400d9ccc2b90c2a80023de1d61185500055a422c230aa000ce572584615402f27d0fba2a2a81df0f1db745455036e1fbb0e8a8aa06dc3c761d151540db0fd0fb22a2a805f0f1d364545500069a3a6c2a8aa000d347418551540016cb0430aa2a80034e1d3705455000c3e432eb20aa000c3d75d92415400b0f90a3b282a80061fa1b75505500343e42ced18aa00187c865d631540030f90cbaa62a805e4f211754c5500051ec24a7b2a80018bd84dcb65500050ff0ea96caa00028fe1152d95400063a328e2b2a8000d34541c5655011387eebba2caa000237e0d725954001c6e41ae4b2a80008f7815c9655000d1e902b92caa001a3da1f71595400063bba8e2b2a8000cb7741c565500010ff0ab8ec6a00161f21571d8d4001c5e422e3b1a800387c87595535008f4e902b2aa6a00062fa1b7454d403dc9f43eeaa1a807dc3c76dd54350001a70e1baa86a01f30f1d87550d400a61e3aecaa1a8000e1e53d9543500071790eb2a86a011aad2056550d40024ce43aa6a1a8000e1d6554d435008d968c3b8a86a00036c8437150d400069c3aee0a1a800087f855cf615000b0f90ab9ec2a00023be0973d854001476412e7b0a8000ae58214761500014ed0b98ec2a000a3de1d21d85400047bc3ac230a8000a748558461500031790cba4a2a00030fd9574945400347c432e128a8088d38545c25150009179083b2a2a00030fd5076545400343e43acaa8a8017c3c74595515000d4e902b2aa2a00062fa1b74545403649f43eeaa0a806fc3c76dd541500dfc68c3baa82a01b70fdd8755054036e1e3b0eaa0a806de34611d5415000d56d0db0a82a00034d1d761505400069a3a8c2a0a8000d3875dc141500031790cba462a001a3e219708c54002c3f428ec98a800087d851d931500031790cba262a00524f215744c5400061eba4a9b2a6000a5d8394b654c0051dd0fb92ca980021fe1572595300046fc1ae4b2a6000
  | 2 => 0x20d95410051ec2041b2a8200a5e8308365504014bb06106caa09be9da0420d95410053ac0841b2a820087f855c9655040117f08b92caa08028f612631954146d3ac0cc632a820087d87988655040147b09310caa0a329d60662195410043fc3ac432a8200a3f84588655040147b09300caa08021fa1f6558d410043f438cab1a820387e87d95535045f878e9b2aa2a08030fd97745454113e1e32ee8a8a826cc3c74197605040317908baec0a09be1f21b75581410043f43ecab02820087e8719560505178eee232ac0a081a1fa1e54596310061fba4a8b2c620687e87949658c40d4ed03292cb1881a1f21d52596310167339242b2c6200e6652485658c401ccaa490acb188028fa1250596310051ec24a0b2c6200c3f749d1658c40d4e902ba2cb188030f5d074596311552f418e8b2c6200a5d831d1658c40147d09392cb188028f61272596310353b40ce4b2c6200a75819c9658c40d4ed02392cb1887e9d60472596310043f43c84b2c620087d87909658c40d4ed03212cb188029d60642596310353b40884b2c6200a7581109658c40d4ef0490acb1881b99e0921596310073339242b2c6200e6572485658c401ccc8490acb188039950921596314573399242b2c628ae6432485658c40147d09382cb188028f61270596310353b40ce0b2c6200a75819c1658c4010fd0f202cb188021f61e40596310353b40880b2c6200a7581101658c40d4ed03902cb188029d60720596310073290e40b2c6200e6521481658c4010fd0e102cb188021f61c20596310051f42040b2c6200a3d84081658c4554bd06102cb188029760c20596310353b40840b2c6200a7581081658c40d1e902bb2a91881a1f21d65552310251e422caaa46200c7565dc5548c40d5cd023aac518876b96047558a310053742ee8b146200a6d85dd1628c40d5cd03ba2c518876b96077458a3100717aa4a8b146200ae781551628c40d5c902aa2c5189a6b3a0c5458a3100566c18a8b146206ae6819c1628c47b5cb03382c518802b3e0d7058a3134d6641ae0b146200a6e851c1628c4014db0a382c518802aba107058a3100556c20e0b14621dace831c1628c40159b06382c51881ab9a047058a310ed72c08e0b146200ce9701c1628c40155d09282c518802ab6125058a310357340ca0b146200ae581941628c40d5cd02282c518802b96045058a310053742c80b146200a6d85901628c40d5cd03202c518802b96064058a310357340880b146200ae581101628c40b0fd0bba2c1188021f61774582310167339242b046200c3d74953654c4014bb072a6ca9881a3760f72d95310245f43ee8b2a6200c3f751d1654c40117f08b92ca988122f21172595310047dc02e4b2a62018f8805c9654c4050f90ea92ca98a1f0f1d152595314365a3a442b2a62028f487485654c50b96
  | 3 => 0x7b22a227a3e851cb64544ef47b0a396c8a89deada0472d915113d5ac08e5b22a2008be870cb645440117b0e196c8a889e8fa1432d91510051ec2865b22a200e8d320cb64544ef56d02196c8a8802ad60432d91510055d40065b22a200ab9800cb645444f17d0f98ec8a88022f61f31d915113d1f42e63b22a200a3d85cc7645444f47d0a386c8a89de8f61470d91510045f43861b22a2008bd870c3645444f47d0a186c8a88028f61430d91510055741061b22a200aad820c364544ef56d02186c8a8802ad60430d91510045f43841b22a2008bd87083645444f47d0a106c8a88028f61420d91510054f41841b22a200a9d8308364544ef56d02106c8a8802ad60420d91510051ec2cc6322a293ab58198c64544db4790d298c8a88038718e53191510045ec3cc4322a200a3d85988645452556b03310c8a88022fe1d62191510051fc2ac4322a291a3e8518864544db56d02310c8a89b68fa19521915136d1e432a4322a200e2f6254864544dbc6ecb108c8a89d6ad219211915136f1bb2a42322a200ea7624846454401e4aa4908c8a88028f61660191510251f436c8aa2a277c3c76d9154544efa6ee838aa8a8802d960871551512de1e326e0aa2a277c3d75d936354401c3ca7b26c6a89ef0f9d464d8d5136e1eba8c9b1aa27b87f875536354409878e8aa6c6a881b1d5d521d8d510167339243b1aa200e6552487635440117d0fb22c6a88022fa1c6458d510062f298eca1aa280c3c64dd5435440717d0fb2286a88030fdd76450d5113e1e3aec8a1aa20593c8755143544094790caa286a88030f1d95450d512de1e3a8c9b02a20187c855d36054401ccaa490ec0a89de2f21b74581510045f43ec8b02a2008be87191605452196ee2322c0a88028f61253596410343e43aa4b2c8200a3f8454965904070fb0bbb2a7209ee4fa1f7550e413ee1fbb6eaa1c827cc3f761d54390401a68e23aa872089f0f1d56550e410070f29acaa1c820499c8754d439051fc3ecaa9a87208034ddd77150e410051e42a86b04820087f855c9609040b0f90ab92c12080237e0d725824101c6e41ae4b048200c6d7294b65504050ff0ea96caa08028f61250d95414753ac0cc5b2a822fa3e849cf655040147b0939ecaa09be9da0672d95414753ac0ce5b2a8200c6d721cb65504010fd0e196caa08021f61c32d954117d1f42065b2a8200a3d840cb6550401c9a64196caa09be9da0432d95410053ac0865b2a8200a7a800cb65504014f300196caa08be1fa1f31d95410043ec3e63b2a822fa3e84cc7655040147b0998ecaa08be8fa1070d954137d1ec20e1b2a820087e870c365504010fb0e186caa08be8fa1030d95410051ec2061b2a8200a6e820c365504014db04186caa09be9da0430d95410053ac0861b2a820087e8708365504010fb0e106caa08be8fa1
  | 4 => 0x8040082203006020001780c00046008080002e020040080801048000420f8000084a018020000004810010100080003800128080602c1883c0c80e008120000003800012021fe1573d85540147bc3a43b0aa800a7585043615500156b08086c2aa002b560c10d855400572c1021b0aa86fc6f655c861550011ef0eb08c2aa1be9de1561185543bd5bc22c230aa80487d85dcb60550df8eeca38ac0aa1df2dd9071581543643fc3aa9b0aa60387d85dcb6154d338eaebb0cc2a98023de1d61185533ec3fc2ae9b02a600a3d8494b6550c018dae5296caa180a1fe1d52d95430051ec24a1b2a8600a768198b6550c014eb03316caa19f68f21942d95430071631285b2a8600a76819cb6550c014eb03396caa1a028fa1072d95433ed1ec20e5b2a8600c6d721cb6550cfb47b09b8ecaa18029ba0a71d954300536c14e3b2a8680a5d831c76550c010fd0e10ecaa18021f61c21d95434051f420e1b2a867da3d841c36550c010fd0e106caa18021f61c20d95434051f42041b2a8600a3d840836550cfb4bd06106caa18029760c20d95430053b40841b2a8600a75810836550c010fd0e086caa18021f61c10d95434051f42021b2a8600a3d840436550cfb4bd06086caa18029760c10d95430053741021b2a8600a6d820436550d3187eebba2caa18021fe1572595430043ec3cc432a8600a76819886550c014eb03310caa18021fe1d62195433e51e4328432a8697a3d849806550cfb878edb2aa8a1a03171db6554d4301d8e43aa8a9a8604d1c875515350c0763d0caa2a6a180ec72195454d4302f0e432a8a9a8605e1f765515350c09a3cecaa2a6a1813471d95454d4302f0e3b2a8a9a8696b1f825515350d2d63b04aa2a6a1a3ec72055454d430058fc02a8a9a860499e84dc55350c01a3aa9b8aa6a180e2f61372d85430147bc3a43b0a8600ab5840436150c015ab06086c2a1802b960810d854300637396cb30a8600c6e721966150c018decab94c2a18031b19572985430367230ae530a8600ce572d866150c010fd0fb2ac2a18021fa1c65585434ae1fba0cab0a867bc3c741946150c011ef0eb08c2a19ef0f1d065d81430246ec1ee5b02867d87c86dd56050c010fd0fb2ac0a18031b1cb65581430043f438cab028600c6c721956050c018decbb92c0a18031b19772581430063bb2ee2b028600c7465dc56050c018eeca38ac0a18031d194715814300666192e4b1ca294ec43248563944f90f90eb22a72880e2f6137650e510061f2a6eca1ca27dc5e63dd5439440d1b90eb1a87288165721d5350e5101d2fc32a6a1ca200a3d8590b645440517f0ea16c8a88028f61640d91514061f3b4a7b22a277a3c8654b645450f87ceca96c8a889ead21921d915142e5b3b243b22a200f255248764544ef47b0bb9ec8a88ae8fa1673d91510051ec2ce
  | 5 => 0x15c51a8d4801c890168044494cd99a2a08ac5710c5369b8b580e02c51d500543923c8b69562ca000991f30a00000000000056d3fa6d49aa64f0a2050e000bb800108355180e61946c9350da184000180001128dc000000564f0d31081e01ac5784c24c000d3a64000504dc9891d27712f15142a908058b82501d85d86100009d208280001888798a138795221794e2000c695c0ce2184ca6f04635c6c1cd20c7c0000005484690f0004a4000d524f18c9dc3800000000000000000000000001521e4a9800000a08d18c15009ac50a9744816c4ba0e0000007d2094022ac4a8f70009140000d5260014415d2c87400000000000121a020263bc1e9da26e9ec922683a6a504f28f14899491a3a1680012e2843e4008bb2951582208ea8a1e6000838003f009924891134000729ed144048000000a6a88000000fa96c662292b2001558f104aa783704405a375409610c69608d9ce00e22c7500c0388291ca5a0003ac0020d0907b8328f43660009c8001b6314a40004507b0e3a60000524ca28316c1b10782e43231c2c800000534b496a554400c81d745e0000001b3be0000010e00039c568001be154b7a3e396000d4a1100047cdd1f1000044c713a19a0000008000040cc1a185168fd2526c3a43491381417e538151bb1b86c5059cf074578ff9e65205140c2a62627dc7607e38c750e526338a0d1431044ce8f00500447a868889ef1ea38c000b30cca30a21f642845c472354660bc001190da0002f1e00000012c87b3085e91a1e9358000768ff3bc2a80008722c5602f9f40b4670591824ea6554f83b13a17106199436434a100930a97cec1dd3b6460040bc1929752a1e43d60000004e140984dfa38356888538002fc5695380045c88407851000001508000341e8891290823f0982a93269f862000298700ec8c34548b47b00611400096001000000001270e694c0020625667c000b733aa38dc00037c000000f8270710a0000092364af9801962a00000032e078000003849c8349982c6954e08be2164b51300002e00010000000000000e407e26103a124a29f0db0102123ec002a52ea55c00136000690b0000000000cb0c03fc298b921d316000f107708a859042ac27a0000009002e060460180c13814000120001a0201e068080a8140302a010020500002830000120000400810060040081600002000020a00c038300080a0080200026000000105200800008000200608038000040181e0700007820040020c8621080001000040080200a0007a0f0200080e000020001c06000008060083e008280400002044028000480a0000800808010040100003802058000204e0380008002018040184800026010061b85e0480000000010160b0000100a0a002080040000202840018240082009800078160b0280e8080280c0001028800150000
  | 6 => 0x80c74170174109259674a0208e199e1a09a452a325128d90f89222807cba24c214aa14d07c190a609502450a484d79024ac1fc6780000027d4b000426758d4279340148388d34ec24cc91543ea3780002c0007313d0b00000cc5a8000ba620000003900014905800000000223220000002171722049fa574208150e08f0326895183e02a7f4be04344a9f48986437a11ca18962f079c8e1e820a380d69b00800743a29d04213cea9b516291948a74368554be8750000f00180036e91c5e98f1ac9cc7e8850002311d8001fc000000d44c413400000062339188e230c53c9a9fb0960001a98c4e0998fc8390de4bcd09220001189f14600a52cb117f3a2128809813c61587c9ea0005b04a2783224cd1616e0c03849a06a4908010218706e0d8d70323f45292707811a5988f1a50d07f01c09b5380a4de11525c3b8688832a45ecb893b2e6
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x24a16012000814386000a8299cb84290698308b2201e004001bc8a36447e6154dc55350c014c9900c97258e514d7099d9524876454401a893260032d915136d89a595248464544f703c981d95450d51006924c9800cb655040103f985d0745963136d0d245741d1658c40181d7460c74596310058965272485658c4014659790921596310063260d701c1628c535c247454921595310250725d65551434c4015159315071591500053264032dcb63540018a4845c96118550006491d182185515400151593150715954047d852456554d43500db836861d761505404d7091d15248565c4135c24745492159510
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xa052857460c7459631
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x4805b22857460c7459631
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x5
  | 5 => 0x6
  | 6 => 0x2
  | 7 => 0x94b
  | 8 => 0x94c
  | 9 => 0x94d
  | 10 => 0x94e
  | 11 => 0x138b
  | 12 => 0x138c
  | 13 => 0x138d
  | 14 => 0x138e
  | 15 => 0x9cb
  | 16 => 0x9cd
  | 17 => 0x9ce
  | 18 => 0xa0b
  | 19 => 0xa0c
  | 20 => 0xa0e
  | 21 => 0xa4b
  | 22 => 0xa4c
  | 23 => 0xa4d
  | 24 => 0xb49
  | 25 => 0xb4b
  | 26 => 0xb4d
  | 27 => 0xb4e
  | 28 => 0x1449
  | 29 => 0x144b
  | 30 => 0x144d
  | 31 => 0x144e
  | 32 => 0xb89
  | 33 => 0xb8b
  | 34 => 0xb8c
  | 35 => 0xb8e
  | 36 => 0x1489
  | 37 => 0x148b
  | 38 => 0x148c
  | 39 => 0x148e
  | 40 => 0xbc9
  | 41 => 0xbcb
  | 42 => 0xbcc
  | 43 => 0xbcd
  | 44 => 0x14c9
  | 45 => 0x14cb
  | 46 => 0x14cc
  | 47 => 0x14cd
  | 48 => 0xe89
  | 49 => 0xe8b
  | 50 => 0xe8e
  | 51 => 0xec9
  | 52 => 0xecb
  | 53 => 0xecd
  | 54 => 0x1049
  | 55 => 0x104b
  | 56 => 0x104c
  | 57 => 0xa0953
  | 58 => 0xa0956
  | 59 => 0xb4953
  | 60 => 0x94b53
  | 61 => 0x144953
  | 62 => 0x95453
  | 63 => 0x249
  | 64 => 0x16c9
  | 65 => 0x1849
  | 66 => 0x19c9
  | 67 => 0xb5393
  | 68 => 0x138b53
  | 69 => 0x4c
  | 70 => 0xe8a
  | 71 => 0xeca
  | 72 => 0xb49d3
  | 73 => 0x9cb53
  | 74 => 0x124c
  | 75 => 0x18c9
  | 76 => 0x1789
  | 77 => 0x180c
  | 78 => 0x130c
  | 79 => 0x1a49
  | 80 => 0x17c9
  | 81 => 0x198c
  | 82 => 0x134c
  | 83 => 0xa0b93
  | 84 => 0x124d
  | 85 => 0xe8a13
  | 86 => 0xa0e93
  | 87 => 0x168d
  | 88 => 0x12cd
  | 89 => 0x1a89
  | 90 => 0x1949
  | 91 => 0x198d
  | 92 => 0x134d
  | 93 => 0xbca53
  | 94 => 0xa4bd3
  | 95 => 0x124e
  | 96 => 0xeca53
  | 97 => 0xa4ed3
  | 98 => 0x168e
  | 99 => 0x12ce
  | 100 => 0x180e
  | 101 => 0x130e
  | 102 => 0xe8b53
  | 103 => 0x184c
  | 104 => 0x19cc
  | 105 => 0xb0c
  | 106 => 0x16cd
  | 107 => 0x18ca
  | 108 => 0x2cd
  | 109 => 0x74a
  | 110 => 0x19cd
  | 111 => 0x194a
  | 112 => 0xe9493
  | 113 => 0x16ce
  | 114 => 0x1a4a
  | 115 => 0x104bd3
  | 116 => 0xbd053
  | 117 => 0x28e
  | 118 => 0x184e
  | 119 => 0x1a8a
  | 120 => 0xed4d3
  | 121 => 0xece93
  | 122 => 0xe9053
  | 123 => 0x5cd
  | 124 => 0x74c
  | 125 => 0x194c
  | 126 => 0x1a8c
  | 127 => 0x1a4d
  | 128 => 0x17cd
  | 129 => 0xed053
  | 130 => 0x18ce
  | 131 => 0x178e
  | 132 => 0xb0954
  | 133 => 0xb0d
  | 134 => 0x140d
  | 135 => 0xd4d
  | 136 => 0x94a16
  | 137 => 0x1a9951
  | 138 => 0xb0bd4
  | 139 => 0x2d255
  | 140 => 0x2cb15
  | 141 => 0x2cb55
  | 142 => 0x14cb15
  | 143 => 0xece92
  | 144 => 0x29256
  | 145 => 0x1a0d
  | 146 => 0x28b16
  | 147 => 0x28b56
  | 148 => 0xb14d4
  | 149 => 0x75494
  | 150 => 0xece905b
  | 151 => 0x74a14
  | 152 => 0x1a9954
  | 153 => 0x19cbd4
  | 154 => 0xd4b15
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 1330
  | 6 => 2452
  | 5 => 685
  | 4 => 24
  | 3 => 1
  | 2 => 1
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (54083+((h/443+packedAt gbK7 (49210+(h % 443)*11) 11) % 1597)*12) 12
  | 6 => packedAt gbK6 (127500+((h/817+packedAt gbK6 (117696+(h % 817)*12) 12) % 2943)*13) 13
  | 5 => packedAt gbK5 (42695+((h/228+packedAt gbK5 (40415+(h % 228)*10) 10) % 823)*11) 11
  | 4 => packedAt gbK4 (1720+((h/8+packedAt gbK4 (1680+(h % 8)*5) 5) % 29)*6) 6
  | 3 => packedAt gbK3 (82+((h/1+packedAt gbK3 (81+(h % 1)*1) 1) % 2)*1) 1
  | 2 => packedAt gbK2 (93+((h/1+packedAt gbK2 (92+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3fffc3870fe1f8061c07fffffc81c0fe19c0ff
  | 1 => 0xc3c3fc07f0fe3fffe00703c0fd462726667c93
  | 2 => 0x3fc3ff800ffc007fff803ff02783839878f1c
  | 3 => 0xfc003fffff000007fffffc0003803fc1f80fe0
  | 4 => 0x3ffffffffff80000000003ffc001fff000
  | 5 => 0xffffc000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x484408201404840040150546000c04a08c025
  | 1 => 0x41628c011032123720320a8298422324221c92
  | 2 => 0x26a150800b480934950032a08582830870518
  | 3 => 0xa8002a55aa00012492a4a80013801581700ac0
  | 4 => 0x200033e6ccc925c000c0300c23ad4001dde000
  | 5 => 0x33b30040881006010300c230c3f7befe000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefea8feecfaa8fefefea8feecfaa8fefefea8feecfaa8fefefea8feecfaa8fefefea8feecfaa8fefefea8feecfaa8fefefea8feecfaa8fefefea8feecfaa8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36362
namespace PEqualNP.Outside.L_meta_36362
open PEqualNP.Outside.L_meta_36362.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 64 := (concat bs0_4_0 bs0_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 40 := (concat bs0_5_0 bs0_5_32)
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 1 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 11 := block_range (n:=11) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 11 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 9 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
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
theorem bs2_4_64 : Interval s2Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_128 : Interval s2Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_160 : Interval s2Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_224 : Interval s2Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_256 : Interval s2Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_320 : Interval s2Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_352 : Interval s2Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_416 : Interval s2Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_448 : Interval s2Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_512 : Interval s2Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 539 := (concat (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96)) (concat (concat bs2_4_128 bs2_4_160) (concat bs2_4_192 bs2_4_224))) (concat (concat (concat bs2_4_256 bs2_4_288) (concat bs2_4_320 bs2_4_352)) (concat (concat bs2_4_384 bs2_4_416) (concat bs2_4_448 (concat bs2_4_480 bs2_4_512)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_64 : Interval s2Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_128 : Interval s2Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_160 : Interval s2Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_224 : Interval s2Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_256 : Interval s2Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_320 : Interval s2Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_352 : Interval s2Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_416 : Interval s2Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_448 : Interval s2Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_512 : Interval s2Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_544 : Interval s2Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_608 : Interval s2Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_640 : Interval s2Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 664 := (concat (concat (concat (concat bs2_5_0 bs2_5_32) (concat bs2_5_64 (concat bs2_5_96 bs2_5_128))) (concat (concat bs2_5_160 bs2_5_192) (concat bs2_5_224 (concat bs2_5_256 bs2_5_288)))) (concat (concat (concat bs2_5_320 bs2_5_352) (concat bs2_5_384 (concat bs2_5_416 bs2_5_448))) (concat (concat bs2_5_480 (concat bs2_5_512 bs2_5_544)) (concat bs2_5_576 (concat bs2_5_608 bs2_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 40 := (concat bs2_6_0 bs2_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_7_0 : Interval s2Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_7 : Interval s2Atlas 7 0 1 := bs2_7_0
theorem alls2 : ∀ k ≤ 7, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
  · exact alls2_7 i (by omega) hi
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
theorem bs4_2_0 : Interval s4Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 10 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 60 := (concat bs4_3_0 bs4_3_32)
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
theorem bs4_4_96 : Interval s4Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_128 : Interval s4Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_160 : Interval s4Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 165 := (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 50 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 91 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 44 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_2_0 : Interval gbAtlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 1 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 1 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 24 := bgb_4_0
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
theorem bgb_5_672 : Interval gbAtlas 5 672 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 685 := (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 (concat bgb_5_448 bgb_5_480))) (concat (concat bgb_5_512 (concat bgb_5_544 bgb_5_576)) (concat bgb_5_608 (concat bgb_5_640 bgb_5_672)))))
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
theorem bgb_6_2432 : Interval gbAtlas 6 2432 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2452 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 (concat bgb_6_384 bgb_6_416))) (concat (concat bgb_6_448 bgb_6_480) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))))) (concat (concat (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)))) (concat (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024))) (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)))))) (concat (concat (concat (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)) (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472)))) (concat (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632))) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792))))) (concat (concat (concat (concat bgb_6_1824 bgb_6_1856) (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952))) (concat (concat bgb_6_1984 bgb_6_2016) (concat bgb_6_2048 (concat bgb_6_2080 bgb_6_2112)))) (concat (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272))) (concat (concat bgb_6_2304 bgb_6_2336) (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)))))))
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
theorem bgb_7_1312 : Interval gbAtlas 7 1312 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1330 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)) (concat bgb_7_576 (concat bgb_7_608 bgb_7_640))))) (concat (concat (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800))) (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)))) (concat (concat (concat bgb_7_992 bgb_7_1024) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120))) (concat (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216)) (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 7 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefea8feecfaa8fefefea8feecfaa8fefefea8feecfaa8fefefea8feecfaa8fefefea8feecfaa8fefefea8feecfaa8fefefea8feecfaa8fefefea8feecfaa8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124200 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36362.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,5]⟩,⟨.or,[4,6]⟩,⟨.and,[4,5]⟩,⟨.or,[3,8]⟩,⟨.or,[1,2]⟩,⟨.or,[0,2]⟩,⟨.and,[1,7]⟩,⟨.and,[0,10]⟩,⟨.or,[9,13]⟩,⟨.and,[11,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124200 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124200 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36362

open PEqualNP.Outside.L_meta_36362 in
theorem PEqualNP.Outside.L_meta_36362 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124200 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124200 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
