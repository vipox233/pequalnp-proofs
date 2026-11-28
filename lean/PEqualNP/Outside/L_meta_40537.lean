import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_40537.Model
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


end PEqualNP.Outside.L_meta_40537.Model

namespace PEqualNP.Outside.L_meta_40537
open PEqualNP.Outside.L_meta_40537.Model
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

def SBf (j : Nat) : Nat := [7, 6, 7, 6, 6, 8].getD j 0

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

end PEqualNP.Outside.L_meta_40537

namespace PEqualNP.Outside.L_meta_40537
open PEqualNP.Outside.L_meta_40537.Model
def s0K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x14f8060020004400000800900c2200300009380000001fe10ff42fd41fd40fd30fe42ff32bf41fe20dc32bc40fe32ff41fe40de32fc40fe41fe31fc41fe21ff20fe30fd42fc32be40bc42fc21ff30fc42fd43fd31fd20fd10bf43ff31fc10fd21fc43ff43bd41fd32fc20fc30bd43ff10fe43ff21be42fc31ff40
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1030000000300000200002d0501848d00000000000181808181028000830300080000060080000200010003808000079d8a800080010100028000808f858100ba008001020517838081030000030015840084821b001d980000071cb00080014f94840ae29a855c534827aa2216750c319faa2413e540cb3a87195b94a319e2a2413c544427aa918db14943b7290213d5390abea6884fd5020aea98813e509027aa898e7550329e2a6435e538827ca1a0cf953319eaa4433e548833884194f14941bba8a413e544c67aa998cf552439e2a4216c524c27ea990cfd51219e2a4653f548427aa8185b149109eaa6659f5350e7ca1a1cf141439ea9e83cc32486e8a290678ca40ce190813f5150e7ea6a0cf940429f2a063cc32c8678a4a1e750d309e2a2653f548c278a8985754f42af29e839f430ca7ca5204f95010cea1865cf420cb6ea2a0cf55310e6190419e53102bca419678cb419f296833e54c827aa6215714d109f2808178504867aa810dbd49309e282835e53d0b3c64a0d714d21d621065cc328831884194754f419e2a0413d5490774a0204f5532096292873e54cca78a890d754c10cea98813e548c67aa3204fd51309ea88815f534867ca820ddd45309faa2213d5190a7ca5a1e7d5232aea9c419e428cb3865204f950219f2a6613d531023aa6205794e21d621665ac5250e7aa818ded4121afa9a419e53d067ca910e7908329f284853d51d0f3a8798670cb41af29465af5250edaa518d7d4d42cea1c639c428ca7ca4214f54e40b6a90213c548c27aa9105bd4943aea9c433f544ca7ca821dd145309faa4659c3250738a9194f55032af298813d540433ca8194f95310e6210653d54cc39ca419678c8409f2a0615e53042dea4885754f41cea9e839f438cb5ca4214f94a42
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x40a005410000000440020800c010102108408800000e04010016400301200201d011c318953d068c6250d30a3189438c68e6010832c3150320820c6254c40a398b548ca1d6395310c3d8c5250f0c520c941c550c514c30f6254f4187189531030d4394a318758e5090a1d650c8408b189531021f6354642a5584548cb0e520ca40c3189531028d61108328758e540868e6290832a3988548cb0f53149438e181544c62d6510832a3d94420cb4832141218b18953d070c540c9218758c540824c6254f41c3950328828c6254f418758c54c861d63141418b189544c70c540cb21a3189430c61f658c8408758e54c823561152328318953d070f6254c4093189531028c6250f30a3594420ca2e62d523087195434c21d6315210a3189531021f658cb418759432d063561150208758e544c70d43149308718953d061f6354640
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x814400228338ec629287215c7651083281aec2a064105047250c514c282b88a819041031c96314141818e4b18a90840c7258e54c4206392c72a043039cb6354640
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
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
  | 5 => 2*((h/30+packedAt s0K5 (800+(h % 30)*6) 6) % 50)
  | 4 => 2*((h/97+packedAt s0K4 (4455+(h % 97)*8) 8) % 165)
  | 3 => 2*((h/48+packedAt s0K3 (2280+(h % 48)*6) 6) % 60)
  | 2 => 2*((h/10+packedAt s0K2 (490+(h % 10)*4) 4) % 10)
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffff81fffffff81ffffffff03ffffe3ff1ff
  | 2 => 0xf03ffffe07ffffffe07fe07fffc1ffffce3e3f
  | 3 => 0xffc07ffff80fe07fff83ff81fffe0f01f3cfcc
  | 4 => 0x7ffffff0007ffffc0001fffff001fc0ff0
  | 5 => 0xffff80000000007ffffffffe00000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x1105108c412248100594a8a25012915414d0d5
  | 2 => 0x248a29103244942960294454a6412aa8ca262a
  | 3 => 0x42934a2490e904caaa8275113aa40c0d634b4c
  | 4 => 0xb2c74492481d974d34c1861cd39c031bc0db0
  | 5 => 0x8c307871c70e1e7f1c739e780e3188c1ffb000
  | _ => 0
def s0Atlas : Atlas := ⟨6,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0fcc0ccc0fcc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_40537
namespace PEqualNP.Outside.L_meta_40537
open PEqualNP.Outside.L_meta_40537.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x70200010000100f431d431f731dc31be40bc40bf42bd42de31
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x200000042a00cb2a06395540c72e8418cb54840ab28c6395420c7286220650c640
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x12a158a540c615650c44085597420c705520c440
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 9
  | 3 => 8
  | 2 => 4
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
  | 5 => 2*((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/17+packedAt s1K4 (144+(h % 17)*4) 4) % 9)
  | 3 => 2*((h/16+packedAt s1K3 (216+(h % 16)*3) 3) % 8)
  | 2 => 2*((h/8+packedAt s1K2 (152+(h % 8)*2) 2) % 4)
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffe07fffffc0fffffffffe07fffe3ff1ff
  | 2 => 0x80fc0fff81ffc1ff0f83c1f03ff87f81d2ce7c
  | 3 => 0xff000ffffe0ffffff003fe003fff87ffe30f8f
  | 4 => 0xffffff001fffffc00003ffff801fc0ff0
  | 5 => 0xfffff000000001ffffffffffc0000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8a10002304008000118442118a0088940450b5
  | 2 => 0x262996451ca512cb06a1d1a296c8550cd2c65c
  | 3 => 0x144aaa88286a31556042b48425550669630b0a
  | 4 => 0x58b34d125143a5a6bb68210939a66031bc0de0
  | 5 => 0x60c38e1c618c39f8cc7339ce01c44441fba000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaaaaafaa0aa00faaaaaaafaa0aa00faaaaaaafaa0aa00faaaaaaafaa0aa00faaaaaaafaa0aa00faaaaaaafaa0aa00faaaaaaafaa0aa00faaaaaaafaa0aa00, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_40537
namespace PEqualNP.Outside.L_meta_40537
open PEqualNP.Outside.L_meta_40537.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x850c108000000110500038f0021420021563c0380ff40fe31fe20fe41dd43de43fc42fc10ff32fe21ff41fd21ff21ff20fd41de31fd10fe10fc21dc31fc43ff30ff31fc41fd31fd40fe30fd43fc32fd32fc30fe32fe40fd42ff43fc31fc20fe43fd20fc40fe42ff10ff42fd30
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x5140c00002822400b182c286004820038101834008582040c0801e0eb195005580020418a008ab8a690d7d4d41ea18e213e54082bca7084f550209f2a0655d5310ab8a6887514543ba28a655d538433a86a15754f42af28c875e53102baa6105d14520b6292215f548c6bca7a0f510431b6a96833d54c86baa7a057d4d21cf2a0635e53d0abaa790ddd4532cfaa287d4310867ea8905d54742af28c635c5150f3a86205dd4520ceaa06375518c2baa6206750f42b7290815e53106baa918f50c5109f2a6615e5310eeca3185794c429faa2215f53482bea818f594431ae29a835e510c63aa818cf95321af29e436d52103aea2a1d794c20bb288416f52442baa818f50c721cea1c817651d0b3a87a0d794f40bba8a873d54cc3ae8218d754c419e2a2413e540c6baa7a0dd94440ba28a877551082eaa2205714d20cea1a835f53442baa921cf55032aa28a873d540c678a8885b94b41
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x700100000f000e23382c080b3702946150f41b198b410c695640c721c5185540c695640c710c595031c87154354440c350d521021d6414d21a518543902946150c40951855310a946150f42c515031442546154f4087596540c695640c421a5590314425565104318759253843154354742d1148314431554d0431c350d52d06946150d42
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x20180302aa4c5a0863411c54354b4182aec2a062884157695031c868238a86a908181590520c510
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
  | 6 => 2*((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 1)
  | 5 => 2*((h/28+packedAt s2K5 (704+(h % 28)*6) 6) % 44)
  | 4 => 2*((h/44+packedAt s2K4 (2430+(h % 44)*7) 7) % 90)
  | 3 => 2*((h/22+packedAt s2K3 (950+(h % 22)*5) 5) % 25)
  | 2 => 2*((h/9+packedAt s2K2 (294+(h % 9)*3) 3) % 6)
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1fffffe07fffff03ffff07ffff07fffcf1f1ff
  | 1 => 0xe03f07ff81ffc3fc3e0ff8781ff87f034ece7c
  | 3 => 0xffc007fffe0fffffc00fff801fff87ff8f0f8f
  | 4 => 0x7fffff003fffff000001ffff803f00ff0
  | 5 => 0xfffff800000003ffffffffffe0000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x428400230400800046110088c50089281050b5
  | 1 => 0xc98a4a451ca5052c1a8748514b48521946c65c
  | 3 => 0x5129488286a2255810a9502129504d28b0b0a
  | 4 => 0x962ce7125143ab9aeda0c4449ce66063f00de0
  | 5 => 0x1830c61c618c33e331cce66700c44083eda000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeaaeeaaee88aa00eeaaeeaaee88aa00eeaaeeaaee88aa00eeaaeeaaee88aa00eeaaeeaaee88aa00eeaaeeaaee88aa00eeaaeeaaee88aa00eeaaeeaaee88aa00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_40537
namespace PEqualNP.Outside.L_meta_40537
open PEqualNP.Outside.L_meta_40537.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xc0000de43bc40be40dc30de30dd43
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x33080185614143
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
  | 5 => 2*((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/9+packedAt s3K4 (96+(h % 9)*3) 3) % 6)
  | 3 => 2*((h/1+packedAt s3K3 (54+(h % 1)*1) 1) % 2)
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7fffff01fffe0c1ffffc1ffffe0ffe00f3f3fc
  | 1 => 0x81f83ffe0fffffe0f83fe1e03ff0ffff4ccc7f
  | 2 => 0xfe003ffff07fffff003ffe003fff0fff8f0f8f
  | 4 => 0x3fffff800fffffc000003ffff003f00ff0
  | 5 => 0xffffc00000000fffffffffffc0000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xc30011c21041003184c02238e0112181151bc
  | 1 => 0x24425224642884a06a1521449290a4a944c455
  | 2 => 0x1094a4488351094d042a5409252a09528b0a8a
  | 4 => 0x596738914a1dae76b683111239ccc063f00f60
  | 5 => 0x618630e18c61cf98c733999c01888183eea000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0eaeaeaeae8e8c0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_40537
namespace PEqualNP.Outside.L_meta_40537
open PEqualNP.Outside.L_meta_40537.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xec21ee21
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
  | 5 => 2*((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 1)
  | 4 => 2*((h/7+packedAt s4K4 (32+(h % 7)*1) 1) % 2)
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
end PEqualNP.Outside.L_meta_40537
namespace PEqualNP.Outside.L_meta_40537
open PEqualNP.Outside.L_meta_40537.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x3031000400404c000b1ce09e0040801c0543200fc42fe10fc41fc20fd31fd32ff30ff21ff10fc40fc32ff31fe20fc43fc31fc21fe30ff42fd30fe31fc30fd43fe43ff43fe42ff32fd40fe21fd42ff40ff20ff41fd21fe40fe32fe41fc10fd10fd41fd20
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x281ed32482fca790dfd4143ec98061fb10442fea9985f55243b7290617d5110afaa6085dd4542bf286877a50086fca1a15b14941bea80877e52906f8a0a1fe88210bf280657c54082faa890df14810be298213f544c2fea0a0df95132bf28021f940103bc64997b8c832fca80437f53086f8a2997dc8521beaa6417f54042faa5105fd4c10be29c217e50903de41105f55321bea8c81ef4250af8a9885f54032dfa0481be405027ca810df95120fb082217f548cafca9985f94b10bea8043f721886fca2085f54f42bfa9a837e5010afea0a15f54841ae29a81fb40cc3f080186f50b41bf29821fb308c2faa8985fd5132ef992637d538cbde8510fd50441bf298437d51cc37c86a1df15120beaa265ed20083f660985f94e40aea98437d544c6fca220efd0e43dea12837c514c2fca8105fd4d40be29a837e53c42f8a6885fd5310bfa9a857c52842f8a098df54242bf29861f741906f8a9906fd0941bea90637e53107be87187d48421de2a2617f53486fea9085fd5131bea8c417e510cbf6a0a1fdd4542ee21c617e544c6fca018dfd4941f699065bf42d06fea5885fd5220bf2a261f5310c6faa7205f54331bf29c837e5210bee20085f54b43bf294217c5050afaa3a05f54830f7a10437c53082fea9905f95032bf2a461ee32c82faa8105f94f42bf28e877e54882faa7887e48210be2a2653f54487ee6318df94443bea84837d53c82faa8085f54231bf280817e518c6fca9085794c21bea98813e540c2dea4a0f78c130bea98837e52442fea8905f94a32bf29481dd320caf8a9085fd4943bf28863df430c2faa3a17ed0240de210837f540c7f621085f14f20bfa90217d50d0afea9185f94d10ee218617e53882fca6207e88020bea9e81e521086fca1105fd4532bfa9e437f53082bea6a05f94e42bfa92817c524c2faa0216f55030deaa0437e53486faa920df14d20be292217c548c2daa4185f54630be2a6657e5090b7e8621df15330bf298857e5210efaa1a1df14e21fd280437e54042fca020df15130bf28c617c54882fca4205f94f20fba0a837f53c42fea2a05f54632be2a243ed21087d88410df94832ee98863dd300c2fea2a16f90a41f7a92837f52442fca7a0fb10a21bea9c41f840cc2faa7a0df54e31bea94217c54cc7ba6498f7d0d43f710a437e5310efea7906f15121be282657d51083ba8621dd94430beaa0617d54c42f8a0a0fd8c510bea9c61ef21886fca918fb94830bfa9c437d53886fca3197ec8220be2926375510c3be6598df94b30bea94617d54087da65905f94e21bfaa0437e51082fca010df95041fd200817d528c6fca5a1fe48020bf2a0437d51103e88210df94b31bea9661be54086fca4105f94341bfa9a21de314c7ee21085f95121bea94877f54082fca3995f15110beaa2417f544437c8420ded4143
  | 1 => 0x19700400690070001b0044c00c000a40e0081502c030ac501544000c0200c000301504c0c018180103c0d8060280100c3e1a4170c00800ca301023084e402400001270200202c0304c56024000088401c01034340dc140043e37025204e010c0c058110a409004010040b0000800c0b1584d020000b4010000203400018040300000400000140440055c04054030242f0001729042000230701a01c1201c010040001055004300385032000284142281c008000fc050384e5b40300c051e80604c770001c0102e03c5e015b80240207c000c8090d81f000000d40500007002faa5a05f94331df218817c53486faa4085f94241bea9c837d52906fca210df54d21df21c817e534837e86a06fd0f40bfaa061ee20483baa610fe44010bc28287745150bde4210fd4c510bfaa6437f54ccbde40105f94440bfaa443dc53503ee6298df15321bf28c857e508cbda84215f14540bea86657f524c2faa598df94e10fa20e437d51c82faa6105f15131bf2a6637e528c2fca4085f15010bf29c87ef4290afaa5885f54243bf288857e51906fca2185f95042bea84437d51ccafea2985f95043bea8861df328cb7c82a0dfd4121bea84657d510cafaa9995f55220be2a065bf4210afea498df94b40bfa9a417e508437a84215f55232bca8043f9300c3e8a2a15f94332beaa065f6310c7ee8210dfd5231be292877e520c7be61185f94621beaa221fa204437a8621df54610bea8c877e54c83bca610df54c42f7994657f504c6fca818dfd5032bea8c857e500c2faa9205f54041bea9a21df53502fca190ef95030bea9c217d5210f7e8320df14e20be28a857d51d0efca9887ec8120bea86437e51d0afaa910df14c21dea1a81bc43102fca6105f55031fd18061bf544c2f8a2a1dfd4132be296217c53c42f8a090ef50441be29e437d53482fca3107bcc932bea92217e54886f8a8185fd4543bf298637d52903ba6598df94a43dfa08837e50082f8a810df94221bfa94217e540c2fca420df54a21beaa6613c544c2fea2905f54e42ef98061ed520c2fca118cf15121fa880217f54486f8a6a17d8c710dea1e817d53c86faa9185f15221bf29865fa10042fca3205f94230bf290617d52d07dc64906fd0a42bf290437e5290bd8a4a0df94b41be292837d5110f7ea890df95040efa1c877e53d027aa8187d54430bea9081bc429077887205f55242bf28e417c548cafca518fe14143beaa663de4310ef8a29077cc631fb288617e548cbec8220ef90942fda00617f544c27aa810df14d40bfa9c217c548c6faa1a0fed0140bf28c877d548c6fca021df95332bfaa663f920443ee8390df54031bf2a221df310c7dc84215f94730bf2a6437c540c7ea63885fd4e20dfa0081bd40102faa610df94243bf28e81df320cafaa9087d88421be29
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xe40502db654c030f4945300c25e6314c2197594430c23e64951309758c540867a60150329d584538827960d4c219e980540c798644c0309758f54c82ac6250441d694d500867960d52329ed81544c23e6414c20c7952530866e6214e10c718d540c25d6315010cd552510c25d63d50219e59610042d86050c439ed81544ca3e64d4c219e594400c27a60d5021b9189411067b6054d21d9549510c26f65508428f590538427461551209b588540c63d64d4f208fd9541106786054d21ad1854210a6d62d50309d185544ca3e64d4f109b189544c67a60150218f59053882746154d20ae1814310e7b6548020ce181540c33654544308f99254486776154d208fd954210a77654c4319dd85544ca3e64d4f208fd91534432d5494830cb951520c2776155120cb15221486b461509419758c52c423d65950309b988530827a60d52329758c520432c52d0941ae18143502d9638c03097d95310c6e461508429b98b548433654944309798c52c423d6590c40d9d085150a7a60d4c218fd954310e5f635513097d95320ca6e62d53319ed95401027661d5030cb55342086e765484219dd95411065e63d53108f59052042766114e20c714f435023f6454d209b58b548423f6550040d9d9521086b8644c0308f992534867960d50219e983548c63c6454d21f2949300c27860551319b988540425c63551209bd89534425c63551108fd9153486d96010c308f990530427960150319d5845308399544c0309d984540cb655294430d6d95300c31e5454c219e583548c66f6255131cb14a415079843100309bd95200826f6255110b9588410865e6315021d654e500869c644c030b6191300c25f63551108f99053843e121940218fd91524426d6214e109dd85544865c63549109d984540c23e65151309d195314427561d53328f191524426d6215010ce552500865f63551209e9805308698644c0308f59353c425e6315010ce952500866d62d5331ad191210865f6354910ab191210863e64d4a1097d954310e7b60551319d984540839b644c030b958a210879b43d003097d95300c26e62150308f99052042e46448421c7152304c27b654c0309e580540867561150309d984530835b43141439798f540863d6414c218f99052c433a54540219798c520435853d01409b195324829c63500409d587548826e6214c10cd9085150a7561d5030a919121087a764484219758c540832d5454830b618d401036452d0541cb189540863e65d0941ce90c5050e7a6014810f194d21087665254430e9951210863c6454d20cd551510c23d6414c208f990540c23e6414c219b18954443e12154021f4545300c23e6414e20e9551210873454c85219b98b540c31d54d0c30f2549300c23d6414b10ad18542d07a742d0421f154d21086756115032ce551500866f6255121
  | 1 => 0x78105e01040149e071a40800170543a061401418040b000420500010a0000483c0800100002828010800000088482408040ac02010c000281202000de04030b8020003000080b0e000220804034740b570180a002980000040280846540113c360006804041f0e008000b05000000a1f85c02000203000040607a7661d5332ce153304c23d6590841d694e50087346155021c7551530865e63150209758f54c42d963100308f593530872e5494830ae18143d032c52509419bd95210867960150329b594420875953540219e580530863d64d4a109b18953442da644c0308f191534423d6414c109ed95100439a544c030cd55341086e664484219dd95210863e65d0d409e195204431c5350d409798f54c823e65151218f592534871d5494c219bd95320ca756115020ce553400c3a442104219d59441086e561108219d984530423e64150219dd95100425d6594c219b988540c76652944308f59654087a464484219b588540c26d6214c109e181544ca7661d5220c714
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x20785c00040000c0a0000510348324a298061c4551514c030e82a690aa010f4152545300c2523b4a890843299d26448421948ecaa24210e846494d2108742322a690843681d12194021d10c8a92601849876951300c30c318c0aa061261d9544c030e42a890aa010e8864949300c348322a298061c2551524c030934e932260186246218554086d03a242a8043c15515348421
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x400000600000a1086551514c030e0064549514c030d007454d2154021a04865515348421920875512154021a0886551524c030
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 538
  | 4 => 269
  | 3 => 22
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
  | 7 => 2*((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 1)
  | 6 => 2*((h/27+packedAt s5K6 (640+(h % 27)*6) 6) % 40)
  | 5 => 2*((h/179+packedAt s5K5 (14526+(h % 179)*10) 10) % 538)
  | 4 => 2*((h/110+packedAt s5K4 (10222+(h % 110)*9) 9) % 269)
  | 3 => 2*((h/21+packedAt s5K3 (1078+(h % 21)*5) 5) % 22)
  | 2 => 2*((h/23+packedAt s5K2 (360+(h % 23)*3) 3) % 6)
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf80fffc0fffff807c7c7f8ffc7fff80033f3fc
  | 1 => 0x7ff07fff03f1fff807f8ff1ff8e03ff1cc7ccf
  | 2 => 0x7fff83fffc01fffff800ffe3ff003ffe0f8f0f
  | 3 => 0x800003fffffe00ffffff0003ffffc00ff00ff0
  | 4 => 0xfffffc00000000fffffffffc0000000ffff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa61084628a0410141413824c129886011b15c
  | 1 => 0x10a5108a1902902802c84909484292a0c454c5
  | 2 => 0x2142291440652052c8009242920525460a8b0a
  | 3 => 0x58a52209240329c949200032496018b600ea0
  | 4 => 0x460c6038e389c4e72724e4900018060dbf6000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfee8eac0fee8eac0fee8eac0fee8eac0fee8eac0fee8eac0fee8eac0fee8eac0fee8eac0fee8eac0fee8eac0fee8eac0fee8eac0fee8eac0fee8eac0fee8eac0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_40537
namespace PEqualNP.Outside.L_meta_40537
open PEqualNP.Outside.L_meta_40537.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x2001400450403800c400a3a30002aa28214004000008904001ffd5001fd3100ff14005fe5200ff04001fd21007f88405ff21007f4c007ff53017fc8003fc40017f90801fe41017f8c805fc4200ff94007fe53017f08401fe4301ff54805fc52007f10407fd5100ff08001ff4101ff14c03fe2000ff90003fc30007fcc407ff51007f50801fd41007fcc801fc43007f44007fd50007fc4007fc5400ff84007fe51007f8c401fd40007fd0c01fd2001ffd4807fc5101ffd4001fd43007fd0007fd54007fd0801fc3101ff95005fc32007f4c801ff3001ff54c03fe30
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xc6208ff10b40025f8c818813fc62c4009ffb1c8204ffc8641027fac420823fd42d000fff21a860eff087301effea0a1823fc62d0c11ff20e8000ff98532017fe42a100bfc21cc80dfeaa2201cff18931177fca5a0823ff62d0005ff90a4202ff90942007be649881efc64cc833ff9006200ffd8910004facba005fff54884117f3224201ffcc130045fcc998813ff628c4537eb24821dff54131027be6218813fc410c41fffaa66008ff5834111ffea998813fc5150483ff1068608ffd834103ffac598803fd414805fdeaa68202ff50b32087f864a000bfc42cc8097fb2c4200ff50531077fe4398013fc648841dff2166001ffd03300e7fca49881efc6348467feaa66404bfd9641005fec688013fc510c449ff1008200ff50d21047f8c3a100bfc424c8017eb246203bf9953101dfccb10823ff4150401ff31a8201ff5412000ff8a188003fd328c45ffea868211bfd95400bffaa910803ff61508077f32e603eef10243007fec0a1023fd54d08017fb226000ff59132017f884a1002fd62cc01bfea926000ff1913201cfccba0026fd65c4005fea126400ff4ca4100fec208801eff65cc00fffb288606bfd951013ffc60a0807be40d0009ff28e821bff14131005fac1a0803ff6250441fea94622dff1434109ffaa5a00f7fc6550c81feaa48607ffcc530006feca8800efc654c801fe18a4004ff18221217fca5a181bfd6544001feb128227ff90141047ee8320803ff31d0001ffb028208f7d0e43007fa851887ffc428c445ff90e6211ffd9540047fac5a080afc6210c0ffe996600bff9452012ffca420803fc614c845ff216620fff54b30025f8c588013fe511040ffeb066200ff1913003ffc601881bff5444073ff9088602ff5493200ffa6088013fe418c471fe0808610ff9894000ff82088023fc5450001fe31a8000bf58f40027f62088023fe4210c05ff2124202bf18a43007fa8520827fc54c40097f30c620aff0cb1021ffaa1a1833fe324c00fff18e6000bf5864300ff461980f7fd5150c31ff2006204ff58a41027fa621890ffe51d0c0bff90a2007bf18d1006ffcca98002fd6110c09fe0844212ff8cb400077a85a0813fc2144051ff9028215ff55121007fac6a0013fe514c41dfe2166032ff04332017fc6499013fe41cc40fff29a8602f70c932047fea821823fc435084dfea808201bf98121025f8cb208b2fd6590409ffb206201ffd0110027facb88012fc620c401ff20e6007ff10d30007f8c69001ffd32cc4097e30a8402bf98b31004faca20823ff65d00117f3226408ff10f40017fea490037ff534c0013fb2a6004ff08621047fcc5a1823fe63d087bffa8a8601ff141201b7f821a10a7fc65504117f3222002ff0c92003ffcc32189ffe205040bff2122008ff9974219ffea999012fe61cc85fffa968204fd90441
  | 1 => 0x2ff6148009ff3006200bfd8542047f8a9a1013fc414c4017fb028229ff5414103fee6298823fc4050409fe3286208ff15243007fe8290013fd648840fffa186207bfd9331027fcc51886ffe504c4017eb106200bfd8532015f8c5a0883fd548c403fea828001ff8831006ffea89801efe6310401fea0a8000ffd9110027fcca208f7fd5250c037e3008203bf9954000ff821a0013fc514c401fe98a4007ff59730047f8c1a1833fc214c00ffea1e6208bf9904108f7aa8a0007fe4048009ff3046207ff59443007f8c6a1107fe50d0c09fe304622cff55241027fec5880d7fd5450801ffa0a6201bfd812000fbc6198013ff410c43bfeb2a6203bf1954116ffc61a0807fe30480017eb046203bf195300c7f88018823fe40d0425fe10e8000ff0c540027f8c518813fd6088409ff2086212ffc8740027fc2018807ff404c0057fb126407bf98d101cff84221823fe43d0887fe28e8624ff8c04115ffc6520806ff634c02bfe2a2421dbf58e31067fe4298023ff54d0049ff2808200fbd0a21005fec4a083ffd54cc061fe082643cff8c94300dfec8a0002fd63484017eb22420cff9093018dfeca99023ff43d044fff0828201ffc8120027f8cb10803fd624c415ff2962008bf19740027f8a22081bf55144009fe98c4208ff90b4008ffca2a006ffe304c437ff2026200ffd0d2003dfcc690813fd658c401ff10e8007ff10f30007fa8598076fd654c401fea1a2039ff9484303ffec99806ffe204c403de2068004ff18041007fac0a08f7ff5350c5dff9068207ff99330047f8842180afe63cc801fe20a4018ff9403103ff8a698013ff4110451fe2928231ffd4d32147fcc4a08a6fd6550401fea1c4207ff50c43015fcc59800bfc214c801ffb026207ff90d32007fac090883ff548c4017fb026207ff50f32027fcc71081efc65cc001feb122008bf99043027fa8388007fd50c4009fe0866201bf1813218ffea899023fe40d0c01fe9926023ff553310e7fe4098803ff434c409fe084622dff8834113ffca0a0867fc520c40fffb048602ffc8532047fc8020812fe6190409f710a4201ff88120025fec8188d7ff545080fff3088600ff4cb40027f8212080bfe424c8117f3206201ff14140007da649000bfe524c809fe10c6240ef9524300df8c1a1813fe631040ffe29a8604fd8c710217fe41a1813fc31c4001ff30a4004ffd8031005fec690823fe61d0011ffa188200ff58543015f8c498806ff6248003fd2068004ff94710017fca490012ff658c405fe10a8411ffd4940005fac888002fd6210409fe10c8207ff0c143047fa87a1027ff52c4001ff18a600cff1093001dfccba0813ff648c403fe0866003bf19531047faa8218b3ff54904057e3168608ef95043007fa8498003fe31d00097fb16201fff90a31007fc82980affe4290409ff9
  | 2 => 0x21005fec2980f7ff5450c01ff30a8435ff54142007fec69086ffc404c4037f3068407bf98d2000dfac1a0023ff4350465fe2866408ff10041047f881a18d3fc5050869ff2028402fb10a211e7fc84a1807de304c005ffa9664039f9973111ff8a998823fd43d0001ff30a8600bf587431e7fe42a180efc65484117e3224202ffd4b4200df8c0908b7fe10d040ffe1908600bfd8d42005fec898807fe40500017fb126004ff94521007fac890002fd60d0c01fe98a8002ffd4a2105ffcca90007fe1048001ffb226207bf98e4103efacb988dbfc50d08017eb148601ff94310005fac890023ef42508097fb1e2008ff105400a7fcc090903ff5290c11df2a68000ff50d42007fec099017fc324402b7eb2a422eff14b4100df8c198823fc65d08057e3126035bf59542047fccba0803fd438c40ffe3066408ff98343017f8a4900fbfc5090c0f7f31e8000bf5933203ff8a7990cffc51cc80fff3066402ff8833201dfcca99012fc62904077f32e8031ff1453200dfec2880a7fd515040fff3066203bf9952014ffea2a0823ff4350061fe302641bff841310177c85a10cefd65cc805fe1966408ff58343045fcc898007fd20c4009ffa0e2004bfd971000ffe40a0003fd434c805ff102642fbf59741047f680a0002bf644c0017eb066400ef50d4018ffca89901ffd64cc80fff3148602ff0ca2114ffca6a080afe62504017fb0a8008ff183421effacaa1823fd63d0401ffb0a4008ff1504306ffaa898023fd61d00097e3286204bfd9441047f884a1873fc524c409fea886204bf18f10017f865a1006ff6044011feaa68004bfd922100ffc6188053fc5048483ff0868600bf58730047f887a089ffc2050411ff2a48204ff98e41007fac69008efd65cc4017fb1a8002bf98a41017fea490807fe40c4001feb0a8004ff4c71000ffc40a0023fe62d0011fe2148204ff5903103ff8652190bfc52d0c57ff9048208ffd834314ffaa4a081bfc544404d7eb28823aff5484300ffca090013fe101040fff2986204ffd9441007ba6498813fc63104077f3288200ff50e41017dc6599013fd4110409fe1088201bf98221027fcc020813ff510c44bff9008207ff50f301a7f820a101eff65cc411feb168000bf58f4103ff8a798873fe424c40fffb266402ef10b4219ff8a99900efe6544011ff31e8207bf98f4100ff82098003fc6150c5bff2868225ff14841007fe878800afc6244039fe2126204ff087310adfeca90813fe658c411feb2e8208ff10143047f8c5a0813fd651040f7e32c8604ff14741027f8c120863fc200c403ff906200bff1452003efcca218c7fd544c809fe20e2010ff9494003df8cb99002fd634800dbe32a2002ff0c92100fe8218800efc654402ffe2a44203bf9944302ffcc4880f6fd6490c09feb048204f78c53106ffaca9800
  | 3 => 0xf31a422aff1424103df8c998083ff528c4077e32a4005ff9491000ffc20a0006fc60504037f3006204ff98a4107ff8a998013ff310c401ffb1a2028ff8c941027fec1108a7ff655045ffea8e822cffd4a4106ff8a89800bf72188411ff32e8603bf19543047f8a9a001fde4310c09ff28e620bff54520027f8c42081ffe62cc4037f3048200ffd0d2100ff881880fbfe2090c0fdf21a863aef55043025f8c988003fc6150803fea822002ffc812114ffea6a080bfe52cc803fe2866008ff98743007fc86a081eff65cc85fff29e8210ff1494021ffea7a1813fc4148411ffb168600ffd854015f7c852081ffe534c41fffa966000ff185301d7faa021803fe6448417ff29a4000bfd9121007fec6a00f7fd5450c11ff3068200ff59130017fca51081ffe320c409ffb2c4201ff94140015fcc5a0802ff644c817ffa8a4008f7d0d4300ffa818801bff654403bfea8a6202ff94b4217ffea3a081ffc328c411ff3168200ffcc94115ff8652081ffc6210c05f72168427ff1814113ff860a081ffc5390c0ffe2186202ff88121015f8c5a00fffc5290c017eb206200fd8c51018ffcca990cffd50cc80ffe196603aff9444318ff8a899013ff63c4009ff32c823fff94a43017d843a1007fc204805bfe1068204ff14710027f86288023ff4250443fe2866226ff94c4100dfcc1a08a7fc5350409ffb2e2004ffd8041017ee4290803fd635043bffa8a6207ff94f43027fa8310813fe514402ffea844207ff98843017fca49081ffd6110c01fe31a2007ffcc83100ffa809010ffd51d0c47ffa96623fffc864300ffc21880dffd50d0867ff28e6401bf9824314ffea0a08ffff2090c71fe2808604ffd8831027f86290813fd650c401de3226004ff18f10027faa2208effc1050c81deaa48600bf58f42047fec5a080efc6550015fe296203dbfd9543047fca8a0823fc40d041bbe32a601bff0813101df8caa1002fd61d08017eb048607ffd4c3103ff86598903fd5090c0ffe2986201ff10120007f8c69081efe63c4011fe2a28400ff99110027f86310802fd644c86fff28e843eff08243007fe841890fff51d0c17feb2a4034ff1814203ff86018883fc548c41b7fb2a6004ff9462101dfcca90813fd639047bfea9a8604ff99621047fe82a0013ec2148411ffa1a8600ff98d20047f8a920847fc51500017fb128601bf9813200ffc60a0107fc20d0c09ffa888211ff9954020ffc61a181ffe430c401fea0a4207ff9873003ffecb9806bff500c40ffe3148608ff5874300ff8a08806bfe540c4037f326803bff9814303ffac321903fe5190c09dea088207ff9873218dfaca9901bff52440177eb2a403cff085431d7fea421857fd504840ffea98623cff98943127f8402080afe6210c117fb2e8401bf18043047fec7a100bfc52d0801fea1a6016ff142
  | 4 => 0x867fe420c40fff32e6000ff5814300ffc4198003ff624c409fe90e2036ff9434200dfac188002fd60d080fffa1e6226ff54841137fea62088bff20cc401ffb226000ff4c9410b7fca110823ff42d0463fea82641dffd4d3103dfcc721803ff6050c09ff304422dff0c34100fdc409001fff324c45ffea9e8236ff8c3421affca2a1022fe648847dff2048602ffcc92008ffca6a0022ff65d0009fe28c421dff19531025fec98801ffc6590c09fe32e2000dfd9530005fac421803ff438845fffa868200ff59110007fa84a0807fe304407dff2848604ff50631004faca21807fe4044005ff10a4000ff50831167faa12082ffc534805ffe29e8208ffd8f41027fe831083bfe52cc085ff1968607bfd964303ff8a69882fff53480037f3066401f70c33007fbaa79801fdf32cc409feb246202ffd092006ffea498103fc5190c11fe2128202fb94920047fac7a0007fc504c0357eb286204ff1931000ff840a0097fe3210463ff28a6408ff953410b7fc81108bfff53d040fff1866404bfd892105ffca890013fe4150401ff21a4001ff1434009ffea5a001ffd62cc073ff900863cff18943027faa38801efc6510c01ffa1a2001fd04110015fec4a1002fd644c403fc0822007ff0c13103ffe8621807ff5048001feb22620bff54d2000ffe4088023fe40d0819ff3126004ff8c43108dfacaa005bfe308846b7fb2a8402ff0c942047fec3a181fff6190c33fe2106200ff18520027f88288023fe54d0c01fea0e6000ffd093103ffcc998813fc514840fffa1c8600ff9913100ffaa19801ffe6010c0fffb0e6402ff88342027fcca18877fd534c4077f32e8614ff9012103ff8a7a1813ff51c40097e32e201dffd413103dfcc621827fe53c401fff28e6004ff94641017fe411088bfe52cc40fff1848604ff19641007fcc8990a7fe6550405ff9066402ff48520097f865a009bfc53104097e3108204efd0441007fe6420807fe2044011faa088200ff5912103ff86498007fc4050011ffa108238ff88043045f8c898823fc63d0461fe2826404bf18520047fe87a10effc6050c01f7b128207ff0c343007f8c89880bff20d0801feb026214ff8c121047fc862080afe62c4017fe32a4002ffd4932027f88310803fd625007bff32a8600bf58d10007fa8398813fc648c403fe1062000ff58d2103ff8c999093fc3010411ffb0e8426ff54c4103df8c99880bf42148411bf32e8002bf18b3103ff8c22181ffc6190c47fea866200ff505100f7f8a11881fff6210c277eb2e8043ffd4343017fc4110803fd3148451fe3128203bf99643027e8431080bff5250801ffb0a8643ff54f43025fcc3a1813fe63c4011ff2a08202ff0c932027de431085efd65884017eb168202fb10942027feca1889bff5010403fc1826000ff18d410d7faa41881ff7318c401f
  | 5 => 0x8540047fa85a08c3fe404c8097e30a8016ff10221027fe4220812fe610c411fe2168600ff9854001dfccb98813fc6390405fe2124008ff10b41047fc8420803fd324c401ff18a401aff55031157fc6120806fc60d0405fea124000ffd073008ffaa6a0003ff614c809feb04623dffd4943007ba6598803fe4148003ff1026004ff9053103ffa6418813ff419043bff2a26200ffd8d4100ffc208803ffc51cc02bfe32a4202bf189410affeca90823fc4090c51ff2128201ff0c14000ffc41a000efe65c4011fba0a8208bf1911008ffacaa002bfe32c4011ffa128002fec812003ffec398047ff5350001ffa1c6201ff541300077a87a0007fe30cc00bfe2922002bf99342005fec4a0003bf4350005ff9026408ff983420f7fc6118803ff434c803df2028004ff8c531007fac2a10e7fc5210c015e3224201ffcc120025fcc220813df318c409fe10a8215ff99521046facba0023fe54500017eb14822aff9024103ffacb99003fd424c401fe9908201ffd414003ff8c021803fc43c40077f32e6407ff583320a7f8809081ffc314c003ee1826007ff0c943027fc2110803fc615000fffb166204ffd922103ffac52180bfd524800fef29e602bff94a41025fcc3a1003ff41cc419ff2926036ff84342027f820a0813fc210c403fe1862001bfd8130027fac020803ff32c4009fe28e6208bf99332027fac018877fd524c43fff904620df754d3004ffea7880bffd52d0425ff2968004bf98740005fac71081ffd31cc005fe2944200ff485401f7fc212180efe655044fff3028208ffd0d42027f8831881bfe6544011ffa1c8204ff90441047f8842080bff2050801fea0a6004ff88710007f8c890813fc100c4057e3166009ff14f1002ff8c488013ff64c400ffe18e6000bf58732047fa8420853fe5048401ff21e2002ff8814203ffec99886ffc604c40fffa1e6004ffd964103ffec1988a7ff545046ffe28e8413ef55340007fe858800bde32cc851ff90a8214ff84121025feca18857fd6548403ff9066001ff481100a7f8c090802ef6250411fe31e8400ff99120047fa83a001ffe6510c017eb266207ff1973000ffaa1a001bfc654400f7e32e621eff88231007f883980bbfe32d0413ff2a62007bf98c3100ffca088012fc6388471ff2808608bf99231017fc6490013ff658c40fff1866204fd94710027facb20807fc304803fff2946200ffd0510197fca1990ebfc5110c037e3026208ff1514303df8c6a0827fd53c400ffd9826004ff1451003ffe879906bff540c41bef29a6004bf1963101dfccaa1022fc644c0017eb008600bfd8931197fc8199022fe644c40ffe32e6403bf9953006ffca298002ff6150c01ff9968208bf99120007f863a010ffd52d0c09fe20e6202ff14921027fcc588003fc4348023fea8a8011ff1954014dfecaa0
  | 6 => 0x5df2128400bf58b400affea69083bfc52cc00dffa8a2001bf18243005fac620813fc104c40fffb166000ff90d210affca890807fc40cc00fdea188604ffd8841027fe8318803ff635080dfea8a2003bf9974200df8c12081eff6510c09fe3006207fbcc9320affea0908a7be54504417eb2c6208bf19132017f8a499047fd52500017fb224007ffd9732027facb10812fc614c80fff2988635ff5954200df8c110806fc608c403ff28680009fd9510047fe83a001bfe5344011feaa08200ff50d4100ff820900f3fe5250c09ffb046202bf98a31027f821a0803fd32c4009ff084623affd444319ffea399007fe504c067fea8e6400ff58142027fc212081afd6544001ffb224004ff18a410fff8a5188d3fe105081bfe28a6007bfd9332187fca09901ffe3010c09ff3106204ff5462100dfcc0a0812fe6190c09ff20e2008ff9514303ff8c198803ff414c00fff29e6400bf5803100dfcc388013fc21d0455ff1048200bf583310177884a1036fd654c06ffea8e8421ff103310bffca71081efe63d0827fe28e8001ff08110045f8cba082fff5448009ffb14820aff10b101effaa0a1813fe31c4005fe292842bff14a41047fea9a0813fd6310403fe9824008ffd8740047fc85a0803ff3150003ff0866000ff50b1001dfcca18883fd508c41bfe32a6001bf98143177fe43a0807ff4048005fe1066400ff581321bffca7a1103fd5190c09ffa8c4202ffc852003fea6218813fc214c405ff2124004bf98621007ea6388076ff654c43bffb2a6201bf58330005fac988002bf6448443ff0866200ff4c510047fac3a1107fc10d0c057f3108204bf1854300ffc61a0102fd6590c05fe1068437ffd474210ffc819880aff6148411fe2068401bfd8140017f8411081ffc61cc021ff1928007ff94e4300ffc8098077ff544c403ff1826000efd0941007fa6298073fe324c40ffeb0e6015ff545210affca690807ff30c4011fe2008604ff04041007fe8290807fe40d0001fe98e8040ffd4643025fec91881f7e65cc439ff90a6208ff18341027f8a320823fd63d0811fe20e8004ffc8431027fac41890bfc21d0c03fe2022007bfd9330005fec090887fe20cc40fff316603bff141431bdfacba1003ff6448445fe2966202bf58a210f7fc8118807fe50cc07b7eb2a8643bf59743187fc609907bfe508c405fe9924007ff58243015fac599003fd32d0411feb2e8602ff0812110ffca198807ff1044011ffaa68600ffd0d30007fe64a0007fd4044013fea962004bfd8e21015fac5a1023fc435000fff98a6232ff10332007fac2990d3fe5050809feb146201ffc8130157fca120802ff6050811ffa1e8042ffc8743007f8829800bde324c801ff21a8035ff14542047fc85a181fff60cc82bffa8a4207ff59731027fe638801ffc434c403ff9068000ff8
  | 7 => 0x9801ffc64cc013feaa6203abf5944303ffca69901ffe53cc00fff29c6202bf98831027fcc120803fd6350811fe32e8000af19130037f8a688003ff324400ffea9e621aff15031047fac1a1023ff60d080fff3048602bfd8d32147f864a081ffe434c463ffa8a6407ff14c4300ff820a00effe3050c0ffe21e6407ff18b31005fec0a183ffd51cc0037f3008204ff54631007f88710807fc40d0011fea1e8202ffcca21017faa490813fe6488401fea1a4004ff94631047f887a1003ff614c003fe1822001ff1013003ff8c399013fd519040fff1948610ff90940007fac29001ffc6510c09ff10a2000bf58b1000ff0409000bfc204c821fe10a8000ef50941007fe62908c7fd654c803fea026037ff14f42007fe848801ffc3010c05ffa166407ff193311c7fc202180bfe3248405f61926407ffd9643047fca821803ec625046ffea9e8417ff14e2108ffea8a001fff5310c7bff28a8608ffd504100df8c0a1807ff4050009ffa8c6204ff18e21037faa688007fa10c4001fea1a6207ff90c43007fec498003fe434400dff2a22035ffd454203dfcc710802fd624400dfb28a2001ffd41101d7fea021813ff5190403ff0826000ff10d2103ff8619901fbf4310c61ff3026407ff54c43015f8c4a1823bf42d0403fb0862033ff953320f7f841188cfff50cc81f7eb2e6007ffd84430477ca9a081fff53cc811fe2a28204bf984431bffea1a1003fd4250009df20a822aff08241017f840a101ffc3090c077f32c6202ffd0a2105ffaa890003fe614c00fff21e6400ff485100bffea1108dbfc30d086bfe32a8408ff98f4000ff82188006fe604c42fffa9c420fffd4730187f88099023fd54d0403ff0868000ff98d40007fcc89800be42148401ff21c4204ff087100dffcc098803fd634406fffa9e8417ff952210077ec8980f3ff2050c11fea188200bf5824111ffaa398823fe65d0011fe21a8204ff98841047fec7a001ffd5390c2ffea9c4208ff9534200ff84198006fe63cc0097e3244204ff59310067f8a498007fe40cc069ff1828434ff98142027ba6218803ff3148005fe10a4002ffcc92103ffea721807fa104803dfe2046212ff14b4003ffec021802fd61d007ddf2048608ff95243047fc8021827ff54c400fff32c8607ff94f3100ffa6188002ff6350403de2028029ff54d411d7faa221823fc4090409ff32e2040ffd4243047f880a1087fc20cc409ff90e2000bfd8910057fc8588007ff40c4011ff21e823bff881430aff8a690877fd544c447ffa8e6213ff947401c7f84021807ff50c4029fe1824204ff8852103ffa861881efc63508057f3168008ff1974100dfcc118823fc42500097e3146207efd0e43017fe8490822fe64cc001ff18a8001ff50330007fec4a0003fe63440057fb228408ff55343047f88620803fe415000
  | 8 => 0xf9931003ff88718857ff5448409ff28a8202ff4ca2114f7aa8a081ffc534c861ff0826426ffd48410cffca418813ff6310463ffb2a6408efd0f4003ff8611881ffc324c457de2148207ff99332007fa4298013fe4144047fea966208ff10e4103ff8609900efe6590405ffa126408bfd9741047f8cba1803ff60484073f3288207ff59331027fac788022fc65d0c01fe90e8000ff1911000ff4408800bee3248001ffa16602aff0c24118ffea099023fc63d0009ff20c4207ff14e3103ffe6518823fc54d044bdf210821aff54031007fe8518823fd62d0c017eb008208ff59740017fca4a100afe62500037e3028402bb18941047fecba180bfd3248401ff9948202ff10a2100ffe60880d3fc3050809fea08620bff1512003ff865a1813bf41904017eb1c8207ff14f30027fc6310847fd5450005ffa128402ff10b421affea6a10d7fc5350877ff0828607ff997321affecaa100bfd42884013eb2e6225ff0c84103ffc659881fff65cc411ffa148204ffd824103ffac998012fe61cc001ff21a8420ffd4e3104feaa388023fc62d0003fe1866029ffd494100ff080a0006fe605080fff29a6008ff18740107fea11881fff32cc023df2a28004fd8c43103ffc87188b3ff5090459ffa9c8208ff10a4303ff8cb988f3fc5250c09feb1c4201bf98331047fcc3a101bfd524400ffeb0e6401bf98043005fac898077fc544c4097e30a600dff54530047fca8a1003fe439046bfea9a8407ff10f31007fc43980d7ff5050801fea1e2031ff19532027fca218813fd62c4001ffb1a4013ff547400b7f86110823ff65d0859fea9c8207ffd4f3003ffc8798013fe414842bfea9a4200ff19120026fcca20813fe3148405ee1966401ffd43301affaa2a1023fc54104037f3068607ffccb3106ffea29800bfd52cc86bff29a8413ffd474000fd84090047fc5350011fe2a68607bf18d4009ffca7a000e7c654401fff2a66007ff54f3202ffc648800e7e6510c05fe2124200bf5822103efaca2189ffc5050411de2108202ff54a21026faca20813fc620c405fea968423ff9533103ffaa7980f7fc5150c017fb1a4000ef19121025f8ca2081fff6290c177fb2a4007ff8c843045f8c89000afe624400fff21e6200ff4c940037fea688006fc600c4117f3262001ff0813018ffaa299013ff3188401ffa166229ff55141005fac598802fd6488459ff29c8200ff5893000ff841a0023dd4310c0ffe1866240ff54a431dffc80a1813fc518c4017fb222004bf196211dffca0a180bfe32cc823ffa8a8010ffc85400d7fea418802fd64cc001fe90e6018ff1403111ffea19880efe6550c0fffa9e6200bf58f10005fec099003fc434400ffeb10860cff18930027f8ca20837ff654c005ff1968402bf18940017fc6510803ff644c871df2008607ff0c83101cf8ca
  | 9 => 0x320230000078d580000606d0b80370ce8012d88068010072d700e83900000a0b280580b80000011980a8000bda5a80101b80a0068f580082380080300300000b8048578060340050e581600f00081683280606e00701900300501c00200d8028060e3a9180500088800080080080000d98c800800801ae580100180d87e82d80100980036580000687000d80380b80000080000a80503880500080002181203900380081f00200401a9aa80b80000080301e8120078a681f1b29a600000000b8670080b980080000180600106680e00c01c80180980380000000000100002d8018058008060003a600080e80200604b8260a5801018ac700900800d80500009000080b80180000080197980586303808980000000300400080004d80082080a80083381a08e83000001900e00180080300200082c01880000493980a80800000200100280000000500400000f80200000b8139c500180101027b0000090963cf80102880880000000f8010020e500085d00003600000000080280480a0ab80101180a00180000001080883f81900e8000118f180b8050008168088000268100002fb80003800383680c80001011300013480000000b081831098803064000800008803005001b4580a00001680680012a2ebbed86a80084f0010018098198ff91880380f00480000202b8000008060d680f0dd80082980d00100100900c00507009681480002c0000e601d855ac200000080736081ffe65cc409ff3206200ff4c910015fcc4a184ffc53d0005fea124200ff98d4203ffe64980effc2050c81ffaa48604ff04121005fac518822ff65d0c45fe2166200ffccb4018ffaa6990fbfc1090c05fea928404ff99231017f843a10b3fd5290401fea166204ffcc631017fe4399022fc65d0811ffa168002fbc8132015fcc5a181ffc6090c01ff10a6002ff90b3203df8c690023fe43d000ffe3166005ff1091000ff86098003ff424c021fe3128008ffd534205ffeca90077ff524c4057f3148602ff90b42007ea62880fffc2190c31ff1006204ffc8621147fca4a08f7ff6550c01fc9022032ff84332025f8c918807fc30d0005ff2144202ffc874209ffea7a000afe624c401feb128607ff10d3214ffacaa0813fc658c405ff1928407ff5964306ffca8980d7fe655080fff21a6001ffd41300fffc6518877fe654c4037e3066402bf98930047fca9a00bbfc32d040ffeb00861cff9893103ffe6398023fd65d0817f6a924002ff14b32027f8c8188fffe4290c1bfea9a6008ef10043027fec710907fc50d0c01fea1a8000efd912100ffea1a0013fe3144049fe2808200bf58b4300df8c1a1083fe548c427fea9e8020ff54e31017fe649910fff52d0c11fe30e8607ff8cb30007fac298023ff65d0409fe10a4200ffcc510167f8a720803fd4244001ffb128604f
  | 10 => 0xc00203483d00280180000700280101108d80601401581f80102a0068000000a180000500016980b81200300f8030001d218b18e80a0019718018300060050038c702781c96c80e06880002e01b81600001c8040000008040618010031c01182d226600000204f81081102b80e00006d08e9993068028010148068000038040002ef0010400000000000050d881f16600080a8000020420030088030390cf00600a02201705e01101e80780584300f8610eb00480a811a8f00080981880580e01080411c81400800f8031448a885100283201b80081b832000805005001801003a4880280000401e80800400900280f01a00380004417902180d01800001d83980901405083800901b8000150128100000018d18aa8028110008000a222680003280000b0080000042dd01100100001a8000018070020000520cc80088700e8000500108028188058030ea80600a81600000027a01f81a0018da80800500a03700100a80002400700500000400117780280b801000000036b5f80500000c81f00682781680000080108780310d000311829a7783a80580a8070009b1001006801b1c83c0018210259e600202204cad182184400984080e8018000000f900101300100080182900c80a00d0000038008bc0000018040008038019f437702303200001e09a00f81f00000003500006b84a00481d00000e9828ab0032868050038268000020018018128140c680180380b84600b00380400326b03d80b8280000440188000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc75d85321febd42d9132005ee76189410067f65d9130004ff7258f10004fd755873203ef83058332004ff73583411defa30d8143046be5458443006ed63d8941004fd7650a3101cfc75d9121044fe76d9130004fe76d0d20004fd75d9132006bc40d913200cfe70d8d10016ec6250940006bf745913120cff73591301e5dd7399132006bd64d08310067f65105302be7c32d9530006ed6318941007cd324c5202f7ad41d0a21044ff76d0730006fb7059120005ef725854000cfc70584431c6be4058043004fc7650d210067e725944303cfd74d8143026dc3158c411c6fa10580431f6bf73d913000cfe705864300dee704c92001cfc7558f4200cfe705874225e7c31d951001c7e76d9530004bf7458d2100cfe76d8141006bf6410d1003cfc7358243006ed75d8941004fd73d9121046be6419130004ff7058c41014fc72591310067f65cc91003ef43158730006dd63cc84114e7e6550731044fc7458a31006f651d85320067f71d9530046be6450e31024fc7158342044fd72d8d420479c4350d4200dbc70d0d400067c75591302b67f40d9530004fd7558c4103cfe73d81420067f6590d10007ad5418941047ac42509400067c7559110046f441587420067f6598d10005df73585402ddbd7550f4003ebf7459332006f7619854200cfc764c51000cfe7058b3100dbe7050f4012ebf21191210467d4259740014fe764c52103eee3258332007ad54d8941014fc7258c411fcfe76191320067f2159740046bd7219130004ff7158343014fc7458342014fc745874203eef3258b3103cfc73591212567d30d95101f6bf6498d40026f7604c51001cfc7558332005dd7310530005ed7290e2103edc634c51003ef77158730046bc64d0d32004fe7690d210267c21594410067f7558d2000cfc70d912100cfc705884100dfa7090540004fe76509310467c7459443014fe7650d320ceef20588310267c1059441024ff768c740044ff76d0d1006d7c75591302eebf1019121004ff7558b43024fc769053006d7e759853013efa10d81410067f65505100067c755824300777654c510004ff75587402eeef621912101cfe7558031005bc7458121006bc75d9130004fd70d8d41045be740c74015ebc52d912101c7c7559110006bd6519130014fc725933101cfc7559231014fe7258f10005dc7359110044ff76d09100067c72d9530044fc7458331025dc764c931044ff765051023f74658c510024ff7258831044fd70d8940024fe71592210067c7558d202567e10d9510006bc65d91211e6bd42593321debf40593301a4ff7059120004fd71d9120007d4714c93103cfe76d8d40004fd761053003cfc76cc94001cfc7559331014fe72d814300cfe7650d30004fc7650d20175f77159121016be6250941117e42198d212577a20d9510046be6450731
  | 1 => 0xc941004fd7690d20025de71cc931004fd75591322f7ac41d8941026bd4158a4100cfc7058b311b6fa205834219e7c65cc91003e7c43594430367e76d951013ef71058740005f97090540006ef7258d20016dc62cc93101cfc7558443004fd7558f40046df4358f41006be60d912103ebf7459331006be73d91210467f745944300cfe7690540006be76191302567c70d9510014fc7258331046bc64105302577771d9510046be5458341004ff705883102fe86248110004ff7458b101c6bd50191302febf72d9121005de76cc93101cfe7558343026be4159031004ff7259330015ee720c5202577410d9510294fe7619120006ef62cc941026ee2158a31026df7358f10005f57110d101f6bc30d91302febe51d9121004fd76cc740005bd74cc54001cfe75d814201cfe75d91200057f755853003cfc76cc9410ffe421d8d2113ebd4059310006bc7458d1003e7c30597310067f755891001cfe75d813101cfc7558231046bc6450d32005f77150e41004fd7558043116ec4258b3103edc6390d4210df77158d100fcfe7618d21004ff7558730006f77159132044fe7688740006bd5459110004ff705912113ef860581411a6fa20d8142004fe7650d20026f91058b10025b47150941004fe760c52025e7e21d9510004fc764c540004ff7558d21006bf531913032dbf7550b412a6bc32191300067c6598d101476e7518941006bf645053100cfc72d8121126fa30580412067c6590d100067f7259443024fc73583310057f75591100def860581311feec6290d41004fd75d8d20024ff72d8d211a6fa40d81420467d4259443006bc53d9121296bf40d912003efb70583310e4fd764c5210467c4259443065ec7250530015ec7250e210073f651913003cff7258843046be76d09410057d7598d2103cfe76d8d20004ff7558f42004ff75d8931004fe760c5402567d71d9510005f77150b1003e7e315944301cfc7558e2101cfc7558d21004ff75d8542026bf4158a41006df6398d41004ff75d8520007cf624c931026de3158f1001cfe75d812122f74654c510046bf7019121006bd54d912014e7c6550510006bc6498d2103cfe73d8520025f4714c841005ef7250530024fe76cca41006bc71d9130004ff7648540006dd634ca4100cfc70592210e7e42158d2103cfd70d89300067f2159443006bf6450d210ad7e7510d21004ff7650a3100dfa709052000cfc7058843006bf651912103ef7315844310efa1058331046bf721913003ef77158443046be5458043145ee76d89410067e74597311be7c65d0930017cf734c92000dfa708c520046ec4258843014ec7259131004ff7258041006bc4259331006ee10d894115dbe7619121004ff764cb401def850d8143044fe74d85321ad7e7518542005ed7210d2015cbe76d0941005ef725854301cf
  | 2 => 0x14fd7358b30004fe7688540024fc71d91102efac41189412b75f73d9530014fe7259331044ff7650d32005fb7050540045bf7350d40006bc6458d21004ff7258343006bf51d913000cfc70d8910004ff75583311f6bd73d913001cfe75d8542006ee43d8941014fe76d8940006ee50d8941006bf52d9130006be71d9130004ff7358b1003ebf4358243046ec4258b41005f97090520004fe768c540004fe76cc94101cfe75d81431f4be7619130196fa2058332006bd545923101cfe7558231014fc72d85302567d40d9510046ec4258b43016ee624c841004ff7559130006be70d9121315bf7550941014fe7258343006bd51191302e67f2059740004ff7359121025f671ccb1001cfe7558f410067f7259731024fe71d813203cfc73582410067e62d951001cfe75591310467e7459740007cf634c920006be425933101cfe7558b4301cfe7558332044fc7458d21006bc3019121004ff75583410067f72d9510006bf6410520227f25148110006be5459310017ae74d0a2112fb42119121006be5458643004fd7558343045be74cc540046bd7319121024fc7158243006bc40d9121044ff76d0a31026bf7459221045bf7650f40004fe7610d2015ebd42d9121005f57190e4125e7e31d95101a4fd769912003ef73158643004fe7650520004fd760c520026de3158c4103f9c4350d320ad7c7558121004ff755804103cff7658d20026df7358c41004ff725844303ef4764c510024f471591322febf10d9121004ff7159120005ed7290d2003e7d435944303efb7058332004fd761073000dbc7050f40014ff70d91200467f405944101cfe75582432f5ed76d0a2103fd83050d3000cfe70d85421f6bf20d913000cfc70d9110046f84058343004fd76d0d2001cfc7558a4304d7e7510f10005f9708c530044fc76d0d20004fe764c9410357c75591100067f65d0d100067d7259441005df735053100cfe76d8143046df4358c410467d74594411f6bf50d91300067f65d89100067f6558530004ff7058a4301cfc75d8132004ff76485300067f2059731006ec7258d100c6fa505803101cfc7559332046fb4058043005f9700c540004ff7258f410067e735944100cfc7458f400ad7e7519121006be651913000cfe70d85320057d7598d1000dfa70d0d30004ff75d8141186f860581322e67c3059740046f7415844301cfe75d85401feee4258a4303f5e654cb310057f755852000cfc7158f10027f3608c510005dc7358141046df7358f40046be641913113cfd765051001cfe7558910215df735913203cfc7650b3000cfe76d0d301667c65905300063c65d9130047bb6050d40006bf7458d20014fc725803103e7e3059443004ff735822103cfe76d0b310067c42d95100067e74d9510024fe71d913018e7c654c930004fd74d8931016ec62c
  | 3 => 0xd3258332146ec425922100cfc7650d4008d7e75cc5400479f7350f400047f755824303cff72d913200cfd72d91200feee3258a3103ef6634c7101c6be301913001cfc7558243004ff705913100cfe7058b43004fe7650d21005f571ccb1015ebc4258a4103e7d325973117e7c65d0530006bf644c93000cfd71582210067c651853003ebe6350f40006bf6490530004fd72d8143006dc30d8d211f6be20d9130004bf7458d10006dc735891012ebf5219121006ec75d894101c7c75582210267c4159441004ff7558a41016de624c93130e7e415973100cfe768c530046fb7058342004fd7558d21024ff7058041024fe76cc841014fe72580412567d20d95101e6ec62589430067e32d9510016ac6250941005f47159132005f47158132077e42148730005ed72cc520006ed65d894101c7c7558241016ef604c9202f6ec21587420067f654c510046be6490f1003efb30583321e6bf4259332024fc715884300cfc73d8131006bf51191210067f7558031045bf75d0d400467e405974000cfc745874000df870509400463d7519121005ef7250540024fe7690d41006ec631894103ebc4359330026fa1058b100e5f57198d2101cfc75d8d20004ff7650910044ff765053103eec634c92000cfc70d9131004fc7650d10044fe76d91100067e42d95101f79e30d91300067c7359740026df3158831044be76d9121046be6450a31005dd73d0531046be7019121006ee63d8941006ec63d8941024fc715823108d7c7558d40005f57190d10046f77158740014fe725844303cfc7650b31004fc764c9100067c325944103ebc6350d40046bd701912101cfc75590310067d7159731004fe7650910004fd7650b31046bc64d0531006bc64d8d212f6ee31d89410067f655891003cfc76cc5400057f7558141006f77158d2100cfe7058b41006bf64d0d3121e7c65d0d10015ee72cc521016bc6250941004fd72d8d41006df6398d21024ff7158f100057d7519132004ff7058f410267e715944103cfc764873000df8705051012ebf2019121044fd70d8d4001cfc75d9131006bf5019121016bc7650941006bf6498d212f6ec31d894101cfe7559310006bc6458530004ff7650b10004fd76cc540027b44150510004ff7158043306ef43d8941044fe74d8d1001cfe7558a430067d73597400067f6550d3015ebf21d9121024fc7610530024f47158d20044fe74d8910006f7764c7100067e40597310067e7059731046bd7519130004fd7559221006bd5219130004ff7058b31004ff7258d10004fd70d854302df97098520006ed52d8931006ee73d89410067c65d8910004bf745891001c7c7558d10027f3604c5102be7c43d9530004fd75587420067c7259731006bc42d9131027e421cc521006bf65d9121006bf64d09302b67e30d9530014fc7650d32
  | 4 => 0x923101cfc75d9110006be62d9130005ef7250d420067c7259443005f57110e2112ebd3219121004ff75d8540024fc7688530006bf6410d20024fe76d0f10024fc76885400067f70594430e5ec7250531004fd76d0d10046bf7119130004fd764c7400067d725974003cfc7650730006dd63cca4103cfc7690d10145f571991212e67f30597400467f4259740146ee42d8941004fd7558a4100df6704c510046dc4358f40044ff7659120014fe745834214e7c6550530007d5324c710004ff7558910006bf70d9121006ec7259131006bf6458d2100df4704c510046be7119121026fb705823103ebe4359031006bd545844300cfc705864303eef3258831004fe768c52003ef77158732006ef75d89410f6df30d8d10024fc7158241006be54d9131006ed65189410ee7c654c5101f6bd10d9130015ec725052003fd43150d31005dc7358540005ef725052012ebe20191210267d71594410067f7359740025f7734c5100057d7518d20004ff7558241004fd7558f10004fe764c910006bd73d9121276f521d85200057d75cc51015fb421d9121006bc30d9121005bf7458931006bc75d9121044bc7458910046fb7058341026dc3158e4101cfc7558f412a6be5319130025bc71d094101cfc7558031006fb7058d1001cfc7558730004fd75d9121026f81058221006ee6318941216ee3258b430067d654cb40046ec42588410067d7159443046bc6450531005ef725053105d7e75cc520004ff755884303e7f31597311f6bf30d9130014fc7359332005f9700c52001cfc75d8d21004ff73593102b67e70d95300057d7510d2103cfd71d8131044fc74582311a6ef2058b4003e7f30597310067c6559130004fd70d894300cfe70d8910014fe7690d42024ff71593102e67e2059740025dc714c931005f77150d41027e421d05210067c6558910306ee54d8941004ff70587430467e4159740014fe725923103ef431584431e6df3258f42086ec6258940005bd74cca41026bc4159231044bc7458d2003edc634c94003cfe76d07300067d65cc7400073e751912101cfe7558341004fd71d8d20004ff7559231044fc7458f1014d7c755814106d7e7599130006bc645893003cfd72d813203cff76ccb10004fd7558831014fc7259231024fc760c540025f47150e411febf42d9132006dd6390e41027e4214851018e7e654cb40046bc731913011e7e65cc740004fd71d8d4003cfe73d8121004fd7690530006be5458243006ef624851001cfe7558c41005dc735852012fa421191210ed7e75191311feee5258a43006f76198532004fe76905202aebf31d913001cfc7558b43004fc764c940006bc70d91211feec2158a43085ec7250540006f77159131006df7358d21006df63cc510004ef7258d10026ee21588412b67c73d9530046bc6450d3003ee
  | 5 => 0x6bf7650f4015ebf52d9121024fc7610f100067e2059731005bf7458d10006bc62d913003ede634cb101c6bc5019130006df63cc521006df6390d4203eef7258b302a6bc5319130004fe7650d101defa60d8143006ee65d8941004fd7650e2101cfc75583310fedd32d8d2100cfc70d85200467f745944103ef43158643025f47150b10006bd651912127def754c920006bf6418530006f7618c53003e7c73597310467d4359441004fd75d8931027e421505210ddf5738c5100073c65d9130004fd73d9120004ff7158b3015cbe7619121004fd755913024ef710d8520004ff75d9121024fd7159310004ff7258c41004ff755822103ebe63d0d40026ec2158a31004fd76d0f10024fc7158e21014fc72580432e67c2059740006bc64cc521004fd73d891000cfc70d8d2103edc6350d41004ff75d8532005f77150a4101cfe7558b31005bc744851015fa421d9121014fc7258243044fd70d854003eec3258843005f77150b31025bc7150b411f6bc20d9130004fd7558b4020edf30d8d40025de714cb310067d65d073100dfb724811000cfc76d0d30006be42d9131026ee2158831005be7498530004fc7648530004fd76d0e21006bf6499110024fe76d85300467f4159740004ff7558f10186ef2058b3025e7c21d9510046be72191302c57e76d9530026f810580310079e53d9130006bf64d8d211dcfd7650d30005bc74581322567c10d9510147ad741894100cfc7059231004ff755883100cfc7058f4203cfc7650531004ff7558231004fd765053103cff76cc841004ff76487302efae2119121014fc7258f41004ff7258730004fc7650930005bc744873001cfc7558041024fc7158043184ff7058d200467c40594430263f4159441004fd7558f41046bc7519121006ef70d8941004fd768c520227e952481100067c2059731216df32d8d420067f6518d1000dfa70d05100479c4350d41024fc7158f40005f57190d41006bc5219130006bf51d9121006bf64d0530004fd76105200067e725973115ebe4258a410357c7558d10004ff7558a31006dd6318d4225e7e71d9510046ef4258b40026ee2158b10146ee52d894115ebf20d91212e67d105974003ede6318d200067f65485302f7ac21d0941044fe76cc740004fd769073001cfe75d8930006bd545834100cfc7058a411ad7e75d81420057d7510f10006bf50d912103cff7058043005bf7458910146ee32d8941026bf745903103cfc7610d10006dd53d8d41025f67190f100057f7558131006df6398d42014fe7258231145ec7258d41014fc7258443014fe76d8930014fc725903100cfc7359330005bf744ca41046f8405804103eee634c92010cff7158d10026f6611854232dbd7550b41004ff7558b41005be76d0941006bf6499132004fd75d81312be7e73d9530004ff705
  | 6 => 0xf75191300067f73d9510007d7634c510006f7614c5300067c70597310a6fa60d8121005f47158930186fa20d813203cfc7358b41014fc76d052100cfc70d894303cff76ccb400079d53191302e67e105974001c7c7558910004fd70d9131046bc649052003cfc73d9130014fc74d89400067c6518d1003e7e43597310be7c6588530006dd6318d4003cfe76d0531004ff7358740006df634c940005bc7458910004fd75d8132026f4614c530004fc7650520006bf64cc52101cfe755923103ef6638c5101f6bc73d91300067f655093015ebd32d9121046be64d0a3103e7d3059731006be5119130004ff72582310067d6550731004fd764cb1001cfc75d8d42004fd75d9110044fc7458b3003cff7650e4103cfc7358a43046bc64d0d31004fd72d81410463c4259441024fd74d81412febc71d9121005f77150e31004fd70d8d21025f47150d4101cfc7559310014fc73d8930004fd75d814315ebe20d9121005be7498d211def86058143046bc6410d10006dd6318d100047f7558d20004fd7558b3103cfc7358341046df4358f421ffe42190d21046bc7519130005f9708c520315bd7550941004fd76cc9100067e10597310067e72d95100067f21d95301f6be10d9130005f77150910014fe72d8543014fe7258f410067c74d9530004fd75591212b67c40d9530044fc74587322b67f10d9530004fe764c520004ff72591310067c71d9530004fd76887301f7b830d91300057f75585402f7af74d8941026f4618c530005ed7210520004ff7058e4101cfe7558f10006be75d9130004fd72d8d4001c7c7558d20024fe7650b10004ff764c910044fc764c740004ff764c5400067d7259731004fd72d9130046be54587400077b6548110026dd3158a31006bd5459310024fe71d8d100f7f2208c510014fc7258041005bd74cc740006bd6450e31004fd75d894303e9c6350d400067c62d9510005ef724c521005df735812103ebf435804301cfc7558b400067e75d8142004ff75d91320067c65d8930006fb50d814313ebf405931001cfc7558c4112eee3258841004ff75d8d2002eef21d891001cfc755913003cfc7358643024ff745903101cfc75d85430067f72d953001cfe75d9132004ff7159131006bf7459130004fd7610d2100cfc7058d2103cff76cca410067d65d0b3103ede6350e4112ebc2019121005ef7258d10006be40d9121004ff7558f41046bc64d0521006f761985302f6ec10d8941004fd72d9131026bf7459231026f66118530006bc644853001cfe7558841046f84058341016bc62d0941006ee65189411dcff7059130006bd641912003dde7310730014fe72593302f6ee71d8941004ff70588410067e3059441067e4214853003cff764c510024bc765094101cfc7558f10006bf64d853000cfd73580310067c7059441
  | 7 => 0x521004ff7258043095fb7059120005ed720c5202d5bd75d0d40007d7324c710196ef20d8930006ee70d8941117cf204cb31006bf6488530006ee60d8941004fd76cc941006f610d8532306ec54d894100cfc764c53003ebc6350f401defa40d81431f5be761913003cff7359330005f77150d31006be545903100cfe76d813201cfe75591210a6ed2058b1030e7e215973103cfe73d89410e6ef21d89310357e7510d102577810d95100057f755813201cfe7558443046f7715874303ef77158643005bc7458d21004ff75d8121026ec2158841005bc744853000df87050540046bf60d0d40005bd740c54000cfe7058f42046bc6490d21014fe7258241004ff7558332147ac6250941004ff7558d10006f9505803101cfe7558b40047b4415054003cff7610d20006bf2119130006ef65d8941026fb7058221004ff7358a4100cfe7058e41004ff735891003e7c3059443004fd76d0910046ef7258b40006bf73d9121014fc72d8d10004fe7648530024fe7610f1003edc630c540005f970d0d30024f876481100ceee4258831024fc768c520015ee7210d20006ef725912119e7e65ccb40046bc64509300b4ff7258910005bf7448510026bc41593100067d650c74003cfc7458743046be6450831006bf64d0531046bc645052103edc63cc94003edf614c931004ff7258e41004ff7650d200067c65985300067d65ccb40014fc76d0d3203cfe76887300dff2204c5100d67e650c740006be1019121014fc7258341006ef65189410067e7059443006bf745911022778654811006d7c7558530006bf6519130004ff7258f40026de3158e4100cfe70d8d21004fd74d89302567f40d951003edc6310d10006ec70d8941024fe76d0a311e4ff725913213df57199110006f751d854203edc6390d40194ff7258d202ffae21d9121004ef7259131006df735913003cfe73d9110006ed53d8941005bf7448730006bd72d9130004fd76d083103ebe4359332026f8105823113efa60d81412b67f70d953000cfc7058e4103cff76cc91000cfe70d854303eec3258a432567f70d95101c6bf101913001cfc75d8542004ff7650b3000dfa7010d10015ee7290d4201cfc75586432567f71d951003dde731053001cfe7558742006bd54586430067f74d9510004fd75d8142006bd64191310067f7558221004ff7558e41025bc71509411067c658c5302aebc31d913000cfe70d894303ebc7650d40016ec624c9300067c7259740004fd75580410f6dd30d8d10024fc71d8910006df6398d10005f7714cb41146bf4259221046ef7258b4100df87050d30004ff70587322aebf32d9130006bf64505300057f755814301cfc7559132014fc7650521005fb7050940016ac62d09410357e7599110016de62cc931014fc7650d4208d7c755854003e7f3259731046b
  | 8 => 0x1cfe7559031004fd76d0931004fd7650b3003edc630c520014ff70d8d20006bf648c530006ef62d0910006df63d0d10026ec2158b10026f66118532004fe7619131046bf751912101cfc75583410be7e6588740004f77158d200067d70597310467c42597400a4fd7648510046bc701912103e7e315973103ddf764cb31006bd5458243044fe74d8132014fc7258343004fd7558331014fe7258331004fd73d8941004fd7558221006bf64d0d30046f74158743046bd7119121006f561185320467f425944300cfe70d8d4100cfe705923101cfe7558e41006ef6250940024fc7650e21004fd760c740006bc42d91300057d759853005d7e75991200067f65191302e67e70597402b67c30d9530004ff7358342014fe7258643014fc7259130026fb1058041004fd7688740024fc76d0d31046bf7119121046be6419120004ff7458d21005f7715893025e7c41d9510006f421d8530024fc7159031006f5611854303cfe73d89100067c7159443146ec625894103e7f4359731015ee72d0521014fc7258d100cfe42118d210067f2059443024fc7610520027b44150531004fd7610d100067c32d9510004ff7558b40026f661185400e5ec7259131044fd73d814303cfd70d9130006df7359132046f74158740045be74cca41004fd7650d1003cfe76d8d21044fe760c74003cfe73d85400ee7c654c530024fe71d8143306ef40d89410ceee52588312e67d7059740024fe71d89430067d7059443004ff75d913003cfc7610d20004fe76d09302567d70d9510005bc7458930087e42148540006ef6318941024fd73d893129ebd42d9120016ec6248510024ff70d8d100e6ee62d8931006ed5258a43024fc715913214d7e7598d410b6ef20d89101f6be50d913000cfd74580412eebc3119121006df630c540006df7358d20006bd75d912103cfc76cc91001cfe75d894001cfe7559110006bd54d91312eeaf6418941306ef71d8941005f970d05102e67d305974000cfe764c510004fd76d0a31014ff764851003cfe7359031024fc7158e4103eec3258b3103cfc7359031005ef7258530006ed54d894100cfe76d8131004ff75d891003ef7315873209d7e75cc740004bf7458d20004ff7158b40006ef63d8941085f9709912001cfc75d8520004fd74d891003ef83058243006df63cc9400463e751912101c7e75d8142025f7758c510006f7619854018d7c7558132006ee601894101cfc7558b100063e4259441024fc71d8d10014fc72d8141004fd7690e21025f671cc910006bf64d8930016ee62d0b31307e441d894115ebc20d912103ede63cc841005bf7458530004fd76d0b30327e44118941025f67110d21024fc7158d2020ddf735913003ef6634c51012ebf3219121004fd75d85320267d2159441014fc72d814301cfc7558a41006bf64d
  | 9 => 0xf7058910004ff7650b310067f65d09302eeae2119121005bf7458132026f461cc52003eef3258b30004ff7058643006bf64d0d3203fd8304c930014fe7259031006be54d9130004fd70d89311f6fa405824301cfe75d81320067d72d953001cfe75586430067f7159740006be42d9130004ff715824316ef710d8540014ec7258d10026bf415884103fd7614c9312eebe3119121006ef53d8941024fd72d9121014fc72d8540065f97098d20024fc76d0b10004ff75580430467e4159443024fe76d0b10027d7734c7100e4ff7258d2101cfc755912103e7f3159443176f621d854203ebc4359331004fd7558b30004ff7559110004fd71d894300cfe73593300067e71d9530006bd6410f10014fd70d9120014fe72593101c6bc3019130025be7150b41024fc76d0e21005bd74cc940046bc64d0d21004ff7358841005bf7448530146ee62d89410067d74d9510046bd7319130006df6350d4101cfe75d8910024fe7690e21006bf64d0510025f67190e410467d4059740004fd755824300cfc70d8543245f5758c510004fd7690f10014fc7258e412b67f20d9530004fd7690d10004ff75d8941024fc71592210267f2159441025be71d0941114ff7158d210067c72d9510025f87648110004ff72593101e4fd7650d3201cfc75d812103cff7690d10014fd70d8d2012ebf7650b41014fe72587300063c6519130006bf75d9130024fc7359331024fc764ca41004ff7558c41006bf75d91212f6ec41d894100df87050d400467d4259441006bf6450521046bc701913003edc638c540026ec2158831004fd7688540006f421d8543004ff7650530006df6390d40006de30d8d41004fd7650831047b761509411f6bd40d91300067c7558031045bc744ca41116f621d8532006be10d91210067d658c740014fe72d9110046be6419132006be40d91320067d65887400467c4059441044ff76d0e21027e4214c521014fc72d8d2000cfc7058743004ff765093121e7c65d0d3001cfe75587300057d75cc5401067e658c7400067f6558930047ac4250d42006be5019121004ff7059031024fd7158f102afbb30d9130006ed50d8941004ff7259331024fc7610e21016ec6288540126fa2058041005ef7250d320057d75991100267f10594411f6bd70d9130146ec32d8941004fd73d812100cfc76cc5100467f43597400067c65d853000cfe7358b3003ede63ccb10046f84058043005f571cc910005f77158132025f47150e310357c7558910005f77158943015ee7210520014fc72d9120004fd76d0d210467e43597400467e4059443026ef7258841024fc7650a310067c4259731025f67110f1003ede634c841014fe72d9120044bc7458d10005f77150831025f671d0e31046be751913003f5d654cb310cedf764cb311f79c30d913002fe42158121
  | 10 => 0x8d1000df8704c510007af62d09410067e325974003efb3058243046be64d083101cfe75d8943014fc7258743046bc731912103e7c73594432b75c73d95302efac2119121004fd75d9131004ff7458b30006dd6318d21006be52d9130024fc7458341046bc64d093000cfe705922103cfe76d8d10004fe76cc52000cfc70d89310067f6550d101b4ff72591200067f6510d102567e30d9510046bc6490d20046dc4358c41005fb7050d300067f6590530046be7219121024fe71d8910026df7358e212b67e20d9530004ff74582212febe21d9121004ff7558f4000df6708c5100057f7558930004fd76d052003edc638c52000cfe70d8520006ed71d894101cfe7558f40006f471591320067e42597310467e425974001c7c7558332004fd7559120004df7358910004fd7558e210067c73d95101c6bf2019130004fd7559331044be76d913001cfc75d8d10024fe71d8d20025dc71cc931006bc6458121005bf745852006d7c7558930004ff7058e21004ff71593300057d7510d102b67e40d9530004fe76d0931066ee62d893003cfe76907300067c73594411ed7c7558143006be5459332004ff72582430067e72d953026df7754c7102e67d2059740006ed52d8941004fd7650d20006bd65d9121004ff7158f420067f755824301cfe75587400ed7c7558131025f67190d100067d654c740004fd75d89102b67d70d953003dde73d0731004fd76cc841004ff735824101cfc7559110006ef624c930005f7715094101cfe75d9130025f47150a41004fc764c9410063f65d91300047f7558031006bf74589102febf641854203e7d325944300ff361481100ee7e654c74001cfe7558743044ff76d0b31006de32d8d100467c74597402577471d95100fedf32d8d21006bf5119130006bc6418d21004ff7258740006df634c510005ed7210d21006ef7258d21044fe74d8d201c6bf501913003e7f3059443004ff7258241025f671d0d31024fc7650f10006be32d9130026dd3158831004ff7650e21046bc72191212b75e30d9530006bf644c5301f6bc70d9130004ff7158d20044fc7458730006bd6450a31006f761cc520014fd74d81421f6bd20d91301c6bf6418d40016ee624ca31044ff76d0b10014fc76cc521174ff7159121004fd72d85430067f6558d1001cfe75d8d100067e2059443006fb705913003e7d31597310067c7558332046dc4358f4100cfc7058732045bc7448540025f47150d3116efa1058341006df638c540006bd545874001cfe7558221004fd7558a43006bf6498530057e421d8121007d5324c51003cfc7358221004ff76505200057d75cc520026fb705804103e7e3259731005f47158d20004fd768c540004ff7158843025bc7650941005fb704c9302febc31d9121004ff7058a4103cfc7610d21014fe72d81410a4f
  | 11 => 0x2efae4118941006ec65d8941006ed51d8941026ef7258b10004fd7559332004fd7558b41045be74cc740014fe7358332006bc21d9130006bc65d9130006ee20d8931004ff735911000cfc70d8941044fd71d8141004ff74583312567e70d951001cfe7558d201e6ec6250d41044ff765073130e7c215973112fb72119121027f01050510004ff75d8d21014fe76d89100079e53191301c6be20191302f7ae41d89411ee7c6550d10046f74158742006bc7458910046be641911003cff7690f10046df7358f42014fc7258f40026fb70582412febe31d91212a6bf31191300067d74d9530017eb604c92027ded754c920046bc6490530006bc644c930044fe76ccb40046bc711913012ebe52191210a6fa20d812130e7c105973100cfc705912129ebf42d91202b67d10d9530025de714c93102dec7258d1003cfe73d89400067c305944103ef4638c5101ceef215884301cfc75d9120006bc51d9130306ec43d894101cfc7559120004fe764854030e7c7159731006ef54d8941024fc7158a31006bf64d0d211f6bc10d9130006ee30d8941006ed43d8941004fe76d0d10046bf6150941004fd764c91003ef431587322b67f30d9530024fc769052000cfc7058c4101cfe75d8d20026bf7459310014fe725913000cfe76d812100cec764c92000cfe7058831005ef72581310067e71597401b6ef20d8940004fd7650730026bd415884101cfe75d913101cfe75d8530004fd75d8930046be70191301476d75189410467f4159443025be715094101cfc75d8d410067f7558d10024fe764cb10005bf745813103cfc7358742004fd70d91321ddbd7490d40004fd74d8131004ff725833115ebe72d91211c79e3019130006bc7458d2103ebd435824303ef83058043004ff7558743004fc7650530026f4634c710044fe768c74003cfe76d0b30004ff75593300057f7558121006bf6490d102ffac21d91210dcff7058d10004ff7558b1001cfc7558740025f47150b31005ef7258d41025f47150910016ec6288530044fc7458b1001cfe75d814101cfe75d8d40006de53d8d41004fe76d05302e67f7059740004ff7458332014fe72d913024df7715891003cff70d9130004ff7558b30006be54d9132006bf5219130024fe71d8d40004fd75d8d42006bd545804312ebe3219121014fc7458f420067f7259441006be50d9121006ef62d0931014fe76d05212be7f31d953003cff7610d10004ff7358b400067c6558d10006bf6490d21006bf645051000df4708c510284fe7618d200067f654c93000cfd71d8910016de624cb310067c2059443004ff75d8d4108d7e7518d40147ac62d094101cfc7558b41004fd7558a31004fc765091015ebf32d9121044fe74d8530004fd76d0730004ff75d9120006bc644c521004ff7458e2103e7e7359443005bc745
  | 12 => 0xf65485101c6bf3019130144fd765052100df8704c53003fcc3250d32146ec52d8941046fb4058342004ff735913101cfc7558f40006bf644c521006be6219130006bd53d9130006bf7459132004fc76485402eebc5119121086ee62d8940014fc72582410dff0704c5100067f65d8530004ff7650f10015ec724c521004ff75d8d40004fd755884103e7d7359731024fe71d89400067e105944303fcf724cb311c4be76d0d40005df735891003ef4634c5100467f4259441006be54d9121006be54d8141004fe76cc91015ebc72d91210067c62d953003edc63cc521044fe76d9131014fe72d8d400c5f6768c51003e7e4359443006bf6490520007f23148110024fc7158b4300cfe70d8941185ed7298d200067f6518530006bf6450d31024ff7610730004fd70d854200cfe7650510047b761d094103e7d3059443024fc760c520006ec50d894103cfd71d8931004ff7558841005f571d0e310079c6350d40217e421d0d2100dfa7010d20005fb704851018d7e75191321c6bd101913003ddc7350731004ff75d8d10005ed72cc521024fe7650f10006bf64581212eebc2119121146ee7618941006df634c5211f4bf7650f4001cfe75d893100cfd72d8d20046be64d0e31004fd755913103ede6318d400e6f62158732005bf74589302eebc1019121004fd7648730046ec4258b40145ee7298d4112cbf7650b41024fc7158b4000df8704c93000cfe7059331047b84050940006ec62d8141147e421591210057d75991201dfb87050d40044ff7650521024fc71591200067c6599130006bd545903103fd761cc931006bf6418d21025f67190d4103eec32588310267f7159441016ee6250831004fd76d0b10145bd72d0941004fe7650930024fc7158b3000cfe70588430467d4159740004ff7358b41004fd71d814203eec764c92000cfe7158b1003cfc7458343005bc7458d20005f7714c931006ee53d8941004ff75d8142047af7250b41014fc7258643004ff725834101cfe7558241017e661d0a21006ef72591201a5ed7299120004ff75d8143004ff75d8943005f97010530014fe7258e41004ff7159130006ef624c931014ff7650a41024ff72588412b67c20d9530005f77158d20004fd75d8d100067f65d0530005bc7458520004ff7558e21006bc64d812100cfe7059332044fc76d0d100067f2059441004fd764ca41004ff7059332004fd7558740004fe764c940024fc7650d41005f77158d42016ee61d0a21046f4415844301cfc75d85401d67c6510d100067c21597401f6bf70d9130006bf745912003cfc7690d21006ec65189410067f7359441005bf7448540044bc7458d21006be72d91302eebe21191210067e62d9530004ff75d8543024fe71d91322e67c1059740005bd740c74003edc6350d4201cfc75d8142006ef7259131
  | 13 => 0x8931116ef2158b3100cfc7058f41004ff7158342006bf64991300079f6350d40024fc7159231014fe7258740005fb704c5100e6ec20d8931006bc64d8530006f56118540046bf7219121004fd75d81210047f7558221014fc7358332004fd7558743045be74cc940046bd7519121015ee74d0a2101cfc75d9132024fc7690f10006bd5319121024ff70d89100057d7518d40004fd7558d1000cfc7159310005f571d0d3100efb6148110004ff7159332044ff76d0b302b67d30d9530004fd73d8520005ef7250521006bc6219130014fe72587431f6bf40d91300267e415944115fb721d9121004ff745873203ede634ca41024ff768874000cfc70587420057d7518d420073c651913018e7e654c8410057d75cc740004fe7610d21004fd74d8d1000cfe7458b40047af7250941006bf64d8121004fd73d814200cfc70d8d41004ff7358041006ef6288530044ff7650e31006bd54d9130006ec53d89412567c71d9510006bc6418530006f7610c52001cfe75591300047f755913015ebe52d91212b77830d953000dbe70d0d400e5dd72cc9310067f65505300f6fa3058231177e421991210067e205944103cfe73d8141044fc76d09302eeac21191212b67e10d953000cbc7650d40006be4059231004ff755834201cfc755874301cfe75d8d4201cfc75d8141025f7764c710004fd7650b10006bd65d9130044fe74d8930026fb1058221004ff7158b43004fd71d8d42004ff765093000cff72d8d20004ff7650d21026fb1058031005ed72d0521014fc7259110004fd7558332006f77158d10005bd749853015ebd72d9121006bd64d0a31026f4610c520024fc7158221004ff75d81312f7ad64d0a21075fb7058d20004ff755913105d7e7510d201c6fa2058043005bc7458532004fd76ccb4000cfe7159310014fc7259330007d7324c510005dc73581210467d4159443004fd764cb40004fe7650530005ef7250e211367c65105300067d715974001cfc7558d10004fd76d0930026fb105824100cfe7059121006f561185300057d7599130024fe76d0831005bd7498d21006df6398d400467e4059441006bf72d913001cfc7558e41005fb7050d400067f65591300067c65d9130006f771591100067f65d911001cfc75d894301cfc7558b301dedf3058f40004ff7259130025f47150941016ec62d0910014fe76cc521044ff7650d301c6bc2019130046bc4258841004fd7690520005ed7290d42005bc745853015ebd20d9121004fd70d8532004fd71d814303ede6318d21004ff75d9110004ff764c94003e7c3159443024fc7650b10044fc7458831006ef62cc91000cfc74d8141046bc64d0530024fd73d8131097e42148740026bc4159031006f410d853203e7f3259443004ff7258743014fe72d8131006bc42d911015ebe32d91210067
  | 14 => 0x6dd53d8d21046ef425884316df77159110046dc4358f42004df7359110046fb7058343004ff7458f1026df5754c710006bd6419130004fd7610e21176ef2158b41004ff7650831014fe72d8d20014fc72587302f6ef10d8941006bd54d91320057d75d8142006df6398d20004ff764c520044fd71d894115ebd71d9121004ff75583430267f315944101cfe75580410e7cf204c931006be54d85400467f4059740004ff7259110024fc7158343004fd75d8540004fd7688530004fd75d912003ebd4358043046bc645053000dfa7010530006bf53d9130046bf61d094103ebe6350d40006f76198543006ef725922103e7c3259731004ff745803103cfd74d89431c6bd3019130046be7319130006ec72591102febc51d9121045bc7448740024fc71588410067c65585302febf649854203cfc735891003e7f73597310073f65d9130004fd7559310024ff760c740004ff70591322f6ee51d8941044fd72d8142004fd73d8940004ff745891001cfc75d8d4024cff715891012ebe4258841004fd7558843006dd6350e411f4fe761913003e7f4359443024fc7650d31014fc7259310046be711913007d7e7510730004ff764c841004fd73d81412f6ef74d894103eef7258843004fe76d09100267d105944105d7c7558520004ff76487402febc21d91210067c705944301cfe7558b10004ff70593311ceef2058843004ff7558243004ff75d8d420067c65d91102febc10d91211c7b83019130015ee72d0d320a6fa10d812101cfc7558831014fe76505210067e70594411c6be10191300067f6550910016bc6250b4100cfd74d8940006be42d9110014ec7259110024fc76ccb10005f97010d10046bf7319130025f67110d1001cfe75593320067f21d951001cfe755933002eec42d891000cfe7058a31026df7358e4100cfc7059132024fe76d8520006bf6499120004fe7610d100057d7510730004ff7558a43007cc634c920014fd70d85202567c40d951000cfc7358b300057f7558d2000cfc7158b10005bd74ccb40007f1314811001cfc7559131046bf7019130004fd71d913003cfc73593101ad7e7518d4200df87048510024fe71d9110006bd64191100e6dd3258e2103cfc76cc520015ec7250d42006bd6419121046be6419121007e93248110044fc76d0910006bf71d91302f7ae64d0a21046be7319121026be4159231065ec725853005d7c7558d202be7c31d9530006bd545933203efb3058043014fe76d0d32006f761905402567f10d95100467d7459740006ed5258831006be545922101cfc755822100feb7248110004fd76509102be7f32d9530006bd6450b100067c7558910004ff75d85300ad7e75cc521005bf7458d21006f451d8542004fd75d8520046be6410f102be7e43d9530156bd40d91100ae7c654851001cfc75d
  | 15 => 0xc71191210067f658c53001cfe7559331025f4714ca31024fd70d911003ebc63d0d40235f7754c5100e6df3258e210067f65d0d30187ea104c920307e571d0a21066ee32d8930006df53d8d40006bc6488530004ff7059221004ff72586431ee7c6550d300067f7159443007cd32cc52001cfe7558b30006bd6419132026ee2158a410067e7159443006bd5019121047b44150d4101cfe75d9110014ff764ca31004fd71d893000cfe7059132004fd76d0b31014fc764c521044fc7458d20006ed70d89411dddd7399130014fe72d91311feef2058a4300cfc70d9132006bc73d9121195ef7258d20005bf7458d200067f65991100467e425944300cfe7058743006ef7259110004ff75587320047f755891001c7c755824300cfc7650d30006bf5319121004ff7058a31006ef7258910045bf725094100cfc70d8532046bc64d05101e5ec7258543004fd75580310dcfd764c51001cfc75d85300067c655893000cfe7058e210047f7558241014fc72d913000cfe7058f411ae7e6550b312aebc32d913001cfe7559221024fe7610e2103cff76cc74001cfe755912003cfc7690d20006bf6490d20005f9701052003cfe76d8d42014fe76d8931007eb704c920006ef6250941004ff7458d10005bd74cc84101cfc755834301cfc755824103cfc7358a41004ff75d89401e6ee32d894303edc6390d41006be65d91300467c4159740026f46190540005f97090d40024fc764c93103cfd72d913200cfe7058732016dc764c9310267f4159441004fe76cc5400067f65d8d101ae7c65509100067c42d9530004ef7259110006df6350d42046bc6450d31014fe72d8d41004fe7690d2001cfe75583312b67c70d953028edd32d8d20024fe7650e2112fe42119121016dc624cb3103efb7058043027d43150531024fc7158332045bf7650b41004fe764c540016ec6250941004fd76d0530006bc60191210467e74594430467c74594411f6bc40582430057d7510e21015ee72cc5202a6bc3119130006bc60d9121004fd7610f10146ef21d8941004fd7558b10027d7734c510004fd755903103ebc43590310067c3259740014fe72d8d10014fe7258d100def710587301f6bd50d9130006df735911000cfe7158f100067c205944101cfc755884101cfe7558f42006dc32d8d1001cfc75d8131006dc30d8d41014fc7258f10007b77150941024fe71d893003edc63cc5100467d4059443044fe76d9121276f621d8520006bd71d91300067d72d9510306ec40d8941006f77159121004ff75592210067f65d893002eee62d891001cfc75d8910016f87648110004f77159132006bf6410530004ff7559332024fc715883100cfe7058a43006bc54d913000cfc7458b402a6bf32191300067f658853001cfe7558831006dd6318d41014fc72d911030e7c4159731
  | 16 => 0x8231004ff7650730004ff75591210067c7558d1000cfe705903100cfc7059031025f87148110024fc7158a41026f63158031004ff7458831004ff7558742026ef7258a31025f4715083119e7e65cc84101c7c75580312b67f73d95300067e42d9530024ff705803100cfe7058a41045be740c54006d7e7510530015ee7210d2125f7b10d9510016ec62d0931004ff7558d20026fb7058031006f761505401debd4059330006bd54d9121004fc764c520024dc764c93101cfc7558a31146bd42592210067d7059441024fd72d8d21004fd7648740026be41592210067c659911003ddf724c931024fe7158e2100cfc7058e2100cfc70d854203dde73d0531116ef2058b31015ee7290e21006df7358d1001cfe7558a310057d7510530004ff7158a43024fe76d0e21005f57110d21044fe74d8131006ee75d8941004fd7558231184fd7698d20005bc7458131046bc64d0d30005bf7448740044fd72d85420467e435944100cfe705844301cfc7558d2000cfe76cc51001cfc75d89300bd7e7510e21006bd64d0b1003cfd735933015ebf42d9121005f7714c84112ebc321912103ef83058031004ff7559120004ff71583320067e725944103e7e325944303cfe73d913001cfc75580432567c30d95100067c65d8d10014fc72d8d4000cfe7690d40044fc745822101cfe7558e21006bd53d9121004ff764ca41006bf645853000cfc7058b43025fa71481101cfe42110d21004ff75590310267d4159441006bc72d9130047ac4250a4101cfe75d8d21014fe7258043006f7715891001cfe75d853202dec72591101e7e42150d212f6ef621854201cfc75592210ad7e7598d21006bc40d9131006bc54d9121006f56118520004fd7650f10025f4714cb41044fc7458e2100cfc70d8d10015ec7250521026fb10582310267e105944112ebd2019121016fa6248110004fd76ccb10005f77159132047bb60d0d40004fe7610530005bf744c841014fd71d81210067f74d95301f6bf6490d40014fd73d813200dec704c92000cfc73587301c6be5019130014fe76d89432b67d40d95300067c745973103fd8304c530044fc74589100067f659853003cfc7359110004fd71d913201cfe7558b412bf7b30d9530044ff76d0831024fd70d8910004fd70d9121007bb7050d4000cf4764c510024fc764cb10006bd52d913000dbe7050d40024fe7159031024fc7158a43006ef725913200dfa7090d40046fb40583430b6ed20d8910006bf6499121005fb704c530014fc725874003cfd72d85320057d7510d200267c7159441006bc64d8930004ff7558443006bd51d9130006bf7459121004fe76d0520007f3704c510026dc3158e212cdbf7550d40286df30d8d20046bc7219130004fd75d8d4003e7d31594432b75c30d9530046bf6050d400e6ec6258931046b
  | 17 => 0x296bd40d9120004ff7359221006df7358910004fd72d911003cfc7358841026de3158e210dedf3058f10046ef4258b41004fd75d8940007ae54d8941006ec73d89412febe71d9121006bd5459221006bd54d8540006fb7059110006ef50d894100cfe70588412aebe53d91300057f75589100047d75d81420b6fa20582212577610d951001cfe7559132005f7714ca31004ff75d9131005ef72591310c6fa205803101cfc7558b3115eee4258a41016ec624c93103f9c4350d31015ef734c920006bf7458d10006bf7458d2103ede6318d4103edf61cc9310467f7459740004fd76cca4103cfd70d8530006bf53d91210067c21594430067f65d09102e67e30597400067f655911003cdc7358910006f551d8532015ee7290d20006fb7058910006bd50d9121025f67110e210ae7c65485300067c75582410e7cc624c9310467c4359740156fa205824103cfc76d053101cfc75d8941004fd755834215ebc32d9121006bf645893003edc6350d4000cfe76d8142004fe76d0d21024fc7650941014fe72d85401e6ee42d8943005f57110f100467d4359740046bd711913001cfc75d8143005ef72591100067d71d953003cfe73d8542026be415931003cfc7359221024ff7690730004fd75d8530004fd75d8d21004fd72d8d10004ff7058f42044fe74d852000cfc7650510046bc6490d10004ff725803100cfe70d913210ef710d8530006df6310d10046be6450b10186fa60d81320067c1059443006bf54d9130006f47158d20066ec21d8930004ff764c740046df4358f40026f4615054000dfa7010520044fc76d053001c7c755913003eec3258b30006bf6450d30004fd75d81412b67d20d9530046fb4058341014fe76d8941004fe7690d10005df7350731004ff735874201cfe75d9121006dd634cb10006ed62d0b31006ec30d8941004fd74d853201cfc75589100c6fa4058031004fd72d853003cfc7358b40016ec62cc91012ebd5219121156fa40582412cdbd7550d40024fc7358b31005f47158943044ff76d0d21004fd71d81322aebe73d9130044fe76d91200067f755913003e7e30597310067c7159740144ff72591211f6be30d9130006be651912100cfc7058b41004fd7558f420473d6550f402a7bb3019130006ec6018941006bc64985300067e7359740007d7714c931004ff764cb41046bc64505100e6ec42d893103e7d43597312567f20d95100067e32d95300067f654c530024fe71582210473e6550f40005df735911015fe421d9121006ef62885401e6ec21d894313cff705911003cfc7358b10006ec60d894103ebe4359330004fd73d8540006bc648c530024fe7690f100defa30d81310e5ec72581310defa10d8131006bd5119121026f810580410067d65cc8411c79c3019130026f6768c510026f66118543004ff745
  | 18 => 0xe40d8941046be76d0d40214ff7359132024fd7158b1003fcf724c9310267e215944103e7e7359731007f0714811000dfa708c53031dbd75d094103cfe73d9120145ec7258141046f84058342004fd755873003cfc735804128edf32d8d200067f7459731006bd51d912106e7e76d95300e6ee52d8931005df7358141004fd70d8d42006ed624ca31007eb6248110024fc7690e21024ff72d9121154fe761911000cfe70d8d42044fe74d8d21024fd70d8d10006bd6450831006be7619121004fd755834113efa40d8141004ff7058d2103ddc735053103e7d7359443004fd74d8d21044fc76d0d21006be53191210067c6559110004fe76cc9401be7c65d091000dec764c920006df630c520006be54d9120006ef73d8941044fc764cb410067e74d9530024fe71d912000cfe70d91311a6f860581420057d75191210067c21d95302e67c70597400047f7558d10006ec6258141004ff70587420067f654c9100067f65cc510045be74ccb400467f435944100dbc7050d4025e7e41d95102567e20d9510006bc52d9130006dd634c84103ebc43593322b67c10d9530046f4415874003efb305803100cfc705913101cfc7558843014fc72d854300cfc7650540044fc7458b31306ed76d0a21006f721d8543006ef625814103ede63cca4103ef731587301c6bd201913003ef6315833101cfc7558342015ec7250d321f6bc50d9130016be6250b41004fe7610520006ed6250831024fc765083101cfe7558a41006be30191210067c74d9510006ef52d8941006bf6450d3203cff7610f10024fc71591300057d751854201cfe7558732024fe71d8d420067f705973101c7e76d9510004fd74d812116cff7159110024fd74d89410067c7558221286dd30d8d2003eef7258b310defa60d8131005df73585200063f6519130005dd73d0731014fc72d813103ef8305833103eef7258a43006bc4059231156bf40d91101a6fa60d8142014ee76d8941046df7358f4100df4764c510006df6350d400e6ee32d893100dfa70cc510004fc76509311be7e65d0b31004ef72591212b67d73d9530024fc7458f4100cfe70d9121006bc644c530024ff70d9110046bc4058043046bc6410d2103ede6318d10004fd764cb41004fd7559231187e8704c920044fd73d8943044ff76d0d20004ff764cb1001cfc75d8940004fd74d8520025f4714c931046bc641052015ebf71d9121006be3219130004ff7458a3100cfc7058a31046bc6450d21024fe76d0d3103ef53158031004fd7559110006ef51d89412567e40d9510006f721d8530055fb70585202f7e671d0a21004ff755931003e7c4359731007ae541894100cfe70d893103cff7690d20024fc7158f42004fd76cc94000cfe705913120efa305834303cff7690e2100cfe7058c41007d4634c510006ef7258d10
  | 19 => 0x5200067e73d9510004ff7058b41004ff7058b430357e75cc5100467c4359441024ff7158b10004fd74d853003ede76cc931046be64d073100cfc76d05100067f65d051002eec62589100267d3159441016f862481100467f405944303cff7610d21006de53d8d21016dc624c931007b47150941006bd70d9121004fd71d894000dfa700c54000cfe70d9110005bf7458121005dc7358910004ff7158f4000cfe7058d2100cfc7648510004fd7650d21004ff7458d20005ef7258141005f97010d200067d65487400067c7259441006bc6519130005bc7458931026ef7258831024fc71593300263d41594410ae7e6548740044fe76d913212eef20588410067f70594410467e4259441004ff7559132004fd72d8540006bc6519121004ff7259031006df7359131004ff755933118e7c654c910014fc72d913101cfe7558d10014fe7259131044fe74d893103ef5315833100cfc71d81210067d73d9510005fb7050510004fd74d8132014fc7358732306ed64d0a210267e315944101cfe75d894111e7c65cc51000cff72d9120006dc7359110004fd73d91100267c3159441026ec2158a41006bc5119130006ef624c941004fd760c540006dd6318d201c6bc10191300467d7459443014fe7258c41044fc7458031046ef4258b43014fc725823103cfc735912003cfe73d91212567d10d951001cfc7558742115ec72507310067d654c841004ff74587300067d745973112ebc5219121004ff75d8930004fd75586431f6be4058243026bc41592212f6ee41d89410067d75d814203cff7690d210057d75cc5210ddf57198d1000cfc7059332005ef7250731005ed72d0d321c5be76d0d4000cfe7648510004ff7359120006bf6448530004ff705884303cfc7358740327e74118941024fe76d8540046ef7258b43046f44158743004fd75d8543006f77158d20024fc7458b411b5ef7259120004fd7559330005ed7298d41005f57190f10046fb4058041025dc714cb31006de30d8d21004fd74d8d202567f30d9510005dd731073003cdc735911003cff7610e2103cfc7458b43007f3714811001cfe75588432aebc53d9130004fd75d913011e7f7159731307e741d8941004fd755824103eef325884303e7c3159731004fd75584430067f651911000cfc7058831004fe7690530045bf75d09410a6f86058121006bc501912103efb70582430047f75583320467c4259441046be7519121004ff7458b31006be65d9121006bc7458d20044fe76ccb41004fd7610d2003edc634c5210057f7559130006be5459110044fc74583320067f755833215cfe7619121006bd64d0e31086ee42d894000cfd72d8520006be52191300467d405944115ebd52d91211ae7c6550930024fe76ccb10006bd64d07310467e7459441146f621587422f6ef6299121006e
  | 20 => 0x46bd70191300f4fe7618d100067f659913000cfe76d051000cfc764c930085ec725854001cfe75d85430067f7559110044fc764cb4003eef3258a43004fd7558b43006fb7058d20004fd72d81312e67f105974000cfd73d8930026df3158a31004fd7690d212ddbf7550f40005f47158d420057f7558d10006be53d91210a6ef2058b10004ff75d81321f6be70d9130086ec21d89400067d7259443176ef61189410067f72597402657e76d9510146ec20d894100dfa700c52003ede6318d42115f77158d21066ec62589300067e3259441046be64d0b102f7af41d0a21004ff7259231006bf21d9130014fe7359332004ff7558643004ff7558031004ff715913202eec32d89100dedd3058f10004fd755891000df4704c710006be5459231004fd764c84103ebe4359331016ee6250a41044fc764874003e7c3259443046bd721912103cff764c521014fe72d85300057d7598d41044fc7458d1001cfe7558342026dc3158f1000df6704c710045bc744c84103e7f7359443006df638c52003ebf745933001cfc75d91300067c4059731004fd7558e41006be51d9130006dd63ccb10024fc764c84103ede6390e41014fe72582430f6fa20582310479f7350d40044ff76d0f10026ef7258a410047f7559110006ed6250a41024fc76d0f10006f561185420067f7558241026f810582411f6bf10d9130006bd6490f10186fa30d8132026f7608c510014fe7259110235f5754c510004fd75d8d4117e7e65d073102fea3248110014fe7258031014fc72d8d411e6ee62d8943004fd76cc520004fd75d8941004ff7058443045be74cc841014fe725834102dec725051003cfe7610730146ef20d8941004fd73d854201cfe75d8520146ee74d894100cfc70d8d4212ebd2119121005f970cc51001cfe7558d21006df6390d4100cfc7058a43006ed73d8941006bd6450731046bc6410d20006dc53d8d4001cfc75593302f6ec51d8941005ef725051000777658c510016be62d0941007af6250941046bf73191210079d53d9130004ff764c9410057f7558d4001cfc7558732006be40d9131004fd75d854200cfc70593312f6ef64d0a21006ef62d8141046ef4258841024fc7159332006bf6499131016ec624c941006bf6410d210067c65191102fdbf7450a4101cfe75d8d4100dbc7650d40075ec7250730004fe76885300057d7510520006bd54d8141046f771587420057d7519131006bc5319121006bf54d912103efb3058331006bc21191300067e7259740014fd7458b40024fe71d814230e7e71597312eeef6418941006be30d9121006bd75d9130005ef725073003edc63d0d10044fe74d8121004ff7558b3101cfe7558043006ee20d89412567c20d95100067d735944100cfc7650940005bf74585320357e7598d10227f1514811005d7e751
  | 21 => 0x5f02f00206d00000436b01000001400101801e00802b07233f00000200003300702620e0025020010ad00a00201301800300000300201700100600901c05c06c01d00600810509803902300100300d05300e00905503601201e00431f03108c02705000700000000206201303e0140032370098090290c00770dc00c99900004700e0260000829f701f01800201000401000101f00d00000d0102ea00a0410010ed617003001ae200200100d00600502a02401c00200073e06701200900300f04a02401e0140000b001400000794f00800003000103f95c0350010ab44802f00202200f0420030081b997800f03a00b00442800400100600500000101200009f7fc0000020052fe00602100100e02400600400200703400300100302907a0d333702d0520000000010f000e00000501d1720010010007e10fb07702200700100002500001100400001400d01b0053230010000000bb00200000102b01700e0555852a800044903d0bc09800b00000600908d00b080b6f00000700200000100500100000300806c009ace33c0030000f70000090030095e000c00603700000000000f00c0120350ad1fd01800700b03202900a0020740030034b3e0210392500000000b0050a603400000700400400101e02e00560b00a00916701eb6698300500600122400e000052002a5703100d00087153400000100503100f01600c02400500419101b001000b0200000000000600000102400200007e00705000302a8a80030000d60005140070290020af0080010b600400002f05102701775100600200a00705e05d00202d0072d500400509b039020017000000009afe19501d01d00000900200b04000230027100105a03504a00001d02e00300e33301c00500100500100205501900000000400d00008700200101500302e00001500902c00c00100000500200302e0540040040cc00b0070190250034ff00c0000410160100020050060460d301700101b00000c001dc600100700a00504c0141a54da0020040010022015090087c000109700000900501a01d00003f0031d700a00900100103100404801819c05702500000f5fe00c0030000010ae01a00201200000000100400501600b00008501f00c042003021006f76198520006ed624c841044fc76d0931044fc76d0520006be601912105d7e7518d20004fd70d894103cff76ccb412f5ed71d0a21024fd72d8121024ff768873030e7f1059731014fe7258f400467c4059740006bd53191300067c6519130004fd768c74002fea5248110024fc768c540004fd76ccb41004ff7650d10006bc50d9121026f661185200067f2159731006be75d91212eebe5119121004fd7558d2017e7c65d05100073d7519121006bf65d91300067d6550b31306ef41d8941006bf645093003cfc73583420467c4159443
  | 22 => 0x13401100004300000000b00f0ca0030de13500300a0150010b000f00201c00f01100d00200802600b01300107500a00e00300204807f00000d0451220d100b00f00a0000f900900004203600100000000200400200c00d01400a00901c00000402400000502d26f02501000f00100400001c02500200100700301202500000100000200801f01f03d1fc00002900203450500201a00200100300202103900000200200300015a27000e00000a00000200000f00d0020060020005610793e600008101e00c0a601300503204802100400001302d01b00905100200704c81900a12352901200103d01800200200365400100002104008b22002000700300a03002c00601304300300500245502402503300010a008002544001ae700e3271a600000201d00601f0000010070600eb07528b00003200704303601c03d00009901c0170000000000078b200500000103615f0000940300035ab713b4e00200804b00302801b00000900101100201f01700001301700300402e06d01806c00000006c00101000401800300700b00100200401f33b00601000002d5ec03f00000c00007e00004800300501500004302701800f00300100000a15a00005500601400000300f03d0c400e00000501e00f02600c03203d02200900200000200507501007000200800239300e01000c07e00081909e00502001300201b0060d102f00105400501201116a04801b0020001bc13f34400100c00000600800601a0010bd0004df0301221540000004e000209307f02405e0027ce01301000d00808e0390940180a03fe0060000050010a401b00c00408f0000030000130000430013e400102f00607d02a00000f00000002c00200e10100b19001601d00d00a0170aa00118d00005f00100316700703201704600100002e00301d01500300000700a0ec0178f400b05355200a0025e900300e0680b402902001700602103903201a00600500e00600200800000015401609f0040960060023d100100200700000500f00b0260cc00904318e1090690120155aa01b00d00c14900500320c05f00500b00700005b00900000f02a01500301a0060720020000060010a80405fc0010041be0bc00f01700100100000000a383000239008001bb700001406104f01e02551000300703f01001f06d00100000200101300200000000701d01202842d02f0620b009e00c2e202100300f00300d9980090001d800800039200100e00a0ba00696301304a00602400001901d00801d03101300200000203e02a50302c00301305e05a06a04100906800508c315ca000502e00000000201300b02b0059e958d1ff00800000011505d07801028e00000505503800303400200800f73604700d04900015e24f0150670
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa9e8314364484018d8ea312c0a08032b193724c5210067210cec90a6000c3c651d1214c0014db04182ca2080e1f21571d8d400061e32ee8b1a20008bf845d943480bf56d02286c8908028fe1173d951001c3f43eeab1a2007a5e831c16510c01998e6392c8880238ba0a42594412543fc3ecb98a20028ee87dc9644400956d03b22829800317197735891000672396e2b226200c6f65dc9414400187ee83aac1218022f61f531912109d1ec26e6b2e8000ad4864c931440010fd0fb2ac298156a7a0c21d91302bc3f438eab066400c3d655d332d00019cee438ac6900032b19172cc5210043f438eab226000ab484584614c8c1958c9b9282908031b1d77258d1000667b98e4b1a200387e85dc1628c4070f90abb284880032b1cb64505100047bc3ac230a805fe3651d4764484018b8ca39ac8880028f61271d95300451f420e0b288608c3c645d6644800147d0a180c8908031b197725053025f3210eca90a2000dc4211cd6048401878cbba2c4880230f1917510d200445e420eca0a60008bd87143644840717f0eaa6c8900022fa1c30d91210063b32ee2a166200c3e7519263484010fd0e10acba00021fa1c65591300247c432e020a40008be861d1214c0f5d4843328c8908032bd93725853000477c12eab22200387f875d760508010ff0abb0629000a3b2097650d1000556412c832220048f4815d942cc0018e8ebb8ac6900021f6177650d100062ebaec798a4200a79800856510c01b48423a2c69080e1fa1b75589100062fb28e6b122007cd4635c443440070f90abb664880021fe15760c5400064fb26e6b024200c5d731cf654400156b0810ec2a18129da0430594410445f43ea63226007cd8635c0434400f4bd0610aca218030f5d475d91210061fb2ee8b0a600087f87d94414c00195cedb1684a08023be1d65189410061f3aec820a6000e576518d314400187eca3a2c4880032b19372585300043ec2ee0b146200c9c741cd62440015ab02186c6a08021fa1f20594430063632ee4b1a200087d85dd932440011df04baac890802a7a0e65191210043ec3864b2e800087e87195624c00187eca3a2428800e1fa1776509100043ec3e40b288200c9f739cf64484af0fd0e3aac1218021f6177059231006363aec4b028204ce4615c83148097c6883b2a82880029ea0021594431f45f43ea7b22600387c855da214c00717f0eaa6c8988029760e425973100556c26a5b12820087d85dc162d040117b0e10ec898156a7a0c75d913000657ba0e4b22626fe1d83197644c0011bf06baac8980021fe1576105302b43e436eab0a6000acc8258c634410547f08b82ca21802b960430d894100657ba0e4b1a20038ef8754b62504011ef0eb08c2990028f61220594410045fc3ac83226204cd47158d32104071bf0ea9ec6a08123721d634c841
  | 1 => 0xf0abb2869000335dcc7158d2001c5e43aa8b222000c3f75d91624c00187aebaa6c8980022fe117558d2101c3f43eeab222008c3e74597321040956d03202c9188028f61070597310061f3aec998a42018be86dd121500091b90eb1a658800e1fa17705884100537410e0b2886048bc87551640c4bbd484232662908021fe1975cc7400064fba0e6b22200087d85dd9424c00f93cc6ba6652084e8f61071597400061e328e8b1260088bc845d563440014bb06202cb988028fe1570d912100637b2ee4b2220028de87d8d325000117d0e10ec8980123d20576508312b53d40043b2a6000a3d84087654c001958e9b92c6880031d19771509100045f43ec8b1a42048bc845db414c0010ff0abb68298002ab61050d894103e2e31aeb31a4200aaf84594625040156b02280c8908021fe1d65cc7400063a328e2b126000c5d75d8e635040187eea322c49800a3b2097558d100065a3a6e2b1a400387e87dd5644c0018deebb12c0a080a3b209755911001c3f43eeab122000a3e8498b654c0018d8e5b2a82880021f61770588410043ec2ee0b16866ac9f73191614c00159b04186c6909d3a908464581210061e3aee8b122074ab5819806448401938c839ac0908031b597725073100667b98e4b22200087f855c3625040153b08186c6a08023de1d611852003c77c32e521c4200c3d75d90414c00117d0e32242980123d2057558d200043ec3864b288200cb7741c5644c80153b06286c890803c908575191210056ac1843b0a8600a6d8598f625040153b07328c890803391cb7158d100061f32ee890e8000aad820c364484010fb0bbb284881b7870c0651913000572c08a1b128200a75811c16510c11878c8ba882980030f5d754d91210043f43864b28820387c855da215000147b0a186c8908030f1d77458d1001c3f42ee2b1e80008fb805d56348401998e7b92c4880021fe157650d1025c3f438eab0442028f4865c4434840f17908bb686908022fa1f645812125d3cc00e5b2a205fa3f8190965104070f90ab86c899002ab61030d89410053742861b12820087d85dd9214c0010ff0abb086880028f21570d9121006563a6e4b12200087d87d94414c0018b8cbb9ac8880028f61262d95300047743861b128200cac74d8921440018d8ebb92c8880030f5d464cc5210051ec2cc5b226000c7865dc1434c07d17f08bb082980023de1d61185300061ebaec820a40038bf87553644c00187aea3aec8980029761430d8d210045ec3ea7b22605dcac629db425040936d0fb8a84a080369084745812112d57410a63224203c3c7595164440010ff0abb664880122f21d54593100043fc2aed20a6000c3e765d464484031d90cb90869017e2fe1176487400051ec2cc43226008a3e840856510c1147d05212ca208032b1d37258d210063ab2ee29908200
  | 2 => 0xf205944103e6c31ae018a800387e85dd9214c0031d90cb9662900029760c21d953003c6e41aeab222000c3c65dd1614c00187aebb24c690803271d373589100061fbaee8b1a2070a3e86194644c0010ff0ab86c8988032719373581210053b408e0b288600a6e821c165104071bf0ea9ec690803175d76398d2101476412eab226200a3e859cf64484095cd03b124288002ab61353d89410052ec1840b2e620387e85dd9414c00f1b906baac488003390877650d210052f418e0b28820087d8710b654c00147d0a216c89800e1fa1f75582410045ec26ec90a60008bd8714064484018b8ebb9ac88800e1fa17764c9100062fb28e6b222060aae84143625040555d05b2284980228fa1071594430245e43ac8a1462088be84dd9214c0c1c5ec53a8c8908031b1c86558d1000672108ec90a60008df8758c63440018d8cbb92c2980021fe1576905200061e3a8e8b1a4000c9f741cd62440011ef02bb28690802ab60a101912100c7a432e321a2000c3f65dd162440014dd04182ca208029d60430594412543e436eab1220088be87dd1624400117f08bb4429801e37a1f73589103cd5bc0aca322420087e87c8165cc401c3ea729ec8908222fa1f52191300061fb2ee890a60088be87d4c644847547b08382ca2197eada0430d912100637b2ee4b1a2038aba80084644c00187ecaba4c2980228fa1273597400043ec3e40b2e620087d85dc16210c7d5750010ec8980222f2117610d210043f43ecab1a200387c855d8414c011179083b242a0002a760f51191300445f438a23226008a3c845c16510c018deebb92c8880021fa1c7558d1012d57416a23224200a6d821c165104010fd0e32ac488002a72116318d1001556412c8a16200387e86dd5614c0015ab0610ec2981321f21975cc5103af52108c9b024238ab88054c644c0c3ac842bae6290803390847650d210461e322ea20a40008be87d4f64484070f90abb086880031bdd77258d1000636392caa0e6208c3c645d443484011bf0eb18c6a0002b360e65d894100c6e432e620a6000a9d83148644c0051d904bb283980029b61663189410045ec3861b224200ae4825846150c018e8ea38ac69019b2b9d954d89410045ec3ea63226000a6d821c165cc4010fb0e10acba000e1f215764c9100051f420e0b2e6226a3d84dc9651041117d0e280c8908031e5d750d81430043fc2ae3b1a4000c5c75dcd62440018d8e5b2ac2980021fe1570d89430061fbaee8b1a40029e4825c443484070f90abb48688013391c562508310047bc0aec9922004ce471589328c40f53d07b228690803590857510d210062e3a8e6b222000caf729cb644c0715390ca98c8980030fdd7645812100557410ebb22603ea9c8654f644c01117908bb086880023be09755913101556412c8a14620087f855db42440010f
  | 3 => 0xa312820087e87d956444001998e6312c0a08031b1c865591100043f43842b2886008bf87594644c0af4bd0610eca980021f61c32d95100451f426e4b288600aad820c064484011dd0e286c4a08021f6177058b3101557436c5a128204c747159532104093c902b9086908aeaba0850d91210461f322ea21e2003c3c759516090c1147d08382ca208022fa1c6458d210461e3a2ca9908200a9d8314064484bd55b083aec4a080359085751912134e4e39ca8b2220028ec821d9414807d970e1b2286980029ee01735974003d2f41c20b2e6255e1e53d4f644c07547b09b92ca218062f219740c5400054ec1843b22600087d85dc164cc40147d0b38ec8980022fa1f645893000477c12eca12200087e8719564440970fd0e3aac01880237e0d755911003e2e31aeb31a827da5f835c565cc40147b0a180c8908023be1d63189410247a40aec18a4004ce471589429040153b06108c898003690857498d2101e1e3aaa8b0486078dc835d564480011ef02bb286900022fa1c64589300445e422eab00860087d8710b65440070f90ab86c4a18021fe1571d8d400045fc3ac83224000ccc73d8960504014dd0b39ec4a080317dce73597403771d980ca3226000da421dd160484018beea39ac8880123e2197010d102f556432a9b128200a9e83140644840157700a98c898003171d773591300043ec3860b2882048f8865c241480e353f06b28c89819f271cd54591100046fc1aeab224060e8c4350f62504b94f50010acba00063e20175591320461e322ea3224200af180087614c0018becbb9ac8880021f61f205944300536c10e0b28865e8ec86dc9605040155b09300c4a0976ada0450191212ef5210ea2322420087e871d564440014b90ab18c6a00023de057650b300063bbaee2b1a4000cb4741c5634800187ae83a6ca9801e9720d705944336f0f180ca3226000ae482584614c00155b05b8ec8980028f61021597403961f3b6ca32260088bc845da214c0011db0e186c4a080e1f21576d093000c7b436e2a12205ca78805cd65d0009968e2b2285880123d20575591320045ec38423226000c3f65dd1624c0018d8ea392c6880022fe117558d200245e43ac8a1620008bf87590644400117f08bb2439800e1f2167610d1000c7a432e221a2000c3f659d2614c0018becbb9ac4880228fa1071597400047bc0aeab1a4000c9c74dcd63440018baeba9ec6a0002a760f54d91300043fc2ae1b1262088bc845d5624400155b05a88c8908030fd977458d10006d210ee8b1a4207c5c7359541cc401958e4322c2980022fa1c50d91210061e32ee890a20028ee829d9414c0070fd0fbaac6900028fa1021d95300047bc0aeab224025cae72193314840f9b0c6b8062900032b1cb645853000476c3cc631282018f4815d942c40a9c3ca7a98c8980021fa1
  | 4 => 0x44c001c38caa98c8980030f195749853001c3f43eeab048603c3e7555360504018d8e5b2ac6880022fa1c64581210070fa9ca63224200c3f651d1214c00147b0b38ec8981331d5c46518d1004656322e5a0a4200ce4621c5624c00199ee6312c0a08222f2117610d200043fc2aec9922000ae78158c62504031f50db82428817e8f60642594410065a3a6e2b1a42008bf845d94244001878ea322c2980028f61672d913003e2e31aeb98a42008df8758c63480015cb03300c4a09cf17dcc65591300147c432e021a40008be87147644c0014bb07082cb988022fe11760c52011d2ec18e0b2e620087d87d9443440014bb0a186c6a08222fa1c21191303055742061b128200a7581881651040153906b20c8880031bdd47258d1001c3e42aeda1a200087e87195614c00155f04a88c8908022f61e65191210051e42ac832260038bf8755364484018d8e432ac29800e1f2157650d200061f3b4ea3224200ccf73dc9644401147d09b92cba00228fa1021597400045fc22eab22607cea421590644841147d09b92ca208031dd9771589300043f43ecab12203ea9d831d7644c0070f90abb06290013391c5624c8410045ec38a3b226007c9c635d031500091790eaa2c91880237e0d76885400061e3aee8b22600087e871956344001ac843baac090a028fe11725944115d5741061b22420387c855db325001117908bb062900063e20175591310043f43860b288200ab5810c3644840159b06286c4a08032b1cb64505310247a40aeab108200c5f751cd624400187cea326629080e1f216761053000667b9ec4b028261a76811c165cc41147d09b9acba00030fd9474585300061e3aec8b0a6000c3d65dd121d000196ee338ec8980029b61430d8941006663b26498a4007a9e8390964cc44d47b08382ca208031759773507310051e422e5b2a20088bc845d9324400f1790eaa2c9990021f61776505300247a40aeab22405daac86550625040f1b906baac02197eade11611854236f1c180ca32260038ef8754b624c40187aebb24c29800237e1d6318d4100557434a831282008df835d562440010fb0fb2e62880022f61f52191300043f43884b2e6255a9f8458c63500018beebb9ac88800f0f9d55458443006563a0e4b1a200087f855db325000187eea322c0908e22f21d5458043307172a6a9b12825ee6651d476250401998e7b92c8880030fdd474589100051ec2ce7b224200c3e75d92644c0051b906bb664a00029e60021d95300051ec2885b226277ea421192634840187aea324c2980021fa1c42d95100051e422e7b2a205dda4211d1214400159d06286c4a08023ba1f62581410061fbaee8b2260088bc87191214c00147f0ab20c8980021f61c42597312f573408a1b12820087f855da43440070f90ab86c49889a9d604705944134557420c
  | 5 => 0x80021fe1f6510d100051f426e4b2e62008ef825d84344001c5ecaaa0c4a08230f19175991300061ebaec998a4200c6f65dc9414c0d947d0b328c898003f04c931481100045f43ec890a60008bf87590644840117b0fa9ec8908022f21f644853001c3f42eeca1a20008bd87144644c001c38cb29ec898003590857598d2101c3e42aeda1220008bd87994644c0a9c38a6a98c8980029e60021597402553d400e5b2a200387c855da4148011938c8b9882980028f61021594430445e422eab1082008bf87594644840156b02286c8908021f614765093112d56412a23224200c3d655d332104ff4ef02b92ca208022f61276485300065a326e2b126008cac645c8434800147d0a186c8908029b21570d89410062e328e6b12206ba9d83988644c0754bb06382ca2180237e0d7650d1000477c12eca1a2000c3c659d2614c00157300108c8980023be097650d210445f424ec90a6000c3c651d121440011dd0e312c0a08030fdd375582430061e328e8b122000cb774dc5634800187eea322c2980ea8f61071594430061fba8e8b1a400387e85dc164cc4010fb0f3aec0a1152a7a0c52191300070e32ca6322605ecac76d89425040155b043aec8980122f21d645083100727a9ca7b128200e6421d95214c00f4bd06102cb9884e8f61372597400065bb26e2b126000a5e8308565d00c155d083aec4a08230f9d165ccb400461f3a2ca18e803eb988054f644c0011db0e286c4a08030f5d074d95100061e3a8e8b1a20078dc835d8434400187aeab2087880021fe1570d913201c3f42ee0b108604a76811c165104014eb02382cb9880327dd3735891000536c2ce7b128278ea421194644840187ee93a2cb988029760c2159740006363a8e4b2220008f7875846150801e48433a8c890802a7a0e65d91210061eb2ee89908200a3c845cb654c00117f0eb20c898002b560430d8d210045fc22eca1a20008df835d942440091f10cb84629017ab9a0430d89410046fc1aec9922000c3f65dd121440070f90abb062a001e2fa1f6450d210064fb20e6b024238b988054c644c04b958e432262908228fa12205944101e1e3aca9b226000ad48358461480091f10ea82c0188123b2197210d2100656310e8b126200caf74dc9634400155b04286c8909b2a7a1a53191300051f42cc5b2260018f4865c7324404b55d05080c8908032bdd072591100253a40ae4b288200c6d75d4b62504070fd0bb82c5988062f21974cc9400063732ee4a0e62008ef825d9324400147d0b310c898176aba1954189412a54f418423226000c77751c563480954eb0239eca880063b2197290d200245e43aa8b244200c3c65dd1214c00117f08bb286908030f1947458d1001c3f42eeca126000a3d840c165104031790cba662a01df2ddc46458d2101c3f43eeab066400ab9800876
  | 6 => 0x61f3a8c930a605dab6810c064484014bb0610aca2180371087735812100556c24ca31282088be870c064484070fd0bb82c5a18123721d634ca4125e3c3b6ca902204b87e871d560904018beebb9ac4881b78760c65191300061ebaec93224000c5d731cd65d0001cc842b2a43a017b691c762509410063632ee4b222000cd473dc5624400117d0dba242980028f61442d91300145f43ec8a12600387c855c364484edd4842320c69080e1fa1476509310062e3a8e6b122000da4219d263484031d90cb9082900063e2017558d210047bc3ac230a860087f855da21500070fd0bb82c5a08030fd9474589300051ec2842322600387c855d9434400187aebb2086900132d1c564508310061e3a8e8b12205fc3f645d4615080147d0a108c898002a761353d8d4000c77436e4a0a4081a5f835c16510c01878ea322c0908021fe1570d912101557436c4a128225aae82140644840156b0828ec2a100317dce73594410046fc3ac631a4208a3c845c9651040517908bb6849819b2b1c9545911015e56396c8a0a4200ce7721c5644c80147f08b96ca880022fe1175591210445e422eab1a4200ace83994625040f1b906bb284880123e219700c52003d2f41880b2e62008bf845d563440010ff0abb686880232b1917210d212dd1ec24e6b2e80008bd870c064484a953d07a88c8980021fa1c75589100061e3aee8b1a4008c3c7459521d000187acaba063a00030fdd774589100043ec2ee2b1e80088bc845d921cc00187cebb24c69080e1f21571d8d200061f3aec821a4200caf64dc9414c0015a902b18c69000f0f9d5545874030656326e4a0a6000c3c75d91624c00187aebb20869080e3de1d51d85320056741ccbb128207a5e831c165cc4014dd0b31ec4a08021fa1f65589300043fc2aed10a6000aae82dc7644c001878ebb22c090982aba1353d894130717b12ea3224200c6c72d95414c0010ff0abb284880fa2fa1e54582430265b38ac921e2000cac7259141cc4011ef02baac8990030f5d46498d210075210ec890a600387e87dd560884974ed0239eca880023be0976507300061ebaec9322600387c855da414c0df87cec328c8980021f21975105300043e432ea21a2000c6c65dc94144001878ea322c4980232d1917110d2100556412c832262008bf87590644c8094ed03102ca2080e1fa1770592310045fc22eab122000c77651c5624c00147b09b92cb9881ea7a1b6350d400051ec2843b22600087d87087654c00117f08bb264880030fdd764585300043f438eab1a40008ed87994625040f938c6ba664a00063b219720c5200051f42ce5b226000a9d8399764484011ef02baac8908028fe1172d953000752108c890a6000c6c72d9564440091d90ea92c41880e2fe1d54d91320063abaea3b0a84078dc835da21500051d904bb0868
  | 7 => 0x1c0000589502c1842400303401d8380102a000000110062140b83c0000080a00004c0003b80f01e050090010120000880000803c048000020300100000c0081801d0300800a81b00c0100500d0420284200000c014003d901c7f80181e0380b40380000c2ac6d89100000c1a8020920140000b3dc0580281000c0ec000080000240880801c000080010061d80300002a1100b01c106020078140603300300202a008230090045955d8180380c80600400001802001040018090540004d40d80207e000000000020084286809c024130090060e84802a0560000e8000000140200c0400300a8020120445481800a00c0088300600000079000090000000020440280000000401016256018031ed0ca48c0284c00002c020010140000000b04200c000002260040000c01201c01801016084108370069cc23026088228298000120340000001803c0904a010000ae84e0000c80180502e008610190080200e8190c8a142e84100206c040030000800000c60c090010130000b80880300003c0680d002000038000000282c84200c004678020620004c053000024000010001103f80d0520080402400e0040300505804c5385f0100c06d0050bc318000060200080281101010c160028fa1421d91300043ec3842b288600acd8399462504011bf0eb18c6a1002b9e0565189410045f43ea5b22600087d8759731d000155b04280c89081e97a0e72597310053742cc63128200a6e821c165cc4bdb4ee438a84a08032b188745891001c3e42aeda0a6000cac72d91414c00917f0eb24878817b391c7625094100637ba8c4b028200a6f855c362504010fd0e196ca880022fa1c64585302563a3b6ca98a2000c7875dc1644c0011f700baac8980031bd9772585300045f43ec8b0a6000ccc621cd624404d47b09b9aca2080e1fa1576cc7400061e32ee8b126008a3e84dcd651040156b02180c8908123d2057650d200063a32ee2b12600087e870c965d000156902b20c89901e3b21d5258a430047dc02eab226408c9c7458d32104018daea3aec4a08030fd947458d1012d57410603224200aad8214c64484019c8c438ac4a18021fa1f655913012e56310e890a200087e8710b654c0014bb06382ca208222f2117558d2001c3e42ae1b1282008ed829d9414c00317908bb243a000a3ba1f7258d100043fc2aed21a400387e87dd5600c41147d08182ca208032ddd07158d203f52ec1ce4b2e6200c3e75d92614c011968c8b88868800e1f2157690d200043fc2aeda126007a5e8390965cc4d1958e52a2c8880023ee0175591310045ec3ea5b22600087e87087654c0070f90ab86c8988030fdd47458d100065a320e2b1260028ec825d9414c4011df04baac6880028fa1271d95303df5210cec3224200c6f751c9644400196ec838ac4980030f19474585300
  | 8 => 0x100700201c0718b034054000bb0140442800825c120010090080e0178000100009f8000240141480900002c0d88f00000000007062000059eb00a4580000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x2400a4006a1086839946448401c846408473581210040f660651d121440bb2a49160853191210040f662751933148401c24211d46458121427090867519331484012a598084644853041f09084651d1214400105f985cc735974036e862006554c644c001c24219d46498d21
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x181210b313a8c998a4200c09085981947448510
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x94b
  | 6 => 0x94e
  | 7 => 0x4
  | 8 => 0x5
  | 9 => 0x138e
  | 10 => 0x138b
  | 11 => 0x98e
  | 12 => 0x9cb
  | 13 => 0x9ce
  | 14 => 0x168b
  | 15 => 0x168e
  | 16 => 0xa0b
  | 17 => 0xa0e
  | 18 => 0x180b
  | 19 => 0x180e
  | 20 => 0xb09
  | 21 => 0xb0e
  | 22 => 0x1409
  | 23 => 0x140e
  | 24 => 0x249
  | 25 => 0x24b
  | 26 => 0x24e
  | 27 => 0xb49
  | 28 => 0xb4b
  | 29 => 0xb4e
  | 30 => 0x1449
  | 31 => 0x144b
  | 32 => 0x144e
  | 33 => 0x16c9
  | 34 => 0x16cb
  | 35 => 0x16ce
  | 36 => 0x289
  | 37 => 0x28b
  | 38 => 0x28e
  | 39 => 0xb89
  | 40 => 0xb8b
  | 41 => 0xb8e
  | 42 => 0x1489
  | 43 => 0x148b
  | 44 => 0x148e
  | 45 => 0x1849
  | 46 => 0x184b
  | 47 => 0x184e
  | 48 => 0xcc9
  | 49 => 0xcce
  | 50 => 0x1709
  | 51 => 0x170e
  | 52 => 0xd09
  | 53 => 0xd0e
  | 54 => 0x1889
  | 55 => 0x188e
  | 56 => 0x589
  | 57 => 0x58b
  | 58 => 0x58e
  | 59 => 0xe89
  | 60 => 0xe8b
  | 61 => 0xe8e
  | 62 => 0x1789
  | 63 => 0x178b
  | 64 => 0x178e
  | 65 => 0x18c9
  | 66 => 0x18cb
  | 67 => 0x18ce
  | 68 => 0x98956
  | 69 => 0xb4956
  | 70 => 0x94b56
  | 71 => 0x144956
  | 72 => 0x95456
  | 73 => 0x1549
  | 74 => 0x14c9
  | 75 => 0x134a
  | 76 => 0x2c9
  | 77 => 0x138b56
  | 78 => 0x124b
  | 79 => 0x98cd6
  | 80 => 0x15c9
  | 81 => 0x12cb
  | 82 => 0x1609
  | 83 => 0x130b
  | 84 => 0x10c
  | 85 => 0x130c
  | 86 => 0x17c9
  | 87 => 0x134c
  | 88 => 0x5c9
  | 89 => 0xa0e96
  | 90 => 0xa18d6
  | 91 => 0x180e96
  | 92 => 0x1049
  | 93 => 0x40a
  | 94 => 0x188a
  | 95 => 0x160a
  | 96 => 0x140d
  | 97 => 0xeca
  | 98 => 0xb8d16
  | 99 => 0xb9896
  | 100 => 0x20d
  | 101 => 0x184d16
  | 102 => 0x104b
  | 103 => 0x104c
  | 104 => 0x194b
  | 105 => 0x194c
  | 106 => 0x59451
  | 107 => 0x58cd1
  | 108 => 0x585d1
  | 109 => 0x5c591
  | 110 => 0x14114
  | 111 => 0x5d791
  | 112 => 0x597d1
  | 113 => 0x59a51
  | 114 => 0x17d791
  | 115 => 0x5d8d1
  | 116 => 0x28953
  | 117 => 0x29393
  | 118 => 0x28253
  | 119 => 0x296d3
  | 120 => 0x2c293
  | 121 => 0x299d3
  | 122 => 0x19c293
  | 123 => 0x148293
  | 124 => 0xb8293
  | 125 => 0x16d456
  | 126 => 0x16ccd6
  | 127 => 0x29556
  | 128 => 0x29616
  | 129 => 0x592d6
  | 130 => 0x59316
  | 131 => 0x14412
  | 132 => 0x1a4412
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2099
  | 6 => 3619
  | 5 => 1049
  | 4 => 12
  | 3 => 2
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
  | 9 => 2*((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 1)
  | 8 => 2*((h/34+packedAt gbK8 (1560+(h % 34)*6) 6) % 60)
  | 7 => 2*((h/720+packedAt gbK7 (77663+(h % 720)*12) 12) % 2099)
  | 6 => 2*((h/1206+packedAt gbK6 (173712+(h % 1206)*12) 12) % 3619)
  | 5 => 2*((h/377+packedAt gbK5 (61891+(h % 377)*11) 11) % 1049)
  | 4 => 2*((h/11+packedAt gbK4 (840+(h % 11)*4) 4) % 12)
  | 3 => 2*((h/1+packedAt gbK3 (162+(h % 1)*1) 1) % 2)
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffe0f81f07fc1ffe1ffff80013d13f033f3fc
  | 1 => 0x1e01f001ff87fe1ffe1c03ffc6d2ecc1cc7ccf
  | 2 => 0xe001fffe0007ffe1ffe003fff8e30f0e0f8f0f
  | 3 => 0x1fffffff80001fffffc003f03f00ff00ff0
  | 4 => 0x1fffffffffffe000000003ffc000ffff000
  | 5 => 0xfffe000000000000000000003ffffff0000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x221c02805009c022602498818004015011b15c
  | 1 => 0x14245000b4825214a208292a825064c0c454c5
  | 2 => 0x4048a5b20004a5415540525518a30b060a8b0a
  | 3 => 0x81395529500001999360062d03b00b600ea0
  | 4 => 0x1111ce69ce6739980001801837fc000dbf6000
  | 5 => 0x99e000700c403110110200603ffbdea0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaeeeafee8eac0feeaeeeafee8eac0feeaeeeafee8eac0feeaeeeafee8eac0feeaeeeafee8eac0feeaeeeafee8eac0feeaeeeafee8eac0feeaeeeafee8eac0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_40537
namespace PEqualNP.Outside.L_meta_40537
open PEqualNP.Outside.L_meta_40537.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 10 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 60 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 165 := (concat bs0_4_0 bs0_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 50 := bs0_5_0
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
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 8 := bs1_3_0
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
theorem bs2_2_0 : Interval s2Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 6 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 25 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 90 := block_range (n:=90) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 90 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 44 := bs2_5_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 6 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 22 := block_range (n:=22) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 22 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_192 : Interval s5Atlas 4 192 77 := block_range (n:=77) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 269 := (concat bs5_4_0 (concat bs5_4_96 bs5_4_192))
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
theorem bs5_5_480 : Interval s5Atlas 5 480 58 := block_range (n:=58) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 538 := (concat (concat bs5_5_0 (concat bs5_5_96 bs5_5_192)) (concat bs5_5_288 (concat bs5_5_384 bs5_5_480)))
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
theorem bgb_3_0 : Interval gbAtlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 2 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 12 := bgb_4_0
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
theorem bgb_5_960 : Interval gbAtlas 5 960 89 := block_range (n:=89) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1049 := (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 (concat bgb_5_576 bgb_5_672)) (concat bgb_5_768 (concat bgb_5_864 bgb_5_960))))
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
theorem bgb_6_3552 : Interval gbAtlas 6 3552 67 := block_range (n:=67) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3619 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)))) (concat (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 (concat bgb_6_1152 bgb_6_1248))) (concat (concat bgb_6_1344 bgb_6_1440) (concat bgb_6_1536 (concat bgb_6_1632 bgb_6_1728))))) (concat (concat (concat (concat bgb_6_1824 bgb_6_1920) (concat bgb_6_2016 bgb_6_2112)) (concat (concat bgb_6_2208 bgb_6_2304) (concat bgb_6_2400 (concat bgb_6_2496 bgb_6_2592)))) (concat (concat (concat bgb_6_2688 bgb_6_2784) (concat bgb_6_2880 (concat bgb_6_2976 bgb_6_3072))) (concat (concat bgb_6_3168 bgb_6_3264) (concat bgb_6_3360 (concat bgb_6_3456 bgb_6_3552))))))
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
theorem bgb_7_1824 : Interval gbAtlas 7 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 83 := block_range (n:=83) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2099 := (concat (concat (concat (concat bgb_7_0 bgb_7_96) (concat bgb_7_192 (concat bgb_7_288 bgb_7_384))) (concat (concat bgb_7_480 (concat bgb_7_576 bgb_7_672)) (concat bgb_7_768 (concat bgb_7_864 bgb_7_960)))) (concat (concat (concat bgb_7_1056 bgb_7_1152) (concat bgb_7_1248 (concat bgb_7_1344 bgb_7_1440))) (concat (concat bgb_7_1536 (concat bgb_7_1632 bgb_7_1728)) (concat bgb_7_1824 (concat bgb_7_1920 bgb_7_2016)))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 8, 9),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
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
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
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
def fullWord : Sig := 0xfeeaeeeafee8eac0feeaeeeafee8eac0feeaeeeafee8eac0feeaeeeafee8eac0feeaeeeafee8eac0feeaeeeafee8eac0feeaeeeafee8eac0feeaeeeafee8eac0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4276677312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_40537.Model.Repr at out
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

def mono : List Gate := [⟨.and,[3,5]⟩,⟨.or,[3,5]⟩,⟨.or,[1,2]⟩,⟨.or,[0,3]⟩,⟨.and,[0,7]⟩,⟨.and,[8,9]⟩,⟨.or,[2,6]⟩,⟨.and,[1,12]⟩,⟨.and,[4,11]⟩,⟨.or,[13,14]⟩,⟨.or,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276677312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276677312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_40537

open PEqualNP.Outside.L_meta_40537 in
theorem PEqualNP.Outside.L_meta_40537 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276677312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276677312) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
