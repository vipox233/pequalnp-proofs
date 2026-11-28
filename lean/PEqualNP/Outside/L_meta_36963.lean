import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_36963.Model
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


end PEqualNP.Outside.L_meta_36963.Model

namespace PEqualNP.Outside.L_meta_36963
open PEqualNP.Outside.L_meta_36963.Model
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

def SBf (j : Nat) : Nat := [8, 6, 4, 7, 6, 7].getD j 0

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

end PEqualNP.Outside.L_meta_36963

namespace PEqualNP.Outside.L_meta_36963
open PEqualNP.Outside.L_meta_36963.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x24acf1000190145400d004e6c226220400000004190a94529420860044601891e4d4003800b244654b8e3e345873a0c30006410080c0001248ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0xe61bc41cc3bc6398770c730bfaa4617e548c2faa9185f15230bea9c61df438c3b887185f94a30bea9461de328c3b865185f94630bea8c61be418c3788318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4987bd4930b7a92617c524c3d8a4985b14930ef99261dd324c2fea2987dd4530bba8a617c514c3e8a2985d14530df20a61bc414c3bc6298770c530fd98261de304c2fea8185f95030df2a0613e540c2faa8186f550309eaa0617c540c2fca61877d0c30ee218617e520c2faa418778c830ee190617e510c2faa2186f90430de20861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c837c83906f10720ef18e41dc31c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5107bd0a20f621441ef32883d865105f94620bea8c41be41883788310778c620ee18c41ee21883d843105f94220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c53482fea2907dd4520bba8a417c51483e8a2905d14520df20a41bc41483bc6290770c520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4107bd0820f621041ef32083d864105f94420fb288417651082faa2107d54420baa8841be41083788210778c420ee18841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10df20e21bc41c43bc6388770c710fb10e21f521c43f641887e08310bfaa4217e548437ca9084f95210beaa421bd548427aa9085f15210bfa9c217e53843bca7085794e10bea9c21dd53842baa7085f14e10bfa94217e52842faa5085f14a10bea8c21f7418437c83086f10610fa20c21b441843ee6308778c610ee18c21f431843a863087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910df20a21bc41443bc6288770c510fb10a21f521443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f7410437c82086f10410fa20821b441043ee6208778c410ee18821f431043a862087dc8410fa108217e50043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xe528c6faa518f7cca31ef19463dd328c7b86518df94631df20c63bc418c7be6318fdcc631bf284637d508c7bea918f795231eeaa463dc548c7bea518f794a31eea9463dc528c7be8518f790a31eea1463dc428c6bca318f7d0631ef20c639e418c7ba8318f710631ce20c63df508c7bca118f754231ee284637f544c77ea898cfd5131bf2a2637d544c6f8a898ef151319e2a2637f524c6f8a498ef90531de20a63f7314c7bc6298dfd4131be282637f540c6fca818df55031be2a0637e530c7be8618f790c31eea1863dc430c6fca418df54831ef99063de320c7ba6418f70c831bf28863f7410c77c8218ef10431fa20863b4410c7be6218fd8c431ee98863f5310c6fca018df54031efaa063de540c7baa818f715031efa9063de520c7baa418f714831efa1063de420c7ba8418f710831ef288635e510c7aca218f7d0431eba0863de410c73c8218f750431ee208639c410c7a88218e510431efa8063de500c7baa018f714031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21df20e43bc41c87bc6390f70c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510df94621fba0c43be41887788310fd10621da20c43f731887bc6310f70c621fa18c43d431887de4310fdc8621bf284437d50886fea890efd51219faa2437e54486faa890df15121de2a2433c54486fea690f7d4d21afa9a437e53486faa690df14d21ee29a435c53487ee8290ef90521de20a43f441487688290fdcc521ef18a43dc31487e86290f50c521fb90a43ee21486fea090fed4121bda82437c50487f0a090de14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e510877c8210ef10421ef18843dc31087de4210fd88421f690843f521086fca010df54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40bf28e817d51d037c83a06f10740ef18e81dc31d02faa9205f94e40bea9c81be439037887205f94a40bea9481be429037885205f94640bea8c81be41903788320778c640ee18c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa9281ef52502dea4a05f14940f6292816c525037e84a06f50940bfa8a81f751502eea2a05f14540fa28a8174515037c82a06f10540ef18a81dc31503f680a06f90140bf2a0817e53103bca6205794c40bea9881dd53102baa6206f90c40de218817e52102faa4206f90840de210817e51102faa2206f90440de20881de31103b862205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730df20
  | 2 => 0xa00c0080400000801003002004000000060000080200c010000020040000000400200000801004004000000080100000000000401004000008020090060100600100a00afca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1fdd4543bba8a877c5150fe8a2a1dd14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443bea88877e5010efaa021df94f42ef29e855e53d0afaa7a17754f42aea9e85be43d0b7887a15f94742bea8e857e50d0afaa1a15f55242bf29c85de5390abca7215f54e42eea9c855d5390b7e87216f50e42bf29485bf4290bde85215f94642fb28c85765190afaa3217d54642baa8c857e5090afaa1215fd4d42be29a85be4350b7886a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6215f54c42dfa1885bd4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a665be54cca7ca9995f55332deaa6653d54ccaf8a99977d0f32ee21e657e51ccafaa3995f94332bea86657f548cafca9196f952329f2a4657d548cb7aa9194f55232be2a4657d538cbbc87197750e32bf29465df328cbde65195f94632fb28c6576518cafaa3197d54632baa8c657e508cafaa1195fd5132bf2a2657d544caf8a89977d0d32ee21a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a0657d540caf8a8195f94c32ef21865dd430cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41ef29e835e53d06faa7a0f754f41aea9e837e52d06faa5a0df94341bea86837d54906fca720df54e41dfa1c83be439077a8720ef10e41bf294837d529077e8520ef90a41dea1483bc42906fca320efd0641fba0c837e50906faa120efd4e41df29c83bd5390778a720efd4a41df29483bd5290778a520efcca41df19483bd32907786520cf94641dfa8483be509077aa120ef14241bfa9a83df53506bea6a0df14d41ee29a835c53506fea4a0df14941fba0a83be41506fea0a0df14141bf2a0837e53106faa620efd0c41df21883bd43107788620df94841bea9083bf421077c8420ef50841de210837e511077e8220fd90441dea0883f541106fca020df54041dfa9883be531077aa620ef14c41dfa9083be521077aa420ef14841df99083be321077a6420ef0c841df288833e511076ca220efd4041df28083bd5010778a020dfd5331bf2a663be54cc67ca998df55331deaa6633d54cc6f8a998df94b31bea9663f741cc77c8398ef10731fa20e63b441cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63df438c7bc8718f750e31ee21c637
  | 3 => 0x818000000b0afc0023f000000001820000c0000470000002e281000cd0000000000006f00046a0000005000000015358000000000004bc65c0000055e1916c2b80007f5678002aa0009692a204000001ad000ca80026e530000001f95fa000000000000000000042434ce489d368c197a00000000000000150c00f7140000001b72300003407e9ea48c0f0d92c30e8cd5a2a3610e091881900000000000000000000000000000ec8ea000000003216ba0000000050c61c000e5000000889530006f0c70792721e1910064bebc00009800000189000000000000003a65d447862132000000200009f8fa2a0000291b096f6c89f0001a23220011d01f000038000353e0d651e29c00000153a542b275d5425b52ac7c5f8b1574000ef800000b5400000308858002442401d8000000983b4000070000000000000000000000000490279bb00000000000000001522600004d4000000000000000000024dbb9c60000009d8000005380000023492c0000000000000000000000000670000000032e27a00000000000000cc800000000000000009dc0000000000000000030000002500000000000004c4bc362da2b8aa97e0005568b03f0000000006a9e60ba0009b8690f80000000000039c6e1233de000f58005ca000000e05842f47f8000aa82c001ae198230001a028a0017b0000003e42a00021eba01c8006860010980054214c00000630814000bb000000228b7174b359f0005900000017c00058400012000000000c10001b8000006b431c00000000000000000000000010000000000309000250003740002247c000418a1050947000868000004760000000000090c3b9ce3ba99559a45080000e00005a20000015f000b00bd1511b03d4003012ac000002b56665c4000000003c0a58003ac000ea800158a95792c900000000000000c68000004f00000033d3260012a80500000a00000002008020020020040080100300200000001000000010020000180000100000001800000000018000000000280000400000002002004018020060040000000401c0200000001c0000400000404800004008000000020040000000001404000000000008080060240300100400c008010020000400100e0000500000a0000000100c03c00800000018000000040000080300600801009008000000010020040000000000c010040000080400000a0080200000400001801000000008000000100000300000001000002004000000020000080001c01c0100000a0000280100c0000100101a000008000040000000000400400002012000000060060280080000201400000000010008000060040000000a000000060020000000501e0200000100a000000010040000080300c0000380601801800003000008000060020000000000001800002000008010040
  | 4 => 0x12e0012e0000c0000002ea000db000000000b5ccf000000ab51c00021686c000004820000000023e000000000000010a8c50000000003b000000168000cad04dc0004b40000000000000000000000001af8000001a80035028200079000000001a6b4a014000000002c8000d50001c695864890000478713560b4c50d30820005e40d8b30920c91b811420d200000000000000292000249b7b0321a7c8079ff278af070b6920a0015b000000000002193c0000000000000013ab2339800017b2c2fa000000004980016c89f0006d4002176bc891132310f4000000001de000568aa00028800000000000002070000016a329000c44f6b5b4fe0000030b000ab8dd3272185c98284400035c000002e86fdaa0000000009080033e0000000051800000000300cd8000000002547600000000000000000000000006260012426c4c493400000000c6daa8006a2000001a1306ad183a1c6c450c48b650908040019b0ccbcc2fadb1b400000000544669872f1678760ca8f61d2000df01906e9080028e6b80013d0004c89a48998c04621539800000ac800000000000630f30000000000064cdb4b8000000000000000005dc000001720000e800000a740a1bd0b20000003e3c400000000000000668a7000000e880004a00000029000000002f74641ccf2000536b8000000000a2c0016064846c000000001fc000001cc02c000d90000017f80052c00000000000000580000000000f2eb00000000289000000d4000000000000005bc00000000000000000000000015e9e529a00000000000000b52e706200000071000000000002fe6c0000000001d46016b2ec0002b8003d200000000000a01378000007ec0000045c000000000001c800000000001b58000008399784600000000000456b116580068000000185000000fb12820669db80000003902104d178144e528d5b800000000000000000001680003eb1e00000192a1f0960002900035699c0080058c00000118000000001c461000000000650960000003f8000002ac4fa0003d98f5be000000004a60145724f6d40005332d000000a400043a9ec8e881000000458000200009f800188000001a9068b040000057c09c000000008a5041af00082400000000d4c000364d483400000000bb0989da48e86116b634225f8a80e86c0000659b75f0000ce800000000e1b3200000000000000000c50000000013a00000000000297000b901d0ca19c001b885e00030c419c1000000000000000001e8ab0004100aace0000000000000015861000674c54c4a0250e000001ec0000a00000060400000000000cfce7800000000002762ae45c9b30d506498000002e6000001b6338344880000008814280061826c000002523ada72280120017489c000651a59685760014790e000894000000000b00000000
  | 5 => 0x1a22630441bc0198d000001a38000004c0fd000294000002683ee0000000011c509bb000000000000000420000000063246400000390001252b9000c8000000366010002270c2000000003b6adccb00000000000367546000000b5528dd4f986b1108505922f1f4c74ef12c000d0825165274068a4901000d249f1e130234800000000b88000004ae7357300000000000000598000b312b24a985bc8fc00081000043000938000000000016e8000000014400000000000000000001249140000004b000000001580000e0000000000000000000000000000368056888000002b000000000000294002fa1dc28c0012201a000ad02e638d3c0023e3a82d80016768c4cc0034c3720000015b114bd4000006f0a41390f12f618c002d62100012c800070878d61e70000000008d000000002d00000000000020e0010014f13c9c59c96c4da0009933b0000000014666e49c00000000000000000000000000000088ccc26b6a47a08a80031600000000288c3c04000000000830004680000012e000714003724140007d8df3844d1b300009c350e3800000cc042000000268000002140000000000083d380fe5de72cae800000a4c000000000fc000000000008e2fe100ce1290002da030f195e62e000000000001a0c31d24a27c570b572dc8cd6529e0007419886d53e36d4caa65a6000d18af0000000001c21200101b2b224000003735da0005c0003f0b14ee18800005cd28000b68f4198005dcc109c000000000000cf0002f8208dd0000596925d0006c40000000000120000000885410d6000550002390008a9450002a4a44bc000000000002791903dc548865f6458a6266140000fab0a58eac4001623fc008c9000534000000000005a57c8000003d009800000b8c00316552000d2163
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xf548433761552109798c548425d63152108f993538423d64d4e10c7952538431d5494e10c7951538431d5454e10d5d85538423e6414e108f590538423e64d4a108f593528425e63d4a109758f528423e6414a108f590528425e6314a109758c52842d663d0610d594f418431e5390610c754e418431e5310610c754c41843355410610d594c41842b56510610cd59441843365310610e594c41843165310610e554c41843345310610cdd4841843355210610ad993318433654cc610c7952318431d548c610e5106318431e540c610c75503184396410c610e51043184336540c610d554c31842d5650c610d55943184356540c610e59503184316540c610e55503184354540c610d5d483184355520c610ad99321842d663c86108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544427761551108f994544423e61151108f184544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d109dd85534425e6514d10c7d50534431c5414d1097984534425c6114d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524427761549109ed81524426e6514910cbd50524432c5414910d3d4c524434c5314910d9584524423e6590510c7d4e414431c5390510cbd4a414432c52905108f994414431f5310510c714c414432f5210510cb148414425e658c510c7d52314431c548c510d3d4a314434c528c51097994314431f540c510c7150314434f520c510d31483144394410c5109d99621443345488510d514e214436452885109d19521443345448510d514d21443645248510bc181214436852c4110cd15210443545384110d914a104425f63550109718d540425e63150109758c540426e62150109b588540423f6454c108f191530423e6414c108f590530426e6214c109b588530423f64548108f191520425f63548109718d520423e64148108f590520425e63148109758c52042766114810b598f41042b661904109d59441043366510410cd59441043365310410cd14c41043375210410cd54841043b26010410ec58041042b664cc410b59863104394418c410e59043104394410c4109d5943104356650c410d55943104356540c410d51503104357520c410d554831043d2600c410f4580310427565c8410ad99321042d663c84109d594210423e64940108f592500425e63940109758e50043344194010d50c650043b041c8010f40c720042796508010ec10420043d03108010f808420042796584010ec10610043d031840109dd9510042b46444010b518d10042e462440109ed9510042e86244010
  | 1 => 0x825c63552209dd85548827461552209798c548825d63152208fd91538823c6454e209dd8553882746154e208f990538823d6414e20b398f42882ae64cca208fd91518823c645462097d8d518825c6354620e510431883a44188620f10c6218823e61d51208f992544825e63951209758e544827661951209d586544825f63551209718d544826f62551209dd85544827461551208f994544823e6115120c7d53534831c54d4d2097987534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209bd8953482776154d209d185534825e6514d20c7d50534831c5414d2097984534823e64d45208f593514825e63d45209758f514833754d4520cd153514835753d4520d514f514833664d4520cd593514835663d4520d558f51483375414520cd15051483575314520d514c51483376414520cd19051483576314520d518c514823e65905208f196414831f5390520c714e41483375190520cd146414823e65105208f194414831f5310520c714c41483375110520cd144414825e658c52097196314831f548c520c71523148357518c520d5146314825e650c52097194314831f540c520c71503148357510c520d51443148394410c520dc147204832c5488120d314e204836451881209798f540825d63d50209d987540827561d50208f596540823e6195020cb189540823c61550208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c2097986530831e5454c20c7551530834c6254c2097185530823e6414c208f590530825e6314c209d98453082756114c20cb55342082ce63d08209b59442082ae64cc820d354f320826d650c820cd95251083355494420d594e51083555394420cdd9251083346494420d5d8e510835463944208fd91510823c645442097d8d510825c6354420cd95151083355454420d594d51083555354420cdd9151083346454420d5d8d51083546354420dc181510823f65904208f596410831e5390420c754e41083365190420cd546410823f65104208f594410831e5310420c754c41083365110420cd544410825f658c42097596310831e548c420c75523108356518c420d5546310825f650c42097594310831e540c420c75503108356510c420d55443108394410c420d954621083a44188420f10c6210826f6548020ab19120082cc6348020b9185200827b6548020bc185200825e63d53109758f54c426e62d53109b58b54c425e63953109758e54c423e64d4f108f59353c426e62d4f109b58b53c423e6494f108f59253c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c425e6394b109758e52c4394410c710bc18121c42f16108310f888420c425e63d52109758
  | 2 => 0x518c540d5146315025e650c54097194315034f520c540d31483150357510c540d51443150394410c540c714e405032c5290140cd146405025e6194c409dd8553102746154c40b518553103576154c409718553103546154c4095185531023d6590c40c754e431031d5310c408f596421029e6390840c754e42102b66190840c754c421025f63544409718d511031e5390440c754e411031e5310440c754c4110336511044097d96311025d658c44097d94311025d650c440e5104311031d53d00408fd95401029c6350040c754d40102ac6250040ad185401027b65500409b98b54cc26d62d53309d98754cc27561d5330c715143cc2d46150f308f99252cc23d6494b309d98652cc2756194b30a759332cc23f64547308f19151cc3365110730cd54441cc356510c730d554431cc394410c7309d987548c27561d5230c7d50438c23f6454a308f191528c29e648ca30b5986328c23f64546308f191518c3365110630cd544418c356518c630e5104318c23e61d51308f992544c26e62951309b58a544c27661951309d586544c25f63551309bd89544c26c62551309dd85544c27461551308f994544c31d63151308f984544c25e6590d30c7152434c25c6550d30c7151434c2d46150d30cbd53524c32c54d4930cbd50524c32c5414930d390c524c34d431493097997324c29d64cc930c7153324c34c52cc930c7151324c34c524c9308f993514c23d64d4530cdd53514c33454d4530d9d4b514c36452d4530cd993514c33564d4530cdd50514c3345414530d9d48514c3645214530cdd90514c3346414530d5d8c514c3564314530d550c514c3573214530d54c8514c23e65905308f196414c32f5290530cb14a414c3375190530cd146414c23e65105308f194414c32f5210530cb148414c3375110530cd144414c31f548c530c7152314c34f528c530d314a314c354518c530c7d50314c31c540c530d3d48314c34c520c530d5d44314c394410c530c7152304c34c528c130d5146304c23d65950308f986540c27761550309d185540c2b46155030c718d540c33761550308f185540c33461550308d185540c23e64150309798c540c25d65d0c30c7553430c25d6510c30c7550430c25d658c830a7992320c31d548c830b5986320c31d540c8308fd91510c23c64544308fd96410c23d65904308fd94410c23d6510430c7952310c31d548c430c7950310c31d540c430d5944310c394410c430c7553300c25f654c030a7191300c31d544c030b3189300c2d4614c0309ed95300c25e63d53209758f54c827661d53209d58754c825e63953209758e54c823e64d4f208f59353c827661d4f209d58753c823e6494f208f59253c823f64547208f19151c825f63547209718d51c83365110720cd54441c8356510c720d554431c8394410c72097d8d548
  | 3 => 0x621d515031887c6620c621f158831886b664c8621b598f218863e64942218f592508865e63942219758e50887344194221d50c6508873561d51218f992544865e63951219758e544867a60951219e582544865f63551219718d544867b60551219e181544863e6515121c7d53534871c54d4d21d5587534863e6494d218f592534865e6394d219e98253486796094d218fd91534863c6454d219ed8153486786054d2197994534871f5414d21c7150534867665d0521b598f414875453d0521b998b414863e6590521c7d4e414871c5390521ad986414863e6510521c7d4c414871c5310521cdd5041487545310521ad99441487366510521e5d4c41487365310521cd14c41487945310521c514c414867665cc521ad993314873454cc521b998b314865e658c521c7d52314871c548c521b59863148794418c52197994314871f540c521c71503148796410c521e51043148734540c521d5d4c31486d6650c521d59943148797540c521d59503148754540c521e51503148714540c521ad99321486d663c8521e910621487c43188521ced53504873854d4121d6d4f504875853d4121ec10750487d031d4121ce907504873841d4121d68c7504875831d4121cd10450487543114121ced5050487385414121d6d4c50487585314121ec10450487d03114121dcd04504873a4114121ce10450487704114121cc10450487733114121d68c450487583114121dc0c450487503114121dcc84504876a21141219798f540865d63d50219d987540865e63950219758e540863e64d4c218f593530867661d4c218f992530863d6494c218f992520863d64948219798e520865d6394821cd9444108756510c421e5104310866f6548421e990521087c63148421ba18121086776548421bc181210863f64540218f191500865f63540219718d50086b46150f409798e52d025d6394b409d98652d02756194b40a758f42d025f63547409718d51d03365110740cd54441d0356510c740d554431d0394410c74097d8d529025c6354a40a798e42902b66190a4097d8d519025c6354640cd9464190356510c640d55443190394410c64097987535025e6114d408f997435031c53d0d40c714d43502b46150d40d3d4f525034c53d4940d3d4c525034c5314940cbd0c525032d43149408f997425029d63d0940c714f425032c52d0940c714d425032c52509409798f515025d63d4540d5d4f515035453d4540d9d4b515036452d4540d598f515035563d4540d5d4c51503545314540d9d4851503645214540cdd9051503576314540d518c51503374314540cd50c51503374214540cd508515031f5390540c714e415032f5290540cb14a41503345190540c7d4c415031c5310540cbd48415032c5210540cdd44415025e658c54097196315034f528c540d314a3150357
  | 4 => 0x7592328c74e524ca31a7993318c69d64cc6318f992508c63d6494231b5987548c71f5495231b3988548c6cd6215231b5984548c6d661d4a31d3d4a528c69f6454a31a7191528c69e6414a31a7590528c6d66114a3197997428c65d65d0a3197996428c65d6590a31b5986428c6d56190a31e5984418c69e64d4231a7593508c6ce62d4231b358b508c69e6494231a7592508c63e64951319758e544c65f63551319dd85544c63e65151318f996414c63e6510531cd153314c71f548c531c7152314c66e62d50319b58b540c63e6494c318f592530c65d6590c31b5586430c71c5450c31b5d85430c65d6510c31c7550430c63e64948318f592520c69e64cc831a7593320c69e648c831a7592320c6d5618c831d3548320c6d5610c831b558f410c6b661904319d594410c7974310431e590c410c7954310431e510c410c7366510431cd594410c7966310431e558c410c7365310431cd548410c7973210431e58c8410c7953210431e50c8410c69e64cc431a7593310c79441cc43197d95310c69f644c431a7191310c794414c4319dd95310c6b4644c431cd106500c63f64540318f191500c66f62540319b189500c6ce62d5031b358b540c6d661d5031c7550540c6d66115031a7993520c69d64d4831b5987520c69e6494831a7592520c74d5214831b5984520c65e65d083197597420c65e659083197596420c6d66190831b5586420c6d76150831b5185420c6d66110831b5584420c7566194431b5992510c6d56294431b5982510c65d65d0431b5597410c75565d0431b558b410c6d660d0431b5986410c69e6190431a5986410c71e5190431e5946410c65f6550431e5504410c69e6110431e5984410c71e5110431e5944410c6d76510431b5594410c6d66410431e5990410c7965410431e5550410c6d56210431e5d08410c7964210431e5508410c7944210431b5980410c7976510431e5994410c7956510431e5194410c7976210431e5988410c7956210431e5188410c7975210431e5948410c7955210431e5148410c7976010431e5980410c7956010431e5180410c79441d4031e5106500c69f6454031a7191500c6cf6254031b3189500c7944154031a7990500c69d6414031b3988500c6cd6214031e5104500c65e63d53219758f54c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c871e5454f21c755153c863e6414f218f59053c871e5390721c754e41c871e5310721c754c41c871e548c721c755231c871e540c721c755031c8794410c72197d8d548865c63552219798c548865d63152218fd91538863c6454e218f990538863d6414e21b598f41887366510621cd59441887365310621cd14c41887a66210621e958841886b664cc621e51063188796410c621e51043188756650c621d55943188756540c
  | 5 => 0x5190b376494642d5d8e5190b546394642cdd0e5190b354394642cdd0a5190a5f63546429718d5190b565354642d554d5190b576354642d518d5190a3e6510d42a798e4250ab661909429798f5150a5d63d45429798c5050a5d63141428fd954310ab46150c42a758f4210a3f65508429bd954210a5f63544429718d5110a5f63540429718d5010a7761540429d1855010a3e61953329dd8554cca746155332ad18554ccb1c6355332cdd8554cca3c6155332cd18554cca346155332c755343ccb1d5410f328fd9151cca3c64547329d987548ca7561d5232c758e548ca3e61952328f185548ca7661152329d584548cb1e5490e32c7951438cad46150e32a7593328cb1e54cca32cd952518cb355494632cdd92518cb346494632d5d8e518cb564394632d550e518cb5732946328fd91518ca3c6454632cd951518cb355454632cdd91518cb3464546329758e544ca7761551329d185544ca7b60551329e181544ca5e65d0d3297994434cb1d5410d32a7992324cad6618c9328f993514ca3d64d45328f990504ca3d64141329798f540ca7661d50329d587540ca3e6494c328f592530ca5d6590c3297d95430cb1c5450c32b5185430ca3e64948328f592520ca9d64cc83297d95320ca6f654c8328fd91510ca3c64544328fd91500ca3c64540329dd85500ca746154032d5d8553d071e5350e4197d8d529065c6354a41a798f429069d63d0a41a798e429069d6390a41cb949429069e63d0641a758f419065e63942419758e50906b661d4e41c7d4e53906ae6214e41ab58853906b66114e41ad987529072f5294a41a7d8d529069c6354a41a798c529069d6314a41ad984529063e65cca418f597329063e658ca418f59632906b6618ca41ad586329069e63d4241a758f50906ae62d4241ab58b509069e6394241a758e509075453d0541c7d4e415071c5390541ad58743106b76150c41c754c431065e63948419758e521069e63d0841a758f421069e6390841a758e42106b56190841cb54842106b56110841a798f411069d63d04418fd95411069f6350441a718d41106776550441b518d411065f63540419718d501066f62540419b18950106ae62d4c41ab58b53106b661d4c41c754c53106b66114c41a798f521069d63d4841ad987521069e6394841a758e521072d5214841ad984521063e65cc8418f597321063e658c8418f59632106b6618c841ad58632106b7614c841ad18532106b6610c841ad58432107366194441ad98e51106b56294441ad982511069f6354041a718d50106af6254041ab189501069e6314041a758c50106ae6214041ab58850107376155331cd55041cc6b56510731cd59441cc7355210731cd10650cc66e62152319b588548c71e5450e31c7d50438c63f6454a318f191528c69e64cca31a7593328c69e648ca31a
  | 6 => 0x6fa171b989900000f0430989c225408e17012a0ae046907107a240141132528f083e81f8002620000000601a1800147a5200024ca8c85e9d31870000001290f215e9ed8531730ff99d1e60c40000ba80006c0000801dfa5f9100391188ea00007a970a569b81349dd20e1ce91c9d29d1000259985a6987802ea5a11f80000000000003485711f00008f00010687726400003d28803a0e695300026c0002861f412b80000380000000499000017780000000000018500014198399880081f0160c0000010000080080901c0000000000e04c00001002028060080320000000b002028008040020ac0081704c0200401d00e004100000180300180702801c0380600401800800000004000050000280b8010000000d00d0000100000901a004060030060240700701601c0080506e0000c8090000c002800036008048000000180100b00c0380100f0000080000200002009005000024000030000080081202e0340000000e0d8068250020340000906e0dc0181b004000120020040080000000001006801010074008040020740080302201c0400204e0000c83100002000038032044000010240400400f0500141100d00c024010020140200a00a01c0000080e000034008040000040200d004010008010000200180602c004050050460180100800003c1000500e0040000e0100000080301e0800a8020060540a0040080140280000800c0280505003802010000098000000660001180000200002007018000018000220a01c8040000080084a024004000120040240380000800017800002098000050000000a00200a01403004000050020100020000100c000040010020020100280700602003001000004018000000080080900c07c050050220140200103600c0b00f01e0240500100405c0100705e01c0d80a0560180300100a02c008000060000e80a00000c00800042034010020000000a80c006000088000000400d009016024000120040000380200200800811004008020020120000400b00e0100681500c01828806008004040090000180102801004c0080100a06002813000020000040000000200700800001811002050018060000300000003600804007cdd905150f576314543d5d0c5150f364314543a75924310e3f6550c43ad1854310e5f6550c43b51854310e9f6550c43c7d954310e9f6250c43e5d854310e9c6150c43e51854310e946150c43a71814310f1d43948439d9865210e756194843c750e5110f1d43540439bd895010e6c62540439dd855010e7461540439798653d0a776154f429d18553d0ad46154f42d5d8553d0a5c6154f42d518553d0a546154f42c754e43d0b1d5310f4297d8d51d0a5c6354742979865390a5c6154e42c794f4390b1e5350e42ad1854390a9d63d0a42c794f4290b565394642d554e
  | 7 => 0x9bca6e2708001880370002669409a09d98f308a1280000118000b421b00000019783194c80020400015f84016a9001ce0938e205a29102a9f18000001f10000aa13180029d8be9f717e0000f192608b0ac24492296417283f89287c217965a1893f00029288719385e000233a089829030920b6a77a2280591d28317f2411e39359bf84420a84a1941631eb8ec07b94ea7c19f0000238261448000fc8002908000cf8718002092570300cc000000203982005001966000000000000077800000085800247a310000c18000b10000420002389d58bf83b166a970941c023280000002b04f1848c4a4909708d13727f9f48459eb01d10a05913d90a9b89a58000002149d910e03323d1689710618e300015d8000490ce0000000f50091581d70001111121f31dc94822499a23921f9aba111391219ee2381d813524b0002198000070000000001270000ef81980015c8000d2a3e8ff09b861110a7410299b8d50cd9e29ba038a0b84b27296000ea7d1f209088da890069fd87d0cb08e952a750362500fe9bb8a29cc06f2460a316ba939d4994a7e25d1ee8580869d688c8528f9a2f181a85a46869a58a308f61b01561a520088c2721fb0f90ee8d20898a0a7ca6a945825a130861a28ca94505f251a8d80025a9ad9f680016e80019f9b69bc0000001308000411d21db82291a09f0000000000002969400001a38c000011829b9fc16e0db0bb0b795e1a10010b19c811d9619b204080000013e0001f98000001720000000539e72718000001b50000001e598e24704d00003e0001840f58d80001ca8569488000000578ce8000001f601b0002648000d38aa973a689bda498a100000001024e800032266261273a1a25c99720d02c81ba580a822882116c8e71c893210d05111782e18f8e00382671e883ba9c9ea8c883114b1b0964a629fba138460a20b021920c9fa878881967939a419ff9ad1999172058b3a9d08f9cd00020f0b511c14214c0001ab1440cd22b07a0418299fd1502681b90188041141268000000000638000db8e41791f911580029997d80011ea3209628115210f22f8fd21a9af8c129904480006885b82f26b1740e5a7b283a9b032a2b8e88dfa2311b9161549df231843a3a92e1768b081d9a7a4e27a0821d428b92b10b23b09e8f70000f81910002208001ca0292849a31f7a26a6b8b90000ac8a79dc0540ed0f29301d78d5912a201a4a6d1230a4a8c227a4d9f882213293c90e83693b1ff151a762920af0d01190bd11184783c0fb00886a1af25617b8891148f39ec80028a9f80a6a400fe17891e0000da8d486691a98f00015525f17993a13c01c8121ac83f0a9096a051770e527e9f59f5242a748f88e114e19e9d18d18c500005d8000000000002151020351be80016515a9019579c50002180810001930fa1c189a00025d80
  | 8 => 0xb7a531c395f23c9608f4a07a0491695ba2aa801b30f78f120f9b7237880950a958001fa0f41ec25790b80000027ba4fa9484e82885482b98b89fa6784ba9328f19c8912978002919c30a18a40561e100006401e0000d90bb8000000da24a9e00dc9e08000690c312780020a1fe2398ab8980b20cc87e84712c93394a98884809d13a8161aa176000210a1424c0001f080015994685d062a3a1010c09bd189a2e00000018d125a0da258109a98001db14395a1a2124800a0e8001e48000218721411f392d80626c92528f815a53a2e81802d2022068ad1240000248270001e92590000c9a559080952691690000000501c58000e61379c287f9a00faa7f1fe9361a693b9dd96c01300c8128000e91981238eb0e79a88001040eca098b88bc8851da23715694a00006e90c20180007f0001138ad884a9884e05fa7a94b897a789a71c098608a8000dd8658000001cf928a210a9882a1d8fd800019109075a238001051ae80024d16980015415102d80017a90c9059a81c126096b23680022981f1ef075079a7980000f8148000519b284890980000008327800000000002828780012d1c484c97812c175a9600b8098a00ed80000022c01100d8001832160000d100000000028423e1341c70000000000001591891f028988881ea12a40971a809b60000bf000000207153a0c0000b29cc8dc00000000020298c8451610000000de1d600004a8841ac0cb81707329a1d506e1d024305c8178e48150002509da98d8fc1062361748398b70df28718aa0607e2731a9091a4207023413e99e0232868c595c0d0a6f80019680e2638c20a613807ca791570022650520fb82c25b0001498621c900006716d8359038b48c68bd9959b5a6f0b9a4a1e800008b80000021f06080014329a9150558000000c283780022d9ae05b0001c68e280000000005502798c0000b6030842a43962a8e00c1e180017c9c625514f92e91b00b1ea2219cf0169639e300009c27d8650ab0d70000901e200000000000004c2330c700001c09aa6017c07622528a013a100001f280023506d24800013f96d1fc94909996200000a8f68000000001be0c821d00013d1ed17e9ef80023b83d9b40d68000002941220660240000000002001388e80958269750b5a9c108987a2800018100d0eb99096708389c9b1a1e06321b9b49d8a7001a99b16f03a8c789e20b00012122d22717a0bc0749b3a5482009b23f8029de1800ee12999285c26187da6e9cd8880f01e518a10f8002630000e0a35a4b8252121e68000ae86d8d3000136a260879310d7a758508932290ca00019da888a512a90080005995b22c8d98002220649e98002900ba1bf0002158711e783c87697b00023d8be02086c95895594607b0000a88001cb23f00028504fa9514d8d899525e9aa95d1c402f97f94f104a1e82a1c9
  | 9 => 0x1e40340ef19616a22a0080c392f12fa8ea5b933298276a6a10da4881a00a0e19d380316826599900006a9a628180019198e84d89d8b80588339429ba8078af8729922118c60000e98002458cf23c2821b10740a598b2300b324419a92025e1cba5c11987927121c9c78ea9208a3a6d8d40001a40738002348002451d08a728299c0e394d1bb0c9251067a1c28b180a0304986b0dea4f28d2168dd1de86814718697d09487085aa0806ba010d616fa771
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x18d1675d88410c68abaec420863455d66210431d0ac43108218c9676d48410c64abb6a420863255da5210431e0aa42908218d1775580410c6c3b92c020863611c96010431b0ce43008218d8572180410c64b3b082a8063a1d884154031d08c420aa018e8662104500c742b108228063451cd6510621a28e8b286310e1663106508870b3206328443459ce5310521a64e12988290e1665106314868b3ac8218a43459d2540c521aa4e12a06290f105310750487882a063a8243c410431d4121a64ea208a090f135310450487882988228243549d43114121e26a8188a090f10540c450486a939e8228243589cb4114121a64e9988a090d6272cc4504878820c6228243c49043114121e2082188a090d3274c8450486a939e4228243c81062114121e8063108a090c547158e540861a38ac929843a89046048421d84623024210c947158f42d028a39aa220e81159c76354a40c28a630a86a05247150c525024a38ac7a12818358c52d0940a2ae7a10a2a051671d4c415028b39ea220a8185994410c540e0ea420862a070452104315030bba0c2a9881851d06154c40a28e2a9c86205147154c431028a38aa7210818554e6190840a28e2a9884205147154e411028a38aa62088185d94410c440a28e2a9e80205147154d4010306a98c4a00818554c6150040c28a830a87984947159332cc28a3a2a218e61459c75410e3086ce3b22a5185147158c544c30a2a0c2a1a61511c54314930928e2b26649841d76153324c306b20a599261455d33214530a2ce3aa0629851674d44314c28b3a88218a61c1d48410c530e08a4208629861463185540c30bb98c2aa061851cc6155030a28e2aa6861851471550430c20fbb2a919061451c5548c830c2aa930c641851471550320c28a38aa918861451c5540c430a2eea208621851471553300c20e3b2a898061451c5544c030c1aa8312601861554185300c22a38ac72a6410d1c56494f20a28e6a8883905147454431c822a38ac62a4410d1c56414e20c2cc931ea2906146418c514828b38ea620a41459cf5110520a2ce3aa0629051674d44314828b3a88218a41451d4410c520c2cca208629061465104314830a320c728841851906354420c60c8302a21065063181510828a38aa620841451cd5110420a28e2aa0621051474544310828bba88218841455d4410c420c2eca2086210615651043108292ba88310841515d43188420a2ce7a90830851674d48318428a388a818a21459d4410c510c2cca20862887075210431443822908218a218c1506048510ca0a6302428866052181214428a39aca208210d5d85310410a4ae429882085147354841042d0392c020821451d1650c4108aaec2a0620854572150310428a3a2a418821701c9600c410c2cc620ca008616640c65004318b288210021945943108010
  | 1 => 0x191a276042a4b258419fcf8c66489d14535422c8ec8342d0a263710017ad31cb04d41f0b0755aa72d0394c2a70a88904337afd241c462ed04b62a9c5b88d0036d56e06800186cd4b2b0706b2b000227b009dc00034eae082bc4a0892a6c2d80000b35b80016811303c1a9a00000e028000010c8e000c856360f20000935cab8ca001029400900025da84e3f000b8c7108cd3e006780026144e331b4000382400000000000874d80034450006000d637151088833a3cc23c4c030fac4312809e1b1886400343d00000c0002c092743680000780000000423317c80051182974a3429e4bcdf000b8585218364c03f398b400ce00375124c589c820000012d48be12800ea025532964c56f0916a371f278a0d70215da4a1148f522d826b8c742f1d9742446031102ac2001286a000035532690babd96000c002000081c080208808141805040026e0280006000180000001301c06000380c0c09008642001000280601020384400028281a0801810540000010040200010440000004160701800024f0080c0a0d000101004a4ce5b20a2a1d4672d8c5150f0bb28c2a188785dd46150c43a1ee4a1ca421d147150e5210f0aa1cc329087451c54394443a28e2a1aa021e0d431895010f0aa18c2a808785dd06154f42c28e830aa7a15147154e43d0a8a38aa621e858594c6150e42928e2b1e852151573d0a5190a2a38ac628285251c563d0842c28c630aa9996177318554ccb0a398c2aa665451c554d0f32a28e2aa087995147158e548cb0b2a0c2a1c65251c564cca3283aed2a6651951574cca518ca8a38aa821a65461c15410d32868e2b20a09961454185430ca4a38ac999065459c75394e4192ce3b1aa520c9473586421064a39ac221083251c56394841928e6b14a220c9673982511068b38ea92a463259c76454a31928e8b0c6418c9474584320c70ab288620863495ca651043192aed1908218f05520c8410c64a38ac929063251d1629443192ce9304a218cc572d94410c68abac8420863a15884210431b0ce5b288218d8572d94410c6c3394ca20863615ca6510431c2aca32882
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x10080439586180004ada0401400dada0682dd46150c43a048150c6254043a0682dd06154f42a0682dcc6155332814865d33294632a048158c52d0940a0682dd06154c40a048154c6250040a048159052cc930814865d33214530a0682dcc615503081487552618c830a0481550624c03081487550614c030
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 890
  | 4 => 1340
  | 3 => 228
  | 2 => 14
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (i*5) 5
  | 6 => packedAt s0K6 (i*16) 16
  | 5 => packedAt s0K5 (i*27) 27
  | 4 => packedAt s0K4 (i*38) 38
  | 3 => packedAt s0K3 (i*49) 49
  | 2 => packedAt s0K2 (i*60) 60
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (6+((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s0K6 (788+((h/14+packedAt s0K6 (704+(h % 14)*6) 6) % 53)*7) 7
  | 5 => packedAt s0K5 (27286+((h/296+packedAt s0K5 (24030+(h % 296)*11) 11) % 1719)*11) 11
  | 4 => packedAt s0K4 (55826+((h/446+packedAt s0K4 (50920+(h % 446)*11) 11) % 1609)*12) 12
  | 3 => packedAt s0K3 (11856+((h/76+packedAt s0K3 (11172+(h % 76)*9) 9) % 274)*9) 9
  | 2 => packedAt s0K2 (860+((h/4+packedAt s0K2 (840+(h % 4)*5) 5) % 20)*5) 5
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffff81ffffffffffffff0fffff
  | 2 => 0xfff01fff80fff80ffe0ffe07ff03ff80f39e7c
  | 3 => 0xfffe07fff03fffffff03ff81ffc0ffffce38f
  | 4 => 0xf000007ffffc000fffffc0001ffff000ff03f0
  | 5 => 0xffffff800000000fffffffffe0000000fffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x12114210922092020052ca8a254510aa052cb5
  | 2 => 0xa4a4c5290e492155960556454b22ad0672965c
  | 3 => 0x88c2894a241a4549aaa0255112a88e54b8c30a
  | 4 => 0xce8b16744890766ecd3981861cf3c418df03e0
  | 5 => 0xf0c187870e3878f71ce39e780c30860eff800
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcc0ccc0ccc0cc00fcc0ccc0ccc0cc00fcc0ccc0ccc0cc00fcc0ccc0ccc0cc00fcc0ccc0ccc0cc00fcc0ccc0ccc0cc00fcc0ccc0ccc0cc00fcc0ccc0ccc0cc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_36963
namespace PEqualNP.Outside.L_meta_36963
open PEqualNP.Outside.L_meta_36963.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x60c928010034c4052c000220000e04f1c000000400c09be43bc43ef42be42bc42ec42ac42ef32ec32be41bc41ee21ec21bf40bd40ef20ed20
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x32412200000068201200621e520000a0040a39c59898050a0c004b94a439b28c872e5290a5ca6214b9444296a80852e54ccacca3994b150328f29c832e529065ca910d394e21962a0431c5350258a4a04d14540962a6412c5448298a6905914520
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x30110899865310a0e63944428318d5010a246154042
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 21
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
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (297+((h/5+packedAt s1K4 (272+(h % 5)*5) 5) % 27)*6) 6
  | 3 => packedAt s1K3 (602+((h/7+packedAt s1K3 (567+(h % 7)*5) 5) % 30)*6) 6
  | 2 => packedAt s1K2 (155+((h/1+packedAt s1K2 (152+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffff03ffffffffffffff87ffff
  | 2 => 0x7ffffc0fe03fffffc1e07fff03e07fff93e4f
  | 3 => 0x7f03fff0003f01fffe007c0ffc007e07e338c
  | 4 => 0xf8003ffffffc001ffffff800fffff8007fc3f0
  | 5 => 0xffffc0000000001fffffffff000000007ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x101084482440820200a4494914429229025495
  | 2 => 0xa2a3188648952c8d2c0a82b262342556392a4a
  | 3 => 0x54c5ad121d5a46b7556144d8be9057835e338c
  | 4 => 0x668a3224919068d99a539020cb3961046d8360
  | 5 => 0x870c3c38e1e38f1ee39de73c0c21861877fc00
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaa0a0aaaaa0a0faaaa0a0aaaaa0a0faaaa0a0aaaaa0a0faaaa0a0aaaaa0a0faaaa0a0aaaaa0a0faaaa0a0aaaaa0a0faaaa0a0aaaaa0a0faaaa0a0aaaaa0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_36963
namespace PEqualNP.Outside.L_meta_36963
open PEqualNP.Outside.L_meta_36963.Model
def s2K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (i*4) 4
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (5+((h/1+packedAt s2K3 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 1 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 3 => 0xebfc1f3fe03f8f1c
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4061010824892131
  | 1 => 0x2088281109124486
  | 3 => 0x1523506a42a52b18
  | 4 => 0xe0a1ab493064ec0
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 27 s2Pos s2Neg, 0xeeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_36963
namespace PEqualNP.Outside.L_meta_36963
open PEqualNP.Outside.L_meta_36963.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x1d345d7281e352a300bc0801c0010b0060b2b102489e400051b000000044503ac54641954e4c29c4c909103e1060052010865a0000034000820041412f0006ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1c994021d00200006313845081c16950762b0014cb41206140dc4f3d1485800000f4747600010fc34208802e003e0000438000d80000271a8f224129e0345d0c9c83e473a0849664201705c6f19a0ce0002288c2c62340f0aa691a834ac460a1ac5460051980661048fc167b188202044389b09277000c0ea673e800ae5b099649a3242920367300000da5e408982a001780044510010c007f00000000007000524c2f8180037000f8000f252083c581401c0a1821000044008280008902454300070786004980c3408081c241c00ac3000b8042000000000142c00482078000c1e7ca5a1cf947439ea86873d5490f3ea6a1cf149439e28a873f5050e7ca821cf54e429f294853e5190a7aa1215794c42aea98859e5310a7aa6216754c428ea98853e5210b5ca4214f944429ea80853e54cca7aa9996750f32bb28e657551cca7ea9194f152329faa2653c544cb3a86994f950329eaa0653d539067ca520cf946419ea84835e53106baa620e794c419ea98839d531063aa620cf948419f28883b6511067aa020cf953319eaa6639d43cc6dca598db54b319faa4633c548c67ea898cf15131cea1a633e540c67aa818cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710cfd51219e2a2433f5408678a810f948421af29e815d53d033ca7a04f54f40cea9e811d53d027ca5a04f947409eaa4813f5350278a4a04f14540dda82813e541027ca9984f553309f2a4613d548c33a87184f951309eaa2613e540c27aa8186750c30b7290616d520c2eca2185d544309faa6413c54c827ca9104f552209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2e20458a000400a989200001808b250c0acc12a0e69e7260200e128a08758e5190a1f6354242c550d51cca3661d523287195434ca8c6250d328758e529061f6354241c350d52cc62e62d523187195434c6946150d318758c544861d63150218e580540861d63149408758c515021d63951308b189544c2346155130c350d520c31543544308758c54c821d63952208758c54c421d6395210
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
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
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (864+((h/16+packedAt s3K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s3K4 (3970+((h/44+packedAt s3K4 (3618+(h % 44)*8) 8) % 161)*9) 9
  | 3 => packedAt s3K3 (1028+((h/8+packedAt s3K3 (988+(h % 8)*5) 5) % 32)*6) 6
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffff0ffffffff81ffff07ff07fffffe78f1ff
  | 1 => 0xf07fff03f07e1ffe1e0ff87ff878383fa73e93
  | 2 => 0xff83fffc007fe1ffe00fff87ff803fc1c7cf1c
  | 4 => 0x3ffffff8001fffff00007ffffc001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x800010208010000044120088008a0a10085025
  | 1 => 0x2519221924a430960a854853485090aca32692
  | 2 => 0x432a44486949032aa109950595012585458b18
  | 4 => 0x6a5388924c0d55cd33a0c446e6658109f00dc0
  | 5 => 0x8c630ee38e7199f1ddcee660c4460631fef000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8eaeae8e8eaeaa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_36963
namespace PEqualNP.Outside.L_meta_36963
open PEqualNP.Outside.L_meta_36963.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x40028e602400594281808080a3bf43bd43be42bc42be41bc41de31dc31bf40bd40df30dd30
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x800c108ea98852e52906b2a018cb14940
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
  | 4 => packedAt s4K4 (212+((h/4+packedAt s4K4 (192+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s4K3 (111+((h/1+packedAt s4K3 (108+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffff83ff83fffe0ff83c3ffc3fe07ffee0f39f
  | 1 => 0x3fffc1ffff07ff07fffc1ffc1fff03f3f3cf3
  | 2 => 0xfc1fffe003ff87ff803ffe1ffe007fc1c7cf1c
  | 3 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x1088888424a442029a08132813221518605185
  | 1 => 0x484110490100805020544044404920a40b2432
  | 2 => 0x295221434a480cb50426a416a4054a85858e18
  | 3 => 0xb29c4a12606d5729ce82311b39960309f00bc0
  | 5 => 0xc318739c738e67ce773b398231180c31fef000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xece8ece8eca8eca8ece8ece8eca8eca8ece8ece8eca8eca8ece8ece8eca8eca8ece8ece8eca8eca8ece8ece8eca8eca8ece8ece8eca8eca8ece8ece8eca8eca8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_36963
namespace PEqualNP.Outside.L_meta_36963
open PEqualNP.Outside.L_meta_36963.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x410440060a2800054649102a5859c003c1a34e9801e00806252600017361ca0100911211c0001d1a08c0900a00005668f80520800c020010601b005081ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x280f8000000000000011902aa08714000016ad801f2288932100188380150000190d8502a3802d259211010007a615ac85a3000224000b80001da7982209a90c961c00001e800c1a801b9b0319a51284138014a9802197ab0a019f8006ab9c9e0f000e0a800927289d248026908d0e86081a04a000972c002a0b0001080c08026100800000008041c00004146011800281120019db7290876d5210ebca6215754c42d6a10853e540ca7aa8195794f41aea9e836e52d06daa5a0db94a41b6a94835f53506b8a6a0d794631aea84633e540c67aa818db94831b6a90637a500c6f2a018e795031ceaa063ce520c79aa418d794431eb28863da500c6baa018f654031aca80633e54c867aa990d794f21aea9e433e548867aa910d7d4d21ae29a435e53902baa7205bd4940b6292815e53102baa6205b94840b6a90817651102eaa2204f953309eaa6616e52cc2daa5986795330ceaa661ce52cc39aa5985794730aea9c615c514c3b6a0985794c30af29c415d538827ea8904f151209f2a0413d54082bca6105754c20bb288417551082bea7885714f10af29c215d53843b261084fd51109e2a2215f53442b8a6885bd4910b629221d9304427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x468e00a00200c10c354d4210b0d5454831c6951500c7195454031d2949500c7495254031c355152cc258654c110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 92
  | 3 => 8
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
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (788+((h/14+packedAt s5K5 (704+(h % 14)*6) 6) % 58)*7) 7
  | 4 => packedAt s5K4 (2694+((h/30+packedAt s5K4 (2484+(h % 30)*7) 7) % 122)*8) 8
  | 3 => packedAt s5K3 (312+((h/2+packedAt s5K3 (304+(h % 2)*4) 4) % 13)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xc7ffff83fe1fff07f0fe1fffc3f81ffe98f39f
  | 1 => 0xf81f0ffc3fff0ff87f0fe1c1fc3ffc1f674cf3
  | 2 => 0xffe00fffc01ff1ff800ffe01ffc01fe1878f1c
  | 3 => 0xfffffe001fffff00001ffffe001f80fe0
  | 4 => 0xfffff000000001fffffffffe00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x40840088002200009010024480488488081185
  | 1 => 0x82421110940810282106208844124854234432
  | 2 => 0x114aaa218d54835b088b54116a815345858e18
  | 3 => 0x3594cc4a2906a595daa11025b3258189d80bc0
  | 4 => 0x261888733198c9e66ccd993822060211f6e000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeeeaeca8eeeaeca8eeeaeca8eeeaeca8eeeaeca8eeeaeca8eeeaeca8eeeaeca8eeeaeca8eeeaeca8eeeaeca8eeeaeca8eeeaeca8eeeaeca8eeeaeca8eeeaeca8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_36963
namespace PEqualNP.Outside.L_meta_36963
open PEqualNP.Outside.L_meta_36963.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x169217818f048a08010a9e980616088c020019988b9e051c801a00140080148013840f9d02801f001f83069c05801a800d1d83911289002097200e9b0c8e0b101513071580118007800d8010899b8019040608107020400e0a0228480001c0891a1400001ffd5001fe54007f55007fc5401ffd4c05fe53007f54c05fc53007fd0c05fe43007f50c05fc4301ffd4801fe52005f94801fd5201ff148017c52007fd0801fe42007f50801fc42017fcc801fe32007f4c805fc3201ffd4401fe51007f54407fc51007fd0401fe41007f50401fc41017fcc401fe31007f4c405fc31007fc8401fe21007f48401fc2100ffd40037f5000ff94003fd5000df54003fc5000ffd0003fe4000ff50003fc4000ffcc003df3000ff8c003fd3000f74c003fc3000ffc8003fe2000ff48003fc2000ffc4003fe1000ff44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x44204ffc4221027ee2110813fe1088409fe884420dfd44221027f82110803ff65484017fb2a4200dfd9521004feca90833fe65484077f32a4200ff59521005faca90833fc65484077e32a4200df1952101cf8ca90803ff64484017fb224200ff9912104dfcc890803fd64484017eb224200ff1912104df8c890833ff5448401ff2a24200ff55121067f8a890803ff63484017fb1a4200f7d8d21005bec69082ffe63484057f31a4200ff58d21005fac69082ffc63484057e31a4200f718d21015b8c690833ff5348417ff29a4200ff54d2105ff8a690803ff4348417ff21a4200ff50d2105ff88690833ff5248401ff2924200df94921007faa490833fc5248401be2924200ffd0921007fc8490803fd4248401fe212420bffcc921007fc6490803ee3248401fe9924200fb4c92105ff86490833ff5148409ff28a4200ff54521027f8a290803ff4148409ff20a4200ff50521027f8829082fff3148409ff18a4200ff4c521027f86290803ff2148401fb90a4204ff88521027dc429082bff60484157fb02420aff9812100dfcc09082bfd60484157eb02420aff1812100df8c09082bff5048415bfa82420aff94121057faa09082b7d5048415fe282420affd0121057fc809082bfd4048415fe202420affcc121057be609082bfe3048415fe982420af74c121057f8609082bff2048415f7902420aff88121057fa409082bed2048415fe1024204ffc4121057ee209082bfe1048415fe882420afd44121027f82090813ff65084097fb284204ff9942101dfcca10813fd65084017eb284204ff19421025f8ca10813ff64084097fb204204ff9902104dfcc810813fd64084017eb204204ff19021025f8c81081fff5408401ff2a04200ff5502103ff8a810813ff63084097fb184204ff98c21015fcc610813fd63084017eb184204ff18c21025f8c61081fff530840dff2984200ff54c21037f8a610803ff430840dff2184200ff50c21037f88610822fe620840fffa904200ff94821006fca410803fd520840ffe2904200df14821007fe8410803fe4208401fea104200ff10821037fe6410803fe3208401fe9904206ff0c821025fcc210813ff5108409ff2884204ff54421027f8a210813ff4108409ff2084204ff50421027f88210813ff3108409ff1884204ff4c421027f86210813ff2108409f79084204ff88421027ec4210813fd2108409f69084200fd48421027fec010812ff6008409ff3004201bf98021027fac010816fd6008409fe3004201bf1802102ffea0108177f500840bff2804205ff5402102efaa010817fc500840bffa004205ff9002102ffa8010817fc400840bff9804205f7cc02102ffc6010817fd300840bee9804205ff0c02102ffe4010817fe200840bfe9004205ff08021027fe2010813fe1008409fe8804204ff04021
  | 1 => 0xbfd504c425bea826212ff14131097fe809884bfe404c425fea026212ff10131017fe609880bdf304c405ff1826202ff4c131097ba609880bfc304c425ff9026212ff88131097fa409884bfc204c409ff8826212ff84131097fa2098813fc104c401ffb2e4200bfd972108ffccb9080efe65c8401feb2e4200bf5972108ff8cb9080efc65c8401ffb264200bfd9321007fcc990826fe64c8401feb264200bf59321007f8c990826fc64c8423ffaa64200ff95321007faa990847fc54c8401ffb1e4200bfd8f21087fcc79080afe63c8401feb1e4200bf58f21087f8c79080afc63c8423ffa9e4210ff94f21007faa790843fc53c8401ffa1e4210ff90f21007fa8790843fc43c8423ffa964200ff94b21006fca590803fd52c8423fe2964200df14b21007fe8590803fe42c8401fea164200ff10b21087fe6590803fe32c8401f71964200ff4cb21007da6590843fc32c8423ffa8e4204ff94721007faa390813fc51c8401ffa0e4204ff90721007fa8390813fc41c8421ff98e4204ff8c721007fa6390813fc31c8411ffb064208bfd8321047fcc190806fe60c8411feb064208bf58321047f8c190806fc60c8411ffa864208dfd4321047fca190823fd50c8411bea864208ff14321047fe8190823fe40c8411fea064208ff10321047fe6190823df30c8411ff1864208ff4c321047ba6190823fc30c8411ff9064208fbc8321047fc4190823fd20c8411f69064208ff08321027fe2190823fe10c8411fe8864204ff04321027fecb10812ff6588409ff32c4203bf99621026fccb1080e7e6588409feb2c4200bf59621026facb108027d6588409fe32c4204bf19621027fec910812ff6488409ff3244209bf992210277cc910802be6488409feb244200bf592210277ac910802bd6488409fe3244204bf1922107ffea910803fe5488401feaa4420fff15221027fec710812ff6388409ff31c4202bf98e21027fac710802fd6388409fe31c4204bf18e2107ffea71083bfe5388401fea9c420eff14e21007fe871083bfe4388401fea1c420eff10e21055fac51083fff5288401ff2944200df94a21007faa51083ffc5288401be2944200ffd0a21007fc8510803fd4288401fe214420effcca21007fc6510803fd328841dfe1944204bf98621027fea310813fe5188409fea8c4204ff14621027fe8310813fe4188409fea0c4204ff10621027fe6310813fe3188409fe98c4204ff0c621027fe4310813ef2188401fb90c4204ffd8221025fec110813fe60884037f3044204ff5822106dfac110813fc60884037e304420dffd422106efea110837fe508841bfea84420ddf5422106ff8a110837ff408841bff204420dff5022106ff88110837ff308841bef984420dff8c22106ffa6110837dd308841bfe184420dffc822106ffc4110837fd208841bfe1
  | 2 => 0x410277e8220813fe4110409fb2088204ff504410277a8220827f54110409ff9888204ff0c441027fec020812ff6010409ff3008201bf98041027fac02085afd6010409fe3008201bf180410b7fea02085b7f501042dff2808216ff540410b6faa02085bfc5010413ffa008209ff9004104ffa8020827fc401042dff9808216f7cc0410b7fc602085bfd301042dee9808216ff0c0410b7fe402085bfe201042dfe9008216ff08041027fe2020813fe1010409fe8808204ff04041027fecb18812ff658c409ff32c6203bf99631027facb18802fd658c409fe32c6204bf19631027fec918812ff648c409ff3246209bf99231027fac918802fd648c409fe3246204bf192310affea918803fe548c401feaa46215ff15231015fac71880bff538c42befa9c6202ff94e31017faa71880bfc538c405ee29c6202ffd0e31007be871880bfe438c405fea1c6202ff10e31017b88718813ff628c409ff3146200bf98a31027fac518802fd628c409fe3146215ffd4a31007fca5188037e528c401fea946215ff14a31006f8a518803ff428c401ff2146200ff50a31007f8851880bff328c405ff1946200f78ca31017fa651880bfc328c405ee1946204bf98631027fea318813fe518c409fea8c6204ff14631027fe8318813fe418c409fea0c6204ff10631027fe6318813df318c405fb98c6204ff0c631027e86318813ff608c4097fb046204ff9823100dfcc118813fd608c4297eb046204ff1823100df8c118853ff508c429bfa846214ff942310a7faa1188537d508c429fe2846214ffd02310a7fc8118853fd408c429fe2046202ffcc231017be611880bfe308c405fe9846214f74c231017f86118853ff208c429ff1046214ff482310a7f84118813ff108c409ff0846204ff44231027f82118803ff654c4017fb2a6200dfd9531004feca9884ffe654c4077f32a6200ff59531005faca9884ffc654c4077e32a6200df1953101cf8ca98803ff644c4017fb226200ff9913104dfcc898803fd644c4017eb226200ff1913104df8c89884fff544c401ff2a26200ff5513109ff8a898812ff634c405ffa9a6202ff94d31017faa69880bfc534c405ffa1a6202ff90d31017fa869880bfc434c401ffb126200bfd8931007fcc498803fd624c401fe3126200bf1893109ffea498803fe524c401bf2926200ff5493109ff8a4988037c524c401ffa126200ff90931007fa8498803fc424c405ff9926202ff8c931017fa649880bfc324c4057fb0a6213ffd4531027fca298803fd514c409fe28a6200ffd0531027fc8298803fd414c409fe20a6202ffcc531017ee6298813fe314c409ef18a6204ff0c531027b8629880bf4314c425ffb026212bfd8131097fcc098806fe604c425feb026212bf58131097f8c098806fc604c425ffa826212dfd4131097fca09884
  | 3 => 0xf2948200df94a41007faa52087bfc5290401be2948209ffd0a41007fc8520803fd4290413fe214821dffcca41007fc6520803fd329043bfe1948204bf98641027fea320813fe5190409fea8c8204ff14641027fe8320813bf4190413fba0c8204ffcc641027f86320813ff60904097fb048204ff9824100dfcc120813fd60904397eb048204ff1824100df8c120873ff5090439bfa84821cff942410e7faa1208737d5090439fe2848209ffd02410e7fc8120873fd4090413fe204821cffcc2410e7be6120873fe3090439fe984821cf74c2410e7f86120873ff2090439ff104821cff482410e7f84120813ff1090409fb8848204ff84241027fa2120873f51090409fe0848200ffd9541005fecaa08037f65504013fb2a821bff9954101dfccaa0803fd65504017eb2a821bff1954101df8caa08037c65504073e32a821bffd514104ffca8a0803be5450401feaa28200ef5514104ff8a8a0803ff63504017fb1a8200f7d8d41005bec6a086bfe63504057f31a8200ff58d410d7f8c6a080afc6350401ee31a8202b718d410dffea6a086bfe5350401fea9a821aff14d4104ffe86a0803bf4350435ff21a8200ff50d410077a86a0827fc4350401ffb128200bfd8941007fcc4a0803fd6250401fe3128200bf189410dffea4a0803fe5250401bf2928200ff549410dff8a4a08037c5250413ffa128200ff909410077c84a0803fd4250413fe2128200ef109410d7fe64a0803fe3250401fe992821aff0c9410dffea2a0813fe5150401fea8a8204ff1454104ffe82a0827f74150409ff20a8204ef905410d7fe62a0813fc3150433ffb028219bfd81410cffcc0a0806fe6050433feb028219bf581410cff8c0a0806fc6050433ffa828219dfd41410cffca0a0867fd5050433bea828219ff1414104ffe80a0867bf4050433ff2028219ff501410cf7a80a0827fc4050433ff9828219f7cc1410cffc60a0867fd3050433ee9828219ff0c1410cffe40a0867fe2050433fe9028219ff08141027fe20a0867f71050433ff0828219ff441410cfea20a0813fc1050409ffb288204bfd9441027fcca2080efe6510409bf32882039f99441027faca20802fd6510409beb2882009f59441027f8ca20812fc65104137f3208209ffd504104ffca820827fd5410413fe2a08204ffd8c41027fcc62080afe6310409feb188200bf58c41027f8c620812fc6310431ffa988217ff94c41007faa62085ffc5310413ffa188209ff90c4104ffa8620827fc4310409ffb108204ff98841005fcc420813fd62104017eb108204ff188410c7fea420803fe5210401bf2908200ff548410c7f8a4208037c5210413ffa108209ff9084104ffa8420827fc421042fff9908200ff8c841007fa642085ffc32104097f3088204ffd4441027fca220813fd5110409fe2888204ffd04
  | 4 => 0x803fe6454401feb22a200ff1915104df8c8a880fff5454407bfaa2a203ff9515101ffaa8a88037d5454407fe2a2a200ffd8d51005fec6a8803df63544016fb1aa223ff98d51015fcc6a8803fd6354447fe31aa202bf18d51007b8c6a880adc6354407ffa9aa203dfd4d5101ffca6a880ffd5354401bea9aa203ff14d51007fe86a888ffe4354401fea1aa223ff10d51007fec4a8802ff6254401ff312a200ff58951007f8c4a8802fc6254407ffa92a203ff94951006fca4a880ffd5254407fe292a203df14951007fe84a8803fe4254401fea12a200ff1095111ffe64a8803fe3254401fe992a223ff0c95101dfec2a880fff5154407fba8aa204ff94551026fca2a8813fc5154409be28aa203fd1455111ffe62a8813fc3154445ffb02a222bfd8151117fcc0a8806fe6054445feb02a222bf58151117f8c0a8806fc6054407ffa82a203dfd415101ffca0a880ffd5054445bea82a203ff14151117fe80a888bfe4054445fea02a222ff10151117fe60a888bdf3054445ff182a222ff4c151117ba60a888bfc3054445ff902a222ff88151117fa40a888bfc2054409ff882a222ff84151117fa20a8813fc1054413ffb2e8209bfd974104ffccba080efe65d0413feb2e8200bf5974104ff8cba0826fc65d0413ffaa68209ff9534104f7ca9a0827fd54d0401deaa68209ff1534104ffec7a0827fe63d04057f31e8209ff58f41005fac7a0827fc63d04057e31e8221ffd4f41107fca7a0803fd53d0441fe29e8209ffd0f4104f7e87a0827fe43d0413fea1e8200ef50f4104ff887a0827ff62d0413ff3168200bf98b4104ffac5a0802fd62d0413fe3168221ffd4b41007fca5a08037e52d0401fea968221ff14b41006f8a5a0827ff42d0413ff2168200ef90b4104ffa85a0827fc42d0413de2168220ffccb41007fc65a0803fd32d0441fe1968221ffd4741027fca3a0803fd51d0409fe28e8220ffcc741027f863a0827ff60d04137fb068209ff9834100dfcc1a0827fd60d043f7eb068209ff1834100df8c1a087fff50d043fbfa86821fff943410fffaa1a087f7d50d043ffe2868209ffd034104f7e81a0827fe40d0413fea06821fef5034104ff881a087fff30d043fef986821fff8c3410fffa61a087fdd30d043ffe186821fffc83410fffc41a087ffd20d043ffe1068204ffc43410fffc21a087ffd10d0409fe0868204ffd9641025fecb20813fe65904077f32c8204ff59641005facb20813fc65904097e32c8219bf592410f7fea920827fe5490401feaa48209ff15241027fec720813fe63904057f31c8204ff58e41005fac720813fc63904097e31c821effd4e410effca720803fd539043bfe29c8209ffd0e410effc8720803fd4390413fe21c8204ffd8a41027fcc520802fe6290409feb148200bf58a41027f8c52087bff5290401f
  | 5 => 0x4632017fe631900bfc318c805ee18c6428ffd8232145fec1190a3fe608c8037f3046428ff58232145fac1190a3fc608c8037e3046428ffd4232146fea1190a3fe508c851fea846428df54232147f8a1190a3ff408c851ff2046428ff50232147f8811900bff308c805ef9846402ff8c232017fa61190a3dd308c805fe1846428ffc8232147fc41190a3fd208c851fe1046428ffc4232147fc21190a3fd108c851fe0846400ffd9532005feca990037f654c8013fb2a6427ff9953201dfcca99003fd654c8017eb2a6427ff1953201df8ca990037c654c8073e32a6400ffd9132005fec899003fe644c8137f3226400ff59132005fac899003fc644c8137e3226427ffd5132007fca899003fd544c84ffe2a26402bfd8d32017fea69900bfe534c805fea9a6402ff14d32017fe869900bfe434c805fea1a6402ff10d32015fec49909fff524c801ff2926400df94932007faa49909ffc524c801be2926400ffd0932007fc8499003fd424c801fe2126402ffcc932017de649900bfe324c801ef1926402ff0c932017b8649900bec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6404bf1853213ffea29909ffc514c805ff98a6402ff0c532137fec09909aff604c84dff3026401bf98132137fac09909afd604c84dfe3026401bf18132137fea09909b7f504c84dff2826426ff54132136faa09909bfc504c84dffa026426ff90132137fa809909bfc404c805ff9826402f7cc132017fc609900bfd304c84dee9826402ff0c132137fe409909bfe204c84dfe9026426ff08132137fe209909bfe104c84dfe8826426ff0413201dfacb28813ff6494409ff324a209bf99251027fac928802fd6494409fe324a203ffd525101ffca9288037e5494407feaa4a203ff1525101ef8a928813ff6394409ff31ca202bf98e51027fac728802fd6394409fe31ca204bf18e5101ffea72880ffe539444bbf29ca203ff54e5101ff8a72880f7c5394401ffa1ca225ff90e51007fa8728897fc4394409ffb14a204ff98a51005fcc528813fd62944017eb14a204ff18a5101ffea52880ffe5294401bf294a203ff54a5101ff8a52880f7c5294401ffa14a200ff90a51007fa8528803fc429444bff994a200ff8ca51007fa6528897fc32944097f30ca204ffd4651026fea32880ff75194409fe28ca204fd14651027fe6328813fc3194409ffb04a204bfd8251027fcc128806fe6094409feb04a224bf58251027f8c128806fc6094407ffa84a203dfd425101ffca12880ffd5094449bea84a203ff14251127fe8128893fe4094449fea04a224ff10251127fe6128893df3094449ff184a224ff4c251127ba6128893fc3094449ff904a224ff88251127fa4128893fc2094409ff884a204ff84251027fa2128813fc10944097fb2aa200ffd9151005fec8a8
  | 6 => 0x77e32a8400df1954201cf8caa10c3ff5450813ff2a28400ff5514204ff8a8a1003ff63508017fb1a842fff98d42015fcc6a1003fd635085ffe31a8402bf18d42187fea6a10bffe5350801fea9a842fff14d4204ffe86a10bffe4350801fea1a8409ff10d42187fea4a1003fe5250801bf2928400ff54942187f8a4a10037c5250813ffa128409fbd0942007fc84a1003be425085fff992842fff0c942007fec2a1002ff6150801ff30a8400ff58542007f8c2a1012fc6150861ffa8a8430ff1454217ffe62a10bffc315085dffb02842ebfd8142177fcc0a1006fe605085dfeb02842ebf58142177f8c0a1006fc605085dffa82842edfd4142177fca0a10bbfd505085dbea82842eff1414204ffe80a10bbbf405085dff202842eff501421777a80a1027fc405085dff982842ef7cc142177fc60a10bbfd305085dee982842eff0c142177fe40a10bbef205085dff102842eff48142177da40a10bbfc205085dff882842eff84142177fa20a10bbfc1050813ffb288409bfd944204ffcca2100efe6510813feb288400bf5944204ff8ca21026fc65108137f3208409ffd504204ffca821027fd5410813fe2a08409ffd8c4204ffcc62100afe6310813feb188400bf58c4204ff8c62100afc6310859ffa98842bff94c42007faa6210affc5310813ffa188409ff90c4204ffa8621027fc431085b7f310842cffd4842007fca4210037e5210801fea90842cff14842006f8a421027ff4210813dfa108409ff9084204fdc8421027fd4210801dea108409fb508420075a84210afff3210857fe1908409ffd844204ffcc221012fe6110813feb088400bf5844204ff8c2210b3ff5110859fe288842bffcc44215ff86221027ff60108137fb008409ff9804200dfcc021027fd60108557eb008409ff1804200df8c0210abff5010855bfa80842aff94042157faa0210ab7d5010855fe2808409ffd004204ffc80210abbe4010813fea008409ff1004204f7880210abff3010855ef980842aff8c042157fa60210abdd3010855fe180842affc8042157fc40210abfd2010855fe100842affc4042157fc20210abfd1010855fe0808400ffd9632005fecb190a7fe658c8077f32c6400ff59632005facb190a7fc658c8077e32c6400ffd9232005fec919003fe648c8137f3246400ff59232005fac919003fc648c8137e3246429ffd5232007fca919003fd548c853fe2a46402bf58e32017fea71900bfe538c805fea9c6402ff14e32017fe871900bfe438c805fea1c6402ff10e32015fcc5190a7ff528c801ff2946400df94a32007faa5190a7fc528c801be2946400ffd0a32007fc8519003fd428c801fe2146402ffcca32017be651900bef328c805fe1946402fb0ca32007fec319003fe618c8097f30c6400ff58632005fac319003fc618c853ffa8c6429ff1
  | 7 => 0x2900f7f6314807bf318a403df58c5201ef8c6290037f431486fbf218a400df50c521bef8862900f7e62148713f310a403db988521befe64290df7c3214807bfb08a403df9845201efac22900f7c611486fbf988a437df0c45201efec02900e7f6014807bf300a403df580521b4fac02900f7c601486dbfa00a436df900521b6fa80290db7c401486dbf980a436d7cc0521b6fc60290db7d301486dae980a436df0c0521b6fe40290db7e201486dbe900a436df080521b6fe20290db7e101486dbe880a436df0405204ffecba1026ff65d0813ff32e8403bf9974204efccba100e7e65d0813feb2e8400bf5974204efacba10027d65d0813fe32e8409bf1974204ffea9a1027fe54d0813feaa68409ff1534204ffec7a1027fe63d08057f31e8409ff58f42005fac7a1027fc63d08057e31e8435ffd4f421a7fca7a1003fd53d0869fe29e8409ffd0f4204ffc87a1027fd43d0813fe21e8435ffd4b42007fca5a10037e52d0801fea968435ff14b42006f8a5a10d3ff32d0869fe1968409ffd874204ffcc3a1012fe61d0813feb0e8400bf5874204ff8c3a10d7ff51d086bfe28e8434ffcc7421a7f863a1027ff60d08137fb068409ff9834200dfcc1a1027fd60d08677eb068409ff1834200df8c1a10cfff50d0867bfa868433ff9434219ffaa1a10cf7d50d0867fe2868409ffd034204f7e81a1027fe40d0813fea068433ef5034204ff881a10cfff30d0867ef9868433ff8c34219ffa61a10cfdd30d0867fe1868433ffc834219ffc41a10cffd20d0867fe1068433ffc434219ffc21a10cffd10d0867fe0868400ffd9642005fecb210cbfe65908077f32c8400ff59642005facb210cbfc65908077e32c842ebf59242197fea921027fe5490801feaa48409ff15242007fec7210c7fe63908057f31c8400ff58e42005fac7210c7fc63908057e31c8432ffd4e4218ffca721003fd5390863fe29c8409ffd0e4218ffc8721003fd4390813fe21c8409bf98a42197fea521003fe5290801bf2948400ff54a42197f8a5210037c5290813ffa148400efd0a4204fde85210c7ff3290863fe1948400ffd8642007fcc321012fe6190801feb0c8400bf58642007f8c3210cbff5190865fe28c8431ffcc64218ff863210b7ff609085b7fb04842dff9824200dfcc1210b7fd609085b7eb04842dff1824200df8c1210b7ff509085bbfa84842dff9424216ffaa1210b77d509085bfe2848409ffd024216ffc81210b7be409085bfea048409ff1024216f7881210b7ff309085bef984842dff8c24216ffa61210b7dd309085bfe184842dffc824216fde41210b7fe209085bfe904842dfb4824216ff841210b7ff109085bff084842dff4424216ff82121003ff65508017fb2a8400dfd9542004fecaa10c3fe65508077f32a8400ff59542005facaa10c3fc655080
  | 8 => 0xf881431e7fa40a18f3fc2050c79ff882863cff841431e7fa20a18f3fc1050c077eb2ca400ffd9252007fcc929026fe6494801feb24a400bf59252007f8c92900fff5494807bfaa4a403ff95252006fca92900ffd5494801beaa4a403ff1525201ef8a929003ff6394877ff31ca402bf98e52007fac729002fd6394877fe31ca402bf18e5201ffea72900f7f5394807ff29ca43bdf94e5201ffaa7290037d5394807fe29ca403df14e52007fe87290effe4394801fea1ca43bff10e5201dfcc52900fff5294807bfa94a403fbd4a5201ff8a52900fec5294877ff994a43bff0ca52007fec329003fe61948097f30ca400ff58652005fac329003fc6194807ffa8ca403dfd465201ff8a32900f7c5194877ff98ca43bff0c6521c7fec1290e2ff6094871ff304a401bf982521c7fac1290e2fd6094871fe304a401bf1825201ffea12900f7f5094807ff284a438df9425201ffaa1290e37d5094807fe284a403df142521c7fe81290e3fe4094871fea04a438ff102521c7fe61290e3df3094871ff184a438ff4c2521c7ba61290e3fc3094871ff904a438ff882521c7fa41290e3fc2094871ff884a438ff842521c7fa21290e3fc1094801bfb24a400df99252006fac9290037c6494801bfb1ca43bdf98e52006fac7290ef7c6394801bfa1ca43bdf90e52006fa87290ef7c43948073f314a43bdfcca521def865290037f6194801bf30ca400df58652006f8c3290ef7f3194877be18ca438dfd82521c4fec1290e37e6094871beb04a4389f582521c6f8c1290e37f4094871bf204a438df502521c6f881290e37f3094871af984a438df8c2521c6fa61290e35d3094871be184a438dfc82521c6fc41290e37d2094871be104a438dfc42521c6fc21290e37d1094871be084a403bfd9552007fec8a9002ff6454801ff322a400ff59152007f8c8a9026fc6454807ffaa2a403ff9515201ffaa8a900ffc5454801ffb1aa400bfd8d521d7fcc6a900afe6354801feb1aa43aff18d52015f8c6a900fff5354807ff29aa403ff54d5201ff8a6a9003ff4354875ff21aa400ff50d521d7f886a900eff6254807ffa92a403fbd495201ffca4a90037e5254807fe292a403df1495201fd8a4a90ebff3254875fe192a400ffd8552005fec2a9003fe6154801feb0aa400ff18552025f8c2a900fff5154807fe28aa43affcc5521d7f862a90e7ff60548737fb02a439ff9815200dfcc0a90e7fd60548737eb02a439ff1815200df8c0a900fff5054807bfa82a403ff9415201ffaa0a90e77d5054807fe282a439ffd01521cffc80a90e7fd4054873fe202a439ffcc1521cfbe60a90e7fe3054873fe982a439f74c1521cff860a90e7ff2054873ff102a439ff481521cff840a90e7ff1054873ff082a439ff441521cff820a900f7f6414807bf320a403df5905201ef8c8
  | 9 => 0xc137e322a603ffd515301ffca8a98037e5454c07feaa2a603ff1515301ef8a8a980aff6354c05ffa9aa603f7d4d53017fca6a980b7e5354c05fe29aa602df14d53017b8a6a980bfe4354c05fe21aa600ffd8953005fec4a9803fe6254c01feb12a600ff18953005f8c4a980fff5254c07fe292a603df14953017fe64a980bfc3254c01ffb0aa600bfd8553007fcc2a9803fd6154c01fe30aa604bf1855301ffea2a980f7f5154c07fe28aa602ffcc553017f862a9903ff6054c817fb02a640ff9815300dfcc0a9903fd6054c817eb02a640ff1815300df8c0a980fff5054c07bfa82a603ff9415301ffaa0a99037d5054c07fe282a640ffd0153207fc80a9903fd4054c81fe202a602ffcc153017be60a980bfe3054c05fe982a640f74c153017f860a9903ff2054c81ff102a640ff48153207f840a9903ff1054c81ff082a640ff44153207f820a9827ff65d0c137fb2e8609ff9974301dfccba18277e65d0c073f32e8609ff59743005facba18277d65d0c013eb2e8609ff1974304df8cba180afe64d0c13ffaa68609ff9534304ffaa9a1827fc54d0c057eb1e8602ffd4f43017fca7a180bfd53d0c05fe29e8602ff90f430177c87a180bde43d0c05fe21e8602ef10f4304ffec5a1827fe62d0c017f3168609ff58b43005fac5a1827fc62d0c7fffa96863fff14b43017fe65a180bfc32d0c13ffb0e8609ff98743025fcc3a1827fd61d0c017eb0e8609ff187431fffea3a18fffc51d0c05ff98e8602ff0c743017b863a1827ff60d0c137fb068609ff9834300dfcc1a1827fd60d0c7d7eb068609ff1834300df8c1a18fbff50d0c7dbfa86863eff943431f7faa1a18fb7d50d0c7dfe2868609ffd034304ffc81a1827fd40d0c13fe2068602ffcc343017be61a180bfe30d0c05fe986863ef74c343017f861a18fbff20d0c7dff106863eff483431f7f841a18fbff10d0c7dff086863eff443431f7f821a1803ff6550c017fb2a863dff9954301dfccaa1803fd6550c017eb2a863dff1954301df8caa180aff6450c7bffaa28609ff95143007faa8a1827fc5450c057fb1a8602ffd4d43017fca6a180bfd5350c05fe29a8602ffd0d4304fbe86a180bfe4350c05df21a8602ff10d430177886a180bdc4350c01ffb128600bfd8943007fcc4a1803fd6250c01fe3128600bf189431effea4a18f7fc5250c05ff9928602ff0c943007fec2a1802ff6150c01ff30a8600ff58543007f8c2a1812fc6150c7bffa8a863dff14543017fe62a180bfc3150c79ffb02863cbfd81431e7fcc0a1806fe6050c79feb02863cbf581431e7f8c0a1806fc6050c79ffa82863cdfd41431e7fca0a18f3fd5050c79bea82863cff1414304ffe80a18f3fe4050c79fea028609ff10143017fe60a180bdf3050c05ff1828602ff4c1431e7ba60a180bfc3050c79ff902863cf
  | 10 => 0x2600000100400300100000b00700000300100000900100900900c00001000000200100200200200600200500100100200200200400100b00200001900200800600300000301400100300400300800100300100100200000000100400f00100000300200000400a00100c00000300101b00200100900300000200000300100000000000100300700003800800900000100000300800500900300000000800100900100701400b00000100400b00000d00000100c00500201000500700100200300300400200100500100001200700500000800800700000000700200700600000400301c00000d00500b00000800100300000100600500200400100101200000c00000000200500000000202002d00100600a00000f00200000100100600000600000000000501dfacb2a026fe6495013ffaa4a809dfd525401f7ea92a00f3f5495013fe2a4a809ef1525404ffec72a027fe63950057f31ca809ff58e54005fac72a027fc63950057e31ca803ffd4e5401efea72a00ffe5395007fe29ca809ff90e5404ff8872a027ff6295013ff314a800bf98a5404ffac52a002fd6295013fe314a803ffd4a5401ff8a52a00f7c5295089ff994a844ff0ca5404ffec32a027fe61950097f30ca809ff58654005fac32a027fc6195007ffa8ca803ff1465401ef8a32a113ff3195089fe18ca809ffd825404dfec12a027fe60950037f304a809ff5825421dfac12a027fc60950037e304a803ffd425401efea12a00ffe5095007fea84a843df5425401ff8a12a027ff4095013ff204a809ff5025404ff8812a10fff3095087ef984a843ff8c25421ffa612a10fdd3095087fe184a843ffc825421ffc412a10ffd2095087fe104a843ffc425421ffc212a10ffd1095087fe084a809bfd955401dfec8aa00fff5455007dfaa2a809ff9515404efca8aa027fc5455013be2a2a803ef15154007fec6aa002ff6355085ff31aa802bf98d54007fac6aa10bfc63550057e31aa803ffd4d5401ffca6aa10b7e5355007fe29aa803df14d54217fc86aa027fc4355001ffb12a800bfd8954007fcc4aa003fd6255001fe312a800bf1895401ffea4aa00ffc5255007be292a842ffcc954217f864aa003ff61550017fb0aa800ff98554007fac2aa003fc61550097e30aa803ffd455401efea2aa00ffc5155085ff98aa842ff0c55420ffec0aa106ff6055083ff302a801bf9815420ffac0aa106fd6055083fe302a801bf1815401ffea0aa00f7f5055007ff282a803ff5415420efaa0aa00ffc5055013ffa02a841ff9015420ffa80aa027fc4055083ff982a841f7cc15420ffc60aa107fd3055083ee982a841ff0c15420ffe40aa107fe2055083fe902a841ff0815420ffe20aa107fe1055083fe882a841ff04154015fecaa9803ff6454c017fb22a600ff99153007fac8a9803fc6454
  | 11 => 0xbc1c03320001010de408f38f192420c2761ff8894b200003af80008807c500000011667e100022d000073720b8000a7e81025294200000000000000cca91b38d0bb4ee000000000000327ed36e000023c0000000138db07172dc0214000000191800000075b00000005f21a747380007a460424d8000c5e16d3fb9e0004c0002bf8000be800800300100000200600000100401d00f00002200a00c00100000000000000900300000200000000200b01400100001201100500400000000600600200600800500200200900800501200500b00200100500e00800000300000c02700300900a00a00000200000100300100a00100000500400900000800000000200600000100700000000200100000301500400a00000300100b00000200100300000000000500300000000300100500200500001b01600400000000000b00000700200400300e00900200400c00000b00100000002400d00500500100000100000600100300900400000f00000000200300400000000200000000200300200100f00000500100000000500400000400400100c00600200900b00801601e00000001800200100200200800800700101200500501000100700500700700001402800000000100f00d00000100300100700000800000100000b00100100800300100000100800000400800400200000100000e00300300100100b01100600201601600500300200100b01100b00100500100000400000a00201301e00d00500a00000000300400300001400f01300500400100000300b00700500000200100901600b00100200300300b00500200000300200a02e00600900100900000200000100000100400000900200300100003800500000100500500600000800200300800500200400500401900000500200000200200100d00f00c00d00400000200200200300000200100200300a00700001d01800000400300000000c00600100200000300100000401d00900300100300a00600000000100300300100100100000300100101300400100400000100300500000000a00500100200000400200000000000700000000000900c00000400000200100600200000100200a00e00000300001100200501400100e00000001700300000c00100000000100c00200002200100400001600200b00100300100000101600200b00500000300100200a01200300100f00500101400000800400101a00500000700e00200000300100600200300400000900100000000100800100100000800700100300000800200000300501900200100200600a00300700000200700800500000300300700100000000100800a01100300200000400701000000200000000100100600300300000000000b00800300000900900800100000100000100000d0000040000030000000090010010010
  | 12 => 0xdd00021f10fe6bb00011748060000001b2cece00022f18dc11407e09409245b05af0a38a410ba3d503a9bc101c17f3e1a414000000000000051493b07b21791e478c2740f2921400016580ec26a2bb2598ecc0006133a98b6868044e00012689c000040d85dd0400000002218e302952370f0c15e39746e800006c00030f82784846eb00000011340003f81efce888d308b98a036418b3ce9888d9439346f0edc36e0003a2830400050111e85e41703af00012248b200000a000000019b31e0000a4a3c627102b910a05c06ca384000038000000122c0000000d5c000000240a2b495a7a8000087d22a00005980009fa34e000000012000035e00009a830911f8330c1c75d11417dc000146000109899a3e849321b400068b4340c080a600000000008f65c8259171c34a00013f09e49066e60281a44c8479c011800110080600001e0000740163800108625c00014ec0009301da9dccef084836a19c8a6c2911308ba912e53006100000001de2ff000027c0002e780000004581829bfc1ac0000000dc8cf00003ae1f48f1a4083e110e8dde0003161e14d7e6ac28904f527815505e04c4c4a0000f6000065463836680006fa05f14d24e4b121321cd12fca308fd00000040005f5195a0fcdb693a00000000005c10b000008580004098000000000000184481855848f800000055510602d864850415623fc6c45ed2b52480e0c00042011c844c7d913400000000e934100008ca57000006a814681533b800045c3361e9945d15070b39f81446e60000bea1ac1ae00029021c05de8bc0341eec6fc83e32400011580004169d691c86a527309f00001ac000000000000020903dc5161823bd8f50000281000000000000016a1dd89d8000136800083c8f30a120b8a983693d81928b6e47a2b796d4af4000000133840e0b040581f48e80003590d501e018f24f80000005c000000005f000000023589e88c30499d3090e1233299a9000000000016e926655300000000001022c28be91a268d1f11d50c860cf00005f80007140548774b4c54b249020482c1831c686352545a500000009ce4a10000ea91184ed486994041038402da4ac000227000004000000009716103b02f32d980007326ec417a08cc3651a0000a98c2c70800019e80000000000000652896000071cba017210d9364d667213ee9a1cbc04dc0ad9fbcdee942371082c374605221106cdec2b449e8768f94488130187809e4c507a9f24000493000237000000007d84d0ebc554429a18c76484e0001e880001f92af826802e00041a00002141930169ca48fc0c302f000033c0000b29c38ffe5723078cd400022227b00005dc2740f98b946c646b2da11147248542c711205a44532f998e4f260cd00000000001891c2a3e91c08650708e2022c8db2fc1e68bba80d11913cc3f45ac3b710
  | 13 => 0x1c8ce000017f83fc0005a143c0298fd400038509348403ab00021a4a2000046696a0e7669a443902ca880000001f009480000000c4050600000000940000ab00000000005630310514ca800013d165c82a0000001f3820a6fb000000000053c0000000fa64b115f1df8be270017b0001132774225800000089f0000770f2a3ba2cf15a0000000000000126e000000000059e00015b00000000003c314f92707ae0ce242c00000045180000006e300002f8b2443d26500006d084a0001898f4a000000029c0007b34108b0c1583a73f88e8801c48d0e2115ce780093378000cc65d64208b980002b507293e45ea0db0f78d3c77850f0dc1900f7059641b80a84328b819ea16d21e89110a03a803400000022f400000000020250847a300007fc1361cd09c058c45e8250000e580ca71c1680201070000000181cdc886c48f18190b81c50000788a123be135178406075833e89547e427d000235037856732e0cf01188a434a8524e4a000146800003a3563fd1cf8cba00006400005882351bb83005c400016e9ab8eee41f2c08000dbc058000080000000000000000000d248e94702ac61006300005ee0001299adc0000000000000f741442ae02c80004c0000000045200000020cc000084000000022248f38d92c0de6000000072400000024e00007587c61d28000b7e000000236400000c17e95d447000000021ec3a8000000000002200034e046800000000000002ba3b432b18b52326f5350885c1e27c847199104982ca000087033246626391e057454220d1ef8c168302078a9000000000005b092c45609fa3a4ab2000092000012c3781dc0da8e1869301115200000001fda1540001c83270bd04060dd05d1140c62000478224894c59c000024426664100000000000610000d680002d62860afd0ac401438a2c0d70000170000000080c0000000d3a2e72d12270e9a71629591b41be1911e59ec85042b701e0dd8d443b94420000c4e0000000d184088b22a49e58d52000223800068e77d39e950c0000001b32310f4e0001ed0ced0ea00000000000002aa32f090c0003c50229ebcf0e42e46500001287152e180008120002001a640008a731f0b1850c3b61c19c0c4a49024839a102e87d607c20ac000000000000000059d000075412e91a40e968cba25393c100000001433c220600005be29100002200003c91a605a200000010e035e88341618ec9d439d0021ac46e88310c08c280c07320af06d108e20f257853868410b41a81bc29a52a000200839844c2c880000ec39f0b820d86dc8072a9068497001c06515f06324b718200186d800023f9aa01da29c00023480004370000000bb20000001fa000000002ba4b00001880291c2400010d496a300b782112a784bce7048b3c893c84d26c529424a4b645e70e91ce8bd60002d480007144
  | 14 => 0x7309bd172913000082911a28823b800049c39810a9ae911000022903cccdc1f13060f74aec12b0002450000047000025454e8951ca00000008f621699309be7eb12b19483842c528710cc0000001fe80002100001c88fb0f363fe2e90ac800089402a8a3c83864500023182a40002c782e470e0000f9000000074b2b30d607b82e90230ac4e8c1570001e8000000012f0b7897800000000001a86300000dc4b5a43b3ab130452e1d012a04ec8720001839c04386000394000000002800000000980003ea1ff88e074f000000000000033080011208ec1bf843c6388ee1599c1455005604700000001ca0001f78b8c5ce1fc8e988c431b2dc8e4013a00d2158000b9200038f83606684aa281119c00024f1978000fcc7a12c00fb400088a000199c9fc2182f19f610e8423336a47050a00009b14d415465820711f501400014f0000a6846f3d60f446864ae0be047400025f19c0000f3076614996ac9aa0eb27281c80e61ce2279a5c55a67e4190264000267000132084a8be4508000f0200027d84003083451ae9c480000003a49e24d7c0c947f24fcd562c228694744942e100013b83a20b12c6a410e9c059497045400000019820501de00044e800000000040d0000f6c7da1e49f94cd66c8363800090c00001d0fe00008c21028de8aae2b9000159400000000006acd0c00000004e4aee0001ad90c429023947580003625b61209eac0000a8387800092806c13721dcb9816125a19a4a488890001ba92181262e980006e00880001f8829656200010fc0009030000224140000144800075a00025b0dad0443de000081809061440c80000240000000000000000000041c000000184095c59c921468068924429820295f83726b50511b0c056931000116843a00027f80003600000000d4d1f00000001d8079e33305b960c62225911819a10920001b68100dbe2d31d8800002c5de000000104e00000018f4a6e80122e000000000039580001f841d000006c00000000007b90a024700005ec8e65f21c6019844241103505d91983370791874dce4e437680004b66e00258ba01964cf0fa941463a4294140fcc3cc0003901d0462600000000009b46240f680000004de37e8a5000000000017e824a1f72ca83e886826b475220478000000005685186a037c1f2d20c7d000000000648f70001244ce830e36119d4cd81782621d0c0007101760a6490a00049a951800081c3f1a5049c20d51330000b8407a23a94510c85da11b87e03245154731fd090078f33e214455c62e4350e1867e93605d86583667f9353988ccd42750000000f5a42a00008a886a0f91dd9b3cb4027b00015b09ea444323809c3ec46a462996ca9c6122e295780008083b795b40000e70000d841c400009d1208caa0000001fed19677534508b0d3c66205aa2e833e76445aa
  | 15 => 0x9728dc200000000008141f03f014e86288c1038118cf6e1e919623f050e4242560940bdc08742c8000e6c4a81a88e084560002758000ec25f000000010246790949b1000011f0001b6924a7832fe216864e91814b0000c6c83b34005e914c000271a45c3143d928f0f343c258b0d499909b644930494646163751aa818c07c33a2de8994d8c224022000071219a18b000115200000000000000000eca110bbe8e80000000000000052094400074a1228000bf60002b880000000002ca00000002bc1e0993c0000000000000cb26213dc861c8a24cc2bc027c7cc00031000d02b019d27880007601db22a111890801547d8c304c631807a21f800069b26106902d407f068000047400000010640008113de8880a4c6bd08180905e23f726590f853e00004597347ac6571b395047c66af1f506001427df0000150d18000220931800015c16406a111c0fe3050aac9d225d0f2219cd288c71f01f9cd467e42cc93e90cc5db30a9c4445a000234000093000019089dc0000000000128c9a61a05fa4204f00002a50c00f1479e0000000d5a55b14d80000000001758000e6035f236000000059b40f0968de889b2819238a147f235b1dc8f8e77132304809148ef080879400073937d0310ce200015c23b4f9a0003398000b480000da84110c48c81969d942e2000000000093c3790df10409a63f02461d64a227db3cf9ea40009272f7800005c77c3d303389523393b184dc6240000000c980d2751010a3385525562ee09cc05200018fa22cdf2000000000051c5134291b580004a00001c0846683c49783780006dd3ea8000ad265a0b30000ba87cc000224c5420e40001db425861923e06fc0008b126814c908a40600010603be0000c705011ea00000022dc7ec5fd043000000056b3cc8000040000393888c7d68aa3ab9b044c85b046f80003d47fd441071854660317802f469a0001ed8d200007c122192400002fb24e8000e6800001621340000000c60000bec88f3740d8000054040203b0ff886123b05ccbb040d36908c4ddc2bd071a2fce4c127314800077a32034722d805e6003960000a7027226c0000f200000001a0c00000032f80000000002a38f94000365000078000072d131000000059a11a24903d65212969db09727f608e002cf1039e4870cb800a31a47292640dc83a20a0530a522101d214f4f2e8f106380cc5926fc0aa209025414f2dd9a203ac05a0e01618f9e0003581d552864be226a1b80f65e5125819c2c864b47a1cd42d221608d95ec3760c5402800000000021096b8ed027f10495449a200017e0d04fea84f0688c940000003f4a2780006512939cb81fa6d50af8eb86969340419e2cef200000000000260001d185bcbc41c11a800000001cb0fa0000da000a16c919109808216f917cd8050700016c40003c810f1580000
  | 16 => 0x13618cc0000002cc17e4d026a61e10000ea400043c80d4ac82f2000027127c0000000df000051f06e04500001680000a94a9a3641fa800115e5aa11d80007400001f38000f6a60100000007a000002084f07420000b11ec4cc069f0860a802608d82f621ccde20002c61f10d0a5d704680000e23442998000b4e00700400006bc3bf2a298a8f5400001895e44905231a5000000007903a000050810e000100855e3e11098c042d60001090ea080e00011b0a8800000000018207be000049012501e6960001dfc0008a01bd800000000000000007380003e880000002cc2cfa424dfc16e4678fbc6b857d19897a103e6c92ff8b044b00da26923e4f68618238807c6a46ce16018e81306d71ca8c3cd2473100000000003ce3f98d244788ae0a500fc00000016e000cdb22fe16d94c400000000006d800000000012d4992573123000095615100000009f80001e20000ccc1a600000dc41c38100023540004bb36981740009100cc0001224561191244463c47900017985c6826347a1808505ea31a08f853a1222c11c7478e2012c5000071c6e900000000000e83f700e44e20640de81aca1652e03b9e50000000000000070043622d85640008a545d8000e460003fc01f048000035a05408c20001868b5ced6000261800000031526b834d2804ba000211800039b090873cab467f43d000000019010100080000002c3800000030300c000034678e00000000006b91ec000009a00000006182ea61c3de0ca07f46cc46488343fa0003b104488d234c2781b4400071300018d40840000000c18b267423550000e485001f206511b400043e9288aa062b1c780008c01e708c00007f84a327b82d0a5874830b93580001851aca4a0cf65e40fd8e2d1c44ef1fa20a425a3a938387f8fd80a52f49834cec9233eb800001e722000000000000038c925c2ce1413b490c88aa82a16a8fa4d207dc382146ca0c21a31920e4a2c1d714902b50ae5c418b8680a5e602209a40520083d15821bcb96858000129c0009320fe044d0be15331f91282328983a3800102e81600015d03c628024aa2ace664bd38695750064271f886546de2cd2b707a04e0000000000035c75000022887980003bd13e08441ad37280f4b1043c0e98fb867c06d3b500010967a400f1ca8e5e1090218b900008000cb80000005d51eb80000000ee12221d886068946b
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc7158c21026de3158c21026dc3158c21026ef2158c21026ed2158c21004ff7058c2100cfe7058c21004fd7058c2100cfc7058c210067f5058c210067d5058c21036df3058c21006dd3058c21004ff7654c21024fe7654c21004fd7654c21024fc7654c2101e7e6554c210067d6554c21016de6354c21006dd6354c2104cff76d0c21024fe76d0c21004fd76d0c21024fc76d0c2103d7e75d0c210057d75d0c2104ebe64d0c21006bd64d0c21005ee72d0c21005ed72d0c21025f671d0c21005f571d0c21004ff7650c21024fe7650c21004fd7650c21024fc7650c2104ebe6450c21006bd6450c21016de6350c21006dd6350c2108cff7694821024fe769482101cfd7694821024fc769482101e7e65948210067d6594821025f67194821005f5719482123e7f769482123e7e769482123e7d769482123e7c769482123e7f64948212867e64948210067d649482123e7c649482123e7f63948211de7e63948210067d639482123e7c639482123d7e729482123e7e629482123f76719482123f75719482127e7e619482123f6f219482123f76219482127f6d219482123d7f70948212757d709482123e7f60948211c67e609482126e7d609482123e7c609482126f5f309482126f5d309482108cff765482123e7f761482123e7e761482123e7d761482123e7c761482123e7f64148212667e64148210067d641482123e7c641482123e7f63148211be7e63148210067d631482123e7c631482123d7e721482123f6e721482123e7e621482123f76711482123f75711482125e7e611482123f6f211482123f76211482125f6d211482123d7f70148212557d701482123e7f60148211b67e601482124e7d601482123e7c601482124f5f301482124f5d301482124f6e201482123f6c2014821004fd76d082103d7e75d08210057d75d0821004ff769082104cfd769082104ebe6490821006bd649082123f6c5290821025f67190821005f57190821004ff76508210057f755082103d7c75508210076c525082104cff7610821024fe7610821004fd7610821024fc761082104ebe6410821006bd6410821007ad4210821025f67110821005f57110821084ff768c821024fe768c821014fd768c821024fc768c821016de638c821006dd638c821086ee628c821025f6718c821005f5718c821084ff764c8210057f754c82103d7c754c821086ee624c821025f77648421006f77648421004f77648421007777548421007747548421007d77348421007d47348421025f77248421027e77248421246f66248421027e6624842123f765248421007e65248421007665248421007e5524842123f745248421237e73248421237e43248421026f7604842122ef5604842122f77504842122f75504842122fd7304842122fd5304842122fe7204842122fe52048421
  | 1 => 0xc92129fe7104c92129fe5104c92101cff7654521064fd765452101cfc76545210067f655452101e7c6554521005df735452105ddc7354521006df635452111edc6354521005ef7254521005ec7254521027e42154521004fe76d05210067f65d052110e7c65d0521006bf64d052104ebc64d0521006df63d0521106dc63d0521005ee72d0521005ed72d052104cff7650521004fd765052104cfc76505210057f75505210657c75505210067f65505210de7c6550521006bf645052104ebc6450521005df735052105ddc7350521006df63505210d6dc6350521005ef7250521005ec7250521014ff764c52105cfd764c521014fc764c5210057f754c5210657c754c5210067f654c52109e7c654c521006df634c521016dc634c521005ef724c521005ec724c5210067f65c852108e7c65c8521006df63c8521086dc63c8521025ee72c8521026ef62c8521025f676c8521026f676c852100cf676c85210077765c85210077465c8521007d763c8521007d463c8521025f672c8521026f762c8521027e762c852123f7652c852123f7452c8521007e632c8521007e532c8521245f770c8521245f570c85212977750c85212977550c8521297d730c8521297d530c8521297e720c8521297e520c85210267f7559421004ff745942104cfc745942103e7f5459421004ff7359421014fe7359421014fc735942103e7f535942101cff725942101cfd725942103cfc725942103e7c5259421024ff7159421024fe7159421024fd7159421024fc71594210267e51594210267c5159421004ff705942100cfe7059421004fd705942100cfc705942103e7f50594210067d5059421006df3059421006dd3059421004ff75590210067f75590210047f755902101cfe755902101cfc75590210067c755902101c7c7559021026bf7459021004ff7359021014fe7359021014fc735902104cff725902104cfd7259021024ff7159021024fe7159021024fd7159021024fc7159021026be4159021026bc4159021004ff705902100cfe7059021004fd705902100cfc70590210067f50590210067d5059021006bf4059021006bd4059021006df3059021006dd305902104cff7695021024fe7695021004fd7695021024fc769502128e7f659502101e7c659502104ebe6495021006bd649502103f3f5495021005ee7295021005ed7295021004ff7655021024fe7655021004fd7655021024fc765502101e7e65550210067d655502104ebe6455021006bd6455021004ff7558c210067f7558c210047f7558c2101cfe7558c2101cfc7558c210067c7558c2101c7c7558c21004ff7458c2104cfc7458c21026df7358c21036de5358c21036de4358c21014ff7258c21014fd7258c21034fc7258c21036dc3258c21024ff7158c21024fe7158c21024fd7158c21024f
  | 2 => 0x676f52949210057e76949210067e76949210047e76949210067f64949212867e64949210067d64949212867c64949210067f63949210075f63949210065f63949211de7e63949210067d63949211de7c63949210075c63949211de5c63949210657e729492127f6e21949212d57f70949212d57d70949212de7f60949211c67e60949212de7d60949211c67c60949212df5f30949212df5d30949212df6f20949212df6d20949212df7710949212df751094921024fc76549210067f655492101e7c6554921006df63549211d6dc6354921005f77154921025f471549210057e76149210667e76149210047e76149210067f64149212667e64149210067d64149212667c64149210067f63149210075f63149210065f63149211be7e63149210067d63149211be7c63149210075c63149211be5c63149212d57e72149210676e721492125f6e21149210657f70149212cd7d70149212c67f60149211b67e60149212c67d60149211b67c60149212c75f30149212c75d30149212c76f20149212c76d20149212c77710149212c7751014921024fe76d0921024fc76d09210657e75d09210057d75d09210067f65d09211ae7c65d0921006bf64d092104ebc64d0921006df63d09211a6dc63d09210076c52d0921025f671d0921005f571d0921004fe76909210067f65909211967c659092104ebe6490921006bd6490921006df639092118edc6390921024fc76509210057f75509210657c75509210067f65509211867c6550921006bf645092104ebc6450921006df635092117edc6350921005f77150921025f47150921004fe76109210067f65109211667c651092104ebe6410921006bd6410921006df631092115edc63109210076c5210921007ad4210921074fe768c9210067f658c92114e7c658c921006df638c921016dc638c9210076e528c9210076c528c921005ee768c921076ee768c9210076f658c9210076c658c92105ded738c921007cf638c921016ee638c921016ec638c92105fcc638c921016cc638c921025ee718c921025ec718c9212bfce318c9212bfcc318c9212b5ef708c9212b5ed708c9212af6f508c9212af6d508c92105fcf308c9212afcd308c9212afe7108c9212afe5108c921024fc764c9210057f754c9210657c754c9210067f654c92113e7c654c921006df634c921016dc634c9210076e524c9210076c524c921005f7714c921025f4714c921025ec764c921016ec764c921024ec764c9210076f754c9210076c754c9210076f654c9210076c654c92105def734c921007cf734c921007cf634c921016ee634c921016ec634c92105fcc634c921007e7714c921025ee714c921025ec714c921007e4714c921025e4714c9212a5ef704c9212a5ed704c92129f6f504c92129f6d504c92105fcf304c92129fcd304
  | 3 => 0xf65d8d210075f65d8d210065f65d8d21006de65d8d21006dd65d8d21006dc65d8d210075c65d8d210065c65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d212bfcf72d8d212bfce21d8d212bfcc21d8d21005df70d8d21005dd70d8d21006df60d8d21006de60d8d21006dd60d8d21006dc60d8d210075f50d8d210075d50d8d21007cf20d8d21007cd20d8d21007d710d8d21007d510d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d212bedf72d8d2105ede72d8d21006dd72d8d21006df52d8d21006dc52d8d21006df71d8d212bede71d8d21006dd71d8d212bedc71d8d21006df51d8d212bede51d8d212bedc51d8d212bede41d8d212bedc41d8d212bede21d8d212bedc21d8d21006df70d8d21004df70d8d21006de70d8d21006dd70d8d21004dd70d8d21006dc70d8d21006df50d8d210065f50d8d21006de50d8d21006dd50d8d210065d50d8d21006dc50d8d21006df40d8d21006de40d8d21006dd40d8d21006dc40d8d21006df20d8d21006de20d8d21006dd20d8d21006dc20d8d212bedf10d8d21006de10d8d21006dd10d8d212bedc10d8d210057f7558d210657c7558d210067f6558d210067c6558d2105edc6358d21004ff7558d210067f7558d210047f7558d2101cfe7558d2101cfc7558d210067c7558d2101c7c7558d21004ff7458d2104cfc7458d2105cff7358d21006df7358d21074ff7258d21006ef7258d21084ff7158d21006f77158d21004ff7058d2100cfe7058d21004fd7058d2100cfc7058d210067f5058d210067d5058d2105edf3058d21006dd3058d21005de7618d2105ede7618d21004de7618d21006df6518d210075f6518d210065f6518d21006de6518d21006dd6518d21006dc6518d210075c6518d210065c6518d21006df6418d21006de6418d21006dd6418d21006dc6418d2105fcd7218d212e6df6218d212e7ce2118d212e7cc2118d2105ddf7018d21005dd7018d21006df6018d21006de6018d21006dd6018d21006dc6018d210075f5018d210075d5018d21007cf2018d21007cd2018d21007d71018d21007d51018d21004ff7654d21004fe7654d21004fd7654d21004fc7654d210067f6554d2101e7c6554d21006df6354d21016dc6354d2104cff76d0d21004fe76d0d21004fd76d0d2104cfc76d0d210657e75d0d210057d75d0d210067f65d0d211fe7c65d0d21006df63d0d21016dc63d0d21004ff7650d21004fe7650d21004fd7650d21004fc7650d210067f6550d211ee7c6550d21006df6350d21016dc6350d2107cfe76949210067f659492101e7e65949210067d659492101e7c6594921006df63949211dedc6394921
  | 4 => 0x9521006dc7359521014dc735952107cff7259521006ef72595210667c525952108cff7159521006f77159521004ff705952100cfe7059521004fd705952100cfc70595210667f50595210067d5059521006df3059521006dd30595210057e76195210667e76195210047e76195210067e63195210067c631952125e7f621952125f6e211952125f6c21195210657f70195210057d70195210067f60195210067e60195210067d60195210067c60195210075f30195210075d30195210076f20195210076d201952100777101952100775101952104cfe76d91210067f65d91210067c65d912101cfe75d9121004fd75d912101cfc75d9121014fe73d9121004fd73d9121014fc73d912104cfe72d912104cfc72d9121024fe71d9121024fc71d9121004ff70d912100cfe70d9121004fd70d912100cfc70d91210067f50d91210067d50d9121006be40d9121006bc40d9121006df30d9121006dd30d9121006ef20d9121006ed20d9121006f710d9121006f510d91210657e75991210057d75991210067f65991210067c6599121006bf649912105dde7399121005dd73991210057f75591210657c75591210067f65591210067c6559121005df735912105ddc7359121005fb7059121055f87059121004ff75591210067f75591210047f755912101cfe755912101cfc75591210067c755912101c7c7559121006bf7459121004ff7359121006df7359121004df7359121014fe7359121014fc7359121006dc7359121014dc7359121004ff7259121006ef7259121004ff7159121006f77159121004ff7059121006fb7059121004fb705912100cfe7059121004fd705912100cfc7059121006f8705912100cf870591210067f50591210067d5059121006bf4059121006bd4059121006df3059121006dd3059121006ef2059121006ed2059121006f71059121006f51059121004fe76191210067f65191210067c651912104ebe6419121006bd641912104cff7695121004fe7695121004fd769512104cfc76951210067f659512101e7c65951210673f5495121226dc6395121004ff7655121004fe7655121004fd7655121004fc76551210067f655512101e7c6555121216dc6355121005ef7255121005ec7255121014fe76d8d210067f65d8d210067c65d8d2105ede63d8d2101cfe75d8d21004fd75d8d2101cfc75d8d2104cfe74d8d21004fd74d8d21006df53d8d2105ede53d8d2105edc53d8d2105ede43d8d2105edc43d8d21014fe72d8d21024fd72d8d21014fc72d8d2105edf32d8d21024fe71d8d2105cfd71d8d21024fc71d8d2105edf31d8d21004ff70d8d2100cfe70d8d21004fd70d8d2100cfc70d8d210067f50d8d210067d50d8d2105edf30d8d21006de30d8d21006dd30d8d2105edc30d8d2105dde76d8d21014de76d8d21006d
  | 5 => 0x25f671d0a21005f571d0a211967e6590a210067d6590a2104ebe6490a21006bd6490a210076c5290a2104cff7650a210057f7550a2107d7c7550a211867e6550a210067d6550a2104ebe6450a21006bd6450a210076c5250a21005f77150a21025f47150a211667e6510a210067d6510a2104ebe6410a21006bd6410a21007ad4210a2105cfd768ca2114e7e658ca210067d658ca21006be648ca21006bd648ca212bedf638ca21016dc638ca21014ff764ca21024fc764ca210057f754ca2107d7c754ca2113e7e654ca210067d654ca21006be644ca21006bd644ca21016de634ca21006dd634ca21005f7714ca21025f4714ca21025f576c8621006f576c86210277665c86210277565c8621027b664c8621027b564c8621027e672c862123f7652c8621007e652c86210076652c8621007e552c862123f7452c86212f5f770c86212f5f570c86212ef7750c86212ef7550c86212efd730c86212efd530c862101cfe76d95210667e65d952104cfe74d9521004fd74d95210667f54d95210667c54d9521014fe73d9521004fd73d9521014fc73d95210667f53d95210067e53d95210667c53d952101cfe72d9521024fd72d952101cfc72d95210667f52d9521024fe71d9521064fd71d9521024fc71d95210667f51d9521004ff70d952100cfe70d9521004fd70d952100cfc70d95210667f50d95210067e50d95210067d50d95210667c50d9521006df30d9521006dd30d95210657e76d952101c7e76d95210067e63d95210067c63d952127f6e21d952127f6c21d95210057f70d95210057d70d95210067f60d95210067e60d95210067d60d95210067c60d95210075f30d95210075d30d95210076f20d95210076d20d95210077710d95210077510d95210067f74d95210067e74d95210067d74d95210067c74d95210067f73d95210067e73d95210067d73d95210067c73d95210067e43d95210067c43d952127e7f72d95210667e72d952101c7e72d95210067d72d952101c7c72d95210067f32d95210067c32d95210067f71d952127e7e71d95210067d71d952127e7c71d952127e7e41d952127e7c41d95210067f31d952127e7e31d952127e7c31d952127e7e21d952127e7c21d95210067f70d95210047f70d95210067e70d95210067d70d95210047d70d95210067c70d95210067f40d95210067e40d95210067d40d95210067c40d95210067f30d95210065f30d95210067e30d95210067d30d95210065d30d95210067c30d95210067f20d95210067e20d95210067d20d95210067c20d952127e7f10d95210067e10d95210067d10d952127e7c10d95210667c6559521005df735952105ddc7359521064ff75595210067f7559521004ff745952104cfc7459521004ff7359521006df7359521004df7359521014fe7359521014fc735
  | 6 => 0xf2159221026be2159221026bd2159221026bc2159221006bf7059221006be7059221006bd7059221006bc7059221006bf50592210063f5059221006be5059221006bd50592210063d5059221006bc5059221006bf30592210069f3059221006be3059221006bd30592210069d3059221006bc3059221006bf2059221006be2059221006bd2059221006bc2059221026bf1059221026b71059221026be1059221026bd1059221006b51059221026bc105922104cff7695221024fe7695221004fd7695221024fc769522101e7e65952210067d659522104ebe6495221006bd649522107f3f5495221005ee7295221005ed7295221004ff7655221024fe7655221004fd7655221024fc765522101e7e65552210067d655522104ebe6455221006bd6455221004ff7558e2101cfe7558e2101cfc7558e21004ff7458e2104cfc7458e21026df7358e21076df3258e21024fc7158e21026de3158e21026dc3158e21026ef2158e21026ed2158e21004ff7058e2100cfe7058e21004fd7058e2100cfc7058e210067f5058e210067d5058e21076df3058e21006dd3058e21004ff7654e21024fe7654e21004fd7654e21024fc7654e2101e7e6554e210067d6554e21006be6454e21006bd6454e2104cff76d0e21024fe76d0e21004fd76d0e21024fc76d0e2107d7e75d0e210057d75d0e211fe7e65d0e210067d65d0e2104ebe64d0e21006bd64d0e21005ee72d0e21005ed72d0e21004ff7650e21024fe7650e21004fd7650e21024fc7650e211ee7e6550e210067d6550e2104ebe6450e21006bd6450e21064fd7694a2127e7f6594a2101e7e6594a210067d6594a2101e7c6594a21006be6494a21006bd6494a2127d7d7694a210067d7694a2127e7f6494a212867e6494a2127f3e6494a210063e6494a210067d6494a2127f3d6494a210063d6494a2127e7c6494a2127e7f6394a211de7e6394a210067d6394a2127e7c6394a2127f6f2194a213157f7094a213157d7094a2127e7f6094a211c67e6094a2130e7d6094a211c67c6094a2130f5f3094a2130f5d3094a2127f771094a2130f751094a2101cff7654a21024fc7654a2101e7e6554a210067d6554a21006be6454a21006bd6454a21005f77154a21025f47154a2125d7d7614a2107e7d7614a2125e7f6414a212667e6414a2125f3e6414a210063e6414a210067d6414a2125f3d6414a210063d6414a2125e7c6414a2125e7f6314a211be7e6314a210067d6314a2125e7c6314a2107f6e7214a2125f6f2114a2107d7f7014a213057d7014a2125e7f6014a211b67e6014a212fe7d6014a211b67c6014a212ff5f3014a212ff5d3014a212ff6e2014a212ff6c2014a2125f771014a212ff751014a2107d7e75d0a210057d75d0a211ae7e65d0a210067d65d0a2104ebe64d0a21006bd64d0a21
  | 7 => 0x9621006dd30596210067f74596210067e74596210067d74596210067c74596210067f73596210067e73596210067d73596210067c73596210067e43596210067c43596210067f72596210067d725962107e7c72596210067f32596210067c32596210267f71596210267e71596210267d71596210267c71596210267f41596210267e41596210267d41596210267c41596210267f31596210267e31596210267d31596210267c31596210267f21596210267e21596210267d21596210267c21596210067f70596210047f70596210067e70596210067d70596210047d70596210067c70596210067f40596210067e40596210067d40596210067c40596210067f30596210065f30596210067e30596210067d30596210065d30596210067c30596210067f20596210067e20596210067d20596210067c20596210267f10596210267e10596210267d10596210267c105962104ebf759922104ebe759922104ebd759922104ebc759922104ebf739922104ebe739922104ebd739922104ebc7399221006bf5399221006be5399221006bc539922104ebf729922104ebd7299221006bf5299221006bc5299221006bf3299221006bc3299221026bf7199221026be7199221026bd7199221026bc7199221026bf5199221026be5199221026bd5199221026bc5199221026bf3199221026be3199221026bd3199221026bc3199221026bf2199221026be2199221026bd2199221026bc219922104ebf709922104ebe709922104ebd709922104ebc7099221006bf50992210063f5099221006be5099221006bd50992210063d5099221006bc5099221006bf30992210069f3099221006be3099221006bd30992210069d3099221006bc3099221006bf2099221006be2099221006bd2099221006bc2099221026bf1099221026be1099221026bd1099221026bc1099221004ff755922101cfe755922101cfc7559221026bf7459221006bf5459221006bc5459221004ff7359221014fe7359221014fc7359221006be4359221006bc4359221024fc7159221026be4159221026bc4159221004ff705922100cfe7059221004fd705922100cfc70592210067f50592210067d5059221006bf4059221006be4059221006bd4059221006bc4059221006df3059221006dd3059221026f71059221006f51059221006bf7559221006be7559221006bd7559221006bc7559221006bf7359221006be7359221006bd7359221006bc7359221006bf5359221006be5359221006bc5359221006bf7259221006bd7259221006bf5259221006bc5259221006bf3259221006bc3259221026bf7159221026be7159221026bd7159221026bc7159221026bf5159221026be5159221026bd5159221026bc5159221026bf3159221026be3159221026bd3159221026bc3159221026b
  | 8 => 0x4fd7650f21004fc7650f21024fd7694b2101e7e6594b210067d6594b2108f6f5294b21025f67194b21005f57194b2123e7e7694b2123e7d7694b2123e7f6494b212867e6494b210067d6494b2123e7c6494b2123e7f6394b211de7e6394b210067d6394b2123e7c6394b2123f767194b2123f757194b2123d7f7094b213557d7094b2123e7f6094b211c67e6094b2134e7d6094b2123e7c6094b2134f5f3094b2134f5d3094b2123f6f2094b2134f6d2094b2103cff7654b2123e7e7614b2123e7d7614b2123e7f6414b212667e6414b210067d6414b2123e7c6414b2123e7f6314b211be7e6314b210067d6314b2123e7c6314b2123f6e7214b2123f767114b2123f757114b2123d7f7014b213457d7014b2123e7f6014b211b67e6014b2133e7d6014b2123e7c6014b2133f5f3014b2133f5d3014b2123f6f2014b2133f6d2014b2108d7e75d0b210057d75d0b210076c52d0b21024fd7690b2104ebe6490b21006bd6490b21025f67190b21005f57190b210057f7550b2108d7c7550b21024fd7610b2104ebe6410b21006bd6410b2123f6c5210b21007ad4210b21025f67110b21005f57110b21024fd768cb21016de638cb21006dd638cb2123f6e528cb2123f6c528cb21025f6718cb21005f5718cb21025ed768cb21016ed768cb21024ed768cb21016ee638cb21087ce638cb21007cd638cb21016ec638cb21025ee718cb21007e6718cb21007e5718cb21025ec718cb212bfce318cb212bfcc318cb21335ef708cb21335ed708cb2132f6f508cb2132f6d508cb21087cf308cb2132fcd308cb21034ff764cb210057f754cb2108d7c754cb210076e524cb210076c524cb21005ef764cb21036ef764cb210076f754cb210076c754cb21007cf734cb21016ee634cb21016ec634cb21025ee714cb21025ec714cb21325ef704cb21325ed704cb2131f6f504cb2131f6d504cb21087cf304cb2131fcd304cb2101cff765472101cfc765472101e7e65547210067d6554721005df7354721085dc7354721005ef7254721005ec7254721027e6215472104ebe64d0721006bd64d0721005ee72d0721005ed72d072104cff76507210057f755072108d7c755072104ebe6450721006bd6450721005df7350721085dc7350721005ef7250721005ec7250721014ff764c721014fc764c7210057f754c72108d7c754c721016de634c721006dd634c721005ef724c721005ec724c7210267f7559621004ff745962104cfc745962107e7f545962107e7c5459621004ff7359621014fe7359621014fc735962107e7f53596210067e535962107e7c535962107e7f5259621024fc71596210267e51596210267c5159621004ff705962100cfe7059621004fd705962100cfc705962107e7f50596210067e50596210067d505962107e7c5059621006df305
  | 9 => 0xd50d9721006df30d9721006dd30d972101cff765972108e7c65597210067f7559721004ff745972104cfc745972108e7c5459721004ff7359721014fe7359721014fc73597210067e535972108e7c5359721024fc725972108e7c525972108e7f5159721004ff705972100cfe7059721004fd705972100cfc705972108e7f50597210067d5059721006df3059721006dd305972108d7e75d93210057d75d9321085de73d9321005dd73d932101cfe75d93210067e75d932101c7e75d9321004fd75d93210067d75d93210047d75d932101cfc75d9321014fe73d9321006de73d9321014de73d9321004fd73d9321006dd73d9321004dd73d9321014fc73d9321006ee72d9321006f571d9321004ff70d932100cfe70d9321004fd70d932100cfc70d93210067f50d93210067d50d9321006df30d9321006dd30d9321006ef20d9321006ed20d9321004fd769932108d7e75993210057d7599321006bf649932104cff7659321004ff755932101cfe755932101cfc7559321006bf7459321006bf5459321006bc5459321004ff7359321014fe7359321014fc7359321006be4359321006bc4359321004ff705932100cfe7059321004fd705932100cfc70593210067f50593210067d5059321006bf4059321006bd4059321006df3059321006dd3059321006ef2059321006ed205932104ebe6419321006bd641932104cff7695321004fe7695321004fd769532104cfc769532101e7e65953210067d659532108f3f5495321004ff7655321004fe7655321004fd7655321004fc76553210067f655532101e7c6555321005ef7255321005ec725532108d7e75d8f210057d75d8f21005be74d8f21005bd74d8f21086de63d8f2101cfe75d8f210067e75d8f2101c7e75d8f21004fd75d8f210067d75d8f210047d75d8f2101cfc75d8f2104cfe74d8f21006be74d8f2104cbe74d8f21004fd74d8f21006bd74d8f21004bd74d8f21084fd73d8f21006ee72d8f21006f571d8f212bede31d8f212bedc31d8f21004ff70d8f2100cfe70d8f21004fd70d8f2100cfc70d8f210067f50d8f210067d50d8f21086df30d8f21006dd30d8f21014ff7658f21086dc6358f21004ff7558f2101cfe7558f2101cfc7558f21004ff7458f2104cfc7458f21006df7358f21006df5358f21086dc5358f21086dc4358f21024fc7258f21086dc3258f21086df3158f21004ff7058f2100cfe7058f21004fd7058f2100cfc7058f210067f5058f210067d5058f21086df3058f21006dd3058f21004ff7654f21004fe7654f21004fd7654f21004fc7654f210067f6554f2101e7c6554f2104cff76d0f21004fe76d0f21004fd76d0f2104cfc76d0f2108d7e75d0f210057d75d0f21016de63d0f21006dd63d0f21025f671d0f21005f571d0f21004ff7650f21004fe7650f21
  | 10 => 0x8931036df3018931006dd3018931006ee2018931006ec2018931004fe7694931004fd7694931004fc76949310067f659493101e7e65949310067d659493101e7c659493123e7f76949310057e76949310067e76949310047e76949310067d76949310057c769493123e7c76949310047c76949310067f64949312867e64949310067d64949312867c649493127e7f63949311bd7e72949310067f629493123e7c62949311de7f61949311df77319493127f5e319493127f5c31949311df7431949313757f70949313757d709493136e7f60949311c67e609493136e7d60949311c67c60949311df5f309493136f5d3094931004ff7654931004fe7654931004fc76549310067f655493101e7c655493123e7f76149310057e761493109e7e76149310047e761493109e7d761493109d7c761493123e7c761493101c7c76149310067f64149312667e64149310067d64149312667c64149311bf5e731493109f5d731493125e7f63149311dd7e721493109f6e72149310067f621493123e7c62149311be7f61149311bf77311493125f5e311493125f5c31149311bf74311493109d7f70149313657d701493135e7f60149311b67e601493135e7d60149311b67c60149311bf5f301493135f5d3014931004fe76d0931004fd76d093104cfc76d093109d7e75d09310057d75d09310067f65d09311ae7c65d0931006bf64d093104ebc64d0931004fe7690931004fd7690931004fc76909310067f65909311967c6590931006ef6290931006ec6290931004ff7650931004fe7650931004fc76509310057f755093109d7c75509310067f65509311867c6550931006bf645093104ebc6450931006ef6250931006ec6250931004fe7610931004fd761093104cfc76109310067f65109311667c6510931015de7310931005dd7310931007ad421093101cff7654531014fe765453111cfd7654531014fc76545310067f655453101e7c6554531005df7354531015dc7354531014fe76d0531014fc76d05310067f65d053110e7c65d0531006bf64d053104ebc64d0531015de73d0531005dd73d053104cff7650531014fe76505310d4fd7650531014fc76505310057f755053109d7c75505310067f65505310de7c6550531006bf645053104ebc6450531005df7350531015dc735053108e7e65d9721005be74d9721005bd74d9721085de73d9721005dd73d972108cfd75d972104cfe74d9721006be74d972104cbe74d9721004fd74d9721006bd74d9721004bd74d972108e7f54d9721014fe73d9721006de73d9721014de73d9721004fd73d9721006dd73d9721004dd73d9721014fc73d972108e7f53d9721006ee72d9721006f571d972127e7e51d972127e7c51d9721004ff70d972100cfe70d9721004fd70d972100cfc70d972108e7f50d97210067
  | 11 => 0x39cff7159531006f77159531004ff705953100cfe7059531004fd705953100cfc705953109e7f50595310067d505953111edf3059531006dd305953112d7e761953109e7e761953112c7e76195313967f63195313965f63195310057e721953138e7f611953138f7731195313975e31195313975c311953138f74311953109d7f70195310057d70195310067f60195310067e60195310067d60195310067c601953138f5f30195310075d301953104cfe76d91310067f65d91310067c65d913101cfe75d9131004fd75d913101cfc75d9131024ff73d9131014fe73d9131024fd73d9131014fc73d91310eebf43d91310eebd43d9131004fe72d9131004fd72d9131004ff70d913100cfe70d9131004fd70d913100cfc70d91310067f50d91310067d50d9131006be40d9131006bc40d91310eedf30d9131006dd30d913109d7e75991310057d75991310067f65991310067c6599131006bf6499131386df6399131005ee7299131005ed72991310d5f571991310057f755913109d7c75591310067f65591310067c6559131105f77159131004ff75591310067f75591310047f755913101cfe755913101cfc75591310067c755913101c7c7559131006bf74591310d4ff7359131006df7359131004df7359131004ff7259131004fc7259131104ff7159131006f77159131004ff705913100cfe7059131004fd705913100cfc70591310067f50591310067d50591310d6df3059131006dd30591310ecfe76191310067f65191310067c651913104ebe6419131006bd641913137edf631913104cff7695131004fe7695131004fd769513104cfc76951310067f659513101e7c659513109f3f5495131004ff7655131004fe7655131004fd7655131004fc76551310067f655513101e7c655513109d7e75d89310057d75d89310067f65d89310067c65d893101cfe75d89310067e75d893101c7e75d8931004fd75d89310067d75d89310047d75d893101cfc75d893104cfe74d8931004fd74d8931024fd73d8931076ee32d8931076ed32d8931004ff70d893100cfe70d8931004fd70d893100cfc70d89310067f50d89310067d50d8931076df30d8931006dd30d8931006ee20d8931006ec20d893109d7e75989310057d75989310067f65989310067c6598931005be7498931005bd7498931006ef629893105df571989310057f755893109d7c75589310067f65589310067c6558931085f771589310067f65189310067c6518931006ed621893123e7f751893101cfe7518931004fd751893101cfc751893123e7c751893104cfe7418931004fd7418931024fd7318931036ee3218931036ed3218931024fe7118931024fc71189312e6de31189312e6dc3118931004ff701893100cfe7018931004fd701893100cfc70189310067f50189310067d501
  | 12 => 0x73114a3125f743114a310ad7f7014a313cd7d7014a3125e7f6014a311b67e6014a313c67d6014a311b67c6014a311bf5f3014a313c75d3014a3104cff76d0a31024fe76d0a31004fd76d0a310ad7e75d0a310057d75d0a31015de73d0a31005dd73d0a31004ff7690a31024fe7690a31004fd7690a3104ebe6490a31006bd6490a31015de7390a31005dd7390a31004ff7650a31004fd7650a31024fc7650a310057f7550a310ad7c7550a31005df7350a31015dc7350a3104cff7610a31024fe7610a31004fd7610a3104ebe6410a31006bd6410a31015dc7310a31007ad4210a310adde758ca310addc758ca313bdde748ca313bddc748ca31015de728ca31017ce728ca312bfce628ca31006dd628ca312bfcd628ca310075e528ca310075c528ca312bfd6718ca312bddd718ca31007d5718ca31016de618ca31017d6618ca313b5df708ca313b5dd708ca312bedf608ca313aedd608ca313af5f508ca313af5d508ca3101cfe76d953109e7e65d953104cfe74d9531004fd74d953109e7f54d953109e7c54d9531024ff73d9531014fe73d9531024fd73d9531014fc73d953112e7f53d953112e7d53d9531004fe72d9531004fd72d953109e7f52d953109e7c52d9531014fd71d953109e7f51d9531004ff70d953100cfe70d9531004fd70d953100cfc70d953109e7f50d95310067e50d95310067d50d953109e7c50d953112edf30d9531006dd30d953138d7e76d953101c7e76d95310057e72d953112f7731d95313a75e31d95313a75c31d953112f7431d95310057f70d95310057d70d95310067f60d95310067e60d95310067d60d95310067c60d953112f5f30d95310075d30d95310067f74d95310067e74d95310067d74d95310067c74d95313a67f73d953112e7e73d953112e7d73d953112e7c73d953112e7f43d953112e7e43d953112e7d43d953112e7c43d95310067f72d95310067e72d95310047e72d95310067d72d95310067c72d953112e7f32d953112e7e32d953112e7d32d953112e7c32d953112e7f71d95313a67e71d953112e7d71d95313a67c71d95313a67e41d95313a67c41d953112e7f31d95313a67e31d95313a67c31d95313a67e21d95313a67c21d95310067f70d95310047f70d95310067e70d95310067d70d95310047d70d95310067c70d95310067f40d95310067e40d95310067d40d95310067c40d953112e7f30d953112e5f30d953112e7e30d953112e7d30d95310065d30d953112e7c30d95310067f20d95310067e20d95310067d20d95310067c20d95313a67f10d95310067e10d95310067d10d95313a67c10d953109e7c655953139df7715953112cff75595310067f7559531004ff745953104cfc745953111cff7359531006df73595310acdf7359531004ff7259531004fc725953109e7c5259531
  | 13 => 0x9231026be4159231026bc4159231004ff705923100cfe7059231004fd705923100cfc70592310067f50592310067d5059231006bf4059231006bd40592310d6df3059231006dd305923104cff7695231024fe7695231004fd7695231024fc769523128e7f659523101e7c659523104ebe6495231006bd64952310af3f5495231015de7395231005dd73952310af5f5395231004ff7655231024fe7655231004fd7655231024fc765523101e7e65552310067d655523104ebe6455231006bd6455231005df7355231015dc73552312175c5355231385dd76d0e313bedd76d0e310adde75d0e313bf5e75d0e310ad5e75d0e313bf5d75d0e313bddc75d0e31015de74d0e310179e74d0e31386df64d0e313879e64d0e313bedd64d0e313879d64d0e31005de72d0e31387d671d0e31385dd71d0e313bfd571d0e31016de61d0e31017d661d0e313879f41d0e313879d41d0e313bddf70d0e313eddd70d0e31386df60d0e313e6dd60d0e313e75f50d0e313e75d50d0e3101cfe7598a31004fd7598a3101cfc7598a3104cfe7498a31004fd7498a31026ee7298a31086ee3298a31086ed3298a31024fe7198a31026ee2198a31026ec2198a31004ff7098a3100cfe7098a31004fd7098a3100cfc7098a310067f5098a310067d5098a31086df3098a31006dd3098a31006ef2098a31006ed2098a31004ff7558a310067f7558a310047f7558a3101cfe7558a3101cfc7558a310067c7558a3101c7c7558a31004ff7458a3104cfc7458a31026ef7258a3105eee3258a3105eed3258a3105edc3258a31024fc7158a31026ee2158a31026ec2158a31004ff7058a3100cfe7058a31004fd7058a3100cfc7058a310067f5058a310067d5058a3105edf3058a31006dd3058a31006ef2058a31006ed2058a31004ff7694a31024fe7694a31004fd7694a3127e7f6594a3101e7e6594a310067d6594a3101e7c6594a31015de7394a31005dd7394a310af5f5394a311df5c5394a3123e7f7694a3127e7e7694a310067d7694a3123e7c7694a3127e7f6494a312867e6494a310067d6494a3127e7c6494a311df5e7394a310075d7394a310075f4394a311df5c4394a3123e7e6294a310067d6294a311df5c3294a3127e7e6194a3127f5f3194a311df773194a3127f743194a313dd7f7094a313dd7d7094a3127e7f6094a311c67e6094a313d67d6094a311c67c6094a311df5f3094a313d75d3094a31004ff7654a31004fd7654a31024fc7654a31005df7354a31015dc7354a3123e7f7614a3125e7e7614a310ae7d7614a3123e7c7614a3125e7f6414a312667e6414a310067d6414a3125e7c6414a310af5f7314a311bf5c7314a310075f4314a311bf5c4314a310af6e7214a3123e7e6214a310067d6214a311bf5c3214a3125e7e6114a3125f5f3114a311bf7
  | 14 => 0x26ee2198841026ec2198841004ff709884100cfe7098841004fd709884100cfc70988410067f50988410067d5098841006df3098841006dd3098841006ef2098841006ed2098841004ff75588410067f75588410047f755884101cfe755884101cfc75588410067c755884101c7c7558841004ff7358841014fe7358841014fc7358841026ef725884104eef425884104eec4258841026ee2158841026ec2158841004ff705884100cfe7058841004fd705884100cfc70588410067f50588410067d5058841006df3058841006dd3058841006ef2058841006ed2058841004ff7694841024fe7694841004fd769484127e7f659484101e7e65948410067d659484101e7c659484104dbe7494841005bd749484127d7f769484123e7f76948410047f769484127e7e769484127d7d76948410067d76948410047d769484123e7c76948412873e74948410073d74948412867e64948411de7e63948410067d639484127e7c639484125d7e729484123e7e62948410067d629484127e7e619484127f3f419484127f76419484127f3d419484128775419484140d7f709484140d7d709484127e7f60948411c67e60948414067d60948411c67c60948414075f30948414075d3094841004ff7654841004fd7654841024fc765484101e7e65548410067d655484125d7f761484123e7f761484101c7f761484125e7e761484125d7d76148410c67d76148410047d761484123e7c76148412667e64148411be7e63148410067d631484125e7c631484127d7e72148410c76e721484123e7e62148410067d621484125e7e611484125f3f411484125f76411484125f3d41148412677541148410c57f70148413fd7d701484125e7f60148411b67e60148413f67d60148411b67c60148413f75f30148413f75d3014841004ff768c841024fe768c841004fd768c84114e7e658c8410067d658c84104dbe748c841005bd748c841006ee628c841006ed628c841004ff764c841004fd764c841024fc764c8410057f754c8410c57c754c84113e7e654c8410067d654c841016de634c841006dd634c841006ee624c841006ed624c8410267f7559631004ff745963104cfc74596310ae7f54596310aedf735963111e7f53596310aedf53596310ae5f535963111e7d535963111edc5359631004ff7259631004fc72596310ae7c5259631024fe7159631024fc71596310267e51596310267c5159631004ff705963100cfe7059631004fd705963100cfc70596310ae7f50596310067d505963111edf3059631006dd3059631004ff75592310067f75592310047f755923101cfe755923101cfc75592310067c755923101c7c7559231026bf7459231006df73592310d6bf43592310d6bd43592310d6dc4359231004ff7259231004fc7259231024fe7159231024fc715
  | 15 => 0xf748c94104dbc748c941006df638c941016dc638c941004ff764c941004fe764c941004fc764c9410057f754c9410dd7c754c9410067f654c94113e7c654c941005bf744c94104dbc744c941006df634c941016dc634c941005f7714c941025f4714c94101cff76545410dcfd765454104cfc76545410067f655454101e7c6554541005bf745454104dbc74545410073d5454541005df73545410d5dc7354541006df635454111edc6354541027b44154541024ff75594410267f755944104cff745944104cfe745944104cfd745944104cfc745944104e7e545944104e7c5459441004ff7359441014fe7359441014fc73594410c67f53594410067e53594410c67c5359441004ff7259441004fc72594410c67f52594410c67c5259441024fe7159441024fc71594410267e51594410267c5159441026bf4159441026bd4159441004ff705944100cfe7059441004fd705944100cfc70594410c67f50594410067e50594410067d50594410c67c5059441006df3059441006dd305944104e7f745944104e7e745944104e7d745944104e7c74594410067f73594410067e73594410067d73594410067c735944104e7f435944104e7e435944104e7d435944104e7c43594410067f72594410067e72594410067d72594410067c72594410047c725944104e7f425944104e7e425944104e7d425944104e7c42594410067f32594410067c32594410267f71594410267e71594410267d71594410267c71594410267f41594410263f41594410267e41594410267d41594410263d41594410267c41594410267f31594410267e31594410267d31594410267c31594410267f21594410267e21594410267d21594410267c21594410067f70594410047f70594410067e70594410067d70594410047d70594410067c705944104e7f405944104e7e405944104e7d405944104e7c40594410067f30594410065f30594410067e30594410067d30594410065d30594410067c30594410067f20594410067e20594410067d20594410067c20594410267f10594410267e10594410267d10594410267c1059441004ff7558c4101cfe7558c4101cfc7558c41014fd7458c41024ff7358c41026df7358c4104edf4358c4104edc4358c41004ff7258c41004fc7258c410bedf3258c41024fc7158c41026bf4158c41026bd4158c41026de3158c41026dc3158c41004ff7058c4100cfe7058c41004fd7058c4100cfc7058c410067f5058c410067d5058c410bedf3058c41006dd3058c41004ff7654c41004fd7654c41024fc7654c4101e7e6554c410067d6554c4123e7f759884101cfe7598841004fd759884101cfc759884123e7c7598841014fe7398841004fd7398841014fc7398841026ee729884104eef429884104eec4298841026bf4198841026bd4198841
  | 16 => 0x4941006df63949411dedc639494123e7f76949410057e76949410067e76949410047e76949410067d76949410057c769494123e7c76949410047c76949410073f74949410073c74949410067f63949410075f63949410065f63949411de7e63949411de7c63949410075c63949411de5c63949410073f43949410073d43949410dd7e72949410067f629494123e7c629494128777419494127f3e41949414457f70949414457d709494144e7f60949411c67e609494144e7d60949411c67c609494144f3f409494144f3d409494144f5f309494144f5d309494144f77109494144f751094941004ff7654941004fe7654941004fc76549410067f655494101e7c6554941005bf745494104dbc7454941006df63549411d6dc635494123e7f76149410057e76149410de7e76149410047e76149410de7d76149410dd7c761494123e7c761494101c7c76149410df3e74149410df3d74149410067f63149410075f63149410065f63149411be7e63149411be7c63149410075c63149411be5c63149410073f43149410073d43149414457e72149410df6e72149410067f621494123e7c621494126777411494125f3e41149410dd7f701494143d7d70149414367f60149411b67e60149414367d60149411b67c60149414373f40149414373d40149414375f30149414375d3014941437771014941437751014941024fe76909410067f65909411967c6590941006df639094118edc6390941006ef6290941006ec6290941025f67190941005f57190941024be7690941005bf7590941005bd75909410073f65909410073c6590941005bd73909410079f63909410079c639094104dbe7290941006bf6290941007af6290941007ac62909410073e52909410073c5290941025be7190941007b67190941007b57190941025bc719094104ebf619094104fb76190941425bf7090941425bd709094116ebe609094116ebc609094142f3f509094142f3d509094142f9f309094142f9d309094142faf209094142fad209094142fb7109094142fb51090941024fc76509410057f75509410dd7c75509410067f65509411867c6550941006df635094117edc6350941006ef6250941006ec625094104fac4250941005f77150941025f47150941005be761094104ebe761094104dbf7510941005bd75109410073f65109410073c6510941005bd73109410079f63109410079c6310941425be721094104fae7210941006bf62109410073e52109410073c5210941025be7110941025bc711094104ebf611094104fb7611094104dbf701094141dbd7010941156be6010941156bc60109414173f50109414173d50109414179f30109414179d3010941417b71010941417b51010941004fe768c941004fd768c941004fc768c9410067f658c94114e7c658c941005b
  | 17 => 0x106df6118d41477d74118d4137f9e4118d4137f9c4118d41477d44118d410d5df7018d41005dd7018d41006df6018d41006de6018d41006dd6018d41006dc6018d410075f5018d410075d5018d410079f4018d410079d4018d41007d71018d41007d51018d41004ff7654d41004fe7654d41004fc7654d410067f6554d4101e7c6554d410073e5454d41006df6354d41016dc6354d41005be76d0d4104ebe76d0d4104dbf75d0d4104f3e75d0d41005bd75d0d4104f3d75d0d410053d75d0d410073f65d0d410073c65d0d410d5bd73d0d410079f63d0d41016be63d0d41016bc63d0d410d79c63d0d410169c63d0d41005be72d0d41025be71d0d41025bc71d0d4104ebf61d0d4104fb761d0d413879c31d0d4104dbf70d0d4146dbd70d0d414673f50d0d414673d50d0d410d79f30d0d414679d30d0d41467b710d0d41467b510d0d41024fc7650d410067f6550d411ee7c6550d41006df6350d41016dc6350d41005f77150d41025f47150d41025bc7650d41016bc7650d41024bc7650d41005bf7550d41005bd7550d410073f6550d410073c6550d4104dbf7350d4104f9f7350d410079f6350d41016be6350d41016bc6350d410d79c6350d41005bc7250d41007b77150d41025be7150d41025bc7150d41007b47150d41025b47150d4104ebf6150d4104fb76150d4145dbf7050d4145dbd7050d414573f5050d414573d5050d410d79f3050d414579d3050d41457b71050d41457b51050d410dd7e75d89410057d75d89410067f65d89410067c65d8941006df63d8941006dc63d894101cfe75d89410067e75d894101c7e75d8941004fd75d89410067d75d89410047d75d894101cfc75d8941014fe73d8941004fd73d8941014fc73d8941004ff70d894100cfe70d8941004fd70d894100cfc70d89410067f50d89410067d50d8941006bf40d8941006bd40d8941006df30d8941006dd30d8941006ee20d8941006ec20d8941006f710d8941006f510d89410dd7e75989410057d75989410067f65989410067c65989410d5de7398941005dd7398941006df6398941006dc6398941006ef62989410057f75589410dd7c75589410067f65589410067c6558941005df73589410d5dc7358941006df6358941006dc6358941005fb70589410cdf870589410067f65189410067c6518941006df6318941006dc6318941006ed621894123e7f751894101cfe7518941004fd751894101cfc751894123e7c7518941014fe7318941004fd7318941014fc7318941004ff701894100cfe7018941004fd701894100cfc70189410067f50189410067d5018941006df3018941006dd3018941006ee2018941006ec2018941004fe7694941004fd7694941004fc76949410067f659494101e7e65949410067d659494101e7c65949410073e54949410073d549
  | 18 => 0xf30951414979d3095141497b71095141497b51095141024fc76551410067f655514101e7c655514104f3c5455141216dc6355141005f77155141025f4715514104fb44155141025bc765514101ebc7655141024bc765514104dbf755514104f3f75551410073f655514101ebe655514101ebc65551410df3c6555141005bf735514148f3e53551410df3c5355141005bc72551410df3c5255141007b77155141025be7155141025bc7155141007b4715514104ebf615514104fb761551410df3f5155141485bf7055141485bd70551410df3f505514147f3d505514147f9f305514147f9d305514147fb7105514147fb51055141014fe76d8d410067f65d8d410067c65d8d410d6de63d8d4101cfe75d8d41004fd75d8d4101cfc75d8d41024fd74d8d41014fc74d8d41006df53d8d410d6de53d8d410d6dc53d8d410d6de43d8d41004fe72d8d41004fd72d8d410d6df32d8d410d6dc32d8d4104cfd71d8d410d6df31d8d41004ff70d8d4100cfe70d8d41004fd70d8d4100cfc70d8d410067f50d8d410067d50d8d410d6df30d8d41006de30d8d41006dd30d8d410d6dc30d8d410d5de76d8d41014de76d8d41006df65d8d410075f65d8d410065f65d8d41006de65d8d41006dd65d8d41006dc65d8d410075c65d8d410065c65d8d413879f74d8d410079e54d8d410079d54d8d413bfd741d8d413879e41d8d413879c41d8d413bfd441d8d41005df70d8d41005dd70d8d41006df60d8d41006de60d8d41006dd60d8d41006dc60d8d410075f50d8d410075d50d8d410079f40d8d410079d40d8d41007d710d8d41007d510d8d41006df75d8d41006de75d8d41006dd75d8d41006dc75d8d41386df74d8d410d6de74d8d41006df54d8d413bede54d8d41006dd54d8d413bedc54d8d41006df72d8d41006de72d8d41006dd72d8d41006dc72d8d41006df52d8d41006dc52d8d413bedf42d8d413bedc42d8d413bedf71d8d41386de71d8d41006dd71d8d41006df51d8d41386de51d8d41386dc51d8d413bedf41d8d41386de41d8d41386dc41d8d41386de21d8d41386dc21d8d41006df70d8d41004df70d8d41006de70d8d41006dd70d8d41004dd70d8d41006dc70d8d41006df50d8d410065f50d8d41006de50d8d41006dd50d8d410065d50d8d41006dc50d8d413bedf40d8d41006de40d8d41006dd40d8d413bedc40d8d41006df20d8d41006de20d8d41006dd20d8d41006dc20d8d41386df10d8d41006de10d8d41006dd10d8d41386dc10d8d410057f7558d410dd7c7558d410067f6558d410067c6558d410d6dc6358d41005de7618d410d6de7618d41006df6518d410075f6518d410065f6518d41006de6518d41006dd6518d41006dc6518d410075c6518d410065c6518d410d79d7418d4137edf6418d410079e5418d410079d5418d41
  | 19 => 0x95410067e53d95410de7c53d9541004fe72d9541004fd72d95410de7f52d95410de7c52d954104cfd71d95410de7f51d9541004ff70d954100cfe70d9541004fd70d954100cfc70d95410de7f50d95410067e50d95410067d50d95410de7c50d9541006df30d9541006dd30d95410dd7e76d954101c7e76d954128f3f74d95410067e63d95410067c63d95410057e72d95414b77741d954128f3e41d954128f3c41d95414b77441d95410057f70d95410057d70d95410067f60d95410067e60d95410067d60d95410067c60d95410073f40d95410073d40d95410075f30d95410075d30d95410077710d95410077510d954128e7f74d95414b67e74d95410067d74d95414b67c74d95410067f73d95410067e73d95410067d73d95410067c73d95414b67f43d95410067e43d95414b67c43d95410067f72d95410067e72d95410047e72d95410067d72d95410067c72d95414b67f42d95414b67c42d95410067f32d95410067c32d95414b67f71d954128e7e71d95410067d71d954128e7c71d95414b67f41d954128e7e41d954128e7c41d95410067f31d954128e7e31d954128e7c31d954128e7e21d954128e7c21d95410067f70d95410047f70d95410067e70d95410067d70d95410047d70d95410067c70d95414b67f40d95410067e40d95410067d40d95414b67c40d95410067f30d95410065f30d95410067e30d95410067d30d95410065d30d95410067c30d95410067f20d95410067e20d95410067d20d95410067c20d954128e7f10d95410067e10d95410067d10d954128e7c10d95410de7c6559541005df73595410d5dc73595410dcff75595410067f75595410f4ff7459541006bf7459541004ff7359541006df7359541004df7359541014fe7359541014fc7359541006dc7359541014dc7359541004ff7259541004fc72595410de7c525954110cff7159541006f77159541004ff705954100cfe7059541004fd705954100cfc70595410de7f50595410067d5059541006df3059541006dd30595410057e76195410de7e76195410047e76195410df3d74195414ae7f64195410067e63195410067c63195410057e72195414a67f61195414a77741195414af3e41195414af3c41195414a77441195410dd7f70195410057d70195410067f60195410067e60195410067d60195410067c60195410073f40195410073d40195410075f30195410075d3019541007771019541007751019541005be769514104ebe76951410ddbd75951410073f659514101ebe659514101ebc65951410df3c659514101e3c6595141005bd73951410df3f5395141005be72951410df3c5295141025be7195141025bc719514104ebf619514104fb7619514128f3e519514128f3c519514104dbf709514149dbd70951410df3f50951414973d50951414979
  | 20 => 0x26bd4158e41026de3158e41026dc3158e41004ff7058e4100cfe7058e41004fd7058e4100cfc7058e410067f5058e410067d5058e410eedf3058e41006dd3058e41004ff7654e41004fd7654e41024fc7654e4101e7e6554e410067d6554e41014ff7650e41016de6350e41006dd6350e41005f77150e41025f47150e4101cfe7598a41004fd7598a4101cfc7598a41014fe7398a41004fd7398a41014fc7398a41026ee7298a41006ef5298a41006ec5298a41024fe7198a41026bf4198a41026bd4198a41026ee2198a41026ec2198a41004ff7098a4100cfe7098a41004fd7098a4100cfc7098a410067f5098a410067d5098a41006df3098a41006dd3098a41006ef2098a41006ed2098a41004ff7558a410067f7558a410047f7558a4101cfe7558a4101cfc7558a410067c7558a4101c7c7558a41004ff7358a41014fe7358a41014fc7358a41026ef7258a41006ef5258a41006ec5258a41024fc7158a41026ee2158a41026ec2158a41004ff7058a4100cfe7058a41004fd7058a4100cfc7058a410067f5058a410067d5058a41006df3058a41006dd3058a41006ef2058a41006ed2058a41026f71058a41006f51058a41004ff7694a41024fe7694a41004fd7694a4127e7f6594a4101e7e6594a410067d6594a4101e7c6594a4104dbe7494a41005bd7494a4123e7f7694a4127e7e7694a410067d7694a4123e7c7694a410073e7494a410073d7494a411de7e6394a410067d6394a4127e7c6394a4123e7e6294a410067d6294a4127f3f4194a41287774194a414d57f7094a414d57d7094a4127e7f6094a411c67e6094a414ce7d6094a411c67c6094a414cf5f3094a414cf5d3094a4127f771094a414cf751094a41004ff7654a41004fd7654a41024fc7654a4123e7f7614a4125e7e7614a410f67d7614a4123e7c7614a411be7e6314a410067d6314a4125e7c6314a410f76e7214a4123e7e6214a4125f6e6214a410066e6214a410067d6214a4125f6d6214a410066d6214a4125f3f4114a41267774114a410f57f7014a414c57d7014a4125e7f6014a411b67e6014a414be7d6014a411b67c6014a414bf5f3014a414bf5d3014a4125f771014a414bf751014a41006ee6290a41006ed6290a41025f67190a41005f57190a410057f7550a410f57c7550a41006ee6250a41006ed6250a4104fac4250a41005f77150a41025f47150a41004ff768ca41024fe768ca41004fd768ca4104dbe748ca41005bd748ca41006ee628ca41006ed628ca41004ff764ca41004fd764ca41024fc764ca410057f754ca410f57c754ca41006ee624ca41006ed624ca41005f7714ca41025f4714ca4101cfe76d95410de7e65d954104cfe74d9541024fd74d954104cfc74d95410de7f54d9541014fe73d9541004fd73d9541014fc73d95410de7f53d
  | 21 => 0xc4258b4104eac4258b41006ef3258b41006ec3258b41004ff7058b4100cfe7058b41004fd7058b4100cfc7058b410067f5058b410067d5058b4104ebf4058b41006bd4058b41006df3058b41006dd3058b41006ef2058b41006ed2058b41004ff7694b4104cfe7694b41004fd7694b412867f6594b4101e7e6594b410067d6594b4101e7c6594b4104dbc7494b412873e5494b410073d5494b4123e7f7694b412867e7694b410067d7694b4123e7c7694b410073f7494b412873c7494b411de7e6394b410067d6394b411de7c6394b412873f4394b410073d4394b4123e7e6294b410067d6294b412873c4294b415057f7094b415057d7094b412867f6094b411c67e6094b414fe7d6094b411c67c6094b412873f4094b414ff3d4094b414ff5f3094b414ff5d3094b41004ff7654b41004fd7654b4104cfc7654b41005bf7454b4104dbc7454b4123e7f7614b412667e7614b4110e7d7614b4123e7c7614b412673e7414b4110f3d7414b411be7e6314b410067d6314b411be7c6314b412673f4314b410073d4314b4110f6e7214b4123e7e6214b412676e6214b410066e6214b410067d6214b412676d6214b410066d6214b412673c4214b4110d7f7014b414f57d7014b412667f6014b411b67e6014b414ee7d6014b411b67c6014b412673f4014b414ef3d4014b414ef5f3014b414ef5d3014b4104dbd7690b41006bd7690b41005bf7590b41005bd7590b41005bd7390b4104fae7290b41006bd6290b410073e5290b410073c5290b41025be7190b41025bc7190b414e5bf7090b414e5bd7090b4116ebe6090b4104ebc6090b414df3f5090b414df3d5090b414df9f3090b414df9d3090b414dfaf2090b414dfad2090b41004ff768cb4104cfe768cb41004fd768cb41005bf748cb4104dbc748cb41016de638cb41006dd638cb41004ff764cb41004fd764cb4104cfc764cb410057f754cb4110d7c754cb41005bf744cb4104dbc744cb4101cff765474104cfc765474101e7e65547410067d6554741005bf745474104dbc74547410073d5454741005df7354741105dc7354741027b641547410267f75596410f67f5459641004ff7359641014fe7359641014fc73596410f67f5359641004ff7259641004fc72596410f67c5259641024fc71596410267e51596410267c5159641026bf4159641026bd4159641004ff705964100cfe7059641004fd705964100cfc70596410f67f50596410067d5059641006df3059641006dd305964101cff7655241024fc765524101e7e65552410067d6555241005f77155241025f4715524104fb74155241004ff7558e410067f7558e410047f7558e4101cfe7558e4101cfc7558e410067c7558e4101c7c7558e41026df7358e410eede4358e41004ff7258e41004fc7258e41024fc7158e41026bf4158e41
  | 22 => 0x9511a6dc63d0951004fe7690951004fd7690951004fc76909510057f759095101d7c7590951006df639095118edc6390951006ef6290951006ec6290951004ff7650951004fe7650951004fc76509510057f755095101d7c7550951006bf645095104ebc6450951006df635095117edc6350951006ef6250951006ec6250951004fe7610951004fd761095104cfc761095101d7e75109510057d7510951006df631095115edc6310951007ad4210951004fe768c951004fd768c951004fc768c9510057f758c95101d7c758c951006df638c951016dc638c951004ff764c951004fe764c951004fc764c9510057f754c95101d7c754c951006df634c951016dc634c95104e7f7559741024fc745974104e7e545974104e7c5459741004ff7359741014fe7359741014fc73597410067e535974110e7c5359741004ff7259741004fc725974110e7c525974110e7f5159741004ff705974100cfe7059741004fd705974100cfc705974110e7f50597410067d5059741006df3059741006dd305974104dbf76553410c6bf765534104f3f755534104f3f655534101ebe655534104ebc655534104f3c6555341005bf73553415373e535534110f3c5355341005bc725534110f3c5255341025be7155341025bc715534110f3f515534152dbf705534152dbd705534110f3f50553415273d50553415279f30553415279d3055341004ff7558f4101cfe7558f4101cfc7558f41024fc7458f4104edf7358f41006df5358f41106dc5358f4104edf4358f4104edc4358f41004ff7258f41004fc7258f41106dc3258f41106df3158f41004ff7058f4100cfe7058f41004fd7058f4100cfc7058f410067f5058f410067d5058f41106df3058f41006dd3058f41004ff7654f41004fd7654f4104cfc7654f4151e7f6554f4101e7c6554f4104dbe7454f4151f3e5454f4104dbf7650f410bebf7650f41005bf7550f41005bd7550f4104f9f7350f41016be6350f41016bc6350f41005bc7250f41025be7150f41025bc7150f41515bf7050f41515bd7050f4150f3f5050f4150f3d5050f411079f3050f4150f9d3050f4101cfe7598b41004fd7598b4101cfc7598b41024fe7498b41014fe7398b41004fd7398b41014fc7398b4104eee7298b41006ef5298b41006ec5298b4104eef4298b4104eec4298b41006ef3298b41006ec3298b41004ff7098b4100cfe7098b41004fd7098b4100cfc7098b410067f5098b410067d5098b41006df3098b41006dd3098b41006ef2098b41006ed2098b41004ff7558b410067f7558b410047f7558b4101cfe7558b4101cfc7558b410067c7558b4101c7c7558b41024fc7458b41024bc7458b41004ff7358b41014fe7358b41014fc7358b4104eef7258b41006ef5258b41006ec5258b4104eef4258b4104ebc4258b4104ee
  | 23 => 0x56edc10d8d5111edc6358d51565f77158d510adde7618d5111ede7618d5111f5e7518d5111f5d7518d51396df6518d513965f6518d51006df6418d51006de6418d51006dd6418d51006dc6418d5155f5f5418d510075d5418d5155f5c5218d5139edf6118d5155fd75118d513975e5118d513975c5118d5155fd45118d5111ddf7018d51005dd7018d51006df6018d51006de6018d51006dd6018d51006dc6018d5155f5f5018d510075d5018d510257c7654d510167c7654d510247c7654d510057f7454d5151e7c6454d5101d7f7354d5101f5f7354d510075f6354d510167e6354d510167c6354d5111f5c6354d510165c6354d510057c7254d51007777154d510257e7154d510257c7154d51007747154d5101e7f6154d5101f776154d515557f7054d515557d7054d5154e7f6054d5154e7d6054d5111f5f3054d5154f5d3054d51004fe76d0d51004fd76d0d5104cfc76d0d5101d7e75d0d510057d75d0d51006df63d0d51016dc63d0d51004ff7650d51004fe7650d51004fc7650d5101d7e7550d510057d7550d51006df6350d51016dc6350d51006df63d8951006dc63d8951024fd75d895104cfe74d8951004fd74d8951014fe73d8951004fd73d8951014fc73d895107eee52d895107eed52d895107e7c52d8951004ff70d895100cfe70d8951004fd70d895100cfc70d895107e7f50d89510067d50d8951006df30d8951006dd30d8951006ee20d8951006ec20d8951005be7498951005bd749895111dde7398951005dd7398951006df6398951006dc6398951006ef6298951065f57198951005df735895111ddc7358951006df6358951006dc635895108df77158951006df6318951006dc6318951006ed621895123e7f7518951024fd751895104cfe7418951004fd741895103e7f54189510067d5418951014fe7318951004fd7318951014fc731895103e7f53189510067d531895103eee521895103eed521895125e7e511895125e7c5118951004ff701895100cfe7018951004fd701895100cfc701895103e7f50189510067d5018951006df3018951006dd3018951006ee2018951006ec20189510247e76949510057d74949510067f64949512867c64949510057d73949510067f63949510075f63949510065f63949511de7e63949511de7c63949510075c63949511de5c639495101d7e729495101f6e72949510067f62949510076f629495123e7c62949510076c62949510066c62949510257e71949510077671949510077571949510257c719495101e7f619495101f7761949515457f70949515457d709495153e7f60949511c67e609495153e7d60949511c67c609495153f5f309495153f5d3094951004fe76d0951004fd76d095104cfc76d095101d7e75d09510057d75d0951006bf64d095104ebc64d0951006df63d
  | 24 => 0xe758ca510057d758ca51006ee628ca51006ed628ca51004ff764ca51004fd764ca51024fc764ca510057f754ca5101d7c754ca51006ee624ca51006ed624ca51024fd75d91510f6be54d91510f6bd54d9151014fe73d9151004fd73d9151014fc73d9151004fe72d9151004fd72d91510f67c52d9151004ff70d915100cfe70d9151004fd70d915100cfc70d91510f67f50d91510067d50d9151006be40d9151006bc40d9151006df30d9151006dd30d915128e7f6599151006bf649915111dde7399151005dd7399151005ee7299151005ed72991510ddf57199151005df735915111ddc735915110df771591514ae7f651915104ebe6419151006bd64191510247c765515101d7f745515101f3f74551510073f645515104e7e645515104e7c64551510073c64551510057f73551512167e63551512167c63551512165c63551510057c72551510077771551510257e71551510257c715515100774715515101e7f615515101f77615515157d7f705515157d7d70551515767f60551515767d60551515775f30551515775d3055151014fe76d8d5111ede63d8d51024fd75d8d51014fc75d8d5104cfe74d8d51004fd74d8d5111ede53d8d510aedd53d8d5111ede43d8d5111edc43d8d51004fe72d8d51004fd72d8d510ae7c52d8d5111edf32d8d5111edc32d8d5101cfd71d8d5111edf31d8d51004ff70d8d5100cfe70d8d51004fd70d8d5100cfc70d8d510ae7f50d8d510067d50d8d5111edf30d8d51006de30d8d51006dd30d8d5111edc30d8d5111dde76d8d51014de76d8d5156f5f75d8d510af5c75d8d51006df64d8d51006de64d8d51006dd64d8d51006dc64d8d510af5f54d8d510075d54d8d510af5c52d8d510afd751d8d5156f5e51d8d5156f5c51d8d510afd451d8d51005df70d8d51005dd70d8d51006df60d8d51006de60d8d51006dd60d8d51006dc60d8d510af5f50d8d510075d50d8d5156edf75d8d5111ede75d8d510aedc75d8d51006df74d8d51006de74d8d51006dd74d8d51006dc74d8d510aedf54d8d510aede54d8d510aedd54d8d510aedc54d8d51006df72d8d51006de72d8d51006dd72d8d51006dc72d8d510aedf52d8d510aede52d8d510aedd52d8d510aedc52d8d510ae5c52d8d510aedf71d8d5156ede71d8d510aedd71d8d5156edc71d8d510aedf51d8d5156ede51d8d5156edc51d8d5156ede41d8d5156edc41d8d5156ede21d8d5156edc21d8d51006df70d8d51004df70d8d51006de70d8d51006dd70d8d51004dd70d8d51006dc70d8d510aedf50d8d510ae5f50d8d510aede50d8d510aedd50d8d510065d50d8d510aedc50d8d51006df40d8d51006de40d8d51006dd40d8d51006dc40d8d51006df20d8d51006de20d8d51006dd20d8d51006dc20d8d5156edf10d8d51006de10d8d51006dd10d8d51
  | 25 => 0x52510063d649525112d7e739525112d7c73952510057e729525128f76719525128d7d71952514b775719525100575719525101e7e619525101f76619525128f3f41952514b57f709525159d7d709525128e7f60952515967d60952515975f30952515975d3095251004ff7458e5104cfc7458e510067e5458e5109e7c5458e51026df7358e5112e7e5358e5112ede5358e5112e5e5358e5109edd5358e5112e7c5358e51004ff7258e51004fc7258e5109e7c5258e51024fe7158e51024fc7158e510267f5158e510267d5158e51026de3158e51026dc3158e51004ff7058e5100cfe7058e51004fd7058e5100cfc7058e5109e7f5058e510067d5058e5112edf3058e51006dd3058e5104cff76d0e51024fe76d0e51004fd76d0e5101d7e75d0e510057d75d0e5104ebe64d0e51006bd64d0e51004ff7650e51004fd7650e51024fc7650e510057f7550e5101d7c7550e5104ebe6450e51006bd6450e5123e7f7598a5104cfe7498a51004fd7498a510067e5498a5108e7c5498a51014fe7398a51004fd7398a51014fc7398a510067e5398a5108e7c5398a51026ee7298a5108eee5298a5108eed5298a51024fe7198a510267f5198a510267d5198a51026ee2198a51026ec2198a51004ff7098a5100cfe7098a51004fd7098a5100cfc7098a5108e7f5098a510067d5098a51006df3098a51006dd3098a51006ef2098a51006ed2098a51004ff7458a5104cfc7458a51004ff7358a51014fe7358a51014fc7358a51026ef7258a51066ee5258a51066ed5258a510667c5258a51024fc7158a51026ee2158a51026ec2158a51004ff7058a5100cfe7058a51004fd7058a5100cfc7058a510667f5058a510067d5058a51006df3058a51006dd3058a51006ef2058a51006ed2058a514b57e7494a512867e6494a510067d6494a5112d7e7394a5112d7c7394a511de7e6394a510067d6394a5127e7c6394a5101d7e7294a5101f6e7294a5123e7e6294a5127f6e6294a510066e6294a510067d6294a5127f6d6294a510066d6294a5127f767194a5127d7d7194a51007757194a51005757194a5101e7e6194a5101f766194a5158d7f7094a5158d7d7094a5127e7f6094a511c67e6094a515867d6094a511c67c6094a515875f3094a515875d3094a5104cff76d0a51024fe76d0a51004fd76d0a5101d7e75d0a510057d75d0a51006ee62d0a51006ed62d0a51004ff7690a51024fe7690a51004fd7690a5101d7e7590a510057d7590a5104ebe6490a51006bd6490a51004ff7650a51004fd7650a51024fc7650a510057f7550a5101d7c7550a5104cff7610a51024fe7610a51004fd7610a514b57f7510a5101d7c7510a5104ebe6410a51006bd6410a51006ee6210a51006ed6210a51007ad4210a51004ff768ca51024fe768ca51004fd768ca5101d7
  | 26 => 0x1bc7e76949320067f64949322867e64949320067d64949322867c649493223e7f63949321bd7e72949321de7f62949321df6f329493223f5c32949321df6c32949321df4c329493227e7c61949325cd7f70949325cd7d70949325c67f60949321c67e60949325c67d60949321c67c60949321df5f30949325c75d309493201cff7654932014fe76549321d4fd7654932014fc76549320067f655493201e7c6554932005df7354932015dc73549321d7cc32549321dd7e761493213e7e76149321dc7e76149320067f64149322667e64149320067d64149322667c641493223e7f63149321dd7e721493213f6e72149321be7f62149321bf6f321493223f5c32149321bf6c321493225e7c611493213d7f70149325bd7d70149325b67f60149321b67e60149325b67d60149321b67c60149321bf5f30149325b75d30149325b76e20149325b76c2014932014fe76d0932014fc76d093213d7e75d09320057d75d09320067f65d09321ae7c65d0932006bf64d093204ebc64d0932015de73d0932005dd73d093215cfe76909320067f65909321967c65909320076c529093218fcc329093204cff7650932014fe765093217cfd7650932014fc76509320057f755093213d7c75509320067f65509321867c6550932006bf645093204ebc6450932005df7350932015dc73509320076c525093217fcc325093218cfe76109320067f65109321667c6510932007ad42109320075f658c9320075c658c932015de728c932017ce728c932016df628c932017cf628c93223f5e528c93223f5c528c9325addf708c9325addd708c9325a6df608c9325a6dd608c9325a75f508c9325a75d508c9320067f65d85320067c65d853201cfe75d8532004fd75d853201cfc75d853204cfe74d8532004fd74d85320067e52d85320067c52d8532086f631d8532004ff70d853200cfe70d8532004fd70d853200cfc70d85320067f50d85320067d50d8532086df30d8532006dd30d8532006f610d8532006f410d853213d7e75985320057d75985320067f65985320067c6598532005be7498532005bd7498532006f761985320057f755853213d7c75585320067f65585320067c65585320067f65185320067c65185322bedf6318532026f66118532006f56118532026bf74592510debe54592510debd54592514b67c5459251004ff7359251014fe7359251014fc73592510067e53592510de7c5359251004ff7259251004fc72592510de7c5259251024fc71592510267f51592510267d5159251026be4159251026bc4159251004ff705925100cfe7059251004fd705925100cfc70592510de7f50592510067d5059251006bf4059251006bd4059251006df3059251006dd305925101d7e749525101f3e749525128e7f649525128f3e64952514b67d649525128f3d649
  | 27 => 0xf73d95321de7e73d95321de7d73d95321de7c73d95321de7f43d95321de7e43d95321de7d43d95321de7c43d95321de7f72d953213e7e72d95321de7d72d95321de7f32d95321de7e32d95321de7c32d95320067f71d95320067e71d95320067d71d95320067c71d95321de7f31d95321de7e31d95321de7d31d95321de7c31d95320067f70d95320047f70d95320067e70d95320067d70d95320047d70d95320067c70d95320067f40d95320067e40d95320067d40d95320067c40d95321de7f30d95321de5f30d95321de7e30d95321de7d30d95320065d30d95321de7c30d95320067f20d95320067e20d95320067d20d95320067c20d95320067f10d95320067e10d95320067d10d95320067c10d953213e7c65595325d5ef72595321dcff75595320067f7559532004ff745953204cfc74595321d4ff7359532006df73595325d4ff7259532006ef725953213e7c5259532004ff7159532024fc7159532004ff705953200cfe7059532004fd705953200cfc705953213e7f50595320067d50595321d6df3059532006dd30595321dd7e761953213e7e76195321dc7e76195321be7f63195321be7f62195321bf6f32195321bf5c32195321bf6c321953213d7f70195320057d70195320067f60195320067e60195320067d60195320067c60195321bf5f30195320075d301953204cfe76d91320067f65d91320067c65d913201cfe75d9132004fd75d913201cfc75d913218cff73d913218cfd73d913218ebf43d913218ebd43d9132024fe71d9132004fd71d9132004ff70d913200cfe70d9132004fd70d913200cfc70d91320067f50d91320067d50d9132006be40d9132006bc40d913218edf30d9132006dd30d913213d7e75991320057d75991320067f65991320067c6599132006bf649913217ded7299132005f67199132005f571991320057f755913213d7c75591320067f65591320067c65591321a5ef7259132004ff75591320067f75591320047f755913201cfe755913201cfc75591320067c755913201c7c7559132006bf745913217cff7359132006df73591321a4ff7259132006ef7259132004ff7159132024fc7159132004ff705913200cfe7059132004fd705913200cfc70591320067f50591320067d505913217edf3059132006dd305913218cfe76191320067f65191320067c651913204ebe6419132006bd641913204cff7695132004fe7695132004fd769513204cfc76951320067f659513201e7c659513213f3f5495132015de7395132005dd7395132005ee7295132005ed7295132004ff7655132004fe7655132004fd7655132004fc76551320067f655513201e7c65551321bcfe76949321de7f659493201e7e65949320067d659493201e7c659493213f6f52949321dfcc32949321bd7e76949320067e7694932
  | 28 => 0x5232006bd649523214f3f5495232005ee7295232005ed7295232004ff7655232004fe7655232004fd7655232004fc765523201e7e65552320067d655523204ebe6455232006bd6455232014ff7694a3201cfe7694a32014fd7694a3201e7e6594a320067d6594a32015de7394a32005dd7394a3214f6f5294a321dfcf3294a3223e7f7694a3223e7e7694a3223e7d7694a3223e7c7694a3223e7f6494a322867e6494a320067d6494a3223e7c6494a3223f5e7394a3223f5d7394a3223e7e6294a3223f5f3294a321df6f3294a321df4f3294a3223f6c3294a3227e7e6194a321df5c3194a3223d7f7094a325f57d7094a3223e7f6094a321c67e6094a325ee7d6094a3223e7c6094a321df5f3094a325ef5d3094a325d4ff7654a321d7cf3254a3223e7f7614a3223e7e7614a3223e7d7614a3223e7c7614a3223e7f6414a322667e6414a320067d6414a3223e7c6414a3223f5e7314a3223f5d7314a3223f6e7214a3223e7e6214a3223f5f3214a321bf6f3214a3223f6c3214a3225e7e6114a321bf5c3114a3223d7f7014a325e57d7014a3223e7f6014a321b67e6014a325de7d6014a3223e7c6014a321bf5f3014a325df5d3014a325df6e2014a3223f6c2014a3217cfd76d0a3214d7e75d0a320057d75d0a32014ff7690a32014fd7690a3204ebe6490a32006bd6490a32015de7390a32005dd7390a3223f6c5290a321a4ff7650a320057f7550a3214d7c7550a320076c5250a32014ff7610a32014fd7610a3204cfc7610a3204ebe6410a32006bd6410a32015de7310a32005dd7310a32007ad4210a3214d7e75d86320057d75d8632005be74d8632005bd74d863214d7e75986320057d7598632005be7498632005bd7498632006f76198632004ff755863201cfe755863201cfc7558632004ff745863204cfc74586320067e52586320067c525863205ef631586322bedc3158632004ff705863200cfe7058632004fd705863200cfc70586320067f50586320067d505863205edf3058632006dd3058632006f71058632006f51058632026f66118632006f5611863201cfe76d953213e7e65d953204cfe74d9532004fd74d953213e7f54d953213e7c54d95321dcff73d95321dcfd73d95321de7f53d95321de7d53d9532014fd72d953213e7f52d9532024fe71d9532004fd71d953213e7f51d953213e7c51d9532004ff70d953200cfe70d9532004fd70d953200cfc70d953213e7f50d95320067e50d95320067d50d953213e7c50d95321dedf30d9532006dd30d95321bd7e76d953201c7e76d95321df6f32d95321df5c32d95321df6c32d95320057f70d95320057d70d95320067f60d95320067e60d95320067d60d95320067c60d95321df5f30d95320075d30d95320067f74d95320067e74d95320067d74d95320067c74d95321de7
  | 29 => 0x4fac6350842617af535084260fae5350842007ad535084260fac5350842007af7150842007ae7150842007ad7150842007ac715084204faf615084204fae615084204fad615084204fac6150842617af5150842617ac515084260faf315084260fac3150842607af70508425ffae7050842607ad70508425ffac705084204faf605084204eaf605084204fae605084204fad60508425fead605084204fac60508425ffaf50508425ff2f50508425ffae50508425ffad50508425ff2d50508425ffac50508425ffaf30508425ff8f30508425ffae30508425ffad30508425ff8d30508425ffac30508425ffaf10508425ffae10508425ffad10508425ffac1050842004ff75584420067f75584420047f755844201cfe755844201cfc75584420067c755844201c7c7558442004ff7358442006df7358442004df7358442014fe7358442014fc7358442006dc7358442014dc73584420067e52584420067c525844204ef7715844204ef7415844204ef44158442004ff705844200cfe7058442004fd705844200cfc70584420067f50584420067d5058442006df3058442006dd3058442006f71058442006f5105844214e7e65d96321bdee72d96321d4fd75d963204cfe74d9632004fd74d963214e7c54d9632006dd73d96321de7e53d96321de7c53d96321bcfe72d9632006ee72d9632024fe71d9632004fd71d963214e7f51d9632004ff70d963200cfe70d9632004fd70d963200cfc70d963214e7f50d96320067d50d96321dedf30d9632006dd30d963201cff765963214e7c65596320067f7559632004ff745963204cfc745963214e7f54596321d67f53596321d67d5359632014fc725963214e7c5259632004ff7159632024fc715963214e7c5159632004ff705963200cfe7059632004fd705963200cfc705963214e7f50596320067d50596321d6df3059632006dd305963215dee72d923201cfe75d9232004fd75d923201cfc75d9232006dd73d923215cfe72d9232006ee72d9232024fe71d9232004fd71d9232004ff70d923200cfe70d9232004fd70d923200cfc70d92320067f50d92320067d50d923218edf30d9232006dd30d923217cfd7699232006bf649923204cff76592320057f755923214d7c7559232004ff75592320067f75592320047f755923201cfe755923201cfc75592320067c755923201c7c7559232006bf745923217ebf435923217ebd4359232004ff7159232024fc7159232004ff705923200cfe7059232004fd705923200cfc70592320067f50592320067d5059232006bf4059232006bd405923217edf3059232006dd305923214d7e75192320057d751923204ebe6419232006bd641923218dee721923204cff7695232004fe7695232004fd769523204cfc76952320067f659523201e7c659523204ebe649
  | 30 => 0x870585420067f65185420067c6518542026f66118542006f5611854204e7f755944204cfe745944204cfc745944204e7e545944204e7c5459442004ff7359442014fe7359442014fc73594420067e53594421667c5359442164fc72594421667c5259442004ff7159442024fc71594421667f515944204ebf4159442004ff705944200cfe7059442004fd705944200cfc70594421667f50594420067d5059442006df3059442006dd3059442004ff7558c4201cfe7558c4201cfc7558c4204edf7358c42006df5358c4215edc5358c4204edf4358c4204edc4358c4215edc3258c42004ff7158c42024fc7158c4204ebf4158c4215edf3158c42004ff7058c4200cfe7058c42004fd7058c4200cfc7058c420067f5058c420067d5058c4215edf3058c42006dd3058c42004ff7654c42004fd7654c4204cfc7654c4251e7f6554c4201e7c6554c42194ff769484204cfe769484201cfd769484204cfc769484201e7e65948420067d659484204dbe7494842005bd749484223e7f769484223e7e769484223e7d769484223e7c769484223f3e749484223f3d74948422867e64948421de7e63948420067d639484223e7c639484223d7e729484223e7e629484223f3f429484223f6e42948422876d429484227e7e619484223d7f709484263d7d709484223e7f60948421c67e60948426367d609484223e7c60948426373e40948422873c40948426375f30948426375d3094842194ff765484223e7f761484223e7e761484223e7d761484223e7c761484223f3e741484223f3d74148422667e64148421be7e63148420067d631484223e7c631484223d7e721484223f6e721484223e7e621484223f3f421484223f6e42148422676d421484225e7e611484223d7f701484262d7d701484223e7f60148421b67e60148426267d601484223e7c60148426273e40148422673c40148426275f30148426275d30148426276e201484223f6c201484204dbf7650842006bf7650842004bf76508420073f75508420073c755084204dbf725084204faf725084261ebe625084204fae6250842617af525084223f3e5250842007ae52508420072e5250842007ad525084223f3c5250842617ac52508420072c525084260faf325084260fac3250842005bf7150842155be7050842155bc705084204ebf60508425febd60508425ff3f50508425ff3d50508425ff9f30508425ff9d30508425ffaf20508425ffae20508425ffad20508425ffac205084204faf765084204daf7650842006af7650842007af75508420072f7550842617ae7550842007ad7550842617ac75508420072c755084204faf655084204fae655084204fad655084204fac6550842007af735084260fae7350842007ad735084260fac735084204faf635084204fae635084204fad6350842
  | 31 => 0x95420067f60195420067e60195420067d60195420067c60195420073f40195420073d40195420075f30195420075d30195420076f20195420076d201954201cfc76551420067f655514201e7c655514204f3c5455142005ef7255142005ec725514204fac4255142014fe76d8d420067f65d8d420067c65d8d4217ede63d8d4201cfe75d8d42004fd75d8d4201cfc75d8d4217ede43d8d4204cfd72d8d4217edf32d8d42024fe71d8d42004fd71d8d4217edc31d8d42004ff70d8d4200cfe70d8d42004fd70d8d4200cfc70d8d420067f50d8d420067d50d8d4217edf30d8d42006dd30d8d420057f7558d421857c7558d420067f6558d420067c6558d4217edc6358d42004ff7654d42004fe7654d42004fc7654d420067f6554d4201e7c6554d42014fc7650d420067f6550d421ee7c6550d42006df6350d42016dc6350d4204f9c4350d42005ef7250d42005ec7250d4204fac4250d421acfe76949420067f659494201e7e65949420067d659494201e7c65949421876f52949420057e76949420067e76949420047e76949420067f63949421de7e63949421de7c63949421857e72949422876f429494227e7c619494265d7f709494265d7d70949426667f60949421c67e60949426667d60949421c67c60949426673f40949426673d40949426675f30949426675d30949426676f20949426676d209494201cff7654942184fd765494204cfc76549420067f655494201e7c6554942005bf745494204dbc74549420057e76149421867e76149420047e76149420067f63149421be7e63149421be7c631494265d7e72149421876e72149422676f421494225e7c61149421857f70149426557d701494264e7f60149421b67e601494264e7d60149421b67c601494264f3f401494264f3d401494264f5f301494264f5d301494264f6f201494264f6d20149420067f65909421967c659094204dee729094204eef62909420073f65909420073c659094204dbe729094204dae729094204ebf629094204faf629094223f3e529094223f3c529094261dbf709094261dbd709094216ebe609094216ebc60909426473f50909426473d50909426479f30909426479d3090942647af2090942647ad20909420067f65d85420067c65d854201cfe75d8542004fd75d854201cfc75d8542014fe73d8542004fd73d8542014fc73d85420067e52d85420067c52d8542006be42d8542004ff70d854200cfe70d8542004fd70d854200cfc70d85420067f50d85420067d50d8542006bf40d8542006bd40d8542006df30d8542006dd30d8542006ef20d8542006ed20d85421857e75985420057d75985420067f65985420067c6598542006f761985420057f75585421857c75585420067f65585420067c6558542005df735854217ddc7358542005fb7058542175f
  | 32 => 0x4f3e75d0a4204f3d75d0a4204fae62d0a4223f3e52d0a42007ae52d0a420072e52d0a42007ad52d0a4223f3c52d0a42005bd71d0a4216dbe70d0a4204dbc70d0a4266ebf60d0a4266ebd60d0a4266f3f50d0a4266f3d50d0a4266f9f30d0a4266f9d30d0a421957e75d86420057d75d864218dde73d8642005dd73d86421957e75986420057d7598642006f76198642004ff755864201cfe755864201cfc7558642004ff7358642014fe7358642014fc73586420067e52586420067c5258642004ff705864200cfe7058642004fd705864200cfc70586420067f50586420067d5058642006df3058642006dd3058642006ef2058642006ed2058642006f71058642006f51058642026f66118642006f5611864201cfe76d95421867e65d9542184fd74d95421867f54d9542014fe73d9542004fd73d9542014fc73d95421867f53d95420067e53d95421867c53d954204cfd72d95421867f52d9542024fe71d9542004fd71d95421867f51d95421867c51d9542004ff70d954200cfe70d9542004fd70d954200cfc70d95421867f50d95420067e50d95420067d50d95421867c50d9542006df30d9542006dd30d95421857e76d954201c7e76d95420067e63d95420067c63d95422876f42d95422876c42d95420057f70d95420057d70d95420067f60d95420067e60d95420067d60d95420067c60d95420073f40d95420073d40d95420075f30d95420075d30d95420076f20d95420076d20d95420067f74d95422867e74d95420067d74d95422867c74d95420067f73d95420067e73d95420067d73d95420067c73d95422867f43d95420067e43d95422867c43d95422867f72d95421867e72d95420067d72d95422867f42d95422867c42d95420067f32d95420067c32d95420067f71d95420067e71d95420067d71d95420067c71d95422867f41d95422867c41d95420067f31d95420067c31d95420067f70d95420047f70d95420067e70d95420067d70d95420047d70d95420067c70d95422867f40d95420067e40d95420067d40d95422867c40d95420067f30d95420065f30d95420067e30d95420067d30d95420065d30d95420067c30d95420067f20d95420067e20d95420067d20d95420067c20d95420067f10d95420067e10d95420067d10d95420067c10d95421867c6559542184ff75595420067f7559542194ff7459542006bf7459542004ff7359542014fe7359542014fc73595421acff7259542006ef72595421867c5259542004ff7159542024fc7159542004ff705954200cfe7059542004fd705954200cfc70595421867f50595420067d5059542006df3059542006dd30595420057e76195421867e76195420047e76195420067e63195420067c63195422667f62195422676f42195422676c42195421857f70195420057d701
  | 33 => 0xf3014b426975d3014b426976e2014b426976c2014b42004ff755874201cfe755874201cfc7558742004ff7358742014fe7358742014fc73587420067e52587420067c525874204ebc425874204ef7715874204ef7415874204ef44158742006f73158742006f43158742004ff705874200cfe7058742004fd705874200cfc70587420067f50587420067d505874204ebf4058742006bd4058742006df3058742006dd3058742006f71058742006f510587421967e65d9642194fd75d9642006bd74d96422867e54d96422867c54d9642014fe73d9642004fd73d9642014fc73d96420067e53d96421967c53d9642006ee72d9642024fe71d9642004fd71d96421967f51d9642004ff70d964200cfe70d9642004fd70d964200cfc70d96421967f50d96420067d50d9642006df30d9642006dd30d964201cff76596421967c65596420067f75596421967f5459642004ff7359642014fe7359642014fc73596421967f535964204cfc72596421967c5259642004ff7159642024fc71596421967c5159642004ff705964200cfe7059642004fd705964200cfc70596421967f50596420067d5059642006df3059642006dd305964201cff765524201e7e65552420067d6555242005ef7255242005ec725524204faf425524218ede63d8e42014ff7658e420057f7558e421957c7558e4218edc6358e42004ff7558e420067f7558e420047f7558e4201cfe7558e4201cfc7558e420067c7558e4201c7c7558e4218ede5358e4218ede4358e4204cfc7258e4218edc3258e42004ff7158e42024fc7158e4218edc3158e42004ff7058e4200cfe7058e42004fd7058e4200cfc7058e420067f5058e420067d5058e4218edf3058e42006dd3058e42004ff7654e42004fd7654e42004fc7654e4201e7e6554e420067d6554e42016de6354e42006dd6354e42014ff7650e42016de6350e42006dd6350e42005ef7250e42005ec7250e4201cfe7694a4204cfd7694a4201e7e6594a420067d6594a4204dbe7494a42005bd7494a421976f5294a4223e7e7694a4223e7d7694a4223f3e7494a4223f3d7494a421de7e6394a420067d6394a4223e7c6394a422876f4294a4227e7e6194a4223d7f7094a4268d7d7094a4223e7f6094a421c67e6094a426867d6094a4223e7c6094a426873e4094a426873c4094a426875f3094a426875d3094a4223f6f2094a426876d2094a42164ff7654a4223e7e7614a4223e7d7614a4223f3e7414a4223f3d7414a421be7e6314a420067d6314a4223e7c6314a4223f6e7214a422676f4214a4225e7e6114a4223d7f7014a4267d7d7014a4223e7f6014a421b67e6014a426767d6014a4223e7c6014a426773e4014a426773c4014a426775f3014a426775d3014a4223f6f2014a426776d2014a42005bd76d0a4204ebd76d0a42
  | 34 => 0xc526c75d30d0c521ed7f7650c5223d7e7650c521ed7d7650c5223d7c7650c521bd7f7450c521bd7f7350c522675f4350c521bf3e4350c521bf3c4350c521bf5c4350c520057f7250c5223d7c7250c521de7e6250c521ef6e6250c520057f7150c5225d7c7150c526bd7f7050c521b57e7050c526bd7d7050c521b57c7050c521ee7f6050c526b67d6050c521bf5f3050c526b75d3050c5204e7f755974204cfc745974204e7e545974204e7c5459742004ff7359742014fe7359742014fc73597421ae7f53597420067e53597421ae7c53597421ae7f5259742004ff7159742024fc71597421ae7f51597421ae7c5159742004ff705974200cfe7059742004fd705974200cfc70597421ae7f50597420067e50597420067d50597421ae7c5059742006df3059742006dd305974204e7f745974204e7e745974204e7d745974204e7c74597420067f73597420067e73597420067d73597420067c735974204e7f435974204e7e435974204e7d435974204e7c43597420067f72597420067d72597421ae7c725974204e7f425974204e7e425974204e7d425974204e7c42597420067f32597420067c32597420067f71597420067e71597420067d71597420067c715974204e7f415974204e7e415974204e7d415974204e7c41597420067f31597420067c31597420067f70597420047f70597420067e70597420067d70597420047d70597420067c705974204e7f405974204e7e405974204e7d405974204e7c40597420067f30597420065f30597420067e30597420067d30597420065d30597420067c30597420067f20597420067e20597420067d20597420067c20597420067f10597420067e10597420067d10597420067c1059742004ff7558f4201cfe7558f4201cfc7558f4204edf7358f4204edf4358f4204edc4358f421a6df3258f42004ff7158f42024fc7158f421a6dc3158f42004ff7058f4200cfe7058f42004fd7058f4200cfc7058f420067f5058f420067d5058f421a6df3058f42006dd3058f42004ff7654f42004fd7654f4204cfc7654f4201e7e6554f420067d6554f42184fd7694b422867f6594b4201e7e6594b420067d6594b4201e7c6594b422857d7694b420067d7694b421de7e6394b420067d6394b421de7c6394b4227e7e6194b426ad7f7094b426ad7d7094b422867f6094b421c67e6094b426a67d6094b421c67c6094b422873f4094b426a73d4094b426a75f3094b426a75d3094b4201cff7654b4204cfc7654b4201e7e6554b420067d6554b42005bf7454b4204dbc7454b422657d7614b421ae7d7614b421be7e6314b420067d6314b421be7c6314b421af6e7214b4225e7e6114b421ad7f7014b4269d7d7014b422667f6014b421b67e6014b426967d6014b421b67c6014b422673f4014b426973d4014b426975
  | 35 => 0x57f74586522857c74586520067f64586520067d64586520057f73586521dd7e73586521dd7c73586520067f63586520067d63586520667e62586520676e625865223f77615865227e7e61586520057f70586521c57e70586520057d70586521c57c70586520067f60586520067d60586520075f30586520075d30586520077710586520077510586522857e74186520057d74186520067e641865223e7c64186521dd7e73186520057d731865223d7c73186520067e631865223e7c631865223f6e721865223f6e621865227d7e711865223e7f611865223f76611865227e7d611865223f75611865200675611865223d7f70186521c57e70186520057d701865223d7c701865223e7f60186520067d60186520075f30186520075d3018652196be54d9152196bd54d9152014fe73d9152004fd73d9152014fc73d91521967c52d9152024fe71d9152004fd71d9152004ff70d915200cfe70d9152004fd70d915200cfc70d91521967f50d91520067d50d9152006be40d9152006bc40d9152006df30d9152006dd30d9152006bf6499152185ed72991521adef725915204ebe6419152006bd6419152014fe76d8d521d6de63d8d5204cfe74d8d52004fd74d8d521d6de53d8d5214edd53d8d5201cfd72d8d5214e7c52d8d521d6df32d8d52024fe71d8d52004fd71d8d521d6dc31d8d52004ff70d8d5200cfe70d8d52004fd70d8d5200cfc70d8d5214e7f50d8d520067d50d8d521d6df30d8d52006dd30d8d521d6dc6358d526e5ef7258d52004fe76d0d52004fd76d0d5204cfc76d0d5201d7e75d0d520057d75d0d52004ff7650d52004fe7650d52004fc7650d520067f64949522867c64949520067f63949521de7e63949521de7c639495201d7e729495201f6e729495201e7f629495201f6f62949526dd7f70949526dd7d70949526d67f60949521c67e60949526d67d60949521c67c60949526d75f30949526d75d309495204cfe74d8552004fd74d8552014fe73d8552004fd73d8552014fc73d85520067e52d855208e7c52d855208ef651d8552004ff70d855200cfe70d8552004fd70d855200cfc70d855208e7f50d85520067d50d8552006df30d8552006dd30d8552005be7498552005bd7498552006f76198552005df73585521d5dc735855227e7f6518552026f66118552006f561185522657f76d0c5223d7e76d0c522667e76d0c5201c7e76d0c521fd7d76d0c522667d76d0c520047d76d0c5223d7c76d0c521bd7e74d0c521bd7d73d0c521bf5e63d0c521ff5d63d0c521bf3e43d0c521bf5e43d0c521bf3c43d0c5223d7e72d0c520057d72d0c521de7e62d0c521ff6e62d0c5225d7e71d0c520057d71d0c521bf5c31d0c522657f70d0c521b57e70d0c526cd7d70d0c521b57c70d0c521fe7f60d0c526c67d60d0c521bf5f30d
  | 36 => 0xc731925223d7e721925223f6e72192520056e721925223f6e621925227d7e71192520057d711925223d7f70192521c57e70192520057d701925223d7c701925223e7f60192520067d60192520075f30192520075d30192522857e74d8e520057d74d8e520067e64d8e5223e7c64d8e521dd7d73d8e521de7e63d8e5223f5e63d8e521de5e63d8e5223e7c63d8e5223d7e72d8e5223f6e72d8e520056e72d8e5223f6e62d8e5227d7e71d8e520057d71d8e5223d7f70d8e521c57e70d8e520057d70d8e5223d7c70d8e5223e7f60d8e520067d60d8e521df5f30d8e520075d30d8e521dd7f7658e520057f7458e522857c7458e520067e6458e520067c6458e5223f5f6358e521de7e6358e521de7c6358e5223f5c6358e521de5c6358e521df5e4358e5223d7c7258e5213e7e6258e5213f6e6258e5223f5c3258e520057f7158e5227d7c7158e521df5c3158e520057f7058e521c57e7058e520057d7058e521c57c7058e520067f6058e520067d6058e521df5f3058e520075d3058e522857f76d0e5223d7e76d0e522867e76d0e520047e76d0e520057d76d0e522867d76d0e520047d76d0e5223d7c76d0e521dd7e74d0e522873e64d0e520073d64d0e521df3e43d0e521df5e43d0e521df3c43d0e5223d7e72d0e520057d72d0e5227d7e71d0e520057d71d0e521df5c31d0e522857f70d0e521c57e70d0e527057d70d0e521c57c70d0e526fe7f60d0e526fe7d60d0e521df5f30d0e526ff5d30d0e520057f7650e5223d7e7650e520057d7650e5223d7c7650e521dd7f7450e520073e6450e520073d6450e521df5e6350e520075d6350e522875f4350e521df3e4350e521df3c4350e521df5c4350e520057f7250e5223d7c7250e520057f7150e5227d7c7150e526f57f7050e521c57e7050e526f57d7050e521c57c7050e526ee7f6050e526ee7d6050e521df5f3050e526ef5d3050e522857e74d865223f3e74d86520053e74d86520057d74d865223f3d74d86520053d74d865223e7f64d86520067d64d86521dd7e73d865223f5e73d86521dd5e73d86520057d73d865223f5d73d86520055d73d865223d7c73d865223e7f63d86520067d63d865223f6e72d865223f6e62d865223d7f70d86521c57e70d86520057d70d865223d7c70d865223e7f60d86520067d60d86520075f30d86520075d30d86520057d76986522857e749865227f3e74986520053e74986520057d749865227f3d74986520053d74986520067e64986520067c64986521dd7e73986520057d739865227d7c73986520067e63986520067c639865225e7e629865207f6e629865227e7f619865223f77619865227d7f70986521c57e70986520057d70986521c57c70986520067f60986520067d60986520075f30986520075d309865227f771098652007751098652
  | 37 => 0x8e521dede5358e521de5e5358e5213edd5358e521de7c5358e521dede4358e5201cfc7258e521dedc3258e52004ff7158e52024fc7158e5213e7f5158e521dedc3158e52004ff7058e5200cfe7058e52004fd7058e5200cfc7058e5213e7f5058e520067d5058e521dedf3058e52006dd3058e521dd7f7654e520167f7654e520147f7654e520057f7454e522857c7454e5251e7e6454e5201d7f7354e5201f5f7354e520167e6354e521df5e6354e520165e6354e520075d6354e520167c6354e520057f7254e520076f7254e520076c7254e5201e7e6254e5201f6e6254e520057f7154e5227d7c7154e527157f7054e521c57e7054e527157d7054e521c57c7054e5270e7f6054e5270e7d6054e521df5f3054e5270f5d3054e5204cff76d0e52004fe76d0e52004fd76d0e522857f75d0e5201d7e75d0e520057d75d0e5201d7c75d0e5204ebe64d0e52006bd64d0e52004ff7650e52004fd7650e52004fc7650e520057f7550e5201d7e7550e520057d7550e5201d7c7550e5204ebe6450e52006bd6450e52016de6350e52006dd6350e52005be74d8652005bd74d86521ddde73d8652005dd73d8652005be7498652005bd7498652006f76198652004ff745865204cfc74586520667f54586520067d5458652004ff7358652014fe7358652014fc73586520667f53586520067d5358652066f6515865227e7c5158652004ff705865200cfe7058652004fd705865200cfc70586520667f50586520067d5058652006df3058652006dd3058652006f71058652006f51058652026f66118652006f561186521dd7e73d92520057d73d925223d7c73d92520067e63d925223e7c63d925223d7e72d925223f6e72d92520056e72d925223f6e62d925227d7e71d92520057d71d925223d7f70d92521c57e70d92520057d70d925223d7c70d925223e7f60d92520067d60d92520075f30d92520075d30d92520057d76992522867f649925223f3f64992520063f64992521dd7e73992520057d73992521dd7c73992522667e62992521af6e629925227d7e71992520057d71992522857f70992521c57e70992520057d70992521c57c70992520067f60992520067d60992522873f40992520073d40992520075f30992520075d309925223f3f64592522867e64592520057f73592521dd7e73592521dd7c73592520067e63592520067c63592521867e62592521876e62592520057f715925227d7c71592520057f70592521c57e70592520057d70592521c57c70592520067f60592520067d60592520073f40592520073d40592520075f30592520075d30592522857e741925223e7f641925223f3e64192522867d641925223f3d64192520063d64192521dd7e731925223f5e73192521dd5e73192520057d731925223f5d73192520055d731925223d7
  | 38 => 0x4fd705954300cfc70595431ee7f50595430067d5059543216df3059543006dd305954301cff7655143014fe7655143214fd7655143014fc76551430067f655514301e7c6555143005df7355143015dc735514304f9c43551431ed7e75d89430057d75d894301cfe75d89430067e75d894301c7e75d8943004fd75d89430067d75d89430047d75d894301cfc75d894304cfd73d89431a6ee32d8943024fe71d8943004fd71d8943004ff70d894300cfe70d8943004fd70d894300cfc70d89430067f50d89430067d50d89431a6df30d8943006dd30d8943006ef62989430057f75589431ed7c7558943006ed621894301cfe7518943004fd751894301cfc751894304cfd731894315eed3218943024fe7118943004fd7118943004ff701894300cfe7018943004fd701894300cfc70189430067f50189430067d501894315edf3018943006dd301894301cfe75d8543004fd75d854301cfc75d854304cfd73d8543004fe72d8543004fd72d8543106f631d8543004ff70d854300cfe70d8543004fd70d854300cfc70d85430067f50d85430067d50d8543106df30d8543006dd30d8543006f761985430057f75585431ed7c75585431ed7e75185430057d7518543386df6318543026f66118543006f56118543165ee72d9252006bf6499252186be5459252186bd54592522867c5459252004ff7359252014fe7359252014fc73592520067e53592521867c5359252004ff7159252024fc71592521867f5159252004ff705925200cfe7059252004fd705925200cfc70592521867f50592520067d5059252006bf4059252006bd4059252006df3059252006dd305925204ebe6419252006bd64192521ddde7319252005dd7319252195ee721925201d7e749525201f3e74952522873e64952522867d64952520073d64952520063d64952521dd7e73952520057d73952521dd7c73952522876e72952520057d72952522876d72952520056d729525201e7e629525201f6e629525227d7e71952520057d719525228e7e61952522857f70952521c57e709525273d7d70952521c57c70952527367f60952527367d60952527375f30952527375d309525204c7f765525201d7f745525201f3f745525204e7e64552520073e645525204e3e64552520073d645525204e7c64552520057f73552521dd7e73552521dd7c73552522167e63552522167c63552520057f72552520076f72552520076c725525201e7e625525201f6e62552520057f715525227d7c715525272d7f70552521c57e705525272d7d70552521c57c70552527267f60552527267d60552527275f30552527275d30552521dede63d8e5271dee72d8e52014ff7658e5201d7c7558e521dedc6358e521df5e5358e52004ff7458e5204cfc7458e520067e5458e5213e7c5458e521de7e535
  | 39 => 0xd745974304e7c74597432167f73597432167e73597432167d73597432167c735974304e7f435974304e7e435974304e7d435974304e7c43597430067f72597430067e72597430067d72597430067c72597430047c725974304e7f425974304e7e425974304e7d425974304e7c42597432167f32597432167e32597432167d32597432167c32597430067f71597430067e71597430067d71597430067c715974304e7f415974304e3f415974304e7e415974304e7d415974304e7c41597432167f31597432167e31597432167d31597432167c31597430067f70597430047f70597430067e70597430067d70597430047d70597430067c705974304e7f405974304e7e405974304e7d405974304e7c40597432167f30597432165f30597432167e30597432167d30597430065d30597432167c30597430067f20597430067e20597430067d20597430067c20597430067f10597430067e10597430067d10597430067c105974323e7f7598b4301cfe7598b43004fd7598b4301cfc7598b4323e7c7598b43014fe7498b4304eee7298b4304eef4298b4304eec4298b4318eed3298b43024fe7198b43004fd7198b4304ebf4198b4318edc3198b43004ff7098b4300cfe7098b43004fd7098b4300cfc7098b430067f5098b430067d5098b4318edf3098b43006dd3098b43006ef2098b43006ed2098b43004ff7558b430067f7558b430047f7558b4301cfe7558b4301cfc7558b430067c7558b4301c7c7558b43014fc7458b4304eef7258b4304eef4258b4304eec4258b4317eee3258b43004ff7158b43024fc7158b43004ff7058b4300cfe7058b43004fd7058b4300cfc7058b430067f5058b430067d5058b4317edf3058b43006dd3058b43006ef2058b43006ed2058b43004ff755874301cfe755874301cfc7558743014fc7458743004ff7258743004fc725874304ef7715874304ef7415874304ef441587430d6f63158743386dc3158743004ff705874300cfe7058743004fd705874300cfc70587430067f50587430067d50587430d6df3058743006dd3058743006f71058743006f5105874301cfe76d95431ee7e65d9543014fd74d95431ee7f54d954304cff73d954304cfd73d95432267f53d95432267d53d9543004fe72d9543004fd72d95431ee7c52d9543024fe71d9543004fd71d95431ee7c51d9543004ff70d954300cfe70d9543004fd70d954300cfc70d95431ee7f50d95430067d50d9543226df30d9543006dd30d95431ee7c6559543745bf7459543224ff75595430067f7559543744ff7459543006bf745954351e7e545954351e7c5459543214ff7359543006df73595432167e53595432167c5359543004ff7259543004fc72595431ee7c5259543004ff7159543024fc71595431ee7f5159543004ff705954300cfe7059543
  | 40 => 0x8554004fd72d855410e7c52d855410ef651d8554004ff70d855400cfe70d8554004fd70d855400cfc70d855410e7f50d85540067d50d8554006df30d8554006dd30d8554005ee7298554005ed7298554006f76198554005df7358554215dc735855428e7f6518554026f66118554006f5611855404cfe76d9153014fd75d91537467d75d915375ebe54d915375ebd54d915351e7c54d915301cfd73d91537467e53d91537467c53d9153746bf43d9153004fe72d9153004fd72d915375e7c52d9153024fe71d9153004fd71d915375e7f51d9153004ff70d915300cfe70d9153004fd70d915300cfc70d915375e7f50d91530067d50d9153746df30d9153006dd30d9153006bf64991531eddd73991531fddf735915304ebe6419153006bd64191530157e76951532267e76951530147e769515301d7e749515301f3e749515351e7f64951530073f64951530063f649515351f3c64951530157e73951532275e739515351f5d73951530157c739515301e7f639515301f5f63951530057e72951530057d719515328e7c619515351d7f70951537557d709515374e7f609515374e7d60951532275f309515374f5d3095153014fd75d89535d67d75d895304cfe74d8953004fd74d895301cfd73d89536e6ee52d89536e67c52d89535d6ee32d8953024fe71d8953004fd71d8953004ff70d895300cfe70d8953004fd70d895300cfc70d89536e67f50d89530067d50d89535d6df30d8953006dd30d8953006ef6298953006ed621895323e7f7518953014fd751895304cfe7418953004fd74189530067e541895371e7c541895301cfd73189531be7e53189531be7c531895371eed521895323e7c52189531beed3218953024fe7118953004fd711895371e7f5118953004ff701895300cfe7018953004fd701895300cfc701895371e7f50189530067d50189531bedf3018953006dd3018953024fe76d8553014fd75d855304cfe74d8553004fd74d855301cfd73d8553004fe72d8553004fd72d85535667c52d8553566f651d855339ef631d8553004ff70d855300cfe70d8553004fd70d855300cfc70d85535667f50d85530067d50d855339edf30d8553006dd30d85533a67f659855356edf6398553006f761985533a67f6518553005be7418553005bd741855356edf6318553026f66118553006f5611855304e7f7559743014fe7459743014fc745974304e7e545974304e7c54597432167f53597432167d5359743004ff7259743004fc72597431fe7f52597431fe7c5259743004ff7159743024fc71597431fe7f51597431fe7c515974304ebf4159743004ff705974300cfe7059743004fd705974300cfc70597431fe7f50597430067e50597430067d50597431fe7c5059743216df3059743006dd305974304e7f745974304e7e745974304e7
  | 41 => 0x4cfc7458e5404edf7358e54226de5358e5404edf4358e5404edc4358e54004ff7258e54004fc7258e541ee7c5258e54226df3258e54004ff7158e54024fc7158e5404ebf4158e54226dc3158e54004ff7058e5400cfe7058e54004fd7058e5400cfc7058e541ee7f5058e540067d5058e54226df3058e54006dd3058e5423e7f7598a5404cfe7498a5404e7f5498a5404e7d5498a54014fe7398a54004fd7398a54014fc7398a541967f5398a5404eee7298a54196ed5298a5404eef4298a5404eec4298a54024fe7198a54004fd7198a541967c5198a5404ebf4198a54004ff7098a5400cfe7098a54004fd7098a5400cfc7098a541967f5098a540067d5098a54006df3098a54006dd3098a54006ef2098a54006ed2098a5404cfc7458a54004ff7358a54014fe7358a54014fc7358a5404eef7258a54186ee5258a541867c5258a5404eef4258a5404eec4258a54004ff7158a54024fc7158a54004ff7058a5400cfe7058a54004fd7058a5400cfc7058a541867f5058a540067d5058a54006df3058a54006dd3058a54006ef2058a54006ed2058a5404cfc745865404e7f545865404e7d5458654004ff7358654014fe7358654014fc73586540de7f5358654004ff7258654004fc72586540de7c525865404ef771586540def6515865428e7c515865404ef7415865404ef44158654004ff705865400cfe7058654004fd705865400cfc70586540de7f50586540067d5058654006df3058654006dd3058654006f71058654006f51058654014fe76d8d5401d7e75d8d54216de63d8d542175e53d8d5404cfd75d8d5404c7d75d8d5401cfd74d8d547667e54d8d547667c54d8d542167e53d8d54216de53d8d542165e53d8d542167c53d8d54216de43d8d54004fe72d8d54004fd72d8d541fe7c52d8d54024fe71d8d54004fd71d8d541fe7f51d8d54216dc31d8d54004ff70d8d5400cfe70d8d54004fd70d8d5400cfc70d8d541fe7f50d8d540067d50d8d54216df30d8d54006dd30d8d54216dc6358d5404cfd75d8954014fe73d8954004fd73d8954014fc73d89541aeee52d89541ae7c52d8954024fe71d8954004fd71d8954004ff70d895400cfe70d8954004fd70d895400cfc70d89541ae7f50d89540067d50d8954006df30d8954006dd30d8954006ee20d8954006ec20d8954006ef6298954006ed621895423e7f751895404cfd75189542667e54189542667c5418954014fe7318954004fd7318954014fc73189540067e53189541667c5318954166ed5218954024fe7118954004fd71189541667f5118954004ff701895400cfe7018954004fd701895400cfc70189541667f50189540067d5018954006df3018954006dd3018954006ee2018954006ec201895404cfd75d8554014fe73d8554004fd73d8554014fc73d8554004fe72d
  | 42 => 0x8000001400000080060000003000401500740000004006002c00c000c00200740090014000002c0000004002000000500000020000003000400c00440000004026000000200000090000001001c0050000003007400b00180030038007001800e01c0000007c011006400800d000f014400b003000000440000000000000000000200010000000001c00c0004012000800a000c000002c007000c00000000000044003000000f000c00a00140000008008001400500a80000008005000001e006c007005000e000000a00400000010001000800100080020008003000000000100010000000004800100f8002001801300dc0060050000001000000400000018009008c000000400a0004014000c011001c00b000400900600000000000000000100100000000000002800a001800a002000500ec007006c00000000020000000000800f0030000000c0180028000002400d000001000040050004009000000f000000100000000004001000801a004c0040004006001000c005400500000220040007000800100240010004017001801300480000008006000c0000040000001401200080040010000000c00200ac0000004010003001c00080020024003001c042001800600040040008001007400000100000028004000001a0058001000c0020008006001000500100210014002000c00000280010000002000400100000210068006000400400000000018000000c0080000011000801a00000050000007000c01a002000300000070074000000c004000c00100bc003001002600000000018001002800101a0002001c01700000050048008001000400ec00100040200020003003000200000020064016000000200580110020026001400100480010000001006400a00040010014021005000700100040000000000803600d400600500010000003002c0040000000000401b003800600240050000013005800500080050034002000000800100070000000000c0140030004000c00c00140260010011001000200000070004038005c008000000a004c014000000500c4007001c00e002800500040080014000000800500000050004042000001300100270000000001c000000002700000010004001000000d003000e001000100000000000002000002000140010018004000400b00380010000005002c0040000002000400a000c005009c002000000400100020008003000000a000c0000000000005c007002000e0000000007c0020000003001000800240010000018000000100d401900800020004007000000700000030010002000400600080190000001002c008002400400080030000004000c00b0004002000002b0008008000400000240010004016000000000180030094003003400100000070008002000401604cfe7458e54
  | 43 => 0x9000c01301800000000006000c0120000023002c00b000800000040200000002000400f003400400080040018001001800c0048000000400b0004007003402800040650058002003400c005000200080020004001002000d001c0060008015000000b000401d0000009001400000200020004006001402b000000b000000000640000098006000406b000001b0030041009c0020000001001c00300000020000007004801d00580040000004000c0030010019002400000000140000000003800100140000018005004c008000801f001000100080000004000000000c0014000003c0040078007000000c0000001001400200080040000009000c00300280050004007004c001000c002002c002000c00e00ac001000400000000070000001013000b00d00010020000000002100240050000006002c013000800e0004025000401300100000010002000400c000000000080100034006003c0000000001000800a001c00700000000054001003000600500010010008009c022002c00f0010002000800000000010024002000c01b003c002000400a0014013000001c00d000b00400000028006002c0060004007000c004000c000000002000100040008000000c0030020000003000000200060000000000c00d0058006001000100980040008001001c010000c047001000000000010044019004c00b001002c0020007010801c000400000000050000001002c000005c0080024000000001600080180008000001c00100400170010001000400e000801b000002f0000005000800400040010034023004800f003400800000080018004000000000240280004006000400e0034018008000e0028005000000200440050000000000000400140140008002000000100080070000045000400b00080030044025000004500500070010053001c000000800000300000000000002801100140010000004000c002000c0020000009000400500480000088001000405c000c017000c00d0010018001c0030010013001801a0000001001800100080030000015005c001001400200dc0000008000000c000000800000000100028003002400f00000010018003000401000080010004000000c08d0078012000000000080020000000005400000040000014002001000c00080100010003000c00100580100044096003400d0018009009c0020000004000c001001c00000200010000000002001f0010006000800300000000014009006c00600500010004019000c00d00100020028007001c01600200050004000001800100040010028012004c00300b8001004c0000034006000000b000000b00040060020002006c0090008011001c00d000400000080380008013000c00600080000014011000400500140000004000000800f000400100940000
  | 44 => 0x4000000000900100050020000002000000000010008003005800200300120004000002800a000000300000010000000000001b000400400400010014016002400100140020038000004003b0018004001400b00300140000003002c00400ac004000401500180050024000000c01a007000000400060008009002000200bc002001c0010068000007c01f00100590034000001c0180000001000001500900180000012003400d009c00c00140000020000001000100ac00800f0006002c001001800200100060004005000000300700050034001001c003002400800080020084009003c01c000800a000000600000000008000001400d000c005000400d000c014000c00100180030048002002000300240000004001000800700000000000004001000d0060004001c004000c003017c00100080000034014001401400080110000003000400300000280034000000802a003c00300200000018005001800300240000004002000000d0000001001001600000080034002000000b00ac0040000004003000000c40000008005000800200040030004001000c005000000a0004000002800e003801b0004001003400c0000003000003800340050024009000c005005c003002800200f00240140005001400a002401d0020001000c00900b40030010000000000b00180020008002003000b0000015000001000000060090001001400400140000090000000400800040040020005000003e000800300380000004001000800000000140000010003000100100020018033000800100b8016000401a000c000002400c00040070000009000400a003400e000400f00740000000015000000a007400000100000004000002000100000020004000000c002000000a005c0000004089000c006001000f00240020004002000000d0014000001c0030004000007801c000800500240060008007003800c000000200240010040000005c00e007000f00000000028005000c0050000000003c0050000000001c01300000020074000000000c003401300040080000000004800600140000008012004000c0000028002000100040010004000000000f00080020010026000001b000c0260008004000400500240000004001002800400140000034003000c0430010002000c000000c003011c00a001000100140020028005004400300540040000000000400100040090004001003402d0054001000400b004c000006000c0000000002400100080030010008000c04d000000b0000017003400200540060020004000800100180130018004000400100a800200440000018018003800100140110004000000c001000400500080060044000000c001001000f000000a0004009000c00100080000000015003c002000c006002c001000000e00b0003003c
  | 45 => 0xc00e0000016000400600840000150003001c002000002b00700010000003000000400080010008039000400e00000000010011000000c00200170028028001400a000000000040000004001000801e00000000000001003400a0140003000800f002c010000000f000800b0000007000c00000240000000003002c03900440080004009008c00b009000d0018000000804200400060014009000800b01d00030028000001802100000020088015013c01100040cd0010000002c0040010006001c01400100000020000000000000500000088002003c00c0064006000000801480010000000000800100000080060002000c00f001002b00000030000004005400100000030008000001c00b000c00000040010010005001c02800e00070018005004800d0000000000801f000002a004c00900000000018003003c0150090003001c00100280020000000000400300000090024015002c00c000800c00000070000007005c00100240020000002000c0120000000006000300000000014002000c011000402c0024001003000000080030008005008c03d00600010028006000000000280000000004001803500d0001001800600b4000000800000080000000001000000a005400a00040000044000001800a00040000068026000000e00000000000002001000b00000080014000004800600040010014003001c011000c0220000007000c0000118000004400000040040000000001002000b00230054009000c004000000000540070000010000c00d000c052000800800b000f000c02600240020000000000000600280000030001001c00a000c0070110009000c0560000009007c0010024014000c0150004042000400300380000004006000000600ec03700000000038001000c000004c00f001c00300240000058004005801300080040008000000c000004401600180180000006005000f0014002000400b004c00500d001a000c03d001003a00000050008007005c0010000000003c0020000002004c0000020000000c009000c01c008400e000400f00040000018000006000800040020004015004c0080008000003c000000c023003000200400130004001000000e00080030000001007c046000c000001400a000400a00b000700440040004014015c000000000500000000014010003400200a4000005000d0000000001c00400f400e006800000200000018000000c004001000100e4004000c0010000002002000300000020024066004400a0000000000003d0030007007400c0000004000400500140000004001000800900080000008007005c000000002a000c0030000006001000c0018001003c017002000a0000000000000b003801f002800b0084008000001100580310000023000400c0014000000400300000240000001
  | 46 => 0xc45089682308112000095e07a2b1e91b800043c8c3a5ef00009202718acba7526768e44d871a84910a424971289a1ba94e24f28000d95a572000000051c0000b739ef600000000af80000003126c75120836d839a2af8000081357eb59816008b002e66087460002cfa000000000002104349ff6819ab7c000017ec7690542689c4e496856e682348e4cd36f47901fb24039bc89a511dc7ff118600009248c71a468458000cee219c6739e72baf025a61489d6b7ba4a0707000001da4c67140c80b8b000092b1ad40b2248c45a96a805e34accbc27601572f0eddfb118d4b868c8fa08f465211ae0001b503c89ef2c83a7d2b22839cc59b3f838b8aec00028e8b7c02640ce13dc94e296aab3a7566712e8213c07845229c704bc1d103282b2461680000001b2cad3800000018e6c34000072b07ea00021d48ec990640aa11e000001caca188ac73800082d80006ce89fa443b5bc0000e2a0003600bab80000002c26b76231a4002f021c5b6ee000202aa5586eca11b5b200029545f1a22a000012c94428c289a0a9abd685d835303e6b14084a00e062290b84be5e31be81a7b1fe6e50000025000000033280002dfe000000001a23d24c81efeae1a26e000000070e00847d68228000000000028da0000000cde936cbb1b43e00000009449256142896cd4426fac46b62654637b600028b28cc320800031aa40980744b11008b3faed21e60b280cba1ee0b6080000000a8714a626beb152c71ca042d2f9cba2bf2b3200000000001b848c080000002d2c668945093e8dac91d01de9deb20c95687e01a5344400028160000de22d20c7a73e9c2e79d0f643358c28959106edff37a6b0bac0a0000000b9a07ba7c8000000fac462650000da7b2cabc2000000000b60001bbe00000000002fe4524aae0df0183a00002560003110bcb846c0ce9f0c9f08de0350b568442a0bcda999165c89dfe0d8b04c0002f40000000051a36c2477987a0002aba00000004eb8e529ca8bea2052dbaa0fb78a0a49498c52aad2a932c9a3d0116c19086d26ec000016fa94ca48049034a9a0c56494ee0a092f6d80a60259627a83ac1c1eabb33600ac1ec4bfc83688a31f64bfd98803d4370ed2a0a46a980000a33854400006006b7354a5a336fc25bb158a151f5e0002f3ad73259a0001882daf012a5f8018484524406ad8682891166e20b2bf66a480000000e4c0003662c2a0ab8456af3417380001a6000002a8000216a87044c1d8000000009a3145a3e20702ae9800085d8000883ace05da80001db000070e80004251d44d40b3c69a58000000000b000802c0038005000c00100040010000022000c001002801e000000200240060004000000c01d00080010010012000c0050004056000c00b0000031000000e000c0070000002002c000000800c0078005000403b00b
  | 47 => 0x3a3161168eb4dc78d501ab8acaa86865467eae6210837e0b0720225001e2e554827c4dc252eddb20ec36697e604c045e90e80fe21e1270c5484d6d209a1653220402e0b046a7b02fe781372438590448aca57e3600eb6c48817cd36035e9a933d80f52dd6738000009e1aee3c78cfe00035c6bd72ed46221e7c6041b06cea8e8c4d429be8612030cb31acc3660ab4bd1995c4ed85c68ee34fc04f07eca0c0000000000000003228eb353c4fc918c0000f5e04ba04ed518000c00b19085f0676d26a9108988000000098a59819b06f6891225f000042c2a0ac0e0000cdc8000051852e96535a68812802c8db4044b4acfcd13a60a0000000da187f6b7500005e98c3000026107a2071eaa0a9923c98276cdbb3202a836589581afe5b3285a4c980eeb78b73e2018fa03228000c1a20cc84f8000c721ee025a848c9dc1374b0a1fb48ef109a0fcb1d0df4b40a5f88998cf7b508cf4a7a60000980775008a7f518b84b31b96a9580001bc8002be2800075306d86930000642b238dfb0e0c000000017c19a4be9b0803db153a3880d925c38c3e590b456db92842b9e8a2e768b7021b6b072977063083110f0aaab780c938512abf295aac6971027422e21f10584def33cec269670af236b0dbf8d86d272c5e79623109138da8bae079406893106e01212d0e20640c4a78cd70a0e69708b7e7f125043f72e084f32fc8be61b6256b067c9bc000027b106803698d8aef8a985379c242e52dc671e82a650086c259e27d08b306807e29e781468954187ab8400014c4a730db2000000037d800038080164ca80001d9014a49780000001a6e000309e87f052a1322ecebc7a62836c1e9860c98762bd967cabb80005be8000c68ab14483a8e09a6942290113ec2023272396a52a1fc2606b66131a3778000dbe353e5743176ab50bb00e408da38028802fd8ecc9bf29e2b920aac3a02c54b0f33ea98e33ac7db24e869f958e8e7209ed680f7ada11b48d62b3be80b80009f91b60bf700000b810a60188000297aa089e436f6383a0c6000000076429e8aa6b31a00037d0140aa9215935009c3902033a9ad245f0d0e3e59a501a4a97ea4b940623bb46e4af8000078284800017021dd921cde7000000024947110242000122e1f01e2cda392240cb0c10000000000023beb29ab107d38d88c122e54db2111263daa0c5348824a4d1b5ca340eeacbf19de7421e025fd27967ffa6582112d0238e97ecc972c3ed9304e048d80005e88b92aac10ded82a57a23c3268c6a08c6000289c4b22bee00004580001cf09e22becb4118a0000095c0000a22733af903739df86698476aad1500cf9000ec0a2126a93ad2ac8000005f90000c208932bcdb6e24559ac24d91a420000000767a8185e4aa6265b09da9ebafe6251b4b09fe0f866810418b66a77e7cd0c0edc437acd38015
  | 48 => 0x6e58190ced4319dc5bd1a3ad3b837ed6b807c86b0000254293a3150f7800012ec84400000000ef878eac6a00000000001aaab573620ba537e40000896bc43494db4818097e24ba10d875481100000000000783000091580000002f721be37a429d138409caa10010a67078f0848963ad4c3c90000000112cd59b62c111962c8d180000001db4c191e129d1088a27d858ab6a84c64e90d785798744a00325e073165470f8d964c50000ddc0e9aa02a54208522da8650e62000294e0002d84c01800000000009759cf61daa2e835d1c267d980cacc196640002ddc3a0b2b8a8c875ad9b813470680000000e3200000005268ed8759800000000007170000414922cd723414542a41646f2e84d9a8000c8a328c00018920001eac69ca0ee153b66434c8000000047e9d425e670d041659b30acdf0814e5272b782dd93a8b37a4264c593d28edad1859a2b3a2eb8c3884d0000000310ade40000148266800008d46ee17660ef039200013901732d00333147e000000000003482fc80000000ca241ca87c50ba59860f837492a2f5286a80005bc016694d23988068c1cc07a5fc519a3e211724fe80f0b7cc24a206c1691280b5337031724544c3b2c2938ad7ad16a824daab4727030f9a126964644726da3ae084221e90141cf11766a62168ae69caeb8886cc24302a2dc12c660001b2410a1c9000010b84fe1038bcf8d707f3b0dec45a86490b33dcde503ec81323c22b11b1e245ad529d931463559f2c2b8079a4682a6a987151c18e155c3a81a364f5143e769af7a3f992ce628aa54b582264b06a1b264331d20c40b309128bda3049e3611ab488494b1a4d0312204b9aa5019a22eaca02c582610ae20e3299a757a422218156c9c1a91649518ae5188f74d3022a400003ee9c50000c77b7cacd79a449f8112e89f3084cb819309c488e627c0daecd42f6a3f2a41c49e17429790dfe427261e22d9ba28d9a8367cb81423360406000231e0479ebac88a87657099cccf31cf411528846dab0560002d823f236ca667afc0b85a7b6ae480006ea1a1200000001bd81ea00000000001da061a9c740002640492a8b63a3984e2b529821d080005670000521a6f209811643f88f36ca6000000027e200022a81bd2d0870381ba77d8c5280200002500d5e4d78bba73e0c04b3726a8c40ad4a4352a0e46888a84d51db63dc114cb6195da0000750127000037301f89b016eaac1378e00016005bb18629d690580001d38000127a6762fee8382e4c3ac9158ce8b11e5a68c8c00020740003322ae0913802409901f2a8689ec2f0a000244800033d684b00966d62b6acf816be27bae98348acb68b10000d3e067e5e58b9cc2b8000333abfe89692f885eaf664e22ce803a10f43f788fa55587925c9267407923da2a43356a45072206b14108062a88c3a080c83e944258
  | 49 => 0x9c0b4233107b857f30a2ca800007f7a7323f12120a049fa068780000000000d499148c34b3680001bd4b2c8dee6d0ab486baa9ca36e23bac5ea2aaad830d83b225305f72a8a34fa9749e811245e007626ca825467a250e56c9a1cd60973e98cadde9c90bb487d8cba16800000000da20000000a8a0748994131e7c7ad100001ed8000020200031f0a7f00006a221404fa8926000358e1c48b52c32b71a3ee156ad75013a49a154684f179c3941a667ad258c9aba978b2c21e2c3fb198b90111a82c88840d5a2c8c2f31f8c3d073e1fc835439f2dc2cbb15f05e819ca000000077100000b58a844eeaafa78c94ea10c11b481413320f1894260303a011e29002752a986130efa021a0f800033b20001ccadcc894a040b0fc63b262cd6aa7203c3a2aebd42da854ca6b4000000002c8f3a0bcb38c0000000529326e0db96e63c0aa767591bdedfca50077cabaa14f14e0a229426b86ab2284e20a8bf5b02c4a113d0625975a6ac08c810e10600a22cc66278000858316200000009480000736a5b49052e7e7be28f465d0acc1b1800000008ce9c200003b09ad61302fded77203a4fd29ba0589fa2973ae96063065eabdaf587d291b0c33858c5720edc4bb9de4bb9a2185922780917000069280000001e0ab8488106c82c003598f2e297060a926b6a4c9d0000b89a046da81ffa6dc008c57711d600004d803cb0b65acb26223aad7c8b49decb67329e00034122270000149800000009c28d489aec75b25a00028522ef89bc4d598fe4702a260000b989132b8037680009b38d4ed4c1e840d388ba66ab542a1c90249f106b600012069929430a68a9c29e70000d258ff86450000000000000000008fc0000bef0432037a76e22bab3e83f08666800608a7e9f504b8801816e834a97a18b45d91f48cd122205591c6e187345c599a00268689304ce192200022ca055a70a9d2811c916ab9600028fa5cea8fca92a0c052c23882e38000a99b62256b9ca0b1d95f6c128a3c68087d0086b25853b16e0b6822a20000492c3c9d96561ac6e0001f5c00006880000bf80000bcab6205e00000fd033691a818f9526bd280006b69f1a000005eb87000020c17f2000000013b850888d800000000004aa8000525a71aa87a798675a6426bc99ea0000c4c01b32022d02f8289d9714a9b8000dc71b64d97125044609c64bc94d66cda8ba1a124329fd18080031c1011d25f276c80004baafbea63872e22201ec1c83596b4c8b8c14b145c868854238c0000c5f07ae0d029ee23c8a9c7ebae5c24b0000404a666000159ad18800032b000011bb1b03b98506000305e2140a8c039b13c3ffa3244dc87fc0002f8c9fe8000ddb800091fae285e68000bfa80000001366000079c83921f00000fb033d2f9e94e9b022f91e863d2839835f22381e92a0000000006081d780002b
  | 50 => 0x33a9f18000c909a82311290cbfe0b0c04e0df4954317e6e69b921040d4a53f0c022e00000cb6359c57b350e9daaa021be981c75f0000ca20000b2a152000006167c100001ef89e481f01941b5ae0294f0382ce000009aa8b688960000000000056eb42e00029bc783800000000003cf8a3422c157ed54000000024660000000000240c00025663588000824800009c069a5b780006e8165a00016d461408741c12e66d572b7a9c8a55878e0ee2b281f0a95a890a76480000001a5e9958d1c00012a000000001ac325238a302e0d90b2032f047a000114e000000065baf3017facf45d7251e8cf8f5cb948a6291c28a0cf6983c46cae5835b268888323fec0683ce26f96286542192000246c76c0000acd1814a5084cc05b32100001e52931000038b23626b8967e1b2297ab7d129c12993aac2a80007910fd233716940bdaf160002380000160278897f60000a6058bb69a953930c0002ac4c538000af7000000000006a31e180002f427a995768e9349e55e2bb238d00e040305a23ec81b81f48000525026282ba59ec1f227800007146881b9000036a292a8c2c45fa21230ba85c00010aa0fa80203938244d93b6da0000000d23209c0001d62530050c3fb0000027a0d83a9926a837a516770a39000000009ed3452000305200034809d6152260a1d8ca719aa085d1b78330b54c32e20366218ce256a9898436143c81aaa180000cca2e4050e31caba426a934a00032d628300009ba0000d9d0000cd9a300000238e06f98be0003096dde356ac2f9428000337c894800021180000000000d0a0000288297684c8d5872a00000001c5600035e400031f6b321c8a99e1fdccc626d4a3da27e7aa376ad838c405439d06af82b7080128bed3d0c361678f9025113c200d822642233f25c1028aac9b24804814140002434a0badc8dd212e023412da0dc1962cf512fa765231819b20feabc205821731441982a8ca24b22c6b62ceec47286a4760222639000072aaa90b65b032389b07e2950b3a890a8a451d1b3032917324d32eba814ac6c74626eaaf401f2a6a2f00459ad3073534f6939865a22019f42e138004f00d3a00000000000000625000000011f80002586cccb5c064bb41cc100c20da514520000000cd08840053299400028940ca8658aafb78892da9a47bd01240111d1ad32b4aa4a4905684c3286d3783ae296284c183a608c8c24606671f0201c21c2319884e7e38a9686d0280baa2738b82926ed37026e16f00006c8853e00009048a48000636861000004da83aadecb8122ce184b1b40000366cbbb1c23a4950c36a9782000339a2d985a82080c48840928eb01000020a046896e90e64728708a1e2618a8db4740000d94464ae0e1fd2fce32d9c580001778c8f94d4644a280b968000dd731640002082aac9eaa9d8871a76eafa0006af68c
  | 51 => 0xdc82e400019b694a10a2000000000021c40000000000309c72680c0c3c227203f00000000000064a4027b192b6809048a3eaa9feb28a5080c9a68072f2d78360b2961261e1ac312a3e63d36dc2e5b6c08e300e2bff8000192000000000000002c1ea8d07380000000235ac38d8baa5eba7116000000000000c7cce7b6f00751cfe95700b40000c429a706e80000c8e0002ef0c638fda00033a000001ae63f32c88ed1ed00c52b1ca35a156401370c3e7000068f157aa28b56c4b094b4b1e958864f04c4b4d00002bf97ea7e580580bb0066440170805d1cee1078c629aeb2c642400008e7953493b94b868c81280edad4ea8c16c204ca3cc8520f3403b1fea90fa9f4cb4838832219543f080001f6907c8070858c1a860c204a19e7e20bb800024cc623800046b3130da2000062daa4656f1c6a30a8320c8f0000b2b15ce88e8d16770000056423848d81f32d008c7e70299920002e74dd4877400000000002f6c6a680007c600001140bb2a620000cfd000000000002a5356079900009f2295800000001d9800000031ec76a9a9e64900006af140a21b919cce42ab897e8000d4480e4a2a2efe981019c90e24840001478000357aba980006b82d1c0000f300003490a4480000001b0a000210442580000000000391b5f00d423e088cb4680000000a4886de0002b0843f930474100006340b0ed8180003ff0f527690d64329b16c0002d92af524b20000e90dc52bfcc30800000036be0002a7c0be2b460003610c0d24900000a86c9a9dd864e9a101809af86e92998a2621fe4f635e2d2eaca44c637340ec928c6ab9634221aa94aed37182b680b08309d8291e881ac0f3036a241ac4a4f8000b51a08e842191c2c2a6d60003010afa8000dba93484f816ae2d6228260e2fd29b4a32a5f5a22426b0212999260c0429dce15c98eaaa3a23e091a79e90432daa7a928aa84809250cb74cdd8acdaad119ee7f5963e77e93825eb0422c7f1fa6518124c96c07a2512344c1131b7a5eaa838000171631e2b5ebfa285630d16dc00000006cd17262ad882a2d3800029287fa000131205200004118c24d3a29dc7fd272e5d62e4eccb0fd889eaa2c0c9173cb4e0894b44ab9c4572cf6dc82e34000350a00024f664c80001a8b4187da978e803809c7230f8001b8000b8f193e19ca9b0100a596a4b00bc3752be23181e1401f8000cfb282200017b63d5207a0003346209ac4e64a260e97281980002400b1e321c88a33a6bd922145bf8f323698e14d8f2f1a8f51516bc72ab678d174e577883a441ae14bf8800013b2260b6932cea0a00002712ce2c65237e000033edfb9ace2f40732558000009015a8a4726ec3d33254c72820696000005df800057ba0a40000e12d2f168a5f6a0dc3ca9b283ab1444bce0e66496091c3fcb7a0d0c099c547a54c93b004edae2
  | 52 => 0xb3386d7844e0000466d7f9ae81aaa0546f08c6883cb69c00006d00003642000000000025a600019a037f1b6c00009780001fc60000000db132dc88b1e462d19f1c1342f9a58ab612b91b67a3fd21c60282a862f1216e000256e00030e64a782485d102080000000a81b33c0000000b7800000000000c3900000002eee70517540a6237a364136e000248862109ca0000000000378279719bcd9791e67c40000000265e3b1194c91f10f819aa1a0d8a000000000000001946dcd868a00036de9b129360002cd0d5d9b5278a8da4761023c55c1deed4a158287416b62d3103ac5c27688322a1c5d2072a1e195542588bde8d11ce8b30292600019b80f028b8ca40ba26d69e0086b8182b5d20d2585a5784b1a6c80c11d9a8f70f480001edc8daa25080f800083380006fb00000002a2069f0000c5d0072940b01c2bd1c68ac31dc87872e3670c30c80000000454a38200000000f7b61ec581a227f32850a372cd4d00021c29aa06c48e9f221c912b80000a1a223837a000200c2941434552220ad5c816e67f95d4485aaf4bcab2fab8eb1849bf8a525ef96c4a393260cd391c60b1811039f99b20000000b4808680003730437121e1562e70c63361a68bb6547cf16989291b8a7d32fae406b57813cb1369a1831653c81e2c7730e211cb3fcb8408e0696844206db7c41ea1c16536875cc9d9c0891a867048c05ee7ba03ba189b41a70081267f4b478d678a3063280000a69198742a5700000bd6949034c574800093c0a3a7930000655aa383461fc2c9280002268000b493264dab031c86399f0cb7944a634992a31d1184000204896480007d0296c3d6056690da8d453ea9f8a920598652952e438230cddf33843710c080000a020001978b3a8cf876b2a80d650c5e97881088418000d8d8e94d34000083d800099bb10e0f8b5804de18bab652bc089292d6419155ab7a91e471f015e4803150402b2d0de49d4a9c9a7ca7198dc86b21640d38abc40c2abba96802b4b2d1ca205ab7d83d8aa64dc48d5a0001086a6e00002db13b8a79269eafe9aec3208000346a338b0220721ed9cbe43585aabe5b0b41940000000000077680003241f988402728000228e46aad62a9730d4b33a4441791b10c1e140e4330ac8cc00e4a23134222c0953e55000000f905da00000005df00003258000341800068e22e02d2821e4911e208c1a62a000169600026f83a5b67839d2de63ed875e0c30e98cd5123c7271752afc321418c804672e250cc02aae404d9ef0671a7fedd3acccb2fa9447e18b7a84ab7283869290244074c1819f30061a36479eac528548fae68a0fea503346cb8e28e6cfea84e9080756a231a940efa48e0770b1e586866428935321f7acaa53c04243b027dc04100007cfa84024ab232c1080d03760f82936167433230badcbafa800a1e6245e97a4
  | 53 => 0x2388b7f00680df000022ba724a7940000462000286e00004b400027cc000148e0f69e9a96f0000a0505b0bc60000d72b3168a28514d75aadabbd800000014e47541b4e0001336a2d0aae6c9aeacbc88a7623f265273c8e36df52c30685000069d835c000144e00006f00002d803fea996a5280007fa20203f1a4a27f8220893280004d8a6a2b5402a898900003a18d2c63389e233bae72c5200006158000d642b54b638cde2b09b880002320829a6820f5912ac06333e7d58f8ebb80000c3eb7723a8a210ac5a51a00000007caa3a8314162614dac120002e44588b34800010c4000074eba0000015d1a8e00011be00031c60002d44082a10aa220f8c47da1b069206ca46000000b6b1e808f8f04a2b859c9e180000000f14a5792d0a2f19c885992a4bdf8000d8f9e4e7b0a676643a1a6000302ad6c0ebc00035221640000b729972609afa4caa9fb815b0cb00d82f767ec327e789232cadd00000c00a685561e6a0d4b012dfd9f9e153351490a93b496b0604d2d1146b0500009b289b000015082fa00000002308d05b67610b14fe9953470c6016447741544d3c93f6a3ba96e91e0a665f0a4587a700f86f2918e01225a26601bb4b1811a400032d41cc090000000004669d6ad4629c40ac922600019d48669032d5c000000011a60000dc66e600cc00026ee2910000bec800016d236e82113a0207b33a0cd308acff8f6659705c0000208c6fbb36493aa6008ae235085300d2004b5c49ac90f60001c18da48e8400000002f322f41ef000058780000000ddc215141ca6a9d7a0000000d49000000000004ce98f00000000ad49df40e0166a68c1aa8b12917816e0b10b34b4e4106abd64aa103665aae50904a3aac5c8b18b4988346b2a0068078f9288f147a3dca20241d22bc9279eeaa89059a7e0b2e6b15a1d81bfb1a028284486ab0e608fe13a250d9b0e773255e90f26c61dfafdad5527d4cfb820c1e32acc27d275e5f39984734932409fb022db3a4d2ce226147ed8a72cf2ae76c919cd0c9598c26e1ac0ca0b329a7981650b5a2dd2041b7860261a0642123ee1df1d324b2a18a78c0b9e1cd8cc6000097685c97e86420628c93163674b18a8cae8000781906a83533e205c80003aeab562c10530b9e25dec298ba429b8bf480b133c73616f6960953c6ce093a4742dbc000035a5f492340000000c3703fc4da86d40d1800023880001af1800bec018a6bd07b049016f200000000000aaa0002ad6000316a000000000023fc0000edac8bb2940000000ca49f540318e580e183ac997249271b30ea387a35abba90e48a5ae24c33238600004b600037da5419e6cb4883c2d47882ea6735e661d12d843b0ca8dd90000665186cd4dafca7479be44e7a03439a800017e80002be30b00000c58b00b070d9692fe5688dc0c420000c6b0e420000540815
  | 54 => 0x9315c420a9b465f1ae4c86a04ac3bb302b20170c3bb8aee00ea070941aa2e25c28aa825971abafac86ca71f7412121fa12eaed05c18d266df990497b85e89f5907a9e881ee17d80f49ac0a109740686d7d01902a22db61eb083ccd28d30ad6923268b36d66c305de86f2d14ddea274b5235b667f10702a394a280ca8cc02883767f62dbedc9a6344e9b4926eb171e0ab2150a9137ba2f23716070a68e6a01ce410386e2020b75a878000000010e200026d803209d80001c04b2f2b90ae800000000988000198a2cf800000000007e12874ab18d6eb4191c45aa9d729fb9812a41937ca631f7adc1a54400037f41e20b6060c07109a609bab5f8000c8ab5627b92caebbe141e7d89ce2b1c30ecd5209183d11c323eb2f5632105762dcb6ae2562d3c74f0000c3180000001598c6200000000e9ec6585b20e3800000000d40ff88c08d5af7867e370851da4c87f89bf609b0000d7e0000984855614608723db8cf077ab45e4e48cfcd6b24b87a0352c5e61d4000f29e6db9a67c194af2438900007318d9e000043e6c68ef6bb69eb612209f21e00a3e4a093e200011e210a80008662a6cce51bd200010067da000079a2450df1800071e15b4000313aadb288e7dd97b25f78404c153668000230e61016ce0658000ce388ca9af3094dac864098f000009d3310000000063200004782012dc2a9da40a08a2b01898e84709926d03614ca92a7e64611f40002f843a28000b6880009fc35ba57a186893d207ec84965608803e0825127e3d800006cf05a4a42acba8f20d00d7a00006e38000000000000000000f20d020938e5416b27be515a34e00000000bf3634000300420398586e79b1c15c2946d2d83b400016625ae00000002e0cb628f2c0c205e600005dc0000000657b6705e20ae6ad030867bb1d2ad538000816841218b21caba6a4ae47e80321fa0000382097ac0c01fe6271f7ec8623a68cd273aa4c935aaaa0000000071c5a1abac80a00000000000d81341e9fa1944662326c817222e0c09d2202e2e3090399768218000bff11eab5785c88afad3ed860c562eb1abe8a180000000000dad000600000000001dd2000000000005c2d3e800000000002a9215ad0d075852a9990000089e0002f328e5ab427519e4a5dc2b58721130aaf4ac842c69b722cb998c1208e7a1d2a4a60a1828e2aeb07ad160000cb000005a7000064d22ee0001b9c0db2b8e75b80000000ee4269800000000002d8b3268fd8088d038000191a4f271224d4000000016092f400000002f72f6e0000c98bc9b27c0000c22cbdad3a0f7078e0ea277200021da0000000000063600000003060d480000e9cdb8000000025482d58b380001504c13b282b4b80008f6264800000000002f8e5ff8f38000195aa18b75e00026acb7e226aa54b756d9fac9c3030000000215c450171
  | 55 => 0x53a00006962e60af7a87e47a10980000ea4c4c9cd60000000cde02cc000000026d351c00000008fcb47a00000000050000ab22200d760726a010a78bfc293c7b380006a433babe481c0cf023044e31e90ca998e05730890d291b00372931c971b5ead150a7c13917a87e00a4e36285601b3927c40b868e0e7ac249fb143841233623c69108ac2b4f09de22de5f401c45fe8a8247f82e2103156e0099bcebf10000cbf9c2c0000abc60aac5c562894c12ba5d857a862ec6e189a54d8000171218cd8c8dfaa1e9e5627035d06fe93282c02f7040c00003ab80000000a28b0635de69d04acc380000d738000b90b4641748000000000033da368ca11f000000000132942a5c801ce0e501160000b8a1601d8864e12bc1f0800076288ec39c000034b8d2800030b24061fd000018b00002db80000a400002aac743a8f8a322cca0b4a8ca075af282d68000000023032d1e3e72da21cbc1a29a7a882aed3b177ac89a7d84e3a4304609bae49d8000a94b64000003fa23e13da0000000aba88d244891f27b2ab8a57f90a40000000d54800055383f62b619c29fd8960bf4214682e1266432281c04314bc9732372476800058ea1620000bbcc28004c80282a0a4a95a4000000015f000054a82eabcb00006a8b0d66783308d668f7ea4e0778326b64a0000000a5cae00be515c0d3322981099288ab7922a21a9274dea2c3275086baccc0996b359b8c15aa3ca5c72b0e9d3a36c993b09058cb060dd9a61624200000001a8630029a6000009a3dd8000d7eabb8db42f3c1180d207261d488a70328584ab2a8fe81c84ac25d476199f207d8adc9cb146ece192fc205afb83e1286012c33965202a40347800050e88640002076097099ea812eb060580000b9a8b04f2002a8591d76af307703b1800045523282f88a800a590b6040374099a8804d28000018eb2ac31c29041f61fca17a9ca60002ec47d180005a90fe8d4816e80000fce00000007e6a73e4628ef00000000000290231b14721028b44509238a7aca12235ab6163f0000074fb1140fe00008b40000a3b3784df980001ed0e0a000234000005d05309ecc65e86a6000275ca2585fc0002b12c7628f2b31000075b000087e1b045a880003411a7a00000001bf3304ad9000000013e611022d40c625ec1c396d200000c200008cc43bb37685780000fa0644000000012a0000ae88000b058de87e320da7de1842247ab3c03c00000000000000259017500004a984ce000000000011d400017cc000030ea360d384989e485e7b79a240a776000266218500000000414b79190096f800040400004e1a4ce3249c2a00000004991cde1488b3468983b874510dab1216d60000ed62a28000695840000000009ad8b701f19de00020efc1e580009db364887b1872c493088a6814cec1412b4374a0ca8be37b293
  | 56 => 0x10000c5686c0d9ca2dc87480006d1353a00915be8b0ab4cd9f2d1666b2e7c00003aa07980008dc00000001996000013e00016d800008a6b6c80008bb0000a0c80001f3b74a0001d9c2ff91743c2982c14d1a240000000092b7b400035642d50000d10303a000000015e806a2fb000000009e6dec0000ba28000000000002380006cc855a6f60ba82178000445888252b168eba82a9e9c0846403a9e2646d987e8f01e7000005280000000c941d56428138ab0817903ea0a0049c82385cd120cd630000bb600cedba10667e480009a10d7e5850000a6b00008b59f24a31a78a79d816440880007fc9c420000000a570000b18800052f82fa000000028b09fc15a28583430fbaa888000420010e000000083a2d0a0000000000161c0000000000000080580000000000000086c0b3abb65880000cef000000031402a8a4c00cf074034d1ff07eeb2ae158aee44678c0a000000012932b61a400002b19c828f3b18a000000038400000002b02d94359228d9c362c181a48de11ee619a1e88c4870038f000000019aeb03b312000185e682ad6c34d80d87e9315ed4d1d5499b34c219d00ba0001214c1982de2db9e280002782a739b7c6c58c8661b9bdc7b48000d5b8634a859be04d825569b78e5edf31d740100dbe10f2a7021f29b2ad880004fbb638066b2a806a15b841b0a56d0c8170d94a0e241331e2cd48000bd526e07e424467322f740001418263249c73983b06da21c00999c8e84da74cac197c03970aa681e264c0b02928af9011a056a476480910cdad84f8ace30f8d56a9d2000104ac6b8000a27800044430240adac10578164c7fb2c680000000d39800033435a21ff97765119a5242a19a856326220001464d831376cc527aca439246d8e80008bf24982b03406269235c18603ccac801bc3e6163c2da97b44b51794aa700001da12de640b3a46aca06043400000748496dd81d340512e90a9c82c2592a29045cb6904b00a706ff00004e52d6ea5a32b40bd203839caf14deaa0d642384aa63881da85c31b64171b18dcb09a095897ca97ab4503d1abb0c1d2d0cc44adcc311b5d21970c76c858050aa824c2567b3345059f06b92800028cb28aa3aa1824f78af2000370084b9de889380000002c5a000112050b00003af89de27e0d6800026e2000000000016824b92a68a111280a3c2fba795248a6191b5643ea266b2e000000000005891510472206200012dc00009388d63000000000001eacd886a0d8c3b4a0ba27806b474802e839d81f41e81b760001be65a2165e451002c5651fee7a3b6300002ce6c3d8000b4d8000464000032fab7e00000006b1800061c21e6000358400004a06902090cf2000045b85d67a80f087223014482b1680c68000de6351a12caede272341042c800095f31e42378a14a5f099a000328ecf9b178a9080
  | 57 => 0x666af6300c58406e60a337cec9024fc9d187c8901b1ee772800000018c40002e1e000124e5832b3600033b429221904e5aeb40002ba82cb000000026304c20000000021600034c8949b5e000000000000000aa9000000000001f9855281a216a000112600035162f0b142a37a964df59f6e431ac94000000050224f87b018ee8cb8000ad28378000000081badc4000000000000000000d54407221a0002240d892be647c1b6eaf0b2c43bc86960c78f1286908387878250550b4865b18586ab8a83c29b08e47252222ab4199acdf8b2426e15cac61aee8488b77428e1f36d51246421319be9e4b4d2bf513fa52103a4af190b451aa53e5fe014070f310c0b70000c4f859665629b62d798360000000cec115e77886b84f58000a0d1bf20000e06df7a82664997500000000c48005696c800000025f06a580006469cec6c5000048f9c4a00000000000000532800000000007f01dae51b000095d3020000081c000000000000003d6a3760001b460000000b3b1bbaba4800000000000000000000000071502b8474800051518d49b400005db373a43a99f6cc3b7580e981769980de4abe07d60089ad086e06a066d34a60000000000000057e1d0272c00000000000d3f9c9e8a83426a7023321882d90c4b2d543381ddc83c18f2708348a33a0af0afe2e6e4d49e8200008dc0000000000000007ea59c000000094b0000000047c000299e0001cb426c980e0001bb227a19e459d847000018a690a04dc0002c7c5b6800055888e839900007e70a048e49e923c4343615e2c36c09aadc20897384589f38b5600000002e5eb1929d473f31be5da170a06aa31400000000000000718aea424880007af37505b037be03eb42465f8a1e7d827bc0002736b992ffadc88678740358633985f8635a5a4ad70332000245e7e50bc622e0000000048e92fa63e0002690bf315020cc073a6300000b130000bb02eb6000320a7b68c4e8f913469611f7cd9800ae0003558dda1952c4b9a6a8cf2158d2b96e2bed00001ab1d3017b23f400000009c4000076a13f018aa9e000022fa15f80005cb368ab958c6e000210e0000be6392132c2149e4200000006788d760000000cf400006b78000aa8ac2ccba04a2de595128bc92488f79802c0385f20001c8020da5e0d691e16000058800003d200010ac7ca019e0e2854800008fe637a55297d10ca44c903e000000000014a0413a39a000000064801a6b2480007118000d7b892e55d2f603e7a7045ee13302f816046332ff47798bfa9208e88354a4b00000ab0747061a000267ea628ad6618181a45289d20d11a544300892163b484925845237b1a0e7c3805ca741580a54305c77597c460627f2cda875218908ac0000c6400000008d79d2e624000052da6e400000002d70000cea000016517866fe11ccd8a800026d96b46
  | 58 => 0x91cb35c137a05e3da95e22a7994e7d08d088df25882599d28c7ea5140001524abf80002c580003ba0ce4cf0901e111175e01908628ac00000002c9600014f80001a5cd2625feb9b0a167bbac981348706875a4d04aeab500002014172878a6639d981fe2924200a1786ffa6e646e167abf0af0406200009b313bcbb70f286f180003da12ae0002b006fc00002b7a576cf103ca14e137e13e9e5e0001cdcbd7a25c45c064a241b43caba2ecc6ae37429460d4021d97745ab00003b816f81bb9e66c6692181473540ce28000952b52a1f726928fb2b66955070a7c20bc013aa5daa0eace440f32ea8622bae3e99a8a8002fd88bda9f0bf82180743027a5e2aaca2aa2748ada26365399368bb0b2340a723480001736015000013998065a428e20002c3a2908000086000020280000002a5a00025b61959f12a081a9c056109e4970cd2c6780000000000a588bce69b366c8eb80a40000eca0001eb08b91f527571b54a12b7e2ccab7fa18f145e531b74622d1f44000306e4e000006479fe40002d287448e0422c8db46dd0c9e510172a2862c2ad11b1005ec2a2accd8dba09a9a70a778ed4d3a9a78b1d0bf09e11b2e3068000631901600000005828000ae50000ba8a0260002b882c5147c0f420b088d0000553196430f0b9ab56b4c60949ba65d193b00fd21289628dd0cbc9970c2605a6a069c860002cc200028d23fd8bd40001c60c7a800044d05162838f8a5ca0fd424d00005f2000021c094e650a118cc2800000020b400000000001c5a000285e00000005598000199800000017d8796adc06bf28828722a7a9b0a9f600024683c5adfad62241a000030634f36f228718ac70025220002db0cac2bbc24d80000000e78c5b8bd874dac7252300005a100000000000a46b7dc98ba7b20000fbc9f994043959dfc68a9dbc02b155ebd300004cba0d04eca6a02d9232276f823a0000a7ecbe00002469d24b769faa5220ad09c7000088c1398000024c417b2bc52e8b325712bf26fa8eec43a0bb605a3506063800000015840a914d86112fb66f89ac056c1fbedd501fca7caf4815798fa49827160002b985331fc83c3263a822000096aaaae4e6b10400004e877c00002c9877294708be92f3598000182236f37b800000002bab73c06c1bbc9cf017a379a21e4e70bd2670234ccd6a3a2a6b81b25d593c44d010ba2731550b47b5f229322704a8a32644d8290d6d1e1001e00003ef87829c31dde4540000a75934200027da8bfad42d5d16728b1af0c937800032c90be4109c760e582846fd36fa85fa81e4650e18704800061286a8000181e06d37fe0dab7c872cb0080f104b866eab2c5822d56102097e38fa1f47c50e40a5c02cac8195d62d40000316800024514201eaa41e048800037c8000902000000001f0af6b7e8ba337ea312b31e00002f00003
  | 59 => 0x1788ef4c89278ea3f9efa5b228c47b5a1ea5d8378c0551f261a70f4253d8cd4cfc26728ad11fc3c62b30bc8174ac41af88a85339c0002eb2942ac340d08cf2d820b74a501286ceb9aa660b8fccb230b1269832f45949d4e0540afad919ccc4c180a641e0f566f10f94661a53295a08562281ca467987e22a48000d1da29e504953800009feb46a6be1c61242c87854a1b803a24a5aaf261180046a9042eba19a68bbc96bac798a5a40d1b4c0000d12c4a17ae0000000ccb8d0a5b9077a7019a64602a734000011835e93fe00002343bf9f3ac05b57c758334c8f99458a642f9c120000053d2f8624fac825b4270035802585068e689d51dc6c23308ec7d27b8000000062cb55e000095abea80001989cc233e825e1492ecad6f91ba36100000003682cb90bee014a646756aa74147ad4000012048448000d2e2d8c00000003b7ae9eb7413bed121c4c8281fe614409740000000bb5890e8a51f703aa1e08571ad7203d800065a15d83fb8dea8f5a886d12a742da302248e500005a827bad36a2264840d142b49bd0730279aa522336db32d64107000000000006bd800020621be0001730bbd13023f5ab184d71b668f1187c6bc230aa1b2288617225eb5aa2c0ba20ae48b60c9400c2c8ed0aa7aa974a25426087ee9d0318280400c49fa84d408b80000fc33248260ace20f95a04230948281800082fb14cc1b1d52c9ea806b1f80003270b080001bd68b98c06c1884f635c800000025b80002b72d35800033b020e52b829e68610c227729185db8000c9117ba000066ed35001086e80d60b4331cced953039b277c422a68a2821cea2c70ae8b3c0000284adae0001680aa1064e44ead765d31322b69a81014013c6879053a486800017d2144a2987601e40000000170024a21dc00024d66b980007088000bb8a8c0a96137a000374400010fc236216c8a9a6a658e2540d310a2a9bd0c32a598060892169e7b89ee6d2881d0938369644faf7cc670d5c6c22c409ff22f063702bc68f82c4c1601d88229358674aac0cd62cf81ca12941518b88d6a09ce6c481c6763a5a87ef34b2b6792385fbb1567a506e48faaeaa37e32664ff1568c29029497010507eb2efc4a630761cb23c6a420ab22cf0dc2d0801147a288f6c36adf27191104d4e29867a5a1de00037a2c7100009189834000000024f0000c11280e0000000725b6d4000261a130800040b265a95b0000d7681ca2ea96b0afa32e2d55805a7fe0532bd380008432e183670f3cb819e8c2559cc47d61998b5c336c56dafa200009a846216a63df34ce416a71e4eb36a83c822b6c732dfcbb22a3a885907e5370b225939228cd031929148d8eb7da142b1082689910232dfe000065020ac87c8e384009efc25499360df23b060931f29060d100002e325cb94908d286c4b9a91ce000188cc780000
  | 60 => 0xab9b46657d1c404f3a154465b37489b16eed7f00002590c1e000000061e0fa447b23a0da030b8000372a00014d0a9e00002ff2342c6c80000001d7079b9692891934e8a119ec25cb1bc00780000cd8cc054a003419300000000dd69ae347e000044a0000000000237400035ec0000fe4921b3f6dce2774bfb1e7e0000000bc4aabc8f4022ace618f80001c281db9fda9f3b1a61411ec88269aba000000000004fc0d6000099ea1ccb880caa000282a2e192b2794144c52089eadb18000a7617f01af96bcbd102ee155296094d88aa75a2c440002f804cf9bc08491f167af80000aeb30c5c62bce893286669380005e10ba63c70000000000000001524ba11c26be84e200004f45ff1b3e84eac9e0002e2e0002db400035040128000bbb0ecec9e134419eafc60001a341f31f723490b3641008bc13fa0a2d1f1740ab636ec527859287384564c0320452ca766d1a9baa0001b8200000000aa99d0aa989201e7808086d9d263aa97d438734609029a62a8f18483fc2c2200037ae4f91c7e424a3541aca7c000002360000000000344297200002de18a41a900000000fe0c8eb2be1eca14eba395e47a791149f788a4000000000033e830527a42e837768528000937087eae780000000000a60126c7b52bca0000a64a4c31ba8958c26de7ae2a0371d3a951b42c0028000000154a0001db810e95720001fa842b80005b280000000000d0e8000000192c22310764ab18aa02f87d4d7d800032b80000000000afd2080a612de87178000c4d0da0add87e4121b2a210d2c8829ea5f600028ac5659d163059d584478a2683d29c8080218612f33826edb4083c199103c026dcce4870cb3c9eaedb617625bf1960418a1960001ab47b787a69bdb12a52a30c0caca91e1cd16305dca80c55f0c6a1250f4e127adac82a9ea4c7010bcae311685698000000000000000004fa15f244f3644000313826195fac8836ba846a80854500000000fa220c961816b80003513698000000096b80003b42620c0f8898bd88000000129a0000000ab09bcc0000e6e0001eb8529ad0e440996663a1b4ab8f8fb400018bc75f800000024da000000092d18540e1151aaa58b2a1b7273016daefa0f62c90d6e22ac1540d46c55
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8dc87d8d51484018deca392a2908031b19672d05210066631ce5a0a4200c6c655cb4148413958c8b9682908033318d72d05210043fc2aeca0a420387c855d941484011bf06bb2829080a3720d76505210047dc02eca0a42018f8805d941484010fd0dbaa82908031718f75505214a43f43ecaa0a429687c87d9541484018b8e7b2a829080237a1b73505210062fb2ee6a0a4200c5c65dcd414851d1bd0fb1a82909de3721f63505210062fbaec6a0a4200c5c75d8d41484010fd0dbaa62908971718f754c52138c3f43eca98a422587c87d9531484018beebb1a6290803171d7634c52100667b18e498a424fc7676d97214849fccec5b2e429080f1d9d865c85212be6b3b6c790a4202cd67618f214848d3cf0e99642908061f21770594210045fc22e0b2842098bc845c165084011d904b82ca108061f21d50594210063db82a0b28420387e87dd5640848f0fd05baac8108021f60375590210043fc2ae0b20420387c855c164084011d904b82c8108021fa1f505902101c3e43ea0b20420087e8754164084010f90ea82c8108062f21d40590210055641280b204200c5f75cc164085e18b8eb982c81080317dd5305902177e2e3aa60b204203a3c8559254084131db0d394a81091f1bd96729502128c3fc2aecaa0420487c8759554084091790eb22a81080e1fa1f7558c2123c3f416eab18420087d80dd563084018be61baac6108063720f7058c210043fc2ae0b18420387c855c1630840117f08b82c6108262f2117058c2100476412e0b1842048f4815c163084010fd0fa82c61080e1f21f5058c210043f43aa0b18420087c8754163084014d904a82c6108063721d3058c210062fbaa60b1842efc5c754c163084019b6e0982c6109d21fe157654c210243e43acaa9842048dc8758d530841387cc8bae86108030f5d564d0c2104c76c34e5a18420087f855d943084070f90abb286108122f21d6450c210246e43ac6a184247a6c82596520848f8eecab8ca4108d61fe1d64948216e43fc3ac7290424787c8758e52084010ff0eb20a4108021fe1d631482123c3e43ac6290420387e85dda42084010fb0bbb4841080a37a0f76908210046ec1eed2104200c6f76149420848f0ff0abb0841091e1f215761082104d56c12c821042018df8758e320848f8eca5bb2421091f1d14b76484210063ba86ec9084200c7550dd921084019ae61bb24210803354c376484210063bbb6ea9084200c77761d521084019aeedb9a421080335dd8734842100673bb4a4908424bb6687949210848facd0f292421091f59dda524842100733bb4a49084200c67769492108401e8ee72924210803d11ce524842123db3c04a490842eeb6580949210848fccec12924210bb799582524842176fa3984a490842edf453094921084019ceeca92421091ed9e155248421
  | 1 => 0x90c880c690803745c11018d210043fc2aeca9a42008df835d953484050fd0fb2aa69080e37a1f6354d2101c3e42ceda1a420087f855db43484070f90abb686908021f21975d0d212162e31aeba1a420096c825d743484010ff0fb2e86908021f61f65d0d210062f3aec7a1a4200c5d75d8f43484070fd0bbb286908021f6177650d210043fc2aeca1a420387c855d943484011f700bb286908063e2017650d2104c6f43ec6a1a424fa6d82d9652484090ff0eb2ca49080297e0d65949211dd2e41acb2924200e4f52d8e524848f4d9053b4a49091f1dc86769492123e3a10ced292420087f809da52484010fb013b4a49080317cc276949210062e984ed292424bc77109da52484018ea213b4a4908021fe1d64949210052fc1ac9292423ba5c8359252484014f700b24a4908e29e20164949211dd2f436c72924200c5e76d8e52484014bf01b1ca4908029760363949210062fb86c72924200c5d70d8e52484010ff0eb1ca490803179d8639492127e3a38ecaa92424787e829d8524848f0f9053b0a49091f1dc86761492123e3a10cec292420087f809d852484010fb013b0a49080317cc276149210062e984ec292424fc77109d852484018ea213b0a4908021fe1d64149210052fc1ac82924237a5c8359052484014f700b20a4908da9e20164149211bd2f436c62924200c5e76d8c52484018bce5b18a490803939cb63149210052fc06c62924200a5d80d8c52484018bee1b18a490803175c363149210043fc3ac62924200a5e8618c52484018bcec318a49092e1f21975d09210062e31aeba12424f87f87d9742484010fb0fb2e8490803179d763d09210062ebaec7a12424bc6e7614b42484019a8c6b8e84908122fe1d649092116d5c402c9212424b87e86dd542484018b8c7baa84909321fa1f655092127c3e43ecaa124200c5f75d8d42484018b8ebb1a84908122fa1276109210045fc3ac8212422aab88059042484018dcec29084908038b590521092100717b2a8421242c2e2c655084248401d1ec6a108490b07a318d42109211df2631ca51924237e4c6314a3248401c98c7b2c64908039318c658c92101567436c71924200cce76d8e32484970fd0dbaa64908ef1718f754c9211bc3f43eca992424f87c87d9532484018beebb1a6490803171d7634c9212be6a38ec6992424fc6c769493248477c98c7292649093f591c6524c92125e363b0a4992424bd647114932484778d8edbaa64908df1b1d8754c92127e363b6ca9924200e4c63d95324849fac8e3b2a649092f1b1d8654c92125eb2388ca9924202ccc76dcd32484af998edb1a649095f711c7634c921024f343ee29924200d67751c53248401ac8ea38a649095f71dcc714c9210062e39ecaa8a42008de86dcd51484018becbb9aa29085717197735452155c6f43ec6a8a4215
  | 2 => 0x254d8d210052fc2ae5b1a4200a5c855cb63484014bd0bb8ec6908029761771d8d210054f426e3b1a4200a9d84dc763484afcaca3a8ec69080297a1670d8d210052ec2ce1b1a4200cdb805c363484014bd0a386c6908029761470d8d210054f420e1b1a4200a9d841c3634840159d04386c69095eb360870d8d212bd6b408e1b1a4200ad5811c363484014bd05a86c69080317dc350d8d210062eb86a1b1a42008de8794363484011bb0f286c6908029720950d8d210072dc02a1b1a4200c5f7054363484018bae0a86c69080237a1c50d8d210046ec38a1b1a42008de8790363484011bb0f206c69080297a1640d8d210052ec2c81b1a42008de8710363484011bb0e206c69080297a1440d8d210052ec2881b1a4200ace82103634840159b04206c69095eb5a0440d8d210056ac0881b1a42578de8788363484011bb0f106c69080297a1620d8d210052ec2c41b1a4200a5f8548363484014b90a906c690802a7e1120d8d210054e42241b1a42008de8708363484171bb0e106c69080297a1420d8d210052ec2841b1a4200a9e84083634840153b08106c69095eb5a0420d8d210056ac0841b1a42008de8784363484011bb0f086c69080297a1610d8d210052ec2c21b1a4200cdb7084363484019b6e0886c6908031718f7558d210043f43ecab1a420087e8719563484070fd0fbaac6908021f6037558d210062f986eab1a4200c5f75dcd63484018b8ebb9ac6908021fe157058d2101c3e42ae0b1a42008bf845c1634841317908b82c69080237e0d7058d2100477c12e0b1a42008f7815c163484010fd0fa82c69080e1f21f5058d210043f43aa0b1a420087c8754163484031b90e982c69080317dd53058d2177e2e3aa60b1a4200cdb704c163484011bb013b0c690803179db6518d2100726b96ca31a4200a5d80d9463484018bee1b28c6908023761e6518d210052f42cca31a42008df8759463484014bd0c328c690803179d86518d2100726b90ca31a4200a5d8019463484018bee0328c6908023761e6418d210052f42cc831a4200a5d8599063484011bf0eb20c69080297e156418d210052e42ac831a4200adb8059063484015b100b20c69080317d957018d210062e32ae031a42008df87d8063484019b2e1b00c6908023761e6018d210052f42cc031a4200a5d8598063484011bf0eb00c69080297e156018d210052e42ac031a4200a9f84580634840153908b00c690802b3e096018d210056bc0ac031a42028de8718063484011bb0e300c69080297a146018d210052ec28c031a4200a9e84180634840153b08300c690803365c06018d210052f436a031a4200a5c86d4063484018bceda80c69080297a195018d210052e432a031a4200c5e76540634840159d0d900c690803725c32018d212e5664324031a4200ad686c4063484015a
  | 3 => 0xb3224200c5e7319664484018becab9cc8908031719573991210043f43ecab224200c5c73d9564484018f0e1b2ac8908021fa1c65591210062e398cab224200c787019564484018becbb9ac8908031719773591210063db2ee0b224200c7865dc164484010fb01baac89080317dd773591210062e3aee6b2242008dd80dcd64484018beea39ac890803171d4735912101c3f42ee4b22420087d85dc964484018f6ebb82c8908031e1d770591210066db9ee0b224200cd873dc164484018f70bb82c8908031e21770591210066dc1ee0b224200cd883dc164484010ff0ab82c89080e1f21570591210045fc22e0b2242008df835c164484051b906b82c8908023be0970591210063dba8e0b224200c78751c16448401976e8382c89080336dcc70591210066c398e0b224200ceb721c164484010fd0fa82c89080e1f21f50591210062fb9ea0b2242f2c5c73d4164484018f6e1a82c8908071e1c350591210043f43aa0b22420087c8754164484018bee6a82c890bc7171cd50591210063db82a0b224201c7870541644840117d0fa02c8908072e1c3405912100c5e43a80b224201cb87050164484011bd0f982c89080a3721f30591210062fbae60b2242f0c5c75cc164484019b6e1982c890807361c330591210046f43a60b2242008dc874c164484018beea982c890bbf171d530591210066db8260b224201cd8704c164484011dd0f902c8908073a1c3205912100c7643a40b224201ce87048164484039e0e1882c8908063d21d10591210076898220b2242008bf87590644840157100b20c89080237e0d76951210146e41aed2a24200a3d84d9654484051bd07bb2a8908023760f76551210046fc1aecaa242028dc835d954484011f700bb2a8908063e201765512104c3f43ecaaa24209a3e84d9554484091dd0db92a8908031bd9472551210043fc2ae9b1a420387c855d363484018baeba9ec69080297a1630d8d210052ec2c61b1a42018df874c363484019b2e0986c6908029760365d8d210052ec00cbb1a4200a5e8599363484014bb0b326c69080297e1564d8d210052e42ac9b1a4200adb8059363484015b100b26c69080317d9770d8d210062e32ee1b1a4200c5f655c363484018b8cab86c690803365c360d8d210052f42cc1b1a4200a5d8598363484014bf0ab06c6908029721560d8d210054fc22c1b1a4200a9c8458363484171bb0e306c69080297a1460d8d210052ec28c1b1a4200a9e84183634840153b08306c690803365c060d8d210052f436a1b1a4200a5c86d4363485e58bceda86c69080297a1950d8d210052e432a1b1a42f1c5e7654363484af5990c906c69080374dc110d8d210062eba8ebb1a4200a9e841d7634840153b083aec69080297e1574d8d210052e42ae9b1a4200a5e851d363484014bb0a3a6c69080387d5
  | 4 => 0x5484014b90c986ca90bbf179d930d952127d3643241b2a4200e68604836548401ce0c0886ca90803d44c110d952127d36c16e9b2a4200c3f749d3654840187ae83a6ca908028fa1073d95210051ec20e7b2a4200c5d731cf65484014dd0439eca9093e9b60873d95210043f43c87b2a420087d8790f654849f0fd0f996ca908021f61f32d95210051f426e3b2a4200a3d84dc765484014bd07b8eca908029760f71d952127e3a38ae3b2a424787e82dc365484014bd07386ca908029760e70d952123c3e412e1b2a4200c7b805c3654840147d08386ca908028f61070d95210052f418e1b2a4200a5d831c365484014dd04386ca9093e9b60870d952127d3b408e1b2a4200a75811c365484010fd0f206ca908021f61e40d95210052f41c81b2a4200a5d8390365484010fd0e206ca908021f61c40d95210052f41881b2a4200a5d8310365484014dd04206ca908029b60840d952127d3b40881b2a4200a7581103654846d8bce5986ca908e3171cb30d95210062fb8661b2a4200c5d70cc365484010fd0f186ca908021f61e30d95211b62f39261b2a4238c5c724c36548401cb700986ca9080317dc130d95210062eb8261b2a420087e870c365484010fb0e186ca9091e1fe1f20d952123c3e43e41b2a424f87e8788365484010fb0f106ca9080297a0e20d95210052ec1c41b2a423687f8748365484710f90e906ca908028fe1120d95210051e42241b2a420087e8708365484190fb0e106ca908028fa1020d95210051ec2041b2a4200a5e8308365484014bb06106ca9093e9da0420d95210053ac0841b2a420087e8784365484010fb0f086ca9080297a0e10d95210052ec1c21b2a4200e59308436548401cb260886ca908031719773595210146f43ee6b2a4200c5f75dcd65484018b8a5b9aca908023760373595210062fa86e6b2a4200c5f751cd65484010ff0ab82ca908022fe11705952104c5e422e0b2a42008df835c165484051b906b82ca908023be09705952100c3e43aa0b2a4200c5f7354165485e38b8e6a82ca908031edc150595210046f43e60b2a42028dc87cc165484011bd0e982ca908023721d30595210043ec04ec32a420087f87d8065484018f2e1b00ca908021f61e60195210052f41cc032a4200a5d8398065484010ff0eb00ca908028fe1160195210051e422c032a4200a5f8358065484014b906b00ca908029be09601952101c3f438c032a420087d87180654840147d08300ca908028f61060195210052f418c032a4200a5d8318065484018f2e0300ca9080297a1b30195210062f3b66032a4200a5c864c065484018bcec980ca908029ba1b201952125d364324032a4200a74864406548401ea260880ca908021fe1573d912101c3e42ae7b224200aad82103644840156b02206c890803b44c110d91210062f39ec
  | 5 => 0x8028fe1520592210051e42a40b2442008be87081648840117b0e102c9108028fa1420592210051ec2840b244200a9e83081648840153b06102c910812ada0420592210055ac0840b244204ab7804416488409d6700882c9108038dd4110592210071aa8220b244200e97304416488401d6460882c910803a54c110592210075898220b244200e9130441648840187ea8bb4a9108121fe1d65952210051fc22cb2a44203a3e8559254884018dacb394a9108272b992729522104c77c32e52a44200c6d655ca548841395cc8b94a9108121f21d65552210245e43ac8aa4420387e85dd163884010fb0bba2c7108029b2095058e2100c6e43a60b1c4200cdb704c163884090f90bbb2a7108121f21d6554e210152e41acaa9c420387e855db43884010ff0cbae87108270f99175d0e210043fc3acba1c420087d87597438840187ceab2687108030f5d564d0e2104e57324e5a1c42098ef865cb438841395cc8b9687108122f21d6450e2125e1f394c92944200c3f70992528840187ae1324a51080387cc26494a210070e984c9294424bc3e72592528840187ee0b24a5108030f5c16494a210070f982c92944200e1d30592528849fc6e20b24a5108038d4416494a210063ab2ee2a94424ce2d82990528849f87ce5320a5108038b9ca6414a2125f1790cc8294424be2d21990528840187ee1320a5108030f5c26414a210070f984c82944200e1d309905288401c5c41320a5108038b0826414a2127e1f392c82944200e2e72590528840187ee0b20a5108030f5c16414a210070f982c82944200e1d305905288497c6e20b20a5108038d4416414a210043fc32eba144209c3e645d742884010ff0eb2e85108030f9d564d0a210061ebaac9a144209cb6645c74288499c5cc829485108021f61b7550a212861f326eaa14425087e8759542884990f90eb2a85108030fdd56450a210061e3aac8a14424cc6f761494288499c5cc829285108032d5937150a2104d57c328421442c2e2e655084288401c5acaa1085108021f61b754ca211dc3f43aca994423787c87595328840187eeb32265108030f1d6644ca210061fbaac89944200c3c755913288409968e2b2265108032d593714ca2127db2c34a590c4247e658694b218849facaed296431091f995da52c862127f93324a590c424ff256494b21885e7e8e612964310bcfd14c252c862123db3c2aa590c4200c5d7394f65484014db0529eca9080297a0e50d95210052ec1ca1b2a420187f8754365484018f2e0a86ca908031e5c360d95210052f41cc1b2a4200a5d83983654840147f08b06ca908028f21160d95210052fc1ac1b2a4200a5c8358365484190fb0e306ca908028fa1060d95210051ec20c1b2a4200a5e8318365484014bb06306ca908031e5c060d95210052f43661b2a42f0c5e76cc36
  | 6 => 0xbd1ec2ca13244200a9e83942648840153b07284c910802abe09509922100556412a13244200e2f82542648840147904a84c9108038b209509922100516412a13244200e3b8054264885ed47d0a284c910802a7a0c50992210054ec18a13244200e1f50cc26488401c3aa1984c9108028fa1630992210051ec2c6132442f5a9d838c26488401d3700984c91080387d4130992210070ea826132442f5e9a104c264885ebd3220984c9108028fa1430992210051ec286132442f4a9e830c2648840147d0b104c9108028f61620992210054f41c413244200a9d83882648845b17f0e904c9108262f21d20992210051fc2a413244200a3c85482648841317d0e104c9108022f61c20992210051f428413244200a3d85082648840153d06104c910802a760c20992210255b408413244200ab581082648840917d0faa2c9108030fdd7545922101c3f42ee6b24420087d85dcd648840917d0f21ac9108028fa1643592210051ec2c86b2442048be87901648840147d0b202c9108028f61640592210054f41c80b244200a9d83901648840956d03202c9108062f21d40592210051f42880b244200a3d85101648840153d06202c910802a760c405922100556c1080b244204ab6811016488401da260882c9108030fdd675592210054f41ceab244200a9d839d5648840147d0bb9ac9108028f61773592210051f42ce6b244200a3d859cd6488401c3ea729ac9108028fa1772592210051ec2ee4b244200a3f855c964884014790ab92c910802a7e0d72592210054e41ae4b244200abb805c9648840157100b92c9108028fa1732592210051ec2e64b244200a3e859c1648840147b0b382c910802a7a0e70592210054ec1ce0b244204ab6819c1648840156b03382c910802abe09705922100556412e0b244200a3e851c1648840147b0a382c910802a7a0c70592210054ec18e0b244200aae821c1648840155b04382c910812ada0470592210055ac08e0b244200a3e82d4164885edc6e21a82c910bde8f61650592210054f41ca0b244200a9d83941648840956d03282c910802ad60650592210051e412a0b244200e3b8054164885efc6e20a82c910bda8fa1450592210054f418a0b244200a9d83141648840956d02282c910802ad60450592210070fa8660b244200e1d50cc164885e9d2e21982c9108028fa1630592210051ec2c60b2442f5a9d838c1648840956d03182c910802ad60630592210074dc0260b244200e1f504c16488401c3aa0982c910bd7a5c4130592217af4d08260b2442f5e99104c1648840147d0a182c9108028f61430592217a54f41860b244204ab6810c1648840156b02182c9108028fa1620592210051ec2c40b244200a9e83881648840153b07102c910812ada0620592210055ac0c40b24422d8bf8748164884551790e902c91
  | 7 => 0x7f805d763c84018be60baec7908030f9d674d8f210061ebace9b1e42098bf875d363c840187ceaba6c7908030f5d574d8f2123e1f292e9b1e4247c3c525d363c840193e60ba6c7908032b5d272d8f2123673392e3b1e420387e85dc363c84010fb0bb86c7908262fa1370d8f210045ec26e1b1e420387f87d4363c84010fb0fa86c790beb0f9d350d8f210061eba6a1b1e420087f8754363c84010fb0ea86c790be70f9d150d8f210061eba2a1b1e42018df874c363c85df8bcea986c790803175d530d8f217c64f3a261b1e4200c9d744c363c84019b2e0986c79080e1fa177458f210043ec2ee8b1e4200a5e85dcd63c840153d09b9ac79080317dd75358f2100c6e43a60b1e4200cdb704c163c84010fb0b3b2a7908262fa127654f210045ec24eca9e42008dd839d953c84050fd0fb2aa790a8e8fa136554f210152f41ecaa9e424796c825d743c84018bceab1e87908263de1971d0f2101c3f42eeca1e420087d85dd943c84070fd0b3b287908021f6167650f210045ec24eca1e4247a6c8259652c84018eacab8ca59091e9b2096414b2123f16292c82164200c5c7359551c8401878eab228390803271cd645072100656b20e4a0e4200c5c7558d31c84090fd0f29acb1080317dce53596210243f43ca0b2c4200a5e8394165884014bb07282cb108061f21d505962100537c12a0b2c4200c7b70541658840187ee93a2cb1080297a0e74596210052ec1ce8b2c4200a6d829d165884018bee739acb10803175cc73596210043f43c86b2c420087d8790d65884014bf06b92cb108029720d72596210043f43e64b2c420087d87cc965885ef0fb0f382cb1080297a0e70596210052ec1ce0b2c4204a76819c165884014eb03382cb108029be09705962100536412e0b2c4200c6f825c165884018d904b82cb108031ee0170596217b43f438e0b2c4200a5e831c165884014bb06382cb108021fa1e40596210043ec3c80b2c4200a5e8390165884014bb07202cb108021fa1c40596210043ec3880b2c4200a5e8310165884014bb06202cb108029ba08405962100536c1080b2c4204a768110165884014eb02202cb1080317dc330596210062eb8660b2c420087e878c165884010fb0f182cb10bd69760e30596210072dc0260b2c4200c5f704c165884018bae0982cb10bd79684130596217af2c88260b2c420087e870c165884010fb0e182cb10bd297a0c30596210043f43c40b2c420087d8788165884014bd07102cb108029760e20596211c43fc3a40b2c423687c87481658840147f08902cb108028f211205962107c3f43840b2c420087d87081658840147d08102cb108028f61020596210052f41840b2c4200a5d8308165884094ed02102cb108029d60420596210070fa9ca73244200a3e85cca648840147b0b994c9108028fa0b50992217
  | 8 => 0xeb24a49880297e0d649493101c3e428eca92620087f809d8524c4010fb013b0a49880317cc276149310062e984ec292620087f87590524c48f0f90eb20a49880297e0d641493101c3e42ceda12620087f855db424c4070f90abb684988021f21975d09310043fc3ecba12620087d87d97424c4010ff0abb4849880e1f215769093101c3f42eeca12620087d85dd9424c4070fd0b3b284988021f616765093101c3e428eca12620087e86dd5424c4010fd0fb2a84988021f21f655093100557416c8a126209aae84d89424c4010ff0abb0849880e1f21576109310062e32ae62126200cae76508424c413958eca1084988038bd9542109316171632a842126225c5c73d95514c4018becbb9aa2988571719773545310062e32ae7a0a627187e86dd5414c5290fd0fb2a82988961f21f655053112e2e39ecaa0a6200c5f65dcd414c4018b8cbb9a82989df2719373505310061f32ce9b2e42098bf875d365c848f87ca4ba6cb9091f0f14974d97210061fa82e9b2e4200c9e749cf65c840193ae939ecb9080a37e1d73d97210064f3a2e7b2e4200c9d745cf65c848f8bca4b9ecb9091f1714973d97210046fc02e7b2e4200c5f505cf65c840195ae9396cb908262fa1370d97210045ec26e1b2e42028de83dc365c84011bb07b86cb908061fe1d50d97217ce1f3a2a1b2e4200c3d7454365c85e38bce6a86cb90803175cd50d97210063cb82a1b2e42028df87cc365c84011bb0f986cb90bef279d330d97210064eba661b2e42008df874c365c84011bb0e986cb90be3279d130d97210064eba261b2e4200a3e84dd565c84014bd07baacb9080317dce535972100c3e43aa0b2e4200c7b7054165c84010ff00baec990803179d673d93210062ebace7b264200c5e755cf64c84018baeab9ec99091f1794973d932123e2e292e7b2642008df805cf64c84070fd0bb86c9908021f61770d93210146f41ee1b2642008dd83dc364c84070ff0fa86c9908021f61f50d93217962f39ea1b264200c5d73d4364c84010ff0ea86c9908021f61d50d932178e2f39aa1b264200c5d7354364c84051bf0f986c9908023761f30d93217862f3ae61b264200c5d75cc364c84011bf0e986c9908023761d30d932177e2f3aa61b264200c5d754c364c84031db0f906c9908023be1d20d932123cb6412eb3264200a3e85d9264c840153d07b24c9908028fa1774593210054f41ee8b264200c3f75d5164c84070fd0bb9ac9908021f61773593210051f42c86b264200aae8290d64c84031790ea02c99080336dc1305932100e6c38260b2642008bf8759064c840147f08b2ca9908022f61276553210146f41cecaa642008dd839d954c84130fd0fb2aa9908268fa1365553212152f41ecaaa642048ed861c954c848f8deca392a9908032798e74d8f2101c3fc3aebb1e42008
  | 9 => 0x705953100476412e0b2a620187c87541654c42b8bee6a82ca988031edc150595310046f43a60b2a62018dc874c1654c4019b6e0982ca9885717d8e72195310ae2fb1ae032a620087f87d80654c4018f2e1b00ca988021f61e60195310052ec1cc032a620087f87580654c40147f08b00ca988028f21160195310052fc1ac032a6200a6f82580654c4014d904b00ca9880e1fa1c60195310043ec38c032a6271a5e83180654c4018f2e0300ca989ca97a1930195313952e4326032a6225c5e764c0654c401cb6c0980ca988021fe1572d913101c3e42ae5b226200a9d83103644c40155b04206c898802ad60440d913100637b2ce53226200c6c659ca644c4ef99ec7394c8988031bd9572991310063632ae53226200caf645ca644c413958c8b94c8988021fa1f65591310043f438cab22620387e87dd5644c48f0fd05baac8988021f60375591310062f986eab226200c5f75dcd644c4018b8ebb9ac89880237603735913101c3f42ee4b22620087d85dc9644c4010ff0ab82c89880e1f21570591310045fc22e0b2262008df835c1644c4011df04b82c8988023b20970591310043f43ea0b22620387c87d41644c4018bee7a82c8988021fa1d50591310043e43aa0b226200c5f73541644c4011bd0e982c8988063721d30591310062fbaa60b2262efc5c754c1644c4019b6e0982c8988022fe1d64191310051ec26cb2a2620087f855d9544c4011bf06bb2a8988261fa1f655513109c3ec3ecbb126200a6e82d97624c4014dd0432ec49880e1fe1d75d89310043fc02ebb126200c5f305d7624c4070fd0bb86c4988021f61770d893104c5f426e1b1262008bd84dc3624c4070ff0fa86c4988021f61f50d893100537416a1b12620087f87543624c4010fb0ea86c4988029b20950d893177e2f3aa61b126200c5d754c3624c40155b08106c498802b360c20d893100572c0841b126200c3f659d2624c401878cb3a4c4989df27d8e74989310061fb2ae93126200c3c655d2624c40195ae9b14c4989d21f21b75589310043f43ecab12620087e87195624c48f4dd05b28c49891e9ba08651893100477c3ac4312620087f855d0624c4070f90aba0c4988021fe15701893101c3e42ae031262008bf845c0624c41317908b80c49891e1fa1f501893123c3e43ea03126247a6e82d40624c48f0f90ea80c49891e9b209501893177e2e3aa603126200acd83880624c40155b08100c498802b9604201893123d37416cb2926200a6d82d96524c42b4bf06b2ca49891e9b209659493123c3f414ed2926200c5e319da524c4018b8633b4a4988021fe0276949310043ec04ed2926200c5f309da524c4018ba613b4a4988021fa18769493123e37410ed292624787f801da524c4010fb003b4a49880317cc076949310062e980ed292620087f87592524c48f0f9
  | 10 => 0xb2c6200c7b70541658c42b4bd0a982cb1880e1fa1f755923123c3f416eab24620087d80dd5648c4018be61baac91880317dd773592310062e3aee6b24620387e85dc9648c4010fb0bb92c9188021fe15705923101c3e42ae0b2462008ef825c1648c4011d904b82c9188021fa1f505923101c3e43ea0b24620087e87541648c4010f90ea82c9188062f21d40592310062fbaa60b2462efc5c754c1648c4074790ab24a91882637e19739523128c3fc2aecaa4620487c87595548c4091790eb22a91880317597735523100c76c3e41314620387e87dd5628c4010fb01baac51880317cc37558a310043fc2ae0b14620387c855c1628c40117f08b82c5188262f2117058a310043f43ea0b14620387c87d41628c4010fd0ea82c5188021f21d5058a310062fbaa60b1462efc5c754c1628c4031d90e902c5188262fa137694a310045ec26ed2946247a6c82596528c4018bacab9ca5188021fe1d6494a3123c3e43ac92946247c5f765ce528c4012bb0fa1ca51892e1fe1d6294a310043fc3ac8294624787c87590528c42b2bd0fa18a51893e1fe1d6214a3101c3f42eed214620087d85dda428c42b2b90ab9c85188021fe157650a3101c3e42aeca1462008fb805d9428c4031f100bb285188021fe157610a3101c3e42aec214625c8df8758a328c401c9ac529465188029760e50d953100c3fc3aa1b2a6200c7970543654c4018f2e1b06ca988028fe1160d95310051e422c1b2a6200a6f82583654c4014d904b06ca9884e1f61c60d95310063cb80c1b2a6274a5c864c3654c4e38bcec986ca9880396d8130d95310072c30261b2a6200c3d741d3654c4010fb01396ca9880317cc272d953100636b90e5b2a624787e82dc3654c4018be61b86ca988021f61e70d953112d2f41ce1b2a6200a5d839c3654c48f0f904b86ca988031ee0170d95310062f982e1b2a6225a5e831c3654c4e94bb06386ca988021fa1e40d95310043ec3c81b2a6225a5e83903654c4014bb07206ca988021fa1c40d95310043ec3881b2a6225a5e83103654c4014bb06206ca988029ba0840d953100536c1081b2a6274a7681103654c4014eb02206ca98803179c930d953112d2fc0261b2a6225e5b804c3654c4018bee0986ca98803175c130d953123c3fc3e41b2a620087e87883654c4010fb0f106ca9889697a0e20d95310052ec1c41b2a620087f87483654c4010f90e906ca988028fe1120d95310051e42241b2a620087e87083654c4010fb0e106ca988028fa1020d95310051ec2041b2a6225a5e83083654c4014bb06106ca989d29da0420d95310053ac0841b2a622587e87843654c4010fb0f086ca9889697a0e10d95310052ec1c21b2a6200e5930843654c401cb260886ca988021fe1570595310045fc22e0b2a62098bc845c1654c4011bf06b82ca988023be09
  | 11 => 0x104014df04b82ca208029b20970594410061fc22e0b2882f9c3c845c165104018df04b82ca2091e1f209705944100636412e0b28820086c825c165105ef87e82b82ca20bdf0f50570594410063dc02e0b2882f687e871c165104014bd06382ca208029760c70594410062e39660b2882f4e1f41cc165105e9c3a83982ca2080317dc330594410062eb8660b28820087e878c165104010fb0f182ca20bd69760e30594410051fc2260b288209a3c844c16510401c3f08982ca20be38721130594410062e39260b2882f5e1f414c165105ebc3a82982ca2080396e0130594410062fb8260b288200c5d704c165105ebcb420982ca20bd79644130594410043f43860b28820087d870c165105e94bd06182ca2091e1f21f20594410043f43c40b28820087d8788165104014bd07102ca208029760e20594410063639440b28820087f8748165104010f90e902ca208028fe11205944104d1e42240b28820087e8708165104010fb0e102ca208268fa1020594410051ec2040b288200a5e8308165104014bb06102ca2091f1b1c820594410253b40840b288200a758108165104070fd0bb92c6208021f6177258c4104c5e422e0b1882018dc874c163104019b6e0982c6208121f21d6554c410043fc2ae7310820387c855ce62104010ff0ab84c42080e1f215709884123c3f43ea1310824787c87d42621048f0f90ea84c420bc3171d7309884177e2e3aa6131082018ed87c82621041355908904c42080e1fa1f75588410043ec06eab10820087f855c162104070f90ab82c4208b62fe11705884104c5e422e0b10820087e87d4162104070f90fa82c4208021fa1d50588410043e43aa0b108200c5f75cc162105e18b8eb982c42080317dd5305884177e2e3aa60b1082018ec87481621041355908902c4208270f9d1659484123d36412cb29082008bf865d2521040187acaba4a42091f0fa13769484123e37416ed290824fc3f41dda521049f87a83bb4a42091e1fe0376948410043ec06ed2908200c5f30dda52104018ba61bb4a42091e1fa09769484123c3e412ed290820087f805da52104010fb00bb4a42080317cc176948410062e982ed2908200a3f865d2521048f87eecba4a42092e1fe1d62948410243e42eeca90824787e825d8521048f0f904bb0a42092f0fd05761484125e1ea0aec290820087f805d852104010fb00bb0a42080317cc176148410062e982ec290824f87f87588521041387ce8b2c64208022fe19748c8410061eb2ae919082048ed8798a32104070f90bbb264208021fe15764c84101c3e42aec990820087d86dd532104010fd0eb2a64208021f21d654c8410247643ac49908200c5f53dc1658c40117f08b82cb188262f21170596310062fa9ae0b2c62008ef825c1658c4011d904b82cb188061f21d50596310052fc1aa0
  | 12 => 0x8ee9720d76949410043f430ed2928247c6e821da525048f0ff003b4a4a08021f60076949410062f980ed2928200c5d301da525049f47d0dba4a4a08030f9db749494100597416e92928200a3e861d2525040187cec3a4a4a0802c760c749494100597410e9292823ba5e86d8e52504018bcedb1ca4a0803171db63949410052fc06c72928200a5d80d8e52504018bee1b1ca4a0803175c363949410062f3b0c72928200c5c7618e525040127d0fa1ca4a08030f9db43949411df0e31e87292824fa3c8650e525040187ceca1ca4a093ecd20543949410146f41eeca9282008dd83dd952504070f90a3b2a4a0a5b0f1d365549410061fb2ee8a92820087f809d852504010fb013b0a4a08030fd0276149410061ea04ec2928200c5f309d852504018ba613b0a4a08031dc4276149410063a884ec2928237a5e86d8c52504018bcedb18a4a0803171db631494100727396c62928200a5f80d8c52504014bb01b18a4a080317dc363149410062eb86c62928200c5e7618c52504018b8ec318a4a08024f61f43149411bf0e31e86292824ba3c8650c525049766902a18a4a08122fa1b759094128e1f3b6cb2128295c3e76196425040127f0ab9c84a09c3279db639094137e4f3b0c72128200e2f65d8a425040147d0d29484a08038bd8a52909410051f430a5212829587e86dd542504018b8c7baa84a08021fa1f65509414b716216caa128200c5f75d8d42504018b8ebb1a84a09dfa310b635094100597416ca2128200c3e76194425040936902b9884a0803279d863109410051f434a42128200a3e8614842504010ff0abb464a080e1f215768c94123d37416cb19282048be86dd2325040936d03ba464a080e1fa17764c9410043ec2eec992820387e859d932504010fb0b3b264a080e1f214764c9410146e418ec992820087e86dd532504778b8c7baa64a08021fa1f654c9410043e43eca9928200a6e82d9532504018beebb1a64a0803171d7634c9413be4e3a6c69928270cd471d8d325052d878e9b2aa2a0803171cf65545410061fb2ee8a8a820493c8755151504094790caa2a2a0a47471cd54545410259a40aa8a8a828e8de86dcd51504018becbb9aa2a085717197735454155c6f43ec6a8a82778dc87d8d51504018bee729aca208262f211705944100477c12e0b2882008ec825c165104090fd0f282ca2080297a0e50594410052ec1ca0b28820187c87541651041347908a82ca208031edc150594410062fb9ce6b288209a3e849c9651048f8dc84392ca209331b508725944125e1fa08e4b28824bc3d411c965104978da42392ca208021f60072594410043f43e64b28820087d87cc9651048f0fd05b82ca20bdb0fd0770594417b61ea0ee0b2882f787d879c165104014bd07382ca208029760e70594410051fc22e0b288209a3c845c165
  | 13 => 0x52f436a031a8200a5c86d4063504014bd0ca80c6a0802972195018d410054f4368031a8200d9970d0063504df5390ca00c6a0a3ab52191018d41006e8b822031a820287e87d955350401878ed2a2a6a080e37a1f6354d4148e8e31aeba1a820093c825d7435041387ec2bae86a08274dd8575d0d410049fc02eba1a820093d805d74350523a3e60bae86a0803474c175d0d410069b882eba1a8200d35105d7435040127f0fb2e86a08038718f65d0d410049ec38cba1a8200e1c63197435040553d0db1e86a0803279db63d0d410068ebaec7a1a8270cd471d8d43504091790cbaa86a08126d2057550d4128e1e3b6caa1a8200e1c63d9543504a3a68e3b2a86a0a570f1d86550d414ae9a388caa1a8270c9c76d8d43504e1b28e3b1a86a08126da1f7150d41386cbb98e2a1a821b87d87d9762504014dd05b2ec4a08029ba0865d89410062f3aec7b128200c5d75d8f62504018bcea31ec4a0803175d463d89410043fc02ebb12820387e85dc362504010fb0bb86c4a080e1fe1f50d89410043ec3ea1b128200a6e82d4362504010ff0ea86c4a08021f61d50d894100536412a1b128200aae82d03625045517f0ea06c4a0802ab20940d89417862f3ae61b128200c5d75cc362505df8bcea986c4a0803175d530d894100556c2041b128200ae581083625040996ae8886c4a0803b44c110d89410062f39ecb3128200c5e7319662504018becab9cc4a08031719573989410062f3aec73128200c5d75d8e62504018bcea31cc4a0803175d4639894128c3e436eab12820087e87d9562504018b8e7b2ac4a08031e1c365589410043f438cab128200c5c7319562504018f0e032ac4a09c23721b73589410062fb2ee6b128200c5c65dcd62504011bd0fb1ac4a080317dd763589410062e3aec6b128200cd870d8d62504011bd0e31ac4a080317dd463589410062e3a8c6b128200cd87018d62504018f6cbb82c4a08031e19770589410066db1ee0b128200cd863dc1625048f4dd05b28c4a091e9ba08651894100477c3ac43128200ae88058862504010ff0ab98c4a080e1f21573189410043fc2ae0312820387c855c0625041317908b80c4a091e1fa1f501894123c3e43ea03128247a6e82d40625048f0f90ea80c4a091e9b20950189417862e3ae6031282efc5c754c0625040155b08100c4a0802b960420189410046fc1aed29282028dc835da525048f4dd05b2ca4a08029b60b65949410052fc1acb292823ba5c83596525048f4d904b2ca4a08030f9da549494101d1e432a92928200c3e76552525040187b093b4a4a091e1fa0a76949410061f20ced2928200c3c419da52504010ff013b4a4a08021f60276949410061fa04ed2928200c3d409da52504018be613b4a4a0803174c276949410063b884ed2928200c75109da52504014bf06bb4a4a0
  | 14 => 0xd75d4f635040153b09a9ec6a08021fe1572d8d4101c3e42ae5b1a8200a5e858c363504014bb0b186c6a080637e1d30d8d410066cb8261b1a8200a5e82d9763504014bb01b2ec6a08038761065d8d410052f410cbb1a8200a5d801976350401c38cb2a6c6a09c2a721954d8d410062fb2ee1b1a8200c5c65dc363504018becab86c6a08031719570d8d410066cb86c1b1a8200a5e8598363504014bb0b306c6a080297e1560d8d410052e42ac1b1a8200acf82583635040159904b06c6a086a3761c60d8d410052f428c1b1a8200a5d85183635040159d04306c6a0802b360860d8d410066cb80c1b1a8200a5e86d4363504014b90da86c6a0bcb179db50d8d410052f432a1b1a8200a5c8654363505e38bceca86c6a09c2a721940d8d413bd6a43221b1a8200dd37044363504018baea3aec6a09dea7a1075d8d413854ec20ebb1a8277e1e54d5363504014bd0bb96c6a08029761772d8d413854ec26e5b1a8277ad581dcb63504014bf0ab96c6a08029721572d8d413872b28ea3b1a8200a5e859c363504014bb0b386c6a080336e0170d8d410052f428e1b1a8200a5d851c363504ef53d08386c6a09c2a761070d8d4100567410e1b1a8200acd821c363504e15ad02386c6a09deb560470d8d410052f416a1b1a8200c5f70d4363504018bae1a86c6a080237a1e50d8d410046ec3ca1b1a8200a5c825436350401cb700a86c6a080317dc150d8d410062eb82a1b1a82008de8714363504011bb0e286c6a09c237a1e40d8d410046ec3c81b1a8200a5e8590363504014bb0b206c6a080237a1e20d8d410046ec3c41b1a8200a5e8588363504014bb0b106c6a080297e1520d8d410052e42a41b1a8200a9f8448363504ef53908906c6a080237a1c20d8d410046ec3841b1a8200a5e8508363504014bb0a106c6a09dea7a1020d8d410054ec2041b1a8270ad68108363504015ab02106c6a09de37a1e10d8d410046ec3c21b1a8200a5e8584363504014bb0b086c6a080336dc210d8d410066db8221b1a8200c5c63dd563504010fd0fb2ac6a08021fa1c6558d410062f3b6ca31a8200e1d74d9463504014bd05b28c6a0802976036518d410062fb86ca31a82008dd8799463504014bd0b328c6a080237e1d6518d410052f430ca31a8200c5e761946350401c3b08328c6a0803875d06518d410052f410ca31a8200a5d8019463504018bee0328c6a0803871965418d4137d4e432a831a8200c5f655c063504018b8cab80c6a0803365c36018d410046ec3cc031a8200a5e8598063504014bb0b300c6a080237e1d6018d410052fc2ac031a8200a5c85580635040153f08b00c6a0802b3e096018d4100566412c031a82028de8718063504011bb0e300c6a080297a146018d410052ec28c031a8200ace82180635040159b04300c6a0803365c06018d4100
  | 15 => 0x6306caa08029760c60d954100537410c1b2a8200a6d8218365504018f2e0306caa09468f21940d95410071c30281b2a8200a5e86cc365505e18bced986caa08029721930d954177e2f3b261b2a8296a74864436550401ce0c0886caa0803d44c110d954128e1e3a2e9b2a8296a3e841cf65504a347b0839ecaa0803175cc73d954100537410e7b2a8200a6d821cf65504010fb0f21ecaa09468f61372d954100637a14e5b2a8247c6c429cb65504018dc43396caa091f1b08672d95410043ec04e5b2a8200c6d721cb65504010fd0f996caa08021f61f32d954128e3a38ae3b2a824787e82dc365504014bd07386caa08029760e70d954123c3e412e1b2a8200c7b805c3655052d47d08386caa09468f61070d95410052f418e1b2a8200a5d831c365504014dd04386caa08029b60870d954128d3b408e1b2a8296a75811c365504a30fd0f206caa08021f61e40d95410052f41c81b2a8200a5d8390365504018bce5986caa080317dc330d95410062eb8661b2a820087e878c365504010fb0f186caa0803179c930d95410072dc0261b2a8200c5f704c365504018bae0986caa08021fa1c30d95410043ec3861b2a824787f87c83655048f8dce5906caa08021fa1e20d95410043ec3c41b2a8200a5e8388365504014bb07106caa08021fe1d20d95410043e43a41b2a8200a3f84483655052d47908906caa08031b9c920d95410043f43841b2a820087d87083655052d47d08106caa08028f61020d95410052f41841b2a8200a5d8308365504a34ed02106caa08029d60420d95414b43f43c21b2a820087d8784365504014bd07086caa08029760e10d95410072c98421b2a8200e593044365504018b8cbb9acaa080a37a1f73595410062fbaee6b2a8200c5c52dcd65504011bb01b9acaa080317d4373595410062fba8e6b2a820087f855c1655040117f08b82caa080237e0d70595410146e41ae0b2a82008ef825c165504011d904b82caa08061f21d50595410062fb9aa0b2a82f1c5c7354165504018f6e0a82caa080237a1f30595410146e43e60b2a82008de874c165504011b90e982caa08021f60276195410043fc3ec032a8200c7970d8065504010fb0f300caa080297a0e60195410052ec1cc032a820087f87580655040147f08b00caa080297e0d60195410052e41ac032a8200a6f8258065504014d904b00caa080e1fa1c60195410043ec38c032a8200a5e8318065504014bb06300caa08029ba08601954100536c10c032a8200c7970180655040147d0da00caa0a568f21940195410052f4366032a8200c5e76cc065504014b90c980caa0803179d930195414a53a4322032a8200f5130440655040747d0db2ca8a08030f9db659514128e3a38ecaaa28251c3c76d95545041327b0bb9aa8a0a474794f735514128e9bba8e2aa28200c5
  | 16 => 0x694b4100637392ed2968250c3e76dd252d040165d05ba4a5a09321fe1d6294b4128716212c529682048bc845d952d048f4df0f310a5a091e9b61e6214b4123f173a4c42968247e2d7498852d048f8dee1310a5a08031b5c26214b4100727984c42968200e4d3098852d04a10ff0eb10a5a09338b1096214b4100537c3ac42968250c6f8758852d04018dee0b10a5a08031b5c16214b4126717a02c42968200e2d4058852d0401c9e60b10a5a0803934c16214b4104e57392ed216820093f855ce42d0401c5ac429485a08021fe15768cb4101c3e42aed19682048bc845da32d04010ff0abb265a080e1f215764cb410245e422ec9968200c5c7359551d04092790eaa2a3a0a9b471cd545474100c3e43aa0b2c8200a3f8454165904018f6e0a82cb2080e1fa1f7558e4123c3f416eab1c8274c3f41dd563904e987a83baac7208021f6037558e410062f986eab1c820387e85dc963904010fb0bb92c7208021fe157058e4101c3e42ae0b1c820087e87d4163904070f90fa82c7208021fa1d5058e410043e43aa0b1c82018dc874c163904018beea982c720bbf171d53058e410066db8260b1c827487f855d953904090f90eb2aa72091e9b2095098a4100c76c3e413148200a6c85482629040155f08904c52080e1fa1f7558a4127e36c16eab14820087d80dd562904018deea292c5208021fe157058a4101c3e42ae0b14820087e87d4162904070f90fa82c5208021fa1d5058a410043e43aa0b148200a6c8254162904018beeb982c520bc3171d73058a410062fbaa60b1482efc5c754c162904031d90e902c5208029b2152058a410076898220b1482028de83dda52904011bb07bb4a52091e9b2096594a410061eb2ae92948200c6e725da529048f878ed3a4a52091f0fdd97494a410043fc3ac7294824787c8758e52904970ff0eb14a5208021fe1d6314a4123c3e43ac62948247a6f87988529048f4db0f310a52092f8bd066214a4125f16a0cc42948247c6f7098852904018dae1310a52080393cc26214a4100726984c4294824f87f8758852904014df0eb10a52093f1be1d6214a4100637b82c42948200c6d705885290401c9e60b10a520803934c16214a4125f33882c42948200e651058852904018d8eb31285208031b1d56250a4101c3f42eed194820087d85dda32904091db0f31465208032b5d2628ca410043fc2aec994820387c855d932904091e902bb265208031b1d6624ca410247643ac49948200c6c7558932904099c8e2b1265208028f61253d95410062eb9ca7b2a8200a3d8494365504014bd07286caa08029760e50d954100c3fc3aa1b2a8200c797054365504018f2e1b06caa080297a0e60d95410052ec1cc1b2a8200a5f8358365504014b906b06caa08029be0960d954100536412c1b2a821b87d8718365504014bd0
  | 17 => 0x12a200c9d7418e625440195ae9b14c4a8ab63721b73589510046f43ec6b12a2008de8718d625446f8b8ea318c4a88023be1d621895123c3e43aa6312a20387c855c0625440117f08b80c4a88262f211701895123c3e43aa0312a247a6c8254062544014db0b100c4a8802ab610201895100572c0840312a29587c865d252544a1878c8ba4a4a88031718d74949513943e432e7292a23bc5c635ce52544774bd0db1ca4a8ab7179db63949510ae2f396c7292a215e4e72d8e52544014bf01b1ca4a88029760363949510062fb86c7292a200c5d70d8e52544e58bcec31ca4a89cb171d863949510643ec3ec5292a200e4f63d8a5254401c9ec6314a4a88039318c629495100636ba0c5292a200e4f3018a5254401c9a60314a4a891f9918a719495123f32312e3292a20987c859db42544011bf06bb684a880a3720d76d09510062e31aeba12a200c3d75d93425442b8bcebb1e84a8803175d763d09510046fc1aed212a2028dc835da42544090fd0dbac84a88031718f759095123e37ba8c5212a2028de83dd942544011bb07bb284a880e1f21476509512861e326eaa12a200c5c63dd5425440187eebb2284a8802aba0b64509510062fbaec6a12a215c5c75d8d425441355d09b1284a88031bdd462509510046fc1aec212a2028dc835d842544018b8c6ba884a88032b9d9421095104e563b284212a200e8f635084254583d18c6a1084a88121fa1b758c9511de2e31eeb192a20387c851d932544051b9063b264a88ef1718f754c9510062fbaec6992a215c5c75d8d32544018bee729acba08061f21d50597410063db82a0b2e82a6d1e53dcd54d04018beeba9ac7a0826a7a135358f4101c3f42ee4b1e820087d85dc963d04031b90e982c7a080336dc13058f410143ec2eeca9e82048be84dd953d054787ca9bb2a7a08021fe157398b4101c3e42ae73168247a6e85d4a62d041355d08294c5a08029ba173298b4123d36412a131682018ed87c8262d04014d90a904c5a0826ab2112098b4101c3f43eeab168250c3c74dd562d04a1c5885baac5a09431b60b7558b410043ec06eab16824cc3c741d562d0499c58843aac5a0826aba135258b4100637ba8a4b168200a6e85cc962d041355d09992c5a08021fe157058b4101c3e42ae0b1682048bc845c162d04010fd0fa82c5a080e1f21f5058b417d716216a0b16820087e8754162d04010f90ea82c5a08029b2095058b417cf16212a0b168200aac8250162d04018beeb982c5a0bc3171d73058b417df4621660b168200c5f754c162d05df8b8ea982c5a0be3a31093058b410066db8260b168201cd8704c162d041355909902c5a08063b21d2058b410053642a40b168209aac8448162d040917908bb4a5a09430f9517694b4123d36412cb2968209c3e7655252d049f47908bb4a5a09430f1d17
  | 18 => 0x44018deeab12652891f1b14a72d91510051ec2c81b22a200a3d85103645440155b04206c8a8802ad60440d91514b637b2ce5322a200caf645ca6454413958c8b94c8a88022fe1d64191513943f436e6aa2a242c5c63dcd54544018b8c6392a8a880a1f21574d8d510143e42ae5b1aa200a5d858c363544031bf0e986c6a8807369c130d8d510066cb8261b1aa200ace82993635440159b05326c6a8ab69721954d8d512162f3b2a9b1aa200cd970d83635440153f08b06c6a8802a721160d8d5100567c12c1b1aa200acc8258363544471bb0e306c6a8803365c060d8d5156d2e432a1b1aa2f1c5e765436354401cb6c0a86c6a880297e1574d8d5111d2e42ae9b1aa2ada5d851d3635455b4bb0bb96c6a880297e1572d8d5111d2e42ae5b1aa200c5c52dc363544018bea1b86c6a88023761e70d8d5111d2f42ce1b1aa200a5d859c363544019b6e1386c6a88031714970d8d510066dc02e1b1aa200c5f505c3635442b4bd0a386c6a8ab69761470d8d510052e412a1b1aa215a5f80543635442bcb700a86c6a880317dc150d8d510062eb82a1b1aa2008de8790363544011bb0f206c6a885697a1640d8d510052ec2c81b1aa2008de8710363544011bb0e206c6a885697a1440d8d510052ec2881b1aa200ace82103635440159b04206c6a8ab6b5a0440d8d510056ac0881b1aa215a5c85c8363544011bd0f106c6a88023761e20d8d510ad2f42c41b1aa200a5d8588363544014bf0a906c6a88569721520d8d510054fc2241b1aa200a9c8448363544011bd0e106c6a88023761c20d8d510ad2f42841b1aa200a5d85083635440153d08106c6a8802a761020d8d5156d6b40841b1aa200ad581083635442b1bd0f086c6a88023761e10d8d510ad2f42c21b1aa200a5d8584363544019b6e1086c6a880336dc110d8d510046ec3cc831aa200ace82990635440159b05320c6a880237e1d6418d517452f428c831aa272a5e8655063544e54b90caa0c6a880387d915418d5112e2fb2ae031aa200d5b505c063544019b2e1b00c6a88023761e6018d510052ec2cc031aa2008df8758063544014bf0ab00c6a8802a7e116018d510054e422c031aa200acf82580635440159904b00c6a880a37a1c6018d510046ec38c031aa2f2a5e8518063544019b2e0300c6a89ca97a195018d513952e432a031aa200e5b60540635452b0fd0dba2a6a8ba31718f7454d510152f436c6a9aa2adc5c76d8d535446f8b8c6392a6a8ab755dcc7154d5104c3e42ceda1aa242c5c635d7435442b8bcebb1e86a8803175d763d0d510243e432eaa1aa242c5c635d5435441317d09b86c4a88022f61370d89511b43fc3aa1b12a200a6c8254362544014db0a106c4a8802ab61020d895100572c0841b12a296c3f659d2625440193ce9b1cc4a8803275d363989510064f3a0c73
  | 19 => 0x21fe15705913201c3e42ae0b2264008bf845c1644c8011ef02b82c8990123d20570591320043f43ea0b22640387c87d41644c8010fd0ea82c8990021f21d505913200c6e43a60b226400c5f754c1644c9df8b8ea982c89900336dc1305913200e6c38260b2264008bf87590644c80147b09b2ca8990ef179cf659513204c6e432e72a26400c5f655ce544c8018decb394a89900a3b219729513200637b2ae52a2640087f855d9544c8130fd0fb2aa89900a1fe1d659493223f26194ed292640087f87592524c8778b8e7b2aa49900317d9773549320043fc3ac8292643787c865d7424c8770ff0fb2e84990021f61f65d09321bc3f436eaa126400d4c32dd5424c8990fd0fb2a84990ee1f21f65509321be363b0a4a12644ce2c64149424c801c5ecaa10849930b8b19542109321df27b16cb1926400cdb704c3614c801da261086c299002ad61010d85320056ac1821b0a6400ae582043614c80187ecb3a4c2990030f19674985320061fb2ae930a6400c3c655d2614c809968c2ba4c2990032d5d361985321dc3e436eab0a640087e87d95614c8010fd0e32ac2990023de1d61185320043f43ca6b24a296a3e8494d64944031790ea02c9288028fe1540592514b51fc3ac92a4a295c3f87592549452d87ee0b24a9288030f5c164952510070f982c92a4a200e1d30592549440187ac9394a9289465de1971952514a63bc32e32a4a251c77605c654944018eac0b8ca92880355cc17195251006aa982e32a4a20087e8795163944018bca7b82c7288022fe117058e5104c5e422e0b1ca200c5e535c1639444b4bd06a82c7288063721d3058e510052fc2a60b1ca200cdb704c1639441387cc8bae87288030f5d564d0e51004bac0eeaa1ca2048bc87591439440187eeab2287288030f1517498a510062e29ae7314a247a6e8294e629448f0f90ea84c5288063b61f2098a5100537c2a41314a200aac84482629440117f08b82c5288262f2117058a511b43e43aa0b14a2018ec8748162944014df0a902c528802ab2112058a51006373a4c5294a247e667198a529448f8dee1314a5288031b5c26294a5100727984c5294a200e4d3098a52944970ff0eb14a52883e9be1d6294a5125e37c3ac5294a200c6f7058a52944018dae0b14a52880393cc16294a5100726982c5294a247e66625c6529449f2ef0cb8ca5288031de197194a5123e3b312e3294a24fc77605c652944018eac0b8ca52880355cc17194a51006aa982e3294a200c6d7598b42944018daeab16852880a37a0f7690a510046ec1eed214a200c3d7559242944012eb03baa8528a5b0fdd56410a5123e37bacc4214a200aad84988429440155f0ca108528802ab6194210a5104c5f426ed194a2008bd84dda32944091db0f31465288025d607754ca5100637bacc4994a2048ec87589329
  | 20 => 0x37b2ce52a464048f6819d9548c8011eb033b2a9190021fe15765523204c3e43acaaa464038bc87591548c88f4d904b2ca519003175957394a321ac3fc3ac9294644787c87592528c8010ff0eb20a51911e1f21d6414a3204e4f322e62146400cd9704c1618c8031e90e882c319003b44c110586320047bc3ac230c64028ed82dc3654c8014bb07286ca990061fe1d50d953200537c12a1b2a6400c7970543654c8018f2e1b06ca990028fe1160d95320051e422c1b2a6400a7781583654c8014e902b06ca9909e1f61c60d95320063cb80c1b2a6437c5e764c3654c801cb6c0986ca990039618130d95320061eba0e9b2a6400a5d831d3654c8774db043a6ca990029760f71d95320051f424e3b2a6400a3d849c7654c8774db0438eca990031d5c471d953200537416e1b2a643ba6d82dc3654c8018dd05b86ca990031b60b70d95320062f986e1b2a640087d879c3654c8774bd07386ca990029760e70d95320063dc02e1b2a6400c5f305c3654c8774bd06386ca990029760c70d95320043f43c81b2a640087d87903654c8774bd07206ca990029760e40d95320043f43881b2a640087d87103654c8774bd06206ca990029760c40d95320053741081b2a6400a6d82103654c8014ed02206ca990029d60440d95321dd2fc0261b2a643be5b804c3654c8018bee0986ca99003175c130d95321dc3f43c41b2a640087d87883654c8774bd07106ca990029760e20d95321b43fc3a41b2a643887c87483654c80147f08906ca990028f21120d95320043f43841b2a642787d87083654c80147d08106ca990028f61020d95321dd2f41841b2a6400a5d83083654c8014ed02106ca990029d60420d95320043f43c21b2a640087d87843654c8774bd07086ca990029760e10d95320072c98421b2a6400e5930443654c8010fd0e086ca990021f61c10d95320051f42021b2a6400a3d84043654c8774bd06086ca990029760c10d95320053741021b2a6400a6d82043654c8010ff0ab82ca990022fe11705953204c5e422e0b2a64008f7815c1654c8091e902b82ca990061f21d50595320063db82a0b2a64018dc874c1654c8019b6e0982ca992de5b20970195320043fc3ec032a6400c7970d80654c8010fb0f300ca990029760e60195320043fc3ac032a6400a3f84580654c80147908b00ca990029de0560195320053a40ac032a640387e87180654c8010fb0e300ca990de97a0c60195320063cb80c032a6400a5c864c0654c8778bcec980ca9900396d81301953201476c16e1b226400a9d83103644c80155b04206c899002ad60440d91320063bb2ce33226400c74659c6644c8018eecab8cc8990031d19571991320065bb22e33226409cb4645c6644c8010fd0fb2ac8990021fa1c655913201c3f43eeab22640087d80dd5644c8018be61baac8990
  | 21 => 0x80949421088fc5ec129284213ff8b58252508427ff87984a4a1084fff0d30949421080195eeca92842111ecbe15525084228597438a4a108447d2e87149421088fa5eec29284210038bdd8525084223d97c00a4a1084feb2d801494210989a5ce029284213134b1c0525084223f17b00a4a1084fde2d6014942109fbe1e6029284213f7c34c0525084200696296e2a108409cae87dd9421080155f01bb28421002ab603765084200717a86eca108400e2d50dd94210801d1e61bb28421003a34c3765084200657bb6eaa10844cb2e87dd542108a1a5eedbaa84210038bddb755084200617bb6eaa108400b2f80dd5421080165b01baa84211438bd83755084200716b06eaa108400f0f30dd54210801e1a61baa8421002abe19755084200657bb2eaa108450b2e871d542109f9a5d0e3aa84211334bdd8755084200717bb0eaa1084c2b2f801d5421080165b003aa84210034b9c0755084200696380eaa10844ce2f601d54210801c5ac03aa8421003c3cc0755084200786980eaa108400aaf865cd421080165f0ab9a842130acb2157350842006963aee2a108400aad869c5421098565d0b38a8421002cb616715084200557c32e2a108400b2f855c542109856590ab8a84210034b1d57150842005c7c1ae2a1084c1b8c835c5421080175700b8a84212feea201715084201c3f43eeab08840087d80dd561108051bd0fb9ac22100317dd773584420062e3aee6b0884008dd80dcd61108018beea39ac221003171d4735844207c3f43ca4b088400c5f7394961108778b8e7292c2210021fa1c52584420062fb98a4b088437c5c7314961108010ff0ab82c22100e1f21570584420046fc1ae0b0884028dc835c161108010fd0fa82c22100e1f21f50584420062fb9ea0b0884f2c5c73d4161108010fd0ea82c2210021f21d50584420062fb9aa0b0884f1c5c7354161108011bd0f982c22100a3721f30584420062fbae60b0884f0c5c75cc161108011bd0e982c2210023721d30584420062fbaa60b0884efc5c754c161108031e90e882c221003b44c1105844200c3fc3aa1b2c6447a6c82543658c8018f2e0a86cb1900637e1d30d96320066cb8261b2c64008bf845c1658c81317908b82cb1900a3b209705963200c3e43aa0b2c6400c7b70541658c8031bf0e986c919003365c130d923223cb7416eab24640387e87dd5648c88f0fd05baac9190021f60375592320062f986eab2464c1aae82dd1648c8010ff0ab82c91900e1f215705923201476412e0b24640087e87d41648c8070f90fa82c9190021fa1d50592320043e43aa0b2464018bc87501648c80155904a02c91900317dd5305923277e2e3aa60b246409c3e645d4648c80117f0eb20c9190030f5d5641923204c5f424ed2a46400a3d84d96548c8074790ab24a91900a3b61a729523223e
  | 22 => 0x106caa10da1fe1d20d95421c43e43a41b2a8400a3f8448365508a147908906caa10021fa1c20d95421843ec3841b2a8450a3e84083655080147b08106caa100297a0c20d95420052ec1841b2a8400a768108365508014eb02106caa10021fa1e10d95420043ec3c21b2a8400a5e8384365508014bb07086caa1003964c210d95420072c98221b2a840087e8704365508010fb0e086caa11428fa1010d95420051ec2021b2a8400a5e8304365508014bb06086caa10029ba0810d954200536c1021b2a840087f855c1655080117f08b82caa10023be09705954200c3e43aa0b2a8400c7b7054165508019b6e0982caa1007361c130595420043ec04ec32a8400a7a8098c65508014f301318caa10021fe1f60195420063cb86c032a840087d8798065508014bd07300caa10029760e60195420043fc3ac032a8400a3f8458065508014df04b00caa100e1fa1c60195420043ec38c032a8400a5e8318065508014bb06300caa10029da0460195420053ac08c032a8400c7970180655080147d0da00caa10028f2194019542005964128032a8400c5e76cc065508018bcec980caa100396d8130195420072c3026032a8400a6e86c8065508994d90c900caa1132cb211201954200637b28e4aa2844cd2c541c954508031bf0e986c6a1003365c130d8d420043f43ecab1a840087e8719563508050fd0fb2aa6a11438710f6550d4228536c16cb292840987f87596525088f87c853b4a4a111f0f10a76949420043fc04ed292840087d809da525089987e813b4a4a10030f50276949420062f984ed2928400c5d309da52508a1878e9b2aa4a10030fd97745494223e1f214ec2928447c3c429d852508010ff013b0a4a10021f60276149422861fa04ec2928400c3d409d852508018be613b0a4a1003174c2761494228717b16cb2128400cdb704c361508039b0e0986c2a11421f21b75585420043f43ecab0a8400c5c73d9561508018f0e1b2ac2a10021fa1c65585420062e398cab0a8400c787019561508018becbb9ac2a10031719773585420063db2ee0b0a8400c7865dc161508011ef0eb08c2a100317dce535944204c5e422e0b2884008ec825c165108030f90ea82ca210268f21150594420063db82a0b288400c5f75d4d631081317908b82c6210029b2095058c4200c6e43a60b188409a9c844c163108019b6e0982c62100a1f6177654c4204e1f3a2cb2908447a6c82596521088f87ecaba4a42111f4b149749484204e56c16eca108447c3e52dd9421088f878a5bb284210030fd4376508420061ea86eca108400c9f30dd9421080193a61bb284210030fddb75508420061fbb0eaa108447b2c821d5421080195eed2928421132cba1e525084223e9743ca4a108447d2f769494210801c5eed29284210030bdda525084223d97c04a4a108500b2d
  | 23 => 0x5974204d1f42020b2e8400a3d8404165d08014bd06082cba10029760c10597420053741020b2e8400a6d8204165d08014d904a82c7a10063721d3058f420066db8260b1e840287c8759553d080187acbba2a5a1026ada10315874200572c1062b0e8400af1800c561d08031e90e882c3a1003b44c110587420062eb9ca7b2c8447a6e8294f65909f995ae9396cb210061fe1d50d96422851e422a1b2c8400c797054365908030f90ea82cb210028fe1150596420063db82a0b2c844796e82dd563908070fd0fbaac72111e1fa0b7558e420043ec06eab1c8400c5f30dd563908010ff0ab82c72100e1f2157058e420043f43ea0b1c840387c87d4163908010fd0ea82c7210021f21d5058e4200c6e43a60b1c8400c5f754c163909df8b8ea982c72100336dc13058e420043fc2aeca9c840287c8759553908071b90eb1aa72111e9b2096594a420061eb2ae929484dc87f8758e529088f0f90eb1ca5210021fe1d6314a4223c3e43ac62948450b2d8794b429088fa5b0f296852111f4b5da52d0a4228716bb4a5a148501f0f3094b4290a03e1a61296852111ecbe1552d0a4200c7a43a20b0c8400ed13044161908011ef0eb08c3210028f61253d95420062eb9ca7b2a8400a6d8294f655080147b09286caa100297a0e50d95420052ec1ca1b2a840187f8754365508018f2e0a86caa10029ea0263d95420053cc04c7b2a8400c7970d8365508014bd07306caa10029760e60d95421843ec38c1b2a8400a5e8318365508014bb06306caa10029da0460d95420053ac08c1b2a8400c7970183655080147d0da06caa1002cb20940d95427862f3b661b2a84efc5e764c36550801cb6c0986caa10039618130d95422853643241b2a8450b2c844836550801cd0c0906caa11430f1d174d95422851f420e7b2a8400a3d841cf65508018bae639ecaa10029ba0873d954228536c10e7b2a840087d8790f65508a10fd0f996caa10021f61f32d95420051ec26e3b2a8400a5e83dc765508014bb07b8ecaa11429b60b71d95422851f424e3b2a8400a3d849c765508018eae238ecaa10021fa1c31d95420043ec3863b2a8450a3e840c7655080147b0818ecaa10029ba0831d954200536c1063b2a8400a7a800c765508014f30018ecaa100297a0e70d95420052ec1ce1b2a8400c7b805c365508a147d08386caa10028f61070d95420052f418e1b2a8400a5d831c365508014dd04386caa11429b60870d95420053b408e1b2a8400a75811c365508010fd0f206caa10021f61e40d95420052f41c81b2a8400a5d8390365508018bee1986caa1003175c330d95420043f43c61b2a840087d878c36550801cb700986caa100317dc130d95420062eb8261b2a840087e870c365508010fb0e186caa11421fa1e20d95420043ec3c41b2a8400a5e8388365508014bb07
  | 24 => 0xca400c3e74d82619480187ae9b04c3290029ba0b60986521c43fc3ac130ca400c3e74582619480187ae8b04c3290e31e9c160986520063cb82c130ca400d1e74cc26194801a3ae9984c329003479d130986520068eba26130ca438d5a704c26194801ab2e0984c3290034d5d11098652007a89822130ca40087e87d9161948014dd05b22c32913e1f21d64586522861e3a2c8b0ca44fa748159161948010fd0fb1ac32913e1f21d63586521de2e39ac6b0ca44fa748158d61948710f90eb02c32913e9d20560586520063db82c0b0ca44797487441619488f4e90c882c329003d44c1105865223e1e322e830ca40087d87990619488f8b8c6b98c3290021f61e631865223e2fb9cc630ca447a778758461948018ef0eb08c32911f999c9611865223e3bb82c230ca43887d865c061948018eac2b80c32911f1ed8170186520072ab0e6030ca400e55614c06194871ab4e0980c329003565c130186520051ec2c81b22a400a3d85103645480155b04206c8a9002ad60440d91520045fc3ac8322a4018df874c363548019b2e0986c6a913f0fd96749855227e1fb2ae930aa4008f787584615480187c86bb686291330f10d76d0c522661fa0aeda18a40087f805db43148010fb00bb6862900317cc176d0c520062e982eda18a45087f865cb43148018bee729acba10261fa1e50597420052f41ca0b2e8400a5d8394165d08030f90ea82cba10029be0950597420063db82a0b2e8409a3e849cd65d080147b0939acba100317dce73597420043f43e64b2e840087d87cc965d08014db0538acba10268f21171597420052fc1ae2b2e8400a5c835c565d081347d0838acba10d68f61071597420043f43862b2e840087d870c565d081347d0818acba10028f61031597420053741062b2e8400a6d820c565d08014f50018acba10029e60031597427cc3ec3ce0b2e8409a3e849c165d080147b09382cba100297a0e70597420052ec1ce0b2e8400a6f825c165d08014d904b82cba10031be09705974200636412e0b2e8400c7b805c165d09f50fd0e382cba100297a0c70597420052ec18e0b2e8400c5f70cc165d08018bae1982cba10021fa1e30597420043ec3c60b2e84f8a5d838c165d0801cb700982cba100317dc130597420062eb8260b2e840087e870c165d08010fb0e182cba13ee97a0c30597420043f43c40b2e840087d8788165d08014bd07102cba10029760e20597421c43fc3a40b2e843687c8748165d080147f08902cba10268f21120597421ac3f43840b2e840087d8708165d081347d08102cba10028f61020597420052f41840b2e8400a5d8308165d08014ed02102cba10029d60420597420043f43c20b2e840087d8784165d08014bd07082cba10029760e10597420072c98420b2e8400e593044165d08010fd0e082cba10021f61c10
  | 25 => 0x8018bee731ac9291428fa10635925200537410c6b24a43887c8758164948a147908b02c9290031edc1605925223c9e43a80b24a447a3c86501649488f47f0eb20c9290030fe1d64192520041fc3ac8324a447e1e73590649488fc3ae6b20c92911f0f9c9641925223f17392c8324a447c3f70590649488fa3cc8b98c92911f47591731925223e2f312e6324a447d4e625cc64948a1a3e82b98c92900257e01731925223e2fb02e6324a447d2e649c8649488fa5ac9390c9291434bd06721925223e37b04e4324a447c74615c4649480187ac8b80c92911f1ed8170192520062f39ac0324a400c5d7358064948018dce4b00c9290ee57e1f3019252004aec3e60324a400e1d64cc06494801a9ce5980c92900257e1d3019252004aec3a60324a400e1d644c06494801a9ce4980c92911f0f19174d8e520062f31ae9b1ca40087d87993639488fa9cc7396c72911f5358e72d8e52816a7984e5b1ca400c5e635c3639488f8f6c0b86c7290ee97a0d60d8e521c4afc3a61b1ca400a5f864c36394801a9ce4986c729003565c130d8e521dc3f43cc8b1ca400c3f7499163948774bd07322c7290021fa1c6458e521dd2f418c8b1ca400a6e8219163948018b8c7b82c7290024fe117058e522849e422e0b1ca400c5c635c1639488f4b907b02c7290029ba0b6058e521c43e43ac0b1ca43ba5c8358163948018f6e0b02c72911e5721d3058e5223d2e43260b1ca400d5b704c1639488f87d093b6872911f1ba0a76d0e522861fa0ceda1ca44787f809db43948010fb013b6872900317cc276d0e520062e984eda1ca450c5e435db43948a18ba86bb6872911e1f20976d0e520062e18aeda1ca40087f805db43948010fb00bb6872900317cc176d0e520062e982eda1ca447c3e7659343948990ff0cb96872911f0f9da6450e5223c9e43ac8a1ca447c3c765914394801c3cc6b22872911e5721d6350e5223e2e3b2c6a1ca400e1e6458d439488f87ec73a6c32911f0f98a74d865223e97314e9b0ca400c3e619d3619488f878c33a6c32911f0fd8274d865223e97312e9b0ca447c3f605d361948a187ce8b26c329003179cd64d865223ea7312e7b0ca40095f805cf619488f8bec0b9ec3290030f9d163d86521de2f39ac7b0ca447c7b605c3619480187ce8b06c3290030f5d160d86520062f39ac1b0ca400c5d7358361948772bf0f986c3290025761f30d86520068f3a661b0ca400d1d74cc361948012bf0e986c3290025761d30d86520068f3a261b0ca400d1d744c3619489787cc53a4c3290034b98a749865225e1f312e930ca400d2e625d2619489f87ec2ba4c32913f0f585749865227e9b882e930ca400c3d74992619480187ae8324c32900297a0c649865200537410c930ca400c3d7498e61948018bae731cc3290028fa1063986520061eba0c730
  | 26 => 0x317cc37558b430043fc2ae0b16860387c855c162d0c0517908b82c5a18021fa1f5058b4301c3e43ea0b16860087e8754162d0c010f90ea82c5a180317dd53058b4377e2e3aa60b1686018ec8748162d0c1355908902c5a180e1fa1772587430043ec2ee4b0e8600cd9704c161d0c031e90e882c3a1803b44c110587430145ec26e1b2a860187f875436550c0147f08a86caa18031e5c150d954381e1fbaee8b2a86008ef825c16550c011d904b82caa18023de0570595430247a40ae0b2a860187c875416550d4747908a82caa18031edc1505954300c6e43a60b2a8600cdb704c16550c018becbb9aa8a180e1fe1d75d89430043fc02ebb128600c5f305d76250c070fd0bb86c4a18021f61770d89430145ec26e1b12860387f87d436250c010fb0fa86c4a18021fe1d50d89430043ec3aa1b128600a6c825436250ddf8bcea986c4a1803175d530d894300477c3ac4312860087f855c46250c070f90ab88c4a191e9b20950189430043fc2ae5b0a860387c855cb6150c019b6e0986c2a18023de1d61185430043f43ca6b24a450a3e8494d64948031790ea02c9290028fe1540592520045fc3ac8324a447e2c52590649481393cc8b98c9290032759173192522851fc3ac92a4a400c3f8759254948a187ee0b24a9290030f5c164952520070f982c92a4a400e1d3059254948990ff0cb94a9290d65be19729525226637c32e52a4a400c6f605ca54948018dac0b94a92900353cc17295252006a6982e52a4a447c3e76991549481347f0cb22a9293b30f99373552521843ec36e4aa4a40087e8795163948774bd072a2c7290031794f7058e520045fc22e0b1ca4098bc845c163948018bca6b82c7290ee97a0d5058e5200c6e43a60b1ca400a5f854c163948019b6e0982c7293a31798f7454e520152fc32c6a9ca447c5c7658d539484f0fb0db92a72911e5ba1f7254e520145f424eda1ca409c3e645d7439488f2d904bae87290030f5d564d0e5223cb7416eaa1ca40096d82dd5439494787cc8baa872910b1798d7550e5223cb6412eaa1ca4028bc87591439480187eeab22872900317dd56350e524a43e43aa8b0ca47187c8754d61948031e90e882c3290029de1510586520076898220b0ca4008f787584619488f8b8c6b9ec92911f17dce63d925223e97324e5b24a447d2d649cb649488f8f6c0b86c929003539cb30d9252006a739261b24a450a3d87d92649488f87b0fb24c9290028f60f649925223d1f416c9324a447e2e82d92649480147d03b24c9290028f603649925223c9e422e3324a400c3f645c664948012bf06b8cc9290ee5720d719925200537416c1324a43887f87582649480147f08b04c9290e31e9c160992520063cb82c1324a447a3e865026494801c3ec9984c92900387d9130992522843f43cc6b24a450a3e8498d6494
  | 27 => 0xfc3aa1b12a800a6c8254362550014db0a106c4aa002ab61020d895400572c0841b12a8008ef8758862550018b8a6b98c4aa00237e0d71189540146e41ae2312a84787c87540625509947908a80c4aa11e9b209501895400536c2c40312a800aad8408062550015cb02100c4aa11f1b14a72d855428e37b2ce530aa8008f78758461550050fb0bb86c8a9bc61f61d50d91530162ebaa61b22a704c3d75d926454c0117f0eb20c8a9a8e8f61f64951530061ec3ec92a2a703e1f30d925454c01c3a61b24a8a99c61f21971951530143ec2ee1b12a6098be84dc36254c0117b09b86c4a98da1fe1d50d895378c3ec3aa1b12a602c5d754c36254c011df0eb10c4a9c0a9be1562189530061e2a2e8312a64787c875406254c019b6e0986c2a99d30fd9574185530047bc3ac230aa674a77855846154d5b5af06b08c2a980a2f211705974300477c12e0b2e86008ec825c165d0c130fd0f282cba18029760e505974300c3e43aa0b2e8609a3c8454165d0c018f6e0a82cba18268fa12725974326636a10e4b2e864cc3f411c965d0c010fb00392cba180317cc0725974304d1f424e2b2e8600a6e829c565d0c014db0538acba180297e0d715974304d1f420e2b2e863fa3d841c565d0c8f0fd05b82cba1beb0fd0770597430062f986e0b2e86f987d879c165d0c854bd07382cba18029760e70597430051fc22e0b2e8609a3c845c165d0c014df04b82cba18029b20970597430061fc22e0b2e86f9c3c845c165d0c018df04b82cba191e1f209705974300636412e0b2e860086c825c165d0df387e82b82cba18031ee0170597430062f982e0b2e86fa87e871c165d0c854bd06382cba18029760c70597430070fc2260b2e86f8e1c844c165d0c018b8e4982cba1be387d0530597432152fc0260b2e8642e5b804c165d0c018bee0982cba1803175c1305974323c3e43e40b2e860087e8788165d0c010fb0f102cba190a97a0e20597430052ec1c40b2e8600c6c7288165d0c010ff0e902cba18021f21d20597430051fc2240b2e8609a3c8448165d0c010fd0e102cba18021f61c205974304d1f42040b2e8600a3d8408165d0c854bd06102cba18029760c205974323e3639040b2e8600a768108165d0c014eb02102cba18268fa1310597430051ec2620b2e860087e8784165d0c010fb0f082cba190a97a0e10597430052ec1c20b2e8600e593084165d0c01cb260882cba18021fa1c10597430043ec3820b2e8609a3e8404165d0c0147b08082cba190a97a0c10597430052ec1820b2e8600a6e8204165d0c014db04082cba18021fe157198b4301c3e42ae3316860087f855c262d0c070f90ab84c5a191e1fa1f5098b4323c3e43ea1316864787c8754262d0ddf8b8ea984c5a18063b61f2098b4304d5642241316860387e87dd562d0c010fb01baac5a180
  | 28 => 0x4001002802000000300180040000110000000002001003001400000a0010000004004000800800600d0038004002003000800c0000030000010000000003001c002001004000000a00000100100000010010014004003001800000002c005807401c001001000c00000b0008024002000000000c0000000050000000003000802000200000000040060060010014002000000801c00000300500300020020010000006000002801c0000010000000000002002005c00200100000040020000008010002005005002000200100000400000030000004002001000000c00a000004000c00000100100000080030008014004003000000800c013002000000a005007000000000000080000000070008008004001002002000601f00100000000030008004004002005804400a0000008064000001001001000000b002801c02200300380000060060008020000016000000004000300a0004042005001002001c00200c804400000200380000020050018008002008005001400a000000000000400300280100060020008018006000001000401c0030000004014019000000001000000580200000050060010002005003000000600200080280040040028010004001001000000800c000003002a0000008004002000000000001c008002802c00800b002001c00400000000040040000028000008004000800400400a001801c014000001000000a0030000000004011000000400000d00180000140030010000004000000000401800500100280060010000000070000000000800000e00100000100000000000016005009000c0100050080018000002000003801200000200000340000000000000001001801c000000000002800000100900100460000060000000000000000800a002000000c0000010000000000001000004800200400000080000060038008000010004800801a0040028000002001001801800a00c000800c0120000038000002004004800c0180000000000014007001800000000100480040220060000010000007005802c01000000900800000040000000000000003001400000600c800c06200700000040000000008000000000003001000400b001800001e001001000000000004c5e422e0b1ca8018dc874c163950019b6e0982c72a00237e0d7198a540146e41ae3314a84787c87542629500147f08a84c52a0063b61f2098a5400537c2a41314a809aac84482629501317908b82c52a0da1f21d5058a5400c7643a40b14a800a6f85481629501355908902c52a0063d21d10586540053bc2a20b0ca800ed130441619500717b09b86c6aa0031794f70d8d540062f29ae1b1aa8eca3c8454363550854bd06a86c6aa00637e1d30d8d540052fc2a61b1aa842c5d754c363550019b2e0986c6aa00e2f61370d89541b43
  | 29 => 0x8000002004000000c00400100c000c000001001000800000700100000000000028024008000000803400000100780380000000010000026005001001c01a002001803001a0010030010012000000000c0020040080038000006002001800200100080180040030018004016007000001000000000000080000000078008002001009800401c0080000000002002001000400400700000180020020000000010003000001800c021001800000e0010008010004001000000c0000050018004002006002001c0020000018010008011001003000400200100000300020020024008000000001000400a00000400060100010018006001002800403000000080000020010050004002000004800000000200580140100010030000000004000000000200400500240060000048010002000004801c000009008003400000f00000000020000008004012001000802800800100200040040010000050000024000000c0000010080038000002000000401e0000020038000007001800c01c005000000401e001004000c066001000000400800400080000000050010028014006001000000400000d8000000000000807c00e0000008018000008004005400400200380080020000018000000004000000401000e0000030022001002004800a010000000000600000000100000030020004000001000800000e0120000014014002001004002200000a000c00c002002002800e002000001c006004000806000a00000000100020000018000000002001800c00200e0058004006001000000000000a0000004000005000800000600100000080040000018000016004007801000000200500040100030000000006004002001000e001007800000a00600500000020000060000002000000000402200300b8000010005001002c00600100000100020040010030000001002800c002005002801c00000f0000054004000000800801400000200100080000090000000000000800401e00900000040000000018000002000002801400000000200140000020000008000003000001c02a002000001000201a0000008004008000009c00000e001000800e0180000000004001007800400000100200080060010010018000005000806000200200500000020000000018008002002804000600000080040000000028004002008000800000800600000000180020020008004000000800000e000001800c00400500b800c008006000000001000600100100040000000008018000007002000400000e000401200300d8018004000000000800c0040038028012017000805800600d000800000400300180000020020010060000001001000c000006004000000001200080000000060000008000011000000c0040000010024006000000000001400b0000018
  | 30 => 0x1c0000e8e47f800122acfe1ff8000e44da077e802400073777721fdde8c5700019cd674501000000036c000021800000000000000000000000000001368c0f00035ccdacac2572a770000efe63413a85d6e6e02a8e2cc84e4f32a0ec16a88603e7b1392906530001b05232bca17a8001e786576ae2fdc0001a611a2855c463264cc365c95058524b3828808000073376cd740005d10001c584312af8001dee00073aacb1adec6e5ebaaa031c34d693142d8ac148429bae57228244a69eb9714e11343800000000024480000000002ca9af516c62400000000000004f680000000000000000000c534048001c8a2c367e04f800000000000012529b10f980011a66e5411aa8527a8be23f14358b853c61b00000006581bdaac049e2e611f30cc0003af5391e400005b100016e4ee8de70000000f9400000000000000005ef086c00000022531040487830000001cb200068b2ecd9d89762a58001d4a00009b09d550aa685e7000119200000000000000001be00000000d90cd80000000000000000000000000000000000000000002cec9a76a8000eb83712d0256cbe2bb1493b1a80000002ac96880003d40a00001e36bc2185134041e9570000cbd76aa9271780008f259d3ffae68eeaeae26f000000083e521b0480006a30002cec47eda2000000000000000000000002470003c7c00036a019a32c80032a00007e00003b14f60ff06e01285c905605f4e5a08a0000db8000000039000000000000000a800003000000880000000000000cc160280019da0001e227ed00ca7900000006ba5d0580af95d40134399246800095100021d4b8a0000000000538ac30001764ee44940000001a3269915facd0000b0629ebcf4c9ab4865e29c127c00177fa13d8a424a00000000008d846aa77d6ac8e316e8001e164f3337b6ac2c246e03c8bc13c8e2536926540008340003258000000000000082a6b600032b082075161e8000fb00001ca0001c4e4ec76ba6b03921882358000000000000000172a00007791200000000000d0c001004800000000a002005800000b001000800800100000140180000008004002002012001c00e00a002000400e000001003c03400e0028000010005000002000400d00280000000000000090030003000007000400000000040120000000008002005001000400200300000440000000018004004000000800000400a003800000000100200000020010000004006005000001400c00a00180080020010000004016001000800c0160060000018002002000001400000500e8004002002001000000000100200000080060000018004004000800000a0000098038000000001800c00a000000000c000003001800c004001000002c0000050000004006006003001400000800280000100010010008004004001801c00600d
  | 31 => 0x24aa4b110430b3fd0cc042c00000000019e80002192e4000000000000000009d70003044000d3c0000000c260003f000000007100001a880008d63e30001cf22f65b9803d7e40c6000337046016036d34c800013a303151459ae3627a0b149087f31d380000000000e68000000aa43b6219c8b817f3648000000f1e729000057a38e000000000007478c2ed80000005512ff4b80304000386000000000000000008112980000000b1e0002704000b020e300000000004268001bfacd0207000000000078d00010a200000000000009e6616952173683b55fb83d1ea64e092800000079600000000007560000001a620057a2a6f45ae0000000000000e170000000f1400009b807800082f6bd3634d900000fc800079014a0003d2c93eaeb0002e105542ee000325c8925af3d8b1c85fae786af01455780cf68700007ba4dc5d5b7900a67a50000000afc00000000001a4b0053f1c5c00019c1281380000000145370c0003f008035182dc0000000000000e562dc0000000000000000000000032d9ee08e656950e1081cd83b4000198400080e0ff0000000a8724b9f04edcb9627c37308140004172b3400000002b89ed4520e847886c5abe29d053a45868a030425bad48a2c1c5489078920ead2e89561246f173419471ac0e050d58f35e0eb1f677aef05a21a253e9ca85fed9836f863da6864b5480c6c1aa27d5b390b54228a2000000131c379000284000093700000000000006d387bc00068176f1d7c000e16102800000000023a000145e0000000000b9a00072020e000000000000000003ce15684c180400007b92d0000120000251054220a5f9b5204bc0002ab000000051d103000000074a000340cb8246a1bf0000dc6b7f65909500942ac52d8f8983601100019b1e8ef466c38c3c0000002221f3978e8b735686b8b9262031a855c1d60e03d0245c000f030001f35d38cce2cf00000009fd00010e89640004222c7467e4b63c91805556a2c3d68205d263f50930f30e70ec63f7a9918bcd3849990e4f7e7e842aa7b8000c2033400000000006a8a8f8000000714a9a5d140006ca800036487d1058001c0e00024780013e201b000000000000029f00006720000000c1800069a000014964e0003130000000e7b1c300002ee0d82c20001da6ad20a59d255f244f0559f6d380b477749411ab28310001a400001ac0001641148ee60f33c2800038f13026ec3b20000003788000f4400000000005256d4000117800000037a8efa5c73ac226867800000014152602a22832ddd7da8f863800011680000002c0c6ca81410c99ed68200000020e507a00000000011d60000000001cf85f4628103c0009cd61f0000c7e85c4c20000000000000229d1540a80001ec0c1ef000002c240000ec5e2bcd4000000000179400020800b05793a0335000
  | 32 => 0x4000065019a3ca31647e63d24908000b8ceb144303cc0000000002940dda5aa6d700000000004bc0001bfc00004f25d00001dd74f8001be2bda000018ca945fb0000001e1e000272b41c62800000036d08bad3373800012dc3f91f781ec71800025f2a595dacbe2eb2efdac60fa74296e9b0a000119337891815900008ed2d00000000001638dd03aa8001ae2311180afbc9ccc0a00017a4000000289b4353a60000000000b788dd3a687041ba8df0ff960cc808a04540e1000061716f1f21d0800738580009c6c0b47ca604be01aa62aaa380009a75c4a5b012ca2034f8034000a5f4ac87d4b480000000000000000796800103a000066000086000073bb5340009a020421d174ca656de3cf8600c2647e99543b094b3bb344d974e81671a1d83d4000169104d768b5d28a9f5c00019450d1d1170624e15780e930af0c00034895a21af19392b90a88c73c2baa593a04241ba3d19960000002759d1e0006bf3898a74684000000000043f0000214bec5c31a88001d421cc651836925e00000027e596233a0889b780000000000c64000d396849ae184e5cf1aa077c292e0605b15b964270e0002f4d34800044900005acd4267d0000000e0007daf98a6600043228f00000004690b64a54aff00000000000001afadc9624000000000000000070db241e6ef4031b8ac15f600000000000008cd0819c2800000048f00009ac00000024157ba0222bc993000000000001a5b9a07159302fd808f0e5ecbc44c180000000d3c00000000015d456e62c0fb00000006a71c0ab6d3eea820000000de4b42212b1880008793b584045909521259ad0000ee42c7a8c91a2b6f3af024161c7430000b6d588913768000000081200012a5b94ae72c3055410e65000000c85e2b8b0d002e92f8d8e1a131dd2548fa39d0eb80cc00019c39444b0a8436389fd5c66d84270871a542ca00010cde2a000000000000000000014a40000003b40001a6a00067722e16540004d800000000000002d484622df5c980008d06a100035c93000006a49625c420000f580002d27e1000000032000000000000009c41760000000b4f5d9000000098c42bbac9b5e6ab779b0a4f00ebd013928994a23868ab768ce00001ab3450000b330001a3136a5b64c88000000a196802c1da7e10b211afb00000000000000000de6587800041c6ac0001c9c078a050001af820a3c64f9000000000054c8000cd4b6a00020fc97e0aa65fa5080003c338a80000000006f2a2c16b8cf544995b107841752c9d9d84a9f438a0ea932ee864518508000ce528d216802e000000000000000020100009788ad0000000bae00017bad008ec0416140f6d70415d00018bc36e00068f9b2cf220005569cfd91e0b1017a9e1a30e800bd80000fca9d3de8c7c0000003948e914da3ec0000000000000000000000
  | 33 => 0xc24530002fade508d71a83348000f31192286d13c622668929cab83e819091b59883a054a0b80f843297840001de41a92d7000000621100026e96267655bf0001c9c00000018f00000000001cb00007950c6a43dcfe3f800000000000004c995e8dd0df40000874000e1a2c080000007da00006b4000000009a71d4bc25600002e0fccd8c000000121c1f05a60000000d24738acd5afa305518af819ce78734eb428000aae000111447850f13f02280000006a638c80b294f00020d4b3ecd824e00008061e13cd9c0dc8e6a9000000000023700000000008210000000f766690392621ce600066db019b9cac72b90000000b0b6a80af19ae89f44a18ac6a4c9f79c202d5a02010000238cca28c264148000000064199900000006069d008860003ee9a4d5942867620c61a22eb06aa86f00000000002bd144277809cadd13fcd7c5888001a6c3eb01321b9942ce4663a96052e0be4aa230529410700037b853e7d000000000000000003bf00000120002794ba8de3000069c0008da42f103009a8c055380012285781f703c4000000000312c00000000000000000000000000b5000042180000008c512f80000004b555da1c400086644ea4b5b4ac9815b102cd6e4f50fe30c86d09ca4142119d187a46d638813de7ed3712898588cd35e413f12ce27871885cc47a6000002ba4a280001ec987d176d86562b81009c8911ec00000000002e13d08c9200000027657f20000001448aa40000002131b1200016021b0eae00057b81f02561191528c89c567f0275a069cbe000000153876ea347933a2051a899022a4e9e2654276c0e9561a25307fb850d9e0000001e698940004a98e4d83e9a567d80ec44cde072f10b8278b9716c0850a560000da15d0d7e6e44e72f0427040d5bc158de567525363a640000005db80015d4eb65603bed7fc0003c30000780000060827c00017a59fb5a5b483dc16982ecea8b505ec1b0933a5b021499e84b833314c1fe12c8f193dab101b6c0006e4800000096a0c039d939200071c800147edc0664bb010fc2630003cecd9a06f615b931740a76000000135a00049b07880f499f1db33884860006798000a3e96664d8000000000516872025c22e0000001502e9734283894d60000000000000af30000e8c51e0e976680000000004f3b5686ae0002f4182065c0000be9589282000111ac95110ae277c000009829118936fce0e71b0f38d704ceeac0ba1d2158c6f70000394e7a8dc290a2f5ace29b2c71e382a077c0000000c0e6410001384aae97500014b89a8d0f2d594288e2e3515d0001d9c1f15ea83000008ef0000168ef4b180000fd1632000323800000000000036e80002070000001902f2e79f8e441720001b9960070e52267012e4000ea858214bd6560006aa344830aa3b3d53160afe4671dd03b400000072
  | 34 => 0x6880000000002509cbc3a8b5929a80011883d50000000d1e0006de9e98e04c9e6c4178d00409143129545aa00040600012000004d4b744d36a896358e758340000e38000e2c8af4aaac59a9c0002533a3400000075d00000000001e7b678000cb70140000784ed26039cd400067f07e8001990dc70a899110387ba61e1dec000236706266969ca37476282dd369061d58cd85d4040437a225dd6bc30003b099e2e3364e1f30cfa42b34514d80001c20510000000ee04419720f880000002ae98d220d2f7000010c3f25fd80000004cd00000000000000000001590f0200009ad8f60000003be4986cb90001238ce40000003c14000cc2231800190ea5d0b8bb7d4a40000003210900ccf0000a90000ddc00012dc0000005279188cc439053d1ac43aea564508c2400000056c935cb6600000003847b40000003cc945cef64c835fcd2200066faf3dd860f6246b1b0a6e66b00031b40920001480bbd5e450034c09e53f0d7723800019ec0ea3b19895b528732e203711d2186000311844203931c0a59dd04550001a9828a3605d7217d8582a324123dd8fa9070310001d7849a5f70ff80001791b21c3cf7c4466279d65db4de17250d4c4ba00016080000005de05983c0d540f90001ddc32416c00300000009db0002c5534c11068d2d78770b2061c800059c16d4a6000013a0001638000000682000252400097300002b55cc00072e25c400008d00000000000002be00010109b82990000000000000370400065e000308c0000002553c9405c9e00501eac0001f700000002c489c0002b5400000055313257029434c1acf5bbed01000000183c0000000000922e661bb966d72814c0001bb92c0b8762e90615463d319a18d0000000110000045e2440001cb40006e003e80016362f309eaca41865d320307d0c3a4c12842428e6c01533caa7968ca5424cb4bc0000cd4cc80001f09220000001136bdb000179016400000000012b42612c900000003cb3c480000001fa37c96ec8980004d40000158d9900027e825e9792583aadaba19f3a709b5900e1d04d3169498631293240411800054000000000001a48000f260005baa8ac000ecb0002d2cbee0000d994c53440001263a8c7524241f207a026431776510f5d24cae0001f0d7a00006001b4c0002950150001156d944812fa40000000c98001d660000000000000000000000185c0003cfa9b9c7c0003d08248000224000000138ccf20003760000000141a87c0006fb1c2862dbaa14f52200000003d11b10001b14e632ee000056268d00027480000000000e08bb67f40000001a46bb06b800000002bb00000013040000000d000000002a39f2c00000000000000005392ccb3e5b46df647735d40004ee0003b3cba44a00052fd00000003cf0d280fe05600000007760ca10109440005bd5b2ae152
  | 35 => 0xb2234c01280000000002f022cc000d4b2698001d4800056a3558000e222b3b3ac00044d16e169db9634436a800000000000020b13f8f2018f1510ac88b235e3085364000000000092663e4f400000000000000000ff2f04000201037c26e232a3881fc0005dd800102e00000000017f81c30ce87a42046ef1b1ac884e8a8f3d3a8cc512c82122a39ca481dc37526494943072a8a174bbe58a63380210448e66eca01c7580de5d790500180002e58001b200004880000f8abe47a18629e28a9b00000002521472a800000001ec00000014608d913285a13bc0001ef800000000026e9da40004b156f80000009263ad07400000004e280000000762610000ee6cf82d4b94c9a4a4b527285c318b7177537b1b8c000242ba45d4c4871c682dd91a0005fa80012fc01a106117c8d8000476b8380000007638000000ccd507ba40000887000000000015c0a0b84c1881bd0000000000000000000071000000018a00000000000000948cd6306800156c1fb00033691620006d995c000098f0000000accb806a2305d0f00f23048315dca7f218b373d5261d50878cec7eea4d34305340dc1045c3229986a4c4023168c0a055d00015854e813f6a3b11c996d3737480003947dc790a84d08200000030243faf2a5e69d1c000dfb71a000000000015900000000000000e25390ab33c6a05486c00000000013c20d10498000a2230e000000168a0001b39530ea086a14700000006b243480016d8bb90000000fbc0005c7000022a00000000000000002f38000000000000085c2c600000018f400014301880000000006249dc400000000000000000001018c680000000002a2021073b1e080000000000000000000000000380d1a8000000000000000000000001a088b0002cd8f800003730000d502721128ee4c946050000001c8696b33380000000000c22708df809c61a31085c20000000000000000000000059e15335d8000000000274a1b4000a241b0b374fe21da2710001230178000000000000000022fcbfe0004a2b6483a611300013e4000000743b5e4000b050000fe855c000000109c000eef07a954de4800074f0001b1e00000009240006124130001792000000000000000027d38c0714ef14bd22100000a512bb4811c80000000001bd20000b81f2400016f000276125c0000870000000ab7550000000000000000015ac06d0000001b600006c0ad88d4a6746498a6833296517d915cf6e0002969ce5c10881389a501a3c45662a258967cf0947f3b715382225339c018f02b56260209738ec528db974a044a31742db9c6edd63b13961d928963570000fb277f43d82d0000ba42d30ff45f2a7310a9261d900005788000258a4879635902acb8c69080000008ba37f0000844c102450000000d7b398ba68f1000076ea4c483e0006d6b9907d2db97
  | 36 => 0x50711a40000000c4a028000bb81d10a151ec9240002f31d9800078b21240008650001a500c20006960efd1f84f018e000023437a0002ea800073050a0178000240000148ddc47d40951e04de85a175fa8d94447b4394096867ca16407a94d694000000000183200030ca1141600000d800000000000002330000d45000000000000000033a8000bdc0000000000b490000d2d74e00055a8001914cf71eb05f1c24c146c98000adecd5349000143c000000000166274b0000000f725190000000000a07552982c000d0800023208fab990000ecc0009be2300001ada00008c0dac0009cf00037ad7a467557e0000d00da62cd0000000c8e4dca23d96c41200024d114a98634b9d80000000000126dc202c94f80000452a380002ac81060000001b9c00000015c2570a1800015000000000000c1bccd6b660475f39b5a4a00009d9f940003755f3a805a1869e000000078a82b21a21080007e217c2c202d45030000000000e9404a80000001910ef1c206185e134a8cc8606204000000075a00000000000004df0000001b36ba500027743962926c5998c0000004bfa6b89e4c6365e8000d5e0006dd9c441ac00022c800052852c5d60b1973c0001242abcc1c0000000000412ae4000244499eb6b66631f93c672647919808f60001268000192df30e90001aaeb6d03380000f05ed61d0000000000000205800081f46700006d855e00008a17c43f102e800000000053128200000000001ff4000cb05238acc0000003148dfd774000000000000000b4df800087cdff1840000096472724800000000000018400000006ad8000000eb4000022c00000000004840006770003cd067a00000000004f4df81d30c0981ca181b4846c0006c00000f98a9e000000240c0000002379fec0000003a325410c642f08332896c0000200b9e9b90e824f980008a000000026dc00000000025387cec714168cb49ec95d4ed0db46460003fa80015d0d6b50ebce5d16dc4000000000000048917388220001e50b3021487a252a8d4128cca00012cc000000420000072e47770aa4ec0008f00000b68000a77776204ca12000119b8a8d10a8a5c69c35a82dbe3b08040bf455a7009bfce324090eda5c8c22341419a624000b7c268a7d50b611e32d32906de6b019b800000041d50938a050400060a8000000000000272c9d05f869800006bc0002f5a57d1c04423f20e716ec0a600033a40000007341ef0000e1e0000000b586d100016700005b730a0000000000654aa300001220bb136d78ce090100e54000154528ba593a8f360e2a18400015a5ac10648cc1d607e2431a524d90279fdd28e00048f80005dacc3442800174600000000009700000002a68d66565000000000098737c2ca15964ca00000002380000000000cba0a400032cd730b9d00016080000004d781dc
  | 37 => 0x9346852418120c33c02d4bd9a7123802c41512ed4fe37221db645ddab7b3b5391000000033c27315163d017219b8aaaa28000060854ef0638e80014460003902cb85686db43917f9b54b3c3893230a2c82529400000000000002df4000ada4af000057cd846e929d40000006c0225c00088d0000000a20d1b57b19150060006eb8000000000721000000067e0002b7400072b2f621c0cf8def390b41800039b0000000000000000000000000000000017e00005af800050e0375e8ab4cad698d65d80001aec6540f2d983da5870b20000f1e00011636e054c0000001fb0000de80d18000000a630001c68000a2769f0000be41e50000001aa600006100019566d900027a400014e732afd800056d11380013d4000000116c896b884708a655e08687173c052de9703bcb7c000027038f1ff0916aac3c109bc7001354d582b80000000002bbc00000069e800000037800022b0a80646538b0604820000000000000b0c5df0ec9e4eafe0001319806a4142b11fce98c2a36b80000e600041900000006150dc399dbea0f43f495ccfd6d2e24900000003923109338c60e57482023c0007041b3189c350742596ad90d120000001b8582c8000000000000000650262d9cc000000000030e00078e9658fec3a13b312748f86c608fa32951abc00e007114f8ed954bab258e64da0b9342c4e686b1291c18e825385883a9cfa6000000307544a00027b800024e6761cc2434a1c426361a984be603637822d5036b5365a1bb01beaf52bb98617a8ce1350139000000072a2de8ec88590000001ac255b3e39a2c0d8801730a98000000000031d18f40003788071aec00000010e00000000000848efc0841ba14d000000043e00000000000000d39412e3b0dd00000009200002da47d4cb502dbd2000051840c00004ee0000001cd0b5a0006fb8e6800041b10f873d48c568301203569a00068e1badd549d10000001bba2665f880006ecc3b2fe2b84042c510000001074acc18e8001ac41bf1ad0000000e7e72838358c0ca7741a064d48f2f413b0891146dd0000001a760756ce90589743fb09888ac8bcc7c3918191b0630d59ba0d80000002ec1c91e820000000000910b5724f02f5278e243a99a58d880000000001e44000000000140c437000296800032b0003808000890000295c000aee134800000000000017f40005da51c80000002cb61f9755df458c1961ae4f660000f90000a2e0656a180015f400056c00009587a235a9b3000093873480000002886fd10842ea8d012a800043c3550000000c5caf80000001db60006ef2ad19fa0000890000fce4d530d85f8030000336badc00073c3ea90692125e60cabae00007ee0000000f080000000a4c0002a92f7bb5990c000000000000048653dae3c00002b000204000000010808a839c64f189a4ac000c44
  | 38 => 0x8086aa18e18000000000000000057600000006ca00027ac75093f000000000000000028318629e200000000000003d917a93380a138c0d183c60000000001e5272e645800156200004c0001ba83257230000ca42b92028db8a92000567b935a2eb51000242c00063972d9eb190ac132600000a9a97752e1c94ac052774e93f4584da14a30c800b80d30848ba43dca0323c2808b684521ccb8e938622d000000000000000000000000007880000c9008825e9184000000000000148097d000045d98a6fd71e97294de92875db5b00d0f123db0265cc000023abc34000c480000000000d3a00025b4000e7200000000006fa7a48000000bd649c80000005886c13b8577a00000000005ce00000034a00000001682d0c0000001a434b45e4afd637913802800042c00000006f60000800ede03f3e88001cd6000000000148ab0a000247400019600000d04740004d080008f48c25b4211dd8206b6578000000b1a61c15c5c3289855c9ff96723596060001c3824600037b54002136da80005c64281f00001660bdf12dab05e60d9c648a3cc00000002c0000000d02000000175a68e737964c30200000030bc4d40006821d7595063a64a8064b28b63656825d2b082949290a87da8db1cb3020000000653000000000042803512c6a6a2e63c7088e00000002240000000000000000000138800000029e0000000e6627c00023a000000400006617886434470001d5e000142101cb30d6800013b4ee0e627919d3c43076d44aaf84000c926448001aca88c00006ec5560000002a61408cd93eb0001492b610d0800115200000005106fa239612367d7505b50000989b6412d3190964c5a67100033a18c871c2aa0d6c3a20a355f1314792df200e8e0da0a0385f50001b629085ad2e7c04600072ab82d89a4e7263a30c7ae2f474c059953e0025a200395707013d18120f2edd3257affda208205b823ec0009b30003714e8a7d264c98ec00087713411692acd27000000133639e000000034ae7d2a30000b2e00054ab319ab0d5200000012d200017f322000000000016f941a5f9266000000078b00000015060000000000000000171000003e1240001b1400000072085493fe0000000d6000000022a2658000ade0000000a76000000000165e05f00012b5bf27a979d043007c0cb633000076a000000180c000b2311aa46d1ca651000000036abfa1cf8691886000073b53db2cd40014b0dc00048100013fcc6c51e00000015c058b000000000000065c1c15a9465f32c80000001e4311a33cf50e7446309d9648d2b51d0ef41dc5bf2778000434ba100000005001460002f8c4c8bcb000141c07a00005e000023a0000000f78000c452c694fd5b83e500000013280006781e300009bc1fb02a48b004721612acc54a0a424317d36c5414571cf8000d9a0cba67
  | 39 => 0xee72b5000062028149910d40000006ba150d8eca422203bd4f3270932b1ebd9fe0006008000000d6a1f09071adc00000023a962ee893673bc17d08b918ab1d418e0003adb708000bf83ef9829e9400000024d58c26f509998589b05e20af86e53aa79c74a8000000000278b8e0aec0af12102d54cc26c0000ef8c3809b66a0000c66dfc66036dccb8a3d42505951bce3c4402c50afaea233313ed6644645bc9bcc7c671f76a2aa85f833108b16c93146d400038b4000e6a4fb15ecbba34763f838cfc6e3f2d280000002e55d48338100e1f3f51b402460000000000beaace00030c18f2c5b6b33b8d57a2a827f201567061a7259e7400015b16a00003c044168e8f1d6aa0c83cc01a945416b4d5000000000055480000000000000000000035000000087861e6552b5c77828b06d8001928d7
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x84404000004080440200018040030040c202800180000180408000400002424143c242c014599094d70d8d540060be10825c165d0c0182c8420970597430060bd04825c165d0c0184c82cc1705974300513249704c165d0c8f82c72610205974323e191c98108165d0c8f06c9261e105974323f03149645cc64948014599094f7058e5223d0b24975593439480143691d91719925200507e5d64cc0649480141f97591301925200417662635c363948014599098d70d8e5200417a6063dc163948014599018f7058e5200417a60635c1639480141d940c576d0e5200516640315db4394801459909cd60d8652006075d283192619480182e74a0b6098652007445d1304426194801c51615c1301865223c1ba4a8754163908016519118130d954200594644604c0655088f42c92502769494223d0ba4b50dd94210801c0f30dda5250842007034c376949421088f82f85dd952508422860ba1f76149421080142e97d43765084200703ddb30dd54210801c0f764c375508422860ba1f761d5421080112d981c0755084200549644701d5421080142c9758075508420070a1c1601d54210801d08704c075508420064a200755c54210801c51604c171952510051664253dc16394401c51604c17194a5179616a1570180635440182c4221d5058b4123c1ba4a875416390401c61704416214a41007904c1105885290401650964c110d95410050ba52219cb655040182c849c920d95410063421970440635040103c9660175d0d410044b249805d7435040141c964c175d0d41007444c1105d7435040112e92e1f65d0d410060761c63197435040103d981067694941007144c1109da525040181e7660c74949410040f66276d0e5250401834819d943949410050b249409d85250401c513044276149410060718d87d0c525048f8682060072594410060be10825c1651040182c8420970594410060bd04825c1651040182d4120970594410051324970cc1651040144c925c1305944123e0b1c984081651048f86472604205944123d0b249655d2521048f06c9260176148410051664353dc1658c401459900c6769493100417e61731cd658840160c92543309922100583249504c264885eb691938c1105922100784d41304416488401e11504c11059221007844c110592528840122d980826414a210050b65c209905288401625910826414a210070a5c0209905288401c31704416414a21007844c1105905288401650964c110d95210040fe61741d365484014d0974c1105912100e3421d3044164484018d0865c11018d2123d19249109da5248401c51304427694921007144c1109d8524858962890590521092123d19a4b50dd92108401c4730dda5248421007114c3769492108401c4776dce524842100711dd873949210848f86785dd95248421
  | 1 => 0x268914800c1dac1a98002aa4228a1f3400021c1895360029249e000034898f8d128004a5b5a3ae030023000007350e0381b38000378038000680002b801b1030000c992f80251412172d08801300108797a6330ab1a18f04280ea7062899919a299d058816368001001fb0a0112cb1169c959ea0850ba10b13b2af00372da200a79b8d82b22eaa2b0241
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xa00002c21a11c1601d54210801680d08e0980eaa108400d08645700826414a21
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x4
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x209
  | 6 => 0x20c
  | 7 => 0x20e
  | 8 => 0x1549
  | 9 => 0x5
  | 10 => 0xb09
  | 11 => 0xb0c
  | 12 => 0xb0e
  | 13 => 0x1409
  | 14 => 0x140c
  | 15 => 0x140e
  | 16 => 0x154c
  | 17 => 0x154e
  | 18 => 0xb49
  | 19 => 0xb4e
  | 20 => 0x1449
  | 21 => 0x144e
  | 22 => 0x289
  | 23 => 0x28c
  | 24 => 0x28e
  | 25 => 0xb89
  | 26 => 0xb8c
  | 27 => 0xb8e
  | 28 => 0x1489
  | 29 => 0x148c
  | 30 => 0x148e
  | 31 => 0x1849
  | 32 => 0x184c
  | 33 => 0x184e
  | 34 => 0xbc9
  | 35 => 0xbcc
  | 36 => 0x14c9
  | 37 => 0x14cc
  | 38 => 0xcc9
  | 39 => 0xcce
  | 40 => 0x15c9
  | 41 => 0x15ce
  | 42 => 0x409
  | 43 => 0x40c
  | 44 => 0x40e
  | 45 => 0x1609
  | 46 => 0xd09
  | 47 => 0xd0c
  | 48 => 0xd0e
  | 49 => 0x160c
  | 50 => 0x160e
  | 51 => 0x1889
  | 52 => 0x188c
  | 53 => 0x188e
  | 54 => 0x449
  | 55 => 0x44c
  | 56 => 0x1649
  | 57 => 0xd49
  | 58 => 0xd4c
  | 59 => 0x164c
  | 60 => 0xe89
  | 61 => 0xe8e
  | 62 => 0x18c9
  | 63 => 0x18ce
  | 64 => 0xec9
  | 65 => 0x1049
  | 66 => 0x104c
  | 67 => 0x1949
  | 68 => 0x194c
  | 69 => 0xb0211
  | 70 => 0xb0214
  | 71 => 0x3
  | 72 => 0xb1551
  | 73 => 0x44211
  | 74 => 0x20451
  | 75 => 0x44a
  | 76 => 0x44d
  | 77 => 0x164211
  | 78 => 0x21651
  | 79 => 0x164a
  | 80 => 0x164d
  | 81 => 0x194a
  | 82 => 0x154b11
  | 83 => 0xccb11
  | 84 => 0xb0cd1
  | 85 => 0x15cb11
  | 86 => 0xb15d1
  | 87 => 0x15ca
  | 88 => 0x44b11
  | 89 => 0xb0451
  | 90 => 0xb1651
  | 91 => 0x164b11
  | 92 => 0x3ca
  | 93 => 0x155411
  | 94 => 0x141551
  | 95 => 0x45411
  | 96 => 0x140451
  | 97 => 0x165411
  | 98 => 0x141651
  | 99 => 0xcd551
  | 100 => 0x154cd1
  | 101 => 0x15d551
  | 102 => 0x1555d1
  | 103 => 0x45551
  | 104 => 0x154451
  | 105 => 0x165551
  | 106 => 0x155651
  | 107 => 0x44b51
  | 108 => 0xb4451
  | 109 => 0x164b51
  | 110 => 0xb5651
  | 111 => 0x58a
  | 112 => 0x18ca
  | 113 => 0x2cc
  | 114 => 0x5ca
  | 115 => 0x19cc
  | 116 => 0x17ca
  | 117 => 0x15d451
  | 118 => 0x1455d1
  | 119 => 0x144d
  | 120 => 0x45451
  | 121 => 0x144451
  | 122 => 0x165451
  | 123 => 0x145651
  | 124 => 0x18d451
  | 125 => 0x1458d1
  | 126 => 0x44291
  | 127 => 0x28451
  | 128 => 0x164291
  | 129 => 0x29651
  | 130 => 0x40b91
  | 131 => 0xb8411
  | 132 => 0xb9611
  | 133 => 0x160b91
  | 134 => 0x44b91
  | 135 => 0xb8451
  | 136 => 0xb9651
  | 137 => 0x164b91
  | 138 => 0xe8b91
  | 139 => 0xb8e91
  | 140 => 0x18cb91
  | 141 => 0xb98d1
  | 142 => 0x24d
  | 143 => 0x104b91
  | 144 => 0xb9051
  | 145 => 0x104b94
  | 146 => 0x194b91
  | 147 => 0xb9951
  | 148 => 0x2cd
  | 149 => 0x74a
  | 150 => 0x14cd
  | 151 => 0x45491
  | 152 => 0x148451
  | 153 => 0x165491
  | 154 => 0x149651
  | 155 => 0x161851
  | 156 => 0x185611
  | 157 => 0x45851
  | 158 => 0x184451
  | 159 => 0x165851
  | 160 => 0x185651
  | 161 => 0xe9851
  | 162 => 0x184e91
  | 163 => 0xecd
  | 164 => 0x105851
  | 165 => 0x185051
  | 166 => 0x105854
  | 167 => 0x164bd1
  | 168 => 0xbd651
  | 169 => 0xecbd1
  | 170 => 0xbced1
  | 171 => 0x24e
  | 172 => 0x16ce
  | 173 => 0x1a4a
  | 174 => 0x104bd1
  | 175 => 0xbd051
  | 176 => 0x1654d1
  | 177 => 0x14d651
  | 178 => 0x1954d1
  | 179 => 0x14d951
  | 180 => 0x15ccd1
  | 181 => 0xcd5d1
  | 182 => 0x44cd1
  | 183 => 0xcc451
  | 184 => 0x164cd1
  | 185 => 0xcd651
  | 186 => 0x1a0c
  | 187 => 0x455d1
  | 188 => 0x15c451
  | 189 => 0x1655d1
  | 190 => 0x15d651
  | 191 => 0xd0411
  | 192 => 0x40d11
  | 193 => 0xd0414
  | 194 => 0xd0416
  | 195 => 0xd1611
  | 196 => 0x44411
  | 197 => 0x40451
  | 198 => 0x164411
  | 199 => 0x41651
  | 200 => 0x160d11
  | 201 => 0x44d11
  | 202 => 0xd0451
  | 203 => 0xd1651
  | 204 => 0x164d11
  | 205 => 0x189611
  | 206 => 0x45611
  | 207 => 0x160451
  | 208 => 0x165611
  | 209 => 0x161651
  | 210 => 0x45891
  | 211 => 0x188451
  | 212 => 0x165891
  | 213 => 0x189651
  | 214 => 0xe8451
  | 215 => 0x44e91
  | 216 => 0x18c451
  | 217 => 0x458d1
  | 218 => 0x164d51
  | 219 => 0xd5651
  | 220 => 0x170e
  | 221 => 0xe9651
  | 222 => 0x164e91
  | 223 => 0x18d651
  | 224 => 0x1658d1
  | 225 => 0xed651
  | 226 => 0x164ed1
  | 227 => 0x3ce
  | 228 => 0x105651
  | 229 => 0x165051
  | 230 => 0x195651
  | 231 => 0x165951
  | 232 => 0x1a8c
  | 233 => 0x194ed1
  | 234 => 0xed951
  | 235 => 0x178e
  | 236 => 0x1a4d
  | 237 => 0x164b0219
  | 238 => 0xb021659
  | 239 => 0x9ce
  | 240 => 0x168e
  | 241 => 0xa4c
  | 242 => 0x198c
  | 243 => 0x16555419
  | 244 => 0x168a
  | 245 => 0x9ca
  | 246 => 0x198a
  | 247 => 0xa4a
  | 248 => 0x9cd
  | 249 => 0xa4d
  | 250 => 0x198d
  | 251 => 0x168d
  | 252 => 0x40d16
  | 253 => 0x44d0419
  | 254 => 0xd040459
  | 255 => 0x164d0419
  | 256 => 0xd041659
  | 257 => 0x16589619
  | 258 => 0x45654
  | 259 => 0x1a9954
  | 260 => 0x1a9054
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 66
  | 7 => 2372
  | 6 => 7169
  | 5 => 3916
  | 4 => 113
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
  | 8 => packedAt gbK8 (1870+((h/22+packedAt gbK8 (1716+(h % 22)*7) 7) % 80)*8) 8
  | 7 => packedAt gbK7 (97244+((h/790+packedAt gbK7 (87764+(h % 790)*12) 12) % 3131)*13) 13
  | 6 => packedAt gbK6 (377558+((h/2389+packedAt gbK6 (344112+(h % 2389)*14) 14) % 8603)*14) 14
  | 5 => packedAt gbK5 (248009+((h/1305+packedAt gbK5 (231044+(h % 1305)*13) 13) % 5687)*13) 13
  | 4 => packedAt gbK4 (8206+((h/37+packedAt gbK4 (7910+(h % 37)*8) 8) % 136)*8) 8
  | 3 => packedAt gbK3 (245+((h/1+packedAt gbK3 (243+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff83f81ff03ffff83ff00ffff033dc1e98f39f
  | 1 => 0x1ffc3fe07fc1e03fc0fffe03f0cd27e7674cf3
  | 2 => 0xe0ffc0007ffe003fff000ffc0f0e38f9878f1c
  | 3 => 0xffffff8000003ffffff0000ff03f01f80fe0
  | 4 => 0xffffffffffffc0000000000fffc001fff000
  | 5 => 0xff00000000000000000000000ffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x29004808800228901190429140104c0a081185
  | 1 => 0x12141220344141084025240aa0450164234432
  | 2 => 0x40ad81045ab4022eaa00a968270a30b1858e18
  | 3 => 0x8caed5d021004b73ccac0304bb03e01d80bc0
  | 4 => 0x10f337966f399702080300408def8001f6e000
  | 5 => 0x9c0006180c211804308c01830effffde000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeaece8eeeaeca8feeaece8eeeaeca8feeaece8eeeaeca8feeaece8eeeaeca8feeaece8eeeaeca8feeaece8eeeaeca8feeaece8eeeaeca8feeaece8eeeaeca8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_36963
namespace PEqualNP.Outside.L_meta_36963
open PEqualNP.Outside.L_meta_36963.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 14 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_32 : Interval s0Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_64 : Interval s0Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_96 : Interval s0Atlas 3 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_128 : Interval s0Atlas 3 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_160 : Interval s0Atlas 3 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_192 : Interval s0Atlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_224 : Interval s0Atlas 3 224 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 228 := (concat (concat (concat bs0_3_0 bs0_3_32) (concat bs0_3_64 bs0_3_96)) (concat (concat bs0_3_128 bs0_3_160) (concat bs0_3_192 bs0_3_224)))
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
theorem bs0_4_128 : Interval s0Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_160 : Interval s0Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_192 : Interval s0Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_224 : Interval s0Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_256 : Interval s0Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_288 : Interval s0Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_320 : Interval s0Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_352 : Interval s0Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_384 : Interval s0Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_416 : Interval s0Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_448 : Interval s0Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_480 : Interval s0Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_512 : Interval s0Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_544 : Interval s0Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_576 : Interval s0Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_608 : Interval s0Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_640 : Interval s0Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_672 : Interval s0Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_704 : Interval s0Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_736 : Interval s0Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_768 : Interval s0Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_800 : Interval s0Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_832 : Interval s0Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_864 : Interval s0Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_896 : Interval s0Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_928 : Interval s0Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_960 : Interval s0Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_992 : Interval s0Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1024 : Interval s0Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1056 : Interval s0Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1088 : Interval s0Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1120 : Interval s0Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1152 : Interval s0Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1184 : Interval s0Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1216 : Interval s0Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1248 : Interval s0Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1280 : Interval s0Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1312 : Interval s0Atlas 4 1312 28 := block_range (n:=28) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1340 := (concat (concat (concat (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 (concat bs0_4_96 bs0_4_128))) (concat (concat bs0_4_160 bs0_4_192) (concat bs0_4_224 (concat bs0_4_256 bs0_4_288)))) (concat (concat (concat bs0_4_320 bs0_4_352) (concat bs0_4_384 (concat bs0_4_416 bs0_4_448))) (concat (concat bs0_4_480 (concat bs0_4_512 bs0_4_544)) (concat bs0_4_576 (concat bs0_4_608 bs0_4_640))))) (concat (concat (concat (concat bs0_4_672 bs0_4_704) (concat bs0_4_736 (concat bs0_4_768 bs0_4_800))) (concat (concat bs0_4_832 bs0_4_864) (concat bs0_4_896 (concat bs0_4_928 bs0_4_960)))) (concat (concat (concat bs0_4_992 bs0_4_1024) (concat bs0_4_1056 (concat bs0_4_1088 bs0_4_1120))) (concat (concat bs0_4_1152 (concat bs0_4_1184 bs0_4_1216)) (concat bs0_4_1248 (concat bs0_4_1280 bs0_4_1312))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_64 : Interval s0Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_96 : Interval s0Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_128 : Interval s0Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_160 : Interval s0Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_192 : Interval s0Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_224 : Interval s0Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_256 : Interval s0Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_288 : Interval s0Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_320 : Interval s0Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_352 : Interval s0Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_384 : Interval s0Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_416 : Interval s0Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_448 : Interval s0Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_480 : Interval s0Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_512 : Interval s0Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_544 : Interval s0Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_576 : Interval s0Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_608 : Interval s0Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_640 : Interval s0Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_672 : Interval s0Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_704 : Interval s0Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_736 : Interval s0Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_768 : Interval s0Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_800 : Interval s0Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_832 : Interval s0Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_864 : Interval s0Atlas 5 864 26 := block_range (n:=26) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 890 := (concat (concat (concat (concat bs0_5_0 (concat bs0_5_32 bs0_5_64)) (concat (concat bs0_5_96 bs0_5_128) (concat bs0_5_160 bs0_5_192))) (concat (concat bs0_5_224 (concat bs0_5_256 bs0_5_288)) (concat (concat bs0_5_320 bs0_5_352) (concat bs0_5_384 bs0_5_416)))) (concat (concat (concat bs0_5_448 (concat bs0_5_480 bs0_5_512)) (concat (concat bs0_5_544 bs0_5_576) (concat bs0_5_608 bs0_5_640))) (concat (concat bs0_5_672 (concat bs0_5_704 bs0_5_736)) (concat (concat bs0_5_768 bs0_5_800) (concat bs0_5_832 bs0_5_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_32 : Interval s0Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 44 := (concat bs0_6_0 bs0_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_7_0 : Interval s0Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_7 : Interval s0Atlas 7 0 1 := bs0_7_0
theorem alls0 : ∀ k ≤ 7, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
  · exact alls0_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 21 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 17 := bs1_4_0
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
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
theorem alls2 : ∀ k ≤ 3, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 26 := bs3_3_0
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
theorem bs3_4_128 : Interval s3Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 134 := (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 (concat bs3_4_96 bs3_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 48 := (concat bs3_5_0 bs3_5_32)
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
theorem bs5_3_0 : Interval s5Atlas 3 0 8 := block_range (n:=8) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 8 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 92 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
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
theorem bgb_4_64 : Interval gbAtlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 113 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96))
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
theorem bgb_5_3904 : Interval gbAtlas 5 3904 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3916 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat (concat bgb_5_96 bgb_5_128) (concat bgb_5_160 bgb_5_192))) (concat (concat (concat bgb_5_224 bgb_5_256) (concat bgb_5_288 bgb_5_320)) (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 bgb_5_448)))) (concat (concat (concat bgb_5_480 (concat bgb_5_512 bgb_5_544)) (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672))) (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 bgb_5_800)) (concat (concat bgb_5_832 bgb_5_864) (concat bgb_5_896 bgb_5_928))))) (concat (concat (concat (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)) (concat (concat bgb_5_1056 bgb_5_1088) (concat bgb_5_1120 bgb_5_1152))) (concat (concat (concat bgb_5_1184 bgb_5_1216) (concat bgb_5_1248 bgb_5_1280)) (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)) (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 bgb_5_1664))) (concat (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 bgb_5_1792)) (concat (concat bgb_5_1824 bgb_5_1856) (concat bgb_5_1888 bgb_5_1920)))))) (concat (concat (concat (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat (concat bgb_5_2048 bgb_5_2080) (concat bgb_5_2112 bgb_5_2144))) (concat (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 bgb_5_2272)) (concat (concat bgb_5_2304 bgb_5_2336) (concat bgb_5_2368 bgb_5_2400)))) (concat (concat (concat (concat bgb_5_2432 bgb_5_2464) (concat bgb_5_2496 bgb_5_2528)) (concat (concat bgb_5_2560 bgb_5_2592) (concat bgb_5_2624 bgb_5_2656))) (concat (concat (concat bgb_5_2688 bgb_5_2720) (concat bgb_5_2752 bgb_5_2784)) (concat (concat bgb_5_2816 bgb_5_2848) (concat bgb_5_2880 bgb_5_2912))))) (concat (concat (concat (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008)) (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 bgb_5_3136))) (concat (concat (concat bgb_5_3168 bgb_5_3200) (concat bgb_5_3232 bgb_5_3264)) (concat (concat bgb_5_3296 bgb_5_3328) (concat bgb_5_3360 bgb_5_3392)))) (concat (concat (concat (concat bgb_5_3424 bgb_5_3456) (concat bgb_5_3488 bgb_5_3520)) (concat (concat bgb_5_3552 bgb_5_3584) (concat bgb_5_3616 bgb_5_3648))) (concat (concat (concat bgb_5_3680 bgb_5_3712) (concat bgb_5_3744 bgb_5_3776)) (concat (concat bgb_5_3808 bgb_5_3840) (concat bgb_5_3872 bgb_5_3904)))))))
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
theorem bgb_6_7168 : Interval gbAtlas 6 7168 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 7169 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat bgb_6_672 (concat bgb_6_704 bgb_6_736)) (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864))))) (concat (concat (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat (concat bgb_6_1216 bgb_6_1248) (concat bgb_6_1280 bgb_6_1312)))) (concat (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536))) (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760)))))) (concat (concat (concat (concat (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)) (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 bgb_6_1984))) (concat (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080)) (concat (concat bgb_6_2112 bgb_6_2144) (concat bgb_6_2176 bgb_6_2208)))) (concat (concat (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304)) (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 bgb_6_2432))) (concat (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)) (concat (concat bgb_6_2560 bgb_6_2592) (concat bgb_6_2624 bgb_6_2656))))) (concat (concat (concat (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)) (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880))) (concat (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)) (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 bgb_6_3104)))) (concat (concat (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200)) (concat (concat bgb_6_3232 bgb_6_3264) (concat bgb_6_3296 bgb_6_3328))) (concat (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424)) (concat (concat bgb_6_3456 bgb_6_3488) (concat bgb_6_3520 bgb_6_3552))))))) (concat (concat (concat (concat (concat (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648)) (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 bgb_6_3776))) (concat (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)) (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 bgb_6_4000)))) (concat (concat (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096)) (concat (concat bgb_6_4128 bgb_6_4160) (concat bgb_6_4192 bgb_6_4224))) (concat (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320)) (concat (concat bgb_6_4352 bgb_6_4384) (concat bgb_6_4416 bgb_6_4448))))) (concat (concat (concat (concat bgb_6_4480 (concat bgb_6_4512 bgb_6_4544)) (concat (concat bgb_6_4576 bgb_6_4608) (concat bgb_6_4640 bgb_6_4672))) (concat (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768)) (concat (concat bgb_6_4800 bgb_6_4832) (concat bgb_6_4864 bgb_6_4896)))) (concat (concat (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992)) (concat (concat bgb_6_5024 bgb_6_5056) (concat bgb_6_5088 bgb_6_5120))) (concat (concat bgb_6_5152 (concat bgb_6_5184 bgb_6_5216)) (concat (concat bgb_6_5248 bgb_6_5280) (concat bgb_6_5312 bgb_6_5344)))))) (concat (concat (concat (concat (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440)) (concat (concat bgb_6_5472 bgb_6_5504) (concat bgb_6_5536 bgb_6_5568))) (concat (concat bgb_6_5600 (concat bgb_6_5632 bgb_6_5664)) (concat (concat bgb_6_5696 bgb_6_5728) (concat bgb_6_5760 bgb_6_5792)))) (concat (concat (concat bgb_6_5824 (concat bgb_6_5856 bgb_6_5888)) (concat (concat bgb_6_5920 bgb_6_5952) (concat bgb_6_5984 bgb_6_6016))) (concat (concat bgb_6_6048 (concat bgb_6_6080 bgb_6_6112)) (concat (concat bgb_6_6144 bgb_6_6176) (concat bgb_6_6208 bgb_6_6240))))) (concat (concat (concat (concat bgb_6_6272 (concat bgb_6_6304 bgb_6_6336)) (concat (concat bgb_6_6368 bgb_6_6400) (concat bgb_6_6432 bgb_6_6464))) (concat (concat bgb_6_6496 (concat bgb_6_6528 bgb_6_6560)) (concat (concat bgb_6_6592 bgb_6_6624) (concat bgb_6_6656 bgb_6_6688)))) (concat (concat (concat bgb_6_6720 (concat bgb_6_6752 bgb_6_6784)) (concat (concat bgb_6_6816 bgb_6_6848) (concat bgb_6_6880 bgb_6_6912))) (concat (concat (concat bgb_6_6944 bgb_6_6976) (concat bgb_6_7008 bgb_6_7040)) (concat (concat bgb_6_7072 bgb_6_7104) (concat bgb_6_7136 bgb_6_7168))))))))
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
theorem bgb_7_2368 : Interval gbAtlas 7 2368 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2372 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)))) (concat (concat (concat bgb_7_288 bgb_7_320) (concat bgb_7_352 bgb_7_384)) (concat (concat bgb_7_416 bgb_7_448) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))))) (concat (concat (concat (concat bgb_7_576 bgb_7_608) (concat bgb_7_640 bgb_7_672)) (concat (concat bgb_7_704 bgb_7_736) (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)))) (concat (concat (concat bgb_7_864 bgb_7_896) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992))) (concat (concat bgb_7_1024 bgb_7_1056) (concat bgb_7_1088 (concat bgb_7_1120 bgb_7_1152)))))) (concat (concat (concat (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280)) (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 (concat bgb_7_1408 bgb_7_1440)))) (concat (concat (concat bgb_7_1472 bgb_7_1504) (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600))) (concat (concat bgb_7_1632 bgb_7_1664) (concat bgb_7_1696 (concat bgb_7_1728 bgb_7_1760))))) (concat (concat (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 bgb_7_1888)) (concat (concat bgb_7_1920 bgb_7_1952) (concat bgb_7_1984 (concat bgb_7_2016 bgb_7_2048)))) (concat (concat (concat bgb_7_2080 bgb_7_2112) (concat bgb_7_2144 (concat bgb_7_2176 bgb_7_2208))) (concat (concat bgb_7_2240 bgb_7_2272) (concat bgb_7_2304 (concat bgb_7_2336 bgb_7_2368)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_64 : Interval gbAtlas 8 64 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 66 := (concat bgb_8_0 (concat bgb_8_32 bgb_8_64))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 18, 22),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 6, 22),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 52, 60),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 28, 60)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaece8eeeaeca8feeaece8eeeaeca8feeaece8eeeaeca8feeaece8eeeaeca8feeaece8eeeaeca8feeaece8eeeaeca8feeaece8eeeaeca8feeaece8eeeaeca8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808936 * 2 ^ 32 + 4008373416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_36963.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,4]⟩,⟨.and,[2,5]⟩,⟨.or,[1,7]⟩,⟨.and,[3,8]⟩,⟨.or,[0,9]⟩,⟨.and,[6,10]⟩,⟨.or,[4,5]⟩,⟨.and,[1,12]⟩,⟨.or,[0,13]⟩,⟨.and,[2,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4008373416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4008373416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_36963

open PEqualNP.Outside.L_meta_36963 in
theorem PEqualNP.Outside.L_meta_36963 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4008373416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4008373416) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
