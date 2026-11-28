import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37355.Model
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


end PEqualNP.Outside.L_meta_37355.Model

namespace PEqualNP.Outside.L_meta_37355
open PEqualNP.Outside.L_meta_37355.Model
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

end PEqualNP.Outside.L_meta_37355

namespace PEqualNP.Outside.L_meta_37355
open PEqualNP.Outside.L_meta_37355.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x729338000936970d20600c669d5016b00c80006122bea239b9401a280a000005eb490b5e01b3990b30000420000580821820cbfe43fd43fc43ff32fe32fd32fc32ff31fe31fd31fc31ff21fe21fd21fc21ff30fe30fd30fc30ff20ef20fe20fd20ed20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xa41fc43483fe64907bcc920ff19241ee32483fa64907b4c920fe19241ec32483fea2905fd4520ff28a41fd51483f8a2905f14520ff98a41fe31483fa62907f0c520ff90a41ef21483fc42907b88520fe90a41ed21483f842907b08520ff98241fe30483fa60907f0c120ff90241fb20483fc40907b88120f7a9a41ee53483daa6907b14d20f721a41ed43483d886907bd4520f728a41ed51483d8a2907bcc520f718a41ed31483d862907bd4120f5a8241ef30483dc60907b4c120f618241ff53082fea6107f94c20bf29841fd53082faa6107f14c20be29841fe43083fa86107f10c20bf290416e52083fe64107f8c820fe99041fc32083fea2107f94420bf28841fd51082faa2107f14420ff98841fe31083fa62107f0c420ff90841fe21083fa42107f08420bf28041ff30083fc60107f4c020fe18041ff20083de40107f88020fd10041fd20083da40107e48020ffa9e217f53c43fca7885f94f10fea9e217d53c43f8a7885f14f10ff21e21fd43c43f887887fd4b10bfa9621fe52c42fca5887f54b10bea9621fc52c42f8a5887fccb10ff19621fd32c43f865887fcc710ff18e21f631c43fa63887d4c710fe18e21ff21c43fc43887f48710fe10e21ff30c43fc61887f4c310fe18621ff20c43de41887f88310fe90621ed20c43f841887fd4e10bfa9c21fe53842fca7087f54e10bea9c21fc53842f8a7087f90e10fea1c21fc43843fea5085fd4a10ff294217e52843dca5085b94a10fea94217d52843daa5085b54a10fe294217c52843fe65087f8ca10fe99421fc32842faa3087fcc610ff18c21fd31843f863087fc8610ff10c21fd21843f843085f94210ff98421fe30843fa61087f0c210ff90421ef20843fc41087e88210fe90421ed20843f241087a48210fe10421ff10843ee21087ec4210ffa9a217f53443fca6885f94d10fea9a217d53443f8a6885f14d10ff21a21fd43443f886887fd4910bfa9221fe52442fca4887f54910bea9221fc52442f8a4887fcc910ff19221fd32443f864887fcc510ff18a21f631443fa62887d4c510fe18a21ff21443fc42887f48510fe10a21ff30443fc60887f4c110fe18221ff20443de40887f88110fd10221fd20443da40887e48110f490221fc20443fe20887ec4110ff08221f610443fea6085fd4c10ff298217e53043bca6085794c10fea98217d53043baa6085754c10fe298217c53043fc86087f50c10fe21821ff52042fea4087f94810bf29021ee52042dca4087f54810bea9021ed52042daa4087f14810be29021ff32043fc64087f4c810fe190217e51043fe62087f8c410fe98821fc31043fe42087f88410fe90821fc21042fca0087fcc010ff18021fd30043f860087fc8010f790021fe20043fa40087b48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xe31cc3fa6398774c730fe18e61ff21cc3fc43987f48730fe10e61ff40cc3fea9185fd5230ff2a4617e548c3faa9185f55230fe2a4617d538c3fe871877d0e30ff21c61fd438c3f887187710e30ffa9461fe528c2fca5187b94a30b729461fd528c2faa5187b54a30b6a9461fc528c3fe85187f90a30fea1461fc428c3fe65187f8ca30fe99461fc328c3fea3187f94630bf28c61fd518c2faa3187f14630ffa0c61fe418c3fa83187f10630ff98c61fe318c3fa63187f0c630ff90c61fe218c3fa43187f08630bf28461ff408c3fc81187fcc230ef98461fb308c3fea8985fd5130dfaa2613f544c3fca8985f95130feaa2617d544c3f8a8985f15130de2a2613c544c3fe86987f90d30ef21a61fd434c3ba86987f10d30ffa92617f524c3fca4987f54930fe292617c524c3fe84987f90930fea1261fc424c3fe64987f8c930fe99261fc324c3fea2985fd4530ff28a61fd514c3f8a2985f14530ffa0a61fe414c3fa82987f10530ff98a61df314c3fc62987f4c530ee98a61fc314c3fe42987f88530fe90a61fc214c3fe80987f90130fea0261ff304c3f660987f8c130ef18261ff540c2fea8187f95030bf2a061be540c27ca8187f55030beaa061bd540c27aa8187f15030be2a0617e530c3fe861877d0c30ff21861fd430c3f886187710c30ffa9061fe520c2fca4187b94830b729061fd520c2faa4187b54830b6a9061fc520c3fe84187f90830fea1061fc420c3fe64187f8c830fe99061fc320c3fea2187f94430bf28861f6510c2eca2187f54430bea8861f5510c2eaa2187f14430ffa0861fe410c3fa82187f10430ff98861fe310c3fa62187f0c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffa9e417f53c83fca7905f94f20fea9e417d53c83f8a7905f14f20ff21e41fd43c83f887907fccb20f799641fe32c83dc65907f4cb20f699641fc32c83d865907fd4720ff28e417e51c83faa3905f54720fe28e41ff31c83fc63907f4c720fe18e41ff21c83de43907f88720f710e41fd21c83da43907f08720f610e41ff30c83fc61907f4c320fe18641ef53c83dca7907b54f20f629e41ee43c83da87907b10f20f7a8e41ee51c83daa3907b14720f798e41ee31c83da63907b0c720f798641ee30c83da61907b0c320ffa9c417f53883fca7105f94e20fea9c417d53883f8a7105f14e20ff21c41fd43883f887105f54a20b6a9441ff32883fc65107f4ca20fe19441ff51883fca3105f94620fea8c417d51883f8a3107fcc620ff18c41fd31883f863107fc8620ff10c41fd21883f843105f94220ff98441fe30883fa61107f0c220ff90441ef20883f641107fd4d20bfa9a41fe53482fca6907f54d20bea9a41fc53482f8a6907f90d20fea1
  | 2 => 0xc7fea918dfd5231ff2a4637e548c77ca918cf95231feaa4637d548c77aa918cf55231fe2a4637d538c7fe8718ff90e31fea1c63fc438c7fea518ff94a31bf29463fd528c6faa518ff14a31ffa1463fe428c7fa8518ff10a31ff99463fe328c7fa6518ff0ca31bf28c63ff418c7fc8318ffcc631ef98c63f7318c7fea118ff94231bf28463fd508c6faa118ff14231ffaa2637f544c7fca898df95131feaa2637d544c7f8a898df15131ffa1a63df434c7fc8698ff50d31fe21a63dc434c7fea498dfd4931f7a92636f524c7fca498ff54931fe292637c524c7d8a498db14931ffa1263fe424c7fa8498ff10931ff99263df324c7fc6498ff4c931ee99263fc324c7fe8298ff90531fea0a63ff314c7ee6298ff8c531ef18a63ff504c6fea098ff94131fea8263fc504c6f8a098ffd5031bfaa063fe540c6fca818ff55031beaa063fc540c6f8a818df94c31ffa1863fe430c7fa8618ff10c31ffa9063fe520c6fca418ff54831bea9063fc520c7fe8418ff90831fea1063fc420c7fe6418ff8c831fe99063fc320c6fca218ffd0431ff20863fd410c7f88218ffcc431ef98863fe310c7ec6218ff4c431ee98863f5310c7fea018ff94031bf28063fd500c6faa018ff14031ffa9e437f53c87fca790df94f21fea9e437d53c87f8a790df14f21ff21e43fd43c87f88790ffccb21ff19643fd32c87f86590ffcc721ff18e43fd31c87f86390ffd4321ff286437e50c87faa190df54321fe28643ff53886fea710ff94e21bf29c43fd53886faa710ff14e21be29c43fe43887fa8710ff10e21bea9443ff32887de6510ff8ca21fe99443fc32887d86510df94621ff98c43fe31887fa6310ff0c621ff90c43ef21887ee4310ffd4221ff284437e50887faa110df54221fe28443ff53486fea690ff94d21bf29a43fd53486faa690ff14d21be29a43fe43487fa8690ff10d21ff99243fe32487fa6490ff0c921ff98a43fe31487fa6290ff0c521ff90a43f721487fc4290fb88521ffa82437f50487fca090ff54121fe282437c50487fea610dfd4c21ff298437e53087bca610d794c21fea98437d53087baa610d754c21fe298437c53087fc8610ff50c21fe218437e52087fe6410fbcc821ff19043fd32087f86410fb0c821bf28843ff31087fc6210ff4c421fe18843ff21087de4210ff88421fb10843fd21087da4210fd48421ffa8043fe50086fca010fe94021bd28043fd50086faa010fe54021bca8043fc50087fea9987f95330bf2a661fd54cc2faa9987f15330be2a661ff43cc3fc87987790f30fea1e61dd43cc3f887987fd4b30ff296617e52cc3faa5985f54b30fe29661ff42cc3fc85987f50b30fe21661ff32cc3fc65987f4cb30fe19661ff51cc3fca3985f94730fea8e617d51cc3f8a3987fd0730ff20e61fd41cc3f883987fcc730ef98e61f
  | 3 => 0xc01003400400000000400800001800000000000000400400004400000800002400003c00000000002800001003002401c00400c00401c02802000002001c00000000c01400400401c00401800000000003c00c00800003800001c00005c00400004c00800c00c02801c04800801000407007005800800002c00801400003c00400000c03000000001000003400400001c00000000c02400807c04000400000000400800000400803c00400002000c00000000000800004006000003800002800403801000000400402002c01800407c00800800000001004c00800401000001000802004400000400000c00001400400000c000008000028000000020010000014034024004000000020022faa921df94e43ffa1c87df4390ffea521ff94a43bf29487fd5290efaa521ff14a43ffa8c87fe5190efca321ff54643bea8c87fc5190ffea121ff94243bf28487fd5090efaa121ff14243ff21a87be4350ffea4a1dfd4943ff29287fd5250ff8a4a1df14943ffa8a877f5150ffca2a1ff54543fe28a877c5150ffea0a1dfd4143ff28287fd5050ff8a0a1df14143bf29887fe4310fbc8621ff50c43eea18879d4310ffea421ff94843bf29087fd5210efaa421ff14843ffa8887fe5110efca221ff54443bea8887fc5110ffea021ff94043bf28087fd5010efaa021ff14043ffaa665fe54ccafca9997f55332beaa665fc54ccaf8a9997fd0f32ff21e65fd43ccbf887997fd0b32ffa8e65fe51ccafca3997f54732bea8e65fc51ccbfea1997f94332bf28665fd50ccafaa1997f14332ffaa4657f548cbfca9195f95232feaa4657d548cbf8a9195f54e32ffa1c65fe438cbfa87197f10e32bf29465ff428cbfc85197fcca32ef99465ef328cbfea3197f94632bf28c65fd518cafaa3197f14632ffa8465fe508cafca1197f54232bea8465fc508cbfea8995fd5132ff2a2657e544cbfaa8995f55132fe2a2657c544cbfe86997f90d32fea1a65fc434cbfe84997f90932fea1265ff324cbde64997f8c932ef19265ff514cafea2997f94532fea8a65fc514caf8a2997fd4132bfa8265fe504cbfaa0997f14132be28265ff540cafea8197f95032bf2a065fd540cafaa8197f15032be2a0657e530cbfe86197f90c32fea1865fc430cafca4197fd0832ff21065fd420cbf884197fcc832ef99065fe320cbdc64197f4c832ee99065ed320cbfea2197f94432bf28865fd510cafaa2197f14432ffa8065fe500cafca0197f54032bea8065fc500cbfea998ff95331bf2a663fd54cc6faa998ff15331be2a663ff43cc7be8798ff90f31fea1e63fc43cc7b88798ffd4b31ff296637e52cc7faa598df54b31fe29663ff42cc7fc8598ff50b31fe21663ff32cc7be6598ff8cb31fe99663dd32cc7f86598ffd0731ffa8663fe50cc6fca198ff54331bea8663fc50c
  | 4 => 0xfc866800040c000000a2e1a9b041685c8001300001dc08e05a1aa8598dd0000a6a080000000b2c00000113dae8222151511ea18340000006b60080000001d800065dfd8000000330000d217443916988600ec001528000001064f71d297bd564000000c20000000001014ad1530001bb8c998a8799cf1739d3d555f5c001190dc83dd3f06d861c9fc001e98079fc8889804000001d800000000000014fc0000000000001bdf80000001cec27a1180008e4000000c740020e9a98001fa00007e8d68001f44348ea1ab9450000001568ca84000011207a0a2172130ce94001a10ba8d502104d9678d48335a05a0cfa1622034cc61700016f00013380e0000001d70000001600b72250000000e24ad80000000000006a61a00014600000000186100013d889c000240cb000116d1c8c6c7c20d97a9c100000000000000000000000000014f000113427e0721b87ee16912c1414d9c405b80f99a9719368c60001a003cc0016649ecf495f4002199b521f99109ca2316d6238b79c222408d80016e8e7993a1144e06e80000000002080006c80005f035cb11660001f306d0000000001de0000001a18000700285f00000000000001e6dd5a0315b8f6958582157dfb184a0a8254a30fd0fa5638d99421d407d4410cd1831c017ad899d35f54000000000130001dd90d22e1c70e180003f9cdcac1f10a183f0001ac4000a1000000000000000000002001400c00000402000400c00800000801000404002400003800400c00805c00000000400001401000400001004000800000800400000003400400000007400c00001400c01c00000000400c00806000001000400001800000000004000401000800401800003401401400000c00000c00800800400003800000400c00000800000000805001800003003c00002403400000402004c00001c00000800400001000401800000000803400803800002c03801806800000000801400007801001400000001400003801800001400402805803c01800802800800000000000005c00000000000401000400401000400001400001c00400000001c04000002802801400001800001406400400807802800000000002802c01400004c01c01001c01c00000000000402c03801800800808c01000400400401c02800801c01400001004400802c03401400000c00402000000002400002400002c01801800800002800400000800000402400003800401c00400001000006001800000400000000002800001800403000801c00002001403000000003001003800400800000c00000400800800400000002000800000c00000000c00000c01c00000400801800400401000000002c04401001c08800800002c00401800402000400800000c00407001c00000002800000000000402400002001c00004401800000002c00
  | 5 => 0x229d2ceba0b9c9956c93c0000015380748580000000011e4001bfd7e0c28991e480008f955c0000008f00000005900000000000009acb840000007b5010000000768eacb1c001958000001bb41d00000000000000000005ea0d1239972354f55178000e84000f9a328f89e09645b28b7cb40740001fb8001808ba51d94a93e80000018bd5a18c44b9418be80b8984618ab1f18118ef00002ac450001598000001ce5aa0ccc0000009356900a102e0f0101ae009973c440b482a10a1180a88d2d4a0299cc9ed08407f89c48000022080010880021253885bd4c0ad6090000e894000007282e8cb81b1f38639398001430c00cc0000df13a8001949e51490001324000ee975000131c000be0000548000001100001da0bd1dd22b000000031c001d89a78b0c1858e09a5a397cc0020e0000e1d9d097845810883e36032124e2c9030000d28002261a917111180017b81496197c1240b8c301ade2a17711d52aa03958c00000000128895885d1e8000001dc85b1bf5070d90add1f13609b5ab62f0001d98000000000000000b80000001489ba40cd94c000b28cd8761b18698360f0c001290001002279428198bd80000023380020b1551c787300e4bc97fcfbc2d00000011a9904000000001f4831165c001a6884c625df8aa80014d4830c1520a311168fb4da09e20a03c04b1b581c5708a48a780016580020182b86ac9500001c84314f406c00146a320000000a000000013dc0015b0000854000c644ec0000022c1674001ec0001ec80001a80000000000000006f4000d45a417f0b91cf58719e138c089d4819d0a83d5a4c9f4080031f4d9f16f4001604b9c170d606b981df959400000000018d00000000016d8fc16d0000001c495f8000e515f000000208800000041c000000f28a3c88205c0017d8001f900009700012b85591f8b3c0f4939c28e2c00000000063c378000cf0bb0680530000000000001ad80002f0c5c4f5079165d61b79039258001774cfa291634000001060000001735fd1264b053716703418b81e0e485c16ecff05e1074d8150dee089594564c3a92e0000000000000000aa11e00010258f46e1778c840000012300bdee8001af0000e40329f60000000281570594308238ae48f4cd482a10143a2587b9e18f402a9b022f8f1a2b6131271198000000930658001548b18000000671408a2800052a0c97a00022e9ac1ca14c4001b70000408a60fb0d318416493cdce22701a5f40001729ba8c061b218000162800000137c24c000174e3a249a286a1780c7d504a984287cc368399c9000000086a078d580000011b83557016106e4000001220000000001a5d7e8cb4d955d0d9c29db20000000aec0000016a80007fd7c80000000000000003c80000000005ac9e80000021792f01f1378000ca4000000000000
  | 6 => 0x19184c0ab80008504d20c1889b61059170001d900000005723480012d182d2100000000020214596400000000000000000000000000006a8a8d5c000181084800000071044428c1b91dc0000007f44a921a06034c0000013d4a70b68000000000000000001a087780000019500000017e4001d500000010c5c08001bae2283d15fc000001a490989f00000016dcc6818c000000000f4c000fe960c544000001df01107380016fc138158069b409809952f9900000c40150000000cc87820100000000000012000000000d800067800000000000163cd8d9817b55742d9e90291754d56300d4d080439688a81d11c6095cce00000011409203a0001590d4032de5c0015194e8001481bc195c00007d498c880019212e8b98001d38001bf999d0205883e118a068000001f9906c890c50001e3c0005680022883180012c80000000000012c2108561b900000c5cc0128e08000838001e88b58844b891a01cde218d8759125ab1790af56e0f20001558900000038660634000000bada597497600000002be2bd1600013f4955b300016a14cd71400000000000094800000000161d1ec000001a719c8001bc878e058c0e319e71470178b006c13d1ef14e0b603880219c1bd8248050491de8000000c480017f87c9c50691768ff8000000000001d0077c0000005d9bbc0000000000020f99f80000000000018fc001c300000021380019286495ec3e9110afd6cc794748a080018000007883b9f087857dc6502b09d8b153209100b00010c0751b10a509b85a5ef800000092800094000000170c0000000013800005b4e1000138447108dfe222113864cb34448ae2048218d710e1e54498380a91a6048004998802a1c1e299e9d32158790000d79b814b8689bf00015340000000000004fc000000001e8166dca8d34000bf853c00000000000000000090981976400007000117c0000000000008a9c823509d1960000a59879ead5457d13b8dc03b00b48784e8f502e09881ad8e8821ac9fc055157985a215174ea8810ee1e78f454418c847800062818163017c4617322d9930001e68ba0010488200656190968040ae9b74cdd32a2987194bc002281b68c31a50000084000734000d08bfc504001705d21148001f70db86f85c5f8879d76d008b213906f161460080a21c000ed84cd5a92602593c1cb166a09901cf78435fa88a000000000000072023000000190c4f0001968000000a7c0007e11300009c09bc0007a51284202f8a41b38e90418ec00022012bca39348469e580a8000000cbcfd82c21619921f00007741f8960b94bb62a9310b0858c0010c8000000000e01478002040000000000001a20000001330001798000c18b25e10cad5804d58f0001d554b16f93942940000010e82c96084c52558618147ac99c000abe368bf18a0001891f6c0000
  | 7 => 0xc5888c090001e30000000001789ce8000270001bb06423580008d00000000000000000000011d0871a54338060000000000000000d18001f28af0000000000e8c001881158000000f38000001150190f90000e152d4000000644f000000000016c0000ed00f00015e000000220c001ff13e0000bc1af80000008e8581e34000538000d100000006093c974c8b8001c88ac96546fc0008c93596800000005a800024583c1c000150800033c00073c7c4000e81b08f80ef92680001a2001cb8351b88000000c800000598b4000ec87da2b8f618521e8af93b000069c424a44f58e2911610c0016c454c0000010f9824194000000eb00d000043de415e4000a8400000180c62df7a1e02880000020500021fda81a30bb9f68ac459c0007f204d318620000000000000000268000000000000260f6d7596500003c40012a08c1280508d890b08b06b21293155009e52520285f9db18c0001abdd19c680010689aa3310487a80021410d8c79d79a45d4d8f92cc0dd53c0000017b00012c61d81880000000c83d95408fc0c00011c1c18000370001eb85209f800094c00000099800000074c4f9341da8000000000000acc00000154d6b95d87b0d854ec344fb80019b8000000000000000001f59d68000e70ea4001019050c554d00014c800000199a1d000000000044c0004dc001f20c10a94884c08de000016c0000000000000000000017412d8579350000000000000001e44f106edcd1fea308000d24c39eb02a4001be0db1829bd0fac899b9952dc5880586983a210518c9c2b5ff8e98e699d9e60501be975cde9d089461ca1490922d0f65ea94e4000002268f5cfe0008415908a35c380016b1ed8001e38000f08dd8000e610f0325cf8c4cf30540e200007bc000002044919b4823e121ad0da94113084e49b096cb3857cb3234016126c00000035a218000000ce800102800000218800098d7c5db96c8000000d018b00012490b84c80019b15e8b501e80e80017d42512451b0001c0c0015215c8e589a05107d0001588000001ad40000000000019a0000001228000c90b744a08ec770000630000ca00000000000012785859793a12b12993f91094f8554d5d040d38000df8c71a895614480000002c5f50744000000965ba1cda1107081b4e305d0818fa8121e0000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xb210427f65884109f596210435e5388410d754e210436e5288410db54a21042fa6088410be582210427f6548410d794d210435d5348410db949210436d52484109fd94210427d6508410b798c21042dd6308410d794c210435d5308410db948210436d5208410f948421042fa6008410be580210427e63940109f58e500427e6294010db98a500426e62940109f58a500436d62940109b58a500427d61940109f597300433e54cc010cf553300435e53cc010d754f300436e52cc010db54b300427f658c0109f596300433e548c010cf552300435e538c010d754e30042ee628c010bb58a300436e528c010db54a30042f6618c010bd586300427f654c010afd9130042bc644c010cf951300433d544c010d794d300435d534c010db949300436d524c0109fd94300427e650c0109f594300427c650c010af99030042bd640c010cf950300433d540c010d794c300435d530c010bb98830042ed620c010db948300436d520c010bd98430042f5610c0109f597200435e53c8010d754f200436f52c8010db94b200436d52c8010db14b20042ed65c8010db597200426d65c8010dbd4f200436e53c8010f394f200434e53c8010db54f20043cd53c8010d354f200436c53c8010db947200436e50c80109fd96200427d6588010d794e200435d5388010bb58a200436e5288010db54a20042f66188010bd586200437a50880109fd95200435e5348010d754d200436f5248010db949200436d5248010db149200437a5048010bbd95200436f65480109bd95200436f5348010db94d20043ce5348010d394d200436d5348010f354d200434d5348010db14d200436e5148010fad81200436e5048010da941200427f65080109f994200427d65080109f194200435e5308010d754c20042ee6208010db948200436d5208010bd98420042f56108010d794f100435d53c4010db94b100436d52c4010dd597100437753c4010f594f100437553c4010f554f100435553c4010f994b10043e552c4010f9c8310043e520c4010d794e100435d5384010bb98a10042ed6284010db94a100436d5284010bd58610043765184010fac8210043e92084010be596100437965840109e59610043da5384010f654e10043ea6284010fa58a100437b5284010fa94a10043795284010fa54a10043695284010be586100437a5184010fc946100427f6544010d794d100435d5344010db949100436d5244010fac8110043e92044010bdd95100437765440109dd9510043775344010f594d10043755344010f554d10043555344010f994910043e55244010bdd8110043765044010f9c8110043e52044010bed95100437b65440109ed9510043da5344010f654d100437b5244010fa94910043795244010fa54910043695244010bed8510043f36144010de94510043f25144010
  | 1 => 0x436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109d984530427e6014c10de980530427f6590c109f996430427d6590c109f196430433e5490c10cf552430435e5390c10d754e430427f6550c109f995430427d6550c109f195430435e5350c10d754d43042fb6050c10be181430427f6510c109f994430427d6510c109f194430435e5310c10d754c430439d4310c10b798f52042dd63d4810d794f520435d53d48109f98f520435e63d48109798f520427d63d4810d758f520425d63d48109f987520437661d48109f983520437a60d48109f596520435e5394810d754e520436f52948109f98e520427d63948109b596520436f5394810db94e52043ce5394810d394e520436d5394810f354e520434d5394810db14e520436f6394810db98e520436d6394810db18e520436e4394810db50e520436c4394810db986520436c6194810db982520436c6094810d794d520435d53548109fd8d520427c6354810dbd89520427f61548109f585520427f60548109f581520436f6554810dbd4d520436e5354810f394d520434e5354810db54d52043cd5354810d354d520436c5354810dbd8d520436e6354810db58d520436c6354810db90d520436d4354810db10d520436e6154810db185520426f6054810db981520426d6054810db181520436c1054810b798c52042dd6314810d794c520435d5314810bb988520436d52148109f98c520435e63148109798c520427d6314810d758c520425d63148109f988520436e62148109b988520427e6114810dd984520427e6014810de980520427a60148109fd97320427e65cc8109f597320427c65cc810cf953320433d54cc810d794f320435d53cc810db94b320436d52cc8109fd96320427e658c8109f596320427c658c810cf952320433d548c810d794e320435d538c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810cf951320433d544c810d794d320435d534c810db949320436d524c810bdd8532042f4614c8109fd94320427e650c8109f594320427c650c810cf950320433d540c810d794c320435d530c810db948320436d520c8109f98e510427d63944109f98a510427d62944109f597310433e54cc410cf553310435e53cc410d754f310436e52cc410db54b310427f658c4109f59631042be648c410af592310433e548c410cf552310435e538c410d754e310436e528c410db54a3104376518c410be98231042f9608c4109fd95310433e544c410cf551310435e534c410d754d31042ef624c410bb189310436e524c410db5493104376514c4109fd94310427d650c410cf950310433d540c410d794c310435d530c410db948310436d520c410be98031042f9600c4109f597210435e53c8410d754f210436e52c8410db54
  | 2 => 0x610c1109f997204436f52c8110db14b20442f661c8110bd587204436f65c8110db997204436d65c8110db197204436f53c8110db94f204436d53c8110db14f20443e661c8110f958720443e631c8110f94c7204427e6588110bb58a20442fa6588110de99620442f96288110ba58a204437a5288110de14a20442fa6188110fc8c620443f131881109fd95204427d65481109f195204436f5248110db14920442f76148110bd185204436f6548110db995204436d6548110db195204436f5348110db94d204436d5348110db14d20443e76148110f918520443e63148110f94c520443eb6048110facc120443ea3048110fa4c120443e83048110be195204437865481109e19520443eb6248110fad49204437a5248110de14920443e85248110facc920443ea3248110fa4c920443e83248110fcd8520442f86148110fc18520443f23148110fc4c520443eb2148110fa88520443e92148110fa08520443eb6548110dad9520443e86548110da19520443eb6348110fa98d20443e96348110fa18d20443eb5348110fa94d20443e95348110fa14d20443ea4348110fa50d20443e84348110fad8520443e36148110fa98520443e96148110fa18520443e06148110facc520443ea3148110f88c520443e93148110f84c520443e831481109f99420442ee6208110be98020443e92008110fac8310443e920c4110bed8b10442f962c4110fc8c710443f131c4110bb98a10442ed6284110fa48210442f76384110bd58e10443e66284110f958a10443f35084110f9c8210443f22084110f948210443f12084110f848210442be64d4c10af59353042ee62d4c10bb58b530427e64d4c10cf993530423e64d4c109f593530433d64d4c108f593530427e62d4c10db98b530426e62d4c109f58b530436d62d4c109b58b530427e61d4c10dd987530427e60d4c10de983530427d6594c10d7d4e530427e6494c109f592530427e6294c109f58a530425d6594c10d7d52530435e5494c10e7952530431e5494c10d7d92530435e6494c10d7592530435c6494c10d7d8a530435e6294c10d758a530435c6294c10d7986530435c6194c10d7982530435c6094c10cf951530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427d6154c109fd81530427d6054c10d7d95530435f5454c10d7951530439e5454c10c7951530435d5454c10e7551530431d5454c10d7d91530435e6454c10d7591530435c6454c10d7d89530435e6254c10d7589530435c6254c10d7985530435c6154c10d7981530435c6054c10d704153042be6414c10af590530433e5414c10cf55053042de6314c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6314c10d798c530425e6314c109f988530
  | 3 => 0xd10dd586534427d6094d10de58253442bf6454d10af19153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109fd81534437b6054d109f994534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427e6114d10dd584534427c6114d109f980534427c6014d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d10bd98643442f56190d109fd95434427e6550d109f595434427c6550d109fd94434427e6510d109f594434427c6510d10d7d4c434435c5310d10e750c43442f66110d10bd58443442fa6010d10be580434427e63d49109f58f524436f52949109f98e524427d63949109f98a524427d6194910dd586524427d6094910de58252442df6354910b718d524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109fd81524437b60549109f994524436d52149109f98c524427d6314910db988524427e61149109f184524427e6014910de580524427c60149109fd97324427e65cc9109f597324427c65cc910dbd4b324436c52cc910bd98732442f561cc9109fd96324427e658c9109f596324427c658c910d7d4e324435c538c910be98232442f9608c9109fd95324427e654c9109f595324427c654c9109fd94324427e650c9109f594324427c650c910d7d4c324435c530c910dbd48324436c520c910bd98432442f5610c910be98032442f9600c9109f997314435f53cc510d714f31442fa60cc510be583314427e658c510af99231442bd648c510bd9963144376658c510bdd9231443b6648c510bd59231443b5648c510ad59231442f5638c510dd94e3144374538c510bd982314427c654c510d7d4d314435c534c510bbd8931442ec624c510bed8131442f8604c510dd1953144274654c510bdd9131442f5644c510f5d8d31443d7534c510dd94d3144374534c510f514d31443d7434c510f510d31443e7624c510f918931443d7324c510f54c931443f3604c510bd18131443f0604c5109f99431442f6610c510f54c4314427e65c8510dbd4b214436c52c8510be98321442f960c85109f996214436e5288510db54a214427c6548510dbd49214436c5248510bed8121442f860485109f99421442de6308510b758c214436e5208510db54821442fa60085109f997304435f53cc110d714f30442f661cc110bd58730443d531cc1109f99630442ee628c110bb58a304427f654c1109f595304427c654c110afd9130442bc644c110d7d4d304435c534c110bdd8530442f4614c110f54c5304427e650c110af99030442bd640c110bb98830442ed620c110bd98430442f5
  | 4 => 0xb585528436e6054a10db181528436d5214a109f98c528427d6314a10db98852843756114a10de980528427f65cca109f997328427d65cca109f197328436e52cca10db54b328427f658ca109f996328427d658ca109f196328436e528ca10db54a32842fa608ca10be582328427f654ca109f995328427d654ca109f195328436e524ca10db54932842f7614ca10bd185328427f650ca109f994328427d650ca109f194328436e520ca10db54832842fa600ca10be580328435e53cc610d754f318436e52cc610db54b31842fa60cc610be58331842be648c610af592318436e528c610db54a318435e534c610d754d31842ef624c610bb189318436e524c610db54931842fb604c610be181318436e520c610db548318436e52c8610db54b21842fa60c8610be583218436e5288610db54a218436e5248610db54921842fb6048610be18121842de6308610b758c218436e5208610db54821843e52108610be580218435f53cc210d714f308436e52cc210db54b308435e538c210d754e30842ee628c210bb58a308436e528c210db54a30842f6618c210bd58630842bf644c210af191308435f534c210d714d308436e524c210db54930842be640c210af590308435e530c210d754c30842ee620c210bb588308436e520c210db54830842f6610c210bd584308436f52c8210db94b208436d52c8210db14b20842ed65c8210db597208436f53c8210db94f208436d53c8210db14f208436e5288210db54a20842f66188210bd58620842f96588210de596208437a5288210fa94a20843e95288210de14a20842fa6188210fc98620843f16188210dbd49208436e5248210db549208436c5248210bbd95208436f6548210dbd4d208436e5348210db54d208436c5348210fad8120843eb3048210fa8c120843e93048210fa0c120842fb6548210ded9520843eb6248210fad49208437a5248210fa949208436a5248210fa54920843785248210fa14920843eb3248210fa8c920843e93248210fa0c920842f86148210fac8520843ea2148210fa48520843e82148210fad9520842eb6548210dad9520843eb6348210fa98d20843e96348210fa18d20843eb5348210fa94d20843e95348210fa14d20843ea4348210fa50d20843e84348210fad8520843ea6148210fa58520843e86148210facc520843ea3148210fa4c520843e83148210db948208436d5208210bd98420842f56108210fa480208436e52c4210db54b10843eb20c4210fa48310842f565c4210dd597108437753c4210dd54f10843e652c4210f954b10843e720c4210f948310842f965c4210de59710842fb62c4210be58b10843ea52c4210fa54b108427e64d4d109f593534427e62d4d109f58b534435f5394d109f992534427d6494d109f98e534427e6294d109f58a534427d6194
  | 5 => 0x31c42f9608c710dd59631c42f7648c710ed99231c42f5648c710ed59231c42b5648c710dd94e31c43d6538c710f554e31c4374538c710bd98231c43f2608c710fc58231c435f534c710d714d31c42ef624c710bb18931c42f7654c710ddd9531c42f7644c710bd59131c43d7634c710f5d4d31c4376534c710dd14d31c43d4534c710f5d0d31c43d4434c710f9d8931c43e4624c710f5cc931c43d5324c710bd18131c435e530c710d754c31c43d5310c710be98031c42f9600c710dbd4b21c436c52c8710db94a21c436d5288710be98221c42f96088710dbd4921c436c5248710b798c21c42dd6308710db94821c436d5208710be98021c42f96008710d794f30c435d53cc310bd98730c42f561cc310f54c730c42ee628c310bb58a30c42bf644c310af19130c435e534c310d754d30c42f7614c310bd18530c43d5314c310af99030c42bd640c310bb98830c42ed620c310bd98430c42f5610c310db94b20c436d52c8310bd98720c42f561c8310db99720c436d65c8310dbd4f20c436e53c8310db54f20c436c53c8310f998720c43e561c8310f98c720c43e531c8310db94920c436d5248310bdd8520c42f46148310dbd9520c436c6548310dbd4d20c436e5348310db54d20c436c5348310f9d8520c43e46148310f98c520c43e53148310fad8120c42ee62d4e10bb58b538427e64d4e109f593538427e62d4e10db98b538426e62d4e109f58b538436d62d4e109b58b538437561d4e10de983538435f5394e109f992538427d6494e109f98a538427d6294e10afd9153842bc6454e109fd91538433f6454e108fd91538427c6454e10cf191538423c6454e10d7d8d538427f6254e109f18953842be6414e10af590538435d5314e10bb98853842ed6214e109f990538433e6414e108f990538427d6414e10cf590538423d6414e10d798c538427e6214e10db988538426e6214e109f588538436d6214e109b58853843756114e10de980538427f6590e109f996438427d6590e109f196438433f5490e10cf152438435e5390e10d754e438427f6550e109f995438427d6550e109f195438435e5350e10d754d438427f6510e109f994438427d6510e109f194438435f5310e10d714c438439d4310e10be98043842f96010e109f98f528427d63d4a10dd587528437a60d4a10dbd4a528427e6394a109f58e528437a6094a10dbd4e528436e5394a10db54e528436c5394a10fa982528436f6394a10db98e528436d6394a10db18e528436e4394a10db50e528436c4394a10dbd86528436d6194a10db982528436a6094a10db182528427f6354a109f18d528436f6254a10dbd95528436f5354a10db94d528436d5354a10db14d52843ea6054a10dbd8d528436e6354a10db58d528436c6354a10db90d528436d4354a10db10d528436f6154a10d
  | 6 => 0x2bd648c420db94a3108376518c420dd546310827f654c4209f595310827c654c420d794d310835d534c420bbd8931082ec624c420db9493108376514c420dd545310827f650c4209f994310827d650c420db948310836e52c8420dd947210837551c8420be98321082f960c84209f596210836e52884209fd95210836e5248420b798c21082dd6308420db94821083765108420dd54421083e52108420be98021082f960084209f98e500827d63940209f597300836e52cc0209fd96300827d658c020d794e300835d538c020bb98a30082ed628c020db94a300827f654c020afd9130082bc644c020db949300827f650c0209f994300827d650c0209f19430082be640c020af590300835e530c020d754c30082ee620c020bb588300836e520c020bd98430082f5610c020dbd4f200836e53c8020db54f200836c53c8020db947200836d51c8020bb58a200836e5288020be58a200837a5288020fa94a200837951880209fd95200836e5248020bbd95200836f65480209bd95200836f5348020db94d200836d5348020db14d200836e5148020db54520082ef6048020db94120082fb6548020ded95200827b6548020bed8920083eb6248020de94920083ea5248020da94920083795148020fac8520083e92148020af99353c42bd64d4f109f99353c433e64d4f108f99353c427d64d4f10cf59353c423d64d4f109f98b53c427d62d4f10dd98753c437960d4f10d7d4e53c427e6494f109f59253c427e6294f109f58a53c43766194f10bbd8953c42ec6254f109fd9153c427c6454f10d7d8d53c427f6254f10dbd8953c426f6254f109f18953c436c6254f109b18953c435d5314f109f99053c427d6414f10d798c53c427e6214f109f58853c43766114f10de58053c427f6590f109f99643c427d6590f109f19643c433e5490f10cf55243c42f66190f10bd58643c427f6550f109f99543c427d6550f109f19543c42fb6050f10be18143c427f6510f109f99443c427d6510f109f19443c435e5310f10d754c43c439d4310f10bd98443c42f56110f109f98f52c427d63d4b10dd98752c437960d4b10dbd4a52c427e6394b109f58e52c427f6354b109f18d52c436f6254b10b798c52c42dd6314b10db54852c427e6314b10d798c52c425e6314b109f58c52c435d6314b109758c52c436e6214b10dd98452c43796014b109fd9732c427e65ccb109f59732c427c65ccb10d794f32c435d53ccb10dbd4b32c436c52ccb10bd98732c42f561ccb109fd9632c427e658cb109f59632c427c658cb109fd9532c427e654cb109f59532c427c654cb10d794d32c435d534cb109fd9432c427e650cb109f59432c427c650cb10dbd4832c436c520cb10bd98432c42f5610cb10d7d4f31c435c53cc710af99231c42bd648c710d794e31c435d538c710be982
  | 7 => 0x3d4120fad4f50483ea53d4120fa54f50483e853d4120fa90f50483e943d4120fa10f50483eb61d4120fa98750483e961d4120ba58750483e861d4120fad4750483ea51d4120fa54750483e851d4120facc750483ea31d4120fa4c750483e831d4120bb99730482ec65cc120bb99330482ed64cc120bb19330483cf53cc120f314f30483ce43cc120f350f30482ee61cc120bb58730483cf31cc120f34c730483eb50cc120fad0330482ee658c120db996304826e658c120bbd9230482ee648c120bb59230482ed638c120f3d0e30483cc438c120bb98630482ed618c120bb98230483eb508c120fa90230483cf308c120facc230482ef654c120bb99530482ed654c120bb19530482ef644c120ebd9130482af644c120bb99130482ed644c120bb19130483ac644c120ab19130483cf534c120f314d30483ce434c120f350d30482ef614c120bb18530483cf314c120f34c530483eb504c120fa90130483e9404c120facc130483ce304c120bb994304836e650c1209b99430482ef640c120bb99030483ae640c120ab99030482ed640c120eb59030482ad640c120bb19030482ee630c120f3d0c30483cc430c120bb98430483e6610c120b998430482ed610c120f958430482e5610c120bb98030483eb500c120fad0030483e8400c120f3cc030483ea300c120f34c030483e9300c120f24c0304827e64d4c209f593530827e62d4c20db98b530826e62d4c209f987530827d61d4c209f983530837a60d4c209f596530835f5394c209f992530827d6494c209f986530827d6194c209fd91530827c6454c20d7d8d530827f6254c209f589530827f6154c209f18553082be6414c20af590530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209f988530836e6214c209b988530827e6114c20dd98453082766114c209f58453083756114c209d584530827e6014c20de980530827f6590c209f996430827d6590c209f196430835e5390c20d754e430827f6550c209f995430827d6550c209f195430835e5350c20d754d430827f6510c209f994430827d6510c209f194430839d4310c209f98e520827d6394820dbd8e520836e6394820db58e520836c6394820db90e520836d4394820db10e520836e6194820db586520827d65cc820db94b320827f658c8209f596320835e538c820d754e320836e528c820be98232082f9608c8209fd95320836e524c8209fd94320827d650c820d794c320835d530c820db94832082fa600c820be580320837751944209f98e510827d63944209fd8d510827c6354420b798c51082dd6314420dd544510827f65cc4209f997310827d65cc420d794f310835d53cc420db94b310827f658c4209f996310827d658c420af9923108
  | 8 => 0x20bb58753482ee6494d20bb59253482ee6394d20dbd4e53483cf5394d20bb98653482ed6194d20bb58253483e96094d20ba58253482ef6454d20ebd9153482af6454d20bb19153483ac6454d20ab19153483cf5354d20db94d53482ef6154d20f9d8553482e76154d20bb18553483e46154d20b918553482ef6054d20fad8153482eb6054d20bb99453482ee6414d20bb590534836f5314d20f394c534836d5314d20f354c53482ee6114d20bb58453482ef6590d20bb99643482ed6590d20bb19643482ed6490d20ebd5243483ac5490d20bb98e43483cf4390d20bb98643482ed6190d20bb98243482ed6090d20bbd9543482ee6550d20bb59543482ec6550d20eb90d43482ef6150d20bb18543482ef6050d20fad8143482eb6050d20bb18143483e86050d20ba18143482ef6510d20bb99443482ed6510d20bb19443482ee6310d20f3d4c43483cc5310d20f390c43483cd4310d20e350c43482ee6110d20bb58443482ee6010d20fa98043482ea6010d20bb58043483e96010d20ba58043482ee63d4520bb58f51483eb60d4520bb98e51482ed6394520db94e514836c5394520bb986514836f5194520f9d4651482ed6094520fa58251482e96094520bbd8d51483cf6354520b3d8d51482ec6354520f318d51482cc6354520f9d45514836e5154520bbd8151483eb6054520bad8151482ee6514520bb98c51483ce6314520b398c51482ed6314520f358c51482cd6314520db94c514836c5314520dbd4451483e65114520db54451483e55114520d954451483e96014520bbd9731482ee65cc520bb59731482ec65cc520bb99331482ed64cc520bb19331483ce53cc520f354f31483cf43cc520f310f31483e751cc520f914731482ee60cc520bb58331482ef658c520bb99631482ed658c520bb19631482ef648c520bb99231483ae648c520ab99231482ed648c520eb59231482ad648c520bb58e31483cf538c520f314e31482ee618c520f3cc631483e7318c520bb98231483ea608c520ba98231482ed608c520fa58231482e9608c520bbd95314836f654c5209bd9531482ee654c520bb59531482ec654c520db195314826c654c520bbd9131482ee644c520bb59131482ec644c520f394d31483cd534c520f3d0d31483cc434c520f9cc531483ce314c520bbd8131482ec604c520bbd9431482ee650c520bb59431482ec650c520bbd9031482ee640c520bb59031482ec640c520bb98c31483cf530c520f314c31482ee610c520f9d4431483e4510c520f3cc431483e6310c520f34c431483e5310c520bb98031483ea600c520ba98031482ed600c520fa58031482e9600c520bb98f50482ed63d4120dbd4f504836e53d4120db54f504836c53d4120bb98750482ed61d4120dbd47504836c51d4120fad8f50483ea63d4120fa58f50483e86
  | 9 => 0x59232482ed638c920db94e324836c538c920bb98632482ed618c920bb982324827c654c920d7d4d324835c534c920bed8132482f8604c920db195324826c654c920bbd9132482ee644c920bb59132482ec644c920f3d8d32483cf534c920db94d324836c534c920f314d32482ef614c920bb18532483eb604c920bb18132483e8604c9209f99432482ee620c920bb994324836e650c920bbd9032482ee640c920bb59032482ec640c920bb98c32483ce630c920dbd4c324836d530c920bb98432482ed610c920bb980324827e63d45209f58f51483775194520b7d8d51482dc6354520b798c51482dd6314520dd544514827e6314520d798c514825e63145209f58c514835d63145209758c514836f3214520db0c8514837960145209f997314827d65cc5209f197314835e53cc520d754f31482ee62cc520bb58b31483cf32cc520f34cb314837751cc520dd147314827e658c5209f596314827c658c520af99231482bd648c520d7d4e314835c538c520bb98a31482ed628c520be98231482f9608c5209fd95314827e654c5209f195314835e534c520d754d31482ef624c520bb18931483cf324c520f34c9314827e650c5209f594314827c650c520d7d4c314835c530c520bb98831482ed620c520ddd443148374510c520be98031482f9600c5209f99721482ee65c8520db99721482ef63c8520bb98f21482ed63c8520bb18f214836c51c8520fad8321482ee60c8520fa18321482ed6288520ddd4621483745188520be98221482f96088520bbd8e21482ee6388520bb58e21482ec6388520db94e214836c5388520bb986214836f5188520f9d4621483e45188520bb98221483ea6088520ba98221483e96088520ddd4521483745148520bed8121482f86048520bbd8d21482ee6348520bb58d21482ec6348520f9d8521483e75148520db14521483e45148520d914521483eb6048520bb18121483e860485209f99421482de6308520b758c21482ee6208520be98021482ee6508520db99421482ef6308520bb98c21483ce6308520b398c21482ed6308520f358c21482cd6308520bb18c214836e5308520db14c21482ee6108520f9984214836f5108520bb98021483ea6008520ba98021483e960085209f997304835f53cc120d714f30482ee62cc120bb58b304827e658c120bb98a30482ed628c1209fd95304827d654c1209f19530482bf644c120af191304835f534c120d714d30482ef624c120bb189304827e650c120af99030482bd640c120bb98830482ed620c120bd98430482f5610c120f64c030483eb32c8120fa8cb20483e932c8120fa0cb20482f961c8120fac8720483ea21c8120fa48720483e821c8120bbd8e20482ee6388120bb58e20482ec6388120bb98620482ed6188120fad4220482ee64d4d20bb59353482ee61d4d
  | 10 => 0x38823e6414e209f590538833d6414e208f590538835e6314e20db588538827e6114e20dd98453882766114e209f58453883756114e209d584538837a6014e209fd96438827e6590e209f596438827c6590e20d794e438835d5390e209fd95438827e6550e209f595438827c6550e20d794d438835d5350e20bed8143882f86050e209fd94438827e6510e209f594438827c6510e20e750c43882fa6010e20be580438835e53cca20d754f32882fa60cca20be583328835e534ca20d754d32882fb604ca20be181328837751946209f98e518827d6394620de982518827f63546209f18d51882de6314620b758c518837551146209fd97318827e65cc6209f597318835e53cc620d754f318827f658c6209f996318827d658c620af99231882bd648c620dd9463188375518c620be98231882f9608c6209fd95318827d654c6209f195318835e534c620d754d31882ef624c620bb1893188376514c620dd545318827f650c6209f994318827d650c620be98031882f9600c620dd94621883755188620be98221882f96088620dd94521883755148620bed8121882f86048620b798c21882dd6308620f948421882f96008620d794e308835d538c220bb98a30882ed628c220afd9130882bc644c220af99030882bd640c220d794c308835d530c220bb98830882ed620c220bd98430882f5610c220f64c030882ed65c8220db597208836f53c8220db94f208836d53c8220db14f208836e51c8220db54720882f965c8220de59720882f961c82209f993534827d64d4d20db58b534827e61d4d209f587534835f5394d209f992534827d6494d209f98e534827d6294d20db58a534827e6194d209f586534827d6094d20de58253482bf6454d20af19153482f76154d20bd185534827f6454d20cfd91534823f6454d209f191534833c6454d208f191534835f6354d209fd89534836f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209f994534835d5314d209f990534827d6414d20d798c534827e6214d20db588534827c6214d209f984534827d6114d209fd96434827e6590d209f596434827c6590d20cfd52434833c5490d20bb98a43482ed6290d209fd95434827e6550d209f595434827c6550d20bbd8943482ec6250d20bed8143482f86050d209fd94434827e6510d209f594434827c6510d20d7d4c434835c5310d20e750c43482ee6210d20bb58843482fa6010d20be580434827e65cc920d7d4f324835c53cc920be98332482f960cc920db997324826e65cc920bb99332482ed64cc920bb193324836f53cc920f3d4f324836d53cc920f314f32482ee61cc920bb58732482ee60cc920fa98332483e960cc9209f99632482ee628c920bb996324836e658c920bbd9232482ee648c920bb
  | 11 => 0xed6014f20fa58053c82e96014f20bbd9643c82ee6590f20bb59643c82ec6590f20eb95243c83ad5490f20f3d0e43c82ee6190f20bb58643c82ee6090f20bb58243c82ef6550f20bb99543c82ed6550f20bb19543c83ae4350f20bbd8543c82ec6150f20bbd8143c82ec6050f20bbd9443c82ee6510f20bb59443c82ec6510f20f394c43c83cd5310f20f390c43c83cd4310f20e350c43c82ee6110f20bb58443c82ee6010f20bb58043c82ee63d4720bb58f51c82ed60d4720fa58351c82e960d4720bb98e51c82ed6394720db94e51c836c5394720dbd4651c83e75194720bbd8d51c82ec6354720f9d4551c836e5154720bb98c51c83ce6314720b398c51c82ed6314720f358c51c82cd6314720db94c51c836c5314720dbd4451c83e65114720db54451c83e55114720d954451c82ed6014720fa58051c82e96014720bbd9731c82ee65cc720bb59731c82ec65cc720bb99331c82ed64cc720bb19331c83ce53cc720f354f31c83cf43cc720f310f31c82ee60cc720bb58331c82ef658c720bb99631c82ed658c720bb19631c82ef648c720bb99231c83ae648c720ab99231c82ed648c720eb59231c82ad648c720f3cc631c83e7318c720bb98231c82ed608c720bbd9531c836f654c7209bd9531c82ee654c720bb59531c82ec654c720db19531c826c654c720bbd9131c82ee644c720bb59131c82ec644c720f394d31c83cd534c720f3d0d31c83cc434c720f9cc531c83ce314c720bbd8131c82ec604c720bbd9431c82ee650c720bb59431c82ec650c720bbd9031c82ee640c720bb59031c82ec640c720f3cc431c83e6310c720f34c431c83e5310c720bb98031c82ed600c720bb59730c82ee64cc320bb59330c82ec64cc320f394f30c83cd53cc320f390f30c83cd43cc320bb98730c82ed61cc320f3cc730c83cd31cc320bb59630c836d658c320bbd9230c82ee648c320bb59230c83cf438c320f310e30c82ee618c320bb58630c83cf308c320facc230c82ef654c320bbd9130c83af644c320abd9130c82ee644c320bb59130c82ec644c320eb19130c82ac644c320f394d30c83cd534c320f390d30c83cd434c320bbd8530c82ec614c320f3cc530c83cd314c320facc130c83ce304c320bb59430c836d650c320bbd9030c82ee640c320eb99030c82ae640c320bb59030c83ad640c320ab59030c82ec640c320f3d0c30c83cc430c320bb98430c83e6610c320b998430c82ed610c320f958430c82e5610c320f3cc030c83ea300c320f34c030c83e9300c3209f993538827d64d4e20db58b538827e61d4e209f587538837a60d4e20d7d4e538827e6494e209f592538827e6194e209f586538827f6454e209f191538835f6354e209fd85538827c6154e20af99053882bd6414e20d754c53882f66114e20bd584538827e6414e20cf9905
  | 12 => 0x50f20bbd8943c82ec6250f209fd9443c827e6510f209f59443c827c6510f20d794c43c835d5310f20e750c43c82ee6210f20bb58843c82ed65ccb20db59732c82ee64ccb20bb59332c82ec64ccb20dbd4f32c836d53ccb20bb98732c82ed61ccb20bb98332c835e538cb20d754e32c82fa608cb20be58232c836d658cb20bbd9232c82ee648cb20bb59232c836e538cb20f394e32c83cd538cb20db14e32c82ee618cb20bb58632c82ee608cb20fa98232c83e9608cb20bbd9532c836f654cb20bbd9132c82ee644cb20bb59132c82ec644cb20f3d8d32c836e534cb20db14d32c82ef614cb20bb18532c82ec604cb20d794c32c835d530cb20be98032c82f9600cb20db59432c82ef640cb20bb99032c82ed640cb20bb19032c83ce630cb20dbd4c32c83ce530cb20db54c32c83cd530cb20bb98432c82ed610cb20bb98032c83ea600cb20fa58032c837751947209f98e51c827d6394720dbcca51c836c32947209fd8d51c827c6354720b798c51c82dd6314720dd54451c827f65cc7209f99731c827d65cc720d794f31c835d53cc720bb98b31c82ed62cc720f3ccb31c83cd32cc7209fd9631c827e658c7209f59631c82be648c720af59231c82ee628c720bb58a31c827f654c7209f59531c827c654c720d794d31c835d534c720bbd8931c82ec624c720f3cc931c83cd324c7209fd9431c827e650c7209f59431c82ee620c720bb58831c837651c8720dd54721c82fa60c8720be58321c82ef63c8720bb98f21c82ed63c8720bb18f21c836e51c8720f994721c83e551c8720bb98321c83ea60c8720fa58321c82ed6588720db59621c82ef6388720bb98e21c82ed6388720bb18e21c836e5388720db14e21c836d5188720bb98221c82ef6548720dbd9521c82ef6348720bb98d21c82ed6348720bb18d21c83e76148720db94521c82ec6048720b798c21c82dd6308720dd94421c83755108720be98021c82f96008720bbd8c21c82ee6308720f398c21c82ce6308720bb58c21c83cd6308720b358c21c82ec6308720db94c21c836c5308720f998421c83e65108720db54421c83e55108720d954421c82ee6008720fa98021c83e96008720d794f30c835d53cc320bb98b30c82ed62cc320bb98a30c82ed628c320afd9130c82bc644c320d794d30c835d534c320bbd8930c82ec624c320af99030c82bd640c320bb98830c82ed620c320bd98430c82f5610c320bb99353c83ae64d4f20ab99353c82ed64d4f20eb59353c82ad64d4f20bb98753c82ed61d4f20bb58353c83e960d4f20ba58353c82ee6494f20bb59253c836f5394f20f3d4e53c82ee6194f20bb58653c82ef6454f20bb19153c83cf5354f20db94d53c82ef6154f20bb18553c82ee6414f20bb59053c836f5314f20f394c53c836d5314f20f354c53c82ee6114f20bb58453c82
  | 13 => 0xdd547210c27f65884309f996210c27d6588430cf952210c33d5488430db94a210c36d5288430dd946210c37551884309fd95210c27d65484309f195210c33e5448430cf551210c2df6348430b718d210c36e5248430db549210c3765148430dd545210c27f65084309f994210c27d6508430af990210c2bd6408430cf950210c33d5408430b798c210c2dd6308430db948210c36d5208430dd944210c3755108430be980210c2f960084309f992500c27d6494030d7d0e500c35c4394030db98a500c36d62940309f597400c33e54d0030cf553400c39f43d0030db94b400c36d52d0030dd947400c37551d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd6390030e710e400c2ee6290030bb58a400c36e5290030db54a400c3765190030dd546400c27f6550030cf951400c33d5450030b7d8d400c2dc6350030e7d0d400c36e5250030db549400c3765150030dd545400c27e65100309f594400c27c6510030b798c400c2dd6310030e710c400c36e5210030db548400c3765110030dd544400c33e54cc030cf553300c36e52cc030db54b300c37651cc030dd547300c2de64cc030b7193300c35f54cc030e7953300c35d54cc030e7553300c31d54cc030f394b300c3cd52cc030f5947300c35d51cc030f5547300c35551cc030cf952300c33d548c030b758e300c35e538c030bb98a300c2ed628c030db94a300c36d528c030dd946300c375518c030ee952300c3b9548c030be58e300c37a538c030f694e300c3db438c030f610e300c3ea628c030fa58a300c3ea528c030fa54a300c3f2518c030fc546300c27f654c030afd91300c2bc644c030cf951300c33d544c030db949300c36d524c030dd945300c375514c030b7d95300c35f654c03097d95300c39f644c030b7991300c2dc644c030e7191300c29c644c030d7d51300c39e544c030d7551300c39d544c030c7551300c3ce524c030f3549300c3d6514c030d7545300c3d5514c030d5545300c2df604c030d7941300c2fb654c030ded95300c27b654c030eed91300c3b8644c030ee951300c3b9544c030bed8d300c3db634c030de94d300c3da534c030fa949300c3e9524c030f6cc9300c3d9324c030fc945300c3f1514c030af99353c82bd64d4f209f99353c833e64d4f208f99353c827d64d4f20cf59353c823d64d4f20db98b53c827e61d4f209f58753c837960d4f20d7d4e53c827e6494f209f59253c836e6294f209f98653c827d6194f209fd9153c827c6454f20d7d8d53c836c6254f209fd8553c827c6154f20d754c53c827e6414f209f59053c835e6314f20db98853c827e6114f209f58453c83796014f209fd9643c827e6590f209f59643c827c6590f20cf95243c833d5490f20bb98a43c82ed6290f209fd9543c827e6550f209f59543c827c65
  | 14 => 0x50320c36e520c830db548320c2fa600c830be580320c2be64d4430af593510c33e54d4430cf553510c2ee62d4430bb58b510c36e52d4430db54b510c33e5494430cf552510c36e5294430db54a510c37751944309f992510c27d64944309f98a510c27d6294430ddd52510c3765494430ed952510c3365494430dd552510c3b55494430cd552510c3745494430f5d0e510c3d44394430ddd4a510c3765294430f994a510c3665294430dd54a510c3e55294430d954a510c3745294430ddd92510c3766494430dd592510c3746494430dd18e510c3774394430dd90e510c3754394430dd10e510c3776294430dd98a510c3756294430dd18a510c3774294430dd90a510c3754294430dd10a510c3773294430dd8ca510c3753294430dd0ca510c3766094430dd182510c33e5454430cf551510c36e5254430db549510c27f64544309f191510c35f4354430d710d510c27f62544309f189510c3776554430ddd51510c3765454430ed951510c3365454430dd551510c3b55454430cd551510c3745454430f5d0d510c3d44354430ddd49510c3765254430f9949510c3665254430dd549510c3e55254430d9549510c3745254430ddd91510c3766454430dd591510c3746454430dd98d510c3774354430d5d0d510c3764354430dd50d510c3744354430d510d510c3776254430dd989510c3756254430dd189510c3774254430dd909510c3754254430dd109510c3773254430dd8c9510c3753254430dd0c9510c3766054430dd181510c3743054430af990510c2bd6414430cf950510c33d5414430bb988510c2ed6214430db948510c36d5214430bd984510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c39c43d0430db94b410c36d52d0430dd947410c37551d04309fd96410c27e65904309f596410c33e5490430cf552410c2de6390430b758e410c36e5290430db54a410c3765190430dd546410c27f65504309f595410c27c6550430cf951410c33d5450430b7d8d410c2dc6350430e710d410c2ef6250430bb189410c36e5250430db549410c3765150430dd545410c2fb6050430be181410c27f65104309f994410c27d6510430cf950410c33d5410430db948410c36d5210430dd944410c3755110430cf953310c33d54cc430d794f310c36e52cc430db54b310c37651cc430dd547310c2fa60cc430be583310c27d658c430af992310c2bd648c430cf952310c33d548c430db94a310c36d528c430dd546310c27f654c430cf951310c33d544c430d794d310c2ef624c430bb189310c36e524c430db549310c376514c430cf950310c33d540c430db948310c36d520c430dd944310c375510c430be980310c2f9600c4309fd97210c27e65c84309f597210c33e54c8430cf553210c36e52c8430db54b210c37651c843
  | 15 => 0xc27f62550309f189540c27f61550309f185540c33f6555030e718d540c33e6355030cf18d540c31c6355030cfd89540c33e6255030cf589540c33c6255030cfd85540c33e6155030cf585540c33c6155030cf981540c33c6055030cf0c1540c2be6415030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6315030d798c540c25e63150309f988540c36e62150309b988540c27d6215030db588540c26d62150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a60150309f592530c27d65d0c30cf953430c33d54d0c30b7597430c35d65d0c3097597430c35f54d0c30e7953430c35d54d0c30e7553430c31d54d0c30b7583430c27f6590c309f596430c33e5490c30cf552430c2de6390c30d794e430c2fa6090c30be582430c27f6550c30cf951430c33d5450c30d794d430c27f6510c309f594430c33e5410c30cf550430c39d4310c30be980430c2f96010c30d7594430c25d6510c30b7990430c39e6410c30d7d50430c39e5410c30d7550430c39d5410c30c7550430c3da6010c30b7580430c3d96010c30af993520c2bd64d4830cf953520c33d54d4830bd987520c2f561d4830cf952520c33d5494830dbd4a520c27e64948309f592520c27e61948309f586520c36f5494830db952520c3ae5494830cb952520c36d5494830eb552520c32d5494830db152520c3cf4394830f310e520c36f6494830db992520c36d6494830db192520c36c6394830dbd0e520c36e4394830db50e520c36c4394830dbd86520c36e6194830db586520c36c6194830db982520c36c6094830cf951520c33d54548309fd91520c27c64548309fd85520c27c6154830dbd95520c36f5454830db951520c3ae5454830cb951520c36d5454830eb551520c32d5454830db151520c3cf4354830f310d520c36f6454830db991520c36d6454830db191520c36e6354830dbd0d520c36e4354830db50d520c36c4354830dbd85520c36e6154830db585520c36c6154830db981520c36c6054830db0c1520c2be6414830af590520c33e5414830cf550520c2ee6214830db548520c2f66114830bd584520c27f65d08309f997420c27d65d0830cf953420c33d54d0830db94b420c36d52d08309fd96420c27e65908309f596420c33e5490830cf552420c2de6390830b758e420c36e5290830db54a420c2fa6090830be582420c27f65508309f595420c27c6550830cf951420c33d5450830b7d8d420c2dc6350830db949420c36d52508309fd94420c27e65108309f594420c33e5410830cf550420c36e5210830db548420c33e54cc830cf553320c36e52cc830db54b320c2fa60cc830be583320c27d658c830cf952320c33d548c830db54a320c27f654c830cf951320c33d544c830db949320c33e540c830cf5
  | 16 => 0xf6454530af191514c33f5454530cf151514c2ef6254530bb189514c33f5414530cf150514c37551145309f990514c27d64145309f988514c27d62145309f997414c27d65d05309f197414c33f54d0530cf153414c2de63d0530b758f414c39e43d05309f996414c27d65905309f196414c33f5490530cf152414c2de6390530b758e414c27f65505309f995414c27c6550530cfd51414c33c5450530e790d414c2ef6250530bb189414c27e65105309f594414c27c6510530cfd50414c33c5410530b798c414c2dd6310530be980414c2f960105309f997314c33f54cc530cf153314c2de65cc530d7997314c2df64cc530b7593314c39f54cc530d7953314c35c54cc530e7153314c31c54cc530d7d4b314c35c51cc530b7983314c2be648c530af592314c33f548c530cf152314c2dd638c530ddd46314c374518c530be982314c2f9608c530cfd51314c33c544c530bbd89314c2ec624c530ddd45314c374514c530bed81314c2f8604c530b7d91314c2dd644c530e7d51314c35e544c530d7151314c39c544c530c7151314c3cf624c530f3189314c35f524c530f5d85314c3d7514c530d7145314c3d4514c530f6d81314c2dc604c530f6181314c27e650c530cfd50314c33c540c530b798c314c3d5310c5309f997214c27d65c85309f197214c33f54c8530cf153214c37751c8530dd147214c27e65885309f596214c27c6588530cfd52214c33c5488530b798e214c2dd6388530dbd4a214c36c52885309fd95214c27e65485309f195214c33f5448530cf151214c27e65085309f594214c27c6508530af990214c2bd6408530cfd50214c33c5408530b798c214c2dd6308530dbd48214c36c5208530ddd44214c3745108530be980214c2f960085309f997404c33f54d0130cf153404c2de63d0130b758f404c39d43d0130cfd52404c33c5490130e790e404c2ee6290130bb58a404c27d65501309f195404c2df6350130b718d404c39d4350130cfd53304c33c54cc130eed53304c3b854cc130f690f304c3d943cc130f6cc7304c3d931cc130cfd52304c33c548c130bb98a304c2ed628c130b7d92304c2dd648c130e7d52304c35e548c130d7152304c39c548c130c7152304c3ce628c130f358a304c2dd618c130f6d42304c2ee62d5030bb58b540c2f661d5030bd587540c35e63d50309f98b540c36e62d50309b98b540c27d62d5030db58b540c26d62d50309f987540c37661d50309d987540c27d61d5030dd587540c27561d5030de983540c27d6595030cfd52540c27e62950309f58a540c27e61950309f586540c23d6595030e718e540c33e6395030cf18e540c33f6295030cf98a540c33d6295030cf18a540c33f6195030cf986540c33d6195030cf186540c33e6095030cf182540c33f64550309fd8d540c27d6355030d718d54
  | 17 => 0x86309f996218c27d6588630db94a218c36d52886309fd95218c27d65486309f195218c2df6348630b718d218c36e5248630db549218c27f65086309f994218c27d6508630af990218c2bd6408630b798c218c2dd6308630db948218c36d5208630be980218c2f96008630e7d0f408c36e52d0230db54b408c2de6390230b758e408c39c4390230db94a408c36d5290230db94b308c36d52cc230b7597308c35d65cc230b7993308c2dc64cc230d7d53308c35d54cc230f394b308c3cd52cc230d7547308c2f965cc230de597308c3ea52cc230fa54b308c27e62d51309f58b544c27e61d51309f587544c39f63d5130cfd8f544c33d63d5130cfd8b544c33e62d5130cf58b544c33c62d5130cfd87544c33e61d5130cf587544c33c61d5130cfd83544c33d60d5130cfd52544c35d63951309f98a544c27d62951309f986544c27d6195130de582544c35f63551309fd89544c27c62551309fd85544c27c61551309fd81544c37b60551309f994544c33d5415130cf990544c27c63151309f988544c27d62151309f984544c27d6115130af994544c33e65151308f994544c39d6315130cfd8c544c33f6215130cf988544c33d6215130cf188544c33f6115130cf984544c33d6115130cf184544c33f6015130cf580544c33d3015130cfd53434c33c54d0d30be983434c2f960d0d309f996434c33f5490d30cf152434c2de6590d30d7996434c25e6590d30b7592434c39f5490d30d7952434c35c5490d30e7152434c31c5490d30b7586434c2de6090d30cfd51434c33c5450d30bed81434c2f86050d30e7d91434c39f5450d30d7951434c35c5450d30e7151434c31c5450d30b7d85434c3db6050d30b7181434c3d86050d309f994434c33f5410d30b798c434c39d4310d30cfd53524c33c54d49309f993524c27d64d49309f987524c27d61d4930af992524c2bd6494930cfd52524c33c5494930dbd4a524c2bf6454930af191524c33f5454930cf151524c2f76154930bd185524c33f5414930cf150524c36d52149309f990524c27d64149309f984524c27d61149309f997424c27d65d09309f197424c33f54d0930cf153424c2de63d0930b758f424c27e65909309f596424c27c6590930cfd52424c33c54909309fd95424c27e65509309f195424c33f5450930cf151424c27e65109309f594424c27c6510930cfd50424c33c5410930b798c424c2dd6310930be980424c2f960109309f997324c33f54cc930cf153324c33f548c930cf152324c36f528c930db14a324c2fa608c930be582324c33f544c930cf151324c36f524c930db149324c2fb604c930be181324c27e650c930cfd50324c33c540c930cfd53514c33c54d45309f993514c27d64d45309f98b514c27d62d4530af992514c2bd6494530cfd52514c33c5494530ddd46514c2b
  | 18 => 0x9f986548c27d6195230cfd91548c27f62552309f189548c27f61552309f185548c33d5415230bb988548c2ed6215230bd984548c2f56115230cf953438c33d54d0e30be983438c2f960d0e30e7953438c35d54d0e30e7553438c3da60d0e30b7583438c3d960d0e30cfd52438c33e5450e30cf551438c2fb6050e30be181438c39d4310e30b7594438c35d6510e30e7990438c35f5410e30e7d50438c31f5410e30d7550438c39c5410e30b7580438c36f5294a309f992528c27d6494a309f986528c27d6194a30dbd52528c36e5494a30db552528c36c5494a30f3d0e528c3cc4394a30dbd92528c36e6494a30db592528c36c6494a30dbd8e528c36f4394a30db90e528c36d4394a30db10e528c36f6194a30db986528c36d6194a30db186528c36e6094a30db182528c27f6454a309f191528c27f6154a309f185528c36f6554a30dbd51528c36e5454a30db551528c36c5454a30f3d0d528c3cc4354a30dbd91528c36e6454a30db591528c36c6454a30db58d528c36f4354a30db90d528c36d4354a30db10d528c36f6154a30db985528c36d6154a30db185528c36e6054a30db181528c36d5214a309fd97428c27e65d0a309f597428c36e52d0a30db54b428c27f6590a309f996428c27d6590a30b798e428c2dd6390a30db94a428c36d5290a309fd95428c27d6550a309f195428c2df6350a30b718d428c36e5250a30db549428c27f6510a309f994428c27d6510a30db948428c36d5210a30be980428c2f96010a30db94b328c36e528ca30db54a328c2fa608ca30be582328c36e524ca30db549328c2fb604ca30be181328c36d520ca30bb98b518c2ed62d4630db94b518c36d52d4630db94a518c36d5294630ddd46518c27e64946309f592518c27e62946309f58a518c36e5254630db549518c27f64546309f191518c35f4354630d710d518c27f62546309f189518c2be6414630af590518c2ee6214630bb588518c36e5214630db548518c37551146309fd97418c27e65d06309f597418c33e54d0630cf553418c39c43d0630db94b418c36d52d06309fd96418c27e65906309f596418c2de6390630b758e418c36e5290630db54a418c3765190630dd546418c27f65506309f595418c27c6550630cf951418c33d5450630b7d8d418c2dc6350630e710d418c2ef6250630bb189418c36e5250630db549418c3765150630dd545418c27f65106309f994418c27d6510630db948418c36d5210630be980418c2f96010630db94b318c36d52cc630af992318c2bd648c630db94a318c36d528c630dd946318c375518c630be982318c2f9608c630bbd89318c2ec624c630db949318c36d524c630dd945318c375514c630bed81318c2f8604c630db948318c36d520c6309fd97218c27e65c86309f597218c36e52c8630db54b218c27f658
  | 19 => 0x5500877a3154021de4c550087783154021dec85500876b2154021de88550087792154021da48550087782154021b798c50086dd6314021d794c500875d5314021be98050087795014021cfd5254cc27e62953309f58a54cc27e61953309f58654cc27f62553309f18954cc27f61553309f18554cc33d5415330d798c54cc27e62153309f58854cc27e61153309f58454cc3796015330cf95243cc33d5490f30be98243cc2f96090f30d795243cc39e5490f30e755243cc35c5490f30b758643cc2de6090f30f698243cc3d96090f30b7d9543cc35f6550f30e7d9143cc39f5450f30d795143cc35c5450f30e715143cc31c5450f30b7d8543cc2dc6050f30cf95043cc33d5410f30e750c43cc2fa6010f30be58043cc36f5294b309f99252cc27d6494b309f98652cc27d6194b309fd9152cc27c6454b309fd8552cc27c6154b30db54852cc27f65d0b309f99742cc27d65d0b30b798f42cc2dd63d0b309fd9642cc27e6590b309f59642cc2fa6090b30be58242cc27f6550b309f59542cc27c6550b309fd9442cc27e6510b309f59442cc2de6310b30b758c42cc36e52ccb30db54b32cc2fa60ccb30be58332cc36e520cb30db54832cc2fa600cb30be58032cc2be6494730af59251cc37751947309f99251cc33e64947308f99251cc27d6494730cf59251cc23d64947309f98a51cc27d6294730bbd8951cc2ec62547309fd9151cc27c64547309fd8951cc36f62547309bd8951cc27c6254730db18951cc26c6254730dd54451cc27f65d07309f99741cc27d65d0730b798f41cc2dd63d0730e790f41cc27f65907309f99641cc27d6590730b798e41cc2dd63907309fd9541cc27d65507309f19541cc39e4350730bbd8941cc2ec6250730bed8141cc2f860507309fd9441cc27e65107309f59441cc2de6310730b758c41cc37651cc730dd54731cc2fa60cc730be58331cc2df64cc730b759331cc35e54cc730d715331cc35d52cc730d794731cc3d651cc730f554731cc2de60cc730f698331cc3d960cc730af99231cc2bd648c730bbd8931cc2ec624c730b7d9531cc35f654c730b7d9131cc2dd644c730d795131cc35c544c730f3d8931cc3cc624c730d754931cc3d7614c730f5d4531cc35e514c730f514531cc2dc604c730dd94431cc375510c730f54c431cc2fa600c730be58031cc27f65c87309f99721cc27d65c87309fd9621cc27e65887309f59621cc2de6388730b758e21cc27f65487309f59521cc27c65487309fd9421cc27e65087309f59421cc2be6408730af59021cc2de6308730b758c21cc2fa6008730be58021cc2de63d0330b758f40cc39d43d0330bb98b548c2ed62d52309f98b548c36e62d52309b98b548c27d62d5230db58b548c26d62d52309f987548c27d61d5230de983548c33f54952309f98a548c27d6295230
  | 20 => 0x87ad54cc821dbd4f32087ce53cc821db54f32087cd53cc821d354f32086ed61cc821bb583320867f658c8219f596320873e548c821cf552320875e538c821d754e32086ee628c821bd98632086f5618c8219fd95320873e544c821cf551320875e534c821d754d320867f650c8219f594320873e540c821cf550320875e530c821d754c32086f6610c821bd584320876d650c8219b59432086ee640c821bb19032087ae540c821eb55032086ee630c821f398c320876f530c821f394c320876d530c821f354c32087e6610c821bb58432087e5610c821b958432086ed600c8219f98e510867d6394421dbcca510876c32944219f597310873e54cc421cf553310875e53cc421d754f31087cf32cc4219fd96310867d658c421af99231086bd648c421cf952310873d548c421d794e310875d538c421bb98a31086ed628c4219fd95310873e544c421cf551310875e534c421d754d31086ef624c421bb18931087cf324c4219fd94310867e650c4219f594310867c650c421cf950310873d540c421d794c310875d530c421bb98831086ed620c421f54c4310875e53c8421d754f21086ee63c8421bb18f21087ce53c8421f354f21086ed60c8421d794e210875d5388421bb58a210876e5288421f594e21087d55388421bd58a21087765288421f994a21087e73288421f90ca210867f6548421d794d210875d5348421bbd95210876f65484219bd9521086ee6348421bb18d21087ce5348421f354d21086ef6148421db94521087e63148421f94c521086ef6048421bdd95210877765484219dd9521087d65348421f554d21086f76248421f9d8921087765248421f994921087e63248421f94c921086de63d4021b758f500875e53d4021d754f500875e5394021d754e500877b50940219f98e500867d6394021ded4e500877a5394021f694e500875a5394021de54e50087d95394021d654e50087785394021fa98a50087eb3294021fa0ca50087eb2194021fc88650087e92194021fc486500877b6394021de98e50087796394021de18e500877a4394021de50e50087784394021de18a500877b3294021de8ca50087793294021de0ca50087786194021decc6500877a3194021de4c650087783194021dec86500877a2194021de486500875e5354021d754d500867f63540219f18d500876e6254021dbcc9500876c3254021dbc85500876d2154021ded95500877b5354021de94d50087da5354021d694d50087795354021f654d50087595354021de14d50087ea6254021facc950087e83254021fac8550087f22154021fa48550087f12154021ded8d500877a6354021de58d50087786354021de90d50087794354021de10d500877a6254021da989500877b3254021dacc9500877a3254021de4c950087783254021da0c9500877a6154021decc
  | 21 => 0x6254d219bd89534867f6154d21ddd85534867f6054d219f181534867e6514d21d754c534867e6414d219f590534875e6314d219f980534867d6014d219fd96434867e6590d219f596434867c6590d21d7d4e434875c5390d219fd95434867e6550d219f595434867c6550d21d7d4d434875c5350d219fd94434867e6510d219f594434867c6510d21e750c43486ee6210d21bb58843486f66110d21bd584434867e65cc921d7d4f324875c53cc921bd98732486f561cc9219f996324867c654c921d7d4d324875c534c921bdd8532486f4614c9219f994324867e65cc521d7d4f314875c53cc521bb98b31486ed62cc5219f99631486be648c521af592314867f654c5219f595314867c654c521d7d4d314875c534c521bbd8931486ec624c5219f994314876e5388521db14e21487e75188521bb582214867e63d41219f58f504876f62d4121db887504877b5094121b7d8d50486dc6354121de540504867e63141219f58c50486be64d4c21af59353086fa60d4c21be583530867e64d4c21cf993530863e64d4c219f593530873d64d4c218f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c21de983530867a60d4c219f583530877960d4c219e583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530865d6594c21d7d52530875e5494c21e7952530871e5494c21f318a530875f6494c21d7992530875d6494c21d7192530875e6294c21d718a530875e6194c21d7186530875f6094c21d7982530875d6094c21d7182530873e5454c219fd91530867c6454c21d7d8d530876c6254c219fd81530867c6054c21d7d95530875f5454c21d7951530879e5454c21c7951530875d5454c21e7551530871d5454c21f3189530875f6454c21d7991530875d6454c21d7191530875e6254c21d7189530874c6254c21d7985530875c6154c21d7085530875f6054c21d7981530875d6054c21d718153086be6414c21af590530873e5414c21cf55053086de6314c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6314c21d798c530865e6314c219f988530876e6214c219f98453087766114c219f980530877a6014c219e980530867d6014c21de58053086796014c219fd96430867e6590c219f596430867c6590c21cf952430873d5490c21d794e430875d5390c21bb98a43086ed6290c21bd98643086f56190c219fd95430867e6550c219f595430867c6550c21d794d430875d5350c21bbd8943086ec6250c219fd94430867e6510c219f594430867c6510c21d794c430875d5310c21e750c430867e63948219f58e520867d65cc821cf953320873d54cc821d794f320875d53cc821bb597320876d65cc821bb99332086ec64cc821eb953320
  | 22 => 0x31de540500c67e64d4f219f59353c876e62d4f21dd58753c867e60d4f219f58353c875f5394f219f99253c867d6494f219f98253c867d6094f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c875d5314f219f99053c867d6414f21d798c53c876e6214f21dd58453c867e6014f219f58053c867f6590f219f99643c867d6590f219f19643c86f66190f21bd58643c867f6550f219f99543c867d6550f219f19543c867f6510f219f99443c867d6510f219f19443c879d4310f21bb98843c86ed6210f21d7d4f32c875c53ccb21d794e32c875d538cb21bd98632c86f5618cb21d7d4d32c875c534cb21d794c32c875d530cb21bd98432c86f5610cb21d794f31c875d53cc721bb98b31c86ed62cc721af99231c86bd648c721d794d31c875d534c721bbd8931c86ec624c721f54c431c877b50943219f98e50c867d63943219fd8d50c867c6354321db98950c87795014321af99353886bd64d4e219f993538873e64d4e218f993538867d64d4e21cf593538863d64d4e21db58b538877661d4e219f983538867d60d4e21d7d4e538867e6494e219f592538867e6094e219f582538867f6454e219f191538875f6354e21dbd89538867f6054e219f181538875d5314e219f990538867d6414e21d798c538876d6214e21dd984538867e6014e219f580538867f6590e219f996438867d6590e219f196438873e5490e21cf55243886ee6290e21bb58a438867f6550e219f995438867d6550e219f19543886ef6250e21bb189438867f6510e219f994438867d6510e219f194438875e5310e21d754c438879d4310e21bd98443886f56110e21d794f328875d53cca21bd98732886f561cca21db59732886ee64cca21bb193328876f53cca21f394f328876d53cca21f354f32887e661cca21bb58732887e561cca21bb583328875e534ca21d754d32886f7614ca21bd18532886ed650ca21db59432886ee640ca21bb19032887ce630ca21dbd4c328876d530ca21bb58432886ed600ca21d7d4f318875c53cc621f3ccb31886be648c621af592318875e538c621d754e31886ee628c621bb58a318875f534c621d714d31886ef624c621bb18931887cf324c621d794c318875d530c621bb98831886ed620c621bb597218876d65c8621bb98f21886ec63c8621bb58321886f565c8621dd597218877b50942219f98e508867d63942219fd8d508867c6354221db589508876f3254221db0c9508876f2154221b798c50886dd6314221de540508867e64d4d219f593534867e60d4d219f58353486be6494d21af592534875f5394d219f992534873e6494d218f992534867d6494d21cf592534863d6494d219f98e534867d6294d21db58a534867d6194d21dd586534867e6094d219f582534867f6454d219f191534875f6354d219fd89534876f
  | 23 => 0xb189504c76f5254131db149504c6be6414131af590504c6ee6214131bb588504c76f5214131db148504c77950141319f990504c73e64141318f990504c67d6414131cf590504c63d6414131d7d0c504c75c43141319f988504c76e62141319b988504c67d6214131db588504c66d6214131d798f540c67e62d50319f58b540c77661d50319f983540c67d60d50319f596540c73f54950319f98a540c67d62950319f982540c67d6095031cfd91540c67f62550319f189540c67f60550319f181540c73d5415031bb988540c6ed6215031be980540c6f960150319f98c540c75e63150319f988540c76e62150319b988540c67d6215031db588540c66d62150319f984540c77661150319f980540c77a60150319e980540c67d6015031de580540c67960150319f592530c67d65d0c31d794f430c67f6590c319f596430c73e5490c31cf552430c6f66190c31bd586430c67f6550c319fd94430c67d6510c31cf950430c73d5410c31d794c430c79d4310c31bd984430c6f56110c31dbd4a520c67e64948319f592520c67e60948319f582520c67f64548319f191520c67f60548319f181520c6be6414831af590520c76d5214831be980520c6f960148319fd97420c67e65d08319f597420c73e54d0831cf553420c6de63d0831b758f420c6f661d0831bd587420c67f65908319f996420c67d6590831db94a420c76d52908319fd95420c67d65508319f195420c73e5450831cf551420c76e5250831db549420c67f65108319f994420c67d6510831d794f320c76e52cc831db54b320c6f661cc831bd587320c67d658c8319fd95320c75e534c831db948320c76d520c831bd984320c6f5610c8319f992510c73e64944318f992510c67d6494431cf592510c63d64944319f597410c73f54d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd63904319fd95410c73f5450431bbd89410c6ec62504319f994410c67d65104319f194410c6de6310431b758c410c75e54cc431d7153310c75d52cc431af992310c6bd648c431b758e310c75e538c431ed992310c7b5648c431bd58e310c776538c431f594e310c67f654c431bbd89310c6ec624c431b7d95310c75f654c43197d95310c75e544c431d7151310c7cf624c431f3189310c75d524c431b7d85310c75e514c431f5905310c7d5414c431bdd95310c777654c4319dd95310c6f7634c431f5d8d310c776534c431f594d310c7d6434c431f550d310c7e7624c431f9189310c7d6324c431f50c9310c6ee6294031bb58a500c77b50940319f992500c67d64940319f98a500c76e62940319b98a500c67d6294031db58a500c66d62940319fd91500c67c64540319fd89500c67c6254031d7cc5500c7763154031d74c5500c7753154031af990500c6bd6414031bb988500c6ed6214
  | 24 => 0x434c75f54d0d31e7d53434c79c54d0d31b758b434c6de61d0d31f5987434c6d661d0d31f5587434c6dd60d0d319f996434c73e5490d31cf552434c6de6390d31cfd51434c73c5450d31bdd85434c6f46150d319f994434c73e5410d31e750c434c6de6510d31d7994434c6de6410d31e7990434c75f5410d31e7950434c75d5410d31e7550434c71d5410d31b7588434c6de6110d31b7580434c67e64d49319f593524c67e60d49319f583524c76f54d4931db953524c76d54d4931db153524c7cf63d4931f3d0f524c7cc43d4931bb583524c76f64d4931db993524c76d64d4931db193524c76f63d4931dbd0f524c76e43d4931db50f524c76c43d4931dbd87524c76d61d4931dbd83524c76e60d4931db583524c66d60d4931db183524c76f5294931db548524c67e64149319f590524c67e60149319f580524c6ee6514931db994524c76f5414931db950524c76d5414931db150524c7cd6314931f3d0c524c7cc4314931bb580524c76f6414931db990524c76d6414931db190524c76f6314931dbd0c524c76e4314931db50c524c76c4314931dbd84524c76d6114931db4c4524c76f6014931db980524c76d60149319b580524c76c60149319f997424c67d65d09319f197424c76f52d0931db14b424c67e65909319f596424c67c6590931b798e424c6dd6390931dbd4a424c76c52909319fd95424c67e65509319f195424c6df6350931b718d424c76f5250931db149424c6f76150931bd185424c67e65109319f594424c67c6510931b798c424c6dd6310931dbd48424c76c5210931bd984424c6f561109319f997324c76c52cc931b7997324c75e65cc931b7993324c6dc64cc931f3d4b324c75c52cc931f314b324c74c52cc931b7987324c6dd60cc931b758e324c76f528c931db14a324c6f6618c931bd586324c76f524c931db149324c6f7614c931bd185324c6de644c931b7191324c7cf624c931f3d49324c75c524c931f3149324c7d7614c931b7185324c7d4614c931b5185324c6df604c9319f994324c6de630c931dbd48324c67e65d0531cfd53414c73c54d0531b798f414c6dd63d0531e710f414c76f52d0531db14b414c6de6390531b758e414c76f5290531db14a414c67d65505319f195414c6df6350531b718d414c79c4350531dbd49414c76c5250531dbd4b314c76c52cc531f5d0f314c7d443cc531f9d4b314c7e452cc531f5ccb314c7d532cc531bd583314c6be648c531af592314c76f528c531db14a314c6de648c531e7992314c69e648c531e7592314c6dd628c531f3d4a314c7cc528c531f5d46314c6dd608c531dbd4b504c76c52d41319f993504c67d64d4131dbd8b504c67e62d41319f58b504c76c62d4131bb98a504c6ed6294131dbd4a504c76c5294131ded42504c6bf6454131af191504c6ef6254131b
  | 25 => 0x67e62d52319f58b548c77661d52319f983548c67d60d5231cfd52548c67e62952319f58a548c67e60952319f582548c73f6395231cf58e548c73f6295231cf98a548c73d6295231cf18a548c73e6195231cf186548c73f6095231cf982548c73d6095231cf182548c73f64552319fd89548c67c62552319fd81548c67c6055231cfd95548c73d6355231cfd89548c73e6255231cf589548c73c6255231cf985548c73c6155231cfd81548c73e6055231cf581548c73c6055231cf550548c73e54d0e31cf553438c6f661d0e31bd587438c73e5490e31cf951438c73d5450e31bdd85438c6f46150e31cf950438c73d5410e31e750c438c6be64d4a31af593528c73e54d4a31cf553528c73e5494a31cf552528c76f5294a319f992528c67d6494a319f982528c67d6094a31cf951528c73d5454a319fd91528c67c6454a319fd81528c67c6054a31af990528c6bd6414a31cf950528c73d5414a31db548528c6fa6014a31be580528c67f65d0a319f997428c67d65d0a31cf953428c73d54d0a31b798f428c6dd63d0a319fd96428c67e6590a319f596428c73e5490a31cf552428c67f6550a319f595428c67c6550a31cf951428c73d5450a31bdd85428c6f46150a319fd94428c67e6510a319f594428c73e5410a31cf550428c6f66110a31bd584428c73e54cca31cf553328c73e548ca31cf552328c76e528ca31db54a328c6f6618ca31bd586328c73e544ca31cf551328c76e524ca31db549328c6f7614ca31bd185328c73e540ca31cf550328c73e54d0631cf553418c6de6390631b758e418c73e54cc631cf553318c6dd65cc631d7597318c75e54cc631e7953318c71e54cc631e7553318c75d52cc631bd597318c77565cc631ed953318c7b554cc631bd583318c6be64d4231af593508c73e54d4231cf553508c73e5494231cf552508c6ee6294231bb58a508c77b50942319f992508c67d64942319f98a508c76e62942319b98a508c67d6294231db58a508c66d6294231cf951508c73d54542319fd91508c67c64542319fd89508c67c6254231d7cc5508c6be6414231af590508c73e5414231cf550508c6ee6214231bb588508c7795014231d758f544c67e62d51319f58b544c67e60d51319f583544c73f5495131bb98a544c6ed6295131d758e544c67e6295131db98a544c66e62951319f58a544c76d62951319b58a544c77561951319f982544c67d6095131bbd89544c6ec6255131bed81544c6f86055131d7d8d544c67f6255131dbd89544c66f62551319f189544c76c62551319b189544c67f6155131ddd85544c67f6055131ded81544c67b60551319f181544c77860551319e181544c67e6515131cf550544c73e64151319f988544c67d62151319f980544c67d6015131cfd53434c73c54d0d31bd987434c6f561d0d31d7997
  | 26 => 0x290c329fd95430ca7f6510c329f594430cb3e5410c32cf550430cb9d4310c32bb988430caed6210c329f992520ca7d64948329f597420ca7f65908329f596420cb3e5490832cf552420cade6390832b758e420ca7f65508329f994420ca7d65108329f194420cade6310832b758c420cadd638c832d794e320caed638c832db94e320cbce538c832bb986320caed608c8329fd95320cadf654c832d7d95320ca5f654c832b7d89320cb5e524c832f3909320cbcd424c832bbd95320cb6f654c8329bd95320caef634c832f3d8d320cb6e534c832f394d320cbce434c832f350d320caec614c832bbd81320cb7751944329f992510ca7d64944329f982510ca7d60944329fd91510ca7c6454432d7cc9510cb5d32544329fd81510ca7c6054432af990510cabd6414432dd544510cafa6014432be580510cb7b50940329f992500ca7d64940329f986500ca7d61940329fd91500ca7c6454032db989500cb6e3254032db4c9500ca7f61540329f185500cabe6414032af590500caf66114032bd584500cb795014032bb98b54cc6ed62d5331cfd5254cc67e62953319f58a54cc67e60953319f58254cc67f62553319f18954cc67f60553319f18154cc73d5415331d798c54cc67e62153319f58854cc77561153319f98054cc67d6015331b759743cc75d65d0f31d755343cc6dd62d0f31b798743cc6dd60d0f31cf95243cc73d5490f31bd98643cc6f56190f31cf95043cc73d5410f31e750c43cc6f66110f31bd58443cc79e6410f31e795043cc75d5410f31e755043cc71d5410f31b758843cc6de6110f31f598443cc7d56110f31b758043cc6be64d4b31af59352cc76f5294b319f99252cc67d6494b319f98252cc67d6094b319fd9152cc67c6454b319fd8152cc67c6054b31db54852cc67f65d0b319f99742cc67d65d0b31db94b42cc76d52d0b31bd98742cc6f561d0b319fd9642cc67e6590b319f59642cc73e5490b31cf55242cc6de6390b31b758e42cc67f6550b319f59542cc67c6550b31b7d8d42cc6dc6350b319fd9442cc67e6510b319f59442cc73e5410b31cf55042cc6de6310b31b758c42cc76e5210b31db54842cc76e52ccb31db54b32cc6f661ccb31bd58732cc6de64ccb31b719332cc75e52ccb31f394b32cc7cd52ccb31b798732cc7d661ccb31f558732cc6dd60ccb31b7d9532cc75f654cb31b799132cc6dc644cb31f3d8932cc75e524cb31b718532cc6df604cb31db94832cc76d520cb31bd98432cc6f5610cb31b798f41cc6dd63d0731e710f41cc6ee6294331bb58a50cc77b50943319f99250cc67d6494331d7d0e50cc75c43943319f98a50cc76e62943319b98a50cc67d6294331db58a50cc66d62943319fd9150cc67c64543319fd8950cc67c6254331af99050cc6bd6414331bb98850cc6ed6214331de54050cc
  | 27 => 0x329f19151cca7f60547329f18151ccb755114732ded4250cca7e64943329f59250cca7e61943329f58650cca7f64543329f19150ccb6d62543329fd8550cca7c6154332af99050ccabd6414332bd98450ccaf56114332de54050ccafa60d5232be583548cb6e62d52329f987548ca7d61d52329f983548cb7a60d52329e983548ca7d60d5232de583548ca7960d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cf550548cb3e54d0e32cf553438caee62d0e32bb58b438cb3e5450e32cf551438caef6250e32bb189438cb9d4310e32b798e428cadd6390a32b7597328cb5d65cca32bb597328cb6d65cca32bb583328cb7751946329f992518ca7d6494632dbcca518ca7e60946329f582518ca7f64546329f191518cb5f32546329fd81518ca7c6054632af990518cabd6414632dd544518cafa6014632be580518cabe64d4232af593508cb7b50942329f992508ca7d64942329f986508ca7d61942329fd91508ca7c6454232db989508cb6f32542329fd85508ca7c6154232de540508ca7e61d51329f587544ca7e60d51329f583544cb3f5495132bd986544caf56195132d758e544cb6d62951329f986544cb7661951329d986544ca7d6195132dd586544ca7561951329f982544ca7d6095132d7d8d544ca7f6255132dbd89544ca7f61551329f185544ca7f60551329f181544ca7e6515132cf550544cb3e64151329f984544ca7d61151329f980544ca7d6015132cfd53434cb3c54d0d32bb98b434caed62d0d329f996434cb3f5450d32cf151434caef6250d32bb189434ca7e6510d32e750c434ca7e65d0932cfd53424cb3c54d0932b798f424cadd63d09329f595424ca7c6550932b7d8d424cadc6350932bb583324cbcf528c932b7586324ca7e64d45329f593514ca7e60d45329f583514cabe6494532af592514cb775194532dd544514ca7e64145329f590514cb6f32145329f980514ca7d60145329f993504ca7d64d4132dbd8b504cb6f32d41329f987504ca7d61d4132ded42504cabf6454132af191504caf76154132bd185504cb7950141329f990504ca7d64141329f984504ca7d6114132d798f540cb6e62d50329f987540ca7d61d50329f983540ca7d60d50329f596540cb3f54950329f986540ca7d61950329f982540ca7d6095032cfd91540ca7f61550329f185540ca7f60550329f181540cb3d5415032bd984540caf56115032be980540caf960150329f98c540cb5e63150329f988540cb6e62150329f984540cb7661150329d984540ca7d6115032dd584540ca7561150329f980540cb7a60150329e980540ca7d6015032de580540ca7960150329f592530ca7d65d0c329fd96430ca7d6590c32cf952430cb3d5490c32bb98a430caed6
  | 28 => 0x98a5090f6e62942439b98a5090e7d6294243db58a5090e6d62942439f9865090e7d6194243cfd0d5090e7f62542439f1895090e7f61542439f1855090eee6214243bb5885090ef66114243bd5845090f795014243e7d4e4350ebd6090d439f9875250e7d61d49439f9835250e7d60d4943dbd4a5250efa6094943be5825250f6d52149439f9845250e7d61149439f9805250e7d6014943cf90f5150e7e62d45439f58b5150e7e60d45439f5835150f775194543bbd895150eec6254543bed815150ef86054543dd5445150e7e62145439f5885150e7e60145439f5805150e7e62d41439f58b5050e7e61d41439f5875050eee6294143bb58a5050f7b5094143bb9885050eed6214143bd9845050ef56114143de5405050f3e43141439f9885050f6e62141439b9885050e7d6214143db5885050e6d62141439f9845050f7661141439d9845050e7d6114143dd5845050e756114143b75924310e9d6490c43d79524310f9e5490c43b75864310ede6090c439fd954310edf6550c43d7d954310e5f6550c43b7d914310f5e5450c43e79514310edf6150c43b71814310f9f6550c43a7d954310f1f6550c43e7d894310f9e6250c43e75894310f9c6250c43e7d854310e9f6150c43e79854310f9d6150c43e71854310f9f6050c43e79814310f9d6050c43e71814310e9c6050c43e750f5210f9d4394843dbd4a5210e7e61948439f5865210e7e60948439f5825210f9d43548439fd855210e7c61548439fd815210e7c6054843e750c5210f6d5214843bd9845210ef56114843be9805210ef96014843e750f5110f9d4394443ddd465110e7e62944439f58a5110e7e60944439f5825110f9d4354443bbd895110eec62544439fd895110f6f62544439bd895110e7c6254443db1895110e6c62544439fd815110e7c6054443e750c5110eee6214443bb5885110f755114443be9805110ef96014443e750f5010f9d4394043bb98a5010eed6294043ded425010e7e6294043db98a5010e6e62940439f58a5010f6d62940439b58a5010e7e61940439f5865010f9d4354043d790d5010f5d4354043c750d5010e7f62540439f1895010e7f61540439f1855010f9d4314043bb9885010eed6214043bd9845010ef56114043de5405010ef661d5332bd58754ccb3f54953329f98654cca7d61953329f98254cca7d60953329fd8554cca7c61553329fd8154cca7c6055332cf55054ccb5e6315332db58854cca7e61153329f58454cca7e60153329f58054ccb3e5490f32cf55243ccaee6290f32bb58a43ccb3e5410f32cf55043ccb9d4310f32bb98843ccaed6210f32b798f42ccadd63d0b32af99351ccabd64d4732af99251ccabd6494732ddd4651cca7e6494732cf99251cca3e64947329f59251ccb3d64947328f59251cca7e60947329f58251cca7f64547
  | 29 => 0x280060004000000001e000c000004c011000c000007400c00d4003001800100000030034004000800c000400f0010011000800100000040004000000000200000200030001003800300040000070011002c00d000000200700000000017011c000001400c000400400b400800000220000002000000200240020008003003800800040080004006000401b000c00d00000040008000002001f00280020008002003800900380000038003000001b0004007004000e00f40010020004005c03100240030010010001c0020030004000400f0034017000c0010030002000000100000280000006000400400000080070003005400d001c0020004004000003f002000c0018000001c00600000010024005002401e00900070004000003400400000050028008000800300000000008007000c0170068000004c00000180010000000004000200500020024005001c00301680170004005000400d000001f000c00d00080060008001000400c0008005000c0020008001001400c00040020000025000800c001000300040030008030000c0000000001003400c00740050000001000000300800060030000001400d000000000180000018020004400200100090004005000800c003c014002c000000000000040050018005002401c001c004000c00200540050000001009802300000050008001000800b001c0030000002000c0020000003000c004005400000080000140002004c00900200000040001005c002000801c003c00e000000000000000028000047c0000088001005c00300500020008016000000f00000000000000003000c00100060014001007c0020000005000000400000020020000005800f003800100300000078000005c00e000c006001400c0008001000c0070020007000c001001c0060000016002800f000800300140040044007000000200140000010001012c00000000100000005001c000000401500080100000003000000500000170000000000801000040160010001000000200000020004067000400f0040008000001a000400e00040000008017000000000000220124014000001c00000470000004009c0360000006000801500080020008003000c002000c000001c00000080090000000000400200100040010006000c001001c0060024021000000200f0009001c000002000f004c01100000020008008001400a00440090012dd65d0e43d75974390ef661d4a43bd5875290f6f5294a439f9865290e7d6194a439f9825290e7d6094a439fd855290e7c6154a439fd815290e7c6054a43db5485290eee62d4643bb58b5190f7751946439f98a5190e7d62946439f9825190e7d6094643d7d0d5190e7f62546439f1895190e7f60546439f1815190f755114643bb98a5090eed6294243ded425090f5f43942439f
  | 30 => 0x60004003000c000000800600ac006000000200f000900080000078005001400000500000000005004c0030000004001c0000000018001c00100280000000004000c00200280000040000001400e0000000004c009009400b000001f000400000000030000000002401600640180240002001c0030010047002c0010310005000002700440000014000000c0100004020002800000100070000002003c0000000002002c00000380080014000000404100080000090001001801700280030004001001401c0074000002402b00140010084014000c007004000b0010000001000b000800c0010000000000a00040040000000002800700140100048006001400000080020004002000800b0024006000803d000000c0008003000c00b0004002000000000000060004006000c008001801600040050008002000400100200000014001006000300040000004000000004700000060000001000000000340050000008006400400480070038004000400100080050004000006c0040004004000000100b8003003400800040000008000009c001000400100000030044001000c0010008003001400a002c00e00000000000002000000a004c0110004000001400100000000014004000000c002c0020004002003800000240000000005004c001004800b00040020008012000c0000004008001c00a001c0020000002001c0000050019012001c0000000000c00000140010000000002400f00000000008011001c012001400800000040050000000400000040020080005010402600e80000020006002001b00080200000000001c000001400100a8000000000200080010044002002800300080020028003000400e00740060034012002000d0034011000c00500000010018006006400100b0004000000b0000005000000a000c00900780010054000000000000240020044001007400a0010000000400000840050014008001c02400140040004000000000400080020094004000801a00380360028005003c0030000023000801c0014008002804b0018004005c00000000030004018001c00b004c0100008002003c000001000e000404300000090028003001400000000040000008000000800080010018017000000b00140010074001000000300600000004002000c00e001400200180090084000006400b007c01a002c002007400e006c001004c01c00000110058013000000a00600110054002000001e000000b00080060000001001000000080000004019003c000002c018000000c003c00100040020014008003c011001c00c0000001002c0010000000003000200480160038000000400600b8000000800b000400000380000010000001000000580080014001000c005004c0050018002002401a00c4000000401f0038012009800700
  | 31 => 0x24008002c00000280120008004007c0020008004000000b00040280000016001400b0038000006000000400010008009006c0020048003002c00c0000000000801200280180000001000000901480000000009007401e000400e00bc00100000000040000002000700000000010000003400300a8005006c01d00680050004000000c000001800a001c00000200030004001001001c0050016000000c0004002000000500c0000004c00300040020024007000400c00240120000005002800400000010010003000401700040030004002000800000040090000015000400300000140010001000c00000340000004002004800600040270010000001000100d800100200090004002001000000040070078004000000e0008000002000000340010024014002800b001405800cc01a00480010010003000000000340270004012003c0000008001002c00a0000008000000100000090004008001c001006c00f001c001004004d004400c0020000001001e001c000000402b000801c0000000000801200080020008002001c000001c00000640040018006000800900040030010001000404b00000200000003002400900000090020014002403b003c0000000000000001b0010002005c0060020001011c025000000200140060000001000000000880060014010005c04b0004002000801700340010014000000002300000020004010000c00000340000008016004001b0010003009c00000140000054001002c0000000013000c0000068002000c0030028001006400100080000004000003c00a0000006001c0050024000001c030000c00a0000002006c0010018004000000000000030010001004400200c800f00240010004007002800100040070330005008402a00000050008007005800d00300050000008000c004001000f0038003000c0000024029000400d0004059000000100300060070005000402600000000008004003801c004c00a000c016002c03a003c00300180070018000000000500180090020022000804b001001e006c001001c01400140000004015000002100140000024000001c008007800700dc0020020000001400000180070010000000800e00ac0040000016000800001d00000000011000400000940090000003000000000480000014003000000400000190008005002001b000c0000000010003000a00000000030007000800a004c000005801c000c0070014003002000d000c000002400500340010004006000c000000800400780080000006013800d004c00200280010018012000800c006400b0000006000800200080020058002000400400040000008006002c00100180050018000000000a003400b000400c000400200000030014014001000800c00030004001000c0000004001001400e00000
  | 32 => 0x6002800000400020014019000402100380010000003000000e00040010088003000401b008c004002c00f000400000100020004000002800000140010008003000002300180040000000000400700c80090004006001000300940060020035000c01000380090010000000001100040170000016001c00f00240090000001000400900040060024007001000a0000009000c02700040020004001000800c0000001000400e001c0000000031000c00200080000044017000400300280060078000000400100000000004018004c0010008007000c00c00400100000001000c0020000000001c00d000001e00100050004027000000a001400800ac00c028c01900000020020002002800b000400000040090000000000c0090038007001002200100030018012006401f009400a002c004000c000000800200000030034005001400b00000070038001000c00a00300000010000000000400040000028003004c002005c00000100030000004001400a000800b00040030004000002800d00180030014007008400200280020050005000c000001000200180010008006001c001001c0060010003001c001003c00a00000030004002000c003000001e000800400140100000002000800c00040030008009003c003001007c0000007002000b000c043002800b004c000005800a000400200000070000009001800d00240010068003007000b004c00100000110000003000c00d00200000034005004c0040008003000000700640010010003009000600140580018006000400a000401700400010018006001403800100500008007000001e004401a0034014003c001000c00000600090000003000000100000000010009003000300000010008003000c0050024001000401a000c00200040110024027005c00d0018009000800b01c0005000400000180050004003003000200e8002000003f0028000000001500000000000009005400300100000000000000000301340000028005000000600080020008003000402000000020108001001400000000040000003005000500440000054000000400100140070004000000000100040070018000001c0010008000001c001002801e000c001007001200040000024009000c002003800000100010008002000000400180040014004009000c0000000001c007000000100280030000003000000e0034000001c000006800e000400000040080038000001c010000001b000400b003000800080010058008000000100080160024000000400000000100000005001000400000170020006001400200080020000001000c003000400200000030000009003401400640180000000000c00000c00040014005000000e0004004000001d001c01a006c025000000700000290028008001402900000000
  | 33 => 0x16198a1ed6000202136596ee1121228a2f1b384c416467032744911088a22acc219efa8fa0000000297d88003d2f52b9800002ecc00030f809e54da5207fe115e2fcec4e022af1aa891c6e00000006cb235ca3713120001fe8c0498f6bfa104e39189bb000046295d82eb03fa4322e607a08050000b4f2e351dba1322bfaf701051aeebd9acc06f48a24353180d60b0e068d5a16637988e6af616e4a2d91fe2791e2310a2bc06f70bc727588f63ab8885a8804d8190036619445ec1ab01585d42f949dc1f7653d29e884c04639ab878849aedbc60389d8205c0ea0000bfa86e021838d82005ce056681090ba95689de569275e0ba4c8e70c80000c440002e4a9ca6170c7c73e1d9e22e922e295a2440001c6900000000b8856c0a8400000016feba81652000000000011cc0000000a51d558ac2800003780007492988afa15dc2e91ad20000000180b0cc0000000744ae48000000000013c6bea9ad65d36dda1d2000000006de0001dda00000000002d806eba6d034aa34297e2633a7e854c5c30cdc88ee6880000b34871c5f8a818000a53a8468288000000144050952e63be000083fa95600000000000c05ac51a46126ad8e9f712db68d8f8021720087f3166401a06a40000000000000100240100000006001c0200024001000c000003800000980000000011000c00500300030000006000800b00000000024007001400000380010054008000000000300150060009002c00a000c007000000c0008002001c000003c00c006c0000000036000001e0018004000400b00140350004005000c003000000200000060008015001c0050000001000800200000040000000003004f0000004001401b000000000280180000002004c00100040000000020003000e00e005d000c00000100020068012000800100280110008022000c003008c017003400300100080000000000400000000350024012002c017000c00200100000000000004800200000010004002000400800040010008000000001c0060002005c00b004400300a4012005c00000080030024005000001200200000000000002800000000000000001003c00000f800d00000000070001001c003004001900d400d0048001001c0000054002000000c001800a001c0050000005000400c002400200100000000005000800c00780010030024000c007004c001004000500e4001000001d00000030064003000000a00040010000002002c006002c0070034000000000d0048003000005300080060008001004c010002400c00b000300000010010005001800100000080000004000c000000c004000000100180000000001001000600140050030005000000c001000900000010024001001800300fc00700000050020006001c004002c00200000010000004001400400180110004
  | 34 => 0x6aa155083c0ae8000c1302749c11e84887000028402779909eb900025d6c432e727f044867571ae140c0fad4279cac9fd9926394af24a7f2e005682cf86470cbac3120480969bacc2f8000953a6ac000000000000009c1800004b400096a9074308c44724c25de49569b629f26de4e5007e00027ec96b06c03c4080260241270d0400046a61fcb3c16d841c0bd286f6070c211b954fb611d771142e485663a09d985825b13609c0044b8db6a44a7b9dcc108143c7cad1c079f1c0e156873601d2a1128f12cba4d9478848ab9e33e123e8caa54aab1a2535c8803e6860d0e45d033ebe7160205887e617a0b76373a0b182dc11c93a9944508c95c7739fa01b70136b360fa2b17a38c25a2d6e062a7906ce8249c2b16a6ae0a1c48eb2235aad2256851d2041caa5a4b2322ccb5a800075d0cca3d912ce9cf2d68bb8676c5c6880c3030a5300b8e78ad4866909e1a4c0000868a7b2a942022c434f358b208380872b11d9800000003c49af38a9c00094a1af86ea46f84188e9c08200002dfa2ad00016fcb9e1ce37a181b852105fac03287617348bd1d41332000000000027c4bb3d9e03b92aac8e2152e1f8125c07992a2394e5e31d7e3a5162a9f8c36acae6a2a7c83bbe71080a1b8b883c5b284a9c945cfa85000011c84450e1ab255e8500027466328e69010c0000002de60d7951e78d03323a6013e98d92b2150ab7e6f650b94a7174ca77dd4d1db1b6a36e163255cadae5530f8f41c515305ec90662112f20b9cc5875f0cfa3ff800099e80000002a48655252e2b29cc44ab0a31c2d8a442a5400000007f718ac00000009901ae304680c8e0e7c913c5a58a75100003002c6932ea03ed8205e200285a80000001d7e0001c88c42134a9f400002ff80001ea05602c600006b612de00023300331ff600027665d6000069663583308de39f29d26b93a94c73880006b355420b14a185ba146c99c00008734cc4475e61c897303819f91a76418608b0d857629eee1c0aa4ec0b0cdf2d1feaaa2060198b2bf03bc52f8b08a398bdd00021ba9cc82fe7f285dc61fae04a268000bb490b4206955a00005df0d480002945d5e33631041ba800000000006616946538c9a221b9a789b1a5888379acc000000000000004398294000000044b0d7f789c680a356d9e123a0bac34800052d64420001a4229d55235789684997af3eb5cd6d0a1ab10e2b92dc0618ae5e71a85043558fb649e87581f7d7008d48000baf00000000000831000080a9ce47e49ae6bf89b8300019f80000000678a56a1ec000000000000002030a638722bf580000001262c4196ec0000000b9b859a3bf14da0001bc484d80007aea0b2053065a0000a6d89009800000000b6f9ace4148bb461301065eb00b0000000000029ffb04000000000003b21fce6db8000000000000000007180aaf
  | 35 => 0x877f0a1a3c687de9b80d90c3aa3f2454a7d183a015000020260fb55b26e92a640000b510cc29b267c00006261a9c0a1ede84611d520001b749534c1b030a9d4000078e45aa74f486a2673ac0f7807a5410b20eafaa9b2c8204b1c7509fc1c478594a022fdf883dbc434876924c0000e7a000291c0f591173090c020002e1d1062a9a0000000000241e000283a0b103a4615a5ee6ffb06e06c1dc500024dd11c40000000b8830280001c50b2300022a48e803df9762fc2b320b8e42400007fee7d606a706112625f420ca88452dc0008dc0a6c8b611ad12c81de3288f3669f146073f12ec5511079ac40863000001e08717f6b7f1682308235408fcfb43c08d08ade5c5e1f1275dad9aabe533e504000012200017bc827a59680d567a8002d4e2fa80001e413ec39240dc37bafe090b0b5f248943616ea35a13192702e014125f325100a887d10000000890849c8965db671ca1f74911f9e0000000a218000712000058100005fb000000023ce4cea4460002cac000014a2d31a0048508f400000000000000b6980007f4e202b6d1067712dbe239f4000adea5c8173c1b5a8b000028d00001ffa87c7214000b6c86c410fa4ed057e3a8421800000016660000a89699400069205b4a669132aba00000d7000000018e64adaba83a4800c7006826a80a320489000084d28003950000ad6800070999ba6712eea2818000000214c000094400000000001d5688e80000ac4a701edabca8ee97fd0000f580001334087400000024ccb57e878c0200005a615de58a2020610400000028c2603dbcc9d840000852210020400079e0766000071770100000000af2a88861eb25dda840d00002850000bcd13ff01480003d2978f38c80005a6856238de7388270f8ab3f091e0000000b4d29d0b0f85a26602eca13e1ee40001b324e21cb670c02f40abc00032d5c8a41725e857e23195050e3843d8d796292ef0c381c4ab41aaccab71b4a00000005e99508b1b0b8489f9e3810e0dac86cc2a849f1e5e2658d666976bc67ef2cf40002c550000e4e5b7ab900d1167e8ca15aa0f089020a8136c0001359895223d15ea9506e3e0161c32f98067a18cb5d1060b48291ab851aa68990d6f19f1d4925f15963dc287290d2afe1070b90180c0020000000000229b00000000000b2e25a986c0e99838a1ba2e200000000002bc83682c0c41b000088f95d2b1046d800010f2af484dc482302b89d805d0002a5d42c800039ac0008824275a1b0000442000000000005c080000000861293a1dc094a8ee0000000527083aa168b1e088c31c0c600006b18f3c000091a338201eb4c22a860d0000082a5a29f3d87a379109ab4e87204418d7c18c2b4a95b292c0e1152c53a800018b5c420000000000293e83aa7260909e767f245364dc61a408ac0b373d9cae597a90865001f4000
  | 36 => 0x35b582ae80005a5066e84ba34e152400001380004e7283c9c6800005b00003fc22bc00007008baa2b21bcaf686af5ede8b2189e0eb2b8032f000000020c8000000000008747614234beca04c6ea800091e0000c29800000000008764000af817b2000172919503043db4b0c0002953be59ebc82fc00054f132024617b69d380000001e8a0000000ac080008c0859c34362241d71f0287213cf78748dc91dea42a488b5091a2a8215b8ab415cae1695fa8b935610b67a80b265b3800072725d0763a39889a800021421b41168dd615e15ca3bb0084b9295842b19462640888802ddb7e559191008128cb2982a0821016c46a34b005b22b2586641322ac40004e800008c5d9e4453a2490001a72c3da4d47ed185a39980007e3ae1a3189de220d400048bda45bd1d216ba69bbca3126925ce8000baa041a094084d596aad77f66c02ad106f00002a5c043cb9c00017aaad807d80002b243aa839cb6a12a62708383aa62ef479c04068c98dde74162328759c808800628894a94099128700000636131304e73740002bc0a2eb0d219800000000002dcc3d8201a94c802008a5aa000000000000000000000098429ce000000000000005889ef28852ae2291844caf58c33a2b057e1b89c1c2ed8000a7fa9749b526d217840fa0a2c9ac00000a0000255800015017d58c8a134b0ca9e9838863e174051722a68071166b772e0c3ca2c58ac6800020e530800000005720000325079e00016e2000033a904988eb0f007c3d3442e67400007dd1e1e98b20be35c00002d1c0001a61c4d000000042207b4b8b253eb15a7bc61501464d9800019708d2000071f000070ab39253400005da6142e94000000039a80009a7a42600026404894000934800033a70e489a12064652694882af086ab148ab0a83a13a013cc00f04f500029de32d8be5443026e04d23d29f7862c4e601427b324b2bca0d6c34a1084aab9e8f74a8abc292993a36d00000000236a57922a9c300009559ec27941342891cdfa9290cc90fd830a0000000544d3bc93a233e000191a73488a509c0000b089b86ad3239e22a06766a304e0000273e0002b6a22015e888e4b3639cac0a78c8e459272c235d290aa23b409638f8000465a1ff3290e6296703af37c29f0096eb566ac94fe02ee72c9ca07aa0000a2c95762d630740005bcedc427b019c9f5c0003f1f03c71310c478deb967702e869cf424894785f242929395c347d63181d846cd2a7200002e690a0cb45ded80b41f053ebb38998abca300808a9ea98d0361084da5c189132813f8c04ac3c424785550c0000000a56163ca83c2f03bb800094040004db948e0001a3a0001dd130502ad02e41a4a4088965dba8480000000199a6b2729800000013bab2f88780c98f0600029c468226f6000245e00000007174e9f04fc0b2344487907443f
  | 37 => 0xc47a50000656000056980000000000000000000020d61ff0000000076a0c66ed62ee2e8c06195f1207800000000007b99bde60f2a9e00025860bc904a36a9eb083c802606651495c0400051e8000265000000021d00000013000000050800006ee04780000836c08268437da76a13a888e04795d800001726b008a4bd52d549f30000aeb970b7f8c0000f4800000000006838adaa04101217e6450a37400077fa0660000000751a9e6000031500008ec509dc3d47d000000000009a2571c000028a00021c6657858000030c06baade42da2ad20000825000226681068f80000280174054a0f7062f8fb2a809d52e3700003f0062c0000cd800059bab3a00000001d6893e36907ec2300b22c201df4531633a9570000000103a60c8bd684eabd0beb8d340000fee098977c65e0000a8f9a20000000043702ac019080126c8b1c084480d000271c00beccc51f818d1a0a4804d914fc8e70d740000000b5f80007a7a4606c181a27ce00000000b5e8a42bb80ad812a9bf15ce5534757aec0a8e57404a80001bb47b3acb400000003a6b010a3ca1f4235616c54cc00649fa85c00000000001d6f00001c08f2a60e000000000023e25ca81cf811d50a0000b4b48d04ab62d1c665c466b6af0897536000001fd1d5084f5c5820b50fe0000000000000080d800000027b64e4b0326c200000000a321fba8b01002a1a70b81e7000159440064071e3e7c6bae00009b3a8900000000000000000005140001767b84088120a869ec3a0ed671ec0007c9b1106ba147606b9d4c5a4203e25baee2a0bc6e9b40299eab08000b89a89881c884566562584ae13a4a7d508e15c08f2979e81c1e596d2ac301168dce43c37d12c920128f00c7e8bb26a8ede7ee2c2e8ae8e5e7078660c3f80764fed81822184709229444b071138a64a86205930247419c18a1498c281694c21d127823a8a6cc5c62aec4da84124b41e3c43a9678c22823dbad800000010d553280006ddcc801e18cf368ba8d4b8f9feabafad180c359d245000348db861c4208d36aed8000824846f68894720001a329bb2a1f000000064c80004460000700a5e6c0b00009d2a6860002736758251c7b20854a10a9a47ce8dd26438c7f714a737a7cafd014ba1b03810c4c75ccd883f11b5c14c807836ed7d4ada210eadd4c0f5efadca3a41956000240b57c800057da7b293faaa07ec17ae96826809d20000537aa70000307e7b80000bfd1a1400000007750b67000275c40b12f861799382fbaa8a02028a45708f999920dcf4d6053a30600000001c7900882a488f10be0160fea928223814084e60000cd676040000001d4400000003f60000772000083516da89f5a9e9aa2bda349229e9d0d03663f11e224013e280e988207f08bca7b4000227c000000000091fd1de68f882659019fa73a00008918bbe91
  | 38 => 0x40872e98b8de030482300468e214c1889286121ebb24e28988b8a6f48883315da26a43fe80000001d5a762c1048830c082a7115692e80009340000a3a9aba0e9e1a8b3798b823410945de1bee87ed2464135e590001cce297a400000000000012ca3c523bc608c000804a866826ae8e40b9ee862f08fe4bba5fc786e8d7c35125400002e1676ab763520bd803f64ce3570aa83f29dacc30a37a00c80000bec0007b6148617ee0fa9029b21238eda763c920e34c25e049625da4c6aca63ee9966a5103b61ee1f1a5070eb29f600548ae17ee46893f60000fdc467a888a80dac45138a67bd12e9e43f1eec0001a9a84a0000b409d5f0000f357bb81da0001788acbe90ebeb117e3e9abee245249a0000818049a8ce8b924664a180003dd1be64a202ecb499f3200016dc755c0005438e79bd80fe54e19350545176c58c247c27018103c00492a590000b8c8000c2080005122a7cbc81f2a8bd4d728a3e5187322768abb8b65b720f9b46f0e504c30334b1402906dc1ebe080c7ba68104503a99af29b6a72255d0dfeadb5b9c60981faaa2000000025b200012fd4498000000240546e1162a6e9f8a1c04e48858048fc39a2c770594502f8405e7db9d6ebf4a35f7c713764f5a4f65e6a3c1b909e648e0ac086488a90447106e1ab80003f597f25191e1a725a1bb00019ec46cae54663a15e7dc9dc754600ca40f29989af1ed2b1b8302b6a9066b9f2ed14fe6c917921bd82efc0293d19c8ea0e2474b778ab20f6852203b0d9327193486758a2267a05c6a0a85aeb8d96f12f829e05a1871047a0b7c4c010e19891d029a0e3793489e9641400b60b75b64309c08989b9a6421b00a2b658c6607490f48a498222230d8c865e55321315e0986010e2e79ebd19ccd606cd8d2600000001472b67000000085a00000301eb22ec0f8c39f1e72c029e9b2f02284000000012980001f31746ae31918192033838d03e2a1609dac3383827c316586b415c06caa3929df8670b27914500017eabcea1445d20e030001e5223a801a00000000000c7a00000002f70684a98872804c023ebff8a081830a88610a10039714e6222d654430815748e0d6447ce2a30000e4c2d2abaa892c0004178dad790a9e59bc898c4790000000000000000006c2956c60d9d4820283b100011dabbb1f707cd0dd00d6885a000106a0b4a11e3b4d87c17d98e2279a6980250b04533300e54199ae531811b3ea0000aea6f30774a7ac22c1b3c11b55b69a58000ae380000001dec19f6feab7c00007819e6a06382d9af30000a549fc30000000000000040a92b449e2ab687f95888aae3644878a6847f1a7048256f51df89cc0fc8000b521137b4400000001e330b0071d3878cec8ac4174a67038a9d66f7242768de3364216872db001c1c5aa00000000001b105fdea7a2c0824621200006f589
  | 39 => 0x7845718d5a3a3230cc25262276f9a0245f2b6c939a1af24a9ff2212842c4d3194a80953eb8010fbc00000003661b2621112a8b011716000112a1ecab8a27a1e07841a50c9ff0916a84c00000024ca0000c345161f980001cf400004de5b089b400017d600000003a1641a25ec5580000000000000000000004729bbe4e11a246aa9ef60000000190e5683f380008bce0466db0d9c1e9669a0f2002c08f1296c01940e2ad86e6ad8800014a2ce08b4ac359c62b3200030ec1b318a6b988e0c1c09ea18e4172388a461063a84bc22b2e0642068d922745cc5f42aa60268ae62681ca800000005fd00005f0800000000002b5830e83dab2200000006cc1fc221f94d3575ea74000000000018cc3fb2764b88478b046614357997e4b1d28cc37350d652f029f65b468a925309e65f6b08a29a103b61e62a9dc800000012e20002df27b72b5464d8e5a2d626001236f5841dec4655d6d651f7017e1dd2a09b3d99f406d8e319dd83a8a44ad64a5521fd46ba2aa99ba3f063fa0ca03ef0dcc3ea59a813847e000145ea8055201089e2554ea0fca088198444a58a0000c6c6c098945312b091ac8390bc78000004861abcaa57c36ac97e00023fa30420d20b30f86526a9371126cee85f88aeb51818400030880000f2269680a15cb0ab90001d221059c9e3ab20c00631c065ed2b9a237802485d83146d486b06c397c8c199042aa3ab0d9eea5421f888779f34000b061f0811366a07575c9871dac64879a7e242b1cde98c90130000268bcc9e8011d9e31416c24c00003121b1a2510002e6c9dd131e96e80002690e614338000a20118c70a8000000048058e211a214800035b96ca00029dd6f38000000228a00019120000000bc3267877a85f3000189a215a93000002df96c1e360001ce0343d4d8b3a0000694d2020000d8a00018a800006230000253bed15a20000000a9989d20002ba44f1e4142358db2a948000000000046aaee61244000319245c00009509d14000184dd347b1800072e000037500003f8e0c28e5aab804dd7a86fd8c0d6e3400054c8cc70000f373d51ddc6af93dc00029bc0e8c0001f0800031127d926b800018fe4f000001cc0b583b21fc0ecdb6c1d1c16183728bd146a57ea5ea4ee01c5c1f0efebe229fb00000082d1a1ea9ac2d671f3c00000000003d3830b00000005dc259209282de69390c808188e7664851e6c549406651a572e0697000000000001e5a0001dc6c10cccc5045890c239f0000000000002b6b0000c4ab420bf2000100c9024ad8458000000004fa4cc0e4b00011e0000129e6c5000000028a87b36ef6000000000029b4aee8000b9a0000000031e000000098c00007ec970a7eaa8ae37b21e10cf14a856413e33bd1186903aaf675a8000b2e80000000000a76c000000000095c9ac241a5230b0e04f6706a2bf0
  | 40 => 0xb2c27a41ad000095e12277151f2e00022154014000000000000023c214680005521ca0000011086807b5878151a6541b4000010fa000089a000125a00023662f1000059700000000e16210cd140f502510000bac1de836a2c9400000001d45fa03780000000000000084feb843768000912a34dbf22676830ea30a7684d46d598ba8a21fc88f32d4c9b0222c153a6ca7442a04588098a92aad8104d6f18b8b68200ff96c07fd1429bef9e9d41201593b08f685be400061394ff24c940c0000c9385eae2a6a504b9a035f862a4829c00026fe26faa12b5c9d8220c0e1c0001e7e173a099000000074e1878000130ea250a04378ac9b8e685b85bbe23f863aba69f00f8836d931182d8000b95a8fe150000037c9b9644ba0b3177a9be0001e7a29baaca36250ee97e8be824707a4170206597b04fc73c8e308beac597c49afe056852b45d8b10bff10ae7de26b475d8942351215a19321e3a0b9fd5400937428de3b45d72dc773feeba08b212475a2c4b3c70a624169104a05942f0bd70560c3ea9601bac4a05825a6a34e18853583aac2692760000f7cb95e78eb17155c11388608790b120158e705cfc000370d424b751d2e86a48caa6a909c0000118b16971faf713e01b523dac1e23744058bc853a40005ae0d508c3a402b579f600002f104ed2d5901dc1ba2aaa96a0be800050a11907a6800035340008d82490296564c99f2ca013b174910a640d29fc4303dcad1e52524b86d31dd0361a2255cd050a25b40e559c23be5488ea14520bfb1c62c128cd22bd14e0ea800021b20b24000346e94f63b234807589fc4ff120a7f59432a9ac000b4b1e871d821c2b0a0c6a1818c43168000078a1c3a05a305c63c0ca0b94932a0002c6a895e960b205fdc33d99febc509b606a87762839c92447896f0000370bd6a7b426f2c803ae838cbfb8000b4e00004e300f3950c000bf90675000248960c0000aa4884e93f2a2a000000028fc3ee75e817c914a6c2c241af656d1efc0ac8f3b690000018012109ba94e25300aa40000bae7cb237867bac45b5c0fde00000003d88000926000017b40000000cf2787303167393467ab28d80001f396f40f9d651801c08780008b4000041ec7943f055820000d92000018229fac4c4ba0833841214000018480001f960d2476275c9cc0a8a2f45bb0e71ead081c2c37860aadf00006c31dbca7e643e0000ac047180288f64000ac7ad784a280002dec06a4d58c1ac00214558900001a50000876c0916101fe2945a523309a926097b0e2aca1e0c0001d0300023368f74d2eada4da2000000000000000000000b6da31600008d818f8000000147405700004d955e4bbf9a12bf5192e57f800000000009ae80005e32e824bf8ebe00028921ce20b071ad5beb1884f9789958032aad628d74d715ee14d49f081144e3e72e753e
  | 41 => 0x9f660000b93a0c009c90a99be0f306043b80dbe889cb29882c5bc2fd800051516a266cacd2552c7615c42f42a431260970840892f1d28a9401cb475a53abb7a75a17aaf4c66a93e8ae8230aa7d8e4a0000b6fc322ef269b019005f46112548f5246700003bc14e57591c4e2d8ea5e41e2b9d407a91497523f8883553020e114272910688a4631012418eeb09076896a23327d089f6bb00cc5b89cf20a1506d6488eb1281f9c566de2eae8818cac7f868daabf0e9b30b087c8c11be8c1c14b4b52e420071d2d29e30544307c1e438b274722416f8a72305887c1b9e6a0c09086a866b6e246123338cb200030c64d71f3002a11ce9e72a5a23b9a795d0980c25ea8440001abb6fe247a7ea0000bc0964e71708ce1b6a424c0ce674885c719314252c7c3a06e00011ba03d82ed8fd96080a9ddb478804a56dfd4e1a4b490c87b40009301a5f1c962f99fb9aca8e025821186fb096f80008fd00000c80edca6c21df0001f5c649040ab0c80008b3ac40000108f4c9211371e83429b896360001a167781a67b308000bab081200010a06e63034ae520a83205b2290887460df890a355f076193ae152b80cfe6568b74bc5816e3730ab30bddd40bb24f048f6e40c462af6a3494946a0ec9ba993913e5662a264f25a28c17800050092fa55e047a823825d1d31dd812094ce3b51ea90000000642265cb9d23063a0d1d559094b816dabe6000000070a000065c1e0aa0faa000000000ab02b16470a3b81bf9168000288ead700310eb5be024e80000002635b569f198a312a4817ae8a1dc2868bea14e72bd00d8219a29cbf1aec264a16cc13ddaf45af0fd252bd556988107f1ae9610b51065038912ba5c5080e7a8c1ee81d238bc1280002f98050000196ab2f087a0000614469816a0bd809893e92d4b7b2e849382b066f28348bcd85744cd9a505dab01e1f48d3a26388adc0525c69ae00000000000000261200000006c78912208ce13000217cc0e8d1a9fa8dbd20702d00a59bc29bd288a52e50a8b2d89e29e7cb3a084a3fe81a305235380ae8380ba691585d52179790a771cb41441aa45a32bf26799ea81faa223b8386bc9546d94321087546d80000000000a340000921c2054116df60000f080000000a50a0d80e500000000d1900003c60000000034da0c29c47ff19d13540000f917bd0000c2a30fc23f1c5a000280cbbf1e74a5e17629420f7eb8a1a471a2224a55f06ee62f899200009b90ff159c0002e46be5d39d6a1116c1a892c25408c3a54f944ab4b880b6e1ebec6410468bbe23c800021e895486e7a30101d1a680003f520a9b85cc900000000a575916000258c00026088861876780000021459a02b4992a7a700000121c241d007f20000d7b55a02ef0001caa0e0021a534024f8c21b445c792ea81628ec4e88000c3ca031c2880bc1d2a31a
  | 42 => 0x200014b10000000583a9332091cdf883a63150e92326cb89b8b2180006a0304731d1fe0b25093c8729524124e59ec1d24829bb9f68bde8a7d9e78289696ce99391c66d0a9a7342389d4e858554e59414b202b2b04b5b67ef11a8e4d585aecb409a2dac2c0cc82f0a6e4b56cd0698090bc2e9c426952030c9502d428101ab8149a5c49df2a18bfe94468a6abea08404a75148d10329b09278116df01829f344902880d422de4b90a287d31c748cb89269d32da05898a3060f80d29222108141afec33907e17c5b03e67c95520eb9504aa11da62252fcc68d2580998845e1e0a7881660d9480b0c7646b037b0000c16506a05641ac00000000000000f2660e4f6eb540000be3000062180004df19bcb24023a4902b634f980000001ade82b0000972abde7ca28cd2ca0e407d2a7520002b00aa323e40000000000000052400002330f187e1266cafe4000726a0943fa00000002eaa0001f9a3268aa664f28146f90000000108ca618000785cc4e25dead91d380003ba0f3e1f0070e46491f15f28afab4530ae0ad49729770a868bf82e53d11d1e3eb293fc0aa02e3efad9c0001182000198d662a3143a10b626588862602ac006e4e25a99191a0021526c1aa1abc178235eb4ca064be484a4bb15c0077e93f49730ddcbb51a5e2828ca85e12078c261d0e878af38000000000028360000e56000196c000226000021de8d400002ba800071fa3e0000122c000053070d04f48a64b5a0000000bd44000600ab1c00028d200000000001080b18e0aa00000006d796ae390ae50b760ac8ac84a380002934ba8aa3c6c4a7a50000000ab405e43e0a1ec05587047329fc000000002eb52a00001b423d5afa2607a2e00001e40a0c9cb218800003b2814434b00004d4800000000003af1b9a8a014348f5af95aae93c049a9d3e5f3963a12b95b81e45bea762a10c89c9860bd430025e580000002f6293b2ad8000000000000000b1c176c2c80002f4ed0a567826400000000b6216e00007d08905322a5b8c5e9058000aac000000000004cf800009e675500000000001e4eb6e000000000006bc1128169189600016b00000000b9240009cee5940f791f62dc000018c6cfa205afce5d2d422000198600000005221d1801b09fe339c000925819a2394000057a44857cdee20000c8c0000d518588fab0050000000272a050134e9191fd851c2ba272f0266000198c71f6b589f50934ba980e44fba8d63d6af400e68dd8bf98e881ad900000009561638a1600000006b8db846d8afbc61ca9160b211100c580c80000a2ab1529412cfa4f49ec000073400009fa5e9f6d1837a443aade4ea61d8275281219e9a6d884db90487ca8c88104652598340549aa8682593dab68ac60b86199c1389a1a405252603ca3722565ffa39daf2235a8a9862a868c000288284593a686d
  | 43 => 0x7213b407162270ad452b54e400012d676c9c372cc926891b214d650a5f0ac540000f41c7000019845f105508d29f6200001112ec400000000000000000b7489ce0002192000255e19b149e0e89e3e34e19345345e2e13cebf80de4000000000044d050e6f501ac00022435132deac18862e7b505d80a79914951ce670000e3c5a28bc531e28e23c782e8b1f14c8803997c280000000020e638a11b4000202d4f7ec96973a7f44bf0d0c7e8af005aa0a4c4cb1b82959a6a200027ae8a3a3867672938000079200017e27c790720e82f8270e15512e889a618a4642537dcfa00005847e998b072c0000792805b6a6139ab2aaad403180003ce1a8600024d641603760a952c40001f044e6c0000000a0c00000002e680001af97393d224583b44f6c0000de82b312bc62700002e08000142000084e26d6b489e9828f800029a5fcf6480000000000077b90c0a0d20500001d80000000000018ae00016ba552a4927ad2d2a2c90a6429e032c00020a1b4b56d4bac29193c32ecc95109e377926e60d614f20efb07a7cfd135aeb173600014ab8cf1974a82ee8079808b432200008d061fa3aeddf65e86f0e00022eca2a88a958b90e02581fcd551866400002c600020ab352afa63249e540000a94000000042600000002dd053e15acba200008954edaa0691702fc2c205e394e0a7d2fb69e588d44740044c3d17dea5f0db042e30301d58d124c9652425d84eb4ea930f20189885c911e64511bb278c1ae4516825806484ba69fc7648ea8d52211e32c1358842495e48f9a41442931aa3ab221f3616a1fa447d44e806f894c04494b644f04ed1d656c6386466288d9da3b60e2a946c0e6c555cd840002ca4480210d7ae1dde6608d324750000c44901a000000014b000089e0000a8313b0000250602fccc610f00ff46add0d5cf16ac000120b9e6c0000000e4f00019dca1303e685407ae1e8d56a18e08736128cf41b39b8027ba6060a606587f1000008bb10a2e516ea0accdbc22083c4114a1cc2904b16b9f936833787ac52b8a9a3d7268e3b1a43000e8f30b29d4ec69580003a5930439a00837ff1212492add67be2900ae72c420d9506da601bf2abd000094c0a7219aa0ce75080001c8d6b60000f0aa4c98dea038724acd101c12201c694a928e04313fd5458bd03cb1292bfc8000408b0221592b860c2172dc111db81bb13af3829cd880e1f821f6800070f0fd03712f049139eda18aaf560106c98a87161488a0d1e77a4000a279a490bf173226c17fa27eaee004f2170a878d030b6800010ca65a81a516eb7ea82499c909646680007141db79d894684979852a652a1b1f1a90a04b88a219c888473c000066d23b692f800000015ec0002550c09ac87a681e1000001ea9930000c2588fa2b781d80002d52694afc00000c366ff0c400fd00000002c7
  | 44 => 0xe100017940881498403800012fabd43fac9280001a440a8e7945d3a60c00004b09310e9e54aab4857ec0000000000174855207c93e123a1a6139ec000000000089d236a0b52f844468fe0c0b80825551f060000000000214200022268bec00025440001650000000167270418d6133800000022eb220e27057d2514b5588769962e6a0000000880400055c000002211169ce856852014b07add8259aa848c1b2000000000008ce54acc290000958924e0736b78254d9b0315acc67d50e26010215223e0000a876d8c56bada502d4000000130a4a00000b628018575013850e2d0c57f08b28dd8a1c52e878c384246e2f69fde7a09bb02192b3665384664f91baf3f91f4893e2cb87a89f5e00000e64a091f800018c82539e225f181e59f82b7300016f60001056828195c4c9a9d66840dba0f86f86139000000002ca52599758b99d546952ee8097227c00000009d5ae38a632f1cb990cee429a10a0c865e58562b464861f8c7a9ace28b1a67e0d5a714a4107d48679bfa79600f8aac93fe90759723a82cb24f125608a5827b5bca713c2805489d0800000000003729298b46a269bad19ca07f4e189791ba2422afa02d099c24ac0285791289c63d22c27da80004f5cbd435e01c84c60b06000000048060f88600e747e700007ed884f3765d9200000000002fc49be24e41cf000050280003709d9a00007b325e4f50731a36c43b02386bdc4bdb5c464529023a234130360e7827d5599960be2ae90a1580004288fc691e6e668220000b5628e8b80a1d48bd967cbee00000ea40005d50da8b3b000021c01a700009f29fa07394f22a561de2f4a29610f87a30a45a60ad0eac62500a3d89f8a0a2c0ebd2095f9eb6c44768a1ac098c68b8ba0974144832a49b8fb0b618b60280997a9040a746899c086cf40005a38092b8d0e08122979e4041c149de9b245b770bc41900003ae057c9fc95102ff2ae616414fb3bd91ea17f20f408981b318f6f267e0129a2081fcb00000fc0000000000000000030b8000053c000000084712f607e676089ed8c000008a08a60000ac8281e53ba66096d21489e19ed00001e568b72cdaa90253600000000000000634221649967803f169a220b99770119c780000ff69cc115861b88c204280005062f6e10aa13c59aac8a151e31cb8e875d0b907a279b090412a8000bdb13ea6ea04a01d5192c0a0977abac9f49a5b046e0aac000739842730d4ce27a4851609a838e63515005d98a821210c9c04ceb3c8294bb200024a1425d8a06f1a4f35a49a2c054840e0000000bee974f000014d71b2ec8b7821ce0000ab8b8791a40001eae953cfaa6a3aa142cb2221ab22d7ab1e90541b49d942d2400013c964a0000000a569c6200011d20000167a6980000000f8400015ba00018c40000000b54d4bb13080bda258000763000000
  | 45 => 0xc511c453c0b6c0dd078d3401f503551c6d3f005e285ecc5a93b8d8f4d25e4f89b18084e3901164299deadb8e12402297e07bcf9e4fe24e28f11396c063028bfd81b2564479ab8811fa849a5908cb6d4a0d2846083415cc6c68cb07cf29eb53eb0d04f763b24d10a6b1722fca09e888d8a8a2ac9488a508dfad986df16607971eaa56692f492313ac189538a32b9044a5217215768fe90a30b3c740007274c274d4028c483cd0f952aba43d6a41146bf625f2194c853b2704bb6661f9405c22ff6980d9eb3fabf49958cd29506ec730187ce2f0d10a0916a6ea0298151f142ce04216b4ae22e2e09f22e327d16804b18b8677982aa9c58ed702aaf4e11a4f9fba92172786170691fa4416ae62b62b70b649b721c062d8ba014b4dfc52a57309d8de2a5f4ab720000000c2e80000d31964000000067192c8790c4f04aab08c56a0c54252a8a0ad90b0e56322b0a3284da4b6ab2eaaf014ba8588c65e1981400026e8a792b748f161740002c3d9610000c0b400044e4000000067800000007b29cbe00001ec7bc099e0000a8100b59964f7823792d88278afa75800018047125c8647ba195389400032f8dc800021144329efe00020ee0c88000b0193cb4dbf0b409fa34900009703981c2c000000096388e42f9e910000000000019c0000000088680008fa2d3660800005be873700000000d388c77890000b5aee1254e27eb33c0eddaf382f1297082c35f9f18bcb0fc2387cc961cc28f49bc0e2aa4608da73dd9b665a0196b932ed5bde02ae5e6305400022a118880006e3270803ba72061102e0000005a0038000507ae31770ae225e2a49e000000000007030352d9a601af7e40a1b0444fc00052aad699d9c000412c402080869292b9d4bb06a02300027da8eb957ebb61f6c6a0a06a39f8beb0002cdc459227f0be18120002a606ed8000000037d00019881c1506300006ca00000002ea95340000fa40000a771e717a40001e2c9438000886657a3ca800095922afc362a7bb8c02220000c1c115938281f100360a0a8a1ccaa0a0000eb69afaa386dd80000d199a635dc00000018dc4f6211980ad4086349198bb70d20a482ada3990faec1688be00021056e5e45a84095f565d8ac26d6cbd1b1c179c29ea21e5010d23066d8c68dd559250c201099a2a4eb2884465e0843600544c05c9a7403c8601fb9704b40000254be00000000000099a800075f473b000000028e8000b1d9bba6640626a4e85ca81803176be9744a12abe2a8392421fe1800b33a6c46e2864a8a0a9c64ef97473cb84047111bda57c07420002c52bb1046c3ff0231b8ac4c8462dd14a8846e000001bf97884d04a32e9600000000001316b448c5c6d9aa36000004c745981c9c165aebe90ea44b72a580001d1a7f506fc00000000001c572279a7a00001bc00021127c88b38abe1c
  | 46 => 0x3ce55880003a5115484eedf848f1b3e489a34726080002eeaaa499400004fc9d3ab3119a3000000000015ee000000012e30f0000000000021540b0af3cb9a67a0896cd82345a04a8029f900000000b8e67980001b1c0000000a1780005019ec03ba93c30000000495947c9ff800000000000000a54708a4ac28b522917d052a00000008bc00000001b1604a216469621238be2dee0002a764400534000231533694663e38c2e6190d0a000142c59a0dc60002b5e00020ec45307637f6a778292d1d80ba800000000002c5000024b80000002df4598800000020c600005a600023945ca05e636ccd76a571fe6733044243307725c9dbf40780000b7f9e4c77ca2861a395c430c8d3c1fe6a6a53d98680001a7e529aa4c92a0000369adce5afaa3110eb06c3da96440574bc66a49ea4b4100001f920dc6bf0e519e0cd750001b5079b81542b39f3e3d98d7a1ba19a25370ecc0ecc57d893ec4800d8000000000006f41f68538000af1039200024b0a65a7f04dca5549c297e052309c8829c000552424446f800005a68b2b642d763a770048090c283a289d0a9505feb64906f2262ff8261814e0000000000078000021f8000304281119ea39948e0000000080600000002f765628000aed00004ce0bca6e2000042c1a66710000091da4542cc22f2266ace640e24a62d00b5678516340f615120980000143022a6de98ac445429abd92a0568712e013561bc9e6a186208adba71f231e02d2712000168800006272bb036e0bb8e2e3ee0706c402d8400000e2a59846bac98fda431aace03c4c6800016e011500000e5a8fc3b605dbbb6ae2500021b70000000a2330d67fc25c09a2ab0e8eac4d70af24c896617e67808cb73f303620efd9f6b0b03e074b1a9b67f16d6531c9620fa27e70001de80188ff24af8588296aadd8da04960058a5288d0fe70d0dc5f063e92738529a865baf651c9a3c60624a12000161a44e80da5aaab018427072a2e1cd42d480003588cd0000000000ac8b8c25c67723c0000985000093c81d030e06342491d638bf4f9a7fb08af0000474b96a33700000007eb0d918229178357a1d20a10232bc28000a4a21e5b74e7aa68f24a2278619bbe40d4243c1e080867048411895e4bc265248e8c220f746862ea08196d52dac5f61fee4d69cdc5c3ec78a76256e25e1b2090b8ee612891f08f022d505200b8000151c761af4d5f7123660b643826108d36e51c68bdf253c8d8a6163dea7a87b10c255ec0fe22af9bcb97481db00002fd000000037a99830ee227a4b30d3ebb41adca8b98fa75041a6a31a1964e40a36b78914a31c0e632298bde10c6b2ab2ec1fb36a43ec07e2f9e7561c4fa4baa784f52efa10cdf109011f40a8367a3b9605465c3a63c2e31dca0c241dc4d7aa346e99a6a5a798da24e23ee6e821152ebd03251b856a7
  | 47 => 0xab827fa8988398000287443605c47028000000000003a00000000000000000000a800020000005d8e70e6eee7b800005ee6d800000ae000012bc0008f7800000010750001e9078ea3a349984b100022739be9a4aad3800000000303208d3f0000000b4f895a0e1a222b59ac854ea2e0ab211ffe0000f9c6e3aa32073a70255e80006d20be4000310256c121c73add6c2e29cec1696c5b55009a88c4af9a7f42275be384722a7acca000134f2da80007c6cf3971198664d009205ff161ea139a6b0830d212051888b269b11112a68c73fa3d8000209090ea7e612b182e5e0225ebb040c12db85698ec0646b901c8c5580ce8b91031364f849e581a8045fc215c8260ff400013147f5d41673a96f42e0c000039e5b609582245ff803800000000000b7dbfc137e5d16a4f9b21a0a00021e70000f1682ec2cb60aad1c3e50ab00002b3800025c704c57fb08e473a937f0500001d360002082897510212a4910409234633993702ca80d00afa9ac2b428bf606922d08ce93c093804a00020548a2c08e81897920001378654800093791dc00000f90002ceab62032f1571a620a3800022ce4400c6a190460000082995861d4d756b45a406c450d7353568e06530a4200026665c829686762cd657540a62e58c6e5e800000000a960001e880001afd0000000000071532cd13058729ae1c688722fb00868f50fc84880a1e551619a2dcac7e363ac7f03de0bc5bee49186d646283690760000000494800049900006a5ac3a88cc000bc4800061aae3c3e5ce3a64c162c04e8e20300219403c21a2231206caec8aee8018d8d742059696f213e3e62ca80f9059e940865e4a10936b89246a86ac042307a9b827c2ac4633800037f660a4ababfbaffac300002c1e1cb00007049f5ac07009300023ebb24a97a0002cf2000287e5249ae08cac12420409487690000b341d625dd0000b534a2f81dab2c87d904c798975e35a274959b1b794f2a1ad0000000582ad638a8000000000000000cea9951f46000244caf9071c00024369070c52b9c0354a19067900000008849b6855ba11f5d916f0aba8ec4001208089300008b4d87000013b65a921a6828cb4563a30f85832b98a4bc0004eba2b400000003ce800000011a870830aa37e0ece4c0848395d0f768b868b4848254c3b883c0abc25c912168607ee987460e84ca9a0943e62329c258610d08e905186aa07ca5cf6fdc80f1cc22770b7a1fa0aa02a0298a14821b9a495b92a73264a7642626952672434d57527edc00088c095b1e9a80876c22ae9e88632272aa90894046722856e68dec87fa060a760adc668675167418e81fea47a60428983a506500000001bc027a8ef26b885f0462209734619cc97b5f44a28800045416960da0000554c000abfc10068e20a400000006e06d5c002892c0001648083651a1111
  | 48 => 0x473e2999d7897d80005758d5301d6b308a5157625755500000aa200022483ad27502b88000000016600000000000efa00000001040858186026c8ff10182320d5541eab4038006e42bd9d830001f0a0002e6b0000e7f553d6b253f4b4e94e000007a1cee000309c7d3ac4d0000aac0000859a91887b80319a482b8000aa7020f4481dba5c22d287efa4c25dc800045721cf1df1df825614a40001a2a3d099c89369e8e4f41a97000175a40f9dd68441a060042a7e0a19c3e303b01a0000bf45c96146aecc0000001f7e3ffcf0e98e00007826c8ebbba07a43508a374cabfa1ef9fe40c4155e0000a8b1c780008d0278f7b16b9200017da1cf4e6e9b600be48315bc0f28000072800059d8cfc8c60000a4a9426086cbfd0b6cf4b4bb5daa1b4299079a30c7000060e1d540009d6dd9631f9172624999e76b93c2000233100001a84c7142a8ce03ea95c2f495a705248e387bc03399b8bd70a6abd2ecd416c0a84000036487b9a746dc85827620d9a8e267f81c480000002e761fd81f05c48445a2e8c304e0095407742e30000ae8000248422a807a64314d269b8e8e39104ee19498d866b1ab04d1cdc0bdd2c145288e02401106547b13f01be827298798a2a321bec957f0ee6b6af4600009080001f5800001f1906218200000003cc863c7599a302be135b2591aa257a80000002924852a24e52cdefa8b504b63e843fa2c9df3b06d0440a92a61a7f9d4e843a234c0ec251298fadc24b6102011724d8ba600002d9a0e400006c28f997a23f84cd485e26373e4e47d9e840000000556125031b0000fe62a4d1f20000c9882340000c1b0605d8000086b81e21a5800000000d50002ca9318c7524e7abf00ed00005c122c5622a9062de04b7a788000a529f5288a8a203f0c00070160341f20000091d2c00001ab68b042b00001ac800018e4434a7926d39aae66a22fc2ef1f7cc1a06a08c913b2bb1a1568bb9d4a7919b18609083b09021f53ec9e120001fc67190d462fa478a0000000000000082e1656799ae1f362dad4ab58000000249f340800020f98072d206a6a5da2200311a881b0d17a0001ca25639fd272093620000000000000000000000000000584800011900007482c164f4800072400a4330000074112484940e2274f1a68388d7760000000b500000638112220d2e7abcbabfc00024706a05c840494cb8b55db5a96e04cc035865603d40000003086b29409f0cfc8c90f38000321997e00000000000616aaa00009a700003278000107a1c900025fe6118f4c0001d0c9f490de00027d3b5b00000002344515a2ca2781f2f82f706a3fe1f7a08a1d0a6ad058c113e3d09e2a1f221aaa68bc180001e102b4b8230402f8d482821000014023848df0f9084b1a5500000004388592017218aa536a103d260f0312418817f445800000e0b5f177e
  | 49 => 0x3a1a20886729d20002806410140089143282f3972e00017618a057f816f9c5b0002984000000037960e21a70b541e60000736ae9c6479eea0001bf082d025945685ac17521be58fab3e000000000000000000070783a3a1921ae920df29720001f203a08b0a1f0e1e97ad8000999000072e8be29f38f240000f5e000013d000155530a8f96b199274ad406f400003240000f920002aaac05800000010da00010e4a7010924dea48e15ed03177c099c0cb88b53501da04a40ed2000055e0ee8d1c000000041fa8e41bd80000000a482f323a60002bbc000118e2fe26a61d7a3eabb91900821a4083e8302f00028c1a100b91a0b22c00002bbe211808c8dbe087b71994822d864484611360001c36ac9e3dc3108b4400000008332d60bd785d61709294580000000013d52d716a054a133c31c97ba1c2243f4e56c26000000000024dc000287a35f417a019a2c4bf6b0640a4abf620a012081720520db090e91c8f476eac71b0681a1e9f91f236059a76a008c3c1032322bf79d7002e92723119bc8adc25468e2ad249db9cd62c80f40a2f8e586bb100636b8690ab90734b691b280b7000092d047c58a9f644fea08cb1a250a66693c17eb97c00d80000827
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x843f75590300421fbb4a8180210f5da540c01087eecaa0600843d76550300430f324a61802187592530c010c3cc8a98600861d6454c3004236bacc4180218b952620c010c5aa9310600864e539883004326a9cc4180211bdd5620c010c5ca8b10600862d54588300432729ac4180219354d620c0108deed290600846d769483004317324a4180218b592520c0108deeca90600846d765483004317322a4180218b591520c010c6ca9308600863554984300432aa9cc2180219994a610c010ccaa5308600863654584300431aaa2c2180219594d610c010caaa6b086008666525843004332a92c218021539cf52c8010a9ae7a96400854e7314b20042a6b98a5900211b5db53c8010a5ce9a9e400852d74d4f2004326b2ca790021c395253c8010c9acaa9e400870e5454f2004386aa2a7900211b5d853c8010a5ce829e400852d7414f20042b3388a7900219554e6188010caaa6b0c40086655258620042a739ea490021535cf5248010ad4e1a92400846e7614920042a7398a490021535cc5248010ad4e0292400856a7294120042b5b86ca900211b9db5348010a5ce9a9a400852d74d4d20042b5386a690021535d65348010c9ecb29a400870e5494d2004327b2aa690021c39515348010e1aa8a9a400846e7614d20042973a0a6900214b5d05348010a9ce629a40085667114d20042b5380a690021d294f6048010e92a7b02400856a76941200422f39cca10021175ce65080108bce6328400845d73194200432729cc4100219354e62080108deeca90400865553984200432aa9ac2100219994961080108eaeda9e200853574d4f100438b2a2a788021c555153c4010e8aa729620087455354b10042b2bae4188021d154f20c4010aceea906200874553483100432729cc5080219354e6284010c9ca6b14200864d5358a1004236bb4a5080211bdd952840108eaed28c200874a5348210043a4a9a41080219a9c96584010cd2e4b2c20086596594e100432cb2aa708021c65515384010cd2cb31420086696558a100423cbb6a5080219a5965284010cd2caa94200874a5354a10043a4a9aa5080215add95284010ad2eca9420084797694610042b4b82a4880215a5d72044010cd6cb902200866b6548110043a529a4088021d254d20440108eceda9a200853574d4d10042aabaca68802195d965344010caecaa9a20087165454d100438aaa2a68802199d965244010e8aa729220086676554910043a2a9aa4880219554f6044010acaeb902200866765c8110043a2a9e408802159dd52044010cceca90220087455348110043b1282408802196d965344010cb6caa9a20087195454d100423d3b6a4880215a5d65244010cd6cb292200866b6554910043a529aa488021d254d5244010cd2a5b0a200876152d85100423d3b4a288021d454e5144010
  | 1 => 0x52042a7398c2a9021535cc6154810a9ce6082a40854d73041520422ebb4a629021879925314810c3ac9298a40845f7654c520430f322a629021875915314810c9ca7310a40864d539885204237bb2a4290219398d5214810c9ac6a90a40861e6498c520430f322c629021875916314810c9cc7310a40864d63988520432ab1cc2290219698e6014810cb2c7300a40843e74997320421eba4cb990210f9d065cc81087ae832e640847671197320421f3a4cb190210f5d2658c81087ce832c640843d74196320423d380cb190210f9d2654c81087ae932a640843e74195320421eba0ca990218d553614c810caaa7b0a640866552d85320423aba8c2990218d550614c810caaa630a640843e74994320421eba4ca190210f9d0650c81087ae8328640847671194320423d380ca190211bdc963944108d8e4b1ca20843e74d96310421eba6cb188210f5d6648c41087eeab24620843f76952310421ebb4a9188210fdd9548c41087aecaa4620861e6494e310430eb24a71882187991538c410c3ac8a9c620862e6494a3104316b24a5188218b991528c410c5ac8a946208635649463104334a94c1188219654d608c410cd2a4b04620862e54d893104316aa6c4988219394f624c410c9aa7b12620862e541893104316aa0c4988219394c624c410c9aa6312620846e7694931042363b4a4988211b9d9524c4108d8eca926208639549803104334a94c0188218e551600c410cb4a6b006208669525803104334a94c1108211edd56088410cd2a4b04420845e73d94210422eb9eca108211e5c165084108baeb318420845f7558c210422fbb4a610821175da5308410c3cc9298420861d6494c210422fbb2a610821175d95308410c3cc8a98420861d6454c210432731ca4108219358e5208410c9cc6a90420864d635482104332b2a4210821d154d2108410cb4a73004208659539802104334a94c0108219694d6008410cb2a6b00420866a525802104334a92c0108210fdd16394010878e8b1ca00866a7098a5004237396cb180211b5cb658c0108daeb314600862e5498a3004316aa4c5180219394e628c010c9aa7314600846f7558a30043172a2c5180218b551628c010c9ca6b14600864d5358a3004237bb4a5180211b5da528c0108deeca94600846d7654a300431aaa4c3180219554e618c0108eeeab0c600863554586300432aa9ac3180210f9da544c010878ed2a2600843e76551300421e3b2a89802187d92534c010c38c929a600861f6454d300430e322a6980218bd92524c010c58c9292600862f645493004316322a4980210f9d3650c01087ae9b28600846e72d943004236b96ca180210f9d2650c01087ae9328600846e729943004236b94ca180211d5c5650c01087ce8328600843d741943004237390ca180211b5c8650c01087aeb32060
  | 2 => 0x629022178dd23148110f44e918a40885e1748c520443d0ba46290221685d23148110bc2e718a40887c3638c520443e031c62902213add931481109d0ec98a40886e3764c520442f13b26290221781d93148110dc0ec98a40885e0754c520442f1ba26290221785d13148110f86e698a40887c2634c520443e0b1a6290221f0d4d3148110f80a698a40887c3434c520443e021a62902215a9d43148110bc4e218a40887c1310c520442d8ba463882212ddd16384110bc6ec90420886e3764821044371b1a4108221b858d2084110c5cc9316a60862d6498b5304317322c5a98218b59162d4c10c6ac930ea60846e729835304236b94c1a98219a58a60d4c10a3ce9a9ca60851d74d4e53042a7396a729821535cb5394c10a9ce5aa4a60854d72d52530430eb20c929821479d26194c10a3ae930ca60854e7298253042a6b94c129821479d06094c10a3ae8304a60854e7218253042a6b90c129821479d36354c10a3ae9b1aa60854e72d8d53042a6b96c6a98211bdc96154c108d8e4b0aa60843f74581530421e3a2c0a9821539cb5454c10a9ae5aa2a60855870591530430eb20c8a9821551c56254c10a3ce930aa60851d7498553042a7394c0a9821535ca6054c10a3ce8302a60851d7418153042a7390c0a9821535c86054c10a3ae8082a60843d76950530421fbb2a829821879526314c10c3aa9318a60845f7654c530430f322a629821875915314c10c5ca9310a60862d549885304326a9cc4298218b9516214c10c5aa8b10a60864d53588530430f324c629821875926314c10c5cc9310a60862d64988530432731cc4298218b9916214c10c5ac8b10a60864e63588530431b324c2298218d5926114c10cccc5308a608665629845304237394c0298211b5ca6014c10c72c9300a608669629805304237394cb218211b5ca6590c108dce432c860846d72196430423b388cb218211b9ca6550c108dae532a860846e721954304236b90caa18211d9c46550c10a38e8a9a860865953d81430423cba8c0a18211b9ca6510c108dae5328860846e721944304236b90ca218211d9c46510c108f4e0328860851d7494c430428fbaa8621821475d54310c10c3ecaa18860861d6550c43042cc38286218218799253d4810c3ac929ea40861e6454f520430eb22a7a90218799263d4810c3cc8b1ea40861d6458f520432ab1cc3a9021539cf5294810a9ae7a94a40852e74d4e5204296ba6a729021c39525394810e1ca8a9ca40870d5454e52042973a0a7290214b5d05394810e1a8621ca40854e7318652042a6b98c329021539cf6254810a9ae7b12a40846e76d4d52042973a6a6a90214b5d35354810e1ca929aa40870e5454d5204386aa2a6a90211b9d85354810a5ce829aa40852d7414d52042b238ac6a90215adc14354810ad0e0a1aa40870d4310d
  | 3 => 0xd5608c91087ee8b2a648843c74595324423bb8aca992210fdd1650c910878e8b28648843e74194324421eba0ca192211d1d5610c910cc8a4b08648847875580324432c29ac0192213a5ca60cc510c9ea6312628864c531893144274b90c098a211d1d5644c510b2ce9b1a62884767614d31442ab3ae8698a2195197434c510ca8ca21a62886956410d31442e8b808698a2199197624c510cc8ca31262885e17018931442aa3aa6498a212d5d0604c510bc2e430262884b57498431442a639aa510a211b9d85248510acae3290428846f7654821442a639aa410a212d5d261cc110aa8ea98e608843f74595304421e3a2ca982211bdc9654c1108d8e4b2a608861c64d4d304430e320a698221551d5314c110d28c898a60886645258720442b4b86cb9022153dcd65c8110a98e6b2e408854e7319720442a6b98cb902211bdd953c81108d8eca9e408852f7454f20442963a2a7902219919561c8110b4ae918e40884e7764c720442b23aa63902216c5d231881108bee6b2a408845c73595204426ab98c29022153dcd6548110a98e6b2a408856b705952044237bb2a6902211b1d95348110a5ee8a9a408852c7454d2044332b28c290221715cc6148110b4ae918a40885e2708c520442723b26290221591d53148110ad4ebb02408866865d8120442b53ae6090221789c73048110f82639824088568754c120442d5ba260902216a1d13048110e90a698240887c1314c120442d53a060902216a5d03048110bc4e2182408847a76149204433432e6490221789c73248110bc2e39924088668650c920442f13886490221785c43248110ba2e630a40885b1748c520443e19926290221f04c93148110cd0cb90a408856a75885204433432a42902215a9d42148110b94e610a40885c97308520442f0b8eca902215a5c76548110ec2e3b2a408866a7619520442b53acc6902215a5d66348110cd0cb31a40885e27198d20442f0b8cc6902215add56348110ad0eab1a40885ab7458d20442d43a2c69022178dc56348110bc0e2b1a40886686518d20442f1388c690221785c46348110bc2e329a40884e87654d20442d5ba2a6902216a1d15348110bc6e2a9a40887495314d20442f138c8690221785c64348110ad6eaa1a40885687550d20442b53a886902215a5d44348110f128621a40885e27110d20442f0b8886902219a1976148110dc0cbb0a40885e173d8520442b53acc290221789c66148110dc6c330a408856b75585204433432ac29022172dcd6148110b90e6b0a408856a7518520442e5398c290221725cc6148110bc4ec30a40886e27618520442f13a8c290221d89d46148110f84e630a40885e17318520443e0b98c290221705cc6148110ad4eb18a40885aa748c520442d4ba46290221789da3148110bc0ed18a40885e2758c520443b13ac
  | 4 => 0xd8eca9263084e9721813184335292c190c219a54b6048610c9cc7290430864d63948218432731aa410c219358d5208610cd4a4b00430866952580218437090ac010c21475d053cc210a38e8a9c610846d7598a3084237baac5184211b5da528c2108deeca94610861c64d4d308422f3b0a698421475d0534c210c38c829a610862f649493084316324a4984218bd91524c210c58c8a92610861d6494c308422fbb2a618421471d1530c210c3ac8a98610846d759883084237baac4184211b5da520c210c5cc9290610862d649483084237bb2a4184218b991520c210c5ac8a906108666529843084332a94c2184219594d610c210caaa6b086108666525843084332a92c2184211b5db53c8210a5ee8a9e410852c7454f2084236bb0a7904214b9d053c8210a5ae829e4108665529862084334b2aa5104211b9d852482108dceda9a410852f7454d20842963a2a6904211b9d85348210a5ce829a410852d7414d20842d5ba260904216a1d13048210e90a698241085aa740c120842d4ba06090421d254c3048210bc2e3a92410866b65549208423d3b0a4904213a9d85248210ad2eb992410856b754c920842f1b8a6490421b81852148210b94e610a41085c97308520842b4bacc6904215add56348210b56e8b1a41085a87458d20842f1b8ac690421781c563482109d4eda9a41085e171d4d20842d5ba2a6904216a1d153482109d4ec29a41085aa7414d20842d4ba0a690421d254c5348210bc2e229a410856b7550d20842b43aa86904215a9d44348210ad2ea21a41087894310d2084335b2ec2904219ad956148210b96e6b0a41085c87358520842e5398c290421725cc6148210dc2c230a41085aa748c520842d4ba462904213add931482109d0ec98a410846f765482084333294c210421b85852008210a6ee8a9e21086656594b1084332b2aa5884219a59652c4210cd2caa96210846f725865344236392c329a21871936354d10c5ec9b12a68862c64d895344317b20c4a9a218b1906254d10c9ec6312a68866462d85534431c326c0a9a2117dd95314d10a38e8a98a68854c7254c534421f3a4c229a210f5d26114d108dce5300a68846d72980534421f3a0c029a210f5d06014d108dce4300a68846d721805344237396cb21a211b5cb6590d108e8eab0c868846f725954344236392caa1a211edc16550d108dee4b28868846c725944344237390ca21a211b5c86510d10a3ae8298868851e7550c434428e3aa8621a211d1d56110d10ca8a6b0886884e972980434423c3aac021a21a650d6010d10c3ec9b1aa48861f6418d524430e320c6a92219318f6254910ca8c7b0aa48846f7654852442a639aa429221179cc61149108bae6308a48843e74d97324421eba6cb992212d5d261cc9108e8eab0e648843e74d96324421eba6cb192211e1
  | 5 => 0x846e72d9643c4236b96cb21e218d5526190f108dee4b2a878846c7259543c4278b88c0a1e211bdc96510f108d8e4b28878846e7219443c4236b90ca21e21475d25310f10a3eeaa18878851d7550c43c42cc3828621e211bdd95214b10c3cc9318a58861e6458c52c430eb22c629621931c96314b10cb4c6b00a5886596358052c421f3a6cb996210f5d365ccb1087ce932e658843d7499732c42a6392a799621535cc52ccb1096ae930e658843e7419632c421eba0cb196210f9d2654cb1087ae932a658843e7419432c421eba0ca1962199149610cb10a3ce9a9e638861e6494e31c430f322a718e218d596648c710c6acab2463886b16458231c428f3a6a698e21179d8534c7109e0e0b22638859674d8d31c42cb3a6a698e21745c3534c7108ecec29a63884d67614d31c42ab3ae8698e21a5590434c710cceca3126388554754c931c425aba0c098e2117dd9530c710da262b00638846e7614921c4237bb2a410e219a9496008710cd2a4b0043884b57498730c430e324a69862187191534c310d28c898a618852e74d4f20c4296ba6a7906211bdd953c8310b4ae918e41884e7764c720c426ab98c290621995486148310a9ce632a418854d7319520c42973a6a6906214b5d353483108d8eca9a41885c57318520c42d2ba46290621391d93148310c38c9b1aa70845f7654c538428e3a2a629c21875915314e10c38e6b20a70861d6498c5384317324c429c218b5926214e10c5cc8b10a70862d64588538431b322c229c218d5916114e10cccc4b08a708665625845384237394cb21c211b5ca6590e108dce432c870846d72196438428eb98a921c21471d15390e108dce532a870846d729954384237390caa1c211b5c86550e108bced29a870851c7454d4384237394ca21c211b5ca6510e108dce4328870846d72194438422ebb6a621c21475d05310e10a3ceaa18870851c7550c438430fb2a8621c21875954310e109d2e53008708699435804384297ba2a7294214b1d15394a10a5ce829ca50852d7414e52842973a6c7294214b5d36394a10ad4e1b1ca50856a7018e5284386a188729421539cc6094a10a9ae6304a50846e76d4d5284297ba2a6a94214b1d15354a108dcec29aa50852e7414d5284296ba0a6a94214bdd16354a10a58e8b1aa5085677158d5284386a1886a94215a9c04354a10ad2e021aa50854f7358552842a639ac2a9421539ce6054a10a9ae7302a50846f76548528421f3a0cb994210f5d065cca1087ce9b2c650843d74d963284335292c1194210fdd1654ca10878e8b2a650866552185328421f3a0ca194210f5d0650ca10cd4a4b00650851c7454f3184274b94c198c218b992528c610c5ac9294630862e6454a3184316b22a518c21471d1534c6108daebb12630846d751893184274b80c498c211b9da524c6108
  | 6 => 0x4831732ac818241a31cd640c120d50e0b20609046e751903048267398c818241399c4640c1209cae232060904ea701903048266bb6861824193997430c120d1ac9a1860904cd7610c30483273288618241a3590430c120b92e02186090666659843048353324c218241a9592610c120dc4e13086090666655843048353322c218241a9591610c120d8e86b0860906c4435843048371382c218241aa993500c120d52c9a8060906e261d403048370b0ea0182413a5db400c120d52c9a00609078b43d003048370b0e80182413a5d8400c120b92e62006090788431003048370b08801824193997300c120d1ac998060906c561cc03048354b246018241725ce300c120dc2c318060904cf764c0304832732a6018241631d1300c120d1ac898060906c5614c03048275bb260182416a1d1300c120d52c898060906e1614c030482e5bb26018241b2dd9300c120d94ca980609074a654c030483c5ba26018241729d1300c120b90e89806090788744c030482c43a26018241b2d91300c120f14c898060906c9644c030483c4b226018241a2591300c120f84c298060906c9614c030483e0b0a6018241b0585300c12087ce930ca61043d74986530822fbb2a629841875915314c20caaa6b08a61061d6498c5308317324c4298418b5926214c20c6cc9308a610635649845308333314c2298418d9916114c20c6ac8b08a610656635845308333312c2298418e5926014c20ce2c3300a61046e729964308237390cb218411d9c46590c208eae232c861046e72995430823d384caa18411b9c86550c208ece232a861047571195430828e3a2a6a18411b9ca6510c208dce4328861047671194430823ab88ca218411e9c06510c20c3ecaa18861061d6550c43082973a6c7290414b5d36394820e1a8621ca41043e74d96320821eba6cb190419654e608c820cd4a4b04641066a52580320823bbb2a2288419558d511442087ce9b2c621043d74d963108317324a5188418b592528c420c6ac928c621063564546310821f3a0ca988410f5d0654c4208daebb12621064e5318931082373b4a4988419918a514c420c9cc7290421064d63948210832ab1ca2108419558d5108420aceea908421067151980210832729cc5180411bdd5628c0208daed294601062f649493008316324a4980410f9d3650c02087ae9b28601043e74194300821eba0ca1804187592530c020c3ac8a98601064d539883008237baac4180411b5da520c020c5cc9290601062d64948300832b29ac2180419554d610c020a5ce829e401052d7414f20082b3388a790041595c453c80208daed29440104797694a20082373b6a6900411b9d85348020a5ce829a401052d7414d20082b3388a690041595c45348020ec2a390a401056b75485200828f3a6a729e21479d36354f108beeca98a78
  | 7 => 0xb18a412b5d0658c5209d4e1b2462904e970d923148347326a718a41a3990538c520d1cc998c62906aa649823148354b24c118a413a9d6608c520cd4eb30462906aa645823148354b22c118a413a1d5608c520d96a6b0462906c853582314836598ac118a413a5c3654c520cd2e1b2a629046e759953148257ba2ca98a412b1d1654c5209d6e0b2a629064d7319531482373acc898a411b5d6644c5208deeab22629046c755913148275b82c898a413a1c1644c5209d4e032262904e97019131482673b4a698a4193196534c520b92e129a62904cc7654d314832632aa698a41631d1534c520b88e2a9a62905cb7054d314832632e8698a41719c7434c520c98ca21a629068d6410d31482e4b808698a4199197314c520c98cb18a629058e748c531482e4b846298a412b9d0604c52095ae830262904e970d943148257ba2ca18a412b1d1650c5209d6e0b2862904ae741943148256ba0ca18a41339cc650c5209d4e1b2062904e970d9031482373a8c818a411b5d4640c5209d4e032062904e9701903148266bb6a618a412b9d2610c52095ae930862906656514431483a2298a218a4133dd9310c520a98ea98862904e7764c431482b23aa6218a413a9d6600c520cd4eb30062904e8755803148365a9ac018a41b214d600c520dc6a2b0062906e051580314836598ac018a41b88c5600c520d9262b0062906e1315803148297ba2a7a82414b1d153d4120acee2a9ea0905647154f50482a7398a3a8241535cc51d4120ccac228ea0905aa74d8f50482d4ba6c7a8241b2d8e63d4120b56e8a9ea0905a87454f50482f1b8aa7a8241781c553d41209d6eca1ea0904e87650f50482753b087a82413a5d843d4120f128621ea0905ca7318750482e4b98c3a8241b858751d4120b96e6a8ea0905c87354750482e5398a3a8241725cc51d4120dc2c228ea0904ea768c75048274bb463a82416a9d231d4120b52e918ea0904ea760c75048274bb063a8241a319143cc120b90e0a1e60904ae749873048256ba4c3982411b1d561cc120a98ea98e609078943d0330482373aec91824193997438c120c9cca21c609068f6410e30482e4b808718241e210e408c120c9ccb98460904ae749953048256ba4ca982412bdd1654c120958e8b2a60904e771595304827238aca982413adc1654c1209d6e0b2260904ae761913048354b80c898241a3193534c120d18c829a60904ce7690d30483463248698241a3191434c120b90e0a1a609068c64cc530482a63aa6298241a3191314c120b90e098a60904ea76d413048355b26a098241aa193504c120b94e7a8260906a86490130483c521c80982413a1d9404c120b90e6a0260907894350130483543266098241539d6304c120d18c9182609046e75d90304827338ec818241395c7640c12095aed320609062e659903
  | 8 => 0x1654c120878e8b2a609061c64d4d304830e320a698241661d1300c120d32c898060906d1614c03048370b0e4390241729cc21c8120b92e610e40904ae7418e2048256ba0c710241399c463881209cae231c40904e9709935348274b84c3a9a412b9d26194d2095ae930ca6906cb535825348275b8ac129a41a31935354d20d4ec9b0aa6906a464d855348371b86c2a9a41a9d906154d20d48c830aa6906c7531855348333298c2a9a41b85c06154d20d56c9b02a6906a864d815348371b0ec0a9a41b81876054d20d96a7b02a6904e971d815348275b82c829a41725c25314d208deeca98a6905647154c5348267bb2a629a41631d15314d20b88e2a98a6905cb7054c5348274b84c229a41399c76590d209cae3b2c86904e970d964348275b82cb21a413a9c26190d209d2e130c869046e759824348274b86caa1a4139dc56550d209c8e2b2a86904eb705954348275380c2a1a413a5c06150d209d4ebb0286904e971d8143482373a8c0a1a41399c46050d209cae230286905e17118143482753a8c0a1a419a9d46050d20d548630286906e2711814348274b88c0a1a41b85c46050d209c2e230286904e970d944348273b8aca21a41391c56510d209d6e0b2886904e6711944348272b88ca21a41935945310d20b1ae8298869058d7490c4348267bb28621a41721c14310d20b1eeca18869068f7650c43482c73aa8621a41631d54310d20b1ee2a18869078b7050c43482c63828621a41e21c14310d20b10e0a1886904ea709844348274b84c221a411bdd56110d208d8eab08869046e7598043483c4a1cc021a413a9d66010d20cd4eb30086904e9719804348346a1ac021a41e250d6010d209d0eab0086906cb53580434836429ac021a41b290d6010d20d9286b008690689435804348275b8ac021a413a5c263d452095ee8b1ea2904ac7458f5148275b82c7a8a41b8d456094520d1ec9b1aa29068f6418d5148346320c6a8a41b118f5154520c98c728aa2906cb63d81514836431ec0a8a41b8d476054520d1cc9318a29068e6458c5148346b22c628a41b11c56314520c9ac7298a2905657114c51482f0b84a228a411bdd95114520a98e6a88a2904e77654451482e239aa228a4178dc15114520aceeca88a2906677654451483a3b9aa228a41591cd5114520e88e6a88a2905447354451483a331aa228a41d158d5114520acee0a88a29076370544514836531ac028a41b258d6014520ec2a2b00a2904ae74d973148256ba6cb98a413a5c365cc5209d6e0b2e62904eb705933148274382c998a413a9c064cc5209d2e032662905c97094f31482c63a2a798a41711c553cc520b96e0a9e629068d6410f31482e4b808798a4199d9451cc520b8ae628e62907465314731482573a6cb18a412b5d3658c5209d2e1b2c62904eb7059631482573a0c
  | 9 => 0xac8b08a710656635845388332b12c229c411d9c46590e208eae232c871047671195438823ab88caa1c41471d15350e209e2e2302871047671194438823ab88ca21c4187d954310e20c3acaa1887105987050c438834ca1ac021c411ddd95114620caac6a88a31043e74d96318821eba6cb18c418d592518c620c6ac8a8c631043e74195318821eba0ca98c419394f624c620ccec528a631064e5358a308830eb24a61844187591530c220c9aa6b10611065653584308832aa9ac218441661d1300c220d32c898061106d1614c030882973a0a7904414b5d053c8220acce229e41105657114f208821f3a4c329a410f5d26194d20c38c9b1aa69063764d85534831a326c2a9a418dd906154d20c68c830aa690657631855348333b10c2a9a4117dd95314d20a38e8a98a6905547154c534823b38ecb21a411d5c76590d208d8eab14869047771595434823a38acaa1a411b9d76250d208f4ebb0286904ea721814348278b88c0a1a411ddc56510d208e8e2b28869047671194434823ab88ca21a41475d05310d20a3ceaa18869051c7550c43482cc3828621a411b1d56210d20c98a6b1086904ea72980434823c3aac021a41a650d6010d208dcea32664904ea7019332482b238aa7992412b9d261cc92095ae930e64904ea709873248275386c9192413a9c2618c9208dceb32264904e6719913248272b8cc8992411b1d5644c9209d0e0b22649046e7614d3248275380c299241399c4640c9209cae232064904ea701903248237bb2a619241591c5530c9209d4e1308649043f7458f514821e3a2c7a8a411ddd95114520aa8e6a88a29061e6498c514830f322c628a41875916314520c9ee4b18a29064c7258c514832a38ac628a419358f3214520acae2190a29065a63580514832cb1ac028a41471d153cc520aa8e2a9e62905557314731483a3990a398a410f9d0658c52087ae832c629061e64d4e314830f320a718a413a9ca608c5208bced29a629051c7454d31482aa38aa698a4193197324c520c98ca99262905c4714c9314821fba2ca18a410f1d1650c52087ce8328629043d74194314822ebb6a618a4199588510c5209d4e5300629046e75d8f21482b53a8c190a412b9d3638852095ae9b1c42904ea70d8e2148275380c710a413a9d66088520cd4eb30442904ae7498d2148256ba4c690a41599d76148520accec28a42906667614521483a3398a290a41d15cc5148520cccc628a42906646314521483b0b80a290a412b9d3630852095ae9b1842904ea70d8c2148266bb4c610a41a39926308520d1cc8b18429068d6458c21483263aac610a412b9d0630852095ae831842904ce7318c2148275380c610a419358e53085208daec29842905657114c214836531cc010a41b258e6008520cd4cab0042906ca635802148364b1ac010a410fdd
  | 10 => 0x7466354421c83a2b1aa210e41d85466008720d94c6b0043906c96358021c83b0a8ac010e4187192534c320c38c8a9a61906aa6458353c8354b22c1a9e41639d35394f20b92e1a9ca7904ae7498653c8256ba4c329e41639d35354f20b92e1a9aa79046f7654c53c8267bb2a629e41b294d6014f20d92a6b00a7904e671d9643c8272b8ecb21e413a5c26590f209d2e032c879062e6555243c8274b84caa1e413a5c06550f209cce230287904e57118143c8274b84ca21e41399c46510f209cae232887904e97019443c82c6ba4a621e4133dd94310f20b1eeca18879068f7650c43c82c7baa8621e41635d54310f20b1ee2a18879058c7050c43c8237baac221e411b1d56110f20d1a86b0087905e170d4651c82573a6c6a8e412b5d36354720bc2e1a8aa39068e6498c51c8347322c628e41a35916314720c9ac7298a3905657114c51c8237bb2a228e4139dd95114720aceeca88a3906677654451c83a331aa228e41d158d5114720ccaa2b00a3906ca6358051c8364b1ac028e41d85456014720cd4a6b00a3906685358051c837128ac028e419a5456014720dc2a2b00a3906615158051c82573a6cb98e412b5d365cc72095ce932e63904ad7499731c8274b84cb98e413a5c065cc720d1ac821e63904ae74d9631c8256ba6cb18e413a5c2658c72095ce832c63904ad7419631c8274b80cb18e41a3993318c72095ce932a63904ad7499531c8274b84ca98e413a5c0654c720c9ae632a63906697019531c82373acc898e411b5d6644c7208deeab22639046c7559131c8275b82c898e413a1c1644c720c98cb29a639064c6554d31c82e238aa698e4193d97434c720b8ce3a1a639064f6510d31c8346b208698e41639d2314c72095ce830263904ad7418131c8274b84ca18e412b9d0650c72095ae832863904e97019431c82373a8c818e411b5d4640c7209d4e032063904e97019031c8267bb26218e4139dd9310c720d18c8a1e61904ae7498730c8256ba4c3986411bdd561cc320a9eea98e619068f6410e30c8346324a698641a3191534c32099ced21a619068c6490d30c83463228698641a3193314c320a9eea98a619068c644c530c83463246098641399c7640c3209cae3b20619062d6599030c8316b2ac818641a31cd640c3209cce232061904e57119030c8266bb68618641a3593430c320d1ac821861906656598430c8353324c218641a9592610c320ccacab0861906a66458430c8352b22c218641b1d0d610c320d8886b08619068d64cc030c8362b0e601864133dd9300c320b18e8980619068d644c030c8362b0a60186413add9300c32087ce930ca71043d74986538822fbb2a629c41875915314e20caaa6b08a71061d6498c5388317322c429c418b5916214e20c6cc9308a710635649845388332b14c229c418d9916114e20c6
  | 11 => 0xc326b1aa4200611d5da5110030cacc7288801865563944400c333314a2200619958a51100308eeeca88801865663544400c32ab1aa220061c510d5110030cccc4a88801866562544400c2aab8ea99806117dd954cc030c3cc8aa6601861f76553300c30e3b2a998061c355252cc030e1aa8a96601871554947300c38b2a2a398061c555151cc030e8ca4a8e601874552547300c32b322a3980619519151cc0308baed29c601862e5498a300c316aa4c5180618b951628c030c5aa8b14601866662946300c332b14a31806199989518c030ccac4a8c60184797694e300c394aa2a518061cc551518c030ec2a4a8c601843e76951300c21e3b4a8980610f9d9544c030c5ec9292601862c64949300c317b22a4980618b191524c030c6ec928a601863464945300c31bb22a2980618d191514c030c3ee9b2a601861c74d95300c30fb2ec898061175d6644c03093ce9322601861f65191300c30eba8c898061179db544c030c38c9aa2601855571d51300c24e3b4a898061475d6544c030c3ecb2a2601845c76551300c30e322a898061271d9544c030c3ecaaa2601861f76551300c28f3b2a898061471d9544c030c38ecaa2601841c76551300c327b2ca498061a3192524c030e1aa9292601864f65549300c346322a498061c3551524c030caecb28a601869464945300c38aaa4a29806187191514c030caecaa8a601869464545300c38b2a2a298061c5551514c030e8ca4a8a601874552545300c38bb22a29806195991514c030ca8c8a8a601871464545300c30a322a29806187553604c030c38c9282601863b74d95300c31c3a6ca980618ed97644c030c76ca322601863b65951300c31db2aa898061a6193634c030b92e5b1a60187195494d300c335b2ca4980619ad95524c030e52a8a92601867365945300c339b2aa298061cc551514c030ea4a6a8a601876152545300c31d322c1a9e41479d35394f2087ce930ca79043d7498653c828f3a6c6a9e4117dd95314f208ece3b2c879047571d9643c8316aa4c521e411d9c46510f208eae2328879051d7494c43c828fbaa8621e41475d54310f2095ce930e65904ad7498732c827338cc899641395c6644cb208dcec29a659065a5358032c8273388c819641395c4640cb208deeca98659043e74d8d51c821eba6c6a8e411ddd9511472087ce9b2e639043d74d9731c821f3a4cb98e410f5d265cc72087ce9b2c639043d74d9631c82aa38aa698e419394c624c720c9aa631263905c4714c931c82573a6c710e412b5d363887208daed29c43904ae7498d21c8256ba4c690e419c545600872095ce9b1843904ad74d8c21c8347324c610e41a39916308720d1ac8b18439064f7558c21c83263aac610e412b9d0630872095ae8318439064d6394c21c82b2b88a610e4159dd95108720cceeca884390
  | 12 => 0xa08611b9ca65904308dae532c821861e5498e410c30eaa4c720861879516390430c3aa8b1c821864e6394a410c326b1ca5208619398d5290430c9ac6a94821865563946410c32b31aa3208619558d51904308dee4b2a821846c72595410c237390caa08611b5c865504308baebb1a821861d54d8d410c30eaa0c6a0861475d44350430c3aca21a821846d75d89410c3172a6c4a08618b55362504308daea312821862e54189410c316aa0c4a08611b9da52504308d8ed292821846e76549410c2363b2a4a086199d8a5150430cc8c528a821865763545410c32a31aa2a0861c510d5150430ccec4a8a821866462545410c31caa6c0a08619c5476050430d3086302821846e72994410c236b94ca208619c54560cc43087eed2a4621843d76952310c21fbb2a9188610f5d9548c430c5cc9294621862d6494a310c317322a5188618b591528c430c6cc8a8c621863564546310c3172a6c4988618b553624c430c5ca8312621862d54189310c274b80c4988611b1da524c4308dceca92621866762945310c332314a2988618e552600c430cd2a5300621863954580310c334a92c0188619c945600c43087ce932e421843d74997210c21f3a4cb108610f5d2658843087ce832a421843d74195210c30eaa6c690861875506348430c9ec6a92421865763545210c32a31aa2908610f9d3650843087ae9b28421843e74994210c21eba4ca108610f5d6640843087eeab20421843f76950210c21ebb4a8108610fdd9540843087aecaa0421861e5498c210c30eaa4c610861879516308430c3aa8b18421862e64948210c316b24a4108619398e5208430c9ac7290421862e64548210c316b22a4108619398d5208430c9ac6a90421863664944210c31ab24a2108619558e5108430c6cc8a88421863564544210c32b31aa2108619558d5108430c74a9300421863954980210c334a94c0108619c5466008430c74a8b00421863954580210c335292c0108619a5496008430ce4a2b00421867151580210c22ebb08728061475d743d0030c3acba1e801871743547400c30eaa4c72006117dd56390030c3aa8b1c801861f6510e400c236bacc5200618b9526290030c5aa9314801846f7558a400c3172a2c5200618b55162900308daed294801846f7654a400c333314a3200619958a5190030cacc6a8c801865563546400c38a21aa320061999895190030ccac4a8c801861e54d8d400c30eaa6c6a0061879506350030c3aa831a801849e76d0d400c28ebae86a006187d974350030c9ec7292801864c63949400c327b1aa4a00619318d5250030caec728a801865463945400c32bb1aa2a00619518d5150030e2e86a8a801861e5458c400c30eaa2c620061875944310030b32e0218801846d76948400c32731ca4200619358e52100308deeca90801864e6354840
  | 13 => 0x62148308deeca90a41862e64548520c316b22a4290618d9526114830c6aa9308a41866552984520c31b2a2c2290618d5516114830ccaa4b08a41847671997420c23ab8ccba10611d9c665908308eae332c841861d5498e420c30eaa2c7210619358e5290830c72a9304841863954582420c335292c1210611d9c465508308eae232a841861d54d8d420c30eaa0c6a106193d8d52508308ece3328841847571994420c334a92c1990618e552600c830c72a8b00641866a52580320c3172a4c5a88618b55262d4430c5ca8b16a21862d5458b510c317324a5a88618b59252d4430c5cc8a96a21862d6454b510c29b3a6a3288614d5d35194430acce5a8ca21856572d46510c237b92c9288611b1c96494430acce5aa4a21856572d52510c38a39aa928861599c85494430acae42a4a21855575d0e510c38aaa68728861c55504394430a6ce9a94a21853574d4a510c3932a4a528861c95525294430e4ca8a94a2187255454a510c29b3a0a5288614d5d05294430aace7b24a21856772592510c2b2392c928861c550c4394430a6ce8314a2185357418a510c2ab398c5288615c9c06294430acce5304a21856572982510c29b3a0c1288614d5d06094430acce4304a21856572182510c21f3a0c4a88610f5d062544308ecedaa2a21856672d51510c2b2b96a8a8861c51ce5454430e28e6aa2a21847676151510c2b3390a8a8861595c85454430aaaeba1aa21871654d0d510c38aaa686a8861c59504354430e2aa821aa21847676d49510c29b3a6a4a88614d5d35254430e4ca9292a21872554949510c3a3a1ca4a8861d110e5254430e4ca8a92a21872554549510c3a3a1aa4a8861d110d52544308ecec292a21853674149510c29aba0a4a8861559cf6454430aa8e6b22a21856772591510c2b2392c8a88615c1c16454430aaae1a1aa2187154310d510c2b938086a88615c5c04354430e2ce821aa2187166410d510c38ab2086a8861d49c04354430aaae021aa2187517010d510c2aa39ac4a88614d9d06254430a6ae8312a21855673189510c2b9380c4a8861559ce4254430aaae7212a21857270909510c2b8b8484a886155dcd4254430aa8e6a12a218572700c9510c2b8b8064a8861599ca6054430acae5302a21853674181510c29aba0c0a8861599c86054430acae4302a218536740c1510c29aba060a8861599c83054430acae4182a21843d76950510c21fbb2a8288618b9526214430c5aa9310a21862e54588510c316aa2c4288611b5da5214430c5cc9290a21862d64948510c237bb2a4288618b9915214430c5ac8a90a21863654984510c31aaa4c2288619994a6114430ccaa5308a21847776544510c31b322a2288618d5915114430cccc4a88a21866562544510c237394cba08611b5ca65d0430a3aea21e821861d6510f410c38a21aa3
  | 14 => 0xe8328429843e75990214c21e3aac810a610fddb540853087aedaa0429843f76150214c21ebb0a810a6187d526308530c38a9318429861f5458c214c30e2a2c610a619358f5208530caac7a88429863b54980214c31c2a4c010a618ed516008530c70a8b00429866b52580214c334292c010a619cd456008530c38a931e809861c5458f404c28f3ac87202618bd526290130c58a9314809862f5458a404c3162a2c52026187d506350130c38a831a809861c6550d404c2cc38286a02618bd52628c130c58a9314609862f5458a304c3162a2c51826187590548c130c3aec2a4609870c5498a304c3862a2c51826187151618c130cccc530ea81866562987540c32b31ac3aa0619998961d5030ccac4b0ea81852e72d52540c296b96a92a0614d9c75495030a6ae3aa4a81846f72586540c236392c32a061479ce6195030a5ee4b0ca81852c72586540c297394c12a0614b5ca6095030a5ce4304a81852d72182540c29b388c12a0614d5c46095030a5ce5b22a81852d72d91540c29b38ec8aa0614d5c76455030a3ce7312a81853a70989540c28e39ac4aa0618718f6155030a3ce730aa81851c73585540c30e31ac2aa0614bdc96155030a58e4b0aa81853870585540c30e31cc0aa0614b9ca6055030a5ae5302a81861c63181540c297390c0aa0614b5c86055030a6ce2302a81853571181540c21fbb2a82a0618b5526215030c5aa8b10a81863554984540c31aaa2c22a0619398e6215030c9cc6b10a81865663984540c333314c22a0619958a6115030cacc6b08a81866662584540c332b12c22a0619a58a6015030ce2c3300a81861e74597430c2aab8ea9a18618759654d0c30c3aa8b06861863954582430c28eb9aa82186187d954310c30c3acaa18861863a54580430c28ebacc821861875966410c30aaae3aa0861851d75950430c22fbb2a821861879915410c30a3eecaa0861861f76550430c28fb8aa82186117dd56010c30c3aa8b00861869a64580430c31b2a4c3a90618d55261d4830c6ca8b0ea41863554587520c2973a6a5290614b5d35294830acce3a94a41856571d4a520c2b338ea929061595c75494830e18e6aa4a41856671152520c2b2b88a929061535d74394830e1aa9a1ca41870d5410e520c2a739ec9290615a9c36494830e1a8621ca41852e74186520c296ba0c329061539cc6194830ad4e030ca41843e74185520c21eba0c2a90611b9db5454830acce3aa2a41856571d51520c38639aa8a90611b9d85454830acce22a2a41856571151520c2a6bae86a9061c35534354830e1aa821aa41854c73591520c386a1886a90615a9c04354830ad2e021aa41854c73585520c2973a0c2a90614b5d06154830a9ce630aa41856a70185520c2973a060a90614b5d0305483087aed2a0a41843f76550520c3172a4c4290618b552
  | 15 => 0x3c74595218c32631aa490c61591c5524863087ce9b28431843d74d94218c317324a410c618b5925208630c9cc7290431864d63948218c2b2b8ca410c618b9915208630c5ac8a90431864e63548218c326b1aa410c619a54a6008630cd4a4b00431866952580218c236bb4a5204611bdd95290230938e8b2e611851f74597308c30e326a9984618799154cc230c9acb296611864d6554b308c334b2ca5984619a59552cc230a5ce5b1ea89852d72d8f544c297396c3aa2614b5cb61d5130c6ec330ea89851d73187544c21fbb2a82a2611bdc961151308d8e4b08a89852e72d8c544c296b96c62a2614d9c76315130a6ae3b18a89851d73d88544c28eb98c42a2614d9c46215130a6ae2310a89853970188544c28eb9ec22a261475ce6115130a5ee4b08a89852c72584544c28eb98c22a2614b9c86115130a5ae4308a89863561184544c29cb80c22a2618e15260d0d30c3ee932c869861e65d52434c30e2a2c321a61871526090d30c76a8302869851e75d91434c22f3b0a8a1a61479d85450d30c3cec2a2869861c54d85434c26ab88c0a1a61a6d906050d3087ce930ea49843d74987524c21f3b6a8a92610f9d85454930c6ea9b0aa49863454d85524c31baa0c2a92618d15061549308deeca90a49856471548524c30e2a4c7a12618715163d09308ece2328849847571194424c30e2a4c621261871516310930c70a9300849863854580424c31c2a4c1192618e151608c93087ce9316a29843d7498b514c21f3b6a8a8a610f9d85454530c5ea9b12a29862c54d89514c317aa0c4a8a618b15062545308eeeca88a29856472544514c30e2a4c7a0a618715163d0530a3ceb21e829861f5498e414c30e2a4c720a618715163905308dce532a829846d72995414c29b38ea8a0a61479d64350530c38cb21a829862f54d89414c3162a6c4a0a618bd506250530c58a831282984e970189414c237390ca20a611b5c86510530a6ae22a0829861c5498c414c30e2a2c620a618e15260105308bcebb26629861d64153314c30f328a998a61879d854cc530c3aec2a6629871671153314c38ab88a998a618715260cc53087ceb324629843c75592314c21ebb6a918a610f5d8548c530c5ea9b12629862c54d89314c317aa0c498a618b150624c530cc8c5a8a629866462145314c31c2a6c098a618e150604c5308bcebb2262984d870591314c2ab38ca898a6187d90544c530c3ac82a2629861e76151314c3862a6c498a61c3150624c530e28a9b0a629871454d45314c38baa0a298a61c6153604c53093ae8302629861c54181314c38c2a0c098a61b2d88604c530e2ea8988629843f74597214c21e3a2cb90a610fdd16588530878e8b2c429861c5498e214c30e2a2c710a610f9d3654853087ae9b2a429843f74594214c21e3a2ca10a610f9d0650853087a
  | 16 => 0xc28f3b0a8a1e61879d85450f30e32e02a2879861c54d8543cc30e2a0c0a1e61355c46050f30d3286b00879846f7654852cc23b38ecba16611d5c765d0b30ad2e0312a39864e7318951cc326b98c4a8e619a9c06254730cd2e0312a3984777654451cc237396cba0e611b5cb65d07308dee4b2a839846c7259541cc26cb98c0a0e61a690c60507308beeab26639861d6415331cc28f3a4a398e613a5c0624c73093ae9b2a639851e74d9531cc26c382c898e61559c6544c730c3ac82a2639864f6518931cc2e4b80c498e61551c5524c730ba2e1a8a639851e7494531cc26b3b0a298e61275d0604c730da262b00639843e74d9621cc21eba6cb10e610f9d3650873087ae9b28439866962983548c237b92c32a4611b1c9619523087eecaa0a91863554584548c22ebb6a821c61275db5410e30b34e1aa0871851d76d50438c30ebb6a821c61c39cb5410e30e1ae5aa0871851d71d50438c38d386a821c61655c45410e30b34e02a0871861f54580438c2b3388a929461595c45494a30a9aea21ca51870f5410e528c2a6b9ec9294615a9c06494a30a5ce9b1ca51852d74d8e528c386a1887294614b9d06194a30a5ae830ca51854d73186528c332b08c3294615a9c06194a30a5ce8304a51852d74182528c2b3388c129461595c46094a3087ce830aa51843d74185528c2373b6a8a94611b9d85454a30acce22a2a51856571151528c2a6ba886a9461c3d504354a30a9ee6b22a51856771591528c2b238ac8a94614bdd16354a30a58e8b1aa5185677158d528c2b238ac6a94615adc14354a30ad0e0a1aa51870d4310d528c297ba2c2a94614b1d16154a30a9ee6b0aa51852e74185528c296ba0c2a9461535cc6154a30ccac230aa51856a70185528c2973a4c0a94614b5d26054a30acce3302a51856571981528c237bb2a4294619398e5290a308eee2b2a851847471595428c32631aa4a14619a9496010a30cd4a4b04651866952d81328c237b92c928c611b1c96494630c3ec821aa31846d76948518c317324a428c618b59252146308deeca90a31862e64548518c316b22a428c611ddd95114630c6ac8a88a31846e72997418c236b94cba0c618799443d06308dce532c831846d72996418c32731ca520c619358e5290630c9cc6a94831864d6354a418c32ab1ca320c619558d51906308dee4b2a831846c72595418c237390caa0c611b5c865506308daebb12831846d75189418c274b80c4a0c611b9da52506308d8ed292831846e76549418c2363b2a4a0c61c510d51506308dce5328831846d72994418c334a94c020c619a5496010630c5cc9294631862d6494a318c317322a518c618b591528c630c6ac928c631863564546318c334a94c118c619a549608c6308daebb12631846d75189318c2373b4a498c611b1d9524c63087ee8b2a43184
  | 17 => 0x88439394d620c421caaca9886210f15544c43108762b126218843c355153c84218daed2944210f155454e210863abb4a5108431b5c365484218daeb31a4210cae7498d2108727b2ca69084393d955348421e1aa8a9a4210da5748c521086723b26290843b118d3148421caecb29a4210e576554d210878aaa2a690843399da3248421c3cc929ea010e1d6494f500870f322a7a80438759153d4021ab4e7a84a010d5973d42500861fba2c7280430f1d16394021a74e9a9ca010d3974d4e500878d2a4a728043c69515394021e32a8a9ca010f487254e500869d3a0a7280434e5d05394021e94a7314a010f495398a50087a4a9e6528043785c43294021ad6ea90ca010d737548650086b5396c7280434edd16394021a70e8b1ca010d3a7418e500869cba0c7280435a9c86394021ae4e231ca010f194310e50086ad398c328043565cc6194021a74e918ca010d39748c650086b5b9263280435a1c9319402187ce831aa010c3d7418d50086b4b8664a8043595c43254021ad2e0192a010d6970c855008637bb242a80435adc121540218f4eda9aa010d3a74d4d500869cba6a6a8043c69525354021e90e529aa010f1a5454d500878caa2a6a8043d21c953540218f4ec29aa010d3a7414d500869cba0a6a8043d294e6254021e92a7312a010d6975cc950087952a664a8043ca5533254021e94a7992a010f4953cc950087952a064a8043ca5503254021e94a6192a010f49530c950086f0b8864a8043d294f2154021e92a790aa010f515388550086b5baa42a8043d294d2154021e92a690aa010d737548550087a8a9a42a80435a9cb6354021a76e8b1aa010d387458d50086b4392c6a80435c1c56354021a74e831aa010d397418d50086b5390c6a80435c9c46354021ad4e521aa010d697290d50086b938c86a80435c5c64354021ad6e4a1aa010d687250d500878ca1886a80435a9ce6254021ec2e3312a010d6976cc950086b53a664a80435a1d33254021ad2e3992a010d72710c950086b8b8864a80435add83254021ad2ec192a010d6a740c950086b43a064a8043d29cc3254021ec4e2192a010d69710c950087b0b8864a8043585c43254021e966598aa010d3a748c5500869cba462a80435a9ca3154021ad2e518aa010d6b724c550086b439262a8043d2cc93154021ad4e418aa010d69720c550087a898862a80435a9cf2154021ad0e790aa010d6b7648550086b539a42a80435a1cd2154021ec6e290aa010f623148550087b098a42a8043569cc2154021ab2e610aa010c5d7694c500870f324a6280438759253140218beeca98a010e1e6454c500870eb22a6280439694e6014021cb2a7300a010c7b76540500872d31aa0280439658d501402187eecaa0a99846f7258454cc236392c22a661665c35450f308bcec2a2879849e7615143c
  | 18 => 0xd4c21c74c8b06a610e39645835308735312c1a98439a9c960d4c21a3ce9a9ca610d1d74d4e53086ad386a729843565c35394c2187ee8b04a610c3c7458253086ad386a929843565c35494c21a9ce5b24a610d5671d92530870eb20c929843479d26194c21a3ae930ca610d4e72982530868fba2c129843471d16094c21a3ce8304a610d1d7418253086a7390c129843559c46094c21a3ce9b1aa610d1d74d8d53086ad386c6a9843565c36354c2187ce8302a610c3d7418153086ad386a8a9843565c35454c21e1ca8312a610f0d5418953086a7394c8a9843559c66454c21a98e4b22a610e1d6419153086a6b80c4a9843479d26154c21a3ae930aa610d1d7408553086a7394c0a984347dd16054c21a38e8b02a610d4c7258153086aa38ac0a9843479d06054c21a3ae8302a610d4e7218153086ab388c0a98430f5da5414c2187eecaa0a610e1e5498c530870eaa4c62984317dd95314c21c3cc8a98a610e1d6454c530871d2a4c0298438e5526014c21cb2a7300a610e3a54580530871caa2c0298439654d6014c21c3cc9318a610e1d6498c5308716b24c4298438d5926114c21c74c9300a610e3964980530872d31cc0298439a9ca6014c21c74c8b00a610e3964580530872d31ac0298439a9896014c21ce4c2b00a610e6a72580530863d384cb218431e5c26590c218f4e032c8610c79701964308636bacc5218438b5526290c21c5aa8b148610e4e5358a430863abacc3218438d5526190c21c6aa8b0c8610e5653586430863d384caa18431e5c26550c218f4e032a8610c7970195430868e3a2a6a18439354f6250c218daea3128610ce571189430863d384ca218431e5c26510c218dce43288610c7671194430863d380ca218431e5c06510c21a3ae92988610d1f7550c430868ebaa862184387d954310c21c3acaa188610ce5719933208636ba8c9990438b59554cc821ad2e1a9e6410e4d6594f32087872a2a799043c355153cc821c9aa6b066410ce771583320872aa9ac3190438d552610c821c6aa8b086410e56535843208636ba8c819043395c4640c8219d2e03206410e4d6598c32086b4b86a6190431bdd9530c821c9cc6a986410f0d5454c3208637baac219043b198d610c8219ceeab086410e677558432087532a2c219043a9551610c821d8ca6b086410ec5535843208726b2e65988430f9d3658c42187ae9b2c6210c3d75992310861fbaac9188430fdda548c42187aed2a46210c3f76552310861ebb2a91884387992538c421c3ac929c6210e1e6454e310870eb22a7188439354d628c421c5ca9b126210e2d54d89310872729ec4988439354f624c421c5ca83126210e2d541893108727298c4988439354c624c421c9ecb9926210c3e74994310861eba4ca188430f9d0650c42187ae83286210e2d549883108716aa2c41
  | 19 => 0x9a946298e8e6414a314c74b326a318a631b9ca64d41318dae5326a098c6f72593504c636392c9a82635a5c362d4131ad2e0316a098c6e76d49504c717b26a4a82638b19352541318dcec292a098e2f64149504c716320a4a82638b9935214131c5ac9a90a098d6970d48504c717320a4282638b5905214131ad2e0290a098c7b76540504c69c3a2a02826387dcd6414131c38e6b20a098e3870590504c62ebb68628263875934314131c3ac8218a098e2e64988504c716b24c4282638b9916214131c5ac8b10a098c6e72983540c636b94c1aa0631b9ca60950318dae5304a818c6e72181540c636b90c0aa0630fdd95415031c5aa8b10a818e3954580540c636b84c42a0639398d62150318dee0b10a818e6562984540c637394c02a0631b5ca6015031cd4c5300a818e6962980540c735394c02a0639a5ca6015031cb4c6b00a818e6a62580540c734b12c02a0639c9856015031cd4e4b00a818e6972580540c71aaa4c321863475d25310c31a3eeaa188618c6f76548520c716b22a4290639a54960148318beeab1e8418c7a70195420c63cb80caa1063879526390431c3aa931c8218c5f7558c410c6a6b90a998863565c054cc4318baed29c6218e1e6494e310c63abb4a718863179d8544c431a9ae42a26218d5970151310c727b2ec49886393d94624c431a3ce928a6218d5575905310c78a2a28298863711c9414c431b2ae9b1a6218d577550d310c733b2ec49886399d94624c431aaaeb1926218c6e72191500c636b90c8a80631edd95014031c72c8a80a018e6962540500c62fbb2a629e43999896114f218f4e132a8790c797099543c863d380ca21e431e5c06510f218bcec29a6590c5f7654c32c8727298c498e431edd95014321c6ac930ea710d1e74d4e538868f3a6c6a9c430f9d06054e2187ae8302a710c5f7654c5388732b14c229c431edc16550e218f0e0b2a8710c7a70194438863cb80ca21c43475d25310e21a3eeaa188710d1d7550c4388672392c221c439554c614ca219cae23206510ce9701903288636bb6a619443479d353cc621c3cc929c6310e1e6454e318868f3a6a698c43179d8534c6218beeca986310c3f7458e508861e3a2c728443531cd6254221ad2e0192a110d6970c85508863dbb2a028443875935394d21c5cc8b14a690e3664586534862fbb2a629a43475d26314d2187ee8b00a690c3c745805348636b96cb21a431d5c76590d218dee4b2a8690c7b70595434863c382caa1a43479d35350d218dee4b288690c7a70194434863cb80ca21a43879954310d21c38caa188690c6e7598843486363aac421a431d1d56110d21ca8a6b0e6490c3e74d95314861eba6ca98a439314f624c521a5ce929c4290c3e7498f504861eba4c7a82435a5c221d41218f6eca80a090e3a64983530871cb24c1a98439a9ca6
  | 20 => 0xd73181548c697390c0aa4634b5c86055231a6ce2302a918c3f76550548c71b2a2c3a1c638d5536150e3187aed2a0a518c3f76550528c637bb2a4294638e9526014a31c72a9300a518e3a54580528c71caa2c0294639a5496014a31c3ca931e8518e1e5458f428c71aaa6c2a14638d5506150a31c6ca8b088518e3554d85328c71aaa0c299463879526390631c3ca8b1c8318e1d65953318c70eb2aa998c638d59654cc631c6acaaa66318e2e5498a508c716aa4c5284638b9516294231c5aa8b14a118c3d76950508c61fbb2a8284638b9526214231c5aa9310a118e2e54588508c716aa2c4284631edd95014231cd2c4a80a118c6e72983544c636b94c1aa2639358e62951318dae1314a898c6f7058a544c733312c32a2631b9ca60951318dae5304a898c6d70d89544c636b80c4aa2639ad8b6055131cd0c5b02a898e6b72d81544c734396c0aa2631b9c860551318dae4302a898e5b63181544c735b10c0aa2639a1886055131cd4e4302a898e6972181544c738b88c0aa2630fdd95415131a70e0aa0a898c6e72980544c636b94c02a263359d661d0d31caceb30e8698cd570987434c69c382a921a630f9d85450d31b2ae32a08698c5f76550434c6ac382a821a6327dd95410d31b2ee2aa08698d9870550434c68fbb2a821a6387dd95410d31e1ee4aa08698f0c72550434c68fb8aa821a63c5dc55410d31e36e0aa08698d1c70550434c78c382a821a63461c15410d319a8e2b108698e1d54580434c6b5b82a9a92635a1c154d4931b1ce9b1ea498dc671d0f524c786aa087a9263535cf64d4931acae3b26a498d2e74d8f524c696ba6c7a9263c350c43d4931a5ce9b0ea498d2d74d87524c6973a0c1a92634b5d060d4931a9ae6306a498d6571183524c637bb2a4292631b5da54149318deecaa0a498d6b70550524c6b4382a829263719c74314931a9cea218a498f0d5410c524c6a6b9ec829263535cc6414931acae2320a498d6a70190524c6b4b80c8292634b9d36314931a5ae9b18a498d6a70d8c524c6b4b86c629263599c74314931acae3a18a498f0d4310c524c6a6b9ec0292634b9d06014931a5ae8300a498d4d73180524c6b2b88c029263351c56390931c9cc62948498e4c63d49424c733a90c2a12631e9c065109318f2e03288498e4e63148424c726b18a4212639914a6110931cc8a4b088498cd671993324c62f3a8c9992639399752cc93193ce930e6498e6452986324c733a90c299263359c6644c931d8ec430a6498cd675185324c72b3a8c299263b1d48614c931d88a430a6498cd570185324c70e2a2c7a0a639398c52d0531c9ac62968298e4e63d4a414c726b1ea520a639398c5290531c9ac62948298e1d6510d414c6373b6a4a0a631b9d85250531c5cc9a946298e2d64d4a314c717320a518a638b590528c531d1cc
  | 21 => 0xf46a1cc428887a350d62144438eeeca88a221f15435445110f32b12a228887a650e6014443d3286b00a221e71515805110e4fbb287a8087271d94394043b30e0a1ca021e8d4398a5010f46a1ac528087271d94354043b30e0a1aa021d5a7090d5010eac38286a808787dd94354043a38eca1aa021e1c7650d5010e8fb8a86a8087c6dc14354043a38e0a1aa021f187050d5010e8c38286a80871b9c861540438dae430aa021c9f7650c5010f46a1cc428087a350d6214043d2a87308a021e95435845010e3dbb2a0280879a5895014043ce2c2a80a021d3671d5254cca3b388c0aa6651d5c4605533287eecaa0a99962e5458843cca9b3a6a328e658bdc96494732c58e4b24a39943e7418151cca1eba0c0a8e651ddd95114732ac8e2b12a19947b7654050ccb35394c1aa4659a98960d5232cd4e4b06a91953a70d52548ca9d386c8aa4650fdd954152328eeeca88a31953a74d42508cab4b8664a84650f9d0615423287ae830aa11947b76540508cb1baa2c32a2659558e6195132ccac530ca89965573986544ca1fbb2a82a2654d5c66415132c38a8b1e849963564d46514ca3bbb2a228a651d9c664d41328eae3326a09956970ccb504ca1f3a4c3a82650f5d261d41328f6eca80a09947671181540ca3ab88c0aa0650fdd95415032c6aa8b08a81963954580540cb2b31ac22a065999896115032cc8e4b08a81967261980540cb38b0cc02a0659a9ca6015032cb4c6b00a81966a62580540cb3930ac02a0659c5856015032cd4e4b00a81962d5498a430cb0eaa4c721065175da538c8328daed29c641946d70d95320ca1f3a0c0a88650f5d060544328eeeca88a21963564544510cb38a8ac0288651d9c464540328eae2322a019569708c9500ca37bb264a80655adc1325403287ce830aa01943d74185500ca3dbb2a0280658e5915014032ce2c2a80a01952e72d5254cc637394c12a6631b5ca60953318dce4302a998c6d7218154cc61fbb2a82a6631b9ca60153318dae5300a998e365458443cc68fbb2a821e6387dd95410f31a38e0aa08798e1d5458043cc6973a6a5296631bdd95214b319aae730e8598c7a70d9642cc63cb86cb21663875526390b3193ce930e6598cd67199132cc6cb38887a0e63175d843943318dce5b22a198c6d72d9150cc63dbb2a0286631b9ca60d52318dae5306a918c6e72982548c636b94c12a4634b9cb6395231a5ae5b1ca918d1d73d8a548c69b388c52a4634b9c86195231a5ae430ca918d3a70186548c69cb80c32a4634b9ca6095231a5ae5304a918d1f73582548c68eb98c12a4634b9c86095231a5ae4304a918d3671182548c637390c0aa4631b5c86055231a5ee4b1aa918d2c7258d548c69db82c6aa4634e1c16355231a68e2b12a918d2e72981548c696b94c0aa4634d9c66055231a3ee6b02a918d1
  | 22 => 0x8004004002007802800d004001c0100030010098014000001802800e006005000800e0000058000008010000000c010008000000c000000000800401000900000000000180020004000000000002800200b0018050004007000001800600600180280560070050000014003001006c00201f0110014008000013800c0000000110004000010000002400008a023802c02a03500000200000000038018008000000006c0000010008050008000000004000a004000000001e0000118008012000015802000c00100d00080000000100010008009002006400c000009817400202300000140000030010000018003001003000000a00c8020000004000002001400a005000001400700d800c00400a011000001a0110000010006013001005801601500200000000000000000002000000001000c000003800001e006000000c00a010012800002600c0088018066014003000800a001000001401c003009800000800b007800c018010001800401400400b800800200100900000120080020014000001000000c0020050040004010001001801c08c007005801004a01a0028064013599c75294a438deeca90a521d6672d465190e37394c128c871b5ca60946438dce4302a321c6d721815190e3bbb2a228c874e9c343542438dce5b0aa121c6d72d855090e3dbb2a0284879ad4960949438deeca90a4a1c7a7098b5150e3cb84c5a8a871b9ca60d45438dae5306a2a1c77765445150e37394c028a871b5ca60145438dee4b0ea0a1c6c725875050f34b16a1282871edd95014143a72e1218a0a1e66629845050f32b14c228287999896114143ccac4b08a0a1e36435845050e2ebb4a921887355c46050c43c3aebb2a8621c9d71d954310e4f386caa1887879db6550c43a3ae1b2a8621d1d759894310ecd384c4a1887665c26250c43a3eeab128621c9e70d854310e8ebacc2a188747dd56150c43b1ee4b0a8621d8c725854310ecdb82c2a1887661c16150c43a3aeb3028621d8e729814310ec6b94c0a188747dd56050c43b1ce43028621d8d721814310ecb388c0a1887655c46050c43c3aea3028621e8e721814310f46b90c0a1887a59c46050c4393ae23028621e95711814310e4ab88c0a188727dd943d48438f4e030aa421c79701855210e4fbb286290871bdd95214843e1a86a90a421e95439845210f4aa1ac229087995496114843d3287300a421e99435805210f34a92c02908727dd943d444393eeca1ca221d977150e5110e37394c1288871b5ca609444393eeca1aa221d977150d5110f46a1ec4a8887a350c62544439d2e0312a221c6d70d895110e3d380c4a88871e5c06254443ad2e0312a221e4e731895110f26b98c4a88879a9c062544438dae0312a221e69701895110e34b80c4a88871b9c860544438dae4302a221c9f7650c5110
  | 23 => 0x70000040004003002000400400e0058004000001005000400800c000011404c011015802c0480100000004002000005002400a000003000000000b0038010000001008000000000601300f402c00001a80040000050108010002000005002800200700100140000010000010000000000800800800100a8040002006000000c03e002002000805c0240080004028009003004801200f000806c01600800180380000260008004002009001001405e01300080240000000000004000006001803c00c00501100100020080028000004015001007801e0000010018006009000000801c01e00080040000050000018014008005801400601f000000c00000e00100ec00201200700500000060038000000004000800c012001000800800a00f002800c000031003000400000000c000000a000001001001c001035000000a00d0058000008001000803c00000c000000c00a011000000001e01e000006800800301f8024006002000000400a00000080180080010080020004000000005800800100d80100000090000008022000000000801c004007800400000f0048008000005008004000c00d001005c010002004803001201b000000400000400b003c05c00c001000400c002005800c0000000018004006000002800c01a000007001400001a002803800400f000002c01e003001800000800000000080180010010030008002002000000e007001000001e000000000804609a00080380180280000000002004000007000400400100d8006009001807c00600c005002c00000300b005407e00400000b800a00800180240040020020000000029004002801000000e807c042016001000401200d00580240040240028008024006000008c008005000000006601b001000800201200100240040050038030006000000001c0000030000008040005003000800000001380a4034001000801400000e0088068024010000801402200100b000400c00d01780080000010028008008000000000c008016019000c002003004000c002016001000000002b00300080000260018000018007003801c00a0020000010014002000801404000100a001c0060060098018032000000804402a015000802000001d005000400001d000000c00e01b008800000c003002005c01a000001800000a0080008004002007002800401200700280080060010000054008006001002400000300000980040050040004000013001800400000000d000800a003001002c00200301c0004004010000000000006e00000000040030028030016004008000c01c000008806011c00902f000402400000f002002a022012000c0020000040040012003000003c0e6002000000000c00a00000080000040030064002017003001003c0090028028000007009000000206f000802
  | 24 => 0x6ad40958ca5360146c0003761ff78c90386a96a1b38dc800d4611a7ed24ccf443d1894585975080b6d115a8ca199b66d6142c18db27993ca9d90000e48754b8046733c903edbf564a2958585220ad8bf42853e870eadcc0c86b03fd146475a40413d2f319a2bbf00020fc7aa42b750a555ca26c120596049d48f12a8f86151c003002c00000000f800000000200400040320020000014004001000800009c000004000002a000000800804a007000000800400400a001800400a00c001000002e001801801e020003801001e0040020000000005000001401401701700a80000210010000002000001002808800000200cc00c000006801c02002a0000080064000006001804e000007002002200000180080360010010044002000006000000a001004001c00001700000040140010020040004004001004c0020000018000024000006802800802e00c8014008026006000000e003001000001003b000800c000004001001001200200000100180020008000006000000807800000400000040000000000000020000007806c00000c000005000a000008000000002c007803001000000580000080030008008000020006000000600e0018018000001000000c0080000088000028004002800000c0040020000002002000005c002002002003000200e001000c00a0030008028000006007805c02a00001a0004012006000009c00000a006000800000000f000800e0010008010002001000800005002a01a004c000000009000001200000080200000020030000002000000802401e00100100000060000220010000002001004c0000070060000000000000003400801600b8010000003026801801c0290010014006005031800007a01000b001800001d0058074006001003002400000f00a0014000005000804800200000a80040580010028004000009006000000000b000000002801801d806400c0190020020000001000000000c0010020010006039000800800c001005003810600200300000140030048074004025014002004e0040068008002019011805000000001200540120010000004000001000000801600b0090004008002000800800200000080100160050050004002000003002801201b001801800e000002000c002016000003800c00d001000c008000001005c00001c00100b0000000001003c01a001001002404601900080180000250040004016000000000c000006002800401000a00000100320150028004054000000000c01803e003003000203b00300140000060018010006000000001400800000480080020010040018000006003803001e013002003403a00b001000001801f009001c01600000c800003e000007800800c0040060004048009003800000a01a000800002e00b004000000200a001003c00000
  | 25 => 0xfd18324ea5f4d8432a46d00000550004628000db86d67370f19322011d3a8f89ba22683870000024c17055332800000039db32142800000000002bd6b2412a2d0d701924abf1b017e8b93c8211945807781e2619832d783662e6bc1cb9d591ce5c9f10006e399f852e4396b8b5a4000ba40a21b54efca6418081988608a80189bd06d0169988af64946cbe8002656ae45435c6b3bd050000000068d414c0c5b8c5d0bde4c46f69bca87347b2ea213477cbf4bb82dd44381763ce322d2a63390881bd23ec4082b4f334a1acce0003264000222223a2e0000421000000000001a5318ff08b441735a860522a00000000000008e000024880002251649844000b29c450dc55b4000152c001178d0d6b78000c60b665f38f6b47c00e6bb26042ae03f0001ff46ae4743f1aec40005f6800000086c9b648c2410a6e2994ca9b8573e2dc60f32dc9d8625850323800068a56f20bc000b4f4f8000076a18a06fe80400071c209acb58a80005c90410e3429410a0000b2a0000001508d7edfc3ab8fac3427d438e800048a0005bb03fc2c031a17d85b4f269984f9b6c061a067000117d6100004ca477b2782f352f23d1c520000000980589e0836728754c40006402cae0001425ae101e0fa0ac19d2b1128e00073e15acb0a32d35d0000b566c52ba8fb95705ca07d2f795fe4be40b0001b3e2a8581800017812141e21059c985d4c180004c4e9344682d200084700012b62c71b554c78d1c98caa00007ad62073d40495048ce65f5c605d59a612b0a8b449ccb0a857c9e21ab07a15c30aa88a8b5e48b36e8a14eb450aaf6dcd4d4c71f986d2b45e4573c88554a233e0fad48e9434f3a0b8a13ce07075d21f01d054716ab6e0542562208e3b00bf69f5bc921c1c5c292c226090201093b109a8452d2221f249d1a489509c35682b80dc93d8ff45c88c7201b9400609a06ae28d576911b3f300001deb5099930c00008fe62e5538000c2617cb9c1910c223923168506c83442a7041047f769a9c28079b639069fb94d6d174b631d1a5c50772b378d66ea26599d9a4d88d132ad12e987e321018f9fc48c6ae499095118098b663477db8c81954d3a006708054b1e1e34320005b456d968e1070ac9ef0cd00020fbd5cc000a2f21e0860a7024700027b058c47d3e5d73834060a2402fe4a508ab4b142ae86400039682dc000aa82431e64000974ee1b47504c4e0b2aa87064414b8002b400000007152a6d4cc00000e5889c4ce2b33bb07170a00c00746503c0b14b210b8258067f653178564b4ee165b65450a54f11735ca0d3533704b176f64a7a59506e1258a1b6138000af635a000003c00000000002aaebab2dde3439a00000056512a4be87431bda0d923cb6d5908ea586258c0c287253a833d4203545722d6fe6216b484c82359e385c8d232e4bf425d9086fe67
  | 26 => 0x58222138848f16db139c2821a2b60da92b914896217dc4b779fdc208fce9629a3f4cc75bb286e2cb272ca104495d31fc102a2e93139ed454c298539889939ebc3a3624097b7413d01149433220330280128480003192bb93f4b563122a7c8de16f022b29064c95d61d01a587a10000032f86cc7ccca72e9ae9cd520a18b60dc0e453e6a4d5a7e0062fccbee9b87e93d77056000000133a375b4a9cc37e2f5d644ea300000f8b7e4b99a900004a617d0aa9506000c903f88e1d36687d6741c5cccca1073930282a0398322ac74000e525e8b55836241dbf5f7416349010001b9814c30211951d88e6e3b11191113e4550d26a1a00000000003368000000559974d31411c045996d25aabf0e61ee876c7382f19aecdd6426973a2d4aaf00034e198c7069b48001879c340003270be03b01c345939d42cadf86882a14884c4882b00000005cb4f09bb49ea67863aa1a821a4f42a07114e6a0ee1b5fa389fcd33017b72d5e667638239909ce000000264169478c49b9558048579e799f407ac7510276cd1394d441d31bcc022606000929d6cf8cc00000000006476c780003a2d48185ae37802a835708d300008f06f51a1c00072303b8001a9200000000007ad02180005340003f23dc2d2c58aafa70308414da46464b331330366a0e35b8c45714626d33e83df82c65916c589367219001482508ee53a0170aef5780001860ce80004d94d1916cdd812b0c58000198592a74c00000015831c600052c19f0000000c8c0002c595865682c3a9256d800000000000000002bd234dc9a2a317812ccff6c9b56a2e8576055e3010c71d7e9870001f74000dce0a78001bba7ed800306d24a0f85eb14810f6bd2200196927e00036904b152ac4923c08acfce92b544a8b8000ccb6838adc0000000000e780008bb5712c16156803b33935455e56d0d6814382a1b700000000009ba00030493683e3000248000042c0000d549d213ad341042d90cbb524109667b000016386c30e5a33a6b5ecd86000000000079a1bb1b2093c21cdee41d3aed984207b520000a7e00075ab44521eae90795950cc200051c8000000e9c246c43d1b07da75c03f83160000c000000005f245385ecac800000000000004aec61152400000000039e400003e8001be903c0006988001ccea9315924e01db3f61271eb8a244b480000000000000000e3c4809611c58edcbb1671557ad116f86c635b2e703d33bb069af2181e82b293190c00011318180000009963e023f482c084316a7e41c80005fe21d893794f20f06c8980afc0000001cc4bff7559e0d752535336a97c0008bf22eb1c98cade534f17e04bfbaa64d1a8085cd801bf902657616147419c1901de200002ecf3ca8b45017aa65000022f00002b9167ac814e800000066c00019955bb71b8979aa878657d890ce54ea29bd2e040
  | 27 => 0x47980007e61146848000000b09708800023215e1ce80000004d450d27815540004071a356b4972b69a7fc00089c0eec952a0a4f0321e9d8fc04fa2dd0b0fb6ea6c1760000d46483000081458138a42e0a2371216b588b7c91d6653ab7587515eac633204680fee4f40230d4235bba4d300010ffac02aee9c535ebae5b66c49d2e97f0002a84e5218f03c8f481026f232e2e82b2800000000016c2ba574a0001cc0000703a9187be257135d1b65aeebe363b28c268531484ba400bc796ae7a718000bac1b288f42827b023ca17c0bb07e0000b945c578b05aa6f83689711d807150b64b82af81690e65fc5668001bf69944c4036e768ccf0000de00df00006906f80d42ce00000000000400002af5a1e91b38cb1f14f2a672ba047c000897131af7c00033c93f8000bd6a560a6240000000024f0d709b63695733095d640000c100015de52d4d2b97c000cfb00000006520003a62ba00000007500001674000000382da36c6d46200012d63890001bbef500000001ffc000000405000000027733100015e043a40e918dc080005974db5cb8000384375089ea9e32913f080be0236517948b84b412f8728fffa786f0aa8c53c811038b3fd6f5276a6c3ad800059f0000a182959653ee175fc5c11135ea5ef46f6df1030c28fd6d5f800026000001be5fc0000000cd565a35400828982540ef2e74253ac8001b6431418723a4000170ecb291d9e04b3b062d0cbd800023d17c6000865324000112843400000000009c3258ab7448495759726f148aad34fea61561e3fa4550185552a230002a61bea5d95e10bb80da4413982469c6252f5ed02304ebc4804e2f1668e8e50001c41d0ee3e24b800012c0bd00028784ca0760000152da80000001b7400000034b96bd6a65325d5400054f00073a21880000000c626c00000001c70001c940001f0304644000060497edcde72e387800000000000000000004e42fb18df4050001c6093401a0001f680e00c6dec2dcb8361c24ed5581bbcd00e2f28fb428bdc35b17b33231200b64942a718d65e20002d35d52e771f8952ca4e86333cb4e80001ae0000e2600076c7602cc2a5c5dd0af8b680afa9600032d8ac235dd13a76c07a0e7800193c0004713bc25184600b20000cd828e0006de10c558e7d72e4ac9ae2431549d94f92a06753a480c9930e840d7849d3f04532054ef5888bc57449fa9bd07b65ea80000000004e480000001ef10e8000f0285a1ffa14ef520002e10001a8adde06a85122240005f58000f0abb80205eec2e22820003a98ec60002676085b5c000659b47875898e67c89cc60cb740000e100000005e685bf3c40002d00000000cec1d9a6880000000000000000000000000159c00024216cb1f853d3bab05055668105798cc1867d60000d2c000ebc3fb175400000051aeab80d83377
  | 28 => 0xdf69da8fc26d1010413e000dcf00038e58f60000e9a83637a4885cf13984f383e1b674399b6cc15fa8000000bbb16b2f84a4200034a80887d43826cbb3196561f53230a4827f37c4fb937c5b20000ed84e60561c7c2aa6d403ba0f61bb801c5364139c80dc000afd5e332a5cc6be8257816c0003fb00000011240002463494dee1f359800011a267789a9af81591ff0e71e9c8b0b0508612e448811734588d4bcb7c8aef1df0fe83a761b2ce400050622bb77d148005000000181a3b9ecd25f7ccde6500003699f88130515468cf8545682162c17c871dd473a400000075600017e0abb1938af80004eb59325807af5f8ad0b890000a3f3098a41ad777b6140a547904823e98388000a8995e000093400000003797263e603a1ca1ca60004358001468bb400000004cc51e208b13d092d0c30f43f099a5a844b01e1c84a130002351abc00000000010e200019a0ee000000000009240000005b1854c0000000ee00016f000000000002b785e000005fa8000019f84ee00074600032f32f437d5113ab99bc72ea689ccd26c69660223196508f220a1401002a0d1dd1d480302a46c680009e6653000205d8ba3a23d682cf1cc406d1b05ddcfa0003b02a317a8db942290ecee44d1baf9be53e2b993f6a2896625e2e47ae60b8a6591b587357e436e66637acfa217f23815f5b8a59844604f00935996e52cc880228900001383c8000341982c25c4ca1002b3c29b99c08eaf8ca3011627292ddb30c5f33580015bf000142e66800000000000009ae00071b4000000e861d90e8a8f8b87189800033e0000000ec40000000000bdc0002c76731fe4618c7100025e048200005880a64fb0db745b5f8d362ed3b42cd43f0ea70378174e688373c92f616162642cd155588d80c5ba4000000412c87256d0fc6ad1ae613a3540006b740007a88db00000001ee0000b60001cb20005e780017b84e262d80001000004de8c5d7924924e71e5585600071e80005a0e9b4ab4000a6c00000008ec3521b317d4000c2a2f4079170c1ca92a29e21e4a1c2f100025a9adb00000034a0000b6e6d124b9508a31434402086a1a5dd5ab90c46764349ab442a41450000000efe00000029116d2d1a49d0b495e29d574faef497ed3639b811ee584c61e525772d007b0002bd5bcc00046684e969114a00cb630e5600015b2760b3c3c500d80000949742dc159c88ad4b4aa132cd5eeb730480007f20000ab40a0000e9561e0000000c40000170147004d97e1f25d3022800000000000000000001c20a0e48414759c2000221b3b81d1e8101b41b6000c770ea2ee5b4888b4dac00100c6145a29fc878400000000007480def4e9188d0889d0002b7186923e9a180000000006c280018e600073f0250000ca0247000000000037ac00133e0000000001376a821ed8f740005f00fe3ae4
  | 29 => 0x58669796d60000382c3858bae89bc8b672501c98000000000000191200017529652dfe5e00034f49ef03a9f824c0bc300000016425e413312820e48708a319fc001484830440b4b120ca0973632f48a441f24c90a98e042f30b39b41982fe266081772a000626ad0104001f3e5280163ed8421045ba00000000008e8000ad735e1aa890d3f512d000158abfb000245c549853510262429c00073b3918f228cb4d61530adc0236fc80016d4d7e9aa300cc068f72a2162979c25146406708df96e21986404f0075247ee296e7a8a2a6b6c412231f1ec826d0865163df17d4f6e6a7089e9bd1625cc1044d65a7c0890018a585946e552c22dd3acdcc0000000fb6bc7344248c000000000000058be66029c000000000000000040e0000000000087cf86ed30584da0003038ac4af5a7044f0f452628ef00018a482096406e2dc956a05f3a414a4000b156d01c356fac3186c448c00092439e11d2c5e9390990a21ae06e42a90ee4000060aca703fd1e0003b68cb00007074e38001354000589c001479000000342075e5d2000000034d00023b8000000a4c51480000000205aeb4ec3b41c64a6a47ce889a17272a5d8b80004f180000005010f82f2d0a20002aa12a8372c020242c18b6801d1409695666a2505ef30a1cb6734cdafdc20c00000015f98115dc0a5afb9048d5b0002948f56a532499ad0660872518396121ab270f1126db9a0d626f035c290b3d1f62690000173270806b350649230b3500383744cf068800016d89bc0019ead3209b0d8c05ace063c8b84942d18395c000000a116c4c318bdfe0324aae2c5906cd2c40000fb2000506613ce0626904788900006e20a489302e400000057e84d30003e1800096cc4742a2a20ca0dfe254330cacc7a61c89c6c1af65166a75ac000145b0012b8dd412f04a800117a0004af6b0887ed66326800000069d04faa3c00065d0000af43e80000ac11b995c9674368001bbf00000033d9a9e56acc9811090761f0002e68000bd00001f303e210b0f30e6cc1c948000000000000000032fdc1478a5f8ac8c4fd5693c13a8883618e00000001ea48d00b80005a23043648bbda9a000741b665a00870a2ab87f94e0f96b1b1293432d30f518652b82481258f246365912db8000ffc7790d3000054ac138000000a46db6664ac83719c5174c8a88408abc04520cd7ec0c599da81dc44d83244b27d8ae0000f93234e9ee49053ae218c4adf6f827a509004967114501e020e5d3c0000720e74f366fd93c00005124bc9de7f3716876f61ac3461234983679f64b0585cdec50d8e3ba68b8891d4f59821478d904a509750b0124167a0ec73db2f4a929c967c89a7569bf4f44d88640d8a9b6659b0e222243d052a65d024c9e4b1b43c0202052cf6ea737a43a9cb0609b871d54e13429003265ead24d85c817a61b5
  | 30 => 0xc3d8a06c72a16b8e02f2906aea409108ef876558800004d6523ae072781fad44e327c31e0000440000200085ab5b4b928b47382be8b4000070cceb000000111ec066b8c0012140000000960bae2f54026d0517cc1d00013c590cbb529c838c04228d46e1bc13d495e07567f87869991e636756be2312f8ae58d04e272b18721a560e92d9ad098c6b01226a77891656a4dbefe9c8241c9fc067976672a82807fe80e50c53725dc4c2b6418906a05403356f395dc2cc2a70518f5c8ac867623102504e13d2ae08d88985c600004fd8cc10216608a87c2dd33250badc605c112aa06167e13910a83824bdda114d8db019e77a02c82949a513da740001cbaaad0a1f76c0005a664e21900000005f9b104000185836413c0003083a007f3ac800033d09f9af463e149a24c84462e1af42843a01f9266f1e905cb66b74011603c94164a2985a5a4a7a7018777d40142c78d74bb675e5ff3645904a372a507b57285d000494ac42cb361d1e8f56099050c30b800008323c78001c2ab0e2d2142cb600000e136a50c2721183930c90a4481921cbd8d294c5aa8000000da70000000a010005b100007827970000f940000006acb5fc45ecdbd0300000990000b51d406ce09214f98f52b000034832bd42e17a267c32977c31e0731a48eb05fe01d06c0000383c899bb09821673f425ccdf60002ffb895c1eab244d92f008e4ce7399031cf41e732f1840c6218d663a44406b3ce558a239842c5550212504b9cfd4f432a1b3c9d21b988b19a06b372a960151a0eb58e2a5083200056600006b00001e21ed013296231ab6ac8754fd22882d070211689da89168cd5d5f0238d99345b1de2b206f278012da0b42991bc1ff04213a24055b79bba93e2750fdafd0e7110a8b4a0500a69517469a51c74b8e2e6914135604355f20a55c04c93e871606c40256bc955660a26e2b5c00034775c543261678ed0374f00a8f0800002c1ab0f3e0ad1c80000000bfd4768000e6c00022c882c000c760fd10a4d6271f3511a3c5142a88301f3cdfed62549160c69a46d0ff5792c50a4b6f88480eb65df3a120c443c51098c0a703225110001364b2e41a72418e9b242ba0001028f668123bea0f441ecc0485b7d8ab3d1c18c9dd9b5453000022b00b93a5583975895a1260440c243ac586534911887a70200034e000059d0000000aae2a911ba5a58fc9a970f88c92e032b386312dc9637071a9454a2604b0000ffe680ae9d140fbc902a816c48a310ea0d15e01b69476d051ab0dbc4f83232ac22615b67d5000235db3f73f20a9868f546216e23130d9e566d7903d8964bad2f32f90582d670968fd1568798a5107f509b0c9352ad459baa6023ab491a0cdfd0db48f975e163105037cdead0100a6388bef1ab5b6dcb76927b91076f9a000afde21178383097c043335c000b90519142
  | 31 => 0xac2fcbe632b80000002116eb13594b6c6f12e0000000aa600032b1795592666562532e0003b0a74032e4c50620001cd0d732270f3c3743940bcb88437e7673788ae020a00025a8000000b70ce431b844546845497a00a3d34e9801f77f09f4521aa40068593550124060050f71071784e0874063a33d88650400012f567640f315a701174ae3481a9f84de9dc6dd9dc402a00013eb81480c0cb0751bc600002700030c883ad4666c9fd4076204c2209c522813890c8d395581d773da30408c6893e9257cd1c7cb54380000000004dc0624fbecdf000239cb78000000000000010a16f2968c1a25d956ae8cad900000023e131a6361a29080ab200037701e6f582aae168374d4cb28bdea0d0f8867b00002694740000eac00000000021bae5c3cabec54e989ee3c4126e4872db024b04b3300181c84c0003528000e2c0001fe1a520001390ab0522000261c0000a807fcf7a0e00002fa6c66dc4f1a8860398691d18a7c5489dd013a1e3330390c4ecc501a480009560007308b7c7a08ae1dfac09424d0b55120349eccb455ca2000009b72144d7c000d866a131f42d1b31861154c00076b2489c017860003ef569d5d6d206f9862011c46b36f1a180aeaec211990000000075049aa0005f300025ea00000000018ed9260005bd8ab909470b70b0001757956000339c00000000026c868815a0cb1db8e26cf171b18d08cc23908ce9fd822b02961912d95a0003828000000d8b263b3dcf8b7c66dab6980000000ce95bc9c30000000001736000170f2480007af3889e6000006e0ff2c8600000006c8000d22556c72002e000eb8cc2178000000035cb4bce62b2415dcdc80007fc1cbc1896feb655bf23d59b81e920100000007eab9f1b2f9787de5ec53dc1662a387a0bfcbbf93440180014aa9920003409a2a3f761705fb372bc419f5574d562b45d7c3ec83052403592704d90c53aa11fc6ea1f706074d036916409b8a1d3eac855351441cf07c710400010100004a2a1b05c7c8702ab0684d640d1612b9d97202e2a008316989cd000159424a0001098144000a1652e88f01b05762df23647d2140bbbb0143bc490d5237d00e42e269b80566fc8d064675d4b0420128e29f464a67d4750afd2ec85700b087c694a086c72b60000af607021995caaed232b2897d20a400016f42dc00056caa9d1866655e2725c15fbb75f2abd00987e46e0b8e0c1ec391c281db6708836a0a9952b27535a4383185e0b02047aa1816a0575280d407b5c7425b84974e0652a887643c22522ed1de2ae0b2c350a4f587cda32b015e2cb07c108f0cf12848b309500cb1f682a0001f090acd2774135b19ca0001ec0000e28e884e28c4149e0002252ba80004c867f00000000000001f2a0000006489b64db08a65802c8046879d0344d6eb6a7874a49bf7ae80332c6952140607
  | 32 => 0x8c000000000000053bba48d329c21d597a95f0b0402100009f6a0b05ca3259aad14067184800030f1cc93fc00097b5d4c000000147800000000011800000000007c837c2c6e516a4e00025bc00086f00005500000c00003190c408f93b2b020bd20000eeaaac0007161d2c64c0d080f4ef9f88a04d5064098e13dad708d2800057fe9100013080004720cd09b1c4680205c1b6c000e962fe99bc000000000316400094016a000071070621385f0000d1f00037012f92123990b8db63428662a511782de0043b1fc000eb13fdc041ba41fd8001349aa6a2a0001c247bc6a84c6009969c2800caad645cc1a74f23040c78dc242824f8fa338d28ba37d4800006ce1277b900006b900019ac0004381ddfcae49800021fc746bae8002e6f7ba5aa6c38e001fa005e19da15adc2af8bc0000c0800044380015ee5a91d42d8681c4601a094d1b140ae000089d649d9450603b1c6600017436bdca80000000000ba29124c7b7dc51ca4a4349e9198733131c85587ce794510800000061c735b1cb58275500016c8b1c0000000000000103000000135a0006eb967f1fe09e0002c61ada7f8a6678f0f400002521d690169fc36b800000012965a9e38000cab00035940000006c10ae451e0002afc001346921734b7bc0008a14411c609f2202000032197000000000018ce00034d357c00000000000000006370002ed83aae710000000000516dd023d9b7c715252ae3db5a5ae45827682e004d5ac0296fb027900386b0f127253739fb0e7400000029707349d71a8179c1daa1f7429d599d43606fd3a281748de56b2c64e4ead54c015182c434223943cdb610361ee28cdc1a97e00002143d8b134b1b5a0afe000000348cf34b2cb4c0000e8a000000000011a7226588000000a540000e80c02c200000000000e470000000412bd5b2583c535c747326010a000c6a629325400000069080000000006340001ac2a3180008cdb7a000000000092755043bb880ede39600024700f48fa6a3aec9af8dd533707b81e38991d0b5dda32d57322269ca06a5708a97b48385548000000000ddc55b95f0ed2a2b1421720dd24a61af0b758c000000006e3482a803d1a4a400000024b09d01523930002ae962819b5aa00001823513f2800045ab7a1b0a774c7ee013dfb28556ce5a3b9afbd9a4c2a24527b977824a365a384976a51071dc04c58b686f34e7d6692385dac000000d5529d84c113e00015a9e586907ef0000000f4ad3c0000611220b8257f06deda096d166b4592860410001adc796000354400099eba8483934d0c0b64800000112247e00534e552190c120c0016c0ce47578f4d618c0715984c4000dff068252cecc8220000576f36e5b005a6c58acc612d12674b3855b3e72a642bae1edf124649a0d2a1e011a8c4c81a1ed10a600000000000009bae192d62d
  | 33 => 0x6452d5c39e8594420748bb05f95ee7acd00eb8370f000163c0005b839104b257975eb64c0008d605869ed08400009f00001d708300019b053a35342732756ee87a8a02940cac37704815c5266c5310b8001ac03e40002860000d7d10d81c2f8ada800000000006
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xd5114520d047458d5114520e056458d5114520a63865456014520b40835456014520e41635456014520a888059043cc520c89645c043cc520a2684d9451cc520c0c651d1534c520c44651c5534c520c44659c7434c5209c1809c7434c520a0c85590434c520a8880590434c520c89645c0434c520c0c659d2314c520c48655c2314c520a2484594510c520e4053145600c520a48854c5600c520a60854c5600c520a8a84d8e63d4120a8b8650c43d4120c88641c143cc1209c1811c143cc120a0e85d90438c120c8b645c0438c1209c1811c1434c120c0c75191314c120989841c1314c120c88641c1314c120c88649cf504c120a8a8690e404c120c88641cd404c120c887650d404c120c0e75192304c120c88731c1640c120aa1811c1640c120c89645c0430c120ac18010d610c120a8986d0f400c120c8976d0f400c120e8343587400c120c89645cc400c120c897610c400c120cc173584400c120e8043584400c120c0e651d1300c12088c87591300c120c8474585300c120ca074585300c12098a849d1300c120c89861d1300c120c8a651d1300c120d0a651d1300c120c8874d91300c120ac181d91300c12098887991300c120a8986991300c1208c887591300c12098887591300c120c8b87591300c120a8a87591300c120a8887591300c120c8887591300c12088887591300c120d8074985300c120e8164985300c120c8874585300c120cc376585300c120d8074585300c120e8264585300c120e8164585300c120e8374585300c120cc274585300c120cc074585300c120e8074585300c120c8074585300c120991811c14310f10a9080590434c71081c875954310e10a188550d6010e10d09435c04354a1081c87591530c210a148454d610c210b098414d3048210d087414d3048210b088454c3048210d097454c3048210b088454c5348210d097454c5348210d41535c45348210b088550c4348210d097550c4348210ac0835846148210a188550d6010d10a1485590434c510c91645c0434c510c60655c0624c510c1475191314c110a448359461481109a1849c73048110d087414d3048110ac0864c53048110b40854c53048110d80744c530481109a1849c73248110c60655c43248110a61819d865481109a1849c66348110c60655c46348110a488654c5348110b088454c5348110868865d44348110b088550c43481109a3845cf6148110c48651cd6148110d82745cc6148110d81745cc61481109a1841da31481108e0865d13148110960855d13148110cc076dcd3148110b8284dcd31481109c28798d31481109c08758d3148110cc07658d3148110b408558d3148110b808458d3148110d817410d31481109a1849c43148110aa38458d2084110a18805906454c10919851c14310c10c19651c14310c10b088050c4354810
  | 1 => 0x391a861c14354043c1a861c14354043d0a821c14354043d09821c14354043d12811c14354043919811c14354043d11811c14354043911811c14354043a61801c96115032a18805516010f31c61725c46055131c1776dc55410d31d0b721c15410d31d08721c15410d31c19861c15410d31d0a821c15410d31d09821c15410d31d11811c15410d318d1801c56210d31a18805516010d31b088055043d4931b08805504314931c29645c05214131b0582151414c431b1180151414c431918805d54310e21a19801954310d21e055454d610c821e0554589310c421d22545c43254021d21545c43254021d42535c43254021d41535c43254021961811c94354021963815db3254021961819d33254021961811d03254021d42735c43254021d41724c4315402192a849cd2154021b21848c52154021d40734c52154021c1a765c05450f30c14545c46050f30c4a735c062547308998790c6050730a1880590544c730c4b655c0624c730c19769c35410e30d09729c35410e30b088050c4354a30a24845846154a30a61819496008630929801c96115130c25725846115130c31615c06115130a1a85d906050d30c28545c0625053081d87150604c530e0854d88604c530991811c14350130c18631c16155030c14635c46055030a19859916010c30b10805904354430d12745c04354430c29545c0624c43081f87d974350030a1686d0d5150030c19655c04310030b118010d5110030c14645c7544c03081e869d9544c030a0c86552524c030a0c86551524c030a1486552514c030a1486951514c030a1486551514c030e0464949514c030e0464549514c030c88645cb634c030e056458d5108720e42635456008720e41635456008720985811c14310f20a888050d6010f20e056458d5114720e42635456014720e41635456014720a618114d6014720a4980196534c720a0f85590434c720a8880590434c720c0f75191314c32088c87591300c320c8474585300c320c19651c14310e20991811c14310e2089887591300c220c9074585300c220991811c14310d20a188550d6010d20c44651c5324c520d05745cc5148520a268498c5148520d41735c0514852089887591300c120c9074585300c120ca2435c46050d20a44815945310d209c1811c14310d2090e851c14310d20985811c14310d20b81811c14310d20c89861c14310d2098a851c14310d20d0a851c14310d20d82811c14310d20989811c14310d20d81811c14310d20981811c14310d209888750e6010d20a888050d6010d209888750d6010d20a898414d6010d20c8b8750d6010d20a888750d6010d20c888750d6010d20a8a8550d6010d20a888550d6010d20a8b8150d6010d20ac1801c56314520d07741cd5114520d04741cd51145209448798d5114520d047498d51145209448758
  | 2 => 0x30010c548cd527cad000f019800000690000000119074ee0005a000002f6f308400270971327b26870280510000c248f545c8906cd20001200916318003784729ed017887b60553f8a38006180045230000ac00214bb000003040017000000000010d000000b4b0000000010b44c6045429bed10028672505b2a4812f80037c643ac77390754447905036000002b06cbdd0200000000002f1200000000084816f239407255050886120e5718a8e060cb167010a81e04e67800d6330b98000d1641c02c12814480009147400158433fc0039c2500000040000010e000238000021800148002cd1b0003b3d8ba1f2873285f89c8032a7d47c9d004f93d00f0f40e000b53b0a331ccd3b4e123cea2982907c063c499338c4228b238c9b399210e0000000049089800781cce9470492a88d294e0000b893865000902c4c22100004d1bae49846062428581b8000d000128a1000a80004d290501bc0036ca4974264303f34e6d38e5e88c3713c8a82aa7000003700017cfe9a08b3e8c305d061be113f031320930590940d1c8f8dd1e91a300002bc7f288031c40027882020d300000091253686b1b0638001a1f800000320007c2f4000644b2fae81d0f8448d74106a00000118a2bf4540540013600000cf0004100000000002fc76450b84206320c3943c2c41cd90003a0d400080000002e000ab14c4232409350b62d0000000000072232d100000110ef0cc000a00000000258003888848840152ae131000bd1e000b700034b4a3c000000002606030080a300580404170284c22000004c020000000000203018000000010040404800060705020220000800060305028000706814000000804040202004020201024220600808020f00800080000014000112800000403008040c0081402000404c020e058000005038040412040242807000000c0001800020fc0d759c86050c43c0d755c86050c43c15759c46050c43c15755c46050c43c86725c46050c43c85725c46050c43e05435496114843e09435496014843c89435c06254443c4a735c06254443c49735c06254443e05435895114443e11435456014443895811d94394043991811c14394043a888050d6294043991811c14354043951811c14354043915811c14354043b09821c14354043b11811c1435404
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x6006400014000003400014124cd8300742111042c0f2c411001a5d18000910810078600042c01500010168a3801880000070000000002a0000000000247ce00010000000181400000001ca06448050d6294043c814130238286a8087901826047050d5010f0130cc10e0aa08698e04619811c15410d31c80c1302382a821a63281912014358043c83022cac08e0a18871062061a811c14310d20c40c33023828621a411819121d43980434825032240286b00869060121d6458d51145209204c2c6a8ac028a41a008458d5158051483080cac04e3a1a6290502255645c0434c520c4032302382879824140a95d917010e3048211330320e098a60906201cd811c1640c120c403a303b22601824108a97a1d644c0304829012eb24c2980609052025e64585300c120a404bac8b0a6018241108985d1530c120842a0128a9ae229a41084422617550c4348210a084aac8b808698a21880861d1314c1204432010a3a26298240886201da84dcd3148110c203b10ab1a629022188076211634c5204429012cba08698a40885402557410d3148110
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 29
  | 6 => 1134
  | 5 => 6283
  | 4 => 3777
  | 3 => 294
  | 2 => 37
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
  | 6 => packedAt gbK6 (36858+((h/520+packedAt gbK6 (30618+(h % 520)*12) 12) % 2267)*12) 12
  | 5 => packedAt gbK5 (274888+((h/2581+packedAt gbK5 (238754+(h % 2581)*14) 14) % 9292)*14) 14
  | 4 => packedAt gbK4 (203780+((h/1439+packedAt gbK4 (185073+(h % 1439)*13) 13) % 5183)*13) 13
  | 3 => packedAt gbK3 (18639+((h/111+packedAt gbK3 (17640+(h % 111)*9) 9) % 443)*10) 10
  | 2 => packedAt gbK2 (2718+((h/13+packedAt gbK2 (2627+(h % 13)*7) 7) % 72)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff83fffc1ffff1c1e38fc7ffe3fff03c09f3f3
  | 1 => 0x7fc3e3fe1f1fffe03f1f8e0fc707ffc764c9f
  | 2 => 0x7ffc03ffe01fe3ffc01ff00ff807fc3878f1c
  | 3 => 0xf800003ffffe003ffffe0000ffff8003f80fe0
  | 4 => 0xffffffc00000003fffffffff00000003fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10880404402002002002412220911088009131
  | 1 => 0xa11108488482a00a0190884444222530324486
  | 2 => 0x5228949148654054e401520aa9054a89858b18
  | 3 => 0x6072a922154064a74aa40010d24e0312d80ec0
  | 4 => 0x84433003998989399349a49c00080c236f6000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeeaeac8feeaeac8feeaeac8feeaeac8feeaeac8feeaeac8feeaeac8feeaeac8feeaeac8feeaeac8feeaeac8feeaeac8feeaeac8feeaeac8feeaeac8feeaeac8, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_37355
namespace PEqualNP.Outside.L_meta_37355
open PEqualNP.Outside.L_meta_37355.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_32 : Interval gbAtlas 2 32 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 37 := (concat bgb_2_0 bgb_2_32)
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
theorem bgb_3_256 : Interval gbAtlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_288 : Interval gbAtlas 3 288 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 294 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 (concat bgb_3_96 bgb_3_128))) (concat (concat bgb_3_160 bgb_3_192) (concat bgb_3_224 (concat bgb_3_256 bgb_3_288))))
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
theorem bgb_4_3744 : Interval gbAtlas 4 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3776 : Interval gbAtlas 4 3776 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3777 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)) (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 bgb_4_416)))) (concat (concat (concat bgb_4_448 (concat bgb_4_480 bgb_4_512)) (concat (concat bgb_4_544 bgb_4_576) (concat bgb_4_608 bgb_4_640))) (concat (concat (concat bgb_4_672 bgb_4_704) (concat bgb_4_736 bgb_4_768)) (concat (concat bgb_4_800 bgb_4_832) (concat bgb_4_864 bgb_4_896))))) (concat (concat (concat (concat bgb_4_928 (concat bgb_4_960 bgb_4_992)) (concat (concat bgb_4_1024 bgb_4_1056) (concat bgb_4_1088 bgb_4_1120))) (concat (concat (concat bgb_4_1152 bgb_4_1184) (concat bgb_4_1216 bgb_4_1248)) (concat (concat bgb_4_1280 bgb_4_1312) (concat bgb_4_1344 bgb_4_1376)))) (concat (concat (concat bgb_4_1408 (concat bgb_4_1440 bgb_4_1472)) (concat (concat bgb_4_1504 bgb_4_1536) (concat bgb_4_1568 bgb_4_1600))) (concat (concat (concat bgb_4_1632 bgb_4_1664) (concat bgb_4_1696 bgb_4_1728)) (concat (concat bgb_4_1760 bgb_4_1792) (concat bgb_4_1824 bgb_4_1856)))))) (concat (concat (concat (concat (concat bgb_4_1888 (concat bgb_4_1920 bgb_4_1952)) (concat (concat bgb_4_1984 bgb_4_2016) (concat bgb_4_2048 bgb_4_2080))) (concat (concat (concat bgb_4_2112 bgb_4_2144) (concat bgb_4_2176 bgb_4_2208)) (concat (concat bgb_4_2240 bgb_4_2272) (concat bgb_4_2304 bgb_4_2336)))) (concat (concat (concat bgb_4_2368 (concat bgb_4_2400 bgb_4_2432)) (concat (concat bgb_4_2464 bgb_4_2496) (concat bgb_4_2528 bgb_4_2560))) (concat (concat (concat bgb_4_2592 bgb_4_2624) (concat bgb_4_2656 bgb_4_2688)) (concat (concat bgb_4_2720 bgb_4_2752) (concat bgb_4_2784 bgb_4_2816))))) (concat (concat (concat (concat bgb_4_2848 (concat bgb_4_2880 bgb_4_2912)) (concat (concat bgb_4_2944 bgb_4_2976) (concat bgb_4_3008 bgb_4_3040))) (concat (concat (concat bgb_4_3072 bgb_4_3104) (concat bgb_4_3136 bgb_4_3168)) (concat (concat bgb_4_3200 bgb_4_3232) (concat bgb_4_3264 bgb_4_3296)))) (concat (concat (concat bgb_4_3328 (concat bgb_4_3360 bgb_4_3392)) (concat (concat bgb_4_3424 bgb_4_3456) (concat bgb_4_3488 bgb_4_3520))) (concat (concat (concat bgb_4_3552 bgb_4_3584) (concat bgb_4_3616 bgb_4_3648)) (concat (concat bgb_4_3680 bgb_4_3712) (concat bgb_4_3744 bgb_4_3776)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefac8feeaeac8feeefac8feeaeac8feeefac8feeaeac8feeefac8feeaeac8feeefac8feeaeac8feeefac8feeaeac8feeefac8feeaeac8feeefac8feeaeac8
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,12,44)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,12,44)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074632 * 2 ^ 32 + 4276808392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37355.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.or,[3,5]⟩,⟨.and,[1,7]⟩,⟨.or,[0,8]⟩,⟨.or,[6,9]⟩,⟨.and,[3,10]⟩,⟨.or,[1,11]⟩,⟨.and,[4,9]⟩,⟨.or,[0,2]⟩,⟨.and,[12,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074632 * 2 ^ 32 + 4276808392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074632 * 2 ^ 32 + 4276808392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37355

open PEqualNP.Outside.L_meta_37355 in
theorem PEqualNP.Outside.L_meta_37355 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074632 * 2 ^ 32 + 4276808392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074632 * 2 ^ 32 + 4276808392) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
