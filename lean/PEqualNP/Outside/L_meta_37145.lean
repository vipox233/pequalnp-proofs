import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_37145.Model
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


end PEqualNP.Outside.L_meta_37145.Model

namespace PEqualNP.Outside.L_meta_37145
open PEqualNP.Outside.L_meta_37145.Model
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

def SBf (j : Nat) : Nat := [6, 6, 5, 5, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_37145

namespace PEqualNP.Outside.L_meta_37145
open PEqualNP.Outside.L_meta_37145.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x4400608030d4090081cf2c314e2802d181bf43de43bd43dd439d43be42bc42de32dc32be41bc41de31dc31bf40bd40df30dd30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x1102031400196300409000a70082047552438e292871c5150e3ea0a1c754c428faa4651d540ca3aa620c7d52318eaa0631d53d023aa9984755130
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0x500006085987548ca0e62d523183189544c2146155130
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 13
  | 2 => 4
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | 2 => packedAt s0K2 (i*38) 38
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (297+((h/5+packedAt s0K4 (272+(h % 5)*5) 5) % 21)*6) 6
  | 3 => packedAt s0K3 (371+((h/4+packedAt s0K3 (351+(h % 4)*5) 5) % 20)*5) 5
  | 2 => packedAt s0K2 (156+((h/1+packedAt s0K2 (152+(h % 1)*4) 4) % 9)*3) 3
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3ffff83fffffffc0fffc1fff83fffffe78f1ff
  | 2 => 0xc0ffffc0fff83fff07ffe0fffc1fe07f9f3e73
  | 3 => 0xff03ffff03ffc1fff83fff07ffe0ff81e7cf9c
  | 4 => 0x3fffffc0001ffffc00007ffff0001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4108888209210402948094901292a282850a5
  | 2 => 0x922911064920608b02952092a4124154932652
  | 3 => 0xa4a22121a44031550265204ca409505458b18
  | 4 => 0xacb3c4a49076b5e69cc318c7739c0619f80de0
  | 5 => 0x30c38738e38739f8e73b9ce063181861fef000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0fcc0fcc0fcc0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_37145
namespace PEqualNP.Outside.L_meta_37145
open PEqualNP.Outside.L_meta_37145.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x53a50a300041306158000002bf43bd43be42bc42be41bc41f721ee21ec21f421e421bf40bd40
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x424e03144408d606000a78784e54343b328c43a641087488210e990821d221043a75408748a810e9d0c21d2a18431d53d034843a06908540
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0xca0000a158c54086a16015021a858343087055308740
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 13
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
  | 4 => packedAt s1K4 (224+((h/4+packedAt s1K4 (208+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s1K3 (367+((h/4+packedAt s1K3 (351+(h % 4)*4) 4) % 16)*5) 5
  | 2 => packedAt s1K2 (155+((h/1+packedAt s1K2 (152+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xfe03fc0fffffffe07fffff01f07ffffe7f81ff
  | 2 => 0x7ffffff01fc07fff83e03fffff83e03f99fe67
  | 3 => 0x7fffffffe0007ffffc003ffffffc003fe1ff87
  | 4 => 0x8003ffffffff81ffffffc001ffffffc1fe0ff8
  | 5 => 0xfffc0000000001fffffffffe00000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x298c462448c106014a64b30302529b22b80ab
  | 2 => 0x242948a1c914a4a5816a1552d483429498b665
  | 3 => 0x4852914483a9494aac1426a569680529615b86
  | 4 => 0x6163220912300d934a5880c18e529601d40d50
  | 5 => 0x7183c38e1c3e71fc739f38f80c631831ffe000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaaf000faaaa000faaaf000faaaa000faaaf000faaaa000faaaf000faaaa000faaaf000faaaa000faaaf000faaaa000faaaf000faaaa000faaaf000faaaa000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_37145
namespace PEqualNP.Outside.L_meta_37145
open PEqualNP.Outside.L_meta_37145.Model
def s2K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (6+((h/1+packedAt s2K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x1ffe07fffff81c1fffff03fe0fffff007e73fc
  | 1 => 0xfffff81f81ffffe0f81ffffff0780fff93fccf
  | 3 => 0xe0ffffe001ffffff001ffc1fff800fffe38f0f
  | 4 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xc22231451041240529272126048a690c26315c
  | 1 => 0x444450c8229208a05a09464a9050a25490d4c5
  | 3 => 0x8aa8a2035525154b0512a9152d014ca9630b0a
  | 4 => 0x14d1049260365a729640c219ca658031d80ea0
  | 5 => 0x18e1c71c79c79f9ce79cf3818c4608c1ffe000
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 59 s2Pos s2Neg, 0xeeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00eeaacc88eeaacc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_37145
namespace PEqualNP.Outside.L_meta_37145
open PEqualNP.Outside.L_meta_37145.Model
def s3K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*5) 5
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (6+((h/1+packedAt s3K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1ffe07fffff81c1fffff03fe0fffff007e73fc
  | 1 => 0xfffff81f81ffffe0f81ffffff0780fff93fccf
  | 2 => 0xe0ffffe001ffffff001ffc1fff800fffe38f0f
  | 4 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xc22231451041240529272126048a690c26315c
  | 1 => 0x444450c8229208a05a09464a9050a25490d4c5
  | 2 => 0x8aa8a2035525154b0512a9152d014ca9630b0a
  | 4 => 0x14d1049260365a729640c219ca658031d80ea0
  | 5 => 0x18e1c71c79c79f9ce79cf3818c4608c1ffe000
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 55 s3Pos s3Neg, 0xeaeac8c8eaeac0c0eaeac8c8eaeac0c0eaeac8c8eaeac0c0eaeac8c8eaeac0c0eaeac8c8eaeac0c0eaeac8c8eaeac0c0eaeac8c8eaeac0c0eaeac8c8eaeac0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_37145
namespace PEqualNP.Outside.L_meta_37145
open PEqualNP.Outside.L_meta_37145.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x8437e52087de6410fb0c821bf28843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e81bf43d037a87a05f94b40bea9681bf42d037a85a05f94740bea8e81be41d037883a05f55240bf29c817d539037c87206f10e40bf294817d529037c85206f10a40bf28c817d519037e83206f50640bf28481bf40903f681205fd4d40be29a81bf435037a86a05fd4940be29281bf425037a84a05fd4540be28a81be415037882a07ed0140df202817e54102fca6205f54c40df21881bc43102fca4205f54840df21081bc42102fca2205f54440dfa0881bd41102fca0206fd0040fd20081bd40103f280206e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730fda0661f840cc2fea9185f95230beaa4617c548c2faa7185f94a30bea94617e518c2faa3185f94230fd20461f9408c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa92617c524c2fea2985f14530fd20261f9404c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf298617e520c2faa4185f94430bea88617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83f681907e10320fd18641f930c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620bea8c417e50883f481107e50220fd98441f830883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20bfa8a417c51483f480907e50120fd98241f830483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53082faa6105f14c20bf290417e51082faa2105f94020fda0041f840083f460107e4c020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fd20621f940c43f661887e0c310fd90621f820c42fea9085f95210df2a4213e54842faa9086f552109eaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fda0421f840843f461087e4c210fd10421f920843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fda0221f840443f460887e4c110fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf288217e50043f480087e50010fd98021f830043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xf4290afca3215f54642bf284857d5090afea6a15f14d42df21a85bc4350bde84a16f90942bfa8a857c5150afea0a17ed4142bda82857c5050bf0a0a15e14142bf2a0857e5310afaa6216fd0c42dea18857e5210b7e84217b90842dea1085ed4210afca2215f54442bf28085fa5010af4a0215f54042fca8085795010afea9995f95332df2a6653e54ccafaa9996f553329eaa6657c54ccafca3995f54732bf28665fa50ccaf4a1995f54332fca86657950ccafea9195f95232df2a4653e548cafaa9196f552329eaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf28465fa508caf4a1195f54232fca846579508cafea8995f95132beaa2657c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cafaa8195f15032bf298657e520cbbe64197b8c832ee99065ed320cb9a64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077a87a0df94b41bea9683bf42d077a85a0df94341fd286837a50d06faa1a0fe54341bca86837d54906fca720df54e41df21c83bc43906fca520df54a41df21483bc42906fca320efd0641fba0c837e50907f4a120de94241bea8483f950906f2a120dfd4d41be29a83bf435077a86a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf298837d531077c8620ef10c41bf290837d521077c8420ef10841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998df94b31bea9663df32cc7ba6598df94331bea86637f548c6fca918df55231be2a4637d538c6fca518df54a31ef19463dc328c6fca318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898dfd4931f7a92636f524c6f8a498fb14931b629263df324c7ba6498fdcc531ef18a637f504c7f6a098ded4131be28263f8504c6f0a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31bf29063ee520c6dca418df54831f6a90636d520c7bc6418f70c831bf28863df310c7ec6218f74c431fa988637e500c7f4a018de94031bea8063f9500c6f2a018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fb8cb21f6996437e50c86faa190dfd5221bf2a4437d54886f8a910dfd4e21bf29c437d53886f8a710df54a21f799443ec32886fca310fbc8621fb90c437e50886faa110dfd5121dfaa2433f54486fca890df55121be2a243bc5448678a890dfd4d21efa9a435f53486fca690df54d21be29a43dc53486b8a690fb8c921f699243f721487dc4290dfd4121fda82437b50486f8a090fe14121bc282437f54086fca810ef950219f2a0437d540877aa810cf55021be2a0437f53086fca610f794c21af298437d53087baa610d754c21be29
  | 2 => 0xb02586e1980009305945c6d8001400ae0000000a026001190411b614c860e1532000b00004ca43cf18000007a13c2330d855000000380001211db0ee735299ab216000000003ee000b80000000004a800000000000003240f00016b358001281941508240008d0001ac2491a0003206e8000daa3c000c9178001140000000000020c0000000022b000774001bb3c471c969c842c7d41821b08425ca19d73500193090724a5e9260003b837cba0000005ed010890000005018723c0093c95130248d1793313e00c4596d4280005d8005180009b087000168e80cd43c074000611fa000d889e3f607c150000005f0d513a3ac140319a11f60004e9e4200888529061360005a8001ce610ce19d0b8a212f0eb01881c0d18e000000000172401d000000228000000001b80014a0000ea3180017700070c00000000568ed18d3de8b00013e0007f4000001f449c000001081445481908c000328000fe398000000006440013b0006600000048e0000012221011c5200023853853a770000007013243410c6d0de3e4708100243b02e08a94144817800235420000000990000005f0001680540da4b49a1bcc300019654800263042000559650005fc0001230a000cc80016c0000400011000000000088001331800001c49580020651c1126c30644c000d6320a18000003bc2bcde823000000a9a7d3884394188336666cb5256000260000294a828c002510000010998238a0005526d47200092000000000000ad0007d83e8070080400c050000100803050010980e00811000070140a03006094120040700c340000800c0200c1d01c0100816030000240500003000020040700802008000200404c0001c010000c04802000010500e02424010090c0000a406004100040e008010000300c1500402014000000000002008040ac030340000c0801c040a40d0780401c000000500c02008010000005c000000606c000001401802004050001201c07000030440801008004280180101805014010000700408004000200000400030000080e00008000000000307c010100000c03098070241e0040002c0b03c0000801000050001e0000800001004290000e0100c000170800000000010000100c07801000120080000c1300c000000900c0006afca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa8287fb5050ef6a0a1df14143fc28287785050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf28087fa5010ef4a021df54043fca8087795010efca7a15f54f42df21e85bc43d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85bf4390b7a87215f94a42dfa1485e
  | 3 => 0x39000918d198b4885c47f03146c1e81a20e4e02dc0f07c4821c03b2734680cc7491d2882c4a78d55247387f98a0c42e417036030828a31bf2b87e92b98f500964891e7230820ae80d4389a06023f1007a8130000000001b8001286f92509c09035c779351e4780aaa272127fd3493d070204591b51667c0a497e4329f0d2025058304bc9ed04e248812034867ad0315e22e9bcb4a493ca0e8e58bf2c667c081a04788445d17843e24d321b0114659390d10f6000001213b2558d90f325446d11a303343dc9c8090d25901f22d09c4c54582f0009800720f4b40009482800000000000000000000000003480000034e0014c0c508a000ac9df3cc948f981117a000b7a183820006a23105a7184b0002ec000770ce2a0000f48000004100016c0004b00000723e3e0ba866000239270000008e06c0004805ccdc8001c66a52e22a51c000cb9bc0fc6bc3c21d0e4800001d125c0ac350f939e5840b00041634c6c8e43180001a94a50a97d020ca1589a949a5d2ce8f8002900000002d9371041541e86707e530250324aa0006391900000053000000815009f1000288b42822cc69400220000134d6a8a4f6848a29574c46787e0b04f44fcb70144522b8979e152a6e0850f14d6388340a136e03d1d8f62b64d13a8001181580e0e83f264cca9a644c180c49d40008dc00217098244882745028948b2581347d0e50002e456143a7f522754a680421a93c480001daa340005411e00106a962fa000fc0000007f000245000000000c30000142f90100000005a6e00033d0aa7e0b052c278f0000000b1128310214001ec3fc000829ee2849c4001380004c061284000a5d2411100099c4303b35c000dd0400a4a243c93c47a74ce62213a46893b1c90c86d12d800000000001481d41cc620f41ca00000a3a0003407a95f0ba3
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0xd40102b86250040ce54940102bb6150040ce945401026e62d53309b58b54cc23e6494b308f59252cc23f64547308f19151cc33b54103309b988548c26d62152308fd91528c23c6454a308f992518c23d6494630ce151408c23e64951309ed81544c23e6515130ce580544c27a6590130ce152404c2786550130ce151404c33854cc1308f596540c33860550308f990540c27a60150309e597400c33954d00309e594400c3395410030ce552300c25f654c0309ed95300c2b8644c030ce551300c25e63d53209758f54c823e64d4f208f59353c823e6494f208f59253c823f64547208f19151c833b5410320ae19130c825e63152209758c548823f6454e208f191538823e6414e208f590538823e64946208f59251883385450220ae590308823e64951209ed81544823e6515120ce580544823e6494d208f59253482796094d208fd91534823c6454d209dd8553482746154d209e996404833854901209e195404833854501209e997304833854cc1209e99430482b9640c120ce150304833854c81208f596540833860550208f990540827a60150208f993530823d64d4c209e983530823e6414c208f59053082766114c209d584530827965d0020ce55340082796510020ce5504008279658c020ce552300827b654c020ae1913008339544c020ce552200826f65480209ed9520082b86448020ce551200833960953108f99353c423d64d4f108f99053c423d6414f109b98853c426d6214f108f99352c423d64d4b108f99052c423d6414b109798c52c425d6314b10ce95240c433a5450310ce95330c42b9640c310ce95030c433a54c8310ae59020c433a5408310ce181548423e64d4e108f593538426e62d4e109b58b538423e6414e108f590538423e64d4a108f593528425e63d4a109758f528423e6414a108f590528433954d0210ce5504084339548c210ae1913084339544c210ce55220842b86448210ce55120842ba64c4210ce5531084279609511097d8d544425c63551109bd89544426c62551108fd91534423c6454d109bd89534426c6254d109ed81534423e6414d108f590534423f64549108f191524425f63549109718d524427b60549108f990524423d64149109e997404427a6510110ce550404427a658c1109e19530442b8644c1109e99620442786548110ae19120442ba64c41109e983540425e63150109758c540426e62150109b588540423f6454c108f191530423e6414c108f590530426e6214c109b588530427a6014c108fd91520423c64548108f990520423d64148109798c520425d63148109e980520423e64944108f592510423e64940108f592500427965900109ed95400433854500109e5973004279650c010ae590300427965c80109e59420042b964080109e59610042b964840109dd95100427b6544010
  | 1 => 0x6b960d04418fd95411067765504419ed8154cc67860553319e98054cc67960153318f99252cc63d6494b319e98252cc6796094b318fd9150cc63c64543319e983548c67960d52319e982548c67960952318fd91528c63c6454a319ed81528c6786054a318f992508c63d64942318f992544c66e62951319b58a544c67a60951319e582544c66f62551319b189544c67b60551319e181544c63e6515131cbd53524c72c54d4931cbd50524c72c541493197997324c74c52cc931d3149324c74c528c531ced53504c73854d4131dad4b504c76852d4131ced50504c7385414131dad48504c76852141319b98b540c66d62d50319e983540c67960d50318f596540c63e64150319b988540c66d62150319e980540c6796015031cb952520c72d5494831cb951520c72d545483197596320c74d528c831d3548320c74d52cc43197d95310c6cc624c431d3549310c677654c431ce952500c7395494031da94a500c7695294031ce951500c7395454031da949500c76952540319ed8154c867860553219e98054c867960153218f99353c863d64d4f219e98353c867960d4f218f99253c863d6494f219e98253c86796094f21d314d32c863f64543218f19150c867a60d52219e583548867a60952219e582548863f6454e218f191538867b6054e219e181538863e6414e218f590538867a6014e219e580538874f530ca218f992508863d64942218f992544865e63951219758e544867a60951219e582544865f63551219718d544867b60551219e181544863e6515121c7d53534871c54d4d218f992534863d6494d219798e534867a6094d219e582534863f6454d218f191534866f6254d219ed8153486786054d2197994534871f5414d21c7150534874d6214d219b996324874c538c9219b195324874c534c921d314e214873b54d4121ce153504875b53d4121d614f504873b5414121ce150504875b5314121d614c504865e63d50219758f540867a60d50219e583540863d65950218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21c7951530871d5454c21d3189530863e6414c218f590530865e6314c219b988530867a6014c219e580530866d65cc821d354f320866d650c821d354c320874d53c84219bd9521086cc6348421d354d21086776548421ce95250087395494021d694e50087595394021ce95150087395454021d694d50087595354021ae18143d02b86050b40ae98241d02b96010e40ae58042902b960d06408f99743502b86050d408f99742502b86050940ae982415023e65105408f59643102b96010c408f59642102b96010840ae583411023f6550440ae592401023f65500409ed9540102bb6550040ced9540102b86350040ce54
  | 2 => 0x4000421400000000011824800033800000140000a00187ccd80c92d00011280039800000145000690000001c67e4000000e20009c01d000000160230005303005c0b42d09c93342c2840008c1ca384b01643644f4c291c402570000001447a4ce9ff18a6bc4b837000718748000000004d04f1a6000499b800002c1a8ca01a27407000000758a8000216658f901714c3d8000443ca448a70000000000012a2b4000768df0724144c82823a000a991304279c00000000000ec800420128001e4428000bf8004400000000025e8308b20a2da1fc7e9a500043ca41ef1ae000e692c3cc034010080100c07004050080000c00014030000100807050040001602804080360040100001010000241a010010100701053004010200000c030180000000018020080000c1300c000500501c00020000040000406010000000803c01024020000100404004000080b04801004000081100410000030080400c03000040180a00005038080200502c010080100405018260040301000020060000000007010080240001c0100000000120000301009004000200004c0401412014000040000c000000b0080300c0101c0e0000000000000090040b0040400401004030000200800030010027b6054b439e18152d0e7a60947439e58251d0e7a6094a439e5825290e7b60546439e1815190f3a43141438fd954310eb86050c4397d954310f3b4354043ce50d5010e7b6054f429e18153d0ab96010f429e98251d0a7960947429e9825390a796094e42ae1814390a7b60546429e1815190a3e6510d42ae5804350b3a4314142ce10c5050b3a42141428fd954310ab86050c428fd954210ab860508429bd954210b3b4354042ce50d5010b3b4254042ce5095010a7a60d53329e58354cca7a60153329e58054ccb3a5494332ce55250ccb3a5454332ce55150cca7a60d52329e583548ca7a60152329e580548cb3a5494232ce552508cb3a5454232ce551508ca7761551329d185544ca7b60551329e181544ca7a60151329e580544ca3e64145328f590514ca7a60145329e580514ca3e64141328f590504ca7b60550329e181540ca7661150329d584540ca7a60150329e580540ca3e6494c328f592530ca3e64948328f592520cacd638c83297d95320ca6f654c832b3d95320cb4f654c832b3185320ca3f64544328f191510cb4d32544329ed81510ca7860544328fd91500ca3c6454032ae18143d06b86050b41ced0d50d07394354341ced0950d07394254341ae58043906b96010a41ae583419073a4394241ce10e509073a4294241ce10a509073b41942419e98053506796014d418f99743506b86050d419e980525067960149418f99742506b86050941ae982415067b6054c419e181531063d6590c41ae580431067b60548419e181521063d6590841ae580421
  | 3 => 0x4b88418d044838130ec1762ac379ab26a15caa000000000ca0003420004186e190048000000000001e0b91243c0dd85e05a0002a83d2cc5600c19a1602d8259463a60d0078000ee000cd8593a00a42016200000061000000000000000006f0af8000000140013a3200410d8003b48107c9c14485cc7d0682764fd058fb084018230bc34c678ab123000000000000006a800000306000000000fa000000ae222000c89a20407783d000000304521e30001940017e0003f8c580002875c000e70000008f1d14221ac8d8001ea5b8711750000010f0191b41d8fb1d235c7c4e297120e56d0c14712225901919264720001bd1a87746b0aa36a344d38af0b00a8e71593be81cb48bf0003c8820853fc000fb8cc0000000017a00030c48192000498000003000000000019e0001287c04e3f00002e00065c0000040452c00079000620f4000000000000003744190e1200c66a05380000036c5f1dc0006083c00000000000033000000000e61b207c88187368874001ed00088c000000006246a8000007880003b000000e01010002946e0871281f8000002420010b8001166f87b87400051000000138654bc1d409000030800000000000002de4d80e1e0332054000950d86100004d0000c4000001145a8770eb21c64c800003960000004322a0080014d102000db8000001c8000000002e1068002ee7e0000000484240010a36671c311fd000000c30001f00008197213c3c40002b31e84c00000000000000000002d40d9d5000000000001d0004fa8000cc000568d216600095845060000320002f80000008800014d1303213e7c0c6007384000471ca0b6710fa00027c000dca222042f4411bf4123900000040c0001c00041e5f41b05224a5c0350b7180000ed9a907437400000000000000c41524883d9fc36c554590ef0147b8a48000008842e9c928211c700cb26047c178000004dc000000000004d95e000000001a30e00003995100000000000000000001c30000009e0162ae7ec518de1d449c7f81a2d6218d01e13d44a10d13107e7ac2b00019a59c7984e4246b0000004000450f8890003184787507c8205d1b133058ca798a1501306c1292684682f8000123d0b601e010604bb08033e2344c14322873c2484118e010ae8540a26385886d25a7600197935a670671fa0002b08ba150265d0bd9650007b10c8691a00000010c40a00000000294584a910d28
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x4a401498000018040c00028400088000278000001c38881a61604b0401c3898eca9a4210e186354d4010314312a4a00814a9cb5410330a52e42a2811843876551300c28d39ea820641465cc5450220872ec2a0609043876551300821c3b2a8900410e5da540c310872ed2a0418843876551308421c3b2a8904210edd954c4210a30e6aa0808852872550404428cb98a8a00214a5c85450010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 666
  | 4 => 551
  | 3 => 20
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (i*5) 5
  | 6 => packedAt s4K6 (i*16) 16
  | 5 => packedAt s4K5 (i*27) 27
  | 4 => packedAt s4K4 (i*38) 38
  | 3 => packedAt s4K3 (i*49) 49
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (6+((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s4K6 (731+((h/13+packedAt s4K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s4K5 (20202+((h/222+packedAt s4K5 (17982+(h % 222)*10) 10) % 880)*11) 11
  | 4 => packedAt s4K4 (22768+((h/183+packedAt s4K4 (20938+(h % 183)*10) 10) % 800)*11) 11
  | 3 => packedAt s4K3 (1016+((h/6+packedAt s4K3 (980+(h % 6)*6) 6) % 34)*6) 6
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf81ffc07ff0fc30fc1f0f87fc7fc0f031277cc
  | 1 => 0xfffffff83ffffff001fffffff83ffffc1ff8ff
  | 2 => 0xffe0ffffc00ffffffe00ff83ffc00fffe38f0f
  | 3 => 0xfffffff003ffffff0003fffff003fc0ff0
  | 5 => 0xffff0000000003fffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x8ac6c4718a92a702f0783c65c664691b1233cc
  | 1 => 0x1040089090040020009148884809224804d055
  | 2 => 0x218a5122062921555200952292808cb1630d0a
  | 3 => 0x8514a24424818a99a52a00432532c022b80ea0
  | 5 => 0xc618c38738ce33ee39cce670062308c3dfe000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfcc8fcc8ecc0ecc0fcc8fcc8ecc0ecc0fcc8fcc8ecc0ecc0fcc8fcc8ecc0ecc0fcc8fcc8ecc0ecc0fcc8fcc8ecc0ecc0fcc8fcc8ecc0ecc0fcc8fcc8ecc0ecc0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_37145
namespace PEqualNP.Outside.L_meta_37145
open PEqualNP.Outside.L_meta_37145.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0xa437d53486f8a690f714d21ae29a43ee32487da6490fdc8521f710a437f50486f8a090dfd5021bf2a043be540867ca810df55021deaa0433d54086f8a810dfd4c21bf29843de53086bca610df54c21eea98435d53086f8a610df94821f799043ec32086fca210fdcc421fa18843ef21087ec4210fb48421fa908437e50087f4a010de94021bea8043f950086f2a010df94f40bea9e817e52d02faa5a05f94740bea8e817d54902fca7205f54e40df21c81bc43902fca5205f54a40df21481bc42902fca3205f54640dfa0c81bd41902fca1206fd0240fda04817f53502f8a6a05fd4940be292817f51502f8a2a07ed0140df202817e54102fca6207794c40af298817d53103baa6205754c40df21881bc43102fca4207b94840b7290817d52103daa4205b54840df21081bc42102fca2207d94440bb288817d51103eaa2205d54440dfa0881bd41102fca0206fd0040fd20081bd40103f280206e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30bf28e617d51cc3f681987e10330bfaa4617e548c2faa9185f15230bea9c617e528c2faa5185f94630bea8c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930bfa8a617c514c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa4185f94430bea88617e500c3f680187e10030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20f721641ed42c82fca3905f54720fda0641f840c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5105f94620bea8c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20f721241ed42482fea2905f14520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea88417e50083f680107e10020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb20e21f541c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fda0421f840843f461087e4c210fd10421f920843ee21087ec4210bfaa2217e54442faa8885f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb20a21f541443f680887e10110fd18221f930443f440887e48110fd88221f610442fea8085f95010beaa0217c54042fea6085f94c10bea98217c53042fea4085f94810bea90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0x41c00803024170040302800000090680001c0503408018430002213001000000a003004060a83a00c1800800030010181b028000000000801024040280c004010340701c3b002fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa8287fb5050ef6a0a1df14143fc28287785050efca821df94c43dfa1887de4310f7a8621f750c43bf290877d5210efca221df54443bf280877d5010efca7a15f54f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42f7a1285be4250afea2a15f14542bfa8285fb5050af6a0a15f14142fc28285785050afca8215f94c42bea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a65f7514caeea2995f14532fa28a6574514cafea0995f14132bfaa0657e540cafaa8195f15032bf298657e520cbbe64197b8c832ee99065ed320cb9a64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077a87a0df94b41bea9683bf42d077a85a0df94341bea86837d54906fca720df54e41bf294837d52906fca320efd0641fba0c837e50907f4a120de94241bea8483f950906f2a120dfd4d41be29a83bf435077a86a0dfd4941be29283bf425077a84a0fdd0541df20a837f50506f8a0a0df95041bf298837d53106fca420df54841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998df94b31bea9663df32cc7ba6598df94331bea86637f548c6fca918df55231be2a4637d538c6fca518df54a31ef19463dc328c6fca318f7cc631fb98c637e508c6faa118dfd5131bf2a2637d544c6f8a898dfd4931f7a92636f524c6f8a498fb14931b629263df324c7ba6498fdcc531ef18a637f504c6f8a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31bf29063ee520c6dca418df54831f6a90636d520c7bc6418f70c831bf28863df310c7ec6218f74c431fa988637e500c7f4a018de94031bea8063f9500c6f2a018dfd5321bf2a6437d54c86f8a990dfd4f21bf29e437d53c86f8a790fb8cb21f699643f731c87e86390df94321bea86437f54886fca910df55221be2a4437f53886fca710df54e21be29c437d52887de6510fb0ca21bf28c43ef21887ee4310df94221bea84437f54486fca890df55121be2a2437f53487bea690d7d4d21bf29
  | 2 => 0x89603280000005d000000db89c3962d4a296a264298ef9752dc41c6514a0ae728119084562a4f91e83403d5010402a20e0c697627c7909205f39a6fcf01120000004d9fd366028cd9c810e3dc768244767accb050244438000552022e4ae1a60d0018ba0e63328c82c81b1a265c5980231e0f8749260ce1e4780d3416064738482c250cdb0e31fc050d11403ba80c058c640c3b0160c742a000ac2262883884b800000894aa80005c000d080034e0011e0001b4880e205a06867c2780000000000000438000c597f48c9151a12d124228000000002ac0014e0648cc5512f000000000f913a0008f0bd000000000001ac10c46000000000391e5236278d58e82f88592087a40044d0394c190414272231ba6a4f122f3a020c8117844e360dc13839c078ce0470c653c089f506a204d9172398764211712961790da113f26c41d9f80ea3790c0b62fa48c090521dc6c0dc87f12643c388ae0924685f16d1ec3e08b0e53b61702b09606c81444a2d35c054401aa2f4218a98e100a7c40b8662124d06188836a040a49b440808904862026574eb8001fe000c091c01e600b4210008238001d82d2000e08001b63081e19e00058cd600021a1f11b98e2067a8c9800484000e320d0f600000099462724001c211e4e80002615e0e51813c33a7f0000001203f5110d23cc7847d0b44525980001f2b64004a0fc1600000000026e000861413a80002c1393ce4ec3483f0dc0044207401202042a1900042c658003c60ccb820a0001944d14d000000000a026a1280000013e000988004801e08a00042e47cc21280000bc6a1543d27b0afa0e1745e4fa0304180a8720c53fc6f4ca8eb150540000b722a419079dc0005b0cd0b807a4606f8000a88683586a3501f8b20d038e50922000374660000f127a304001040824946704c3ac059090003de0000c1bb3e02340001a42800094800000000b59473e6518c600031491c970002548f4039be1581909088b01a7691c9ee3128e8e91173804c0ef19203a8b84c1862ce038fb0cf45864509a382ac5dc750b22900a4f69d33868d85e0fb2148a8d19902c41145d8d900090cc112c000334a91591e47ec5093347e3009b02035a2080e0000008a00006f1880005195e000084231f7074000c28002408791f0004420b4128a20000ac000f40005cc001fa0000dc268a50da01000000000540f0040a0100b0040601001010030a0160380003400034020281c000010080502000000030340c00002020050000f0000100c0006408020000080a0080600c01030000040000803008200cc0400006008000001d00404008011041d0ac00050120040c0000b1200b0000800404000020100900401004010042b104080080101c1601c0a0400004c050041006003038020980500c0d0001707801090000380f0580000c180100000
  | 3 => 0x30c38bf0501f4568c9378568700000ee55cb2800348820000001ae7fd1204425616c7997b3aa1d8e28001b81c000127000920e78a42205f87791d000254361d127e8048886000014c288610000c43980046a5bc0002714e9250e84b0063540000012287c000cc35e000c400034a0000011900060c5
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1530874c6254c21d5185530863e6414c218f590530865e6314c219b988530867a6014c219e580530866d65cc821d354f320866d650c821d354c320875553cc421f1ccb3108675650c421f10c8310874d53c84219bd9521086cc6348421d354d21086776548421b518d210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d50087586054c40c754e43102b96010c40d394e521034d5394840d394d521034d5354840da181521032d5290840ae58042103565394440d554e51103665294440d954a51103726094440d594d51103555354440d994951103655254440c754f411032d52d0440ae583411031d5350440cb54941103365150440ae592401023f65500409ed9540102bb6550040ced9540102b86350040e694d40103995350040ae18940103aa5250040ea54940102bb6150040ec94540103b151500409b98b54cc26d62d5330b618143cc33b5410330b658c40cc39a43103309b988548c26d62152309d984548c27561152308f992518c23d64946308f992544c27b60551308f994544c31d6315130c7152434c25c6550d30ce153304c25e63150309b988540c26d62150309d984540c27561150309e594400c339541003097d95300c27b654c030ae191300c25e63d53209758f54c823e64d4f208f59353c82e86050b20ced5040c82e96210320ea90840c825e63152209758c548827661152209d584548827661d4e209d587538823e64946208f592518823e64951209ed81544823e6515120cb588544823e6494d208f592534823f6454d208f19153482776154d209d185534832c54909209b195424833854c81209798c540825d63150209b988540827661150209d584540823e6414c208f59053082766114c209d58453082796510020ce550400826f65480209ed9520082b86448020cd98654c423e64d4f108f59353c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c423e6414b108f59052c425e6314b109758c52c433654507109798c548425d63152109b988548426d62152109b98b538426d62d4e109798f528425d63d4a10ce55040842d96310210ba58840842b8644c210ae19120842ba64c421097d8d544425c63551109bd89544426c62551108fd91534423c6454d109bd89534426c6254d108fd91524423c645491097d8d524425c6354910bc982414427465505109e99740443395410110b658c40442e96210110bc98440443b141101109e19530442b8644c1109e19520442b86448110ae993104427a60d50109798c540425d63150109b988540426d62150109d984540423e6414c108f590530426e6214c109b588530427a6014c108f990520423d64148109798c520425d63148109e980520423e64944108f592510427965840109dd95100427b6544010
  | 1 => 0xab8000000000000002b600190001f292ae4522160000c34000000167b91205018b8000001a08a0827d800832a45d800000000000000000000001f80000000170a8001bc4d8000000000000000002e0960013aa080095a3600001010040140b0240b038010000200003008080040300c02000010000400c00000000000100000000000040200405004000000800c0000c00000010140200000000020000100c0d00001040040000900402028030340b010000080200800000010440a03c0200c0100004000030000000008010000340000c10014020240000001064010000f00400004010640b02804000000040c0000d00406030060027a60947439e58251d0f3a43141438fd954310eb86050c4397d954310e7a60947429e58251d0b3a42141428fd954210ab860508429bd954210a7a60d53329e58354cca7a60d52329e583548ca7661951329d586544ca7761551329d185544ca7b60551329e181544ca3e64145328f590514ca7a60145329e580514cb366414532cd590514cb673214532d58c8514cb726014532dc580514ca7b60550329e181540ca7661150329d584540ca7a60150329e580540cacd638c83297d95320cad4614c8329bd95320cae4614c832b3d95320cb4f654c832f1d85320cacc614c832f1185320cac4614c832d34c9510ca3f64540328f191500cab86050f41ae18142d073b4194241ae18143506b86050941ae982415063f65504419dd95411067b60553319e18154cc6d4614cb318fd9150cc63c64543319e983548c67960d52319b98a544c66d62951319bd89544c66c62551319ed81544c678605513197997324c74c52cc931d3149324c6d4614c931d914b314c74c528c5319b98b540c66d62d50319e983540c67960d50318f596540c63e64150319b988540c66d62150319e980540c6796015031cb952520c72d5494831cb951520c72d5454831d9185520c65d658c831d354a320c74d520c831d354b310c65f654c431b3189310c74d524c4319dd95310c6e4624c431ce952500c7395494031da94a500c7695294031ce951500c7395454031da949500c76952540319ed8154c86786055321d314d32c86e4614cb21f14cb31c86e5620c721f18c831c863f64543218f19150c867a60d52219e583548863e6414e218f590538867a6014e219e580538874f530ca219798e544865d639512197d8d544865c63551219ed81544867860551219798e534866f6254d219dd85534865e6514d21d3588534866e658c921d314e324866c654c921d314d32486e4614c921d514f214874c53885219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c755
  | 2 => 0x24a14002848e80000000a380000000002860021c0021e02800320a6000002b000000c688174000cc5600000000802980011600000b40004000000222000709700037000b796a00000001260015c0019a1f1d24e2ce002541880030000b89284092c3aae8a59f0b08000127e0003c002a26ba66700e00002a6d1842386c38abc00170559044ca2a4d0787399e000002ea9e000000da68000000194e00000000289196600084758b66700099000271d477278910007990a3c8681086a4a8a054800000f062800000e8002045e14a000000029000000229c200124688008d000a0000368000000000000000389494c9e8000000020000b3000002acb5858518ae5fa626397200020892260000078000ad00000000092f2001408391400000aa2d8581960000000206002eeb00000000079182a20ec088e62c1c67fa025788c0fa8a9f2ec1797c000cea828c25212001b02fa2c0000000000728007e000002da978d4438a4a69a66a0ee508641ea580d05a6b066b984e92046ae0027b000002d43795a2f26e9696e218e46f9a47aabe5a2b2620fa1b9200027436000440009384c260003e1949311a020ca9822e001fa48a7622000619ba312504f0000001e2aa32001aa7d01200000a49644c0329b0c2241b80000000192122a6ae81a181e20002c3f000002c80002e001d8b48006000000118630008f0008f83ab2a0811000349544f8b4bc0f45401c711ccaa876000000000090242000002c8001d2c41400076a108617a8e2dc3f9d009852000000000000000a509e00000ac21a101fc35a70001c843000000009a9de1c91c660001591e4200e7a1063d800bd010001629ca30002c6000000000000000000005b000000000000000000511b6a70000c0000009a000000004a6c800002ea4ba0a1500000000000a2000000000000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xea80a0088899890071a40029210201459e80000000000c0001800001410840000718b22c028a65915d4614c832d0ce830a641968574185320cb61380c299065b05c0614c832c88a630a6590cc5768c831c8722298c299243911886154c21a8aeb9966210e45650c831086263b2a690843c254d5250040e22a6a8a8020721525454010295396a820661469cf5410320a30e6aa08088528725504044348b1a8220221a85894110110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1400c05755d0614c832c41755c0614c832c81745c0614c832
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 586
  | 4 => 379
  | 3 => 22
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
  | 5 => packedAt s5K5 (17772+((h/195+packedAt s5K5 (15822+(h % 195)*10) 10) % 704)*11) 11
  | 4 => packedAt s5K4 (15662+((h/126+packedAt s5K4 (14402+(h % 126)*10) 10) % 605)*10) 10
  | 3 => packedAt s5K3 (1120+((h/7+packedAt s5K3 (1078+(h % 7)*6) 6) % 37)*6) 6
  | 2 => packedAt s5K2 (182+((h/1+packedAt s5K2 (180+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf83ffff01ff1f01f1e3f8ffff8fc0e0033f7cc
  | 1 => 0x7fc0f8ffe1ffffe01fc7f1c07f1ffff8ccc8ff
  | 2 => 0x7fff00fffe01ffffe007fe007fe00fff0f0f0f
  | 3 => 0x800000fffffe01fffff800007ffff007f00ff0
  | 4 => 0xffffff00000001ffffffffff80000007fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x9863011c422220306098247382462301153cc
  | 1 => 0x10920122448080400a4290890909249044c055
  | 2 => 0x23085244886540ad20052412524089630b0d0a
  | 3 => 0x62ca48911406536549000246492c045b00ea0
  | 4 => 0x4430c00e198989d89926493800030186eea000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xfeeaecc0feeaecc0feeaecc0feeaecc0feeaecc0feeaecc0feeaecc0feeaecc0feeaecc0feeaecc0feeaecc0feeaecc0feeaecc0feeaecc0feeaecc0feeaecc0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_37145
namespace PEqualNP.Outside.L_meta_37145
open PEqualNP.Outside.L_meta_37145.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x111500028d763169d5401b0000ccd1e00817b91285b801e0400a586402600183ae6a219343689480487c5ba0601c302a0022b289493c6240b964660e002639e804e181810110040002a004801008700263c18000ffd50037f5400ff95003fd5400df55003fc54017fd4c05fe53017f54c05fc5300ffd0c03fe4300ff50c03fc43017fd4805fe52017f54805fc5200ffd0803fe4200ff50803fc42007fcc801fe32007f4c801fc32017fd4405fe51017f54405fc5100ffd0403fe4100ff50403fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21017fd4005fe50017f54005fc5000ffd0003fe4000ff50003fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x842004ff94210027faa108013fc5084009ffa042004ff90210027fa8108013fc4084009ff9842004ff8c210027f46108013fd3084001fc9842004ff0c210027fe4108013fe2084009fd1042004ff48210007f24108013fc2084009ff8842004fdc421001ff62108023ff65440117fb2a2008ff99510015fcca88023fd65440117eb2a2008ff19510015f8ca8801fff644400f7fb222007ff9911000dfcc88801ffd644400f7eb222007ff1911000df8c88801fff544400fbfaa22007ff9511003ffaa88801f7d544400ffe2a22000ffd8d10005fec688003fe63440017f31a2000ff58d10005fac688003fc63440017e31a2008ffd4d10047fca688023fd5344011fe29a2007ffd0d1003ffc868801ffd434400ffe21a2000ffd8910005fec488003fe62440017f3122000ff58910005fac488003fc62440017e3122008ffd4910047fca488023fd5244011fe2922007ffd091003ffc848801ffd424400ffe2122000ffcc910007fc6488003fd3244001fe1922008ffd451001ffca288023fd5144007fe28a2007ffd051001ffc828801ff6414400ffea0a2007fd5051001ff88288003ff3144007ff18a2000ff4c51001ff86288003ff2144007ff10a2000ff4851001ff84288023ff5044009ff2822008ff54110027f8a08801fff4044009ff2022007ff50110027f88088003ff3044009ff1822000fe8c110007fa6088003f93044009fe1822000ffc8110027fc4088003fa2044001fe9022000fe48110027f8408800fff1044007fd8822004ff84110027ec2088013ff65040097fb282004ff99410015fcca08013fd650400d7eb282004ff19410025f8ca08013ff64040097fb202004ff9901000dfcc808013fd640400b7eb202004ff19010025f8c808017ff540400bbfaa02005ff9501002ffaa8080177d540400bfe2a02004ffd8c10025fec608013fe63040017f3182004ff58c10005fac608013fc63040097e3182006ffd4c10037fca60801bfd530400dfe2982005ffd0c1002ffc8608017fd430400bfe2182004ffd8810025fec408013fe62040017f3102004ff58810005fac408013fc62040097e3102006ffd4810037fca40801bfd520400dfe2902005ffd081002ffc8408017fd420400bfe2102000ffcc810007fc6408003fd3204001fe1902003bf9841001ffea20800ffe5104007fea882003ff1441001ffe820800ffe4104007fea082003ff1041001ffe620800ffe3104007fe9882003ff0c41001ffe420800ffe2104007fe9082003ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff4004009ff2002004ff50010027f88008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802003fe44010
  | 1 => 0x3fe61080077f3084004ff58420005fac210013fc610801fffa88400fff9442007ffaa21003ffc510801dffa08400eff90420077fa821003bfc4108001ff9884000ff8c420007fa6210003fc310801bff9084000ff88420007fa4210037fc21080097f3004004ffd4020027fca010013fd5008009fe2804004ffd0020027fc8010013fd4008009fe2004004ffcc020027fc6010013fd3008009fe1804004ffc8020027de4010013fe2008009fd1004004ff48020027da4010003f92008007ffb2e2003bfd971001ffccb8800afe65c4007bf32e20029f9971001ffacb88032fd65c4007beb2e20009f5971001ff8cb8800efc65c4007ffb262003bfd931001ffcc988006fe64c4007df3262001af9931001ffac98802efd64c4007deb262000af5931001ff8c98800efc64c4017ffaa6200bdfd531005ffca98802ffd54c4017beaa6200bff1531001ffec78800eff63c4007ff31e2000bf98f1001ffac788002fd63c4007fe31e2003bf18f10067fea788033fe53c4019fea9e200cff14f1005ffe878802ffe43c4017fea1e200bff10f1001ffec58800eff62c4007ff3162000bf98b1001ffac588002fd62c4007fe3162003bf18b10067fea588033fe52c4019fea96200cff14b1005ffe858802ffe42c4017fea16200bff10b10007fe6588003fe32c4001fe9962000ff0cb1001ffea38800ffe51c4007fea8e2003ff1471001ffe838800ffe41c4007fb20e2003ff5071005fea838800ffc41c4007ff98e2003ff8c71001ffa638800ffc31c4007ff90e2003ff8871001ffa438800ffc21c4019ffa862004ff94310067faa188013fc50c4017ffa062004ff9031005ffa8188013fc40c4001ff9862004ff8c310007fa6188013fc30c4001ff9062004ff88310007fa4188013fc20c4009ffb2c2004bfd9610027fccb0800afe6584009bf32c20029f99610027facb0802afd6584009beb2c20009f59610027f8cb08012fc6584009ffb242004bfd9210027fcc908006fe6484009feb242009bf59210027f8c908012fc6484013ffaa42009dfd521004ffca908027fd5484013beaa42009ff15210027fec708012ff6384009ff31c2000bf98e10027fac708002fd6384009fe31c2004bf18e10057fea70802bfe5384015fea9c200aff14e1004ffe8708027fe4384013fea1c2009ff10e10027fec508012ff6284009ff3142000bf98a10027fac508002fd6284009fe3142004bf18a10057fea50802bfe5284015fea94200aff14a1004ffe8508027fe4284013fea142009ff10a10007fe6508003fe3284001fe9942000ff0ca1003dfac30802bff5184007ff28c200aff5461001ff8a308027ff4184007ff20c2009ff5061001ff88308003ff3184007ff18c2000ff4c61001ff86308003ff2184007ff10c2000ff4861001ff84308012fe6084009ffa
  | 2 => 0x20027fec710012ff6388009ff31c4000bf98e20027fac710002fd6388009fe31c4004bf18e200a7fea710053fe5388029fea9c4014ff14e2009ffe871004ffe4388027fea1c4013ff10e2008dfac510053ff5288029ff2944014ff54a200a7f8a51004fff4288027ff2144013ff50a2009ff88510003ff3288001ff1944000ff4ca20007f86510013ff6188009ff30c4003bf98620027fac310002fd6188009fe30c4014ffd46200a7fca310053fd5188029fe28c4013ffd062009ffc831004ffd4188027fe20c4000ffcc620007fc6310003fd3188001fe18c4000ffc8620007fc4310003fd2188001fe10c4004bf98220027fea110013fe5088009fea844004ff14220027fe8110013fe4088009fea044004ff10220027fe6110013fe3088009fe9844004ff0c220027fe4110013ef2088001fd9044012ffd9520095feca900037f65480013fb2a4012ff99520015fcca9004bfd65480257eb2a4012ff19520015f8ca9004b7c65480053e32a4011ffd912008dfec890003bf64480015fb224011ff9912000dfcc890047fd64480237eb224011ff1912000df8c890047bc64480035e3224011ffd512008efea890047fe5448023feaa24011df5512008ff8a890003ff63480017fb1a4000ff98d20005fcc690003fd63480017eb1a4000ff18d20005f8c69004bff5348025ff29a4012ff54d20097f8a690047ff4348023ff21a4011ff50d2008ff8869004bff5248025ff2924012ff54920097f8a490047ff4248023ff2124011fb9092008ffa8490047ed4248023fe2124000ffcc920007fc6490003fd3248001fe1924000ffd8520005fec290003fe6148001feb0a4000ff1852001df8c29004bff5148025ff28a4012ff54520097f8a290047ff4148023ff20a4011ff5052008ff88290003ff3148001ff18a4000ff4c520007f86290003ff2148001ff10a4000ff48520007f8429004bff5048009ff2824012ff54120027f8a090047ff4048009ff2024011ff50120027f88090003ff3048009ff1824000ff4c120027f86090003ff2048001fd9024004ff88120027dc4090013ff65080097fb284004ff99420015fcca100137e65080053f3284004ff5942007dfaca100137d65080013eb284004ff19420025f8ca10013ff64080097fb204004ff9902000dfcc810013fd640801d7eb204004ff19020025f8c81003bff540801dbfaa0400eff95020077faa81003b7d540801dfe2a04004ffd8c20025fec610013fe63080017f3184004ff58c20005fac610013fc63080097e318400fffd4c2007ffca61003ffd530801ffe298400effd0c20077fc861003bfd430801dfe2184010bf9882007ffea410037fe520801ffea90400dff14820077fe8410037fe420801dfea10400dff10820007fe6410037fe3208001fe990400dff0c820027fec21001
  | 3 => 0xf20a601aff505300d7f88298003ff314c001ff18a6000ff4c530007f86298003ff214c001ff10a6000ff48530007f8429806fff504c009ff282601bff54130027f8a09806bff404c009ff202601aff50130027f88098003ff304c001fd9826004ff8c130027bc6098013ff650c0097fb286004ff99430015fcca180137e650c0053f3286004ff594300c5faca180137d650c0013eb286004ff19430025f8ca18013ff640c0097fb206004ff9903000dfcc818013fd640c02f7eb206004ff19030025f8c81805fff540c02fbfaa06017ff950300bffaa81805f7d540c02ffe2a06019bf98c300c7fea61805bfe530c031fea986016ff14c300bffe861805bfe430c02ffea186016ff10c30027fec418013fe620c0017f3106004ff58830005fac418013fc620c031ffa906018ff948300c7faa418063fc520c02fffa106017ff908300bffa841805ffc420c02dff9906000ff8c830007fa641805bfc320c009ffb086004ff9843001dfcc218013fd610c0017eb086004ff184300c7fea218063fe510c031fea886018ff144300bffe821805ffe410c02ffea086017ff104300b7fe6218003fe310c001fe9886016ff0c430007fe4218003fe210c001fe9086000ff08430025fcc018013ff500c009ff2806004ff54030027f8a018013ff400c009ff2006004ff50030027f88018013ff300c009ef9806004ff8c030027f46018013fd300c009ee9806000fe4c03006ffecb90056ff65c802bff32e4002bf997200affacb90056fd65c801bfe32e4002bf1972006ffec990042ff64c8021ff3264001bf99320087fac990042fd64c801bfe3264001bf19320087fea9900437f54c8021ff2a64010ff55320086faa990043fc54c801bffb1e4000bfd8f20007fcc790002fe63c8001feb1e4000bf58f2006ff8c790002fc63c802bffa9e4015ff94f200affaa790057fc53c8021ffa1e4010ff90f20087fa8790043fc43c802bffa96400dff94b200affaa590037fc52c8021ffa16400dff90b20087dc8590043fd42c8021f6a16400dff10b20007fe6590037fe32c8001fe996400dff0cb2006ffec390003fe61c80077f30e4000ff58720005fac390037fc61c802bffa8e4015ff947200affaa390057fc51c8021ffa0e4010ff90720087fa8390043fc41c8001ff98e4000ff8c720007fa6390003fc31c801bff90e4000ff88720007fa4390037fc21c802bffa864004ff943200affaa190013fc50c8021ffa064004ff90320087fa8190013fc40c8001ff9864004ff8c320007fa6190013fc30c8009ffb2c4004bfd9620027fccb1000afe6588009feb2c4014bf59620027f8cb10012fc6588009ffb244004bfd9220027fcc910006fe6488009feb244013bf59220027f8c910012fc6488027ffaa44013dfd522009ffca91004ffd5488027beaa44013ff152
  | 4 => 0x6fe64cc033feb266019bf593300b7f8c998006fc64cc033ffaa66019dfd53300cffca998067fd54cc033beaa66019ff153300f7fea79805bfe53cc03dfea9e6016ff14f300cffe879805bfe43cc033ef21e6019ff50f300cfba879805bfc43cc02dffb166000ff98b30005fcc598003fd62cc0017eb166016ff18b300f7fea59807bfe52cc03dfea96601eff14b300cffe8598067fe42cc033fea166019ff10b300b7fe6598003fe32cc001fe9966016ff0cb300b7fec398003fe61cc0077f30e6000ff58730005fac39805bfc61cc03dffa8e601eff947300f7faa39807bfc51cc033ffa0e6019ff907300cffa8398067fc41cc02dff98e6000ff8c730007fa639805bfc31cc001ff90e6000ff88730007fa4398003fc21cc03dffa866004ff943300f7faa198013fc50cc033ffa066004ff903300cffa8198013fc40cc009ffb2c6004bfd9630027fccb1800afe658c009feb2c601dbf59630027f8cb18012fc658c009ffb246004bfd9230027fcc918006fe648c009feb24601cbf59230027f8c918012fc648c039ffaa4601cdfd52300e7fca918073fd548c039beaa4601cff152300d5fac718077ff538c03bff29c601dff54e300eff8a718073ff438c039ff21c601cff50e300e7f88718013ff628c009ff3146000bf98a30027fac518002fd628c009fe314601dffd4a300effca518077fd528c03bfe294601cffd0a300e7fc8518073fd428c039fe2146000ffcca30007fc6518003fd328c001fe1946004ffd8630027fcc31800efe618c009feb0c6000bf58630027f8c318077ff518c03bff28c601dff546300eff8a318073ff418c039ff20c601cff506300e7f88318003ff318c001ff18c6000ff4c630007f86318003ff218c001ff10c6000ff48630007f84318012fe608c009ffa846004ff94230027faa118013fc508c009ffa046004ff90230027fa8118013fc408c009ff9846004f7cc230007f6611806fff654c0377fb2a6000dfd9530004feca9806ffe654c0057f32a601bff595300ddfaca9806ffc654c0057e32a601bdf19530014f8ca9806bff644c0357fb226000efd91300057ec89806bfe644c0037f322601aff591300d5fac89806bfc644c0037e322601aef1913000d78c89806bff544c035bfaa2601aff951300d7faa89806b7d544c035fe2a2601bffd4d300dffca69806ffd534c037fe29a601affd0d300d7fc869806bde434c035fea1a601af750d300d7f88698003ff624c0017fb126000ff98930007fac498003fc624c0017e312601bffd49300dffca49806ffd524c037fe292601affd09300d7fc849806bfd424c035fe2126000ffcc930007fc6498003fd324c001fe1926000ffd8530005fec298003fe614c001feb0a6000ff1853001df8c29806fff514c037ff28a601bff545300dff8a29806bff414c035f
  | 5 => 0xc62101ffe431080fef2188401fb90c4203ffd822101ffcc110812fe6088407feb044200bf5822101ff8c110897ff508844bff2844225ff5422112ff8a110893ff4088449ff2044224ff50221127f8811088fff65484477fb2a4200dfd9521004feca9088ffe65484057f32a4223ff5952111dfaca9088ffc65484057e32a4223df19521014f8ca9088bff64484457fb224222ff9912100dfcc89088bfd64484457eb224222ff1912100df8c89088bff5448445bfaa24222ff95121117faa89088b7d5448445fe2a24200ffd8d21005fec690803df63484016fb1a4200ff98d21005fcc690803fd63484017eb1a4200ff18d21005f8c690803dc63484016e31a4223ffd4d2111ffca69088ffd5348447fe29a4222ffd0d21117fc869088bfd4348445fe21a4223ffd492111ffca49088ffd5248447fe2924222ffd0921117fc849088bfd4248445fe2124200ffcc921007fc6490803ee3248401fe9924200fb4c921007f8649088fff5148407ff28a4223ff5452101ff8a29088bff4148407ff20a4222ff5052101ff88290803ff3148407ff18a4200ff4c52101ff86290803ff2148401fb90a4203ff8852101fdc4290803ff60484017fb024200ff98121007fac090803fc60484097e3024223ffd412111ffca09088ffd5048447fe2824222ffd0121117fc809088bfd4048445fe2024203ffd942101dfeca1080ffe65084057f3284203df99421014fcca1080ffd65084417eb284203df59421004faca1080ffc65084077e3284203ffd902101dfec81080ffe64084037f3204203ef9902100d7cc81080ffd640843f7eb204203ef590210057ac81080ffc64084077e320421fffd50210fefea81087ffe540843ffeaa0421fdf550210fff8a81080fff63084077fb184203ff98c21005fcc61080fde63084016f3184203ff58c21005fac61080fdd63084016eb184203ff18c2101df8c610883ff5308441ff2984220ff54c21107f8a61087fff430843fff218421fff50c210fff88610886fe6208441ffa90420dff94821107faa410837fc520843fffa10420dff908210fffa8410837fc4208401ff9904200fbcc82106ffc6410803fd320841bfe1904200fb0c82101dfcc21080fff5108407ff2884203ff5442101ff8a21080fff4108407ff2084203ff5042101ff8821080fff3108407ff1884203ff4c42101ff8621080fff2108407f79084203ff8842101fec421080ffd2108407f69084200fd4842101ffec01080ffe60084097f3004203fe98021005f4c01080ffd60084017eb004203fe58021005f2c01080ffc6008441ffa804220ff94021107faa010883fc500843fffa00421fff900210fffa801087ffc400842dffb2e601ebfd97300f7fccb9800afe65cc03dfeb2e601ebf597300b7f8cb9800afc65cc02dffb266019bfd93300cffcc998
  | 6 => 0xf7eb206203ef590310057ac81880ffc640c4077e3206227ffd503113efea81889ffe540c44ffeaa06227df5503113ff8a8188a6fe630c451ffa986216ff94c31147faa61885bfc530c44fffa186216ff90c3113ffa861885bfc430c407ffb106203ff98831005fcc41880fee620c401773106203ff58831005fac41880fed620c40176b106203ff18831147fea4188a3fe520c451fea906228ff1483113ffe841889ffe420c44ffea106227ff108310b7fe6418803fe320c401ef1906200ff4c8310b7f86418803dc320c4077f3086203ffd443101ffca21880ffd510c407fe2886203ffd043101ffc821880ffd410c407fe2086203ffcc43101fbe621880ffe310c407fb1886203ff4c43101fba6218803f5310c407ffb006203ff98031025fcc01880ffa600c4017d3006203ff58031005fac01880ff9600c4017cb006203ff18031147fea0188a3fe500c451fea806228ff1403113ffe801889ffe400c44ffea006227ff1003106ffecb9089aff65c844dff32e4202bf99721137facb9089afd65c841bfe32e4202bf1972106ffec990886ff64c8443ff3264201bf9932110ffac990886fd64c841bfe3264201bf1932110ffea9908877f54c8443ff2a64221ff5532110efaa990887fc54c841bffb1e4200bfd8f21007fcc790802fe63c8401feb1e4200bf58f2106ff8c790802fc63c844dffa9e4226ff94f21137faa79089bfc53c8443ffa1e4221ff90f2110ffa8790887fc43c844dffa96420dff94b21137faa590837fc52c8443ffa16420dff90b2110ffa8590837fc42c8401ff996420dff8cb21007dc6590803fd32c8401f6996420dff0cb21137fea39080ffe51c844dfea8e4203ff1472110ffe839080ffe41c8443fea0e4203ff10721007fe639080ffe31c8401fe98e4203ff0c72106ffec190803fe60c84097f3064200ff58321005fac190837fc60c844dffa864226ff94321137faa19089bfc50c8443ffa064221ff9032110ffa8190887fc40c8407ffb2c4203bfd962101ffccb1080afe6588407feb2c4225bf5962101ff8cb1080efc6588407ffb244203bfd922101ffcc910806fe6488407feb244224bf5922101ff8c91080efc6488449ffaa44224dfd5221127fca910893fd5488449beaa44224ff1522101ffec71080eff6388407ff31c4200bf98e2101ffac710802fd6388407fe31c4203bf18e2112ffea710897fe538844bfea9c4225ff14e21127fe8710893fe4388449fea1c4224ff10e21115fac510897ff528844bff2944225ff54a2112ff8a510893ff4288449ff2144224ff50a21127f88510803ff3288401f79944200ff8ca21007fa6510803fc3288401f61944203bf9862101ffea31080ffe5188407fea8c4203ff1462101ffe831080ffe4188407fea0c4203ff1062101ffe631080ffe3188407fe98c4203ff0
  | 7 => 0x98803fe62cc4017f3166200ff58b31005fac59885bfc62cc45dffa96622eff94b31177faa5988bbfc52cc453ffa166229ff90b3114ffa85988a7fc42cc42dff9966200f7ccb31007fc6598803fd32cc401ee9966216ff0cb31177fea39880ffe51cc45dfea8e6203ff1473114ffe839880ffe41cc453fea0e6203ff107310b7fec198803fe60cc4097f3066200ff58331005fac19885bfc60cc45dffa86622eff94331177faa1988bbfc50cc453ffa066229ff9033114ffa81988a7fc40cc407ffb2c6203bfd963101ffccb1880afe658c407feb2c622dbf5963101ff8cb1880efc658c407ffb246203bfd923101ffcc918806fe648c407feb24622cbf5923101ff8c91880efc648c459ffaa4622cdfd5231167fca9188b3fd548c459beaa4622cff15231155fac7188b7ff538c45bff29c622dff54e3116ff8a7188b3ff438c459ff21c622cff50e31167f8871880fff628c407ff3146200bf98a3101ffac518802fd628c407fe314622dffd4a3116ffca5188b7fd528c45bfe294622cffd0a31167fc85188b3fd428c459fe2146200ffcca31007fc6518803de328c401fe9946200ff0ca31007b8651880efe618c407ffa8c6203ff9463101ffaa31880ffc518c407ffa0c6203ff9063101ffa831880ffc418c407ff98c6203f7cc631007ee631880fff608c407ff3046204bf9823101ffac118802fd608c407fe304622dffd423116ffca1188b7fd508c45bfe284622cffd0231167fc81188b3fd408c459fe204622bffd953115dfeca988037f654c4013fb2a622bff99531015fcca988affd654c4577eb2a622bff19531015f8ca988af7c654c4053e32a622affd9131155fec8988abfe644c4037f322622aff59131155fac8988abfc644c4037e322622affd5131156fea8988abfe544c455feaa2622adf55131157f8a8988afff534c457ff29a622bff54d3115ff8a6988abff434c455ff21a622aff50d31157f88698803ff624c4017fb126200fbd8931005dec498803fe624c401feb126200ff18931005f8c498803ec624c40176312622bffd493115ffca4988affd524c457fe292622affd0931157fc84988abfd424c455fe2126200ffcc931007be6498803fe324c401fe9926200f74c931007f864988afff514c407ff28a622bff5453101ff8a2988abff414c407ff20a622aff5053101ff88298803ff314c401fb98a6203ff8c53101fbc6298803ff604c4017fb026200ff98131007fac098803fc604c4097e302622bffd413115ffca0988affd504c457fe282622affd0131157fc80988abfd404c455fe2026203ffd943101dfeca1880ffe650c4057f3286203df99431014fcca1880ffd650c4517eb286203df59431004faca1880ffc650c4077e3286203ffd903101dfec81880ffe640c4037f3206203ef9903100d7cc81880ffd640c44
  | 8 => 0xf14e3218ffe87190c7fe438c863fea1c6431ff10e3217dfcc5190d7ff528c81bff2946435ff54a3206ff8a5190c7ff428c81bff2146431ff50a3206ff88519003ff328c801ef9946400fbcca3206ffec319003fe618c8077f30c6400ff58632005fac319037fc618c86bffa8c6435ff946321affaa3190d7fc518c863ffa0c6431ff9063218ffa83190c7fc418c81bffb046400ff98232025fcc119003fd608c8017eb04640dff182321affea1190d7fe508c86bfea846435ff1423218ffe81190c7fe408c863fea046431ff102321a7feca990d2ff654c869ff32a6402bf995321a7faca990d2fd654c869fe32a6402bf1953219ffec8990ceff644c867ff3226401bf9913219ffac8990cefd644c867fe3226401bf1913219ffea8990cf7f544c867ff2a26433ff5513219efaa8990cffc544c869ffa9a6434ff94d321a7faa6990d3fc534c867ffa1a6433ff90d3219ffa86990cffc434c869ffa926434ff949321a7faa4990d3fc524c867ffa126433ff9093219ffa84990cffc424c801ff9926400fbcc932007fc6499003de324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6403bf185321a7fea2990d3fe514c869fea8a6434ff1453219ffe82990cffe414c867fea0a6433ff10532007fec099002ff604c801ff3026400ff58132007f8c099012fc604c869ffa826434ff941321a7faa0990d3fc504c867ffa026433ff9013219ffa80990cffc404c81bffb286430bfd9432187fcca1900afe650c861feb286430bf5943206ff8ca1900afc650c81bffb20642fbfd903217ffcc819006fe640c85ffeb20642fbf5903206ff8c819006fc640c85fffaa0642fdfd503217ffca8190bffd540c85fbeaa0642fff15032195fcc6190c3ff530c82dff2986430ff54c320b7f8a6190bfff430c82dff218642fff50c320b7f886190c6fe620c861ffa90640dff94832187faa419037fc520c85fffa10640dff9083217ffa8419037fc420c82dff9906400f7cc83206ffc6419003ee320c801fe9906400f74c832007da6419003cd320c81bffb086400ff9843201dfcc219003fd610c8017eb08640dff18432187fea2190c3fe510c861fea886430ff1443217ffe82190bffe410c85ffea08642fff1043206ffec019003fe600c8097f3006400ff58032005fac019037fc600c861ffa806430ff94032187faa0190c3fc500c85fffa00642fff9003217ffa80190bffc400c82dffb2e622ebfd9731177fccb9880afe65cc45dfeb2e622ebf597310b7f8cb9880afc65cc42dffb266229bfd933114ffcc998806fe64cc453feb266229bf593310b7f8c998806fc64cc453ffaa66229dfd533114ffca9988a7fd54cc453beaa66229ff15331177fea79885bfe53cc45dfea9e6216ff14f3114ffe879885bfe43cc453fea1e6216ff10f310b7fec5
  | 9 => 0x201800601600200000a00400400200800000400601a00400400200200000000a01200000000400400800600200000800200000800000000200200401200600e00c00200000200000200000a00c01200001000000000000c04c00601400e00600600801000600000600201200000200c00c00601e00200200200800800c00000000000a00400000000400001201200200000200e00201a00001c00800400201e00600e00c00000600600000800400c00000003200600200a00a00800000400000001000400a00601e00400000000e00800800800002a01400400002803800000200200200602e00001a00400400000001200200003600000200001600a00400402e02000600400202600201000800a00000000000200e01201200401200600e00000c00400202800000200800800000000c00000c00a00000001a01200a00600000a00000200800600c00000c01000600000200000000001400000400800801800000a00000e04600201e00000400000600200000001800200200000000000600200400000000200200000000200200200600600c01400c00000c01a00600400803600200400800000200000000000001400c01600c00a00200200600000400000000000004a01000200000600000000400200c00a00200001000000200200800200200600800000400000200200200600400800000c00a00000600000400200800000a00200200000c01600000001401401a02a00401c00000000800002000200800e00000600000400e00001600001a16ffd97321b5fecb990dbfe65cc8057f32e6436df99732014fccb990dbfd65cc86d7eb2e6400df59732004facb9905bfc65cc8057e32e6416ffd9332195fec9990cbfe64cc8037f3266432ff59332195fac99905bfc64cc8037e3266432ffd5332196fea9990cbfe54cc865feaa66432df55332197f8a9990dbff53cc82dff29e6436ff54f320b7f8a7990cbff43cc82dff21e6432ff50f320b7f887990dbff52cc86dff2966436ff54b321b7f8a5990cbff42cc865ff2166432ff50b32197f8859905bff61cc801ff30e6403bf98732007fac399002fd61cc82dfe30e6436ffd47321b7fca3990dbfd51cc86dfe28e6432ffd0732197fc83990cbfd41cc865fe20e6416ffd8332007fcc199012fe60cc801feb066400bf583320b7f8c1990dbff50cc86dff2866436ff543321b7f8a1990cbff40cc865ff2066432ff50332197f88199037ff658c86b7fb2c6435ff99632015fccb190d77e658c8053f32c6435ff596321adfacb190037d658c8013eb2c640dff19632015f8cb19037ff648c8637fb246431ff9923200dfcc9190c7fd648c8637eb24640dff1923200df8c9190c7ff548c863bfaa46431ff9523218ffaa9190c77d548c863fe2a46433bf58e321affea7190d7fe538c86bfea9c6435f
  | 10 => 0x8279000011000000020a000000000025e1baceb60001c89cc8baa6422cd93200000000000b5452c0000001a9c4b200000000001a40000188508466804258800032a1d21018c9400070f0000000000000000000002820c0000000f047b011d029826e56e2d50e6cdce00000007d4ce419b3af95e00000000000000e765f23720bd400043c25180000007cf3a78000c5870033491a80004da1f613089e606f000075000004114b9aa000000024e00008164810000f4cf4831200020a02ce6dc00000000002fa0e800005244320001b840004a90ff9b4800078300005002626b400019242c624a37e0dc476e0000a680000001b70e20000fc200000000000000000001afce7821f00000000003c1288000000000018e0e08afe000000000000000002110940000000d1000000000000016500000000000000000000381800086005d1c08000a18000000000052600000000000001653da17b8000000000085001805338b873400000000000009ae0002630000ec20000000000ba612a17b000079c0001c81d540003f10000000b1617400018a02783760c980000000000000d446ca0000001f38bd65db260000000024b2c90d7cfdc568000000000058f0000000000000379800000000000013e40007b200000000000000e710f86944f428182f4c6600016e1064e6c00025400000000000000aec0000002a48000fea4d40000000fe079c37111d47586b52530b640004e01d200000000002fb14f000000600000000001800400800000200000200000000600200801000003000000601200400001000000000000a00200c00200000001800000000800200400001200a00000200000001800802202400001800400400000000001000000400400800201400200000000000000600000000200600200800000001800c00000000000802c00000201600000e00601a00000200000000200201200a00000000a00000000000003800c02c00400000a00c00a01a00801000a00001600000203a00200400000000600400600001400800000001601a04a00401c00600200200400002c01a03200000400000800201800000400000000600400000001600200200000200200000800a00400401400000000000001200800000000800800000800e01c00200000200000200000000200a00000000402401400000600800000801a01600200800201200a00000400a00600800000800000200201000400001201000a00600600400000600c01000200400001a00400000200400801600a00800000200c00800000802600200200802200600e00200000000600400000400200001401400000000200400800200000400600201001c00000200200800201c00001a00600601200400201201000001602000600400200800400400000400001200c01000002800000200000
  | 11 => 0xd6602800016087b04ba000000018a0cb12017040c64843bf003838400009b1ef00007ec28708c860c1f92311748b1c6ed0000000be200032b80000000000000000000000000000048a0000001e3484200039b80000003bc1ca02b501e58c00010409163b30001bd000000001e9b20bfa06819c8aa80360003ed863c36a22e3ca8e882600c9000000057c10000000000005140000f540004ff0bd94c02402b32ef000038000032c0000000000336011864c0000b5088ca4058700000000000000000fe83ce4b82ba1418000000000051c0000000ef800000019c1f4800102006600000000000000001c944002ab00000000000c61b8047800000017080000000000000000a9e5fb000000000000000004040000001c200000004222a594482420000a2086057822b16380047141c9370131400052c05709103005393a38d6cc061a900000000000002e3000000000000000000005b40a880000000000000000000380000000087200014f00008540001d8800000066136f104423e2fc2c4000050a0000a80000bca1bb07d0634dae3a13d18bac0000003fa00005be0000000018b6e22c07009980000002a6800000000000000000000000000000f247020b880005700001fc99a85dc1d123817d4c200e92ba8a089ee52523280001ee14b20e9ea8ab81f809c08fc12e5ba22109bc53e0000c900000000002e4800046200000001f08d65ea0000d48c2800025a800062600019a800000064a0000000000000000000000000034d80008f63be0000000092000213800000009400000000006ec332874c0003791ac80009b24d0043960cb3832c000000000051831788d0bc012e1d69df074a49e00020640003af000033473e000000139400000000018f00000000001a608025e81da98541a87340000c504b42cf16c1a2000000018e8000ac62fe0a61de49c63482a29f48000033000000000000000000000000000000fd48340193ec000018276600000000d400027e000021640f0000000dcc6483988a3ce5817d000000095870426f05f80002c90389c68a5075e09c8000ad803022d000097c00014194ec61e0f8405131cf2602216a090c42e5fa0f40000c7c0002e70000b007b52219d38a866ff0000000000000000000079a0db0f000000006832b989841500003dd1f5000032f000108c0007f11588000cbc5c83e01d8000014523c1c4883067400000007bc6340e315900003db04a92240001661cf0d2c000278084000051866b0d38000d544503fb000000659d2d90f74594000000123d02c2de0001af80f060c0611530d3282a3c29744a5e00d3e8a0806c62bd0e187cc7ee04a2b3962460044027f137cee86cf0000898360000126029400000000018944360000000ee4fc673e0000000ef43d233d20045cc62e1469fac9563c00849120ea
  | 12 => 0x841463d09a1477003a01b05245de581009000000048e14880000000002ae80000006c0000202c0002b20718d38cc82690f514b903646336d16442462a70e41e00f9074c109165cd9c44c1f109746f60d72e605880003ea241927c0007b60001b6095a0000001ce400021d000000026460028f8000f1e1b2000000000000008600fc92e01f15000000000000000000000000000000000000003f80000000000fd00003120000000000000000145841c0e80000000000b5c7c90f285e45d46d31a78f7071800012b868036c0cf362099c4e43fe000000042a4cc07080001d80003ef9758674000201800000000000012608487a733b089cdf64083270e0c5c80000000434aa420605200005420000258b380005e4000000000022f0e591cc00038e40e9010fc8757036136c2865010c19128d8208a03e9ad8528000144978c6d60000d68dd020a3a0000130cd700001279a9800070b07f000000000000e1628000153000000000043b00000400002c000000002b233408a0878a642980f18370000781345898862a6d40002084c1e00000016b0bb800003002880000000001708d0000016895886b80000001ce800000000014fced2000000000013a295259184c78a36700000006620ff0200b4063c0000bc000016200a38e94f8e9a6c52d38eec0f20000000000d4800025202fca143860001f74000000000009403400000020080005710000000c34000000000079e0000000bb400077f26706103546510000b146ae6ac0cf000025e67b000000000000029b8ad00007e20000000e7052122480005020f63238000cfa3360eb00000007860000000ddc4070001d70bba4d80000000d2403e0001adc00000000020240002461a203b8156740184134c2e46b900a80009d07101cb07309dc6670a7027cee440e32218fc13c093026800000027431a8000b5651d0d9800033009b40305d8cc45c319b86a06b45b13fb85704fe00000001301800f40001a04000343000000000000000015f8b9a3fd24900000006970001e30f8400000014e00002c62df94240005662b91ac8cc60d512d823066400000000001320000000000bf80000000114c300000000000ef00000f3072888c0000488d54bb079413b00001f84910c38894620000000000000072639800000006c33468f3056a1d920608102080722438a206d463129103887522680b6068cc1602f34a8d008a41102d10f80fac7ab0560280fb276b0001458c146663e800004443e600000000000002278d84b4a51a04e0b3041a6ef2d01070cb47762551bf8e3e5b834115381fa00017a13850240a117011f06e65a813b8b040fc51b0139d183201752339cb800053336a991400045739510b400034c40d141c00002d0f20d347f809a1a08444fca0003d01b2900e0002160000d46000000189800000000
  | 13 => 0xf9ffcf880d63908ceccaa52623682c88ba04737505e80000002d218c87167132c815640003180000000786000000000000020f00000000002cd1b60c300006e32379b7400080d00000000002c20da03bc9260003a9209400000029a11d8d5a00000000000002e93cc16147e60730000e20bf03b206716b400041230400006ea69d00000000007870ed80000000bb19f80003fc28e2c69784214000081000089c1d81521c2400000033a945c0000002189f68e827901571be000000000000000000000000c8462c00022b1f300c825400001ac3d66700271b3400035d0001d5837226b2bb0fd06520b90000788ba83da3db856cf8662210500003180d10001fbcbce66e05383786a07e633f08a4ae02f33851584ee02ec1c797b4b260e515282104f41033f417406c0000000003c67a170000000000000022c800000000000013ec2a4000220800000023d13e03c4d5200000000000004681d8208ccac11c00001b8d783450001b580000bc1a9816c6220f01d302044f63ae3c20e7101c2bf2598768a6213e1db1be87dc14831c181ce4481c00480102ee6f60001db00000000001c500003890471cf45a600000000000000002a11b300903ab3fd15205b66193ee010cf323a312f09c017408d07500004c80000000000ea60001b4036000025210384743d216f0001e940006910010674ca81fc00000000005bd3c880000000000000fb400000009d00000000002050000c4e39900013f4d2000019820305e400020a93c048400000000001100002b019fccb6000000055403c0752db00000005f02ef88a80c219602c9ca4f824fa2be141092017c06500010264e73f697e4c3c03521480e4c5221601507d874e000302800039e68900010786462050000000420677000207800000035e8d60ee257913880a47340eb0000000f7c7b900013540007fe3b391c8dea32e129819c0007ac26e1d6000000028400008aa2cb0000000000000000000000000030b8b2000071b0000000b0825f2468c28c044e43860c0c8fa53a0af808c4508223838000c860d90088224eda3ba2aa86b00006c217800000b855716b80000000000000000abc0000000ce07d023719e156cf1c80526900000001bd21f80004024c91c9000000023030480000000000f61a280001ba2268a2862e00000000000ec0001ef98e837850f0001948000000000000000000027509b0ed00e60831ff0edc0000000000c8200730e00004a00001921810a5619f000000095e0000000a408d818b1e8142c78e6f240199e0e382f91fd8d5896c0002d79f2c2c20000d899a00480003dc000083666f09e8944d1c2a604100000000000519268c567593368000b800000911efc000000000000085e000250800000024100000003aa221000122086a70d02d017c0c400032980000000000001a947
  | 14 => 0x7a0000e7400000000015bc85000010880003100000000da40000000000000f8c6db12716ec00000000017dc000000000000088e3ef00014704720000000000000000000096000067c1e512f4000000110020c000000266925410c000068000086847a32605685f6000368997000000009f800000000037b9f5ceba000000000000041300000010280000c08000b425e205b8d080000000000000d0c6e90001aac304000388852800000000000000da82b00000002ae29d08c9cfc0005ef206916c02c62100000000005963b20000000000222000070e5cf0000000ea27d30000000fce1f036300000003043a400000000000000000e305e600015dc000000000000000031a00002d8ec679d00000000000000100dfca004b012b0bdcdbe000072000000000000009a815e6ba000000000037a19580008ee0002cf00005ba61200012ecbb445f1af031c4fc44530312881e632a000114470a23832c9e58a946b100000005080f93e384d07b200005c1c200165692779e680000000d220440000000000b480000801438000f160001bf0d880000003d78000a8000000000000000650000df463e49600013b0e8a1fb048209800059f2e21a8094000018685ac35c09621c04605382ba23494646a863028a8b0cb6652d02912008e82f1257157c9825351b70e4c00000000005609ba5e900007b8936694000000000000012698f4f8a00034d000000000000010f464e3020580000aac5540fa033000013b00018740000b53ba9f80fe400031d9ea00000000001b2c54455a3bd9f343321d73d11aec03a4940000ad800053d00008b400017f0001cb400000000005a00005232d30000d600003998000754000000143494e02c2b581a47ce32000009ccbae0ed23200c8c6c2d63a48000c9e3c80f09b24a546232a21c8c3bc1863c500000000000000a680001160001fe000000000000000000000001e5c7c87e9000209041200017c0a8c0005f43a200009880003cd944c1160000b48f440000003680c38d4200027c0000f6605100000000007bd25f88680000000000000000000000000000000000000000000b30cb86ac00000000000009da12c099830c43200000000000000000001a3000061b000192c00060e00006fc0007de0000020a4e0002460c6c0001c52650000ed400000018dc94a64d3570cf8000000000034c0000003d893d4d4400028895f4b7c0002d8171c47c20e3901fe4e0c71e0000ed00004370fe9e2060a7bb0000000000000000000000076f00004b4550000000000004c62a2411be43ba0000000000c480003a1000000000014c80000e000008a90b80005d900012280000000001fa809e3f6310000000000000000000000000000000000000000000000059900010009ec1a515489707ca72400b831031c2b90ca1058b9644b2
  | 15 => 0x4ac33400000019cc0000000000a18a8c00007d984400000036380000007d51c68c64b3400022e0b108bc5ca000000000071500020a42ac3cb0000468a6c00011b1bc04fa2fd1bb800077e4530791c1503e000000000065a00000013c8000000000080884c00000012e466669e00015a813016e1b31f2900000000019808dc00028287c4af40df13709942500e82689a3cc021850a780009963a83940fc822e0be14d9d284922550478000c5a00030b046c0aa8181059a702a82ac000168c9322b02f60178000000000000000034928100000006f100000000003d40000fac79205400005ccb720da3be81ec00000009a9714490693042815c0000b41cb800000000000000000000000000000ee61291b90980b5273500019c44264b70fb99005ca5fe0001abcc8c5530000000d0e4790ae80d000054100006e055a3f0140059022482700003d485614101b9cac8b02da4160ffc0000002758c2407680817f951c000000093121880415e3c480aceca07700000000002b711e0fe00000000000c880003c400000008125ff292000090a0003d49a7cf5a00032f9c640000183a187bc6500922de032068e3d72f990140000003cf1c58cf24e201080005c481702814a422656d0001c04aa00000000000000000393800000000010400009d2127000071c8fc00013a9d686de16d2731a5800000000015ec8c043637400006c80000001834152000000000000000020b8870eee4b4387000046a000000000086618a00000004480003a586f80004710b0159402600000006440000001f18b8caa27a600000000006fd397947899e63900015600ac00000000008405981cc0c1c87400027880b821c1dc3d700000004d60d30df0ff67500d78490cba2af342000000030100000006da23b1bc00007ac0000001ff400000000000000b07f340a8000c3e0000000b9c0001ed17416d48fe6d92ca8000000000000098c00034600000001ba0002c30f84f3e454002901893a7621238000000000000000000065000000000000aa000000021e00001c00000003c60d0800072a1f2000000024a0001de9b94000000000119838203c000118400026d07380006160000000000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xb7248110027eb7248110007eb624811006efa624811006ef86248110007e862481101bfea42481101bfe94248110007f3714811001dfa714811001df87148110007f07148110026fb6148110027f361481101bff241481101bff141481100b4ff7598c10014fe7598c10004fd7598c100b4fc7598c100b4ff7498c1000cfe7498c10004fd7498c100b4fc7498c100067f5498c100067d5498c10024fe7398c10026de7398c100b6de5398c10006dd5398c100b6de4398c10006dd4398c1006cfe7298c10004fd7298c1001cfe7198c1001cfc7198c1001ede3198c1001edc3198c10024fe7098c10024fc7098c10026de3098c10026dc3098c10004ff7558c100067f7558c100047f7558c10014fe7558c10004fd7558c10014fc7558c100067c7558c100147c7558c10004ff7458c1000cfe7458c10004fd7458c1000cfc7458c100067f5458c100067d5458c10024ff7358c10026df7358c10006de5358c10006dd5358c10006de4358c10006dd4358c10004ff7258c1006cfc7258c1001cff7158c1001cfe7158c1001cfd7158c1001cfc7158c1001ede3158c1001edc3158c10024ff7058c10024fe7058c10024fd7058c10024fc7058c10026de3058c10026dc3058c10026fa1058c1001ef91058c1006cff7598810014fe7598810004fd759881006cfc759881006cff749881000cfe7498810004fd749881006cfc74988100067f54988100067d54988100b4fe7398810004fd7398810024fe7298810026ee729881006eee5298810006ed529881006eee4298810006ed429881001cfe719881001cfc719881001eee219881001eec2198810024fe7098810024fc7098810026ee2098810026ec2098810004ff75588100067f75588100047f7558810014fe7558810004fd7558810014fc75588100067c75588100147c7558810004ff745881000cfe7458810004fd745881000cfc74588100067f54588100067d5458810004ff73588100b4fc7358810024ff7258810026ef7258810006ee5258810006ed5258810006ee4258810006ed425881001cff715881001cfe715881001cfd715881001cfc715881001eee215881001eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810026fa105881001ef910588100b4ff76cc810024fe76cc810004fd76cc810024fc76cc8100357e75cc8100057d75cc8100b6de63cc810006dd63cc81006cff768c810024fe768c810004fd768c810024fc768c8100357e758c8100057d758c81006eee628c810006ed628c810004ff764c810024fe764c810004fd764c810024fc764c810006de634c810006dd634c810006ee624c810006ed624c810005f7714c81001df4714c81006cff760c810024fe760c810004fd760c810024fc760c810007cd320c810
  | 1 => 0x8910004fd731891006eee721891001cfe711891001cfc7118910024fe701891006ef97018910024fc70189100b4ff76cc910004fe76cc910004fd76cc9100b4fc76cc9100457e75cc9100057d75cc910006ef62cc910006ec62cc910025fa70cc910005f970cc91006cff768c910004fe768c910004fd768c91006cfc768c9100457e758c9100057d758c910006df638c910006dc638c910025fa708c910005f9708c910004ff764c910004fe764c910004fd764c910004fc764c91006cff760c910004fe760c910004fd760c91006cfc760c910006df630c9100b6dc630c910006ef620c91006eec620c910007cd320c91001df6710c910005f5710c910025fa700c910005f9700c910024fe76cc510006df63cc5100b6dc63cc510025fa70cc510005f970cc510024fc764c5100057f754c5100457c754c510006df634c510006dc634c510005ef724c510005ec724c510005fb704c510025f8704c510024fe76c8510006ef62c851006eec62c8510025fa70c8510005f970c8510024fc76485100057f75485100457c7548510005df7348510005dc7348510006ef6248510006ec6248510005fb7048510025f8704851001cfe76cc110006df63cc1100b6dc63cc11001df671cc110005f571cc110005fa768c110026fa768c1101ef7b548c1101ef79548c1101f5f9738c1100b6fa638c1100b6f8638c110005f9728c11001dfa718c110025f8718c110026fb618c110027f3618c1101eff2418c1101eff1418c1100b4ff764c110004fd764c11001cfc764c1100057f754c1100457c754c110005bf744c11003dbc744c110006df634c110006dc634c110005f7714c11001df4714c11001df8764c110006f8764c11001cf8764c1100077b754c1101e778754c110007bb744c1101dfb8744c1101df7b544c1101df79544c110025fb734c110027db734c110007db634c1100b6fa634c1100b6f8634c110007d8634c1101dfda434c1101dfd9434c110005fb724c110007f3714c11001dfa714c11001df8714c110007f0714c110026fb614c110027f3614c1101dff2414c1101dff1414c11001cfe76c8110006ef62c811006eec62c811001df671c8110005f571c8110005fa7688110026fa76881101cf7b54881101cf795488110025fb7388110005f973881101d5f9728811006efa628811006ef8628811001dfa7188110025f87188110026fb6188110027f361881101cff241881101cff1418811006cff7648110004fd764811001cfc76481100057f75481100457c7548110005bf744811003dbc7448110006ef6248110006ec6248110005f7714811001df4714811001df87648110006f8764811001cf876481100077b75481101c7787548110007bb74481101bfb874481101bf7b54481101bf795448110005fb7348110005f97348110025f
  | 2 => 0x4ff74d8d1000cfe74d8d10004fd74d8d1000cfc74d8d100067f54d8d100067d54d8d1006cfe72d8d10004fd72d8d10006df6398d100b4ff7598d10014fe7598d10004fd7598d100b4fc7598d100b4ff7498d1000cfe7498d10004fd7498d100b4fc7498d100067f5498d100067d5498d100b4fe7398d1006cfe7298d10004fd7298d10004fd7198d100b6f57198d10004fd7098d100b6f97098d100057f7558d100457c7558d10005bf7458d1003dbc7458d10005ef7258d10005ec7258d10004ff7558d100067f7558d100047f7558d10014fe7558d10004fd7558d10014fc7558d100067c7558d100147c7558d10004ff7458d10006bf7458d10004bf7458d1000cfe7458d10004fd7458d1000cfc7458d10006bc7458d1000cbc7458d100067f5458d100067d5458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1006cfc7258d10006ec7258d10004ec7258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d100457e7518d100057d7518d10006dd6318d100b4ff7518d10014fe7518d100b67e7518d100147e7518d10004fd7518d100b67d7518d100047d7518d100b4fc7518d100b4ff7418d1000cfe7418d10004fd7418d100b4fc7418d100067f5418d100067d5418d100b6de7318d1006cfe7218d10004fd7218d1001cfe7118d1001cfc7118d10024fe7018d100b6f97018d10024fc7018d10004ff75d8910014fe75d8910004fd75d8910014fc75d8910004ff74d891000cfe74d8910004fd74d891000cfc74d89100067f54d89100067d54d89100b4fe73d8910004fd73d8910006ef629891006cff7598910014fe7598910004fd759891006cfc759891006cff749891000cfe7498910004fd749891006cfc74989100067f54989100067d54989100b4fe7398910004fd739891006cfe7298910004fd719891006ef57198910004fd709891006ef970989100057f75589100457c7558910005bf745891003dbc7458910005df7358910005dc7358910004ff75589100067f75589100047f7558910014fe7558910004fd7558910014fc75589100067c75589100147c7558910004ff7458910006bf7458910004bf745891000cfe7458910004fd745891000cfc7458910006bc745891000cbc74589100067f54589100067d5458910004ff7358910006df7358910004df73589100b4fc7358910006dc7358910004dc7358910006ef7258910004ff7158910006f77158910004ff7058910006fb7058910004fe76189100457e75189100057d7518910006ed621891006cff7518910014fe751891006e7e75189100147e7518910004fd751891006e7d75189100047d751891006cfc751891006cff741891000cfe7418910004fd741891006cfc74189100067f54189100067d54189100b4fe731
  | 3 => 0xe7458e10004fd7458e1000cfc7458e100067f5458e100067d5458e10026df7358e10006de4358e10006dd4358e10004ff7258e1006cfc7258e10024fc7058e10026de3058e10026dc3058e1006cff7598a10014fe7598a10004fd7598a1006cfc7598a1006cff7498a1000cfe7498a10004fd7498a1006cfc7498a100067f5498a100067d5498a100b4fe7398a10004fd7398a10026ee7298a1006eee4298a10006ed4298a10024fe7098a10026fa7098a10024fa7098a10026ee2098a10026fa2098a10026ec2098a10004ff7558a10014fe7558a10004fd7558a10014fc7558a10004ff7458a1000cfe7458a10004fd7458a1000cfc7458a100067f5458a100067d5458a10004ff7358a100b4fc7358a10026ef7258a10006ee4258a10006ed4258a10024fc7058a10026ee2058a10026ec2058a100b4ff76cca10024fe76cca10004fd76cca10024fc76cca100557e75cca100057d75cca101b67e65cca100067d65cca10006ee62cca10006ed62cca10025fa70cca10005f970cca1006cff768ca10024fe768ca10004fd768ca10024fc768ca100557e758ca100057d758ca101ae7e658ca100067d658ca10006de638ca10006dd638ca10025fa708ca10005f9708ca10004ff764ca10024fe764ca10004fd764ca10024fc764ca101a67e654ca100067d654ca10005f7714ca1001df4714ca10025fa704ca1006cff760ca10024fe760ca10004fd760ca10024fc760ca101867e650ca100067d650ca100b6de630ca10006dd630ca1006eee620ca10006ed620ca10007cd320ca10025fa700ca10005f9700ca101767e65cc6100067d65cc6100b6de63cc610006dd63cc610025fa70cc610005f970cc6100057f754c6100557c754c61015e7e654c6100067d654c610006de634c610006dd634c610005ef724c610005ec724c610005fb704c610025f8704c6101367e65c86100067d65c861006eee62c8610006ed62c8610025fa70c8610005f970c86100057f75486100557c754861011e7e65486100067d6548610005df7348610005dc7348610006ee6248610006ed6248610005fb7048610025f87048610025fb764c210006fb764c2100077b754c21021778754c2100277a654c21002779654c210007bb744c21020fb8744c21020f7b544c21020f79544c210027db734c2100b6fa634c210026f8634c21020fda434c21020fd9434c210005fb724c21001dfa714c21001df8714c210025fb7648210006fb76482100077b75482102077875482100277a6548210027796548210007bb74482101ffb874482101ff7b54482101ff795448210005fb7348210005f97348210027eb724821006efa6248210026f862482101ffea42482101ffe9424821001dfa714821001df87148210004ff75d8d10014fe75d8d10004fd75d8d10014fc75d8d10
  | 4 => 0x8b1001eec2158b1001efa1058b1001ef91058b100b4ff76ccb1001cfe76ccb10004fd76ccb1001cfc76ccb100657e75ccb100057d75ccb101b67e65ccb100067d65ccb10196be64ccb10006bd64ccb100b6de63ccb10006dd63ccb1006cff768cb1001cfe768cb10004fd768cb1001cfc768cb100657e758cb100057d758cb101ae7e658cb100067d658cb1018ebe648cb10006bd648cb1006eee628cb10006ed628cb10004ff764cb1001cfe764cb10004fd764cb1001cfc764cb101a67e654cb100067d654cb1019ebe644cb10006bd644cb10006de634cb10006dd634cb10006ee624cb10006ed624cb1006cff760cb1001cfe760cb10004fd760cb1001cfc760cb101867e650cb100067d650cb1017ebe640cb10006bd640cb10007cd320cb1001df6710cb10005f5710cb100f67e65cc3100067d65cc3100cebe64cc310006bd64cc3100b6de63cc310006dd63cc31001df671cc310005f571cc3100057f754c3100657c754c3100de7e654c3100067d654c310005bf744c31005dbc744c3100d6be644c310006bd644c310006de634c310006dd634c310005f7714c31001df4714c3100ae7e65c83100067d65c8310086be64c8310006bd64c831006eee62c8310006ed62c831001df671c8310005f571c83100057f75483100657c75483100967e65483100067d6548310005bf744831005dbc744831008ebe6448310006bd6448310006ee6248310006ed6248310005f7714831001df471483100067f74596100047f74596100067e74596100067d74596100047d74596100067c74596100067f73596100067e73596100067d73596100067c73596100067f43596100067e43596100067d43596100067c43596100067f72596100067e72596100067d72596100067c72596100067f42596100067e42596100067d42596100067c42596100567f715961021e7e71596100067d715961021e7c71596100067f415961021e7e41596100067d415961021e7c415961021e7e315961021e7c315961021e7e215961021e7c21596100267f70596100267e70596100267d70596100267c70596100267f40596100267e40596100267d40596100267c40596100267f30596100267e30596100267d30596100267c30596100267f20596100267e20596100267d20596100267c20596100267f10596100267e10596100267d10596100267c10596100b4ff7598e10014fe7598e10004fd7598e100b4fc7598e100b4ff7498e1000cfe7498e10004fd7498e100b4fc7498e100067f5498e100067d5498e10026de7398e100b6de4398e10006dd4398e1006cfe7298e10004fd7298e10024fe7098e10026fa7098e10024fa7098e10026de3098e10026fa3098e10026dc3098e10004ff7558e10014fe7558e10004fd7558e10014fc7558e10004ff7458e1000cf
  | 5 => 0x67e74597100067d74597100047d74597100067c74597100067f73597100067e73597100067d73597100067c73597100067f43597100067e43597100067d43597100067c43597100067f72597100067e72597100067d72597100067c72597100067f42597100067e42597100067d42597100067c425971001e7f715971001e7e715971001e7d715971001e7c715971001e7f415971001e7e415971001e7d415971001e7c415971001e7f315971001e7e315971001e7d315971001e7c315971001e7f215971001e7e215971001e7d215971001e7c21597100667f705971022e7e70597100067d705971022e7c70597100067f405971022e7e40597100067d405971022e7c405971022e7e305971022e7c305971022e7e205971022e7c205971001e7f105971001e7e105971001e7d105971001e7c1059710006bf7559310006be75593100063e7559310006bd75593100063d7559310006bc7559310006bf7359310006be7359310006bd7359310006bc7359310006bf5359310006be5359310006bd5359310006bc5359310006bf7259310006be7259310006bd7259310006bc7259310006bf5259310006be5259310006bd5259310006bc525931001ebf715931001ebe715931001ebd715931001ebc715931001ebf515931001ebe515931001ebd515931001ebc515931001ebf315931001ebe315931001ebd315931001ebc315931001ebf215931001ebe215931001ebd215931001ebc215931005ebf7059310226be7059310006bd7059310226bc7059310006bf5059310226be5059310006bd5059310226bc5059310226be3059310226bc3059310226be2059310226bc205931001ebf105931001ebe105931001ebd105931001ebc10593100b4ff7598f10014fe7598f10004fd7598f100b4fc7598f100b4ff7498f1000cfe7498f10004fd7498f100b4fc7498f100067f5498f100067d5498f1001ede7398f1006cfe7298f10004fd7298f10024fe7198f1001ede3198f1001edc3198f10004ff7558f10014fe7558f10004fd7558f10014fc7558f10004ff7458f1000cfe7458f10004fd7458f1000cfc7458f100067f5458f100067d5458f1001edf7358f10004ff7258f1006cfc7258f10024fc7158f1001ede3158f1001edc3158f1001efa1058f1001ef91058f1006cff7598b10014fe7598b10004fd7598b1006cfc7598b1006cff7498b1000cfe7498b10004fd7498b1006cfc7498b100067f5498b100067d5498b100b4fe7398b10004fd7398b1001eee7298b10024fe7198b1001eee2198b1001eec2198b10004ff7558b10014fe7558b10004fd7558b10014fc7558b10004ff7458b1000cfe7458b10004fd7458b1000cfc7458b100067f5458b100067d5458b10004ff7358b100b4fc7358b1001eef7258b10024fc7158b1001eee215
  | 6 => 0xd70594200267c70594200267f40594200267e40594200267d40594200267c40594200267f30594200267e30594200267d30594200267c30594200267f20594200267e20594200267d20594200267c20594200267f10594200267e10594200267d10594200267c10594200b4ff7598c20014fe7598c20004fd7598c200b4fc7598c200b4ff7498c2000cfe7498c20004fd7498c200b4fc7498c200067f5498c200067d5498c20024fe7398c20026de7398c200b6de4398c20006dd4398c2006cfe7298c2006cfc7298c2006ede3298c2006edc3298c2001cfe7198c20004fd7198c20024fe7098c20024fc7098c20026de3098c20026dc3098c20004ff7558c20014fe7558c20004fd7558c20014fc7558c20004ff7458c2000cfe7458c20004fd7458c2000cfc7458c200067f5458c200067d5458c20024ff7358c20026df7358c20006de4358c20006dd4358c200b4ff7258c2006cfe7258c2019cfd7258c2006cfc7258c2006ede3258c2006edc3258c20004ff7158c2001cfc7158c20024fe7058c20024fc7058c20026de3058c20026dc3058c20004fd76cc82007d7e75cc8200057d75cc8201b67e65cc8200067d65cc820004ff764c8201a67e654c8200067d654c82006fcc324c820004ff7558420014fe7558420004fd7558420014fc7558420004ff745842000cfe7458420004fd745842000cfc74584200067f54584200067d5458420004ff73584200b4fc7358420026f77158420006f64158420006f5415842006ef7215842006ef42158420024ff7058420024fd7058420026fa2058420026f61058420026f410584200b4ff76cc420024fe76cc420004fd76cc4201767e65cc4200067d65cc4200b6de63cc420006dd63cc42001cff768c420024fe768c420004fd768c42016e7e658c4200067d658c42001ef6618c420006f5618c420004ff764c420004fd764c420024fc764c4200057f754c42007d7c754c42015e7e654c4200067d654c420006de634c420006dd634c420005ef724c42006dec724c42001ef6614c420006f5614c42001cff760c420024fe760c420004fd760c42007d7e750c4200057d750c4201467e650c4200067d650c420075be740c420005bd740c42006dee720c420005ed720c420025fa700c420005f9700c420004fd768842012e7e65884200067d6588420004ff76484200057f754842007d7c754842011e7e65484200067d6548420005df7348420005dc7348420025fb7648020006fb7648020004fb76480200077b75480202377875480200277a6548020027796548020007bb744802023fb8744802023f7b544802023f795448020025fb7248020027eb724802006efa6248020027ea624802006fea5248020237e9524802006fea3248020007e93248020006f961480200067f74597100047f7459710
  | 7 => 0x8520004fe76cc520004fd76cc5200b4fc76cc5200067f65cc5201767c65cc520006bf64cc52014ebc64cc520006f761cc52001ef461cc520004fe768c520004fd768c52001cfc768c5200067f658c52016e7c658c520006bf648c520166bc648c520006df638c520006dc638c520025fa708c520005f9708c520004ff764c520004fe764c520004fc764c5200057f754c5200957c754c5200067f654c52015e7c654c520006bf644c520156bc644c520005ef724c520005ec724c520004fe760c520004fd760c52001cfc760c5200957e750c5200057d750c5200067f650c5201467c650c52008dbe740c520005bd740c520006bf640c52013ebc640c520006df630c5200b6dc630c520005ee720c520005ed720c520006f7610c52001ef4610c520025fa700c520005f9700c520004fe76c85200067f65c85201367c65c8520006bf64c852010ebc64c8520024fe76885200067f658852012e7c6588520006bf6488520126bc6488520006f7618852001ef46188520025fa7088520005f97088520024fc76485200057f75485200957c75485200067f654852011e7c6548520006bf6448520116bc6448520005df7348520005dc7348520006f7614852001ef46148520005fb7048520025f87048520004fe76085200957e75085200057d75085200067f65085201067c650852008dbe7408520005bd7408520006bf64085200febc6408520005de7308520005dd7308520025fa7008520004fe76cc1200067f65cc1200f67c65cc120006bf64cc1200cebc64cc120006df63cc1200b6dc63cc120005ee72cc120005ed72cc1200b4ff764c120004fd764c120004fc764c1200057f754c1200957c754c1200067f654c1200de7c654c120005bf744c12008dbc744c120006bf644c1200d6bc644c120006df634c120006dc634c120005ef724c120005ec724c120027d8304c120027e8204c1200067f65c81200ae7c65c8120006bf64c8120086bc64c8120025ee72c8120026ef62c8120024fa76c81200077b65c812024f7865c8120007bb64c8120247b864c81202477b54c81202477954c8120025fa72c8120026fb62c8120027eb62c812006fea42c8120247e942c8120005f971c81200067f74594200047f74594200067e74594200067d74594200047d74594200067c74594200067f73594200067e73594200067d73594200067c73594200067f43594200067e43594200067d43594200067c435942007e7f725942006e7e725942007e7d725942006e7c72594200067f425942006e7e42594200067d425942006e7c425942006e7e325942006e7c32594200067f71594200067e71594200067d71594200067c71594200067f41594200067e41594200067d41594200067c415942006e7f215942006e7c21594200267f70594200267e70594200267
  | 8 => 0x4fd71d8d200957e7598d200057d7598d200067f6598d200067c6598d2008dbe7498d20005bd7498d20006bf6498d20006bc6498d20006df6398d200b4ff7598d20014fe7598d200b67e7598d200147e7598d20004fd7598d200b67d7598d200047d7598d200b4fc7598d200b4ff7498d2000cfe7498d200b6be7498d2000cbe7498d20004fd7498d200b6bd7498d20004bd7498d200b4fc7498d200067f5498d200067d5498d200b4fe7398d20004fd7298d200b6ed7298d2001cfe7198d20004fd7198d20004fd7098d200b6f97098d200057f7558d200957c7558d200067f6558d200067c6558d20005bf7458d2008dbc7458d20006bf6458d20006bc6458d20005f77158d20005f47158d20004ff7558d200067f7558d200047f7558d20014fe7558d20004fd7558d20014fc7558d200067c7558d200147c7558d20004ff7458d20006bf7458d20004bf7458d2000cfe7458d20004fd7458d2000cfc7458d20006bc7458d2000cbc7458d200067f5458d200067d5458d20006df7358d20004ff7258d20006ef7258d20004ff7158d20006f77158d20004f77158d2001cfc7158d20006f47158d2001cf47158d20004ff7058d20006fb7058d20004fe7618d200067f6518d200067c6518d20006bf6418d20006bc6418d20006dd6318d200b4ff7518d20014fe7518d20004fd7518d200b4fc7518d200b4ff7418d2000cfe7418d20004fd7418d200b4fc7418d200067f5418d200067d5418d200b6de7318d2006cfe7218d2006cfc7218d2001cfe7118d20004fd7118d20024fe76cc9200957e75cc9200057d75cc9200067f65cc9201b67c65cc920006bf64cc920196bc64cc920006df63cc9200b6dc63cc920025fa70cc920005f970cc920004fe768c9200957e758c9200057d758c9200067f658c9201ae7c658c920006bf648c92018ebc648c920024fc764c9200067f654c9201a67c654c920006bf644c92019ebc644c920006df634c920006dc634c920005fb704c920025f8704c920004fe760c9200067f650c9201867c650c920006bf640c92017ebc640c920007cd320c9200067f65d85200067c65d8520006bf64d8520006bc64d8520004ff75d8520014fe75d8520004fd75d8520014fc75d8520004ff74d852000cfe74d8520004fd74d852000cfc74d85200067f54d85200067d54d85200b4fe73d8520004fd73d8520024fe70d8520024fc70d85200957e75985200057d75985200067f65985200067c659852008dbe7498520005bd7498520006bf6498520006bc6498520006f761985200057f75585200957c75585200067f65585200067c6558520005bf745852008dbc7458520006bf6458520006bc6458520005df7358520005dc73585200067f65185200067c6518520006bf6418520006bc641852001ef66118520006f5611
  | 9 => 0xe720c620005ed720c620025fa700c620005f9700c620025f870c862001ef66188620006f56188620025fa7088620005f9708862001cff76486200057f75486200a57c7548620005df7348620005dc734862001ef66148620006f56148620005fb7048620025f870486200a57e75086200057d750862009dbe7408620005bd7408620005de7308620005dd7308620025fa7008620005f97008620025f976c822006ef976c822026f7b54c822026f7954c8220027ea72c822006fea52c8220267e952c8220005f971c82200957e76d95200967e76d95200147e76d95200057f74d95200057d74d95200067f64d95200067e64d95200067d64d95200067c64d95200073c64d95200063c64d95200076e42d95200076d42d952025f6e20d952025f6c20d95200067f74d95200047f74d95200067e74d95200067d74d95200047d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d952025e7f72d95200967e72d95200967d72d95200967c72d95200067f42d95200067e42d95200067d42d95200067c42d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067e41d95200067d41d95200067c41d95200067f70d952025e7e70d95200967d70d952025e7c70d95200067f40d952025e7e40d95200067d40d952025e7c40d952025e7e30d952025e7c30d952025e7e20d95200967d20d952025e7c20d952025e7e10d952025e7c10d952008dbe76d912008ebe76d912000cbe76d91200073f75d91200073c75d9120006bf65d91200073f65d91200063f65d9120006be65d9120006bd65d9120006bc65d91200073c65d91200063c65d9120257af72d912008fac72d9120257ae20d9120257ac20d9120006bf75d91200063f75d9120006be75d9120006bd75d9120006bc75d91200063c75d9120006bf73d9120006be73d9120006bd73d9120006bc73d9120006bf53d9120006be53d9120006bd53d9120006bc53d9120256bf72d912008ebe72d912008ebd72d912008ebc72d9120006bf52d9120006be52d9120006bd52d9120006bc52d9120006bf71d9120006be71d9120006bd71d9120006bc71d9120006bf51d9120006be51d9120006bd51d9120006bc51d9120006bf70d9120256be70d912008ebd70d9120256bc70d9120006bf50d9120256be50d9120006bd50d9120256bc50d9120256be30d9120256bc30d9120256be20d912008ebd20d9120256bc20d9120256be10d9120256bc10d91200067f65d8d200067c65d8d20006bf64d8d20006bc64d8d20004ff75d8d20014fe75d8d20004fd75d8d20014fc75d8d20004ff74d8d2000cfe74d8d20004fd74d8d2000cfc74d8d200067f54d8d200067d54d8d2001cfe71d8d20
  | 10 => 0xcb2006fcc324cb2006ef7619872001ef461987200057f75587200ad7c755872006ef46158720004ff75587200067f75587200047f7558720014fe7558720004fd7558720014fc75587200067c75587200147c7558720004ff745872000cfe7458720004fd745872000cfc74587200067f54587200067d5458720004ff73587200b4fc7358720024fc725872006ef7215872006ef421587200b4ff76cc72006cfe76cc720004fd76cc7200b6de63cc720006dd63cc72001cff768c72006cfe768c720004fd768c720004ff764c720004fd764c72006cfc764c7200057f754c7200ad7c754c720006de634c720006dd634c720005ef724c72006dec724c72001cff760c72006cfe760c720004fd760c7200ad7e750c7200057d750c720085be740c720005bd740c72006dee720c720005ed720c720025fa700c720005f9700c7200057f75487200ad7c7548720005df7348720005dc73487200b6de63cc320006dd63cc32006dee72cc320005ed72cc3200057f754c3200ad7c754c320005bf744c320085bc744c320006de634c320006dd634c320005ef724c32006dec724c3200b4ff7598e20014fe7598e20004fd7598e200b4fc7598e200b4ff7498e2000cfe7498e20004fd7498e200b4fc7498e200067f5498e200067d5498e20026de7398e200b6de5398e20006dd5398e200b6de4398e20006dd4398e2001cfe7198e20004fd7198e20024fe7098e20026de3098e20026dc3098e20004ff7558e200067f7558e200047f7558e20014fe7558e20004fd7558e20014fc7558e200067c7558e200147c7558e20004ff7458e2000cfe7458e20004fd7458e2000cfc7458e200067f5458e200067d5458e20026df7358e20006de5358e20006dd5358e20006de4358e20006dd4358e20004ff7158e2001cfc7158e20024fc7058e20026de3058e20026dc3058e20026fa1058e200a57e75cca200057d75cca200b6de63cca20006dd63cca20025fa70cca20005f970cca200a57e758ca200057d758ca20006de634ca20006dd634ca20005fb704ca20025f8704ca20007cd320ca20004ff7558620014fe7558620004fd7558620014fc7558620004ff745862000cfe7458620004fd745862000cfc74586200067f54586200067d5458620004ff73586200b4fc7358620026f77158620006f64158620006f54158620026f61058620026f410586200b4ff76cc620024fe76cc620004fd76cc62001cff768c620024fe768c620004fd768c620006de638c620006dd638c620025fa708c620005f9708c620004ff764c620004fd764c620024fc764c6200057f754c6200a57c754c620005ef724c620005ec724c62001cff760c620024fe760c620004fd760c6200a57e750c6200057d750c62009dbe740c620005bd740c6200b6de630c620006dd630c620005e
  | 11 => 0xb7cc324c830004ff7558430014fe7558430004fd7558430014fc7558430004ff745843000cfe7458430004fd745843000cfc74584300067f54584300067d5458430004ff725843006cfc7258430026f77158430006f64158430006f541584300b6f731584300b6f43158430026fa3058430026f61058430026f41058430004fd768c43016e7e658c4300067d658c430004ff764c4300057f754c4300c57c754c43015e7e654c4300067d654c430005ef724c430005ec724c43006cff76c8430024fe76c8430004fd76c84301367e65c84300067d65c843006eee62c8430006ed62c843001cff7688430024fe7688430004fd768843012e7e65884300067d658843001ef66188430006f56188430004ff7648430004fd7648430024fc76484300057f75484300c57c754843011e7e65484300067d6548430005df73484300b5dc7348430006ee6248430006ed624843001ef66148430006f5614843001cff7608430024fe7608430004fd76084300c57e75084300057d75084301067e65084300067d65084300bdbe7408430005bd74084300b5de7308430005dd7308430025fa7008430005f97008430025fb764c030006fb764c030004fb764c0300077b754c03027778754c0300277a654c03002779654c030007bb744c03027fb8744c03027f7b544c03027f79544c030025fb734c030027db734c0300b6fa634c030027da634c0300b7da534c030277d9534c0300b7db324c030007d9324c030006f9614c03006cff75d8f20014fe75d8f2006e7e75d8f200147e75d8f20004fd75d8f2006e7d75d8f200047d75d8f2006cfc75d8f2006cff74d8f2000cfe74d8f2006ebe74d8f2000cbe74d8f20004fd74d8f2006ebd74d8f20004bd74d8f2006cfc74d8f200067f54d8f200067d54d8f2006eee72d8f2001cfe71d8f20004fd71d8f2006ef970d8f20004fd7698f200ad7e7598f200057d7598f2006edf6398f200b4ff7598f20014fe7598f200b67e7598f200147e7598f20004fd7598f200b67d7598f200047d7598f200b4fc7598f200b4ff7498f2000cfe7498f20004fd7498f200b4fc7498f200067f5498f200067d5498f20024fe7298f2006ede3298f2006edc3298f2001cfe7198f20004fd7198f2006edc6358f20004ff7558f20014fe7558f20004fd7558f20014fc7558f20004ff7458f2000cfe7458f20004fd7458f2000cfc7458f200067f5458f200067d5458f2006edf7358f20024fc7258f2006ede3258f2006edc3258f20004ff7158f2001cfc7158f2006cff7518f20014fe7518f20004fd7518f2006cfc7518f2006cff7418f2000cfe7418f20004fd7418f2006cfc7418f200067f5418f200067d5418f200b4fe7318f2006ede7318f2006eee7218f2001cfe7118f20004fd7118f2006ef97018f200ad7e75ccb200057d75c
  | 12 => 0xe720c530005ed720c530025fa700c530004fe76c8530004fd76c853006cfc76c85300067f65c85301367c65c8530006bf64c853010ebc64c8530006f761c853001ef461c8530004fe7688530004fd768853001cfc76885300067f658853012e7c6588530006bf6488530126bc6488530006ef6288530006ec6288530025fa7088530005f97088530004ff7648530004fe7648530004fc76485300057f75485300dd7c75485300067f654853011e7c6548530006bf6448530116bc6448530005df7348530005dc7348530004fe7608530004fd760853001cfc76085300dd7e75085300057d75085300067f65085301067c65085300d5be7408530005bd7408530006bf64085300febc6408530005de7308530005dd7308530006ef620853006eec6208530006f7610853001ef46108530025fa7008530005f970085300067f65cc1300f67c65cc130006bf64cc1300cebc64cc130025de73cc130026df63cc1300077b65cc13028f7865cc130007bb64cc130287b864cc1302877b54cc1302877954cc130025fa73cc130026fb63cc130027db63cc1300b7da43cc130287d943cc130005f971cc1300067f74594300047f74594300067e74594300067d74594300047d74594300067c74594300c67f73594300b67e73594300c67d73594300b67c73594300067f43594300b67e43594300067d43594300b67c43594300067f72594300067e72594300067d72594300067c72594300067f42594300067e42594300067d42594300067c42594300b67f32594300b67c32594300067f71594300067e71594300067d71594300067c71594300067f41594300067e41594300067d41594300067c41594300b67f31594300b67c31594300267f70594300267e70594300267d70594300267c70594300267f40594300267e40594300267d40594300267c40594300267f30594300267e30594300267d30594300267c30594300267f20594300267e20594300267d20594300267c20594300267f10594300267e10594300267d10594300267c105943006cff7598830014fe7598830004fd759883006cfc759883006cff749883000cfe7498830004fd749883006cfc74988300067f54988300067d5498830026ee729883006eee4298830006ed42988300b6ef329883006eec329883001cfe7198830004fd7198830026ee2098830026ec2098830004ff7558830014fe7558830004fd7558830014fc7558830004ff745883000cfe7458830004fd745883000cfc74588300067f54588300067d5458830026ef7258830006ee4258830006ed42588300b6ef32588300b6ec3258830004ff715883001cfc7158830026ee2058830026ec2058830004fd768c8300c57e758c8300057d758c8301ae7e658c8300067d658c830004ff764c8301a67e654c8300067d654c830
  | 13 => 0x9130296bc50d9130296be30d91300d6bd30d9130296bc30d9130296be20d9130296bc20d9130296be10d9130296bc10d91300067f65d89300067c65d8930006bf64d8930006bc64d8930004ff75d8930014fe75d8930004fd75d8930014fc75d8930004ff74d893000cfe74d8930004fd74d893000cfc74d89300067f54d89300067d54d893001cfe71d8930004fd71d89300dd7e75989300057d75989300067f65989300067c65989300d5be7498930005bd7498930006bf6498930006bc6498930006ef62989300057f75589300dd7c75589300067f65589300067c6558930005bf74589300d5bc7458930006bf6458930006bc6458930005f77158930005f471589300067f65189300067c6518930006bf6418930006bc6418930006ed621893006cff7518930014fe7518930004fd751893006cfc751893006cff741893000cfe7418930004fd741893006cfc74189300067f54189300067d541893001cfe7118930004fd7118930004fe76cc9300dd7e75cc9300057d75cc9300067f65cc9301b67c65cc930006bf64cc930196bc64cc930024fe768c9300dd7e758c9300057d758c9300067f658c9301ae7c658c930006bf648c93018ebc648c930006ef628c93006eec628c930025fa708c930005f9708c930024fc764c9300067f654c9301a67c654c930006bf644c93019ebc644c930006ef624c930006ec624c930005fb704c930025f8704c930004fe760c9300067f650c9301867c650c930006bf640c93017ebc640c930007cd320c9300067f65d85300067c65d8530006bf64d8530006bc64d8530004ff75d8530014fe75d8530004fd75d8530014fc75d8530004ff74d853000cfe74d8530004fd74d853000cfc74d85300067f54d85300067d54d853006cfe72d8530004fd72d85300dd7e75985300057d75985300067f65985300067c65985300d5be7498530005bd7498530006bf6498530006bc6498530006f761985300057f75585300dd7c75585300067f65585300067c6558530005bf74585300d5bc7458530006bf6458530006bc6458530005ef7258530005ec72585300067f65185300067c6518530006bf6418530006bc641853001ef66118530006f56118530004fe76cc5300067f65cc5301767c65cc530006bf64cc53014ebc64cc530024fe768c5300067f658c53016e7c658c530006bf648c530166bc648c530006f7618c53001ef4618c530025fa708c530005f9708c530024fc764c5300057f754c5300dd7c754c5300067f654c53015e7c654c530006bf644c530156bc644c530005ef724c530005ec724c530006f7614c53001ef4614c530005fb704c530025f8704c530004fe760c5300dd7e750c5300057d750c5300067f650c5301467c650c5300d5be740c530005bd740c530006bf640c53013ebc640c530005e
  | 14 => 0x25fa708c630005f9708c63001cff764c6300057f754c6300ed7c754c630005ef724c630005ec724c63001ef6614c630006f5614c630005fb704c630025f8704c6300ed7e750c6300057d750c6300e5be740c630005bd740c630005ee720c630005ed720c630025fa700c630005f9700c63006cff76c8630024fe76c8630004fd76c863001cff7688630024fe7688630004fd7688630006ee6288630006ed6288630025fa7088630005f97088630004ff7648630004fd7648630024fc76486300057f75486300ed7c7548630005df7348630005dc734863001cff7608630024fe7608630004fd76086300ed7e75086300057d75086300e5be7408630005bd7408630005de7308630005dd730863006eee6208630006ed6208630025fa7008630005f97008630025f976cc2300b6f976cc2302af7b54cc2302af7954cc230027da73cc2300b7da53cc2302a7d953cc230005f971cc2300dd7e76d95300de7e76d95300147e76d95300057f74d95300057d74d95300067f64d95300067e64d95300067d64d95300067c64d95300073c64d95300063c64d95300075e43d95300075d43d953029f5e30d953029f5c30d95300067f74d95300047f74d95300067e74d95300067d74d95300047d74d95300067c74d953029e7f73d95300de7e73d95300de7d73d95300de7c73d95300067f43d95300067e43d95300067d43d95300067c43d95300067f72d95300067e72d95300067d72d95300067c72d95300067f42d95300067e42d95300067d42d95300067c42d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95300067f70d953029e7e70d95300de7d70d953029e7c70d95300067f40d953029e7e40d95300067d40d953029e7c40d953029e7e30d95300de7d30d953029e7c30d953029e7e20d953029e7c20d953029e7e10d953029e7c10d95300d5be76d91300d6be76d913000cbe76d91300073f75d91300073c75d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d91302979f73d91300d79c73d91302979e30d91302979c30d9130006bf75d91300063f75d9130006be75d9130006bd75d9130006bc75d91300063c75d9130296bf73d91300d6be73d91300d6bd73d91300d6bc73d9130006bf53d9130006be53d9130006bd53d9130006bc53d9130006bf72d9130006be72d9130006bd72d9130006bc72d9130006bf52d9130006be52d9130006bd52d9130006bc52d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bd51d9130006bc51d9130006bf70d9130296be70d91300d6bd70d9130296bc70d9130006bf50d9130296be50d9130006bd50d
  | 15 => 0xf6298b3006cff7598b30014fe7598b3006e7e7598b300147e7598b30004fd7598b3006e7d7598b300047d7598b3006cfc7598b3006cff7498b3000cfe7498b30004fd7498b3006cfc7498b300067f5498b300067d5498b30024fe7398b300b6ef3298b3006eec3298b3001cfe7198b30004fd7198b300b6ec6258b30004ff7558b30014fe7558b30004fd7558b30014fc7558b30004ff7458b3000cfe7458b30004fd7458b3000cfc7458b300067f5458b300067d5458b30024fc7358b300b6ef3258b300b6ec3258b30004ff7158b3001cfc7158b300f57e758cb300057d758cb300b7cc324cb300b6f7619873001ef461987300057f75587300f57c75587300b6f46158730004ff75587300067f75587300047f7558730014fe7558730004fd7558730014fc75587300067c75587300147c7558730004ff745873000cfe7458730004fd745873000cfc74587300067f54587300067d5458730024fc7358730004ff725873006cfc72587300b6f731587300b6f431587300057f754c7300f57c754c730005ef724c730005ec724c73006cff76c87300b4fe76c8730004fd76c873006eee62c8730006ed62c873001cff76887300b4fe7688730004fd7688730004ff7648730004fd76487300b4fc76487300057f75487300f57c7548730005df73487300b5dc7348730006ee6248730006ed624873001cff76087300b4fe7608730004fd76087300f57e75087300057d75087300cdbe7408730005bd74087300b5de7308730005dd7308730025fa7008730005f9700873006cff7598a30014fe7598a30004fd7598a3006cfc7598a3006cff7498a3000cfe7498a30004fd7498a3006cfc7498a300067f5498a300067d5498a30026ee7298a3006eee5298a30006ed5298a3006eee4298a30006ed4298a3001cfe7198a30004fd7198a30026ee2098a30026ec2098a30004ff7558a300067f7558a300047f7558a30014fe7558a30004fd7558a30014fc7558a300067c7558a300147c7558a30004ff7458a3000cfe7458a30004fd7458a3000cfc7458a300067f5458a300067d5458a30026ef7258a30006ee5258a30006ed5258a30006ee4258a30006ed4258a30004ff7158a3001cfc7158a30026ee2058a30026ec2058a30026fa1058a300ed7e75cca300057d75cca300ed7e758ca300057d758ca3006eee628ca30006ed628ca30025fa708ca30005f9708ca30006ee624ca30006ed624ca30005fb704ca30025f8704ca30007cd320ca30004ff7558630014fe7558630004fd7558630014fc7558630004ff745863000cfe7458630004fd745863000cfc74586300067f54586300067d5458630004ff725863006cfc7258630026f77158630006f64158630006f54158630026f61058630026f41058630025f870cc63001ef6618c630006f5618c630
  | 16 => 0xc8212c7cc310c82106fea600c82106fe9600c82101df77648421006f77648421004f776484210077775484212bf74754842101f76654842101f75654842101fb6644842101fb564484212b77754484212b7755448421007d77348421007d4734842101fd6634842101fd5634842101df7724842101fe7724842106ef6624842101fe6624842106fe642484212b7e5424842101ff2604842101ff16048421026fb7598021026fa7598021026f97598021026f87598021026fb7498021026fa7498021026f97498021026f87498021006fb54980210067b5498021006fa5498021006f95498021006795498021006f85498021026fb7398021026fa7398021026f97398021026f87398021006fb5398021006fa5398021006f95398021006f85398021006fb4398021006fa4398021006f94398021006f84398021026f87298021006fb529802106efa5298021006f9529802106ef85298021006fb429802106efa4298021006f9429802106ef84298021006fb329802106efa3298021006f9329802106ef83298021026fb7198021026fa7198021026f97198021026f8719802101efb519802101efa519802101ef9519802101ef8519802101efb419802101efa419802101ef9419802101ef8419802101efb319802101efa319802101ef9319802101ef8319802101efb219802101efa219802101ef9219802101ef82198021004ff7558021014fe7558021004fd7558021014fc7558021004ff745802100cfe7458021004fd745802100cfc74580210067f54580210067d5458021004ff73580210b4fc735802101efb7058021006fb5058021006fa5058021006f95058021006f85058021006fb4058021006fa4058021006f94058021006f8405802106efb205802106ef8205802101efb105802101ef81058021006fb7558021006fa7558021006f97558021006f87558021006fb7458021006fa7458021006f97458021006f87458021006fb54580210067b5458021006fa5458021006f95458021006795458021006f85458021006fb7358021006fa7358021006f97358021006f87358021006fb5358021006fa5358021006f95358021006f85358021006fb4358021006fa4358021006f94358021006f8435802106efa7258021006fb525802106efa5258021006f9525802106ef85258021006fb425802106efa4258021006f9425802106ef84258021006fb325802106efa3258021006f9325802106ef8325802101efb715802101efa715802101ef8715802101efb515802101efa515802101ef9515802101ef8515802101efb415802101efa415802101ef9415802101ef8415802101efb315802101efa315802101ef9315802101ef8315802101efb215802101efa215802101ef9215802101ef821580210f57e7598b300057d7598b300b6e
  | 17 => 0x6dc5098c21006df4098c21006de4098c21006dd4098c21006dc4098c2106edf2098c2106edc2098c2101edf1098c2101ede1098c2101edd1098c2101edc1098c21004ff7558c21014fe7558c21004fd7558c21014fc7558c21004ff7458c2100cfe7458c21004fd7458c2100cfc7458c210067f5458c210067d5458c2101cff7358c2101edf7358c21006df5358c21006de5358c21006dd5358c21006dc5358c21006df4358c21006de4358c21006dd4358c21006dc4358c2106cfe7258c2106cfc7258c21006ec7258c2106ede3258c2106edc3258c2101cfe7158c2101cfc7158c2101ede3158c2101edc3158c2101eef2158c2101eed2158c21004ff7058c21024fc7058c21006df7558c21006de7558c21006dd7558c21006dc7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c210065f5458c21006de5458c21006dd5458c210065d5458c21006dc5458c2106ede7258c2106edc7258c21006cc7258c21006df5258c2106ede5258c21006dd5258c2106edc5258c21006df4258c2106ede4258c21006dd4258c2106edc4258c2101edf7158c2101ede7158c2101edd7158c2101edc7158c2101edf5158c2101ede5158c2101edd5158c2101edc5158c2101edf4158c2101ede4158c2101edd4158c2101edc4158c2101edf2158c2101ecf2158c2101ede2158c2101edd2158c2101ecd2158c2101edc2158c21006df7058c21006de7058c21006dd7058c21006dc7058c21006df5058c21006de5058c21006dd5058c21006dc5058c21006df4058c21006de4058c21006dd4058c21006dc4058c2106edf2058c2106edc2058c2101edf1058c2101ede1058c2101edd1058c2101edc1058c21004fd76cc8211057e75cc8210057d75cc8211b67e65cc8210067d65cc821196be64cc821006bd64cc8210b6de63cc821006dd63cc8212cded76cc821006ed76cc821004ed76cc8212ef6e75cc8210076d75cc8212cf6e65cc8212cf6d65cc8212cfae64cc8212cfad64cc8212e76f54cc8212e76d54cc82106dee73cc8212ceef63cc8212cfce63cc821006ed63cc8212cfcd63cc821006cd63cc8212cdef71cc8212cded71cc8212ceee61cc8212cfe661cc8212cfcf31cc8212cfcd31cc8212cfea60cc8212cfe960cc821004ff764c8211a67e654c8210067d654c82119ebe644c821006bd644c821006de634c821006dd634c8212deee624c82106fcc324c82106ded760c82106eed760c821004ed760c82106f6e650c82106f6d650c82106fae640c82106fad640c8212d76f540c8212d76d540c8212cdee730c82106fce730c82106eef630c82106fce630c821006ed630c82106fcd630c821006cd630c82106def710c82106fe6710c8212c5ed710c82106fe5710c8212c6ee610c82106fe6610c8212c7ce310
  | 18 => 0xf725942106e7e72594211067d725942106e7c72594210067f425942106e7e42594210067d425942106e7c425942106e7e325942106e7c325942101e7f715942101e7e715942101e7d715942101e7c715942101e7f415942101e7e415942101e7d415942101e7c415942101e7f315942101e7e315942101e7d315942101e7c315942101e7f215942101e7e215942101e7d215942101e7c21594210067f70594210067e70594210067d70594210067c70594210067f40594210067e40594210067d40594210067c405942106e7f205942106e7c205942101e7f105942101e7e105942101e7d105942101e7c1059421006bf7559021006be75590210063e7559021006bd75590210063d7559021006bc7559021006bf7359021006be7359021006bd7359021006bc7359021006bf5359021006be5359021006bd5359021006bc53590210febf725902106ebe72590210febd725902106ebc7259021006bf525902106ebe5259021006bd525902106ebc525902106ebe325902106ebc325902101ebf715902101ebe715902101ebd715902101ebc715902101ebf515902101ebe515902101ebd515902101ebc515902101ebf315902101ebe315902101ebd315902101ebc315902101ebf215902101ebe215902101ebd215902101ebc2159021006bf7059021006be7059021006bd7059021006bc7059021006bf5059021006be5059021006bd5059021006bc505902106ebf205902106ebc205902101ebf105902101ebe105902101ebd105902101ebc10590210b4ff7598c21014fe7598c21004fd7598c210b4fc7598c210b4ff7498c2100cfe7498c21004fd7498c210b4fc7498c210067f5498c210067d5498c2101cfe7398c2101ede7398c21006df5398c210b6de5398c21006dd5398c210b6dc5398c21006df4398c210b6de4398c21006dd4398c210b6dc4398c2106cfe7298c2106cfc7298c2106ede3298c2106edc3298c2101cfe7198c2101cfc7198c2101ede3198c2101edc3198c21024fe7098c21004fd7098c210b6df7598c21006de7598c21006dd7598c210b6dc7598c210b6df7498c21006de7498c21006dd7498c210b6dc7498c21006df5498c210065f5498c21006de5498c21006dd5498c210065d5498c21006dc5498c2106ede7298c2106edc7298c21006df5298c2106ede5298c21006dd5298c2106edc5298c21006df4298c2106ede4298c21006dd4298c2106edc4298c2101edf7198c2101ede7198c2101edd7198c2101edc7198c2101edf5198c2101ede5198c2101edd5198c2101edc5198c2101edf4198c2101ede4198c2101edd4198c2101edc4198c2101edf2198c2101ede2198c2101edd2198c2101edc2198c210b6df7098c21006de7098c21006dd7098c210b6dc7098c21006df5098c21006de5098c21006dd5098c21
  | 19 => 0x8d21006de5018d21006dd5018d21006dc5018d21006df4018d21006de4018d21006dd4018d21006dc4018d212c6df1018d212c6dc1018d2101cfe76cc92111d7e75cc9210057d75cc9210067f65cc9211b67c65cc921006df63cc9210b6dc63cc92101df671cc921005f571cc921004fe768c92111d7e758c9210057d758c9210067f658c9211ae7c658c921006df638c921006dc638c921005ee768c921006ee768c921004ee768c9213376e758c9210076d758c9210076f658c9213376c658c92132f6f548c92132f6d548c921325ed738c921007cf638c9210b6ee638c9210b6ec638c921007cc638c921006cc638c92101dee718c92101dec718c92106eef618c92131fce318c92131fcc318c92101cfc764c9210067f654c9211a67c654c921006df634c921006dc634c921005f7714c92101df4714c92101dec764c921006ec764c92101cec764c9210076f654c9213176c654c92130f6f544c92130f6d544c921007cf734c921007cf634c9210b6ee634c9210b6ec634c921007cc634c921006cc634c921007e7714c92101dee714c92101dec714c921007e4714c921004fe760c9210067f650c9211867c650c921006df630c9210b6dc630c921305ee720c921007cd320c921004fe76cc5210067f65cc5211767c65cc521006df63cc5210b6dc63cc521005ee72cc521005ed72cc521007cd32cc5210b4ff764c521004fd764c521004fc764c5210057f754c52111d7c754c5210067f654c52115e7c654c521006df634c521006dc634c521005ef724c521005ec724c521007cd324c5210067f65c85211367c65c8521006df63c8521006dc63c852101dee72c852101eef62c85210077765c85212ff7465c85212f77754c85212f77554c8521007d763c8521007d463c852101df672c852101ef762c852101fe762c852106fe632c8521007e532c85210067f65d81210067c65d8121006df63d8121006dc63d8121004ff75d8121014fe75d8121004fd75d8121014fc75d8121004ff74d812100cfe74d8121004fd74d812100cfc74d81210067f54d81210067d54d81210b4fe73d8121004fd73d8121006fb40d8121006f840d812111d7e75981210057d75981210067f65981210067c6598121005de7398121005dd7398121006df6398121006dc6398121006fb60981210057f755812111d7c75581210067f65581210067c6558121005bf7458121115bc7458121005df7358121005dc7358121006df6358121006dc63581210067f65181210067c6518121006df6318121006dc6318121026fa6018121006f960181210067f74594210047f74594210067e74594210067d74594210047d74594210067c74594210067f73594210067e73594210067d73594210067c73594210067f43594210067e43594210067d43594210067c43594211067
  | 20 => 0x6dd51d8d2131edc51d8d21006df41d8d2131ede41d8d21006dd41d8d2131edc41d8d2131ede21d8d2131edc21d8d21006df70d8d21006de70d8d21006dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006df40d8d21006de40d8d21006dd40d8d21006dc40d8d2131edf10d8d2131edc10d8d2111d7e7598d210057d7598d210067f6598d210067c6598d21006df6398d210b4ff7598d21014fe7598d210b67e7598d210147e7598d21004fd7598d210b67d7598d210047d7598d210b4fc7598d210b4ff7498d2100cfe7498d21004fd7498d210b4fc7498d210067f5498d210067d5498d210b4fe7398d21004de7398d21004fd7298d210b6ed7298d21004fd7198d210b6f57198d212ceee2198d21024fe7098d21004fd7098d210057f7558d2111d7c7558d210067f6558d210067c6558d21004ff7558d210067f7558d210047f7558d21014fe7558d21004fd7558d21014fc7558d210067c7558d210147c7558d21004ff7458d2100cfe7458d21004fd7458d2100cfc7458d210067f5458d210067d5458d21006df7358d21004ff7258d21006ef7258d21004ef7258d21004ff7158d21006f77158d21004ff7058d21024fc7058d21004fe7618d210067f6518d210067c6518d21006dd6318d210b4ff7518d21014fe7518d21004fd7518d210b4fc7518d210b4ff7418d2100cfe7418d21004fd7418d210b4fc7418d210067f5418d210067d5418d210b6de7318d21006df5318d210b6de5318d21006dd5318d210b6dc5318d21006df4318d210b6de4318d21006dd4318d210b6dc4318d210b6ed7218d212c6ee2118d212c6ec2118d21024fe7018d21004fd7018d21005de7618d21006de7618d21004de7618d21006df6518d210075f6518d210065f6518d21006de6518d21006dd6518d21006dc6518d210075c6518d210065c6518d21006df6418d21006de6418d21006dd6418d21006dc6418d210075f5418d210075d5418d21007cd7218d212c7ce2118d212c7cc2118d210b6df7518d21006de7518d21006dd7518d210b6dc7518d210b6df7418d21006de7418d21006dd7418d210b6dc7418d21006df5418d210065f5418d21006de5418d21006dd5418d210065d5418d21006dc5418d210b6df7218d21006dd7218d21006cd7218d21006df5218d21006de5218d21006dd5218d21006dc5218d21006df4218d21006de4218d21006dd4218d21006dc4218d210b6df7118d212c6de7118d21006dd7118d210b6dc7118d21006df5118d212c6de5118d21006dd5118d212c6dc5118d21006df4118d212c6de4118d21006dd4118d212c6dc4118d212c6de2118d212c6ce2118d21006dd2118d212c6dc2118d212c6cc2118d210b6df7018d21006de7018d21006dd7018d210b6dc7018d21006df501
  | 21 => 0xd758ca2131edf638ca2131edc638ca21006de634ca21006dd634ca21005f7714ca2101df4714ca212c6df630ca210b6dc630ca21007cd320ca212c5ed760ca21006ed760ca213576f540ca213576d540ca21007ce730ca212c6ef630ca212c7cf630ca212c6cf630ca21006ed630ca212c7cc630ca212c5ef710ca212c5ed710ca212c7ce310ca212c7cc310ca2101df576c862106ef576c862134f7754c862134f7554c862101fe672c862106fe652c8621347e552c8621004ff7558221014fe7558221004fd7558221014fc7558221004ff745822100cfe7458221004fd745822100cfc74582210067f54582210067d5458221004ff73582210b4fc735822101efb705822101efb105822101ef8105822111d7e76d952111e7e76d95210147e76d95210057f74d95210057d74d95210067f64d95210067e64d95210067d64d95210067c64d952133f6e21d952133f6c21d95210067f74d95210047f74d95210067e74d95210067d74d95210047d74d95210067c74d95210067f73d95210067e73d95210067d73d95210067c73d95210067f43d95210067e43d95210067d43d95210067c43d952133e7f72d952111e7e72d952111e7d72d952111e7c72d95210067f42d95210067e42d95210067d42d95210067c42d95210067f71d952133e7e71d952111e7d71d952133e7c71d95210067f41d952133e7e41d95210067d41d952133e7c41d952133e7e31d952133e7c31d952133e7e21d952111e7d21d952133e7c21d95210067f70d95210067e70d95210067d70d95210067c70d95210067f40d95210067e40d95210067d40d95210067c40d952133e7f10d952133e7c10d95210067f65d8d210067c65d8d21004ff75d8d21014fe75d8d21004fd75d8d21014fc75d8d21004ff74d8d2100cfe74d8d21004fd74d8d2100cfc74d8d210067f54d8d210067d54d8d21006df53d8d21006de53d8d21006dd53d8d21006dc53d8d21006df43d8d21006de43d8d21006dd43d8d21006dc43d8d21024fe70d8d21004fd70d8d21006df65d8d210075f65d8d210065f65d8d21006de65d8d21006dd65d8d21006dc65d8d210075c65d8d210065c65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d210075f54d8d210075d54d8d2131fcf72d8d2131fce21d8d2131fcc21d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d210065f54d8d21006de54d8d21006dd54d8d210065d54d8d21006dc54d8d2131edf72d8d21006dd72d8d21006df52d8d21006de52d8d21006dd52d8d21006dc52d8d21006df42d8d21006de42d8d21006dd42d8d21006dc42d8d21006df71d8d2131ede71d8d21006dd71d8d2131edc71d8d21006df51d8d2131ede51d8d21
  | 22 => 0x8f21014fc7558f21004ff7458f2100cfe7458f21004fd7458f2100cfc7458f210067f5458f210067d5458f2106edf7358f2101cfc7258f2106ede3258f2106edc3258f21004ff7058f21024fc7058f2106cff7518f21014fe7518f21004fd7518f2106cfc7518f2106cff7418f2100cfe7418f21004fd7418f2106cfc7418f210067f5418f210067d5418f210b4fe7318f2106ede7318f2106eee7218f2106ef57118f212c6de3118f210b6dc3118f21024fe7018f21004fd7018f211357e75ccb210057d75ccb2106edf63ccb2106edc63ccb2101ded768cb2106eed768cb2101ced768cb2106f6e758cb2106f6d758cb2136f6f548cb2136f6d548cb210b6ee638cb2106fce638cb2106fcd638cb2106eec638cb2101dee718cb2106fe6718cb2106fe5718cb2101dec718cb2131fce318cb2131fcc318cb2106edf634cb2106edc634cb2106fcc324cb21005ef764cb21006ef764cb212df6f544cb212df6d544cb2106fcf734cb2106fcf634cb210b6ee634cb210b6ec634cb2106fcc634cb21006cc634cb2101dee714cb2101dec714cb210b6de63cc721006dd63cc72106dee72cc721005ed72cc721007cd32cc7210057f754c7211357c754c721006de634c721006dd634c721005ef724c72106dec724c721007cd324c72106efb6098321026f860983210057f75583211357c7558321005bf745832110dbc745832106ef86058321004ff75583210067f75583210047f7558321014fe7558321004fd7558321014fc75583210067c75583210147c7558321004ff7458321006bf7458321004bf745832100cfe7458321004fd745832100cfc7458321006bc745832100cbc74583210067f54583210067d5458321004ff73583210b4fc735832101cfc725832106efb205832106ef820583210b4ff7598e21014fe7598e21004fd7598e210b4fc7598e210b4ff7498e2100cfe7498e21004fd7498e210b4fc7498e210067f5498e210067d5498e2101ede7398e2101cfe7198e2101ede3198e2101edc3198e21024fe7098e21004fd7098e21004ff7558e210067f7558e210047f7558e21014fe7558e21004fd7558e21014fc7558e210067c7558e210147c7558e21004ff7458e2100cfe7458e21004fd7458e2100cfc7458e210067f5458e210067d5458e2101edf7358e21006ef7258e2101cfc7158e2101ede3158e2101edc3158e2101eef2158e2101eed2158e21004ff7058e21024fc7058e2112d7e75cca210057d75cca210b6de63cca21006dd63cca2101df671cca21005f571cca212cded76cca21006ed76cca213676e75cca210076d75cca2135f6f54cca2135f6d54cca212ceef63cca212cfce63cca21006ed63cca212cfcd63cca212cfe671cca212cded71cca21007e571cca212cfcf31cca212cfcd31cca2112d7e758ca210057
  | 23 => 0x6f943980310b6f84398031026fb7298031026fa7298031026f97298031026f87298031006fb5298031006fa5298031006f95298031006f85298031006fb4298031006fa4298031006f94298031006f842980310b6fb3298031006fa3298031006f932980310b6f83298031026fb7198031026fa7198031026f97198031026f8719803101efb519803101efa519803101ef9519803101ef8519803101efb419803101efa419803101ef9419803101ef8419803101efb319803101efa319803101ef9319803101ef8319803101efb219803101efa219803101ef9219803101ef82198031004ff7558031014fe7558031004fd7558031014fc7558031004ff745803100cfe7458031004fd745803100cfc74580310067f54580310067d5458031004ff725803106cfc725803101efb7058031006fb5058031006fa5058031006f95058031006f85058031006fb4058031006fa4058031006f94058031006f840580310b6fb30580310b6f8305803101efb105803101ef81058031006fb7558031006fa7558031006f97558031006f87558031006fb7458031006fa7458031006f97458031006f87458031006fb54580310067b5458031006fa5458031006f95458031006795458031006f854580310b6fa7358031006fb53580310b6fa5358031006f953580310b6f85358031006fb43580310b6fa4358031006f943580310b6f84358031006fb7258031006fa7258031006f97258031006f87258031006fb5258031006fa5258031006f95258031006f85258031006fb4258031006fa4258031006f94258031006f842580310b6fb3258031006fa3258031006f932580310b6f8325803101efb715803101efa715803101ef8715803101efb515803101efa515803101ef9515803101ef8515803101efb415803101efa415803101ef9415803101ef8415803101efb315803101efa315803101ef9315803101ef8315803101efb215803101efa215803101ef9215803101ef8215803106cff75d8f21014fe75d8f2106e7e75d8f210147e75d8f21004fd75d8f2106e7d75d8f210047d75d8f2106cfc75d8f2106cff74d8f2100cfe74d8f21004fd74d8f2106cfc74d8f210067f54d8f210067d54d8f2106eee72d8f2106ef571d8f2131ede31d8f2131edc31d8f21024fe70d8f21004fd70d8f21004fd7698f211357e7598f210057d7598f2106edf6398f210b4ff7598f21014fe7598f210b67e7598f210147e7598f21004fd7598f210b67d7598f210047d7598f210b4fc7598f210b4ff7498f2100cfe7498f21004fd7498f210b4fc7498f210067f5498f210067d5498f2101cfe7298f210b6ee7298f2106ede3298f2106edc3298f212ceee2198f212ceec2198f21024fe7098f21004fd7098f2106edc6358f21004ff7558f21014fe7558f21004fd755
  | 24 => 0xc5258831006ef4258831006ee4258831006ed4258831006ec42588310b6ef32588310b6ec325883101edf315883101edd315883101eee215883101eec2158831004ff7058831024fc7058831006ef7558831006ee7558831006ed7558831006ec7558831006ef7458831006ee7458831006ed7458831006ec7458831006ef54588310066f5458831006ee5458831006ed54588310066d5458831006ec54588310b6ee7358831006ef53588310b6ee5358831006ed53588310b6ec5358831006ef43588310b6ee4358831006ed43588310b6ec435883101eef715883101eee715883101eec715883101eef515883101eee515883101eed515883101eec515883101eef415883101eee415883101eed415883101eec415883101eef315883101ecf315883101eee315883101eed315883101ecd315883101eec3158831006ef7058831006ee7058831006ed7058831006ec7058831006ef5058831006ee5058831006ed5058831006ec5058831006ef4058831006ee4058831006ed4058831006ec40588310b6ef30588310b6ec305883101eef105883101eee105883101eed105883101eec1058831004fd768c8311457e758c8310057d758c8311ae7e658c8310067d658c83118ebe648c831006bd648c831006ed628c83131ddd768c831006dd768c831004dd768c83139f5e758c8310075d758c83131f5e658c83131f5d658c83131f9e648c83131f9d648c8313975f548c8313975d548c8310b5de728c83131fce628c831006dd628c83131fcd628c831006cd628c83131ddd718c83131ede618c83131fd6618c83131fda608c83131fd9608c831004ff764c8311a67e654c8310067d654c83119ebe644c831006bd644c83138ede634c831006ee624c8310b7cc324c8310b75e650c8310b75d650c8310b79e640c8310b79d640c8313875f540c8313875d540c83131dde720c8310b7ce720c8310b7ce620c831006dd620c8310b7cd620c831006cd620c8310b7d6710c8312c5dd710c8310b7d5710c8312c6de610c8310b7d6610c8310b7da600c8310b7d9600c83101df7764c431006f7764c431004f7764c43100777754c43137f74754c43101f76654c43101f75654c43101fb6644c43101fb5644c43137777544c43137775544c43101df7734c43101fd7734c4310b6f6634c43101fd6634c4310b7d6434c431377d5434c431007e7724c431007e4724c43101fe6624c43101fe5624c43101ff2604c43101ff1604c431026fb7598031026fa7598031026f97598031026f87598031026fb7498031026fa7498031026f97498031026f87498031006fb54980310067b5498031006fa5498031006f95498031006795498031006f85498031026f87398031006fb53980310b6fa5398031006f953980310b6f85398031006fb43980310b6fa4398031
  | 25 => 0x943101e7e315943101e7d315943101e7c315943101e7f215943101e7e215943101e7d215943101e7c21594310067f70594310067e70594310067d70594310067c70594310067f40594310067e40594310067d40594310067c40594310b67f30594310b67c305943101e7f105943101e7e105943101e7d105943101e7c1059431006bf7559031006be75590310063e7559031006bd75590310063d7559031006bc755903113ebf73590310b6be735903113ebd73590310b6bc7359031006bf53590310b6be5359031006bd53590310b6bc5359031006bf7259031006be7259031006bd7259031006bc7259031006bf5259031006be5259031006bd5259031006bc52590310b6bf32590310b6bc325903101ebf715903101ebe715903101ebd715903101ebc715903101ebf515903101ebe515903101ebd515903101ebc515903101ebf315903101ebe315903101ebd315903101ebc315903101ebf215903101ebe215903101ebd215903101ebc2159031006bf7059031006be7059031006bd7059031006bc7059031006bf5059031006be5059031006bd5059031006bc50590310b6bf30590310b6bc305903101ebf105903101ebe105903101ebd105903101ebc105903106cff7598831014fe7598831004fd759883106cfc759883106cff749883100cfe7498831004fd749883106cfc74988310067f54988310067d549883101eee7298831006ef529883106eee5298831006ed529883106eec5298831006ef429883106eee4298831006ed429883106eec42988310b6ef329883106eec329883101eee219883101eec2198831024fe7098831004fd709883106eef7598831006ee7598831006ed759883106eec759883106eef7498831006ee7498831006ed749883106eec7498831006ef54988310066f5498831006ee5498831006ed54988310066d5498831006ec549883106eec7398831006ef53988310b6ee5398831006ed53988310b6ec5398831006ef43988310b6ee4398831006ed43988310b6ec439883101eee719883101eed719883101eec719883101eef519883101eee519883101eed519883101eec519883101eef419883101eee419883101eed419883101eec419883101eef319883101eee319883101eed319883101eec319883106eef7098831006ee7098831006ed709883106eec7098831006ef5098831006ee5098831006ed5098831006ec5098831006ef4098831006ee4098831006ed4098831006ec40988310b6ef30988310b6ec309883101eef109883101eee109883101eed109883101eec1098831004ff7558831014fe7558831004fd7558831014fc7558831004ff745883100cfe7458831004fd745883100cfc74588310067f54588310067d545883101eef7258831006ef5258831006ee5258831006ed5258831006e
  | 26 => 0x2c6ee31189312c6ce3118931006ed31189312c6ec31189312c6cc311893106eef7018931006ee7018931006ed701893106eec7018931006ef5018931006ee5018931006ed5018931006ec5018931006ef4018931006ee4018931006ed4018931006ec40189312c6ef10189312c6ec1018931004fe76cc93115d7e75cc9310057d75cc9310067f65cc9311b67c65cc931006ec62cc931005de76cc931006de76cc931004de76cc9313df5e75cc9310075d75cc9310075f65cc9313df5c65cc9313d75f54cc9313d75d54cc931007cf62cc93106edc62cc931007cc62cc931006cc62cc93101dde71cc93101ddc71cc9310b6df61cc93101cfe768c93115d7e758c9310057d758c9310067f658c9311ae7c658c9313cddd738c931006ef628c93106eec628c93101df6718c931005f5718c93101cfc764c9310067f654c9311a67c654c931006ef624c931006ec624c931005f7714c93101df4714c93101cdc764c9310075f654c9313c75c654c9313bf5f544c9313bf5d544c931007cf724c931007cf624c93106edc624c931007cc624c931006cc624c931007d7714c93101dde714c93101ddc714c931007d4714c931004fe760c9310067f650c9311867c650c9313b5de730c931006ef620c931007cd320c9310067f65cc5311767c65cc53101dde73cc53101edf63cc531006ef62cc531006ec62cc5310077765cc5313af7465cc5313a77754cc5313a77554cc53101df673cc53101ef763cc53101fd763cc531007e762cc531007e462cc5310b7d732cc531007d532cc5310067f65d81310067c65d8131006ef62d8131006ec62d8131004ff75d8131014fe75d8131004fd75d8131014fc75d8131004ff74d813100cfe74d8131004fd74d813100cfc74d81310067f54d81310067d54d813106cfe72d8131004fd72d8131006fb40d8131006f840d813115d7e75981310057d75981310067f65981310067c6598131005ee7298131005ed7298131006ef6298131006ec6298131006fb60981310057f755813115d7c75581310067f65581310067c6558131005bf7458131155bc7458131005ef7258131005ec7258131006ef6258131006ec62581310067f65181310067c6518131006ef6218131006ec6218131026fa6018131006f960181310067f74594310047f74594310067e74594310067d74594310047d74594310067c74594311467f73594310b67e73594311467d73594310b67c73594310067f43594310b67e43594310067d43594310b67c43594310067f72594310067e72594310067d72594310067c72594310067f42594310067e42594310067d42594310067c42594310b67f32594310b67c325943101e7f715943101e7e715943101e7d715943101e7c715943101e7f415943101e7e415943101e7d415943101e7c415943101e7f315
  | 27 => 0xc75d8931004ff74d893100cfe74d8931004fd74d893100cfc74d89310067f54d89310067d54d8931006ef52d8931006ee52d8931006ed52d8931006ec52d8931006ef42d8931006ee42d8931006ed42d8931006ec42d8931024fe70d8931004fd70d8931006ef65d89310076f65d89310066f65d8931006ee65d8931006ed65d8931006ec65d89310076c65d89310066c65d8931006ef64d8931006ee64d8931006ed64d8931006ec64d89310076f54d89310076d54d89312cfcf73d89312cfce31d89312cfcc31d8931006ef75d8931006ee75d8931006ed75d8931006ec75d8931006ef74d8931006ee74d8931006ed74d8931006ec74d8931006ef54d89310066f54d8931006ee54d8931006ed54d89310066d54d8931006ec54d89312ceef73d8931006ef53d8931006ee53d8931006ed53d8931006ec53d8931006ef43d8931006ee43d8931006ed43d8931006ec43d8931006ef71d89312ceee71d8931006ed71d8931006ef51d89312ceee51d8931006ed51d89312ceec51d8931006ef41d89312ceee41d8931006ed41d89312ceec41d89312ceee31d89312ceec31d8931006ef70d8931006ee70d8931006ed70d8931006ec70d8931006ef50d8931006ee50d8931006ed50d8931006ec50d8931006ef40d8931006ee40d8931006ed40d8931006ec40d89312ceef10d89312ceec10d893115d7e75989310057d75989310067f65989310067c6598931006ef62989310057f755893115d7c75589310067f65589310067c65589310067f65189310067c6518931006ed621893106cff7518931014fe7518931004fd751893106cfc751893106cff741893100cfe7418931004fd741893106cfc74189310067f54189310067d5418931006ef521893106eee5218931006ed521893106eec5218931006ef421893106eee4218931006ed421893106eec42189312c6de31189312c6dc3118931024fe7018931004fd7018931005ee7618931006ee7618931006ef65189310076f65189310066f6518931006ee6518931006ed6518931006ec65189310076c65189310066c6518931006ef6418931006ee6418931006ed6418931006ec64189310076f54189310076d5418931007cd73189312c7ce31189312c7cc311893106eef7518931006ee7518931006ed751893106eec751893106eef7418931006ee7418931006ed741893106eec7418931006ef54189310066f5418931006ee5418931006ed54189310066d5418931006ec541893106eef7318931006ef5318931006ee5318931006ed5318931006ec5318931006ef4318931006ee4318931006ed4318931006ec431893106eef71189312c6ee7118931006ed7118931006ef51189312c6ee5118931006ed51189312c6ec5118931006ef41189312c6ee4118931006ed41189312c6ec4118931
  | 28 => 0x8331004fd7558331014fc75583310067c75583310147c7558331004ff7458331006bf7458331004bf745833100cfe7458331004fd745833100cfc7458331006bc745833100cbc74583310067f54583310067d545833101cfc7358331004ff725833106cfc72583310b6fb30583310b6f8305833106cff7598a31014fe7598a31004fd7598a3106cfc7598a3106cff7498a3100cfe7498a31004fd7498a3106cfc7498a310067f5498a310067d5498a3101eee7298a3101eee2198a3101eec2198a31024fe7098a31004fd7098a31004ff7558a310067f7558a310047f7558a31014fe7558a31004fd7558a31014fc7558a310067c7558a310147c7558a31004ff7458a3100cfe7458a31004fd7458a3100cfc7458a310067f5458a310067d5458a3101eef7258a3101edf3158a3101edd3158a3101eee2158a3101eec2158a31004ff7058a31024fc7058a3116d7e75cca310057d75cca3116d7e758ca310057d758ca3106eee628ca31006ed628ca3101df6718ca31005f5718ca3140f5e758ca310075d758ca314075f548ca314075d548ca3131fce628ca31006dd628ca3131fcd628ca3131fd6718ca3131ddd718ca31007d5718ca31006ee624ca31006ed624ca31005f7714ca3101df4714ca31007cd320ca312c5dd760ca31006dd760ca313ff5f540ca313ff5d540ca31007ce720ca312c7cf620ca31006dd620ca312c7cc620ca312c5dd710ca3101df576cc6310b6f576cc6313f77754cc6313f77554cc63101fd673cc6310b7d653cc6313efd553cc631004ff7558231014fe7558231004fd7558231014fc7558231004ff745823100cfe7458231004fd745823100cfc74582310067f54582310067d5458231004ff725823106cfc725823101efb705823101efb105823101ef8105823115d7e76d953115e7e76d95310147e76d95310057f74d95310057d74d95310067f64d95310067e64d95310067d64d95310067c64d95313e75e31d95313e75c31d95310067f74d95310047f74d95310067e74d95310067d74d95310047d74d95310067c74d95313e67f73d953115e7e73d953115e7d73d953115e7c73d95310067f43d95310067e43d95310067d43d95310067c43d95310067f72d95310067e72d95310067d72d95310067c72d95310067f42d95310067e42d95310067d42d95310067c42d95310067f71d95313e67e71d953115e7d71d95313e67c71d95310067f41d95313e67e41d95310067d41d95313e67c41d95313e67e31d953115e7d31d95313e67c31d95313e67e21d95313e67c21d95310067f70d95310067e70d95310067d70d95310067c70d95310067f40d95310067e40d95310067d40d95310067c40d95313e67f10d95313e67c10d95310067f65d89310067c65d8931004ff75d8931014fe75d8931004fd75d8931014f
  | 29 => 0x427cf514c832427ce514c832427cd514c832427cc514c83241fcf414c83241fce414c83241fcd414c83241fcc414c832007cf704c832007ce704c832007cd704c832007cc704c83206fcf604c83206fcc604c832427cf504c832427ce504c832427cd504c832427cc504c83241fcf404c83241fce404c83241fcd404c83241fcc404c832007cd329843206ef7619843201ef461984320057f75584321857c7558432007cd325843206ef46158432004ff75584320067f75584320047f7558432014fe7558432004fd7558432014fc75584320067c75584320147c7558432004ff745843200cfe7458432004fd745843200cfc74584320067f54584320067d5458432006df3258432006ee3258432006dd3258432006ed3258432006cd3258432006f65158432006f55158432006f64158432006f541584320b6f731584320b6f4315843206ef7215843206ef42158432004ff7058432024fc7058432007cd329803206efb6098032026f860980320057f75580321857c7558032005bf745803217dbc7458032007cd325803206ef86058032004ff75580320067f75580320047f7558032014fe7558032004fd7558032014fc75580320067c75580320147c7558032004ff7458032006bf7458032004bf745803200cfe7458032004fd745803200cfc7458032006bc745803200cbc74580320067f54580320067d5458032004ff715803201cfc7158032006fa5058032006f95058032006fa4058032006f940580320b6fb30580320b6f8305803206efb205803206ef820580321757e7598b310057d7598b310b6ef6298b3106cff7598b31014fe7598b3106e7e7598b310147e7598b31004fd7598b3106e7d7598b310047d7598b3106cfc7598b3106cff7498b3100cfe7498b31004fd7498b3106cfc7498b310067f5498b310067d5498b3101cfe7398b310b6ef3298b3106eec3298b3131ede3198b3131edc3198b31024fe7098b31004fd7098b310b6ec6258b31004ff7558b31014fe7558b31004fd7558b31014fc7558b31004ff7458b3100cfe7458b31004fd7458b3100cfc7458b310067f5458b310067d5458b3101cfc7358b310b6ef3258b310b6ec3258b31004ff7058b31024fc7058b3101cdd76ccb310b75e75ccb310b75d75ccb314175f54ccb314175d54ccb3106ede62ccb310b7ce62ccb310b7cd62ccb3101dde71ccb310b7d671ccb310b7d571ccb3101ddc71ccb311757e758cb310057d758cb310b7cc324cb31005df764cb31006df764cb3138f5f544cb3138f5d544cb310b7cf724cb310b7cf624cb3106ede624cb310b7cc624cb3101dde714cb3101ddc714cb310b6fb6098331026f860983310057f75583311757c7558331005bf745833114dbc74583310b6f86058331004ff75583310067f75583310047f7558331014fe755
  | 30 => 0xb6098232026f860982320067e65582320067d655823206ef86058232004ff7558232014fe7558232004fd7558232014fc7558232004ff745823200cfe7458232004fd745823200cfc74582320067f54582320067d5458232004ff715823201cfc7158232006fb4058232006f8405823206efb205823206ef820582321a57e75cc9320057d75cc9320b76e75cc9320b76d75cc9324576f54cc9324576d54cc932005ed71cc9321a57e758c9320057d758c93206f5e758c93206f5d758c93244f5f548c93244f5d548c932007cf628c932005dd718c932004ff75d8532014fe75d8532004fd75d8532014fc75d8532004ff74d853200cfe74d8532004fd74d853200cfc74d85320067f54d85320067d54d8532006f751d8532006f451d8532006f641d8532006f541d8532024fe70d8532004fd70d8532006f761985320057f75585321a57c75585321a57e75185320057d751853219dbe7418532005bd741853231edf63185322ceef621853201ef66118532006f56118532005fa7018532005f97018532004ff75d8132014fe75d8132004fd75d8132014fc75d8132004ff74d813200cfe74d8132004fd74d813200cfc74d81320067f54d81320067d54d813201cfe71d8132004fd71d8132006fb60981320057f75581321a57c7558132005bf745813219dbc7458132005f77158132005f471581321a57e75181320057d7518132026fa6018132006f960181320b75e75cc8320b75d75cc8324475f54cc8324475d54cc83206ddd72cc83206ede62cc8322c5de71cc83206f6e758c83206f6d758c83243f6f548c83243f6d548c8320b5ed738c83242dcd738c8320b6ee638c83206fce638c8322c5ee718c832004ff764c83206ddf764c832006df764c832004df764c83241f5f544c83241f5d544c83206ddf724c83206ede624c832427cf524c83206fce524c832427cd524c83206fcc524c83241fcf424c83206fce424c83241fcd424c83206fcc424c8322c5dc714c8320b5ef764c832006ef764c832004ef764c83241f6f544c83241f6d544c83206def734c83206fcf734c8320b6ee634c8320b7ce634c832427cf534c8320b7ce534c832427cd534c8320b7cc534c83241fcf434c8320b7ce434c83241fcd434c8320b7cc434c8322c5ec714c832007cf764c832005cf764c832006cf764c832437cf754c832427ce754c832437cd754c832427cc754c83206fcf654c832427ce654c832427cd654c83206fcc654c83242fcf744c83241fce744c83242fcd744c83241fcc744c83206fcf644c83241fce644c83241fcd644c83206fcc644c83241fcf544c83241f4f544c83241fce544c83241fcd544c83241f4d544c83241fcc544c832007cf714c832007ce714c832007cd714c832007cc714c8322c5cc714c83206fcf614c83206fcc614c832
  | 31 => 0x97320067d71597320067c71597320067f41597320067e41597320067d41597320067c41597320b67f31597320b67c31597320067f70597320067e70597320067d70597320067c70597320067f40597320067e40597320067d40597320067c40597320b67f30597320b67c30597320067e65987320067d65987320b6f7619873201ef461987320067e65587320067d65587320b6f46158732004ff7558732014fe7558732004fd7558732014fc7558732004ff745873200cfe7458732004fd745873200cfc74587320067f54587320067d54587320b6f731587320b6f43158732004ff7058732024fc70587320067e65983320067d65983320b6fb6098332026f860983320067e65583320067d65583320b6f86058332004ff7558332014fe7558332004fd7558332014fc7558332004ff745833200cfe7458332004fd745833200cfc74583320067f54583320067d5458332004ff715833201cfc7158332006fb4058332006f840583320b6fb30583320b6f8305833206d7f76596321ae7f76596320147f76596320057f74596320057d745963206e7f64596320067e64596320067d645963206e7c645963206e7f615963206e7c615963206e7f605963206e7c60596320067f74596320047f74596320067e74596320067d74596320047d74596320067c74596321ae7f73596321ae7e73596320067d73596321ae7c73596320067f43596320067e43596320067d43596320067c43596321ae7f725963206e7e72596321ae7d725963206e7c72596320067f425963206e7e42596320067d425963206e7c425963206e7e325963206e7c32596320067f71596320067e71596320067d71596320067c71596320067f41596320067e41596320067d41596320067c415963206e7f215963206e7c21596320067f70596320067e70596320067d70596320067c70596320067f40596320067e40596320067d40596320067c405963206e7f205963206e7c20596321ad7e75cca320057d75cca321b67e65cca320067d65cca3206ddd76cca32006dd76cca3245f5e75cca320075d75cca3206f5e65cca3206f5d65cca324675f54cca324675d54cca3206fce52cca3245fcd52cca3231dde71cca32005ed76cca320b6ed76cca320b76e75cca320b76d75cca3245f6e65cca320076d65cca324676f54cca324676d54cca320b7ce53cca3245fcd53cca32005ed71cca322ceee61cca320067e65986320067d659863206ef7619863201ef461986320067e65586320067d655863206ef46158632004ff7558632014fe7558632004fd7558632014fc7558632004ff745863200cfe7458632004fd745863200cfc74586320067f54586320067d5458632006df325863206ef7215863206ef42158632004ff7058632024fc70586320067e65982320067d659823206ef
  | 32 => 0x100000020008000000c000000000200000000000001000000100000000004004000c001000000200000040004001000400000000000004000000c0020020000000400100040000008000001000000000020010002000000000040010000001000000000000020000000000c002001000000000020000003000000100000020000001000800000040000004001000000100000000008000000000000040000000000000000000040020004000001800100000000004005000000000000030018001000400000000020000000000000300000000004004000c00000080000010001000400000040060004000001c004000000000080000008004000000100000010000001000800000000020000000001c0000000000001400000040000004001000000200000000004001000c0020034006000000100000000000002000400000000000008003001c000001000000000000000000000400000000000014003000800000000000010000000400200000000000000001000000040000004001000000100000000000000000000200000010008000000000100040010000000000000500000000010000000000000040000004000000000000000010000000000400200000000008000000400400000020024002000400000000030000000000c001000800000140000000001001000000040010000003000800100080040000000001000200080000004001000c0020000000000400600000000000004000c000000000100000030008000001800000000000004002000000000000020004000000000100100020000000000c0000000000000000000040030004000000c00100000000000005000000000000030000000000c00000040020000004000c0020008004000000200080000000002000000000000000000001000400100000000000000000000300000020000000000800000000000000000000400c0000000000c0070008003000000100000050008000000800200000010008000002000000080000000003000000000040000000001000800100080000008001000000500000000008000000c000000000000140000008004000000000000030b57f76597321b67f76597320147f76597320057f74597320057d74597320b67f64597320067e64597320067d64597320b67c64597320b67f61597320b67c61597320b67f60597320b67c60597320067f74597320047f74597320067e74597320067d74597320047d74597320067c74597321b67f73597320b67e73597321b67d73597320b67c73597320067f43597320b67e43597320067d43597320b67c43597321b67f72597321b67e72597320067d72597321b67c72597320067f42597320067e42597320067d42597320067c42597320b67f32597320b67c32597320067f71597320067e715
  | 33 => 0x14000000000500080020004000000800000040000004001000000000280010004002000400000180000000000000c0010004000000400000000000000000002c00400140000004004000400100040020000000003800100040020000001000400000040000000005000000400000000000002000400000000000000001000400000000010000000001800000000000000004000c000000800300000040004000000c00100000010000000000000000080000008001000c0000000000000000000000010000000000000200000000018003002c00100000010010000000c0000008000000400a0004002000000000040030004006000000100080000000003000000000000000000000000c00200040000000000000400000040000000000001000000000000004000000000000000000000005000000200000020000001000000000100020004000000000400000000000000000c000000000000040000000001000000000040000000001000400300080010010000000000000100000000001000000000000020000004000000100000010004000000c000001400000100010010000001000100000020000002000800600000060000001000000500000000008000000400100000060000000000000000040020000000000c00000080000000000001000000000000000000001400000000000014000000c00100040000000000000800100000040000000000800000000000000007000c000001800000000000000001000c0000004000000c0000000001001c00500000020008001000000100040000000002000000200000000008002000c000000c003000000100000000000003000c001000400000000040004000000000000000040000000000c00100100010000008000c00000080000014005000400100100000000000000400000040000000000001c00000000030004004000000200000010000000000c00000000080000000000c0000000001000801400000000000001001000000040010004005000000900000010010000000400000040010000001000000000040040000001000000000000000000000000000100000010000001000000000000010008000001000500000030000001000000000000000004000001800400040000010000000000000000060008000000000000000000010000000c00000000030014003000000d0004003000000000000000000000000c000000000400280020008000000400000080000008000000800000000000000000000c00300000000004000000000000000020004000000000300000000000003000800000000040000004000000300000000000000000000300000010000000001400000040030000003000000100080010000000000c0010004003000000200000010000006000400000000
  | 34 => 0x400000000000000002000000000100040008000001400000280010008002000400100080010000000000400000100010008000000c00000040000000001000000900000010008002000400100000070000000000400000000000000000000800000040000008000000000000000020018001000c000000000000000000000000000400000000030000001000000200040010004001000000100000000000000001800000000000004000000800200000000000000001000000000010010001001000100000010004007000000000000000008000000000000000000008002000800100080020008002000000300000000000000000c002000000000080000000001000000000000000000002000c001000400c00000010000001000c001000000000000020000002000c00000000000008000000000000080000004004000000000000010008001000400600040000004002000400000040030000000000000100140000008003000000100000000000000000c000000400000000000008004000400200040000000000000000000000000000001000400000000020000002000000100040000018000001800100000000000000000000300000020000000000000100080060008000002c000000c00200000020008003000000000000010004000001000900000000014001000000500040000000000000000000040010000001000000000080090000000001000200040000004002000000200080000004000000000000080000000003001000d00040010000001000400000000000000000000800000000040010000000000000080070000000000000000100000004000000400100100000004003000400000000000004001000c0000000000000400000080010004001000000100000040000000000c00000140000004002000000000000000000000000c00300080000000003000c00000000000004000000000000140010000000000000000040000004000001000000000010008000000400300000000000000000000100000000010000000000100000020008000000000000000000000000000400000200050010005000000100080000000000000000100000010004001000000000000000000002000c00000000000000002000c000000c00100000000000001001c00200100010010000000800100000000000000000000000000000000000000400000000000004000000000000000000000000001000000080020000000003800000040000000000000400000000010000002000c0000004000000400000000010004000000000100000010004001000800000000000000000000400100000010000000000400000040030000005000c0020004000000c004000000000000000008001001c0020004000000000000080000
  | 35 => 0x65e00000000000000000000000007fc65080000000000000021600029bc15811ee0f4800000022860001f0c7bc000007900003d880000000000000000000024ac0001cd49e58000513255800029287bd8000000173c0ef9c8425a8cc8000000080d2728a8e019269600006b401c800000000000000000000000000000ae00005980000000050a2c888b400000004510000000000006d0000000000000000000d115d48e68ba20000000000000000000008c518d00002a9c29500003960198000000000000000000000000000000000000000000000000000000001dd8000000000000000000000000a7491d20000000000000000001c400021b4000000000000000001f487791e249b008b258c17c865f14e20000000643255a0002176000000000000000a78bd200000000000000159000000000000001cbc239000000025f2000054000017b00000000000000000000000000000000015a00000000000000779800019e81f69b980008b800000000000000000000022e2405800047000000a98000000000000011660000000000038a6e11480000142024b00001301b18000024a0afa70a0000000000000000000000000000000000000018dc000000000000000000000a9e0e325a500000000000000000000005b40000000000000000000000000000000229c000000000000000000000000241e00000380000000ab5000000026c20000bb60000000007282e6c8850e73b1e260000000000085e59980007560ab800000008c1000038e8000a668000000000000000000000000000000000016fe000000092500002dc8000000000000014660002aac00008d80000000000000000000008d780003540000000000099ca37c3c095ee00000000c8202400000006060000000000000000010008001000400000000010000000000000000000080004000000400000080000000004001000f001400300000000008000000000100000010000001000400300080000000002000400000000040000000000400000000000010000000c001000000000000000000004000800200000000008000000000200080000000000000000000300000000000000400100000000000003000000000080010000009000800000100000004000000c0000000000000000000080000000001000000100140060000002000c00200000000000000000000000000030000001000000000200000000000000400100080000000001001400000000010000001000c002000000100080000000000000c000000400d0004006000000000040000000000000c002000800300000010000004000000100000020000000000c000000400100040020000005000c0020004001000000100000000000001000c000000800000000000000000000c002000000000100010000
  | 36 => 0x8000000000000000000000dd85c01d6a0020000000000061f0c5e00014d60d90dec175012400000000000000000000000000009ae800045f800086000000002770000000075f096200000000000000000138800000000001ae6000000019b80002ae8000000000008aa45c00023f252200000000a801ee000073d0000000000053b8000000271c0d78f3608880000000000000000000002f802193ac0f600000000632000210800000000002212000250e000176000000002f88000000000045b0000000000000009485ff131e0001e64000000000027b4000266c00000000002a70000094482a0c0800021ba2948000000284a00002401988000000000076300000000000aac800000000008cd00002d59c6200001fc6da88bc00000000000f0a865a12a0001156000045c0000000000000000000000000f300000000000000000010bc369000a0000d2a9450fcc00009c8000000000008a85f7000017e09b00001eb67a506e800021705a980000000000000000065a0000000000094400009ac80004de95866bf87d0000036274b81220fe2390000000000000000001d7200000003599fe0842800000000000000a1c000000000017800000000100000000000000000ba40000000000261e0000000000000010500000001bc200000000000a024c89ac60001e3c000000000000c6854000002b0000250822e00004f69dea358000000000000009cc800000000005be00000000000915000000018ca17715520000000a7898562468e6600000000bbaa1a0000000000172c0001d625659c3a00027a46e882da00000000000a8a0418ed8000000000007ac0fa254600013f8000110400000000000000000000000021e08990000000066454380000001d8a0000e0600006520000ee00000ea6121a12400005461c98848000000000029481098000000000000015341ea000000000000000c9a0001658000000000000000001c5c0000000000000000025120000bb00001cee4760000a22000000000007f38000000075a00023ca000292a0000000000000000000000001dd8000000000000002518fc09a8000e31586ce4368d286a320360000f3c7710c26000000000000001f395c800022bc00000000000000000000036f00005d59a0400000000000a880000000000000000001ac000000000000000000000000223606693c48ce0adc424834a0001bbc000280e8e9000077188e8801a70e7590a980000000000000000000000001eba00000000000000000000000000000000000000000047980004cb12d84a790b06c904503bd09fc5390c24a8a00007f5125c03497d097092527d58bf4000000009d1c1a0000a5600000005ec8b2e0000154000282c0000000009982287d04d64528c4073c18cea738000000015c33e00000948000abc0000a800682
  | 37 => 0xc2ea000000028a80002320004000042680000a680000000372000000000000007b7800025a1eac0000000000101a0000d640000fd80000000000000000001fe0000dd40001bdaa7a0d48535038600018363131b4a0000db03261d9810800000000000000043045f000000000000000000000000000018d8000000045e8e8200000007dd21a000000000000000000000000017980000000000000000000008f69d320001f0e4f3800000000000000000000000000000000000000000000000013dc88b8f52335969200000000000000000000000024c86b6000036600000002426000000000002e600016b000005a600026d4a590b0e71a283295ea06e00000000000000000000000000000000000000000000000000000000000000000003f20f280000000000000080600000007580000702000000013a416896640000d260000000000000001514bc502000000000000000ccc000000000000009e88000000000000008200000000000000027c800000000003f28000000000000000001cb000000000008b289d8000000000021f800000000000000a9700000000000720000003e886600000003118000194000090b800008a08501700000632000035f8ee60001392000199600000000000000243000045310c427e80001a20000000130c1568aee0d68000000000000000009c4800000d0000000213000000000000000000000058d00003682084000000000000009c6092e5daa51e0000556000032a9b687f400000000000bbe000000000019b00000000000000000000005c28000000247271398ec61b06405eb0b20000000000000008c41102000000000014a2000000018a0000563800000000004a402ca0000000000223e00000000000000000000000022a294f80004fd800000000007e3800000020f4000168817e800091780006439d6c597831a00000000000000000000000000001e78d860000000000000000011b200000000000000000000000000000001e8000000007e280007f60000000000000000000001e820000000000000000000000000000000000000000000001962000000072d000000021b00000000000111600000004ce063a00000005bd0000000000000000000000000000138a003106a18880000001206000166e6b3000011620280000000a090f663a3800000000000001f2400005d8000003200000000d62ade0001964000000068a0000000009464a0a860000ec200000000001820000159a3df0c3e331000087094ae13aa716866a91a47da5821a1a4e4465957e43a80003ee8000000205a4629fec00000000000000000000000006cc11e13200001a1a00000000000000000000011f00000000000000000096f80006ba800000000000000000000000022a8bb400014fc0000000000004a704800000000009b5
  | 38 => 0x20600000001a7800000000000001592000000000000002d7000000000ce000000000000007eaa5425be800000000000002048a4e146e0000fdc000224c1e804a015e0000000196c0000000786953000000000000f7830a0000790800000013f0ab729b29d580001130000000000034800002cb00005eeaa4a00000000000000a3c0000000000019a8000392916e0001a060000c1a0001bf6000000000000000000000000000016c005ca05000079b8eea000049c9ef00002158000000168600029005380000000000000000000000000000000000029102ad1ef835300000000000000000072a1db6000000000000000731f5200010a2000291c000000000000000000000000000020a00001ef93b2841a214299a31a3552554416810800014ec97380e082200000000000195000019d000000000000002866000133016b1fb000006a408b0590000000014580000000ceea43000094c000000018aa000000000000009b613a830a800050483f64371e722f908241040000000000000000006f3800088228ec0000e620000000557000000000008aa80009da0000705a43a00000005da12640de020a67baace4a6057629409189e189d485700003d180000000000000097a00001d0660000000000000001f340000000701800073e800084e05340000000468800086a83840001e220000f446d18000aad80000001fc86d8000026b9e9a4db800072e8000000179c42b0000000000000016e47599f6e07295a8000000055989e60000e700000000418000013ca4f25bf25ee99890024a697cc00024cc29d1f980000000000000000008340000000000000000000000000000000000000020ca0001db400003d6859000053d000000000000001930000218e928800000018da78c00007e6800000000000761fa40000f684b0115000881007112a141ab0000000000000000000000000000000000014b000015d837e00000000000000000000013740000000000000000024b400000007e503f47e11056a861eda7eb0000a3a26aa000000049e80000001e705d000000001146000000000000000f08d4a00005b2000000000000003a125b40820c6c0001b2e000000000019e659c00000000fe44db1802000000030c00000000000000000000000000000000000000000000008758000000000000000005bb80006a200000000000000000073080001b4000099e800000015a070d8d9a7d3a2f694d15469811d860ba00008c01f68341a736a59a4ea9831382000031c0000000000000000028da000280400000005588000045825471c0000000000000000000001c049a7800084024ca00000000000000000000037e80006afa9e00000000000000000000000000000000140e0000000000000000002340000000484826c71081109fa017e000000068420a
  | 39 => 0x29c80240000000000000008380000000000000179e00000003e600001f1800000017de00000000000d00000000000000008a0016844d83c06df8f9014e800000000004b59e605b10a6e7d70000000121640f892a00000000000000000000051b0218000000000000001be9576210000000000000002a400000000000000000000000000d1c936800077c00000000000000000000000000391c5400010ba998000078b80004fb000000016f236fa57650280003f400000000000000000000000004cf039e49b12309fa8ea225b0b660001284000000000000000000000000000000000000ee13fa0000000000000000029f4a4b80000000000269800070f91c451c841e0000000000000000000000000000000000000007100002a169ac09ac68799069d10d3c00000009ec800058799c409719a4a7b1c7661497067c51076000000000000000001a2e07c000000025da5d1902600002fe03709e852821de20e85360000000000000000000000001dfa000250a44f11003ea00008d10000023252600000000002a3486a0000063800000000009530810000120800020f83fd000000000000000000000205200000000000000000000000000007aa00000000a1a00000006928000000017a00000001c8800040aaa5e1be0bdc3ba22c0000239c0000000000000070000000000d1aa2827cc000089a00010b2000000000000000000000466266a000000000018fe00000000000000000000086f802a9de00003e304a86cf8000683014c000000000010840000000847839c6138000000000000000000000000000000051e000000000000000000000000000000000000990000000000000004978000624a87800024320000000000000000000005889cc65df8000548800000000003de89aa000000000000007920000922800000017da0000000000181a9f0032c00000004cc8000000000000000007d9a14e6f204ec15784f400000000000a9a000293a651800086100000001e4400000000000000000000000010e200006be00005aa3c6000060300002c79ce2000000000027580000000994800000002b20001e08000156c0000000aa611ae0000000000000000000000000be0934128e6e5800052789f0000000095780000000fa00002476000000027d89d243e90b400009ca5e90000000000000002a0000289e00000007ef800000000000000000000000000000000000000000125a2782a0600000009a880000000000000000007380000000000000000000025ec000000000000004ea80008bd14fe000000000000000000000000000021600003850000000000000008540000000000000000000000001e2000010e050010cc9310dba586000090b00006728000000102c00000000001b6200000000120000000063666e898a0000000000000000
  | 40 => 0x62000084483b255d00000000000000000081d2ae000000000001fae1dd041c839049200024d800003c60af0000000000000017540ad800069b00000001b880000000000000000000003831d3890f9f1ca5c9a7a0000000000148e000000000029ae1f6069c0002a5a0000000000000048d94309a68000000135600000000000000000000000020a047f8000000000008c16ea1cb8000000000004f043c5690000000000000000005a30000000000093b800000000005ba18d227b000000000001bd17fe9af0c2c10b8000000000000017620000000475000000004ba00009ce32000001511a321b4a80600000000000000544000000028f89680000000000000000000a480000000cb8902000000000000000b5e00000000000e7800007200000000000016c0000000000000006280008628000000000000000000001b800000000000171a0000000493000033a80005770000527000000000005b997e6000281800024b800002c000000000000f4e43e0000000000004d0fe681c800077780000000000000000010680000000000000295e00000006ff908a000000000022fa0000984000000000000000000000000009838e11e800000000000000ab8961074400000000260a6b00000001c7a9d52a581220000000000000000000000000000000000012141d72830a02800035e0000000250206e8000000000009580007a10a360001e8600000000000000000000000000000000000000000000000000000cca9f1800071b000000000000000000000286a630000077300000000000000000000000000000000594800081b000087d8028306070600000005a408ae00000006c48000000000000000000000290000000000000000000000000000000000005068f7645a80002a10b4800000000001b0200000000000000000000000000000000000000000050b0000000000000000000000000000000000000000000000000000000000009b880000000000a04859258c800003b19d00001bde00000000000000000000000000000000000000000000000000000000000000000000000000000000000055401bc00001580000e7670b1a5c00000000000000000000000005e85b380000000000000000000000000000000000000008d8000000000000028be00006100000000000000000000008130000733000000000000000000000255c00000000000000000000000019600000bf80000ad600000008de0000000299c0000000000051000000000000000000000000013a69042210348a8f63f8046e00000001e480007a880000000e4e000000019a000035a8f1400000000000000000007c00000005a38000000000084685705c20000000000000017a030020644b1000000025dc000209a00000000000000000000000000000000000000000060a00
  | 41 => 0xf6c9fe24746ea0000000000065ba564770a78c4ce8330000000000016462e7a216780000000000000000afe0000000049800000000000000000000000000000000000000000000077700001ad8000000000000026ea00019e00000000675800000000000000000a2b0000000094e0000d160001bc6000000077b1888000000000004e06a1800000000006401b3aa8780009611f3c0d4800000014500000ec4868a5ae0001ff029c000000000000000000662045a00029425a08000000094a35081a600000000c60000000000000000000002700000000056423ae0000000a6580000000000000000000000009c7a5407b2800000002ec9bf00000c189ea42a800000000000000000000000022529a80002a2e000000074389cca9d263e0000000000000085f18400000000000256c43926b800009644c503504be002c7639be49cd0000000115400000000000000134000035e81e8000000053680000000000000000000000009a4a5d400000000000000000000003e005aa9a000000022400000000000000000000000000000000000090d06ea00000000000000000000020100009d8a0200d5800043c2a9e000027c0001dda3d006b40000000000121000026e89c30000517802e00028d8000000000000000000000498249200000000000b2a0000000621800000000003cf97e20000000000000000000000000000000000000000006f0000000000000000000000000000000000000000000031259580008d2906800007fa5f804685dc000000000006ed2022000000000011d0ab9000012c800040480006ca0000661800077f99900000000000217a70500000001d5c903800000000000000000000174c00000000000000000000000000000000000000000000000002d9000098227c82270d74000238000000006a2800000000000000000a980000000000014c12b80000000123800000018b0000000041987980002ab40001584000000000000000000aac8b10d567b6280c000000000000004bf903638f8e0e00000008e8000000005ee000000000018a600000000000000a67800086c800048e00000000000799a05e666012800000007ee000000016767c180000000000122800037f0000000000000000004f580005c580000002668000000000000001d8a7a000000000000f16000000073c9ae400000001838000545833a0000ebe000000000000004f800000b911d600000000000000000150400000000000000237800073a000000023220000000000000049582aa14b00003a2203a70c00000000000000000000000009c20fb608e96a000000000000000000000065280001bc000000000000000000000000018e09ee00000000000000000000000000000001f36000000059394340e309d012f90a800000002200000000000000026060
  | 42 => 0x61d000000025f400000000f42ac600017d60000e7c000000000000000000a5c9b9256200014466420000a64895834480001960000000024c000000000013fe034000000000000001dc8000000000000000000000823000000000000000bc400000000000000000000000000000000000000214a0000000a481b40136910c443a76a000000060f80000002ad20000000000282a00000000000000000000071fa59a7e004a68cb1cbe000000000000000001bf800027e400000006b380000000000000000025500000000938267a2000540000000000000000000000f720001cb60000000000000000000007149d282afa9d43f10ac897a8000000000000000000000528000000000000000000e52000000000000004c480004de242200000000000000925800000000007ba9e4e237215a000000067525e2000000052d13d0aa5800098599946d6151860e91061628c50000000044500001f727fe40183ea000112c9bd00000000000000182a0000000000000000000000000000000188e0000000000000000000000000000000000000000000002a1c0000000000028e00000000000000000000000000000002abc0990e7a4c38000000000000000000001cc866680000000000000000000000006c680000001ff800000000001e3a000046495d0000000000000000004e78e9212798ba0000000000000000000001470780a7aa19898813f452b11740000000000006e000000000000000000000000000000000000001c3c8cea96000003ae26680000000000000099c000000000000000000000000078a00000000000000000000000000000000000000000000006bc00000000000e023e596d000000000001d260000d82774988a0000000000000000000007d300000000c78000095a0000000000000073f857a00000009a1800000005800000000000025a101000000011e20000000000098c00000000658000000000000000000000000000280000000001b721940000000000000089180000000000000000000026de7ea24006761f8273580005d0800082d85ca7d90c16a52800000000000000000000000000000000000000000000000000000988000000000000014f200010b60000000000000049ca5a800014aa000000080ba74a0000000000197a00000000d080000000b864ca00000000000000000000000007ff80000bda52097e00009630cdc0320000000168000000000001adc4ee800017d2998000000052080c4000164000000009bf8e444a300000f8932400000000000000000000000000000000000000000000015e2000000000000006db000000018120000a346a4268495a00000000000113a4be00000000000000000000041e800000000000000000000000000000001878bf2a8c000000000000000000000000000012be0001
  | 43 => 0x59d000000000000000be8000284e0da00000000000a0209c66b00000000251a0002388000000006c000094b855c0000000000151c000089000000000001fb4000000000e88d0000000000023ac0000000000000000000000000a3272980000000b06000000000000000000efe54e016e00010700000000000000078e000058b9564000194899b8460000000000000000000c14000213a000246800000000000000000148a00000000001a7601923b24f600000001f700000000000000000015ac8ed80003af0000503000000015f20000000000000000000000000000000000000010c84a1a324a80aa72000070a000000072400004a00000000000000000000000000a9480b60000000000000000000003430000000043e98c00006b8000000000000000000a38800000028260000000000000000000001939d9458f94049068912000055000019cc65f90be00000008548ec66e38000000142202c80009df860a00010f21a996c211984b822e00004ba0b7e0001b5e8d7000000000007d0000000022689460af60000000000000000028bc00000000000000000000082980000001cce53e800000000000c2800098a0c6e000000000000000000000000000000000000000000000000000000000000000000000000000000001ca400027f05d623cc0000000000077802b812e00004428ae8000000000000000000001240000000000019f20000000552aaea301118400023c651f275a00000000001f6a6c4000000000008d58000000000000000003ae800000011ba000000044f8000000000000000000002a6e00001fa000000000000000e8000000000000000000000127e000000000000cc8439c34a940000a6a80006678000025800000000000000000000000000000008330b6a00000000000000000000097d91f867a80006ae00005f606aa00000000000000756800000012dc030a186000000000008b6000000000000000000000000000000000000000d4600000000000000000000000014ca0001940000000000000007f28000614000000009c20000a92a1a00007b300000001f0800000000002922a2100008d3027e4e3a36ca8100000000000000239885a8000000156e28180009ef9b4882b8b6200000002b41ad23c39292934a9dc8a080003a900000000000000000054f00000000ac0000000000000000000000880800062b8a2c7bb800036500000002654947000056b800000018de30080008f10d5c000285454b0bfe0000000a5c1b0e000052a92a8000028800000000000000634000000000000005261eec01c80000000000000149600008c60000cf6534a78225b800043b00141551a9e79280001250000000000000000007b011725468000000000000000000328000000000000006e20000e9a00000000000000
  | 44 => 0xd9e0000000000000000004029f40000000297812900003659b2000000000000000000000000000000000000000000069b80000000000000000000028460000000000166a1c7000000000008e1800066a000000002d8949048c000298c0000000000000021e9b0a06a10de0002ab0000296812b87d6690203279b1a347428f502308000115800000000006ab00009ab800082c28b20000000000000000007b600000000000f7034e9d904da800000000000000000000207833380000000000000050682a800000000000000000000000000000000000000395800060380009c88000280103400000000000000000000000000000000000000193e0000f0435d80006f1136084700000000000000000083c95c0000000000000000000000000000000000004c6800000000000000b960002026000000031c107c00000000000a189f11caa5778000266000000002e0000000000000007410000000000092e9870000000000001c200016360000000000000000013900001fdc0001aca9aa024e96a800000000000000000a65000000000000000a823daa93271680000000000000000021b20d608800000000000000108c66aa01618580004e721e844c0000000000000018d4000079a000000000000000000cd80000000000000000000000001c782138c9c047a834000052600028d409980004520000000254a000226200005c8000000000002960000000000000000000009a980000678aca0000000000294640b93ee00017c400005663ab00000c9a95c41c94be0000000000000000000002d3800032300009c80000898093a41b80008d5211400000000000000000000000000000000000000000000013646e19e180a0998c6dd07148ee02c600000008ab000059080000000000000000083b1bbe00000000001b7c66f8d6003c800000000005899ea00000eb4aba2710060000000020bc0000000000000000000000000c925c080002f1800030d17fa00000006f80000000000000000000d800000000000000000076e00000000e864b8000000027400002308000000000000000000164000000054e80000000000ab98000539a2f20000c385fda6b410e095c80400000000000000000000027eea43813229904f8a4288ce303800000028ba00000008da80000000000a7f06149730000000000050d800000000000000e9e9520000000106c000020000000000002956000193200017820000000000000000000000000914000000000000000808000000181c00022c20000eaa00000000c900000000000000000000000002de844000000002d3062007a8fe20000000000000000000003759d180001ca000000000001d962ce800000000000000000089800000000000000000173800000000000000000000000000000009728000000
  | 45 => 0x50dc8000000000002c4000084200000000000000000066000012ce33ca6dc0000000000000000000000002750154968a00000000fb800000026fa0000000000155e00000000001e7e0000000000000005c800065798d60000ce475d0148163000041380000000000000000057a80002038000045000000029f60000a900000000000000000000009a08fbc0000da6000102458080000ff00000000000000120a000000000004fa0000000000000000000007cb00001cc000062b00000000000000246e000186e00000000000000000000000006720001fbaa560000000000003780008b51d689b200002e98000000000052e800000000008118000000173e000267e00000000001d9a4668b1c32a87c800000000000dca6b20000038a3961a3800006516504f2000076f06b0000160c13900000000000000000000000003f50000000134c00000005ce80003921b94997800062a000000007646280000aae0000000000068c000091180000000000000000000000000000000000000000000000000000a832a428d887e200000000000000000185800007e00000000971212e00000009c5000014c800061a1ce60001b4479f000000005c200023ce5d900000000cde89e800000008be00000006fc995a4f920c021a8d4000000000000000000000000000000000000000000000027c200022ee00020fa0770b90298102200006fe86d800075e0000000000045000000000000000000082d00005aa87da000186a10c8b040000000000000000000000000000221800000008d40000000000000000000001e50000000000000000000000000803a8921b9800000000008c7984a6a8813e00000000000a2617b04b09ea1648a29800000000009202ac20000e2a00018040000000871000030c9c7443d000000000000000000138800000000001a4000078580002ba1cb000016080000000000000000000000000000a0e0000000000000009ba0000000a16244200000000000000000000000026f08f629be0000862000000091100002f50000000000000000009a28000000159897821560001b66a5aa59851c1eaa000000000000003f1aaf6760800068da62a39f98b600011386000c2e00000005fc06040000000000201c00000000000434106248e00000000002664000000000010c600021fa000000000000007c9912e00000001dc8000000000083a047200000000000000000091000000000000000000000000019b400000000000e544e6857c000000000000000001a6412f000000003ec5aa0f6e00000000000000000000000026447269bcc00000000001c2e00024a800028903629844290000000000000000000000000020c91cc00000000000000000000000015069d980000000000000000000000007418000000000071c800041102a4000000
  | 46 => 0x79d8000028120e44ea04a00000000000000000000000025600002748000264c000000000000000002882000000083680b00c880000000000000221837ca6f65ee000000000000001a440000000000000017980000000000000000019b000000000000918e4c000000000000002a900000002a765e5159c6a48c5c000000061e800081880000000000000000000029ee9398000a6000005fc90ce0001bb6a149a9630885cc5d215b000000007401aa800000000000754000000023b800000009320000fa68608b880000000000000023d8000000152a000261262c80004fa00000001d70a1f80000000000000144a00000000000000000238a5059a7e000185c37c0000000220cab400000e5800085fa63800000000000de4000000022c00000000000000000000000007c7a9149ce8000000000003d23944b91094000174400010b84d117345a70a4a9d199104718cba0000fea00000000000000a1d000000000000000000000000028f98144a709020aa0000a21901409400000000000000033400009fe10e800069c264a869000000009920000000000000000028288d82a8c7962704a1d9cda4e508aca7e000000000007c280005d280000000000132258e0d395940000f58470800000004ca0000000000000000000005891ade9510000000000069d178e0000066000000000000000000000000000000000000001da6584800071900000002702000000000000007a98af09e5000069510040002252000000063d800000014322fea45000000000000000000050c415264e000000000000000001f3e75b800000000000000000a720000ab21a4253a00002c6000000022769c9230e25c941459f800023f800000000002f980000000d5200000000000ac424104f00000000000000000028eaaa6a09c91e0000a4480000000000000000000000000000000000000000028ca0000000000290800000000000000000000000000000000aa000021da49c1a5677b8ad800008f251e8000000225a2a98cfe00000000000000000000017c8f22000112a610800098400000000000084000058e80005d480000000000000194e79580000000a4ea890000000000000000004240000000000062300000ef00000000000368a4702ee066600000004d78000a621b8c000000000019bc70616e28410000000122600000000000000000000000000000000000000000000000000000000000000032100000000000725126e000000000000000000000000000000000000000c7c0000000000000000000000000000000265c4570562a6d04e677e1dbe90580000000000000000000000000000000000000034606a83aa207c0000476a371a785bc24a6288800000020040000000000000015b0fae00000000000000000000061
  | 47 => 0x118c00000000000000a178000000000089c96de507826e55c11f24ef876687a8b1600000000001fe4000082666389b493500004d029746b080000001956000247c000000000000000000d885b322380000000087049a8738000642a63400000000000000000000000000006c780006e700000000000000000000010f600000000000000000218c378000060b0a9e00000000000000000077a00027ca8ba94925448000140800063e80001a58000000000014500000000000000000052c800041099d2000098e00002cc6f700000cb80004448000498a76079793100001e4c38b0ee400000000001a2432d8c7e338a9c2000000000000000000000000000000000007e995f8000000038f00000000000000000000000000a880be954062aa6da1885e3086485e076e6f6000046080000000000000000000000000bc800000000009718000000000010491fa8af88fc00027b60000000000000001d8000000000000000000000000000000000005080000000918a56e979000000021627811158a7c1684000000000000009e6000000000000000000000286c0000000000000000029fe0001bfa0001b080001d1600000000001424017800082e191e00000001c3800067b21c8000000000006c07bf000037d28f200000008309da24c2000000000000000ca22d50aaa3e500000000000000000000002800000000aa8000089c000000000000000000000000000000000000000000000000000000000000000000000000000000000a9b00c000000003b5185a0000000000000002e972400026580000000000000000000000000000000242400001a200000008ff80000001cd869a8e6a78180000000000516000000012fc0000000000000041180007071b5c3280000a0da8b6000000036d0000000000000000003490000000000000000000001d2c00000001d3800000000000000648a1080000000000000000045918ea000000000007283ea8b020000000000049600000000000000000000000004ac00018a200000008798b400001a5e43f27ae8f80b8c840800065513b80000d0a000000000000001ae0000000000073125fc000000000000000001a94000233000000007a4800064080002dd8000000000015b800027e00001e080002850000000070c1d6000000000000000000000000000013fc000000000028e623c000036711ce39d00007d8000000007ec5871672abb800000000000000000a8d9fde8238c94846000000000000000000000000000000000000f540000000000000016e8000000241c47680004c58000000000062f008098e8000000000000000000000000000000000000000000000000061c647060200014564832a209ce04248fe2a3200003a600000000001fc200000000000000000134e0000feca91000000000
  | 48 => 0x4c60000000000260a1188000000000000000004ba80000000000000220657300007b400003778000000195c000000000000006860000000000000028a46241dc047200003a32a90612000000015b476100000000000000214419580008e08000000000064aa4f8000000029b000070a000000000000000000000125400000004d40000000000000000000000000000000000000000001d300001be692200000000000488a40c00000000000000995800000000001cd80000000000895a2cc684a3c80000994000099600013ca000182e4f780006e08000316000053c00000000000000000000000000001b2a000178a8d4800000000000000000000000087182b07e88000000000000000000000000953800000000000000000000000000015442c901460000dc40000000000000000000006f89bd6000000000000000000000a75800001112f017fa8ee000297e571a8508bb000000000009838000000000000000000001cac000087e000155a00011bc000203c7e78000000000094181ee7a9000000024e01d8138400000000000ddc00000000001cf667c00000000e0a000245800028a2000000000025c8000000005100000000000000000000000000000b3e000000048a00004800000ab6800062514b858b00000000000708a1d43c4800000000006a392ca9f591de2b499dc00000000000c0689d0000000000017791208fd296e00000000000eae00000000000000000000000000000000000000054259e0000000000028f000049d0ee26cc00000000b428b18000000000088c800000013480000000a7c8000000000000000000e4000000000005b800000000b4600000008d41d24000000000001a07e800007c0054876c00000000000000297a00000000000000000000076b00009908dc2000154200000000000000a1220e06c000000000bb20000000000000000000003610000000000000000005f280000001c406312592000226a0000000000000021b93b61caa23c81f9ce400005fc5cd89560bf08e600000000848000000000080e279e6fc1ee60000000000061a0000000000000000000000000000000161a26d90ae04380003e780000000000000276e000293e2cf000065300000000000000000000000000000000000000000000009ec04cc9008e1c00028b40000000576a49a8b400000002862000000000000006548000226111800000005af097692daa488a1000000000000002af40000000000000000000000000000000000000010280001ec65bb000000028c40001f5859320145758cae000000078710525d7000000000000000000000000092c8000000000081a21546a0000060215fe00000000000000000000000017a800000000002a083a800000000000000000000000000001a22a8f8ef0477000029a00004b780000
  | 49 => 0x7ce80000000000000000000022fe000000000000000018000000000000000000dd800000000000000000000000020880000000f5600000000000ca690296ae955800035680000000000000000000008a200020180000000a6e800000008d60000bac0000000000000000000000000000a2c00000078000000000000000000000000504000000f8000962807e32c8aea000000000000000000000000199c97f8000293000000000000000000000000000005e200000001f79ece77d800085b1f4a66d80006540b140df20c600000004b4a420000000000000003d78a5a03b9bd07348000000030254080000a713a0000000000000000000000000000000000004bd00000000000a8480000000d447081edc0000000891000000010d4055875e7fa1b265af80000001a8274e8000000000000000002a700000000000000000003d8000000000000018980000000000000000000000000000000229e434800062680000000000000000000000009411ee819d92a00000d729e3800078280006a100005c9a3e400009a2000059800026a4507000000000000000000000000074809200000a2a376a71a0000000000000000000581df99c87ac8000a538b1298da9b880480008be0000000000053003b036da34800000001fa0000000139800010780000000000000000022de0000000000079c8aa15f600000000000e12436213e0000cb000014ce000082a00009d6a3792f654da0fc5c5000000000006738000074aa0e0000000a348d6241d230a0000000000000000000009fc91a4a20000000000006a903ac4af20926490fee5b70f5c00010d031c86f2514800000000000002a660ed80000000b2600000000000000000000088a00000000f9a00000000000000000228e000279c000033c00021bc00000000dc000000020d2000142642380009940000560000000010962118000000009a4548000000177400019f68d980002e617ae00000003ec000094ca02a63e1b06a260ac6499800056e80006e91de2000192e00000001448000000000000023844290000000000000024fe00001de64683f000015e42479454747865c3f48e34754a4389bc9b9800017ea9b2a4c00000f601e20e4033527763890c1e0000428000000000028708b5800075d8000000000083100004e58272a9501903b22a2246b011c91a8000000225e05980009888000000000000000006ec80008e88000450a2a46451b70798a4985c4800034104b612000003d680000000000ab3081e3ef80005108000000000000000008ed00003ac95e00000a6a338000057402f011b000092f000089280000000000000000092c180a8342a6435a000054c8000000000000000001a5163820280000000000000007400000000000000053800000000000001b92000000000000000001
  | 50 => 0x185e0000000000000077a80009bb000000000000000000000000000000000000000000000000000000000000837097437f80000000000000000000000008ff0000000000000000000000000000000034b992000000000001b2c0000000238227c0000000176800000000000000000000000000027da00007c4000000005e040e46a932e16380009b180000000000000000000000000001b50000198a943174e000000048600000000b8a000000089722420000000000000075780000001db266b00000001c0a1d000d48580000000000000000000000500696943e0000000000166868a80002829e8e7d08eee00000000000000236888c6130000000247aa79924878795a2000000041407aa0000000000000000000000000000000000000024ec2459c9c3ca80000c002b4426000057480000b50000000000003a00008998dc60000b500001a4e6af08600d19018000286028e972e000000000000000000000000013000000000000ffa000000000000000000cbc000000000000000ea00000001304000000000000000000000000000042097d2000000000000000000000000000000013ea00000000000000000118000000000f1278800007ee8fd80000000c540001832000111a6c300006ee0000000281e980000000000000000b1000012ba00000000e6076c0000000000000073e00001f003400000ec027d124a55800000001f5400000000001b4e000000000009da00000007840000000000000020807cc80005851204000107e10b0000000106200015c4857800000004fe00000000220000000021a0000000000000000018f27c0800000000000000000463a13461180001378000625800000000005e482dc4b680000b39f3006900007bd000000000000000a166eb020c867000000000004650000000000071a8000000029800013760000000039949a00000000002a260001ee007b1b3233a0dac20b886859f00009a5800043b8000000000047800008ab86ba00000000000000000000000000009df00009860000000050400000000000000000000094a239e5f01776000000014e123c1b8231c000000000000000000000000000000000000000000000000000014c83290fa40000000a0802440000000000000000024de00000000000e8a00000000000000aa4800004480006f4a060000000000016caa3315e82c00000204800046c033e000000011220f0000000056c80006d300007530da80000b9267929c6046000000029a0000034c2ac800000027fc000000093d80000000000000000000000000000dd2000000000022d8000000000010d6aae8000000000074f193423e99825ada37e0000000000297c00000000002ad63dd0b9a24d00000000e5a19e115e00000007bc80000001d883df9cd000000000000000
  | 51 => 0x80f8d3e360286e618000017a9cc0000000000002ea7c40000000298a0c1143a1e5904c000135c33180000000000000000000000003d90000000000000000002490000000000000000000001fd25950f8a00000001780000000000071222248b680003b7000000021680001b360f69246000000027700000000000000000046d0000000178800001d4000000000685b63ee00005e40b7400000002890000020a5a676811a67d89362560a49e7c687fe2de0fb400012320c316b499e2392000000000023740c5993c036863ea8a8000000000000000000000626000000000000003c700000000000000000000000009a700000000e10000000000000009cc22b80000000000000089f80002ea8b5889e2ad83f09568000152400022927381b520000000000217230700000000000000235a0001d9c000283c30400007ab970e2401f8c00026e02ac22fc94896b8000000002e122e00000000000000000000023d07ca000238c00000000000000000000086b80000000000000000081d80208951df25a7800074680007221b3c4ab2940000000040e800030280007f580000000000000124e0000b6c9e699c2694a95a0001c32000295200000008d0000000000000000000000000000000000000eda0000000000003600000000000000000268800000000000000a5b000000013a220728f47d680001ce133400028562e0000000000003c40000000000064611ea050000068e800037400000002aa26b500009ca93f200000000001f162fd80002b5000000000000001a4800000000000000000000000000006ac800000021cc000000000000000002440000000000000000000ada0ca1dfc000087000000002ad800000000004100000000257e7288000000137c000000000000000b0870405280000000000000000000008080000000682892676a0000aa2244800026ee000000000000004b200009808000000122c000000000000000000000430000007829de9e9800000012785310a7687b8000000000000001866b88bcc0000000000000000000005d41fcc0002aca00000000001d02000000000000001ce80000000e902f393460ce00000000000000000000000000001d50000095e000295000000000001a020001a500000db83db00009fe800091b000043280000000000000000000000001740f2435796ba182028c14699ae8b3a4a40909d400000354000000002480000000000000144000020ba04ea45200000000000000000078e45a160a000259013496a215280000000000677a098954a72600007845e8800056a80000000000000000000000004f480003f380009901202000000000000000000000714284c234aa862ca000000000000b48000000000000000001ee80000001c7c8fa98b400000000000000000000000000002988a44000
  | 52 => 0xd955801eaa5628a1f7e3ff800071780004b8800000000002e10000000000000025b09d380000001d22aaa000028322e40000000a55229600000008a60000000244c0000e6c00026460002ac091823c2000221e40c000000000004d600000000000000000000000006a821ca000248c000115a62700000000000000000000000000000454394000000000001b58000000000000000000000000000000081e89e2000175a5c60142325993a00000001a800006a70000000000000021588fe800000000001f500000000000000000056e096696880007f1249c7a580000001d920000000000000093f0aa8000000000016c8609000001a8c42254800000000004be800001a17aa7750000000000000000000001300000000099d253650a00000061fb200000003220000000000094580006b100000000000000229a8c091280001bd481580000000000000000000000009c1800076a95882da292678c9f720000000a76000000000000000000000170400000000001efe94e04060000000000000000009868870000439800000000007c80b82aaa9826000000000000003c200001d580004a900003f780009129f7a0000000000000000017e400000000000000000000000000000000000631a52c5ab127c46d80000000000000000000000000000000000233e54280000000eb01e89fe639c800019f80001b5121e00000000000000000000000000000000000000000000023d60000000000000000000000000000000000000000000000000000026a6e4000000000002d800005fb0000000019c05d8000000000000000000000000000007802109a000013c27099b545b18000000028a000188249600bc0002a2c00000000000f32000045e00000001fc02f4048083c0000e1a0000606000000000000000001f469e293e21b1a0be000000000000000000000000000073783cc5db800000013b400012a2000000000000000001cca000292400000000000000000000000000000000000000000020080000000df69f828ce0001c0c52501be000000000000000000e180001ebc0001f9c00003dc000000000000000000000179000016e100a00028aa0000c5a00000d60000f2c000039251f97960000000000214233980003bd8000000000000014d80000ede00000000000000000063c0000000000238e00000000000000901062413394604f180160000000000000075380002b788ec000090622481f2aa9a3d49a5275e00000000000000000194400000000000000000244e607800094a8cb430f1b9e00005a40000000000149000005725f5177200015e600000000e92982000100800006fc419000000012a600023720000000000274c5a580008ad80000000000a4c000000010105341eb40000000000000094200300001e3e5deaa4e45c1620000000
  | 53 => 0x3ec8000494000081400000000e360000000641000077d00000001aaa3340000000261c000000038992d0000000000000000000ff60000000000000000000000000fd600000000000bd800000000db8000000112200000000000000000000000000003981baa52917301658e1e47b23c0449900c9159c24442000055025b600000000000000000000000000005c400000000000000010c000000004a800000027b88a2000000000003d2000000000006a99c4a0001a2000000006a697b40001c982c298e4000000000000000000000000163c00000008ec0000000000000000000000000000000000007f200000000000000810000000000000001e90000000000000001a1000000000007c10940664a5d21651d4865a867c000084aa611d1c0000000000000088e8000000000000001f8000000000000000000000000000000000000001aee49a000021d800010305c600020ee501800033d0000000000000000000000000322874a000000000012883ca130600024c6000181608e23e60000000000143c000000000000003e09c9200000002ff000000000000000000a07000000000000000000000000054f80005a900004f9800000017b60001e8a51100005d98000000000000000000000000000000000000001561c8ea3580466fa9c9600000005bd8c742388000000092800000000000aae0000874000000000000000000000a4d000000018060000e08795000092102c80428d4e00000001ac800000000000000000000000000000d8000000000000000000000000000000000000000000000000006080000000000000000000027f472b8000000000045d87d2000073c000000000000000000000a0880000000000000000000000006ad800000000000000f92000000000000000000a3860c081a5ef80000000000000006200000004eb800051a8838000147400020b200000000000a468ea1a6000000000000000000000010a800013a012c000071200000005190ecc2bf00003c99508639800004d80007cb8000000000047c00007ca80007de00000000d8c00021d0000a0084cf800078b0000486800053080000000000000000000000000002090000000000000006330000000000000000000000c904001a7c8bc00004df800000000000000000581090e3a000000000d020d9803c00000000db0000a5880000000bc000000000000000087893000010c284400002208000000000096ca01a000169a0000e9892080000000000271006c59e8524000000034c00005ef00b40001086000000000007ae00000000000000573800000000001c0800049a8000000000000025fa000000000021f200024ae0000000000000000000001c900006c1000000000002b380002fc00000000000000000016f0bd69ee8b9c2df07001480000a4
  | 54 => 0x4e30000000000024d94b60002a622dc000054019da000154e00023aa00015caa39000013080004478000000204e00000002149ba63c0068c3bc87a685d000000001e60000000000000000022a600000000000000850000000000000000000000000087f80000000000000000090483b400027dc40380000000000000000077580000000acc2fba08639780a840e00006bb071a4538000a7280002bea342000000000000000001e140000040000212c000027600027e600000005de00000002abe48a8000000000000000000000000000000000000001608000687000026e2a8234d8e5c0000000248800000025bc00008a6743000000000000000000000000000003ba00000003fa0000000268ca1f0000000056a00002d04d9a59c0000000000000015d000050ba2e8000000000003743d28000000000064b0f9c00023d200000000000000105800000000007ce00000000e940000750000000000000000000000175800071300000000fc800000000000000000000056f20962fb292c00000000000000a27000001480002050a96940000098b1b34869800000000001288e680000818772800027000000002742000000000000000000000000000000000000001d3e0961d8000000000000000000000031a98ee715800000000009eb14387fd9c8c01400002310a2e88800009f38000000000000000a600000001c6124400007b4000216605c24a0000000023a80002d129cc29f8000000000093d0000000000000009a84bb8000a3f000000005a800000000000000381105c00020d80001ec86fb8000111074656300004ef25960ae80000001020000253c0f7800067f000000000000000000000000096ea87aa31800081a80000000ceca0f888a69c800000006187a31f2883508ba51d80000000000000000000000000001a2626026b600000006db8000000000000025e80000000000000053300000001ed4000000049d800000000009e000002330cda1ab800000006440000000000089e0cd8000a3f86ca05d00004b095b618c06d84a0a2b0919a614000000000000000000000518a4fa83f9d4a0001c2a06b800020580005a600000001f5e5db00004aa0000000000000000004ac8000000000075f800000020000000000a0e8000000000000000000000000543000099680009ea807016b800000002942e5000000000003f6922000000000000000000000000000000000000000228a0000000000000059127646ab91a000000000001c1e4588d924a5000000028fa000000000000003180000727800061f80000000000a82a36465e1a1600000000000000000000000000000000000000000000012ec0000f1a0001f900001c1096e000057f00004bc800064d909c38b80000000000000103c0001af40000000000000000000
  | 55 => 0x84c00000000001ab00001572000236e0000000279005600000000000000a17000000024d60000c7a3fc000067a0000000000074aa294000000008900000000000000000000000008b200000001ff29b4a4860000000000000087880004f68dae580000000000000000d3400000a4000000024700000000000161800000021f03d3000000001f4000000053e000000000005480000000288e2ee8000000000000000000000000000000090600000000000874800045e145c0000de81478000000000000000000000f84428000000000000000000000000000019f488d000000000000548000000101e3990c82000000011c00000000b0c14b800000000000000a120000bc800019a0000000000000000000000000000000000000000000000000000000000000000000000000000000002414000000000000000002894000068a00000000000000000000000000000000bdea6980000000000000000034223d000000000000000000000000007cc0000cc00000000000000000000000000000852285a00000000000000659849800000002d284aa745016232b1bfc4d282480001186000000000008840000000000000000025c0108800097c03e05f3a89a84a0daa619957a1c212d400000002420000000000000000004ec00000000ca83ad800000000000002318838800085b80001908000000000091f80000000ed22b8800000000008cb800033f062e44c800000000000001b4200000009650000000000086400000001f960000000000000020b00000000000000000068f00000001aba000000000000000000000a5da7d20000d8e7a2202c0000bc20002aec2e80cbe00000000000000755000022580000000000000000000000001148b380000000784a0de00000008339884000000000000000000000000000000000000000dce1e312e69cb81c01bd800000000000000000000025e0de9354390a9a40000000000000025e00000000000000000000007e600000004c600000e5077000000000001f7c000000086b0000000000020f8000000028800000003b2800000000000001e0c0000000678800000000006e2a49029f161697990a6000000000020e600007a4000087c00000004d0a12200000000000000472a59e0000000000000000000007d100000000000000205800000000000484000078695c80007160692000000000000000001b56ab100000182a8413f00005c880000000af400000000001e74000000000000000000000000000034e0000330800000000009620000000175e00000003c804c6000243c0000000000000000000000000000000000000000000000db266888a40001876000000000000000f5000000000000000c12000000026090e80000000000261a00000004da17a60
  | 56 => 0x845800007180005b68e1600022a012405be00000001b2000000000000001bca0e380002110d7000000000000000a4584ee00000000000000000280200000000000000a3200000000000000171e2cd8000901952e00026480002a800001728000000000000000000000000000055f00007a70748000097c0000000a640000000009c3802328000000000000007fa8000000000000005a000000000000000000103298f00002239c0e796a90616703fe000200c1128a5e00007440000cd2000000000000000000000000090a000000000000004470000000000076e800000000006de06ee00026cc851a0a2843001278a0ff26498b0878d288a0e206c411a8000a1c80000000000000183c31480006d900008838000388000000000000000000000000000000007b1291e00003c83eb226e6700000549a0ea1da800000002780000af87180000000201e000000000019fa000000000026980000000000000000000003bf00f0000000000000004640000000000000000000001578000000000000000001786000000000024dc0000000000155400000003798000000080c79e94ea62906e458a1ffc000000087000007c8a7ec00000003218000000000069180001669f767f6a09e000000000000006ec00005478c3a000000000000000000eb80000000000298e598a57c000232631100009af93526be03804c988300a1929618300000000000000000000017c65fa00000f923163e380000000000000023200000001e4000019c1a080000cf000019a679029047e2053c00004081b0800000000000000000aa384d40000f880769a000000000000000037a8000000000095c06ec000051848f8768000000000000001748000848000006a800095985888960000000000000000000000000000000000008780001ec2aa2800000000001b695f07448b520001ae800000aa00029fa000135a0002632370000000000001fe00000000000000016a00000000000efa00000001678000877000008f07c22e393860000000000116000000009cb0000024000000000000000000000000000022040000000000011a70080000000c483ce80000002aa45558000000000000000000000000000000065d094c00025a400000000000000000000000000000001bae00000008ad000014f8000000000000000006c7165c00011be000000000000000001f86000000095e00007af946826f97f40001d4220d80000000000000222c00013803c18000867800000000000000000120800000000000000000000000000000003ff000000000007f88bca52992cc822800000000002b80000000000000000002820000000110a00000000001124000000000000000000000262000000000000000000a9f800037880000000000000000000000000000000000000000026d00df8
  | 57 => 0x800083d800024f80000000000000000000000000ea964a26f0c64000000000000001d080009db00000001ba096195a600000009a0000084f2336000200a3c31a383a58dcc00024f00001fc000000008b49b720000a420000ae60000000041000000000000000000000273e00000000000000000000000000000000e6e000000044d23bc930a42a00000000000000000237000000000001c38000000024f189e000000000000000000000882800000000000000000000000000000000000f38000073e0001a981cca24e00000000000000000040a68b000035602d60000000000000000000000000800abc800000000000000000000000000000005218000000000000000000001cea58185f0000000000000000000000000119e00025d00000000000000099f000000012b00000000000183479e000000000001a6800028c195800000000000ac20000f34864839aa68905e0000000500a33c00005f600028ae000000053780000000000000047e000000000019f80000ed64ad0000000118800005220000000000000000029c480080000000c68aab80009cf17380000000000000000016d600000000002666000000000000000000000000000071b80000001b387ef1b7600014f651200002b90000000000000029c00000fa2000047a0001af286e00008b980000002864000000000000005370f2e000000052300000000000989956a00000000000000000000000000000000c0c0000000817033200024cea9300000000000000000000000000000646000000000000000000000000166c000000000000000001336000187200029da0000d0e671800018480000000000521000077a1ad630801843d097ee33ea1d80001afa0000000000000000000005c820945968000000074ca3080001360000000000000000000000a2028380001a6000000000000000000aa524e27b4800047928961c78000000000000000000c20000000000072080000000f869600c36000144e00000006e68000000000000000000001a4c0000aec00000000001d4656f8000000000000000005ca8b6e00001387a79dd08ca80000001f1800000006fb0436319958a01380000000000000000000000000001972000000000000000000000000253a2a3800021c8000638000000000000001da4000000003f0000000000068380000000000000000000000000d200000000000000000000000009890bae00000006de896089b0000058000072ca6ce7b901b682900000e09e368f880007b59bf40000000000000000007b000000000000000000000012d0000a110000000000015f82de000000000000000000000000000000000000000000000000006c9efa3bb1f5000023de75580000001b14000000000000004a2800000016c09e4213667fa8c00000000820800081c294c
  | 58 => 0x6bc000000000004b18000000000000019160000c8e4c2960e29e008e09c00000578bd0000000000000002320000000000050600008c3031e00000006c5800081080002879048000214c0001912000000088880008869810567885a000000000000002bc8000416000000027520000000000000079400005f0800000024e8000000047d1b5a69a279200000004ca800031d908800000005cc96d862f91fc00000000000000000000000000000002690a9f0000000000000000000000000000000000000000000000347800074d0000000000046e000000019380000000a79000000000004ab98801f90c622a31864312a5ac4f00b34000000079a000000000000001a1400028407808000000000080c256a0000000000000090d800073f0000000000000002ac000000000000007f183ce0000284000000000000003440000000000000000000000000000000000023060000000000044600012340000000000000000004c4000000003a92b60000e465ac80000000e28000000000002e299da5d64aa97f8000000018b0000000000000000000000000a460d2c00000000000000000000042780000000474000000000000000001d9e0000000254000000015f4a5126ac407275c000000000000000000000000000000014a80000000000000000000001a023322cc9c660001c8a8d18e3069980000000a9488a80000000d141a882fa0000000a8f1d3600000000001e5c0000600a9ea78488c021481500009a380000000e9c000000000000000001fee28101e261e00000001ee200000000000000000000000000000000000000000000000000000000000000000000000000000a6c00004dc00000001de00000a5861880009be23765c700004c08f1e000000034c8bbc00027d8000000009e800077399b863d123a1ef1ffa7948000000000000000000000000000000000000000000000000000063f000000000000000000000142a00000000000000a38277466127d498b800000025de00016d4737131c000290200000000000000230000000024641c58000000000046725d800008a00000000000097e516809e00000004f5000000024307ac00008ef8a1000000000000000000293c00000000000000000000055217840000000000000000000000002a1000000008fb10fe00027f604088f80001e4666c888835f0d6ea9a80008fb80000f987f663a00000000000000000000009dea8e8000000137200000006ad008a0000c9e7ae01d68790000000152878a96d2a741a3e8da1cb80001d080000000000000000011a80000000a6180000001fb66bf1c86196800000028b8000000019300000000000000000000000007e48000000000000006de0000ff800023e800000008f70000000000089200000000a7a0001dae0000000000000000000001ec
  | 59 => 0x3100000000000231203f80000000bda00000000000000570835c00000000000000000121c000000000028160000000000000000000000000b3071189a457eaa466488000000077c0000000000000000000000001e0e9f880000001e9805f0a480000000000073487b0000000122400000001538f8000003fa000000016100000000ed09dc80000630204000000000000000000000000036a364000013700005c318b88e985c4a231fd0000179a6bd8000000000083200000000000000000000026c4000000000000000000000000000000000003b380008b71f122329bba192a81a1fa9be837b951469891929f7a04460e0c4e000104a01080000000000000000000009b20000000000000008f800000000002c68000751000400000000000abc388800087f000049080000000000000245a00018f01d4a2907fd18c20000000000000015a0000000000057b2670000197625c000000000000001080000000000000002d6800089400008d38ef84f30000a340000000177c0001ada2a880002fa91108a300000001b688198000000000000000000c3a81000000000c50d6c000000000000000001e6a00000000000000000000000001b8000213265c000075e8000000162a013085c55300000002428638a22684982ae00000000000000153000000000000000268000000000000000e8a3f000000000000000000000000000008ac80008de8000000000000023ba00000000000000000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87d84dd5624400117f08baac4880062f21175589100046fc1aeab1220168dc835d5624400187eebba2c4880030f1d774589100061fc2ee8b122000c3c85dd162440010ff0aba2c48800a1f21574589100046fc1ae8b1220168dc835d162440011f700ba2c4880030fdd474589100061e3a8e8b12200087e87d5162440050f90faa2c4880030fdd3545891000e1e3a6a8b12200087e8755162440010f90eaa2c4880030fdd1545891000e1e3a2a8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f54dcd62440018baa9b9ac48800317dd473589100062e3a8e6b122000c9f741cd6244001938e839ac48800317d5073589100062eaa0e6b122000ccc73dc962440019a8e7b8ac4880032e1d3705891000477c3ac43122000acc8358862440010ff08ba8c48800a1fe1f54189100043ec3ea8312208ec7970d5062440010ff0eaa0c4880021f61d541891046e3cb82a8312200dccc325cc62440071f10cb86648800e3e219708c9100043fc2aec992200287c855d9324400117f08bb264880062f211764c9100047bc0aec992200287e851d932440010fb0a3b264880021fe15760c9100143e42aec19220008bf845d8324400317908bb06488002b3a19320c910005664326419220048f4865c43244001b8a64b88648800e3e219700c9100b66c31ae0192200dce8625c0324400199ec639262880033318c724c5100066639ec490a2000ccc7318921440010ff0abb2608800a1f215764c1100045fc22ec98220018bc845d930440011df04bb260880363b209764c1100063c3a8ec9822000cb8741d930440018f0edbaa60880032e1db744c110006b9ba8e2982200087f855d920440050f90abb240880022fe11764811000c5e422ec90220008df835d9204402d1b906bb240880123da1b71481100063c3a8ec9022000cb8741d920440018f0edbaa40880032e1db744811001c7c432e69022000d73751c520440050fd0fbaac6080021f6137558c1029c3f438eab18200087f855d163040050f90aba2c6080123e2017458c100043f43ea8b18200287c87d5163040010fd0eaa2c6080021f21d5458c100162e3aca6b1820048dc8754d63040091b90ea1ac60800a1fa1f75588100043ec26eab10204b87e871d562040010ff0aba2c40800a1f21574588100247c402e8b10200087e87d5162040050f90faa2c4080021fa1d54588100043e43aa8b102002c6c7594962040091d90ea92c4080123b21d42588100b62f31aeb9902000c5d7558f320401b8dcc4bac64080031b5d5628c8100043fc2aec990200287c855d932040071e902bb264080123721d634c81006d66412c699020048ec87589320402d59906b1264080021fe15760c8100143e42aec190200dccf764c8320400199aec9906408162f1205320c810
  | 1 => 0xb0e212cb082469ee0171596100043f43e82b2c200087d87d05658400187ae9a0acb080030f5d141596100053dc0282b2c2004a788050565841218f4e1aa4c7080070f9d15498e100061eba2a931c208fc7a7055263840091b906b94c70805b330c97298e100061fba2a8b1c2001c3c7455163840091b90ea1ac70800a1fa177258e100043ec2ee4b1c2090c7a70d52628400387ce8aa4c5080030f5d15498a1047e3d382a931420048ec825ce628401b99864b9cc5080030fdd15458a1000e1e3a2a8b14200287e85dcd62840010fb0bb9ac5080123b21d4258a100143f42aed994200087f865d732840010ff0eb2e65080021f61d65cca1002477c3ac59942004cea7058b32840050fd0abb465080021fe19758ca100043fc3acb194200087d8759632840091bf0eb1c6508013369c1638ca100247d406ec9942000c7665dc532840098f4e0b286508002b3e19320ca1000566c32641942084e4e654c83284001c9aca9906508162f1205320ca100063cb2ae0194200087d86dd531840010f90eb2a63080031b997724c61000636b2ee498c2000c6e651c931840018daca39263080033398c724c61000666b18e498c200087d86dd521840010f90eb2a43080031799773486100062eb2ee690c2000c5e651cd21840018baca39a4308003331ce62486100066639ac490c2000cb874dd93084001970e9bb2410800e7c20573482100043fc2ae5b1a200287c855cb634400387ce8aa4c6880030f5d15498d100043fc2ae331a200287c855c663440010ff0ab84c68800a1f2157098d100045fc22e131a20018bc845c263440010fb09baac6880022fe117558d1000c5e422eab1a20008ef825d5634401b1d904baac6880030fdd77458d100061e3aee8b1a2000c3f85dd163440018790bba2c6880021fe157458d100143e42ae8b1a20008ef825d1634401b1d904ba2c6880023ee017458d100061fba8e8b1a2000c3c751d163440010fd0faa2c68800a1f21f5458d100061fba6a8b1a2001c3c74d5163440010fd0eaa2c6880021f21d5458d100061fba2a8b1a2001c3c7455163440018deebb92c6880031b1d77258d1000657ba6e4b1a2000cac74dc963440018dea9b92c6880031b5537258d1000637ba8e4b1a2000c6c751c9634400195ee8392c6880032b1d07258d1000667b98e4b1a2000c6f541c963440018daa8392c688003391cb7158d100065c3a6e0b1a20008df8758c634400159904b18c6880021fe117518d100143fc3ea831a200087d87d50634411d8f2e1aa0c6880021fe1d5418d100043ec3aa831a208dc7970550634402d99864b90c6880021fe1573d89100143e42ae7b122001c3e74552624400187ae8aa4c4880021fe1571989100143e42ae3312200087f855c262440050f90ab84c4880022fe11709891000c5e422e13122000
  | 2 => 0x473484200063c3aeec9004000cb874dd920080018f70bbb240100031e21776480200063daa6ec9004000c7954dd9200801b9d4a5bb240100033a54b76480200063dbb6ea9004000cbb76dd1200811b0fb0f3a2cb880030fdd2745971001d3b40ce8b2e2097a75819d165c400187f08ba2cb8823a1fa1c74597100062fb9ce6b2e200087e87d0d65c40010fb0fa1acb880021fa1c43597100043ec3886b2e2000c6f729c965c40010fd0fa12cb880021f61f42597100043f43884b2e200087d8710965c412d4ef02b82cb880021fa1f40597100043ec3e80b2e2000c3f759d564c4089575013aac988002ae602755931046d1ec3ceab262000e3a809d564c4001c73013aac9880030fe1d755931046e1fb8aeab26208dc3d715d564c400187ce0baac9880030f1c175593104751f428eab262000a3e85dcd64c400147b0bb9ac988002aee0173593102255c402e6b262000a3e851cd64c400147b0a39ac98800387d4e53593100051f42ee4b262000a3d85dc964c400157700b92c988112ae20172593100051f428e4b262000a3d851c964c412b56f02b82c9880022fa1f50593100045ec3ea0b262044e3a50d4164c40050fd0bb92c7880021f6177258f100143f42ee6b16200087d85dcd62c40050fd0abb665880021fe1975ccb100061f322eb996200087f8759732c40010fb0eb2e65880030f9d564ccb100061ebaac9996200287e855da32c40010ff0cbac65880030f991758cb100043fc3acb196200087d8759632c400187ceab2465880030f5d5648cb1001c6e43ac6996200dacc8258d32c40071d90eb12658805ab320d624cb1001e3b38aca1962003cb67159032c401b99eec9906588003335d9320cb104272732a641962000e4d654c832c4107d1cc89906588003a3591320cb100063ab2ae21962000cb5645c432c4001b8a64b8865880021f61b754c3100061f326ea986200087c8759530c4001878e8b2a61880022f61b744c3100061f32ee89862000c3d65dd130c40011790eb2261880030fdd5644c3100061e3aac8986200087d86dd520c400187cc9baa41880021f21d65483100061e3a2ca90620008bd86dd120c400187ccbba241880030f59774483100045e43ac89062000c3f7559120c4001878eab22418823e1f61e74596100061fba4e8b2c2094a7b805d165840094f100ba2cb080030fe1174596100063dc02e8b2c208fc78805d1658411f87c80ba2cb0823f0f10174596104843f438e8b2c2000c3d741d165840018bee739acb080129ea02735961049d3cc04e6b2c200087e87d0d65840010fb0fa1acb080129ea0243596100053cc0486b2c200087e8710d65840010fb0e21acb080129ea0272596104953cc04e4b2c200087e87d0965840010fb0fa12cb080129ea0242596100053cc0484b2c200087e8710965840010f
  | 3 => 0xd90a409a87e86dd52148001878c9baa42902661fa1f65485200061fbaec890a4000c3c75d9121480018becbb9a42900031719773485200064fb26e690a4000c9c64dcd21480018beca39a42900031719473485200064fb20e690a4000c9c641cd21480b19a8c239a4290003351cf61485200065c326e090a400287c859d82148003179093b042900123e20276085201043e432ea10a4000c3c645d421480010ff0fb28429004a1f61f65085200061f3a6ca10a404bc7a70d94214803f1790cba042900030fd9574085200061e32ae810a40008bf87d90214802317b0fb2042900030f9d764085200061ebaec810a404acba70d9021480018becb39842900031719673085200064fb24e610a4000c9c649cc21480018becab9842900031719573085200064fb22e610a4000c9c645cc214802d998c6b9660900021fe15764c1200143e42aec98240008bf845d9304800317908bb2609000a1f214764c12000c5e420ec982400087e86dd53048001878c9baa609014f5a083754c1200043f43eca982400087c87d953048001878e9b2a609012f960c3654c1200045f436e89824000c3f65dd13048001878cbba260900022fa1f644c1200045e43ec89824000c3f75d913048001878ebb22609012f1e9db65c812025f35b16cb902404acba76d93204811f0fb0f3a2ca100030fdd274594204c53dc02e8b284004a78805d1650800187f08ba2ca100031ee01745942047e3c402e8b28408fc3e405d1650811f87880ba2ca102421fa1c74594200062fb9ce6b28400087e87d0d65080010fb0fa1aca100129ea0243594200053cc0486b28400087e8710d65080010fb0e21aca1003e1fa1f42594200043ec3e84b284000a3e841c5650800147b0838aca100021fa1f41594200043ec3e82b284000c3d74d05650800187ae8a0aca100029ee0141594200253c40282b28400087e8710565080010fb0e20aca100021fe157198c200143e42ae331840048dc8750d63080050fd0abb664100da1fe1975cc82007c3fc3acb990400087d87597320801bc9864b2a64100123d21d41584200071aaa282b08400287c85dd931080010ff0abb2621000a1f215764c4202cc77c12ec988400087d86dd531080010fd0eb2a62100021f21d654c42006e36392ca988400dccc7298d310801b998e4b1a62100031b997724c42000636b2ee4988400287e855d831080071db04bb0621000e3e601760c4200043fc32ea188400087f8759431080010fb0eb2862100030f9d1650c42006e37392ca1884004c7a70594310800187ccaba062100030f595740c4200063732ae41884000c6d655c831080018f4cab8062100031e595700c4200143e42eec908402387d86dd521080010fd0eb2a421003e1f21d65484200062f32ee69084000c5d65dcd21080018bcca39a42100031759
  | 4 => 0x3480018e8ebb8ac6900032ddd37158d200065a3a6e2b1a4000c7754dc563480018eaa9b8ac6900031ddd47158d200063a3a8e2b1a4000cb7741c56348001968e838ac69000335dcc7158d2000673b90e2b1a40008df8758c63480015a902b18c6900021fe157118d200143e42ae231a409a87c865d73248001878c8bae649012e1fe1f65cc9200043ec3ecb9924000c3e75d93324800187aebb2664900032e19170cc9200143e42ced192403587c865d63248001878c8bac64900375a081758c9200043fc3ecb192401287d87d96324800187cebb2464900030f5d7648c92006d66410c69924000e4f654c83248109c98ca9906490003a3d91320c92041f46322641924000c3f745536148003878e8aa6c2900030f9d365985200061f3a0cb30a4000c3f655d26148001878caba4c2900030f9d764985200061ebaec930a4000c3e75192614800187aea324c29000a1fa1b75585200043f43ecab0a4000c3c74d9561480010fd0e32ac2900030f1d0655852000c5f436e8b0a4000c3f65dd16148001878cbba2c2900022fa1f64585200061fbaec8b0a4000c3c75d91614800117d0e322c2900030fdd464585200061e3a8c8b0a4000c5f65dcd61480018b8cbb9ac29000327d9373585200064e326e6b0a4000c5f651cd61480018b8ca39ac29000327d9073585200064e320e6b0a40008f78758461480015a906b08c2900021fe1576cc5200143e42aed98a40008bf845db314800317908bb662900021fe15768c5200143e42aed18a40008bf845da314800317908bb4629000a1fa17764c5200043ec2eec98a40018be84dd9314800117b09bb2629000a1fa16764c5200043ec2cec98a400287c851d9314801b1d9043b262900021fa1b754c5200061e326ea98a400087e87d9531480010f90fb2a62900030fdd7644c5200061e3aec898a4000c6f65dc931480018d8cbb9262900032bd93724c52000656326e498a4000c6f651c931480018d8ca39262900032bd90724c52000656320e498a400287c859d83148003179093b0629000e3b20a760c5200247c404ec18a400087f855d831480050f90abb062900022fe11760c52000c5e422ec18a400087c865d43148001878c8ba862900021fe1f650c5200043ec3eca18a4000c3e74d9431480978f4e1b2862900022f219740c5200061fb2ae818a4000c3c655d0314800117f0fb2062900022f61f640c5200061f3aec818a4000c3d75d903148095974e1b2062900031bd96720c5200063632ce418a4000caf649c83148001958c939062900031bd95720c5200063632ae418a4000caf645c83148001958c8b90629000333d8d720c5200b66631ae418a4000ce572d8431480018f6cab8062900031e195700c5200065db22e018a4000cb8645c031480019b6c6b8062900033cd85700c52001c7cc04e
  | 5 => 0x38b19242d952025d3643285b2a4000e2c6450b65480010fb0f3a6ca900030fe1174d95200043f438e9b2a4000c3d741d365481374dd043a6ca9012e9b60874d95200062eb98e7b2a400087e87d0f65480010fb0fa1eca900021fa1c43d95200043ec3887b2a404b87e87d0b65480010fb0fa16ca900021fa1c42d95200943ec3885b2a4000a3e849c7654800147b0938eca9012e9ea0071d95200053cc00e3b2a400087e87d0765480010fb0fa0eca900030fdd341d95200061fba283b2a400087e8710765480010fb0e20eca9011a9ba0b70d95200043f43e81b2a400087d87d03654800147d0dbaec8900030f9db75d91200051f430ebb224000c3e761d7644800187cedb2ec8900022f61e65d91200051f42ccbb2240008bf87597644800147d0c32ec8900030f9d865d91200061f386ebb224000c3c70dd7644800147d0b3aec8900030f5d475d91202555d400ebb224000ab9801d7644800147d0e3aec8900030fa1c75d91200071d400ebb224000e39801d7644809557501b9ec890002ae60373d91200051f42ce7b224000a3d859cf644800147f0ab9ec8900028f21573d91200070fa9ca7b224000e2f5294b644800187eebb8ec8900028fa1671d91200051ec2ce3b224000a3f855c764480014790ab8ec8900030fdd571d91202555d400e3b224000ab9801c7644800117d0e28ec8900022f61c51d912023d57416e1b2240008be87d43644800117b0fa86c89012b8e94350d912006c7cc06e9b1a4000c3e74d96634800187ce832cc6900030fd957498d200061e32ae931a4000c3e75d92634800187aebb24c6900030f9d46498d200061eba8c931a400087f845d6634800187d0aba4c6900030f6157498d200143fc3ea931a400087d87d52634800387ce9aa4c6900030f5d35498d200043fc3aa931a400087d87552634800387ce8aa4c6900030f5d15498d200043f43ecab1a4000c3c74d9563480010fd0e32ac6900030f1d06558d200061fb2ee8b1a4000c3c65dd1634800117d0fb22c6900030fdd76458d200061e3aec8b1a40008be87191634800187eea322c6900030f1d46458d200063bb2ee2b1a4000c7465dc5634800196ec9b8ac6900032d1937158d200063bb28e2b1a4000c74651c5634800196ec838ac6900032d1907158d200043ec26eab1a40008bf845d5634800317908baac6900023de057558d2001c7a40aeab1a4000c3f75dd16348001878ebba2c6900030fe177458d200061e42ee8b1a400087f855d163480050f90aba2c6900023de057458d2001c7a40ae8b1a4000c3f751d16348001878ea3a2c6900021fa1f5458d200143e43ea8b1a4000c3f74d516348003878e9aa2c69023b1d1c75458d200043f43aa8b1a400087c87551634800187ee8aa2c6900070f1d15458d2046e3a38aa8b1a4000c7775dc56
  | 6 => 0x43ec3e82b286000c3d74d05650c00187ae8a0aca180029ee0141594300253c40282b28600087e87105650c0010fb0e20aca180021fe1571988300143e42ae331060048ec87509620c0050fd0abb464180d61fe19758c8300c43fc3acb190600087d87596320c02dc9864b2a64180123d21d41584300071aaa282b08600287c85dd9310c0570fb0dbaa62180021fa1d654c4300c43e43aca9886000c6e65dc9310c0018dacbb9262180031b994724c43000636b28e4988600287c85dd9210c0010ff0abb2421800a1f215764843031c6fc1aec908600087d86dd5210c0010fd0eb2a42180021f21d65484300b62e39aca9086000c5e65dcd210c0018bacbb9a421805b331ce62484300b66639ac4908600287e855d8210c0071bb06bb042180021fe1975084300043fc3aca108600087d87594210c00187ce8b28421805b179cd65084300263d382ca1086000c3e655d0210c00187acaba042180031799573084300062eb2ae61086000c7a655c0210c0018f2cab8042180031e1d7764c0300065c3a6ec9806000c7b85dd9300c0018f10bbb260180031ed53764c0300063caa6ec9806016cda53dd9300c0019b2a7bb260180031eddb754c0300065dbb6e8980600087f845d763c800187d0aba6c7900030f61574d8f200143fc3ea9b1e400087d87d5363c800387ce9aa6c7900030f5d354d8f200043fc3aa9b1e400087d8755363c800387ce8aa6c7900030f5d154d8f200043fc22eb31e400287f87d5263c80010fb0faa4c7900021fe1d5498f200043ec3aa931e4001c3e7455063c800187ae8aa0c7900021fe157118f200143e42ae231e400087d84dd561c800147b083aac3900021fe1574587200143e42ae8b0e400087e87d5161c80050f90faa2c3900021fa1d54587200043e43aa8b0e4001c3e7455161c800187ae8aa2c3900021fe15768c7200143e42aed18e400087f855d931c80050f90abb26390037331ca634c72006e66392c698e400dccc7258d30c800387ce8aa4c7100030f5d15498e200043fc2ae331c400287c855c663880050fd0fbaac7100021f6137558e2029c3f438eab1c400087f855d163880050f90aba2c7100123e2017458e200043f43ea8b1c400287c87d5163880010fd0eaa2c7100021f21d5458e200162e3aca6b1c40048dc8754d63880091b90ea1ac71005b1798d75cca200062ebaac799440048f4875056188001c6aa8a0ac3100021fe1576cc6200143e42aed98c400087f855d931880050f90abb2631005b1798d750c6200b64f31ae818c4000c5d7558c318800193ae8b186310013369c1630c6200b66731ae418c4000ccd635c831880010fd0dba6ca9000a1fe1f64d95200061eba6c9b2a400087d8799365480010ff0eb26ca9004a1f61c64d95200061eba0c9b2a4000c3d871936548001c5b04326ca9
  | 7 => 0xac64dc9614c0018deca392c2980031b194725853000657b20e4b0a6000cac641c9614c0011ef0eb08c298002b920961185304f43f436ea98a6000c3c64dd5314c13b0fd0fb2a62980030fdd7644c5300061e3aec898a6000c6f65dc9314c0018d8cbb9262980032bd93724c53000656326e498a6000c6f651c9314c0018d8ca39262980032bd90724c53000656320e498a6058ce4611c9314c0019c8e5b0a62980032e193704c5300143e42cec18a60018bc849d8314c0510f90cba862980030f191750c5300043fc3eca18a601b87d87d94314c00187ce9b28629814f1e9c3650c53013c5e432e818a6000c3f655d0314c001878caba062980022fe1f640c5300d45ec3ec818a6000c3e75d90314c00187aebb20629814b2e9c3640c53000637b2ce418a6000c6c659c8314c00195ec939062980032b192720c53000637b2ae418a6000c6c655c8314c00195ec8b9062980032b191720c5300043fc2aed90a600287c855db214c00117f08bb642980062f21176c85300043fc2aed10a600287c855da214c00117f08bb442980062f21176885300143f42eec90a600087d85dd9214c00317d09bb242980022f61376485300143f42cec90a600087d859d9214c0050f90a3b2429805a3720c76485300043f436ea90a6000c3c64dd5214c0010fd0fb2a42980021f21f65485300061fbaec890a6000c3c75d91214c0018becbb9a42980031719773485300064fb26e690a6000c9c64dcd214c0018beca39a42980031719473485300064fb20e690a6000c9c641cd214c0050f90b3b042980062f212760853001c6e41cec10a600087f855d8214c0050f90abb042980022fe11760853000c5e422ec10a600087c865d4214c001878c8ba842980021fe1f65085300043ec3eca10a6000c3e74d94214c0a78f4e1b2842980022f21974085300061fb2ae810a6000c3c655d0214c00117f0fb2042980022f61f64085300061f3aec810a6000c3d75d90214c0a5974e1b20429800317d9673085300062e32ce610a6000c9f649cc214c001938c9398429800317d9573085300062e32ae610a6000c9f645cc214c001938c8b98429803733189730853000666b9ec410a6000cd573d84214c0018f6cab8042980031e19570085300065db22e010a6000cb8645c0214c0019d6c4b8042980033cd85700853029e3d3b6cb9826053e5b63d97304c0a5974edb26609823e1f61e74594300061fba4e8b28609ca7b805d1650c0094f100ba2ca180030fe1174594300063dc02e8b28608fc78805d1650c11f87c80ba2ca1823f0f10174594304843f438e8b28601887e87d0d650c0010fb0fa1aca180021fa1f42594300043ec3e84b286004a7a80909650c0014f301212ca180021fa1c42594300043ec3884b286000a3e841c5650c00147b0838aca180021fa1f41594300
  | 8 => 0xe21eca9806e1f61c43d953000636b90e5b2a600087e87d0b654c0010fb0fa16ca980021fa1c42d95300043ec3885b2a6000a3e849c7654c00147b0938eca9814e9ea0071d95300053cc00e3b2a600087e87d07654c0010fb0fa0eca980030fdd341d95300061fba283b2a600087e87107654c0010fb0e20eca9813a97a0f70d95300043f43e81b2a600087d87d03654c00147d0dbaec8980030f9db75d91300051f430ebb226000c3e761d7644c00187cedb2ec8980022f61e65d91300051f42ccbb2260008bf87597644c00147d0c32ec8980030f9d865d91300061f386ebb226000c3c70dd7644c00147d0b3aec8980030f5d475d91302955d400ebb226000ab9801d7644c00147d0e3aec8980030fa1c75d91300071d400ebb226000e39801d7644c001c3ea729ec89814aaea0372d91300055cc06e5b226000a3e859cb644c00147b0b396c8980028fe1572d91300051e42ae5b226000c3f75dc7644c00147d0b38ec8980028f61671d91300051fc2ae3b226000a3c855c7644c00187eeab8ec89814aaea0071d91300055cc00e3b2260008be87147644c00117b0e28ec89813ea7a0f70d91300045f43ea1b2260008bd87d43644c0a5c74a1a86c89805a3e60374d89300061f3a6cb3126000c3e74196624c00187ecaba4c4980030f19574989300061f3aec93126000c3d75d92624c00187cea324c4980030f5d464989300043f43ecab126000c3c74d95624c0010fd0e32ac4980030f1d065589300061fb2ee8b126000c3c65dd1624c00117d0fb22c4980030fdd764589300061e3aec8b1260008be87191624c00187eea322c4980030f1d464589300063bb2ee2b126000c7465dc5624c00196ec9b8ac4980032d19371589300063bb28e2b126000c74651c5624c00196ec838ac4980032d190715893000477c3ac43126000ae481588624c0010ff0ab88c49800a1f21571189300143e42ced992603687c865d7324c001878c8bae649805b560c175cc9300043fc3ecb992601b87d87d97324c00187cebb2664980030f5d764cc9304f43e432eb1926000c3c645d6324c0010fb0fb2c64980030f9d7648c9300061ebaec91926000cb8645c2324c001c9eca990649821393195320c93000747b22641926083e8c644c8324c00187ee8aa6c2980070f1d154d85300061f3a6cb30a6000c3e74196614c00187ecaba4c2980030f19574985300061f3aec930a6000c3d75d92614c00187cea324c2980030f5d464985300143f436eab0a600087e87d95614c001878e9b2ac2980021fa1c65585300061e3a0cab0a60018be86dd1614c00187ecbba2c2980030f19774585300045f43ec8b0a6000c3f75d91614c001878ebb22c2980022fa1c64585300061fba8c8b0a6000c3c75191614c0018decbb92c2980031b197725853000657b26e4b0a6000c
  | 9 => 0x43980210053d42e853004200a7985d0a60084014f50b994c0108029e617329802106f64192653004200c3f745516008403878e8aa2c01080e3ea1f50580210055d426a0b004200ab984d4160084071f10ea82c01080e3ea1f40580210053d42e80b004200a7985d016008401c72a9202c01080e3e21d40580210053d42880b004200a79851016008401c72a8202c010802b6a0c40580210056cc1880b00420daea8210160084075e502202c010802aea1275580210055cc24eab004200a7a859d160084014f30b3a2c0108029ea1474580210053cc28e8b004200ada831d160084015b3063a2c010836baa08745802100574c10e8b004203af2811d160084015e3023a2c0108038ed5254580210071dc22a8b004200e3b745516008401c70e8aa2c010a378ed05545802146f1ca0aa8b004200a7b855cd60084014f10ab9ac010802aee1173580210055c422e6b00420dae8825cd60084075e102b9ac0108029ea1473580210053cc28e6b00420daea82d4d60084015d305a9ac01080396d4e53580210053d42e86b004200a7985d0d600841b5d505a1ac010802ba60b435802101d7940e86b004200af181d0d60084014f50a21ac0108029e614435802106f35296a4b004200a7a85d0960084014f30ba12c0108029ea1732580210053cc2e64b00420dec8324c960084010ff08bacc59800a1fe1f5498b300043ec3ea9316600087f8755262cc0010fb0eaa4c5980021f61375587300051ec20eab0e600087f855d161cc0050f90aba2c3980021fa1f54587300143e43ea8b0e600087e8755161cc0010f90eaa2c3980070f9d154587300061eba2a8b0e600087f855da21cc0050f90abb443980021fe1576487300143e42aec90e6016ccc7398921cc02d998e6b1243980070f9d15498a300061eba2a9314600087f855c6628c0050f90ab8cc51800a1fa1f7558a300043ec26eab14600087f855d1628c0050f90aba2c5180123e2017458a300043f43ea8b14600287c87d51628c0010fd0eaa2c5180021f21d5458a30016363aca4b1460048ec87549628c0091d90ea12c5180371b989758ca3000636baac519460048f487505618c001c6aa8a0ac3180021fe1576c86300143e42aed90c600087f855d9218c0050f90abb243180371b989750863006e57312e810c600dcce625cc218c0018daeab1043180032b5d1620863000666b9ac410c6004cea70588218c0010fd0dba6ca9800a1fe1f64d95300061eba6c9b2a600087d87993654c0010ff0eb26ca9806e1f61c64d95300061eba0c9b2a6000c3d87193654c001c3b06326ca980038719243d953029d2e43287b2a6000e1c6450f654c0010fb0f3a6ca980030fe1174d95300043f438e9b2a6000c3d741d3654c13f4bd063a6ca9814e9760c74d953029c3f43e87b2a600087d87d0f654c0010fd
  | 10 => 0xb1842038dc8754d630841b59904a9ac61080e37a1f4358c210052f42e86b184200a5d85d0d630841b59d05a1ac61080eb5a074358c2101c6e43a86b18420dacc8250d63084014bd0a21ac610802976144358c210062fbaceab18420dace829d5630840159b053aac610802b3e097558c2106d66412eab184200ad7815d563084075a902baac61080297a167458c210052ec2ce8b18420dace829d1630840159b053a2c61080eb5a067458c210056ac0ce8b184200acf825d1630841b59904ba2c61080297a147458c210052ec28e8b18428ee4f21d51630851dc9a43aa2c610a36976165458c210070faa4a8b184200e1f84551630851bc3e82aa2c610a37875055458c2146f2790aa8b18428de4d21551630851d4bd0a2a2c61080393d507258c2100726aa0e4b184258cce711c963084b1998e2392c6108379394b5258c210052f42e84b184200a5d85d09630841b59d05382c61080297e157058c210052e42ae0b184200a9f845c1630840153908b82c610836b32097058c2101d6a40ae0b184200a5e851c163084014bb0a382c610802a7a135058c210054ec26a0b184200a5e85d0163084014bb0ba02c610803875524058c210046f43880b1842008dd8710163084014bd0a202c610802976144058c210070eaa080b18420dace82101630840159b04202c61080eb5a044058c210056ac0880b18420287e855db320846d0ff0cbae64108030f99175cc8210b62f31aeb990422087f8759732084010fb0eb2e64108030f9d564cc8210061ebaac99904200c5e7558f32084018baeab1e64108031b9d576cc82106e6739aed9904200c6e855db32084018db0abb664108031bd5176cc82100636aa2ed990420dcce835db32084b399b06bb6641096733cc576cc8212ce6698aed9904200c6d765d7320841b99ce6b1e6410803939d563cc82100726baac79904200e4f5458f3208401c9aa8b1e641096733dc563cc8212ce66b8ac7990420de4c32595320841bd1864b226410836b320a634c82106d66412c69904200c6f545d832084018daa8bb0641083733a0d760c82106e66c1aec1904258cce315d832084b199862bb064109663be1d630c8212ce6739ac6190420dacf8758c32084b399f0eb18641080393d51630c82100726aa2c61904258ace8158c32084b159902b18641083733dc5630c8212c666b8ac61904200c7475dd921084018ef0bbb242108031d21776484210063baa6ec9084200c7554dd921084019af07bb242108033520f76484210063bbb6ea9084200cd776dcd21084019aeec39a4210803551d473484212c6e3b90e69084200e3b549526008401c7708aa4c010a3f8edd1549802147f1c3a2a9300428de3b41552600851bc7282aa4c01080396d4e53980210053d42e873004200a7985d0e60084014f50a21cc0108029e614
  | 11 => 0x4840187ae8aa6c0908038e55040d812100574c1081b024200af18110360484018becb39cc0908031719673981210062fb2ae73024200c5c655ce60484018bcebb1cc090803175d763981210062f3a8c73024200c5d7518e60484050fd0dbaac09099e1f21b75581210043f43ecab024200c3c74d9560484010fd0e32ac0908030f1d065581210061fb2ee8b024200c3c65dd160484018becbb9ac0908031719773581210062fb28e6b024200c5c651cd60484011bd0fb1ac09080317dd763581210062e3aec6b024200c9f74d8d6048401938e9b1ac09080237a1c63581210062fba8c6b024200c5c7518d604840193ee831ac090803271d063581210047dc3ac03024200ab884580604851b0fb0f3a2ca108030fdd274594210061fc22e8b28428e87e871d165084018bee739aca10a8a9be09735942106d36412e6b2842a1a77815cd65084074e902b9aca108021fa1f43594210043ec3e86b28420087e8710d65084010fb0e21aca108821fa1f42594210043ec3e84b284200a3e84dc1650840147b09b82ca108021fa1f40594210043ec3e80b284200c3d7490165084010fd0e202ca108021f61c40594210061eba080b284200a5e8310165084014bb06202ca108369ba08405942100536c1080b284203a768110165084014eb02202ca108030fdd6755902146d1ec3ceab204200c3f875d5640851b87ee2baac810a370f5c575590214751f428eab204200a3e85dcd640840147b0bb9ac810a82abe09735902106d56412e6b204200a3e851cd640840147b0a39ac81080387d4e535902106f17296a4b204200a3e85dc1640840147b0bb82c8108030f5d670590210051f428e0b204200a3d851c1640840187aea382c810802a7a0c70590210054ec18e0b20420daae821c1640843f55b04382c81080eada0470590210fd5ac08e0b2042008be87d41640840117b0fa82c81080e3720d7598c2101c6e41ae93184216c5f75d4e63084014bd0ba1cc610802976174398c210043fc2ae1318420287c855c2630840117f08b84c6108062f2117098c2101c6e41ae13184216c5f759d663084014bd0b3a4c610802976167498c2146d2ec2ca93184200e1f549526308401c3f08aa4c610a3787d055498c2146f0ea0aa9318428ea5e8515263084014bd0ba14c610802976174298c210052fc2ae13184200a5c855c2630840153f08b84c610802a72117098c210054f426a13184200a9d84d4263084014bd0ba04c610802976174098c210070eaa48131842168de8710263084011bb0e204c61080297a144098c210052ec28813184200e1d54102630841b59d04204c610802b36084098c2101d6b408813184200ad581102630841b1d904baac61080e3d2057558c2106c76412e8b1842038de87d4d63084018beeba9ac610836b3a0b5358c210162f3aca6
  | 12 => 0xa8f938855418d2151f2610aa831a4200a5e851506348401c9ea8b90c690803935517218d210b667b8ae431a4200ad78154863484b15a902a90c69080297a174218d210052ec2e8431a4258ad681d0863484015ab03a10c69080297a144218d210052ec288431a4200a5f855c463484014b90ab88c690963335c97118d2100567416a231a4200acd82d44634840159f04a88c690802b32095118d210052f42e8231a4200a5d85d046348401c3aa9a08c690802b3a0b4118d2100566c168231a4200e1d54504634840159f04a08c690802b32094118d212c76210a8231a4200a5f8548463484014b90a908c690962b3e092118d210052fc2ae031a4200a5c855c0634840153f08b80c690802a72117018d210054f426a031a4200a9d84d40634840159d04280c690802b36085018d210052f42e8031a4200a5d85d006348401c3aa9200c69085a37a1c4018d210046ec388031a4200a5e8510063484014bb0a200c690803875504018d21005674108031a4200acd8210063484b15ad02200c690802b56044018d214cc3e432eb9924216c5c635d732484cf0ff0fb2e64908021f61f65cc9210062f3aec79924200c5d75d8f32484050f90b3b464908d61f219758c9210043fc3ecb192422387d87d9632484018bcebb1c6490803175d7638c9210062f3a8c71924200c5d7518e32484018d8cb3b464908031b9d6768c92100637c2ced1924200c6c859da32484018dea93b464908031b552768c9212c667c1ced1924258cce319da32484b1998633b464908031b9d9758c921006373b6cb1924216ace86d8e324840199cedb1c6490963339d8638c92100727b28c71924200e4c6518e3248401c9cea31c6490803935d4638c92100727aa0c71924200e4d5418e32484b199ce231c6490963331c4638c92131e6a38ec69924200c7465dc532484cf8d8edb2a6490802b3a1b734c92131e663b6e69924216ace86d8d32484c7998edb1a649085b331d8634c92100727b28c69924200e4c6518d324840159d0e31a649085b33a1c634c92100727aa0c69924200e4d5418d32484b199ce231a6490963331c4634c92131ee3b98e29924216acc864c83248401c9eca9906490a1393195320c9212c477434e598a4216ccc639cb314842d998c6b96629098e73e1d32cc52101d664326598a420087f855d931484050f90abb2629080a1f214764c5210043f436ea98a420087e87d9531484010f90fb2a629080317dd7634c5210062e3aec698a4200c5f7518d31484018b8ea31a62908031bd97724c5210063632ee498a4200ccc63dc931484018deca39262908031b194724c52100667b18e498a4258ccc631c931484073990e992629080eb3219324c521006663b26498a4203bc4814c931484b199ce431e429099f99d8b65c85210072a328c790a4201c3e7455360
  | 13 => 0x52ec20cbb1a4200a5e8599363484014bb0b326c69080297e1564d8d210052e42ac9b1a4200adb8059363484015b100b26c69080297a1464d8d210052ec28c9b1a4200a5e86d5363484014b90daa6c69080297a1954d8d210052e432a9b1a4200c5d751d763484014bd0b3a6c6908029761674d8d210052f428e9b1a4200a5d851d36348401c3ea92a6c69080387e1154d8d210052fc2ae5b1a4200a5c855cb63484014bd0ba16c6908029761742d8d210052f42885b1a4200a5d8510b63484014bd0bb8ec6908029761771d8d2131f2b28ea3b1a4200a5e85d0763484014bb0ba0ec6908038755341d8d210070eaa283b1a4200a5e85dc363484014bb0bb86c690802a7a1370d8d210054ec26e1b1a4200a5e859c363484014bb0b386c690802a7a1350d8d210054ec26a1b1a4200a5e85d0363484014bb0ba06c6908038755240d8d210046f43881b1a42008dd8710363484014bd0a206c6908029761440d8d210070eaa081b1a4200ace82103634840159b04206c69098eb5a0440d8d210056ac0881b1a4216c5c635d663484018bcebb1cc690803175d76398d210043fc22eb31a420287f87d5263484010fb0faa4c6908021fe1d5498d210043ec3aa931a420087e87d9563484010fd0e32ac6908021f6137558d210046fc1aeab1a42008ef825d563484011ef02baac6908021fe157458d210143e42ae8b1a42008df835d163484011df04ba2c6908023ee017458d210247c402e8b1a420087e87d5163484050f90faa2c6908021fa1d5458d210043e43aa8b1a4200c5f75dcd63484018b8ebb9ac6908031bdd77258d21006363aee4b1a4200c6f54dc963484018daa9b92c6908031d1d77158d214ce36b90ca31a42008df8758c63484014bf0ab18c690802972156318d210b46e41aea31a42168dc835d0634851d8dae5aa0c6908070f9d15418d210061eba2a831a428dc6d72550634842d8beeba98c69080297a174318d210052ec2e8631a420087f855c063484050f90ab80c6908022fe117018d2100c5e422e031a4200c5e76d9463484014bb09b28c690a9b938876518d215372610eca31a42008dd8799463484011bf0eb28c690803179d86518d210052ec20ca31a42a5e4e21194634854bc9842328c6908023761e6418d210052f42cc831a4200a5d8599063484011bf0eb20c69080297e156418d210052e42ac831a4200adb8059063484015b100b20c69080297a146418d210052ec28c831a4200a5e86d5063484014b90daa0c690803179db5418d210052f432a831a4200a5c8655063484018bcecaa0c69080393d957218d210072632ae431a4216c5f759d463484014bd0b3a0c690802976167418d215272710ea831a42a4e4c21d5063484014bb0b2a0c69080387d525418d210070fc22a831a4200e1e745506348401c3ae8aa0c690
  | 14 => 0xa85109600c4014f30a212c0188029ea1632580310053cc2c64b006216ec8324c9600c4010ff08baec79080a1fe1f54d8f210043ec3ea9b1e420087f8755363c84010fb0eaa6c7908021fe117598f210143fc3ea931e420087d87d5263c851d8dce5aa4c7908021fe1d5498f210043ec3aa931e428dc6e7255263c840387ce8aa0c7908030f5d15418f210043fc2ae031e420287c855c063c840117f08b80c7908062f2117018f2100567438c6996420dcce8718d32c8401c9ea831a659080393550634cb2106f62c08c69964258cce7118d32c84b1998e231a659098e37e1d63cc7212cc77c32e598e42639cf874cb31c84b11bd0f31a6390837331ca634c72106e66392c698e42039cc874c931c84010fb09baac1908022fe11755832100c5e422eab064200c3f75dd160c8401878ebba2c1908030fe1774583210061e42ee8b06420087f855d160c84050f90aba2c1908030fdd474583210061e3a8e8b06420087e87d5160c84050f90faa2c1908030fdd3545832100e1e3a6a8b06420087e8755160c84010f90eaa2c1908030fdd1545832100e1e3a2a8b06420087f855c263884050f90ab84c7108022fe117098e2100c5e422e131c420287e87dd563884010fb09baac7109f21fa1c7558e210043fc2ae8b1c420287c855d163884011f700ba2c7108123e2017458e210043f43ea8b1c420287c87d5163884010fd0eaa2c7108021f21d5458e2100637baee4b1c4200c6c75dc963884b11bf0eb1e65108031b9d576cca2100636bb2eb99442588ef8758f3288401acaeab8e651098e37a1e634ca212c5e240a641944258bc6819cc328840187ee8aa2c1108070f1d154582210043f436e9b2a420287f87d93654840187ae9b26ca908021f61e64d95210052f41cc9b2a4200a5d8399365484010ff0eb26ca9080297e0d64d95210052e41ac9b2a4200a7b8059365484014f100b26ca9088e1f61c64d95210061eba0c9b2a420087d879d3654840187f08ba6ca908021fa1c74d95210061eba0e9b2a4200c5d731cf654854f4dd0439eca9099e9b60873d95210043f43e87b2a420087d87d0f65484010fd0e21eca908021f61c43d952133c3f43e85b2a420087d87d0b65484010fd0e216ca9088e1f61c42d95212bd37416e3b2a420087e87d0765484010fb0fa0eca908030fdd341d95210061fba283b2a4200a3f845c3654840147908b86ca908021fa1f40d95210043ec3e81b2a4200c3f7490365484010fd0e206ca908021f61c40d95210061fba081b2a4200a5e8310365484014bb06206ca908029ba0840d952100536c1081b2a4267a768110365484014eb02206ca90803175d753d8d210162e3aca7b1a42028df8754f63484014bd0ba1ec6908029761743d8d2100c6fc3a87b1a4200a5e8510f63484014bb0a21ec6908029761365d8d2100
  | 15 => 0xba1ac4188029b61743588310b56741ce0b106200a6f855c1620c4014d90ab82c418802abe11705883100556422e0b106216acc835c1620c4075c902b82c4188029ba14705883100536c28e0b106200aae84d41620c40155b09a82c4188029ba17405883100536c2e80b106200e2d54901620c4011dd0e202c4188023b61c40588310053742880b106200a6d85101620c401c5aa8202c41885ab3a0c405883100566c1880b106203ae681101620c4015cb02202c41880a1fa15768c8311ac3fc32eb1906200c3e645d6320c41b8dcc4bac64188a21fe1d658c8310043ec3acb1906200c3e75592320c40187aeab2464188031b9d5628c83100636baac51906200c5e755da320c42d99ce4bb4641880317a15768c8310062ec2aed1906200c5f545da320c4018baa8bb4641885b33a09768c83131e66c12ed1906200c5d765d6320c401c9ceab146418803935d5628c83100727aa2c51906200e4d5458a320c4c799ee2b14641898f335c5628c8310b726192ca9906216e8c32591320c42d59f0eb10641898f33e1d620c83100727aa2c41906200e4d54588320c4018e8ebbb262188031de17764c4310063a42eec9886200c7754dd9310c4018eaa9bb2621880339e0b764c43100672416ec9886200c7776dd5310c4019ceedb92621880339dd8724c431006b23a8e49886258dc7731c9310c401c76a92a4c0188038ee11549803147f1dba2a9300628fe3874552600c51bc7682aa4c018a378e50554980310b72d29ea73006200a7a85d0e600c4014f30ba1cc0188029ea1742980310053cc2e853006200a7a8510a600c4014f30a214c0188029ea1632980310053cc2c653006216ec8324ca600c40187ee8aa2c0188070f1d1545803101c7d43ea0b006200aba84d41600c40157309a82c01880e3e21d505803101c7d43e80b006200a7a85d01600c4014f30ba02c0188038e552405803101c7c43a80b006200a7a85101600c4014f30a202c0188038e55040580310b56d41880b006200aea82101600c4015d304202c01880ebca0440580310055d424eab006200ab9849d5600c4014f50b3a2c0188029e61674580310053d428e8b006200a79851d1600c42d5b5063a2c018802b660c745803100575410e8b006200ae9821d1600c4075e5023a2c018802bc60474580310071daa4a8b006200e3b84551600c401c76e8aa2c0188038e1d1545803146f1da0aa8b00628de3941551600c42dcb4a7a9ac0188029ea1743580310053cc2e86b006200a7b855c9600c4014f10ab92c018802aee1172580310055c422e4b006216ad8835c9600c4075e102b92c0188029ea1472580310053cc28e4b006216ada83d49600c4015b307a92c0188029ea1742580310053cc2e84b006216ada83d09600c4015b307a12c01880ebca07425803100578c0e84b006200a7
  | 16 => 0x25813100657ba6c4b026200cac74d89604c4011dd0e312c0988031bdd46258131006363a8c4b026200caf74189604c401958e8312c0988023ee1d60181310055c422c0302628d87d879d1650c40187ee93a2ca188030fe1174594314743f438e8b28622887e87d0d650c4010fb0fa1aca18aaa97e0d72594310b52e41ae4b2862a9a77815c9650c4074e902b92ca188021fa1f42594310043ec3e84b28620087e87109650c4010fb0e212ca188028fa1370594310051ec26e0b28620087e87d01650c4010fb0fa02ca188030f5d240594310043f43880b28620087d87101650c40187ae8202ca1885a97a0c40594310052ec1880b286200a6e82101650c4014db04202ca1880e9da0440594310053ac0880b286200c3f759d5640c51b47b0f3aac8188030fe1d755903146e1fb8aeab20628dc3d715d5640c51d47d0a3aac81885b8794f53590310051f42ee4b206200a3d85dc9640c55153f06b92c81885aa720d72590310051f428e4b206200a3d851c9640c40147d0bb82c8188028f61770590310061ebace0b206200a3e851c1640c40147b0a382c8188030f5d470590310b54f418e0b206227a9d831c1640c40155d04382c818802ab608705903101d5b408e0b206227ab5811c1640c40117d0fa82c8188022f61f505903101c76412eb31062038ec825d2620c4014dd0ba14c4188029b61742988310043fc2ae1310620287c855c2620c40117f08b84c4188062f211709883101c76412e13106200a6e859d2620c4014db0b3a4c4188038bd52549883100717c22a9310628de2f41552620c51bc5a82aa4c41885b9394f53988310053742e873106200a6d85d0e620c4014df0ab84c4188029b215709883100557c22e13106200aac845c2620c40155d09a84c418802ab61350988310053742e813106200a6d85d02620c401c5aa9204c4188363ba1c409883100476c38813106200a6e85102620c4014db0a204c4188038b55040988310b567418813106200acd83102620c4075cd02204c418802b9604409883101c7743ea4b106216ace83d49620c4071d90ea92c41885ab320d525883101c7743e84b106200a6e85d09620c4014db0ba12c41885ab3a0f425883101d7340e84b1062038ec87509620c42d59906a12c4188029ba14425883100536c2884b106216ace839d5620c40159b073aac418802b3e0d75588310b56641aeab106200ae7815d5620c4075c902baac4188029ba16745883100536c2ce8b106216ace839d1620c40159b073a2c41880eb9a06745883100572c0ce8b106200acf835d1620c42d59906ba2c4188029ba14745883100536c28e8b10628ee4f31d51620c51dc9a63aa2c4188038bd52545883100717c22a8b10628de2f41551620c51bc5a82aa2c418a3793cc5545883146f2698aa8b106216e4e53d4d620c4014dd0
  | 17 => 0x126200a6d85190624c4014dd0daa0c4988029b21b541893100537432a83126200a6c86550624c401c9ecab98c4988039319573189310053742ce83126200a6d859d0624c549c9c63aa0c498a93930c7541893100717aa4a83126200e2f84550624c401c5ce8aa0c4988038b5d1541893151f2718aa831262a3e4c31550624c401c9ea7298c498802b9e0553189312c57240aa63126200a6e85d0c624c4014db0ba18c498962b9a07431893100572c0e863126200a6e8510c624c4014db0a218c4988029be1571189310053642ae23126200ace83d44624c40159b07a88c498802b3e0d51189310056641aa23126200a6e85d04624c4014db0ba08c4988038b55341189310056741e823126200acd83d04624c401c5aa8a08c498802b3e0d41189310056641a823126258ec431504624c4014df0a988c4988029b215311893100537c2ae03126200a6c855c0624c40155f08b80c498802ab211701893100557426a03126200aad84d40624c40159d06280c498802b360c50189310053742e803126200a6d85d00624c401c5aa9200c4988363ba1c401893100476c38803126200a6e85100624c4014db0a200c4988038b550401893100567418803126200acd83100624c4b15cd02200c498802b960440189310143e42ced992623687c865d7324c4010ff0fb2e64988ae1f61f65cc931006373a8c59926200c6d7518b324c4018b8cb3b66498803179d676cc9310062fc2ced9926200c5c859db324c4018bea93b664988031755276cc9312c667c14ed9926258cce219db324c4b1998433b66498803179d975cc9310062f3b6cb9926200cce76d8b324c4b199cec316649880393d9462cc93100726328c59926200e4e7518b324c401c9aea316649880393d5062cc93100726aa0c59926258cce7118b324c4b1998e23166498a761f219758c93106e36312eb192620087d87d96324c4018dcebb1464988031b5d7628c9312ce7238ec49926200c7465dc5324c4f98b8edb2a6498802b3a1b724c9312ce663b6c49926200e4f65189324c401c98ca3126498802b3a1c624c93106e67438c49926200e4f54189324c401c9aa8312649896771dc8714c93100727b2a641926284e4c654c8324c4f9caec7b2e62988039919462cc53100e1f3a2a9b026200c3d74553604c401c72a8206c098802b660c40d813100578c0881b026200c6f659ca604c4018d8cb394c0988031bd9572981310063632ae53026200c6e75d8a604c4018daebb14c0988031b9d4629813100636ba8c5302620287e86dd5604c4f90f90dbaac0988021fa1f65581310061e3a6cab02620087e87195604c401878e832ac0988030fd9774581310061e32ee8b026200c6f65dc9604c4018d8cbb92c0988031bd94725813100636328e4b0262008ee87d89604c4018deebb12c0988031b1d76
  | 18 => 0xc4050ff0fb26ca988030f5d364d95310043ec3cc9b2a6200a6e82993654c4014db05326ca988021fe1d64d953100537c12c9b2a6200a6c82593654c4014f700b26ca988029e20164d953115c3ec38c9b2a6200c3d74193654c4010fb0f3a6ca988030fe1174d95310043f438e9b2a6200c3d741d3654c4f90fd0fa1eca988021f61f43d95310043f43887b2a622b87d8710f654c55b4bd06396ca989f29760c72d95310043f43e85b2a620087d87d0b654c4010fd0e216ca988021f61c42d953137d2f41ee3b2a620087e87d07654c4010fb0fa0eca988030fdd341d95310061fba283b2a6200a3f845c3654c40147908b86ca988021fa1f40d95310043ec3e81b2a6200c3f74903654c4010fd0e206ca988021f61c40d95310061fba081b2a6200a5e83103654c4014bb06206ca988029ba0840d953100536c1081b2a627ca7681103654c4014eb02206ca9880a3be1d52d89310053742e85b126200a6d85d0b624c4031df0ea16c4988029ba1442d893100536c2885b126200a6d84d97624c4014db0832ec4988029ba1664d893100536c2cc9b126200a6f85593624c4014d90ab26c498802bae0164d893100574402c9b126200a6e85193624c4014db0a326c4988029ba1b54d893100536436a9b126200a6e86553624c4014d90caa6c4988029ba1674d893100536c2ce9b126200a6e851d3624c4014db0a3a6c4988038bd5254d893100717c22a9b126200e4f5394f624c4014dd0ba1ec4988029b61743d89310053742887b126200a6d8510f624c4014dd0bb8ec4988029b61771d89312cf3328ea3b126200a6e85d07624c4014db0ba0ec4988038b55341d893100716aa283b126200a6e85dc3624c4014db0bb86c498802aba1370d893100556c26e1b126200a6e859c3624c4014db0b386c498802aba1350d893100556c26a1b126200a6e85d03624c4014db0ba06c4988038b55240d89310047743881b1262008ed87103624c4014dd0a206c4988029b61440d893100716aa081b126200ace83103624c40159b06206c498966b9a0440d893100572c0881b12620dc6c625d6624c4018dcebb14c4988031b5d762989310043f43ecab12620087e87195624c53b8bae6328c4988023be1d621893100537c2ac43126200a6c85588624c40387ce8aa0c4988030f5d154189310053742e843126200a6d85d08624c4010ff0ab80c49880a1f21570189310045fc22e031262018bc845c0624c4018dcedb28c4988029b61365189315672718eca31262ace4c31d94624c4011db0f328c4988023be1d6518931006373b0ca3126200a6d84194624c557c9c62328c498aaf930c4651893100476c3cc83126200a6e85990624c4014db0b320c4988023be1d641893100537c2ac83126200a6c85590624c4015d700b20c498802ba201641893100537428c83
  | 19 => 0xee3a10714c832005c6c20e29906458dc6711c5320c8017950038a6419002f2600714c83200566c34e09906400acf865c1320c80169f0ab826419212d3215704c832005c7c22e09906483b8c845c1320c80178f02b826419002f1205704c832425a7428e09906400b4d851c1320c8b13990e994c219162f120532984322c4e643a64b086400d4f754c9610c909a98ea992c219162f120532584320043ec26eab086400a3d841d5610c8010ff0aba2c21900a1f21574584320047dc02e8b0864048f8805d1610c8010fd0faa2c21900a1f21f54584320043f43aa8b08640087c87551610c80387ce8aa2c2190030f5d154584322c46f43e64b086458ad681cc9610c81bd8843992c2191623ba1e32584322c57340c64b086416ec4318c9610c8b11b90e992c219162b5205325843206f6390a64b0864588ec874c9610c8b15c902992c21905bb1cc5325843200667c3a64b086458acc874c9610c8019990e992c2191623321d325843200727baa64b086400e4c754c9610c801c9ea8992c21900393551325843200763c0a64b086458ace814c9610c8b159902992c219003b120532584322c56240a64b086402c7475945610c801d8a6528ac2190363d21d515843200762992a2b086400ec532905610c81b1e90ea0ac2190038d55141584320076299282b086400d4f754c9600c909a98ea992c01900363dd1325803241ec63a264b00640dec8604c9600c8010fb09baac0190022fe11755803200c5e422eab006400c3f75dd1600c801878ebba2c0190030fe1774580320061e42ee8b00640087f855d1600c8050f90aba2c0190030fdd474580320061e3a8e8b00640087e87d51600c8050f90faa2c0190030fdd3545803200e1e3a6a8b00640087e87551600c8010f90eaa2c0190030fdd1545803200e1e3a2a8b006402c7875941600c81b1f10ea82c0190072e1d240580320071caa480b00640d8f887501600c8010ff08bacc59880a1fe1f5498b310043ec3ea9316620087f8755262cc4010fb0eaa4c5988021f61375583310045fc22eab0662018bc845d560cc40187eebba2c1988030f1d774583310061fc2ee8b066200c3c85dd160cc4010ff0aba2c19880a1f21574583310061fba8e8b066200c3c751d160cc4010fd0faa2c19880a1f21f54583310061fba6a8b066201c3c74d5160cc4010fd0eaa2c1988021f21d54583310061fba2a8b066201c3c7455160cc4010ff0ab84c51880a1f2157098a310045fc22e131462018bc845c2628c4050fd0fbaac5188021f6137558a310043fc2ae8b14620287c855d1628c4011f700ba2c5188123e2017458a310043f43ea8b14620287c87d51628c4010fd0eaa2c5188021f21d5458a31006aabaae31946258bc4814c8328c4b178d0339065188030fdd1545823100e1e3a2a8b04620087e86dd3654
  | 20 => 0x5ec26e0b0e6400c3f7455160cc803878e8aa2c19900a1fa1771583320043ec2ee2b066400e395410160cc82d5b506202c199002ba608405833200578c0880b06640087f865d1658c86b0fd0f322cb190030fdd264596320143f43ac8b2c6400c3f74591658c8010fb0f3a2cb190030fdd274596320061fc22e8b2c640087e871d1658c95d4df04b9acb190029de0573596320053a40ae6b2c640087e87d0d658c8010fb0fa1acb190d61fa1c43596320043ec3886b2c643587e87d09658c8010fb0fa12cb190378b109425963206d37414e2b2c6466a6d829c5658c8014bf06b8acb191ce9720d71596320051f420e2b2c6400a3d841c5658c8010fd0fa0acb190021f61f41596320061eba682b2c6400c3d74505658c8010fd0e20acb190021f61c41596320051f426e0b2c6400a3d84dc1658c8010fd0fa02cb190021f61f40596320061eba480b2c640087e87101658c8010fb0e202cb190030f5d040596320052f41880b2c6400a5d83101658c81b4dd04202cb190029b60840596320053b40880b2c6400a7581101658c86d0ff0cbae65190d61fe1d65cca320062f3aaed9946400c5d765d7328c8018dccabb665190031b5d965cca322cc77c32e39946459ce6615c7328c81b8dce532cc31903799c85659863231c6f43e64b0c6463ad681cc9618c8050fd0bb82c3190021f617705863200c5f426e0b0c64008bd84dc1618c80187ee8aa2c1190070f1d154582320143f42ee2b04640087d85dc5608c801c72a8202c119002b660c405823206d7541080b046400af181101608c82da9864bae64991663b21971cc9322ce7230ae39926416dc7315c7324c81ba9864bac649918e37219718c93231e6a30ae3192640ddc7215c6324c8018eaeba8ec299002ad61051d853200c7bc3a83b0a6400e3554507614c8010ff0ab86c29900a1f21570d85320045fc22e1b0a64018bc845c3614c8011ef0eb08c2990029d215611853200e1f3a2a9b026400c3d74553604c8010ff0ab8ec09900a1f21571d81320047dc3ac0302640287e85dd9320c8010fb0bbb2641900317a17764c8320062ec2eec9906400c5f54dd9320c8018baa9bb264190373394b764c83200666a96ec9906400c6e85dd9320c8018db0bbb264190031bd53764c83200636aa6ec9906416cce53dd9320c80199aa7bb26419212d3a17764c832005a6c2eec9906400ccd86dd9320c801a9d0bbb2641900353617764c83206e67b2eec9906400ccd65dd9320c801a9ea9bb2641900353553764c8322c4e740eec990640dcce87dd9320c801c9d0bbb2641900393617764c83200667baeec9906400ccd75dd9320c801c9ea9bb2641900393553764c83200566c0eec9906400acd869c5320c80159f0cb8a6419002d3e15714c832425a642ae29906484b4e851c5320c80169b0a38a64192
  | 21 => 0x800000001002400800002400c00404000000004000804800801401803406c00800004c00c00400800400402000401801405402000002000c00000400800808800402803401c00c00c00c00c01000000400400004400000405800000000401804c01000400003800001001000004008000800807801c0040000c401400002802004001401806007c00400c00c00001401c00002400c02c00800001802001c00c00004000800c00800001001805c01c00000800000800402400c01403000000003c01801400000000c04c00400000000004000c05401000000004c01005c00800000401000001000401801c07800000c04001800c00000001001803c00c04004001c00000c00c08803800001000000005001001000000005404c03c01001800800c01000003000000008c02003c00c00401001c00001400c07000001001400001000400c00403000400c00801402c00001804001c00000000c02001800412800801000800000403000000401000001800c00000800400400401001800001000c00409800000002007802002401000801800401400000401800401800404c00405001800001005001c00c00001802402800009000401400402c03404005403801c03000c01c02c01c06c00000002c01400001400000c00000002c00402c00c00004801c00001801000400000800803402c02800c05c00405c01401c00000804000003002000000000408401800000800001000404801008000400000003401400002407801c01401c00800c01400800000000000000005c01800c02400804404c00400003003400000000405000401800000000005400400800400000002001807c05c00000402c01000000000401801400404000000001401c0000000c000801c00000400400003c0b000801c018010ff0cba2cb990da1fa1e64597320061fba4c8b2e640287e8759165cc80187ee8b22cb990021f61e74597320061fba4e8b2e6400c3f845d165cc8010fd0e3a2cb990da1fa1f43597320043ec3e86b2e6416e1c4350d65cc9174bf06b92cb990029de0572597320053a40ae4b2e640087e87d0965cc8010fb0fa12cb990da1fa1c42597320043ec3884b2e6416a5e839c565cc8f74bb0738acb990029be0971597322ed36412e2b2e6400a3e841c565cc80147b0838acb990021fa1f41597320043ec3e82b2e6400c3d74d0565cc80187ae8a0acb990021fa1c41597320043ec3882b2e6400a3e84dc165cc80147b09b82cb990021fa1f40597320043ec3e80b2e6400c3d7490165cc8010fd0e202cb990021f61c40597320061eba080b2e6416a5e8310165cc8014bb06202cb990029ba08405973200536c1080b2e6400a768110165cc8014eb02202cb9905b179ce65987320b72b98acb30e640287e85dc161cc8010fb0bb82c3990062fa137058732004
  | 22 => 0xb80015463ec056000101ca5e346ab2ce9a00e498a0f84103b217600000004df53100011a28be0001adc0005bb00000010ee45c1048000bfe000000000164890f3dd0cb910c8513820a551da1c81a900011c896227a173c0f400052688103e22e914b0000000000000000000094700000000000ab1e808140005b02fa96d0cec1f2363964049c68231c84ec4c45964d6a0405a26c93dca1053789203eb183cf163f659d03ec000220395a1ad4da7e84ad81014ae4cd1ad20e4a0e1a1438181d06e6d925b801401801c01000800003402c0000080e401c00401c00001404800c00000006800401001c00400000800805c05000400800800400002c00001000400400000400401400409c02801c00000c00000000400001401400809000000400000802000000001005c02003800002c0100080000240140000740000780180000000d800401c00001004401000001000000c03c00006004001003000803c05c01c03003002800400c01001801000000000002801401c01c04000c00800c00000000001800402803c00000801002c0200180000000000180b800400c00400c03001800c00400002801002c00402400800400000400001000401801000400001c02400804000400c00000400000000000004802400000000000402800006800001400008801800004800c0a806800800c04801c00002810401800001002c00c03800001c0240000080000080140000000900080080c400001800c0000280180100080ac00000000808c01001000c00400402401000c01000400002c00400400404400c01c02000c02802000400801800c07802800401401800000000000c00000802801002000001800001406001c02001c00002c06001000801402000401803006c00400807000001000401000c00800809003401404000400800401401400400000400002402800400c01c02c0780240180000000100bc00801000004c00000001800000400c02000808400801400000000800400000c00400c00401800800c00c00400800c01400000400000000c00000800002400007c00800002807000403400003800001400000000c03c00006400400c02401400400001414001000400001801401400802000000400400000c00400c00000800000800000000800001403805401400c00803c01801002800c00000401001401402005c01000000000800400000400000c06000403000400807000400000c00001c0a400401400408800803001c02801400801000000002c02000406800800403403000000403401c01401800001401c00806800000000400004400800800c00000400001c0000300080140000000000440b801807401000000c00000c00801c00800007c09c00000001405401801405800800800401001000803000403400009c000034000008014000010
  | 23 => 0xac73800011c0fe26b12d8a0ac61860e4f60000cd8330000000000067b2978000000000000126c54826000c1970000600000151c01aa4400000000000000000a140005c817caa5800000000019b8000aaa50a9b60c3033a000293800000000000003f62c14ba000085838b2849b54d28a72000044c1ae5b500024f000030a572ab3000070809d22b09ce9ff3ec9b7cb8682815415f05d66c24390000bda4893cd8000d543b1177292925a4991f10000b0c68f04c23254f6732541800018c00056514300000000000000e900005a180001486da00006155c4000000004cfec5c73f588d857473913a984046271b000163d4ca31e09808c13c44444c923d929a00000022f50902760d91f2004a1a90000d7d204b7b4f8a828df000053307c12385870000000c0a06a00016b41605ca0000f80a54ad40d516995b679c2b285f459e3d72b12c114f24ba3450a80f9a3e72e826740002cc2a18face06b0712380000003f80000000000a784fe238802474046305a0fd450332287457020ba45d81d829295227c25c473e80f10729a50dc71e3838f34d38a9d111910520c14c55312495c8000008a4e81d8850000002000000031d21d057200003f80001705e330f00015800001190000e745c200000010ac44d0e0101800000014008b53d22ce05a07d85226640000f900001a20002b442e601b000033cd02460000000000047a0000c900008e828a000000045b5a49250f80ac100498f04886b429a150111613334b27948f6ad71bc05001220001bc800000096a00008440006194790198e3200045a26f4f940001d42b602a65212939f7d62e0000000c45400a1b5611c3860e2610879d6023251a014000100e6e015e2abcf320000828000e5023e5770c10b24b8b0000edc000405000278146600005090215c27f43a59dcc8d24174e39aa118099f5bb122d0c0a742b58908ef8a211061230d2602b3e204b4f86b1b1d0224c18832c115aab48de6992c18694c7639b49d8ad035a2435a8a2a4d986c1164027c53c785590930546ea851de80000004683ae221cf420a70000c1400066755f9e50a3c00000000000006020f327c94f418704e800148a0005be00000bc7d04d2000000800010900011962450b60efcf0e73c1b42964aee44622e875893e8e70c500009ba91225f917c46a0805631b4c2683ab5118000b6e84d000000134c12b1a8875039877954129c483444900004614ee826000007c9200000d9a8b44006ec0000000000a4f38a8b24db851f1f4aa280003db00000011a89052c4ac410387a338f933c0907f2438aaa4b646b931a0e540a26112871bf829cb8354687411142a114202554fe1eb037a664d7c8ba5c1296d2ec00f3d997395c6713000000000028606e9a88be866a0d2050cb9601c1b1196400000000021d41e4a073ad80004440001c
  | 24 => 0x4c134c6907f85b0a3e44be9b33680000af40001a2ac6883c786507aca8000a5a51900004fc00000016e45120001492748e42b031cd13dcc9661b4e32824e446d120f80007203080000000ab4834000273476a0001e3035800022900028f00b869b000000000000000001380009b50000000000b5534600002203f1043aa905449505800000dbc7843ca848c0000025b6a4e032a00055e03d5542000097800058600041e21784969eb239277d7100a30002b1443453f1e480007da0fd3d6000116cacf07406f85aa90c1c380015ba0000a7800094e1c700008e40006655458000000a9b450800000093700010a4000a6b2782c795340005ab91f8c6e000512109531c082000274535657000005c84f286350e9028d460000001bf400084913d000105a0be00002ec6ae00000003e0000a401411ab0a1e8b13e58cdd08e2810e0aab00e00fe50f957881e0003d2266900092300b8000fcc00054614c887e4e01eb0bcc00007d25a0d6c5963c751c9909340000318085c2f800017a00000000000000dd0000000444022c0002f716daba0d667af22b1c24fde2592118748182a733b78a8c0005e8395160146c5c439f0ac49fa56422980000989e80b715104de41b367060530c1b82f3140515e5062f1209c4b45ac3289fa56722660000000b3a8b72cca30c6f66383bb80000000000000000fd8109000000025800025990cc0006ba000000000000000000013ae5182aa00011f880c52a8000aae00018d215c000341000000125463d0e981903bc22a3740f00b10b411dc038911846200000009d80c80001a600001b11e29c0136409a05000003fc81b00023401da87b43106d53e056f00029a097292c2b400011f4a4914e80000004aa0808d4d00c057000234800000021880000009f44f1aac057031500000013980000000dfc4f616700000006ceb23000000000037d000000057c94e2ce00000000012d289a54184a939e96784ba36e3d0000000030e00000007ee0000002a4c1a8024520a63c0001322371c6026249710a29703ae003366a0100005d300012280a80003c10e4c0009fe0001324f8a7c6000000000042b000042097a000282800075e5e0000149800093537d8db40789011dc957d5240000000b502946211bb800121a00026ba9811b66b0256a12cdca9193ff9f455ac1464781114cd013e2690001318b7e3a91ccc000a7e3e3839167ab312d780000000002911c7000000000000000007fb493800014456d00020c8788b9015a9954cfa0000000000000b0a2270000ff4b6358597cc2707a91f40acc54c37358a91c40000005c90000de033820896a523e00000017f88f88da0002b24f2c000000000093c9b600022c00000000002ae10983cf20b217c6061622b50c416fa455143800000033b0000b6008a0004180c8c0003b62d9a940d
  | 25 => 0x4a871110e0d1c136b650fa23304ca17a3a70bb4ff846500019f03b41ea2940e295e668314ca1b52129c02ac0000bd23b30d82d38baeb68192a02c000000338abb54fa19437a02f4000691000013564e8150001bcd60a00036519892f06240a3a4cc1149a859425f42229685068474ed06f60e68bf568c7341cc1c413908141cc97709c204a5b516a86247242fd02a04fe47d1d52620bbc6543a184856a658e00005652bc6a933d000170805a000000000000000000014beacd19690bcff21e10ad169d3b000000b11ac000943246a4f479455042714107009322ac8df01b676b24305c0000a51041a46c00089f25d8bc840c0ad3208a300c61960000000ce64fb3eba6e470aa05155290c8d40f103f0a4cef61f812f2cd43dc8923f2849c1785fb34380005a41d51a78cfc40497c5ac252d6b400012408644d09db0800e44bfa0000e700008385f60001cb0a2c3b00002d813ce64700000e8e948b2169a1f058e00019e000031a0004a3000124a6434530468000b2d0e4aa955a058156f2bb169aa1429717e4a52a6f10f03a53b24f14d2800153270233c924c4aa041567000004c0000001db4f6025c30d095880012e3de80d512e0000002aed30a7905900e345162ff0000000a1600a00000000000000001c155502f83ea86680001144230000000000593180431e01951c0001220904017906444e3ae32d9d093a6ad937500b54409ee35297e04c891a38d155471e0001ff000000077800000011cc18000016d800074f5018ab0240000000000000000000000000008c70000000000ae64c689342b67e24ca14f0a2a0531e98000ea000000007dc47404f4c9ad2c9da6db1b887886861392f52d647f62bb51fa99024834a391a5dcb1668850b862cacc7e4523148cabaa1e04607112b2b38000000104416100000011f646d574866121071d15910503387475c3ad8832000034e9df45063a447c039c99c000575a8ec92a8b535e958c2e8000575000035e0ae065000000008e00016688c8a1113e173496258d3bf138d3448a002aa574fe06b2000079c9ec000561adc05d4122583000106a0000002de4ec000032507fc17e48f00000000000004a090a8f303965a3831498812600000000000000fe845cfc67350028bd43224964a984d40007cf07bac7c16ea2e00001813702630000bd922e756000142000081217800000000000cf000064e3825090a29368000030a9d958e0000ee07e4fba000065800057aa87265a59912298b1b4a0f426c0003111db80007fe3230000b08a97000000000062e000000118a10b00005d935800000000000000000000000000000228ae2800000000000000007f30000000f9c8ec0002a380003941da14cd1660004d797248203ce29a98109c87ab00000004b600022a0a709345da3ee03980009892a9a7a869c8cf1
  | 26 => 0x2ae253d6d287e1390dbc80e4ab4bdacfd5f282352921b000000000001dcf6245a00000000007ad000000090617b0002cf08f00000002a7052e0004552930c3a00003298480ceb4a24e89a8a4a4630000e9445894a04b0000f6e3e142a26f895c511289a20062c57b2a780001e878800000000000000001b2c78400046f8001132b290000000000b6b0000f0400035620c00011e28a800022251940000000c3cfc200057397447ba28f21a000103e0005898ea49a02fb57bacacf5c9ba48194907e87445bf9bbc520a584089e9c0d65e41af10b907612525313fcd889814478618cc654c1dd2cc935c32b55b85588eaaba2412678a404662cb9c286aa84f3dfa68d2fc4c24b4ad400000000532bf4c380005c30fc0000ab257a1d4c98a0003fa901119c26b4c22184adc03d27c8b8cfb41ed0001544f1e0003b3a42d2302670001b00a6e70b5009c9c0005d20b79b90a8a73f295a0212f2831514800000000007019c96cc08f16f08f51d640d1b6067415212919ea4010a69ed0bf8d505de80527f1a78c649c52a687d44143cb0d6255d68423705291301e654900006245be0000b58c187a80004b086ac7b22380afa97480200044b0394000000139800019ab544fc0000000000077a6a955c64001806b87fe1a600012b045c8245bc0270f02b01350a8c45ce01a2528000a8416951791640000000bb8000000a863490000d6a4130001d306cc43701b00000008c21c4952c75a0004cd800088e000000035400022400015f8a7a43900029580002253102278f649c90000000d080003cb88fcc929da1fd000034602733c1bb87765310f2a5cc2148a23ef22348125f21251d90ad82c449f1a006f443d0a883fc2da36411a2a447be3700660aac2888e0375860cccc4a32169dd0f541062d100013bc2074ac09049ac3e332c00a800065259119586800002a080016dcabd0890a510b6a1a1e422708d88e3425168d214a13296a1e16c88ee0000ac00a473753827081540000cd880cc46000474872c00000000021a4000576000000000076c0a580002ae94c3e929b84a25ee0a818cc000000000000123a00000007150e60005bd0764000000247000029a3e53b800012da0000002514000073000087c6380000000610ad2000000000000043a50e21a961013f48a0a6968a00000013bc0007ee4e1a8f8b269513748074c2e77a53e18a0552a2838ba3dca148ff5ba8018bee8671a300f80006744faa9d434032800000000000003f0025c0000000002b4c3c600000606f4b5073600019352b41b92790b1423833503da498000aa034f8000bba0002f60e9d1de5d8000000140c32643c9f04bce3d258c0e18e0282f2012c94b0a3be05900000008c1000000000089a00006300009564c3800067c477000278567c49830b1350d8c2502caac448bcb1d5a9112d
  | 27 => 0x8d9e27d0280300d3400000000000000003df11409ca0003fe93315080c20002c700000003dc09607f20002a500000004d5000000000054e00018946d480100022f0000141000000129004b2cc000000000000a05988f2a6a1b19af000073121001b54900493dd80011fa8680001bfc00050251a8000aea1b70000775102000494800000010e0002e2400064c304800042676226d98f80206af5a00cc40e80002b98000000657011294c5c8000000290800000038a00010b200000024440000002df14ec00020141022b48803a3240883c36c49c000000057e00059b909965ea1001888416e80003c181c43241b40000fccd4c1fc43f80004dc95c3a29a9000000051ea0a86423320bcabe800047450100008fe1654fd17ad1ca5ef14d8e300d80841f78000dc672543d113c000000000131c00016a034000112a85826e00000000000001d5400000006f03d81329e44aa273c0001162b38000d9000007e2e380005a02d71d447b496449c930108a0001faa1693149ef16b038cc2a99c4aaa364000ab420618fc602b0d16b90c14106d21ea9dc8f3a5cc2bc8364128b0928b9d5000000024400009501f30100000fb070d531aaf8b1418801c8ab956200049822fc3785d6581156d01a34245280000007c2344a6540001cf5ae96850c892136293ac6302da00015c44ee0000001d8c7865944fe80001f40d1000193863a0e100003248b0443318800000000037d269d4600003acad3000070f0000000000adf2ec80000000000e308592480000001c9805213d40480011a60000000000000a195b7ad58a1aaf02192839108000342a0080000001f32bc519a0420780b802bc0000f41f6d11c7650000000000b5e3050a34cd660d2800b889cc78c186887544a65f07c8d707082261f9244d1bc38e25119804ae944334a1f42a800058c80000009d40dd20653887122338000f349751910a3800031725f291d320b0e000001d376b8f18483715ec8432399e950b88ea1c085749b43020481d747dc5bf1539a2d69073b000000048000014f9b0c65e6130a2800000067e3c01cb87f8218000057081624f4d8191169e2ca36a248955683300012449609152bfa4bd50039e35f90f8e9262f1789e3875803727403386666e60000000ba80003e6040813c00046e2a24a7c60c0d3ab4971838346b0054986a18000121c6b2270316120162810d22100796be27419a1e255dea2b3e493a800000000008bc7d46f236ba1bc9b07b600000014744363ab80000000003cf00001b41d833f8001510000412800004686657f26c510612a2f088cc0005c627d034c0000002d22e1400045700004a00664380d409b000000000012d80002e656424b87fa1ca00022615fe4ca02ea0740007bc5ca136400056101080016e472f20a9cb503019902394e07b008d57a8e8872407c
  | 28 => 0x912620b8a6c79316692808ec96c3b319842fc00018a0000ebc0000000000a360c31b2a7cc89062a242258cb7895f08a9630b561df28c80fcf1a0005c980000007305b38000000706420000000000054c00004365c03d4000114e00031583400001420ddab6965c00001627d91206271290d80ed41e035da658eea72934b9e98dc268e00004114161934fda0fc9dc00051302cc6ec83815b80015c06e740b93f048c00000010ec23c9420000b74ac0000000000000000000015480000790001dd8ca00000000000c4c8210b00ef02069c1547aa8826e9720b22cc0f140003169dc522c3440000000c0c4b500021085106295308000b749a92c880000004612c118d40640004b8000000051c2cd800000000000007b15e42c00000000dee36b4e8289c5b81e9021aad53f28a455b0ce4cbc9e601a0001156998106934429041d2eda92c0e42a502da4d0a60967252265cae861f27aa35cbe282c03713cc00085225792140008b95caa26ceb49b70001704f3e1820000000000991042800016c00000025940f03dc2f801109901c21a816e0d5c940301800058c65d5b880013ac4221368158bca8c40cf817d20e1bf5c8a0284502e8000258000000029c9d1832e5484220e7008c7614d09e452fea9f1b082c4076792296260142c2154959a9d71a0b55b9ae0153ca900000638ce000006c0000850ab93da00000003de57c02182b08652b91c300007161bf0cd800064856a9da51fc0000000c00d0c2d0000236139c4b20e183480006dd3ea0001052a94409a6fc000b365b600006ea0000000000ca689d000000000000043b17140003a600000000000c705c9ad800051d000000062600041d1a809c42af0002214824000225288800000012980003f451056e00000002e508f8000000b77000299c0005782a3018855a0813040d2514642145c109d0ba97a20719b423600008605546524c657e1f9c4e26b847aa4788a40004412acd02c7a203a8d349d29dc0171ab54d80691ac1d0400066f0449d7cdda00037880007985bd37c977d4540000a923cc00000000010900000000b8800166600000000013aa000000000000000030a00012d6a811950d300006e21d0a6081be2fa15b24d800023b33b816519008859a00005fc00b4941c80d205fc355ad6c0009ca11e243962c00046a80002f05d55878d752de1635538000126803000215400081e44a2a54b3e31f00002495887ed1858e749bc57d40d260c4f0b1232d1bd407031b0000e2161851216c90f03c82fc45703a800053a0000c640004351e882bc2780eb077000129200000000000000000002d7020e83600007bcc6c9dd0000000aac7b5502082d4680001709f4c806a2c46e8161676000000076c97093f1b91dfcc9e96e37e000000000057d92f13eeb2c25080011c200000005d40006754e58b0
  | 29 => 0x4422543fb8000000320000182d1e834b0002d10d2a24
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xd89c2838c8b8f024b4bc3c5020010440551080ac4c08588c304800ccd518010c1ce870fc648401292488000000002cecc0e00c6069083414dc04a400000000a0c4e4000075009010a81920b0006c5c00d114991cf47c784400f8940c00202005002c0990c00304803c010822c040000214018357460440597320068c5518110160cc8018357460440596320068c55181101608c8b18c47161a714c8320140f26174551610c91f438905d154584320061321f754c9610c801a4481dd532584320061321c754c9610c80160d941d5325843200691204754c9610c94984c87d51325843252691207544c9610c94784c87551325843251e91205544c9610c801645952053258432005a1650814c9610c8016c1902053258432004b126132545610c8b14c4974ca4158432004b126132505610c8b14c4974c941584320078155132505610c8014389755240580320060ddd181103654c401a255460440d89310048b650855c4624c547e043155141189310060b61d54100624c401a2554604401893100507650859db324c4b18c471a1b724c9310068c55181103604c401835815d470590310068955181102620c401a255460440588310058c64474551600c4018377460440d95210068555181103634840121d942157118d2151f8108554504634840181d875504018d210068555181100634840142d94216768c9212c6311c686dcd32484b10cc981d9324c5212c631204764c93148401a315460440d81210060d605751c16408401a15546044098c2100685551811016308401631911d154580210140f2617455161cc001435919c375d913047e0e20174505650c00503c985d154587200050d64670dd7644811f838805d141594200050d644705d564c4001c45654c9710cb1000721591325c432c400103f985d0745961047e0e20174505658400103d94e1975cca100040f653865d6328400143594997714ca100040fe5186dd5318400142d94997724c6100050b652651c9318400103f9461b75486100050765265dcd218400141d94994734861000531259325c432440b18c4815d9320c810
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x100400300c87650754c9610c801902ca1023aa64b0864a3d0125d544c94158432
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x5
  | 2 => 0x6
  | 3 => 0x2
  | 4 => 0x1
  | 5 => 0x4d
  | 6 => 0x4e
  | 7 => 0x94d
  | 8 => 0x94e
  | 9 => 0x124d
  | 10 => 0x124e
  | 11 => 0x138d
  | 12 => 0x138e
  | 13 => 0x3
  | 14 => 0x8d
  | 15 => 0x8e
  | 16 => 0x150d
  | 17 => 0x98d
  | 18 => 0x98e
  | 19 => 0x128d
  | 20 => 0x128e
  | 21 => 0x150e
  | 22 => 0x4
  | 23 => 0xcd
  | 24 => 0xce
  | 25 => 0x168d
  | 26 => 0x9cd
  | 27 => 0x9ce
  | 28 => 0x12cd
  | 29 => 0x12ce
  | 30 => 0x168e
  | 31 => 0x20d
  | 32 => 0x20e
  | 33 => 0x154d
  | 34 => 0xb0d
  | 35 => 0xb0e
  | 36 => 0x140d
  | 37 => 0x140e
  | 38 => 0x154e
  | 39 => 0x24d
  | 40 => 0x24e
  | 41 => 0x16cd
  | 42 => 0xb4d
  | 43 => 0xb4e
  | 44 => 0x144d
  | 45 => 0x144e
  | 46 => 0x16ce
  | 47 => 0x3cd
  | 48 => 0x3ce
  | 49 => 0x15cd
  | 50 => 0x170d
  | 51 => 0xccd
  | 52 => 0xcce
  | 53 => 0x15ce
  | 54 => 0x170e
  | 55 => 0x98955
  | 56 => 0x98956
  | 57 => 0x128955
  | 58 => 0x94995
  | 59 => 0x9c955
  | 60 => 0x9c956
  | 61 => 0x12c955
  | 62 => 0x949d5
  | 63 => 0x99255
  | 64 => 0x99256
  | 65 => 0x9d255
  | 66 => 0x9d256
  | 67 => 0xa4a
  | 68 => 0xb89
  | 69 => 0xbc9
  | 70 => 0x98096
  | 71 => 0x98095
  | 72 => 0x150995
  | 73 => 0x150996
  | 74 => 0x1609
  | 75 => 0x1649
  | 76 => 0x151296
  | 77 => 0x151295
  | 78 => 0x9c0d6
  | 79 => 0x9c0d5
  | 80 => 0x1689d5
  | 81 => 0x1689d6
  | 82 => 0x1789
  | 83 => 0x17c9
  | 84 => 0x1692d6
  | 85 => 0x1692d5
  | 86 => 0xb0215
  | 87 => 0xb0216
  | 88 => 0x3ca
  | 89 => 0x170a
  | 90 => 0x3c215
  | 91 => 0xcd555
  | 92 => 0x170215
  | 93 => 0x170216
  | 94 => 0x154b15
  | 95 => 0x154b16
  | 96 => 0xb15d5
  | 97 => 0xccb15
  | 98 => 0xccb16
  | 99 => 0x15ca
  | 100 => 0xb0cd5
  | 101 => 0x15cb15
  | 102 => 0x15cb16
  | 103 => 0x164a
  | 104 => 0x155416
  | 105 => 0x155415
  | 106 => 0x3d415
  | 107 => 0x171415
  | 108 => 0x171416
  | 109 => 0x15d555
  | 110 => 0xb4255
  | 111 => 0xb4256
  | 112 => 0x3c255
  | 113 => 0xcd6d5
  | 114 => 0x15c255
  | 115 => 0x15c256
  | 116 => 0x16cb55
  | 117 => 0x16cb56
  | 118 => 0xb5715
  | 119 => 0xccb55
  | 120 => 0xccb56
  | 121 => 0xb4cd5
  | 122 => 0x170b55
  | 123 => 0x170b56
  | 124 => 0x17ca
  | 125 => 0x16d456
  | 126 => 0x16d455
  | 127 => 0x3d455
  | 128 => 0x15d455
  | 129 => 0x15d456
  | 130 => 0x1716d5
  | 131 => 0xcc3d5
  | 132 => 0xcc3d6
  | 133 => 0x3ccd5
  | 134 => 0x3ccd6
  | 135 => 0x15c3d5
  | 136 => 0x1703d5
  | 137 => 0x15ccd5
  | 138 => 0x170cd5
  | 139 => 0x1715d6
  | 140 => 0x1715d5
  | 141 => 0x104a
  | 142 => 0x1a8a
  | 143 => 0x1049
  | 144 => 0x1a89
  | 145 => 0x125396
  | 146 => 0x124996
  | 147 => 0x1249d6
  | 148 => 0x125816
  | 149 => 0x139255
  | 150 => 0x139256
  | 151 => 0x138b96
  | 152 => 0x9816
  | 153 => 0x44a
  | 154 => 0x449
  | 155 => 0x99616
  | 156 => 0xd816
  | 157 => 0x5ca
  | 158 => 0x5c9
  | 159 => 0x9d796
  | 160 => 0x21715
  | 161 => 0x216d6
  | 162 => 0x21716
  | 163 => 0x1043d2
  | 164 => 0x1a83d2
  | 165 => 0x443d2
  | 166 => 0x1643d2
  | 167 => 0xb15d6
  | 168 => 0x255d5
  | 169 => 0x25556
  | 170 => 0x255d6
  | 171 => 0x5c3d2
  | 172 => 0x17c3d2
  | 173 => 0xb5716
  | 174 => 0x15d716
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2093
  | 6 => 5500
  | 5 => 2966
  | 4 => 75
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
  | 7 => packedAt gbK7 (85805+((h/697+packedAt gbK7 (77441+(h % 697)*12) 12) % 3342)*13) 13
  | 6 => packedAt gbK6 (289662+((h/1833+packedAt gbK6 (264000+(h % 1833)*14) 14) % 14146)*14) 14
  | 5 => packedAt gbK5 (186850+((h/988+packedAt gbK5 (174994+(h % 988)*12) 12) % 3916)*13) 13
  | 4 => packedAt gbK4 (5425+((h/25+packedAt gbK4 (5250+(h % 25)*7) 7) % 91)*8) 8
  | 3 => packedAt gbK3 (245+((h/1+packedAt gbK3 (243+(h % 1)*2) 2) % 4)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7e1f0783fe0fffffc7fc03c0033f893833f7cc
  | 1 => 0xffe007fc1ff07803f83fffffccc80ff8ccc8ff
  | 2 => 0x81fff8001fff8003ffc003fff0f1f1c70f0f0f
  | 3 => 0x1ffffffe0000003fffffc003f01fe07f00ff0
  | 4 => 0x1fffffffffffffc000000003ffe0007fff000
  | 5 => 0xfe00000000000000000000003ffffff8000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x3203018126048a39c6641a41811389181153cc
  | 1 => 0xc44002a40a905048480948948448026844c055
  | 2 => 0x10ad4800152d00929280232b10b0b1830b0d0a
  | 3 => 0x2136954b400001232532b0022b015c05b00ea0
  | 4 => 0x41d8e67299ca65c00000c00c3eec0006eea000
  | 5 => 0x7800c063018c4600062302303fffeff0000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeafcc8feeaecc0feeafcc8feeaecc0feeafcc8feeaecc0feeafcc8feeaecc0feeafcc8feeaecc0feeafcc8feeaecc0feeafcc8feeaecc0feeafcc8feeaecc0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_37145
namespace PEqualNP.Outside.L_meta_37145
open PEqualNP.Outside.L_meta_37145.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 4 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 13 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 17 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 13 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 13 := bs1_4_0
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
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 20 := block_range (n:=20) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 20 := bs4_3_0
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
theorem bs4_4_160 : Interval s4Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_224 : Interval s4Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_256 : Interval s4Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_320 : Interval s4Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_352 : Interval s4Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_416 : Interval s4Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_448 : Interval s4Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_512 : Interval s4Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_544 : Interval s4Atlas 4 544 7 := block_range (n:=7) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 551 := (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96)) (concat (concat bs4_4_128 bs4_4_160) (concat bs4_4_192 (concat bs4_4_224 bs4_4_256)))) (concat (concat (concat bs4_4_288 bs4_4_320) (concat bs4_4_352 bs4_4_384)) (concat (concat bs4_4_416 bs4_4_448) (concat bs4_4_480 (concat bs4_4_512 bs4_4_544)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_64 : Interval s4Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_128 : Interval s4Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_160 : Interval s4Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_224 : Interval s4Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_256 : Interval s4Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_320 : Interval s4Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_352 : Interval s4Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_416 : Interval s4Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_448 : Interval s4Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_512 : Interval s4Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_544 : Interval s4Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_608 : Interval s4Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_640 : Interval s4Atlas 5 640 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 666 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 bs4_5_192) (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)))) (concat (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 (concat bs4_5_416 bs4_5_448))) (concat (concat bs4_5_480 (concat bs4_5_512 bs4_5_544)) (concat bs4_5_576 (concat bs4_5_608 bs4_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 40 := (concat bs4_6_0 bs4_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_7_0 : Interval s4Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_7 : Interval s4Atlas 7 0 1 := bs4_7_0
theorem alls4 : ∀ k ≤ 7, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
  · exact alls4_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 3 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 22 := block_range (n:=22) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 22 := bs5_3_0
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
theorem bs5_4_352 : Interval s5Atlas 4 352 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 379 := (concat (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160))) (concat (concat bs5_4_192 (concat bs5_4_224 bs5_4_256)) (concat bs5_4_288 (concat bs5_4_320 bs5_4_352))))
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
theorem bs5_5_576 : Interval s5Atlas 5 576 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 586 := (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 bs5_5_96)) (concat (concat bs5_5_128 bs5_5_160) (concat bs5_5_192 (concat bs5_5_224 bs5_5_256)))) (concat (concat (concat bs5_5_288 bs5_5_320) (concat bs5_5_352 (concat bs5_5_384 bs5_5_416))) (concat (concat bs5_5_448 bs5_5_480) (concat bs5_5_512 (concat bs5_5_544 bs5_5_576)))))
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
theorem bgb_4_64 : Interval gbAtlas 4 64 11 := block_range (n:=11) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 75 := (concat bgb_4_0 (concat bgb_4_32 bgb_4_64))
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
theorem bgb_5_2944 : Interval gbAtlas 5 2944 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2966 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 (concat bgb_5_832 bgb_5_864))) (concat (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)))) (concat (concat (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248))) (concat (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344)) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)))))) (concat (concat (concat (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600))) (concat (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696)) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792)))) (concat (concat (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984))) (concat (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080)) (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176))))) (concat (concat (concat (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272)) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368))) (concat (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)) (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)))) (concat (concat (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656)) (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752))) (concat (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848)) (concat bgb_5_2880 (concat bgb_5_2912 bgb_5_2944)))))))
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
theorem bgb_6_5472 : Interval gbAtlas 6 5472 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5500 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat bgb_6_576 (concat bgb_6_608 bgb_6_640))))) (concat (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800))) (concat (concat bgb_6_832 (concat bgb_6_864 bgb_6_896)) (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)))) (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152))) (concat (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)) (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)))))) (concat (concat (concat (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504))) (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664)))) (concat (concat (concat bgb_6_1696 bgb_6_1728) (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824))) (concat (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)) (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016))))) (concat (concat (concat (concat bgb_6_2048 bgb_6_2080) (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176))) (concat (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272)) (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368)))) (concat (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528))) (concat (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)) (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720))))))) (concat (concat (concat (concat (concat (concat bgb_6_2752 bgb_6_2784) (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880))) (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040)))) (concat (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200))) (concat (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296)) (concat bgb_6_3328 (concat bgb_6_3360 bgb_6_3392))))) (concat (concat (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552))) (concat (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648)) (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744)))) (concat (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904))) (concat (concat bgb_6_3936 (concat bgb_6_3968 bgb_6_4000)) (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096)))))) (concat (concat (concat (concat (concat bgb_6_4128 bgb_6_4160) (concat bgb_6_4192 (concat bgb_6_4224 bgb_6_4256))) (concat (concat bgb_6_4288 bgb_6_4320) (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416)))) (concat (concat (concat bgb_6_4448 bgb_6_4480) (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576))) (concat (concat bgb_6_4608 (concat bgb_6_4640 bgb_6_4672)) (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768))))) (concat (concat (concat (concat bgb_6_4800 bgb_6_4832) (concat bgb_6_4864 (concat bgb_6_4896 bgb_6_4928))) (concat (concat bgb_6_4960 (concat bgb_6_4992 bgb_6_5024)) (concat bgb_6_5056 (concat bgb_6_5088 bgb_6_5120)))) (concat (concat (concat bgb_6_5152 bgb_6_5184) (concat bgb_6_5216 (concat bgb_6_5248 bgb_6_5280))) (concat (concat bgb_6_5312 (concat bgb_6_5344 bgb_6_5376)) (concat bgb_6_5408 (concat bgb_6_5440 bgb_6_5472))))))))
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
theorem bgb_7_2080 : Interval gbAtlas 7 2080 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2093 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))))) (concat (concat (concat (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152)) (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280))) (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536)))) (concat (concat (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 bgb_7_1664)) (concat (concat bgb_7_1696 bgb_7_1728) (concat bgb_7_1760 bgb_7_1792))) (concat (concat (concat bgb_7_1824 bgb_7_1856) (concat bgb_7_1888 bgb_7_1920)) (concat (concat bgb_7_1952 bgb_7_1984) (concat bgb_7_2016 (concat bgb_7_2048 bgb_7_2080)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 12, 13),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeafcc8feeaecc0feeafcc8feeaecc0feeafcc8feeaecc0feeafcc8feeaecc0feeafcc8feeaecc0feeafcc8feeaecc0feeafcc8feeaecc0feeafcc8feeaecc0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276813000 * 2 ^ 32 + 4276808896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_37145.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.or,[4,5]⟩,⟨.and,[0,4]⟩,⟨.and,[2,3]⟩,⟨.and,[0,5]⟩,⟨.or,[0,7]⟩,⟨.and,[9,11]⟩,⟨.or,[6,10]⟩,⟨.and,[1,13]⟩,⟨.or,[8,12]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813000 * 2 ^ 32 + 4276808896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813000 * 2 ^ 32 + 4276808896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_37145

open PEqualNP.Outside.L_meta_37145 in
theorem PEqualNP.Outside.L_meta_37145 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813000 * 2 ^ 32 + 4276808896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813000 * 2 ^ 32 + 4276808896) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
